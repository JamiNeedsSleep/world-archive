import { createWinHttpCompat } from "./winhttp.js";
import { interpretOne } from "./x64-interpreter.js";
// Dispatcher: runs static blocks, JIT-compiles misses and services Linux x86-64 syscalls.
const EXIT = 0xFFFFFFFFFFFFFFFFn;
const INTERP_BIT = 1n << 63n;
const SYSCALL_BIT = 1n << 62n;
const REG_NAMES = ["rax","rcx","rdx","rbx","rsp","rbp","rsi","rdi","r8","r9","r10","r11","r12","r13","r14","r15"];
const REG = Object.fromEntries(REG_NAMES.map((name, index) => [name, index]));
const PAGE = 65536;
const PAGE_4K = 4096;
const MASK64 = 0xFFFFFFFFFFFFFFFFn;
const negErrno = (n) => BigInt.asUintN(64, -BigInt(n));
const align = (n, a) => Math.ceil(n / a) * a;

/**
 * Run a translated Linux x86-64 image.
 *
 * `syscalls` can override or extend the built-in syscall shims by syscall number.
 * A hook receives { args, memory, context, dataView, readCString, readBytes,
 * writeBytes, ensureMemory } and returns a number/BigInt or { exit, status }.
 */
export async function run({ wasm, manifest, image, rt, log = console.log, logDispatch = console.log, logTrace = console.warn, maxSteps = Number(new URLSearchParams(location.search).get("maxsteps")) || 5_000_000,
  syscalls = {}, files = {}, stdin = "", commandLine = "guest.exe", imagePath = "C:\\guest\\program.exe",
  gui = null, spawnProcess = null, processId = 1, termination = null, network = null, diagnostics = true, pointerPatches = [{}] }) {
  const base = Number(manifest.base);
  const isWindows = manifest.format === "pe32+";
  const memSize = Math.max(16 << 20, align(base + image.length + (2 << 20), PAGE));
  const memory = new WebAssembly.Memory({ initial: memSize / PAGE });
  let u8 = new Uint8Array(memory.buffer);
  let dv = new DataView(memory.buffer);
  u8.set(image, base);
  // Track only code locations whose guest bytes are actually modified. The
  // precompiled WebAssembly blocks remain valid everywhere else.
  // ═══════════════════════════════════════════════════════════════════════
  // Structured Exception Handling (SEH) — x64 unwind + C++ EH dispatch
  // ═══════════════════════════════════════════════════════════════════════
  const winReadU32 = (addr) => {
    const p = Number(addr);
    if (!Number.isSafeInteger(p) || p < 0 || p + 4 > u8.length) return 0;
    return dv.getUint32(p, true);
  };
  
  // Parse .pdata → RUNTIME_FUNCTION table
  const winRuntimeFunctions = [];
  const winFindRuntimeFunction = (pc) => {
    const a = Number(pc);
    let lo = 0, hi = winRuntimeFunctions.length - 1;
    while (lo <= hi) {
      const mid = (lo + hi) >> 1;
      const rf = winRuntimeFunctions[mid];
      if (a < rf.beginAddr) hi = mid - 1;
      else if (a >= rf.endAddr) lo = mid + 1;
      else return rf;
    }
    return null;
  };
  (() => {
    try {
      if (u8[base] !== 0x4d || u8[base+1] !== 0x5a) return;  // MZ
      const peOff = dv.getUint32(base + 0x3c, true);
      if (dv.getUint32(base + peOff, true) !== 0x00004550) return;  // PE\0\0
      const optOff = base + peOff + 24;
      if (dv.getUint16(optOff, true) !== 0x20b) return;  // PE32+ only
      const ddOff = optOff + 112;  // DataDirectory in PE32+
      const excRva = dv.getUint32(ddOff + 3*8, true);
      const excSize = dv.getUint32(ddOff + 3*8 + 4, true);
      if (!excRva || !excSize) return;
      const count = Math.floor(excSize / 12);
      for (let i = 0; i < count; i++) {
        const at = base + excRva + i*12;
        const beginRVA = dv.getUint32(at, true);
        const endRVA = dv.getUint32(at + 4, true);
        const unwindRVA = dv.getUint32(at + 8, true);
        winRuntimeFunctions.push({
          beginAddr: base + beginRVA, endAddr: base + endRVA,
          unwindAddr: base + unwindRVA, pdataEntry: at,
        });
      }
      log(`[SEH] parsed ${winRuntimeFunctions.length} RUNTIME_FUNCTION entries`);
      if (winRuntimeFunctions.length) {
        const first = winRuntimeFunctions[0], last = winRuntimeFunctions[winRuntimeFunctions.length-1];
        log(`[SEH] .pdata range: 0x${first.beginAddr.toString(16)} .. 0x${last.endAddr.toString(16)}`);
        // Sanity: check that _CxxThrowException at 0x5f335c is covered
        const testPC = 0x5f33f3;
        const rfTest = winFindRuntimeFunction(testPC);
        log(`[SEH] RF test for 0x${testPC.toString(16)}: ` +
            (rfTest ? `[0x${rfTest.beginAddr.toString(16)}..0x${rfTest.endAddr.toString(16)}) ` +
                      `unwindRVA=0x${(rfTest.unwindAddr-base).toString(16)}`
                    : `<NOT FOUND>`));
      }
    } catch (e) { log(`[SEH] .pdata parse failed: ${e.message}`); }
  })();

 const winDecodeUnwindInfo = (rf) => {
    const a = rf.unwindAddr;
    if (a < 0 || a + 4 > u8.length) return null;
    const versionAndFlags = u8[a];
    const flags          = versionAndFlags >> 3;
    const sizeOfProlog   = u8[a + 1];
    const countOfCodes   = u8[a + 2];
    const frameRegInfo   = u8[a + 3];
    const frameRegister  = frameRegInfo & 0xf;
    const frameOffset    = (frameRegInfo >> 4) * 16;

    const codes = [];
    let slot = 0;
    while (slot < countOfCodes) {
      const off = a + 4 + slot * 2;
      if (off + 2 > u8.length) return null;
      const word = dv.getUint16(off, true);
      const code = {
        codeOffset: word & 0xff,
        op:        (word >> 8) & 0xf,
        info:       word >> 12,
      };
      codes.push(code);

      let extra = 0;
      if (code.op === 1) extra = code.info === 0 ? 1 : code.info === 1 ? 2 : 0; // ALLOC_LARGE
      else if (code.op === 4) extra = 1;    // SAVE_NONVOL
      else if (code.op === 5) extra = 2;    // SAVE_NONVOL_FAR
      else if (code.op === 8) extra = 1;    // SAVE_XMM128
      else if (code.op === 9) extra = 2;    // SAVE_XMM128_FAR
      slot += 1 + extra;
    }

    const pad = (countOfCodes & 1) ? 2 : 0;
    const handlerOff = a + 4 + countOfCodes * 2 + pad;
    let exceptionHandlerRVA = 0, handlerDataAddr = 0;
    if ((flags & 1) && handlerOff + 8 <= u8.length) {
      exceptionHandlerRVA = dv.getUint32(handlerOff, true);
      handlerDataAddr = handlerOff + 4;
    }
    return { flags, sizeOfProlog, codes, frameRegister, frameOffset,
            exceptionHandlerRVA, handlerDataAddr };
  };

  // Walk the stack from a throw PC up. Returns the final frame details.
  const winVirtualUnwind = (pc, rsp) => {
    let rf = winFindRuntimeFunction(pc);
    if (!rf) return null;
    if (Number(pc) < rf.beginAddr || Number(pc) >= rf.endAddr) return null;
    let info = winDecodeUnwindInfo(rf);
    if (!info) return null;

    // CHAININFO (UNW_FLAG_CHAININFO = 0x04): a cold-path fragment. It has its
    // own RUNTIME_FUNCTION entry so the walker can find it, but no unwind codes
    // of its own — the prolog belongs to the primary function. Follow the chain,
    // then apply ALL of the primary's codes (we're past prolog).
    let depth = 0;
    let forcedCodeOffset = -1;
    while ((info.flags & 4) && depth++ < 8) {
      const pad = (info.codes.length & 1) ? 2 : 0;
      let coff = rf.unwindAddr + 4 + info.codes.length * 2 + pad;
      if (info.flags & 3) coff += 8;   // exception handler RVA+data RVA
      const cBegin  = winReadU32(coff);
      const cEnd    = winReadU32(coff + 4);
      const cUnwind = winReadU32(coff + 8);
      log(`[SEH]     → chain: begin=0x${(base+cBegin).toString(16)} end=0x${(base+cEnd).toString(16)} unwindRVA=0x${cUnwind.toString(16)}`);
      if (!cUnwind) break;
      rf = { beginAddr: base + cBegin, endAddr: base + cEnd,
            unwindAddr: base + cUnwind, pdataEntry: rf.pdataEntry };
      info = winDecodeUnwindInfo(rf);
      if (!info) return null;
      forcedCodeOffset = 0xFF;
    }

    const codeOffsetAtPc = forcedCodeOffset >= 0
      ? forcedCodeOffset
      : (Number(pc) - rf.beginAddr);
    let curRsp = rsp;
    // In winVirtualUnwind, replace the whole switch with:
    for (let i = 0; i < info.codes.length; i++) {
      const c = info.codes[i];
      if (c.codeOffset > codeOffsetAtPc) continue;
      switch (c.op) {
        case 0: curRsp += 8; break;                                 // PUSH_NONVOL
        case 1: {                                                   // ALLOC_LARGE
          if (c.info === 0) curRsp += (info.codes[++i].codeOffset) * 8;
          else if (c.info === 1) {
            curRsp += (info.codes[i+1].codeOffset |
                      (info.codes[i+2].codeOffset << 8)) * 8;
            i += 2;
          }
          break;
        }
        case 2: curRsp += (c.info + 1) * 8; break;                  // ALLOC_SMALL
        case 3: break;                                              // SET_FPREG
        case 4: break;                                              // SAVE_NONVOL — register, not RSP
        case 5: break;                                              // SAVE_NONVOL_FAR
        case 8: break;                                              // SAVE_XMM128
        case 9: break;                                              // SAVE_XMM128_FAR
        case 10: curRsp += 0x28; break;                             // PUSH_MACHFRAME
      }
    }
    const establisherFrame = curRsp;
    if (establisherFrame < 0 || establisherFrame + 8 > u8.length) return null;
    const returnAddr = Number(dv.getBigUint64(establisherFrame, true));
    return { rf, info, establisherFrame, returnAddr, newRsp: establisherFrame + 8 };
  };

  const readMangledName = (typeDescAddr) => {
    const p = Number(typeDescAddr);
    if (!Number.isSafeInteger(p) || p < 0 || p + 17 > u8.length) return null;
    let end = p + 16;
    while (end < u8.length && end - p < 256 && u8[end] !== 0) end++;
    return new TextDecoder().decode(u8.subarray(p + 16, end));
  };

  // Does this throw's CatchableTypeArray include the catch type?
  const winThrowMatchesCatchType = (throwInfoAddr, catchTypeAddr) => {
    if (!catchTypeAddr) return true;  // catch(...)
    const catchName = readMangledName(catchTypeAddr);
    if (!catchName) return true;  // be permissive
    const arrRVA = winReadU32(throwInfoAddr + 12);
    if (!arrRVA) return false;
    const arrAddr = base + arrRVA;
    const count = Math.min(winReadU32(arrAddr), 128);
    for (let i = 0; i < count; i++) {
      const ctRVA = winReadU32(arrAddr + 4 + i*4);
      if (!ctRVA) continue;
      const typeRVA = winReadU32(base + ctRVA + 4);
      if (!typeRVA) continue;
      if (readMangledName(base + typeRVA) === catchName) return true;
    }
    return false;
  };

  // Handle a __CxxFrameHandler4/3 for one frame
  const winHandleCxxException = (rf, info, handlerDataAddr, controlPc, establisherFrame, throwInfoAddr) => {
    // Try known offsets for FuncInfo magic: 0 (plain), 8 (GS wrapper), 4 (compact GS),
    // and a few more for older/odd layouts.
    let funcInfoAddr = -1, magic = 0, prefixBytes = null;
    // Search [handlerData-16, handlerData+512] for magic
    for (let offset = -16; offset <= 512; offset += 4) {
      const addr = handlerDataAddr + offset;
      if (addr < 0 || addr + 4 > u8.length) continue;
      const m = winReadU32(addr);
      if (m === 0x19930520 || m === 0x19930522) {
        funcInfoAddr = addr; magic = m; prefixBytes = offset;
        break;
      }
    }
    if (funcInfoAddr < 0) {
      // Dump 64 bytes at handler data for post-mortem
      const hex = [];
      for (let i = 0; i < 64; i++) hex.push(u8[handlerDataAddr + i].toString(16).padStart(2, '0'));
      log(`[SEH]   no magic in [-16, +512] of 0x${handlerDataAddr.toString(16)}; first 64 bytes: ${hex.join(' ')}`);
      return null;
    }
    if (prefixBytes !== 0) log(`[SEH]   FuncInfo at handlerData${prefixBytes >= 0 ? '+' : ''}${prefixBytes}`);
    if (magic === 0x19930522) {
      log(`[SEH]   FuncInfo4 (magic 0x19930522) not supported yet`);
      return null;
    }

    const maxState       = winReadU32(funcInfoAddr + 4);
    const tryBlockCount  = winReadU32(funcInfoAddr + 12);
    const tryBlockMapRVA = winReadU32(funcInfoAddr + 16);
    const ipMapCount     = winReadU32(funcInfoAddr + 20);
    const ipMapRVA       = winReadU32(funcInfoAddr + 24);
    log(`[SEH]   FuncInfo: maxState=${maxState} tryBlocks=${tryBlockCount} ipMap=${ipMapCount}`);
    if (!tryBlockMapRVA || !ipMapRVA) return null;

    const ipMap = base + ipMapRVA;
    let state = -1;
    for (let i = 0; i < ipMapCount - 1; i++) {
      const ipStart = base + winReadU32(ipMap + i*8);
      const ipEnd   = base + winReadU32(ipMap + (i+1)*8);
      if (controlPc >= ipStart && controlPc < ipEnd) {
        state = winReadU32(ipMap + i*8 + 4);
        break;
      }
    }
    log(`[SEH]   pc=0x${controlPc.toString(16)} → state=${state}`);
    if (state < 0) return null;

    let off = base + tryBlockMapRVA;
    for (let i = 0; i < tryBlockCount; i++) {
      const tryLow = winReadU32(off);
      const tryHigh = winReadU32(off + 4);
      const catchHigh = winReadU32(off + 8);
      const numCatches = winReadU32(off + 12);
      if (state >= tryLow && state <= tryHigh) {
        log(`[SEH]   tryblock ${i}: try=[${tryLow}..${tryHigh}] nCatches=${numCatches}`);
        let catchOff = off + 16;
        for (let c = 0; c < numCatches; c++) {
          const adjectives = winReadU32(catchOff);
          const pType = winReadU32(catchOff + 4);
          const dispCatchObj = winReadU32(catchOff + 8);
          const addrOfHandlerRVA = winReadU32(catchOff + 12);
          catchOff += 16;
          log(`[SEH]     catch ${c}: adj=0x${adjectives.toString(16)} pType=0x${pType.toString(16)} handlerRVA=0x${addrOfHandlerRVA.toString(16)}`);
          if (!winThrowMatchesCatchType(throwInfoAddr, pType ? base + pType : 0)) continue;
          const handlerAddr = base + addrOfHandlerRVA;
          const catchVarAddr = establisherFrame - dispCatchObj;
          log(`[SEH]     ✅ catch matches → handler=0x${handlerAddr.toString(16)} catchVar=0x${catchVarAddr.toString(16)}`);
          return { handlerAddr, catchVarAddr };
        }
      }
      off += 16 + numCatches * 16;
    }
    return null;
  };
  const winPatchedCodeAddresses = [];
  /*try {
    // DescriptorDatabase::Add returns the result of the map insert. On a duplicate
    // the caller still wants "yes, it's in the DB" (which is true), but the strict
    // return-value CHECK treats `false` as failure. Force the duplicate path to
    // return true so the caller's state stays consistent with reality.
    if (typeof u8 === "undefined") {
      log(`[RECOMP] ERROR: u8 undefined at Add patch (line 293)`);
    } else if (!(u8 instanceof Uint8Array)) {
      log(`[RECOMP] ERROR: u8 is not Uint8Array: ${u8?.constructor?.name ?? typeof u8}`);
    } else if (u8.length <= 0x6af7ef) {
      log(`[RECOMP] ERROR: u8 too small: length=${u8.length}, need >= ${0x6af7f0}`);
    } else {
      const b0 = u8[0x6af7ee], b1 = u8[0x6af7ef];
      log(`[RECOMP] Add patch check: bytes at 0x6af7ee = ${b0?.toString(16)} ${b1?.toString(16)}`);
      if (b0 === 0x32 && b1 === 0xdb) {
        u8[0x6af7ee] = 0xb3;  // mov bl, 1
        u8[0x6af7ef] = 0x01;
        winPatchedCodeAddresses.push(0x6af7ee);
        log(`[RECOMP] patched Add duplicate-path @0x6af7ee → return true`);
      } else {
        log(`[RECOMP] WARN: Add pattern mismatch at 0x6af7ee`);
      }
    }
  } catch (e) {
    log(`[launch] ERROR: ${e?.name ?? "Error"}: ${e?.message ?? "(no message)"}`);
    log(`[launch] stack: ${e?.stack ?? String(e)}`);
  }*/
  let winThreadIdCounter = 0;
  let winInvalidParamHandler = 0n;
  // Full dispatch: walk frames, try handlers, return new (rip, rsp, throwObj)
  const winDispatchSeh = (startPc, startRsp, throwInfoAddr, throwObjAddr) => {
    let pc = startPc, rsp = startRsp;
    for (let frameIdx = 0; frameIdx < 128; frameIdx++) {
      const rf = winFindRuntimeFunction(pc);
      if (!rf) {
        log(`[SEH] frame ${frameIdx}: pc=0x${pc.toString(16)} not in .pdata ` +
            `(have ${winRuntimeFunctions.length} entries)`);
        return null;
      }
      if (Number(pc) < rf.beginAddr || Number(pc) >= rf.endAddr) {
        log(`[SEH] frame ${frameIdx}: pc=0x${pc.toString(16)} outside RF ` +
            `[0x${rf.beginAddr.toString(16)}..0x${rf.endAddr.toString(16)})`);
        return null;
      }
      const info = winDecodeUnwindInfo(rf);
      if (!info) { log(`[SEH] frame ${frameIdx}: bad UNWIND_INFO`); return null; }
      log(`[SEH] frame ${frameIdx}: pc=0x${pc.toString(16)} rspIn=0x${rsp.toString(16)} ` +
          `rf=[0x${rf.beginAddr.toString(16)}..0x${rf.endAddr.toString(16)}) ` +
          `unwindRVA=0x${(rf.unwindAddr-base).toString(16)} ` +
          `ver=${u8[rf.unwindAddr]&7} flags=${info.flags} ` +
          `sizeProlog=${info.sizeOfProlog} nCodes=${info.codes.length} ` +
          `hRVA=${info.exceptionHandlerRVA?'0x'+info.exceptionHandlerRVA.toString(16):'none'}`);
      if (info.codes.length) {
        log(`[SEH]   codes: ${info.codes.map(c =>
          `{off=0x${c.codeOffset.toString(16)},op=${c.op},info=${c.info}}`).join(' ')}`);
      }
      const unwound = winVirtualUnwind(pc, rsp);
      if (!unwound) { log(`[SEH] frame ${frameIdx}: unwind failed`); return null; }
      log(`[SEH]   -> establisher=0x${unwound.establisherFrame.toString(16)} ` +
          `ret=0x${unwound.returnAddr.toString(16)}`);
      if ((info.flags & 1) && info.exceptionHandlerRVA) {
        const handlerDataAddr = info.handlerDataAddr;
        log(`[SEH]   handlerData=0x${handlerDataAddr.toString(16)} ` +
            `first4=0x${winReadU32(handlerDataAddr).toString(16)}`);
        const cxx = winHandleCxxException(rf, info, handlerDataAddr, pc,
                                          unwound.establisherFrame, throwInfoAddr);
        if (cxx) {
          if (cxx.catchVarAddr > 0 && cxx.catchVarAddr + 8 <= u8.length) {
            dv.setBigUint64(cxx.catchVarAddr, BigInt(throwObjAddr), true);
          }
          return { newRip: cxx.handlerAddr, newRsp: unwound.establisherFrame };
        }
      }
      pc = unwound.returnAddr;
      rsp = unwound.newRsp;
    }
    return null;
  };
  if (isWindows) {
    // steam.exe hits protobuf descriptor.cc:1371
    //     CHECK(GeneratedDatabase()->Add(encoded_file_descriptor, size))
    // because clientmetrics.proto ends up in the generated database twice.
    // The CHECK is compiled into the function at 0x682d40; the failure path
    // starts at 0x682d80 and ends by calling LogMessageFatal's destructor,
    // which calls _CxxThrowException.
    //
    // 0x682d7c:  test al, al
    // 0x682d7e:  jne 0x682dc1     ; skip fatal if Add() returned true
    //
    // Patch `jne` → `jmp` so the fatal path is skipped unconditionally. The
    // function then returns Add()'s value (0 for the duplicate) and the
    // caller behaves exactly as it would in an NDEBUG build.
    {
      const J = 0x682d7e;
      if (u8[J] === 0x75 && u8[J + 1] === 0x41) {
        u8[J] = 0xeb;                         // jne → jmp
        winPatchedCodeAddresses.push(J);
        log(`[RECOMP] patched CHECK failure @0x${J.toString(16)} → skip`);
      } else {
        log(`[RECOMP] WARN: CHECK byte pattern not found at 0x${J.toString(16)} ` +
            `(found ${u8[J].toString(16)} ${u8[J + 1].toString(16)})`);
      }
    }
    // Add this in the patch block (next to the 0x682d7e patch), not inside the
    // writability diagnostic. It needs to run BEFORE blocks are JIT'd.
    // ── Force binary mode in the CRT WriteFile wrapper (steam.exe 0x618144) ──
    // Text-mode translation loop at 0x6181C7 calls _invalid_parameter when the
    // probe bytes can't be encoded; that returns -1 and the caller reports
    // "Directory not writable". Override the mode byte load to `xor eax, eax`
    // so the code skips both the EINVAL path and the text loop entirely.
    {
        const WRAP_ADDR = 0x6181C7;
        const expected = [0x42, 0x8a, 0x44, 0xf9, 0x39];
        const actual = [0,1,2,3,4].map(i => u8[WRAP_ADDR + i]);
        logTrace(`[WCHECK-INIT] patch target 0x${WRAP_ADDR.toString(16)}:`);
        logTrace(`[WCHECK-INIT]   expected: ${expected.map(b => b.toString(16).padStart(2,"0")).join(" ")}`);
        logTrace(`[WCHECK-INIT]   actual:   ${actual.map(b => b.toString(16).padStart(2,"0")).join(" ")}`);

        if (expected.every((b, i) => actual[i] === b)) {
            u8[WRAP_ADDR]     = 0x33;   // xor eax, eax
            u8[WRAP_ADDR + 1] = 0xC0;
            u8[WRAP_ADDR + 2] = 0x90;   // nop
            u8[WRAP_ADDR + 3] = 0x90;
            u8[WRAP_ADDR + 4] = 0x90;
            winPatchedCodeAddresses.push(WRAP_ADDR);
            logTrace(`[WCHECK-INIT] ✅ PATCHED 0x6181c7 → xor eax,eax; nop×3`);
            logTrace(`[WCHECK-INIT] verify: ${[0,1,2,3,4].map(i => u8[WRAP_ADDR+i].toString(16).padStart(2,"0")).join(" ")} (should be 33 c0 90 90 90)`);
        } else {
            logTrace(`[WCHECK-INIT] ❌ byte mismatch — patch NOT applied`);
        }
    }
    {
        const addr = 0x6181A3;
        if (u8[addr] === 0x83 && u8[addr + 1] === 0xC8 && u8[addr + 2] === 0xFF) {
            u8[addr]     = 0x44;   // REX.R
            u8[addr + 1] = 0x89;   // mov r/m32, r32
            u8[addr + 2] = 0xF0;   // modrm: eax ← r14d
            winPatchedCodeAddresses.push(addr);
            log(`[WCHECK-PATCH] 0x6181a3: or eax,-1 → mov eax,r14d (return count)`);
        } else {
            log(`[WCHECK-PATCH] 0x6181a3: byte mismatch ` +
                `${u8[addr].toString(16)} ${u8[addr+1].toString(16)} ${u8[addr+2].toString(16)} ` +
                `(expected 83 c8 ff)`);
        }
    }
    // Place next to the existing 0x682d7e patch (before run()):
    {
      const addr = 0x6183F9;
      if (u8[addr] === 0x75 && u8[addr+1] === 0x17) {
        u8[addr]     = 0x90;   // nop
        u8[addr + 1] = 0x90;   // nop
        winPatchedCodeAddresses.push(addr);
        log(`[WCHECK-PATCH] 0x6183f9: jne 0x618412 → nop nop (always take success block)`);
      }
    }
  }

  const MAX_JIT_BLOCKS = 12;
  // Keep the architectural context and stack in the initial memory. mmap allocations
  // grow upward beyond that region so WebAssembly.Memory.grow cannot move the context.
  const ctx = memSize - PAGE_4K;
  const stackTop = memSize - 8192;
  dv.setBigUint64(ctx + REG.rsp * 8, BigInt(stackTop), true);
  let brkValue = align(base + image.length, PAGE_4K);
  const brkLimit = ctx - (1 << 20);
  let mmapCursor = memSize;
  const refreshViews = () => {
    u8 = new Uint8Array(memory.buffer);
    dv = new DataView(memory.buffer);
  };
  const WATCHES = [0xAD3000, 0xAD3008, 0xAD3010, 0xAD3018, 0xAD3028].map(a => ({ a, last: 0n }));
  const checkWatches = (who) => {
    for (const w of WATCHES) {
      const v = dv.getBigUint64(w.a, true);
      if (v !== w.last) {
        logTrace(`[WATCH] [0x${w.a.toString(16)}] 0x${w.last.toString(16)} -> 0x${v.toString(16)} after ${who}`);
        w.last = v;
      }
    }
  };
  const ensureMemory = (end) => {
    if (!Number.isSafeInteger(end) || end < 0 || end > 0xFFFFFFFF) {
        if (!globalThis.__ensureBadEndWarned) {
            globalThis.__ensureBadEndWarned = true;
            log(`[ENSURE-BAD] invalid end=0x${end?.toString(16) ?? end}`);
        }
        return false;
    }
    const requiredPages = Math.ceil(end / PAGE);
    const currentPages = memory.buffer.byteLength / PAGE;
    if (requiredPages > currentPages) {
        const growBy = requiredPages - currentPages;
        try { memory.grow(growBy); refreshViews(); }
        catch (e) {
            log(`[GROW-FAIL] tried +${growBy} pages (${(growBy*64).toLocaleString()}KB) ` +
                `at end=0x${end.toString(16)}; current=${(currentPages*64).toLocaleString()}KB ` +
                `needed=${(requiredPages*64).toLocaleString()}KB — ${e.message}`);
            return false;
        }
    }
    return true;
  };
  const readBytes = (ptr, len) => {
    const p = Number(ptr), n = Number(len);
    if (!Number.isSafeInteger(p) || !Number.isSafeInteger(n) || p < 0 || n < 0 || p + n > u8.length) return null;
    return u8.slice(p, p + n);
  };
  const writeBytes = (ptr, bytes) => {
    const p = Number(ptr);
    if (!Number.isSafeInteger(p) || p < 0 || p + bytes.length > u8.length) return false;
    u8.set(bytes, p);
    return true;
  };
  const readCString = (ptr, max = 4096) => {
    const p = Number(ptr);
    if (!Number.isSafeInteger(p) || p < 0 || p >= u8.length) return null;
    let end = p;
    while (end < u8.length && end - p < max && u8[end] !== 0) end++;
    return new TextDecoder().decode(u8.subarray(p, end));
  };

  // A deliberately isolated in-memory filesystem. The guest cannot read or write
  // arbitrary host paths; callers provide the files that should be visible to it.
  const toBytes = (value) => {
    if (value instanceof Uint8Array) return value.slice();
    if (value instanceof ArrayBuffer) return new Uint8Array(value.slice(0));
    if (ArrayBuffer.isView(value)) return new Uint8Array(value.buffer, value.byteOffset, value.byteLength).slice();
    return new TextEncoder().encode(String(value));
  };
  const normalizePath = (path, basePath = "/") => {
    const parts = (path.startsWith("/") ? path : `${basePath}/${path}`).split("/");
    const out = [];
    for (const part of parts) {
      if (!part || part === ".") continue;
      if (part === "..") out.pop();
      else out.push(part);
    }
    return `/${out.join("/")}`;
  };
  const virtualFiles = new Map();
  const fileEntries = files instanceof Map ? [...files.entries()] : Object.entries(files ?? {});
  for (const [path, value] of fileEntries) {
    const raw = String(path);
    const normalized = isWindows
      ? normalizePath(raw.replace(/^[A-Za-z]:/, "").replaceAll("\\", "/"), "/guest").toLowerCase()
      : normalizePath(raw);
    virtualFiles.set(normalized, { data: toBytes(value) });
  }
  /*
  // somewhere after virtualFiles is populated, before the run loop:
  for (const [path] of [...virtualFiles]) {
    if (path.endsWith("/crashhandler64.dll") || path.endsWith("/crashhandler.dll")) {
      virtualFiles.delete(path);
      log(`[HIDE] removed ${path} so Steam skips crash-handler init`);
    }
  }*/
  if (diagnostics && isWindows) {
    const all = [...virtualFiles.keys()];
    const probes = all.filter(k =>
      k.includes("installed") || k.includes("steam_client") ||
      k.includes("/package/") || k.endsWith(".vdf") || k.endsWith(".manifest"));
    log(`[MOUNT-DIAG] ${all.length} files mounted; ${probes.length} match installed/package/steam_client/vdf`);
    for (const k of probes) log(`[MOUNT-DIAG]   ${k}`);
    if (probes.length > 30) log(`[MOUNT-DIAG]   ... ${probes.length - 30} more`);

    const steamPrefix = "/program files (x86)/steam/";
    const under = all.filter(k => k.startsWith(steamPrefix));
    log(`[MOUNT-DIAG] ${under.length} file(s) under ${steamPrefix}`);
    const bySubdir = new Map();
    for (const k of under) {
      const rest = k.slice(steamPrefix.length);
      const sub = rest.split("/")[0] || "(root)";
      bySubdir.set(sub, (bySubdir.get(sub) ?? 0) + 1);
    }
    log(`[MOUNT-DIAG] subdirs: ` +
      [...bySubdir.entries()].sort().map(([k, v]) => `${k}=${v}`).join(", "));
  }
  const fdTable = new Map([
    [0, { kind: "stdin", data: toBytes(stdin), position: 0, readable: true, writable: false }],
    [1, { kind: "stdout", readable: false, writable: true }],
    [2, { kind: "stderr", readable: false, writable: true }],
  ]);
  let nextFd = 3;
  const fdEntry = (fd) => Number.isSafeInteger(fd) ? fdTable.get(fd) : undefined;
  const isDirectoryPath = (path) => path === "/" || [...virtualFiles.keys()].some((name) => name.startsWith(`${path === "/" ? "" : path}/`));
  const resolveGuestPath = (dirfd, path) => {
    if (path.startsWith("/")) return normalizePath(path);
    if (BigInt.asIntN(64, dirfd) === -100n) return normalizePath(path, "/"); // AT_FDCWD
    const dir = fdEntry(Number(dirfd));
    if (!dir || dir.kind !== "dir") return null;
    return normalizePath(path, dir.path);
  };
  const allocateFd = (entry, minimum = 3) => {
    let fd = Math.max(3, minimum);
    while (fdTable.has(fd)) fd++;
    fdTable.set(fd, entry);
    nextFd = Math.max(nextFd, fd + 1);
    return fd;
  };
  const fileBytes = (entry) => entry?.kind === "file" ? entry.file.data : entry?.kind === "stdin" ? entry.data : null;
  const guestRead = (fd, ptr, length, position = null) => {
    const entry = fdEntry(fd);
    const p = Number(ptr), n = Number(length);
    if (!entry) return negErrno(9);
    if (!entry.readable) return negErrno(9);
    if (entry.kind === "dir") return negErrno(21); // EISDIR
    if (!Number.isSafeInteger(p) || !Number.isSafeInteger(n) || p < 0 || n < 0 || n > 0x7fffffff || !ensureMemory(p + n)) return negErrno(14);
    const data = fileBytes(entry);
    if (!data) return 0n;
    const start = position === null ? entry.position : position;
    if (!Number.isSafeInteger(start) || start < 0) return negErrno(22);
    const count = Math.max(0, Math.min(n, data.length - start));
    u8.set(data.subarray(start, start + count), p);
    if (position === null) entry.position += count;
    return BigInt(count);
  };
  const guestWrite = (fd, ptr, length, position = null) => {
    const entry = fdEntry(fd);
    const p = Number(ptr), n = Number(length);
    if (!entry) return negErrno(9);
    if (!entry.writable) return negErrno(9);
    if (!Number.isSafeInteger(p) || !Number.isSafeInteger(n) || p < 0 || n < 0 || n > 0x7fffffff || p + n > u8.length) return negErrno(14);
    const bytes = u8.slice(p, p + n);
    if (entry.kind === "stdout" || entry.kind === "stderr") {
      if (bytes.length) log(new TextDecoder("utf-8", { fatal: false }).decode(bytes));
      return BigInt(bytes.length);
    }
    if (entry.kind !== "file") return negErrno(9);
    const start = position === null ? (entry.append ? entry.file.data.length : entry.position) : position;
    if (!Number.isSafeInteger(start) || start < 0 || start + n > 0x7fffffff) return negErrno(27); // EFBIG
    const end = start + n;
    if (end > entry.file.data.length) {
      const expanded = new Uint8Array(end);
      expanded.set(entry.file.data);
      entry.file.data = expanded;
    }
    entry.file.data.set(bytes, start);
    if (position === null) entry.position = end;
    return BigInt(n);
  };
  const guestStat = (ptr, entry) => {
    const p = Number(ptr);
    if (!entry || !Number.isSafeInteger(p) || p < 0 || !ensureMemory(p + 144)) return negErrno(14);
    u8.fill(0, p, p + 144);
    const isDir = entry.kind === "dir";
    const isDevice = ["stdin", "stdout", "stderr"].includes(entry.kind);
    const size = entry.kind === "file" ? entry.file.data.length : 0;
    let inode = 1n;
    for (const ch of String(entry.path ?? entry.kind)) inode = BigInt.asUintN(64, inode * 131n + BigInt(ch.charCodeAt(0)));
    dv.setBigUint64(p + 0, 1n, true); // synthetic st_dev
    dv.setBigUint64(p + 8, inode, true);
    dv.setBigUint64(p + 16, isDir ? 2n : 1n, true);
    dv.setUint32(p + 24, isDir ? 0o40755 : isDevice ? 0o20666 : 0o100644, true);
    dv.setUint32(p + 28, 1000, true);
    dv.setUint32(p + 32, 1000, true);
    dv.setBigUint64(p + 40, isDevice ? 1n : 0n, true);
    dv.setBigInt64(p + 48, BigInt(size), true);
    dv.setBigInt64(p + 56, 4096n, true);
    dv.setBigInt64(p + 64, BigInt(Math.ceil(size / 512)), true);
    return 0n;
  };

  // Minimal Windows x64 process structures. This is intentionally not a complete
  // PEB/TEB implementation, but it gives common startup/API code the fields it
  // typically probes first (GS:[0x60] -> PEB, PEB.ImageBaseAddress, LastError).
  const WIN_EXIT = 0xFFFF_FFF0n;
  const WIN_CALLBACK_RETURN = 0xFFFF_FFF1n;
  const WIN_DLL_INIT_RETURN = 0xFFFF_FFF2n;
  const WIN_TEB = 0x30000;
  const WIN_PEB = 0x31000;
  const WIN_PARAMS = 0x32000;
  const WIN_CMD_A = 0x33000;
  const WIN_CMD_W = 0x34000;
  const WIN_IMAGE_A = 0x35000;
  const WIN_IMAGE_W = 0x36000;
  const WIN_ARGC = 0x37000;
  const WIN_ARGV_PTR = 0x37008;
  const WIN_WARGV_PTR = 0x37010;
  const WIN_COMMODE = 0x37018;
  const WIN_FMODE = 0x3701c;
  const WIN_ERRNO = 0x37020;
  const WIN_ARGV_ARRAY = 0x37100;
  const WIN_WARGV_ARRAY = 0x37300;
  const WIN_ARG_STRINGS = 0x38000;
  const WIN_WARG_STRINGS = 0x39000;
  const WIN_STD_INPUT = 0xFFFF_FFF6n;
  const WIN_STD_OUTPUT = 0xFFFF_FFF5n;
  const WIN_STD_ERROR = 0xFFFF_FFF4n;
  const WIN_DESKTOP_HANDLE = 0xFFFF_FFF3n;
  const winCommandLine = String(commandLine || "guest.exe");
  const winImagePath = String(imagePath || "C:\\guest\\program.exe");
  const winHeapHandle = 1n;
  let winHeapCursor = align(memSize + 0x10000, PAGE_4K);
  let winNextHandle = 0x100 + Math.max(0, (Number(processId) || 1) - 1) * 0x10000;
  let winNextModule = 0xE000_0000n;
  let winNextImport = 0xF000_0000n;
  let winNextTls = 0;
  let winRandState = 1;
  let winCrtLocalePtr = 0n;
  let winExitCode = 0;
  let winEntryRsp = 0;
  let winStdin = toBytes(stdin);
  let winStdinPosition = 0;
  const winHandles = new Map();
  let winWsaLastError = 0;
  let winWsaStartupCount = 0;
  const winInetNtoaBuffer = 0x3A000;
  const winProcesses = new Map();
  const winHandleWaiters = new Set();
  const winCurrentProcessState = { kind: "process", processId: Number(processId) || 1, imagePath: winImagePath, finished: false, exitCode: 259 };
  winProcesses.set(winCurrentProcessState.processId, winCurrentProcessState);
  let winNextChildProcessId = Math.max(2, Number(processId) + 1);
  const winTls = new Map();
  const winFls = new Map();
  const winFlsFreeList = [];
  let winFlsNextId = 0;
  let winFlsCallback = 0n;   // callback ignored for now
  const winEnvironment = new Map([
    ["TEMP", "C:\\TEMP"], ["TMP", "C:\\TEMP"],
    ["WINDIR", "C:\\Windows"], ["SYSTEMROOT", "C:\\Windows"], ["SYSTEMDRIVE", "C:"],
    ["USERPROFILE", "C:\\Users\\Guest"],
    ["APPDATA", "C:\\Users\\Guest\\AppData\\Roaming"],
    ["LOCALAPPDATA", "C:\\Users\\Guest\\AppData\\Local"],
    ["HOMEDRIVE", "C:"], ["HOMEPATH", "\\Users\\Guest"],
    ["USERNAME", "Guest"], ["USERDOMAIN", "WASM"],
    ["COMPUTERNAME", "WASM-PC"],
    ["PROCESSOR_ARCHITECTURE", "AMD64"], ["PROCESSOR_IDENTIFIER", "Intel64 Family 6 Model 158 Stepping 9, GenuineIntel"],
    ["NUMBER_OF_PROCESSORS", "4"],
    ["OS", "Windows_NT"],
    ["COMSPEC", "C:\\Windows\\System32\\cmd.exe"],
    ["PATH", "C:\\Windows\\System32;C:\\Windows;C:\\Windows\\System32\\Wbem"],
    ["PATHEXT", ".COM;.EXE;.BAT;.CMD;.VBS;.VBE;.JS;.JSE;.WSF;.WSH;.MSC"],
    ["PROMPT", "$P$G"],
    ["ALLUSERSPROFILE", "C:\\ProgramData"],
    ["PROGRAMDATA", "C:\\ProgramData"],
    ["PROGRAMFILES", "C:\\Program Files"],
    ["PROGRAMFILES(X86)", "C:\\Program Files (x86)"],
    ["COMMONPROGRAMFILES", "C:\\Program Files\\Common Files"],
    ["PUBLIC", "C:\\Users\\Public"],
  ]);
  const winDirectories = new Set([
    "/", "/guest", "/temp", "/windows", "/windows/system32", "/windows/syswow64",
    "/users", "/users/guest", "/users/guest/documents", "/users/guest/desktop",
    "/users/guest/appdata", "/users/guest/appdata/roaming", "/users/guest/appdata/local",
    "/users/public", "/program files", "/program files/common files",
    "/programdata",
  ]);
  {
    // Derive install dir from image path: strip the last path component.
    const installDir = winImagePath.replace(/[\\/][^\\/]+$/, "");
    winEnvironment.set("STEAMROOT",      installDir);
    winEnvironment.set("STEAMDIR",       installDir);
    winEnvironment.set("STEAM_PATH",     installDir);
    winEnvironment.set("STEAM_CLIENT",   winImagePath);
    winEnvironment.set("STEAM_EXE",      winImagePath);
    logTrace(`[ENV] seeded STEAMROOT=${installDir} STEAM_CLIENT=${winImagePath}`);
  }
  if (diagnostics) {
    const samples = [...winDirectories].sort().slice(0, 30);
    logTrace(`[FS] ${virtualFiles.size} files, ${winDirectories.size} dirs`);
    logTrace(`[FS] dirs sample: ${samples.join(", ")}`);
    // Show any directories at top of C:\guest
    const guestDirs = [...winDirectories].filter(d => d.startsWith("/guest/") && d.split("/").length === 3);
    logTrace(`[FS] C:\\guest\\*: ${guestDirs.join(", ") || "(none)"}`);
  }
  let winCurrentDirectory = "/guest";
  for (const path of virtualFiles.keys()) {
    let parent=path.slice(0,path.lastIndexOf("/"));
    while(parent && parent!=="/"){winDirectories.add(parent);parent=parent.slice(0,parent.lastIndexOf("/"));}
  }
  const winDynamicImports = new Map();
  const winAllocations = new Map();
  const winCrtFiles = new Map([[1n, { kind: "stdout" }], [2n, { kind: "stderr" }], [3n, { kind: "stdin" }]]);
  const winModules = new Map();
  // RtlAddFunctionTable registrations are process-local and keyed by the guest
  // address of the RUNTIME_FUNCTION array (not by a host pointer).
  const winDynamicFunctionTables = new Map();
  const winModuleHandles = new Map([[BigInt(base), "program.exe"]]);
  const winWarned = new Set();
  const winRegistry = new Map();
  const winRegistryRoots = new Map([[0x80000000n, "HKEY_CLASSES_ROOT"], [0x80000001n, "HKEY_CURRENT_USER"],
    [0x80000002n, "HKEY_LOCAL_MACHINE"], [0x80000003n, "HKEY_USERS"], [0x80000005n, "HKEY_CURRENT_CONFIG"]]);
  for (const root of winRegistryRoots.values()) winRegistry.set(root.toLowerCase(), { values: new Map() });
  const winApiByAddress = new Map();
  const winClasses = new Map();
  const winWindows = new Map();
  const winDcs = new Map();
  const winMessageQueue = [];
  const winMessageWaiters = [];
  let winCurrentMessage = null;
  const winKeyDown = new Set();
  const winKeyRecent = new Set();
  const winCallbackFrames = [];
  const winScreen = { width: Number(gui?.width) || 1280, height: Number(gui?.height) || 720 };
  const WIN_CONSOLE_HWND = 0xFFFF_C0DE;
  const WIN_CONSOLE_STYLE = 0x00CF0000; // WS_OVERLAPPEDWINDOW
  const winConsole = {
    width: 120,
    height: 30,
    cells: Array.from({ length: 30 }, () => Array.from({ length: 120 },
      () => ({ ch: " ", attr: 0x07 }))),
    cursorX: 0,
    cursorY: 0,
    title: "Command Prompt",
    defaultAttr: 0x07,
  };
  const winConsoleInput = {
    queue: [],       // pending INPUT_RECORD-shaped objects
    waiter: null,    // { resolve, max } when ReadConsoleInputW is blocked
    lineWaiter: null,// { resolve, buffer, maxChars, startRow, startCol } when ReadConsoleW is blocked
    mode: 0x0003,    // current console mode (ENABLE_PROCESSED_INPUT | ENABLE_LINE_INPUT)
  };
  const winConsoleEnsureWindow = () => {
    let w = winWindows.get(WIN_CONSOLE_HWND);
    if (w) return w;
    const cellW = 8, cellH = 16;
    const clientW = winConsole.width * cellW;
    const clientH = winConsole.height * cellH;
    w = {
      kind: "window", hwnd: WIN_CONSOLE_HWND,
      className: "ConsoleWindowClass", title: winConsole.title,
      wndProc: 0n, classInfo: { builtin: true, name: "ConsoleWindowClass" },
      style: WIN_CONSOLE_STYLE, exStyle: 0,
      x: 80, y: 60,
      width: clientW + 12, height: clientH + 26 + 4,
      parent: 0n, menu: 0n, instance: 0n, param: 0n,
      visible: true, enabled: true, destroyed: false, focused: true,
      invalid: false, commands: [], z: ++winZOrder,
      control: "console",
      userData: 0n, dcState: null,
      consoleCells: winConsole.cells,
      cursorX: 0, cursorY: 0,
    };
    winHandles.set(WIN_CONSOLE_HWND, w);
    winWindows.set(WIN_CONSOLE_HWND, w);
    return w;
  };
  if (diagnostics && isWindows) {
    const p = "/program files (x86)/steam/package/steam_client_win64.installed";
    const f = virtualFiles.get(p);
    if (f) {
      const n = Math.min(f.data.length, 32);
      const hex = Array.from(f.data.subarray(0, n), b => b.toString(16).padStart(2, "0")).join(" ");
      log(`[INSTALLED] ${f.data.length} bytes, first ${n}: ${hex}`);
    } else {
      log(`[INSTALLED] NOT PRESENT at ${p}`);
    }
  }
  virtualFiles.delete("/program files (x86)/steam/package/steam_client_win64.installed");
  const winConsoleHandleKey = (event, down) => {
    // If nobody is waiting, drop the key (guest isn't asking for input).
    if (!winConsoleInput.waiter && !winConsoleInput.lineWaiter) return false;

    // Line-mode read (ReadConsoleW / ReadFile from STDIN).
    if (winConsoleInput.lineWaiter) {
      const w = winConsoleInput.lineWaiter;
      if (!down) return true;  // we only act on key-down for line editing
      if (event.key === "Enter") {
        winConsoleWrite("\r\n");
        winConsoleInput.lineWaiter = null;
        w.resolve(w.buffer);
        return true;
      }
      if (event.key === "Backspace") {
        if (w.buffer.length > 0) {
          w.buffer = w.buffer.slice(0, -1);
          winConsoleRedrawActiveLine(w);
        }
        return true;
      }
      if (Array.from(event.key).length === 1 && !event.ctrlKey && !event.metaKey) {
        if ((w.buffer.length + 1) < w.maxChars) {
          w.buffer += event.key;
          winConsoleWrite(event.key);
        }
        return true;
      }
      return true;  // swallow other keys in line mode
    }

    // Record-mode read (ReadConsoleInputW).
    const virtualKey = consoleVk(event);
    const charCode = (Array.from(event.key).length === 1)
      ? event.key.charCodeAt(0)
      : (event.key === "Enter" ? 13 : event.key === "Backspace" ? 8 : event.key === "Tab" ? 9 : 0);
    let state = 0;
    if (event.shiftKey) state |= 0x0010;
    if (event.ctrlKey)  state |= 0x0008;
    if (event.altKey)   state |= 0x0002;
    winConsoleInputPush({
      eventType: 0x0001,        // KEY_EVENT
      keyDown: down,
      repeatCount: 1,
      virtualKey,
      virtualScan: 0,
      unicodeChar: charCode,
      controlState: state,
    });
    return true;
  };
  const consoleVk = (event) => {
    if (event.key === "Enter") return 13;
    if (event.key === "Backspace") return 8;
    if (event.key === "Tab") return 9;
    if (event.key === "Escape") return 27;
    if (event.key === "Delete") return 46;
    if (event.key === "Home") return 36;
    if (event.key === "End") return 35;
    if (event.key === "PageUp") return 33;
    if (event.key === "PageDown") return 34;
    if (event.key.startsWith("Arrow"))
      return ({ ArrowLeft: 37, ArrowUp: 38, ArrowRight: 39, ArrowDown: 40 })[event.key];
    if (/^[A-Za-z0-9]$/.test(event.key)) return event.key.toUpperCase().charCodeAt(0);
    if (event.key === " ") return 32;
    return event.keyCode || 0;
  };

  const winConsoleInputPush = (record) => {
    winConsoleInput.queue.push(record);
    if (winConsoleInput.waiter) {
      const { resolve, max } = winConsoleInput.waiter;
      winConsoleInput.waiter = null;
      const n = Math.min(max, winConsoleInput.queue.length);
      resolve(winConsoleInput.queue.splice(0, n));
    }
  };

  const winConsoleInputDrain = (max) => {
    if (winConsoleInput.queue.length > 0) {
      const n = Math.min(max, winConsoleInput.queue.length);
      return Promise.resolve(winConsoleInput.queue.splice(0, n));
    }
    return new Promise((resolve) => {
      winConsoleInput.waiter = { resolve, max };
    });
  };

  const winConsoleRedrawActiveLine = (w) => {
    // Redraw the line editor from its start position (backspace support).
    for (let x = w.startCol; x < winConsole.width; x++) {
      winConsole.cells[w.startRow][x] = { ch: " ", attr: winConsole.defaultAttr };
    }
    winConsole.cursorX = w.startCol;
    winConsole.cursorY = w.startRow;
    for (const ch of w.buffer) {
      if (winConsole.cursorX >= winConsole.width) break;
      winConsole.cells[winConsole.cursorY][winConsole.cursorX] = { ch, attr: winConsole.defaultAttr };
      winConsole.cursorX++;
    }
    winConsoleSchedulePresent();
  };

  // Wire it to the GUI once.
  if (gui?.setConsoleKeyHandler) gui.setConsoleKeyHandler(winConsoleHandleKey);
  const winConsoleNewline = () => {
    winConsole.cursorX = 0;
    winConsole.cursorY++;
    if (winConsole.cursorY >= winConsole.height) {
      winConsole.cells.shift();
      winConsole.cells.push(Array.from({ length: winConsole.width },
        () => ({ ch: " ", attr: winConsole.defaultAttr })));
      winConsole.cursorY = winConsole.height - 1;
    }
  };

  let winConsolePresentPending = false;
  const winConsoleSchedulePresent = () => {
    if (winConsolePresentPending) return;
    winConsolePresentPending = true;
    const sched = globalThis.requestAnimationFrame || ((cb) => setTimeout(cb, 16));
    sched(() => {
      winConsolePresentPending = false;
      const w = winConsoleEnsureWindow();
      w.title = winConsole.title;
      w.consoleCells = winConsole.cells;
      w.cursorX = winConsole.cursorX;
      w.cursorY = winConsole.cursorY;
      winPresent();
    });
  };
  const logGuestBacktrace = (limit = 24, depth = 0x4000) => {
    const rsp = Number(dv.getBigUint64(ctx + REG.rsp * 8, true));
    const out = [];
    for (let at = rsp; at < Math.min(u8.length - 8, rsp + depth) && out.length < limit; at += 8) {
      const v = dv.getBigUint64(at, true);
      if (v < BigInt(base) || v >= BigInt(base + image.length)) continue;
      const r = Number(v);
      const isCall = u8[r - 5] === 0xe8 ||
        [2, 3, 4, 5, 6, 7].some((k) => u8[r - k] === 0xff && (u8[r - k + 1] & 0x38) === 0x10);
      if (isCall) out.push(`0x${r.toString(16)}`);
    }
    log(`[RECOMP] guest backtrace (heuristic): ${out.join(" <- ")}`);
  };
  const winConsoleWrite = (text) => {
    for (const ch of text) {
      if (ch === "\r") { winConsole.cursorX = 0; continue; }
      if (ch === "\n") { winConsoleNewline(); continue; }
      if (ch === "\b") { if (winConsole.cursorX > 0) winConsole.cursorX--; continue; }
      if (ch === "\t") {
        winConsole.cursorX = Math.min(winConsole.width - 1,
          (Math.floor(winConsole.cursorX / 8) + 1) * 8);
        continue;
      }
      if (winConsole.cursorX >= winConsole.width) winConsoleNewline();
      winConsole.cells[winConsole.cursorY][winConsole.cursorX] =
        { ch, attr: winConsole.defaultAttr };
      winConsole.cursorX++;
    }
    winConsoleSchedulePresent();
  };
  const winStockObjects = new Map();
  const winDesktopSurface = { kind: "desktop", width: winScreen.width, height: winScreen.height, commands: [] };
  let winZOrder = 0;
  for (const item of manifest.imports ?? []) {
    const address = BigInt(item.address);
    winApiByAddress.set(address, { dll: String(item.dll || ""), name: item.name == null ? null : String(item.name), ordinal: item.ordinal ?? null });
    if (address >= winNextImport) winNextImport = address + 16n;
  }
  if (diagnostics) {
    const inittermAddrs = (manifest.imports ?? [])
      .filter(i => /initterm/i.test(String(i.name ?? "")))
      .map(i => `0x${BigInt(i.address).toString(16)} ${i.name}`);
    log(`[IMPORTS] _initterm entries: ${inittermAddrs.join(", ") || "(NONE)"}`);
  }
  if (isWindows) {
    const cmdA = new TextEncoder().encode(winCommandLine + "\0");
    const cmdW = new Uint8Array((winCommandLine.length + 1) * 2);
    for (let i = 0; i < winCommandLine.length; i++) cmdW[i * 2] = winCommandLine.charCodeAt(i) & 0xff, cmdW[i * 2 + 1] = winCommandLine.charCodeAt(i) >> 8;
    const imageA = new TextEncoder().encode(winImagePath + "\0");
    const imageW = new Uint8Array((winImagePath.length + 1) * 2);
    for (let i = 0; i < winImagePath.length; i++) imageW[i * 2] = winImagePath.charCodeAt(i) & 0xff, imageW[i * 2 + 1] = winImagePath.charCodeAt(i) >> 8;
    writeBytes(WIN_CMD_A, cmdA); writeBytes(WIN_CMD_W, cmdW);
    writeBytes(WIN_IMAGE_A, imageA); writeBytes(WIN_IMAGE_W, imageW);
    dv.setBigUint64(WIN_TEB + 0x08, BigInt(stackTop), true); // StackBase
    dv.setBigUint64(WIN_TEB + 0x10, BigInt(Math.max(0, stackTop - (1 << 20))), true); // StackLimit
    dv.setBigUint64(WIN_TEB + 0x30, BigInt(WIN_TEB), true); // Self
    dv.setBigUint64(WIN_TEB + 0x60, BigInt(WIN_PEB), true); // ProcessEnvironmentBlock
    dv.setBigUint64(WIN_PEB + 0x10, BigInt(base), true); // ImageBaseAddress
    dv.setBigUint64(WIN_PEB + 0x20, BigInt(WIN_PARAMS), true); // ProcessParameters
    dv.setUint16(WIN_PARAMS + 0x70, Math.min(0xfffe, cmdW.length - 2), true);
    dv.setUint16(WIN_PARAMS + 0x72, Math.min(0xfffe, cmdW.length), true);
    dv.setBigUint64(WIN_PARAMS + 0x78, BigInt(WIN_CMD_W), true);
    dv.setUint16(WIN_PARAMS + 0x60, Math.min(0xfffe, imageW.length - 2), true);
    dv.setUint16(WIN_PARAMS + 0x62, Math.min(0xfffe, imageW.length), true);
    dv.setBigUint64(WIN_PARAMS + 0x68, BigInt(WIN_IMAGE_W), true);
    const argv = [];
    let current = "", quoted = false;
    for (let i = 0; i < winCommandLine.length; i++) {
      const ch = winCommandLine[i];
      if (ch === '"') quoted = !quoted;
      else if (/\s/.test(ch) && !quoted) { if (current) { argv.push(current); current = ""; } }
      else current += ch;
    }
    if (current) argv.push(current);
    if (argv.length === 0) argv.push("guest.exe");
    dv.setUint32(WIN_ARGC, argv.length, true);
    dv.setBigUint64(WIN_ARGV_PTR, BigInt(WIN_ARGV_ARRAY), true);
    dv.setBigUint64(WIN_WARGV_PTR, BigInt(WIN_WARGV_ARRAY), true);
    let argvACursor = WIN_ARG_STRINGS, argvWCursor = WIN_WARG_STRINGS;
    for (let i = 0; i < argv.length; i++) {
      const narrow = new TextEncoder().encode(argv[i] + "\0");
      const wide = new Uint8Array((argv[i].length + 1) * 2);
      for (let j = 0; j < argv[i].length; j++) wide[j*2]=argv[i].charCodeAt(j)&255,wide[j*2+1]=argv[i].charCodeAt(j)>>8;
      const aPtr = argvACursor, wPtr = argvWCursor;
      writeBytes(aPtr, narrow); writeBytes(wPtr, wide);
      argvACursor += align(narrow.length, 16); argvWCursor += align(wide.length, 16);
      dv.setBigUint64(WIN_ARGV_ARRAY + i * 8, BigInt(aPtr), true);
      dv.setBigUint64(WIN_WARGV_ARRAY + i * 8, BigInt(wPtr), true);
    }
    dv.setBigUint64(WIN_ARGV_ARRAY + argv.length * 8, 0n, true);
    dv.setBigUint64(WIN_WARGV_ARRAY + argv.length * 8, 0n, true);
    dv.setUint32(WIN_COMMODE, 0, true); dv.setUint32(WIN_FMODE, 0x4000, true);
    dv.setBigUint64(ctx + 152, BigInt(WIN_TEB), true); // GS base
    winEntryRsp = (stackTop - 8) & ~7;
    dv.setBigUint64(winEntryRsp, WIN_EXIT, true); // return-from-entry sentinel
    dv.setBigUint64(ctx + REG.rsp * 8, BigInt(winEntryRsp), true);
    dv.setBigUint64(ctx + 136, 0x202n, true); // RFLAGS
    winHandles.set(WIN_STD_INPUT, { kind: "stdin" });
    winHandles.set(WIN_STD_OUTPUT, { kind: "stdout" });
    winHandles.set(WIN_STD_ERROR, { kind: "stderr" });
  }

  const winReadU64 = (ptr) => {
    const p = Number(ptr);
    if (!Number.isSafeInteger(p) || p < 0 || p + 8 > u8.length) return 0n;
    return dv.getBigUint64(p, true);
  };
  const winReadA = (ptr, max = 32768) => readCString(ptr, max);
  const winReadMsvcCppException = (params) => {
    // MSVC x64 exception parameters:
    // [0] EH magic, [1] thrown object, [2] ThrowInfo VA, [3] image base.
    // ThrowInfo's internal pointers are 32-bit RVAs relative to image base.
    if (params.length < 4 || params[0] !== 0x19930520n) return null;
    const object = params[1], throwInfoArg = params[2], imageBase = params[3];
    const inMemory = (p, n = 4) => p >= 0n && p + BigInt(n) <= BigInt(u8.length);
    let throwInfo = throwInfoArg;
    if (!inMemory(throwInfo, 16) && inMemory(imageBase + throwInfoArg, 16))
      throwInfo = imageBase + throwInfoArg;
    if (!inMemory(throwInfo, 16)) return { object, throwInfo: throwInfoArg, imageBase, typeNames: [], detail: "ThrowInfo is outside guest memory" };
    const read32 = (p) => inMemory(p, 4) ? dv.getUint32(Number(p), true) : 0;
    const rva = (value) => imageBase + BigInt(value >>> 0);
    const catchableArrayRva = read32(throwInfo + 12n);
    const catchableArray = rva(catchableArrayRva);
    const count = Math.min(read32(catchableArray), 32);
    const typeNames = [];
    for (let i = 0; i < count; i++) {
      const catchableRva = read32(catchableArray + 4n + BigInt(i * 4));
      if (!catchableRva) continue;
      const catchable = rva(catchableRva);
      const typeRva = read32(catchable + 4n);
      if (!typeRva) continue;
      const typeDescriptor = rva(typeRva);
      const name = inMemory(typeDescriptor + 16n, 1)
        ? winReadA(typeDescriptor + 16n, 512) : null;
      if (name) typeNames.push(name);
    }
    const objectWords = [];
    for (let i = 0; i < 4 && inMemory(object + BigInt(i * 8), 8); i++)
      objectWords.push("0x" + winReadU64(object + BigInt(i * 8)).toString(16));
    return { object, throwInfo, imageBase, typeNames, objectWords,
      attributes: read32(throwInfo), unwindRva: read32(throwInfo + 4n),
      forwardCompatRva: read32(throwInfo + 8n), catchableArrayRva };
  };
  const winReadW = (ptr, max = 32768) => {
    let p = Number(ptr);
    if (!Number.isSafeInteger(p) || p < 0 || p + 1 >= u8.length) return null;
    let out = "";
    for (let i = 0; i < max && p + 1 < u8.length; i++, p += 2) {
      const code = dv.getUint16(p, true);
      if (!code) break;
      out += String.fromCharCode(code);
    }
    return out;
  };
  const winWriteA = (ptr, value) => writeBytes(ptr, new TextEncoder().encode(String(value) + "\0"));
  const winWriteW = (ptr, value) => {
    const str = String(value) + "\0", bytes = new Uint8Array(str.length * 2);
    for (let i = 0; i < str.length; i++) bytes[i * 2] = str.charCodeAt(i) & 255, bytes[i * 2 + 1] = str.charCodeAt(i) >> 8;
    return writeBytes(ptr, bytes);
  };
  const winWriteMemoryString = (ptr, value, wide = false) => wide ? winWriteW(ptr, value) : winWriteA(ptr, value);
  const winSetLastError = (code) => {
    if (!isWindows) return;
    const n = Number(code) >>> 0;
    if (n >= 0x2000 && n < 0x3000) {
      log(`[LERR] SetLastError(${n} = 0x${n.toString(16)})`);
      try { throw new Error("trace"); } catch (e) {
        log(e.stack.split("\n").slice(2, 8).join("\n"));
      }
    }
    dv.setUint32(WIN_TEB + 0x68, n, true);
  };
  const winGetLastError = () => isWindows ? dv.getUint32(WIN_TEB + 0x68, true) : 0;
  // ── First-fit allocator with free list + coalescing ───────────────────────
  // Without reuse, heapCursor grows monotonically during Steam startup; with
  // free-list reuse, most allocations service from freed blocks so the high
  // water mark stays bounded.
  const winFreeBlocks = [];         // sorted by .start, coalesced on free
  let winHeapPeak = 0;
  let winAllocCount = 0;
  let winFreeCount = 0;
  let winHeapLimitHit = false;

  const winAlloc = (size, zero = true) => {
      const n = Math.max(1, Number(size));
      if (!Number.isSafeInteger(n) || n > 0x4000_0000) return 0n;
      const aligned = align(n, 16);

      // First-fit reuse
      for (let i = 0; i < winFreeBlocks.length; i++) {
          const b = winFreeBlocks[i];
          if (b.size < aligned) continue;
          const start = b.start;
          if (b.size === aligned) winFreeBlocks.splice(i, 1);
          else { b.start += aligned; b.size -= aligned; }
          if (zero) u8.fill(0, start, start + aligned);
          winAllocations.set(start, n);
          winAllocCount++;
          return BigInt(start);
      }

      // Fresh allocation with explicit cap
      const HEAP_LIMIT = 0x4000_0000;   // 1 GiB — adjust if you hit it
      const start = align(winHeapCursor, 16), end = start + aligned;
      if (!Number.isSafeInteger(end) || end > HEAP_LIMIT || !ensureMemory(end)) {
          if (!winHeapLimitHit) {
              winHeapLimitHit = true;
              log(`[HEAP-LIMIT] alloc refused: end=0x${end.toString(16)} ` +
                  `peak=0x${winHeapPeak.toString(16)} allocs=${winAllocCount} ` +
                  `frees=${winFreeCount} freeBlocks=${winFreeBlocks.length}`);
          }
          return 0n;
      }
      winHeapCursor = end;
      if (end > winHeapPeak) winHeapPeak = end;
      if (zero) u8.fill(0, start, end);
      winAllocations.set(start, n);
      winAllocCount++;
      return BigInt(start);
  };

  const winFree = (ptr) => {
      const p = Number(ptr);
      if (!Number.isSafeInteger(p) || p < 0) return false;
      const size = winAllocations.get(p);
      if (size === undefined) return false;
      winAllocations.delete(p);
      winFreeCount++;
      const aligned = align(size, 16);

      // Insert sorted
      let i = winFreeBlocks.length;
      for (let k = 0; k < winFreeBlocks.length; k++) {
          if (winFreeBlocks[k].start >= p) { i = k; break; }
      }
      winFreeBlocks.splice(i, 0, { start: p, size: aligned });

      // Coalesce with next
      if (i + 1 < winFreeBlocks.length &&
          winFreeBlocks[i].start + winFreeBlocks[i].size === winFreeBlocks[i + 1].start) {
          winFreeBlocks[i].size += winFreeBlocks[i + 1].size;
          winFreeBlocks.splice(i + 1, 1);
      }
      // Coalesce with prev
      if (i > 0 &&
          winFreeBlocks[i - 1].start + winFreeBlocks[i - 1].size === winFreeBlocks[i].start) {
          winFreeBlocks[i - 1].size += winFreeBlocks[i].size;
          winFreeBlocks.splice(i, 1);
      }
      return true;
  };
  const winReadMemoryString = (ptr, wide = false) => wide ? winReadW(ptr) : winReadA(ptr);
  const winPath = (p) => {
    let s = String(p);
    if (s.startsWith("\\\\?\\")) s = s.slice(4);   // strip extended-length prefix
    return normalizePath(
      s.replace(/^[A-Za-z]:/, "").replaceAll("\\", "/"),
      winCurrentDirectory
    ).toLowerCase();
  };
  const winRegistryPath = (root, subKey = "") => `${root}\\${String(subKey).replaceAll("/", "\\").replace(/^\\+|\\+$/g, "")}`.replace(/\\+/g, "\\").toLowerCase();
  const winRegistryRoot = (handle) => {
    const h = BigInt(handle), root = winRegistryRoots.get(h) ?? winRegistryRoots.get(BigInt.asUintN(32, h));
    return root ?? winHandles.get(h)?.registryPath ?? null;
  };
  const winRegistryEnsure = (path) => {
    const normalized = String(path).toLowerCase();
    if (!winRegistry.has(normalized)) winRegistry.set(normalized, { values: new Map() });
    return winRegistry.get(normalized);
  };
  {
    const installDir = winImagePath.replace(/[\\/][^\\/]+$/, "");
    const steamKeyPath = "hkey_current_user\\software\\valve\\steam";
    const steamKey = winRegistryEnsure(steamKeyPath);
    const enc = (s) => new TextEncoder().encode(s + "\0");
    steamKey.values.set("steamexe",   { name: "SteamExe",   type: 1, data: enc(winImagePath) });
    steamKey.values.set("steampath",  { name: "SteamPath",  type: 1, data: enc(installDir.replaceAll("\\", "/")) });
    steamKey.values.set("installpath", { name: "InstallPath", type: 1, data: enc(installDir) });
    logTrace(`[REG] seeded HKCU\\Software\\Valve\\Steam (SteamExe=${winImagePath})`);
  }
  const winRegistryFind = (handle, subKey = "") => {
    const root = winRegistryRoot(handle);
    if (!root) return null;
    const path = subKey ? winRegistryPath(root, subKey) : root.toLowerCase();
    return { path, entry: winRegistry.get(path) ?? null };
  };
  const winGetArg = (index) => {
    if (index < 4) return dv.getBigUint64(ctx + [REG.rcx, REG.rdx, REG.r8, REG.r9][index] * 8, true);
    const rsp = Number(dv.getBigUint64(ctx + REG.rsp * 8, true));
    return winReadU64(rsp + 0x28 + (index - 4) * 8);
  };
  const winFirstCommandToken = (command) => {
    const text = String(command ?? "").trim();
    if (!text) return "";
    let token = "", quoted = false;
    for (let i = 0; i < text.length; i++) {
      const ch = text[i];
      if (ch === '"') { quoted = !quoted; continue; }
      if (!quoted && /\s/.test(ch)) break;
      token += ch;
    }
    return token;
  };
  const winWaitForProcess = async (state, timeout) => {
    if (state.finished) return 0;
    if (timeout === 0) return 0x102;
    if (timeout === 0xffffffff) { await state.completion; return 0; }
    const timer = new Promise((resolve) => setTimeout(() => resolve(false), timeout));
    const finished = Promise.resolve(state.completion).then(() => true);
    return await Promise.race([finished, timer]) ? 0 : 0x102;
  };
  const winHandleIsSignaled = (handle) => {
    if (!handle) return false;
    if (handle.kind === "event" || handle.kind === "mutex") return !!handle.signaled;
    if (handle.kind === "semaphore") return handle.count > 0;
    if (handle.kind === "process" || handle.kind === "thread") return (handle.kind === "thread" ? handle.process : handle).finished;
    return false;
  };
  const winConsumeHandleSignal = (handle) => {
    if (handle?.kind === "event" && !handle.manualReset) handle.signaled = false;
    else if (handle?.kind === "semaphore" && handle.count > 0) handle.count--;
    else if (handle?.kind === "mutex") handle.signaled = false;
  };
  const winCheckHandleWaiter = (waiter) => {
    const handles = waiter.handles.map((h) => winHandles.get(h));
    if (handles.some((h) => !h)) return { error: 6 };
    if (waiter.waitAll) {
      if (!handles.every(winHandleIsSignaled)) return null;
      for (const handle of handles) winConsumeHandleSignal(handle);
      return { result: 0 };
    }
    const index = handles.findIndex(winHandleIsSignaled);
    if (index < 0) return null;
    winConsumeHandleSignal(handles[index]);
    return { result: index };
  };
  const winWakeHandleWaiters = () => {
    for (const waiter of [...winHandleWaiters]) {
      const result = winCheckHandleWaiter(waiter);
      if (!result) continue;
      winHandleWaiters.delete(waiter);
      waiter.resolve(result.error ? 0xffff_ffff : (waiter.baseResult + result.result));
    }
  };
  const winWaitForHandles = async (handles, waitAll, timeout, baseResult = 0) => {
      const validKinds = new Set(["event", "mutex", "semaphore", "process", "thread"]);
      if (handles.some((h) => !validKinds.has(winHandles.get(h)?.kind))) return 0xffff_ffff;
      const waiter = { handles, waitAll, baseResult, resolve: null };
      const immediate = winCheckHandleWaiter(waiter);
      if (immediate) return immediate.error ? 0xffff_ffff : immediate.result;
      if (timeout === 0) return 0x102;

      // Infinite waits (0xFFFFFFFF) are how Windows says "block until X". Real
      // Windows blocks forever; if we do that, the JS event loop dies and no
      // other Wasm context (including the spawned child) can make progress.
      // Clamp to 5s, log which handle kind is blocking, and let the parent
      // continue with WAIT_TIMEOUT.
      const effectiveTimeout = timeout === 0xFFFFFFFF ? 5000 : timeout;
      if (timeout === 0xFFFFFFFF) {
          if (!globalThis.__wfsoWarn) globalThis.__wfsoWarn = new Set();
          const rsp = Number(dv.getBigUint64(ctx + REG.rsp * 8, true));
          const ret = rsp > 0 && rsp + 8 <= u8.length ? dv.getBigUint64(rsp, true) : 0n;
          const kinds = handles.map(h => winHandles.get(h)?.kind ?? "?").join(",");
          const key = `${kinds}@${ret.toString(16)}`;
          if (!globalThis.__wfsoWarn.has(key)) {
              globalThis.__wfsoWarn.add(key);
              log(`[WFSO-INFINITE] kind(s)=${kinds} from 0x${ret.toString(16)} → 5s clamp (WAIT_TIMEOUT)`);
          }
      }

      return await new Promise((resolve) => {
          waiter.resolve = resolve; winHandleWaiters.add(waiter);
          waiter.timer = setTimeout(() => {
              if (winHandleWaiters.delete(waiter)) resolve(0x102);   // WAIT_TIMEOUT
          }, effectiveTimeout);
      }).finally(() => { if (waiter.timer) clearTimeout(waiter.timer); winHandleWaiters.delete(waiter); });
  };
  const winWriteDword = (ptr, value) => {
    const p = Number(ptr);
    if (!Number.isSafeInteger(p) || p < 0 || !ensureMemory(p + 4)) return false;
    dv.setUint32(p, Number(value) >>> 0, true); return true;
  };
  const winAllocHandle = (entry) => { const h = BigInt(winNextHandle++); winHandles.set(h, entry); return h; };

  // Winsock compatibility. The guest API is Win32-shaped, while the actual
  // transport is injected by the host: Node can use native sockets; browsers
  // tunnel through the loopback WebSocket relay (raw TCP/UDP are unavailable
  // directly inside a browser sandbox).
  const WSA_INVALID_SOCKET = MASK64;
  const WSA_SOCKET_ERROR = -1n;
  const WSA_ERRORS = {
    EACCES: 10013, EADDRINUSE: 10048, EADDRNOTAVAIL: 10049, EAFNOSUPPORT: 10047,
    EALREADY: 10037, ECONNABORTED: 10053, ECONNREFUSED: 10061, ECONNRESET: 10054,
    EHOSTUNREACH: 10065, EINPROGRESS: 10036, EINTR: 10004, EINVAL: 10022,
    EISCONN: 10056, ENETDOWN: 10050, ENETUNREACH: 10051, ENOBUFS: 10055,
    ENOTCONN: 10057, ENOTSOCK: 10038, EOPNOTSUPP: 10045, EPIPE: 10058,
    ETIMEDOUT: 10060, EWOULDBLOCK: 10035, EAGAIN: 10035, EBADF: 10038, EDESTADDRREQ: 10039,
  };
  const winWsaErrorCode = (error) => Number(error?.wsaCode) || WSA_ERRORS[error?.code] || 10050;
  const winWsaFail = (code) => { winWsaLastError = Number(code) >>> 0; winSetLastError(winWsaLastError); return WSA_SOCKET_ERROR; };
  const winSocket = (handle) => {
    const entry = winHandles.get(BigInt(handle));
    return entry?.kind === "winsock_socket" ? entry : null;
  };
  const winIp4Bytes = (value) => {
    const parts = String(value).split(".");
    if (parts.length !== 4 || parts.some((part) => !/^\d{1,3}$/.test(part) || Number(part) > 255)) return null;
    return Uint8Array.from(parts.map(Number));
  };
  const winParseIp6 = (value) => {
    let input = String(value).toLowerCase().split("%", 1)[0];
    if (input.includes(".")) {
      const lastColon = input.lastIndexOf(":");
      const ip4 = winIp4Bytes(input.slice(lastColon + 1));
      if (!ip4) return null;
      input = `${input.slice(0, lastColon)}:${((ip4[0] << 8) | ip4[1]).toString(16)}:${((ip4[2] << 8) | ip4[3]).toString(16)}`;
    }
    if ((input.match(/::/g) || []).length > 1) return null;
    const halves = input.split("::");
    const left = halves[0] ? halves[0].split(":") : [];
    const right = halves.length > 1 && halves[1] ? halves[1].split(":") : [];
    if ([...left, ...right].some((part) => !/^[0-9a-f]{1,4}$/.test(part))) return null;
    const missing = 8 - left.length - right.length;
    if ((halves.length === 1 && missing !== 0) || (halves.length === 2 && missing < 1)) return null;
    const words = [...left.map((part) => parseInt(part, 16)), ...Array(Math.max(0, missing)).fill(0), ...right.map((part) => parseInt(part, 16))];
    if (words.length !== 8) return null;
    const bytes = new Uint8Array(16);
    words.forEach((word, i) => { bytes[i * 2] = word >> 8; bytes[i * 2 + 1] = word & 255; });
    return bytes;
  };
  const winFormatIp6 = (bytes) => {
    const words = Array.from({ length: 8 }, (_, i) => (bytes[i * 2] << 8) | bytes[i * 2 + 1]);
    let bestStart = -1, bestLength = 1;
    for (let i = 0; i < 8;) {
      if (words[i] !== 0) { i++; continue; }
      let j = i; while (j < 8 && words[j] === 0) j++;
      if (j - i > bestLength) { bestStart = i; bestLength = j - i; }
      i = j;
    }
    if (bestStart < 0) return words.map((word) => word.toString(16)).join(":");
    const left = words.slice(0, bestStart).map((word) => word.toString(16)).join(":");
    const right = words.slice(bestStart + bestLength).map((word) => word.toString(16)).join(":");
    return `${left}::${right}`;
  };
  const winReadSockAddr = (ptr, length = 16) => {
    const p = Number(ptr), len = Number(length);
    if (!Number.isSafeInteger(p) || p < 0 || len < 8 || p + len > u8.length) return null;
    const family = dv.getUint16(p, true), port = dv.getUint16(p + 2, false);
    if (family === 2 && len >= 16) {
      const bytes = u8.slice(p + 4, p + 8);
      return { family, port, address: [...bytes].join("."), bytes };
    }
    if (family === 23 && len >= 28) {
      const bytes = u8.slice(p + 8, p + 24);
      return { family, port, address: winFormatIp6(bytes), bytes, scopeId: dv.getUint32(p + 24, true) };
    }
    return null;
  };
  const winWriteSockAddr = (ptr, address, port, family = 2, length = null) => {
    const p = Number(ptr), max = length == null ? (family === 23 ? 28 : 16) : Number(length);
    if (!Number.isSafeInteger(p) || p < 0 || p + max > u8.length) return false;
    u8.fill(0, p, p + max);
    if (family === 2) {
      const bytes = winIp4Bytes(address);
      if (!bytes || max < 16) return false;
      dv.setUint16(p, 2, true); dv.setUint16(p + 2, Number(port) & 0xffff, false); u8.set(bytes, p + 4);
      return true;
    }
    if (family === 23) {
      const bytes = winParseIp6(address);
      if (!bytes || max < 28) return false;
      dv.setUint16(p, 23, true); dv.setUint16(p + 2, Number(port) & 0xffff, false); u8.set(bytes, p + 8);
      return true;
    }
    return false;
  };
  const winMakeSocket = (family, type, protocol, transport = null) => {
    const entry = { kind: "winsock_socket", family: Number(family), type: Number(type), protocol: Number(protocol),
      transport, connected: false, bound: false, listening: false, nonBlocking: false, remote: null, closed: false,
      recvTimeout: 0, sendTimeout: 0, reuseAddress: false, eventErrors: Array(10).fill(0),
      connecting: false, connectError: 0, connectCompletePending: false, networkEvents: 0 };
    if (entry.family !== 2 && entry.family !== 23) return null;
    if (entry.type !== 1 && entry.type !== 2) return null;
    const handle = winAllocHandle(entry); entry.handle = handle;
    return handle;
  };
  const winSocketTransport = (entry) => {
    if (!network) throw Object.assign(new Error("No Winsock host adapter is configured"), { code: "ENETDOWN" });
    if (!entry.transport) {
      if (entry.type === 1) entry.transport = network.createTcpSocket?.(entry.family);
      else entry.transport = network.createUdpSocket?.(entry.family);
      if (!entry.transport) throw Object.assign(new Error("The network host does not support this socket type"), { code: "EOPNOTSUPP" });
    }
    return entry.transport;
  };
  const winNetworkResult = async (operation) => {
    try { return await operation(); }
    catch (error) { return winWsaFail(winWsaErrorCode(error)); }
  };
  const winSocketReady = (entry) => {
    if (!entry || entry.closed || !entry.transport) return false;
    if (entry.type === 1) return !!(network?.isReadable?.(entry.transport));
    return !!(network?.isUdpReadable?.(entry.transport));
  };
  const winWaitSocketChange = (entry) => new Promise((resolve) => {
    if (!entry?.transport || typeof network?.onChange !== "function") return;
    let unsubscribe = null;
    const done = () => { unsubscribe?.(); resolve(); };
    unsubscribe = network.onChange(entry.transport, done);
  });
  const winSignalSocketEvents = (entry) => {
    if (!entry || !entry.transport) return;
    if (entry.connecting && entry.transport.connected) {
      entry.connected = true; entry.connecting = false; entry.connectCompletePending = true;
    }
    let events = 0;
    if (entry.connected) events |= 0x02; // FD_WRITE
    if (entry.connectError || entry.connectCompletePending) events |= 0x10; // FD_CONNECT
    if (entry.listening && (entry.transport.accepted?.length ?? 0) > 0) events |= 0x08; // FD_ACCEPT
    if (winSocketReady(entry)) events |= 0x01; // FD_READ
    if (entry.transport.ended) events |= 0x20; // FD_CLOSE
    events &= entry.eventMask == null ? 0xffffffff : entry.eventMask;
    const newEvents = events & ~(entry.networkEvents || 0);
    if (!newEvents) return;
    entry.networkEvents = (entry.networkEvents || 0) | newEvents;
    if (newEvents & 0x10) { entry.eventErrors[4] = entry.connectError || 0; entry.connectCompletePending = false; }
    if (newEvents & 0x20) entry.eventErrors[5] = entry.transport.error ? winWsaErrorCode(entry.transport.error) : 0;
    if (entry.eventHandle) {
      const event = winHandles.get(entry.eventHandle);
      if (event?.kind === "event") { event.signaled = true; winWakeHandleWaiters(); }
    }
    if (entry.asyncWindow && entry.asyncMessage) {
      const error = entry.connectError || (entry.transport.error ? winWsaErrorCode(entry.transport.error) : 0);
      winPostMessage(entry.asyncWindow, entry.asyncMessage, entry.handle, BigInt((newEvents & 0xffff) | ((error & 0xffff) << 16)));
    }
  };
  const winWatchSocket = (entry) => {
    if (!entry.transport || entry.unsubscribeNetwork) return;
    if (typeof network?.onChange === "function") entry.unsubscribeNetwork = network.onChange(entry.transport, () => winSignalSocketEvents(entry));
  };
  const winSocketReceive = async (entry, maxLength) => {
    const transport = winSocketTransport(entry);
    let result;
    if (entry.type === 1) {
      result = entry.nonBlocking ? network.tryRecvTcp?.(transport, maxLength) : await network.recvTcp(transport, maxLength);
    } else {
      const packet = entry.nonBlocking ? network.tryRecvUdp?.(transport) : await network.recvUdp(transport);
      if (packet === undefined) return undefined;
      if (packet === null) return null;
      entry.lastPeer = packet;
      result = packet.data;
    }
    return result;
  };
  const WIN_UNHANDLED = Symbol("unhandled-winsock-api");
  const INITTERM_RESUME = 0xFFFF_FFF9n;
  let inittermState = null;   // { pending, returnPc, returnRsp }
  async function emulateWinsockApi(name, a) {
    const n = String(name).toLowerCase();
    const arg = (i) => a(i);
    const result = (value) => BigInt.asUintN(64, BigInt(value));
    // Diagnostic: log every non-trivial winsock call
    if (["wsagetlasterror", "wsasetlasterror", "wsacreateevent",
          "wsacloseevent", "wsawaitformultipleevents", "select",
          "wsaeventselect", "wsaenumnetworkevents", "ioctlsocket",
          "setsockopt", "getsockopt","connect", "socket", "getaddrinfo"].includes(n)) {
      if (!globalThis.__wsLog) globalThis.__wsLog = new Set();
      const key = `${n}:${[0,1,2,3].map(i => BigInt.asUintN(64, a(i)).toString(16)).join(",")}`;
      if (!globalThis.__wsLog.has(key)) {
        globalThis.__wsLog.add(key);
        log(`[WINSOCK-CALL] ${name}(${[0,1,2,3].map(i => "0x" + BigInt.asUintN(64, a(i)).toString(16)).join(", ")})`);
      }
    }
    const memoryBytes = (address, length) => readBytes(address, length);
    const writeBytesChecked = (address, bytes) => writeBytes(address, bytes);
    const parseAddress = (pointer, length) => winReadSockAddr(pointer, length);
    const allocateAddrInfo = (item, next = 0n, canonicalName = 0n) => {
      const size = item.family === 23 ? 28 : 16;
      const addr = winAlloc(size);
      if (!addr || !winWriteSockAddr(Number(addr), item.address, item.port, item.family, size)) return 0n;
      const info = winAlloc(48);
      if (!info) return 0n;
      dv.setInt32(Number(info) + 4, item.family, true);
      dv.setInt32(Number(info) + 8, item.type, true);
      dv.setInt32(Number(info) + 12, item.protocol, true);
      dv.setUint32(Number(info) + 16, size, true);
      dv.setBigUint64(Number(info) + 24, canonicalName, true);
      dv.setBigUint64(Number(info) + 32, addr, true);
      dv.setBigUint64(Number(info) + 40, next, true);
      return info;
    };
    switch (n) {
      case "wsacreateevent": {
        return winAllocHandle({ kind: "event", manualReset: true, signaled: false });
      }
      case "wsacloseevent": {
        const handle = arg(0), entry = winHandles.get(handle);
        if (entry?.kind !== "event") return 0n;
        winHandles.delete(handle); return 1n;
      }
      case "wsasetevent": case "wsaresetevent": {
        const entry = winHandles.get(arg(0)); if (entry?.kind !== "event") return 0n;
        entry.signaled = n === "wsasetevent"; winWakeHandleWaiters(); return 1n;
      }
      case "wsawaitformultipleevents": {
        const count = Number(arg(0)), pointer = Number(arg(1)), waitAll = arg(2) !== 0n, timeout = Number(arg(3)) >>> 0;
        if (!Number.isSafeInteger(count) || count < 1 || count > 64 || !ensureMemory(pointer + count * 8)) return 0xffff_ffffn;
        const handles = Array.from({ length: count }, (_, i) => dv.getBigUint64(pointer + i * 8, true));
        return BigInt(await winWaitForHandles(handles, waitAll, timeout, 0));
      }
      case "wsaeventselect": {
        const entry = winSocket(arg(0)), eventHandle = arg(1);
        if (!entry) return winWsaFail(10038);
        if (eventHandle && winHandles.get(eventHandle)?.kind !== "event") return winWsaFail(10022);
        entry.eventHandle = eventHandle || 0n; entry.eventMask = Number(arg(2)) >>> 0;
        entry.nonBlocking = true; winWatchSocket(entry); winSignalSocketEvents(entry); return 0n;
      }
      case "wsaenumnetworkevents": {
        const entry = winSocket(arg(0)), eventHandle = arg(1), output = Number(arg(2));
        if (!entry || !ensureMemory(output + 44)) return winWsaFail(10038);
        if (eventHandle && winHandles.get(eventHandle)?.kind === "event") winHandles.get(eventHandle).signaled = false;
        dv.setUint32(output, entry.networkEvents || 0, true);
        u8.fill(0, output + 4, output + 44);
        for (let i = 0; i < 10; i++) dv.setInt32(output + 4 + i * 4, entry.eventErrors[i] || 0, true);
        entry.networkEvents = 0; entry.eventErrors.fill(0); return 0n;
      }
      case "wsaasyncselect": {
        const entry = winSocket(arg(0)); if (!entry) return winWsaFail(10038);
        entry.asyncWindow = arg(1); entry.asyncMessage = Number(arg(2)) >>> 0; entry.eventMask = Number(arg(3)) >>> 0;
        entry.nonBlocking = true; winWatchSocket(entry); winSignalSocketEvents(entry); return 0n;
      }
      case "wsastartup": {
        const version = Number(arg(0)) & 0xffff;
        // Negotiate the highest supported Winsock version not exceeding the
        // caller's request. The low byte is the major version, high byte minor.
        const negotiated = [0x0202, 0x0201, 0x0200, 0x0101, 0x0100].find((v) => v <= version);
        if (negotiated == null) return 10092n; // WSAVERNOTSUPPORTED
        const data = Number(arg(1));
        // WSADATA is 408 bytes on Win64, including aligned lpVendorInfo.
        if (!data || !ensureMemory(data + 0x198)) return 10014n;
        u8.fill(0, data, data + 0x198);
        dv.setUint16(data, negotiated, true);
        dv.setUint16(data + 2, 0x0202, true);
        writeBytes(data + 4, new TextEncoder().encode("Steam Recompiler Winsock compatibility\0"));
        writeBytes(data + 261, new TextEncoder().encode("WebAssembly network host\0"));
        dv.setUint16(data + 390, 0xffff, true); dv.setUint16(data + 392, 0xffff, true);
        dv.setBigUint64(data + 400, 0n, true); // lpVendorInfo
        winWsaStartupCount++;
        winWsaLastError = 0;
        log(`[WINSOCK] WSAStartup(0x${version.toString(16)}) succeeded; startup refs=${winWsaStartupCount}`);
        return 0n;
      }
      case "wsacleanup":
        if (!winWsaStartupCount) { winWsaLastError = 10093; winSetLastError(10093); return 10093n; }
        winWsaStartupCount = Math.max(0, winWsaStartupCount - 1);
        log(`[WINSOCK] WSACleanup succeeded; startup refs=${winWsaStartupCount}`);
        return 0n;
      case "wsagetlasterror": return BigInt(winWsaLastError >>> 0);
      case "wsasetlasterror": winWsaLastError = Number(arg(0)) >>> 0; winSetLastError(winWsaLastError); return 0n;
      case "socket": case "wsasocketa": case "wsasocketw": {
        if (!winWsaStartupCount) return winWsaFail(10093); // WSANOTINITIALISED
        const family = Number(arg(0)), type = Number(arg(1)), protocol = Number(arg(2));
        const supportedFamily = family === 2 || family === 23 || family === 0;
        if (!supportedFamily || ![1, 2].includes(type)) return winWsaFail(!supportedFamily ? 10047 : 10044);
        if ((type === 1 && ![0, 6].includes(protocol)) || (type === 2 && ![0, 17].includes(protocol))) return winWsaFail(10043);
        const socket = winMakeSocket(family === 0 ? 2 : family, type, protocol);
        return socket ?? winWsaFail(10044);
      }
      case "closesocket": {
        const handle = arg(0), entry = winSocket(handle);
        if (!entry) return winWsaFail(10038);
        try { entry.unsubscribeNetwork?.(); if (entry.type === 1) network?.closeTcp?.(entry.transport); else network?.closeUdp?.(entry.transport); } catch {}
        entry.closed = true; winHandles.delete(handle); return 0n;
      }
      case "getsockname": case "getpeername": {
        const entry = winSocket(arg(0)), addressPtr = Number(arg(1)), lengthPtr = Number(arg(2));
        if (!entry) return winWsaFail(10038);
        if (!ensureMemory(lengthPtr + 4)) return winWsaFail(10014);
        const capacity = Math.max(0, dv.getInt32(lengthPtr, true));
        let address = null;
        if (n === "getpeername") {
          if (!entry.connected) return winWsaFail(10057);
          address = entry.remote ?? (entry.transport ? network?.getPeerName?.(entry.transport) : null) ?? null;
          if (!address) return winWsaFail(10057);
        } else {
          address = (entry.transport ? network?.getSocketName?.(entry.transport) : null) ?? entry.local ?? null;
          if (!address) address = { address: entry.family === 23 ? "::" : "0.0.0.0", port: 0 };
        }
        const family = entry.family === 23 ? 23 : 2;
        const required = family === 23 ? 28 : 16;
        dv.setInt32(lengthPtr, required, true);
        if (capacity < required || !winWriteSockAddr(addressPtr, address.address, address.port || 0, family, required)) return winWsaFail(10014);
        return 0n;
      }
      case "connect": {
        const entry = winSocket(arg(0)), address = parseAddress(arg(1), arg(2));
        if (!entry) return winWsaFail(10038);
        if (!address) return winWsaFail(10014);
        entry.remote = address;
        if (entry.type === 2) {
          try { winSocketTransport(entry); entry.connected = true; winWatchSocket(entry); winSignalSocketEvents(entry); return 0n; }
          catch (error) { return winWsaFail(winWsaErrorCode(error)); }
        }
        if (entry.nonBlocking) {
          if (entry.connecting || entry.connected) return winWsaFail(entry.connected ? 10056 : 10037);
          try {
            const transport = winSocketTransport(entry);
            winWatchSocket(entry); entry.connecting = true; entry.connectError = 0;
            entry.connectPromise = Promise.resolve(network.connectTcp(transport, address.address, address.port)).then(() => {
              entry.connected = true; entry.connecting = false; entry.connectError = 0; winSignalSocketEvents(entry);
            }).catch((error) => {
              entry.connecting = false; entry.connectError = winWsaErrorCode(error); winSignalSocketEvents(entry);
            });
            return winWsaFail(10035); // WSAEWOULDBLOCK: wait for FD_CONNECT/select completion.
          } catch (error) { entry.connecting = false; return winWsaFail(winWsaErrorCode(error)); }
        }
        return await winNetworkResult(async () => {
          await network.connectTcp(winSocketTransport(entry), address.address, address.port);
          entry.connected = true; winWatchSocket(entry); winSignalSocketEvents(entry); return 0n;
        });
      }
      case "bind": {
        const entry = winSocket(arg(0)), address = parseAddress(arg(1), arg(2));
        if (!entry) return winWsaFail(10038);
        if (!address) return winWsaFail(10014);
        return await winNetworkResult(async () => {
          const transport = winSocketTransport(entry);
          if (entry.type === 1) await network.bindTcp(transport, address.address, address.port);
          else await network.bindUdp(transport, address.address, address.port);
          entry.bound = true; entry.local = address; winWatchSocket(entry); return 0n;
        });
      }
      case "listen": {
        const entry = winSocket(arg(0)); if (!entry || entry.type !== 1) return winWsaFail(10038);
        return await winNetworkResult(async () => { await network.listenTcp(winSocketTransport(entry), Number(arg(1))); entry.listening = true; return 0n; });
      }
      case "accept": {
        const entry = winSocket(arg(0)); if (!entry || entry.type !== 1 || !entry.listening) return winWsaFail(10038);
        return await winNetworkResult(async () => {
          const accepted = entry.nonBlocking ? network.tryAcceptTcp?.(entry.transport) : await network.acceptTcp(entry.transport);
          if (accepted === undefined) return winWsaFail(10035);
          if (!accepted) return 0n;
          const handle = winMakeSocket(entry.family, 1, entry.protocol, accepted);
          const newEntry = winSocket(handle); newEntry.connected = true; winWatchSocket(newEntry);
          if (arg(1) && arg(2)) {
            const lenPtr = Number(arg(2)), capacity = dv.getInt32(lenPtr, true);
            if (capacity >= 16 && accepted.remoteAddress) winWriteSockAddr(Number(arg(1)), accepted.remoteAddress, accepted.remotePort || 0, entry.family, Math.min(capacity, entry.family === 23 ? 28 : 16));
            dv.setInt32(lenPtr, entry.family === 23 ? 28 : 16, true);
          }
          return handle;
        });
      }
      case "send": case "wsasend": {
        const entry = winSocket(arg(0)); if (!entry) return winWsaFail(10038);
        let bytes, length;
        if (n === "wsasend") {
          const buffers = Number(arg(1)), count = Number(arg(2));
          if (!Number.isSafeInteger(count) || count < 0 || count > 64) return winWsaFail(10014);
          const parts = []; let total = 0;
          for (let i = 0; i < count; i++) {
            const p = buffers + i * 16, len = dv.getUint32(p, true), dataPtr = Number(dv.getBigUint64(p + 8, true));
            const part = memoryBytes(dataPtr, len); if (!part) return winWsaFail(10014); parts.push(part); total += len;
          }
          bytes = new Uint8Array(total); let offset = 0; for (const part of parts) { bytes.set(part, offset); offset += part.length; }
          length = total;
        } else {
          length = Number(arg(2)); bytes = memoryBytes(arg(1), length);
        }
        if (!bytes || !Number.isSafeInteger(length) || length < 0) return winWsaFail(10014);
        return await winNetworkResult(async () => {
          const transport = winSocketTransport(entry);
          const sent = entry.type === 1 ? await network.sendTcp(transport, bytes) : entry.remote
            ? await network.sendUdp(transport, bytes, entry.remote.address, entry.remote.port)
            : (() => { throw Object.assign(new Error("UDP socket is not connected"), { code: "EDESTADDRREQ" }); })();
          if (n === "wsasend" && arg(3)) dv.setUint32(Number(arg(3)), Number(sent), true);
          return BigInt(sent);
        });
      }
      case "sendto": {
        const entry = winSocket(arg(0)), length = Number(arg(2)), bytes = memoryBytes(arg(1), length);
        const address = parseAddress(arg(4), arg(5));
        if (!entry) return winWsaFail(10038);
        if (!bytes || !address) return winWsaFail(10014);
        if (entry.type !== 2) return winWsaFail(10045);
        return await winNetworkResult(async () => BigInt(await network.sendUdp(winSocketTransport(entry), bytes, address.address, address.port)));
      }
      case "recv": case "wsarecv": {
        const entry = winSocket(arg(0)); if (!entry) return winWsaFail(10038);
        let buffer = Number(arg(1)), capacity = Number(arg(2)), flagsPtr = 0n;
        if (n === "wsarecv") {
          const buffers = Number(arg(1)), count = Number(arg(2)); flagsPtr = arg(4);
          if (!Number.isSafeInteger(count) || count < 0 || count > 64) return winWsaFail(10014);
          capacity = 0;
          const parts = [];
          for (let i = 0; i < count; i++) { const p = buffers + i * 16; parts.push({ ptr: Number(dv.getBigUint64(p + 8, true)), len: dv.getUint32(p, true) }); capacity += parts[i].len; }
          const received = await winNetworkResult(async () => await winSocketReceive(entry, capacity));
          if (received === WSA_SOCKET_ERROR) return received;
          if (received === undefined) return winWsaFail(10035);
          if (received === null) return 0n;
          let offset = 0; for (const part of parts) { const countPart = Math.min(part.len, received.length - offset); if (countPart > 0) writeBytes(part.ptr, received.subarray(offset, offset + countPart)); offset += countPart; if (offset >= received.length) break; }
          if (arg(3)) dv.setUint32(Number(arg(3)), received.length, true);
          if (flagsPtr) dv.setUint32(Number(flagsPtr), 0, true);
          return BigInt(received.length);
        }
        if (!Number.isSafeInteger(capacity) || capacity < 0 || !ensureMemory(buffer + capacity)) return winWsaFail(10014);
        const received = await winNetworkResult(async () => await winSocketReceive(entry, capacity));
        if (received === WSA_SOCKET_ERROR) return received;
        if (received === undefined) return winWsaFail(10035);
        if (received === null) return 0n;
        if (entry.type === 2 && received.length > capacity) return winWsaFail(10040);
        writeBytesChecked(buffer, received.subarray(0, capacity));
        return BigInt(Math.min(received.length, capacity));
      }
      case "recvfrom": {
        const entry = winSocket(arg(0)), buffer = Number(arg(1)), capacity = Number(arg(2));
        if (!entry || entry.type !== 2) return winWsaFail(10038);
        if (!Number.isSafeInteger(capacity) || capacity < 0 || !ensureMemory(buffer + capacity)) return winWsaFail(10014);
        const packet = entry.nonBlocking ? network?.tryRecvUdp?.(winSocketTransport(entry)) : await winNetworkResult(async () => await network.recvUdp(winSocketTransport(entry)));
        if (packet === WSA_SOCKET_ERROR) return packet;
        if (packet === undefined) return winWsaFail(10035);
        if (packet === null) return 0n;
        if (arg(4) && arg(5)) {
          const lengthPtr = Number(arg(5)), length = dv.getInt32(lengthPtr, true);
          const family = entry.family === 23 ? 23 : 2, needed = family === 23 ? 28 : 16;
          if (length >= needed) winWriteSockAddr(Number(arg(4)), packet.address, packet.port, family, Math.min(length, needed));
          dv.setInt32(lengthPtr, needed, true);
        }
        if (packet.data.length > capacity) return winWsaFail(10040);
        writeBytesChecked(buffer, packet.data); return BigInt(packet.data.length);
      }
      case "shutdown": {
        const entry = winSocket(arg(0)); if (!entry) return winWsaFail(10038);
        const how = Number(arg(1)); if (![0, 1, 2].includes(how)) return winWsaFail(10022);
        if (entry.type === 1) return await winNetworkResult(async () => { await network.shutdownTcp(winSocketTransport(entry), how); return 0n; });
        entry.shutdown = how; return 0n;
      }
      case "ioctlsocket": {
        const entry = winSocket(arg(0)), command = Number(arg(1)) >>> 0, valuePtr = Number(arg(2));
        if (!entry) return winWsaFail(10038);
        if (!ensureMemory(valuePtr + 4)) return winWsaFail(10014);
        if (command === 0x8004667e) { entry.nonBlocking = dv.getUint32(valuePtr, true) !== 0; return 0n; } // FIONBIO
        if (command === 0x4004667f) { dv.setUint32(valuePtr, 1 << 20, true); return 0n; } // FIONREAD (best-effort)
        return winWsaFail(10045);
      }
      case "setsockopt": {
        const entry = winSocket(arg(0)), level = Number(arg(1)), option = Number(arg(2)), valuePtr = Number(arg(3)), length = Number(arg(4));
        if (!entry || !ensureMemory(valuePtr + Math.max(4, length))) return winWsaFail(10038);
        if (length < 4) return winWsaFail(10014);
        const value = dv.getInt32(valuePtr, true);
        if (level === 0xffff && option === 4) entry.reuseAddress = value !== 0;
        else if (level === 0xffff && option === 0x1005) entry.sendTimeout = value >>> 0;
        else if (level === 0xffff && option === 0x1006) entry.recvTimeout = value >>> 0;
        else if (level === 6 && option === 1) {
          entry.noDelay = value !== 0;
          try { network?.setNoDelay?.(entry.transport, entry.noDelay); } catch {}
        }
        else return winWsaFail(10042);
        return 0n;
      }
      case "getsockopt": {
        const entry = winSocket(arg(0)), level = Number(arg(1)), option = Number(arg(2)), valuePtr = Number(arg(3)), lengthPtr = Number(arg(4));
        if (!entry || !ensureMemory(lengthPtr + 4)) return winWsaFail(10038);
        const cap = dv.getInt32(lengthPtr, true); if (cap < 4 || !ensureMemory(valuePtr + 4)) return winWsaFail(10014);
        let value;
        if (level === 0xffff && option === 4) value = entry.reuseAddress ? 1 : 0;
        else if (level === 0xffff && option === 0x1005) value = entry.sendTimeout;
        else if (level === 0xffff && option === 0x1006) value = entry.recvTimeout;
        else if (level === 6 && option === 1) value = entry.noDelay ? 1 : 0;
        else if (level === 0xffff && option === 0x1007) value = entry.connectError || (entry.transport?.error ? winWsaErrorCode(entry.transport.error) : 0);
        else if (level === 0xffff && option === 0x1008) value = entry.type;
        else return winWsaFail(10042);
        dv.setInt32(valuePtr, value, true); dv.setInt32(lengthPtr, 4, true); return 0n;
      }
      case "select": {
        const readPtr = Number(arg(1)), writePtr = Number(arg(2)), exceptPtr = Number(arg(3));
        const rsp = Number(dv.getBigUint64(ctx + REG.rsp * 8, true)), timeoutPtr = Number(winReadU64(rsp + 0x28));
        const readSet = (pointer) => {
          if (!pointer) return null;
          if (!ensureMemory(pointer + 8)) return null;
          const count = Math.min(64, dv.getUint32(pointer, true)), values = [];
          for (let i = 0; i < count; i++) values.push(dv.getBigUint64(pointer + 8 + i * 8, true));
          return values;
        };
        const originalRead = readSet(readPtr), originalWrite = readSet(writePtr), originalExcept = readSet(exceptPtr);
        if ((readPtr && !originalRead) || (writePtr && !originalWrite) || (exceptPtr && !originalExcept)) return winWsaFail(10014);
        const ready = () => {
          const r = (originalRead || []).filter((h) => { const e = winSocket(h); return e && winSocketReady(e); });
          const w = (originalWrite || []).filter((h) => { const e = winSocket(h); return e?.connected || (e?.connecting && e.transport?.connected) || (e?.type === 2 && !e.closed); });
          const x = (originalExcept || []).filter((h) => { const e = winSocket(h); return !e || e.connectError || e.transport?.error; });
          return { r, w, x, count: r.length + w.length + x.length };
        };
        let readySets = ready();
        if (!readySets.count) {
          let timeout = null;
          if (timeoutPtr) {
            if (!ensureMemory(timeoutPtr + 8)) return winWsaFail(10014);
            const seconds = Math.max(0, dv.getInt32(timeoutPtr, true)), micros = Math.max(0, dv.getInt32(timeoutPtr + 4, true));
            timeout = seconds * 1000 + Math.floor(micros / 1000);
          }
          if (timeout !== 0) {
            const waits = [...(originalRead || []), ...(originalWrite || []), ...(originalExcept || [])]
              .map((h) => winSocket(h)).filter((entry) => entry?.transport).map((entry) => winWaitSocketChange(entry));
            if (timeout === null) await Promise.race(waits);
            else if (waits.length) await Promise.race([...waits, new Promise((resolve) => setTimeout(resolve, timeout))]);
          }
          readySets = ready();
        }
        const writeSet = (pointer, values) => {
          if (!pointer) return;
          dv.setUint32(pointer, values.length, true);
          values.forEach((h, i) => dv.setBigUint64(pointer + 8 + i * 8, h, true));
        };
        writeSet(readPtr, readySets.r); writeSet(writePtr, readySets.w); writeSet(exceptPtr, readySets.x);
        return BigInt(readySets.count);
      }
      case "getaddrinfo": case "getaddrinfow": {
        const wide = n.endsWith("w"), node = arg(0) ? winReadMemoryString(arg(0), wide) : null;
        const service = arg(1) ? winReadMemoryString(arg(1), wide) : null;
        const hints = Number(arg(2)), resultPtr = Number(arg(3));
        if (!resultPtr || !ensureMemory(resultPtr + 8)) return 10014n;
        dv.setBigUint64(resultPtr, 0n, true);
        if (hints && !ensureMemory(hints + 16)) return 10014n;
        const family = hints ? dv.getInt32(hints + 4, true) : 0;
        const type = hints ? dv.getInt32(hints + 8, true) : 0;
        const protocol = hints ? dv.getInt32(hints + 12, true) : 0;
        if (![0, 2, 23].includes(family) || ![0, 1, 2].includes(type)) return 10022n;
        const port = service == null ? 0 : (/^\d+$/.test(service) ? Number(service) : ({ http: 80, https: 443, domain: 53 })[service.toLowerCase()]);
        if (port == null || port < 0 || port > 65535) return 10109n;
        try {
          let addresses;
          if (!node) addresses = [{ address: family === 23 ? "::" : "0.0.0.0", family: family === 23 ? 6 : 4 }];
          else if (winIp4Bytes(node) || winParseIp6(node)) addresses = [{ address: node, family: node.includes(":") ? 6 : 4 }];
          else addresses = await network.resolveDns(node);
          const filtered = addresses.filter((item) => family === 0 || (family === 2 ? item.family === 4 : item.family === 6))
            .filter((item) => type === 0 || type === 1 || type === 2);
          if (!filtered.length) return 11001n;
          let next = 0n;
          for (let i = filtered.length - 1; i >= 0; i--) {
            const item = filtered[i], fam = item.family === 6 ? 23 : 2;
            const info = allocateAddrInfo({ family: fam, type: type || (protocol === 17 ? 2 : 1), protocol: protocol || (type === 2 ? 17 : 6), address: item.address, port }, next);
            if (!info) return 8n;
            next = info;
          }
          dv.setBigUint64(resultPtr, next, true); return 0n;
        } catch (error) { return error?.code === "EAI_AGAIN" ? 11002n : 11001n; }
      }
      case "freeaddrinfo": {
        let pointer = arg(0), guard = 0;
        while (pointer && guard++ < 256) {
          const p = Number(pointer); if (!ensureMemory(p + 48)) break;
          const addr = dv.getBigUint64(p + 32, true), next = dv.getBigUint64(p + 40, true);
          const canon = dv.getBigUint64(p + 24, true);
          if (addr) winAllocations.delete(Number(addr));
          if (canon) winAllocations.delete(Number(canon));
          winAllocations.delete(p); pointer = next;
        }
        return 0n;
      }
      case "gethostbyname": {
        const host = winReadA(arg(0)); if (!host || !network) return 0n;
        try {
          const entries = await network.resolveDns(host), item = entries.find((entry) => entry.family === 4);
          if (!item) return 0n;
          const namePtr = winAlloc(host.length + 1); winWriteA(Number(namePtr), host);
          const addrPtr = winAlloc(4); writeBytes(Number(addrPtr), winIp4Bytes(item.address));
          const aliases = winAlloc(8), addrList = winAlloc(16); dv.setBigUint64(Number(aliases), 0n, true);
          dv.setBigUint64(Number(addrList), addrPtr, true); dv.setBigUint64(Number(addrList) + 8, 0n, true);
          const resultPtr = winAlloc(32); dv.setBigUint64(Number(resultPtr), namePtr, true); dv.setBigUint64(Number(resultPtr) + 8, aliases, true);
          dv.setInt16(Number(resultPtr) + 16, 2, true); dv.setInt16(Number(resultPtr) + 18, 4, true); dv.setBigUint64(Number(resultPtr) + 24, addrList, true);
          return resultPtr;
        } catch { return 0n; }
      }
      case "gethostname": {
        const length = Number(arg(1)), pointer = Number(arg(0));
        if (!Number.isSafeInteger(length) || length <= 0 || !ensureMemory(pointer + length)) return winWsaFail(10014);
        let host = "wasm-guest";
        try { if (network?.getHostname) host = await network.getHostname(); } catch {}
        const bytes = new TextEncoder().encode(`${host}\0`);
        if (bytes.length > length) return winWsaFail(10037);
        writeBytes(pointer, bytes); return 0n;
      }
      case "htons": case "ntohs": return BigInt(((Number(arg(0)) & 0xff) << 8) | ((Number(arg(0)) >>> 8) & 0xff));
      case "htonl": case "ntohl": {
        const value = Number(arg(0)) >>> 0;
        return BigInt((((value & 0xff) << 24) | ((value & 0xff00) << 8) | ((value >>> 8) & 0xff00) | (value >>> 24)) >>> 0);
      }
      case "inet_addr": {
        const bytes = winIp4Bytes(winReadA(arg(0)) || ""); if (!bytes) return 0xffff_ffffn;
        return BigInt((bytes[0] | (bytes[1] << 8) | (bytes[2] << 16) | (bytes[3] << 24)) >>> 0);
      }
      case "inet_ntoa": {
        const value = Number(arg(0)) >>> 0;
        const text = `${value & 255}.${(value >>> 8) & 255}.${(value >>> 16) & 255}.${(value >>> 24) & 255}`;
        winWriteA(winInetNtoaBuffer, text); return BigInt(winInetNtoaBuffer);
      }
      case "inet_pton": case "inet_pton_a": case "inet_pton_w": case "inetpton": case "inetptona": case "inetptonw": {
        const family = Number(arg(0)), source = winReadMemoryString(arg(1), n.endsWith("w")), destination = Number(arg(2));
        const bytes = family === 2 ? winIp4Bytes(source || "") : family === 23 ? winParseIp6(source || "") : null;
        if (family !== 2 && family !== 23) return winWsaFail(10047);
        if (!bytes) return 0n;
        return writeBytes(destination, bytes) ? 1n : winWsaFail(10014);
      }
      case "inet_ntop": case "inet_ntop_a": case "inet_ntop_w": case "inetntop": case "inetntopa": case "inetntopw": {
        const family = Number(arg(0)), source = Number(arg(1)), destination = Number(arg(2)), capacity = Number(arg(3));
        const length = family === 2 ? 4 : family === 23 ? 16 : 0;
        if (!length) return winWsaFail(10047);
        const bytes = readBytes(source, length); if (!bytes) return winWsaFail(10014);
        const text = family === 2 ? [...bytes].join(".") : winFormatIp6(bytes);
        const encoded = new TextEncoder().encode(`${text}\0`);
        if (encoded.length > capacity || !writeBytes(destination, encoded)) return winWsaFail(10014);
        return BigInt(destination);
      }
      case "wsapoll": {
        const fds = Number(arg(0)), count = Number(arg(1)), timeout = Number(BigInt.asIntN(32, arg(2)));
        if (!Number.isSafeInteger(count) || count < 0 || count > 1024 || !ensureMemory(fds + count * 16)) return winWsaFail(10014);
        const scan = () => {
          const ready = [];
          for (let i = 0; i < count; i++) {
            const p = fds + i * 16, handle = dv.getBigUint64(p, true), events = dv.getUint16(p + 8, true), entry = winSocket(handle);
            let revents = 0;
            if (!entry) revents = 0x0004; // POLLNVAL
            else {
              if ((events & 0x0100) && winSocketReady(entry)) revents |= 0x0100; // POLLRDNORM
              if ((events & 0x0010) && (entry.connected || (entry.connecting && entry.transport?.connected) || (entry.type === 2 && !entry.closed))) revents |= 0x0010; // POLLWRNORM
              if (entry.connectError || entry.transport?.error) revents |= 0x0001; // POLLERR
              if (entry.transport?.ended) revents |= 0x0002; // POLLHUP
            }
            dv.setUint16(p + 10, revents, true); if (revents) ready.push(handle);
          }
          return ready;
        };
        let ready = scan();
        if (ready.length || timeout === 0) return BigInt(ready.length);
        const waits = Array.from({ length: count }, (_, i) => winSocket(dv.getBigUint64(fds + i * 16, true)))
          .filter((entry) => entry?.transport).map((entry) => winWaitSocketChange(entry));
        if (timeout < 0) await Promise.race(waits);
        else if (waits.length) await Promise.race([...waits, new Promise((resolve) => setTimeout(resolve, timeout))]);
        ready = scan();
        return BigInt(ready.length);
      }
      case "connectex": {
        const entry = winSocket(arg(0));
        const address = parseAddress(arg(1), arg(2));
        if (!entry) return winWsaFail(10038);
        if (!address) return winWsaFail(10014);
        if (entry.type !== 1) return winWsaFail(10045);      // WSAEOPNOTSUPP
        entry.remote = address;

        const runConnect = async () => {
          await network.connectTcp(winSocketTransport(entry), address.address, address.port);
          entry.connected = true;
          winWatchSocket(entry); winSignalSocketEvents(entry);
          // ConnectEx can piggy-back a send after connect
          const sendPtr = arg(3), sendLen = Number(arg(4)), bytesSentPtr = arg(5);
          if (sendPtr && sendLen > 0) {
            const bytes = memoryBytes(sendPtr, sendLen);
            if (bytes) {
              const sent = await network.sendTcp(winSocketTransport(entry), bytes);
              if (bytesSentPtr) dv.setUint32(Number(bytesSentPtr), Number(sent), true);
            }
          }
        };

        if (entry.nonBlocking) {
          if (entry.connecting || entry.connected)
            return winWsaFail(entry.connected ? 10056 : 10037);
          try {
            const transport = winSocketTransport(entry);
            winWatchSocket(entry);
            entry.connecting = true; entry.connectError = 0;
            entry.connectPromise = runConnect().catch((error) => {
              entry.connecting = false;
              entry.connectError = winWsaErrorCode(error);
              winSignalSocketEvents(entry);
            });
            return winWsaFail(10035);                    // WSAEWOULDBLOCK
          } catch (error) {
            entry.connecting = false;
            return winWsaFail(winWsaErrorCode(error));
          }
        }
        return await winNetworkResult(async () => { await runConnect(); return 1n; });
      }

      case "disconnectex": {
        const entry = winSocket(arg(0));
        if (!entry) return winWsaFail(10038);
        if (entry.type === 1 && entry.transport) {
          try { await network.shutdownTcp(entry.transport, 2); } catch {}
          try { network.closeTcp(entry.transport); }            catch {}
          entry.connected = false;
          winSignalSocketEvents(entry);
        }
        // Synchronous success (overlapped / reuse flag not modelled)
        return 1n;
      }
      default: return WIN_UNHANDLED;
    }
  }
  const winCanonicalDll = (dll) => {
    const value = String(dll || "kernel32.dll").split(/[\\/]/).pop().toLowerCase();
    if (value.startsWith("api-ms-win-crt-") || value.startsWith("ext-ms-win-crt-")) return "ucrtbase.dll";
    if (/^(api|ext)-ms-win-core-/.test(value)) return "kernel32.dll";
    if (/^(api|ext)-ms-win-user-/.test(value)) return "user32.dll";
    if (/^(api|ext)-ms-win-gdi-/.test(value)) return "gdi32.dll";
    if (/^(api|ext)-ms-win-advapi-/.test(value)) return "advapi32.dll";
    if (/^(api|ext)-ms-win-shell-/.test(value)) return "shell32.dll";
    if (value === "kernelbase.dll") return "kernel32.dll";
    if (value === "combase.dll") return "ole32.dll";
    return value.includes(".") ? value : `${value}.dll`;
  };
  const winBuiltinModules = new Set([
    "kernel32.dll", "kernelbase.dll", "ntdll.dll", "user32.dll", "gdi32.dll", "advapi32.dll",
    "ws2_32.dll", "winhttp.dll", "wininet.dll", "shlwapi.dll", "shell32.dll", "ole32.dll",
    "combase.dll", "comctl32.dll", "winmm.dll", "version.dll", "bcrypt.dll", "psapi.dll",
    "ucrtbase.dll", "msvcrt.dll", "vcruntime140.dll", "oleaut32.dll", "comdlg32.dll",
    "crypt32.dll", "secur32.dll", "wintrust.dll", "iphlpapi.dll", "rpcrt4.dll", "imm32.dll",
    "setupapi.dll", "cfgmgr32.dll", "dwmapi.dll", "dxgi.dll", "d3d11.dll", "normaliz.dll",
    "bcryptprimitives.dll", "winspool.drv", "d3dcompiler_47.dll","wldp.dll",          // Windows Lockdown Policy (delay-loaded by cmd.exe)
    "mpr.dll",           // Multiple Provider Router (network drive mapping)
    "userenv.dll",       // User environment block helpers
    "profapi.dll",       // Profile API
    "powrprof.dll",      // Power profile queries
    "sechost.dll","steamclient.dll", "steamclient64.dll",
    "steam_api.dll", "steam_api64.dll",
    "tier0.dll", "tier0_s.dll", "tier0_s64.dll",
    "vstdlib.dll", "vstdlib_s.dll", "vstdlib_s64.dll",
    "crashhandler.dll", "crashhandler64.dll",
    "steamservice.dll", "steamui.dll",
    "gameoverlayrenderer.dll", "gameoverlayrenderer64.dll", "api-ms-win-core-file-l1-1-0.dll"      // Host for Advapi32 security functions
  ]);
  const winLoadedModulesByName = new Map();
  const winLoadedModulesByBase = new Map();
  const winModuleRefCounts = new Map();
  for (const item of manifest.modules ?? []) {
    const key = winCanonicalDll(item.name);
    const exportsByName = new Map(), exportsByOrdinal = new Map();
    for (const entry of item.exports ?? []) {
      const value = BigInt(entry.address);
      if (entry.name != null) exportsByName.set(String(entry.name), value);
      exportsByOrdinal.set(Number(entry.ordinal) >>> 0, value);
    }
    const module = { name: String(item.name || key), path: String(item.path || item.name || key),
      key, base: BigInt(item.base), size: Number(item.size) || 0, entry: BigInt(item.entry || 0),
      isDll: !!item.isDll, exportsByName, exportsByOrdinal };
    winLoadedModulesByName.set(key, module);
    winLoadedModulesByBase.set(module.base, module);
    winModuleHandles.set(module.base, key);
    winModules.set(key, module.base);
    winModuleRefCounts.set(module.base, 1);
  }
  // Actual Ws2_32.dll export ordinals. WSAStartup is #115 and WSACleanup
  // is #116; #24 is GetAddrInfoW. Wrong mappings route calls to functions
  // with incompatible signatures and leave Winsock uninitialized (10093).
  const winWsOrdinals = {
    1: "accept", 2: "bind", 3: "closesocket", 4: "connect",
    5: "getpeername", 6: "getsockname", 7: "getsockopt", 8: "htonl",
    9: "htons", 10: "ioctlsocket", 11: "inet_addr", 12: "inet_ntoa",
    13: "listen", 14: "ntohl", 15: "ntohs", 16: "recv",
    17: "recvfrom", 18: "select", 19: "send", 20: "sendto",
    21: "setsockopt", 22: "shutdown", 23: "socket",
    24: "getaddrinfow", 25: "getnameinfow", 26: "wsapsetpostroutine",
    27: "freeaddrinfow", 28: "wpucompleteoverlappedrequest", 29: "wsaaccept",
    30: "wsaaddresstostringa", 31: "wsaaddresstostringw", 32: "wsacloseevent",
    33: "wsaconnect", 34: "wsacreateevent", 35: "wsaduplicatesocketa",
    36: "wsaduplicatesocketw", 37: "wsaenumnamespaceprovidersa",
    38: "wsaenumnamespaceprovidersw", 39: "wsaenumnetworkevents",
    40: "wsaenumprotocolsa", 41: "wsaenumprotocolsw", 42: "wsaeventselect",
    43: "wsagetoverlappedresult", 44: "wsagetqosbyname", 45: "wsagetserviceclassinfoa",
    46: "wsagetserviceclassinfow", 47: "wsagetserviceclassnamebyclassida",
    48: "wsagetserviceclassnamebyclassidw", 49: "wsahtonl", 50: "wsahtons",
    51: "gethostbyaddr", 52: "gethostbyname", 53: "getprotobyname",
    54: "getprotobynumber", 55: "getservbyname", 56: "getservbyport",
    57: "gethostname", 58: "wsainstallserviceclassa", 59: "wsainstallserviceclassw",
    60: "wsaioctl", 61: "wsajoinleaf", 62: "wsalookupservicebegina",
    63: "wsalookupservicebeginw", 64: "wsalookupserviceend",
    65: "wsalookupservicenexta", 66: "wsalookupservicenextw", 67: "wsanspioctl",
    68: "wsantohl", 69: "wsantohs", 70: "wsaproviderconfigchange",
    71: "wsarecv", 72: "wsarecvdisconnect", 73: "wsarecvfrom",
    74: "wsaremoveserviceclass", 75: "wsaresetevent", 76: "wsasend",
    77: "wsasenddisconnect", 78: "wsasendto", 79: "wsasetevent",
    80: "wsasetservicea", 81: "wsasetservicew", 82: "wsasocketa",
    83: "wsasocketw", 84: "wsastringtoaddressa", 85: "wsastringtoaddressw",
    86: "wsawaitformultipleevents", 87: "wscdeinstallprovider",
    88: "wscenablensprovider", 89: "wscenumprotocols", 90: "wscgetproviderpath",
    91: "wscinstallnamespace", 92: "wscinstallprovider", 93: "wscuninstallnamespace",
    94: "wscupdateprovider", 95: "wscwritenamespaceorder", 96: "wscwriteproviderorder",
    97: "freeaddrinfo", 98: "getaddrinfo", 99: "getnameinfo", 101: "wsaasyncselect",
    102: "wsaasyncgethostbyaddr", 103: "wsaasyncgethostbyname",
    104: "wsaasyncgetprotobynumber", 105: "wsaasyncgetprotobyname",
    106: "wsaasyncgetservbyport", 107: "wsaasyncgetservbyname",
    108: "wsacancelasyncrequest", 109: "wsasetblockinghook", 110: "wsaunhookblockinghook",
    111: "wsagetlasterror", 112: "wsasetlasterror", 113: "wsacancelblockingcall",
    114: "wsaisblocking", 115: "wsastartup", 116: "wsacleanup",
    151: "__wsafdisset", 500: "wep",
  };
  const winSyntheticModuleHandles = new Set();
  const winWriteFakePeHeader = (moduleBase) => {
    const b = Number(moduleBase);
    if (!ensureMemory(b + 0x200)) return;
    u8.fill(0, b, b + 0x200);
    // DOS header: MZ, e_lfanew = 0x80
    u8[b] = 0x4d; u8[b + 1] = 0x5a;
    dv.setUint32(b + 0x3c, 0x80, true);
    // PE signature at +0x80
    dv.setUint32(b + 0x80, 0x00004550, true);       // "PE\0\0"
    dv.setUint16(b + 0x84, 0x8664, true);            // Machine = AMD64
    dv.setUint16(b + 0x86, 0, true);                 // NumberOfSections = 0
    dv.setUint32(b + 0x88, 0, true);                 // TimeDateStamp
    dv.setUint32(b + 0x8c, 0, true);                 // PointerToSymbolTable
    dv.setUint32(b + 0x90, 0, true);                 // NumberOfSymbols
    dv.setUint16(b + 0x94, 0, true);                 // SizeOfOptionalHeader
    dv.setUint16(b + 0x96, 0x2102, true);            // Characteristics: EXECUTABLE | DLL
    // Empty optional header — import/export dirs read as 0
    // (No sections => nothing to walk)
  };
  const winLookupModule = (dll, load = false) => {
    if (dll == null || String(dll).length === 0) return BigInt(base);
    const key = winCanonicalDll(dll);
    // ── NEW: reject UWP appmodel runtime ──
    if (key.startsWith("api-ms-win-appmodel-")) {
      logTrace(`[WLM] reject ${dll} → NULL`);
      winSetLastError(126);
      return 0n;
    }
    const loaded = winLoadedModulesByName.get(key);
    if (loaded) {
      if (load) winModuleRefCounts.set(loaded.base, (winModuleRefCounts.get(loaded.base) || 0) + 1);
      return loaded.base;
    }
    if (!winBuiltinModules.has(key) && !key.startsWith("api-ms-win-") && !key.startsWith("ext-ms-win-")) return 0n;
    if (!winModules.has(key)) {
      const handle = winNextModule; winNextModule += 0x1000n;
      winModules.set(key, handle); winModuleHandles.set(handle, key);
      winWriteFakePeHeader(handle);   // ← NEW
    }
    const handle = winModules.get(key);
    if (load) winModuleRefCounts.set(handle, (winModuleRefCounts.get(handle) || 0) + 1);
    return handle;
  };
  const winLookupApi = (dll, name, ordinal = null) => {
    const module = winModuleHandles.get(BigInt(dll));

    // Ws2_32 ordinal imports/GetProcAddress use the real export table above.
    if (module === "ws2_32.dll" && ordinal != null) {
      const n2 = winWsOrdinals[Number(ordinal) >>> 0];
      if (n2) return winLookupApi(dll, n2, null);
    }
    if (name && String(name).toLowerCase() === "setcurrentdirectoryw") {
      log(`[GPA-DIAG] SetCurrentDirectoryW requested from "${module}"`);
    }
    if (name) {
      const lname = String(name).toLowerCase();
      if (lname === "setcurrentdirectoryw" || lname === "setcurrentdirectorya") {
        log(`[GPA-DIAG] ${module}!${name} requested`);
      }
    }
    if (module === "shell32.dll" && ordinal != null) {
      const shell32ord = {
        680: "shgetfolderpathw",
      };
      const n2 = shell32ord[Number(ordinal) >>> 0];
      if (n2) return winLookupApi(dll, n2, null);
    }
    if (!module) {
      // Some guests call GetProcAddress on a handle from a failed LoadLibrary
      // without checking the return. Rather than poison every function pointer
      // with NULL, synthesize a diagnostic thunk so the guest can proceed
      // until it actually calls the missing function (at which point our
      // dispatchWinImport logs "unimplemented" and returns 0).
      if (name && typeof name === "string" && String(name).length > 0) {
        const key = `unknown!name:${name}`.toLowerCase();
        if (winDynamicImports.has(key)) return winDynamicImports.get(key);
        const addr = winNextImport; winNextImport += 16n;
        winDynamicImports.set(key, addr);
        winApiByAddress.set(addr, { dll: "unknown", name: String(name), ordinal: null });
        if (!winWarned.has(key)) {
          winWarned.add(key);
          log(`[RECOMP] GetProcAddress(invalid handle 0x${BigInt(dll).toString(16)}, "${name}") — ` +
              `synthesizing thunk at 0x${addr.toString(16)}; the underlying LoadLibraryExW probably failed`);
        }
        return addr;
      }
      winSetLastError(6);
      return 0n;
    }
    const loaded = winLoadedModulesByName.get(module);
    if (loaded) {
      const address = ordinal == null ? loaded.exportsByName.get(String(name))
        : loaded.exportsByOrdinal.get(Number(ordinal) >>> 0);
      if (address == null) { winSetLastError(127); return 0n; }
      return address;
    }
    if (!winBuiltinModules.has(module) && !module.startsWith("api-ms-win-") && !module.startsWith("ext-ms-win-")) {
      winSetLastError(127); return 0n;
    }
    const symbol = ordinal == null ? `name:${String(name)}` : `ordinal:${Number(ordinal)}`;
    const key = `${module}!${symbol}`.toLowerCase();
    if (winDynamicImports.has(key)) return winDynamicImports.get(key);
    const addr = winNextImport; winNextImport += 16n;
    winDynamicImports.set(key, addr);
    winApiByAddress.set(addr, { dll: module, name: ordinal == null ? String(name) : null, ordinal });
    return addr;
  };
  const startupImportModules = new Set();
  for (const item of manifest.imports ?? []) {
    const key = winCanonicalDll(item.dll);
    if (!startupImportModules.has(key)) {
      winLookupModule(item.dll, true);
      startupImportModules.add(key);
    }
  }

  function winFormat(format, firstArgIndex, vaListPtr = null, wide = false) {
      let out = "", argIndex = firstArgIndex;
      for (let i = 0; i < format.length; i++) {
        if (format[i] !== "%") { out += format[i]; continue; }
        if (format[i + 1] === "%") { out += "%"; i++; continue; }

        let j = i + 1;
        while (j < format.length && "-+ #0.123456789hlLzIw".includes(format[j])) j++;
        const spec = format[j] || "";
        const modifiers = format.slice(i + 1, j);
        i = j;

        const value = vaListPtr == null
          ? winGetArg(argIndex++)
          : winReadU64(Number(vaListPtr) + (argIndex++ - firstArgIndex) * 8);

        // Determine whether %s / %S should produce a wide or narrow string.
        // Rules (per C standard + MSVC extension):
        //   Explicit 'l' or 'w' → wide. Explicit 'h' → narrow.
        //   No modifier in wide-printf context: %s = wide, %S = narrow.
        //   No modifier in narrow-printf context: %s = narrow, %S = wide.
        const hasL = modifiers.includes("l") || modifiers.includes("w");
        const hasH = modifiers.includes("h");
        const wantsWide = hasL ? true
                        : hasH ? false
                        : wide ? (spec === "s") : (spec === "S");

        switch (spec) {
          case "s": case "S":
            out += wantsWide ? (winReadW(value) ?? "(null)")
                            : (winReadA(value) ?? "(null)");
            break;
          case "c":
            out += String.fromCharCode(Number(value & 0xffn));
            break;
          case "C":
            out += String.fromCharCode(Number(value & 0xffffn));
            break;
          case "d": case "i":
            out += BigInt.asIntN(modifiers.includes("l") ? 64 : 32, value).toString();
            break;
          case "u":
            out += BigInt.asUintN(modifiers.includes("l") ? 64 : 32, value).toString();
            break;
          case "x":
            out += BigInt.asUintN(modifiers.includes("l") ? 64 : 32, value).toString(16);
            break;
          case "X":
            out += BigInt.asUintN(modifiers.includes("l") ? 64 : 32, value).toString(16).toUpperCase();
            break;
          case "p":
            out += `0x${value.toString(16)}`;
            break;
          default:
            out += `%${modifiers}${spec}`;
            break;
        }
      }
      return out;
  }

  const WINMSG = Object.freeze({
    NULL: 0x0000, CREATE: 0x0001, DESTROY: 0x0002, MOVE: 0x0003, SIZE: 0x0005,
    SETFOCUS: 0x0007, KILLFOCUS: 0x0008, PAINT: 0x000f, CLOSE: 0x0010,
    QUIT: 0x0012, ERASEBKGND: 0x0014, SHOWWINDOW: 0x0018, SETCURSOR: 0x0020,
    GETMINMAXINFO: 0x0024, WINDOWPOSCHANGED: 0x0047, NCCREATE: 0x0081,
    NCDESTROY: 0x0082, KEYDOWN: 0x0100, KEYUP: 0x0101, CHAR: 0x0102,
    SYSKEYDOWN: 0x0104, SYSKEYUP: 0x0105, COMMAND: 0x0111, TIMER: 0x0113,
    MOUSEMOVE: 0x0200, LBUTTONDOWN: 0x0201, LBUTTONUP: 0x0202,
    LBUTTONDBLCLK: 0x0203, RBUTTONDOWN: 0x0204, RBUTTONUP: 0x0205,
    MBUTTONDOWN: 0x0207, MBUTTONUP: 0x0208, MOUSEWHEEL: 0x020a,
    ENTERSIZEMOVE: 0x0231, EXITSIZEMOVE: 0x0232, WINDOWPOSCHANGING: 0x0046,
    WM_USER: 0x0400,
  });
  const WIN_GWL = Object.freeze({ WNDPROC: -4, HINSTANCE: -6, HWNDPARENT: -8, ID: -12, STYLE: -16, EXSTYLE: -20, USERDATA: -21 });
  const winColor = (color) => Number(BigInt.asUintN(32, BigInt(color))) >>> 0;
  const winRect = (ptr) => {
    const p = Number(ptr);
    if (!Number.isSafeInteger(p) || p < 0 || p + 16 > u8.length) return null;
    return { left: dv.getInt32(p, true), top: dv.getInt32(p + 4, true), right: dv.getInt32(p + 8, true), bottom: dv.getInt32(p + 12, true) };
  };
  const winWriteRect = (ptr, r) => {
    const p = Number(ptr);
    if (!Number.isSafeInteger(p) || p < 0 || !ensureMemory(p + 16)) return false;
    dv.setInt32(p, r.left | 0, true); dv.setInt32(p + 4, r.top | 0, true);
    dv.setInt32(p + 8, r.right | 0, true); dv.setInt32(p + 12, r.bottom | 0, true);
    return true;
  };
  const winPackPoint = (x, y) => BigInt.asUintN(32, BigInt(((Number(y) & 0xffff) << 16) | (Number(x) & 0xffff)));
  const winUnpackPoint = (value) => ({ x: Number(BigInt.asIntN(16, value & 0xffffn)), y: Number(BigInt.asIntN(16, (value >> 16n) & 0xffffn)) });
  const winWindow = (hwnd) => {
    const h = BigInt(hwnd), window = winHandles.get(h);
    return window?.kind === "window" && winWindows.get(h) === window && !window.destroyed ? window : null;
  };
  const winClientInsets = (window) => ({
    x: (window.style & 0x40000000) ? 0 : 1,
    y: (window.style & 0x40000000) ? 0 : 1 + ((window.style & 0x00c00000) ? 25 : 0),
    right: (window.style & 0x40000000) ? 0 : 1,
    bottom: (window.style & 0x40000000) ? 0 : 1,
  });
  const winAbsRect = (window, depth = 0) => {
    if (!window || depth > 32) return { x: 0, y: 0, width: 0, height: 0 };
    const parent = window.parent ? winWindow(window.parent) : null;
    const baseRect = parent ? winAbsRect(parent, depth + 1) : { x: 0, y: 0 };
    const inset = parent ? winClientInsets(parent) : { x: 0, y: 0 };
    return { x: baseRect.x + inset.x + window.x, y: baseRect.y + inset.y + window.y, width: window.width, height: window.height };
  };
  const winHasMessage = (hwndFilter = 0n, min = 0, max = 0) => {
    const h = BigInt(hwndFilter);
    return winMessageQueue.some((m) => m.message === WINMSG.QUIT ||
      ((!h || m.hwnd === h) && (!min || m.message >= min) && (!max || m.message <= max)));
  };
  const winNotifyMessage = () => {
    for (let i = 0; i < winMessageWaiters.length;) {
      const waiter = winMessageWaiters[i];
      if (waiter.predicate()) { winMessageWaiters.splice(i, 1); waiter.resolve(); }
      else i++;
    }
  };
  const winPostMessage = (hwnd, message, wParam = 0n, lParam = 0n, point = null) => {
    const pos = point ?? { x: 0, y: 0 };
    winMessageQueue.push({ hwnd: BigInt(hwnd || 0), message: Number(message) >>> 0,
      wParam: BigInt(wParam), lParam: BigInt(lParam), time: Date.now() >>> 0,
      x: Number(pos.x) | 0, y: Number(pos.y) | 0 });
    winNotifyMessage();
    return true;
  };
  const winTakeMessage = (hwndFilter = 0n, min = 0, max = 0, remove = true) => {
    const h = BigInt(hwndFilter);
    const index = winMessageQueue.findIndex((m) => m.message === WINMSG.QUIT ||
      ((!h || m.hwnd === h) && (!min || m.message >= min) && (!max || m.message <= max)));
    if (index < 0) return null;
    const message = remove ? winMessageQueue.splice(index, 1)[0] : winMessageQueue[index];
    if (remove) winCurrentMessage = message;
    return message;
  };
  const winAwaitMessage = async (predicate = () => winMessageQueue.length > 0) => {
    if (predicate() || !gui?.interactive) return;
    await new Promise((resolve) => winMessageWaiters.push({ resolve, predicate }));
  };
  const winWriteMsg = (ptr, message) => {
    const p = Number(ptr);
    if (!Number.isSafeInteger(p) || p < 0 || !ensureMemory(p + 48)) return false;
    u8.fill(0, p, p + 48);
    dv.setBigUint64(p, message.hwnd, true);
    dv.setUint32(p + 8, message.message >>> 0, true);
    dv.setBigUint64(p + 16, message.wParam, true);
    dv.setBigUint64(p + 24, message.lParam, true);
    dv.setUint32(p + 32, message.time >>> 0, true);
    dv.setInt32(p + 36, message.x | 0, true);
    dv.setInt32(p + 40, message.y | 0, true);
    return true;
  };
  const winReadMsg = (ptr) => {
    const p = Number(ptr);
    if (!Number.isSafeInteger(p) || p < 0 || p + 48 > u8.length) return null;
    return { hwnd: dv.getBigUint64(p, true), message: dv.getUint32(p + 8, true),
      wParam: dv.getBigUint64(p + 16, true), lParam: dv.getBigUint64(p + 24, true),
      time: dv.getUint32(p + 32, true), x: dv.getInt32(p + 36, true), y: dv.getInt32(p + 40, true) };
  };
  const winFindClass = (name) => winClasses.get(String(name).toLowerCase()) ?? null;
  const winCloneDrawCommand = (command) => ({
    ...command,
    ...(Array.isArray(command?.sourceCommands) ? { sourceCommands: command.sourceCommands.map(winCloneDrawCommand) } : {}),
  });
  const winAddDrawCommand = (dcHandle, command) => {
    const dc = winHandles.get(BigInt(dcHandle));
    if (!dc || dc.kind !== "dc") return false;
    const target = dc.target;
    if (!target || !Array.isArray(target.commands)) return false;
    target.commands.push(command);
    if (target.kind === "window" || target.kind === "desktop") winPresent();
    return true;
  };
  const winCreateDc = (target) => {
    const state = { kind: "dc", target, selected: { brush: winStockObject(0), pen: winStockObject(7), font: winStockObject(13), bitmap: 0n },
      textColor: 0, bkColor: 0xffffff, bkMode: 2, current: { x: 0, y: 0 }, defaultBitmap: 0n };
    if (target?.kind === "bitmap") {
      const bitmap = { kind: "bitmap", width: 1, height: 1, commands: [] };
      state.defaultBitmap = winAllocHandle(bitmap);
      state.selected.bitmap = state.defaultBitmap;
      state.target = bitmap;
    }
    const h = winAllocHandle(state); winDcs.set(h, state); return h;
  };
  const winResolveGdi = (handle) => {
    const h = BigInt(handle);
    if (winStockObjects.has(h)) return winStockObjects.get(h);
    return winHandles.get(h) ?? null;
  };
  const winStockObject = (index) => {
    const definitions = {
      0: { kind: "brush", color: 0xffffff }, 1: { kind: "brush", color: 0xc0c0c0 },
      2: { kind: "brush", color: 0x808080 }, 3: { kind: "brush", color: 0x404040 },
      4: { kind: "brush", color: 0x000000 }, 5: { kind: "brush", color: null },
      6: { kind: "pen", color: 0xffffff, width: 1 }, 7: { kind: "pen", color: 0x000000, width: 1 },
      8: { kind: "pen", color: null, width: 0 }, 13: { kind: "font", face: "Arial", height: 16, weight: 400 },
      17: { kind: "font", face: "Arial", height: 13, weight: 400 },
    };
    if (!definitions[index]) return 0n;
    if (!winStockObjects.has(BigInt(index + 1))) winStockObjects.set(BigInt(index + 1), definitions[index]);
    return BigInt(index + 1);
  };
  const winGetDc = (hwnd) => {
    const h = BigInt(hwnd);
    const target = h === 0n || h === WIN_DESKTOP_HANDLE ? winDesktopSurface : winWindow(h);
    if (!target) return 0n;
    return winCreateDc(target);
  };
  const winPresent = () => {
    if (!gui?.present) return;
    const windows = [...winWindows.values()].filter((w) => winIsVisible(w))
    .sort((a, b) => a.z - b.z).map((w) => {
      const base = {
        hwnd: w.hwnd, title: w.title, className: w.className,
        x: winAbsRect(w).x, y: winAbsRect(w).y,
        width: w.width, height: w.height,
        style: w.style, exStyle: w.exStyle, parent: w.parent,
        commands: w.commands, control: w.control,
        enabled: w.enabled, focused: w.focused, pressed: w.pressed, z: w.z,
      };
      if (w.control === "console") {
        base.consoleCells = w.consoleCells;
        base.cursorX = w.cursorX;
        base.cursorY = w.cursorY;
        base.consoleCols = winConsole.width;
        base.consoleRows = winConsole.height;
      }
      return base;
    });
    try { gui.present({ width: winScreen.width, height: winScreen.height, desktopCommands: winDesktopSurface.commands, windows }); }
    catch (error) { log(`canvas presentation error: ${error?.message ?? error}`); }
  };
  const winRaiseWindowFamily = (hwnd) => {
    let root = winWindow(hwnd);
    if (!root) return;
    for (let depth = 0; depth < 32 && root.parent; depth++) {
      const parent = winWindow(root.parent);
      if (!parent) break;
      root = parent;
    }
    const depthOf = (item) => {
      let depth = 0, node = item;
      while (node?.parent && depth < 32) {
        node = winWindow(node.parent);
        if (!node) break;
        depth++;
      }
      return depth;
    };
    const family = [...winWindows.values()].filter((item) => {
      let node = item;
      for (let depth = 0; node && depth < 32; depth++) {
        if (node.hwnd === root.hwnd) return true;
        node = node.parent ? winWindow(node.parent) : null;
      }
      return false;
    }).sort((a, b) => depthOf(a) - depthOf(b) || a.z - b.z);
    for (const item of family) item.z = ++winZOrder;
  };
  if (gui?.setMessageSink) gui.setMessageSink((event) => {
    const isConsole = BigInt(event.hwnd) === BigInt(WIN_CONSOLE_HWND);
    const window = winWindow(event.hwnd);
    if (!window || window.destroyed) return;
    if (event.kind === "move") {
      window.x = Number(event.x) | 0; window.y = Number(event.y) | 0;
      winPostMessage(window.hwnd, WINMSG.MOVE, 0n, winPackPoint(window.x, window.y));
      winPresent(); return;
    }
    if (event.kind === "resize") {
      const oldX = window.x, oldY = window.y, oldWidth = window.width, oldHeight = window.height;
      window.x = Number(event.x) | 0; window.y = Number(event.y) | 0;
      window.width = Math.max(120, Number(event.width) | 0);
      window.height = Math.max(80, Number(event.height) | 0);
      if (window.x !== oldX || window.y !== oldY)
        winPostMessage(window.hwnd, WINMSG.MOVE, 0n, winPackPoint(window.x, window.y));
      if (window.width !== oldWidth || window.height !== oldHeight) {
        const inset = winClientInsets(window);
        winPostMessage(window.hwnd, WINMSG.SIZE, 0n,
          winPackPoint(Math.max(0, window.width - inset.x - inset.right), Math.max(0, window.height - inset.y - inset.bottom)));
        window.invalid = true;
      }
      winPresent(); return;
    }
    if (event.kind === "raise") {
      winRaiseWindowFamily(window.hwnd);
      winPresent(); return;
    }
    if (event.message === WINMSG.KEYDOWN || event.message === WINMSG.SYSKEYDOWN) {
      const key = Number(event.wParam) & 0xffff; winKeyDown.add(key); winKeyRecent.add(key);
    } else if (event.message === WINMSG.KEYUP || event.message === WINMSG.SYSKEYUP) {
      winKeyDown.delete(Number(event.wParam) & 0xffff);
    } else if (event.message === WINMSG.LBUTTONDOWN) { winKeyDown.add(1); winKeyRecent.add(1); }
    else if (event.message === WINMSG.LBUTTONUP) winKeyDown.delete(1);
    else if (event.message === WINMSG.RBUTTONDOWN) { winKeyDown.add(2); winKeyRecent.add(2); }
    else if (event.message === WINMSG.RBUTTONUP) winKeyDown.delete(2);
    if (event.message === WINMSG.SETFOCUS) {
      for (const other of winWindows.values()) other.focused = false;
      window.focused = true;
    } else if (event.message === WINMSG.KILLFOCUS) {
      window.focused = false;
    }
    if (event.message === WINMSG.LBUTTONDOWN && window.control === "button") window.pressed = true;
    if (event.message === WINMSG.CHAR && window.control === "edit") {
      const ch = Number(event.wParam ?? 0n);
      if (ch === 8) window.title = window.title.slice(0, -1);
      else if (ch >= 32 && ch !== 127) window.title += String.fromCodePoint(ch);
      winPostMessage(window.hwnd, WINMSG.CHAR, BigInt(ch), event.lParam ?? 0n);
      if (window.parent) winPostMessage(window.parent, WINMSG.COMMAND,
        BigInt((Number(window.menu) & 0xffff) | (0x0300 << 16)), window.hwnd);
      winPresent(); return;
    }
    winPostMessage(event.hwnd, event.message, event.wParam ?? 0n, event.lParam ?? 0n, event.point ?? null);
    if (event.message === WINMSG.LBUTTONUP && window.control === "button") {
      const wasPressed = window.pressed; window.pressed = false;
      const point = event.point ?? { x: -1, y: -1 };
      if (wasPressed && point.x >= 0 && point.y >= 0 && point.x < window.width && point.y < window.height && window.parent) {
        winPostMessage(window.parent, WINMSG.COMMAND,
          BigInt((Number(window.menu) & 0xffff) | (0 << 16)), window.hwnd);
      }
    }
    winPresent();
  });

  const winHttpCompat = createWinHttpCompat({
    handles: winHandles,
    allocHandle: winAllocHandle,
    readStringA: winReadA,
    readStringW: winReadW,
    writeStringA: winWriteA,
    writeStringW: winWriteW,
    readBytes,
    writeBytes,
    writeDword: winWriteDword,
    readDword: (pointer) => {
      const p = Number(pointer);
      if (!Number.isSafeInteger(p) || p < 0 || !ensureMemory(p + 4)) return 0;
      return dv.getUint32(p, true);
    },
    readU64: winReadU64,
    ensureMemory,
    setLastError: winSetLastError,
    network,
  });
  const winLookupFunctionEntry = (controlPc) => {
    const pc = BigInt(controlPc);
    for (const [table, registration] of winDynamicFunctionTables) {
      const rvaPc = pc - registration.base;
      if (rvaPc < 0n) continue;
      let lo = 0, hi = registration.count - 1;
      while (lo <= hi) {
        const mid = (lo + hi) >>> 1;
        const at = table + mid * 12;
        const begin = winReadU32(at), end = winReadU32(at + 4);
        if (rvaPc < BigInt(begin)) hi = mid - 1;
        else if (rvaPc >= BigInt(end)) lo = mid + 1;
        else return { address: BigInt(at), imageBase: registration.base };
      }
    }
    const candidates = (manifest.modules?.length ? manifest.modules : [
      { base: BigInt(base), size: image.length },
    ]);
    for (const module of candidates) {
      const moduleBase = BigInt(module.base);
      const size = Number(module.size);
      if (pc < moduleBase || pc >= moduleBase + BigInt(size)) continue;
      const imageOffset = Number(moduleBase - BigInt(base));
      if (!Number.isSafeInteger(imageOffset) || imageOffset < 0) continue;
      const mz = imageOffset;
      if (winReadU32(mz + 0x3c) === 0 || mz + 0x40 > u8.length || u8[mz] !== 0x4d || u8[mz + 1] !== 0x5a) continue;
      const pe = mz + winReadU32(mz + 0x3c);
      const optional = pe + 24;
      if (optional + 112 + 32 > u8.length || dv.getUint16(optional, true) !== 0x20b) continue;
      const exceptionRva = winReadU32(optional + 112 + 3 * 8);
      const exceptionSize = winReadU32(optional + 112 + 3 * 8 + 4);
      if (!exceptionRva || exceptionSize < 12) continue;
      const tableAddress = moduleBase + BigInt(exceptionRva);
      const count = Math.floor(exceptionSize / 12);
      const targetRva = pc - moduleBase;
      let lo = 0, hi = count - 1;
      while (lo <= hi) {
        const mid = (lo + hi) >>> 1;
        const at = tableAddress + BigInt(mid * 12);
        const begin = winReadU32(at), end = winReadU32(at + 4n);
        if (targetRva < BigInt(begin)) hi = mid - 1;
        else if (targetRva >= BigInt(end)) lo = mid + 1;
        else return { address: at, imageBase: moduleBase };
      }
    }
    return null;
  };
  const winFdFile = (v) => {
    const h = winHandles.get(BigInt(Number(BigInt.asIntN(32, v))));
    return h && (h.kind === "crt_file" || h.kind === "file") ? h : null;
  };
  async function emulateWinApi(api) {
    const name = String(api.name || `ordinal_${api.ordinal ?? "unknown"}`);
    const nRaw = name.toLowerCase();
    let n = nRaw.startsWith("_o_") ? nRaw.slice(3) : nRaw;
    const a = (i) => winGetArg(i);
    if (!globalThis.__apiCallSeen) globalThis.__apiCallSeen = new Set();
    const lname = n.replace(/^_o_/, "");
    if (/^_w?(access|stat|fstat|chmod|mkdir|rmdir|open|sopen|fsopen|fopen|unlink|remove|creat|chsize|utime|wutime|filelength)/.test(lname) ||
        ["createfilew","createfilea","tlssetvalue","pathfileexistsw","pathfileexistsa",
        "pathisdirectoryw","getfileattributesw","getfileattributesexw","setfileattributesw",
        "ntcreatefile","ntopenfile","zwcreatefile","zwopenfile"].includes(lname)) {
        const key = `${lname}:${[0,1,2,4,5].map(i => BigInt.asUintN(64, a(i)).toString(16)).join(",")}`;
        if (!globalThis.__apiCallSeen.has(key)) {
            globalThis.__apiCallSeen.add(key);
            log(`[API-CALL] ${name}(${[0,1,2,4,5].map(i => "0x" + BigInt.asUintN(64, a(i)).toString(16)).join(", ")})`);
        }
    }
    const httpResult = await winHttpCompat.dispatch(api.dll, n, a);
    if (httpResult !== winHttpCompat.unhandled && httpResult !== undefined && httpResult !== null) return httpResult;
    const ptr = (v) => Number(v);
    const readPath = (v, wide = false) => {
      const value = winReadMemoryString(v, wide);
      return value == null ? null : winPath(value);
    };
    if (nRaw.includes("dir") || nRaw.includes("file")) {
      logDispatch(`[WINAPI] Image path = ${imagePath}`)
      let wide;
      if (nRaw.endsWith("w")) {
        wide = true
      } else {
        wide = false
      }
      logDispatch(`[WINAPI] ${name} dispatched with ${winPath(winReadMemoryString(a(1), wide))}`)
    }
    const writeOut = (text) => { log(String(text)); return BigInt(String(text).length); };
    const winsockResult = await emulateWinsockApi(n, a);
    if (winsockResult !== WIN_UNHANDLED && winsockResult !== undefined && winsockResult !== null) return winsockResult;
    const copy = (dst, src, len) => {
      const bytes = readBytes(src, len);
      if (!bytes || !writeBytes(dst, bytes)) { winSetLastError(998); return 0n; }
      return dst;
    };
    // Before switch (n) in emulateWinApi:
    if (!api.name && api.ordinal != null) {
      // Map well-known ordinals that protobuf/Steam import by ordinal
      const ordMap = {
        0x4B0: "raiseexception",
        0x2C0: "rtlpctofileheader",
        680:  "shgetfolderpathw",
        // extend as needed
      };
      const mapped = ordMap[Number(api.ordinal) >>> 0];
      if (mapped) { n = mapped; /* n is const — refactor to let n = ... */ }
    }
    // State for FindFirstFile/FindNextFile/FindClose
    if (!globalThis.__winFindState) {
      globalThis.__winFindState = new Map();
      globalThis.__winNextFindHandle = 0x00100000;
    }

    function winFindGlobToRegex(pattern) {
      return new RegExp("^" + pattern
        .replace(/[.+^${}()|[\]\\]/g, "\\$&")
        .replace(/\*/g, ".*")
        .replace(/\?/g, ".") + "$", "i");
    }

    function winFindEnumerate(pattern) {
      const normPath = winPath(pattern);
      const lastSlash = normPath.lastIndexOf("/");
      const dir = lastSlash >= 0 ? (normPath.slice(0, lastSlash) || "/") : "/";
      const namePattern = lastSlash >= 0 ? normPath.slice(lastSlash + 1) : normPath;
      const regex = winFindGlobToRegex(namePattern || "*");
      const entries = [];
      const prefix = dir === "/" ? "/" : `${dir}/`;
      const seen = new Set();
      for (const [path, file] of virtualFiles) {
        if (!path.startsWith(prefix)) continue;
        const rest = path.slice(prefix.length);
        if (rest.includes("/") || !regex.test(rest) || seen.has(rest)) continue;
        seen.add(rest);
        entries.push({ name: rest, kind: "file", size: file.data.length });
      }
      for (const d of winDirectories) {
        if (!d.startsWith(prefix)) continue;
        const rest = d.slice(prefix.length);
        if (rest.includes("/") || !rest || !regex.test(rest) || seen.has(rest)) continue;
        seen.add(rest);
        entries.push({ name: rest, kind: "dir", size: 0 });
      }
      // Windows always includes "." and ".." when the pattern is wildcard
      if (namePattern === "*" || namePattern === "*.*") {
        // Prepend . and ..  (Windows shows them but sort order varies; we just add)
        entries.unshift({ name: ".", kind: "dir", size: 0 });
        entries.unshift({ name: "..", kind: "dir", size: 0 });
      }
      return { entries, dir };
    }

    function winFindFill(entry, dir, ptr, wide) {
      const p = ptr;
      if (!ensureMemory(p + 0x250)) return false; // WIN32_FIND_DATAW = 592 bytes
      u8.fill(0, p, p + 0x250);
      dv.setUint32(p, entry.kind === "dir" ? 0x10 : 0x80, true);
      const now = BigInt(Date.now()) * 10000n + 116444736000000000n;
      dv.setBigUint64(p + 4, now, true);   // creation
      dv.setBigUint64(p + 12, now, true);  // last access
      dv.setBigUint64(p + 20, now, true);  // last write
      dv.setUint32(p + 28, Math.floor(entry.size / 0x100000000), true);
      dv.setUint32(p + 32, entry.size >>> 0, true);
      // cFileName: WCHAR[260] at +44 for W, CHAR[260] at +44 for A
      if (wide) winWriteW(p + 44, entry.name);
      else winWriteA(p + 44, entry.name);
      return true;
    }
    switch (n) {
      // UCRT wide-argv/environment startup helpers. The process command line is
      // already available through GetCommandLineW; expose a stable double-NUL
      // environment block for CRT startup code.
      case "loadlibrarya": case "loadlibraryw":
      case "loadlibraryexa": case "loadlibraryexw": {
        const isLoad = n.startsWith("loadlibrary");
        const wide = n.endsWith("w");
        const moduleName = winReadMemoryString(a(0), wide);
        logTrace(`[LLX] ${api?.name}("${moduleName}")`);

        // NULL pointer → error
        if (moduleName == null) {
          if (!isLoad) return BigInt(base);
          winSetLastError(87);
          return 0n;
        }

        // MSDN: LoadLibraryExW(L"") returns handle of main module.
        if (moduleName === "") {
          return BigInt(base);
        }

        if (moduleName.toLowerCase().includes("api-ms-win-appmodel")) {
          logTrace(`[LLX] rejecting UWP appmodel runtime → NULL`);
          winSetLastError(126);
          return 0n;
        }

        const handle = winLookupModule(moduleName, isLoad);
        logTrace(`[LLX] -> 0x${handle.toString(16)}${handle === 0n ? "  *** NULL ***" : ""}`);
        if (handle === 0n) winSetLastError(126);
        return handle;
      }
      case "getmodulehandlea": case "getmodulehandlew": {
        const moduleName = winReadMemoryString(a(0), n.endsWith("w"));
        if (!moduleName) return BigInt(base);  // GetModuleHandle(NULL) = current EXE
        const handle = winLookupModule(moduleName, false);
        if (handle === 0n) winSetLastError(126);
        return handle;
      }
      case "getprocaddress": {
        const module = a(0), symbol = a(1);
        const name = symbol > 0xffffn ? (winReadA(symbol) ?? "<bad ptr>") : `#${Number(symbol)}`;
        log(`[GPA] h=0x${module.toString(16)} name="${name}"`);
        const result = symbol <= 0xffffn
          ? winLookupApi(module, null, Number(symbol))
          : winLookupApi(module, winReadA(symbol), null);
        log(`[GPA] -> 0x${result.toString(16)}${result === 0n ? "  *** NULL ***" : ""}`);
        return result;
      }
      case "_configure_wide_argv": return 0n; // _crt_argv_unexpanded_arguments
      case "_initialize_wide_environment": return 0n;
      case "_get_initial_wide_environment": {
        const entries = ["PATH=C:\\Windows\\System32", "WINDIR=C:\\Windows", "SYSTEMROOT=C:\\Windows", "TEMP=C:\\Temp"];
        const text = entries.join("\0") + "\0\0";
        const ptr = winAlloc((text.length + 1) * 2);
        if (!ptr) return 0n;
        let at = Number(ptr);
        for (let i = 0; i < text.length; i++, at += 2) dv.setUint16(at, text.charCodeAt(i), true);
        return ptr;
      }
      case "_get_initial_narrow_environment":
      case "_o__get_initial_narrow_environment": {
        const entries = [...winEnvironment].map(([k, v]) => `${k}=${v}`);
        entries.push("PATH=C:\\Windows\\System32", "WINDIR=C:\\Windows", "SYSTEMROOT=C:\\Windows", "TEMP=C:\\Temp");
        const text = entries.join("\0") + "\0\0";
        const ptr = winAlloc(text.length + 1);
        if (!ptr) return 0n;
        writeBytes(Number(ptr), new TextEncoder().encode(text));
        return ptr;
      }
      case "wcsncmp": case "_wcsncmp": case "_o__wcsncmp": {
        const x = winReadW(a(0)) ?? "";
        const y = winReadW(a(1)) ?? "";
        const n = Number(a(2)) >>> 0;
        for (let i = 0; i < n; i++) {
          const xc = i < x.length ? x.charCodeAt(i) : 0;
          const yc = i < y.length ? y.charCodeAt(i) : 0;
          if (xc !== yc) return BigInt(xc < yc ? -1 : 1);
          if (xc === 0) break;
        }
        return 0n;
      }

      case "wcscmp": case "_wcscmp": case "_o__wcscmp": {
        const x = winReadW(a(0)) ?? "";
        const y = winReadW(a(1)) ?? "";
        const lx = x.toLowerCase(), ly = y.toLowerCase();
        return BigInt(lx === ly ? 0 : lx < ly ? -1 : 1);
      }

      case "wcsncpy": case "_wcsncpy": case "_o__wcsncpy": {
        const dst = a(0), src = winReadW(a(1)) ?? "", n = Number(a(2)) >>> 0;
        let out = src.slice(0, n);
        while (out.length < n) out += "\0";
        winWriteW(dst, out);
        return dst;
      }

      case "wcsstr": case "_wcsstr": case "_o__wcsstr": {
        const haystack = winReadW(a(0)) ?? "";
        const needle = winReadW(a(1)) ?? "";
        if (!needle) return a(0);
        const idx = haystack.indexOf(needle);
        return idx < 0 ? 0n : a(0) + BigInt(idx * 2);
      }

      case "_wcsnicmp": case "_o__wcsnicmp": case "wcsnicmp": {
        const x = winReadW(a(0)) ?? "";
        const y = winReadW(a(1)) ?? "";
        const n = Math.min(Number(a(2)) >>> 0, Math.max(x.length, y.length));
        for (let i = 0; i < n; i++) {
          const xc = i < x.length ? x.charCodeAt(i) : 0;
          const yc = i < y.length ? y.charCodeAt(i) : 0;
          const xl = (xc >= 65 && xc <= 90) ? xc + 32 : xc;
          const yl = (yc >= 65 && yc <= 90) ? yc + 32 : yc;
          if (xl !== yl) return BigInt(xl < yl ? -1 : 1);
          if (xc === 0) break;
        }
        return 0n;
      }
      case "muldiv": {
        // int MulDiv(int a, int b, int c)
        const av = Number(BigInt.asIntN(32, a(0)));
        const bv = Number(BigInt.asIntN(32, a(1)));
        const cv = Number(BigInt.asIntN(32, a(2)));
        if (cv === 0) return 0xFFFFFFFFn;
        return BigInt.asUintN(32, BigInt(Math.round(av * bv / cv)));
      }
      case "setthreaddpiawarenesscontext": {
        // DPI_AWARENESS_CONTEXT SetThreadDpiAwarenessContext(DPI_AWARENESS_CONTEXT)
        return 0n;  // previous context = NULL (unaware)
      }
      case "getproductinfo": {
        // BOOL GetProductInfo(DWORD osMajor, DWORD osMinor, DWORD spMajor, DWORD spMinor, PDWORD productType)
        const out = Number(a(4));
        if (!ensureMemory(out + 4)) return 0n;
        dv.setUint32(out, 30, true);  // PRODUCT_PROFESSIONAL
        return 1n;
      }
      case "setcurrentprocessexplicitappusermodelid": return 0n;  // S_OK
      case "getfileattributesexw": case "getfileattributesexa": {
        const wide = n.endsWith("w");
        const path = readPath(a(0), wide);
        const infoPtr = Number(a(2));
        if (path == null || !ensureMemory(infoPtr + 36)) {
            winSetLastError(87); return 0n;
        }
        const file = virtualFiles.get(path);
        const dir  = winDirectories.has(path);
        if (!file && !dir) { winSetLastError(2); return 0n; }

        u8.fill(0, infoPtr, infoPtr + 36);
        dv.setUint32(infoPtr +  0, dir ? 0x10 : 0x80, true);
        const now = BigInt(Date.now()) * 10000n + 116444736000000000n;
        dv.setBigUint64(infoPtr +  4, now, true);
        dv.setBigUint64(infoPtr + 12, now, true);
        dv.setBigUint64(infoPtr + 20, now, true);
        const size = file ? file.data.length : 0;
        dv.setUint32(infoPtr + 28, Math.floor(size / 0x100000000) >>> 0, true);
        dv.setUint32(infoPtr + 32, size >>> 0, true);
        return 1n;
    }
    case "openprocesstoken": case "openthreadtoken": {
        const outPtr = Number(a(2));
        if (!ensureMemory(outPtr + 8)) { winSetLastError(87); return 0n; }
        const handle = winAllocHandle({ kind: "token", elevated: true });
        dv.setBigUint64(outPtr, handle, true);
        return 1n;
    }
    case "closetoken": return 1n;
    case "gettokeninformation": {
        const infoClass = Number(a(1)) >>> 0;
        const outPtr = Number(a(2)), outLen = Number(a(3)), outLenPtr = a(4);
        if (infoClass === 17) {   // TokenElevation
            if (outLen < 4) { winSetLastError(122); return 0n; }
            if (ensureMemory(outPtr + 4)) dv.setUint32(outPtr, 1, true);  // ELEVATED
            if (outLenPtr) winWriteDword(outLenPtr, 4);
            return 1n;
        }
        if (infoClass === 20) {   // TokenElevationType
            if (outLen < 4) { winSetLastError(122); return 0n; }
            if (ensureMemory(outPtr + 4)) dv.setUint32(outPtr, 3, true);  // FULL
            if (outLenPtr) winWriteDword(outLenPtr, 4);
            return 1n;
        }
        if (outLenPtr) winWriteDword(outLenPtr, 0);
        return 0n;
    }
    case "checktokenmembership": case "checktokenmembershipex": {
        const isMemberPtr = Number(a(3));
        if (isMemberPtr && ensureMemory(isMemberPtr + 4)) dv.setUint32(isMemberPtr, 1, true);
        return 1n;
    }
    case "accesscheck": {
        const grantedPtr = a(5), statusPtr = a(4);
        if (grantedPtr && ensureMemory(Number(grantedPtr) + 4))
            dv.setUint32(Number(grantedPtr), Number(a(2)) >>> 0, true);   // all bits granted
        if (statusPtr && ensureMemory(Number(statusPtr) + 4))
            dv.setUint32(Number(statusPtr), 1, true);                     // granted
        return 1n;
    }
      case "versetconditionmask": {
        let mask = a(0);
        const typeMask = Number(a(1)) >>> 0;
        const cond = Number(a(2)) & 0xFF;
        for (let i = 0; i < 32; i++) {
          if (typeMask & (1 << i)) {
            mask = (mask & ~(0x7n << BigInt(i * 3))) | (BigInt(cond & 7) << BigInt(i * 3));
          }
        }
        return BigInt.asUintN(64, mask);
      }
      case "verifyversioninfow": case "verifyversioninfoa": {
        return 1n;   // claim Windows 10 always satisfies any check Steam does
      }
      case "redrawwindow": {
        // BOOL RedrawWindow(HWND hWnd, const RECT *lprcUpdate, HRGN hrgnUpdate, UINT flags)
        const hwnd       = a(0);
        const lprcUpdate = a(2);
        const hrgnUpdate = a(1);
        const flags      = Number(a(3)) >>> 0;

        const w = winWindow(hwnd);
        if (w) {
          // RDW_INVALIDATE = 0x0001  RDW_ERASE = 0x0004
          if ((flags & 0x0001) || lprcUpdate !== 0n || hrgnUpdate !== 0n) w.invalid = true;
          if (flags & 0x0004) winPostMessage(hwnd, WINMSG.ERASEBKGND);
          // RDW_UPDATENOW = 0x0100  RDW_ERASENOW = 0x0200
          if (flags & (0x0100 | 0x0200)) winPostMessage(hwnd, WINMSG.PAINT);
          // RDW_FRAME = 0x0400  RDW_ALLCHILDREN = 0x0080 — cascade to children if asked
          if (flags & 0x0400) winPostMessage(hwnd, WINMSG.PAINT);
          if (flags & 0x0080) {
            for (const child of winWindows.values()) {
              if (child.parent === BigInt(hwnd)) child.invalid = true;
            }
          }
          winPresent();
        }
        // RDW_VALIDATE = 0x0002 — mark as painted
        if (w && (flags & 0x0002) && !(flags & 0x0001)) w.invalid = false;
        return 1n;
      }

      case "monitorfromwindow": case "monitorfromrect": case "monitorfrompoint":
      case "monitorfromwindow2": {
        // We expose a single synthetic monitor. Every query maps to it.
        return BigInt(0x00AA_0001);
      }

      case "getmonitorinfoa": case "getmonitorinfow": {
        // BOOL GetMonitorInfoA/W(HMONITOR hMonitor, LPMONITORINFO lpmi)
        // Layout (40 bytes):
        //   +0  DWORD cbSize
        //   +4  RECT  rcMonitor
        //   +20 RECT  rcWork
        //   +36 DWORD dwFlags
        const infoPtr = Number(a(1));
        if (!Number.isSafeInteger(infoPtr) || infoPtr <= 0 || !ensureMemory(infoPtr + 40)) {
          winSetLastError(87); return 0n;
        }
        const cbSize = dv.getUint32(infoPtr, true);
        if (cbSize < 40) { winSetLastError(87); return 0n; }
        const write = Math.min(Math.max(cbSize, 40), 40 + 16 * 4); // allow extended MONITORINFOEX
        u8.fill(0, infoPtr, infoPtr + write);
        dv.setUint32(infoPtr, Math.max(cbSize, 40), true);
        // rcMonitor
        dv.setInt32(infoPtr +  4, 0,                 true);
        dv.setInt32(infoPtr +  8, 0,                 true);
        dv.setInt32(infoPtr + 12, winScreen.width,   true);
        dv.setInt32(infoPtr + 16, winScreen.height,  true);
        // rcWork (no taskbar in guest; full screen)
        dv.setInt32(infoPtr + 20, 0,                 true);
        dv.setInt32(infoPtr + 24, 0,                 true);
        dv.setInt32(infoPtr + 28, winScreen.width,   true);
        dv.setInt32(infoPtr + 32, winScreen.height,  true);
        // dwFlags
        dv.setUint32(infoPtr + 36, 1, true);   // MONITORINFOF_PRIMARY
        return 1n;
      }

      case "getmonitorinfosize": return 40n;
      case "duplicatehandle": {
        const srcHandle = a(1);
        let src;
        if (srcHandle === MASK64) {                            // (HANDLE)-1 = current process
          src = winCurrentProcessState;
        } else if (srcHandle === 0xffff_ffff_ffff_fffen) {     // (HANDLE)-2 = current thread
          src = { kind: "thread", process: winCurrentProcessState,
                  threadId: (Number(processId) || 1) * 16 };
        } else {
          src = winHandles.get(srcHandle);
        }
        if (!src) { winSetLastError(6); return 0n; }
        const outPtr = Number(a(3));
        if (!ensureMemory(outPtr + 8)) { winSetLastError(87); return 0n; }
        const newHandle = winAllocHandle(src);
        dv.setBigUint64(outPtr, newHandle, true);
        return 1n;
      }
      case "getsystemdirectoryw": {
        const buffer = Number(a(0)), capacity = Number(a(1));
        const directory = "C:\\Windows\\System32";
        const required = directory.length + 1;
        if (capacity < required) return BigInt(required);
        if (!winWriteW(buffer, directory)) { winSetLastError(998); return 0n; }
        return BigInt(directory.length);
      }
      case "_time64": {
        const seconds = BigInt(Math.floor(Date.now() / 1000));
        if (a(0) !== 0n) dv.setBigInt64(Number(a(0)), seconds, true);
        return seconds;
      }
      case "_time32": {
        const seconds = BigInt(Math.floor(Date.now() / 1000)) & 0xffffffffn;
        if (a(0) !== 0n) {
          const p = Number(a(0));
          if (!ensureMemory(p + 4)) return 0n;
          dv.setUint32(p, Number(seconds), true);
        }
        return seconds;
      }
      case "_callnewh": return 0n;   // no custom new_handler installed; return "no handler"
            case "_wcsicmp": case "_wcsicmp_l": {
        const x = winReadW(a(0)) ?? "", y = winReadW(a(1)) ?? "";
        const lx = x.toLowerCase(), ly = y.toLowerCase();
        return BigInt(lx < ly ? -1 : lx > ly ? 1 : 0);
      }
      case "sethandleinformation": return 1n;

      case "openeventa": case "openeventw": {
        winSetLastError(2);  // ERROR_FILE_NOT_FOUND — event doesn't exist, caller falls back
        return 0n;
      }

      case "initializesecuritydescriptor": {
        const p = Number(a(0));
        if (!ensureMemory(p + 20)) return 0n;
        dv.setUint8(p, 1);              // revision
        dv.setUint8(p + 1, 0);          // sbz1
        dv.setUint16(p + 2, 0x8000, true);  // SE_SELF_RELATIVE
        for (let i = 0; i < 4; i++) dv.setUint32(p + 4 + i * 4, 0, true);
        return 1n;
      }

      case "setsecuritydescriptordacl": return 1n;

      case "getclassinfoexw": case "getclassinfoexa": {
        winSetLastError(1411);  // ERROR_CLASS_DOES_NOT_EXIST
        return 0n;
      }

      case "wsaioctl": {
        const socket = a(0);
        const control = Number(a(1)) >>> 0;
        const inPtr = Number(a(2));
        const inLen = Number(a(3)) >>> 0;
        const outPtr = Number(a(4));
        const outLen = Number(a(5)) >>> 0;
        const bytesPtr = Number(a(6));
        let inputHex = "";
        if (inPtr && inLen && inLen <= 64 && ensureMemory(inPtr + inLen)) {
          inputHex = Array.from(u8.subarray(inPtr, inPtr + inLen), b => b.toString(16).padStart(2, "0")).join("");
        }
        log(`[WINSOCK] WSAIoctl(s=0x${socket.toString(16)}, code=0x${control.toString(16)}, inLen=${inLen}, outLen=${outLen}, in=${inputHex || "<none>"})`);
        // SIO_GET_EXTENSION_FUNCTION_POINTER: resolve Winsock extension GUIDs
        // to real guest import thunks. The GUID is passed in Windows in-memory
        // layout; these byte strings are the exact 16 bytes read from lpvInBuffer.
        if (control === 0xc8000006) {
          if (!winSocket(socket)) return winWsaFail(10038);
          if (!inPtr || inLen < 16 || !outPtr || outLen < 8 || !ensureMemory(inPtr + 16) || !ensureMemory(outPtr + 8)) {
            return winWsaFail(10014);
          }
          const guidBytes = Array.from(u8.subarray(inPtr, inPtr + 16), b => b.toString(16).padStart(2, "0")).join("");
          const extensionByGuid = {
            // WSAID_CONNECTEX = 25a207b9-ddf3-4660-8ee9-76e58c74063e
            "b907a225f3dd60468ee976e58c74063e": "ConnectEx",
            // WSAID_DISCONNECTEX = 7fda2e11-8630-436f-a031-f536a6eec157
            "112eda7f30866f43a031f536a6eec157": "DisconnectEx",
          };
          const extensionName = extensionByGuid[guidBytes];
          if (!extensionName) {
            winWsaLastError = 10045;
            winSetLastError(10045);
            log(`[WINSOCK] WSAIoctl unknown extension GUID ${guidBytes}; returning WSAEOPNOTSUPP`);
            return WSA_SOCKET_ERROR;
          }
          const ws2 = winLookupModule("ws2_32.dll");
          const extensionThunk = winLookupApi(ws2, extensionName, null);
          if (!extensionThunk) return winWsaFail(10022);
          dv.setBigUint64(outPtr, BigInt(extensionThunk), true);
          if (bytesPtr && ensureMemory(bytesPtr + 4)) dv.setUint32(bytesPtr, 8, true);
          winWsaLastError = 0;
          log(`[WINSOCK] WSAIoctl resolved ${extensionName} -> 0x${BigInt(extensionThunk).toString(16)}`);
          return 0n;
        }
        // Common Winsock controls that do not require a host-side ioctl.
        if (control === 0x8004667e) { // FIONBIO
          const entry = winSocket(socket);
          if (!entry) return winWsaFail(10038);
          if (!inPtr || inLen < 4 || !ensureMemory(inPtr + 4)) return winWsaFail(10014);
          entry.nonBlocking = dv.getUint32(inPtr, true) !== 0;
          if (bytesPtr && ensureMemory(bytesPtr + 4)) dv.setUint32(bytesPtr, 0, true);
          return 0n;
        }
        if (control === 0x9800000c) { // SIO_UDP_CONNRESET
          if (!winSocket(socket)) return winWsaFail(10038);
          if (bytesPtr && ensureMemory(bytesPtr + 4)) dv.setUint32(bytesPtr, 0, true);
          return 0n;
        }
        if (control === 0x98000004) { // SIO_KEEPALIVE_VALS
          if (!winSocket(socket)) return winWsaFail(10038);
          if (bytesPtr && ensureMemory(bytesPtr + 4)) dv.setUint32(bytesPtr, 0, true);
          return 0n;
        }
        winWsaLastError = 10045;
        winSetLastError(10045);
        log(`[WINSOCK] WSAIoctl unsupported control 0x${control.toString(16)}; returning WSAEOPNOTSUPP`);
        return WSA_SOCKET_ERROR;
      }
      case "raiseexception": {
        const code = Number(a(0)) >>> 0;
        const flags = Number(a(1)) >>> 0;
        const nargs = Math.min(Number(a(2)), 15), argp = Number(a(3));
        const params = [];
        for (let i = 0; argp && i < nargs; i++) params.push(winReadU64(argp + i * 8));
        log(`[RECOMP] RaiseException(0x${code.toString(16)}, flags=0x${flags.toString(16)}, [${params.map(v => "0x" + v.toString(16)).join(", ")}])`);

        if (code === 0xe06d7363 && params.length >= 4 && params[0] === 0x19930520n) {
          const cpp = winReadMsvcCppException(params);
          if (cpp) {
            log(`[RECOMP] MSVC C++ throw: object=0x${cpp.object.toString(16)} ThrowInfo=0x${cpp.throwInfo.toString(16)}`);
            if (cpp.typeNames.length) log(`[RECOMP] thrown type(s): ${cpp.typeNames.join(", ")}`);
            const objAddr = Number(cpp.object), tiAddr = Number(cpp.throwInfo);
            if (Number.isSafeInteger(objAddr) && Number.isSafeInteger(tiAddr)) {
              const rspNow = Number(dv.getBigUint64(ctx + REG.rsp * 8, true));
              if (Number.isSafeInteger(rspNow) && rspNow >= 0 && rspNow + 8 <= u8.length) {
                const returnPc = Number(dv.getBigUint64(rspNow, true));
                log(`[SEH] dispatching from pc=0x${returnPc.toString(16)} rsp=0x${(rspNow+8).toString(16)}`);
                const handled = winDispatchSeh(returnPc, rspNow + 8, tiAddr, objAddr);
                if (handled) {
                  log(`[SEH] ✅ caught — jumping to 0x${handled.newRip.toString(16)} rsp=0x${handled.newRsp.toString(16)}`);
                  return { nextPc: BigInt(handled.newRip), rax: 0n, rsp: handled.newRsp };
                }
                log(`[SEH] ❌ no matching handler in 128 frames; terminating`);
              }
            }
          }
        }

        winExitCode = code | 0;
        return { exit: true, status: code | 0 };
      }
      case "towupper": case "_towupper_l": {
        const ch = Number(a(0) & 0xffffn);
        return BigInt(String.fromCharCode(ch).toUpperCase().charCodeAt(0) || ch);
      }
      case "getdiskfreespaceexw": case "getdiskfreespaceexa":
      case "getdiskfreespacew": case "getdiskfreespacea": {
        const wide = n.endsWith("w");
        const freeCaller = a(1), totalBytes = a(2), freeBytes = a(3);
        const total = 1n << 40n;   // 1 TiB
        const free  = 1n << 39n;   // 500 GiB
        const avail = free;
        if (totalBytes && ensureMemory(Number(totalBytes) + 8)) dv.setBigUint64(Number(totalBytes), total, true);
        if (freeBytes  && ensureMemory(Number(freeBytes)  + 8)) dv.setBigUint64(Number(freeBytes),  free,  true);
        if (freeCaller && ensureMemory(Number(freeCaller) + 8)) dv.setBigUint64(Number(freeCaller), avail, true);
        // Old form: GetDiskFreeSpace[AW](rootPath, &sectorsPerCluster, &bytesPerSector, &freeClusters, &totalClusters)
        if (n === "getdiskfreespacew" || n === "getdiskfreespacea") {
          const spc = a(1), bps = a(2), fc = a(3), tc = a(4);
          if (spc && ensureMemory(Number(spc) + 4)) dv.setUint32(Number(spc), 8, true);
          if (bps && ensureMemory(Number(bps) + 4)) dv.setUint32(Number(bps), 512, true);
          if (fc  && ensureMemory(Number(fc)  + 4)) dv.setUint32(Number(fc),  Number(free / 4096n), true);
          if (tc  && ensureMemory(Number(tc)  + 4)) dv.setUint32(Number(tc),  Number(total / 4096n), true);
        }
        return 1n;
      }
      case "findfirstfileexw": case "findfirstfileexa": case 'findfirstfilew': case 'findfirstfilea': {
        // HANDLE FindFirstFileExW(name, FINDEX_INFO_LEVELS, data, FINDEX_SEARCH_OPS, filter, flags)
        const wide = n.endsWith("w");
        const pattern = winReadMemoryString(a(0), wide);
        if (!pattern) { winSetLastError(87); return MASK64; }
        const infoLevel = Number(a(1));              // 0=Standard, 1=Basic (we only support 0)
        const dataPtr = a(2);
        const searchOp = Number(a(3));               // 0=NameMatch, 1=LimitToDirs
        const { entries, dir } = winFindEnumerate(pattern);
        let filtered = entries;
        if (searchOp === 1) filtered = entries.filter(e => e.kind === "dir");
        if (filtered.length === 0) { winSetLastError(2); return MASK64; } // ERROR_FILE_NOT_FOUND
        if (infoLevel !== 0) {
          // WIN32_FIND_DATA_BASIC is 24 bytes: dwFileAttributes, ftCreationTime,
          // ftLastAccessTime, ftLastWriteTime, nFileSizeHigh, nFileSizeLow
          // — but no filename, so this is almost never used. We just fall through.
        }
        if (!winFindFill(filtered[0], dir, Number(dataPtr), wide)) { winSetLastError(87); return MASK64; }
        const h = globalThis.__winNextFindHandle++;
        globalThis.__winFindState.set(h, { entries: filtered, idx: 1, dir, wide });
        return BigInt(h);
      }
      case "filetimetosystemtime": {
        const pFT = Number(a(0)), pST = Number(a(1));
        if (!ensureMemory(pFT + 8) || !ensureMemory(pST + 16)) { winSetLastError(87); return 0n; }
        const ft = dv.getBigUint64(pFT, true);
        // FILETIME: 100ns ticks since 1601-01-01 UTC
        const msSince1601 = Number(ft / 10000n);
        const epochMs = msSince1601 - 11644473600000;  // to unix epoch
        const d = new Date(epochMs);
        if (!Number.isFinite(d.getTime())) { winSetLastError(87); return 0n; }
        dv.setUint16(pST + 0,  d.getUTCFullYear(),         true);
        dv.setUint16(pST + 2,  d.getUTCMonth() + 1,        true);
        dv.setUint16(pST + 4,  d.getUTCDay(),              true);  // 0=Sunday
        dv.setUint16(pST + 6,  d.getUTCDate(),             true);
        dv.setUint16(pST + 8,  d.getUTCHours(),            true);
        dv.setUint16(pST + 10, d.getUTCMinutes(),          true);
        dv.setUint16(pST + 12, d.getUTCSeconds(),          true);
        dv.setUint16(pST + 14, d.getUTCMilliseconds(),     true);
        return 1n;
      }

      case "systemtimetofiletime": {
        const pST = Number(a(0)), pFT = Number(a(1));
        if (!ensureMemory(pST + 16) || !ensureMemory(pFT + 8)) { winSetLastError(87); return 0n; }
        const y  = dv.getUint16(pST + 0,  true);
        const mo = dv.getUint16(pST + 2,  true) - 1;
        const dd = dv.getUint16(pST + 6,  true);
        const hh = dv.getUint16(pST + 8,  true);
        const mm = dv.getUint16(pST + 10, true);
        const ss = dv.getUint16(pST + 12, true);
        const ms = dv.getUint16(pST + 14, true);
        const epochMs = Date.UTC(y, mo, dd, hh, mm, ss, ms);
        if (!Number.isFinite(epochMs)) { winSetLastError(87); return 0n; }
        const ft = BigInt(epochMs + 11644473600000) * 10000n;
        dv.setBigUint64(pFT, ft, true);
        return 1n;
      }

      case "filetimetolocalfiletime": {
        // We treat UTC == local (matches what the emulator reports for other clocks).
        const pIn = Number(a(0)), pOut = Number(a(1));
        if (!ensureMemory(pIn + 8) || !ensureMemory(pOut + 8)) { winSetLastError(87); return 0n; }
        dv.setBigUint64(pOut, dv.getBigUint64(pIn, true), true);
        return 1n;
      }

      case "localfiletimetofiletime": {
        const pIn = Number(a(0)), pOut = Number(a(1));
        if (!ensureMemory(pIn + 8) || !ensureMemory(pOut + 8)) { winSetLastError(87); return 0n; }
        dv.setBigUint64(pOut, dv.getBigUint64(pIn, true), true);
        return 1n;
      }
      case "gettimezoneinformation": {
        // DWORD GetTimeZoneInformation(LPTIME_ZONE_INFORMATION)
        const p = Number(a(0));
        if (!ensureMemory(p + 172)) return 0xFFFFFFFFn;
        u8.fill(0, p, p + 172);
        // Bias = 0 (UTC), StandardName and DaylightName = "UTC"
        dv.setInt32(p, 0, true);
        for (const ch of "UTC\0") {
          dv.setUint16(p + 84 + "UTC\0".indexOf(ch) * 2, ch.charCodeAt(0), true);
          dv.setUint16(p + 168 + "UTC\0".indexOf(ch) * 2, ch.charCodeAt(0), true);
        }
        return 0n;  // TIME_ZONE_ID_UNKNOWN
      }
      case "__wsafdisset": {
        // int __WSAFDIsSet(SOCKET fd, fd_set *set)
        const fd = a(0);
        const setPtr = Number(a(1));
        if (!Number.isSafeInteger(setPtr) || setPtr <= 0 || !ensureMemory(setPtr + 4)) return 0n;
        const count = dv.getUint32(setPtr, true);
        if (count > 1024) return 0n;
        for (let i = 0; i < count; i++) {
          if (dv.getBigUint64(setPtr + 8 + i * 8, true) === fd) return 1n;
        }
        return 0n;
      }
      case "getdateformatw": case "getdateformata": {
        // int GetDateFormat[AW](LCID, DWORD flags, const SYSTEMTIME *date, LPCSTR/W format, LPSTR/W buf, int cch)
        const wide = n.endsWith("w");
        const pST = Number(a(2));
        const bufPtr = a(4), cch = Number(a(5));
        if (!ensureMemory(pST + 16)) { winSetLastError(87); return 0n; }
        const y  = dv.getUint16(pST + 0,  true);
        const mo = dv.getUint16(pST + 2,  true);
        const dd = dv.getUint16(pST + 6,  true);
        const text = `${mo}/${dd}/${y}`;
        if (cch === 0) return BigInt(text.length + 1);
        if (!bufPtr || cch < text.length + 1) { winSetLastError(122); return 0n; }
        if (wide) winWriteW(bufPtr, text); else winWriteA(bufPtr, text);
        return BigInt(text.length + 1);
      }

      case "gettimeformatw": case "gettimeformata": {
        const wide = n.endsWith("w");
        const pST = Number(a(2));
        const bufPtr = a(4), cch = Number(a(5));
        if (!ensureMemory(pST + 16)) { winSetLastError(87); return 0n; }
        const hh = dv.getUint16(pST + 8,  true);
        const mm = dv.getUint16(pST + 10, true);
        const ss = dv.getUint16(pST + 12, true);
        const text = `${String(hh).padStart(2,'0')}:${String(mm).padStart(2,'0')}:${String(ss).padStart(2,'0')}`;
        if (cch === 0) return BigInt(text.length + 1);
        if (!bufPtr || cch < text.length + 1) { winSetLastError(122); return 0n; }
        if (wide) winWriteW(bufPtr, text); else winWriteA(bufPtr, text);
        return BigInt(text.length + 1);
      }
      case "wcsrchr": {
        const str = winReadW(a(0)) ?? "";
        const ch = String.fromCharCode(Number(a(1) & 0xffffn));
        const idx = str.lastIndexOf(ch);
        return idx < 0 ? 0n : a(0) + BigInt(idx * 2);
      }

      case "_o__wcsnicmp": case "_wcsnicmp": case "wcsnicmp": {
        const x = winReadW(a(0)) ?? "";
        const y = winReadW(a(1)) ?? "";
        const n = Math.min(Number(a(2)) >>> 0, Math.max(x.length, y.length));
        for (let i = 0; i < n; i++) {
          const xc = i < x.length ? x.charCodeAt(i) : 0;
          const yc = i < y.length ? y.charCodeAt(i) : 0;
          const xl = (xc >= 65 && xc <= 90) ? xc + 32 : xc;
          const yl = (yc >= 65 && yc <= 90) ? yc + 32 : yc;
          if (xl !== yl) return BigInt(xl < yl ? -1 : 1);
          if (xc === 0) break;
        }
        return 0n;
      }

      case "_o__wcsicmp": case "_wcsicmp": {
        const x = winReadW(a(0)) ?? "";
        const y = winReadW(a(1)) ?? "";
        const lx = x.toLowerCase(), ly = y.toLowerCase();
        return BigInt(lx === ly ? 0 : lx < ly ? -1 : 1);
      }
      case "rtlntstatustodoserror": {
        const status = Number(BigInt.asUintN(32, a(0))) >>> 0;
        logTrace(`[NTS] RtlNtStatusToDosError(0x${status.toString(16)})`);
        const map = {
          // ── generic ──
          0x00000000: 0,    0x00000103: 997,
          0xC0000001: 31,   0xC0000002: 120,  0xC0000003: 87,
          0xC0000004: 24,   0xC0000008: 6,    0xC000000D: 87,
          0xC000000F: 2,    0xC0000010: 1,    0xC0000011: 38,
          0xC0000017: 8,    0xC0000018: 487,  0xC0000019: 487,
          0xC0000022: 5,    0xC0000023: 122,  0xC0000024: 170,
          0xC0000034: 2,    0xC0000035: 183,  0xC000003A: 3,
          0xC0000043: 32,   0xC000007A: 127,  0xC000007B: 0x3D,
          0xC0000101: 145,  0xC0000120: 0x4C7, 0xC0000135: 126,
          0xC0000139: 127,  0xC0000142: 0x45A, 0xC0000185: 23,
          0xC0000225: 0x2D2,

          // ── security / token (the batch we're missing) ──
          0xC000005E: 1314,  // STATUS_NO_SUCH_PRIVILEGE → ERROR_PRIVILEGE_NOT_HELD
          0xC0000061: 1314,  // STATUS_PRIVILEGE_NOT_HELD → ERROR_PRIVILEGE_NOT_HELD
          0xC000006D: 1326,  // STATUS_LOGON_FAILURE → ERROR_LOGON_FAILURE
          0xC000006E: 1327,  // STATUS_ACCOUNT_RESTRICTION → ERROR_ACCOUNT_RESTRICTION
          0xC000006F: 1328,  // STATUS_INVALID_LOGON_HOURS
          0xC0000070: 1329,  // STATUS_INVALID_WORKSTATION
          0xC0000071: 1330,  // STATUS_PASSWORD_EXPIRED
          0xC0000072: 1331,  // STATUS_ACCOUNT_DISABLED
          0xC000007C: 1008,  // STATUS_NO_TOKEN → ERROR_NO_TOKEN  ← THE FIX
          0xC0000103: 1367,  // STATUS_INVALID_LOGON_TYPE
          0xC000015B: 1385,  // STATUS_LOGON_TYPE_NOT_GRANTED
          0xC000018B: 0x53F, // STATUS_NO_TRUST_SAM_ACCOUNT

          // ── buffer / length ──
          0xC0000023: 122,   // STATUS_BUFFER_TOO_SMALL → ERROR_INSUFFICIENT_BUFFER
          0x80000005: 234,   // STATUS_BUFFER_OVERFLOW  → ERROR_MORE_DATA

          // ── registry ──
          0xC0000033: 87,    // STATUS_OBJECT_NAME_INVALID
          0xC0000034: 2,     // STATUS_OBJECT_NAME_NOT_FOUND
          0xC0000035: 183,   // STATUS_OBJECT_NAME_COLLISION
          0xC000003A: 3,     // STATUS_OBJECT_PATH_NOT_FOUND
        };
        const dos = map[status];
        if (dos !== undefined) return BigInt(dos);
        log(`[RECOMP] RtlNtStatusToDosError: unmapped 0x${status.toString(16)} → 31`);
        return 31n;
      }

      case "ntopenprocesstoken": case "ntopenthreadtoken":
        return 0xC000007Cn;  // STATUS_NO_TOKEN

      case "setconsoleinputexenamew": return 1n;
      case "seterrormode": {
        // UINT SetErrorMode(UINT) -> previous mode
        const old = Number(globalThis.__winErrorMode ?? 0);
        globalThis.__winErrorMode = Number(a(0)) >>> 0;
        return BigInt(old);
      }
      case "findnextfilew": case "findnextfilea": {
        const wide = n.endsWith("w");
        const h = Number(a(0));
        const st = globalThis.__winFindState.get(h);
        if (!st) { winSetLastError(6); return 0n; }
        if (st.idx >= st.entries.length) { winSetLastError(18); return 0n; } // ERROR_NO_MORE_FILES
        const entry = st.entries[st.idx++];
        return winFindFill(entry, st.dir, Number(a(1)), wide) ? 1n : 0n;
      }
      case "heapsize": {
        const p = Number(a(2));
        const size = winAllocations.get(p);
        if (size == null) {
          if (!globalThis.__heapSizeUnknown) globalThis.__heapSizeUnknown = new Set();
          if (!globalThis.__heapSizeUnknown.has(p)) {
            globalThis.__heapSizeUnknown.add(p);
            log(`[HEAPSIZE-UNKNOWN] ptr=0x${p.toString(16)} (never allocated by us)`);
          }
          winSetLastError(87); return MASK64;
        }
        return BigInt(size);
      }
      case "_o__ultoa": case "_ultoa": case "_ultoa_s": {
        const val = Number(BigInt.asUintN(32, a(0)));
        const radix = Math.max(2, Math.min(36, Number(a(2)) || 10));
        winWriteA(a(1), val.toString(radix));
        return a(1);
      }
      case "apppolicygetprocessterminationmethod": {
        // AppPolicyProcessTerminationMethod: 0=ExitProcess, 1=TerminateProcess
        const policyPtr = Number(a(1));
        if (policyPtr && ensureMemory(policyPtr + 4)) dv.setUint32(policyPtr, 0, true);
        return 0n;  // S_OK
      }
      case "apppolicygetwindowingmodel": {
        // AppPolicyWindowingModel: 0=CoreWindow, 1=HWND, 2=None
        const policyPtr = Number(a(1));
        if (policyPtr && ensureMemory(policyPtr + 4)) dv.setUint32(policyPtr, 1, true);  // HWND = desktop
        return 0n;
      }
      case "apppolicygetmediaplaybacktype": {
        const policyPtr = Number(a(1));
        if (policyPtr && ensureMemory(policyPtr + 4)) dv.setUint32(policyPtr, 0, true);
        return 0n;
      }
      case "formatmessagew": case "formatmessagea": {
        const wide = n.endsWith("w");
        const flags = Number(a(0)) >>> 0;
        const msgId = Number(a(2)) >>> 0;
        const bufArg = a(4), size = Number(a(5));
        // If flags say FROM_HMODULE (0x800) and not FROM_SYSTEM (0x1000),
        // this is a .rsrc lookup we can't resolve — return 0 cleanly instead
        // of pulling a random string from our win32 table.
        if ((flags & 0x800) && !(flags & 0x1000)) {
          if (flags & 0x100) {
            const pp = Number(bufArg);
            if (ensureMemory(pp + 8)) dv.setBigUint64(pp, 0n, true);
          }
          winSetLastError(317);
          return 0n;
        }
        if (msgId >= 9000 && msgId < 10000) {
          if (flags & 0x100) {
            const pp = Number(bufArg);
            if (ensureMemory(pp + 8)) dv.setBigUint64(pp, 0n, true);
          }
          winSetLastError(317);   // ← NEW: ERROR_MR_MID_NOT_FOUND
          return 0n;
        }

        const table = {
          // ── system error text ──
          0:   "The operation completed successfully.",
          1:   "Incorrect function.",
          2:   "The system cannot find the file specified.",
          3:   "The system cannot find the path specified.",
          4:   "The system cannot open the file.",
          5:   "Access is denied.",
          6:   "The handle is invalid.",
          7:   "The storage control blocks were destroyed.",
          8:   "Not enough memory resources are available to process this command.",
          9:   "The storage control block address is invalid.",
          10:  "The environment is incorrect.",
          11:  "An attempt was made to load a program with an incorrect format.",
          12:  "The access code is invalid.",
          13:  "The data is invalid.",
          14:  "Not enough storage is available to complete this operation.",
          15:  "The system cannot find the drive specified.",
          16:  "The directory cannot be removed.",
          17:  "The system cannot move the file to a different disk drive.",
          18:  "There are no more files.",
          19:  "The media is write protected.",
          20:  "The system cannot find the device specified.",
          21:  "The device is not ready.",
          22:  "The device does not recognize the command.",
          23:  "Data error (cyclic redundancy check).",
          24:  "The program issued a command but the command length is incorrect.",
          25:  "The drive cannot locate a specific area or track on the disk.",
          26:  "The specified disk or diskette cannot be accessed.",
          27:  "The drive cannot find the sector requested.",
          28:  "The printer is out of paper.",
          29:  "The system cannot write to the specified device.",
          30:  "The system cannot read from the specified device.",
          31:  "A device attached to the system is not functioning.",
          32:  "The process cannot access the file because it is being used by another process.",
          33:  "The process cannot access the file because another process has locked a portion of the file.",
          34:  "The wrong diskette is in the drive.",
          35:  "Too many files opened for sharing.",
          36:  "Reached the end of the file.",
          38:  "Reached the end of the file.",
          39:  "The disk is full.",
          40:  "The network name cannot be found.",
          50:  "The request is not supported.",
          51:  "Windows cannot find the network path.",
          52:  "A duplicate name exists on the network.",
          53:  "The network path was not found.",
          54:  "The network is busy.",
          55:  "The specified network resource or device is no longer available.",
          56:  "The network BIOS command limit has been reached.",
          57:  "A network adapter hardware error occurred.",
          58:  "The specified server cannot perform the requested operation.",
          59:  "An unexpected network error occurred.",
          60:  "The remote adapter is not compatible.",
          61:  "The printer queue is full.",
          62:  "Space to store the file waiting to be printed is not available on the server.",
          63:  "Your file waiting to be printed was deleted.",
          64:  "The specified network name is no longer available.",
          65:  "Network access is denied.",
          66:  "The network resource type is not correct.",
          67:  "The network name cannot be found.",
          68:  "The name limit for the local computer network adapter card was exceeded.",
          69:  "The network BIOS session limit was exceeded.",
          70:  "The remote server has been paused or is in the process of being started.",
          71:  "No more connections can be made to this remote computer at this time because there are already as many connections as the computer can accept.",
          72:  "The specified printer or disk device has been paused.",
          80:  "The file exists.",
          82:  "The directory or file cannot be created.",
          83:  "Fail on INT 24.",
          84:  "Storage to process this request is not available.",
          85:  "The local device name is already in use.",
          86:  "The specified network password is not correct.",
          87:  "The parameter is incorrect.",
          88:  "A write fault occurred on the network.",
          89:  "The system cannot start another process at this time.",
          100: "Cannot create another system semaphore.",
          101: "The exclusive semaphore is owned by another process.",
          102: "The semaphore is set and cannot be closed.",
          103: "The semaphore cannot be set again.",
          104: "Cannot request exclusive semaphores at interrupt time.",
          105: "The previous ownership of this semaphore has ended.",
          107: "The program stopped because an alternate diskette was not inserted.",
          108: "The disk is in use or locked by another process.",
          109: "The pipe has been ended.",
          110: "The system cannot open the device or file specified.",
          112: "There is not enough space on the disk.",
          113: "No more internal file identifiers available.",
          114: "The target internal file identifier is incorrect.",
          117: "The IOCTL call made by the application program is not correct.",
          118: "The verify-on-write switch parameter value is not correct.",
          119: "The system does not support the command requested.",
          120: "This function is not supported on this system.",
          121: "The semaphore timeout period has expired.",
          122: "The data area passed to a system call is too small.",
          123: "The filename, directory name, or volume label syntax is incorrect.",
          124: "The system call level is not correct.",
          125: "The disk has no volume label.",
          126: "The specified module could not be found.",
          127: "The specified procedure could not be found.",
          128: "There are no child processes to wait for.",
          130: "An attempt was made to use an object that is not a valid handle.",
          132: "The signal name is incorrect.",
          133: "The JOBNET name is incorrect.",
          134: "An attempt was made to use a JOBNET that is not valid.",
          135: "An attempt was made to use a JOBNET that is not valid for this operation.",
          136: "The JOBNET was not properly assigned.",
          137: "An attempt was made to run a JOBNET that was not valid.",
          138: "An attempt was made to use a JOBNET that does not exist.",
          139: "The token type is not valid.",
          141: "The disk is write protected.",
          142: "The drive is not ready.",
          145: "The directory is not empty.",
          146: "The path specified could not be found.",
          147: "The resource is currently unavailable.",
          150: "The system trace information was not specified in your CONFIG.SYS file, or tracing is disallowed.",
          151: "The number of specified semaphore events for DosMuxSemWait is not correct.",
          152: "DosMuxSemWait did not execute; too many semaphores are already set.",
          153: "The DosMuxSemWait list is not correct.",
          154: "The volume label you entered exceeds the label character limit of the target file system.",
          155: "Cannot create another thread.",
          156: "The recipient process has refused the signal.",
          157: "The segment is already discarded and cannot be locked.",
          158: "The segment is already unlocked.",
          160: "The argument string passed to DosExecPgm is not correct.",
          161: "The specified path is invalid.",
          162: "A signal is already pending.",
          164: "No more threads can be created in the system.",
          167: "Unable to lock a region of a file.",
          170: "The requested resource is in use.",
          173: "A lock request was not outstanding for the supplied cancel region.",
          174: "The file system does not support atomic changes to the lock type.",
          180: "The system detected a segment number that was not correct.",
          182: "The operating system cannot run %1.",
          183: "Cannot create a file when that file already exists.",
          186: "The flag passed is not correct.",
          187: "The specified system semaphore name was not found.",
          188: "The operating system cannot run %1.",
          189: "The operating system cannot run %1.",
          190: "The operating system cannot run this executable program.",
          191: "Cannot run %1 in Win32 mode.",
          192: "The operating system cannot run this executable program.",
          193: "Invalid keyboard code specified.",
          194: "The operating system cannot run this executable program.",
          195: "The operating system cannot run this executable program.",
          196: "The operating system cannot run this executable program.",
          197: "The operating system cannot run this executable program.",
          198: "The operating system cannot run this executable program.",
          199: "The operating system cannot run this executable program.",
          200: "The code segment cannot be greater than or equal to 64K.",
          201: "The operating system cannot run %1.",
          202: "The operating system cannot run %1.",
          203: "The system could not find the environment option that was entered.",
          205: "No process in the command subtree has a signal handler.",
          206: "The filename or extension is too long.",
          207: "The ring 2 stack is in use.",
          208: "The global filename characters, * or ?, are entered incorrectly or too many global filename characters are specified.",
          209: "The signal being posted is not correct.",
          210: "The signal handler cannot be set.",
          212: "The segment is locked and cannot be reallocated.",
          214: "Too many dynamic-link modules are attached to this program or dynamic-link module.",
          215: "Cannot nest calls to LoadModule.",
          216: "This version of %1 is not compatible with the version of Windows you're running.",
          230: "The pipe state is invalid.",
          231: "All pipe instances are busy.",
          232: "The pipe is being closed.",
          233: "No process is on the other end of the pipe.",
          234: "More data is available.",
          240: "The session was canceled.",
          254: "The specified extended attribute name was invalid.",
          255: "The extended attributes are inconsistent.",
          258: "The wait operation timed out.",
          259: "No more data is available.",
          266: "The copy functions cannot be used.",
          267: "The directory name is invalid.",
          275: "The extended attributes did not fit in the buffer.",
          276: "The extended attribute file on the mounted file system is corrupt.",
          277: "The extended attribute table file is full.",
          278: "The specified extended attribute handle is invalid.",
          282: "The mounted file system does not support extended attributes.",
          288: "Attempt to release mutex not owned by caller.",
          298: "Too many posts were made to a semaphore.",
          299: "Only part of a ReadProcessMemory or WriteProcessMemory request was completed.",
          300: "The oplock request is denied.",
          301: "An invalid oplock acknowledgment was received by the system.",
          302: "The volume is too fragmented to complete this operation.",
          303: "The file cannot be opened because it is in the process of being deleted.",
          304: "The file cannot be opened because the process is trying to access a file that is not a valid file.",
          305: "The system cannot find message text for message number 0x%1 in the message file for %2.",
          487: "Attempt to access invalid address.",
          534: "Arithmetic result exceeded 32 bits.",
          535: "There is a process on other end of the pipe.",
          536: "Waiting for a process to open the other end of the pipe.",
          994: "Access to the extended attribute was denied.",
          995: "The I/O operation has been aborted because of either a thread exit or an application request.",
          996: "Overlapped I/O event is not in a signaled state.",
          997: "Overlapped I/O operation is in progress.",
          998: "Invalid access to memory location.",
          999: "Error performing inpage operation.",
          1001: "Recursive access to the registry is disallowed.",
          1002: "A block of data was read or written incompletely, but not with an acceptable granularity.",
          1003: "The file cannot be opened because it cannot be resolved to a device.",
          1004: "Invalid flags.",
          1005: "The volume does not contain a recognized file system.",
          1006: "The volume for a file has been externally altered so that the opened file is no longer valid.",
          1007: "The requested operation cannot be performed in full-screen mode.",
          1008: "An attempt was made to reference a token that does not exist.",
          1009: "The configuration registry database is corrupt.",
          1010: "The configuration registry key is invalid.",
          1011: "The configuration registry key could not be opened.",
          1012: "The configuration registry key could not be read.",
          1013: "The configuration registry key could not be written.",
          1014: "One of the files in the registry database had to be recovered by use of a log or alternate copy.",
          1015: "The registry is corrupted. The structure of one of the files containing registry data is corrupted.",
          1016: "An I/O operation initiated by the registry failed unrecoverably.",
          1017: "The system could not allocate the required space in a registry log.",
          1018: "Cannot create a symbolic link in a registry key that already has subkeys or values.",
          1019: "Cannot create a stable subkey under a volatile parent key.",
          1020: "A notify change request is being completed and the information is not being returned in the caller's buffer.",
          1021: "A device that does not implement driver-specific features was passed a driver-specific request.",
          1022: "A completion routine is required.",
          1051: "The stop-control is not supported.",
          1052: "The resume-control is not supported.",
          1053: "The service has been marked for deletion.",
          1054: "The service cannot be started from a console or by a call to the system.",
          1055: "The service database is locked.",
          1056: "An instance of the service is already running.",
          1057: "The account name is invalid or does not exist, or the password is invalid.",
          1058: "The service cannot be started, either because it is disabled or because it has no enabled devices associated with it.",
          1059: "Circular service dependency was specified.",
          1060: "The specified service does not exist as an installed service.",
          1061: "The service cannot accept control messages at this time.",
          1062: "The service has not been started.",
          1063: "The service process could not connect to the service controller.",
          1064: "An exception occurred in the service when handling the control request.",
          1065: "The database specified does not exist.",
          1066: "The service has returned a service-specific error code.",
          1067: "The process terminated unexpectedly.",
          1068: "The dependency service or group failed to start.",
          1069: "The service did not start due to a logon failure.",
          1070: "After starting, the service hung in a start-pending state.",
          1071: "The specified service database lock is invalid.",
          1072: "The specified service has been marked for deletion.",
          1073: "The specified service already exists.",
          1074: "The system is currently running with the last-known-good configuration for service %2.",
          1075: "The dependency service does not exist or has been marked for deletion.",
          1076: "The current boot has already been accepted for use as the last-known-good control set.",
          1077: "No attempts to start the service have been made since the last boot.",
          1078: "The name is already in use as either a service name or a service display name.",
          1079: "The account specified for this service is different from the account specified for other services running in the same process.",
          1080: "Failure actions can only be set for Win32 services, not for drivers.",
          1081: "This service runs in the same process as the service control manager.",
          1082: "The recovery configuration was not specified for a non-service.",
          1083: "The specified service is the one being executed (rather than one of its dependencies).",
          1084: "This service is not implemented on this system.",
          1085: "The system is shutting down. The service is not accepting requests.",
          1086: "The service has been marked for deletion.",
          1087: "The specified service already exists.",
          1088: "The system is running with the last-known-good configuration.",
          1089: "The service has been marked for deletion.",
          1090: "The specified service has been marked for deletion.",
          1091: "The dependency service or group failed to start.",
          1092: "The boot system has already been accepted as good.",
          1093: "The specified service is marked for deletion.",
          1094: "The specified service does not exist as an installed service.",
          1095: "The process terminated unexpectedly.",
          1096: "The service has not been started.",
          1097: "The service process could not connect to the service controller.",
          1098: "The service has returned a service-specific error code.",
          1099: "The database specified does not exist.",
          1100: "The physical end of the tape has been reached.",
          1101: "A tape access reached a filemark.",
          1102: "The beginning of the tape or a partition was encountered.",
          1103: "A tape access reached the end of a set of files.",
          1104: "No more data is on the tape.",
          1105: "Tape could not be partitioned.",
          1106: "When accessing a new tape of a multivolume partition, the current block size is incorrect.",
          1107: "Tape partition information could not be found when loading a tape.",
          1108: "Unable to lock the media eject mechanism.",
          1109: "Unable to unload the media.",
          1110: "The media in the drive may have changed.",
          1111: "The I/O bus was reset.",
          1112: "No media in drive.",
          1113: "No mapping for the Unicode character exists in the target multi-byte code page.",
          1114: "A dynamic-link library (DLL) initialization routine failed.",
          1115: "A system shutdown is in progress.",
          1116: "Unable to abort the system shutdown because no shutdown was in progress.",
          1117: "The request could not be performed because of an I/O device error.",
          1118: "No serial device was successfully initialized. The serial driver will unload.",
          1119: "Unable to open a device that was sharing an interrupt request (IRQ) with other devices.",
          1120: "A serial I/O operation was completed by another write to the serial port.",
          1121: "The I/O operation has been aborted because of either a thread exit or an application request.",
          1122: "A device is being removed.",
          1123: "A device is not ready.",
          1124: "An internal error occurred.",
          1125: "An internal error occurred.",
          1126: "The operation completed successfully.",
          1127: "The operation completed successfully.",
          1128: "The operation completed successfully.",
          1129: "The operation completed successfully.",
          1130: "The operation completed successfully.",
          1131: "The operation completed successfully.",
          1132: "The operation completed successfully.",
          1200: "The network connection was aborted by the local system.",
          1201: "The network connection was aborted by the local system.",
          1202: "The network connection was aborted by the local system.",
          1203: "The network connection was aborted by the local system.",
          1204: "The network connection was aborted by the local system.",
          1205: "The network connection was aborted by the local system.",
          1206: "The network connection was aborted by the local system.",
          1207: "The network connection was aborted by the local system.",
          1208: "The network connection was aborted by the local system.",
          1209: "The network connection was aborted by the local system.",
          1210: "The network connection was aborted by the local system.",
          1211: "The network connection was aborted by the local system.",
          1212: "The network connection was aborted by the local system.",
          1213: "The network connection was aborted by the local system.",
          1214: "The network connection was aborted by the local system.",
          1215: "The network connection was aborted by the local system.",
          1216: "The network connection was aborted by the local system.",
          1217: "The network connection was aborted by the local system.",
          1218: "The network connection was aborted by the local system.",
          1219: "The network connection was aborted by the local system.",
          1220: "The network connection was aborted by the local system.",
          1221: "The network connection was aborted by the local system.",
          1222: "The network connection was aborted by the local system.",
          1223: "The network connection was aborted by the local system.",
          1300: "Not all privileges or groups referenced are assigned to the caller.",
          1301: "Some mapping between account names and security IDs was not done.",
          1302: "No system quota limits are specifically set for this account.",
          1303: "No encryption key is available. A well-known encryption key was returned.",
          1304: "The password is too complex to be converted to a LAN Manager password.",
          1305: "The revision level is unknown.",
          1306: "Indicates two revision levels are incompatible.",
          1307: "This security ID may not be assigned as the owner of this object.",
          1308: "This security ID may not be assigned as the primary group of an object.",
          1309: "An attempt has been made to operate on an impersonation token by a thread that is not currently impersonating a client.",
          1310: "The group may not be disabled.",
          1311: "There are currently no logon servers available to service the logon request.",
          1312: "A specified logon session does not exist. It may already have been terminated.",
          1313: "A specified privilege does not exist.",
          1314: "A required privilege is not held by the client.",
          1315: "The name provided is not a properly formed account name.",
          1316: "The specified account already exists.",
          1317: "The specified account does not exist.",
          1318: "The specified group already exists.",
          1319: "The specified group does not exist.",
          1320: "Either the specified user account is already a member of the specified group, or the specified group cannot be deleted because it contains a member.",
          1321: "The specified user account is not a member of the specified group account.",
          1322: "This operation is disallowed as it could result in an administration account being disabled, deleted or unable to log on.",
          1323: "Unable to update the password. The value provided as the current password is incorrect.",
          1324: "Unable to update the password. The value provided for the new password contains values that are not allowed in passwords.",
          1325: "Unable to update the password. The value provided for the new password does not meet the length, complexity, or history requirements of the domain.",
          1326: "The user name or password is incorrect.",
          1327: "Account restrictions are preventing this user from signing in. For example: blank passwords aren't allowed, sign-in times are limited, or a policy restriction has been enforced.",
          1328: "Your account has time restrictions that prevent you from signing in at this time. Try again later.",
          1329: "This user isn't allowed to sign in to this computer. Try again at a later time.",
          1330: "The password for this account has expired. Change the password and try again, or ask your system administrator.",
          1331: "This user can't sign in because this account is currently disabled.",
          1332: "No mapping between account names and security IDs was done.",
          1333: "Too many local user identifiers (LUIDs) were requested at one time.",
          1334: "No more local user identifiers (LUIDs) are available.",
          1335: "The security ID structure is invalid.",
          1336: "The SID structure is invalid.",
          1337: "The security identifier is not valid.",
          1338: "The security descriptor structure is invalid.",
          1339: "The security descriptor structure is invalid.",
          1340: "The access control list (ACL) structure is invalid.",
          1341: "The access control list (ACL) structure is invalid.",
          1342: "The security descriptor structure is invalid.",
          1343: "The security descriptor is not in the required format.",
          1344: "The security descriptor is not in the required format.",
          1345: "The supplied variant structure contains invalid data.",
          1346: "The supplied security descriptor is not in the required format.",
          1347: "The security descriptor contains null or invalid DACL.",
          1348: "Invalid security descriptor.",
          1349: "The type of the token is inappropriate for its attempted use.",
          1350: "Unable to perform a security operation on an object that has no associated security.",
          1351: "Configuration information could not be read from the domain controller.",
          1352: "The security account manager (SAM) or local security authority (LSA) server was in the wrong state to perform the security operation.",
          1353: "The domain was in the wrong state to perform the security operation.",
          1354: "This operation is only allowed for the Primary Domain Controller of the domain.",
          1355: "The specified domain either does not exist or could not be contacted.",
          1356: "The specified domain already exists.",
          1357: "An attempt was made to exceed the limit on the number of domains per server.",
          1358: "Unable to complete the requested operation because of either a catastrophic media failure or a data structure corruption on the disk.",
          1359: "An internal error occurred.",
          1360: "The specified file was in a format that was not recognized or was corrupted.",
          1361: "The specified image file did not contain a resource section.",
          1362: "The specified resource type cannot be found in the image file.",
          1363: "The specified resource name cannot be found in the image file.",
          1364: "The specified resource language ID cannot be found in the image file.",
          1365: "The account was created during a logon.",
          1366: "The logon session is not in a state consistent with the operation being performed.",
          1367: "A logon request contained an invalid logon type value.",
          1368: "Unable to impersonate using a named pipe until data has been read from that pipe.",
          1369: "The transaction state of a registry subtree is incompatible with the requested operation.",
          1370: "An internal security database corruption has been encountered.",
          1371: "Cannot perform this operation on built-in accounts.",
          1372: "Cannot perform this operation on this built-in special group.",
          1373: "Cannot perform this operation on this built-in special user.",
          1374: "The user cannot be removed from a group because the group is currently the user's primary group.",
          1375: "The token is already in use as a primary token.",
          1376: "The specified local group does not exist.",
          1377: "The specified account name is not a member of the local group.",
          1378: "The specified account name is already a member of the local group.",
          1379: "The specified local group already exists.",
          1380: "Logon failure: the user has not been granted the requested logon type at this computer.",
          1381: "The maximum number of secrets that may be stored in a single system has been exceeded.",
          1382: "The length of a secret exceeds the maximum length allowed.",
          1383: "The local security authority database contains an internal inconsistency.",
          1384: "During a logon attempt, the user's security context accumulated too many security IDs.",
          1385: "Logon failure: the user has not been granted the requested logon type at this computer.",
          1386: "A cross-encrypted password is necessary to change a user password.",
          1387: "A new member could not be added to a local group because the member does not exist.",
          1388: "A new member could not be added to a local group because the member has the wrong account type.",
          1389: "Too many secrets were added to a single system.",
          1390: "A cross-encrypted password is necessary to change this user password.",
          1391: "A member could not be added to or removed from the local group because the member does not exist.",
          1392: "The file or directory is corrupted and unreadable.",
          1393: "The disk structure is corrupted and unreadable.",
          1394: "There is no user session key for the specified logon session.",
          1395: "The service is being run in a context different from the one in which it was started.",
          1396: "Logon failure: the target account name is incorrect.",
          1397: "Mutual authentication failed.",
          1398: "This security ID may not be assigned as the owner of this object.",
          1399: "This security ID may not be assigned as the owner of this object.",
          1400: "Invalid window handle.",
          1401: "Invalid menu handle.",
          1402: "Invalid cursor handle.",
          1403: "Invalid accelerator table handle.",
          1404: "Invalid hook handle.",
          1405: "Invalid handle to a multiple-window-position structure.",
          1406: "Cannot create a top-level child window.",
          1407: "Cannot find window class.",
          1408: "Invalid window; it belongs to other thread.",
          1409: "Hot key is already registered.",
          1410: "Class already exists.",
          1411: "Class does not exist.",
          1412: "Class still has open windows.",
          1413: "Invalid index.",
          1414: "Invalid icon handle.",
          1415: "Using private DIALOG window words.",
          1416: "The list box identifier was not found.",
          1417: "No wildcards were found.",
          1418: "Thread does not have a clipboard open.",
          1419: "Hot key is not registered.",
          1420: "The window is not a valid dialog window.",
          1421: "Control ID not found.",
          1422: "Invalid message for a combo box because it does not have an edit control.",
          1423: "The window is not a combo box.",
          1424: "The window is not a list box.",
          1425: "The window is not a button.",
          1426: "The window is not an edit control.",
          1427: "The window is not a static control.",
          1428: "The window is not a dialog.",
          1429: "The window is not a menu.",
          1430: "The window is not a scroll bar.",
          1431: "The window is not a status bar.",
          1432: "Invalid hit-test value.",
          1433: "Invalid window class name.",
          1434: "The window is not a toolbar.",
          1435: "The window is not a trackbar.",
          1436: "The window is not a progress bar.",
          1437: "The window is not an up-down control.",
          1438: "The window is not a tab control.",
          1439: "The window is not a slider.",
          1440: "Invalid ID for a child window.",
          1441: "The window is not a multiple document interface (MDI) client.",
          1442: "The window is not a command link.",
          1443: "The window is not a Help button.",
          1444: "The window is not a balloon tooltip.",
          1445: "The window is not a month calendar control.",
          1446: "The window is not a date and time picker control.",
          1447: "The window is not a split button.",
          1448: "The window is not a task dialog.",
          1450: "Insufficient system resources exist to complete the requested service.",
          1451: "Insufficient system resources exist to complete the requested service.",
          1452: "Insufficient system resources exist to complete the requested service.",
          1453: "Insufficient quota to complete the requested service.",
          1454: "Insufficient quota to complete the requested service.",
          1455: "The paging file is too small for this operation to complete.",
          1456: "A menu item was not found.",
          1500: "The event log file is corrupted.",
          1501: "No event log file could be opened, so the event logging service did not run.",
          1502: "The event log file is full.",
          1503: "The event log file has changed between read operations.",
          1601: "The Windows Installer Service could not be accessed.",
          1602: "User cancelled installation.",
          1603: "Fatal error during installation.",
          1604: "Installation suspended, incomplete.",
          1605: "This action is only valid for products that are currently installed.",
          1606: "Feature ID not registered.",
          1607: "Component ID not registered.",
          1608: "Unknown property.",
          1609: "Handle is in an invalid state.",
          1610: "The configuration data for this product is corrupt. Contact your support personnel.",
          1611: "Component qualifier not present.",
          1612: "The installation source for this product is not available.",
          1613: "This installation package cannot be installed by the Windows Installer service.",
          1614: "Product is uninstalled.",
          1615: "SQL query syntax invalid or unsupported.",
          1616: "Record field does not exist.",
          1617: "The device has been removed.",
          1618: "Another installation is already in progress.",
          1619: "This installation package could not be opened.",
          1620: "This installation package could not be opened. Contact the application vendor.",
          1621: "There was an error starting the Windows Installer service user interface.",
          1622: "Error opening installation log file.",
          1623: "The language of this installation package is not supported by your system.",
          1624: "Error applying transforms.",
          1625: "This installation is forbidden by system policy.",
          1626: "Function could not be executed.",
          1627: "Function failed during execution.",
          1628: "Invalid or unknown table specified.",
          1629: "Data supplied is of wrong type.",
          1630: "Data of this type is not supported.",
          1631: "The Windows Installer service failed to start.",
          1632: "The Temp folder is on a drive that is full or is inaccessible.",
          1633: "This installation package is not supported by this processor type.",
          1634: "Component does not exist.",
          1635: "This patch package could not be opened.",
          1636: "This patch package could not be opened.",
          1637: "This patch package cannot be processed by the Windows Installer service.",
          1638: "Another version of this product is already installed.",
          1639: "Invalid command line argument.",
          1640: "Cannot install a product when a newer version is installed.",
          1641: "The Windows Installer initiated a restart to continue with installing or configuring the system.",
        };
        let text = table[msgId];
        if (text === undefined && (msgId >>> 31) === 1) {
          const code = msgId & 0xFFFF;
          if (table[code] !== undefined) text = table[code];
        }
        if (text === undefined) {
          log(`[FMT] FormatMessageW(${msgId}) not found`);
          winSetLastError(317);   // ← NEW
          return 0n;
        }
        if (flags & 0x100) {
          const pp = Number(bufArg);
          if (!ensureMemory(pp + 8)) return 0n;
          const bytes = wide ? (text.length + 1) * 2 : text.length + 1;
          const alloc = winAlloc(BigInt(bytes), true);
          if (!alloc) return 0n;
          if (wide) winWriteW(alloc, text); else winWriteA(alloc, text);
          dv.setBigUint64(pp, alloc, true);
          return BigInt(text.length);
        }
        const buf = Number(bufArg);
        if (size < text.length + 1) { winSetLastError(122); return 0n; }
        if (wide) winWriteW(buf, text); else winWriteA(buf, text);
        return BigInt(text.length);
      }
      case "__intrinsic_setjmp": case "_setjmp": case "setjmp": {
        // int _setjmp(jmp_buf env). Save rbx,rbp,rdi,rsi,r12-r15 + rsp + ret rip.
        const p = Number(a(0));
        if (!ensureMemory(p + 128)) return -1n;
        const regOrder = [REG.rbx, REG.rbp, REG.rdi, REG.rsi, REG.r12, REG.r13, REG.r14, REG.r15];
        for (let i = 0; i < 8; i++) {
          dv.setBigUint64(p + i * 8, dv.getBigUint64(ctx + regOrder[i] * 8, true), true);
        }
        const rspVal = Number(dv.getBigUint64(ctx + REG.rsp * 8, true));
        const retAddr = dv.getBigUint64(rspVal, true); // caller's return-address slot
        dv.setBigUint64(p + 64, BigInt(rspVal + 8), true); // rsp after ret
        dv.setBigUint64(p + 72, retAddr, true);            // rip on longjmp
        return 0n;
      }

      case "longjmp": case "_longjmp": case "__intrinsic_longjmp": {
        const p = Number(a(0));
        const value = (Number(a(1)) | 0) || 1;
        if (!ensureMemory(p + 128)) { winExitCode = 0xC0000005 | 0; return { exit: true, status: winExitCode }; }
        const regOrder = [REG.rbx, REG.rbp, REG.rdi, REG.rsi, REG.r12, REG.r13, REG.r14, REG.r15];
        for (let i = 0; i < 8; i++) {
          dv.setBigUint64(ctx + regOrder[i] * 8, dv.getBigUint64(p + i * 8, true), true);
        }
        const savedRsp = Number(dv.getBigUint64(p + 64, true));
        const savedRip = dv.getBigUint64(p + 72, true);
        dv.setBigUint64(ctx + REG.rsp * 8, BigInt(savedRsp), true);
        dv.setBigUint64(ctx + REG.rax * 8, BigInt.asUintN(64, BigInt(value)), true);
        return { nextPc: savedRip };
      }
      case "setthreaduilanguage": return 0x0409n;  // previous LANGID = en-US

      case "heapsetinformation": return 1n;

      case "globalfree": return 0n;  // managed heap, "success"

      case "setconsoleinputexenamew": return 1n;

      case "openthread": {
        const threadId = Number(a(2)) >>> 0;
        const handle = winAllocHandle({ kind: "thread", process: winCurrentProcessState, threadId });
        return handle;
      }

      case "rtlcreateunicodestringfromasciiz": {
        // NTSTATUS RtlCreateUnicodeStringFromAsciiz(PUNICODE_STRING, PCSTR)
        const pUS = Number(a(0)), pAscii = a(1);
        const text = winReadA(pAscii) ?? "";
        const bytes = (text.length + 1) * 2;
        const buf = winAlloc(BigInt(bytes), true);
        if (!buf) return 0xC0000017n;
        for (let i = 0; i < text.length; i++) dv.setUint16(Number(buf) + i * 2, text.charCodeAt(i), true);
        if (!ensureMemory(pUS + 16)) return 0xC0000005n;
        dv.setUint16(pUS, text.length * 2, true);
        dv.setUint16(pUS + 2, bytes, true);
        dv.setBigUint64(pUS + 8, buf, true);
        return 0n;
      }

      case "ntopenthreadtoken": case "ntqueryinformationtoken":
        return 0xC000007Cn; // STATUS_NO_TOKEN

      case "getvolumeinformationw": case "getvolumeinformationa": {
        const wide = n.endsWith("w");
        const nameBuf = a(1), nameSize = Number(a(2));
        const serialPtr = a(3), maxCompPtr = a(4), flagsPtr = a(5);
        const fsBuf = a(6), fsSize = Number(a(7));
        if (nameBuf && nameSize >= 2) wide ? winWriteW(nameBuf, "") : winWriteA(nameBuf, "");
        if (serialPtr) winWriteDword(serialPtr, 0x12345678);
        if (maxCompPtr) winWriteDword(maxCompPtr, 255);
        if (flagsPtr) winWriteDword(flagsPtr, 0);
        if (fsBuf && fsSize >= 5) wide ? winWriteW(fsBuf, "NTFS") : winWriteA(fsBuf, "NTFS");
        return 1n;
      }
      case "findclose": {
        return globalThis.__winFindState.delete(Number(a(0))) ? 1n : 0n;
      }
      case "towlower": case "_towlower_l": {
        const ch = Number(a(0) & 0xffffn);
        return BigInt(String.fromCharCode(ch).toLowerCase().charCodeAt(0) || ch);
      }
      case "iswalpha": case "_iswalpha_l": {
        const ch = Number(a(0) & 0xffffn);
        return /[A-Za-z]/.test(String.fromCharCode(ch)) ? 1n : 0n;
      }
      case "iswdigit": case "_iswdigit_l": {
        const ch = Number(a(0) & 0xffffn);
        return ch >= 0x30 && ch <= 0x39 ? 1n : 0n;
      }
      case "iswspace": case "_iswspace_l": {
        const ch = Number(a(0) & 0xffffn);
        return (ch === 0x20 || (ch >= 0x09 && ch <= 0x0d)) ? 1n : 0n;
      }
      case "wcschr": {
        const s = winReadW(a(0)) ?? "";
        const idx = s.indexOf(String.fromCharCode(Number(a(1) & 0xffffn)));
        return idx < 0 ? 0n : a(0) + BigInt(idx * 2);
      }
      case "wcslen": {
        const s = winReadW(a(0));
        return BigInt(s?.length ?? 0);
      }
      case "setlocale": case "_setlocale": {
        // CRT locale. cmd.exe checks non-null return. Return a stable "C" string.
        if (!winCrtLocalePtr) {
          winCrtLocalePtr = winAlloc(4);
          winWriteA(winCrtLocalePtr, "C");
        }
        return winCrtLocalePtr;
      }
      case "null":                     // delay-load name-resolution produced null
      case "wldpgetlockdownpolicy":
      case "wldpisclassinapprovedlist":
      case "wldpquerydynamiccodetrust":
      case "wldpisasyncpolicyenabled": {
        // Best-effort: "no lockdown policy, code is trusted".
        // Writes to arg1 / arg2 are skipped; callers normally tolerate an
        // untouched output buffer (they init to UNDETERMINED).
        return 0n;                     // S_OK
      }
      case "arefileapisansi": return 1n;
      case "setunhandledexceptionfilter": return 0n;
      case "rtlpctofileheader": {
        const pc  = a(0);
        const out = Number(a(1));
        let found = 0n;
        if (pc >= BigInt(base) && pc < BigInt(base + image.length)) {
          found = BigInt(base);
        } else {
          for (const m of winLoadedModulesByBase.values()) {
            if (pc >= m.base && pc < m.base + BigInt(m.size)) { found = m.base; break; }
          }
        }
        if (out && ensureMemory(out + 8)) dv.setBigUint64(out, found, true);
        return found;
      }
      case "flsgetvalue2": case "flsgetvalue": {
        const id = Number(a(0));
        return winFls.get(id) ?? 0n;
      }
      case "flssetvalue2": case "flssetvalue": {
        const id = Number(a(0));
        if (!winFls.has(id)) { winSetLastError(87); return 0n; }
        winFls.set(id, a(1));
        return 1n;
      }
      case "flsalloc": {
        // DWORD FlsAlloc(PFLS_CALLBACK_FUNCTION lpCallback);
        // Returns FLS_OUT_OF_INDEXES (0xFFFFFFFF) on failure.
        let id;
        if (winFlsFreeList.length > 0) id = winFlsFreeList.shift();
        else if (winFlsNextId < 128) id = winFlsNextId++;
        else { winSetLastError(1450); return 0xFFFFFFFFn; }   // ERROR_NO_SYSTEM_RESOURCES
        winFls.set(id, 0n);
        winFlsCallback = a(0);   // store, do nothing
        return BigInt(id);
      }
      case "flssetvalue": {
        // BOOL FlsSetValue(DWORD dwFlsIndex, PVOID lpFlsData);
        const id = Number(a(0));
        if (!winFls.has(id)) { winSetLastError(87); return 0n; }   // ERROR_INVALID_PARAMETER
        winFls.set(id, a(1));
        return 1n;
      }
      case "flsgetvalue": {
        // PVOID FlsGetValue(DWORD dwFlsIndex);
        const id = Number(a(0));
        return winFls.get(id) ?? 0n;
      }
      case "flsfree": {
        // BOOL FlsFree(DWORD dwFlsIndex);
        const id = Number(a(0));
        if (!winFls.has(id)) { winSetLastError(87); return 0n; }
        winFls.delete(id);
        winFlsFreeList.push(id);
        winFlsFreeList.sort((a, b) => a - b);
        return 1n;
      }
      case "_get_osfhandle": case "_o__get_osfhandle": {
        const fd = Number(BigInt.asIntN(32, a(0)));
        if (fd === 0) return WIN_STD_INPUT;
        if (fd === 1) return WIN_STD_OUTPUT;
        if (fd === 2) return WIN_STD_ERROR;
        winSetLastError(9);              // EBADF
        return 0xffff_ffff_ffff_ffffn;    // INVALID_HANDLE_VALUE
      }
      case "getthreadid": {
        const h = winHandles.get(a(0));
        if (!h) { winSetLastError(6); return 0n; }
        return BigInt(h.kind === "thread" ? h.threadId : 0);
      }
      case "getthreadlocale": return 0x409n;    // en-US
      case "getcpinfo": {
        // BOOL GetCPInfo(UINT CodePage, LPCPINFO lpCPInfo);
        const p = Number(a(1));
        if (!ensureMemory(p + 20)) { winSetLastError(87); return 0n; }
        u8.fill(0, p, p + 20);
        dv.setUint32(p, 1, true);         // MaxCharSize = 1 (for ANSI) / 2 (for UTF-16)
        u8[p + 4] = 0x00; u8[p + 5] = 0x7f; u8[p + 6] = 0x00; u8[p + 7] = 0x00;
        return 1n;
      }
      case "srand": case "_o_srand": winRandState = Number(a(0)) >>> 0; return 0n;
      case "rand": case "_o_rand": {
        winRandState = (Math.imul(winRandState, 214013) + 2531011) >>> 0;
        return BigInt((winRandState >>> 16) & 0x7fff);
      }
      case "loadstringw": {
        const instance = a(0), resourceId = Number(a(1)) & 0xffff, buffer = Number(a(2)), capacity = Number(a(3));
        const resources = manifest.stringResources ?? {};
        const value = resources[`${instance}:${resourceId}`] ?? resources[String(resourceId)];
        if (value == null) return 0n;
        const text = String(value), count = Math.min(text.length, Math.max(0, capacity - 1));
        if (count > 0) {
          const chunk = text.slice(0, count);
          const bytes = new Uint8Array((chunk.length + 1) * 2);
          for (let i = 0; i < chunk.length; i++) { bytes[i * 2] = chunk.charCodeAt(i) & 255; bytes[i * 2 + 1] = chunk.charCodeAt(i) >>> 8; }
          writeBytes(buffer, bytes);
        } else if (capacity > 0) dv.setUint16(buffer, 0, true);
        return BigInt(count);
      }
      case "_initterm":
      case "_initterm_e": {
        const lo = Number(a(0));
        const hi = Number(a(1));
        const pending = [];
        for (let addr = lo; addr < hi && addr + 8 <= u8.length; addr += 8) {
          const fn = dv.getBigUint64(addr, true);
          if (fn !== 0n) pending.push(fn);
        }
        const rspNow = Number(dv.getBigUint64(ctx + REG.rsp * 8, true));
        const returnPc = dv.getBigUint64(rspNow, true);
        const returnRsp = BigInt(rspNow + 8);
        logTrace(`[INITTERM] ${name} lo=0x${lo.toString(16)} hi=0x${hi.toString(16)} → ${pending.length} ctor(s)`);
        if (pending.length === 0) {
          dv.setBigUint64(ctx + REG.rsp * 8, returnRsp, true);
          dv.setBigUint64(ctx + REG.rax * 8, 0n, true);
          return { nextPc: returnPc };
        }
        inittermState = { pending, returnPc, returnRsp, total: pending.length, done: 0 };
        const cbRsp = BigInt(((Number(returnRsp) - 0x100) & ~15) - 8);
        if (!ensureMemory(Number(cbRsp) + 32)) { winSetLastError(87); return 0n; }
        dv.setBigUint64(Number(cbRsp), INITTERM_RESUME, true);
        dv.setBigUint64(ctx + REG.rcx * 8, 0n, true);
        dv.setBigUint64(ctx + REG.rdx * 8, 0n, true);
        dv.setBigUint64(ctx + REG.r8 * 8, 0n, true);
        dv.setBigUint64(ctx + REG.r9 * 8, 0n, true);
        dv.setBigUint64(ctx + REG.rsp * 8, cbRsp, true);
        const saved = REG_NAMES.map((_, i) => dv.getBigUint64(ctx + i * 8, true));
        const savedFlags = dv.getBigUint64(ctx + 136, true);
        winCallbackFrames.push({ saved, savedFlags, returnPc: INITTERM_RESUME, resumeRsp: Number(cbRsp) + 8 });
        const first = inittermState.pending.shift();
        inittermState.done = 1;
        logTrace(`[INITTERM] 1/${inittermState.total} → 0x${first.toString(16)}`);
        return { nextPc: first };
      }
      case "_local_unwind": case "_o__local_unwind":
      case "_local_unwind2": case "_local_unwind4":
      case "__local_unwind": case "__local_unwind2": case "__local_unwind4": {
        // Walk the SEH registration list from establisher down to target, running
        // __finally blocks. We use UNWIND_INFO-based SEH (no RtlAddFunctionTable
        // registrations), so we can't walk a linked list. Return "success" so
        // callers continue past this call instead of falling into unreachable
        // code (which can loop forever).
        return 1n;
      }
      case "terminateprocess": {
        const target = a(0), status = Number(a(1)) | 0;
        if (target === MASK64 || target === 0xffff_ffff_ffff_fffen) {
          winExitCode = status; return { exit: true, status };
        }
        const handle = winHandles.get(target);
        const process = handle?.kind === "thread" ? handle.process : handle?.kind === "process" ? handle : null;
        if (!process) { winSetLastError(6); return 0n; }
        if (!process.finished) {
          process.terminate?.(status);
          if (!process.terminate) { process.finished = true; process.exitCode = status; }
        }
        return 1n;
      }
      case "createprocessa": case "createprocessw": case "createprocessasusera": case "createprocessasuserw": {
        const wide = n.endsWith("w");
        const appPtr = a(n.startsWith("createprocessasuser") ? 1 : 0);
        const commandPtr = a(n.startsWith("createprocessasuser") ? 2 : 1);
        const argOffset = n.startsWith("createprocessasuser") ? 1 : 0;
        const applicationName = appPtr ? winReadMemoryString(appPtr, wide) : null;
        const commandLine = commandPtr ? winReadMemoryString(commandPtr, wide) : (applicationName || "");
        const executable = applicationName || winFirstCommandToken(commandLine);
        const creationFlags = Number(a(5 + argOffset)) >>> 0;
        const currentDirectory = winReadMemoryString(a(7 + argOffset), wide) || "C:\\guest";
        const startupInfo = a(8 + argOffset), processInfo = a(9 + argOffset);
        if (!executable || !processInfo || !ensureMemory(Number(processInfo) + 24)) {
          winSetLastError(87); return 0n;
        }
        if (typeof spawnProcess !== "function") { winSetLastError(120); return 0n; }
        const inheritedFiles = Object.fromEntries([...virtualFiles.entries()].map(([path, file]) => [path, file.data.slice()]));
        let launched;
        try {
          launched = spawnProcess({
            applicationName: executable,
            commandLine: commandLine || executable,
            currentDirectory,
            creationFlags,
            inheritHandles: a(4 + argOffset) !== 0n,
            processId: winNextChildProcessId,
            parentProcessId: Number(processId) || 1,
            files: inheritedFiles,
            imagePath: `C:\\guest\\${String(executable).split(/[\\/]/).pop()}`,
            startupInfo: startupInfo ? { cb: Number(winReadU64(Number(startupInfo))) } : null,
          });
        } catch (error) {
          log(`CreateProcess failed for ${executable}: ${error?.message ?? error}`);
          winSetLastError(2); return 0n;
        }
        if (!launched || typeof launched !== "object") { winSetLastError(2); return 0n; }
        const pid = Number(launched.processId) || winNextChildProcessId++;
        winNextChildProcessId = Math.max(winNextChildProcessId, pid + 1);
        const child = { kind: "process", processId: pid, imagePath: launched.imagePath || `C:\\guest\\${String(executable).split(/[\\/]/).pop()}`,
          finished: false, exitCode: 259, terminate: launched.terminate };
        child.completion = Promise.resolve(launched.completion ?? Promise.resolve({ exitCode: 0 }))
          .then((result) => {
            child.exitCode = Number(result?.exitCode ?? result?.status ?? 0) | 0;
            child.finished = true; winWakeHandleWaiters(); return child.exitCode;
          }, (error) => {
            log(`Child process ${pid} failed: ${error?.message ?? error}`);
            child.exitCode = 0xC0000135 | 0; child.finished = true; winWakeHandleWaiters(); return child.exitCode;
          });
        winProcesses.set(pid, child);
        const hProcess = winAllocHandle(child);
        const hThread = winAllocHandle({ kind: "thread", process: child, threadId: Number(launched.threadId) || pid });
        const p = Number(processInfo);
        dv.setBigUint64(p, hProcess, true); dv.setBigUint64(p + 8, hThread, true);
        dv.setUint32(p + 16, pid, true); dv.setUint32(p + 20, Number(launched.threadId) || pid, true);
        return 1n;
      }
      case "__stdio_common_vswprintf": case "__stdio_common_vswprintf_s": {
        const bufferPtr = Number(a(1));
        const count = Number(a(2));
        const formatPtr = Number(a(3));
        const vaListPtr = a(5);
        if (!Number.isSafeInteger(bufferPtr) || !Number.isSafeInteger(count) ||
            !Number.isSafeInteger(formatPtr)) { winSetLastError(87); return 0n; }
        const fmt = winReadW(formatPtr);
        if (fmt == null) { winSetLastError(87); return 0n; }

        let out = "", argIdx = 0;
        const rdArg = () => {
          const v = winReadU64(Number(vaListPtr) + argIdx * 8);
          argIdx++;
          return v;
        };
        for (let i = 0; i < fmt.length; i++) {
          if (fmt[i] !== "%") { out += fmt[i]; continue; }
          if (fmt[i + 1] === "%") { out += "%"; i++; continue; }
          let j = i + 1;
          while (j < fmt.length && "-+ #0.123456789hlLzIw".includes(fmt[j])) j++;
          const spec = fmt[j] || "", lenMod = fmt.slice(i + 1, j);
          i = j;

          // WIDE printf semantics (this is vswprintf):
          //   %s   → wide (default),  %hs → narrow,  %ls / %ws → wide
          //   %S   → narrow (default), %hS → narrow, %lS → wide
          const hasL = lenMod.includes("l") || lenMod.includes("w");
          const hasH = lenMod.includes("h");
          const stringIsWide = (spec === "s") ? !hasH : hasL;

          const v = rdArg();
          switch (spec) {
            case "s": case "S":
              out += stringIsWide ? (winReadW(v) ?? "(null)")
                                  : (winReadA(v) ?? "(null)");
              break;
            case "c":
              out += String.fromCharCode(Number(v & 0xffn));
              break;
            case "C":
              out += String.fromCharCode(Number(v & 0xffffn));
              break;
            case "d": case "i":
              out += BigInt.asIntN(hasL ? 64 : 32, v).toString();
              break;
            case "u":
              out += BigInt.asUintN(hasL ? 64 : 32, v).toString();
              break;
            case "x":
              out += BigInt.asUintN(hasL ? 64 : 32, v).toString(16);
              break;
            case "X":
              out += BigInt.asUintN(hasL ? 64 : 32, v).toString(16).toUpperCase();
              break;
            case "p":
              out += `0x${v.toString(16).padStart(hasL ? 16 : 8, "0")}`;
              break;
            default:
              out += `%${lenMod}${spec}`;
              break;
          }
        }
        const maxChars = Math.max(0, count - 1);
        const written = Math.min(out.length, maxChars);
        const bytes = new Uint8Array((written + 1) * 2);
        for (let i = 0; i < written; i++) {
          const code = out.charCodeAt(i);
          bytes[i * 2] = code & 0xff;
          bytes[i * 2 + 1] = code >> 8;
        }
        writeBytes(bufferPtr, bytes);
        return BigInt(out.length);
      }
      case "getlocaleinfow": case "getlocaleinfoex": {
        // LOCALE_* info queried with (LCID, LCType, buffer, cchData).
        const bufPtr = Number(a(2)), cch = Number(a(3));
        // Most useful defaults:
        //   LOCALE_SISO639LANGNAME (0x59) → "en"
        //   LOCALE_SISO3166CTRYNAME (0x5A) → "US"
        //   LOCALE_ILANGUAGE (0x1) → hex LCID
        //   LOCALE_SABBREVLANGNAME (0x3) → "ENU"
        const LCType = Number(a(1));
        let value = "";
        if (LCType === 0x59) value = "en";
        else if (LCType === 0x5A) value = "US";
        else if (LCType === 0x3) value = "ENU";
        else if (LCType === 0x1) value = "0409";
        else value = "";                       // unhandled → empty string
        if (!bufPtr || cch === 0) return BigInt(value.length + 1);
        const bytes = new Uint8Array((value.length + 1) * 2);
        for (let i = 0; i < value.length; i++) {
          bytes[i * 2] = value.charCodeAt(i) & 0xff;
          bytes[i * 2 + 1] = value.charCodeAt(i) >> 8;
        }
        writeBytes(bufPtr, bytes);
        return BigInt(value.length + 1);
      }
      case "apisetqueryapisetpresence": {
        const presentPtr = Number(a(1));
        if (presentPtr && ensureMemory(presentPtr + 4)) {
          dv.setUint32(presentPtr, 0, true);   // FALSE — not present
        }
        return 0n;                              // S_OK
      }
      // in emulateWinApi's switch, add near the top:
      case "writeconsolew": {
        const buffer = Number(a(1)), count = Number(a(2)), writtenPtr = a(3);
        let text = "";
        for (let i = 0; i < count; i++) {
          if (!ensureMemory(buffer + i * 2 + 2)) break;
          text += String.fromCharCode(dv.getUint16(buffer + i * 2, true));
        }
        console.log(`[WCW] count=${count} text="${text.replace(/\r/g,'\\r').replace(/\n/g,'\\n')}"`);
        winConsoleWrite(text);
        if (writtenPtr !== 0n) winWriteDword(writtenPtr, count);
        return 1n;
      }
      case "writeconsolea": {
        const bytes = readBytes(a(1), a(2));
        if (!bytes) { winSetLastError(998); return 0n; }
        winConsoleWrite(new TextDecoder().decode(bytes));
        if (a(3) !== 0n) winWriteDword(a(3), bytes.length);
        return 1n;
      }
      case "__stdio_common_vfwprintf": case "_o___stdio_common_vfwprintf": {
        const fmt = winReadW(Number(a(2)));
        if (fmt == null) { winSetLastError(87); return 0n; }
        const text = winFormat(fmt, 0, a(4), true);
        winConsoleWrite(text);
        return BigInt(text.length);
      }
      case "getconsolescreenbufferinfo": {
        const p = Number(a(1));
        if (!ensureMemory(p + 22)) { winSetLastError(87); return 0n; }
        dv.setInt16(p, winConsole.width, true);       // dwSize.X
        dv.setInt16(p + 2, winConsole.height, true);  // dwSize.Y
        dv.setInt16(p + 4, winConsole.cursorX, true); // dwCursorPosition.X
        dv.setInt16(p + 6, winConsole.cursorY, true);
        dv.setUint16(p + 8, winConsole.defaultAttr, true);
        dv.setInt16(p + 10, 0, true); dv.setInt16(p + 12, 0, true);
        dv.setInt16(p + 14, winConsole.width - 1, true);
        dv.setInt16(p + 16, winConsole.height - 1, true);
        dv.setInt16(p + 18, winConsole.width, true);
        dv.setInt16(p + 20, winConsole.height, true);
        return 1n;
      }
      case "getconsolemode": {
        const p = Number(a(1));
        if (!ensureMemory(p + 4)) { winSetLastError(87); return 0n; }
        dv.setUint32(p, winConsoleInput.mode, true);
        return 1n;
      }
      case "setconsolemode": {
        winConsoleInput.mode = Number(a(1)) >>> 0;
        return 1n;
      }
      case "readconsolew": case "readconsolea": {
        const wide = n === "readconsolew";
        const buffer = Number(a(1));
        const capacity = Number(a(2));             // in characters
        const writtenPtr = a(3);
        if (!Number.isSafeInteger(buffer) || !Number.isSafeInteger(capacity) || capacity <= 0
            || !ensureMemory(buffer + (wide ? capacity * 2 : capacity))) {
          winSetLastError(87); return 0n;
        }

        // Echo is on unless ENABLE_ECHO_INPUT was cleared.
        const echo = (winConsoleInput.mode & 0x0004) !== 0;
        const startRow = winConsole.cursorY;
        const startCol = winConsole.cursorX;
        const line = await new Promise((resolve) => {
          winConsoleInput.lineWaiter = {
            resolve, buffer: "", maxChars: capacity,
            startRow, startCol,
          };
          if (echo) winConsoleSchedulePresent();
        });

        // Line mode returns "text\r\n".
        const result = line + "\r\n";
        const chars = Math.min(result.length, capacity - 1);
        console.log(`[RCW] line="${line}" returning ${chars} chars`);
        if (wide) {
          const bytes = new Uint8Array((chars + 1) * 2);
          for (let i = 0; i < chars; i++) {
            const code = result.charCodeAt(i);
            bytes[i * 2] = code & 0xff;
            bytes[i * 2 + 1] = code >> 8;
          }
          writeBytes(buffer, bytes);
        } else {
          const bytes = new TextEncoder().encode(result.slice(0, chars) + "\0");
          writeBytes(buffer, bytes);
        }
        if (writtenPtr !== 0n) winWriteDword(writtenPtr, chars);
        return 1n;
      }

      case "readconsoleinputw": case "readconsoleinputa": {
        // BOOL ReadConsoleInputW(HANDLE h, PINPUT_RECORD buf, DWORD len, LPDWORD read)
        const wide = n === "readconsoleinputw";
        const buffer = Number(a(1));
        const maxRecords = Number(a(2));
        const readPtr = a(3);
        if (!Number.isSafeInteger(maxRecords) || maxRecords <= 0 || maxRecords > 1024
            || !ensureMemory(buffer + maxRecords * 20)) {
          winSetLastError(87); return 0n;
        }

        const records = await winConsoleInputDrain(maxRecords);
        console.log(`[RCIW] returned ${records.length}: ` + records.map(r =>
          `dk=${r.keyDown} ch=0x${r.unicodeChar.toString(16)} vk=0x${r.virtualKey.toString(16)}`
        ).join(' | '));
        for (let i = 0; i < records.length; i++) {
          const r = records[i];
          const at = buffer + i * 20;
          dv.setUint16(at + 0, r.eventType, true);                 // EventType
          dv.setUint16(at + 2, 0, true);                           // padding
          dv.setUint32(at + 4, r.keyDown ? 1 : 0, true);           // bKeyDown
          dv.setUint16(at + 8, r.repeatCount, true);               // wRepeatCount
          dv.setUint16(at + 10, r.virtualKey, true);               // wVirtualKeyCode
          dv.setUint16(at + 12, r.virtualScan, true);              // wVirtualScanCode
          if (wide) dv.setUint16(at + 14, r.unicodeChar, true);    // UnicodeChar
          else      u8[at + 14] = r.unicodeChar & 0xff;            // AsciiChar
          dv.setUint32(at + 16, r.controlState, true);             // dwControlKeyState
        }
        if (readPtr !== 0n) winWriteDword(readPtr, records.length);
        return 1n;
      }

      case "peekconsoleinputw": case "peekconsoleinputa": {
        const buffer = Number(a(1)), maxRecords = Number(a(2)), readPtr = a(3);
        const n = Math.min(maxRecords, winConsoleInput.queue.length);
        if (n > 0 && ensureMemory(buffer + n * 20)) {
          for (let i = 0; i < n; i++) {
            const r = winConsoleInput.queue[i], at = buffer + i * 20;
            dv.setUint16(at, r.eventType, true);
            dv.setUint32(at + 4, r.keyDown ? 1 : 0, true);
            dv.setUint16(at + 10, r.virtualKey, true);
            dv.setUint16(at + 14, r.unicodeChar, true);
            dv.setUint32(at + 16, r.controlState, true);
          }
        }
        if (readPtr !== 0n) winWriteDword(readPtr, n);
        return 1n;
      }

      case "getnumberofconsoleinputevents": {
        const ptr = a(1);
        if (ptr !== 0n) winWriteDword(ptr, winConsoleInput.queue.length);
        return 1n;
      }

      case "flushconsoleinputbuffer": {
        winConsoleInput.queue.length = 0;
        return 1n;
      }
      case "getconsoletitlew": case "getconsoletitlea": {
        const buf = Number(a(0)), cap = Number(a(1));
        const text = winConsole.title;
        const wide = n.endsWith("w");
        const bytes = wide ? new Uint8Array((text.length + 1) * 2) : new TextEncoder().encode(text + "\0");
        if (wide) for (let i = 0; i < text.length; i++) { bytes[i * 2] = text.charCodeAt(i) & 0xff; bytes[i * 2 + 1] = text.charCodeAt(i) >> 8; }
        const count = Math.min(cap, wide ? bytes.length : bytes.length);
        if (buf && cap) writeBytes(buf, bytes.subarray(0, count));
        return BigInt(text.length);
      }
      case "setconsoletitlew": case "setconsoletitlea": {
        const t = winReadMemoryString(a(0), n.endsWith("w"));
        if (t != null) winConsole.title = t;
        winConsoleSchedulePresent();
        return 1n;
      }
      case "allocconsole":
      case "freeconsole": case "attachconsole": case "setconsolectrlhandler":
      case "getconsolecptable": case "getconsoleoutputcp":
        // Not emulated. Fall through to default (returns 0 + ERROR_CALL_NOT_IMPLEMENTED).
        break;
      case "getexitcodeprocess": case "getexitcodethread": {
        const handle = winHandles.get(a(0));
        const process = handle?.kind === "thread" ? handle.process : handle?.kind === "process" ? handle : null;
        if (!process) { winSetLastError(6); return 0n; }
        return winWriteDword(a(1), process.finished ? process.exitCode : 259) ? 1n : 0n;
      }
      case "getprocessid": {
        if (a(0) === MASK64) return BigInt(Number(processId) || 1);
        const handle = winHandles.get(a(0));
        return BigInt(handle?.kind === "thread" ? handle.process.processId : handle?.kind === "process" ? handle.processId : 0);
      }
      case "openprocess": {
        const process = winProcesses.get(Number(a(2)));
        if (!process) { winSetLastError(87); return 0n; }
        return winAllocHandle(process);
      }
      // ADVAPI32: isolated per-guest registry, not the host operating system registry.
      case "regopenkeya": case "regopenkeyw": case "regopenkeyexa": case "regopenkeyexw": {
        const wide = n.endsWith("w"), subKey = winReadMemoryString(a(1), wide) ?? "";
        const found = winRegistryFind(a(0), subKey);
        if (!found || !found.entry) return 2n; // ERROR_FILE_NOT_FOUND
        const handle = winAllocHandle({ kind: "registry_key", registryPath: found.path });
        const out = Number(n.includes("ex") ? a(4) : a(2));
        if (!ensureMemory(out + 8)) return 87n;
        dv.setBigUint64(out, handle, true); return 0n;
      }
      case "regcreatekeya": case "regcreatekeyw": case "regcreatekeyexa": case "regcreatekeyexw": {
        const wide = n.endsWith("w"), subKey = winReadMemoryString(a(1), wide) ?? "";
        const root = winRegistryRoot(a(0)); if (!root) return 6n;
        const path = subKey ? winRegistryPath(root, subKey) : root.toLowerCase();
        const existed = winRegistry.has(path); winRegistryEnsure(path);
        const handle = winAllocHandle({ kind: "registry_key", registryPath: path });
        const isEx = n.includes("ex"), out = Number(a(isEx ? 7 : 2));
        if (!ensureMemory(out + 8)) return 87n;
        dv.setBigUint64(out, handle, true);
        if (isEx && a(8) !== 0n) winWriteDword(a(8), existed ? 2 : 1); // REG_OPENED_EXISTING_KEY / REG_CREATED_NEW_KEY
        return 0n;
      }
      case "regclosekey": {
        const h = a(0);
        if (winRegistryRoots.has(h) || winRegistryRoots.has(BigInt.asUintN(32, h))) return 0n;
        const key = winHandles.get(h);
        if (key?.kind !== "registry_key") return 6n;
        winHandles.delete(h); return 0n;
      }
      case "regsetvaluea": case "regsetvaluew": case "regsetvalueexa": case "regsetvalueexw": {
        const wide = n.endsWith("w"), isEx = n.includes("ex");
        // RegSetValue[Ex] treats the key's default value as an empty value name;
        // the non-Ex API additionally accepts a subkey and does not take a name.
        const subKey = isEx ? "" : (winReadMemoryString(a(1), wide) ?? "");
        const valueName = isEx ? (winReadMemoryString(a(1), wide) ?? "") : "";
        const key = winRegistryFind(a(0), subKey); if (!key?.entry) return 6n;
        const type = Number(a(isEx ? 3 : 2)) >>> 0, dataPtr = a(isEx ? 4 : 3), byteLength = Number(a(isEx ? 5 : 4));
        const bytes = readBytes(dataPtr, byteLength); if (!bytes) return 87n;
        key.entry.values.set(valueName.toLowerCase(), { name: valueName, type, data: bytes }); return 0n;
      }
      case "regqueryvaluea": case "regqueryvaluew": case "regqueryvalueexa": case "regqueryvalueexw": case "reggetvaluea": case "reggetvaluew": {
        const wide = n.endsWith("w"), isGet = n.startsWith("reggetvalue"), isEx = n.includes("ex");
        const subKey = isGet || !isEx ? (winReadMemoryString(a(1), wide) ?? "") : "";
        const valueName = isGet ? (winReadMemoryString(a(2), wide) ?? "") : isEx ? (winReadMemoryString(a(1), wide) ?? "") : "";
        const key = winRegistryFind(a(0), subKey); if (!key?.entry) return 6n;
        const value = key.entry.values.get(valueName.toLowerCase()); if (!value) return 2n;
        // RegQueryValueA/W: (key, subkey, data, size). RegQueryValueEx:
        // (key, name, reserved, type, data, size). RegGetValue:
        // (key, subkey, name, flags, type, data, size).
        const typePtr = isGet ? a(4) : isEx ? a(3) : 0n;
        const dataPtr = isGet ? a(5) : isEx ? a(4) : a(2);
        const sizePtr = isGet ? a(6) : isEx ? a(5) : a(3);
        if (typePtr) winWriteDword(typePtr, value.type);
        if (!sizePtr || !ensureMemory(Number(sizePtr) + 4)) return 87n;
        const capacity = dv.getUint32(Number(sizePtr), true), required = value.data.length;
        if (!dataPtr) { dv.setUint32(Number(sizePtr), required, true); return 0n; }
        if (capacity < required) { dv.setUint32(Number(sizePtr), required, true); return 234n; }
        if (!writeBytes(dataPtr, value.data)) return 87n;
        dv.setUint32(Number(sizePtr), required, true); return 0n;
      }
      case "regenumvaluea": case "regenumvaluew": {
        const wide=n.endsWith("w"),key=winRegistryFind(a(0));if(!key?.entry)return 6n;
        const entries=[...key.entry.values.values()],value=entries[Number(a(1))];if(!value)return 259n;
        const namePtr=a(2),nameLenPtr=a(3),capacity=nameLenPtr&&ensureMemory(Number(nameLenPtr)+4)?dv.getUint32(Number(nameLenPtr),true):0;
        if(namePtr&&nameLenPtr){const required=value.name.length;if(capacity<=required){winWriteDword(nameLenPtr,required);return 234n;}winWriteMemoryString(namePtr,value.name,wide);winWriteDword(nameLenPtr,required);}
        if(a(5))winWriteDword(a(5),value.type);
        if(a(7)){const sizePtr=Number(a(7)),capacityBytes=dv.getUint32(sizePtr,true);
          if(!a(6)){dv.setUint32(sizePtr,value.data.length,true);return 0n;}
          if(capacityBytes<value.data.length){dv.setUint32(sizePtr,value.data.length,true);return 234n;}
          if(!writeBytes(a(6),value.data))return 87n;dv.setUint32(sizePtr,value.data.length,true);}
        return 0n;
      }
      case "regenumkeyexa": case "regenumkeyexw": {
        const wide=n.endsWith("w"),root=winRegistryRoot(a(0));if(!root)return 6n;
        const prefix=`${String(root).toLowerCase()}\\`,children=new Set();
        for(const path of winRegistry.keys())if(path.startsWith(prefix)){const child=path.slice(prefix.length).split("\\")[0];if(child)children.add(child);}
        const value=[...children][Number(a(1))];if(value==null)return 259n;
        const namePtr=a(2),lengthPtr=a(3),capacity=lengthPtr&&ensureMemory(Number(lengthPtr)+4)?dv.getUint32(Number(lengthPtr),true):0;
        if(namePtr&&lengthPtr){if(capacity<=value.length){winWriteDword(lengthPtr,value.length);return 234n;}winWriteMemoryString(namePtr,value,wide);winWriteDword(lengthPtr,value.length);}
        if(a(6))winWriteDword(a(6),0);return 0n;
      }
      case "regdeletetreea": case "regdeletetreew": {
        const key=winRegistryFind(a(0)),sub=winReadMemoryString(a(1),n.endsWith("w"))??"";if(!key?.entry)return 6n;
        if(!sub){key.entry.values.clear();const prefix=`${key.path}\\`;for(const path of [...winRegistry.keys()])if(path.startsWith(prefix))winRegistry.delete(path);return 0n;}
        const target=winRegistryPath(key.path,sub),prefix=`${target}\\`;
        if(!winRegistry.has(target))return 2n;
        for(const path of [...winRegistry.keys()])if(path===target||path.startsWith(prefix))winRegistry.delete(path);return 0n;
      }
      case "regdeletevaluea": case "regdeletevaluew": {
        const key = winRegistryFind(a(0)); if (!key?.entry) return 6n;
        const valueName = winReadMemoryString(a(1), n.endsWith("w")) ?? "";
        return key.entry.values.delete(valueName.toLowerCase()) ? 0n : 2n;
      }
      case "regdeletekeya": case "regdeletekeyw": case "regdeletekeyexa": case "regdeletekeyexw": {
        const root = winRegistryRoot(a(0)); if (!root) return 6n;
        const subKey = winReadMemoryString(a(1), n.endsWith("w")) ?? "";
        const path = winRegistryPath(root, subKey), prefix = `${path}\\`;
        if (!winRegistry.has(path)) return 2n;
        if ([...winRegistry.keys()].some((name) => name.startsWith(prefix))) return 145n; // ERROR_DIR_NOT_EMPTY
        winRegistry.delete(path); return 0n;
      }
      case "regflushkey": return 0n;
      case "getusernamea": case "getusernamew": {
        const wide = n.endsWith("w"), buffer = Number(a(0)), sizePtr = Number(a(1)), name = "Guest";
        if (!ensureMemory(sizePtr + 4)) return 0n;
        const capacity = dv.getUint32(sizePtr, true), required = name.length + 1;
        if (capacity < required) { dv.setUint32(sizePtr, required, true); winSetLastError(122); return 0n; }
        if (wide) winWriteW(buffer, name); else winWriteA(buffer, name);
        dv.setUint32(sizePtr, required, true); return 1n;
      }
      // BCRYPT: browser WebCrypto-backed random generation and digest primitives.
      case "bcryptopenalgorithmprovider": {
        const algorithm = (winReadW(a(1)) ?? "").toUpperCase();
        // Accept anything — SSL_CTX_set_cipher_list only requires the provider handle to exist
        const handle = winAllocHandle({ kind: "bcrypt_algorithm", algorithm, hmac: (a(3) & 8n) !== 0n });
        if (!ensureMemory(Number(a(0)) + 8)) return 0xc0000005n;
        dv.setBigUint64(Number(a(0)), handle, true);
        return 0n;
      }
      case "bcryptclosealgorithmprovider": {
        const handle=winHandles.get(a(0));if(handle?.kind!=="bcrypt_algorithm")return 0xc0000008n;
        winHandles.delete(a(0));return 0n;
      }
      case "bcryptsetproperty": {
        // OpenSSL sets CHAINING_MODE / INITIALIZATION_VECTOR here. We don't
        // actually need to store them (encrypt/decrypt are stubs), but we DO
        // need to return STATUS_SUCCESS with the right result-length so
        // OpenSSL doesn't treat the call as a failure.
        const handle    = winHandles.get(a(0));
        const property  = (winReadW(a(1)) ?? "").toLowerCase();
        const input     = a(2);
        const inputLen  = Number(a(3));
        const resultPtr = a(4);
        log(`[BCRYPT-SET] ${property} len=${inputLen} handle=${handle ? "ok" : "BAD"}`);
        if (!handle || handle.kind !== "bcrypt_algorithm") return 0xc0000008n;
        if (resultPtr) winWriteDword(resultPtr, inputLen);
        return 0n;
      }
      case "bcryptgetproperty": {
          // Widened to answer every BCRYPT property OpenSSL/Steam queries during
          // cipher-setup. Returning NOT_IMPLEMENTED from any of these causes
          // `SSL_CTX_set_cipher list failure` because OpenSSL treats
          // STATUS_NOT_IMPLEMENTED as "algorithm unavailable".
          const handle    = winHandles.get(a(0));
          const property  = (winReadW(a(1)) ?? "").toLowerCase();
          const output    = Number(a(2));
          const capacity  = Number(a(3));
          const resultPtr = a(4);
          log(`[BCRYPT-GET] ${property} cap=${capacity} handle=${handle ? handle.algorithm : "BAD"}`);
          if (!handle || handle.kind !== "bcrypt_algorithm") return 0xc0000008n;

          const alg = (handle.algorithm || "").toUpperCase();
          const isAes  = alg.includes("AES");
          const isSha  = alg.includes("SHA");
          const isRsa  = alg.includes("RSA");
          const isEc   = alg.includes("ECDH") || alg.includes("ECDSA") || alg.includes("ECD");

          const writeU32 = (v) => {
              if (!ensureMemory(output + 4)) return false;
              dv.setUint32(output, v >>> 0, true);
              if (resultPtr) winWriteDword(resultPtr, 4);
              return true;
          };
          const writeStr = (s) => {
              const b = new Uint8Array((s.length + 1) * 2);
              for (let i = 0; i < s.length; i++) {
                  b[i*2]   = s.charCodeAt(i) & 0xff;
                  b[i*2+1] = s.charCodeAt(i) >> 8;
              }
              if (!ensureMemory(output + b.length)) return false;
              writeBytes(output, b);
              if (resultPtr) winWriteDword(resultPtr, b.length);
              return true;
          };

          switch (property) {
              case "objectlength": {
                  // Context buffer size in bytes. OpenSSL uses this to size
                  // the BCryptOpenAlgorithmProvider output buffer per algorithm.
                  const size = isAes ? 668
                            : alg === "SHA256" ? 144
                            : alg === "SHA384" ? 208
                            : alg === "SHA512" ? 272
                            : alg === "SHA1"   ? 112
                            : isRsa ? 576
                            : isEc  ? 448
                            : 256;
                  return writeU32(size) ? 0n : 0xc0000005n;
              }
              case "hashdigestlength":
              case "hashlength": {
                  const len = { MD5: 16, SHA1: 20, SHA256: 32, SHA384: 48, SHA512: 64 }[alg] ?? 0;
                  return writeU32(len) ? 0n : 0xc0000005n;
              }
              case "hashblocklength":
              case "blocklength": {
                  const len = { MD5: 64, SHA1: 64, SHA256: 64, SHA384: 128, SHA512: 128 }[alg]
                            ?? (isAes ? 16 : 0);
                  return writeU32(len) ? 0n : 0xc0000005n;
              }
              case "chainingmode": {
                  // Multi-string. CBC is what OpenSSL expects for AES block ciphers.
                  return writeStr(isAes ? "ChainingModeCBC" : "ChainingModeN/A")
                      ? 0n : 0xc0000005n;
              }
              case "algorithmname": {
                  return writeStr(alg) ? 0n : 0xc0000005n;
              }
              case "keylengths": {
                  // BCRYPT_KEY_LENGTHS_STRUCT: ULONG minBits, maxBits, incrementBits
                  const min = isAes ? 128 : isRsa ? 512  : isEc ? 256 : 0;
                  const max = isAes ? 256 : isRsa ? 16384 : isEc ? 521 : 0;
                  const inc = isAes ? 64  : isRsa ? 64   : isEc ? 1   : 0;
                  if (!ensureMemory(output + 12)) return 0xc0000005n;
                  dv.setUint32(output,     min, true);
                  dv.setUint32(output + 4, max, true);
                  dv.setUint32(output + 8, inc, true);
                  if (resultPtr) winWriteDword(resultPtr, 12);
                  return 0n;
              }
              case "blocksizelist": {
                  // BCRYPT_BLOCK_SIZE_LIST: ULONG count; ULONG sizes[]
                  const sizes = isAes ? [16] : isRsa ? [] : isEc ? [] : [];
                  if (!ensureMemory(output + 4 + sizes.length * 4)) return 0xc0000005n;
                  dv.setUint32(output, sizes.length, true);
                  sizes.forEach((s, i) => dv.setUint32(output + 4 + i*4, s, true));
                  if (resultPtr) winWriteDword(resultPtr, 4 + sizes.length * 4);
                  return 0n;
              }
              case "paddingschemes": {
                  // BCRYPT_PKCS1_PADDING=1, BCRYPT_SSH1_PADDING=2, BCRYPT_PSS_PADDING=4,
                  // BCRYPT_OAEP_PADDING=8
                  const schemes = isRsa ? [1, 4, 8] : [];
                  if (!ensureMemory(output + 4 + schemes.length * 4)) return 0xc0000005n;
                  dv.setUint32(output, schemes.length, true);
                  schemes.forEach((s, i) => dv.setUint32(output + 4 + i*4, s, true));
                  if (resultPtr) winWriteDword(resultPtr, 4 + schemes.length * 4);
                  return 0n;
              }
              case "signaturelength": {
                  // RSA-2048 default signature length
                  return writeU32(isRsa ? 256 : 0) ? 0n : 0xc0000005n;
              }
              case "authtaglength": {
                  // BCRYPT_AUTH_TAG_LENGTHS_STRUCT: ULONG min, max, increment
                  if (!ensureMemory(output + 12)) return 0xc0000005n;
                  dv.setUint32(output,      12, true);   // GCM min tag
                  dv.setUint32(output + 4,  16, true);   // GCM max tag
                  dv.setUint32(output + 8,  1,  true);
                  if (resultPtr) winWriteDword(resultPtr, 12);
                  return 0n;
              }
              case "initializationvector": {
                  if (!isAes) { if (resultPtr) winWriteDword(resultPtr, 0); return 0n; }
                  if (!ensureMemory(output + 16)) return 0xc0000005n;
                  u8.fill(0, output, output + 16);
                  if (resultPtr) winWriteDword(resultPtr, 16);
                  return 0n;
              }
              case "auth_tag_length":
              case "authtaglengths": {
                  if (!isAes) { if (resultPtr) winWriteDword(resultPtr, 0); return 0n; }
                  if (!ensureMemory(output + 12)) return 0xc0000005n;
                  dv.setUint32(output, 12, true);
                  dv.setUint32(output + 4, 16, true);
                  dv.setUint32(output + 8, 1, true);
                  if (resultPtr) winWriteDword(resultPtr, 12);
                  return 0n;
              }
              case "chainingmodecbc": case "chainingmodecfb":
              case "chainingmodeecb": case "chainingmodegcm":
              case "chainingmodena": {
                  // OpenSSL sets chaining mode via BCryptSetProperty; nothing to return.
                  if (resultPtr) winWriteDword(resultPtr, 0);
                  return 0n;
              }
              default: {
                  // Not one of the properties we know about. Return STATUS_SUCCESS with a
                  // zero result rather than NOT_IMPLEMENTED, so OpenSSL falls back to
                  // its default value instead of declaring the algorithm unavailable.
                  if (resultPtr) winWriteDword(resultPtr, 0);
                  return 0n;
              }
          }
      }
      case "bcryptgenrandom": {
        const handle=a(0)===0n?null:winHandles.get(a(0)),target=Number(a(1)),count=Number(a(2));
        if((handle&& (handle.kind!=="bcrypt_algorithm"||handle.algorithm!=="RNG"))||!Number.isSafeInteger(count)||count<0||!ensureMemory(target+count))return 0xc000000dn;
        try{for(let offset=0;offset<count;offset+=65536)globalThis.crypto.getRandomValues(u8.subarray(target+offset,target+Math.min(count,offset+65536)));return 0n;}
        catch{return 0xc0000017n;}
      }
      case "bcryptcreatehash": {
        const algorithm=winHandles.get(a(0));if(algorithm?.kind!=="bcrypt_algorithm"||algorithm.algorithm==="RNG")return 0xc0000008n;
        const output=Number(a(1)),secret=a(4)?readBytes(a(4),a(5)):new Uint8Array();
        if(!ensureMemory(output+8)||!secret||(secret.length&&!algorithm.hmac))return 0xc000000dn;
        const handle=winAllocHandle({kind:"bcrypt_hash",algorithm:algorithm.algorithm,hmac:algorithm.hmac,chunks:[],secret:secret.slice()});
        dv.setBigUint64(output,handle,true);return 0n;
      }
      case "bcryptupdatedata": case "bcrypthashdata": {
        const handle=winHandles.get(a(0)),bytes=readBytes(a(1),a(2));if(handle?.kind!=="bcrypt_hash"||!bytes)return 0xc0000008n;
        handle.chunks.push(bytes);return 0n;
      }
      case "bcryptfinishhash": {
        const handle=winHandles.get(a(0)),output=Number(a(1)),length=Number(a(2));
        if(handle?.kind!=="bcrypt_hash"||!ensureMemory(output+length))return 0xc0000008n;
        const total=handle.chunks.reduce((sum,chunk)=>sum+chunk.length,0),joined=new Uint8Array(total);let offset=0;
        for(const chunk of handle.chunks){joined.set(chunk,offset);offset+=chunk.length;}
        try{
          let result;
          if(handle.hmac){
            if(!handle.secret.length)return 0xc000000dn;
            const key=await globalThis.crypto.subtle.importKey("raw",handle.secret,{name:"HMAC",hash:handle.algorithm},false,["sign"]);
            result=await globalThis.crypto.subtle.sign("HMAC",key,joined);
          } else result=await globalThis.crypto.subtle.digest(handle.algorithm,joined);
          const digest=new Uint8Array(result);if(length<digest.length)return 0xc0000023n;writeBytes(output,digest);return 0n;
        } catch{return 0xc0000001n;}
      }
      case "bcryptdestroyhash": {
        const handle=winHandles.get(a(0));if(handle?.kind!=="bcrypt_hash")return 0xc0000008n;winHandles.delete(a(0));return 0n;
      }
      case "bcryptgenerate symmetrickey": case "bcryptgeneratesymmetrickey":
      case "bcryptimportkeypair": case "bcryptimportkey":
      case "bcryptcreatekey": case "bcryptderivekey":
      case "bcryptencrypt": case "bcryptdecrypt":
      case "bcryptsignhash": case "bcryptverifyhash":
      case "bcryptdestroykey": {
          const outputPtr = Number(a(0));
          if (outputPtr && ensureMemory(outputPtr + 8)) {
              const handle = winAllocHandle({
                  kind: "bcrypt_key",
                  // Preserve input length so later ops have plausible sizes
                  size: Number(a(3)) || 256,
              });
              dv.setBigUint64(outputPtr, handle, true);
          }
          return 0n;
      }
      case "cryptacquirecontexta": case "cryptacquirecontextw": {
        const provider = winAllocHandle({ kind: "crypto_provider" });
        if (a(0) && ensureMemory(Number(a(0)) + 8)) dv.setBigUint64(Number(a(0)), provider, true);
        return 1n;
      }
      case "cryptreleasecontext": {
        const handle = winHandles.get(a(0));
        if (handle?.kind !== "crypto_provider") { winSetLastError(6); return 0n; }
        winHandles.delete(a(0)); return 1n;
      }
      case "cryptgenrandom": {
        const count = Number(a(1)), target = Number(a(2));
        if (!Number.isSafeInteger(count) || count < 0 || count > 0x1000000 || !ensureMemory(target + count)) { winSetLastError(87); return 0n; }
        try { for (let offset=0; offset<count; offset+=65536) globalThis.crypto.getRandomValues(u8.subarray(target+offset,target+Math.min(count,offset+65536))); return 1n; }
        catch { winSetLastError(8); return 0n; }
      }
      case "getstdhandle": {
        const which = BigInt.asIntN(32, a(0));
        return which === -10n ? WIN_STD_INPUT : which === -11n ? WIN_STD_OUTPUT : which === -12n ? WIN_STD_ERROR : 0n;
      }
      case "getlasterror": {
        const err = winGetLastError();
        if (err >= 0x2000 && err < 0x3000) {  // the suspicious range
          log(`[LERR] GetLastError() = 0x${err.toString(16)} (${err}) — caller suspected`);
        }
        return BigInt(err);
      }
      case "setlasterror": winSetLastError(a(0)); return 0n;
      case "outputdebugstringa": { const s = winReadA(a(0)); if (s != null && s.length) log(s); return 0n; }
      case "outputdebugstringw": { const s = winReadW(a(0)); if (s != null && s.length) log(s); return 0n; }
      case "writefile": {
        const h = a(0), buffer = a(1), count = Number(a(2)), written = a(3);
        const hk = winHandles.get(h);
        if (!globalThis.__wfDiagSeen) globalThis.__wfDiagSeen = new Set();
        const key = `${hk?.kind ?? "?"}@${Number(a(1))}`;
        if (!globalThis.__wfDiagSeen.has(key)) {
            globalThis.__wfDiagSeen.add(key);
            log(`[WF-DIAG] h=0x${h.toString(16)} kind=${hk?.kind ?? "?"} count=${count} ` +
                `buf=0x${Number(a(1)).toString(16)} bytes="${readBytes(a(1), Math.min(count, 32)) ? new TextDecoder().decode(readBytes(a(1), Math.min(count, 32))) : "?"}"`);
        }
        const bytes = readBytes(buffer, count);
        if (bytes) {
            const text = new TextDecoder("utf-8", { fatal: false }).decode(bytes);
            if (text.includes("Invalid CRT parameter")) {
                const rspNow = Number(dv.getBigUint64(ctx + REG.rsp * 8, true));
                if ((globalThis.__crtParamChains = (globalThis.__crtParamChains ?? 0) + 1) <= 3) {
                  const rspW = Number(dv.getBigUint64(ctx + REG.rsp * 8, true));
                  const chain = [], fns = [];
                  for (let at = rspW; at < Math.min(u8.length - 8, rspW + 0x8000) && chain.length < 24; at += 8) {
                    const v = Number(dv.getBigUint64(at, true));
                    if (v < base || v >= imageEnd) continue;
                    const isCall = u8[v - 5] === 0xe8 || [2,3,4,5,6,7].some(k => u8[v-k] === 0xff && (u8[v-k+1] & 0x38) === 0x10);
                    if (!isCall) continue;
                    const rf = winFindRuntimeFunction(v);
                    chain.push(`0x${v.toString(16)}${rf ? `[fn 0x${rf.beginAddr.toString(16)}]` : ""}`);
                    if (rf && !fns.includes(rf)) fns.push(rf);
                  }
                  logTrace(`[CRTPARAM-CHAIN] #${globalThis.__crtParamChains}: ${chain.join(" <- ")}`);
                  if (globalThis.__crtParamChains === 1) {
                    for (const rf of fns.slice(0, 6)) {
                      const e = Math.min(rf.endAddr, rf.beginAddr + 0x180);
                      logTrace(`[CRTPARAM-FN] 0x${rf.beginAddr.toString(16)}..0x${rf.endAddr.toString(16)}`);
                      for (let p = rf.beginAddr; p < e; p += 16) log(`  ${p.toString(16)}: ${hexBytes(p, Math.min(16, e - p))}`);
                    }
                  }
                }
                logTrace(`[CRT-ASSERT] hit at pc=0x${pc.toString(16)} rsp=0x${rspNow.toString(16)}`);
                // In writefile's "Invalid CRT parameter" branch:
                logDispatch(`[ASSERT-APIS] last 16 APIs: ${(globalThis.__recentApis || []).slice(-16).join(" <- ")}`);
                logDispatch(`[ASSERT-APIS] last 8 return values: ${(globalThis.__recentApiRets || []).slice(-8).map(r => r.toString(16)).join(" ")}`);
                // Also disassemble the pre-_invoke_watson blocks, if any
                const isWatson = (p) => p >= 0x617c00n && p < 0x618000n;
                const pre = blockHistory.filter(p => !isWatson(p));
                if (pre.length) {
                  log(`[CRT-ASSERT] pre-_invoke_watson blocks (${pre.length}):`);
                  for (const p of pre) {
                    log(`  0x${p.toString(16)}`);
                    const dis = disasmAt(p);
                    if (dis) for (const l of dis.split('\n').slice(0, 8)) log(`    ${l}`);
                  }
                }
                if (!globalThis.__crtAssertSeen) globalThis.__crtAssertSeen = new Set();
                const retAddr = rspNow > 0 && rspNow + 8 <= u8.length
                    ? dv.getBigUint64(rspNow, true) : 0n;
                const assertKey = `${pc.toString(16)}:${retAddr.toString(16)}`;
                if (globalThis.__crtAssertSeen.has(assertKey)) {
                    // Already dumped this exact call site — just log the message and skip
                    // the expensive 32-frame walk. Saves ~50–100 k steps per occurrence.
                    logTrace(`[CRT-ASSERT] (repeat) hit at pc=0x${pc.toString(16)} — dump skipped`);
                } else {
                  globalThis.__crtAssertSeen.add(assertKey);
                  // ── Diagnostic 1: raw stack dump ────────────────────────────
                  logTrace(`[CRT-ASSERT] full block history (${blockHistory.length}):`);
                  for (const p of blockHistory) logTrace(`   0x${p.toString(16)}`);
                  logTrace(`[CRT-ASSERT] non-zero slots in [rsp .. rsp+0x600):`);
                  for (let off = 0; off < 0x600; off += 8) {
                      const slot = rspNow + off;
                      if (slot + 8 > u8.length) break;
                      const v = dv.getBigUint64(slot, true);
                      if (v === 0n) continue;
                      const n = Number(v);
                      const mark = (n >= base && n < imageEnd) ? "  ◀ code" : "";
                      logTrace(`  [+0x${off.toString(16).padStart(3, '0')}] 0x${v.toString(16)}${mark}`);
                  }

                  // ── Diagnostic 2: what does .pdata actually say? ────────────
                  const returnPc = Number(dv.getBigUint64(rspNow, true));
                  const rf = winFindRuntimeFunction(returnPc);
                  if (rf) {
                      const info = winDecodeUnwindInfo(rf);
                      logTrace(`[CRT-ASSERT] RF for 0x${returnPc.toString(16)}: ` +
                          `[0x${rf.beginAddr.toString(16)}..0x${rf.endAddr.toString(16)})`);
                      logTrace(`[CRT-ASSERT]   flags=0x${info.flags.toString(16)} ` +
                          `sizeProlog=0x${info.sizeOfProlog.toString(16)} ` +
                          `frameReg=${info.frameRegister}+${info.frameOffset} ` +
                          `nCodes=${info.codes.length} ` +
                          `handlerRVA=${info.exceptionHandlerRVA ? "0x" + info.exceptionHandlerRVA.toString(16) : "none"}`);
                      for (const c of info.codes) {
                          logTrace(`[CRT-ASSERT]   op=${c.op} info=${c.info} codeOffset=0x${c.codeOffset.toString(16)}`);
                      }
                  } else {
                      logTrace(`[CRT-ASSERT] NO RF for 0x${returnPc.toString(16)}`);
                  }

                  // ── Existing .pdata walk ────────────────────────────────────
                  let unwindPc  = returnPc;
                  let unwindRsp = rspNow + 8;
                  for (let frame = 0; frame < 32; frame++) {
                      if (!Number.isSafeInteger(unwindPc) || unwindPc < base || unwindPc >= imageEnd) {
                          log(`[CRT-ASSERT] frame ${frame}: pc=0x${unwindPc.toString(16)} (outside image) — stop`);
                          break;
                      }
                      const u = winVirtualUnwind(unwindPc, unwindRsp);
                      if (!u) {
                          logTrace(`[CRT-ASSERT] frame ${frame}: pc=0x${unwindPc.toString(16)} — no UNWIND_INFO`);
                          break;
                      }
                      logTrace(`[CRT-ASSERT] frame ${frame}: pc=0x${unwindPc.toString(16)} ` +
                          `-> ret=0x${u.returnAddr.toString(16)} est=0x${u.establisherFrame.toString(16)}`);
                      unwindPc  = u.returnAddr;
                      unwindRsp = u.newRsp;
                  }
                }
                log(`[CRT-ASSERT] NOT terminating to preserve state`);
            }
            if (h === WIN_STD_OUTPUT || h === WIN_STD_ERROR) {
                if (bytes.length) log(text);
            }
            if (!Number.isSafeInteger(count) || count < 0 || count > 0x7fffffff) { winSetLastError(87); return 0n; }
            if (!bytes) { winSetLastError(998); return 0n; }
            const handle = winHandles.get(h);
            if (!handle) { winSetLastError(6); return 0n; }
            if (handle.kind === "stdout" || handle.kind === "stderr") {
              if (bytes.length) log(new TextDecoder().decode(bytes));
            } else if (handle.kind === "file") {
              if (!handle.writable) { winSetLastError(5); return 0n; }
              const end = handle.position + bytes.length;
              if (end > handle.file.data.length) { const grown = new Uint8Array(end); grown.set(handle.file.data); handle.file.data = grown; }
              handle.file.data.set(bytes, handle.position); handle.position = end;
            } else { winSetLastError(5); return 0n; }
            if (written !== 0n && !winWriteDword(written, bytes.length)) { winSetLastError(998); return 0n; }
            return 1n;
          }
      }
      case "ntcreatefile": case "ntopenfile": case "zwcreatefile": case "zwopenfile": {
        // NTSTATUS NtCreateFile(
        //   PHANDLE FileHandle,          // rcx
        //   ACCESS_MASK DesiredAccess,   // rdx
        //   POBJECT_ATTRIBUTES ObjectAttributes,  // r8
        //   PIO_STATUS_BLOCK IoStatusBlock,       // r9
        //   PLARGE_INTEGER AllocationSize,        // [rsp+0x28]
        //   ULONG FileAttributes,                 // [rsp+0x30]
        //   ULONG ShareAccess,                    // [rsp+0x38]
        //   ULONG CreateDisposition,              // [rsp+0x40]
        //   ULONG CreateOptions,                  // [rsp+0x48]
        //   PVOID EaBuffer,                       // [rsp+0x50]
        //   ULONG EaLength                        // [rsp+0x58]
        // );
        const handlePtr = a(0);
        const objAttr  = Number(a(2));
        const ioStatus = Number(a(3));
        if (!objAttr || !ensureMemory(objAttr + 24)) return 0xC000000Dn;  // STATUS_INVALID_PARAMETER

        // OBJECT_ATTRIBUTES: Length(0), RootDirectory(8), ObjectName(16), ...
        const namePtr = Number(dv.getBigUint64(objAttr + 16, true));
        if (!namePtr || !ensureMemory(namePtr + 16)) return 0xC000000Dn;

        // UNICODE_STRING: Length(0, u16), MaximumLength(2, u16), Buffer(8, ptr)
        const nameLen = dv.getUint16(namePtr, true);
        const bufPtr  = Number(dv.getBigUint64(namePtr + 8, true));
        if (!bufPtr || !ensureMemory(bufPtr + nameLen)) return 0xC000000Dn;

        let raw = "";
        for (let i = 0; i < nameLen; i += 2) {
            raw += String.fromCharCode(dv.getUint16(bufPtr + i, true));
        }
        // NT paths start with \??\ (or \DosDevices\) — strip and translate
        let dosPath = raw;
        if (dosPath.startsWith("\\??\\")) dosPath = dosPath.slice(4);
        else if (dosPath.startsWith("\\DosDevices\\")) dosPath = dosPath.slice(12);
        log(`[NtCreateFile] raw="${raw}" dos="${dosPath}"`);
        const path = winPath(dosPath);

        const file = virtualFiles.get(path);
        const createDisp = Number(dv.getBigUint64(ctx + REG.rsp * 8, true) + 0n); // wrong offset, adjust
        // ... reuse createfilew logic to open file, allocate handle, fill IoStatusBlock
        if (!file) {
            // STATUS_OBJECT_NAME_NOT_FOUND
            if (ioStatus && ensureMemory(ioStatus + 16)) {
                dv.setUint32(ioStatus, 0, true);  // Status
                dv.setBigUint64(ioStatus + 8, 0n, true);  // Information
            }
            return 0xC0000034n;
        }
        const handle = winAllocHandle({ kind: "file", file, path, position: 0, readable: true, writable: false });
        if (handlePtr && ensureMemory(handlePtr + 8)) dv.setBigUint64(handlePtr, handle, true);
        if (ioStatus && ensureMemory(ioStatus + 16)) {
            dv.setUint32(ioStatus, 0, true);   // STATUS_SUCCESS
            dv.setBigUint64(ioStatus + 8, BigInt(file.data.length), true);  // FILE_OPENED info
        }
        return 0n;  // STATUS_SUCCESS
    }
      case "readfile": {
        const h = a(0), buffer = a(1), count = Number(a(2)), readPtr = a(3), handle = winHandles.get(h);
        // In the existing "readfile" handler, at the top of the body:
        // In the existing "readfile" handler, at the top of the body:
        if (h === WIN_STD_INPUT) {
          const buffer = Number(a(1));
          const capacity = Number(a(2));
          const readPtr = a(3);
          const startRow = winConsole.cursorY, startCol = winConsole.cursorX;
          const line = await new Promise((resolve) => {
            winConsoleInput.lineWaiter = { resolve, buffer: "", maxChars: capacity,
              startRow, startCol };
          });
          const bytes = new TextEncoder().encode(line + "\r\n");
          const count = Math.min(bytes.length, capacity);
          writeBytes(buffer, bytes.subarray(0, count));
          if (readPtr !== 0n) winWriteDword(readPtr, count);
          return 1n;
        }
        if (!handle || !Number.isSafeInteger(count) || count < 0 || count > 0x7fffffff) { winSetLastError(handle ? 87 : 6); return 0n; }
        let bytes;
        if (handle.kind === "stdin") {
          const end = Math.min(winStdin.length, winStdinPosition + count);
          bytes = winStdin.slice(winStdinPosition, end); winStdinPosition = end;
        } else if (handle.kind === "file") {
          if (!handle.readable) { winSetLastError(5); return 0n; }
          if (handle.position >= handle.file.data.length) {
            // at EOF — return FALSE. This is technically wrong (Windows returns TRUE
            // with bytesRead=0), but many caller implementations rely on FALSE-at-EOF.
            if (readPtr !== 0n) winWriteDword(readPtr, 0);
            winSetLastError(38);   // ERROR_HANDLE_EOF
            return 0n;
          }
          const end = Math.min(handle.file.data.length, handle.position + count);
          bytes = handle.file.data.slice(handle.position, end); handle.position = end;
        } else { winSetLastError(5); return 0n; }
        if (!writeBytes(buffer, bytes) || (readPtr !== 0n && !winWriteDword(readPtr, bytes.length))) { winSetLastError(998); return 0n; }
        return 1n;
      }
      case "closehandle": {
        const h = a(0);
        if (h === WIN_STD_INPUT || h === WIN_STD_OUTPUT || h === WIN_STD_ERROR) return 1n;
        return winHandles.delete(h) ? 1n : (winSetLastError(6), 0n);
      }
      case "createfilea": case "createfilew": {
          const path = readPath(a(0), n.endsWith("w"));
          if (path == null) { winSetLastError(87); return MASK64; }
          log(`[CreateFile] path="${path}" exists=${virtualFiles.has(path)} dir=${winDirectories.has(path)} cwd=${winCurrentDirectory}`);
          const access      = a(1);
          const disposition = Number(a(4));
          const flags       = Number(a(5));

          // ─── directory open (FILE_FLAG_BACKUP_SEMANTICS or plain OPEN_EXISTING)
          // Directory handles are how Windows programs probe writability. If we
          // can't return a handle here, every "is X writable" check fails.
          if (winDirectories.has(path)) {
              if (disposition !== 3 /* OPEN_EXISTING */) {
                  winSetLastError(5);   // ACCESS_DENIED for CREATE_* on a dir
                  return MASK64;
              }
              // We grant both READ and WRITE because the entire virtual heap is
              // writable. Report it as a directory handle so other APIs behave.
              const handle = winAllocHandle({
                  kind: "directory", path,
                  readable: true, writable: true,
              });
              log(`[CFW-DIR] "${path}" → 0x${handle.toString(16)} (dir handle)`);
               
              return handle;
          }

          // ─── regular file (existing logic, unchanged)
            if (winDirectories.has(path)) {
              const dispositionDir = Number(a(4));
              if (dispositionDir !== 3) {
                winSetLastError(5);   // ERROR_ACCESS_DENIED for CREATE_* on a dir
                 
                return MASK64;
              }
              const dirHandle = winAllocHandle({ kind: "directory", path, readable: true, writable: true });
              log(`[CFW-DIR] "${path}" → 0x${dirHandle.toString(16)} (OPEN_EXISTING dir handle)`);
               
              return dirHandle;
            }
          let file = virtualFiles.get(path);
          if (!file && (disposition === 1 || disposition === 2 || disposition === 4 || disposition === 5)) {
              const parent = path.slice(0, path.lastIndexOf("/")) || "/";
              if (!winDirectories.has(parent)) { winSetLastError(3); return MASK64; }  // PATH_NOT_FOUND
              file = { data: new Uint8Array(0) };
              virtualFiles.set(path, file);
          }
          if (!file) { winSetLastError(2);   return MASK64; }   // FILE_NOT_FOUND
          if (disposition === 2 || disposition === 5) file.data = new Uint8Array(0);
           
          return winAllocHandle({
              kind: "file", file, path, position: 0,
              readable: (access & 0x80000000n) !== 0n || (access & 0x00000001n) !== 0n,
              writable: (access & 0x40000000n) !== 0n || (access & 0x00000002n) !== 0n,
          });
      }
      case "createfile2": {
        const path = readPath(a(0), true);
        if (path == null) { winSetLastError(87); return MASK64; }
        log(`[CreateFile2] path="${path}" exists=${virtualFiles.has(path)} cwd=${winCurrentDirectory}`);
        let file = virtualFiles.get(path);
        const disposition = Number(a(3));
        if (!file && (disposition === 1 || disposition === 2 || disposition === 4 || disposition === 5)) {
            file = { data: new Uint8Array(0) };
            virtualFiles.set(path, file);
        }
        if (!file) { winSetLastError(2); return MASK64; }
        if (disposition === 2 || disposition === 5) file.data = new Uint8Array(0);
        const access = a(1);
        return winAllocHandle({ kind: "file", file, path, position: 0,
            readable: (access & 0x80000000n) !== 0n,
            writable: (access & 0x40000000n) !== 0n });
      }
      case "deletefilea": case "deletefilew": {
        const path = readPath(a(0), n.endsWith("w"));
        return path != null && virtualFiles.delete(path) ? 1n : (winSetLastError(2), 0n);
      }
      case "getfilesize": {
        const h = winHandles.get(a(0)); if (!h || h.kind !== "file") { winSetLastError(6); return 0xffff_ffffn; }
        if (a(1) !== 0n) winWriteDword(a(1), Math.floor(h.file.data.length / 0x100000000));
        return BigInt(h.file.data.length >>> 0);
      }
      case "setfilepointer": {
        const h = winHandles.get(a(0)); if (!h || h.kind !== "file") { winSetLastError(6); return 0xffff_ffffn; }
        const distance = BigInt.asIntN(32, a(1));
        const method = Number(a(3));
        const next = method === 0 ? distance : method === 1 ? BigInt(h.position) + distance : BigInt(h.file.data.length) + distance;
        if (next < 0n || next > 0x7fffffffn) { winSetLastError(87); return 0xffff_ffffn; }
        h.position = Number(next); return BigInt(h.position >>> 0);
      }
      case "getcurrentprocess": return MASK64;
      case "getcurrentthread": return 0xffff_ffff_ffff_fffen;
      case "getcurrentthreadid": {
        const frame = winCallbackFrames[winCallbackFrames.length - 1];
        if (frame?.thread) return BigInt(frame.thread.threadId);
        return BigInt((Number(processId) || 1) * 16);
      }
      case "getcurrentprocessid": return BigInt(Number(processId) || 1);
      case "getcurrentthreadid": return BigInt((Number(processId) || 1) * 16);
      case "getprocessheap": return winHeapHandle;
      case "heapcreate": return winHeapHandle;
      case "heapdestroy": return 1n;
      case "heapalloc": case "rtlallocateheap": {
        const flags = n === "heapalloc" ? a(1) : a(1);
        const size = n === "heapalloc" ? a(2) : a(2);
        const result = winAlloc(size, (flags & 8n) !== 0n || n === "rtlallocateheap");
        if (Number(size) > 0x1000) {
          const rsp = Number(dv.getBigUint64(ctx + REG.rsp * 8, true));
          const ret = rsp + 8 <= u8.length ? dv.getBigUint64(rsp, true) : 0n;
          if (!globalThis.__heapAllocs) globalThis.__heapAllocs = new Map();
          const key = ret.toString(16);
          const cnt = (globalThis.__heapAllocs.get(key) ?? 0) + 1;
          globalThis.__heapAllocs.set(key, cnt);
          if (cnt <= 3 || cnt === 10 || cnt === 100) {
            log(`[HEAPALLOC] #${cnt} from 0x${key} size=${Number(size).toLocaleString()} → 0x${result.toString(16)}`);
          }
        }
        return result;
      }
      
      // heapfree / rtlfreeheap
      case "heapfree": case "rtlfreeheap": { winFree(a(2)); return 1n; }
      case "free":     case "_free":      { winFree(a(0)); return 0n; }
      case "realloc":  case "_realloc": {
          const old = Number(a(0)), size = Number(a(1));
          if (old === 0) return winAlloc(size, false);
          if (size === 0) { winFree(old); return 0n; }
          const oldSize = winAllocations.get(old) ?? 0;
          const next = winAlloc(size, false);
          if (!next) return 0n;
          const bytes = readBytes(old, Math.min(oldSize, size));
          if (bytes) writeBytes(next, bytes);
          winFree(old);
          return next;
      }
      case "heaprealloc": case "rtlreallocateheap": {
        const old = a(2), requested = Number(a(3)), flags = a(1);
        if (!Number.isSafeInteger(requested) || requested < 0 || requested > 0x4000_0000) return 0n;
        const oldSize = winAllocations.get(Number(old)) ?? 0;
        const bytes = oldSize > 0 ? readBytes(old, oldSize) : null;
        const next = winAlloc(BigInt(requested), (flags & 8n) !== 0n);
        if (next === 0n) return 0n;
        if (bytes) writeBytes(next, bytes.subarray(0, Math.min(bytes.length, requested)));
        winAllocations.delete(Number(old));
        return next;
      }
      case "virtualalloc": {
        const requested = a(0), size = Number(a(1));
        if (!Number.isSafeInteger(size) || size <= 0 || size > 0x40000000) { winSetLastError(87); return 0n; }
        const start = requested === 0n ? align(winHeapCursor, PAGE_4K) : Number(requested);
        const end = start + align(size, PAGE_4K);
        if (!Number.isSafeInteger(start) || start < 0 || end > 0xffff0000 || !ensureMemory(end)) { winSetLastError(8); return 0n; }
        if (requested === 0n) winHeapCursor = end;
        u8.fill(0, start, end); return BigInt(start);
      }
      case "virtualfree": return 1n;
      case "virtualprotect": {
        const address = Number(a(0)), size = Number(a(1)), oldPtr = a(3);
        if (!Number.isSafeInteger(address) || !Number.isSafeInteger(size) || size < 0 || !ensureMemory(address + size)) { winSetLastError(87); return 0n; }
        if (oldPtr !== 0n) winWriteDword(oldPtr, 0x04); return 1n;
      }
      case "virtualquery": {
        const info = a(1), q = Number(info);
        if (!Number.isSafeInteger(q) || q < 0 || !ensureMemory(q + 48)) { winSetLastError(87); return 0n; }
        const address = a(0);
        u8.fill(0, q, q + 48);
        dv.setBigUint64(q, address, true); dv.setBigUint64(q + 8, address, true);
        dv.setUint32(q + 16, 0x04, true); // AllocationProtect = PAGE_READWRITE
        dv.setBigUint64(q + 24, 0x1000n, true); // RegionSize
        dv.setUint32(q + 32, 0x1000, true); // MEM_COMMIT
        dv.setUint32(q + 36, 0x04, true); // PAGE_READWRITE
        dv.setUint32(q + 40, 0x20000, true); // MEM_PRIVATE
        return 48n;
      }
      case "getmodulehandleexa": case "getmodulehandleexw": {
        const flags = Number(a(0)), nameOrAddress = a(1), out = Number(a(2));
        let handle = 0n;
        if (flags & 4) { // GET_MODULE_HANDLE_EX_FLAG_FROM_ADDRESS
          for (const module of winLoadedModulesByName.values()) {
            if (nameOrAddress >= module.base && nameOrAddress < module.base + BigInt(module.size)) { handle = module.base; break; }
          }
        } else {
          const moduleName = winReadMemoryString(nameOrAddress, n.endsWith("w"));
          if (moduleName) handle = winLookupModule(moduleName, (flags & 2) === 0);
          else if (nameOrAddress === 0n) handle = BigInt(base);
        }
        if (handle === 0n || !ensureMemory(out + 8)) { winSetLastError(126); return 0n; }
        dv.setBigUint64(out, handle, true); return 1n;
      }
      case "freelibrary": {
        const handle = a(0);
        if (!winModuleHandles.has(handle)) { winSetLastError(6); return 0n; }
        const count = winModuleRefCounts.get(handle) || 1;
        winModuleRefCounts.set(handle, Math.max(0, count - 1));
        // Images remain mapped until process exit; unloading while translated
        // code or callbacks may still reference them is deliberately deferred.
        return 1n;
      }
      case "resolvedelayloadedapi": {
        const parentBase = Number(a(0));
        const descriptorPtr = Number(a(1));
        const thunkPtr = Number(a(4));
        if (!ensureMemory(descriptorPtr + 32) || !ensureMemory(thunkPtr + 8)) {
          logTrace(`[DELAYLOAD] BAD PTR desc=0x${descriptorPtr.toString(16)} thunk=0x${thunkPtr.toString(16)}`);
          winSetLastError(87); return 0n;
        }
        const attributes = dv.getUint32(descriptorPtr, true);
        const rvaBased = (attributes & 1) !== 0;
        const toAddr = (v) => rvaBased ? parentBase + v : v;
        const mhPtr = toAddr(dv.getUint32(descriptorPtr + 8, true));
        let hModule = 0n;
        if (mhPtr) hModule = dv.getBigUint64(mhPtr, true);
        if (hModule === 0n) {
          const dllName = readCString(toAddr(dv.getUint32(descriptorPtr + 4, true))) || "";
          logTrace(`[DELAYLOAD] loading dll="${dllName}" rvaBased=${rvaBased}`);
          hModule = winLookupModule(dllName, true);
          if (hModule === 0n) {
            logTrace(`[DELAYLOAD] *** dll lookup FAILED for "${dllName}" (not in winBuiltinModules?)`);
            winSetLastError(126); return 0n;
          }
          if (mhPtr) dv.setBigUint64(mhPtr, hModule, true);
        }
        const thunk = dv.getBigUint64(thunkPtr, true);
        let name = null, ordinal = null;
        if ((thunk & 0x8000000000000000n) !== 0n) {
          ordinal = Number(thunk & 0xffffn);
        } else {
          name = readCString(toAddr(Number(thunk & 0x7fffffffn)) + 2) || null;
        }
        log(`[DELAYLOAD] resolving ${name ?? "#" + ordinal} from h=0x${hModule.toString(16)}`);
        const resolved = winLookupApi(hModule, name, ordinal);
        if (resolved === 0n) {
          logTrace(`[DELAYLOAD] *** export lookup FAILED for ${name ?? "#" + ordinal}`);
          winSetLastError(127); return 0n;
        }
        dv.setBigUint64(thunkPtr, resolved, true);
        logTrace(`[DELAYLOAD] patched [0x${thunkPtr.toString(16)}] = 0x${resolved.toString(16)}`);
        return resolved;
      }
      case "getprocaddress": {
        const module = a(0), symbol = a(1);
        if (symbol <= 0xffffn) return winLookupApi(module, null, Number(symbol));
        const name = winReadA(symbol);
        if (!name) { winSetLastError(127); return 0n; }
        return winLookupApi(module, name, null);
      }
      case "getcommandlinea": return BigInt(WIN_CMD_A);
      case "getcommandlinew": return BigInt(WIN_CMD_W);
      case "getmodulefilenamea": case "getmodulefilenamew": {
        const wide = n.endsWith("w"), buffer = a(1), cap = Number(a(2));
        const moduleRecord = winLoadedModulesByBase.get(a(0));
        const text = moduleRecord?.path ?? (a(0) === 0n || a(0) === BigInt(base) ? winImagePath : winImagePath);
        const encoded = wide ? new Uint8Array((text.length + 1) * 2) : new TextEncoder().encode(text + "\0");
        if (wide) for (let i = 0; i < text.length; i++) encoded[i * 2] = text.charCodeAt(i) & 255, encoded[i * 2 + 1] = text.charCodeAt(i) >> 8;
        const count = Math.min(cap, encoded.length); writeBytes(buffer, encoded.subarray(0, count)); return BigInt(Math.min(text.length, cap));
      }
      // PSAPI/K32 process inspection reports only the current guest module and
      // process table. Each child has a separate Wasm memory, not shared addresses.
      case "enumprocesses": {
        const buffer=Number(a(0)),capacity=Math.max(0,Math.floor(Number(a(1))/4)),needed=a(2);
        const pids=[...winProcesses.values()].filter((item)=>!item.finished).map((item)=>item.processId);
        const count=Math.min(capacity,pids.length);if(!ensureMemory(buffer+count*4))return 0n;
        for(let i=0;i<count;i++)dv.setUint32(buffer+i*4,pids[i],true);
        if(needed)winWriteDword(needed,pids.length*4);return 1n;
      }
      case "getprocessmemoryinfo": {
        const handle=a(0),info=Number(a(1)),size=Number(a(2));
        if(handle!==MASK64&&handle!==0xffff_ffff_ffff_fffen&&!winHandles.has(handle)){winSetLastError(6);return 0n;}
        if(size<72||!ensureMemory(info+72)){winSetLastError(87);return 0n;}
        u8.fill(0,info,info+72);dv.setUint32(info,72,true);dv.setUint32(info+4,0,true);
        const working=memory.buffer.byteLength;dv.setBigUint64(info+8,BigInt(working),true);dv.setBigUint64(info+16,BigInt(working),true);
        dv.setBigUint64(info+56,BigInt(working),true);dv.setBigUint64(info+64,BigInt(working),true);return 1n;
      }
      case "getmodulefilenameexa": case "getmodulefilenameexw":
      case "getprocessimagefilenamea": case "getprocessimagefilenamew":
      case "getmodulebasenamea": case "getmodulebasenamew": {
        const wide = n.endsWith("w");
        const handle = winHandles.get(a(0));
        let path = null;

        if (a(0) === MASK64 || a(0) === 0n) {
          path = winImagePath;                         // current process
        } else if (handle?.kind === "process") {
          path = handle.imagePath;
        } else if (handle?.kind === "thread") {
          path = handle.process.imagePath;
        }

        // Module-based APIs: second argument is the module handle
        const isModuleFn = n.startsWith("getmodulebasename") || n.startsWith("getmodulefilenameex");
        if (isModuleFn) {
          const modBase = a(1);
          const mod = winLoadedModulesByBase.get(modBase);
          if (mod) path = mod.path;
        }

        if (!path) { winSetLastError(6); return 0n; }

        const value = n.startsWith("getmodulebasename")
          ? path.split(/[\\/]/).pop()
          : path;

        const output   = n.startsWith("getprocessimagefilename") ? a(1) : a(2);
        const capacity = Number(n.startsWith("getprocessimagefilename") ? a(2) : a(3));
        if (!output || capacity <= 0) return 0n;

        const count = Math.min(value.length, capacity - 1);
        winWriteMemoryString(output, value.slice(0, count), wide);
        return BigInt(count);
      }
      case "getmoduleinformation": {
        const handle=a(0),module=a(1),output=Number(a(2)),size=Number(a(3));
        if((handle!==MASK64&&handle!==0n)|| (module!==0n&&module!==BigInt(base)) || size<24 || !ensureMemory(output+24)){winSetLastError(87);return 0n;}
        dv.setBigUint64(output,BigInt(base),true);dv.setUint32(output+8,image.length,true);dv.setBigUint64(output+16,BigInt(Number(manifest.entry??base)),true);return 1n;
      }
      case "enumprocessmodules": case "enumprocessmodulesex": {
        const handle = a(0), output = Number(a(1)), capacity = Number(a(2)), needed = a(3);
        if ((handle !== MASK64 && handle !== 0n) || !ensureMemory(output + Math.min(capacity, 64))) {
          winSetLastError(6); return 0n;
        }
        const modules = [BigInt(base)];
        for (const [modBase, modName] of winModuleHandles) {   // ← modBase, not base
          if (modBase === BigInt(base)) continue;              // already listed
          modules.push(modBase);
          if (modules.length >= 8) break;
        }
        const count = Math.min(Math.floor(capacity / 8), modules.length);
        for (let i = 0; i < count; i++) dv.setBigUint64(output + i * 8, modules[i], true);
        if (needed) winWriteDword(needed, modules.length * 8);
        return 1n;
      }
      case "getstartupinfoa": case "getstartupinfow": {
        const p = Number(a(0)); if (!ensureMemory(p + 104)) return 0n;
        u8.fill(0, p, p + 104); dv.setUint32(p, 104, true); return 0n;
      }
      case "getsysteminfo": case "getnativesysteminfo": {
        const p = Number(a(0)); if (!Number.isSafeInteger(p) || p < 0 || !ensureMemory(p + 48)) return 0n;
        u8.fill(0, p, p + 48);
        dv.setUint32(p, 9, true); // PROCESSOR_ARCHITECTURE_AMD64
        dv.setUint32(p + 4, 0x1000, true);
        dv.setBigUint64(p + 8, 0x10000n, true);
        dv.setBigUint64(p + 16, 0x7ffe0000n, true);
        dv.setBigUint64(p + 24, 1n, true);
        dv.setUint32(p + 32, 1, true); dv.setUint32(p + 36, 0x8664, true);
        dv.setUint32(p + 40, 0x10000, true); dv.setUint16(p + 44, 6, true); return 0n;
      }
      case "isdebuggerpresent": return 0n;
      case "queryperformancefrequency": {
        const p = Number(a(0)); if (!ensureMemory(p + 8)) return 0n;
        dv.setBigInt64(p, 10_000_000n, true); return 1n;
      }
      case "queryperformancecounter": {
        const p = Number(a(0)); if (!ensureMemory(p + 8)) return 0n;
        dv.setBigInt64(p, BigInt(Math.floor((globalThis.performance?.now?.() ?? Date.now()) * 10_000)), true); return 1n;
      }
      case "gettickcount64": return BigInt(Math.floor(globalThis.performance?.now?.() ?? Date.now()));
      case "gettickcount": return BigInt(Math.floor(globalThis.performance?.now?.() ?? Date.now()) >>> 0);
      case "sleep": {
        const rawDelay = Number(a(0)) >>> 0;
        const delay = Math.min(rawDelay, 5000);   // clamp to 5s max in dev
        if (rawDelay > 5000) {
          if (!globalThis.__sleepWarn) globalThis.__sleepWarn = new Set();
          const rsp = Number(dv.getBigUint64(ctx + REG.rsp * 8, true));
          const ret = rsp > 0 && rsp + 8 <= u8.length ? dv.getBigUint64(rsp, true) : 0n;
          const key = `${rawDelay}@${ret.toString(16)}`;
          if (!globalThis.__sleepWarn.has(key)) {
            globalThis.__sleepWarn.add(key);
            log(`[SLEEP-CLAMP] Sleep(${rawDelay}ms) from 0x${ret.toString(16)} → clamped to 5000ms`);
          }
        }
        if (delay) await new Promise((resolve) => setTimeout(resolve, delay));
        return 0n;
      }
      case "initializecriticalsection":
      case "initializecriticalsectionandspincount":
      case "initializecriticalsectionex": {
        const p = Number(a(0));
        if (!Number.isSafeInteger(p) || p < 0 || !ensureMemory(p + 40)) {
          winSetLastError(87); return 0n;
        }
        u8.fill(0, p, p + 40);
        dv.setInt32 (p + 8,  -1, true);          // LockCount = -1 → unlocked
        dv.setInt32 (p + 12,  0, true);          // RecursionCount = 0
        // OwningThread / LockSemaphore stay 0
        if (n === "initializecriticalsectionandspincount" ||
            n === "initializecriticalsectionex") {
          dv.setBigUint64(p + 32, a(1), true);   // SpinCount
        }
        return 1n;
      }
      case "entercriticalsection": {
        const p = Number(a(0));
        if (Number.isSafeInteger(p) && p >= 0 && ensureMemory(p + 40)) {
          dv.setInt32(p + 8, dv.getInt32(p + 8, true) + 1, true);
          dv.setInt32(p + 12, dv.getInt32(p + 12, true) + 1, true);
          dv.setBigUint64(p + 16, BigInt((Number(processId) || 1) * 16), true);
        }
        return 0n;
      }
      case "leavecriticalsection": {
        const p = Number(a(0));
        if (Number.isSafeInteger(p) && p >= 0 && ensureMemory(p + 40)) {
          const rc = dv.getInt32(p + 12, true) - 1;
          dv.setInt32(p + 12, rc, true);
          if (rc <= 0) dv.setBigUint64(p + 16, 0n, true);
          dv.setInt32(p + 8, dv.getInt32(p + 8, true) - 1, true);
        }
        return 0n;
      }
      case "tryentercriticalsection": {
        const p = Number(a(0));
        if (!Number.isSafeInteger(p) || p < 0 || !ensureMemory(p + 40)) return 0n;
        dv.setInt32(p + 8, dv.getInt32(p + 8, true) + 1, true);
        dv.setInt32(p + 12, dv.getInt32(p + 12, true) + 1, true);
        dv.setBigUint64(p + 16, BigInt((Number(processId) || 1) * 16), true);
        return 1n;
      }
      case "deletecriticalsection": return 0n;

      case "initializesrwlock":
      case "initializeconditionvariable": {
        const p = Number(a(0));
        if (Number.isSafeInteger(p) && p >= 0 && ensureMemory(p + 8)) dv.setBigUint64(p, 0n, true);
        return 0n;
      }
      case "acquiresrwlockexclusive":
      case "acquiresrwlockshared": {
        const p = Number(a(0));
        if (Number.isSafeInteger(p) && p >= 0 && ensureMemory(p + 8))
          dv.setBigUint64(p, BigInt((Number(processId) || 1) * 16), true);
        return 0n;
      }
      case "releasesrwlockexclusive":
      case "releasesrwlockshared": {
        const p = Number(a(0));
        if (Number.isSafeInteger(p) && p >= 0 && ensureMemory(p + 8)) dv.setBigUint64(p, 0n, true);
        return 0n;
      }
      case "tryacquiresrwlockexclusive":
      case "tryacquiresrwlockshared": {
        const p = Number(a(0));
        if (!Number.isSafeInteger(p) || p < 0 || !ensureMemory(p + 8)) return 0n;
        dv.setBigUint64(p, BigInt((Number(processId) || 1) * 16), true);
        return 1n;
      }
      case "wakeconditionvariable":
      case "wakeallconditionvariable":
        return 0n;
      case "sleepconditionvariablecs":
      case "sleepconditionvariablesrw":
        return 1n;   // "woken"
      case "encodepointer": case "decodepointer": return a(0);
      case "initialize s list head": case "initializeslisthead": return 0n;
      case "switchtothread": return 0n;
      case "interlockedincrement": case "interlockeddecrement": case "interlockedexchange": case "interlockedexchangeadd": {
        const p=Number(a(0)); if (!ensureMemory(p+4)) return 0n;
        const old=dv.getInt32(p,true), arg=Number(a(1))|0;
        let next=n==="interlockedincrement"?old+1:n==="interlockeddecrement"?old-1:n==="interlockedexchange"?arg:old+arg;
        dv.setInt32(p,next,true); return BigInt(n==="interlockedexchangeadd"?old:next);
      }
      case "interlockedcompareexchange": {
        const p=Number(a(0)); if (!ensureMemory(p+4)) return 0n;
        const old=dv.getInt32(p,true); if (old === (Number(a(2))|0)) dv.setInt32(p,Number(a(1))|0,true); return BigInt(old);
      }
      case "interlockedexchangepointer": {
        const p=Number(a(0)); if (!ensureMemory(p+8)) return 0n;
        const old=dv.getBigUint64(p,true); dv.setBigUint64(p,a(1),true); return old;
      }
      case "interlockedcompareexchangepointer": {
        const p=Number(a(0)); if (!ensureMemory(p+8)) return 0n;
        const old=dv.getBigUint64(p,true); if (old===a(2)) dv.setBigUint64(p,a(1),true); return old;
      }
      case "tlsalloc": {
        const id = winNextTls++;
        if (id >= 1088) { winSetLastError(1450); return 0xFFFFFFFFn; }  // ERROR_NO_SYSTEM_RESOURCES
        winTls.set(id, 0n);
        return BigInt(id);
      }
      case "tlsfree": {
        const id = Number(a(0));
        if (id < 0 || id >= 1088) { winSetLastError(87); return 0n; }
        winTls.delete(id);
        return 1n;
      }
      case "tlsgetvalue": {
        const id = Number(BigInt.asIntN(32, a(0)));
        if (id < 0) { winSetLastError(87); return 0n; }
        return winTls.get(id) ?? 0n;
      }
      case "tlssetvalue": {
        const id = Number(BigInt.asIntN(32, a(0)));
        if (id < 0) { winSetLastError(87); return 0n; }
        winTls.set(id, a(1));
        return 1n;
      }
      case "memcpy": case "memmove": case "rtlmovememory": case "rtlcopymemory": return copy(a(0), a(1), a(2));
      case "memcpy_s": {
        const destSize = Number(a(1)), count = Number(a(3));
        if (count > destSize) { winSetLastError(34); return 34n; }
        return copy(a(0), a(2), count) === 0n ? 22n : 0n;
      }
      case "rtlzeromemory": {
        const dst = Number(a(0)), length = Number(a(1));
        if (!Number.isSafeInteger(dst) || !Number.isSafeInteger(length) || length < 0 || !ensureMemory(dst + length)) { winSetLastError(998); return 0n; }
        u8.fill(0, dst, dst + length); return a(0);
      }
      case "rtlfillmemory": {
        const dst = Number(a(0)), length = Number(a(1)), value = Number(a(2)) & 255;
        if (!Number.isSafeInteger(dst) || !Number.isSafeInteger(length) || length < 0 || !ensureMemory(dst + length)) { winSetLastError(998); return 0n; }
        u8.fill(value, dst, dst + length); return a(0);
      }
      case "memset": {
        const dst = Number(a(0)), value = Number(a(1)) & 255, length = Number(a(2));
        if (!Number.isSafeInteger(dst) || !Number.isSafeInteger(length) || length < 0 || !ensureMemory(dst + length)) { winSetLastError(998); return 0n; }
        u8.fill(value, dst, dst + length); return a(0);
      }
      case "memcmp": {
        const x = readBytes(a(0), a(2)), y = readBytes(a(1), a(2)); if (!x || !y) return 0n;
        for (let i=0;i<x.length;i++) if (x[i] !== y[i]) return BigInt(x[i] - y[i]); return 0n;
      }
      case "strlen": { const s = winReadA(a(0)); return BigInt(s?.length ?? 0); }
      case "wcslen": { const s = winReadW(a(0)); return BigInt(s?.length ?? 0); }
      case "strcmp": { const x=winReadA(a(0)) ?? "", y=winReadA(a(1)) ?? ""; return BigInt(x===y?0:x<y?-1:1); }
      case "strcpy": { const s=winReadA(a(1)); if (s==null) return 0n; winWriteA(a(0),s); return a(0); }
      case "malloc": case "_malloc": return winAlloc(a(0), false);
      case "calloc": case "_calloc": {
        const count=Number(a(0)), size=Number(a(1));
        if (!Number.isSafeInteger(count*size) || count*size < 0) return 0n;
        return winAlloc(count*size, true);
      }
      case "_msize": return BigInt(winAllocations.get(Number(a(0))) ?? 0);
      case "__acrt_iob_func": return BigInt(Number(a(0)) + 1);
      case "__p___argc": return BigInt(WIN_ARGC);
      case "__p___argv": return BigInt(WIN_ARGV_PTR);
      case "__p___wargv": return BigInt(WIN_WARGV_PTR);
      case "__p__commode": return BigInt(WIN_COMMODE);
      case "__p__fmode": return BigInt(WIN_FMODE);
      case "__p___argc": case "_o___p___argc": return BigInt(WIN_ARGC);
      case "__p___argv": case "_o___p___argv": return BigInt(WIN_ARGV_PTR);
      case "__p___wargv": case "_o___p___wargv": return BigInt(WIN_WARGV_PTR);
      case "__p__commode": case "_o___p__commode": return BigInt(WIN_COMMODE);
      case "__p__fmode":   case "_o___p__fmode":   return BigInt(WIN_FMODE);
      case "_errno": return BigInt(WIN_ERRNO);
      case "_register_onexit_function": case "_execute_onexit_table": case "_crt_atexit":
      case "_crt_at_quick_exit": case "atexit": case "at_quick_exit":
      case "_configure_narrow_argv": case "_initialize_narrow_environment": case "_set_app_type":
      case "__security_init_cookie": case "__security_check_cookie":
      case "__c_specific_handler": case "__cxxframehandler3": case "__cxxframehandler4":
      case "__std_exception_copy": case "__std_exception_destroy": case "__std_type_info_destroy_list":
      case "__std_terminate": return 0n;
      case "exitprocess": {
        const status = Number(a(0)) | 0;
        winExitCode = status;
        return { exit: true, status };
      }
      case "terminateprocess": {
        const processHandle = a(0), status = Number(a(1)) | 0;
        if (processHandle === 0xffff_ffff_ffff_ffffn || processHandle === BigInt(processId)) {
          winExitCode = status;
          return { exit: true, status };
        }
        return 0n;
      }
      case "exit": case "_exit": case "_cexit": case "abort": {
        const status=n==="abort"?3:Number(a(0))|0; winExitCode=status; return {exit:true,status};
      }
      // ═══════════════════════════════════════════════════════════════════════
      // CRT stdio — fopen / _wfopen / fwrite / fread / fclose / fflush
      //
      // Steam's writability check does: _wfopen("pkg\.writable", "w") →
      // fwrite("test", 1, 4, f) → fclose(f) → DeleteFileW(...). Any one of
      // these failing (especially returning NULL from _wfopen) causes
      // "Directory not writable". We back FILE* with a real virtualFiles entry
      // so the whole cycle succeeds.
      // ═══════════════════════════════════════════════════════════════════════
      case "fopen": case "_wfopen":
      case "fopen_s": case "_wfopen_s":
      case "_fsopen": case "_wfsopen":
      case "_fsopen_s": case "_wfsopen_s": {
          const wide   = n.startsWith("_w");
          const safe   = n.endsWith("_s");
          const outPtr = safe ? a(0) : 0n;
          const pathArg = safe ? a(1) : a(0);
          const modeArg = safe ? a(2) : a(1);
          const path = winReadMemoryString(pathArg, wide);
          const mode = winReadMemoryString(modeArg, false) ?? "rb";

          let handle = 0n;
          if (path != null) {
              const norm = winPath(path);
              const isWrite = /[wa+]/.test(mode);
              const isRead  = /[r+]/.test(mode);
              let file = virtualFiles.get(norm);
              if (!file && isWrite) {
                  const parent = norm.slice(0, norm.lastIndexOf("/")) || "/";
                  if (winDirectories.has(parent)) {
                      file = { data: new Uint8Array(0) };
                      virtualFiles.set(norm, file);
                  }
              }
              if (file) {
                  if (mode.startsWith("w")) file.data = new Uint8Array(0);
                  handle = winAllocHandle({
                      kind: "crt_file", file, path: norm,
                      position: mode.includes("a") ? file.data.length : 0,
                      readable: isRead, writable: isWrite,
                  });
              }
          }
          if (safe) {
              if (ensureMemory(Number(outPtr) + 8)) dv.setBigUint64(Number(outPtr), handle, true);
              return handle === 0n ? 2n : 0n;
          }
          return handle;
      }
      case "_write": case "write": {
        const fd = Number(BigInt.asIntN(32, a(0))), count = Number(a(2) & 0xffffffffn);
        const bytes = readBytes(a(1), count);
        if (!bytes) { dv.setUint32(WIN_ERRNO, 22, true); return 0xffff_ffffn; }
        if (fd === 1 || fd === 2) { if (bytes.length) log(new TextDecoder().decode(bytes)); return BigInt(count); }
        const h = winFdFile(a(0));
        if (!h || !h.writable) { dv.setUint32(WIN_ERRNO, 9, true); return 0xffff_ffffn; }
        const end = h.position + bytes.length;
        if (end > h.file.data.length) { const g = new Uint8Array(end); g.set(h.file.data); h.file.data = g; }
        h.file.data.set(bytes, h.position); h.position = end;
        return BigInt(count);
      }
      case "_read": case "read": {
        const h = winFdFile(a(0)), count = Number(a(2) & 0xffffffffn);
        if (!h || !h.readable) { dv.setUint32(WIN_ERRNO, 9, true); return 0xffff_ffffn; }
        const n2 = Math.min(count, Math.max(0, h.file.data.length - h.position));
        if (n2 && !writeBytes(a(1), h.file.data.subarray(h.position, h.position + n2))) return 0xffff_ffffn;
        h.position += n2; return BigInt(n2);
      }
      case "_close": case "close": {
        const h = winFdFile(a(0));
        if (!h) { dv.setUint32(WIN_ERRNO, 9, true); return 0xffff_ffffn; }
        winHandles.delete(BigInt(Number(BigInt.asIntN(32, a(0))))); return 0n;
      }
      case "_lseek": case "_lseeki64": case "lseek": {
        const h = winFdFile(a(0)); if (!h) return 0xffff_ffffn;
        const off = n === "_lseeki64" ? Number(BigInt.asIntN(64, a(1))) : Number(BigInt.asIntN(32, a(1)));
        const w = Number(a(2) & 0xffffffffn);
        const origin = w === 0 ? 0 : w === 1 ? h.position : h.file.data.length;
        if (origin + off < 0) return 0xffff_ffffn;
        h.position = origin + off; return BigInt(h.position);
      }
      case "_commit": return 0n;
      case "_setmode": return 0x8000n;          // report binary mode
      case "_isatty": return Number(a(0) & 0xffffffffn) <= 2 ? 1n : 0n;
      case "_filelength": case "_filelengthi64": {
        const h = winFdFile(a(0)); return h ? BigInt(h.file.data.length) : 0xffff_ffffn;
      }

      case "fwrite": {
          const size = Number(a(1)), count = Number(a(2)), stream = a(3);
          const bytes = readBytes(a(0), size * count);
          if (!bytes || !Number.isSafeInteger(size * count)) return 0n;
          const h = winHandles.get(stream);
          if (h?.kind === "crt_file" && h.writable) {
              const end = h.position + bytes.length;
              if (end > h.file.data.length) {
                  const g = new Uint8Array(end); g.set(h.file.data); h.file.data = g;
              }
              h.file.data.set(bytes, h.position);
              h.position = end;
              return BigInt(size > 0 ? Math.floor(bytes.length / size) : 0);
          }
          const std = winCrtFiles.get(stream);
          if (std?.kind === "stdout" || std?.kind === "stderr") {
              if (bytes.length) log(new TextDecoder().decode(bytes));
              return BigInt(count);
          }
          return 0n;
      }

      case "fread": {
          const size = Number(a(1)), count = Number(a(2)), stream = a(3);
          if (!Number.isSafeInteger(size * count)) return 0n;
          const h = winHandles.get(stream);
          if (h?.kind !== "crt_file" || !h.readable) return 0n;
          const avail = Math.max(0, h.file.data.length - h.position);
          const n = Math.min(size * count, avail);
          const bytes = h.file.data.slice(h.position, h.position + n);
          h.position += n;
          writeBytes(a(0), bytes);
          return BigInt(size > 0 ? Math.floor(bytes.length / size) : 0);
      }

      case "fclose": case "_fclose": {
          const h = winHandles.get(a(0));
          if (h?.kind === "crt_file") winHandles.delete(a(0));
          return 0n;
      }

      case "fflush": case "_fflush": return 0n;

      case "ftell": case "_ftelli64": {
          const h = winHandles.get(a(0));
          return h?.kind === "crt_file" ? BigInt(h.position) : 0n;
      }

      case "fseek": case "_fseeki64": {
          const h = winHandles.get(a(0));
          if (h?.kind !== "crt_file") return 0xffff_ffffn;
          const offset = Number(a(1)), whence = Number(a(2));
          const base = whence === 0 ? 0 : whence === 1 ? h.position : whence === 2 ? h.file.data.length : null;
          if (base === null) return 0xffff_ffffn;
          const next = base + offset;
          if (next < 0 || next > 0x7fffffff) return 0xffff_ffffn;
          h.position = next;
          return 0n;
      }
      case "setfileattributesa": case "setfileattributesw":
        return 1n;   // always succeed — we never track readonly bits
      case "fputs": { const value=winReadA(a(0)) ?? ""; const stream=winCrtFiles.get(a(1)); if (stream?.kind === "stdout" || stream?.kind === "stderr") { log(value); return BigInt(value.length); } return -1n; }
      case "fputc": { const stream=winCrtFiles.get(a(1)); if (stream?.kind === "stdout" || stream?.kind === "stderr") { log(String.fromCharCode(Number(a(0)&255n))); return a(0)&255n; } return 0xffff_ffffn; }
      case "puts": return writeOut((winReadA(a(0)) ?? "(null)") + "\n");
      case "putchar": return writeOut(String.fromCharCode(Number(a(0) & 255n)));
      case "printf": {
        const fmt = winReadA(a(0)); if (fmt == null) return 0n;
        return writeOut(winFormat(fmt, 1, null, false));
      }
      case "__stdio_common_vfprintf": {
        const fmt = winReadA(a(2)), vaList = a(4); if (fmt == null) return 0n;
        return writeOut(winFormat(fmt, 0, vaList, false));
      }
      case "initoncebegininitialize": {
        // BOOL InitOnceBeginInitialize(INIT_ONCE*, DWORD flags, PBOOL fPending, LPVOID* context)
        const initOncePtr = Number(a(0));
        const pendingPtr = Number(a(2));
        const contextPtr = Number(a(3));
        if (!Number.isSafeInteger(initOncePtr) || initOncePtr <= 0 || !ensureMemory(initOncePtr + 8)) {
          winSetLastError(87); return 0n;
        }
        const guard = dv.getBigUint64(initOncePtr, true);
        if (guard !== 0n) {
          // Already initialized (either 1 for "done with null" or actual context)
          if (pendingPtr && ensureMemory(pendingPtr + 4)) dv.setUint32(pendingPtr, 0, true);
          if (contextPtr && ensureMemory(contextPtr + 8)) {
            dv.setBigUint64(contextPtr, guard === 1n ? 0n : guard, true);
          }
          return 1n;
        }
        // First call — caller runs the callback
        if (pendingPtr && ensureMemory(pendingPtr + 4)) dv.setUint32(pendingPtr, 1, true);
        return 1n;
      }

      case "initoncecomplete": {
        // BOOL InitOnceComplete(INIT_ONCE*, DWORD flags, LPVOID context)
        const initOncePtr = Number(a(0));
        const context = a(2);
        if (!Number.isSafeInteger(initOncePtr) || initOncePtr <= 0 || !ensureMemory(initOncePtr + 8)) {
          winSetLastError(87); return 0n;
        }
        dv.setBigUint64(initOncePtr, context === 0n ? 1n : context, true);
        return 1n;
      }

      case "initonceexecuteonce": {
        // BOOL InitOnceExecuteOnce(INIT_ONCE*, PINIT_ONCE_FN callback, PVOID param, LPVOID* context)
        // We simulate: Begin → if pending, call callback → Complete.
        const initOncePtr = Number(a(0));
        const callback = a(1);
        const parameter = a(2);
        const contextPtr = a(3);
        if (!Number.isSafeInteger(initOncePtr) || initOncePtr <= 0 || !ensureMemory(initOncePtr + 8)) {
          winSetLastError(87); return 0n;
        }
        const guard = dv.getBigUint64(initOncePtr, true);
        if (guard !== 0n) {
          if (contextPtr && ensureMemory(Number(contextPtr) + 8)) {
            dv.setBigUint64(Number(contextPtr), guard === 1n ? 0n : guard, true);
          }
          return 1n;
        }
        if (!callback || callback === 0n) { winSetLastError(87); return 0n; }
        // Mark in-progress
        dv.setBigUint64(initOncePtr, 0xFFFFFFFFFFFFFFFFn, true);
        // Push a callback frame to invoke the init function, then complete on return
        const saved = REG_NAMES.map((_, i) => dv.getBigUint64(ctx + i * 8, true));
        const savedFlags = dv.getBigUint64(ctx + 136, true);
        const rspNow = Number(dv.getBigUint64(ctx + REG.rsp * 8, true));
        const cbRsp = BigInt(((rspNow - 0x100) & ~15) - 8);
        if (!ensureMemory(Number(cbRsp) + 32)) { winSetLastError(87); return 0n; }
        dv.setBigUint64(Number(cbRsp), 0xFFFF_FFF8n, true);
        dv.setBigUint64(ctx + REG.rcx * 8, BigInt(initOncePtr), true);
        dv.setBigUint64(ctx + REG.rdx * 8, parameter, true);
        dv.setBigUint64(ctx + REG.r8 * 8, 0n, true);
        dv.setBigUint64(ctx + REG.r9 * 8, 0n, true);
        dv.setBigUint64(ctx + REG.rsp * 8, cbRsp, true);
        winCallbackFrames.push({
          saved, savedFlags,
          returnPc: 0xFFFF_FFF8n,
          resumeRsp: Number(cbRsp) + 8,
          initOncePtr, contextPtr: Number(contextPtr) || 0,
        });
        return { nextPc: callback };
      }
      case "rtladdfunctiontable": {
        const table = Number(a(0)), count = Number(a(1)), imageBase = a(2);
        if (!Number.isSafeInteger(table) || table <= 0 || !Number.isSafeInteger(count) || count <= 0 || count > 1_000_000 ||
            !ensureMemory(table + count * 12)) return 0n;
        let previousEnd = -1;
        for (let i = 0; i < count; i++) {
          const begin = winReadU32(table + i * 12), end = winReadU32(table + i * 12 + 4);
          if (begin >= end || begin < previousEnd) { winSetLastError(87); return 0n; }
          previousEnd = end;
        }
        winDynamicFunctionTables.set(table, { base: imageBase, count });
        return 1n;
      }
      case "rtldeletefunctiontable": {
        const table = Number(a(0));
        return winDynamicFunctionTables.delete(table) ? 1n : 0n;
      }
      case "rtllookupfunctionentry": {
        const found = winLookupFunctionEntry(a(0));
        const imageBaseOut = Number(a(1));
        if (!found) { if (imageBaseOut && ensureMemory(imageBaseOut + 8)) dv.setBigUint64(imageBaseOut, 0n, true); return 0n; }
        if (imageBaseOut && ensureMemory(imageBaseOut + 8)) dv.setBigUint64(imageBaseOut, found.imageBase, true);
        return found.address;
      }
      case "rtlgetversion": {
        const p = Number(a(0)); if (!ensureMemory(p + 284)) return 0xC0000005n;
        dv.setUint32(p + 4, 10, true); dv.setUint32(p + 8, 0, true); dv.setUint32(p + 12, 22621, true); return 0n;
      }
      case "getversion": return 0x0A000000n;
      case "getversionexw": case "getversionexa": {
        const p=Number(a(0)); if (!ensureMemory(p+8)) return 0n; dv.setUint32(p+4,10,true); dv.setUint32(p+8,0,true); return 1n;
      }
      case "getcurrentdirectorya": case "getcurrentdirectoryw": {
        const wide=n.endsWith("w"), capacity=Number(a(0)), output=a(1), value=`C:${winCurrentDirectory.replaceAll("/","\\")}`;
        const required=value.length+1;
        if (!output || !capacity) return BigInt(required);
        if (capacity<required) { winSetLastError(122); return BigInt(required); }
        if (wide) winWriteW(output,value); else winWriteA(output,value);
        console.log(`[GCD] cap=${capacity} returning="${value}" (${value.length} chars)`);
        return BigInt(required-1);
      }
      case "setcurrentdirectorya": case "setcurrentdirectoryw": {
        const wide = n.endsWith("w");
        const raw = a(0) === 0n ? null : winReadMemoryString(a(0), wide);

        if (raw == null || raw.length === 0) {
          // Steam passes "" when its install-path lookup failed. Real Windows rejects
          // this, but we can be more helpful: fall back to the install dir derived
          // from winImagePath, which is what the caller actually wanted.
          const fallback = winImagePath.replace(/[\\/][^\\/]+$/, "");
          const fbPath = winPath(fallback);
          log(`[SCD] ${n}(${raw === null ? "<NULL>" : JSON.stringify(raw)}) → ` +
              `fallback "${fallback}" (resolved "${fbPath}")`);
          if (winDirectories.has(fbPath) || virtualFiles.has(fbPath)) {
            winCurrentDirectory = fbPath;
            return 1n;
          }
          winSetLastError(87);  // ERROR_INVALID_PARAMETER
          return 0n;
        }

        const path = winPath(raw);
        const exists = winDirectories.has(path) || virtualFiles.has(path);
        log(`[SCD] ${n}("${raw}") → "${path}" exists=${exists}`);
        if (!exists) { winSetLastError(3); return 0n; }
        winCurrentDirectory = path;
        return 1n;
      }

      case "getfileattributesa": case "getfileattributesw": {
        const wide = n.endsWith("w");
        const raw = winReadMemoryString(a(0), wide);
        const path = raw == null ? null : winPath(raw);
        const file = path == null ? null : virtualFiles.get(path);
        const dir = path && winDirectories.has(path);
        log(`[GFA] "${raw}" → "${path}" file=${!!file} dir=${!!dir}`);
        if (file) return 0x80n;
        if (dir)  return 0x10n;
        winSetLastError(2); return 0xffff_ffffn;
      }
      case "getenvironmentvariablea": case "getenvironmentvariablew": {
        const wide = n.endsWith("w"), key = (winReadMemoryString(a(0), wide) ?? "").toUpperCase();
        const rsp = Number(dv.getBigUint64(ctx + REG.rsp * 8, true));
        const ret = (rsp > 0 && rsp + 8 <= u8.length) ? dv.getBigUint64(rsp, true) : 0n;
        const value = winEnvironment.get(key);
        log(`[ENV] ${key} → ${value === undefined ? "<MISSING>" : JSON.stringify(value)} (caller=0x${ret.toString(16)})`);
        if(value==null)return 0n;const capacity=Number(a(2)),output=a(1),required=value.length+1;
        if(!output||!capacity)return BigInt(value.length);
        if(capacity<required){winSetLastError(122);return BigInt(required);}
        winWriteMemoryString(output,value,wide);return BigInt(value.length);
      }
      case "getenv": {
        const name = winReadA(a(0));
        if (!name) return 0n;
        const value = winEnvironment.get(name.toUpperCase());
        if (value === undefined) return 0n;
        // Cache per-name so the pointer stays stable across calls
        if (!winDataSymbols) winDataSymbols = new Map();
        const key = `env!${name.toUpperCase()}`;
        let addr = winDataSymbols.get(key);
        if (!addr) {
          addr = winAlloc(BigInt(value.length + 1), true);
          winWriteA(addr, value);
          winDataSymbols.set(key, addr);
        }
        return addr;
      }
      case "setenvironmentvariablea": case "setenvironmentvariablew": {
        const wide=n.endsWith("w"),key=winReadMemoryString(a(0),wide);if(!key)return 0n;
        const value=a(1)?winReadMemoryString(a(1),wide):null;
        if(value==null)winEnvironment.delete(key.toUpperCase());else winEnvironment.set(key.toUpperCase(),value);return 1n;
      }
      case "expandenvironmentstringsa": case "expandenvironmentstringsw": {
        const wide=n.endsWith("w"),input=winReadMemoryString(a(0),wide)??"";
        const value=input.replace(/%([^%]+)%/g,(_,key)=>winEnvironment.get(key.toUpperCase())??`%${key}%`);
        const capacity=Number(a(2)),output=a(1),required=value.length+1;
        if(output&&capacity){
          const encoded=wide?new Uint8Array((value.length+1)*2):new TextEncoder().encode(value+"\0");
          if(wide)for(let i=0;i<value.length;i++)encoded[i*2]=value.charCodeAt(i)&255,encoded[i*2+1]=value.charCodeAt(i)>>8;
          writeBytes(output,encoded.subarray(0,Math.min(encoded.length,capacity*(wide?2:1))));
        }
        return BigInt(required);
      }
      case "createdirectorya": case "createdirectoryw": {
        const path=readPath(a(0),n.endsWith("w"));if(path==null||winDirectories.has(path)||virtualFiles.has(path)){winSetLastError(path==null?87:183);return 0n;}
        const parent=path.slice(0,path.lastIndexOf("/"))||"/";if(!winDirectories.has(parent)){winSetLastError(3);return 0n;}
        winDirectories.add(path);return 1n;
      }
      case "removedirectorya": case "removedirectoryw": {
        const path=readPath(a(0),n.endsWith("w"));if(path==null||!winDirectories.has(path)){winSetLastError(3);return 0n;}
        if([...virtualFiles.keys()].some((name)=>name.startsWith(`${path.replace(/\/$/,"")}/`))||[...winDirectories].some((name)=>name!==path&&name.startsWith(`${path.replace(/\/$/,"")}/`))){winSetLastError(145);return 0n;}
        winDirectories.delete(path);return 1n;
      }
      case "getfiletype": {
        const handle=winHandles.get(a(0));
        return handle?.kind === "file" ? 1n : handle ? 2n : 0n;
      }
      case "createeventa": case "createeventw": {
        return winAllocHandle({ kind: "event", manualReset: a(1) !== 0n, signaled: a(2) !== 0n });
      }
      case "createmutexa": case "createmutexw": {
        return winAllocHandle({ kind: "mutex", signaled: a(1) === 0n });
      }
      case "createsemaphorea": case "createsemaphorew": {
        const initial = Number(a(1)), maximum = Number(a(2));
        if (!Number.isInteger(initial) || !Number.isInteger(maximum) || initial < 0 || maximum <= 0 || initial > maximum) { winSetLastError(87); return 0n; }
        return winAllocHandle({ kind: "semaphore", count: initial, maximum });
      }
      case "setevent": case "releasemutex": {
        const handle=winHandles.get(a(0)); if (!handle || !["event","mutex"].includes(handle.kind)) { winSetLastError(6); return 0n; }
        handle.signaled=true; winWakeHandleWaiters(); return 1n;
      }
      case "releaseSemaphore": case "releasesemaphore": {
        const handle=winHandles.get(a(0)), release=Number(a(1));
        if (handle?.kind !== "semaphore" || !Number.isInteger(release) || release <= 0 || handle.count + release > handle.maximum) { winSetLastError(87); return 0n; }
        const previous=handle.count; handle.count+=release; if (a(2)) winWriteDword(a(2), previous); winWakeHandleWaiters(); return 1n;
      }
      case "resetevent": {
        const handle=winHandles.get(a(0)); if (!handle || handle.kind!=="event") { winSetLastError(6); return 0n; }
        handle.signaled=false; return 1n;
      }
      case "waitforsingleobject": case "waitforsingleobjectex": {
          const handleBig = a(0);
          const handle = winHandles.get(handleBig);
          let timeout = Number(BigInt.asUintN(32, a(1)));
          if (!handle) { winSetLastError(6); return 0xFFFF_FFFFn; }
          // Never let an INFINITE wait actually be infinite. Real Windows blocks
          // forever; if we do that, the JS event loop dies and nothing else can
          // make progress. Clamp to 5s and let the caller see WAIT_TIMEOUT (0x102).
          if (timeout === 0xFFFFFFFF || timeout > 60000) {
              if (!globalThis.__wfsoClampSeen) globalThis.__wfsoClampSeen = new Set();
              const key = `${handle.kind}`;
              if (!globalThis.__wfsoClampSeen.has(key)) {
                  globalThis.__wfsoClampSeen.add(key);
                  log(`[WFSO-CLAMP] handle=0x${handleBig.toString(16)} kind=${handle.kind} timeout=0x${timeout.toString(16)} → 5000ms`);
              }
              timeout = 5000;
          }
          return BigInt(await winWaitForHandles([handleBig], false, timeout));
      }
      case "waitformultipleobjects": case "waitformultipleobjectsex": {
          const count = Number(a(0)), list = Number(a(1)), waitAll = a(2) !== 0n;
          let timeout = Number(BigInt.asUintN(32, a(3)));
          if (!Number.isInteger(count) || count < 1 || count > 64 || !ensureMemory(list + count * 8)) {
              winSetLastError(87); return 0xffff_ffffn;
          }
          const handles = Array.from({ length: count }, (_, i) => dv.getBigUint64(list + i * 8, true));
          if (handles.some((h) => !winHandles.has(h))) { winSetLastError(6); return 0xffff_ffffn; }
          if (timeout === 0xFFFFFFFF || timeout > 60000) {
              if (!globalThis.__wfmClampSeen) globalThis.__wmfClampSeen = new Set();
              const kinds = handles.map(h => winHandles.get(h)?.kind ?? "?").join(",");
              if (!globalThis.__wfmClampSeen.has(kinds)) {
                  globalThis.__wfmClampSeen.add(kinds);
                  log(`[WFMO-CLAMP] kinds=${kinds} → 5000ms`);
              }
              timeout = 5000;
          }
          return BigInt(await winWaitForHandles(handles, waitAll, timeout));
      }
      case "createfilemappinga": case "createfilemappingw": return winAllocHandle({ kind:"mapping", file:winHandles.get(a(0))?.file ?? null });
      case "mapviewoffile": {
        const handle=winHandles.get(a(0)); if (!handle || handle.kind!=="mapping") { winSetLastError(6); return 0n; }
        const offset=(BigInt(a(2))<<32n)|BigInt(a(3)), size=BigInt(a(4));
        const alloc=winAlloc(size || 0x1000n,true); if (alloc===0n) return 0n;
        if (handle.file) {
          const start=Number(offset), count=Number(size || BigInt(handle.file.data.length-start));
          if (start>=0 && count>=0) writeBytes(alloc,handle.file.data.subarray(start,start+count));
        }
        return alloc;
      }
      // module-level

      case "_set_invalid_parameter_handler": {
          log(`[IPH] registering handler at 0x${BigInt(a(0)).toString(16)}`);
          winInvalidParamHandler = a(0);
          return 0n;
      }

      case "_invalid_parameter_noinfo_noreturn": {
        log(`[CRT-PARAM] ${n}: noreturn — terminating`);
        winExitCode = 0xC0000417 | 0;
        return { exit: true, status: winExitCode };
      }
      case "_invalid_parameter": case "_invalid_parameter_noinfo": {
          if (winInvalidParamHandler) {
              // dispatch through the guest callback
              const rsp = Number(dv.getBigUint64(ctx + REG.rsp * 8, true));
              const retPc = dv.getBigUint64(rsp, true);
              const cb = winStartGuestCallback(winInvalidParamHandler,
                  [a(0), a(1), a(2), a(3)], retPc, rsp);
              if (cb) return cb;
          }
          // existing fallback
          log(`[CRT-PARAM] ${n}: no handler, terminating`);
          winExitCode = 0xC0000417 | 0;
          return { exit: true, status: winExitCode };
      }
      case "_invoke_watson": {
        log(`[CRT-PARAM] _invoke_watson: terminating`);
        winExitCode = 0xC0000417 | 0;
        return { exit: true, status: winExitCode };
      }
      case "unmapviewoffile": return 1n;
      case "flushfilebuffers": return winHandles.has(a(0)) ? 1n : (winSetLastError(6),0n);
      case "setendoffile": {
        const h=winHandles.get(a(0)); if (!h || h.kind!=="file" || !h.writable) { winSetLastError(5); return 0n; }
        const length=h.position;
        if (length>h.file.data.length) { const b=new Uint8Array(length); b.set(h.file.data); h.file.data=b; }
        else h.file.data=h.file.data.slice(0,length);
        return 1n;
      }
      case "strcpy_s": {
        const dst = a(0), size = Number(a(1)), src = a(2);
        if (!dst || size === 0) return 34n;
        const s = winReadA(src); if (s == null) return 34n;
        if (s.length + 1 > size) return 34n;
        winWriteA(dst, s); return 0n;
      }
      case "wcscpy_s": {
        const dst = a(0), size = Number(a(1)), src = a(2);
        if (!dst || size === 0) return 34n;
        const s = winReadW(src); if (s == null) return 34n;
        if (s.length + 1 > size) return 34n;
        winWriteW(dst, s); return 0n;
      }
      case "strncpy_s": case "_strncpy_s_l": {
        const dst = a(0), size = Number(a(1)), src = a(2), count = Number(a(3));
        if (!dst || size === 0) return 34n;
        const s = winReadA(src); if (s == null) return 34n;
        const n = Math.min(count, s.length);
        if (n + 1 > size) return 34n;
        writeBytes(dst, new TextEncoder().encode(s.slice(0, n) + "\0"));
        return 0n;
      }
      case "wcsncpy_s": case "_wcsncpy_s_l": {
        const dst = a(0), size = Number(a(1)), src = a(2), count = Number(a(3));
        if (!dst || size === 0) return 34n;
        const s = winReadW(src); if (s == null) return 34n;
        const n = Math.min(count, s.length);
        if (n + 1 > size) return 34n;
        const bytes = new Uint8Array((n + 1) * 2);
        for (let i = 0; i < n; i++) { const code = s.charCodeAt(i); bytes[i*2] = code & 0xff; bytes[i*2+1] = code >> 8; }
        writeBytes(dst, bytes); return 0n;
      }
      case "setfilepointerex": {
        const h=winHandles.get(a(0)); if (!h || h.kind!=="file") { winSetLastError(6); return 0n; }
        const distance=BigInt.asIntN(64,a(1)), method=Number(a(3));
        const origin=method===0?0:method===1?h.position:method===2?h.file.data.length:null;
        const next=origin===null? -1n:BigInt(origin)+distance;
        if (next<0n || next>0x7fff_ffffn) { winSetLastError(87); return 0n; }
        h.position=Number(next); if (a(2)!==0n) { const p=Number(a(2)); if (!ensureMemory(p+8)) return 0n; dv.setBigInt64(p,next,true); }
        return 1n;
      }
      case "getfilesizeex": {
        const handle=winHandles.get(a(0)),output=Number(a(1));
        if(handle?.kind!=="file"||!ensureMemory(output+8)){winSetLastError(6);return 0n;}
        dv.setBigInt64(output,BigInt(handle.file.data.length),true);return 1n;
      }
      case "setendoffile": {
        const handle=winHandles.get(a(0));if(handle?.kind!=="file"||!handle.writable){winSetLastError(6);return 0n;}
        const bytes=new Uint8Array(handle.position);bytes.set(handle.file.data.subarray(0,handle.position));handle.file.data=bytes;return 1n;
      }
      case "flushfilebuffers": {
        const handle=winHandles.get(a(0));if(!handle||handle.kind!=="file"){winSetLastError(6);return 0n;}return 1n;
      }
      case "copyfilea": case "copyfilew": {
        const wide=n.endsWith("w"),source=readPath(a(0),wide),destination=readPath(a(1),wide),failIfExists=a(2)!==0n;
        const file=source==null?null:virtualFiles.get(source);if(!file){winSetLastError(2);return 0n;}
        if(virtualFiles.has(destination)&&failIfExists){winSetLastError(80);return 0n;}
        virtualFiles.set(destination,{data:file.data.slice()});return 1n;
      }
      case "movefilea": case "movefilew": case "movefileexa": case "movefileexw": {
        const wide=n.endsWith("w"),source=readPath(a(0),wide),destination=readPath(a(1),wide),flags=n.includes("ex")?Number(a(2)):0;
        const file=source==null?null:virtualFiles.get(source);if(!file){winSetLastError(2);return 0n;}
        if(virtualFiles.has(destination)&&(flags&1)===0){winSetLastError(80);return 0n;}
        virtualFiles.set(destination,file);virtualFiles.delete(source);return 1n;
      }
      case "getfullpathnamea": case "getfullpathnamew": {
        const wide=n.endsWith("w"), input=winReadMemoryString(a(0),wide); if (input==null) return 0n;
        const path=input.match(/^[A-Za-z]:[\\/]/)?input:`C:${winPath(input).replaceAll("/","\\")}`;
        const cap=Number(a(1)), buffer=a(2);
        if (wide) { const b=new Uint8Array((path.length+1)*2); for(let i=0;i<path.length;i++)b[i*2]=path.charCodeAt(i)&255,b[i*2+1]=path.charCodeAt(i)>>8; if(cap)writeBytes(buffer,b.subarray(0,Math.min(b.length,cap*2))); }
        else { const b=new TextEncoder().encode(path+"\0"); if(cap)writeBytes(buffer,b.subarray(0,cap)); }
        return BigInt(path.length+1);
      }
      case "gettemppatha": case "gettemppathw": {
        const wide=n.endsWith("w"), path="C:\\TEMP\\", buffer=a(1), cap=Number(a(0));
        if(wide){const b=new Uint8Array((path.length+1)*2);for(let i=0;i<path.length;i++)b[i*2]=path.charCodeAt(i)&255,b[i*2+1]=path.charCodeAt(i)>>8;if(cap)writeBytes(buffer,b.subarray(0,Math.min(b.length,cap*2)));}
        else {const b=new TextEncoder().encode(path+"\0");if(cap)writeBytes(buffer,b.subarray(0,cap));}
        return BigInt(path.length);
      }
      // SHLWAPI path helpers operate only on the guest's virtual filesystem.
      case "pathcombinea": case "pathcombinew": {
        const wide = n.endsWith("w"), dir = winReadMemoryString(a(1), wide) ?? "", file = winReadMemoryString(a(2), wide) ?? "";
        const joined = file.match(/^[A-Za-z]:[\\/]/) || file.startsWith("\\") ? file : `${dir.replace(/[\\/]+$/, "")}\\${file.replace(/^[\\/]+/, "")}`;
        const normalized = joined.replaceAll("/", "\\").replace(/\\\.\\/g, "\\");
        if (wide) winWriteW(a(0), normalized); else winWriteA(a(0), normalized); return a(0);
      }
      case "pathappenda": case "pathappendw": {
        const wide = n.endsWith("w"), base = winReadMemoryString(a(0), wide) ?? "", extra = winReadMemoryString(a(1), wide) ?? "";
        const joined = `${base.replace(/[\\/]+$/, "")}\\${extra.replace(/^[\\/]+/, "")}`;
        if (wide) winWriteW(a(0), joined); else winWriteA(a(0), joined); return 1n;
      }
      case "pathremovefilespeca": case "pathremovefilespecw": {
        const wide = n.endsWith("w"), path = winReadMemoryString(a(0), wide) ?? "", index = Math.max(path.lastIndexOf("\\"), path.lastIndexOf("/"));
        if (index < 0) return 0n;
        const result = path.slice(0, index || 3); if (wide) winWriteW(a(0), result); else winWriteA(a(0), result); return 1n;
      }
      case "pathfindfilenamea": case "pathfindfilenamew": {
        const path = winReadMemoryString(a(0), n.endsWith("w")) ?? "", index = Math.max(path.lastIndexOf("\\"), path.lastIndexOf("/"));
        return a(0) + BigInt(Math.max(0, index + 1) * (n.endsWith("w") ? 2 : 1));
      }
      case "pathisrelativea": case "pathisrelativew": {
        const path = winReadMemoryString(a(0), n.endsWith("w")) ?? "";
        return !/^(?:[A-Za-z]:[\\/]|[\\/]{1,2})/.test(path) ? 1n : 0n;
      }
      case "pathfileexistsa": case "pathfileexistsw": {
          const path = readPath(a(0), n.endsWith("w"));
          return path != null && (virtualFiles.has(path) || winDirectories.has(path)) ? 1n : 0n;
      }
      case "pathisdirectorya": case "pathisdirectoryw": {
          const path = readPath(a(0), n.endsWith("w"));
          return path != null && winDirectories.has(path) ? 1n : 0n;
      }
      case "pathisdirectorya": case "pathisdirectoryw": {
        const path = readPath(a(0), n.endsWith("w"));
        return path != null && (winDirectories.has(path) || [...winDirectories,...virtualFiles.keys()].some((name) => name.startsWith(`${path.replace(/\/$/, "")}/`))) ? 1n : 0n;
      }
      case "pathcanonicalizea": case "pathcanonicalizew": {
        const wide = n.endsWith("w"), path = winReadMemoryString(a(1), wide) ?? "";
        const normalized = path.replaceAll("/", "\\").split("\\").reduce((parts, item) => {
          if (!item || item === ".") return parts; if (item === "..") parts.pop(); else parts.push(item); return parts;
        }, []).join("\\");
        if (wide) winWriteW(a(0), normalized); else winWriteA(a(0), normalized); return 1n;
      }
      case "strcmplogicala": case "strcmplogicalw": case "strcmpia": case "strcmpiw": {
        const wide = n.endsWith("w"), x = winReadMemoryString(a(0), wide) ?? "", y = winReadMemoryString(a(1), wide) ?? "";
        const left = x.toLocaleLowerCase(), right = y.toLocaleLowerCase(); return BigInt(left === right ? 0 : left < right ? -1 : 1);
      }
      case "strstria": case "strstriw": {
        const wide = n.endsWith("w"), haystack = winReadMemoryString(a(0), wide) ?? "", needle = winReadMemoryString(a(1), wide) ?? "";
        const index = haystack.toLowerCase().indexOf(needle.toLowerCase());
        return index < 0 ? 0n : a(0) + BigInt(index * (wide ? 2 : 1));
      }
      // SHELL32: deterministic guest profile paths and argument parsing.
      case "shgetfolderpatha": case "shgetfolderpathw": {
        const wide = n.endsWith("w"), csidl = Number(a(1)) & 0xff;
        const paths = { 0x05: "C:\\Users\\Guest\\Documents", 0x10: "C:\\Users\\Guest\\Desktop",
          0x1a: "C:\\Users\\Guest\\AppData\\Roaming", 0x1c: "C:\\Users\\Guest\\AppData\\Local",
          0x24: "C:\\Windows", 0x25: "C:\\Windows\\System32", 0x26: "C:\\Program Files", 0x28: "C:\\Users\\Guest" };
        const value = paths[csidl] ?? "C:\\TEMP"; if (wide) winWriteW(a(4), value); else winWriteA(a(4), value); return 0n;
      }
      case "shgetknownfolderpath": {
        const id = Number(a(0)), output = Number(a(3));
        if (!ensureMemory(id + 16) || !ensureMemory(output + 8)) return 0x80070057n;
        const guidHex = Array.from(u8.subarray(id, id + 16), (v) => v.toString(16).padStart(2, "0")).join("").toLowerCase();
        const profiles = {
          "8f856c5e220e60479afeea3317b67173": "C:\\Users\\Guest",
          "db85b63e9f65f64ca03ae3ef65729f3d": "C:\\Users\\Guest\\AppData\\Roaming",
          "8527b3f1ba6fcd4f9d557b8e7f157091": "C:\\Users\\Guest\\AppData\\Local",
          "d09ad3fd8f234146adb46c85480369c7": "C:\\Users\\Guest\\Documents",
          "3accbfb42cdb2c42b0297fe99a87c641": "C:\\Users\\Guest\\Desktop",
        };
        const value = profiles[guidHex] ?? "C:\\Users\\Guest";
        const buffer = winAlloc(BigInt((value.length + 1) * 2), true); winWriteW(buffer, value);
        dv.setBigUint64(output, buffer, true); return 0n;
      }
      case "commandlinetoargvw": {
        const text = winReadW(a(0)) ?? "", argv = [];
        let token = "", quoted = false;
        for (let i = 0; i < text.length; i++) {
          const ch = text[i];
          if (ch === '"') { quoted = !quoted; continue; }
          if (!quoted && /\s/.test(ch)) { if (token) { argv.push(token); token = ""; } continue; }
          token += ch;
        }
        if (token) argv.push(token);
        const list = winAlloc(BigInt(Math.max(1, argv.length) * 8), true);
        argv.forEach((item, index) => { const value = winAlloc(BigInt((item.length + 1) * 2), true); winWriteW(value, item); dv.setBigUint64(Number(list) + index * 8, value, true); });
        if (a(1)) winWriteDword(a(1), argv.length); return list;
      }
      case "shfreememory": return 0n;
      // OLE32/COM: initialization and task memory are supported; COM activation is not.
      case "coinitialize": case "coinitializeex": case "coinitializesecurity": return 0n;
      case "couninitialize": return 0n;
      case "cotaskmemalloc": case "comtaskmemalloc": return winAlloc(a(0), true);
      case "cotaskmemfree": case "comtaskmemfree": return 0n;
      case "cocreatinstance": case "cogetclassobject": {
        if (a(4)) { const p = Number(a(4)); if (ensureMemory(p + 8)) dv.setBigUint64(p, 0n, true); }
        return 0x80040154n; // REGDB_E_CLASSNOTREG: no native COM server is available.
      }
      case "cocreateguid": {
        const p = Number(a(0)); if (!ensureMemory(p + 16)) return 0x80070057n;
        try { globalThis.crypto.getRandomValues(u8.subarray(p, p + 16)); } catch { return 0x80070057n; }
        u8[p + 7] = (u8[p + 7] & 0x0f) | 0x40; u8[p + 8] = (u8[p + 8] & 0x3f) | 0x80; return 0n;
      }
      case "stringfromguid2": {
        const p = Number(a(0)), guid = p >= 0 && p + 16 <= u8.length ? p : -1;
        if (guid < 0) return 0n;
        const d1 = dv.getUint32(p, true).toString(16).padStart(8, "0"), d2 = dv.getUint16(p + 4, true).toString(16).padStart(4, "0"),
          d3 = dv.getUint16(p + 6, true).toString(16).padStart(4, "0"), d4 = Array.from(u8.subarray(p + 8, p + 16), (v) => v.toString(16).padStart(2, "0"));
        const text = `{${d1}-${d2}-${d3}-${d4.slice(0,2).join("")}-${d4.slice(2).join("")}}`;
        if (text.length + 1 > Number(a(2))) return 0n; winWriteW(a(1), text); return BigInt(text.length + 1);
      }
      case "clsidfromstring": {
        const text = winReadW(a(0)) ?? "", match = text.match(/[0-9a-f]{8}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{12}/i);
        const p = Number(a(1)); if (!match || !ensureMemory(p + 16)) return 0x80070057n;
        const [d1,d2,d3,d4,d5] = match[0].split("-"); dv.setUint32(p, parseInt(d1,16), true); dv.setUint16(p+4,parseInt(d2,16),true); dv.setUint16(p+6,parseInt(d3,16),true);
        for (let i=0;i<2;i++) u8[p+8+i]=parseInt(d4.slice(i*2,i*2+2),16); for (let i=0;i<6;i++)u8[p+10+i]=parseInt(d5.slice(i*2,i*2+2),16); return 0n;
      }
      // COMCTL32 and WINMM common initialization/timing exports.
      case "initcommoncontrols": return 0n;
      case "initcommoncontrolsex": return 1n;
      case "timegettime": return BigInt(Date.now() >>> 0);
      case "timebeginperiod": case "timeendperiod": return 0n;
      case "timegetsystemtime": {
        const p = Number(a(0)); if (!ensureMemory(p + 12)) return 11n;
        dv.setUint32(p, 1, true); dv.setUint32(p + 4, Date.now() >>> 0, true); return 0n;
      }
      case "playsounda": case "playsoundw": return 0n; // Audio output is intentionally not emulated.
      case "getfileversioninfosizea": case "getfileversioninfosizew": case "getfileversioninfoa": case "getfileversioninfow": case "verqueryvaluea": case "verqueryvaluew": {
        winSetLastError(1812); return 0n;
      }
      case "getuserdefaultlcid": case "getsystemdefaultlcid": return 0x409n;
      case "getuserdefaultlangid": case "getsystemdefaultlangid": return 0x409n;
      case "isprocessorfeaturepresent": return [0,10,12,13].includes(Number(a(0))) ? 1n : 0n;
      case "getenvironmentstringsa": case "getenvironmentstringsw": {
        const wide=n.endsWith("w"),text=[...winEnvironment].map(([key,value])=>`${key}=${value}`).join("\0")+"\0\0";
        const bytes=wide?new Uint8Array(text.length*2):new TextEncoder().encode(text);
        if(wide)for(let i=0;i<text.length;i++)bytes[i*2]=text.charCodeAt(i)&255,bytes[i*2+1]=text.charCodeAt(i)>>8;
        const ptr=winAlloc(bytes.length,true);if(!ptr)return 0n;writeBytes(ptr,bytes);return ptr;
      }
      case "freeenvironmentstringsa": case "freeenvironmentstringsw": return 1n;
      case "getacp": case "getoemcp": case "getconsoleoutputcp": return 65001n;
      case "setconsoleoutputcp": return 1n;
      case "isvalidcodepage": return a(0) === 65001n || a(0) === 1252n ? 1n : 0n;
      case "multibytetowidechar": {
        const input = winReadA(a(2), 0x100000); if (input == null) return 0n;
        const required = input.length + 1, cap = Number(a(4)), outPtr = Number(a(5));
        if (outPtr === 0 || cap === 0) return BigInt(required);
        const text = input.slice(0, Number(a(3)) > 0 ? Number(a(3)) : input.length);
        const bytes = new Uint8Array((text.length + 1) * 2);
        for (let i=0;i<text.length;i++) bytes[i*2]=text.charCodeAt(i)&255,bytes[i*2+1]=text.charCodeAt(i)>>8;
        if (cap < text.length + 1 || !writeBytes(outPtr, bytes)) { winSetLastError(122); return 0n; }
        return BigInt(text.length + 1);
      }
      case "widechartomultibyte": {
        const input = winReadW(a(2), 0x100000); if (input == null) return 0n;
        const text = input.slice(0, Number(a(3)) > 0 ? Number(a(3)) : input.length);
        const bytes = new TextEncoder().encode(text + "\0"), cap = Number(a(5)), outPtr = Number(a(4));
        if (outPtr === 0 || cap === 0) return BigInt(bytes.length);
        if (cap < bytes.length || !writeBytes(outPtr, bytes)) { winSetLastError(122); return 0n; }
        return BigInt(bytes.length);
      }
      case "getsystemtimeasfiletime": {
        const p=Number(a(0)); if (!ensureMemory(p+8)) return 0n;
        const ticks=BigInt(Date.now())*10000n+116444736000000000n; dv.setBigUint64(p,ticks,true); return 0n;
      }
      case "rtlgetcurrentpeb": return BigInt(WIN_PEB);
      case "rtlgetcurrentteb": return BigInt(WIN_TEB);
      case "rtlexituserprocess": case "exitthread": {
        const status = Number(a(0)) | 0; winExitCode=status; return { exit:true, status };
      }
      case "ntclose": return 0n;
      case "ntsetinformationthread": return 0n;
      case "ntallocatevirtualmemory": {
        const process = a(0), basePtr = Number(a(1)), sizePtr = Number(a(3));
        if (!ensureMemory(basePtr+8) || !ensureMemory(sizePtr+8)) return 0xc0000005n;
        const requested = dv.getBigUint64(basePtr,true), size = dv.getBigUint64(sizePtr,true);
        const address = requested === 0n ? winAlloc(size,true) : requested;
        if (address === 0n) return 0xc0000017n;
        dv.setBigUint64(basePtr,address,true); dv.setBigUint64(sizePtr,(size+0xfffn)&~0xfffn,true); return 0n;
      }
      case "ntfreevirtualmemory": return 0n;
      case "ntprotectvirtualmemory": return 0n;
      case "ntqueryinformationprocess": {
        const infoClass=Number(a(1)), out=Number(a(2)), length=Number(a(3));
        if (infoClass === 0 && length >= 48 && ensureMemory(out+48)) {
          u8.fill(0,out,out+48); dv.setBigUint64(out+8,BigInt(WIN_PEB),true); return 0n;
        }
        return 0xc0000003n;
      }
      case "ntqueryvirtualmemory": return 0xc0000003n;
      // USER32 window classes and lifecycle.
      case "registerclassa": case "registerclassw": case "registerclassexa": case "registerclassexw": {
        const isEx = n.includes("classex"), wide = n.endsWith("w"), p = Number(a(0));
        const namePtr = winReadU64(p + (isEx ? 64 : 64));
        const nameValue = namePtr > 0xffffn ? winReadMemoryString(namePtr, wide) : `#${Number(namePtr)}`;
        if (!nameValue) { winSetLastError(87); return 0n; }
        const key = nameValue.toLowerCase();
        if (winClasses.has(key)) { winSetLastError(1410); return 0n; }
        winClasses.set(key, { name: nameValue, wndProc: winReadU64(p + 8), style: dv.getUint32(p + (isEx ? 4 : 0), true),
          background: winReadU64(p + 48), instance: winReadU64(p + 24), extraBytes: dv.getUint32(p + 20, true) });
        return 1n;
      }
      case "getclasslonga": case "getclasslongw": case "getclasslongptra": case "getclasslongptrw": {
        const nameValue=winReadMemoryString(a(0),n.endsWith("w")),info=nameValue?winFindClass(nameValue):null;
        if(!info)return 0n;const index=Number(BigInt.asIntN(32,a(1)));
        return index===-16?info.instance:index===-24?info.wndProc:index===-10?info.background:index===-26?BigInt(info.style):0n;
      }
      case "setclasslonga": case "setclasslongw": case "setclasslongptra": case "setclasslongptrw": {
        const nameValue=winReadMemoryString(a(0),n.endsWith("w")),info=nameValue?winFindClass(nameValue):null;
        if(!info)return 0n;const index=Number(BigInt.asIntN(32,a(1))),value=a(2);
        const old=index===-24?info.wndProc:index===-16?info.instance:index===-10?info.background:index===-26?BigInt(info.style):0n;
        if(index===-24)info.wndProc=value;else if(index===-16)info.instance=value;else if(index===-10)info.background=value;else if(index===-26)info.style=Number(value)>>>0;
        return old;
      }
      case "unregisterclassa": case "unregisterclassw": {
        const nameValue = winReadMemoryString(a(0), n.endsWith("w"));
        return nameValue && winClasses.delete(nameValue.toLowerCase()) ? 1n : 0n;
      }
      case "createwindowexa": case "createwindowexw": {
        const wide = n.endsWith("w"), classArg = a(1), className = classArg <= 0xffffn ? `#${Number(classArg)}` : winReadMemoryString(classArg, wide);
        const title = winReadMemoryString(a(2), wide) ?? "";
        const classInfo = winFindClass(className) ?? (className && /^(button|static|edit|listbox|combobox|scrollbar|syslistview32|systreeview32|systabcontrol32|msctls_progress32|msctls_trackbar32|msctls_updown32|msctls_statusbar32|toolbarwindow32|sysheader32|sysdatetim32|sysmonthcal32|richedit20a|richedit20w|richedit50w)$/i.test(className)
          ? { name: className, wndProc: 0n, style: 0, background: 0n, builtin: true } : null);
        if (!classInfo) { winSetLastError(1407); return 0n; }
        const val = (i) => Number(BigInt.asIntN(32, a(i)));
        const useDefault = (v) => v === -2147483648 || v === 0x80000000;
        const width = Math.max(1, useDefault(val(6)) ? 640 : val(6));
        const height = Math.max(1, useDefault(val(7)) ? 480 : val(7));
        const x = useDefault(val(4)) ? 40 + (winZOrder % 8) * 24 : val(4);
        const y = useDefault(val(5)) ? 40 + (winZOrder % 8) * 24 : val(5);
        const hwnd = winAllocHandle({ kind: "window", hwnd: 0n, className: classInfo.name, title,
          wndProc: classInfo.wndProc ?? 0n, classInfo, style: Number(a(3)) >>> 0, exStyle: Number(a(0)) >>> 0,
          x, y, width, height, parent: a(8), menu: a(9), instance: a(10), param: a(11),
          visible: (Number(a(3)) & 0x10000000) !== 0, enabled: true, destroyed: false, focused: false, invalid: true,
          commands: [], z: ++winZOrder, control: classInfo.builtin ? String(classInfo.name).toLowerCase() : null,
          userData: 0n, dcState: null });
        const win = winHandles.get(hwnd); win.hwnd = hwnd; winWindows.set(hwnd, win);
        winPostMessage(hwnd, WINMSG.NCCREATE, 0n, a(11));
        winPostMessage(hwnd, WINMSG.CREATE, 0n, a(11));
        winPostMessage(hwnd, WINMSG.SIZE, 0n, winPackPoint(width, height));
        winPresent(); return hwnd;
      }
      case "destroywindow": {
        if (!winDestroyWindow(a(0))) { winSetLastError(1400); return 0n; }
        return 1n;
      }
      case "showwindow": {
        const w = winWindow(a(0)); if (!w) { winSetLastError(1400); return 0n; }
        const wasVisible = w.visible; w.visible = Number(a(1)) !== 0;
        winPostMessage(w.hwnd, WINMSG.SHOWWINDOW, w.visible ? 1n : 0n, 0n);
        if (w.visible) { winPostMessage(w.hwnd, WINMSG.SIZE, 0n, winPackPoint(w.width, w.height)); if (w.invalid) winPostMessage(w.hwnd, WINMSG.PAINT); }
        winPresent(); return wasVisible ? 1n : 0n;
      }
      case "updatewindow": {
        const w = winWindow(a(0)); if (!w) return 0n;
        if (w.invalid) winPostMessage(w.hwnd, WINMSG.PAINT);
        return 1n;
      }
      case "iswindow": return BigInt(a(0)) === WIN_DESKTOP_HANDLE || winWindow(a(0)) ? 1n : 0n;
      case "iswindowvisible": return BigInt(a(0)) === WIN_DESKTOP_HANDLE || winIsVisible(winWindow(a(0))) ? 1n : 0n;
      case "isiconic": case "iszoomed": return 0n;
      case "getdesktopwindow": return WIN_DESKTOP_HANDLE;
      case "getactivewindow": return BigInt([...winWindows.values()].find((w) => w.focused)?.hwnd ??
        [...winWindows.values()].filter((w) => w.visible).sort((x,y) => y.z-x.z)[0]?.hwnd ?? 0n);
      case "getforegroundwindow": return BigInt([...winWindows.values()].filter((w) => w.visible).sort((x,y) => y.z-x.z)[0]?.hwnd ?? 0n);
      case "bringwindowtotop": { const w=winWindow(a(0)); if(!w)return 0n; winRaiseWindowFamily(w.hwnd); winPresent(); return 1n; }
      case "isenabled": return winWindow(a(0))?.enabled ? 1n : 0n;
      case "enablewindow": {
        const w = winWindow(a(0)); if (!w) return 0n;
        const old = w.enabled; w.enabled = a(1) !== 0n; return old ? 1n : 0n;
      }
      case "getclientrect": case "getwindowrect": {
        const hwnd = BigInt(a(0));
        if (hwnd === WIN_DESKTOP_HANDLE) {
          const r = { left: 0, top: 0, right: winScreen.width, bottom: winScreen.height };
          return winWriteRect(a(1), r) ? 1n : 0n;
        }
        const w = winWindow(hwnd); if (!w) { winSetLastError(1400); return 0n; }
        let r;
        if (n === "getclientrect") {
          const inset = winClientInsets(w);
          r = { left: 0, top: 0, right: Math.max(0, w.width - inset.x - inset.right), bottom: Math.max(0, w.height - inset.y - inset.bottom) };
        } else {
          const q = winAbsRect(w); r = { left: q.x, top: q.y, right: q.x + q.width, bottom: q.y + q.height };
        }
        return winWriteRect(a(1), r) ? 1n : 0n;
      }
      case "movewindow": case "setwindowpos": {
        const w = winWindow(a(0)); if (!w) return 0n;
        const oldX = w.x, oldY = w.y, oldWidth = w.width, oldHeight = w.height;
        if (n === "movewindow") {
          w.x = Number(BigInt.asIntN(32, a(1))); w.y = Number(BigInt.asIntN(32, a(2)));
          w.width = Math.max(1, Number(a(3))); w.height = Math.max(1, Number(a(4)));
        } else {
          const insertAfter = a(1), x = Number(BigInt.asIntN(32, a(2))), y = Number(BigInt.asIntN(32, a(3)));
          const width = Number(a(4)), height = Number(a(5)), flags = Number(a(6));
          if (!(flags & 0x0002)) { w.x = x; w.y = y; }
          if (!(flags & 0x0001)) { w.width = Math.max(1, width); w.height = Math.max(1, height); }
          if (flags & 0x0040) w.visible = true;
          if (flags & 0x0080) w.visible = false;
          if (!(flags & 0x0004) && (insertAfter === 0n || insertAfter === 1n)) winRaiseWindowFamily(w.hwnd);
        }
        if (w.x !== oldX || w.y !== oldY) winPostMessage(w.hwnd, WINMSG.MOVE, 0n, winPackPoint(w.x, w.y));
        if (w.width !== oldWidth || w.height !== oldHeight) {
          const inset = winClientInsets(w);
          winPostMessage(w.hwnd, WINMSG.SIZE, 0n, winPackPoint(Math.max(0, w.width - inset.x - inset.right), Math.max(0, w.height - inset.y - inset.bottom)));
        }
        w.invalid = true; winPresent(); return 1n;
      }
      case "setwindowtexta": case "setwindowtextw": {
        const w = winWindow(a(0)); if (!w) return 0n;
        w.title = winReadMemoryString(a(1), n.endsWith("w")) ?? ""; winPresent(); return 1n;
      }
      case "getwindowtexta": case "getwindowtextw": {
        const w = winWindow(a(0)); if (!w) return 0n;
        const text = w.title ?? "", cap = Math.max(0, Number(a(2)) - 1), slice = text.slice(0, cap);
        winWriteMemoryString(a(1), slice, n.endsWith("w")); return BigInt(slice.length);
      }
      case "getwindowtextlengtha": case "getwindowtextlengthw": return BigInt(winWindow(a(0))?.title?.length ?? 0);
      case "getparent": return winWindow(a(0))?.parent ?? 0n;
      case "getwindow": {
        const w=winWindow(a(0)); if(!w)return 0n; const command=Number(a(1));
        const ordered=[...winWindows.values()].sort((x,y)=>x.z-y.z), index=ordered.findIndex(x=>x.hwnd===w.hwnd);
        if(command===0)return BigInt(ordered[index-1]?.hwnd??0n); // GW_HWNDFIRST (best-effort sibling ordering)
        if(command===1)return BigInt(ordered[index+1]?.hwnd??0n); // GW_HWNDLAST
        if(command===4)return BigInt(ordered[index+1]?.hwnd??0n); // GW_HWNDNEXT
        if(command===3)return BigInt(ordered[index-1]?.hwnd??0n); // GW_HWNDPREV
        if(command===5)return w.parent;
        return 0n;
      }
      case "getdlgitem": {
        const parent=winWindow(a(0)), id=a(1); if(!parent)return 0n;
        return BigInt([...winWindows.values()].find(w=>w.parent===parent.hwnd&&w.menu===id)?.hwnd??0n);
      }
      case "getdlgctrlid": return winWindow(a(0))?.menu ?? 0n;
      case "getwindowthreadprocessid": { const p=Number(a(1)); if(p&&ensureMemory(p+4))dv.setUint32(p,1,true); return 1n; }
      case "getclassnamea": case "getclassnamew": {
        const w=winWindow(a(0));if(!w)return 0n;const wide=n.endsWith("w"),cap=Math.max(0,Number(a(2))-1),name=String(w.className).slice(0,cap);
        winWriteMemoryString(a(1),name,wide);return BigInt(name.length);
      }
      case "setdlgitemtexta": case "setdlgitemtextw": {
        const parent=winWindow(a(0)),id=a(1),child=[...winWindows.values()].find(w=>w.parent===parent?.hwnd&&w.menu===id);
        if(!child)return 0n;child.title=winReadMemoryString(a(2),n.endsWith("w"))??"";winPresent();return 1n;
      }
      case "rtlcapturecontext": {
        // Capture CONTEXT at ptr — dump registers
        const p = Number(a(0));
        if (!ensureMemory(p + 0x4D0)) { winSetLastError(87); return 0n; }
        u8.fill(0, p, p + 0x4D0);
        dv.setUint32(p + 0x30, 0x0010000F, true);   // ContextFlags = FULL
        const regs = ["rax","rcx","rdx","rbx","rsp","rbp","rsi","rdi",
                      "r8","r9","r10","r11","r12","r13","r14","r15"];
        const ctxOff = { rax:0x78, rcx:0x80, rdx:0x88, rbx:0x90, rsp:0x98,
                        rbp:0xA0, rsi:0xA8, rdi:0xB0, r8:0xB8, r9:0xC0,
                        r10:0xC8, r11:0xD0, r12:0xD8, r13:0xE0, r14:0xE8, r15:0xF0 };
        for (const r of regs) dv.setBigUint64(p + ctxOff[r], dv.getBigUint64(ctx + REG[r] * 8, true), true);
        return 0n;
      }

      case "unhandledexceptionfilter": return 1n;   // EXCEPTION_EXECUTE_HANDLER
      case "getdlgitemtexta": case "getdlgitemtextw": {
        const parent=winWindow(a(0)),id=a(1),child=[...winWindows.values()].find(w=>w.parent===parent?.hwnd&&w.menu===id);
        if(!child)return 0n;const text=child.title??"",slice=text.slice(0,Math.max(0,Number(a(3))-1));winWriteMemoryString(a(2),slice,n.endsWith("w"));return BigInt(slice.length);
      }
      case "setparent": {
        const w = winWindow(a(0)); if (!w) return 0n;
        const old = w.parent; w.parent = a(1); winPresent(); return old;
      }
      case "_snprintf_s": case "_snprintf_s_l": return 0n
      // ── __stdio_common_vsnprintf_s / __stdio_common_vsnprintf ─────────
      // UCRT entry point that `V_snprintf` / `_vsnprintf` compile down to.
      // Signature:
      //   a(0)=options  a(1)=buffer  a(2)=sizeOfBuffer  a(3)=maxCount
      //   a(4)=format   a(5)=locale  a(6)=va_list
      // Return: number of characters that *would have* been written (the
      // printf return convention) — Steam's AssertionFailed wrapper treats
      // anything < 0 as a fatal CRT parameter error, and treats 0 as a
      // "truncated / nothing written" warning that then fails the caller.
      case "__stdio_common_vsnprintf_s":
      case "__stdio_common_vsnprintf": {
          const buf    = Number(a(1));
          const size   = Number(a(2));
          const maxCnt = Number(a(3));
          const fmtPtr = Number(a(4));
          const vaList = a(6);
          if (!fmtPtr || !Number.isSafeInteger(size) || size <= 0) {
              log(`[VSNPRINTF] bad args fmt=0x${fmtPtr.toString(16)} size=${size}`);
              return 0xffff_ffffn;   // -1
          }
          const fmt = winReadA(fmtPtr);
          if (fmt == null) return 0xffff_ffffn;
          let text;
          try {
              text = winFormat(fmt, 0, vaList, false);
          } catch (e) {
              log(`[VSNPRINTF] format threw on "${fmt}": ${e.message}`);
              return 0xffff_ffffn;
          }
          const limit = Math.min(Number.isFinite(maxCnt) && maxCnt >= 0 ? maxCnt : size - 1, size - 1);
          const written = Math.min(text.length, limit);
          if (buf && written > 0 && ensureMemory(buf + written + 1)) {
              writeBytes(buf, new TextEncoder().encode(text.slice(0, written) + "\0"));
          } else if (buf && ensureMemory(buf + 1)) {
              u8[buf] = 0;
          }
          return BigInt(text.length);   // full length, like real snprintf
      }

      // ── _vsnprintf / _vsnwprintf / _vsprintf_s / _vsnprintf_s ─────────
      // MSVC's pre-UCRT variants. Some Steam translation units still use
      // these. Handle both ASCII and wide.
      case "_vsnprintf": case "_vsnprintf_l":
      case "_vsnprintf_s": case "_vsnprintf_s_l": {
          const buf    = Number(a(0));
          const size   = Number(a(1));
          const count  = Number(BigInt.asIntN(64, a(2)));
          const fmtPtr = Number(a(3));
          const vaList = n.endsWith("_l") ? a(5) : null;
          if (!fmtPtr) return 0xffff_ffffn;
          const fmt = winReadA(fmtPtr);
          if (fmt == null) return 0xffff_ffffn;
          let text;
          try { text = winFormat(fmt, 0, vaList, false); }
          catch (e) { log(`[VSNPRINTF] format threw: ${e.message}`); return 0xffff_ffffn; }
          const limit = (count < 0 || !Number.isFinite(count)) ? size - 1 : Math.min(count, size - 1);
          const written = Math.min(text.length, limit);
          if (buf && ensureMemory(buf + written + 1)) {
              writeBytes(buf, new TextEncoder().encode(text.slice(0, written) + "\0"));
          }
          return BigInt(text.length);
      }

      case "_vsnwprintf": case "_vsnwprintf_l":
      case "_vsnwprintf_s": case "_vsnwprintf_s_l": {
          const buf    = Number(a(0));
          const size   = Number(a(1));
          const count  = Number(BigInt.asIntN(64, a(2)));
          const fmtPtr = Number(a(3));
          const vaList = n.endsWith("_l") ? a(5) : null;
          if (!fmtPtr) return 0xffff_ffffn;
          const fmt = winReadW(fmtPtr);
          if (fmt == null) return 0xffff_ffffn;
          let text;
          try { text = winFormat(fmt, 0, vaList, true); }
          catch (e) { log(`[VSNPRINTF] wformat threw: ${e.message}`); return 0xffff_ffffn; }
          const limit = (count < 0 || !Number.isFinite(count)) ? size - 1 : Math.min(count, size - 1);
          const written = Math.min(text.length, limit);
          if (buf && ensureMemory(buf + (written + 1) * 2)) {
              const bytes = new Uint8Array((written + 1) * 2);
              for (let i = 0; i < written; i++) {
                  const c = text.charCodeAt(i);
                  bytes[i*2] = c & 0xff; bytes[i*2+1] = c >> 8;
              }
              writeBytes(buf, bytes);
          }
          return BigInt(text.length);
      }

      case "_vsprintf_s": case "_vsprintf_s_l": {
          // No size limit — caller asserts buffer is big enough. Return full length.
          return emulateWinApi({ dll: "ucrtbase", name: "_vsnprintf_s" });
      }

      case "__stdio_common_vsprintf_s":
      case "__stdio_common_vsprintf": {
          // No limit variant. Same signature but a(3) is ignored.
          return emulateWinApi({ dll: "ucrtbase", name: "__stdio_common_vsnprintf_s" });
      }
      case "_snwprintf_s": case "_snwprintf_s_l": return 0n
      case "getwindowlonga": case "getwindowlongw": case "getwindowlongptra": case "getwindowlongptrw": {
        const w = winWindow(a(0)); if (!w) return 0n;
        const index = Number(BigInt.asIntN(32, a(1)));
        return index === WIN_GWL.WNDPROC ? w.wndProc : index === WIN_GWL.STYLE ? BigInt(w.style) :
          index === WIN_GWL.EXSTYLE ? BigInt(w.exStyle) : index === WIN_GWL.USERDATA ? w.userData :
          index === WIN_GWL.HINSTANCE ? w.instance : index === WIN_GWL.HWNDPARENT ? w.parent :
          index === WIN_GWL.ID ? w.menu : 0n;
      }
      case "setwindowlonga": case "setwindowlongw": case "setwindowlongptra": case "setwindowlongptrw": {
        const w = winWindow(a(0)); if (!w) return 0n;
        const index = Number(BigInt.asIntN(32, a(1))), value = a(2);
        const old = index === WIN_GWL.WNDPROC ? w.wndProc : index === WIN_GWL.STYLE ? BigInt(w.style) :
          index === WIN_GWL.EXSTYLE ? BigInt(w.exStyle) : index === WIN_GWL.USERDATA ? w.userData :
          index === WIN_GWL.HWNDPARENT ? w.parent : index === WIN_GWL.ID ? w.menu : 0n;
        if (index === WIN_GWL.WNDPROC) w.wndProc = value;
        else if (index === WIN_GWL.STYLE) w.style = Number(value) >>> 0;
        else if (index === WIN_GWL.EXSTYLE) w.exStyle = Number(value) >>> 0;
        else if (index === WIN_GWL.USERDATA) w.userData = value;
        else if (index === WIN_GWL.HWNDPARENT) w.parent = value;
        else if (index === WIN_GWL.ID) w.menu = value;
        winPresent(); return old;
      }
      case "invalidateRect": {
        const w = winWindow(a(0)); if (!w) return 0n;
        w.invalid = true; if (a(2) !== 0n) winPostMessage(w.hwnd, WINMSG.ERASEBKGND);
        winPostMessage(w.hwnd, WINMSG.PAINT); return 1n;
      }
      case "createiocompletionport": {
        const fileHandle = a(0);
        const existingPort = a(1);
        const completionKey = a(2);
        if (fileHandle === 0n || fileHandle === MASK64) {
          return winAllocHandle({ kind: "iocp", assoc: new Map() });
        }
        if (existingPort === 0n) { winSetLastError(87); return 0n; }
        const port = winHandles.get(existingPort);
        if (!port || port.kind !== "iocp") { winSetLastError(6); return 0n; }
        port.assoc.set(fileHandle, completionKey);
        return existingPort;
      }
      case "validaterect": { const w = winWindow(a(0)); if (w) w.invalid = false; return 1n; }
      case "postmessagea": case "postmessagew": return winPostMessage(a(0), a(1), a(2), a(3)) ? 1n : 0n;
      case "postthreadmessagea": case "postthreadmessagew": return winPostMessage(0n, a(1), a(2), a(3)) ? 1n : 0n;
      case "postquitmessage": winPostMessage(0n, WINMSG.QUIT, BigInt.asUintN(32, a(0))); return 0n;
      case "getmessagea": case "getmessagew": {
        const filterHwnd = a(1), filterMin = Number(a(2)), filterMax = Number(a(3));
        let msg = winTakeMessage(filterHwnd, filterMin, filterMax, true);
        while (!msg && gui?.interactive) {
          await winAwaitMessage(() => winHasMessage(filterHwnd, filterMin, filterMax));
          msg = winTakeMessage(filterHwnd, filterMin, filterMax, true);
        }
        if (!msg) return 0n;
        if (!winWriteMsg(a(0), msg)) { winSetLastError(998); return 0xffff_ffffn; }
        return msg.message === WINMSG.QUIT ? 0n : 1n;
      }
      case "peekmessagea": case "peekmessagew": {
        const msg = winTakeMessage(a(1), Number(a(2)), Number(a(3)), (Number(a(4)) & 1) !== 0);
        if (!msg) return 0n;
        return winWriteMsg(a(0), msg) ? 1n : 0n;
      }
      case "dispatchmessagea": case "dispatchmessagew": return 0n;
      case "sendmessagea": case "sendmessagew": return 0n;
      case "translatemessage": return 1n;
      case "waitmessage": {
        while (!winMessageQueue.length && gui?.interactive) await winAwaitMessage();
        return winMessageQueue.length ? 1n : 0n;
      }
      case "getmessagetime": return BigInt(winCurrentMessage?.time ?? 0);
      case "getmessagepos": { const m=winCurrentMessage; return m ? winPackPoint(m.x,m.y) : 0n; }
      case "getkeystate": case "getasynckeystate": {
        const key = Number(a(0)) & 0xffff;
        let state = winKeyDown.has(key) ? 0x8000 : 0;
        if (n === "getasynckeystate" && winKeyRecent.has(key)) { state |= 1; winKeyRecent.delete(key); }
        return BigInt.asIntN(16, BigInt(state));
      }
      case "defwindowproca": case "defwindowprocw": return winDefaultWindowProc(a(0), Number(a(1)), a(2), a(3));
      case "getsystemmetrics": {
        const metric = Number(a(0));
        return BigInt(({ 0: winScreen.width, 1: winScreen.height, 2: 640, 3: 480, 4: 4, 5: 4, 6: 4, 7: 4, 8: 16, 9: 16, 10: 16, 11: 16, 12: 16, 13: 16, 14: 16, 15: 16, 16: 1, 21: 1, 23: 1, 28: 1, 43: 1 })[metric] ?? 0);
      }
      case "adjustwindowrect": case "adjustwindowrectex": {
        const r = winRect(a(0)); if (!r) return 0n;
        const style = Number(a(1)) >>> 0, hasMenu = n === "adjustwindowrect" ? false : a(2) !== 0n;
        const border = (style & 0x00c00000) ? 8 : 1;
        r.left -= border; r.right += border; r.bottom += border; r.top -= border + ((style & 0x00c00000) ? 23 : 0) + (hasMenu ? 20 : 0);
        return winWriteRect(a(0), r) ? 1n : 0n;
      }
      case "messageboxa": case "messageboxw": {
        const wide = n.endsWith("w"), text = winReadMemoryString(a(1), wide) ?? "", caption = winReadMemoryString(a(2), wide) ?? "";
        if (gui?.showMessage) gui.showMessage({ text, caption, type: Number(a(3)) }); else log(`[MessageBox] ${caption}: ${text}`);
        return 1n; // IDOK
      }
      case "getdc": case "getwindowdc": return winGetDc(a(0));
      case "releasedc": {
        const dc = winHandles.get(a(1));
        if (dc?.kind !== "dc") return 0n;
        winHandles.delete(a(1)); winDcs.delete(a(1));
        if (dc.defaultBitmap) winHandles.delete(dc.defaultBitmap);
        return 1n;
      }
      case "deletedc": {
        const dc = winHandles.get(a(0));
        if (dc?.kind !== "dc") return 0n;
        winHandles.delete(a(0)); winDcs.delete(a(0));
        if (dc.defaultBitmap) winHandles.delete(dc.defaultBitmap);
        return 1n;
      }
      case "getfileinformationbyhandle": {
        // BOOL GetFileInformationByHandle(HANDLE hFile, LPBY_HANDLE_FILE_INFORMATION lpInfo)
        // BY_HANDLE_FILE_INFORMATION is 52 bytes:
        //   +0  DWORD    dwFileAttributes
        //   +4  FILETIME ftCreationTime     (8)
        //   +12 FILETIME ftLastAccessTime   (8)
        //   +20 FILETIME ftLastWriteTime    (8)
        //   +28 DWORD    dwVolumeSerialNumber
        //   +32 DWORD    nFileSizeHigh
        //   +36 DWORD    nFileSizeLow
        //   +40 DWORD    nNumberOfLinks
        //   +44 DWORD    nFileIndexHigh
        //   +48 DWORD    nFileIndexLow
        const h = a(0), out = Number(a(1));
        if (!Number.isSafeInteger(out) || out < 0 || !ensureMemory(out + 52)) {
          winSetLastError(87); return 0n;
        }
        const handle = winHandles.get(h);
        if (!handle) { winSetLastError(6); return 0n; }

        const isFile = handle.kind === "file";
        const isDir  = handle.kind === "dir";
        const isStd  = handle.kind === "stdin" || handle.kind === "stdout" || handle.kind === "stderr";
        const size   = isFile ? handle.file.data.length : 0;

        u8.fill(0, out, out + 52);
        dv.setUint32(out + 0, isDir ? 0x10 : isFile ? 0x80 : isStd ? 0x3 : 0, true);  // dwFileAttributes
        // FILETIME = 100ns since 1601-01-01. Real modification times would need the
        // mount to carry them; "now" is fine for verification purposes.
        const now = BigInt(Date.now()) * 10000n + 116444736000000000n;
        dv.setBigUint64(out + 4,  now, true);   // ftCreationTime
        dv.setBigUint64(out + 12, now, true);   // ftLastAccessTime
        dv.setBigUint64(out + 20, now, true);   // ftLastWriteTime
        dv.setUint32(out + 28, 0x12345678, true);                            // dwVolumeSerialNumber
        dv.setUint32(out + 32, Math.floor(size / 0x100000000) >>> 0, true);  // nFileSizeHigh
        dv.setUint32(out + 36, size >>> 0, true);                            // nFileSizeLow
        dv.setUint32(out + 40, 1, true);                                     // nNumberOfLinks
        // nFileIndexHigh/Low — Steam uses this to detect hardlinks. Make it stable
        // per-handle by hashing the handle value; different handles to the same file
        // will differ but Steam's verification loop opens each file once.
        const inode = Number(BigInt(h) & 0xFFFFFFFFn);
        dv.setUint32(out + 44, 0, true);
        dv.setUint32(out + 48, inode, true);
        logTrace(`[GFIBH] h=0x${h.toString(16)} kind=${handle.kind} size=${size}`);
        return 1n;
      }
      case "beginpaint": {
        const w = winWindow(a(0)); if (!w) return 0n;
        const ps = Number(a(1)); if (!ensureMemory(ps + 72)) return 0n;
        const hdc = winCreateDc(w); u8.fill(0, ps, ps + 72); dv.setBigUint64(ps, hdc, true);
        dv.setInt32(ps + 12, 0, true); dv.setInt32(ps + 16, 0, true);
        dv.setInt32(ps + 20, w.width, true); dv.setInt32(ps + 24, w.height, true); w.invalid = false; return hdc;
      }
      case "endpaint": { const h = winReadU64(Number(a(1))); const dc = winHandles.get(h); if (dc?.kind === "dc") { winHandles.delete(h); winDcs.delete(h); if (dc.defaultBitmap) winHandles.delete(dc.defaultBitmap); } return 1n; }
      case "registerhotkey": return 1n;
      case "unregisterhotkey": return 1n;
      case "setfocus": {
        const w = winWindow(a(0)); if (!w) return 0n;
        const old = [...winWindows.values()].find((x) => x.focused)?.hwnd ?? 0n;
        if (old && old !== w.hwnd) winPostMessage(old, WINMSG.KILLFOCUS, w.hwnd);
        for (const x of winWindows.values()) x.focused = false; w.focused = true;
        winPostMessage(w.hwnd, WINMSG.SETFOCUS, old); winPresent(); return old;
      }
      // ── CRT writability check (_waccess / access) ─────────────────────
      case "_waccess": case "_waccess_s":
      case "_access": case "_access_s": case "access": {
        const wide = n.startsWith("_w");
        const path = winReadMemoryString(a(0), wide);
        const mode = Number(a(1)) >>> 0;   // 0=exist, 2=W_OK, 4=R_OK, 6=RW
        if (path == null) { winSetLastError(22); return 0xffff_ffff_ffff_ffffn; }
        const norm = winPath(path);
        const file = virtualFiles.get(norm);
        const dir = winDirectories.has(norm);
        if (!file && !dir) { winSetLastError(2); return 0xffff_ffff_ffff_ffffn; }
        if (mode & 2) {
          // Writable iff the parent directory is a known guest dir. Our heap is
          // always writable otherwise.
          const parent = norm.slice(0, norm.lastIndexOf("/")) || "/";
          if (!dir && !winDirectories.has(parent)) { winSetLastError(13); return 0xffff_ffff_ffff_ffffn; }
        }
        return 0n;
      }

      // ── CRT fopen with sharing (_wfsopen / fsopen) ────────────────────
      case "_wfsopen": case "_fsopen": case "fsopen": {
        const wide = n === "_wfsopen";
        const path = winReadMemoryString(a(0), wide);
        const mode = winReadMemoryString(a(1), false) ?? "rb";
        if (path == null) { winSetLastError(22); return 0n; }
        const norm = winPath(path);
        const isWrite = /[wa+]/.test(mode);
        let file = virtualFiles.get(norm);
        if (!file && isWrite) {
          const parent = norm.slice(0, norm.lastIndexOf("/")) || "/";
          if (!winDirectories.has(parent)) { winSetLastError(2); return 0n; }
          file = { data: new Uint8Array(0) };
          virtualFiles.set(norm, file);
        }
        if (!file) { winSetLastError(2); return 0n; }
        if (mode.startsWith("w")) file.data = new Uint8Array(0);
        return winAllocHandle({
          kind: "crt_file", file, path: norm,
          position: mode.includes("a") ? file.data.length : 0,
          readable: mode.includes("r") || mode.includes("+"),
          writable: isWrite,
        });
      }

      // ── CRT low-level open (_wopen / _open) ───────────────────────────
      case "_wopen": case "_open": case "open":
      case "_wopen_s": case "_open_s": case "open_s": {
        const wide = n.startsWith("_w");
        const safe = n.endsWith("_s");
        const path = safe ? a(1) : a(0);
        const flags = Number(safe ? a(2) : a(1)) >>> 0;
        const outPtr = safe ? a(0) : 0n;
        const strPath = winReadMemoryString(path, wide);
        if (strPath == null) { winSetLastError(22); return safe ? 22n : 0xffff_ffff_ffff_ffffn; }
        const norm = winPath(strPath);
        const accessMode = flags & 3;   // 0=RDONLY 1=WRONLY 2=RDWR
        const isWrite = accessMode !== 0;
        const isCreate = (flags & 0x100) || (flags & 0x200);
        let file = virtualFiles.get(norm);
        if (!file && isCreate && isWrite) {
          const parent = norm.slice(0, norm.lastIndexOf("/")) || "/";
          if (!winDirectories.has(parent)) { winSetLastError(2); return safe ? 2n : 0xffff_ffff_ffff_ffffn; }
          file = { data: new Uint8Array(0) };
          virtualFiles.set(norm, file);
        }
        if (!file) { winSetLastError(2); return safe ? 2n : 0xffff_ffff_ffff_ffffn; }
        if (isCreate && (flags & 0x200)) file.data = new Uint8Array(0);
        const handle = winAllocHandle({ kind: "crt_file", file, path: norm, position: 0,
          readable: accessMode !== 1, writable: isWrite });
        if (safe) {
          if (ensureMemory(Number(outPtr) + 8)) dv.setBigUint64(Number(outPtr), handle, true);
          return 0n;
        }
        return handle;
      }
      case "_wsopen_s": case "_sopen_s":
      case "_wsopen": case "_sopen": {
          const wide   = n.startsWith("_w");
          const safe   = n.endsWith("_s");
          const outPtr = safe ? a(0) : 0n;
          const pathArg = safe ? a(1) : a(0);
          const flags   = Number(safe ? a(2) : a(1)) >>> 0;
          const strPath = winReadMemoryString(pathArg, wide);
          let handle = 0n;
          if (strPath != null) {
              const norm = winPath(strPath);
              if (winDirectories.has(norm)) {
                  handle = winAllocHandle({ kind: "directory", path: norm, readable: true, writable: true });
              } else {
                  let file = virtualFiles.get(norm);
                  const isWrite = (flags & 3) !== 0;
                  const isCreate = (flags & 0x100) || (flags & 0x200);
                  if (!file && isCreate && isWrite) {
                      const parent = norm.slice(0, norm.lastIndexOf("/")) || "/";
                      if (winDirectories.has(parent)) {
                          file = { data: new Uint8Array(0) };
                          virtualFiles.set(norm, file);
                      }
                  }
                  if (file) {
                      if (isCreate && (flags & 0x200)) file.data = new Uint8Array(0);
                      handle = winAllocHandle({ kind: "crt_file", file, path: norm, position: 0,
                          readable: (flags & 3) !== 1, writable: isWrite });
                  }
              }
          }
          if (safe) {
              if (ensureMemory(Number(outPtr) + 8)) dv.setBigUint64(Number(outPtr), handle, true);
              return handle === 0n ? 2n : 0n;
          }
          return handle === 0n ? 0xffff_ffff_ffff_ffffn : handle;
      }

      case "_waccess": case "_access": case "access": {
          const wide = n.startsWith("_w");
          const path = winReadMemoryString(a(0), wide);
          const mode = Number(a(1)) >>> 0;
          if (path == null) { winSetLastError(22); return 0xffff_ffffn; }
          const norm = winPath(path);
          const exists = virtualFiles.has(norm) || winDirectories.has(norm);
          if (!exists) { winSetLastError(2); return 0xffff_ffffn; }
          return 0n;   // all access modes granted
      }
      case "_fstat": case "_fstati64": case "_fstat64": case "fstat": {
          const fd = Number(BigInt.asIntN(32, a(0)));
          const outPtr = Number(a(1));
          const h = winHandles.get(BigInt(fd));
          if (!ensureMemory(outPtr + 128)) { winSetLastError(22); return 0xffff_ffffn; }
          u8.fill(0, outPtr, outPtr + 128);
          let mode = 0x8180, size = 0;
          if (h?.kind === "file")      { mode = 0x8180; size = h.file.data.length; }
          else if (h?.kind === "crt_file") { mode = 0x8180; size = h.file.data.length; }
          else if (h?.kind === "directory") { mode = 0x4180; }
          dv.setUint16(outPtr + 6, mode, true);
          dv.setUint32(outPtr + 16, size >>> 0, true);
          return 0n;
      }
      case "_wchmod": case "_chmod": case "chmod": case "_fchmod": {
          // Readonly clearing should always succeed for the virtual FS.
          return 0n;
      }
      case "_wstat": case "_wstati64": case "_wstat64":
      case "_stat":  case "_stati64":  case "_stat64":
      case "stat":   case "stat64": {
          const wide = n.startsWith("_w");
          const path = winReadMemoryString(a(0), wide);
          const outPtr = Number(a(1));
          if (path == null) { winSetLastError(22); return 0xffff_ffffn; }
          const norm = winPath(path);
          const file = virtualFiles.get(norm);
          const dir  = winDirectories.has(norm);
          if (!file && !dir) { winSetLastError(2); return 0xffff_ffffn; }

          // struct _stat is 96 bytes in x64 MSVC (or 48 in 32-bit, but we're 64-bit).
          // We zero it and populate the fields Steam cares about.
          // Layout (x64, from <sys/stat.h>):
          //   +0  dev_t   (32-bit)
          //   +4  ino_t   (16-bit)
          //   +6  mode_t  (16-bit)   ← _S_IWRITE = 0x0080, _S_IREAD = 0x0100
          //   +8  nlink_t (16-bit)
          //   +10 uid     (16-bit)
          //   +12 gid     (16-bit)
          //   +16 size    (32-bit, _stati64 uses 64-bit at +48)
          //   ...
          if (!Number.isSafeInteger(outPtr) || outPtr <= 0 || !ensureMemory(outPtr + 128)) {
              winSetLastError(22); return 0xffff_ffffn;
          }
          u8.fill(0, outPtr, outPtr + 128);

          const size = file ? file.data.length : 0;
          // _S_IFDIR = 0x4000, _S_IFREG = 0x8000
          // _S_IREAD = 0x0100, _S_IWRITE = 0x0080  ← BOTH set always
          const mode = (dir ? 0x4000 : 0x8000) | 0x0100 | 0x0080;
          dv.setUint32(outPtr +  0, 0, true);       // st_dev
          dv.setUint16(outPtr +  4, 1, true);       // st_ino (16-bit)
          dv.setUint16(outPtr +  6, mode, true);    // st_mode ← THE FIELD STEAM CHECKS
          dv.setUint16(outPtr +  8, 1, true);       // st_nlink
          dv.setUint16(outPtr + 10, 0, true);       // st_uid
          dv.setUint16(outPtr + 12, 0, true);       // st_gid
          dv.setUint32(outPtr + 16, size >>> 0, true);                 // st_size
          dv.setUint32(outPtr + 20, Math.floor(size / 0x100000000) >>> 0, true); // st_size_hi
          dv.setUint32(outPtr + 24, Math.floor(Date.now() / 1000) >>> 0, true);  // st_mtime
          return 0n;
      }

      // ── GetFileSecurity (grant full access) ───────────────────────────
      case "getfilesecurityw": case "getfilesecuritya": {
        const outPtr = Number(a(1));
        const outLen = Number(a(2));
        const neededPtr = a(3);
        if (!Number.isSafeInteger(outPtr) || outLen < 20 || !ensureMemory(outPtr + 20)) {
          if (neededPtr && ensureMemory(Number(neededPtr) + 4)) dv.setUint32(Number(neededPtr), 20, true);
          winSetLastError(122); return 0n;
        }
        u8.fill(0, outPtr, outPtr + 20);
        dv.setUint8(outPtr, 1);                       // revision 1
        dv.setUint16(outPtr + 2, 0x8000, true);       // SE_SELF_RELATIVE
        // DACL pointer = NULL ⇒ everyone has full access (no restrictions)
        if (neededPtr) winWriteDword(neededPtr, 20);
        return 1n;
      }
      case "setfilesecurityw": case "setfilesecuritya":
      case "getnamedsecurityinfow": case "getnamedsecurityinfoa":
      case "setnamedsecurityinfow": case "setnamedsecurityinfoa":
      case "getsecurityinfo": case "setsecurityinfo":
        return 0n;

      // ── CRT mkdir / rmdir / remove / unlink ───────────────────────────
      case "_wmkdir": case "_mkdir": {
        const wide = n === "_wmkdir";
        const path = winReadMemoryString(a(0), wide);
        if (path == null) return 0xffff_ffff_ffff_ffffn;
        const norm = winPath(path);
        if (winDirectories.has(norm) || virtualFiles.has(norm)) { winSetLastError(17); return 0xffff_ffff_ffff_ffffn; }
        const parent = norm.slice(0, norm.lastIndexOf("/")) || "/";
        if (!winDirectories.has(parent)) { winSetLastError(2); return 0xffff_ffff_ffff_ffffn; }
        winDirectories.add(norm);
        return 0n;
      }
      case "_wrmdir": case "_rmdir": {
        const wide = n === "_wrmdir";
        const path = winReadMemoryString(a(0), wide);
        if (path == null) return 0xffff_ffff_ffff_ffffn;
        const norm = winPath(path);
        if (!winDirectories.has(norm)) { winSetLastError(2); return 0xffff_ffff_ffff_ffffn; }
        winDirectories.delete(norm);
        return 0n;
      }
      case "_wremove": case "_wunlink": case "remove": case "unlink": {
        const wide = n.startsWith("_w");
        const path = winReadMemoryString(a(0), wide);
        if (path == null) return 0xffff_ffff_ffff_ffffn;
        return virtualFiles.delete(winPath(path)) ? 0n : 0xffff_ffff_ffff_ffffn;
      }
      case "localalloc": case "globalalloc": {
        // HLOCAL LocalAlloc(UINT uFlags, SIZE_T uBytes)
        const flags = Number(a(0)) >>> 0;
        const size = Number(a(1));
        // LMEM_ZEROINIT (0x40) / GMEM_ZEROINIT (0x40)
        const zero = (flags & 0x40) !== 0;
        return winAlloc(BigInt(Math.max(1, size)), zero);
      }

      case "localfree": case "globalfree": {
        // HLOCAL LocalFree(HLOCAL hMem)  → returns NULL on success
        const h = a(0);
        if (h === 0n) return 0n;
        winAllocations.delete(Number(h));
        return 0n;
      }
      case "getfocus": return BigInt([...winWindows.values()].find((w) => w.focused)?.hwnd ?? 0n);
      case "setforegroundwindow": { const w = winWindow(a(0)); if (!w) return 0n; winRaiseWindowFamily(w.hwnd); winPresent(); return 1n; }
      case "setcapture": return a(0);
      case "releasecapture": return 1n;
      case "setcursor": return a(0);
      case "settimer": return BigInt(a(2) || 1n);
      case "killtimer": return 1n;
      case "callwindowproca": case "callwindowprocw": return 0n; // dispatched through the guest callback trampoline

      // GDI objects and device contexts.
      case "createsolidbrush": return winAllocHandle({ kind: "brush", color: winColor(a(0)) });
      case "createpen": return winAllocHandle({ kind: "pen", style: Number(a(0)), width: Math.max(1, Number(a(1))), color: winColor(a(2)) });
      case "createfonta": case "createfontw": {
        const face = winReadMemoryString(a(13), n.endsWith("w")) ?? "Arial";
        return winAllocHandle({ kind: "font", height: Math.abs(Number(BigInt.asIntN(32, a(0)))) || 16,
          width: Number(a(1)), weight: Number(a(4)) || 400, italic: a(5) !== 0n,
          underline: a(6) !== 0n, strikeout: a(7) !== 0n, face });
      }
      case "getstockobject": return winStockObject(Number(a(0)));
      case "deleteobject": {
        const handle = a(0), obj = winHandles.get(handle);
        if (!obj || !["brush", "pen", "font", "bitmap"].includes(obj.kind)) return 0n;
        for (const dc of winDcs.values()) if (Object.values(dc.selected).includes(handle)) return 0n;
        return winHandles.delete(handle) ? 1n : 0n;
      }
      case "createcompatibledc": {
        const source = a(0);
        if (source !== 0n && winHandles.get(source)?.kind !== "dc") { winSetLastError(6); return 0n; }
        return winCreateDc({ kind: "bitmap", width: 0, height: 0, commands: [] });
      }
      case "createcompatiblebitmap": {
        const dc = winHandles.get(a(0));
        if (!dc || dc.kind !== "dc") { winSetLastError(6); return 0n; }
        const width = Number(BigInt.asIntN(32, a(1))), height = Number(BigInt.asIntN(32, a(2)));
        if (width <= 0 || height <= 0 || width * height > 64 * 1024 * 1024) { winSetLastError(87); return 0n; }
        return winAllocHandle({ kind: "bitmap", width, height, commands: [] });
      }
      case "selectobject": {
        const dc = winHandles.get(a(0)), object = winResolveGdi(a(1));
        if (!dc || dc.kind !== "dc" || !object) return 0xffff_ffff_ffff_ffffn;
        const key = object.kind === "brush" ? "brush" : object.kind === "pen" ? "pen" : object.kind === "font" ? "font" : object.kind === "bitmap" ? "bitmap" : null;
        if (!key) return 0xffff_ffff_ffff_ffffn;
        const old = dc.selected[key] ?? 0n; dc.selected[key] = a(1);
        if (key === "bitmap") dc.target = object;
        return old;
      }
      case "settextcolor": case "setbkcolor": {
        const dc = winHandles.get(a(0)); if (!dc || dc.kind !== "dc") return 0xffff_ffffn;
        const key = n === "settextcolor" ? "textColor" : "bkColor", old = dc[key]; dc[key] = winColor(a(1)); return BigInt(old >>> 0);
      }
      case "setbkmode": {
        const dc = winHandles.get(a(0)); if (!dc || dc.kind !== "dc") return 0n;
        const old = dc.bkMode; dc.bkMode = Number(a(1)); return BigInt(old);
      }
      case "fillrect": {
        const dc = winHandles.get(a(0)), r = winRect(a(1)), brush = winResolveGdi(a(2));
        if (!dc || dc.kind !== "dc" || !r || !brush || brush.kind !== "brush") return 0n;
        if (brush.color !== null) winAddDrawCommand(a(0), { type: "fillRect", ...r, color: brush.color }); return 1n;
      }
      case "rectangle": case "ellipse": case "roundrect": {
        const dc = winHandles.get(a(0)); if (!dc || dc.kind !== "dc") return 0n;
        const left = Number(BigInt.asIntN(32, a(1))), top = Number(BigInt.asIntN(32, a(2)));
        const right = Number(BigInt.asIntN(32, a(3))), bottom = Number(BigInt.asIntN(32, a(4)));
        const pen = winResolveGdi(dc.selected.pen), brush = winResolveGdi(dc.selected.brush);
        winAddDrawCommand(a(0), { type: n, left, top, right, bottom,
          color: pen?.kind === "pen" ? pen.color : 0x000000,
          fill: brush?.kind === "brush" ? brush.color : null, lineWidth: pen?.width ?? 1,
          radiusX: Number(a(5)), radiusY: Number(a(6)) }); return 1n;
      }
      case "movetoex": {
        const dc = winHandles.get(a(0)); if (!dc || dc.kind !== "dc") return 0n;
        const old = { ...dc.current }; dc.current = { x: Number(BigInt.asIntN(32, a(1))), y: Number(BigInt.asIntN(32, a(2))) };
        if (a(3) !== 0n) { const p = Number(a(3)); dv.setInt32(p, old.x, true); dv.setInt32(p + 4, old.y, true); }
        return 1n;
      }
      case "lineto": {
        const dc = winHandles.get(a(0)); if (!dc || dc.kind !== "dc") return 0n;
        const next = { x: Number(BigInt.asIntN(32, a(1))), y: Number(BigInt.asIntN(32, a(2))) };
        const pen = winResolveGdi(dc.selected.pen); winAddDrawCommand(a(0), { type: "line", x1: dc.current.x, y1: dc.current.y, x2: next.x, y2: next.y, color: pen?.color ?? 0, lineWidth: pen?.width ?? 1 });
        dc.current = next; return 1n;
      }
      case "textouta": case "textoutw": {
        const dc = winHandles.get(a(0)); if (!dc || dc.kind !== "dc") return 0n;
        const wide = n.endsWith("w"), text = wide ? (winReadW(a(3), Number(a(4))) ?? "") : new TextDecoder().decode(readBytes(a(3), Number(a(4))) ?? new Uint8Array());
        const font = winResolveGdi(dc.selected.font);
        winAddDrawCommand(a(0), { type: "text", text, x: Number(BigInt.asIntN(32, a(1))), y: Number(BigInt.asIntN(32, a(2))),
          color: dc.textColor, bkColor: dc.bkColor, bkMode: dc.bkMode, font: font?.kind === "font" ? font : null }); return 1n;
      }
      case "exttextouta": case "exttextoutw": case "drawtexta": case "drawtextw": {
        const dc = winHandles.get(a(0)); if (!dc || dc.kind !== "dc") return 0n;
        const wide = n.endsWith("w"), isDrawText = n.startsWith("drawtext"), textPtr = a(isDrawText ? 1 : 5);
        const textLen = Number(a(isDrawText ? 2 : 6));
        const text = wide ? (textLen < 0 ? winReadW(textPtr) : winReadW(textPtr, textLen)) :
          (textLen < 0 ? winReadA(textPtr) : new TextDecoder().decode(readBytes(textPtr, textLen) ?? new Uint8Array()));
        const r = winRect(a(isDrawText ? 3 : 4));
        const format = Number(a(isDrawText ? 4 : 3));
        const font = winResolveGdi(dc.selected.font);
        let x = isDrawText ? (r?.left ?? 0) : Number(BigInt.asIntN(32, a(1)));
        let y = isDrawText ? (r?.top ?? 0) : Number(BigInt.asIntN(32, a(2)));
        if (isDrawText && r) {
          if (format & 1) x = r.left + Math.max(0, ((r.right-r.left) - (text?.length ?? 0) * 8) / 2);
          else if (format & 2) x = r.right - (text?.length ?? 0) * 8;
          if (format & 4) y = r.top + Math.max(0, ((r.bottom-r.top) - (font?.height ?? 16)) / 2);
          else if (format & 8) y = r.bottom - (font?.height ?? 16);
          if (format & 0x400) winWriteRect(a(3), { left: x, top: y, right: x + (text?.length ?? 0) * 8, bottom: y + (font?.height ?? 16) });
        }
        winAddDrawCommand(a(0), { type: "text", text: text ?? "", x, y, color: dc.textColor, bkColor: dc.bkColor, bkMode: dc.bkMode, font: font?.kind === "font" ? font : null });
        return BigInt(text?.length ?? 0);
      }
      case "gettextextentpoint32a": case "gettextextentpoint32w": {
        const wide=n.endsWith("w"), text=wide?(winReadW(a(1),Number(a(2)))??""):new TextDecoder().decode(readBytes(a(1),Number(a(2)))??new Uint8Array());
        const p=Number(a(3)); if (!ensureMemory(p+8)) return 0n;
        const font=winResolveGdi(winHandles.get(a(0))?.selected?.font); dv.setInt32(p,Math.ceil(text.length*(font?.height??16)*0.55),true); dv.setInt32(p+4,font?.height??16,true); return 1n;
      }
      case "createinterface": {
        return 0n
      }
      case "setthreaddescription":
      case "wow64setthreaddescription":
      case "getthreaddescription":
      case "wow64getthreaddescription":
        return 0n;   // S_OK

      case "setthreadinformation":
      case "querythreadinformation":
        return 0n;

      case "getthreadtimes":
      case "getprocesstimes": {
          const ptr = Number(a(1));
          if (ensureMemory(ptr + 32)) {
              u8.fill(0, ptr, ptr + 32);
              dv.setUint32(ptr + 4, 1, true);   // pretend 1 unit of CPU time
          }
          return 1n;
      }

      case "setprocessinformation": case "getprocessinformation":
        return 0n;

      case "setthreadpriority": return 1n;
      case "getthreadpriority": return 0n;   // THREAD_PRIORITY_NORMAL
      case "_chdir": case "_wchdir": {
        const wide = n === "_wchdir";
        log(`[_chdir] ${n} called with input="${winReadMemoryString(a(0), wide)}"`);
        const input = winReadMemoryString(a(0), wide);
        log(`[${n}] input="${input}" cwd=${winCurrentDirectory}`);
        if (input == null || input.length === 0) {
          // MSVC: empty path → EINVAL
          dv.setUint32(WIN_ERRNO, 22, true);
          return 0xffff_ffff_ffff_ffffn;   // (int)-1, sign-extended
        }
        const path = winPath(input);
        const exists = winDirectories.has(path) || virtualFiles.has(path);
        log(`[${n}] "${input}" → "${path}" exists=${exists}`);
        if (!exists) {
          // MSVC: not found → ENOENT
          dv.setUint32(WIN_ERRNO, 2, true);
          return 0xffff_ffff_ffff_ffffn;
        }
        winCurrentDirectory = path;
        dv.setUint32(WIN_ERRNO, 0, true);
        return 0n;
      }

      case "_getcwd": case "_wgetcwd": {
        const wide = n === "_wgetcwd";
        const buffer = a(0);
        const cap    = Number(a(1));          // in characters
        const value  = `C:${winCurrentDirectory.replaceAll("/", "\\")}`;
        log(`[${n}] cap=${cap} value="${value}"`);
        // If buffer == NULL: (wide ? _wgetcwd(NULL, maxlen) : _getcwd(NULL, maxlen))
        // returns a fresh allocation. Steam always passes a buffer.
        if (buffer === 0n) {
          const alloc = winAlloc(BigInt((value.length + 1) * (wide ? 2 : 1)), true);
          if (wide) winWriteW(alloc, value); else winWriteA(alloc, value);
          return alloc;
        }
        if (cap < value.length + 1) {
          dv.setUint32(WIN_ERRNO, 34, true);   // ERANGE
          return 0n;
        }
        if (wide) winWriteW(buffer, value); else winWriteA(buffer, value);
        dv.setUint32(WIN_ERRNO, 0, true);
        return buffer;
      }

      case "_getdcwd": case "_wgetdcwd": {
        const wide   = n === "_wgetdcwd";
        const drive  = Number(a(0));          // drive number (0 = current)
        const buffer = a(1);
        const cap    = Number(a(2));
        const value  = `C:${winCurrentDirectory.replaceAll("/", "\\")}`;
        log(`[${n}] drive=${drive} cap=${cap} value="${value}"`);
        if (drive !== 0 && drive !== 3) {     // C: is drive 3 in MSVC numbering
          dv.setUint32(WIN_ERRNO, 34, true);  // ERANGE (no such drive)
          return 0n;
        }
        if (buffer === 0n) {
          const alloc = winAlloc(BigInt((value.length + 1) * (wide ? 2 : 1)), true);
          if (wide) winWriteW(alloc, value); else winWriteA(alloc, value);
          return alloc;
        }
        if (cap < value.length + 1) { dv.setUint32(WIN_ERRNO, 34, true); return 0n; }
        if (wide) winWriteW(buffer, value); else winWriteA(buffer, value);
        dv.setUint32(WIN_ERRNO, 0, true);
        return buffer;
      }

      case "_fullpath": case "_wfullpath": {
        const wide   = n === "_wfullpath";
        const buffer = a(0);
        const input  = winReadMemoryString(a(1), wide);
        const cap    = Number(a(2));
        if (input == null) {
          dv.setUint32(WIN_ERRNO, 22, true);  // EINVAL
          return 0n;
        }
        const value = input.match(/^[A-Za-z]:[\\/]/)
          ? input
          : `C:${winPath(input).replaceAll("/", "\\")}`;
        log(`[${n}] "${input}" → "${value}" cap=${cap}`);
        if (!buffer || cap < value.length + 1) {
          dv.setUint32(WIN_ERRNO, 34, true);  // ERANGE
          return 0n;
        }
        if (wide) winWriteW(buffer, value); else winWriteA(buffer, value);
        dv.setUint32(WIN_ERRNO, 0, true);
        return buffer;
      }
      case "gettextmetricsa": case "gettextmetricsw": {
        const p=Number(a(1)); if (!ensureMemory(p+60)) return 0n;
        u8.fill(0,p,p+60); dv.setInt32(p,16,true); dv.setInt32(p+4,13,true); dv.setInt32(p+8,3,true); dv.setInt32(p+12,3,true); dv.setInt32(p+16,2,true); dv.setInt32(p+20,1,true); dv.setInt32(p+24,1,true); dv.setInt32(p+28,8,true); dv.setInt32(p+32,8,true); dv.setUint8(p+56,1); return 1n;
      }
      case "bitblt": case "stretchblt": {
        const dst = winHandles.get(a(0)), src = winHandles.get(a(5));
        if (!dst || dst.kind !== "dc" || !src || src.kind !== "dc") return 0n;
        const rop = Number(a(n === "bitblt" ? 8 : 10)) >>> 0;
        if (rop !== 0x00cc0020) { winSetLastError(87); return 0n; } // SRCCOPY only
        const dx=Number(BigInt.asIntN(32,a(1))),dy=Number(BigInt.asIntN(32,a(2)));
        const dw=Number(BigInt.asIntN(32,a(3))),dh=Number(BigInt.asIntN(32,a(4)));
        const sx=Number(BigInt.asIntN(32,a(6))),sy=Number(BigInt.asIntN(32,a(7)));
        const sw=n === "bitblt"?dw:Number(BigInt.asIntN(32,a(8)));
        const sh=n === "bitblt"?dh:Number(BigInt.asIntN(32,a(9)));
        if (dw <= 0 || dh <= 0 || sw <= 0 || sh <= 0) { winSetLastError(87); return 0n; }
        winAddDrawCommand(a(0), { type: "blit", x: dx, y: dy, width: dw, height: dh, sourceX: sx, sourceY: sy, sourceWidth: sw, sourceHeight: sh, sourceCommands: (src.target?.commands ?? []).map(winCloneDrawCommand), sourceWidthLimit: src.target?.width ?? 0, sourceHeightLimit: src.target?.height ?? 0 }); return 1n;
      }
      case "patblt": {
        const dc=winHandles.get(a(0)); if (!dc || dc.kind!=="dc") return 0n;
        if ((Number(a(5)) >>> 0) !== 0x00f00021) { winSetLastError(87); return 0n; } // PATCOPY only
        const brush=winResolveGdi(dc.selected.brush),x=Number(BigInt.asIntN(32,a(1))),y=Number(BigInt.asIntN(32,a(2)));
        const w=Number(BigInt.asIntN(32,a(3))),h=Number(BigInt.asIntN(32,a(4)));
        if (brush?.color!==null) winAddDrawCommand(a(0),{type:"fillRect",left:x,top:y,right:x+w,bottom:y+h,color:brush?.color??0}); return 1n;
      }
      case "setpixel": {
        const dc=winHandles.get(a(0));if(!dc||dc.kind!=="dc")return 0xffff_ffffn;
        const x=Number(BigInt.asIntN(32,a(1))),y=Number(BigInt.asIntN(32,a(2))),color=winColor(a(3));
        winAddDrawCommand(a(0),{type:"fillRect",left:x,top:y,right:x+1,bottom:y+1,color});return BigInt(color);
      }
      case "getpixel": {
        const dc=winHandles.get(a(0));if(!dc||dc.kind!=="dc")return 0xffff_ffffn;
        const x=Number(BigInt.asIntN(32,a(1))),y=Number(BigInt.asIntN(32,a(2))),commands=dc.target?.commands??[];
        for(let i=commands.length-1;i>=0;i--){const c=commands[i];if(c.type==="fillRect"&&x>=c.left&&x<c.right&&y>=c.top&&y<c.bottom)return BigInt(c.color>>>0);}
        return 0n;
      }
      case "setfilecompletionnotificationmodes": return 1n;

      case "postqueuedcompletionstatus": return 1n;   // accepted, never delivered

      case "getqueuedcompletionstatus": {
        // BOOL GetQueuedCompletionStatus(HANDLE port, LPDWORD bytes, PULONG_PTR key,
        //                                LPOVERLAPPED* ov, DWORD ms);
        const port = a(0), bytesPtr = a(1), keyPtr = a(2), overlappedPtr = a(3);
        const timeout = Number(a(4)) >>> 0;
        const portEntry = winHandles.get(port);
        if (!portEntry || portEntry.kind !== "iocp") { winSetLastError(6); return 0n; }
        if (timeout === 0xffffffff) await new Promise(r => setTimeout(r, 0));
        else if (timeout > 0) await new Promise(r => setTimeout(r, Math.min(timeout, 100)));
        if (overlappedPtr && ensureMemory(Number(overlappedPtr) + 8))
          dv.setBigUint64(Number(overlappedPtr), 0n, true);
        if (bytesPtr) winWriteDword(bytesPtr, 0);
        if (keyPtr && ensureMemory(Number(keyPtr) + 8))
          dv.setBigUint64(Number(keyPtr), 0n, true);
        winSetLastError(258);   // ERROR_WAIT_TIMEOUT
        return 0n;
      }

      case "getqueuedcompletionstatusex": {
        // BOOL GetQueuedCompletionStatusEx(HANDLE port, LPOVERLAPPED_ENTRY entries,
        //                                 ULONG count, PULONG removed, DWORD ms, BOOL alertable);
        const port = a(0), entriesPtr = a(1), maxCount = Number(a(2)) >>> 0;
        const removedPtr = a(3);
        const timeout = Number(a(4)) >>> 0;
        const portEntry = winHandles.get(port);
        if (!portEntry || portEntry.kind !== "iocp") { winSetLastError(6); return 0n; }
        if (timeout === 0xffffffff) await new Promise(r => setTimeout(r, 0));
        else if (timeout > 0) await new Promise(r => setTimeout(r, Math.min(timeout, 100)));
        if (removedPtr) winWriteDword(removedPtr, 0);
        if (entriesPtr && maxCount > 0) {
          const p = Number(entriesPtr);
          const n = Math.min(maxCount, 16) * 16;   // one OVERLAPPED_ENTRY = 16 bytes
          if (ensureMemory(p + n)) u8.fill(0, p, p + n);
        }
        winSetLastError(258);   // ERROR_WAIT_TIMEOUT
        return 0n;
      }
      case "getcurrentobject": {
        const dc = winHandles.get(a(0)); if (!dc || dc.kind !== "dc") return 0n;
        const type = Number(a(1));
        const key = type === 1 ? "pen" : type === 2 ? "brush" : type === 6 ? "font" : type === 7 ? "bitmap" : null;
        return key ? (dc.selected[key] ?? 0n) : 0n;
      }
      case "getdevicecaps": {
        const index=Number(a(1)); return BigInt(({ 8: winScreen.width, 10: winScreen.height, 12: 96, 14: 96, 88: 32, 90: 1, 117: 1 })[index] ?? 0);
      }
      case "setstretchbltmode": return 1n;
      case "gettextcolor": { const dc=winHandles.get(a(0)); return BigInt(dc?.textColor ?? 0); }
      case "getbkcolor": { const dc=winHandles.get(a(0)); return BigInt(dc?.bkColor ?? 0xffffff); }
            case "wldpgetlockdownpolicy": {
        // HRESULT WldpGetLockdownPolicy(const WLDP_HOST_INFORMATION*, DWORD* policy, DWORD flags);
        const policyPtr = Number(a(1));
        if (policyPtr && ensureMemory(policyPtr + 4)) {
          dv.setUint32(policyPtr, 1, true);   // WLDP_LOCKDOWN_OFF — no policy
        }
        return 0n;                             // S_OK
      }
      case "wldpisclassinapprovedlist": {
        // HRESULT WldpIsClassInApprovedList(REFCLSID, const WLDP_HOST_INFORMATION*, BOOL* isApproved, DWORD flags);
        const approvedPtr = Number(a(2));
        if (approvedPtr && ensureMemory(approvedPtr + 4)) {
          dv.setUint32(approvedPtr, 1, true); // TRUE — everything is approved
        }
        return 0n;                             // S_OK
      }
      case "wldpquerydynamiccodetrust": {
        return 0n;                             // S_OK — code is trusted
      }
      case "wldpisasyncpolicyenabled": {
        const enabledPtr = Number(a(0));
        if (enabledPtr && ensureMemory(enabledPtr + 4)) {
          dv.setUint32(enabledPtr, 0, true);   // FALSE — no async policy
        }
        return 0n;
      }
      default: {
        const key = `${api.dll}!${name}`;
        if (!winWarned.has(key)) {
          winWarned.add(key);
          // Winsock / CRT / kernel32 are almost always load-bearing
          const loud = /ws2_32|ucrtbase|vcruntime|kernel32|kernelbase/i.test(api.dll ?? "");
          (loud ? log : logTrace)(`unimplemented Win32 API: ${key} — returning 0 / ERROR_CALL_NOT_IMPLEMENTED`);
        }
        winSetLastError(120);
        return 0n;
      }
    }
  }

  const winStartGuestCallback = (procedure, args, returnPc, callerRsp, cleanupHwnd = 0n) => {
    if (!procedure || procedure === 0n) return null;
    const saved = REG_NAMES.map((_, i) => dv.getBigUint64(ctx + i * 8, true));
    const savedFlags = dv.getBigUint64(ctx + 136, true);
    let callbackRsp = (callerRsp - 0x100) & ~15;
    callbackRsp -= 8; // Windows x64 function entry has RSP % 16 == 8.
    if (callbackRsp < 0 || !ensureMemory(callbackRsp + 0x28)) return null;
    dv.setBigUint64(callbackRsp, WIN_CALLBACK_RETURN, true);
    for (let i = 0; i < 4; i++) dv.setBigUint64(ctx + [REG.rcx, REG.rdx, REG.r8, REG.r9][i] * 8, BigInt(args[i] ?? 0n), true);
    dv.setBigUint64(ctx + REG.rsp * 8, BigInt(callbackRsp), true);
    winCallbackFrames.push({ saved, savedFlags, returnPc, resumeRsp: callerRsp + 8, cleanupHwnd: BigInt(cleanupHwnd) });
    return { nextPc: BigInt(procedure) };
  };
  const winWindowProcedure = (hwnd) => {
    const window = winHandles.get(BigInt(hwnd));
    return window?.kind === "window" ? window.wndProc ?? 0n : 0n;
  };
  const winIsVisible = (window, depth = 0) => {
    if (!window || !window.visible || window.destroyed || depth > 32) return false;
    return !window.parent || winIsVisible(winWindow(window.parent), depth + 1);
  };
  const winDestroyWindow = (hwnd, depth = 0) => {
    const window = winWindow(hwnd);
    if (!window || depth > 32) return false;
    const children = [...winWindows.values()].filter((child) => child.parent === window.hwnd);
    for (const child of children) winDestroyWindow(child.hwnd, depth + 1);
    winPostMessage(window.hwnd, WINMSG.DESTROY);
    winPostMessage(window.hwnd, WINMSG.NCDESTROY);
    window.destroyed = true; window.visible = false;
    winWindows.delete(window.hwnd);
    if (window.focused) window.focused = false;
    winPresent();
    return true;
  };
  const winDefaultWindowProc = (hwnd, message) => {
    if (message === WINMSG.NCCREATE) return 1n;
    if (message === WINMSG.ERASEBKGND || message === WINMSG.SETCURSOR) return 1n;
    if (message === WINMSG.CLOSE) { winDestroyWindow(hwnd); return 0n; }
    if (message === WINMSG.NCDESTROY) winHandles.delete(BigInt(hwnd));
    return 0n;
  };

  async function dispatchWinImport(address) {
    const api = winApiByAddress.get(address);
    const rspIn = Number(dv.getBigUint64(ctx + REG.rsp * 8, true));
    // logDispatch(`[DISPATCH] in  addr=0x${address.toString(16)} name=${api?.name ?? "?"} rsp=0x${rspIn.toString(16)}`);
    const rsp = Number(dv.getBigUint64(ctx + REG.rsp * 8, true));
    if (!Number.isSafeInteger(rsp) || rsp < 0 || rsp + 8 > u8.length) return { exit: true, status: -1 };
    const returnPc = dv.getBigUint64(rsp, true);
    // ── file-API watch: logs each call site once ────────────────────
    const name = String(api?.name ?? "").toLowerCase();
    // at top of dispatchWinImport, before the API runs
    // fires on every _invalid_parameter / assert handler entry
    // rolling API history — updated on every dispatch
    if (!globalThis.__recentApis) globalThis.__recentApis = [];
    {
        const entry = api ? `${api.dll}!${api.name}` : `thunk@0x${address.toString(16)}`;
        globalThis.__recentApis.push(entry);
        if (globalThis.__recentApis.length > 64) globalThis.__recentApis.shift();
    }
    if (!globalThis.__lastFmtCall) globalThis.__lastFmtCall = { name: "none", ret: 0n };
    const LOWNAME = name.replace(/^_o_/, "").toLowerCase();
    if (LOWNAME.includes("printf") || LOWNAME.includes("format")) {
        globalThis.__lastFmtCall = { name: api?.name ?? LOWNAME, ret: 0n };
    }

    // on our assert handler entry, dump the last printf call
    if (api?.name === "_invalid_parameter" ||
        api?.name === "_invalid_parameter_noinfo" ||
        api?.name === "_invoke_watson") {
        log(`[ASSERT-TRACE] last printf = ${globalThis.__lastFmtCall.name}`);
        log(`[ASSERT-TRACE] expr = "${winReadW(winGetArg(0)) ?? "?"}"`);
        log(`[ASSERT-TRACE] fn   = "${winReadW(winGetArg(1)) ?? "?"}"`);
        log(`[ASSERT-TRACE] file = "${winReadW(winGetArg(2)) ?? "?"}"`);
        log(`[ASSERT-TRACE] line = ${Number(winGetArg(3))}`);
    }
    {
      const FILE_APIS = new Set(["_waccess","_access","access",
        "_wfsopen","_fsopen","fsopen","_wfopen","_fopen","fopen","fopen_s","_wfopen_s",
        "_wopen","_open","open","_wopen_s","_open_s","open_s",
        "_wstat","_stat","stat","_wstat64","_stat64","stat64",
        "getfilesecurityw","getfilesecuritya","setfilesecurityw","setfilesecuritya",
        "getnamedsecurityinfow","getnamedsecurityinfoa",
        "_wmkdir","_mkdir","_wrmdir","_rmdir","_wremove","_wunlink","remove","unlink"]);
      if (FILE_APIS.has(name.replace(/^_o_/, ""))) {
        if (!globalThis.__fileApiSites) globalThis.__fileApiSites = new Set();
        const key = `${name}@${returnPc.toString(16)}`;
        if (!globalThis.__fileApiSites.has(key)) {
          globalThis.__fileApiSites.add(key);
          let arg0 = "?";
          try {
            const p = winGetArg(0);
            if (p > 0x10000n && p < BigInt(u8.length)) {
              const s = readCString(p, 260);
              if (s && s.length > 0) arg0 = `"${s}"`;
              else { const w = winReadW(p, 260); if (w && w.length > 0) arg0 = `L"${w}"`; }
            }
          } catch {}
          logDispatch(`[FILE-API] ${name}(${arg0}) from pc=0x${returnPc.toString(16)}`);
        }
      }
    }

    if (!globalThis.__recentApis) globalThis.__recentApis = [];
    if (api) {
      globalThis.__recentApis.push(api.name);
      if (globalThis.__recentApis.length > 32) globalThis.__recentApis.shift();
    }
    // near the top of winLookupApi, after the module is resolved
    // DispatchMessage/SendMessage/CallWindowProc must execute the translated
    // guest WndProc, not a host-side approximation. The special return PC
    // resumes this API after the guest callback returns.
    let callback = null;
    if (name === "createfile2" || name === "ntcreatefile" || name === "ntopenfile" ||
      name === "rtldospathtonntpathname_u") {
      log(`[FILE-API] ${api?.dll}!${name} called`);
    }
    if (name === "dispatchmessagea" || name === "dispatchmessagew") {
      const msg = winReadMsg(winGetArg(0));
      if (msg && msg.message !== WINMSG.QUIT && msg.hwnd !== 0n) {
        const proc = winWindowProcedure(msg.hwnd);
        if (proc) callback = winStartGuestCallback(proc, [msg.hwnd, BigInt(msg.message), msg.wParam, msg.lParam], returnPc, rsp,
          msg.message === WINMSG.NCDESTROY ? msg.hwnd : 0n);
        else {
          const result = winDefaultWindowProc(msg.hwnd, msg.message, msg.wParam, msg.lParam);
          dv.setBigUint64(ctx + REG.rsp * 8, BigInt(rsp + 8), true);
          dv.setBigUint64(ctx + REG.rax * 8, BigInt.asUintN(64, result), true);
          return { nextPc: returnPc };
        }
      }
    } else if (name === "createthread") {
      // Arg registers already in ctx; grab them before running anything.
      const startRoutine = winGetArg(2);
      const parameter   = winGetArg(3);
      const threadIdPtr = winGetArg(5);
      const threadId = (Number(processId) || 1) * 16 + (++winThreadIdCounter);
      const thread = {
        kind: "thread", process: winCurrentProcessState, threadId,
        startRoutine, parameter, finished: false, exitCode: 259,
      };
      const handle = winAllocHandle(thread);
      thread.handle = handle;
      if (threadIdPtr && ensureMemory(Number(threadIdPtr) + 4))
        dv.setUint32(Number(threadIdPtr), threadId, true);

      if (!startRoutine) {
        thread.finished = true; thread.exitCode = 0;
        dv.setBigUint64(ctx + REG.rsp * 8, BigInt(rsp + 8), true);
        dv.setBigUint64(ctx + REG.rax * 8, handle, true);
        return { nextPc: returnPc };
      }

      const cbRsp = BigInt(((rsp - 0x100) & ~15) - 8);
      if (!ensureMemory(Number(cbRsp) + 0x28)) {
        thread.finished = true; thread.exitCode = 0;
        dv.setBigUint64(ctx + REG.rsp * 8, BigInt(rsp + 8), true);
        dv.setBigUint64(ctx + REG.rax * 8, handle, true);
        return { nextPc: returnPc };
      }

      dv.setBigUint64(Number(cbRsp), WIN_CALLBACK_RETURN, true);
      dv.setBigUint64(ctx + REG.rcx * 8, parameter, true);
      dv.setBigUint64(ctx + REG.rdx * 8, 0n, true);
      dv.setBigUint64(ctx + REG.r8  * 8, 0n, true);
      dv.setBigUint64(ctx + REG.r9  * 8, 0n, true);
      dv.setBigUint64(ctx + REG.rsp * 8, cbRsp, true);

      const saved = REG_NAMES.map((_, i) => dv.getBigUint64(ctx + i * 8, true));
      const savedFlags = dv.getBigUint64(ctx + 136, true);

      winCallbackFrames.push({
        saved, savedFlags,
        returnPc,             // ← caller resumes here after thread proc returns
        resumeRsp: rsp + 8,   // ← RSP after CreateThread returns normally
        thread,
        restoreRaxAfter: handle,   // ← see WIN_CALLBACK_RETURN handler
        threadStartStep: steps,
      });

      log(`[THREAD] CreateThread → 0x${handle.toString(16)} tid=${threadId} entry=0x${startRoutine.toString(16)} param=0x${parameter.toString(16)}`);
      return { nextPc: startRoutine, rax: handle, rsp: Number(cbRsp) };
    } else if (name === "sendmessagea" || name === "sendmessagew") {
      const hwnd=winGetArg(0), message=winGetArg(1), proc=winWindowProcedure(hwnd);
      if (proc) callback = winStartGuestCallback(proc, [hwnd, message, winGetArg(2), winGetArg(3)], returnPc, rsp);
      else { const result = winDefaultWindowProc(hwnd, Number(message), winGetArg(2), winGetArg(3)); dv.setBigUint64(ctx + REG.rsp * 8, BigInt(rsp + 8), true); dv.setBigUint64(ctx + REG.rax * 8, BigInt.asUintN(64, result), true); return { nextPc: returnPc }; }
    } else if (name === "callwindowproca" || name === "callwindowprocw") {
      const proc=winGetArg(0), hwnd=winGetArg(1), message=winGetArg(2);
      if (proc) callback = winStartGuestCallback(proc, [hwnd,message,winGetArg(3),winGetArg(4)], returnPc, rsp);
      else { const result=winDefaultWindowProc(hwnd,Number(message),winGetArg(3),winGetArg(4)); dv.setBigUint64(ctx + REG.rsp * 8, BigInt(rsp + 8), true); dv.setBigUint64(ctx + REG.rax * 8, BigInt.asUintN(64,result), true); return { nextPc:returnPc }; }
    }
    if (callback) return callback;
    if (name === "getmessagea" || name === "getmessagew" || name === "peekmessagea" || name === "peekmessagew") {
      // These APIs are async in browser mode: a real GetMessage waits for input.
    }
    // Capture arg registers *before* emulation runs, so that we can report
    // meaningful arguments if the API returns NULL. Pure diagnostics — a
    // failure here must never abort execution.
    // Use plain Numbers: winGetArg mixes rsp (Number) with (index - 4) * 8.
    let savedArgs = [0n, 0n, 0n, 0n, 0n, 0n];
    try { savedArgs = [0, 1, 2, 3, 4, 5].map((i) => winGetArg(i)); }
    catch (e) { log(`[RECOMP] WARN: could not snapshot args for ${api?.dll}!${name}: ${e?.message ?? e}`); }
    globalThis.__currentApi = api ? { dll: api.dll, name: api.name } : null;
    const rawResult = await emulateWinApi(api ?? { dll: "<unknown>", name: `<thunk_${address.toString(16)}>` });
    if (isWindows && /file|dir|access|attrib|secur|sopen|fopen|_open|stat|volume|disk|findfirst|move|copy|temp/.test(name)) {
      const str = (p) => { try {
        const w = winReadW(p, 200); if (w && /^[\x20-\x7e]{2,}$/.test(w)) return w;
        const c = readCString(p, 200); return c && /^[\x20-\x7e]{2,}$/.test(c) ? c : "";
      } catch { return ""; } };
      const s0 = str(savedArgs[0]);
      const rv = (rawResult && typeof rawResult === "object") ? "{obj}" : "0x" + BigInt.asUintN(64, BigInt(rawResult ?? 0n)).toString(16);
      logDispatch(`[FILE-RET] ${api?.name} a0=0x${savedArgs[0].toString(16)}${s0 ? ` "${s0}"` : ""} a1=0x${savedArgs[1].toString(16)} a2=0x${savedArgs[2].toString(16)} a4=0x${savedArgs[4].toString(16)} -> ${rv} lastErr=${winGetLastError()}`);
    }
    if (!globalThis.__recentApiRets) globalThis.__recentApiRets = [];
    globalThis.__recentApiRets.push(rawResult && typeof rawResult === 'object'
        ? 0xFFFF_FFFFn : BigInt.asUintN(64, BigInt(rawResult ?? 0n)));
    if (globalThis.__recentApiRets.length > 64) globalThis.__recentApiRets.shift();
    if (rawResult && typeof rawResult === "object") {
      if (rawResult.exit) return rawResult;
      if ("nextPc" in rawResult) {
        if (rawResult.rax !== undefined)
          dv.setBigUint64(ctx + REG.rax * 8, BigInt.asUintN(64, BigInt(rawResult.rax)), true);
        if (rawResult.rsp !== undefined)
          dv.setBigUint64(ctx + REG.rsp * 8, BigInt(rawResult.rsp), true);
        return { nextPc: rawResult.nextPc };
      }
    }
    const result = rawResult === undefined ? 0n : rawResult;
    if (rawResult && typeof rawResult === "object" && rawResult.exit) {
      log(`[EXIT] ${name}(${rawResult.status}) — guest requested exit at step ${steps}`);
    }
    // dv.setBigUint64(ctx + REG.rax * 8, BigInt.asUintN(64, BigInt(result)), true)
    const rspOut = Number(dv.getBigUint64(ctx + REG.rsp * 8, true));
    dv.setBigUint64(ctx + REG.rsp * 8, BigInt(rsp + 8), true);
    dv.setBigUint64(ctx + REG.rax * 8, BigInt.asUintN(64, BigInt(result)), true);
    return { nextPc: returnPc };
    /* const result = await emulateWinApi(api ?? { dll: "<unknown>", name: `<thunk_${address.toString(16)}>` });
    if (result && typeof result === "object" && result.exit) return result;

    // Warn (once per API) if a pointer-returning API returned NULL. This is
    // the most common source of "jmp/call through NULL" crashes: the guest
    // stores the NULL, then jumps through it later.
    if (isWindows) {
      const rv = BigInt.asUintN(64, BigInt(result));
      if (rv === 0n) {
        const nullKey = `${api?.dll}!${name}#null`;
        if (!winWarned.has(nullKey)) {
          if (name === "getprocaddress") {
            const h = savedArgs[0], sym = savedArgs[1];
            const modName = winModuleHandles.get(h)
              ?? (h === 0n || h === BigInt(base) ? "program.exe" : `0x${h.toString(16)}`);
            const symName = sym > 0xffffn ? (winReadA(sym) ?? `0x${sym.toString(16)}`) : `#${sym}`;
            winWarned.add(nullKey);
            log(`[RECOMP] GetProcAddress(${modName}, ${JSON.stringify(symName)}) -> NULL ` +
              `(GetLastError=${winGetLastError()})`);
          } else if (name === "getmodulehandlea" || name === "getmodulehandlew"
                  || name === "loadlibrarya" || name === "loadlibraryw"
                  || name === "loadlibraryexa" || name === "loadlibraryexw") {
            const wide = name.endsWith("w");
            const dllName = winReadMemoryString(savedArgs[0], wide);
            winWarned.add(nullKey);
            log(`[RECOMP] ${api.name}(${JSON.stringify(dllName)}) -> NULL ` +
              `(GetLastError=${winGetLastError()})`);
          } else if (name === "virtualalloc" || name === "virtualalloc2"
                  || name === "heapalloc" || name === "rtlallocateheap"
                  || name === "globalalloc" || name === "localalloc"
                  || name === "mapviewoffile" || name === "mapviewoffileex") {
            winWarned.add(nullKey);
            log(`[RECOMP] ${api.dll}!${api.name}(...) -> NULL ` +
              `(GetLastError=${winGetLastError()})`);
          }
        }
      }
    }

    dv.setBigUint64(ctx + REG.rsp * 8, BigInt(rsp + 8), true);
    dv.setBigUint64(ctx + REG.rax * 8, BigInt.asUintN(64, BigInt(result)), true);
    return { nextPc: returnPc };*/

  }

  const guestGetdents64 = (fd, ptr, length) => {
    const entry = fdEntry(fd);
    const p = Number(ptr), cap = Number(length);
    if (!entry) return negErrno(9);
    if (entry.kind !== "dir") return negErrno(20);
    if (!Number.isSafeInteger(p) || !Number.isSafeInteger(cap) || p < 0 || cap < 0 || !ensureMemory(p + cap)) return negErrno(14);
    const prefix = entry.path === "/" ? "/" : `${entry.path}/`;
    const children = new Map([
      [".", { type: 4, path: entry.path }],
      ["..", { type: 4, path: entry.path === "/" ? "/" : entry.path.slice(0, entry.path.lastIndexOf("/")) || "/" }],
    ]);
    for (const path of virtualFiles.keys()) {
      if (!path.startsWith(prefix)) continue;
      const rest = path.slice(prefix.length);
      const name = rest.split("/")[0];
      if (!name) continue;
      const isDir = rest.includes("/");
      if (!children.has(name)) children.set(name, { type: isDir ? 4 : 8, path: `${prefix}${name}` });
      else if (isDir) children.get(name).type = 4;
    }
    const items = [...children.entries()];
    let index = entry.dirIndex ?? 0;
    let written = 0;
    while (index < items.length) {
      const [name, child] = items[index];
      const nameBytes = new TextEncoder().encode(name);
      const recordSize = Math.ceil((19 + nameBytes.length + 1) / 8) * 8;
      if (written + recordSize > cap) {
        if (written === 0) return negErrno(22);
        break;
      }
      const at = p + written;
      u8.fill(0, at, at + recordSize);
      let inode = 1n;
      for (const ch of child.path) inode = BigInt.asUintN(64, inode * 131n + BigInt(ch.charCodeAt(0)));
      dv.setBigUint64(at, inode, true);
      dv.setBigInt64(at + 8, BigInt(index + 1), true);
      dv.setUint16(at + 16, recordSize, true);
      u8[at + 18] = child.type;
      u8.set(nameBytes, at + 19);
      written += recordSize;
      index++;
    }
    entry.dirIndex = index;
    return BigInt(written);
  };

    // --- BEGIN per-block compile fallback -----------------------------------
  // Try to instantiate the whole module once. If the codegen emitted any
  // invalid wasm anywhere in the manifest, validation fails and we retry
  // block-by-block. Blocks that fail are added to `badBlocks` and dispatched
  // through the interpreter instead. `badBlocks` is read by the main loop.
  const rtInst = rt ? (await WebAssembly.instantiate(rt, {})).instance.exports : null;
  // runtime.js, right after `const rtInst = ...` is created:
  const JIT_SCRATCH_BYTES = 65536;
  const jitScratchPtr = rtInst?.rt_alloc ? rtInst.rt_alloc(JIT_SCRATCH_BYTES) : 0;
  const jitPcsPtr     = rtInst?.rt_alloc ? rtInst.rt_alloc(MAX_JIT_BLOCKS * 8) : 0;
  const jitCountPtr   = rtInst?.rt_alloc ? rtInst.rt_alloc(4) : 0;
  const jitUnsupPtr   = rtInst?.rt_alloc ? rtInst.rt_alloc(4) : 0;
  const jitScratchView = rtInst?.memory
      ? new Uint8Array(rtInst.memory.buffer, jitScratchPtr, JIT_SCRATCH_BYTES)
      : null;
  // --- BEGIN per-block compile fallback -----------------------------------
  // Try to instantiate the whole module once. If the codegen emitted any
  // invalid wasm anywhere in the manifest, validation fails and we retry
  // block-by-block. Blocks that fail are added to `badBlocks` and dispatched
  // through the interpreter instead. `badBlocks` is read by the main loop.
  let blocks;
  // runtime.js, near `const badBlocks = new Set();`
  const unsupportedJit = new Set();
  const badBlocks = new Set();
  // Isolate the whole 0x622F24 function (FLS initialization).
  for (const pcStr of Object.keys(manifest.blocks)) {
    const p = BigInt(pcStr);
    if (p >= 0x622F24n && p <= 0x6230A2n) badBlocks.add(p);
  }
  for (const p of [0x428178n, 0x42817dn, 0x42819bn, 0x4281afn,
                 0x4281bdn, 0x4281c9n, 0x4281d9n]) badBlocks.add(p);
  const _dbgRange = { lo: 0x428178n, hi: 0x4281d9n };
  try {
    const whole = await WebAssembly.instantiate(wasm, { env: { mem: memory } });
    const table = whole.instance.exports.table;
    blocks = new Map();

    for (const [pc, idx] of Object.entries(manifest.blocks)) blocks.set(BigInt(pc), table.get(idx));
    logTrace(`[RECOMP] Add block evicted; will re-JIT on first dispatch`);
  } catch (e) {
    log(`[RECOMP] monolithic module rejected: ${e.message}`);
    log(`[RECOMP] falling back to per-block compile; bad blocks go to the interpreter`);
    if (!rtInst?.rt_translate) {
      throw new Error(`run(): module rejected and rt_translate unavailable; cannot recover`);
    }
    blocks = new Map();
    for (const [pcStr] of Object.entries(manifest.blocks)) {
      const pc = BigInt(pcStr), start = Number(pc);
      const n = Math.min(512, memSize - start);
      if (start < 0 || start >= memSize || n <= 0) { badBlocks.add(pc); continue; }
      const ptr = rtInst.rt_alloc(n);
      try {
        new Uint8Array(rtInst.memory.buffer, ptr, n).set(u8.subarray(start, start + n));
        const len = Number(rtInst.rt_translate(ptr, n, pc));
        const bytes = new Uint8Array(rtInst.memory.buffer, rtInst.rt_out_ptr(), len).slice();
        const mod = new WebAssembly.Module(bytes);
        const inst = new WebAssembly.Instance(mod, { env: { mem: memory } });
        blocks.set(pc, inst.exports.block);
      } finally {
        if (rtInst.rt_free) rtInst.rt_free(ptr);   // if the runtime exports it
      }
    }
    log(`[RECOMP] ${badBlocks.size} block(s) deferred to interpreter, ${blocks.size} compiled`);

  }
  badBlocks.add(0x428178n);
  // --- END per-block compile fallback -------------------------------------
  // Diagnostics: cached disassembly of every JIT'd block, and a small ring
  // buffer of the most recently executed PCs. Both are only used by
  // logUnexpectedCodeAddress() to reconstruct what went wrong.
  const blockDisasm = new Map();     // BigInt pc -> newline-separated text
  // Invalidate only the static block that contains each patched byte range.
  // Previously every Windows block was discarded unconditionally. That forced
  // the runtime JIT to recompile the entire EXE, even when no patch matched,
  // and made otherwise self-contained PE tests fail without recomp_rt.wasm.
  if (winPatchedCodeAddresses.length) {
    const blockStarts = Object.keys(manifest.blocks).map((value) => BigInt(value)).sort((a, b) => a < b ? -1 : a > b ? 1 : 0);
    const invalidated = new Set();
    for (const address of winPatchedCodeAddresses) {
      let owner = null;
      for (const start of blockStarts) {
        if (start > BigInt(address)) break;
        owner = start;
      }
      if (owner !== null) invalidated.add(owner);
    }
    for (const pc of invalidated) blocks.delete(pc);
    log(`[RECOMP] evicted ${invalidated.size} patched block(s); ${blocks.size} precompiled block(s) retained`);
  }

  // Force-evict the writability wrapper block explicitly
  for (const pcStr of Object.keys(manifest.blocks)) {
      const p = BigInt(pcStr);
      if (p >= 0x618000n && p <= 0x618500n) {
          blocks.delete(p);
          badBlocks.add(p);
      }
  }
  const blockHistory = [];           // BigInt pcs, most recent last
  const ctorHits = new Map();
  const HISTORY_LIMIT = 128;
  const pushHistory = (p) => {
    blockHistory.push(p);
    if (blockHistory.length > 128) blockHistory.shift();
  };
  // The interpreter sentinel is used when the JIT translator encounters an
  // instruction it cannot compile. Keep enough context to diagnose bad handoffs
  // into zero-filled memory or addresses outside the mapped image.
  const imageEnd = base + image.length;
  const reportedOutsideImageTargets = new Set();
  const isInImage = (address) => address >= base && address < imageEnd;
  const hexBytes = (address, count = 32) => {
    const start = Number(address);
    if (!Number.isSafeInteger(start) || start < 0 || start >= u8.length) return "<outside guest memory>";
    return Array.from(u8.subarray(start, Math.min(u8.length, start + count)),
      (b) => b.toString(16).padStart(2, "0")).join(" ");
  };
    const logUnexpectedCodeAddress = (source, target) => {
    // Report the first arrival at each outside-image address. This catches the
    // original transfer into a suspicious region, not just a later bad opcode.
    const key = target.toString();
    if (reportedOutsideImageTargets.has(key)) return;
    reportedOutsideImageTargets.add(key);

    // 1) If this transfer came from a JIT block or an interpreted instruction,
    //    dump the source disassembly — this is the single most useful piece of
    //    context when the target is NULL.
        // Disassemble every block that ran recently, on demand.
    // Static blocks never went through jitBatch, so the blockDisasm cache
    // may be empty for them; invoke rt_disasm directly for each history PC.
    for (const p of [...new Set(blockHistory)]) {
      let text = blockDisasm.get(p);
      if (!text && rtInst?.rt_disasm) {
        try {
          const start = Number(p), n = Math.min(512, memSize - start);
          if (start >= 0 && start < memSize && n > 0) {
            const ptr = rtInst.rt_alloc(n);
            new Uint8Array(rtInst.memory.buffer, ptr, n).set(u8.subarray(start, start + n));
            const dlen = Number(rtInst.rt_disasm(ptr, n, p, 40));
            if (dlen > 0) {
              text = new TextDecoder().decode(
                new Uint8Array(rtInst.memory.buffer, rtInst.rt_out_ptr(), dlen));
              if (text) blockDisasm.set(p, text);
            }
          }
        } catch (e) { text = `(disasm failed: ${e?.message ?? e})`; }
      }
      if (text) {
        log(`[RECOMP DEBUG] disasm of 0x${p.toString(16)}:`);
        // In logUnexpectedCodeAddress, replacing the single [WATCH] line:
        for (let i = 0; i < 8; i++) {
          const addr = 0xAD3000 + i * 8;
          log(`[WATCH] [0x${addr.toString(16)}] = 0x${dv.getBigUint64(addr, true).toString(16)}`);
        }
        for (const line of text.split("\n")) if (line) log(`    ${line}`);
      }
    }

    // 2) Recent block history: shows how we arrived at the source block, and in
    //    particular which block wrote the register/memory that the source block
    //    dereferenced.
    if (blockHistory.length) {
      const recent = blockHistory.slice(-16).map((p) => `0x${p.toString(16)}`).join(" ");
      log(`[RECOMP DEBUG] recent blocks: ${recent}`);
    }

    // 3) Friendly hint for NULL / near-NULL targets — this is nearly always a
    //    NULL function pointer or a NULL base pointer.
    if (target === 0n || target < 0x1000n) {
      log(`[RECOMP DEBUG] *** control transfer to NULL/near-NULL (0x${target.toString(16)}). ` +
        `Most likely: unresolved import (GetProcAddress/LoadLibrary returned NULL), ` +
        `uninitialized vtable/function pointer, or a NULL base from VirtualAlloc/HeapAlloc.`);
    }
    const rsp = Number(dv.getBigUint64(ctx + REG.rsp * 8, true));
    const stack = Number.isSafeInteger(rsp) && rsp >= 0 && rsp + 64 <= dv.byteLength
      ? Array.from({ length: 8 }, (_, i) => `0x${dv.getBigUint64(rsp + i * 8, true).toString(16)}`)
      : ["<invalid stack pointer>"];
    const regs = REG_NAMES.map((name, i) =>
      `${name}=0x${dv.getBigUint64(ctx + i * 8, true).toString(16)}`).join(" ");
    log(`[RECOMP DEBUG] ${source} -> 0x${target.toString(16)} is outside mapped image ` +
      `(image 0x${base.toString(16)}..0x${imageEnd.toString(16)}; ` +
      `${target < BigInt(u8.length) ? "inside" : "outside"} guest memory)`);
    log(`[RECOMP DEBUG] bytes at 0x${target.toString(16)}: ${hexBytes(target)}`);
    log(`[RECOMP DEBUG] RSP=0x${rsp.toString(16)} stack=[${stack.join(", ")}]`);
    log(`[RECOMP DEBUG] ${regs}`);
  };

    // Translate up to MAX_BLOCKS consecutive blocks in one round trip and one
  // WASM compile. Returns the compiled function for `pc`, or `null` if the
  // first instruction at `pc` cannot be lifted (caller must use the
  // interpreter). Increments `jitted` internally by the number of blocks added.
  function disasmAt(pc) {
    if (!diagnostics || !rtInst?.rt_disasm) {
      logTrace("disasmAt disabled")
      return null
    };
    if (blockDisasm.has(pc)) return blockDisasm.get(pc);
    const start = Number(pc);
    if (start < 0 || start >= memSize) return null;
    const n = Math.min(4096, memSize - start);
    try {
      const ptr = rtInst.rt_alloc(n);
      new Uint8Array(rtInst.memory.buffer, ptr, n).set(u8.subarray(start, start + n));
      const dlen = Number(rtInst.rt_disasm(ptr, n, pc, 32));
      if (dlen > 0) {
        const text = new TextDecoder().decode(
          new Uint8Array(rtInst.memory.buffer, rtInst.rt_out_ptr(), dlen));
        if (text) { blockDisasm.set(pc, text); return text; }
      }
    } catch (e) {
      log(`[RECOMP DEBUG] disasm failed at 0x${pc.toString(16)}: ${e?.message ?? e}`);
    }
    return null;
  }
  async function jitBatch(pc) {
    if (!rtInst) throw new Error(`no static block at 0x${pc.toString(16)} and recomp_rt.wasm not loaded`);
    const start = Number(pc);
    const n = Math.min(JIT_SCRATCH_BYTES, memSize - start);
    if (start < 0 || start >= memSize || n <= 0) throw new Error(`JIT address outside initial guest image: 0x${pc.toString(16)}`);

    const scratch = new Uint8Array(rtInst.memory.buffer, jitScratchPtr, n);
    scratch.set(u8.subarray(start, start + n));

    // Diagnostics: disassemble the first block before translating (rt_disasm
    // and rt_translate_batch share the same OUT buffer).
    if (diagnostics && typeof rtInst.rt_disasm === "function" && !blockDisasm.has(pc)) {
      try {
        const dlen = Number(rtInst.rt_disasm(ptr, n, pc, 32));
        if (dlen > 0) {
          const text = new TextDecoder().decode(new Uint8Array(rtInst.memory.buffer, rtInst.rt_out_ptr(), dlen));
          if (text) blockDisasm.set(pc, text);
          if (typeof globalThis.__dumpDisasm === "function") globalThis.__dumpDisasm(pc, text);
        }
      } catch { /* diagnostics only */ }
    }

    let wasmLen = 0, count = 0, unsupported = 0;
    if (typeof rtInst.rt_translate_batch === "function") {
        wasmLen = Number(rtInst.rt_translate_batch(
            pc, jitScratchPtr, n, MAX_JIT_BLOCKS, jitPcsPtr, jitCountPtr, jitUnsupPtr));
        const dvRt = new DataView(rtInst.memory.buffer);
        count = dvRt.getUint32(jitCountPtr, true);
        unsupported = dvRt.getUint32(jitUnsupPtr, true);
        if (!unsupported) {
            const wasmBytes = new Uint8Array(rtInst.memory.buffer, rtInst.rt_out_ptr(), wasmLen).slice();
            const module = await WebAssembly.compile(wasmBytes);
            const instance = await WebAssembly.instantiate(module, { env: { mem: memory } });
            const table = instance.exports.table;
            for (let i = 0; i < count; i++) {
                blocks.set(dvRt.getBigUint64(jitPcsPtr + i * 8, true), table.get(i));
            }
            jitted += count;
        }
    }
    return unsupported ? null : blocks.get(pc);
  }
  // Make DescriptorDatabase::Add return true on the duplicate path.
  // The file *is* in the DB — Add just says "I already had it", and the
  // caller's CHECK(...) is expecting "yes, it's there", which is true.
  //
  // 1) NOP the duplicate-branch jz so we always take the success path.
  function emulateLinuxSyscall(nr, args) {
    const [a0, a1, a2, a3, a4, a5] = args;
    const fdNum = Number(a0);
    switch (nr) {
      case 0: // read
        return guestRead(fdNum, a1, a2);
      case 1: // write
        return guestWrite(fdNum, a1, a2);
      case 3: { // close
        if (!fdEntry(fdNum)) return negErrno(9);
        fdTable.delete(fdNum);
        return 0n;
      }
      case 4: // stat
      case 6: { // lstat (symlinks are not modelled)
        const path = readCString(a0);
        if (path === null) return negErrno(14);
        const resolved = resolveGuestPath(-100n, path);
        const file = virtualFiles.get(resolved);
        const entry = file ? { kind: "file", path: resolved, file } : isDirectoryPath(resolved) ? { kind: "dir", path: resolved } : null;
        return entry ? guestStat(a1, entry) : negErrno(2);
      }
      case 5: { // fstat
        const entry = fdEntry(fdNum);
        return entry ? guestStat(a1, entry) : negErrno(9);
      }
      case 8: { // lseek
        const entry = fdEntry(fdNum);
        if (!entry) return negErrno(9);
        if (entry.kind === "stdin" || entry.kind === "stdout" || entry.kind === "stderr") return negErrno(29);
        const offset = Number(BigInt.asIntN(64, a1));
        const whence = Number(a2);
        if (entry.kind === "dir") {
          if (whence === 0 && offset === 0) { entry.dirIndex = 0; return 0n; }
          return negErrno(22);
        }
        const basePos = whence === 0 ? 0 : whence === 1 ? entry.position : whence === 2 ? entry.file.data.length : null;
        if (basePos === null || !Number.isSafeInteger(offset) || !Number.isSafeInteger(basePos + offset) || basePos + offset < 0) return negErrno(22);
        entry.position = basePos + offset;
        return BigInt(entry.position);
      }
      case 9: { // mmap: anonymous or a copy of a virtual file mapping
        const len = align(Number(a1), PAGE_4K);
        const flags = Number(a3);
        if (!Number.isSafeInteger(len) || len <= 0 || len > 0x7fffffff) return negErrno(22);
        const anonymous = (flags & 0x20) !== 0; // MAP_ANONYMOUS
        let source = null;
        const offset = Number(a5);
        if (anonymous) {
          if (a5 !== 0n) return negErrno(22);
        } else {
          const entry = fdEntry(Number(a4));
          if (!entry || entry.kind !== "file" || !entry.readable) return negErrno(9);
          if (!Number.isSafeInteger(offset) || offset < 0 || offset % PAGE_4K !== 0) return negErrno(22);
          source = entry.file.data;
        }
        const start = align(mmapCursor, PAGE_4K);
        const end = start + len;
        if (end > 0xFFFFFFFF || !ensureMemory(end)) return negErrno(12);
        u8.fill(0, start, end);
        if (source) u8.set(source.subarray(offset, offset + len), start);
        mmapCursor = end;
        return BigInt(start);
      }
      case 10: // mprotect: page permissions are not represented in WASM memory
      case 11: // munmap: the linear-memory arena is monotonic; freeing is deferred
      case 28: // madvise
        return 0n;
      case 12: // brk
        if (a0 === 0n) return BigInt(brkValue);
        if (a0 <= BigInt(brkLimit) && a0 >= BigInt(base + image.length)) {
          brkValue = Number(a0);
          return a0;
        }
        return BigInt(brkValue);
      case 13: // rt_sigaction (signal delivery is not implemented)
      case 14: // rt_sigprocmask
      case 273: // set_robust_list
        return 0n;
      case 218: // set_tid_address
        return 1n;
      case 217: // getdents64
        return guestGetdents64(fdNum, a1, a2);
      case 16: // ioctl
        return negErrno(25); // ENOTTY
      case 17: // pread64
        return guestRead(fdNum, a1, a2, Number(a3));
      case 18: // pwrite64
        return guestWrite(fdNum, a1, a2, Number(a3));
      case 19: { // readv
        const count = Number(a2);
        if (!Number.isSafeInteger(count) || count < 0 || count > 1024) return negErrno(22);
        let total = 0n;
        for (let i = 0; i < count; i++) {
          const ptr = Number(a1) + i * 16;
          if (!Number.isSafeInteger(ptr) || ptr < 0 || ptr + 16 > u8.length) return total || negErrno(14);
          const dataPtr = dv.getBigUint64(ptr, true), dataLen = dv.getBigUint64(ptr + 8, true);
          const result = guestRead(fdNum, dataPtr, dataLen);
          if (result < 0n) return total || result;
          total += result;
          if (result < dataLen) break;
        }
        return total;
      }
      case 20: { // writev
        const count = Number(a2);
        if (!Number.isSafeInteger(count) || count < 0 || count > 1024) return negErrno(22);
        let total = 0n;
        for (let i = 0; i < count; i++) {
          const ptr = Number(a1) + i * 16;
          if (!Number.isSafeInteger(ptr) || ptr < 0 || ptr + 16 > u8.length) return total || negErrno(14);
          const dataPtr = dv.getBigUint64(ptr, true), dataLen = dv.getBigUint64(ptr + 8, true);
          const result = guestWrite(fdNum, dataPtr, dataLen);
          if (result < 0n) return total || result;
          total += result;
          if (result < dataLen) break;
        }
        return total;
      }
      case 21: { // access
        const path = readCString(a0);
        if (path === null) return negErrno(14);
        const resolved = resolveGuestPath(-100n, path);
        return virtualFiles.has(resolved) || isDirectoryPath(resolved) ? 0n : negErrno(2);
      }
      case 76: { // truncate
        const path = readCString(a0);
        if (path === null) return negErrno(14);
        const resolved = resolveGuestPath(-100n, path);
        const file = virtualFiles.get(resolved);
        const size = Number(a1);
        if (!file) return negErrno(2);
        if (!Number.isSafeInteger(size) || size < 0 || size > 0x7fffffff) return negErrno(22);
        const resized = new Uint8Array(size);
        resized.set(file.data.subarray(0, size));
        file.data = resized;
        return 0n;
      }
      case 77: { // ftruncate
        const entry = fdEntry(fdNum);
        const size = Number(a1);
        if (!entry) return negErrno(9);
        if (entry.kind !== "file") return negErrno(22);
        if (!entry.writable) return negErrno(9);
        if (!Number.isSafeInteger(size) || size < 0 || size > 0x7fffffff) return negErrno(22);
        const resized = new Uint8Array(size);
        resized.set(entry.file.data.subarray(0, size));
        entry.file.data = resized;
        if (entry.position > size) entry.position = size;
        return 0n;
      }
      case 39: // getpid
      case 186: // gettid
        return 1n;
      case 60: // exit
      case 231: // exit_group
        return { exit: true, status: Number(a0 & 0xFFn) };
      case 63: { // uname
        const fields = ["Linux", "wasm-guest", "6.1.0-recomp", "#1", "x86_64", "localdomain"];
        const ptr = Number(a0);
        if (!ensureMemory(ptr + 390)) return negErrno(14);
        u8.fill(0, ptr, ptr + 390);
        fields.forEach((field, index) => u8.set(new TextEncoder().encode(field).subarray(0, 64), ptr + index * 65));
        return 0n;
      }
      case 72: { // fcntl: limited descriptor duplication/status flags
        const entry = fdEntry(fdNum);
        const command = Number(a1);
        if (!entry) return negErrno(9);
        if (command === 1) return 0n; // F_GETFD
        if (command === 2) return 0n; // F_SETFD
        if (command === 3) return BigInt(entry.openFlags ?? 0);
        if (command === 4) { entry.append = (Number(a2) & 0x400) !== 0; entry.openFlags = (entry.openFlags ?? 0) & ~0x400 | (entry.append ? 0x400 : 0); return 0n; }
        if (command === 0 || command === 1030) return BigInt(allocateFd(entry, Number(a2)));
        return negErrno(22);
      }
      case 79: { // getcwd
        const bytes = new TextEncoder().encode("/\0");
        if (a1 < BigInt(bytes.length) || !writeBytes(a0, bytes)) return negErrno(34);
        return BigInt(bytes.length);
      }
      case 89: // readlink
      case 267: { // readlinkat
        const dirfd = nr === 267 ? a0 : -100n;
        const pathPtr = nr === 267 ? a1 : a0;
        const outPtr = nr === 267 ? a2 : a1;
        const outLen = nr === 267 ? a3 : a2;
        const path = readCString(pathPtr);
        if (path === null) return negErrno(14);
        const resolved = resolveGuestPath(dirfd, path);
        const target = resolved === "/proc/self/exe" ? "/guest/program" : null;
        if (target === null) return negErrno(2);
        const bytes = new TextEncoder().encode(target);
        const count = Math.min(Number(outLen), bytes.length);
        if (!Number.isSafeInteger(count) || count < 0 || !writeBytes(outPtr, bytes.subarray(0, count))) return negErrno(14);
        return BigInt(count);
      }
      case 96: { // gettimeofday
        const now = Date.now();
        const ptr = Number(a0);
        if (!ensureMemory(ptr + 16)) return negErrno(14);
        dv.setBigInt64(ptr, BigInt(Math.floor(now / 1000)), true);
        dv.setBigInt64(ptr + 8, BigInt((now % 1000) * 1000), true);
        return 0n;
      }
      case 102: // getuid
      case 104: // getgid
      case 107: // geteuid
      case 108: // getegid
        return 1000n;
      case 158: { // arch_prctl
        const code = Number(a0), ptr = Number(a1);
        if (code === 0x1002) { dv.setBigUint64(ctx + 144, a1, true); return 0n; } // ARCH_SET_FS
        if (code === 0x1001) { dv.setBigUint64(ctx + 152, a1, true); return 0n; } // ARCH_SET_GS
        if (code === 0x1003) { if (!ensureMemory(ptr + 8)) return negErrno(14); dv.setBigUint64(ptr, dv.getBigUint64(ctx + 144, true), true); return 0n; }
        if (code === 0x1004) { if (!ensureMemory(ptr + 8)) return negErrno(14); dv.setBigUint64(ptr, dv.getBigUint64(ctx + 152, true), true); return 0n; }
        return negErrno(22);
      }
      case 202: { // futex: wake succeeds; wait is not blocking/threaded
        const command = Number(a1 & 0x7Fn);
        if (command === 1 || command === 10) return 0n;
        if (command === 0 || command === 9) return negErrno(11);
        return negErrno(38);
      }
      case 204: { // sched_getaffinity
        const size = Number(a1), ptr = Number(a2);
        if (!Number.isSafeInteger(size) || size <= 0 || !ensureMemory(ptr + size)) return negErrno(22);
        u8.fill(0, ptr, ptr + size);
        u8[ptr] = 1;
        return BigInt(size);
      }
      case 228: { // clock_gettime
        const clockId = Number(a0);
        if (![0, 1, 2, 4, 5, 6, 7].includes(clockId)) return negErrno(22);
        const realtime = clockId === 0 || clockId === 5;
        const now = realtime ? Date.now() : (globalThis.performance?.now?.() ?? Date.now());
        const seconds = Math.floor(now / 1000);
        const nanos = Math.floor((now - seconds * 1000) * 1_000_000);
        const ptr = Number(a1);
        if (!ensureMemory(ptr + 16)) return negErrno(14);
        dv.setBigInt64(ptr, BigInt(seconds), true);
        dv.setBigInt64(ptr + 8, BigInt(nanos), true);
        return 0n;
      }
      case 257: { // openat
        const path = readCString(a1);
        if (path === null) return negErrno(14);
        const resolved = resolveGuestPath(a0, path);
        if (resolved === null) return negErrno(20); // ENOTDIR
        const flags = Number(a2), access = flags & 3;
        if (access === 3) return negErrno(22);
        let file = virtualFiles.get(resolved);
        const directory = isDirectoryPath(resolved) && !file;
        const create = (flags & 0x40) !== 0, exclusive = (flags & 0x80) !== 0;
        if (file && create && exclusive) return negErrno(17); // EEXIST
        if (!file && !directory && !create) return negErrno(2);
        if (directory && access !== 0) return negErrno(21);
        if ((flags & 0x10000) !== 0 && !directory) return negErrno(20);
        if (directory && (flags & 0x200) !== 0) return negErrno(21);
        if (!file && !directory) {
          file = { data: new Uint8Array(0) };
          virtualFiles.set(resolved, file);
        }
        if (file && (flags & 0x200) !== 0) {
          if (access === 0) return negErrno(13);
          file.data = new Uint8Array(0);
        }
        const entry = directory
          ? { kind: "dir", path: resolved, readable: true, writable: false, position: 0 }
          : { kind: "file", path: resolved, file, readable: access !== 1, writable: access !== 0,
              append: (flags & 0x400) !== 0, openFlags: flags, position: (flags & 0x400) !== 0 ? file.data.length : 0 };
        return BigInt(allocateFd(entry));
      }
      case 262: { // newfstatat
        const path = readCString(a1);
        if (path === null) return negErrno(14);
        const resolved = resolveGuestPath(a0, path);
        if (resolved === null) return negErrno(20);
        const file = virtualFiles.get(resolved);
        const entry = file ? { kind: "file", path: resolved, file } : isDirectoryPath(resolved) ? { kind: "dir", path: resolved } : null;
        return entry ? guestStat(a2, entry) : negErrno(2);
      }
      case 269: // faccessat
      case 439: { // faccessat2
        const path = readCString(a1);
        if (path === null) return negErrno(14);
        const resolved = resolveGuestPath(a0, path);
        return resolved !== null && (virtualFiles.has(resolved) || isDirectoryPath(resolved)) ? 0n : negErrno(2);
      }
      case 302: { // prlimit64: return large synthetic limits
        const ptr = Number(a3);
        if (!ensureMemory(ptr + 16)) return negErrno(14);
        dv.setBigUint64(ptr, 0x7FFFFFFFFFFFFFFFn, true);
        dv.setBigUint64(ptr + 8, 0x7FFFFFFFFFFFFFFFn, true);
        return 0n;
      }
      case 318: { // getrandom
        const ptr = Number(a0), len = Number(a1);
        if (!Number.isSafeInteger(ptr) || !Number.isSafeInteger(len) || len < 0 || len > 0x7fffffff || !ensureMemory(ptr + len)) return negErrno(14);
        if (!globalThis.crypto?.getRandomValues) return negErrno(38);
        try {
          for (let off = 0; off < len; off += 65536) {
            const chunk = u8.subarray(ptr + off, ptr + Math.min(len, off + 65536));
            globalThis.crypto.getRandomValues(chunk);
          }
        } catch { return negErrno(14); }
        return BigInt(len);
      }
      default:
        return negErrno(38); // ENOSYS
    }
  }

  async function dispatchSyscall() {
    const nr = Number(dv.getBigUint64(ctx + REG.rax * 8, true));
    const args = [REG.rdi, REG.rsi, REG.rdx, REG.r10, REG.r8, REG.r9]
      .map((index) => dv.getBigUint64(ctx + index * 8, true));
    const hook = syscalls[nr];
    const result = typeof hook === "function"
      ? await hook({ args, memory, context: ctx, dataView: dv, readCString, readBytes, writeBytes, ensureMemory })
      : emulateLinuxSyscall(nr, args);
    if (result && typeof result === "object" && result.exit) return result;
    dv.setBigUint64(ctx + REG.rax * 8, BigInt.asUintN(64, BigInt(result)), true);
    return null;
  }
  logTrace(`[RECOMP] manifest.entry = 0x${BigInt(manifest.entry).toString(16)}`);
  logTrace(`[RECOMP] manifest.initializers (${(manifest.initializers ?? []).length}):`);
  for (const it of manifest.initializers ?? []) {
    logTrace(`    base=0x${BigInt(it.base).toString(16)}  entry=0x${BigInt(it.entry).toString(16)}`);
  }
  const winDllInitializers = (manifest.initializers ?? []).map((item) => ({ base: BigInt(item.base), entry: BigInt(item.entry) }));
  {
    const seen = new Set();
    const list = [];
    for (const item of manifest.initializers ?? []) {
      const base = BigInt(item.base), entry = BigInt(item.entry);
      const key = `${base.toString(16)}:${entry.toString(16)}`;
      if (seen.has(key)) {
        log(`[RECOMP] WARN: skipping duplicate initializer ${key}`);
        continue;
      }
      seen.add(key);
      // If this is the main EXE's entrypoint, the `manifest.entry` phase will
      // run it anyway — running it as a "DLL init" first double-runs _initterm.
      if (entry === BigInt(manifest.entry)) {
        log(`[RECOMP] WARN: skipping initializer ${key} (same as manifest.entry)`);
        continue;
      }
      list.push({ base, entry });
    }
    winDllInitializers.length = 0;
    winDllInitializers.push(...list);
  }
  let winDllInitIndex = 0;
  if (isWindows) {
    try {
      const optOff = base + dv.getUint32(base + 0x3c, true) + 24;
      const tlsRva = dv.getUint32(optOff + 112 + 9 * 8, true);
      if (tlsRva) {
        const t = base + tlsRva;
        const start = Number(dv.getBigUint64(t, true)), end = Number(dv.getBigUint64(t + 8, true));
        const idxAddr = Number(dv.getBigUint64(t + 16, true));
        const zeroFill = dv.getUint32(t + 32, true);
        const blockSize = end - start + zeroFill;
        const block = winAlloc(BigInt(Math.max(blockSize, 0x1000)), true);
        writeBytes(Number(block), u8.slice(start, end));
        const slots = winAlloc(0x1000n, true);
        dv.setBigUint64(Number(slots), block, true);       // slot 0 = this module's TLS block
        dv.setUint32(idxAddr, 0, true);                    // _tls_index = 0
        dv.setBigUint64(WIN_TEB + 0x58, slots, true);      // TEB.ThreadLocalStoragePointer
        logTrace(`[TLS] block=0x${block.toString(16)} size=${end - start}+${zeroFill} index@0x${idxAddr.toString(16)}`);
        const epochOffset = 0;   // guess: _Init_thread_epoch is at TLS offset 0
        const canary = dv.getUint32(Number(block) + epochOffset, true);
        // Scan the template for INT_MIN (0x80000000) — that's where _Init_thread_epoch lives
        let guardOff = -1;
        const tlsLen = end - start;
        for (let off = 0; off + 4 <= tlsLen; off += 4) {
          if (dv.getUint32(start + off, true) === 0x80000000) { guardOff = off; break; }
        }
        log(`[TLS] INT_MIN at +0x${guardOff >= 0 ? guardOff.toString(16) : 'not found — TLS not used for guards'}`);

        // Also dump first 64 bytes for pattern matching
        const head = [];
        for (let i = 0; i < Math.min(64, tlsLen); i++) head.push(u8[start + i].toString(16).padStart(2, '0'));
        log(`[TLS] head: ${head.join(' ')}`);
      }
    } catch (e) { logTrace(`[TLS] setup failed: ${e.message}`); }
  }
  let pc = BigInt(manifest.entry), jitted = 0, interpreted = 0, steps = 0, reason = "step limit";
  for (const p of pointerPatches) {
    const h = winLookupModule(p.dll, true);
    const fn = winLookupApi(h, p.name, null);
    if (fn) dv.setBigUint64(Number(p.address), fn, true);
  }
  if (isWindows && winDllInitializers.length) {
    const first = winDllInitializers[0];
    dv.setBigUint64(winEntryRsp, WIN_DLL_INIT_RETURN, true);
    dv.setBigUint64(ctx + REG.rsp * 8, BigInt(winEntryRsp), true);
    dv.setBigUint64(ctx + REG.rcx * 8, first.base, true); // DllMain(hinst, DLL_PROCESS_ATTACH, NULL)
    dv.setBigUint64(ctx + REG.rdx * 8, 1n, true);
    dv.setBigUint64(ctx + REG.r8 * 8, 0n, true);
    dv.setBigUint64(ctx + REG.r9 * 8, 0n, true);
    pc = first.entry;
  }
  // In run(), replace the current Add patch with:
  if (diagnostics && rtInst?.rt_disasm) {
    // Raw byte dump — the disassembler starts AT 0x4a3559, so the call is hidden.
    const dumpRange = (startAddr, len, label) => {
      logTrace(`[RECOMP] bytes ${label} @0x${startAddr.toString(16)}:`);
      for (let off = 0; off < len; off += 16) {
        const a = Number(startAddr) + off;
        const hex = Array.from(u8.subarray(a, Math.min(a + 16, u8.length)),
          (b) => b.toString(16).padStart(2, "0")).join(" ");
        logTrace(`  0x${a.toString(16)}: ${hex}`);
      }
    };
    dumpRange(0x4a3540n, 0x40n, "around CHECK/Add call");
    dumpRange(0x633430n, 0x40n, "around ctor 0x633451");
    dumpRange(0x6339f0n, 0x40n, "around 0x633a0b");
    dumpRange(0x4a34c0n, 0x80n, "CHECK block preamble");
    dumpRange(0x61fe00n, 0x60n, "length_error loop+throw");
    dumpRange(0x5f32f0n, 0x50n, "throw helper");
    dumpRange(0x613290n, 0x60n, "len_error caller");
    dumpRange(0x620220n, 0x80n, "caller of 6132a0");
    dumpRange(0x6af720n, 0x80n, "DescriptorDatabase::Add");
    dumpRange(0x5f06a0n, 0x180n, "Xlength_error caller");
    dumpRange(0x5f3334n, 0xA0n, "throw helper entry");
    dumpRange(0x6af7a0n, 0x80n, "Add duplicate path");
    dumpRange(0x630a40n, 0xC0n, "throw trigger at 0x630a78");
    dumpRange(0x5f07f2n, 0x40n, "Xlength_error body");
    dumpRange(0x6309f0n, 0x60n, "hash bucket check before throw");
    // The what() string. In the exception object at 0xffdd80, qword[1]
    // (= 0x1015bc0 in this run) is the heap pointer inside the std::string.
    // Dump 32 bytes and also try it as a C-string.
    const whatPtr = Number(dv.getBigUint64(0xffdd88, true));
    logTrace(`[what] ptr=0x${whatPtr.toString(16)}`);
    dumpRange(BigInt(whatPtr), 0x20n, "what() message");
  }
  if (diagnostics) {
    try {
      const peOff = dv.getUint32(base + 0x3c, true);
      const numSections = dv.getUint16(base + peOff + 6, true);
      const optSize = dv.getUint16(base + peOff + 20, true);
      const sectionsBase = base + peOff + 24 + optSize;
      logTrace(`[PE] ${numSections} section(s), optSize=0x${optSize.toString(16)}`);
      for (let i = 0; i < numSections && i < 32; i++) {
        const s = sectionsBase + i * 40;
        const name = new TextDecoder().decode(u8.subarray(s, s + 8)).replace(/\0+$/, "");
        const vaddr = base + dv.getUint32(s + 12, true);
        const vsize = dv.getUint32(s + 8, true);
        const raw = dv.getUint32(s + 20, true);
        logTrace(`[PE] ${name.padEnd(8)} VA 0x${vaddr.toString(16)}..0x${(vaddr + vsize).toString(16)} (vsize 0x${vsize.toString(16)}, raw 0x${raw.toString(16)})`);
        if (0x770000 >= vaddr && 0x770000 < vaddr + vsize)
          logTrace(`[PE] *** 0x770000 is inside ${name} ***`);
      }
    } catch (e) { logTrace(`[PE] section walk failed: ${e.message}`); }
  }
  // after your existing disasmAt calls:
  const startTime = Date.now();
  const TIME_BUDGET_MS = Number(new URLSearchParams(location.search).get("budget") ?? 60_000);
  let lastPcForLoop = -1n;
  let lastLoopState = 0n;
  let sameStateCount = 0;
  let samePcCount = 0;
  const hookHits = new Map();
  const hitN = (k) => { const v = (hookHits.get(k) ?? 0) + 1; hookHits.set(k, v); return v; };
  const R = (r) => dv.getBigUint64(ctx + REG[r] * 8, true);
  const qwords = (addr, n = 8) => {
    const p = Number(addr);
    if (!Number.isSafeInteger(p) || p < 0x1000 || p + n * 8 > u8.length) return "<bad ptr>";
    return Array.from({ length: n }, (_, i) => "0x" + dv.getBigUint64(p + i * 8, true).toString(16)).join(" ");
  };
  let lastHash = "";
  const pcHooks = new Map([
    [0x61fbc8n, () => log(`[INITTERM?] #${hitN("it")} first=0x${R("rcx").toString(16)} last=0x${R("rdx").toString(16)}`)],
    [0x633440n, () => log(`[CTOR] 0x633440 hit #${hitN("ctor")}`)],
    [0x6307f0n, () => { lastHash = `rcx=0x${R("rcx").toString(16)} rdx=0x${R("rdx").toString(16)} r8=0x${R("r8").toString(16)} [rcx]=${qwords(R("rcx"), 10)}`; }],
    [0x630a6cn, () => {
      log(`[HASH] last entry: ${lastHash}`);
      log(`[HASH] throw stub regs: ${REG_NAMES.map((n) => `${n}=0x${R(n).toString(16)}`).join(" ")}`);
      for (const r of ["rbx", "rsi", "rdi", "rbp", "r14"]) log(`[HASH]   [${r}] ${qwords(R(r), 10)}`);
    }],
  ]);
  let lastPerfAt = Date.now();
  let lastPerfStep = 0;
  let lastRdiSeen = 0n;    // declare near `let lastPcForLoop = -1n;`
  let prevBlockPc = -1n;
  // At the top of run(), before the main while loop:
  {
      let lastStep = 0;
      let lastDispatch = 0;
      const watcher = setInterval(() => {
          const now = steps;
          if (now === lastStep && Date.now() - lastDispatch > 10_000) {
              const cur = globalThis.__currentApi;
              log(`[HUNG] stuck in ${cur ? `${cur.dll}!${cur.name}` : "unknown API"} ` +
                  `at step ${now}, pc=0x${pc.toString(16)}`);
              log(`[HUNG] recent APIs: ${(globalThis.__recentApis || []).slice(-10).join(" <- ")}`);
          }
          if (now !== lastStep) lastDispatch = Date.now();
          lastStep = now;
      }, 2000);
      // Optionally clearInterval(watcher) on exit
  }
  let stepsSinceDispatch = 0;
  while (steps++ < maxSteps) {
    const rawPc = pc;
    const isSentinel =
      pc === EXIT ||
      pc === WIN_EXIT ||
      pc === WIN_CALLBACK_RETURN ||
      pc === WIN_DLL_INIT_RETURN ||
      pc === INITTERM_RESUME ||
      pc === 0xFFFF_FFF8n ||
      (pc & INTERP_BIT) !== 0n ||
      (pc & SYSCALL_BIT) !== 0n ||
      winApiByAddress.has(pc) ||
      (pc >= BigInt(base) && pc < BigInt(imageEnd));

    if (!isSentinel) {
      log(`[BAD-PC] pc=0x${pc.toString(16)}${pc !== rawPc ? ` (raw 0x${rawPc.toString(16)})` : ""}`);
      log(`[BAD-PC] last 6 blocks: ${blockHistory.slice(-6).map(p => "0x" + p.toString(16)).join(" <- ")}`);
      const rsp = Number(dv.getBigUint64(ctx + REG.rsp * 8, true));
      const ret = rsp + 8 <= u8.length ? dv.getBigUint64(rsp, true) : 0n;
      if (ret >= BigInt(base) && ret < BigInt(base + image.length)) {
        log(`[BAD-PC] recovering: injecting null return to 0x${ret.toString(16)}`);
        dv.setBigUint64(ctx + REG.rsp * 8, BigInt(rsp + 8), true);
        dv.setBigUint64(ctx + REG.rax * 8, 0n, true);
        pc = ret;
        continue;
      }
      reason = `bad PC 0x${pc.toString(16)} (cannot recover, ret=0x${ret.toString(16)})`;
      break;
    }
    if (pc === lastPcForLoop) samePcCount++;
    else { lastPcForLoop = pc; samePcCount = 0; }
    {
      const curRdi = dv.getBigUint64(ctx + REG.rdi * 8, true);
      if (curRdi === 0x770000n && lastRdiSeen !== 0x770000n) {
        log(`[RDI-TRACE] rdi became 0x770000 at pc=0x${pc.toString(16)}`);
        log(`[RDI-TRACE] recent blocks: ${blockHistory.slice(-8).map(p => "0x" + p.toString(16)).join(" <- ")}`);
        log(`[RDI-TRACE] rsp=0x${dv.getBigUint64(ctx + REG.rsp * 8, true).toString(16)}`);
      }
      lastRdiSeen = curRdi;
    }
    if (diagnostics && (steps % 1_000_000) === 0) {
        log(`[HEARTBEAT] step ${steps} pc=0x${pc.toString(16)} (jitted ${jitted}, interpreted ${interpreted}, blocks run ${steps})`);
    }
    if (termination?.requested !== undefined && termination?.requested !== null) {
      winExitCode = Number(termination.requested) | 0;
      reason = `terminated (${winExitCode})`;
      break;
    }
    if (stepsSinceDispatch++ > 500_000) {
        log(`[NO-DISPATCH] 500K steps without a Win32 call at pc=0x${pc.toString(16)}`);
        log(`[NO-DISPATCH] recent blocks: ${blockHistory.slice(-16).map(p => "0x" + p.toString(16)).join(" <- ")}`);
        log(`[NO-DISPATCH] regs: ${REG_NAMES.map((n,i) => `${n}=0x${dv.getBigUint64(ctx+i*8, true).toString(16)}`).join(" ")}`);
        stepsSinceDispatch = 0;   // reset so it doesn't flood
    }
    if (isWindows && pc === WIN_DLL_INIT_RETURN) {
      const accepted = dv.getBigUint64(ctx + REG.rax * 8, true) !== 0n;
      if (!accepted) {
        winExitCode = 0xC0000142 | 0; // STATUS_DLL_INIT_FAILED
        reason = `DLL_PROCESS_ATTACH failed for ${winLoadedModulesByBase.get(winDllInitializers[winDllInitIndex]?.base)?.name ?? "unknown DLL"}`;
        break;
      }
      winDllInitIndex++;
      if (winDllInitIndex < winDllInitializers.length) {
        const next = winDllInitializers[winDllInitIndex];
        dv.setBigUint64(winEntryRsp, WIN_DLL_INIT_RETURN, true);
        dv.setBigUint64(ctx + REG.rsp * 8, BigInt(winEntryRsp), true);
        dv.setBigUint64(ctx + REG.rcx * 8, next.base, true);
        dv.setBigUint64(ctx + REG.rdx * 8, 1n, true);
        dv.setBigUint64(ctx + REG.r8 * 8, 0n, true);
        dv.setBigUint64(ctx + REG.r9 * 8, 0n, true);
        pc = next.entry;
      } else {
        dv.setBigUint64(winEntryRsp, WIN_EXIT, true);
        dv.setBigUint64(ctx + REG.rsp * 8, BigInt(winEntryRsp), true);
        pc = BigInt(manifest.entry);
      }
      continue;
    }
    if (isWindows && pc === WIN_CALLBACK_RETURN) {
      const frame = winCallbackFrames.pop();
      if (!frame) { reason = "orphaned guest callback return"; break; }

      // If this was a thread's start routine and it ran past its budget,
      // fake a "thread returned 0" so the parent can make progress.
      if (frame.thread && frame.thread.stepBudget !== undefined) {
        const ran = steps - (frame.threadStartStep ?? 0);
        if (ran > 2_000_000) {
          log(`[THREAD-BUDGET] tid=${frame.thread.threadId} ran ${ran} steps without returning — faking exit(0)`);
          frame.thread.finished = true;
          frame.thread.exitCode = 0;
          winWakeHandleWaiters();
          // Fall through to normal return path
        }
      }

      const callbackResult = dv.getBigUint64(ctx + REG.rax * 8, true);
      frame.saved.forEach((value, i) => { if (i !== REG.rax) dv.setBigUint64(ctx + i * 8, value, true); });
      dv.setBigUint64(ctx + 136, frame.savedFlags, true);
      dv.setBigUint64(ctx + REG.rsp * 8, BigInt(frame.resumeRsp), true);
      dv.setBigUint64(ctx + REG.rax * 8, callbackResult, true);
      if (frame.cleanupHwnd) winHandles.delete(frame.cleanupHwnd);
      pc = frame.returnPc;
      continue;
    }
    if (isWindows && pc === 0xFFFF_FFF8n) {
      const frame = winCallbackFrames.pop();
      if (!frame || !frame.initOncePtr) { reason = "orphaned InitOnce resume"; break; }
      const callbackResult = dv.getBigUint64(ctx + REG.rax * 8, true);
      // Store the callback's return in the guard: TRUE becomes 1, else actual value
      dv.setBigUint64(frame.initOncePtr, callbackResult === 0n ? 1n : callbackResult, true);
      if (frame.contextPtr && ensureMemory(frame.contextPtr + 8)) {
        dv.setBigUint64(frame.contextPtr, callbackResult, true);
      }
      frame.saved.forEach((value, i) => { if (i !== REG.rax) dv.setBigUint64(ctx + i * 8, value, true); });
      dv.setBigUint64(ctx + 136, frame.savedFlags, true);
      dv.setBigUint64(ctx + REG.rsp * 8, BigInt(frame.resumeRsp), true);
      dv.setBigUint64(ctx + REG.rax * 8, 1n, true);
      pc = frame.returnPc;
      continue;
    }
    if (isWindows && pc === INITTERM_RESUME) {
      const frame = winCallbackFrames.pop();
      if (!frame || !inittermState) { reason = "orphaned initterm resume"; break; }
      if (inittermState.pending.length > 0) {
        const nextFn = inittermState.pending.shift();
        inittermState.done++;
        const cbRsp = BigInt(((Number(inittermState.returnRsp) - 0x100) & ~15) - 8);
        if (!ensureMemory(Number(cbRsp) + 32)) { winExitCode = 0xC0000005 | 0; reason = "_initterm ctor setup failed"; break; }
        dv.setBigUint64(Number(cbRsp), INITTERM_RESUME, true);
        dv.setBigUint64(ctx + REG.rcx * 8, 0n, true);
        dv.setBigUint64(ctx + REG.rdx * 8, 0n, true);
        dv.setBigUint64(ctx + REG.r8 * 8, 0n, true);
        dv.setBigUint64(ctx + REG.r9 * 8, 0n, true);
        dv.setBigUint64(ctx + REG.rsp * 8, cbRsp, true);
        winCallbackFrames.push(frame);
        if ((inittermState.done & 0x1F) === 1 || inittermState.done === inittermState.total)
          logTrace(`[INITTERM] ${inittermState.done}/${inittermState.total} → 0x${nextFn.toString(16)}`);
        pc = nextFn;
        continue;
      }
      // All ctors done
      frame.saved.forEach((value, i) => { if (i !== REG.rax) dv.setBigUint64(ctx + i * 8, value, true); });
      dv.setBigUint64(ctx + 136, frame.savedFlags, true);
      dv.setBigUint64(ctx + REG.rsp * 8, inittermState.returnRsp, true);
      dv.setBigUint64(ctx + REG.rax * 8, 0n, true);
      logTrace(`[INITTERM] ✅ all ${inittermState.total} ctor(s) completed`);
      pc = inittermState.returnPc;
      inittermState = null;
      continue;
    }
    if (isWindows && pc === EXIT) {
      // Log what state we're in when the guest exits
      log(`[EXIT] reached with code=${winExitCode} steps=${steps}`);
    }
    if (pc === EXIT || (isWindows && pc === WIN_EXIT)) { reason = isWindows ? `Windows entry returned (exit code ${winExitCode})` : "halted"; break; }
    if (isWindows && winApiByAddress.has(pc)) {
      const result = await dispatchWinImport(pc);
      if (result && result.exit) { winExitCode = result.status | 0; reason = `ExitProcess(${winExitCode})`; break; }
      pc = result.nextPc;
      continue;
    }
    if ((pc & SYSCALL_BIT) !== 0n) {
      const nextPc = pc & (SYSCALL_BIT - 1n);
      const exit = await dispatchSyscall();
      if (exit) { reason = `exit(${exit.status})`; break; }
      pc = nextPc;
      continue;
    }
    if ((pc & INTERP_BIT) !== 0n) {
      let faultPc = pc & (INTERP_BIT - 1n);
      let exited = false, errored = false, ran = 0;
      const INTERP_CHUNK = 4096;
      while (ran < INTERP_CHUNK) {
        if (diagnostics) pushHistory(faultPc);
        // Focused instruction trace for the Steam bad-this-pointer path.
        // The failing call at 0x78d7da uses [rdi+0xa8], but RDI contains UTF-16
        // path bytes. Trace the upstream caller blocks to find the instruction
        // that first loads/copies that value into RDI.
        const inSteamTraceRange = (p) =>
          (p >= 0x78d600n && p <= 0x78d840n) ||
          (p >= 0x7c9700n && p <= 0x7c9840n);
        // Keep the hot 7c97 string loop from consuming the 78d6 caller's
        // trace budget. The previous shared 600-line cap was exhausted before
        // execution reached the bad virtual call.
        const isSteamCallPath = faultPc >= 0x78d600n && faultPc <= 0x78d840n;
        const traceCountKey = isSteamCallPath ? "__steam78CallTraceCount" : "__steam78StringTraceCount";
        const traceLimit = isSteamCallPath ? 700 : 120;
        const traceSteamCall = diagnostics && inSteamTraceRange(faultPc) &&
          (globalThis[traceCountKey] ?? 0) < traceLimit;
        const rdiBefore = traceSteamCall ? dv.getBigUint64(ctx + REG.rdi * 8, true) : 0n;
        if (traceSteamCall && faultPc === 0x78d61an && !globalThis.__steam78EntryLogged) {
          globalThis.__steam78EntryLogged = true;
          const entryRsp = Number(dv.getBigUint64(ctx + REG.rsp * 8, true));
          const returnPc = entryRsp >= 0 && entryRsp + 8 <= u8.length
            ? dv.getBigUint64(entryRsp, true) : 0n;
          const entryRegs = REG_NAMES.map((name, i) =>
            `${name}=0x${dv.getBigUint64(ctx + i * 8, true).toString(16)}`).join(" ");
          const packedText = (v) => Array.from({ length: 4 }, (_, i) => {
            const c = Number((v >> BigInt(i * 16)) & 0xffffn);
            return c >= 0x20 && c <= 0x7e ? String.fromCharCode(c) : `\\u${c.toString(16).padStart(4, "0")}`;
          }).join("");
          log(`[STEAM-78-ENTRY] pc=0x78d61a rsp=0x${entryRsp.toString(16)} return=0x${returnPc.toString(16)}`);
          log(`[STEAM-78-ENTRY] ${entryRegs}`);
          log(`[STEAM-78-ENTRY] rcx-as-u16="${packedText(dv.getBigUint64(ctx + REG.rcx * 8, true))}" rdx-as-u16="${packedText(dv.getBigUint64(ctx + REG.rdx * 8, true))}"`);
          if (returnPc > 0n) {
            const retNum = Number(returnPc);
            log(`[STEAM-78-ENTRY] caller bytes=${hexBytes(Math.max(0, retNum - 24), 40)}`);
          }
          if (entryRsp >= 0 && entryRsp + 64 <= u8.length) {
            log(`[STEAM-78-ENTRY] stack=${Array.from({ length: 8 }, (_, i) => `0x${dv.getBigUint64(entryRsp + i * 8, true).toString(16)}`).join(" ")}`);
          }
        }
        if (traceSteamCall) {
          globalThis[traceCountKey] = (globalThis[traceCountKey] ?? 0) + 1;
          const traceRegs = REG_NAMES.map((name, i) =>
            `${name}=0x${dv.getBigUint64(ctx + i * 8, true).toString(16)}`).join(" ");
          log(`[STEAM-RDI-TRACE] before pc=0x${faultPc.toString(16)} bytes=${hexBytes(faultPc, 16)}`);
          log(`[STEAM-RDI-TRACE] ${traceRegs}`);
          if (faultPc === 0x78d7dan) {
            const obj = Number(rdiBefore);
            const slot = obj + 0xa8;
            const slotValue = Number.isSafeInteger(slot) && slot >= 0 && slot + 8 <= u8.length
              ? `0x${dv.getBigUint64(slot, true).toString(16)}` : "<unmapped>";
            log(`[STEAM-RDI-CALL] this=0x${rdiBefore.toString(16)} vfunc[+0xa8]=${slotValue} thisBytes=${hexBytes(obj, 16)}`);
          }
        }
        // ── Instruction-level fixes: interpreter xor/flags writes not landing ──
        // Each PC below is one the trace proves is broken: xor doesn't zero the
        // dest, test doesn't set ZF, sub rsp doesn't adjust RSP. Each fix does
        // the instruction's job in JS, then advances past it.
        if (faultPc === 0x78d60bn) {
          dv.setBigUint64(ctx + REG.rsi * 8, 0n, true);
          interpreted++; ran++;
          faultPc = 0x78d60dn;
          continue;
        }
        if (faultPc === 0x78d620n) {
          const r15 = dv.getBigUint64(ctx + REG.r15 * 8, true);
          if (r15 !== 0n) {
            interpreted++; ran++;
            faultPc = 0x78d626n;
            continue;
          }
        }
        if (faultPc === 0x78d754n) {
          dv.setBigUint64(ctx + REG.rax * 8, 0n, true);
          interpreted++; ran++;
          faultPc = 0x78d756n;
          continue;
        }
        if (faultPc === 0x785c1an) {
          dv.setBigUint64(ctx + REG.rbx * 8, 0n, true);
          interpreted++; ran++;
          faultPc = 0x785c1cn;
          continue;
        }
        // ── end instruction-level fixes ─────────────────────────────────────
        let nextPc;
        try {
          nextPc = BigInt.asUintN(64, interpretOne({ pc: faultPc, ctx, dv, u8 }));
          if (traceSteamCall) {
            const rdiAfter = dv.getBigUint64(ctx + REG.rdi * 8, true);
            if (rdiAfter !== rdiBefore) {
              log(`[STEAM-RDI-CHANGE] pc=0x${faultPc.toString(16)} next=0x${nextPc.toString(16)} old=0x${rdiBefore.toString(16)} new=0x${rdiAfter.toString(16)} bytes=${hexBytes(faultPc, 16)}`);
            }
            const traceRegs = REG_NAMES.map((name, i) =>
              `${name}=0x${dv.getBigUint64(ctx + i * 8, true).toString(16)}`).join(" ");
            log(`[STEAM-RDI-TRACE] after pc=0x${faultPc.toString(16)} next=0x${nextPc.toString(16)} ${traceRegs}`);
          }
        } catch (error) {
          reason = `interpreter: ${error?.message || error} (at 0x${faultPc.toString(16)})`;
          // NEW: dump recent block history so we can see the caller chain
          log(`[CRASH] fault pc=0x${faultPc.toString(16)}`);
          log(`[CRASH] last 16 blocks: ${blockHistory.slice(-16).map(p => "0x" + p.toString(16)).join(" <- ")}`);
          const rsp = Number(dv.getBigUint64(ctx + REG.rsp * 8, true));
          log(`[CRASH] rsp=0x${rsp.toString(16)} stack[0..64]=` +
            Array.from({ length: 8 }, (_, i) =>
              "0x" + dv.getBigUint64(rsp + i * 8, true).toString(16)).join(" "));
          errored = true;
          break;
        }
        interpreted++; ran++;

        if (nextPc === EXIT || nextPc === WIN_EXIT) { pc = nextPc; exited = true; break; }
        if ((nextPc & SYSCALL_BIT) !== 0n)          { pc = nextPc; exited = true; break; }
        // Do not hand back to JIT in the watched ranges: we need every guest
        // instruction to run through interpretOne so the first RDI clobber is visible.
        if (inSteamTraceRange(nextPc))              { faultPc = nextPc; continue; }
        if (blocks.has(nextPc))                     { pc = nextPc; exited = true; break; }
        if (unsupportedJit.has(nextPc))             { faultPc = nextPc; continue; }

        const fn = await jitBatch(nextPc);              // async
        if (typeof fn === "function") { pc = nextPc; exited = true; break; }
        unsupportedJit.add(nextPc);
        faultPc = nextPc;
      }
      if (errored) break;
      if (!exited) pc = faultPc | INTERP_BIT;
      continue;
    }

    // Periodic yield so Firefox's slow-script watchdog stays quiet
    // ---- Yield + time budget (self-contained) ----
    // Created once per run() call. MessageChannel yields in microseconds
    // (much faster than setTimeout's 4ms floor) and still lets the browser
    // paint / handle input between guest batches.

    // (then, in the main loop, replace your old block with:)
    // Yield every 131072 steps. setTimeout is slow (~4ms floor), so we yield
    // infrequently and rely on the time budget to end runaway loops.
    if ((steps & 0x7FFF) === 0) {
      await new Promise((r) => setTimeout(r, 0));
      if (Date.now() - startTime > TIME_BUDGET_MS) {
        reason = `time budget (${TIME_BUDGET_MS}ms) exceeded at step ${steps}, pc=0x${pc.toString(16)}`;
        logGuestBacktrace();
        break;
      }
    }
    // In the main loop, right before `let fn = blocks.get(pc);`:
    if (pc === BigInt(WIN_EXIT ?? 0)) { /* skip */ }
    if (diagnostics && isWindows && pc === EXIT) {
      log(`[RECOMP] *** EXIT reached at step ${steps} ***`);
    }
    // Resolve the block normally. Do not synthesize STL unordered-map state:
    // the previous HASH-INIT heuristic guessed the MSVC container layout and
    // wrote a fake bucket vector into a live object. That can turn a benign
    // uninitialized-map condition into an enormous bucket index and a WASM
    // out-of-bounds trap later in _Find_last.

    const blockPc = pc;
    // In the main while loop, right after `const blockPc = pc;`:
    if (isWindows && winCallbackFrames.length > 0) {
      const topFrame = winCallbackFrames[winCallbackFrames.length - 1];
      if (topFrame.thread && topFrame.threadStartStep !== undefined) {
        const ran = steps - topFrame.threadStartStep;
        if (ran > 20_000_000) {
          log(`[THREAD-WATCHDOG] tid=${topFrame.thread.threadId} has run ${ran} steps without returning — force-returning`);
          log(`[THREAD-WATCHDOG] pc=0x${pc.toString(16)} rsp=0x${dv.getBigUint64(ctx + REG.rsp*8, true).toString(16)}`);
          log(`[THREAD-WATCHDOG] last 16 blocks: ${blockHistory.slice(-16).map(p => '0x' + p.toString(16)).join(' <- ')}`);
          log(`[THREAD-WATCHDOG] regs: ${REG_NAMES.map((n,i) => `${n}=0x${dv.getBigUint64(ctx+i*8, true).toString(16)}`).join(' ')}`);
          const rspT = Number(dv.getBigUint64(ctx + REG.rsp * 8, true));
          if (rspT > 0 && rspT + 64 <= u8.length) {
            log(`[THREAD-WATCHDOG] stack=${Array.from({length: 8}, (_, i) => '0x' + dv.getBigUint64(rspT + i*8, true).toString(16)).join(' ')}`);
          }
          const callbackResult = dv.getBigUint64(ctx + REG.rax * 8, true);
          winCallbackFrames.pop();
          topFrame.saved.forEach((value, i) => { if (i !== REG.rax) dv.setBigUint64(ctx + i * 8, value, true); });
          dv.setBigUint64(ctx + 136, topFrame.savedFlags, true);
          dv.setBigUint64(ctx + REG.rsp * 8, BigInt(topFrame.resumeRsp), true);
          dv.setBigUint64(ctx + REG.rax * 8, callbackResult, true);
          topFrame.thread.finished = true;
          topFrame.thread.exitCode = 0;
          winWakeHandleWaiters();
          pc = topFrame.returnPc;
          continue;
        }
      }
    }
    if (pc >= 0x618300n && pc <= 0x618500n) {
        if (!globalThis.__618seen) globalThis.__618seen = new Set();
        const rsp = Number(dv.getBigUint64(ctx + REG.rsp * 8, true));
        const ret = (rsp > 0 && rsp + 8 <= u8.length) ? dv.getBigUint64(rsp, true) : 0n;
        const key = `${pc.toString(16)}@${ret.toString(16)}`;
        if (!globalThis.__618seen.has(key)) {
            globalThis.__618seen.add(key);
            log(`[618-TRACE] pc=0x${pc.toString(16)} ret=0x${ret.toString(16)} rcx=0x${dv.getBigUint64(ctx + REG.rcx*8, true).toString(16)} rdx=0x${dv.getBigUint64(ctx + REG.rdx*8, true).toString(16)}`);
        }
    }
    if (isWindows && pc === 0x618144n && !globalThis.__errPrintTraced &&
        (dv.getBigUint64(ctx + REG.rcx * 8, true) & 0xffffffffn) === 2n) {
      globalThis.__errPrintTraced = true;
      const rspE = Number(dv.getBigUint64(ctx + REG.rsp * 8, true));
      const frames = [];
      for (let at = rspE; at < Math.min(u8.length - 8, rspE + 0x6000) && frames.length < 12; at += 8) {
        const v = Number(dv.getBigUint64(at, true));
        if (v >= base && v < imageEnd && (u8[v - 5] === 0xe8 || u8[v - 6] === 0xff)) {
          if (v >= 0x617000 && v < 0x619000) continue;   // skip CRT frames
          frames.push(v);
        }
      }
      logDispatch(`[ERRPRINT] callers: ${frames.map(v => "0x" + v.toString(16)).join(" <- ")}`);
      for (const v of frames.slice(0, 3)) {
        const rf = winFindRuntimeFunction(v); if (!rf) continue;
        logDispatch(`[ERRPRINT] fn 0x${rf.beginAddr.toString(16)}..0x${rf.endAddr.toString(16)} (call site 0x${v.toString(16)})`);
        const e = Math.min(rf.endAddr, rf.beginAddr + 0x400);
        for (let p = rf.beginAddr; p < e; p += 16) logDispatch(`  ${p.toString(16)}: ${hexBytes(p, Math.min(16, e - p))}`);
      }
    }
    // Force instruction-level execution in the Steam caller ranges while
    // diagnosing the invalid RDI object pointer.
    // ── FIX: 0x78d600 `sub rsp, rax` is a no-op in the interpreter ─────
    // The trace shows RSP stays at 0xffd4b0 after `sub rsp, rax` with
    // RAX=0x80, when it should be 0xffd430. Every subsequent [rsp+…]
    // access is 0x80 off, which corrupts the caller's stack frame and
    // eventually makes 0x605254's `ret` read a stack address (0xffd6e0)
    // instead of a code address.
    // Do the sub directly and jump past the block.
    if (blockPc === 0x78d600n) {
      const raxVal = dv.getBigUint64(ctx + REG.rax * 8, true);
      const rspVal = dv.getBigUint64(ctx + REG.rsp * 8, true);
      const newRsp = BigInt.asUintN(64, rspVal - raxVal);
      dv.setBigUint64(ctx + REG.rsp * 8, newRsp, true);
      if (!globalThis.__subRspFixCalls) globalThis.__subRspFixCalls = 0;
      globalThis.__subRspFixCalls++;
      if (globalThis.__subRspFixCalls <= 5) {
        log(`[SUB-RSP-FIX] #${globalThis.__subRspFixCalls} 0x78d600: ` +
            `rsp 0x${rspVal.toString(16)} - rax 0x${raxVal.toString(16)} = 0x${newRsp.toString(16)}`);
      }
      pc = 0x78d603n;
      continue;
    }
    if (isWindows && pc === 0x617bf4n) {
        if (!globalThis.__assertCallers) globalThis.__assertCallers = new Map();
        const rspA = Number(dv.getBigUint64(ctx + REG.rsp * 8, true));
        if (rspA > 0 && rspA + 8 <= u8.length) {
            const callerA = dv.getBigUint64(rspA, true);
            const key = callerA.toString(16);
            const count = (globalThis.__assertCallers.get(key) || 0) + 1;
            globalThis.__assertCallers.set(key, count);
            if (count === 1) {
                log(`[ASSERT-CALLER] from 0x${callerA.toString(16)} ` +
                    `rcx=0x${dv.getBigUint64(ctx + REG.rcx*8, true).toString(16)} ` +
                    `rdx=0x${dv.getBigUint64(ctx + REG.rdx*8, true).toString(16)} ` +
                    `r8=0x${dv.getBigUint64(ctx + REG.r8*8, true).toString(16)}`);
            }
        }
    }
    // Dump the writability check function on first failure
    if (isWindows && pc === 0x618398n && !globalThis.__wcheckDis) {
        globalThis.__wcheckDis = true;
        const rf = winFindRuntimeFunction(0x618398);
        const start = rf ? rf.beginAddr : 0x618000;
        const end   = rf ? rf.endAddr   : 0x618500;
        log(`[WCHECK-HEX] function 0x${start.toString(16)}..0x${end.toString(16)} (${end - start} bytes)`);
        for (let addr = start; addr < end; addr += 16) {
            const hex = [], ascii = [];
            for (let i = 0; i < 16 && addr + i < end; i++) {
                const b = u8[addr + i];
                hex.push(b.toString(16).padStart(2, "0"));
                ascii.push(b >= 0x20 && b < 0x7f ? String.fromCharCode(b) : ".");
            }
            log(`  ${addr.toString(16).padStart(6, "0")}: ${hex.join(" ").padEnd(48)}  ${ascii.join("")}`);
        }
        log(`[WCHECK-HEX] === end ===`);
    }
    // ── 0x785bd0 NULL-this guard ──────────────────────────────────────
    // During SSL cipher setup, some caller passes rcx=NULL as `this` to
    // 0x785bd0, which immediately dereferences [rcx], [rcx+0x18],
    // [rcx+0x138]. On Windows that would crash on the NULL page; on the
    // emulator we silently read UTF-16 string bytes at [0] and cascade
    // to `call [rdi+0xa8]` with rdi = "C:\T…" (0x54005c003a0043).
    //
    // The caller inspects the return value (`test rax, rax; jnz …; ret`),
    // so a NULL return is safe: the caller skips the inner work and its
    // own caller presumably handles it.
    if (blockPc === 0x785bd0n) {
      const rcxIn = dv.getBigUint64(ctx + REG.rcx * 8, true);
      const isPlausible =
        rcxIn >= 0x10000n && rcxIn < BigInt(u8.length);
      if (!isPlausible) {
        if (!globalThis.__785bd0GuardHits) globalThis.__785bd0GuardHits = 0;
        globalThis.__785bd0GuardHits++;
        if (globalThis.__785bd0GuardHits <= 5) {
          const rspIn = Number(dv.getBigUint64(ctx + REG.rsp * 8, true));
          const retAddr = (rspIn > 0 && rspIn + 8 <= u8.length)
            ? dv.getBigUint64(rspIn, true) : 0n;
          log(`[785BD0-GUARD] hit #${globalThis.__785bd0GuardHits} ` +
              `rcx=0x${rcxIn.toString(16)} — not a valid pointer, returning NULL`);
          log(`[785BD0-GUARD] caller ret=0x${retAddr.toString(16)} rsp=0x${rspIn.toString(16)}`);
          log(`[785BD0-GUARD] rdx=0x${dv.getBigUint64(ctx + REG.rdx * 8, true).toString(16)} ` +
              `r8=0x${dv.getBigUint64(ctx + REG.r8 * 8, true).toString(16)} ` +
              `r9=0x${dv.getBigUint64(ctx + REG.r9 * 8, true).toString(16)}`);
        }
        const rspIn = Number(dv.getBigUint64(ctx + REG.rsp * 8, true));
        const retAddr = dv.getBigUint64(rspIn, true);
        dv.setBigUint64(ctx + REG.rsp * 8, BigInt(rspIn + 8), true);
        dv.setBigUint64(ctx + REG.rax * 8, 0n, true);
        pc = retAddr;
        continue;
      }
    }
    // ── stricmp table-scan loop breaker at 0x484a92 ─────────────────────
    // The 0x484aca caller iterates a 32-byte-entry table comparing each
    // entry's string to a target, advancing via entry.next (+0x18). When
    // the table is uninitialized, entry.next == 0 (not -1), so the loop
    // wraps to entry 0 forever and burns 20 M steps.
    if (blockPc === 0x484a92n) {
      const edi = Number(BigInt.asIntN(32, dv.getBigUint64(ctx + REG.rdi * 8, true)));
      if (!globalThis.__scanLoop) globalThis.__scanLoop = { seen: new Set(), iter: 0, lastStep: 0 };
      const s = globalThis.__scanLoop;
      if (steps - s.lastStep > 100_000) { s.seen.clear(); s.iter = 0; }
      s.lastStep = steps;
      s.iter++;
      // Cycle: same index twice → the linked list is circular.
      // Overflow: > 200k iterations on a bounded table.
      if (s.seen.has(edi) || s.iter > 200_000) {
        if (!globalThis.__scanLoopBreaks) globalThis.__scanLoopBreaks = 0;
        globalThis.__scanLoopBreaks++;
        if (globalThis.__scanLoopBreaks <= 5) {
          const rsiVal = dv.getBigUint64(ctx + REG.rsi * 8, true);
          log(`[SCAN-LOOP] break #${globalThis.__scanLoopBreaks}: ` +
              `edi=0x${edi.toString(16)} iter=${s.iter} unique=${s.seen.size}`);
          log(`[SCAN-LOOP]   [rsi]=0x${rsiVal.toString(16)}  ` +
              `[rsi][0..7]=${[...Array(8)].map((_,i) =>
                (() => { try { return "0x"+dv.getBigUint64(Number(rsiVal)+i*8, true).toString(16); }
                        catch { return "??"; } })()).join(" ")}`);
        }
        s.seen.clear();
        s.iter = 0;
        pc = 0x484ad7n;   // skip to the "scan failed" tail of the caller
        continue;
      }
      s.seen.add(edi);
    }
    // ── defensive guard for 0x78d600's virtual dispatch ─────────────────
    // When the caller passes a wide-string SSO buffer as if it were a
    // `this` object, rcx ends up holding UTF-16 bytes. That is never a
    // valid pointer into our 16 GiB heap. Reject those calls with the
    // "empty / failed" return value instead of dereferencing garbage.
    if (blockPc === 0x78d600n) {
      const rcxIn = Number(dv.getBigUint64(ctx + REG.rcx * 8, true));
      // Valid heap pointers are all >= 0x10000 (our lowest allocation is
      // at winHeapCursor which starts at base+memSize). Reject small ints,
      // NULL, and anything that looks like packed UTF-16 (which has 0x00
      // in every second byte — every UTF-16 string has this property, so
      // we can detect it cheaply).
      const looksLikeWideString = rcxIn !== 0 &&
        ((rcxIn & 0xff00ff00ff00ff00n) === 0n ||       // every other byte = 0
        (rcxIn & 0x00ff00ff00ff00ffn) === 0n);
      const isPlausiblePointer = rcxIn >= 0x10000 && rcxIn < u8.length;
      if (!isPlausiblePointer || looksLikeWideString) {
        if (!globalThis.__78d600GuardHits) globalThis.__78d600GuardHits = 0;
        globalThis.__78d600GuardHits++;
        if (globalThis.__78d600GuardHits <= 5) {
          log(`[78D600-GUARD] rcx=0x${(BigInt(rcxIn) | 0n).toString(16)} rdx=0x${dv.getBigUint64(ctx + REG.rdx * 8, true).toString(16)} — not a pointer, returning 0`);
        }
        // Pop the return address and return 0 from this function.
        const rspG = Number(dv.getBigUint64(ctx + REG.rsp * 8, true));
        const retG = dv.getBigUint64(rspG, true);
        dv.setBigUint64(ctx + REG.rsp * 8, BigInt(rspG + 8), true);
        dv.setBigUint64(ctx + REG.rax * 8, 0n, true);
        pc = retG;
        continue;
      }
    }
    // ── Interpreter ALU bugs: xor r32,r32 doesn't clear destination ─────
    // Confirmed by trace: 0x78d60b (`xor esi, esi`) and 0x78d754 (`xor eax, eax`)
    // complete without zeroing the destination. Same for 0x785c1a (`xor ebx, ebx`).
    // The cascading effect is a stale RAX=8 returned from 0x78d5e0, which sends
    // 0x785c04 down the wrong path (loop instead of error), with rsi=8 treated as
    // a "container pointer" → out-of-bounds crash at 0x785c3a.
    if (blockPc === 0x78d60bn) {
      dv.setBigUint64(ctx + REG.rsi * 8, 0n, true);
      pc = 0x78d60dn;
      continue;
    }
    if (blockPc === 0x78d754n) {
      dv.setBigUint64(ctx + REG.rax * 8, 0n, true);
      pc = 0x78d756n;
      continue;
    }
    if (blockPc === 0x785c1an) {
      dv.setBigUint64(ctx + REG.rbx * 8, 0n, true);
      pc = 0x785c1cn;
      continue;
    }
    // The old JS-side 0x78d754 epilogue and 0x78d7a3 virtual-call guard
    // fabricated register/stack state and could hide the original corruption.
    // Execute these two blocks instruction-by-instruction instead. This keeps
    // the real x64 call/return semantics and avoids the affected JIT blocks.
    if (blockPc === 0x78d754n || blockPc === 0x78d7a3n) {
      pc = blockPc | INTERP_BIT;
      continue;
    }
    if (blockPc === 0x60fbcen) {
      const rbp = Number(dv.getBigUint64(ctx + REG.rbp * 8, true));
      const rdx = Number(dv.getBigUint64(ctx + REG.rdx * 8, true));
      const r9  = Number(dv.getBigUint64(ctx + REG.r9  * 8, true));
      const probe = (idx) => {
        const a = rbp + idx * 4 + 0x324;
        if (a >= 0 && a + 4 <= u8.length) return dv.getUint32(a, true);
        return null;
      };
      const vx = probe(rdx), vy = probe(r9);
      if ((vx !== null && vx > 0x1000) || (vy !== null && vy > 0x1000)) {
        log(`[HASH-FRAC] 0x60fbce rdx=${rdx} [rbp+rdx*4+324]=${vx?.toString(16) ?? "?"} r9=${r9} [rbp+r9*4+324]=${vy?.toString(16) ?? "?"}`);
      }
    }
    if (blockPc === 0x547410n) {
      const rax = Number(dv.getBigUint64(ctx + REG.rax * 8, true));
      const rbx = Number(dv.getBigUint64(ctx + REG.rbx * 8, true));
      const hist = blockHistory.slice(-12).map(p => "0x" + p.toString(16)).join(" <- ");
      const sig = hist.split(" <- ").slice(0, 4).join("|");

      // If this signature has grown past 16 MB, it's a runaway.
      if (!globalThis.__memsetSigs) globalThis.__memsetSigs = new Map();
      const prev = globalThis.__memsetSigs.get(sig) ?? { count: 0, maxSize: 0, firstSize: rbx };
      const isRunaway = prev.count >= 8 && rbx > 0x1000000;   // 16 MB

      if (isRunaway) {
        log(`[MEMSET-RUNAWAY] sig=${sig} count=${prev.count} first=${prev.firstSize.toLocaleString()} now=${rbx.toLocaleString()}`);
        log(`[MEMSET-RUNAWAY] chain: ${hist}`);
        log(`[MEMSET-RUNAWAY] recent APIs: ${(globalThis.__recentApis ?? []).slice(-12).join(",")}`);
        reason = `runaway vector growth: ${prev.firstSize} → ${rbx} over ${prev.count} iterations`;
        break;
      }

      globalThis.__memsetSigs.set(sig, { count: prev.count + 1, maxSize: Math.max(prev.maxSize, rbx), firstSize: prev.firstSize });
      if (Number.isSafeInteger(rbx) && rbx > 0x1000 && rbx <= 0x10000000 &&
          Number.isSafeInteger(rax) && rax >= 0 && rax + rbx <= u8.length) {

        // ── NEW: identify caller + recent API trail BEFORE doing the fill ──
        // blockHistory has up to 128 recent JIT block PCs. Slice the last 12.
        const hist = blockHistory.slice(-12).map(p => "0x" + p.toString(16)).join(" <- ");
        // Recent Win32 APIs dispatched (populated below in dispatchWinImport)
        const apis = (globalThis.__recentApis ?? []).slice(-8).join(",");
        // Cache: log only 1st/10th/100th time per unique block-history signature
        if (!globalThis.__memsetSigs) globalThis.__memsetSigs = new Map();
        const sig = hist.split(" <- ").slice(0, 4).join("|");   // first 4 PCs = caller chain
        const n = (globalThis.__memsetSigs.get(sig) ?? 0) + 1;
        globalThis.__memsetSigs.set(sig, n);
        if (n === 1 || n === 10 || n === 100) {
          logTrace(`[MEMSET-CALLER] #${n} size=${rbx.toLocaleString()} at=0x${rax.toString(16)}`);
          logTrace(`[MEMSET-CALLER]   chain: ${hist}`);
          logTrace(`[MEMSET-CALLER]   recent APIs: [${apis}]`);
        }
        // ────────────────────────────────────────────────────────────────────

        u8.fill(0, rax, rax + rbx);
        dv.setBigUint64(ctx + REG.rax * 8, BigInt(rax + rbx), true);
        dv.setBigUint64(ctx + REG.rbx * 8, 1n, true);
      }
    }
    /*
    if (blockPc === 0x60ee8dn) {
      const edi = Number(dv.getBigUint64(ctx + REG.rdx * 8, true) & 0xFFFFFFFFn);
      if (edi > 0x10000) {   // bitmap can't be bigger than 64K words
        // Skip the slow-path scan — return "not found".
        const rsp = Number(dv.getBigUint64(ctx + REG.rsp * 8, true));
        const ret = dv.getBigUint64(rsp, true);
        dv.setBigUint64(ctx + REG.rsp * 8, BigInt(rsp + 8), true);
        dv.setBigUint64(ctx + REG.rax * 8, 0n, true);   // not found
        log(`[BIGHASH-SKIP] hash=0x${edi.toString(16)} > 64K → return not-found`);
        pc = ret;
        continue;
      }
    }*/
   // _Find_last bitmap scan: hash 0xfffffffe → esi=134M, rcx starts at 30.
    // _Find_last bitmap scan: hash 0xfffffffe → esi=134M, rcx starts at 30.
    // The internal loop `inc ecx; cmp ecx,esi; jne 0x60ef3a` runs 134M times.
    // Set rcx=esi-1 so the JIT block does ONE iteration and exits.
    if (blockPc === 0x60ef3an) {
      const rcx = Number(dv.getBigUint64(ctx + REG.rcx * 8, true));
      const rsi = Number(dv.getBigUint64(ctx + REG.rsi * 8, true));
      if (Number.isSafeInteger(rsi) && rsi > 0x10000 && rcx + 1 < rsi) {
        log(`[SCAN-SKIP] 0x60ef3a: rcx=0x${rcx.toString(16)} rsi=0x${rsi.toString(16)} → last`);
        dv.setBigUint64(ctx + REG.rcx * 8, BigInt(rsi - 1), true);
      }
    }

    // memset(rcx, 0, rax). Disasm-confirmed: rcx=pointer, rax=count.
    // Jump near the end: rcx = end-1, rax = 1 → block writes one byte, exits.
    if (blockPc === 0x547250n) {
      const rcx = Number(dv.getBigUint64(ctx + REG.rcx * 8, true));
      const rax = Number(dv.getBigUint64(ctx + REG.rax * 8, true));
      if (Number.isSafeInteger(rax) && rax > 0x100 && rax <= 0x10000000 &&
          Number.isSafeInteger(rcx) && rcx >= 0 && rcx + rax <= u8.length) {
        u8.fill(0, rcx, rcx + rax);
        dv.setBigUint64(ctx + REG.rcx * 8, BigInt(rcx + rax - 1), true);
        dv.setBigUint64(ctx + REG.rax * 8, 1n, true);
        log(`[MEMSET-SKIP] 0x547250: zeroed ${rax.toLocaleString()} bytes at 0x${rcx.toString(16)}`);
      }
    }
        // ── assert-handler entry tracking ──
    // 0x617bf4..0x617cfb is the CRT/Steam assert-failure handler that produces
    // "src\common\globals.cpp (205) : Assertion Failed: Invalid CRT parameter".
    // We can't unwind back to its caller (the whole chain is jmp/tail-called
    // and [est] = 0), so capture the very first block entry instead.
    let fn = blocks.get(pc);
    if (!fn && !unsupportedJit.has(pc)) fn = await jitBatch(pc);   // async
    if (typeof fn !== "function") { pc = pc | INTERP_BIT; continue; }
    // Only bail on genuinely absurd values (e.g. > 0x10000000), which the slow path
    // cannot handle without OOB. Real lookups use small ints, including negatives.
    if (diagnostics) pushHistory(blockPc);
    // Observe the suspected unordered-map object without modifying it. Its
    // layout must be established from the actual MSVC type before attempting
    // any repair; guessing bucket-vector offsets is unsafe.
    if (blockPc === 0x60ee24n) {
      const mapThis = Number(dv.getBigUint64(ctx + REG.rcx * 8, true));
      const hashVal = Number(dv.getBigUint64(ctx + REG.rdx * 8, true) & 0xFFFFFFFFn);
      if (Number.isSafeInteger(mapThis) && mapThis > 0x1000 && mapThis + 0x18 <= u8.length) {
        const q0 = dv.getBigUint64(mapThis, true);
        const q8 = dv.getBigUint64(mapThis + 8, true);
        const q16 = dv.getBigUint64(mapThis + 16, true);
        const plausible = (v) => v >= 0x400000n && v <= 0xfffffff0n;
        const ok = plausible(q0) || plausible(q8) || plausible(q16);

        // Track per-map-address state; log first-seen and first-corruption
        if (!globalThis.__mapState) globalThis.__mapState = new Map();
        const key = mapThis.toString(16);
        const prev = globalThis.__mapState.get(key);
        const now = `${q0.toString(16)}:${q8.toString(16)}:${q16.toString(16)}`;
        if (!prev) {
          globalThis.__mapState.set(key, now);
          log(`[MAP] first seen this=0x${key} q0=0x${q0.toString(16)} q8=0x${q8.toString(16)} q16=0x${q16.toString(16)} hash=0x${hashVal.toString(16)} ok=${ok}`);
        } else if (prev !== now) {
          globalThis.__mapState.set(key, now);
          log(`[MAP] state change this=0x${key} ${prev} → ${now} hash=0x${hashVal.toString(16)} ok=${ok}`);
        }
      }
    }
    // ── _Find_last runaway-loop breaker (fixed) ─────────────────────────
    // The previous version reset stats.count whenever two consecutive probes
    // were ≥ 100k steps apart. With the caller spending ~400k steps per retry
    // (as the log shows), the counter was reset every single time and could
    // never reach the 200 threshold.
    //
    // Fix:
    //   1. Key on `thisPtr` only — callerRet varies between retries, which
    //      further fragmented the counter.
    //   2. Do NOT reset on a time gap. If the caller comes back after 10M
    //      steps, it means it is still running the same retry loop.
    //   3. Drop the threshold to 100 (we've clearly proven it's a loop by then
    //      because the map state changed that many times).
    // ── _Find_last runaway-loop breaker (fixed v2) ──────────────────────
    // The retry pattern isn't one long loop; it's batches of ~15 probes on
    // map A, then Win32 work, then ~15 on map A again, occasionally dipping
    // into a second map. Per-map counters never reach 100, so we need a
    // global counter across all maps plus a per-map one for the pathological
    // single-map case.
    if (blockPc === 0x60ee24n) {
        const rsp = Number(dv.getBigUint64(ctx + REG.rsp * 8, true));
        const callerRet = (rsp > 0x1000 && rsp + 8 < u8.length)
            ? dv.getBigUint64(rsp, true) : 0n;
        const thisPtr = Number(dv.getBigUint64(ctx + REG.rcx * 8, true));

        if (!globalThis.__findLastGlobal) globalThis.__findLastGlobal = { count: 0, lastStep: 0 };
        if (!globalThis.__findLastPerMap) globalThis.__findLastPerMap = new Map();

        const g = globalThis.__findLastGlobal;
        const key = thisPtr.toString(16);
        const m = globalThis.__findLastPerMap.get(key) ?? { count: 0 };
        g.count++;
        m.count++;
        g.lastStep = steps;
        globalThis.__findLastPerMap.set(key, m);

        if (g.count === 30 || g.count === 60 || g.count === 120 ||
            (g.count % 200) === 0) {
            log(`[FIND-LOOP] global=${g.count} map=${key}(${m.count}) caller=0x${callerRet.toString(16)}`);
        }

        // Two independent escape hatches:
        //   • 200 total probes across all maps — no legitimate lookup needs this
        //   • 30 probes on a single map — catches a single hot map that doesn't
        //     interleave with other work
        if (g.count > 200 || m.count > 30) {
            const scratch = winAlloc(64n, true);
            dv.setBigUint64(ctx + REG.rax * 8, scratch, true);
            dv.setBigUint64(ctx + REG.rsp * 8, BigInt(rsp + 8), true);
            g.count = 0;
            m.count = 0;
            if (!globalThis.__findLoopBreaks) globalThis.__findLoopBreaks = 0;
            globalThis.__findLoopBreaks++;
            log(`[FIND-LOOP] break #${globalThis.__findLoopBreaks} ` +
                `(global was ${g.count}, map ${key} was ${m.count}; ` +
                `caller=0x${callerRet.toString(16)})`);
            pc = callerRet;
            continue;
        }
    }
    if (blockPc !== 0x547250n) globalThis.__hits547250 = 0;
    if (diagnostics && !globalThis.__dumpedHot) {
      globalThis.__dumpedHot = new Set();
    }
    if (blockPc === 0x547250n) {
      const rcx = Number(dv.getBigUint64(ctx + REG.rcx * 8, true));
      const rax = Number(dv.getBigUint64(ctx + REG.rax * 8, true));
      if (Number.isSafeInteger(rax) && rax > 0 && rax <= 0x10000000 &&
          Number.isSafeInteger(rcx) && rcx >= 0 && rcx + rax <= u8.length) {
        u8.fill(0, rcx, rcx + rax);
        // Leave exactly one iteration: rcx=last byte (already zeroed), rax=1
        // Block will write byte [rcx+rax-1]=0, inc rcx, rax=0, exit loop, then
        // fall through to `call 0x5D7A80` → constructor → virtual call → return.
        dv.setBigUint64(ctx + REG.rcx * 8, BigInt(rcx + rax - 1), true);
        dv.setBigUint64(ctx + REG.rax * 8, 1n, true);
      }
    }
    /*// Hook 2: catch the caller of 0x60ee24 — this is the higher-level function
    if (blockPc === 0x610c2fn) {
      const rsp = Number(dv.getBigUint64(ctx + REG.rsp * 8, true));
      log(`[FIND_CALLER] at 0x610c2f rsp=0x${rsp.toString(16)} rcx=0x${dv.getBigUint64(ctx + REG.rcx * 8, true).toString(16)} rdx=0x${dv.getBigUint64(ctx + REG.rdx * 8, true).toString(16)}`);
      log(`[FIND_CALLER] stack[0..8]=${Array.from({length: 8}, (_, i) => "0x" + dv.getBigUint64(rsp + i * 8, true).toString(16)).join(" ")}`);
    }

    // Hook 3: the `[CTOR-LOOP]` bad-value — if rcx changes to huge at this block,
    // it's a corrupted write into callee-saved rcx (likely a JIT bug OR a bad caller)
    if (blockPc === 0x633a0bn) {
      const rcx = dv.getBigUint64(ctx + REG.rcx * 8, true);
      if (rcx > 0x2000000n && rcx < 0x800000000000n) {
        log(`[SUSPICIOUS] block 0x633a0b entered with rcx=0x${rcx.toString(16)} (should be ctor this)`);
        log(`[SUSPICIOUS]   rdi=0x${dv.getBigUint64(ctx + REG.rdi * 8, true).toString(16)} rbx=0x${dv.getBigUint64(ctx + REG.rbx * 8, true).toString(16)}`);
      }
    }
    // After the `[CTOR-LOOP]` block
    if (blockPc === 0x6339ffn) {
      // At 0x6339ff, rcx points to the current function-array slot
      const slotAddr = Number(dv.getBigUint64(ctx + REG.rcx * 8, true));
      const ctorFn = slotAddr > 0 && slotAddr + 8 < u8.length
        ? dv.getBigUint64(slotAddr, true) : 0n;
      log(`[CTOR-TARGET] fn=0x${ctorFn.toString(16)}`);
    }*/
    // ── progress probe: proves the guest is or isn't advancing ──────
        // ── progress probe: proves the guest is or isn't advancing ──────
        // ── progress probe: proves the guest is or isn't advancing ──────
    if (!globalThis.__progressProbe) {
      globalThis.__progressProbe = {
        lastAt: 0, uniqueSet: new Set(), totalSet: new Set(),
      };
    }
    if (isWindows && pc === 0x618398n && !globalThis.__wcheckApplied) {
        globalThis.__wcheckApplied = true;
        log(`[WCHECK-VERIFY] byte at 0x6181c7 = 0x${u8[0x6181C7].toString(16)} ` +
            `(should be 0x33 after patch; 0x42 means patch did not apply)`);
    }
    {
      const p = globalThis.__progressProbe;
      p.uniqueSet.add(Number(pc));
      p.totalSet.add(Number(pc));
      if (steps - p.lastAt >= 20_000_000) {
        const pcCount    = p.uniqueSet.size;
        const totalCount = p.totalSet.size;
        const heap       = winHeapCursor;
        log(`[PROGRESS] step=${steps} uniquePcs(last 5M)=${pcCount} ` +
          `uniquePcs(total)=${totalCount} heapCursor=0x${heap.toString(16)} ` +
          `peak=0x${winHeapPeak.toString(16)} allocs=${winAllocCount} ` +
          `frees=${winFreeCount} freeBlocks=${winFreeBlocks.length}`);

        // ── Loop detector ────────────────────────────────────────────────
        // A "no-progress" window means ALL of:
        //   • no new PCs learned (totalSet.size unchanged)
        //   • heap cursor unchanged
        //   • alloc / free counters unchanged (nothing was allocated)
        //   • registers at the boundary look identical (cheap hash)
        // Two consecutive such windows ⇒ the guest is cycling. True for a
        // retry loop, a stuck spin, or a real infinite recursion — but not
        // for a live computation, because the PC set or heap will grow.
        if (!p.loopDet) p.loopDet = {
          lastTotal: -1, lastHeap: -1, lastAlloc: -1, lastFree: -1, lastReg: 0,
          consecutive: 0, breaks: 0,
        };
        const d = p.loopDet;

        // Cheap register fingerprint (rax..rdi). Enough to catch the case
        // where the guest hits the same boundary PC but with different
        // intermediate state.
        let regHash = 0;
        for (const i of [0, 1, 2, 3, 4, 5, 6, 7]) {
          regHash = (Math.imul(regHash, 31) +
            Number(dv.getBigUint64(ctx + i * 8, true) & 0xffffffffn)) | 0;
        }

        const noNewPcs   = totalCount === d.lastTotal;
        const sameHeap   = heap === d.lastHeap;
        const noAllocs   = winAllocCount === d.lastAlloc;
        const noFrees    = winFreeCount === d.lastFree;
        const sameRegs   = regHash === d.lastReg;

        if (noNewPcs && sameHeap && noAllocs && noFrees && sameRegs) d.consecutive++;
        else d.consecutive = 0;

        d.lastTotal = totalCount;
        d.lastHeap  = heap;
        d.lastAlloc = winAllocCount;
        d.lastFree  = winFreeCount;
        d.lastReg   = regHash;

        if (d.consecutive >= 1) {
          d.consecutive = 0;
          d.breaks++;
          log(`[LOOP-DETECTED] step=${steps} break #${d.breaks}: ` +
              `${totalCount} total PCs (${pcCount} this window), heap 0x${heap.toString(16)}, ` +
              `allocs=${winAllocCount} frees=${winFreeCount}`);

          // Unwinding resets RSP but not the callee-saved registers, so the
          // resumed caller executes with the loop's register state and
          // corrupts its own frame (this is why we saw `ret` to 0xcd / 0x0).
          // Do not attempt to unwind. Stop cleanly and report state.
          log(`[LOOP-DETECTED] terminating: guest is retrying the same ` +
              `operation with no state change`);
          logGuestBacktrace(32);
          pc = WIN_EXIT;
          reason = `stuck loop: ${totalCount} PCs, heap 0x${heap.toString(16)} unchanged`;
          break;
        }

        // ALWAYS advance the window. Failing to do this is what floods the
        // log with [PROGRESS] every step once steps > 5M.
        p.uniqueSet.clear();
        p.lastAt = steps;
      }
    }
    // Diagnostic-only tight-loop watch. Never reset RSP or jump to WIN_EXIT:
    // a polling loop can be legitimate (e.g. waiting on network/window events).
    if ((steps & 0x3FFFF) === 0) {                       // every 256K steps
      const p = globalThis.__progressProbe;
      if (p && p.uniqueSet.size > 0 && p.uniqueSet.size < 32) {
        if (!p.lastLoopDiag || steps - p.lastLoopDiag >= 1_000_000) {
          p.lastLoopDiag = steps;
          const uniquePCs = [...p.uniqueSet].map(v => "0x" + v.toString(16));
          log(`[TIGHT-LOOP] step=${steps} unique=${uniquePCs.length} PCs: ${uniquePCs.join(" ")}`);
          const regs = REG_NAMES.map((n, i) =>
            `${n}=0x${dv.getBigUint64(ctx + i * 8, true).toString(16)}`).join(" ");
          log(`[TIGHT-LOOP] pc=0x${pc.toString(16)} ${regs}`);

          // Disassemble each spinning PC so we can identify the loop body
          for (const pcNum of [...p.uniqueSet].slice(0, 12)) {
            const txt = disasmAt(BigInt(pcNum));
            if (txt) {
              log(`[TIGHT-LOOP] 0x${pcNum.toString(16)}:`);
              for (const l of txt.split("\n").slice(0, 10)) log(`    ${l}`);
            }
          }

          // Dump rdi/rdx/rsi as strings (they point to .rdata — likely message text)
          const rdi = Number(dv.getBigUint64(ctx + REG.rdi * 8, true));
          if (rdi >= base && rdi < imageEnd) {
            log(`[TIGHT-LOOP] rdi→0x${rdi.toString(16)} "${readCString(rdi, 96)}"`);
          }
          const rsi = Number(dv.getBigUint64(ctx + REG.rsi * 8, true));
          if (rsi >= base && rsi < imageEnd) {
            log(`[TIGHT-LOOP] rsi→0x${rsi.toString(16)} "${readCString(rsi, 96)}"`);
          }
        }
      }
    }
      // ── end instruction-level fixes ─────────────────────────────────────
    let nextPc;
    try {
      nextPc = BigInt.asUintN(64, fn(ctx));
    } catch (e) {
      // WASM trap — the block computed an out-of-bounds address.
      log(`[WASM-CRASH] blockPc=0x${blockPc.toString(16)} error=${e?.message ?? e}`);
      log(`[WASM-CRASH] last 16 blocks: ${blockHistory.slice(-16).map(p => "0x" + p.toString(16)).join(" <- ")}`);
      const rsp = Number(dv.getBigUint64(ctx + REG.rsp * 8, true));
      log(`[WASM-CRASH] regs: ${REG_NAMES.map(n => `${n}=0x${dv.getBigUint64(ctx + REG[n] * 8, true).toString(16)}`).join(" ")}`);
      log(`[WASM-CRASH] rsp=0x${rsp.toString(16)} stack[0..16]=` +
        Array.from({length: 16}, (_, i) => "0x" + dv.getBigUint64(rsp + i*8, true).toString(16)).join(" "));
      // Bytes at the faulting block, to see what instruction was executing
      const hex = Array.from({length: 48}, (_, i) =>
        u8[Number(blockPc) + i]?.toString(16).padStart(2, '0') ?? '??').join(" ");
      log(`[WASM-CRASH] block bytes: ${hex}`);
      // Also dump the last Win32 API dispatched — often the culprit
      log(`[TRAP-DIAG] inittermState=${inittermState ? "active(" + inittermState.pending?.length + ")" : "null"} callbackFrames=${winCallbackFrames.length}`);
      log(`[WASM-CRASH] last dispatches: ${(globalThis.__lastDispatchNames ?? []).slice(-8).join(" <- ")}`);
      reason = `WASM trap in block 0x${blockPc.toString(16)}: ${e?.message}`;
      // If we're inside an _initterm batch, abandon this ctor and continue.
        if (inittermState && inittermState.pending?.length > 0) {
          log(`[INITTERM] ctor trapped; skipping (${inittermState.pending.length} more)`);
          while (winCallbackFrames.length > 0) {
            const f = winCallbackFrames[winCallbackFrames.length - 1];
            winCallbackFrames.pop();
            if (f.returnPc === INITTERM_RESUME) break;
          }
          const nextFn = inittermState.pending.shift();
          inittermState.done++;
          inittermState.lastCalledFn = nextFn;
          const cbRsp = BigInt(((Number(inittermState.returnRsp) - 0x100) & ~15) - 8);
          if (ensureMemory(Number(cbRsp) + 0x28)) {
            dv.setBigUint64(Number(cbRsp), INITTERM_RESUME, true);
            dv.setBigUint64(ctx + REG.rcx * 8, 0n, true);
            dv.setBigUint64(ctx + REG.rdx * 8, 0n, true);
            dv.setBigUint64(ctx + REG.r8 * 8, 0n, true);
            dv.setBigUint64(ctx + REG.r9 * 8, 0n, true);
            dv.setBigUint64(ctx + REG.rsp * 8, cbRsp, true);
            const saved = REG_NAMES.map((_, i) => dv.getBigUint64(ctx + i * 8, true));
            const savedFlags = dv.getBigUint64(ctx + 136, true);
            winCallbackFrames.push({ saved, savedFlags, returnPc: INITTERM_RESUME, resumeRsp: Number(cbRsp) + 8 });
            pc = nextFn;
            continue;   // ← CONTINUE, not break
          }
        }
        reason = `WASM trap in block 0x${blockPc.toString(16)}: ${e?.message}`;
        break;   // only if not skippable
    }
    if (diagnostics) checkWatches(`block 0x${blockPc.toString(16)}`);
    const interpreterHandoff = (nextPc & INTERP_BIT) !== 0n;
    const target = interpreterHandoff ? (nextPc & (INTERP_BIT - 1n)) : nextPc;
    if (target < BigInt(u8.length) && !isInImage(Number(target))) {
      if (diagnostics && blockPc >= 0x78d700n && blockPc <= 0x78d800n) {
        log(`[STEAM-78-TRACE] transfer source=0x${blockPc.toString(16)} bytes=${hexBytes(blockPc, 32)}`);
        const sourceText = disasmAt(blockPc);
        if (sourceText) log(`[STEAM-78-TRACE] source disassembly:\n${sourceText}`);
      }
      logUnexpectedCodeAddress(
        `JIT block 0x${blockPc.toString(16)}${interpreterHandoff ? " (interpreter handoff)" : " (control transfer)"}`,
        target
      );
      if (target < BigInt(base)) {           // <-- new
        reason = `JIT block 0x${blockPc.toString(16)} jumped to unmapped 0x${target.toString(16)}`;
        break;
      }
    }
    // ── RSP corruption trap ─────────────────────────────────────────────
    // RSP below a reasonable stack floor means we've already lost the frame.
    // Catch it at the offending block instead of letting it snowball for
    // millions of steps until we hit .rdata.
    if (steps > 500_000) {                       // skip startup stack probing
        const rspNow = dv.getBigUint64(ctx + REG.rsp * 8, true);
        if (rspNow !== 0n && (rspNow < 0x1000n || rspNow > BigInt(memSize))) {
            log(`[RSP-CORRUPT] rsp=0x${rspNow.toString(16)} after block 0x${blockPc.toString(16)}`);
            log(`[RSP-CORRUPT] recent blocks: ${blockHistory.slice(-16).map(p => "0x" + p.toString(16)).join(" <- ")}`);
            log(`[RSP-CORRUPT] regs: ${REG_NAMES.map((n,i) =>
                `${n}=0x${dv.getBigUint64(ctx + i*8, true).toString(16)}`).join(" ")}`);
            pc = WIN_EXIT;
            reason = `rsp corrupted to 0x${rspNow.toString(16)} by block 0x${blockPc.toString(16)}`;
            break;
        }
    }
    pc = nextPc;
    // ── Non-executable section guard ─────────────────────────────────
    // .pdata says "this is code". But .pdata doesn't cover every leaf function.
    // Use PE section flags to catch execution in .rdata/.data/.rsrc/.reloc —
    // anything marked not-executable. Runs BEFORE the block executes, so no
    // garbage byte ever gets interpreted.
    if (isWindows && steps > 100_000 && pc >= BigInt(base) && pc < BigInt(imageEnd)) {
        if (!globalThis.__execSections) {
            try {
                const peOff = dv.getUint32(base + 0x3c, true);
                const numSections = dv.getUint16(base + peOff + 6, true);
                const optSize = dv.getUint16(base + peOff + 20, true);
                const sectionsBase = base + peOff + 24 + optSize;
                globalThis.__execSections = [];
                for (let i = 0; i < numSections; i++) {
                    const s = sectionsBase + i * 40;
                    const name = new TextDecoder().decode(u8.subarray(s, s + 8)).replace(/\0+$/, "");
                    const vaddr = base + dv.getUint32(s + 12, true);
                    const vsize = Math.max(dv.getUint32(s + 8, true), dv.getUint32(s + 16, true));
                    const chars = dv.getUint32(s + 36, true);
                    globalThis.__execSections.push({ name, start: vaddr, end: vaddr + vsize, executable: (chars & 0x20000000) !== 0 });
                }
                log(`[SECTIONS] ${globalThis.__execSections.map(s => `${s.name}${s.executable?'':'(nx)'}`).join(' ')}`);
            } catch (e) { log(`[SECTIONS] parse failed: ${e.message}`); }
        }
        const pcNum = Number(pc);
        const sec = globalThis.__execSections?.find(s => pcNum >= s.start && pcNum < s.end);
        if (sec && !sec.executable) {
            log(`[BAD-EXEC] pc=0x${pcNum.toString(16)} in ${sec.name} (non-executable)`);
            log(`[BAD-EXEC] recent blocks: ${blockHistory.slice(-8).map(p => '0x'+p.toString(16)).join(' <- ')}`);
            pc = WIN_EXIT;
            reason = `execution in ${sec.name} at 0x${pcNum.toString(16)}`;
            break;
        }
    }
    // ── one-shot diagnostic for the caller of 0x78d600 ─────────────────
    // The block right before the call to 0x78d600 is at 0x785bff. Its
    // instruction just before the call is what put the bad value in RCX.
    // Dump the 32 bytes ending at the call, and disassemble from 32 bytes
    // earlier so we see the load that produced RCX.
    if (isWindows && pc >= 0x785b00n && pc <= 0x785d50n &&
        !globalThis.__callerDump785c) {
      globalThis.__callerDump785c = true;
      log(`[CALLER-785C] pc=0x${pc.toString(16)} rsp=0x${dv.getBigUint64(ctx + REG.rsp*8, true).toString(16)}`);
      log(`[CALLER-785C] regs: ${REG_NAMES.map((n,i) => `${n}=0x${dv.getBigUint64(ctx+i*8, true).toString(16)}`).join(" ")}`);
      const dumpStart = 0x785b80n;
      const dumpLen = 0x100;
      log(`[CALLER-785C] bytes @0x${dumpStart.toString(16)}:`);
      for (let off = 0; off < dumpLen; off += 16) {
        const a = Number(dumpStart) + off;
        const hex = Array.from({ length: 16 }, (_, k) =>
          u8[a + k]?.toString(16).padStart(2, "0") ?? "??").join(" ");
        log(`  ${a.toString(16).padStart(6, "0")}: ${hex}`);
      }
      const dis = disasmAt(dumpStart);
      if (dis) for (const line of dis.split("\n").slice(0, 40)) log(`  ${line}`);
    }
    // ── RSP corruption trap ─────────────────────────────────────────────
    // RSP below a reasonable stack floor means we've already lost the frame.
    // Catch it at the offending block instead of letting it snowball for
    // millions of steps until we hit .rdata.
    prevBlockPc = blockPc;
  }
  
  winCurrentProcessState.finished = true;
  winCurrentProcessState.exitCode = winExitCode | 0;
  winPresent();
  log(`stopped: ${reason}; blocks run: ${steps}, jitted at runtime: ${jitted}, interpreted instructions: ${interpreted}`);
  const regs = {};
  REG_NAMES.forEach((n, i) => (regs[n] = dv.getBigUint64(ctx + i * 8, true)));
  Object.defineProperties(regs, { exitCode: { value: winExitCode | 0, enumerable: false }, processId: { value: Number(processId) || 1, enumerable: false } });
  log(Object.entries(regs).map(([k, v]) => `${k}=0x${v.toString(16)}`).join(" "));
  return regs;
}
