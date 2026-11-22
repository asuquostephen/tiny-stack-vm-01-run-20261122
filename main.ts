// Tiny stack VM — make.fun tiny-stack-vm-01 (ISA v1). Written from ISA.md; the
// reference VM (kit/program/generator/subject/vm.mjs) is the rule where the two differ.
// One run answers every instance under the input dir: per <id> it reads program.bin
// + input.bin and writes stdout.bin + exit.txt under the output dir.
import { mkdirSync, readFileSync, readdirSync, writeFileSync, existsSync } from 'node:fs';
import { join } from 'node:path';

// [immediate bytes, pops, pushes] for opcodes not shaped [0,2,1]; 0x10-0x1E and
// 0x20-0x22 default to [0,2,1]; any other byte with no entry is not an opcode
// (note: 0x1F is not an opcode). NEG (0x17) and NOT (0x1B) are unary, so they
// sit in the table even though they fall inside the 0x10-0x1E band.
const SH = {
  0x00: [0, 0, 0], 0x01: [1, 0, 1], 0x02: [4, 0, 1], 0x03: [0, 1, 0],
  0x04: [0, 1, 2], 0x05: [0, 2, 2], 0x06: [0, 2, 3], 0x07: [0, 3, 3],
  0x17: [0, 1, 1], 0x1b: [0, 1, 1],
  0x30: [2, 0, 0], 0x31: [2, 1, 0], 0x32: [2, 1, 0], 0x33: [2, 0, 0],
  0x34: [0, 0, 0], 0x40: [0, 1, 1], 0x41: [0, 2, 0],
  0x50: [0, 1, 0], 0x51: [0, 1, 0], 0x52: [0, 0, 1], 0x53: [0, 1, 0],
};

function run(p, inp) {
  const n = p.length;
  const S = new Int32Array(256); let sp = 0;      // data stack
  const C = new Int32Array(64); let cp = 0;       // call stack
  const M = new Int32Array(256);                  // memory
  const O = new Uint8Array(65536); let ol = 0;    // output buffer
  let ip = 0, pc = 0, st = 0;
  const fin = (e) => ({ exit: e, out: O.subarray(0, ol) });

  for (;;) {
    // Checks in the reference's exact order.
    if (st === 1000000) return fin(10);           // step limit
    if (pc < 0 || pc >= n) return fin(9);         // pc outside the program
    const op = p[pc];
    let sh = SH[op];
    if (!sh) {
      if ((op >= 0x10 && op <= 0x1e) || (op >= 0x20 && op <= 0x22)) sh = [0, 2, 1];
      else return fin(5);                         // unknown opcode
    }
    if (pc + sh[0] >= n) return fin(9);           // immediate cut off
    st++;
    const nx = pc + 1 + sh[0];                    // address past this instruction
    if (sp < sh[1]) return fin(2);                // stack underflow
    if (sp - sh[1] + sh[2] > 256) return fin(3);  // stack overflow
    pc = nx;

    if (op === 0x00) return fin(0);               // HALT
    if (op === 0x01) { S[sp++] = (p[nx - 1] << 24) >> 24; continue; } // PUSH8, sign-extended
    if (op === 0x02) { S[sp++] = p[nx - 4] | (p[nx - 3] << 8) | (p[nx - 2] << 16) | (p[nx - 1] << 24); continue; } // PUSH32, little-endian
    if (op === 0x03) { sp--; continue; }          // POP
    if (op === 0x04) { S[sp] = S[sp - 1]; sp++; continue; } // DUP
    if (op === 0x05) { const t = S[sp - 1]; S[sp - 1] = S[sp - 2]; S[sp - 2] = t; continue; } // SWAP
    if (op === 0x06) { S[sp] = S[sp - 2]; sp++; continue; } // OVER
    if (op === 0x07) { const a = S[sp - 3]; S[sp - 3] = S[sp - 2]; S[sp - 2] = S[sp - 1]; S[sp - 1] = a; continue; } // ROT
    if (op === 0x17) { S[sp - 1] = -S[sp - 1] | 0; continue; } // NEG (wraps)
    if (op === 0x1b) { S[sp - 1] = ~S[sp - 1]; continue; } // NOT

    if (op >= 0x10 && op <= 0x22) { // binary operators (NEG/NOT already handled)
      const b = S[sp - 1], a = S[sp - 2];
      let r;
      switch (op) {
        case 0x10: r = (a + b) | 0; break;                                  // ADD
        case 0x11: r = (a - b) | 0; break;                                  // SUB
        case 0x12: r = Math.imul(a, b); break;                              // MUL, low 32 bits
        case 0x13: if (!b) return fin(4); r = a === -2147483648 && b === -1 ? a : (a / b) | 0; break; // DIV
        case 0x14: if (!b) return fin(4); r = b === -1 ? 0 : (a % b) | 0; break; // MOD, sign of a
        case 0x15: if (!b) return fin(4); r = Math.floor((a >>> 0) / (b >>> 0)) | 0; break; // DIVU
        case 0x16: if (!b) return fin(4); r = ((a >>> 0) % (b >>> 0)) | 0; break; // MODU
        case 0x18: r = a & b; break;                                        // AND
        case 0x19: r = a | b; break;                                        // OR
        case 0x1a: r = a ^ b; break;                                        // XOR
        case 0x1c: r = a << (b & 31); break;                                // SHL
        case 0x1d: r = a >> (b & 31); break;                                // SHR, arithmetic
        case 0x1e: r = (a >>> (b & 31)) | 0; break;                         // SHRU, logical
        case 0x20: r = a === b ? 1 : 0; break;                              // EQ
        case 0x21: r = a < b ? 1 : 0; break;                                // LT, signed
        default: r = (a >>> 0) < (b >>> 0) ? 1 : 0;                         // LTU, unsigned
      }
      sp -= 2;
      S[sp++] = r;
      continue;
    }

    if (op === 0x30 || op === 0x31 || op === 0x32) { // JMP / JZ / JNZ
      const rel = ((p[nx - 2] | (p[nx - 1] << 8)) << 16) >> 16; // signed 16-bit offset
      let take = true;
      if (op !== 0x30) { const v = S[--sp]; take = op === 0x31 ? v === 0 : v !== 0; }
      if (take) pc = nx + rel;
      continue;
    }
    if (op === 0x33) { // CALL: target is the unsigned 16-bit immediate
      if (cp === 64) return fin(7);
      C[cp++] = nx;
      pc = p[nx - 2] | (p[nx - 1] << 8);
      continue;
    }
    if (op === 0x34) { // RET
      if (!cp) return fin(8);
      pc = C[--cp];
      continue;
    }
    if (op === 0x40) { // LOAD
      const a = S[sp - 1];
      if (a < 0 || a > 255) return fin(6);
      S[sp - 1] = M[a];
      continue;
    }
    if (op === 0x41) { // STORE: (v addr --)
      const a = S[sp - 1], v = S[sp - 2];
      if (a < 0 || a > 255) return fin(6);
      sp -= 2;
      M[a] = v;
      continue;
    }
    if (op === 0x50) { // PRINT: decimal ASCII, no newline
      const t = String(S[sp - 1]); // "-2147483648" for INT_MIN, 11 bytes
      if (ol + t.length > 65536) return fin(11);
      sp--;
      for (let i = 0; i < t.length; i++) O[ol++] = t.charCodeAt(i);
      continue;
    }
    if (op === 0x51) { // PUTC
      if (ol + 1 > 65536) return fin(11);
      O[ol++] = S[--sp] & 255;
      continue;
    }
    if (op === 0x52) { // IN: -1 forever once the input is used up
      S[sp++] = ip < inp.length ? inp[ip++] : -1;
      continue;
    }
    return fin(S[--sp] & 255); // 0x53 EXIT: low byte
  }
}

// program/v1 driver
const I = process.env.MAKEFUN_INPUT_DIR ?? '/input';
const O = process.env.MAKEFUN_OUTPUT_DIR ?? '/output';
for (const id of readdirSync(I).sort()) {
  const d = join(I, id), pp = join(d, 'program.bin');
  if (!existsSync(pp)) continue;
  const inpPath = join(d, 'input.bin');
  const { exit, out } = run(readFileSync(pp), existsSync(inpPath) ? readFileSync(inpPath) : Buffer.alloc(0));
  const od = join(O, id);
  mkdirSync(od, { recursive: true });
  writeFileSync(join(od, 'stdout.bin'), out);
  writeFileSync(join(od, 'exit.txt'), exit + '\n');
}
