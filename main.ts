// Tiny stack VM v2 — exact interpreter for make.fun's tiny stack ISA v1.
// Compact on purpose: at equal scores the smaller entry wins the tie.
// Semantics mirror the kit's reference VM: per-step order is step limit,
// pc range, opcode known, immediate fits, underflow, overflow, own trap.
import { mkdirSync, readFileSync, readdirSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';

const PO = [0, 0, 0, 1, 1, 2, 2, 3]; // pops for opcodes 0..7
const PU = [0, 1, 1, 0, 2, 2, 3, 3]; // pushes for opcodes 0..7

function run(P, I) {
  const D = new Int32Array(256), C = new Int32Array(64), M = new Int32Array(256), O = new Uint8Array(65536);
  let sp = 0, cp = 0, pc = 0, ip = 0, ol = 0, st = 0;
  const n = P.length;
  try {
    for (;;) {
      if (st == 1000000) throw 10;
      if (pc < 0 || pc >= n) throw 9;
      const op = P[pc];
      if (!(op < 8 || (op >= 16 && op <= 30) || (op >= 32 && op <= 34) || (op >= 48 && op <= 52) || op == 64 || op == 65 || (op >= 80 && op <= 83))) throw 5;
      const im = op == 1 ? 1 : op == 2 ? 4 : op >= 48 && op <= 51 ? 2 : 0;
      if (pc + im >= n) throw 9;
      st++;
      const nx = pc + 1 + im;
      let po = 0, pu = 0;
      if (op < 8) { po = PO[op]; pu = PU[op]; }
      else if (op < 35) { po = op == 23 || op == 27 ? 1 : 2; pu = 1; }
      else if (op < 53) po = op == 49 || op == 50 ? 1 : 0;
      else if (op < 66) { po = op - 63; pu = op == 64 ? 1 : 0; }
      else { po = op == 82 ? 0 : 1; pu = op == 82 ? 1 : 0; }
      if (sp < po) throw 2;
      if (sp - po + pu > 256) throw 3;
      pc = nx;
      if (op == 0) return [O.slice(0, ol), 0];
      else if (op == 1) D[sp++] = (P[nx - 1] << 24) >> 24;
      else if (op == 2) D[sp++] = P[nx - 4] | P[nx - 3] << 8 | P[nx - 2] << 16 | P[nx - 1] << 24;
      else if (op == 3) sp--;
      else if (op == 4) { D[sp] = D[sp - 1]; sp++; }
      else if (op == 5) { const t = D[sp - 1]; D[sp - 1] = D[sp - 2]; D[sp - 2] = t; }
      else if (op == 6) { D[sp] = D[sp - 2]; sp++; }
      else if (op == 7) { const t = D[sp - 3]; D[sp - 3] = D[sp - 2]; D[sp - 2] = D[sp - 1]; D[sp - 1] = t; }
      else if (op == 23) D[sp - 1] = -D[sp - 1];
      else if (op == 27) D[sp - 1] = ~D[sp - 1];
      else if (op < 35) {
        const b = D[sp - 1], a = D[sp - 2];
        let r;
        if (op == 16) r = a + b;
        else if (op == 17) r = a - b;
        else if (op == 18) r = Math.imul(a, b);
        else if (op == 19) { if (!b) throw 4; r = a / b; }
        else if (op == 20) { if (!b) throw 4; r = a % b; }
        else if (op == 21) { if (!b) throw 4; r = Math.floor((a >>> 0) / (b >>> 0)); }
        else if (op == 22) { if (!b) throw 4; r = (a >>> 0) % (b >>> 0); }
        else if (op == 24) r = a & b;
        else if (op == 25) r = a | b;
        else if (op == 26) r = a ^ b;
        else if (op == 28) r = a << b;
        else if (op == 29) r = a >> b;
        else if (op == 30) r = a >>> b;
        else if (op == 32) r = a == b ? 1 : 0;
        else if (op == 33) r = a < b ? 1 : 0;
        else r = (a >>> 0) < (b >>> 0) ? 1 : 0;
        D[sp - 2] = r; sp--;
      }
      else if (op < 51) {
        const rel = ((P[nx - 2] | P[nx - 1] << 8) << 16) >> 16;
        let take = op == 48;
        if (!take) take = (D[--sp] == 0) == (op == 49);
        if (take) pc = nx + rel;
      }
      else if (op == 51) { if (cp == 64) throw 7; C[cp++] = nx; pc = P[nx - 2] | P[nx - 1] << 8; }
      else if (op == 52) { if (cp == 0) throw 8; pc = C[--cp]; }
      else if (op == 64) { const a = D[sp - 1]; if (a < 0 || a > 255) throw 6; D[sp - 1] = M[a]; }
      else if (op == 65) { const a = D[sp - 1]; if (a < 0 || a > 255) throw 6; M[a] = D[sp - 2]; sp -= 2; }
      else if (op == 80) {
        const s = '' + D[sp - 1];
        if (ol + s.length > 65536) throw 11;
        for (let i = 0; i < s.length; i++) O[ol++] = s.charCodeAt(i);
        sp--;
      }
      else if (op == 81) { if (ol > 65535) throw 11; O[ol++] = D[--sp] & 255; }
      else if (op == 82) D[sp++] = ip < I.length ? I[ip++] : -1;
      else return [O.slice(0, ol), D[--sp] & 255];
    }
  } catch (e) {
    if (typeof e != 'number') throw e;
    return [O.slice(0, ol), e];
  }
}

const I = process.env.MAKEFUN_INPUT_DIR ?? '/input';
const O = process.env.MAKEFUN_OUTPUT_DIR ?? '/output';
for (const id of readdirSync(I).sort()) {
  const [out, ex] = run(readFileSync(join(I, id, 'program.bin')), readFileSync(join(I, id, 'input.bin')));
  mkdirSync(join(O, id), { recursive: true });
  writeFileSync(join(O, id, 'stdout.bin'), out);
  writeFileSync(join(O, id, 'exit.txt'), ex + '\n');
}
