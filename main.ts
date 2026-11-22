// Tiny stack VM for make.fun's ISA v1: runs every /input/<id>/program.bin
// on its input.bin, writes /output/<id>/stdout.bin + exit.txt.
import { mkdirSync, readdirSync, readFileSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';

const IN_DIR = process.env.MAKEFUN_INPUT_DIR ?? '/input';
const OUT_DIR = process.env.MAKEFUN_OUTPUT_DIR ?? '/output';
const enc = new TextEncoder();

// Opcode table: [byte, immediate bytes, pops, pushes]. -1 immediate = no such opcode.
const IMM = new Int8Array(256).fill(-1);
const POP = new Uint8Array(256);
const PSH = new Uint8Array(256);
for (const [b, i, p, q] of [
  [0x00, 0, 0, 0], [0x01, 1, 0, 1], [0x02, 4, 0, 1], [0x03, 0, 1, 0],
  [0x04, 0, 1, 2], [0x05, 0, 2, 2], [0x06, 0, 2, 3], [0x07, 0, 3, 3],
  [0x10, 0, 2, 1], [0x11, 0, 2, 1], [0x12, 0, 2, 1], [0x13, 0, 2, 1],
  [0x14, 0, 2, 1], [0x15, 0, 2, 1], [0x16, 0, 2, 1], [0x17, 0, 1, 1],
  [0x18, 0, 2, 1], [0x19, 0, 2, 1], [0x1a, 0, 2, 1], [0x1b, 0, 1, 1],
  [0x1c, 0, 2, 1], [0x1d, 0, 2, 1], [0x1e, 0, 2, 1], [0x20, 0, 2, 1],
  [0x21, 0, 2, 1], [0x22, 0, 2, 1], [0x30, 2, 0, 0], [0x31, 2, 1, 0],
  [0x32, 2, 1, 0], [0x33, 2, 0, 0], [0x34, 0, 0, 0], [0x40, 0, 1, 1],
  [0x41, 0, 2, 0], [0x50, 0, 1, 0], [0x51, 0, 1, 0], [0x52, 0, 0, 1],
  [0x53, 0, 1, 0],
]) { IMM[b] = i; POP[b] = p; PSH[b] = q; }

function run(P, IN) {
  const n = P.length;
  const D = new Int32Array(256); // data stack, values are signed 32-bit
  let sp = 0;
  const C = new Int32Array(64); // call stack of return addresses
  let cp = 0;
  const M = new Int32Array(256); // memory, zeroed
  const out = new Uint8Array(65536);
  let ol = 0, ip = 0, pc = 0, steps = 0;
  const done = (exit) => [out.subarray(0, ol), exit];
  for (;;) {
    // Checks in ISA order: step limit, pc range, opcode, immediate fit.
    if (steps === 1000000) return done(10);
    if (pc < 0 || pc >= n) return done(9);
    const op = P[pc];
    const imm = IMM[op];
    if (imm < 0) return done(5);
    if (pc + imm >= n) return done(9);
    steps++;
    const next = pc + 1 + imm;
    if (sp < POP[op]) return done(2);
    if (sp - POP[op] + PSH[op] > 256) return done(3);
    pc = next;
    switch (op) {
      case 0x00: return done(0); // HALT
      case 0x01: D[sp++] = (P[next - 1] << 24) >> 24; break; // PUSH8 sign-extended
      case 0x02: // PUSH32 little-endian signed
        D[sp++] = P[next - 4] | (P[next - 3] << 8) | (P[next - 2] << 16) | (P[next - 1] << 24);
        break;
      case 0x03: sp--; break; // POP
      case 0x04: D[sp] = D[sp - 1]; sp++; break; // DUP
      case 0x05: { const t = D[sp - 1]; D[sp - 1] = D[sp - 2]; D[sp - 2] = t; break; } // SWAP
      case 0x06: D[sp] = D[sp - 2]; sp++; break; // OVER
      case 0x07: { const a = D[sp - 3]; D[sp - 3] = D[sp - 2]; D[sp - 2] = D[sp - 1]; D[sp - 1] = a; break; } // ROT
      case 0x17: D[sp - 1] = -D[sp - 1] | 0; break; // NEG (wraps at INT_MIN)
      case 0x1b: D[sp - 1] = ~D[sp - 1]; break; // NOT
      case 0x10: case 0x11: case 0x12: case 0x13: case 0x14: case 0x15: case 0x16:
      case 0x18: case 0x19: case 0x1a: case 0x1c: case 0x1d: case 0x1e:
      case 0x20: case 0x21: case 0x22: {
        const b = D[sp - 1], a = D[sp - 2];
        let r;
        if (op === 0x10) r = (a + b) | 0;
        else if (op === 0x11) r = (a - b) | 0;
        else if (op === 0x12) r = Math.imul(a, b); // exact low 32 bits
        else if (op === 0x13) {
          if (b === 0) return done(4);
          r = (a === -2147483648 && b === -1) ? a : (a / b) | 0; // trunc toward zero
        } else if (op === 0x14) {
          if (b === 0) return done(4);
          r = b === -1 ? 0 : (a % b) | 0; // sign of a
        } else if (op === 0x15) {
          if (b === 0) return done(4);
          r = Math.floor((a >>> 0) / (b >>> 0)) | 0;
        } else if (op === 0x16) {
          if (b === 0) return done(4);
          r = ((a >>> 0) % (b >>> 0)) | 0;
        } else if (op === 0x18) r = a & b;
        else if (op === 0x19) r = a | b;
        else if (op === 0x1a) r = a ^ b;
        else if (op === 0x1c) r = a << (b & 31);
        else if (op === 0x1d) r = a >> (b & 31);
        else if (op === 0x1e) r = (a >>> (b & 31)) | 0;
        else if (op === 0x20) r = a === b ? 1 : 0;
        else if (op === 0x21) r = a < b ? 1 : 0;
        else r = (a >>> 0) < (b >>> 0) ? 1 : 0; // LTU
        sp -= 2;
        D[sp++] = r;
        break;
      }
      case 0x30: case 0x31: case 0x32: { // JMP / JZ / JNZ, signed 16-bit offset
        const rel = ((P[next - 2] | (P[next - 1] << 8)) << 16) >> 16;
        let take = true;
        if (op !== 0x30) { const v = D[--sp]; take = op === 0x31 ? v === 0 : v !== 0; }
        if (take) pc = next + rel;
        break;
      }
      case 0x33: // CALL, unsigned 16-bit target
        if (cp === 64) return done(7);
        C[cp++] = next;
        pc = P[next - 2] | (P[next - 1] << 8);
        break;
      case 0x34: // RET
        if (cp === 0) return done(8);
        pc = C[--cp];
        break;
      case 0x40: { // LOAD
        const addr = D[sp - 1];
        if (addr < 0 || addr > 255) return done(6);
        D[sp - 1] = M[addr];
        break;
      }
      case 0x41: { // STORE: ( v addr -- ), top of stack is the address
        const addr = D[sp - 1], v = D[sp - 2];
        if (addr < 0 || addr > 255) return done(6);
        sp -= 2;
        M[addr] = v;
        break;
      }
      case 0x50: { // PRINT decimal, no newline; trap 11 writes none of it
        const bytes = enc.encode(String(D[sp - 1]));
        if (ol + bytes.length > 65536) return done(11);
        sp--;
        out.set(bytes, ol);
        ol += bytes.length;
        break;
      }
      case 0x51: // PUTC: low byte
        if (ol + 1 > 65536) return done(11);
        out[ol++] = D[--sp] & 255;
        break;
      case 0x52: D[sp++] = ip < IN.length ? IN[ip++] : -1; break; // IN, -1 at EOF
      case 0x53: return done(D[--sp] & 255); // EXIT, low byte
    }
  }
}

for (const id of readdirSync(IN_DIR).sort()) {
  const dir = join(IN_DIR, id);
  let prog, inp;
  try { prog = readFileSync(join(dir, 'program.bin')); } catch { prog = new Uint8Array(0); }
  try { inp = readFileSync(join(dir, 'input.bin')); } catch { inp = new Uint8Array(0); }
  const [stdout, exit] = run(prog, inp);
  mkdirSync(join(OUT_DIR, id), { recursive: true });
  writeFileSync(join(OUT_DIR, id, 'stdout.bin'), stdout);
  writeFileSync(join(OUT_DIR, id, 'exit.txt'), exit + '\n');
}
