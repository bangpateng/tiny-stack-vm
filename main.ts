// Tiny stack VM for make.fun's tiny-stack-vm-01: a faithful interpreter of
// the kit's tiny stack ISA. Values are 32-bit wrapping ints, the data stack
// holds 256, the call stack 64 return addresses, memory is 256 words, and
// the ten traps each end the program with their own exit code. Steps cap at
// 1,000,000, output at 65,536 bytes. Answers every instance in one run.
import { mkdirSync, readdirSync, readFileSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';

// One base-32 digit per opcode byte 0x00..0x53: value = pops * 4 + pushes + 1
// (0 = no such opcode). Decoded below as pops = (v - 1) >> 2, pushes = (v - 1) & 3.
const T = '12257bcg00000000aaaaaaa6aaa6aaa0aaa0000000000000155110000000000069000000000000005525';

function run(p, q) {
  const S = new Int32Array(256); let s = 0;      // data stack
  const C = new Int32Array(64); let c = 0;       // call stack
  const M = new Int32Array(256);                 // memory, 256 words
  const o = new Uint8Array(65537); let n = 0;    // output bytes
  let pc = 0, steps = 0, ip = 0;
  const end = (e) => ({ o: o.slice(0, n), e });
  for (;;) {
    if (steps === 1000000) return end(10);       // step limit
    if (pc < 0 || pc >= p.length) return end(9); // pc outside the program
    const op = p[pc];
    const v = parseInt(T[op] ?? '0', 32);
    if (!v) return end(5);                       // unknown opcode
    const L = op === 1 ? 1 : op === 2 ? 4 : op > 47 && op < 52 ? 2 : 0;
    if (pc + L >= p.length) return end(9);       // immediate cut off
    steps++;
    const u = (v - 1) >> 2, w = (v - 1) & 3, nx = pc + 1 + L;
    if (s < u) return end(2);                    // stack underflow
    if (s - u + w > 256) return end(3);          // stack overflow
    pc = nx;
    switch (op) {
      case 0: return end(0);                     // HALT
      case 1: S[s++] = (p[nx - 1] << 24) >> 24; break; // PUSH8, sign-extended
      case 2: S[s++] = p[nx - 4] | (p[nx - 3] << 8) | (p[nx - 2] << 16) | (p[nx - 1] << 24); break; // PUSH32
      case 3: s--; break;                        // POP
      case 4: S[s] = S[s - 1]; s++; break;       // DUP
      case 5: { const a = S[s - 1]; S[s - 1] = S[s - 2]; S[s - 2] = a; break; } // SWAP
      case 6: S[s] = S[s - 2]; s++; break;       // OVER
      case 7: { const a = S[s - 3]; S[s - 3] = S[s - 2]; S[s - 2] = S[s - 1]; S[s - 1] = a; break; } // ROT
      case 0x17: S[s - 1] = -S[s - 1] | 0; break; // NEG, wraps
      case 0x1b: S[s - 1] = ~S[s - 1]; break;    // NOT
      case 0x30: case 0x31: case 0x32: {         // JMP / JZ / JNZ
        const r = ((p[nx - 2] | (p[nx - 1] << 8)) << 16) >> 16;
        let take = op === 0x30;
        if (op !== 0x30) { const z = S[--s]; take = op === 0x31 ? z === 0 : z !== 0; }
        if (take) pc = nx + r;
        break;
      }
      case 0x33:                                 // CALL
        if (c === 64) return end(7);
        C[c++] = nx; pc = p[nx - 2] | (p[nx - 1] << 8); break;
      case 0x34:                                 // RET
        if (!c) return end(8);
        pc = C[--c]; break;
      case 0x40: {                               // LOAD
        const a = S[s - 1];
        if (a < 0 || a > 255) return end(6);
        S[s - 1] = M[a]; break;
      }
      case 0x41: {                               // STORE
        const a = S[s - 1];
        if (a < 0 || a > 255) return end(6);
        M[a] = S[s - 2]; s -= 2; break;
      }
      case 0x50: {                               // PRINT, decimal ASCII
        const b = String(S[s - 1]);
        if (n + b.length > 65536) return end(11);
        s--;
        for (let i = 0; i < b.length; i++) o[n++] = b.charCodeAt(i);
        break;
      }
      case 0x51:                                 // PUTC, one byte
        if (n + 1 > 65536) return end(11);
        o[n++] = S[--s] & 255; break;
      case 0x52: S[s++] = ip < q.length ? q[ip++] : -1; break; // IN
      case 0x53: return end(S[--s] & 255);       // EXIT, low byte
      default: {                                 // binary ops
        const b = S[s - 1], a = S[s - 2]; let r = 0;
        if (op === 0x10) r = (a + b) | 0;                       // ADD
        else if (op === 0x11) r = (a - b) | 0;                  // SUB
        else if (op === 0x12) r = Math.imul(a, b);              // MUL, low 32 bits
        else if (op === 0x13) { if (!b) return end(4); r = (a / b) | 0; }  // DIV
        else if (op === 0x14) { if (!b) return end(4); r = (a % b) | 0; }  // MOD
        else if (op === 0x15) { if (!b) return end(4); r = Math.floor((a >>> 0) / (b >>> 0)) | 0; } // DIVU
        else if (op === 0x16) { if (!b) return end(4); r = ((a >>> 0) % (b >>> 0)) | 0; }           // MODU
        else if (op === 0x18) r = a & b;                        // AND
        else if (op === 0x19) r = a | b;                        // OR
        else if (op === 0x1a) r = a ^ b;                        // XOR
        else if (op === 0x1c) r = a << (b & 31);                // SHL
        else if (op === 0x1d) r = a >> (b & 31);                // SHR, arithmetic
        else if (op === 0x1e) r = (a >>> (b & 31)) | 0;         // SHRU, logical
        else if (op === 0x20) r = a === b ? 1 : 0;              // EQ
        else if (op === 0x21) r = a < b ? 1 : 0;                // LT, signed
        else r = (a >>> 0) < (b >>> 0) ? 1 : 0;                 // LTU, unsigned
        s -= 2; S[s++] = r;
      }
    }
  }
}

const I = process.env.MAKEFUN_INPUT_DIR ?? '/input';
const O = process.env.MAKEFUN_OUTPUT_DIR ?? '/output';
for (const id of readdirSync(I).sort()) {
  const r = run(readFileSync(join(I, id, 'program.bin')), readFileSync(join(I, id, 'input.bin')));
  mkdirSync(join(O, id), { recursive: true });
  writeFileSync(join(O, id, 'stdout.bin'), r.o);
  writeFileSync(join(O, id, 'exit.txt'), `${r.e}\n`);
}
