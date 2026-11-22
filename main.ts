// Tiny stack VM, faithful to the kit's ISA.md and reference vm.mjs.
import { mkdirSync as mk, readdirSync as ls, readFileSync as rd, writeFileSync as wr } from 'node:fs';
import { join } from 'node:path';
// Per opcode (in the order 00-07, 10-16, 17, 18-1e, 20-22, 30-34, 40-41,
// 50-53): immediate bytes, values popped, values pushed.
const IMM = '0140000000000000000000000022220000000';
const POP = '0001122322222221222122222201100121101';
const PSH = '0110223311111111111111111100000100010';
const IDX = new Int8Array(256).fill(-1);
let k = 0;
for (const [a, b] of [[0, 8], [16, 31], [32, 35], [48, 53], [64, 66], [80, 84]]) for (let o = a; o < b; o++) IDX[o] = k++;
function run(p, inp) {
  const D = new Int32Array(256), C = new Int32Array(64), M = new Int32Array(256);
  const out = new Uint8Array(65536), dg = new Uint8Array(11);
  let sp = 0, cp = 0, pc = 0, ip = 0, st = 0, ol = 0;
  const end = c => ({ o: out.slice(0, ol), c });
  for (;;) {
    if (st === 1e6) return end(10);
    if (pc < 0 || pc >= p.length) return end(9);
    const op = p[pc], i = IDX[op];
    if (i < 0) return end(5);
    const im = IMM.charCodeAt(i) - 48;
    if (pc + im >= p.length) return end(9);
    st++;
    const nx = pc + 1 + im, po = POP.charCodeAt(i) - 48, ps = PSH.charCodeAt(i) - 48;
    if (sp < po) return end(2);
    if (sp - po + ps > 256) return end(3);
    pc = nx;
    switch (op) {
      case 0x00: return end(0);
      case 0x01: D[sp++] = (p[nx - 1] << 24) >> 24; break;
      case 0x02: D[sp++] = p[nx - 4] | (p[nx - 3] << 8) | (p[nx - 2] << 16) | (p[nx - 1] << 24); break;
      case 0x03: sp--; break;
      case 0x04: D[sp] = D[sp - 1]; sp++; break;
      case 0x05: { const t = D[sp - 1]; D[sp - 1] = D[sp - 2]; D[sp - 2] = t; break; }
      case 0x06: D[sp] = D[sp - 2]; sp++; break;
      case 0x07: { const a = D[sp - 3]; D[sp - 3] = D[sp - 2]; D[sp - 2] = D[sp - 1]; D[sp - 1] = a; break; }
      case 0x17: D[sp - 1] = -D[sp - 1] | 0; break;
      case 0x1b: D[sp - 1] = ~D[sp - 1]; break;
      case 0x10: case 0x11: case 0x12: case 0x13: case 0x14: case 0x15: case 0x16:
      case 0x18: case 0x19: case 0x1a: case 0x1c: case 0x1d: case 0x1e:
      case 0x20: case 0x21: case 0x22: {
        const b = D[sp - 1], a = D[sp - 2];
        let r;
        if (op === 0x10) r = (a + b) | 0;
        else if (op === 0x11) r = (a - b) | 0;
        else if (op === 0x12) r = Math.imul(a, b);
        else if (op === 0x13) { if (!b) return end(4); r = a === -2147483648 && b === -1 ? a : (a / b) | 0; }
        else if (op === 0x14) { if (!b) return end(4); r = b === -1 ? 0 : (a % b) | 0; }
        else if (op === 0x15) { if (!b) return end(4); r = Math.floor((a >>> 0) / (b >>> 0)) | 0; }
        else if (op === 0x16) { if (!b) return end(4); r = ((a >>> 0) % (b >>> 0)) | 0; }
        else if (op === 0x18) r = a & b;
        else if (op === 0x19) r = a | b;
        else if (op === 0x1a) r = a ^ b;
        else if (op === 0x1c) r = a << (b & 31);
        else if (op === 0x1d) r = a >> (b & 31);
        else if (op === 0x1e) r = (a >>> (b & 31)) | 0;
        else if (op === 0x20) r = a === b ? 1 : 0;
        else if (op === 0x21) r = a < b ? 1 : 0;
        else r = (a >>> 0) < (b >>> 0) ? 1 : 0;
        D[sp - 2] = r; sp--;
        break;
      }
      case 0x30: case 0x31: case 0x32: {
        const rel = ((p[nx - 2] | (p[nx - 1] << 8)) << 16) >> 16;
        if (op !== 0x30) { const v = D[--sp]; if ((op === 0x31) !== (v === 0)) break; }
        pc = nx + rel;
        break;
      }
      case 0x33:
        if (cp === 64) return end(7);
        C[cp++] = nx;
        pc = p[nx - 2] | (p[nx - 1] << 8);
        break;
      case 0x34:
        if (cp === 0) return end(8);
        pc = C[--cp];
        break;
      case 0x40: {
        const a = D[sp - 1];
        if (a < 0 || a > 255) return end(6);
        D[sp - 1] = M[a];
        break;
      }
      case 0x41: {
        const a = D[sp - 1], v = D[sp - 2];
        if (a < 0 || a > 255) return end(6);
        sp -= 2;
        M[a] = v;
        break;
      }
      case 0x50: {
        const v = D[sp - 1], neg = v < 0;
        let u = neg ? -v : v, n = 0;
        do { dg[n++] = 48 + (u % 10); u = Math.floor(u / 10); } while (u);
        const len = n + (neg ? 1 : 0);
        if (ol + len > 65536) return end(11);
        sp--;
        if (neg) out[ol++] = 45;
        while (n) out[ol++] = dg[--n];
        break;
      }
      case 0x51:
        if (ol + 1 > 65536) return end(11);
        out[ol++] = D[--sp] & 255;
        break;
      case 0x52: D[sp++] = ip < inp.length ? inp[ip++] : -1; break;
      case 0x53: return end(D[--sp] & 255);
    }
  }
}
const I = process.env.MAKEFUN_INPUT_DIR ?? '/input', O = process.env.MAKEFUN_OUTPUT_DIR ?? '/output';
for (const id of ls(I).sort()) {
  const r = run(rd(join(I, id, 'program.bin')), rd(join(I, id, 'input.bin')));
  mk(join(O, id), { recursive: true });
  wr(join(O, id, 'stdout.bin'), r.o);
  wr(join(O, id, 'exit.txt'), r.c + '\n');
}
