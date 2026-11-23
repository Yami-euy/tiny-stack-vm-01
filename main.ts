import { mkdirSync, readdirSync, readFileSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';

// Tiny stack VM for make.fun's ISA v1. One program.bin on its input.bin,
// answering with exactly the bytes it writes and the exit code it ends with.
// Written from ISA.md; every trap, limit and wrapping rule follows it.
// Pops (PU8) and pushes (PW8) of opcodes 0..7, as a lookup table built once.
// Same values as the old string-index decode, except b = 7 (ROT3): the old
// string '0110233' has only 7 chars, so w was NaN and the overflow check
// s - u + w > 256 was always false; the table gives w = 0, and s - 3 + 0 > 256
// is likewise always false (s <= 256), so no trap behaviour changes.
const PU8 = new Int32Array([0, 0, 0, 1, 1, 2, 2, 3]);
const PW8 = new Int32Array([0, 1, 1, 0, 2, 3, 3, 0]);

function run(p, q) {
  const S = new Int32Array(256); // data stack
  const C = new Int32Array(64); // call stack
  const M = new Int32Array(256); // memory
  const O = new Uint8Array(65536); // output
  let s = 0, c = 0, o = 0, i = 0, x = 0, t = 0;
  const n = p.length;
  const done = (e) => ({ o: O.slice(0, o), e });
  for (;;) {
    if (t === 1000000) return done(10);
    if (x < 0 || x >= n) return done(9);
    const b = p[x];
    // Per opcode: immediate length (m), pops (u), pushes (w).
    let m = 0, u = 0, w = 0, ok = false;
    if (b < 8) { ok = true; m = b === 1 ? 1 : b === 2 ? 4 : 0; u = PU8[b]; w = PW8[b]; }
    else if (b >= 16 && b <= 34) { ok = true; u = b === 23 || b === 27 ? 1 : 2; w = 1; }
    else if (b >= 48 && b <= 52) { ok = true; m = b === 52 ? 0 : 2; u = b === 49 || b === 50 ? 1 : 0; }
    else if (b === 64) { ok = true; u = 1; w = 1; }
    else if (b === 65) { ok = true; u = 2; }
    else if (b >= 80 && b <= 83) { ok = true; u = b === 82 ? 0 : 1; w = b === 82 ? 1 : 0; }
    if (!ok) return done(5);
    if (x + m >= n) return done(9);
    t++;
    const y = x + 1 + m;
    if (s < u) return done(2);
    if (s - u + w > 256) return done(3);
    x = y;
    switch (b) {
      case 0: return done(0);
      case 1: S[s++] = (p[y - 1] << 24) >> 24; break;
      case 2: S[s++] = p[y - 4] | p[y - 3] << 8 | p[y - 2] << 16 | p[y - 1] << 24; break;
      case 3: s--; break;
      case 4: S[s] = S[s - 1]; s++; break;
      case 5: { const a = S[s - 1]; S[s - 1] = S[s - 2]; S[s - 2] = a; break; }
      case 6: S[s] = S[s - 2]; s++; break;
      case 7: { const a = S[s - 3]; S[s - 3] = S[s - 2]; S[s - 2] = S[s - 1]; S[s - 1] = a; break; }
      case 23: S[s - 1] = -S[s - 1] | 0; break;
      case 27: S[s - 1] = ~S[s - 1]; break;
      case 48: case 49: case 50: {
        const r = (p[y - 2] | p[y - 1] << 8) << 16 >> 16;
        if (b === 48) { x = y + r; break; }
        const v = S[--s];
        if ((b === 49) === (v === 0)) x = y + r;
        break;
      }
      case 51: if (c === 64) return done(7); C[c++] = y; x = p[y - 2] | p[y - 1] << 8; break;
      case 52: if (c === 0) return done(8); x = C[--c]; break;
      case 64: { const a = S[s - 1]; if (a < 0 || a > 255) return done(6); S[s - 1] = M[a]; break; }
      case 65: { const a = S[s - 1]; if (a < 0 || a > 255) return done(6); M[a] = S[s - 2]; s -= 2; break; }
      case 80: { const d = String(S[s - 1]); if (o + d.length > 65536) return done(11); s--; for (let k = 0; k < d.length; k++) O[o++] = d.charCodeAt(k); break; }
      case 81: if (o + 1 > 65536) return done(11); O[o++] = S[--s] & 255; break;
      case 82: S[s++] = i < q.length ? q[i++] : -1; break;
      case 83: return done(S[--s] & 255);
      default: {
        const v = S[s - 1], a = S[s - 2];
        let r;
        if (b === 16) r = a + v | 0;
        else if (b === 17) r = a - v | 0;
        else if (b === 18) r = Math.imul(a, v);
        else if (b === 19) { if (v === 0) return done(4); r = a === -2147483648 && v === -1 ? a : a / v | 0; }
        else if (b === 20) { if (v === 0) return done(4); r = v === -1 ? 0 : a % v | 0; }
        else if (b === 21) { if (v === 0) return done(4); r = Math.floor((a >>> 0) / (v >>> 0)) | 0; }
        else if (b === 22) { if (v === 0) return done(4); r = (a >>> 0) % (v >>> 0) | 0; }
        else if (b === 24) r = a & v;
        else if (b === 25) r = a | v;
        else if (b === 26) r = a ^ v;
        else if (b === 28) r = a << (v & 31);
        else if (b === 29) r = a >> (v & 31);
        else if (b === 30) r = a >>> (v & 31) | 0;
        else if (b === 32) r = a === v ? 1 : 0;
        else if (b === 33) r = a < v ? 1 : 0;
        else r = (a >>> 0) < (v >>> 0) ? 1 : 0;
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
  writeFileSync(join(O, id, 'exit.txt'), r.e + '\n');
}
