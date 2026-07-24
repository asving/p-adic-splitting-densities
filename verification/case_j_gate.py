#!/usr/bin/env python3
"""case_j_gate.py — SEALED a > 0 gate for the rev-7 anchor-monomial transport (MOVES §B2⁵.2).

SEALED PREDICTIONS (2026-07-24, before first run). Config: n = 4, p = 5, root x⁴
cluster; the ANCHOR-1 side: slots 1..4 on the slope −1 line (side (1,3)–(4,0)), slot 0
strictly above. Stratum per (c̃, r), c̃ ∈ F₅ˣ, r ∉ {0, c̃}: v(a₃) = 1 exact with
digit₁(a₃) = −(2c̃+r); v(a₂) = 2 exact with digit₂(a₂) = c̃² + 2c̃r; v(a₁) = 3 exact
with digit₃(a₁) = −c̃²r; v(a₀) ≥ 5. [Anchored residual R_anch = (z−c̃)²(z−r) at
absolute anchor a = 1.] Move: x ↦ x + ĉ·5.

Rev-7 formula: P′ = (z+c̃)^a·R_anch(z+c̃) = (z+c̃)·z²·(z+c̃−r) ⟹ a′ = 2 and
R′_anch = (z+c̃)(z+c̃−r). SEALED:
 J1: v(a₁′) ≥ 4 (slot 1 leaves the line — RISES from exact 3);  v(a₀′) ≥ 5.
 J2: v(a₂′) = 2 exact with digit₂(a₂′) = c̃·(c̃−r)  (the new vertex, POINT MASS).
 J3: digit₁(a₃′) = 2c̃ − r (point mass; may be 0 mod 5, in which case v(a₃′) > 1 —
     both cases covered by the digit-value prediction).
 J4: child digit windows above the forced minima uniform on the (sub-box) stratum.
Sub-box: 2 free digits per coefficient above each pinned block, N = 7.
"""
import sys
from itertools import product
from collections import Counter
from math import comb

P, N = 5, 7
M = P ** N

def shift(coeffs, c):
    n = len(coeffs)
    poly = list(coeffs) + [1]
    out = [0] * (n + 1)
    for i in range(n + 1):
        for j in range(i + 1):
            out[j] = (out[j] + poly[i] * comb(i, j) * pow(c, i - j, M)) % M
    return out[:n]

def vp(x, cap):
    if x % M == 0: return cap
    v = 0
    while x % P == 0: x //= P; v += 1
    return v

def digit(x, h):
    return (x // P ** h) % P

def main():
    ok = True
    FREE = 2
    for ct in range(1, 5):
        for r in range(1, 5):
            if r == ct: continue
            d3 = (-(2*ct + r)) % P; d2 = (ct*ct + 2*ct*r) % P; d1 = (-ct*ct*r) % P
            buckets = Counter(); vert = Counter(); slot3 = Counter()
            mins = [99]*4
            n_mem = 0
            for f3, f2, f1, f0 in product(range(P**FREE), repeat=4):
                a3 = (d3 * P + f3 * P**2) % M
                a2 = (d2 * P**2 + f2 * P**3) % M
                a1 = (d1 * P**3 + f1 * P**4) % M
                a0 = (0 + f0 * P**5) % M
                sh = shift([a0, a1, a2, a3], 5 * ct)
                n_mem += 1
                vs = [vp(sh[i], N) for i in range(4)]
                mins = [min(a, b) for a, b in zip(mins, vs)]
                vert[digit(sh[2], 2)] += 1
                slot3[digit(sh[3], 1)] += 1
                buckets[(digit(sh[0],5), digit(sh[1],4), digit(sh[2],3))] += 1
            j1 = mins[1] >= 4 and mins[0] >= 5
            j2 = set(vert) == {(ct*(ct-r)) % P} and mins[2] == 2
            j3 = set(slot3) == {(2*ct - r) % P}
            sizes = set(buckets.values()); j4 = len(sizes) == 1
            ok = ok and j1 and j2 and j3 and j4
            print(f'c̃={ct} r={r}: mins {mins}; J1 {"OK" if j1 else "FAIL"}; '
                  f'J2 vertex {dict(vert) if len(vert)<3 else "..."} vs {(ct*(ct-r))%P} {"OK" if j2 else "FAIL"}; '
                  f'J3 slot3 {dict(slot3) if len(slot3)<3 else "..."} vs {(2*ct-r)%P} {"OK" if j3 else "FAIL"}; '
                  f'J4 {len(buckets)} buckets sizes {sorted(sizes)[:2]} {"OK" if j4 else "FAIL"}')
    print('\nVERDICT:', 'CASE J GATE PASSES (rev-7 anchor-monomial transport confirmed)'
          if ok else 'CASE J GATE FAILS')
    return 0 if ok else 1

if __name__ == '__main__':
    sys.exit(main())
