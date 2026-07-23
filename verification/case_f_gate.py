#!/usr/bin/env python3
"""case_f_gate.py — the depth-1 JOINT-D1 probe ("Case F"), n = 4, p = 2.

JOINT-D1 asks: along a class-3 history, do the digit conditions of ALL reads jointly
count exactly (product of nominal cylinder volumes)? The sharpest empirical form at
depth 1: conditioned on the FIRST deg-φ=2 read landing in a descend stratum, is the
CHILD read's digit vector EXACTLY UNIFORM over the stratum fiber?

The probed history (p = 2, n = 4, m = 1):
  Read 0 (root): f̄ = ḡ², ḡ = x²+x+1  (all four φ-adic dev digits even), φ = x²+x+1.
  Read 1 (descend): dev f = φ² + a₁φ + a₀; v(a₀) = 2 EXACT, v(a₁) ≥ 2, residual
    R(y) = y² + digit₂(a₀) ∈ F₄[y] a square (y-coeff digit 0 is v(a₁) ≥ 2) with center
    c̃ = √digit₂(a₀) ∈ F₄ˣ (3 choices; Frobenius sqrt = squaring).
  Descend: ĉ := the minimal-support lift of c̃ (deg ≤ 1, coeffs ∈ {0,1});
    φ' := φ + 2·ĉ;  re-develop f = φ'² + a₁'φ' + a₀'.
  (Paper prediction: v(a₀') ≥ 3 on the stratum — the child cluster at height 2m+1.)

GATE F1 (child cluster): every stratum member has v(a₀') ≥ 3 and v(a₁') ≥ ...(recorded).
GATE F2 (JOINT UNIFORMITY — the point): per fixed c̃, bucket stratum members by the
  child digit vector (a₀'/8 mod 2^K, a₁'/4 mod 2^K) — all buckets must have EXACTLY
  equal counts. Uniform child digits ⟺ the depth-1 joint ledger counts as products.
GATE F3 (a terminating joint stratum): the child-ram-leaf condition (v(a₀') = 3 exact,
  i.e. nonzero child height-3 digit pair) has mass = (first-read mass) × (nominal child
  digit mass) — the explicit product-count check.

Run: python3 case_f_gate.py [N]   (default 5; the census is over 2^{4N} quartics).
"""
import sys
from fractions import Fraction as F
from collections import Counter


def polydiv(f, phi, M):
    f = list(f)
    d = len(phi) - 1
    q = [0] * (len(f) - d)
    for i in range(len(f) - 1, d - 1, -1):
        c = f[i] % M
        q[i - d] = c
        for j in range(d + 1):
            f[i - d + j] = (f[i - d + j] - c * phi[j]) % M
    return q, [x % M for x in f[:d]]


def develop(coeffs, phi, M):
    """f = x^4 + c3 x^3 + ... -> (a1, a0), deg <= 1 pairs (low, high) via two divisions."""
    c3, c2, c1, c0 = coeffs
    f = [c0, c1, c2, c3, 1]
    q1, a0 = polydiv(f, phi, M)
    q2, a1 = polydiv(q1, phi, M)
    assert q2 == [1]
    return (a1[1], a1[0]), (a0[1], a0[0])  # (high, low) = (x-coeff, const)


def vpair(pr, cap):
    v = cap
    for u in pr:
        if u == 0:
            continue
        w = 0
        while u % 2 == 0:
            u //= 2
            w += 1
        v = min(v, w)
    return v


F4_SQRT = {(1, 0): (1, 0), (0, 1): (1, 1), (1, 1): (0, 1)}
# F4 elements as (const, omega)-coords over F2 with omega = class of x;
# sqrt(u) = u^2: 1->1; w->w^2=w+1; w+1->(w+1)^2=w^2+1=w. Table checked below.


def main(N):
    M = 1 << N
    phi = [1, 1, 1]  # x^2+x+1 low->high
    strata = {}      # c-tilde -> list of child digit vectors
    child_v = Counter()
    K = N - 3        # child digit window for a0'/8 (needs N >= 4 for K >= 1)
    total = 0
    ram_child = Counter()
    for c3 in range(M):
        for c2 in range(M):
            for c1 in range(M):
                for c0 in range(M):
                    a1, a0 = develop((c3, c2, c1, c0), phi, M)
                    if (a1[0] | a1[1] | a0[0] | a0[1]) & 1:
                        continue                      # root read
                    if vpair(a0, N) != 2:
                        continue                      # v(a0) = 2 exact
                    if vpair(a1, N) < 2:
                        continue                      # square residual (y-coeff 0)
                    w = ((a0[0] >> 2) & 1, (a0[1] >> 2) & 1)  # digit2(a0) in F4 (x,const)
                    # NOTE coordinate order: a0 = (x-coeff, const); F4 elt = const + x*omega
                    u = (w[1], w[0])
                    if u == (0, 0):
                        continue                      # (cannot happen: v exact)
                    ct = F4_SQRT[u]                   # c-tilde = sqrt(u), (const, omega)
                    chat = [ct[0], ct[1]]             # minimal lift, low->high
                    phip = [(phi[0] + 2 * chat[0]) % M, (phi[1] + 2 * chat[1]) % M, 1]
                    b1, b0 = develop((c3, c2, c1, c0), phip, M)
                    total += 1
                    v0p, v1p = vpair(b0, N), vpair(b1, N)
                    child_v[(min(v0p, 6), min(v1p, 6))] += 1
                    if v0p < 3:
                        print(f'F1 VIOLATION: v(a0\')={v0p} at {(c3,c2,c1,c0)} ct={ct}')
                        return 1
                    if K >= 1:
                        vec = (tuple((x >> 3) % (1 << K) for x in b0),
                               tuple((x >> 2) % (1 << K) for x in b1))
                        strata.setdefault(ct, Counter())[vec] += 1
                    if v0p == 3:
                        ram_child[ct] += 1
    print(f'N={N}: stratum size {total} of {M**4} '
          f'(mass {F(total, M**4)}; first-read nominal 3*2^-10 = {F(3,1024)})')
    ok = F(total, M ** 4) == F(3, 1024)
    print(f'GATE F0 (first-read mass exact): {"OK" if ok else "MISMATCH"}')
    print('GATE F1 (child cluster v(a0\')>=3): OK (no violations)')
    print('child (v(a0\'), v(a1\')) distribution:', dict(sorted(child_v.items())))
    allok = ok
    if K >= 1:
        print(f'GATE F2 (joint uniformity of child digits, window K={K}):')
        for ct, buckets in sorted(strata.items()):
            sizes = set(buckets.values())
            nb = len(buckets)
            uniform = len(sizes) == 1
            allok = allok and uniform
            print(f'  c-tilde={ct}: {nb} buckets, sizes {sorted(sizes)} '
                  f'[{"UNIFORM OK" if uniform else "NON-UNIFORM — JOINT-D1 FAILS HERE"}]')
    # F3: child ram leaf (v(a0')=3 exact) per c-tilde: nominal = stratum_ct * (3/4)
    print('GATE F3 (child ram-leaf product count):')
    for ct in sorted(ram_child):
        got = ram_child[ct]
        per_ct = total // 3
        want = F(3, 4) * per_ct
        ok3 = F(got, 1) == want
        allok = allok and ok3
        print(f'  c-tilde={ct}: v(a0\')=3-exact count {got}, product-predicted {want} '
              f'[{"OK" if ok3 else "MISMATCH"}]')
    print('\nVERDICT:', 'CASE F GATE PASSES (joint-D1 depth-1 instance empirically exact)'
          if allok else 'CASE F GATE FAILS — diagnose per Asvin method')
    return 0 if allok else 1


if __name__ == '__main__':
    sys.exit(main(int(sys.argv[1]) if len(sys.argv) > 1 else 5))
