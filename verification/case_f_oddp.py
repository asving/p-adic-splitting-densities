#!/usr/bin/env python3
"""case_f_oddp.py — Case F at odd p (p = 3), corrected sign φ' = φ − p^m·ĉ.

Tests Conjecture J1-step (blueprint W8 §5) at odd p: the class-3 descend
re-development Θ_ĉ maps the parent descend stratum bijectively onto the child
cluster box, with EXACTLY uniform child digits.

Design note: D1-marginal (the first development's exactness) is already proved
(paper + Lean, W8a), so the parent stratum is enumerated directly in development
coordinates (a₁, a₀) — the map under test is Θ: f = φ² + a₁φ + a₀ re-developed
at φ' = φ − p^m·ĉ. Stratum at slope m, center c̃ ∈ F_Q^× (Q = p²):
  root read: digit₀(a₁) = digit₀(a₀) = 0;
  v(a₀) ≥ 2m with digit_{2m}(a₀) = c̃²;  v(a₁) ≥ m with digit_m(a₁) = −2c̃.
Child box prediction: v(a₀') ≥ 2m+1, v(a₁') ≥ m+1, child digits uniform.

φ = x² + 1 (irreducible mod 3); F₉ = F₃[x]/(x²+1); digits of a deg-≤1 poly at
height h = the coefficient pair of p^h in its (p-adic, coefficientwise) expansion.
Run: python3 case_f_oddp.py [N] [m]   (defaults N=6, m=1).
"""
import sys
from itertools import product
from collections import Counter

P = 3
S, T = 0, 1          # phi = x^2 + 0x + 1


def f9_mul(a, b):
    # elements (const, xcoef) mod 3, x^2 = -1
    return ((a[0] * b[0] - a[1] * b[1]) % P, (a[0] * b[1] + a[1] * b[0]) % P)


def f9_neg2(c):
    return ((-2 * c[0]) % P, (-2 * c[1]) % P)


def polydiv(f, phi, M):
    f = list(f)
    d = len(phi) - 1
    for i in range(len(f) - 1, d - 1, -1):
        c = f[i] % M
        for j in range(d + 1):
            f[i - d + j] = (f[i - d + j] - c * phi[j]) % M
    return [x % M for x in f[:d]]


def develop2(coeffs, phi, M):
    c3, c2, c1, c0 = coeffs
    f = [c0, c1, c2, c3, 1]
    fl = list(f)
    d = 2
    q = [0] * 3
    for i in range(4, 1, -1):
        c = fl[i] % M
        q[i - d] = c
        for j in range(3):
            fl[i - d + j] = (fl[i - d + j] - c * phi[j]) % M
    a0 = (fl[1] % M, fl[0] % M)          # (xcoef, const)
    a1 = (q[2] and 0, 0)                  # placeholder; recompute below properly
    # second division of q (monic quadratic) by phi:
    r1 = (q[1] - q[2] * phi[1]) % M
    r0 = (q[0] - q[2] * phi[0]) % M
    a1 = (r1 % M, r0 % M)                 # (xcoef, const) — q - phi since q2 = 1
    return a1, a0


def vpair(pr, cap):
    v = cap
    for u in pr:
        if u == 0:
            continue
        w = 0
        while u % P == 0:
            u //= P
            w += 1
        v = min(v, w)
    return v


def digit(pr, h):
    return ((pr[0] // P ** h) % P, (pr[1] // P ** h) % P)


def main(N, m):
    M = P ** N
    ok_all = True
    # centers: F9^x, coordinates (const, xcoef)
    centers = [c for c in product(range(P), repeat=2) if c != (0, 0)]
    for ct in centers:
        ct_sq = f9_mul(ct, ct)
        neg2ct = f9_neg2(ct)
        chat = [ct[0], ct[1]]                       # minimal lift, low->high
        phip = [(1 - P ** m * chat[0]) % M, (0 - P ** m * chat[1]) % M, 1]
        # enumerate the stratum in dev coordinates:
        # a1: digits 0..m-1 = 0 (root read + v>=m), digit m = -2c (as (x,const) pair
        #     careful: our digit() returns (xcoef,const); neg2ct is (const,xcoef))
        # free digits of a1 at heights m+1..N-1; a0: digits 0..2m-1 = 0, digit 2m = c^2,
        # free heights 2m+1..N-1.
        free1 = N - (m + 1)
        free0 = N - (2 * m + 1)
        buckets = Counter()
        childK1 = 1   # child digit windows (1 height each is enough for the test)
        childK0 = 1
        n_members = 0
        f1_viol = 0
        for e1 in product(range(P), repeat=2 * free1):
            a1x = sum(e1[2 * i] * P ** (m + 1 + i) for i in range(free1)) + neg2ct[1] * P ** m
            a1c = sum(e1[2 * i + 1] * P ** (m + 1 + i) for i in range(free1)) + neg2ct[0] * P ** m
            for e0 in product(range(P), repeat=2 * free0):
                a0x = sum(e0[2 * i] * P ** (2 * m + 1 + i) for i in range(free0)) + ct_sq[1] * P ** (2 * m)
                a0c = sum(e0[2 * i + 1] * P ** (2 * m + 1 + i) for i in range(free0)) + ct_sq[0] * P ** (2 * m)
                # reconstruct f = phi^2 + a1*phi + a0  (phi = x^2+1)
                # phi^2 = x^4 + 2x^2 + 1; a1*phi = a1x x^3 + a1c x^2 + a1x x + a1c
                c3 = a1x % M
                c2 = (2 + a1c) % M
                c1 = (a1x + a0x) % M
                c0 = (1 + a1c + a0c) % M
                b1, b0 = develop2((c3, c2, c1, c0), phip, M)
                n_members += 1
                if vpair(b0, N) < 2 * m + 1 or vpair(b1, N) < m + 1:
                    f1_viol += 1
                    if f1_viol < 4:
                        print(f'  F1 VIOLATION ct={ct}: v={vpair(b0,N)},{vpair(b1,N)} '
                              f'at f=({c3},{c2},{c1},{c0})')
                    continue
                vec = (digit(b0, 2 * m + 1), digit(b1, m + 1))
                buckets[vec] += 1
        sizes = set(buckets.values())
        nb = len(buckets)
        expect_buckets = P ** (2 * childK0) * P ** (2 * childK1)
        uniform = len(sizes) == 1 and nb == expect_buckets and f1_viol == 0
        ok_all = ok_all and uniform
        print(f'c̃={ct}: members {n_members}, F1 violations {f1_viol}, '
              f'{nb}/{expect_buckets} child-digit buckets, sizes {sorted(sizes)} '
              f'[{"UNIFORM OK" if uniform else "FAIL"}]')
    print('\nVERDICT:', 'CASE F ODD-p PASSES (J1-step exact at p=3, sign −)'
          if ok_all else 'CASE F ODD-p FAILS')
    return 0 if ok_all else 1


if __name__ == '__main__':
    N = int(sys.argv[1]) if len(sys.argv) > 1 else 6
    m = int(sys.argv[2]) if len(sys.argv) > 2 else 1
    sys.exit(main(N, m))
