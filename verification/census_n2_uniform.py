#!/usr/bin/env python3
"""census_n2_uniform.py — external cross-check for Wave 6q (n=2 ALL-PRIMES uniformity).

Two independent checks against the W6q blueprint ledger
(lean/notes/WILD_WAVE6Q_BLUEPRINT_2026-07-22.md §1.1-§1.2):

1. TYPE census (disc square-class oracle): per-type full-box masses over Z_p mod p^N
   must approach R_ram = 1/(q+1), R_inert = R_split = q/(2(q+1)) from below, with the
   undecided remainder inside the envelope.
2. FAMILY census (digit-definition strata): per-(translate c, family, height) counts at
   depth 0 must equal the ledger's exact per-height masses:
     ram H:      (q-1) * q^{-(3H+1)/2 - 1}      (full-box per point: q^{-2} * (1-1/q) q^{-3(H-1)/2})
     inert m:    [q(q-1)/2] * q^{-3m - 2}
     splitU m:   [(q-1)(q-2)/2] * q^{-3m - 2}   (EMPTY at q = 2)
     twoSided k: (q-1) * q^{-(3k-1) - 3}        (full-box per point: q^{-2} * (1-1/q) q^{-(3k-1)})
     descend m:  (q-1) * q^{-3m - 2}
   (Each family's conditions are evaluated on the c-translated pair, mirroring the Lean
   fiber predicates TransChainP / TransChainU / LeafPair / LeafPairU / StratumPair.)

Run: python3 census_n2_uniform.py [p] [N]   (defaults p=3 N=6; p=2 N=8 also standard)
"""
import sys
from fractions import Fraction as F


def v_p(x, p, cap):
    if x == 0:
        return cap
    v = 0
    while x % p == 0:
        x //= p
        v += 1
    return v


def qp_type(a1, a0, p, N):
    """split/inert/ram/undecided via the disc square class (odd p) or mod-8 class (p=2)."""
    M = p ** N
    d = (a1 * a1 - 4 * a0) % M
    if d == 0:
        return 'und'
    v = v_p(d, p, N)
    if p == 2:
        if v >= N - 3:
            return 'und'
        u = (d >> v) % 8
        if v % 2 == 1:
            return 'ram'
        return 'split' if u == 1 else ('inert' if u == 5 else 'ram')
    if v >= N - 1:
        return 'und'
    u = (d // p ** v) % p
    if v % 2 == 1:
        return 'ram'
    return 'split' if pow(u, (p - 1) // 2, p) == 1 else 'inert'


def residual_class(w0, w1, p):
    """classify z^2 + w1 z + w0 over F_p: 'noroot' / 'rooted' (two distinct) / 'square'."""
    roots = [r for r in range(p) if (r * r + w1 * r + w0) % p == 0]
    if not roots:
        return 'noroot'
    if len(roots) == 2:
        return 'rooted'
    return 'square'


def family_census(p, N):
    """Depth-0 per-family counts at each translate; compare to the ledger."""
    M = p ** N
    fams = {}

    def bump(key):
        fams[key] = fams.get(key, 0) + 1

    for a1 in range(M):
        for a0 in range(M):
            for c in range(p):
                # translate f(x+c): (b0, b1) = (a0 + c a1 + c^2, a1 + 2c) mod p^N
                b0 = (a0 + c * a1 + c * c) % M
                b1 = (a1 + 2 * c) % M
                v0 = v_p(b0, p, N)
                v1 = v_p(b1, p, N)
                if v0 < 1 or v1 < 1:
                    continue  # not in the c-cluster
                # two-sided: v(b1) = k exact, v(b0) >= 2k+1
                if v1 < N and v0 >= 2 * v1 + 1 and 2 * v1 + 1 <= N:
                    bump((c, 'twoSided', v1))
                    continue
                if v0 >= N:
                    continue  # tail/stall at this level
                if v0 % 2 == 1:
                    H = v0
                    if v1 >= (H + 1) // 2:
                        bump((c, 'ram', H))
                    continue
                m = v0 // 2
                if v1 < m:
                    continue  # belongs to a two-sided regime already caught or deeper
                w0 = (b0 // p ** v0) % p
                w1d = (b1 // p ** m) % p if v1 == m else 0
                cls = residual_class(w0, w1d, p)
                if cls == 'noroot':
                    bump((c, 'inert', m))
                elif cls == 'rooted':
                    bump((c, 'splitU', m))
                else:
                    bump((c, 'descend', m))

    box = F(1, M * M)
    ledger = {}
    for H in range(1, N, 2):
        ledger['ram', H] = F(p - 1, 1) * F(1, p ** 2) * F(1, p ** ((3 * (H - 1)) // 2 + 1))
    for m in range(1, (N - 1) // 2 + 1):
        ledger['inert', m] = F(p * (p - 1), 2) * F(1, p ** (3 * m + 2))
        ledger['splitU', m] = F((p - 1) * (p - 2), 2) * F(1, p ** (3 * m + 2))
        ledger['descend', m] = F(p - 1, 1) * F(1, p ** (3 * m + 2))
    for k in range(1, (N - 1) // 2 + 1):
        ledger['twoSided', k] = F(p - 1, 1) * F(1, p ** (3 * k + 2))

    print(f'\nper-family depth-0 census (p={p}, N={N}); ledger vs counted, per translate:')
    ok = True
    for (fam, h), target in sorted(ledger.items()):
        for c in range(p):
            got = F(fams.get((c, fam, h), 0), 1) * box
            mark = 'OK' if got == target else 'MISMATCH'
            if got != target:
                ok = False
            if c == 0 or got != target:
                print(f'  c={c} {fam:9s} h={h}:  counted {got}  target {target}  [{mark}]')
    return ok


def type_census(p, N):
    M = p ** N
    cnt = {'ram': 0, 'inert': 0, 'split': 0, 'und': 0}
    for a1 in range(M):
        for a0 in range(M):
            cnt[qp_type(a1, a0, p, N)] += 1
    tot = M * M
    targets = {'ram': F(1, p + 1), 'inert': F(p, 2 * (p + 1)), 'split': F(p, 2 * (p + 1))}
    print(f'type census (p={p}, N={N}):')
    ok = True
    for k in ('ram', 'inert', 'split'):
        got = F(cnt[k], tot)
        lo_ok = got <= targets[k] and targets[k] <= got + F(cnt['und'], tot)
        ok = ok and lo_ok
        print(f'  {k:6s} {got}  target {targets[k]}  '
              f'[{"OK: inside envelope" if lo_ok else "FAIL"}]')
    print(f'  undecided {F(cnt["und"], tot)}')
    return ok


if __name__ == '__main__':
    p = int(sys.argv[1]) if len(sys.argv) > 1 else 3
    N = int(sys.argv[2]) if len(sys.argv) > 2 else 6
    ok1 = type_census(p, N)
    ok2 = family_census(p, min(N, 5))
    print('\nVERDICT:', 'ALL OK' if (ok1 and ok2) else 'MISMATCHES FOUND')
