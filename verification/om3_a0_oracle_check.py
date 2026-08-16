#!/usr/bin/env python3
"""OM-3 certification leg 6 (HYP.25, the (A0) lift well-posedness): order-1 window-decided cubic
reads vs an INDEPENDENT (e, f) oracle, on the canonical lift AND a decorrelated lift.

(A0) (W-12.D, ledger HYP.25): "every window-decided core-family member has all disc ≠ 0 O-lifts
of the read's type."  This leg checks the n = 3 order-1 instance decisively at mixed
characteristic: for EVERY class mod p^N whose order-1 read decides (level-0 pattern + shifted
branch polygon + separable residuals, all window-visible), the splitting type of the canonical
lift AND of a pseudo-random decorrelated lift (digits added at levels ≥ N), both with disc ≠ 0,
equals the read's type.

READER (this script; the W-12.A order-1 rules, independent implementation):
  · f̄ squarefree over F_p  ⟹  decided, type = {(1, d_i)} over the irreducible factors;
  · else (degree 3: exactly one repeated root c): shift x ↦ x + c and read the Newton polygon of
    the shifted cubic with ALL its sides (the simple co-branch appears as the slope-0 side); a
    side of length L and slope num/den (lowest terms) carries a residual of degree L/den read at
    the den-strided line digits; if EVERY residual is separable and the polygon is window-solid
    (v(shifted a₀) < N), the member is DECIDED with one (e, f) = (den, m) factor per irreducible
    residual factor of degree m; otherwise UNDECIDED at order 1 (out of (A0)'s scope — skipped).

ORACLE (independent leg): PARI/GP — factor the lift over ℚ, then `nfinit` + `idealprimedec` at p
per irreducible factor; the multiset of (e, f) over the primes above p IS the splitting type.
No polygon, no residual read — a fully decorrelated computation (the verification/README oracle
pattern, batched through one `gp -q` subprocess per cell).

Cells: (p, N) ∈ {(2,2), (2,3), (3,2), (3,3)} — every class enumerated, every decided class
oracle-checked twice.  Equal characteristic is NOT covered by this leg (PARI has no F_q((t))
factorization); the equal-char count structure is covered by legs 3–5.  Exit 0 iff all green.
"""

import subprocess
import sys
import re
from itertools import product

GP = "/data/users/asvin/.local/bin/gp"


# ------------------------------- the order-1 reader --------------------------------------------


def val(a, p, N):
    if a % p ** N == 0:
        return N
    v = 0
    while a % p == 0:
        a //= p
        v += 1
    return v


def digit(a, p, i):
    return (a // p ** i) % p


def _syndiv(coeffs_low, r, p):
    """Divide the poly (low→high coeffs) by (x − r) over F_p; returns (quot_low, rem)."""
    hi = list(reversed(coeffs_low))
    q = []
    acc = 0
    for c in hi:
        acc = (acc * r + c) % p
        q.append(acc)
    rem = q[-1]
    quot = list(reversed(q[:-1]))
    return quot, rem


def fp_factor_pattern_cubic(a2, a1, a0, p):
    """Roots-with-multiplicity of x³+a2x²+a1x+a0 over F_p."""
    roots = {}
    for r in range(p):
        m = 0
        coeffs = [a0 % p, a1 % p, a2 % p, 1]
        while len(coeffs) > 1:
            quot, rem = _syndiv(coeffs, r, p)
            if rem != 0:
                break
            coeffs = quot
            m += 1
        if m:
            roots[r] = m
    tot = sum(roots.values())
    return roots, tot


def lower_hull(points):
    hull = []
    for pt in points:
        while len(hull) >= 2:
            (x1, y1), (x2, y2) = hull[-2], hull[-1]
            if (y2 - y1) * (pt[0] - x1) >= (pt[1] - y1) * (x2 - x1):
                hull.pop()
            else:
                break
        hull.append(pt)
    return hull


def poly_shift(coeffs, c, mod):
    """f(x + c) mod `mod` for monic cubic coeffs (a0, a1, a2)."""
    a0, a1, a2 = coeffs
    b0 = (a0 + a1 * c + a2 * c * c + c ** 3) % mod
    b1 = (a1 + 2 * a2 * c + 3 * c * c) % mod
    b2 = (a2 + 3 * c) % mod
    return b0, b1, b2


def fq_pattern_of_residual(rc, p):
    """Factorization pattern of the monic normalization of residual coeffs rc (low→high ints
    mod p): returns sorted list of (deg, mult) or None if not squarefree-separable readable."""
    # monic normalize
    inv = pow(rc[-1], -1, p)
    mon = [(c * inv) % p for c in rc]
    # factor off roots (with multiplicity, recorded as repeated parts)
    parts = []
    coeffs = mon[:]
    for r in range(p):
        while len(coeffs) > 1:
            quot, rem = _syndiv(coeffs, r, p)
            if rem != 0:
                break
            coeffs = quot
            parts.append((1, r))
    rem_deg = len(coeffs) - 1
    if rem_deg > 0:
        # remaining factor has no roots: deg ≤ 3 without roots is irreducible
        parts.append((rem_deg, None))
    return parts


def order1_read(a0, a1, a2, p, N):
    """Returns ('dec', sorted type multiset [(e,f),...]) or ('und', None)."""
    mod = p ** N
    roots, tot = fp_factor_pattern_cubic(a2 % p, a1 % p, a0 % p, p)
    if all(m == 1 for m in roots.values()):
        # squarefree reduction (roots simple; nonlinear part squarefree? deg-3: remaining part
        # of degree 2 with no roots is irreducible; degree 3 no roots irreducible)
        rem = 3 - tot
        typ = [(1, 1)] * tot
        if rem > 0:
            typ.append((1, rem))
        return ('dec', tuple(sorted(typ)))
    # exactly one repeated root c
    c = next(r for r, m in roots.items() if m >= 2)
    b0, b1, b2 = poly_shift((a0, a1, a2), c, mod)
    vs = [val(b0, p, N), val(b1, p, N), val(b2, p, N)]
    if vs[0] >= N:
        return ('und', None)
    pts = [(i, v) for i, v in enumerate(vs) if v < N] + [(3, 0)]
    verts = lower_hull(pts)
    typ = []
    for (x1, y1), (x2, y2) in zip(verts, verts[1:]):
        L = x2 - x1
        drop = y1 - y2
        if drop == 0:
            num, den = 0, 1
        else:
            from math import gcd
            g = gcd(L, drop)
            num, den = drop // g, L // g
        rdeg = L // den
        rc = []
        for j in range(rdeg + 1):
            i = x1 + j * den
            h = y1 - j * num
            rc.append(1 if i == 3 else digit([b0, b1, b2][i], p, h))
        parts = fq_pattern_of_residual(rc, p)
        # separability: all parts distinct — for our reads: multiplicity shows up as repeated
        # linear parts with the same root, or (deg≥2 with square factor — impossible at deg ≤ 3
        # without roots).  Detect repeats:
        seen = set()
        sep = True
        for part in parts:
            if part in seen:
                sep = False
            seen.add(part)
        # a repeated root appears as the SAME (1, r) twice; irreducible tail unique
        if not sep:
            return ('und', None)
        for (m, _tag) in parts:
            typ.append((den, m))
    return ('dec', tuple(sorted(typ)))


# ------------------------------- the oracle -----------------------------------------------------


def disc_cubic(a, b, c):
    return 18 * a * b * c - 4 * a ** 3 * c + a ** 2 * b ** 2 - 4 * b ** 3 - 27 * c ** 2


def run_cell(p, N):
    mod = p ** N
    queries = []   # (qid, a2, a1, a0 as integer coeffs of the lift)
    expected = {}  # qid -> type
    skipped_und = 0
    rng_state = 12345
    def prand():
        nonlocal rng_state
        rng_state = (1103515245 * rng_state + 12345) % (1 << 31)
        return rng_state % p
    qid = 0
    for a2 in range(0, mod):
        for a1 in range(0, mod):
            for a0 in range(0, mod):
                st, typ = order1_read(a0, a1, a2, p, N)
                if st == 'und':
                    skipped_und += 1
                    continue
                # canonical lift + decorrelated lift, both with disc ≠ 0
                for variant in range(2):
                    if variant == 0:
                        A2, A1, A0 = a2, a1, a0
                    else:
                        A2 = a2 + mod * (1 + prand())
                        A1 = a1 + mod * prand()
                        A0 = a0 + mod * (1 + prand() * p)
                    tries = 0
                    while disc_cubic(A2, A1, A0) == 0 and tries < 5:
                        A0 += mod * (p ** tries)
                        tries += 1
                    assert disc_cubic(A2, A1, A0) != 0
                    queries.append((qid, A2, A1, A0))
                    expected[qid] = typ
                    qid += 1
    # one gp batch
    lines = [
        "typ(f, p) = {my(fa = factor(f), res = List());"
        "for (i = 1, matsize(fa)[1], my(g = fa[i,1]);"
        "if (poldegree(g) >= 1, my(nf = nfinit([g, [p]]), dec = idealprimedec(nf, p));"
        "for (j = 1, #dec, listput(res, [dec[j].e, dec[j].f]))));"
        "vecsort(Vec(res))}"
    ]
    for (i, A2, A1, A0) in queries:
        lines.append(f"print({i}, \" \", typ(x^3 + ({A2})*x^2 + ({A1})*x + ({A0}), {p}))")
    lines.append("quit")
    gp_in = ";\n".join(lines[:1]) + "\n" + "\n".join(lines[1:]) + "\n"
    out = subprocess.run([GP, "-q", "-s", "64000000"], input=gp_in, capture_output=True,
                         text=True, timeout=3600)
    bad = 0
    seenq = 0
    for line in out.stdout.splitlines():
        m = re.match(r"^(\d+) \[(.*)\]$", line.strip())
        if not m:
            continue
        seenq += 1
        i = int(m.group(1))
        pairs = re.findall(r"\[(\d+),\s*(\d+)\]", m.group(2))
        got = tuple(sorted((int(e), int(f)) for (e, f) in pairs))
        if got != expected[i]:
            bad += 1
            if bad <= 5:
                print(f"    MISMATCH qid={i} read={expected[i]} oracle={got} "
                      f"poly={queries[i][1:]}")
    ok = bad == 0 and seenq == len(queries) and len(queries) > 0
    ndec = len(queries) // 2
    print(f"  [{'OK ' if ok else 'FAIL'}] p={p} N={N}: classes={mod ** 3} decided={ndec} "
          f"undecided={skipped_und} oracle-calls={len(queries)} answered={seenq} mismatches={bad}")
    return ok


def main():
    okall = True
    for (p, N) in [(2, 2), (2, 3), (3, 2), (3, 3)]:
        okall &= run_cell(p, N)
    print("\nRESULT:", "ALL CHECKS PASS" if okall else "FAILURES PRESENT")
    sys.exit(0 if okall else 1)


if __name__ == "__main__":
    main()
