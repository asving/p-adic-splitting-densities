#!/usr/bin/env python3
"""OM-3 certification leg 5 (HYP.88, GENIND-BOX-4's residue; also HYP.35's quartic stratum and
HYP.30's simple-slice ingredients): the n = 4 PER-GENRE PREFACTOR LEDGER, expanded and checked.

GENIND-BOX-4 (EFF.GENIND.78) prices the simple-slice β-term bookkeeping as "displayed, not
expanded per genre"; ANNEX R R1.4 records that "the per-genre prefactor ledgers" are exactly what
remains compressed.  This leg EXPANDS the ledger at m = 4 (the first degree with β-genres) and
certifies it exhaustively.

THE LEDGER LAW (the §C lemma of the unit note).  Per center (reduction x⁴, coefficients
a₃..a₀ with v ≥ 1, window N, total Q^{4(N−1)}), classify window-solid members
(v(a₀) < N as read) by their FIRST-STEP READ datum:
  hull  = the Newton polygon, sides (length L_ℓ, slope k_ℓ = num/den in lowest terms),
          slopes strictly decreasing left→right;
  per-side residual = the monic residual polynomial class (unit-normalized from the line digits;
          for den > 1 read at the den-strided abscissas), classified by its FACTORIZATION
          PATTERN over F_Q — the HYP.23 census objects.
Then, with ℓ(i) the hull height at abscissa i:
  (D.2) [explicit-residual law]   #members with (hull, explicit residual tuple) fixed
          =  Q^{ Σ_{i=0}^{3} (N − 1 − ℓ(i))  or  (N − ⌈ℓ(i)⌉) at non-integer line heights };
  (D.3) [genre prefactor = census] #distinct residual tuples of a genre
          =  Π_sides  S⁰_λ(Q, d) — the pattern census over F_Q with the irreducible y EXCLUDED
          (z-letters ∈ F_Q^×), i.e. formula (B.2) of the census leg with I(1, Q) → I(1, Q) − 1;
  (D.1) [per-genre ledger]        #members entering the genre = (D.3) × (D.2).
Consequences certified as named instances:
  · α-genre (single side, integer k, residual (y−z)⁴):  (Q−1)·Q^{4(N−1) − 10k} — GENIND.A(I)'s
    relative mass (Q−1)Q^{−k·m(m+1)/2} at m = 4;
  · CS4-E(h) (single side, slope h/2, h odd, residual (y−z)²):  (Q−1)·Q^{4N−5h−3} — the corpus's
    quartic e-first law (EFF.GENIND.48), REPRODUCED by the ledger (HYP.35's stratum exactness);
  · deep bucket (a₀ ≡ 0 mod π^N): exactly Q^{3(N−1)}.
Every genre count is an exact finite product of Q-powers and census factors — the (CS-EXACT)
shape — and the β-genres' letter factors (Q−1) per continuing child are visible per genre.

Rings: ℤ/p^N (p = 2, 3) and F_q[t]/(t^N) (q = 2, 3, 4), windows N ≤ 5.  Exit 0 iff all green.
"""

import sys
from math import gcd
from itertools import product
from collections import Counter

from om3_bracket_history_check import MixedChar, EqualChar
from om3_residual_census_check import necklace, census_formula

# ------------------------------- hull machinery ------------------------------------------------


def lower_hull(points):
    """points: list of (x, y) with x increasing; returns hull vertex list."""
    hull = []
    for p in points:
        while len(hull) >= 2:
            (x1, y1), (x2, y2) = hull[-2], hull[-1]
            # remove hull[-1] if it is above or on the segment hull[-2]→p
            if (y2 - y1) * (p[0] - x1) >= (p[1] - y1) * (x2 - x1):
                hull.pop()
            else:
                break
        hull.append(p)
    return hull


def hull_heights(verts, m):
    """ℓ(i) as a Fraction-free (num, den) pair per abscissa 0..m."""
    from fractions import Fraction
    ell = {}
    for (x1, y1), (x2, y2) in zip(verts, verts[1:]):
        for i in range(x1, x2 + 1):
            ell[i] = Fraction(y1) + Fraction(y2 - y1, x2 - x1) * (i - x1)
    return ell


# ------------------------------- per-member first read -----------------------------------------


def first_read(A, coeffs, N):
    """coeffs = (a0, a1, a2, a3); returns None (deep) or (genre_key, residual_tuple_key, ndigits)
    where ndigits = Σ free digits (the (D.2) exponent)."""
    from fractions import Fraction
    vs = [A.val(coeffs[i], N) for i in range(4)]
    if vs[0] >= N:
        return None
    pts = [(i, vs[i]) for i in range(4) if vs[i] < N] + [(4, 0)]
    verts = lower_hull(pts)
    vset = {x for (x, y) in verts}
    ell = hull_heights(verts, 4)
    # sides
    sides = []
    restuples = []
    ndig = 0
    for i in range(4):
        li = ell[i]
        if li.denominator == 1:
            ndig += N - 1 - int(li)
        else:
            ndig += N - (int(li) + 1)  # ⌈ℓ(i)⌉ for non-integer
    for (x1, y1), (x2, y2) in zip(verts, verts[1:]):
        L = x2 - x1
        drop = y1 - y2
        den = L // gcd(L, drop) if drop != 0 else L // L
        g = gcd(L, drop) if drop != 0 else L
        num = drop // g if drop != 0 else 0
        den = L // g if drop != 0 else 1
        # residual coefficients at abscissas x1, x1+den, ..., x2
        deg = L // den
        rc = []
        for j in range(deg + 1):
            i = x1 + j * den
            h = y1 - j * num
            if i == 4:
                rc.append('ONE')
            else:
                rc.append(digit_key(A, coeffs[i], h))
        sides.append((L, num, den))
        restuples.append(tuple(rc))
    genre = (tuple(sides), tuple(pattern_key(A, rt) for rt in restuples))
    return genre, (tuple(sides), tuple(restuples)), ndig


def digit_key(A, a, h):
    return A.digit(a, h) if not isinstance(A, MixedChar) else A.digit(a, h)


# residual pattern classification over the residue field --------------------------------------


def field_ops(A):
    if isinstance(A, MixedChar):
        p = A.p
        elts = list(range(p))
        add = lambda x, y: (x + y) % p
        mul = lambda x, y: (x * y) % p
        neg = lambda x: (-x) % p
        zero, one = 0, 1
    else:
        F = A.F
        elts = F.elts
        add, mul, neg = F.add, F.mul, F.neg
        zero, one = F.zero, F.one
    return elts, add, mul, neg, zero, one


_pattern_cache = {}


def pattern_key(A, rc):
    """Factorization pattern of the monic normalization of the residual with coeff keys rc
    (low→high; entries field elements or 'ONE').  Pattern = sorted tuple of (deg, mult)."""
    elts, add, mul, neg, zero, one = field_ops(A)
    coeffs = tuple(one if c == 'ONE' else c for c in rc)
    key = (A.name, coeffs)
    if key in _pattern_cache:
        return _pattern_cache[key]
    # normalize monic: divide by leading (leading is a unit)
    lead = coeffs[-1]
    inv = next(e for e in elts if mul(lead, e) == one)
    mon = tuple(mul(c, inv) for c in coeffs)
    pat = factor_pattern_field(A, mon)
    _pattern_cache[key] = pat
    return pat


def polmul_f(A, a, b):
    elts, add, mul, neg, zero, one = field_ops(A)
    out = [zero] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            out[i + j] = add(out[i + j], mul(x, y))
    return tuple(out)


def poldiv_f(A, a, b):
    """a / monic b over the residue field; returns (q, r)."""
    elts, add, mul, neg, zero, one = field_ops(A)
    a = list(a)
    db = len(b) - 1
    if len(a) - 1 < db:
        return (), tuple(a)
    q = [zero] * (len(a) - db)
    for i in range(len(a) - 1, db - 1, -1):
        c = a[i]
        if c != zero:
            q[i - db] = c
            for j in range(db + 1):
                a[i - db + j] = add(a[i - db + j], neg(mul(c, b[j])))
    while a and a[-1] == zero:
        a.pop()
    return tuple(q), tuple(a)


_irr_cache = {}


def irreducibles_field(A, dmax):
    key = (A.name, dmax)
    if key in _irr_cache:
        return _irr_cache[key]
    elts, add, mul, neg, zero, one = field_ops(A)
    irr = {d: [] for d in range(1, dmax + 1)}
    for d in range(1, dmax + 1):
        for tail in product(elts, repeat=d):
            f = tuple(tail) + (one,)
            ok = True
            for dd in range(1, d // 2 + 1):
                for g in irr[dd]:
                    if poldiv_f(A, f, g)[1] == ():
                        ok = False
                        break
                if not ok:
                    break
            if ok:
                irr[d].append(f)
    _irr_cache[key] = irr
    return irr


def factor_pattern_field(A, mon):
    d = len(mon) - 1
    irr = irreducibles_field(A, max(d, 1))
    pat = []
    f = mon
    for dd in sorted(irr):
        for g in irr[dd]:
            m = 0
            while len(f) > 1:
                q, r = poldiv_f(A, f, g)
                if r == ():
                    f, m = q, m + 1
                else:
                    break
            if m:
                pat.append((dd, m))
        if len(f) == 1:
            break
    return tuple(sorted(pat))


def census_no_y(pattern, Q, dmax):
    """(B.2) census of monic pattern-λ polys with y ∤ (constant ≠ 0): I(1) → I(1) − 1."""
    I = {d: necklace(d, Q) for d in range(1, dmax + 1)}
    I[1] -= 1
    return census_formula(pattern, I)


# ------------------------------- the check ----------------------------------------------------


def check_ring(A, N, table=False):
    Q = A.Q
    tal_genre = Counter()
    tal_tuple = Counter()
    ndig_of = {}
    deep = 0
    rng = A.digits_range(N)
    for a0 in rng:
        for a1 in rng:
            for a2 in rng:
                for a3 in rng:
                    fr = first_read(A, (a0, a1, a2, a3), N)
                    if fr is None:
                        deep += 1
                        continue
                    genre, tup, ndig = fr
                    tal_genre[genre] += 1
                    tal_tuple[tup] += 1
                    ndig_of[genre] = ndig
    ok = True
    # partition cross-foot
    xf = sum(tal_genre.values()) + deep == Q ** (4 * (N - 1))
    ok &= xf
    # deep bucket
    dok = deep == Q ** (3 * (N - 1))
    ok &= dok
    # (D.2): every explicit tuple count is Q^{ndig}
    bad2 = 0
    for tup, cnt in tal_tuple.items():
        genre = (tup[0], tuple(pattern_key(A, rt) for rt in tup[1]))
        if cnt != Q ** ndig_of[genre]:
            bad2 += 1
    ok &= bad2 == 0
    # (D.3)+(D.1): per genre, #tuples = Π census_no_y(pattern) and count = that × Q^{ndig}
    bad3 = []
    for genre, cnt in tal_genre.items():
        sides, pats = genre
        ntup = sum(1 for tup in tal_tuple if (tup[0], tuple(pattern_key(A, rt) for rt in tup[1])) == genre)
        want_tup = 1
        for (L, num, den), pat in zip(sides, pats):
            want_tup *= census_no_y(pat, Q, max(1, L // den))
        if ntup != want_tup or cnt != want_tup * Q ** ndig_of[genre]:
            bad3.append((genre, cnt, ntup, want_tup))
    ok &= not bad3
    # named instances
    inst = []
    # α-genre k=1: sides ((4,1,1)), pattern ((1,4),)
    if 4 * 1 <= N - 1:
        g = (((4, 1, 1),), (((1, 4),),))
        got = tal_genre.get(g, 0)
        want = (Q - 1) * Q ** (4 * (N - 1) - 10)
        inst.append(('alpha k=1', got, want))
    # CS4-E(h=1): single side slope 1/2, residual pattern (1,2)
    if 2 * 1 <= N - 1:
        g = (((4, 1, 2),), (((1, 2),),))
        got = tal_genre.get(g, 0)
        want = (Q - 1) * Q ** (4 * N - 5 * 1 - 3)
        inst.append(('CS4-E h=1', got, want))
    if 2 * 3 <= N - 1:
        g = (((4, 3, 2),), (((1, 2),),))
        inst.append(('CS4-E h=3', tal_genre.get(g, 0), (Q - 1) * Q ** (4 * N - 5 * 3 - 3)))
    # β-genres with a continuing child + another block:
    #   same-slope two children inside one side: length-4 side slope k, pattern (1,2)+(1,2)
    if 4 * 1 <= N - 1:
        g = (((4, 1, 1),), (((1, 2), (1, 2)),))
        if g in tal_genre:
            # census: monic quartics = P₁²P₂², P₁ ≠ P₂ linear ≠ y: (Q−1)(Q−2)/2; Σℓ = 10
            want = (Q - 1) * (Q - 2) // 2 * Q ** (4 * (N - 1) - 10)
            inst.append(('beta[(2,2)@k=1 same-slope]', tal_genre[g], want))
        #   child μ=3 + linear at the same slope: pattern (1,1)+(1,3)
        g = (((4, 1, 1),), (((1, 1), (1, 3)),))
        if g in tal_genre:
            want = (Q - 1) * (Q - 2) * Q ** (4 * (N - 1) - 10)
            inst.append(('beta[(3,1)@k=1 same-slope]', tal_genre[g], want))
    #   distinct-slope: single root at slope 2 + continuing μ=3 child at slope 1: Σℓ = 11
    if 5 <= N - 1:
        g = (((1, 2, 1), (3, 1, 1)), (((1, 1),), ((1, 3),)))
        got = tal_genre.get(g, 0)
        want = (Q - 1) ** 2 * Q ** (4 * (N - 1) - 11)
        inst.append(('beta[1@2 | (3)@1]', got, want))
    iok = all(got == want for (_, got, want) in inst)
    ok &= iok
    print(f"  [{'OK ' if ok else 'FAIL'}] {A.name} N={N}: members={Q ** (4 * (N - 1))} "
          f"genres={len(tal_genre)} deep={deep}(=Q^{3 * (N - 1)}:{dok}) xfoot={xf} D2bad={bad2} "
          f"D3bad={len(bad3)} instances={[(n, g, w) for (n, g, w) in inst]}")
    if bad3:
        for b in bad3[:3]:
            print("      D3 FAIL:", b)
    if table:
        print(f"    -- LEDGER TABLE {A.name} N={N} (genre: sides | patterns | census Πc | "
              f"Q-exp | count) --")
        for genre in sorted(tal_genre, key=lambda g: (-tal_genre[g])):
            sides, pats = genre
            cens = 1
            for (L, num, den), pat in zip(sides, pats):
                cens *= census_no_y(pat, Q, max(1, L // den))
            print(f"    {sides} | {pats} | {cens} | Q^{ndig_of[genre]} | {tal_genre[genre]}")
    return ok


def check_slice(A, N, v0):
    """Slice mode: restrict to v(a₀) = v0 exactly and check (D.2)/(D.3) for the genres with
    ℓ(0) = v0 (exactly the genres contained in the slice).  Reaches the same-slope
    multi-child β-genres (e.g. residual (y−z₁)²(y−z₂)², Q ≥ 3) at windows where the full
    enumeration is out of reach."""
    Q = A.Q
    elts_a0 = [a for a in A.digits_range(N) if A.val(a, N) == v0]
    rng = A.digits_range(N)
    tal_genre, tal_tuple, ndig_of = Counter(), Counter(), {}
    for a0 in elts_a0:
        for a1 in rng:
            for a2 in rng:
                for a3 in rng:
                    fr = first_read(A, (a0, a1, a2, a3), N)
                    assert fr is not None
                    genre, tup, ndig = fr
                    tal_genre[genre] += 1
                    tal_tuple[tup] += 1
                    ndig_of[genre] = ndig
    ok = True
    bad2 = 0
    for tup, cnt in tal_tuple.items():
        genre = (tup[0], tuple(pattern_key(A, rt) for rt in tup[1]))
        if ndig_of[genre] is None:
            continue
        # only genres with ℓ(0) = v0 are complete in the slice
        sides, pats = genre
        ell0 = sum(L * num / den for (L, num, den) in sides)
        if ell0 != v0:
            continue
        if cnt != Q ** ndig_of[genre]:
            bad2 += 1
    bad3 = []
    seen_two_child = False
    for genre, cnt in tal_genre.items():
        sides, pats = genre
        ell0 = sum(L * num / den for (L, num, den) in sides)
        if ell0 != v0:
            continue
        ntup = sum(1 for tup in tal_tuple
                   if (tup[0], tuple(pattern_key(A, rt) for rt in tup[1])) == genre)
        want_tup = 1
        for (L, num, den), pat in zip(sides, pats):
            want_tup *= census_no_y(pat, Q, max(1, L // den))
        if ntup != want_tup or cnt != want_tup * Q ** ndig_of[genre]:
            bad3.append((genre, cnt, ntup, want_tup))
        if pats == (((1, 2), (1, 2)),):
            seen_two_child = True
            # the co-evolving two-double-children genre: census (Q−1)(Q−2)/2, Σℓ = 10
            want = (Q - 1) * (Q - 2) // 2 * Q ** (4 * (N - 1) - 10)
            if cnt != want:
                bad3.append(('two-child instance', cnt, want))
            else:
                print(f"    [instance OK] same-slope two-double-children genre: {cnt} = "
                      f"(Q−1)(Q−2)/2 · Q^{4 * (N - 1) - 10}")
    ok &= bad2 == 0 and not bad3 and seen_two_child
    print(f"  [{'OK ' if ok else 'FAIL'}] {A.name} N={N} SLICE v(a0)={v0}: genres@slice="
          f"{sum(1 for g in tal_genre if sum(L * n / d for (L, n, d) in g[0]) == v0)} "
          f"D2bad={bad2} D3bad={len(bad3)} two-child-seen={seen_two_child}")
    if bad3:
        for b in bad3[:3]:
            print("      D3 FAIL:", b)
    return ok


def main():
    okall = True
    okall &= check_ring(MixedChar(2), 4)
    okall &= check_ring(MixedChar(2), 5, table=True)
    okall &= check_ring(MixedChar(3), 3)
    okall &= check_ring(MixedChar(3), 4, table=True)
    okall &= check_ring(EqualChar(2, 1), 4)
    okall &= check_ring(EqualChar(2, 1), 5)
    okall &= check_ring(EqualChar(3, 1), 3)
    okall &= check_ring(EqualChar(2, 2), 3)
    # the distinct-slope β-genre needs ℓ(0) = 5, i.e. N = 6 (2^20 members at q = 2)
    okall &= check_ring(MixedChar(2), 6)
    # the same-slope TWO-CONTINUING-CHILDREN genre ((y−z₁)²(y−z₂)², Q ≥ 3) at ℓ(0) = 4, N = 5
    okall &= check_slice(MixedChar(3), 5, 4)
    okall &= check_slice(EqualChar(3, 1), 5, 4)
    print("\nRESULT:", "ALL CHECKS PASS" if okall else "FAILURES PRESENT")
    sys.exit(0 if okall else 1)


if __name__ == "__main__":
    main()
