#!/usr/bin/env python3
"""OM-3 certification leg 2 (HYP.23, the [H-d] residual censuses): the exact per-degree
factorization-pattern census law over EVERY finite residue field, and the κ(T) orbit factor.

CLAIMS CERTIFIED (the §B law of docs/openmath-campaign/OM-3_count-layer_2026-08-16.md):

  (B.1) [irreducible census]  I(d, Q) = (1/d) Σ_{e|d} μ(e) Q^{d/e}  — checked against direct
        sieve construction of the monic irreducibles.
  (B.2) [pattern census]  For a pattern λ giving, per degree d, multiplicity counts r_{d,m}
        (r_{d,m} = number of branches of degree d carrying multiplicity m; R_d = Σ_m r_{d,m}):
            #{monic f of degree n over F_Q with pattern λ}
              = Π_d  I_d! / ( (I_d − R_d)! · Π_m r_{d,m}! )
        — checked against brute factorization of ALL monic degree-n polynomials.
  (B.3) [κ(T) = the decoration-orbit factor]  For branches additionally carrying decorations D
        (multiplicities r_{d,m,D} within each (d, m) class):
            #decorated configurations = κ(T) · C₀(Q),
            κ(T) = Π_{d,m} r_{d,m}! / Π_D r_{d,m,D}!,   C₀(Q) = the (B.2) product,
        — checked against DIRECT enumeration of decorated configurations (sets of
        (irreducible, m, D) with distinct irreducibles), i.e. the 2026-08-12 orbit correction
        of W-12.A / LEMMA W12-S2.1's C₀(q) rider, reproduced from first principles.

Fields: Q ∈ {2, 3, 4, 5, 8, 9} — primes AND prime powers, both characteristics of residue field
(char 2 and char 3 appear at prime-power order), per GENIND-BOX-3's prime-power fence and the
G.23 two-prime lesson.  Degrees: n ≤ 6 at Q ∈ {2, 3}, n ≤ 5 at Q ∈ {4, 5}, n ≤ 4 at Q ∈ {8, 9}.
All arithmetic exact (finite fields implemented directly; no floating point).

Exit 0 iff every check passes.
"""

import sys
from itertools import product
from math import factorial

# ------------------------------- finite fields F_{p^k} ----------------------------------------
# Elements: tuples of length k over Z_p (coeffs of the class of x^i modulo the defining poly).

DEFPOLY = {  # monic defining polynomial coefficients (low to high), irreducible over F_p
    (2, 1): (0, 1), (3, 1): (0, 1), (5, 1): (0, 1),
    (2, 2): (1, 1, 1),        # x^2 + x + 1 over F_2
    (2, 3): (1, 1, 0, 1),     # x^3 + x + 1 over F_2
    (3, 2): (1, 0, 1),        # x^2 + 1 over F_3
}


class FF:
    """F_{p^k} with exact tuple arithmetic."""

    def __init__(self, p, k):
        self.p, self.k, self.q = p, k, p ** k
        self.red = DEFPOLY[(p, k)]
        self.zero = (0,) * k
        self.one = tuple([1] + [0] * (k - 1))
        self.elts = [tuple(t) for t in product(range(p), repeat=k)]

    def add(self, a, b):
        return tuple((x + y) % self.p for x, y in zip(a, b))

    def neg(self, a):
        return tuple((-x) % self.p for x in a)

    def mul(self, a, b):
        p, k = self.p, self.k
        prod_ = [0] * (2 * k - 1)
        for i, x in enumerate(a):
            if x:
                for j, y in enumerate(b):
                    prod_[i + j] = (prod_[i + j] + x * y) % p
        # reduce by defining poly (monic, degree k): x^k ≡ −(red[0..k−1])
        for deg in range(2 * k - 2, k - 1, -1):
            c = prod_[deg]
            if c:
                prod_[deg] = 0
                for j in range(k):
                    prod_[deg - k + j] = (prod_[deg - k + j] - c * self.red[j]) % p
        return tuple(prod_[:k])


# ------------------------------- polynomials over F_Q -----------------------------------------
# Poly = tuple of field elements, low to high, last element nonzero (or empty tuple = 0).


def pnorm(F, c):
    c = list(c)
    while c and c[-1] == F.zero:
        c.pop()
    return tuple(c)


def pmul(F, a, b):
    if not a or not b:
        return ()
    out = [F.zero] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        if x != F.zero:
            for j, y in enumerate(b):
                out[i + j] = F.add(out[i + j], F.mul(x, y))
    return pnorm(F, out)


def pdivmod_monic(F, a, b):
    """Divide a by MONIC b; returns (quot, rem)."""
    a = list(a)
    db = len(b) - 1
    if len(a) - 1 < db:
        return (), pnorm(F, a)
    quot = [F.zero] * (len(a) - db)
    for i in range(len(a) - 1, db - 1, -1):
        c = a[i]
        if c != F.zero:
            quot[i - db] = c
            for j in range(db + 1):
                a[i - db + j] = F.add(a[i - db + j], F.neg(F.mul(c, b[j])))
    return pnorm(F, quot), pnorm(F, a)


def monic_polys(F, d):
    """All monic polynomials of degree d (as coefficient tuples)."""
    for lower in product(F.elts, repeat=d):
        yield tuple(lower) + (F.one,)


def irreducibles_up_to(F, dmax):
    """Monic irreducibles of degree 1..dmax, by sieve."""
    irr = {d: [] for d in range(1, dmax + 1)}
    for d in range(1, dmax + 1):
        for f in monic_polys(F, d):
            divisible = False
            for dd in range(1, d // 2 + 1):
                for g in irr[dd]:
                    if pdivmod_monic(F, f, g)[1] == ():
                        divisible = True
                        break
                if divisible:
                    break
            if not divisible:
                irr[d].append(f)
    return irr


def factor_pattern(F, f, irr):
    """Multiset pattern {(d, m)} of monic f (assumed degree ≥ 1)."""
    pat = []
    for d in sorted(irr):
        for g in irr[d]:
            m = 0
            while True:
                q, r = pdivmod_monic(F, f, g)
                if r == () and q is not None:
                    f, m = q, m + 1
                    if len(f) == 1:  # reduced to a constant
                        break
                else:
                    break
            if m:
                pat.append((d, m))
        if len(f) == 1:
            break
    assert len(f) == 1, "factorization incomplete"
    return tuple(sorted(pat))


def moebius(n):
    m, res = n, 1
    d = 2
    while d * d <= m:
        if m % d == 0:
            m //= d
            if m % d == 0:
                return 0
            res = -res
        d += 1
    if m > 1:
        res = -res
    return res


def divisors(n):
    return [d for d in range(1, n + 1) if n % d == 0]


def necklace(d, Q):
    s = sum(moebius(e) * Q ** (d // e) for e in divisors(d))
    assert s % d == 0
    return s // d


def census_formula(pattern, Icounts):
    """(B.2): Π_d I_d!/((I_d − R_d)!·Π_m r_{d,m}!)."""
    from collections import Counter
    byd = {}
    for (d, m) in pattern:
        byd.setdefault(d, []).append(m)
    val = 1
    for d, ms in byd.items():
        I = Icounts[d]
        R = len(ms)
        if R > I:
            return 0
        val *= factorial(I) // factorial(I - R)
        for mult in Counter(ms).values():
            val //= factorial(mult)
    return val


def check_field(p, k, nmax):
    F = FF(p, k)
    Q = F.q
    irr = irreducibles_up_to(F, nmax)
    ok = True
    # (B.1)
    for d in range(1, nmax + 1):
        got, want = len(irr[d]), necklace(d, Q)
        if got != want:
            ok = False
        print(f"  [B.1 {'OK' if got == want else 'FAIL'}] Q={Q} I({d}) sieve={got} necklace={want}")
    Icounts = {d: len(irr[d]) for d in range(1, nmax + 1)}
    # (B.2)
    for n in range(1, nmax + 1):
        from collections import Counter
        tally = Counter()
        for f in monic_polys(F, n):
            tally[factor_pattern(F, f, irr)] += 1
        total_ok = sum(tally.values()) == Q ** n
        bad = []
        for pat, cnt in sorted(tally.items()):
            fc = census_formula(pat, Icounts)
            if fc != cnt:
                bad.append((pat, cnt, fc))
        # also check formula gives 0 or absent patterns consistently: every formula-positive
        # pattern of total degree n must appear
        allpats = enumerate_patterns(n, Icounts)
        for pat in allpats:
            fc = census_formula(pat, Icounts)
            if fc > 0 and tally.get(pat, 0) != fc:
                if (pat, tally.get(pat, 0), fc) not in bad:
                    bad.append((pat, tally.get(pat, 0), fc))
        stat = total_ok and not bad
        ok &= stat
        print(f"  [B.2 {'OK' if stat else 'FAIL'}] Q={Q} n={n}: {len(tally)} patterns, "
              f"Σ={sum(tally.values())}=Q^n:{total_ok}" + (f" BAD={bad[:3]}" if bad else ""))
    return ok, F, irr, Icounts


def enumerate_patterns(n, Icounts):
    """All multisets {(d, m)} with Σ d·m = n (d ≤ max degree available)."""
    out = set()

    def rec(rem, minpair, cur):
        if rem == 0:
            out.add(tuple(sorted(cur)))
            return
        for d in range(1, rem + 1):
            if d not in Icounts and d <= rem:
                continue
            for m in range(1, rem // d + 1):
                pair = (d, m)
                if pair < minpair:
                    continue
                rec(rem - d * m, pair, cur + [pair])

    rec(n, (0, 0), [])
    # filter: allow repeated (d, m) pairs — multiset; rec as written never repeats a pair.
    # Redo allowing repeats via counts:
    out2 = set()

    def rec2(rem, pairs, idx, cur):
        if rem == 0:
            out2.add(tuple(sorted(cur)))
            return
        if idx >= len(pairs):
            return
        d, m = pairs[idx]
        maxrep = rem // (d * m)
        for rep in range(maxrep + 1):
            rec2(rem - rep * d * m, pairs, idx + 1, cur + [(d, m)] * rep)

    pairs = [(d, m) for d in sorted(Icounts) for m in range(1, n // d + 1) if d * m <= n]
    rec2(n, pairs, 0, [])
    return out2


def check_kappa(F, irr, Icounts):
    """(B.3): decorated-configuration count = κ(T)·C₀(Q), against direct enumeration.
    A decorated shape at a single degree d: a list of (m, D) branch classes; configurations =
    injections of distinct irreducibles of degree d into the branches, unordered within
    identical (m, D) classes."""
    from collections import Counter
    ok = True
    Q = F.q
    shapes = [
        # (d, [(m, D), ...]) — the classes; D is an opaque decoration tag
        (1, [(2, "A"), (2, "B")]),          # two same-(d,m) branches, DISTINCT decorations
        (1, [(2, "A"), (2, "A")]),          # ... identical decorations (κ = 1)
        (1, [(2, "A"), (2, "B"), (1, "C")]),
        (1, [(3, "A"), (3, "B"), (3, "A")]),
        (2, [(2, "A"), (2, "B")]),          # degree-2 branches
        (1, [(2, "A"), (2, "B"), (2, "C")]),
    ]
    for d, classes in shapes:
        I = Icounts.get(d, 0)
        R = len(classes)
        if I < R:
            continue
        # direct: count distinct sets of (irreducible ↦ (m, D)) assignments
        seen = set()
        from itertools import permutations, combinations
        for combo in combinations(range(I), R):
            for perm in permutations(combo):
                assign = frozenset((perm[i], classes[i]) for i in range(R))
                seen.add(assign)
        direct = len(seen)
        # formula: κ·C₀ at this degree
        ms = [m for (m, D) in classes]
        kappa = 1
        for m, cnt in Counter(ms).items():
            kappa *= factorial(cnt)
        for (m, D), cnt in Counter(classes).items():
            kappa //= factorial(cnt)
        c0 = factorial(I) // factorial(I - R)
        for m, cnt in Counter(ms).items():
            c0 //= factorial(cnt)
        stat = direct == kappa * c0
        ok &= stat
        print(f"  [B.3 {'OK' if stat else 'FAIL'}] Q={Q} d={d} classes={classes}: "
              f"direct={direct} κ={kappa} C0={c0} κ·C0={kappa * c0}")
    return ok


def main():
    okall = True
    plan = [(2, 1, 6), (3, 1, 6), (2, 2, 5), (5, 1, 5), (2, 3, 4), (3, 2, 4)]
    for p, k, nmax in plan:
        print(f"== F_{p ** k} (p={p}, k={k}), n ≤ {nmax} ==")
        ok, F, irr, Icounts = check_field(p, k, nmax)
        okall &= ok
        okall &= check_kappa(F, irr, Icounts)
    print("\nRESULT:", "ALL CHECKS PASS" if okall else "FAILURES PRESENT")
    sys.exit(0 if okall else 1)


if __name__ == "__main__":
    main()
