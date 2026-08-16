#!/usr/bin/env python3
"""OM-1 certification script — the n=3 rate (docs/openmath-campaign/OM-1_n3-rate_2026-08-16.md).

Certifies, in exact integer/rational arithmetic, the NEW steps of the OM-1 outline:

  T1 (S4): the sharp triple count  #(undecided ∩ triple at M+3) <= q^4 * u(M);
  T2 (S5): the peel branch — Hensel root exactness, the reconstruction identity,
           injectivity of the (r, cofactor)-record, the count <= q^N * (n=2 tangent count),
           and the n=2 exact law #tangent = q^N re-verified numerically;
  T3 (S7): the sharp recursion u(M+3) <= q^(2(M+3)) + q^4 * u(M) on enumerated counts,
           plus consistency of the final geometric bound with the deep honest-decider
           fractions recorded in leancheck/notes/N3_CHECK_2026-08-13.md §6c;
  T4 (S8): exact-rational replay of the unroll T(M) = q^M*s(M) <= q^3 and the final
           RateSpecies (K,B,c) = (1,0,3) inequality with NAT-subtraction semantics,
           driven by the recursion's worst case; also checked on enumerated counts;
  T5     : the narrowed residue — H.97's literal hrate (1,1,0) is TRUE on all data,
           and the worst-case-recursion route provably misses it at M = 1.

READER (mirrors the Lean certificate set exactly; SOUND over-approximation of the
undecided set — it marks DECIDED only where a landed/ported certificate fires):
  * squarefree residue      -> DECIDED (level-1 certificates G.55/G.56/G.61c);
  * residue a perfect cube  -> for N >= 3 recentre and read E/L/R (H97r2 certificates,
                               all mod-p^3 conditions); case S recurses on the level-(N-3)
                               class of the extraction (the H97r3 step lemma);
                               for N < 3: UNDECIDED;
  * repeated root, not cube -> simple residual root exists; Hensel-lift, peel; DECIDED
                               iff some simple root has a NON-TANGENT quadratic cofactor
                               (the exact n=2 law undecided <=> tangent, G.36).
The T1/T3 inequalities are checked with the reader's sets on BOTH sides; the injection
logic being certified applies verbatim to the reader's sets (the step lemma's case split
and the extraction's descent are the reader's own recursion), so a violation would
falsify the counting argument. Exactness beyond that is not claimed.

Runtime: ~1 minute, stdlib only.  Exits ALL CHECKS PASSED or raises.
"""

from fractions import Fraction
from itertools import product
import sys

# ----------------------------------------------------------------------------
# basic p-adic helpers over Z/p^N (integers 0..p^N-1)
# ----------------------------------------------------------------------------

def vmin(x, p, N):
    """valuation of x mod p^N, capped at N (v(0 mod p^N) = N)."""
    x %= p ** N
    if x == 0:
        return N
    v = 0
    while x % p == 0:
        x //= p
        v += 1
    return v

def inv_mod(x, m):
    return pow(x, -1, m)

def cubic_val(a, x, m):
    a0, a1, a2 = a
    return (x**3 + a2 * x**2 + a1 * x + a0) % m

def cubic_der(a, x, m):
    a0, a1, a2 = a
    return (3 * x**2 + 2 * a2 * x + a1) % m

def shift_vec(a, g, m):
    """shiftVec a gamma, mod m: (F(g), F'(g), a2 + 3g)."""
    a0, a1, a2 = a
    return (cubic_val(a, g, m), cubic_der(a, g, m), (a2 + 3 * g) % m)

def cube_coeff(g, p):
    """coefficient vector of (X-g)^3 over F_p."""
    return ((-(g**3)) % p, (3 * g**2) % p, (-(3 * g)) % p)

# ----------------------------------------------------------------------------
# n = 2: the tangency reader (exact law: undecided <=> tangent, G.36)
# ----------------------------------------------------------------------------

def quad_tangent(g, p, N):
    """Is the quadratic class g = (g0, g1) mod p^N tangent at depth N?
    Tang: exists gamma with p^N | G(gamma), p^ceil(N/2) | G'(gamma);
    G = X^2 + g1 X + g0, G' = 2X + g1.  Solve the derivative congruence first."""
    g0, g1 = g
    m = p ** N
    h = (N + 1) // 2
    ph = p ** h
    # 2*gamma = -g1 mod p^h
    if p == 2:
        if g1 % 2 != 0:
            return False  # 2gamma+g1 odd, never divisible by 2 (h>=1)
        # gamma = -g1/2 mod 2^(h-1); enumerate the 2^(N-h+1) candidates mod 2^N
        base = (-(g1 // 2)) % (2 ** (h - 1)) if h >= 1 else 0
        step = 2 ** (h - 1)
    else:
        base = (-g1 * inv_mod(2, ph)) % ph
        step = ph
    gamma = base
    while gamma < m:
        if (gamma * gamma + g1 * gamma + g0) % m == 0 and (2 * gamma + g1) % ph == 0:
            return True
        gamma += step
    return False

# ----------------------------------------------------------------------------
# the n = 3 reader
# ----------------------------------------------------------------------------

class Reader:
    def __init__(self, p):
        self.p = p
        self.memo = {}

    def simple_roots(self, a):
        """simple roots of the residue cubic over F_p."""
        p = self.p
        return [r for r in range(p)
                if cubic_val(a, r, p) == 0 and cubic_der(a, r, p) != 0]

    def repeated_root(self, a):
        p = self.p
        return any(cubic_val(a, r, p) == 0 and cubic_der(a, r, p) == 0
                   for r in range(p))

    def cube_centre(self, a):
        """gamma-bar if the residue cubic is (X-gamma)^3, else None."""
        p = self.p
        res = tuple(x % p for x in a)
        for g in range(p):
            if cube_coeff(g, p) == res:
                return g
        return None

    def hensel_root(self, a, rho, N):
        """Newton-lift the simple residue root rho to a root of F_a mod p^N."""
        p = self.p
        m = p ** N
        r = rho
        for _ in range(N + 2):
            fr = cubic_val(a, r, m)
            if fr == 0:
                break
            dr = cubic_der(a, r, m)
            r = (r - fr * inv_mod(dr, m)) % m
        assert cubic_val(a, r, m) == 0, "Hensel iteration failed to converge"
        assert cubic_der(a, r, m) % p != 0, "derivative not a unit at the lifted root"
        return r

    def undecided(self, a, N):
        """SOUND reader: True = (reader-)undecided for the class a mod p^N."""
        p = self.p
        a = tuple(x % p ** N for x in a)
        key = (a, N)
        if key in self.memo:
            return self.memo[key]
        res = self._undecided(a, N)
        self.memo[key] = res
        return res

    def _undecided(self, a, N):
        p = self.p
        if N == 0:
            return True
        centre = self.cube_centre(a)
        if centre is not None:
            # triple-root stratum
            if N < 3:
                return True
            m = p ** N
            B0, B1, B2 = shift_vec(a, centre, m)
            v0 = vmin(B0, p, N)
            v1 = vmin(B1, p, N)
            if v0 < 2:
                return False           # CASE E: c3ram
            if v1 < 2:
                return False           # CASE L: c3linRam
            if v0 < 3:
                return False           # CASE R: c3ram
            # CASE S: extraction, recurse at level M = N-3
            M = N - 3
            d = (B0 // p**3, B1 // p**2, B2 // p)
            return self.undecided(tuple(x % p ** max(M, 1) for x in d), M)
        if not self.repeated_root(a):
            # squarefree residue (no repeated root in F_p; for a cubic every repeated
            # factor is linear, so this IS squarefreeness): level-1 certificates decide
            return False
        roots = self.simple_roots(a)
        # repeated root present but not a cube => a simple root exists
        assert roots, "trichotomy violated: repeated non-cube residue with no simple root"
        for rho in roots:
            r = self.hensel_root(a, rho, N)
            m = p ** N
            g = ((a[1] + a[2] * r + r * r) % m, (a[2] + r) % m)
            if not quad_tangent(g, p, N):
                return False           # peel branch decides through the n=2 law
        return True

# ----------------------------------------------------------------------------
# enumeration
# ----------------------------------------------------------------------------

def enumerate_undecided(reader, N):
    p = reader.p
    m = p ** N
    und = []
    for a in product(range(m), repeat=3):
        if reader.undecided(a, N):
            und.append(a)
    return und

def is_triple(reader, a):
    return reader.cube_centre(a) is not None

# ----------------------------------------------------------------------------
# the checks
# ----------------------------------------------------------------------------

def run():
    ok = lambda s: print("  OK   " + s)
    LEVELS = {2: 6, 3: 4}
    undec = {}      # (p, N) -> list of undecided classes
    counts = {}     # (p, N) -> u(N)
    print("== enumeration (sound reader) ==")
    for p, Nmax in LEVELS.items():
        r = Reader(p)
        counts[(p, 0)] = 1
        for N in range(1, Nmax + 1):
            u = enumerate_undecided(r, N)
            undec[(p, N)] = u
            counts[(p, N)] = len(u)
            print(f"  p={p} N={N}: u(N) = {len(u)}  (fraction {Fraction(len(u), p**(3*N))})")

    # --- sanity: level-1 exactness (true undecided set = repeated-root residues, q^2)
    print("== level-1 exact census (sanity anchor for the reader) ==")
    for p in LEVELS:
        assert counts[(p, 1)] == p ** 2, (p, counts[(p, 1)])
        ok(f"p={p}: u(1) = q^2 = {p**2}, i.e. s(1) = 1/q exactly")

    # --- T1: sharp triple count
    print("== T1 (S4): #(undecided & triple at M+3) <= q^4 * u(M) ==")
    t1_cells = 0
    for p, Nmax in LEVELS.items():
        r = Reader(p)
        for N in range(3, Nmax + 1):
            M = N - 3
            lhs = sum(1 for a in undec[(p, N)] if is_triple(r, a))
            rhs = p ** 4 * counts[(p, M)]
            assert lhs <= rhs, ("T1 FAIL", p, N, lhs, rhs)
            ok(f"p={p} M+3={N}: {lhs} <= q^4*u({M}) = {rhs}")
            t1_cells += 1
            # A1 attack surface: also check the mixed-box record has no collisions
            seen = {}
            m = p ** N
            for a in undec[(p, N)]:
                if not is_triple(r, a):
                    continue
                g = r.cube_centre(a)
                B0, B1, B2 = shift_vec(a, g, m)
                assert B0 % p**3 == 0 and B1 % p**2 == 0 and B2 % p == 0, \
                    ("step lemma violated: undecided triple class not in case S", p, N, a)
                box = (g, (B0 // p**3) % p**max(M, 1) if M > 0 else 0,
                          (B1 // p**2) % p**(M + 1), (B2 // p) % p**(M + 2))
                assert box not in seen, ("T1 injection collision", p, N, a, seen[box])
                seen[box] = a
                if M > 0:
                    d = ((B0 // p**3) % p**M, (B1 // p**2) % p**M, (B2 // p) % p**M)
                    assert r.undecided(d, M), \
                        ("extraction's level-M class decided", p, N, a)
            ok(f"p={p} M+3={N}: mixed-box record injective; extractions undecided at level {M}")

    # --- T2: the peel branch
    print("== T2 (S5): peel branch — root, reconstruction, injection, count ==")
    t2_cells = 0
    for p, Nmax in LEVELS.items():
        r = Reader(p)
        # the n=2 exact law, re-verified numerically: #tangent classes = q^N
        for N in range(1, min(Nmax, 5) + 1):
            m = p ** N
            tang = sum(1 for g in product(range(m), repeat=2) if quad_tangent(g, p, N))
            assert tang == p ** N, ("n=2 law violated numerically", p, N, tang)
        ok(f"p={p}: #tangent quadratic classes = q^N for N <= {min(Nmax,5)} (G.36's law)")
        for N in range(1, Nmax + 1):
            m = p ** N
            record = {}
            n_peel = 0
            for a in undec[(p, N)]:
                roots = r.simple_roots(a)
                if not roots:
                    continue
                n_peel += 1
                rho = roots[0]
                rr = r.hensel_root(a, rho, N)
                g = ((a[1] + a[2] * rr + rr * rr) % m, (a[2] + rr) % m)
                # (i) root and unit derivative verified inside hensel_root
                # (ii) reconstruction identity a = (-r g0, g0 - g1 r, g1 - r)
                rec = ((-rr * g[0]) % m, (g[0] - g[1] * rr) % m, (g[1] - rr) % m)
                assert rec == a, ("reconstruction identity FAIL", p, N, a, rec)
                # cofactor must be n=2-undecided (tangent) — the S5 reduction
                assert quad_tangent(g, p, N), ("cofactor decided on undecided cubic", p, N, a)
                # (iii) injectivity of the record
                key = (rr, g)
                assert key not in record, ("T2 record collision", p, N, a, record[key])
                record[key] = a
            bound = p ** N * p ** N
            assert n_peel <= bound, ("T2 count FAIL", p, N, n_peel, bound)
            ok(f"p={p} N={N}: peel-branch classes {n_peel} <= q^(2N) = {bound}; "
               f"record injective; all cofactors n=2-undecided")
            t2_cells += 1

    # --- T3: the sharp recursion on enumerated counts
    print("== T3 (S7): u(M+3) <= q^(2(M+3)) + q^4*u(M) ==")
    for p, Nmax in LEVELS.items():
        for N in range(3, Nmax + 1):
            M = N - 3
            lhs = counts[(p, N)]
            rhs = p ** (2 * N) + p ** 4 * counts[(p, M)]
            assert lhs <= rhs, ("T3 FAIL", p, N, lhs, rhs)
            ok(f"p={p}: u({N}) = {lhs} <= q^(2*{N}) + q^4*u({M}) = {rhs}")

    # deep consistency: honest-decider undecided fractions (sound over-approximations
    # of s(N)), transcribed from leancheck/notes/N3_CHECK_2026-08-13.md §6c
    decider = {2: [Fraction(1, 2), Fraction(1875, 10000), Fraction(94, 1000),
                   Fraction(47, 1000), Fraction(21, 1000), Fraction(107, 10000),
                   Fraction(54, 10000), Fraction(26, 10000)],
               3: [Fraction(33, 100), Fraction(86, 1000), Fraction(29, 1000),
                   Fraction(96, 10000), Fraction(31, 10000)]}
    print("== T3b: geometric bound q^3*q^(-N) vs the deep decider fractions ==")
    for p, fr in decider.items():
        for i, f in enumerate(fr):
            N = i + 1
            bound = Fraction(p ** 3, p ** N)
            assert f <= bound, ("T3b FAIL", p, N, f, bound)
        ok(f"p={p}: decider s(N) <= q^(3-N) for N = 1..{len(fr)}")

    # --- T4: the unroll and the RateSpecies shape, exact rationals
    print("== T4 (S8): T(M) = q^M s(M) <= q^3, and RateSpecies (1,0,3) ==")
    for q in (2, 3, 4):
        # worst-case sequence driven by the recursion
        s = {0: Fraction(1), 1: Fraction(1), 2: Fraction(1)}
        for M in range(0, 38):
            s[M + 3] = Fraction(1, q ** (M + 3)) + Fraction(1, q ** 5) * s[M]
        for M in range(0, 41):
            TM = q ** M * s[M]
            assert TM <= q ** 3, ("T4 induction FAIL", q, M, TM)
            if M >= 1:
                cexp = M - 3 if M >= 3 else 0          # NAT subtraction
                bound = Fraction(1) * 1 * Fraction(1, q ** cexp)  # K*M^B*(q^(M-c))^-1
                assert s[M] <= bound, ("T4 species FAIL", q, M, s[M], bound)
        ok(f"q={q}: worst-case recursion satisfies T(M) <= q^3 and "
           f"s(M) <= 1*M^0*(q^(M-3))^-1 for M = 1..40")
    # and on the enumerated counts
    for p, Nmax in LEVELS.items():
        for N in range(1, Nmax + 1):
            sN = Fraction(counts[(p, N)], p ** (3 * N))
            cexp = N - 3 if N >= 3 else 0
            assert sN <= Fraction(1, p ** cexp), ("T4 enum FAIL", p, N, sN)
        ok(f"p={p}: enumerated s(N) <= (q^(N-3))^-1 for N = 1..{Nmax}")

    # --- T5: the narrowed residue (1,1,0)
    print("== T5: hrate (1,1,0) — true on all data, missed by the route at M=1 ==")
    for p, Nmax in LEVELS.items():
        for N in range(1, Nmax + 1):
            sN = Fraction(counts[(p, N)], p ** (3 * N))
            assert sN <= Fraction(N, p ** N), ("T5 FAIL on enumeration", p, N, sN)
        ok(f"p={p}: enumerated s(N) <= N*q^(-N) (H.97's hrate shape) for N = 1..{Nmax}")
    for p, fr in decider.items():
        for i, f in enumerate(fr):
            N = i + 1
            assert f <= Fraction(N, p ** N), ("T5 FAIL on decider", p, N, f)
        ok(f"p={p}: decider s(N) <= N*q^(-N) for N = 1..{len(fr)}")
    for q in (2, 3, 4):
        # the worst-case recursion value at M=1 is 1 > 1/q: the route cannot give (1,1,0)
        assert Fraction(1) > Fraction(1, q)
    ok("the peel+triple route's base bound s(1) <= 1 exceeds q^(-1): "
       "(1,1,0) needs the level-1 census — recorded as the narrowed residue")

    print("ALL CHECKS PASSED")

if __name__ == "__main__":
    sys.setrecursionlimit(10000)
    run()
