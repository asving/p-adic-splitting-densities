#!/usr/bin/env python3
"""
A-C.2 certification: the RE-SIGNED C.109 node-cell count law (blueprint
CHAP-C_tower_grammar.md NODE C.109, amendment A-C.2, 2026-08-16).

WHAT IS CHECKED (exact counts, brute force over O = Z/p^N truncating Z_p):

  [LAW]  For well-formed nodes v (HTNode.WF: monic top, ceiled-consistency,
         L = #{j<m : (j,Pceil j) on hull}, sides = genuine cleared side slopes,
         side types of the sides' residual degrees), with the RE-SIGNED cell
         (EFF.W12.23's three-way membership: >= Pceil everywhere, equality at
         VERTICES only, per-side residual types):

           #{level-N classes in htCell}  =  Q^{B_v(N)} * prod_S S_{lambda_S}(Q)

         with B_v(N) = m*N - sum_{j<m} Pceil(j) - L  and  S_lambda(Q) the
         census of monic residuals with nonzero constant term of type lambda
         (C.107's sideCensus).  Instances at q = 2, 3 (and one at Q = 4 via a
         degree-2 key), m <= 2, including: an interior lattice point on a side
         (I2), a non-lattice interior position ell = 2 (I3), two sides sharing
         a vertex (the right-to-left sweep, I6), and a flat side (I5).

  [ENC]  The A-C.2 Lean encodings (OnHull / IsVertex / nodeSideSet / IsSide /
         nodeSideDeg, all N-arithmetic chord tests over the CEILED data) agree
         with a direct rational-arithmetic lower-convex-hull computation on
         every instance.  This is the non-textual leg for the new predicates.

  [MUT]  Mutations each KILL the law:
         M1 (drop WF, the machine-refuted C109Frozen defect): L off by one =>
            RHS changes, LHS fixed.
         M2 (refutation note's secondary example, VERIFIED here): m=1,
            Pceil=(2,0), sides = EMPTY: true count is Q^{N-3}(Q-1); NO value
            of L matches for Q >= 3; exactly L=1 matches at Q=2.
         M3 (the A-C.2 NEW finding, defect D3): the OLD htCell pin clause
            (npHgt = Pceil at EVERY j <= m) breaks the law wherever the
            polygon has a non-vertex position: at I2/q=2 with type (1,2) the
            old cell is EMPTY (char-2: (Y-c)^2 has zero interior coefficient)
            while RHS = (q-1) q^B; at I3 the old cell forces an exact pin at a
            non-lattice position, LHS_old = Q^{2N-4}(Q-1)^2 != Q^{2N-3}(Q-1).

  [C111] The frozen ht_fiber_exponent_nonneg (A-C.1) is numerically refuted
         (companion to the Lean refutation): a 2-node tree with hvis satisfied
         and sum(D, non-root) > sum(B).  ALSO: a WF-resistant instance (both
         nodes HTNode.WF) — so the A-C.2 re-sign must carry the per-node
         hypothesis, not just WF.

  [C114] The frozen ht_branch (A-C.1) is numerically refuted at the formula
         level: the singleton m=0 tree has stratum count 1 for EVERY kappa,
         while htBranchCount = kappa.  (Machine-checked in Lean at
         leanfinal/Uniformity/ChapC/C114_C111_REFUTATION.lean.txt.)

Exit 0 iff every check passes.  Run:  python3 c109_ac2_cell_check.py
"""

import itertools, sys
from fractions import Fraction
from math import gcd

# ----------------------------------------------------------------------------
# F_Q arithmetic: F_{p^d} as tuples of F_p coefficients mod a monic irreducible
# ----------------------------------------------------------------------------

class FQ:
    """The field F_{p^d}, elements = tuples (c_0,...,c_{d-1}) over F_p."""
    def __init__(self, p, modpoly=None):
        # modpoly: tuple of F_p coeffs (g_0,...,g_{d-1}) of monic g = x^d + ...
        self.p = p
        self.g = modpoly if modpoly is not None else ()
        self.d = len(self.g) if modpoly is not None else 1
        self.Q = p ** self.d
        self.zero = (0,) * self.d
        self.one = (1,) + (0,) * (self.d - 1)
        self.elems = [tuple(t) for t in itertools.product(range(p), repeat=self.d)]

    def add(self, a, b):
        return tuple((x + y) % self.p for x, y in zip(a, b))

    def neg(self, a):
        return tuple((-x) % self.p for x in a)

    def mul(self, a, b):
        p, d, g = self.p, self.d, self.g
        prod = [0] * (2 * d - 1)
        for i, x in enumerate(a):
            for j, y in enumerate(b):
                prod[i + j] = (prod[i + j] + x * y) % p
        for k in range(2 * d - 2, d - 1, -1):  # reduce x^k = -g * x^{k-d}
            c = prod[k]
            if c:
                prod[k] = 0
                for t in range(d):
                    prod[k - d + t] = (prod[k - d + t] - c * g[t]) % p
        return tuple(prod[:d])

    def inv(self, a):
        for b in self.elems:
            if self.mul(a, b) == self.one:
                return b
        raise ZeroDivisionError

# ---- polynomials over F_Q (dense coeff lists, index = degree) ---------------

def poly_trim(F, c):
    while c and c[-1] == F.zero:
        c = c[:-1]
    return c

def poly_mul(F, a, b):
    if not a or not b:
        return []
    out = [F.zero] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            out[i + j] = F.add(out[i + j], F.mul(x, y))
    return poly_trim(F, out)

def monic_polys(F, deg):
    """All monic polynomials of exact degree deg over F_Q, as coeff lists."""
    for tail in itertools.product(F.elems, repeat=deg):
        yield list(tail) + [F.one]

def factor_type(F, c):
    """Factorization type of monic c: sorted multiset of (deg, mult) over the
    DISTINCT monic irreducible factors (= residualTypeOf, C.107)."""
    c = list(c)
    assert c and c[-1] == F.one
    # build monic irreducibles up to deg(c) by sieve
    D = len(c) - 1
    irr = []
    for dd in range(1, D + 1):
        for cand in monic_polys(F, dd):
            reducible = False
            for a in irr:
                if len(a) - 1 <= dd - 1 and poly_divides(F, a, cand):
                    reducible = True
                    break
            if not reducible and dd > 1:
                # also check products of two lower-deg (covered by irr divisor test)
                pass
            if not reducible:
                irr.append(list(cand))
    ftype = []
    rem = c
    for a in irr:
        mult = 0
        while len(rem) > 1 and poly_divides(F, a, rem):
            rem = poly_quo(F, rem, a)
            mult += 1
        if mult:
            ftype.append((len(a) - 1, mult))
    assert len(rem) == 1, "unit remainder expected"
    return tuple(sorted(ftype))

def poly_divmod(F, num, den):
    """num, den coeff lists; den monic. Returns (quo, rem)."""
    num = list(num)
    dd = len(den) - 1
    quo = [F.zero] * max(0, len(num) - dd)
    while len(poly_trim(F, num)) - 1 >= dd and len(num) - 1 >= dd:
        num = poly_trim(F, num)
        if len(num) - 1 < dd:
            break
        k = len(num) - 1 - dd
        c = num[-1]
        quo[k] = c
        for t in range(dd + 1):
            num[k + t] = F.add(num[k + t], F.neg(F.mul(c, den[t])))
        num = num[:-1]
    return poly_trim(F, quo), poly_trim(F, num)

def poly_divides(F, a, b):
    _, r = poly_divmod(F, b, a)
    return not r

def poly_quo(F, b, a):
    q, r = poly_divmod(F, b, a)
    assert not r
    return q

# ----------------------------------------------------------------------------
# O = Z/p^N, polynomials over O; dev, gaussVal, digits (chapter B primitives)
# ----------------------------------------------------------------------------

def opoly_divmod(pN, num, den):
    """Polynomial division over Z/p^N by MONIC den. Coeff lists mod p^N."""
    num = [x % pN for x in num]
    den = [x % pN for x in den]
    while den and den[-1] == 0:
        den.pop()
    assert den[-1] == 1
    dd = len(den) - 1
    while num and num[-1] == 0:
        num.pop()
    quo = [0] * max(0, len(num) - dd)
    while len(num) - 1 >= dd and num:
        c = num[-1]
        k = len(num) - 1 - dd
        quo[k] = c
        for t in range(dd + 1):
            num[k + t] = (num[k + t] - c * den[t]) % pN
        while num and num[-1] == 0:
            num.pop()
    return quo, num

def dev(pN, Phi, f, m):
    """Phi-adic development coefficients a_0..a_m of f (B.02's dev)."""
    out = []
    cur = list(f)
    for _ in range(m + 1):
        cur, rem = opoly_divmod(pN, cur, Phi)
        out.append(rem)
    return out

def val_p(p, N, x):
    x %= p ** N
    if x == 0:
        return None  # infinity (as a level-N read: >= N)
    v = 0
    while x % p == 0:
        x //= p
        v += 1
    return v

def gauss_val(p, N, a):
    vals = [val_p(p, N, c) for c in a]
    vals = [v for v in vals if v is not None]
    return min(vals) if vals else None  # None = infinity

def digit(F, p, N, a, h, Phibar):
    """digit_h(a) in F_Q for a in (Z/p^N)[x]_{<d}: (a div p^h) mod p, reduced
    to the residue class mod Phibar (the class map is the identity on
    representatives of degree < d)."""
    d = F.d
    coeffs = [((c // (p ** h)) % p) for c in a] + [0] * d
    return tuple(coeffs[:d])

# ----------------------------------------------------------------------------
# The polygon: direct rational hull AND the A-C.2 Lean-form encodings
# ----------------------------------------------------------------------------

def hull_fn(pts):
    """Lower convex hull value H(j) at each integer j, for pts = {j: height}."""
    xs = sorted(pts)
    H = {}
    for j in xs:
        best = None
        for i in xs:
            for k in xs:
                if i <= j <= k and (i < k or i == j == k):
                    if i == k:
                        val = Fraction(pts[j])
                    else:
                        val = Fraction(pts[i]) * (k - j) / (k - i) + Fraction(pts[k]) * (j - i) / (k - i)
                    if best is None or val < best:
                        best = val
        H[j] = best
    return H

def direct_polygon_data(Pceil, m):
    """From the CEILED vector: hull, on-hull set, vertices, sides with spans.
    (Rational arithmetic; the ceiled points' hull = the true hull, the A-C.2
    reconstruction lemma.)"""
    pts = {j: Pceil[j] for j in range(m + 1)}
    H = hull_fn(pts)
    onhull = {j for j in range(m + 1) if Fraction(Pceil[j]) == H[j]}
    verts = []
    for j in sorted(onhull):
        if j in (0, m):
            verts.append(j)
            continue
        # vertex iff slope changes at j along the hull restricted to onhull pts
        left = max(i for i in onhull if i < j)
        right = min(k for k in onhull if k > j)
        sl = Fraction(pts[j] - pts[left], j - left)
        sr = Fraction(pts[right] - pts[j], right - j)
        if sl != sr:
            verts.append(j)
    sides = {}
    vs = verts
    for a, b in zip(vs, vs[1:]):
        du, dl = pts[a] - pts[b], b - a
        g = gcd(du, dl)
        u, l = du // g, dl // g
        sides[(u, l)] = (a, b, (b - a) // l)  # left, right, residual degree
    return H, onhull, set(verts), sides

# ---- the Lean-form (A-C.2) chord-test encodings over N -----------------------

def lean_OnHull(P, m, j):
    return all((k - i) * P[j] <= (k - j) * P[i] + (j - i) * P[k]
               for i in range(j + 1) for k in range(j, m + 1))

def lean_IsVertex(P, m, j):
    return all((k - i) * P[j] < (k - j) * P[i] + (j - i) * P[k]
               for i in range(j) for k in range(j + 1, m + 1))

def lean_ceiled_consistent(P, m):
    return all((k - i) * P[j] < (k - j) * P[i] + (j - i) * P[k] + (k - i)
               for i in range(m + 1) for j in range(i, m + 1) for k in range(j, m + 1)
               if i < k)

def lean_nodeSideSet(P, m, u, l):
    vals = {j: l * P[j] + u * j for j in range(m + 1)}
    mn = min(vals.values())
    return sorted(j for j in range(m + 1) if vals[j] == mn)

def lean_IsSide(P, m, u, l):
    return l > 0 and gcd(u, l) == 1 and len(lean_nodeSideSet(P, m, u, l)) >= 2

def lean_nodeSideDeg(P, m, u, l):
    s = lean_nodeSideSet(P, m, u, l)
    return (max(s) - min(s)) // l if s else 0

def lean_WF_data(P, m):
    """Returns (ok_ceiled, L, sides_set{(u,l): sideDeg}) per the A-C.2 defs."""
    okc = lean_ceiled_consistent(P, m)
    L = sum(1 for j in range(m) if lean_OnHull(P, m, j))
    # candidate slopes: from consecutive on-hull pairs
    oh = [j for j in range(m + 1) if lean_OnHull(P, m, j)]
    cands = set()
    for a, b in zip(oh, oh[1:]):
        du, dl = P[a] - P[b], b - a
        g = gcd(du, dl)
        cands.add((du // g, dl // g))
    sides = {(u, l): lean_nodeSideDeg(P, m, u, l) for (u, l) in cands if lean_IsSide(P, m, u, l)}
    return okc, L, sides

# ----------------------------------------------------------------------------
# The cell membership (re-signed and old), and the counts
# ----------------------------------------------------------------------------

def side_reads(F, p, N, Phi, devs, mdeg, u, l):
    """B.16/B.20/B.29: sideSet, sideMin, H0, resPoly over F_Q for the (u,l)
    direction, read from the development valuations."""
    nph = [gauss_val(p, N, a) for a in devs]  # index j = 0..m
    vals = {}
    for j, h in enumerate(nph):
        if h is not None:
            vals[j] = l * h + u * j
    if not vals:
        return None
    mn = min(vals.values())
    sideset = sorted(j for j, v in vals.items() if v == mn)
    j0 = sideset[0]
    H0 = nph[j0]
    ddeg = (max(sideset) - j0) // l
    coeffs = []
    for k in range(ddeg + 1):
        j = j0 + l * k
        h = H0 - u * k
        a = devs[j] if j < len(devs) else []
        if h < 0 or h >= N:
            coeffs.append(F.zero)
        else:
            coeffs.append(digit(F, p, N, a, h, None))
    return sideset, j0, H0, poly_trim(F, coeffs)

def monic_normalize(F, c):
    if not c:
        return c
    lead = c[-1]
    li = F.inv(lead)
    return [F.mul(li, x) for x in c]

def in_cell(F, p, N, Phi, f, node, semantics):
    """node = dict(m, Pceil, sides={(u,l): type}); semantics in {'new','old'}."""
    m, P = node["m"], node["Pceil"]
    d = len(Phi) - 1
    devs = dev(p ** N, Phi, f, m)
    nph = [gauss_val(p, N, a) for a in devs]
    for j in range(m + 1):
        h = nph[j]
        if semantics == "old":
            if h != P[j]:
                return False
        else:
            if not (h is None or h >= P[j]):
                return False
            if lean_IsVertex(P, m, j) and h != P[j]:
                return False
    for (u, l), lam in node["sides"].items():
        r = side_reads(F, p, N, Phi, devs, m * d, u, l)
        if r is None:
            continue
        _, _, _, res = r
        if len(res) <= 1:
            return False  # degenerate residual cannot carry the side type
        if factor_type(F, monic_normalize(F, res)) != lam:
            return False
    return True

def lhs_count(F, p, N, Phi, node, semantics="new"):
    d = len(Phi) - 1
    n = node["m"] * d
    pN = p ** N
    cnt = 0
    for a in itertools.product(range(pN), repeat=n):
        f = list(a) + [1]  # monicPoly
        if in_cell(F, p, N, Phi, f, node, semantics):
            cnt += 1
    return cnt

def side_census(F, lam):
    degree = sum(dd * mm for dd, mm in lam)
    c = 0
    for pol in monic_polys(F, degree):
        if pol[0] != F.zero and factor_type(F, pol) == lam:
            c += 1
    return c

def rhs_count(F, node, N):
    m, P, L = node["m"], node["Pceil"], node["L"]
    B = m * N - sum(P[j] for j in range(m)) - L
    assert B >= 0
    val = F.Q ** B
    for lam in node["sides"].values():
        val *= side_census(F, lam)
    return val, B

# ----------------------------------------------------------------------------
# Instances and checks
# ----------------------------------------------------------------------------

FAIL = 0

def check(name, cond, detail=""):
    global FAIL
    tag = "PASS" if cond else "FAIL"
    if not cond:
        FAIL += 1
    print(f"[{tag}] {name}" + (f"  ({detail})" if detail else ""))

def make_node(P, m, types):
    """Build a WF node from Pceil + per-side types; checks WF and [ENC]."""
    okc, L, lean_sides = lean_WF_data(P, m)
    H, onhull, verts, dsides = direct_polygon_data(P, m)
    check(f"ENC ceiled-consistency (P={P[:m+1]})", okc)
    check(f"ENC L agrees with direct hull (P={P[:m+1]})",
          L == sum(1 for j in range(m) if Fraction(P[j]) == H[j]),
          f"lean L={L}")
    check(f"ENC sides agree with direct hull (P={P[:m+1]})",
          set(lean_sides) == set(dsides) and
          all(lean_sides[s] == dsides[s][2] for s in dsides),
          f"lean={lean_sides} direct={{(u,l): deg}}={{{', '.join(f'{s}: {v[2]}' for s, v in dsides.items())}}}")
    check(f"ENC vertices agree with direct hull (P={P[:m+1]})",
          {j for j in range(m + 1) if lean_IsVertex(P, m, j)} == verts)
    assert set(types) == set(lean_sides), "types must be given for exactly the genuine sides"
    for s, lam in types.items():
        check(f"ENC side-type degree law at {s}",
              sum(dd * mm for dd, mm in lam) == lean_sides[s])
    return {"m": m, "Pceil": P, "L": L, "sides": types}

def law(name, F, p, N, Phi, node):
    lhs = lhs_count(F, p, N, Phi, node)
    rhs, B = rhs_count(F, node, N)
    check(f"LAW {name}", lhs == rhs, f"LHS={lhs} RHS={rhs} B={B} Q={F.Q} N={N}")
    return lhs

def main():
    print("=" * 78)
    print("A-C.2 certification: re-signed C.109 cell count law + mutations")
    print("=" * 78)

    for p in (2, 3):
        F = FQ(p)
        Phi = [0, 1]  # Phi = x, a degree-1 key over Z/p^N
        N = 5

        # I1: m=1, Pceil=(2,0), one side (2,1), linear type.  (The refutation
        # note's secondary example, REPAIRED: with the genuine side set the law
        # holds with L = 1.)
        n1 = make_node([2, 0], 1, {(2, 1): ((1, 1),)})
        check(f"I1 q={p}: WF L=1", n1["L"] == 1)
        lhs1 = law(f"I1 q={p} (m=1, steep side)", F, p, N, Phi, n1)

        # M2: same cell data but sides = EMPTY (the refutation note's claim,
        # VERIFIED): LHS with no side clause = Q^{N-2} - Q^{N-3}; no L works
        # for Q >= 3, exactly L = 1 works at Q = 2.
        n1e = {"m": 1, "Pceil": [2, 0], "L": None, "sides": {}}
        lhs_e = lhs_count(F, p, N, Phi, n1e)
        check(f"M2 q={p}: empty-sides LHS = Q^(N-3)(Q-1)",
              lhs_e == F.Q ** (N - 3) * (F.Q - 1), f"LHS={lhs_e}")
        matches = [L for L in range(0, 2 * N) if N - 2 - L >= 0 and F.Q ** (N - 2 - L) == lhs_e]
        if p == 2:
            check("M2 q=2: exactly L=1 accidentally matches", matches == [1])
        else:
            check(f"M2 q={p}: NO L matches (census factor is load-bearing)", matches == [])

        # M1: L off by one on I1 (the machine-refuted free-L defect): RHS moves,
        # LHS does not.
        bad = dict(n1); bad["L"] = n1["L"] + 1
        rhs_bad, _ = rhs_count(F, bad, N)
        check(f"M1 q={p}: L+1 mutation kills the law", rhs_bad != lhs1)

        # I2: m=2, Pceil=(2,1,0): one slope-1 side of residual degree 2 with an
        # INTERIOR lattice point.  All three quadratic types.
        for lam, nm in (
            (((1, 2),), "double root"),
            (((1, 1), (1, 1)), "two distinct roots"),
            (((2, 1),), "irreducible quadratic"),
        ):
            cen = side_census(F, lam)
            if cen == 0:
                print(f"[note] I2 q={p} type {lam} ({nm}): census 0, skipping law "
                      f"(empty on both sides; q=2 two-distinct-roots case)")
                nn = make_node([2, 1, 0], 2, {(1, 1): lam})
                lhs = lhs_count(F, p, N, Phi, nn)
                check(f"I2 q={p} {nm}: LHS also 0", lhs == 0)
                continue
            nn = make_node([2, 1, 0], 2, {(1, 1): lam})
            law(f"I2 q={p} ({nm})", F, p, N, Phi, nn)

        # M3a: OLD (exact-pin) cell semantics on I2: the pin at the INTERIOR
        # lattice point j=1 forces the residual's interior coefficient to be
        # nonzero, which the type census does not.  The killer type is
        # characteristic-dependent: at q=2 the double root (Y-c)^2 = Y^2+c^2
        # has interior coefficient -2c = 0 (old cell EMPTY); at q=3 the unique
        # two-distinct-roots residual (Y-1)(Y-2) has interior -(1+2) = 0.
        # NOTE (found by this script's first run): at q=3 the double-root type
        # has -2c != 0, so the old pin is IMPLIED by that type there — the old
        # semantics coincides with the law on single types by accident of the
        # characteristic; the defect is exactly that it smuggles a type-
        # dependent extra constraint into the polygon pin.
        killer = ((1, 2),) if p == 2 else ((1, 1), (1, 1))
        nn = make_node([2, 1, 0], 2, {(1, 1): killer})
        lhs_old = lhs_count(F, p, N, Phi, nn, semantics="old")
        rhs_dr, _ = rhs_count(F, nn, N)
        check(f"M3a q={p}: OLD cell EMPTY on the char-{p} killer type", lhs_old == 0,
              f"LHS_old={lhs_old}, RHS={rhs_dr}")
        check(f"M3a q={p}: OLD pin semantics kills the law", lhs_old != rhs_dr,
              f"LHS_old={lhs_old} RHS={rhs_dr}")

        # I3: m=2, Pceil=(1,1,0): ell=2 side, NON-lattice interior position.
        n3 = make_node([1, 1, 0], 2, {(1, 2): ((1, 1),)})
        check(f"I3 q={p}: WF L=1 (only j=0 lattice)", n3["L"] == 1)
        lhs3 = law(f"I3 q={p} (ell=2 side)", F, p, N, Phi, n3)
        # M3b: old semantics pins the non-lattice position exactly: kills it.
        lhs3_old = lhs_count(F, p, N, Phi, n3, semantics="old")
        check(f"M3b q={p}: OLD pin kills ell=2 law", lhs3_old != lhs3 and
              lhs3_old == F.Q ** (2 * N - 4) * (F.Q - 1) ** 2,
              f"LHS_old={lhs3_old} LHS_new={lhs3}")

        # I5: flat side (u=0): m=1, Pceil=(0,0).
        n5 = make_node([0, 0], 1, {(0, 1): ((1, 1),)})
        law(f"I5 q={p} (flat side)", F, p, N, Phi, n5)

        # I6: two sides sharing a vertex: Pceil=(3,1,0): sides (2,1),(1,1) --
        # the right-to-left sweep: NO extra unit factor at the shared vertex.
        n6 = make_node([3, 1, 0], 2, {(2, 1): ((1, 1),), (1, 1): ((1, 1),)})
        check(f"I6 q={p}: WF L=2", n6["L"] == 2)
        law(f"I6 q={p} (two sides, shared vertex)", F, p, N, Phi, n6)

    # I4: degree-2 key, Q = 4: Phi = x^2 + x + 1 over Z/2^N.
    F4 = FQ(2, modpoly=(1, 1))  # g = x^2 + x + 1
    p, N = 2, 4
    Phi = [1, 1, 1]
    n4 = make_node([1, 0], 1, {(1, 1): ((1, 1),)})
    law("I4 q=2 d=2 (Q=4)", F4, p, N, Phi, n4)

    # ------------------------------------------------------------------
    # [C111] the frozen arithmetic-shadow inequality is FALSE
    # ------------------------------------------------------------------
    def B(P, m, L, N):
        return m * N - sum(P[j] for j in range(m)) - L  # true integer here

    def D(m, s, N):
        return sum(max(N - ((m - j) * s + 1), 0) for j in range(m))

    N = 2
    # frozen-form counterexample (hvis holds; L free garbage): root and child
    # m=1, Pceil=(1,0), L=1; child s=0.
    SB = max(B([1, 0], 1, 1, N), 0) + max(B([1, 0], 1, 1, N), 0)
    SD = D(1, 0, N)
    check("C111 frozen refuted: sum D > sum B at N=2 two-node tree", SD > SB,
          f"sum D={SD} sum B={SB}")
    # WF-resistant: N=4, both nodes WF (Pceil=(N-1,0), L=1 correct), child s=0.
    N = 4
    okc, L, sides = lean_WF_data([N - 1, 0], 1)
    check("C111 WF-resistant: node IS HTNode.WF", okc and L == 1 and set(sides) == {(N - 1, 1)})
    SB = 2 * max(B([N - 1, 0], 1, 1, N), 0)
    SD = D(1, 0, N)
    check("C111 WF-resistant refutation: WF alone cannot rescue it", SD > SB,
          f"sum D={SD} sum B={SB}")
    # the A-C.2 re-signed form (per-node hypothesis => telescope) holds by
    # construction: hnode gives sum_children D <= B per node; summing over
    # nodes covers every non-root exactly once (parent unique).  Numeric spot:
    hnode_ok = D(1, 0, N) <= B([N - 1, 0], 1, 1, N)
    check("C111 re-signed form: counterexample violates the per-node hypothesis",
          not hnode_ok)

    # ------------------------------------------------------------------
    # [C114] the frozen ht_branch is FALSE at the formula level
    # ------------------------------------------------------------------
    # singleton tree, node m=0: stratum = the empty coefficient box, count 1;
    # htBranchCount = kappa * (empty census product) * Q^0 = kappa.
    for kappa in (1, 2):
        formula = kappa * 1 * 1
        stratum = 1
        check(f"C114 kappa={kappa}: stratum={stratum} vs formula={formula} "
              + ("(consistent)" if kappa == 1 else "(REFUTES the frozen axiom)"),
              (stratum == formula) == (kappa == 1))

    print("=" * 78)
    if FAIL:
        print(f"RESULT: {FAIL} FAILURES")
        return 1
    print("RESULT: ALL CHECKS PASS")
    return 0

if __name__ == "__main__":
    sys.exit(main())
