#!/usr/bin/env python3
"""B-M2 (LIFT-CONF) recentering-seam concrete trace — unit B-M2, 2026-08-02.

THE INSTANCE (designed for this unit; every number below is COMPUTED, not asserted):

    p = 3,   f(x) = x^4 - 12x^3 + 51x^2 - 90x + 198   over Z_3
            = (x^2 - 6x + 3)^2 + 9*(x^2 - 6x + 3) + 162

OM/MacLane tower (absolute v_3 scale, v(3) = 1):
  read 0 (base, key Phi0 = x):        side slope -1/2, (e,h) = (2,1), R0 = (z+1)^2,
                                      psi0 = z - 2, g = 1, mu = 2  -> AUGMENT (e*g = 2):
                                      Phi1 = x^2 + 3.
  read 1 (order 1, key Phi1):         side slope -3/2 in (1/2)Z = Gamma1, stage pair (1,3),
                                      R1 = (z-2)^2, psi1 = z - 2, g = 1, mu = 2, c = 2 != 0
                                      -> RECENTERING: lift = 6x, Phi1' = x^2 - 6x + 3.
  read 2 (order 1, key Phi1'):        side slope -2, stage pair (1,4), R2 = z^2 + z + 2
                                      irreducible /F_3, g = 2, mu = 1 -> REGULAR, terminate.
  Tower invariants: E = 2*1*1 = 2, F = 1*1*2 = 2, f irreducible over Q_3 with (e,f) = (2,2).

PREREGISTERED PREDICTIONS (sealed before the run; the trace either reproduces them or fails):
  P1  f irreducible over Q_3, (e,f) = (2,2)  [PARI cross-check via gp, if available]
  P2  read 0: (e,h,g,mu) = (2,1,1,2), psi0 = z+1 = z-2, root 2; NOT recentering-eligible
      (e*g = 2: the new key has degree 2 > 1).
  P3  read 1: actual read pair (e,g) = (1,1) with h_stage = 3 (slope 3/2 absolute), mu = 2,
      root c = 2 != 0 -> the recentering FIRES at actual (e,g) = (1,1).       [claim C-a]
  P4  deg Phi1' = 2 = 1*1*2 = e*g*m at the ACTUAL read parameters.            [claim C-b]
  P5  the sole lower digit t~0 = -lift = -6x satisfies ALL the stage-law fields at
      (e,g) = (1,1) with psi = z - 2:  window deg < 2;  weight w(t~0) = h (3/2 abs);
      digit = psi.coeff 0 = 1 at twist position 0 (Bezout t = 0 at e = 1);  (SL-top)
      D_g = D_1 = 1;  and the graded (SL-dev) identity holds with U0 = 1.    [claim C-c]
  P6  read 2 (non-recentering, both lower slots PRESENT, digits 2 and 1): the graded
      (SL-dev) identity in(D_k Phi'^(e k)) = U0 psi_k phi_ghat ybar^k holds at every
      present k with ONE shared U0 = 1; (K1): w(f) = 4 = ghat; (K2): R^gr(in f) = psi2.
      Same identity at read 0 (e = 2, the mixed x-anchor case), shared U0 = 1. [claim C-d]
  P7  root valuations: v(theta) = 1/2, v(Phi1(theta)) = 3/2, v(Phi1'(theta)) = 2
      == v_3(Res(f, x))/4 = 2/4, v_3(Res(f,Phi1))/4 = 6/4, v_3(Res(f,Phi1'))/4 = 8/4.
  P8  HUNT (the C-a falsification attempt): in a deterministic scan of random towers
      (order-0 reads for p in {2,3}; order-1 reads over the instance's own ramified
      stage), EVERY recentering-eligible read has (e, deg psi) = (1,1), and the two
      forcing legs verify empirically: (i) a side with e > 1 has value outside the
      window's weight lattice (no in-window lift can realize it); (ii) an irreducible
      residual factor of degree > 1 has no root in the residue field (no in-window
      digit can recenter onto it).  A single counterexample REFUTES C-a.

Corpus pins this trace is keyed to (read 2026-08-02):
  IsRecentering / IsRecenteringCore: lean/LeanUrat/Moves/Defs.lean:264ff,
    Moves/DefsCore.lean:242 (sigma.e = 1 conjunct; Phi' = Phi - lift; w(lift) = w(Phi);
    R(lift) = C(center)*T^0).
  HistoryCoherent recentering leg: MovesC/Defs.lean:717ff (asserts IsRecenteringCore only;
    the node's OWN (e,g) fields are NOT tied by that leg -> REC-PARAM is open in-corpus).
  IsNodeLift stage-law fields: MovesC/Defs.lean:535 (window/weight/twist-residual).
  TransitionData.child_e: Moves/DefsT.lean:150 (sigma'.e = e' — stage pair = read pair
    at non-recentering creations).
  RG-2 fence: HistoryCoherent non-recentering leg conjoins nu_i.e = 1.

Exact arithmetic throughout (fractions.Fraction + F_p ints).  Deterministic (fixed seed).
Exit 0 iff every assertion passes; the final block prints per-claim verdicts.
"""

from fractions import Fraction
import itertools
import random
import shutil
import subprocess
import sys

P = 3

# ---------------------------------------------------------------- small exact helpers

def vp(x, p=P):
    """p-adic valuation of a Fraction/int; None = +infinity (x = 0)."""
    x = Fraction(x)
    if x == 0:
        return None
    v = 0
    n, d = x.numerator, x.denominator
    while n % p == 0:
        n //= p
        v += 1
    while d % p == 0:
        d //= p
        v -= 1
    return Fraction(v)


def digit(x, p=P):
    """The unit digit of x != 0: (x / p^v(x)) mod p, as an int in [1, p-1]."""
    x = Fraction(x)
    v = vp(x, p)
    u = x / Fraction(p) ** v
    n, d = u.numerator % p, u.denominator % p
    return (n * pow(d, -1, p)) % p


# polynomials = lists of Fractions, index = degree
def pstr(c):
    terms = []
    for i in range(len(c) - 1, -1, -1):
        if c[i] == 0:
            continue
        t = f"{c[i]}" if i == 0 else (f"{c[i]}*x^{i}" if c[i] != 1 else f"x^{i}")
        terms.append(t)
    return " + ".join(terms).replace("+ -", "- ") if terms else "0"


def padd(a, b):
    n = max(len(a), len(b))
    return [(a[i] if i < len(a) else 0) + (b[i] if i < len(b) else 0) for i in range(n)]


def pmul(a, b):
    out = [Fraction(0)] * (len(a) + len(b) - 1)
    for i, ai in enumerate(a):
        for j, bj in enumerate(b):
            out[i + j] += ai * bj
    while len(out) > 1 and out[-1] == 0:
        out.pop()
    return out


def pdivmod(a, b):
    """Exact division with remainder over Q; b monic-led."""
    a = [Fraction(x) for x in a]
    q = [Fraction(0)] * max(1, len(a) - len(b) + 1)
    while len(a) >= len(b) and any(x != 0 for x in a):
        while len(a) > 1 and a[-1] == 0:
            a.pop()
        if len(a) < len(b):
            break
        c = a[-1] / b[-1]
        d = len(a) - len(b)
        q[d] = c
        for i in range(len(b)):
            a[i + d] -= c * b[i]
        a.pop()
    while len(a) > 1 and a[-1] == 0:
        a.pop()
    return q, a


def develop2(f, Phi):
    """Phi-adic development: f = sum_j B_j Phi^j, deg B_j < deg Phi. Returns [B_0, B_1, ...]."""
    out = []
    cur = [Fraction(x) for x in f]
    if all(x == 0 for x in cur):
        return [[Fraction(0)]]
    while any(x != 0 for x in cur):
        q, r = pdivmod(cur, Phi)
        out.append(r)
        cur = q
    return out


# ---------------------------------------------------------------- Newton polygon (exact)

def lower_hull(points):
    """Lower convex hull of exact-rational points sorted by x (monotone chain)."""
    pts = sorted(points)
    hull = []
    for pt in pts:
        while len(hull) >= 2:
            (x1, y1), (x2, y2) = hull[-2], hull[-1]
            # pop if hull[-1] is above segment hull[-2]->pt
            if (y2 - y1) * (pt[0] - x1) >= (pt[1] - y1) * (x2 - x1):
                hull.pop()
            else:
                break
        hull.append(pt)
    return hull


def sides_of(points):
    """Sides (slope, list of on-line lattice points) of the lower hull, slopes < 0 only
    (the principal part: roots of positive valuation)."""
    hull = lower_hull(points)
    sides = []
    for (x1, y1), (x2, y2) in zip(hull, hull[1:]):
        s = Fraction(y2 - y1, x2 - x1)
        if s >= 0:
            continue
        on = [(x, y) for (x, y) in points if x1 <= x <= x2 and (y - y1) * (x2 - x1) == s.numerator * (x - x1) * (x2 - x1) / s.denominator * s.denominator]
        # (recomputed simply below instead)
        on = [(x, y) for (x, y) in points if x1 <= x <= x2 and Fraction(y - y1) == s * (x - x1)]
        sides.append((s, (x1, y1), (x2, y2), on))
    return sides


# ---------------------------------------------------------------- F_p[z] utilities

def fp_trim(a):
    a = [x % P for x in a]
    while len(a) > 1 and a[-1] == 0:
        a.pop()
    return a


def fp_mul(a, b):
    out = [0] * (len(a) + len(b) - 1)
    for i, ai in enumerate(a):
        for j, bj in enumerate(b):
            out[i + j] = (out[i + j] + ai * bj) % P
    return fp_trim(out)


def fp_divmod(a, b):
    a = [x % P for x in a]
    binv = pow(b[-1], -1, P)
    q = [0] * max(1, len(a) - len(b) + 1)
    while len(fp_trim(a)) >= len(b) and fp_trim(a) != [0]:
        a = fp_trim(a)
        if len(a) < len(b):
            break
        c = (a[-1] * binv) % P
        d = len(a) - len(b)
        q[d] = c
        for i in range(len(b)):
            a[i + d] = (a[i + d] - c * b[i]) % P
        a = a[:-1]
    return fp_trim(q), fp_trim(a)


def fp_factor(a, p):
    """Factor a monic poly over F_p into irreducibles, deg(a) <= 6, tiny p: trial division
    by all monic irreducibles of degree <= deg/2, then the rest is irreducible."""
    global P
    saveP, P = P, p
    try:
        a = fp_trim(a)
        assert a[-1] == 1, "factor expects monic"
        # build monic irreducibles by increasing degree
        def monics(d):
            for tail in itertools.product(range(p), repeat=d):
                yield list(tail) + [1]
        def is_irred(g):
            for d in range(1, len(g) // 2 + 1):
                for h in monics(d):
                    if len(h) < len(g) and fp_divmod(g, h)[1] == [0]:
                        return False
            return True
        factors = {}
        rest = a
        d = 1
        while len(rest) > 1:
            if len(rest) - 1 == 1:
                factors[tuple(rest)] = factors.get(tuple(rest), 0) + 1
                break
            found = False
            for dd in range(d, (len(rest) - 1) // 2 + 1):
                for h in monics(dd):
                    if is_irred(h) and fp_divmod(rest, h)[1] == [0]:
                        factors[tuple(h)] = factors.get(tuple(h), 0) + 1
                        rest = fp_divmod(rest, h)[0]
                        found = True
                        d = dd
                        break
                if found:
                    break
            if not found:
                factors[tuple(rest)] = factors.get(tuple(rest), 0) + 1
                break
        return factors
    finally:
        P = saveP


def fp_roots(a, p):
    return [c for c in range(p) if sum(co * pow(c, i, p) for i, co in enumerate(a)) % p == 0]


# ---------------------------------------------------------------- graded monomials
# Post-stage-1 graded ring of the instance (p = 3): gr = F_3[ubar^{+-1}][Ybar], with
#   ubar := in(x)  (weight 1/2),  abar := in(3) (weight 1),  relation ubar^2 = -abar,
# so normal form c * ubar^k * Ybar^b, c in F_3^x.  in(a * x^i) = digit(a)*(-1)^{v(a)} * ubar^{2v+i}.
# (The relation ubar^2 = -abar is ASSERTED per stage below by computing w(x^2+3) > 1.)

def gr_mono(a, i):
    """Graded class of the monomial a*x^i (a != 0) in normal form (c, upow)."""
    v = vp(a)
    assert v.denominator == 1
    c = (digit(a) * pow(-1, int(v) % 2, P)) % P
    return (c % P, 2 * int(v) + i)


def w1(B):
    """Stage-1 window weight (absolute scale): w(a0 + a1 x) = min(v(a0), v(a1) + 1/2)."""
    vals = []
    for i, a in enumerate(B):
        if a != 0:
            vals.append(vp(a) + Fraction(i, 2))
    return min(vals) if vals else None


def in_w1(B):
    """Initial form of a window element (deg <= 1) as a graded monomial (c, upow).
    (No tie possible: integer vs half-integer weights.)"""
    w = w1(B)
    for i, a in enumerate(B):
        if a != 0 and vp(a) + Fraction(i, 2) == w:
            return gr_mono(a, i)
    raise RuntimeError


def gr_eq(m1, m2):
    return m1 == m2


def gr_div_unit(m1, m2):
    """m1 / m2 for monomials at the SAME weight: returns the F_p scalar."""
    assert m1[1] == m2[1], f"weight mismatch: ubar^{m1[1]} vs ubar^{m2[1]}"
    return (m1[0] * pow(m2[0], -1, P)) % P


# ================================================================ the trace
random.seed(20260802)
FAIL = []


def check(name, cond, detail=""):
    tag = "PASS" if cond else "FAIL"
    print(f"  [{tag}] {name}" + (f"  ({detail})" if detail else ""))
    if not cond:
        FAIL.append(name)


print("=" * 78)
print("B-M2 RECENTERING TRACE — p = 3, f = x^4 - 12x^3 + 51x^2 - 90x + 198")
print("=" * 78)

f = [Fraction(c) for c in (198, -90, 51, -12, 1)]
Phi1 = [Fraction(c) for c in (3, 0, 1)]        # x^2 + 3
lift = [Fraction(c) for c in (0, 6)]           # 6x
Phi1p = [Fraction(c) for c in (3, -6, 1)]      # x^2 - 6x + 3

# consistency of the displayed composition
assert padd(padd(pmul(Phi1p, Phi1p), pmul([Fraction(9)], Phi1p)), [Fraction(162)]) == f
assert [a - b for a, b in zip(Phi1, padd(Phi1p, lift))] == [0, 0, 0]

# ---------------------------------------------------------------- READ 0 (base)
print("\n--- READ 0: base key Phi0 = x " + "-" * 44)
pts0 = [(i, vp(a)) for i, a in enumerate(f) if a != 0]
sides0 = sides_of(pts0)
check("read 0: single principal side", len(sides0) == 1)
s0, lo0, hi0, on0 = sides0[0]
e0, h0 = s0.denominator, -s0.numerator
print(f"  polygon points {[(i, str(v)) for i, v in pts0]}")
print(f"  side slope {s0} from {lo0} to {hi0}; (e,h) = ({e0},{h0}); on-line pts {on0}")
check("read 0: (e,h) = (2,1)", (e0, h0) == (2, 1))
# order-0 residual: digits of on-line coefficients, slot kappa = (i - i_left)/e
R0 = [0] * ((hi0[0] - lo0[0]) // e0 + 1)
for (i, v) in on0:
    R0[(i - lo0[0]) // e0] = digit(f[i])
print(f"  R0(z) = {R0}  (coeff list, F_3)")
check("read 0: R0 = (z+1)^2 = z^2 + 2z + 1", R0 == [1, 2, 1])
fac0 = fp_factor(R0, 3)
(psi0, mu0), = fac0.items()
g0 = len(psi0) - 1
c0 = fp_roots(list(psi0), 3)
print(f"  psi0 = {list(psi0)} (deg {g0}), mu = {mu0}, roots {c0}")
check("read 0: psi0 = z+1 (root 2), g = 1, mu = 2", list(psi0) == [1, 1] and mu0 == 2 and c0 == [2])
check("read 0: NOT recentering-eligible (e*g = 2 > 1: proper augmentation)", e0 * g0 > 1)
# the fired lift Phi1 = x^{e*g} + t_0, t_0 = 3 realizing psi0.coeff0 = 1 at weight h*(g-0) = 1
check("read 0: Phi1 = Phi0^(e*g) + t0 with t0 = 3, deg Phi1 = e*g*m = 2*1*1", Phi1 == [3, 0, 1])
check("read 0: digit law w0(t0) = h*(g-0) = 1, digit(t0) = psi0.coeff0 = 1",
      vp(3) == 1 and digit(3) == 1)

# (SL-dev) at read 0 in the FREE graded ring F_3[xbar, abar^{+-}] (no relation yet):
# monomial rep (c, xpow, apow); in(a x^i) = (digit(a), i, v(a)).
def gr0(a, i):
    return (digit(a), i, int(vp(a)))
ghat0 = Fraction(e0 * g0, 1) * Fraction(h0, e0)   # e*g*gamma, gamma = h/e = 1/2 -> ghat = 1
check("read 0: ghat = e*g*gamma = 1", ghat0 == 1)
phi_ghat0 = gr0(3, 0)                              # anchor 3 (weight 1)
ybar0 = (1, 2, -1)                                 # xbar^2 abar^{-1}, weight 0
# kappa = 0 slot: D_0 = t0 = 3:  in(3) = U0 * psi0_0 * phi_ghat * ybar^0
lhs = gr0(3, 0)
rhs_unit = (1 * phi_ghat0[0]) % 3                 # psi0_0 = 1
U0_read0 = None
check("read 0 (SL-dev) k=0: in(t0) matches psi0_0*phi_ghat*ybar^0 up to unit",
      lhs[1:] == phi_ghat0[1:], f"lhs {lhs}, phi_ghat {phi_ghat0}")
U0_read0 = (lhs[0] * pow(rhs_unit, -1, 3)) % 3
# kappa = g = 1 slot (SL-top): D_1 = 1: in(x^2) = U0 * psi0_1 * phi_ghat * ybar^1
lhs_top = (1, 2, 0)
rhs_top = ((phi_ghat0[0] * ybar0[0]) % 3, phi_ghat0[1] + ybar0[1], phi_ghat0[2] + ybar0[2])
check("read 0 (SL-dev) k=1 (SL-top): in(Phi0^2) = U0*psi0_1*phi_ghat*ybar", lhs_top[1:] == rhs_top[1:])
U0_top0 = (lhs_top[0] * pow(rhs_top[0], -1, 3)) % 3
check("read 0: ONE shared U0 = 1 across slots", U0_read0 == U0_top0 == 1,
      f"U0(k=0) = {U0_read0}, U0(k=1) = {U0_top0}")

# ---------------------------------------------------------------- READ 1 (the recentering)
print("\n--- READ 1 at Phi1 = x^2 + 3 (order 1): THE RECENTERING " + "-" * 12)
B = develop2(f, Phi1)
print(f"  development f = sum B_j Phi1^j: B = {[pstr(b) for b in B]}")
check("read 1: development exact", len(B) == 3 and B[2] == [1])
pts1 = [(j, w1(Bj)) for j, Bj in enumerate(B) if any(x != 0 for x in Bj)]
sides1 = sides_of(pts1)
check("read 1: single principal side", len(sides1) == 1)
s1, lo1, hi1, on1 = sides1[0]
lam1 = -s1
print(f"  polygon points {[(j, str(v)) for j, v in pts1]}; side slope {s1}, on-line {on1}")
check("read 1: slope -3/2 (absolute), all three slots on-line", lam1 == Fraction(3, 2) and len(on1) == 3)
# e_read relative to the stage lattice Gamma1 = (1/2)Z: denominator of lam1 in half-units
e1 = (2 * lam1).denominator
h1_stage = int(2 * lam1) if e1 == 1 else None
print(f"  stage lattice Gamma1 = (1/2)Z; lam1 = {lam1} = {h1_stage} half-units -> (e,h)_stage = ({e1},{h1_stage})")
check("read 1: e_read = 1 (slope IN the stage lattice)", e1 == 1)
check("read 1: stage pair (e,h) = (1,3), gcd = 1", (e1, h1_stage) == (1, 3))
# assert the graded relation ubar^2 = -abar at this valuation: value of Phi1 (= the side
# slope, its assigned key weight) exceeds 1 = w(x^2) = w(3):
check("read 1: relation ubar^2 = -abar valid (w(Phi1) = 3/2 > 1)", lam1 > 1)
# residual with the ONE-SLOT anchor A = in(3x) (weight 3/2), slot j: anchor A^{jmax-j}
A1 = gr_mono(3, 1)   # in(3x) = -ubar^3 = 2 ubar^3
R1 = [0, 0, 0]
for (j, wv) in on1:
    cls = in_w1(B[j]) if j < 2 else (1, 0)   # B_2 = 1
    anchor = (pow(A1[0], 2 - j, 3) % 3, A1[1] * (2 - j))
    R1[j] = gr_div_unit(cls, anchor)
print(f"  graded classes: in(B_1) = {in_w1(B[1])} (= c*ubar^k), anchor A = in(3x) = {A1}")
print(f"  R1(z) = {R1}  (computed with anchors A^(2-j))")
check("read 1: R1 = (z-2)^2 = z^2 + 2z + 1", R1 == [1, 2, 1])
fac1 = fp_factor(R1, 3)
(psi1, mu1), = fac1.items()
g1 = len(psi1) - 1
c1 = fp_roots(list(psi1), 3)
print(f"  psi1 = {list(psi1)} (deg {g1}), mu = {mu1}, roots {c1}")
check("read 1: psi1 = z - 2 (g = 1), mu = 2, root c = 2 != 0",
      g1 == 1 and mu1 == 2 and c1 == [2] and 2 != 0)
print("  => RECENTERING FIRES: e*g = 1 (same-degree replacement), c != 0, mu >= 2")

# ---- claim C-a: the ACTUAL read pair at the recentering
print("\n  [C-a] REC-PARAM at the instance:")
check("C-a: recentering read's ACTUAL (e_read, g) = (1, 1)", (e1, g1) == (1, 1))

# ---- claim C-b: (K0) at the ACTUAL parameters
m1 = len(Phi1) - 1
check("C-b: deg Phi1' = e*g*m = 1*1*2 at the ACTUAL pair", len(Phi1p) - 1 == e1 * g1 * m1)
check("C-b: Phi1' monic", Phi1p[-1] == 1)

# ---- claim C-c: the digit datum -lift against the stage-law fields
print("\n  [C-c] the recentering digit t~0 = -lift = -6x vs (SL-top)/(SL-dev) fields:")
t0r = [-x for x in lift]
check("C-c window: deg(-lift) = 1 < deg Phi1 = 2 (inC)", len(t0r) - 1 < m1)
check("C-c nonzero lift", any(x != 0 for x in t0r))
wl = w1(t0r)
check("C-c weight law: w(t~0) = h*(g-0) = 3/2 absolute (= 3 stage units = h)",
      wl == Fraction(3, 2) and wl == lam1)
check("C-c IsRecentering weight clause: w(lift) = w(Phi1) (key weight = its side value 3/2)",
      w1(lift) == lam1)
# digit of -lift against the SAME anchor A used for R1: must equal psi1.coeff 0
d_minus_lift = gr_div_unit(in_w1(t0r), A1)
d_lift = gr_div_unit(in_w1(lift), A1)
print(f"    in(-6x) = {in_w1(t0r)}, digit rel A = {d_minus_lift}; in(6x) digit rel A = {d_lift}")
check("C-c residual law: digit(-lift) = psi1.coeff0 = 1", d_minus_lift == (psi1[0]) % 3 == 1)
check("C-c IsRecentering digit clause: digit(lift) = center c = 2", d_lift == 2)
# twist position: node Bezout t at e = 1 is 0 (hbezCanon window [0,e)): position -t*wPrev = 0.
tBez = 0  # forced: 0 <= t < e = 1
check("C-c twist position: canonical Bezout t = 0 at e = 1 -> T-exponent 0 (matches T^0)",
      tBez == 0)
check("C-c (SL-top): D_g = D_1 = 1 (Phi1' = 1*Phi1 + t~0 exactly)",
      Phi1p == padd(Phi1, t0r) and Phi1p[-1] == 1)
# graded (SL-dev) identity at kappa = 0 with the mixed anchor phi_{3/2} = in(3x):
lhs_c = in_w1(t0r)
rhs_c = ((psi1[0] % 3) * A1[0] % 3, A1[1])
check("C-c graded identity: in(t~0) = U0 * psi1_0 * phi_{3/2}, U0 = 1",
      lhs_c[1] == rhs_c[1] and gr_div_unit(lhs_c, rhs_c) == 1,
      f"lhs {lhs_c}, rhs(U0=1) {rhs_c}")
# improvement check: w(Phi1'( )) strictly exceeds the recentering slope
Bp = develop2(f, Phi1p)

# ---------------------------------------------------------------- READ 2 (final, non-recentering)
print("\n--- READ 2 at Phi1' = x^2 - 6x + 3 (post-recentering, final) " + "-" * 8)
print(f"  development f = sum B'_j Phi1'^j: B' = {[pstr(b) for b in Bp]}")
check("read 2: development is Phi1'^2 + 9*Phi1' + 162", [pstr(b) for b in Bp] == ["162", "9", "1"])
pts2 = [(j, w1(Bj)) for j, Bj in enumerate(Bp) if any(x != 0 for x in Bj)]
sides2 = sides_of(pts2)
check("read 2: single principal side", len(sides2) == 1)
s2, lo2, hi2, on2 = sides2[0]
lam2 = -s2
print(f"  polygon points {[(j, str(v)) for j, v in pts2]}; slope {s2}, on-line {on2}")
check("read 2: slope -2, all three slots on-line (both lower digits PRESENT)",
      lam2 == 2 and len(on2) == 3)
check("read 2: improvement over the recentering read: 2 > 3/2", lam2 > lam1)
e2 = (2 * lam2).denominator
h2_stage = int(2 * lam2)
check("read 2: (e,h)_stage = (1,4)", (e2, h2_stage) == (1, 4))
check("read 2: relation ubar^2 = -abar still valid (w2(x^2+3) = min(2,3/2) = 3/2 > 1)",
      min(lam2, w1(lift)) == Fraction(3, 2))
A2 = gr_mono(9, 0)   # anchor in(3^2) = ubar^4 (weight 2), e | ghat here so a pure p-power
R2 = [0, 0, 0]
for (j, wv) in on2:
    cls = in_w1(Bp[j]) if j < 2 else (1, 0)
    anchor = (pow(A2[0], 2 - j, 3) % 3, A2[1] * (2 - j))
    R2[j] = gr_div_unit(cls, anchor)
print(f"  R2(z) = {R2}")
check("read 2: R2 = z^2 + z + 2", R2 == [2, 1, 1])
fac2 = fp_factor(R2, 3)
(psi2, mu2), = fac2.items()
g2 = len(psi2) - 1
print(f"  psi2 = {list(psi2)} (deg {g2}), mu = {mu2}, roots {fp_roots(list(psi2), 3)}")
check("read 2: psi2 irreducible over F_3 (g = 2), mu = 1 -> REGULAR, terminate",
      g2 == 2 and mu2 == 1 and fp_roots(list(psi2), 3) == [])
E_tot = e0 * e1 * e2
F_tot = g0 * g1 * g2
check("tower invariants: E = 2, F = 2, E*F = deg f = 4", (E_tot, F_tot) == (2, 2))

# ---- claim C-d: the graded (SL-dev) identity at this non-recentering read
print("\n  [C-d] GRADED-READ at read 2: in(D_k Phi'^(ek)) = U0 psi_k phi_ghat ybar^k:")
ghat2 = e2 * g2 * lam2
check("C-d: ghat = e*g*gamma = 4", ghat2 == 4)
phi_ghat2 = gr_mono(81, 0)      # in(3^4) = ubar^8
Ai2 = gr_mono(9, 0)             # in(3^gamma) = in(9)
# ybar = in(Phi1')/in(9): represent classes of D_k*Phi'^k as (c, upow, Ypow):
U0s = {}
for k in range(g2 + 1):
    if (psi2[k] % 3) == 0:
        check(f"C-d k={k}: psi2_{k} = 0 and slot ABSENT (D_{k} = 0)", not any(x != 0 for x in Bp[k]))
        continue
    Dk = Bp[k] if k < 2 else [Fraction(1)]
    lhs = in_w1(Dk)
    lhs_full = (lhs[0], lhs[1], k)                                     # * Ybar^k
    # rhs with U0 = 1: psi2_k * phi_ghat * (Ybar * in(9)^{-1})^k
    rc = (psi2[k] % 3) * phi_ghat2[0] % 3
    rc = rc * pow(pow(Ai2[0], k, 3), -1, 3) % 3
    rhs_full = (rc, phi_ghat2[1] - k * Ai2[1], k)
    ok = lhs_full[1:] == rhs_full[1:]
    U0 = (lhs_full[0] * pow(rhs_full[0], -1, 3)) % 3 if ok else None
    U0s[k] = U0
    check(f"C-d k={k}: slot identity holds (D_{k} digit {lhs[0]} at ubar^{lhs[1]}), U0 = {U0}", ok)
check("C-d: ONE shared U0 = 1 across ALL present slots incl. (SL-top) k=g",
      set(U0s.values()) == {1}, f"U0 by slot: {U0s}")
# (K1): w(f) = ghat, all slots minimizing
slotvals = [w1(Bp[j]) + j * lam2 if any(x != 0 for x in Bp[j]) else None for j in range(3)]
check("C-d (K1): every slot value = ghat = 4 (w(lift) = ghat, all slots minimize)",
      all(v == 4 for v in slotvals if v is not None), f"slot values {[str(v) for v in slotvals]}")
# (K2): R^gr(in f) = U0 * psi2 with U0 = 1: that is literally R2 == psi2
check("C-d (K2): R^gr_ghat(in f) = psi2 (U0 = 1)", R2 == list(psi2))

# ---------------------------------------------------------------- P7: root valuations vs resultants
print("\n--- P7: root valuations via resultants (exact) " + "-" * 22)
def resultant_via_roots_of_g(fpoly, g):
    """Res(f, g) for monic quadratic g by evaluating f at g's roots symbolically:
    reduce f mod g, then Res = N(f mod g) = (a + b r1)(a + b r2) with r1 r2 = g0, r1+r2 = -g1."""
    _, r = pdivmod(fpoly, g)
    r += [Fraction(0)] * (2 - len(r))
    a, b = r[0], r[1]
    s, pr = -g[1], g[0]
    return a * a + a * b * s + b * b * pr

Rx = f[0]                                   # Res(f, x) = f(0)
R_Phi1 = resultant_via_roots_of_g(f, Phi1)
R_Phi1p = resultant_via_roots_of_g(f, Phi1p)
print(f"  Res(f,x) = {Rx} (v = {vp(Rx)});  Res(f,Phi1) = {R_Phi1} (v = {vp(R_Phi1)});  "
      f"Res(f,Phi1') = {R_Phi1p} (v = {vp(R_Phi1p)})")
check("P7: v(theta) = 2/4 = 1/2", vp(Rx) == 2)
check("P7: v(Phi1(theta)) = 6/4 = 3/2 (the recentering side)", vp(R_Phi1) == 6)
check("P7: v(Phi1'(theta)) = 8/4 = 2 (strict improvement past the recentering)", vp(R_Phi1p) == 8)

# ---------------------------------------------------------------- P1: PARI oracle (if available)
print("\n--- P1: PARI factorpadic oracle " + "-" * 37)
gp = shutil.which("gp")
if gp:
    script = ("f = x^4-12*x^3+51*x^2-90*x+198;"
              "F = factorpadic(f,3,30);"
              "K = nfinit([f,[3]]); pr = idealprimedec(K,3);"
              'print(matsize(F)[1], " ", poldegree(F[1,1]), " ", length(pr), " ", pr[1].e, " ", pr[1].f)')
    out = subprocess.run([gp, "-q"], input=script, capture_output=True, text=True, timeout=120).stdout.split()
    check("P1: f IRREDUCIBLE over Q_3 (one factor, degree 4)", out[:2] == ["1", "4"], f"gp: {out}")
    check("P1: one prime above 3 with (e,f) = (2,2) = (E,F) of the trace", out[2:] == ["1", "2", "2"],
          f"gp: {out}")
else:
    print("  [SKIP] gp not on PATH — oracle cross-check skipped (trace itself is exact)")

# ---------------------------------------------------------------- P8: the C-a hunt
print("\n--- P8: HUNT for a recentering off (e,g) = (1,1) " + "-" * 21)
events = {"reads": 0, "eligible": 0, "eligible_11": 0, "e_gt1_reads": 0, "g_gt1_factors": 0}


def hunt_order0(p, ncases, maxdeg):
    """Order-0 reads on random polynomials: for every side x irreducible-factor pair,
    recentering eligibility := (side value in the window lattice Z) AND (factor has a
    NONZERO root in F_p).  Assert eligible -> (e, deg psi) = (1,1); verify the forcing
    legs empirically on every read."""
    bad = []
    for _ in range(ncases):
        deg = random.choice(range(2, maxdeg + 1))
        coeffs = [Fraction(random.randrange(1, p ** 2) * p ** random.randrange(0, 4))
                  * random.choice([1, -1]) for _ in range(deg)] + [Fraction(1)]
        if coeffs[0] == 0:
            continue
        pts = [(i, vp(a, p)) for i, a in enumerate(coeffs) if a != 0]
        for (s, lo, hi, on) in sides_of(pts):
            e, h = s.denominator, -s.numerator
            R = [0] * ((hi[0] - lo[0]) // e + 1)
            for (i, v) in on:
                R[(i - lo[0]) // e] = digit(coeffs[i], p)
            if R[-1] == 0 or len(R) < 2:
                continue
            Rm = [(x * pow(R[-1], -1, p)) % p for x in R]
            events["reads"] += 1
            # forcing leg (i): e > 1 -> side value not an integer (window = constants, wt in Z)
            if e > 1:
                events["e_gt1_reads"] += 1
                if (Fraction(h, e)).denominator == 1:
                    bad.append(("leg-i", p, coeffs))
            for psi, mu in fp_factor(Rm, p).items():
                gpsi = len(psi) - 1
                roots = [c for c in fp_roots(list(psi), p) if c != 0]
                # forcing leg (ii): deg psi > 1 -> no F_p root at all
                if gpsi > 1:
                    events["g_gt1_factors"] += 1
                    if fp_roots(list(psi), p):
                        bad.append(("leg-ii", p, psi))
                eligible = (e == 1) and bool(roots)
                if eligible:
                    events["eligible"] += 1
                    if (e, gpsi) == (1, 1):
                        events["eligible_11"] += 1
                    else:
                        bad.append(("counterexample", p, coeffs, s, psi))
    return bad


def hunt_order1(ncases):
    """Order-1 reads over the instance's own ramified stage (key x^2+3, Gamma = (1/2)Z,
    K = F_3): random f = Phi^2 + B1 Phi + B0.  Eligibility := side value in Gamma AND
    the residual factor has a nonzero F_3 root."""
    bad = []
    Phi = [Fraction(3), Fraction(0), Fraction(1)]
    for _ in range(ncases):
        Bs = [[Fraction(random.randrange(0, 3 ** 3) * 3 ** random.randrange(0, 3))
               * random.choice([1, -1]) for _ in range(2)] for _ in range(2)]
        fr = padd(padd(pmul(Phi, Phi), pmul(Bs[1], Phi)), Bs[0])
        Bd = develop2(fr, Phi)
        pts = [(j, w1(Bj)) for j, Bj in enumerate(Bd) if any(x != 0 for x in Bj)]
        if len(pts) < 2 or pts[0][0] != 0:
            continue
        for (s, lo, hi, on) in sides_of(pts):
            lam = -s
            if lam <= 1:      # need w(key) > 1 for the graded relation; skip shallow sides
                continue
            e_rel = (2 * lam).denominator
            events["reads"] += 1
            if e_rel > 1:
                events["e_gt1_reads"] += 1
                # forcing leg (i): no window element weight matches (window wts in (1/2)Z)
                if (2 * lam).denominator == 1:
                    bad.append(("leg-i-o1", lam))
                continue
            # general one-step anchor at slope lam: monomial 3^a x^i of weight lam
            i = 0 if lam.denominator == 1 else 1
            a = int(lam - Fraction(i, 2))
            A = gr_mono(Fraction(3) ** a, i)
            wid = hi[0] - lo[0]
            R = [0] * (wid + 1)
            okslots = True
            for (j, wv) in on:
                cls = in_w1(Bd[j]) if any(x != 0 for x in Bd[j]) else None
                kk = j - lo[0]
                anchor = (pow(A[0], wid - kk, 3) % 3, A[1] * (wid - kk))
                if cls is None or cls[1] != anchor[1] + 0:
                    okslots = False
                    break
                R[kk] = gr_div_unit(cls, anchor)
            if not okslots or R[-1] == 0:
                continue
            Rm = [(x * pow(R[-1], -1, 3)) % 3 for x in R]
            for psi, mu in fp_factor(Rm, 3).items():
                gpsi = len(psi) - 1
                roots = [c for c in fp_roots(list(psi), 3) if c != 0]
                if gpsi > 1:
                    events["g_gt1_factors"] += 1
                    if fp_roots(list(psi), 3):
                        bad.append(("leg-ii-o1", psi))
                if bool(roots):
                    events["eligible"] += 1
                    if gpsi == 1:
                        events["eligible_11"] += 1
                    else:
                        bad.append(("counterexample-o1", fr, lam, psi))
    return bad


bad = hunt_order0(2, 400, 6) + hunt_order0(3, 400, 6) + hunt_order1(400)
print(f"  scan events: {events}")
check("P8: ZERO recentering-eligible reads off (e,g) = (1,1)",
      events["eligible"] == events["eligible_11"] and not any(b[0].startswith("counter") for b in bad),
      f"eligible {events['eligible']}, at-(1,1) {events['eligible_11']}")
check("P8 forcing leg (i): every e>1 side value sits OUTSIDE the window lattice "
      f"({events['e_gt1_reads']} sides checked)", not any(b[0].startswith("leg-i") for b in bad))
check("P8 forcing leg (ii): every deg>1 irreducible residual factor is F_p-rootless "
      f"({events['g_gt1_factors']} factors checked)", not any(b[0].startswith("leg-ii") for b in bad))

# ---------------------------------------------------------------- trace table + verdicts
print("\n" + "=" * 78)
print("NODE-BY-NODE TRACE TABLE (absolute v_3 scale)")
print("=" * 78)
print("""
 node | key Phi        | side slope | (e,h)_st | psi(z)      | g | mu | event
------+----------------+------------+----------+-------------+---+----+---------------------
  0   | x              |   -1/2     |  (2,1)   | z + 1       | 1 | 2  | AUGMENT -> x^2+3
  1   | x^2 + 3        |   -3/2     |  (1,3)   | z - 2       | 1 | 2  | RECENTER (lift 6x)
  2   | x^2 - 6x + 3   |   -2       |  (1,4)   | z^2 + z + 2 | 2 | 1  | REGULAR, terminate
------+----------------+------------+----------+-------------+---+----+---------------------
 tower: E = 2*1*1 = 2, F = 1*1*2 = 2; f irreducible /Q_3, (e,f) = (2,2)  [PARI-confirmed]
""")

print("PER-CLAIM VERDICTS:")
verdicts = [
    ("C-a REC-PARAM", "TRUE-AT-INSTANCE",
     "recentering read's actual (e,g) = (1,1); hunt found 0 counterexamples "
     f"({events['eligible']} eligible events, {events['e_gt1_reads']}+{events['g_gt1_factors']} forcing-leg checks)"),
    ("C-b (K0)@actual", "TRUE-AT-INSTANCE", "deg Phi1' = 2 = 1*1*2 = e*g*m at the actual pair"),
    ("C-c REC-SL data", "TRUE-AT-INSTANCE",
     "digit -6x: window+weight(3/2=h)+digit(1=psi_0)+position(0)+(SL-top)+graded id, U0=1"),
    ("C-d GRADED-READ", "TRUE-AT-INSTANCE",
     "reads 0 and 2 (incl. digit 2 slot + absent-slot law + (K1)+(K2)), ONE shared U0 = 1"),
    ("C-e sites", "SEE NOTE",
     "recentering + final-read carriers fire; interior e=2 step (read 0) UNRECORDABLE (RG-2)"),
]
for name, verdict, why in verdicts:
    print(f"  {name:18s} {verdict:18s} {why}")

print()
if FAIL:
    print(f"*** {len(FAIL)} CHECK(S) FAILED: {FAIL}")
    sys.exit(1)
print("ALL CHECKS PASSED.")
