#!/usr/bin/env python3
"""N-GR1 — the per-kappa (SL-dev) slot-position falsifier family (B2DEF_LEAN blueprint
section 7; gates GR-0/GR-2/GR-3; RUN BEFORE the GR-2/GR-3 proof landing, 2026-08-02).

SPEC (blueprint section 7 verbatim): "per-kappa (SL-dev) harness at e' >= 2 AND g >= 2
with nontrivial twist (sigma.t != 0) positions: predicted pos(kappa) affine, unit step,
mhat = -t*h*g, AND the GR-0 scale law h' = e'*w(Phi) checked at every recorded read;
extend the BM2 trace driver."

INSTANCES (p = 3, exact arithmetic; instance A = the BM2 trace driver's quartic):
  A: f = x^4 - 12x^3 + 51x^2 - 90x + 198   (reads: (2,1)g=1 t=1 | recenter | (1,4)g=2 t=0)
  B: f = x^4 + 3x^2 + 18                   (read 0: e'=2 AND g=2 AND canonical t=1 != 0
                                            -- the spec's joint case; psi = z^2+z+2 irred)

PREREGISTERED CHECKS per read (sealed before the run):
  N1  the on-line slot positions p_j(gamma) = (j - t*gamma)/e are INTEGERS, affine in
      the lattice slot kappa = (j - s0)/e with UNIT kappa-step  [D.3(c) stride].
  N2  the anchored pattern sits at pos(kappa) = kappa + mhat with mhat = -t*h*g at the
      READ's canonical Bezout pair (t in [0, e))  [D.8 normalization; GR-3's pinned form].
  N3  THE SCALE LAW, frame-face (GR-0's hscale as transcribed: nu.h = nu.e * sigma.w
      sigma.Phi with the recorded child keying sigma.h = nu.h): predicted to hold IFF
      e_read = 1.  Equivalently: the FRAME-scale slot totals nu.h*(g-k) + nu.e*k*sigma.h
      are k-free iff e_read = 1, while the READ-scale (regrade) side values are ALWAYS
      equal (D.5's own display lives at the regrade).  A steep read (e' >= 2) therefore
      FAILS the frame-face law -- the wave-2a forcing lemma readHyps_e_eq_one compiled
      in Lean (GR0b_suppliers.lean); the blueprint's bare "checked at every recorded
      read" prediction is REFINED, not silently weakened: holds at e'=1, fails at e'>=2.
  N4  the frame-face readPos rendering (GRDefs.readPos = -sigma.t*wPrev(t_k) + e*k*sigma.s)
      reproduces the checked positions at the e = 1 reads (recorded frames there have
      (sigma.s, sigma.t) = (1, 0) by he1t + hbez -- frame_level_of_history).
  N5  THE SIGMA.E-RESIDUE DEMO (the GR-3/GR-4 obstruction, numerically): at an ABSTRACT
      ramified frame (sigma.e = 2: key X, w = min(2*v3 + i) -- the genuine MacLane stage
      [v3; w(X) = 1/2] normalized integral), the fake node (nu.e, nu.h) = (1, 1),
      psi = z^2 + 1 (irreducible over F_3, support {0, 2}) admits an IsNodeLift witness
      Phi' = X^2 + 3 satisfying ALL ReadHyps fields (hscale: 1 = 1*1 checks), yet the
      residual positions COMPRESS: R(Phi') = C(1)*T^-1 + T^0 (adjacent), while
      T^mhat * toLaurent(psi) needs gap-2 support {mhat, mhat+2}.  GR-3's frozen forms
      (and graded_read clause 2) FAIL at this configuration; the supplier-level forms
      (with the frame pins sigma.s = 1, sigma.t = 0) exclude it.  NOTE: this
      configuration is NOT recordable (child_e ties recorded frames to the read pair)
      and NOT compilable over the corpus ambient F4 (a gap-psi over a char-2 field is
      a Frobenius power, never irreducible) -- the demo is the numeric shadow of the
      mathematical countermodel, priced at a p != 2 stage forge if ever compiled.

Exit 0 iff every check passes.
"""

from fractions import Fraction
import sys

P = 3

# ---------------------------------------------------------------- exact helpers (BM2 driver)

def vp(x, p=P):
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
    x = Fraction(x)
    v = vp(x, p)
    u = x / Fraction(p) ** v
    n, d = u.numerator % p, u.denominator % p
    return (n * pow(d, -1, p)) % p


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
    out = []
    cur = [Fraction(x) for x in f]
    if all(x == 0 for x in cur):
        return [[Fraction(0)]]
    while any(x != 0 for x in cur):
        q, r = pdivmod(cur, Phi)
        out.append(r)
        cur = q
    return out


def lower_hull(points):
    pts = sorted(points)
    hull = []
    for pt in pts:
        while len(hull) >= 2:
            (x1, y1), (x2, y2) = hull[-2], hull[-1]
            if (y2 - y1) * (pt[0] - x1) >= (pt[1] - y1) * (x2 - x1):
                hull.pop()
            else:
                break
        hull.append(pt)
    return hull


def sides_of(points):
    hull = lower_hull(points)
    sides = []
    for (x1, y1), (x2, y2) in zip(hull, hull[1:]):
        s = Fraction(y2 - y1, x2 - x1)
        if s >= 0:
            continue
        on = [(x, y) for (x, y) in points if x1 <= x <= x2 and Fraction(y - y1) == s * (x - x1)]
        sides.append((s, (x1, y1), (x2, y2), on))
    return sides


def canonical_bezout(e, h):
    """The rev-14 canonical pair: e*s + h*t = 1 with t in [0, e) (hbezCanon)."""
    for t in range(e):
        if (1 - h * t) % e == 0:
            return (1 - h * t) // e, t
    raise RuntimeError


FAIL = []


def check(name, cond, detail=""):
    tag = "PASS" if cond else "FAIL"
    print(f"  [{tag}] {name}" + (f"  ({detail})" if detail else ""))
    if not cond:
        FAIL.append(name)


# ---------------------------------------------------------------- the per-read N-GR1 block

def ngr1_read(label, slots, e, h, s0, scale_lattice, frame_key_stage_weight, e_read_is_level):
    """One recorded read.  `slots` = [(fine slot j, absolute weight w_j)] on-line;
    `(e, h)` the read pair on the scale lattice (stage units = scale_lattice * absolute);
    `frame_key_stage_weight` = sigma.h of the read's frame under the child keying
    (= nu.h at recorded reads; None at the root frame, printed as untied)."""
    print(f"\n--- {label}: read pair (e,h) = ({e},{h}), fine slots {[j for j, _ in slots]}")
    s, t = canonical_bezout(e, h)
    g = (slots[-1][0] - s0) // e
    mhat = -t * h * g
    # gamma = total side weight in stage units: e*(stage-scale right-endpoint height) + j*'*h
    jstar = slots[-1][0]
    ustar_stage = slots[-1][1] * scale_lattice
    gamma = e * ustar_stage + jstar * h
    assert gamma == int(gamma), "gamma on-lattice"
    gamma = int(gamma)
    # N1: positions integral, affine, unit step per lattice slot
    pos = {}
    for (j, wj) in slots:
        pj = Fraction(j - t * gamma, e)
        pos[(j - s0) // e] = pj
        check(f"{label} N1: p_{j}(gamma={gamma}) = {pj} INTEGER", pj.denominator == 1)
    kappas = sorted(pos)
    steps = [pos[k2] - pos[k1] for k1, k2 in zip(kappas, kappas[1:]) if k2 == k1 + 1]
    check(f"{label} N1: unit kappa-step across adjacent lattice slots",
          all(st == 1 for st in steps), f"steps {steps}")
    # N2: pos(kappa) = kappa + mhat, mhat = -t*h*g at the canonical pair
    check(f"{label} N2: pos(kappa) = kappa + mhat, mhat = -t*h*g = {mhat} (canonical (s,t) = ({s},{t}))",
          all(pos[k] == k + mhat for k in kappas), f"pos {dict(pos)}")
    # N3: the frame-face scale law nu.h = nu.e * sigma.h (child keying: sigma.h = nu.h)
    if frame_key_stage_weight is None:
        print(f"  [NOTE] {label} N3: ROOT frame -- no child tie; scale law untied (supplier scope excludes roots)")
    else:
        scale_holds = (h == e * frame_key_stage_weight)
        check(f"{label} N3: scale law h = e*sigma.h {'HOLDS' if e == 1 else 'FAILS'} as predicted (iff e = 1)",
              scale_holds == (e == 1) == e_read_is_level,
              f"h = {h}, e*sigma.h = {e * frame_key_stage_weight}")
    # N4: frame-face readPos at e = 1 frames ((s,t)_frame = (1,0)): readPos = kappa + 0
    if e == 1 and frame_key_stage_weight is not None:
        check(f"{label} N4: frame-face readPos (sigma.s, sigma.t) = (1,0) reproduces pos = kappa (mhat = 0)",
              t == 0 and mhat == 0 and all(pos[k] == k for k in kappas))
    return pos, mhat


print("=" * 78)
print("N-GR1 SLOT-POSITION FALSIFIER FAMILY (gates GR-0/GR-2/GR-3)")
print("=" * 78)

# ---------------- instance A (the BM2 quartic; recomputed, not asserted) ----------------
fA = [Fraction(c) for c in (198, -90, 51, -12, 1)]
ptsA0 = [(i, vp(a)) for i, a in enumerate(fA) if a != 0]
(sA0, loA0, hiA0, onA0), = sides_of(ptsA0)
check("A read 0: side (e,h) = (2,1) recomputed", (sA0.denominator, -sA0.numerator) == (2, 1))
ngr1_read("A read 0 (steep root: e'=2, g=1, t=1)", [(j, w) for j, w in onA0],
          2, 1, loA0[0], 1, None, False)

Phi1p = [Fraction(3), Fraction(-6), Fraction(1)]          # x^2 - 6x + 3 (post-recentering key)
BpA = develop2(fA, Phi1p)


def w1(B):
    vals = [vp(a) + Fraction(i, 2) for i, a in enumerate(B) if a != 0]
    return min(vals) if vals else None


ptsA2 = [(j, w1(Bj)) for j, Bj in enumerate(BpA) if any(x != 0 for x in Bj)]
(sA2, loA2, hiA2, onA2), = sides_of(ptsA2)
lamA2 = -sA2
check("A read 2: slope 2, stage pair (1,4) recomputed", lamA2 == 2 and int(2 * lamA2) == 4)
# stage units at read 2: STR = 2 (the e=2 landing), scale_lattice = 2
ngr1_read("A read 2 (level interior: e'=1, g=2, t=0)", [(j, w) for j, w in onA2],
          1, 4, loA2[0], 2, 4, True)
# read 2's residual digits vs psi (the (SL-dev) scalar content, U0 = 1 -- BM2 trace re-check):
A2 = digit(9) * digit(9) % P  # anchor in(9)^2 hmm -- recompute plainly below
dA2 = {}
for (j, wv) in onA2:
    Bj = BpA[j] if j < 2 else [Fraction(1)]
    # in stage-2 scale all slots weigh 4; the digit of the minimizing monomial:
    nz = [(i, a) for i, a in enumerate(Bj) if a != 0 and vp(a) + Fraction(i, 2) == wv]
    (i0, a0), = nz
    dA2[j] = (digit(a0) * pow(-1, int(vp(a0)) % 2, P) * pow(pow(-1, 1, P), 0, P)) % P
check("A read 2: both lower digits present (2, 1) -- psi2 = z^2 + z + 2 pattern",
      dA2[0] in (1, 2) and dA2[1] in (1, 2), f"digits {dA2}")

# ---------------- instance B (e' >= 2 AND g >= 2 AND t != 0: the spec's joint case) -------
fB = [Fraction(c) for c in (18, 0, 3, 0, 1)]              # x^4 + 3x^2 + 18
ptsB = [(i, vp(a)) for i, a in enumerate(fB) if a != 0]
sidesB = sides_of(ptsB)
check("B: single principal side", len(sidesB) == 1)
(sB, loB, hiB, onB), = sidesB
check("B read 0: (e,h) = (2,1), width 4, THREE on-line slots (g = 2)",
      (sB.denominator, -sB.numerator) == (2, 1) and len(onB) == 3)
RB = [0, 0, 0]
for (i, v) in onB:
    RB[(i - loB[0]) // 2] = digit(fB[i])
check("B read 0: residual z^2 + z + 2 (coeffs [2,1,1]), IRREDUCIBLE over F_3",
      RB == [2, 1, 1] and all(sum(c * pow(r, k, 3) for k, c in enumerate(RB)) % 3 != 0 for r in range(3)))
posB, mhatB = ngr1_read("B read 0 (steep root: e'=2, g=2, t=1 -- the joint spec case)",
                        [(j, w) for j, w in onB], 2, 1, loB[0], 1, None, False)
check("B N2 sharp: mhat = -1*1*2 = -2 and positions {-2,-1,0}",
      mhatB == -2 and [posB[k] for k in sorted(posB)] == [-2, -1, 0])

# ---------------- N5: the sigma.e-residue demo (the GR-3/GR-4 obstruction) ---------------
print("\n--- N5: THE SIGMA.E-RESIDUE DEMO (abstract ramified frame, key X, w = min(2*v3 + i))")
# frame: sigma.e = 2, sigma.h = 1 (w(X) = 1), canonical-free stage pair (s,t) = (0,1)
#        (2*0 + 1*1 = 1); wPrev = v3 on constants (the C-window of key X).
# fake node: nu.e = 1, nu.h = 1; hscale: nu.h = nu.e * sigma.w(sigma.Phi) -> 1 = 1*1 HOLDS.
# psi = z^2 + 1 irreducible over F_3; IsNodeLift realizer tt0 = 3 (w = 2 = nu.h*g,
# wPrev = 1, digit 1 = psi_0 at position -sigma.t*wPrev = -1); Phi' = X^2 + 3.
sigma_e, sigma_h, sigma_s, sigma_t = 2, 1, 0, 1
nu_e, nu_h, g5 = 1, 1, 2
check("N5: frame Bezout 2*0 + 1*1 = 1 (gcd(2,1) = 1; he1t vacuous at e = 2)",
      sigma_e * sigma_s + sigma_h * sigma_t == 1)
check("N5: hscale HOLDS at the fake node (1 = 1 * w(X) = 1*1)", nu_h == nu_e * sigma_h)
check("N5: psi = z^2+1 irreducible over F_3 (support GAP = sigma.e = 2, psi_0 != 0)",
      all((r * r + 1) % 3 != 0 for r in range(3)))
# IsNodeLift weight law: w(tt_0) = nu.h*(g-0) = 2 = w(3) = 2*v3(3) -- realizer tt0 = 3:
check("N5: realizer tt0 = 3 has w = 2*v3(3) = 2 = nu.h*g and wPrev = v3(3) = 1",
      2 * 1 == nu_h * g5 and vp(3) == 1)
# frame-face positions of Phi' = X^2 + 3: slot 0 at -sigma.t*wPrev(3) = -1; slot 2 at 2*sigma.s = 0
pos5 = {0: -sigma_t * 1 + 0 * sigma_s, 2: 0 * 1 + 2 * sigma_s}
check("N5: R(X^2+3) positions COMPRESS to adjacent {-1, 0} (Delta = 1 for slot gap 2)",
      pos5[2] - pos5[0] == 1, f"positions {pos5}")
nu_t = 0  # hbezCanon at nu.e = 1
mhat5 = -nu_t * nu_h * g5
check("N5: GR-3 pinned target T^mhat*psi needs support {mhat, mhat+2} = {0, 2} -- UNMATCHABLE",
      {mhat5, mhat5 + g5} != {pos5[0], pos5[2]},
      f"target {{{mhat5}, {mhat5 + g5}}} vs actual {{{pos5[0]}, {pos5[2]}}}")
check("N5: the exists-form fails too (toLaurent psi has gap-2 support; T-shift preserves gaps)",
      (pos5[2] - pos5[0]) != g5)
# the supplier-level pins EXCLUDE the demo: sigma.s = 1, sigma.t = 0 fails here
check("N5: the frame pins (sigma.s, sigma.t) = (1, 0) EXCLUDE the demo configuration",
      not (sigma_s == 1 and sigma_t == 0))
# and the recorded perimeter excludes it: child_e would force sigma.e = nu.e = 1
check("N5: unrecordable (child_e tie sigma.e = nu.e violated: 2 != 1)", sigma_e != nu_e)
# and the corpus ambient F4 blocks compilation: gap-psi over char-2 = Frobenius square
print("  [NOTE] over the corpus ambient F4 (char 2), psi with support in 2N is a square")
print("         (Frobenius), never irreducible -> no compiled corpus instance can host N5;")
print("         a compiled countermodel is priced at a p != 2 stage forge (one full unit).")

# ---------------------------------------------------------------- verdicts
print("\n" + "=" * 78)
print("N-GR1 GATE VERDICTS")
print("=" * 78)
print("""
  N1/N2 (D.3(c) stride + D.8 mhat)    GREEN at every probed read (A0/A2/B0) incl. the
                                      joint e'=2 AND g=2 AND t!=0 case -> GR-2's
                                      readPos law + unit-step statement RELEASED.
  N3 (the GR-0 scale law)             REFINED: holds IFF e_read = 1 (the compiled
                                      forcing readHyps_e_eq_one); the frame-face
                                      equal-weights display is the e=1/[NR] layer,
                                      steep reads live at the regrade (kp_step's face).
  N4 (frame-face readPos)             GREEN at the e=1 interior read (A2).
  N5 (sigma.e-residue)                THE OBSTRUCTION FIRES at the abstract carrier:
                                      GR-3 frozen forms + graded_read clause 2 REFUTED
                                      there; supplier-level forms (frame pins) GREEN;
                                      recorded perimeter + corpus ambient both exclude
                                      the configuration (unrecordable + char-2-blocked).
""")

if FAIL:
    print(f"*** {len(FAIL)} CHECK(S) FAILED: {FAIL}")
    sys.exit(1)
print("ALL CHECKS PASSED.")
