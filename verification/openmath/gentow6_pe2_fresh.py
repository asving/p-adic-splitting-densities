#!/usr/bin/env python3
"""GENTOW6 passPE2 fresh instrument — hostile verifier leg, 2026-08-10.

INDEPENDENT code: no import of any sealed runner (gentow1/3/4/6_checks,
gentow6_r1_caplemma, gentow6_pe1_fresh). Frames DISJOINT from every
battery/fresh/repair frame in the GENTOW6 arc. Dual oracles: own
integer-exact polynomial core vs PARI/gp (division, factorpadic,
resultant valuations); hand ledgers preregistered below.

LEG A — the f1 = 2 / eta != 1 BOUNDARY TOOTH (tests the [GT6-r1]
f1 = 1 scope pin from OUTSIDE) + first machine contact for
ANNEX-THEOREM GENTOW-6.3'(b')'s certificate display.
  Frame: Q2, Phi' = x^4 + 2x^2 + 4 (e1 = 2, f1 = 2, h = 1, D' = 4;
  eta = res(x^2/2), eta^2 + eta + 1 = 0: K = F_4). Genre e2 = 2,
  f2 = 1, u2 = 9 (> e2 D' h = 8), T = {0}, t* = 0; E2 = 18,
  delta = 1, THETA_0 = 37; w(a,b) = 2a + 9b; e1e2 = 4.
  nhat-decomposition of m = 9: i_0 = 1, a_0 = 4. r_max = 1, so
  I_0 = i_0 + e1*r_max = 3.
  A-simple: c_0 = eta  => corrected lift L = 2^3 x^3;
     Phi2 = Phi'^2 - 8x^3.
  A-rich:   c_0 = 1+eta => L = 2^4 x + 2^3 x^3;
     Phi2 = Phi'^2 - 8x^3 - 16x  (a second lift monomial: exercises
     (b') delta (ii): the non-top pair extracts to a DISTINCT slot).
  PREREGISTERED (hand ledger, derived from the note's S6.1 displays
  before any run):
   PA-1 scope data: 2*i_0 = 2 < 4 = D' (sealed (b) hypothesis
     UNSATISFIABLE — the vacuity inequality instance) and the sealed
     (c) hypothesis i_t + i_t' < D' HOLDS at this genre.
   PA-2 the TOOTH: the sealed (c) CONCLUSION FAILS — dev(Phi2^2) by
     Phi' has NONZERO Phi'^1-coefficient (an x-carry fired), vs the
     formal square K2^2 whose Y^1-coefficient is 0. Exact values:
     A-simple: dev = [512, 64x^2-128, -16x^3, 0, 1];
     A-rich:   dev = [-256x^2-512, 64x^2+128, -16x^3-32x, 0, 1].
   PA-3 honest read of f = Phi2^2 at key Phi2 is DRAIN (C_0=C_1=0);
     shadow division of F by K2 over R = Z[x]/(Phi') gives
     Ghat_2 = 1, Ghat_1 = 0, and Ghat_0 = ShC_0 with slots
     {(2,1): 64, (0,1): -128} (A-simple) / {(2,1): 64, (0,1): 128}
     (A-rich).
   PA-4 CERT-TOP' (6.3'(b')): certificate slot (j*,a*,b*) = (0,2,1)
     [Y-exp 2 e2 t* + 1 = 1; a* = 2 I_0 - D' = 2], digit 64 with
     v = 6 = 2(a_0 - r* h), unit part 1, slot height 4*6 + w(2,1)
     = 37 = THETA_0 — divergence EXACTLY on the floor; the A-rich
     frame's extra pair lands at slot (0,1), NOT the cert slot, and
     leaves the cert digit 64 byte-unchanged.
   PA-5 PARI oracle: same dev coefficient vectors via gp divrem;
     factorpadic: Phi' irreducible /Q2 (one factor, deg 4, f = 2);
     both Phi2's irreducible /Q2 (one factor, deg 8) — the genre
     members are genuine keys, non-vacuous.
  TOOTH T-NAIVE: fires iff the sealed-(c) equality fails at each
  A-frame (if it held, the scope pin's justification would be wrong).

LEG B — a mixed side with an f2 = 3 class (l*deg r = 6: beyond the
sealed fence's named l*deg r = 4 gap) + LEMMA GENTOW-6.4 stress at a
partial-side member the r1 repair did NOT use.
  Geography: Q3, Phi' = x^2 - 3 (e1 = 2, f1 = 1, h = 1), inner side
  slope 5/2 (u2 = 5, e2 = 2, l = 2). Keys:
   Phi2_c = Phi'^6 - 3^5 Phi'^2 - 3^7 x  (f2 = 3, D2 = 12, E2 = 30,
     grid b < 6; psi_c predicted T^3 - T - 1, irreducible /F_3);
   Phi2_l = Phi'^2 - 9x (f2 = 1, D2 = 4, E2 = 10, grid b < 2;
     psi_l = T - 1).
  Blocks: B_c = Phi2_c + 3^11 (pert height 44 > E2+...; in-budget),
  B_l = Phi2_l + 3^6 (height 24). MEMBER (new, partial-side both
  ways): f = B_c * B_l * (Phi' - 27), deg 18; sibling side slope 6.
  PREREGISTERED:
   PB-1 level-1 side of f: hull (0,26) -> (1,20) -> (9,0): the
     sibling side (slope -6, steeper) sits LEFT, the 5/2-side spans
     [1,9], length 8; s = 1 lattice point ABOVE the side (residual
     T-coeff 0);
     measured residuals: R(Phi2_c) = T^3 - T - 1, R(Phi2_l) = T - 1,
     R(B_c)/R(B_l) identical (pert above side), R(f) monic-normalized
     = (T^3 - T - 1)(T - 1) = T^4 - T^3 - T^2 + 1; multiplicity
     profile {deg3: 1, deg1: 1} — m_c = m_l = 1.
   PB-2 composed reads: at Phi2_c: pins (p_0, p_1) = (59, 15), hull
     slope 44 > T2 = 30, mu2*(c) = 1; at Phi2_l: mu2*(l) = 1
     (T2 = 10). THE TIE (LEMMA 6.1): mu2*(r) = m_r = 1 at BOTH
     classes, first f2 = 3 class read anywhere in the arc.
   PB-3 PARI decorrelated leg: poldisc != 0; factor degrees
     {12, 4, 2}; class degree sums via per-root resultant
     valuations: cubic class (v(Phi2_c(rho)) > 30/4) sum 12 =
     D' l deg(r) m_r; linear class (v(Phi2_l(rho)) > 10/4) sum 4;
     sibling in NEITHER (its valuations land exactly AT 7.5 / 2.5,
     hand-derived: unit tests psi_c(1) != 0, u^2 not in F_3).
   PB-4 [6.4(a) TRI at the unused member] perturbing [f]_d (d in
     0..17, eps in {1, 9}) at EACH key grid (cubic: slot jD2+bD'+a,
     b < 6; linear: b < 2): digits at slot degrees > d unchanged,
     slot-degree-d digit shifts by exactly eps (full grid incl.
     zero slots).
   PB-5 [6.4(a)(b) WIN/PIN] N = 7: random pi^N lifts: all digits
     congruent mod 3^7, in-window valuations equal; pins below cap
     e1e2 N = 28 stable at both keys.
   PB-6 [6.4(b) UNDERCUT] N_u = 5 at the cubic key: base p_0 = 59 >=
     cap 20; f + 3^5 moves p_0 to EXACTLY 20; below-cap pins held
     (p_1 = 15 unchanged).
   PB-7 [6.4(c) PROJECTION, the conditional COR 4.C face at an
     instance] c_g := p_{mu2*}(f): cubic key c_g = 15 with
     p_j(f) - c_g = p_j(B_c) for j = 0,1 ((59,15) - 15 = (44,0));
     linear key: p_j(f) - c_g' = p_j(B_l) = (24, 0) for j = 0,1.
  TOOTH T-SLOT: a +1-mutant slot map must MISS the TRI diagonal
  (per scanned degree, cubic key).

Verdict: GREEN iff 0 violations and both teeth fired.

RUN-1 DISCLOSURE (RED; transcript-captured tail kept as
gentow6_pe2_fresh_output_run1_RED.txt — the verifier piped run 1
through tail and did not save full stdout; the run aborted at the
LEG B side assert): three verifier-side defects,
all hand-traced before repair — (i) the coded literal for the top
dev coefficient was [0,0,0,0,1] (a degree-4 x-poly, OFF-GRID); the
hand ledger's A_4 = 1 means [1]; (ii) K2y used pneg(L) but the L
literal already carries the lift's minus sign (K2 = Y^2 + L); (iii)
the LEG B residual side was placed at [0,8] from (0,26); the
Minkowski order puts the steeper sibling side (slope -6) LEFT, so
the 5/2-side spans [1,9] from (1,20) — PE1's fresh leg A had shown
this exact hull shape at its own member. Defect (iii) corrected the
PB-1 side-location prereg; NO content prediction (residual factors,
multiplicities, tie values, pins, certificate digits/heights)
changed. The gp oracle line [] vs [0] canonicalization was also
aligned (gp prints [] for the zero coefficient).
"""
import random
import subprocess
import sys

random.seed(20260810)
CHECKS = [0, 0]
TEETH = {}


def check(name, ok):
    CHECKS[0 if ok else 1] += 1
    if not ok:
        print("VIOLATION: %s" % name)


def tooth(name, fired):
    TEETH[name] = TEETH.get(name, 0) + (1 if fired else 0)


# ---------- integer-exact polynomial core ----------

def trim(f):
    while f and f[-1] == 0:
        f.pop()
    return f


def padd(f, g):
    n = max(len(f), len(g))
    return trim([(f[i] if i < len(f) else 0) + (g[i] if i < len(g) else 0)
                 for i in range(n)])


def pneg(f):
    return [-c for c in f]


def pmul(f, g):
    if not f or not g:
        return []
    out = [0] * (len(f) + len(g) - 1)
    for i, a in enumerate(f):
        for j, b in enumerate(g):
            out[i + j] += a * b
    return trim(out)


def pdivmod_monic(f, g):
    assert g and g[-1] == 1
    r = list(f)
    dg = len(g) - 1
    q = [0] * max(1, len(f) - dg)
    while trim(r) and len(r) - 1 >= dg:
        d = len(r) - 1
        c = r[-1]
        q[d - dg] += c
        for i in range(len(g)):
            r[i + d - dg] -= c * g[i]
        trim(r)
    return trim(q), trim(r)


def dev(f, key):
    out = []
    cur = list(f)
    while cur:
        cur, rem = pdivmod_monic(cur, key)
        out.append(rem)
    return out


def vp(n, p):
    if n == 0:
        return None
    v = 0
    while n % p == 0:
        n //= p
        v += 1
    return v


# ---------- gp bridge ----------

def gp(src):
    out = subprocess.run(['gp', '-q', '-f'], input=src,
                         capture_output=True, text=True, timeout=120)
    return out.stdout.strip()


def poly_to_gp(f):
    return "Pol(%s)" % [c for c in reversed(f)] if f else "0"


# ================= LEG A =================

def leg_a():
    PHI1 = [4, 0, 2, 0, 1]          # x^4 + 2x^2 + 4
    D1 = 4
    e2, u2, h, e1 = 2, 9, 1, 2
    i0, a0, rmax = 1, 4, 1
    I0 = i0 + e1 * rmax
    check("A scope: 2*i0 < D' (sealed (c) hyp holds, (b) hyp empty)",
          2 * i0 < D1)
    check("A scope: 2*I0 >= D' ((b') fires)", 2 * I0 >= D1)
    frames = [
        ('A-simple', [0, 0, 0, -8],
         [[512], [-128, 0, 64], [0, 0, 0, -16], [], [1]],
         {(2, 1): 64, (0, 1): -128}),
        ('A-rich', [0, -16, 0, -8],
         [[-512, 0, -256], [128, 0, 64], [0, -32, 0, -16], [], [1]],
         {(2, 1): 64, (0, 1): 128}),
    ]
    E2 = e2 * 1 * u2
    delta = u2 - e2 * D1 * h
    THETA0 = 2 * E2 + delta

    def w(a, b):
        return a * e2 * h + b * u2

    for name, L, pred_dev, pred_sh0 in frames:
        PHI2 = padd(pmul(PHI1, PHI1), L)
        F2 = pmul(PHI2, PHI2)
        dv = dev(F2, PHI1)
        dv += [[]] * (5 - len(dv))
        check("%s dev(Phi2^2) matches hand ledger" % name,
              [trim(list(x)) for x in dv] == [trim(list(x))
                                              for x in pred_dev])
        # the TOOTH: sealed (c) conclusion fails (Y^1-coeff nonzero)
        carry_fired = trim(list(dv[1])) != []
        check("%s T-NAIVE: x-carry fired (A_1 != 0)" % name, carry_fired)
        tooth('T-NAIVE', carry_fired)
        # honest read DRAIN
        hon = dev(F2, PHI2)
        check("%s honest DRAIN (C_0 = C_1 = 0)" % name,
              len(hon) == 3 and hon[0] == [] and hon[1] == [])
        # shadow division in R[Y], R = Z[x]/(Phi'): represent F as
        # list of R-elts (in-grid x-polys) indexed by Y-exp; K2 = Y^2 - L
        Fy = [list(dv[j]) for j in range(5)]
        K2y = [list(L), [], [1]]   # K2 = Y^2 + L (L carries the minus)

        def rmod(g):
            return pdivmod_monic(g, PHI1)[1]

        def ydiv(F, K):
            # F, K lists of R-elts; K monic in Y (top coeff [1])
            Fw = [list(c) for c in F]
            dk = len(K) - 1
            q = [[] for _ in range(max(1, len(Fw) - dk))]
            while len(Fw) - 1 >= dk and any(trim(list(c)) for c in Fw):
                dtop = len(Fw) - 1
                if not trim(list(Fw[-1])):
                    Fw.pop()
                    continue
                c = Fw[-1]
                q[dtop - dk] = padd(q[dtop - dk], c)
                for i in range(len(K)):
                    Fw[i + dtop - dk] = padd(
                        Fw[i + dtop - dk], pneg(rmod(pmul(c, K[i]))))
                Fw.pop()
            while len(Fw) < dk:
                Fw.append([])
            return q, Fw

        q1, r1_ = ydiv(Fy, K2y)
        q2, r2_ = ydiv(q1, K2y)
        gh = [r1_, r2_, q2]
        check("%s shadow Ghat_2 = 1" % name,
              [trim(list(c)) for c in gh[2]] == [[1]] or
              [trim(list(c)) for c in gh[2] if trim(list(c))] == [[1]])
        check("%s shadow Ghat_1 = 0" % name,
              not any(trim(list(c)) for c in gh[1]))
        sh0 = {}
        for b, cx in enumerate(gh[0]):
            for a, c in enumerate(cx):
                if c:
                    sh0[(a, b)] = c
        check("%s ShC_0 slots match" % name, sh0 == pred_sh0)
        # certificate slot: digit, valuation, height = THETA_0
        cd = sh0.get((2, 1), 0)
        check("%s CERT' digit 64 at (2,1)" % name, cd == 64)
        check("%s CERT' v = 6 = 2(a0 - r*h)" % name,
              vp(cd, 2) == 6 == 2 * (a0 - rmax * h))
        check("%s CERT' unit part 1" % name, cd // 2 ** 6 == 1)
        hts = [4 * vp(c, 2) + w(a, b) for (a, b), c in sh0.items()]
        check("%s discrepancy pin = THETA_0 = %d exactly" % (name, THETA0),
              min(hts) == THETA0 and 4 * 6 + w(2, 1) == THETA0)
        # PARI oracle: dev + irreducibility
        src = ("K=%s;F=(%s)^2;r=[];while(F!=0,d=divrem(F,K);"
               "r=concat(r,[Vecrev(d[2])]);F=d[1]);print(r);"
               "print(#factorpadic(K,2,60)~);"
               "print(#factorpadic(%s,2,60)~)"
               % (poly_to_gp(PHI1), poly_to_gp(PHI2), poly_to_gp(PHI2)))
        lines = gp(src).splitlines()
        gp_dev = lines[0].replace(' ', '')
        my_dev = str([list(x) for x in dev(F2, PHI1)]).replace(' ', '')
        check("%s PARI dev oracle match" % name, gp_dev == my_dev)
        check("%s PARI: Phi' irreducible /Q2 (f1=2 genuine)" % name,
              lines[1].strip() == '1')
        check("%s PARI: Phi2 irreducible /Q2 (genuine key)" % name,
              lines[2].strip() == '1')


# ================= LEG B =================

P3 = 3
PHI1B = [-3, 0, 1]                              # x^2 - 3


def pw(f, k):
    out = [1]
    for _ in range(k):
        out = pmul(out, f)
    return out


PHI2C = padd(padd(pw(PHI1B, 6), pneg(pmul([3 ** 5], pw(PHI1B, 2)))),
             [0, -3 ** 7])                       # Phi'^6 - 3^5 Phi'^2 - 3^7 x
PHI2L = padd(pw(PHI1B, 2), [0, -9])              # Phi'^2 - 9x
BC = padd(PHI2C, [3 ** 11])
BL = padd(PHI2L, [3 ** 6])
SIB = padd(PHI1B, [-27])
FB = pmul(pmul(BC, BL), SIB)                     # deg 18


def dv1(a):
    """min over monomials of 2*v3(c) + i (h = 1, e1 = 2)."""
    best = None
    for i, c in enumerate(a):
        if c:
            t = 2 * vp(c, P3) + i
            if best is None or t < best:
                best = t
    return best


def side_residual(f, j0, j1, v0, slope_num, slope_den):
    """residual on the side (j0,v0)->(j1, v0 - slope*(j1-j0)); unit
    convention: res(minimal monomial / nhat(height))."""
    aj = dev(f, PHI1B)
    l = slope_den
    R = []
    for s in range((j1 - j0) // l + 1):
        j = j0 + l * s
        h = v0 - slope_num * s
        a = aj[j] if j < len(aj) else []
        d = dv1(a)
        if d is None or d > h:
            R.append(0)
            continue
        assert d == h, "point below claimed side"
        i = h % 2
        c = a[i]
        R.append((c // P3 ** ((h - i) // 2)) % P3)
    return R


def f3mul(f, g):
    out = [0] * (len(f) + len(g) - 1)
    for i, a in enumerate(f):
        for j, b in enumerate(g):
            out[i + j] = (out[i + j] + a * b) % 3
    while out and out[-1] == 0:
        out.pop()
    return out


class Grid(object):
    def __init__(self, name, key, e2, f2, u2):
        self.name, self.key = name, key
        self.e2, self.f2, self.u2 = e2, f2, u2
        self.D2 = len(key) - 1
        self.E2 = e2 * f2 * u2
        self.e1e2 = 2 * e2

    def w(self, a, b):
        return a * self.e2 + b * self.u2      # h = 1

    def digits(self, f):
        nn = len(f) - 1
        M = nn // self.D2
        e2f2 = self.e2 * self.f2
        devP = dev(f, self.key)
        devP += [[]] * (M + 1 - len(devP))
        out = {}
        for j, C in enumerate(devP):
            devB = dev(C, PHI1B)
            devB += [[]] * (e2f2 - len(devB))
            for b, B in enumerate(devB):
                Bp = list(B) + [0] * (2 - len(B))
                for a, c in enumerate(Bp):
                    out[(j, a, b)] = (c, j * self.D2 + b * 2 + a)
        return out

    def pins(self, f):
        ncoord = len(dev(f, self.key))
        pins = [None] * ncoord
        for (j, a, b), (c, _) in self.digits(f).items():
            v = vp(c, P3)
            if v is None:
                continue
            hgt = self.e1e2 * v + self.w(a, b)
            if pins[j] is None or hgt < pins[j]:
                pins[j] = hgt
        return pins

    def mu2star(self, f):
        pts = [(j, p) for j, p in enumerate(self.pins(f)) if p is not None]
        # lower hull, left to right
        hull = []
        for pt in pts:
            while len(hull) >= 2 and \
                (hull[-1][1] - hull[-2][1]) * (pt[0] - hull[-1][0]) >= \
                    (pt[1] - hull[-1][1]) * (hull[-1][0] - hull[-2][0]):
                hull.pop()
            hull.append(pt)
        m = 0
        for (ja, pa), (jb, pb) in zip(hull, hull[1:]):
            if pa - pb > self.E2 * (jb - ja):
                m += jb - ja
        return m


def leg_b():
    GC = Grid('cubic', PHI2C, 2, 3, 5)
    GL = Grid('linear', PHI2L, 2, 1, 5)
    # PB-1 residuals
    psi_c = side_residual(PHI2C, 0, 6, 15, 5, 2)
    check("B psi_c = T^3 - T - 1", psi_c == [2, 2, 0, 1])
    psi_l = side_residual(PHI2L, 0, 2, 5, 5, 2)
    check("B psi_l = T - 1", psi_l == [2, 1])
    check("B R(B_c) = psi_c (pert above side)",
          side_residual(BC, 0, 6, 15, 5, 2) == psi_c)
    check("B R(B_l) = psi_l", side_residual(BL, 0, 2, 5, 5, 2) == psi_l)
    Rf = side_residual(FB, 1, 9, 20, 5, 2)
    check("B R(f) deg 4 monic-normalizable", len(Rf) == 5 and Rf[4] != 0)
    lcinv = pow(Rf[4], 1, 3)
    inv = 1 if lcinv == 1 else 2
    Rfm = [(c * inv) % 3 for c in Rf]
    check("B R(f) = psi_c * psi_l exactly (MULT/UFD display)",
          Rfm == f3mul(psi_c, psi_l))
    check("B R(f) = T^4-T^3-T^2+1 (hand prereg)", Rfm == [1, 0, 2, 2, 1])
    # m-profile: psi_c, psi_l distinct irreducibles each dividing once
    q1, r1_ = pdivmod_f3(Rfm, psi_c)
    check("B m_c = 1 (psi_c | R, psi_c^2 does not)",
          r1_ == [] and pdivmod_f3(q1, psi_c)[1] != [])
    q2, r2_ = pdivmod_f3(Rfm, psi_l)
    check("B m_l = 1", r2_ == [] and pdivmod_f3(q2, psi_l)[1] != [])
    # PB-2 composed reads + THE TIE
    pc = GC.pins(FB)
    check("B cubic pins (p_0, p_1) = (59, 15)", pc[0] == 59 and pc[1] == 15)
    mc = GC.mu2star(FB)
    ml = GL.mu2star(FB)
    check("B TIE mu2*(cubic) = m_c = 1 (f2 = 3 class)", mc == 1)
    check("B TIE mu2*(linear) = m_l = 1", ml == 1)
    # PB-3 PARI leg
    src = ("f=%s;print(valuation(poldisc(f),3));"
           "F=factorpadic(f,3,200);K1=%s;K2=%s;"
           "for(i=1,#F~,my(g=F[i,1],d=poldegree(g));"
           "print(d,\":\",valuation(polresultant(g,K1),3),\":\","
           "valuation(polresultant(g,K2),3)))"
           % (poly_to_gp(FB), poly_to_gp(PHI2C), poly_to_gp(PHI2L)))
    lines = gp(src).splitlines()
    check("B PARI poldisc(f) != 0 (finite valuation)",
          lines[0].strip().isdigit())
    rows = [tuple(int(t) for t in ln.split(':')) for ln in lines[1:]
            if ':' in ln]
    degs = sorted(r[0] for r in rows)
    check("B PARI factor degrees {12,4,2}", degs == [2, 4, 12])
    csum = sum(d for d, v1, v2 in rows if 2 * v1 > 15 * d)
    lsum = sum(d for d, v1, v2 in rows if 2 * v2 > 5 * d)
    check("B PARI cubic-class degree sum = 12 = D' l deg(r) m_r",
          csum == 12)
    check("B PARI linear-class degree sum = 4", lsum == 4)
    sib = [r for r in rows if r[0] == 2]
    check("B PARI sibling in NEITHER class (vals AT the floors)",
          len(sib) == 1 and 2 * sib[0][1] == 15 * 2 and
          2 * sib[0][2] == 5 * 2)
    # PB-4 TRI at both grids
    for G in (GC, GL):
        base = G.digits(FB)
        for d in range(18):
            for eps in (1, 9):
                pert = [0] * (d + 1)
                pert[d] = eps
                new = G.digits(padd(list(FB), pert))
                above_ok, diag_ok = True, False
                for k, (c, sd) in base.items():
                    c2 = new[k][0]
                    if sd > d and c2 != c:
                        above_ok = False
                    if sd == d and c2 - c == eps:
                        diag_ok = True
                check("B %s TRI-above d=%d eps=%d" % (G.name, d, eps),
                      above_ok)
                check("B %s TRI-diag d=%d eps=%d" % (G.name, d, eps),
                      diag_ok)
        # T-SLOT tooth at the cubic grid only
        if G.name == 'cubic':
            for d in range(18):
                pert = [0] * (d + 1)
                pert[d] = 1
                new = G.digits(padd(list(FB), pert))
                mut_diag = False
                for k, (c, sd) in base.items():
                    if sd + 1 == d and new[k][0] - c == 1:
                        mut_diag = True
                tooth('T-SLOT', not mut_diag)
    # PB-5 WIN/PIN
    N = 7
    pN = P3 ** N
    for G in (GC, GL):
        base_dig = G.digits(FB)
        base_pins = G.pins(FB)
        cap = G.e1e2 * N
        for trial in range(3):
            pert = [random.randint(-8, 8) for _ in range(18)]
            lift = padd(list(FB), [pN * c for c in pert])
            dig = G.digits(lift)
            check("B %s WIN-cong trial %d" % (G.name, trial),
                  all((dig[k][0] - c) % pN == 0
                      for k, (c, _) in base_dig.items()))
            inwin = True
            for k, (c, _) in base_dig.items():
                v = vp(c, P3)
                if v is not None and v < N and vp(dig[k][0], P3) != v:
                    inwin = False
            check("B %s WIN-inwindow trial %d" % (G.name, trial), inwin)
            pins = G.pins(lift)
            check("B %s PIN-STAB trial %d (cap %d)" % (G.name, trial, cap),
                  all(pins[j] == base_pins[j]
                      for j in range(len(base_pins))
                      if base_pins[j] is not None and base_pins[j] < cap))
    # PB-6 undercut (cubic key)
    Nu = 5
    cap = 4 * Nu
    base_pins = GC.pins(FB)
    check("B UND setup p_0 = 59 >= 20", base_pins[0] == 59 >= cap)
    lift = padd(list(FB), [P3 ** Nu])
    pins = GC.pins(lift)
    check("B UND p_0 -> exactly 20", pins[0] == cap)
    check("B UND below-cap held (p_1 = 15)", pins[1] == base_pins[1] == 15)
    # PB-7 projection (COR 4.C face at an instance)
    cg_c = GC.pins(FB)[1]
    check("B PROJ cubic c_g = 15", cg_c == 15)
    bc_pins = GC.pins(BC)
    check("B PROJ cubic p_j(f) - c_g = p_j(B_c) = (44, 0)",
          [GC.pins(FB)[j] - cg_c for j in (0, 1)] ==
          [bc_pins[0], bc_pins[1]] == [44, 0])
    pl = GL.pins(FB)
    cg_l = pl[1]
    bl_pins = GL.pins(BL)
    check("B PROJ linear p_j(f) - c_g' = p_j(B_l) = (24, 0)",
          [pl[0] - cg_l, pl[1] - cg_l] ==
          [bl_pins[0], bl_pins[1]] == [24, 0])


def pdivmod_f3(f, g):
    r = [c % 3 for c in f]
    while r and r[-1] == 0:
        r.pop()
    dg = len(g) - 1
    q = [0] * max(1, len(r) - dg)
    ginv = 1 if g[-1] == 1 else 2
    while r and len(r) - 1 >= dg:
        d = len(r) - 1
        c = (r[-1] * ginv) % 3
        q[d - dg] = (q[d - dg] + c) % 3
        for i in range(len(g)):
            r[i + d - dg] = (r[i + d - dg] - c * g[i]) % 3
        while r and r[-1] == 0:
            r.pop()
    return q, r


def main():
    leg_a()
    leg_b()
    print('teeth: ' + ', '.join('%s fired x%d' % (k, v)
                                for k, v in sorted(TEETH.items())))
    ok = CHECKS[1] == 0 and all(v > 0 for v in TEETH.values())
    print('=== PE2 FRESH VERDICT: %s -- %d checks, %d violations ==='
          % ('GREEN' if ok else 'RED', sum(CHECKS), CHECKS[1]))
    sys.exit(0 if ok else 1)


if __name__ == '__main__':
    main()
