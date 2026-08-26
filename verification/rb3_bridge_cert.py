#!/usr/bin/env python3
"""
rb3_bridge_cert.py — RB3's upward budget->height bridge, examples-first certificate.

UNIT MBRIDGE, 2026-08-26.  Certificate spec: BLOCKERS_PLAN_2026-08-26.md, F3B
("verification/dec4_shadow_budget_cert.py" spec; filename per brief_MBRIDGE.md).

TARGET (leanspec ChapC.lean:3482-3494, `shadow_persistence`, clause 1 = plan node F3.6):
  hbudget : forall j' < mu2, a < e1*f1, b < e2*f2,
      budgetFloor T mu2 j' a b <= addVal O ((dev key (dev Phi2 g j') b).coeff a)
  ==>  theta(mu2,j) + 1 <= dv2Hgt(shadowDev T g j - dev Phi2 g j)      [clause 1]
  and  dv2Hgt(discrepancy of Phi2^mu2 + g) = theta(mu2,j)              [clause 2]
given hj : j < mu2 and hc : TouchCert (key-power discrepancy height == theta exactly).

DEFINITIONS MODELED EXACTLY (leanfinal sources):
  dev phi g j          -- iterated monic divmod digits              (ChapB B02)
  key = x^2 - p        -- s2Frame key at p=2 (C97 s2Key); p=3 mirror
  Phi2 = key^{e2} - lift, lift = p^2 * x  (u2=5)  /  p^3 * x (u2=7) (C43 composedKey,
                          C14a stageLiftO at M=u2: i=slotIdx=1, a=(u2-1)/2)
  biRead / devQ / shadowDev                                          (C71:140-144, leanspec 3408-3426)
  dvHgt F A b   = min_a (e1*v_p(coeff) + h*a)   over a in range(natDegree+1)   (C02/C06)
  dv2Hgt L A    = min_b (e2*dvHgt(A,b) + u2*b)  over b in range(natDegree+1)   (C06/C11)
  slotOffset    = a*(e2*h) + b*u2                                    (C50:121)
  wtCoeff       = (e1*e2)*v + slotOffset                             (C131a:33)
  budgetFloor   = 0 if (mu2-j)*E2 < w else ceil(tgt/d) + [d | tgt]   (C52:2022-2028 leanspec)
  E2 = e2*f2*u2,  margin = u2 - e2*(e1*f1)*h,  theta = (mu2-j)*E2 + margin  (C71:149-157)

PREREGISTERED PREDICTIONS (read off the intended proof mechanism BEFORE running):
  P0. budgetFloor v-threshold ARITHMETIC: v >= budgetFloor(mu2,j,a,b)
        <=>  (e1*e2)*v + slotOffset(a,b) >= (mu2-j)*E2 + 1   (strictly above the line).
  P1. Every g with hbudget AND natDegree g < mu2*D2 has discrepancy height >= theta_j + 1,
      at every j < mu2.
  P2. Tightness structure: for single-slot g = u * p^floor * x^a key^b Phi2^{j0}, the
      mechanism's floor is (slot weight) + j0*E2 - j*E2 + margin, slot weight excess over
      (mu2-j0)*E2 being 4 - (tgt mod 4) in {1,2,3,4}; observed heights should be >= that,
      with equality somewhere (locating where theta+1 is TIGHT: excess 1 slots).
  P3. DEFEAT of the SIGNED statement (no degree hypothesis): g := Phi2^mu2 satisfies
      hbudget VACUOUSLY (its Phi2-digits below mu2 all vanish), yet its discrepancy height
      equals theta_j exactly wherever TouchCert holds -- clause 1 (theta+1 <= theta) FALSE.
      Hand-computed instance: s2, mu2=2, j=0: discrepancy = 16*Phi', height 21 = theta.
  P4. Clause 2 holds for budgeted g (with the degree bound): at TouchCert coordinates,
      dv2Hgt(discrepancy of Phi2^mu2 + g) == theta_j exactly (ultrametric strict-add).
  N1. Negative controls: one slot exactly one unit below floor makes hbudget fail; at
      slots feeding a nonzero discrepancy the observed height drops below theta_j + 1
      for at least one control per (frame, mu2) -- the floor genuinely bites.
Cross-check: s2Witness digit height == 31 (C131uf.s2Witness_digit_height).
"""

from fractions import Fraction
from itertools import product
import sys

INF = float('inf')

# ---------------------------------------------------------------- polynomial core
def trim(p):
    while p and p[-1] == 0:
        p.pop()
    return p

def padd(p, q):
    n = max(len(p), len(q))
    return trim([ (p[i] if i < len(p) else 0) + (q[i] if i < len(q) else 0) for i in range(n) ])

def pneg(p): return [-c for c in p]
def psub(p, q): return padd(p, pneg(q))

def pmul(p, q):
    if not p or not q: return []
    out = [Fraction(0)] * (len(p) + len(q) - 1)
    for i, a in enumerate(p):
        for j, b in enumerate(q):
            out[i + j] += a * b
    return trim(out)

def ppow(p, n):
    out = [Fraction(1)]
    for _ in range(n):
        out = pmul(out, p)
    return out

def pdivmod(g, phi):
    """monic phi division: g = q*phi + r, deg r < deg phi."""
    assert phi and phi[-1] == 1
    r = list(g); q = []
    d = len(phi) - 1
    while len(r) - 1 >= d and r:
        k = len(r) - 1 - d
        c = r[-1]
        while len(q) <= k: q.append(Fraction(0))
        q[k] += c
        for i in range(len(phi)):
            r[k + i] -= c * phi[i]
        trim(r)
    return trim(q), r

def dev(phi, g, j):
    """B02 dev: j-th phi-adic digit."""
    for _ in range(j):
        g, _r = pdivmod(g, phi)[0], None
    _q, r = pdivmod(g, phi)
    return r

def natdeg(p):  # Lean natDegree: 0 for the zero polynomial
    return len(p) - 1 if p else 0

def vp(c, p):
    if c == 0: return INF
    v = 0
    num, den = c.numerator, c.denominator
    assert den % p != 0, "not p-integral"
    while num % p == 0:
        num //= p; v += 1
    return v

# ------------------------------------------------- quotient ring R = O[x]/(key), R[Z]
class Frame:
    def __init__(self, name, p, u2, lift_unit=1):
        """lift_unit: stageLiftO's resLift(1) is SOME unit lift of the residue 1, not
        necessarily 1 (C14a resLift is a choice); the bridge must be unit-blind."""
        self.name, self.p = name, p
        self.e1, self.f1, self.h = 2, 1, 1
        self.key = [Fraction(-p), Fraction(0), Fraction(1)]      # x^2 - p
        self.e2, self.f2, self.u2 = 2, 1, u2
        self.Dp = self.e1 * self.f1                              # D' = deg key = 2
        self.D2 = self.Dp * self.e2 * self.f2                    # 4
        self.E2 = self.e2 * self.f2 * self.u2
        self.margin = self.u2 - self.e2 * self.Dp * self.h
        # composedKey: key^{e2 f2} - stageLiftO(u2)(1) ; slotIdx u2 = 1 (h=1,e1=2,u2 odd),
        # pi-exponent a = (u2-1)/2, lift = p^a * x   (C14a f1=1 unfolding check)
        a = (u2 - 1) // 2
        lift = [Fraction(0), Fraction(lift_unit) * Fraction(p) ** a]   # u * p^a * x
        self.Phi2 = psub(ppow(self.key, self.e2 * self.f2), lift)

    def slotOffset(self, a, b): return a * (self.e2 * self.h) + b * self.u2
    def wtCoeff(self, v, a, b):
        return INF if v == INF else (self.e1 * self.e2) * v + self.slotOffset(a, b)
    def budgetFloor(self, mu2, j, a, b):
        w = self.slotOffset(a, b); tgt = (mu2 - j) * self.E2 - w; d = self.e1 * self.e2
        if (mu2 - j) * self.E2 < w: return 0
        return (tgt + d - 1) // d + (1 if tgt % d == 0 else 0)
    def theta(self, mu2, j): return (mu2 - j) * self.E2 + self.margin

    # R = O[x]/(key); elements = canonical reps (deg < 2 polys)
    def rmul(self, u, v): return pdivmod(pmul(u, v), self.key)[1]
    def rp_mul(self, P, Q):
        """multiply in R[Z]; P,Q lists of R-elements."""
        if not P or not Q: return []
        out = [[] for _ in range(len(P) + len(Q) - 1)]
        for i, a in enumerate(P):
            for j, b in enumerate(Q):
                out[i + j] = padd(out[i + j], self.rmul(a, b))
        while out and not out[-1]: out.pop()
        return out
    def rp_divmod(self, G, Psi):
        assert Psi and Psi[-1] == [Fraction(1)]                  # monic in Z
        R = [list(c) for c in G]; Q = []
        d = len(Psi) - 1
        while len(R) - 1 >= d and R:
            k = len(R) - 1 - d
            c = R[-1]
            while len(Q) <= k: Q.append([])
            Q[k] = padd(Q[k], c)
            for i in range(len(Psi)):
                R[k + i] = psub(R[k + i], self.rmul(c, Psi[i]))
            while R and not R[-1]: R.pop()
        while Q and not Q[-1]: Q.pop()
        return Q, R

    def biRead(self, g):
        """digits of g by key, as R[Z] element (digits ARE canonical reps)."""
        out = [dev(self.key, g, b) for b in range(natdeg(g) // self.Dp + 2)]
        while out and not out[-1]: out.pop()
        return out

    def shadowDev(self, f, j):
        Psi = self.biRead(self.Phi2)
        G = self.biRead(f)
        for _ in range(j):
            G = self.rp_divmod(G, Psi)[0]
        S = self.rp_divmod(G, Psi)[1]
        out = []
        for b, c in enumerate(S):                                # c already the canonical rep
            out = padd(out, pmul(c, ppow(self.key, b)))
        return out

    def dvHgt(self, A, b):
        dig = dev(self.key, A, b)
        if not dig: return INF
        return min(self.e1 * vp(c, self.p) + self.h * a
                   for a, c in enumerate(dig) if c != 0) if any(dig) else INF

    def dv2Hgt(self, A):
        if not A: return INF
        best = INF
        for b in range(natdeg(A) + 1):
            hb = self.dvHgt(A, b)
            if hb != INF:
                best = min(best, self.e2 * hb + self.u2 * b)
        return best

    def discrepancy(self, g, j):
        return psub(self.shadowDev(g, j), dev(self.Phi2, g, j))

    def hbudget_ok(self, g, mu2, detail=False):
        """check the signed hbudget on the NESTED dev grid, honestly recomputed."""
        bad = []
        for j in range(mu2):
            dj = dev(self.Phi2, g, j)
            for b in range(self.e2 * self.f2):
                db = dev(self.key, dj, b)
                for a in range(self.e1 * self.f1):
                    c = db[a] if a < len(db) else 0
                    v = vp(Fraction(c), self.p) if c != 0 else INF
                    fl = self.budgetFloor(mu2, j, a, b)
                    if v < fl:
                        bad.append((j, a, b, v, fl))
        return (len(bad) == 0, bad) if detail else len(bad) == 0

# ---------------------------------------------------------------- report helpers
PASS, FAIL = 0, 0
def check(label, ok, note=""):
    global PASS, FAIL
    tag = "PASS" if ok else "FAIL"
    if ok: PASS += 1
    else:  FAIL += 1
    print(f"  [{tag}] {label}{('  ' + note) if note else ''}")

def fmt(h): return "inf" if h == INF else str(h)

# ================================================================ the battery
def run_frame(F, mu2):
    print(f"\n================ frame {F.name} (p={F.p}, u2={F.u2}, E2={F.E2}, "
          f"margin={F.margin}, D2={F.D2}), mu2={mu2} ================")
    p = Fraction(F.p)
    thetas = [F.theta(mu2, j) for j in range(mu2)]
    print(f"  theta_j = {thetas}; Phi2 = {[str(c) for c in F.Phi2]}")

    # ---- P0: budgetFloor <-> strict line arithmetic
    ok0 = True
    for j, a, b in product(range(mu2), range(F.e1 * F.f1), range(F.e2 * F.f2)):
        fl = F.budgetFloor(mu2, j, a, b)
        for v in range(0, fl + 4):
            lhs = (v >= fl)
            rhs = (F.e1 * F.e2) * v + F.slotOffset(a, b) >= (mu2 - j) * F.E2 + 1
            if lhs != rhs: ok0 = False
    check("P0 budgetFloor v-threshold == strict-line wtCoeff >= (mu2-j')E2+1", ok0)

    # ---- TouchCert table: g = Phi2^mu2
    gk = ppow(F.Phi2, mu2)
    ok, bad = F.hbudget_ok(gk, mu2, detail=True)
    check("P3a hbudget holds VACUOUSLY for g = Phi2^mu2", ok, f"violations={bad}")
    touch = {}
    for j in range(mu2):
        hj = F.dv2Hgt(F.discrepancy(gk, j))
        touch[j] = (hj == thetas[j])
        print(f"    key-power discrepancy: j={j}  dv2Hgt={fmt(hj)}  theta={thetas[j]}"
              f"  TouchCert={'YES' if touch[j] else 'no'}")
        # the defeat exists exactly at TouchCert coordinates (elsewhere hc itself fails,
        # so the signed statement is not instantiable there)
        if touch[j]:
            check(f"P3b DEFEAT at TouchCert j={j}: signed clause1 theta+1<=h FALSE "
                  f"for g=Phi2^mu2", hj < thetas[j] + 1,
                  f"h={fmt(hj)} < theta+1={thetas[j]+1}")
    check("P3c degree fix excludes the defeat: natDegree(Phi2^mu2) == mu2*D2 (not <)",
          natdeg(gk) == mu2 * F.D2)

    # ---- slot bank
    slots = [(j0, a, b) for j0, a, b in
             product(range(mu2), range(F.e1 * F.f1), range(F.e2 * F.f2))]
    def slot_poly(j0, a, b, v, unit=1):
        mono = [Fraction(0)] * a + [Fraction(unit) * p ** v]
        return pmul(pmul(mono, ppow(F.key, b)), ppow(F.Phi2, j0))

    # ---- Family A: single tight slot
    print("  -- Family A: single-slot g, coefficient exactly AT budgetFloor --")
    print("     (slot j0,a,b | floor | excess=4-(tgt%4) | per-j: obs h_j vs theta_j+1"
          " and vs mechanism floor mech_j = (mu2-j0)E2+excess + j0 E2 - j E2 + margin)")
    tightA = []
    for (j0, a, b) in slots:
        fl = F.budgetFloor(mu2, j0, a, b)
        w = F.slotOffset(a, b); tgt = (mu2 - j0) * F.E2 - w
        excess = 4 - (tgt % 4) if tgt >= 0 else None
        g = slot_poly(j0, a, b, fl)
        assert natdeg(g) < mu2 * F.D2
        okb = F.hbudget_ok(g, mu2)
        row = []
        allok = True
        for j in range(mu2):
            h = F.dv2Hgt(F.discrepancy(g, j))
            mech = (mu2 - j0) * F.E2 + excess + j0 * F.E2 - j * F.E2 + F.margin
            row.append((j, h, mech))
            if h != INF and h < thetas[j] + 1: allok = False
            if h != INF and h == thetas[j] + 1: tightA.append((j0, a, b, j))
        print(f"     ({j0},{a},{b}) fl={fl} exc={excess} hbud={'Y' if okb else 'N'} | "
              + "  ".join(f"j={j}:h={fmt(h)}(th+1={thetas[j]+1},mech={m})"
                          for j, h, m in row))
        check(f"P1 single-slot ({j0},{a},{b}): hbudget & all h_j >= theta_j+1",
              okb and allok)
        for j, h, m in row:
            if h != INF:
                check(f"P2 mech floor at ({j0},{a},{b}) j={j}: h >= mech", h >= m,
                      f"h={fmt(h)} mech={m}")
    print(f"  P2 tight-at-theta+1 slots (h == theta_j+1): {tightA if tightA else 'NONE'}")

    # ---- Family B: all slots tight simultaneously (units 1 and a p-unit mix)
    print("  -- Family B: all-slots-tight g (two unit patterns) --")
    for tag, unitf in (("units=1", lambda i: 1), ("units=alt", lambda i: 1 + 2 * (i % 2))):
        g = []
        for i, (j0, a, b) in enumerate(slots):
            g = padd(g, slot_poly(j0, a, b, F.budgetFloor(mu2, j0, a, b), unitf(i)))
        okb = F.hbudget_ok(g, mu2)
        hs = [F.dv2Hgt(F.discrepancy(g, j)) for j in range(mu2)]
        check(f"P1 family-B({tag}): hbudget & h_j >= theta_j+1 all j",
              okb and all(h == INF or h >= thetas[j] + 1 for j, h in enumerate(hs)),
              f"h={[fmt(h) for h in hs]} theta+1={[t+1 for t in thetas]}")

    # ---- Family C: slack budgets
    for extra in (1, 2):
        g = []
        for (j0, a, b) in slots:
            g = padd(g, slot_poly(j0, a, b, F.budgetFloor(mu2, j0, a, b) + extra))
        hs = [F.dv2Hgt(F.discrepancy(g, j)) for j in range(mu2)]
        check(f"P1 family-C slack +{extra}: h_j >= theta_j+1 all j",
              all(h == INF or h >= thetas[j] + 1 for j, h in enumerate(hs)),
              f"h={[fmt(h) for h in hs]}")

    # ---- N1: negative controls, one unit below floor
    print("  -- N1: negative controls (single slot at floor-1) --")
    bites = 0
    for (j0, a, b) in slots:
        fl = F.budgetFloor(mu2, j0, a, b)
        if fl == 0: continue
        g = slot_poly(j0, a, b, fl - 1)
        okb, bad = F.hbudget_ok(g, mu2, detail=True)
        check(f"N1 control ({j0},{a},{b}) at fl-1: hbudget FAILS at exactly that slot",
              (not okb) and bad == [(j0, a, b, fl - 1, fl)])
        hs = [F.dv2Hgt(F.discrepancy(g, j)) for j in range(mu2)]
        below = [(j, h) for j, h in enumerate(hs) if h != INF and h < thetas[j] + 1]
        if below: bites += 1
        print(f"     ({j0},{a},{b}) h={[fmt(h) for h in hs]}"
              f"  below-theta+1-at={below if below else '-'}")
    check("N1 the floor BITES: some control drops below theta+1", bites > 0,
          f"{bites} controls bite")

    # ---- P4: clause 2 at TouchCert coordinates
    print("  -- P4: clause 2, f = Phi2^mu2 + g at TouchCert coordinates --")
    gsamples = []
    for (j0, a, b) in slots:                       # tight singles
        gsamples.append(slot_poly(j0, a, b, F.budgetFloor(mu2, j0, a, b)))
    gall = []
    for (j0, a, b) in slots:
        gall = padd(gall, slot_poly(j0, a, b, F.budgetFloor(mu2, j0, a, b)))
    gsamples.append(gall)
    for j in range(mu2):
        if not touch[j]: continue
        ok2 = True; obs = []
        for g in gsamples:
            f = padd(gk, g)
            h = F.dv2Hgt(F.discrepancy(f, j))
            obs.append(fmt(h))
            if h != thetas[j]: ok2 = False
        check(f"P4 clause2 at TouchCert j={j}: dv2Hgt(D(Phi2^mu2+g)) == theta_j",
              ok2, f"obs={set(obs)} theta={thetas[j]}")

# ---------------------------------------------------------------- main
def main():
    s2 = Frame("s2Tower", 2, 5)
    # cross-check the landed exact digit height 31 (C131uf.s2Witness_digit_height)
    s2extra = pmul([Fraction(0), Fraction(2) ** 6], s2.key)          # 2^6 x * key
    witness = padd(ppow(s2.Phi2, 3), s2extra)
    check("landed cross-check: s2Witness j=0 digit height == 31",
          s2.dv2Hgt(dev(s2.Phi2, witness, 0)) == 31)
    check("landed cross-check: s2Witness in-budget (mu2=3)", s2.hbudget_ok(witness, 3))
    check("landed cross-check: wtCoeff(2^6,a=1,b=1) == 31", s2.wtCoeff(6, 1, 1) == 31)
    check("landed cross-check: budgetFloor(3,0,1,1) == 6 (tight)",
          s2.budgetFloor(3, 0, 1, 1) == 6)

    frames = [(s2, 2), (s2, 3),
              (Frame("s2margin3(u2=7)", 2, 7), 2),
              (Frame("s2unit3(resLift=3)", 2, 5, lift_unit=3), 2),
              (Frame("p3mirror", 3, 5), 2), (Frame("p3mirror", 3, 5), 3)]
    for F, mu2 in frames:
        run_frame(F, mu2)

    print(f"\n==== TOTAL: {PASS} PASS, {FAIL} FAIL ====")
    return 0 if FAIL == 0 else 1

if __name__ == "__main__":
    sys.exit(main())
