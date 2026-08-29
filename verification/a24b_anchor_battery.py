#!/usr/bin/env python3
"""UNIT A24B battery — the A-C.24' anchor-shift decision at the landed S2 depth-2 data.

Context: runs/wave-c/verdict_A24A.md §4 (guarded/anchored classical R2 redesign) and §5
(the ONE open risk: does the mod-Psi slot-0 reduction shift the per-digit level-1 anchor
at mu-value ties, and does the anchored carrier absorb it?).

Faithful integer-exact model of the landed S2 stack (O = Z_2 realised as Z with exact
2-adic valuation; every constructed polynomial has integer coefficients, so all reads
are exact):

  frame  F = s2Frame            : e1=2, f1=1, h=1, key Phi' = X^2 - 2, H0 = 1, K1 = F_2
  datum  L = s2Tower.levelDatum : u=5, l=2, r = X - 1 in F_2[X], seam = 5, keyDeg2 = 4
                                  K2 = AdjoinRoot(X-1) ~ F_2, root beta = 1 (mk = eval@1)
  key    Psi = Phi2 = composedKey(s2Tower) = Phi'^2 - stageLiftO(5)(1) = X^4-4X^2-4X+4
  outer  (u2, l2) = (21, 2)     : the M3-NV1 pair (C132nv4)
  g8     = Phi2^2 - 2^4 Phi'    : the RP-10 territory polynomial (C132rp10b)

Definition sources (leanfinal/Uniformity/...):
  dev            ChapB/B02   phi-adic digits: dev f 0 = f % phi, dev f (j+1) = dev (f / phi) j
  digAt          ChapB/B21   residue(x / pi^k) if pi^k | x else junk 0
  stageHeight    ChapC/C02   min_i (e1*v2(coeff_i) + h*i)  [suppVal at key X]
  slotIdx/twist  ChapC/C15   slotIdx k = k % 2 (h=1, e1=2); twistExp k = k div 2
  slotWindow     ChapC/C17   {0} always at f1 = 1
  twistRead      ChapC/C22   = digAt(2, k div 2, coeff_{k mod 2})   [eta = 1 in K1 = F_2]
  dvHgt/dvSupp   ChapC/C06   dvSupp f u l = min_j (l*dvHgt(j) + u*j), j <= natDegree f
  dvSide*        ChapC/C07   attainment set / min / max / (max-min)/l
  dvResPoly      ChapC/C25   R(Z) = sum_t twistRead(M0 - t*u, dev[jmin + t*l]) Z^t, t<=sideDeg
  dv2Hgt/Pin/Sup ChapC/C11   dv2Hgt = dvSupp at (5,2); dv2Pin(j) = dv2Hgt(dev_Psi(j));
                             dv2Supp = min_j (l2*pin + u2*j)
  dv2Res         ChapC/C38a  mk_(X-1)(dvResPoly A at A's OWN side) = R_A(1); junk 0 at A=0
  dv2ResPoly     ChapC/C38a  BARE carrier: sum_t C(dv2Res(dev2[min2+t*l2])) X^t
  shift/cocycle  ChapC/C28   shift m = m % 2; cocycle a b = 1 iff a,b both odd
  dv2FullRead    ChapC/C136l2e0  anchored absolute read at inner height k (eval@1 of the
                             fence-free line read based at the canonical slot shift k)
  GUARDED CARRIER (A24A section 4 draft, THIS unit's candidate):
       coeff t = dv2FullRead(M2min - t*u2, dev_Psi f (min2 + t*l2)),  t <= side2Deg
       (the level-2 analogue of C.25's fixed-grade twistRead: anchored at the side LINE)

Decision targets:
  Q1  do anchor shifts (jmin of the reduced slot-0 digit != jmin of the unreduced
      product) occur at mu-value ties, in reachable digit products - incl. the exact
      F1.4 territory (block digit -16*Phi' x complement sweep)?
  Q2  is the anchored read reduction-stable (absorbs the shift): full read at the
      product line height unchanged by the mod-Psi subtraction?
  Q3  on g8-territory products f = g8*b: does the bare dv2ResPoly constant-scalar law
      fail / the guarded one hold, coefficientwise?
  Q4  the recorded-unproven Dv2FullReadCarryLawStatement at S2 (beta = 1 collapses the
      root factor; the equality content survives), and the bare dv2Res product law
      after slot-0 reduction.

Honest S2 collapse note, printed in the report: K2 = F_2 has beta = 1, so ROOT-POWER
VALUES are invisible here; the battery therefore reports the anchor-shift EXPONENT
delta (the would-be root power, exact by C134p1d.lineRes_eq_shift) as an integer
observable, which does not collapse.
"""

import sys
import random
from fractions import Fraction

INF = None  # top of N-infinity


# ---------------------------------------------------------------- polynomial core
# polynomials are lists of ints, index = X-power, normalized (no trailing zeros)

def norm(p):
    while p and p[-1] == 0:
        p.pop()
    return p


def padd(p, q):
    n = max(len(p), len(q))
    return norm([(p[i] if i < len(p) else 0) + (q[i] if i < len(q) else 0)
                 for i in range(n)])


def pneg(p):
    return [-c for c in p]


def psub(p, q):
    return padd(p, pneg(q))


def pmul(p, q):
    if not p or not q:
        return []
    out = [0] * (len(p) + len(q) - 1)
    for i, a in enumerate(p):
        for j, b in enumerate(q):
            out[i + j] += a * b
    return norm(out)


def pdivmod_monic(f, g):
    """f = q*g + r with deg r < deg g; g monic with integer coeffs => exact over Z."""
    assert g and g[-1] == 1
    f = list(f)
    dg = len(g) - 1
    q = [0] * max(1, len(f) - dg)
    while len(f) - 1 >= dg and f:
        c = f[-1]
        k = len(f) - 1 - dg
        q[k] += c
        for i in range(len(g)):
            f[k + i] -= c * g[i]
        norm(f)
    return norm(q), norm(f)


def coeff(p, i):
    return p[i] if i < len(p) else 0


def natdeg(p):
    return len(p) - 1 if p else 0  # Lean natDegree 0 = 0


def v2(n):
    if n == 0:
        return INF
    n = abs(n)
    v = 0
    while n % 2 == 0:
        n //= 2
        v += 1
    return v


# ---------------------------------------------------------------- S2 frame constants
PHI1 = [-2, 0, 1]            # Phi' = X^2 - 2
PSI = [4, -4, -4, 0, 1]      # Phi2 = (X^2-2)^2 - 4X = X^4 - 4X^2 - 4X + 4
U1, L1 = 5, 2                # level datum (u, l)
U2, L2 = 21, 2               # outer pair
JUNK = {"digAt": 0, "natsub": 0}


def dev(phi, f):
    """All phi-adic digits of f (list of polys, each deg < deg phi)."""
    out = []
    f = list(f)
    while f:
        q, r = pdivmod_monic(f, phi)
        out.append(r)
        f = q
    return out


def dig_at(k, x):
    """B21 digAt at pi = 2: residue(x / 2^k) mod 2 if 2^k | x else junk 0."""
    if x == 0:
        return 0
    if x % (1 << k) != 0:
        JUNK["digAt"] += 1
        return 0
    return (abs(x) >> k) & 1


def stage_height(A):
    """C02: min_i (2*v2(a_i) + i); INF for A = 0."""
    best = INF
    for i, c in enumerate(A):
        if c != 0:
            t = 2 * v2(c) + i
            if best is INF or t < best:
                best = t
    return best


def twist_read(k, A):
    """C22 at the S2 frame: digAt(2, k//2, A.coeff(k%2)) in F_2 (eta = 1)."""
    return dig_at(k // 2, coeff(A, k % 2))


def dv_hgt(devs, j):
    return stage_height(devs[j]) if j < len(devs) else INF


def dv_supp(f):
    """C06 dvSupp at (5,2). INF iff f = 0."""
    if not f:
        return INF
    devs = dev(PHI1, f)
    best = INF
    for j in range(natdeg(f) + 1):
        h = dv_hgt(devs, j)
        if h is not INF:
            t = L1 * h + U1 * j
            if best is INF or t < best:
                best = t
    return best


def dv_side(f):
    """(sideSet, jmin, jmax, sideDeg, M0) at (5,2); None for f = 0."""
    if not f:
        return None
    devs = dev(PHI1, f)
    W = dv_supp(f)
    side = [j for j in range(natdeg(f) + 1)
            if dv_hgt(devs, j) is not INF and L1 * dv_hgt(devs, j) + U1 * j == W]
    jmin, jmax = min(side), max(side)
    M0 = dv_hgt(devs, jmin)
    return side, jmin, jmax, (jmax - jmin) // L1, M0


def dv_res_poly(f):
    """C25 dvResPoly at (5,2), based at f's OWN side min. F_2[Z] coeff list."""
    if not f:
        return None
    devs = dev(PHI1, f)
    _, jmin, _, sdeg, M0 = dv_side(f)
    out = []
    for t in range(sdeg + 1):
        k = M0 - t * U1
        if k < 0:
            JUNK["natsub"] += 1
            k = 0
        out.append(twist_read(k, devs[jmin + t * L1] if jmin + t * L1 < len(devs) else []))
    return out


def dv2_res(A):
    """C38a dv2Res: R_A evaluated at 1 in F_2 (mk (X-1)); junk 0 at A = 0."""
    if not A:
        return 0
    return sum(dv_res_poly(A)) % 2


# ---------------------------------------------------------------- level-2 gadgets
def dv2_pin(devs2, j):
    return dv_supp(devs2[j]) if j < len(devs2) else INF


def dv2_supp(f):
    if not f:
        return INF
    devs2 = dev(PSI, f)
    best = INF
    for j in range(natdeg(f) + 1):
        p = dv2_pin(devs2, j)
        if p is not INF:
            t = L2 * p + U2 * j
            if best is INF or t < best:
                best = t
    return best


def dv2_side(f):
    if not f:
        return None
    devs2 = dev(PSI, f)
    W = dv2_supp(f)
    side = [j for j in range(natdeg(f) + 1)
            if dv2_pin(devs2, j) is not INF and L2 * dv2_pin(devs2, j) + U2 * j == W]
    jmin, jmax = min(side), max(side)
    M2 = dv2_pin(devs2, jmin)  # = pinHeight (C.39)
    return side, jmin, jmax, (jmax - jmin) // L2, M2


def dv2_res_poly(f):
    """C38a (g): the BARE level-2 residual polynomial, K2[Z] = F_2[Z] coeff list."""
    if not f:
        return None
    devs2 = dev(PSI, f)
    _, jmin, _, sdeg, _ = dv2_side(f)
    return [dv2_res(devs2[jmin + t * L2] if jmin + t * L2 < len(devs2) else [])
            for t in range(sdeg + 1)]


def shift(m):
    return m % L1  # b*5 = m mod 2  =>  b = m mod 2


def cocycle(a, b):
    return (shift(a) + shift(b) - shift(a + b)) // L1


def dv2_full_read(k, P):
    """C136l2e0 dv2FullRead at inner height k, evaluated at beta = 1 in K2 = F_2.

    Coefficient t of dv2FullReadPoly reads twistRead at the inner HEIGHT
    (k - j*u)/l of the Phi'-digit at abscissa j = shift(k) + l*t; the mk (X-1)
    image is the XOR (F_2 sum) of the coefficients."""
    if k < 0:
        JUNK["natsub"] += 1
        k = 0
    devs = dev(PHI1, P) if P else []
    acc = 0
    for t in range(k + 1):
        j = shift(k) + L1 * t
        if j * U1 <= k:
            h = (k - j * U1) // L1
            acc ^= twist_read(h, devs[j] if j < len(devs) else [])
    return acc


def dv2_res_poly_anch(f):
    """THE A24A section-4 GUARDED/ANCHORED carrier: coeff t = dv2FullRead at the level-2
    side LINE height M2min - t*u2 of the lattice digit dev_Psi f (min2 + t*l2)."""
    if not f:
        return None
    devs2 = dev(PSI, f)
    _, jmin, _, sdeg, M2 = dv2_side(f)
    out = []
    for t in range(sdeg + 1):
        k = M2 - t * U2
        if k < 0:
            JUNK["natsub"] += 1
            k = 0
        d = devs2[jmin + t * L2] if jmin + t * L2 < len(devs2) else []
        out.append(dv2_full_read(k, d))
    return out


# ---------------------------------------------------------------- oracle validation
def oracles():
    fails = []

    def chk(name, got, want):
        ok = got == want
        if not ok:
            fails.append((name, got, want))
        print(f"  [{'ok' if ok else 'FAIL'}] {name}: got {got}, want {want}")

    print("== ORACLE VALIDATION (landed Lean pins) ==")
    chk("Phi2 = X^4-4X^2-4X+4 monic deg 4 (s2Phi2_natDegree)", (PSI[-1], natdeg(PSI)), (1, 4))
    d2 = dev(PHI1, PSI)
    chk("dev Phi' Phi2 = [-4X, 0, 1] (C130np5/C43)", d2, [[0, -4], [], [1]])
    chk("stageHeight(dev0 Phi2) = 5 (C130np5)", stage_height(d2[0]), 5)
    chk("twistRead(5, dev0 Phi2) = r.coeff0 = 1 (IsTestKey c5)", twist_read(5, d2[0]), 1)
    chk("dv2Hgt Psi = dvSupp Phi2 (5,2) = l*seam = 10 (dv2Hgt_testKey)", dv_supp(PSI), 10)
    G8 = psub(pmul(PSI, PSI), pmul([16], PHI1))
    chk("dv2Supp g8 (21,2) = 42 (s2Hgt3_g8)", dv2_supp(G8), 42)
    chk("g8 level-2 side = {0,2} (RP-10 territory)", dv2_side(G8)[0], [0, 2])
    chk("dvSupp corr=16Phi' = 21 (s2Hgt2_corr)", dv_supp(pmul([16], PHI1)), 21)
    chk("dv2FullRead(10, Psi) = 0 (dv2FullRead_testKey)", dv2_full_read(10, PSI), 0)
    # cocycle grid (C28 numeric regression, S2 slice)
    bad = [(a, b) for a in range(13) for b in range(13)
           if not (L1 * cocycle(a, b) == shift(a) + shift(b) - shift(a + b)
                   and cocycle(a, b) <= 1)]
    chk("cocycle grid a,b<=12 exact & {0,1} (C28)", bad, [])
    # dv2Res product law spot check (C136l2e1.dv2Res_mul) + supp multiplicativity
    rng = random.Random(24)
    badm, bads = 0, 0
    for _ in range(400):
        a = [rng.choice([-4, -2, -1, 0, 1, 2, 3, 4, 8]) for _ in range(rng.randint(1, 4))]
        b = [rng.choice([-4, -2, -1, 0, 1, 2, 3, 4, 8]) for _ in range(rng.randint(1, 4))]
        a, b = norm(a), norm(b)
        if not a or not b:
            continue
        ab = pmul(a, b)
        if dv2_res(ab) != (dv2_res(a) * dv2_res(b)) % 2:
            badm += 1
        if dv_supp(ab) != dv_supp(a) + dv_supp(b):
            bads += 1
    chk("dv2Res(ab)=dv2Res(a)dv2Res(b), 400 random (dv2Res_mul)", badm, 0)
    chk("dvSupp(ab)=dvSupp(a)+dvSupp(b), 400 random", bads, 0)
    print()
    return fails, G8


# ---------------------------------------------------------------- digit families
def digit_family():
    """Curated digit polys (deg <= 3), the slot-0 reduction arena."""
    fam = []
    # monomials 2^e X^i
    for e in range(0, 5):
        for i in range(4):
            m = [0] * i + [1 << e]
            fam.append(m)
            fam.append(pneg(m))
    # structured: Phi'-aligned and near-key shapes
    for c in [1, 2, 3, 4, -1, -2, -4]:
        fam.append(padd(PHI1, [c]))               # Phi' + c
        fam.append(padd(PHI1, [0, c]))            # Phi' + cX
        fam.append(padd(pmul(PHI1, [0, 1]), [c]))  # X*Phi' + c
    fam.append(list(PHI1))
    fam.append(pmul([2], PHI1))
    fam.append(pmul([4], PHI1))
    fam.append(pmul([16], PHI1))                  # the g8 correction digit (up to sign)
    fam.append(pneg(pmul([16], PHI1)))            # b0 of g8
    fam.append(pmul(PHI1, [0, 1]))                # X*Phi'
    fam.append([2, 1])
    fam.append([0, 2, 1])
    fam.append([2, 0, 0, 1])
    fam.append([-2, 0, 0, 1])
    fam.append([4, 0, 2, 1])
    fam.append([0, 4, 0, 1])
    # random tail
    rng = random.Random(1024)
    for _ in range(60):
        p = norm([rng.choice([-16, -8, -6, -4, -3, -2, -1, 0, 0, 1, 2, 3, 4, 6, 8, 16])
                  for _ in range(rng.randint(2, 4))])
        if p:
            fam.append(p)
    # dedup
    seen, out = set(), []
    for p in fam:
        t = tuple(p)
        if t and t not in seen:
            seen.add(t)
            out.append(p)
    return out


# ---------------------------------------------------------------- PART A
def part_A(fam):
    print("== PART A: slot-0 mod-Psi reduction at digit products (the section-5 decision) ==")
    stats = dict(pairs=0, red=0, tie=0, strict_below=0, strict_above=0,
                 surv_fail=0, shift_tie=0, shift_notie=0,
                 bare_change=0, anch_change=0)
    shift_examples = []
    deltas = {}
    for ia, a in enumerate(fam):
        for b in fam[ia:]:
            ab = pmul(a, b)
            if not ab:
                continue
            stats["pairs"] += 1
            if natdeg(ab) < 4:
                continue
            stats["red"] += 1
            q, D = pdivmod_monic(ab, PSI)
            Wab = dv_supp(ab)
            WPq = dv_supp(pmul(PSI, q)) if q else INF
            if WPq is INF:
                continue  # q = 0 impossible at deg >= 4
            kind = ("tie" if WPq == Wab else
                    ("strict_below" if Wab < WPq else "strict_above"))
            stats[{"tie": "tie", "strict_below": "strict_below",
                   "strict_above": "strict_above"}[kind]] += 1
            WD = dv_supp(D)
            ka, kb = dv_supp(a), dv_supp(b)
            if WD != ka + kb:
                stats["surv_fail"] += 1
            # anchor comparison (only meaningful when the reduced digit is nonzero)
            if D and WD == Wab:
                jab = dv_side(ab)[1]
                jD = dv_side(D)[1]
                if jD != jab:
                    delta = (jab - jD) // L1  # would-be root exponent, lineRes_eq_shift
                    deltas[delta] = deltas.get(delta, 0) + 1
                    if kind == "tie":
                        stats["shift_tie"] += 1
                        if len(shift_examples) < 6:
                            shift_examples.append((a, b, jab, jD, delta, kind))
                    else:
                        stats["shift_notie"] += 1
                # value stability of the two reads at the product line
                if dv2_res(D) != dv2_res(ab):
                    stats["bare_change"] += 1
                if dv2_full_read(Wab, D) != dv2_full_read(Wab, ab):
                    stats["anch_change"] += 1
            elif D:
                # supp changed by reduction (possible only outside survival; counted above)
                pass
    for k, v in stats.items():
        print(f"  {k:14s} = {v}")
    print(f"  anchor-shift delta histogram (would-be root exponent): {deltas}")
    for a, b, jab, jD, delta, kind in shift_examples:
        print(f"    example [{kind}] a={a} b={b}: jmin(ab)={jab} -> jmin(dev0)={jD}, delta={delta}")
    print()
    return stats, deltas


def part_A_f14(fam):
    print("== PART A': the exact F1.4 territory: b0(g8) = -16*Phi' x complement sweep ==")
    b0 = pneg(pmul([16], PHI1))
    stats = dict(g=0, red=0, tie=0, shift_tie=0, shift_notie=0,
                 bare_change=0, anch_change=0, surv_fail=0)
    for g in fam:
        ab = pmul(b0, g)
        if not ab:
            continue
        stats["g"] += 1
        if natdeg(ab) < 4:
            continue
        stats["red"] += 1
        q, D = pdivmod_monic(ab, PSI)
        Wab, WPq, WD = dv_supp(ab), dv_supp(pmul(PSI, q)), dv_supp(D)
        if WD != dv_supp(b0) + dv_supp(g):
            stats["surv_fail"] += 1
        tie = (WPq == Wab)
        if tie:
            stats["tie"] += 1
        if D and WD == Wab:
            jab, jD = dv_side(ab)[1], dv_side(D)[1]
            if jD != jab:
                stats["shift_tie" if tie else "shift_notie"] += 1
            if dv2_res(D) != dv2_res(ab):
                stats["bare_change"] += 1
            if dv2_full_read(Wab, D) != dv2_full_read(Wab, ab):
                stats["anch_change"] += 1
    for k, v in stats.items():
        print(f"  {k:14s} = {v}")
    print()
    return stats


# ---------------------------------------------------------------- PART B
def part_B(fam, G8):
    print("== PART B: the C.39 shape on g8-territory products f = g8*b ==")
    stats = dict(b=0, bare_law_fail=0, anch_law_fail=0, side_add_fail=0,
                 offside_lattice=0, offside_bare_junk=0, offside_anch_nonzero=0)
    bare_fail_ex, anch_fail_ex = [], []
    Rg8_bare = dv2_res_poly(G8)
    Rg8_anch = dv2_res_poly_anch(G8)
    for b in fam:
        if not b or natdeg(b) >= 4:
            continue
        f = pmul(G8, b)
        stats["b"] += 1
        side_f, jmin_f, jmax_f, sdeg_f, M2f = dv2_side(f)
        side_g, jmin_g, jmax_g, sdeg_g, M2g = dv2_side(G8)
        # endpoint additivity: b is a digit => its level-2 side = {0}
        if not (jmin_f == jmin_g + 0 and sdeg_f == sdeg_g):
            stats["side_add_fail"] += 1
            continue
        gamma = dv2_res(b)                    # gamma_g, bare (in F_2)
        gammaA = dv2_full_read(dv_supp(b), b)  # anchored complement read
        Rf_bare = dv2_res_poly(f)
        Rf_anch = dv2_res_poly_anch(f)
        want_bare = [(gamma * c) % 2 for c in Rg8_bare]
        want_anch = [(gammaA * c) % 2 for c in Rg8_anch]
        if Rf_bare != want_bare:
            stats["bare_law_fail"] += 1
            if len(bare_fail_ex) < 4:
                bare_fail_ex.append((b, Rf_bare, want_bare, gamma))
        if Rf_anch != want_anch:
            stats["anch_law_fail"] += 1
            if len(anch_fail_ex) < 4:
                anch_fail_ex.append((b, Rf_anch, want_anch, gammaA))
        # off-side lattice hunt on f
        devs2 = dev(PSI, f)
        for t in range(sdeg_f + 1):
            j = jmin_f + t * L2
            if j not in side_f:
                stats["offside_lattice"] += 1
                d = devs2[j] if j < len(devs2) else []
                if dv2_res(d) != 0:
                    stats["offside_bare_junk"] += 1
                k = M2f - t * U2
                if k >= 0 and dv2_full_read(k, d) != 0:
                    stats["offside_anch_nonzero"] += 1
    for k, v in stats.items():
        print(f"  {k:22s} = {v}")
    for b, got, want, g in bare_fail_ex:
        print(f"    BARE law fail at b={b}: R2(f)={got} vs gamma*R2(g8)={want} (gamma={g})")
    for b, got, want, g in anch_fail_ex:
        print(f"    ANCH law fail at b={b}: R2A(f)={got} vs gammaA*R2A(g8)={want} (gammaA={g})")
    print()
    return stats


def part_B_offside_hunt(fam, G8):
    """Wider hunt for off-side interior lattice slots in block*block products."""
    print("== PART B': off-side interior-slot hunt on block-shaped squares/products ==")
    blocks = [G8, pmul(PSI, PSI), psub(pmul(PSI, PSI), pmul([4], PHI1)),
              psub(pmul(PSI, PSI), pmul([64], PHI1)),
              padd(pmul(PSI, PSI), pmul([16], PHI1)),
              psub(pmul(PSI, PSI), pmul([16, 0, 16], [1])),
              psub(pmul(PSI, PSI), [0, 32]),
              psub(pmul(PSI, PSI), [64]), padd(pmul(PSI, PSI), [0, 0, 8])]
    found = 0
    tested = 0
    for i, g in enumerate(blocks):
        for z in blocks[i:]:
            f = pmul(g, z)
            tested += 1
            s = dv2_side(f)
            if s is None:
                continue
            side_f, jmin_f, _, sdeg_f, M2f = s
            devs2 = dev(PSI, f)
            for t in range(sdeg_f + 1):
                j = jmin_f + t * L2
                if j not in side_f:
                    d = devs2[j] if j < len(devs2) else []
                    bare = dv2_res(d)
                    k = M2f - t * U2
                    anch = dv2_full_read(k, d) if k >= 0 else 0
                    found += 1
                    print(f"    off-side slot: product #{tested}, j={j}, bare={bare}, anch={anch}, digit deg={natdeg(d) if d else '-'}")
    print(f"  products tested = {tested}, off-side interior lattice slots found = {found}")
    print()
    return found


# ---------------------------------------------------------------- PART C
def part_C(fam):
    print("== PART C: the carry law (Dv2FullReadCarryLawStatement) + slot-0 laws at S2 ==")
    stats = dict(pairs=0, carry_fail=0, carry_fail_short=0, slot0_anch_fail=0,
                 slot0_bare_fail=0, nonzero_reads=0)
    carry_fail_ex = []
    for ia, a in enumerate(fam):
        for b in fam[ia:]:
            if not a or not b:
                continue
            ka, kb = dv_supp(a), dv_supp(b)
            ab = pmul(a, b)
            stats["pairs"] += 1
            # the carry law shape (beta=1: root^delta = 1): FullRead(ka+kb, a*b)
            #   =? FullRead(ka,a)*FullRead(kb,b)
            lhs = dv2_full_read(ka + kb, ab)
            rhs = (dv2_full_read(ka, a) * dv2_full_read(kb, b)) % 2
            if lhs != rhs:
                stats["carry_fail"] += 1
                if natdeg(a) < 4 and natdeg(b) < 4:
                    stats["carry_fail_short"] += 1
                    if len(carry_fail_ex) < 4:
                        carry_fail_ex.append((a, b, ka, kb, lhs, rhs))
            if rhs == 1:
                stats["nonzero_reads"] += 1
            # slot-0 laws for digit pairs
            if natdeg(a) < 4 and natdeg(b) < 4 and natdeg(ab) >= 4:
                _, D = pdivmod_monic(ab, PSI)
                if dv2_full_read(ka + kb, D) != rhs:
                    stats["slot0_anch_fail"] += 1
                if dv2_res(D) != (dv2_res(a) * dv2_res(b)) % 2:
                    stats["slot0_bare_fail"] += 1
    for k, v in stats.items():
        print(f"  {k:18s} = {v}")
    for a, b, ka, kb, lhs, rhs in carry_fail_ex:
        print(f"    carry fail: a={a} (k={ka}), b={b} (k={kb}): full(ka+kb,ab)={lhs} vs {rhs}")
    print()
    return stats


# ================================================================ PART D (UNIT A24C)
# The NON-COLLAPSING synthetic frame: same inner tower (Phi' = X^2-2, u=5, l=2 — so
# shift/cocycle are unchanged), datum residual r := Z^2+Z+1 over K1 = F_2, so
# K2 = F_4 and root beta satisfies beta^2 = beta+1, beta^3 = 1, beta != 1: root-power
# VALUES are visible here (S2's K2 = F_2 collapse is lifted).
#
# HONEST SCOPE (recorded, per the A24C charge): this frame is SYNTHETIC.  The outer key
# Psi = Phi2 is the composed key of the d_r = 1 datum (r = X-1), not of the F4 datum
# (whose composed key would have degree D'' = D'*l*d_r = 8 and would need a fresh oracle
# set).  What Part D discriminates are therefore the CARRIER-LEVEL laws — exactly where
# the constant-vs-family question lives: dv2Res/dv2FullRead/dv2ResPolyAnch and their
# product/carry/scalar laws are stated for ANY LevelDatum and are Psi-generic (the carry
# law dv2FullRead_mul_of_eq and dv2Res_mul are Psi-FREE), so the landed frame-generic
# THEOREMS serve as this frame's oracles: if the model reproduces them, the model is a
# faithful instance of the Lean reads at this datum.
#
# Twist exponents (SOURCE: spec/EFF-HE7.md DEFINITION HE7-3, verbatim closed form
# "c_t := (s(d2u2 - tu2) + t*s(u2) - s(d2u2))/l"; implemented as the cocycle sum
# eps(M,t) = c1(M-t*u2, t*u2) + sum_{i<t} c1(u2, i*u2), the Lean-native form):
# the TWISTED carrier tw_t = beta^eps(M2,t) * anch_t is the source's own residual
# polynomial shape (HE7 SS1 CONVENTION / HE7-7' "twist carried through the residual
# assembly"); the source's C.39/.39 constant-scalar display is a claim about THIS
# carrier.

BETA = 2  # F4 element beta; encoding: int 0..3, bit0 = 1-part, bit1 = beta-part


def f4_mul(x, y):
    a0, a1 = x & 1, (x >> 1) & 1
    b0, b1 = y & 1, (y >> 1) & 1
    return ((a0 & b0) ^ (a1 & b1)) | ((((a0 & b1) ^ (a1 & b0)) ^ (a1 & b1)) << 1)


def f4_pow(x, n):
    out = 1
    for _ in range(n % 3 if x in (2, 3) else n):  # beta, beta+1 have order 3
        out = f4_mul(out, x)
    return out if x != 0 or n == 0 else 0


def f4_eval_beta(p):
    """mk r for r = Z^2+Z+1: reduce an F_2[Z] coefficient list mod r = Horner at beta."""
    acc = 0
    for c in reversed(p):
        acc = f4_mul(acc, BETA) ^ (c & 1)
    return acc


def dv2_res4(A):
    """dv2Res at the F4 datum: mk_(Z^2+Z+1) of A's own-side level-1 residual."""
    if not A:
        return 0
    return f4_eval_beta(dv_res_poly(A))


def dv2_full_read4(k, P):
    """dv2FullRead at the F4 datum: positional coefficient list of dv2FullReadPoly
    (coeff t = twistRead((k - j*u)/l, dev_j) when j = shift k + l*t prices <= k, else 0),
    then mk r = Horner at beta."""
    if k < 0:
        JUNK["natsub"] += 1
        k = 0
    devs = dev(PHI1, P) if P else []
    coeffs = []
    for t in range(k + 1):
        j = shift(k) + L1 * t
        if j * U1 <= k:
            h = (k - j * U1) // L1
            coeffs.append(twist_read(h, devs[j] if j < len(devs) else []))
        else:
            coeffs.append(0)
    return f4_eval_beta(coeffs)


def dv2_res_poly_anch4(f):
    """The guarded/anchored carrier at the F4 datum (F4-element coefficient list)."""
    if not f:
        return None
    devs2 = dev(PSI, f)
    _, jmin, _, sdeg, M2 = dv2_side(f)
    out = []
    for t in range(sdeg + 1):
        k = M2 - t * U2
        if k < 0:
            JUNK["natsub"] += 1
            k = 0
        d = devs2[jmin + t * L2] if jmin + t * L2 < len(devs2) else []
        out.append(dv2_full_read4(k, d))
    return out


def eps(M, t):
    """DEFINITION HE7-3's twist exponent at pin M, slot t (cocycle-sum form)."""
    assert t * U2 <= M
    return cocycle(M - t * U2, t * U2) + sum(cocycle(U2, i * U2) for i in range(t))


def tw_poly(f):
    """The SOURCE-faithful twisted carrier: tw_t = beta^eps(M2,t) * anch_t."""
    a = dv2_res_poly_anch4(f)
    if a is None:
        return None
    M2 = dv2_side(f)[4]
    return [f4_mul(f4_pow(BETA, eps(M2, t)), c) for t, c in enumerate(a)]


def f4_conv(p, q):
    out = [0] * (len(p) + len(q) - 1) if p and q else []
    for i, a in enumerate(p):
        for j, b in enumerate(q):
            out[i + j] ^= f4_mul(a, b)
    return out


def part_D_oracles():
    print("== PART D ORACLES (the F4 frame vs the landed frame-generic THEOREMS) ==")
    fails = []

    def chk(name, got, want):
        ok = got == want
        if not ok:
            fails.append((name, got, want))
        print(f"  [{'ok' if ok else 'FAIL'}] {name}: got {got}, want {want}")

    chk("beta^2 = beta+1, beta^3 = 1, beta != 1",
        (f4_mul(BETA, BETA), f4_pow(BETA, 3), BETA == 1), (3, 1, False))
    # eps closed form == DEFINITION HE7-3's display (the identity C136f14d proves)
    bad = [(M, t) for M in range(64) for t in range(3) if t * U2 <= M
           and L1 * eps(M, t) != t * shift(U2) + shift(M - t * U2) - shift(M)]
    chk("eps cocycle-sum == HE7-3 closed form (M<64, t<=2)", bad, [])
    # ID1: the scalar-transfer identity (C136f14d.twistExp_cocycle_transfer)
    bad = [(M, c, t) for M in range(50) for c in range(25) for t in range(3)
           if t * U2 <= M and cocycle(M, c) + eps(M, t)
           != cocycle(M - t * U2, c) + eps(M + c, t)]
    chk("ID1 c1(M,c)+eps(M,t) == c1(M-tu2,c)+eps(M+c,t)", bad, [])
    # ID2: the product identity (C136f14d.twistExp_cocycle_mul)
    bad = [(Mg, Mz, t1, t2) for Mg in range(0, 50, 3) for Mz in range(0, 50, 3)
           for t1 in range(3) for t2 in range(3)
           if t1 * U2 <= Mg and t2 * U2 <= Mz
           and cocycle(Mg, Mz) + eps(Mg, t1) + eps(Mz, t2)
           != cocycle(Mg - t1 * U2, Mz - t2 * U2) + eps(Mg + Mz, t1 + t2)]
    chk("ID2 c1(Mg,Mz)+eps(Mg,t1)+eps(Mz,t2) == c1(...)+eps(Mg+Mz,t1+t2)", bad, [])
    # the landed carry law (C136f14c.dv2FullRead_mul_of_eq) AT the F4 frame
    rng = random.Random(1441)
    badc, badm, n = 0, 0, 0
    for _ in range(600):
        a = norm([rng.choice([-4, -2, -1, 0, 1, 2, 3, 4, 8]) for _ in range(rng.randint(1, 4))])
        b = norm([rng.choice([-4, -2, -1, 0, 1, 2, 3, 4, 8]) for _ in range(rng.randint(1, 4))])
        if not a or not b:
            continue
        n += 1
        ka, kb = dv_supp(a), dv_supp(b)
        ab = pmul(a, b)
        delta = cocycle(ka, kb)
        lhs = dv2_full_read4(ka + kb, ab)
        rhs = f4_mul(f4_pow(BETA, delta), f4_mul(dv2_full_read4(ka, a), dv2_full_read4(kb, b)))
        if lhs != rhs:
            badc += 1
        if dv2_res4(ab) != f4_mul(dv2_res4(a), dv2_res4(b)):
            badm += 1
    chk(f"carry law dv2FullRead_mul_of_eq at F4 ({n} random pairs)", badc, 0)
    chk(f"dv2Res_mul at F4 ({n} random pairs)", badm, 0)
    print()
    return fails


def part_D(fam, G8):
    """The constant-vs-family discriminator.  TWO LEVELS, honestly separated:

    (I) UNREDUCED slot products (pure carry-law territory, Psi-free): the slot-t
        object digit_t(g8)*z read at its exact height (Mg - t*u2) + c_z.  At a GENUINE
        C.39 frame the landed theorem dv2FullRead_modByMonic (IsTestKey premise) makes
        the anch coefficient of f = g8*z EQUAL this read; here the reads themselves are
        computed kill-free, so level (I) is faithful at THIS frame too.
    (II) the anch/tw carriers of f = g8*z themselves: these pass through mod-Psi digit
        reduction, and at THIS synthetic frame Psi = Phi2 is NOT the F4 datum's test
        key (dvResPoly(Phi2) = 1+Z, mk_{Z^2+Z+1} image = beta^2 != 0), so the kill —
        and hence dv2FullRead_modByMonic — does NOT apply where a reduction TIE fires.
        Level (II) is therefore scoped to the kill-clean subset, with the contaminated
        products counted, leak-ACCOUNTED (additivity oracle), and reported."""
    print("== PART D: constant-vs-family DISCRIMINATOR at the F4 frame (beta != 1) ==")
    side_g, jmin_g, _, sdeg_g, Mg = dv2_side(G8)
    devs2_g = dev(PSI, G8)
    anch_g = dv2_res_poly_anch4(G8)
    tw_g = tw_poly(G8)
    stats = dict(z=0, skipped_side=0, odd_cz=0,
                 unred_fam_ok=0, unred_fam_fail=0,
                 unred_const_ok=0, unred_const_fail=0,
                 unred_tw_ok=0, unred_tw_fail=0,
                 contaminated=0, leak_acct_fail=0,
                 clean_fam_ok=0, clean_fam_fail=0,
                 clean_enacted_ok=0, clean_enacted_fail=0,
                 clean_tw_ok=0, clean_tw_fail=0,
                 contam_eq_oddcz=0)
    ex_unred, ex_radical = None, None
    for z in fam:
        if not z or natdeg(z) >= 4:
            continue
        f = pmul(G8, z)
        s = dv2_side(f)
        if s is None:
            continue
        _, jmin_f, _, sdeg_f, Mf = s
        cz = dv_supp(z)
        if not (jmin_f == jmin_g and sdeg_f == sdeg_g and Mf == Mg + cz):
            stats["skipped_side"] += 1
            continue
        stats["z"] += 1
        odd = (shift(cz) != 0)
        if odd:
            stats["odd_cz"] += 1
        gA = dv2_full_read4(cz, z)      # gamma-hat (the anchored complement read)
        # ---------- level (I): unreduced slot products ----------
        u_fam, u_const = True, True
        u_tw = True
        slot_reads = []
        for t in range(sdeg_g + 1):
            dg = devs2_g[jmin_g + t * L2] if jmin_g + t * L2 < len(devs2_g) else []
            prod = pmul(dg, z)
            kt = (Mg - t * U2) + cz
            rt = dv2_full_read4(kt, prod)
            slot_reads.append(rt)
            want_fam = f4_mul(f4_pow(BETA, cocycle(Mg - t * U2, cz)),
                              f4_mul(gA, anch_g[t]))
            want_const = f4_mul(f4_pow(BETA, cocycle(Mg, cz)),
                                f4_mul(gA, anch_g[t]))
            if rt != want_fam:
                u_fam = False
            if rt != want_const:
                u_const = False
            # twisted level (I): beta^eps(Mf,t)*r_t vs the .39 constant * beta^eps(Mg,t)*anch_g[t]
            lhs_tw = f4_mul(f4_pow(BETA, eps(Mf, t)), rt)
            rhs_tw = f4_mul(f4_mul(f4_pow(BETA, cocycle(Mg, cz)), gA),
                            f4_mul(f4_pow(BETA, eps(Mg, t)), anch_g[t]))
            if lhs_tw != rhs_tw:
                u_tw = False
        stats["unred_fam_ok" if u_fam else "unred_fam_fail"] += 1
        stats["unred_const_ok" if u_const else "unred_const_fail"] += 1
        stats["unred_tw_ok" if u_tw else "unred_tw_fail"] += 1
        if odd and u_fam and not u_const and ex_unred is None:
            ex_unred = (z, cz, gA, slot_reads,
                        [cocycle(Mg - t * U2, cz) for t in range(sdeg_g + 1)],
                        cocycle(Mg, cz))
            if sdeg_g == 1 and all(r != 0 for r in slot_reads):
                root_f = next(x for x in range(4)
                              if f4_mul(slot_reads[1], x) == slot_reads[0])
                root_g = next(x for x in range(4)
                              if f4_mul(anch_g[1], x) == anch_g[0])
                ex_radical = (z, root_f, root_g)
        # ---------- level (II): the carriers of f, kill-contamination accounting ----------
        devs2_f = dev(PSI, f)
        contam = False
        for t in range(sdeg_g + 1):
            dg = devs2_g[jmin_g + t * L2] if jmin_g + t * L2 < len(devs2_g) else []
            prod = pmul(dg, z)
            if natdeg(prod) < 4 or not prod:
                continue
            q, D = pdivmod_monic(prod, PSI)
            kt = (Mg - t * U2) + cz
            leak = dv2_full_read4(kt, pmul(PSI, q))
            if leak != 0:
                contam = True
                # leak accounting (F4 additivity): read(D) + read(Psi q) == read(prod)
                if dv2_full_read4(kt, D) ^ leak != dv2_full_read4(kt, prod):
                    stats["leak_acct_fail"] += 1
        if contam:
            stats["contaminated"] += 1
            if odd:
                stats["contam_eq_oddcz"] += 1
            continue
        anch_f = dv2_res_poly_anch4(f)
        tw_f = tw_poly(f)
        fam_ok = all(anch_f[t] == f4_mul(f4_pow(BETA, cocycle(Mg - t * U2, cz)),
                                         f4_mul(gA, anch_g[t]))
                     for t in range(sdeg_g + 1))
        stats["clean_fam_ok" if fam_ok else "clean_fam_fail"] += 1
        en_ok = all(anch_f[t] == f4_mul(f4_pow(BETA, cocycle(Mg, cz)),
                                        f4_mul(gA, anch_g[t]))
                    for t in range(sdeg_g + 1))
        stats["clean_enacted_ok" if en_ok else "clean_enacted_fail"] += 1
        pred = f4_mul(f4_pow(BETA, cocycle(Mg, cz)), gA)  # the .39 display's scalar
        twc_ok = all(f4_mul(pred, tw_g[t]) == tw_f[t] for t in range(sdeg_g + 1))
        stats["clean_tw_ok" if twc_ok else "clean_tw_fail"] += 1
    for k, v in stats.items():
        print(f"  {k:18s} = {v}")
    if ex_unred:
        z, cz, gA, reads, exps, base = ex_unred
        print(f"    UNREDUCED-level exhibit: z={z} (c_z={cz}, gamma-hat={gA}):")
        print(f"      slot reads {reads} = beta^{exps} * gamma-hat * anch(g8) — the FAMILY;")
        print(f"      the enacted constant pins exponent {base} at every slot: FALSE at the"
              f" slot(s) with exponent != {base}")
    if ex_radical:
        z, rf, rg = ex_radical
        print(f"    RADICAL exhibit at z={z}: family-weighted residual root={rf} vs"
              f" anch(g8) root={rg} (differ by a beta-power) — same-radical FAILS over the"
              f" untwisted carrier; the twisted carriers' constant law restores it")
    print()
    return stats


def part_D_product(G8):
    print("== PART D': the classical product law over the TWISTED carrier (block x block) ==")
    blocks = [G8, pmul(PSI, PSI), psub(pmul(PSI, PSI), pmul([4], PHI1)),
              psub(pmul(PSI, PSI), pmul([64], PHI1)),
              padd(pmul(PSI, PSI), pmul([16], PHI1)),
              psub(pmul(PSI, PSI), [0, 32]), psub(pmul(PSI, PSI), [64])]
    stats = dict(pairs=0, additive=0, tw_mul_ok=0, tw_mul_fail=0,
                 tw_mul_fail_uncontaminated=0, anch_mul_plain_fail=0)
    for i, g in enumerate(blocks):
        for z in blocks[i:]:
            stats["pairs"] += 1
            f = pmul(g, z)
            sg, sz, sf = dv2_side(g), dv2_side(z), dv2_side(f)
            if None in (sg, sz, sf):
                continue
            _, jg, _, dg, Mgg = sg
            _, jz, _, dz, Mzz = sz
            _, jf, _, df, Mff = sf
            if not (jf == jg + jz and df == dg + dz and Mff == Mgg + Mzz):
                continue
            stats["additive"] += 1
            tw_f, tw_g, tw_z = tw_poly(f), tw_poly(g), tw_poly(z)
            want = [f4_mul(f4_pow(BETA, cocycle(Mgg, Mzz)), c) for c in f4_conv(tw_g, tw_z)]
            want += [0] * (len(tw_f) - len(want))
            ok = tw_f == want[:len(tw_f)] and all(c == 0 for c in want[len(tw_f):])
            stats["tw_mul_ok" if ok else "tw_mul_fail"] += 1
            if not ok:
                # honesty check: is the failure kill-contaminated? (some antidiagonal
                # digit product overflows mod Psi with a NONZERO leak at its line grade
                # — the missing test-key kill of this synthetic frame)
                devs2_g, devs2_z = dev(PSI, g), dev(PSI, z)
                contam = False
                for t1 in range(dg + 1):
                    for t2 in range(dz + 1):
                        d1 = devs2_g[jg + t1 * L2] if jg + t1 * L2 < len(devs2_g) else []
                        d2 = devs2_z[jz + t2 * L2] if jz + t2 * L2 < len(devs2_z) else []
                        prod = pmul(d1, d2)
                        if not prod or natdeg(prod) < 4:
                            continue
                        q, _D = pdivmod_monic(prod, PSI)
                        kt = (Mgg - t1 * U2) + (Mzz - t2 * U2)
                        if q and dv2_full_read4(kt, pmul(PSI, q)) != 0:
                            contam = True
                if not contam:
                    stats["tw_mul_fail_uncontaminated"] += 1
            # contrast: the PLAIN (unweighted, untwisted) product over anch
            af, ag, az = dv2_res_poly_anch4(f), dv2_res_poly_anch4(g), dv2_res_poly_anch4(z)
            wp = f4_conv(ag, az)
            wp += [0] * (len(af) - len(wp))
            if af != wp[:len(af)]:
                stats["anch_mul_plain_fail"] += 1
    for k, v in stats.items():
        print(f"  {k:26s} = {v}")
    print()
    return stats


# ---------------------------------------------------------------- main
def main():
    random.seed(24)
    fails, G8 = oracles()
    if fails:
        print("!! ORACLE FAILURES — the model is NOT faithful; results below are void !!")
        for name, got, want in fails:
            print(f"   {name}: got {got}, want {want}")
        sys.exit(1)
    fam = digit_family()
    print(f"digit family size = {len(fam)}\n")
    a_stats, deltas = part_A(fam)
    af_stats = part_A_f14(fam)
    b_stats = part_B(fam, G8)
    off_found = part_B_offside_hunt(fam, G8)
    c_stats = part_C(fam)
    print("== JUNK COUNTERS (Lean junk-branch hits inside used reads) ==")
    print(f"  {JUNK}")
    print()
    print("== VERDICT LINES ==")
    q1 = a_stats["shift_tie"] + af_stats.get("shift_tie", 0)
    print(f"  Q1 anchor shifts at mu-ties: {'REALIZED' if q1 else 'NOT OBSERVED'} "
          f"({a_stats['shift_tie']} generic + {af_stats['shift_tie']} in F1.4 territory; "
          f"delta histogram {deltas})")
    q2bad = a_stats["anch_change"] + af_stats["anch_change"]
    print(f"  Q2 anchored read reduction-stable: {'YES' if q2bad == 0 else 'NO'} "
          f"({q2bad} violations)")
    q2bare = a_stats["bare_change"] + af_stats["bare_change"]
    print(f"      bare dv2Res value change under reduction at S2 (beta=1): {q2bare} "
          f"(root-power collapse: value-invisible, anchor-visible)")
    print(f"  Q3 g8 products: bare law failures = {b_stats['bare_law_fail']}, "
          f"guarded law failures = {b_stats['anch_law_fail']} "
          f"(off-side lattice slots on g8*b: {b_stats['offside_lattice']}; "
          f"wider block-product hunt found {off_found})")
    print(f"  Q4 carry law at S2: {c_stats['carry_fail']} failures over "
          f"{c_stats['pairs']} pairs ({c_stats['carry_fail_short']} among short pairs); "
          f"slot-0 anchored law fails = {c_stats['slot0_anch_fail']}, "
          f"slot-0 bare law fails = {c_stats['slot0_bare_fail']}")
    # -------- PART D (UNIT A24C): the F4 non-collapsing discriminator --------
    print()
    d_fails = part_D_oracles()
    if d_fails:
        print("!! PART D ORACLE FAILURES — the F4 model is NOT faithful; Part D void !!")
        for name, got, want in d_fails:
            print(f"   {name}: got {got}, want {want}")
        sys.exit(1)
    d_stats = part_D(fam, G8)
    dp_stats = part_D_product(G8)
    print("== PART D VERDICT LINES (UNIT A24C) ==")
    nz = d_stats["z"]
    print(f"  D0 UNREDUCED slot level (carry-law territory, kill-free; the level the landed"
          f" modByMonic theorem equates to the anch coefficients at GENUINE frames):")
    print(f"     FAMILY (slot-indexed exponents c1(Mg-t*u2,c_z)): "
          f"{d_stats['unred_fam_ok']}/{nz} hold ({d_stats['unred_fam_fail']} fail)")
    print(f"     ENACTED constant (base-pin exponent at every slot): "
          f"{d_stats['unred_const_fail']} FAILURES / {d_stats['unred_const_ok']} hold "
          f"— fails exactly at odd c_z ({d_stats['odd_cz']} of {nz}); S2 could not see"
          f" this (beta = 1 there)")
    print(f"     SOURCE law over the TWISTED reads (HE7-3 exponents, .39's display"
          f" scalar): {d_stats['unred_tw_ok']}/{nz} hold ({d_stats['unred_tw_fail']} fail)")
    print(f"  D1 carrier level, kill-clean subset ({nz - d_stats['contaminated']} of {nz};"
          f" {d_stats['contaminated']} contaminated by the synthetic frame's missing"
          f" test-key kill, all leak-accounted: {d_stats['leak_acct_fail']} accounting"
          f" failures; contaminated == odd-c_z set: {d_stats['contam_eq_oddcz']}"
          f" == {d_stats['contaminated']}):")
    print(f"     family {d_stats['clean_fam_ok']}/{nz - d_stats['contaminated']},"
          f" enacted {d_stats['clean_enacted_ok']}/{nz - d_stats['contaminated']},"
          f" twisted-.39 {d_stats['clean_tw_ok']}/{nz - d_stats['contaminated']}"
          f" (on this subset all three coincide: the exponents are constant at even c_z)")
    print(f"  D5 twisted product law tw(gz) = beta^c1(Mg,Mz) tw(g)tw(z) on additive block"
          f" pairs: {dp_stats['tw_mul_ok']}/{dp_stats['additive']}"
          f" ({dp_stats['tw_mul_fail']} failures, of which UNcontaminated ="
          f" {dp_stats['tw_mul_fail_uncontaminated']} — every failure must be"
          f" kill-contaminated for the law to stand; plain unweighted anch product"
          f" fails on {dp_stats['anch_mul_plain_fail']})")


if __name__ == "__main__":
    main()
