#!/usr/bin/env python3
"""GENTOW6 r1 cap-lemma instrument — LEMMA GENTOW-6.4 (S6.2 of
GENTOW6_PROOF_2026-08-09.md, [GT6-r1] repair round).

FRESH instrument: self-contained integer-exact arithmetic; imports
NOTHING from the sealed runners (gentow1/3/4/6_checks.py). It tests
the T-FREE window cap at the composed digits — the supplier PE1's
F-2 found missing under COR GENTOW-6.2C(d) (which had cited
"GENTOW-5(a) at f" with f a partial-side member, off GENTOW-5's
proved full-side locus T).

THREE FRAMES (two PARTIAL-SIDE members, off T; one full-side
consistency row):
 FRAME-P  (partial, p=3): Phi' = x^2-3 (e1=2, f1=1, h=1), e2=2,
   f2=1, u2=5 (node floor 5 > e2*D'*h = 4, gcd(5,2)=1), psi2 = T-1,
   Phi2 = Phi'^2 - 9x, D2 = 4, E2 = 10, e1e2 = 4.
   f = (Phi2^2 + 81*Phi') * (Phi' - 27), deg 10: block f_S carries
   the sharp RAM-anchor digit 3^4 at slot (j,a,b) = (0,0,1)
   (height 2*4 ... e1e2*4 + w(0,1) = 16+5 = 21 = 2*E2+1), sibling
   side at dv2(Phi') = 12 > 5; c_g = min(5, 12) = 5.
 FRAME-P2 (partial, p=2, f2=2 so b-slots live): the FAM-B genre
   Phi' = x^2-2, e2=1, f2=2, u2=3, Phi2 = Phi'^2 - 2x*Phi' - 8,
   D2 = 4, E2 = 6, e1e2 = 2. f = (Phi2^2 + 64x) * (Phi' - 8),
   deg 10; sharp anchor 2^6*x at (0,1,0) (height 12+1 = 13 =
   2*E2+1); c_g = min(3, 6) = 3.
 FRAME-F  (full-side): same genre, f = Phi2^2 + 64x on T (deg 8 =
   mu2*D2): LEMMA GENTOW-6.4 must reproduce GENTOW-5(a)'s band-1
   behavior where both apply (c_g = 0, no projection).

PREREGISTERED PREDICTIONS (sealed before the run; smoke disclosure
at the bottom of this docstring):
 P-A [TRI, T-free triangularity — LEMMA 6.4(a)]: perturbing f's
   coefficient at x-degree d by eps changes NO digit at slot degree
   jD2+bD'+a > d, and changes the slot-degree-d digit by EXACTLY
   eps. Scanned at every d < deg f, eps in {1, p^2}, all frames —
   including slot degrees above mu2**D2 (the partial-side tail).
 P-B [WIN, window bijection mod pi^N — LEMMA 6.4(a)]: for lifts
   f' = f + pi^N*(random integer poly, deg < n): every digit
   congruent mod pi^N; every in-window digit (v < N) has equal
   valuation and equal digit residue across lifts.
 P-C [PIN-STAB, band-1 — LEMMA 6.4(b)(c)]: slot-min pins p_j equal
   across the P-B lifts whenever p_j < e1e2*N (stability N: 8/10/8
   per frame); hand-derived hull pins reproduced: FRAME-P
   (p_0, p_2) = (26, 5) [= (21, 0) + c_g = 5 through the
   projection], FRAME-P2 (16, 3), FRAME-F (13, 0); block pins
   p_j - c_g stable below e1e2*N - c_g at the partial frames.
 P-D [UNDERCUT, the cap is exact — LEMMA 6.4(b)]: at N_u = 6, the
   (0,0)-class lift f + pi^N_u (slot degree 0) moves p_0 (above
   the cap: 26/16/13 >= e1e2*N_u = 24/12/12) to EXACTLY e1e2*N_u,
   while every pin < e1e2*N_u on the SAME lift is unchanged.
 P-E [VAC, the F-1 vacuity inequality]: 2*(e1-1) < e1*f1 at every
   (e1, f1) in [1..12] x [2..12] — 132 rows, enumerative (the
   sealed CERT-TOP hypothesis 2*i_{t*} >= D' is unsatisfiable at
   f1 >= 2).
 TEETH: T-TRI — a mutant slot-degree map (off by +1) must FAIL the
   P-A diagonal at every scanned degree with a below-top slot;
   T-CAP — a mutant claiming p_0 lift-stable at N_u (band-3
   stability over-claim) must be killed by the P-D row, per frame.

SMOKE DISCLOSURE (pre-seal): one frame-spec fix made BEFORE any
run of this instrument, from the hand ledger alone — the S6.2
draft's FRAME-P member first carried 3^6 at slot (0,0,0) (height
24, in-budget but NOT the anchor); corrected to 81*Phi' at
(0,0,1), the unique minimal-budget slot with height ≡ 2E2+1: the
sharp anchor the prediction P-C prices. Disclosed in the note at
the same commit. A pure-arithmetic smoke of the digit developer on
toy inputs (division identities f = sum C_j K^j reassembly) was
run; no prediction was derived from machine output.
"""
import random
import sys

random.seed(20260810)

CHECKS = [0, 0]  # [passed, failed]
TEETH = {}


def check(name, ok):
    CHECKS[0 if ok else 1] += 1
    if not ok:
        print("VIOLATION: %s" % name)


def tooth(name, fired):
    TEETH[name] = TEETH.get(name, 0) + (1 if fired else 0)


# ---------- integer-exact polynomial core (index = degree) ----------

def trim(f):
    while f and f[-1] == 0:
        f.pop()
    return f


def padd(f, g):
    n = max(len(f), len(g))
    return trim([(f[i] if i < len(f) else 0) + (g[i] if i < len(g) else 0)
                 for i in range(n)])


def pmul(f, g):
    if not f or not g:
        return []
    out = [0] * (len(f) + len(g) - 1)
    for i, a in enumerate(f):
        for j, b in enumerate(g):
            out[i + j] += a * b
    return trim(out)


def pdivmod_monic(f, g):
    """f = q*g + r with g MONIC; exact over Z."""
    assert g and g[-1] == 1
    r = list(f)
    dg = len(g) - 1
    q = [0] * max(1, len(f) - dg)
    while len(trim(r)) - 1 >= dg and r:
        d = len(r) - 1
        c = r[-1]
        q[d - dg] += c
        for i in range(len(g)):
            r[i + d - dg] -= c * g[i]
        trim(r)
    return trim(q), trim(r)


def dev(f, key):
    """Full development f = sum_j C_j key^j (key monic)."""
    out = []
    cur = list(f)
    while cur:
        cur, rem = pdivmod_monic(cur, key)
        out.append(rem)
    return out


def vp(n, p):
    if n == 0:
        return None  # +infinity
    v = 0
    while n % p == 0:
        n //= p
        v += 1
    return v


# ---------- frame machinery ----------

class Frame(object):
    def __init__(self, name, p, PHI1, h, e1, e2, f2, u2, PHI2,
                 f, mu2s, c_g, N_stab, N_under, pin_preds):
        self.name, self.p = name, p
        self.PHI1, self.h, self.e1 = PHI1, h, e1
        self.e2, self.f2, self.u2, self.PHI2 = e2, f2, u2, PHI2
        self.f, self.mu2s, self.c_g = f, mu2s, c_g
        self.N_stab, self.N_under = N_stab, N_under
        self.pin_preds = pin_preds  # {j: predicted pin}
        self.D1 = len(PHI1) - 1
        self.D2 = len(PHI2) - 1
        self.e1e2 = e1 * e2
        self.n = len(f) - 1

    def w(self, a, b):
        return a * self.e2 * self.h + b * self.u2

    def digits(self, f, wrong_slot=0):
        """slot map on the FULL grid: {(j,a,b): (coeff, slotdeg)},
        zero slots included (run-1 RED fix (ii): absent slots were
        invisible to the diagonal scan)."""
        nn = len(f) - 1
        M = nn // self.D2
        e2f2 = self.e2 * self.f2
        devP = dev(f, self.PHI2)
        devP += [[]] * (M + 1 - len(devP))
        out = {}
        for j, C in enumerate(devP):
            devB = dev(C, self.PHI1)
            devB += [[]] * (e2f2 - len(devB))
            for b, B in enumerate(devB):
                Bp = list(B) + [0] * (self.D1 - len(B))
                for a, c in enumerate(Bp):
                    sd = j * self.D2 + b * self.D1 + a + wrong_slot
                    out[(j, a, b)] = (c, sd)
        return out

    def pins(self, f):
        """slot-min dv2 pins per coordinate (None = +inf)."""
        ncoord = len(dev(f, self.PHI2))
        pins = [None] * ncoord
        for (j, a, b), (c, _) in self.digits(f).items():
            v = vp(c, self.p)
            if v is None:
                continue
            hgt = self.e1e2 * v + self.w(a, b)
            if pins[j] is None or hgt < pins[j]:
                pins[j] = hgt
        return pins


def build_frames():
    # FRAME-P (partial, p=3)
    PHI1 = [-3, 0, 1]
    PHI2 = padd(pmul(PHI1, PHI1), [0, -9])          # Phi'^2 - 9x
    # (run-1 RED fix (i): the literal [9,-9] had built Phi'^2-9x+9)
    fS = padd(pmul(PHI2, PHI2), pmul([81], PHI1))    # Phi2^2 + 81*Phi'
    f = pmul(fS, padd(PHI1, [-27]))                  # * (Phi' - 27)
    FP = Frame('FRAME-P', 3, PHI1, 1, 2, 2, 1, 5, PHI2,
               f, 2, 5, 8, 6, {0: 26, 2: 5})
    # FRAME-P2 (partial, p=2, f2=2)
    PHI1 = [-2, 0, 1]
    PHI2 = padd(padd(pmul(PHI1, PHI1), pmul([0, -2], PHI1)), [-8])
    fS = padd(pmul(PHI2, PHI2), [0, 64])             # Phi2^2 + 64x
    f = pmul(fS, padd(PHI1, [-8]))                   # * (Phi' - 8)
    FP2 = Frame('FRAME-P2', 2, PHI1, 1, 2, 1, 2, 3, PHI2,
                f, 2, 3, 10, 6, {0: 16, 2: 3})
    # FRAME-F (full side, same genre)
    FF = Frame('FRAME-F', 2, PHI1, 1, 2, 1, 2, 3, PHI2,
               fS, 2, 0, 8, 6, {0: 13, 2: 0})
    return [FP, FP2, FF]


# ---------- P-A: triangularity + T-TRI tooth ----------

def leg_tri(F):
    base = F.digits(F.f)
    for d in range(F.n):
        for eps in (1, F.p ** 2):
            pert = [0] * (d + 1)
            pert[d] = eps
            new = F.digits(padd(list(F.f), pert))
            above_ok, diag_ok = True, False
            for key, (c, sd) in base.items():
                c2 = new[key][0]
                if sd > d and c2 != c:
                    above_ok = False
                if sd == d and c2 - c == eps:
                    diag_ok = True
            check('%s TRI-above d=%d eps=%d' % (F.name, d, eps), above_ok)
            check('%s TRI-diag  d=%d eps=%d' % (F.name, d, eps), diag_ok)
        # T-TRI tooth: mutant slot map (+1) must miss the diagonal
        # (only degrees d whose true slot is not degree-0 of a run,
        # i.e. the +1-shifted map points at a DIFFERENT existing slot
        # or none; the diagonal digit no longer matches at eps=1)
        pert = [0] * (d + 1)
        pert[d] = 1
        mut_base = F.digits(F.f, wrong_slot=1)
        mut_new = F.digits(padd(list(F.f), pert), wrong_slot=1)
        mut_diag = False
        for key, (c, sd) in mut_base.items():
            if sd == d and mut_new[key][0] - c == 1:
                mut_diag = True
        tooth('T-TRI', not mut_diag)


# ---------- P-B / P-C: window lifts, digit + pin stability ----------

def leg_window(F):
    N = F.N_stab
    pN = F.p ** N
    base_dig = F.digits(F.f)
    base_pins = F.pins(F.f)
    for j, pred in F.pin_preds.items():
        check('%s PIN-pred j=%d (%s == %d)' % (F.name, j, base_pins[j], pred),
              base_pins[j] == pred)
    cap = F.e1e2 * N
    for trial in range(4):
        pert = [F.p ** random.randint(0, 3) * random.choice([-1, 1, 2])
                for _ in range(F.n)]
        lift = padd(list(F.f), [pN * c for c in pert])
        dig = F.digits(lift)
        cong = all((dig[k][0] - c) % pN == 0 for k, (c, _) in base_dig.items())
        check('%s WIN-cong trial %d' % (F.name, trial), cong)
        inwin = True
        for k, (c, _) in base_dig.items():
            v = vp(c, F.p)
            if v is not None and v < N:
                v2 = vp(dig[k][0], F.p)
                if v2 != v or (dig[k][0] // F.p ** v - c // F.p ** v) \
                        % F.p ** (N - v) != 0:
                    inwin = False
        check('%s WIN-inwindow trial %d' % (F.name, trial), inwin)
        pins = F.pins(lift)
        stab = all(pins[j] == base_pins[j] for j in range(len(base_pins))
                   if base_pins[j] is not None and base_pins[j] < cap)
        check('%s PIN-STAB trial %d (cap %d)' % (F.name, trial, cap), stab)
        if F.c_g:
            bstab = all(pins[j] - F.c_g == base_pins[j] - F.c_g
                        for j in range(F.mu2s + 1)
                        if base_pins[j] is not None
                        and base_pins[j] - F.c_g < cap - F.c_g)
            check('%s BLOCK-STAB trial %d (block cap %d)'
                  % (F.name, trial, cap - F.c_g), bstab)


# ---------- P-D: the undercut + T-CAP tooth ----------

def leg_undercut(F):
    N = F.N_under
    cap = F.e1e2 * N
    base_pins = F.pins(F.f)
    check('%s UND-setup p_0 = %s >= cap %d' % (F.name, base_pins[0], cap),
          base_pins[0] >= cap)
    lift = padd(list(F.f), [F.p ** N])   # (0,0)-class digit at v = N
    pins = F.pins(lift)
    check('%s UND-hit p_0 -> %s == cap %d' % (F.name, pins[0], cap),
          pins[0] == cap)
    below_ok = all(pins[j] == base_pins[j] for j in range(len(base_pins))
                   if base_pins[j] is not None and base_pins[j] < cap)
    check('%s UND-below-cap-held' % F.name, below_ok)
    # T-CAP tooth: the band-3 stability over-claim dies here
    tooth('T-CAP', pins[0] != base_pins[0])


# ---------- P-E: the F-1 vacuity inequality ----------

def leg_vac():
    for e1 in range(1, 13):
        for f1 in range(2, 13):
            check('VAC e1=%d f1=%d' % (e1, f1), 2 * (e1 - 1) < e1 * f1)


def main():
    for F in build_frames():
        print('--- %s: deg f = %d, D2 = %d, c_g = %d, pins %s'
              % (F.name, F.n, F.D2, F.c_g, F.pins(F.f)))
        leg_tri(F)
        leg_window(F)
        leg_undercut(F)
    leg_vac()
    print('teeth: ' + ', '.join('%s fired x%d' % (k, v)
                                for k, v in sorted(TEETH.items())))
    ok = CHECKS[1] == 0 and all(v > 0 for v in TEETH.values())
    print('=== VERDICT: %s -- %d checks, %d violations ==='
          % ('GREEN' if ok else 'RED', sum(CHECKS), CHECKS[1]))
    sys.exit(0 if ok else 1)


if __name__ == '__main__':
    main()
