#!/usr/bin/env python3
"""LAW B-S2 prover unit (C.128) -- certification of the PROOF'S OWN DISPLAYS.

OM-10 LEG B certified LAW B-S2 (cascade geography e2(f2 - t*) = 1: pure-power
top-coordinate floor attainment iff p !| binom(mu2,2) OR p !| binom(mu2,3))
as a 7/7 verdict law (B3/B4/B5, BP3..BP6).  This battery certifies the
proof's actual bookkeeping BEFORE the proof note is written (method
discipline), one Phi2-division deeper than LAW E-W:

  the pure power's development A = K^mu2 + T-hat, where T-hat is the sum of
  WRAP SEEDS of the over-grid diagonals: the (k,l,r) multinomial term
  binom-mult * P^l * c0^r * Y^(2k+l) with l >= 2 wraps x^l = x^rho (x^2)^w,
  x^2 = PHI' + pi^h*omega, producing depth-j seeds at Y^(2k+l+j) of weight
  mu2*E2 + j*delta.  Only three branches reach the top coordinate
  j* = mu2 - 1 (chain_{mu2-1}(Y^N) = 0 for N < 2mu2-2):

    PAIR   (l=2, j=1, N = 2mu2-1):  chain = Y - (mu2-1)P
    TRIPLE (l=3, j=1, N = 2mu2-2):  chain = 1
    QUAD   (l=4, j=2, N = 2mu2-2):  chain = 1     [exists iff mu2 >= 4]

  giving the EXACT top-coordinate discrepancy dict (binomial keys):

    (0,1) -> binom(mu2,2) * c2h^2 * p^(2 v2)                     [floor layer]
    (1,0) -> (binom(mu2,3) - (mu2-1)binom(mu2,2)) * c2h^3 * p^(3 v2)   [floor]
    (0,0) -> binom(mu2,4) * c2h^4 * p^(4 v2)   [mu2 >= 4; floor + delta]

  Heights: Theta_{j*} + ee*vp(digit) at the two floor slots and
  Theta_{j*} + delta + ee*vp(binom(mu2,4)) at the quad slot -- the quad
  branch reaches the top ONLY at wrap depth 2, i.e. delta above the floor
  layer, REGARDLESS of binom(mu2,4)'s unitness.  That is the B4 refutation's
  mechanism (binom(4,4) = 1 a unit yet pin = Theta + 1 = Theta + delta).

CHECKS (all hard unless marked MEASURED):
  BS2-ANCH   frame ties: B3..B5 / BP3..BP6 PHI2 byte-equal to om10_cert's
             FR_B/FR_BP; BP3 top dict == the sealed r1 bracket record
             {(0,1): 27, (1,0): 135}.
  DUAL       route R == route E on every frame (om10 instrument).
  BS2-STUBJ  the leanspec stub's j* formula (mu2-2) + (2 e2 t* + 1)/(e2 f2)
             == mu2 - 1 at every frame.
  BS2-DICT   measured slotdict(ShC_{j*}) == the predicted 3-slot dict,
             bit-exact (binomial keys).
  BS2-HT     the weight law: slot heights == Theta + ee*vp(b2), Theta +
             ee*vp(M), Theta + delta + ee*vp(b4).
  BS2-FLOOR  pin(ShC_j) >= theta(j) at EVERY coordinate (S2's floor
             corollary at this geography).
  BS2-LAW    attainment (pin == Theta_{j*}) == (p !| binom(mu2,2) or
             p !| binom(mu2,3)), every frame incl. tau/h/omega axes.
  BS2-SWAP   integer leg: M == mu2(mu2-1)(1-2mu2)/6 exactly, and
             (p!|b2 or p!|M) == (p!|b2 or p!|b3), mu2 <= 3000, p <= 199.
  BS2-TAUG   non-binomial keys (kappa1 != 0): the TWO FLOOR-LAYER digits
             (0,1), (1,0) match the binomial prediction mod p^(v+1) (all
             kappa1-decorated seeds raise weight by >= 2v(kappa1) - h >= 1,
             so the Theta-layer is exact-graded); everything else sits at
             height >= Theta + 1; the LAW verdict unchanged.  RUN-1
             FINDING (kept): the (0,0) slot is NOT protected -- the
             kappa1-triple seed (x^3 = (x - kappa1)PHI' + in-grid) lands
             there at the quad grade.
  BS2-TAUR   the refined first-kappa1-order (0,0) display
             binom(mu2,4)c2h^4 p^(4v2) - kappa1*binom(mu2,3)c2h^3 p^(3v2)
             matches measured up to height >= Theta + 2 remainders
             (bit-exact where the kappa1^2 tail is empty: T3m4 measured
             -243 = 81 - 324, T3m5 measured -405 = 405 - 810).
  BS2-STUBGAP (CONSTRUCTED REFUTATION of the stub AS STATED, kept
             verbatim-reproducible): the D' = 4, f2 = 2 frame P4
             (PHI' = x^4 - 5 over Z5, PHI2 = PHI'^2 + 5x PHI' + 25x^2;
             PARI (e,f) = (4,2)) satisfies EVERY hypothesis of
             lawBS2_pair_or_triple (e2(f2-t*) = 1, slotIdx(u2) = 1,
             f1 = 1, mu2 >= 3) yet its top coordinate is EMPTY (no wrap
             seed climbs 1 Y-power per 4 x-powers into the top band):
             TouchCert FALSE while p !| binom says attain, at mu2 = 3, 4.
             SECOND AXIS: at D' = 3 (PHI' = x^3 - p, c0 = c0h*p^2*x^2,
             PARI (3,2)) the census is the SINGLE merged digit
             (b3*c2h^2 + mu2(mu2-1)*c0h)*c2h*p^(3v2) -- unit-DEPENDENT;
             at p = 13, mu2 = 3, c0h = 2 it dies (1 + 12 = 13; residual
             disc -7 == 6 a non-QR mod 13, valid key) while
             pair-or-triple says attain.  The stub's promotion path
             REQUIRES the narrowing F.e1 = 2 (and T.f2 = 2 -- see the
             P32 probe).
  PROBE      (MEASURED ONLY) the f2 = 3, D' = 2 frame P32 (x-ful c0 =
             c0h p^4 x, the slotIdx(3u2) = 1 slice): inside the stub's
             hypotheses, outside the certified law; the seed calculus
             predicts a DIFFERENT Theta-layer census there (the P*c0
             cross-diagonal joins at wrap depth 1); tabulated as scope
             data for the stub flag.

TEETH:
  T-BS2-QUAD   the REFUTED "any in-band k-diagonal" law (att iff any
               binom(mu2,k), 2<=k<=mu2, is a p-unit) must FAIL at B4, B5
               and F5(mu2=6), while the measured (0,0) slot at B4 equals
               the predicted 16 at height Theta+delta exactly -- the
               mechanism pinpoint: the k=4 digit is PRESENT and UNIT but
               one delta-layer up.
  T-BS2-WDEPTH the wrap-depth-blind weight mutant (all seeds at the floor
               layer) predicts pin(B4) = Theta; measured Theta + 1.
  T-BS2-MIX    the naive (1,0)-digit mutant binom(mu2,3)*c2h^3*p^(3v2)
               (cross-term dropped) differs bit-exactly at BP3 (-27 vs
               measured 135).
  T-BS2-SIGN   c2h -> -c2h flips the (1,0) digit and fixes (0,1)/(0,0)
               (odd vs even c2h powers), measured exactly.
  T-BS2-OMEGA  omega-pair F5/F5o (x^2-5 vs x^2-10, same tail): top dicts
               EQUAL (the top band is omega-free: all (pi^h omega)^0), a
               lower coordinate DIFFERS (the battery would see omega).
  T-BS2-TAU    at a kappa1 != 0 frame the exact binomial dict prediction
               FAILS somewhere (the tau-tail is real), while BS2-TAUG holds.

Usage: python3 bs2_lawbs2_cert.py
"""
import sys
import os

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import om10_cert as om
from om10_cert import (padd, pneg, pmul, ppow, pstrip, dev, vp, chk, tooth,
                       mkframe, binom, top_j, FR_B, FR_BP, gp_sig_batch)


# ----------------------------------------------------------------------
# frame construction (the cascade trinomial shape, D' = 2)
# ----------------------------------------------------------------------

def cascade_frame(name, p, v2, mu2, h=1, omega=1, c2h=1, c0h=1, tau=0):
    """PHI' = x^2 + tau*x - p^h*omega  (one-sided of slope h/2 requires
    vp(tau) >= (h+1)/2 -- asserted), PHI2 = PHI'^2 + c2h p^v2 x PHI'
    + c0h p^u2, u2 = 2*v2 + h (t* = 1 entry on-side, x-power 1; c0
    on-side x-free -- slotIdx(2u2) = 0 is automatic at D' = 2)."""
    assert h % 2 == 1, (name, 'h must be coprime to e1 = 2')
    u2 = 2 * v2 + h
    assert u2 - 2 * h >= 1, (name, 'delta < 1 (TowerDatum.hfloor)')
    assert tau == 0 or 2 * vp(tau, p) >= h + 1, (name, 'key not one-sided')
    PHI1 = [-(p ** h) * omega, tau, 1]
    P = [0, c2h * p ** v2]
    PHI2 = padd(padd(pmul(PHI1, PHI1), pmul(P, PHI1)), [c0h * p ** u2])
    fr = mkframe(name, p, PHI1, h, 2, 1, 2, mu2, u2, PHI2)
    fr.v2, fr.omega, fr.c2h, fr.c0h, fr.tau = v2, omega, c2h, c0h, tau
    assert fr.K2[0] == [c0h * p ** u2] and fr.K2[1] == P \
        and fr.K2[2] == [1], (name, 'K2 not the built trinomial')
    assert fr.delta == u2 - 2 * h
    return fr


# ----------------------------------------------------------------------
# the proof's predicted top-coordinate dict (S3's closed form)
# ----------------------------------------------------------------------

def mixed_digit(mu2):
    """M = binom(mu2,3) - (mu2-1)*binom(mu2,2); closed form checked in
    BS2-SWAP."""
    return binom(mu2, 3) - (mu2 - 1) * binom(mu2, 2)


def predicted_top(fr):
    p, v2, c2h, mu2 = fr.p, fr.v2, fr.c2h, fr.mu2
    d = {}
    d[(0, 1)] = binom(mu2, 2) * c2h ** 2 * p ** (2 * v2)
    d[(1, 0)] = mixed_digit(mu2) * c2h ** 3 * p ** (3 * v2)
    if mu2 >= 4:
        d[(0, 0)] = binom(mu2, 4) * c2h ** 4 * p ** (4 * v2)
    return d


def law_want(fr):
    return (binom(fr.mu2, 2) % fr.p != 0) or (binom(fr.mu2, 3) % fr.p != 0)


# ----------------------------------------------------------------------
# per-frame sweep
# ----------------------------------------------------------------------

def sweep_binomial(fr):
    """The full hard-check battery on a binomial-key cascade frame."""
    f = ppow(fr.PHI2, fr.mu2)
    sh = fr.dual_shadow(f, fr.name)
    js = top_j(fr, 1)
    chk('BS2-STUBJ', js == fr.mu2 - 1,
        '%s stub j* = %s != mu2 - 1' % (fr.name, js))
    for j in range(fr.mu2):
        pn = fr.pin(sh[j])
        chk('BS2-FLOOR', pn is None or pn >= fr.theta(j),
            '%s floor at j=%d: pin %s < theta %d'
            % (fr.name, j, pn, fr.theta(j)))
    got = fr.slotdict(sh[js])
    want = predicted_top(fr)
    chk('BS2-DICT', got == want,
        '%s top dict: got %s want %s' % (fr.name, got, want))
    # the weight law (S2): heights of the three slots
    th, ee, dl = fr.theta(js), fr.ee, fr.delta
    b2, b4 = binom(fr.mu2, 2), binom(fr.mu2, 4)
    M = mixed_digit(fr.mu2)
    ht = lambda a, b, v: ee * v + fr.w(a, b)
    chk('BS2-HT', ht(0, 1, vp(got[(0, 1)], fr.p)) == th + ee * vp(b2, fr.p),
        '%s (0,1) height' % fr.name)
    chk('BS2-HT', ht(1, 0, vp(got[(1, 0)], fr.p)) == th + ee * vp(M, fr.p),
        '%s (1,0) height' % fr.name)
    if fr.mu2 >= 4:
        chk('BS2-HT',
            ht(0, 0, vp(got[(0, 0)], fr.p)) == th + dl + ee * vp(b4, fr.p),
            '%s (0,0) height (quad = floor + delta)' % fr.name)
    att = (fr.pin(sh[js]) == th)
    chk('BS2-LAW', att == law_want(fr),
        '%s LAW B-S2: att %s want %s' % (fr.name, att, law_want(fr)))
    return sh, got, att


def sweep_tau(fr):
    """Non-binomial key (kappa1 != 0): graded checks (S6) + the law."""
    f = ppow(fr.PHI2, fr.mu2)
    sh = fr.dual_shadow(f, fr.name)
    js = top_j(fr, 1)
    for j in range(fr.mu2):
        pn = fr.pin(sh[j])
        chk('BS2-FLOOR', pn is None or pn >= fr.theta(j),
            '%s floor at j=%d: pin %s < theta %d'
            % (fr.name, j, pn, fr.theta(j)))
    got = fr.slotdict(sh[js])
    want = predicted_top(fr)
    exact = (got == want)
    th, ee = fr.theta(js), fr.ee
    # the FLOOR-LAYER digits (0,1), (1,0): graded-exact
    for slot in ((0, 1), (1, 0)):
        wv, gv = want[slot], got.get(slot, 0)
        chk('BS2-TAUG',
            (gv - wv) % (fr.p ** (vp(wv, fr.p) + 1)) == 0,
            '%s slot %s Theta-layer digit: got %s want %s (mod p^%d)'
            % (fr.name, slot, gv, wv, vp(wv, fr.p) + 1))
    # everything else: height >= Theta + 1
    for slot, gv in got.items():
        if slot in ((0, 1), (1, 0)):
            continue
        chk('BS2-TAUG',
            ee * vp(gv, fr.p) + fr.w(*slot) >= th + 1,
            '%s slot %s below Theta+1: %s' % (fr.name, slot, gv))
    # the refined (0,0) display is EXACT (the kappa1-correction at the
    # top coordinate is completely enumerable: only the kappa1-triple's
    # (0,0) deposit -kappa1*b3*c2h^3*p^(3v2); pair and quad admit no
    # kappa1-decoration in the top band)
    refined = (binom(fr.mu2, 4) * fr.c2h ** 4 * fr.p ** (4 * fr.v2)
               if fr.mu2 >= 4 else 0) \
        - fr.tau * binom(fr.mu2, 3) * fr.c2h ** 3 * fr.p ** (3 * fr.v2)
    chk('BS2-TAUR', got.get((0, 0), 0) == refined,
        '%s refined (0,0) EXACT: got %s refined %s'
        % (fr.name, got.get((0, 0), 0), refined))
    rest = {k: v for k, v in got.items() if k != (0, 0)}
    wantf = {k: v for k, v in predicted_top(fr).items() if k != (0, 0)}
    chk('BS2-TAUR', rest == wantf,
        '%s refined dict (non-(0,0) slots) EXACT: got %s want %s'
        % (fr.name, rest, wantf))
    # BS2-TAUH: the (0,0) height min-formula (the note's Sec 5 display):
    # quad deposit at Theta + delta + ee*vp(b4), kappa1-triple deposit at
    # Theta + (2 vp(kappa1) - h) + ee*vp(b3); slot height == Theta + min
    # when the deposit valuations differ (they do on every swept frame).
    deps = [3 * fr.v2 + vp(fr.tau, fr.p) + vp(binom(fr.mu2, 3), fr.p)]
    if fr.mu2 >= 4:
        deps.append(4 * fr.v2 + vp(binom(fr.mu2, 4), fr.p))
    gv = got.get((0, 0), 0)
    if len(deps) == len(set(deps)) and gv:
        chk('BS2-TAUH', ee * vp(gv, fr.p) == th
            + min(fr.delta + ee * vp(binom(fr.mu2, 4), fr.p)
                  if fr.mu2 >= 4 else 10 ** 9,
                  (2 * vp(fr.tau, fr.p) - fr.h)
                  + ee * vp(binom(fr.mu2, 3), fr.p)),
            '%s (0,0) height min-formula: ht %s'
            % (fr.name, ee * vp(gv, fr.p)))
    else:
        chk('BS2-TAUH', gv == 0 or ee * vp(gv, fr.p) >= th + 1,
            '%s (0,0) collision case below Theta+1' % fr.name)
    att = (fr.pin(sh[js]) == th)
    chk('BS2-LAW', att == law_want(fr),
        '%s LAW B-S2 (tau key): att %s want %s'
        % (fr.name, att, law_want(fr)))
    return exact


# ----------------------------------------------------------------------
# integer leg (S5): the mixed digit and the congruence swap
# ----------------------------------------------------------------------

def integer_swap_leg():
    primes = [q for q in range(2, 200)
              if all(q % r for r in range(2, q)) and q > 1]
    bad = 0
    for mu2 in range(2, 3001):
        b2, b3 = binom(mu2, 2), binom(mu2, 3)
        M = mixed_digit(mu2)
        if 6 * M != mu2 * (mu2 - 1) * (1 - 2 * mu2):
            bad += 1
        for q in primes:
            if ((b2 % q != 0) or (M % q != 0)) \
                    != ((b2 % q != 0) or (b3 % q != 0)):
                bad += 1
    chk('BS2-SWAP', bad == 0,
        'integer leg: %d bad rows (closed form / verdict swap)' % bad)


# ----------------------------------------------------------------------
# main
# ----------------------------------------------------------------------

def main():
    print('== C.128 LAW B-S2 proof-display certification ==')

    # ---- anchor ties: the om10 frames are this builder's frames --------
    for mu2 in (3, 4, 5):
        fr_om, fr_here = FR_B(mu2), cascade_frame('Bt%d' % mu2, 2, 1, mu2,
                                                  c2h=-1, c0h=-1)
        chk('BS2-ANCH', fr_om.PHI2 == fr_here.PHI2 and fr_om.u2 ==
            fr_here.u2, 'B%d tie' % mu2)
    for mu2 in (3, 4, 5, 6):
        fr_om, fr_here = FR_BP(mu2), cascade_frame('BPt%d' % mu2, 3, 1, mu2,
                                                   c2h=-1, c0h=-1)
        chk('BS2-ANCH', fr_om.PHI2 == fr_here.PHI2 and fr_om.u2 ==
            fr_here.u2, 'BP%d tie' % mu2)

    # ---- the binomial-key frame grid -----------------------------------
    frames = []
    for mu2 in range(2, 9):                      # B: p = 2, the om10 shape
        frames.append(cascade_frame('B%d' % mu2, 2, 1, mu2, c2h=-1, c0h=-1))
    for mu2 in range(2, 10):                     # BP: p = 3 (BP9 = first
        frames.append(cascade_frame('BP%d' % mu2, 3, 1, mu2,     # p=3 no-att)
                                    c2h=-1, c0h=-1))
    for mu2 in range(3, 9):                      # F5: p = 5 fresh prime
        frames.append(cascade_frame('F5m%d' % mu2, 5, 1, mu2))
    for mu2 in (3, 4, 5):                        # F5o: omega = 2 axis
        frames.append(cascade_frame('F5om%d' % mu2, 5, 1, mu2, omega=2))
    for mu2 in (3, 4, 5):                        # H3: h = 3 axis (x^2 - 8)
        frames.append(cascade_frame('H3m%d' % mu2, 2, 2, mu2, h=3))
    for mu2 in (3, 4):                           # V2: deeper v2 (u2 = 5)
        frames.append(cascade_frame('V2m%d' % mu2, 3, 2, mu2, c0h=2))
    # unit/sign sweep at p = 3, mu2 = 3, 4
    for c2h in (1, -1, 2):
        for c0h in (1, -1, 2):
            for mu2 in (3, 4):
                frames.append(cascade_frame(
                    'U%d_%d_%d' % (mu2, c2h % 5, c0h % 5), 3, 1, mu2,
                    c2h=c2h, c0h=c0h))
    results = {}
    for fr in frames:
        sh, got, att = sweep_binomial(fr)
        results[fr.name] = (fr, sh, got, att)
        print('  %s: p=%d h=%d u2=%d delta=%d mu2=%d j*=%d pin=%s '
              'theta=%d att=%s dict=%s'
              % (fr.name, fr.p, fr.h, fr.u2, fr.delta, fr.mu2, fr.mu2 - 1,
                 fr.pin(sh[fr.mu2 - 1]), fr.theta(fr.mu2 - 1), att,
                 {k: (v, vp(v, fr.p)) for k, v in sorted(got.items())}))

    # ---- the sealed r1 bracket record (BP3) -----------------------------
    got_bp3 = results['BP3'][2]
    chk('BS2-ANCH', got_bp3 == {(0, 1): 27, (1, 0): 135},
        'BP3 sealed record: got %s' % got_bp3)

    # ---- integer leg -----------------------------------------------------
    integer_swap_leg()

    # ---- tau frames (S6) -------------------------------------------------
    tau_exact = []
    for mu2 in (3, 4, 5):
        tau_exact.append(sweep_tau(cascade_frame('T2m%d' % mu2, 2, 1, mu2,
                                                 tau=2)))
        tau_exact.append(sweep_tau(cascade_frame('T3m%d' % mu2, 3, 1, mu2,
                                                 c0h=-1, tau=3)))
    print('  tau frames: %d/%d dicts bit-equal to the binomial prediction'
          % (sum(tau_exact), len(tau_exact)))

    # ---- teeth -----------------------------------------------------------
    # T-BS2-QUAD: the refuted any-k mutant + the mechanism pinpoint at B4
    kills, pin_b4 = [], None
    for nm in ('B4', 'B5', 'F5m6'):
        fr, sh, got, att = results[nm]
        anyk = any(binom(fr.mu2, k) % fr.p != 0
                   for k in range(2, fr.mu2 + 1))
        kills.append(anyk != att)
        if nm == 'B4':
            pin_b4 = fr.pin(sh[fr.mu2 - 1])
            quad_ok = (got.get((0, 0)) == 16
                       and fr.ee * vp(16, 2) + fr.w(0, 0)
                       == fr.theta(3) + fr.delta)
    tooth('T-BS2-QUAD', all(kills) and quad_ok,
          'any-k mutant kills %s; B4 quad slot pinpoint %s'
          % (kills, quad_ok))
    # T-BS2-WDEPTH: depth-blind weight mutant says pin(B4) = Theta
    frB4 = results['B4'][0]
    tooth('T-BS2-WDEPTH', pin_b4 == frB4.theta(3) + frB4.delta
          and pin_b4 != frB4.theta(3),
          'B4 pin %s vs theta %d (mutant) / theta+delta %d (law)'
          % (pin_b4, frB4.theta(3), frB4.theta(3) + frB4.delta))
    # T-BS2-MIX: cross-term-dropped (1,0) digit at BP3
    frBP3 = results['BP3'][0]
    mut = binom(3, 3) * frBP3.c2h ** 3 * frBP3.p ** (3 * frBP3.v2)
    tooth('T-BS2-MIX', mut != got_bp3[(1, 0)] and mut == -27
          and got_bp3[(1, 0)] == 135,
          'mixed-digit mutant %s vs measured %s' % (mut, got_bp3[(1, 0)]))
    # T-BS2-SIGN: c2h sign flip at p = 3, mu2 = 3 (unit-sweep frames)
    dp = results['U3_1_1'][2]         # c2h = +1
    dm_fr = cascade_frame('SGN', 3, 1, 3, c2h=-1)
    shm = dm_fr.shadow_E(ppow(dm_fr.PHI2, 3))
    dm = dm_fr.slotdict(shm[2])
    tooth('T-BS2-SIGN',
          dm[(0, 1)] == dp[(0, 1)] and dm[(1, 0)] == -dp[(1, 0)],
          'sign flip: +c2h %s vs -c2h %s' % (dp, dm))
    # T-BS2-OMEGA: F5/F5o pair -- top dicts equal, a lower coordinate differs
    f5, f5o = results['F5m3'], results['F5om3']
    lower_differ = any(
        f5[0].slotdict(f5[1][j]) != f5o[0].slotdict(f5o[1][j])
        for j in range(2))
    tooth('T-BS2-OMEGA', f5[2] == f5o[2] and lower_differ,
          'omega pair: top equal %s, lower differ %s'
          % (f5[2] == f5o[2], lower_differ))
    # T-BS2-TAU: the exact binomial dict must FAIL somewhere on tau frames
    tooth('T-BS2-TAU', not all(tau_exact),
          'tau tail never seen: all tau dicts binomial-exact')

    # ---- the D' = 4 stub-gap frame (CONSTRUCTED REFUTATION, hard) --------
    print('  -- STUBGAP: D\' = 4, f2 = 2 (slotIdx(2u2) = 2: c0 carries'
          ' x^2; inside the stub\'s hypotheses, outside the certified'
          ' law) --')
    PHI1 = [-5, 0, 0, 0, 1]
    P = [0, 5]
    c0 = [0, 0, 25]
    PHI2 = padd(padd(pmul(PHI1, PHI1), pmul(P, PHI1)), c0)
    sigs = gp_sig_batch([(PHI2, 5, 'probe')])
    chk('BS2-STUBGAP', sigs['probe'] == ((4, 2),),
        'P4 key PARI (e,f): %s' % (sigs['probe'],))
    for mu2 in (3, 4, 5):
        fr = mkframe('P4m%d' % mu2, 5, PHI1, 1, 4, 1, 2, mu2, 5, PHI2)
        # the stub's own hypothesis arithmetic at this frame:
        # e2(f2 - t*) = 1, slotIdx((f2-t*)u2) = slotIdx(5) = 1 (1*h = 1
        # == 5 mod e1 = 4), hfloor e2*D'*h = 4 < 5 = u2, f1 = 1.
        chk('BS2-STUBGAP', 5 % 4 == 1 and 1 * (2 - 1) == 1 and 4 < 5,
            'P4 stub hypothesis arithmetic')
        f = ppow(fr.PHI2, mu2)
        sh = fr.dual_shadow(f, fr.name)
        js = top_j(fr, 1)
        for j in range(mu2):
            pn = fr.pin(sh[j])
            chk('BS2-FLOOR', pn is None or pn >= fr.theta(j),
                '%s floor at j=%d: pin %s < theta %d'
                % (fr.name, j, pn, fr.theta(j)))
        got = fr.slotdict(sh[js])
        pn = fr.pin(sh[js])
        att = (pn == fr.theta(js))
        print('  %s: j*=%d pin=%s theta=%d att=%s pair-or-triple=%s '
              'dict=%s'
              % (fr.name, js, pn, fr.theta(js), att, law_want(fr),
                 {k: (v, vp(v, 5)) for k, v in sorted(got.items())}))
        if mu2 in (3, 4):
            # the refutation rows: RHS true (p = 5 misses binom(mu2,2)),
            # TouchCert false (empty top coordinate)
            chk('BS2-STUBGAP', law_want(fr) and got == {} and not att,
                'P4m%d refutation row: law_want %s dict %s'
                % (mu2, law_want(fr), got))

    # ---- the D' = 3 stub-gap frames (second refutation axis) -------------
    # At D' = 3 the pair diagonal is IN-GRID (x^2 < x^3): no pair seed.
    # The mechanism's census: the top coordinate is the SINGLE slot (0,0)
    # with the MERGED digit (b3*c2h^2 + mu2(mu2-1)*c0h)*c2h*p^(3v2) --
    # the triple diagonal plus the P*c0 cross-diagonal (c0 carries x^2:
    # slotIdx(2u2) = 2), both at wrap depth 1.  This law is UNIT-DEPENDENT
    # (c0h enters the digit) -- pair-or-triple is unit-independent, so a
    # c0h making the merged digit die refutes the stub as stated:
    # mu2 = 3, p = 5, c0h = 4: 1 + 6*4 = 25 == 0 mod 25.
    # (Run-2 finding, kept: at p = 5, mu2 = 3 the digit-death congruence
    # c2h^2 + 6c0h == 0 COINCIDES mod 5 with the residual-degeneracy
    # disc = c2h^2 - 4c0h == 0, so hpsi-irr rescues the stub there --
    # c0h in {4, -1} give PARI (6,1), invalid keys.  At p = 13 the two
    # congruences separate: c0h = 2 kills the digit (1 + 12 = 13) with
    # disc = -7 == 6 a non-QR mod 13 -- a VALID key.)
    print('  -- STUBGAP: D\' = 3, f2 = 2 (pair in-grid; merged'
          ' triple + P*c0-cross census, unit-DEPENDENT) --')
    jobs, d3frames = [], []
    for nm, p, mu2, c0h in (('D3m3', 5, 3, 1), ('D3m7', 5, 7, 1),
                            ('D3r13', 13, 3, 2)):
        PHI1 = [-p, 0, 0, 1]
        PHI2 = padd(padd(pmul(PHI1, PHI1), pmul([0, p], PHI1)),
                    [0, 0, c0h * p ** 2])
        d3frames.append((nm, p, mu2, c0h, PHI1, PHI2))
        jobs.append((PHI2, p, nm))
    sigs = gp_sig_batch(jobs)
    for nm, p, mu2, c0h, PHI1, PHI2 in d3frames:
        chk('BS2-STUBGAP', sigs[nm] == ((3, 2),),
            '%s key PARI (e,f): %s' % (nm, sigs[nm]))
        fr = mkframe(nm, p, PHI1, 1, 3, 1, 2, mu2, 4, PHI2)
        # stub hypothesis arithmetic: slotIdx(u2) = slotIdx(4): 1*h = 1
        # == 4 mod e1 = 3 OK; e2(f2-t*) = 1; hfloor 3 < 4.
        chk('BS2-STUBGAP', 4 % 3 == 1 and 3 < 4,
            '%s stub hypothesis arithmetic' % nm)
        f = ppow(fr.PHI2, mu2)
        sh = fr.dual_shadow(f, fr.name)
        js = top_j(fr, 1)
        for j in range(mu2):
            pn = fr.pin(sh[j])
            chk('BS2-FLOOR', pn is None or pn >= fr.theta(j),
                '%s floor at j=%d: pin %s < theta %d'
                % (fr.name, j, pn, fr.theta(j)))
        got = fr.slotdict(sh[js])
        merged = (binom(mu2, 3) + mu2 * (mu2 - 1) * c0h) * p ** 3
        want = {(0, 0): merged} if merged else {}
        chk('BS2-STUBGAP', got == want,
            '%s D3 census dict: got %s want %s' % (nm, got, want))
        pn = fr.pin(sh[js])
        att = (pn == fr.theta(js))
        print('  %s: j*=%d pin=%s theta=%d att=%s pair-or-triple=%s '
              'dict=%s'
              % (fr.name, js, pn, fr.theta(js), att, law_want(fr),
                 {k: (v, vp(v, p)) for k, v in sorted(got.items())}))
        if nm == 'D3r13':
            # the refutation row: pair-or-triple TRUE via b2 = 3
            # (13 !| 3); merged digit (1 + 6*2)*13^3 = 13^4 dies
            chk('BS2-STUBGAP', law_want(fr) and not att,
                '%s refutation row: law_want %s att %s'
                % (nm, law_want(fr), att))

    # ---- the f2 = 3 probe (MEASURED ONLY) --------------------------------
    print('  -- PROBE: f2 = 3, D\' = 2 (x-ful c0; inside the stub\'s'
          ' hypotheses, outside the certified law) --')
    PHI1 = [-5, 0, 1]
    P = [0, 5]
    c0 = [0, 5 ** 4]
    PHI2 = padd(padd(ppow(PHI1, 3), pmul(P, ppow(PHI1, 2))), c0)
    sigs = gp_sig_batch([(PHI2, 5, 'p32')])
    chk('PROBE', sigs['p32'] == ((2, 3),),
        'P32 key PARI (e,f): %s' % (sigs['p32'],))
    # frozen measured records (the note's Sec 7.3 claims, machine-backed):
    # slot dicts, the number of slots, and the Theta-carrier locations.
    p32_frozen = {
        3: ({(0, 0): 40625, (0, 2): 75, (1, 1): -625},
            {(0, 0), (0, 2)}),
        4: ({(0, 0): 118750, (0, 1): 625, (0, 2): 150, (1, 0): -9375,
             (1, 1): -1750}, {(0, 0), (0, 2), (1, 1)}),
    }
    for mu2 in (3, 4):
        fr = mkframe('P32m%d' % mu2, 5, PHI1, 1, 2, 1, 3, mu2, 3, PHI2)
        f = ppow(fr.PHI2, mu2)
        sh = fr.dual_shadow(f, fr.name)
        js = top_j(fr, 2)              # t* = f2 - 1 = 2
        for j in range(mu2):
            pn = fr.pin(sh[j])
            chk('BS2-FLOOR', pn is None or pn >= fr.theta(j),
                '%s floor at j=%d: pin %s < theta %d'
                % (fr.name, j, pn, fr.theta(j)))
        got = fr.slotdict(sh[js])
        pn = fr.pin(sh[js])
        att = (pn == fr.theta(js))
        dict_want, carriers_want = p32_frozen[mu2]
        chk('PROBE', got == dict_want,
            '%s frozen dict: got %s want %s' % (fr.name, got, dict_want))
        carriers = {s for s, v in got.items()
                    if fr.ee * vp(v, fr.p) + fr.w(*s) == fr.theta(js)}
        chk('PROBE', carriers == carriers_want and att,
            '%s Theta-carriers: got %s want %s (att %s)'
            % (fr.name, sorted(carriers), sorted(carriers_want), att))
        print('  %s: j*=%d pin=%s theta=%d att=%s pair-or-triple=%s '
              'dict=%s'
              % (fr.name, js, pn, fr.theta(js), att, law_want(fr),
                 {k: (v, vp(v, 5)) for k, v in sorted(got.items())}))

    print()
    print('CHECKS: %d, VIOLATIONS: %d' % (om.NCHK, om.NVIO))
    print('TALLY: %s' % om.TALLY)
    print('KILLS: %s' % om.KILLS)
    print('VERDICT: %s' % ('GREEN' if om.NVIO == 0 else 'RED'))
    return 0 if om.NVIO == 0 else 1


if __name__ == '__main__':
    sys.exit(main())
