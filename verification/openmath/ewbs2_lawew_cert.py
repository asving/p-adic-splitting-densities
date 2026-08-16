#!/usr/bin/env python3
"""LAW E-W conversion unit (EWBS2) — certification of the PROOF'S OWN DISPLAYS.

OM-10 certified LAW E-W (mindiff_j = Theta_j + entry excess at single-crossing
geographies) as a PIN law, 54/54 crossing reads at W1/W2, and named its proof
"one careful page at the K2-division bookkeeping".  This battery certifies the
page's actual bookkeeping BEFORE the proof is written (method discipline):

  the crossing seed  G = g * Y^(b+m-1) * (Y - PHI')  divides against the
  trinomial K = Y^m + P*Y^(m-1) + c0 with the EXACT closed forms

     q_G = sum_{k=0}^{b} (-1)^k     g P^k        Y^(b-k)          (quotient)
     r_G = (-1)^(b+1) g P^(b+1) Y^(m-1)
           + sum_{k=0}^{b} (-1)^(k+1) g P^k c0   Y^(b-k)          (remainder)

  and Delta_{j'} = red(q_G), Delta_{j'-1} = red(r_G), Delta_j = 0 otherwise,
  where red is the mod-PHI' slot reduction x^N |-> (pi*w)^(N div D') x^(N mod D'),
  g = red(c * pi^alpha * Pc * x^(a+i2)) (the crossing wrap of the entry times
  the P-coefficient), for the member f = PHI2^mu2 + c pi^alpha x^a PHI'^b PHI2^j'.

CHECKS (all hard):
  EW-Q / EW-R    measured discrepancy slot DICTS == predicted dicts, bit-exact
                 (strictly stronger than the OM-10 pin law: every slot value).
  EW-PIN         mindiff_j == theta_j + excess at j in {j'-1, j'}.
  EW-HI          Delta_j empty at every other coordinate (mu2 = 3 leg).
  EW-NOX         no crossing (j' = 0, or a + i2 < D')  ==>  all Delta empty.
  EW-TIGHT       on-side rows (excess = 0): pins = theta exactly (T-E-BOUND
                 family, now at every frame where the boundary is integral).
  EW-MERGE       two entries at one slot merge coefficients (E-LIN, fresh frame).
  EW-PURE        pure power PHI2^mu2 has EMPTY shadow (in-grid cleanliness).

FRAMES (all trinomial single-crossing: e2 = 1, f2 = m, f1 = 1, h = 1, e1 = D',
PHI' = x^D' - p*w, PHI2 = PHI'^m + c2h*p^v2*x^i2*PHI'^(m-1) + c0h*p^v0):
  W1, W2   the OM-10 anchors, verbatim (54-row sweep reproduced inside).
  W5o      p = 5, w = 2 (omega != 1 axis), c2h = 2, c0h = 3.
  V1p2/V1p3  D' = 4, m = 4, i2 = 1 (u2 = 5, v2 = 1, v0 = 5, delta = 1);
             mu2 = 2 AND mu2 = 3 (the mu2 >= 3 extension; j' = 2 measured).
  V2p2/V2p3  D' = 5, m = 5, i2 = 2 (u2 = 7, delta = 2): crossing at s in {0,1}
             (the s >= 1 axis, beyond OM-10's s = 0).
  V3p2/V3p3  D' = 6, m = 3, i2 = 2 (u2 = 8, v0 = 4, delta = 2).

TEETH:
  T-EW-DELTA   mutant pin law theta + excess - delta (margin forgotten).
  T-EW-J0      mutant crossing predicate ignoring j' (coordinate-0 entries
               DO satisfy a + i2 >= D' on swept rows yet never cross).
  T-EW-SIGN    mutant quotient with all-(+) signs: slot dict must differ at
               a b >= 1 crossing row.
  T-EW-WRAP    mutant red without the omega unit: must differ at W5o.
  T-EW-COLLIDE the b = m-1 collision (P-chain lands on the k = 0 slot,
               D' | m*i2 always): the merged slot value must match the
               predicted SUM, and at W1 its valuation JUMPS (the sum is
               even) — the census sees the collision, it is not blind.

Usage: python3 ewbs2_lawew_cert.py
"""
import sys
import os

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import om10_cert as om
from om10_cert import (padd, pneg, pmul, ppow, pstrip, dev, vp, chk, tooth,
                       mkframe)


# ----------------------------------------------------------------------
# frame construction (trinomial single-crossing shape)
# ----------------------------------------------------------------------

def trinomial_frame(name, p, Dp, i2, m, v2, v0, mu2, omega=1, c2h=1, c0h=1):
    """PHI' = x^Dp - p*omega, PHI2 = PHI'^m + c2h p^v2 x^i2 PHI'^(m-1)
    + c0h p^v0.  On-side conditions asserted: u2 = Dp*v2 + i2, Dp*v0 = m*u2.
    In-grid: mu2*i2 < Dp."""
    u2 = Dp * v2 + i2
    assert Dp * v0 == m * u2, (name, 'entry t=0 not on-side')
    assert mu2 * i2 < Dp, (name, 'pure power not in-grid')
    assert u2 - Dp >= 1, (name, 'delta < 1')
    PHI1 = [-p * omega] + [0] * (Dp - 1) + [1]
    P = [0] * i2 + [c2h * p ** v2]
    PHI2 = padd(padd(ppow(PHI1, m), pmul(P, ppow(PHI1, m - 1))),
                [c0h * p ** v0])
    fr = mkframe(name, p, PHI1, 1, Dp, 1, m, mu2, u2, PHI2)
    fr.i2, fr.omega, fr.Pc, fr.c0c = i2, omega, c2h * p ** v2, c0h * p ** v0
    # sanity: K2 is the trinomial we built
    assert fr.K2[0] == [fr.c0c] and fr.K2[m - 1] == P and fr.K2[m] == [1]
    assert all(fr.K2[t] == [] for t in range(1, m - 1)), (name, 'not trinomial')
    return fr


def W_frame(name, p, mu2=2, omega=1, c2h=1, c0h=1):
    return trinomial_frame(name, p, 3, 1, 3, 3, 10, mu2, omega, c2h, c0h)


# ----------------------------------------------------------------------
# predicted discrepancy dicts (the proof's closed forms)
# ----------------------------------------------------------------------

def red_mono(coeff, xpow, fr):
    """x^N mod (x^D' - p*omega): x^N |-> (p*omega)^(N div D') x^(N mod D')."""
    w = xpow // fr.Dp
    return coeff * (fr.p * fr.omega) ** w, xpow % fr.Dp


def dict_add(d, coeff, xpow, ypow):
    key = (xpow, ypow)
    d[key] = d.get(key, 0) + coeff
    if d[key] == 0:
        del d[key]


def predicted_deltas(fr, jp, a, b, alpha, c):
    """Return (delta at coordinate jp-1, delta at coordinate jp) as slot
    dicts {(a', b'): value}, per the closed forms; (None, None) if no
    crossing.  Only valid for jp <= 1."""
    assert jp in (0, 1)
    if jp == 0 or a + fr.i2 < fr.Dp:
        return None, None
    # the crossing seed: g = c p^alpha Pc x^s, s = a + i2 - D' (the LIFT
    # of the wrap x^(a+i2) = x^s(PHI' + p*omega); no wrap factor on g —
    # the trace half is the (Y - PHI') factor's PHI'-multiple, killed by
    # the final reduction)
    gc, s = c * fr.p ** alpha * fr.Pc, a + fr.i2 - fr.Dp
    q, r = {}, {}
    for k in range(b + 1):
        cf, xr = red_mono(gc * fr.Pc ** k, s + k * fr.i2, fr)
        dict_add(q, (-1) ** k * cf, xr, b - k)
        dict_add(r, (-1) ** (k + 1) * cf * fr.c0c, xr, b - k)
    cf, xr = red_mono(gc * fr.Pc ** (b + 1), s + (b + 1) * fr.i2, fr)
    dict_add(r, (-1) ** (b + 1) * cf, xr, fr.m - 1)
    return r, q


def measured_deltas(fr, memb):
    """All mu2 discrepancy slot dicts of a member (route E, honest-subtracted),
    exactly the instrument's mindiff object but keeping the dict."""
    shm = fr.shadow_E(memb)
    hon = fr.honest(memb)
    out = []
    for j in range(fr.mu2):
        dif = [padd(list(sb), pneg(hb)) for sb, hb in
               zip(shm[j], dev(hon[j], fr.PHI1, fr.m))]
        out.append(fr.slotdict(dif))
    return out


def entry_member(fr, jp, a, b, alpha, c):
    C = pmul([c * fr.p ** alpha], pmul(ppow([0, 1], a), ppow(fr.PHI1, b)))
    return padd(ppow(fr.PHI2, fr.mu2), pmul(C, ppow(fr.PHI2, jp))), C


def pin_of(fr, d):
    best = None
    for (a, bb), v in d.items():
        ht = fr.ee * vp(v, fr.p) + fr.w(a, bb)
        best = ht if best is None else min(best, ht)
    return best


# ----------------------------------------------------------------------
# the sweep
# ----------------------------------------------------------------------

def sweep_frame(fr, include_tight=True):
    print('  -- %s: p=%d D\'=%d i2=%d m=%d u2=%d delta=%d mu2=%d omega=%d'
          % (fr.name, fr.p, fr.Dp, fr.i2, fr.m, fr.u2, fr.delta, fr.mu2,
             fr.omega))
    # EW-PURE: the pure power's shadow is EMPTY
    sh = fr.dual_shadow(ppow(fr.PHI2, fr.mu2), fr.name)
    chk('EW-PURE', all(fr.slotdict(cc) == {} for cc in sh),
        '%s pure power shadow nonempty' % fr.name)
    units = [1] if fr.p == 2 else [1, fr.p - 1]
    ncross = 0
    for jp in (0, 1):
        for a in range(fr.Dp):
            for b in range(fr.m):
                base = a + fr.u2 * b
                side = (fr.mu2 - jp) * fr.E2
                amin = (side - base) // fr.ee + 1
                alphas = [amin, amin + 1, amin + 2]
                # boundary row (excess = 0) when integral and >= 0
                if include_tight and (side - base) % fr.ee == 0 \
                        and (side - base) // fr.ee >= 0:
                    alphas.append((side - base) // fr.ee)
                for alpha in alphas:
                    excess = fr.ee * alpha + base - side
                    for c in units:
                        memb, C = entry_member(fr, jp, a, b, alpha, c)
                        mds = measured_deltas(fr, memb)
                        crosses = (jp == 1) and (a + fr.i2 >= fr.Dp)
                        if not crosses:
                            chk('EW-NOX', all(d == {} for d in mds),
                                '%s (j%d,a%d,b%d,al%d,c%d) no crossing '
                                'but nonempty %s'
                                % (fr.name, jp, a, b, alpha, c, mds))
                            continue
                        ncross += 1
                        r_pred, q_pred = predicted_deltas(
                            fr, jp, a, b, alpha, c)
                        chk('EW-R', mds[jp - 1] == r_pred,
                            '%s (j%d,a%d,b%d,al%d,c%d) remainder dict: '
                            'got %s want %s'
                            % (fr.name, jp, a, b, alpha, c,
                               mds[jp - 1], r_pred))
                        chk('EW-Q', mds[jp] == q_pred,
                            '%s (j%d,a%d,b%d,al%d,c%d) quotient dict: '
                            'got %s want %s'
                            % (fr.name, jp, a, b, alpha, c, mds[jp], q_pred))
                        for j in range(fr.mu2):
                            if j in (jp - 1, jp):
                                want = fr.theta(j) + excess
                                got = pin_of(fr, mds[j])
                                tag = 'EW-TIGHT' if excess == 0 else 'EW-PIN'
                                chk(tag, got == want,
                                    '%s (j%d,a%d,b%d,al%d,c%d) pin_%d = %s '
                                    'want %d'
                                    % (fr.name, jp, a, b, alpha, c, j,
                                       got, want))
                            else:
                                chk('EW-HI', mds[j] == {},
                                    '%s (j%d,a%d,b%d,al%d,c%d) Delta_%d '
                                    'nonempty: %s'
                                    % (fr.name, jp, a, b, alpha, c, j,
                                       mds[j]))
    print('     %d crossing rows dict-checked' % ncross)
    return ncross


def measure_jp2(fr):
    """mu2 = 3, j' = 2 rows: MEASURED ONLY (outside the theorem's j' <= 1
    scope).  Tabulate pin agreement with theta_j + excess at every
    coordinate; report, do not assert (floors asserted only)."""
    assert fr.mu2 == 3
    agree, total, rows_bad = 0, 0, []
    units = [1] if fr.p == 2 else [1, fr.p - 1]
    jp = 2
    for a in range(fr.Dp):
        for b in range(fr.m):
            base = a + fr.u2 * b
            side = (fr.mu2 - jp) * fr.E2
            amin = (side - base) // fr.ee + 1
            for alpha in (amin, amin + 1):
                excess = fr.ee * alpha + base - side
                for c in units:
                    memb, C = entry_member(fr, jp, a, b, alpha, c)
                    mds = measured_deltas(fr, memb)
                    for j in range(fr.mu2):
                        pn = pin_of(fr, mds[j])
                        if pn is not None:
                            chk('EW3-FLOOR', pn >= fr.theta(j) + 1,
                                '%s j\'=2 (a%d,b%d,al%d,c%d) pin_%d = %d '
                                '< theta+1' % (fr.name, a, b, alpha, c,
                                               j, pn))
                            # descriptive: does the naive per-coordinate
                            # law hold at every NONEMPTY coordinate?
                            total += 1
                            if pn == fr.theta(j) + excess:
                                agree += 1
                            else:
                                rows_bad.append((a, b, alpha, c, j, pn,
                                                 fr.theta(j) + excess))
    print('     %s j\'=2 MEASURED: pin = theta + excess at %d/%d NONEMPTY '
          'coordinates%s'
          % (fr.name, agree, total,
             '' if not rows_bad else '; deviations (a,b,al,c,j,pin,pred): %s'
             % rows_bad[:8]))


# ----------------------------------------------------------------------
# teeth
# ----------------------------------------------------------------------

def teeth(W1, W5o, V3p3):
    # T-EW-DELTA: margin-forgotten pin mutant at a W1 crossing row
    fr = W1
    jp, a, b = 1, 2, 1
    amin = ((2 - jp) * fr.E2 - (a + fr.u2 * b)) // fr.ee + 1
    memb, _ = entry_member(fr, jp, a, b, amin, 1)
    mds = measured_deltas(fr, memb)
    excess = fr.ee * amin + a + fr.u2 * b - (2 - jp) * fr.E2
    mut = fr.theta(0) + excess - fr.delta
    tooth('T-EW-DELTA', pin_of(fr, mds[0]) != mut and fr.delta >= 1,
          'margin-forgotten mutant not separated (delta = %d)' % fr.delta)
    # T-EW-J0: crossing predicate ignoring j': at j' = 0, a + i2 >= D'
    # the mutant predicts nonempty; measured must be empty.
    memb0, _ = entry_member(fr, 0, 2, 1, 40, 1)
    mds0 = measured_deltas(fr, memb0)
    tooth('T-EW-J0', all(d == {} for d in mds0),
          'coordinate-0 entry with a + i2 >= D\' produced a discrepancy')
    # T-EW-SIGN: all-plus-sign quotient mutant differs at b >= 1
    r_pred, q_pred = predicted_deltas(fr, jp, a, b, amin, 1)
    gc, s = fr.p ** amin * fr.Pc, a + fr.i2 - fr.Dp
    q_mut = {}
    for k in range(b + 1):
        cf, xr = red_mono(gc * fr.Pc ** k, s + k * fr.i2, fr)
        dict_add(q_mut, cf, xr, b - k)          # sign dropped
    tooth('T-EW-SIGN', q_mut != q_pred and mds[1] == q_pred,
          'sign mutant not separated from the measured dict')
    # T-EW-WRAP: omega-forgotten red mutant at W5o (omega = 2); b = m-1
    # so that the P-chain deposit wraps (x^(s+m*i2), D' | m*i2)
    fr = W5o
    jp, a, b = 1, 2, fr.m - 1
    amin = ((2 - jp) * fr.E2 - (a + fr.u2 * b)) // fr.ee + 1
    memb, _ = entry_member(fr, jp, a, b, amin, 1)
    mds = measured_deltas(fr, memb)
    r_pred, q_pred = predicted_deltas(fr, jp, a, b, amin, 1)
    om_save = fr.omega
    fr.omega = 1                                # mutant red
    r_mut, q_mut = predicted_deltas(fr, jp, a, b, amin, 1)
    fr.omega = om_save
    # the crossing wrap x^3 -> p*omega enters g itself, so BOTH dicts shift
    tooth('T-EW-WRAP',
          (r_mut, q_mut) != (r_pred, q_pred)
          and mds[0] == r_pred and mds[1] == q_pred,
          'omega mutant not separated at W5o')
    # T-EW-COLLIDE: b = m-1 at W1 — P-chain lands on the k = 0 slot
    # (D' | m*i2), the merged value is the SUM, and at W1 (p = 2,
    # c0h = c2h = omega = 1) the sum -g(c0 + P^m-red) is EVEN: the slot
    # valuation JUMPS by 1 while the k >= 1 slots hold the pin.
    fr = W1
    jp, a, b = 1, 2, fr.m - 1
    amin = ((2 - jp) * fr.E2 - (a + fr.u2 * b)) // fr.ee + 1
    memb, _ = entry_member(fr, jp, a, b, amin, 1)
    mds = measured_deltas(fr, memb)
    r_pred, q_pred = predicted_deltas(fr, jp, a, b, amin, 1)
    gc, s = fr.p ** amin * fr.Pc, a + fr.i2 - fr.Dp
    slot = (s, fr.m - 1)
    v_single = vp(gc * fr.c0c, fr.p)            # an uncollided k = 0 value
    got = mds[0].get(slot)
    tooth('T-EW-COLLIDE',
          mds[0] == r_pred and got is not None
          and vp(got, fr.p) == v_single + 1
          and pin_of(fr, mds[0]) == fr.theta(0)
          + (fr.ee * amin + a + fr.u2 * b - fr.E2),
          'collision slot: got %s (v=%s), single-path v=%d'
          % (got, None if got is None else vp(got, fr.p), v_single))


# ----------------------------------------------------------------------
# E-LIN merge at a fresh frame
# ----------------------------------------------------------------------

def merge_check(fr):
    """Two crossing entries at ONE slot merge coefficients: (c1 + c2) at
    p = 3 with c1 = 1, c2 = 2 gives 3 = p, i.e. the theorem at
    (c = 1, alpha + 1).  Fresh frame (V3p3)."""
    jp, a, b = 1, fr.Dp - 1, 1
    amin = ((fr.mu2 - jp) * fr.E2 - (a + fr.u2 * b)) // fr.ee + 1
    m1, C1 = entry_member(fr, jp, a, b, amin, 1)
    C2 = pmul([2 * fr.p ** amin], pmul(ppow([0, 1], a), ppow(fr.PHI1, b)))
    memb = padd(ppow(fr.PHI2, fr.mu2), pmul(padd(C1, C2), ppow(fr.PHI2, jp)))
    mds = measured_deltas(fr, memb)
    r_pred, q_pred = predicted_deltas(fr, jp, a, b, amin + 1, 1)
    chk('EW-MERGE', mds[jp] == q_pred and mds[jp - 1] == r_pred,
        '%s merged entry (1+2)p^%d != theorem at (c=1, alpha+1)'
        % (fr.name, amin))


# ----------------------------------------------------------------------
# main
# ----------------------------------------------------------------------

def main():
    print('== EWBS2 LAW E-W proof-display certification ==')
    W1 = W_frame('W1', 2)
    W2 = W_frame('W2', 3, c0h=2)
    W5o = W_frame('W5o', 5, omega=2, c2h=2, c0h=3)
    V1p2 = trinomial_frame('V1p2', 2, 4, 1, 4, 1, 5, 2)
    V1p3 = trinomial_frame('V1p3', 3, 4, 1, 4, 1, 5, 2, c2h=2, c0h=2)
    V1p2m3 = trinomial_frame('V1p2m3', 2, 4, 1, 4, 1, 5, 3)
    V1p3m3 = trinomial_frame('V1p3m3', 3, 4, 1, 4, 1, 5, 3, c2h=2, c0h=2)
    V2p2 = trinomial_frame('V2p2', 2, 5, 2, 5, 1, 7, 2)
    V2p3 = trinomial_frame('V2p3', 3, 5, 2, 5, 1, 7, 2, c2h=2)
    V3p2 = trinomial_frame('V3p2', 2, 6, 2, 3, 1, 4, 2)
    V3p3 = trinomial_frame('V3p3', 3, 6, 2, 3, 1, 4, 2, c2h=2, c0h=2)
    total = 0
    for fr in (W1, W2, W5o, V1p2, V1p3, V1p2m3, V1p3m3, V2p2, V2p3,
               V3p2, V3p3):
        total += sweep_frame(fr)
    for fr in (V1p2m3, V1p3m3):
        measure_jp2(fr)
    merge_check(V3p3)
    teeth(W1, W5o, V3p3)
    print()
    print('TOTAL CROSSING ROWS (dict-exact): %d' % total)
    print('CHECKS: %d, VIOLATIONS: %d' % (om.NCHK, om.NVIO))
    print('TALLY: %s' % om.TALLY)
    print('KILLS: %s' % om.KILLS)
    print('VERDICT: %s' % ('GREEN' if om.NVIO == 0 else 'RED'))
    return 0 if om.NVIO == 0 else 1


if __name__ == '__main__':
    sys.exit(main())
