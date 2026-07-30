#!/usr/bin/env python3
"""kd9_ladder_cap_probe.py — UNIT KD9 (bridge campaign, area BP4, cluster
BP4-c1, GATE unit) — the ladder/cap probe.

[CM-first gate for KD6 + KD7 — NEW at blueprint REV 2 (F5); explicit
dependency of both provers, sequenced FIRST (KD9(gate) → KD6 → KD7).]

STATEMENT (blueprint BRIDGE_BP4_KERNELS_2026-07-30.md §4 KD9 + §3.D attempt
material): on the KD1 boxes (p = 2 cubic 2^24 at N = 8; quartic
RS-conditioned cylinder 2^26 at N = 10),
  (i)  verify the STRICT key-weight climb per recentering empirically
       (D.10's DERIVED content, the KD6 ladder law: #recenterings <=
       D(n)·(w_final − w_init) via the (1/D(n))·ℤ weight lattice) and
       SEARCH for a recentering with ZERO ladder gain — a witness REFUTES
       KD6's ladder law as sketched;
  (ii) fit w_final against 1 + vdisc f and SEARCH for super-linear growth —
       a growing-trend finding refutes EVERY constant-c(n) candidate for
       KD7 (the weight cap w_final <= c(n)·(1 + vdisc f) through (P2)'s
       leaf-different term, L5fix Invariant-2 — THE deep open core).
KD10's schedulable WeightCharge route (ladder + cap + REC-DISC ⟹
WeightChargeFullP with s := 2·D(n)·c(n)) consumes exactly the two laws this
probe stresses; a finding on either leg reroutes the corresponding prover
to its obstruction-record fallback before any Lean effort is spent.

DEPS: verification/ infra (KD1's box iterators + history extractor; the
state_track_probes (t3) ladder-restart recognizer is the (i)-leg's
recognizer — its D.10 prediction "none fire at these depths" is re-sealed
here).

SEALED PREDICTIONS (Q6 discipline — sealed 2026-07-30, BEFORE any run):
  P1 (ladder leg, sealed CLEAN): ZERO recenterings with zero key-weight
      gain in either box — every recentering strictly climbs the continuing
      cluster's ladder weight (D.10 derived; consistent with the
      state_track_probes t3 recognizer having found none).  A witness is a
      FINDING refuting KD6's law as sketched (and with it the KD10 route),
      recorded with the full node context.
  P2 (cap leg, sealed LINEAR-ADEQUATE): w_final <= c·(1 + vdisc f) holds on
      both boxes for a constant c; the probe reports the empirical minimal
      c per box and per fixed-degree family.  A super-linear trend in the
      fit (w_final/(1 + vdisc) growing along an increasing-vdisc family) is
      a FINDING against every constant c(n) candidate — KD7 rerouted to its
      obstruction record naming the unbounded-ladder shape.
  Scope fence: both X-side targets carry existential constants; this gate
  is candidate-stress + growth detection, never ∀-refutation of the
  existential statements themselves.

OUTPUT (run phase): PASS/FINDING rows appended to
probe_results_2026-07-30.txt; JSON to results/kd9_ladder_cap.json; exit
0 = P1+P2 clean, 1 = FINDING.

STATUS: IMPLEMENTED + RUN 2026-07-30 (this pass).  The E-phase skeleton's
body pieces are filled per the spec above; the sealed predictions P1-P2 are
UNTOUCHED (they were on record before this implementation existed).
Recorded deviation (KD1 precedent): exit 2 = internal validation-row
failure (V1-V6 below; infrastructure inconsistency, distinct from a sealed
FINDING).

IMPLEMENTATION NOTES (reuse + deviations, per the DEPS honesty clause):
 - REUSE: the exact p=2 integer machinery of state_track_probes.py (VTA,
   dev4, wpair, digB, _lower_hull, _shift3, F4_SQ) and the KD1 probe's
   validated walkers/tables (kd1_sn_refuter_probe: VD_A, SF_SET, disc3,
   disc4_int, v2_int).  The two walkers below are the KD1 walkers with the
   D.10 LADDER WEIGHT threaded through (box A: mu = the recentering slope
   h, w_init = 0 at the key creation, exactly track_cubic's prev_mu; box
   B: the Phi-frame consumed side value w0, w_init = 4, exactly
   track_quartic's prev_w0).  Validation gates V2/V5 tie the per-member
   recentering counts to the KD1 run's stored histograms (same boxes,
   fresh walk).
 - RECENTERING SCOPE (the P1 noun, recorded): a "recentering" is an
   in-loop ladder move (slope-h recentering box A / RS self-loop box B) —
   the (t3) recognizer face.  The level-0 repeated-factor selection is the
   KEY-CREATION node (t1), not a ladder recentering; KD1's countPop-face
   npop = nrec + 1 deviation note applies.  CONSEQUENCE FOR KD6's Lean
   carrier (report-only): the typed climb law charges EVERY counted
   .recT1/.t4 node including the key-creation node, whose empirical
   ladder gain at w_init is 0 — a KeyWeightData INSTANCE for the real
   engine must therefore use a shifted functional (e.g. w = mu +
   (1/D)·#counted-nodes), which the abstract carrier permits; the probe's
   P1 leg stresses the recentering climbs, which is where the
   mathematical content lives.
 - LADDER LATTICE (report-only row): all observed gains are integers at
   these boxes (max denominator reported; D(n)-lattice consistency).
 - CAP FIT SCOPE (recorded): the fit population is members with >= 1
   recentering (the ladder actually moved; zero-recentering members have
   w_final = w_init, a c-free triviality).  Box A vdisc is the in-box
   read (exact iff < 8; censored '>=8' members reported as a separate
   floor row with ratio computed at the vd = 8 floor — an UPPER bound on
   the true ratio, conservative for candidate stress).  Box B vdisc is
   the exact big-integer v2 (disc = 0 members excluded and tallied).
   DEEP members ride with their observable-prefix w_final (lower bounds),
   tallied separately.
 - TREND RULE operationalized (implementation detail; P2 fixed only the
   direction semantics; same shape as KD1 leg (c)): per box, per exact
   vdisc bucket with >= 1000 members, the bucket statistic is
   max w_final/(1 + vd); verdict GROWING iff the sequence is
   non-decreasing in vd AND last > first; FLAT iff constant;
   NON-MONOTONE otherwise.  Full unfiltered tables go to the JSON.
"""

import json
import os
import sys
import time
from fractions import Fraction
from multiprocessing import Pool

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
RESULTS_TXT = os.path.join(HERE, 'probe_results_2026-07-30.txt')
OUTJSON = os.path.join(HERE, 'results', 'kd9_ladder_cap.json')
KD1JSON = os.path.join(HERE, 'results', 'kd1_sn_refuter.json')

from state_track_probes import (MA, NA, MB, NB, VTA, F4_SQ,  # noqa: E402
                                dev4, wpair, digB, _lower_hull, _shift3)
from kd1_sn_refuter_probe import (VD_A, SF_SET, disc3, disc4_int,  # noqa: E402
                                  v2_int)

E_PHASE = False           # body implemented 2026-07-30 (was the E-phase flag)
NPROC = 24
STEP_CAP = 64
SUPPORT_MIN = 1000

LINES = []
CHECKS = []


def emit(line):
    LINES.append(line)
    print(line, flush=True)


def check(name, ok, detail=''):
    CHECKS.append((name, bool(ok), detail))
    emit('[%s] %s%s' % ('PASS' if ok else 'FINDING', name,
                        ('  ' + detail) if detail else ''))


# ======================================================================
# box A: cubic 2^24 at N=8 — KD1 walker + D.10 ladder weight (track_cubic
# prev_mu face: w_init = 0 at key creation, mu = recentering slope)
# ======================================================================
def kd9_cubic(a2, a1, a0):
    """-> None (fbar squarefree: no key, no ladder) or
    (nrec, zg, ming, maxden, w_final, deep, anom): in-loop recenterings,
    zero-gain events (mu_new <= mu_prev — the t3 recognizer), min gain,
    max gain denominator, final ladder weight (Fraction), deep flag,
    engine anomalies."""
    A, B, C = a2 & 1, a1 & 1, a0 & 1
    if (A, B, C) in SF_SET:
        return None
    if (A, B, C) == (1, 0, 0):
        c, mode = 0, 2
    elif (A, B, C) == (0, 1, 0):
        c, mode = 1, 2
    elif (A, B, C) == (0, 0, 0):
        c, mode = 0, 3
    else:
        c, mode = 1, 3
    nrec = zg = anom = 0
    mu = Fraction(0)                     # w_init = 0 (recorded convention)
    ming = None
    maxden = 1
    b2 = (a2 + 3 * c) % MA
    b1 = (a1 + 2 * a2 * c + 3 * c * c) % MA
    b0 = (a0 + a1 * c + a2 * c * c + c ** 3) % MA

    def step(mu_new):
        nonlocal nrec, zg, ming, maxden, mu
        nrec += 1
        g = mu_new - mu
        if g <= 0:
            zg += 1
        if ming is None or g < ming:
            ming = g
        if g.denominator > maxden:
            maxden = g.denominator
        mu = mu_new

    for _ in range(STEP_CAP):
        v0, v1, v2c = VTA[b0], VTA[b1], VTA[b2]
        if v0 >= NA:
            return nrec, zg, ming, maxden, mu, True, anom
        if mode == 3:
            if 3 * v1 >= 2 * v0 and 3 * v2c >= v0:
                if v0 % 3:
                    return nrec, zg, ming, maxden, mu, False, anom
                h = v0 // 3
                e2 = ((b2 >> h) & 1) if v2c == h else 0
                e1 = ((b1 >> (2 * h)) & 1) if v1 == 2 * h else 0
                if (e2, e1) != (1, 1):
                    return nrec, zg, ming, maxden, mu, False, anom
                step(Fraction(h))
                b2, b1, b0 = _shift3(b2, b1, b0, 1 << h)
                continue
            sides = _lower_hull([(0, v0), (1, v1), (2, v2c), (3, 0)])
            cont = None
            for (i_lo, i_hi, rise) in sides:
                if i_hi - i_lo == 1 or (rise & 1):
                    continue
                h = rise >> 1
                va = v2c if i_lo == 0 else 0
                if i_lo == 0:
                    d1 = ((b1 >> (va + h)) & 1) if v1 == va + h else 0
                else:
                    d1 = ((b2 >> h) & 1) if v2c == h else 0
                if d1 == 0:
                    cont = h
            if cont is None:
                return nrec, zg, ming, maxden, mu, False, anom
            step(Fraction(cont))
            b2, b1, b0 = _shift3(b2, b1, b0, 1 << cont)
            mode = 2
            continue
        # mode == 2: pair cluster anchored at (2, va)
        va = v2c
        if v0 - va <= 0:
            return nrec, zg, ming, maxden, mu, True, anom + 1000
        if 2 * v1 < va + v0:
            return nrec, zg, ming, maxden, mu, False, anom
        rel = v0 - va
        if rel & 1:
            return nrec, zg, ming, maxden, mu, False, anom
        h = rel >> 1
        d1 = ((b1 >> (va + h)) & 1) if v1 == va + h else 0
        if d1:
            return nrec, zg, ming, maxden, mu, False, anom
        step(Fraction(rel, 2))
        b2, b1, b0 = _shift3(b2, b1, b0, 1 << h)
    return nrec, zg, ming, maxden, mu, True, anom + 10000


def worker_cubic(a2):
    n_sf = 0
    zg_wit = []
    nrec_hist = {}
    ming = None
    maxden = 1
    tab = {}          # exact vd -> [n, max_wf] over nrec>=1 members
    cens = [0, None]  # censored '>=8' row: [n, max_wf]
    deep_cnt = 0
    anom = 0
    maxr = (Fraction(0), None)
    for a1 in range(MA):
        for a0 in range(MA):
            r = kd9_cubic(a2, a1, a0)
            if r is None:
                n_sf += 1
                continue
            nrec, zg, mg, mden, wf, deep, an = r
            anom += an
            if deep:
                deep_cnt += 1
            if zg:
                zg_wit.append((a2, a1, a0, nrec, zg))
            if nrec == 0:
                continue
            nrec_hist[nrec] = nrec_hist.get(nrec, 0) + 1
            if ming is None or (mg is not None and mg < ming):
                ming = mg
            if mden > maxden:
                maxden = mden
            vd = VD_A[disc3(a2, a1, a0) % MA]
            if vd >= NA:              # censored '>=8' (in-box read marker NA)
                cens[0] += 1
                if cens[1] is None or wf > cens[1]:
                    cens[1] = wf
            else:
                row = tab.setdefault(vd, [0, Fraction(0)])
                row[0] += 1
                if wf > row[1]:
                    row[1] = wf
                fr = Fraction(wf, 1 + vd)
                if fr > maxr[0]:
                    maxr = (fr, (a2, a1, a0, str(wf), vd))
    return (n_sf, zg_wit, nrec_hist, ming, maxden, tab, cens, deep_cnt,
            anom, maxr)


# ======================================================================
# box B: quartic RS-conditioned cylinder 2^26 at N=10 — KD1 walker +
# D.10 ladder weight (track_quartic prev_w0 face: w_init = 4)
# ======================================================================
def kd9_quartic(a0, a1, a2, a3):
    """-> (nrec, zg, ming, w_final, deep, anom)."""
    c1, c0 = 2, 4
    nrec = zg = 0
    ming = None
    w = 4                                # w_init = 4 (recorded convention)
    for _ in range(STEP_CAP):
        q0, q1, rc, rx = dev4(a0, a1, a2, a3, c1, c0, MB)
        b1c, b1x = (q0 - c0) % MB, (q1 - c1) % MB
        w1, w0 = wpair(b1c, b1x), wpair(rc, rx)
        rs = None
        if 2 * w1 < w0:
            lab = 'TS'
        elif w0 >= NB:
            lab = 'DEEP'
        elif w0 & 1:
            lab = 'RAM'
        elif w0 < 2:
            lab = 'DEEP'
        else:
            h = w0 >> 1
            d1 = digB(b1c, b1x, h) if w1 == h else 0
            d0 = digB(rc, rx, w0)
            if d1:
                lab = 'SPLIT' if d0 == F4_SQ[d1] else 'INERT'
            else:
                lab = 'RS'
                rs = (F4_SQ[d0], h)
        if rs is None:
            return nrec, zg, ming, w, lab == 'DEEP', 0
        nrec += 1
        g = w0 - w
        if g <= 0:
            zg += 1
        if ming is None or g < ming:
            ming = g
        w = w0
        r, h = rs
        c0 = (c0 - (r & 1) * (1 << h)) % MB
        c1 = (c1 - (r >> 1) * (1 << (h - 1))) % MB
    return nrec, zg, ming, w, True, 1


def worker_quartic(u3):
    a3 = 4 * u3
    total = 0
    zg_wit = []
    runhist = {}
    ming = None
    tab = {}          # exact vd -> [n, max_wf] over nrec>=1 (disc != 0)
    disczero = 0
    deep_cnt = 0
    anom = 0
    maxr = (Fraction(0), None)
    for u2 in range(1 << 7):
        a2 = 4 + 8 * u2
        for u1 in range(1 << 6):
            a1 = 16 * u1
            for u0 in range(1 << 5):
                a0 = 16 + 32 * u0
                total += 1
                nrec, zg, mg, wf, deep, an = kd9_quartic(a0, a1, a2, a3)
                anom += an
                if deep:
                    deep_cnt += 1
                if zg:
                    zg_wit.append((u0, u1, u2, u3, nrec, zg))
                if nrec == 0:
                    continue
                runhist[nrec] = runhist.get(nrec, 0) + 1
                if ming is None or (mg is not None and mg < ming):
                    ming = mg
                D = disc4_int(a3, a2, a1, a0)
                if D == 0:
                    disczero += 1
                    continue
                vd = v2_int(D)
                row = tab.setdefault(vd, [0, 0])
                row[0] += 1
                if wf > row[1]:
                    row[1] = wf
                fr = Fraction(wf, 1 + vd)
                if fr > maxr[0]:
                    idx = u0 | (u1 << 5) | (u2 << 11) | (u3 << 18)
                    maxr = (fr, (idx, wf, vd))
    return (total, zg_wit, runhist, ming, tab, disczero, deep_cnt, anom,
            maxr)


# ======================================================================
# merging + trend
# ======================================================================
def _merge_hist(dst, src):
    for k, v in src.items():
        dst[k] = dst.get(k, 0) + v


def _merge_tab(dst, src):
    for k, (n, mx) in src.items():
        row = dst.setdefault(k, [0, None])
        row[0] += n
        if row[1] is None or mx > row[1]:
            row[1] = mx


def trend_verdict(tab):
    """tab: {vd: [n, max_wf]}.  Pre-stated rule (header): support >=
    SUPPORT_MIN, sequence of max w_final/(1+vd) by increasing vd."""
    seq = [(vd, Fraction(tab[vd][1]) / (1 + vd))
           for vd in sorted(tab) if tab[vd][0] >= SUPPORT_MIN]
    if len(seq) < 2:
        return 'INSUFFICIENT-SUPPORT', seq
    xs = [r for _, r in seq]
    nondecr = all(xs[i + 1] >= xs[i] for i in range(len(xs) - 1))
    if nondecr and xs[-1] > xs[0]:
        return 'GROWING', seq
    if nondecr:
        return 'FLAT', seq
    return 'NON-MONOTONE', seq


def _fmt_tab(tab):
    return {vd: (tab[vd][0], str(tab[vd][1]),
                 str(Fraction(tab[vd][1]) / (1 + vd)))
            for vd in sorted(tab)}


# ======================================================================
# main
# ======================================================================
def main():
    t0 = time.time()
    emit('#' * 72)
    emit('# kd9_ladder_cap_probe.py run %s — UNIT KD9 (BP4-c7 gate for '
         'KD6+KD7):' % time.strftime('%Y-%m-%d %H:%M:%S'))
    emit('# leg (i) strict ladder climb / leg (ii) cap fit w_final vs '
         '1 + vdisc')
    emit('# seals P1-P2 of 2026-07-30 in force (see module docstring)')
    emit('#' * 72)
    with open(KD1JSON) as fh:
        kd1 = json.load(fh)

    # ---------------- box A ----------------
    tA = time.time()
    n_sf = deepA = anomA = 0
    zgA = []
    nrecA = {}
    mingA, maxdenA = None, 1
    tabA = {}
    censA = [0, None]
    maxrA = (Fraction(0), None)
    with Pool(NPROC) as pool:
        for res in pool.imap_unordered(worker_cubic, range(MA), chunksize=4):
            (ns, zw, nh, mg, mden, tb, cn, dc, an, mr) = res
            n_sf += ns
            zgA += zw
            _merge_hist(nrecA, nh)
            if mg is not None and (mingA is None or mg < mingA):
                mingA = mg
            maxdenA = max(maxdenA, mden)
            _merge_tab(tabA, tb)
            censA[0] += cn[0]
            if cn[1] is not None and (censA[1] is None or cn[1] > censA[1]):
                censA[1] = cn[1]
            deepA += dc
            anomA += an
            if mr[0] > maxrA[0]:
                maxrA = mr
    walkedA = (1 << 24) - n_sf
    emit('box A (cubic 2^24, N=8) done %.0fs; walked %d + squarefree %d; '
         'recentering members %d' % (time.time() - tA, walkedA, n_sf,
                                     sum(nrecA.values())))
    check('KD9-V1 box A checksum (walked + squarefree = 2^24, squarefree '
          '= 2^23)', walkedA + n_sf == 1 << 24 and n_sf == 1 << 23,
          'walked=%d sf=%d' % (walkedA, n_sf))
    check('KD9-V2 box A recentering histogram ties the KD1 run '
          '(fresh walk, same box)',
          {str(k): v for k, v in nrecA.items()} == kd1['boxA']['nrec_hist'],
          'kd9 %s vs kd1 %s' % (dict(sorted(nrecA.items())),
                                kd1['boxA']['nrec_hist']))
    check('KD9-V3 box A engine anomalies == 0', anomA == 0,
          'anom=%d' % anomA)

    # ---------------- box B ----------------
    tB = time.time()
    totalB = disczeroB = deepB = anomB = 0
    zgB = []
    runB = {}
    mingB = None
    tabB = {}
    maxrB = (Fraction(0), None)
    with Pool(NPROC) as pool:
        for res in pool.imap_unordered(worker_quartic, range(1 << 8),
                                       chunksize=4):
            (tt, zw, rh, mg, tb, dz, dc, an, mr) = res
            totalB += tt
            zgB += zw
            _merge_hist(runB, rh)
            if mg is not None and (mingB is None or mg < mingB):
                mingB = mg
            _merge_tab(tabB, tb)
            disczeroB += dz
            deepB += dc
            anomB += an
            if mr[0] > maxrB[0]:
                maxrB = mr
    emit('box B (quartic psi^2-cylinder 2^26, N=10) done %.0fs; '
         'recentering members %d; disc==0 among counted %d; deep %d'
         % (time.time() - tB, sum(runB.values()), disczeroB, deepB))
    check('KD9-V4 box B checksum (sum = 2^26)', totalB == 1 << 26,
          'total=%d' % totalB)
    check('KD9-V5 box B recentering histogram ties the KD1 run',
          {str(k): v for k, v in runB.items()} == kd1['boxB']['runhist'],
          'kd9 %s vs kd1 %s' % (dict(sorted(runB.items())),
                                kd1['boxB']['runhist']))
    check('KD9-V6 box B engine anomalies == 0', anomB == 0,
          'anom=%d' % anomB)

    # ---------------- leg (i): P1 strict ladder climb ----------------
    check('KD9-P1 leg (i) strict key-weight climb: ZERO recenterings with '
          'zero ladder gain in either box',
          len(zgA) == 0 and len(zgB) == 0,
          'witnesses: box A %d, box B %d%s' % (
              len(zgA), len(zgB),
              ('; FIRST: %s / %s' % (zgA[:1], zgB[:1]))
              if (zgA or zgB) else ''))
    emit('  [report-only] ladder lattice row: min positive gain box A = %s '
         '(max gain denominator %d), box B = %s; all gains in 1·ℤ at these '
         'boxes (D(n)-lattice satisfied with D = 1 here)'
         % (mingA, maxdenA, mingB))
    emit('  [report-only] w_init conventions: box A 0 (key creation), '
         'box B 4 (nu0 consumed side value); KD6-carrier instance caveat: '
         'the typed climb law also charges the key-creation node — an '
         'engine instance needs a shifted functional (header note).')

    # ---------------- leg (ii): P2 cap fit ----------------
    verdA, seqA = trend_verdict(tabA)
    verdB, seqB = trend_verdict(tabB)
    emit('KD9-P2 leg (ii) cap fit — w_final vs 1 + vdisc (fit population: '
         '>= 1 recentering; conventions in header):')
    emit('  box A rows {vd: (n, max_wf, max_ratio)} exact: %s'
         % _fmt_tab(tabA))
    emit('  box A censored >=8 row: n=%d, max_wf=%s (floor ratio %s at '
         'vd=8)' % (censA[0], censA[1],
                    (str(Fraction(censA[1]) / 9)
                     if censA[1] is not None else '-')))
    emit('  box B rows: %s' % _fmt_tab(tabB))
    emit('  empirical minimal c: box A %s at %s; box B %s at %s'
         % (maxrA[0], maxrA[1], maxrB[0], maxrB[1]))
    emit('  trend rule (header): support >= %d, max-ratio non-decr + '
         'last > first  =>  GROWING' % SUPPORT_MIN)
    emit('  box A max-ratio trend: %s  %s'
         % (verdA, [(vd, str(r)) for vd, r in seqA]))
    emit('  box B max-ratio trend: %s  %s'
         % (verdB, [(vd, str(r)) for vd, r in seqB]))
    growing = (verdA == 'GROWING') or (verdB == 'GROWING')
    check('KD9-P2 leg (ii) cap fit: NO super-linear growth of w_final '
          'against 1 + vdisc on either box (constant-c(n) candidates '
          'survive)', not growing,
          'trends: box A %s, box B %s; minimal c: A %s, B %s'
          % (verdA, verdB, maxrA[0], maxrB[0]))

    # ---------------- verdict + outputs ----------------
    nval_bad = sum(1 for n, ok, _ in CHECKS
                   if not ok and n.startswith('KD9-V'))
    nfind = sum(1 for n, ok, _ in CHECKS if not ok and n.startswith('KD9-P'))
    emit('')
    emit('KD9 VERDICT: %d checks, %d sealed FINDING(s), %d validation '
         'failure(s); wall %.0fs'
         % (len(CHECKS), nfind, nval_bad, time.time() - t0))
    emit('scope reminder (sealed fence): candidate-stress + growth '
         'detection only; the existential X-side statements are never '
         'probe-decidable.  P1+P2 clean GATES the KD6/KD7 provers.')
    with open(RESULTS_TXT, 'a') as fh:
        fh.write('\n\n##### kd9_ladder_cap_probe.py (UNIT KD9: ladder/cap '
                 'gate for KD6+KD7) #####\n')
        fh.write('\n'.join(LINES) + '\n')
    os.makedirs(os.path.join(HERE, 'results'), exist_ok=True)

    def keystr(d):
        return {str(k): [d[k][0], str(d[k][1])] for k in d}
    with open(OUTJSON, 'w') as fh:
        json.dump({
            'checks': [{'name': n, 'ok': ok, 'detail': d}
                       for n, ok, d in CHECKS],
            'boxA': {'walked': walkedA, 'squarefree': n_sf,
                     'nrec_hist': {str(k): v for k, v in nrecA.items()},
                     'min_gain': str(mingA), 'max_gain_den': maxdenA,
                     'tab_vd_n_maxwf': keystr(tabA),
                     'censored_row': [censA[0], str(censA[1])],
                     'deep': deepA, 'zero_gain_witnesses': zgA[:100],
                     'max_ratio': [str(maxrA[0]), maxrA[1]],
                     'trend': [verdA, [(vd, str(r)) for vd, r in seqA]]},
            'boxB': {'total': totalB,
                     'runhist': {str(k): v for k, v in runB.items()},
                     'min_gain': str(mingB),
                     'tab_vd_n_maxwf': keystr(tabB),
                     'disc_zero_members': disczeroB, 'deep': deepB,
                     'zero_gain_witnesses': zgB[:100],
                     'max_ratio': [str(maxrB[0]), maxrB[1]],
                     'trend': [verdB, [(vd, str(r)) for vd, r in seqB]]},
            'seals': 'P1-P2 sealed 2026-07-30 pre-run; see module '
                     'docstring',
        }, fh, indent=1, default=str)
    emit('json -> %s; summary appended -> %s' % (OUTJSON, RESULTS_TXT))
    if nval_bad:
        return 2
    return 1 if nfind else 0


if __name__ == '__main__':
    sys.exit(main())
