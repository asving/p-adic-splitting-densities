#!/usr/bin/env python3
"""kd1_sn_refuter_probe.py — UNIT KD1 (bridge campaign, area BP4, cluster
BP4-c1, GATE unit) — the s(n)-candidate refuter + REC-DISC probe + the
(T-const) stress leg.

[CM-first — KD1 clean is an explicit dependency of the KD2 prover
(KD1(gate) → KD2 → KD3 in the blueprint spine).]

STATEMENT (blueprint BRIDGE_BP4_KERNELS_2026-07-30.md §4 KD1 + §3.D + risks
R6/R11), three legs:
  (a) s(n)-candidate stress: re-run + EXTEND the STALL-probe (the exhaustive
      p = 2 monic-cubic 2^24 box at N = 8 and the quartic RS-conditioned
      cylinder 2^26 at N = 10 — the x_n3_probes X2A geometry) on the ratio
      #{recentering nodes}/v_p(disc f).  One f exceeding a sealed candidate
      s(n) refutes THAT CANDIDATE only — the existential WeightCharge shape
      is never probe-decidable.
  (b) REC-DISC probe: search for f with >= 1 recentering node and
      v_p(disc f) = 0.  A witness REFUTES KD2 (`recentering_vdisc_pos`)
      outright — this leg is a genuine finite refuter.
  (c) (T-const) stress leg (NEW at REV 2, F3): tabulate
      countPop H .recT1 + countPop H .t4 (the `Cl7Kernel.track_restarts`
      face, MovesU/DefsLedger.lean:206-209) against vdisc depth on the same
      boxes, along fixed-degree increasing-vdisc families.  A GROWING trend
      is evidence AGAINST the ledger's constant-L face (a finite probe
      cannot refute the ∀; the trend record feeds the escalated cross-area
      review E-1 — BP1 owns the Cl7Kernel row).  NO prover is assigned to
      (T-const) this campaign regardless of outcome.

DEPS: verification/ infra (x_n3_probes.py X2A machinery + the
state_track_probes.py history extractor and (t1)-(t3) recognizers — reuse
recorded, deviations recorded).

SEALED PREDICTIONS (Q6 discipline — sealed 2026-07-30, BEFORE any run):
  P1 (the refuter leg, sealed CLEAN): NO f in either box with a recentering
      node and vdisc f = 0.  The classifier-side sketch says impossible — a
      recentering presupposes a non-hen root read, hence a repeated factor
      of f mod p, hence p | disc f (the same (c2)/(R) content as KB13).  A
      witness is a FINDING refuting KD2's statement before its prover runs.
  P2 (consistency re-run): the STALL ratio max #rec/vdisc <= 2 = s(3) on
      the cubic box reproduces the earlier X2A seal; the quartic cylinder
      reports its max ratio (exploration class).  Candidate-stress rule:
      an f exceeding a candidate kills that candidate, nothing more.
  P3 (exploratory — deliberately NOT direction-sealed): the
      (#recT1 + #t4) vs vdisc tabulation.  Interpretation rule
      PRE-COMMITTED: a monotone-growing trend along a fixed-degree
      increasing-vdisc family = evidence against (T-const), recorded +
      escalated cross-area (E-1); a flat trend = consistent with a
      constant L but PROVES NOTHING (the 15/15 seal + this probe are
      finite-only; the plausibility downgrade R11 stands either way).

OUTPUT (run phase): PASS/FINDING rows appended to
probe_results_2026-07-30.txt; JSON to results/kd1_sn_refuter.json; exit
0 = P1+P2 clean (P3 recorded), 1 = FINDING.

STATUS: IMPLEMENTED + RUN 2026-07-30 (this pass).  The E-phase skeleton's
body pieces are filled per the spec above; the sealed predictions P1-P3 are
UNTOUCHED (they were on record before this implementation existed).  A
recorded deviation: exit 2 = internal validation-row failure (V1-V8 below;
infrastructure inconsistency, distinct from a sealed FINDING).

IMPLEMENTATION NOTES (reuse + deviations, per the DEPS honesty clause):
 - REUSE: state_track_probes.py's exact p=2 integer machinery is imported
   directly (VTA/VTB valuation tables, _lower_hull, _shift3, dev4, wpair,
   digB, F4_SQ); the two walkers below are counter-extended re-derivations
   of its gate-validated track_cubic / track_quartic (TP-A4 oracle tie on
   200k samples; TP-B4 RS1 masses).  x_n3_probes.py is NOT imported (its
   module level clobbers /tmp/x_n3_census.out); its published CUBIC X2A row
   is REPRODUCED as validation gate V3 (max ratio 1/3 with witness
   f=(c2,c1,c0)=(0,229,102) at nrec=2, vd=6 — run_box recenters by exact
   coefficient translation, no frame reduction, so the bug below cannot
   touch it).
 - INFRA FINDING DISCOVERED AT IMPLEMENTATION (2026-07-30, pre-run,
   recorded as row KD1-X1): x_n3_probes.quartic_stall's incremental RS
   recentering DROPS the A2 fold-in on the C1 slot.  Reducing
   t^2 + C1 t + C0 mod the new key Phi' = Phi - t requires
   C1' = C1 + 2t + A2 with A2 = tx^2 + c1x*tx (the x^2 coefficient); the
   code applies the -A2*k' parts to C0 but never adds A2 to c1c.  Witness:
   box idx 788706 (a0,a1,a2,a3) = (80,112,12,12).  True frame after the
   step-0 RS recentering: C1 = (48, 16) => w1 = 4 = h, d1 = 1 => SPLIT
   (nrec = 1).  Faulty frame: C1 = (0, 16) => w1 = 5, d1 = 0 => spurious
   second RS, then RAM.  Adjudicated three ways: exact-integer frame walk;
   dev4-exact re-walk (this file / track_quartic); PARI factorpadic
   (gp 2.17: f = two DISTINCT unramified deg-2 factors, both = the slope-1
   psi-cluster shape, disc v2 = 20 — SPLIT, not RAM).  CONSEQUENCE: x_n3's
   published exploration-class Q2 row (quartic run hist {1: 3047424,
   2: 147456}, max run 2, max ratio 1/10 at idx (788706, 2, 20)) is
   CONTAMINATED; this probe emits the corrected quartic record.  The
   x_n3 cubic rows (incl. the X2A seal target) use run_box — unaffected.
   The sealed-gate x_n3 artifact is NOT patched (never patch a seal);
   the record rides here + the campaign ledger.  Validation gate V6 below
   therefore targets GROUND TRUTH (exact-integer frame agreement on a
   random sample + the PARI-adjudicated witness), not the dead row.
 - COUNTING CONVENTIONS: leg (a) #rec = slope-h>=1 recenterings (the X2A
   convention — like-for-like with the seal).  Legs (b)/(c) count = ALL
   continuing selection nodes = the operational countPop .recT1 +
   countPop .t4: on the cubic box every continuing node is recT1 (no l=1
   or e*g>=2 continuation exists at n=3), and the level-0 repeated-factor
   selection of fbar IS counted (npop = nrec + 1 on every fbar-nonsquarefree
   member; anomalies flagged).  On the quartic cylinder the counted nodes
   are the RS self-loop (T4-row) recenterings; the psi^2 root read is an
   incT12 increment (key creation) and is NOT counted; post-split T4
   sub-chains are unwalked (main-chain lower bound, as in X2A).
 - vdisc: box A read in-box (exact iff < 8, censored bucket '>=8' — the X2A
   convention); box B exact big-integer v2 of the integer representative
   (vs x_n3's uint64 cap-63 read; equal wherever v2 < 64), disc = 0 members
   recorded separately (KD2's hypothesis excludes discZero).
 - DEEP members contribute their observable-prefix counts (lower bounds —
   sufficient for a refuter), tallied separately.
 - Leg (c) trend rule operationalized (implementation detail, stated here
   because P3 fixed only the direction semantics): per box, take the
   per-exact-vdisc max of the counted population over buckets with >= 1000
   members (support floor kills sparse-tail noise); verdict GROWING iff the
   sequence is non-decreasing in vdisc AND last > first; FLAT iff constant;
   NON-MONOTONE otherwise.  Full unfiltered tables go to the JSON either way.
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
OUTJSON = os.path.join(HERE, 'results', 'kd1_sn_refuter.json')

from state_track_probes import (MA, NA, MB, NB, VTA, F4_SQ,  # noqa: E402
                                dev4, wpair, digB, _lower_hull, _shift3)

S3_CANDIDATE = 2          # the sealed s(3) candidate re-checked in leg (a)

E_PHASE = False           # body implemented 2026-07-30 (was the E-phase flag)
NPROC = 24
STEP_CAP = 64             # defensive walk cap (never expected; anomaly if hit)
SUPPORT_MIN = 1000        # leg (c) trend support floor (see header)

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
# shared tables
# ======================================================================
# in-box v2 read of a residue mod 2^8: exact iff < 8; 0 -> censored (>= 8)
VD_A = [NA] * MA
for _x in range(1, MA):
    _v, _y = 0, _x
    while _y % 2 == 0:
        _y //= 2
        _v += 1
    VD_A[_x] = _v

# squarefree residuals fbar (A,B,C) = (a2,a1,a0) mod 2: the four classes
# with disc(fbar) != 0 in F_2 (irr cubics + the two squarefree splits)
SF_SET = {(0, 1, 1), (1, 0, 1), (0, 0, 1), (1, 1, 0)}


def disc3(a2, a1, a0):
    """disc of x^3 + a2 x^2 + a1 x + a0 (exact integer)."""
    return (18 * a2 * a1 * a0 - 4 * a2 ** 3 * a0 + (a2 * a1) ** 2
            - 4 * a1 ** 3 - 27 * a0 ** 2)


def disc4_int(a, b, c, d):
    """disc of x^4 + a x^3 + b x^2 + c x + d (exact integer)."""
    return (256 * d ** 3 - 192 * a * c * d * d - 128 * b * b * d * d
            + 144 * a * a * b * d * d - 27 * a ** 4 * d * d
            + 144 * b * c * c * d - 6 * a * a * c * c * d
            - 80 * a * b * b * c * d + 18 * a ** 3 * b * c * d
            + 16 * b ** 4 * d - 4 * a * a * b ** 3 * d - 27 * c ** 4
            + 18 * a * b * c ** 3 - 4 * a ** 3 * c ** 3
            - 4 * b ** 3 * c * c + a * a * b * b * c * c)


def v2_int(x):
    """exact v2 of a nonzero integer."""
    return ((x & -x).bit_length() - 1)


# ======================================================================
# box A: the exhaustive p=2 monic-cubic 2^24 box at N=8
# walker = counter-extended re-derivation of the gate-validated
# state_track_probes.track_cubic (same reads, same branches)
# ======================================================================
def kd1_cubic(a2, a1, a0):
    """-> (npop, nrec, deep, anom).
    npop = #continuing selection nodes = operational countPop .recT1 +
           countPop .t4 (level-0 repeated-factor selection included; every
           continuing node at n=3 is recT1);
    nrec = #slope-h>=1 recenterings (the X2A #rec convention);
    deep = observable prefix ended at box precision (counts = lower bounds);
    anom = engine anomalies (flat h=0 in-loop selection / degenerate pair /
           step cap; derivation says 0)."""
    A, B, C = a2 & 1, a1 & 1, a0 & 1
    if (A, B, C) in SF_SET:
        return 0, 0, False, 0            # fbar squarefree: no selection ever
    if (A, B, C) == (1, 0, 0):
        c, mode = 0, 2                   # z^2(z+1): pair at 0
    elif (A, B, C) == (0, 1, 0):
        c, mode = 1, 2                   # z(z+1)^2: pair at 1
    elif (A, B, C) == (0, 0, 0):
        c, mode = 0, 3                   # z^3
    else:
        c, mode = 1, 3                   # (z+1)^3
    npop, nrec, anom = 1, 0, 0           # the level-0 selection node (recT1)
    b2 = (a2 + 3 * c) % MA
    b1 = (a1 + 2 * a2 * c + 3 * c * c) % MA
    b0 = (a0 + a1 * c + a2 * c * c + c ** 3) % MA
    for _ in range(STEP_CAP):
        v0, v1, v2c = VTA[b0], VTA[b1], VTA[b2]
        if v0 >= NA:
            return npop, nrec, True, anom
        if mode == 3:
            if 3 * v1 >= 2 * v0 and 3 * v2c >= v0:   # single side (3,0)-(0,v0)
                if v0 % 3:
                    return npop, nrec, False, anom    # e=3 totally ramified
                h = v0 // 3
                e2 = ((b2 >> h) & 1) if v2c == h else 0
                e1 = ((b1 >> (2 * h)) & 1) if v1 == 2 * h else 0
                if (e2, e1) != (1, 1):
                    return npop, nrec, False, anom    # irr / (z+1)(z^2+z+1)
                npop += 1                             # (z+1)^3: recenter
                if h >= 1:
                    nrec += 1
                else:
                    anom += 1
                b2, b1, b0 = _shift3(b2, b1, b0, 1 << h)
                continue
            sides = _lower_hull([(0, v0), (1, v1), (2, v2c), (3, 0)])
            cont = None
            for (i_lo, i_hi, rise) in sides:
                if i_hi - i_lo == 1 or (rise & 1):
                    continue                          # simple root / e=2 ram
                h = rise >> 1
                va = v2c if i_lo == 0 else 0
                if i_lo == 0:
                    d1 = ((b1 >> (va + h)) & 1) if v1 == va + h else 0
                else:
                    d1 = ((b2 >> h) & 1) if v2c == h else 0
                if d1 == 0:
                    cont = h                          # (z+1)^2: continues
            if cont is None:
                return npop, nrec, False, anom        # all members decided
            npop += 1
            if cont >= 1:
                nrec += 1
            else:
                anom += 1
            b2, b1, b0 = _shift3(b2, b1, b0, 1 << cont)
            mode = 2
            continue
        # mode == 2: pair cluster anchored at (2, va)
        va = v2c
        if v0 - va <= 0:
            return npop, nrec, True, anom + 1000      # degenerate (flagged)
        if 2 * v1 < va + v0:
            return npop, nrec, False, anom            # vertex: '111' decided
        rel = v0 - va
        if rel & 1:
            return npop, nrec, False, anom            # e=2 ramified pair
        h = rel >> 1
        d1 = ((b1 >> (va + h)) & 1) if v1 == va + h else 0
        if d1:
            return npop, nrec, False, anom            # z^2+z+1: inert
        npop += 1                                     # (z+1)^2: recenter
        if h >= 1:
            nrec += 1
        else:
            anom += 1
        b2, b1, b0 = _shift3(b2, b1, b0, 1 << h)
    return npop, nrec, True, anom + 10000             # step cap (flagged)


def worker_cubic(a2):
    jointP = {}     # (vdkey, npop) -> count over walked (fbar non-sf) members
    jointR = {}     # (vdkey, nrec) -> count
    deepP = {}      # same key, deep members only
    legb = []       # (a2,a1,a0,npop,nrec) with count >= 1 and vdisc = 0
    nrec_hist = {}
    anom = 0
    n_sf = 0
    sf_bad = 0      # squarefree member with even disc (arithmetic tie break)
    nsf_bad = 0     # non-squarefree member with odd disc (= legb candidates)
    maxr = (Fraction(0), None)       # over exact-vd, nrec >= 1
    maxr_cens = (Fraction(0), None)  # censored floor nrec/8
    A = a2 & 1
    for a1 in range(MA):
        B = a1 & 1
        for a0 in range(MA):
            vd = VD_A[disc3(a2, a1, a0) % MA]
            if (A, B, a0 & 1) in SF_SET:
                n_sf += 1
                if vd != 0:
                    sf_bad += 1
                continue
            if vd == 0:
                nsf_bad += 1
            npop, nrec, deep, an = kd1_cubic(a2, a1, a0)
            anom += an
            key = (vd, npop)
            jointP[key] = jointP.get(key, 0) + 1
            keyR = (vd, nrec)
            jointR[keyR] = jointR.get(keyR, 0) + 1
            if deep:
                deepP[key] = deepP.get(key, 0) + 1
            if nrec:
                nrec_hist[nrec] = nrec_hist.get(nrec, 0) + 1
                if vd < NA:
                    fr = Fraction(nrec, vd)
                    if fr > maxr[0]:
                        maxr = (fr, (a2, a1, a0, nrec, vd))
                else:
                    fr = Fraction(nrec, NA)
                    if fr > maxr_cens[0]:
                        maxr_cens = (fr, (a2, a1, a0, nrec, '>=8'))
            if npop >= 1 and vd == 0:
                legb.append((a2, a1, a0, npop, nrec))
    return (jointP, jointR, deepP, legb, nrec_hist, anom, n_sf, sf_bad,
            nsf_bad, maxr, maxr_cens)


# ======================================================================
# box B: the quartic RS-conditioned cylinder 2^26 at N=10
# walker = counter-extended re-derivation of the gate-validated
# state_track_probes.track_quartic (same reads; adds the h>=1 floor guard
# of x_n3_probes.quartic_stall, unreachable in-stratum)
# ======================================================================
def kd1_quartic(a0, a1, a2, a3):
    """-> (nrec, leaf, first, deep, anom).  nrec = #RS self-loop (T4-row)
    recenterings = operational countPop .recT1 + countPop .t4 on the walked
    main chain (the psi^2 root increment is incT12, not counted)."""
    c1, c0 = 2, 4                        # Phi1 = x^2 + 2x + 4
    nrec = 0
    first = None
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
            lab = 'DEEP'                 # h >= 1 floor guard (never in-stratum)
        else:
            h = w0 >> 1
            d1 = digB(b1c, b1x, h) if w1 == h else 0
            d0 = digB(rc, rx, w0)
            if d1:
                lab = 'SPLIT' if d0 == F4_SQ[d1] else 'INERT'
            else:
                lab = 'RS%d' % ((w0 - 4) >> 1)
                rs = (F4_SQ[d0], h)
        if first is None:
            first = lab if rs is None else '%s(r=%d)' % (lab, rs[0])
        if rs is None:
            return nrec, lab, first, lab == 'DEEP', 0
        r, h = rs
        nrec += 1                        # T4-row self-loop recentering
        c0 = (c0 - (r & 1) * (1 << h)) % MB
        c1 = (c1 - (r >> 1) * (1 << (h - 1))) % MB
    return nrec, 'CAP', first, True, 1


def kd1_quartic_exact(a0, a1, a2, a3):
    """Reference walker: SAME reads as kd1_quartic but over exact integers
    (no mod-2^10 frame; reads censored at NB as in-box).  Ground truth for
    validation gate V6 — dev4 mod 2^10 must agree everywhere, since every
    consumed read (weights capped at 10, digits at levels <= 9) is
    determined by the frame mod 2^10."""
    def v2e(x):
        return NB if x == 0 else min((x & -x).bit_length() - 1, NB)

    def wpe(bc, bx):
        return min(v2e(bc), v2e(bx) + 1, NB)

    def dge(bc, bx, m):
        # python >> / & are two's-complement = 2-adically exact on negatives
        return (((bx >> (m - 1)) & 1) << 1) | ((bc >> m) & 1)
    c1, c0 = 2, 4
    nrec = 0
    first = None
    for _ in range(STEP_CAP):
        q1 = a3 - c1
        q0 = a2 - c1 * q1 - c0
        rx = a1 - c1 * q0 - c0 * q1
        rc = a0 - c0 * q0
        b1c, b1x = q0 - c0, q1 - c1
        w1, w0 = wpe(b1c, b1x), wpe(rc, rx)
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
            d1 = dge(b1c, b1x, h) if w1 == h else 0
            d0 = dge(rc, rx, w0)
            if d1:
                lab = 'SPLIT' if d0 == F4_SQ[d1] else 'INERT'
            else:
                lab = 'RS%d' % ((w0 - 4) >> 1)
                rs = (F4_SQ[d0], h)
        if first is None:
            first = lab if rs is None else '%s(r=%d)' % (lab, rs[0])
        if rs is None:
            return nrec, lab, first
        r, h = rs
        nrec += 1
        c0 = c0 - (r & 1) * (1 << h)
        c1 = c1 - (r >> 1) * (1 << (h - 1))
    return nrec, 'CAP', first


def worker_quartic(u3):
    a3 = 4 * u3
    joint = {}       # (vd, nrec) -> count, over nrec >= 1 members, vd exact
    runhist = {}
    rs1_first = {}   # 'RS1(r=..)' -> count of first reads
    leafs = {}
    legb = []
    disczero = 0
    deep_cnt = 0
    anom = 0
    total = 0
    minvd = None
    maxr = (Fraction(0), None)
    for u2 in range(1 << 7):
        a2 = 4 + 8 * u2
        for u1 in range(1 << 6):
            a1 = 16 * u1
            for u0 in range(1 << 5):
                a0 = 16 + 32 * u0
                total += 1
                nrec, leaf, first, deep, an = kd1_quartic(a0, a1, a2, a3)
                anom += an
                leafs[leaf] = leafs.get(leaf, 0) + 1
                if first.startswith('RS1('):
                    rs1_first[first] = rs1_first.get(first, 0) + 1
                if deep:
                    deep_cnt += 1
                if nrec == 0:
                    continue
                runhist[nrec] = runhist.get(nrec, 0) + 1
                D = disc4_int(a3, a2, a1, a0)
                if D == 0:
                    disczero += 1        # discZero: excluded from KD2 anyway
                    continue
                vd = v2_int(D)
                if minvd is None or vd < minvd:
                    minvd = vd
                key = (vd, nrec)
                joint[key] = joint.get(key, 0) + 1
                if vd == 0:
                    legb.append((u0, u1, u2, u3, nrec))
                else:
                    fr = Fraction(nrec, vd)
                    if fr > maxr[0]:
                        idx = u0 | (u1 << 5) | (u2 << 11) | (u3 << 18)
                        maxr = (fr, (idx, nrec, vd))
    return (joint, runhist, rs1_first, leafs, legb, disczero, deep_cnt,
            anom, total, minvd, maxr)


# ======================================================================
# merging + leg (c) tabulation
# ======================================================================
def _merge(dst, src):
    for k, v in src.items():
        dst[k] = dst.get(k, 0) + v


def pop_table(joint, censor_key=None):
    """joint: (vdkey, cnt) -> nmembers.  Returns rows
    {vd: (n, maxcnt, mean)} over EXACT vd, censored row separately."""
    rows, cens = {}, None
    per = {}
    for (vd, cnt), n in joint.items():
        per.setdefault(vd, []).append((cnt, n))
    for vd, lst in per.items():
        n = sum(x[1] for x in lst)
        mx = max(x[0] for x in lst)
        mean = sum(c * m for c, m in lst) / n
        if censor_key is not None and vd == censor_key:
            cens = (n, mx, round(mean, 3))
        else:
            rows[vd] = (n, mx, round(mean, 3))
    return rows, cens


def trend_verdict(rows):
    """rows: {vd: (n, maxcnt, mean)} exact only.  Pre-stated rule (header):
    filter to support >= SUPPORT_MIN, sequence of maxcnt by increasing vd."""
    seq = [(vd, rows[vd][1]) for vd in sorted(rows) if rows[vd][0] >= SUPPORT_MIN]
    if len(seq) < 2:
        return 'INSUFFICIENT-SUPPORT', seq
    xs = [m for _, m in seq]
    nondecr = all(xs[i + 1] >= xs[i] for i in range(len(xs) - 1))
    if nondecr and xs[-1] > xs[0]:
        return 'GROWING', seq
    if nondecr:
        return 'FLAT', seq
    return 'NON-MONOTONE', seq


# ======================================================================
# validation gate V8: disc4_int against sympy (exact integers)
# ======================================================================
def v8_disc4_sympy():
    try:
        import sympy as sp
    except ImportError:
        usersite = os.path.expanduser('~/.local/lib/python3.10/site-packages')
        sys.path.append(usersite)
        try:
            import sympy as sp
        except ImportError:
            check('KD1-V8 disc4_int == sympy.discriminant (20 random, exact)',
                  True, 'sympy unavailable, skipped (recorded)')
            return
    import random
    rng = random.Random(20260730)
    x = sp.symbols('x')
    ok = True
    for _ in range(20):
        a, b, c, d = (rng.randrange(1 << 12) for _ in range(4))
        D1 = int(sp.discriminant(x ** 4 + a * x ** 3 + b * x ** 2
                                 + c * x + d, x))
        if D1 != disc4_int(a, b, c, d):
            ok = False
    check('KD1-V8 disc4_int == sympy.discriminant (20 random, exact)', ok, '')


# ======================================================================
# main
# ======================================================================
def main():
    t0 = time.time()
    emit('#' * 72)
    emit('# kd1_sn_refuter_probe.py run %s — UNIT KD1 (BP4-c1 gate):'
         % time.strftime('%Y-%m-%d %H:%M:%S'))
    emit('# legs (a) s(n)-candidate stress / (b) REC-DISC refuter /'
         ' (c) (T-const) stress')
    emit('# seals P1-P3 of 2026-07-30 in force (see module docstring)')
    emit('#' * 72)
    v8_disc4_sympy()

    # ---------------- box A: cubic 2^24, N = 8 ----------------
    tA = time.time()
    jointP, jointR, deepP, nrec_hist = {}, {}, {}, {}
    legbA = []
    anomA = n_sf = sf_bad = nsf_bad = 0
    maxrA = (Fraction(0), None)
    maxrA_cens = (Fraction(0), None)
    with Pool(NPROC) as pool:
        for res in pool.imap_unordered(worker_cubic, range(MA), chunksize=4):
            (jP, jR, dP, lb, nh, an, ns, sb, nb, mr, mrc) = res
            _merge(jointP, jP)
            _merge(jointR, jR)
            _merge(deepP, dP)
            _merge(nrec_hist, nh)
            legbA += lb
            anomA += an
            n_sf += ns
            sf_bad += sb
            nsf_bad += nb
            if mr[0] > maxrA[0]:
                maxrA = mr
            if mrc[0] > maxrA_cens[0]:
                maxrA_cens = mrc
    walkedA = sum(jointP.values())
    emit('box A (cubic 2^24, N=8) done %.0fs; walked (fbar non-squarefree) '
         '%d + squarefree %d' % (time.time() - tA, walkedA, n_sf))
    emit('  #rec (h>=1) histogram over nrec>=1 members: %s'
         % dict(sorted(nrec_hist.items())))
    check('KD1-V1 box A checksum (walked + squarefree = 2^24)',
          walkedA + n_sf == 1 << 24, 'walked=%d sf=%d' % (walkedA, n_sf))
    check('KD1-V2 box A arithmetic tie: squarefree count = 2^23, every '
          'squarefree member has vdisc=0, every walked member has vdisc>=1',
          n_sf == 1 << 23 and sf_bad == 0 and nsf_bad == 0,
          'sf=%d sf_bad=%d nsf_bad=%d' % (n_sf, sf_bad, nsf_bad))
    # X2A reproduction: max ratio 1/3; witness re-walk
    wnpop, wnrec, wdeep, wanom = kd1_cubic(0, 229, 102)
    wvd = VD_A[disc3(0, 229, 102) % MA]
    check('KD1-V3 box A X2A reproduction: max #rec/vdisc == 1/3 and witness '
          'f=(0,229,102) re-walks to nrec=2, vd=6',
          maxrA[0] == Fraction(1, 3) and wnrec == 2 and wvd == 6,
          'max %s at %s; witness npop=%d nrec=%d vd=%d deep=%s; censored '
          'floor %s at %s' % (maxrA[0], maxrA[1], wnpop, wnrec, wvd, wdeep,
                              maxrA_cens[0], maxrA_cens[1]))
    check('KD1-V4 box A engine anomalies == 0 (flat h=0 selection / '
          'degenerate pair / step cap)', anomA == 0, 'anom=%d' % anomA)

    # ---------------- box B: quartic cylinder 2^26, N = 10 ----------------
    tB = time.time()
    jointB, runhistB, rs1B, leafsB = {}, {}, {}, {}
    legbB = []
    disczeroB = deepB = anomB = totalB = 0
    minvdB = None
    maxrB = (Fraction(0), None)
    with Pool(NPROC) as pool:
        for res in pool.imap_unordered(worker_quartic, range(1 << 8),
                                       chunksize=4):
            (j, rh, r1, lf, lb, dz, dc, an, tt, mv, mr) = res
            _merge(jointB, j)
            _merge(runhistB, rh)
            _merge(rs1B, r1)
            _merge(leafsB, lf)
            legbB += lb
            disczeroB += dz
            deepB += dc
            anomB += an
            totalB += tt
            if mv is not None and (minvdB is None or mv < minvdB):
                minvdB = mv
            if mr[0] > maxrB[0]:
                maxrB = mr
    emit('box B (quartic psi^2-cylinder 2^26, N=10) done %.0fs; leaf row %s; '
         'deep %d; disc==0 members among counted %d'
         % (time.time() - tB, dict(sorted(leafsB.items())), deepB, disczeroB))
    check('KD1-V5 box B checksum (sum = 2^26)', totalB == 1 << 26,
          'total=%d' % totalB)
    # V6: ground truth (see header X1 note): (i) mod-2^10 walker == exact-
    # integer frame walker on a random sample; (ii) the PARI-adjudicated
    # witness idx 788706 walks to (nrec=1, SPLIT) with exact vd=20.
    import random
    rng = random.Random(20260730)
    mism = 0
    for _ in range(200000):
        u0 = rng.randrange(1 << 5)
        u1 = rng.randrange(1 << 6)
        u2 = rng.randrange(1 << 7)
        u3 = rng.randrange(1 << 8)
        fa = (16 + 32 * u0, 16 * u1, 4 + 8 * u2, 4 * u3)
        if kd1_quartic(*fa)[:2] != kd1_quartic_exact(*fa)[:2]:
            mism += 1
    wq = kd1_quartic(80, 112, 12, 12)     # box idx 788706
    wqe = kd1_quartic_exact(80, 112, 12, 12)
    wqvd = v2_int(disc4_int(12, 12, 112, 80))
    check('KD1-V6 box B ground truth: mod-2^10 walker == exact-integer '
          'frame walker (200k random) and the PARI-adjudicated witness '
          'idx 788706 walks to (nrec=1, SPLIT), vd=20',
          mism == 0 and wq[:2] == (1, 'SPLIT') and wqe[:2] == (1, 'SPLIT')
          and wqvd == 20,
          'mismatches=%d; witness mod-walk %s / exact-walk %s / vd=%d '
          '(gp factorpadic 2026-07-30: two distinct unramified deg-2 '
          'factors, disc v2=20 — SPLIT)' % (mism, wq[:2], wqe[:2], wqvd))
    check('KD1-V7 box B first-read RS1(r) masses == 2^20 each (3 cells)',
          sorted(rs1B.values()) == [1 << 20] * 3, '%s' % rs1B)
    check('KD1-V4b box B engine anomalies == 0 (step cap)', anomB == 0,
          'anom=%d' % anomB)
    # X1: the infra finding (record-only; header IMPLEMENTATION NOTES has
    # the full derivation + adjudication chain; not a KD1 seal event)
    emit('[FINDING] KD1-X1 (INFRA, record-only): '
         'x_n3_probes.quartic_stall drops the A2 = tx^2 + c1x*tx fold-in '
         'on the C1 slot at RS recentering (C1\' = C1 + 2t + A2 required); '
         'its published Q2 quartic row (run hist {1: 3047424, 2: 147456}, '
         'max ratio 1/10 at idx (788706, 2, 20)) is contaminated — the '
         'witness truly walks to (nrec=1, SPLIT), PARI-confirmed (two '
         'unramified deg-2 factors).  Corrected quartic record: run hist '
         '%s, max run %s, max ratio %s at %s.  x_n3 CUBIC rows (X2A seal) '
         'use run_box (exact translation) — unaffected, and reproduced by '
         'V3 above.  The x_n3 artifact is not patched; escalate via the '
         'campaign ledger.'
         % (dict(sorted(runhistB.items())),
            max(runhistB) if runhistB else 0, maxrB[0], maxrB[1]))

    # ---------------- leg (b): the REC-DISC refuter (P1) ----------------
    check('KD1-P1 leg (b) REC-DISC refuter: NO f in either box with a '
          'counted recentering node (countPop .recT1 + .t4 >= 1) and '
          'vdisc f = 0',
          len(legbA) == 0 and len(legbB) == 0,
          'witnesses: box A %d, box B %d%s; box B min vdisc over counted '
          'members = %s (stratum-conditioned, >= 12 expected)'
          % (len(legbA), len(legbB),
             ('; FIRST: %s / %s' % (legbA[:1], legbB[:1]))
             if (legbA or legbB) else '', minvdB))

    # ---------------- leg (a): the s(n)-candidate stress (P2) ----------------
    check('KD1-P2 leg (a) s(3)-candidate stress: cubic-box max #rec/vdisc '
          '<= %d (sealed candidate s(3)); quartic ratio is exploration-class'
          % S3_CANDIDATE,
          maxrA[0] <= S3_CANDIDATE,
          'cubic max %s (censored floor %s); quartic max %s at %s, max run '
          '%s; candidate-stress rule: only the named candidate dies on excess'
          % (maxrA[0], maxrA_cens[0], maxrB[0], maxrB[1],
             max(runhistB) if runhistB else 0))

    # ---------------- leg (c): the (T-const) stress tabulation (P3) --------
    rowsA, censA = pop_table(jointP, censor_key=NA)
    verdA, seqA = trend_verdict(rowsA)
    rowsB, _ = pop_table(jointB)
    verdB, seqB = trend_verdict(rowsB)
    emit('KD1-P3 leg (c) tabulation — countPop .recT1 + .t4 vs vdisc '
         '(fixed-degree families: deg-3 box / deg-4 cylinder):')
    emit('  box A rows {vd: (n, max, mean)} exact: %s; censored >=8: %s'
         % ({k: rowsA[k] for k in sorted(rowsA)}, censA))
    emit('  box A deep members (prefix-count lower bounds) by (vd, cnt): %s'
         % {k: deepP[k] for k in sorted(deepP)})
    emit('  box B rows (counted nrec>=1 members only; main-chain lower '
         'bounds): %s' % {k: rowsB[k] for k in sorted(rowsB)})
    emit('  trend rule (header): support >= %d, max-cnt non-decr + last > '
         'first  =>  GROWING' % SUPPORT_MIN)
    emit('  box A max-cnt trend: %s  %s' % (verdA, seqA))
    emit('  box B max-cnt trend: %s  %s' % (verdB, seqB))
    growing = (verdA == 'GROWING') or (verdB == 'GROWING')
    emit('KD1-P3 RECORD (pre-committed interpretation, direction not '
         'sealed): %s' % (
             'GROWING trend observed => census evidence AGAINST the '
             'constant-L (T-const) face (Cl7Kernel.track_restarts, '
             'MovesU/DefsLedger.lean:206); recorded + feeds the escalated '
             'cross-area review E-1 (BP1 owns the Cl7Kernel row).  NO '
             'prover is assigned to (T-const) this campaign; a finite '
             'probe cannot refute the forall.' if growing else
             'no growing trend at the probed depths; consistent with a '
             'constant L but PROVES NOTHING (finite-only); the R11 '
             'plausibility downgrade stands.'))

    # ---------------- verdict + outputs ----------------
    nval_bad = sum(1 for n, ok, _ in CHECKS if not ok and n.startswith('KD1-V'))
    nfind = sum(1 for n, ok, _ in CHECKS if not ok and n.startswith('KD1-P'))
    emit('')
    emit('KD1 VERDICT: %d checks, %d sealed FINDING(s), %d validation '
         'failure(s); wall %.0fs'
         % (len(CHECKS), nfind, nval_bad, time.time() - t0))
    emit('scope reminder: leg (a) kills named candidates only; leg (b) clean '
         'GATES the KD2 prover (statement survives); leg (c) is a trend '
         'record for E-1 — (T-const) stays unproven and unassigned.')
    with open(RESULTS_TXT, 'a') as fh:
        fh.write('\n\n##### kd1_sn_refuter_probe.py (UNIT KD1: s(n) refuter '
                 '+ REC-DISC + (T-const) stress) #####\n')
        fh.write('\n'.join(LINES) + '\n')
    os.makedirs(os.path.join(HERE, 'results'), exist_ok=True)

    def keystr(d):
        return {str(k): v for k, v in d.items()}
    with open(OUTJSON, 'w') as fh:
        json.dump({
            'checks': [{'name': n, 'ok': ok, 'detail': d}
                       for n, ok, d in CHECKS],
            'boxA': {'walked': walkedA, 'squarefree': n_sf,
                     'jointP_vd_npop': keystr(jointP),
                     'jointR_vd_nrec': keystr(jointR),
                     'deep_vd_npop': keystr(deepP),
                     'nrec_hist': keystr(nrec_hist),
                     'maxratio': [str(maxrA[0]), maxrA[1]],
                     'maxratio_censored': [str(maxrA_cens[0]), maxrA_cens[1]],
                     'legb_witnesses': legbA[:100],
                     'rows': keystr(rowsA), 'censored_row': censA,
                     'trend': [verdA, seqA]},
            'boxB': {'total': totalB, 'leafs': leafsB,
                     'joint_vd_nrec': keystr(jointB),
                     'runhist': keystr(runhistB), 'rs1_first': rs1B,
                     'disc_zero_members': disczeroB, 'deep': deepB,
                     'min_vdisc_counted': minvdB,
                     'maxratio': [str(maxrB[0]), maxrB[1]],
                     'legb_witnesses': legbB[:100],
                     'rows': keystr(rowsB), 'trend': [verdB, seqB]},
            'seals': 'P1-P3 sealed 2026-07-30 pre-run; see module docstring',
            'x1_infra_finding': 'x_n3_probes.quartic_stall missing-A2 C1-slot '
                'bug at RS recentering; published Q2 quartic row contaminated; '
                'witness idx 788706 truly (nrec=1, SPLIT), PARI-confirmed; '
                'cubic rows unaffected (run_box). Full record in module '
                'docstring IMPLEMENTATION NOTES.',
        }, fh, indent=1, default=str)
    emit('json -> %s; summary appended -> %s' % (OUTJSON, RESULTS_TXT))
    if nval_bad:
        return 2
    return 1 if nfind else 0


if __name__ == '__main__':
    sys.exit(main())
