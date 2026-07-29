#!/usr/bin/env python3
"""state_track_probes.py — PROBE-4: STATE-probe-2 + TRACK-probe censuses.

CENSUS 1 (STATE-probe-2, plan ASSEMBLY_PLAN_2026-07-26.md §4; sealed
predictions verification/CASE_STATEPROBE2_SEALED_PREDICTIONS.md).  This
script RE-RUNS the sealed gate `case_stateprobe2_gate.py` (15 exhaustive
2^27 boxes: 3 nu1 root boxes N=9 + 9 h'=1 states N=10 + 3 h'=2 states
N=11, p=2 monic sextics, R0 = psi^2*chi) as a subprocess and reports each
sealed family P1..P5 (+ arith layer; P6 report-only) as PASS/FINDING.

CENSUS 2 (TRACK-probe, MOVES_2026-07-24.md §U-SQUEEZE (TRK-RULE) display +
plan §6/§7 roster row 11; exploration-class CANDIDATE-REFUTER only).  On
the STALL-probe boxes — (A) the exhaustive 2^24 monic-cubic box at p=2,
N=8, and (B) the 2^26 quartic conditioned cylinder at N=10 (the
state-probe geometry: root stratum R0 = psi^2, psi = z^2+z+1, key
Phi1 = x^2+2x+4) — extract each f's canonical history and count its
track-OPENING events under the sealed rule (TRK-RULE):
  (t1) KEY CREATION   — a node whose move creates a new key (each
       continuing repeated-factor cluster's key lift; box B: Phi1);
  (t2) BRANCH OPENING — at a branching node with m >= 2 members, each
       member beyond the designated continuing one (+= m-1);
  (t3) LADDER RESTART — a recentering at which D.10's strict-climb chain
       breaks (recognizer: the continuing cluster's ladder weight fails
       to strictly increase across a recentering); any firing is ALSO an
       adjudication FINDING (D.10 predicts none at these depths).
ONE f exceeding the sealed candidate L(n) <= n^2 (L(3)=9, L(4)=16)
refutes THAT CANDIDATE.  SCOPE (plan REV 7, verbatim): the existential
TRACK-COUNT statement (SOME L(n) exists) is decided by the charging
derivation alone, never by this probe.

HONESTY / DEVIATIONS RECORDED (per the (TRK-RULE) honesty clause):
 - The probe consumes ONLY the event recognition (t1)-(t3); the (c1)
   assignment MAP and its well-definedness remain TRACK-COUNT's open
   charging-derivation duty — nothing here advances it.
 - The history extractor is a from-spec reimplementation of the
   classifier's canonical reading at n <= 4 / shallow depth (Newton
   lower hull + residual factorization over F_2/F_4 + Hensel branch
   peeling + zero-gain recenterings), NOT the full §B2-DEF carry-algebra
   engine; the base coefficient frame (key x of the ambient box) is NOT
   counted as a creation event — a report-only row records max+1 (the
   count if the base frame were charged as a track).
 - Members undecided at census precision (DEEP) contribute their
   observable history PREFIX count (a lower bound; sufficient for a
   refuter).
CONSISTENCY LAYERS: box A leaf types vs the independent exact oracle
padic_types.cubic_type_monic on a random sample; box B first-read
RS1(r) entry masses vs state_probe.py's published |S_r| = 2^20.

Run:  python3 state_track_probes.py
Appends PASS/FINDING rows to probe_results_2026-07-30.txt; JSON to
results/state_track_probes_results.json.
"""
import json
import os
import random
import subprocess
import sys
import time
from fractions import Fraction
from multiprocessing import Pool

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import padic_types  # independent exact oracle (degrees <= 3)

RESULTS_TXT = os.path.join(HERE, 'probe_results_2026-07-30.txt')
OUTJSON = os.path.join(HERE, 'results', 'state_track_probes_results.json')
NPROC = 24
L3, L4 = 9, 16          # sealed candidates L(n) <= n^2

LINES = []
CHECKS = []             # (name, ok, detail)


def emit(line):
    LINES.append(line)
    print(line, flush=True)


def check(name, ok, detail=''):
    CHECKS.append((name, bool(ok), detail))
    emit('[%s] %s%s' % ('PASS' if ok else 'FINDING', name,
                        ('  ' + detail) if detail else ''))


# ======================================================================
# CENSUS 1 — STATE-probe-2 (re-run of the sealed gate, subprocess)
# ======================================================================
def census_state_probe_2():
    emit('=' * 72)
    emit('CENSUS 1: STATE-probe-2 (sealed gate case_stateprobe2_gate.py '
         're-run; seal: CASE_STATEPROBE2_SEALED_PREDICTIONS.md)')
    emit('=' * 72)
    t0 = time.time()
    env = dict(os.environ)
    usersite = os.path.expanduser('~/.local/lib/python3.10/site-packages')
    env['PYTHONPATH'] = usersite + os.pathsep + env.get('PYTHONPATH', '')
    proc = subprocess.run(
        ['python3', os.path.join(HERE, 'case_stateprobe2_gate.py')],
        cwd=HERE, capture_output=True, text=True, env=env)
    emit('gate exit=%d, wall %.0fs' % (proc.returncode, time.time() - t0))
    if proc.returncode not in (0, 1) or proc.stdout.strip() == '':
        check('SP2-gate-ran', False, 'stderr tail: %s' % proc.stderr[-400:])
        return None
    with open(os.path.join(HERE, 'results',
                           'case_stateprobe2_results.json')) as fh:
        res = json.load(fh)
    vp = res['verdict_parts']
    check('SP2-arith (closed-form division == literal polydiv + '
          'reconstruction, 500/box)', vp['arith_layer'],
          'unit_test_fails=%s' % res.get('unit_test_fails'))
    check('SP2-P1 REP identity (same-type laws identical; the vtx-VARYING '
          '6-way group + type-A 3-way + h\'=2 pair)', vp['P1_identity'],
          'differing cells=%d' % res['p1_bad_cells'])
    check('SP2-P2 sealed per-tau rows (uniform 2^17 x 1024 / 2^19 x 256)',
          vp['P2_sealed_rows'], 'off-uniform cells=%d' % res['p2_bad_cells'])
    check('SP2-P3 sizes 2^27 + floors + vtx transport, 0 exceptions',
          vp['P3_floors_sizes'],
          'floor_viol=%s vtx_viol=%s' % (sum(res['floors_viol'].values()),
                                         sum(res['vtx_viol'].values())))
    check('SP2-P4 nu1 root-box dictionary + named-bucket row (incl. '
          'RS1(r) = 2^21 entry masses)', vp['P4_nu1_dictionary'],
          'bad=%d' % res['p4_bad'])
    check('SP2-P5 loop-position invariance (h\'=1 marginal == h\'=2 word, '
          'floor-aligned)', vp['P5_loop_position'],
          'differing cells=%d' % res['p5_bad_cells'])
    emit('  [report-only] SP2-P6 cross-type differing cells: %d '
         '(NON-falsifying); Galois relabel layer: %d'
         % (res['p6_crosstype_cells'], res['galois_cells']))
    check('SP2-VERDICT (sealed rule §3)', res['verdict'] == 'PASS',
          res['verdict'])
    return res['verdict']


# ======================================================================
# CENSUS 2 — TRACK-probe: shared p=2 exact-integer machinery
# ======================================================================
NA, MA = 8, 1 << 8            # box A: cubics mod 2^8
NB, MB = 10, 1 << 10          # box B: quartics mod 2^10
VTA = [NA] * MA
for _y in range(1, MA):
    VTA[_y] = 0 if _y & 1 else min(VTA[_y >> 1] + 1, NA)
VTB = [NB] * MB
for _y in range(1, MB):
    VTB[_y] = 0 if _y & 1 else min(VTB[_y >> 1] + 1, NB)


def _f4_mul(a, b):
    c1, x1, c2, x2 = a & 1, a >> 1, b & 1, b >> 1
    return ((c1 * c2 + x1 * x2) & 1) + 2 * ((c1 * x2 + x1 * c2 + x1 * x2) & 1)


F4_SQ = [_f4_mul(t, t) for t in range(4)]   # squaring = sqrt on F_4


# ---------------------------- box A: cubic walker ----------------------
# leaf codes -> oracle types: see map below.  Returns
# (t1, t2, t3, leaf, climb_breaks) — t3 == climb_breaks by the recognizer.
def track_cubic(a2, a1, a0):
    A, B, C = a2 & 1, a1 & 1, a0 & 1
    # nu0 residual factorization of z^3+Az^2+Bz+C over F_2 (see MOVES
    # (TRK-RULE); squarefree residual -> decided, no key created)
    if (A, B, C) in ((0, 1, 1), (1, 0, 1)):
        return (0, 0, 0, '3', 0)                    # irreducible cubic
    if (A, B, C) in ((0, 0, 1), (1, 1, 0)):
        return (0, 1, 0, '12', 0)                   # (lin)(irr quad): m=2
    if (A, B, C) == (1, 0, 0):
        c, mode = 0, 2                              # z^2(z+1): pair at 0
    elif (A, B, C) == (0, 1, 0):
        c, mode = 1, 2                              # z(z+1)^2: pair at 1
    elif (A, B, C) == (0, 0, 0):
        c, mode = 0, 3                              # z^3
    else:
        c, mode = 1, 3                              # (z+1)^3
    # shift g(x) = f(x+c), exact mod 2^NA
    b2 = (a2 + 3 * c) % MA
    b1 = (a1 + 2 * a2 * c + 3 * c * c) % MA
    b0 = (a0 + a1 * c + a2 * c * c + c ** 3) % MA
    t1, t2, t3 = 1, (1 if mode == 2 else 0), 0      # key x+c created; the
    #                                   simple member of z^2(z+1) peeled
    prev_mu = Fraction(0)                           # D.10 ladder weight
    while True:
        v0, v1, v2c = VTA[b0], VTA[b1], VTA[b2]
        if v0 >= NA:
            return (t1, t2, t3, 'UND', t3)          # observable prefix ends
        if mode == 3:
            if 3 * v1 >= 2 * v0 and 3 * v2c >= v0:  # single side (3,0)-(0,v0)
                if v0 % 3:
                    return (t1, t2, t3, '1c', t3)   # e=3 totally ramified
                h = v0 // 3
                e2 = ((b2 >> h) & 1) if v2c == h else 0
                e1 = ((b1 >> (2 * h)) & 1) if v1 == 2 * h else 0
                if (e2, e1) in ((0, 1), (1, 0)):
                    return (t1, t2, t3, '3', t3)    # residual irreducible
                if (e2, e1) == (0, 0):              # (z+1)(z^2+z+1): branch
                    return (t1, t2 + 1, t3, '12', t3)
                # (1,1) = (z+1)^3: zero-gain recentering, same key ladder
                mu = Fraction(h)
                if mu <= prev_mu:
                    t3 += 1                         # (t3) recognizer fires
                prev_mu = mu
                b2, b1, b0 = _shift3(b2, b1, b0, 1 << h)
                continue
            # vertex case: exact lower hull over the 4 points
            sides = _lower_hull([(0, v0), (1, v1), (2, v2c), (3, 0)])
            t2 += len(sides) - 1                    # branch node, m members
            cont = None
            leafparts = []
            for (i_lo, i_hi, rise) in sides:        # each side a sub-cluster
                if i_hi - i_lo == 1:
                    leafparts.append('1')           # simple rational root
                    continue
                if rise & 1:
                    leafparts.append('1r1')         # e=2 ramified pair
                    continue
                h = rise >> 1                       # integral pair slope
                va = v2c if i_lo == 0 else 0        # value at side's right end
                if i_lo == 0:                       # side cols 0..2
                    d1 = ((b1 >> (va + h)) & 1) if v1 == va + h else 0
                else:                               # side cols 1..3
                    d1 = ((b2 >> h) & 1) if v2c == h else 0
                if d1:
                    leafparts.append('12')          # residual z^2+z+1: inert
                    continue
                cont = h                            # repeated (z+1)^2: continue
            if cont is None:
                leaf = ('111' if leafparts.count('1') == 3 else
                        '111' if '111' in leafparts else
                        '1r1' if '1r1' in leafparts else '12')
                return (t1, t2, t3, leaf, t3)
            mu = Fraction(cont)
            if mu <= prev_mu:
                t3 += 1
            prev_mu = mu
            b2, b1, b0 = _shift3(b2, b1, b0, 1 << cont)
            mode = 2                                # continuing pair deepens;
            continue                                # pair = hull cols 0..2 now
        # mode == 2: pair cluster anchored at (2, va)
        va = v2c
        if v0 - va <= 0:                            # degenerate (never for a
            return (t1, t2, t3, 'UND', t3 + 1000)   # genuine pair) -> flag
        if 2 * v1 < va + v0:                        # vertex at col 1: 2 deg-1
            return (t1, t2 + 1, t3, '111', t3)      # sides, both decided
        rel = v0 - va
        if rel & 1:
            return (t1, t2, t3, '1r1', t3)          # e=2 ramified
        h = rel >> 1
        d1 = ((b1 >> (va + h)) & 1) if v1 == va + h else 0
        if d1:
            return (t1, t2, t3, '12', t3)           # residual z^2+z+1: inert
        mu = Fraction(rel, 2)                       # repeated: recenter
        if mu <= prev_mu:
            t3 += 1
        prev_mu = mu
        b2, b1, b0 = _shift3(b2, b1, b0, 1 << h)


def _shift3(b2, b1, b0, c):
    return ((b2 + 3 * c) % MA,
            (b1 + 2 * b2 * c + 3 * c * c) % MA,
            (b0 + b1 * c + b2 * c * c + c ** 3) % MA)


def _lower_hull(pts):
    """Lower convex hull of (col, val) pts (cols ascending); returns sides
    [(col_lo, col_hi, rise)] with rise = val(col_lo) - val(col_hi) >= 0."""
    hull = []
    for p in pts:
        while len(hull) >= 2:
            (x1, y1), (x2, y2) = hull[-2], hull[-1]
            if (y2 - y1) * (p[0] - x1) >= (p[1] - y1) * (x2 - x1):
                hull.pop()
            else:
                break
        hull.append(p)
    return [(hull[i][0], hull[i + 1][0], hull[i][1] - hull[i + 1][1])
            for i in range(len(hull) - 1)]


def worker_cubic(a2):
    hist, leafs, breaks = {}, {}, 0
    argmax = (-1, None)
    for a1 in range(MA):
        for a0 in range(MA):
            t1, t2, t3, leaf, cb = track_cubic(a2, a1, a0)
            tot = t1 + t2 + t3
            hist[tot] = hist.get(tot, 0) + 1
            leafs[leaf] = leafs.get(leaf, 0) + 1
            breaks += cb
            if tot > argmax[0]:
                argmax = (tot, (a2, a1, a0, t1, t2, t3, leaf))
    return hist, leafs, breaks, argmax


# ---------------------------- box B: quartic walker --------------------
def dev4(a0, a1, a2, a3, c1, c0, m):
    q1 = (a3 - c1) % m
    q0 = (a2 - c1 * q1 - c0) % m
    rx = (a1 - c1 * q0 - c0 * q1) % m
    rc = (a0 - c0 * q0) % m
    return q0, q1, rc, rx


def wpair(bc, bx):
    vc, vx = VTB[bc], VTB[bx] + 1
    return vc if vc < vx else (vx if vx < NB else NB)


def digB(bc, bx, m):
    return (((bx >> (m - 1)) & 1) << 1) | ((bc >> m) & 1)


def track_quartic(a0, a1, a2, a3):
    """Box-B member (root stratum R0 = psi^2, vtx = 1): Phi1-frame ladder.
    Returns (t1, t2, t3, leaf, first_read, climb_breaks)."""
    c1, c0 = 2, 4                       # Phi1 = x^2 + 2x + 4 (t1 creation)
    t1, t2, t3 = 1, 0, 0
    prev_w0 = 4                         # nu0 consumed side value (slope-1
    first = None                        # side at Phi-weight 4)
    while True:
        q0, q1, rc, rx = dev4(a0, a1, a2, a3, c1, c0, MB)
        b1c, b1x = (q0 - c0) % MB, (q1 - c1) % MB      # C1 = Q - Phi
        w1, w0 = wpair(b1c, b1x), wpair(rc, rx)
        if 2 * w1 < w0:                 # vertex at slot 1: TS two-sided
            lab = 'TS'
        elif w0 >= NB:
            lab = 'DEEP'
        elif w0 & 1:
            lab = 'RAM'
        else:
            h = w0 >> 1
            d1 = digB(b1c, b1x, h) if w1 == h else 0
            d0 = digB(rc, rx, w0)
            if d1:
                lab = 'SPLIT' if d0 == F4_SQ[d1] else 'INERT'
            else:
                lab = 'RS%d' % ((w0 - 4) >> 1), F4_SQ[d0]  # r = sqrt(d0)
        if first is None:
            first = lab if isinstance(lab, str) else '%s(r=%d)' % lab
        if isinstance(lab, tuple):      # RS self-loop: zero-gain recentering
            r = lab[1]
            if w0 <= prev_w0:
                t3 += 1                 # (t3) strict-climb break recognizer
            prev_w0 = w0
            h = w0 >> 1
            c0 = (c0 - (r & 1) * (1 << h)) % MB
            c1 = (c1 - (r >> 1) * (1 << (h - 1))) % MB
            continue
        if lab in ('TS', 'SPLIT'):
            t2 += 1                     # branching node, 2 members
        return (t1, t2, t3, lab, first, t3)


def worker_quartic(u3):
    a3 = 4 * u3
    hist, leafs, firsts, breaks = {}, {}, {}, 0
    argmax = (-1, None)
    for u2 in range(1 << 7):
        a2 = 4 + 8 * u2
        for u1 in range(1 << 6):
            a1 = 16 * u1
            for u0 in range(1 << 5):
                a0 = 16 + 32 * u0
                t1, t2, t3, leaf, first, cb = track_quartic(a0, a1, a2, a3)
                tot = t1 + t2 + t3
                hist[tot] = hist.get(tot, 0) + 1
                leafs[leaf] = leafs.get(leaf, 0) + 1
                firsts[first] = firsts.get(first, 0) + 1
                breaks += cb
                if tot > argmax[0]:
                    argmax = (tot, (a0, a1, a2, a3, t1, t2, t3, leaf))
    return hist, leafs, firsts, breaks, argmax


def _merge(dst, src):
    for k, v in src.items():
        dst[k] = dst.get(k, 0) + v


def census_track_probe():
    emit('')
    emit('=' * 72)
    emit('CENSUS 2: TRACK-probe ((TRK-RULE) counts on the STALL-probe '
         'boxes; candidate-refuter for L(3)=9, L(4)=16)')
    emit('=' * 72)
    t0 = time.time()
    # ---- box A: exhaustive 2^24 cubic box, N = 8 ----
    histA, leafA, breaksA = {}, {}, 0
    argA = (-1, None)
    with Pool(NPROC) as pool:
        for h, l, b, am in pool.imap_unordered(worker_cubic, range(MA),
                                               chunksize=4):
            _merge(histA, h)
            _merge(leafA, l)
            breaksA += b
            if am[0] > argA[0]:
                argA = am
    totalA = sum(histA.values())
    maxA = max(k for k, v in histA.items() if v)
    emit('box A (cubic 2^24, N=8) done %.0fs; count histogram %s' %
         (time.time() - t0, dict(sorted(histA.items()))))
    emit('  leaf row: %s' % dict(sorted(leafA.items())))
    emit('  max-count witness (a2,a1,a0,t1,t2,t3,leaf): %s' % (argA[1],))
    check('TP-A1 box partition checksum (sum = 2^24)', totalA == 1 << 24,
          'total=%d' % totalA)
    check('TP-A2 candidate L(3)=9 unrefuted (max track count <= 9)',
          maxA <= L3, 'max=%d (report-only max incl. base frame: %d)'
          % (maxA, maxA + 1))
    check('TP-A3 zero (t3) ladder restarts / strict-climb breaks (D.10)',
          breaksA == 0, 'breaks=%d' % breaksA)
    # oracle consistency sample (decided members must match padic_types)
    rng = random.Random(20260730)
    mism = comp = 0
    for _ in range(200000):
        a2, a1, a0 = rng.randrange(MA), rng.randrange(MA), rng.randrange(MA)
        leaf = track_cubic(a2, a1, a0)[3]
        if leaf == 'UND':
            continue
        comp += 1
        if padic_types.cubic_type_monic(a2, a1, a0, 2) != leaf:
            mism += 1
    check('TP-A4 oracle consistency (decided leaves == '
          'padic_types.cubic_type_monic, 200k sample)', mism == 0,
          'compared=%d mismatches=%d' % (comp, mism))
    # ---- box B: 2^26 quartic conditioned cylinder, N = 10 ----
    t1 = time.time()
    histB, leafB, firstB, breaksB = {}, {}, {}, 0
    argB = (-1, None)
    with Pool(NPROC) as pool:
        for h, l, f, b, am in pool.imap_unordered(worker_quartic,
                                                  range(1 << 8), chunksize=4):
            _merge(histB, h)
            _merge(leafB, l)
            _merge(firstB, f)
            breaksB += b
            if am[0] > argB[0]:
                argB = am
    totalB = sum(histB.values())
    maxB = max(k for k, v in histB.items() if v)
    emit('box B (quartic psi^2-cylinder 2^26, N=10) done %.0fs; count '
         'histogram %s' % (time.time() - t1, dict(sorted(histB.items()))))
    emit('  leaf row: %s' % dict(sorted(leafB.items())))
    emit('  first-read row: %s' % dict(sorted(firstB.items())))
    emit('  max-count witness (a0,a1,a2,a3,t1,t2,t3,leaf): %s' % (argB[1],))
    check('TP-B1 cylinder checksum (sum = 2^26)', totalB == 1 << 26,
          'total=%d' % totalB)
    check('TP-B2 candidate L(4)=16 unrefuted (max track count <= 16)',
          maxB <= L4, 'max=%d (report-only max incl. base frame: %d)'
          % (maxB, maxB + 1))
    check('TP-B3 zero (t3) ladder restarts / strict-climb breaks (D.10)',
          breaksB == 0, 'breaks=%d' % breaksB)
    rs1 = {k: v for k, v in firstB.items() if k.startswith('RS1')}
    check('TP-B4 first-read RS1(r) entry masses = 2^20 each '
          '(state_probe |S_r| tie)', sorted(rs1.values()) == [1 << 20] * 3,
          '%s' % rs1)
    return {'histA': {str(k): v for k, v in histA.items()},
            'leafA': leafA, 'maxA': maxA, 'breaksA': breaksA,
            'argmaxA': argA[1], 'histB': {str(k): v for k, v in histB.items()},
            'leafB': leafB, 'firstB': firstB, 'maxB': maxB,
            'breaksB': breaksB, 'argmaxB': argB[1]}


def main():
    t0 = time.time()
    emit('#' * 72)
    emit('# state_track_probes.py run %s — PROBE-4 (STATE-probe-2 + '
         'TRACK-probe)' % time.strftime('%Y-%m-%d %H:%M:%S'))
    emit('#' * 72)
    sp2 = census_state_probe_2()
    tp = census_track_probe()
    nfind = sum(1 for _, ok, _ in CHECKS if not ok)
    emit('')
    emit('OVERALL: %d checks, %d FINDING(s); wall %.0fs' %
         (len(CHECKS), nfind, time.time() - t0))
    emit('TRACK-probe scope reminder: candidate-refuter only; TRACK-COUNT '
         'and its charging derivation remain OPEN (CL-7) regardless.')
    with open(RESULTS_TXT, 'a') as fh:
        fh.write('\n\n##### state_track_probes.py #####\n')
        fh.write('\n'.join(LINES) + '\n')
    os.makedirs(os.path.join(HERE, 'results'), exist_ok=True)
    with open(OUTJSON, 'w') as fh:
        json.dump({'sp2_verdict': sp2, 'track_probe': tp,
                   'checks': [{'name': n, 'ok': ok, 'detail': d}
                              for n, ok, d in CHECKS]}, fh, indent=1)
    return 0 if nfind == 0 else 1


if __name__ == '__main__':
    sys.exit(main())
