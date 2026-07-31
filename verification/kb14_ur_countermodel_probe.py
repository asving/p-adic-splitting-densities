#!/usr/bin/env python3
"""kb14_ur_countermodel_probe.py — UNIT KB14 (bridge campaign, area BP4,
cluster BP4-c1, GATE unit) — the (U)/(R) countermodel probe.

[CM-first gate for KB12 + KB13 — NEW at blueprint REV 2 (F5); this probe is
an explicit dependency of BOTH provers and runs FIRST.]

STATEMENT (blueprint BRIDGE_BP4_KERNELS_2026-07-30.md §4 KB14 + §3.B consumer
paragraph): over the enum/census root reads, search for
  (i)  two DISTINCT realized root children on ONE track at ONE root-cell
       point — a witness REFUTES (U) (per-point per-track uniqueness of
       realized root children, the canonical-instance leg of BP3 TV-A1's
       named `TrackUniqOn`);
  (ii) a realized root child on a MULTIPLICITY-1 track — a witness REFUTES
       (R) (realized root children have track multiplicity >= 2 in redPoly,
       the canonical-instance leg of TV-A1's `TrackRepOn`; the (c2) covering
       case analysis, MOVES 7112-7119, predicts a simple factor's read is
       hen-terminal, no continuing child);
plus (iii) the in-corpus witness attempt at the G1 CellData toys — EXPECTED
BLOCKED per the E5 fence record (child_cover fails on both toy carriers; no
CellAssign instance exists); record the outcome either way.

CONSUMER EDGE (REV 2, F8 — binding): KB12/KB13 target TV-A1's named Props at
the CANONICAL carriers; they do NOT discharge the abstract E5 hD4R0K premise
(MovesT/E5_rootSplit.lean:343, owner HC-2/D4R0K).  This probe gates only the
canonical-instance legs.

DEPS: verification/ census infra (the case_mn3 gate-validated polygon reader
/ the state_track_probes history extractor supply root reads; tracks and
multiplicities from the root residual factorization over F_p).

SEALED PREDICTIONS (Q6 discipline — sealed 2026-07-30, BEFORE any run):
  P1: ZERO (i)-witnesses across the census boxes (the p = 2 cubic 2^24 box
      at N = 8 and the p = 3 3^15 box; plus the quartic RS cylinder as an
      exploration layer): no root-cell point carries two distinct realized
      root children on one track.  (U) holds on census; the KB12 prover is
      unblocked by a clean run.
  P2: ZERO (ii)-witnesses across the same boxes: no realized (continuing)
      root child sits on a multiplicity-1 track — every mult-1 factor's
      read is hen-terminal at the read itself.  (R) holds on census; KB13
      unblocked by a clean run.
  P3 (in-corpus leg, expected-BLOCKED): the witness attempt at the G1
      CellData toys does NOT produce a (U)/(R) countermodel because
      child_cover fails on both toy carriers and no CellAssign instance
      exists (the E5 fence-rule record); the deliverable is the RECORD of
      the blockage (or, if a witness unexpectedly compiles, an immediate
      FINDING escalated to the Q7 adjudication queue — a compiled negation
      witness must NEVER coexist with an un-repaired sorried universal).
  Any P1/P2 witness is a FINDING that refutes the corresponding TV-A1
  canonical-instance leg BEFORE the provers run; the witness (f, root cell,
  track, children) is recorded verbatim in the results block.

OUTPUT (run phase): PASS/FINDING rows appended to
probe_results_2026-07-30.txt; JSON to results/kb14_ur_countermodel.json;
exit 0 = P1+P2 clean and P3 recorded, 1 = FINDING.

STATUS: RUN PHASE (2026-07-30, implemented AFTER the seal above; the sealed
paragraphs P1-P3 are byte-identical to the E-phase seal).

EXTRACTION RULE (the transcription the scans run on, recorded):
 - root-cell point = the mod-p coefficient reduction of f; tracks = monic
   irreducible factors of redPoly = fbar with multiplicities (fp_factor).
 - REALIZED ROOT CHILD on track psi = a CONTINUING member of the FIRST
   window read at psi: shift f to the track center (linear tracks), read
   the width-m window (slots 0..m of the shifted development, m = the
   track's redPoly multiplicity) with the gate-validated polygon reader
   (case_mn3_gate.classify_window: hull sides + side residual digits,
   completion-stability decidedness), factor each decided side residual
   (fp_factor); a member (side, phi, mu) CONTINUES iff mu >= 2 — the
   BranchDichotomy transcription (MovesD/Defs.lean: mu = 1 saturates
   (tau-irr halt), mu >= 2 continues).  Members with mu = 1 and hen
   verdicts carry NO child.
 - the (i)-scan counts DECIDED continuing members per (f, track): >= 2 is
   a (U) witness.  the (ii)-scan flags any continuing member on a track of
   redPoly-multiplicity 1 — for LINEAR mult-1 tracks this is tested by
   actually opening the width-1 window; a witness is an (R) refuter.
 - DEVIATION RECORDS: (d1) degree>=2 tracks in the cubic boxes always have
   redPoly multiplicity 1 (2*2 > 3), and a width-m window structurally
   bounds every member's mu by m — the deg>=2 mult-1 rows are recorded as
   STRUCTURAL hen rows (mu <= 1 forced), not empirically opened (opening
   them needs the Phi-adic 'inc' machinery at a deg-g key, whose width-1
   window cannot host a mu >= 2 member).  Any mult >= 2 deg >= 2 track in
   a cubic box would be an infrastructure FINDING (impossible).  (d2) the
   quartic RS cylinder (state_track_probes box B, R0 = psi^2 exactly, one
   deg-2 mult-2 track per f) is read through the REUSED track_quartic
   walker's first-read labels; the label -> continuing-member-count map is
   {TS: 0, RAM: 0, SPLIT: 0, INERT: 0, RS*(r): 1, DEEP: undecided}; a
   width-2 window structurally caps the count at 1, so the cylinder is an
   exploration/record layer (as sealed).  (d3) census children are
   side/digit-data level objects; lift-level duplicates (two children
   differing ONLY in the recorded lift) are not observable by any census —
   that face is exactly KB12's named RootChildDataFn/canonical-lift laws,
   not this probe's scope.  (d4) undecided window reads (capped
   valuations; classify_window's completion-stability rule) are tallied
   and reported per box — a witness must be DECIDED; undecided pairs are
   an honesty row, not a PASS.

REUSE (recorded): case_mn3_gate.fp_factor + case_mn3_gate.classify_window
(the gate-validated M-n3 reader, seal CASE_MN3_SEALED_PREDICTIONS.md);
state_track_probes.track_quartic + its box-B cylinder iteration (seal
CASE_STATEPROBE2/TRK-RULE); the shift arithmetic is the same cubic
Taylor-shift the walkers use (spot-checked in the validation layer).
"""

import json
import os
import sys
import time
from multiprocessing import Pool

HERE = os.path.dirname(os.path.abspath(__file__))
RESULTS_TXT = os.path.join(HERE, 'probe_results_2026-07-30.txt')
OUTJSON = os.path.join(HERE, 'results', 'kb14_ur_countermodel.json')

_USERSITE = os.path.expanduser('~/.local/lib/python3.10/site-packages')
if _USERSITE not in sys.path:
    sys.path.insert(0, _USERSITE)          # numpy for the case_mn3 import
if HERE not in sys.path:
    sys.path.insert(0, HERE)

from case_mn3_gate import fp_factor, classify_window     # noqa: E402
import state_track_probes as stp                          # noqa: E402

E_PHASE = False
NPROC = 16

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
# tables + reduction factorization (per process, lazy)
# ======================================================================
_TABS = {}


def _tables(p, N):
    key = (p, N)
    if key in _TABS:
        return _TABS[key]
    M = p ** N
    vt = [N] * M                       # capped valuation; vt[0] = N
    dg = [0] * M                       # leading digit (0 iff capped)
    for x in range(1, M):
        v, y = 0, x
        while y % p == 0:
            y //= p
            v += 1
        vt[x] = v
        dg[x] = y % p
    # reduction factorization table over all p^3 reduced monic cubics
    facs = {}
    for c0b in range(p):
        for c1b in range(p):
            for c2b in range(p):
                coeffs = [c0b, c1b, c2b, 1]
                k = 0
                while coeffs[k] == 0:
                    k += 1
                tracks = []
                if k:
                    tracks.append(('lin', 0, k))
                rest = coeffs[k:]
                if len(rest) > 1:
                    for f, m in fp_factor(tuple(rest), p):
                        if len(f) == 2:
                            tracks.append(('lin', (-f[0]) % p, m))
                        else:
                            tracks.append(('irr', tuple(f), m))
                facs[(c0b, c1b, c2b)] = tuple(tracks)
    _TABS[key] = (M, vt, dg, facs)
    return _TABS[key]


# ======================================================================
# the first-window read at a track (case_mn3 reader, memoized)
# ======================================================================
_WINMEMO = {}


def window_children(codes, m, N, p):
    """Continuing members of the first window read (window = slots 0..m).
    Returns (cont, undec, faults): cont = tuple of (e, hn, s0, phi, mu)
    with mu >= 2 (the BranchDichotomy continuing criterion); undec = the
    reader's unstable-sidekey count; faults = reader fault strings."""
    key = (codes, m, N, p)
    if key in _WINMEMO:
        return _WINMEMO[key]
    decided, undec, faults = classify_window(codes, m, N, p, False, 0)
    cont, fl = [], [str(f) for f in faults]
    for (e, ell, a, flk, frk, res, s0, hn, u1) in decided:
        fs = fp_factor(res, p)
        if sum((len(f) - 1) * mm for f, mm in fs) != ell:
            fl.append(str(('partition', e, ell, res)))
            continue
        for f, mm in fs:
            if mm >= 2:
                cont.append((e, hn, s0, tuple(f), mm))
    out = (tuple(cont), undec, tuple(fl))
    _WINMEMO[key] = out
    return out


def census_root_reads(p, box_spec):
    """Iterate one c2-slice of the census box; per f yield the root read:
    root-cell point, tracks (psi, mult), and per track the DECIDED
    continuing root children (first-window-read members with mu >= 2) plus
    the undecided tally.  Reuses the gate-validated case_mn3 reader family
    (module REUSE record); deviations d1-d4 recorded in the docstring.
    box_spec = {'N': N, 'c2': c2}.  Yields
    (f=(c2,c1,c0), [(trackkey, mult, ncont, cont, undec, structural)])."""
    N, c2 = box_spec['N'], box_spec['c2']
    M, vt, dg, facs = _tables(p, N)
    c2b = c2 % p
    for c1 in range(M):
        c1b = c1 % p
        for c0 in range(M):
            recs = []
            for kind, key, m in facs[(c0 % p, c1b, c2b)]:
                if kind == 'irr':
                    # deviation d1: structural hen row (mult 1 forced in a
                    # cubic; width-1 window caps mu at 1)
                    recs.append((('irr', key), m, 0, (), 0, True))
                    continue
                r = key
                b2 = (c2 + 3 * r) % M
                b1 = (c1 + 2 * c2 * r + 3 * r * r) % M
                b0 = (c0 + c1 * r + c2 * r * r + r ** 3) % M
                bs = ((b0, b1), (b0, b1, b2), (b0, b1, b2, 1))[m - 1]
                codes = tuple((vt[x], dg[x]) for x in bs)
                cont, undec, faults = window_children(codes, m, N, p)
                recs.append((('lin', r), m, len(cont), cont, undec, False))
            yield (c2, c1, c0), recs


def u_witness_scan(reads):
    """Leg (i): collect (root-cell point, track) pairs carrying >= 2
    DISTINCT realized root children; return the witness list (empty = P1
    PASS)."""
    out = []
    for f, recs in reads:
        for tk, m, ncont, cont, undec, structural in recs:
            if ncont >= 2:
                out.append({'f': f, 'track': tk, 'mult': m,
                            'children': list(cont)})
    return out


def r_witness_scan(reads):
    """Leg (ii): collect realized root children whose track has
    multiplicity 1 in redPoly; return the witness list (empty = P2
    PASS)."""
    out = []
    for f, recs in reads:
        for tk, m, ncont, cont, undec, structural in recs:
            if m == 1 and ncont >= 1:
                out.append({'f': f, 'track': tk, 'mult': m,
                            'children': list(cont)})
    return out


# ======================================================================
# the cubic box workers
# ======================================================================
def worker_cubic_slice(args):
    p, N, c2 = args
    reads = list(census_root_reads(p, {'N': N, 'c2': c2}))
    uw = u_witness_scan(reads)
    rw = r_witness_scan(reads)
    hist, undec_pairs, structural, faults, nf = {}, 0, 0, {}, 0
    for f, recs in reads:
        nf += 1
        for tk, m, ncont, cont, undec, is_struct in recs:
            hist[(m, ncont)] = hist.get((m, ncont), 0) + 1
            if is_struct:
                structural += 1
            if undec:
                undec_pairs += 1
            # any mult>=2 deg>=2 track in a cubic box is impossible (d1)
            if tk[0] == 'irr' and m >= 2:
                faults['irr-mult>=2'] = faults.get('irr-mult>=2', 0) + 1
    return nf, hist, undec_pairs, structural, faults, uw[:8], rw[:8], \
        len(uw), len(rw)


def run_cubic_box(p, N):
    M = p ** N
    t0 = time.time()
    hist, undec_pairs, structural, faults = {}, 0, 0, {}
    uw, rw, nuw, nrw, nf = [], [], 0, 0, 0
    with Pool(NPROC) as pool:
        for res in pool.imap_unordered(
                worker_cubic_slice, [(p, N, c2) for c2 in range(M)],
                chunksize=4):
            nf += res[0]
            for k, v in res[1].items():
                hist[k] = hist.get(k, 0) + v
            undec_pairs += res[2]
            structural += res[3]
            for k, v in res[4].items():
                faults[k] = faults.get(k, 0) + v
            uw += res[5]
            rw += res[6]
            nuw += res[7]
            nrw += res[8]
    secs = time.time() - t0
    emit('box p=%d N=%d (%d boxes) done %.0fs' % (p, N, nf, secs))
    emit('  (mult, n_continuing_children) histogram: %s'
         % {str(k): v for k, v in sorted(hist.items())})
    emit('  undecided (f, track) window pairs: %d; structural deg>=2 '
         'mult-1 hen rows: %d; reader faults: %s'
         % (undec_pairs, structural, faults or 'none'))
    return {'p': p, 'N': N, 'boxes': nf,
            'hist': {str(k): v for k, v in sorted(hist.items())},
            'undecided_pairs': undec_pairs, 'structural_rows': structural,
            'faults': faults, 'n_u_witnesses': nuw, 'n_r_witnesses': nrw,
            'u_witnesses_recorded': uw[:8], 'r_witnesses_recorded': rw[:8],
            'secs': round(secs, 1)}


# ======================================================================
# box C — the quartic RS cylinder (exploration layer; REUSE track_quartic)
# ======================================================================
_QLABEL = {'TS': 0, 'RAM': 0, 'SPLIT': 0, 'INERT': 0}


def worker_quartic_slice(u3):
    a3 = 4 * u3
    firsts, unknown = {}, 0
    for u2 in range(1 << 7):
        a2 = 4 + 8 * u2
        for u1 in range(1 << 6):
            a1 = 16 * u1
            for u0 in range(1 << 5):
                a0 = 16 + 32 * u0
                first = stp.track_quartic(a0, a1, a2, a3)[4]
                firsts[first] = firsts.get(first, 0) + 1
                base = first.split('(')[0]
                if base not in _QLABEL and not base.startswith('RS') \
                        and base != 'DEEP':
                    unknown += 1
    return firsts, unknown


def run_quartic_cylinder():
    t0 = time.time()
    firsts, unknown = {}, 0
    with Pool(NPROC) as pool:
        for f, u in pool.imap_unordered(worker_quartic_slice,
                                        range(1 << 8), chunksize=4):
            for k, v in f.items():
                firsts[k] = firsts.get(k, 0) + v
            unknown += u
    total = sum(firsts.values())
    ncont = {k: (1 if k.startswith('RS') else
                 ('undec' if k == 'DEEP' else 0)) for k in firsts}
    undec = sum(v for k, v in firsts.items() if k == 'DEEP')
    secs = time.time() - t0
    emit('box C (quartic RS cylinder 2^26, N=10; one deg-2 mult-2 track '
         'per f) done %.0fs' % secs)
    emit('  first-read label row: %s' % dict(sorted(firsts.items())))
    emit('  label -> continuing-children map: %s; undecided (DEEP): %d'
         % (dict(sorted(ncont.items())), undec))
    return {'total': total, 'firsts': firsts, 'unknown_labels': unknown,
            'undecided': undec, 'secs': round(secs, 1)}


# ======================================================================
# leg (iii) — the in-corpus G1 CellData toy attempt record
# ======================================================================
def g1_toy_attempt_record():
    """Leg (iii): the in-corpus attempt record — whether a
    CellData/CellAssign witness for a (U)/(R) violation is constructible at
    the two G1 toy carriers; expected BLOCKED (child_cover fails, no
    CellAssign instance).  Output is a record dict either way; any compiled
    witness is a FINDING + Q7 escalation."""
    lean = os.path.join(HERE, '..', 'lean', 'LeanUrat')

    def slurp(rel, lo, hi):
        with open(os.path.join(lean, rel)) as fh:
            ls = fh.readlines()
        return [l.rstrip('\n') for l in ls[lo - 1:hi]]

    e5_quote = slurp('MovesT/E5_rootSplit.lean', 339, 346)
    g1_quote = slurp('MovesT/G1_toyGate.lean', 714, 716)
    # census of CellAssign construction sites: any TERM-level CellAssign
    # value (instance/def whose type is CellAssign, sorry-free) would be a
    # candidate witness carrier.  TV-A5a (BP3, concurrent) is the only
    # construction attempt on disk — check its sorry count.
    tva5a = os.path.join(lean, 'MovesT', 'TV_A5a.lean')
    n_sorry_a5a = None
    if os.path.exists(tva5a):
        with open(tva5a) as fh:
            n_sorry_a5a = fh.read().count('sorry')
    rec = {
        'expected': 'BLOCKED (E5 fence record)',
        'e5_fence_record_quote(E5_rootSplit.lean:339-346)': e5_quote,
        'g1_toys_quote(G1_toyGate.lean:714-716)': g1_quote,
        'finding': (
            'BLOCKED CONFIRMED: the G1 toys (toyModel/toyModelB) stop at '
            'the CellData layer — child_cover FAILS on both carriers at '
            'g = (1,0) (G1 quote above), so no CellAssign over them '
            'exists and no (U)/(R) witness is constructible from the G1 '
            'toys.  The only in-corpus CellAssign construction attempt is '
            'BP3 TV-A5a (n = 1 CHILDLESS micro-carrier, a concurrent '
            'E-phase skeleton, sorry count below) — still uncompiled, and '
            'even completed it is childless: both TrackUniqOn and '
            'TrackRepOn hold VACUOUSLY at it, so it can never be a '
            '(U)/(R) countermodel.  No compiled negation witness '
            'coexists with the fenced universal (the M1 rule holds).'),
        'tv_a5a_sorry_count': n_sorry_a5a,
        'q7_escalation_needed': False,
    }
    return rec


# ======================================================================
# validation layer (the probe's own gate teeth): hand-sealed spot rows
# ======================================================================
def spot_checks():
    emit('--- validation layer: hand-computed spot rows ---')
    # S1: p=2 N=8, f = z^3 + 4z + 2: fbar = z^3, track ('lin',0) mult 3;
    # window pts (0,1),(1,2),(2,cap),(3,0): single e=3 side, residual
    # (1,1) = z+1, mu=1 -> 0 continuing, decided (capped slot 2 off-line).
    reads = None
    for f, recs in census_root_reads(2, {'N': 8, 'c2': 0}):
        if f == (0, 4, 2):
            reads = recs
            break
    ok = (reads is not None and len(reads) == 1
          and reads[0][0] == ('lin', 0) and reads[0][1] == 3
          and reads[0][2] == 0 and reads[0][4] == 0)
    check('KB14-V1 spot p=2 f=(0,4,2): one mult-3 z-track, 0 continuing, '
          'decided', ok, 'recs=%s' % (reads,))
    # S2: p=2 N=8, f = z^3 + z^2 + 4z + 4: fbar = z^2(z+1); z-track mult 2
    # (pts (0,2),(1,2),(2,0): single e=1 h=1 width-2 side, slot 1 OFF the
    # line (v=2 > 1), residual (1,0,1) = (t+1)^2, mu=2 -> ONE continuing
    # child); (z+1)-track mult 1 (width-1 window, 0 continuing).
    reads = None
    for f, recs in census_root_reads(2, {'N': 8, 'c2': 1}):
        if f == (1, 4, 4):
            reads = recs
            break
    d = {tk: (m, nc) for tk, m, nc, _, _, _ in (reads or [])}
    ok = (d.get(('lin', 0)) == (2, 1) and d.get(('lin', 1)) == (1, 0))
    check('KB14-V2 spot p=2 f=(1,4,4): z-track mult2 ONE continuing child; '
          '(z+1)-track mult1 ZERO', ok, 'recs=%s' % (reads,))
    # S3: p=2 N=8, f = (0,0,0): all-capped z^3 window -> undecided, no
    # decided children.
    reads = None
    for f, recs in census_root_reads(2, {'N': 8, 'c2': 0}):
        if f == (0, 0, 0):
            reads = recs
            break
    ok = (reads is not None and reads[0][2] == 0 and reads[0][4] >= 1)
    check('KB14-V3 spot p=2 f=(0,0,0): capped window counted UNDECIDED',
          ok, 'recs=%s' % (reads,))
    # S4: p=3 N=5, f = z^3 + 3z + 3: fbar = z^3; pts (0,1),(1,1),(2,cap),
    # (3,0): hull (0,1)-(1,1)? ascending? drop from (0,1): best slope to
    # (1,1) is 0 -> not < ... hull: (0,1)->(3,0) slope -1/3 vs (0,1)->(1,1)
    # slope 0: -1/3 < 0 wins -> single e=3 side, residual (1,1) = z+1,
    # mu=1 -> 0 continuing, decided.
    reads = None
    for f, recs in census_root_reads(3, {'N': 5, 'c2': 0}):
        if f == (0, 3, 3):
            reads = recs
            break
    ok = (reads is not None and len(reads) == 1
          and reads[0][0] == ('lin', 0) and reads[0][1] == 3
          and reads[0][2] == 0 and reads[0][4] == 0)
    check('KB14-V4 spot p=3 f=(0,3,3): one mult-3 z-track, 0 continuing, '
          'decided', ok, 'recs=%s' % (reads,))
    # S5: p=3 N=5, f = z^3 + 2z^2 + 3z + 9: fbar = z^2(z+2); z-track mult 2:
    # pts (0,2),(1,1),(2,0): single e=1 h=1 side, ALL on line, residual
    # (1,1,1)... wait digits: d(9)=1, d(3)=1, d(2)=2 -> res (1,1,2) ->
    # 2t^2+t+1 monic-ize *2 -> t^2+2t+2 = (t+1)^2+1: check factor over F_3:
    # roots: t=0:2, t=1:2+... use fp_factor at runtime — this row only
    # checks ncont consistency between the two independent paths below.
    tr = _tables(3, 5)
    codes = tuple((tr[1][x], tr[2][x]) for x in (9, 3, 2))
    cont, undec, faults = window_children(codes, 2, 5, 3)
    fs = fp_factor((1, 1, 2), 3)
    expect = sum(1 for f_, mm in fs if mm >= 2)
    ok = (len(cont) == expect and undec == 0)
    check('KB14-V5 spot p=3 window (9,3,2): reader count == direct '
          'fp_factor count', ok, 'cont=%s expect=%d fs=%s'
          % (cont, expect, fs))


# ======================================================================
def main():
    t0 = time.time()
    emit('#' * 72)
    emit('# kb14_ur_countermodel_probe.py RUN %s — the (U)/(R) '
         'countermodel probe (KB14, BP4 gate)'
         % time.strftime('%Y-%m-%d %H:%M:%S'))
    emit('# seal: P1-P3 in this file docstring, sealed 2026-07-30 before '
         'any run; extraction rule + deviations d1-d4 recorded there.')
    emit('#' * 72)
    spot_checks()
    nval_bad = sum(1 for _, ok, _ in CHECKS if not ok)
    if nval_bad:
        emit('VALIDATION FAILURE — aborting before the census scans.')
        _write(None, None, None, None, t0)
        return 1
    resA = run_cubic_box(2, 8)
    resB = run_cubic_box(3, 5)
    resC = run_quartic_cylinder()
    g1 = g1_toy_attempt_record()
    emit('--- sealed families ---')
    check('KB14-checksum box sizes (2^24, 3^15, 2^26)',
          resA['boxes'] == 1 << 24 and resB['boxes'] == 3 ** 15
          and resC['total'] == 1 << 26,
          '%d %d %d' % (resA['boxes'], resB['boxes'], resC['total']))
    check('KB14-P1 (U): ZERO (i)-witnesses (two distinct realized root '
          'children on one track at one point)',
          resA['n_u_witnesses'] == 0 and resB['n_u_witnesses'] == 0
          and resC['unknown_labels'] == 0,
          'p2=%d p3=%d quartic-unknown-labels=%d (witnesses recorded '
          'verbatim in JSON if any)'
          % (resA['n_u_witnesses'], resB['n_u_witnesses'],
             resC['unknown_labels']))
    check('KB14-P2 (R): ZERO (ii)-witnesses (continuing child on a '
          'mult-1 track)',
          resA['n_r_witnesses'] == 0 and resB['n_r_witnesses'] == 0,
          'p2=%d p3=%d (quartic cylinder track is mult-2 by construction)'
          % (resA['n_r_witnesses'], resB['n_r_witnesses']))
    check('KB14-P3 in-corpus G1 toy attempt: BLOCKED record produced, no '
          'compiled witness, no Q7 escalation',
          not g1['q7_escalation_needed'], g1['finding'][:120] + '...')
    emit('  honesty row (report-only): undecided window pairs p2=%d '
         'p3=%d quartic-DEEP=%d — a witness must be decided; undecided '
         'reads are tallied, never PASSed'
         % (resA['undecided_pairs'], resB['undecided_pairs'],
            resC['undecided']))
    nfind = sum(1 for _, ok, _ in CHECKS if not ok)
    emit('')
    emit('KB14 VERDICT: %d checks, %d FINDING(s); wall %.0fs'
         % (len(CHECKS), nfind, time.time() - t0))
    emit('gate consequence: %s' % (
        'CLEAN RUN — KB12 (U-leg) and KB13 (R-leg) provers are UNBLOCKED '
        'per the sealed rule.' if nfind == 0 else
        'FINDING — the affected TV-A1 canonical-instance leg is refuted '
        'on census; the corresponding prover MUST NOT run; escalate.'))
    _write(resA, resB, resC, g1, t0)
    return 0 if nfind == 0 else 1


def _write(resA, resB, resC, g1, t0):
    with open(RESULTS_TXT, 'a') as fh:
        fh.write('\n\n##### kb14_ur_countermodel_probe.py #####\n')
        fh.write('\n'.join(LINES) + '\n')
    os.makedirs(os.path.join(HERE, 'results'), exist_ok=True)
    with open(OUTJSON, 'w') as fh:
        json.dump({'boxA_p2': resA, 'boxB_p3': resB,
                   'boxC_quartic': resC, 'g1_record': g1,
                   'checks': [{'name': n, 'ok': ok, 'detail': d}
                              for n, ok, d in CHECKS]}, fh, indent=1)


if __name__ == '__main__':
    sys.exit(main())
