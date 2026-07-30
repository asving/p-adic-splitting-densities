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

STATUS: E-PHASE SPEC — statement skeleton only; body pieces raise
NotImplementedError (the python `sorry`); running prints the spec and exits
3 (NOT-RUN).
"""

import json
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
RESULTS_TXT = os.path.join(HERE, 'probe_results_2026-07-30.txt')
OUTJSON = os.path.join(HERE, 'results', 'kd1_sn_refuter.json')

S3_CANDIDATE = 2          # the sealed s(3) candidate re-checked in leg (a)

E_PHASE = True


def _todo(piece):
    raise NotImplementedError('KD1 E-phase skeleton (sorry): ' + piece)


def stall_boxes():
    """The two STALL-probe boxes: (A) exhaustive p=2 monic cubics 2^24 at
    N=8; (B) the quartic RS-conditioned cylinder 2^26 at N=10 (state-probe
    geometry: R0 = psi^2, psi = z^2+z+1, key Phi1 = x^2+2x+4)."""
    _todo('box iterators (x_n3_probes reuse)')


def history_of(f, p, box):
    """Canonical history: recentering nodes, per-node population letters
    (recT1 / t4 per the MovesX Pop vocabulary), vdisc f; DEEP members
    contribute their observable prefix (lower bound — sufficient for a
    refuter), recorded as such."""
    _todo('history extractor (state_track_probes reuse)')


def leg_a_ratio_stress(histories):
    """max #rec/vdisc per box + the per-candidate verdict vs S3_CANDIDATE."""
    _todo('leg (a)')


def leg_b_recdisc_refuter(histories):
    """Witness list of f with #rec >= 1 and vdisc = 0 (empty = P1 PASS)."""
    _todo('leg (b) — the KD2 refuter')


def leg_c_tconst_stress(histories):
    """(#recT1 + #t4) vs vdisc tabulation + fixed-degree family trend fit;
    emits the pre-committed interpretation verdict (trend record only)."""
    _todo('leg (c) — the (T-const) stress tabulation')


def main():
    print(__doc__)
    print('KD1: E-PHASE SPEC ONLY — body not implemented; NO probe was run;')
    print('sealed predictions P1-P3 above are on record as of 2026-07-30.')
    return 3


if __name__ == '__main__':
    sys.exit(main())
