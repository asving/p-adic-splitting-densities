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

STATUS: E-PHASE SPEC — statement skeleton only; body pieces raise
NotImplementedError (the python `sorry`); running prints the spec and exits
3 (NOT-RUN).
"""

import json
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
RESULTS_TXT = os.path.join(HERE, 'probe_results_2026-07-30.txt')
OUTJSON = os.path.join(HERE, 'results', 'kd9_ladder_cap.json')

E_PHASE = True


def _todo(piece):
    raise NotImplementedError('KD9 E-phase skeleton (sorry): ' + piece)


def boxes_with_histories():
    """The KD1 boxes with per-f canonical histories carrying: per-node key
    weights (the KeyWeightData face), recentering nodes, w_init, w_final,
    vdisc f.  DEEP members: observable prefix, recorded as lower bounds."""
    _todo('box + key-weight history extractor (KD1/state_track reuse)')


def leg_i_ladder_gain(histories):
    """Per recentering: key-weight gain (post − pre) on the continuing
    cluster's ladder; witness list of zero-gain recenterings (empty = P1
    PASS); also report the min positive gain vs the (1/D(n))·ℤ lattice."""
    _todo('leg (i) — strict-climb verification + zero-gain search')


def leg_ii_cap_fit(histories):
    """Fit w_final vs 1 + vdisc f: empirical minimal constant c per box and
    per fixed-degree increasing-vdisc family; growth detector on
    w_final/(1 + vdisc) (flat = P2 PASS, growing = FINDING)."""
    _todo('leg (ii) — cap fit + super-linear growth detector')


def main():
    print(__doc__)
    print('KD9: E-PHASE SPEC ONLY — body not implemented; NO probe was run;')
    print('sealed predictions P1-P2 above are on record as of 2026-07-30.')
    return 3


if __name__ == '__main__':
    sys.exit(main())
