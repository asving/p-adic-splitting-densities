#!/usr/bin/env python3
"""ke4_tails_stress_probe.py — UNIT KE4 (bridge campaign, area BP4, cluster
BP4-c1, GATE unit) — the tails candidate-stress probe, TWO-PHASE.

[CM-first for KE5, TWO-PHASE per blueprint REV 2 (F10): X2TailsP is
EXISTENTIAL in the pair (C_T, c_T) (XConsts data), so NO finite probe can
refute it, and a probe run before the prover knows no candidate constants.
The honest gate shape is candidate-stress + divergence detection.]

STATEMENT (blueprint BRIDGE_BP4_KERNELS_2026-07-30.md §4 KE4 + §3.E (E-iv) +
risk R8):
  PHASE 1 (BEFORE the KE5 prover; this spec's primary content): exhaustive
  tall-event masses at n = 3, p in {2, 3}, h* <= 8 — frac(TallEvent h*) =
  the census mass of branches whose FIRST height->= h* read occurs; fit the
  empirical decay exponent; COMPUTE the explicit candidate pair (C_T, c_T)
  the KE5 sketch implies (the D4R.2 pool-bound composition mu(P-hat) <=
  M(P-hat)·p^{W(P-hat)−A(P-hat)}, A growing with the tall read's height,
  summed over prefixes with the per-depth species-menu branching factor)
  and STRESS it in-box; track mass·p^{c·h*} growth in h* as the divergence
  detector — per-depth branching outrunning per-height decay is the known
  divergence risk (R8).
  PHASE 2 (AFTER KE5 drafts its actual constants, BEFORE acceptance):
  re-run the stress against the prover's actual (C_T, c_T).  KE5's
  acceptance is GATED on phase 2.  Phase 2 is BLOCKED until the KE5 draft
  exists (a within-unit sequencing stub, not a unit blockage).

DEPS: verification/ census infra (the x_n3_probes X2B per-letter teeth
machinery already prices per-letter height tails mu <= p^{−(h−h0(L))};
reuse recorded).  Phase 2 additionally: the KE5 draft's constants.

SEALED PREDICTIONS (Q6 discipline — sealed 2026-07-30, BEFORE any run):
  P1: frac(TallEvent h*) decays geometrically in h* at both p — the fitted
      empirical exponent c_T^emp is > 0 (the X2B teeth h0(L)-anchored decay
      suggests c_T ~ 1 per letter).
  P2 (candidate-stress): the sketch-implied explicit pair passes in-box:
      frac(TallEvent h*) <= C_T·p^{−c_T·h*} for every h* <= 8; the prior
      X-n3 sealed reference numbers C_T(3) = 53, c_T(3) = 1 are stressed
      alongside as the reference candidates.  A candidate failure kills
      THAT candidate (the composition's constants recomputed and the gap
      recorded), never the existential.
  P3 (divergence detector): mass·p^{c_T·h*} stays bounded (no growing
      trend in h*) at the candidate c_T.  A growing trend is THE divergence
      FINDING (R8) — KE5 rerouted toward its divergent-series obstruction
      record (the union over prefixes with the species-menu factor is the
      exact suspect, named in the record).
  P4 (phase 2 — sealed CONDITIONALLY, constants unknown at spec time): the
      prover's actual (C_T, c_T) passes the same in-box stress; failure =
      acceptance blocked, constants returned to the prover with the
      violating (p, h*) rows.

OUTPUT (run phase): PASS/FINDING rows appended to
probe_results_2026-07-30.txt; JSON to results/ke4_tails_stress.json; exit
0 = phase-1 seals clean, 1 = FINDING, and the phase flag recorded per run.

STATUS: E-PHASE SPEC — statement skeleton only; body pieces raise
NotImplementedError (the python `sorry`); running prints the spec and exits
3 (NOT-RUN).
"""

import json
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
RESULTS_TXT = os.path.join(HERE, 'probe_results_2026-07-30.txt')
OUTJSON = os.path.join(HERE, 'results', 'ke4_tails_stress.json')

PRIMES = [2, 3]
HSTAR_MAX = 8
REFERENCE_CANDIDATES = {'C_T3': 53, 'c_T3': 1}   # prior X-n3 sealed numbers

E_PHASE = True


def _todo(piece):
    raise NotImplementedError('KE4 E-phase skeleton (sorry): ' + piece)


def tall_event_masses(p, hstar_max=HSTAR_MAX):
    """Exact census masses frac(TallEvent h*) for h* = 1..hstar_max at
    n = 3: the mass of f whose branch history contains a first read of
    height >= h* (x_n3/X2B reader reuse; exact Fractions)."""
    _todo('tall-event mass census')


def fit_decay_exponent(masses, p):
    """Empirical decay exponent fit: c_T^emp from log_p of successive mass
    ratios (report the min/mean slope; P1 verdict c_T^emp > 0)."""
    _todo('decay-exponent fit')


def candidate_pair_from_sketch(p):
    """The EXPLICIT (C_T, c_T) the KE5 sketch implies: compose D4R.2's pool
    bound mu(P-hat) <= M(P-hat)·p^{W−A} over the first height->=h* read,
    summed over prefixes with the per-depth species-menu branching factor;
    return the computed pair + the composition ledger (each factor named)."""
    _todo('sketch-implied candidate computation (the D4R.2 composition)')


def stress_candidates(masses, pairs, p):
    """P2: check mass <= C_T·p^{−c_T·h*} for each candidate pair at every
    h* <= HSTAR_MAX; P3: divergence detector mass·p^{c_T·h*} trend."""
    _todo('candidate stress + divergence detector')


def phase2_stress(prover_constants):
    """PHASE 2 (BLOCKED until the KE5 draft): re-run stress_candidates
    against the prover's actual (C_T, c_T); acceptance-gating verdict."""
    _todo('phase 2 — blocked on the KE5 draft constants')


def main():
    print(__doc__)
    print('KE4: E-PHASE SPEC ONLY — body not implemented; NO probe was run;')
    print('sealed predictions P1-P4 above are on record as of 2026-07-30.')
    return 3


if __name__ == '__main__':
    sys.exit(main())
