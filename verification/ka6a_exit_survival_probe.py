#!/usr/bin/env python3
"""ka6a_exit_survival_probe.py — UNIT KA6a (bridge campaign, area BP4, cluster
BP4-c1, GATE unit) — the exit-cell survival probe.

[CM-first for KA6b2 — this probe is an explicit dependency of the KA6b2 prover
and MUST run (and its record land) BEFORE that prover is assigned.]

STATEMENT (blueprint BRIDGE_BP4_KERNELS_2026-07-30.md §4 KA6a + §3.A (1d) +
risk R1): for synthetic (K-SUB)-shaped tables at pools q0 in {2, 3, 4, 8, 9}
and states with anchored windows, SEARCH for a (state, pool) whose EVERY exit
cell dies (cell count 0 at q0).  SEARCH ORDER (REV 2, F2): anchored states
with pin a >= 2 FIRST — there the squarefree-residual mechanism is provably
ABSENT (z^2 divides every residual regardless of the free window digits), so
any survival must come from a DIFFERENT exit (the cofactor criterion); that
zone is likeliest to refute the per-state form.  A finding REFUTES the
per-state form of E0's escape (row sum < 1 at every realized active state)
and REROUTES KA6b2 to the class-level statement (KA2c reachability from
anchored states).  A finding does NOT refute E0 itself.

DEPS: none (gate unit; verification/ infra only).  Carriers: the M-SPECIES
menu (lean/LeanUrat/MovesSp) transcribed, or a self-contained window model —
the Q1-ratified Kernels/ placement does not bind this python side; the
transcription choice is recorded at run time in the results block.

SKETCH (blueprint §3.A route 1 (1d)): per (state, pool) enumerate the exit
cells of the (K-SUB) classification (terminal/hen + split columns); a cell
"dies" at q0 when its cell-count polynomial vanishes at q = q0 (the probes
already show p = 2 kills six cells — escape_probe_a §2 sealed list); the
per-state form needs only that SOME exit cell survives at every (state, q0).
Case split on the anchor pin a of the state's window:
  a = 0: some free-digit choice makes the residual squarefree
         (count q^e - q^{e-1} > 0 for e >= 2, q >= 2; degree-1 separable);
  a = 1: target z * (squarefree cofactor coprime to z) — same count one
         degree down;
  a >= 2: NO residual is squarefree (KA6b1's compiled impossibility);
         search the anchored read's cofactor-criterion exit instead.

SEALED PREDICTIONS (Q6 discipline — sealed 2026-07-30, BEFORE any run;
recorded here at E-phase spec time; a run that contradicts a seal is a
FINDING, adjudicated, never patched):
  P1 (consistency, must hold — compiled arithmetic): at every a >= 2
      anchored state, the squarefree-residual exit count is 0 at EVERY pool
      (z^2 | every residual).  This leg checks the model transcription, not
      a conjecture; failure = transcription bug, stop and adjudicate.
  P2 (the load-bearing seal): at every a <= 1 state and every
      q0 in {2, 3, 4, 8, 9}, some free window-digit choice yields a
      squarefree residual — i.e. a surviving terminal/hen exit cell;
      per-state row sum < 1 follows (KA5 shape).
  P3 (OPEN — deliberately NOT sealed): whether every a >= 2 (state, pool)
      retains SOME exit cell (the cofactor-criterion exit).  Either outcome
      is a deliverable: all survive => KA6b2 keeps the per-state target at
      a >= 2 via the cofactor mechanism; a (state, pool) with ALL exit
      cells dead => FINDING, KA6b2 rerouted to the class-level escape, the
      obstruction record pins the window-to-residual coefficient map and
      the resisting (state, pool).
  P4 (context re-check): at q0 = 2 the six known dead cells of the sealed
      escape_probe_a §2 list reappear ('A.3dist', 'A.dblsimple',
      'C_even.dist', 'D_even.dist', 'm2.o_split', 'root.m_H3');
      INDIVIDUAL cell death is expected and is NOT a finding — only
      all-exit death at a single state is.

OUTPUT (run phase): PASS/FINDING rows appended to
probe_results_2026-07-30.txt; JSON to results/ka6a_exit_survival.json;
exit code 0 = all sealed legs PASS (P3 recorded either way), 1 = FINDING.

STATUS: E-PHASE SPEC — statement skeleton only.  Body pieces below raise
NotImplementedError (the python analogue of `sorry`); running this file
prints the spec and exits with code 3 (NOT-RUN) so a spec can never be
mistaken for a probe run.
"""

import json
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
RESULTS_TXT = os.path.join(HERE, 'probe_results_2026-07-30.txt')
OUTJSON = os.path.join(HERE, 'results', 'ka6a_exit_survival.json')

POOLS = [2, 3, 4, 8, 9]          # q0 sweep (blueprint-specified)
DEAD_CELLS_Q2 = ['A.3dist', 'A.dblsimple', 'C_even.dist', 'D_even.dist',
                 'm2.o_split', 'root.m_H3']   # escape_probe_a §2 sealed list

E_PHASE = True


def _todo(piece):
    raise NotImplementedError('KA6a E-phase skeleton (sorry): ' + piece)


def build_ksub_tables(q0):
    """Synthetic (K-SUB)-shaped tables at pool q0: states = realized active
    window states (anchor pin a, window shape, e_read), columns = exit cells
    (terminal/hen + split) and still-in-block cells, entries = cell-count
    polynomials evaluated at q = q0."""
    _todo('synthetic (K-SUB) table builder (M-SPECIES transcription or '
          'self-contained window model; record the choice)')


def anchored_states(tables, a_min=0, a_max=None):
    """Enumerate states with anchor pin a in [a_min, a_max], SORTED so that
    a >= 2 states come FIRST (the F2-mandated search order)."""
    _todo('anchored-state enumeration, a >= 2 first')


def exit_cells(state):
    """The exit cells (terminal/hen + split columns) of a state under the
    (K-SUB) classification."""
    _todo('exit-cell extraction per state')


def cell_count_at_pool(cell, q0):
    """Evaluate the cell-count polynomial at q = q0 (exact integer)."""
    _todo('cell-count evaluation')


def squarefree_residual_count(state, q0):
    """Number of free window-digit choices whose residual is squarefree
    (the P1/P2 legs; must be 0 at a >= 2 by compiled arithmetic)."""
    _todo('window-to-residual map + squarefree count')


def sweep():
    """Main sweep: for each pool q0 and each state (a >= 2 first), record
    surviving exit cells; FINDING iff some (state, pool) has all exit cells
    dead.  Emit P1-P4 verdicts."""
    _todo('the sweep')


def main():
    print(__doc__)
    print('KA6a: E-PHASE SPEC ONLY — body not implemented; NO probe was run;')
    print('sealed predictions P1-P4 above are on record as of 2026-07-30.')
    return 3   # NOT-RUN sentinel (0/1 are reserved for the run phase)


if __name__ == '__main__':
    sys.exit(main())
