/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import LeanUrat.MovesT.TV_A1
import LeanUrat.MovesT.TV_A5b_forge

/-! # TV-A5b — the stray-countermodel ATTEMPT at n = 2 (necessity probe for (U)∧(R))

BRIDGE CAMPAIGN unit **TV-A5b** (area BP3, cluster A; blueprint
`lean/notes/BRIDGE_BP3_TV_2026-07-30.md` §3.A(ii) + §4 + risk R4; REV 2 finding
12, split from the old A5). **GATE UNIT (countermodel-attempt)** — E-PHASE
SKELETON: docstring states the sealed prediction; the body is the countermodel
construction attempt with `sorry` placeholders.

SEALED PREDICTION (the standing fence record, E5_rootSplit.lean:311-342 + risk
R4): the (U)∧(R) pair is believed NOT derivable from the `CellData`/`CellAssign`
laws — the recorded countermodel shape is a STRAY root child realized on a
`.red`-cell DISJOINT from the fiber's own cells but inside the same root cell
{f̄ = g}. If that shape is compilable at n = 2, the pair's NECESSITY as a named
hypothesis is certified. INTENDED WITNESS (blueprint): extend G1 carrier A's
tables (`toyModel : TreeModel 2 (ZMod 2) 2 3 9 polTriv`, G1_toyGate.lean:528 —
which deliberately stops at the `CellData` layer because `child_cover` FAILS at
g = (1,0)) with a child at track X + 1 on the g = (1, 0) cell: there
`redPoly χ x = X² + 1 = (X + 1)²` over `ZMod 2` (repeated), so `child_cover`
FORCES a child at track X + 1; add one, then probe whether (U) or (R) can be
broken while EVERY `CellData`/`CellAssign` law holds. Candidate blocking laws to
check (each named if it fires): `child_red_uniform` (kills SAME-cell strays),
`RedCellPartition`'s ψ-keying clause 3, `child_cell_red`.

ALLOWED OUTCOME (blueprint, verbatim): "blocked by law L" with L named — an
acceptable deliverable that UPGRADES the fence record instead of refuting the
pair. Deliverable either way is recorded at the TV-A1 docstrings (prover-phase
edit) and reported to the orchestrator.

STATEMENT RESOLUTION (recorded): the probe is stated as one `∃`-sentence over
its own carriers (N, m, pol, T, χ, trackOf, CellAssign, g) rather than
importing G1's 2200-line toy module — the intended witness (carrier-A extension
at g = ![1, 0]) is docstring-pinned; the ∃-form keeps imports minimal and the
statement independent of the eventual carrier layout.

deps: TV-A1, TV-A5a (carrier machinery pattern reuse at prover time).
difficulty: hard-fable, ~90 lines or blocked-record (blueprint estimate). -/

set_option linter.style.longLine false
set_option linter.unusedVariables false

namespace LeanUrat.MovesT

open Polynomial LeanUrat.Moves LeanUrat.MovesC LeanUrat.MovesD

/-- TV-A5b piece (the pinned reduction check): on the g = (1, 0) root cell over
`ZMod 2` at n = 2, the level-0 reduction is the repeated square
`redPoly χ x = X² + 1 = (X + 1)²` — the cell where `child_cover` FORCES a child
at track X + 1 (the probe's insertion point). -/
theorem stray_redPoly_repeated (m : ℕ) (χ : Fin 2 → Fin m) (x : Box 2 m)
    (hx : x ∈ rootCell χ ![1, 0]) :
    redPoly χ x = (Polynomial.X + Polynomial.C 1) ^ 2 := by
  have hx' : ∀ b : Fin 2, x (χ b) = ![1, 0] b := hx
  have h0 : x (χ 0) = 1 := by simpa using hx' 0
  have h1 : x (χ 1) = 0 := by simpa using hx' 1
  rw [add_pow_char]
  unfold redPoly
  rw [Fin.sum_univ_two, h0, h1]
  simp [Polynomial.C_1]

/-- **TV-A5b, the probe statement**: a full `CellAssign` carrier at n = 2 over
`ZMod 2` at which the TV-A1 pair FAILS — the compiled-negation branch of the
gate. The sealed prediction and the "blocked by law L" alternative outcome are
in the module docstring; if every construction route is blocked, this
declaration is NOT to be forced — the unit returns the blocking law instead
(honest-sorries discipline). -/
theorem stray_countermodel_attempt :
    ∃ (N m : ℕ) (pol : CanonPolicy 2 (ZMod 2))
      (T : TreeModel 2 (ZMod 2) 2 N m pol)
      (χ : Fin 2 → Fin m) (trackOf : Node 2 (ZMod 2) → Polynomial (ZMod 2))
      (_ : CellAssign 2 (ZMod 2) 2 N m pol T χ trackOf)
      (g : Fin 2 → ZMod 2),
      ¬ (TrackUniqOn T χ trackOf g ∧ TrackRepOn T χ trackOf g) := by
  -- piece 1: carrier-A extension tables (a child at track X + 1 on the g = (1,0)
  --          cell; `stray_redPoly_repeated` is the forcing computation)
  -- piece 2: the CellData re-check at the extended tables (child_cell /
  --          child_root_sub / child_cell_red / child_red_uniform / branch laws)
  -- piece 3: child_cover at the extended tables (now satisfiable at g = (1,0))
  -- piece 4: the stray breaking (U) (second child sharing track X + 1 on a
  --          disjoint .red-cell) or (R) (a child on a multiplicity-1 track)
  exact stray_countermodel_witness

end LeanUrat.MovesT
