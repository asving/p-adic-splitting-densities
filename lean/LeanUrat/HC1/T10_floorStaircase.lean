/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.HC1.DefsCar
import LeanUrat.MovesC.C2_DOM_floorForm

/-!
# HC1.T10_floorStaircase — on factor-interior blocks the coordinate STEP floor is the
block staircase

moves_ref: MOVES 3743–3745 (LST(ii)) + 3650–3651 (DOM: "the floor is the current
staircase: F_i(b) = old_i(slot(b))"). deps: T3, C4 (DOM_real), MovesC
`C2_DOM_floorForm` (proved). The first conjunct (`floorB b = (lines K).at
(blockEdge b)`) is DEFINITIONAL (rfl-level; the F3-3 repair by construction).
difficulty: medium. hyp: `TowerRealizable` (the realizability chain (SAE)/(NA)/(HV)
of the tower's moves — §5's open kernel, carried as `rl`).

**F-1 RESTATEMENT (sign-off event 2026-07-28, blueprint §9.1):** conjunct 2 was
MACHINE-REFUTED on the raw-line pointwise floor `floorC`
(`ScratchT10.T10_conjunct2_refuted`, retained: on any realizable tower, any
factor-interior block, any coordinate with a nonzero sub-top slot,
`floorC c < floorB b` STRICTLY — slope-K > 0 is forced by `slope_law` + κ
positivity, and `Line.at` descends across the block). The note's floor is old_i
evaluated at the SLOT of b — a STEP function constant on each current block
(MovesC's own `Node.lineStep`/`History.floorH` convention). Conjunct 2 is RESTATED
on the F-1 step floor `floorS` (DefsCar); `floorC` stays for the DOM-side
consumers; conjunct 1 and the hypotheses are unchanged. PROOF ROUTE (blueprint
§9.1, checked on the refutation kernel's own lemmas): the m = K summand of the sup'
is exactly `floorB b` (frame-K quantization of `baseIdx c = OFF + blockEdge b` with
`OFF < deg Φ_top` returns `blockEdge b`); for m < K the frame-m edge is ≥ the
frame-K edge (nested radices `frameWidth (m+1) ∣ frameWidth (K+1)`), `Line.at`
decreasing gives `lineStep m ≤ (rl.line m).at (blockEdge b)`, and DOM
(`C2_DOM_floorForm.dom_le` at `blockEdge b ≤ interiorEnd`) caps it by `floorB b`.
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

namespace LeanUrat.HC1

open Polynomial LeanUrat.Moves

/-- Unit T10: the staircase equation (rfl-level) + THE CONTENT (F-1 restated): on
factor-interior blocks the history STEP floor at every block coordinate equals the
block staircase value. -/
theorem T10_floorStaircase {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
    (T : Tower p F) (rl : TowerRealizable T) (b : ℕ) (hb : rl.interiorB b) :
    rl.floorB b = (rl.line T.K).at (T.blockEdge b) ∧
    (∀ c : T.Coord, T.blk c = b → rl.floorS c = rl.floorB b) := by
  sorry

end LeanUrat.HC1

#print axioms LeanUrat.HC1.T10_floorStaircase
