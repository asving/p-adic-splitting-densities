/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.HC1.DefsCar
import LeanUrat.MovesC.C2_DOM
import LeanUrat.MovesC.C2_DOM_floorForm
import LeanUrat.Moves.L2_iaugRoot
import LeanUrat.Moves.L2_iaugStep
import LeanUrat.Moves.L2_iaugRecenter

/-!
# HC1.C4_DOM — Lemma DOM's DISPLAYED CONCLUSION (the G3-3 repair)

moves_ref: MOVES 3647–3651 "line_i(b) ≥ line_m(b) for all m < i; consequently the
floor is the current staircase". deps: DefsCar; MovesC `C2_DOM`,
`C2_DOM_floorForm`, `DomData` (proved, base-free); Moves `L2_iaugRoot`, `L2_iaugStep`, `L2_iaugRecenter` for the steeper chain (`L2_iaugStep` PROVED on disk with the
+Irreducible hypothesis, §4.2 CLOSED — instantiated here at TransHyp's own `hirr`).
Per-i interiors nest (MOVES 3683–3688), recorded. difficulty: medium.
hyp: `TowerRealizable` — (SAE)+(NA)+(HV) per move.
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

namespace LeanUrat.HC1

open Polynomial LeanUrat.Moves

/-- Unit C4: for a realizable tower, at every base index of the PER-i factor
interior and every m < i ≤ K, the current line dominates, and the floor form
holds there. -/
theorem C4_DOM {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
    (T : Tower p F) (rl : TowerRealizable T) (i : Fin (T.K + 1)) (m : ℕ)
    (hm : m < i.val) (b : ℕ) (hb : b < rl.interiorEnd i.val) :
    (rl.line m).at b ≤ (rl.line i.val).at b ∧
    MovesC.floorOf rl.line i.val b = (rl.line i.val).at b := by
  -- Package the (I-aug) steepness chain and the (SAE) vertex-entry seed recorded on
  -- the realizable tower as MovesC's `DomData` at the per-i interior end.
  have dom : MovesC.DomData rl.line i.val (rl.interiorEnd i.val) :=
    ⟨fun m' hm' => rl.steeper i m' hm', fun m' hm' => rl.vertex_entry i m' hm'⟩
  have hble : b ≤ rl.interiorEnd i.val := le_of_lt hb
  exact ⟨MovesC.C2_DOM dom b hble m (le_of_lt hm), MovesC.C2_DOM_floorForm dom b hble⟩

end LeanUrat.HC1

#print axioms LeanUrat.HC1.C4_DOM
