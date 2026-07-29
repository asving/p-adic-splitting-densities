/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.MovesT.Defs

/-! # T-F4 `belowHalt_decomp` — the note's EXACT below-halt decomposition (MOVES
7606–7611), REV 8 (Codex-7 #5 = Fable-7 CRIT-2): the `hne` premise joins (the built
D11a `mult_sum`'s own), and the ∅-shape truth is the displayed COMPANION
(`mult_empty_shape` cited BY NAME; the uniform incidence form is MovesD's
`mult_sum_opt`, not this unit's). THE FENCE: no consumer may convert the excess to a
per-f quantity without first restricting to Pref^τ — conversion runs through
TREE-EXP's fiber expansion ONLY. -/

set_option linter.style.longLine false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesT

open Polynomial LeanUrat.Moves LeanUrat.MovesC LeanUrat.MovesD

variable {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
variable {n N m : ℕ} {pol : CanonPolicy p F}

theorem belowHalt_decomp {P : Shape n} (S : Presented p F n N m pol P)
    (T : TreeModel p F n N m pol) (χ : Fin n → Fin m) (x : Box p m)
    (hne : (P : ShapePrefix).reads ≠ []) :
    S.mult x
      = Nat.card {i : PrefIdx n pol P // x ∈ S.fiber i ∧ PreHalt (reprOf i)}
      + Nat.card {i : PrefIdx n pol P // x ∈ S.fiber i ∧ ¬ PreHalt (reprOf i)} := by
  sorry

/-- the ∅-shape display (REV 8): `mult x = 1` is the built
`Presented.mult_empty_shape` VERBATIM; the `PrefIdx` emptiness is why the two-count
decomposition CANNOT be stated there. PROVED. -/
theorem belowHalt_empty_shape {P : Shape n} (S : Presented p F n N m pol P)
    (x : Box p m) (hP : (P : ShapePrefix).reads = []) :
    S.mult x = 1 ∧ IsEmpty (PrefIdx n pol P) := by
  refine ⟨Presented.mult_empty_shape S hP x, ⟨fun i => ?_⟩⟩
  obtain ⟨H, hH, _⟩ := i.2
  obtain ⟨hlen, _⟩ := hH.1
  rw [hP] at hlen
  simp only [List.length_nil] at hlen
  exact H.nonempty (List.length_eq_zero_iff.mp hlen)

/-- rev 1's ≤ form, kept as the excess corollary (same `hne`). -/
theorem belowHalt_excess {P : Shape n} (S : Presented p F n N m pol P)
    (T : TreeModel p F n N m pol) (χ : Fin n → Fin m) (x : Box p m)
    (hne : (P : ShapePrefix).reads ≠ []) :
    Nat.card {i : PrefIdx n pol P // x ∈ S.fiber i ∧ PreHalt (reprOf i)}
      ≤ S.mult x := by
  sorry

end LeanUrat.MovesT
