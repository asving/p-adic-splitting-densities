/-
Unit D11a.mult_sum  (MovesD campaign, E-phase)
moves_ref: (double counting — the multiplicity sum equals the fiber-count sum).
deps: D2a.
sketch: Fintype double counting on the incidence set.  difficulty: medium.
hypothesis_fields: mult_sum carries hne (reads ≠ []) since D4″ 2026-07-29 (the ∅-dispatch
deviation, recorded below); mult_sum_opt (R3-B) is the uniform all-shapes form, none.
-/
import Mathlib
import LeanUrat.MovesD.Defs
import LeanUrat.MovesD.D2a_finite

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesD
open LeanUrat.Moves LeanUrat.MovesC

variable {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F] {n N m : ℕ}
  {pol : CanonPolicy p F} {P : Shape n}

/-- Double counting: Σ_x mult(x) = Σ_i #fiber(i).

Both counts enumerate the incidence set `{(x, i) : x ∈ S.fiber i}`: the left-hand side
groups it by the box coordinate `x` (each `mult x` is the number of classes whose fiber
contains `x`), the right-hand side by the class index `i` (each `#fiber(i)`). Both index
types are finite (`Box p m` is a Fintype; `PrefIdx` is `Finite` via D2a), so each
`Nat.card` is a filtered-cardinality, hence a sum of `{0,1}`-indicators, and the identity
is `Finset.sum_comm`.

[D4″ 2026-07-29 — FORCED hypothesis addition, recorded deviation]: `Presented.mult` now
carries the note's ∅ dispatch (reads = [] ↦ 1, L5/L12), under which this incidence
identity holds only on NONEMPTY shapes (at reads = [] the LHS is #Box ≠ 0 = RHS, PrefIdx
being empty by `Pref_empty_shape`); `hne` added. Both consumers (D12, D13) already carry
it. -/
theorem mult_sum (S : Presented p F n N m pol P)
    (hne : (P : ShapePrefix).reads ≠ []) :
    ∑ x : Box p m, S.mult x = ∑ᶠ i : PrefIdx n pol P, Nat.card ↥(S.fiber i) := by
  classical
  haveI : Fintype (PrefIdx n pol P) := Fintype.ofFinite _
  have hL : ∀ x : Box p m, S.mult x
      = ∑ i : PrefIdx n pol P, (if x ∈ S.fiber i then 1 else 0) := by
    intro x
    rw [S.mult_of_ne hne, Nat.card_eq_fintype_card, Fintype.card_subtype, Finset.card_filter]
  have hR : ∀ i : PrefIdx n pol P, Nat.card ↥(S.fiber i)
      = ∑ x : Box p m, (if x ∈ S.fiber i then 1 else 0) := by
    intro i
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype, Finset.card_filter]
  rw [finsum_eq_sum_of_fintype]
  simp only [hL, hR]
  exact Finset.sum_comm

open Classical in
/-- [R3-B, 2026-07-29 — confirm-2's queued option-level form] **The note-faithful UNIFORM
incidence law, over ALL shapes.** L5 includes the EMPTY prefix η = ∅ as a first-class
member (note ~4788–4800: "INCLUDING the EMPTY prefix η = ∅ (k = −1) … S(∅,⊤) = the box
(§C C.0's EMPTY HISTORY clause T(∅, Z) := Z, at Z = ⊤ …) — this empty case is the base of
L6's induction"), and Pref(∅) = {∅} (L12/F3), so on the EMPTY shape the note's incidence
identity reads Σ_x mult_∅(x) = #Box — the count THROUGH the unique ∅-class fiber
`emptyFiber = univ` — not zero. The RHS here is therefore OPTION-LEVEL: full-box
cardinality on the empty shape (the `none`/∅ class of `PrefOpt`, whose fiber is
`emptyFiber`), the `PrefIdx`-indexed fiber-count sum otherwise. `mult_sum` above (with
`hne`) is the PrefIdx-indexed FACE of this law — honest but empty-blind, because the Lean
`PrefIdx` cannot carry the ∅ class itself (the History type has no empty chain — F3's
displayed deviation, `Pref_empty_shape`). -/
theorem mult_sum_opt (S : Presented p F n N m pol P) :
    ∑ x : Box p m, S.mult x
      = if (P : ShapePrefix).reads = [] then Nat.card (Box p m)
        else ∑ᶠ i : PrefIdx n pol P, Nat.card ↥(S.fiber i) := by
  by_cases hP : (P : ShapePrefix).reads = []
  · rw [if_pos hP]
    simp [S.mult_empty_shape hP, Nat.card_eq_fintype_card]
  · rw [if_neg hP]
    exact mult_sum S hP

end LeanUrat.MovesD
