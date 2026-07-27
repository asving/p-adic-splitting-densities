/-
Unit D11a.mult_sum  (MovesD campaign, E-phase)
moves_ref: (double counting — the multiplicity sum equals the fiber-count sum).
deps: D2a.
sketch: Fintype double counting on the incidence set.  difficulty: medium.
hypothesis_fields: none.
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
is `Finset.sum_comm`. -/
theorem mult_sum (S : Presented p F n N m pol P) :
    ∑ x : Box p m, S.mult x = ∑ᶠ i : PrefIdx n pol P, Nat.card ↥(S.fiber i) := by
  classical
  haveI : Fintype (PrefIdx n pol P) := Fintype.ofFinite _
  have hL : ∀ x : Box p m, S.mult x
      = ∑ i : PrefIdx n pol P, (if x ∈ S.fiber i then 1 else 0) := by
    intro x
    rw [Presented.mult, Nat.card_eq_fintype_card, Fintype.card_subtype, Finset.card_filter]
  have hR : ∀ i : PrefIdx n pol P, Nat.card ↥(S.fiber i)
      = ∑ x : Box p m, (if x ∈ S.fiber i then 1 else 0) := by
    intro i
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype, Finset.card_filter]
  rw [finsum_eq_sum_of_fintype]
  simp only [hL, hR]
  exact Finset.sum_comm

end LeanUrat.MovesD
