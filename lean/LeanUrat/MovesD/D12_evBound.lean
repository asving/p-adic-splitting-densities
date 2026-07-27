/-
Unit D12.D4R1_EV  (MovesD campaign, E-phase)
moves_ref: "μ(P̂) ≤ C_P̂(p)·p^{−A(P̂)} (D4R.1-EV) by subadditivity" ≡ "(D4R.4-EV) … the
union bound within the level-N box", at every N ≥ N(P̂) (same quantifier note as D10).
deps: D10, D11a, D11b.
sketch: card event = #{mult ≥ 1} ≤ Σ mult.  difficulty: medium.
hypothesis_fields: none beyond D10's.
-/
import Mathlib
import LeanUrat.MovesD.Defs
import LeanUrat.MovesD.D10_sumLaw
import LeanUrat.MovesD.D11a_multSum
import LeanUrat.MovesD.D11b_eventMult

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesD
open LeanUrat.Moves LeanUrat.MovesC

variable {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F] {n m : ℕ}
  {pol : CanonPolicy p F} {P : Shape n}

/-- D4R.1-EV ≡ D4R.4-EV: the union bound, division-free. -/
theorem D4R1_EV (hne : (P : ShapePrefix).reads ≠ []) (N : ℕ)
    (hA : (P : ShapePrefix).A n N = (P : ShapePrefix).A' n)
    (S : Presented p F n N m pol P) :
    Nat.card ↥S.event * p ^ ((P : ShapePrefix).A' n)
      ≤ Nat.card (PrefIdx n pol P) * p ^ (n * N) := by
  classical
  -- The union-bound core: #{event} = #{x : mult x ≥ 1} ≤ Σ_x mult x.
  have hsum : Nat.card ↥S.event ≤ ∑ x : Box p m, S.mult x := by
    rw [Nat.card_coe_set_eq, Set.ncard_eq_toFinset_card']
    calc S.event.toFinset.card
        = ∑ _x ∈ S.event.toFinset, 1 := by rw [Finset.card_eq_sum_ones]
      _ ≤ ∑ x ∈ S.event.toFinset, S.mult x := by
          apply Finset.sum_le_sum
          intro x hx
          rw [Set.mem_toFinset] at hx
          exact (event_iff_mult S x).mp hx
      _ ≤ ∑ x : Box p m, S.mult x :=
          Finset.sum_le_sum_of_subset (Finset.subset_univ _)
  -- Multiply the union bound by p^{A′} and close with D11a (double counting) + D10 (SUM).
  calc Nat.card ↥S.event * p ^ ((P : ShapePrefix).A' n)
      ≤ (∑ x : Box p m, S.mult x) * p ^ ((P : ShapePrefix).A' n) :=
        Nat.mul_le_mul_right _ hsum
    _ = (∑ᶠ i : PrefIdx n pol P, Nat.card ↥(S.fiber i)) * p ^ ((P : ShapePrefix).A' n) := by
        rw [mult_sum]
    _ = Nat.card (PrefIdx n pol P) * p ^ (n * N) := D4R1_SUM hne N hA S

end LeanUrat.MovesD
