/-
Unit D13.D4R1_EV_iff  (MovesD campaign, E-phase)
moves_ref: "with EQUALITY iff mult_P̂ ≡ 1 on the event … count-equality ⟺ … mult_P̂ ≡ 1
POINTWISE on the event — the finite-level statement carries no measure-zero exception"
(D4R.1/L12).
deps: D10, D11a, D11b.
sketch: cancel p^{A′} (p ≥ 2); Finset double counting, pointwise.
difficulty: medium-hard.  hypothesis_fields: none beyond D10's.
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

/-- The EV equality criterion: count-equality ⟺ mult ≡ 1 pointwise on the event. -/
theorem D4R1_EV_iff (hne : (P : ShapePrefix).reads ≠ []) (N : ℕ)
    (hA : (P : ShapePrefix).A n N = (P : ShapePrefix).A' n)
    (S : Presented p F n N m pol P) :
    (Nat.card ↥S.event * p ^ ((P : ShapePrefix).A' n)
        = Nat.card (PrefIdx n pol P) * p ^ (n * N))
      ↔ (∀ x ∈ S.event, S.mult x = 1) := by
  classical
  -- p^{A'} > 0, so we may cancel it from the count-equality.
  have hp : 0 < p := (Fact.out : p.Prime).pos
  have hpA : 0 < p ^ ((P : ShapePrefix).A' n) := pow_pos hp _
  -- D10 (D4R1_SUM): (Σᶠ_i #fiber i)·p^{A'} = C·p^{nN}.
  have hsum := D4R1_SUM hne N hA S
  -- D11a (mult_sum): Σ_x mult x = Σᶠ_i #fiber i.  Combine into the multiplicity form.
  have key : (∑ x : Box p m, S.mult x) * p ^ ((P : ShapePrefix).A' n)
      = Nat.card (PrefIdx n pol P) * p ^ (n * N) := by
    rw [mult_sum S]; exact hsum
  -- The count-equality is equivalent to card(event) = Σ_x mult x (cancel p^{A'}).
  have hEQ : (Nat.card ↥S.event * p ^ ((P : ShapePrefix).A' n)
        = Nat.card (PrefIdx n pol P) * p ^ (n * N))
      ↔ (Nat.card ↥S.event = ∑ x : Box p m, S.mult x) := by
    constructor
    · intro h
      rw [← key] at h
      exact Nat.eq_of_mul_eq_mul_right hpA h
    · intro h; rw [h]; exact key
  -- mult x = 0 off the event, so the full sum collapses onto the event's toFinset.
  have hsupp : (∑ x : Box p m, S.mult x) = ∑ x ∈ S.event.toFinset, S.mult x := by
    refine (Finset.sum_subset (Finset.subset_univ S.event.toFinset) ?_).symm
    intro x _ hx
    rw [Set.mem_toFinset] at hx
    have hlt : ¬ 1 ≤ S.mult x := fun h => hx ((event_iff_mult S x).mpr h)
    omega
  -- card(event) is the sum of ones over the event's toFinset.
  have hcard : Nat.card ↥S.event = ∑ _x ∈ S.event.toFinset, 1 := by
    rw [← Finset.card_eq_sum_ones, Set.toFinset_card, ← Nat.card_eq_fintype_card]
  -- On the event every multiplicity is ≥ 1 (D11b), so double-counting gives the pointwise iff.
  have hle : ∀ x ∈ S.event.toFinset, (1 : ℕ) ≤ S.mult x := by
    intro x hx
    rw [Set.mem_toFinset] at hx
    exact (event_iff_mult S x).mp hx
  rw [hEQ, hcard, hsupp, Finset.sum_eq_sum_iff_of_le hle]
  simp only [Set.mem_toFinset, eq_comm]

end LeanUrat.MovesD
