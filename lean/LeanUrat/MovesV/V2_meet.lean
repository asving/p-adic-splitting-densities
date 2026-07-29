/-  MovesV unit V2-3 `meet_finite_uniform` — clause (i)'s proved core: the
    product-of-generators cell map partitions the carrier, finitely, with the
    p-independent label set. -/
import LeanUrat.MovesV.Defs

set_option linter.style.longLine false
set_option linter.style.header false

namespace LeanUrat.MovesV

theorem meet_finite_uniform {n : ℕ} {s : Skeleton n} (B : BlockData n s)
    (q₀ : ℚ) :
    (∀ x : B.Carrier q₀, ∃! a : ∀ g : B.Gen, (B.gen g).idx,
       ∀ g, (B.gen g).part q₀ x = a g) ∧
    Finite (∀ g : B.Gen, (B.gen g).idx) := by
  constructor
  · intro x
    refine ⟨fun g => (B.gen g).part q₀ x, fun g => rfl, ?_⟩
    intro y hy
    funext g
    exact (hy g).symm
  · haveI := B.finG
    haveI := fun g => (B.gen g).finI
    infer_instance

end LeanUrat.MovesV
