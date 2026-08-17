import Uniformity.ChapC.C107

namespace Scratch

theorem factors_mul_unit {α : Type*} [CommMonoidWithZero α] [UniqueFactorizationMonoid α]
    {c a : α} (hc : IsUnit c) :
    UniqueFactorizationMonoid.factors (c * a) = UniqueFactorizationMonoid.factors a := by
  classical
  rcases eq_or_ne a 0 with rfl | ha
  · simp
  have hca : c * a ≠ 0 := fun h => ha (hc.mul_right_eq_zero.1 h)
  have hassoc : Associated (c * a) a := (associated_unit_mul_left a c hc)
  have hpred : (fun f : Multiset α => (∀ b ∈ f, Prime b) ∧ Associated f.prod (c * a))
      = (fun f : Multiset α => (∀ b ∈ f, Prime b) ∧ Associated f.prod a) := by
    funext f
    exact propext ⟨fun h => ⟨h.1, h.2.trans hassoc⟩, fun h => ⟨h.1, h.2.trans hassoc.symm⟩⟩
  rw [UniqueFactorizationMonoid.factors, UniqueFactorizationMonoid.factors,
    dif_neg hca, dif_neg ha]
  congr 1

#print axioms Scratch.factors_mul_unit

end Scratch
