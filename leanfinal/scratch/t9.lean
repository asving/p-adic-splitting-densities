import Uniformity.ChapB.B82

namespace Uniformity.Density.Leaf
open Polynomial IsLocalRing

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {π : O}

theorem npHgt_eq_top_of_gt {φ : Polynomial O} (hφ : φ.Monic) (hd : 0 < φ.natDegree)
    {f : Polynomial O} (hf : f.Monic) {μ : ℕ} (hdeg : f.natDegree = μ * φ.natDegree)
    {j : ℕ} (hj : μ < j) : npHgt φ f j = ⊤ :=
  npHgt_eq_top_iff.2 (dev_eq_zero_of_lt hφ hd f j (by
    rw [hdeg]; exact Nat.mul_lt_mul_of_lt_of_le hj (le_refl _) hd))

example {ℓ : ℕ} (hℓ : 0 < ℓ) : ℓ • (⊤ : ℕ∞) = ⊤ := by
  simp [hℓ.ne']

example {ℓ : ℕ} : ℓ • (1 : ℕ∞) = (ℓ : ℕ∞) := by simp

example {ℓ : ℕ} : ℓ • (0 : ℕ∞) = (0 : ℕ∞) := by simp

end Uniformity.Density.Leaf
