import Uniformity.ChapB.B82
import Uniformity.ChapB.B80

namespace Uniformity.Density.Leaf
open Polynomial IsLocalRing

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {π : O}

/-- The Gauss valuation, pinned to an explicit natural. -/
theorem gaussVal_eq_nat (hπ : Irreducible π) {k : ℕ} {a : Polynomial O}
    (h1 : ∀ i, π ^ k ∣ a.coeff i) (h2 : ∃ i, ¬ π ^ (k + 1) ∣ a.coeff i) :
    gaussVal a = (k : ℕ∞) := by
  have hle : (k : ℕ∞) ≤ gaussVal a := (le_gaussVal_iff hπ).2 h1
  have hnl : ¬ ((k + 1 : ℕ) : ℕ∞) ≤ gaussVal a := by
    intro hc
    obtain ⟨i, hi⟩ := h2
    exact hi ((le_gaussVal_iff hπ).1 hc i)
  refine le_antisymm ?_ hle
  by_contra hlt
  exact hnl (by exact_mod_cast Order.add_one_le_of_lt (not_le.1 hlt))

/-- degree-one polynomials over a field are separable. -/
theorem separable_of_natDegree_eq_one {K : Type*} [Field K] {p : Polynomial K}
    (h : p.natDegree = 1) : p.Separable := by
  have hne : p ≠ 0 := fun hc => by simp [hc] at h
  have hlc : p.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.2 hne
  have hd : Polynomial.derivative p = Polynomial.C p.leadingCoeff := by
    conv_lhs => rw [Polynomial.eq_X_add_C_of_natDegree_le_one (le_of_eq h)]
    simp [Polynomial.leadingCoeff, h]
  have hu : IsUnit (Polynomial.C p.leadingCoeff) :=
    (Polynomial.isUnit_C).2 (isUnit_iff_ne_zero.2 hlc)
  obtain ⟨v, hv⟩ := hu
  rw [Polynomial.Separable, hd]
  exact ⟨0, ↑v⁻¹, by rw [← hv]; simp⟩

end Uniformity.Density.Leaf
