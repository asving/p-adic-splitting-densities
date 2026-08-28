import Uniformity.ChapB.B82

namespace Uniformity.Density.Leaf
open Polynomial IsLocalRing

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {π : O}

theorem resFactorFinset_eq_singleton (hπ : Irreducible π) {φ : Polynomial O} (hφ : IsKey φ)
    {f : Polynomial O} (hf : f.Monic) {μ : ℕ} (hdeg : f.natDegree = μ * φ.natDegree)
    {u ℓ : ℕ} (hℓ : 0 < ℓ) (hcop : Nat.Coprime u ℓ)
    (hne : (sideSet φ f u ℓ).Nonempty) (hd1 : sideDeg φ f u ℓ hne = 1) :
    ∃ ψ₀ : Polynomial (resField φ),
      resFactorFinset π φ f (u, ℓ) = {ψ₀} ∧ ψ₀.natDegree = 1 := by
  classical
  letI := instFieldResField hφ
  have htop : suppVal φ f u ℓ ≠ ⊤ :=
    ne_top_of_le_ne_top (ENat.coe_ne_top _) (suppVal_ne_top hφ.monic hφ.pos hf hdeg u ℓ)
  have honside : OnSide φ f u ℓ (sideMin φ f u ℓ hne) :=
    onSide_of_mem_sideSet (Finset.min'_mem _ hne)
  obtain ⟨H₀, hH₀⟩ := ENat.ne_top_iff_exists.1 (npHgt_ne_top_of_onSide hℓ htop honside)
  have hH₀' : npHgt φ f (sideMin φ f u ℓ hne) = (H₀ : ℕ∞) := hH₀.symm
  obtain ⟨hPdeg, hPc0⟩ := natDegree_resPoly hπ hφ hℓ hcop htop hne hH₀'
  set P := resPoly π φ f u ℓ hne H₀ with hP
  have hPdeg1 : P.natDegree = 1 := by rw [hPdeg, hd1]
  have hP0 : P ≠ 0 := fun hc => by
    rw [hc] at hPdeg1; simp at hPdeg1
  set ψ₀ : Polynomial (resField φ) := P * Polynomial.C P.leadingCoeff⁻¹ with hψ₀
  have hψ₀mon : ψ₀.Monic := Polynomial.monic_mul_leadingCoeff_inv hP0
  have hψ₀deg : ψ₀.natDegree = 1 := by
    rw [hψ₀, Polynomial.natDegree_mul_leadingCoeff_inv _ hP0, hPdeg1]
  have hψ₀irr : Irreducible ψ₀ := by
    apply Polynomial.irreducible_of_degree_eq_one
    rw [Polynomial.degree_eq_natDegree hψ₀mon.ne_zero, hψ₀deg]
    rfl
  have hPeq : P = ψ₀ * Polynomial.C P.leadingCoeff := by
    rw [hψ₀, mul_assoc, ← Polynomial.C_mul,
      inv_mul_cancel₀ (Polynomial.leadingCoeff_ne_zero.2 hP0), Polynomial.C_1, mul_one]
  have hulc : IsUnit (Polynomial.C P.leadingCoeff) :=
    (Polynomial.isUnit_C).2 (isUnit_iff_ne_zero.2 (Polynomial.leadingCoeff_ne_zero.2 hP0))
  refine ⟨ψ₀, ?_, hψ₀deg⟩
  ext ψ
  rw [mem_resFactorFinset hπ hφ hf hdeg hℓ hcop, Finset.mem_singleton]
  constructor
  · rintro ⟨hmon, hirr, hdvd⟩
    have hd : ψ ∣ P := hdvd hne H₀ hH₀'
    have hd0 : ψ ∣ ψ₀ := (hulc.dvd_mul_right).1 (hPeq ▸ hd)
    obtain ⟨q, hq⟩ := hd0
    have hnu : ¬ IsUnit ψ := hirr.not_isUnit
    rcases hψ₀irr.isUnit_or_isUnit hq with h | h
    · exact absurd h hnu
    · exact (Polynomial.eq_of_monic_of_associated hmon hψ₀mon ⟨h.unit, by
        rw [hq]; simp [IsUnit.unit_spec]⟩)
  · rintro rfl
    refine ⟨hψ₀mon, hψ₀irr, fun hne' H₀' hH₀'' => ?_⟩
    have : (H₀' : ℕ∞) = (H₀ : ℕ∞) := by rw [← hH₀'', hH₀']
    have hEq : H₀' = H₀ := by exact_mod_cast this
    subst hEq
    exact Dvd.intro _ hPeq.symm

end Uniformity.Density.Leaf
