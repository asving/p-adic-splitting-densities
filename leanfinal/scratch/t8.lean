import Uniformity.ChapB.B82

namespace Uniformity.Density.Leaf
open Polynomial IsLocalRing

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {π : O}

axiom resFactorFinset_eq_singleton (hπ : Irreducible π) {φ : Polynomial O} (hφ : IsKey φ)
    {f : Polynomial O} (hf : f.Monic) {μ : ℕ} (hdeg : f.natDegree = μ * φ.natDegree)
    {u ℓ : ℕ} (hℓ : 0 < ℓ) (hcop : Nat.Coprime u ℓ)
    (hne : (sideSet φ f u ℓ).Nonempty) (hd1 : sideDeg φ f u ℓ hne = 1) :
    ∃ ψ₀ : Polynomial (resField φ),
      resFactorFinset π φ f (u, ℓ) = {ψ₀} ∧ ψ₀.natDegree = 1

axiom separable_of_natDegree_eq_one {K : Type*} [Field K] {p : Polynomial K}
    (h : p.natDegree = 1) : p.Separable

theorem order1Type_of_sideDeg_one (hπ : Irreducible π) {φ : Polynomial O} (hφ : IsKey φ)
    {f : Polynomial O} (hf : f.Monic) {μ : ℕ} (hdeg : f.natDegree = μ * φ.natDegree)
    (hd1 : ∀ p ∈ slopeFinset π φ f, ∀ hne : (sideSet φ f p.1 p.2).Nonempty,
      sideDeg φ f p.1 p.2 hne = 1) :
    order1Type π φ f = ⟨(slopeFinset π φ f).val.map (fun p => (p.2, φ.natDegree))⟩ := by
  classical
  rw [order1Type]
  congr 1
  rw [← Multiset.bind_singleton (s := (slopeFinset π φ f).val)
    (f := fun p : ℕ × ℕ => (p.2, φ.natDegree))]
  refine Multiset.bind_congr fun p hp => ?_
  have hp' : p ∈ slopeFinset π φ f := hp
  obtain ⟨hℓ, hcop, -⟩ := mem_slopeFinset_imp hp'
  have hne : (sideSet φ f p.1 p.2).Nonempty := sideSet_nonempty hφ.monic hφ.pos hf hdeg p.1 p.2
  obtain ⟨ψ₀, hsing, hψdeg⟩ :=
    resFactorFinset_eq_singleton hπ hφ hf hdeg hℓ hcop hne (hd1 p hp' hne)
  have : resFactorFinset π φ f p = {ψ₀} := by
    rw [← hsing]
  rw [this]
  simp [hψdeg]

theorem not_needsDescent_of_sideDeg_one (hπ : Irreducible π) {φ : Polynomial O} (hφ : IsKey φ)
    {f : Polynomial O} (hf : f.Monic) {μ : ℕ} (hdeg : f.natDegree = μ * φ.natDegree)
    (hd1 : ∀ u ℓ : ℕ, 0 < ℓ → Nat.Coprime u ℓ → 1 < (sideSet φ f u ℓ).card →
      ∀ hne : (sideSet φ f u ℓ).Nonempty, sideDeg φ f u ℓ hne = 1) :
    ¬ NeedsDescent π φ f := by
  classical
  letI := instFieldResField hφ
  rintro ⟨u, ℓ, hne, H₀, hℓ, hcop, hcard, hH₀, hsep⟩
  have htop : suppVal φ f u ℓ ≠ ⊤ :=
    ne_top_of_le_ne_top (ENat.coe_ne_top _) (suppVal_ne_top hφ.monic hφ.pos hf hdeg u ℓ)
  obtain ⟨hPdeg, -⟩ := natDegree_resPoly hπ hφ hℓ hcop htop hne hH₀
  exact hsep (separable_of_natDegree_eq_one (by rw [hPdeg, hd1 u ℓ hℓ hcop hcard hne]))

end Uniformity.Density.Leaf
