import Uniformity.ChapB.B82

namespace Uniformity.Density.Leaf
open Polynomial IsLocalRing

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {π : O}

theorem perim_core (hπ : Irreducible π) {φ : Polynomial O} (hφ : IsKey φ)
    {gT : Polynomial O} (hgT : gT.Monic) {μ : ℕ}
    (hresT : gT.map (residue O) = (φ.map (residue O)) ^ μ)
    {u ℓ : ℕ} (hℓ : 0 < ℓ)
    {gS : Polynomial O} (hgS : gS.Monic) (hdvd : gS ∣ gT)
    (hpure : IsPure φ gS u ℓ)
    (hne : (sideSet φ gS u ℓ).Nonempty) {H₀ : ℕ}
    (hH₀ : npHgt φ gS (sideMin φ gS u ℓ hne) = (H₀ : ℕ∞))
    {ψ : Polynomial (resField φ)} (hψi : Irreducible ψ)
    (hcψ : ∃ c : (resField φ)ˣ, resPoly π φ gS u ℓ hne H₀ = c • ψ)
    (hcop : Nat.Coprime u ℓ) :
    ∃ k : ℕ, k ≤ μ ∧ gS.natDegree = k * φ.natDegree ∧ ℓ * ψ.natDegree = k
      ∧ 1 ≤ ψ.natDegree ∧ u * k = ℓ * H₀ ∧ (1 ≤ k → 1 ≤ H₀)
      ∧ (H₀ : ℕ∞) ≤ npHgt φ gT 0 := by
  classical
  letI := instFieldResField hφ
  -- 1. the reduction of `gS`
  have hp : Prime (φ.map (residue O)) := hφ.irred.prime
  have hdmap : gS.map (residue O) ∣ (φ.map (residue O)) ^ μ := by
    rw [← hresT]; exact Polynomial.map_dvd _ hdvd
  obtain ⟨k, hkμ, hassoc⟩ := (dvd_prime_pow hp μ).1 hdmap
  have hresS : gS.map (residue O) = (φ.map (residue O)) ^ k :=
    Polynomial.eq_of_monic_of_associated (hgS.map _) ((hφ.monic.map _).pow _) hassoc
  -- 2. the degree
  have hdegS : gS.natDegree = k * φ.natDegree := by
    rw [Uniformity.Hensel.natDegree_eq_of_map_eq hgS hresS,
      Polynomial.natDegree_pow, hφ.monic.natDegree_map]
  -- 3. purity consequences
  have htop : suppVal φ gS u ℓ ≠ ⊤ := by
    rw [suppVal_of_pure hφ.monic hφ.pos hgS hdegS hpure]; exact ENat.coe_ne_top _
  have hmin0 : sideMin φ gS u ℓ hne = 0 := sideMin_of_pure hpure hne
  have hH₀' : npHgt φ gS 0 = (H₀ : ℕ∞) := by rwa [hmin0] at hH₀
  have hsd : ℓ * sideDeg φ gS u ℓ hne = k :=
    sideDeg_of_pure hφ.monic hφ.pos hgS hdegS hℓ hcop hpure hne
  -- 4. the residual degree
  obtain ⟨c, hc⟩ := hcψ
  have hdegres := (natDegree_resPoly hπ hφ hℓ hcop htop hne hH₀).1
  have hψdeg : ψ.natDegree = sideDeg φ gS u ℓ hne := by
    rw [← hdegres, hc]
    rw [Units.smul_def, Polynomial.smul_eq_C_mul]
    rw [Polynomial.natDegree_C_mul (Units.ne_zero c)]
  have hψpos : 1 ≤ ψ.natDegree := hψi.natDegree_pos
  -- 5. the purity equation `u * k = ℓ * H₀`
  have honside : ℓ • npHgt φ gS 0 + ((u * 0 : ℕ) : ℕ∞) = suppVal φ gS u ℓ := hpure.1
  have hukeq : u * k = ℓ * H₀ := by
    rw [suppVal_of_pure hφ.monic hφ.pos hgS hdegS hpure, hH₀'] at honside
    have : ((ℓ * H₀ : ℕ) : ℕ∞) = ((u * k : ℕ) : ℕ∞) := by
      rw [← honside]
      push_cast
      ring
    exact_mod_cast this.symm
  -- 6. `k ≥ 1 → H₀ ≥ 1`
  have hH1 : 1 ≤ k → 1 ≤ H₀ := by
    intro hk1
    have hdvdφ : (φ.map (residue O)) ∣ gS.map (residue O) := by
      rw [hresS]; exact dvd_pow_self _ (by omega)
    have hle : ((1:ℕ) : ℕ∞) ≤ gaussVal (dev φ gS 0) := by
      refine (le_gaussVal_iff hπ).2 fun i => ?_
      have hz : ((dev φ gS 0).map (residue O)) = 0 := by
        show ((gS %ₘ φ).map (residue O)) = 0
        rw [Polynomial.map_modByMonic _ hφ.monic]
        exact (Polynomial.modByMonic_eq_zero_iff_dvd (hφ.monic.map _)).2 hdvdφ
      have hz0 : (residue O) ((dev φ gS 0).coeff i) = 0 := by
        have := congrArg (fun q => Polynomial.coeff q i) hz
        simpa using this
      have hmem : (dev φ gS 0).coeff i ∈ maximalIdeal O := Ideal.Quotient.eq_zero_iff_mem.1 hz0
      rw [hπ.maximalIdeal_eq, Ideal.mem_span_singleton] at hmem
      simpa using hmem
    have : ((1:ℕ) : ℕ∞) ≤ ((H₀ : ℕ) : ℕ∞) := by rw [← hH₀']; exact hle
    exact_mod_cast this
  -- 7. the height comparison `H₀ ≤ npHgt φ gT 0`
  have hcomp : (H₀ : ℕ∞) ≤ npHgt φ gT 0 := by
    obtain ⟨w, hw⟩ := hdvd
    rw [hw, npHgt_zero_mul hπ hφ, ← hH₀']
    exact le_self_add
  exact ⟨k, hkμ, hdegS, by rw [hψdeg]; exact hsd, hψpos, hukeq, hH1, hcomp⟩

end Uniformity.Density.Leaf
