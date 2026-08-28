import Uniformity.ChapB.B82
import Uniformity.ChapB.B80

namespace Uniformity.Density.Leaf
open Polynomial IsLocalRing

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {π : O}

-- the reduction of a monic divisor of `φ̄ ^ μ` is `φ̄ ^ k`
example (hπ : Irreducible π) {φ : Polynomial O} (hφ : IsKey φ)
    {gT : Polynomial O} (hgT : gT.Monic) {μ : ℕ}
    (hresT : gT.map (residue O) = (φ.map (residue O)) ^ μ)
    {gS : Polynomial O} (hgS : gS.Monic) (hdvd : gS ∣ gT) :
    ∃ k ≤ μ, gS.map (residue O) = (φ.map (residue O)) ^ k := by
  have hp : Prime (φ.map (residue O)) := hφ.irred.prime
  have hd : gS.map (residue O) ∣ (φ.map (residue O)) ^ μ := by
    rw [← hresT]; exact Polynomial.map_dvd _ hdvd
  obtain ⟨k, hk, hassoc⟩ := (dvd_prime_pow hp μ).1 hd
  refine ⟨k, hk, ?_⟩
  exact Polynomial.eq_of_monic_of_associated (hgS.map _) ((hφ.monic.map _).pow _) hassoc

-- π ∣ dev φ gS 0 when φ̄ ∣ ḡS
example (hπ : Irreducible π) {φ : Polynomial O} (hφ : IsKey φ)
    {gS : Polynomial O} (hdvd : (φ.map (residue O)) ∣ gS.map (residue O)) :
    (1 : ℕ∞) ≤ npHgt φ gS 0 := by
  have : ((1:ℕ) : ℕ∞) ≤ gaussVal (dev φ gS 0) := by
    refine (le_gaussVal_iff hπ).2 fun i => ?_
    have hz : ((dev φ gS 0).map (residue O)) = 0 := by
      show ((gS %ₘ φ).map (residue O)) = 0
      rw [Polynomial.map_modByMonic _ hφ.monic]
      exact (Polynomial.modByMonic_eq_zero_iff_dvd (hφ.monic.map _)).2 hdvd
    have : (residue O) ((dev φ gS 0).coeff i) = 0 := by
      have := congrArg (fun q => Polynomial.coeff q i) hz
      simpa using this
    have hmem : (dev φ gS 0).coeff i ∈ maximalIdeal O := Ideal.Quotient.eq_zero_iff_mem.1 this
    rw [hπ.maximalIdeal_eq, Ideal.mem_span_singleton] at hmem
    simpa using hmem
  simpa [npHgt] using this

end Uniformity.Density.Leaf
