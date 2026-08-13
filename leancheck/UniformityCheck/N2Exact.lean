/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import UniformityCheck.N2Base
import UniformityCheck.RamCensus

/-!
# UniformityCheck.N2Exact — the exact `n = 2` densities

The verification target: do the `leanfinal` definitions compute the values the corpus predicts?

    genuineDensity O 2 ramType = 1 / (q + 1)          (`ram_density_two`)

for every complete DVR `O` with finite residue field, `q = residueCard O`. The two halves:

* the certified RAM classes at level `2M` number exactly `∑_{i<M} (q-1) q^(2M+2i)`
  (`RamCensus.card_ramSet` + `N2Base.card_iUnion_eq_sum`), and every one of them is RAM-decided
  (`ramSet_subset_decided`);
* conversely a RAM-decided class either carries a RAM certificate or is deeply tangent
  (`decided_ram_subset`, via the `Drainage.lean` dichotomy), and the deep classes number at most
  `q^(3M)` (`DeepSet.card_deepSet_le`).

So the decided count is pinned between the census and the census plus `q^(3M)`, and
`N2Base.genuineDensity_of_census` turns that into `(q-1)/(q²-1) = 1/(q+1)`.

## Status

Sorry-free, axiom-free (Lean core only).
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

namespace UniformityCheck

open Uniformity Uniformity.Density IsLocalRing Filter Topology

section Ram

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [IsAdicComplete (maximalIdeal O) O] [Finite (ResidueField O)] {π : O}

/-- **Every certified RAM class is RAM-decided.** -/
theorem ramSet_subset_decided (hπ : Irreducible π) {j N : ℕ} :
    ramSet π j N ⊆ decidedSet O 2 ramType N := by
  intro c hc a ha
  have hj := ramSet_param_le hπ hc
  obtain ⟨γ, hγ⟩ := hc
  obtain ⟨g, rfl⟩ := Ideal.Quotient.mk_surjective (I := (maximalIdeal O) ^ N) γ
  rw [← ha, ramCert_iff hπ hj] at hγ
  exact typeOf_of_certRam hπ (N := N) ⟨g, j, hj, hγ.1, hγ.2.1, hγ.2.2⟩

/-- **Conversely**: a RAM-decided class carries a RAM certificate unless it is deeply tangent.
(The dichotomy of `Drainage.lean` offers three certificates; the split and inert ones would
force the wrong type.) -/
theorem decided_ram_subset (hπ : Irreducible π) (N : ℕ) :
    decidedSet O 2 ramType N ⊆ {c : Coeff O 2 N | ∃ j, c ∈ ramSet π j N} ∪ deepSet π N := by
  intro c hc
  by_cases hd : c ∈ deepSet π N
  · exact Or.inr hd
  refine Or.inl ?_
  obtain ⟨a, ha⟩ := proj_surjective O 2 N c
  have hty : typeOf (monicPoly a) = ramType := hc a ha
  have hnt : ¬ ∃ γ, Tang π a N γ := fun h => hd ⟨a, ha, h⟩
  rcases cert_of_not_tang hπ a N hnt with h | h | h
  · exfalso
    have hs := typeOf_of_certSplit hπ h
    rw [hty] at hs
    exact splitType_ne_ramType hs.symm
  · obtain ⟨γ, j, hj, h1, h2, h3⟩ := h
    exact ⟨j, Ideal.Quotient.mk _ γ, by rw [← ha, ramCert_iff hπ hj]; exact ⟨h1, h2, h3⟩⟩
  · exfalso
    have hs := typeOf_of_certInert hπ h
    rw [hty] at hs
    exact inertType_ne_ramType hs.symm

/-- The RAM census, summed: the certified classes at level `2M` number
`∑_{i<M} (q-1) q^(2M+2i)`. -/
theorem card_ramBig (hπ : Irreducible π) (M : ℕ) :
    (Nat.card {c : Coeff O 2 (2 * M) | ∃ j, c ∈ ramSet π j (2 * M)} : ℝ)
      = ∑ i ∈ Finset.range M,
          ((residueCard O - 1 : ℕ) : ℝ) * (residueCard O : ℝ) ^ (2 * M + 2 * i) := by
  classical
  rw [card_iUnion_eq_sum M (fun j => ramSet π j (2 * M))
    (fun j hj => ramSet_eq_empty hπ (by omega))
    (fun _ _ _ hx hx' => ramSet_param_unique hπ hx hx')]
  push_cast
  rw [← Finset.sum_range_reflect (fun i => (Nat.card (ramSet π i (2 * M)) : ℝ)) M]
  refine Finset.sum_congr rfl (fun i hi => ?_)
  have hi' : i < M := Finset.mem_range.1 hi
  have h := card_ramSet (O := O) hπ (M - 1 - i) (2 * i)
  rw [show 2 * (M - 1 - i) + 2 + 2 * i = 2 * M from by omega,
    show 2 * (M - 1 - i) + 2 * (2 * i) + 2 = 2 * M + 2 * i from by omega,
    show 2 * (M - 1 - i) + 2 * (2 * i) + 3 = 2 * M + 2 * i + 1 from by omega] at h
  have hc : (Nat.card (ramSet π (M - 1 - i) (2 * M)) : ℝ) + (residueCard O : ℝ) ^ (2 * M + 2 * i)
      = (residueCard O : ℝ) ^ (2 * M + 2 * i + 1) := by exact_mod_cast congrArg (fun n : ℕ => (n : ℝ)) h
  rw [pow_succ] at hc
  have hcast : ((residueCard O - 1 : ℕ) : ℝ) = (residueCard O : ℝ) - 1 := by
    have h1 : (1 : ℕ) ≤ residueCard O := residueCard_pos O
    push_cast [h1]
    ring
  rw [hcast]
  linarith

/-- **TARGET 1 — THE EXACT RAMIFIED DENSITY.** For every complete discrete valuation ring `O`
with finite residue field of cardinality `q` (residue characteristic 2 included), the genuine
density of the monic quadratics with a totally ramified factorization is exactly `1/(q+1)`. -/
theorem ram_density_two (O : Type*) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [IsAdicComplete (maximalIdeal O) O] [Finite (ResidueField O)] :
    genuineDensity O 2 ramType = 1 / ((residueCard O : ℝ) + 1) := by
  classical
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible O
  have hB : ∀ M : ℕ, {c : Coeff O 2 (2 * M) | ∃ j, c ∈ ramSet π j (2 * M)}
      ⊆ decidedSet O 2 ramType (2 * M) := by
    rintro M c ⟨j, hj⟩
    exact ramSet_subset_decided hπ hj
  have hlow : ∀ M : ℕ, (∑ i ∈ Finset.range M,
        ((residueCard O - 1 : ℕ) : ℝ) * (residueCard O : ℝ) ^ (2 * M + 2 * i))
      ≤ (decidedCount O 2 ramType (2 * M) : ℝ) := by
    intro M
    rw [← card_ramBig hπ M]
    exact_mod_cast (count_bounds_of_subsets _ (deepSet π (2 * M)) (hB M)
      (decided_ram_subset hπ (2 * M))).1
  have hhigh : ∀ M : ℕ, (decidedCount O 2 ramType (2 * M) : ℝ)
      ≤ (∑ i ∈ Finset.range M,
          ((residueCard O - 1 : ℕ) : ℝ) * (residueCard O : ℝ) ^ (2 * M + 2 * i))
        + (residueCard O : ℝ) ^ (3 * M) := by
    intro M
    rw [← card_ramBig hπ M]
    have h2 := (count_bounds_of_subsets _ (deepSet π (2 * M)) (hB M)
      (decided_ram_subset hπ (2 * M))).2
    have h3 : (Nat.card (deepSet π (2 * M)) : ℝ) ≤ (residueCard O : ℝ) ^ (3 * M) := by
      exact_mod_cast card_deepSet_le hπ M
    calc (decidedCount O 2 ramType (2 * M) : ℝ)
        ≤ (Nat.card {c : Coeff O 2 (2 * M) | ∃ j, c ∈ ramSet π j (2 * M)} : ℝ)
            + (Nat.card (deepSet π (2 * M)) : ℝ) := by exact_mod_cast h2
      _ ≤ _ := by linarith
  have hres := genuineDensity_of_census (O := O) (σ := ramType) (c := residueCard O - 1)
    hlow hhigh
  rw [hres]
  have hcast : ((residueCard O - 1 : ℕ) : ℝ) = (residueCard O : ℝ) - 1 := by
    have h1 : (1 : ℕ) ≤ residueCard O := residueCard_pos O
    push_cast [h1]
    ring
  have hq : (2 : ℝ) ≤ (residueCard O : ℝ) := by exact_mod_cast two_le_residueCard O
  rw [hcast]
  have h1 : (residueCard O : ℝ) + 1 ≠ 0 := by linarith
  have h2 : (residueCard O : ℝ) ^ 2 - 1 ≠ 0 := by nlinarith
  field_simp
  ring

end Ram

end UniformityCheck

section AxCheck

#print axioms UniformityCheck.ram_density_two

end AxCheck
