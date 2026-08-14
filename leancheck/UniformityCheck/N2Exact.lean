/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import UniformityCheck.N2Base
import UniformityCheck.RamCensus
import UniformityCheck.InertCensus

/-!
# UniformityCheck.N2Exact — the exact `n = 2` densities

The verification target: do the `leanfinal` definitions compute the values the corpus predicts?

    genuineDensity O 2 ramType = 1 / (q + 1)          (`ram_density_two`)

for every complete DVR `O` with finite residue field, `q = residueCard O`.

**Which density.** The census machinery below counts DECIDED classes, so it proves the value
for `decidedDensity` first (`ram_decidedDensity_two` and friends). At `n = 2` the tie
`genuineDensity_eq_decidedDensity_two` (unconditional, via `leanfinal`'s `drainage_two`) then
carries every value verbatim to THE density `genuineDensity` — the limit of the proportion of
coefficient classes consistent with the type. §4 does that transfer; the unsuffixed names are
the headline statements over THE density, the `_decidedDensity_` ones are the census route.

The two halves of the census:

* the certified RAM classes at level `2M` number exactly `∑_{i<M} (q-1) q^(2M+2i)`
  (`RamCensus.card_ramSet` + `N2Base.card_iUnion_eq_sum`), and every one of them is RAM-decided
  (`ramSet_subset_decided`);
* conversely a RAM-decided class either carries a RAM certificate or is deeply tangent
  (`decided_ram_subset`, via the `Drainage.lean` dichotomy), and the deep classes number at most
  `q^(3M)` (`DeepSet.card_deepSet_le`).

So the decided count is pinned between the census and the census plus `q^(3M)`, and
`N2Base.decidedDensity_of_census` turns that into `(q-1)/(q²-1) = 1/(q+1)`.

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
          ((residueCard O : ℝ) - 1) * (residueCard O : ℝ) ^ (2 * M + 2 * i) := by
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
  linarith

/-- **TARGET 1 — THE EXACT RAMIFIED DENSITY.** For every complete discrete valuation ring `O`
with finite residue field of cardinality `q` (residue characteristic 2 included), the genuine
density of the monic quadratics with a totally ramified factorization is exactly `1/(q+1)`. -/
theorem ram_decidedDensity_two (O : Type*) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [IsAdicComplete (maximalIdeal O) O] [Finite (ResidueField O)] :
    decidedDensity O 2 ramType = 1 / ((residueCard O : ℝ) + 1) := by
  classical
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible O
  have hB : ∀ M : ℕ, {c : Coeff O 2 (2 * M) | ∃ j, c ∈ ramSet π j (2 * M)}
      ⊆ decidedSet O 2 ramType (2 * M) := by
    rintro M c ⟨j, hj⟩
    exact ramSet_subset_decided hπ hj
  have hlow : ∀ M : ℕ, (∑ i ∈ Finset.range M,
        ((residueCard O : ℝ) - 1) * (residueCard O : ℝ) ^ (2 * M + 2 * i))
      ≤ (decidedCount O 2 ramType (2 * M) : ℝ) := by
    intro M
    rw [← card_ramBig hπ M]
    exact_mod_cast (count_bounds_of_subsets _ (deepSet π (2 * M)) (hB M)
      (decided_ram_subset hπ (2 * M))).1
  have hhigh : ∀ M : ℕ, (decidedCount O 2 ramType (2 * M) : ℝ)
      ≤ (∑ i ∈ Finset.range M,
          ((residueCard O : ℝ) - 1) * (residueCard O : ℝ) ^ (2 * M + 2 * i))
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
  have hres := decidedDensity_of_census (O := O) (σ := ramType) ((residueCard O : ℝ) - 1)
    hlow hhigh
  rw [hres]
  have hq : (2 : ℝ) ≤ (residueCard O : ℝ) := by exact_mod_cast two_le_residueCard O
  have h1 : (residueCard O : ℝ) + 1 ≠ 0 := by linarith
  have h2 : (residueCard O : ℝ) ^ 2 - 1 ≠ 0 := by nlinarith
  field_simp
  ring

end Ram

/-! ## 2. The inert density -/

section Inert

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [IsAdicComplete (maximalIdeal O) O] [Finite (ResidueField O)] {π : O}

/-- **Every certified INERT class is INERT-decided.** -/
theorem inertSet_subset_decided (hπ : Irreducible π) {k N : ℕ} :
    inertSet π k N ⊆ decidedSet O 2 inertType N := by
  intro c hc a ha
  have hk := inertSet_param_le hc
  obtain ⟨γ, hγ⟩ := hc
  obtain ⟨g, rfl⟩ := Ideal.Quotient.mk_surjective (I := (maximalIdeal O) ^ N) γ
  rw [← ha, inertCert_iff hπ hk] at hγ
  obtain ⟨b₀, b₁, hv, hd, han⟩ := hγ
  exact typeOf_of_certInert hπ (N := N) ⟨g, k, b₀, b₁, hk, hv, hd, han⟩

/-- **Conversely**: an INERT-decided class carries an INERT certificate unless it is deeply
tangent. -/
theorem decided_inert_subset (hπ : Irreducible π) (N : ℕ) :
    decidedSet O 2 inertType N ⊆ {c : Coeff O 2 N | ∃ k, c ∈ inertSet π k N} ∪ deepSet π N := by
  intro c hc
  by_cases hd : c ∈ deepSet π N
  · exact Or.inr hd
  refine Or.inl ?_
  obtain ⟨a, ha⟩ := proj_surjective O 2 N c
  have hty : typeOf (monicPoly a) = inertType := hc a ha
  have hnt : ¬ ∃ γ, Tang π a N γ := fun h => hd ⟨a, ha, h⟩
  rcases cert_of_not_tang hπ a N hnt with h | h | h
  · exfalso
    have hs := typeOf_of_certSplit hπ h
    rw [hty] at hs
    exact splitType_ne_inertType hs.symm
  · exfalso
    have hs := typeOf_of_certRam hπ h
    rw [hty] at hs
    exact inertType_ne_ramType hs
  · obtain ⟨γ, k, b₀, b₁, hk, h1, h2, h3⟩ := h
    exact ⟨k, Ideal.Quotient.mk _ γ,
      by rw [← ha, inertCert_iff hπ hk]; exact ⟨b₀, b₁, h1, h2, h3⟩⟩

/-- The INERT census, summed. -/
theorem card_inertBig (hπ : Irreducible π) (M : ℕ) :
    (Nat.card {c : Coeff O 2 (2 * M) | ∃ k, c ∈ inertSet π k (2 * M)} : ℝ)
      = ∑ i ∈ Finset.range M,
          (((residueCard O : ℝ) ^ 2 - (residueCard O : ℝ)) / 2)
            * (residueCard O : ℝ) ^ (2 * M + 2 * i) := by
  classical
  rw [card_iUnion_eq_sum M (fun k => inertSet π k (2 * M))
    (fun k hk => inertSet_eq_empty π (by omega))
    (fun _ _ _ hx hx' => inertSet_param_unique hπ hx hx')]
  push_cast
  rw [← Finset.sum_range_reflect (fun i => (Nat.card (inertSet π i (2 * M)) : ℝ)) M]
  refine Finset.sum_congr rfl (fun i hi => ?_)
  have hi' : i < M := Finset.mem_range.1 hi
  have h := card_inertSet (O := O) hπ (M - 1 - i) (2 * i + 1)
  rw [show 2 * (M - 1 - i) + 1 + (2 * i + 1) = 2 * M from by omega,
    show 2 * (M - 1 - i) + 2 * (2 * i + 1) + 1 = 2 * M + 2 * i + 1 from by omega,
    show 2 * (M - 1 - i) + 2 * (2 * i + 1) + 2 = 2 * M + 2 * i + 2 from by omega] at h
  have hc : 2 * (Nat.card (inertSet π (M - 1 - i) (2 * M)) : ℝ)
      + (residueCard O : ℝ) ^ (2 * M + 2 * i + 1)
      = (residueCard O : ℝ) ^ (2 * M + 2 * i + 2) := by
    exact_mod_cast congrArg (fun n : ℕ => (n : ℝ)) h
  have hq1 : (residueCard O : ℝ) ^ (2 * M + 2 * i + 1)
      = (residueCard O : ℝ) ^ (2 * M + 2 * i) * (residueCard O : ℝ) := by rw [pow_succ]
  have hq2 : (residueCard O : ℝ) ^ (2 * M + 2 * i + 2)
      = (residueCard O : ℝ) ^ (2 * M + 2 * i) * (residueCard O : ℝ) * (residueCard O : ℝ) := by
    rw [pow_succ, pow_succ]
  rw [hq1, hq2] at hc
  linarith

/-- **THE EXACT INERT DENSITY.** `q / (2(q+1))`, for every complete DVR with finite residue
field — the anisotropic residual census is uniform in the residue characteristic. -/
theorem inert_decidedDensity_two (O : Type*) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [IsAdicComplete (maximalIdeal O) O] [Finite (ResidueField O)] :
    decidedDensity O 2 inertType = (residueCard O : ℝ) / (2 * ((residueCard O : ℝ) + 1)) := by
  classical
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible O
  have hB : ∀ M : ℕ, {c : Coeff O 2 (2 * M) | ∃ k, c ∈ inertSet π k (2 * M)}
      ⊆ decidedSet O 2 inertType (2 * M) := by
    rintro M c ⟨k, hk⟩
    exact inertSet_subset_decided hπ hk
  have hlow : ∀ M : ℕ, (∑ i ∈ Finset.range M,
        (((residueCard O : ℝ) ^ 2 - (residueCard O : ℝ)) / 2)
          * (residueCard O : ℝ) ^ (2 * M + 2 * i))
      ≤ (decidedCount O 2 inertType (2 * M) : ℝ) := by
    intro M
    rw [← card_inertBig hπ M]
    exact_mod_cast (count_bounds_of_subsets _ (deepSet π (2 * M)) (hB M)
      (decided_inert_subset hπ (2 * M))).1
  have hhigh : ∀ M : ℕ, (decidedCount O 2 inertType (2 * M) : ℝ)
      ≤ (∑ i ∈ Finset.range M,
          (((residueCard O : ℝ) ^ 2 - (residueCard O : ℝ)) / 2)
            * (residueCard O : ℝ) ^ (2 * M + 2 * i))
        + (residueCard O : ℝ) ^ (3 * M) := by
    intro M
    rw [← card_inertBig hπ M]
    have h2 := (count_bounds_of_subsets _ (deepSet π (2 * M)) (hB M)
      (decided_inert_subset hπ (2 * M))).2
    have h3 : (Nat.card (deepSet π (2 * M)) : ℝ) ≤ (residueCard O : ℝ) ^ (3 * M) := by
      exact_mod_cast card_deepSet_le hπ M
    calc (decidedCount O 2 inertType (2 * M) : ℝ)
        ≤ (Nat.card {c : Coeff O 2 (2 * M) | ∃ k, c ∈ inertSet π k (2 * M)} : ℝ)
            + (Nat.card (deepSet π (2 * M)) : ℝ) := by exact_mod_cast h2
      _ ≤ _ := by linarith
  have hres := decidedDensity_of_census (O := O) (σ := inertType)
    (((residueCard O : ℝ) ^ 2 - (residueCard O : ℝ)) / 2) hlow hhigh
  rw [hres]
  have hq : (2 : ℝ) ≤ (residueCard O : ℝ) := by exact_mod_cast two_le_residueCard O
  have h1 : (residueCard O : ℝ) + 1 ≠ 0 := by linarith
  have h2 : (residueCard O : ℝ) ^ 2 - 1 ≠ 0 := by nlinarith
  field_simp
  ring

end Inert

/-! ## 3. The payoff: all three exact values, and the split/inert symmetry -/

section Payoff

variable (O : Type*) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [IsAdicComplete (maximalIdeal O) O] [Finite (ResidueField O)]

/-- **THE EXACT SPLIT DENSITY**, by subtraction from the landed
`sum_three_decidedDensities_eq_one`. -/
theorem split_decidedDensity_two :
    decidedDensity O 2 splitType = (residueCard O : ℝ) / (2 * ((residueCard O : ℝ) + 1)) := by
  have hsum := sum_three_decidedDensities_eq_one (O := O)
  rw [inert_decidedDensity_two O, ram_decidedDensity_two O] at hsum
  have hq : (2 : ℝ) ≤ (residueCard O : ℝ) := by exact_mod_cast two_le_residueCard O
  have h1 : (residueCard O : ℝ) + 1 ≠ 0 := by linarith
  field_simp at hsum ⊢
  linarith

/-- **TARGET 2 — THE SPLIT/INERT SYMMETRY.** Equal densities, for every complete DVR with finite
residue field. Proved not by a coefficient involution (there is none uniform in the residue
characteristic) but by evaluating both sides exactly. -/
theorem split_eq_inert_decidedDensity_two :
    decidedDensity O 2 splitType = decidedDensity O 2 inertType := by
  rw [split_decidedDensity_two, inert_decidedDensity_two]

/-- **The whole `n = 2` density function, exactly.** -/
theorem decidedDensity_two_exact :
    decidedDensity O 2 splitType = (residueCard O : ℝ) / (2 * ((residueCard O : ℝ) + 1))
    ∧ decidedDensity O 2 inertType = (residueCard O : ℝ) / (2 * ((residueCard O : ℝ) + 1))
    ∧ decidedDensity O 2 ramType = 1 / ((residueCard O : ℝ) + 1)
    ∧ ∀ σ : FactorizationType, σ ≠ splitType → σ ≠ inertType → σ ≠ ramType →
        decidedDensity O 2 σ = 0 :=
  ⟨split_decidedDensity_two O, inert_decidedDensity_two O, ram_decidedDensity_two O,
    fun _ hs hi hr => decidedDensity_two_eq_zero hs hi hr⟩

end Payoff

/-! ## 4. The concrete instances (the numbers the corpus predicts) -/

section Padic

/-- **`q = 2`, the wild prime.** All three degree-2 densities over `ℤ_[2]` are exactly `1/3` —
the W-11 values, and inside `leanfinal`'s certified brackets `gate_bracket_padic_two_decided`
(`[1/4, 11/16]` for split and inert, `[1/16, 1/2]` for ram). -/
theorem decidedDensity_two_padic_two :
    decidedDensity ℤ_[2] 2 splitType = 1 / 3
    ∧ decidedDensity ℤ_[2] 2 inertType = 1 / 3
    ∧ decidedDensity ℤ_[2] 2 ramType = 1 / 3 := by
  refine ⟨?_, ?_, ?_⟩
  · rw [split_decidedDensity_two, residueCard_padicInt 2]; norm_num
  · rw [inert_decidedDensity_two, residueCard_padicInt 2]; norm_num
  · rw [ram_decidedDensity_two, residueCard_padicInt 2]; norm_num

/-- **`q = 3`, tame.** `split = inert = 3/8`, `ram = 1/4` — the W-11 values, inside
`gate_bracket_padic_three_decided`. -/
theorem decidedDensity_two_padic_three :
    decidedDensity ℤ_[3] 2 splitType = 3 / 8
    ∧ decidedDensity ℤ_[3] 2 inertType = 3 / 8
    ∧ decidedDensity ℤ_[3] 2 ramType = 1 / 4 := by
  refine ⟨?_, ?_, ?_⟩
  · rw [split_decidedDensity_two, residueCard_padicInt 3]; norm_num
  · rw [inert_decidedDensity_two, residueCard_padicInt 3]; norm_num
  · rw [ram_decidedDensity_two, residueCard_padicInt 3]; norm_num

end Padic

/-! ## 5. THE HEADLINE VALUES, over THE density `genuineDensity`

The census above certifies decided classes, so it lands on `decidedDensity`. `leanfinal`'s
`genuineDensity_eq_decidedDensity_two` — unconditional at `n = 2`, since `drainage_two` is a
theorem — transfers every value to THE density, the limit of the proportion of coefficient
classes consistent with the type. The numbers do not move; the object they describe does. -/

section Genuine

variable (O : Type*) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [IsAdicComplete (maximalIdeal O) O] [Finite (ResidueField O)]

/-- **THE EXACT RAMIFIED DENSITY.** `genuineDensity O 2 ramType = 1/(q+1)`, every `O`. -/
theorem ram_density_two : genuineDensity O 2 ramType = 1 / ((residueCard O : ℝ) + 1) := by
  rw [genuineDensity_eq_decidedDensity_two]; exact ram_decidedDensity_two O

/-- **THE EXACT INERT DENSITY.** `genuineDensity O 2 inertType = q/(2(q+1))`, every `O`. -/
theorem inert_density_two :
    genuineDensity O 2 inertType = (residueCard O : ℝ) / (2 * ((residueCard O : ℝ) + 1)) := by
  rw [genuineDensity_eq_decidedDensity_two]; exact inert_decidedDensity_two O

/-- **THE EXACT SPLIT DENSITY.** `genuineDensity O 2 splitType = q/(2(q+1))`, every `O`. -/
theorem split_density_two :
    genuineDensity O 2 splitType = (residueCard O : ℝ) / (2 * ((residueCard O : ℝ) + 1)) := by
  rw [genuineDensity_eq_decidedDensity_two]; exact split_decidedDensity_two O

/-- **TARGET 2 — THE SPLIT/INERT SYMMETRY**, over THE density. -/
theorem split_eq_inert_two : genuineDensity O 2 splitType = genuineDensity O 2 inertType := by
  rw [split_density_two, inert_density_two]

/-- **The whole `n = 2` density function, exactly, over THE density.** Together with
`leanfinal`'s `sum_three_densities_eq_one` this is the complete degree-2 answer: three values
summing to `1`, everything else `0`. -/
theorem density_two_exact :
    genuineDensity O 2 splitType = (residueCard O : ℝ) / (2 * ((residueCard O : ℝ) + 1))
    ∧ genuineDensity O 2 inertType = (residueCard O : ℝ) / (2 * ((residueCard O : ℝ) + 1))
    ∧ genuineDensity O 2 ramType = 1 / ((residueCard O : ℝ) + 1)
    ∧ ∀ σ : FactorizationType, σ ≠ splitType → σ ≠ inertType → σ ≠ ramType →
        genuineDensity O 2 σ = 0 :=
  ⟨split_density_two O, inert_density_two O, ram_density_two O,
    fun _ hs hi hr => genuineDensity_two_eq_zero hs hi hr⟩

end Genuine

/-- **`q = 2`, the wild prime, over THE density.** All three degree-2 densities over `ℤ_[2]` are
exactly `1/3` — the W-11 values, inside `leanfinal`'s certified brackets
`gate_bracket_padic_two` (`[1/4, 11/16]` for split and inert, `[1/16, 1/2]` for ram). -/
theorem density_two_padic_two :
    genuineDensity ℤ_[2] 2 splitType = 1 / 3
    ∧ genuineDensity ℤ_[2] 2 inertType = 1 / 3
    ∧ genuineDensity ℤ_[2] 2 ramType = 1 / 3 := by
  simpa only [genuineDensity_eq_decidedDensity_two] using decidedDensity_two_padic_two

/-- **`q = 3`, tame, over THE density.** `split = inert = 3/8`, `ram = 1/4` — the W-11 values,
inside `gate_bracket_padic_three`. -/
theorem density_two_padic_three :
    genuineDensity ℤ_[3] 2 splitType = 3 / 8
    ∧ genuineDensity ℤ_[3] 2 inertType = 3 / 8
    ∧ genuineDensity ℤ_[3] 2 ramType = 1 / 4 := by
  simpa only [genuineDensity_eq_decidedDensity_two] using decidedDensity_two_padic_three

end UniformityCheck

section AxCheck

#print axioms UniformityCheck.ram_decidedDensity_two
#print axioms UniformityCheck.inert_decidedDensity_two
#print axioms UniformityCheck.split_decidedDensity_two
#print axioms UniformityCheck.split_eq_inert_decidedDensity_two
#print axioms UniformityCheck.decidedDensity_two_exact
#print axioms UniformityCheck.decidedDensity_two_padic_two
#print axioms UniformityCheck.decidedDensity_two_padic_three
-- unit UNIFORMITY-P4 (2026-08-13): the same values over THE density
#print axioms UniformityCheck.ram_density_two
#print axioms UniformityCheck.inert_density_two
#print axioms UniformityCheck.split_density_two
#print axioms UniformityCheck.split_eq_inert_two
#print axioms UniformityCheck.density_two_exact
#print axioms UniformityCheck.density_two_padic_two
#print axioms UniformityCheck.density_two_padic_three

end AxCheck
