/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import UniformityCheck.Counting
import UniformityCheck.DeepSet

/-!
# UniformityCheck.N2Base — from a per-parameter census to an exact density

Two type-agnostic tools:

* `card_iUnion_eq_sum` — a family of pairwise-disjoint sets, empty past `M`, has
  `#⋃ = ∑_{i < M} #Fᵢ`;
* **`genuineDensity_of_census`** — if the level-`2M` decided count of `σ` is sandwiched between
  `∑_{i < M} c·q^(2M+2i)` and that plus `q^(3M)` (the deep-class bound of `DeepSet.lean`), then

      genuineDensity O 2 σ = c / (q² - 1).

  The geometric sum contributes `c·q^(2M)(q^(2M)-1)/(q²-1)`, so the normalised count is
  `(c/(q²-1))·(1 - q^(-2M))`, and the slack `q^(3M)/q^(4M) = q^(-M)` drains.

At `c = q - 1` this reads `1/(q+1)` (the RAM value) and at `c = (q²-q)/2` it reads `q/(2(q+1))`
(the INERT value).

## Status

Sorry-free, axiom-free (Lean core only).
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

namespace UniformityCheck

open Uniformity Uniformity.Density IsLocalRing Filter Topology

/-! ## 1. Counting a disjoint family -/

section Union

variable {α : Type*} [Finite α]

/-- A pairwise-disjoint family of sets, empty from `M` on, has union of cardinality
`∑_{i < M} #Fᵢ`. -/
theorem card_iUnion_eq_sum (M : ℕ) (F : ℕ → Set α)
    (hempty : ∀ j, M ≤ j → F j = ∅)
    (hdisj : ∀ (j j' : ℕ) (x : α), x ∈ F j → x ∈ F j' → j = j') :
    Nat.card {x : α | ∃ j, x ∈ F j} = ∑ i ∈ Finset.range M, Nat.card (F i) := by
  classical
  have hbij : Function.Bijective
      (fun p : (Σ i : Fin M, (F (i : ℕ) : Set α)) =>
        (⟨(p.2 : α), ⟨(p.1 : ℕ), p.2.2⟩⟩ : {x : α | ∃ j, x ∈ F j})) := by
    constructor
    · rintro ⟨i, x⟩ ⟨i', x'⟩ h
      have hxx : (x : α) = (x' : α) := congrArg Subtype.val h
      have hmem : (x : α) ∈ F (i' : ℕ) := by rw [hxx]; exact x'.2
      have hii : i = i' := Fin.ext (hdisj _ _ _ x.2 hmem)
      subst hii
      simp only [Sigma.mk.injEq, heq_eq_eq, true_and]
      exact Subtype.ext hxx
    · rintro ⟨x, j, hj⟩
      have hjM : j < M := by
        by_contra hc
        rw [hempty j (by omega)] at hj
        exact hj
      exact ⟨⟨⟨j, hjM⟩, ⟨x, hj⟩⟩, rfl⟩
  rw [← Nat.card_eq_of_bijective _ hbij, Nat.card_sigma,
    Fin.sum_univ_eq_sum_range (fun i => Nat.card (F i)) M]

end Union

/-! ## 2. From a census to a density -/

section Density

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)]

/-- The geometric sum of a census family, in closed form. -/
theorem census_sum (c : ℝ) (M : ℕ) :
    (∑ i ∈ Finset.range M, c * (residueCard O : ℝ) ^ (2 * M + 2 * i))
      = (c / ((residueCard O : ℝ) ^ 2 - 1))
          * ((residueCard O : ℝ) ^ (4 * M) - (residueCard O : ℝ) ^ (2 * M)) := by
  have hq : (1 : ℝ) < (residueCard O : ℝ) := by exact_mod_cast one_lt_residueCard O
  have hq0 : (0 : ℝ) < (residueCard O : ℝ) := by linarith
  have hne : ((residueCard O : ℝ) ^ 2 - 1) ≠ 0 := by nlinarith
  have h1 : ∑ i ∈ Finset.range M, c * (residueCard O : ℝ) ^ (2 * M + 2 * i)
      = c * (residueCard O : ℝ) ^ (2 * M)
          * ∑ i ∈ Finset.range M, ((residueCard O : ℝ) ^ 2) ^ i := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [pow_add, ← pow_mul]
    ring
  rw [h1, geom_sum_eq (by nlinarith) M, ← pow_mul,
    show 4 * M = 2 * M + 2 * M from by omega, pow_add]
  field_simp

/-- Sandwiching the decided count between a certified family `B` and the slack `D`. -/
theorem count_bounds_of_subsets {σ : FactorizationType} {N : ℕ} (B D : Set (Coeff O 2 N))
    (hsub : B ⊆ decidedSet O 2 σ N) (hsup : decidedSet O 2 σ N ⊆ B ∪ D) :
    Nat.card B ≤ decidedCount O 2 σ N ∧ decidedCount O 2 σ N ≤ Nat.card B + Nat.card D := by
  classical
  refine ⟨Nat.card_le_card_of_injective (Set.inclusion hsub) (Set.inclusion_injective _), ?_⟩
  have h1 : decidedCount O 2 σ N ≤ Nat.card ((B ∪ D : Set (Coeff O 2 N))) :=
    Nat.card_le_card_of_injective (Set.inclusion hsup) (Set.inclusion_injective _)
  have h2 : Nat.card ((B ∪ D : Set (Coeff O 2 N))) ≤ Nat.card B + Nat.card D := by
    rw [Nat.card_coe_set_eq, Nat.card_coe_set_eq, Nat.card_coe_set_eq]
    exact Set.ncard_union_le _ _
  exact h1.trans h2

/-- **THE CENSUS ⟹ DENSITY BRIDGE.** -/
theorem genuineDensity_of_census {σ : FactorizationType} (c : ℝ)
    (hlow : ∀ M : ℕ, (∑ i ∈ Finset.range M, c * (residueCard O : ℝ) ^ (2 * M + 2 * i))
      ≤ (decidedCount O 2 σ (2 * M) : ℝ))
    (hhigh : ∀ M : ℕ, (decidedCount O 2 σ (2 * M) : ℝ)
      ≤ (∑ i ∈ Finset.range M, c * (residueCard O : ℝ) ^ (2 * M + 2 * i))
          + (residueCard O : ℝ) ^ (3 * M)) :
    genuineDensity O 2 σ = c / ((residueCard O : ℝ) ^ 2 - 1) := by
  have hq : (1 : ℝ) < (residueCard O : ℝ) := by exact_mod_cast one_lt_residueCard O
  have hq0 : (0 : ℝ) < (residueCard O : ℝ) := by linarith
  set q : ℝ := (residueCard O : ℝ) with hqdef
  set L : ℝ := c / (q ^ 2 - 1) with hL
  -- the normalised sandwich
  have hseq : ∀ M : ℕ, decidedSeq O 2 σ (2 * M) = (decidedCount O 2 σ (2 * M) : ℝ) / q ^ (4 * M) := by
    intro M
    rw [decidedSeq, show 2 * (2 * M) = 4 * M from by ring]
  have hpow : ∀ M : ℕ, (0 : ℝ) < q ^ (4 * M) := fun M => pow_pos hq0 _
  have e1 : ∀ M : ℕ, ((q ^ 2)⁻¹) ^ M * q ^ (4 * M) = q ^ (2 * M) := by
    intro M
    rw [inv_pow, ← pow_mul, show 4 * M = 2 * M + 2 * M from by omega, pow_add, ← mul_assoc,
      inv_mul_cancel₀ (by positivity), one_mul]
  have e2 : ∀ M : ℕ, (q⁻¹) ^ M * q ^ (4 * M) = q ^ (3 * M) := by
    intro M
    rw [inv_pow, show 4 * M = M + 3 * M from by omega, pow_add, ← mul_assoc,
      inv_mul_cancel₀ (by positivity), one_mul]
  have hlo : ∀ M : ℕ, L - L * ((q ^ 2)⁻¹) ^ M ≤ decidedSeq O 2 σ (2 * M) := by
    intro M
    rw [hseq M, le_div_iff₀ (hpow M)]
    have h := (census_sum (O := O) c M).symm.trans_le (hlow M)
    have hid : (L - L * ((q ^ 2)⁻¹) ^ M) * q ^ (4 * M) = L * (q ^ (4 * M) - q ^ (2 * M)) := by
      calc (L - L * ((q ^ 2)⁻¹) ^ M) * q ^ (4 * M)
          = L * q ^ (4 * M) - L * (((q ^ 2)⁻¹) ^ M * q ^ (4 * M)) := by ring
        _ = L * (q ^ (4 * M) - q ^ (2 * M)) := by rw [e1 M]; ring
    rw [hid]
    exact h
  have hhi : ∀ M : ℕ, decidedSeq O 2 σ (2 * M) ≤ L - L * ((q ^ 2)⁻¹) ^ M + (q⁻¹) ^ M := by
    intro M
    rw [hseq M, div_le_iff₀ (hpow M)]
    have h := (hhigh M).trans_eq (by rw [census_sum (O := O) c M])
    have hid : (L - L * ((q ^ 2)⁻¹) ^ M + (q⁻¹) ^ M) * q ^ (4 * M)
        = L * (q ^ (4 * M) - q ^ (2 * M)) + q ^ (3 * M) := by
      calc (L - L * ((q ^ 2)⁻¹) ^ M + (q⁻¹) ^ M) * q ^ (4 * M)
          = L * q ^ (4 * M) - L * (((q ^ 2)⁻¹) ^ M * q ^ (4 * M))
              + ((q⁻¹) ^ M * q ^ (4 * M)) := by ring
        _ = L * (q ^ (4 * M) - q ^ (2 * M)) + q ^ (3 * M) := by rw [e1 M, e2 M]; ring
    rw [hid]
    exact h
  -- both bounds converge to `L`
  have hz2 : Tendsto (fun M : ℕ => ((q ^ 2)⁻¹) ^ M) atTop (𝓝 0) := by
    refine tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity) ?_
    rw [inv_lt_one₀ (by positivity)]
    nlinarith
  have hz1 : Tendsto (fun M : ℕ => (q⁻¹) ^ M) atTop (𝓝 0) := by
    refine tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity) ?_
    rw [inv_lt_one₀ (by positivity)]
    exact hq
  have hlolim : Tendsto (fun M : ℕ => L - L * ((q ^ 2)⁻¹) ^ M) atTop (𝓝 L) := by
    have := (tendsto_const_nhds (x := L) (f := atTop (α := ℕ))).sub
      ((tendsto_const_nhds (x := L) (f := atTop (α := ℕ))).mul hz2)
    simpa using this
  have hhilim : Tendsto (fun M : ℕ => L - L * ((q ^ 2)⁻¹) ^ M + (q⁻¹) ^ M) atTop (𝓝 L) := by
    have := hlolim.add hz1
    simpa using this
  have hsq : Tendsto (fun M : ℕ => decidedSeq O 2 σ (2 * M)) atTop (𝓝 L) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le hlolim hhilim hlo hhi
  have hgen : Tendsto (fun M : ℕ => decidedSeq O 2 σ (2 * M)) atTop (𝓝 (genuineDensity O 2 σ)) :=
    (decidedSeq_tendsto 2 σ).comp tendsto_two_mul_atTop
  exact tendsto_nhds_unique hgen hsq

end Density

end UniformityCheck
