/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import Uniformity.ChapH.H124b
import Uniformity.ChapI.IFCG16

/-!
# Uniformity.ChapI.IFCG17 — [FP2 2026-08-29] the multi-residual-point genres' exact counts

FP1 (`IFCG16.lean`, `runs/wave-c/verdict_FP1.md`) landed the per-genre census interface
(`RationalNonloopCensusAt` + `decidedSliceAt_all_of_census`) and the BINARY residue-layer
cardinality bridge (finite-precision Hensel uniqueness + the coprime stratum product count).
Its verdict names this unit: the multi-distinct-residual-point genres of `nonloopDecidedSet`
(strata whose residual polynomial has ≥ 2 distinct irreducible factors — where the coprime
split machinery bites) now have their exact finite-level counts in reach.

This file builds the whole multi-point layer:

* **§1 the stratum-refined decided count** `stratDecCount O n σ N g` — the number of
  `σ`-DECIDED level-`N` classes inside the level-0 stratum of `g` — with the bank lemma
  (a nonzero count forces `σ ∈ IFCG0.residuePatternFinset n`) and the fiberwise partition
  of the global `decidedCount` over the monic residuals.
* **§2 ★ THE DECIDED-REFINEMENT** (`exists_decided_factors`): if a `mulClass` product class
  is `σ`-decided, its factor classes are decided at types whose data-multisets sum to
  `σ.data`.  Pure `typeOf_mul` + multiset cancellation — NO Hensel, NO coprimality, NO
  completeness.  This is the converse the F-1 fence (H.103) does NOT forbid: the fence
  blocks recovering the SUMMANDS from the sum, not the decidedness of the factors.
* **§3 ★ THE BINARY COUNT CONVOLUTION** (`stratDecCount_mul`): over a coprime residual
  split, at every finite level,

      #dec_σ(strat(g₁·g₂)) = Σ_{s ≤ σ.data} #dec_{⟨s⟩}(strat g₁) · #dec_{⟨σ.data−s⟩}(strat g₂)

  — §2 + H.102's no-precision-loss bijection + FP1's `card_image2_mulClass`.
* **§4 the type algebra**: the per-stratum counts packaged as one element `stratPoly` of
  `AddMonoidAlgebra ℚ (Multiset (ℕ × ℕ))`, where §3 becomes literal ring multiplication
  (`stratPoly_mul`), so the n-ary fold over pairwise-coprime residual factors is
  `Multiset.prod` — commutativity and order-independence for free.
* **§5 the primary-pattern layer** (UFD bookkeeping over the residue field): `patternOf g`
  (the multiset of `(δ, e)` = (irreducible-factor degree, multiplicity) pairs), the coprime
  prime-power peel, and the pattern fiber Finsets with point-avoidance.
* **§6 the distinct-tuple aggregates** `V` over super-block lists, the exact collision peel
  `SP(b)·V(L) = V(b::L) + Σ_j V(merge_j)`, and the labelled double count tying `V` on
  simple lists to pattern-fiber sums with the multiplicity factor `multL`.
* **§7 the uniform-rational-limit calculus** (`URseq`) and THE NAMED SINGLE-POINT
  REMAINDER (`SinglePointAggregateLaw` + `DeepLinearClusterLaw`) — the campaign's LAST
  kernel — with `V_tendsto` propagating rational limits through the peel.
* **§8 the assembly**: pattern cells partition `nonloopDecidedSet`, the loop image is
  exactly inside the `{(1, m)}` (deep linear) cell, and
  `rationalNonloopCensusAt_of_singlePoint` fires the FULL census — hence
  `decidedSliceAt_all_of_singlePoint : SinglePointAggregateLaw → DeepLinearClusterLaw →
  ∀ n, DecidedSliceAt n`.

## Axiom fence

Lean core everywhere (`propext`, `Classical.choice`, `Quot.sound`); the C.33 cite does not
occur.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

noncomputable section

namespace Uniformity.Density.IFCG17

open IsLocalRing Polynomial
open Uniformity.Density.Induction

attribute [local instance] Classical.propDecidable

/-! ## §0 — counting bridges and coefficient-vector helpers -/

section Bridges

/-- `Nat.card` of a set in a finite type, as a `Finset.filter` card. -/
private theorem natCard_set_eq_card_filter {α : Type*} [Fintype α] (s : Set α) :
    Nat.card s = (Finset.univ.filter (fun a => a ∈ s)).card := by
  rw [Nat.card_coe_set_eq, ← Set.ncard_coe_finset (Finset.univ.filter (fun a => a ∈ s))]
  congr 1
  ext a
  simp

/-- Fiberwise decomposition of a set count along any labelling into a covering `Finset`. -/
private theorem natCard_eq_sum_fiber {α β : Type*} [Fintype α] (s : Set α) (φ : α → β)
    (T : Finset β) (hT : ∀ a ∈ s, φ a ∈ T) :
    Nat.card s = ∑ b ∈ T, Nat.card ((s ∩ φ ⁻¹' {b} : Set α)) := by
  rw [natCard_set_eq_card_filter,
    Finset.card_eq_sum_card_fiberwise (f := φ) (t := T)
      (fun a ha => hT a (by simpa using (Finset.mem_filter.1 ha).2))]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [natCard_set_eq_card_filter, Finset.filter_filter]
  congr 1
  ext a
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Set.mem_inter_iff,
    Set.mem_preimage, Set.mem_singleton_iff]

/-- Count of a `Finset`-indexed union of pairwise disjoint sets in a finite type. -/
private theorem natCard_biUnion {α β : Type*} [Fintype α] (T : Finset β) (F : β → Set α)
    (hdisj : ∀ b₁ ∈ T, ∀ b₂ ∈ T, b₁ ≠ b₂ → Disjoint (F b₁) (F b₂)) :
    Nat.card (⋃ b ∈ T, F b : Set α) = ∑ b ∈ T, Nat.card (F b) := by
  rw [natCard_set_eq_card_filter]
  have hfin : Finset.univ.filter (fun a => a ∈ ⋃ b ∈ T, F b)
      = T.biUnion (fun b => Finset.univ.filter (fun a => a ∈ F b)) := by
    ext a
    simp [Set.mem_iUnion]
  rw [hfin, Finset.card_biUnion]
  · exact Finset.sum_congr rfl fun b _ => (natCard_set_eq_card_filter (F b)).symm
  · intro b₁ h₁ b₂ h₂ hne
    refine Finset.disjoint_left.2 fun a ha₁ ha₂ => ?_
    exact Set.disjoint_left.1 (hdisj b₁ (Finset.mem_coe.1 h₁) b₂ (Finset.mem_coe.1 h₂) hne)
      (Finset.mem_filter.1 ha₁).2 (Finset.mem_filter.1 ha₂).2

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

/-- `monicPoly` of the coefficient vector of a monic degree-`n` polynomial is the
polynomial itself. -/
theorem monicPoly_coeff_eq_self {n : ℕ} {P : Polynomial O} (hP : P.Monic)
    (hd : P.natDegree = n) :
    monicPoly (fun i : Fin n => P.coeff (i : ℕ)) = P := by
  obtain ⟨b, hb⟩ := exists_monicPoly_eq hP hd
  have hfe : (fun i : Fin n => P.coeff (i : ℕ)) = b := by
    funext i
    rw [← hb, monicPoly_coeff_lt b i.isLt]
  rw [hfe, hb]

/-- A class is decided at (at most) one type. -/
theorem decidedAt_unique {n N : ℕ} {c : Coeff O n N} {σ τ : FactorizationType}
    (h1 : DecidedAt O n σ N c) (h2 : DecidedAt O n τ N c) : σ = τ := by
  obtain ⟨a, ha⟩ := proj_surjective' O n N c
  rw [← h1 a ha, ← h2 a ha]

end Bridges

/-! ## §1 — the stratum-refined decided count -/

section Counts

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)]

/-- **The `σ`-decided count within the level-0 stratum of `g`** — the refined census cell
whose exact multiplicativity (§3) is FP2's engine. -/
def stratDecCount (O : Type*) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Finite (ResidueField O)] (n : ℕ) (σ : FactorizationType) (N : ℕ)
    (g : Polynomial (ResidueField O)) : ℕ :=
  Nat.card ((decidedSet O n σ N ∩ levelZeroStratum O n N g : Set (Coeff O n N)))

/-- **The bank lemma**: a nonzero refined count forces the label into the O-independent
finite bank `IFCG0.residuePatternFinset n` (degree `n`, positive entries). -/
theorem mem_residuePatternFinset_of_stratDecCount_ne {n N : ℕ} {σ : FactorizationType}
    {g : Polynomial (ResidueField O)} (h : stratDecCount O n σ N g ≠ 0) :
    σ ∈ IFCG0.residuePatternFinset n := by
  have hne : (decidedSet O n σ N ∩ levelZeroStratum O n N g : Set (Coeff O n N)).Nonempty := by
    by_contra hcon
    rw [Set.not_nonempty_iff_eq_empty] at hcon
    rw [stratDecCount, hcon] at h
    simp at h
  obtain ⟨c, hcdec, -⟩ := hne
  obtain ⟨a, ha⟩ := proj_surjective' O n N c
  have hty : typeOf (monicPoly a) = σ := hcdec a ha
  rw [IFCG0.mem_residuePatternFinset_iff]
  refine ⟨?_, ?_⟩
  · rw [← hty, typeOf_degree (monicPoly_monic a), monicPoly_natDegree]
  · intro p hp
    have hpos := efPair_pos_of_mem (monicPoly_monic a) (by rw [hty]; exact hp)
    exact ⟨hpos.1, hpos.2⟩

/-- Degree-mismatch vanishing: the refined count is zero off the bank, in particular
whenever `σ.degree ≠ n`. -/
theorem stratDecCount_eq_zero_of_degree_ne {n N : ℕ} {σ : FactorizationType}
    {g : Polynomial (ResidueField O)} (h : σ.degree ≠ n) :
    stratDecCount O n σ N g = 0 := by
  by_contra hcon
  exact h ((IFCG0.mem_residuePatternFinset_iff n σ).1
    (mem_residuePatternFinset_of_stratDecCount_ne hcon)).1

/-- **The stratum partition of the global decided count**: at `1 ≤ N` the decided count is
the sum of the refined counts over the monic degree-`n` residuals. -/
theorem decidedCount_eq_sum_stratDecCount [Fintype (ResidueField O)]
    {n N : ℕ} (hN : 1 ≤ N) (σ : FactorizationType) :
    decidedCount O n σ N
      = ∑ f : IFCG4.MonicOfDeg (ResidueField O) n, stratDecCount O n σ N f.val := by
  haveI : Fintype (Coeff O n N) := Fintype.ofFinite _
  have hpart := natCard_eq_sum_fiber (decidedSet O n σ N)
    (fun c => (⟨stratumPoly O n N c, stratumPoly_monic c, stratumPoly_natDegree c⟩ :
      IFCG4.MonicOfDeg (ResidueField O) n))
    Finset.univ (fun _ _ => Finset.mem_univ _)
  calc decidedCount O n σ N = Nat.card (decidedSet O n σ N) := rfl
    _ = ∑ f : IFCG4.MonicOfDeg (ResidueField O) n, stratDecCount O n σ N f.val := by
        rw [hpart]
        refine Finset.sum_congr rfl fun f _ => ?_
        rw [stratDecCount]
        refine Nat.card_congr (Equiv.setCongr ?_)
        ext c
        simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff]
        refine and_congr_right fun _ => ?_
        rw [mem_levelZeroStratum_iff_stratumPoly hN]
        constructor
        · intro h
          rw [← h]
        · intro h
          exact Subtype.ext h

end Counts

/-! ## §2 — ★ THE DECIDED-REFINEMENT

If the product class is `σ`-decided, each factor class is decided outright, at types whose
data sum to `σ.data`.  The mechanism: `typeOf_mul` makes the type-data of any lift of the
product the SUM of the factor lifts' type-datas; freezing one factor's lift and varying the
other, the sum is constant, so by multiset cancellation each summand is constant — which is
exactly decidedness.  No Hensel input: this direction never splits anything. -/

section Refinement

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

/-- ★ **The decided-refinement.**  A `σ`-decided `mulClass` product has decided factors, at
types summing to `σ`.  (No strata, no coprimality, no completeness.) -/
theorem exists_decided_factors {n₁ n₂ N : ℕ} {c₁ : Coeff O n₁ N} {c₂ : Coeff O n₂ N}
    {σ : FactorizationType} (hdec : DecidedAt O (n₁ + n₂) σ N (mulClass c₁ c₂)) :
    ∃ σ₁ σ₂ : FactorizationType,
      DecidedAt O n₁ σ₁ N c₁ ∧ DecidedAt O n₂ σ₂ N c₂ ∧ σ₁.data + σ₂.data = σ.data := by
  obtain ⟨a₁, ha₁⟩ := proj_surjective' O n₁ N c₁
  obtain ⟨a₂, ha₂⟩ := proj_surjective' O n₂ N c₂
  have key : ∀ (b₁ : Fin n₁ → O) (b₂ : Fin n₂ → O), proj O n₁ N b₁ = c₁ →
      proj O n₂ N b₂ = c₂ →
      (typeOf (monicPoly b₁)).data + (typeOf (monicPoly b₂)).data = σ.data := by
    intro b₁ b₂ hb₁ hb₂
    have hv : proj O (n₁ + n₂) N (fun i => (monicPoly b₁ * monicPoly b₂).coeff (i : ℕ))
        = mulClass c₁ c₂ := by
      rw [mulClass_proj, hb₁, hb₂]
    have hty := hdec _ hv
    rw [monicPoly_coeff_eq_self ((monicPoly_monic b₁).mul (monicPoly_monic b₂))
      (by rw [(monicPoly_monic b₁).natDegree_mul (monicPoly_monic b₂),
        monicPoly_natDegree, monicPoly_natDegree])] at hty
    rw [← hty]
    exact (typeOf_mul (monicPoly_monic b₁) (monicPoly_monic b₂)).symm
  refine ⟨typeOf (monicPoly a₁), typeOf (monicPoly a₂), ?_, ?_, key a₁ a₂ ha₁ ha₂⟩
  · intro b hb
    exact FactorizationType.ext
      (add_right_cancel ((key b a₂ hb ha₂).trans (key a₁ a₂ ha₁ ha₂).symm))
  · intro b hb
    exact FactorizationType.ext
      (add_left_cancel ((key a₁ b ha₁ hb).trans (key a₁ a₂ ha₁ ha₂).symm))

end Refinement

/-! ## §3 — ★ THE BINARY COUNT CONVOLUTION -/

section Convolution

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [IsAdicComplete (maximalIdeal O) O] [Finite (ResidueField O)]

/-- The set-level refinement: over a coprime residual split, the `σ`-decided part of the
product stratum is EXACTLY the disjoint union, over sub-multisets `s ≤ σ.data`, of the
`mulClass` images of the `⟨s⟩`- and `⟨σ.data − s⟩`-decided parts of the factor strata. -/
theorem decidedSet_inter_stratum_mul_eq {N : ℕ} (hN : 1 ≤ N) {n₁ n₂ : ℕ}
    {g₁ g₂ : Polynomial (ResidueField O)} (hg₁ : g₁.Monic) (hg₂ : g₂.Monic)
    (hd₁ : g₁.natDegree = n₁) (hd₂ : g₂.natDegree = n₂) (hcop : IsCoprime g₁ g₂)
    (σ : FactorizationType) :
    (decidedSet O (n₁ + n₂) σ N ∩ levelZeroStratum O (n₁ + n₂) N (g₁ * g₂)
        : Set (Coeff O (n₁ + n₂) N))
      = ⋃ s ∈ σ.data.powerset.toFinset,
          Set.image2 mulClass
            (decidedSet O n₁ ⟨s⟩ N ∩ levelZeroStratum O n₁ N g₁)
            (decidedSet O n₂ ⟨σ.data - s⟩ N ∩ levelZeroStratum O n₂ N g₂) := by
  ext c
  constructor
  · rintro ⟨hcdec, hcstrat⟩
    rw [IFCG16.levelZeroStratum_mul_eq_image2 hN hg₁ hg₂ hd₁ hd₂ hcop] at hcstrat
    obtain ⟨c₁, h₁, c₂, h₂, rfl⟩ := hcstrat
    obtain ⟨σ₁, σ₂, hσ₁, hσ₂, hsum⟩ := exists_decided_factors hcdec
    refine Set.mem_biUnion (?_ : σ₁.data ∈ σ.data.powerset.toFinset) ?_
    · rw [Multiset.mem_toFinset, Multiset.mem_powerset, ← hsum]
      exact self_le_add_right _ _
    · refine ⟨c₁, ⟨?_, h₁⟩, c₂, ⟨?_, h₂⟩, rfl⟩
      · exact (show (⟨σ₁.data⟩ : FactorizationType) = σ₁ from rfl) ▸ hσ₁
      · have hs₂ : σ.data - σ₁.data = σ₂.data := by
          rw [← hsum, add_tsub_cancel_left]
        rw [show (⟨σ.data - σ₁.data⟩ : FactorizationType) = σ₂ from
          FactorizationType.ext hs₂]
        exact hσ₂
  · intro hc
    simp only [Set.mem_iUnion, exists_prop] at hc
    obtain ⟨s, hs, hmem⟩ := hc
    obtain ⟨c₁, ⟨h₁d, h₁s⟩, c₂, ⟨h₂d, h₂s⟩, rfl⟩ := hmem
    have hsle : s ≤ σ.data := Multiset.mem_powerset.1 (Multiset.mem_toFinset.1 hs)
    refine ⟨?_, mulClass_mem_levelZeroStratum hN h₁s h₂s⟩
    have hmul := decidedAt_mulClass hN hg₁ hg₂ hd₁ hd₂ hcop h₁s h₂s h₁d h₂d
    have hty : (⟨(⟨s⟩ : FactorizationType).data + (⟨σ.data - s⟩ : FactorizationType).data⟩
        : FactorizationType) = σ := by
      refine FactorizationType.ext ?_
      show s + (σ.data - s) = σ.data
      exact add_tsub_cancel_of_le hsle
    rwa [hty] at hmul

/-- ★ **The binary count convolution** — over a coprime residual split, at EVERY finite
level, the refined `σ`-decided census of the product stratum is the convolution of the
factor strata's refined censuses over the sub-multisets of `σ.data`. -/
theorem stratDecCount_mul {N : ℕ} (hN : 1 ≤ N) {n₁ n₂ : ℕ}
    {g₁ g₂ : Polynomial (ResidueField O)} (hg₁ : g₁.Monic) (hg₂ : g₂.Monic)
    (hd₁ : g₁.natDegree = n₁) (hd₂ : g₂.natDegree = n₂) (hcop : IsCoprime g₁ g₂)
    (σ : FactorizationType) :
    stratDecCount O (n₁ + n₂) σ N (g₁ * g₂)
      = ∑ s ∈ σ.data.powerset.toFinset,
          stratDecCount O n₁ ⟨s⟩ N g₁ * stratDecCount O n₂ ⟨σ.data - s⟩ N g₂ := by
  haveI : Fintype (Coeff O (n₁ + n₂) N) := Fintype.ofFinite _
  have hdisj : ∀ s₁ ∈ σ.data.powerset.toFinset, ∀ s₂ ∈ σ.data.powerset.toFinset,
      s₁ ≠ s₂ →
      Disjoint
        (Set.image2 mulClass
          (decidedSet O n₁ ⟨s₁⟩ N ∩ levelZeroStratum O n₁ N g₁)
          (decidedSet O n₂ ⟨σ.data - s₁⟩ N ∩ levelZeroStratum O n₂ N g₂))
        (Set.image2 mulClass
          (decidedSet O n₁ ⟨s₂⟩ N ∩ levelZeroStratum O n₁ N g₁)
          (decidedSet O n₂ ⟨σ.data - s₂⟩ N ∩ levelZeroStratum O n₂ N g₂)) := by
    intro s₁ hs₁ s₂ hs₂ hne
    rw [Set.disjoint_left]
    rintro x ⟨c₁, ⟨h₁d, h₁s⟩, c₂, ⟨h₂d, h₂s⟩, rfl⟩ ⟨c₁', ⟨h₁d', h₁s'⟩, c₂', ⟨h₂d', h₂s'⟩, hx⟩
    obtain ⟨e₁, e₂⟩ := eq_of_mulClass_eq hN hg₁ hg₂ hcop h₁s' h₁s h₂s' h₂s hx
    rw [e₁] at h₁d'
    have := decidedAt_unique h₁d h₁d'
    exact hne (congrArg FactorizationType.data this)
  rw [stratDecCount, decidedSet_inter_stratum_mul_eq hN hg₁ hg₂ hd₁ hd₂ hcop σ,
    natCard_biUnion _ _ hdisj]
  refine Finset.sum_congr rfl fun s hs => ?_
  rw [IFCG16.card_image2_mulClass hN hcop Set.inter_subset_right Set.inter_subset_right]
  rfl

end Convolution

/-! ## §4 — the type algebra

The refined census, packaged: `stratPoly O n N g` is the element of the commutative ring
`AddMonoidAlgebra ℚ (Multiset (ℕ × ℕ))` whose coefficient at a data-multiset `s` is the
`⟨s⟩`-decided count within the stratum of `g`.  §3's convolution becomes literal ring
multiplication (`stratPoly_mul`), so folds over pairwise-coprime residual factors are
`prod`s in a commutative ring — order-independence for free. -/

section Algebra

/-- The commutative ring carrying the type-indexed census. -/
abbrev TypeAlg : Type := AddMonoidAlgebra ℚ (Multiset (ℕ × ℕ))

/-- **Product coefficients via sub-multisets**: because `Multiset` addition is cancellative
and canonically ordered, the coefficient of a product at `t` is the convolution over the
(deduplicated) sub-multisets of `t`. -/
theorem mul_apply_powerset (X Y : TypeAlg) (t : Multiset (ℕ × ℕ)) :
    (X * Y) t = ∑ s ∈ t.powerset.toFinset, X s * Y (t - s) := by
  rw [AddMonoidAlgebra.mul_apply]
  have hinner : ∀ a₁ : Multiset (ℕ × ℕ),
      (Y.sum fun a₂ r₂ => if a₁ + a₂ = t then X a₁ * r₂ else 0)
        = if a₁ ≤ t then X a₁ * Y (t - a₁) else 0 := by
    intro a₁
    rw [Finsupp.sum]
    by_cases hle : a₁ ≤ t
    · rw [if_pos hle]
      have hcond : ∀ a₂ : Multiset (ℕ × ℕ), (a₁ + a₂ = t) ↔ (a₂ = t - a₁) := by
        intro a₂
        constructor
        · intro h
          rw [← h, add_tsub_cancel_left]
        · intro h
          rw [h, add_tsub_cancel_of_le hle]
      by_cases hsupp : (t - a₁) ∈ Y.support
      · rw [Finset.sum_eq_single (t - a₁)]
        · rw [if_pos ((hcond _).2 rfl)]
        · intro a₂ _ hne
          rw [if_neg (fun hcon => hne ((hcond a₂).1 hcon))]
        · intro hcon
          exact absurd hsupp hcon
      · have hY0 : Y (t - a₁) = 0 := Finsupp.notMem_support_iff.1 hsupp
        rw [hY0, mul_zero]
        refine Finset.sum_eq_zero fun a₂ ha₂ => ?_
        rw [if_neg]
        intro hcon
        rw [(hcond a₂).1 hcon] at ha₂
        exact hsupp ha₂
    · rw [if_neg hle]
      refine Finset.sum_eq_zero fun a₂ _ => ?_
      rw [if_neg]
      intro hcon
      exact hle (hcon ▸ self_le_add_right a₁ a₂)
  rw [Finsupp.sum]
  have hstep : ∑ a₁ ∈ X.support, (Y.sum fun a₂ r₂ => if a₁ + a₂ = t then X a₁ * r₂ else 0)
      = ∑ a₁ ∈ X.support.filter (fun a₁ => a₁ ≤ t), X a₁ * Y (t - a₁) := by
    rw [Finset.sum_filter]
    exact Finset.sum_congr rfl fun a₁ _ => hinner a₁
  rw [hstep]
  refine Finset.sum_subset ?_ ?_
  · intro s hs
    rw [Multiset.mem_toFinset, Multiset.mem_powerset]
    exact (Finset.mem_filter.1 hs).2
  · intro s hs hnot
    have hX0 : X s = 0 := by
      by_contra hcon
      exact hnot (Finset.mem_filter.2 ⟨Finsupp.mem_support_iff.2 hcon,
        Multiset.mem_powerset.1 (Multiset.mem_toFinset.1 hs)⟩)
    rw [hX0, zero_mul]

/-- Pointwise evaluation of `TypeAlg` finset sums (the `Finsupp` fact, restated on the
ring synonym). -/
private theorem typeAlg_sum_apply {ι : Type*} (S : Finset ι) (f : ι → TypeAlg)
    (t : Multiset (ℕ × ℕ)) : (∑ i ∈ S, f i) t = ∑ i ∈ S, f i t := by
  classical
  induction S using Finset.cons_induction with
  | empty => rw [Finset.sum_empty, Finset.sum_empty]; rfl
  | cons a s ha ih => rw [Finset.sum_cons, Finset.sum_cons, ← ih]; rfl

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)]

/-- **The type-indexed refined census, as one ring element.** -/
def stratPoly (O : Type*) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Finite (ResidueField O)] (n N : ℕ) (g : Polynomial (ResidueField O)) : TypeAlg :=
  ∑ σ ∈ IFCG0.residuePatternFinset n,
    AddMonoidAlgebra.single σ.data ((stratDecCount O n σ N g : ℚ))

/-- The coefficient formula, unconditional in `s` (both sides vanish off the bank). -/
theorem stratPoly_apply (n N : ℕ) (g : Polynomial (ResidueField O))
    (s : Multiset (ℕ × ℕ)) :
    stratPoly O n N g s = (stratDecCount O n ⟨s⟩ N g : ℚ) := by
  rw [stratPoly, typeAlg_sum_apply]
  by_cases hmem : (⟨s⟩ : FactorizationType) ∈ IFCG0.residuePatternFinset n
  · rw [Finset.sum_eq_single (⟨s⟩ : FactorizationType)]
    · rw [AddMonoidAlgebra.single_apply, if_pos rfl]
    · intro σ _ hne
      rw [AddMonoidAlgebra.single_apply, if_neg (fun hcon => hne (FactorizationType.ext hcon))]
    · intro hcon
      exact absurd hmem hcon
  · have hzero : stratDecCount O n ⟨s⟩ N g = 0 := by
      by_contra hcon
      exact hmem (mem_residuePatternFinset_of_stratDecCount_ne hcon)
    rw [hzero, Nat.cast_zero]
    refine Finset.sum_eq_zero fun σ hσ => ?_
    rw [AddMonoidAlgebra.single_apply, if_neg]
    intro hcon
    have : σ = (⟨s⟩ : FactorizationType) := FactorizationType.ext hcon
    exact hmem (this ▸ hσ)

/-- ★ **The census product law**: over a coprime residual split the type-indexed census
multiplies in `TypeAlg` — §3's convolution, now a ring identity. -/
theorem stratPoly_mul [IsAdicComplete (maximalIdeal O) O] {N : ℕ} (hN : 1 ≤ N)
    {n₁ n₂ : ℕ} {g₁ g₂ : Polynomial (ResidueField O)}
    (hg₁ : g₁.Monic) (hg₂ : g₂.Monic) (hd₁ : g₁.natDegree = n₁) (hd₂ : g₂.natDegree = n₂)
    (hcop : IsCoprime g₁ g₂) :
    stratPoly O (n₁ + n₂) N (g₁ * g₂) = stratPoly O n₁ N g₁ * stratPoly O n₂ N g₂ := by
  refine AddMonoidAlgebra.ext fun t => ?_
  rw [mul_apply_powerset, stratPoly_apply,
    stratDecCount_mul hN hg₁ hg₂ hd₁ hd₂ hcop ⟨t⟩]
  push_cast
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [stratPoly_apply, stratPoly_apply]

/-- The degree-`0` stratum of `1` has census `1` (the empty class, decided at `⟨0⟩`) —
the multiplicative unit of the fold. -/
theorem stratPoly_zero_one (N : ℕ) :
    stratPoly O 0 N (1 : Polynomial (ResidueField O)) = 1 := by
  have hcount : ∀ σ : FactorizationType, stratDecCount O 0 σ N 1
      = if σ = ⟨0⟩ then 1 else 0 := by
    intro σ
    by_cases hσ : σ = (⟨0⟩ : FactorizationType)
    · rw [if_pos hσ, hσ]
      have hset : (decidedSet O 0 ⟨0⟩ N ∩ levelZeroStratum O 0 N 1 :
          Set (Coeff O 0 N)) = Set.univ := by
        apply Set.eq_univ_of_forall
        intro c
        constructor
        · intro a _
          have ha1 : monicPoly a = (1 : Polynomial O) := by
            simp [monicPoly]
          rw [ha1, IFCG0.typeOf_one]
        · intro a _
          have ha1 : monicPoly a = (1 : Polynomial O) := by
            simp [monicPoly]
          rw [ha1, Polynomial.map_one]
      rw [stratDecCount, hset]
      haveI : Unique (Coeff O 0 N) :=
        ⟨⟨fun i => i.elim0⟩, fun c => funext fun i => i.elim0⟩
      simp
    · rw [if_neg hσ]
      rw [stratDecCount]
      have hset : (decidedSet O 0 σ N ∩ levelZeroStratum O 0 N 1 :
          Set (Coeff O 0 N)) = ∅ := by
        rw [Set.eq_empty_iff_forall_notMem]
        rintro c ⟨hcdec, -⟩
        have ha1 : monicPoly (fun i : Fin 0 => (0 : O)) = (1 : Polynomial O) := by
          simp [monicPoly]
        have hty := hcdec (fun _ => 0) (funext fun i => i.elim0)
        rw [ha1, IFCG0.typeOf_one] at hty
        exact hσ hty.symm
      rw [hset]
      simp
  refine AddMonoidAlgebra.ext fun t => ?_
  rw [stratPoly_apply, hcount]
  rw [AddMonoidAlgebra.one_def, AddMonoidAlgebra.single_apply]
  by_cases ht : t = 0
  · rw [if_pos (show (⟨t⟩ : FactorizationType) = ⟨0⟩ by rw [ht]), if_pos ht.symm]
    norm_num
  · rw [if_neg (fun hcon => ht (congrArg FactorizationType.data hcon)),
      if_neg (fun hcon => ht hcon.symm)]
    norm_num

end Algebra

/-! ## §5 — the primary-pattern layer (UFD bookkeeping over the residue field)

Every monic polynomial over the (finite) residue field factors uniquely into monic
irreducibles; its **primary pattern** is the multiset of `(δ, e)` = (component degree,
component multiplicity) pairs.  The multi-residual-point genres are exactly the patterns
with ≥ 2 entries.  This section builds the pattern map, the coprime prime-power peel, the
avoidance fibers, and THE DOUBLE COUNT (`sum_sigma_fiber_eq`) — the labelled/unlabelled
exchange that §6's induction consumes. -/

section Patterns

open UniqueFactorizationMonoid

variable {K : Type*} [Field K]

/-- Members of `normalizedFactors` are monic (over a field, normalized = monic). -/
theorem monic_of_mem_normalizedFactors {f p : Polynomial K}
    (hp : p ∈ normalizedFactors f) : p.Monic := by
  have h1 : normalize p = p := normalize_normalized_factor p hp
  have h2 : p ≠ 0 := (irreducible_of_normalized_factor p hp).ne_zero
  rw [← h1]
  exact monic_normalize h2

/-- A multiset of monic polynomials has monic product (unmapped form). -/
theorem monic_prod_of_forall_monic {s : Multiset (Polynomial K)}
    (h : ∀ p ∈ s, (p : Polynomial K).Monic) : s.prod.Monic := by
  have hmap := monic_multiset_prod_of_monic s id (fun p hp => h p hp)
  rwa [Multiset.map_id] at hmap

/-- The product of the normalized factors of a monic polynomial is the polynomial. -/
theorem prod_normalizedFactors_of_monic {f : Polynomial K} (hf : f.Monic) :
    (normalizedFactors f).prod = f := by
  refine eq_of_monic_of_associated ?_ hf (prod_normalizedFactors hf.ne_zero)
  exact monic_prod_of_forall_monic (fun p hp => monic_of_mem_normalizedFactors hp)

/-- For a monic irreducible `p` and nonzero `g`: membership in the factor multiset IS
divisibility. -/
theorem mem_normalizedFactors_iff_dvd {p g : Polynomial K} (hg : g ≠ 0) (hp : p.Monic)
    (hirr : Irreducible p) : p ∈ normalizedFactors g ↔ p ∣ g := by
  constructor
  · exact dvd_of_mem_normalizedFactors
  · intro hdvd
    obtain ⟨q, hq, hassoc⟩ := exists_mem_normalizedFactors_of_dvd hg hirr hdvd
    rwa [eq_of_monic_of_associated hp (monic_of_mem_normalizedFactors hq) hassoc]

/-- **The primary pattern** of a polynomial: the multiset of
`(component degree, component multiplicity)` pairs over its distinct monic irreducible
factors. -/
def patternOf (g : Polynomial K) : Multiset (ℕ × ℕ) :=
  (normalizedFactors g).toFinset.val.map
    (fun p => (p.natDegree, (normalizedFactors g).count p))

@[simp] theorem patternOf_one : patternOf (1 : Polynomial K) = 0 := by
  rw [patternOf, normalizedFactors_one]
  rfl

/-- The pattern multiplicity of `(δ, e)` counts the components with that data. -/
theorem count_patternOf (g : Polynomial K) (δ e : ℕ) :
    (patternOf g).count (δ, e)
      = ((normalizedFactors g).toFinset.filter
          (fun p => p.natDegree = δ ∧ (normalizedFactors g).count p = e)).card := by
  rw [patternOf, Multiset.count_map, Finset.card_def, Finset.filter_val]
  congr 1
  refine Multiset.filter_congr fun p _ => ?_
  rw [Prod.ext_iff]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1.symm, h2.symm⟩
  · rintro ⟨h1, h2⟩
    exact ⟨h1.symm, h2.symm⟩

/-- **The coprime prime-power peel for patterns**: multiplying a fresh monic irreducible
power onto a coprime cofactor prepends its `(δ, e)` block. -/
theorem patternOf_pow_mul {p g : Polynomial K} (hp : p.Monic) (hirr : Irreducible p)
    {e : ℕ} (he : 1 ≤ e) (hg : g ≠ 0) (hnd : ¬ p ∣ g) :
    patternOf (p ^ e * g) = (p.natDegree, e) ::ₘ patternOf g := by
  have hpe : (p ^ e : Polynomial K) ≠ 0 := pow_ne_zero e hp.ne_zero
  have hnf : normalizedFactors (p ^ e * g)
      = e • ({p} : Multiset (Polynomial K)) + normalizedFactors g := by
    rw [normalizedFactors_mul hpe hg, normalizedFactors_pow,
      normalizedFactors_irreducible hirr, hp.normalize_eq_self]
  have hpmem : p ∉ normalizedFactors g := fun hmem =>
    hnd (dvd_of_mem_normalizedFactors hmem)
  have htf : (e • ({p} : Multiset (Polynomial K)) + normalizedFactors g).toFinset
      = insert p (normalizedFactors g).toFinset := by
    rw [Multiset.toFinset_add, Multiset.toFinset_nsmul _ e (by omega),
      Multiset.toFinset_singleton, Finset.singleton_union]
  have hcount : ∀ q : Polynomial K,
      (e • ({p} : Multiset (Polynomial K)) + normalizedFactors g).count q
        = (if q = p then e else 0) + (normalizedFactors g).count q := by
    intro q
    rw [Multiset.count_add, Multiset.count_nsmul, Multiset.count_singleton]
    by_cases hqp : q = p
    · rw [if_pos hqp, if_pos hqp, mul_one]
    · rw [if_neg hqp, if_neg hqp, mul_zero]
  rw [patternOf, patternOf, hnf, htf,
    Finset.insert_val_of_notMem (by rwa [Multiset.mem_toFinset]),
    Multiset.map_cons]
  congr 1
  · rw [hcount p, if_pos rfl, Multiset.count_eq_zero.2 hpmem, add_zero]
  · refine Multiset.map_congr rfl fun q hq => ?_
    have hqmem : q ∈ normalizedFactors g := by
      rwa [← Multiset.mem_toFinset]
    have hqp : q ≠ p := fun hcon => hpmem (hcon ▸ hqmem)
    rw [hcount q, if_neg hqp, zero_add]

/-- **The primary extraction**: any component of a monic polynomial peels off as an exact
prime power times a monic cofactor prime to it. -/
theorem exists_primary_decomposition {g : Polynomial K} (hg : g.Monic) {p : Polynomial K}
    (hp : p ∈ normalizedFactors g) :
    ∃ g' : Polynomial K, g'.Monic ∧ g = p ^ ((normalizedFactors g).count p) * g'
      ∧ ¬ p ∣ g' := by
  have hsplit : Multiset.filter (fun q => q = p) (normalizedFactors g)
      + Multiset.filter (fun q => ¬ q = p) (normalizedFactors g) = normalizedFactors g :=
    Multiset.filter_add_not _ _
  rw [Multiset.filter_eq'] at hsplit
  set rest := (normalizedFactors g).filter (fun q => ¬ q = p) with hrest
  refine ⟨rest.prod, ?_, ?_, ?_⟩
  · exact monic_prod_of_forall_monic (fun q hq =>
      monic_of_mem_normalizedFactors (Multiset.mem_of_mem_filter hq))
  · conv_lhs => rw [← prod_normalizedFactors_of_monic hg, ← hsplit,
      Multiset.prod_add, Multiset.prod_replicate]
  · intro hdvd
    have hprime : Prime p :=
      (UniqueFactorizationMonoid.irreducible_iff_prime).1
        (irreducible_of_normalized_factor p hp)
    obtain ⟨q, hq, hpq⟩ := hprime.exists_mem_multiset_dvd hdvd
    have hqmem : q ∈ normalizedFactors g := Multiset.mem_of_mem_filter hq
    have hqp : ¬ q = p := by
      have := Multiset.of_mem_filter hq
      simpa using this
    have hqirr : Irreducible q := irreducible_of_normalized_factor q hqmem
    exact hqp (eq_of_monic_of_associated (monic_of_mem_normalizedFactors hp)
      (monic_of_mem_normalizedFactors hqmem)
      (hprime.irreducible.associated_of_dvd hqirr hpq)).symm

/-- The exact multiplicity of a fresh prime power in a coprime product. -/
theorem count_normalizedFactors_pow_mul {p g : Polynomial K} (hp : p.Monic)
    (hirr : Irreducible p) (e : ℕ) (hg : g ≠ 0) (hnd : ¬ p ∣ g) :
    (normalizedFactors (p ^ e * g)).count p = e := by
  rw [normalizedFactors_mul (pow_ne_zero e hp.ne_zero) hg, normalizedFactors_pow,
    normalizedFactors_irreducible hirr, hp.normalize_eq_self, Multiset.count_add,
    Multiset.count_nsmul, Multiset.count_singleton_self, mul_one,
    Multiset.count_eq_zero.2 (fun hmem => hnd (dvd_of_mem_normalizedFactors hmem)), add_zero]

end Patterns

/-! ### §5b — the avoidance fibers and THE DOUBLE COUNT -/

section Fibers

open UniqueFactorizationMonoid

variable {K : Type*} [Field K] [Fintype K]

/-- The Finset of monic degree-`n` polynomials (IFCG4's carrier, as a `Finset` of
polynomials). -/
def monicFinset (K : Type*) [Field K] [Fintype K] (n : ℕ) : Finset (Polynomial K) :=
  (Finset.univ : Finset (IFCG4.MonicOfDeg K n)).image Subtype.val

theorem mem_monicFinset_iff {n : ℕ} {g : Polynomial K} :
    g ∈ monicFinset K n ↔ g.Monic ∧ g.natDegree = n := by
  rw [monicFinset, Finset.mem_image]
  constructor
  · rintro ⟨f, -, rfl⟩
    exact f.2
  · intro h
    exact ⟨⟨g, h⟩, Finset.mem_univ _, rfl⟩

/-- The Finset of monic irreducible degree-`δ` polynomials. -/
def irredFinset (K : Type*) [Field K] [Fintype K] (δ : ℕ) : Finset (Polynomial K) :=
  (monicFinset K δ).filter Irreducible

theorem mem_irredFinset_iff {δ : ℕ} {p : Polynomial K} :
    p ∈ irredFinset K δ ↔ p.Monic ∧ p.natDegree = δ ∧ Irreducible p := by
  rw [irredFinset, Finset.mem_filter, mem_monicFinset_iff]
  tauto

/-- **The avoidance pattern fiber**: monic degree-`n` polynomials of primary pattern `π`
not divisible by any point of `A`. -/
def fiberFinset (K : Type*) [Field K] [Fintype K] (n : ℕ) (π : Multiset (ℕ × ℕ))
    (A : Finset (Polynomial K)) : Finset (Polynomial K) :=
  (monicFinset K n).filter (fun g => patternOf g = π ∧ ∀ p ∈ A, ¬ p ∣ g)

theorem mem_fiberFinset_iff {n : ℕ} {π : Multiset (ℕ × ℕ)} {A : Finset (Polynomial K)}
    {g : Polynomial K} :
    g ∈ fiberFinset K n π A
      ↔ (g.Monic ∧ g.natDegree = n) ∧ patternOf g = π ∧ ∀ p ∈ A, ¬ p ∣ g := by
  rw [fiberFinset, Finset.mem_filter, mem_monicFinset_iff]

/-- Base case: the degree-0 empty-pattern fiber is `{1}` regardless of the avoidance set
(of irreducibles). -/
theorem fiberFinset_zero (A : Finset (Polynomial K)) (hA : ∀ q ∈ A, Irreducible q) :
    fiberFinset K 0 0 A = {1} := by
  ext g
  rw [mem_fiberFinset_iff, Finset.mem_singleton]
  constructor
  · rintro ⟨⟨hm, hd⟩, -, -⟩
    exact (Polynomial.Monic.natDegree_eq_zero hm).1 hd
  · rintro rfl
    refine ⟨⟨monic_one, natDegree_one⟩, patternOf_one, ?_⟩
    intro q hq hdvd
    exact (hA q hq).not_isUnit (isUnit_of_dvd_one hdvd)

/-- ★ **THE DOUBLE COUNT** — the labelled/unlabelled exchange.  Summing any function of
the assembled polynomial `p₀ ^ e * g'` over (a fresh monic irreducible point `p₀` of
degree `δ`) × (the `π`-fiber avoiding `A ∪ {p₀}`) hits each member of the
`(δ,e) ::ₘ π`-fiber avoiding `A` exactly `π.count (δ,e) + 1` times — once per
`(δ,e)`-component of the target. -/
theorem sum_sigma_fiber_eq {M : Type*} [AddCommMonoid M]
    {δ e : ℕ} (hδ : 1 ≤ δ) (he : 1 ≤ e) (n' : ℕ) (π : Multiset (ℕ × ℕ))
    (A : Finset (Polynomial K)) (hA : ∀ q ∈ A, q.Monic ∧ Irreducible q)
    (F : Polynomial K → M) :
    ∑ p₀ ∈ irredFinset K δ \ A, ∑ g' ∈ fiberFinset K n' π (insert p₀ A), F (p₀ ^ e * g')
      = (π.count (δ, e) + 1)
          • ∑ g ∈ fiberFinset K (δ * e + n') ((δ, e) ::ₘ π) A, F g := by
  classical
  -- the per-target component Finset
  set comps : Polynomial K → Finset (Polynomial K) := fun g =>
    (normalizedFactors g).toFinset.filter
      (fun p => p.natDegree = δ ∧ (normalizedFactors g).count p = e) with hcomps
  -- RHS = the (g, marked component) sigma sum
  have hRHS : (π.count (δ, e) + 1)
        • ∑ g ∈ fiberFinset K (δ * e + n') ((δ, e) ::ₘ π) A, F g
      = ∑ x ∈ (fiberFinset K (δ * e + n') ((δ, e) ::ₘ π) A).sigma (fun g => comps g),
          F x.1 := by
    rw [Finset.sum_sigma, Finset.smul_sum]
    refine Finset.sum_congr rfl fun g hg => ?_
    have hcard : (comps g).card = π.count (δ, e) + 1 := by
      have hpat : patternOf g = (δ, e) ::ₘ π := (mem_fiberFinset_iff.1 hg).2.1
      rw [hcomps, ← count_patternOf, hpat, Multiset.count_cons_self]
    calc (π.count (δ, e) + 1) • F g = (comps g).card • F g := by rw [hcard]
      _ = ∑ _s ∈ comps g, F g := (Finset.sum_const _).symm
      _ = ∑ s ∈ comps g, F (⟨g, s⟩ : Σ _ : Polynomial K, Polynomial K).fst := rfl
  rw [hRHS, Finset.sum_sigma']
  -- the bijection between the two sigma index sets
  refine Finset.sum_nbij' (i := fun x => (⟨x.1 ^ e * x.2, x.1⟩ : Σ _ : Polynomial K, Polynomial K))
    (j := fun y => (⟨y.2, y.1 /ₘ y.2 ^ e⟩ : Σ _ : Polynomial K, Polynomial K))
    ?_ ?_ ?_ ?_ ?_
  · -- membership forward
    rintro ⟨p₀, g'⟩ hx
    rw [Finset.mem_sigma] at hx ⊢
    obtain ⟨hp₀, hg'⟩ := hx
    obtain ⟨hp₀i, hp₀A⟩ := Finset.mem_sdiff.1 hp₀
    obtain ⟨hp₀m, hp₀d, hp₀irr⟩ := mem_irredFinset_iff.1 hp₀i
    obtain ⟨⟨hg'm, hg'd⟩, hg'pat, hg'avoid⟩ := mem_fiberFinset_iff.1 hg'
    have hnd : ¬ p₀ ∣ g' := hg'avoid p₀ (Finset.mem_insert_self _ _)
    have hgm : (p₀ ^ e * g').Monic := (hp₀m.pow e).mul hg'm
    have hgd : (p₀ ^ e * g').natDegree = δ * e + n' := by
      rw [(hp₀m.pow e).natDegree_mul hg'm, Polynomial.natDegree_pow, hp₀d, hg'd,
        Nat.mul_comm]
    constructor
    · rw [mem_fiberFinset_iff]
      refine ⟨⟨hgm, hgd⟩, ?_, ?_⟩
      · rw [patternOf_pow_mul hp₀m hp₀irr he hg'm.ne_zero hnd, hp₀d, hg'pat]
      · intro q hq hdvd
        obtain ⟨hqm, hqirr⟩ := hA q hq
        have hqprime : Prime q := (UniqueFactorizationMonoid.irreducible_iff_prime).1 hqirr
        rcases hqprime.dvd_mul.1 hdvd with hq1 | hq2
        · have hqp₀ : q = p₀ := eq_of_monic_of_associated hqm hp₀m
            (hqprime.irreducible.associated_of_dvd hp₀irr (hqprime.dvd_of_dvd_pow hq1))
          exact hp₀A (hqp₀ ▸ hq)
        · exact hg'avoid q (Finset.mem_insert_of_mem hq) hq2
    · -- the marked component
      rw [hcomps, Finset.mem_filter, Multiset.mem_toFinset,
        mem_normalizedFactors_iff_dvd hgm.ne_zero hp₀m hp₀irr]
      exact ⟨Dvd.dvd.mul_right (dvd_pow_self p₀ (by omega)) _,
        hp₀d, count_normalizedFactors_pow_mul hp₀m hp₀irr e hg'm.ne_zero hnd⟩
  · -- membership backward
    rintro ⟨g, p₀⟩ hy
    rw [Finset.mem_sigma] at hy ⊢
    obtain ⟨hg, hp₀⟩ := hy
    replace hg : g ∈ fiberFinset K (δ * e + n') ((δ, e) ::ₘ π) A := hg
    replace hp₀ : p₀ ∈ comps g := hp₀
    obtain ⟨⟨hgm, hgd⟩, hgpat, hgavoid⟩ := mem_fiberFinset_iff.1 hg
    rw [hcomps, Finset.mem_filter, Multiset.mem_toFinset] at hp₀
    obtain ⟨hp₀mem, hp₀d, hp₀cnt⟩ := hp₀
    have hp₀m : p₀.Monic := monic_of_mem_normalizedFactors hp₀mem
    have hp₀irr : Irreducible p₀ := irreducible_of_normalized_factor p₀ hp₀mem
    obtain ⟨g₀, hg₀m, hg₀eq, hg₀nd⟩ := exists_primary_decomposition hgm hp₀mem
    rw [hp₀cnt] at hg₀eq
    have hquot : g /ₘ p₀ ^ e = g₀ := by
      rw [hg₀eq]
      exact Polynomial.mul_divByMonic_cancel_left g₀ (hp₀m.pow e)
    have hg₀d : g₀.natDegree = n' := by
      have h1 : g.natDegree = e * δ + g₀.natDegree := by
        rw [hg₀eq, (hp₀m.pow e).natDegree_mul hg₀m, Polynomial.natDegree_pow, hp₀d]
      rw [hgd, Nat.mul_comm δ e] at h1
      omega
    have hg₀pat : patternOf g₀ = π := by
      have h1 : patternOf g = (p₀.natDegree, e) ::ₘ patternOf g₀ := by
        rw [hg₀eq]
        exact patternOf_pow_mul hp₀m hp₀irr he hg₀m.ne_zero hg₀nd
      rw [hgpat, hp₀d] at h1
      exact (Multiset.cons_inj_right _).1 h1.symm
    constructor
    · rw [Finset.mem_sdiff, mem_irredFinset_iff]
      refine ⟨⟨hp₀m, hp₀d, hp₀irr⟩, fun hcon => ?_⟩
      exact hgavoid p₀ hcon (dvd_of_mem_normalizedFactors hp₀mem)
    · rw [hquot, mem_fiberFinset_iff]
      refine ⟨⟨hg₀m, hg₀d⟩, hg₀pat, ?_⟩
      intro q hq
      rcases Finset.mem_insert.1 hq with rfl | hqA
      · exact hg₀nd
      · intro hdvd
        exact hgavoid q hqA (hdvd.trans ⟨p₀ ^ e, by rw [hg₀eq]; ring⟩)
  · -- j ∘ i = id
    rintro ⟨p₀, g'⟩ hx
    rw [Finset.mem_sigma] at hx
    obtain ⟨hp₀, hg'⟩ := hx
    obtain ⟨hp₀i, -⟩ := Finset.mem_sdiff.1 hp₀
    obtain ⟨hp₀m, -, -⟩ := mem_irredFinset_iff.1 hp₀i
    have : (p₀ ^ e * g') /ₘ p₀ ^ e = g' :=
      Polynomial.mul_divByMonic_cancel_left g' (hp₀m.pow e)
    simp only [this]
  · -- i ∘ j = id
    rintro ⟨g, p₀⟩ hy
    rw [Finset.mem_sigma] at hy
    obtain ⟨hg, hp₀⟩ := hy
    replace hg : g ∈ fiberFinset K (δ * e + n') ((δ, e) ::ₘ π) A := hg
    replace hp₀ : p₀ ∈ comps g := hp₀
    obtain ⟨⟨hgm, -⟩, -, -⟩ := mem_fiberFinset_iff.1 hg
    rw [hcomps, Finset.mem_filter, Multiset.mem_toFinset] at hp₀
    obtain ⟨hp₀mem, -, hp₀cnt⟩ := hp₀
    have hp₀m : p₀.Monic := monic_of_mem_normalizedFactors hp₀mem
    obtain ⟨g₀, hg₀m, hg₀eq, -⟩ := exists_primary_decomposition hgm hp₀mem
    rw [hp₀cnt] at hg₀eq
    have hquot : g /ₘ p₀ ^ e = g₀ := by
      rw [hg₀eq]
      exact Polynomial.mul_divByMonic_cancel_left g₀ (hp₀m.pow e)
    simp only [hquot, ← hg₀eq]
  · -- values agree
    rintro ⟨p₀, g'⟩ _
    rfl

end Fibers

/-! ## §6 — the distinct-tuple aggregates and the exact collision peel

A **super-block** is a degree `δ` with a list of exponents `E` — one residual point
carrying several prime-power constraints (multiple exponents arise ONLY as collision
corrections; the genre cells use singleton `E`).  `VAgg` sums, over tuples of DISTINCT
monic irreducibles (one of degree `(B i).δ` per block, all avoiding `A`), the `TypeAlg`
product of the per-block censuses.  The two structural facts:

* `VAgg_cons_eq` — the EXACT collision peel: head-block-summed-freely × tail aggregate
  = the (r+1)-aggregate + the merge corrections.  No inclusion-exclusion cascade: a fresh
  point collides with at most one tuple coordinate.
* `VAgg_eq_fiber` (§6b) — on simple blocks the aggregate is `multB` times the pattern
  fiber's census sum: the labelled/unlabelled exchange, by induction on `r` through the
  avoidance parameter and §5b's double count. -/

section Aggregates

/-- A super-block: a residual-point degree with a list of exponent constraints. -/
structure SBlock where
  /-- the degree of the residual point -/
  δ : ℕ
  /-- the exponents of the prime powers carried at this point -/
  E : List ℕ

/-- The mass of a super-block. -/
def SBlock.mass (b : SBlock) : ℕ := b.δ * b.E.sum

section Tuples

variable {K : Type*} [Field K] [Fintype K]

/-- Distinct tuples of monic irreducibles matching a block system, avoiding `A`. -/
def tupleFinset (K : Type*) [Field K] [Fintype K] (r : ℕ) (B : Fin r → SBlock)
    (A : Finset (Polynomial K)) : Finset (Fin r → Polynomial K) :=
  (Fintype.piFinset (fun i => irredFinset K (B i).δ \ A)).filter Function.Injective

theorem mem_tupleFinset_iff {r : ℕ} {B : Fin r → SBlock} {A : Finset (Polynomial K)}
    {t : Fin r → Polynomial K} :
    t ∈ tupleFinset K r B A
      ↔ (∀ i, t i ∈ irredFinset K (B i).δ \ A) ∧ Function.Injective t := by
  rw [tupleFinset, Finset.mem_filter, Fintype.mem_piFinset]

/-- **The avoidance head-peel**: summing over `(r+1)`-tuples of a cons block system is
summing the head point freely (off `A`) and the tail tuples avoiding `A ∪ {head}`. -/
theorem tuple_sum_succ {M : Type*} [AddCommMonoid M] {r : ℕ} (b : SBlock)
    (B : Fin r → SBlock) (A : Finset (Polynomial K))
    (f : (Fin (r + 1) → Polynomial K) → M) :
    ∑ t ∈ tupleFinset K (r + 1) (Fin.cons b B) A, f t
      = ∑ p₀ ∈ irredFinset K b.δ \ A,
          ∑ t' ∈ tupleFinset K r B (insert p₀ A), f (Fin.cons p₀ t') := by
  rw [Finset.sum_sigma']
  refine Finset.sum_nbij' (i := fun t => ⟨t 0, Fin.tail t⟩)
    (j := fun x => Fin.cons x.1 x.2) ?_ ?_ ?_ ?_ ?_
  · intro t ht
    obtain ⟨hval, hinj⟩ := mem_tupleFinset_iff.1 ht
    rw [Finset.mem_sigma]
    constructor
    · exact hval 0
    · rw [mem_tupleFinset_iff]
      refine ⟨fun i => ?_, fun i₁ i₂ h12 => ?_⟩
      · have hv := hval i.succ
        rw [Finset.mem_sdiff] at hv ⊢
        refine ⟨hv.1, ?_⟩
        rw [Finset.mem_insert]
        rintro (hcon | hcon)
        · exact Fin.succ_ne_zero i (hinj hcon)
        · exact hv.2 hcon
      · exact Fin.succ_injective r (hinj h12)
  · rintro ⟨p₀, t'⟩ hx
    dsimp only
    rw [Finset.mem_sigma] at hx
    obtain ⟨hp₀, ht'⟩ := hx
    replace hp₀ : p₀ ∈ irredFinset K b.δ \ A := hp₀
    replace ht' : t' ∈ tupleFinset K r B (insert p₀ A) := ht'
    obtain ⟨hval, hinj⟩ := mem_tupleFinset_iff.1 ht'
    rw [mem_tupleFinset_iff]
    constructor
    · intro i
      refine Fin.cases ?_ (fun i' => ?_) i
      · rwa [Fin.cons_zero, Fin.cons_zero]
      · rw [Fin.cons_succ, Fin.cons_succ]
        have hv := hval i'
        rw [Finset.mem_sdiff] at hv ⊢
        exact ⟨hv.1, fun hcon => hv.2 (Finset.mem_insert_of_mem hcon)⟩
    · rw [Fin.cons_injective_iff]
      refine ⟨?_, hinj⟩
      rintro ⟨i', hcon⟩
      have hv := hval i'
      rw [Finset.mem_sdiff, Finset.mem_insert] at hv
      exact hv.2 (Or.inl hcon)
  · intro t _
    exact Fin.cons_self_tail t
  · rintro ⟨p₀, t'⟩ _
    dsimp only
    rw [Sigma.mk.injEq]
    exact ⟨Fin.cons_zero (α := fun _ : Fin (r + 1) => Polynomial K) p₀ t',
      heq_of_eq (Fin.tail_cons (α := fun _ : Fin (r + 1) => Polynomial K) p₀ t')⟩
  · intro t _
    rw [Fin.cons_self_tail]

/-- **The collision split**: a fresh head point summed freely against distinct tuples of
the tail system either misses the tuple (the `(r+1)`-aggregate) or equals exactly one
coordinate of matching degree (the merge corrections). -/
theorem tuple_sum_collision {M : Type*} [AddCommMonoid M] {r : ℕ} (b : SBlock)
    (B : Fin r → SBlock) (A : Finset (Polynomial K))
    (f : Polynomial K → (Fin r → Polynomial K) → M) :
    ∑ p₀ ∈ irredFinset K b.δ \ A, ∑ t ∈ tupleFinset K r B A, f p₀ t
      = (∑ t ∈ tupleFinset K (r + 1) (Fin.cons b B) A, f (t 0) (Fin.tail t))
        + ∑ j ∈ Finset.univ.filter (fun j : Fin r => (B j).δ = b.δ),
            ∑ t ∈ tupleFinset K r B A, f (t j) t := by
  classical
  rw [← Finset.sum_product']
  rw [← Finset.sum_filter_add_sum_filter_not
    ((irredFinset K b.δ \ A) ×ˢ tupleFinset K r B A) (fun x => ∀ i, x.2 i ≠ x.1)]
  congr 1
  · -- the missing-point part is the (r+1)-aggregate
    refine Finset.sum_nbij' (i := fun x => Fin.cons x.1 x.2)
      (j := fun t => (t 0, Fin.tail t)) ?_ ?_ ?_ ?_ ?_
    · rintro ⟨p₀, t⟩ hx
      rw [Finset.mem_filter, Finset.mem_product] at hx
      obtain ⟨⟨hp₀, ht⟩, hfresh⟩ := hx
      obtain ⟨hval, hinj⟩ := mem_tupleFinset_iff.1 ht
      rw [mem_tupleFinset_iff]
      constructor
      · intro i
        refine Fin.cases ?_ (fun i' => ?_) i
        · rwa [Fin.cons_zero, Fin.cons_zero]
        · rw [Fin.cons_succ, Fin.cons_succ]
          exact hval i'
      · rw [Fin.cons_injective_iff]
        refine ⟨?_, hinj⟩
        rintro ⟨i', hcon⟩
        exact hfresh i' hcon
    · intro t ht
      obtain ⟨hval, hinj⟩ := mem_tupleFinset_iff.1 ht
      rw [Finset.mem_filter, Finset.mem_product]
      refine ⟨⟨hval 0, ?_⟩, ?_⟩
      · rw [mem_tupleFinset_iff]
        refine ⟨fun i => hval i.succ, fun i₁ i₂ h12 => Fin.succ_injective r (hinj h12)⟩
      · intro i hcon
        exact Fin.succ_ne_zero i (hinj hcon)
    · rintro ⟨p₀, t⟩ _
      dsimp only
      rw [Prod.mk.injEq]
      exact ⟨Fin.cons_zero (α := fun _ : Fin (r + 1) => Polynomial K) p₀ t,
        Fin.tail_cons (α := fun _ : Fin (r + 1) => Polynomial K) p₀ t⟩
    · intro t _
      exact Fin.cons_self_tail t
    · rintro ⟨p₀, t⟩ _
      dsimp only
      rw [Fin.cons_zero, Fin.tail_cons]
  · -- the collision part: the point IS one (unique, degree-matching) coordinate
    rw [Finset.sum_sigma']
    refine (Finset.sum_bij (i := fun x _ => ((x.2 x.1, x.2) : Polynomial K × (Fin r → Polynomial K)))
      ?_ ?_ ?_ ?_).symm
    · -- maps into the collision filter
      rintro ⟨j, t⟩ hx
      rw [Finset.mem_sigma] at hx
      obtain ⟨hj, ht⟩ := hx
      replace ht : t ∈ tupleFinset K r B A := ht
      have hδ : (B j).δ = b.δ := (Finset.mem_filter.1 hj).2
      obtain ⟨hval, hinj⟩ := mem_tupleFinset_iff.1 ht
      rw [Finset.mem_filter, Finset.mem_product]
      have hvj := hval j
      rw [Finset.mem_sdiff] at hvj
      refine ⟨⟨?_, ht⟩, ?_⟩
      · rw [Finset.mem_sdiff, ← hδ]
        exact hvj
      · push_neg
        exact ⟨j, rfl⟩
    · -- injectivity
      rintro ⟨j₁, t₁⟩ hx₁ ⟨j₂, t₂⟩ hx₂ heq
      rw [Finset.mem_sigma] at hx₁ hx₂
      replace ht₁ : t₁ ∈ tupleFinset K r B A := hx₁.2
      rw [Prod.mk.injEq] at heq
      obtain ⟨hval, htt⟩ := heq
      subst htt
      obtain ⟨-, hinj⟩ := mem_tupleFinset_iff.1 ht₁
      rw [Sigma.mk.injEq]
      exact ⟨hinj hval, HEq.rfl⟩
    · -- surjectivity onto the collision filter
      rintro ⟨p₀, t⟩ hy
      rw [Finset.mem_filter, Finset.mem_product] at hy
      obtain ⟨⟨hp₀, ht⟩, hcol⟩ := hy
      push_neg at hcol
      obtain ⟨j, hj⟩ := hcol
      obtain ⟨hval, hinj⟩ := mem_tupleFinset_iff.1 ht
      have hδ : (B j).δ = b.δ := by
        have h1 := hval j
        rw [Finset.mem_sdiff, mem_irredFinset_iff] at h1
        rw [Finset.mem_sdiff, mem_irredFinset_iff] at hp₀
        rw [← h1.1.2.1, hj, hp₀.1.2.1]
      refine ⟨⟨j, t⟩, ?_, ?_⟩
      · rw [Finset.mem_sigma]
        exact ⟨Finset.mem_filter.2 ⟨Finset.mem_univ _, hδ⟩, ht⟩
      · rw [Prod.mk.injEq]
        exact ⟨hj, rfl⟩
    · -- values agree
      rintro ⟨j, t⟩ _
      rfl

end Tuples

section VAgg

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)] [Fintype (ResidueField O)]

/-- The `TypeAlg` census of one super-block at the point `p`. -/
def blockPoly (O : Type*) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Finite (ResidueField O)] (N : ℕ) (δ : ℕ) (p : Polynomial (ResidueField O))
    (E : List ℕ) : TypeAlg :=
  (E.map (fun e => stratPoly O (δ * e) N (p ^ e))).prod

theorem blockPoly_append (N δ : ℕ) (p : Polynomial (ResidueField O)) (E₁ E₂ : List ℕ) :
    blockPoly O N δ p (E₁ ++ E₂) = blockPoly O N δ p E₁ * blockPoly O N δ p E₂ := by
  rw [blockPoly, blockPoly, blockPoly, List.map_append, List.prod_append]

theorem blockPoly_singleton (N δ : ℕ) (p : Polynomial (ResidueField O)) (e : ℕ) :
    blockPoly O N δ p [e] = stratPoly O (δ * e) N (p ^ e) := by
  rw [blockPoly, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]

/-- **The distinct-tuple aggregate** over a block system, avoiding `A`. -/
def VAgg (O : Type*) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Finite (ResidueField O)] [Fintype (ResidueField O)] (N : ℕ) {r : ℕ}
    (B : Fin r → SBlock) (A : Finset (Polynomial (ResidueField O))) : TypeAlg :=
  ∑ t ∈ tupleFinset (ResidueField O) r B A,
    ∏ i, blockPoly O N (B i).δ (t i) (B i).E

/-- **The single-point aggregate** of one super-block — the object of the NAMED
single-point remainder. -/
def SPAgg (O : Type*) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Finite (ResidueField O)] [Fintype (ResidueField O)] (N : ℕ) (b : SBlock)
    (A : Finset (Polynomial (ResidueField O))) : TypeAlg :=
  ∑ p ∈ irredFinset (ResidueField O) b.δ \ A, blockPoly O N b.δ p b.E

set_option maxHeartbeats 2000000 in
/-- ★ **THE EXACT COLLISION PEEL**: head-summed-freely × tail aggregate = the extended
aggregate + one merge correction per degree-matching tail block.  An identity of finite
`TypeAlg` sums — no inclusion-exclusion cascade. -/
theorem VAgg_cons_eq (N : ℕ) {r : ℕ} (b : SBlock) (B : Fin r → SBlock)
    (A : Finset (Polynomial (ResidueField O))) :
    SPAgg O N b A * VAgg O N B A
      = VAgg O N (Fin.cons b B) A
        + ∑ j ∈ Finset.univ.filter (fun j : Fin r => (B j).δ = b.δ),
            VAgg O N (Function.update B j ⟨(B j).δ, (B j).E ++ b.E⟩) A := by
  classical
  rw [SPAgg, VAgg, Finset.sum_mul_sum]
  rw [tuple_sum_collision b B A
    (fun p₀ t => blockPoly O N b.δ p₀ b.E * ∏ i, blockPoly O N (B i).δ (t i) (B i).E)]
  congr 1
  · -- the fresh part IS the (r+1)-aggregate
    rw [VAgg]
    refine Finset.sum_congr rfl fun t ht => ?_
    show blockPoly O N b.δ (t 0) b.E
        * ∏ i, blockPoly O N (B i).δ (Fin.tail t i) (B i).E = _
    rw [Fin.prod_univ_succ, Fin.cons_zero]
    congr 1
  · -- the collision part IS the merge corrections
    refine Finset.sum_congr rfl fun j hj => ?_
    have hδ : (B j).δ = b.δ := (Finset.mem_filter.1 hj).2
    rw [VAgg]
    have htup : tupleFinset (ResidueField O) r
        (Function.update B j ⟨(B j).δ, (B j).E ++ b.E⟩) A
        = tupleFinset (ResidueField O) r B A := by
      unfold tupleFinset
      have hfam : (fun i => irredFinset (ResidueField O)
            ((Function.update B j ⟨(B j).δ, (B j).E ++ b.E⟩ : Fin r → SBlock) i).δ \ A)
          = fun i => irredFinset (ResidueField O) (B i).δ \ A := by
        funext i
        by_cases hij : i = j
        · subst hij
          rw [Function.update_self]
        · rw [Function.update_of_ne hij]
      rw [hfam]
    rw [htup]
    refine Finset.sum_congr rfl fun t ht => ?_
    have hfun : (fun i => blockPoly O N ((Function.update B j
          ⟨(B j).δ, (B j).E ++ b.E⟩ : Fin r → SBlock) i).δ (t i)
          ((Function.update B j ⟨(B j).δ, (B j).E ++ b.E⟩ : Fin r → SBlock) i).E)
        = Function.update (fun i => blockPoly O N (B i).δ (t i) (B i).E) j
            (blockPoly O N (B j).δ (t j) ((B j).E ++ b.E)) := by
      funext i
      by_cases hij : i = j
      · subst hij
        rw [Function.update_self, Function.update_self]
      · rw [Function.update_of_ne hij, Function.update_of_ne hij]
    rw [hfun, Finset.prod_update_of_mem (Finset.mem_univ j), blockPoly_append, hδ,
      ← Finset.mul_prod_erase Finset.univ
        (fun i => blockPoly O N (B i).δ (t i) (B i).E) (Finset.mem_univ j),
      Finset.sdiff_singleton_eq_erase, hδ, ← mul_assoc,
      mul_comm (blockPoly O N b.δ (t j) b.E) (blockPoly O N b.δ (t j) (B j).E)]

end VAgg

end Aggregates

end Uniformity.Density.IFCG17

end

/-! ## AXCHECK FOOTER (partial — stages S1–S2) -/

#print axioms Uniformity.Density.IFCG17.monicPoly_coeff_eq_self
#print axioms Uniformity.Density.IFCG17.decidedAt_unique
#print axioms Uniformity.Density.IFCG17.mem_residuePatternFinset_of_stratDecCount_ne
#print axioms Uniformity.Density.IFCG17.stratDecCount_eq_zero_of_degree_ne
#print axioms Uniformity.Density.IFCG17.decidedCount_eq_sum_stratDecCount
#print axioms Uniformity.Density.IFCG17.exists_decided_factors
#print axioms Uniformity.Density.IFCG17.decidedSet_inter_stratum_mul_eq
#print axioms Uniformity.Density.IFCG17.stratDecCount_mul
