/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib.RingTheory.DedekindDomain.Basic
import Uniformity.Density.TypeOf
import Uniformity.Quarry.RamificationInertiaLocal

/-!
# Uniformity.Density.TypeOfFaithful — HYP.01 on the monogenic-maximal locus

**HYP.01 (`typeOf` faithfulness)**, the `[CORE-SET]` row of `spec/HYPOTHESIS_LEDGER.md:63`:
the gcd-defined `(e, f)` pair of `Uniformity/Density/TypeOf.lean` is the *classical*
ramification-index / residue-degree pair. This file proves that identification on the
**monogenic-maximal locus**.

## What is proved

For `O` a DVR and `g ∈ O[X]` monic of positive degree, write `A = AdjoinRoot g = O[x]/(g)`.
The two hypotheses `[IsDomain A] [IsDiscreteValuationRing A]` say exactly that the order
`O[x]/(g)` **is already the maximal order**: a Noetherian local domain of dimension one is a
DVR iff it is integrally closed, so `A = integralClosure O (Frac A)`. Under that hypothesis:

* `inertiaDegOf_eq_inertiaDeg'` — the gcd `inertiaDegOf g` equals
  `(IsLocalRing.maximalIdeal A).inertiaDeg' O`, the residue-field degree;
* `ramIndexOf_eq_ramificationIdx'` — `ramIndexOf g = deg g / inertiaDegOf g` equals
  `(IsLocalRing.maximalIdeal A).ramificationIdx' O`;
* `typeOf_eq_classical_of_isDiscreteValuationRing` — for irreducible `g`, therefore,
  `typeOf g` is the singleton `⟨{(ramificationIdx', inertiaDeg')}⟩`.

## What is NOT proved

The **non-maximal-order case**: if `A` is a proper suborder of the integral closure the
argument below breaks (the normal form `x = u · ϖ ^ j` is unavailable, since `A` has no
uniformizer). That is exactly the erratum recorded at `spec/EFF-GENHN-s1of2.md:1105` — "the
false part is exactly '`R` a complete DVR'". Nothing here licenses the classical reading of
`typeOf` off this locus.

## No completeness is used

Note that **no completeness hypothesis on `O`** enters: the identity holds over any DVR, and
the proof is a normal-form computation with the norm form of the valuation plus the
fundamental identity `e · f = [A : O]`. Completeness is what makes the DVR hypothesis on
`AdjoinRoot g` *checkable* in our applications (Hensel/Montes certificates), not what makes
the identity true.

## The argument

Pick `π` irreducible in `O` and `ϖ` irreducible in `A`, and let `m` be the exponent in
`algebraMap O A π = u · ϖ ^ m`. Computing `v (N (algebraMap O A π))` two ways — once as
`v (π ^ n) = n`, once through the normal form as `m · v (N ϖ)` — gives `n = m · f₀` with
`f₀ := v (N ϖ)`. The same normal form shows `f₀` divides every norm-valuation and is one, so
`inertiaDegOf g = f₀`. Meanwhile `π A = ϖ ^ m A` identifies `m` with the classical
ramification index (`Ideal.ramificationIdx_spec`), and the fundamental identity
`e · f = finrank O A = n` then forces `f = f₀`.

## Status

Sorry-free, axiom-free (Lean core only).
-/

set_option linter.style.longLine false
-- The helper lemmas share one `variable` bundle; not every one consumes every instance.
set_option linter.unusedSectionVars false

namespace Uniformity.Density

open IsLocalRing Polynomial

section Helpers

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {g : Polynomial O}

/-! ## 0. The standing instances on `A = AdjoinRoot g` -/

/-- For `g` of positive degree the structure map `O → O[x]/(g)` is injective. -/
theorem injective_algebraMap_adjoinRoot (hd : 0 < g.natDegree) :
    Function.Injective (algebraMap O (AdjoinRoot g)) := by
  rw [AdjoinRoot.algebraMap_eq]
  exact AdjoinRoot.of.injective_of_degree_ne_zero
    (ne_of_gt (natDegree_pos_iff_degree_pos.1 hd))

/-- `O` acts faithfully on `AdjoinRoot g` when `deg g > 0`. -/
theorem faithfulSMul_adjoinRoot (hd : 0 < g.natDegree) : FaithfulSMul O (AdjoinRoot g) :=
  (faithfulSMul_iff_algebraMap_injective O (AdjoinRoot g)).2 (injective_algebraMap_adjoinRoot hd)

/-- `AdjoinRoot g` is free of rank `deg g` over `O` for monic `g`. -/
theorem finrank_adjoinRoot (hg : g.Monic) : Module.finrank O (AdjoinRoot g) = g.natDegree := by
  rw [(AdjoinRoot.powerBasis' hg).finrank]; rfl

/-! ## 1. Valuations of norms out of `A` -/

/-- Norms of nonzero elements are nonzero, so their valuations are finite. -/
theorem addVal_norm_ne_top (hg : g.Monic) [IsDomain (AdjoinRoot g)] {x : AdjoinRoot g}
    (hx : x ≠ 0) : IsDiscreteValuationRing.addVal O (Algebra.norm O x) ≠ ⊤ := by
  haveI : Module.Finite O (AdjoinRoot g) := (AdjoinRoot.powerBasis' hg).finite
  haveI : Module.Free O (AdjoinRoot g) :=
    Module.Free.of_basis (AdjoinRoot.powerBasis' hg).basis
  rw [ne_eq, IsDiscreteValuationRing.addVal_eq_top_iff]
  exact Algebra.norm_ne_zero_iff.2 hx

/-- **The normal-form computation.** If `A` is a DVR with uniformizer `ϖ`, every nonzero `x`
is `u · ϖ ^ j`, and the norm valuation of `x` is `j` times that of `ϖ`. -/
theorem exists_addVal_norm_eq_nsmul [IsDomain (AdjoinRoot g)]
    [IsDiscreteValuationRing (AdjoinRoot g)] {ϖ : AdjoinRoot g} (hϖ : Irreducible ϖ)
    {x : AdjoinRoot g} (hx : x ≠ 0) :
    ∃ j : ℕ, IsDiscreteValuationRing.addVal O (Algebra.norm O x)
      = j • IsDiscreteValuationRing.addVal O (Algebra.norm O ϖ) := by
  obtain ⟨j, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hx hϖ
  refine ⟨j, ?_⟩
  rw [map_mul, map_pow, IsDiscreteValuationRing.addVal_mul,
    IsDiscreteValuationRing.addVal_pow,
    IsDiscreteValuationRing.addVal_eq_zero_iff.2 (u.isUnit.map (Algebra.norm O)), zero_add]

/-! ## 2. The exponent `m` with `π A = 𝔪_A ^ m` -/

/-- **The ramification data.** On the monogenic-maximal locus there is an `m > 0` with
`𝔪_O · A = 𝔪_A ^ m` and `m · inertiaDegOf g = deg g`: the exponent of the uniformizer of `O`
in the uniformizer of `A`, read off both as an ideal exponent and as a degree factor. -/
theorem exists_ramification_data (hg : g.Monic) (hd : 0 < g.natDegree)
    [IsDomain (AdjoinRoot g)] [IsDiscreteValuationRing (AdjoinRoot g)] :
    ∃ m : ℕ, 0 < m ∧
      Ideal.map (algebraMap O (AdjoinRoot g)) (maximalIdeal O)
        = maximalIdeal (AdjoinRoot g) ^ m ∧
      m * inertiaDegOf g = g.natDegree := by
  haveI : Module.Finite O (AdjoinRoot g) := (AdjoinRoot.powerBasis' hg).finite
  haveI : Module.Free O (AdjoinRoot g) :=
    Module.Free.of_basis (AdjoinRoot.powerBasis' hg).basis
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible O
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible (AdjoinRoot g)
  -- `f₀ = v (N ϖ)`, finite because `N ϖ ≠ 0`
  obtain ⟨f₀, hf₀⟩ := ENat.ne_top_iff_exists.1 (addVal_norm_ne_top hg hϖ.ne_zero)
  -- the normal form of the image of `π`
  have hπA : (algebraMap O (AdjoinRoot g)) π ≠ 0 := fun h =>
    hπ.ne_zero (injective_algebraMap_adjoinRoot hd (by simpa using h))
  obtain ⟨m, u, hmu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hπA hϖ
  -- (a) `N (algebraMap O A π) = π ^ n`, of valuation `n`
  have ha : IsDiscreteValuationRing.addVal O (Algebra.norm O ((algebraMap O (AdjoinRoot g)) π))
      = (g.natDegree : ℕ∞) := by
    rw [Algebra.norm_algebraMap, finrank_adjoinRoot hg, hπ.addVal_pow]
  -- (b) the same valuation, read off the normal form
  have hb : IsDiscreteValuationRing.addVal O (Algebra.norm O ((algebraMap O (AdjoinRoot g)) π))
      = m • ((f₀ : ℕ) : ℕ∞) := by
    rw [hmu, map_mul, map_pow, IsDiscreteValuationRing.addVal_mul,
      IsDiscreteValuationRing.addVal_pow,
      IsDiscreteValuationRing.addVal_eq_zero_iff.2 (u.isUnit.map (Algebra.norm O)), zero_add,
      ← hf₀]
  have hnat : g.natDegree = m * f₀ := by
    have hc : ((g.natDegree : ℕ) : ℕ∞) = ((m * f₀ : ℕ) : ℕ∞) := by
      rw [← ha, hb, nsmul_eq_mul, Nat.cast_mul]
    exact_mod_cast hc
  have hmpos : 0 < m := by
    rcases Nat.eq_zero_or_pos m with rfl | h
    · rw [zero_mul] at hnat; omega
    · exact h
  have hf₀pos : 0 < f₀ := by
    rcases Nat.eq_zero_or_pos f₀ with rfl | h
    · rw [mul_zero] at hnat; omega
    · exact h
  -- the gcd of the norm-valuations is `f₀`
  have hgcd : inertiaDegOf g = f₀ := by
    refine inertiaDegOf_eq_of ⟨hf₀pos, ϖ, hϖ.ne_zero, hf₀.symm⟩ ?_
    rintro k ⟨-, x, hx0, hxk⟩
    obtain ⟨j, hj⟩ := exists_addVal_norm_eq_nsmul hϖ hx0
    have hc : ((k : ℕ) : ℕ∞) = ((j * f₀ : ℕ) : ℕ∞) := by
      rw [← hxk, hj, ← hf₀, nsmul_eq_mul, Nat.cast_mul]
    have hk : k = j * f₀ := by exact_mod_cast hc
    exact ⟨j, by rw [hk]; ring⟩
  refine ⟨m, hmpos, ?_, by rw [hgcd]; exact hnat.symm⟩
  rw [hπ.maximalIdeal_eq, Ideal.map_span, Set.image_singleton, hmu, hϖ.maximalIdeal_eq,
    Ideal.span_singleton_pow, Ideal.span_singleton_mul_left_unit u.isUnit]

/-- **`m` is the classical ramification index.** The ideal identity `𝔪_O · A = 𝔪_A ^ m` pins
`ramificationIdx'` down, via `Ideal.ramificationIdx_spec` and the reconciliation
`Ideal.ramificationIdx_eq_ramificationIdx'`. -/
theorem ramificationIdx'_eq_of_map_maximalIdeal_eq_pow (hg : g.Monic) (hd : 0 < g.natDegree)
    [IsDomain (AdjoinRoot g)] [IsDiscreteValuationRing (AdjoinRoot g)] {m : ℕ}
    (hmap : Ideal.map (algebraMap O (AdjoinRoot g)) (maximalIdeal O)
      = maximalIdeal (AdjoinRoot g) ^ m) :
    (maximalIdeal (AdjoinRoot g)).ramificationIdx' O = m := by
  haveI : Module.Finite O (AdjoinRoot g) := (AdjoinRoot.powerBasis' hg).finite
  haveI : FaithfulSMul O (AdjoinRoot g) := faithfulSMul_adjoinRoot hd
  haveI : Module.IsTorsionFree O (AdjoinRoot g) := Module.isTorsionFree_iff_faithfulSMul.2 ‹_›
  have hp0 : maximalIdeal O ≠ ⊥ := IsDiscreteValuationRing.not_a_field O
  have hsingle : Ideal.primesOver (maximalIdeal O) (AdjoinRoot g)
      = {maximalIdeal (AdjoinRoot g)} := IsLocalRing.primesOver_eq (AdjoinRoot g) hp0
  have hmem : maximalIdeal (AdjoinRoot g) ∈
      (maximalIdeal O).primesOver (AdjoinRoot g) := by rw [hsingle]; rfl
  haveI : (maximalIdeal (AdjoinRoot g)).LiesOver (maximalIdeal O) := hmem.2
  rw [← Ideal.ramificationIdx_eq_ramificationIdx' (maximalIdeal O)
    (maximalIdeal (AdjoinRoot g)) hp0]
  refine Ideal.ramificationIdx_spec (le_of_eq hmap) ?_
  rw [hmap]
  intro hle
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible (AdjoinRoot g)
  rw [hϖ.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.span_singleton_pow,
    Ideal.span_singleton_le_span_singleton, pow_succ] at hle
  have h1 : ϖ ^ m * ϖ ∣ ϖ ^ m * 1 := by rw [mul_one]; exact hle
  exact hϖ.not_isUnit (isUnit_of_dvd_one
    ((mul_dvd_mul_iff_left (pow_ne_zero m hϖ.ne_zero)).1 h1))

end Helpers

/-! ## 3. The contract -/

/-- **HYP.01, residue-degree half.** On the monogenic-maximal locus the gcd-defined
`inertiaDegOf g` of `TypeOf.lean` is the classical inertia degree of the maximal ideal of
`AdjoinRoot g` over `O`. -/
theorem inertiaDegOf_eq_inertiaDeg' {O : Type*} [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] {g : Polynomial O} (hg : g.Monic) (hd : 0 < g.natDegree)
    [IsDomain (AdjoinRoot g)] [IsDiscreteValuationRing (AdjoinRoot g)] :
    inertiaDegOf g = (IsLocalRing.maximalIdeal (AdjoinRoot g)).inertiaDeg' O := by
  haveI : Module.Finite O (AdjoinRoot g) := (AdjoinRoot.powerBasis' hg).finite
  haveI : FaithfulSMul O (AdjoinRoot g) := faithfulSMul_adjoinRoot hd
  obtain ⟨m, hmpos, hmap, hmul⟩ := exists_ramification_data hg hd
  have he : (maximalIdeal (AdjoinRoot g)).ramificationIdx' O = m :=
    ramificationIdx'_eq_of_map_maximalIdeal_eq_pow hg hd hmap
  have hfund := Ideal.ramificationIdx_mul_inertiaDeg_eq_finrank_of_isLocalRing (AdjoinRoot g)
    (IsDiscreteValuationRing.not_a_field O)
  rw [he, finrank_adjoinRoot hg] at hfund
  exact Nat.eq_of_mul_eq_mul_left hmpos (hmul.trans hfund.symm)

/-- **HYP.01, ramification half.** On the monogenic-maximal locus `ramIndexOf g` is the
classical ramification index. -/
theorem ramIndexOf_eq_ramificationIdx' {O : Type*} [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] {g : Polynomial O} (hg : g.Monic) (hd : 0 < g.natDegree)
    [IsDomain (AdjoinRoot g)] [IsDiscreteValuationRing (AdjoinRoot g)] :
    ramIndexOf g = (IsLocalRing.maximalIdeal (AdjoinRoot g)).ramificationIdx' O := by
  haveI : Module.Finite O (AdjoinRoot g) := (AdjoinRoot.powerBasis' hg).finite
  haveI : FaithfulSMul O (AdjoinRoot g) := faithfulSMul_adjoinRoot hd
  have hfund := Ideal.ramificationIdx_mul_inertiaDeg_eq_finrank_of_isLocalRing (AdjoinRoot g)
    (IsDiscreteValuationRing.not_a_field O)
  rw [finrank_adjoinRoot hg] at hfund
  have hef : ramIndexOf g * inertiaDegOf g = g.natDegree := ramIndexOf_mul_inertiaDegOf hg hd
  rw [inertiaDegOf_eq_inertiaDeg' hg hd] at hef
  exact Nat.eq_of_mul_eq_mul_right
    (Ideal.inertiaDeg'_pos (maximalIdeal (AdjoinRoot g)) O) (hef.trans hfund.symm)

/-- **HYP.01 on the monogenic-maximal locus.** For irreducible monic `g` of positive degree
whose order `O[x]/(g)` is already maximal, `typeOf g` is the classical singleton
`⟨{(e, f)}⟩`. -/
theorem typeOf_eq_classical_of_isDiscreteValuationRing {O : Type*} [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] {g : Polynomial O} (hg : g.Monic) (hd : 0 < g.natDegree)
    (hirr : Irreducible g) [IsDomain (AdjoinRoot g)] [IsDiscreteValuationRing (AdjoinRoot g)] :
    typeOf g = ⟨{((IsLocalRing.maximalIdeal (AdjoinRoot g)).ramificationIdx' O,
      (IsLocalRing.maximalIdeal (AdjoinRoot g)).inertiaDeg' O)}⟩ := by
  have hF : IsMonicFactorization g {g} :=
    ⟨by intro h hh; rw [Multiset.mem_singleton.1 hh]; exact ⟨hg, hirr⟩, by simp⟩
  ext
  rw [typeOf_data, monicFactors_eq hF]
  simp [efPair, inertiaDegOf_eq_inertiaDeg' hg hd, ramIndexOf_eq_ramificationIdx' hg hd]

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.injective_algebraMap_adjoinRoot
#print axioms Uniformity.Density.faithfulSMul_adjoinRoot
#print axioms Uniformity.Density.finrank_adjoinRoot
#print axioms Uniformity.Density.addVal_norm_ne_top
#print axioms Uniformity.Density.exists_addVal_norm_eq_nsmul
#print axioms Uniformity.Density.exists_ramification_data
#print axioms Uniformity.Density.ramificationIdx'_eq_of_map_maximalIdeal_eq_pow
#print axioms Uniformity.Density.inertiaDegOf_eq_inertiaDeg'
#print axioms Uniformity.Density.ramIndexOf_eq_ramificationIdx'
#print axioms Uniformity.Density.typeOf_eq_classical_of_isDiscreteValuationRing

end AxCheck

end Uniformity.Density
