/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.Density.TypeOf

/-!
# Uniformity.Density.InertLeaf — the unramified leaf `(1, n)` at every degree

**CN-21** of `spec/CERTAIN_NODES_2026-08-14.md`: the generalization to all `n` of the landed
degree-2 instance `typeOf_inert_of_anisotropic` (`QuadCert.lean:400`). If the reduction of a
monic `f` of degree `n > 0` is irreducible over the residue field, then

  `typeOf f = ⟨{(1, n)}⟩`  —  one unramified factor of residue degree `n`.

## The argument (see `notes/CN_BATCH_D_2026-08-14.md` for the informal write-up)

Write `A = AdjoinRoot f = O[X]/(f)`, `k = ResidueField O`, `π` a uniformizer.

1. `f` is irreducible over `O` (`Monic.irreducible_of_irreducible_map`), so `monicFactors f = {f}`
   and the type is the single pair `efPair f`.
2. `A ⧸ 𝔪A ≅ k[X]/(f̄)` (`AdjoinRoot.quotEquivQuotMap`), a field because `k[X]` is a PID and `f̄`
   is irreducible; hence `𝔪A` is a **maximal** ideal of `A`
   (`isMaximal_map_maximalIdeal_adjoinRoot`).
3. Therefore every `z ∉ 𝔪A` is a **unit** of `A` (`isUnit_of_notMem_map_maximalIdeal`): it has an
   inverse modulo the maximal ideal `𝔪A`, so multiplication by `z` is surjective mod `𝔪 • A`, and
   Nakayama over the local ring `O` (`LinearMap.surjective_of_surjective_comp_mkQ`, legitimate
   because `A` is a *finite* `O`-module) upgrades that to surjectivity, giving `z * x = 1`.
4. Hence `n ∣ v(N z)` for every `z` (`natDegree_dvd_addVal_norm`), by strong induction on the
   valuation: a unit has norm a unit, i.e. valuation `0`; a non-unit is `π z'`, whose norm is
   `π ^ n · N z'` (`Algebra.norm_algebraMap`, `finrank O A = n`), dropping the valuation by
   exactly `n`.
5. `n` is itself a norm-valuation (landed `natDegree_mem_normValues`), so the gcd definition of
   the residue degree gives `inertiaDegOf f = n` (`inertiaDegOf_eq_of`) and
   `ramIndexOf f = n / n = 1`.

**On the hypotheses.** `[IsAdicComplete (maximalIdeal O) O]` is carried because the signature is a
frozen contract; the proof above never uses it. (Completeness is what makes `inertiaDegOf` *mean*
the residue degree — the trust-boundary discussion in `TypeOf.lean` — but the identity proved here
holds over any DVR.)

## Status

Sorry-free, axiom-free (Lean core only).
-/

set_option linter.style.longLine false
-- The contract signature (`spec/CERTAIN_NODES_2026-08-14.md`, CN-21) carries the full standing
-- bundle, including the completeness instance the proof does not consume.
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Uniformity.Density

open IsLocalRing Polynomial

-- `Ideal.Quotient.field` is not a global instance in mathlib; it is needed to see `O ⧸ 𝔪` (the
-- unfolded `ResidueField O` produced by `AdjoinRoot.quotEquivQuotMap`) as a field, hence
-- `(O ⧸ 𝔪)[X]` as a principal ideal ring.
attribute [local instance] Ideal.Quotient.field

section Inert

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

/-! ## 1. `𝔪·A` is a maximal ideal of `A = AdjoinRoot f` -/

/-- **`𝔪A` is maximal** when the reduction of `f` is irreducible: `A ⧸ 𝔪A ≅ k[X]/(f̄)`
(`AdjoinRoot.quotEquivQuotMap`) and the right-hand side is a field. -/
theorem isMaximal_map_maximalIdeal_adjoinRoot {f : Polynomial O}
    (h : Irreducible (f.map (residue O))) :
    (Ideal.map (algebraMap O (AdjoinRoot f)) (maximalIdeal O)).IsMaximal := by
  have hmaxB : (Ideal.span {Polynomial.map (Ideal.Quotient.mk (maximalIdeal O)) f}).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible h
  have hfieldB : IsField ((O ⧸ maximalIdeal O)[X] ⧸
      Ideal.span {Polynomial.map (Ideal.Quotient.mk (maximalIdeal O)) f}) :=
    (Ideal.Quotient.maximal_ideal_iff_isField_quotient _).1 hmaxB
  refine Ideal.Quotient.maximal_of_isField _ ?_
  exact MulEquiv.isField hfieldB
    (AdjoinRoot.quotEquivQuotMap f (maximalIdeal O)).toRingEquiv.toMulEquiv

/-! ## 2. Off `𝔪·A` everything is a unit -/

/-- **The unit lemma.** If the reduction of the monic `f` is irreducible then every element of
`A = AdjoinRoot f` outside `𝔪A` is a unit.

`𝔪A` is maximal (§1), so `z` has an inverse `w` modulo `𝔪A`; hence multiplication by `z` is
surjective modulo `𝔪 • A`. Since `A` is a finite `O`-module and `𝔪` lies in the Jacobson radical
of the local ring `O`, Nakayama removes the "modulo": multiplication by `z` is surjective, so
`z * x = 1` for some `x`. -/
theorem isUnit_of_notMem_map_maximalIdeal {f : Polynomial O} (hf : f.Monic)
    (h : Irreducible (f.map (residue O))) {z : AdjoinRoot f}
    (hz : z ∉ Ideal.map (algebraMap O (AdjoinRoot f)) (maximalIdeal O)) : IsUnit z := by
  classical
  haveI hfin : Module.Finite O (AdjoinRoot f) := (AdjoinRoot.powerBasis' hf).finite
  haveI hmax := isMaximal_map_maximalIdeal_adjoinRoot (f := f) h
  -- an inverse modulo the maximal ideal `𝔪A`
  obtain ⟨w, i, hi, hwz⟩ := hmax.exists_inv hz
  have hw : z * w - 1 ∈ Ideal.map (algebraMap O (AdjoinRoot f)) (maximalIdeal O) := by
    have : z * w - 1 = -i := by linear_combination hwz
    rw [this, Ideal.neg_mem_iff]
    exact hi
  -- multiplication by `z` is surjective modulo `𝔪 • A`, hence (Nakayama) surjective
  have hsurj : Function.Surjective (LinearMap.mulLeft O z) := by
    refine LinearMap.surjective_of_surjective_comp_mkQ (LinearMap.mulLeft O z) (maximalIdeal O)
      (IsLocalRing.maximalIdeal_le_jacobson ⊥) ?_
    intro y
    obtain ⟨a, rfl⟩ := Submodule.mkQ_surjective _ y
    refine ⟨w * a, ?_⟩
    show Submodule.Quotient.mk (z * (w * a)) = Submodule.Quotient.mk a
    rw [Submodule.Quotient.eq, Ideal.smul_top_eq_map]
    show z * (w * a) - a ∈ Ideal.map (algebraMap O (AdjoinRoot f)) (maximalIdeal O)
    have heq : z * (w * a) - a = (z * w - 1) * a := by ring
    rw [heq]
    exact Ideal.mul_mem_right _ _ hw
  obtain ⟨x, hx⟩ := hsurj 1
  exact IsUnit.of_mul_eq_one x (by simpa using hx)

/-! ## 3. Every norm valuation is a multiple of `n` -/

/-- **The divisibility.** With `f` monic of degree `n > 0` and irreducible reduction, every
valuation of a norm from `A = AdjoinRoot f` is a multiple of `n`.

Strong induction on the valuation `k`: if `z` is a unit so is `N z`, whence `k = 0`; otherwise
`z ∈ 𝔪A` (the unit lemma), so `z = π z'` and `N z = π ^ n · N z'`, which drops the valuation by
exactly `n`. -/
theorem natDegree_dvd_addVal_norm {f : Polynomial O} (hf : f.Monic) (hd : 0 < f.natDegree)
    (h : Irreducible (f.map (residue O))) {π : O} (hπ : Irreducible π) :
    ∀ k : ℕ, ∀ z : AdjoinRoot f,
      IsDiscreteValuationRing.addVal O (Algebra.norm O z) = (k : ℕ∞) → f.natDegree ∣ k := by
  haveI hfin : Module.Finite O (AdjoinRoot f) := (AdjoinRoot.powerBasis' hf).finite
  haveI hfree : Module.Free O (AdjoinRoot f) :=
    Module.Free.of_basis (AdjoinRoot.powerBasis' hf).basis
  have hrank : Module.finrank O (AdjoinRoot f) = f.natDegree := by
    rw [(AdjoinRoot.powerBasis' hf).finrank]; rfl
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro z hk
    by_cases hu : IsUnit z
    · -- a unit has unit norm, so valuation `0`
      have hnu : IsUnit (Algebra.norm O z) := hu.map (Algebra.norm O)
      have hz0 : IsDiscreteValuationRing.addVal O (Algebra.norm O z) = 0 := by
        rw [← hnu.unit_spec]; exact IsDiscreteValuationRing.addVal_eq_zero_of_unit _
      rw [hk] at hz0
      have hk0 : k = 0 := by exact_mod_cast hz0
      simp [hk0]
    · -- a non-unit lies in `𝔪A = π A`
      have hmem : z ∈ Ideal.map (algebraMap O (AdjoinRoot f)) (maximalIdeal O) := by
        by_contra hnot
        exact hu (isUnit_of_notMem_map_maximalIdeal hf h hnot)
      rw [hπ.maximalIdeal_eq, Ideal.map_span, Set.image_singleton] at hmem
      obtain ⟨z', rfl⟩ := Ideal.mem_span_singleton.1 hmem
      have hnorm : Algebra.norm O (algebraMap O (AdjoinRoot f) π * z')
          = π ^ f.natDegree * Algebra.norm O z' := by
        rw [map_mul, Algebra.norm_algebraMap, hrank]
      rw [hnorm, AddValuation.map_mul, hπ.addVal_pow] at hk
      have htne : IsDiscreteValuationRing.addVal O (Algebra.norm O z') ≠ ⊤ := by
        intro htop
        rw [htop] at hk
        simp at hk
      obtain ⟨m, hm⟩ := WithTop.ne_top_iff_exists.1 htne
      rw [← hm] at hk
      have hcast : ((f.natDegree + m : ℕ) : ℕ∞) = ((k : ℕ) : ℕ∞) := by push_cast; exact hk
      have hsum : f.natDegree + m = k := by exact_mod_cast hcast
      have hdvd : f.natDegree ∣ m := ih m (by omega) z' hm.symm
      have : f.natDegree ∣ f.natDegree + m := dvd_add (dvd_refl _) hdvd
      rwa [hsum] at this

/-! ## 4. The contract -/

/-- **CN-21 — the unramified leaf at every degree.** A monic `f` of positive degree whose
reduction is irreducible over the residue field has splitting type `⟨{(1, deg f)}⟩`: a single
unramified factor of residue degree `deg f`.

At `n = 2` this is the landed `typeOf_inert_of_anisotropic` (there `Anisotropic a` says exactly
that the reduction has no residual root, i.e. is irreducible). -/
theorem typeOf_inert_of_irreducible_map {O : Type*} [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [IsAdicComplete (maximalIdeal O) O] {f : Polynomial O}
    (hf : f.Monic) (hd : 0 < f.natDegree) (h : Irreducible (f.map (residue O))) :
    typeOf f = ⟨{(1, f.natDegree)}⟩ := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible O
  -- `f` is irreducible over `O`, so it is its own monic factorization
  have hirr : Irreducible f := hf.irreducible_of_irreducible_map (residue O) f h
  have hF : IsMonicFactorization f {f} :=
    ⟨by intro g hg; rw [Multiset.mem_singleton.1 hg]; exact ⟨hf, hirr⟩, by simp⟩
  -- the residue degree is the full degree
  have hinf : inertiaDegOf f = f.natDegree := by
    refine inertiaDegOf_eq_of (natDegree_mem_normValues hf hd hπ) ?_
    rintro m ⟨-, x, -, hx⟩
    exact natDegree_dvd_addVal_norm hf hd h hπ m x hx
  ext
  rw [typeOf_data, monicFactors_eq hF]
  simp [efPair, ramIndexOf, hinf, Nat.div_self hd]

end Inert

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.isMaximal_map_maximalIdeal_adjoinRoot
#print axioms Uniformity.Density.isUnit_of_notMem_map_maximalIdeal
#print axioms Uniformity.Density.natDegree_dvd_addVal_norm
#print axioms Uniformity.Density.typeOf_inert_of_irreducible_map

end AxCheck

end Uniformity.Density
