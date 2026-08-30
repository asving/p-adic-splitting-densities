/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import Uniformity.ChapI.IFCG41

/-!
# Uniformity.ChapI.IFCG42 — [CSL 2026-08-30] the q-power fiber law and the Hensel leg:
the Smith-normal-form index law over the DVR, the depth-`v` Sylvester kernel count,
the neighborhood fiber law `#fiber = q^v`, and the discharge of `LiftsFactor`

Stage CSL of the cone census (consumes RDC = `IFCG41`).  RDC reduced the `m ≥ 4` split
defect leg to `CollisionLaw`/`StrayLaw` plus the named remainders (i) the q-power fiber
law and (ii) the Hensel existence leg `LiftsFactor`.  This file lands the quantitative
core of (i) and discharges (ii):

* **§1 ★★ THE INDEX-DETERMINANT LAW over the DVR** (`natCard_quotient_range_smith`):
  for an injective endomorphism `φ` of a finite free `O`-module with
  `det φ ~ π^w`, the cokernel has exactly `q^w` elements (`q = residueCard O`).
  Mechanism: mathlib's Smith normal form over the PID (`Submodule.quotientEquivPiSpan`)
  + the corpus's `card_res`.  The Igusa-genre counting engine, uniform in everything.
* **§2 the depth-`v` Sylvester counts**: mathlib's `sylvesterMap` (whose matrix is the
  Sylvester matrix, hence determinant = the pinned-size resultant) is injective when
  the resultant is nonzero; its cokernel has `q^w` elements (`w` = the resultant
  valuation); and mod `π^v` (any `w ≤ v`) its kernel has EXACTLY `q^w` elements.
* **§3 ★★ THE NEIGHBORHOOD FIBER LAW** (`natCard_pairNbhd`): at exact resultant depth
  `v` with `2v+1 ≤ N`, the set of level-`N` class pairs with the same `mulClass`
  product as `(a₁, a₂)` and factors congruent to `(a₁, a₂)` mod `π^{v+1}` has EXACTLY
  `q^v` members — THE q-POWER FIBER LAW (both directions at once: RDC's gap engine is
  the separation/injectivity leg; the Sylvester kernel parametrization is the
  construction leg).
* **§4 ★★ THE HENSEL LEG DISCHARGED** (`liftsFactor_of_not_dvd_resultant`): for
  `2v+1 ≤ N` and `π^{v+1} ∤ Res`, RDC's `LiftsFactor π v N a₁ a₂` HOLDS — by a
  depth-`v` Newton iteration (fresh normalized Bezout witness from the resultant at
  every stage, exact linear-term kill, quadratic error at doubled level, limits via
  the corpus's adic-limit engine).  Corollary `decidedAt_mulClass_of_not_dvd_resultant`:
  RDC's decidedness-transfer criterion fires with the Hensel leg PROVED.

## THE HONEST FENCE

The census laws (`CollisionLaw`/`StrayLaw`) are NOT fired here: with this file the
per-cluster fiber size is pinned at `q^v` exactly, but the census still needs the
depth-stratum root counts (the level-`(v+1)` digit-box measure of the depth-`v`
strata) and the drainage premise (shifted-level decidedness of the fiber members).
See §5 for the precise named remainder.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

noncomputable section

namespace Uniformity.Density.IFCG42

open IsLocalRing Polynomial
open Uniformity.Density.Induction
open Uniformity.Density.IFCG41 (LiftsFactor exists_bezout_of_not_dvd_resultant
  decidedAt_mulClass_of_liftsFactor mulClass_fiber_gap mixDepth classRes classRes_proj
  mk_pow_dvd_mk_iff mixDepth_le mixDepth_dvd le_mixDepth)

/-! ## §0 — supply -/

section Supply

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

/-- Powers of an irreducible are associated only when the exponents agree. -/
private theorem pow_eq_of_associated_pow {π : O} (hπ : Irreducible π) {a b : ℕ}
    (h : Associated (π ^ a) (π ^ b)) : a = b := by
  rcases le_total a b with hab | hab
  · obtain ⟨u, hu⟩ := h
    have hsplit : π ^ b = π ^ a * π ^ (b - a) := by rw [← pow_add]; congr 1; omega
    rw [hsplit] at hu
    have hcan : (u : O) = π ^ (b - a) :=
      mul_left_cancel₀ (pow_ne_zero a hπ.ne_zero) hu
    have hunit : IsUnit (π ^ (b - a)) := hcan ▸ u.isUnit
    rcases Nat.eq_zero_or_pos (b - a) with h0 | hpos'
    · omega
    · exact absurd ((isUnit_pow_iff (Nat.pos_iff_ne_zero.mp hpos')).mp hunit)
        hπ.not_isUnit
  · obtain ⟨u, hu⟩ := h.symm
    have hsplit : π ^ a = π ^ b * π ^ (a - b) := by rw [← pow_add]; congr 1; omega
    rw [hsplit] at hu
    have hcan : (u : O) = π ^ (a - b) :=
      mul_left_cancel₀ (pow_ne_zero b hπ.ne_zero) hu
    have hunit : IsUnit (π ^ (a - b)) := hcan ▸ u.isUnit
    rcases Nat.eq_zero_or_pos (a - b) with h0 | hpos'
    · omega
    · exact absurd ((isUnit_pow_iff (Nat.pos_iff_ne_zero.mp hpos')).mp hunit)
        hπ.not_isUnit

/-- `#(O ⧸ (x)) = q^w` when `x ~ π^w` (the DVR quotient count, via `card_res`). -/
private theorem card_quot_span_associated_pow [Finite (ResidueField O)] {π : O}
    (hπ : Irreducible π) {x : O} {w : ℕ} (hx : Associated x (π ^ w)) :
    Nat.card (O ⧸ Ideal.span {x}) = residueCard O ^ w := by
  have hspan : Ideal.span {x} = (maximalIdeal O) ^ w := by
    rw [hπ.maximalIdeal_eq, Ideal.span_singleton_pow]
    exact Ideal.span_singleton_eq_span_singleton.mpr hx
  rw [Nat.card_congr (Ideal.quotEquivOfEq hspan).toEquiv]
  exact card_res w

end Supply

/-! ## §1 — ★★ THE INDEX-DETERMINANT LAW over the DVR (the Smith-normal-form engine) -/

section IndexDet

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)]

/-- ★★ **THE INDEX-DETERMINANT LAW**: an injective endomorphism `φ` of a finite free
`O`-module with `det φ ~ π^w` has cokernel of size EXACTLY `q^w`.  Mechanism: Smith
normal form over the PID (`Submodule.quotientEquivPiSpan`) turns the cokernel into
`Π O ⧸ (aᵢ)`; the determinant is associated to `Π aᵢ` through the diagonal basis; the
corpus's `card_res` counts each cyclic factor. -/
theorem natCard_quotient_range_smith {M : Type*} [AddCommGroup M] [Module O M]
    [Module.Free O M] [Module.Finite O M] {π : O} (hπ : Irreducible π)
    {φ : M →ₗ[O] M} (hinj : Function.Injective φ) {w : ℕ}
    (hdet : Associated (LinearMap.det φ) (π ^ w)) :
    Nat.card (M ⧸ LinearMap.range φ) = residueCard O ^ w := by
  classical
  set N : Submodule O M := LinearMap.range φ with hN
  let e : M ≃ₗ[O] N := LinearEquiv.ofInjective φ hinj
  have hrank : Module.finrank O N = Module.finrank O M := e.symm.finrank_eq
  haveI : Fintype (Module.Free.ChooseBasisIndex O M) := Fintype.ofFinite _
  let b : Module.Basis (Module.Free.ChooseBasisIndex O M) O M :=
    Module.Free.chooseBasis O M
  set a := Submodule.smithNormalFormCoeffs b hrank with ha
  set b' := Submodule.smithNormalFormTopBasis b hrank with hb'
  set ab := Submodule.smithNormalFormBotBasis b hrank with hab
  have ab_eq := Submodule.smithNormalFormBotBasis_def b hrank
  -- count the quotient through the Smith pi decomposition
  have hcard : Nat.card (M ⧸ N)
      = ∏ i, Nat.card (O ⧸ Ideal.span ({a i} : Set O)) := by
    rw [Nat.card_congr (Submodule.quotientEquivPiSpan N b hrank).toEquiv, Nat.card_pi]
  -- factor each Smith coefficient in the DVR
  have hane : ∀ i, a i ≠ 0 := fun i => Submodule.smithNormalFormCoeffs_ne_zero b hrank i
  choose wa ua hua using fun i =>
    IsDiscreteValuationRing.eq_unit_mul_pow_irreducible (hane i) hπ
  have hassoc : ∀ i, Associated (a i) (π ^ wa i) := fun i =>
    ⟨(ua i)⁻¹, by rw [hua i, mul_comm ((ua i : O)), mul_assoc, Units.mul_inv, mul_one]⟩
  have hcards : ∀ i, Nat.card (O ⧸ Ideal.span ({a i} : Set O)) = residueCard O ^ wa i :=
    fun i => card_quot_span_associated_pow hπ (hassoc i)
  -- the determinant side: det φ ~ ∏ a i
  have hφeq : φ = N.subtype ∘ₗ (e : M →ₗ[O] N) := by ext x; rfl
  let e' : M ≃ₗ[O] N := b'.equiv ab (Equiv.refl _)
  have hdet2 : Associated (LinearMap.det (N.subtype ∘ₗ (e : M →ₗ[O] N)))
      (LinearMap.det (N.subtype ∘ₗ (e' : M →ₗ[O] N))) :=
    LinearMap.associated_det_comp_equiv _ _ _
  have hdiag : LinearMap.det (N.subtype ∘ₗ (e' : M →ₗ[O] N)) = ∏ i, a i := by
    have hmat : LinearMap.toMatrix b' b' (N.subtype ∘ₗ (e' : M →ₗ[O] N))
        = Matrix.diagonal a := by
      ext i j
      have h1 : (N.subtype ∘ₗ (e' : M →ₗ[O] N)) (b' j) = a j • b' j := by
        have h2 : e' (b' j) = ab j := Module.Basis.equiv_apply b' j ab (Equiv.refl _)
        simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, h2, Submodule.coe_subtype]
        exact ab_eq j
      rw [LinearMap.toMatrix_apply, h1, map_smul, Module.Basis.repr_self,
        Finsupp.smul_single, smul_eq_mul, mul_one]
      by_cases hij : i = j
      · rw [hij, Matrix.diagonal_apply_eq, Finsupp.single_eq_same]
      · rw [Matrix.diagonal_apply_ne _ hij, Finsupp.single_eq_of_ne hij]
    rw [← LinearMap.det_toMatrix b', hmat, Matrix.det_diagonal]
  have hprodform : ∏ i, a i = (∏ i, (ua i : O)) * π ^ (∑ i, wa i) := by
    rw [Finset.prod_congr rfl (fun i _ => hua i), Finset.prod_mul_distrib,
      Finset.prod_pow_eq_pow_sum]
  -- the exponent identification
  have hchain : Associated (π ^ (∑ i, wa i)) (π ^ w) := by
    have hU : IsUnit (∏ i, (ua i : O)) := by
      refine Finset.prod_induction _ IsUnit (fun x y hx hy => hx.mul hy) isUnit_one ?_
      exact fun i _ => (ua i).isUnit
    have h3 : Associated (π ^ (∑ i, wa i)) (∏ i, a i) := by
      rw [hprodform]
      exact ⟨hU.unit, by rw [IsUnit.unit_spec, mul_comm]⟩
    exact h3.trans ((hdiag ▸ hdet2.symm).trans (hφeq ▸ hdet))
  have hw : (∑ i, wa i) = w := pow_eq_of_associated_pow hπ hchain
  rw [hcard, Finset.prod_congr rfl (fun i _ => hcards i), Finset.prod_pow_eq_pow_sum, hw]

end IndexDet

/-! ## §2 — the depth-`v` Sylvester counts -/

section SylvesterCount

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

variable {g h : Polynomial O} {n₁ n₂ : ℕ}

/-- The Sylvester pair map is injective as soon as the pinned-size resultant is nonzero
(the adjugate composition `adj ∘ syl = Res • id` cancels in the torsion-free module). -/
theorem sylvesterMap_injective (hg : g.natDegree ≤ n₁) (hh : h.natDegree ≤ n₂)
    (hres : Polynomial.resultant g h n₁ n₂ ≠ 0) :
    Function.Injective (Polynomial.sylvesterMap g h hg hh) := by
  intro x y hxy
  have hadj := Polynomial.adjSylvester_comp_sylveserMap g h hg hh
  have hx : Polynomial.adjSylvester g h (Polynomial.sylvesterMap g h hg hh x)
      = Polynomial.resultant g h n₁ n₂ • x := by
    have := LinearMap.ext_iff.mp hadj x
    simpa using this
  have hy : Polynomial.adjSylvester g h (Polynomial.sylvesterMap g h hg hh y)
      = Polynomial.resultant g h n₁ n₂ • y := by
    have := LinearMap.ext_iff.mp hadj y
    simpa using this
  have hsmul : Polynomial.resultant g h n₁ n₂ • x = Polynomial.resultant g h n₁ n₂ • y := by
    rw [← hx, ← hy, hxy]
  -- cancel the nonzero scalar coordinatewise in the torsion-free polynomial module
  have h1 : Polynomial.resultant g h n₁ n₂ • (x.1 : Polynomial O) =
      Polynomial.resultant g h n₁ n₂ • (y.1 : Polynomial O) :=
    congrArg (fun z : Polynomial.degreeLT O n₁ × Polynomial.degreeLT O n₂ =>
      (z.1 : Polynomial O)) hsmul
  have h2 : Polynomial.resultant g h n₁ n₂ • (x.2 : Polynomial O) =
      Polynomial.resultant g h n₁ n₂ • (y.2 : Polynomial O) :=
    congrArg (fun z : Polynomial.degreeLT O n₁ × Polynomial.degreeLT O n₂ =>
      (z.2 : Polynomial O)) hsmul
  have e1 : (x.1 : Polynomial O) = (y.1 : Polynomial O) := by
    exact mul_left_cancel₀ (a := Polynomial.C (Polynomial.resultant g h n₁ n₂))
      (by simpa using hres) (by
        rw [← Polynomial.smul_eq_C_mul, ← Polynomial.smul_eq_C_mul]; exact h1)
  have e2 : (x.2 : Polynomial O) = (y.2 : Polynomial O) := by
    exact mul_left_cancel₀ (a := Polynomial.C (Polynomial.resultant g h n₁ n₂))
      (by simpa using hres) (by
        rw [← Polynomial.smul_eq_C_mul, ← Polynomial.smul_eq_C_mul]; exact h2)
  exact Prod.ext (Subtype.ext e1) (Subtype.ext e2)

/-- `O[X]` is torsion-free over the domain `O` (the scalars enter through `C`). -/
private theorem noZeroSMulDivisors_polynomial :
    NoZeroSMulDivisors O (Polynomial O) := by
  refine ⟨fun {c p} hcp => ?_⟩
  rcases eq_or_ne c 0 with rfl | hc
  · exact Or.inl rfl
  · refine Or.inr ?_
    rw [Polynomial.smul_eq_C_mul] at hcp
    rcases mul_eq_zero.mp hcp with h1 | h2
    · exact absurd (Polynomial.C_eq_zero.mp h1) hc
    · exact h2

/-- Submodules inherit torsion-freeness. -/
private theorem noZeroSMulDivisors_submodule {M : Type*} [AddCommGroup M] [Module O M]
    [NoZeroSMulDivisors O M] (p : Submodule O M) : NoZeroSMulDivisors O p := by
  refine ⟨fun {c x} hcx => ?_⟩
  rcases eq_or_ne c 0 with rfl | hc
  · exact Or.inl rfl
  · refine Or.inr ?_
    have h1 : c • (x : M) = 0 := by
      rw [← Submodule.coe_smul, hcx, Submodule.coe_zero]
    exact Subtype.ext ((smul_eq_zero.mp h1).resolve_left hc)

/-- Products inherit torsion-freeness. -/
private theorem noZeroSMulDivisors_prod {M N : Type*} [AddCommGroup M] [Module O M]
    [AddCommGroup N] [Module O N] [NoZeroSMulDivisors O M] [NoZeroSMulDivisors O N] :
    NoZeroSMulDivisors O (M × N) := by
  refine ⟨fun {c x} hcx => ?_⟩
  rcases eq_or_ne c 0 with rfl | hc
  · exact Or.inl rfl
  · refine Or.inr ?_
    have h1 : c • x.1 = 0 := congrArg Prod.fst hcx
    have h2 : c • x.2 = 0 := congrArg Prod.snd hcx
    exact Prod.ext ((smul_eq_zero.mp h1).resolve_left hc)
      ((smul_eq_zero.mp h2).resolve_left hc)

attribute [local instance] noZeroSMulDivisors_polynomial noZeroSMulDivisors_submodule
  noZeroSMulDivisors_prod

/-- Scalar multiples of the identity are injective for nonzero scalars (torsion-free). -/
private theorem smul_id_injective {M : Type*} [AddCommGroup M] [Module O M]
    [NoZeroSMulDivisors O M] {x : O} (hx : x ≠ 0) :
    Function.Injective (x • (LinearMap.id : M →ₗ[O] M)) := by
  intro a b hab
  simp only [LinearMap.smul_apply, LinearMap.id_apply] at hab
  exact smul_right_injective M hx hab

variable [Finite (ResidueField O)]

/-- The level-`v` box count: `#(M ⧸ π^v·M) = q^{v·rank}` — §1 applied to `π^v • id`. -/
private theorem natCard_quotient_smul_id {M : Type*} [AddCommGroup M] [Module O M]
    [Module.Free O M] [Module.Finite O M] [NoZeroSMulDivisors O M]
    {π : O} (hπ : Irreducible π) (v : ℕ) :
    Nat.card (M ⧸ LinearMap.range ((π ^ v) • (LinearMap.id : M →ₗ[O] M)))
      = residueCard O ^ (v * Module.finrank O M) := by
  have hdet : LinearMap.det ((π ^ v) • (LinearMap.id : M →ₗ[O] M))
      = π ^ (v * Module.finrank O M) := by
    rw [LinearMap.det_smul, LinearMap.det_id, mul_one, ← pow_mul]
  exact natCard_quotient_range_smith hπ (smul_id_injective (pow_ne_zero v hπ.ne_zero))
    (by rw [hdet])

/-- The cokernel of the Sylvester pair map has size `q^w`, `w` = the resultant depth
(§1 through the `finSumFinEquiv`-reindexed product basis, whose matrix is the Sylvester
matrix). -/
theorem natCard_quotient_range_sylvesterMap {π : O} (hπ : Irreducible π)
    (hg : g.natDegree ≤ n₁) (hh : h.natDegree ≤ n₂) {w : ℕ}
    (hres : Associated (Polynomial.resultant g h n₁ n₂) (π ^ w)) :
    Nat.card ((Polynomial.degreeLT O (n₁ + n₂))
        ⧸ LinearMap.range (Polynomial.sylvesterMap g h hg hh))
      = residueCard O ^ w := by
  classical
  have hres0 : Polynomial.resultant g h n₁ n₂ ≠ 0 := by
    intro h0
    rw [h0] at hres
    exact pow_ne_zero w hπ.ne_zero ((associated_zero_iff_eq_zero _).mp hres.symm)
  set bpair := ((Polynomial.degreeLT.basis O n₁).prod
    (Polynomial.degreeLT.basis O n₂)).reindex finSumFinEquiv with hbpair
  set b' := Polynomial.degreeLT.basis O (n₁ + n₂) with hb'
  haveI : Module.Free O (Polynomial.degreeLT O (n₁ + n₂)) := Module.Free.of_basis b'
  haveI : Module.Finite O (Polynomial.degreeLT O (n₁ + n₂)) := Module.Finite.of_basis b'
  set e1 : Polynomial.degreeLT O (n₁ + n₂)
      ≃ₗ[O] Polynomial.degreeLT O n₁ × Polynomial.degreeLT O n₂ :=
    b'.equiv bpair (Equiv.refl _) with he1
  set G := (Polynomial.sylvesterMap g h hg hh) ∘ₗ e1.toLinearMap with hG
  have hmat1 : LinearMap.toMatrix b' bpair e1.toLinearMap = 1 := by
    ext i j
    rw [LinearMap.toMatrix_apply]
    have h2 : e1 (b' j) = bpair j := Module.Basis.equiv_apply b' j bpair (Equiv.refl _)
    rw [LinearEquiv.coe_coe, h2, Module.Basis.repr_self]
    by_cases hij : i = j
    · rw [hij, Matrix.one_apply_eq, Finsupp.single_eq_same]
    · rw [Matrix.one_apply_ne hij, Finsupp.single_eq_of_ne hij]
  have hGdet : LinearMap.det G = Polynomial.resultant g h n₁ n₂ := by
    rw [← LinearMap.det_toMatrix b', hG, LinearMap.toMatrix_comp b' bpair b',
      Polynomial.toMatrix_sylvesterMap', hmat1, mul_one, Polynomial.resultant]
  have hGinj : Function.Injective G := by
    rw [hG]
    exact (sylvesterMap_injective hg hh hres0).comp e1.injective
  have hrange : LinearMap.range G = LinearMap.range (Polynomial.sylvesterMap g h hg hh) := by
    rw [hG]
    exact LinearMap.range_comp_of_range_eq_top _ (LinearEquiv.range e1)
  rw [← hrange]
  exact natCard_quotient_range_smith hπ hGinj (hGdet ▸ hres)

/-- `π^v`-multiples land in the range of the Sylvester map when `w ≤ v` (the adjugate
prices `π^w` and the surplus `π^{v-w}` scales). -/
theorem smul_top_le_range_sylvesterMap {π : O} (hg : g.natDegree ≤ n₁)
    (hh : h.natDegree ≤ n₂) {w v : ℕ} (hwv : w ≤ v)
    (hres : Associated (Polynomial.resultant g h n₁ n₂) (π ^ w)) :
    LinearMap.range ((π ^ v) • (LinearMap.id :
        Polynomial.degreeLT O (n₁ + n₂) →ₗ[O] Polynomial.degreeLT O (n₁ + n₂)))
      ≤ LinearMap.range (Polynomial.sylvesterMap g h hg hh) := by
  rintro z ⟨x, rfl⟩
  have hadj := Polynomial.sylveserMap_comp_adjSylvester g h hg hh
  have h1 : Polynomial.sylvesterMap g h hg hh (Polynomial.adjSylvester g h x)
      = Polynomial.resultant g h n₁ n₂ • x := by
    have := LinearMap.ext_iff.mp hadj x
    simpa using this
  obtain ⟨u, hu⟩ := hres.symm
  refine ⟨(π ^ (v - w) * ((u⁻¹ : Oˣ) : O)) • Polynomial.adjSylvester g h x, ?_⟩
  rw [map_smul, h1, smul_smul, LinearMap.smul_apply, LinearMap.id_apply]
  congr 1
  rw [← hu]
  have hvw : v - w + w = v := by omega
  calc π ^ (v - w) * ((u⁻¹ : Oˣ) : O) * (π ^ w * ((u : Oˣ) : O))
      = (π ^ (v - w) * π ^ w) * (((u⁻¹ : Oˣ) : O) * ((u : Oˣ) : O)) := by ring
    _ = π ^ v * 1 := by rw [← pow_add, hvw, Units.inv_mul]
    _ = π ^ v := mul_one _

/-- ★ **THE DEPTH-`v` SYLVESTER KERNEL COUNT**: mod `π^v` (any `w ≤ v`), the Sylvester
pair map has kernel of size EXACTLY `q^w` — the Smith-normal-form fiber count, the
quantitative core of the q-power fiber law. -/
theorem natCard_ker_sylvesterMap_quot {π : O} (hπ : Irreducible π)
    (hg : g.natDegree ≤ n₁) (hh : h.natDegree ≤ n₂) {w v : ℕ} (hwv : w ≤ v)
    (hres : Associated (Polynomial.resultant g h n₁ n₂) (π ^ w))
    (hmapq : LinearMap.range ((π ^ v) • (LinearMap.id :
          Polynomial.degreeLT O n₁ × Polynomial.degreeLT O n₂ →ₗ[O] _))
        ≤ Submodule.comap (Polynomial.sylvesterMap g h hg hh)
            (LinearMap.range ((π ^ v) • (LinearMap.id :
              Polynomial.degreeLT O (n₁ + n₂) →ₗ[O] _)))) :
    Nat.card (LinearMap.ker (Submodule.mapQ _ _ (Polynomial.sylvesterMap g h hg hh)
        hmapq)) = residueCard O ^ w := by
  classical
  set T := Polynomial.sylvesterMap g h hg hh with hT
  set Tbar := Submodule.mapQ _ _ T hmapq with hTbar
  -- the two level-`v` box counts
  have hfrP : Module.finrank O (Polynomial.degreeLT O n₁ × Polynomial.degreeLT O n₂)
      = n₁ + n₂ := by
    rw [Module.finrank_eq_card_basis (Polynomial.degreeLT.basisProd O n₁ n₂),
      Fintype.card_fin]
  have hfrM : Module.finrank O (Polynomial.degreeLT O (n₁ + n₂)) = n₁ + n₂ := by
    rw [Module.finrank_eq_card_basis (Polynomial.degreeLT.basis O (n₁ + n₂)),
      Fintype.card_fin]
  have hcardP : Nat.card ((Polynomial.degreeLT O n₁ × Polynomial.degreeLT O n₂)
      ⧸ LinearMap.range ((π ^ v) • (LinearMap.id :
        Polynomial.degreeLT O n₁ × Polynomial.degreeLT O n₂ →ₗ[O] _)))
      = residueCard O ^ (v * (n₁ + n₂)) := by
    rw [natCard_quotient_smul_id hπ v, hfrP]
  have hcardM : Nat.card ((Polynomial.degreeLT O (n₁ + n₂))
      ⧸ LinearMap.range ((π ^ v) • (LinearMap.id :
        Polynomial.degreeLT O (n₁ + n₂) →ₗ[O] _)))
      = residueCard O ^ (v * (n₁ + n₂)) := by
    rw [natCard_quotient_smul_id hπ v, hfrM]
  haveI hfinP : Finite ((Polynomial.degreeLT O n₁ × Polynomial.degreeLT O n₂)
      ⧸ LinearMap.range ((π ^ v) • (LinearMap.id :
        Polynomial.degreeLT O n₁ × Polynomial.degreeLT O n₂ →ₗ[O] _))) :=
    (Nat.card_pos_iff.mp (by rw [hcardP]; exact pow_pos (residueCard_pos O) _)).2
  haveI hfinM : Finite ((Polynomial.degreeLT O (n₁ + n₂))
      ⧸ LinearMap.range ((π ^ v) • (LinearMap.id :
        Polynomial.degreeLT O (n₁ + n₂) →ₗ[O] _))) :=
    (Nat.card_pos_iff.mp (by rw [hcardM]; exact pow_pos (residueCard_pos O) _)).2
  -- Lagrange + first iso on the domain side
  have hlag1 := Submodule.card_eq_card_quotient_mul_card (LinearMap.ker Tbar)
  have hfi : Nat.card (((Polynomial.degreeLT O n₁ × Polynomial.degreeLT O n₂)
      ⧸ LinearMap.range ((π ^ v) • (LinearMap.id :
        Polynomial.degreeLT O n₁ × Polynomial.degreeLT O n₂ →ₗ[O] _)))
      ⧸ LinearMap.ker Tbar) = Nat.card (LinearMap.range Tbar) :=
    Nat.card_congr (Tbar.quotKerEquivRange).toEquiv
  -- Lagrange on the codomain side
  have hlag2 := Submodule.card_eq_card_quotient_mul_card (LinearMap.range Tbar)
  -- the cokernel of `Tbar` is the §-cokernel (third iso, sup form)
  have hrangebar : LinearMap.range Tbar
      = (LinearMap.range T).map (LinearMap.range ((π ^ v) • (LinearMap.id :
          Polynomial.degreeLT O (n₁ + n₂) →ₗ[O] _))).mkQ := by
    ext z
    constructor
    · rintro ⟨x, rfl⟩
      obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective _ x
      refine ⟨T y, ⟨y, rfl⟩, ?_⟩
      simp [hTbar, Submodule.mkQ_apply, Submodule.mapQ_apply]
    · rintro ⟨-, ⟨y, rfl⟩, rfl⟩
      refine ⟨Submodule.Quotient.mk y, ?_⟩
      simp [hTbar, Submodule.mkQ_apply, Submodule.mapQ_apply]
  have hcoker : Nat.card (((Polynomial.degreeLT O (n₁ + n₂))
      ⧸ LinearMap.range ((π ^ v) • (LinearMap.id :
        Polynomial.degreeLT O (n₁ + n₂) →ₗ[O] _)))
      ⧸ LinearMap.range Tbar) = residueCard O ^ w := by
    rw [hrangebar,
      Nat.card_congr (Submodule.quotientQuotientEquivQuotientSup _ _).toEquiv,
      sup_eq_right.mpr (smul_top_le_range_sylvesterMap hg hh hwv hres)]
    exact natCard_quotient_range_sylvesterMap hπ hg hh hres
  -- assemble: #ker · #range = q^{v·n} = #range · q^w, cancel #range
  have heq1 : Nat.card (LinearMap.ker Tbar) * Nat.card (LinearMap.range Tbar)
      = residueCard O ^ (v * (n₁ + n₂)) := by
    rw [← hcardP, hlag1, hfi]
  have heq2 : Nat.card (LinearMap.range Tbar) * residueCard O ^ w
      = residueCard O ^ (v * (n₁ + n₂)) := by
    rw [← hcardM, hlag2, hcoker]
  have hrpos : 0 < Nat.card (LinearMap.range Tbar) := by
    rcases Nat.eq_zero_or_pos (Nat.card (LinearMap.range Tbar)) with h0 | h
    · rw [h0, zero_mul] at heq2
      exact absurd heq2.symm (Nat.pos_iff_ne_zero.mp (pow_pos (residueCard_pos O) _))
    · exact h
  have := heq1.trans heq2.symm
  rw [mul_comm (Nat.card (LinearMap.range Tbar)) (residueCard O ^ w)] at this
  exact Nat.eq_of_mul_eq_mul_right hrpos this

end SylvesterCount

/-! ## §3 — ★★ THE NEIGHBORHOOD FIBER LAW (the q-power fiber law) -/

section FiberLaw

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)]

/-- **The depth-`v` pair neighborhood**: the level-`N` class pairs with the same
`mulClass` product as `(a₁, a₂)` whose factors are congruent to `(a₁, a₂)` mod
`π^{v+1}` (the congruence is read on any lifts; it is lift-independent for
`v + 1 ≤ N`). -/
def pairNbhd (π : O) {n₁ n₂ : ℕ} (N v : ℕ) (a₁ : Fin n₁ → O) (a₂ : Fin n₂ → O) :
    Set (Coeff O n₁ N × Coeff O n₂ N) :=
  {c | mulClass c.1 c.2 = mulClass (proj O n₁ N a₁) (proj O n₂ N a₂) ∧
    (∃ b₁ : Fin n₁ → O, proj O n₁ N b₁ = c.1 ∧ ∀ i, π ^ (v + 1) ∣ (b₁ i - a₁ i)) ∧
    (∃ b₂ : Fin n₂ → O, proj O n₂ N b₂ = c.2 ∧ ∀ i, π ^ (v + 1) ∣ (b₂ i - a₂ i))}

/-- The polynomial of a coefficient vector (no monic head). -/
private def vecPoly {n : ℕ} (z : Fin n → O) : Polynomial O :=
  ∑ j ∈ Finset.range n,
    Polynomial.C (if hj : j < n then z ⟨j, hj⟩ else 0) * Polynomial.X ^ j

private theorem vecPoly_coeff {n : ℕ} (z : Fin n → O) (j : ℕ) :
    (vecPoly z).coeff j = if hj : j < n then z ⟨j, hj⟩ else 0 := by
  rw [vecPoly, Uniformity.Hensel.coeff_sum_range_C_mul_X_pow]
  split_ifs with h1
  · rfl
  · rfl

private theorem vecPoly_degree_lt {n : ℕ} (z : Fin n → O) :
    (vecPoly z).degree < (n : WithBot ℕ) :=
  Uniformity.Hensel.degree_sum_range_C_mul_X_pow_lt _ n

private theorem vecPoly_mem_degreeLT {n : ℕ} (z : Fin n → O) :
    vecPoly z ∈ Polynomial.degreeLT O n :=
  Polynomial.mem_degreeLT.mpr (vecPoly_degree_lt z)

/-- **The frame identity**: if the coefficient vectors differ by `π^s`-multiples read
off a polynomial `P` supported in degrees `< n`, the monic frames differ by
`C(π^s) · P` (tops cancel). -/
private theorem monicPoly_sub_eq_C_mul {s : ℕ} {π : O} {n : ℕ} {a b : Fin n → O}
    {P : Polynomial O} (hPdeg : ∀ j, n ≤ j → P.coeff j = 0)
    (hz : ∀ i : Fin n, b i - a i = π ^ s * P.coeff (i : ℕ)) :
    monicPoly b - monicPoly a = Polynomial.C (π ^ s) * P := by
  ext j
  rw [Polynomial.coeff_sub, Polynomial.coeff_C_mul]
  rcases Nat.lt_or_ge j n with hj | hj
  · rw [monicPoly_coeff_lt b hj, monicPoly_coeff_lt a hj]
    exact hz ⟨j, hj⟩
  · have e1 : (monicPoly b).coeff j = (monicPoly a).coeff j := by
      rcases eq_or_lt_of_le hj with heqj | hlt
      · rw [← heqj]
        have hb1 : (monicPoly b).coeff n = 1 := by
          have h1 := (monicPoly_monic b).coeff_natDegree
          rwa [monicPoly_natDegree] at h1
        have ha1 : (monicPoly a).coeff n = 1 := by
          have h1 := (monicPoly_monic a).coeff_natDegree
          rwa [monicPoly_natDegree] at h1
        rw [hb1, ha1]
      · rw [Polynomial.coeff_eq_zero_of_natDegree_lt
            (by rw [monicPoly_natDegree]; exact hlt),
          Polynomial.coeff_eq_zero_of_natDegree_lt
            (by rw [monicPoly_natDegree]; exact hlt)]
    rw [e1, sub_self, hPdeg j hj, mul_zero]

/-- Equality of `mulClass` products at level `N` gives `π^N`-divisibility of the
lift-product difference (IFCG41's private cancellation-genre bridge, copied). -/
private theorem C_pow_dvd_mul_sub_of_mulClass_eq {π : O} (hπ : Irreducible π)
    {n₁ n₂ N : ℕ} {a₁ b₁ : Fin n₁ → O} {a₂ b₂ : Fin n₂ → O}
    (heq : mulClass (proj O n₁ N a₁) (proj O n₂ N a₂)
         = mulClass (proj O n₁ N b₁) (proj O n₂ N b₂)) :
    Polynomial.C (π ^ N) ∣ monicPoly b₁ * monicPoly b₂ - monicPoly a₁ * monicPoly a₂ := by
  refine (Polynomial.C_dvd_iff_dvd_coeff _ _).mpr fun i => ?_
  have hspan : (maximalIdeal O) ^ N = Ideal.span {π ^ N} := by
    rw [hπ.maximalIdeal_eq, Ideal.span_singleton_pow]
  rcases Nat.lt_or_ge i (n₁ + n₂) with hi | hi
  · have h1 : proj O (n₁ + n₂) N (fun j => (monicPoly a₁ * monicPoly a₂).coeff (j : ℕ))
        = proj O (n₁ + n₂) N (fun j => (monicPoly b₁ * monicPoly b₂).coeff (j : ℕ)) := by
      rw [mulClass_proj, mulClass_proj, heq]
    have h2 := congrFun h1 ⟨i, hi⟩
    have h3 : (monicPoly b₁ * monicPoly b₂).coeff i - (monicPoly a₁ * monicPoly a₂).coeff i
        ∈ (maximalIdeal O) ^ N := (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mp h2.symm
    rw [hspan, Ideal.mem_span_singleton] at h3
    rw [Polynomial.coeff_sub]
    exact h3
  · have hd : (monicPoly a₁ * monicPoly a₂).natDegree = n₁ + n₂ := by
      rw [(monicPoly_monic a₁).natDegree_mul (monicPoly_monic a₂),
        monicPoly_natDegree, monicPoly_natDegree]
    have hd' : (monicPoly b₁ * monicPoly b₂).natDegree = n₁ + n₂ := by
      rw [(monicPoly_monic b₁).natDegree_mul (monicPoly_monic b₂),
        monicPoly_natDegree, monicPoly_natDegree]
    have e1 : (monicPoly b₁ * monicPoly b₂).coeff i
        = (monicPoly a₁ * monicPoly a₂).coeff i := by
      rcases eq_or_lt_of_le hi with heqi | hlt
      · rw [← heqi]
        have hb1 : (monicPoly b₁ * monicPoly b₂).coeff (n₁ + n₂) = 1 := by
          rw [← hd']
          exact ((monicPoly_monic b₁).mul (monicPoly_monic b₂)).coeff_natDegree
        have ha1 : (monicPoly a₁ * monicPoly a₂).coeff (n₁ + n₂) = 1 := by
          rw [← hd]
          exact ((monicPoly_monic a₁).mul (monicPoly_monic a₂)).coeff_natDegree
        rw [hb1, ha1]
      · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [hd']; exact hlt),
          Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [hd]; exact hlt)]
    rw [Polynomial.coeff_sub, e1, sub_self]
    exact dvd_zero _

/-- The converse bridge: `π^N`-divisibility of the lift-product difference gives
equality of the `mulClass` products at level `N`. -/
private theorem mulClass_eq_of_C_pow_dvd {π : O} (hπ : Irreducible π)
    {n₁ n₂ N : ℕ} {a₁ b₁ : Fin n₁ → O} {a₂ b₂ : Fin n₂ → O}
    (hdvd : Polynomial.C (π ^ N)
      ∣ monicPoly b₁ * monicPoly b₂ - monicPoly a₁ * monicPoly a₂) :
    mulClass (proj O n₁ N b₁) (proj O n₂ N b₂)
      = mulClass (proj O n₁ N a₁) (proj O n₂ N a₂) := by
  rw [← mulClass_proj, ← mulClass_proj]
  funext i
  show Ideal.Quotient.mk ((maximalIdeal O) ^ N) ((monicPoly b₁ * monicPoly b₂).coeff (i : ℕ))
      = Ideal.Quotient.mk ((maximalIdeal O) ^ N) ((monicPoly a₁ * monicPoly a₂).coeff (i : ℕ))
  refine (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mpr ?_
  rw [hπ.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
  have h1 := (Polynomial.C_dvd_iff_dvd_coeff _ _).mp hdvd (i : ℕ)
  rwa [Polynomial.coeff_sub] at h1

/-- A `degreeLT` element with `C(π^v)`-divisible coefficients is a `π^v`-multiple
inside `degreeLT` (the quotient polynomial keeps the degree bound). -/
private theorem mem_smul_range_of_C_dvd {π : O} (hπ : Irreducible π) {v n : ℕ}
    (x : Polynomial.degreeLT O n)
    (hdvd : Polynomial.C (π ^ v) ∣ (x : Polynomial O)) :
    x ∈ LinearMap.range ((π ^ v) • (LinearMap.id :
      Polynomial.degreeLT O n →ₗ[O] Polynomial.degreeLT O n)) := by
  obtain ⟨Q, hQ⟩ := hdvd
  have hQdeg : Q.degree < (n : WithBot ℕ) := by
    rcases eq_or_ne Q 0 with rfl | hQ0
    · rw [Polynomial.degree_zero]
      exact WithBot.bot_lt_coe n
    · have hdeg : ((x : Polynomial O)).degree = Q.degree := by
        rw [hQ, Polynomial.degree_mul, Polynomial.degree_C (pow_ne_zero v hπ.ne_zero),
          zero_add]
      rw [← hdeg]
      exact Polynomial.mem_degreeLT.mp x.2
  refine ⟨⟨Q, Polynomial.mem_degreeLT.mpr hQdeg⟩, ?_⟩
  refine Subtype.ext ?_
  show π ^ v • Q = (x : Polynomial O)
  rw [Polynomial.smul_eq_C_mul, ← hQ]

private theorem coeff_eq_zero_of_mem_degreeLT {n j : ℕ} (x : Polynomial.degreeLT O n)
    (hj : n ≤ j) : (x : Polynomial O).coeff j = 0 :=
  Polynomial.coeff_eq_zero_of_degree_lt
    ((Polynomial.mem_degreeLT.mp x.2).trans_le (by exact_mod_cast hj))

/-- Cancel a `C(π^s)` factor out of a `C(π^{s+t})` divisibility. -/
private theorem C_pow_dvd_cancel {π : O} (hπ : Irreducible π) {s t : ℕ}
    {W : Polynomial O}
    (hd : Polynomial.C (π ^ (s + t)) ∣ Polynomial.C (π ^ s) * W) :
    Polynomial.C (π ^ t) ∣ W := by
  obtain ⟨c, hc⟩ := hd
  refine ⟨c, ?_⟩
  have h1 : Polynomial.C (π ^ s) * W = Polynomial.C (π ^ s) * (Polynomial.C (π ^ t) * c) := by
    rw [hc, pow_add, Polynomial.C_mul]
    ring
  exact mul_left_cancel₀ (fun h0 => pow_ne_zero s hπ.ne_zero (Polynomial.C_eq_zero.mp h0)) h1

/-- **The perturbation parametrization**: a pair of small polynomials perturbs the base
lift pair at level `π^{N-v}` and reads off the level-`N` class pair. -/
private def phiMap (π : O) {n₁ n₂ : ℕ} (N v : ℕ) (a₁ : Fin n₁ → O) (a₂ : Fin n₂ → O)
    (x : Polynomial.degreeLT O n₁ × Polynomial.degreeLT O n₂) :
    Coeff O n₁ N × Coeff O n₂ N :=
  (proj O n₁ N (fun i => a₁ i + π ^ (N - v) * (x.1 : Polynomial O).coeff i),
   proj O n₂ N (fun i => a₂ i + π ^ (N - v) * (x.2 : Polynomial O).coeff i))

/-- The perturbed monic frame, displayed additively. -/
private theorem monicPoly_phi_eq {π : O} {n : ℕ} (s : ℕ) (a : Fin n → O)
    (P : Polynomial.degreeLT O n) :
    monicPoly (fun i => a i + π ^ s * (P : Polynomial O).coeff i)
      = monicPoly a + Polynomial.C (π ^ s) * (P : Polynomial O) := by
  have h1 := monicPoly_sub_eq_C_mul (s := s) (π := π) (a := a)
    (b := fun i => a i + π ^ s * (P : Polynomial O).coeff i)
    (P := (P : Polynomial O)) (fun j hj => coeff_eq_zero_of_mem_degreeLT P hj)
    (fun i => by ring)
  linear_combination h1

/-- **The frame-product expansion**: the perturbed product differs from the base product
by `C(π^{N-v})·(Sylvester image) + C(π^{N-v})²·(quadratic term)`. -/
private theorem frame_prod_expand {π : O} {n₁ n₂ : ℕ} (N v : ℕ)
    (a₁ : Fin n₁ → O) (a₂ : Fin n₂ → O)
    (hgd : (monicPoly a₁).natDegree ≤ n₁) (hhd : (monicPoly a₂).natDegree ≤ n₂)
    (x : Polynomial.degreeLT O n₁ × Polynomial.degreeLT O n₂) :
    monicPoly (fun i => a₁ i + π ^ (N - v) * (x.1 : Polynomial O).coeff i)
      * monicPoly (fun i => a₂ i + π ^ (N - v) * (x.2 : Polynomial O).coeff i)
      - monicPoly a₁ * monicPoly a₂
    = Polynomial.C (π ^ (N - v))
        * ((Polynomial.sylvesterMap (monicPoly a₁) (monicPoly a₂) hgd hhd x : Polynomial O))
      + Polynomial.C (π ^ (N - v)) ^ 2 * ((x.1 : Polynomial O) * (x.2 : Polynomial O)) := by
  rw [monicPoly_phi_eq (N - v) a₁ x.1, monicPoly_phi_eq (N - v) a₂ x.2,
    Polynomial.sylvesterMap_apply_coe]
  ring

/-- **The parametrization is `π^v`-coset-faithful**: two perturbation pairs read off the
same class pair exactly when they differ by a `π^v`-multiple. -/
private theorem phiMap_eq_iff {π : O} (hπ : Irreducible π) {n₁ n₂ N v : ℕ}
    (hvN' : v ≤ N) (a₁ : Fin n₁ → O) (a₂ : Fin n₂ → O)
    (x x' : Polynomial.degreeLT O n₁ × Polynomial.degreeLT O n₂) :
    phiMap π N v a₁ a₂ x = phiMap π N v a₁ a₂ x'
      ↔ x - x' ∈ LinearMap.range ((π ^ v) • (LinearMap.id :
          Polynomial.degreeLT O n₁ × Polynomial.degreeLT O n₂ →ₗ[O] _)) := by
  have hNvv : N - v + v = N := by omega
  constructor
  · intro hΦ
    have h1 := congrArg Prod.fst hΦ
    have h2 := congrArg Prod.snd hΦ
    have hc1 : ∀ i : Fin n₁, π ^ v ∣
        ((x.1 : Polynomial O).coeff i - ((x'.1 : Polynomial O)).coeff i) := by
      intro i
      have h3 : Ideal.Quotient.mk ((maximalIdeal O) ^ N)
            (a₁ i + π ^ (N - v) * (x.1 : Polynomial O).coeff i)
          = Ideal.Quotient.mk ((maximalIdeal O) ^ N)
            (a₁ i + π ^ (N - v) * ((x'.1 : Polynomial O)).coeff i) := congrFun h1 i
      have h4 := (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mp h3
      rw [hπ.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton] at h4
      obtain ⟨c, hc⟩ := h4
      refine ⟨c, ?_⟩
      refine mul_left_cancel₀ (pow_ne_zero (N - v) hπ.ne_zero) ?_
      have hsplit : π ^ N = π ^ (N - v) * π ^ v := by rw [← pow_add, hNvv]
      calc π ^ (N - v) * ((x.1 : Polynomial O).coeff i - ((x'.1 : Polynomial O)).coeff i)
          = (a₁ i + π ^ (N - v) * (x.1 : Polynomial O).coeff i)
            - (a₁ i + π ^ (N - v) * ((x'.1 : Polynomial O)).coeff i) := by ring
        _ = π ^ N * c := hc
        _ = π ^ (N - v) * (π ^ v * c) := by rw [hsplit]; ring
    have hc2 : ∀ i : Fin n₂, π ^ v ∣
        ((x.2 : Polynomial O).coeff i - ((x'.2 : Polynomial O)).coeff i) := by
      intro i
      have h3 : Ideal.Quotient.mk ((maximalIdeal O) ^ N)
            (a₂ i + π ^ (N - v) * (x.2 : Polynomial O).coeff i)
          = Ideal.Quotient.mk ((maximalIdeal O) ^ N)
            (a₂ i + π ^ (N - v) * ((x'.2 : Polynomial O)).coeff i) := congrFun h2 i
      have h4 := (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mp h3
      rw [hπ.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton] at h4
      obtain ⟨c, hc⟩ := h4
      refine ⟨c, ?_⟩
      refine mul_left_cancel₀ (pow_ne_zero (N - v) hπ.ne_zero) ?_
      have hsplit : π ^ N = π ^ (N - v) * π ^ v := by rw [← pow_add, hNvv]
      calc π ^ (N - v) * ((x.2 : Polynomial O).coeff i - ((x'.2 : Polynomial O)).coeff i)
          = (a₂ i + π ^ (N - v) * (x.2 : Polynomial O).coeff i)
            - (a₂ i + π ^ (N - v) * ((x'.2 : Polynomial O)).coeff i) := by ring
        _ = π ^ N * c := hc
        _ = π ^ (N - v) * (π ^ v * c) := by rw [hsplit]; ring
    have hd1 : Polynomial.C (π ^ v) ∣ ((x.1 - x'.1 : Polynomial.degreeLT O n₁) : Polynomial O) := by
      refine (Polynomial.C_dvd_iff_dvd_coeff _ _).mpr fun j => ?_
      have hcoe : ((x.1 - x'.1 : Polynomial.degreeLT O n₁) : Polynomial O)
          = (x.1 : Polynomial O) - ((x'.1 : Polynomial O)) := rfl
      rw [hcoe, Polynomial.coeff_sub]
      rcases Nat.lt_or_ge j n₁ with hj | hj
      · exact hc1 ⟨j, hj⟩
      · rw [coeff_eq_zero_of_mem_degreeLT x.1 hj, coeff_eq_zero_of_mem_degreeLT x'.1 hj,
          sub_self]
        exact dvd_zero _
    have hd2 : Polynomial.C (π ^ v) ∣ ((x.2 - x'.2 : Polynomial.degreeLT O n₂) : Polynomial O) := by
      refine (Polynomial.C_dvd_iff_dvd_coeff _ _).mpr fun j => ?_
      have hcoe : ((x.2 - x'.2 : Polynomial.degreeLT O n₂) : Polynomial O)
          = (x.2 : Polynomial O) - ((x'.2 : Polynomial O)) := rfl
      rw [hcoe, Polynomial.coeff_sub]
      rcases Nat.lt_or_ge j n₂ with hj | hj
      · exact hc2 ⟨j, hj⟩
      · rw [coeff_eq_zero_of_mem_degreeLT x.2 hj, coeff_eq_zero_of_mem_degreeLT x'.2 hj,
          sub_self]
        exact dvd_zero _
    obtain ⟨y₁, hy₁⟩ := mem_smul_range_of_C_dvd hπ (x.1 - x'.1) hd1
    obtain ⟨y₂, hy₂⟩ := mem_smul_range_of_C_dvd hπ (x.2 - x'.2) hd2
    refine ⟨(y₁, y₂), ?_⟩
    have e1 : (π ^ v • (LinearMap.id : Polynomial.degreeLT O n₁ × Polynomial.degreeLT O n₂ →ₗ[O] _)) (y₁, y₂)
        = ((π ^ v • (LinearMap.id : Polynomial.degreeLT O n₁ →ₗ[O] _)) y₁,
           (π ^ v • (LinearMap.id : Polynomial.degreeLT O n₂ →ₗ[O] _)) y₂) := by
      simp only [LinearMap.smul_apply, LinearMap.id_apply]
      rfl
    rw [e1, hy₁, hy₂]
    rfl
  · rintro ⟨y, hy⟩
    have hy1 : π ^ v • (y.1 : Polynomial O) = (x.1 : Polynomial O) - ((x'.1 : Polynomial O)) := by
      have := congrArg (fun z : Polynomial.degreeLT O n₁ × Polynomial.degreeLT O n₂ =>
        ((z.1 : Polynomial.degreeLT O n₁) : Polynomial O)) hy
      simpa using this
    have hy2 : π ^ v • (y.2 : Polynomial O) = (x.2 : Polynomial O) - ((x'.2 : Polynomial O)) := by
      have := congrArg (fun z : Polynomial.degreeLT O n₁ × Polynomial.degreeLT O n₂ =>
        ((z.2 : Polynomial.degreeLT O n₂) : Polynomial O)) hy
      simpa using this
    refine Prod.ext ?_ ?_
    · funext i
      show Ideal.Quotient.mk ((maximalIdeal O) ^ N)
            (a₁ i + π ^ (N - v) * (x.1 : Polynomial O).coeff i)
          = Ideal.Quotient.mk ((maximalIdeal O) ^ N)
            (a₁ i + π ^ (N - v) * ((x'.1 : Polynomial O)).coeff i)
      refine (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mpr ?_
      rw [hπ.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
      refine ⟨(y.1 : Polynomial O).coeff i, ?_⟩
      have h5 : (x.1 : Polynomial O).coeff i - ((x'.1 : Polynomial O)).coeff i
          = π ^ v * (y.1 : Polynomial O).coeff i := by
        have := congrArg (fun p : Polynomial O => p.coeff i) hy1
        simpa [Polynomial.coeff_smul, smul_eq_mul] using this.symm
      calc (a₁ i + π ^ (N - v) * (x.1 : Polynomial O).coeff i)
            - (a₁ i + π ^ (N - v) * ((x'.1 : Polynomial O)).coeff i)
          = π ^ (N - v) * ((x.1 : Polynomial O).coeff i - ((x'.1 : Polynomial O)).coeff i) := by
            ring
        _ = π ^ (N - v) * (π ^ v * (y.1 : Polynomial O).coeff i) := by rw [h5]
        _ = π ^ N * (y.1 : Polynomial O).coeff i := by rw [← mul_assoc, ← pow_add, hNvv]
    · funext i
      show Ideal.Quotient.mk ((maximalIdeal O) ^ N)
            (a₂ i + π ^ (N - v) * (x.2 : Polynomial O).coeff i)
          = Ideal.Quotient.mk ((maximalIdeal O) ^ N)
            (a₂ i + π ^ (N - v) * ((x'.2 : Polynomial O)).coeff i)
      refine (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mpr ?_
      rw [hπ.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
      refine ⟨(y.2 : Polynomial O).coeff i, ?_⟩
      have h5 : (x.2 : Polynomial O).coeff i - ((x'.2 : Polynomial O)).coeff i
          = π ^ v * (y.2 : Polynomial O).coeff i := by
        have := congrArg (fun p : Polynomial O => p.coeff i) hy2
        simpa [Polynomial.coeff_smul, smul_eq_mul] using this.symm
      calc (a₂ i + π ^ (N - v) * (x.2 : Polynomial O).coeff i)
            - (a₂ i + π ^ (N - v) * ((x'.2 : Polynomial O)).coeff i)
          = π ^ (N - v) * ((x.2 : Polynomial O).coeff i - ((x'.2 : Polynomial O)).coeff i) := by
            ring
        _ = π ^ (N - v) * (π ^ v * (y.2 : Polynomial O).coeff i) := by rw [h5]
        _ = π ^ N * (y.2 : Polynomial O).coeff i := by rw [← mul_assoc, ← pow_add, hNvv]

/-- **The construction leg**: a Sylvester-kernel element (mod `π^v`) parametrizes a
member of the depth-`v` pair neighborhood. -/
private theorem phiMap_mem_pairNbhd {π : O} (hπ : Irreducible π) {n₁ n₂ N v : ℕ}
    (hN : 2 * v + 1 ≤ N) (a₁ : Fin n₁ → O) (a₂ : Fin n₂ → O)
    (x : Polynomial.degreeLT O n₁ × Polynomial.degreeLT O n₂)
    (hTx : (Polynomial.sylvesterMap (monicPoly a₁) (monicPoly a₂)
        (monicPoly_natDegree a₁).le (monicPoly_natDegree a₂).le) x
      ∈ LinearMap.range ((π ^ v) • (LinearMap.id :
          Polynomial.degreeLT O (n₁ + n₂) →ₗ[O] _))) :
    phiMap π N v a₁ a₂ x ∈ pairNbhd π N v a₁ a₂ := by
  obtain ⟨y, hy⟩ := hTx
  have hycoe : Polynomial.C (π ^ v) * (y : Polynomial O)
      = ((Polynomial.sylvesterMap (monicPoly a₁) (monicPoly a₂)
          (monicPoly_natDegree a₁).le (monicPoly_natDegree a₂).le) x : Polynomial O) := by
    have h1 := congrArg (fun z : Polynomial.degreeLT O (n₁ + n₂) => (z : Polynomial O)) hy
    simpa [Polynomial.smul_eq_C_mul] using h1
  have hprod : Polynomial.C (π ^ N) ∣
      monicPoly (fun i => a₁ i + π ^ (N - v) * (x.1 : Polynomial O).coeff i)
        * monicPoly (fun i => a₂ i + π ^ (N - v) * (x.2 : Polynomial O).coeff i)
      - monicPoly a₁ * monicPoly a₂ := by
    rw [frame_prod_expand N v a₁ a₂ (monicPoly_natDegree a₁).le (monicPoly_natDegree a₂).le x,
      ← hycoe]
    have hsplit : π ^ N = π ^ (N - v) * π ^ v := by
      rw [← pow_add]
      congr 1
      omega
    have hterm1 : Polynomial.C (π ^ N)
        ∣ Polynomial.C (π ^ (N - v)) * (Polynomial.C (π ^ v) * (y : Polynomial O)) :=
      ⟨(y : Polynomial O), by rw [hsplit, Polynomial.C_mul]; ring⟩
    have hterm2 : Polynomial.C (π ^ N)
        ∣ Polynomial.C (π ^ (N - v)) ^ 2 * ((x.1 : Polynomial O) * (x.2 : Polynomial O)) := by
      refine dvd_mul_of_dvd_left ?_ _
      rw [← Polynomial.C_pow, ← pow_mul]
      exact map_dvd Polynomial.C (pow_dvd_pow π (by omega))
    exact dvd_add hterm1 hterm2
  refine ⟨mulClass_eq_of_C_pow_dvd hπ hprod, ?_, ?_⟩
  · refine ⟨fun i => a₁ i + π ^ (N - v) * (x.1 : Polynomial O).coeff i, rfl, fun i => ?_⟩
    have h2 : (fun i => a₁ i + π ^ (N - v) * (x.1 : Polynomial O).coeff i) i - a₁ i
        = π ^ (N - v) * (x.1 : Polynomial O).coeff i := by ring
    rw [h2]
    exact (pow_dvd_pow π (by omega : v + 1 ≤ N - v)).trans (dvd_mul_right _ _)
  · refine ⟨fun i => a₂ i + π ^ (N - v) * (x.2 : Polynomial O).coeff i, rfl, fun i => ?_⟩
    have h2 : (fun i => a₂ i + π ^ (N - v) * (x.2 : Polynomial O).coeff i) i - a₂ i
        = π ^ (N - v) * (x.2 : Polynomial O).coeff i := by ring
    rw [h2]
    exact (pow_dvd_pow π (by omega : v + 1 ≤ N - v)).trans (dvd_mul_right _ _)

/-- **The exhaustion leg**: every member of the depth-`v` pair neighborhood is
parametrized by a Sylvester-kernel element (RDC's gap engine supplies the divided
differences). -/
private theorem exists_phiMap_eq {π : O} (hπ : Irreducible π) {n₁ n₂ N v : ℕ}
    (hN : 2 * v + 1 ≤ N) (hpos : n₁ ≠ 0 ∨ n₂ ≠ 0)
    {a₁ : Fin n₁ → O} {a₂ : Fin n₂ → O}
    (hv1 : ¬ π ^ (v + 1) ∣ Polynomial.resultant (monicPoly a₁) (monicPoly a₂) n₁ n₂)
    {c : Coeff O n₁ N × Coeff O n₂ N} (hc : c ∈ pairNbhd π N v a₁ a₂) :
    ∃ x : Polynomial.degreeLT O n₁ × Polynomial.degreeLT O n₂,
      ((Polynomial.sylvesterMap (monicPoly a₁) (monicPoly a₂)
          (monicPoly_natDegree a₁).le (monicPoly_natDegree a₂).le) x
        ∈ LinearMap.range ((π ^ v) • (LinearMap.id :
            Polynomial.degreeLT O (n₁ + n₂) →ₗ[O] _)))
      ∧ phiMap π N v a₁ a₂ x = c := by
  obtain ⟨heqc, ⟨b₁, hb₁, hcong₁⟩, ⟨b₂, hb₂, hcong₂⟩⟩ := hc
  have hbez := exists_bezout_of_not_dvd_resultant hπ
    (monicPoly_natDegree a₁).le (monicPoly_natDegree a₂).le hpos hv1
  have heq' : mulClass (proj O n₁ N a₁) (proj O n₂ N a₂)
      = mulClass (proj O n₁ N b₁) (proj O n₂ N b₂) := by
    rw [← hb₁, ← hb₂] at heqc
    exact heqc.symm
  have hgap := mulClass_fiber_gap hπ hbez hcong₁ hcong₂ heq'
  choose z₁ hz₁ using hgap.1
  choose z₂ hz₂ using hgap.2
  refine ⟨(⟨vecPoly z₁, vecPoly_mem_degreeLT z₁⟩, ⟨vecPoly z₂, vecPoly_mem_degreeLT z₂⟩),
    ?_, ?_⟩
  · -- the kernel condition: `C(π^v) ∣ T x`, extracted from the product congruence
    set x : Polynomial.degreeLT O n₁ × Polynomial.degreeLT O n₂ :=
      (⟨vecPoly z₁, vecPoly_mem_degreeLT z₁⟩, ⟨vecPoly z₂, vecPoly_mem_degreeLT z₂⟩) with hx
    have hb₁x : b₁ = fun i => a₁ i + π ^ (N - v) * ((x.1 : Polynomial O)).coeff i := by
      funext i
      have h1 : ((x.1 : Polynomial O)).coeff (i : ℕ) = z₁ i := by
        show (vecPoly z₁).coeff (i : ℕ) = z₁ i
        rw [vecPoly_coeff, dif_pos i.isLt]
      rw [h1]
      have h2 := hz₁ i
      linear_combination h2
    have hb₂x : b₂ = fun i => a₂ i + π ^ (N - v) * ((x.2 : Polynomial O)).coeff i := by
      funext i
      have h1 : ((x.2 : Polynomial O)).coeff (i : ℕ) = z₂ i := by
        show (vecPoly z₂).coeff (i : ℕ) = z₂ i
        rw [vecPoly_coeff, dif_pos i.isLt]
      rw [h1]
      have h2 := hz₂ i
      linear_combination h2
    have hprod := C_pow_dvd_mul_sub_of_mulClass_eq hπ heq'
    rw [hb₁x, hb₂x, frame_prod_expand N v a₁ a₂
      (monicPoly_natDegree a₁).le (monicPoly_natDegree a₂).le x] at hprod
    have hterm2 : Polynomial.C (π ^ N)
        ∣ Polynomial.C (π ^ (N - v)) ^ 2 * ((x.1 : Polynomial O) * (x.2 : Polynomial O)) := by
      refine dvd_mul_of_dvd_left ?_ _
      rw [← Polynomial.C_pow, ← pow_mul]
      exact map_dvd Polynomial.C (pow_dvd_pow π (by omega))
    rw [add_comm] at hprod
    have h5 : Polynomial.C (π ^ N) ∣ Polynomial.C (π ^ (N - v))
        * ((Polynomial.sylvesterMap (monicPoly a₁) (monicPoly a₂)
            (monicPoly_natDegree a₁).le (monicPoly_natDegree a₂).le) x : Polynomial O) :=
      (dvd_add_right hterm2).mp hprod
    have h5' : Polynomial.C (π ^ ((N - v) + v)) ∣ Polynomial.C (π ^ (N - v))
        * ((Polynomial.sylvesterMap (monicPoly a₁) (monicPoly a₂)
            (monicPoly_natDegree a₁).le (monicPoly_natDegree a₂).le) x : Polynomial O) := by
      have hNvv : N - v + v = N := by omega
      rw [hNvv]
      exact h5
    exact mem_smul_range_of_C_dvd hπ _ (C_pow_dvd_cancel hπ h5')
  · -- the reconstruction: `Φ x = c`
    refine Prod.ext ?_ ?_
    · show proj O n₁ N (fun i => a₁ i + π ^ (N - v) * (vecPoly z₁).coeff i) = c.1
      have hfun : (fun i : Fin n₁ => a₁ i + π ^ (N - v) * (vecPoly z₁).coeff i) = b₁ := by
        funext i
        rw [vecPoly_coeff, dif_pos i.isLt]
        linear_combination (hz₁ i).symm
      rw [hfun, hb₁]
    · show proj O n₂ N (fun i => a₂ i + π ^ (N - v) * (vecPoly z₂).coeff i) = c.2
      have hfun : (fun i : Fin n₂ => a₂ i + π ^ (N - v) * (vecPoly z₂).coeff i) = b₂ := by
        funext i
        rw [vecPoly_coeff, dif_pos i.isLt]
        linear_combination (hz₂ i).symm
      rw [hfun, hb₂]

/-- ★★ **THE q-POWER FIBER LAW** (the neighborhood form): at exact resultant depth `v`
(`π^v ∣ Res`, `π^{v+1} ∤ Res`) with `2v + 1 ≤ N`, the depth-`v` pair neighborhood has
EXACTLY `q^v` members.  The `≤`/separation direction is RDC's gap engine
(`mulClass_fiber_gap`); the `≥`/construction direction is the depth-`v` Sylvester
kernel parametrization `(ε, η) ↦ (a₁ + π^{N-v}·ε, a₂ + π^{N-v}·η)` (§2). -/
theorem natCard_pairNbhd {π : O} (hπ : Irreducible π) {n₁ n₂ N v : ℕ}
    (hN : 2 * v + 1 ≤ N) (hpos : n₁ ≠ 0 ∨ n₂ ≠ 0)
    {a₁ : Fin n₁ → O} {a₂ : Fin n₂ → O}
    (hv : π ^ v ∣ Polynomial.resultant (monicPoly a₁) (monicPoly a₂) n₁ n₂)
    (hv1 : ¬ π ^ (v + 1) ∣ Polynomial.resultant (monicPoly a₁) (monicPoly a₂) n₁ n₂) :
    Nat.card (pairNbhd π N v a₁ a₂) = residueCard O ^ v := by
  classical
  -- exact depth: the resultant is associated to `π^v`
  have hres0 : Polynomial.resultant (monicPoly a₁) (monicPoly a₂) n₁ n₂ ≠ 0 :=
    fun h0 => hv1 (h0 ▸ dvd_zero _)
  obtain ⟨w0, u0, hwu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hres0 hπ
  have hw0v : w0 ≤ v := by
    by_contra hcon
    exact hv1 (hwu ▸ ((pow_dvd_pow π (by omega : v + 1 ≤ w0)).trans (dvd_mul_left _ _)))
  have hvw0 : v ≤ w0 := by
    by_contra hcon
    rw [not_le] at hcon
    have h1 : π ^ (w0 + 1) ∣ (u0 : O) * π ^ w0 := by
      rw [← hwu]
      exact (pow_dvd_pow π (by omega : w0 + 1 ≤ v)).trans hv
    obtain ⟨c, hc⟩ := h1
    have h3 : (u0 : O) = π * c := by
      refine mul_left_cancel₀ (pow_ne_zero w0 hπ.ne_zero) ?_
      calc π ^ w0 * (u0 : O) = (u0 : O) * π ^ w0 := by ring
        _ = π ^ (w0 + 1) * c := hc
        _ = π ^ w0 * (π * c) := by rw [pow_succ]; ring
    exact hπ.not_isUnit (isUnit_of_mul_isUnit_left (h3 ▸ u0.isUnit))
  have hres_assoc : Associated
      (Polynomial.resultant (monicPoly a₁) (monicPoly a₂) n₁ n₂) (π ^ v) := by
    rw [← le_antisymm hw0v hvw0]
    exact ⟨u0⁻¹, by
      rw [hwu, mul_comm ((u0 : Oˣ) : O), mul_assoc, Units.mul_inv, mul_one]⟩
  -- the level-`v` Sylvester reduction and its kernel count (§2)
  set T := Polynomial.sylvesterMap (monicPoly a₁) (monicPoly a₂)
    (monicPoly_natDegree a₁).le (monicPoly_natDegree a₂).le with hT
  have hmapq : LinearMap.range ((π ^ v) • (LinearMap.id :
        Polynomial.degreeLT O n₁ × Polynomial.degreeLT O n₂ →ₗ[O] _))
      ≤ Submodule.comap T
        (LinearMap.range ((π ^ v) • (LinearMap.id :
          Polynomial.degreeLT O (n₁ + n₂) →ₗ[O] _))) := by
    rintro z ⟨x, rfl⟩
    refine Submodule.mem_comap.mpr ⟨T x, ?_⟩
    simp only [LinearMap.smul_apply, LinearMap.id_apply, map_smul]
  have hker := natCard_ker_sylvesterMap_quot hπ (monicPoly_natDegree a₁).le
    (monicPoly_natDegree a₂).le (le_refl v) hres_assoc hmapq
  rw [← hker]
  -- the kernel-membership bridge
  have hkerm : ∀ x : Polynomial.degreeLT O n₁ × Polynomial.degreeLT O n₂,
      (Submodule.Quotient.mk x ∈ LinearMap.ker (Submodule.mapQ _ _ T hmapq))
      ↔ T x ∈ LinearMap.range ((π ^ v) • (LinearMap.id :
          Polynomial.degreeLT O (n₁ + n₂) →ₗ[O] _)) := by
    intro x
    rw [LinearMap.mem_ker, Submodule.mapQ_apply, Submodule.Quotient.mk_eq_zero]
  -- the bijection with the kernel
  have key1 := fun (c : Coeff O n₁ N × Coeff O n₂ N)
      (hc : c ∈ pairNbhd π N v a₁ a₂) => exists_phiMap_eq hπ hN hpos hv1 hc
  choose θ hθker hθΦ using key1
  refine Nat.card_eq_of_bijective
    (fun c => ⟨Submodule.Quotient.mk (θ c.1 c.2), (hkerm _).mpr (hθker c.1 c.2)⟩)
    ⟨?_, ?_⟩
  · intro c c' hcc'
    have h1 : (Submodule.Quotient.mk (θ c.1 c.2) :
          (Polynomial.degreeLT O n₁ × Polynomial.degreeLT O n₂)
            ⧸ LinearMap.range ((π ^ v) • LinearMap.id))
        = Submodule.Quotient.mk (θ c'.1 c'.2) := congrArg Subtype.val hcc'
    have h2 : θ c.1 c.2 - θ c'.1 c'.2 ∈ LinearMap.range ((π ^ v) • (LinearMap.id :
        Polynomial.degreeLT O n₁ × Polynomial.degreeLT O n₂ →ₗ[O] _)) :=
      (Submodule.Quotient.eq _).mp h1
    have h3 := (phiMap_eq_iff (N := N) (v := v) hπ (by omega) a₁ a₂ _ _).mpr h2
    exact Subtype.ext (by rw [← hθΦ c.1 c.2, ← hθΦ c'.1 c'.2, h3])
  · rintro ⟨ξ, hξ⟩
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ ξ
    have hxmem : phiMap π N v a₁ a₂ x ∈ pairNbhd π N v a₁ a₂ :=
      phiMap_mem_pairNbhd hπ hN a₁ a₂ x ((hkerm x).mp hξ)
    refine ⟨⟨phiMap π N v a₁ a₂ x, hxmem⟩, ?_⟩
    refine Subtype.ext ?_
    show (Submodule.Quotient.mk (θ _ _) :
        (Polynomial.degreeLT O n₁ × Polynomial.degreeLT O n₂)
          ⧸ LinearMap.range ((π ^ v) • LinearMap.id)) = Submodule.Quotient.mk x
    refine (Submodule.Quotient.eq _).mpr ?_
    exact (phiMap_eq_iff (N := N) (v := v) hπ (by omega) a₁ a₂ _ _).mp
      (hθΦ _ hxmem)

end FiberLaw

/-! ## §4 — ★★ THE HENSEL LEG: the depth-`v` Newton engine and `LiftsFactor` -/

section HenselLeg

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [IsAdicComplete (maximalIdeal O) O]

/-- Membership in `coeffIdeal (𝔪^s)` reads as `C(π^s)`-divisibility over the DVR. -/
private theorem mem_coeffIdeal_iff_C_dvd {π : O} (hπ : Irreducible π) {s : ℕ}
    {p : Polynomial O} :
    p ∈ Uniformity.Hensel.coeffIdeal ((maximalIdeal O) ^ s)
      ↔ Polynomial.C (π ^ s) ∣ p := by
  rw [Uniformity.Hensel.mem_coeffIdeal]
  have hspan : (maximalIdeal O) ^ s = Ideal.span {π ^ s} := by
    rw [hπ.maximalIdeal_eq, Ideal.span_singleton_pow]
  constructor
  · intro hmem
    refine (Polynomial.C_dvd_iff_dvd_coeff _ _).mpr fun i => ?_
    have := hmem i
    rwa [hspan, Ideal.mem_span_singleton] at this
  · intro hdvd i
    rw [hspan, Ideal.mem_span_singleton]
    exact (Polynomial.C_dvd_iff_dvd_coeff _ _).mp hdvd i

/-- **The Newton step at depth `v`**: one stage of the iteration — fresh depth-stable
resultant, normalized Bezout witness, EXACT linear-term kill, quadratic error at
doubled level. -/
private theorem newton_step {π : O} (hπ : Irreducible π) {g h G H F : Polynomial O}
    {v n₁ n₂ k : ℕ}
    (hpos : n₁ ≠ 0 ∨ n₂ ≠ 0)
    (hres : ¬ π ^ (v + 1) ∣ Polynomial.resultant g h n₁ n₂)
    (hG : G.Monic) (hH : H.Monic) (hdG : G.natDegree = n₁) (hdH : H.natDegree = n₂)
    (hcongG : Polynomial.C (π ^ (v + 1)) ∣ G - g)
    (hcongH : Polynomial.C (π ^ (v + 1)) ∣ H - h)
    (hk : 2 * v + 1 ≤ k)
    (hF : F.Monic) (hdF : F.natDegree = n₁ + n₂)
    (herr : Polynomial.C (π ^ k) ∣ F - G * H) :
    ∃ G' H' : Polynomial O, G'.Monic ∧ H'.Monic
      ∧ G'.natDegree = n₁ ∧ H'.natDegree = n₂
      ∧ Polynomial.C (π ^ (k - v)) ∣ G' - G ∧ Polynomial.C (π ^ (k - v)) ∣ H' - H
      ∧ Polynomial.C (π ^ (k + 1)) ∣ F - G' * H' := by
  classical
  -- 1. the fresh resultant keeps its depth (congruence-stability mod π^{v+1})
  have hresk : ¬ π ^ (v + 1) ∣ Polynomial.resultant G H n₁ n₂ := by
    intro hdvd
    apply hres
    set ψ := Ideal.Quotient.mk (Ideal.span {π ^ (v + 1)}) with hψ
    have hmapeq : ∀ {A B : Polynomial O}, Polynomial.C (π ^ (v + 1)) ∣ A - B →
        A.map ψ = B.map ψ := by
      intro A B hAB
      have h0 : (A - B).map ψ = 0 := by
        refine Polynomial.ext fun i => ?_
        rw [Polynomial.coeff_map, Polynomial.coeff_zero]
        exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton.mpr
          ((Polynomial.C_dvd_iff_dvd_coeff _ _).mp hAB i))
      rwa [Polynomial.map_sub, sub_eq_zero] at h0
    have hres_eq : ψ (Polynomial.resultant G H n₁ n₂)
        = ψ (Polynomial.resultant g h n₁ n₂) := by
      rw [← Polynomial.resultant_map_map, ← Polynomial.resultant_map_map,
        hmapeq hcongG, hmapeq hcongH]
    have h1 : ψ (Polynomial.resultant G H n₁ n₂) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton.mpr hdvd)
    rw [h1] at hres_eq
    exact Ideal.mem_span_singleton.mp (Ideal.Quotient.eq_zero_iff_mem.mp hres_eq.symm)
  -- 2. the normalized Bezout witness at exact scale π^v
  have hresk0 : Polynomial.resultant G H n₁ n₂ ≠ 0 := fun h0 => hresk (h0 ▸ dvd_zero _)
  obtain ⟨w0, u0, hwu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hresk0 hπ
  have hw0v : w0 ≤ v := by
    by_contra hcon
    exact hresk (hwu ▸ ((pow_dvd_pow π (by omega : v + 1 ≤ w0)).trans (dvd_mul_left _ _)))
  obtain ⟨p0, q0, hp0, hq0, hkey⟩ := Polynomial.exists_mul_add_mul_eq_C_resultant G H
    (hdG.le) (hdH.le) hpos
  set cscale : O := (↑u0⁻¹ : O) * π ^ (v - w0) with hcscale
  set p' := Polynomial.C cscale * p0 with hp'
  set q' := Polynomial.C cscale * q0 with hq'
  have hbez : G * p' + H * q' = Polynomial.C (π ^ v) := by
    have hexp : (↑u0 : O) * π ^ w0 * cscale = π ^ v := by
      rw [hcscale, mul_mul_mul_comm, Units.mul_inv, one_mul, ← pow_add]
      congr 1
      omega
    calc G * p' + H * q'
        = (G * p0 + H * q0) * Polynomial.C cscale := by rw [hp', hq']; ring
      _ = Polynomial.C ((↑u0 : O) * π ^ w0 * cscale) := by
          rw [hkey, hwu, ← Polynomial.C_mul]
      _ = Polynomial.C (π ^ v) := by rw [hexp]
  have hp'deg : p'.degree < (n₂ : WithBot ℕ) :=
    lt_of_le_of_lt (Uniformity.Hensel.degree_C_mul_le_degree _ _) hp0
  have hq'deg : q'.degree < (n₁ : WithBot ℕ) :=
    lt_of_le_of_lt (Uniformity.Hensel.degree_C_mul_le_degree _ _) hq0
  -- 3. the error and its degree
  obtain ⟨E, hE⟩ := herr
  rcases eq_or_ne E 0 with rfl | hE0
  · -- exact factorization already: stay put
    refine ⟨G, H, hG, hH, hdG, hdH, by simp, by simp, ?_⟩
    have h1 : F - G * H = 0 := by rw [hE, mul_zero]
    rw [h1]
    exact dvd_zero _
  have hdegFGH : (F - G * H).degree < ((n₁ + n₂ : ℕ) : WithBot ℕ) := by
    have hGH : (G * H).natDegree = n₁ + n₂ := by
      rw [hG.natDegree_mul hH, hdG, hdH]
    have hdeq : F.degree = (G * H).degree := by
      rw [Polynomial.degree_eq_natDegree hF.ne_zero,
        Polynomial.degree_eq_natDegree (hG.mul hH).ne_zero]
      exact_mod_cast congrArg (Nat.cast : ℕ → WithBot ℕ) (hdF.trans hGH.symm)
    have hlc : F.leadingCoeff = (G * H).leadingCoeff := by
      rw [hF.leadingCoeff, (hG.mul hH).leadingCoeff]
    have h1 := Polynomial.degree_sub_lt hdeq hF.ne_zero hlc
    rwa [Polynomial.degree_eq_natDegree hF.ne_zero, hdF] at h1
  have hdegE : E.degree < ((n₁ + n₂ : ℕ) : WithBot ℕ) := by
    have h1 : (F - G * H).degree = E.degree := by
      rw [hE, Polynomial.degree_mul, Polynomial.degree_C (pow_ne_zero k hπ.ne_zero),
        zero_add]
    rwa [h1] at hdegFGH
  -- 4. solve `G·w₀ + H·u₀ = C(π^v)·E` with degree bounds
  set u₀ := (q' * E) %ₘ G with hu₀
  set s := (q' * E) /ₘ G with hs
  set w₀ := p' * E + H * s with hw₀
  have hdiv : u₀ + G * s = q' * E := Polynomial.modByMonic_add_div (q' * E) G
  have hsolve : G * w₀ + H * u₀ = Polynomial.C (π ^ v) * E := by
    calc G * w₀ + H * u₀
        = G * (p' * E) + H * (u₀ + G * s) := by rw [hw₀]; ring
      _ = G * (p' * E) + H * (q' * E) := by rw [hdiv]
      _ = (G * p' + H * q') * E := by ring
      _ = Polynomial.C (π ^ v) * E := by rw [hbez]
  have hu₀deg : u₀.degree < (n₁ : WithBot ℕ) := by
    have h1 := Polynomial.degree_modByMonic_lt (q' * E) hG
    rwa [Polynomial.degree_eq_natDegree hG.ne_zero, hdG] at h1
  have hw₀deg : w₀.degree < (n₂ : WithBot ℕ) := by
    rcases eq_or_ne w₀ 0 with h0 | h0
    · rw [h0, Polynomial.degree_zero]
      exact WithBot.bot_lt_coe n₂
    · have hGw : (G * w₀).degree = (n₁ : WithBot ℕ) + w₀.degree := by
        rw [Polynomial.degree_mul, Polynomial.degree_eq_natDegree hG.ne_zero, hdG]
      have hGwlt : (G * w₀).degree < ((n₁ + n₂ : ℕ) : WithBot ℕ) := by
        have h1 : G * w₀ = Polynomial.C (π ^ v) * E - H * u₀ := by
          rw [← hsolve]; ring
        rw [h1]
        refine lt_of_le_of_lt (Polynomial.degree_sub_le _ _) (max_lt ?_ ?_)
        · exact lt_of_le_of_lt (Uniformity.Hensel.degree_C_mul_le_degree _ _) hdegE
        · refine lt_of_le_of_lt (Polynomial.degree_mul_le _ _) ?_
          rw [Polynomial.degree_eq_natDegree hH.ne_zero, hdH]
          have : ((n₁ + n₂ : ℕ) : WithBot ℕ) = (n₂ : WithBot ℕ) + (n₁ : WithBot ℕ) := by
            rw [← Nat.cast_add, Nat.add_comm]
          rw [this]
          exact WithBot.add_lt_add_left (by simp) hu₀deg
      rw [hGw] at hGwlt
      have : ((n₁ + n₂ : ℕ) : WithBot ℕ) = (n₁ : WithBot ℕ) + (n₂ : WithBot ℕ) := by
        rw [← Nat.cast_add]
      rw [this] at hGwlt
      exact (WithBot.add_lt_add_iff_left (by simp)).mp hGwlt
  -- 5. the update
  refine ⟨G + Polynomial.C (π ^ (k - v)) * u₀, H + Polynomial.C (π ^ (k - v)) * w₀,
    ?_, ?_, ?_, ?_, ⟨u₀, by ring⟩, ⟨w₀, by ring⟩, ?_⟩
  · refine hG.add_of_left ?_
    exact lt_of_le_of_lt (Uniformity.Hensel.degree_C_mul_le_degree _ _)
      (by rw [Polynomial.degree_eq_natDegree hG.ne_zero, hdG]; exact hu₀deg)
  · refine hH.add_of_left ?_
    exact lt_of_le_of_lt (Uniformity.Hensel.degree_C_mul_le_degree _ _)
      (by rw [Polynomial.degree_eq_natDegree hH.ne_zero, hdH]; exact hw₀deg)
  · rw [← hdG]
    refine Polynomial.natDegree_add_eq_left_of_degree_lt ?_
    exact lt_of_le_of_lt (Uniformity.Hensel.degree_C_mul_le_degree _ _)
      (by rw [Polynomial.degree_eq_natDegree hG.ne_zero, hdG]; exact hu₀deg)
  · rw [← hdH]
    refine Polynomial.natDegree_add_eq_left_of_degree_lt ?_
    exact lt_of_le_of_lt (Uniformity.Hensel.degree_C_mul_le_degree _ _)
      (by rw [Polynomial.degree_eq_natDegree hH.ne_zero, hdH]; exact hw₀deg)
  · -- the new error: EXACT linear kill, quadratic term at doubled level
    have hsplitk : Polynomial.C (π ^ (k - v)) * Polynomial.C (π ^ v) =
        Polynomial.C (π ^ k) := by
      rw [← Polynomial.C_mul, ← pow_add]
      congr 2
      omega
    have hkill : F - (G + Polynomial.C (π ^ (k - v)) * u₀)
          * (H + Polynomial.C (π ^ (k - v)) * w₀)
        = - (Polynomial.C (π ^ (k - v)) ^ 2 * (u₀ * w₀)) := by
      have hiden : F - (G + Polynomial.C (π ^ (k - v)) * u₀)
            * (H + Polynomial.C (π ^ (k - v)) * w₀)
          = (F - G * H) - Polynomial.C (π ^ (k - v)) * (G * w₀ + H * u₀)
            - Polynomial.C (π ^ (k - v)) ^ 2 * (u₀ * w₀) := by
        ring
      rw [hiden, hsolve, ← mul_assoc, hsplitk, hE]
      ring
    rw [hkill]
    rw [dvd_neg]
    refine dvd_mul_of_dvd_left ?_ _
    rw [← Polynomial.C_pow, ← pow_mul]
    exact map_dvd Polynomial.C (pow_dvd_pow π (by omega : k + 1 ≤ (k - v) * 2))

/-- ★★ **The depth-`v` Newton factorization engine**: a monic `F` congruent mod `π^N`
(`2v + 1 ≤ N`) to a monic product `g·h` whose pinned-size resultant is NOT divisible by
`π^{v+1}` factors EXACTLY, with factors congruent to `(g, h)` mod `π^{N-v}`.
Mechanism: at every Newton stage the resultant of the updated pair keeps its depth
(resultants are congruence-stable), mathlib's Sylvester-adjugate Bezout identity gives a
NORMALIZED witness `G·p + H·q = C(π^{v'})` with the degree bounds, the linear term is
killed EXACTLY, and the quadratic error sits at doubled level; the corpus's adic-limit
engine takes the limit. -/
theorem exists_monic_factorization_of_bezout {π : O} (hπ : Irreducible π)
    {g h F : Polynomial O} {v N n₁ n₂ : ℕ}
    (hg : g.Monic) (hh : h.Monic) (hF : F.Monic)
    (hdg : g.natDegree = n₁) (hdh : h.natDegree = n₂)
    (hdF : F.natDegree = n₁ + n₂) (hpos : n₁ ≠ 0 ∨ n₂ ≠ 0)
    (hN : 2 * v + 1 ≤ N)
    (hres : ¬ π ^ (v + 1) ∣ Polynomial.resultant g h n₁ n₂)
    (hprod : Polynomial.C (π ^ N) ∣ F - g * h) :
    ∃ g' h' : Polynomial O, g'.Monic ∧ h'.Monic ∧ F = g' * h' ∧
      g'.natDegree = n₁ ∧ h'.natDegree = n₂ ∧
      Polynomial.C (π ^ (N - v)) ∣ g' - g ∧ Polynomial.C (π ^ (N - v)) ∣ h' - h := by
  classical
  -- the one-stage improvement, phrased on the invariant package
  have hstep : ∀ (j : ℕ) (P : Polynomial O × Polynomial O),
      (P.1.Monic ∧ P.2.Monic ∧ P.1.natDegree = n₁ ∧ P.2.natDegree = n₂
        ∧ Polynomial.C (π ^ (v + 1)) ∣ P.1 - g ∧ Polynomial.C (π ^ (v + 1)) ∣ P.2 - h
        ∧ Polynomial.C (π ^ (N + j)) ∣ F - P.1 * P.2) →
      ∃ P' : Polynomial O × Polynomial O,
        (P'.1.Monic ∧ P'.2.Monic ∧ P'.1.natDegree = n₁ ∧ P'.2.natDegree = n₂
          ∧ Polynomial.C (π ^ (v + 1)) ∣ P'.1 - g ∧ Polynomial.C (π ^ (v + 1)) ∣ P'.2 - h
          ∧ Polynomial.C (π ^ (N + (j + 1))) ∣ F - P'.1 * P'.2)
        ∧ Polynomial.C (π ^ (N + j - v)) ∣ P'.1 - P.1
        ∧ Polynomial.C (π ^ (N + j - v)) ∣ P'.2 - P.2 := by
    intro j P hP
    obtain ⟨hP1, hP2, hPd1, hPd2, hPc1, hPc2, hPerr⟩ := hP
    obtain ⟨G', H', hG', hH', hdG', hdH', hi1, hi2, herr'⟩ :=
      newton_step hπ hpos hres hP1 hP2 hPd1 hPd2 hPc1 hPc2
        (by omega : 2 * v + 1 ≤ N + j) hF hdF hPerr
    refine ⟨(G', H'), ⟨hG', hH', hdG', hdH', ?_, ?_, herr'⟩, hi1, hi2⟩
    · have h1 : G' - g = (G' - P.1) + (P.1 - g) := by ring
      rw [h1]
      exact dvd_add ((map_dvd Polynomial.C (pow_dvd_pow π (by omega))).trans hi1) hPc1
    · have h1 : H' - h = (H' - P.2) + (P.2 - h) := by ring
      rw [h1]
      exact dvd_add ((map_dvd Polynomial.C (pow_dvd_pow π (by omega))).trans hi2) hPc2
  choose stepF hstepInv hstepIncr1 hstepIncr2 using hstep
  -- the recursive sequence of stage pairs
  let seq : ∀ j : ℕ, {P : Polynomial O × Polynomial O //
      P.1.Monic ∧ P.2.Monic ∧ P.1.natDegree = n₁ ∧ P.2.natDegree = n₂
        ∧ Polynomial.C (π ^ (v + 1)) ∣ P.1 - g ∧ Polynomial.C (π ^ (v + 1)) ∣ P.2 - h
        ∧ Polynomial.C (π ^ (N + j)) ∣ F - P.1 * P.2} := fun j =>
    Nat.rec (motive := fun j => {P : Polynomial O × Polynomial O //
        P.1.Monic ∧ P.2.Monic ∧ P.1.natDegree = n₁ ∧ P.2.natDegree = n₂
          ∧ Polynomial.C (π ^ (v + 1)) ∣ P.1 - g ∧ Polynomial.C (π ^ (v + 1)) ∣ P.2 - h
          ∧ Polynomial.C (π ^ (N + j)) ∣ F - P.1 * P.2})
      ⟨(g, h), hg, hh, hdg, hdh, by simp, by simp, by simpa using hprod⟩
      (fun j Pp => ⟨stepF j Pp.1 Pp.2, hstepInv j Pp.1 Pp.2⟩) j
  have hseqsucc : ∀ j, (seq (j + 1)).1 = stepF j (seq j).1 (seq j).2 := fun j => rfl
  have hincr1 : ∀ j, Polynomial.C (π ^ (N + j - v)) ∣ (seq (j + 1)).1.1 - (seq j).1.1 := by
    intro j
    rw [hseqsucc j]
    exact hstepIncr1 j (seq j).1 (seq j).2
  have hincr2 : ∀ j, Polynomial.C (π ^ (N + j - v)) ∣ (seq (j + 1)).1.2 - (seq j).1.2 := by
    intro j
    rw [hseqsucc j]
    exact hstepIncr2 j (seq j).1 (seq j).2
  have hmon1 : ∀ j, ((seq j).1.1).Monic := fun j => (seq j).2.1
  have hmon2 : ∀ j, ((seq j).1.2).Monic := fun j => (seq j).2.2.1
  have hd1 : ∀ j, ((seq j).1.1).natDegree = n₁ := fun j => (seq j).2.2.2.1
  have hd2 : ∀ j, ((seq j).1.2).natDegree = n₂ := fun j => (seq j).2.2.2.2.1
  have herrj : ∀ j, Polynomial.C (π ^ (N + j)) ∣ F - (seq j).1.1 * (seq j).1.2 :=
    fun j => (seq j).2.2.2.2.2.2.2
  -- the adic limits of the two coordinate sequences
  obtain ⟨Gl, hGldeg, hGlapprox⟩ :=
    Uniformity.Hensel.exists_adicLimit_of_degree_lt (n₁ + 1) (fun j => (seq j).1.1)
      (fun j => by
        rw [Polynomial.degree_eq_natDegree (hmon1 j).ne_zero, hd1 j]
        exact_mod_cast Nat.lt_succ_self n₁)
      (fun j => by
        rw [mem_coeffIdeal_iff_C_dvd hπ]
        exact (map_dvd Polynomial.C (pow_dvd_pow π (by omega : j ≤ N + j - v))).trans
          (hincr1 j))
  obtain ⟨Hl, hHldeg, hHlapprox⟩ :=
    Uniformity.Hensel.exists_adicLimit_of_degree_lt (n₂ + 1) (fun j => (seq j).1.2)
      (fun j => by
        rw [Polynomial.degree_eq_natDegree (hmon2 j).ne_zero, hd2 j]
        exact_mod_cast Nat.lt_succ_self n₂)
      (fun j => by
        rw [mem_coeffIdeal_iff_C_dvd hπ]
        exact (map_dvd Polynomial.C (pow_dvd_pow π (by omega : j ≤ N + j - v))).trans
          (hincr2 j))
  -- the Hausdorff vanishing principle
  have hhaus : ∀ x : O, (∀ j : ℕ, x ∈ (maximalIdeal O) ^ j) → x = 0 := by
    intro x hx
    refine IsHausdorff.haus (inferInstance : IsHausdorff (maximalIdeal O) O) x fun j => ?_
    rw [SModEq.zero, ← Ideal.one_eq_top, Ideal.smul_eq_mul, mul_one]
    exact hx j
  -- monicity and degree of the limits
  have hlimmon : ∀ (n : ℕ) (L : Polynomial O) (Pj : ℕ → Polynomial O),
      (∀ j, (Pj j).Monic) → (∀ j, (Pj j).natDegree = n) →
      L.degree < ((n + 1 : ℕ) : WithBot ℕ) →
      (∀ j, L - Pj j ∈ Uniformity.Hensel.coeffIdeal ((maximalIdeal O) ^ j)) →
      L.Monic ∧ L.natDegree = n := by
    intro n L Pj hPmon hPdeg hLdeg hLapp
    have hcoeff : L.coeff n = 1 := by
      have hz : L.coeff n - 1 = 0 := by
        refine hhaus _ fun j => ?_
        have h1 := (Uniformity.Hensel.mem_coeffIdeal.mp (hLapp j)) n
        rw [Polynomial.coeff_sub] at h1
        have h2 : (Pj j).coeff n = 1 := by
          have h3 := (hPmon j).coeff_natDegree
          rwa [hPdeg j] at h3
        rwa [h2] at h1
      exact sub_eq_zero.mp hz
    have hne : L ≠ 0 := fun h0 => by
      rw [h0, Polynomial.coeff_zero] at hcoeff
      exact one_ne_zero hcoeff.symm
    have hndlt : L.natDegree < n + 1 :=
      (Polynomial.natDegree_lt_iff_degree_lt hne).mpr (by exact_mod_cast hLdeg)
    have hndge : n ≤ L.natDegree :=
      Polynomial.le_natDegree_of_ne_zero (by rw [hcoeff]; exact one_ne_zero)
    have hnd : L.natDegree = n := by omega
    constructor
    · rw [Polynomial.Monic, Polynomial.leadingCoeff, hnd, hcoeff]
    · exact hnd
  obtain ⟨hGlmon, hGlnd⟩ := hlimmon n₁ Gl (fun j => (seq j).1.1) hmon1 hd1 hGldeg hGlapprox
  obtain ⟨hHlmon, hHlnd⟩ := hlimmon n₂ Hl (fun j => (seq j).1.2) hmon2 hd2 hHldeg hHlapprox
  -- the exact factorization
  have hmemj : ∀ j : ℕ, F - Gl * Hl
      ∈ Uniformity.Hensel.coeffIdeal ((maximalIdeal O) ^ j) := by
    intro j
    have h1 : F - Gl * Hl = (F - (seq j).1.1 * (seq j).1.2)
        + ((seq j).1.1 * ((seq j).1.2 - Hl) + (Gl - (seq j).1.1) * Hl * (-1)) := by
      ring
    rw [h1]
    refine Ideal.add_mem _ ?_ (Ideal.add_mem _ ?_ ?_)
    · rw [mem_coeffIdeal_iff_C_dvd hπ]
      exact (map_dvd Polynomial.C (pow_dvd_pow π (by omega : j ≤ N + j))).trans (herrj j)
    · refine Ideal.mul_mem_left _ _ ?_
      have h2 := hHlapprox j
      have h3 : (seq j).1.2 - Hl = -(Hl - (seq j).1.2) := by ring
      rw [h3]
      exact neg_mem h2
    · exact Ideal.mul_mem_right _ _ (Ideal.mul_mem_right _ _ (hGlapprox j))
  have hFeq : F = Gl * Hl := by
    have hz : F - Gl * Hl = 0 := by
      refine Polynomial.ext fun i => ?_
      rw [Polynomial.coeff_zero]
      exact hhaus _ fun j => (Uniformity.Hensel.mem_coeffIdeal.mp (hmemj j)) i
    linear_combination hz
  -- the final congruences: telescoping + the limit approximation at stage `N - v`
  have htel1 : ∀ j, Polynomial.C (π ^ (N - v)) ∣ (seq j).1.1 - g := by
    intro j
    induction j with
    | zero =>
      have h0 : (seq 0).1.1 = g := rfl
      rw [h0, sub_self]
      exact dvd_zero _
    | succ j ih =>
      have h1 : (seq (j + 1)).1.1 - g
          = ((seq (j + 1)).1.1 - (seq j).1.1) + ((seq j).1.1 - g) := by ring
      rw [h1]
      exact dvd_add ((map_dvd Polynomial.C
        (pow_dvd_pow π (by omega : N - v ≤ N + j - v))).trans (hincr1 j)) ih
  have htel2 : ∀ j, Polynomial.C (π ^ (N - v)) ∣ (seq j).1.2 - h := by
    intro j
    induction j with
    | zero =>
      have h0 : (seq 0).1.2 = h := rfl
      rw [h0, sub_self]
      exact dvd_zero _
    | succ j ih =>
      have h1 : (seq (j + 1)).1.2 - h
          = ((seq (j + 1)).1.2 - (seq j).1.2) + ((seq j).1.2 - h) := by ring
      rw [h1]
      exact dvd_add ((map_dvd Polynomial.C
        (pow_dvd_pow π (by omega : N - v ≤ N + j - v))).trans (hincr2 j)) ih
  have hcongGl : Polynomial.C (π ^ (N - v)) ∣ Gl - g := by
    have h2 : Gl - g = (Gl - (seq (N - v)).1.1) + ((seq (N - v)).1.1 - g) := by ring
    rw [h2]
    refine dvd_add ?_ (htel1 (N - v))
    have h3 := hGlapprox (N - v)
    rwa [mem_coeffIdeal_iff_C_dvd hπ] at h3
  have hcongHl : Polynomial.C (π ^ (N - v)) ∣ Hl - h := by
    have h2 : Hl - h = (Hl - (seq (N - v)).1.2) + ((seq (N - v)).1.2 - h) := by ring
    rw [h2]
    refine dvd_add ?_ (htel2 (N - v))
    have h3 := hHlapprox (N - v)
    rwa [mem_coeffIdeal_iff_C_dvd hπ] at h3
  exact ⟨Gl, Hl, hGlmon, hHlmon, hFeq, hGlnd, hHlnd, hcongGl, hcongHl⟩

variable [Finite (ResidueField O)]

/-- ★★ **THE HENSEL LEG DISCHARGED**: for `2v + 1 ≤ N` and `π^{v+1} ∤ Res`, RDC's
`LiftsFactor π v N a₁ a₂` HOLDS — every monic lift of the product class factors through
the pair mod `π^{v+1}` (indeed mod `π^{N-v}`). -/
theorem liftsFactor_of_not_dvd_resultant {π : O} (hπ : Irreducible π)
    {n₁ n₂ N v : ℕ} (hN : 2 * v + 1 ≤ N) (hpos : n₁ ≠ 0 ∨ n₂ ≠ 0)
    {a₁ : Fin n₁ → O} {a₂ : Fin n₂ → O}
    (hres : ¬ π ^ (v + 1) ∣ Polynomial.resultant (monicPoly a₁) (monicPoly a₂) n₁ n₂) :
    LiftsFactor π v N a₁ a₂ := by
  intro Fv hF
  -- the product congruence at level `N`
  have hprod : Polynomial.C (π ^ N) ∣ monicPoly Fv - monicPoly a₁ * monicPoly a₂ := by
    refine (Polynomial.C_dvd_iff_dvd_coeff _ _).mpr fun i => ?_
    have hspan : (maximalIdeal O) ^ N = Ideal.span {π ^ N} := by
      rw [hπ.maximalIdeal_eq, Ideal.span_singleton_pow]
    rcases Nat.lt_or_ge i (n₁ + n₂) with hi | hi
    · have h1 : Ideal.Quotient.mk ((maximalIdeal O) ^ N) (Fv ⟨i, hi⟩)
          = mulClass (proj O n₁ N a₁) (proj O n₂ N a₂) ⟨i, hi⟩ := congrFun hF ⟨i, hi⟩
      have h2 : mulClass (proj O n₁ N a₁) (proj O n₂ N a₂) ⟨i, hi⟩
          = Ideal.Quotient.mk ((maximalIdeal O) ^ N)
              ((monicPoly a₁ * monicPoly a₂).coeff i) := by
        rw [← mulClass_proj]
        rfl
      have h3 : Fv ⟨i, hi⟩ - (monicPoly a₁ * monicPoly a₂).coeff i
          ∈ (maximalIdeal O) ^ N :=
        (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mp (h1.trans h2)
      rw [hspan, Ideal.mem_span_singleton] at h3
      rw [Polynomial.coeff_sub, monicPoly_coeff_lt Fv hi]
      exact h3
    · have hd : (monicPoly a₁ * monicPoly a₂).natDegree = n₁ + n₂ := by
        rw [(monicPoly_monic a₁).natDegree_mul (monicPoly_monic a₂),
          monicPoly_natDegree, monicPoly_natDegree]
      have e1 : (monicPoly Fv).coeff i = (monicPoly a₁ * monicPoly a₂).coeff i := by
        rcases eq_or_lt_of_le hi with heqi | hlt
        · rw [← heqi]
          have hF1 : (monicPoly Fv).coeff (n₁ + n₂) = 1 := by
            have h1 := (monicPoly_monic Fv).coeff_natDegree
            rwa [monicPoly_natDegree] at h1
          have hP1 : (monicPoly a₁ * monicPoly a₂).coeff (n₁ + n₂) = 1 := by
            rw [← hd]
            exact ((monicPoly_monic a₁).mul (monicPoly_monic a₂)).coeff_natDegree
          rw [hF1, hP1]
        · rw [Polynomial.coeff_eq_zero_of_natDegree_lt
              (by rw [monicPoly_natDegree]; exact hlt),
            Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [hd]; exact hlt)]
      rw [Polynomial.coeff_sub, e1, sub_self]
      exact dvd_zero _
  -- fire the Newton engine
  obtain ⟨g', h', hg', hh', hFeq, hdg', hdh', hcg, hch⟩ :=
    exists_monic_factorization_of_bezout hπ (monicPoly_monic a₁) (monicPoly_monic a₂)
      (monicPoly_monic Fv) (monicPoly_natDegree a₁) (monicPoly_natDegree a₂)
      (monicPoly_natDegree Fv) hpos hN hres hprod
  refine ⟨fun i => g'.coeff (i : ℕ), fun i => h'.coeff (i : ℕ), ?_, ?_, ?_⟩
  · rw [Uniformity.Density.IFCG17.monicPoly_coeff_eq_self hg' hdg',
      Uniformity.Density.IFCG17.monicPoly_coeff_eq_self hh' hdh']
    exact hFeq
  · intro i
    have h1 := (Polynomial.C_dvd_iff_dvd_coeff _ _).mp hcg (i : ℕ)
    rw [Polynomial.coeff_sub, monicPoly_coeff_lt a₁ i.isLt] at h1
    exact (pow_dvd_pow π (by omega : v + 1 ≤ N - v)).trans h1
  · intro i
    have h1 := (Polynomial.C_dvd_iff_dvd_coeff _ _).mp hch (i : ℕ)
    rw [Polynomial.coeff_sub, monicPoly_coeff_lt a₂ i.isLt] at h1
    exact (pow_dvd_pow π (by omega : v + 1 ≤ N - v)).trans h1

/-- ★★ **THE DECIDEDNESS TRANSFER, HENSEL LEG PROVED**: at exact depth `v` with
`2v + 1 ≤ N` and shifted-level decided factors, the product class is decided — RDC's
criterion with BOTH legs (uniqueness AND existence) machine-checked. -/
theorem decidedAt_mulClass_of_not_dvd_resultant {π : O} (hπ : Irreducible π)
    {n₁ n₂ N v : ℕ} (hN : 2 * v + 1 ≤ N) (hpos : n₁ ≠ 0 ∨ n₂ ≠ 0)
    {a₁ : Fin n₁ → O} {a₂ : Fin n₂ → O} {σ₁ σ₂ : FactorizationType}
    (hres : ¬ π ^ (v + 1) ∣ Polynomial.resultant (monicPoly a₁) (monicPoly a₂) n₁ n₂)
    (hd₁ : DecidedAt O n₁ σ₁ (N - v) (proj O n₁ (N - v) a₁))
    (hd₂ : DecidedAt O n₂ σ₂ (N - v) (proj O n₂ (N - v) a₂)) :
    DecidedAt O (n₁ + n₂) ⟨σ₁.data + σ₂.data⟩ N
      (mulClass (proj O n₁ N a₁) (proj O n₂ N a₂)) :=
  decidedAt_mulClass_of_liftsFactor hπ
    (exists_bezout_of_not_dvd_resultant hπ
      (monicPoly_natDegree a₁).le (monicPoly_natDegree a₂).le hpos hres)
    (liftsFactor_of_not_dvd_resultant hπ hN hpos hres) hd₁ hd₂

end HenselLeg

/-! ## §5 — the mixDepth-keyed sockets (what the census consumes) and the honest fence

NOT proved here (the exact named remainder of `CollisionLaw`/`StrayLaw`, per the file
docstring): (i) the depth-stratum ROOT COUNTS — with the fiber law each depth-`v`
cluster has exactly `q^v` members, so the graded strata sums of RDC's
`convCount_graded_census` reduce to counting the CLUSTER ROOTS (a level-`(v+1)`
digit-box quantity) per depth; their normalized limits are the remaining engine;
(ii) the DRAINAGE premise — identifying each `pairDepthFiber` with a disjoint union of
`pairNbhd`s requires the fiber members to be decided at the SHIFTED level `N - v`
(exactly the transfer criterion's `hd₁/hd₂` hypothesis genre), which is the
level-stabilization (drainage) of the decided census.  Both are census-side; every
uniqueness/existence/counting mechanism they need is landed in §§1–4. -/

section MixDepthSocket

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)]

/-- The depth instrument reads down to lifts: `π^{mixDepth}` divides the pinned-size
resultant of any lift pair. -/
theorem dvd_resultant_of_mixDepth {π : O} (hπ : Irreducible π) {n₁ n₂ N : ℕ}
    (a₁ : Fin n₁ → O) (a₂ : Fin n₂ → O) :
    π ^ (mixDepth π (proj O n₁ N a₁) (proj O n₂ N a₂))
      ∣ Polynomial.resultant (monicPoly a₁) (monicPoly a₂) n₁ n₂ := by
  have h1 := mixDepth_dvd π (proj O n₁ N a₁) (proj O n₂ N a₂)
  rw [classRes_proj] at h1
  exact (mk_pow_dvd_mk_iff hπ (mixDepth_le π _ _) _).mp h1

/-- Below the frame cap the depth is EXACT: `mixDepth = v < N` forbids `π^{v+1}`. -/
theorem not_dvd_resultant_of_mixDepth_lt {π : O} (hπ : Irreducible π) {n₁ n₂ N v : ℕ}
    {a₁ : Fin n₁ → O} {a₂ : Fin n₂ → O}
    (hd : mixDepth π (proj O n₁ N a₁) (proj O n₂ N a₂) = v) (hvN : v < N) :
    ¬ π ^ (v + 1) ∣ Polynomial.resultant (monicPoly a₁) (monicPoly a₂) n₁ n₂ := by
  intro hdvd
  have h1 : (Ideal.Quotient.mk ((maximalIdeal O) ^ N) (π ^ (v + 1)))
      ∣ classRes (proj O n₁ N a₁) (proj O n₂ N a₂) := by
    rw [classRes_proj]
    exact (mk_pow_dvd_mk_iff hπ (by omega : v + 1 ≤ N) _).mpr hdvd
  have h2 := le_mixDepth π (by omega : v + 1 ≤ N) h1
  omega

/-- ★★ **THE q-POWER FIBER LAW, mixDepth-keyed** (the census socket): a lift pair whose
classes sit at mixing depth exactly `v` below half the frame (`2v + 1 ≤ N`) has pair
neighborhood of size EXACTLY `q^v`. -/
theorem natCard_pairNbhd_of_mixDepth {π : O} (hπ : Irreducible π) {n₁ n₂ N v : ℕ}
    (hN : 2 * v + 1 ≤ N) (hpos : n₁ ≠ 0 ∨ n₂ ≠ 0)
    {a₁ : Fin n₁ → O} {a₂ : Fin n₂ → O}
    (hd : mixDepth π (proj O n₁ N a₁) (proj O n₂ N a₂) = v) :
    Nat.card (pairNbhd π N v a₁ a₂) = residueCard O ^ v := by
  refine natCard_pairNbhd hπ hN hpos ?_ (not_dvd_resultant_of_mixDepth_lt hπ hd (by omega))
  rw [← hd]
  exact dvd_resultant_of_mixDepth hπ a₁ a₂

/-- ★★ **THE DECIDEDNESS TRANSFER, mixDepth-keyed, BOTH LEGS PROVED**: at mixing depth
exactly `v` with `2v + 1 ≤ N`, shifted-level decided factors make the product class
decided at full level — RDC's criterion with the Hensel existence leg discharged by the
Newton engine and the depth read off the class instrument. -/
theorem decidedAt_mulClass_of_mixDepth [IsAdicComplete (maximalIdeal O) O]
    {π : O} (hπ : Irreducible π) {n₁ n₂ N v : ℕ}
    (hN : 2 * v + 1 ≤ N) (hpos : n₁ ≠ 0 ∨ n₂ ≠ 0)
    {a₁ : Fin n₁ → O} {a₂ : Fin n₂ → O} {σ₁ σ₂ : FactorizationType}
    (hd : mixDepth π (proj O n₁ N a₁) (proj O n₂ N a₂) = v)
    (hd₁ : DecidedAt O n₁ σ₁ (N - v) (proj O n₁ (N - v) a₁))
    (hd₂ : DecidedAt O n₂ σ₂ (N - v) (proj O n₂ (N - v) a₂)) :
    DecidedAt O (n₁ + n₂) ⟨σ₁.data + σ₂.data⟩ N
      (mulClass (proj O n₁ N a₁) (proj O n₂ N a₂)) :=
  decidedAt_mulClass_of_not_dvd_resultant hπ hN hpos
    (not_dvd_resultant_of_mixDepth_lt hπ hd (by omega)) hd₁ hd₂

end MixDepthSocket

end Uniformity.Density.IFCG42

end

/-! ## AXCHECK FOOTER — every declaration below expects PURE Lean core
`{propext, Classical.choice, Quot.sound}`: nothing in this file consumes the B.42 cite
(the SDL legs are not touched), the C.33 cites, or `AX_cellRecursion`.  The q-power
fiber law and the Hensel existence leg are Lean-core theorems. -/
#print axioms Uniformity.Density.IFCG42.natCard_quotient_range_smith
#print axioms Uniformity.Density.IFCG42.sylvesterMap_injective
#print axioms Uniformity.Density.IFCG42.natCard_quotient_range_sylvesterMap
#print axioms Uniformity.Density.IFCG42.smul_top_le_range_sylvesterMap
#print axioms Uniformity.Density.IFCG42.natCard_ker_sylvesterMap_quot
#print axioms Uniformity.Density.IFCG42.natCard_pairNbhd
#print axioms Uniformity.Density.IFCG42.exists_monic_factorization_of_bezout
#print axioms Uniformity.Density.IFCG42.liftsFactor_of_not_dvd_resultant
#print axioms Uniformity.Density.IFCG42.decidedAt_mulClass_of_not_dvd_resultant
#print axioms Uniformity.Density.IFCG42.dvd_resultant_of_mixDepth
#print axioms Uniformity.Density.IFCG42.not_dvd_resultant_of_mixDepth_lt
#print axioms Uniformity.Density.IFCG42.natCard_pairNbhd_of_mixDepth
#print axioms Uniformity.Density.IFCG42.decidedAt_mulClass_of_mixDepth
