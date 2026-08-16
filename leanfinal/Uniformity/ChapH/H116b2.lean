/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapH.H116bR

/-!
# Uniformity.ChapH.H116b2 — multiplicity ADDS, and the genre of a planted product

**Chapter H, NODE H.116b2** (`blueprint/CHAP-H_general_induction.md`, AMENDMENT A-H.7 §5).
The first sub-node of the H.116b re-split, and the one that carries the SHARED DEFINITIONAL
CARRIER `plantedPoly` of §§5–8 of that amendment.

* **clause (i) `coeff_level_mul_trailing`** — MULTIPLICITY ADDS.  If `π ^ s` is the exact
  coefficient level of `P₁` with its first unit at abscissa `μ₁`, and `π ^ t` the exact level
  of `P₂` with its first unit at `μ₂`, then `π ^ (s + t)` is the exact level of `P₁ P₂` and
  its first unit sits at `μ₁ + μ₂`.  H116bR §5's landed `not_pow_add_succ_dvd_coeff_mul` is
  exactly the `μ₁ = μ₂ = 0` case (the CONTENT half); this is the MULTIPLICITY half.
* **clause (ii) `plantedPoly_genre`** — THE GENRE OF A PLANTED PRODUCT.

⚠ FENCE A-H.7/F1: nothing in this module builds a map between fibres.

DEPENDS: H.107 (`mem_maximalIdeal_pow_iff_dvd_of_irr`, `resOrd`), H.108 (`betaContent`,
`IsDrainState`), H.109 (`HasChildAt`, `hasChildAt_of_exists`), H.115 (`resSect`, `classSect`),
H.115b (`alphaParent`, `alphaFrame`, `alphaParent_coeff`, `alphaFrame_map_residue`) ·
landed in `H116bR.lean`: `pow_add_dvd_coeff_mul`, `not_pow_add_succ_dvd_coeff_mul`,
`pow_min_dvd_coeff_recentre_alphaParent`, `not_pow_min_succ_dvd_coeff_recentre_alphaParent`,
`recentre_alphaParent_own`, `coeff_zero_recentre_alphaParent_not_dvd`,
`pow_content_dvd_coeff_recentre`, `not_pow_content_succ_dvd_coeff_recentre`,
`betaContent_eq_of_recentre_exact` · mathlib `Polynomial.C_dvd_iff_dvd_coeff`,
`Polynomial.coeff_mul`, `Finset.induction_on`, `Finset.prod_insert`.

**ENVIRONMENT — ENV-H17** + `[IsAdicComplete]` (clause (ii) only) + `π` explicit.

## Status

Sorry-free, axiom-free (Lean core only); footprint printed at the end of the file.
-/

namespace Uniformity.Density.Induction

open IsLocalRing Polynomial

/-! ## 0. Two arithmetic helpers (both re-derived; the H116bR copies are `private`) -/

section Helpers

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

/-- `π ∣ x` is the residue reading of `x`. -/
theorem residue_eq_zero_iff_dvd {π : O} (hπ : Irreducible π) (x : O) :
    residue O x = 0 ↔ π ∣ x := by
  constructor
  · intro h0
    have hmem : x ∈ maximalIdeal O := Ideal.Quotient.eq_zero_iff_mem.1 h0
    have h := (mem_maximalIdeal_pow_iff_dvd_of_irr hπ 1 x).1 (by rwa [pow_one])
    rwa [pow_one] at h
  · intro hd
    refine Ideal.Quotient.eq_zero_iff_mem.2 ?_
    have h := (mem_maximalIdeal_pow_iff_dvd_of_irr hπ 1 x).2 (by rwa [pow_one])
    rwa [pow_one] at h

/-- `π ^ (E + 1)` never divides `π ^ E * U` when `U` is a unit (nonzero residue). -/
theorem not_pow_succ_dvd_pow_mul' {π : O} (hπ : Irreducible π) (E : ℕ) {U : O}
    (hU : residue O U ≠ 0) : ¬ π ^ (E + 1) ∣ π ^ E * U := by
  intro hdvd
  have hcan : π ^ E * π ∣ π ^ E * U := by rw [← pow_succ]; exact hdvd
  exact hU ((residue_eq_zero_iff_dvd hπ U).2
    ((mul_dvd_mul_iff_left (pow_ne_zero E hπ.ne_zero)).1 hcan))

end Helpers

/-! ## 1. H.116b2 (clause i) — MULTIPLICITY ADDS -/

section Trailing

/-- The trailing-coefficient computation over an arbitrary commutative ring: if `f` vanishes
below `μ₁` and `g` below `μ₂`, then `f g` vanishes below `μ₁ + μ₂` and its coefficient there
is the product of the two first coefficients.  (This is mathlib's
`coeff_mul_natTrailingDegree_add_natTrailingDegree` argument, stated at explicit abscissae so
that no `natTrailingDegree` bookkeeping is needed.) -/
theorem coeff_mul_first {R : Type*} [CommRing R] {f g : Polynomial R} {μ₁ μ₂ : ℕ}
    (hf : ∀ j < μ₁, f.coeff j = 0) (hg : ∀ j < μ₂, g.coeff j = 0) :
    (∀ n < μ₁ + μ₂, (f * g).coeff n = 0) ∧
      (f * g).coeff (μ₁ + μ₂) = f.coeff μ₁ * g.coeff μ₂ := by
  classical
  constructor
  · intro n hn
    rw [Polynomial.coeff_mul]
    refine Finset.sum_eq_zero ?_
    rintro ⟨i, j⟩ hij
    rw [Finset.mem_antidiagonal] at hij
    by_cases hi : i < μ₁
    · rw [hf i hi, zero_mul]
    · have hj : j < μ₂ := by omega
      rw [hg j hj, mul_zero]
  · rw [Polynomial.coeff_mul]
    refine Finset.sum_eq_single (μ₁, μ₂) ?_ fun h => (h (Finset.mem_antidiagonal.mpr rfl)).elim
    rintro ⟨i, j⟩ hij hne
    rw [Finset.mem_antidiagonal] at hij
    by_cases hi : i < μ₁
    · rw [hf i hi, zero_mul]
    · by_cases hj : j < μ₂
      · rw [hg j hj, mul_zero]
      · exact absurd (show ((i, j) : ℕ × ℕ) = (μ₁, μ₂) by
          have h1 : i = μ₁ := by omega
          have h2 : j = μ₂ := by omega
          rw [h1, h2]) hne

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

/-- **H.116b2 (clause i) [A-H.7 §5].  MULTIPLICITY ADDS.**  If `π ^ s` is the exact coefficient
level of `P₁` with the first unit at abscissa `μ₁`, and `π ^ t` the exact level of `P₂` with
the first unit at `μ₂`, then `π ^ (s + t)` is the exact level of `P₁ P₂` and its first unit
sits at `μ₁ + μ₂`.

Proof: divide the exact levels out (`C_dvd_iff_dvd_coeff`); the hypotheses say precisely that
the divided reduction of `Pᵢ` vanishes below `μᵢ` and is nonzero at `μᵢ`; `(ResidueField O)[X]`
is a domain, so the product's divided reduction vanishes below `μ₁ + μ₂` and is the (nonzero)
product of the two first coefficients there. -/
theorem coeff_level_mul_trailing {π : O} (hπ : Irreducible π) {s t μ₁ μ₂ : ℕ}
    {P₁ P₂ : Polynomial O}
    (h1 : ∀ j, π ^ s ∣ P₁.coeff j) (h1' : ∀ j < μ₁, π ^ (s + 1) ∣ P₁.coeff j)
    (h1'' : ¬ π ^ (s + 1) ∣ P₁.coeff μ₁)
    (h2 : ∀ j, π ^ t ∣ P₂.coeff j) (h2' : ∀ j < μ₂, π ^ (t + 1) ∣ P₂.coeff j)
    (h2'' : ¬ π ^ (t + 1) ∣ P₂.coeff μ₂) :
    (∀ j, π ^ (s + t) ∣ (P₁ * P₂).coeff j) ∧
      (∀ j < μ₁ + μ₂, π ^ (s + t + 1) ∣ (P₁ * P₂).coeff j) ∧
      ¬ π ^ (s + t + 1) ∣ (P₁ * P₂).coeff (μ₁ + μ₂) := by
  classical
  obtain ⟨F₁, hF₁⟩ := (Polynomial.C_dvd_iff_dvd_coeff (π ^ s) P₁).2 h1
  obtain ⟨F₂, hF₂⟩ := (Polynomial.C_dvd_iff_dvd_coeff (π ^ t) P₂).2 h2
  have hc1 : ∀ j, P₁.coeff j = π ^ s * F₁.coeff j := by
    intro j; rw [hF₁, coeff_C_mul]
  have hc2 : ∀ j, P₂.coeff j = π ^ t * F₂.coeff j := by
    intro j; rw [hF₂, coeff_C_mul]
  -- the two divided reductions, read off the hypotheses
  have hr1 : ∀ j < μ₁, (F₁.map (residue O)).coeff j = 0 := by
    intro j hj
    rw [coeff_map]
    refine (residue_eq_zero_iff_dvd hπ _).2 ?_
    have h := h1' j hj
    rw [hc1 j, pow_succ] at h
    exact (mul_dvd_mul_iff_left (pow_ne_zero s hπ.ne_zero)).1 h
  have hr2 : ∀ j < μ₂, (F₂.map (residue O)).coeff j = 0 := by
    intro j hj
    rw [coeff_map]
    refine (residue_eq_zero_iff_dvd hπ _).2 ?_
    have h := h2' j hj
    rw [hc2 j, pow_succ] at h
    exact (mul_dvd_mul_iff_left (pow_ne_zero t hπ.ne_zero)).1 h
  have hn1 : (F₁.map (residue O)).coeff μ₁ ≠ 0 := by
    rw [coeff_map]
    intro hcon
    refine h1'' ?_
    rw [hc1 μ₁, pow_succ]
    exact mul_dvd_mul_left _ ((residue_eq_zero_iff_dvd hπ _).1 hcon)
  have hn2 : (F₂.map (residue O)).coeff μ₂ ≠ 0 := by
    rw [coeff_map]
    intro hcon
    refine h2'' ?_
    rw [hc2 μ₂, pow_succ]
    exact mul_dvd_mul_left _ ((residue_eq_zero_iff_dvd hπ _).1 hcon)
  obtain ⟨hzero, htop⟩ := coeff_mul_first hr1 hr2
  -- transport back through the reduction of the product
  have hmapmul : (F₁ * F₂).map (residue O)
      = (F₁.map (residue O)) * (F₂.map (residue O)) := Polynomial.map_mul _
  have hFzero : ∀ n < μ₁ + μ₂, π ∣ (F₁ * F₂).coeff n := by
    intro n hn
    refine (residue_eq_zero_iff_dvd hπ _).1 ?_
    have h := hzero n hn
    rw [← hmapmul, coeff_map] at h
    exact h
  have hFtop : residue O ((F₁ * F₂).coeff (μ₁ + μ₂)) ≠ 0 := by
    have h : ((F₁ * F₂).map (residue O)).coeff (μ₁ + μ₂)
        = (F₁.map (residue O)).coeff μ₁ * (F₂.map (residue O)).coeff μ₂ := by
      rw [hmapmul]; exact htop
    rw [coeff_map] at h
    rw [h]
    exact mul_ne_zero hn1 hn2
  have hPQ : P₁ * P₂ = Polynomial.C (π ^ (s + t)) * (F₁ * F₂) := by
    rw [hF₁, hF₂, pow_add, Polynomial.C_mul]; ring
  have hcoeff : ∀ n, (P₁ * P₂).coeff n = π ^ (s + t) * (F₁ * F₂).coeff n := by
    intro n; rw [hPQ, coeff_C_mul]
  refine ⟨fun j => ?_, fun j hj => ?_, ?_⟩
  · rw [hcoeff j]; exact Dvd.intro _ rfl
  · rw [hcoeff j, pow_succ]
    exact mul_dvd_mul_left _ (hFzero j hj)
  · rw [hcoeff (μ₁ + μ₂)]
    exact not_pow_succ_dvd_pow_mul' hπ (s + t) hFtop

/-- **The `Finset`-product form of clause (i).**  Exact levels and first-unit abscissae both
ADD along a finite product. -/
theorem coeff_level_prod_trailing {π : O} (hπ : Irreducible π) {ι : Type*}
    (S : Finset ι) (P : ι → Polynomial O) (s μ : ι → ℕ)
    (h1 : ∀ p ∈ S, ∀ j, π ^ s p ∣ (P p).coeff j)
    (h2 : ∀ p ∈ S, ∀ j < μ p, π ^ (s p + 1) ∣ (P p).coeff j)
    (h3 : ∀ p ∈ S, ¬ π ^ (s p + 1) ∣ (P p).coeff (μ p)) :
    (∀ j, π ^ (∑ p ∈ S, s p) ∣ (∏ p ∈ S, P p).coeff j) ∧
      (∀ j < ∑ p ∈ S, μ p, π ^ ((∑ p ∈ S, s p) + 1) ∣ (∏ p ∈ S, P p).coeff j) ∧
      ¬ π ^ ((∑ p ∈ S, s p) + 1) ∣ (∏ p ∈ S, P p).coeff (∑ p ∈ S, μ p) := by
  classical
  revert h1 h2 h3
  induction S using Finset.induction_on with
  | empty =>
      intro _ _ _
      rw [Finset.prod_empty, Finset.sum_empty, Finset.sum_empty]
      refine ⟨fun j => by rw [pow_zero]; exact one_dvd _, fun j hj => absurd hj (by omega), ?_⟩
      rw [zero_add, pow_one, Polynomial.coeff_one, if_pos rfl]
      exact fun hcon => hπ.not_isUnit (isUnit_of_dvd_one hcon)
  | insert a S ha ih =>
      intro h1 h2 h3
      rw [Finset.prod_insert ha, Finset.sum_insert ha, Finset.sum_insert ha]
      exact coeff_level_mul_trailing hπ
        (h1 a (Finset.mem_insert_self a S))
        (h2 a (Finset.mem_insert_self a S))
        (h3 a (Finset.mem_insert_self a S))
        (ih (fun p hp => h1 p (Finset.mem_insert_of_mem hp))
            (fun p hp => h2 p (Finset.mem_insert_of_mem hp))
            (fun p hp => h3 p (Finset.mem_insert_of_mem hp))).1
        (ih (fun p hp => h1 p (Finset.mem_insert_of_mem hp))
            (fun p hp => h2 p (Finset.mem_insert_of_mem hp))
            (fun p hp => h3 p (Finset.mem_insert_of_mem hp))).2.1
        (ih (fun p hp => h1 p (Finset.mem_insert_of_mem hp))
            (fun p hp => h2 p (Finset.mem_insert_of_mem hp))
            (fun p hp => h3 p (Finset.mem_insert_of_mem hp))).2.2

end Trailing

/-! ## 2. The shared carrier `plantedPoly`, and its elementary shape -/

section Carrier

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

/-- **Every lift of a `ClusterState` is `𝔪`-valued** (for `1 ≤ N`).  The class lies in the
image of `𝔪`, and `𝔪 ^ N ≤ 𝔪` closes the gap between the witness and the lift.  This is what
makes `classSect` usable as a presentation section with no `𝔪`-respecting refinement
(A-H.7 §5's soundness note on the carrier). -/
theorem mem_maximalIdeal_of_proj {n N : ℕ} (hN : 1 ≤ N) (c : ClusterState O n N)
    {a : Fin n → O} (ha : proj O n N a = c.1) (i : Fin n) : a i ∈ maximalIdeal O := by
  obtain ⟨b, hb, hba⟩ :=
    (Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).1 (c.2 i)
  have hmk : Ideal.Quotient.mk ((maximalIdeal O) ^ N) (a i) = c.1 i := congrFun ha i
  have hsub : b - a i ∈ (maximalIdeal O) ^ N := Ideal.Quotient.eq.1 (hba.trans hmk.symm)
  have hsub' : b - a i ∈ maximalIdeal O := Ideal.pow_le_self (by omega) hsub
  have hrw : a i = b - (b - a i) := by ring
  rw [hrw]
  exact Ideal.sub_mem _ hb hsub'

/-- The pinned class lift is `𝔪`-valued. -/
theorem mem_maximalIdeal_classSect {n N : ℕ} (hN : 1 ≤ N) (c : ClusterState O n N) (i : Fin n) :
    classSect O n N c.1 i ∈ maximalIdeal O :=
  mem_maximalIdeal_of_proj hN c (proj_classSect O n N c.1) i

/-- **A-H.7 §5 (THE SHARED CARRIER of H.116b1–H.116b4).**  The PLANTED POLYNOMIAL of a
genre-indexed family `bb` of child presentations against a cofactor presentation `Qc`: the
product of the planted factors `alphaParent π b_p k_p (resSect O z_p)` (H.115b's inverse shear,
at the PINNED centres of A-H.5) times the cofactor's canonical lift.

Presentations are indexed by CLASSES, not by lifts, and that is sound: for `1 ≤ N` every lift
of a `ClusterState` is automatically `𝔪`-valued (`mem_maximalIdeal_of_proj`), so `classSect`
needs no `𝔪`-respecting refinement.  The dependent index `{x // x ∈ L}` (rather than
`∀ p ∈ L`) is deliberate: it is a `Fintype`, which is what makes H.116b4's presentation space
finite. -/
noncomputable def plantedPoly (π : O) {N r : ℕ} (L : Finset (ℕ × ℕ × ResidueField O))
    (bb : ∀ p : {x : ℕ × ℕ × ResidueField O // x ∈ L}, ClusterState O p.1.1 N)
    (Qc : ClusterState O r N) : Polynomial O :=
  (∏ p ∈ L.attach, alphaParent π (classSect O p.1.1 N (bb p).1) p.1.2.1 (resSect O p.1.2.2))
    * monicPoly (classSect O r N Qc.1)

variable (π : O) {N r : ℕ} (L : Finset (ℕ × ℕ × ResidueField O))
  (bb : ∀ p : {x : ℕ × ℕ × ResidueField O // x ∈ L}, ClusterState O p.1.1 N)
  (Qc : ClusterState O r N)

/-- The planted product is monic. -/
theorem plantedPoly_monic : (plantedPoly π L bb Qc).Monic :=
  ((Polynomial.monic_prod_of_monic _ _
    (fun _ _ => alphaParent_monic π _ _ _)).mul (monicPoly_monic _))

/-- The planted product has degree `Σ_p μ_p + r`. -/
theorem plantedPoly_natDegree :
    (plantedPoly π L bb Qc).natDegree = (∑ p ∈ L, p.1) + r := by
  have hprodm : (∏ p ∈ L.attach,
      alphaParent π (classSect O p.1.1 N (bb p).1) p.1.2.1 (resSect O p.1.2.2)).Monic :=
    Polynomial.monic_prod_of_monic _ _ (fun p _ => alphaParent_monic π _ _ _)
  rw [plantedPoly, Polynomial.natDegree_mul hprodm.ne_zero (monicPoly_monic _).ne_zero,
    Polynomial.natDegree_prod _ _ (fun p _ => (alphaParent_monic π _ _ _).ne_zero),
    monicPoly_natDegree]
  congr 1
  rw [Finset.sum_congr rfl (fun p _ => alphaParent_natDegree π _ _ _)]
  exact Finset.sum_attach L (fun q => q.1)

omit [IsDiscreteValuationRing O] in
/-- Reading a monic polynomial's coefficient vector back through `monicPoly` is the identity —
the explicit form of `exists_monicPoly_eq`'s witness. -/
theorem monicPoly_coeff_self {n : ℕ} {f : Polynomial O} (hf : f.Monic) (hd : f.natDegree = n) :
    monicPoly (fun i : Fin n => f.coeff (i : ℕ)) = f := by
  set a : Fin n → O := fun i => f.coeff (i : ℕ) with ha
  refine Polynomial.ext fun i => ?_
  rcases lt_trichotomy i n with hi | hi | hi
  · rw [monicPoly_coeff_lt a hi]
  · subst hi
    have h1 : (monicPoly a).coeff i = 1 := by
      have h := (monicPoly_monic a).coeff_natDegree
      rwa [monicPoly_natDegree] at h
    have h2 : f.coeff i = 1 := by
      have h := hf.coeff_natDegree
      rwa [hd] at h
    rw [h1, h2]
  · rw [coeff_eq_zero_of_natDegree_lt (by rw [monicPoly_natDegree]; omega),
      coeff_eq_zero_of_natDegree_lt (by omega)]

/-- The frame of a planted product splits over the product. -/
theorem plantedPoly_comp (q : Polynomial O) :
    (plantedPoly π L bb Qc).comp q
      = (∏ p ∈ L.attach, (alphaParent π (classSect O p.1.1 N (bb p).1) p.1.2.1
            (resSect O p.1.2.2)).comp q) * ((monicPoly (classSect O r N Qc.1)).comp q) := by
  rw [plantedPoly, Polynomial.mul_comp, Polynomial.prod_comp]

end Carrier

/-! ## 3. The frame profile of a planted factor at its OWN frame -/

section OwnFrame

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

/-- **The planted factor's profile at its OWN slope-and-residue.**  The frame is
`π ^ (μ k) ·` a MONIC degree-`μ` polynomial whose reduction is `X ^ μ`, so every coefficient
below abscissa `μ` carries one more `π` and the coefficient AT `μ` does not.  This is the
`k' = k, z' = z` half of the exact planted profile; the FOREIGN half is H116bR's landed
`coeff_zero_recentre_alphaParent_not_dvd` (abscissa `0`). -/
theorem planted_frame_own {π : O} (hπ : Irreducible π) {μ k : ℕ} {b : Fin μ → O}
    (hb : ∀ i, b i ∈ maximalIdeal O) {ŵ w' : O} {z : ResidueField O}
    (hŵ : residue O ŵ = z) (hw' : residue O w' = z) :
    (∀ j < μ, π ^ (μ * k + 1) ∣
        ((alphaParent π b k ŵ).comp (C (π ^ k) * (X + C w'))).coeff j) ∧
      ¬ π ^ (μ * k + 1) ∣ ((alphaParent π b k ŵ).comp (C (π ^ k) * (X + C w'))).coeff μ := by
  have hG : (alphaParent π b k ŵ).comp (C (π ^ k) * (X + C w'))
      = C (π ^ (μ * k)) * ((alphaFrame b ŵ).comp (X + C w')) := recentre_alphaParent_own b k ŵ w'
  set G : Polynomial O := (alphaFrame b ŵ).comp (X + C w') with hGdef
  have hGmonic : G.Monic :=
    (alphaFrame_monic b ŵ).comp (monic_X_add_C w') (by rw [natDegree_X_add_C]; exact one_ne_zero)
  have hGdeg : G.natDegree = μ := by
    rw [hGdef, natDegree_comp, natDegree_X_add_C, alphaFrame_natDegree, Nat.mul_one]
  have hGmap : G.map (residue O) = X ^ μ := by
    rw [hGdef, Polynomial.map_comp, alphaFrame_map_residue hb ŵ, hŵ, Polynomial.map_add,
      map_X, Polynomial.map_C, hw', pow_comp, sub_comp, X_comp, C_comp]
    congr 1
    ring
  refine ⟨fun j hj => ?_, ?_⟩
  · rw [hG, coeff_C_mul, pow_succ]
    refine mul_dvd_mul_left _ ?_
    refine (residue_eq_zero_iff_dvd hπ _).1 ?_
    have h := congrArg (fun p : Polynomial (ResidueField O) => p.coeff j) hGmap
    simp only [coeff_map, coeff_X_pow, if_neg (Nat.ne_of_lt hj)] at h
    exact h
  · rw [hG, coeff_C_mul]
    have htop : G.coeff μ = 1 := by
      have h := hGmonic.coeff_natDegree
      rwa [hGdeg] at h
    rw [htop]
    exact not_pow_succ_dvd_pow_mul' hπ (μ * k) (by rw [map_one]; exact one_ne_zero)

/-- A polynomial with a UNIT constant term is Bézout-coprime to `X ^ μ` — the residue-level
datum both the genre computation and `monicFactor_congr_of_pow_dvd_sub` consume.  (The witness
is the one `exists_residue_split` builds; it is isolated here because the split itself is not
what this node needs.) -/
theorem isCoprime_X_pow_of_coeff_zero_ne_zero {u : Polynomial (ResidueField O)}
    (hu0 : u.coeff 0 ≠ 0) (μ : ℕ) : IsCoprime (X ^ μ : Polynomial (ResidueField O)) u := by
  refine IsCoprime.pow_left ?_
  refine ⟨-(C (u.coeff 0)⁻¹ * u.divX), C (u.coeff 0)⁻¹, ?_⟩
  have hsplit : X * u.divX + C (u.coeff 0) = u := X_mul_divX_add u
  have hinv : C (u.coeff 0)⁻¹ * C (u.coeff 0) = (1 : Polynomial (ResidueField O)) := by
    rw [← C_mul, inv_mul_cancel₀ hu0, map_one]
  linear_combination (-(C (u.coeff 0)⁻¹)) * hsplit + hinv

end OwnFrame

/-! ## 4. The exact frame profile of a PLANTED PRODUCT -/

section Profile

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

omit [IsDomain O] [IsDiscreteValuationRing O] in
/-- Two exact first-unit abscissae at the same level coincide. -/
theorem abscissa_unique {π : O} {D ν A : ℕ} {F : Polynomial O}
    (h1 : ∀ j < ν, π ^ (D + 1) ∣ F.coeff j) (h2 : ¬ π ^ (D + 1) ∣ F.coeff ν)
    (h3 : ∀ j < A, π ^ (D + 1) ∣ F.coeff j) (h4 : ¬ π ^ (D + 1) ∣ F.coeff A) : ν = A := by
  rcases lt_trichotomy ν A with h | h | h
  · exact absurd (h3 ν h) h2
  · exact h
  · exact absurd (h1 A h) h4

/-- **The COFACTOR's frame abscissa**, packaged with the child event it would witness.  The
`2 ≤ A → HasChildAt` clause is what turns the cofactor's child-freeness (`hQchild`) into the
statement that a planted product has NO child at a frame outside `L`.  The degenerate `r = 0`
cofactor (`monicPoly = 1`, content `0`) sits at abscissa `0`, so the clause is vacuous there —
which is why no `¬ IsDrainState Qc` hypothesis is needed. -/
theorem exists_cofactor_abscissa {π : O} (hπ : Irreducible π) {r N : ℕ} (hN : 1 ≤ N)
    (Qc : ClusterState O r N) (hQnd : r = 0 ∨ ¬ IsDrainState Qc)
    {k' : ℕ} (hk' : 1 ≤ k') {z' : ResidueField O} (hz' : z' ≠ 0) :
    ∃ A : ℕ,
      (∀ j < A, π ^ (betaContent Qc k' + 1) ∣
        ((monicPoly (classSect O r N Qc.1)).comp
          (C (π ^ k') * (X + C (resSect O z')))).coeff j) ∧
      (¬ π ^ (betaContent Qc k' + 1) ∣
        ((monicPoly (classSect O r N Qc.1)).comp
          (C (π ^ k') * (X + C (resSect O z')))).coeff A) ∧
      (2 ≤ A → HasChildAt π Qc A k' z') := by
  classical
  rcases hQnd with rfl | hnd
  · -- the degenerate cofactor: `monicPoly = 1`, content `0`, abscissa `0`
    refine ⟨0, fun j hj => absurd hj (by omega), ?_, fun h2 => absurd h2 (by omega)⟩
    have hQ0 : betaContent Qc k' = 0 := by
      have h := betaContent_le_mul Qc k'
      omega
    have hmp : monicPoly (classSect O 0 N Qc.1) = 1 := by
      rw [monicPoly]; simp
    rw [hQ0, hmp, Polynomial.one_comp, Polynomial.coeff_one, if_pos rfl, zero_add, pow_one]
    exact fun hcon => hπ.not_isUnit (isUnit_of_dvd_one hcon)
  · have hr : 1 ≤ r := by
      by_contra hcon
      exact hnd (isDrainState_of_eq_zero (by omega) Qc)
    have hex : ∃ j, ¬ π ^ (betaContent Qc k' + 1) ∣
        ((monicPoly (classSect O r N Qc.1)).comp
          (C (π ^ k') * (X + C (resSect O z')))).coeff j :=
      not_forall.1 (not_pow_content_succ_dvd_coeff_recentre hπ hr hN Qc hnd k'
        (proj_classSect O r N Qc.1) (resSect O z'))
    refine ⟨Nat.find hex, fun j hj => not_not.1 (Nat.find_min hex hj), Nat.find_spec hex,
      fun h2 => ?_⟩
    exact hasChildAt_of_exists hπ hN hnd h2 hk' hz' (classSect O r N Qc.1) (resSect O z')
      (proj_classSect O r N Qc.1) (residue_resSect O z')
      (pow_content_dvd_coeff_recentre hπ Qc k' (proj_classSect O r N Qc.1) (resSect O z'))
      (fun j hj => not_not.1 (Nat.find_min hex hj)) (Nat.find_spec hex)

/-- **The exact frame profile of a planted product** (A-H.7 §5 clause (ii), steps 1–3).  At an
arbitrary frame `(k', w')` with `residue w' = z' ≠ 0`, the planted product's frame has EXACT
level `Σ_p μ_p · min(k_p, k') + betaContent Qc k'` and its first unit sits at abscissa
`Σ_p μ'_p + A`, where `μ'_p` is `μ_p` at `p`'s OWN frame and `0` at every foreign frame
(hypotheses `hown`/`hfor`) and `A` is the cofactor's abscissa.

The abscissa function `μ'` is passed in rather than written with an `if`, so that the statement
carries no decidability instance; the two evaluation hypotheses pin it completely. -/
theorem plantedPoly_frame_profile {π : O} (hπ : Irreducible π) {N r : ℕ} (hN : 1 ≤ N)
    (L : Finset (ℕ × ℕ × ResidueField O))
    (hLchild : ∀ p ∈ L, 2 ≤ p.1 ∧ 1 ≤ p.2.1 ∧ p.2.2 ≠ 0)
    (bb : ∀ p : {x : ℕ × ℕ × ResidueField O // x ∈ L}, ClusterState O p.1.1 N)
    (Qc : ClusterState O r N)
    {k' : ℕ} {z' : ResidueField O} (hz' : z' ≠ 0) {w' : O} (hw' : residue O w' = z')
    (μ' : {x : ℕ × ℕ × ResidueField O // x ∈ L} → ℕ)
    (hown : ∀ p : {x : ℕ × ℕ × ResidueField O // x ∈ L},
      p.1.2.1 = k' → p.1.2.2 = z' → μ' p = p.1.1)
    (hfor : ∀ p : {x : ℕ × ℕ × ResidueField O // x ∈ L},
      ¬ (p.1.2.1 = k' ∧ p.1.2.2 = z') → μ' p = 0)
    (A : ℕ)
    (hA1 : ∀ j < A, π ^ (betaContent Qc k' + 1) ∣
      ((monicPoly (classSect O r N Qc.1)).comp (C (π ^ k') * (X + C w'))).coeff j)
    (hA2 : ¬ π ^ (betaContent Qc k' + 1) ∣
      ((monicPoly (classSect O r N Qc.1)).comp (C (π ^ k') * (X + C w'))).coeff A) :
    (∀ j, π ^ ((∑ p ∈ L, p.1 * min p.2.1 k') + betaContent Qc k') ∣
        ((plantedPoly π L bb Qc).comp (C (π ^ k') * (X + C w'))).coeff j) ∧
      (∀ j < (∑ p ∈ L.attach, μ' p) + A,
        π ^ ((∑ p ∈ L, p.1 * min p.2.1 k') + betaContent Qc k' + 1) ∣
          ((plantedPoly π L bb Qc).comp (C (π ^ k') * (X + C w'))).coeff j) ∧
      ¬ π ^ ((∑ p ∈ L, p.1 * min p.2.1 k') + betaContent Qc k' + 1) ∣
          ((plantedPoly π L bb Qc).comp (C (π ^ k') * (X + C w'))).coeff
            ((∑ p ∈ L.attach, μ' p) + A) := by
  classical
  have hb : ∀ p : {x : ℕ × ℕ × ResidueField O // x ∈ L},
      ∀ i, classSect O p.1.1 N (bb p).1 i ∈ maximalIdeal O :=
    fun p i => mem_maximalIdeal_classSect hN (bb p) i
  set F : {x : ℕ × ℕ × ResidueField O // x ∈ L} → Polynomial O :=
    fun p => (alphaParent π (classSect O p.1.1 N (bb p).1) p.1.2.1
      (resSect O p.1.2.2)).comp (C (π ^ k') * (X + C w')) with hFdef
  have h1 : ∀ p ∈ L.attach, ∀ j, π ^ (p.1.1 * min p.1.2.1 k') ∣ (F p).coeff j :=
    fun p _ j => pow_min_dvd_coeff_recentre_alphaParent _ _ _ _ _ j
  have h2 : ∀ p ∈ L.attach, ∀ j < μ' p,
      π ^ (p.1.1 * min p.1.2.1 k' + 1) ∣ (F p).coeff j := by
    intro p _ j hj
    by_cases hcase : p.1.2.1 = k' ∧ p.1.2.2 = z'
    · obtain ⟨hk, hzz⟩ := hcase
      rw [hown p hk hzz] at hj
      subst hk
      rw [Nat.min_self]
      exact (planted_frame_own hπ (hb p) (residue_resSect O p.1.2.2)
        (hw'.trans hzz.symm)).1 j hj
    · rw [hfor p hcase] at hj
      omega
  have h3 : ∀ p ∈ L.attach, ¬ π ^ (p.1.1 * min p.1.2.1 k' + 1) ∣ (F p).coeff (μ' p) := by
    intro p _
    by_cases hcase : p.1.2.1 = k' ∧ p.1.2.2 = z'
    · obtain ⟨hk, hzz⟩ := hcase
      rw [hown p hk hzz]
      subst hk
      rw [Nat.min_self]
      exact (planted_frame_own hπ (hb p) (residue_resSect O p.1.2.2)
        (hw'.trans hzz.symm)).2
    · rw [hfor p hcase]
      exact coeff_zero_recentre_alphaParent_not_dvd hπ (hb p)
        (residue_resSect O p.1.2.2) (hLchild p.1 p.2).2.2 hw' hz'
        (fun hcon => hcase ⟨hcon.1.symm, hcon.2.symm⟩)
  obtain ⟨g1, g2, g3⟩ :=
    coeff_level_prod_trailing hπ L.attach F (fun p => p.1.1 * min p.1.2.1 k') μ' h1 h2 h3
  have hQ1 := pow_content_dvd_coeff_recentre hπ Qc k' (proj_classSect O r N Qc.1) w'
  have hkey := coeff_level_mul_trailing hπ g1 g2 g3 hQ1 hA1 hA2
  have hsum : (∑ p ∈ L.attach, p.1.1 * min p.1.2.1 k') = ∑ p ∈ L, p.1 * min p.2.1 k' :=
    Finset.sum_attach L (fun q => q.1 * min q.2.1 k')
  rw [hsum] at hkey
  rw [plantedPoly_comp]
  exact hkey

end Profile

/-! ## 5. H.116b2 (clause ii) — THE GENRE OF A PLANTED PRODUCT -/

section Genre

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [IsAdicComplete (maximalIdeal O) O]

/-- **H.116b2 (clause ii) [A-H.7 §5].  THE GENRE OF A PLANTED PRODUCT.**  Under the three
b-FREE conditions on the cofactor — the product is non-drain, the cofactor carries NO child of
its own, and the cofactor is ROOT-FREE at every frame of `L` — the planted product's child set
is EXACTLY `L`, its content at each child slope is the planted floor plus the cofactor's
content, and its child read at `p` is the presentation `bb p` truncated to the genuine window.

**`hQroot` IS NOT IMPLIED BY `hQchild`** (A-H.7 §2.2, certification check `(e2)`): a cofactor
with a SIMPLE root at `(k_p, z_p)` has no child of its own but pushes the product's
multiplicity there to `μ_p + 1`.  Dropping it makes this theorem FALSE.

PROOF.  §4's `plantedPoly_frame_profile` computes the exact level and the first-unit abscissa
of the product's frame at every frame; `betaContent_eq_of_recentre_exact` turns the level into
the content clause, `hasChildAt_of_exists` turns the abscissa into the child at each `p ∈ L`,
and `abscissa_unique` turns it into the ABSENCE of a child elsewhere (through
`exists_cofactor_abscissa`'s `2 ≤ A → HasChildAt π Qc A k' z'`, refuted by `hQchild`).  The
read clause peels `p`'s planted factor with `alphaParent_recentre` and identifies the monic
degree-`μ_p` factor against `betaChild_spec`'s through `monicFactor_congr_of_pow_dvd_sub`. -/
theorem plantedPoly_genre {π : O} (hπ : Irreducible π) {m N r : ℕ}
    (hm : 2 ≤ m) (hN : 1 ≤ N) (L : Finset (ℕ × ℕ × ResidueField O))
    (hLchild : ∀ p ∈ L, 2 ≤ p.1 ∧ 1 ≤ p.2.1 ∧ p.2.2 ≠ 0)
    (hLsep : ∀ p ∈ L, ∀ p' ∈ L, p.2 = p'.2 → p = p')
    (hdeg : (∑ p ∈ L, p.1) + r = m)
    (bb : ∀ p : {x : ℕ × ℕ × ResidueField O // x ∈ L}, ClusterState O p.1.1 N)
    (Qc : ClusterState O r N)
    (hQchild : ∀ (ν k' : ℕ) (y : ResidueField O), ¬ HasChildAt π Qc ν k' y)
    (hQroot : ∀ p ∈ L, ∀ aQ : Fin r → O, proj O r N aQ = Qc.1 →
      ¬ π ^ (betaContent Qc p.2.1 + 1) ∣
        ((monicPoly aQ).comp (C (π ^ p.2.1) * (X + C (resSect O p.2.2)))).coeff 0)
    (c : ClusterState O m N)
    (hc : proj O m N (fun i : Fin m => (plantedPoly π L bb Qc).coeff (i : ℕ)) = c.1)
    (h0 : ¬ IsDrainState c) :
    (∀ p : ℕ × ℕ × ResidueField O, HasChildAt π c p.1 p.2.1 p.2.2 ↔ p ∈ L) ∧
      (∀ p ∈ L, betaContent c p.2.1
          = (∑ p' ∈ L, p'.1 * min p'.2.1 p.2.1) + betaContent Qc p.2.1) ∧
      (∀ (p : {x : ℕ × ℕ × ResidueField O // x ∈ L})
          (hcp : HasChildAt π c p.1.1 p.1.2.1 p.1.2.2),
        (betaChild π c hcp (N - betaContent c p.1.2.1)).1
          = proj O p.1.1 (N - betaContent c p.1.2.1) (classSect O p.1.1 N (bb p).1)) := by
  classical
  have hm1 : 1 ≤ m := by omega
  have hb : ∀ q : {x : ℕ × ℕ × ResidueField O // x ∈ L},
      ∀ i, classSect O q.1.1 N (bb q).1 i ∈ maximalIdeal O :=
    fun q i => mem_maximalIdeal_classSect hN (bb q) i
  set a : Fin m → O := fun i => (plantedPoly π L bb Qc).coeff (i : ℕ) with hadef
  have hdegP : (plantedPoly π L bb Qc).natDegree = m := by
    rw [plantedPoly_natDegree]; exact hdeg
  have ha : monicPoly a = plantedPoly π L bb Qc :=
    monicPoly_coeff_self (plantedPoly_monic π L bb Qc) hdegP
  -- (0) the cofactor is non-drain unless it is the degenerate `r = 0` one
  have hQnd : r = 0 ∨ ¬ IsDrainState Qc := by
    rcases Nat.eq_zero_or_pos r with hr | hr
    · exact Or.inl hr
    · refine Or.inr fun hd => h0 ?_
      refine (isDrainState_iff (by omega) c).2 ?_
      have h1 : Qc.1 ⟨0, hr⟩ = 0 := (isDrainState_iff hr Qc).1 hd
      have h2 : Ideal.Quotient.mk ((maximalIdeal O) ^ N) (classSect O r N Qc.1 ⟨0, hr⟩) = 0 := by
        have hq := congrFun (proj_classSect O r N Qc.1) (⟨0, hr⟩ : Fin r)
        rw [h1] at hq
        exact hq
      have h3 : π ^ N ∣ classSect O r N Qc.1 ⟨0, hr⟩ :=
        (mem_maximalIdeal_pow_iff_dvd_of_irr hπ N _).1 (Ideal.Quotient.eq_zero_iff_mem.1 h2)
      have h6 : π ^ N ∣ (plantedPoly π L bb Qc).coeff 0 := by
        rw [plantedPoly, Polynomial.mul_coeff_zero,
          monicPoly_coeff_lt (classSect O r N Qc.1) hr]
        exact Dvd.dvd.mul_left h3 _
      have h7 : c.1 ⟨0, by omega⟩
          = Ideal.Quotient.mk _ ((plantedPoly π L bb Qc).coeff 0) :=
        (congrFun hc ⟨0, by omega⟩).symm
      rw [h7]
      exact Ideal.Quotient.eq_zero_iff_mem.2 ((mem_maximalIdeal_pow_iff_dvd_of_irr hπ N _).2 h6)
  -- (1) the OWN-frame package at every member of `L`
  have hOwn : ∀ (μ₀ k' : ℕ) (z' : ResidueField O), (μ₀, k', z') ∈ L →
      betaContent c k' = (∑ p' ∈ L, p'.1 * min p'.2.1 k') + betaContent Qc k' ∧
      (∀ j, π ^ betaContent c k' ∣
        ((monicPoly a).comp (C (π ^ k') * (X + C (resSect O z')))).coeff j) ∧
      (∀ j < μ₀, π ^ (betaContent c k' + 1) ∣
        ((monicPoly a).comp (C (π ^ k') * (X + C (resSect O z')))).coeff j) ∧
      ¬ π ^ (betaContent c k' + 1) ∣
        ((monicPoly a).comp (C (π ^ k') * (X + C (resSect O z')))).coeff μ₀ := by
    intro μ₀ k' z' hmem
    have hz0 : z' ≠ 0 := (hLchild _ hmem).2.2
    set μ' : {x : ℕ × ℕ × ResidueField O // x ∈ L} → ℕ :=
      fun q => if q.1 = (μ₀, k', z') then q.1.1 else 0 with hμ'def
    have hown : ∀ q : {x : ℕ × ℕ × ResidueField O // x ∈ L},
        q.1.2.1 = k' → q.1.2.2 = z' → μ' q = q.1.1 := by
      intro q h1 h2
      have heq : q.1 = (μ₀, k', z') := by
        refine hLsep q.1 q.2 (μ₀, k', z') hmem ?_
        rw [show q.1.2 = (q.1.2.1, q.1.2.2) from rfl, h1, h2]
      rw [hμ'def]
      simp only [heq, if_pos]
    have hfor : ∀ q : {x : ℕ × ℕ × ResidueField O // x ∈ L},
        ¬ (q.1.2.1 = k' ∧ q.1.2.2 = z') → μ' q = 0 := by
      intro q hq
      have hne : q.1 ≠ (μ₀, k', z') := by
        intro heq
        exact hq ⟨by rw [heq], by rw [heq]⟩
      rw [hμ'def]
      simp [hne]
    have hsum : (∑ q ∈ L.attach, μ' q) = μ₀ := by
      rw [Finset.sum_eq_single_of_mem (⟨(μ₀, k', z'), hmem⟩ :
          {x : ℕ × ℕ × ResidueField O // x ∈ L}) (Finset.mem_attach _ _) ?_]
      · rw [hμ'def]; simp
      · intro q _ hq
        have hne : q.1 ≠ (μ₀, k', z') := fun heq => hq (Subtype.ext heq)
        rw [hμ'def]
        simp [hne]
    obtain ⟨g1, g2, g3⟩ := plantedPoly_frame_profile hπ hN L hLchild bb Qc hz0
      (residue_resSect O z') μ' hown hfor 0 (fun j hj => absurd hj (by omega))
      (hQroot (μ₀, k', z') hmem (classSect O r N Qc.1) (proj_classSect O r N Qc.1))
    rw [hsum, Nat.add_zero] at g2 g3
    rw [← ha] at g1 g2 g3
    have hD : betaContent c k' = (∑ p' ∈ L, p'.1 * min p'.2.1 k') + betaContent Qc k' :=
      betaContent_eq_of_recentre_exact hπ hm1 hN c h0 k' hc (resSect O z') g1
        (fun hall => g3 (hall _))
    exact ⟨hD, by rw [hD]; exact g1, by rw [hD]; exact g2, by rw [hD]; exact g3⟩
  -- (2) no child at a frame outside `L`
  have hForeign : ∀ (k' : ℕ), 1 ≤ k' → ∀ (z' : ResidueField O), z' ≠ 0 →
      (∀ μ₀, (μ₀, k', z') ∉ L) → ∀ ν, ¬ HasChildAt π c ν k' z' := by
    intro k' hk1 z' hz0 hnot ν hch
    obtain ⟨hν2, -, -, hall⟩ := hch
    obtain ⟨c1, c2, c3⟩ := hall a (resSect O z') hc (residue_resSect O z')
    obtain ⟨A, hA1, hA2, hAchild⟩ := exists_cofactor_abscissa hπ hN Qc hQnd hk1 hz0
    set μ' : {x : ℕ × ℕ × ResidueField O // x ∈ L} → ℕ := fun _ => 0 with hμ'def
    have hown : ∀ q : {x : ℕ × ℕ × ResidueField O // x ∈ L},
        q.1.2.1 = k' → q.1.2.2 = z' → μ' q = q.1.1 := by
      intro q h1 h2
      refine absurd ?_ (hnot q.1.1)
      rw [show ((q.1.1, k', z') : ℕ × ℕ × ResidueField O)
        = (q.1.1, q.1.2.1, q.1.2.2) from by rw [h1, h2]]
      exact q.2
    have hfor : ∀ q : {x : ℕ × ℕ × ResidueField O // x ∈ L},
        ¬ (q.1.2.1 = k' ∧ q.1.2.2 = z') → μ' q = 0 := fun _ _ => rfl
    obtain ⟨g1, g2, g3⟩ := plantedPoly_frame_profile hπ hN L hLchild bb Qc hz0
      (residue_resSect O z') μ' hown hfor A hA1 hA2
    rw [hμ'def, Finset.sum_const_zero, Nat.zero_add] at g2 g3
    rw [← ha] at g1 g2 g3
    have hD : betaContent c k' = (∑ p' ∈ L, p'.1 * min p'.2.1 k') + betaContent Qc k' :=
      betaContent_eq_of_recentre_exact hπ hm1 hN c h0 k' hc (resSect O z') g1
        (fun hall => g3 (hall _))
    rw [← hD] at g2 g3
    have hνA : ν = A := abscissa_unique c2 c3 g2 g3
    exact hQchild A k' z' (hAchild (by omega))
  -- (3) the child set is EXACTLY `L`
  have hiff : ∀ p : ℕ × ℕ × ResidueField O, HasChildAt π c p.1 p.2.1 p.2.2 ↔ p ∈ L := by
    intro p
    constructor
    · intro hch
      by_cases hex : ∃ μ₀, (μ₀, p.2.1, p.2.2) ∈ L
      · obtain ⟨μ₀, hμ₀⟩ := hex
        obtain ⟨-, -, g2, g3⟩ := hOwn μ₀ p.2.1 p.2.2 hμ₀
        obtain ⟨-, -, -, hall⟩ := hch
        obtain ⟨-, c2, c3⟩ := hall a (resSect O p.2.2) hc (residue_resSect O p.2.2)
        have hpe : p.1 = μ₀ := abscissa_unique c2 c3 g2 g3
        rw [show p = (μ₀, p.2.1, p.2.2) from by rw [← hpe]]
        exact hμ₀
      · exact absurd hch (hForeign p.2.1 hch.2.1 p.2.2 hch.2.2.1
          (fun μ₀ hmem => hex ⟨μ₀, hmem⟩) p.1)
    · intro hp
      obtain ⟨-, g1, g2, g3⟩ := hOwn p.1 p.2.1 p.2.2 (by
        rw [show ((p.1, p.2.1, p.2.2) : ℕ × ℕ × ResidueField O) = p from rfl]; exact hp)
      exact hasChildAt_of_exists hπ hN h0 (hLchild p hp).1 (hLchild p hp).2.1
        (hLchild p hp).2.2 a (resSect O p.2.2) hc (residue_resSect O p.2.2) g1 g2 g3
  refine ⟨hiff, fun p hp => (hOwn p.1 p.2.1 p.2.2 (by
    rw [show ((p.1, p.2.1, p.2.2) : ℕ × ℕ × ResidueField O) = p from rfl]; exact hp)).1, ?_⟩
  -- (4) THE READ: the child at `p` is the presentation `bb p`, truncated
  intro p hcp
  set k := p.1.2.1 with hkdef
  set z := p.1.2.2 with hzdef
  set D := betaContent c k with hDdef
  set bp := classSect O p.1.1 N (bb p).1 with hbpdef
  -- the description's factorization
  obtain ⟨b₁, H₁, hb₁mem, hb₁eq, hb₁proj⟩ := betaChild_spec hπ hm hN c hcp h0 a hc
  -- the planted factorization at `p`'s own frame
  set Fq : {x : ℕ × ℕ × ResidueField O // x ∈ L} → Polynomial O :=
    fun q => (alphaParent π (classSect O q.1.1 N (bb q).1) q.1.2.1
      (resSect O q.1.2.2)).comp (C (π ^ k) * (X + C (resSect O z))) with hFqdef
  have hforeign : ∀ q ∈ (L.attach).erase p, ¬ (q.1.2.1 = k ∧ q.1.2.2 = z) := by
    intro q hq hcase
    refine (Finset.mem_erase.1 hq).1 (Subtype.ext (hLsep q.1 q.2 p.1 p.2 ?_))
    rw [show q.1.2 = (q.1.2.1, q.1.2.2) from rfl, show p.1.2 = (p.1.2.1, p.1.2.2) from rfl,
      hcase.1, hcase.2]
  obtain ⟨e1, e2, e3⟩ := coeff_level_prod_trailing hπ ((L.attach).erase p) Fq
    (fun q => q.1.1 * min q.1.2.1 k) (fun _ => 0)
    (fun q _ j => pow_min_dvd_coeff_recentre_alphaParent _ _ _ _ _ j)
    (fun q _ j hj => absurd hj (by omega))
    (fun q hq => coeff_zero_recentre_alphaParent_not_dvd hπ (hb q)
      (residue_resSect O q.1.2.2) (hLchild q.1 q.2).2.2 (residue_resSect O z)
      (hLchild p.1 p.2).2.2 (fun hcon => hforeign q hq ⟨hcon.1.symm, hcon.2.symm⟩))
  rw [Finset.sum_const_zero] at e2 e3
  obtain ⟨f1, -, f3⟩ := coeff_level_mul_trailing hπ e1 e2 e3
    (pow_content_dvd_coeff_recentre hπ Qc k (proj_classSect O r N Qc.1) (resSect O z))
    (fun j hj => absurd hj (by omega))
    (hQroot p.1 p.2 (classSect O r N Qc.1) (proj_classSect O r N Qc.1))
  set T := (∑ q ∈ (L.attach).erase p, q.1.1 * min q.1.2.1 k) + betaContent Qc k with hTdef
  obtain ⟨H', hH'⟩ := (Polynomial.C_dvd_iff_dvd_coeff (π ^ T) _).2 f1
  have hH'0 : (H'.map (residue O)).coeff 0 ≠ 0 := by
    rw [coeff_map]
    intro hcon
    refine f3 ?_
    rw [Nat.add_zero, hH', coeff_C_mul, pow_succ]
    exact mul_dvd_mul_left _ ((residue_eq_zero_iff_dvd hπ _).1 hcon)
  -- the two levels agree
  have hDT : D = p.1.1 * k + T := by
    obtain ⟨hD0, -, -, -⟩ := hOwn p.1.1 k z (by
      rw [hkdef, hzdef, show ((p.1.1, p.1.2.1, p.1.2.2) : ℕ × ℕ × ResidueField O) = p.1 from rfl]
      exact p.2)
    rw [hDdef, hD0, hTdef, ← Finset.sum_attach L (fun q => q.1 * min q.2.1 k),
      ← Finset.add_sum_erase L.attach (fun q => q.1.1 * min q.1.2.1 k) (Finset.mem_attach _ p),
      ← hkdef, Nat.min_self]
    omega
  have hfac : (monicPoly a).comp (C (π ^ k) * (X + C (resSect O z)))
      = C (π ^ D) * (monicPoly bp * H') := by
    have hsplit : (monicPoly a).comp (C (π ^ k) * (X + C (resSect O z)))
        = (C (π ^ (p.1.1 * k)) * monicPoly bp) * (C (π ^ T) * H') := by
      rw [ha, plantedPoly_comp, ← Finset.mul_prod_erase L.attach Fq (Finset.mem_attach _ p),
        mul_assoc, hH']
      congr 1
      exact alphaParent_recentre π bp k (resSect O z)
    have hCsplit : (C (π ^ D) : Polynomial O) = C (π ^ (p.1.1 * k)) * C (π ^ T) := by
      rw [hDT, pow_add π (p.1.1 * k) T, C_mul]
    rw [hsplit, hCsplit]
    ring
  -- the two monic factors agree to level `π ^ (N − D)`
  have hcancel : monicPoly bp * H' = monicPoly b₁ * H₁ := by
    have hCne : (C (π ^ D) : Polynomial O) ≠ 0 := by
      simpa using pow_ne_zero D hπ.ne_zero
    refine mul_left_cancel₀ hCne ?_
    rw [← hfac, hb₁eq]
  have hcongr := monicFactor_congr_of_pow_dvd_sub hπ (monicPoly_monic bp) (monicPoly_monic b₁)
    (monicPoly_natDegree bp) (monicPoly_natDegree b₁) (monicPoly_map_residue hb₁mem)
    (isCoprime_X_pow_of_coeff_zero_ne_zero hH'0 p.1.1) (s := N - D)
    (fun j => by rw [hcancel, sub_self]; exact dvd_zero _)
  rw [← hb₁proj]
  refine ((proj_eq_iff_pow_dvd hπ bp b₁).2 fun i => ?_).symm
  have h := hcongr (i : ℕ)
  rwa [coeff_sub, monicPoly_coeff_lt bp i.isLt, monicPoly_coeff_lt b₁ i.isLt] at h

end Genre

end Uniformity.Density.Induction

/-! ## 6. Statement pins — the two signed theorems and the signed carrier, verbatim

Re-typed from `leanspec/Leanspec/ChapH.lean` (`LeanspecH17`, A-H.7 §5) with the section
`variable`s spelled out, and discharged by the landed declarations.  A drift in any binder,
implicit/explicit marker, or hypothesis would break these. -/

section Pins

open Uniformity.Density Uniformity.Density.Induction Polynomial IsLocalRing

/-- The signed carrier, verbatim. -/
noncomputable example {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (π : O) {N r : ℕ} (L : Finset (ℕ × ℕ × ResidueField O))
    (bb : ∀ p : {x : ℕ × ℕ × ResidueField O // x ∈ L}, ClusterState O p.1.1 N)
    (Qc : ClusterState O r N) : Polynomial O :=
  plantedPoly π L bb Qc

/-- H.116b2 clause (i), verbatim. -/
example {O : Type*} [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] {π : O} (hπ : Irreducible π) {s t μ₁ μ₂ : ℕ}
    {P₁ P₂ : Polynomial O}
    (h1 : ∀ j, π ^ s ∣ P₁.coeff j) (h1' : ∀ j < μ₁, π ^ (s + 1) ∣ P₁.coeff j)
    (h1'' : ¬ π ^ (s + 1) ∣ P₁.coeff μ₁)
    (h2 : ∀ j, π ^ t ∣ P₂.coeff j) (h2' : ∀ j < μ₂, π ^ (t + 1) ∣ P₂.coeff j)
    (h2'' : ¬ π ^ (t + 1) ∣ P₂.coeff μ₂) :
    (∀ j, π ^ (s + t) ∣ (P₁ * P₂).coeff j) ∧
      (∀ j < μ₁ + μ₂, π ^ (s + t + 1) ∣ (P₁ * P₂).coeff j) ∧
      ¬ π ^ (s + t + 1) ∣ (P₁ * P₂).coeff (μ₁ + μ₂) :=
  coeff_level_mul_trailing hπ h1 h1' h1'' h2 h2' h2''

/-- H.116b2 clause (ii), verbatim. -/
example {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [IsAdicComplete (maximalIdeal O) O] {π : O} (hπ : Irreducible π) {m N r : ℕ}
    (hm : 2 ≤ m) (hN : 1 ≤ N) (L : Finset (ℕ × ℕ × ResidueField O))
    (hLchild : ∀ p ∈ L, 2 ≤ p.1 ∧ 1 ≤ p.2.1 ∧ p.2.2 ≠ 0)
    (hLsep : ∀ p ∈ L, ∀ p' ∈ L, p.2 = p'.2 → p = p')
    (hdeg : (∑ p ∈ L, p.1) + r = m)
    (bb : ∀ p : {x : ℕ × ℕ × ResidueField O // x ∈ L}, ClusterState O p.1.1 N)
    (Qc : ClusterState O r N)
    (hQchild : ∀ (ν k' : ℕ) (y : ResidueField O), ¬ HasChildAt π Qc ν k' y)
    (hQroot : ∀ p ∈ L, ∀ aQ : Fin r → O, proj O r N aQ = Qc.1 →
      ¬ π ^ (betaContent Qc p.2.1 + 1) ∣
        ((monicPoly aQ).comp (C (π ^ p.2.1) * (X + C (resSect O p.2.2)))).coeff 0)
    (c : ClusterState O m N)
    (hc : proj O m N (fun i : Fin m => (plantedPoly π L bb Qc).coeff (i : ℕ)) = c.1)
    (h0 : ¬ IsDrainState c) :
    (∀ p : ℕ × ℕ × ResidueField O, HasChildAt π c p.1 p.2.1 p.2.2 ↔ p ∈ L) ∧
      (∀ p ∈ L, betaContent c p.2.1
          = (∑ p' ∈ L, p'.1 * min p'.2.1 p.2.1) + betaContent Qc p.2.1) ∧
      (∀ (p : {x : ℕ × ℕ × ResidueField O // x ∈ L})
          (hcp : HasChildAt π c p.1.1 p.1.2.1 p.1.2.2),
        (betaChild π c hcp (N - betaContent c p.1.2.1)).1
          = proj O p.1.1 (N - betaContent c p.1.2.1) (classSect O p.1.1 N (bb p).1)) :=
  plantedPoly_genre hπ hm hN L hLchild hLsep hdeg bb Qc hQchild hQroot c hc h0

end Pins

/-! ## Axiom footprint (§1–§5) -/

section AxCheck

#print axioms Uniformity.Density.Induction.coeff_mul_first
#print axioms Uniformity.Density.Induction.coeff_level_mul_trailing
#print axioms Uniformity.Density.Induction.coeff_level_prod_trailing
#print axioms Uniformity.Density.Induction.mem_maximalIdeal_of_proj
#print axioms Uniformity.Density.Induction.plantedPoly
#print axioms Uniformity.Density.Induction.plantedPoly_monic
#print axioms Uniformity.Density.Induction.plantedPoly_natDegree
#print axioms Uniformity.Density.Induction.monicPoly_coeff_self
#print axioms Uniformity.Density.Induction.plantedPoly_comp
#print axioms Uniformity.Density.Induction.planted_frame_own
#print axioms Uniformity.Density.Induction.isCoprime_X_pow_of_coeff_zero_ne_zero
#print axioms Uniformity.Density.Induction.abscissa_unique
#print axioms Uniformity.Density.Induction.exists_cofactor_abscissa
#print axioms Uniformity.Density.Induction.plantedPoly_frame_profile
#print axioms Uniformity.Density.Induction.plantedPoly_genre

end AxCheck
