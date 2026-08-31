/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.Density.TypeOfFaithful
import Uniformity.Density.NormLeaves
import Uniformity.Density.InertLeaf
import Uniformity.Quarry.AdjoinRootDVR
import Uniformity.ChapI.IFCG39

/-!
# IFCG76 — UNIT CUR: the currency lemma (`inertiaDegOf` = the true residue degree)

**Charge.** Caveat A of the consolidated FGMN cite package (`I10CitePkg.lean`): the corpus's
`(e, f)` currency is the ORDER's gcd read — `inertiaDegOf h` = gcd of `addVal ∘ Algebra.norm`
over `O[x]/(h)` — while the source's `f` is the FIELD invariant.  This file proves the
identification **off the maximal locus**: `TypeOfFaithful.lean` landed
`inertiaDegOf g = (maximalIdeal (AdjoinRoot g)).inertiaDeg' O` under the hypothesis that the
monogenic order `AdjoinRoot g` is itself a DVR (the maximal order); here that hypothesis is
replaced by a *closure realization* — an injective `O`-algebra embedding of `AdjoinRoot g`
into ANY rank-`deg g` free DVR `B` (mathematically: `B = O_L`, the integral closure).

**The mechanism (all Lean-core, no completeness, no cite):**

1. *Norm transport* (§1): an injective `O`-algebra map `ι` between free `O`-algebras of the
   same finite rank preserves `Algebra.norm` EXACTLY — conjugate the multiplication matrices
   through the (nonsingular) matrix of `ι` and cancel its determinant in the domain `O`.
2. *The adjugate conductor* (§1): `det(ι) • B ⊆ range ι` — Cramer's identity
   `M * adjugate M = det M • 1` read through the bases.  No integral-closure theory, no
   torsion modules: the conductor witness is an explicit matrix adjugate.
3. *The squeeze* (§2–§3): with `f₀ := v(N ϖ_B)`,
   `f₀ ∣ (every norm-valuation of the order)` transports along 1., while the conductor
   elements `ι⁻¹(det(ι) • ϖ^k)`, `k = 1, 2`, have norm-valuations `n·v(det) + k·f₀`, whose
   difference `f₀` is divisible by the gcd.  Hence `inertiaDegOf g = f₀`, and the
   `TypeOfFaithful` endgame (ramification data + the quarried fundamental identity
   `e·f = finrank`) pins `f₀ = (maximalIdeal B).inertiaDeg' O`, the CLASSICAL residue degree.

**Formulation finding (recorded honestly).**  The charge's candidate corpus-internal witness
form `∃ P, addVal (norm P) = inertiaDegOf h` (the attained gcd) is FALSE: the corpus's own
recorded example (`TypeOf.lean` docstring, UNIFORMITY-P2) `h = X² − π³` over `ℤ₃` has
norm-valuation set `{2, 3, 4, …}` with gcd `1` never attained.  More: ANY corpus-internal
∃-witness form built from norm-valuation clauses alone is extensionally equivalent to the gcd
read itself (`w := v∘N / gcd` is always a tautological witness), so no re-wording eliminates
caveat A — the elimination must be a THEOREM tying the gcd to the classical field invariant.
That theorem is `inertiaDegOf_eq_inertiaDeg'_of_closure` below; its one hypothesis beyond the
landed corpus is the closure realization (`DVRClosure`), which is the textbook fact "the
integral closure of a complete DVR in a finite extension is a DVR, finite free of full rank"
(Serre, *Corps Locaux*, ch. II §2, Prop. 3 — no separability needed over a COMPLETE base) —
a far cleaner future cite/proof target than the per-equality trusted reading of caveat A.

**Source-side carrier (the addendum's ask).**  `DVRClosure g` bundles a realization;
`HasResidueDegree g f` says some realization has classical residue degree `f`.  The BRIDGE
`inertiaDegOf_eq_of_hasResidueDegree : HasResidueDegree g f → inertiaDegOf g = f` is the
proved translation from the source's currency into the corpus's; `hasResidueDegree_unique`
makes `HasResidueDegree` a genuine invariant.  A follow-up can restate the cite package's
legs with `HasResidueDegree`/`inertiaDeg'` conclusions (the authors' own currency) and derive
the current gcd-currency legs as corollaries of the bridge.

**Anchors (consistency teeth, no cite):** Eisenstein — `inertiaDegOf = 1` at every degree
(extracted standalone from CN-20's inline proof) with the classical mirror
`(ramificationIdx', inertiaDeg') = (n, 1)` and the `eisKey` instance `efPair = (e', 1)`;
unramified — `inertiaDegOf = deg` (from InertLeaf's Nakayama divisibility) with
`HasResidueDegree g (deg g)`.

**Status.** Sorry-free, Lean-core only (see the AxCheck footer).
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

noncomputable section

namespace Uniformity.Density.IFCG76

open IsLocalRing Polynomial
open Module (Basis)
open Uniformity.Density.IFCG39 (eisKey eisKey_monic eisKey_natDegree)

/-! ## §1 — Norm transport along an injective algebra embedding

`O` any domain, `A`, `B` two `O`-algebras free of the same finite rank `n`, and
`ι : A →ₐ[O] B` injective.  Then (i) the matrix of `ι` has nonzero determinant,
(ii) `Algebra.norm O (ι x) = Algebra.norm O x`, and (iii) `det(ι) • B ⊆ range ι`. -/

section NormTransport

variable {O : Type*} [CommRing O] [IsDomain O]
variable {A B : Type*} [CommRing A] [CommRing B] [Algebra O A] [Algebra O B]
variable {n : ℕ}

/-- **(i) The matrix of an injective map between free modules of equal rank is nonsingular.**
(`Matrix.exists_mulVec_eq_zero_iff` over the domain `O`.) -/
theorem det_toMatrix_ne_zero (bA : Basis (Fin n) O A) (bB : Basis (Fin n) O B)
    (ι : A →ₐ[O] B) (hι : Function.Injective ι) :
    (LinearMap.toMatrix bA bB ι.toLinearMap).det ≠ 0 := by
  intro h0
  obtain ⟨v, hv0, hMv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h0
  set a := bA.equivFun.symm v with ha_def
  have hrepr : ⇑(bA.repr a) = v := by
    rw [ha_def, ← Basis.equivFun_apply, LinearEquiv.apply_symm_apply]
  have hkey := LinearMap.toMatrix_mulVec_repr bA bB ι.toLinearMap a
  rw [AlgHom.toLinearMap_apply, hrepr] at hkey
  have hone : ⇑(bB.repr (ι a)) = 0 := by rw [← hkey]; exact hMv
  have hzero : bB.repr (ι a) = 0 := by
    ext i
    simpa using congrFun hone i
  have hia : ι a = 0 := bB.repr.map_eq_zero_iff.1 hzero
  have ha0 : a = 0 := hι (by rw [hia, map_zero])
  rw [ha_def] at ha0
  exact hv0 (bA.equivFun.symm.map_eq_zero_iff.1 ha0)

/-- **(ii) Norm transport.**  An injective `O`-algebra map between free `O`-algebras of the
same rank preserves the norm exactly: conjugate `lmul x` through the matrix of `ι` and cancel
its (nonzero) determinant.  No localization, no fraction fields. -/
theorem norm_algHom_of_injective (bA : Basis (Fin n) O A) (bB : Basis (Fin n) O B)
    (ι : A →ₐ[O] B) (hι : Function.Injective ι) (x : A) :
    Algebra.norm O (ι x) = Algebra.norm O x := by
  classical
  set M := LinearMap.toMatrix bA bB ι.toLinearMap with hM
  have hdet : M.det ≠ 0 := det_toMatrix_ne_zero bA bB ι hι
  have hcomm : ι.toLinearMap ∘ₗ (Algebra.lmul O A x : A →ₗ[O] A)
      = (Algebra.lmul O B (ι x) : B →ₗ[O] B) ∘ₗ ι.toLinearMap := by
    apply LinearMap.ext
    intro a
    simp [map_mul]
  have hmat : M * LinearMap.toMatrix bA bA (Algebra.lmul O A x : A →ₗ[O] A)
      = LinearMap.toMatrix bB bB (Algebra.lmul O B (ι x) : B →ₗ[O] B) * M := by
    rw [hM, ← LinearMap.toMatrix_comp bA bA bB, ← LinearMap.toMatrix_comp bA bB bB, hcomm]
  have hdets : M.det * (LinearMap.toMatrix bA bA (Algebra.lmul O A x : A →ₗ[O] A)).det
      = M.det * (LinearMap.toMatrix bB bB (Algebra.lmul O B (ι x) : B →ₗ[O] B)).det := by
    rw [← Matrix.det_mul, hmat, Matrix.det_mul, mul_comm]
  have hXY := mul_left_cancel₀ hdet hdets
  rw [Algebra.norm_eq_matrix_det bA x, Algebra.norm_eq_matrix_det bB (ι x),
    Algebra.leftMulMatrix_apply, Algebra.leftMulMatrix_apply]
  exact hXY.symm

/-- **(iii) The adjugate conductor.**  Every `b : B` becomes an element of the image of `ι`
after multiplication by `det(ι)`: Cramer's rule, `M * adjugate M = det M • 1`, read through
the bases.  This replaces the classical finite-index/conductor argument. -/
theorem exists_preimage_det_smul (bA : Basis (Fin n) O A) (bB : Basis (Fin n) O B)
    (ι : A →ₐ[O] B) (b : B) :
    ∃ a : A, ι a = (LinearMap.toMatrix bA bB ι.toLinearMap).det • b := by
  classical
  set M := LinearMap.toMatrix bA bB ι.toLinearMap with hM
  set w : Fin n → O := M.adjugate.mulVec ⇑(bB.repr b) with hw
  refine ⟨bA.equivFun.symm w, ?_⟩
  have hrepr : ⇑(bA.repr (bA.equivFun.symm w)) = w := by
    rw [← Basis.equivFun_apply, LinearEquiv.apply_symm_apply]
  have hkey := LinearMap.toMatrix_mulVec_repr bA bB ι.toLinearMap (bA.equivFun.symm w)
  rw [AlgHom.toLinearMap_apply, hrepr] at hkey
  apply bB.repr.injective
  apply DFunLike.coe_injective
  calc ⇑(bB.repr (ι (bA.equivFun.symm w)))
      = M.mulVec w := hkey.symm
    _ = (M * M.adjugate).mulVec ⇑(bB.repr b) := by rw [hw, Matrix.mulVec_mulVec]
    _ = M.det • ⇑(bB.repr b) := by
        rw [Matrix.mul_adjugate, Matrix.smul_mulVec, Matrix.one_mulVec]
    _ = ⇑(bB.repr (M.det • b)) := by rw [map_smul]; rfl

end NormTransport

/-! ## §2 — The anchors (Eisenstein and unramified), both currencies

The two keys the cite package fires at.  Eisenstein: `inertiaDegOf = 1` at EVERY degree
(the standalone extraction of CN-20's inline computation — `N(root) = ±a₀` of valuation 1),
with the classical mirror `(ramificationIdx', inertiaDeg') = (n, 1)` on the DVR locus and the
`eisKey` instance.  Unramified: `inertiaDegOf = deg` from InertLeaf's Nakayama divisibility. -/

section Anchors

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

/-- **The Eisenstein anchor, gcd currency.**  A monic Eisenstein `f` (all lower coefficients
in `𝔪`, constant one not in `𝔪²`) has `inertiaDegOf f = 1`, at every degree — `1` is itself a
norm-valuation (of the root), so the gcd is `1`.  No DVR hypothesis on `AdjoinRoot f`, no
completeness.  (Extraction of the `hinf` step inside `NormLeaves.typeOf_eisenstein`.) -/
theorem inertiaDegOf_eisenstein {f : Polynomial O} (hf : f.Monic) (hd : 0 < f.natDegree)
    (hlow : ∀ i < f.natDegree, f.coeff i ∈ maximalIdeal O)
    (h0 : f.coeff 0 ∉ (maximalIdeal O) ^ 2) :
    inertiaDegOf f = 1 := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible O
  have hm : maximalIdeal O = Ideal.span {π} := hπ.maximalIdeal_eq
  obtain ⟨b, hb⟩ : π ∣ f.coeff 0 := by
    have := hlow 0 hd
    rwa [hm, Ideal.mem_span_singleton] at this
  have hbu : IsUnit b := by
    by_contra hbn
    refine h0 ?_
    obtain ⟨c, rfl⟩ : π ∣ b := by
      rw [← Ideal.mem_span_singleton, ← hm]
      exact (mem_maximalIdeal _).2 (mem_nonunits_iff.2 hbn)
    rw [hm, Ideal.span_singleton_pow, Ideal.mem_span_singleton, hb]
    exact ⟨c, by ring⟩
  have hbv : IsDiscreteValuationRing.addVal O b = 0 := by
    rw [← hbu.unit_spec]; exact IsDiscreteValuationRing.addVal_eq_zero_of_unit _
  have hval : IsDiscreteValuationRing.addVal O (f.coeff 0) = 1 := by
    rw [hb, AddValuation.map_mul, IsDiscreteValuationRing.addVal_uniformizer hπ, hbv, add_zero]
  haveI : Nontrivial (AdjoinRoot f) :=
    AdjoinRoot.nontrivial f (ne_of_gt (natDegree_pos_iff_degree_pos.1 hd))
  haveI : Module.Free O (AdjoinRoot f) := hf.free_adjoinRoot
  haveI : Module.Finite O (AdjoinRoot f) := hf.finite_adjoinRoot
  have hsign : ((-1 : O)) ^ f.natDegree ≠ 0 := pow_ne_zero _ (neg_ne_zero.2 one_ne_zero)
  have ha0 : f.coeff 0 ≠ 0 := fun hz => h0 (hz ▸ Ideal.zero_mem _)
  have hne : (AdjoinRoot.root f) ≠ 0 := by
    intro hz
    have hnorm := norm_adjoinRoot_root hf hd
    rw [hz, Algebra.norm_zero] at hnorm
    exact ha0 ((mul_eq_zero.1 hnorm.symm).resolve_left hsign)
  have hunit : IsUnit ((-1 : O) ^ f.natDegree) := (isUnit_one.neg).pow _
  have hsignval : IsDiscreteValuationRing.addVal O ((-1 : O) ^ f.natDegree) = 0 := by
    rw [← hunit.unit_spec]; exact IsDiscreteValuationRing.addVal_eq_zero_of_unit _
  have hmem : (1 : ℕ) ∈ normValues f := by
    refine ⟨one_pos, AdjoinRoot.root f, hne, ?_⟩
    rw [norm_adjoinRoot_root hf hd, AddValuation.map_mul, hval, hsignval, zero_add]
    rfl
  exact inertiaDegOf_eq_of hmem (fun m _ => one_dvd m)

/-- The Eisenstein anchor, `e`-leg: `ramIndexOf f = deg f`. -/
theorem ramIndexOf_eisenstein {f : Polynomial O} (hf : f.Monic) (hd : 0 < f.natDegree)
    (hlow : ∀ i < f.natDegree, f.coeff i ∈ maximalIdeal O)
    (h0 : f.coeff 0 ∉ (maximalIdeal O) ^ 2) :
    ramIndexOf f = f.natDegree := by
  rw [ramIndexOf, inertiaDegOf_eisenstein hf hd hlow h0, Nat.div_one]

/-- The Eisenstein anchor, pair form: `efPair f = (deg f, 1)`. -/
theorem efPair_eisenstein {f : Polynomial O} (hf : f.Monic) (hd : 0 < f.natDegree)
    (hlow : ∀ i < f.natDegree, f.coeff i ∈ maximalIdeal O)
    (h0 : f.coeff 0 ∉ (maximalIdeal O) ^ 2) :
    efPair f = (f.natDegree, 1) := by
  rw [efPair, inertiaDegOf_eisenstein hf hd hlow h0, ramIndexOf_eisenstein hf hd hlow h0]

/-- **The Eisenstein anchor, CLASSICAL currency** — the mirror of
`typeOf_inert_faithful` that the reconnaissance found missing: on the DVR locus the classical
pair of an Eisenstein polynomial is `(ramificationIdx', inertiaDeg') = (deg f, 1)`.
(With `eis_isDVR`/completeness the instances are checkable; here they are hypotheses,
IFCG48-style.) -/
theorem eisenstein_classical {f : Polynomial O} (hf : f.Monic) (hd : 0 < f.natDegree)
    (hlow : ∀ i < f.natDegree, f.coeff i ∈ maximalIdeal O)
    (h0 : f.coeff 0 ∉ (maximalIdeal O) ^ 2)
    [IsDomain (AdjoinRoot f)] [IsDiscreteValuationRing (AdjoinRoot f)] :
    (IsLocalRing.maximalIdeal (AdjoinRoot f)).ramificationIdx' O = f.natDegree ∧
      (IsLocalRing.maximalIdeal (AdjoinRoot f)).inertiaDeg' O = 1 :=
  ⟨by rw [← ramIndexOf_eq_ramificationIdx' hf hd]; exact ramIndexOf_eisenstein hf hd hlow h0,
   by rw [← inertiaDegOf_eq_inertiaDeg' hf hd]; exact inertiaDegOf_eisenstein hf hd hlow h0⟩

/-- The `eisKey` coefficients are Eisenstein: instance of the anchor at leg E's key.
`inertiaDegOf (eisKey π c e') = 1` for `c` a unit (`residue c ≠ 0`). -/
theorem inertiaDegOf_eisKey {π c : O} (hπ : Irreducible π) (hc : IsLocalRing.residue O c ≠ 0)
    {e' : ℕ} (he' : 0 < e') :
    inertiaDegOf (eisKey π c e') = 1 := by
  have hcu : IsUnit c := by
    by_contra hcn
    exact hc (Ideal.Quotient.eq_zero_iff_mem.2 ((mem_maximalIdeal _).2 (mem_nonunits_iff.2 hcn)))
  have hdeg : (eisKey π c e').natDegree = e' := eisKey_natDegree he'
  have hc0 : (eisKey π c e').coeff 0 = c * π := by
    simp [eisKey, coeff_X_pow, he'.ne]
  refine inertiaDegOf_eisenstein (eisKey_monic he') (by omega) ?_ ?_
  · intro i hi
    rw [hdeg] at hi
    rcases Nat.eq_zero_or_pos i with rfl | hipos
    · rw [hc0]
      exact Ideal.mul_mem_left _ c ((mem_maximalIdeal _).2 (mem_nonunits_iff.2 hπ.not_isUnit))
    · have hci : (eisKey π c e').coeff i = 0 := by
        simp [eisKey, coeff_X_pow, coeff_C, Nat.ne_of_lt hi, hipos.ne']
      rw [hci]
      exact Ideal.zero_mem _
  · rw [hc0, hπ.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    rintro ⟨t, ht⟩
    have hpc : π ∣ c := by
      refine ⟨t, ?_⟩
      have hcancel : π * c = π * (π * t) := by
        calc π * c = c * π := mul_comm _ _
          _ = π ^ 2 * t := ht
          _ = π * (π * t) := by ring
      exact mul_left_cancel₀ hπ.ne_zero hcancel
    exact hπ.not_isUnit (isUnit_of_dvd_unit hpc hcu)

/-- The `eisKey` pair: `efPair (eisKey π c e') = (e', 1)` — leg E's per-key `(e, f)` read,
machine-checked in gcd currency. -/
theorem efPair_eisKey {π c : O} (hπ : Irreducible π) (hc : IsLocalRing.residue O c ≠ 0)
    {e' : ℕ} (he' : 0 < e') :
    efPair (eisKey π c e') = (e', 1) := by
  have h1 := inertiaDegOf_eisKey hπ hc he'
  rw [efPair, ramIndexOf, h1, Nat.div_one, eisKey_natDegree he']

/-- **The unramified anchor, gcd currency.**  `ḡ` irreducible over the residue field forces
`inertiaDegOf g = deg g`: `deg g` is itself a norm-valuation (of `π`), and InertLeaf's
Nakayama divisibility makes every norm-valuation a multiple of `deg g`. -/
theorem inertiaDegOf_of_irreducible_map {g : Polynomial O} (hg : g.Monic)
    (hd : 0 < g.natDegree) (h : Irreducible (g.map (residue O))) :
    inertiaDegOf g = g.natDegree := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible O
  refine inertiaDegOf_eq_of (natDegree_mem_normValues hg hd hπ) ?_
  rintro m ⟨-, z, -, hzm⟩
  exact natDegree_dvd_addVal_norm hg hd h hπ m z hzm

end Anchors

/-! ## §3 — The closure side: valuation bookkeeping in an abstract free DVR extension

`TypeOfFaithful.lean`'s helpers, ported from `AdjoinRoot g` to an ABSTRACT `O`-algebra `B`
that is a DVR, free and module-finite over `O` — the shape of the integral closure `O_L`.
Every proof is the landed one with `AdjoinRoot g` replaced by `B`. -/

section ClosureSide

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
variable {B : Type*} [CommRing B] [IsDomain B] [IsDiscreteValuationRing B] [Algebra O B]
  [Module.Free O B] [Module.Finite O B]

/-- Norms of nonzero elements of `B` are nonzero (port of `addVal_norm_ne_top`). -/
theorem addVal_norm_ne_top_of_free {x : B} (hx : x ≠ 0) :
    IsDiscreteValuationRing.addVal O (Algebra.norm O x) ≠ ⊤ := by
  rw [ne_eq, IsDiscreteValuationRing.addVal_eq_top_iff]
  exact Algebra.norm_ne_zero_iff.2 hx

/-- The normal-form computation in `B` (port of `exists_addVal_norm_eq_nsmul`): every nonzero
`x = u · ϖ^j` has norm-valuation `j` times that of the uniformizer. -/
theorem exists_addVal_norm_eq_nsmul_of_free {ϖ : B} (hϖ : Irreducible ϖ) {x : B} (hx : x ≠ 0) :
    ∃ j : ℕ, IsDiscreteValuationRing.addVal O (Algebra.norm O x)
      = j • IsDiscreteValuationRing.addVal O (Algebra.norm O ϖ) := by
  obtain ⟨j, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hx hϖ
  refine ⟨j, ?_⟩
  rw [map_mul, map_pow, IsDiscreteValuationRing.addVal_mul,
    IsDiscreteValuationRing.addVal_pow,
    IsDiscreteValuationRing.addVal_eq_zero_iff.2 (u.isUnit.map (Algebra.norm O)), zero_add]

/-- The ramification data in `B` (port of `exists_ramification_data`): with
`f₀ := v(N ϖ)`, there is `m > 0` with `𝔪_O · B = 𝔪_B ^ m` and `m · f₀ = finrank O B`;
in particular `f₀ > 0`. -/
theorem exists_ramification_data_of_free (hinj : Function.Injective (algebraMap O B))
    {n : ℕ} (hrank : Module.finrank O B = n) (hn : 0 < n)
    {ϖ : B} (hϖ : Irreducible ϖ) {f₀ : ℕ}
    (hf₀ : IsDiscreteValuationRing.addVal O (Algebra.norm O ϖ) = (f₀ : ℕ∞)) :
    0 < f₀ ∧ ∃ m : ℕ, 0 < m ∧
      Ideal.map (algebraMap O B) (maximalIdeal O) = maximalIdeal B ^ m ∧ m * f₀ = n := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible O
  have hπB : algebraMap O B π ≠ 0 := fun h => hπ.ne_zero (hinj (by simpa using h))
  obtain ⟨m, u, hmu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hπB hϖ
  have ha : IsDiscreteValuationRing.addVal O (Algebra.norm O (algebraMap O B π))
      = (n : ℕ∞) := by
    rw [Algebra.norm_algebraMap, hrank, hπ.addVal_pow]
  have hb : IsDiscreteValuationRing.addVal O (Algebra.norm O (algebraMap O B π))
      = m • ((f₀ : ℕ) : ℕ∞) := by
    rw [hmu, map_mul, map_pow, IsDiscreteValuationRing.addVal_mul,
      IsDiscreteValuationRing.addVal_pow,
      IsDiscreteValuationRing.addVal_eq_zero_iff.2 (u.isUnit.map (Algebra.norm O)), zero_add,
      ← hf₀]
  have hnat : n = m * f₀ := by
    have hc : ((n : ℕ) : ℕ∞) = ((m * f₀ : ℕ) : ℕ∞) := by
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
  refine ⟨hf₀pos, m, hmpos, ?_, hnat.symm⟩
  rw [hπ.maximalIdeal_eq, Ideal.map_span, Set.image_singleton, hmu, hϖ.maximalIdeal_eq,
    Ideal.span_singleton_pow, Ideal.span_singleton_mul_left_unit u.isUnit]

/-- The classical pin in `B` (port of `ramificationIdx'_eq_of_map_maximalIdeal_eq_pow`):
`𝔪_O · B = 𝔪_B ^ m` identifies `m` with `ramificationIdx'`. -/
theorem ramificationIdx'_eq_of_map_eq_pow_of_free (hinj : Function.Injective (algebraMap O B))
    {m : ℕ} (hmap : Ideal.map (algebraMap O B) (maximalIdeal O) = maximalIdeal B ^ m) :
    (IsLocalRing.maximalIdeal B).ramificationIdx' O = m := by
  haveI : FaithfulSMul O B := (faithfulSMul_iff_algebraMap_injective O B).2 hinj
  haveI : Module.IsTorsionFree O B := Module.isTorsionFree_iff_faithfulSMul.2 ‹_›
  have hp0 : maximalIdeal O ≠ ⊥ := IsDiscreteValuationRing.not_a_field O
  have hsingle : Ideal.primesOver (maximalIdeal O) B = {maximalIdeal B} :=
    IsLocalRing.primesOver_eq B hp0
  have hmem : maximalIdeal B ∈ (maximalIdeal O).primesOver B := by rw [hsingle]; rfl
  haveI : (maximalIdeal B).LiesOver (maximalIdeal O) := hmem.2
  rw [← Ideal.ramificationIdx_eq_ramificationIdx' (maximalIdeal O) (maximalIdeal B) hp0]
  refine Ideal.ramificationIdx_spec (le_of_eq hmap) ?_
  rw [hmap]
  intro hle
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible B
  rw [hϖ.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.span_singleton_pow,
    Ideal.span_singleton_le_span_singleton, pow_succ] at hle
  have h1 : ϖ ^ m * ϖ ∣ ϖ ^ m * 1 := by rw [mul_one]; exact hle
  exact hϖ.not_isUnit (isUnit_of_dvd_one
    ((mul_dvd_mul_iff_left (pow_ne_zero m hϖ.ne_zero)).1 h1))

end ClosureSide

/-! ## §4 — THE CURRENCY LEMMA

`g` monic of positive degree over the DVR `O`, and `ι : AdjoinRoot g →ₐ[O] B` an injective
`O`-algebra embedding into a DVR `B` free of rank `deg g` (mathematically: `B = O_L`, and the
hypotheses force `g` irreducible).  Then the ORDER's gcd read equals the CLASSICAL residue
degree of `B` over `O` — caveat A's identification, proved.  No completeness anywhere. -/

section Currency

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
variable {B : Type*} [CommRing B] [IsDomain B] [IsDiscreteValuationRing B] [Algebra O B]

/-- The structure map `O → B` is injective whenever `O → AdjoinRoot g → B` is. -/
theorem injective_algebraMap_of_embedding {g : Polynomial O} (hd : 0 < g.natDegree)
    (ι : AdjoinRoot g →ₐ[O] B) (hι : Function.Injective ι) :
    Function.Injective (algebraMap O B) := by
  intro z₁ z₂ h
  refine injective_algebraMap_adjoinRoot hd (hι ?_)
  rw [ι.commutes z₁, ι.commutes z₂]
  exact h

/-- **THE CURRENCY LEMMA, valuation form.**  Through a closure realization the gcd read is
the norm-valuation of the closure's uniformizer: `inertiaDegOf g = v(N_{B/O}(ϖ))`.
Mechanism: `f₀ ∣ everything` transports along the norm-preserving embedding (§1), while the
adjugate-conductor elements `ι⁻¹(det(ι) • ϖ^k)`, `k = 1, 2`, produce the two attained values
`n·v(det) + f₀` and `n·v(det) + 2f₀` whose difference recovers `f₀` from the gcd. -/
theorem inertiaDegOf_eq_of_closure {g : Polynomial O} (hg : g.Monic) (hd : 0 < g.natDegree)
    (bB : Basis (Fin g.natDegree) O B) (ι : AdjoinRoot g →ₐ[O] B)
    (hι : Function.Injective ι) {ϖ : B} (hϖ : Irreducible ϖ) {f₀ : ℕ}
    (hf₀ : IsDiscreteValuationRing.addVal O (Algebra.norm O ϖ) = (f₀ : ℕ∞)) :
    inertiaDegOf g = f₀ := by
  haveI : Module.Free O B := Module.Free.of_basis bB
  haveI : Module.Finite O B := Module.Finite.of_basis bB
  haveI : Module.Free O (AdjoinRoot g) := hg.free_adjoinRoot
  haveI : Module.Finite O (AdjoinRoot g) := hg.finite_adjoinRoot
  set bA : Basis (Fin g.natDegree) O (AdjoinRoot g) :=
    (AdjoinRoot.powerBasis' hg).basis.reindex (finCongr (AdjoinRoot.powerBasis'_dim hg))
    with hbA
  have hrankB : Module.finrank O B = g.natDegree := by
    rw [Module.finrank_eq_card_basis bB, Fintype.card_fin]
  have hinjB : Function.Injective (algebraMap O B) :=
    injective_algebraMap_of_embedding hd ι hι
  have hnorm : ∀ x : AdjoinRoot g, Algebra.norm O (ι x) = Algebra.norm O x :=
    norm_algHom_of_injective bA bB ι hι
  have hne : (normValues g).Nonempty := normValues_nonempty hg hd
  have hd0 : 0 < inertiaDegOf g := inertiaDegOf_pos hne
  obtain ⟨hf₀pos, m, hmpos, hmap, hmf⟩ :=
    exists_ramification_data_of_free hinjB hrankB hd hϖ hf₀
  -- (I) `f₀` divides every norm-valuation of the order
  have hdvd : ∀ k ∈ normValues g, f₀ ∣ k := by
    rintro k ⟨hkpos, x, hx0, hxk⟩
    have hιx : ι x ≠ 0 := fun h => hx0 (hι (by rw [h, map_zero]))
    obtain ⟨j, hj⟩ := exists_addVal_norm_eq_nsmul_of_free (O := O) hϖ hιx
    have hc : ((k : ℕ) : ℕ∞) = ((j * f₀ : ℕ) : ℕ∞) := by
      rw [← hxk, ← hnorm x, hj, hf₀, nsmul_eq_mul, Nat.cast_mul]
    have hk : k = j * f₀ := by exact_mod_cast hc
    exact ⟨j, by rw [hk]; ring⟩
  -- (II) `f₀ ∣ inertiaDegOf g` (the lcm trick)
  have hlcmpos : 0 < Nat.lcm f₀ (inertiaDegOf g) :=
    Nat.pos_of_ne_zero (Nat.lcm_ne_zero hf₀pos.ne' hd0.ne')
  have hlcm_mem : Nat.lcm f₀ (inertiaDegOf g) ∈ normDivisors g :=
    ⟨hlcmpos, fun k hk => Nat.lcm_dvd (hdvd k hk) (inertiaDegOf_dvd hne hk)⟩
  have hlcm_eq : Nat.lcm f₀ (inertiaDegOf g) = inertiaDegOf g :=
    le_antisymm (le_inertiaDegOf hne hlcm_mem)
      (Nat.le_of_dvd hlcmpos (Nat.dvd_lcm_right _ _))
  have hf₀d : f₀ ∣ inertiaDegOf g := hlcm_eq ▸ Nat.dvd_lcm_left _ _
  -- (III) `inertiaDegOf g ∣ f₀` (the adjugate conductor)
  set M := LinearMap.toMatrix bA bB ι.toLinearMap with hM
  have hdet : M.det ≠ 0 := det_toMatrix_ne_zero bA bB ι hι
  have hdettop : IsDiscreteValuationRing.addVal O M.det ≠ ⊤ := by
    rw [ne_eq, IsDiscreteValuationRing.addVal_eq_top_iff]; exact hdet
  obtain ⟨vc, hvc⟩ := ENat.ne_top_iff_exists.1 hdettop
  have hval_k : ∀ k : ℕ, 0 < k → (g.natDegree * vc + k * f₀) ∈ normValues g := by
    intro k hk
    obtain ⟨a, ha⟩ := exists_preimage_det_smul bA bB ι (ϖ ^ k)
    have hsmul : M.det • (ϖ ^ k) = algebraMap O B M.det * ϖ ^ k := Algebra.smul_def _ _
    have hdetB : algebraMap O B M.det ≠ 0 := fun h => hdet (hinjB (by simpa using h))
    have hιa0 : ι a ≠ 0 := by
      rw [ha, hsmul]
      exact mul_ne_zero hdetB (pow_ne_zero _ hϖ.ne_zero)
    have ha0 : a ≠ 0 := fun h => hιa0 (by rw [h, map_zero])
    have hnval : IsDiscreteValuationRing.addVal O (Algebra.norm O a)
        = ((g.natDegree * vc + k * f₀ : ℕ) : ℕ∞) := by
      rw [← hnorm a, ha, hsmul, map_mul, map_pow, Algebra.norm_algebraMap, hrankB,
        IsDiscreteValuationRing.addVal_mul, IsDiscreteValuationRing.addVal_pow,
        IsDiscreteValuationRing.addVal_pow, ← hvc, hf₀, nsmul_eq_mul, nsmul_eq_mul]
      push_cast
      ring
    exact ⟨Nat.add_pos_right _ (Nat.mul_pos hk hf₀pos), a, ha0, hnval⟩
  have hd1 : inertiaDegOf g ∣ g.natDegree * vc + 1 * f₀ :=
    inertiaDegOf_dvd hne (hval_k 1 one_pos)
  have hd2 : inertiaDegOf g ∣ g.natDegree * vc + 2 * f₀ :=
    inertiaDegOf_dvd hne (hval_k 2 two_pos)
  have hdf : inertiaDegOf g ∣ f₀ := by
    have hsub := Nat.dvd_sub hd2 hd1
    have heq : (g.natDegree * vc + 2 * f₀) - (g.natDegree * vc + 1 * f₀) = f₀ := by omega
    rwa [heq] at hsub
  exact Nat.dvd_antisymm hdf hf₀d

/-- **THE CURRENCY LEMMA, classical currency** — caveat A's identification: through a closure
realization, the order's gcd read `inertiaDegOf g` IS the classical residue degree
`(𝔪_B).inertiaDeg' O` of the closure.  Off the maximal locus, no completeness, Lean-core. -/
theorem inertiaDegOf_eq_inertiaDeg'_of_closure {g : Polynomial O} (hg : g.Monic)
    (hd : 0 < g.natDegree) (bB : Basis (Fin g.natDegree) O B)
    (ι : AdjoinRoot g →ₐ[O] B) (hι : Function.Injective ι) :
    inertiaDegOf g = (IsLocalRing.maximalIdeal B).inertiaDeg' O := by
  haveI : Module.Free O B := Module.Free.of_basis bB
  haveI : Module.Finite O B := Module.Finite.of_basis bB
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible B
  obtain ⟨f₀, hf₀⟩ := ENat.ne_top_iff_exists.1 (addVal_norm_ne_top_of_free (O := O) hϖ.ne_zero)
  have hrankB : Module.finrank O B = g.natDegree := by
    rw [Module.finrank_eq_card_basis bB, Fintype.card_fin]
  have hinjB : Function.Injective (algebraMap O B) :=
    injective_algebraMap_of_embedding hd ι hι
  have h1 : inertiaDegOf g = f₀ := inertiaDegOf_eq_of_closure hg hd bB ι hι hϖ hf₀.symm
  obtain ⟨hf₀pos, m, hmpos, hmap, hmf⟩ :=
    exists_ramification_data_of_free hinjB hrankB hd hϖ hf₀.symm
  have he : (IsLocalRing.maximalIdeal B).ramificationIdx' O = m :=
    ramificationIdx'_eq_of_map_eq_pow_of_free hinjB hmap
  haveI : FaithfulSMul O B := (faithfulSMul_iff_algebraMap_injective O B).2 hinjB
  have hfund := Ideal.ramificationIdx_mul_inertiaDeg_eq_finrank_of_isLocalRing B
    (IsDiscreteValuationRing.not_a_field O)
  rw [he, hrankB] at hfund
  rw [h1]
  exact Nat.eq_of_mul_eq_mul_left hmpos (by omega)

/-- The `e`-leg mirror: `ramIndexOf g = (𝔪_B).ramificationIdx' O` through a closure
realization. -/
theorem ramIndexOf_eq_ramificationIdx'_of_closure {g : Polynomial O} (hg : g.Monic)
    (hd : 0 < g.natDegree) (bB : Basis (Fin g.natDegree) O B)
    (ι : AdjoinRoot g →ₐ[O] B) (hι : Function.Injective ι) :
    ramIndexOf g = (IsLocalRing.maximalIdeal B).ramificationIdx' O := by
  haveI : Module.Free O B := Module.Free.of_basis bB
  haveI : Module.Finite O B := Module.Finite.of_basis bB
  have hrankB : Module.finrank O B = g.natDegree := by
    rw [Module.finrank_eq_card_basis bB, Fintype.card_fin]
  have hinjB : Function.Injective (algebraMap O B) :=
    injective_algebraMap_of_embedding hd ι hι
  haveI : FaithfulSMul O B := (faithfulSMul_iff_algebraMap_injective O B).2 hinjB
  have hfund := Ideal.ramificationIdx_mul_inertiaDeg_eq_finrank_of_isLocalRing B
    (IsDiscreteValuationRing.not_a_field O)
  rw [hrankB] at hfund
  have hef : ramIndexOf g * inertiaDegOf g = g.natDegree := ramIndexOf_mul_inertiaDegOf hg hd
  rw [inertiaDegOf_eq_inertiaDeg'_of_closure hg hd bB ι hι] at hef
  exact Nat.eq_of_mul_eq_mul_right
    (Ideal.inertiaDeg'_pos (IsLocalRing.maximalIdeal B) O) (hef.trans hfund.symm)

/-- The `typeOf` mirror: for irreducible `g` with a closure realization, `typeOf g` is the
classical singleton — `TypeOfFaithful.typeOf_eq_classical_of_isDiscreteValuationRing` with the
maximal-locus hypothesis replaced by the realization. -/
theorem typeOf_eq_classical_of_closure {g : Polynomial O} (hg : g.Monic)
    (hd : 0 < g.natDegree) (hirr : Irreducible g)
    (bB : Basis (Fin g.natDegree) O B) (ι : AdjoinRoot g →ₐ[O] B)
    (hι : Function.Injective ι) :
    typeOf g = ⟨{((IsLocalRing.maximalIdeal B).ramificationIdx' O,
      (IsLocalRing.maximalIdeal B).inertiaDeg' O)}⟩ := by
  have hF : IsMonicFactorization g {g} :=
    ⟨by intro h hh; rw [Multiset.mem_singleton.1 hh]; exact ⟨hg, hirr⟩, by simp⟩
  ext
  rw [typeOf_data, monicFactors_eq hF]
  simp [efPair, inertiaDegOf_eq_inertiaDeg'_of_closure hg hd bB ι hι,
    ramIndexOf_eq_ramificationIdx'_of_closure hg hd bB ι hι]

end Currency

/-! ## §5 — The source-side carrier: `DVRClosure` and `HasResidueDegree`

The addendum's restatement vehicle.  A follow-up restating the cite package's legs in the
SOURCE's currency states per-factor conclusions as `HasResidueDegree g' f` (with the source's
`f`-relations); the BRIDGE below derives the current gcd-currency legs as corollaries.  The
trusted content of a so-restated cite is then the source's own object (the residue degree of
the closure), and the order-vs-field translation of caveat A is a machine-checked theorem. -/

section Carrier

universe u v

/-- A **closure realization** of the monogenic order `O[x]/(g)`: a DVR `B`, free of rank
`deg g` over `O`, receiving an injective `O`-algebra map from `AdjoinRoot g`.
Mathematically this is exactly the integral closure `O_L` of `O` in `L = Frac O[x]/(g)`
(any such `B` is integrally closed with the same fraction field, hence IS `O_L`); its
existence for every monic irreducible `g` over a COMPLETE `O` is the classical
Serre, *Corps Locaux* II §2 Prop. 3 — the named remainder of this unit. -/
structure DVRClosure {O : Type u} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (g : Polynomial O) : Type (u + 1) where
  /-- the receiving ring (mathematically `O_L`) -/
  carrier : Type u
  [commRing : CommRing carrier]
  [isDomain : IsDomain carrier]
  [isDVR : IsDiscreteValuationRing carrier]
  [alg : Algebra O carrier]
  /-- freeness of full rank `deg g` -/
  basis : Basis (Fin g.natDegree) O carrier
  /-- the embedding of the monogenic order -/
  emb : AdjoinRoot g →ₐ[O] carrier
  emb_injective : Function.Injective emb

attribute [instance] DVRClosure.commRing DVRClosure.isDomain DVRClosure.isDVR DVRClosure.alg

/-- **The field-side residue degree, corpus-internally**: `f` is THE residue degree of `g`
when some closure realization has classical residue degree `f`.  (Single-valued by
`hasResidueDegree_unique`; equal to the gcd read by the bridge below.) -/
def HasResidueDegree {O : Type u} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (g : Polynomial O) (f : ℕ) : Prop :=
  ∃ D : DVRClosure g, (IsLocalRing.maximalIdeal D.carrier).inertiaDeg' O = f

variable {O : Type u} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

/-- **THE BRIDGE — caveat A's elimination.**  A source-currency residue-degree read IS the
corpus's gcd read.  This is the one theorem a source-side restatement of the cite package's
legs consumes to recover the landed gcd-currency legs. -/
theorem inertiaDegOf_eq_of_hasResidueDegree {g : Polynomial O} (hg : g.Monic)
    (hd : 0 < g.natDegree) {f : ℕ} (h : HasResidueDegree g f) :
    inertiaDegOf g = f := by
  obtain ⟨D, hD⟩ := h
  rw [← hD]
  exact inertiaDegOf_eq_inertiaDeg'_of_closure hg hd D.basis D.emb D.emb_injective

/-- `HasResidueDegree` is single-valued: all realizations read the same `f` (they all equal
the gcd).  This makes the source-side carrier a genuine invariant of `g`. -/
theorem hasResidueDegree_unique {g : Polynomial O} (hg : g.Monic) (hd : 0 < g.natDegree)
    {f₁ f₂ : ℕ} (h₁ : HasResidueDegree g f₁) (h₂ : HasResidueDegree g f₂) : f₁ = f₂ := by
  rw [← inertiaDegOf_eq_of_hasResidueDegree hg hd h₁,
    ← inertiaDegOf_eq_of_hasResidueDegree hg hd h₂]

/-- **Non-vacuity on the maximal locus**: when `AdjoinRoot g` is itself a DVR the identity
embedding realizes the closure, and the residue degree read is the gcd read.  (Off the
maximal locus, existence = the Serre II §2 remainder; on it, free.) -/
theorem hasResidueDegree_of_isDVR {g : Polynomial O} (hg : g.Monic) (hd : 0 < g.natDegree)
    [IsDomain (AdjoinRoot g)] [IsDiscreteValuationRing (AdjoinRoot g)] :
    HasResidueDegree g (inertiaDegOf g) := by
  refine ⟨{ carrier := AdjoinRoot g
            basis := (AdjoinRoot.powerBasis' hg).basis.reindex
              (finCongr (AdjoinRoot.powerBasis'_dim hg))
            emb := AlgHom.id O (AdjoinRoot g)
            emb_injective := Function.injective_id }, ?_⟩
  exact (inertiaDegOf_eq_inertiaDeg' hg hd).symm

/-- The Eisenstein anchor in SOURCE currency: `HasResidueDegree f 1` on the DVR locus
(at `eisKey`, the instances are `eis_isDVR`'s output under completeness). -/
theorem hasResidueDegree_eisenstein {f : Polynomial O} (hf : f.Monic) (hd : 0 < f.natDegree)
    (hlow : ∀ i < f.natDegree, f.coeff i ∈ maximalIdeal O)
    (h0 : f.coeff 0 ∉ (maximalIdeal O) ^ 2)
    [IsDomain (AdjoinRoot f)] [IsDiscreteValuationRing (AdjoinRoot f)] :
    HasResidueDegree f 1 := by
  have h := hasResidueDegree_of_isDVR hf hd (g := f)
  rwa [inertiaDegOf_eisenstein hf hd hlow h0] at h

/-- The unramified anchor in SOURCE currency: `HasResidueDegree g (deg g)` — the DVR
instance is the quarried `AdjoinRoot.isDiscreteValuationRing_of_irreducible_map_residue`. -/
theorem hasResidueDegree_of_irreducible_map {g : Polynomial O} (hg : g.Monic)
    (hd : 0 < g.natDegree) (h : Irreducible (g.map (residue O)))
    [IsDomain (AdjoinRoot g)] :
    HasResidueDegree g g.natDegree := by
  haveI : IsDiscreteValuationRing (AdjoinRoot g) :=
    (AdjoinRoot.isDiscreteValuationRing_of_irreducible_map_residue hg
      (ne_of_gt (natDegree_pos_iff_degree_pos.1 hd)) h).2.1
  have hh := hasResidueDegree_of_isDVR hg hd (g := g)
  rwa [inertiaDegOf_of_irreducible_map hg hd h] at hh

/-- **The full ⟺, conditional on realization existence**: in the presence of ANY closure
realization the source-currency read and the gcd-currency read are interchangeable in both
directions.  (Existence off the maximal locus is the named Serre II §2 remainder; when the
restated cite legs assert `HasResidueDegree` conclusions, existence rides along and only the
`→` direction — the unconditional bridge — is consumed.) -/
theorem hasResidueDegree_iff_of_closure {g : Polynomial O} (hg : g.Monic)
    (hd : 0 < g.natDegree) (D : DVRClosure g) {f : ℕ} :
    HasResidueDegree g f ↔ inertiaDegOf g = f := by
  constructor
  · exact inertiaDegOf_eq_of_hasResidueDegree hg hd
  · intro h
    exact ⟨D, (inertiaDegOf_eq_inertiaDeg'_of_closure hg hd D.basis D.emb
      D.emb_injective).symm.trans h⟩

/-- **Caveat-A elimination, leg U genre**: source-currency residue-degree reads on the two
floors of the unramified tower (`f(h) = d · f(H)`, the source's Cor 6.6(2) shape) yield leg
U's gcd-currency conclusion `inertiaDegOf h = d · inertiaDegOf H` verbatim.  (Leg R's genre
`inertiaDegOf g' = deg ψ` is the bridge itself at `f := deg ψ`; leg E's genre
`inertiaDegOf h = inertiaDegOf H` is this at `d = 1` across the two base rings.) -/
theorem inertiaDegOf_scale_of_hasResidueDegree
    {O' : Type v} [CommRing O'] [IsDomain O'] [IsDiscreteValuationRing O']
    {h : Polynomial O} (hh : h.Monic) (hdh : 0 < h.natDegree)
    {H : Polynomial O'} (hH : H.Monic) (hdH : 0 < H.natDegree)
    {d fH : ℕ} (h₁ : HasResidueDegree h (d * fH)) (h₂ : HasResidueDegree H fH) :
    inertiaDegOf h = d * inertiaDegOf H := by
  rw [inertiaDegOf_eq_of_hasResidueDegree hh hdh h₁,
    inertiaDegOf_eq_of_hasResidueDegree hH hdH h₂]

end Carrier

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.IFCG76.det_toMatrix_ne_zero
#print axioms Uniformity.Density.IFCG76.norm_algHom_of_injective
#print axioms Uniformity.Density.IFCG76.exists_preimage_det_smul
#print axioms Uniformity.Density.IFCG76.inertiaDegOf_eisenstein
#print axioms Uniformity.Density.IFCG76.ramIndexOf_eisenstein
#print axioms Uniformity.Density.IFCG76.efPair_eisenstein
#print axioms Uniformity.Density.IFCG76.eisenstein_classical
#print axioms Uniformity.Density.IFCG76.inertiaDegOf_eisKey
#print axioms Uniformity.Density.IFCG76.efPair_eisKey
#print axioms Uniformity.Density.IFCG76.inertiaDegOf_of_irreducible_map
#print axioms Uniformity.Density.IFCG76.addVal_norm_ne_top_of_free
#print axioms Uniformity.Density.IFCG76.exists_addVal_norm_eq_nsmul_of_free
#print axioms Uniformity.Density.IFCG76.exists_ramification_data_of_free
#print axioms Uniformity.Density.IFCG76.ramificationIdx'_eq_of_map_eq_pow_of_free
#print axioms Uniformity.Density.IFCG76.injective_algebraMap_of_embedding
#print axioms Uniformity.Density.IFCG76.inertiaDegOf_eq_of_closure
#print axioms Uniformity.Density.IFCG76.inertiaDegOf_eq_inertiaDeg'_of_closure
#print axioms Uniformity.Density.IFCG76.ramIndexOf_eq_ramificationIdx'_of_closure
#print axioms Uniformity.Density.IFCG76.typeOf_eq_classical_of_closure
#print axioms Uniformity.Density.IFCG76.inertiaDegOf_eq_of_hasResidueDegree
#print axioms Uniformity.Density.IFCG76.hasResidueDegree_unique
#print axioms Uniformity.Density.IFCG76.hasResidueDegree_of_isDVR
#print axioms Uniformity.Density.IFCG76.hasResidueDegree_eisenstein
#print axioms Uniformity.Density.IFCG76.hasResidueDegree_of_irreducible_map
#print axioms Uniformity.Density.IFCG76.hasResidueDegree_iff_of_closure
#print axioms Uniformity.Density.IFCG76.inertiaDegOf_scale_of_hasResidueDegree

end AxCheck

end Uniformity.Density.IFCG76
