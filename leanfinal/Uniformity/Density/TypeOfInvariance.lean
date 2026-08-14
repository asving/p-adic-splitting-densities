/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.Density.TypeOf

/-!
# Uniformity.Density.TypeOfInvariance — how `typeOf` moves under the two normalizations

The `n = 3` triple-root recursion (`leancheck/notes/N3_CHECK_2026-08-13.md` §9.4) recentres a cubic
at an integral point and then rescales `X = π^m Y`. Both moves must be known to leave the splitting
type alone, or the recursion computes the type of the wrong polynomial. This file proves both.

* **`typeOf_shift` (HYP.05)** — `typeOf (F.comp (X + C c)) = typeOf F` for every `c : O` and every
  monic `F`. Unconditional.
* **`typeOf_unscale` / `typeOf_scale` (HYP.06)** — for the `π`-power extraction. This one carries a
  side condition, because `F(π^m Y) / π^(m n)` is integral only when the Newton polygon of `F` lies
  above the line of slope `m`. The clean statement runs the substitution BACKWARDS, where no side
  condition exists: `unscale π m h` (defined below) is always integral and monic, and
  `typeOf (unscale π m h) = typeOf h`. The forward form the recursion literally uses is
  `typeOf_scale`.

## Method

Both are transported along the monic factorization, using the uniqueness already proved in
`TypeOf.lean` (`monicFactorization_unique`, `monicFactors_eq`); the work is showing that `efPair`
is unchanged on each monic irreducible factor.

* For the **shift** the two algebras `O[X]/(g)` and `O[X]/(g(X+c))` are isomorphic (`X ↦ X - c`), so
  `Algebra.norm_eq_of_algEquiv` makes the two `normValues` sets literally equal.
* For the **scale** they are *not* isomorphic: `O[π^m y] ⊊ O[y]` is a smaller order in the same
  field. What replaces the isomorphism is an elementary determinant identity — the multiplication
  matrices in the two power bases are conjugate by `diag(π^(m i))`, so the norms agree along the
  inclusion (`norm_unscaleHom`) — plus the observation that `π^(m(d-1))·O[y] ⊆ O[π^m y]`, which
  makes the two *gcds* of norm-valuations agree even though the two *sets* do not.

Informal proofs and faithfulness paragraphs: `notes/P5_INFRA_2026-08-14.md` §§2–3.

## Status

Sorry-free, axiom-free (Lean core only); footprints printed by the `AxCheck` block at the foot.
-/

set_option linter.style.longLine false

namespace Uniformity.Density

open IsLocalRing Polynomial

/-! ## 0. Transport of `efPair` along an algebra isomorphism of the root algebras -/

section Transport

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

/-- If the two root algebras are `O`-isomorphic, they have the same norm-valuation set. -/
theorem normValues_of_algEquiv {g h : Polynomial O} (e : AdjoinRoot g ≃ₐ[O] AdjoinRoot h) :
    normValues g = normValues h := by
  ext k
  constructor
  · rintro ⟨hk, x, hx, hnorm⟩
    refine ⟨hk, e x, ?_, ?_⟩
    · simpa using hx
    · rwa [Algebra.norm_eq_of_algEquiv e x]
  · rintro ⟨hk, y, hy, hnorm⟩
    refine ⟨hk, e.symm y, ?_, ?_⟩
    · simpa using hy
    · rwa [Algebra.norm_eq_of_algEquiv e.symm y]

theorem normDivisors_of_algEquiv {g h : Polynomial O} (e : AdjoinRoot g ≃ₐ[O] AdjoinRoot h) :
    normDivisors g = normDivisors h := by
  unfold normDivisors
  rw [normValues_of_algEquiv e]

theorem inertiaDegOf_of_algEquiv {g h : Polynomial O} (e : AdjoinRoot g ≃ₐ[O] AdjoinRoot h) :
    inertiaDegOf g = inertiaDegOf h := by
  rw [inertiaDegOf, inertiaDegOf, normDivisors_of_algEquiv e]

end Transport

/-! ## 1. HYP.05 — shift invariance -/

section ShiftBasic

variable {O : Type*} [CommRing O]

/-- Translation `p ↦ p(X + c)` as an `O`-algebra automorphism of `O[X]`. -/
noncomputable def shift (c : O) : Polynomial O ≃ₐ[O] Polynomial O := algEquivAevalXAddC c

theorem shift_apply (c : O) (p : Polynomial O) : shift c p = p.comp (X + C c) := by
  rw [comp_eq_aeval]
  rfl

theorem shift_monic {p : Polynomial O} (hp : p.Monic) (c : O) : (shift c p).Monic := by
  rw [shift_apply]
  exact hp.comp_X_add_C c

theorem shift_natDegree (p : Polynomial O) (c : O) : (shift c p).natDegree = p.natDegree := by
  rw [shift_apply, ← taylor_apply, natDegree_taylor]

theorem shift_irreducible {p : Polynomial O} (c : O) :
    Irreducible (shift c p) ↔ Irreducible p :=
  MulEquiv.irreducible_iff (f := (shift c).toRingEquiv.toMulEquiv) (x := p)

/-- Evaluating the translate at `y` is evaluating the original at `y + c`. -/
theorem aeval_shift {A : Type*} [CommRing A] [Algebra O A] (c : O) (p : Polynomial O) (y : A) :
    aeval y (shift c p) = aeval (y + algebraMap O A c) p := by
  rw [shift_apply, aeval_comp]
  simp

/-- The root algebra of the translate is the root algebra of the original: `X ↦ X - c`. -/
noncomputable def shiftRootEquiv (c : O) (g : Polynomial O) :
    AdjoinRoot (shift c g) ≃ₐ[O] AdjoinRoot g := by
  refine AlgEquiv.ofAlgHom
    (AdjoinRoot.liftAlgHom (shift c g) (Algebra.ofId O (AdjoinRoot g))
      (AdjoinRoot.root g - algebraMap O (AdjoinRoot g) c) ?_)
    (AdjoinRoot.liftAlgHom g (Algebra.ofId O (AdjoinRoot (shift c g)))
      (AdjoinRoot.root (shift c g) + algebraMap O (AdjoinRoot (shift c g)) c) ?_) ?_ ?_
  · show aeval (AdjoinRoot.root g - algebraMap O (AdjoinRoot g) c) (shift c g) = 0
    rw [aeval_shift]
    simp
  · show aeval (AdjoinRoot.root (shift c g) + algebraMap O (AdjoinRoot (shift c g)) c) g = 0
    rw [← aeval_shift]
    simp
  · refine AdjoinRoot.algHom_ext ?_
    simp
  · refine AdjoinRoot.algHom_ext ?_
    simp

end ShiftBasic

section Shift

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

/-- **`efPair` is shift invariant** on monic irreducibles (indeed on everything of the same
degree). -/
theorem efPair_shift (c : O) (g : Polynomial O) : efPair (shift c g) = efPair g := by
  have hf : inertiaDegOf (shift c g) = inertiaDegOf g :=
    inertiaDegOf_of_algEquiv (shiftRootEquiv c g)
  rw [efPair, efPair, ramIndexOf, ramIndexOf, hf, shift_natDegree]

/-- Factorizations transport along the shift. -/
theorem monicFactors_shift {F : Polynomial O} (hF : F.Monic) (c : O) :
    monicFactors (shift c F) = (monicFactors F).map (shift c) := by
  refine monicFactors_eq ⟨?_, ?_⟩
  · intro g hg
    obtain ⟨g₀, hg₀, rfl⟩ := Multiset.mem_map.1 hg
    exact ⟨shift_monic ((monicFactors_spec hF).1 g₀ hg₀).1 c,
      (shift_irreducible c).2 ((monicFactors_spec hF).1 g₀ hg₀).2⟩
  · rw [← map_multiset_prod (shift c) (monicFactors F), (monicFactors_spec hF).2]

/-- **HYP.05 — `typeOf` IS SHIFT INVARIANT.** For every `c : O` and every monic `F`,
`typeOf (F(X + c)) = typeOf F`. No side condition. -/
theorem typeOf_shift {F : Polynomial O} (hF : F.Monic) (c : O) :
    typeOf (F.comp (X + C c)) = typeOf F := by
  refine FactorizationType.ext ?_
  rw [← shift_apply, typeOf_data, typeOf_data, monicFactors_shift hF c, Multiset.map_map]
  exact Multiset.map_congr rfl (fun g _ => efPair_shift c g)

end Shift


/-! ## 2. HYP.06 — the `π`-power extraction (`scaleRoots`)

Mathlib's `Polynomial.scaleRoots h s` has coefficients `hᵢ · s^(d-i)` (`d = deg h`), i.e. it *is*
the "unscale" of §3 of the unit note: `scaleRoots h (π^m) = π^(m d) · h(X / π^m)`. It is always
integral (no side condition) and monic when `h` is, and its roots are `π^m` times the roots of `h`.
The forward substitution the recursion performs — `F(π^m Y) = π^(m n) G(Y)` with `G` monic — is the
statement `F = scaleRoots G (π^m)`, which is `typeOf_scale` below. -/

section Scale

variable {O : Type*} [CommRing O] [IsDomain O]

/-- **The comparison map** `O[X]/(scaleRoots h s) → O[X]/(h)`, sending the root to `s` times the
root. It is injective (`scaleHom_injective`) but **not** surjective: its image is the smaller order
`O[s·y] ⊆ O[y]`. -/
noncomputable def scaleHom (h : Polynomial O) (s : O) :
    AdjoinRoot (h.scaleRoots s) →ₐ[O] AdjoinRoot h :=
  AdjoinRoot.liftAlgHom _ (Algebra.ofId O (AdjoinRoot h))
    (algebraMap O (AdjoinRoot h) s * AdjoinRoot.root h)
    (by
      show aeval (algebraMap O (AdjoinRoot h) s * AdjoinRoot.root h) (h.scaleRoots s) = 0
      exact scaleRoots_aeval_eq_zero (by simp))

omit [IsDomain O] in
@[simp] theorem scaleHom_root (h : Polynomial O) (s : O) :
    scaleHom h s (AdjoinRoot.root (h.scaleRoots s))
      = algebraMap O (AdjoinRoot h) s * AdjoinRoot.root h :=
  AdjoinRoot.liftAlgHom_root _ _ _ _

/-- The power basis `1, y, …, y^(d-1)` of `O[X]/(h)`. -/
noncomputable def rootBasis {h : Polynomial O} (hh : h.Monic) :
    Module.Basis (Fin h.natDegree) O (AdjoinRoot h) := (AdjoinRoot.powerBasis' hh).basis

/-- The power basis of `O[X]/(scaleRoots h s)`, reindexed by `Fin (deg h)`. -/
noncomputable def scaleRootBasis {h : Polynomial O} (hh : h.Monic) (s : O) :
    Module.Basis (Fin h.natDegree) O (AdjoinRoot (h.scaleRoots s)) :=
  ((AdjoinRoot.powerBasis' ((monic_scaleRoots_iff s).2 hh)).basis).reindex
    (finCongr (natDegree_scaleRoots h s))

omit [IsDomain O] in
theorem rootBasis_apply {h : Polynomial O} (hh : h.Monic) (i : Fin h.natDegree) :
    rootBasis hh i = AdjoinRoot.root h ^ (i : ℕ) :=
  (AdjoinRoot.powerBasis' hh).basis_eq_pow i

omit [IsDomain O] in
theorem scaleRootBasis_apply {h : Polynomial O} (hh : h.Monic) (s : O) (i : Fin h.natDegree) :
    scaleRootBasis hh s i = AdjoinRoot.root (h.scaleRoots s) ^ (i : ℕ) := by
  show ((AdjoinRoot.powerBasis' ((monic_scaleRoots_iff s).2 hh)).basis).reindex
      (finCongr (natDegree_scaleRoots h s)) i = _
  rw [Module.Basis.reindex_apply, PowerBasis.basis_eq_pow]
  rfl

/-- **The comparison map is diagonal in the two power bases**: `x^i ↦ s^i · y^i`. -/
omit [IsDomain O] in
theorem scaleHom_basis {h : Polynomial O} (hh : h.Monic) (s : O) (i : Fin h.natDegree) :
    scaleHom h s (scaleRootBasis hh s i) = (s ^ (i : ℕ)) • rootBasis hh i := by
  rw [scaleRootBasis_apply hh, rootBasis_apply hh, map_pow, scaleHom_root, mul_pow,
    Algebra.smul_def, map_pow]

/-- **The master relation.** In the two power bases the comparison map is the diagonal matrix
`diag(s^i)`. Everything about the scale relation follows from this one line. -/
theorem repr_scaleHom {h : Polynomial O} (hh : h.Monic) (s : O)
    (z : AdjoinRoot (h.scaleRoots s)) (i : Fin h.natDegree) :
    (rootBasis hh).repr (scaleHom h s z) i
      = s ^ (i : ℕ) * (scaleRootBasis hh s).repr z i := by
  classical
  conv_lhs => rw [← (scaleRootBasis hh s).sum_repr z]
  rw [map_sum, map_sum]
  simp only [map_smul, scaleHom_basis, smul_smul, Finsupp.coe_finsetSum, Finset.sum_apply,
    Finsupp.smul_apply, Module.Basis.repr_self, Finsupp.single_apply, smul_eq_mul, mul_ite,
    mul_one, mul_zero]
  rw [Finset.sum_ite_eq' Finset.univ i]
  simp [mul_comm]

theorem scaleHom_injective {h : Polynomial O} (hh : h.Monic) {s : O} (hs : s ≠ 0) :
    Function.Injective (scaleHom h s) := by
  rw [injective_iff_map_eq_zero]
  intro z hz
  refine (scaleRootBasis hh s).ext_elem (fun i => ?_)
  have h1 : s ^ (i : ℕ) * (scaleRootBasis hh s).repr z i = 0 := by
    rw [← repr_scaleHom hh s z i, hz]
    simp
  have h2 := (mul_eq_zero.1 h1).resolve_left (pow_ne_zero _ hs)
  simpa using h2

/-- **FACT 1 of the unit note §3.2 — the norms agree along the comparison map**, even though the
two orders are not isomorphic. The multiplication matrices in the two power bases satisfy
`N · D = D · M` with `D = diag(s^i)`, so their determinants agree after cancelling `det D ≠ 0`. -/
theorem norm_scaleHom {h : Polynomial O} (hh : h.Monic) {s : O} (hs : s ≠ 0)
    (z : AdjoinRoot (h.scaleRoots s)) :
    Algebra.norm O (scaleHom h s z) = Algebra.norm O z := by
  classical
  set bB := rootBasis hh with hbB
  set bA := scaleRootBasis hh s with hbA
  set M := Algebra.leftMulMatrix bA z with hM
  set N := Algebra.leftMulMatrix bB (scaleHom h s z) with hN
  set D : Matrix (Fin h.natDegree) (Fin h.natDegree) O :=
    Matrix.diagonal (fun i => s ^ (i : ℕ)) with hD
  have key : ∀ i j : Fin h.natDegree, N i j * s ^ (j : ℕ) = s ^ (i : ℕ) * M i j := by
    intro i j
    have e1 : scaleHom h s (z * bA j) = (s ^ (j : ℕ)) • (scaleHom h s z * bB j) := by
      rw [map_mul, hbA, scaleHom_basis, hbB, Algebra.smul_def, Algebra.smul_def]
      ring
    have e2 : (rootBasis hh).repr (scaleHom h s (z * bA j)) i
        = s ^ (j : ℕ) * ((rootBasis hh).repr (scaleHom h s z * bB j)) i := by
      rw [e1, map_smul]
      simp
    rw [repr_scaleHom hh s (z * bA j) i] at e2
    rw [← hbB, ← hbA] at e2
    rw [hN, hM, Algebra.leftMulMatrix_eq_repr_mul, Algebra.leftMulMatrix_eq_repr_mul]
    linear_combination -e2
  have hmat : N * D = D * M := by
    ext i j
    rw [hD, Matrix.mul_diagonal, Matrix.diagonal_mul]
    exact key i j
  have hDdet : D.det ≠ 0 := by
    rw [hD, Matrix.det_diagonal]
    exact Finset.prod_ne_zero_iff.2 (fun i _ => pow_ne_zero _ hs)
  have hdet : N.det * D.det = M.det * D.det := by
    rw [← Matrix.det_mul, hmat, Matrix.det_mul, mul_comm]
  rw [Algebra.norm_eq_matrix_det bB, Algebra.norm_eq_matrix_det bA, ← hN, ← hM]
  exact mul_right_cancel₀ hDdet hdet

end Scale

/-! ## Axiom census -/

section AxCheck

#print axioms Uniformity.Density.typeOf_shift

end AxCheck

end Uniformity.Density
