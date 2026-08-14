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

omit [IsDomain O] in
/-- **The comparison map is diagonal in the two power bases**: `x^i ↦ s^i · y^i`. -/
theorem scaleHom_basis {h : Polynomial O} (hh : h.Monic) (s : O) (i : Fin h.natDegree) :
    scaleHom h s (scaleRootBasis hh s i) = (s ^ (i : ℕ)) • rootBasis hh i := by
  rw [scaleRootBasis_apply hh, rootBasis_apply hh, map_pow, scaleHom_root, mul_pow,
    Algebra.smul_def, map_pow]

omit [IsDomain O] in
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


/-! ### The gcd comparison (FACT 2 of the unit note §3.2) -/

section ScaleGcd

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

open IsDiscreteValuationRing hiding maximalIdeal

omit [IsDiscreteValuationRing O] in
/-- Multiplying by a nonzero scalar does not kill a nonzero element of the (free) root algebra. -/
theorem algebraMap_mul_ne_zero {h : Polynomial O} (hh : h.Monic) {c : O} (hc : c ≠ 0)
    {v : AdjoinRoot h} (hv : v ≠ 0) : algebraMap O (AdjoinRoot h) c * v ≠ 0 := by
  intro hzero
  refine hv ((rootBasis hh).ext_elem (fun i => ?_))
  have h1 : c * (rootBasis hh).repr v i = 0 := by
    have h2 : (rootBasis hh).repr (algebraMap O (AdjoinRoot h) c * v) i = 0 := by
      rw [hzero]; simp
    rwa [← Algebra.smul_def, map_smul, Finsupp.smul_apply, smul_eq_mul] at h2
  simpa using (mul_eq_zero.1 h1).resolve_left hc

omit [IsDomain O] [IsDiscreteValuationRing O] in
/-- **`π^(m(d-1))·O[y] ⊆ O[π^m y]`** — the index bound that makes the two gcds agree. -/
theorem exists_scaleHom_eq {h : Polynomial O} (hh : h.Monic) (s : O) (v : AdjoinRoot h) :
    ∃ z : AdjoinRoot (h.scaleRoots s),
      scaleHom h s z = algebraMap O (AdjoinRoot h) (s ^ (h.natDegree - 1)) * v := by
  classical
  refine ⟨∑ i : Fin h.natDegree,
    ((rootBasis hh).repr v i * s ^ (h.natDegree - 1 - (i : ℕ))) • scaleRootBasis hh s i, ?_⟩
  rw [map_sum]
  simp only [map_smul, scaleHom_basis, smul_smul]
  have hpow : ∀ i : Fin h.natDegree,
      (rootBasis hh).repr v i * s ^ (h.natDegree - 1 - (i : ℕ)) * s ^ (i : ℕ)
        = s ^ (h.natDegree - 1) * (rootBasis hh).repr v i := by
    intro i
    have hi := i.isLt
    have he : h.natDegree - 1 - (i : ℕ) + (i : ℕ) = h.natDegree - 1 := by omega
    rw [mul_assoc, ← pow_add, he]; ring
  calc ∑ i : Fin h.natDegree,
        ((rootBasis hh).repr v i * s ^ (h.natDegree - 1 - (i : ℕ)) * s ^ (i : ℕ)) • rootBasis hh i
      = ∑ i : Fin h.natDegree,
          (s ^ (h.natDegree - 1) * (rootBasis hh).repr v i) • rootBasis hh i :=
        Finset.sum_congr rfl (fun i _ => by rw [hpow i])
    _ = s ^ (h.natDegree - 1) • ∑ i : Fin h.natDegree, ((rootBasis hh).repr v i) • rootBasis hh i := by
        rw [Finset.smul_sum]
        exact Finset.sum_congr rfl (fun i _ => by rw [smul_smul])
    _ = s ^ (h.natDegree - 1) • v := by rw [(rootBasis hh).sum_repr v]
    _ = algebraMap O (AdjoinRoot h) (s ^ (h.natDegree - 1)) * v := (Algebra.smul_def _ _)

/-- The `normValues` of the rescaled polynomial are among those of the original (the comparison
map is injective and norm-preserving). -/
theorem normValues_scaleRoots_subset {h : Polynomial O} (hh : h.Monic) {s : O} (hs : s ≠ 0) :
    normValues (h.scaleRoots s) ⊆ normValues h := by
  rintro k ⟨hk, z, hz, hnorm⟩
  refine ⟨hk, scaleHom h s z, ?_, ?_⟩
  · intro hzero
    exact hz (scaleHom_injective hh hs (by rw [hzero, map_zero]))
  · rwa [norm_scaleHom hh hs]

omit [IsDomain O] [IsDiscreteValuationRing O] in
/-- The norm of a scalar in the root algebra of a monic polynomial of degree `d` is its `d`-th
power. -/
theorem norm_algebraMap_rootBasis {h : Polynomial O} (hh : h.Monic) (c : O) :
    Algebra.norm O (algebraMap O (AdjoinRoot h) c) = c ^ h.natDegree := by
  rw [Algebra.norm_algebraMap_of_basis (rootBasis hh) c]
  simp

/-- **The reverse gcd inclusion.** A common divisor of the rescaled polynomial's norm-valuations
divides the original's, because `π^(m(d-1))·v` lies in the image of the comparison map and
`v(N(π^(m(d-1)))) = m(d-1)d` is itself a norm-valuation (or zero). -/
theorem normDivisors_scaleRoots_subset {π : O} (hπ : Irreducible π) {h : Polynomial O}
    (hh : h.Monic) (hd : 0 < h.natDegree) (m : ℕ) :
    normDivisors (h.scaleRoots (π ^ m)) ⊆ normDivisors h := by
  classical
  have hs : (π : O) ^ m ≠ 0 := pow_ne_zero _ hπ.ne_zero
  have hA : (h.scaleRoots (π ^ m)).Monic := (monic_scaleRoots_iff _).2 hh
  have hdegA : (h.scaleRoots (π ^ m)).natDegree = h.natDegree := natDegree_scaleRoots h _
  rintro k ⟨hk, hdvd⟩
  refine ⟨hk, ?_⟩
  rintro n ⟨hn, v, hv, hnv⟩
  set d := h.natDegree with hddef
  set c : O := π ^ (m * (d - 1)) with hcdef
  have hc : c ≠ 0 := pow_ne_zero _ hπ.ne_zero
  have hcpow : ((π : O) ^ m) ^ (d - 1) = c := by rw [hcdef, ← pow_mul]
  -- the lifted element
  obtain ⟨z, hz⟩ := exists_scaleHom_eq hh ((π : O) ^ m) v
  rw [hcpow] at hz
  have hzne : z ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hz
    exact algebraMap_mul_ne_zero hh hc hv hz.symm
  -- its norm-valuation
  have hnz : Algebra.norm O z = c ^ d * Algebra.norm O v := by
    rw [← norm_scaleHom hh hs z, hz, map_mul, norm_algebraMap_rootBasis hh]
  have hvalz : addVal O (Algebra.norm O z) = ((m * (d - 1) * d + n : ℕ) : ℕ∞) := by
    rw [hnz, addVal_mul, hcdef, ← pow_mul, hπ.addVal_pow, hnv, Nat.cast_add]
  have hmem : (m * (d - 1) * d + n) ∈ normValues (h.scaleRoots (π ^ m)) :=
    ⟨by omega, z, hzne, hvalz⟩
  have hk1 : k ∣ m * (d - 1) * d + n := hdvd _ hmem
  -- and the scalar's norm-valuation
  have hk2 : k ∣ m * (d - 1) * d := by
    rcases Nat.eq_zero_or_pos (m * (d - 1) * d) with h0 | h0
    · rw [h0]; exact dvd_zero k
    · refine hdvd _ ⟨h0, algebraMap O (AdjoinRoot (h.scaleRoots (π ^ m))) c, ?_, ?_⟩
      · intro hzero
        have hdeg : (h.scaleRoots (π ^ m)).degree ≠ 0 := by
          refine ne_of_gt (natDegree_pos_iff_degree_pos.1 ?_)
          omega
        exact hc (AdjoinRoot.of.injective_of_degree_ne_zero hdeg (by simpa using hzero))
      · rw [norm_algebraMap_rootBasis hA, hdegA, hcdef, ← pow_mul, hπ.addVal_pow]
  exact (Nat.dvd_add_right hk2).1 hk1

/-- **The residue degree is unchanged by the `π`-power extraction.** -/
theorem inertiaDegOf_scaleRoots {π : O} (hπ : Irreducible π) {h : Polynomial O} (hh : h.Monic)
    (hd : 0 < h.natDegree) (m : ℕ) :
    inertiaDegOf (h.scaleRoots (π ^ m)) = inertiaDegOf h := by
  have h1 : normDivisors h ⊆ normDivisors (h.scaleRoots (π ^ m)) := by
    rintro j ⟨hj, hdvd⟩
    exact ⟨hj, fun n hn =>
      hdvd n (normValues_scaleRoots_subset hh (pow_ne_zero _ hπ.ne_zero) hn)⟩
  rw [inertiaDegOf, inertiaDegOf,
    Set.Subset.antisymm (normDivisors_scaleRoots_subset hπ hh hd m) h1]

/-- **`(e, f)` is unchanged by the `π`-power extraction.** -/
theorem efPair_scaleRoots {π : O} (hπ : Irreducible π) {h : Polynomial O} (hh : h.Monic)
    (hd : 0 < h.natDegree) (m : ℕ) : efPair (h.scaleRoots (π ^ m)) = efPair h := by
  rw [efPair, efPair, ramIndexOf, ramIndexOf, inertiaDegOf_scaleRoots hπ hh hd m,
    natDegree_scaleRoots]

end ScaleGcd

/-! ### Irreducibility transfer (FACT 3 of the unit note §3.2) -/

section ScaleIrred

/-- Over a field, scaling the roots by a unit is a multiplicative automorphism of `K[X]` (it is
NOT additive: degrees move). That is enough to transfer irreducibility. -/
noncomputable def scaleRootsMulEquiv {K : Type*} [Field K] (r : Kˣ) :
    Polynomial K ≃* Polynomial K where
  toFun p := p.scaleRoots (r : K)
  invFun p := p.scaleRoots ((r⁻¹ : Kˣ) : K)
  left_inv p := by
    show (p.scaleRoots (r : K)).scaleRoots ((r⁻¹ : Kˣ) : K) = p
    rw [← scaleRoots_mul]; simp
  right_inv p := by
    show (p.scaleRoots ((r⁻¹ : Kˣ) : K)).scaleRoots (r : K) = p
    rw [← scaleRoots_mul]; simp
  map_mul' p q := mul_scaleRoots_of_noZeroDivisors p q _

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

/-- **Irreducibility is preserved by the `π`-power extraction**, in both directions. Gauss's lemma
(a DVR is integrally closed) moves the question to the fraction field, where `π^m` is a unit. -/
theorem irreducible_scaleRoots_iff {π : O} (hπ : Irreducible π) {g : Polynomial O} (hg : g.Monic)
    (m : ℕ) : Irreducible (g.scaleRoots (π ^ m)) ↔ Irreducible g := by
  classical
  set K := FractionRing O
  set φ : O →+* K := algebraMap O K with hφ
  have hinj : Function.Injective φ := IsFractionRing.injective O K
  have hπK : φ (π ^ m) ≠ 0 := by
    simp only [ne_eq, map_eq_zero_iff φ hinj]
    exact pow_ne_zero _ hπ.ne_zero
  have hA : (g.scaleRoots (π ^ m)).Monic := (monic_scaleRoots_iff _).2 hg
  rw [hA.irreducible_iff_irreducible_map_fraction_map (K := K),
    hg.irreducible_iff_irreducible_map_fraction_map (K := K),
    map_scaleRoots _ _ φ (by simp [hg.leadingCoeff])]
  exact MulEquiv.irreducible_iff (f := scaleRootsMulEquiv (Units.mk0 _ hπK))
    (x := g.map φ)

end ScaleIrred

/-! ### The scale relation -/

section ScaleType

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

omit [IsDiscreteValuationRing O] in
theorem prod_map_scaleRoots (s : O) (F : Multiset (Polynomial O)) :
    (F.map (fun g => g.scaleRoots s)).prod = F.prod.scaleRoots s := by
  refine Multiset.induction_on F (by simp) (fun a F ih => ?_)
  simp [ih, mul_scaleRoots_of_noZeroDivisors]

theorem monicFactors_scaleRoots {π : O} (hπ : Irreducible π) {F : Polynomial O} (hF : F.Monic)
    (m : ℕ) : monicFactors (F.scaleRoots (π ^ m))
      = (monicFactors F).map (fun g => g.scaleRoots (π ^ m)) := by
  refine monicFactors_eq ⟨?_, ?_⟩
  · intro g hg
    obtain ⟨g₀, hg₀, rfl⟩ := Multiset.mem_map.1 hg
    obtain ⟨hm, hi⟩ := (monicFactors_spec hF).1 g₀ hg₀
    exact ⟨(monic_scaleRoots_iff _).2 hm, (irreducible_scaleRoots_iff hπ hm m).2 hi⟩
  · rw [prod_map_scaleRoots, (monicFactors_spec hF).2]

/-- **HYP.06 — the `π`-power extraction preserves `typeOf`** (backward form, no side condition).
`scaleRoots F (π^m)` is the always-integral polynomial `π^(m·deg F)·F(X/π^m)`. -/
theorem typeOf_scaleRoots {π : O} (hπ : Irreducible π) {F : Polynomial O} (hF : F.Monic) (m : ℕ) :
    typeOf (F.scaleRoots (π ^ m)) = typeOf F := by
  refine FactorizationType.ext ?_
  rw [typeOf_data, typeOf_data, monicFactors_scaleRoots hπ hF m, Multiset.map_map]
  refine Multiset.map_congr rfl (fun g hg => ?_)
  obtain ⟨hm, hi⟩ := (monicFactors_spec hF).1 g hg
  have hd : 0 < g.natDegree := by
    rcases Nat.eq_zero_or_pos g.natDegree with h0 | h0
    · exact absurd ((Polynomial.Monic.natDegree_eq_zero hm).1 h0 ▸ isUnit_one) hi.not_isUnit
    · exact h0
  exact efPair_scaleRoots hπ hm hd m

omit [IsDiscreteValuationRing O] in
/-- The substitution identity `F(π^m Y) = π^(m·n)·G(Y)` says exactly that `F = scaleRoots G (π^m)`
(monicity is not needed for this coefficient computation, only the degree match). This is the bridge between the recursion's own phrasing
and `typeOf_scaleRoots`. -/
theorem eq_scaleRoots_of_comp {π : O} (hπ : Irreducible π) {F G : Polynomial O}
    (hdeg : G.natDegree = F.natDegree) (m : ℕ)
    (hFG : F.comp (C (π ^ m) * X) = C (π ^ (m * F.natDegree)) * G) :
    F = G.scaleRoots (π ^ m) := by
  ext i
  have hco := congrArg (fun p => Polynomial.coeff p i) hFG
  simp only [comp_C_mul_X_coeff, coeff_C_mul] at hco
  rw [coeff_scaleRoots, hdeg]
  rcases le_or_gt i F.natDegree with hi | hi
  · have hsplit : π ^ (m * F.natDegree) = (π ^ m) ^ i * (π ^ m) ^ (F.natDegree - i) := by
      rw [← pow_add, ← pow_mul, Nat.add_sub_cancel' hi]
    rw [hsplit, mul_assoc] at hco
    exact mul_right_cancel₀ (pow_ne_zero i (pow_ne_zero m hπ.ne_zero))
      (by rw [hco]; ring)
  · rw [coeff_eq_zero_of_natDegree_lt hi, Nat.sub_eq_zero_of_le hi.le, pow_zero, mul_one]
    have hGi : G.coeff i = 0 := coeff_eq_zero_of_natDegree_lt (by omega)
    rw [hGi]

/-- **HYP.06 in the recursion's own phrasing.** -/
theorem typeOf_scale {π : O} (hπ : Irreducible π) {F G : Polynomial O}
    (hG : G.Monic) (hdeg : G.natDegree = F.natDegree) (m : ℕ)
    (hFG : F.comp (C (π ^ m) * X) = C (π ^ (m * F.natDegree)) * G) :
    typeOf F = typeOf G := by
  rw [eq_scaleRoots_of_comp hπ hdeg m hFG]
  exact typeOf_scaleRoots hπ hG m


/-! ### Non-vacuity gate for the scale relation

The extraction is not the identity map: it carries the Eisenstein `X² - π` to `X² - π³` —
precisely the polynomial whose residue degree the *old* `sInf` form of `inertiaDegOf` got wrong
(the defect recorded in `TypeOf.lean`'s module docstring, found 2026-08-13). `typeOf_scaleRoots`
says the two have the same splitting type, as they must (both generate `K(π^(1/2))`). -/

theorem scaleRoots_X_sq_sub_C {π : O} : (X ^ 2 - C π : Polynomial O).scaleRoots π
    = X ^ 2 - C (π ^ 3) := by
  have hd : (X ^ 2 - C π : Polynomial O).natDegree = 2 := natDegree_X_pow_sub_C
  ext i
  rw [coeff_scaleRoots, hd]
  rcases i with _ | _ | _ | n <;> simp [coeff_X_pow, coeff_C, -map_pow]
  ring

/-- **The gate fires**: `X² - π³` and `X² - π` have the same `typeOf`, by the scale relation. -/
theorem typeOf_scale_gate {π : O} (hπ : Irreducible π) :
    typeOf (X ^ 2 - C (π ^ 3) : Polynomial O) = typeOf (X ^ 2 - C π : Polynomial O) := by
  have hm : (X ^ 2 - C π : Polynomial O).Monic := monic_X_pow_sub_C π (by norm_num)
  have h1 := typeOf_scaleRoots (π := π) hπ hm 1
  rwa [pow_one, scaleRoots_X_sq_sub_C] at h1

end ScaleType

/-! ## Axiom census -/

section AxCheck

#print axioms Uniformity.Density.typeOf_shift
#print axioms Uniformity.Density.norm_scaleHom
#print axioms Uniformity.Density.typeOf_scaleRoots
#print axioms Uniformity.Density.typeOf_scale
#print axioms Uniformity.Density.typeOf_scale_gate

end AxCheck

end Uniformity.Density
