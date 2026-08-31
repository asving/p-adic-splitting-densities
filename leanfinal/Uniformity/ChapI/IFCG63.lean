/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import Uniformity.ChapI.IFCG61
import Uniformity.ChapI.IFCG32
import Uniformity.ChapI.IFCG16

/-!
# Uniformity.ChapI.IFCG63 — [DGT 2026-08-31] the Weierstrass/localization engine for
the diagonal `m ≥ 2` depth values: THE NORM STEP and THE BINARY LOCALIZATION, landed

Stage DGT of the cone census (design record `runs/wave-c/verdict_DGT.md`).  IGV's
IFCG61 confined VCL's axis-1 value side to the DIAGONAL reduced census
`#redDepthPairSet(n, N, v)` and derived (mathematics of record, battery-verified) the
master law `Σ_v P_v t^v = Z_m(t) = ∏_{j≤m} (1−s^j t^{j−1})/(1−s^j t^j)` via the route
norm → Hensel localization → `r`-adic Weierstrass peel → Euler assembly.  THIS file
transcribes the route's steps (a) and (b) — the norm step and the FULL binary
localization — to Lean, uniform in `q`, every level:

* **§0 ★★ THE NORM STEP (route step (a))**: `resultant_eq_norm` — for monic `F` over
  ANY nontrivial commutative ring, the pinned-size resultant IS the algebra norm:
  `Res(F, P, deg F, k) = N_{R[X]/(F)}(P)` for every window `k ≥ deg P`.  NOT in
  mathlib; proved by the adapted-basis block-triangular determinant — IFCG32 §1's
  `norm_mk_mul` technique run on mathlib's `sylvesterMap`: the codomain basis
  `{X^i}_{i<deg F} ⊔ {X^j·F}_{j<k}` of `R[X]_(deg F + k)` (`sylBasis`) makes the
  Sylvester matrix the product of a unitriangular change of basis (det `1`) and the
  block matrix `[[leftMul(P) , 0], [quotients, 1]]`.  Kit: `rootBasis_repr_mk` (the
  power-basis coordinates of `mk F Q` are the remainder coefficients).
* **§1 the reduced carrier reads as a norm**: ★ `redRes_eq_norm`
  (`redRes c b = N_{(Res O N)[X]/(monicPoly c)}(polyOf b)` — the depth of the reduced
  resultant IS the depth of the norm, as ring elements), `monicPoly_mulClass`, and
  ★ `redRes_norm_mul` — the norm splits over `mulClass` frames with NO coprimality
  (INS's landed `norm_mk_mul`).
* **§2 the localization identity**: `resultant_modByMonic_right` (the
  `classRes_eq_redRes` mechanism at any window) and ★ `redRes_mulClass`:
  `redRes (mulClass c₁ c₂) b = redRes c₁ (remOf c₁ b) · redRes c₂ (remOf c₂ b)` —
  sign-free, coprimality-free (mathlib's `resultant_mul_left`).
* **§3 depth additivity**: `resOrd_mul` — `resOrd (x·y) = min N (resOrd x + resOrd y)`
  (the windowed valuation is additive below the cap), and the exact-depth reader
  `resOrd_mul_eq_iff`.
* **§4 the CRT box split**: `crtPair_bijective` — for COPRIME monic frames over the
  truncation ring, `b ↦ (b mod F₁, b mod F₂)` is a bijection of the tail boxes
  (injectivity by Bézout + degree, surjectivity by cardinality).
* **§5 ★★ THE BINARY LOCALIZATION CENSUS (route step (b), frame level)**:
  `card_frameDepthSet_mulClass` — at a coprime product frame the depth-`v` box census
  is the CONVOLUTION of the factor censuses:
  `#fd(v, c₁·c₂) = Σ_{a≤v} #fd(a, c₁) · #fd(v−a, c₂)`.
* **§6 ★★ THE STRATUM ASSEMBLY (route step (b), stratum level)**:
  `isCoprime_monicPoly_of_stratum` (residual coprimality descends to the truncation
  ring — the Hensel Bézout lift pushed through the projection), and
  `card_stratumDepthSet_mul` — over a complete DVR, the stratified PAIR census
  (frame in the residual stratum × box at exact depth) at a coprime product residual
  is the depth convolution of the factor-stratum censuses (H.102's `bijOn_mulClass`
  frame bijection composed with §5).
* **§7 ★ THE SHAPE PARTITION**: `card_redDepthPairSet_eq_sum_strata` — IFCG61's
  diagonal reduced census at every depth IS the sum of the stratified censuses over
  all residual shapes.  With §6, every composite shape splits into its coprime parts:
  **the diagonal census is a sum over factor shapes**, with only the primary-shape
  values open.

## THE HONEST FENCE (the exact named remainder)

NOT proved here (IGV route steps (c), (d)): (i) **the Weierstrass peel** — the
primary-stratum censuses `#stratumDepthSet(n, N, v, r^e)` for `r` irreducible residual,
`e ≥ 1` (`δe = n`); IGV's `B_e` recursion at finite level (the `e = 1` unramified case
is the `(1,1)` law at scale `q^δ`); (ii) **the Euler/zeta assembly** — summing §7's
shape partition to the closed form `[t^v]Z_m · q^{2nN}` (the `F_q[x]` zeta collapse and
`q`-binomial extraction; note the shape count grows with `q`, so this is a genuine
assembly step, not a finite-sum transport); (iii) consequently the `ZcURLim` premise of
IFCG61's `zcURLim_depthDensity_of_reduced` at `n ≥ 2` is not yet fired — (i)+(ii) at
fixed `n` produce exactly the required diagonal values.  The vis-restriction (VCL
axis 3) untouched.  Nothing weakened; every consumed statement byte-untouched.

## Axiom fence (machine-exact at landing)

EVERY row of the AxCheck footer expects PURE Lean core
`{propext, Classical.choice, Quot.sound}` — the file consumes only mathlib resultant/
basis algebra, IFCG61's carrier kit, IFCG32's norm kit, H.100–H.102's stratum kit, and
`Uniformity.Hensel` (all landed Lean-core).  B.42, the C.33 cites, and
`AX_cellRecursion` must NOT occur.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

noncomputable section

namespace Uniformity.Density.IFCG63

open IsLocalRing Polynomial
open Uniformity.Density.Induction
open Uniformity.Density.IFCG61 (polyOf polyOf_coeff_lt polyOf_degree_lt polyOf_eq_self
  redRes redDepthPairSet mk_pow_dvd_iff_le_resOrd)
open Uniformity.Density.IFCG32 (mk_sum repr_basis_sum coeff_sum_C_X_pow
  natDegree_sum_C_X_pow_le norm_mk_one norm_mk_mul norm_mk_prod
  isCoprime_of_isCoprime_map_residue)

/-! ## §0 — ★★ THE NORM STEP: `Res(F, P) = N_{R[X]/(F)}(P)` for monic `F` -/

section NormStep

variable {R : Type*} [CommRing R] [Nontrivial R]

/-- Reconstruction from the coefficient window, degree form (handles `p = 0`, any `k`). -/
theorem polyOf_eq_self_of_degree_lt {k : ℕ} {p : Polynomial R}
    (hp : p.degree < (k : WithBot ℕ)) :
    polyOf (fun j : Fin k => p.coeff (j : ℕ)) = p := by
  rcases eq_or_ne p 0 with rfl | hp0
  · unfold Uniformity.Density.IFCG61.polyOf
    simp
  · exact polyOf_eq_self ((Polynomial.natDegree_lt_iff_degree_lt hp0).mpr hp)

/-- **Power-basis coordinates of `mk F Q` are the remainder coefficients.** -/
theorem rootBasis_repr_mk {F : Polynomial R} (hF : F.Monic) (Q : Polynomial R)
    (t : Fin F.natDegree) :
    (rootBasis hF).repr (AdjoinRoot.mk F Q) t = (Q %ₘ F).coeff (t : ℕ) := by
  have h0 : 0 < F.natDegree := t.pos
  have hne1 : F ≠ 1 := by
    intro h
    rw [h, Polynomial.natDegree_one] at h0
    omega
  have hdeg : (Q %ₘ F).natDegree < F.natDegree := Polynomial.natDegree_modByMonic_lt Q hF hne1
  have hmk : AdjoinRoot.mk F Q = AdjoinRoot.mk F (Q %ₘ F) := by
    rw [AdjoinRoot.mk_eq_mk]
    exact ⟨Q /ₘ F, by linear_combination -(Polynomial.modByMonic_add_div Q F)⟩
  have hsum : AdjoinRoot.mk F (Q %ₘ F)
      = ∑ i : Fin F.natDegree, (Q %ₘ F).coeff (i : ℕ) • rootBasis hF i := by
    have hpoly : Q %ₘ F = ∑ i : Fin F.natDegree,
        Polynomial.C ((Q %ₘ F).coeff (i : ℕ)) * Polynomial.X ^ (i : ℕ) :=
      (polyOf_eq_self hdeg).symm
    conv_lhs => rw [hpoly]
    rw [mk_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [rootBasis_apply, map_pow, AdjoinRoot.mk_X]
  rw [hmk, hsum, repr_basis_sum]

variable {F : Polynomial R} {k : ℕ}

/-- The adapted polynomial family `{X^i}_{i < deg F} ⊔ {X^j·F}_{j < k}`. -/
private def adaptedPoly (F : Polynomial R) {k : ℕ} (s : Fin F.natDegree ⊕ Fin k) :
    Polynomial R :=
  Sum.elim (fun i : Fin F.natDegree => Polynomial.X ^ (i : ℕ))
    (fun j : Fin k => Polynomial.X ^ (j : ℕ) * F) s

private theorem adaptedPoly_mem (hF : F.Monic) (s : Fin F.natDegree ⊕ Fin k) :
    adaptedPoly F s ∈ Polynomial.degreeLT R (F.natDegree + k) := by
  rcases s with i | j
  · rw [adaptedPoly, Sum.elim_inl, Polynomial.mem_degreeLT, Polynomial.degree_X_pow]
    exact_mod_cast lt_of_lt_of_le i.isLt (Nat.le_add_right _ _)
  · rw [adaptedPoly, Sum.elim_inr, Polynomial.mem_degreeLT]
    have hm : (Polynomial.X ^ (j : ℕ) * F).Monic := (Polynomial.monic_X_pow _).mul hF
    have hd : (Polynomial.X ^ (j : ℕ) * F).natDegree = (j : ℕ) + F.natDegree := by
      rw [(Polynomial.monic_X_pow _).natDegree_mul hF, Polynomial.natDegree_X_pow]
    rw [Polynomial.degree_eq_natDegree hm.ne_zero, hd]
    have hlt : (j : ℕ) + F.natDegree < F.natDegree + k := by
      have := j.isLt
      omega
    exact_mod_cast hlt

/-- The quotient by the monic frame of anything of degree `< deg F + k` fits the `k`-window. -/
private theorem div_degree_lt (hF : F.Monic) {p : Polynomial R}
    (hp : p.degree < ((F.natDegree + k : ℕ) : WithBot ℕ)) :
    (p /ₘ F).degree < (k : WithBot ℕ) := by
  rcases eq_or_ne (p /ₘ F) 0 with h | h
  · rw [h, Polynomial.degree_zero]
    exact WithBot.bot_lt_coe k
  · have hp0 : p ≠ 0 := by
      rintro rfl
      exact h (Polynomial.zero_divByMonic F)
    have hge : F.natDegree ≤ p.natDegree := by
      have hnot : ¬ p.degree < F.degree := fun hc =>
        h ((Polynomial.divByMonic_eq_zero_iff hF).mpr hc)
      exact Polynomial.natDegree_le_natDegree (le_of_not_gt hnot)
    have hq : (p /ₘ F).natDegree = p.natDegree - F.natDegree :=
      Polynomial.natDegree_divByMonic p hF
    have hpd : p.natDegree < F.natDegree + k :=
      (Polynomial.natDegree_lt_iff_degree_lt hp0).mpr hp
    exact (Polynomial.natDegree_lt_iff_degree_lt h).mp (by omega)

/-- The division decomposition of any `p` of degree `< deg F + k` over the adapted family. -/
private theorem poly_decomp (hF : F.Monic) (h0 : 0 < F.natDegree) {p : Polynomial R}
    (hp : p.degree < ((F.natDegree + k : ℕ) : WithBot ℕ)) :
    p = (∑ t : Fin F.natDegree, Polynomial.C ((p %ₘ F).coeff (t : ℕ)) * Polynomial.X ^ (t : ℕ))
      + (∑ j : Fin k, Polynomial.C ((p /ₘ F).coeff (j : ℕ)) * Polynomial.X ^ (j : ℕ)) * F := by
  have hne1 : F ≠ 1 := by
    intro h
    rw [h, Polynomial.natDegree_one] at h0
    omega
  have hrem : (∑ t : Fin F.natDegree,
      Polynomial.C ((p %ₘ F).coeff (t : ℕ)) * Polynomial.X ^ (t : ℕ)) = p %ₘ F :=
    polyOf_eq_self (Polynomial.natDegree_modByMonic_lt p hF hne1)
  have hquot : (∑ j : Fin k,
      Polynomial.C ((p /ₘ F).coeff (j : ℕ)) * Polynomial.X ^ (j : ℕ)) = p /ₘ F :=
    polyOf_eq_self_of_degree_lt (div_degree_lt hF hp)
  rw [hrem, hquot, mul_comm (p /ₘ F) F]
  exact (Polynomial.modByMonic_add_div p F).symm

/-- The division decomposition, lifted to the window submodule. -/
private theorem adapted_expand (hF : F.Monic) (h0 : 0 < F.natDegree)
    (z : Polynomial.degreeLT R (F.natDegree + k)) :
    z = ∑ s : Fin F.natDegree ⊕ Fin k,
        (Sum.elim (fun t : Fin F.natDegree => (((z : Polynomial R)) %ₘ F).coeff (t : ℕ))
          (fun j : Fin k => (((z : Polynomial R)) /ₘ F).coeff (j : ℕ)) s)
          • (⟨adaptedPoly F s, adaptedPoly_mem hF s⟩ :
              Polynomial.degreeLT R (F.natDegree + k)) := by
  have hz : ((z : Polynomial R)).degree < ((F.natDegree + k : ℕ) : WithBot ℕ) :=
    Polynomial.mem_degreeLT.mp z.2
  apply Subtype.ext
  rw [AddSubmonoidClass.coe_finsetSum]
  simp only [SetLike.val_smul, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, adaptedPoly,
    Polynomial.smul_eq_C_mul]
  conv_lhs => rw [poly_decomp hF h0 hz]
  congr 1
  rw [Finset.sum_mul]
  exact Finset.sum_congr rfl fun j _ => by ring

private theorem adapted_linearIndependent (hF : F.Monic) (h0 : 0 < F.natDegree) :
    LinearIndependent R (fun s : Fin F.natDegree ⊕ Fin k =>
      (⟨adaptedPoly F s, adaptedPoly_mem hF s⟩ : Polynomial.degreeLT R (F.natDegree + k))) := by
  classical
  have hcomp : LinearIndependent R (fun s : Fin F.natDegree ⊕ Fin k => adaptedPoly F s) := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    rw [Fintype.sum_sum_type] at hg
    simp only [adaptedPoly, Sum.elim_inl, Sum.elim_inr, Polynomial.smul_eq_C_mul] at hg
    set PD := ∑ i : Fin F.natDegree, Polynomial.C (g (Sum.inl i)) * Polynomial.X ^ (i : ℕ)
      with hPDdef
    set PC := ∑ j : Fin k, Polynomial.C (g (Sum.inr j)) * Polynomial.X ^ (j : ℕ) with hPCdef
    have hg' : PD + PC * F = 0 := by
      rw [hPDdef, hPCdef, Finset.sum_mul, ← hg]
      congr 1
      exact Finset.sum_congr rfl fun j _ => by ring
    have hPDdeg : PD.natDegree ≤ F.natDegree - 1 := by
      rw [hPDdef]; exact natDegree_sum_C_X_pow_le _ _
    have hPC0 : PC = 0 := by
      by_contra hne
      have hPD : PD = -(PC * F) := by linear_combination hg'
      have hdeg1 : (PC * F).natDegree = PC.natDegree + F.natDegree :=
        Polynomial.natDegree_mul' (by
          rw [hF.leadingCoeff, mul_one]
          exact Polynomial.leadingCoeff_ne_zero.mpr hne)
      have hPDdeg2 : PD.natDegree = PC.natDegree + F.natDegree := by
        rw [hPD, Polynomial.natDegree_neg, hdeg1]
      omega
    have hPD0 : PD = 0 := by
      have h := hg'
      rw [hPC0, zero_mul, add_zero] at h
      exact h
    intro s
    rcases s with i | j
    · have h : PD.coeff (i : ℕ) = 0 := by rw [hPD0]; exact Polynomial.coeff_zero _
      rw [hPDdef, coeff_sum_C_X_pow] at h
      exact h
    · have h : PC.coeff (j : ℕ) = 0 := by rw [hPC0]; exact Polynomial.coeff_zero _
      rw [hPCdef, coeff_sum_C_X_pow] at h
      exact h
  exact LinearIndependent.of_comp (Polynomial.degreeLT R (F.natDegree + k)).subtype hcomp

private theorem adapted_span (hF : F.Monic) (h0 : 0 < F.natDegree) :
    ⊤ ≤ Submodule.span R (Set.range (fun s : Fin F.natDegree ⊕ Fin k =>
      (⟨adaptedPoly F s, adaptedPoly_mem hF s⟩ : Polynomial.degreeLT R (F.natDegree + k)))) := by
  rintro z -
  rw [adapted_expand hF h0 z]
  exact Submodule.sum_mem _ fun s _ =>
    Submodule.smul_mem _ _ (Submodule.subset_span ⟨s, rfl⟩)

/-- **The adapted basis** of `R[X]_(deg F + k)`: `{X^i} ⊔ {X^j·F}`. -/
private noncomputable def sylBasis (hF : F.Monic) (h0 : 0 < F.natDegree) :
    Module.Basis (Fin F.natDegree ⊕ Fin k) R (Polynomial.degreeLT R (F.natDegree + k)) :=
  Module.Basis.mk (adapted_linearIndependent hF h0) (adapted_span hF h0)

private theorem sylBasis_coe (hF : F.Monic) (h0 : 0 < F.natDegree)
    (s : Fin F.natDegree ⊕ Fin k) :
    ((sylBasis hF h0 s : Polynomial.degreeLT R (F.natDegree + k)) : Polynomial R)
      = adaptedPoly F s := by
  rw [sylBasis, Module.Basis.mk_apply]

/-- Coordinates in the adapted basis: remainder coefficients on the `inl` block, quotient
coefficients on the `inr` block. -/
private theorem sylBasis_repr (hF : F.Monic) (h0 : 0 < F.natDegree)
    (z : Polynomial.degreeLT R (F.natDegree + k)) (s : Fin F.natDegree ⊕ Fin k) :
    (sylBasis hF h0).repr z s
      = Sum.elim (fun t : Fin F.natDegree => (((z : Polynomial R)) %ₘ F).coeff (t : ℕ))
          (fun j : Fin k => (((z : Polynomial R)) /ₘ F).coeff (j : ℕ)) s := by
  have hb : ∀ s' : Fin F.natDegree ⊕ Fin k,
      (⟨adaptedPoly F s', adaptedPoly_mem hF s'⟩ : Polynomial.degreeLT R (F.natDegree + k))
        = sylBasis hF h0 s' := fun s' => Subtype.ext (sylBasis_coe hF h0 s').symm
  conv_lhs => rw [adapted_expand hF h0 z]
  simp only [hb]
  rw [repr_basis_sum]

/-- ★★ **THE NORM STEP** — for monic `F` over any nontrivial commutative ring, the
pinned-size resultant IS the algebra norm of the second argument in `R[X]/(F)`:
`Res(F, P, deg F, k) = N_{R[X]/(F)}(P)` for every window `k ≥ deg P`.  (IGV route
step (a); the depth of the resultant IS the depth of the norm, as ring elements.) -/
theorem resultant_eq_norm {R : Type*} [CommRing R] [Nontrivial R] {F P : Polynomial R}
    (hF : F.Monic) {k : ℕ} (hP : P.natDegree ≤ k) :
    Polynomial.resultant F P F.natDegree k = Algebra.norm R (AdjoinRoot.mk F P) := by
  classical
  rcases Nat.eq_zero_or_pos F.natDegree with h0 | h0
  · -- degenerate frame: `F = 1`, both sides are `1`
    have hF1 : F = 1 := hF.natDegree_eq_zero.mp h0
    subst hF1
    rw [norm_mk_one, Polynomial.natDegree_one, Polynomial.resultant_one_left]
    simp
  -- the triangular change-of-basis determinant
  have hdetT : (LinearMap.toMatrix ((sylBasis (k := k) hF h0).reindex finSumFinEquiv)
      (Polynomial.degreeLT.basis R (F.natDegree + k)) LinearMap.id).det = 1 := by
    have htri : (LinearMap.toMatrix ((sylBasis (k := k) hF h0).reindex finSumFinEquiv)
        (Polynomial.degreeLT.basis R (F.natDegree + k)) LinearMap.id).BlockTriangular id := by
      intro i j hij
      simp only [id_eq] at hij
      rw [LinearMap.toMatrix_apply, LinearMap.id_apply, Module.Basis.reindex_apply,
        Polynomial.degreeLT.basis_repr, sylBasis_coe]
      revert hij
      induction j using Fin.addCases with
      | left j₀ =>
        intro hij
        rw [finSumFinEquiv_symm_apply_castAdd, adaptedPoly, Sum.elim_inl,
          Polynomial.coeff_X_pow, if_neg]
        intro hcon
        rw [Fin.lt_def, Fin.val_castAdd] at hij
        omega
      | right j₀ =>
        intro hij
        rw [finSumFinEquiv_symm_apply_natAdd, adaptedPoly, Sum.elim_inr]
        apply Polynomial.coeff_eq_zero_of_natDegree_lt
        rw [(Polynomial.monic_X_pow _).natDegree_mul hF, Polynomial.natDegree_X_pow]
        rw [Fin.lt_def, Fin.val_natAdd] at hij
        omega
    rw [Matrix.det_of_upperTriangular htri]
    refine Finset.prod_eq_one fun j _ => ?_
    rw [LinearMap.toMatrix_apply, LinearMap.id_apply, Module.Basis.reindex_apply,
      Polynomial.degreeLT.basis_repr, sylBasis_coe]
    induction j using Fin.addCases with
    | left j₀ =>
      rw [finSumFinEquiv_symm_apply_castAdd, adaptedPoly, Sum.elim_inl, Fin.val_castAdd,
        Polynomial.coeff_X_pow, if_pos rfl]
    | right j₀ =>
      rw [finSumFinEquiv_symm_apply_natAdd, adaptedPoly, Sum.elim_inr, Fin.val_natAdd]
      have hm : (Polynomial.X ^ (j₀ : ℕ) * F).Monic := (Polynomial.monic_X_pow _).mul hF
      have hd : (Polynomial.X ^ (j₀ : ℕ) * F).natDegree = (j₀ : ℕ) + F.natDegree := by
        rw [(Polynomial.monic_X_pow _).natDegree_mul hF, Polynomial.natDegree_X_pow]
      have hcoeff := hm.coeff_natDegree
      rw [hd] at hcoeff
      rw [Nat.add_comm]
      exact hcoeff
  -- the reindexed middle matrix is a double-`submatrix` of the block matrix
  have hsub : LinearMap.toMatrix (((Polynomial.degreeLT.basis R F.natDegree).prod
        (Polynomial.degreeLT.basis R k)).reindex finSumFinEquiv)
        ((sylBasis (k := k) hF h0).reindex finSumFinEquiv)
        (Polynomial.sylvesterMap F P (le_refl F.natDegree) hP)
      = (LinearMap.toMatrix ((Polynomial.degreeLT.basis R F.natDegree).prod
            (Polynomial.degreeLT.basis R k)) (sylBasis (k := k) hF h0)
          (Polynomial.sylvesterMap F P (le_refl F.natDegree) hP)).submatrix
          finSumFinEquiv.symm finSumFinEquiv.symm := by
    ext i j
    rw [Matrix.submatrix_apply, LinearMap.toMatrix_apply, LinearMap.toMatrix_apply,
      Module.Basis.reindex_apply, Module.Basis.repr_reindex_apply]
  -- the block structure in the adapted basis
  have hblock : LinearMap.toMatrix ((Polynomial.degreeLT.basis R F.natDegree).prod
        (Polynomial.degreeLT.basis R k)) (sylBasis (k := k) hF h0)
        (Polynomial.sylvesterMap F P (le_refl F.natDegree) hP)
      = Matrix.fromBlocks (Algebra.leftMulMatrix (rootBasis hF) (AdjoinRoot.mk F P)) 0
          (Matrix.of fun (j : Fin k) (i : Fin F.natDegree) =>
            ((P * Polynomial.X ^ (i : ℕ)) /ₘ F).coeff (j : ℕ)) 1 := by
    ext s d
    rw [LinearMap.toMatrix_apply]
    rcases d with i | j
    · have hB : ((Polynomial.degreeLT.basis R F.natDegree).prod
          (Polynomial.degreeLT.basis R k)) (Sum.inl i)
          = (Polynomial.degreeLT.basis R F.natDegree i, 0) := by
        rw [Module.Basis.prod_apply]
        simp
      rw [hB, sylBasis_repr]
      have hval : ((Polynomial.sylvesterMap F P (le_refl F.natDegree) hP
          (Polynomial.degreeLT.basis R F.natDegree i, 0) :
            Polynomial.degreeLT R (F.natDegree + k)) : Polynomial R)
          = P * Polynomial.X ^ (i : ℕ) := by
        rw [Polynomial.sylvesterMap_apply_coe]
        simp
      rw [hval]
      rcases s with t | j'
      · rw [Sum.elim_inl, Matrix.fromBlocks_apply₁₁,
          Algebra.leftMulMatrix_eq_repr_mul]
        have hmul : AdjoinRoot.mk F P * rootBasis hF i
            = AdjoinRoot.mk F (P * Polynomial.X ^ (i : ℕ)) := by
          rw [rootBasis_apply, ← AdjoinRoot.mk_X, ← map_pow, ← map_mul]
        rw [hmul, rootBasis_repr_mk hF]
      · rw [Sum.elim_inr, Matrix.fromBlocks_apply₂₁, Matrix.of_apply]
    · have hB : ((Polynomial.degreeLT.basis R F.natDegree).prod
          (Polynomial.degreeLT.basis R k)) (Sum.inr j)
          = (0, Polynomial.degreeLT.basis R k j) := by
        rw [Module.Basis.prod_apply]
        simp
      rw [hB, sylBasis_repr]
      have hval : ((Polynomial.sylvesterMap F P (le_refl F.natDegree) hP
          (0, Polynomial.degreeLT.basis R k j) :
            Polynomial.degreeLT R (F.natDegree + k)) : Polynomial R)
          = F * Polynomial.X ^ (j : ℕ) := by
        rw [Polynomial.sylvesterMap_apply_coe]
        simp
      rw [hval]
      have hrem : (F * Polynomial.X ^ (j : ℕ)) %ₘ F = 0 :=
        (Polynomial.modByMonic_eq_zero_iff_dvd hF).mpr (dvd_mul_right F _)
      have hquot : (F * Polynomial.X ^ (j : ℕ)) /ₘ F = Polynomial.X ^ (j : ℕ) :=
        Polynomial.mul_divByMonic_cancel_left _ hF
      rcases s with t | j'
      · rw [Sum.elim_inl, hrem, Polynomial.coeff_zero, Matrix.fromBlocks_apply₁₂,
          Matrix.zero_apply]
      · rw [Sum.elim_inr, hquot, Matrix.fromBlocks_apply₂₂, Polynomial.coeff_X_pow,
          Matrix.one_apply]
        by_cases hjj : j' = j
        · rw [if_pos (by rw [hjj]), if_pos hjj]
        · rw [if_neg (fun hcon => hjj (Fin.ext hcon)), if_neg hjj]
  -- assemble
  rw [Polynomial.resultant, ← Polynomial.toMatrix_sylvesterMap' F P (le_refl F.natDegree) hP,
    ← LinearMap.id_comp (Polynomial.sylvesterMap F P (le_refl F.natDegree) hP),
    LinearMap.toMatrix_comp _ ((sylBasis (k := k) hF h0).reindex finSumFinEquiv) _
      LinearMap.id (Polynomial.sylvesterMap F P (le_refl F.natDegree) hP),
    Matrix.det_mul, hdetT, one_mul, hsub, Matrix.det_submatrix_equiv_self, hblock,
    Matrix.det_fromBlocks_zero₁₂, Matrix.det_one, mul_one,
    Algebra.norm_eq_matrix_det (rootBasis hF) (AdjoinRoot.mk F P)]

end NormStep

/-! ## §1 — the reduced diagonal carrier reads as a norm -/

section RedResNorm

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)]

/-- ★ The reduced diagonal resultant IS the norm of the tail box in the frame's root
algebra over the truncation ring. -/
theorem redRes_eq_norm {n N : ℕ} (hN : 0 < N) (c b : Coeff O n N) :
    redRes c b
      = Algebra.norm (Res O N) (AdjoinRoot.mk (monicPoly c) (polyOf b)) := by
  letI : Nontrivial (Res O N) := nontrivial_res O hN
  have hm : (monicPoly c).Monic := monicPoly_monic_ring c
  have hd : (monicPoly c).natDegree = n := monicPoly_natDegree_ring c
  have hP : (polyOf b).natDegree ≤ n :=
    Polynomial.natDegree_le_iff_degree_le.mpr (le_of_lt (polyOf_degree_lt b))
  have h := resultant_eq_norm (P := polyOf b) hm (k := n) hP
  rw [hd] at h
  exact h

/-- The frame product at the class level: `monicPoly (mulClass c₁ c₂)` IS the polynomial
product. -/
theorem monicPoly_mulClass {n₁ n₂ N : ℕ} (hN : 0 < N)
    (c₁ : Coeff O n₁ N) (c₂ : Coeff O n₂ N) :
    monicPoly (mulClass c₁ c₂) = monicPoly c₁ * monicPoly c₂ := by
  letI : Nontrivial (Res O N) := nontrivial_res O hN
  have hm : (monicPoly c₁ * monicPoly c₂).Monic :=
    (monicPoly_monic_ring c₁).mul (monicPoly_monic_ring c₂)
  have hd : (monicPoly c₁ * monicPoly c₂).natDegree = n₁ + n₂ := by
    rw [(monicPoly_monic_ring c₁).natDegree_mul (monicPoly_monic_ring c₂),
      monicPoly_natDegree_ring, monicPoly_natDegree_ring]
  rw [mulClass_apply]
  exact monicPoly_coeff_self_ring hm hd

/-- ★ **The norm splits over the frame factors** (no coprimality — INS's block
triangular `norm_mk_mul`): the reduced resultant at a product frame is the product of
the factor norms of the SAME tail box. -/
theorem redRes_norm_mul {n₁ n₂ N : ℕ} (hN : 0 < N)
    (c₁ : Coeff O n₁ N) (c₂ : Coeff O n₂ N) (b : Coeff O (n₁ + n₂) N) :
    redRes (mulClass c₁ c₂) b
      = Algebra.norm (Res O N) (AdjoinRoot.mk (monicPoly c₁) (polyOf b))
        * Algebra.norm (Res O N) (AdjoinRoot.mk (monicPoly c₂) (polyOf b)) := by
  letI : Nontrivial (Res O N) := nontrivial_res O hN
  rw [redRes_eq_norm hN, monicPoly_mulClass hN c₁ c₂,
    norm_mk_mul (monicPoly_monic_ring c₁) (monicPoly_monic_ring c₂)]

end RedResNorm

/-! ## §2 — the modulus split at pinned sizes (the localization identity) -/

section ModulusSplit

variable {R : Type*} [CommRing R] [Nontrivial R]

/-- Resultant against a monic modulus only sees the remainder: size-drop to the
diagonal pinned sizes.  (The `classRes_eq_redRes` mechanism at general window `K`.) -/
theorem resultant_modByMonic_right {F g : Polynomial R} (hF : F.Monic)
    (h0 : 0 < F.natDegree) {K : ℕ} (hg : g.natDegree ≤ K) (hFK : F.natDegree ≤ K) :
    Polynomial.resultant F g F.natDegree K
      = Polynomial.resultant F (g %ₘ F) F.natDegree F.natDegree := by
  have hne1 : F ≠ 1 := by
    intro h
    rw [h, Polynomial.natDegree_one] at h0
    omega
  have hrd : (g %ₘ F).natDegree ≤ F.natDegree :=
    (Polynomial.natDegree_modByMonic_lt g hF hne1).le
  have hqd : (g /ₘ F).natDegree = g.natDegree - F.natDegree :=
    Polynomial.natDegree_divByMonic g hF
  have h1 : Polynomial.resultant F (g %ₘ F + F * (g /ₘ F)) F.natDegree K
      = Polynomial.resultant F (g %ₘ F) F.natDegree K :=
    Polynomial.resultant_add_mul_right F (g %ₘ F) (g /ₘ F) F.natDegree K
      (by omega) (le_refl _)
  have h2 := Polynomial.resultant_add_right_deg (f := F) (g := g %ₘ F) (m := F.natDegree)
    (n := F.natDegree) (K - F.natDegree) hrd
  have hKe : F.natDegree + (K - F.natDegree) = K := by omega
  rw [hKe] at h2
  conv_lhs => rw [← Polynomial.modByMonic_add_div g F]
  rw [h1, h2, hF.coeff_natDegree, one_pow, one_mul]

end ModulusSplit

section RedResMul

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)]

/-- The CRT residue coordinates: the coefficient vector of `polyOf b %ₘ monicPoly c`. -/
def remOf {n m N : ℕ} (c : Coeff O n N) (b : Coeff O m N) : Coeff O n N :=
  fun i => (polyOf b %ₘ monicPoly c).coeff (i : ℕ)

theorem polyOf_remOf {n m N : ℕ} (hN : 0 < N) (h0 : 0 < n)
    (c : Coeff O n N) (b : Coeff O m N) :
    polyOf (remOf c b) = polyOf b %ₘ monicPoly c := by
  letI : Nontrivial (Res O N) := nontrivial_res O hN
  have hne1 : monicPoly c ≠ 1 := by
    intro h
    have hd := monicPoly_natDegree_ring c
    rw [h, Polynomial.natDegree_one] at hd
    omega
  have hdeg : (polyOf b %ₘ monicPoly c).natDegree < n := by
    have h := Polynomial.natDegree_modByMonic_lt (polyOf b) (monicPoly_monic_ring c) hne1
    rwa [monicPoly_natDegree_ring] at h
  exact polyOf_eq_self hdeg

/-- ★ **THE LOCALIZATION IDENTITY on the reduced carrier**: the reduced resultant at a
product frame is the product of the reduced resultants of the CRT residues — no
coprimality, no sign. -/
theorem redRes_mulClass {n₁ n₂ N : ℕ} (hN : 0 < N) (h₁ : 0 < n₁) (h₂ : 0 < n₂)
    (c₁ : Coeff O n₁ N) (c₂ : Coeff O n₂ N) (b : Coeff O (n₁ + n₂) N) :
    redRes (mulClass c₁ c₂) b = redRes c₁ (remOf c₁ b) * redRes c₂ (remOf c₂ b) := by
  letI : Nontrivial (Res O N) := nontrivial_res O hN
  have hm₁ : (monicPoly c₁).Monic := monicPoly_monic_ring c₁
  have hm₂ : (monicPoly c₂).Monic := monicPoly_monic_ring c₂
  have hd₁ : (monicPoly c₁).natDegree = n₁ := monicPoly_natDegree_ring c₁
  have hd₂ : (monicPoly c₂).natDegree = n₂ := monicPoly_natDegree_ring c₂
  have hgd : (polyOf b).natDegree ≤ n₁ + n₂ :=
    Polynomial.natDegree_le_iff_degree_le.mpr (le_of_lt (polyOf_degree_lt b))
  show Polynomial.resultant (monicPoly (mulClass c₁ c₂)) (polyOf b) (n₁ + n₂) (n₁ + n₂) = _
  rw [monicPoly_mulClass hN c₁ c₂]
  have hml := Polynomial.resultant_mul_left (monicPoly c₁) (monicPoly c₂) (polyOf b)
    (n₁ + n₂) hgd
  rw [hd₁, hd₂] at hml
  rw [hml]
  have hr₁ := resultant_modByMonic_right hm₁ (by omega : 0 < (monicPoly c₁).natDegree)
    (K := n₁ + n₂) hgd (by omega : (monicPoly c₁).natDegree ≤ n₁ + n₂)
  have hr₂ := resultant_modByMonic_right hm₂ (by omega : 0 < (monicPoly c₂).natDegree)
    (K := n₁ + n₂) hgd (by omega : (monicPoly c₂).natDegree ≤ n₁ + n₂)
  rw [hd₁] at hr₁
  rw [hd₂] at hr₂
  rw [hr₁, hr₂, Uniformity.Density.IFCG61.redRes, Uniformity.Density.IFCG61.redRes,
    polyOf_remOf hN h₁ c₁ b, polyOf_remOf hN h₂ c₂ b]

end RedResMul

/-! ## §3 — the windowed valuation is additive below the cap -/

section ResOrdMul

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

/-- `resOrd` of a product: additive, capped at the window. -/
theorem resOrd_mul {N : ℕ} (x y : Res O N) :
    resOrd (x * y) = min N (resOrd x + resOrd y) := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible O
  rcases eq_or_ne x 0 with rfl | hx0
  · rw [zero_mul]
    have h0 : resOrd (0 : Res O N) = N := (resOrd_eq_iff _).mpr rfl
    rw [h0]
    have := resOrd_le y
    omega
  rcases eq_or_ne y 0 with rfl | hy0
  · rw [mul_zero]
    have h0 : resOrd (0 : Res O N) = N := (resOrd_eq_iff _).mpr rfl
    rw [h0]
    have := resOrd_le x
    omega
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective y
  have hA : resOrd (Ideal.Quotient.mk ((maximalIdeal O) ^ N) a) < N :=
    lt_of_le_of_ne (resOrd_le _) fun h => hx0 ((resOrd_eq_iff _).mp h)
  have hB : resOrd (Ideal.Quotient.mk ((maximalIdeal O) ^ N) b) < N :=
    lt_of_le_of_ne (resOrd_le _) fun h => hy0 ((resOrd_eq_iff _).mp h)
  set A := resOrd (Ideal.Quotient.mk ((maximalIdeal O) ^ N) a) with hAdef
  set B := resOrd (Ideal.Quotient.mk ((maximalIdeal O) ^ N) b) with hBdef
  have hdvda : π ^ A ∣ a := (resOrd_ge_iff hπ hA.le a).mp le_rfl
  have hdvdb : π ^ B ∣ b := (resOrd_ge_iff hπ hB.le b).mp le_rfl
  have hnda : ¬ π ^ (A + 1) ∣ a := fun h => by
    have := (resOrd_ge_iff hπ (by omega : A + 1 ≤ N) a).mpr h
    omega
  have hndb : ¬ π ^ (B + 1) ∣ b := fun h => by
    have := (resOrd_ge_iff hπ (by omega : B + 1 ≤ N) b).mpr h
    omega
  obtain ⟨u, hu⟩ := hdvda
  obtain ⟨w, hw⟩ := hdvdb
  have hπu : ¬ π ∣ u := fun ⟨t, ht⟩ => hnda ⟨t, by rw [hu, ht]; ring⟩
  have hπw : ¬ π ∣ w := fun ⟨t, ht⟩ => hndb ⟨t, by rw [hw, ht]; ring⟩
  rw [← map_mul]
  apply le_antisymm
  · rcases Nat.lt_or_ge (A + B) N with hNlt | hNle
    case inr =>
      rw [min_eq_left hNle]
      exact resOrd_le _
    · rw [min_eq_right hNlt.le]
      by_contra hcon
      rw [Nat.not_le] at hcon
      have hdvd : π ^ (A + B + 1) ∣ a * b :=
        (resOrd_ge_iff hπ (by omega : A + B + 1 ≤ N) _).mp (by omega)
      obtain ⟨t, ht⟩ := hdvd
      have he : π ^ (A + B) * (u * w) = π ^ (A + B) * (π * t) := by
        calc π ^ (A + B) * (u * w) = a * b := by rw [hu, hw]; ring
          _ = π ^ (A + B + 1) * t := ht
          _ = π ^ (A + B) * (π * t) := by ring
      have huw : u * w = π * t := mul_left_cancel₀ (pow_ne_zero _ hπ.ne_zero) he
      rcases (hπ.prime).2.2 u w ⟨t, huw⟩ with h | h
      · exact hπu h
      · exact hπw h
  · have hdvd : π ^ (min N (A + B)) ∣ a * b := by
      have hAB : π ^ (A + B) ∣ a * b := ⟨u * w, by rw [hu, hw]; ring⟩
      exact dvd_trans (pow_dvd_pow π (min_le_right _ _)) hAB
    exact (resOrd_ge_iff hπ (min_le_left _ _) _).mpr hdvd

/-- The exact-depth convolution reader below the cap. -/
theorem resOrd_mul_eq_iff {N v : ℕ} (hv : v < N) (x y : Res O N) :
    resOrd (x * y) = v ↔ resOrd x + resOrd y = v := by
  rw [resOrd_mul]
  omega

end ResOrdMul

/-! ## §4 — the CRT box bijection for coprime monic frames -/

section CrtBox

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)]

/-- The CRT residue pair of a tail box at a pair of frames. -/
def crtPair {n₁ n₂ N : ℕ} (c₁ : Coeff O n₁ N) (c₂ : Coeff O n₂ N)
    (b : Coeff O (n₁ + n₂) N) : Coeff O n₁ N × Coeff O n₂ N :=
  (remOf c₁ b, remOf c₂ b)

theorem crtPair_bijective {n₁ n₂ N : ℕ} (hN : 0 < N) (h₁ : 0 < n₁) (h₂ : 0 < n₂)
    {c₁ : Coeff O n₁ N} {c₂ : Coeff O n₂ N}
    (hcop : IsCoprime (monicPoly c₁) (monicPoly c₂)) :
    Function.Bijective (crtPair c₁ c₂) := by
  letI : Nontrivial (Res O N) := nontrivial_res O hN
  have hinj : Function.Injective (crtPair c₁ c₂) := by
    intro b b' h
    have h1 : remOf c₁ b = remOf c₁ b' := congrArg Prod.fst h
    have h2 : remOf c₂ b = remOf c₂ b' := congrArg Prod.snd h
    have hp1 : polyOf b %ₘ monicPoly c₁ = polyOf b' %ₘ monicPoly c₁ := by
      rw [← polyOf_remOf hN h₁ c₁ b, ← polyOf_remOf hN h₁ c₁ b', h1]
    have hp2 : polyOf b %ₘ monicPoly c₂ = polyOf b' %ₘ monicPoly c₂ := by
      rw [← polyOf_remOf hN h₂ c₂ b, ← polyOf_remOf hN h₂ c₂ b', h2]
    have hb1 := Polynomial.modByMonic_add_div (polyOf b) (monicPoly c₁)
    have hb1' := Polynomial.modByMonic_add_div (polyOf b') (monicPoly c₁)
    have hb2 := Polynomial.modByMonic_add_div (polyOf b) (monicPoly c₂)
    have hb2' := Polynomial.modByMonic_add_div (polyOf b') (monicPoly c₂)
    have hd1 : monicPoly c₁ ∣ polyOf b - polyOf b' :=
      ⟨polyOf b /ₘ monicPoly c₁ - polyOf b' /ₘ monicPoly c₁, by
        linear_combination -hb1 + hb1' + hp1⟩
    have hd2 : monicPoly c₂ ∣ polyOf b - polyOf b' :=
      ⟨polyOf b /ₘ monicPoly c₂ - polyOf b' /ₘ monicPoly c₂, by
        linear_combination -hb2 + hb2' + hp2⟩
    have hdvd : monicPoly c₁ * monicPoly c₂ ∣ polyOf b - polyOf b' := hcop.mul_dvd hd1 hd2
    have hmul : (monicPoly c₁ * monicPoly c₂).Monic :=
      (monicPoly_monic_ring c₁).mul (monicPoly_monic_ring c₂)
    have hmuld : (monicPoly c₁ * monicPoly c₂).natDegree = n₁ + n₂ := by
      rw [(monicPoly_monic_ring c₁).natDegree_mul (monicPoly_monic_ring c₂),
        monicPoly_natDegree_ring, monicPoly_natDegree_ring]
    have hzero : polyOf b - polyOf b' = 0 := by
      by_contra hne
      obtain ⟨t, ht⟩ := hdvd
      have ht0 : t ≠ 0 := by
        rintro rfl
        rw [mul_zero] at ht
        exact hne ht
      have hdegeq : (polyOf b - polyOf b').natDegree
          = n₁ + n₂ + t.natDegree := by
        rw [ht, Polynomial.natDegree_mul' (by
          rw [hmul.leadingCoeff, one_mul]
          exact Polynomial.leadingCoeff_ne_zero.mpr ht0), hmuld]
      have hdlt : (polyOf b - polyOf b').natDegree < n₁ + n₂ := by
        refine (Polynomial.natDegree_lt_iff_degree_lt hne).mpr ?_
        refine lt_of_le_of_lt (Polynomial.degree_sub_le _ _) ?_
        exact max_lt (polyOf_degree_lt b) (polyOf_degree_lt b')
      omega
    have hpoly : polyOf b = polyOf b' := by linear_combination hzero
    funext i
    have hco : (polyOf b).coeff (i : ℕ) = (polyOf b').coeff (i : ℕ) := by rw [hpoly]
    rwa [polyOf_coeff_lt b i.isLt, polyOf_coeff_lt b' i.isLt] at hco
  refine (Nat.bijective_iff_injective_and_card _).mpr ⟨hinj, ?_⟩
  rw [Nat.card_prod, card_coeff, card_coeff, card_coeff, ← pow_add]
  congr 1
  ring

end CrtBox

/-! ## §5 — ★★ THE BINARY LOCALIZATION CENSUS (the depth convolution) -/

section Convolution

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)]

/-- The per-frame depth-`v` census set on the tail box (windowed-valuation form,
uniformizer-free). -/
def frameDepthSet (O : Type*) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Finite (ResidueField O)] (n L v : ℕ) (c : Coeff O n L) : Set (Coeff O n L) :=
  {b | resOrd (redRes c b) = v}

/-- The bridge to IFCG61's carrier: below the cap, the pair `(c, b)` is in the reduced
depth stratum iff `b` is in the frame's census set. -/
theorem mem_redDepthPairSet_iff_frame {π : O} (hπ : Irreducible π) {n L v : ℕ}
    (hv : v < L) (c b : Coeff O n L) :
    (c, b) ∈ redDepthPairSet O π n L v ↔ b ∈ frameDepthSet O n L v c := by
  simp only [Uniformity.Density.IFCG61.redDepthPairSet, frameDepthSet, Set.mem_setOf_eq]
  rw [mk_pow_dvd_iff_le_resOrd hπ hv.le, mk_pow_dvd_iff_le_resOrd hπ hv]
  omega

/-- ★★ **THE BINARY LOCALIZATION CENSUS**: at a coprime product frame, the depth-`v`
box census is the convolution of the factor censuses.  (IGV route step (b): the
Hensel-local pieces are independent and the depth adds.) -/
private theorem natCard_prod_set {α β : Type*} (s : Set α) (t : Set β) :
    Nat.card (s ×ˢ t : Set (α × β)) = Nat.card s * Nat.card t := by
  rw [← Nat.card_prod]
  exact Nat.card_congr (Equiv.Set.prod s t)

theorem card_frameDepthSet_mulClass {n₁ n₂ N v : ℕ} (h₁ : 0 < n₁) (h₂ : 0 < n₂)
    (hv : v < N) (c₁ : Coeff O n₁ N) (c₂ : Coeff O n₂ N)
    (hcop : IsCoprime (monicPoly c₁) (monicPoly c₂)) :
    Nat.card (frameDepthSet O (n₁ + n₂) N v (mulClass c₁ c₂))
      = ∑ a ∈ Finset.range (v + 1),
          Nat.card (frameDepthSet O n₁ N a c₁) * Nat.card (frameDepthSet O n₂ N (v - a) c₂) := by
  classical
  have hN : 0 < N := by omega
  letI : Nontrivial (Res O N) := nontrivial_res O hN
  haveI : Fintype (Coeff O (n₁ + n₂) N) := Fintype.ofFinite _
  set S := frameDepthSet O (n₁ + n₂) N v (mulClass c₁ c₂) with hSdef
  set φ : Coeff O (n₁ + n₂) N → ℕ := fun b => resOrd (redRes c₁ (remOf c₁ b)) with hφdef
  set ψ : Coeff O (n₁ + n₂) N → ℕ := fun b => resOrd (redRes c₂ (remOf c₂ b)) with hψdef
  have hmem : ∀ b, b ∈ S ↔ φ b + ψ b = v := by
    intro b
    rw [hSdef, frameDepthSet, Set.mem_setOf_eq, redRes_mulClass hN h₁ h₂ c₁ c₂ b,
      resOrd_mul_eq_iff hv]
  -- the per-fiber image identity under the CRT bijection
  have himg : ∀ a : ℕ, a ≤ v →
      crtPair c₁ c₂ '' {b | b ∈ S ∧ φ b = a}
        = (frameDepthSet O n₁ N a c₁) ×ˢ (frameDepthSet O n₂ N (v - a) c₂) := by
    intro a ha
    ext p
    constructor
    · rintro ⟨b, ⟨hb, hba⟩, rfl⟩
      have hsum := (hmem b).mp hb
      refine ⟨?_, ?_⟩
      · show φ b = a
        exact hba
      · show ψ b = v - a
        omega
    · rintro ⟨hp₁, hp₂⟩
      obtain ⟨b, hbeq⟩ := (crtPair_bijective hN h₁ h₂ hcop).2 p
      have hb1 : remOf c₁ b = p.1 := congrArg Prod.fst hbeq
      have hb2 : remOf c₂ b = p.2 := congrArg Prod.snd hbeq
      have hφb : φ b = a := by
        show resOrd (redRes c₁ (remOf c₁ b)) = a
        rw [hb1]
        exact hp₁
      have hψb : ψ b = v - a := by
        show resOrd (redRes c₂ (remOf c₂ b)) = v - a
        rw [hb2]
        exact hp₂
      exact ⟨b, ⟨(hmem b).mpr (by omega), hφb⟩, hbeq⟩
  -- per-fiber cardinality via the bijection
  have hcard : ∀ a : ℕ, a ≤ v →
      Nat.card {b | b ∈ S ∧ φ b = a}
        = Nat.card (frameDepthSet O n₁ N a c₁) * Nat.card (frameDepthSet O n₂ N (v - a) c₂) := by
    intro a ha
    calc Nat.card {b | b ∈ S ∧ φ b = a}
        = Nat.card (crtPair c₁ c₂ '' {b | b ∈ S ∧ φ b = a}) :=
          (Nat.card_image_of_injective (crtPair_bijective hN h₁ h₂ hcop).1 _).symm
      _ = Nat.card ((frameDepthSet O n₁ N a c₁) ×ˢ (frameDepthSet O n₂ N (v - a) c₂)) := by
          rw [himg a ha]
      _ = Nat.card (frameDepthSet O n₁ N a c₁) * Nat.card (frameDepthSet O n₂ N (v - a) c₂) :=
          natCard_prod_set _ _
  -- fiberwise decomposition of the census
  have hfin : S.toFinset.card
      = ∑ a ∈ Finset.range (v + 1), (S.toFinset.filter (fun b => φ b = a)).card := by
    apply Finset.card_eq_sum_card_fiberwise
    intro b hb
    have hb' : b ∈ S := by simpa [Set.mem_toFinset] using hb
    have hsum := (hmem b).mp hb'
    simp only [Finset.coe_range, Set.mem_Iio]
    omega
  have hfilter : ∀ a : ℕ, (S.toFinset.filter (fun b => φ b = a)).card
      = Nat.card {b | b ∈ S ∧ φ b = a} := by
    intro a
    rw [Nat.card_coe_set_eq, Set.ncard_eq_toFinset_card']
    congr 1
    ext b
    simp [Set.mem_toFinset]
  rw [Nat.card_coe_set_eq, Set.ncard_eq_toFinset_card', hfin]
  refine Finset.sum_congr rfl fun a ha => ?_
  rw [Finset.mem_range] at ha
  rw [hfilter a, hcard a (by omega)]

end Convolution

/-! ## §6 — ★★ THE STRATUM ASSEMBLY: the pair census over a coprime product stratum -/

section StratumAssembly

attribute [local instance] Classical.propDecidable

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)]

/-- The fiber decomposition of a pair census over its first coordinate. -/
private theorem card_pairSet_fiber {α β : Type*} [Fintype α] [Finite β]
    (S : Set α) (T : α → Set β) :
    Nat.card {d : α × β | d.1 ∈ S ∧ d.2 ∈ T d.1}
      = ∑ c ∈ S.toFinset, Nat.card (T c) := by
  classical
  have e : {d : α × β | d.1 ∈ S ∧ d.2 ∈ T d.1}
      ≃ Σ c : ↥S.toFinset, ↥(T (c : α)) :=
    { toFun := fun d => ⟨⟨d.val.1, Set.mem_toFinset.mpr d.prop.1⟩, ⟨d.val.2, d.prop.2⟩⟩
      invFun := fun p => ⟨(p.1.val, p.2.val), ⟨Set.mem_toFinset.mp p.1.prop, p.2.prop⟩⟩
      left_inv := fun d => rfl
      right_inv := fun p => rfl }
  rw [Nat.card_congr e, Nat.card_sigma, ← Finset.sum_coe_sort S.toFinset
    (fun c => Nat.card (T c))]

/-- The all-frames fiber decomposition (over the full first coordinate). -/
private theorem card_pairSet_fiber_univ {α β : Type*} [Fintype α] [Finite β]
    (T : α → Set β) :
    Nat.card {d : α × β | d.2 ∈ T d.1} = ∑ c : α, Nat.card (T c) := by
  have e : {d : α × β | d.2 ∈ T d.1} ≃ Σ c : α, ↥(T c) :=
    { toFun := fun d => ⟨d.val.1, ⟨d.val.2, d.prop⟩⟩
      invFun := fun p => ⟨(p.1, p.2.val), p.2.prop⟩
      left_inv := fun d => rfl
      right_inv := fun p => rfl }
  rw [Nat.card_congr e, Nat.card_sigma]

/-- **Residual coprimality of stratified frames descends to the truncation ring** — the
level-0 Bézout witness lifts (`Uniformity.Hensel.isCoprime_of_map_eq`, as landed it sits
in the complete-DVR section) and pushes through the projection. -/
theorem isCoprime_monicPoly_of_stratum [IsAdicComplete (maximalIdeal O) O] {n₁ n₂ N : ℕ}
    {g₁ g₂ : Polynomial (ResidueField O)} (hg₁ : g₁.Monic) (hg₂ : g₂.Monic)
    (hcop : IsCoprime g₁ g₂) {c₁ : Coeff O n₁ N} {c₂ : Coeff O n₂ N}
    (h₁ : c₁ ∈ levelZeroStratum O n₁ N g₁) (h₂ : c₂ ∈ levelZeroStratum O n₂ N g₂) :
    IsCoprime (monicPoly c₁) (monicPoly c₂) := by
  obtain ⟨a₁, ha₁⟩ := proj_surjective' O n₁ N c₁
  obtain ⟨a₂, ha₂⟩ := proj_surjective' O n₂ N c₂
  have hcopO : IsCoprime (monicPoly a₁) (monicPoly a₂) :=
    Uniformity.Hensel.isCoprime_of_map_eq (monicPoly_monic a₁) (monicPoly_monic a₂)
      hg₁ hg₂ hcop (h₁ a₁ ha₁) (h₂ a₂ ha₂)
  have hmap := hcopO.map (Polynomial.mapRingHom (Ideal.Quotient.mk ((maximalIdeal O) ^ N)))
  simpa only [Polynomial.coe_mapRingHom, map_monicPoly_proj, ha₁, ha₂] using hmap

/-- **The stratified pair census**: monic frame in the residual stratum `g`, tail box at
exact reduced depth `v`. -/
def stratumDepthSet (O : Type*) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Finite (ResidueField O)] (n L v : ℕ) (g : Polynomial (ResidueField O)) :
    Set (Coeff O n L × Coeff O n L) :=
  {d | d.1 ∈ levelZeroStratum O n L g ∧ d.2 ∈ frameDepthSet O n L v d.1}

/-- The stratified pair census is the frame-fiber sum.  (The `Fintype` instance is an
explicit argument to keep the `toFinset` in the statement canonical; instantiate with
`Fintype.ofFinite`.) -/
theorem card_stratumDepthSet_eq_sum {n L v : ℕ} [Fintype (Coeff O n L)]
    (g : Polynomial (ResidueField O)) :
    Nat.card (stratumDepthSet O n L v g)
      = ∑ c ∈ (levelZeroStratum O n L g).toFinset, Nat.card (frameDepthSet O n L v c) :=
  card_pairSet_fiber _ _

/-- IFCG61's reduced depth stratum is the all-frames fiber sum of the new censuses. -/
theorem card_redDepthPairSet_eq_sum {π : O} {n N v : ℕ} [Fintype (Coeff O n N)]
    (hπ : Irreducible π) (hv : v < N) :
    Nat.card (redDepthPairSet O π n N v)
      = ∑ c : Coeff O n N, Nat.card (frameDepthSet O n N v c) := by
  have hset : redDepthPairSet O π n N v
      = {d : Coeff O n N × Coeff O n N | d.2 ∈ frameDepthSet O n N v d.1} := by
    ext ⟨c, b⟩
    simp only [Set.mem_setOf_eq]
    exact mem_redDepthPairSet_iff_frame hπ hv c b
  rw [hset, card_pairSet_fiber_univ]

/-- ★★ **THE STRATUM ASSEMBLY** (the binary shape split of the diagonal census): over a
complete DVR, the stratified pair census at a coprime product residual is the depth
CONVOLUTION of the factor-stratum censuses — the Hensel frame bijection (H.102), the CRT
box bijection (§4), and the depth additivity (§3) composed. -/
theorem card_stratumDepthSet_mul [IsAdicComplete (maximalIdeal O) O] {n₁ n₂ N v : ℕ}
    (h₁ : 0 < n₁) (h₂ : 0 < n₂) (hv : v < N)
    {g₁ g₂ : Polynomial (ResidueField O)} (hg₁ : g₁.Monic) (hg₂ : g₂.Monic)
    (hd₁ : g₁.natDegree = n₁) (hd₂ : g₂.natDegree = n₂) (hcop : IsCoprime g₁ g₂) :
    Nat.card (stratumDepthSet O (n₁ + n₂) N v (g₁ * g₂))
      = ∑ a ∈ Finset.range (v + 1),
          Nat.card (stratumDepthSet O n₁ N a g₁)
            * Nat.card (stratumDepthSet O n₂ N (v - a) g₂) := by
  classical
  have hN : 1 ≤ N := by omega
  haveI f1 : Fintype (Coeff O n₁ N) := Fintype.ofFinite _
  haveI f2 : Fintype (Coeff O n₂ N) := Fintype.ofFinite _
  haveI f12 : Fintype (Coeff O (n₁ + n₂) N) := Fintype.ofFinite _
  rw [card_stratumDepthSet_eq_sum]
  -- reindex the frame sum along the Hensel stratum bijection (H.102)
  have hbij := bijOn_mulClass (O := O) hN hg₁ hg₂ hd₁ hd₂ hcop
  have hreindex : ∑ c ∈ (levelZeroStratum O (n₁ + n₂) N (g₁ * g₂)).toFinset,
        Nat.card (frameDepthSet O (n₁ + n₂) N v c)
      = ∑ p ∈ ((levelZeroStratum O n₁ N g₁) ×ˢ (levelZeroStratum O n₂ N g₂)).toFinset,
          Nat.card (frameDepthSet O (n₁ + n₂) N v (mulClass p.1 p.2)) := by
    refine (Finset.sum_bij (fun p _ => mulClass p.1 p.2) ?_ ?_ ?_ ?_).symm
    · intro p hp
      rw [Set.mem_toFinset] at hp ⊢
      exact hbij.mapsTo hp
    · intro p hp q hq heq
      rw [Set.mem_toFinset] at hp hq
      exact hbij.injOn hp hq heq
    · intro c hc
      rw [Set.mem_toFinset] at hc
      obtain ⟨p, hp, hpc⟩ := hbij.surjOn hc
      exact ⟨p, Set.mem_toFinset.mpr hp, hpc⟩
    · intro p hp
      rfl
  rw [hreindex]
  -- the per-frame convolution (coprimality descends per stratified pair)
  have hconv : ∀ p ∈ ((levelZeroStratum O n₁ N g₁) ×ˢ (levelZeroStratum O n₂ N g₂)).toFinset,
      Nat.card (frameDepthSet O (n₁ + n₂) N v (mulClass p.1 p.2))
        = ∑ a ∈ Finset.range (v + 1),
            Nat.card (frameDepthSet O n₁ N a p.1)
              * Nat.card (frameDepthSet O n₂ N (v - a) p.2) := by
    intro p hp
    rw [Set.mem_toFinset] at hp
    exact card_frameDepthSet_mulClass h₁ h₂ hv p.1 p.2
      (isCoprime_monicPoly_of_stratum hg₁ hg₂ hcop hp.1 hp.2)
  rw [Finset.sum_congr rfl hconv, Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [card_stratumDepthSet_eq_sum, card_stratumDepthSet_eq_sum, Finset.sum_mul_sum,
    Set.toFinset_prod, Finset.sum_product]

end StratumAssembly

/-! ## §7 — the shape partition: the diagonal census is a sum over residual shapes -/

section ShapePartition

attribute [local instance] Classical.propDecidable

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)]

private theorem monicPoly_coeff_lt' {S : Type*} [CommRing S] {n : ℕ} (a : Fin n → S)
    {i : ℕ} (hi : i < n) : (monicPoly a).coeff i = a ⟨i, hi⟩ := by
  classical
  unfold monicPoly
  rw [Polynomial.coeff_add, Polynomial.coeff_X_pow, if_neg (Nat.ne_of_lt hi), zero_add,
    Polynomial.finsetSum_coeff, Finset.sum_eq_single (⟨i, hi⟩ : Fin n)]
  · rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_pos rfl, mul_one]
  · intro b _ hbi
    rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
      if_neg fun h => hbi (Fin.ext h.symm), mul_zero]
  · simp

/-- Every level-`N ≥ 1` frame class lies in exactly one residual-shape stratum, indexed
by the residual coefficient vector. -/
theorem existsUnique_stratum_vec {n N : ℕ} (hN : 1 ≤ N) (c : Coeff O n N) :
    ∃! r : Fin n → ResidueField O, c ∈ levelZeroStratum O n N (monicPoly r) := by
  obtain ⟨a, ha⟩ := proj_surjective' O n N c
  refine ⟨fun i => residue O (a i), ?_, ?_⟩
  · exact (mem_levelZeroStratum_iff hN _ _).2 ⟨a, ha, map_monicPoly _ a⟩
  · intro r hr
    have hmap : (monicPoly a).map (residue O) = monicPoly r := hr a ha
    rw [map_monicPoly] at hmap
    funext i
    have hco : (monicPoly r).coeff (i : ℕ)
        = (monicPoly (fun j => residue O (a j))).coeff (i : ℕ) := by rw [hmap]
    rwa [monicPoly_coeff_lt' r i.isLt, monicPoly_coeff_lt' _ i.isLt] at hco

/-- ★ **THE SHAPE PARTITION**: the diagonal reduced census at every depth is the sum of
the stratified censuses over all residual shapes (indexed by residual coefficient
vectors).  With `card_stratumDepthSet_mul`, every composite-shape summand splits as a
convolution of its coprime-part censuses — the diagonal census IS a sum over factor
shapes, with only the primary-shape values (`ḡ = r^e`) left open. -/
theorem card_redDepthPairSet_eq_sum_strata {π : O} {n N v : ℕ}
    [Fintype (Coeff O n N)] [Fintype (Fin n → ResidueField O)]
    (hπ : Irreducible π) (hv : v < N) :
    Nat.card (redDepthPairSet O π n N v)
      = ∑ r : Fin n → ResidueField O,
          Nat.card (stratumDepthSet O n N v (monicPoly r)) := by
  have hN : 1 ≤ N := by omega
  have hEU : ∀ c : Coeff O n N,
      ∃! r : Fin n → ResidueField O, c ∈ levelZeroStratum O n N (monicPoly r) :=
    fun c => existsUnique_stratum_vec hN c
  set χ : Coeff O n N → (Fin n → ResidueField O) := fun c => (hEU c).choose with hχdef
  have hχmem : ∀ c, c ∈ levelZeroStratum O n N (monicPoly (χ c)) :=
    fun c => (hEU c).choose_spec.1
  have hχuniq : ∀ c r, c ∈ levelZeroStratum O n N (monicPoly r) → χ c = r :=
    fun c r hr => ((hEU c).choose_spec.2 r hr).symm
  rw [card_redDepthPairSet_eq_sum hπ hv,
    ← Finset.sum_fiberwise_of_maps_to (t := Finset.univ)
      (fun (c : Coeff O n N) _ => Finset.mem_univ (χ c))
      (fun c => Nat.card (frameDepthSet O n N v c))]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [card_stratumDepthSet_eq_sum]
  refine Finset.sum_congr ?_ fun c _ => rfl
  ext c
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Set.mem_toFinset]
  constructor
  · rintro rfl
    exact hχmem c
  · exact hχuniq c r

end ShapePartition

end Uniformity.Density.IFCG63

end

/-! ## AXCHECK FOOTER — EVERY row expects PURE Lean core
`{propext, Classical.choice, Quot.sound}`.  B.42, the C.33 cites, and
`AX_cellRecursion` must NOT occur. -/
#print axioms Uniformity.Density.IFCG63.polyOf_eq_self_of_degree_lt
#print axioms Uniformity.Density.IFCG63.rootBasis_repr_mk
#print axioms Uniformity.Density.IFCG63.resultant_eq_norm
#print axioms Uniformity.Density.IFCG63.redRes_eq_norm
#print axioms Uniformity.Density.IFCG63.monicPoly_mulClass
#print axioms Uniformity.Density.IFCG63.redRes_norm_mul
#print axioms Uniformity.Density.IFCG63.resultant_modByMonic_right
#print axioms Uniformity.Density.IFCG63.polyOf_remOf
#print axioms Uniformity.Density.IFCG63.redRes_mulClass
#print axioms Uniformity.Density.IFCG63.resOrd_mul
#print axioms Uniformity.Density.IFCG63.resOrd_mul_eq_iff
#print axioms Uniformity.Density.IFCG63.crtPair_bijective
#print axioms Uniformity.Density.IFCG63.mem_redDepthPairSet_iff_frame
#print axioms Uniformity.Density.IFCG63.card_frameDepthSet_mulClass
#print axioms Uniformity.Density.IFCG63.isCoprime_monicPoly_of_stratum
#print axioms Uniformity.Density.IFCG63.card_stratumDepthSet_eq_sum
#print axioms Uniformity.Density.IFCG63.card_redDepthPairSet_eq_sum
#print axioms Uniformity.Density.IFCG63.card_stratumDepthSet_mul
#print axioms Uniformity.Density.IFCG63.existsUnique_stratum_vec
#print axioms Uniformity.Density.IFCG63.card_redDepthPairSet_eq_sum_strata
