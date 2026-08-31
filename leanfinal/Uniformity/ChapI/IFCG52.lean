/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import Uniformity.ChapI.IFCG50

/-!
# Uniformity.ChapI.IFCG52 — [KDW 2026-08-30] KRASNER CLOSED: `KrasnerIrredAt n` at EVERY
`n` (hence `KrasnerDeepAt`, `KrasnerAt`), and the capstone's `a2` field UNCONDITIONAL

**Unit KDW.**  KDN's IFCG50 left the capstone's ENTIRE `a2` field resting on the single
classical residual `KrasnerDeepAt m` (irreducible separable monic over a complete DVR
with non-irreducible residue reduction is eventually decided).  THIS file proves the
STRONGER `KrasnerIrredAt m` outright, for every `m`, by a fully algebraic Krasner
mechanism — no normed fields, no `IsKrasner`, no maximal orders:

**THE ISO ROUTE.**  Let `f = monicPoly a` be irreducible with `Res(f, f') = u·π^{v₀}`
(finite `v₀` by the separability hypothesis), and let `N := 2v₀ + 1`.  For ANY monic
`g ≡ f mod π^N`:

1. `Res(g, f') ≡ Res(f, f') mod π^N` (the resultant is a polynomial in the coefficients
   at pinned degrees — `resultant_map_map` through `O/π^N`), so `Res(g, f')` has exact
   depth `v₀` and IFCG41's Bezout witness gives `g·p + f'·q = C(π^{v₀})`.  Evaluated at
   `x₀ := AdjoinRoot.root g` this yields `c·q(x₀) = π̄^{v₀}` with `c := f'(x₀)` — the
   derivative divides `π̄^{v₀}` INSIDE the order `A_g := AdjoinRoot g`.
2. **Newton in the order** (§2): `A_g` is π-adically complete via coordinates in the
   power basis (the same `IsPrecomplete` trick as IFCG49's König limit).  Since
   `f(x₀) = (f−g)(x₀) ∈ π̄^N·A_g ⊆ π̄·c²·A_g`, the Taylor fixed-point iteration
   converges to `ξ ∈ A_g` with `f(ξ) = 0` and `ξ ≡ x₀ mod π̄`.
3. **The unit-determinant isomorphism** (§3): `Φ := AdjoinRoot.liftHom f ξ` maps the
   power basis of `A_f` to `ξ^j ≡ x₀^j mod π̄`, so its matrix is `≡ 1 mod 𝔪` and its
   determinant is a unit: `Φ` is an O-ALGEBRA ISOMORPHISM `A_f ≃ₐ[O] A_g`.
4. **Transport** (§4): `A_f` is a domain (`f` prime in the UFD `O[X]`), so `A_g` is a
   domain, so `g` is IRREDUCIBLE; `Algebra.norm` is invariant under the isomorphism
   (multiplication-operator conjugation), so `normValues f = normValues g`, so
   `efPair g = efPair f`, so `typeOf g = ⟨{efPair f}⟩ = typeOf f`.

Hence the level-`N` class of `a` is `typeOf f`-DECIDED: `KrasnerIrredAt n` (§5), and

    ★★★ `krasnerIrredAt : ∀ n, KrasnerIrredAt n`                 -- UNCONDITIONAL
    ★★★ `krasnerDeepAt : ∀ n, KrasnerDeepAt n`                   -- the charged Prop
    ★★★ `krasnerAt : ∀ n, KrasnerAt n`
    ★★★ `drainageAt_all : ∀ n, DrainageAt n`                     -- THE a2 FIELD CLOSES

`drainageAt_all` is byte-identical to the capstone's `a2` consumer shape
(`CapstoneHypotheses.a2 : DrainageAt n`, I10_I15_I18) — the field is now supplied
unconditionally at every degree.

## Honesty

`KrasnerIrredAt`, `KrasnerDeepAt`, `KrasnerAt`, `DrainageAt`, `DecidedAt`, `typeOf`,
`efPair`, `normValues` are consumed byte-unchanged from IFCG50/IFCG49/the corpus;
nothing is weakened — the fires are implications INTO the landed Props.  All statements
are uniform in `q`, `n` (∀-`O` with `O : Type`, the corpus universe convention).
Axioms: Lean core only (the file adds no axiom and consumes no cite).
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

namespace Uniformity.Density.IFCG52

open IsLocalRing Polynomial
open Uniformity.Density.IFCG49
open Uniformity.Density.IFCG50

/-! ## §0 Coordinate calculus on the order `AdjoinRoot g` (monic `g`)

The power basis turns π-adic statements in `A_g` into coordinatewise statements in `O`:
divisibility, Hausdorffness, and limits of Cauchy sequences all reduce to `O`, where
adic completeness lives. -/

section Coord

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)]

variable {g : Polynomial O} (hg : g.Monic)

/-- Coordinates of a `π^m`-multiple are `π^m`-multiples. -/
theorem pow_dvd_repr_of_pow_dvd {π : O} {m : ℕ} {y : AdjoinRoot g}
    (h : (algebraMap O (AdjoinRoot g) π) ^ m ∣ y)
    (i : Fin (AdjoinRoot.powerBasis' hg).dim) :
    π ^ m ∣ (AdjoinRoot.powerBasis' hg).basis.repr y i := by
  obtain ⟨w, rfl⟩ := h
  have h1 : (algebraMap O (AdjoinRoot g) π) ^ m * w = (π ^ m) • w := by
    rw [Algebra.smul_def, map_pow]
  rw [h1, map_smul, Finsupp.smul_apply, smul_eq_mul]
  exact dvd_mul_right _ _

/-- Conversely, an element with all coordinates in `π^m O` is a `π^m`-multiple. -/
theorem pow_dvd_of_pow_dvd_repr {π : O} {m : ℕ} {y : AdjoinRoot g}
    (h : ∀ i, π ^ m ∣ (AdjoinRoot.powerBasis' hg).basis.repr y i) :
    (algebraMap O (AdjoinRoot g) π) ^ m ∣ y := by
  classical
  choose d hd using h
  refine ⟨(AdjoinRoot.powerBasis' hg).basis.repr.symm (Finsupp.equivFunOnFinite.symm d), ?_⟩
  have h1 : (algebraMap O (AdjoinRoot g) π) ^ m
        * (AdjoinRoot.powerBasis' hg).basis.repr.symm (Finsupp.equivFunOnFinite.symm d)
      = (π ^ m) • (AdjoinRoot.powerBasis' hg).basis.repr.symm
          (Finsupp.equivFunOnFinite.symm d) := by
    rw [Algebra.smul_def, map_pow]
  rw [h1]
  apply (AdjoinRoot.powerBasis' hg).basis.repr.injective
  rw [map_smul, LinearEquiv.apply_symm_apply]
  ext i
  rw [Finsupp.smul_apply, smul_eq_mul]
  exact hd i

variable [IsAdicComplete (maximalIdeal O) O]

include hg in
/-- π-adic Hausdorffness of the order: divisible by every `π^m` ⟹ zero. -/
theorem eq_zero_of_forall_pow_dvd {π : O} (hπ : Irreducible π) {y : AdjoinRoot g}
    (h : ∀ m, (algebraMap O (AdjoinRoot g) π) ^ m ∣ y) : y = 0 := by
  have hcoord : ∀ i, (AdjoinRoot.powerBasis' hg).basis.repr y i = 0 := by
    intro i
    by_contra hne
    obtain ⟨k, hk⟩ := IFCG50.exists_notMem_maximalIdeal_pow hne
    exact hk ((IFCG50.mem_maximalIdeal_pow_iff_dvd hπ k _).mpr
      (pow_dvd_repr_of_pow_dvd hg (h k) i))
  have h1 : (AdjoinRoot.powerBasis' hg).basis.repr y = 0 := Finsupp.ext hcoord
  exact ((AdjoinRoot.powerBasis' hg).basis.repr.map_eq_zero_iff).mp h1

include hg in
/-- π-adic completeness of the order: a Cauchy sequence has a limit. -/
theorem exists_limit_of_cauchy {π : O} (hπ : Irreducible π) (z : ℕ → AdjoinRoot g)
    (hz : ∀ {m M : ℕ}, m ≤ M → (algebraMap O (AdjoinRoot g) π) ^ m ∣ z M - z m) :
    ∃ w : AdjoinRoot g, ∀ m, (algebraMap O (AdjoinRoot g) π) ^ m ∣ w - z m := by
  classical
  have hcau : ∀ i : Fin (AdjoinRoot.powerBasis' hg).dim, ∀ {m M : ℕ}, m ≤ M →
      (AdjoinRoot.powerBasis' hg).basis.repr (z m) i
        ≡ (AdjoinRoot.powerBasis' hg).basis.repr (z M) i
          [SMOD ((maximalIdeal O) ^ m • ⊤ : Ideal O)] := by
    intro i m M hmM
    rw [← Ideal.one_eq_top, Ideal.smul_eq_mul, mul_one, SModEq.sub_mem]
    have h1 : π ^ m ∣ (AdjoinRoot.powerBasis' hg).basis.repr (z M - z m) i :=
      pow_dvd_repr_of_pow_dvd hg (hz hmM) i
    rw [map_sub, Finsupp.sub_apply] at h1
    rw [IFCG50.mem_maximalIdeal_pow_iff_dvd hπ]
    exact dvd_sub_comm.mp h1
  choose L hL using fun i : Fin (AdjoinRoot.powerBasis' hg).dim =>
    IsPrecomplete.prec (inferInstance : IsPrecomplete (maximalIdeal O) O)
      (f := fun m => (AdjoinRoot.powerBasis' hg).basis.repr (z m) i)
      (fun {m M} h => hcau i h)
  classical
  refine ⟨(AdjoinRoot.powerBasis' hg).basis.repr.symm (Finsupp.equivFunOnFinite.symm L),
    fun m => ?_⟩
  refine pow_dvd_of_pow_dvd_repr hg fun i => ?_
  rw [map_sub, Finsupp.sub_apply]
  have hrepr : (AdjoinRoot.powerBasis' hg).basis.repr
      ((AdjoinRoot.powerBasis' hg).basis.repr.symm (Finsupp.equivFunOnFinite.symm L)) i
      = L i := by
    rw [LinearEquiv.apply_symm_apply]
    rfl
  rw [hrepr]
  have h3 := hL i m
  rw [← Ideal.one_eq_top, Ideal.smul_eq_mul, mul_one, SModEq.sub_mem] at h3
  rw [IFCG50.mem_maximalIdeal_pow_iff_dvd hπ] at h3
  exact dvd_sub_comm.mp h3

end Coord

/-! ## §1 The quadratic Taylor identity (any commutative ring) -/

section Taylor

/-- `F(x + y) = F(x) + F'(x)·y + y²·(tail)(y)` with the tail an EVALUATION of the fixed
polynomial `(taylor x F).divX.divX` — the form the Newton contraction needs. -/
theorem eval_add_eq_taylor_quadratic {A : Type*} [CommRing A] (F : Polynomial A)
    (x y : A) :
    F.eval (x + y) = F.eval x + F.derivative.eval x * y
      + y ^ 2 * (((Polynomial.taylor x F).divX.divX).eval y) := by
  have h0 : (Polynomial.taylor x F).eval y = F.eval (x + y) := by
    rw [Polynomial.taylor_eval, add_comm]
  have h1 : Polynomial.taylor x F
      = Polynomial.X * (Polynomial.taylor x F).divX
        + Polynomial.C ((Polynomial.taylor x F).coeff 0) :=
    (Polynomial.X_mul_divX_add _).symm
  have h2 : (Polynomial.taylor x F).divX
      = Polynomial.X * (Polynomial.taylor x F).divX.divX
        + Polynomial.C ((Polynomial.taylor x F).divX.coeff 0) :=
    (Polynomial.X_mul_divX_add _).symm
  calc F.eval (x + y) = (Polynomial.taylor x F).eval y := h0.symm
    _ = (Polynomial.taylor x F).coeff 0
        + y * ((Polynomial.taylor x F).divX.coeff 0
          + y * ((Polynomial.taylor x F).divX.divX.eval y)) := by
        conv_lhs => rw [h1, h2]
        simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
          Polynomial.eval_X]
        ring
    _ = F.eval x + F.derivative.eval x * y
        + y ^ 2 * (((Polynomial.taylor x F).divX.divX).eval y) := by
        rw [Polynomial.coeff_divX, Polynomial.taylor_coeff_zero,
          Polynomial.taylor_coeff_one]
        ring

end Taylor

/-! ## §2 NEWTON IN THE ORDER — a root of `f` in `AdjoinRoot g` from closeness

The quantitative Hensel step, run inside `A_g` with the Bezout witness supplying the
exact division of `f(x₀)` by `f'(x₀)²·π`. -/

section Newton

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [IsAdicComplete (maximalIdeal O) O] [Finite (ResidueField O)]

/-- ★★ **THE NEWTON ROOT**: if `g ≡ f mod π^{2v+1}` and the elimination ideal of
`(g, f')` reaches `π^v`, then `f` has a root in the order `AdjoinRoot g`, congruent to
`root g` mod `π`. -/
theorem exists_aeval_eq_zero_of_close {π : O} (hπ : Irreducible π)
    {f g : Polynomial O} (hg : g.Monic) {v : ℕ}
    (hcong : Polynomial.C (π ^ (2 * v + 1)) ∣ f - g)
    (hbez : ∃ p q : Polynomial O,
      g * p + (Polynomial.derivative f) * q = Polynomial.C (π ^ v)) :
    ∃ ξ : AdjoinRoot g, Polynomial.aeval ξ f = 0
      ∧ (algebraMap O (AdjoinRoot g) π) ∣ ξ - AdjoinRoot.root g := by
  obtain ⟨p, q, hpq⟩ := hbez
  obtain ⟨h₀, hh₀⟩ := hcong
  set x₀ : AdjoinRoot g := AdjoinRoot.root g with hx₀
  set π' : AdjoinRoot g := algebraMap O (AdjoinRoot g) π with hπ'
  set c : AdjoinRoot g := Polynomial.aeval x₀ (Polynomial.derivative f) with hc
  -- the Bezout division: `c · q(x₀) = π'^v` — the derivative divides `π'^v` in the order
  have hgx₀ : Polynomial.aeval x₀ g = 0 := by
    rw [AdjoinRoot.aeval_eq, AdjoinRoot.mk_self]
  have hcq : c * Polynomial.aeval x₀ q = π' ^ v := by
    have h1 := congrArg (Polynomial.aeval x₀) hpq
    rw [map_add, map_mul, map_mul, hgx₀, zero_mul, zero_add, Polynomial.aeval_C,
      map_pow] at h1
    exact h1
  -- `f(x₀)` is an exact `π'·c²`-multiple
  have hfx₀ : Polynomial.aeval x₀ f = π' ^ (2 * v + 1) * Polynomial.aeval x₀ h₀ := by
    have h1 : Polynomial.aeval x₀ f = Polynomial.aeval x₀ (f - g) := by
      rw [map_sub, hgx₀, sub_zero]
    rw [h1, hh₀, map_mul, Polynomial.aeval_C, map_pow]
  set u : AdjoinRoot g := Polynomial.aeval x₀ q ^ 2 * Polynomial.aeval x₀ h₀ with hu
  have hfu : Polynomial.aeval x₀ f = π' * c ^ 2 * u := by
    have h2 : π' ^ (2 * v + 1) = π' * (c * Polynomial.aeval x₀ q) ^ 2 := by
      rw [hcq]; ring
    rw [hfx₀, hu, h2]; ring
  -- the Taylor tail and the master identity
  set F : Polynomial (AdjoinRoot g) := f.map (algebraMap O (AdjoinRoot g)) with hF
  have hFeval : ∀ t : AdjoinRoot g, F.eval t = Polynomial.aeval t f := by
    intro t
    rw [hF, Polynomial.eval_map, ← Polynomial.aeval_def]
  have hFderiv : F.derivative.eval x₀ = c := by
    rw [hF, Polynomial.derivative_map, Polynomial.eval_map, ← Polynomial.aeval_def]
  set T : Polynomial (AdjoinRoot g) := (Polynomial.taylor x₀ F).divX.divX with hT
  set H : Polynomial (AdjoinRoot g) :=
    Polynomial.X ^ 2 * (T.comp (Polynomial.C (π' * c) * Polynomial.X)) with hH
  have hkey : ∀ z : AdjoinRoot g,
      F.eval (x₀ + (π' * c) * z) = π' * c ^ 2 * (u + z + π' * H.eval z) := by
    intro z
    rw [eval_add_eq_taylor_quadratic F x₀ ((π' * c) * z), hFeval x₀, hfu, hFderiv,
      ← hT, hH]
    simp only [Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_comp,
      Polynomial.eval_C, Polynomial.eval_X]
    ring
  -- the fixed-point iteration, its contraction, and the limit
  set zs : ℕ → AdjoinRoot g :=
    fun m => Nat.rec (motive := fun _ => AdjoinRoot g) 0
      (fun _ ih => -(u + π' * H.eval ih)) m with hzs
  have hzsS : ∀ m, zs (m + 1) = -(u + π' * H.eval (zs m)) := fun m => rfl
  have hgain : ∀ m, π' ^ m ∣ zs (m + 1) - zs m := by
    intro m
    induction m with
    | zero => rw [pow_zero]; exact one_dvd _
    | succ m ih =>
      have h1 : zs (m + 2) - zs (m + 1)
          = -(π' * (H.eval (zs (m + 1)) - H.eval (zs m))) := by
        rw [hzsS (m + 1), hzsS m]; ring
      obtain ⟨d1, hd1⟩ := ih
      obtain ⟨d2, hd2⟩ := Polynomial.sub_dvd_eval_sub (zs (m + 1)) (zs m) H
      refine ⟨-(d1 * d2), ?_⟩
      rw [h1, hd2, hd1, pow_succ]
      ring
  have hcau : ∀ {m M : ℕ}, m ≤ M → π' ^ m ∣ zs M - zs m := by
    intro m M h
    induction M, h using Nat.le_induction with
    | base => rw [sub_self]; exact dvd_zero _
    | succ M hmM ih =>
      have h1 : zs (M + 1) - zs m = (zs (M + 1) - zs M) + (zs M - zs m) := by ring
      rw [h1]
      exact dvd_add ((pow_dvd_pow π' hmM).trans (hgain M)) ih
  obtain ⟨w, hw⟩ := exists_limit_of_cauchy hg hπ zs hcau
  -- the limit solves the fixed-point equation exactly
  have hGw : u + w + π' * H.eval w = 0 := by
    refine eq_zero_of_forall_pow_dvd hg hπ (fun m => ?_)
    rcases m with _ | m
    · rw [pow_zero]; exact one_dvd _
    · have h1 : u + w + π' * H.eval w
          = (w - zs (m + 1)) + π' * (H.eval w - H.eval (zs m)) := by
        rw [hzsS m]; ring
      rw [h1]
      refine dvd_add (hw (m + 1)) ?_
      obtain ⟨d2, hd2⟩ := Polynomial.sub_dvd_eval_sub w (zs m) H
      obtain ⟨d1, hd1⟩ := hw m
      refine ⟨d1 * d2, ?_⟩
      rw [hd2, hd1, pow_succ]
      ring
  -- the root
  refine ⟨x₀ + (π' * c) * w, ?_, ⟨c * w, by ring⟩⟩
  rw [← hFeval, hkey w, hGw, mul_zero]

end Newton

/-! ## §3 THE UNIT-DETERMINANT ISOMORPHISM `A_f ≃ₐ[O] A_g` -/

section Iso

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)]

/-- The evaluation `O`-algebra map `A_f →ₐ[O] A_g` sending `root f` to a root `ξ` of
`f` in `A_g` (mathlib's `AdjoinRoot.liftAlgHom` specialised along `Algebra.ofId`). -/
noncomputable def krasnerHom {f g : Polynomial O} (ξ : AdjoinRoot g)
    (hξ : Polynomial.aeval ξ f = 0) : AdjoinRoot f →ₐ[O] AdjoinRoot g :=
  AdjoinRoot.liftAlgHom f (Algebra.ofId O (AdjoinRoot g)) ξ
    (by rwa [Polynomial.aeval_def] at hξ)

@[simp] theorem krasnerHom_root {f g : Polynomial O} (ξ : AdjoinRoot g)
    (hξ : Polynomial.aeval ξ f = 0) :
    krasnerHom ξ hξ (AdjoinRoot.root f) = ξ :=
  AdjoinRoot.liftAlgHom_root _ _ _ _

/-- ★★ **THE ISO**: a root `ξ` of `f` in `AdjoinRoot g` with `ξ ≡ root g mod π` makes
the evaluation map `krasnerHom ξ` bijective — its matrix in the power bases is
`≡ 1 mod 𝔪`, hence has unit determinant. -/
theorem krasnerHom_bijective {π : O} (hπ : Irreducible π)
    {f g : Polynomial O} (hf : f.Monic) (hg : g.Monic) (hdeg : f.natDegree = g.natDegree)
    {ξ : AdjoinRoot g} (hξ : Polynomial.aeval ξ f = 0)
    (hclose : (algebraMap O (AdjoinRoot g) π) ∣ ξ - AdjoinRoot.root g) :
    Function.Bijective (krasnerHom ξ hξ) := by
  classical
  set Φ := krasnerHom ξ hξ with hΦ
  set pbf := AdjoinRoot.powerBasis' hf with hpbf
  set pbg := AdjoinRoot.powerBasis' hg with hpbg
  have hdim : pbf.dim = pbg.dim := by
    rw [hpbf, hpbg, AdjoinRoot.powerBasis'_dim, AdjoinRoot.powerBasis'_dim, hdeg]
  set bf := pbf.basis.reindex (finCongr hdim) with hbf
  set M := LinearMap.toMatrix bf pbg.basis Φ.toLinearMap with hM
  -- the matrix is ≡ 1 mod 𝔪
  have hentry : ∀ i j,
      M i j - (1 : Matrix (Fin pbg.dim) (Fin pbg.dim) O) i j ∈ maximalIdeal O := by
    intro i j
    have hMij : M i j = pbg.basis.repr (Φ (bf j)) i := by
      rw [hM, LinearMap.toMatrix_apply, AlgHom.toLinearMap_apply]
    have hbfj : bf j = AdjoinRoot.root f ^ (j : ℕ) := by
      rw [hbf, Module.Basis.reindex_apply, PowerBasis.basis_eq_pow]
      rfl
    have hΦbfj : Φ (bf j) = ξ ^ (j : ℕ) := by
      rw [hbfj, map_pow, hΦ, krasnerHom_root]
    have h1j : (1 : Matrix (Fin pbg.dim) (Fin pbg.dim) O) i j
        = pbg.basis.repr (AdjoinRoot.root g ^ (j : ℕ)) i := by
      have hgen : AdjoinRoot.root g ^ (j : ℕ) = pbg.basis j := by
        rw [PowerBasis.basis_eq_pow]
        rfl
      rw [hgen, Module.Basis.repr_self]
      simp [Matrix.one_apply, Finsupp.single_apply, eq_comm]
    have hπdvd : (algebraMap O (AdjoinRoot g) π)
        ∣ ξ ^ (j : ℕ) - AdjoinRoot.root g ^ (j : ℕ) := by
      refine dvd_trans hclose ?_
      have h2 := Polynomial.sub_dvd_eval_sub ξ (AdjoinRoot.root g)
        (Polynomial.X ^ (j : ℕ) : Polynomial (AdjoinRoot g))
      simpa using h2
    have hcoord : π ∣ pbg.basis.repr (ξ ^ (j : ℕ) - AdjoinRoot.root g ^ (j : ℕ)) i := by
      have h2 := pow_dvd_repr_of_pow_dvd hg (π := π) (m := 1)
        (by simpa using hπdvd) i
      simpa using h2
    rw [hMij, hΦbfj, h1j, ← Finsupp.sub_apply, ← map_sub]
    rw [hπ.maximalIdeal_eq]
    exact Ideal.mem_span_singleton.mpr hcoord
  -- the determinant is a unit
  have hdet : IsUnit M.det := by
    have hmap : M.map (Ideal.Quotient.mk (maximalIdeal O)) = 1 := by
      ext i j
      rw [Matrix.map_apply,
        (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mpr (hentry i j)]
      simp [Matrix.one_apply, apply_ite (Ideal.Quotient.mk (maximalIdeal O))]
    have h2 : Ideal.Quotient.mk (maximalIdeal O) M.det = 1 := by
      rw [RingHom.map_det, RingHom.mapMatrix_apply, hmap, Matrix.det_one]
    by_contra hnu
    have h3 : M.det ∈ maximalIdeal O :=
      (IsLocalRing.mem_maximalIdeal _).mpr (mem_nonunits_iff.mpr hnu)
    rw [(Ideal.Quotient.eq_zero_iff_mem).mpr h3] at h2
    exact zero_ne_one h2
  -- bijectivity through the nonsingular inverse
  have hlin : Φ.toLinearMap = Matrix.toLin bf pbg.basis M :=
    (Matrix.toLin_toMatrix bf pbg.basis Φ.toLinearMap).symm
  have hMM : M * M⁻¹ = 1 := Matrix.mul_nonsing_inv M hdet
  have hMM' : M⁻¹ * M = 1 := Matrix.nonsing_inv_mul M hdet
  constructor
  · intro a b hab
    have h1 : Matrix.toLin bf pbg.basis M a = Matrix.toLin bf pbg.basis M b := by
      rw [← hlin, AlgHom.toLinearMap_apply, AlgHom.toLinearMap_apply]
      exact hab
    have hcomp : (Matrix.toLin pbg.basis bf M⁻¹).comp (Matrix.toLin bf pbg.basis M)
        = LinearMap.id := by
      rw [← Matrix.toLin_mul, hMM', Matrix.toLin_one]
    have h2 := congrArg (Matrix.toLin pbg.basis bf M⁻¹) h1
    rwa [← LinearMap.comp_apply, ← LinearMap.comp_apply, hcomp, LinearMap.id_apply,
      LinearMap.id_apply] at h2
  · intro y
    refine ⟨Matrix.toLin pbg.basis bf M⁻¹ y, ?_⟩
    have hcomp : (Matrix.toLin bf pbg.basis M).comp (Matrix.toLin pbg.basis bf M⁻¹)
        = LinearMap.id := by
      rw [← Matrix.toLin_mul, hMM, Matrix.toLin_one]
    calc Φ (Matrix.toLin pbg.basis bf M⁻¹ y)
        = (Matrix.toLin bf pbg.basis M) (Matrix.toLin pbg.basis bf M⁻¹ y) := by
          rw [← hlin, AlgHom.toLinearMap_apply]
      _ = y := by rw [← LinearMap.comp_apply, hcomp, LinearMap.id_apply]

end Iso

/-! ## §4 TRANSPORT: domains, norms, `normValues`, `efPair`, `typeOf` -/

section Transport

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)]

/-- `Algebra.norm` is invariant under an `O`-algebra isomorphism (conjugation of the
multiplication operator preserves the determinant). -/
theorem norm_algEquiv {A B : Type*} [CommRing A] [CommRing B] [Algebra O A] [Algebra O B]
    (e : A ≃ₐ[O] B) (x : A) : Algebra.norm O (e x) = Algebra.norm O x :=
  Algebra.norm_eq_of_algEquiv e x

/-- The norm-valuation sets of `f` and `g` coincide along an isomorphism of their
orders. -/
theorem normValues_eq_of_algEquiv {f g : Polynomial O}
    (e : AdjoinRoot f ≃ₐ[O] AdjoinRoot g) : normValues f = normValues g := by
  ext k
  simp only [normValues, Set.mem_setOf_eq]
  constructor
  · rintro ⟨hk, x, hx0, hval⟩
    refine ⟨hk, e x, ?_, ?_⟩
    · intro h0
      exact hx0 (by simpa using congrArg e.symm h0)
    · rw [norm_algEquiv e x]
      exact hval
  · rintro ⟨hk, y, hy0, hval⟩
    refine ⟨hk, e.symm y, ?_, ?_⟩
    · intro h0
      exact hy0 (by simpa using congrArg e h0)
    · have h1 := norm_algEquiv e (e.symm y)
      rw [e.apply_symm_apply] at h1
      rw [← h1]
      exact hval

/-- `efPair` transport: same degree + same norm values ⟹ same `(e, f)` pair. -/
theorem efPair_eq_of_normValues {f g : Polynomial O} (hdeg : f.natDegree = g.natDegree)
    (hnv : normValues f = normValues g) : efPair f = efPair g := by
  have h1 : inertiaDegOf f = inertiaDegOf g := by
    unfold inertiaDegOf normDivisors
    rw [hnv]
  rw [efPair, efPair, ramIndexOf, ramIndexOf, h1, hdeg]

/-- `AdjoinRoot` of an irreducible over the UFD `O[X]` is a domain. -/
theorem isDomain_adjoinRoot_of_irreducible {f : Polynomial O} (hirr : Irreducible f) :
    IsDomain (AdjoinRoot f) := by
  have hprime : Prime f := UniqueFactorizationMonoid.irreducible_iff_prime.mp hirr
  have hsp : (Ideal.span {f} : Ideal (Polynomial O)).IsPrime :=
    (Ideal.span_singleton_prime hprime.ne_zero).mpr hprime
  exact Ideal.Quotient.isDomain (Ideal.span {f})

/-- Conversely, a monic `g` of positive degree with `AdjoinRoot g` a domain is
irreducible (a nontrivial monic factorization gives zero divisors). -/
theorem irreducible_of_isDomain_adjoinRoot {g : Polynomial O} (hg : g.Monic)
    (hd : g.natDegree ≠ 0) (hdom : IsDomain (AdjoinRoot g)) : Irreducible g := by
  haveI := hdom
  rw [irreducible_iff]
  refine ⟨fun hu => hd (Polynomial.natDegree_eq_zero_of_isUnit hu), ?_⟩
  intro u w huw
  by_contra hcon
  obtain ⟨hu, hw⟩ := not_or.mp hcon
  have hg0 : g ≠ 0 := hg.ne_zero
  have hu0 : u ≠ 0 := fun h0 => hg0 (by rw [huw, h0, zero_mul])
  have hw0 : w ≠ 0 := fun h0 => hg0 (by rw [huw, h0, mul_zero])
  have hulead : IsUnit u.leadingCoeff :=
    isUnit_leadingCoeff_of_dvd_monic hg ⟨w, huw⟩
  have hwlead : IsUnit w.leadingCoeff :=
    isUnit_leadingCoeff_of_dvd_monic hg ⟨u, by rw [huw, mul_comm]⟩
  have hund : u.natDegree ≠ 0 := fun h0 => hu (isUnit_of_natDegree_zero h0 hulead)
  have hwnd : w.natDegree ≠ 0 := fun h0 => hw (isUnit_of_natDegree_zero h0 hwlead)
  have hsum : u.natDegree + w.natDegree = g.natDegree := by
    rw [huw, Polynomial.natDegree_mul hu0 hw0]
  have hmku : AdjoinRoot.mk g u ≠ 0 := by
    intro h0
    rw [AdjoinRoot.mk_eq_zero] at h0
    have h1 := Polynomial.natDegree_le_of_dvd h0 hu0
    omega
  have hmkw : AdjoinRoot.mk g w ≠ 0 := by
    intro h0
    rw [AdjoinRoot.mk_eq_zero] at h0
    have h1 := Polynomial.natDegree_le_of_dvd h0 hw0
    omega
  have hprod : AdjoinRoot.mk g u * AdjoinRoot.mk g w = 0 := by
    rw [← map_mul, ← huw, AdjoinRoot.mk_self]
  rcases mul_eq_zero.mp hprod with h | h
  · exact hmku h
  · exact hmkw h

/-- The type of a monic irreducible is the singleton of its `(e, f)` pair. -/
theorem typeOf_of_irreducible {g : Polynomial O} (hg : g.Monic) (hirr : Irreducible g) :
    typeOf g = ⟨{efPair g}⟩ := by
  have hF : IsMonicFactorization g {g} := by
    refine ⟨?_, by simp⟩
    intro h hh
    rw [Multiset.mem_singleton.mp hh]
    exact ⟨hg, hirr⟩
  apply FactorizationType.ext
  rw [typeOf_data, monicFactors_eq hF]
  simp

end Transport

/-! ## §5 THE THEOREMS — `KrasnerIrredAt` at every degree, and THE FIRES -/

section Main

/-- ★★★ **KRASNER, CLOSED** — `KrasnerIrredAt n` holds at EVERY `n`: an irreducible
separable monic over a complete DVR is decided at level `2·v(Res(f,f')) + 1`.  The
mechanism is the unit-determinant isomorphism `A_f ≃ₐ[O] A_g` for every lift `g` of the
class, built by Newton iteration inside the order `A_g`. -/
theorem krasnerIrredAt (n : ℕ) : KrasnerIrredAt n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact IFCG50.krasnerIrredAt_zero
  intro O _ _ _ _ _ a hirr hres
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible O
  -- the exact discriminant depth `v₀`
  obtain ⟨v₀, u₀, hRf⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hres hπ
  refine ⟨2 * v₀ + 1, typeOf (monicPoly a), ?_⟩
  intro b hb
  set f := monicPoly a with hf
  set g := monicPoly b with hg
  have hfm : f.Monic := monicPoly_monic a
  have hgm : g.Monic := monicPoly_monic b
  have hfd : f.natDegree = n := monicPoly_natDegree a
  have hgd : g.natDegree = n := monicPoly_natDegree b
  -- the coefficientwise congruence `f ≡ g mod π^{2v₀+1}`
  have hcoeffs : ∀ i : Fin n, π ^ (2 * v₀ + 1) ∣ (a i - b i) := by
    intro i
    have h1 : Ideal.Quotient.mk ((maximalIdeal O) ^ (2 * v₀ + 1)) (b i)
        = Ideal.Quotient.mk ((maximalIdeal O) ^ (2 * v₀ + 1)) (a i) := congrFun hb i
    have h2 : b i - a i ∈ (maximalIdeal O) ^ (2 * v₀ + 1) :=
      (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mp h1
    have h3 : a i - b i ∈ (maximalIdeal O) ^ (2 * v₀ + 1) := by
      have h4 := neg_mem h2
      rwa [neg_sub] at h4
    exact (IFCG50.mem_maximalIdeal_pow_iff_dvd hπ _ _).mp h3
  have hcong : Polynomial.C (π ^ (2 * v₀ + 1)) ∣ f - g := by
    refine (Polynomial.C_dvd_iff_dvd_coeff _ _).mpr fun i => ?_
    rcases Nat.lt_or_ge i n with hi | hi
    · rw [Polynomial.coeff_sub, hf, hg, monicPoly_coeff_lt a hi, monicPoly_coeff_lt b hi]
      exact hcoeffs ⟨i, hi⟩
    · rcases eq_or_lt_of_le hi with heq | hlt
      · rw [Polynomial.coeff_sub, ← heq]
        have h1 : f.coeff n = 1 := by rw [← hfd]; exact hfm.coeff_natDegree
        have h2 : g.coeff n = 1 := by rw [← hgd]; exact hgm.coeff_natDegree
        rw [h1, h2, sub_self]
        exact dvd_zero _
      · rw [Polynomial.coeff_sub,
          Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [hfd]; exact hlt),
          Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [hgd]; exact hlt), sub_self]
        exact dvd_zero _
  -- `Res(g, f')` has the same exact depth `v₀` (resultants are coefficient polynomials)
  have hmapeq : g.map (Ideal.Quotient.mk ((maximalIdeal O) ^ (2 * v₀ + 1)))
      = f.map (Ideal.Quotient.mk ((maximalIdeal O) ^ (2 * v₀ + 1))) := by
    ext i
    rw [Polynomial.coeff_map, Polynomial.coeff_map]
    refine (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mpr ?_
    rw [IFCG50.mem_maximalIdeal_pow_iff_dvd hπ]
    have h1 := (Polynomial.C_dvd_iff_dvd_coeff _ _).mp hcong i
    rw [Polynomial.coeff_sub] at h1
    exact dvd_sub_comm.mp h1
  have hRcong : π ^ (2 * v₀ + 1)
      ∣ Polynomial.resultant g (Polynomial.derivative f) n (n - 1)
        - Polynomial.resultant f (Polynomial.derivative f) n (n - 1) := by
    have h1 : Ideal.Quotient.mk ((maximalIdeal O) ^ (2 * v₀ + 1))
        (Polynomial.resultant g (Polynomial.derivative f) n (n - 1))
        = Ideal.Quotient.mk ((maximalIdeal O) ^ (2 * v₀ + 1))
          (Polynomial.resultant f (Polynomial.derivative f) n (n - 1)) := by
      rw [← Polynomial.resultant_map_map, ← Polynomial.resultant_map_map, hmapeq]
    exact (IFCG50.mem_maximalIdeal_pow_iff_dvd hπ _ _).mp
      ((Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mp h1)
  have hRg : ¬ π ^ (v₀ + 1)
      ∣ Polynomial.resultant g (Polynomial.derivative f) n (n - 1) := by
    intro hdvd
    have h1 : π ^ (v₀ + 1)
        ∣ Polynomial.resultant f (Polynomial.derivative f) n (n - 1) := by
      have h2 : Polynomial.resultant f (Polynomial.derivative f) n (n - 1)
          = Polynomial.resultant g (Polynomial.derivative f) n (n - 1)
            - (Polynomial.resultant g (Polynomial.derivative f) n (n - 1)
              - Polynomial.resultant f (Polynomial.derivative f) n (n - 1)) := by ring
      rw [h2]
      exact dvd_sub hdvd ((pow_dvd_pow π (by omega : v₀ + 1 ≤ 2 * v₀ + 1)).trans hRcong)
    rw [hRf] at h1
    have h3 := (IFCG50.pow_dvd_unit_mul_pow_iff hπ u₀ (v₀ + 1) v₀).mp h1
    omega
  -- Bezout at the exact depth, and the Newton root
  have hbez := Uniformity.Density.IFCG41.exists_bezout_of_not_dvd_resultant hπ
    (le_of_eq hgd) ((Polynomial.natDegree_derivative_le f).trans (by rw [hfd]))
    (Or.inl (by omega : n ≠ 0)) hRg
  obtain ⟨ξ, hξ, hclose⟩ := exists_aeval_eq_zero_of_close hπ hgm hcong hbez
  -- the isomorphism and the transports
  have hbij := krasnerHom_bijective hπ hfm hgm (by rw [hfd, hgd]) hξ hclose
  have hdomf : IsDomain (AdjoinRoot f) := isDomain_adjoinRoot_of_irreducible hirr
  have hdomg : IsDomain (AdjoinRoot g) := by
    haveI := hdomf
    exact Function.Injective.isDomain
      ((AlgEquiv.ofBijective (krasnerHom ξ hξ) hbij).symm : AdjoinRoot g →+* AdjoinRoot f)
      (AlgEquiv.ofBijective (krasnerHom ξ hξ) hbij).symm.injective
  have hgirr : Irreducible g :=
    irreducible_of_isDomain_adjoinRoot hgm (by rw [hgd]; omega) hdomg
  have hnv : normValues f = normValues g :=
    normValues_eq_of_algEquiv (AlgEquiv.ofBijective (krasnerHom ξ hξ) hbij)
  have hef : efPair f = efPair g := efPair_eq_of_normValues (by rw [hfd, hgd]) hnv
  rw [typeOf_of_irreducible hgm hgirr, typeOf_of_irreducible hfm hirr, hef]

/-- ★★★ **THE CHARGED PROP** — `KrasnerDeepAt n` at every `n` (a hypothesis-weakening
of `krasnerIrredAt`; the deep-wild restriction is never needed). -/
theorem krasnerDeepAt (n : ℕ) : KrasnerDeepAt n :=
  fun O _ _ _ _ _ a hirr _ hres => krasnerIrredAt n O a hirr hres

/-- ★★★ `KrasnerAt n` at every `n`, through IFCG50's UFD recombination. -/
theorem krasnerAt (n : ℕ) : KrasnerAt n :=
  krasnerAt_of_krasnerIrred krasnerIrredAt

/-- ★★★ UDR's deep-tail drain at every `n`, now unconditional. -/
theorem deepTailDrainAt (n : ℕ) : IFCG46.DeepTailDrainAt n :=
  deepTailDrainAt_of_krasner (krasnerAt n)

/-- ★★★ **THE CAPSTONE'S `a2` FIELD, UNCONDITIONAL** — `DrainageAt n` at EVERY `n`,
the exact consumer shape of `CapstoneHypotheses.a2` (I10_I15_I18).  The deep-wild
drainage fence is CLOSED: no Krasner-genre hypothesis remains anywhere in the `a2`
supply chain. -/
theorem drainageAt_all : ∀ n, DrainageAt n :=
  drainageAt_all_of_krasnerIrred krasnerIrredAt

end Main

end Uniformity.Density.IFCG52

/-! ## AXCHECK FOOTER — expect Lean core `{propext, Classical.choice, Quot.sound}` only -/

#print axioms Uniformity.Density.IFCG52.exists_limit_of_cauchy
#print axioms Uniformity.Density.IFCG52.eval_add_eq_taylor_quadratic
#print axioms Uniformity.Density.IFCG52.exists_aeval_eq_zero_of_close
#print axioms Uniformity.Density.IFCG52.krasnerHom_bijective
#print axioms Uniformity.Density.IFCG52.norm_algEquiv
#print axioms Uniformity.Density.IFCG52.normValues_eq_of_algEquiv
#print axioms Uniformity.Density.IFCG52.isDomain_adjoinRoot_of_irreducible
#print axioms Uniformity.Density.IFCG52.irreducible_of_isDomain_adjoinRoot
#print axioms Uniformity.Density.IFCG52.typeOf_of_irreducible
#print axioms Uniformity.Density.IFCG52.krasnerIrredAt
#print axioms Uniformity.Density.IFCG52.krasnerDeepAt
#print axioms Uniformity.Density.IFCG52.krasnerAt
#print axioms Uniformity.Density.IFCG52.deepTailDrainAt
#print axioms Uniformity.Density.IFCG52.drainageAt_all
