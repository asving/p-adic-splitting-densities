/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib.LinearAlgebra.FreeModule.Finite.Quotient
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.Norm.Defs
import Mathlib.LinearAlgebra.Determinant
import Mathlib.Algebra.Algebra.Bilinear

/-!
# Uniformity.ChapB.B50 — the determinant–length identity

**Chapter B, NODE B.50** (`blueprint/CHAP-B_leaf_layer.md` §7). *The determinant–length identity.*
Let `A` be an `O`-algebra, free and module-finite over the discrete valuation ring `O`, and let
`z ∈ A` have nonzero norm. Then

`addVal O (Algebra.norm O z) = the O-length of A ⧸ zA`,

stated — per the blueprint, avoiding any dependence on a `Module.length` API — in **elementary
divisor form**: there are exponents `e : Fin (finrank O A) → ℕ` with an `O`-linear isomorphism
`A ⧸ zA ≃ₗ ⨁ i, O ⧸ (π ^ e i)` and `addVal O (norm z) = Σ i, e i`.

The two clauses share the single Smith normal form of `zA ⊆ A`, so they are proved together: the
`e i` are the `π`-adic valuations of the Smith coefficients `a i`, the direct sum is the Smith
decomposition of the quotient, and the valuation identity says the determinant of multiplication
by `z` is `∏ a i` up to a unit.

DEPENDS: mathlib only. ENVIRONMENT: ENV-A′ (ENV-A plus the explicit `hπ : Irreducible π`).

**MATHLIB-API RISK RESOLVED.** The blueprint flagged this node as *"the chapter's third hard core
and its only mathlib-API risk of the first kind"*, warning that if `Submodule.smithNormalForm`
were available only as an `∃ (n : ℕ) (bM : Basis (Fin n) …)` package rather than a decomposition,
step 3 would become a 60-line repackaging (~200-line node), and that the sanctioned **fallback**
was to restate B.50 for `A` a DVR only — which would lose B.52 and make the chapter's
`ℓ ≥ 2, d = 1` row conditional. **The fallback was NOT needed and is NOT applied.** At our pin
(mathlib `v4.31.0`) the full-rank Smith package exists in exactly the shape the node wants:
`Submodule.smithNormalFormTopBasis` / `smithNormalFormBotBasis` / `smithNormalFormCoeffs` with
`smithNormalFormBotBasis_def` and `smithNormalFormCoeffs_ne_zero`
(`Mathlib/LinearAlgebra/FreeModule/PID.lean`), together with a ready-made quotient decomposition
`Submodule.quotientEquivPiSpan` (`Mathlib/LinearAlgebra/FreeModule/Finite/Quotient.lean`). The
node lands at full strength for arbitrary free module-finite `A`, so B.52 keeps its lower half.

**PROOF.**
1. `Algebra.norm O z = LinearMap.det (LinearMap.mulLeft O z)` — definitionally (`Algebra.norm_apply`
   is `rfl`, and `Algebra.lmul` is `LinearMap.mulLeft`). Write `g := LinearMap.mulLeft O z`.
2. `g` is injective: over a domain, a nonzero determinant forces trivial kernel
   (`LinearMap.det_eq_zero_iff_ker_ne_bot`). Its range is exactly `zA` viewed as an `O`-submodule
   (`Ideal.mem_span_singleton`), so `zA ≅ A` and `finrank O (zA) = finrank O A`: `zA` has **full
   rank**, which is the hypothesis the mathlib Smith package needs.
3. Smith normal form of `zA ⊆ A` gives bases `b'` of `A`, `ab` of `zA` and coefficients `a i ≠ 0`
   with `ab i = a i • b' i`. Writing `a i = u i * π ^ e i`
   (`IsDiscreteValuationRing.eq_unit_mul_pow_irreducible`) gives `span {a i} = span {π ^ e i}`
   (`Ideal.span_singleton_eq_span_singleton`, associated generators), so
   `Submodule.quotientEquivPiSpan` followed by `LinearEquiv.piCongrRight` and
   `DirectSum.linearEquivFunOnFintype` produces the direct sum in the signed shape.
4. The diagonal endomorphism `d` sending `b' i ↦ a i • b' i` has `det d = ∏ a i`
   (`LinearMap.toMatrix` is `Matrix.diagonal a`; `Matrix.det_diagonal`). Both `d` and `g` are
   injective with the same range `zA`, so `d = g ∘ₗ w` for a linear **automorphism** `w` of `A`;
   `det w` is a unit (`LinearEquiv.isUnit_det'`), hence
   `addVal (∏ a i) = addVal (det g) + 0 = addVal (norm z)`. Finally
   `addVal (∏ a i) = Σ addVal (a i) = Σ e i` by induction over `Finset.univ`, using
   `IsDiscreteValuationRing.addVal_def` on each `a i = u i * π ^ e i`.

**NOTE ON `hr`.** The signed hypothesis `0 < Module.finrank O A` is not used: the identity is
already true at rank `0` (both sides are `0`). It is retained because the signature is frozen; the
`unusedVariables` linter is silenced locally rather than the binder renamed.

**SPLIT NOT TAKEN.** The blueprint mandated a 3-way file split (`B50a`/`B50b`/`B50c`) against an
estimated 140–200 lines. With the pinned mathlib API the whole node is one ~90-line proof whose
three steps share the same `set` block (`b'`, `ab`, `a`, `e`, `u`); splitting it would mean
exporting the Smith data as three separate contracts that the blueprint never signed, so it is
kept as one file with the steps marked in place.

**SOURCE.** classical (the corpus imports it inside `EFF.HE6.06`'s "resultant symmetry … Galois
invariance of `v`" package and never isolates it); `EFF.HE3.20` (`LEMMA HE3-1`, the resultant
identity `Σ_ρ dv(Φ″(ρ)) = D′·dv(B₀)`, is the corpus's root-indexed form of this identity — this
node is its root-free form).

## Status

Sorry-free, axiom-free (Lean core only).
-/

set_option linter.style.longLine false

namespace Uniformity.Density.Leaf

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {π : O}

set_option linter.unusedVariables false in
open DirectSum in
/-- **B.50.** *The determinant–length identity, in elementary-divisor form.* For `z` of nonzero
norm in a free module-finite `O`-algebra `A`, there are exponents `e i` with
`A ⧸ zA ≃ₗ[O] ⨁ i, O ⧸ (π ^ e i)` and `addVal O (Algebra.norm O z) = Σ i, e i`. -/
theorem exists_smith_of_norm (hπ : Irreducible π) {A : Type*} [CommRing A] [Algebra O A]
    [Module.Free O A] [Module.Finite O A] (hr : 0 < Module.finrank O A)
    {z : A} (hz : Algebra.norm O z ≠ 0) :
    ∃ e : Fin (Module.finrank O A) → ℕ,
      Nonempty ((A ⧸ (Ideal.span {z}).restrictScalars O) ≃ₗ[O]
        (⨁ i, O ⧸ (Ideal.span {π ^ e i}))) ∧
      IsDiscreteValuationRing.addVal O (Algebra.norm O z) = ((∑ i, e i : ℕ) : ℕ∞) := by
  classical
  set g : A →ₗ[O] A := LinearMap.mulLeft O z with hgdef
  have hdet : LinearMap.det g = Algebra.norm O z := rfl
  have hginj : Function.Injective g := by
    rw [← LinearMap.ker_eq_bot]
    by_contra hk
    exact hz (hdet ▸ LinearMap.det_eq_zero_iff_ker_ne_bot.mpr hk)
  set N : Submodule O A := (Ideal.span {z}).restrictScalars O with hNdef
  have hrange : LinearMap.range g = N := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      exact Ideal.mem_span_singleton.mpr ⟨y, rfl⟩
    · intro hx
      obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton.mp hx
      exact ⟨c, rfl⟩
  have hNfr : Module.finrank O N = Module.finrank O A :=
    ((LinearEquiv.ofInjective g hginj).trans
      (LinearEquiv.ofEq _ _ hrange)).finrank_eq.symm
  set b : Module.Basis (Fin (Module.finrank O A)) O A := Module.finBasis O A with hbdef
  set a : Fin (Module.finrank O A) → O := Submodule.smithNormalFormCoeffs b hNfr with hadef
  set b' : Module.Basis (Fin (Module.finrank O A)) O A :=
    Submodule.smithNormalFormTopBasis b hNfr with hb'def
  set ab : Module.Basis (Fin (Module.finrank O A)) O N :=
    Submodule.smithNormalFormBotBasis b hNfr with habdef
  have hsnf : ∀ i, ((ab i : A)) = a i • b' i := Submodule.smithNormalFormBotBasis_def b hNfr
  have hane : ∀ i, a i ≠ 0 := fun i => Submodule.smithNormalFormCoeffs_ne_zero b hNfr i
  choose e u hu using fun i => IsDiscreteValuationRing.eq_unit_mul_pow_irreducible (hane i) hπ
  refine ⟨e, ⟨?_⟩, ?_⟩
  · have hspan : ∀ i, Ideal.span ({a i} : Set O) = Ideal.span ({π ^ e i} : Set O) := by
      intro i
      refine Ideal.span_singleton_eq_span_singleton.mpr ⟨(u i)⁻¹, ?_⟩
      rw [hu i, mul_comm ((u i : O)) (π ^ e i), mul_assoc, Units.mul_inv, mul_one]
    exact ((Submodule.quotientEquivPiSpan N b hNfr).trans
      (LinearEquiv.piCongrRight fun i => Submodule.quotEquivOfEq _ _ (hspan i))).trans
      (DirectSum.linearEquivFunOnFintype O _ _).symm
  · -- the diagonal endomorphism `d` of `A`, `d (b' i) = a i • b' i`
    set d : A →ₗ[O] A := N.subtype ∘ₗ (b'.equiv ab (Equiv.refl _)).toLinearMap with hddef
    have hdapp : ∀ i, d (b' i) = a i • b' i := by
      intro i
      simp [hddef, Module.Basis.equiv_apply, hsnf i]
    have hdmat : LinearMap.toMatrix b' b' d = Matrix.diagonal a := by
      ext i j
      rw [LinearMap.toMatrix_apply, hdapp j]
      by_cases hij : i = j
      · subst hij; simp
      · simp [Matrix.diagonal_apply_ne _ hij, Ne.symm hij]
    have hdetd : LinearMap.det d = ∏ i, a i := by
      rw [← LinearMap.det_toMatrix b' d, hdmat, Matrix.det_diagonal]
    have hdinj : Function.Injective d := by
      intro x y hxy
      exact (b'.equiv ab (Equiv.refl _)).injective (Subtype.ext hxy)
    have hdrange : LinearMap.range d = LinearMap.range g := by
      rw [hrange, hddef, LinearMap.range_comp]
      simp
    -- `w`, the change of basis relating `d` to multiplication by `z`
    set w : A ≃ₗ[O] A :=
      (LinearEquiv.ofInjective d hdinj).trans
        ((LinearEquiv.ofEq _ _ hdrange).trans (LinearEquiv.ofInjective g hginj).symm) with hwdef
    have hgw : g ∘ₗ (w : A →ₗ[O] A) = d := by
      ext x
      show g (w x) = d x
      have h1 : ((LinearEquiv.ofInjective g hginj) (w x) : A) = g (w x) :=
        LinearEquiv.ofInjective_apply g (w x)
      have h2 : (LinearEquiv.ofInjective g hginj) (w x)
          = (LinearEquiv.ofEq _ _ hdrange) ((LinearEquiv.ofInjective d hdinj) x) := by
        rw [hwdef]; simp
      rw [← h1, h2]
      simp [LinearEquiv.ofInjective_apply]
    have hsplit : LinearMap.det d = LinearMap.det g * LinearMap.det (w : A →ₗ[O] A) := by
      rw [← hgw, LinearMap.det_comp]
    have hwu : IsUnit (LinearMap.det (w : A →ₗ[O] A)) := LinearEquiv.isUnit_det' w
    have key : IsDiscreteValuationRing.addVal O (∏ i, a i)
        = IsDiscreteValuationRing.addVal O (Algebra.norm O z) := by
      rw [← hdetd, hsplit, IsDiscreteValuationRing.addVal_mul, hdet,
        IsDiscreteValuationRing.addVal_eq_zero_iff.mpr hwu, add_zero]
    have hone : ∀ i, IsDiscreteValuationRing.addVal O (a i) = ((e i : ℕ) : ℕ∞) :=
      fun i => IsDiscreteValuationRing.addVal_def (a i) (u i) hπ (e i) (hu i)
    have H : ∀ s : Finset (Fin (Module.finrank O A)),
        IsDiscreteValuationRing.addVal O (∏ i ∈ s, a i) = ((∑ i ∈ s, e i : ℕ) : ℕ∞) := by
      intro s
      induction s using Finset.induction_on with
      | empty => simp
      | @insert i s hi ih =>
          rw [Finset.prod_insert hi, Finset.sum_insert hi, IsDiscreteValuationRing.addVal_mul,
            hone i, ih, Nat.cast_add]
    exact key.symm.trans (H Finset.univ)

end Uniformity.Density.Leaf

/-! ## Axiom footprint -/

section AxCheck
#print axioms Uniformity.Density.Leaf.exists_smith_of_norm
end AxCheck
