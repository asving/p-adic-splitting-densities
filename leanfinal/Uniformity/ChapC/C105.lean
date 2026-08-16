/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib

/-!
# Uniformity.ChapC.C105 — `w`-blindness, the invariance that hides the uncomputed unit

**Chapter C, NODE C.105** [lemma] (`blueprint/CHAP-C_tower_grammar.md` §10), **ENV-C4** — the
pure residue-tower arena: one field `K`, no local base `O`, nothing counted.

For a unit `w ∈ K^×` and `P ∈ K[y]` the **`w`-conjugate** is
`wconj w P = P^{(w)} := w^(deg P) · P(y/w)`, written in Lean as
`C (w ^ P.natDegree) * P.comp (C w⁻¹ * X)`.  `wconj_invariants` bundles the six reads that
every §9/§10 consumer of a `ψ^{(w)}`-form actually performs, and shows each is unchanged:

1. monicity, 2. degree, 3. the constant term (`w^(deg)·P(0)`, the one clause that *moves*, and
   moves by an explicitly named unit), 4. irreducibility, 5. separability, 6. the
   **irreducible-factor degree pattern**, as the multiset `Multiset.map natDegree (factors ·)`.

Consequently every consumer that reads σ, values, degrees, irreducibility or residue classes
through a `ψ^{(w)}`-form is `w`-independent: this is the corpus's "w-blind" claim, as ONE lemma,
consumed wherever C.90/C.101 say "w-blind".

## The `w`-DISCLOSURE (blueprint STATEMENT, carried here verbatim as documentation)

`w` is *measured* `≠ 1` at 6 primes / 4 frames and is `u₃`-dependent (PE6); **its closed form is
OPEN** — no node of this development computes it.  This lemma is precisely why none needs to.
The measurement rows are the node's retained TEETH: they guard the DISCLOSURE, not the lemma.
The honest scope note of `EFF.GENTOW2.82`/`.83` applies to the disclosure and is repeated here:
the measurements "do not decide `w_i` at unmeasured frames or levels `i > 2`".

## The proof, in one line each

The substitution `y ↦ w⁻¹y` is a `K`-algebra automorphism `wsub w hw` of `K[y]` (private, below),
and `wconj w P = C (w ^ deg P) * wsub w hw P` is that automorphism followed by scaling by a unit.
Clauses 1–3 come from the identification `wconj w P = P.scaleRoots w` (an exact coefficient
identity once `w ≠ 0`), which puts mathlib's `monic_scaleRoots_iff` / `natDegree_scaleRoots` /
`coeff_scaleRoots` in charge.  Clause 4 is `MulEquiv.irreducible_iff` after discarding the unit;
clause 5 is the chain rule `derivative (P.comp (C w⁻¹ * X)) = C w⁻¹ * (derivative P).comp …`
plus coprimality's invariance under composing with the substitution; clause 6 is
`UniqueFactorizationMonoid.factors_unique` against `Multiset.map (wsub w hw) (factors P)`,
transported to degrees because associated polynomials over a domain have equal degree.

**DEPENDS.** Nothing from this repo — mathlib's `Polynomial.scaleRoots` family only.

## Status

Sorry-free, axiom-free (Lean core only).
-/

namespace Uniformity.Density.Tower

open Polynomial

/-- The `w`-conjugate `P^{(w)} := w^(deg P)·P(y/w)`. -/
noncomputable def wconj {K : Type*} [Field K] (w : K) (P : Polynomial K) : Polynomial K :=
  Polynomial.C (w ^ P.natDegree) * P.comp (Polynomial.C w⁻¹ * Polynomial.X)

section Aux

variable {K : Type*} [Field K]

/-- Private. The substitution `y ↦ w⁻¹y`, as a `K`-algebra automorphism of `K[y]`. -/
private noncomputable def wsub (w : K) (hw : w ≠ 0) : Polynomial K ≃ₐ[K] Polynomial K :=
  AlgEquiv.ofAlgHom (aeval (C w⁻¹ * X)) (aeval (C w * X))
    (by
      apply algHom_ext
      simp [← C_mul, mul_inv_cancel₀ hw, ← mul_assoc])
    (by
      apply algHom_ext
      simp [← C_mul, inv_mul_cancel₀ hw, ← mul_assoc])

private lemma wsub_apply (w : K) (hw : w ≠ 0) (P : Polynomial K) :
    wsub w hw P = P.comp (C w⁻¹ * X) := by
  simp [wsub, comp_eq_aeval]

/-- Private. Composing the substitution with its inverse is the identity. -/
private lemma comp_scale_scale (w : K) (hw : w ≠ 0) (P : Polynomial K) :
    (P.comp (C w⁻¹ * X)).comp (C w * X) = P := by
  rw [comp_assoc]
  have : (C w⁻¹ * X).comp (C w * X) = (X : Polynomial K) := by
    rw [mul_comp, C_comp, X_comp, ← mul_assoc, ← C_mul, inv_mul_cancel₀ hw, C_1, one_mul]
  rw [this, comp_X]

/-- Private. Coprimality survives composing both entries with a fixed polynomial. -/
private lemma isCoprime_comp (q : Polynomial K) {a b : Polynomial K} (h : IsCoprime a b) :
    IsCoprime (a.comp q) (b.comp q) := by
  obtain ⟨u, v, huv⟩ := h
  exact ⟨u.comp q, v.comp q, by rw [← mul_comp, ← mul_comp, ← add_comp, huv, one_comp]⟩

/-- Private. Scaling the right entry by a nonzero constant does not change coprimality. -/
private lemma isCoprime_C_mul_right {a : K} (ha : a ≠ 0) (p q : Polynomial K) :
    IsCoprime p (C a * q) ↔ IsCoprime p q := by
  have h1 : (C a⁻¹ : Polynomial K) * C a = 1 := by
    rw [← C_mul, inv_mul_cancel₀ ha, C_1]
  constructor
  · rintro ⟨u, v, huv⟩
    exact ⟨u, v * C a, by rw [← huv]; ring⟩
  · rintro ⟨u, v, huv⟩
    refine ⟨u, v * C a⁻¹, ?_⟩
    calc u * p + v * C a⁻¹ * (C a * q) = u * p + v * (C a⁻¹ * C a) * q := by ring
      _ = u * p + v * q := by rw [h1, mul_one]
      _ = 1 := huv

/-- Private. Scaling by a nonzero constant does not change separability. -/
private lemma separable_C_mul_iff {a : K} (ha : a ≠ 0) (p : Polynomial K) :
    (C a * p).Separable ↔ p.Separable := by
  refine ⟨fun h => ?_, fun h => h.unit_mul (isUnit_C.mpr (isUnit_iff_ne_zero.mpr ha))⟩
  have h2 := h.unit_mul (isUnit_C.mpr (isUnit_iff_ne_zero.mpr (inv_ne_zero ha)))
  rwa [← mul_assoc, ← C_mul, inv_mul_cancel₀ ha, C_1, one_mul] at h2

/-- Private. The substitution preserves separability. -/
private lemma separable_comp_scale (w : K) (hw : w ≠ 0) (P : Polynomial K) :
    (P.comp (C w⁻¹ * X)).Separable ↔ P.Separable := by
  have hderiv : derivative (P.comp (C w⁻¹ * X))
      = C w⁻¹ * (derivative P).comp (C w⁻¹ * X) := by
    rw [derivative_comp]
    simp
  rw [Polynomial.Separable, hderiv, isCoprime_C_mul_right (inv_ne_zero hw)]
  refine ⟨fun h => ?_, fun h => isCoprime_comp _ h⟩
  have h2 := isCoprime_comp (C w * X) h
  rwa [comp_scale_scale w hw, comp_scale_scale w hw] at h2

/-- Private. The `w`-conjugate IS mathlib's `scaleRoots` at `w`, coefficient by coefficient. -/
private lemma wconj_eq_scaleRoots (w : K) (hw : w ≠ 0) (P : Polynomial K) :
    wconj w P = P.scaleRoots w := by
  ext i
  rw [wconj, coeff_C_mul, comp_C_mul_X_coeff, coeff_scaleRoots]
  rcases le_or_gt i P.natDegree with h | h
  · have hwi : (w ^ i) ≠ 0 := pow_ne_zero _ hw
    have key : w ^ P.natDegree * (w⁻¹ : K) ^ i = w ^ (P.natDegree - i) := by
      rw [inv_pow, ← div_eq_mul_inv, div_eq_iff hwi, ← pow_add, Nat.sub_add_cancel h]
    rw [mul_left_comm, key]
  · simp [coeff_eq_zero_of_natDegree_lt h]

/-- Private. The unit-times-automorphism factorization of the `w`-conjugate. -/
private lemma wconj_eq_unit_mul (w : K) (hw : w ≠ 0) (P : Polynomial K) :
    wconj w P = C (w ^ P.natDegree) * wsub w hw P := by
  rw [wsub_apply, wconj]

end Aux

/-- **NODE C.105 — `w`-blindness.** For a unit `w` and monic `P`, the `w`-conjugate
`P^{(w)} = w^(deg P)·P(y/w)` is monic of the same degree, has constant term
`w^(deg P)·P(0)`, is irreducible iff `P` is, is separable iff `P` is, and has the same
multiset of irreducible-factor degrees.  Hence every consumer that reads only these data
through a `ψ^{(w)}`-form is `w`-independent — the uncomputed `w` is invisible. -/
theorem wconj_invariants {K : Type*} [Field K] (w : K) (hw : w ≠ 0) (P : Polynomial K)
    (hP : P.Monic) :
    (wconj w P).Monic ∧ (wconj w P).natDegree = P.natDegree ∧
    (wconj w P).coeff 0 = w ^ P.natDegree * P.coeff 0 ∧
    (Irreducible (wconj w P) ↔ Irreducible P) ∧
    ((wconj w P).Separable ↔ P.Separable) ∧
    Multiset.map Polynomial.natDegree (UniqueFactorizationMonoid.factors (wconj w P))
      = Multiset.map Polynomial.natDegree (UniqueFactorizationMonoid.factors P) := by
  classical
  set E := wsub w hw with hEdef
  have hsr : wconj w P = P.scaleRoots w := wconj_eq_scaleRoots w hw P
  have hEq : wconj w P = C (w ^ P.natDegree) * E P := wconj_eq_unit_mul w hw P
  have hunit : IsUnit (C (w ^ P.natDegree) : Polynomial K) :=
    isUnit_C.mpr (isUnit_iff_ne_zero.mpr (pow_ne_zero _ hw))
  have hassoc : Associated (wconj w P) (E P) := by
    rw [hEq]; exact associated_unit_mul_left _ _ hunit
  -- 1–3: the coefficient clauses, through `scaleRoots`
  have h1 : (wconj w P).Monic := by rw [hsr]; exact (monic_scaleRoots_iff w).mpr hP
  have h2 : (wconj w P).natDegree = P.natDegree := by rw [hsr]; exact natDegree_scaleRoots P w
  have h3 : (wconj w P).coeff 0 = w ^ P.natDegree * P.coeff 0 := by
    rw [hsr, coeff_scaleRoots, Nat.sub_zero, mul_comm]
  -- 4: irreducibility
  have h4 : Irreducible (wconj w P) ↔ Irreducible P := by
    rw [hassoc.irreducible_iff]
    exact MulEquiv.irreducible_iff E
  -- 5: separability
  have h5 : (wconj w P).Separable ↔ P.Separable := by
    rw [hEq, separable_C_mul_iff (pow_ne_zero _ hw), hEdef, wsub_apply]
    exact separable_comp_scale w hw P
  -- 6: the irreducible-factor degree pattern
  have hPne : P ≠ 0 := hP.ne_zero
  have hWne : wconj w P ≠ 0 := h1.ne_zero
  have hdegE : ∀ p : Polynomial K, (E p).natDegree = p.natDegree := by
    intro p
    rw [hEdef, wsub_apply, natDegree_comp, natDegree_C_mul_X _ (inv_ne_zero hw), mul_one]
  have hprod : Associated (UniqueFactorizationMonoid.factors (wconj w P)).prod
      (Multiset.map (E : Polynomial K → Polynomial K)
        (UniqueFactorizationMonoid.factors P)).prod := by
    rw [Multiset.prod_hom _ (E : Polynomial K ≃ₐ[K] Polynomial K)]
    refine (UniqueFactorizationMonoid.factors_prod hWne).trans (hassoc.trans ?_)
    exact Associated.map (E : Polynomial K ≃ₐ[K] Polynomial K)
      (UniqueFactorizationMonoid.factors_prod hPne).symm
  have hrel : Multiset.Rel Associated (UniqueFactorizationMonoid.factors (wconj w P))
      (Multiset.map (E : Polynomial K → Polynomial K)
        (UniqueFactorizationMonoid.factors P)) := by
    refine UniqueFactorizationMonoid.factors_unique
      (fun x hx => UniqueFactorizationMonoid.irreducible_of_factor x hx) (fun x hx => ?_) hprod
    obtain ⟨y, hy, rfl⟩ := Multiset.mem_map.mp hx
    exact (MulEquiv.irreducible_iff (E : Polynomial K ≃ₐ[K] Polynomial K)).mpr
      (UniqueFactorizationMonoid.irreducible_of_factor y hy)
  have h6 : Multiset.map Polynomial.natDegree (UniqueFactorizationMonoid.factors (wconj w P))
      = Multiset.map Polynomial.natDegree (UniqueFactorizationMonoid.factors P) := by
    have hstep : Multiset.map Polynomial.natDegree
        (UniqueFactorizationMonoid.factors (wconj w P))
        = Multiset.map Polynomial.natDegree
          (Multiset.map (E : Polynomial K → Polynomial K)
            (UniqueFactorizationMonoid.factors P)) := by
      rw [← Multiset.rel_eq]
      rw [Multiset.rel_map]
      exact hrel.mono fun a _ b _ hab =>
        natDegree_eq_of_degree_eq (degree_eq_degree_of_associated hab)
    rw [hstep, Multiset.map_map]
    refine Multiset.map_congr rfl fun x _ => ?_
    exact hdegE x
  exact ⟨h1, h2, h3, h4, h5, h6⟩

end Uniformity.Density.Tower

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Tower.wconj
#print axioms Uniformity.Density.Tower.wconj_invariants

end AxCheck
