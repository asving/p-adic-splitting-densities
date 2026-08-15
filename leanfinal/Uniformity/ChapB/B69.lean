/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapB.B02
import Uniformity.ChapB.B08
import Uniformity.ChapB.B11

/-!
# Uniformity.ChapB.B69 — the development is shift-covariant

**Chapter B, NODE B.69** (`blueprint/CHAP-B_leaf_layer.md` §8, the recentering calculus).
Source: `EFF.HE3.27` (`LEMMA HE3-2`, the recentering).  The corpus's recentering has two halves —
a shift of the *key* and a shift of the *variable*; only the variable shift is a chapter-B node
(the key shift `φ ↦ φ − C` changes the order-1 datum and is chapter C's descent step).

The substitution `X ↦ X + c` is an `O`-algebra automorphism of `O[X]`, so it commutes with the
whole order-1 apparatus.  Two clauses:

* `dev_comp_shift` — the `φ`-adic development transports:
  `dev (φ(X+c)) (f(X+c)) j = (dev φ f j)(X+c)`;
* `npHgt_comp_shift` — hence the Newton-polygon heights are literally invariant:
  `npHgt (φ(X+c)) (f(X+c)) j = npHgt φ f j`.

`suppVal`, `sideSet`, `sideDeg` are defined from `npHgt` alone, so clause 2 propagates to them
verbatim at their own nodes; `resPoly` transports only up to the induced isomorphism of residual
fields, which is why the SIGNATURE stops at `npHgt`.

## Two remarks on the signed statements

**No monicity hypothesis, and none is needed.**  The blueprint STATEMENT says "`φ` monic", but
the signed SIGNATURE of `dev_comp_shift` carries no `hφ : φ.Monic`, and the identity is true
unconditionally — proved here in that stronger signed form.  The reason is that monicity
transports too: `Monic (φ.comp (X + C c)) ↔ Monic φ` (`Polynomial.leadingCoeff_taylor`).  So for
non-monic `φ` *both* sides fall into the junk branches of `%ₘ` and `/ₘ` simultaneously —
`f %ₘ φ = f` and `f /ₘ φ = 0` on the right, the same on the left — and the two sides agree
because `dev φ 0 j = 0` for every `φ` and `j` (the private `dev_zero_poly`), while `0.comp` is
`0`.  This is checked, not assumed: it is the `by_cases hφ : φ.Monic` split below.

**`hπ` is used, in clause 2 only.**  `npHgt_comp_shift` reads `gaussVal` through B.08's
`le_gaussVal_iff`, whose divisibility characterisation needs `hπ : Irreducible π`; clause 1 is
purely about monic division and carries no `π` at all.

DEPENDS: B.02 (`dev`) · B.07/B.08 (`gaussVal`, `le_gaussVal_iff`) · B.11 (`npHgt`) · mathlib
`Polynomial.taylor_apply`, `Polynomial.degree_taylor`, `Polynomial.leadingCoeff_taylor`,
`Polynomial.div_modByMonic_unique`, `Polynomial.modByMonic_add_div`,
`Polynomial.modByMonic_eq_of_not_monic`, `Polynomial.divByMonic_eq_of_not_monic`,
`Polynomial.comp_assoc`, `Polynomial.map_comp`, `Ideal.Quotient.eq_zero_iff_mem`,
`ENat.eq_of_forall_natCast_le_iff`.

**PROOF.**
1. The shift is `Polynomial.taylor c` (`taylor_apply : taylor c f = f.comp (X + C c)`, a `rfl`),
   which mathlib equips with exactly the two facts needed: `degree_taylor` (degrees are
   preserved) and `leadingCoeff_taylor` (hence monicity is preserved, both ways).  This is the
   same automorphism as the landed `Uniformity.Density.shift` of `Density/TypeOfInvariance.lean`
   named in the blueprint's DEPENDS; `taylor` is used instead because it carries the degree API
   and keeps this file's import surface inside chapter B.
2. Monic division commutes with the shift: apply `Polynomial.div_modByMonic_unique` to the
   candidate pair `q := (f /ₘ φ)(X+c)`, `r := (f %ₘ φ)(X+c)` — the reconstruction
   `r + φ(X+c) * q = f(X+c)` is `modByMonic_add_div` composed with the shift (`add_comp`,
   `mul_comp`), and `degree r < degree (φ(X+c))` is `degree_modByMonic_lt` after
   `degree_taylor` on both sides.  This is the uniqueness clause the blueprint's step 1 names.
3. Clause 1 is then induction on `j`, generalizing `f`, in the monic branch; the non-monic
   branch is the junk-branch computation described above.
4. Clause 2 reduces to `gaussVal (a.comp (X + C c)) = gaussVal a` (private
   `gaussVal_comp_shift`).  For that, `ENat.eq_of_forall_natCast_le_iff` turns the equality into
   `∀ k, (k ≤ gaussVal (a(X+c))) ↔ (k ≤ gaussVal a)`, and B.08's `le_gaussVal_iff hπ` turns each
   side into "π ^ k divides every coefficient".  One direction: if every coefficient of `a` is
   killed in `O ⧸ (π ^ k)` then `a.map (Ideal.Quotient.mk _) = 0`, and `Polynomial.map_comp`
   gives `(a(X+c)).map (mk) = (0).comp _ = 0`, i.e. the shifted coefficients are divisible too.
   The other direction is the same statement applied at `−c`, since
   `(a(X+c))(X + C (−c)) = a` (`comp_assoc`).  This is the blueprint's "`≤` in both directions
   using `c ↦ −c`".

Environment ENV-A′ (blueprint §0.1): ENV-A plus the explicit hypothesis `hπ : Irreducible π`
carried per signature.

## Status

Sorry-free, axiom-free (Lean core only).
-/

namespace Uniformity.Density.Leaf

open Polynomial

-- ENV-A′ (blueprint §0.1): the polynomial arena over a DVR, with `π` an explicit uniformizer
-- hypothesis on the statements that need it.
variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {π : O}

/-! ### The shift as a degree- and monicity-preserving automorphism -/

omit [IsDomain O] [IsDiscreteValuationRing O] in
/-- The shift preserves monicity, in both directions: `φ(X+c)` is monic iff `φ` is.  This is what
makes `dev_comp_shift` true with no monicity hypothesis. -/
private theorem monic_comp_shift_iff (φ : Polynomial O) (c : O) :
    (φ.comp (X + Polynomial.C c)).Monic ↔ φ.Monic := by
  rw [← Polynomial.taylor_apply, Polynomial.Monic, Polynomial.Monic,
    Polynomial.leadingCoeff_taylor]

/-- Monic division commutes with the shift, quotient and remainder together.  Proved by the
uniqueness clause of monic division applied to the shifted candidate pair. -/
private theorem div_mod_comp_shift {φ : Polynomial O} (hφ : φ.Monic) (c : O) (f : Polynomial O) :
    (f.comp (X + Polynomial.C c)) %ₘ (φ.comp (X + Polynomial.C c))
        = (f %ₘ φ).comp (X + Polynomial.C c) ∧
      (f.comp (X + Polynomial.C c)) /ₘ (φ.comp (X + Polynomial.C c))
        = (f /ₘ φ).comp (X + Polynomial.C c) := by
  have hmon : (φ.comp (X + Polynomial.C c)).Monic := (monic_comp_shift_iff φ c).2 hφ
  have h := Polynomial.div_modByMonic_unique
    ((f /ₘ φ).comp (X + Polynomial.C c)) ((f %ₘ φ).comp (X + Polynomial.C c)) hmon
    ⟨by rw [← Polynomial.mul_comp, ← Polynomial.add_comp, Polynomial.modByMonic_add_div], by
      rw [← Polynomial.taylor_apply, ← Polynomial.taylor_apply, Polynomial.degree_taylor,
        Polynomial.degree_taylor]
      exact Polynomial.degree_modByMonic_lt f hφ⟩
  exact ⟨h.2, h.1⟩

omit [IsDomain O] [IsDiscreteValuationRing O] in
/-- The development of `0` is `0`, at every height and for every key — monic or not.  Needed for
the junk branch of `dev_comp_shift`. -/
private theorem dev_zero_poly (φ : Polynomial O) (j : ℕ) : dev φ (0 : Polynomial O) j = 0 := by
  induction j with
  | zero => rw [dev, Polynomial.zero_modByMonic]
  | succ j ih => rw [dev, Polynomial.zero_divByMonic]; exact ih

/-! ### Clause 1 — the development transports -/

/-- **B.69 (a) — the development is shift-covariant.**  For every `c : O`, every key `φ` and
every `f`, the `φ`-adic development of `f` transports along `X ↦ X + c`:
`dev (φ(X+c)) (f(X+c)) j = (dev φ f j)(X+c)`.  No monicity hypothesis is needed (see the module
docstring: monicity itself transports, so the junk branches of `%ₘ`/`/ₘ` agree on both sides). -/
theorem dev_comp_shift (φ : Polynomial O) (c : O) (f : Polynomial O) (j : ℕ) :
    dev (φ.comp (X + Polynomial.C c)) (f.comp (X + Polynomial.C c)) j
      = (dev φ f j).comp (X + Polynomial.C c) := by
  by_cases hφ : φ.Monic
  · induction j generalizing f with
    | zero => rw [dev, dev]; exact (div_mod_comp_shift hφ c f).1
    | succ j ih => rw [dev, dev, (div_mod_comp_shift hφ c f).2]; exact ih _
  · have hns : ¬ (φ.comp (X + Polynomial.C c)).Monic :=
      fun h => hφ ((monic_comp_shift_iff φ c).1 h)
    cases j with
    | zero =>
      rw [dev, dev, Polynomial.modByMonic_eq_of_not_monic _ hns,
        Polynomial.modByMonic_eq_of_not_monic _ hφ]
    | succ j =>
      rw [dev, dev, Polynomial.divByMonic_eq_of_not_monic _ hns,
        Polynomial.divByMonic_eq_of_not_monic _ hφ, dev_zero_poly, dev_zero_poly,
        Polynomial.zero_comp]

/-! ### Clause 2 — the Gauss valuation, hence the heights, are invariant -/

omit [IsDomain O] [IsDiscreteValuationRing O] in
/-- The shift by `−c` undoes the shift by `c`. -/
private theorem comp_shift_comp_shift (a : Polynomial O) (c : O) :
    (a.comp (X + Polynomial.C c)).comp (X + Polynomial.C (-c)) = a := by
  rw [Polynomial.comp_assoc]
  simp

omit [IsDomain O] [IsDiscreteValuationRing O] in
/-- Coefficientwise divisibility by `π ^ k` survives the shift: pushing into `O ⧸ (π ^ k)` turns
the hypothesis into `a.map (mk) = 0`, and `map` commutes with `comp`. -/
private theorem pow_dvd_coeff_comp_shift {k : ℕ} {a : Polynomial O} (c : O)
    (h : ∀ i, π ^ k ∣ a.coeff i) (i : ℕ) :
    π ^ k ∣ (a.comp (X + Polynomial.C c)).coeff i := by
  have key : (a.comp (X + Polynomial.C c)).map (Ideal.Quotient.mk (Ideal.span {π ^ k})) = 0 := by
    rw [Polynomial.map_comp]
    have ha : a.map (Ideal.Quotient.mk (Ideal.span {π ^ k})) = 0 := by
      ext j
      rw [Polynomial.coeff_map, Polynomial.coeff_zero, Ideal.Quotient.eq_zero_iff_mem,
        Ideal.mem_span_singleton]
      exact h j
    rw [ha, Polynomial.zero_comp]
  have h2 := congrArg (fun p => Polynomial.coeff p i) key
  simp only [Polynomial.coeff_map, Polynomial.coeff_zero] at h2
  rwa [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton] at h2

/-- The Gauss valuation is shift-invariant.  Kept private: the node's signed surface is the two
theorems `dev_comp_shift` / `npHgt_comp_shift`, and a later node that needs this on its own
should promote it with its own contract. -/
private theorem gaussVal_comp_shift (hπ : Irreducible π) (a : Polynomial O) (c : O) :
    gaussVal (a.comp (X + Polynomial.C c)) = gaussVal a := by
  refine ENat.eq_of_forall_natCast_le_iff fun k => ?_
  rw [le_gaussVal_iff hπ, le_gaussVal_iff hπ]
  refine ⟨fun h i => ?_, fun h i => pow_dvd_coeff_comp_shift c h i⟩
  have h2 := pow_dvd_coeff_comp_shift (π := π) (-c) h i
  rwa [comp_shift_comp_shift] at h2

/-- **B.69 (b) — the Newton-polygon heights are shift-invariant.**  `npHgt` is `gaussVal ∘ dev`,
so clause 1 plus the shift-invariance of the Gauss valuation gives
`npHgt (φ(X+c)) (f(X+c)) j = npHgt φ f j` on the nose.  `suppVal`, `sideSet` and `sideDeg`, being
defined from `npHgt`, inherit this verbatim. -/
theorem npHgt_comp_shift (hπ : Irreducible π) (φ : Polynomial O) (c : O) (f : Polynomial O)
    (j : ℕ) :
    npHgt (φ.comp (X + Polynomial.C c)) (f.comp (X + Polynomial.C c)) j = npHgt φ f j := by
  rw [npHgt, npHgt, dev_comp_shift, gaussVal_comp_shift hπ]

end Uniformity.Density.Leaf

/-! ## Axiom footprint -/

section AxCheck
#print axioms Uniformity.Density.Leaf.dev_comp_shift
#print axioms Uniformity.Density.Leaf.npHgt_comp_shift
end AxCheck
