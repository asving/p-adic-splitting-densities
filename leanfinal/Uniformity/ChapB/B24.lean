/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapB.B08
import Uniformity.ChapB.B22
import Uniformity.ChapB.B23
import Uniformity.HenselFactorization

/-!
# Uniformity.ChapB.B24 — the digit polynomial's specification

**Chapter B, NODE B.24** [lemma] (`blueprint/CHAP-B_leaf_layer.md` §4, the order-1 residual
layer), ENV-A′.

*The digit polynomial's specification.*  For `hπ : Irreducible π` and `a ∈ O[X]`:

* `(digPoly π k a).coeff i = digAt π k (a.coeff i)` for every `i`;
* `(digPoly π k a).degree ≤ a.degree`;
* if `a = C (π^k) * b` then `digPoly π k a = b.map (residue O)`;
* if `(k : ℕ∞) ≤ gaussVal a` then `digPoly π k a = 0 ↔ (k+1 : ℕ∞) ≤ gaussVal a`.  In particular
  for `a ≠ 0` and `k` with `gaussVal a = (k : ℕ∞)`, `digPoly π k a ≠ 0`.

Four public declarations, as signed (same justification as B.22: one specification, read at
four call sites — B.28's residual coefficients, B.30's nonvanishing, B.36's `resMk_eq_zero_iff`,
B.53's unit extraction).  The single private helper `digAt_of_zero` is the content of the
`hπ` hypothesis, isolated: see the A-F.5 note below.

DEPENDS: B.08 (`le_gaussVal_iff`) · B.21 (`digAt`) · B.22 (`digAt_eq`, `digAt_eq_zero_iff`) ·
B.23 (`digPoly`) · landed `Uniformity.Hensel.coeff_sum_range_C_mul_X_pow`
(`HenselFactorization.lean:175`) · mathlib `Polynomial.ext_iff`,
`Polynomial.coeff_eq_zero_of_degree_lt`, `Polynomial.degree_le_iff_coeff_zero`,
`Polynomial.coeff_C_mul`, `Polynomial.coeff_map`.

**PROOF.**
1. `digPoly_coeff`: landed `coeff_sum_range_C_mul_X_pow` gives the value
   `if i < a.natDegree + 1 then digAt π k (a.coeff i) else 0`; for `i > a.natDegree`,
   `a.coeff i = 0` and `digAt π k 0 = 0` (B.22's `digAt_eq` at `y = 0`).
2. `degree_digPoly_le`: `Polynomial.degree_le_iff_coeff_zero` plus step 1 and
   `coeff_eq_zero_of_degree_lt`.
3. `digPoly_eq_map`: coefficientwise by step 1 — `a.coeff i = π^k * b.coeff i` (from `h` and
   `coeff_C_mul`), so B.22's `digAt_eq` gives `residue O (b.coeff i)`, which is
   `(b.map (residue O)).coeff i` (`coeff_map`).
4. `digPoly_eq_zero_iff`: by step 1 and `Polynomial.ext_iff`, `digPoly π k a = 0` iff
   `digAt π k (a.coeff i) = 0` for all `i`, iff `π^(k+1) ∣ a.coeff i` for all `i` (B.22's
   `digAt_eq_zero_iff`, whose hypothesis `π^k ∣ a.coeff i` comes from `h` via B.08's
   `le_gaussVal_iff`), iff `(k+1 : ℕ∞) ≤ gaussVal a` (B.08 again).

## The `hπ` hypothesis on `degree_digPoly_le` (blueprint amendment A-F.5)

`degree_digPoly_le` was signed *without* `(hπ : Irreducible π)` and that form was
**conditionally refuted**: over a bare `{π : O}` it is equivalent to `∀ π k, digAt π k 0 = 0`
(at `a = 0`, `a.degree = ⊥` while `digPoly π k 0 = C (digAt π k 0)`), and that is independent
at our pin — B.21's `digAt` reads an `Exists.choose` witness of `π ^ k ∣ 0`, which is
unconstrained when `π ^ k = 0`.  `hπ` gives `π ^ k ≠ 0`, which pins the witness to `0` in the
domain `O`.  That is exactly the private `digAt_of_zero` below, and it is also what steps 1
and 2 above consume; the other three clauses carried `hπ` already, and the STATEMENT prose
always scoped all four under it.

SOURCE: `EFF.W12.23` (the three-way slot-membership law); `EFF.HE3.14`.

TEETH: `W12-SHAPE` → Lean theorem (the *"digit at the polygon height is nonzero at a vertex"*
half of `EFF.W12.23`'s membership law is `digPoly_eq_zero_iff`, contrapositive at
`gaussVal a = k`).

## Status

Sorry-free, axiom-free (Lean core only).
-/

namespace Uniformity.Density.Leaf

open Polynomial IsLocalRing

-- ENV-A′ (blueprint §0.1): the polynomial arena over a DVR, with `π` an explicit uniformizer
-- hypothesis on the statements that need it.
variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {π : O}

/-- The whole content of `hπ` in this node: in a domain, `π ^ k ≠ 0` pins the `Exists.choose`
witness of `π ^ k ∣ 0` to `0`, so the digit of `0` is `0`.  Without it the value is
independent (blueprint amendment A-F.5). -/
private theorem digAt_of_zero (hπ : Irreducible π) (k : ℕ) : digAt π k (0 : O) = 0 := by
  rw [digAt_eq hπ (mul_zero (π ^ k)).symm, map_zero]

/-- **B.24 (a) — the digit polynomial's coefficients.**  `digPoly` is assembled from a
truncated sum, but its coefficients are the scalar digits at *every* index: past
`a.natDegree` both sides are `0`. -/
theorem digPoly_coeff (hπ : Irreducible π) (k i : ℕ) (a : Polynomial O) :
    (digPoly π k a).coeff i = digAt π k (a.coeff i) := by
  rw [digPoly, Uniformity.Hensel.coeff_sum_range_C_mul_X_pow]
  split_ifs with h
  · rfl
  · rw [a.coeff_eq_zero_of_natDegree_lt (by omega), digAt_of_zero hπ]

/-- **B.24 (b) — the degree bound.**  Taking digits never raises the degree.
*[repaired: A-F.5]* `(hπ : Irreducible π)` is load-bearing at `a = 0`; see the module note. -/
theorem degree_digPoly_le (hπ : Irreducible π) (k : ℕ) (a : Polynomial O) :
    (digPoly π k a).degree ≤ a.degree := by
  refine (Polynomial.degree_le_iff_coeff_zero _ _).mpr fun m hm => ?_
  rw [digPoly_coeff hπ, Polynomial.coeff_eq_zero_of_degree_lt hm, digAt_of_zero hπ]

/-- **B.24 (c) — the digit polynomial of an exact multiple.**  If `a = π^k · b` then the digit
of `a` at height `k` is the reduction of `b`. -/
theorem digPoly_eq_map (hπ : Irreducible π) {k : ℕ} {a b : Polynomial O}
    (h : a = Polynomial.C (π ^ k) * b) : digPoly π k a = b.map (IsLocalRing.residue O) := by
  refine Polynomial.ext fun i => ?_
  rw [digPoly_coeff hπ, Polynomial.coeff_map,
    digAt_eq hπ (show a.coeff i = π ^ k * b.coeff i by rw [h, Polynomial.coeff_C_mul])]

/-- **B.24 (d) — the vanishing criterion.**  At a height the Gauss valuation already reaches,
the digit polynomial vanishes exactly when the valuation is strictly larger.  Contrapositive:
if `gaussVal a = k` then `digPoly π k a ≠ 0`, the nonvanishing of the residual coefficient at
a vertex. -/
theorem digPoly_eq_zero_iff (hπ : Irreducible π) {k : ℕ} {a : Polynomial O}
    (h : (k : ℕ∞) ≤ gaussVal a) : digPoly π k a = 0 ↔ ((k + 1 : ℕ) : ℕ∞) ≤ gaussVal a := by
  have hdvd : ∀ i, π ^ k ∣ a.coeff i := (le_gaussVal_iff hπ).mp h
  rw [Polynomial.ext_iff, le_gaussVal_iff hπ]
  simp only [Polynomial.coeff_zero, digPoly_coeff hπ]
  exact forall_congr' fun i => digAt_eq_zero_iff hπ (hdvd i)

section AxCheck
#print axioms Uniformity.Density.Leaf.digPoly_coeff
#print axioms Uniformity.Density.Leaf.degree_digPoly_le
#print axioms Uniformity.Density.Leaf.digPoly_eq_map
#print axioms Uniformity.Density.Leaf.digPoly_eq_zero_iff
end AxCheck

end Uniformity.Density.Leaf
