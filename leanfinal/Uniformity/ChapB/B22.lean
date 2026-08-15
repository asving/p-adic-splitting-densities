/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapB.B21

/-!
# Uniformity.ChapB.B22 — the digit's specification

**Chapter B, NODE B.22** (`blueprint/CHAP-B_leaf_layer.md` §4, the order-1 residual layer).
Source: `EFF.W12.23` (*"write `digit_h(a_j) ∈ F_{q^d}` for the slot at height `h`"* — the GMN
order-1 residual-coefficient convention); `EFF.HE3.14`.

B.21 defines `digAt π k x` by a `dite` on `π ^ k ∣ x`, which is the wrong thing to reason with.
This node is the API that replaces it, for `π` irreducible:

* `digAt_eq` — well-definedness: if `x = π ^ k * y` then `digAt π k x = residue O y`, for **any**
  witness `y` (the `Exists.choose` in the definition is pinned by cancellation in the domain `O`);
* `digAt_eq_zero_iff` — the digit *detects exactness*: on the divisible branch the digit vanishes
  exactly when the divisibility improves by one;
* `digAt_add` — additivity at a common height;
* `digAt_zero` — height `0` is the plain residue.

Every consumer of the digit calculus reads at least two of the four, so they land together.

DEPENDS: B.21 (`digAt`) · mathlib `mul_left_cancel₀`, `pow_ne_zero`,
`IsLocalRing.residue_eq_zero_iff`, `Irreducible.maximalIdeal_eq`, `Ideal.mem_span_singleton`,
`mul_dvd_mul_iff_left`.

**PROOF.**
1. `digAt_eq`: `π ^ k ∣ x` holds by `⟨y, h⟩`, so the `dif_pos` branch fires with the chosen `y'`
   satisfying `π ^ k * y' = x = π ^ k * y`; `mul_left_cancel₀ (pow_ne_zero k hπ.ne_zero)` gives
   `y' = y`.  Only `π ^ k ≠ 0` is used, so this is factored through the private
   `digAt_eq_of_pow_ne_zero`.
2. `digAt_eq_zero_iff`: write `x = π ^ k * y`; by step 1 the digit is `residue O y`, which is `0`
   iff `y ∈ maximalIdeal O` (`residue_eq_zero_iff`) iff `π ∣ y` (`hπ.maximalIdeal_eq`,
   `Ideal.mem_span_singleton`) iff `π ^ k * π ∣ π ^ k * y` (`mul_dvd_mul_iff_left`, again using
   `π ^ k ≠ 0`), which is `π ^ (k + 1) ∣ x` after `pow_succ`.
3. `digAt_add`: write `x = π ^ k * y`, `x' = π ^ k * y'`; then `x + x' = π ^ k * (y + y')`; apply
   step 1 three times and `map_add`.
4. `digAt_zero`: step 1's core at `k = 0` with `y = x`, since `π ^ 0 = 1 ≠ 0` in the domain `O`
   whatever `π` is — this clause needs no irreducibility of `π` and its signature carries none.

Environment ENV-A′ (blueprint §0.1): ENV-A plus the explicit hypothesis `hπ : Irreducible π`
carried per signature.

## Status

Sorry-free, axiom-free (Lean core only).
-/

-- `digAt_zero` does not use `[IsDiscreteValuationRing O]`, but the signature is frozen against
-- the gate-verified stub (`leanspec/Leanspec/ChapB.lean`, **B.22d**), which is elaborated in
-- exactly the ENV-A′ `variable` block reproduced below; trimming the binders would break the
-- type diff.
set_option linter.unusedSectionVars false

namespace Uniformity.Density.Leaf

open IsLocalRing

-- ENV-A′ (blueprint §0.1): the polynomial arena over a DVR, with `π` an explicit uniformizer
-- hypothesis on the statements that need it.
variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {π : O}

/-- The cancellation core of `digAt_eq`: all that is used of `hπ` is `π ^ k ≠ 0`.  Stated
separately so that `digAt_zero`, whose signature carries no irreducibility, can use it at
`k = 0` where `π ^ 0 = 1 ≠ 0` unconditionally. -/
private theorem digAt_eq_of_pow_ne_zero {k : ℕ} (hk : π ^ k ≠ 0) {x y : O}
    (h : x = π ^ k * y) : digAt π k x = IsLocalRing.residue O y := by
  classical
  have hd : π ^ k ∣ x := ⟨y, h⟩
  have hchoose : hd.choose = y := mul_left_cancel₀ hk (hd.choose_spec.symm.trans h)
  simp only [digAt, dif_pos hd, hchoose]

/-- **B.22 (a) — the digit is well defined.**  Any witness of `π ^ k ∣ x` computes the digit:
if `x = π ^ k * y` then `digAt π k x` is the residue of `y`. -/
theorem digAt_eq (hπ : Irreducible π) {k : ℕ} {x y : O} (h : x = π ^ k * y) :
    digAt π k x = IsLocalRing.residue O y :=
  digAt_eq_of_pow_ne_zero (pow_ne_zero k hπ.ne_zero) h

/-- **B.22 (b) — the digit detects exactness.**  On the divisible branch the digit at height `k`
vanishes exactly when the divisibility improves to height `k + 1`. -/
theorem digAt_eq_zero_iff (hπ : Irreducible π) {k : ℕ} {x : O} (h : π ^ k ∣ x) :
    digAt π k x = 0 ↔ π ^ (k + 1) ∣ x := by
  obtain ⟨y, rfl⟩ := h
  rw [digAt_eq hπ rfl, IsLocalRing.residue_eq_zero_iff, hπ.maximalIdeal_eq,
    Ideal.mem_span_singleton, pow_succ, mul_dvd_mul_iff_left (pow_ne_zero k hπ.ne_zero)]

/-- **B.22 (c) — additivity at a common height.**  The digit is additive on elements both
divisible by `π ^ k`. -/
theorem digAt_add (hπ : Irreducible π) {k : ℕ} {x x' : O} (h : π ^ k ∣ x) (h' : π ^ k ∣ x') :
    digAt π k (x + x') = digAt π k x + digAt π k x' := by
  obtain ⟨y, rfl⟩ := h
  obtain ⟨y', rfl⟩ := h'
  rw [digAt_eq hπ (mul_add (π ^ k) y y').symm, digAt_eq hπ rfl, digAt_eq hπ rfl, map_add]

/-- **B.22 (d) — height zero is the residue.**  No irreducibility is needed: at `k = 0` the
witness is pinned by `one_mul`. -/
theorem digAt_zero (x : O) : digAt π 0 x = IsLocalRing.residue O x :=
  digAt_eq_of_pow_ne_zero (by simp) (by simp)

end Uniformity.Density.Leaf

/-! ## Axiom footprint -/

section AxCheck
#print axioms Uniformity.Density.Leaf.digAt_eq
#print axioms Uniformity.Density.Leaf.digAt_eq_zero_iff
#print axioms Uniformity.Density.Leaf.digAt_add
#print axioms Uniformity.Density.Leaf.digAt_zero
end AxCheck
