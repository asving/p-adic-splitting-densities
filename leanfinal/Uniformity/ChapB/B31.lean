/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapB.B10
import Uniformity.ChapB.B11

/-!
# Uniformity.ChapB.B31 — monic division does not lower the Gauss valuation

**Chapter B, NODE B.31** [lemma] (`blueprint/CHAP-B_leaf_layer.md` §5, the slot lemma and the
product law), ENV-A′.

For `φ` monic and any `a ∈ O[X]`, both halves of monic division can only *raise* the Gauss
valuation:

* `gaussVal_le_modByMonic` — `gaussVal a ≤ gaussVal (a %ₘ φ)`;
* `gaussVal_le_divByMonic` — `gaussVal a ≤ gaussVal (a /ₘ φ)`;
* `gaussVal_le_npHgt` — consequently `gaussVal f ≤ npHgt φ f j` for every `j`: every height of
  the `φ`-adic polygon lies weakly above the Gauss valuation of `f` itself.

This is what makes carrying safe in B.32: moving mass from `φ`-index `t` to `t + 1` adds `u` to
the weight and cannot lower the Gauss valuation.

DEPENDS: B.02 (`dev`) · B.07 (`gaussVal`) · B.08 (`le_gaussVal_iff`, `gaussVal_eq_top_iff`) ·
B.10 (its step-2 map-commutation, reproved here in the `a ↦ 0` shape the statement needs) ·
B.11 (`npHgt`) · mathlib `Polynomial.map_modByMonic`, `Polynomial.map_divByMonic`,
`Polynomial.zero_modByMonic`, `Polynomial.zero_divByMonic`, `Ideal.mem_span_singleton`,
`Ideal.Quotient.eq_zero_iff_mem`, `WithTop.ne_top_iff_exists`.

**PROOF.**
1. Reduce to the case `gaussVal a ≠ ⊤` (else `a = 0` by B.08's `gaussVal_eq_top_iff`, and both
   sides are `⊤`), and write `gaussVal a = (k : ℕ∞)`.
2. By B.08, `π ^ k` divides every coefficient of `a`, i.e. `a.map ρ = 0` for
   `ρ := Ideal.Quotient.mk (Ideal.span {π ^ k})`.
3. By B.10's step 2 (`map` commutes with monic division — mathlib
   `Polynomial.map_modByMonic` / `Polynomial.map_divByMonic`, which is exactly the ingredient
   B.10's own `map_dev_congr` runs on), `(a %ₘ φ).map ρ = (a.map ρ) %ₘ (φ.map ρ) = 0` and
   likewise for `/ₘ`.
4. B.08 in the other direction turns each `map … = 0` back into `(k : ℕ∞) ≤ gaussVal (…)`.
5. `gaussVal_le_npHgt`: induction on `j` with `f` generalized, using both halves —
   `npHgt φ f 0 = gaussVal (f %ₘ φ)` is the `%ₘ` half, and
   `npHgt φ f (j+1) = npHgt φ (f /ₘ φ) j` reduces to the `/ₘ` half composed with the induction
   hypothesis at `f /ₘ φ`.

The quotient `ρ` is taken modulo the **principal ideal `span {π ^ k}`** rather than modulo
`(maximalIdeal O) ^ k`, matching B.10's landed choice: nothing in the argument uses that the
ideal is a power of the maximal ideal, and the principal form is what
`Ideal.mem_span_singleton` reads off directly.  `hπ : Irreducible π` is genuinely used — it is
the hypothesis of B.08's `le_gaussVal_iff`, which is the bridge between `gaussVal` and
coefficientwise divisibility in both directions.

## Faithfulness

`EFF.W12.23` ("the development lives at level `N`", i.e. the digits of `a_j` are digits of `f`)
and `EFF.HE3.27`(c). The Lean statement is the arithmetic content of both: no digit of a
development coefficient can sit below a digit of `f`.

SOURCE: `EFF.W12.23`; `EFF.HE3.27`(c).

## Status

Sorry-free, axiom-free (Lean core only).
-/

namespace Uniformity.Density.Leaf

open Polynomial

-- ENV-A′ (blueprint §0.1): the polynomial arena, plus `hπ : Irreducible π` carried per
-- signature.
variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {π : O}

omit [IsDomain O] [IsDiscreteValuationRing O] in
/-- Step 2 of the proof: divisibility of every coefficient by `π ^ N` says exactly that the
polynomial dies in `O ⧸ span {π ^ N}`. Private helper. -/
private theorem map_span_eq_zero {N : ℕ} {b : Polynomial O} (h : ∀ i, π ^ N ∣ b.coeff i) :
    b.map (Ideal.Quotient.mk (Ideal.span {π ^ N})) = 0 := by
  refine Polynomial.ext fun i => ?_
  rw [Polynomial.coeff_map, Polynomial.coeff_zero, Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.mem_span_singleton.2 (h i)

omit [IsDomain O] [IsDiscreteValuationRing O] in
/-- Step 4 of the proof: the converse reading of `map_span_eq_zero`. Private helper. -/
private theorem dvd_coeff_of_map_span_eq_zero {N : ℕ} {b : Polynomial O}
    (h : b.map (Ideal.Quotient.mk (Ideal.span {π ^ N})) = 0) (i : ℕ) : π ^ N ∣ b.coeff i := by
  have hc : (Ideal.Quotient.mk (Ideal.span {π ^ N})) (b.coeff i) = 0 := by
    have := congrArg (fun p => Polynomial.coeff p i) h
    simpa only [Polynomial.coeff_map, Polynomial.coeff_zero] using this
  exact Ideal.mem_span_singleton.1 (Ideal.Quotient.eq_zero_iff_mem.1 hc)

/-- **B.31 (a) — monic remainder does not lower the Gauss valuation.** -/
theorem gaussVal_le_modByMonic (hπ : Irreducible π) {φ : Polynomial O} (hφ : φ.Monic)
    (a : Polynomial O) : gaussVal a ≤ gaussVal (a %ₘ φ) := by
  by_cases htop : gaussVal a = ⊤
  · have ha : a = 0 := gaussVal_eq_top_iff.1 htop
    subst ha
    rw [Polynomial.zero_modByMonic]
  · obtain ⟨k, hk⟩ := WithTop.ne_top_iff_exists.1 htop
    rw [← hk]
    refine (le_gaussVal_iff hπ).2 fun i => ?_
    refine dvd_coeff_of_map_span_eq_zero (N := k) ?_ i
    rw [Polynomial.map_modByMonic _ hφ,
      map_span_eq_zero ((le_gaussVal_iff hπ).1 (le_of_eq hk)), Polynomial.zero_modByMonic]

/-- **B.31 (b) — monic quotient does not lower the Gauss valuation.** -/
theorem gaussVal_le_divByMonic (hπ : Irreducible π) {φ : Polynomial O} (hφ : φ.Monic)
    (a : Polynomial O) : gaussVal a ≤ gaussVal (a /ₘ φ) := by
  by_cases htop : gaussVal a = ⊤
  · have ha : a = 0 := gaussVal_eq_top_iff.1 htop
    subst ha
    rw [Polynomial.zero_divByMonic]
  · obtain ⟨k, hk⟩ := WithTop.ne_top_iff_exists.1 htop
    rw [← hk]
    refine (le_gaussVal_iff hπ).2 fun i => ?_
    refine dvd_coeff_of_map_span_eq_zero (N := k) ?_ i
    rw [Polynomial.map_divByMonic _ hφ,
      map_span_eq_zero ((le_gaussVal_iff hπ).1 (le_of_eq hk)), Polynomial.zero_divByMonic]

/-- **B.31 (c) — every polygon height lies above the Gauss valuation.** -/
theorem gaussVal_le_npHgt (hπ : Irreducible π) {φ : Polynomial O} (hφ : φ.Monic)
    (f : Polynomial O) (j : ℕ) : gaussVal f ≤ npHgt φ f j := by
  induction j generalizing f with
  | zero => exact gaussVal_le_modByMonic hπ hφ f
  | succ j ih => exact (gaussVal_le_divByMonic hπ hφ f).trans (ih (f /ₘ φ))

end Uniformity.Density.Leaf

/-! ## Axiom footprint -/

section AxCheck
#print axioms Uniformity.Density.Leaf.gaussVal_le_modByMonic
#print axioms Uniformity.Density.Leaf.gaussVal_le_divByMonic
#print axioms Uniformity.Density.Leaf.gaussVal_le_npHgt
end AxCheck
