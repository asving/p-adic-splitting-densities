/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapB.B04
import Uniformity.ChapB.B09
import Uniformity.ChapB.B24
import Uniformity.ChapB.B31
import Uniformity.ChapB.B25
import Uniformity.ChapB.B32a

/-!
# Uniformity.ChapB.B35a — the digit calculus of the product law (helpers)

**Chapter B, NODE B.35, part (a) of the mandated 4-way split**
(`blueprint/CHAP-B_leaf_layer.md` §5), ENV-A′. Helper declarations only; the two signed
contract theorems are `B35c` (`resPoly_mul_of_pure`) and `B35d` (`suppVal_mul_of_pure`).

This file collects the two mechanical ingredients the blueprint's PROOF steps 1 and 4 name:

* **the development of a `φ`-power multiple** — `dev φ (x * φ ^ t) (t + s) = dev φ x s` and
  `dev φ (x * φ ^ t) j = 0` for `j < t`, plus additivity of `dev` over a `Finset.sum`. Together
  these turn the *representation* `f * g = Σ_{j,i} (dev φ f j · dev φ g i) · φ^(j+i)` (B.05 twice)
  into a term-by-term computation of the product's development, which is what the blueprint's
  "convolution after carrying" needs: the term `x · φ^t` contributes `x %ₘ φ` at abscissa `t` and
  the **carry** `x /ₘ φ` at abscissa `t + 1`, and nothing anywhere else.
* **the graded ring laws of `resMk`** (B.25's height-`k` residual reduction): at heights where the
  arguments are `π`-divisible enough, `resMk` is additive, multiplicative with heights adding,
  kills multiples of the key, is insensitive to `%ₘ φ`, and vanishes on arguments of strictly
  larger Gauss valuation. This is the blueprint's step-4 helper
  (`digAt π (k+k') (x*y) = digAt π k x * digAt π k' y`) in the form the later files consume, and
  it is proved through B.24's `digPoly_eq_map` rather than coefficientwise: `(K : ℕ∞) ≤ gaussVal a`
  is *equivalent* to `C (π ^ K) ∣ a` (mathlib `Polynomial.C_dvd_iff_dvd_coeff` + B.08), so every
  law below is `digPoly π K (C (π^K) * b) = b.map (residue O)` composed with the ring-hom
  properties of `Polynomial.map` and `AdjoinRoot.mk`.

DEPENDS: B.02 (`dev`) · B.04 (`dev_eq_zero_of_lt`, and its `%ₘ`/`/ₘ` idioms) · B.07 (`gaussVal`) ·
B.08 (`le_gaussVal_iff`) · B.09 (`gaussVal_mul`) · B.21/B.23 (`digAt`, `digPoly`) ·
B.24 (`digPoly_eq_map`, `digPoly_eq_zero_iff`) · B.25 (`resMk`) ·
B.31 (`gaussVal_le_modByMonic`, `gaussVal_le_divByMonic`) · mathlib
`Polynomial.C_dvd_iff_dvd_coeff`, `Polynomial.mul_divByMonic_cancel_left`,
`Polynomial.modByMonic_add_div`, `AdjoinRoot.mk_self`.

## Status

Sorry-free, axiom-free (Lean core only).
-/

namespace Uniformity.Density.Leaf

open Polynomial

-- ENV-A′ (blueprint §0.1): the polynomial arena, plus `hπ : Irreducible π` carried per signature.
variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {π : O}

/-! ### The development of a `φ`-power multiple -/

omit [IsDomain O] [IsDiscreteValuationRing O] in
/-- The development of `0` vanishes at every abscissa (B.04's private helper, re-exported for the
`Finset.sum` induction below). -/
theorem dev_of_zero (φ : Polynomial O) : ∀ j : ℕ, dev φ (0 : Polynomial O) j = 0 := by
  intro j
  induction j with
  | zero => exact zero_modByMonic φ
  | succ j ih => rw [dev, zero_divByMonic]; exact ih

omit [IsDomain O] [IsDiscreteValuationRing O] in
/-- **The development shifts along multiplication by `φ ^ t`.** `dev φ (x * φ ^ t) (t + s)` is
`dev φ x s`: multiplying by `φ ^ t` translates the whole development `t` steps to the right. -/
theorem dev_mul_pow {φ : Polynomial O} (hφ : φ.Monic) :
    ∀ (t : ℕ) (x : Polynomial O) (s : ℕ), dev φ (x * φ ^ t) (t + s) = dev φ x s := by
  intro t
  induction t with
  | zero => intro x s; simp
  | succ t ih =>
    intro x s
    have hidx : t + 1 + s = (t + s) + 1 := by omega
    have hdiv : (x * φ ^ (t + 1)) /ₘ φ = x * φ ^ t := by
      have hrw : x * φ ^ (t + 1) = φ * (x * φ ^ t) := by rw [pow_succ]; ring
      rw [hrw, mul_divByMonic_cancel_left _ hφ]
    rw [hidx, dev, hdiv, ih]

omit [IsDomain O] [IsDiscreteValuationRing O] in
/-- **Nothing sits left of the shift.** `dev φ (x * φ ^ t) j = 0` for `j < t`. -/
theorem dev_mul_pow_of_lt {φ : Polynomial O} (hφ : φ.Monic) :
    ∀ (t : ℕ) (x : Polynomial O) (j : ℕ), j < t → dev φ (x * φ ^ t) j = 0 := by
  intro t
  induction t with
  | zero => intro x j hj; exact absurd hj (Nat.not_lt_zero j)
  | succ t ih =>
    intro x j hj
    have hdiv : (x * φ ^ (t + 1)) /ₘ φ = x * φ ^ t := by
      have hrw : x * φ ^ (t + 1) = φ * (x * φ ^ t) := by rw [pow_succ]; ring
      rw [hrw, mul_divByMonic_cancel_left _ hφ]
    match j with
    | 0 =>
      have hdvd : φ ∣ x * φ ^ (t + 1) := ⟨x * φ ^ t, by rw [pow_succ]; ring⟩
      exact (modByMonic_eq_zero_iff_dvd hφ).2 hdvd
    | (j + 1) =>
      rw [dev, hdiv]
      exact ih x j (by omega)

/-- **The development is additive over a `Finset.sum`** (B.32 (a)'s `dev_add_of_monic`, iterated). -/
theorem dev_finsetSum {φ : Polynomial O} (hφ : φ.Monic) {ι : Type*} (s : Finset ι)
    (F : ι → Polynomial O) (j : ℕ) :
    dev φ (∑ i ∈ s, F i) j = ∑ i ∈ s, dev φ (F i) j := by
  classical
  induction s using Finset.cons_induction with
  | empty => simpa using dev_of_zero φ j
  | cons i s hi ih => rw [Finset.sum_cons, Finset.sum_cons, dev_add_of_monic hφ, ih]

/-! ### The graded ring laws of `resMk` -/

/-- `(K : ℕ∞) ≤ gaussVal a` says exactly that `a` is `C (π ^ K)` times a polynomial. -/
theorem exists_eq_C_pow_mul (hπ : Irreducible π) {K : ℕ} {a : Polynomial O}
    (h : (K : ℕ∞) ≤ gaussVal a) : ∃ b : Polynomial O, a = Polynomial.C (π ^ K) * b := by
  have hdvd : Polynomial.C (π ^ K) ∣ a :=
    (Polynomial.C_dvd_iff_dvd_coeff _ _).2 ((le_gaussVal_iff hπ).1 h)
  obtain ⟨b, hb⟩ := hdvd
  exact ⟨b, hb⟩

/-- A `Finset.sum` of polynomials all of Gauss valuation `≥ K` has Gauss valuation `≥ K`. -/
theorem le_gaussVal_finsetSum (hπ : Irreducible π) {K : ℕ} {ι : Type*} (s : Finset ι)
    (F : ι → Polynomial O) (h : ∀ i ∈ s, (K : ℕ∞) ≤ gaussVal (F i)) :
    (K : ℕ∞) ≤ gaussVal (∑ i ∈ s, F i) := by
  rw [le_gaussVal_iff hπ]
  intro j
  rw [Polynomial.finsetSum_coeff]
  exact Finset.dvd_sum fun i hi => ((le_gaussVal_iff hπ).1 (h i hi)) j

/-- `resMk` kills `0`. -/
theorem resMk_of_zero (hπ : Irreducible π) (φ : Polynomial O) (K : ℕ) :
    resMk π φ K (0 : Polynomial O) = 0 := by
  rw [resMk, digPoly_eq_map hπ (a := (0 : Polynomial O)) (b := 0) (by simp)]
  simp

/-- **`resMk` is additive at a common height**, on arguments of Gauss valuation `≥ K`. -/
theorem resMk_add (hπ : Irreducible π) {φ : Polynomial O} {K : ℕ} {a b : Polynomial O}
    (ha : (K : ℕ∞) ≤ gaussVal a) (hb : (K : ℕ∞) ≤ gaussVal b) :
    resMk π φ K (a + b) = resMk π φ K a + resMk π φ K b := by
  obtain ⟨a', ha'⟩ := exists_eq_C_pow_mul hπ ha
  obtain ⟨b', hb'⟩ := exists_eq_C_pow_mul hπ hb
  have hsum : a + b = Polynomial.C (π ^ K) * (a' + b') := by rw [ha', hb']; ring
  rw [resMk, resMk, resMk, digPoly_eq_map hπ ha', digPoly_eq_map hπ hb',
    digPoly_eq_map hπ hsum, Polynomial.map_add, map_add]

/-- **`resMk` is multiplicative with heights adding**, on arguments of Gauss valuation `≥ K₁`,
`≥ K₂`. This is the blueprint's step-4 digit law
`digAt π (k+k') (x*y) = digAt π k x * digAt π k' y`. -/
theorem resMk_mul (hπ : Irreducible π) {φ : Polynomial O} {K₁ K₂ : ℕ} {a b : Polynomial O}
    (ha : (K₁ : ℕ∞) ≤ gaussVal a) (hb : (K₂ : ℕ∞) ≤ gaussVal b) :
    resMk π φ (K₁ + K₂) (a * b) = resMk π φ K₁ a * resMk π φ K₂ b := by
  obtain ⟨a', ha'⟩ := exists_eq_C_pow_mul hπ ha
  obtain ⟨b', hb'⟩ := exists_eq_C_pow_mul hπ hb
  have hprod : a * b = Polynomial.C (π ^ (K₁ + K₂)) * (a' * b') := by
    rw [ha', hb', pow_add, Polynomial.C_mul]; ring
  rw [resMk, resMk, resMk, digPoly_eq_map hπ ha', digPoly_eq_map hπ hb',
    digPoly_eq_map hπ hprod, Polynomial.map_mul, map_mul]

/-- **`resMk` is additive over a `Finset.sum`** at a common height. -/
theorem resMk_finsetSum (hπ : Irreducible π) {φ : Polynomial O} {K : ℕ} {ι : Type*} (s : Finset ι)
    (F : ι → Polynomial O) (h : ∀ i ∈ s, (K : ℕ∞) ≤ gaussVal (F i)) :
    resMk π φ K (∑ i ∈ s, F i) = ∑ i ∈ s, resMk π φ K (F i) := by
  classical
  induction s using Finset.cons_induction with
  | empty => simpa using resMk_of_zero hπ φ K
  | cons i s hi ih =>
    have hi' : (K : ℕ∞) ≤ gaussVal (F i) := h i (Finset.mem_cons_self _ _)
    have hs : ∀ x ∈ s, (K : ℕ∞) ≤ gaussVal (F x) := fun x hx =>
      h x (Finset.mem_cons_of_mem hx)
    rw [Finset.sum_cons, Finset.sum_cons, resMk_add hπ hi' (le_gaussVal_finsetSum hπ s F hs),
      ih hs]

/-- **`resMk` vanishes above its height**: an argument of Gauss valuation `> K` has no digit at
height `K`. -/
theorem resMk_eq_zero_of_lt (hπ : Irreducible π) {φ : Polynomial O} {K : ℕ} {a : Polynomial O}
    (h : ((K + 1 : ℕ) : ℕ∞) ≤ gaussVal a) : resMk π φ K a = 0 := by
  have hK : (K : ℕ∞) ≤ gaussVal a := le_trans (by exact_mod_cast Nat.le_succ K) h
  rw [resMk, (digPoly_eq_zero_iff hπ hK).2 h, map_zero]

/-- **`resMk` kills the key**: `resMk π φ 0 φ = 0`. -/
theorem resMk_key (hπ : Irreducible π) (φ : Polynomial O) : resMk π φ 0 φ = 0 := by
  rw [resMk, digPoly_eq_map hπ (show φ = Polynomial.C (π ^ 0) * φ by simp)]
  exact AdjoinRoot.mk_self

/-- **`resMk` does not see the `φ`-carry**: reducing mod `φ` first changes nothing. -/
theorem resMk_modByMonic (hπ : Irreducible π) {φ : Polynomial O} (hφ : φ.Monic) {K : ℕ}
    {a : Polynomial O} (h : (K : ℕ∞) ≤ gaussVal a) :
    resMk π φ K (a %ₘ φ) = resMk π φ K a := by
  have hmod : (K : ℕ∞) ≤ gaussVal (a %ₘ φ) := le_trans h (gaussVal_le_modByMonic hπ hφ a)
  have hdiv : (K : ℕ∞) ≤ gaussVal (a /ₘ φ) := le_trans h (gaussVal_le_divByMonic hπ hφ a)
  have h0 : ((0 : ℕ) : ℕ∞) ≤ gaussVal φ := by simp
  have hmul : resMk π φ (0 + K) (φ * (a /ₘ φ)) = resMk π φ 0 φ * resMk π φ K (a /ₘ φ) :=
    resMk_mul hπ h0 hdiv
  rw [resMk_key hπ, zero_mul, Nat.zero_add] at hmul
  have hφmul : (K : ℕ∞) ≤ gaussVal (φ * (a /ₘ φ)) := by
    rw [gaussVal_mul hπ]
    exact le_trans hdiv le_add_self
  have key : resMk π φ K a = resMk π φ K (a %ₘ φ) + resMk π φ K (φ * (a /ₘ φ)) := by
    rw [← resMk_add hπ hmod hφmul, Polynomial.modByMonic_add_div a φ]
  rw [key, hmul, add_zero]

end Uniformity.Density.Leaf

/-! ## Axiom footprint -/

section AxCheck
#print axioms Uniformity.Density.Leaf.dev_of_zero
#print axioms Uniformity.Density.Leaf.dev_mul_pow
#print axioms Uniformity.Density.Leaf.dev_mul_pow_of_lt
#print axioms Uniformity.Density.Leaf.dev_finsetSum
#print axioms Uniformity.Density.Leaf.exists_eq_C_pow_mul
#print axioms Uniformity.Density.Leaf.le_gaussVal_finsetSum
#print axioms Uniformity.Density.Leaf.resMk_of_zero
#print axioms Uniformity.Density.Leaf.resMk_add
#print axioms Uniformity.Density.Leaf.resMk_mul
#print axioms Uniformity.Density.Leaf.resMk_finsetSum
#print axioms Uniformity.Density.Leaf.resMk_eq_zero_of_lt
#print axioms Uniformity.Density.Leaf.resMk_key
#print axioms Uniformity.Density.Leaf.resMk_modByMonic
end AxCheck
