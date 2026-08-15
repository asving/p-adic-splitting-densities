/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapB.B08

/-!
# Uniformity.ChapB.B09 — `gaussVal` is additive on products (Gauss's lemma)

**Chapter B, NODE B.09** [lemma] (`blueprint/CHAP-B_leaf_layer.md` §3, the development /
polygon layer), ENV-A′ (= ENV-A with `hπ : Irreducible π`, carried in the signature).

The Gauss valuation of B.07 is a valuation: `gaussVal (a * b) = gaussVal a + gaussVal b` for
every pair of polynomials over the DVR `O`. This is what makes the corpus's `(★)` a valuation
and is the engine behind the product law for Newton-polygon heights.

DEPENDS: B.07 (`gaussVal`) · B.08 (`le_gaussVal_iff`, `gaussVal_eq_top_iff`) · landed
`Uniformity.Hensel.pow_dvd_iff_le_addVal` · mathlib `Polynomial.coeff_mul`,
`Finset.mem_antidiagonal`, `Finset.add_sum_erase`, `Finset.dvd_sum`, `ENat.ne_top_iff_exists`,
`IsDiscreteValuationRing.addVal_mul`, `Nat.find`.

**PROOF ROUTE — a deliberate departure from the blueprint's step 4.** The blueprint proves `≤`
by dividing out the content (`a = C (π ^ α) * a'`, then reducing mod `π` into the residue field),
which needs the two private helpers `exists_eq_C_pow_mul` and `gaussVal_C_pow_mul` and — per the
node's SIZE note — would trigger a RE-PLAN request booking `exists_eq_C_pow_mul` as **B.09a**.
That is not done here: the `≤` half is proved by the classical *lowest-unsaturated-coefficient*
argument instead, which needs no content extraction, no residue field, and no new helper beyond
one three-line arithmetic fact about `ℕ∞`. **No RE-PLAN is therefore raised by this node**; a
consumer that genuinely needs `exists_eq_C_pow_mul` (the blueprint names B.28) must book it on
its own account.

The proof proper:

1. If `a = 0` or `b = 0` both sides are `⊤` (B.08's `gaussVal_eq_top_iff`, `top_add`, `add_top`).
2. Otherwise `gaussVal a = (α : ℕ∞)` and `gaussVal b = (β : ℕ∞)` for naturals `α, β`
   (`ENat.ne_top_iff_exists` — **not** `WithTop.ne_top_iff_exists`, whose `↑m` is `WithTop.some`
   and does not match the `Nat.cast` coercion the `norm_cast` lemmas for `ℕ∞` fire on).
   By B.08, `π ^ α` divides every coefficient of `a` and `π ^ β`
   every coefficient of `b`, while `π ^ (α+1)` fails to divide *some* coefficient of `a` and
   `π ^ (β+1)` some coefficient of `b`. Let `i₀`, `j₀` be the **least** such indices (`Nat.find`).
3. `≥`: each coefficient of `a * b` is `∑_{i+j=n} a_i b_j` (`coeff_mul`) and every term is
   divisible by `π ^ α * π ^ β = π ^ (α+β)`; B.08 turns this back into
   `(α + β : ℕ∞) ≤ gaussVal (a * b)`.
4. `≤`: suppose instead `π ^ (α+β+1)` divided every coefficient of `a * b`, and look at index
   `i₀ + j₀`. Every off-diagonal term `a_{x₁} b_{x₂}` with `x₁ + x₂ = i₀ + j₀`, `x ≠ (i₀, j₀)`
   is divisible by `π ^ (α+β+1)`: if `x₁ < i₀` then `π ^ (α+1) ∣ a_{x₁}` by minimality of `i₀`
   and `π ^ β ∣ b_{x₂}`; if `x₁ > i₀` then `x₂ < j₀`, so `π ^ α ∣ a_{x₁}` and
   `π ^ (β+1) ∣ b_{x₂}` by minimality of `j₀`. Subtracting them off,
   `π ^ (α+β+1) ∣ a_{i₀} b_{j₀}`. But the bracket `π ^ α ∣ a_{i₀}`, `¬ π ^ (α+1) ∣ a_{i₀}` pins
   `addVal O a_{i₀} = α` exactly (and likewise `addVal O b_{j₀} = β`), so `addVal_mul` gives
   `α + β + 1 ≤ α + β` — false.
5. Steps 3 and 4 bracket `gaussVal (a * b)` between `α + β` and `α + β + 1` exclusive, which in
   `ℕ∞` forces equality (the private helper `enat_eq_of_le_of_not_le`).

SOURCE: `EFF.HE6.06` (classical import: "resultant symmetry, ultrametric ineq."); the additivity
itself is the corpus's unstated background fact — it is what makes `EFF.HE3.31`'s `(★)` a
valuation.

## Status

Sorry-free, axiom-free (Lean core only).
-/

namespace Uniformity.Density.Leaf

open Polynomial IsDiscreteValuationRing

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {π : O}

/-- An element of `ℕ∞` bracketed between `n` and `n + 1` (exclusive above) is `n`. -/
private theorem enat_eq_of_le_of_not_le {v : ℕ∞} {n : ℕ} (h1 : (n : ℕ∞) ≤ v)
    (h2 : ¬ ((n + 1 : ℕ) : ℕ∞) ≤ v) : v = (n : ℕ∞) := by
  rcases eq_or_ne v ⊤ with rfl | hv
  · exact absurd le_top h2
  · obtain ⟨m, rfl⟩ := ENat.ne_top_iff_exists.1 hv
    have h1' : n ≤ m := by exact_mod_cast h1
    have h2' : ¬ n + 1 ≤ m := fun hc => h2 (by exact_mod_cast hc)
    exact_mod_cast (show m = n by omega)

/-- The Gauss valuation is additive on products: **Gauss's lemma** over a DVR. -/
theorem gaussVal_mul (hπ : Irreducible π) (a b : Polynomial O) :
    gaussVal (a * b) = gaussVal a + gaussVal b := by
  classical
  rcases eq_or_ne a 0 with rfl | ha
  · rw [zero_mul, gaussVal_eq_top_iff.2 rfl, top_add]
  rcases eq_or_ne b 0 with rfl | hb
  · rw [mul_zero, gaussVal_eq_top_iff.2 rfl, add_top]
  -- the two Gauss valuations are finite
  obtain ⟨α, hα⟩ := ENat.ne_top_iff_exists.1 (fun h => ha (gaussVal_eq_top_iff.1 h))
  obtain ⟨β, hβ⟩ := ENat.ne_top_iff_exists.1 (fun h => hb (gaussVal_eq_top_iff.1 h))
  have hadvd : ∀ i, π ^ α ∣ a.coeff i := (le_gaussVal_iff hπ).1 (le_of_eq hα)
  have hbdvd : ∀ i, π ^ β ∣ b.coeff i := (le_gaussVal_iff hπ).1 (le_of_eq hβ)
  -- the lowest coefficient of `a` that `π ^ (α+1)` misses, and its analogue for `b`
  have hexA : ∃ i, ¬ π ^ (α + 1) ∣ a.coeff i := by
    by_contra hc
    rw [not_exists] at hc
    simp only [not_not] at hc
    have hle := (le_gaussVal_iff hπ).2 hc
    rw [← hα] at hle
    have : α + 1 ≤ α := by exact_mod_cast hle
    omega
  have hexB : ∃ j, ¬ π ^ (β + 1) ∣ b.coeff j := by
    by_contra hc
    rw [not_exists] at hc
    simp only [not_not] at hc
    have hle := (le_gaussVal_iff hπ).2 hc
    rw [← hβ] at hle
    have : β + 1 ≤ β := by exact_mod_cast hle
    omega
  obtain ⟨i₀, hi₀, hi₀min⟩ :
      ∃ i, (¬ π ^ (α + 1) ∣ a.coeff i) ∧ ∀ m < i, π ^ (α + 1) ∣ a.coeff m :=
    ⟨Nat.find hexA, Nat.find_spec hexA, fun m hm => not_not.1 (Nat.find_min hexA hm)⟩
  obtain ⟨j₀, hj₀, hj₀min⟩ :
      ∃ j, (¬ π ^ (β + 1) ∣ b.coeff j) ∧ ∀ m < j, π ^ (β + 1) ∣ b.coeff m :=
    ⟨Nat.find hexB, Nat.find_spec hexB, fun m hm => not_not.1 (Nat.find_min hexB hm)⟩
  -- the lower bound
  have hge : ((α + β : ℕ) : ℕ∞) ≤ gaussVal (a * b) := by
    refine (le_gaussVal_iff hπ).2 fun n => ?_
    rw [Polynomial.coeff_mul]
    refine Finset.dvd_sum fun x _ => ?_
    rw [pow_add]
    exact mul_dvd_mul (hadvd x.1) (hbdvd x.2)
  -- the strict upper bound
  have hnot : ¬ ((α + β + 1 : ℕ) : ℕ∞) ≤ gaussVal (a * b) := by
    intro hle
    have hdvd := (le_gaussVal_iff hπ).1 hle (i₀ + j₀)
    rw [Polynomial.coeff_mul] at hdvd
    have hmem : (i₀, j₀) ∈ Finset.antidiagonal (i₀ + j₀) := Finset.mem_antidiagonal.2 rfl
    rw [← Finset.add_sum_erase _ _ hmem] at hdvd
    have hrest : π ^ (α + β + 1) ∣
        ∑ x ∈ (Finset.antidiagonal (i₀ + j₀)).erase (i₀, j₀), a.coeff x.1 * b.coeff x.2 := by
      refine Finset.dvd_sum fun x hx => ?_
      have hxsum : x.1 + x.2 = i₀ + j₀ :=
        Finset.mem_antidiagonal.1 (Finset.mem_of_mem_erase hx)
      have hxne : x ≠ (i₀, j₀) := Finset.ne_of_mem_erase hx
      rcases lt_trichotomy x.1 i₀ with hlt | heq | hgt
      · have hd : π ^ (α + 1) * π ^ β ∣ a.coeff x.1 * b.coeff x.2 :=
          mul_dvd_mul (hi₀min x.1 hlt) (hbdvd x.2)
        rwa [← pow_add, show α + 1 + β = α + β + 1 by omega] at hd
      · exact absurd (Prod.ext heq (by omega)) hxne
      · have hd : π ^ α * π ^ (β + 1) ∣ a.coeff x.1 * b.coeff x.2 :=
          mul_dvd_mul (hadvd x.1) (hj₀min x.2 (by omega))
        rwa [← pow_add, show α + (β + 1) = α + β + 1 by omega] at hd
    have hcore : π ^ (α + β + 1) ∣ a.coeff i₀ * b.coeff j₀ := (dvd_add_left hrest).1 hdvd
    have hva : addVal O (a.coeff i₀) = (α : ℕ∞) :=
      enat_eq_of_le_of_not_le ((Uniformity.Hensel.pow_dvd_iff_le_addVal hπ).1 (hadvd i₀))
        (fun hc => hi₀ ((Uniformity.Hensel.pow_dvd_iff_le_addVal hπ).2 hc))
    have hvb : addVal O (b.coeff j₀) = (β : ℕ∞) :=
      enat_eq_of_le_of_not_le ((Uniformity.Hensel.pow_dvd_iff_le_addVal hπ).1 (hbdvd j₀))
        (fun hc => hj₀ ((Uniformity.Hensel.pow_dvd_iff_le_addVal hπ).2 hc))
    have hfin := (Uniformity.Hensel.pow_dvd_iff_le_addVal hπ).1 hcore
    rw [addVal_mul, hva, hvb, ← Nat.cast_add] at hfin
    have : α + β + 1 ≤ α + β := by exact_mod_cast hfin
    omega
  rw [← hα, ← hβ, ← Nat.cast_add]
  exact enat_eq_of_le_of_not_le hge hnot

section AxCheck
#print axioms Uniformity.Density.Leaf.gaussVal_mul
end AxCheck

end Uniformity.Density.Leaf
