/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G, Codex 5.6
-/
import Uniformity.ChapC.C128

/-!
# Uniformity.ChapC.C128b1 — C.128 (B1): wrap seeds and weight calculus

This module transcribes the fully specified algebraic and arithmetic pieces of §§2–3 of
`LAWBS2_PROOF_2026-08-16.md` using the vocabulary landed in `Uniformity.ChapC.C128`.

## BLOCKED boundary

The note prints an exact finite wrap-seed sum `T̂` only for the binomial subclass `κ₁ = 0`.
For the signed non-binomial scope it says only that every `κ₁`-branch consumes one `x`-power,
does not produce a `Φ′`, and raises weight.  It does not specify the branch index set,
multiplicities, signs, or monomials needed to state the promised identity
`Δ_j = red (R_j(T̂))` in Lean.  `C128.lean` likewise lands the three low-power dictionary rows,
not a general iterated non-binomial wrap formula.  Per the transcription fence, this file does
not invent that missing formula.

Landed here: the exact multinomial expansion, the displayed seed-weight calculation, its floor
and depth-one consequences, and the complete arithmetic top-band filter.  The generic
non-binomial seed identity and therefore LEMMA 3(b)–(d) on the actual shadow carrier remain
blocked on a precise source statement.
-/

namespace Uniformity.Density.Tower

open Uniformity.Density.Leaf Polynomial

/-! ## The multinomial wrap source (§2) -/

section Multinomial

variable {R : Type*} [CommRing R]

/-- The three summands of `K = Y² + P Y + c₀`, indexed in the order `(k,l,r)` used in the
proof note. -/
noncomputable def triSummand (P c0 : R) : Fin 3 → Polynomial R
  | 0 => Polynomial.X ^ 2
  | 1 => Polynomial.C P * Polynomial.X
  | 2 => Polynomial.C c0

/-- The `(k,l,r)` term in the multinomial expansion of the degree-two trinomial key.  Using a
`Fin 3 → ℕ` exponent vector keeps the side condition `k+l+r=μ` in mathlib's
`Finset.piAntidiag` rather than encoding it with truncated subtraction. -/
noncomputable def triMultiTerm (P c0 : R) (d : Fin 3 → ℕ) : Polynomial R :=
  (Nat.multinomial Finset.univ d : Polynomial R) *
    ∏ i : Fin 3, triSummand P c0 i ^ d i

/-- **§2, multinomial expansion.**

`K^μ = Σ_{k+l+r=μ} C(μ;k,l,r) P^l c₀^r Y^(2k+l)`.
The right side is deliberately stored in product form: subsequent wrap lemmas can select the
`l`-coordinate without first normalizing a large polynomial expression. -/
theorem triKey_pow_eq_sum_triMultiTerm (P c0 : R) (μ : ℕ) :
    triKey P c0 ^ μ =
      ∑ d ∈ Finset.piAntidiag (Finset.univ : Finset (Fin 3)) μ, triMultiTerm P c0 d := by
  rw [show triKey P c0 = ∑ i ∈ (Finset.univ : Finset (Fin 3)), triSummand P c0 i by
    simp [triKey, triSummand, Fin.sum_univ_three]]
  rw [Finset.sum_pow_eq_sum_piAntidiag]
  simp only [triMultiTerm]

/-- The product-form multinomial term is the monomial printed in §2. -/
theorem triMultiTerm_eq (P c0 : R) (d : Fin 3 → ℕ) :
    triMultiTerm P c0 d =
      Polynomial.C (Nat.multinomial Finset.univ d : R) *
        Polynomial.C (P ^ d 1 * c0 ^ d 2) * Polynomial.X ^ (2 * d 0 + d 1) := by
  simp [triMultiTerm, triSummand, Fin.prod_univ_succ]
  rw [show (Nat.multinomial Finset.univ d : Polynomial R) =
      Polynomial.C (Nat.multinomial Finset.univ d : R) by simp]
  ring

end Multinomial

/-! ## The numerical weight carried by a wrap seed (§3) -/

/-- Weight of the depth-`j` wrap seed born from a `(k,l,r)` multinomial term, after writing
`l = 2w+ρ`.  The final argument is the valuation of the integer coefficient; unit factors have
already been discarded. -/
def wrapSeedWeight (h u₂ v₂ v₀ k l r w ρ j ν : ℕ) : ℕ :=
  2 * (l * v₂ + r * v₀ + h * (w - j) + ν) + ρ * h + (2 * k + l + j) * u₂

/-- **LEMMA 3, wrap-depth calculation.**  A depth-`j` seed has weight
`μE₂ + jδ + 2ν`, where `E₂=2u₂` and `δ=u₂-2h`.  This is the displayed calculation in §3,
including its two uses of the on-side equations. -/
theorem wrapSeedWeight_eq_layer {h u₂ v₂ v₀ μ k l r w ρ j ν : ℕ}
    (hu : u₂ = 2 * v₂ + h) (hv₀ : v₀ = u₂) (hμ : k + l + r = μ)
    (hl : l = 2 * w + ρ) (hj : j ≤ w) (hmargin : 2 * h ≤ u₂) :
    wrapSeedWeight h u₂ v₂ v₀ k l r w ρ j ν =
      μ * (2 * u₂) + j * (u₂ - 2 * h) + 2 * ν := by
  have hZ : ((wrapSeedWeight h u₂ v₂ v₀ k l r w ρ j ν : ℕ) : ℤ) =
      ((μ * (2 * u₂) + j * (u₂ - 2 * h) + 2 * ν : ℕ) : ℤ) := by
    simp only [wrapSeedWeight]
    push_cast [Nat.cast_sub hj, Nat.cast_sub hmargin]
    have A : (u₂ : ℤ) = 2 * v₂ + h := by exact_mod_cast hu
    have B : (v₀ : ℤ) = u₂ := by exact_mod_cast hv₀
    have C : (k : ℤ) + l + r = μ := by exact_mod_cast hμ
    have D : (l : ℤ) = 2 * w + ρ := by exact_mod_cast hl
    nlinarith
  exact_mod_cast hZ

/-- The seed weight is at least its depth layer; this is the inequality used by the floor
argument after forgetting the nonnegative valuation of the integer coefficient. -/
theorem wrapSeedWeight_ge_layer {h u₂ v₂ v₀ μ k l r w ρ j ν : ℕ}
    (hu : u₂ = 2 * v₂ + h) (hv₀ : v₀ = u₂) (hμ : k + l + r = μ)
    (hl : l = 2 * w + ρ) (hj : j ≤ w) (hmargin : 2 * h ≤ u₂) :
    μ * (2 * u₂) + j * (u₂ - 2 * h) ≤ wrapSeedWeight h u₂ v₂ v₀ k l r w ρ j ν := by
  rw [wrapSeedWeight_eq_layer hu hv₀ hμ hl hj hmargin]
  omega

/-- **The `Θ`-layer is depth one only.**  If a positive-depth seed attains the first wrap
layer, then its depth is exactly one and its integer coefficient has valuation zero. -/
theorem eq_first_layer_iff {μ E δ j ν : ℕ} (hδ : 1 ≤ δ) (hj : 1 ≤ j) :
    μ * E + j * δ + 2 * ν = μ * E + δ ↔ j = 1 ∧ ν = 0 := by
  constructor
  · intro h
    have hjv : j * δ + 2 * ν = δ := by omega
    have hjone : j = 1 := by
      by_contra hne
      have hjtwo : 2 ≤ j := by omega
      have hmul : 2 * δ ≤ j * δ := Nat.mul_le_mul_right δ hjtwo
      omega
    refine ⟨hjone, ?_⟩
    rw [hjone, one_mul] at hjv
    omega
  · rintro ⟨rfl, rfl⟩
    simp

/-- Numerical form of the floor propagation in LEMMA 3(b): removing `q` key weights from a
seed at or above `μE+δ` leaves it at or above `(μ-q)E+δ`. -/
theorem chain_floor_arithmetic {μ q E δ W : ℕ} (hq : q ≤ μ) (hW : μ * E + δ ≤ W) :
    (μ - q) * E + δ ≤ W - q * E := by
  have hqe : q * E ≤ μ * E := Nat.mul_le_mul_right E hq
  have hqeW : q * E ≤ W := le_trans hqe (le_trans (Nat.le_add_right _ _) hW)
  have hsplitμ : (μ - q) * E + q * E = μ * E := by
    calc
      (μ - q) * E + q * E = (μ - q + q) * E := by ring
      _ = μ * E := by rw [Nat.sub_add_cancel hq]
  have hsplitW : W - q * E + q * E = W := Nat.sub_add_cancel hqeW
  omega

/-- **§4's arithmetic filter, prepared in B1.**  If an over-grid seed can reach chain
coordinate `μ-1`, then it has no `c₀` factor and is exactly the pair, triple, or quad branch.
This is the comparison `j ≥ l+2r-2` against `j ≤ ⌊l/2⌋`, expressed without division by the
decomposition `l=2w+ρ`, `ρ<2`. -/
theorem topSeed_pair_triple_or_quad {μ k l r w ρ j : ℕ}
    (hμ₂ : 2 ≤ μ) (hsum : k + l + r = μ) (hover : 2 ≤ l)
    (hl : l = 2 * w + ρ) (hρ : ρ < 2) (hjpos : 1 ≤ j) (hjw : j ≤ w)
    (hreaches : 2 * μ - 2 ≤ 2 * k + l + j) :
    r = 0 ∧
      ((l = 2 ∧ w = 1 ∧ ρ = 0 ∧ j = 1) ∨
       (l = 3 ∧ w = 1 ∧ ρ = 1 ∧ j = 1) ∨
       (l = 4 ∧ w = 2 ∧ ρ = 0 ∧ j = 2)) := by
  omega

end Uniformity.Density.Tower

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Tower.triSummand
#print axioms Uniformity.Density.Tower.triMultiTerm
#print axioms Uniformity.Density.Tower.triKey_pow_eq_sum_triMultiTerm
#print axioms Uniformity.Density.Tower.triMultiTerm_eq
#print axioms Uniformity.Density.Tower.wrapSeedWeight
#print axioms Uniformity.Density.Tower.wrapSeedWeight_eq_layer
#print axioms Uniformity.Density.Tower.wrapSeedWeight_ge_layer
#print axioms Uniformity.Density.Tower.eq_first_layer_iff
#print axioms Uniformity.Density.Tower.chain_floor_arithmetic
#print axioms Uniformity.Density.Tower.topSeed_pair_triple_or_quad

end AxCheck
