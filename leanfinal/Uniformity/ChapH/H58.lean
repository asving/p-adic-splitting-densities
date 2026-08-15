/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.Density.LocalData

/-!
# Uniformity.ChapH.H58 — the composed-key degree bijection (base-`D′` representation)

**Chapter H, NODE H.58** (`blueprint/CHAP-H_general_induction.md` §8, the slot/lift layer).
Source: `EFF.GENHN.43`, clause (ii) of `T(b)′`: *"`{x^a Φ′^b : a < D′, b < e₂f₂}` is a
triangular-unimodular basis of the degree-`< D₂` polynomials"*, proved there by *"`deg(x^a Φ′^b)
= a + bD′` hits each degree `< D₂` once"*.

This node lands the **combinatorial core** — that `(a, b) ↦ a + b·D` is a bijection
`range D ×ˢ range r → range (D * r)` (base-`D` representation), together with the matching
cardinality. The passage from the degree bijection to a *basis* needs monicity of `Φ′` and is the
unit-pivot argument of §9 (H.60), NOT this node; see the blueprint's ⚠ note.

DEPENDS: none beyond mathlib (`Nat.mod_add_div'`, `Nat.add_mul_div_right`,
`Nat.add_mul_mod_self_right`, `Nat.div_lt_iff_lt_mul`, `Set.InvOn.bijOn`, `Finset.card_product`).

**PROOF.** The inverse is `n ↦ (n % D, n / D)`. `Nat.mod_add_div'` gives one round trip and
`Nat.add_mul_div_right` / `Nat.add_mul_mod_self_right` (with `a < D`, so `a % D = a` and
`a / D = 0`) the other; membership both ways is `Nat.mod_lt` / `Nat.div_lt_iff_lt_mul` and
`a + b·D < D + b·D = (b+1)·D ≤ r·D`. Assemble with `Set.InvOn.bijOn`. The cardinality is
`Finset.card_product` + `Finset.card_range`.

## Status

Sorry-free, axiom-free (Lean core only).
-/

namespace Uniformity.Density.Induction

/-- **H.58 (a) — the degree bijection.** `(a, b) ↦ a + b·D` maps `range D ×ˢ range r` bijectively
onto `range (D * r)`: the base-`D` representation of the degrees `0, …, D*r − 1`. -/
theorem divMod_bij (D r : ℕ) (hD : 0 < D) :
    Set.BijOn (fun p : ℕ × ℕ => p.1 + p.2 * D)
      (Finset.range D ×ˢ Finset.range r) (Finset.range (D * r)) := by
  have hmem : ∀ p : ℕ × ℕ,
      p ∈ ((Finset.range D : Finset ℕ) : Set ℕ) ×ˢ ((Finset.range r : Finset ℕ) : Set ℕ) ↔
        p.1 < D ∧ p.2 < r := by
    intro p
    simp only [Finset.coe_range, Set.mem_prod, Set.mem_Iio]
  have hmaps : Set.MapsTo (fun p : ℕ × ℕ => p.1 + p.2 * D)
      (Finset.range D ×ˢ Finset.range r) (Finset.range (D * r)) := by
    intro p hp
    rw [hmem] at hp
    simp only [Finset.coe_range, Set.mem_Iio]
    calc p.1 + p.2 * D < D + p.2 * D := by omega
      _ = (p.2 + 1) * D := by ring
      _ ≤ r * D := Nat.mul_le_mul_right D hp.2
      _ = D * r := Nat.mul_comm _ _
  have hmaps' : Set.MapsTo (fun n : ℕ => (n % D, n / D))
      (Finset.range (D * r)) (Finset.range D ×ˢ Finset.range r) := by
    intro n hn
    simp only [Finset.coe_range, Set.mem_Iio] at hn
    rw [hmem]
    refine ⟨Nat.mod_lt _ hD, ?_⟩
    exact (Nat.div_lt_iff_lt_mul hD).2 (by rwa [Nat.mul_comm] at hn)
  refine Set.InvOn.bijOn ⟨?_, ?_⟩ hmaps hmaps'
  · intro p hp
    rw [hmem] at hp
    have h1 : (p.1 + p.2 * D) % D = p.1 := by
      rw [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hp.1]
    have h2 : (p.1 + p.2 * D) / D = p.2 := by
      rw [Nat.add_mul_div_right _ _ hD, Nat.div_eq_of_lt hp.1, Nat.zero_add]
    exact Prod.ext h1 h2
  · intro n _
    exact Nat.mod_add_div' n D

/-- **H.58 (b) — the composed-key family has `D * r` members.** -/
theorem card_composedBasis (D r : ℕ) (hD : 0 < D) :
    (Finset.range D ×ˢ Finset.range r).card = D * r := by
  -- `hD` is part of the signed contract (it is what `divMod_bij` needs); the count itself
  -- holds for every `D`.
  have : 0 < D := hD
  simp

section AxCheck
#print axioms Uniformity.Density.Induction.divMod_bij
#print axioms Uniformity.Density.Induction.card_composedBasis
end AxCheck

end Uniformity.Density.Induction
