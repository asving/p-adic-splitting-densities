/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapB.B12
import Uniformity.ChapB.B14
import Uniformity.ChapB.B31
import Uniformity.ChapB.B32a

/-!
# Uniformity.ChapB.B32b — the weight monotonicity laws of `suppVal`

**Chapter B, NODE B.32, part (b) of the mandated 3-way split**
(`blueprint/CHAP-B_leaf_layer.md` §5), ENV-A′.

The blueprint's step 2 ("the carry raises the weight") in the form the landed route needs: the
cleared support value `suppVal φ · u ℓ` is a **twisted Gauss valuation**, i.e.

* `min_suppVal_le_suppVal_add` — ultrametric on sums:
  `min (suppVal φ a u ℓ) (suppVal φ b u ℓ) ≤ suppVal φ (a + b) u ℓ`, and its finite-sum form
  `inf_suppVal_le_suppVal_sum`;
* `suppVal_add_le_suppVal_mul_key` — multiplying by the key shifts the polygon right by one
  abscissa, hence adds `u` to the weight: `suppVal φ h u ℓ + u ≤ suppVal φ (h * φ) u ℓ`;
* `weight_le_suppVal_mul_pow` — the two combined at a monomial of the `φ`-adic scale:
  `ℓ • gaussVal c + u * t ≤ suppVal φ (c * φ ^ t) u ℓ`, **with no degree restriction on `c`**.

The last one is the whole point: a representation coefficient `c t` of arbitrary degree still
contributes at least its own weight, which is what makes carrying unnecessary (see B32a's
module docstring for the route note).

Two bookkeeping lemmas support them: `suppVal_eq_inf_range` (the value may be computed over any
range strictly containing the degree — the `suppVal` analogue of B.08's `gaussVal_range`, using
B.12's `npHgt_eq_top_of_lt`), and `suppVal_zero_eq_top`.

DEPENDS: B.11 (`npHgt`) · B.12 (`npHgt_eq_top_of_lt`) · B.14 (`suppVal`) · B.31
(`gaussVal_le_npHgt`) · B32a (`dev_add_of_monic`, `min_gaussVal_le_gaussVal_add`) · mathlib
`Polynomial.self_mul_modByMonic`, `Polynomial.mul_divByMonic_cancel_left`,
`Polynomial.natDegree_mul_le`, `Finset.le_inf`, `Finset.inf_le`, `Finset.inf_insert`.

## Faithfulness

`EFF.W12.24`'s right-to-left sweep read as an inequality: a `φ`-index shift costs exactly `u`
of weight, and superposition of two developments can only raise the polygon.

SOURCE: `EFF.W12.23`; `EFF.W12.24`.

## Status

Sorry-free, axiom-free (Lean core only).
-/

namespace Uniformity.Density.Leaf

open Polynomial IsDiscreteValuationRing

-- ENV-A (blueprint §0.1): the polynomial arena; `hπ : Irreducible π` is carried per signature
-- where B.31 is consumed.
variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {π : O}

/-- With `0 < ℓ`, an empty abscissa (`npHgt = ⊤`) contributes `⊤` to the `suppVal` infimum.
Private helper. -/
private theorem smul_top_add {ℓ : ℕ} (hℓ : 0 < ℓ) (c : ℕ∞) : ℓ • (⊤ : ℕ∞) + c = ⊤ := by
  rw [nsmul_eq_mul, ENat.mul_top (Nat.cast_ne_zero.2 hℓ.ne'), top_add]

/-- **`suppVal` may be computed over any range strictly containing the degree.** Past
`f.natDegree` every abscissa is empty (B.12), so it contributes `ℓ • ⊤ + u * j = ⊤`, which no
infimum can see. The `suppVal` analogue of B.08's `gaussVal_range`. -/
theorem suppVal_eq_inf_range {φ : Polynomial O} (hφ : φ.Monic) (hd : 0 < φ.natDegree)
    {ℓ : ℕ} (hℓ : 0 < ℓ) (u : ℕ) (f : Polynomial O) {M : ℕ} (hM : f.natDegree < M) :
    suppVal φ f u ℓ = (Finset.range M).inf (fun j => ℓ • npHgt φ f j + (u * j : ℕ)) := by
  simp only [suppVal]
  refine le_antisymm (Finset.le_inf fun j _ => ?_) (Finset.le_inf fun j hj => ?_)
  · by_cases h : j < f.natDegree + 1
    · exact Finset.inf_le (Finset.mem_range.2 h)
    · rw [npHgt_eq_top_of_lt hφ hd f (by omega), smul_top_add hℓ]
      exact le_top
  · exact Finset.inf_le (Finset.mem_range.2 (by have := Finset.mem_range.1 hj; omega))

/-- The zero polynomial has empty polygon: `suppVal φ 0 u ℓ = ⊤`. -/
theorem suppVal_zero_eq_top {φ : Polynomial O} {ℓ : ℕ} (hℓ : 0 < ℓ) (u : ℕ) :
    suppVal φ (0 : Polynomial O) u ℓ = ⊤ := by
  have h0 : npHgt φ (0 : Polynomial O) 0 = ⊤ := by
    show gaussVal ((0 : Polynomial O) %ₘ φ) = ⊤
    rw [Polynomial.zero_modByMonic]
    exact gaussVal_eq_top_iff.2 rfl
  simp only [suppVal, Polynomial.natDegree_zero, Nat.zero_add, Finset.range_one,
    Finset.inf_singleton, h0]
  exact smul_top_add hℓ _

/-- **`suppVal` is ultrametric on sums.** The abscissa-by-abscissa reading of B32a's
`dev_add_of_monic` and `min_gaussVal_le_gaussVal_add`. -/
theorem min_suppVal_le_suppVal_add {φ : Polynomial O} (hφ : φ.Monic) (hd : 0 < φ.natDegree)
    {ℓ : ℕ} (hℓ : 0 < ℓ) (u : ℕ) (a b : Polynomial O) :
    min (suppVal φ a u ℓ) (suppVal φ b u ℓ) ≤ suppVal φ (a + b) u ℓ := by
  set M := max (max a.natDegree b.natDegree) (a + b).natDegree + 1 with hMdef
  rw [suppVal_eq_inf_range hφ hd hℓ u a (M := M) (by omega),
    suppVal_eq_inf_range hφ hd hℓ u b (M := M) (by omega),
    suppVal_eq_inf_range hφ hd hℓ u (a + b) (M := M) (by omega)]
  refine Finset.le_inf fun j hj => ?_
  have hmin : min (npHgt φ a j) (npHgt φ b j) ≤ npHgt φ (a + b) j := by
    show min (gaussVal (dev φ a j)) (gaussVal (dev φ b j)) ≤ gaussVal (dev φ (a + b) j)
    rw [dev_add_of_monic hφ]
    exact min_gaussVal_le_gaussVal_add _ _
  rcases le_total (npHgt φ a j) (npHgt φ b j) with h | h
  · rw [min_eq_left h] at hmin
    calc min ((Finset.range M).inf (fun j => ℓ • npHgt φ a j + (u * j : ℕ)))
          ((Finset.range M).inf (fun j => ℓ • npHgt φ b j + (u * j : ℕ)))
        ≤ (Finset.range M).inf (fun j => ℓ • npHgt φ a j + (u * j : ℕ)) := min_le_left _ _
      _ ≤ ℓ • npHgt φ a j + (u * j : ℕ) := Finset.inf_le hj
      _ ≤ ℓ • npHgt φ (a + b) j + (u * j : ℕ) := by gcongr
  · rw [min_eq_right h] at hmin
    calc min ((Finset.range M).inf (fun j => ℓ • npHgt φ a j + (u * j : ℕ)))
          ((Finset.range M).inf (fun j => ℓ • npHgt φ b j + (u * j : ℕ)))
        ≤ (Finset.range M).inf (fun j => ℓ • npHgt φ b j + (u * j : ℕ)) := min_le_right _ _
      _ ≤ ℓ • npHgt φ b j + (u * j : ℕ) := Finset.inf_le hj
      _ ≤ ℓ • npHgt φ (a + b) j + (u * j : ℕ) := by gcongr

/-- **The finite-sum form of the ultrametric law.** -/
theorem inf_suppVal_le_suppVal_sum {φ : Polynomial O} (hφ : φ.Monic) (hd : 0 < φ.natDegree)
    {ℓ : ℕ} (hℓ : 0 < ℓ) (u : ℕ) (F : ℕ → Polynomial O) (K : ℕ) :
    (Finset.range K).inf (fun t => suppVal φ (F t) u ℓ)
      ≤ suppVal φ (∑ t ∈ Finset.range K, F t) u ℓ := by
  induction K with
  | zero => simp [suppVal_zero_eq_top hℓ]
  | succ K ih =>
    rw [Finset.sum_range_succ, Finset.range_add_one, Finset.inf_insert]
    refine le_trans ?_ (min_suppVal_le_suppVal_add hφ hd hℓ u (∑ t ∈ Finset.range K, F t) (F K))
    rw [min_comm]
    exact min_le_min ih le_rfl

/-- **Multiplying by the key shifts the polygon by one abscissa**, so the weight grows by `u`:
`suppVal φ h u ℓ + u ≤ suppVal φ (h * φ) u ℓ`. (An equality holds, but only the `≤` half is
used.) -/
theorem suppVal_add_le_suppVal_mul_key {φ : Polynomial O} (hφ : φ.Monic) (hd : 0 < φ.natDegree)
    {ℓ : ℕ} (hℓ : 0 < ℓ) (u : ℕ) (h : Polynomial O) :
    suppVal φ h u ℓ + (u : ℕ∞) ≤ suppVal φ (h * φ) u ℓ := by
  have hM2 : (h * φ).natDegree < h.natDegree + φ.natDegree + 1 :=
    lt_of_le_of_lt (Polynomial.natDegree_mul_le) (by omega)
  rw [suppVal_eq_inf_range hφ hd hℓ u h (M := h.natDegree + φ.natDegree + 1) (by omega),
    suppVal_eq_inf_range hφ hd hℓ u (h * φ) (M := h.natDegree + φ.natDegree + 1) hM2]
  refine Finset.le_inf fun j hj => ?_
  match j with
  | 0 =>
    have htop : npHgt φ (h * φ) 0 = ⊤ := by
      show gaussVal ((h * φ) %ₘ φ) = ⊤
      rw [mul_comm, Polynomial.self_mul_modByMonic hφ]
      exact gaussVal_eq_top_iff.2 rfl
    rw [htop, smul_top_add hℓ]
    exact le_top
  | (j + 1) =>
    have hshift : npHgt φ (h * φ) (j + 1) = npHgt φ h j := by
      show gaussVal (dev φ ((h * φ) /ₘ φ) j) = gaussVal (dev φ h j)
      rw [mul_comm, Polynomial.mul_divByMonic_cancel_left h hφ]
    have hle : (Finset.range (h.natDegree + φ.natDegree + 1)).inf
        (fun i => ℓ • npHgt φ h i + (u * i : ℕ)) ≤ ℓ • npHgt φ h j + (u * j : ℕ) :=
      Finset.inf_le (Finset.mem_range.2 (by have := Finset.mem_range.1 hj; omega))
    rw [hshift]
    calc (Finset.range (h.natDegree + φ.natDegree + 1)).inf
          (fun i => ℓ • npHgt φ h i + (u * i : ℕ)) + (u : ℕ∞)
        ≤ (ℓ • npHgt φ h j + (u * j : ℕ)) + (u : ℕ∞) := by gcongr
      _ = ℓ • npHgt φ h j + (u * (j + 1) : ℕ) := by
          rw [add_assoc]
          norm_cast

/-- **The weight of a `φ`-adic monomial, with no degree restriction on the coefficient.**
`ℓ • gaussVal c + u * t ≤ suppVal φ (c * φ ^ t) u ℓ`. This is the step the blueprint's carry
induction exists to prove: a coefficient of degree `≥ φ.natDegree` still contributes at least
its own weight at its own abscissa, because B.31 says monic division cannot lower the Gauss
valuation. -/
theorem weight_le_suppVal_mul_pow (hπ : Irreducible π) {φ : Polynomial O} (hφ : φ.Monic)
    (hd : 0 < φ.natDegree) {ℓ : ℕ} (hℓ : 0 < ℓ) (u : ℕ) (c : Polynomial O) (t : ℕ) :
    ℓ • gaussVal c + (u * t : ℕ) ≤ suppVal φ (c * φ ^ t) u ℓ := by
  induction t with
  | zero =>
    simp only [pow_zero, mul_one, Nat.mul_zero, Nat.cast_zero, add_zero, suppVal]
    refine Finset.le_inf fun j _ => ?_
    calc ℓ • gaussVal c ≤ ℓ • npHgt φ c j := by gcongr; exact gaussVal_le_npHgt hπ hφ c j
      _ ≤ ℓ • npHgt φ c j + (u * j : ℕ) := le_self_add
  | succ t ih =>
    calc ℓ • gaussVal c + (u * (t + 1) : ℕ)
        = (ℓ • gaussVal c + (u * t : ℕ)) + (u : ℕ∞) := by
          rw [add_assoc]; norm_cast
      _ ≤ suppVal φ (c * φ ^ t) u ℓ + (u : ℕ∞) := by gcongr
      _ ≤ suppVal φ ((c * φ ^ t) * φ) u ℓ := suppVal_add_le_suppVal_mul_key hφ hd hℓ u _
      _ = suppVal φ (c * φ ^ (t + 1)) u ℓ := by rw [pow_succ, mul_assoc]

end Uniformity.Density.Leaf

/-! ## Axiom footprint -/

section AxCheck
#print axioms Uniformity.Density.Leaf.suppVal_eq_inf_range
#print axioms Uniformity.Density.Leaf.suppVal_zero_eq_top
#print axioms Uniformity.Density.Leaf.min_suppVal_le_suppVal_add
#print axioms Uniformity.Density.Leaf.inf_suppVal_le_suppVal_sum
#print axioms Uniformity.Density.Leaf.suppVal_add_le_suppVal_mul_key
#print axioms Uniformity.Density.Leaf.weight_le_suppVal_mul_pow
end AxCheck
