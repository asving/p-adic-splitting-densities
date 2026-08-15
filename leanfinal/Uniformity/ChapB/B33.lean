/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapB.B05
import Uniformity.ChapB.B09
import Uniformity.ChapB.B32b

/-!
# Uniformity.ChapB.B33 — the easy half of the product law

**Chapter B, NODE B.33** (`blueprint/CHAP-B_leaf_layer.md` §5), ENV-A′. One signed
declaration.

*The easy half of the product law.* For `φ` monic with `0 < deg φ`, `0 < ℓ`, and any
`f g ∈ O[X]`:

```
suppVal φ f u ℓ + suppVal φ g u ℓ  ≤  suppVal φ (f * g) u ℓ.
```

The cleared support value is **super**additive on products: the `φ`-adic polygon of a product
lies (weakly) above the Minkowski sum of the two polygons. The reverse inequality is *false* in
general — it is exactly what B.35 has to buy, and it is `EFF.HE3.22`'s "generically".

## The landed route

The blueprint's route convolves the two developments into `c t := Σ_{j+i=t} dev φ f j · dev φ g i`
and then invokes B.32's representation bound (`inf_weight_le_suppVal`) on `f * g = Σ_t c t · φ^t`.
The route below **skips the convolution**, and with it the antidiagonal reindexing helper and the
`Finset.sum` extension of the ultrametric bound that the blueprint budgeted (~18 extra lines):
B32b already exports the two facts the convolution was there to produce, so the double sum can be
bounded directly, term by term.

1. `K := f.natDegree + g.natDegree + 2`, so B.05's `sum_dev_eq` applies to both `f` and `g`
   (`natDegree < K ≤ K * φ.natDegree` since `0 < φ.natDegree`), and B32b's `suppVal_eq_inf_range`
   recomputes both `suppVal`s over the *common* range `Finset.range K`.
2. **The term bound.** For `j, i < K`,
   `(dev φ f j · φ^j)·(dev φ g i · φ^i) = (dev φ f j · dev φ g i)·φ^(j+i)`, so B32b's
   `weight_le_suppVal_mul_pow` (no degree restriction on the coefficient — that is its point)
   bounds its `suppVal` below by `ℓ • gaussVal (dev φ f j · dev φ g i) + u·(j+i)`, which by B.09's
   `gaussVal_mul` (Gauss's lemma over a DVR) splits as
   `(ℓ • npHgt φ f j + u·j) + (ℓ • npHgt φ g i + u·i)`, and each bracket is `≥` its own `suppVal`
   by `Finset.inf_le` in the range-`K` form of step 1.
3. **Two sweeps.** B32b's `inf_suppVal_le_suppVal_sum` (the finite-sum ultrametric law) applied
   to the inner sum over `i`, then to the outer sum over `j`, lifts the constant lower bound of
   step 2 through `Finset.sum_mul_sum`'s
   `f * g = Σ_{j<K} Σ_{i<K} (dev φ f j · φ^j)·(dev φ g i · φ^i)`.

Degenerate inputs need no separate case: at `f = 0` both sides are `⊤` (B32b's
`suppVal_zero_eq_top`, and `⊤ + x = ⊤` in `ℕ∞`), and the argument above already produces that.

DEPENDS: B.05 (`sum_dev_eq`) · B.07 (`gaussVal`) · B.09 (`gaussVal_mul`) · B.11 (`npHgt`) ·
B.14 (`suppVal`) · B.32, part (b) (`suppVal_eq_inf_range`, `inf_suppVal_le_suppVal_sum`,
`weight_le_suppVal_mul_pow`) · mathlib `Finset.sum_mul_sum`, `Finset.le_inf`, `Finset.inf_le`.

## Faithfulness

`EFF.HE6.06` (the ultrametric inequality, imported classically there — proved here);
`EFF.HE3.22` (`LEMMA HE3-1′`, whose "generically" is exactly the failure of the reverse
inequality that B.35 must rule out). The corpus writes the statement for the *uncleared*
support function `h_F(u/ℓ) = min_j (dv(A_j) + j·u/ℓ)`; `suppVal` is `ℓ·h_F(u/ℓ)` (B.14), and
multiplying an inequality by the positive integer `ℓ` is faithful.

SOURCE: `EFF.HE6.06`; `EFF.HE3.22`.

**TEETH.** `HE-PSI` (`EFF.HE3.51`, guarding `EFF.HE3.22`) → **Lean theorem**: the inequality
half of `LEMMA HE3-1′` is discharged here (the equality half stays at B.35).

## Status

Sorry-free, axiom-free (Lean core only).
-/

namespace Uniformity.Density.Leaf

open Polynomial

-- ENV-A′ (blueprint §0.1): the polynomial arena, plus `hπ : Irreducible π` carried per
-- signature.
variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {π : O}

/-- **B.33 — the easy half of the product law.** `suppVal` is superadditive on products:
`suppVal φ f u ℓ + suppVal φ g u ℓ ≤ suppVal φ (f * g) u ℓ`. -/
theorem suppVal_add_le_suppVal_mul (hπ : Irreducible π) {φ : Polynomial O} (hφ : φ.Monic)
    (hd : 0 < φ.natDegree) {ℓ : ℕ} (hℓ : 0 < ℓ) (u : ℕ) (f g : Polynomial O) :
    suppVal φ f u ℓ + suppVal φ g u ℓ ≤ suppVal φ (f * g) u ℓ := by
  classical
  -- Step 1: a common range `K` past both degrees.
  set K := f.natDegree + g.natDegree + 2 with hKdef
  have hdf : f.natDegree < K := by omega
  have hdg : g.natDegree < K := by omega
  have hfsum : ∑ j ∈ Finset.range K, dev φ f j * φ ^ j = f :=
    sum_dev_eq hφ hd f (lt_of_lt_of_le hdf (Nat.le_mul_of_pos_right K hd))
  have hgsum : ∑ i ∈ Finset.range K, dev φ g i * φ ^ i = g :=
    sum_dev_eq hφ hd g (lt_of_lt_of_le hdg (Nat.le_mul_of_pos_right K hd))
  have hfinf : suppVal φ f u ℓ
      = (Finset.range K).inf (fun j => ℓ • npHgt φ f j + (u * j : ℕ)) :=
    suppVal_eq_inf_range hφ hd hℓ u f hdf
  have hginf : suppVal φ g u ℓ
      = (Finset.range K).inf (fun i => ℓ • npHgt φ g i + (u * i : ℕ)) :=
    suppVal_eq_inf_range hφ hd hℓ u g hdg
  -- Step 2: the term bound.
  have hterm : ∀ j ∈ Finset.range K, ∀ i ∈ Finset.range K,
      suppVal φ f u ℓ + suppVal φ g u ℓ
        ≤ suppVal φ ((dev φ f j * φ ^ j) * (dev φ g i * φ ^ i)) u ℓ := by
    intro j hj i hi
    have hrw : (dev φ f j * φ ^ j) * (dev φ g i * φ ^ i)
        = (dev φ f j * dev φ g i) * φ ^ (j + i) := by
      rw [pow_add]; ring
    rw [hrw]
    refine le_trans ?_ (weight_le_suppVal_mul_pow hπ hφ hd hℓ u _ (j + i))
    have hf' : suppVal φ f u ℓ ≤ ℓ • gaussVal (dev φ f j) + (u * j : ℕ) := by
      rw [hfinf]; exact Finset.inf_le hj
    have hg' : suppVal φ g u ℓ ≤ ℓ • gaussVal (dev φ g i) + (u * i : ℕ) := by
      rw [hginf]; exact Finset.inf_le hi
    calc suppVal φ f u ℓ + suppVal φ g u ℓ
        ≤ (ℓ • gaussVal (dev φ f j) + (u * j : ℕ))
            + (ℓ • gaussVal (dev φ g i) + (u * i : ℕ)) := add_le_add hf' hg'
      _ = ℓ • gaussVal (dev φ f j * dev φ g i) + (u * (j + i) : ℕ) := by
          rw [gaussVal_mul hπ, smul_add, Nat.mul_add, Nat.cast_add]
          abel
  -- Step 3: the two ultrametric sweeps.
  have hrow : ∀ j ∈ Finset.range K,
      suppVal φ f u ℓ + suppVal φ g u ℓ
        ≤ suppVal φ (∑ i ∈ Finset.range K, (dev φ f j * φ ^ j) * (dev φ g i * φ ^ i)) u ℓ :=
    fun j hj => le_trans (Finset.le_inf fun i hi => hterm j hj i hi)
      (inf_suppVal_le_suppVal_sum hφ hd hℓ u
        (fun i => (dev φ f j * φ ^ j) * (dev φ g i * φ ^ i)) K)
  have hsum : (∑ j ∈ Finset.range K, ∑ i ∈ Finset.range K,
      (dev φ f j * φ ^ j) * (dev φ g i * φ ^ i)) = f * g := by
    rw [← Finset.sum_mul_sum, hfsum, hgsum]
  rw [← hsum]
  exact le_trans (Finset.le_inf hrow)
    (inf_suppVal_le_suppVal_sum hφ hd hℓ u
      (fun j => ∑ i ∈ Finset.range K, (dev φ f j * φ ^ j) * (dev φ g i * φ ^ i)) K)

end Uniformity.Density.Leaf

/-! ## Axiom footprint -/

section AxCheck
#print axioms Uniformity.Density.Leaf.suppVal_add_le_suppVal_mul
end AxCheck
