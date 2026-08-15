/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapB.B32b

/-!
# Uniformity.ChapB.B32c — the representation bound (the contract of NODE B.32)

**Chapter B, NODE B.32, part (c) of the mandated 3-way split**
(`blueprint/CHAP-B_leaf_layer.md` §5), ENV-A′. This file carries the node's single signed
declaration.

*The representation bound (the carry lemma).* For `φ` monic of positive degree, `0 < ℓ`, and
**any** family `c : ℕ → O[X]` — no degree restriction — with
`f = Σ_{t ∈ range K} c t * φ ^ t`,

```
(Finset.range K).inf (fun t => ℓ • gaussVal (c t) + (u * t : ℕ))  ≤  suppVal φ f u ℓ.
```

In words: the canonical `φ`-adic development minimises the weighted infimum among all
`φ`-representations of `f`. Carrying can only raise the weight.

**PROOF (the landed route; see B32a's docstring for why it is not the blueprint's carry
induction).** Three lines, once B32b is in hand:

1. each summand carries at least its own weight —
   `ℓ • gaussVal (c t) + u * t ≤ suppVal φ (c t * φ ^ t) u ℓ` (B32b's
   `weight_le_suppVal_mul_pow`, itself B.31 plus the abscissa shift), so the infimum of the
   weights is below the infimum of the summand values;
2. `suppVal` is ultrametric on finite sums (B32b's `inf_suppVal_le_suppVal_sum`), so that
   infimum is below `suppVal φ (Σ_t c t * φ ^ t) u ℓ`;
3. rewrite by `hc`.

DEPENDS: B.07 (`gaussVal`) · B.14 (`suppVal`) · B32b (`weight_le_suppVal_mul_pow`,
`inf_suppVal_le_suppVal_sum`) · mathlib `Finset.le_inf`, `Finset.inf_le`.

## Faithfulness

`EFF.W12.23` ("monic division gives the UNIQUE `Φ`-adic development") with `EFF.W12.24`'s
right-to-left sweep read as an inequality rather than a count: no re-bracketing of `f` into
`φ`-powers beats the canonical one.

**TEETH.** `W12-BLOCK` (`EFF.W12.55`, 0/1,594,670) stays an executable regression; nothing
here consumes it.

SOURCE: `EFF.W12.23`; `EFF.W12.24`.

## Status

Sorry-free, axiom-free (Lean core only).
-/

namespace Uniformity.Density.Leaf

open Polynomial

-- ENV-A′ (blueprint §0.1): the polynomial arena, plus `hπ : Irreducible π` carried per
-- signature.
variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {π : O}

/-- **B.32 — the representation bound (the carry lemma).** Among all `φ`-representations of
`f`, the canonical development minimises the weighted infimum. -/
theorem inf_weight_le_suppVal (hπ : Irreducible π) {φ : Polynomial O} (hφ : φ.Monic)
    (hd : 0 < φ.natDegree) {ℓ : ℕ} (hℓ : 0 < ℓ) (u : ℕ) {f : Polynomial O}
    {c : ℕ → Polynomial O} {K : ℕ} (hc : ∑ t ∈ Finset.range K, c t * φ ^ t = f) :
    (Finset.range K).inf (fun t => ℓ • gaussVal (c t) + (u * t : ℕ)) ≤ suppVal φ f u ℓ := by
  subst hc
  calc (Finset.range K).inf (fun t => ℓ • gaussVal (c t) + (u * t : ℕ))
      ≤ (Finset.range K).inf (fun t => suppVal φ (c t * φ ^ t) u ℓ) :=
        Finset.le_inf fun t ht =>
          (Finset.inf_le ht).trans (weight_le_suppVal_mul_pow hπ hφ hd hℓ u (c t) t)
    _ ≤ suppVal φ (∑ t ∈ Finset.range K, c t * φ ^ t) u ℓ :=
        inf_suppVal_le_suppVal_sum hφ hd hℓ u (fun t => c t * φ ^ t) K

end Uniformity.Density.Leaf

/-! ## Axiom footprint -/

section AxCheck
#print axioms Uniformity.Density.Leaf.inf_weight_le_suppVal
end AxCheck
