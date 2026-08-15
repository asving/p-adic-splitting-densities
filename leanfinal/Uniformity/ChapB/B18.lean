/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapB.B13b
import Uniformity.ChapB.B16

/-!
# Uniformity.ChapB.B18 — the support value is attained, and finite

**Chapter B, NODE B.18** [lemma] (`blueprint/CHAP-B_leaf_layer.md` §3, the development /
polygon layer), ENV-A.

*The support value is attained, and its finiteness criterion.*  Let `φ` be monic with
`0 < deg φ` and let `f` be monic with `f.natDegree = μ * φ.natDegree`.  Then

* `suppVal φ f u ℓ ≤ (u * μ : ℕ)` for every `u ℓ` — in particular `suppVal φ f u ℓ ≠ ⊤`;
* the `inf` defining `suppVal` is attained, so `sideSet φ f u ℓ` is nonempty.

The finiteness is exactly the corpus's *"`A_μ = 1`"*: the top coefficient of the `φ`-adic
development of a monic `f` of degree `μ·m` is `1`, so the polygon has an honest terminal
point `(μ, 0)` (B.13b's `npHgt_top`) and the `inf` cannot run away to `⊤`.  Every later node
that needs `suppVal φ f u ℓ ≠ ⊤` — B.17's spacing, B.19's vertex property, B.20's endpoints —
gets it here; B.30's *"three `Nonempty` witnesses `hf' hg' hfg'`"* are `sideSet_nonempty`.

Two declarations, as signed.

DEPENDS: B.13b (`npHgt_top`) · B.14 (`suppVal`) · B.16 (`OnSide`, `sideSet`) · mathlib
`Finset.inf_le`, `Finset.exists_mem_eq_inf`, `Nat.le_mul_of_pos_right`.

**PROOF.**
1. `suppVal_ne_top`: `μ ≤ f.natDegree` when `0 < φ.natDegree` (from `hdeg`, by
   `Nat.le_mul_of_pos_right`), so `μ ∈ Finset.range (f.natDegree + 1)`; `Finset.inf_le` at
   `j = μ` gives `suppVal ≤ ℓ • npHgt φ f μ + u*μ = ℓ • 0 + u*μ = u*μ` by B.13b's `npHgt_top`.
2. `sideSet_nonempty`: `Finset.range (f.natDegree + 1)` is nonempty, so by
   `Finset.exists_mem_eq_inf` the `inf` is attained at some `j` in it; that `j` satisfies
   `OnSide` by definition and hence lies in the filter.  (Step 2 is where `hφ hd hf hdeg` are
   *not* consumed — attainment of an `inf` over a nonempty range is unconditional — but the
   signature is signed and frozen, so the hypotheses stay; they are what makes the
   accompanying `suppVal_ne_top` true, and every call site holds them already.)

SOURCE: `EFF.HE3.13` (`A_μ = 1` is what makes the polygon's right end finite);
`EFF.HE6.30`(a) (the length argument `Σ_λ L_λ = μ`, whose premise is this finiteness).

TEETH: signed non-applicable.

## Status

Sorry-free, axiom-free (Lean core only).
-/

namespace Uniformity.Density.Leaf

open Polynomial

-- ENV-A (blueprint §0.1): the polynomial arena.
variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

/-- **B.18 (a) — the support value is finite, with an explicit bound.**  For `φ` monic of
positive degree and `f` monic of degree `μ * φ.natDegree`, the cleared support value at any
slope `−u/ℓ` is at most `u * μ`: the polygon's terminal point `(μ, 0)` already witnesses it. -/
theorem suppVal_ne_top {φ : Polynomial O} (hφ : φ.Monic) (hd : 0 < φ.natDegree)
    {f : Polynomial O} (hf : f.Monic) {μ : ℕ} (hdeg : f.natDegree = μ * φ.natDegree) (u ℓ : ℕ) :
    suppVal φ f u ℓ ≤ ((u * μ : ℕ) : ℕ∞) := by
  have hmem : μ ∈ Finset.range (f.natDegree + 1) := by
    rw [Finset.mem_range, hdeg]
    exact Nat.lt_succ_of_le (Nat.le_mul_of_pos_right μ hd)
  refine le_trans (Finset.inf_le (f := fun j => ℓ • npHgt φ f j + ((u * j : ℕ) : ℕ∞)) hmem) ?_
  rw [npHgt_top hφ hd hf hdeg]
  simp

-- The four signed hypotheses `hφ hd hf hdeg` are kept (frozen signature) but are not consumed:
-- attainment of an `inf` over the nonempty range `Finset.range (f.natDegree + 1)` is
-- unconditional.  They are what makes the companion `suppVal_ne_top` true, and B.20/B.30 —
-- which need both halves at once — hold them anyway.
set_option linter.unusedVariables false in
/-- **B.18 (b) — the side is nonempty.**  The `inf` defining `suppVal` is taken over the
nonempty range `Finset.range (f.natDegree + 1)`, hence attained; an abscissa attaining it is
on the `(u,ℓ)`-side by definition. -/
theorem sideSet_nonempty {φ : Polynomial O} (hφ : φ.Monic) (hd : 0 < φ.natDegree)
    {f : Polynomial O} (hf : f.Monic) {μ : ℕ} (hdeg : f.natDegree = μ * φ.natDegree) (u ℓ : ℕ) :
    (sideSet φ f u ℓ).Nonempty := by
  classical
  obtain ⟨j, hjmem, hjeq⟩ :=
    Finset.exists_mem_eq_inf (Finset.range (f.natDegree + 1)) Finset.nonempty_range_add_one
      (fun j => ℓ • npHgt φ f j + ((u * j : ℕ) : ℕ∞))
  refine ⟨j, ?_⟩
  have honside : OnSide φ f u ℓ j := hjeq.symm
  simpa [sideSet, Finset.mem_filter, hjmem] using honside

section AxCheck
#print axioms Uniformity.Density.Leaf.suppVal_ne_top
#print axioms Uniformity.Density.Leaf.sideSet_nonempty
end AxCheck

end Uniformity.Density.Leaf
