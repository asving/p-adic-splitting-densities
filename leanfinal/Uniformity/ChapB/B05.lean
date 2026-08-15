/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapB.B04

/-!
# Uniformity.ChapB.B05 — the `φ`-adic development sums back to `f`

**Chapter B, NODE B.05** [lemma] (`blueprint/CHAP-B_leaf_layer.md` §3, the development /
polygon layer), ENV-A.

For monic `φ` with `0 < deg φ`, any `f`, and any `k` with `f.natDegree < k * φ.natDegree`,
`∑ j ∈ Finset.range k, dev φ f j * φ ^ j = f`. Together with B.06 (uniqueness) this says
`dev` is *the* `φ`-adic development: the truncation at `k` is exact as soon as `k` is past
the degree.

DEPENDS: B.02 (`dev`) · B.04 (`dev_eq_zero_of_lt`) · mathlib
`Polynomial.modByMonic_add_div`, `Polynomial.modByMonic_eq_self_iff`,
`Polynomial.natDegree_divByMonic`, `Finset.sum_range_succ'`, `Finset.sum_mul`.

**PROOF.** Induction on `k`, generalising `f`.

* `k = 0`: the hypothesis reads `f.natDegree < 0`, impossible.
* `k + 1`: `Finset.sum_range_succ'` splits the sum as
  `(∑ j ∈ range k, dev φ f (j+1) * φ^(j+1)) + dev φ f 0 * φ^0`. Since
  `dev φ f (j+1) = dev φ (f /ₘ φ) j` by `rfl` and `φ^(j+1) = φ^j * φ`, the tail is
  `(∑ j ∈ range k, dev φ (f /ₘ φ) j * φ^j) * φ` after `Finset.sum_mul`; the head is
  `f %ₘ φ`. Now split on whether `f` reaches the degree of `φ`:
  * `f.natDegree < φ.natDegree`: every tail term vanishes by B.04
    (`f.natDegree < φ.natDegree ≤ (j+1) * φ.natDegree`), and
    `f %ₘ φ = f` by `modByMonic_eq_self_iff hφ` (through `degree_lt_degree`).
  * `φ.natDegree ≤ f.natDegree`: the induction hypothesis at `f /ₘ φ` applies — its degree
    is `f.natDegree - φ.natDegree < k * φ.natDegree` by `omega` from `Nat.succ_mul` — so the
    tail is `(f /ₘ φ) * φ` and `modByMonic_add_div f φ : f %ₘ φ + φ * (f /ₘ φ) = f` closes
    (in the pinned mathlib this identity is unconditional — the non-monic branch is
    `p %ₘ q = p`, `p /ₘ q = 0` — so `hφ` is not needed at this last step).

SOURCE: `EFF.W12.23`; `EFF.HE3.13`; `EFF.HE6.10`.

TEETH: `W12-BLOCK` (`EFF.W12.55`, 0/1,594,670 — "Hensel product identity `g·l == f`"; the
development identity is the same shape of check at the branch level) → **Lean theorem**: this
node is that identity, proved at general `O`.

## Status

Sorry-free, axiom-free (Lean core only).
-/

namespace Uniformity.Density.Leaf

open Polynomial

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

-- The signed hypothesis `hd : 0 < φ.natDegree` is kept (frozen signature) but is not
-- consumed: the induction only needs `hφ` plus `Nat` arithmetic, and at `φ.natDegree = 0` the
-- statement is vacuous anyway (`f.natDegree < k * 0 = 0` is false).
set_option linter.unusedVariables false in
/-- The `φ`-adic development sums back to `f`: for `k` past the degree,
`∑ j < k, dev φ f j * φ ^ j = f`. -/
theorem sum_dev_eq {φ : Polynomial O} (hφ : φ.Monic) (hd : 0 < φ.natDegree) (f : Polynomial O)
    {k : ℕ} (hk : f.natDegree < k * φ.natDegree) :
    ∑ j ∈ Finset.range k, dev φ f j * φ ^ j = f := by
  induction k generalizing f with
  | zero => simp at hk
  | succ k ih =>
    rw [Finset.sum_range_succ']
    have htail : ∀ j : ℕ, dev φ f (j + 1) * φ ^ (j + 1)
        = (dev φ (f /ₘ φ) j * φ ^ j) * φ := by
      intro j
      rw [show dev φ f (j + 1) = dev φ (f /ₘ φ) j from rfl, pow_succ]
      ring
    rw [Finset.sum_congr rfl (fun j _ => htail j), ← Finset.sum_mul]
    have hhead : dev φ f 0 * φ ^ 0 = f %ₘ φ := by
      rw [show dev φ f 0 = f %ₘ φ from rfl, pow_zero, mul_one]
    rw [hhead]
    by_cases hlt : f.natDegree < φ.natDegree
    · have hzero : ∀ j ∈ Finset.range k, dev φ (f /ₘ φ) j * φ ^ j = 0 := by
        intro j _
        rw [show dev φ (f /ₘ φ) j = dev φ f (j + 1) from rfl,
          dev_eq_zero_of_lt hφ hd f (j + 1) (by nlinarith [Nat.succ_le_succ (Nat.zero_le j)]),
          zero_mul]
      rw [Finset.sum_congr rfl hzero, Finset.sum_const_zero, zero_mul, zero_add,
        (modByMonic_eq_self_iff hφ).2 (degree_lt_degree hlt)]
    · have hdeg : (f /ₘ φ).natDegree < k * φ.natDegree := by
        rw [natDegree_divByMonic f hφ]
        rw [Nat.succ_mul] at hk
        omega
      rw [ih (f /ₘ φ) hdeg]
      linear_combination modByMonic_add_div f φ

section AxCheck
#print axioms Uniformity.Density.Leaf.sum_dev_eq
end AxCheck

end Uniformity.Density.Leaf
