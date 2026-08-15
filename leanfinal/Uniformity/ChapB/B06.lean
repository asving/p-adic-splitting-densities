/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapB.B03

/-!
# Uniformity.ChapB.B06 — uniqueness of the `φ`-adic development

**Chapter B, NODE B.06** [lemma] (`blueprint/CHAP-B_leaf_layer.md` §3, the development /
polygon layer), ENV-A.

The `φ`-adic development of B.02 is *the* development: if `φ` is monic with `0 < deg φ` and
`a : ℕ → O[X]` satisfies `(a j).degree < φ.degree` for every `j` together with
`∑_{j < k} a j * φ ^ j = f`, then `a j = dev φ f j` for every `j < k`. This is what identifies
the corpus's `A_j` with this chapter's `dev φ f j`.

DEPENDS: B.02 (`dev`) · B.03 (`degree_dev_lt`, the companion degree bound — imported for the
DAG, not consumed by the proof below) · mathlib `Polynomial.add_modByMonic`,
`Polynomial.self_mul_modByMonic`, `Polynomial.modByMonic_eq_self_iff`,
`Polynomial.modByMonic_add_div`, `Finset.sum_range_succ'`, `Finset.mul_sum`.

**PROOF.** Induction on `k`, generalising `f` and `a`; at `k = 0` there is no `j < 0`.

At `k + 1`, set `g := ∑_{i < k} a (i+1) * φ ^ i`. Reindexing with `Finset.sum_range_succ'`
(**not** `Finset.sum_range_succ`) and pulling one `φ` out of the tail gives the decomposition
`f = a 0 + φ * g`.

* *The remainder.* `f %ₘ φ = (a 0) %ₘ φ + (φ * g) %ₘ φ` by `add_modByMonic`; the second summand
  is `0` by `self_mul_modByMonic`, and the first is `a 0` by `modByMonic_eq_self_iff` applied to
  `hdeg 0`. So `f %ₘ φ = a 0`, i.e. `a 0 = dev φ f 0` — the `j = 0` clause. (This is the
  remainder-uniqueness clause the blueprint flags as a named risk: at our pin it is available
  as the `add_modByMonic`/`self_mul_modByMonic` pair, so no private helper is needed.)
* *The quotient.* `modByMonic_add_div` reads `f %ₘ φ + φ * (f /ₘ φ) = f = a 0 + φ * g`; with the
  previous point this cancels to `φ * (f /ₘ φ) = φ * g`, and `φ ≠ 0` in the domain `O[X]` gives
  `f /ₘ φ = g`.
* *The reindexing.* For `j + 1 < k + 1` we have `dev φ f (j+1) = dev φ (f /ₘ φ) j = dev φ g j`
  by definition and the previous point, so the induction hypothesis at `g` with the shifted
  family `fun i => a (i+1)` (whose degree bound is `fun i => hdeg (i+1)` and whose sum is `g` by
  definition) closes the goal.

SOURCE: `EFF.W12.23` ("the **UNIQUE** `Φ`-adic development").

## Status

Sorry-free, axiom-free (Lean core only).
-/

namespace Uniformity.Density.Leaf

open Polynomial

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

-- The signed hypothesis `hd : 0 < φ.natDegree` is kept (frozen signature) but is not consumed:
-- monicity of `φ` plus the degree bound `hdeg` already pin the decomposition, the degenerate
-- case `φ = 1` being the one where `hdeg j : (a j).degree < 0` forces every `a j = 0`.
set_option linter.unusedVariables false in
/-- Uniqueness of the `φ`-adic development: any degree-bounded family summing to `f` is the
family of development coefficients of `f`. -/
theorem dev_unique {φ : Polynomial O} (hφ : φ.Monic) (hd : 0 < φ.natDegree)
    {f : Polynomial O} {a : ℕ → Polynomial O} {k : ℕ}
    (hdeg : ∀ j, (a j).degree < φ.degree)
    (hsum : ∑ j ∈ Finset.range k, a j * φ ^ j = f) :
    ∀ j < k, a j = dev φ f j := by
  induction k generalizing f a with
  | zero => intro j hj; exact absurd hj (Nat.not_lt_zero j)
  | succ k ih =>
    set g : Polynomial O := ∑ i ∈ Finset.range k, a (i + 1) * φ ^ i with hgdef
    have hdecomp : f = a 0 + φ * g := by
      rw [← hsum, Finset.sum_range_succ', pow_zero, mul_one, hgdef, Finset.mul_sum, add_comm]
      refine congrArg (a 0 + ·) (Finset.sum_congr rfl fun i _ => ?_)
      rw [pow_succ]; ring
    have h0 : f %ₘ φ = a 0 := by
      rw [hdecomp, add_modByMonic, self_mul_modByMonic hφ, add_zero,
        (modByMonic_eq_self_iff hφ).2 (hdeg 0)]
    have hdiv : f /ₘ φ = g := by
      have hadd : f %ₘ φ + φ * (f /ₘ φ) = f := modByMonic_add_div f φ
      rw [h0] at hadd
      have : φ * (f /ₘ φ) = φ * g := by
        have := hadd.trans hdecomp
        exact add_left_cancel this
      exact mul_left_cancel₀ hφ.ne_zero this
    intro j hj
    match j with
    | 0 => exact h0.symm
    | (i + 1) =>
      have hik : i < k := Nat.lt_of_succ_lt_succ hj
      have hstep : dev φ f (i + 1) = dev φ g i := by
        rw [show dev φ f (i + 1) = dev φ (f /ₘ φ) i from rfl, hdiv]
      rw [hstep]
      exact ih (a := fun t => a (t + 1)) (fun t => hdeg (t + 1)) hgdef.symm i hik

section AxCheck
#print axioms Uniformity.Density.Leaf.dev_unique
end AxCheck

end Uniformity.Density.Leaf
