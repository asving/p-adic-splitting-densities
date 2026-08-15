/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

/-!
# Uniformity.ChapH.H63 — the union bound `prod_sub_prod_le_sum`

**Chapter H, NODE H.63** (`blueprint/CHAP-H_general_induction.md` §10, sources `EFF.GENIND.152`
(`GENIND-C1`(ii), leg F) and `EFF.GENIND.170` (`R6.2`, the identity-vs-bound separation)). For a
`Finset` index `s` and reals `0 ≤ u i ≤ T i` on `s`,
`∏_{i∈s} T i − ∏_{i∈s} (T i − u i) ≤ ∑_{i∈s} u i * ∏_{j ∈ s.erase i} T j`.

**No exactness hypothesis.** The bound direction needs only nonnegativity: the corpus's leg F was
checked symbolically at `r = 2, 3`; the induction here is uniform in `#s`, which is what
`GENIND-C1`(iii)'s summation over an arbitrary child family needs. Hypotheses are at their true
minimum — `0 ≤ u i` and `u i ≤ T i` on `s` only, no `0 < T i`, no exactness, no finiteness beyond
`Finset`.

DEPENDS: none · mathlib `Finset.prod_insert`, `Finset.induction_on`, `Finset.sum_insert`,
`Finset.prod_le_prod`, `Finset.prod_nonneg`, `Finset.erase_insert`,
`Finset.erase_insert_of_ne`.

**Split mandate (blueprint SIZE field).** The two monotonicity facts used by the induction step —
`0 ≤ ∏ (T − u)` and `∏ (T − u) ≤ ∏ T` — are landed here as the private helpers
`prod_sub_nonneg_aux` and `prod_sub_le_prod_aux`, per the node's "land them as a separate small
node or as private helpers".

**Parse note (carried from the stub gate).** Mathlib's `∏ x ∈ s, f` body parses at precedence 67
and `-` is `infixl:65`, so `∏ i ∈ s, T i - ∏ i ∈ s, (T i - u i)` DOES split at the subtraction as
intended (the `∑ … , u i * ∏ …` on the right, at `*`'s level 70, does NOT split). No
parenthesization added; recorded because the reading is load-bearing and not obvious.

## Status

Sorry-free, axiom-free (Lean core only).
-/

set_option linter.style.longLine false

namespace Uniformity.Density.Induction

open Finset

/-- Helper (split mandate): a product of nonnegative complements is nonnegative. -/
private theorem prod_sub_nonneg_aux {ι : Type*} (s : Finset ι) (u T : ι → ℝ)
    (huT : ∀ i ∈ s, u i ≤ T i) : 0 ≤ ∏ i ∈ s, (T i - u i) :=
  Finset.prod_nonneg fun i hi => sub_nonneg.2 (huT i hi)

/-- Helper (split mandate): the complement product is dominated by the total product. -/
private theorem prod_sub_le_prod_aux {ι : Type*} (s : Finset ι) (u T : ι → ℝ)
    (hu : ∀ i ∈ s, 0 ≤ u i) (huT : ∀ i ∈ s, u i ≤ T i) :
    ∏ i ∈ s, (T i - u i) ≤ ∏ i ∈ s, T i :=
  Finset.prod_le_prod (fun i hi => sub_nonneg.2 (huT i hi))
    (fun i hi => by linarith [hu i hi])

/-- **The union bound** (`GENIND-C1`(ii), leg F), at every `r`. The composed undecided mass
`∏ T − ∏ (T − u)` is at most the first-order sum `∑ u i · ∏_{j ≠ i} T j`; only `0 ≤ u ≤ T` is
needed, never exactness. -/
theorem prod_sub_prod_le_sum {ι : Type*} [DecidableEq ι] (s : Finset ι) (u T : ι → ℝ)
    (hu : ∀ i ∈ s, 0 ≤ u i) (huT : ∀ i ∈ s, u i ≤ T i) :
    ∏ i ∈ s, T i - ∏ i ∈ s, (T i - u i) ≤ ∑ i ∈ s, u i * ∏ j ∈ s.erase i, T j := by
  revert hu huT
  refine Finset.induction_on s ?_ ?_
  · intro _ _
    simp
  · intro a t ha ih hu huT
    -- Split the hypotheses across `insert a t`.
    have hua : 0 ≤ u a := hu a (Finset.mem_insert_self a t)
    have huaT : u a ≤ T a := huT a (Finset.mem_insert_self a t)
    have hut : ∀ i ∈ t, 0 ≤ u i := fun i hi => hu i (Finset.mem_insert_of_mem hi)
    have huTt : ∀ i ∈ t, u i ≤ T i := fun i hi => huT i (Finset.mem_insert_of_mem hi)
    have ih' := ih hut huTt
    have hTa : (0 : ℝ) ≤ T a := le_trans hua huaT
    have hP' : ∏ i ∈ t, (T i - u i) ≤ ∏ i ∈ t, T i := prod_sub_le_prod_aux t u T hut huTt
    -- Peel the `a` slot off both products and off the sum.
    rw [Finset.prod_insert ha, Finset.prod_insert ha, Finset.sum_insert ha,
      Finset.erase_insert ha]
    -- Every remaining summand gains exactly the factor `T a`.
    have key : ∀ i ∈ t, u i * ∏ j ∈ (insert a t).erase i, T j
        = T a * (u i * ∏ j ∈ t.erase i, T j) := by
      intro i hi
      have hne : a ≠ i := fun h => ha (h ▸ hi)
      have hmem : a ∉ t.erase i := fun h => ha (Finset.mem_of_mem_erase h)
      rw [Finset.erase_insert_of_ne hne, Finset.prod_insert hmem]
      ring
    rw [Finset.sum_congr rfl key, ← Finset.mul_sum]
    -- `T a · (P − P') + u a · P' ≤ T a · S + u a · P`.
    have h1 : T a * (∏ i ∈ t, T i - ∏ i ∈ t, (T i - u i))
        ≤ T a * ∑ i ∈ t, u i * ∏ j ∈ t.erase i, T j :=
      mul_le_mul_of_nonneg_left ih' hTa
    have h2 : u a * ∏ i ∈ t, (T i - u i) ≤ u a * ∏ i ∈ t, T i :=
      mul_le_mul_of_nonneg_left hP' hua
    linarith [h1, h2]

end Uniformity.Density.Induction

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Induction.prod_sub_prod_le_sum

end AxCheck
