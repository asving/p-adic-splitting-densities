/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring

/-!
# Uniformity.ChapH.H63w — the EXACT inclusion–exclusion identity behind the mixed drain

**A witness/law file adjacent to NODE H.63, not a blueprint node** (the H09w precedent; landed by
the OM-3 count-layer unit, 2026-08-16).  H.63 (`prod_sub_prod_le_sum`) lands the BOUND direction
of `GENIND-C1`(ii)'s composition — all that chapter H's rate theorems need, per `EFF.GENIND.170`
(R6.2): *"upper bounds propagate by monotonicity + union bound"*.  The IDENTITY direction — the
(CS-EXACT)-side content of `GENIND-6(d)`'s mixed-drain composition, *"inclusion–exclusion prices
it: children's u's exact by (IH) member 4, stage drains exact by (CS-EXACT)"* (`EFF.GENIND.37`) —
was nowhere landed and its corpus support was leg F's `r = 2, 3` symbolic check only.  This file
lands it at every `r`, over any commutative ring:

* `prod_sub_eq_signed_sum` — `∏ (T i − u i) = ∑_{t ⊆ s} (−1)^{|t|} (∏_t u) (∏_{s∖t} T)`;
* `prod_sub_prod_eq_signed_sum` — the drain form: `∏ T − ∏ (T − u)` **equals** the finite signed
  sum `∑_{∅ ≠ t ⊆ s} (−1)^{|t|+1} (∏_t u) (∏_{s∖t} T)` — one exact closed form, a finite sum of
  signed products, which is exactly the *shape* (CS-EXACT) (`EFF.GENIND.66`) demands of a stage
  drain when the `u`'s are exact `q`-power sums.

**FENCE (H.09's RE-PLAN rule respected).** Nothing here adds an `exactDrain` field to
`StageInterface` or discharges (CS-EXACT) for any stage: the theorem is the COMPOSITION identity;
whether a stage's `u_l` are themselves exact `q`-power sums is the per-stage (CS-EXACT) content,
which stays CARRY (ledger HYP.35).  A node needing the exactness identity at the interface must
still return RE-PLAN per H.09's signature note.

DEPENDS: none (mathlib `Finset.prod_add`, `Finset.add_sum_erase`).

## Status

Sorry-free, axiom-free (Lean core only).
-/

set_option linter.style.longLine false

namespace Uniformity.Density.Induction

open Finset

/-- The signed-subset expansion of a product of differences: inclusion–exclusion as an identity,
at every `r`, over any commutative ring. -/
theorem prod_sub_eq_signed_sum {ι R : Type*} [DecidableEq ι] [CommRing R]
    (s : Finset ι) (u T : ι → R) :
    ∏ i ∈ s, (T i - u i)
      = ∑ t ∈ s.powerset, (-1 : R) ^ t.card * (∏ i ∈ t, u i) * ∏ j ∈ s \ t, T j := by
  have h := Finset.prod_add (fun i => -u i) T s
  simp only [neg_add_eq_sub] at h
  rw [h]
  refine Finset.sum_congr rfl fun t _ => ?_
  have hneg : (∏ i ∈ t, -u i) = (-1 : R) ^ t.card * ∏ i ∈ t, u i := by
    calc (∏ i ∈ t, -u i) = ∏ i ∈ t, (-1 : R) * u i := by simp
      _ = (∏ _i ∈ t, (-1 : R)) * ∏ i ∈ t, u i := Finset.prod_mul_distrib
      _ = (-1 : R) ^ t.card * ∏ i ∈ t, u i := by rw [Finset.prod_const]
  rw [hneg]

/-- **The exact mixed-drain composition** (`GENIND-6(d)`'s inclusion–exclusion, the identity the
corpus's leg F checked only at `r = 2, 3`): the composed drain `∏ T − ∏ (T − u)` IS the finite
signed sum over nonempty child subsets — an exact closed form, not a bound. -/
theorem prod_sub_prod_eq_signed_sum {ι R : Type*} [DecidableEq ι] [CommRing R]
    (s : Finset ι) (u T : ι → R) :
    ∏ i ∈ s, T i - ∏ i ∈ s, (T i - u i)
      = ∑ t ∈ s.powerset.erase ∅, (-1 : R) ^ (t.card + 1) * (∏ i ∈ t, u i) * ∏ j ∈ s \ t, T j := by
  have h := prod_sub_eq_signed_sum s u T
  have h0 : (∅ : Finset ι) ∈ s.powerset := Finset.empty_mem_powerset s
  rw [← Finset.add_sum_erase _ _ h0] at h
  simp only [Finset.card_empty, pow_zero, Finset.prod_empty, one_mul, Finset.sdiff_empty] at h
  rw [h]
  have hflip : ∀ t ∈ s.powerset.erase ∅,
      (-1 : R) ^ (t.card + 1) * (∏ i ∈ t, u i) * ∏ j ∈ s \ t, T j
        = -((-1 : R) ^ t.card * (∏ i ∈ t, u i) * ∏ j ∈ s \ t, T j) := by
    intro t _
    ring
  rw [Finset.sum_congr rfl hflip]
  rw [Finset.sum_neg_distrib]
  ring

end Uniformity.Density.Induction

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Induction.prod_sub_eq_signed_sum
#print axioms Uniformity.Density.Induction.prod_sub_prod_eq_signed_sum

end AxCheck
