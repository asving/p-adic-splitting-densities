/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.OM.RealInstanceV2
import LeanUrat.OM.OMCountV2
import LeanUrat.OM.Order0Alpha

/-!
# OM/RealInstanceV2Gates — the W3 machine-checked gates (G1 non-vacuity, G2 σ-separation)

This module is **Wave 3 of `notes/M9_REBASE_BLUEPRINT_2026-07-19.md`** (§4-W3): the mandatory
machine-checked gates pinned to the CORRECTED real V2 instance's own density
`g_σ(q') := ∑_{T ∈ omMenu n σ} omCount T q'` — the exact sum appearing in the conclusion of the
W2 capstone `RealInstanceV2.montes_unconditional` (named `montes_unconditional_v2` until the W4a
swap, 2026-07-21).

* **G1 (V1 reversal — non-vacuity at the capstone's own density).** At `n = 2`, the INERT type
  `unramType 2 (indiscrete 2)`, and the real prime `realP = 2`, the capstone's menu-sum density
  is EXACTLY `1/4` (`gate_v2_value_inert2`) and hence strictly positive (`gate_v2_nonvacuous`).
  Bonus pin to the instance: the genuine DECIDED-LIMIT density of `realM2` at the inert type is
  `1/4` too (`gate_v2_countingDensity_inert2`, via `realD2`'s decomposition theorem) — the gate
  is against the REAL instance, not the free interface (blueprint D2 mitigation).
* **G2 (O1 reversal — genuine σ-dependence).** At `n = 2`, `q' = 3`: the SPLIT type
  (λ = (1,1)) and the INERT type (λ = (2)) are DISTINCT types with DISTINCT menu-sum values —
  `1/9` vs `1/3` (`gate_v2_split_q3` / `gate_v2_inert_q3` / `gate_v2_sigma_separation`).
  RAMIFIED half: the totally ramified quadratic type `⟨{(2,1)}⟩` has an EMPTY order-0 menu
  (`omMenu_ramified_empty` — order-0 honesty: ramified types stay in the undecided pool), so its
  menu sum is `0` (`gate_v2_ramified_zero`) ≠ the inert `1/4 > 0` at `realP`
  (`gate_v2_ramified_vs_inert`). A σ-discarding regression (the old `if σ = σ₀` shape) fails
  these gates.

The evaluation spine is the singleton-menu collapse `sepShapesOf n (unramType n lam) =
{sepShape n lam}` (`unramType` is injective), which reduces every menu sum to the single
per-shape `omCount` pinned by the OMCountV2 CAL-p gates (`gate3_*`) and the Phase-A `1/4` gate
(`Order0.gate_rootCount_inert2`).

Footprints (`AxCheck` section): every gate must be Lean core ONLY.
-/

set_option linter.style.longLine false
set_option linter.style.header false

namespace LeanUrat.OM.RealInstanceV2Gates

open LeanUrat LeanUrat.MontesAxiom Polynomial
open LeanUrat.OM

/-! ## 0. The singleton-menu evaluation bank -/

/-- `unramType n` is INJECTIVE: the type's `(1, d)` multiset recovers the partition's parts
(`d ↦ (1, d)` is injective on multisets), and a partition is its parts. -/
theorem unramType_injective (n : ℕ) : Function.Injective (Order0.unramType n) := by
  intro lam lam' h
  have hdata : lam.parts.map (fun d => ((1 : ℕ), d))
      = lam'.parts.map (fun d => ((1 : ℕ), d)) := congrArg FactorizationType.data h
  have hinj : Function.Injective (fun d : ℕ => ((1 : ℕ), d)) := fun a b hab =>
    ((Prod.mk.injEq _ _ _ _).mp hab).2
  exact Nat.Partition.ext (Multiset.map_injective hinj hdata)

/-- **The σ-keyed order-0 menu of an unramified type is the SINGLETON of its own shape**:
`sepShapesOf n (unramType n lam) = {sepShape n lam}` — injectivity of `unramType` makes the
partition filter pick exactly `lam`. -/
theorem sepShapesOf_unramType (n : ℕ) (lam : Nat.Partition n) :
    Order0.sepShapesOf n (Order0.unramType n lam) = {Order0.sepShape n lam} := by
  ext T
  rw [Order0.sepShapesOf, Finset.mem_image, Finset.mem_singleton]
  constructor
  · rintro ⟨l, hl, rfl⟩
    rw [Finset.mem_filter] at hl
    rw [unramType_injective n hl.2]
  · rintro rfl
    exact ⟨lam, Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩, rfl⟩

/-- **The V2 capstone's own density collapses to the single per-shape count** at an unramified
type: `∑_{T ∈ omMenu n (unramType n lam)} omCount T q' = omCount (sepShape n lam) q'`. -/
theorem menuSum_unramType (n : ℕ) (lam : Nat.Partition n) (q' : ℕ) :
    (∑ T ∈ OMCountV2.omMenu n (Order0.unramType n lam), OMCountV2.omCount T q')
      = OMCountV2.omCount (Order0.sepShape n lam) q' := by
  rw [OMCountV2.omMenu_order0, sepShapesOf_unramType, Finset.sum_singleton]

/-! ## 1. G1 — non-vacuity (V1 reversal) at the V2 capstone's own density -/

/-- **G1, exact value.** The V2 capstone's menu-sum density at `n = 2`, the INERT type
`unramType 2 (indiscrete 2)`, and the real prime `realP = 2` is EXACTLY `1/4` (the audit's
"1/4 gate", now tied to the W2 capstone's own sum: singleton menu + the Phase-A
`gate_rootCount_inert2` through the D3 compatibility lemma). -/
theorem gate_v2_value_inert2 :
    (∑ T ∈ OMCountV2.omMenu 2 (Order0.unramType 2 (Nat.Partition.indiscrete 2)),
        OMCountV2.omCount T M9.realP) = 1 / 4 := by
  rw [menuSum_unramType, OMCountV2.omCount_sepShape_eq_rootCount]
  exact Order0.gate_rootCount_inert2

/-- **G1 (V1 reversal).** The V2 capstone's menu-sum density is STRICTLY POSITIVE at a concrete
type: the corrected σ-keyed engine density certified by `RealInstanceV2.montes_unconditional` is NOT the
vacuous constant `0`. -/
theorem gate_v2_nonvacuous :
    (0 : ℚ) < ∑ T ∈ OMCountV2.omMenu 2 (Order0.unramType 2 (Nat.Partition.indiscrete 2)),
        OMCountV2.omCount T M9.realP := by
  rw [gate_v2_value_inert2]
  norm_num

/-- **G1, pinned to the REAL instance** (blueprint D2 mitigation: gates are stated against the
instance, never the free interface): the genuine DECIDED-LIMIT density of the corrected real
counting model `realM2` at the inert `n = 2` type equals `1/4` — via `realD2`'s decomposition
theorem, so this consumes the instance's `partition` + `stratum_tendsto_C` discharges, not just
the engine evaluator. -/
theorem gate_v2_countingDensity_inert2 :
    (RealInstanceV2.realM2 2 (by norm_num)).countingDensity
        (Order0.unramType 2 (Nat.Partition.indiscrete 2)) = 1 / 4 := by
  rw [LeanUrat.MontesV2.MontesDataV2.countingDensity_eq_sum_coeff
    (RealInstanceV2.realD2 2 (by norm_num))]
  exact gate_v2_value_inert2

/-! ## 2. G2 — σ-separation (O1 reversal), unramified half -/

/-- **G2, split value.** At `q' = 3` the SPLIT degree-2 type (λ = (1,1)) has menu-sum `1/9`. -/
theorem gate_v2_split_q3 :
    (∑ T ∈ OMCountV2.omMenu 2 (Order0.unramType 2 OMCountV2.lam11), OMCountV2.omCount T 3)
      = 1 / 9 := by
  rw [menuSum_unramType]
  exact OMCountV2.gate3_split_q3

/-- **G2, inert value.** At `q' = 3` the INERT degree-2 type (λ = (2)) has menu-sum `1/3`. -/
theorem gate_v2_inert_q3 :
    (∑ T ∈ OMCountV2.omMenu 2 (Order0.unramType 2 OMCountV2.lam2), OMCountV2.omCount T 3)
      = 1 / 3 := by
  rw [menuSum_unramType]
  exact OMCountV2.gate3_inert_q3

/-- **G2 (O1 reversal).** Two DISTINCT degree-2 factorization types get DIFFERENT V2 capstone
menu-sum values at `q' = 3` (`1/9` vs `1/3`): the certified density is genuinely σ-DEPENDENT —
the old `shapesOf σ₀ σ = if σ = σ₀ then … else ∅` σ-discarding shape is machine-checked dead. -/
theorem gate_v2_sigma_separation :
    Order0.unramType 2 OMCountV2.lam11 ≠ Order0.unramType 2 OMCountV2.lam2
      ∧ (∑ T ∈ OMCountV2.omMenu 2 (Order0.unramType 2 OMCountV2.lam11),
            OMCountV2.omCount T 3)
        ≠ (∑ T ∈ OMCountV2.omMenu 2 (Order0.unramType 2 OMCountV2.lam2),
            OMCountV2.omCount T 3) := by
  refine ⟨OMCountV2.gate6_sigma_separation.1, ?_⟩
  rw [gate_v2_split_q3, gate_v2_inert_q3]
  norm_num

/-! ## 3. G2 — σ-separation, ramified half -/

/-- The totally RAMIFIED quadratic type: one factor with `(e, f) = (2, 1)`, degree `2·1 = 2`. -/
def ramType2 : FactorizationType := ⟨{(2, 1)}⟩

/-- `ramType2` has degree 2 (a genuine degree-2 type, comparable with the unramified ones). -/
theorem ramType2_degree : ramType2.degree = 2 := by
  simp [ramType2, FactorizationType.degree]

/-- **The ramified menu is EMPTY** (order-0 honesty: order 0 cannot decide ramified types — they
live in the undecided pool until Phase B): no partition's `unramType` carries an `e = 2` pair. -/
theorem omMenu_ramified_empty : OMCountV2.omMenu 2 ramType2 = ∅ := by
  rw [OMCountV2.omMenu_order0, Order0.sepShapesOf, Finset.image_eq_empty,
    Finset.filter_eq_empty_iff]
  intro lam _ heq
  have hdata : ramType2.data = lam.parts.map (fun d => ((1 : ℕ), d)) :=
    congrArg FactorizationType.data heq
  have hmem : ((2 : ℕ), (1 : ℕ)) ∈ lam.parts.map (fun d => ((1 : ℕ), d)) := by
    rw [← hdata]
    simp [ramType2]
  rw [Multiset.mem_map] at hmem
  obtain ⟨d, -, hd⟩ := hmem
  exact absurd (congrArg Prod.fst hd) (by norm_num)

/-- **G2, ramified value**: the V2 capstone's menu-sum density of the ramified type at `realP`
is `0` (empty menu — the honest "order 0 certifies nothing ramified", NOT a claim that the true
ramified density vanishes). -/
theorem gate_v2_ramified_zero :
    (∑ T ∈ OMCountV2.omMenu 2 ramType2, OMCountV2.omCount T M9.realP) = 0 := by
  rw [omMenu_ramified_empty, Finset.sum_empty]

/-- **G2, ramified separation**: at the real prime the ramified type's menu sum (`0`) differs
from the inert type's (`1/4`) — σ-dependence is visible across the ramified/unramified split
too. -/
theorem gate_v2_ramified_vs_inert :
    (∑ T ∈ OMCountV2.omMenu 2 ramType2, OMCountV2.omCount T M9.realP)
      ≠ (∑ T ∈ OMCountV2.omMenu 2 (Order0.unramType 2 (Nat.Partition.indiscrete 2)),
          OMCountV2.omCount T M9.realP) := by
  rw [gate_v2_ramified_zero, gate_v2_value_inert2]
  norm_num

/-! ## 4. G1-tame — the `htameFE` hypothesis constrains a NONZERO value (semantic audit item 2) -/

/-- **G1-tame (2026-07-19 fresh-context semantic audit, item 2 — the audit's single
JUSTIFICATION GAP, closed).** The capstone hypothesis `htameFE : TameFunctionalEquation realF2 n σ`
quantifies its value clause over TAME primes `q > n` only — and every previously banked positive
value (the `1/4` gate) sits at the WILD prime `q = 2 = n`, outside that quantifier. So no banked
fact excluded the degenerate reading "`realF2.density` vanishes at all tame primes", under which
`htameFE` would be dischargeable by the vacuous `num = 0, den = 1` witness and the capstone's
palindromy clause (P) would constrain nothing.

This gate closes that gap: `3` is prime, `3 > 2` is TAME for `n = 2`, and
`realF2.density 2 (unramType 2 lam2) 3 = 1/3 > 0` (the inert menu sum, `gate_v2_inert_q3` — the
value clause of any `htameFE` witness at the inert type must hit `1/3` at `q = 3`, forcing
`num ≠ 0`). Hence `TameFunctionalEquation realF2 2 σ_inert` genuinely constrains a nonzero
rational function, and (P) is a substantive palindromy claim about it. -/
theorem gate_v2_htameFE_nontrivial :
    Nat.Prime 3 ∧ 2 < 3 ∧
    (0 : ℚ) < RealInstanceV2.realF2.density 2 (Order0.unramType 2 OMCountV2.lam2) 3 := by
  refine ⟨by norm_num, by norm_num, ?_⟩
  show (0 : ℚ) < ∑ T ∈ OMCountV2.omMenu 2 (Order0.unramType 2 OMCountV2.lam2),
      OMCountV2.omCount T 3
  rw [gate_v2_inert_q3]
  norm_num

end LeanUrat.OM.RealInstanceV2Gates

section AxCheck

-- Blueprint W3 gate: every gate theorem must be Lean core ONLY
-- (`propext, Classical.choice, Quot.sound` — fewer is fine, MORE is a stop-the-line event).
#print axioms LeanUrat.OM.RealInstanceV2Gates.gate_v2_value_inert2
#print axioms LeanUrat.OM.RealInstanceV2Gates.gate_v2_nonvacuous
#print axioms LeanUrat.OM.RealInstanceV2Gates.gate_v2_countingDensity_inert2
#print axioms LeanUrat.OM.RealInstanceV2Gates.gate_v2_split_q3
#print axioms LeanUrat.OM.RealInstanceV2Gates.gate_v2_inert_q3
#print axioms LeanUrat.OM.RealInstanceV2Gates.gate_v2_sigma_separation
#print axioms LeanUrat.OM.RealInstanceV2Gates.omMenu_ramified_empty
#print axioms LeanUrat.OM.RealInstanceV2Gates.gate_v2_ramified_zero
#print axioms LeanUrat.OM.RealInstanceV2Gates.gate_v2_ramified_vs_inert
#print axioms LeanUrat.OM.RealInstanceV2Gates.gate_v2_htameFE_nontrivial

end AxCheck
