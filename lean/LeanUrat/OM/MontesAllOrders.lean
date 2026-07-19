/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.OM.Order0Capstone
import LeanUrat.OM.Order0Alpha
import LeanUrat.OM.OMCountV2

/-!
# MontesAllOrders — S1: the ALL-ORDERS ASSEMBLY SKELETON (`notes/ASSEMBLY_BLUEPRINT.md` §S1)

**The skeleton.** `montes_allorders_of_hnode` generalizes the Phase-A capstone
`Order0Capstone.montes_order0` from the SEPARABLE SLICE `(sepShapesOf n σ, rootCount)` to an
ARBITRARY menu `M : Finset ClusterShape` and the CORRECTED per-node recursion
`OMCountV2.omCount`, taking the two open pieces as an explicit hypothesis:

* `h_node` — the per-shape counting limit `stratumCount T N / realP^{nN} → omCount T realP` for
  every `T ∈ M`. (The order-0 discharge is `h_node0_proved`; the order-≥1 discharge is the S2/S3
  work item.)

Conclusion: `q' ↦ ∑_{T ∈ M} omCount T q'` is a UNIFORM RATIONAL FUNCTION of `q'` (one `num/den`,
denominator nonvanishing at every `q' > 1`), and — GIVEN `h_node` — the REAL normalized menu-sum
counts at `realP` converge to `num(realP)/den(realP)`.

**The key generalization.** `montes_order0` needed a per-shape LEAF HYPOTHESIS
(`rootCount_isRational_of_leaf` fed the `sepShape_leaf` witness) to know the coefficient was
rational. Here that step is `OMCountV2.omCount_isRational` — PROVEN for EVERY shape (the full
recursion's rationality, cluster nodes included), so NO leaf hypothesis is required. The proof is
otherwise `montes_order0`'s VERBATIM structure: (1) each coefficient rational, (2) the finite menu
sum rational via `isRationalFn_finsetSum`, (3) the value tie via `tendsto_finsetSum` on `h_node`
plus the `Finset.sum_div` push (`montes_order0`'s `hpush`/`hsum` step).

**The soundness gate (S1 requirement).** `montes_allorders_of_hnode_specializes`: at
`M = sepShapesOf n σ` the skeleton REPRODUCES `montes_order0`'s conclusion. On the separable menu
`omCount T = rootCount ... T` (`OMCountV2.omCount_sepShape_eq_rootCount`), so `h_node` at
`sepShapesOf` IS `h_node0_proved` — the corollary is UNCONDITIONAL and recovers the order-0
capstone. This proves the skeleton is a genuine generalization, not a weaker statement.

This module is a REPACKAGING (the proven `montes_order0` structure + the proven
`omCount_isRational`); it is additive over the frozen OM capstone chain.
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedVariables false

namespace LeanUrat.OM.MontesAllOrders

open scoped Classical
open LeanUrat LeanUrat.MontesAxiom RatFn Polynomial Filter Topology
open LeanUrat.OM LeanUrat.OM.Order0 LeanUrat.OM.OMCountV2

/-! ## The skeleton -/

/-- **S1 — the ALL-ORDERS ASSEMBLY SKELETON** (`notes/ASSEMBLY_BLUEPRINT.md` §S1). For an
ARBITRARY degree-`n` factorization type `σ` and menu `M : Finset ClusterShape`, GIVEN the per-shape
counting limit `h_node` (`stratumCount T N / realP^{nN} → omCount T realP` on `M`), the menu-sum
density `q' ↦ ∑_{T ∈ M} omCount T q'` is a UNIFORM RATIONAL FUNCTION of `q'` (one `num/den`,
denominator nonvanishing at every `q' > 1`), and the REAL normalized menu-sum counts at `realP`
converge to `num(realP)/den(realP)`.

Proof = `Order0Capstone.montes_order0`'s VERBATIM structure with the leaf-rationality step
(`rootCount_isRational_of_leaf`) REPLACED by `OMCountV2.omCount_isRational` — proven for every
shape, so NO leaf hypothesis is needed (the key generalization). -/
theorem montes_allorders_of_hnode (n : ℕ) (σ : FactorizationType) (M : Finset ClusterShape)
    (h_node : ∀ T ∈ M,
      Filter.Tendsto
        (fun N => M8.stratumCount (M9.rawCount n) T N / (M9.realP : ℚ) ^ (n * N))
        Filter.atTop
        (nhds (omCount T M9.realP))) :
    ∃ (num den : Polynomial ℚ), den ≠ 0 ∧
      (∀ q' : ℕ, 1 < q' → den.eval (q' : ℚ) ≠ 0 ∧
        (∑ T ∈ M, omCount T q') = num.eval (q' : ℚ) / den.eval (q' : ℚ)) ∧
      Filter.Tendsto
        (fun N => (∑ T ∈ M, M8.stratumCount (M9.rawCount n) T N)
            / (M9.realP : ℚ) ^ (n * N))
        Filter.atTop
        (nhds (num.eval (M9.realP : ℚ) / den.eval (M9.realP : ℚ))) := by
  classical
  -- (1) each menu shape's corrected coefficient is rational — NO leaf hypothesis needed
  -- (`omCount_isRational` is proven for EVERY shape, cluster nodes included).
  have hrat : ∀ T ∈ M, IsRationalFn (fun q' => omCount T q') := fun T _ => omCount_isRational T
  -- (2) the finite menu sum is rational:
  obtain ⟨num, den, hden, hall⟩ :=
    isRationalFn_finsetSum M (fun T q' => omCount T q') hrat
  refine ⟨num, den, hden, hall, ?_⟩
  -- (3) the value tie at `realP`: sum of the per-shape limits (h_node) = the rational value.
  have hq : 1 < M9.realP := by unfold M9.realP; norm_num
  have hsum : Filter.Tendsto
      (fun N => ∑ T ∈ M, M8.stratumCount (M9.rawCount n) T N / (M9.realP : ℚ) ^ (n * N))
      Filter.atTop
      (nhds (∑ T ∈ M, omCount T M9.realP)) :=
    tendsto_finsetSum M (fun T hT => h_node T hT)
  have hpush : (fun N => (∑ T ∈ M, M8.stratumCount (M9.rawCount n) T N)
        / (M9.realP : ℚ) ^ (n * N))
      = fun N => ∑ T ∈ M, M8.stratumCount (M9.rawCount n) T N / (M9.realP : ℚ) ^ (n * N) := by
    funext N
    rw [Finset.sum_div]
  rw [hpush]
  have hval := (hall M9.realP hq).2
  rw [← hval]
  exact hsum

/-! ## The soundness gate — the skeleton recovers `montes_order0` -/

/-- **The S1 SOUNDNESS GATE** (`notes/ASSEMBLY_BLUEPRINT.md` §S1). At `M = sepShapesOf n σ`
(with `0 < n`) the skeleton REPRODUCES `Order0Capstone.montes_order0`'s conclusion VERBATIM: on the
separable menu `omCount T = rootCount ... T` (`OMCountV2.omCount_sepShape_eq_rootCount`), so the
`h_node` hypothesis at `sepShapesOf` IS `Order0Alpha.h_node0_proved` — the corollary is
UNCONDITIONAL and recovers the order-0 capstone. This certifies the skeleton is a genuine
generalization, not a weaker statement. -/
theorem montes_allorders_of_hnode_specializes (n : ℕ) (hn : 0 < n) (σ : FactorizationType) :
    ∃ (num den : Polynomial ℚ), den ≠ 0 ∧
      (∀ q' : ℕ, 1 < q' → den.eval (q' : ℚ) ≠ 0 ∧
        (∑ T ∈ sepShapesOf n σ,
            rootCount M7.cellsOfShapeWF M6.treeSize M7.cellsOfShapeWF_descend T q')
          = num.eval (q' : ℚ) / den.eval (q' : ℚ)) ∧
      Filter.Tendsto
        (fun N => (∑ T ∈ sepShapesOf n σ, M8.stratumCount (M9.rawCount n) T N)
            / (M9.realP : ℚ) ^ (n * N))
        Filter.atTop
        (nhds (num.eval (M9.realP : ℚ) / den.eval (M9.realP : ℚ))) := by
  classical
  -- Discharge `h_node` at `M = sepShapesOf n σ` FROM `h_node0_proved`: on the separable menu
  -- `omCount = rootCount` (`omCount_sepShape_eq_rootCount`), so `h_node` there IS `h_node0_proved`.
  have h_node : ∀ T ∈ sepShapesOf n σ,
      Filter.Tendsto
        (fun N => M8.stratumCount (M9.rawCount n) T N / (M9.realP : ℚ) ^ (n * N))
        Filter.atTop
        (nhds (omCount T M9.realP)) := by
    intro T hT
    rw [sepShapesOf, Finset.mem_image] at hT
    obtain ⟨lam, hlam, rfl⟩ := hT
    have hmem : sepShape n lam ∈ sepShapesOf n σ := by
      rw [sepShapesOf, Finset.mem_image]
      exact ⟨lam, hlam, rfl⟩
    rw [omCount_sepShape_eq_rootCount]
    exact h_node0_proved n hn σ (sepShape n lam) hmem
  obtain ⟨num, den, hden, hall, htie⟩ :=
    montes_allorders_of_hnode n σ (sepShapesOf n σ) h_node
  -- rewrite the `∑ omCount` conclusion back to `∑ rootCount` on the separable menu
  refine ⟨num, den, hden, fun q' hq' => ?_, htie⟩
  obtain ⟨hnv, hval⟩ := hall q' hq'
  refine ⟨hnv, ?_⟩
  rw [← hval]
  refine Finset.sum_congr rfl fun T hT => ?_
  rw [sepShapesOf, Finset.mem_image] at hT
  obtain ⟨lam, _, rfl⟩ := hT
  exact (omCount_sepShape_eq_rootCount n lam q').symm

end LeanUrat.OM.MontesAllOrders
