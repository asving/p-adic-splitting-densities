/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.OM.GradedHensel

/-!
# P5 — GradedMargin: the M1/M2 admissibility-margin arithmetic (general)

The deep-wild graded (per-slot) Hensel margin has three ingredients M0/M1/M2 (`GRADED_MARGIN_PROOF`).
`GradedHensel.gate_margin_graded_A/B/C` prove M1/M2 at the three concrete deep-wild gates by `decide`.
This leaf lifts the M1 and M2 inequalities to GENERAL Newton data (`e, m, S, N` arbitrary), so the
graded margins are theorems rather than per-case decisions. Purely additive leaf (nothing imports it).

The remaining, HARD half of P5 — the general-cell **M0** (`GradedUpgradeAt` + `polyKer` card `= p^c`)
— is NOT here: it needs the Schur/unimodular-top-block reduction (no machinery in-tree) and stays the
numerically-gated obligation `ProductTheorem.obligation_hensel_surjective`. This file makes NO claim
about M0, about closing D9, or about coset-wide constancy; it is the two admissibility inequalities only.
-/

open LeanUrat LeanUrat.OM

namespace LeanUrat.OM.GradedMargin

/-- **M1 (general): the x-slot floor is below the graded kernel depth, per slot.** For a block of
degree `m` and ramification `e > 0`, at slot `t`, the pattern floor `sideFloor e m t = ⌈(m+1-t)/e⌉`
is `≤` the graded kernel depth `sideDepth e S N t = N - S - ⌊t/e⌋`, PROVIDED the admissibility budget
`(m+1-t) + e·(S + ⌊t/e⌋) ≤ e·N` holds (the per-slot θ-weight fits under the level-`N` ceiling).
Generalizes the `decide`-proved per-slot halves of `GradedHensel.gate_margin_graded_A/B/C`. -/
theorem sideFloor_le_sideDepth_of_admissible {e m S N t : ℕ} (he : 0 < e)
    (hadm : m + 1 - t + e * (S + t / e) ≤ e * N) :
    GradedHensel.sideFloor e m t ≤ GradedHensel.sideDepth e S N t := by
  rw [GradedHensel.sideFloor, GradedHensel.sideDepth, GradedHensel.cdiv_le_iff he,
    Nat.sub_sub, Nat.mul_sub]
  omega

/-- **M2 (general): two graded kernel depths sum to at least `N`.** For two blocks with ramifications
`eA, eB`, cross-shares `SA, SB`, at slots `s, t`, the graded kernel depths sum to `≥ N` PROVIDED the
admissibility budget `⌊s/eA⌋ + ⌊t/eB⌋ + SA + SB ≤ N` holds (the two per-slot depths jointly cover the
level). Generalizes the `decide`-proved cross halves of `GradedHensel.gate_margin_graded_A/B/C`. -/
theorem sideDepth_add_sideDepth_ge_of_admissible {eA SA eB SB N s t : ℕ}
    (hadm : s / eA + t / eB + SA + SB ≤ N) :
    N ≤ GradedHensel.sideDepth eA SA N s + GradedHensel.sideDepth eB SB N t := by
  rw [GradedHensel.sideDepth, GradedHensel.sideDepth]
  omega

-- Footprint checks: must be ⊆ [propext, Classical.choice, Quot.sound].
#print axioms sideFloor_le_sideDepth_of_admissible
#print axioms sideDepth_add_sideDepth_ge_of_admissible

end LeanUrat.OM.GradedMargin
