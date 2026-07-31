/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import LeanUrat.MovesX.Defs

/-! # KE9 — [ATTEMPT, lowest priority] X2ProgressP linear

BRIDGE CAMPAIGN unit **KE9** (area BP4, cluster c3; blueprint
`lean/notes/BRIDGE_BP4_KERNELS_2026-07-30.md` §3.E (E-vi) + §4 KE9).
PROVED 2026-07-31 (`x2Progress_of_pricing`, footprint Lean-core; conditional on
the ⚑ `ProgressPricing` law). EXPLICITLY DEFERRABLE: X.3 does NOT consume
`X2ProgressP` (only SQ.3's quantitative envelope does), and the √N form is also
PROVED (XD4 `x2hypAssembled`).

THE KERNEL: `X2ProgressP n X K` (MovesX/Defs.lean) — an undetected-at-N
fourth-piece branch is deep or tall at LINEAR rates
(`cd·N − cd' ≤ d_total ∨ ch·N − ch' ≤ max h`).

RECORDED RESOLUTIONS:
1. ⚑ `ProgressPricing` is the NAMED LAW carrying the blueprint's "per-move
   mass-pricing idea" at its arithmetic interface: an affine bound of
   `thr + cap` in `d_total + max h` JOINTLY (not in `Σ h_r` — the `Σ h_r`
   currency of KE2/KE3 only yields the PROVED √N form via
   `Σ h ≤ (d_total+1)·max h`, XD2). This law is exactly what the per-move
   pricing must produce for linearity; its failure shape is the obstruction
   record. The blueprint gives no finer decomposition — recorded as the
   minimal resolution; the ⚑ ratification decides whether the pricing route
   is developed against it or the unit stays parked.
2. Constants: from `N < Cprog·(1 + d_total + max h)` one of `d_total`, `max h`
   exceeds `N/(2·Cprog) − 1/2`; the slope hypotheses
   `K.cd·(2·Cprog) ≤ 1`, `K.ch·(2·Cprog) ≤ 1` and intercepts
   `1/2 ≤ K.cd'`, `1/2 ≤ K.ch'` make the target follow — pure `nlinarith`
   territory once the law is applied.

deps: KE2/KE3 (scheduling gate only — no logical dep), KE11's probe record
for candidate stress. Consumers: SQ.3's exponential envelope ONLY.
-/

namespace LeanUrat.MovesX

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedVariables false

/-- **KE9 named law (⚑ ratification)** — the linear-coercivity pricing over one
context: on the fourth-piece family, `thr + cap` is affinely dominated by
`d_total + max h` JOINTLY (the per-move mass pricing's arithmetic output;
resolution 1 of the module docstring). -/
structure ProgressPricing (n p : ℕ) [Fact p.Prime] (C : XCtx n p)
    (Cprog : ℚ) : Prop where
  bound : ∀ (f : MonicBox n p) (b : C.Branch f), FourthPieceB C b →
    ((C.threshold b : ℕ) : ℚ) + ((capHB C b : ℕ) : ℚ) ≤
      Cprog * (1 + (dTotal (C.hist b) : ℚ) + (maxH (C.hist b) : ℚ))

/-- **KE9 [PROVED 2026-07-31]** — `X2ProgressP` (the LINEAR progress
kernel) from the pricing law: `N < thr + cap ≤ Cprog·(1 + d_total + max h)`
forces `d_total` or `max h` past `N/(2·Cprog) − 1/2`, and the slope/intercept
hypotheses convert that to the `K`-rated dichotomy (resolution 2).
deps: `ProgressPricing` (⚑); scheduling per the blueprint's "only if KE2+KE3
land with room". -/
theorem x2Progress_of_pricing {n : ℕ} (X : XFamily n) (K : XConsts n)
    (Cprog : ℚ) (hC : 0 < Cprog)
    (hpr : ∀ (p : ℕ) [Fact p.Prime], ProgressPricing n p (X.ctx p) Cprog)
    (hcd : K.cd * (2 * Cprog) ≤ 1) (hcd' : (1 : ℚ) / 2 ≤ K.cd')
    (hch : K.ch * (2 * Cprog) ≤ 1) (hch' : (1 : ℚ) / 2 ≤ K.ch') :
    X2ProgressP n X K := by
  intro p hp f b N hfp hN
  -- The pricing law at this prime, evaluated on the fourth-piece branch.
  have hprice := (hpr p).bound f b hfp
  -- `N < thr + cap` (nat) casts to ℚ.
  have hNQ : (N : ℚ) < ((X.ctx p).threshold b : ℚ) + (capHB (X.ctx p) b : ℚ) := by
    exact_mod_cast hN
  set d : ℚ := (dTotal ((X.ctx p).hist b) : ℚ) with hd_def
  set h : ℚ := (maxH ((X.ctx p).hist b) : ℚ) with hh_def
  -- Chain: `N < thr + cap ≤ Cprog·(1 + d + h)`.
  have hN2 : (N : ℚ) < Cprog * (1 + d + h) := lt_of_lt_of_le hNQ hprice
  have hNnn : (0 : ℚ) ≤ (N : ℚ) := by positivity
  -- Suppose both disjuncts fail; the pricing bound then forces `N < N`.
  by_contra hcon
  simp only [not_or, not_le] at hcon
  obtain ⟨hd, hh⟩ := hcon
  nlinarith [hN2, hC,
    mul_pos hC (by linarith : (0 : ℚ) < K.cd * (N : ℚ) - K.cd' - d),
    mul_pos hC (by linarith : (0 : ℚ) < K.ch * (N : ℚ) - K.ch' - h),
    mul_nonneg (by linarith : (0 : ℚ) ≤ 1 - K.cd * (2 * Cprog)) hNnn,
    mul_nonneg (by linarith : (0 : ℚ) ≤ 1 - K.ch * (2 * Cprog)) hNnn,
    mul_nonneg hC.le (by linarith : (0 : ℚ) ≤ K.cd' - 1 / 2),
    mul_nonneg hC.le (by linarith : (0 : ℚ) ≤ K.ch' - 1 / 2)]

end LeanUrat.MovesX
