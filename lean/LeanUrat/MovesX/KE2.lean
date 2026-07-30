/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import LeanUrat.MovesX.Defs

/-! # KE2 — [ATTEMPT] X2AffP: the affine threshold bound from a per-move law

BRIDGE CAMPAIGN unit **KE2** (area BP4, cluster c3; blueprint
`lean/notes/BRIDGE_BP4_KERNELS_2026-07-30.md` §3.E (E-ii) + §4 KE2).
E-PHASE STATEMENT MODULE — statement with `sorry` body.

THE KERNEL: `X2AffP n X K` (MovesX/Defs.lean) — `thr(b) ≤ 1 + c₀·Σ h_r` on the
fourth-piece family. Blueprint sketch: branch induction through D.11's per-move
threshold form ("largest constrained height + 1") with scale product `Π e_i ≤ n`;
candidate `c₀ = n·C_move`.

RECORDED RESOLUTIONS:
1. ⚑ `ThresholdStep` is the blueprint-flagged NAMED LAW (the check "which XCtx
   threshold laws exist" came back EMPTY — `XCtx.threshold` is free data, the
   per-move form is unbuilt, so the ⚑ fires as the blueprint anticipates;
   hypothesis shape per Q4, never a new `XCtx` field). Its `step` field is the
   D.11 per-move form with the scale factor applied at CONTINUING INCREMENTS
   ONLY (`ν.continuing && ν.isIncrement`) — the minimal resolution against the
   repo vocabulary, since `HistWF.degProd` (the corpus's ONLY `Π e_i ≤ n`) is
   filtered on exactly that predicate. Whether D.11 also scales at recentering
   moves is part of the ⚑ ratification.
2. The constant hypothesis is `n·(C_move + 1) ≤ K.c0`, STRENGTHENED from the
   blueprint's candidate `c₀ = n·C_move`: unrolling the step law along a
   nonempty history yields `thr ≤ Π(scale) + C_move·Π(scale)·Σ h_r ≤
   n + n·C_move·Σ h_r`, and absorbing the root term `n` into the affine form
   `1 + c₀·Σ h_r` uses `Σ h_r ≥ 1` (each `ν.hpos`), costing the extra `+n·Σ h_r`.
   This is hypothesis-side slack only; `X2AffP` itself is untouched.

deps: KE11 (CM gate — the affine-envelope probe runs FIRST; acceptance of any
proof is gated on its candidate-stress record, REV 2 F5). Fallback: the
obstruction record with the branch shape whose threshold outruns the affine
bound. Consumers: XD4 `x2hypAssembled` (via `X2AffP` by name), KE9.
-/

namespace LeanUrat.MovesX

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedVariables false

/-- **KE2 named law (⚑ ratification)** — D.11's per-move threshold form over one
context: the root threshold is at most `1`, and each child read moves the
threshold by at most the increment scale `e` times the parent threshold plus
`C_move` times the read's own height ("largest constrained height + 1", with the
scale applied at continuing increments only — resolution 1 of the module
docstring). Owner of the instance leg: the D.11/MovesD side (not this unit). -/
structure ThresholdStep (n p : ℕ) [Fact p.Prime] (C : XCtx n p)
    (Cmove : ℚ) : Prop where
  root : ∀ f : MonicBox n p, ((C.threshold (C.root f) : ℕ) : ℚ) ≤ 1
  step : ∀ (f : MonicBox n p) (b c : C.Branch f) (ν : XNode n),
    c ∈ C.children b → C.hist c = C.hist b ++ [ν] →
      ((C.threshold c : ℕ) : ℚ) ≤
        (if ν.continuing && ν.isIncrement then (ν.e : ℚ) else 1)
            * ((C.threshold b : ℕ) : ℚ)
          + Cmove * (ν.h : ℚ)

/-- **KE2 [ATTEMPT]** — `X2AffP` from the per-move law: branch induction along
the `parent` chain (every branch reaches the root, `C.reach`; each step appends
one node, `C.parent_hist`/`children_iff`), unrolling `ThresholdStep.step` and
bounding every partial scale product by `n` through `HistWF.degProd`
(`C.wf`; all factors ≥ 1 by `XNode.epos`). Constant bookkeeping per
resolution 2: `thr(b) ≤ n + n·C_move·Σ h_r ≤ 1 + n·(C_move+1)·Σ h_r ≤
1 + K.c0·Σ h_r`, the empty history closed by `root`. deps: KE11 (gate),
`ThresholdStep` (⚑). -/
theorem x2Aff_of_thresholdStep {n : ℕ} (X : XFamily n) (K : XConsts n)
    (Cmove : ℚ) (hCmove : 0 ≤ Cmove)
    (hstep : ∀ (p : ℕ) [Fact p.Prime], ThresholdStep n p (X.ctx p) Cmove)
    (hc0 : (n : ℚ) * (Cmove + 1) ≤ K.c0) :
    X2AffP n X K := by
  sorry

end LeanUrat.MovesX
