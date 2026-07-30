/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import LeanUrat.MovesX.Defs

/-! # KE3 — [ATTEMPT] X2CapP: the affine cap bound from TB-CAP per-clause caps

BRIDGE CAMPAIGN unit **KE3** (area BP4, cluster c3; blueprint
`lean/notes/BRIDGE_BP4_KERNELS_2026-07-30.md` §3.E (E-iii) + §4 KE3).
E-PHASE STATEMENT MODULE — statement with `sorry` body.

THE KERNEL: `X2CapP n X K` (MovesX/Defs.lean) — `cap(b) ≤ c_cap·(1 + Σ h_r)`
inside the ns-free fourth-piece family, on `capDetectable` branches. Blueprint
sketch: from TB-CAP's per-clause caps ((τ-hen) `N_V = 1` PROVED; (τ-irr)
per-realized-cell, level-indexed by the leaf cell's own heights).

RECORDED RESOLUTIONS:
1. ⚑ `CapStep` is a NAMED LAW (Q4 shape: hypothesis of the reduction theorem,
   never a new `XCtx` field): `XCtx.detCap` is free data ("TB-CAP cap of the
   branch's OWN cells") with NO in-corpus tie to the [3t] TB-CAP Lean surface
   (MovesT); the per-clause content is transcribed as a per-move accumulation —
   root cap ≤ `C_root`, each appended read adds ≤ `C_cell·(1 + h)` ((τ-hen)'s
   `N_V = 1` feeds the constant part, (τ-irr)'s level-indexed per-cell cap the
   `h`-part). The MovesT instance leg (the seam from the TB-CAP surface to this
   law) is owner-corpus work, not this unit's.
2. `CapStep` is stated on the TOTAL `detCap` field (defined on every branch);
   the `capDetectable` gate enters only in the target `X2CapP`, matching the
   XD1 `capTotal` 0-convention.
3. Constant bookkeeping: unrolling gives `cap(b) ≤ C_root + C_cell·(len + Σ h_r)
   ≤ C_root + 2·C_cell·Σ h_r` (`len ≤ Σ h_r` by `ν.hpos`), so
   `C_root + 2·C_cell ≤ K.ccap` suffices — recorded as the hypothesis.

deps: KE11 (CM gate — the affine-envelope probe runs FIRST; acceptance gated on
its candidate-stress record, REV 2 F5); [3t] TB-CAP Lean surface (MovesT) for
the eventual instance leg. Fallback: obstruction record naming the clause whose
per-cell cap outruns the affine form. Consumers: XD4 `x2hypAssembled`, KE9.
-/

namespace LeanUrat.MovesX

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedVariables false

/-- **KE3 named law (⚑ ratification)** — the TB-CAP per-clause cap accumulation
over one context: the root branch's cap is at most `Croot`, and each appended
read grows the cap by at most `Ccell·(1 + h)` (constant part = the (τ-hen)
`N_V = 1` clause; height part = the (τ-irr) per-realized-cell level-indexed
clause). Stated on the total `detCap` (resolution 2 of the module docstring). -/
structure CapStep (n p : ℕ) [Fact p.Prime] (C : XCtx n p)
    (Croot Ccell : ℚ) : Prop where
  root : ∀ f : MonicBox n p, ((C.detCap (C.root f) : ℕ) : ℚ) ≤ Croot
  step : ∀ (f : MonicBox n p) (b c : C.Branch f) (ν : XNode n),
    c ∈ C.children b → C.hist c = C.hist b ++ [ν] →
      ((C.detCap c : ℕ) : ℚ) ≤ ((C.detCap b : ℕ) : ℚ) + Ccell * (1 + (ν.h : ℚ))

/-- **KE3 [ATTEMPT]** — `X2CapP` from the per-clause accumulation: branch
induction along the `parent` chain (`C.reach`/`C.parent_hist`/`children_iff`),
summing `CapStep.step` to `cap(b) ≤ Croot + Ccell·(len + Σ h_r)`, then
`len ≤ Σ h_r` (`ν.hpos` per node) and `Croot + 2·Ccell ≤ K.ccap` close the
affine target `K.ccap·(1 + Σ h_r)`; the empty history is `root` directly.
deps: KE11 (gate), `CapStep` (⚑). -/
theorem x2Cap_of_capStep {n : ℕ} (X : XFamily n) (K : XConsts n)
    (Croot Ccell : ℚ) (hroot : 0 ≤ Croot) (hcell : 0 ≤ Ccell)
    (hstep : ∀ (p : ℕ) [Fact p.Prime], CapStep n p (X.ctx p) Croot Ccell)
    (hccap : Croot + 2 * Ccell ≤ K.ccap) :
    X2CapP n X K := by
  sorry

end LeanUrat.MovesX
