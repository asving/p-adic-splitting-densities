/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.OM.OMType
import LeanUrat.OM.UnramifiedBase
import LeanUrat.OM.ChildResidualExt
import LeanUrat.OM.OrderTwoContext
import LeanUrat.OM.ResidualBridgeExt

/-!
# `OrderTwoContextR` — the residue-field-EXTENSION OM-context with GENUINE `Rr := childResidualExt`
(P9, WAVE 3, Goal 2)

**The de-stubbed extension context.** Where `OrderTwoContext.fChildCtxExt` is an INTERFACE STUB with
`Rr := 0` (reads nothing from `f`), this file builds `fChildCtxExtR` — the same `M5.OMType`
scaffolding but with `Rr := childResidualExt …` (guarded to fit the budget), i.e. the GENUINE
`resField[X]`-valued residual read off the `O″`-development. It is the EXTENSION analogue of
`Classifier.fChildCtx` (which sets `Rr := if (childResidual …).natDegree ≤ s then childResidual … else 0`
over `Fr = ZMod p`), now over the residue-field EXTENSION `Fr = resField = F_{p^{deg g}}`.

This is ADDITIVE and in a NEW file: it does NOT edit the committed `OrderTwoContext.fChildCtxExt` stub
in place (two-stream contention rule — only B's own + new files; never `Classifier`/`OMType`/
`ResidualPolynomial`/`UnramifiedBase`/`Development` edited). The stub `fChildCtxExt` remains as the
interface witness; `fChildCtxExtR` is the reader-carrying upgrade.

## What this file lands (core-only, no `sorry`/`axiom`)

* `fChildCtxExtR` — an `M5.OMType` with `Fr := resField` (genuine degree-`deg g` field extension of
  `ZMod p`), `Rr := if (childResidualExt …).natDegree ≤ s then childResidualExt … else 0`,
  `dr := Rr.natDegree`. The three OMType obligations discharge exactly as in `fChildCtx`:
  - `hResidueDeg` from `OrderTwoContext.finrank_resField` (δ = finrank);
  - `hResidualDeg` by `rfl` (`dr := Rr.natDegree`);
  - `hDrLeCs` from the `≤ s` guard (`childResidualExt`'s degree bound `< μ` — here the guard makes it
    `≤ s` unconditionally, mirroring `fChildCtx`'s clamp; the guard is a budget-safety clamp, NOT a
    faithfulness lever, exactly as documented for `fChildCtx`/`rootResidual`).
* `clusterSize_fChildCtxExtR` — `clusterSize (fChildCtxExtR …) = s` by `rfl` (budget invariant).
* `Rr_fChildCtxExtR_eq_residualPoly` — the FAITHFULNESS TIE: when the residual is within budget
  (`natDegree ≤ s`), `fChildCtxExtR`'s `Rr` IS `M4.residualPoly (childDigitDataExt …) S` under the
  index reconciliation `residualDeg S + 1 = μ`, via the wave-3 B.2 bridge
  `ResidualBridgeExt.childResidualExt_eq_residualPoly`. This certifies the context's residual is the
  genuine GMN Def 2.21 residual over the extension field (for `deg ψ ≥ 2`), not the `0` stub.

## What this file does NOT do (open — wave 4)

* It does NOT thread a base-changed `f` (`O″Box`, blueprint §1a) nor tie `Φ = liftKeyExt … Ψ`
  (Lemma A); `Φ`, `h` are arbitrary, exactly as in `childResidualExt`/`ResidualBridgeExt`. Wiring
  those into the `classifyGenuineExtAux` recursion (blueprint §3) is wave 4.
* It is NOT yet consumed by any recursion — `classifyGenuineExtAux` (the SEPARATE `Nat.strongRecOn`-
  on-budget recursion threading `resField` as data per level) is the wave-4 target; this file supplies
  its per-node context TYPE with a genuine reader.

Discipline: no `sorry`/`axiom`/`native_decide`; core-only `[propext, Classical.choice, Quot.sound]`.
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false

namespace LeanUrat.OM.OrderTwoContextR

open Polynomial LeanUrat.OM

noncomputable section

variable (p N : ℕ) [hp : Fact p.Prime] (g : (ZMod (p ^ N))[X])

/-! ## The genuine-`Rr` residue-field-EXTENSION context -/

/-- **`fChildCtxExtR`** — the residue-field-EXTENSION OM-context with a GENUINE residual reader
(the de-stubbed `OrderTwoContext.fChildCtxExt`). `M5.OMType` with `F0 := ZMod p`,
`Fr := resField = F_{p^{deg g}}` (a genuine field extension), order `r`, cluster size `s`, extension
degree `δ := g.natDegree`, and

`Rr := if (childResidualExt … Φ μ h).natDegree ≤ s then childResidualExt … Φ μ h else 0`,
`dr := Rr.natDegree`.

The `≤ s` guard is the budget-safety clamp (identical to `Classifier.fChildCtx`'s), discharging
`hDrLeCs`; it never fires for genuine within-budget residuals. Reads the `O″`-development residual
into `resField[X]` — NOT the `Rr := 0` stub. `Φ`, `h` arbitrary (wave-4 wires them to a base-changed
`f`). -/
def fChildCtxExtR (r s : ℕ) (hgm : g.Monic) (hN : 0 < N)
    (hgirr : Irreducible (UnramifiedBase.gbar p N g hN))
    (Φ : (UnramifiedBase.Oring p N g)[X]) (μ : ℕ) (h : (UnramifiedBase.Oring p N g)[X]) :
    M5.OMType :=
  haveI : Fact (Irreducible (UnramifiedBase.gbar p N g hN)) := ⟨hgirr⟩
  letI : Finite (UnramifiedBase.resField p N g hN) :=
    OrderTwoContext.finite_resField p N g hgm hN hgirr
  { order := r
    F0 := ZMod p
    Fr := UnramifiedBase.resField p N g hN
    δ := g.natDegree
    Nr := ⟨0, fun _ => 0, fun _ => false⟩
    Rr := if (ChildResidualExt.childResidualExt p N g hgm hN Φ μ h).natDegree ≤ s
            then ChildResidualExt.childResidualExt p N g hgm hN Φ μ h else 0
    dr := (if (ChildResidualExt.childResidualExt p N g hgm hN Φ μ h).natDegree ≤ s
            then ChildResidualExt.childResidualExt p N g hgm hN Φ μ h else 0).natDegree
    keyDeg := 0
    cs := s
    hResidueDeg := (OrderTwoContext.finrank_resField p N g hgm hN).symm
    hResidualDeg := rfl
    hDrLeCs := by
      by_cases hle : (ChildResidualExt.childResidualExt p N g hgm hN Φ μ h).natDegree ≤ s
      · rw [if_pos hle]; exact hle
      · rw [if_neg hle, Polynomial.natDegree_zero]; exact Nat.zero_le _ }

/-- `clusterSize (fChildCtxExtR …) = s` (by `rfl`, `cs := s`). The budget invariant, matching
`clusterSize_fChildCtxExt` / `clusterSize_fChildCtx`. -/
theorem clusterSize_fChildCtxExtR (r s : ℕ) (hgm : g.Monic) (hN : 0 < N)
    (hgirr : Irreducible (UnramifiedBase.gbar p N g hN))
    (Φ : (UnramifiedBase.Oring p N g)[X]) (μ : ℕ) (h : (UnramifiedBase.Oring p N g)[X]) :
    M5.clusterSize (fChildCtxExtR p N g r s hgm hN hgirr Φ μ h) = s := rfl

/-- **The context's `Rr` is the GENUINE extension residual** (the faithfulness tie). When the
extension residual is within the cluster-size budget (`natDegree ≤ s`, the guard's on-branch) and the
side's residual degree matches the digit budget (`residualDeg S + 1 = μ`), `fChildCtxExtR`'s residual
`Rr` IS `M4.residualPoly (childDigitDataExt …) S` — the genuine GMN Def 2.21 residual polynomial over
the residue-field EXTENSION `k_S = resField`, via the wave-3 B.2 bridge
`ResidualBridgeExt.childResidualExt_eq_residualPoly`. Certifies the context carries the real residual,
not the `Rr := 0` stub. Core-only. -/
theorem Rr_fChildCtxExtR_eq_residualPoly (r s : ℕ) (hgm : g.Monic) (hN : 0 < N)
    (hgirr : Irreducible (UnramifiedBase.gbar p N g hN))
    (Φ : (UnramifiedBase.Oring p N g)[X]) (μ : ℕ) (h : (UnramifiedBase.Oring p N g)[X])
    (S : NewtonPolygon.Side) (hdeg : M4.residualDeg S + 1 = μ)
    (hle : (ChildResidualExt.childResidualExt p N g hgm hN Φ μ h).natDegree ≤ s) :
    haveI : Fact (Irreducible (UnramifiedBase.gbar p N g hN)) := ⟨hgirr⟩
    haveI : Finite (UnramifiedBase.resField p N g hN) :=
      OrderTwoContext.finite_resField p N g hgm hN hgirr
    (fChildCtxExtR p N g r s hgm hN hgirr Φ μ h).Rr =
      M4.residualPoly (ResidualBridgeExt.childDigitDataExt p N g hgm hN Φ μ h) S := by
  haveI : Fact (Irreducible (UnramifiedBase.gbar p N g hN)) := ⟨hgirr⟩
  haveI : Finite (UnramifiedBase.resField p N g hN) :=
    OrderTwoContext.finite_resField p N g hgm hN hgirr
  show (if (ChildResidualExt.childResidualExt p N g hgm hN Φ μ h).natDegree ≤ s
          then ChildResidualExt.childResidualExt p N g hgm hN Φ μ h else 0) =
      M4.residualPoly (ResidualBridgeExt.childDigitDataExt p N g hgm hN Φ μ h) S
  rw [if_pos hle]
  exact ResidualBridgeExt.childResidualExt_eq_residualPoly p N g hgm hN Φ μ h S hdeg

-- Footprint checks: each built decl must be ⊆ [propext, Classical.choice, Quot.sound].
#print axioms clusterSize_fChildCtxExtR
#print axioms Rr_fChildCtxExtR_eq_residualPoly

end

end LeanUrat.OM.OrderTwoContextR
