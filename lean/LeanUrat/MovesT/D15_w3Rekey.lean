/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.MovesT.Defs
import LeanUrat.MovesT.D12_packages

/-! # T-D15 `w3_rekey` — the S-3 demand VERBATIM: "assume XRB's CONCLUSION … re-keyed
form", the ledger premise the REAL imported `MovesS.LedgerIV` (REV 4, Codex-3 #18 —
the central round-3 adjudication COMPLETED). STATUS HONESTY: this unit STATES the
re-keyed obligation (an rfl-level identity pinning its shape); DERIVING its
conclusion is MovesS wave-5's RS.1 work. PROVED (rfl). -/

set_option linter.style.longLine false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesT

open Polynomial LeanUrat.Moves LeanUrat.MovesC LeanUrat.MovesD

theorem w3_rekey_typed {n' : ℕ} (T' : MovesS.TableShape n')
    (M : MovesS.MeasuredSide T') (RB : MovesS.RatBurdens T' M)
    (hdc : MovesS.DegCons T') (Pi' : RS1GivenPackage)
    (B₀ : MovesS.RS1Meas T' M) :
    w3Rekeyed RB hdc (RS1GivenHolds Pi') B₀
      = (RS1GivenHolds Pi' → MovesS.LedgerIV T' M → hxrbStmt T' M B₀ →
          ∀ e (he : e ∈ Finset.Icc 1 n') (τ : T'.State e) (σ' : Multiset T'.VType)
            (q₀ : ℚ) (hq : q₀ ∈ M.Pools), M.activeState q₀ e τ →
            ∀ h_ent, B₀.βmeas e he h_ent τ σ' q₀
              = MovesS.evalRe T' M RB hdc e he τ σ' q₀
                  (fun e' he' => B₀.βmeas e' he' h_ent)) :=
  rfl

end LeanUrat.MovesT
