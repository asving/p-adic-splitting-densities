/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.B2D.TDDefsV2

/-!
# B2D/TD1_floorsCharge — `FloorsChargeLaw` at the ledger instance
  [B2DEF_LEAN unit TD-1; wave 2b]

Blueprint §5 TD-1. moves_ref: §B2-DEF D.8 (BOX), D.11 (A1/TRI ledger). deps: TD-0,
CL5 (via the `slot_count_val` lawfulness clause — TDDefs design flag 2: the
LED/T10/C6(CL5)/`L6_ledgerCount` substance is discharged at TD-0; this unit
derives the ∀-q H2 law, vacuous off q₀ by the support constraint).
difficulty: medium-hard as priced; see the TDDefs flag for the E-phase
re-pricing finding. E-phase file: statement only.

STATEMENT ROUND 2 (v2, 2026-08-02): the lawfulness hypothesis is now
`LedgerLawfulV2` (TDDefsV2's finite-box semantics) — v1's `LedgerSemantics`
was REFUTED at the TD-0/TD-3 hard-hole run (commit 5371139,
`TD3_countermodel.lean`: `Nat.card` over all of `Coord → ℕ` forced ≡ 0 and
made this law's siblings vacuously satisfiable). This clause consumes
`slot_count_val`, untouched by the v1→v2 diff; the hypothesis re-key
de-vacuifies its instance supply. -/

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false

namespace LeanUrat.B2D

open LeanUrat.Scaffold LeanUrat.Scaffold.HDischarge.H2 LedgerStratumData

variable {D : CensusData} {W : WindowDatum D} {P : ParentShape D W}

/-- **TD-1**: the (F) floors face at the ledger instance — per-slot height counts
at the joint condition max(β_k, g_k), for every q (substantive at q₀, vacuous off
support). -/
theorem ledger_floorsCharge (L : LedgerStratumData D W P) (hL : L.LedgerLawfulV2)
    (hscope : LedgerScope W P) (hclean : LedgerClean D W P L.N) :
    FloorsChargeLaw W P L.ledgerJoint := by
  sorry -- B2DEF_LEAN E-phase sorry [unit TD-1, statement round 2 (v2)]

end LeanUrat.B2D
