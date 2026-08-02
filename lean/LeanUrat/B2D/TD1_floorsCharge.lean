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
de-vacuifies its instance supply.

PROVED (v3 wave, 2026-08-08 wallclock 2026-08-02) — AT THE v2 STATEMENT,
byte-unchanged: the law is `slot_count_val` at `q = q₀` plus the [R2-C1]
support constraint (`ledger_rhoCount_off_support`) off it, exactly as the
E-phase re-pricing finding predicted (TDDefs design flag 2: the count-VALUE
substance rides the clause TD-0 discharges). Deliberately NOT re-keyed to
`LedgerLawfulV3`: v2 suffices here, and a theorem at the weaker pack is the
stronger (and still non-vacuous: `td_lawfulV2`) statement — v3-lawful
instances consume it through `extends`. -/

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false

namespace LeanUrat.B2D

open LeanUrat.Scaffold LeanUrat.Scaffold.HDischarge.H2 LedgerStratumData

variable {D : CensusData} {W : WindowDatum D} {P : ParentShape D W}

set_option linter.unusedVariables false in
/-- **TD-1**: the (F) floors face at the ledger instance — per-slot height counts
at the joint condition max(β_k, g_k), for every q (substantive at q₀, vacuous off
support). -/
theorem ledger_floorsCharge (L : LedgerStratumData D W P) (hL : L.LedgerLawfulV2)
    (hscope : LedgerScope W P) (hclean : LedgerClean D W P L.N) :
    FloorsChargeLaw W P L.ledgerJoint := by
  intro q ρ hρ k hk
  by_cases hq : q = L.q0
  · subst hq
    have hρ0 : ρ < L.rho0 := by
      simpa [LedgerStratumData.ledgerJoint] using hρ
    simp only [LedgerStratumData.ledgerJoint, if_true]
    exact hL.slot_count_val ρ hρ0 k hk
  · rw [ledger_rhoCount_off_support L q hq] at hρ
    omega

end LeanUrat.B2D

#print axioms LeanUrat.B2D.ledger_floorsCharge
