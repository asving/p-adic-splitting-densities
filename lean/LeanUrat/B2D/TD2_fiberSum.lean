/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.B2D.TDDefsV2

/-!
# B2D/TD2_fiberSum — `FiberSumLaw` at the ledger instance
  [B2DEF_LEAN unit TD-2; wave 2b]

Blueprint §5 TD-2. moves_ref: §B2-DEF D.3(e)(ii) bottom-up display
"w ≥ γ ⟺ all lower digits vanish" (MOVES :2170–2173). deps: TD-0.
difficulty: medium. REUSE: T3/T5 (through TD-0's clauses); at the abstract datum
the proof is the partition count: summing the member-cylinder cards over the
`Fin (q₀^d)` digit box recovers the height-only card (`semantics` +
`digit_range`). E-phase file: statement only.

STATEMENT ROUND 2 (v2, 2026-08-02): the lawfulness hypothesis is now
`LedgerLawfulV2` (TDDefsV2's finite-box semantics). Under v1 this law was
VACUOUSLY satisfiable (both sides forced 0 — the TD-0/TD-3 refutation's
adjacent consequence, `TD3_countermodel.lean` docstring); at v2 the members
partition over their read vectors on a FINITE carrier, so the sum is a
genuine partition count. -/

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false

namespace LeanUrat.B2D

open LeanUrat.Scaffold LeanUrat.Scaffold.HDischarge.H2 LedgerStratumData

variable {D : CensusData} {W : WindowDatum D} {P : ParentShape D W}

/-- **TD-2**: the (F) aggregation seam at the ledger instance — digit-level
counts aggregate to the height-only fiber count. -/
theorem ledger_fiberSum (L : LedgerStratumData D W P) (hL : L.LedgerLawfulV2)
    (hscope : LedgerScope W P) (hclean : LedgerClean D W P L.N) :
    FiberSumLaw W P L.ledgerJoint := by
  sorry -- B2DEF_LEAN E-phase sorry [unit TD-2, statement round 2 (v2)]

end LeanUrat.B2D
