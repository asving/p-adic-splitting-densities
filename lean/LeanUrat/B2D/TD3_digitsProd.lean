/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.B2D.TDDefs

/-!
# B2D/TD3_digitsProd — `DigitsProdLaw` at the ledger instance
  [B2DEF_LEAN unit TD-3; wave 1 — THE HARDEST HOLE, front 1]

Blueprint §5 TD-3 (+ the §5 hardest-hole call, [R2-G2 fold]). moves_ref: §B2-DEF
D.3(e)(ii.3)/(ii.4), D.8 (BOX), D.11 attainable product. deps: TD-0.
difficulty: **hardest**.

Proof skeleton (blueprint verbatim, transposed to the TD-0 clauses): (ii.3) =
`slots_disjoint`/`parent_interior_disjoint` (distinct pins hit disjoint leaf
sets; T9's display) + (ii.4) = `pinned_forced` (unit-diagonal: each pinned leaf
forced given predecessors — T12's display) ⟹ the level-N box splits as a product
over slot blocks (`member_split` + the support clauses; the parent factor is 1 by
`pinned_forced`) ⟹ card = ∏ (`semantics` + `slot_sem`/`slotDigits_sem`
`blockCount`s). The shallow-height regime rides the ATTAINABLE product (T11
dichotomy, discharged inside TD-0's `slotDigits_sem` counts) — NEVER full
alphabets (D¹¹c: the uniform field-alphabet display is FALSE at shallow heights).
Falsifier N-TD1 (shallow-height harness) gates this statement BEFORE proof
effort. E-phase file: statement only.
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false

namespace LeanUrat.B2D

open LeanUrat.Scaffold LeanUrat.Scaffold.HDischarge.H2 LedgerStratumData

variable {D : CensusData} {W : WindowDatum D} {P : ParentShape D W}

/-- **TD-3**: the (F) product-box face at the ledger instance — fiberwise
per-slot factorization of the prescribed-digit counts (on-line digit counts ×
off-line height counts). -/
theorem ledger_digitsProd (L : LedgerStratumData D W P) (hL : L.LedgerLawful)
    (hscope : LedgerScope W P) (hclean : LedgerClean D W P L.N) :
    DigitsProdLaw W P L.ledgerJoint := by
  sorry -- B2DEF_LEAN E-phase sorry [unit TD-3]

end LeanUrat.B2D
