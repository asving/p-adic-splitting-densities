/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.HC1.R1_LSTStmt

/-!
# HC1.R3_DOMStmt — `DOMStmt'`: the displayed CONCLUSION (G3-3)

moves_ref: MOVES 3647–3651; MOVESR_AUDIT_FABLE3 G3-3. `DomData` stays the note's
proof-input record (MovesC) but is no longer the statement. difficulty: easy.
hyp: open REL.1 clause.
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

namespace LeanUrat.HC1

/-- **`DOMStmt'`** (R3): interior line domination — the DISPLAYED conclusion
`∀ m < i, ∀ b < interiorEnd H i, line_i(b) ≥ line_m(b)` (per-i interiorEnd). -/
def DOMStmt' (p : ℕ) [Fact p.Prime] (K : CarrierPackR p) : Prop :=
  ∀ (H : K.Hist) (i m b : ℕ), m < i → b < K.interiorEnd H i →
    (K.lines H m).at b ≤ (K.lines H i).at b

end LeanUrat.HC1

#print axioms LeanUrat.HC1.DOMStmt'
