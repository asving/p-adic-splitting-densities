/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.HC1.R1_LSTStmt

/-!
# HC1.R4_SecB1Stmt — `SecB1Stmt'`: slot-coefficient additivity at the graded-piece
level (G3-1)

moves_ref: MOVES 3799–3801; MOVESR_AUDIT_FABLE3 G3-1 (the model-commitment
removed: additivity is stated AT WEIGHT in the piece, not of the raw coefficient
map). difficulty: easy. hyp: open REL.1 clause.
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

namespace LeanUrat.HC1

/-- **`SecB1Stmt'`** (R4): `inγ γ (slotCoeff (x+y)) = inγ γ (slotCoeff x) +
inγ γ (slotCoeff y)` at weight — the stage-carrier law restated at the
graded-piece level. -/
def SecB1Stmt' (p : ℕ) [Fact p.Prime] (K : CarrierPackR p) : Prop :=
  ∀ (H : K.Hist) (b : ℕ) (γ : ℚ) (x y : K.Coord → K.Digit),
    K.G.inγ γ (K.slotCoeff H b (x + y))
      = K.G.inγ γ (K.slotCoeff H b x) + K.G.inγ γ (K.slotCoeff H b y)

end LeanUrat.HC1

#print axioms LeanUrat.HC1.SecB1Stmt'
