/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.HC1.G4_caseKGate

/-!
# HC1.G5_spanGate — the F₉ a = 2 span-pricing gate (the F3-2 check)

moves_ref: MOVES 9580–9582 ("the full position a = 2 gives each re-based branch
𝔸_δ = F₉, i.e. a_δ = 2 ≠ δ·a = 4"); MOVESR_AUDIT_FABLE3 F3-2. deps: G4's F9
object. The ADDITIVE closure of the two slot-image lines {c·1} ∪ {c·τ} is all of
F₉ (card 9 = 3², aDim = 2), while any single line prices card 3. difficulty: easy.
hyp: none.
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

namespace LeanUrat.HC1

/-- Unit G5: span pricing over F₉ — two independent F₃-lines span the full piece;
one line alone prices 3. -/
theorem G5_spanGate :
    (AddSubgroup.closure ({x : F9 | ∃ c : ZMod 3, x = (c, 0)} ∪
        {x : F9 | ∃ c : ZMod 3, x = (0, c)}) = ⊤) ∧
    Nat.card ↥(AddSubgroup.closure {x : F9 | ∃ c : ZMod 3, x = (c, 0)}) = 3 ∧
    Nat.card ↥(AddSubgroup.closure {x : F9 | ∃ c : ZMod 3, x = (0, c)}) = 3 ∧
    Nat.card F9 = 3 ^ 2 := by
  sorry

end LeanUrat.HC1

#print axioms LeanUrat.HC1.G5_spanGate
