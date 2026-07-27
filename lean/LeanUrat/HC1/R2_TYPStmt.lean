/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.HC1.R1_LSTStmt

/-!
# HC1.R2_TYPStmt — `TYPStmt'` over the re-keyed carriers

moves_ref: MOVES 3801–3824; 9401–9406 (walk item (i): additive on digit blocks;
F_δ-linearity stays walked, NOT asserted). REPAIRS: conjunct 1 = the COMPOSITE's
additivity in the digit tuple (F3-1 — never the jet map on box points); conjunct 2
= SPAN pricing (F3-2 — the Fable-3 displayed form on the slot-image closure).
difficulty: medium (statement unit; quantifier care). hyp: open REL.1 clause.
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

namespace LeanUrat.HC1

open scoped Classical

/-- **`TYPStmt'`** (R2): TYP over the abstract carriers — additivity of the
composite in the digit TUPLE, and span pricing `#(closure of slot images) =
p^aDim`. -/
def TYPStmt' (p : ℕ) [Fact p.Prime] (K : CarrierPackR p) : Prop :=
  ∀ (H : K.Hist) (b : ℕ) (γ' : ℚ),
    (∀ x y : K.Coord → K.Digit,
      K.G.inγ γ' (K.slotCoeff H b (x + y))
        = K.G.inγ γ' (K.slotCoeff H b x) + K.G.inγ γ' (K.slotCoeff H b y)) ∧
    (Nat.card ↥(AddSubgroup.closure
        (⋃ c ∈ K.lvl H b γ', Set.range fun y : K.Digit =>
          K.G.inγ γ' (K.slotCoeff H b (Pi.single c y))))
      = p ^ K.aDim H b γ')

end LeanUrat.HC1

#print axioms LeanUrat.HC1.TYPStmt'
