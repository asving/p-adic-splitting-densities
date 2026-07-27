/-
Unit XD.1 nsFreeDec (+ capTotal, maxHNil)  [E-phase: stated, bodies sorry]
moves_ref: DOMAIN CONVENTIONS (predicate exclusion; cap 0-convention; max h(∅) = 0).
deps: Defs. difficulty: EASY. Three declarations per the blueprint's unit spec.
-/
import LeanUrat.MovesX.Defs

namespace LeanUrat.MovesX
set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

/-- (τ-ns)-freeness of a branch is decidable (from `XCtx.nsDec` along the finite
history). -/
instance nsFreeDec {n p : ℕ} [Fact p.Prime] (C : XCtx n p) (f : MonicBox n p) :
    DecidablePred (NsFreeB C (f := f)) :=
  sorry

/-- The cap 0-convention is TOTAL: `capHB` is 0 off `capDetectable` and the branch's
own cap on it. -/
theorem capTotal {n p : ℕ} [Fact p.Prime] (C : XCtx n p) (f : MonicBox n p)
    (b : C.Branch f) :
    (¬ C.capDetectable b → capHB C b = 0) ∧
    (C.capDetectable b → capHB C b = C.detCap b) := by
  sorry

/-- max h(∅) = 0 and Σ h(∅) = 0. -/
theorem maxHNil {n : ℕ} : maxH ([] : XHistory n) = 0 ∧ sumH ([] : XHistory n) = 0 := by
  sorry

end LeanUrat.MovesX
