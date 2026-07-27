/-
Unit XA.9 ind2Region  [E-phase: stated, body sorry]
moves_ref: the table's ind(S) column, EQUALITY (doubled per D2).
deps: XA.3–XA.8. difficulty: MEDIUM.
-/
import LeanUrat.MovesX.Defs
import LeanUrat.MovesX.XA1
import LeanUrat.MovesX.XA3
import LeanUrat.MovesX.XA4
import LeanUrat.MovesX.XA5
import LeanUrat.MovesX.XA6
import LeanUrat.MovesX.XA7a
import LeanUrat.MovesX.XA7b
import LeanUrat.MovesX.XA8

namespace LeanUrat.MovesX
set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

theorem ind2Region {n : ℕ} (ν : XNode n) (hc : ν.continuing) :
    ind2 ν = 2 * ν.region.card ∧ ((rowOf ν = .T1 ∨ rowOf ν = .T2) → 1 ≤ ind2 ν) := by
  have hsel : ν.sel ≠ none := by
    intro h
    simp [XNode.continuing, h] at hc
  rcases hrow : rowOf ν with _ | _ | _ | _ | _
  · -- T1: ℓ ≥ 2 row.  ind2 = ℓ·(ehℓ+1−e−h) = 2·|region| by latGen (XA.7b);
    -- positivity from the T1 witness (XA.3), which pins |region| ≥ 1.
    have hmain : ind2 ν = 2 * ν.region.card := by
      simp only [ind2, hrow, XNode.region]
      rw [latGen ν.s0 ν.u0 ν.e ν.h ν.ell ν.epos ν.hpos ν.ellpos ν.hcop]
    refine ⟨hmain, fun _ => ?_⟩
    have hw := (t1Witness ν hrow).2
    rw [hmain]; omega
  · -- T2: ℓ = 1 row.  ind2 = (e−1)(h−1) = 2·|region| by lat1 (XA.6);
    -- positivity from the T2 witness (XA.5), which gives 2 ≤ (e−1)(h−1).
    have hell : ν.ell = 1 := ((rowTotal ν).2.2.1.mp hrow).2.1
    have hmain : ind2 ν = 2 * ν.region.card := by
      simp only [ind2, hrow, XNode.region, hell]
      rw [lat1 ν.s0 ν.u0 ν.e ν.h ν.epos ν.hpos ν.hcop]
    refine ⟨hmain, fun _ => ?_⟩
    have hw := (t2Witness ν hrow).2.1
    simp only [ind2, hrow]
    omega
  · -- T3: ind2 = 0 = 2·0 = 2·|region| by t34Zero (XA.8); antecedent false.
    have hz := t34Zero ν (Or.inl hrow)
    refine ⟨by rw [hz.2, hz.1], fun h => ?_⟩
    rcases h with h | h <;> exact absurd h (by decide)
  · -- T4: same as T3.
    have hz := t34Zero ν (Or.inr hrow)
    refine ⟨by rw [hz.2, hz.1], fun h => ?_⟩
    rcases h with h | h <;> exact absurd h (by decide)
  · -- T5: excluded — a continuing node has sel ≠ none, but rowOf = T5 forces sel = none.
    exact absurd ((rowTotal ν).1.mp hrow) hsel

end LeanUrat.MovesX
