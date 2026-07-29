/-  MovesV unit V6-3a `blk2_table` — s_blk2 closed forms + PART-1 + the
    char-2 recount convention as polynomial identities. -/
import LeanUrat.MovesV.DefsGate

set_option linter.style.longLine false
set_option linter.style.header false

namespace LeanUrat.MovesV
open Polynomial

theorem blk2_part1 : Tsplit + Tinert + Tdbl = X * (X - 1) := by
  apply Polynomial.funext
  intro x
  simp [Tsplit, Tinert, Tdbl]
  ring

theorem blk2_degrees : Tsplit.natDegree ≤ 2 ∧ Tinert.natDegree ≤ 2 ∧
    Tdbl.natDegree ≤ 2 ∧ Tw2.natDegree ≤ 2 ∧ Tvv.natDegree ≤ 2 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [Tsplit, Tinert, Tdbl, Tw2, Tvv] <;> compute_degree <;> norm_num

theorem tw2_tvv : Tw2 = Tdbl ∧ Tvv = Tdbl ^ 2 := by
  constructor
  · rfl
  · apply Polynomial.funext
    intro x
    simp [Tvv, Tdbl]

end LeanUrat.MovesV
