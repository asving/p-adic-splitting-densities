/-
Unit Sp.rankRadix [REV 2, F14 — fullBit defined in Defs; hypotheses and the
four-case disjunction spelled in full] — moves_ref: "(ii) The rank ρ(s) :=
( D,  tagord,  n − W,  1 − [s is full] ), tagord := 0/1/2 for
ROOT/POST-INC/POST-REC" + "it has at most |range(ρ)| ≤ n·3·n·2 = 6n² letters".
sketch: digit bounds D − 1 < n (B1 + WellTyped), tagord < 3, n − s.W < n (W ≥ 1),
fullBit < 2; both claims are mixed-radix arithmetic — unfold rankNat, `rcases`
the disjunction, `omega` per case. difficulty: medium.
-/
import LeanUrat.MovesSp.Defs

set_option linter.style.longLine false
set_option linter.style.header false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesSp

theorem rankNat_lt {n : ℕ} {s : Species} (hn : 1 ≤ n)
    (hc : Coherent s) (hb : Budget n s) : rankNat n s < 6 * n ^ 2 := sorry

theorem rankNat_lt_of_lex {n : ℕ} {s s' : Species}
    (hc : Coherent s) (hb : Budget n s) (hc' : Coherent s') (hb' : Budget n s')
    (h : s.D < s'.D ∨
         (s.D = s'.D ∧ tagord s.tag < tagord s'.tag) ∨
         (s.D = s'.D ∧ s.tag = s'.tag ∧ n - s.W < n - s'.W) ∨
         (s.D = s'.D ∧ s.tag = s'.tag ∧ s.W = s'.W ∧ fullBit s < fullBit s')) :
    rankNat n s < rankNat n s' := sorry

end LeanUrat.MovesSp
