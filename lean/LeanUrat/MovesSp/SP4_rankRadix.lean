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

/-- The tag ordinal is bounded by 2 (values 0/1/2 for ROOT/POST-INC/POST-REC). -/
private lemma tagord_le_two (t : Tag) : tagord t ≤ 2 := by
  cases t <;> decide

/-- The full-bit is a genuine bit: it is 0 or 1. -/
private lemma fullBit_le_one (s : Species) : fullBit s ≤ 1 := by
  unfold fullBit; split <;> decide

/-- If the high mixed-radix part strictly increases, so does `rankNat`; the lower
two digits (n − W and the full-bit) cannot overtake a one-unit gain of the high
part, because `(n − W)·2 + fullBit < 2·n` when `1 ≤ W` and `1 ≤ n`. -/
private lemma rank_lt_of_high {n : ℕ} {s s' : Species}
    (hHlt : (s.D - 1) * 3 + tagord s.tag < (s'.D - 1) * 3 + tagord s'.tag)
    (hn : 1 ≤ n) (hW1 : 1 ≤ s.W) (hbit : fullBit s ≤ 1) :
    rankNat n s < rankNat n s' := by
  have hlow : (n - s.W) * 2 + fullBit s < 2 * n := by omega
  have key : ((s.D - 1) * 3 + tagord s.tag + 1) * n
      ≤ ((s'.D - 1) * 3 + tagord s'.tag) * n := by
    have h1 : (s.D - 1) * 3 + tagord s.tag + 1 ≤ (s'.D - 1) * 3 + tagord s'.tag := by omega
    exact Nat.mul_le_mul h1 (le_refl n)
  unfold rankNat
  nlinarith [hlow, key, Nat.zero_le (n - s'.W), Nat.zero_le (fullBit s')]

theorem rankNat_lt {n : ℕ} {s : Species} (hn : 1 ≤ n)
    (hc : Coherent s) (hb : Budget n s) : rankNat n s < 6 * n ^ 2 := by
  have hD1 : 1 ≤ s.D := hc.1.1
  have hDn : s.D ≤ n := hb.1
  have hW1 : 1 ≤ s.W := hc.1.2.2.1
  have ht : tagord s.tag ≤ 2 := tagord_le_two _
  have hbit : fullBit s ≤ 1 := fullBit_le_one _
  have ha : s.D - 1 < n := by omega
  have hq : n - s.W < n := by omega
  unfold rankNat
  nlinarith [ha, hq, ht, hbit, hn, Nat.zero_le (s.D - 1), Nat.zero_le (n - s.W),
    Nat.zero_le (tagord s.tag), Nat.zero_le (fullBit s)]

theorem rankNat_lt_of_lex {n : ℕ} {s s' : Species}
    (hc : Coherent s) (hb : Budget n s) (hc' : Coherent s') (hb' : Budget n s')
    (h : s.D < s'.D ∨
         (s.D = s'.D ∧ tagord s.tag < tagord s'.tag) ∨
         (s.D = s'.D ∧ s.tag = s'.tag ∧ n - s.W < n - s'.W) ∨
         (s.D = s'.D ∧ s.tag = s'.tag ∧ s.W = s'.W ∧ fullBit s < fullBit s')) :
    rankNat n s < rankNat n s' := by
  have hD1 : 1 ≤ s.D := hc.1.1
  have hD1' : 1 ≤ s'.D := hc'.1.1
  have hW1 : 1 ≤ s.W := hc.1.2.2.1
  have hWn : s.W ≤ n := hb.2.2.2.2.2.2.2.2.1
  have hn : 1 ≤ n := le_trans hW1 hWn
  have ht2 : tagord s.tag ≤ 2 := tagord_le_two _
  have hbit : fullBit s ≤ 1 := fullBit_le_one _
  rcases h with hD | ⟨hDeq, htag⟩ | ⟨hDeq, htageq, hWlt⟩ | ⟨hDeq, htageq, hWeq, hblt⟩
  · -- s.D < s'.D : the high part strictly increases
    refine rank_lt_of_high ?_ hn hW1 hbit
    omega
  · -- s.D = s'.D, tagord s.tag < tagord s'.tag : the high part strictly increases
    refine rank_lt_of_high ?_ hn hW1 hbit
    omega
  · -- equal high part, n − s.W strictly less
    unfold rankNat
    rw [hDeq, htageq]
    generalize ((s'.D - 1) * 3 + tagord s'.tag) * n = X
    omega
  · -- equal high part and window, full-bit strictly less
    unfold rankNat
    rw [hDeq, htageq]
    generalize ((s'.D - 1) * 3 + tagord s'.tag) * n = X
    omega

end LeanUrat.MovesSp
