/-
Unit C0.digitSystemMass
moves_ref: §C.0 BLOCK CONVENTION; D.3(e)(ii)/D.11 count law

Specialization of the accepted `L2_P6ii` `DigitSystem` count `|α|^{n−k}` to `α = ZMod p`
(`Nat.card (ZMod p) = p`, `p` prime). Reuses `LeanUrat.Moves.L2_P6ii` verbatim.
-/
import LeanUrat.MovesC.Defs
import LeanUrat.Moves.L2_P6ii_R3

set_option linter.style.longLine false
set_option linter.style.header false

namespace LeanUrat.MovesC

open LeanUrat.Moves

variable {p : ℕ} [Fact p.Prime]

theorem C0_digitSystemMass {m : ℕ} (D : Locus p m) : D.mass = p ^ (m - D.numPinned) := by
  haveI : NeZero p := ⟨(Fact.out (p := p.Prime)).pos.ne'⟩
  unfold Locus.mass
  rw [LeanUrat.Moves.L2_P6ii m D, Nat.card_zmod]

end LeanUrat.MovesC
