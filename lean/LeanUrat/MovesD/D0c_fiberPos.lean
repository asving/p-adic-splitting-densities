/-
Unit D0c.fiber_pos  (MovesD campaign, E-phase)
moves_ref: "Theorem C(b) gives mass p^{−A(P̂)} > 0" (§D4-R L6 corollary).
deps: D0b.  difficulty: easy.
hypothesis_fields: none.
-/
import Mathlib
import LeanUrat.MovesD.Defs
import LeanUrat.MovesC.C6_thmC_b

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesD
open LeanUrat.Moves LeanUrat.MovesC

variable {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F] {n N m : ℕ}
  {pol : CanonPolicy p F} {P : Shape n}

/-- Every presented class fiber is nonempty (positive Theorem-C(b) mass). -/
theorem fiber_pos (S : Presented p F n N m pol P) (i : PrefIdx n pol P) :
    (S.fiber i).Nonempty := by
  -- The fiber is `S(η, ⊤) = (S.jet i).SHZ (topLocus p m)`; Theorem C(b) at Z = ⊤ gives
  -- `#S · p^(pins) = p^m > 0`, so the count is positive, so the fiber is nonempty.
  change ((S.jet i).SHZ (topLocus p m)).Nonempty
  have hZ : AdmissibleZ ((S.jet i).Sigma (reprOf i).nodes.length) (topLocus p m) := by
    intro c h
    simp [topLocus] at h
  have hkey := C6_thmC_b (S.jet i) (topLocus p m) hZ
  have hbox : 0 < boxMass p m := pow_pos (Fact.out : p.Prime).pos m
  have hcard : 0 < Nat.card ((S.jet i).SHZ (topLocus p m)) :=
    Nat.pos_of_ne_zero fun h => by
      rw [h, zero_mul] at hkey
      omega
  exact Set.nonempty_coe_sort.mp (Nat.card_pos_iff.mp hcard).1

end LeanUrat.MovesD
