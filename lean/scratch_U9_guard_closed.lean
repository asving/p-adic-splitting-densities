/- SCRATCH (HC-2 defs repairer, 2026-07-27): the CLOSURE CHECK for the
`scratch_U9_presentSeed_false.lean` refutation route, post the D5 DEFS-REPAIR
(blueprint §2.2 DC-1).

The old route fired `ZCSeedLaws.downsets_literal`'s ← direction at i = 0, j = 0
with threshold `β = w(B 0)/STR + 1` against `f = C(p^N)` — sound ONLY because the
transcription box-truncated the note's zero system. The repaired field carries the
CHART-COVERAGE GUARD. This file machine-checks that the guard is UNSATISFIABLE at
the route's site whenever the threshold exceeds the box's level cap (`β > N`):
the out-of-chart tower coordinate `(N, 0)` lies in the `(j = 0, β)` zero system
(`fineSlot 0 = 0`, `htH 0 (N,0) = N < β`) but not in `boxChart`'s image. Any
truncation-leak threshold is of this kind, so the ← direction can no longer fire
on a leaking system: the contradiction route is CLOSED. (For β ≤ N the guard may
hold, but there the box records the whole system and the iff is the note's own
C.1.5 identity — the honest law SEED-EXIST supplies over PrefSet histories.)
NOT part of the corpus; keep as the DC-1 compiled record. -/
import Mathlib
import LeanUrat.HC2.Defs

set_option linter.style.longLine false
set_option linter.style.header false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesJ
open Polynomial LeanUrat.Moves LeanUrat.MovesC LeanUrat.MovesD

variable {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]

/-- The refutation route's guard instance is FALSE for every threshold beyond the
box's level cap: the chart cannot cover the `(j = 0, β)` literal zero system once
`β > N`. -/
theorem guard_closed_beyond_box {n N : ℕ} (H : History p F) (h0 : 0 < H.nodes.length)
    {β : ℚ} (hβ : (N : ℚ) < β) :
    ¬ (∀ cc : Coord, (H.nodes[0]'h0).fineSlot cc.2 = 0 → H.htH 0 cc < β →
        ∃ c : Fin (n * N), boxChart n N c = cc) := by
  intro hcov
  -- the out-of-chart witness: tower coordinate (level N, base index 0)
  have hfs : (H.nodes[0]'h0).fineSlot ((N, 0) : Coord).2 = 0 := Nat.zero_div _
  have hht : H.htH 0 ((N, 0) : Coord) < β := by
    unfold History.htH
    simpa using hβ
  obtain ⟨c, hc⟩ := hcov (N, 0) hfs hht
  -- but boxChart's levels are < N: (c : ℕ)/n = N forces n*N ≤ c < n*N
  have h1 : ((c : ℕ) / n) = N := congrArg Prod.fst hc
  have hda := Nat.div_add_mod (c : ℕ) n
  have hlt := c.isLt
  rw [h1] at hda
  omega

end LeanUrat.MovesJ

#print axioms LeanUrat.MovesJ.guard_closed_beyond_box
