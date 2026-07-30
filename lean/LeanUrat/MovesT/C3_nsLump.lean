/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.MovesT.Defs

/-! # T-C3 `ns_lump` — (ns-lump) CAP-APPROXIMABILITY (MOVES 7203–7209): monotone with
the class as the intersection. "PROVED (a re-reading of B(iii), no new content)" —
antitonicity and the intersection identity PROVED from `vanish`+`interior_mono`+`tie`
(non-circular; the `tie` field is the standing-perimeter B(iii) identification, owner
D4R0K, typed not re-proved). PROVED (E-phase prove-now set). -/

set_option linter.style.longLine false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesT

open Polynomial LeanUrat.Moves LeanUrat.MovesC LeanUrat.MovesD

variable {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
variable {n N m : ℕ} {pol : CanonPolicy p F}

theorem ns_lump (T : TreeModel p F n N m pol) {H : History p F}
    (J : JetSetup H n N m) (Lf : NsLumpFamily T J) :
    (∀ M M', M ≤ M' → Lf.L M' ⊆ Lf.L M) ∧
    nsClass T H = {x | T.mem (some H) x} ∩ ⋂ M, Lf.L M := by
  constructor
  · intro M M' hMM' x hx
    rw [Lf.vanish]
    intro bl hbl
    exact (Lf.vanish M' x).mp hx bl (Lf.interior_mono M M' hMM' hbl)
  · ext x
    constructor
    · rintro ⟨hm, hnc⟩
      exact ⟨hm, Set.mem_iInter.mpr ((Lf.tie x hm).mp hnc)⟩
    · rintro ⟨hm, hL⟩
      exact ⟨hm, (Lf.tie x hm).mpr (Set.mem_iInter.mp hL)⟩

end LeanUrat.MovesT
