/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.MovesT.Defs

/-! # T-V5 `tau_disjoint` — τ mutual exclusivity by domain stratification (MOVES
7104–7111): (τ-irr) verdicts attach to members of a NONEMPTY branch set; (τ-ns)
demands the branch set EMPTY. The hen/chain disjointness is BY TYPE (hen lives in
`henV`/`henPayload`, never on `chains`) — no theorem needed. PROVED. -/

set_option linter.style.longLine false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesT

open Polynomial LeanUrat.Moves LeanUrat.MovesC LeanUrat.MovesD

variable {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
variable {n N m : ℕ} {pol : CanonPolicy p F}

theorem tau_disjoint (T : TreeModel p F n N m pol) (o : Option (History p F))
    (ν : Node p F) (x : Box p m) (h : IrrHaltsAsChild T o ν x) :
    ¬ NsHalts T o x :=
  fun hns => hns.2 ν h.2.1

end LeanUrat.MovesT
