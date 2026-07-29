/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.MovesT.Defs
import LeanUrat.MovesT.D9_shapeCtbl

/-! # T-D10 `classTree_countable` — MovesS §W4-SYNC S-7: `ClassTree` (Defs §2.9 — the
REV-5 key-unique `Finset` carrier, §0 record #12 dead BY CARRIER) is countable:
countable-of-finite fibers over countable Shape data. -/

set_option linter.style.longLine false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesT

open Polynomial LeanUrat.Moves LeanUrat.MovesC LeanUrat.MovesD

variable {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]

instance (n : ℕ) (pol : CanonPolicy p F) : Countable (ClassTree n pol) := by
  sorry

end LeanUrat.MovesT
