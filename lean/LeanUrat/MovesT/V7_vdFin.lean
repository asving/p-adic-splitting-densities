/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.MovesT.Defs

/-! # T-V7 `vdAt_finite` — W4-2's `hVfin` instantiable at V := VdAt n, AND the
singleton-V degeneracy REJECTED (W4-2(b)(i)): at d ≥ 2, {(1,d)} ≠ {(d,1)}. -/

set_option linter.style.longLine false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesT

open Polynomial LeanUrat.Moves LeanUrat.MovesC LeanUrat.MovesD

/-- a verdict of deg d has ≤ d pairs, each in [1,d]²; inject into a finite carrier. -/
instance vdAt_finite (d : ℕ) : Finite (VdAt d) := by
  sorry

theorem vdAt_nontrivial (d : ℕ) (hd : 2 ≤ d) : 1 < Nat.card (VdAt d) := by
  sorry

end LeanUrat.MovesT
