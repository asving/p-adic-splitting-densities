/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.MovesT.Defs

/-! # T-D9 `shape_countable` — infrastructure for S-7's `ctbl`: finite tuples of
countable data; lists; subtype. PROVED. -/

set_option linter.style.longLine false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.unreachableTactic false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesT

open Polynomial LeanUrat.Moves LeanUrat.MovesC LeanUrat.MovesD

instance : Countable ReadSpecies := by
  have hinj : Function.Injective (fun s : ReadSpecies => match s with
      | .root => (0 : Fin 3) | .increment => 1 | .recentering => 2) := by
    intro a b h
    cases a <;> cases b <;> simp_all
  exact hinj.countable

instance : Countable ShapeRead := by
  have hinj : Function.Injective (fun R : ShapeRead =>
      (R.species, R.e, R.h, R.g, R.μ, R.a, R.s0, R.wSide, R.Dwidth, R.ustar,
        R.gam, R.w, R.monicTop)) := by
    intro R R' h
    cases R; cases R'
    simp_all
  exact hinj.countable

instance : Countable ShapePrefix := by
  have hinj : Function.Injective (fun P : ShapePrefix => P.reads) := by
    intro P P' h
    cases P; cases P'
    simp_all
  exact hinj.countable

instance (n : ℕ) : Countable (Shape n) := Subtype.countable

end LeanUrat.MovesT
