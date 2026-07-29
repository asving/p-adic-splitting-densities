/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.MovesT.Defs
import LeanUrat.MovesD.NPv_npid

/-! # T-D7 `np_id` [hard, split D7a/D7b] — W4-4(a) VERBATIM (the ∀-jet quantifier is
the CONTRACT'S — REV 2, Codex 24) + `np_id_pin` (REV 7, W4-SYNC delta 6): the
AS-BUILT consumption target for MovesD's `NPIDPin`/`NthrSup`/`noteNP`/
`D4R4_all_noteRange` (imported BY NAME). `bandLevels`/`transportedLevels` are Defs
carriers (CLOSED over the built band vocabulary). -/

set_option linter.style.longLine false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesT

open Polynomial LeanUrat.Moves LeanUrat.MovesC LeanUrat.MovesD

variable {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
variable {n N m : ℕ} {pol : CanonPolicy p F}

/-- D7a/D7b: NP-ID — the transported level support IS the shape-side band grid. -/
theorem np_id {P : Shape n} (i : PrefIdx n pol P)
    (J : JetSetup (reprOf i) n N m) :
    transportedLevels J (topLocus p m) = bandLevels (P : ShapePrefix) n := by
  sorry

/-- the BUILT pin supplied (REV 7): W4-4's as-built form. -/
theorem np_id_pin {P : Shape n}
    (Nthr : PrefIdx n pol P → ℕ)
    (hNthr : ∀ (i : PrefIdx n pol P) (J : JetSetup (reprOf i) n N m),
      Nthr i = 1 + (transportedLevels J (topLocus p m)).sup Prod.fst) :
    NPIDPin n pol P Nthr := by
  sorry

end LeanUrat.MovesT
