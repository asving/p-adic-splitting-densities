/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.MovesT.Defs

/-! # T-C5 `nsZ_free` [hard; pre-approved split C5a/C5b] — the (ns-null) mechanism
(MOVES 7216–7229 (i)/(iii)): construct Z_M explicitly from the block/height grid;
freeness via `hzc.inclusive_top`; rim leads never interior via `hzc.rim_sep`; the
ladder count from `hzc.slot0_grid`. THE ONE SUBSTANTIVE NEW PROOF of the C-layer.
This theorem also DISCHARGES `NsLumpFamily.slot0` at every presented instance.
REV 9 (Codex-8 crit 5): `IsLumpLocus` carries BOTH conjuncts — the explicit
construction sets `solve := fun _ _ => 0`, discharging the literal-zero conjunct. -/

set_option linter.style.longLine false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesT

open Polynomial LeanUrat.Moves LeanUrat.MovesC LeanUrat.MovesD

variable {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
variable {n N m : ℕ} {pol : CanonPolicy p F}

theorem nsZ_free {H : History p F} (J : JetSetup H n N m) (hzc : ZCPack J)
    (M : ℕ) (hM : M₀ J ≤ M) (hMcap : M ≤ Mlev J N) :
    ∃ Z : Locus p m, AdmissibleZ (J.Sigma H.nodes.length) Z ∧
      IsLumpLocus J M Z ∧ M - M₀ J ≤ pinCount Z := by
  sorry

end LeanUrat.MovesT
