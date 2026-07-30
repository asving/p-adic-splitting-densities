/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.MovesU.Defs
import LeanUrat.OM.QuotientBox

/-!
# IB-A8 — the level-0 edge: `monicBox p 0 n` is EMPTY, `Box p n 0` is a singleton

E-phase skeleton per `lean/notes/BRIDGE_BP1_INSTANCE_2026-07-30.md` §3.2 (†2, the
"AT N = 0 THE EQUIV IS FALSE" edge) / §4 group A (IB-A8).

INFORMAL STATEMENT: at level N = 0 the coefficient ring `ZMod (p^0) = ZMod 1` is
the trivial ring, so (a) every polynomial over it is 0 with natDegree 0 ≠ n, hence
the monic degree-n box `QuotientBox.monicBox p 0 n` is EMPTY for n ≥ 1
(`monicBox_empty_of_level0`), while (b) the coefficient box `Box p n 0` is a
SINGLETON (`box0_unique`).  This is exactly why (†2)'s `boxPolyEquiv` (IB-A9)
carries the `0 < N` guard — the two sides genuinely differ at N = 0 (the same
mechanism as `OM.RealInstanceV2.stratumCount_level0`, the guard discipline of
`TreePin.chart`, round-3 CRITICAL 1).

DEPS: — (leaf unit; IB-A9 consumes it as edge documentation only).

PROOF SKETCH (blueprint: "trivial-ring polynomial ext — replay
`RealInstanceV2.stratumCount_level0`'s core", OM/RealInstanceV2.lean:61–74):
* `monicBox_empty_of_level0`: `Subsingleton (ZMod (p ^ 0))` via
  `ZMod.subsingleton_iff.mpr (pow_zero _)`; any member's polynomial is 0 by
  `Polynomial.ext fun k => Subsingleton.elim _ _`; then `natDegree_zero` reads
  0 = n against 1 ≤ n — `omega`.
* `box0_unique`: `funext` + `Subsingleton.elim` in the trivial ring.

TRANSCRIPTION RESOLUTIONS (recorded per the E-phase charge): (i) "n ≥ 1" is
transcribed as `1 ≤ n`; (ii) "Box p n 0 is a singleton" is transcribed as the
two-point equality `box0_unique : ∀ f g, f = g` (the box is inhabited outright —
`fun _ => 0` — so uniqueness is the only content; no `Unique` instance is
packaged, none is consumed downstream); (iii) `[Fact p.Prime]` is NOT carried:
the level-0 collapse is ring-trivial for every p.
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesU

/-- IB-A8(a) — (†2)'s level-0 edge, polynomial side: the monic degree-n box over
    the trivial ring `ZMod (p ^ 0)` is EMPTY for n ≥ 1 (every polynomial is 0,
    natDegree 0 ≠ n). -/
theorem monicBox_empty_of_level0 (p n : ℕ) (hn : 1 ≤ n) :
    IsEmpty (OM.QuotientBox.monicBox p 0 n) := by
  constructor
  rintro ⟨f, hmon, hdeg⟩
  haveI : Subsingleton (ZMod (p ^ 0)) := ZMod.subsingleton_iff.mpr (pow_zero _)
  have hf : f = 0 := Polynomial.ext fun k => Subsingleton.elim _ _
  rw [hf, Polynomial.natDegree_zero] at hdeg
  omega

/-- IB-A8(b) — (†2)'s level-0 edge, coefficient side: the level-0 coefficient box
    is a singleton (all points equal in `Fin n → ZMod (p ^ 0)`). -/
theorem box0_unique (p n : ℕ) (f g : Box p n 0) : f = g := by
  haveI : Subsingleton (ZMod (p ^ 0)) := ZMod.subsingleton_iff.mpr (pow_zero _)
  funext i
  exact Subsingleton.elim _ _

end LeanUrat.MovesU
