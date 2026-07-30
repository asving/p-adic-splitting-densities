/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.MovesU.DefsLedger

/-!
# IB-B4 — `Fintype`/`DecidableEq` for the real leg roster (bridge campaign BP1)

E-phase skeleton per `lean/notes/BRIDGE_BP1_INSTANCE_2026-07-30.md` §3.3 (†4b
neighborhood) / §4 group B (IB-B4): `Fintype (LegRoster C.T e)` +
`DecidableEq` (Classical).

TRANSCRIPTION RESOLUTION (recorded): the blueprint writes the statement at
`C.T`; `LegRoster` (DefsLedger.lean:422) is keyed to a bare
`T : MovesS.TableShape n`, so the unit is stated at that minimal generality —
IB-B8 consumes it at `C.T` by instantiation, losing nothing.

DEPS: none.  CONSUMERS: IB-B5 (`card_legRoster`), IB-B8 (`instL`).

PROOF SKETCH (R, ~20): Sigma-Fintype over the registered `TableShape.fin`/
`finO` instances; the `splitOuts` subtype is the Finset-coe carrier
(`Finset.attach` face); the continuing-position subtype is decidable via the
Bool equation `μ.status.isRight = true` (`Member.continuing`,
MovesS/Defs.lean:37).  Classical decidability where Finset membership on
`T.Out` lacks a `DecidableEq`.  Kept as NAMED defs, not global instances —
IB-B8 wires them explicitly into the `bridgeRegData` record (`instL`), per the
blueprint's assembly-order discipline.
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesU

/-- IB-B4 (Fintype): the real consumed β-leg roster of block e is finite —
    states × split outcomes × continuing member positions, each level a
    registered or Classical instance. -/
noncomputable def legRosterFintype {n : ℕ} (T : MovesS.TableShape n) (e : ℕ) :
    Fintype (LegRoster T e) := by
  unfold LegRoster; classical; infer_instance

/-- IB-B4 (DecidableEq, Classical — blueprint-prescribed). -/
noncomputable def legRosterDecEq {n : ℕ} (T : MovesS.TableShape n) (e : ℕ) :
    DecidableEq (LegRoster T e) :=
  Classical.decEq _

end LeanUrat.MovesU
