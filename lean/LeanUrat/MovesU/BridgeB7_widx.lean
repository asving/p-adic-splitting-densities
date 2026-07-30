/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.MovesU.DefsCarriers

/-!
# IB-B7 — the W-coefficient index carrier `BridgeWIdx` (bridge campaign BP1)

E-phase skeleton per `lean/notes/BRIDGE_BP1_INSTANCE_2026-07-30.md` §3.3 (the
`WIdx`/`shapeCount`/`Wcoef` lines of the `bridgeRegData` display) / §4 group B
(IB-B7): `WIdx` = the Finset-coe carrier of the shallow shape family, its
Fintype, and `card = Sh.card`.

DEPS: none.  CONSUMERS: IB-B8 (`WIdx`/`instW`/`WIdx_card`/`Wcoef`), IB-B12
(`bridge_W_pin`).

PROOF SKETCH (R, ~6): the carrier IS `↥C.Fam.Sh`, so `FinsetCoe.fintype` and
`Fintype.card_coe` close both obligations.
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesU

/-- IB-B7 (carrier): the W_Ŝ index at the tautological roster — one label per
    carried shallow shape (the Finset-coe subtype of `C.Fam.Sh`). -/
def BridgeWIdx {n : ℕ} (C : UCarriers n) : Type :=
  {Ŝ : MovesS.Shape C.T // Ŝ ∈ C.Fam.Sh}

/-- IB-B7 (Fintype): the attach/Finset-coe instance.  A NAMED def, not a
    global instance (IB-B8 wires it into `instW` explicitly). -/
noncomputable def bridgeWIdxFintype {n : ℕ} (C : UCarriers n) :
    Fintype (BridgeWIdx C) :=
  FinsetCoe.fintype _

/-- IB-B7 (cardinality law): the label count equals `C.Fam.Sh.card` — EXACTLY
    `RegPin.shape_pin`'s RHS at the tautological roster, so IB-B8's `WIdx_card`
    field IS this lemma.  Sketch: `Fintype.card_coe`. -/
theorem card_bridgeWIdx {n : ℕ} (C : UCarriers n) :
    @Fintype.card (BridgeWIdx C) (bridgeWIdxFintype C) = C.Fam.Sh.card := by
  sorry

end LeanUrat.MovesU
