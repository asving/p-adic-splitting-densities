/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.MovesU.DefsCarriers

/-!
# IB-B6 — the per-cell J index carrier `BridgeJIdx` (bridge campaign BP1)

E-phase skeleton per `lean/notes/BRIDGE_BP1_INSTANCE_2026-07-30.md` §3.3 (the
`JIdx` line of the `bridgeRegData` display + (†4c)/(†4d)) / §4 group B (IB-B6):
the JIdx carrier def + Fintype + `card_JIdx = Σ τ, Σ o ∈ splitOuts, card cells`.

TRANSCRIPTION RESOLUTION (recorded): the blueprint display leaves the innermost
carrier as `{c // c ∈ (C.MS.cells e.1 τ o.1).?}`; per (†4c)'s prescription
("`Finset.attach` on cells is the cleanest carrier choice — pick `JIdx` to make
this proof shortest") it is resolved to the Finset-coe subtype
`{c // c ∈ C.MS.cells e τ o.1}` — definitionally `↥(C.MS.cells e τ o.1)`, the
attach carrier.

DEPS: none.  CONSUMERS: IB-B8 (`JIdx`/`instJ`/`JIdx_card`/`Jcell`), IB-B11
(`bridge_Jcell_pin`).

PROOF SKETCH (R, ~25): same shape as IB-B5 one level simpler —
`Fintype.card_sigma` twice, then `Fintype.card_coe` on the cells Finset;
no Prop/Bool coercion anywhere.
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesU

/-- IB-B6 (carrier): the per-cell J index of block e at the tautological
    roster — one label per (state, split outcome, branching cell of that
    outcome), the innermost level the attach/Finset-coe carrier of
    `MeasuredSide.cells` (resolution note in the file header). -/
def BridgeJIdx {n : ℕ} (C : UCarriers n) (e : ℕ) : Type :=
  Σ (τ : C.T.State e) (o : {o : C.T.Out e τ // o ∈ MovesS.splitOuts C.T e τ}),
    {c : C.MS.Cell e τ // c ∈ C.MS.cells e τ o.1}

open Classical in
/-- IB-B6 (Fintype): finite — states × split outcomes × cells, each level a
    registered (`TableShape.fin`/`finO`, `MeasuredSide.finC`) or Classical
    instance.  A NAMED instance; IB-B8 still wires it into `instJ`
    explicitly. -/
noncomputable instance bridgeJIdxFintype {n : ℕ} (C : UCarriers n) (e : ℕ) :
    Fintype (BridgeJIdx C e) := by
  unfold BridgeJIdx; infer_instance

/-- IB-B6 (cardinality law, †4d cell case): the label count at
    `bridgeJIdxFintype` equals the roster's branching-cell population — EXACTLY
    `RegPin.cell_pin`'s RHS (DefsLedger.lean:513) at the tautological roster,
    so IB-B8's `JIdx_card` field IS this lemma. -/
theorem card_bridgeJIdx {n : ℕ} (C : UCarriers n) (e : ℕ) :
    @Fintype.card (BridgeJIdx C e) (bridgeJIdxFintype C e)
      = ∑ τ : C.T.State e, ∑ o ∈ MovesS.splitOuts C.T e τ,
          (C.MS.cells e τ o).card := by
  sorry

end LeanUrat.MovesU
