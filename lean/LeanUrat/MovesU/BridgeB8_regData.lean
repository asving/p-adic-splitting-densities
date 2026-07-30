/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.MovesU.BridgeB2_stateNe
import LeanUrat.MovesU.BridgeB3_act
import LeanUrat.MovesU.BridgeB4_legRosterFintype
import LeanUrat.MovesU.BridgeB5_cardLegRoster
import LeanUrat.MovesU.BridgeB6_jidx
import LeanUrat.MovesU.BridgeB7_widx
import LeanUrat.MovesU.BridgeB9_diteFields

/-!
# IB-B8 — `bridgeRegData`: the tautological roster (bridge campaign BP1)

E-phase skeleton per `lean/notes/BRIDGE_BP1_INSTANCE_2026-07-30.md` §3.3 (the
full `bridgeRegData` display, transcribed verbatim) / §4 group B (IB-B8): the
FULL `RegData p` record assembly in ONE literal — no postponed fields (the
post-Codex finding-3 assembly order: the two dite fields are IB-B9's standalone
defs, consumed here; the pin LEMMAS (IB-B11/B12/B13) are stated over this def
by other units, and IB-B10 wires them into the `RegPin` record LAST).

DESIGN PRINCIPLE (§3.3, the r_is_solve pattern): `RegData` is free data +
`RegPin` equates it to the real §S objects; constructing D FROM those objects
makes every pin `rfl`/`Equiv.refl`/proof-irrelevance.

SIGNATURE (per the display + post-Codex finding 2): `hn : 2 ≤ n` feeds
`instNe` (the top block ⟨1, _⟩ exists — at n = 0 `Block` is EMPTY and `hne` is
vacuous, so `hn` is LOAD-BEARING); `hne : HStateNe n C` (IB-B2's factored
sentence = the Q3-ratified `BridgePre.hStateNe` premise) feeds
`instBiNe`/`blockDim_pos`.

DEPS: IB-B1 (`one_mem_consumedDeltas` — ANOTHER CLUSTER's unit; its (†4a)
obligation is carried here as the file's one deliberate `sorry`, to be wired
when IB-B1 lands), IB-B2 (`HStateNe`), IB-B3 (`bridgeAct`), IB-B4
(`legRosterFintype`), IB-B5 (`card_legRoster`), IB-B6 (`BridgeJIdx` family),
IB-B7 (`BridgeWIdx` family), IB-B9 (`bridgeBsplit`/`bridgeBetaLeg`).
CONSUMERS: IB-B10..B17, IB-F4 (`mkUInstance`).

PROOF SKETCH (R, ~35, mostly record lines): every count/law field is `rfl`, a
wired IB-B4/B5/B6/B7 lemma, or a one-line consequence of `hn`/`hne`;
`one_mem_depthSet` is IB-B1's iterate-monotone seed membership.
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesU

/-- IB-B8: THE TAUTOLOGICAL ROSTER (†4) — `RegData p` built FROM the carried §S
    corpus, so that every `RegPin` pin holds by `rfl`/`Equiv.refl`/proof
    irrelevance (§3.3's display, verbatim): depths = the consumed-deltas
    closure; blocks = the working degrees `e ∈ [1, n]` with the REAL table
    states as row indices; K/bterm/bsplit/iota = the real `Kmat`/assembled
    `bTerm` rows/IB-B9's dite split rows/the real ι; J/W/leg families = the
    attach carriers of the real cells/shapes/`LegRoster` with the real
    `jPCell`/`WshP`/IB-B9 β values; act = IB-B3's `bridgeAct`. -/
noncomputable def bridgeRegData {n : ℕ} (hn : 2 ≤ n) (C : UCarriers n)
    (hne : HStateNe n C) (p : ℕ) : RegData p :=
  let ds : Finset ℕ :=
    (MovesS.consumedDeltas C.T C.Fam).image (fun d : ℕ+ => (d : ℕ))
  { depthSet := ds
    -- (†4a): `1 ∈ consumedDeltas` is IB-B1's lemma (another cluster's unit);
    -- carried as this file's one deliberate placeholder until IB-B1 lands.
    one_mem_depthSet := sorry
    Pool := ds.image (p ^ ·)
    pool_eq := rfl
    Block := {e : ℕ // e ∈ Finset.Icc 1 n}
    instB := FinsetCoe.fintype _
    instNe := ⟨⟨1, Finset.mem_Icc.mpr ⟨le_rfl, by omega⟩⟩⟩
    bidx := fun e => C.T.State e.1
    instBi := fun e => C.T.fin e.1
    instBd := fun e => C.T.deq e.1
    instBiNe := fun e => hne e.1 e.2
    blockDim := fun e => Fintype.card (C.T.State e.1)
    blockDim_pos := fun e => Fintype.card_pos_iff.mpr (hne e.1 e.2)
    bidx_card := fun _ => rfl
    K := fun e => MovesS.Kmat C.T C.RB e.1 (C.hK e.1 e.2)
    bterm := fun e i =>
      ∑ σ' ∈ MovesS.verdictImage C.T e.1 i, MovesS.bTerm C.T C.RB e.1 σ' i
    bsplit := fun e i => bridgeBsplit C e i
    iota := fun e i => C.RB.ι e.1 i
    cellCount := fun e =>
      ∑ τ : C.T.State e.1, ∑ o ∈ MovesS.splitOuts C.T e.1 τ,
        (C.MS.cells e.1 τ o).card
    JIdx := fun e => BridgeJIdx C e.1
    instJ := fun e => bridgeJIdxFintype C e.1
    JIdx_card := fun e => card_bridgeJIdx C e.1
    Jcell := fun e j => (C.RB.jPCell e.1 j.1 j.2.2.1).val
    shapeCount := C.Fam.Sh.card
    WIdx := BridgeWIdx C
    instW := bridgeWIdxFintype C
    WIdx_card := card_bridgeWIdx C
    Wcoef := fun Ŝ => (C.chain.WshP Ŝ.1).val
    legCount := fun e =>
      ∑ τ : C.T.State e.1, ∑ o ∈ MovesS.splitOuts C.T e.1 τ,
        (C.T.odata e.1 τ o).c
    legIdx := fun e => LegRoster C.T e.1
    instL := fun e => legRosterFintype C.T e.1
    legIdx_card := fun e => card_legRoster C.T e.1
    betaLeg := fun e l δ => bridgeBetaLeg C e l δ
    act := bridgeAct }

end LeanUrat.MovesU
