/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.Scaffold.Spine
import LeanUrat.MovesU.U10_theoremU
import LeanUrat.MovesU.BridgeMk
import LeanUrat.MovesU.SlotsG18_relPack
import LeanUrat.MovesU.SlotsG2_relFamily
import LeanUrat.MovesU.SlotsG3_rel3
import LeanUrat.MovesU.SlotsG4_rs0Lump
import LeanUrat.MovesU.SlotsG5_trackRule
import LeanUrat.MovesU.SlotsG6_dnLattice
import LeanUrat.MovesU.SlotsG7_m1m5Echo
import LeanUrat.MovesU.SlotsG8_x1aDict
import LeanUrat.MovesU.SlotsG9_m4bConst
import LeanUrat.MovesU.SlotsG10_jcInvHist

/-!
# Scaffold/CorpusBridge — theoremU → RootC [wave VI-1]

Transcription of `lean/blueprints/BP_VI.md` §1.3 (unit VI-B1). The sole proof
input is `LeanUrat.MovesU.theoremU` (U10_theoremU.lean:104); the target shape
`RootC` is `Scaffold/Spine.lean` (VI-S2). Every import above is explicit per
§1.3 — no reliance on re-export.

Import-line display adjustment (module names only, statement untouched): §1.3
lists `SlotsG2_rel1` and `SlotsG3_rel2`; the built corpus's modules are
`LeanUrat.MovesU.SlotsG2_relFamily` and `LeanUrat.MovesU.SlotsG3_rel3` (no
files of the §1.3 names exist) — the unique on-disk readings of the G2/G3
slot modules.

CONDITIONALITY OF RECORD (inherited verbatim from theoremU's WAVE-4 BOUNDARY
record): the 13 bare-`Prop` slot parameters (`rel1 … jcInvHist`) are UNPINNED
named assumptions — True-instantiable, no typed mathematical obligation yet —
pending the wave-D carriers. They are NEVER discharged or typed here; this
unit only transports theoremU's conclusion into the spine shape.
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option maxHeartbeats 1000000

namespace LeanUrat.Scaffold

open LeanUrat.MovesU Filter Topology

/-- VI-B1: theoremU's conclusion, transported into the spine shape. -/
theorem rootC_of_theoremU (n : ℕ) (hn : 2 ≤ n) (C : UCarriers n)
    (KC : KernelCarriers n C) (K7 : Cl7Kernel n KC) (S : SolveData n)
    (KT : UpstreamTyped n KC)
    (rel1 rel2a rel2b rel2d rel2e rel3 rs0Lump trackRule dnLattice
      m1m5Echo x1aDict m4bConst jcInvHist : Prop)
    (hrel1 : rel1) (hrel2a : rel2a) (hrel2b : rel2b)
    (hrel2d : rel2d) (hrel2e : rel2e) (hrel3 : rel3)
    (hrs0 : rs0Lump) (htrack : trackRule) (hdn : dnLattice)
    (hm15 : m1m5Echo) (hx1a : x1aDict) (hm4b : m4bConst)
    (hjc : jcInvHist)
    (inst : ∀ (p : ℕ) (hp : p.Prime), UInstance n C KC K7 S p hp) :
    RootC n C KC K7 S inst := by
  obtain ⟨R, hR, hs, h⟩ :=
    theoremU n hn C KC K7 S KT rel1 rel2a rel2b rel2d rel2e rel3
      rs0Lump trackRule dnLattice m1m5Echo x1aDict m4bConst jcInvHist
      hrel1 hrel2a hrel2b hrel2d hrel2e hrel3
      hrs0 htrack hdn hm15 hx1a hm4b hjc inst
  refine ⟨R, hR, hs, fun p hp hr => ?_⟩
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨t1, t2, t3, t4, t5⟩ := h p hp hr
  exact ⟨t1, t2, t3, t4, t5⟩

/-- VI-B2: direct VI-B1 specialization at the same inputs used by
    `theoremU_fired`; it does not consume `theoremU_fired` as an argument. -/
theorem rootC_fired (n : ℕ) (hn : 2 ≤ n) (C : UCarriers n)
    (KC : KernelCarriers n C) (K7 : Cl7Kernel n KC)
    (KT : UpstreamTyped n KC) (BP : BridgePre n C)
    (rel1 rel2a rel2b rel2d rel2e rel3 rs0Lump trackRule dnLattice
      m1m5Echo x1aDict m4bConst jcInvHist : Prop)
    (hrel1 : rel1) (hrel2a : rel2a) (hrel2b : rel2b)
    (hrel2d : rel2d) (hrel2e : rel2e) (hrel3 : rel3)
    (hrs0 : rs0Lump) (htrack : trackRule) (hdn : dnLattice)
    (hm15 : m1m5Echo) (hx1a : x1aDict) (hm4b : m4bConst)
    (hjc : jcInvHist)
    (BD : ∀ (p : ℕ) (hp : p.Prime), BridgeInputs n C KC K7 p hp) :
    RootC n C KC K7 (bridgeSolve C BP.hdet)
      (fun p hp => mkUInstance n hn C KC K7 BP p hp (BD p hp)) :=
  rootC_of_theoremU n hn C KC K7 (bridgeSolve C BP.hdet) KT
    rel1 rel2a rel2b rel2d rel2e rel3 rs0Lump trackRule dnLattice
    m1m5Echo x1aDict m4bConst jcInvHist
    hrel1 hrel2a hrel2b hrel2d hrel2e hrel3 hrs0 htrack hdn
    hm15 hx1a hm4b hjc
    (fun p hp => mkUInstance n hn C KC K7 BP p hp (BD p hp))

/- REVISION-3 STATEMENT REPAIR OF RECORD (VI-B3/VI-B4, compile-gated): the
§1.3 Revision-2 display `(SS : LeanUrat.MovesV.StepSys n 𝓕)` with
`m4b : Slot_m4bConst n 𝓕 SS` was COMPILER-REFUTED (corpus `MovesV.StepSys`
takes only `(n : ℕ)`, MovesV/Defs.lean:81; `Slot_m4bConst`'s explicit argument
after `n` is the MEASURED carrier `V : MovesV.CtsMeasured n Cv Sv`,
SlotsG9_m4bConst.lean:74). The unique well-typed intent-preserving reading —
three binders `(𝓕 : CtsFamily n) (Sv : StepSys n) (SS : CtsMeasured n 𝓕 Sv)`
with `m4b : Slot_m4bConst n SS`, keeping `𝓕` before `SS` per the Revision-2
finding-1 decision — is what lands below (BP_VI.md REVISION 3). -/

/-- VI-B3: the D-SC SLOT ASSIGNMENT — the typed faces of theoremU's 13 bare-Prop
    slot parameters, NAMED (statement-layer map only; wires NO wave-D carrier —
    parked items 22–29 untouched). Records which sited definition each row takes:
    rel1..rel3 ← `RelRow_rel1..rel3 RP` (SlotsG18_relPack.lean:88–…, over a
    `RelCarrierPack`); rs0Lump ← `Slot_rs0Lump n C` (SlotsG4); trackRule ←
    `Slot_trackRule n KC K7` (SlotsG5); dnLattice ← `Slot_dnLattice n KC K7`
    (SlotsG6); m1m5Echo ← `Slot_m1m5Echo n C` (SlotsG7); x1aDict ←
    `Slot_x1aDict n KC` (SlotsG8); m4bConst ← `Slot_m4bConst n SS` over the
    measured carrier `SS : CtsMeasured n 𝓕 Sv` (SlotsG9); jcInvHist ←
    `Slot_jcInvHist n` (SlotsG10). -/
structure SlotAssignment (n : ℕ) (C : UCarriers n) (KC : KernelCarriers n C)
    (K7 : Cl7Kernel n KC) (RP : RelCarrierPack)
    (𝓕 : LeanUrat.MovesV.CtsFamily n)
    (Sv : LeanUrat.MovesV.StepSys n)
    (SS : LeanUrat.MovesV.CtsMeasured n 𝓕 Sv) : Prop where
  rel1 : RelRow_rel1 RP
  rel2a : RelRow_rel2a RP
  rel2b : RelRow_rel2b RP
  rel2d : RelRow_rel2d RP
  rel2e : RelRow_rel2e RP
  rel3 : RelRow_rel3 RP
  rs0 : Slot_rs0Lump n C
  trk : Slot_trackRule n KC K7
  dn : Slot_dnLattice n KC K7
  m15 : Slot_m1m5Echo n C
  x1a : Slot_x1aDict n KC
  m4b : Slot_m4bConst n SS
  jc : Slot_jcInvHist n

/-- VI-B4: RootC fired with all thirteen theoremU propositions instantiated by
    the sited slot faces. Typed ledger, bridge preconditions, and per-prime
    bridge inputs remain explicit. -/
theorem rootC_fired_at_slots (n : ℕ) (hn : 2 ≤ n) (C : UCarriers n)
    (KC : KernelCarriers n C) (K7 : Cl7Kernel n KC)
    (KT : UpstreamTyped n KC) (BP : BridgePre n C)
    (RP : RelCarrierPack) (𝓕 : LeanUrat.MovesV.CtsFamily n)
    (Sv : LeanUrat.MovesV.StepSys n)
    (SS : LeanUrat.MovesV.CtsMeasured n 𝓕 Sv)
    (SA : SlotAssignment n C KC K7 RP 𝓕 Sv SS)
    (BD : ∀ (p : ℕ) (hp : p.Prime), BridgeInputs n C KC K7 p hp) :
    RootC n C KC K7 (bridgeSolve C BP.hdet)
      (fun p hp => mkUInstance n hn C KC K7 BP p hp (BD p hp)) :=
  rootC_fired n hn C KC K7 KT BP
    (RelRow_rel1 RP) (RelRow_rel2a RP) (RelRow_rel2b RP) (RelRow_rel2d RP)
    (RelRow_rel2e RP) (RelRow_rel3 RP) (Slot_rs0Lump n C)
    (Slot_trackRule n KC K7) (Slot_dnLattice n KC K7) (Slot_m1m5Echo n C)
    (Slot_x1aDict n KC) (Slot_m4bConst n SS) (Slot_jcInvHist n)
    SA.rel1 SA.rel2a SA.rel2b SA.rel2d SA.rel2e SA.rel3 SA.rs0 SA.trk SA.dn
    SA.m15 SA.x1a SA.m4b SA.jc BD

end LeanUrat.Scaffold
