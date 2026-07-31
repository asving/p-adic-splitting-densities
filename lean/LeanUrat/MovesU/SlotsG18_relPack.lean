/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.MovesU.SlotsG17_rel3Display

/-!
# IB-G18 — the p-uniform REL carrier pack + closure rows (bridge BP1, D-SC, †21)

E-phase skeleton per `lean/notes/BRIDGE_BP1_INSTANCE_2026-07-30.md` DESIGN
ADDENDUM D-SC.  `theoremU`'s thirteen reserved parameters are p-UNIFORM Props
(bound BEFORE the prime quantifier — U10's F11 discipline), while every REL
carrier is p-indexed: this unit supplies the p-uniform closure — ONE bundle
carrying, for every prime, the realized site family, the per-member data
assignment, and the [4]-display pack — plus the SIX closure-row Props the
re-scoped consumption theorem (IB-G13′) will feed to `theoremU`'s
rel1/rel2a/rel2b/rel2d/rel2e/rel3 parameters.

WHERE THE TRUE-ESCAPE DIES (the wave-4 boundary duty, restated at this design's
altitude): a caller of `theoremU_bridged′` cannot instantiate the six REL rows
at `True` — they are PINNED to the named `SitedSlot_*`/`Slot_rel1` Props at the
caller's own `RelCarrierPack` binder.  What the caller CAN still do is supply a
degenerate pack; that liability is (i) VISIBLE (the pack is a named binder in
the conditionality record), (ii) FALSIFIABLE (IB-G19a's compiled falsifiers
show the rows are not tautologies), and (iii) exactly the same epistemic status
as `theoremU`'s existing carrier binders (`C : UCarriers n` etc.) — the
supplied-carrier discipline the capstone already lives under.  Semantic pinning
beyond that is wave-D's instance construction, as everywhere else in BP1.

FORMULATION TARGETS for the rows (H-phase bodies, behind the Q5 audit; the
quantifier shape IS the design content — recorded here, ratified there):
* `RelRow_rel1 RP` — ∀ p [Fact p.Prime], ∀ S hS, Slot_rel1 ((RP.assign p).tgt S hS)
  — REL.1 (the G2-formulated ledger clause) at EVERY base the realized family
  reaches (root δ = 1 included via `root_mem`; descent bases via `desc_amb`).
* `RelRow_rel2a RP` — ∀ p, ∀ S hS, SitedSlot_rel2a S ((RP.assign p).data S hS).
* `RelRow_rel2b RP` — ∀ p, ∀ S hS, SitedSlot_rel2b S (data S hS) (tgt S hS).
* `RelRow_rel2d RP` — ∀ p, ∀ S hS, SitedSlot_rel2d S (data S hS).
* `RelRow_rel2e RP` — ∀ p, ∀ S hS, SitedSlot_rel2e S (data S hS)
    ((RP.assign p).tableConv S hS) ((RP.assign p).consumed S hS) (tgt S hS)
    — `tableConv` per-site since R-19 (D-SC REVISION 2, finding 5).
  ROW-LEVEL POSITIVITY (D-SC REVISION 2, finding 7 rebuttal, displayed): every
  site the rel2b/rel2e rows quantify over satisfies `0 < S.cellMass` — that is
  G14's `RelSiteFamily.mem_pos` field (CF1/R-8) at the row's own `hS : S ∈
  (RP.fam p).mem`, so the slot-level positive-cell guard (the note's scoping,
  MOVES 9483–85) discharges at every quantified site; a zero-mass site is
  simply not a family member.  Compiled witness: SlotsG19c
  `rel2b_guard_fires_on_family`.
* `RelRow_rel3 RP` — ∀ p, SitedSlot_rel3 (RP.fam p) (RP.assign p) (RP.display p).
These ∀-closures are over the SUPPLIED family — the G2 record's junk-site
∀-falseness does not apply (the quantifier never ranges over abstract sites).

CONSUMPTION SHAPE (IB-G13′, NOT landed here — D-SC escalation E-1, orchestrator
adjudication required; supersedes-informs the queued rel3-fallback item):
`theoremU_bridged′ … (RP : RelCarrierPack) … :=` theoremU applied with
rel1 := RelRow_rel1 RP, …, rel3 := RelRow_rel3 RP, the seven mechanics/seam
slots at their landed G4–G10 Props, and the 13 hypothesis arguments as visible
binders.  ALL THIRTEEN typed — G4's requirement met without the 12-slot
fallback.  G13′ WAITS on: E-1 ratification + the Q5 Codex audits of
G14–G18 + IB-G19a falsifiers + IB-G19b hygiene gate.
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesU

open MovesRBase

/-- **THE p-UNIFORM REL CARRIER PACK** (†21): one species syntax (EQ-1: the SAME
finite syntax over every base — p-free by the note's own grammar discipline),
per-prime alphabet data, per-prime realized site families, per-prime data
assignments (with the [3]-exports), and per-prime [4]-display packs.  The ONE
binder `theoremU_bridged′` adds for the whole REL family; wave-D's instance
construction inhabits it. -/
structure RelCarrierPack where
  Sp : SpeciesSyntax
  AD : ∀ (p : ℕ) [Fact p.Prime], AlphabetData p Sp
  fam : ∀ (p : ℕ) [Fact p.Prime], RelSiteFamily p
  assign : ∀ (p : ℕ) [Fact p.Prime], RelAssignment p Sp (AD p) (fam p)
  display : ∀ (p : ℕ) [Fact p.Prime], ConsumedDisplayPack p (fam p)

/-- Closure row 1/6 — **`RelRow_rel1`**: REL.1 at every base the realized family
reaches (see the file-header target).  H-phase fills behind the Q5 audit. -/
def RelRow_rel1 (RP : RelCarrierPack) : Prop :=
  ∀ (p : ℕ) [Fact p.Prime], ∀ (S : RelSite p) (hS : S ∈ (RP.fam p).mem),
    Slot_rel1 ((RP.assign p).tgt S hS)

/-- Closure row 2/6 — **`RelRow_rel2a`** (see the file-header target). -/
def RelRow_rel2a (RP : RelCarrierPack) : Prop :=
  ∀ (p : ℕ) [Fact p.Prime], ∀ (S : RelSite p) (hS : S ∈ (RP.fam p).mem),
    SitedSlot_rel2a S ((RP.assign p).data S hS)

/-- Closure row 3/6 — **`RelRow_rel2b`** (see the file-header target). -/
def RelRow_rel2b (RP : RelCarrierPack) : Prop :=
  ∀ (p : ℕ) [Fact p.Prime], ∀ (S : RelSite p) (hS : S ∈ (RP.fam p).mem),
    SitedSlot_rel2b S ((RP.assign p).data S hS) ((RP.assign p).tgt S hS)

/-- Closure row 4/6 — **`RelRow_rel2d`** (see the file-header target). -/
def RelRow_rel2d (RP : RelCarrierPack) : Prop :=
  ∀ (p : ℕ) [Fact p.Prime], ∀ (S : RelSite p) (hS : S ∈ (RP.fam p).mem),
    SitedSlot_rel2d S ((RP.assign p).data S hS)

/-- Closure row 5/6 — **`RelRow_rel2e`** (see the file-header target). -/
def RelRow_rel2e (RP : RelCarrierPack) : Prop :=
  ∀ (p : ℕ) [Fact p.Prime], ∀ (S : RelSite p) (hS : S ∈ (RP.fam p).mem),
    SitedSlot_rel2e S ((RP.assign p).data S hS)
      ((RP.assign p).tableConv S hS) ((RP.assign p).consumed S hS)
      ((RP.assign p).tgt S hS)

/-- Closure row 6/6 — **`RelRow_rel3`** (see the file-header target). -/
def RelRow_rel3 (RP : RelCarrierPack) : Prop :=
  ∀ (p : ℕ) [Fact p.Prime],
    SitedSlot_rel3 (RP.fam p) (RP.assign p) (RP.display p)

end LeanUrat.MovesU
