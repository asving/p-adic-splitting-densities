/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.MovesU.SlotsG18_relPack

/-!
# IB-G19b (half 1) — ELABORATION PROBE for the sited-slot targets (BP1, D-SC, †22)

The WELL-TYPEDNESS half of the D-SC quantifier-hygiene gate: every H-phase
formulation target displayed in the IB-G16/IB-G17 headers is elaborated here as
an anonymous `example : Prop := …` — COMPILED evidence that the recorded targets
are well-typed over the G14/G15/G17 carriers, WITHOUT asserting anything and
WITHOUT filling any named slot body (the named `SitedSlot_*` stay `sorry`; fills
remain statement-design events behind the Q5 Codex audit).  Nothing may import
this file as evidence of content: `example`s are not consumable.

The other half of IB-G19b — the CLOSURE-HYGIENE re-analysis (no ∀/∃ carrier
closure re-introduced inside any body; each slot False at its designated
degenerate; the True-escape dead at the IB-G18 rows) — is the H-phase gate that
runs BEFORE the fills; the falsifier family is IB-G19a (after the fills).
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesU

open MovesRBase

section probe
variable {p : ℕ} [Fact p.Prime] {Sp : SpeciesSyntax} {AD : AlphabetData p Sp}
variable (S : RelSite p) (SD : SiteData p S Sp AD)
variable (CI : CInterface p Sp AD S.δabs S.dRel)
variable (tableConv : ℕ → Prop) (consumed : Set S.PTree)

/-- probe: `SitedSlot_rel2a`'s (a1) leg — freeCoords infinite, digit cylinders
priced into `prodEvents`, event-algebra compatibility of `domIdent`. -/
example : Prop :=
  SD.dom.freeCoords.Infinite ∧
  (∀ W, W ∈ SD.dom.prodEvents ↔ (fun f => SD.dom.domIdent f) ⁻¹' W ∈ S.AmbEvents) ∧
  (∀ (E : Finset (ℕ × ℕ)) (v : (ℕ × ℕ) → ↥(Fsub p S.δ)),
    {x : SD.dom.freeCoords → ↥(Fsub p S.δ) |
      ∀ c : SD.dom.freeCoords, (c : ℕ × ℕ) ∈ E → x c = v (c : ℕ × ℕ)} ∈ SD.dom.prodEvents)

/-- probe: (a2) integrality + (a3) the Teichmüller pin. -/
example : Prop :=
  ((S.δrel : ℕ) ∣ (S.d : ℕ) ∧ 0 < S.dRel) ∧
  (∀ x, ((SD.emb.teich x : ↥(O p S.δabs)) : Wbar p)
    = WittVector.teichmuller p (x : Kbar p))

/-- probe: (a5) — ambient unitriangularity of `S.reframe` through `domIdent` at
`MovesC.CoordPrec`, target unitriangularity of `tgtOf` at the Fin-order, and the
Θ-commutation. -/
example : Prop :=
  (∀ (F F' : S.FrameC) (x y : SD.dom.freeCoords → ↥(Fsub p S.δ)) (c : SD.dom.freeCoords),
    (∀ c' : SD.dom.freeCoords, MovesC.CoordPrec (c' : ℕ × ℕ) (c : ℕ × ℕ) → x c' = y c') →
    SD.dom.domIdent (S.reframe F F' (SD.dom.domIdent.symm x)) c - x c
      = SD.dom.domIdent (S.reframe F F' (SD.dom.domIdent.symm y)) c - y c) ∧
  (∀ (F F' : S.FrameC) (x y : Fin S.dRel → ↥(O p S.δabs)) (j : Fin S.dRel),
    (∀ j' < j, x j' = y j') →
    SD.frames.tgtOf F F' x j - x j = SD.frames.tgtOf F F' y j - y j) ∧
  (∀ (F F' : S.FrameC) (f : S.Cont),
    SD.theta.Θ (SD.dom.domIdent (S.reframe F F' f))
      = SD.frames.tgtOf F F' (SD.theta.Θ (SD.dom.domIdent f)))

/-- probe: (a6) — dictionary injectivity + letter/shape/anchor/side preservation. -/
example : Prop :=
  Function.Injective SD.dict.readDict ∧
  (∀ r, SD.dict.tgtLetter (SD.dict.readDict r) = SD.dict.ambLetter r) ∧
  (∀ r, SD.dict.tgtShape (SD.dict.readDict r) = SD.dict.ambShape r) ∧
  (∀ r, SD.dict.tgtAnchor (SD.dict.readDict r) = SD.dict.ambAnchor r) ∧
  (∀ r, SD.dict.tgtSide (SD.dict.readDict r) = SD.dict.ambSide r)

/-- probe: `SitedSlot_rel2b`'s target — `Slot_rel1` displayed + the Θ-pullback
pricing at the target's own cylinder-pinned `BoxVol`. -/
example : Prop :=
  Slot_rel1 CI ∧
  (0 < S.cellMass → ∀ W ∈ CI.C.V.events,
    (fun f => SD.theta.Θ (SD.dom.domIdent f)) ⁻¹' W ∈ S.AmbEvents ∧
    S.condMass ((fun f => SD.theta.Θ (SD.dom.domIdent f)) ⁻¹' W) = CI.C.V.vol W)

/-- probe: `SitedSlot_rel2d`'s target — the square + node-data correspondence +
the (CF12) `posOf_letter` wiring. -/
example : Prop :=
  (∀ f : S.Cont, SD.trees.nodeCorr (SD.trees.ambTcan f)
    = SD.trees.tgtTcan (SD.theta.Θ (SD.dom.domIdent f))) ∧
  (∀ t, SD.trees.tgtWord (SD.trees.nodeCorr t) = SD.trees.ambWord t) ∧
  (∀ t, SD.trees.tgtReads (SD.trees.nodeCorr t)
    = (SD.trees.ambReads t).map SD.dict.readDict) ∧
  (∀ t, SD.trees.tgtVerdict (SD.trees.nodeCorr t) = SD.trees.ambVerdict t) ∧
  (∀ r, AD.posLetter S.δabs (SD.trees.posOf r) = SD.dict.tgtLetter r)

/-- probe: `SitedSlot_rel2e`'s target — (e1) compatibility, (e4) `tableConv`
agreement, (e5) determination, (e3) MASS = ENTRY at the REL.1 vol, `Slot_rel1`
displayed. -/
example : Prop :=
  (∀ s, SD.beta.stateReadsRel (SD.beta.stateDict s)
    = (SD.beta.stateReadsAmb s).map SD.dict.readDict) ∧
  tableConv SD.beta.entryFirst ∧
  (∀ T ∈ consumed, ∀ T' ∈ consumed, T = T') ∧
  (Slot_rel1 CI ∧ ∀ T ∈ consumed,
    {g | SD.trees.TgtRealizes (SD.trees.tgtTcan g) (SD.trees.subtreeCorr T)}
      ∈ CI.C.V.events ∧
    SD.beta.β SD.beta.entryFirst S.τ S.βarg
      = CI.C.V.vol {g | SD.trees.TgtRealizes (SD.trees.tgtTcan g) (SD.trees.subtreeCorr T)})

end probe

section probe3
variable {p : ℕ} [Fact p.Prime] {Sp : SpeciesSyntax} {AD : AlphabetData p Sp}
variable (Fam : RelSiteFamily p) (RA : RelAssignment p Sp AD Fam)
variable (CD : ConsumedDisplayPack p Fam)

/-- probe: `SitedSlot_rel3`'s target — per-leg certification (value = the site's
β read; event = the realization event; both DERIVED, none free), keying, and the
consumption tie. -/
example : Prop :=
  ∀ l : CD.Leg,
    (Slot_rel1 (RA.tgt (CD.site l) (CD.site_mem l)) ∧
      {g | (RA.data (CD.site l) (CD.site_mem l)).trees.TgtRealizes
            ((RA.data (CD.site l) (CD.site_mem l)).trees.tgtTcan g)
            ((RA.data (CD.site l) (CD.site_mem l)).trees.subtreeCorr (CD.presc l))}
        ∈ (RA.tgt (CD.site l) (CD.site_mem l)).C.V.events ∧
      (RA.data (CD.site l) (CD.site_mem l)).beta.β (CD.first l) (CD.site l).τ (CD.site l).βarg
        = (RA.tgt (CD.site l) (CD.site_mem l)).C.V.vol
            {g | (RA.data (CD.site l) (CD.site_mem l)).trees.TgtRealizes
                  ((RA.data (CD.site l) (CD.site_mem l)).trees.tgtTcan g)
                  ((RA.data (CD.site l) (CD.site_mem l)).trees.subtreeCorr (CD.presc l))}) ∧
    (CD.first l = (RA.data (CD.site l) (CD.site_mem l)).beta.entryFirst ∧
      RA.tableConv (CD.first l)) ∧
    CD.presc l ∈ RA.consumed (CD.site l) (CD.site_mem l)

end probe3

end LeanUrat.MovesU
