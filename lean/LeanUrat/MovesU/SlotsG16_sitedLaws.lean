/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.MovesU.SlotsG15_siteData
import LeanUrat.MovesU.SlotsG2_relFamily

/-!
# IB-G16 — the SITED REL.2 law slots (bridge BP1, DESIGN ADDENDUM D-SC, †19)

E-phase skeleton per `lean/notes/BRIDGE_BP1_INSTANCE_2026-07-30.md` DESIGN
ADDENDUM D-SC.  The FOUR sited slot Props re-typing the BLOCKED
`Slot_rel2a`/`Slot_rel2b`/`Slot_rel2d`/`Slot_rel2e` of `SlotsG2_relFamily.lean`
at the supplied-carrier signature the G2 BLOCKED record demands.  The G2 records
stay untouched as the compiled failure evidence (D-SC escalation E-2); NOTHING
here edits them — these are NEW declarations, `SitedSlot_*`.

WHY THIS SIGNATURE CLOSES THE G2 TRAP (D-SC principle P1): the G2 H-phase found
(i) ∀-closure over abstract sites FALSE AT EVERY CI (junk Dirac site), (ii)
∃-closure True-instantiable (identity site), (iii) the middle road blocked on
missing carriers.  Here the site `S`, the data pack `SD`, the target interface
`CI`, and the [3]-exports `tableConv`/`consumed` are all PARAMETERS: no closure
happens inside any Prop; the junk site becomes the IB-G19a falsifier witness;
the identity-site inhabitant is the CALLER's visible liability at the IB-G18
row (it must supply that site AS the instance's own, in the named binder — the
conditionality record displays it), not a hidden escape inside the slot.

FORMULATION TARGETS (H-phase bodies, behind the Q5 Codex audit; deps IB-G15 +
`Slot_rel1` (G2); note displays MOVES_2026-07-24.md 9449–9540):
* `SitedSlot_rel2a` — the six (a)-obligations at (S, SD):
  (a1) `SD.dom.freeCoords.Infinite` ∧ digit cylinders ∈ `prodEvents` ∧
       (∀ W, W ∈ prodEvents ↔ domIdent ⁻¹' W ∈ S.AmbEvents);
  (a2) `(S.δrel : ℕ) ∣ (S.d : ℕ)` ∧ `0 < S.dRel` (target integrality);
  (a3) the Teichmüller pin: ∀ x, ((SD.emb.teich x : ↥(O p S.δabs)) : Wbar p)
       = WittVector.teichmuller p (x : Kbar p);
  (a5) ambient unitriangularity of `S.reframe` through `domIdent` at
       `MovesC.CoordPrec`, target unitriangularity of `SD.frames.tgtOf` at the
       Fin-order, and the commutation Θ ∘ reframe = tgtOf ∘ Θ;
  (a6) `Function.Injective SD.dict.readDict` ∧ letter/shape/anchor/side
       preservation (tgt∘readDict = amb, four equations).
  ((a4) is pure data — `SD.theta.Θ` — no law conjunct.)
* `SitedSlot_rel2b` — the `_linked` pricing at (S, SD, CI):
  `Slot_rel1 CI` (the REL.1 conditionality DISPLAYED per site) ∧
  (0 < S.cellMass → ∀ W ∈ CI.C.V.events,
    (fun f => SD.theta.Θ (SD.dom.domIdent f)) ⁻¹' W ∈ S.AmbEvents ∧
    S.condMass ((fun f => SD.theta.Θ (SD.dom.domIdent f)) ⁻¹' W) = CI.C.V.vol W)
  — the target vol IS the CI's own cylinder-pinned `BoxVol` (FF5(ii)/FF6).
* `SitedSlot_rel2d` — the acceptance-criterion square at (S, SD)
  (REVISED at D-SC REVISION 2, finding 3 — the prescribed-subtree
  identification the G2 blocked spec requires is RESTORED as the fourth leg):
  ∀ f : S.Cont, SD.trees.nodeCorr (SD.trees.ambTcan f)
    = SD.trees.tgtTcan (SD.theta.Θ (SD.dom.domIdent f)),
  ∧ word/read/verdict preservation (tgtWord ∘ nodeCorr = ambWord;
    tgtReads ∘ nodeCorr = map readDict ∘ ambReads; verdicts equal)
  ∧ (CF12) ∀ r, AD.posLetter S.δabs (SD.trees.posOf r) = SD.dict.tgtLetter r
  ∧ (R-17, the PRESCRIBED-SUBTREE IDENTIFICATION — what pins
     `TgtSub`/`subtreeCorr`/`TgtRealizes`, and what makes S_j(T) an
     O_{δ_j}-statement so (SIB-Oδ) is well-typed):
     ∀ (T : S.PTree) (f : S.Cont), f ∈ S.SEvent T ↔
       SD.trees.TgtRealizes (SD.trees.tgtTcan (SD.theta.Θ (SD.dom.domIdent f)))
         (SD.trees.subtreeCorr T).
* `SitedSlot_rel2e` — (e1)–(e5) at (S, SD, tableConv, consumed, CI)
  (REVISED at D-SC REVISION 2, findings 1/5 — the empty-`consumed` and
  free-`tableConv` escapes are killed at the statement: (e3) is pinned AT the
  site's own `S.Tj` (R-16) with NO `consumed`-quantifier left to vacate; (e5)
  gains the coverage half; (e4) gains unique determination):
  (e1) ∀ s, SD.beta.stateReadsRel (SD.beta.stateDict s)
        = (SD.beta.stateReadsAmb s).map SD.dict.readDict;
  (e4) tableConv SD.beta.entryFirst ∧ (∀ m, tableConv m → m = SD.beta.entryFirst)
       — [3]'s exported convention ONLY (CF13), which as a CONVENTION must
       DETERMINE the first index (R-18; `fun _ => True` is now refuted, and no
       ambient-vs-rebased reading is chosen — the G15b seam stays open, resolved
       only by [3]'s actual export);
  (e5) S.Tj ∈ consumed ∧ (∀ T ∈ consumed, T = S.Tj) — coverage (the table
       actually consumes THE site's prescription) + determination (nothing
       else at this key); `consumed = ∅` is now refuted (R-16/R-18);
  (e3) `Slot_rel1 CI` ∧
        {g | SD.trees.TgtRealizes (SD.trees.tgtTcan g)
              (SD.trees.subtreeCorr S.Tj)} ∈ CI.C.V.events ∧
        SD.beta.β SD.beta.entryFirst S.τ S.βarg
          = CI.C.V.vol {g | …realizes S.Tj…}
       — MASS = ENTRY stated unconditionally AT `S.Tj`, never behind a
       supplied-carrier quantifier
  ((e2) is definitional at `RelSite.βarg` — the draft's `βarg_eq` face).

E-PHASE DIVISION OF LABOR (the G2 discipline, verbatim): bodies are `sorry`;
filling one is a STATEMENT-DESIGN EVENT routed through the Q5 Codex audit,
never a silent fill.  NON-VACUITY DUTY (IB-G19a): per-slot compiled falsifiers —
rel2b's is the G2 record's own countermodel INVERTED (the Dirac site against a
cylinder-pinned BoxVol falsifies the pricing clause).  QUANTIFIER-HYGIENE GATE
(IB-G19b): before any H-phase fill, re-run the G2 closure analysis at these
signatures (no ∀/∃ re-introduced inside bodies; each slot False at its
designated degenerate; the True-escape dead at the G18 rows).
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesU

open MovesRBase

/-- IB-G16 slot 1/4 — **`SitedSlot_rel2a`** (CL-8 REL.2(a), owner [2r]; the sited
re-type of the BLOCKED `Slot_rel2a`): the six-item continuation-map package
(a1)–(a6) as LAWS over the supplied site `S` and data pack `SD` — all six or
nothing (the parked bundle discipline).  See the file header for the displayed
target.  H-phase fills behind the Q5 audit; IB-G19b gates the fill. -/
def SitedSlot_rel2a {p : ℕ} [Fact p.Prime] {Sp : SpeciesSyntax}
    {AD : AlphabetData p Sp} (S : RelSite p) (SD : SiteData p S Sp AD) : Prop :=
  sorry

/-- IB-G16 slot 2/4 — **`SitedSlot_rel2b`** (CL-8 REL.2(b), owner [2r]; the sited
re-type of the BLOCKED `Slot_rel2b`): normalization/Jacobian — the conditioned
ambient mass of every Θ-pullback of a REL.1-measurable target event equals the
target's own cylinder-pinned `BoxVol` mass, positive-cell guarded, with
`Slot_rel1 CI` the displayed per-site REL.1 conditionality (`_linked`, FF6).
See the file header for the displayed target. -/
def SitedSlot_rel2b {p : ℕ} [Fact p.Prime] {Sp : SpeciesSyntax}
    {AD : AlphabetData p Sp} (S : RelSite p) (SD : SiteData p S Sp AD)
    (CI : CInterface p Sp AD S.δabs S.dRel) : Prop :=
  sorry

/-- IB-G16 slot 3/4 — **`SitedSlot_rel2d`** (CL-8 REL.2(d), owner [2r]; the sited
re-type of the BLOCKED `Slot_rel2d`): lift-policy compatibility — the
acceptance-criterion commutative square `nodeCorr (T_can f) = T_can^{O_δ}(Θ f)`
with the SPECIFIED node-data correspondence (word/reads/verdicts preserved,
(EQ-2) wiring constrained by `posOf_letter`) over the supplied `SD.trees`,
PLUS the prescribed-subtree identification (R-17: `SEvent T` = the Θ-pullback
of the target realization event, restored at D-SC REVISION 2 finding 3).
See the file header for the displayed target. -/
def SitedSlot_rel2d {p : ℕ} [Fact p.Prime] {Sp : SpeciesSyntax}
    {AD : AlphabetData p Sp} (S : RelSite p) (SD : SiteData p S Sp AD) : Prop :=
  sorry

/-- IB-G16 slot 4/4 — **`SitedSlot_rel2e`** (CL-8 REL.2(e), owner [2r]; the sited
re-type of the BLOCKED `Slot_rel2e`): the β-identification (e1)–(e5) with
`tableConv`/`consumed` as [3]/MovesS-supplied PARAMETERS (CF13/CF14 — the
audited-vacuity repairs, carried verbatim) and MASS = ENTRY priced at the
supplied CI's REL.1 vol, `Slot_rel1 CI` displayed — REVISED at D-SC REVISION 2
(findings 1/5): (e3) pinned unconditionally at the site's own `S.Tj`, (e5) =
coverage + determination at `S.Tj`, (e4) = unique agreement with the exported
convention, so the empty-`consumed`/`fun _ => True` degenerate carriers make
the slot FALSE, not vacuously true (compiled: SlotsG19c).  See the file header
for the displayed target. -/
def SitedSlot_rel2e {p : ℕ} [Fact p.Prime] {Sp : SpeciesSyntax}
    {AD : AlphabetData p Sp} (S : RelSite p) (SD : SiteData p S Sp AD)
    (tableConv : ℕ → Prop) (consumed : Set S.PTree)
    (CI : CInterface p Sp AD S.δabs S.dRel) : Prop :=
  sorry

end LeanUrat.MovesU
