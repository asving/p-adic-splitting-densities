/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.MovesU.SlotsG14_relSite

/-!
# IB-G15 — the per-site DATA PACKS (bridge BP1, DESIGN ADDENDUM D-SC, †18)

E-phase skeleton per `lean/notes/BRIDGE_BP1_INSTANCE_2026-07-30.md` DESIGN
ADDENDUM D-SC.  This unit is the SECOND layer of the site-carrier design: the
DATA the REL.2 obligations are ABOUT — the Θ transport, the read dictionary, the
tree correspondence, the β table — as data-only structures over a `RelSite`.

RAW MATERIAL: the parked draft's `REL2a1`–`REL2a6`, `REL2d`, `REL2e`
(`lean/notes/MOVESR_LEAN_BLUEPRINT_2026-07-28.md` §1, with the CF10/CF11/CF12/
CF13/CF14 repairs folded), transcribing the note's (REL.2a) six-item checklist
(MOVES_2026-07-24.md 9449–9474), the (REL.2d) commutative-square acceptance
criterion (9494–9507), and the (REL.2e) (e1)–(e5) roster (9508–9540).

THE LAW/DATA SPLIT (D-SC principle P2 — THE central E-phase resolution, R-9,
FLAGGED for the Q5 audit): the parked draft carried the note's obligations as
LAW FIELDS of these structures (its consumers hypothesized the Props directly,
so data-with-laws was fine there).  Here the packs feed `theoremU`'s slot
PARAMETERS: if the laws were fields, supplying the pack would discharge its own
laws and each slot Prop would degenerate to `Nonempty (pack)` — exactly the
∃-closure trap the G2 BLOCKED record compiled.  So: the packs below carry DATA
plus structural wellformedness ONLY (nonemptiness per draft D2; event-set
closure); every note OBLIGATION (measurability transport, integrality,
Teichmüller pin, unitriangular anchors, frame commutation, dictionary
preservation, the square, the β pricing) is hoisted to the IB-G16/G17 slot
Props.  Consequence: degenerate packs are constructible BY DESIGN — they are
the IB-G19a falsifier witnesses.

E-PHASE RESOLUTIONS (minimal, flagged):
* R-9 (law/data split) — above.
* R-10 (dependency thinning): `SiteFrames` needs only `S` (the target-side
  transports mention no domain data — the draft's `REL2a5` dependence on a1/a4
  lived entirely in its law fields, which are now IB-G16 content); `SiteTrees`
  needs `S`/`Sp`/`AD`/`SiteDict` but not Θ (the square law carries the Θ
  dependence, in IB-G16).
* R-11 (CF13/CF14, carried over verbatim): `tableConv` and `consumed` are NOT
  fields of any pack — they are PARAMETERS of the (e)-slot, supplied by
  [3]/MovesS's export (instance-chosen versions were the audited vacuity).
  They enter at IB-G16's `SitedSlot_rel2e` and IB-G17's `RelAssignment`.

STATEMENT-FENCE FLAG: new hypothesis-side carrier vocabulary; Q5 Codex audit
before any consumer.  DELIVERABLE STATUS (draft D7): inhabiting these packs at
the REAL instance is wave-D's deliverable; nothing here asserts existence.
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesU

open MovesRBase

variable (p : ℕ) [Fact p.Prime]

/-- (a1)-DATA (†18; draft `REL2a1` minus its laws — R-9): the free base
coordinates (ℓ, i) on Σ_c, the identification of continuation points with the
digit-product space ((R0-box)'s F_δ-digit ATOM), and the product-side event set.
The (a1) LAWS — `freeCoords` infinite, digit cylinders in `prodEvents`,
event-algebra compatibility of `domIdent` — are IB-G16 (`SitedSlot_rel2a`)
conjuncts. -/
structure SiteDom (S : RelSite p) where
  freeCoords : Set (ℕ × ℕ)
  domIdent : S.Cont ≃ (freeCoords → ↥(Fsub p S.δ))
  prodEvents : Set (Set (freeCoords → ↥(Fsub p S.δ)))

/-- (a3)-DATA (†18; draft `REL2a3` minus `teich_pin` — R-9): the named
F_{δ_j} ↪ (tower residue field) embedding and the canonical-lift map.  The
Teichmüller PIN (`teich_pin`: the lift IS Mathlib's `WittVector.teichmuller`)
is an IB-G16 conjunct. -/
structure SiteEmbed (S : RelSite p) where
  TowerRes : Type
  [towerResField : Field TowerRes]
  embed : ↥(Fsub p S.δabs) →+* TowerRes
  teich : ↥(Fsub p S.δabs) → ↥(O p S.δabs)

attribute [instance] SiteEmbed.towerResField

/-- (a4)-DATA (†18; draft `REL2a4`, verbatim — it was already data-only): the
map Θ_j itself, from (a1)'s free coordinates to the O_{δ_j} coefficient box of
monic degree-d_j^rel polynomials. -/
structure SiteTheta (S : RelSite p) (DM : SiteDom p S) where
  Θ : (DM.freeCoords → ↥(Fsub p S.δ)) → (Fin S.dRel → ↥(O p S.δabs))

/-- (a5)-DATA (†18; draft `REL2a5` minus its laws — R-9/R-10): the TARGET-side
frame transports.  The ambient side is `S.reframe` (the site's own C.0.5 family,
CF10).  The (a5) LAWS — unitriangularity anchors on BOTH sides (`CoordPrec`
ambient, `Fin`-order target) and the displayed Θ-commutation — are IB-G16
conjuncts. -/
structure SiteFrames (S : RelSite p) where
  tgtOf : S.FrameC → S.FrameC →
    ((Fin S.dRel → ↥(O p S.δabs)) ≃ (Fin S.dRel → ↥(O p S.δabs)))

/-- (a6)-DATA (†18; draft `REL2a6` minus its laws — R-9): the per-read dictionary
carriers — ambient/target read types, the transport map, and the per-read field
READERS (letter, shape, anchor, side, residue data).  The (a6) LAWS —
injectivity + letter/shape/anchor/side preservation ("integer/lattice fields
PRESERVED, the SAME GRAMMAR"; residue data transported by the DECLARED
`resDict`, never an equality) — are IB-G16 conjuncts. -/
structure SiteDict (S : RelSite p) (Sp : SpeciesSyntax) where
  AmbRead : Type
  ambReadNe : Nonempty AmbRead
  TgtRead : Type
  readDict : AmbRead → TgtRead
  ambLetter : AmbRead → Sp.Letter
  tgtLetter : TgtRead → Sp.Letter
  ambShape : AmbRead → ℕ × ℕ × ℕ × ℕ
  tgtShape : TgtRead → ℕ × ℕ × ℕ × ℕ
  ambAnchor : AmbRead → ℕ
  tgtAnchor : TgtRead → ℕ
  ambSide : AmbRead → (ℚ × ℚ) × List ℕ
  tgtSide : TgtRead → (ℚ × ℚ) × List ℕ
  AmbResDat : AmbRead → Type
  TgtResDat : TgtRead → Type
  resDict : ∀ r, AmbResDat r → TgtResDat (readDict r)

/-- (d)-DATA (†18; draft `REL2d` minus its laws — R-9/R-10): the four square
vertices' carriers — b_j's continuation subtrees of T_can(f), the
O_{δ_j}-engine's canonical trees, the node-data correspondence `nodeCorr`, the
word/read/verdict readers on both sides, the (EQ-2) position assignment, and
the prescribed-subtree identification (`TgtSub`/`subtreeCorr`/`TgtRealizes` —
without which (SIB-Oδ) is ill-typed).  The (d) LAWS — the commuting square at
Θ, word/read/verdict preservation, the `posOf_letter` wiring constraint (CF12),
and the PRESCRIBED-SUBTREE EVENT IDENTIFICATION (R-17: `SEvent T` is exactly
the Θ-pullback of `subtreeCorr T`'s realization event — what constrains
`TgtSub`/`subtreeCorr`/`TgtRealizes`) — are IB-G16 conjuncts. -/
structure SiteTrees (S : RelSite p) (Sp : SpeciesSyntax) (AD : AlphabetData p Sp)
    (Dc : SiteDict p S Sp) where
  AmbTree : Type
  ambTreeNe : Nonempty AmbTree
  ambTcan : S.Cont → AmbTree
  TgtTree : Type
  tgtTcan : (Fin S.dRel → ↥(O p S.δabs)) → TgtTree
  nodeCorr : AmbTree → TgtTree
  ambWord : AmbTree → List Sp.Letter
  tgtWord : TgtTree → List Sp.Letter
  ambReads : AmbTree → List Dc.AmbRead
  tgtReads : TgtTree → List Dc.TgtRead
  ambVerdict : AmbTree → List Bool
  tgtVerdict : TgtTree → List Bool
  posOf : Dc.TgtRead → AD.Pos
  TgtSub : Type
  subtreeCorr : S.PTree → TgtSub
  TgtRealizes : TgtTree → TgtSub → Prop

/-- (e)-DATA (†18; draft `REL2e` minus `stateDict_compat` — R-9; CF13/CF14 per
R-11): REL.1-side states over O_{δ_j}, the (e1) dictionary from [3]/[3t]'s state
index, the per-state read rosters on both sides, [3]'s β TABLE in [3]'s own
keying (first index, state, argument) ↦ entry, and the (e4) first index
`entryFirst` FIXED per branch.  `tableConv`/`consumed` are NOT fields (R-11).
The (e) LAWS — (e1)-compatibility, (e4) UNIQUE agreement with the exported
convention (R-18), (e5) coverage + determination anchored at the site's `Tj`
(R-16/R-18), (e3) MASS = ENTRY at the REL.1 vol pinned AT `Tj` — are IB-G16
conjuncts. -/
structure SiteBeta (S : RelSite p) (Sp : SpeciesSyntax) (Dc : SiteDict p S Sp) where
  RelState : Type
  relStateNe : Nonempty RelState
  stateDict : S.StateIdx → RelState
  stateReadsAmb : S.StateIdx → List Dc.AmbRead
  stateReadsRel : RelState → List Dc.TgtRead
  β : ℕ → S.StateIdx → ℕ → ℚ
  entryFirst : ℕ

/-- **THE PER-SITE DATA BUNDLE** (†18): everything the five sited slot Props of
IB-G16/G17 read at one site — the seven packs, dependency-threaded.  Wave-D
inhabits this at the real instance; the IB-G18 `RelAssignment` supplies one per
family member. -/
structure SiteData (S : RelSite p) (Sp : SpeciesSyntax) (AD : AlphabetData p Sp) where
  dom : SiteDom p S
  emb : SiteEmbed p S
  theta : SiteTheta p S dom
  frames : SiteFrames p S
  dict : SiteDict p S Sp
  trees : SiteTrees p S Sp AD dict
  beta : SiteBeta p S Sp dict

end LeanUrat.MovesU
