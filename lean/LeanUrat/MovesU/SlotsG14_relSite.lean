/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.MovesU.SlotsG1_cinterface

/-!
# IB-G14 — the RelSite/RelSiteFamily CARRIER (bridge BP1, DESIGN ADDENDUM D-SC, †17)

E-phase skeleton per `lean/notes/BRIDGE_BP1_INSTANCE_2026-07-30.md` DESIGN ADDENDUM
D-SC (2026-07-31; the adjudicated site-carrier design round the BLOCKED records
`SlotsG2_relFamily.lean`/`SlotsG3_rel3.lean` escalated: "the site-carrier layer (or
a ratified alternative closure) is an orchestrator adjudication — surfaced, never
improvised").  This unit is the FIRST layer: the branch continuation SITE and the
realized site FAMILY the REL.2/REL.3 slot family quantifies over.

RAW MATERIAL (transcribed, with the D-SC resolutions): the parked MovesR draft's
`Setting`/`SettingsFamily` (`lean/notes/MOVESR_LEAN_BLUEPRINT_2026-07-28.md` §1,
findings 2/19/20 + CF1/CF10 folded in), transcribing the note's SETTING display
(MOVES_2026-07-24.md 9430–9448: "Ambient base O_δ …, a realized prefix η, state
cylinder Σ (frame Ψ_η), digit cell c of Σ, and a branch b_j …" + the BASE-INDEX
CONVENTION 9423–9429, ALL indices ABSOLUTE) and the (SIB-Oδ) family quantifier
(9613–9627: "simultaneously over every unramified O_δ that arises … the same
typing applies at every descendant branching cell inside T_j, ABSOLUTE indices
throughout").

THE QUANTIFIER DISCIPLINE THIS LAYER EXISTS FOR (the compiled G2/G3 lesson —
D-SC principle P1): site data is SUPPLIED to the slot Props as carrier
parameters, NEVER ∀/∃-closed inside them.  The G2 BLOCKED record's two
countermodels (junk Dirac site kills ∀-closure at every CI; the identity site
True-ifies ∃-closure) both die at the supplied-carrier signature: the junk site
becomes the IB-G19a FALSIFIER witness, and the ∃-escape is gone because there is
no ∃.

E-PHASE RESOLUTIONS (each minimal, FLAGGED for the Q5 Codex audit):
* R-5 (naming): the draft's `Setting` lands as `RelSite`, `SettingsFamily` as
  `RelSiteFamily` — "site" is the failure records' own word for the missing
  carrier; re-homed into `LeanUrat.MovesU` like G1's CInterface (R-1's precedent).
* R-6 (phantom index): `p` is an explicit phantom parameter of `RelSite`
  (no field mentions it; the site sits over O_δ ⊂ W(F̄_p) and every consumer
  (`SiteDom`, `βarg`) demands the index) — G1's R-2 discipline, verbatim.
* R-7 (carrier-law boundary, D-SC principle P2 — the LAW/DATA SPLIT): `RelSite`
  keeps the draft's REALIZED-MEASURE laws as fields (event-algebra closure,
  condMass measure axioms, mass bounds) — these are STRUCTURAL wellformedness,
  what makes `condMass` a conditional content at all (BoxVol's precedent in G1).
  The note's REL.2 OBLIGATIONS over the site are NOT fields — they are the
  IB-G16 slot Props.  A degenerate site (Dirac condMass) remains constructible,
  BY DESIGN: it is the rel2b falsifier witness.
* R-8 (CF1, transcribed): `mem_pos` types the note's proviso "μ(Σ_c) > 0, the
  only cells any (SIB) display conditions on" as FAMILY SCOPE — the family IS
  the family of (SIB)-conditioning sites; no positive-cell existence law beyond
  the parameterized `ne`.

STATEMENT-FENCE FLAG: every structure below is NEW carrier vocabulary
(hypothesis-side; nothing here is a built-corpus statement and no ratified file
is touched).  Ratification = the Q5 Codex audit gate before any consumer
(IB-G13′) lands.  Non-vacuity duty for the slot Props over this layer: IB-G19a.
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesU

open MovesRBase

variable (p : ℕ) [Fact p.Prime]

/-- **THE BRANCH CONTINUATION SITE** (†17; the parked draft's `Setting`, verbatim
with R-6/R-7): one realized instance of the note's SETTING — ambient base O_δ,
realized prefix η, state cylinder Σ (frame Ψ_η), digit cell c, branch b_j; η/Σ/c/b_j
absorbed into carriers; the REALIZED-MEASURE LAWS are fields (draft finding 2).
`δ` is the ambient ABSOLUTE index (root δ = 1), `δrel` = δ_j^rel (residual degrees
g accumulated over F_δ down b_j), `d` = d_j (the O_δ-degree of b_j's cluster).
`FrameC`/`reframe` is (CF10) the AMBIENT C.0.5 frame family at the cell — (a5)'s
commutation quantifies over THIS family, so no instance can substitute a private
identity-only family.  `p` is a phantom index (R-6). -/
structure RelSite (p : ℕ) where
  δ : ℕ+                                  -- ambient ABSOLUTE index (root: δ = 1)
  δrel : ℕ+                               -- δ_j^rel over F_δ down b_j
  d : ℕ+                                  -- d_j, the O_δ-degree of b_j's cluster
  Cont : Type                             -- continuation points of Σ_c
  contNe : Nonempty Cont
  AmbEvents : Set (Set Cont)              -- the ambient event algebra on Σ_c
  univ_mem : Set.univ ∈ AmbEvents
  compl_mem : ∀ E ∈ AmbEvents, Eᶜ ∈ AmbEvents
  union_mem : ∀ E ∈ AmbEvents, ∀ E' ∈ AmbEvents, E ∪ E' ∈ AmbEvents
  cellMass : ℚ                            -- μ(Σ_c)
  cellMass_nonneg : 0 ≤ cellMass
  cellMass_le_one : cellMass ≤ 1
  condMass : Set Cont → ℚ                 -- μ( · │ Σ_c )
  condMass_nonneg : ∀ E, 0 ≤ condMass E
  condMass_empty : condMass ∅ = 0
  condMass_univ : 0 < cellMass → condMass Set.univ = 1
  condMass_add : ∀ E ∈ AmbEvents, ∀ E' ∈ AmbEvents,
    Disjoint E E' → condMass (E ∪ E') = condMass E + condMass E'
  PTree : Type                            -- prescribed finite subtrees T_j for b_j
  prescNe : Nonempty PTree
  SEvent : PTree → Set Cont               -- S_j(T); (W1)'s reading kept opaque
  SEvent_mem : ∀ T, SEvent T ∈ AmbEvents
  StateIdx : Type                         -- [3]/[3t]'s state indices
  τ : StateIdx                            -- τ_j(c)
  FrameC : Type                           -- (CF10) the ambient C.0.5 frame family
  frameCNe : Nonempty FrameC
  reframe : FrameC → FrameC → Cont → Cont

/-- `δ_j := δ·δ_j^rel` — the ABSOLUTE accumulated residue degree; the target base
is O_{δ_j} (BASE-INDEX CONVENTION: a literal subring of W(F̄_p)). -/
def RelSite.δabs {p : ℕ} (S : RelSite p) : ℕ+ := S.δ * S.δrel

/-- (a2)'s target degree `d_j^rel := d_j/δ_j^rel` (ℕ-division; INTEGRALITY is the
(a2) obligation, an IB-G16 law conjunct — never assumed here). -/
def RelSite.dRel {p : ℕ} (S : RelSite p) : ℕ := (S.d : ℕ) / (S.δrel : ℕ)

/-- (e2)'s DEGREE CONVENTION pinned: "the β-argument is p^{δ_j} with δ_j ABSOLUTE". -/
def RelSite.βarg {p : ℕ} [Fact p.Prime] (S : RelSite p) : ℕ := qq p S.δabs

/-- **THE REALIZED SITE FAMILY** (†17; the parked draft's `SettingsFamily`,
findings 19/20 + CF1): what the (SIB-Oδ)/REL.2 quantifiers range over — nonempty,
containing the root (δ = 1) reading, POSITIVE-mass by family scope (R-8), and
CLOSED UNDER DESCENT with absolute re-indexing ("the same typing applies at every
descendant branching cell inside T_j, ABSOLUTE indices throughout" — what
TREE-EXP's induction consumes).  Supplied by the ambient theory (wave-D); the
IB-G18 closure rows quantify over `mem`, so a junk family is the caller's visible
liability, never a hidden escape. -/
structure RelSiteFamily (p : ℕ) where
  mem : Set (RelSite p)
  ne : mem.Nonempty
  root_mem : ∃ S ∈ mem, S.δ = 1
  mem_pos : ∀ S ∈ mem, 0 < S.cellMass
  desc : (S : RelSite p) → S ∈ mem → S.PTree → Set (RelSite p)
  desc_sub : ∀ S hS T, desc S hS T ⊆ mem
  desc_amb : ∀ S hS T, ∀ S' ∈ desc S hS T, S'.δ = S.δabs

end LeanUrat.MovesU
