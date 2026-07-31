/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.MovesU.SlotsG16_sitedLaws

/-!
# IB-G17 — the REL.3 CONSUMED-DISPLAY carrier + sited slot (bridge BP1, D-SC, †20)

E-phase skeleton per `lean/notes/BRIDGE_BP1_INSTANCE_2026-07-30.md` DESIGN
ADDENDUM D-SC.  The sited re-type of the BLOCKED `Slot_rel3`
(`SlotsG3_rel3.lean`, untouched — the compiled failure record stands).

THE NOTE'S FIXED CONTENT (MOVES_2026-07-24.md 9639–9657, all that exists):
the [4]-side displays (SQ.0–SQ.2) DO NOT EXIST YET; what IS fixed is the
consumption DISCIPLINE — "SQ.2's cluster-size induction consumes each
base-changed leg β_m(p^δ) as a CERTIFIED O_δ-statement — the induction
hypothesis is an input theorem about vol_{O_δ}, NEVER the formal substitution
q ↦ q^δ in a ℤ_p-display".

HOW THIS DESIGN KILLS BOTH G3 COUNTERMODEL ARMS (D-SC principle P3 — DERIVED,
NOT FREE): the G3 BLOCKED record's abstract display pack carried a FREE value
read and a FREE event read, so a junk pack (value 2; value 1/3 at qq = 2^δ)
falsified every ∀-closure and a self-certified pack True-ified every ∃-closure.
`ConsumedDisplayPack` below carries NEITHER: a leg is ONLY a consumption KEY —
(site, first index, prescribed subtree).  The leg's VALUE is DERIVED as the
site's β-table read `β entryFirst τ βarg` (through the family's `RelAssignment`
data), and its EVENT is DERIVED as the realization event
`{g | TgtRealizes (tgtTcan g) (subtreeCorr T)}` — the (SIB-Oδ) display's own
right side.  The q ↦ q^δ substitution is EXCLUDED BY CONSTRUCTION: there is no
field a ℤ_p-display value could ride in; the certified form IS the vol_{O_δ}
equation.  What remains genuinely open — the tie of this pack to the ACTUAL
SQ.0–SQ.2 displays once [4] drafts them — is rel3's honest residue: the pack is
[4]-SUPPLIED (like `tableConv`/`consumed` are [3]-supplied, CF13/CF14), and
populating it faithfully is [4]'s wave-D drafting event, ledgered as such
(D-SC escalation E-3).  Round 1's sin (inventing SQ content) is not committed:
the pack types only the consumption keying the note itself fixes.

FORMULATION TARGET for `SitedSlot_rel3` (H-phase body, behind the Q5 audit):
∀ l : CD.Leg, with S := CD.site l, hS := CD.site_mem l, SD := RA.data S hS,
CI := RA.tgt S hS:
  (certification) `Slot_rel1 CI` (REL.1-conditional, displayed per site) ∧
    {g | SD.trees.TgtRealizes (SD.trees.tgtTcan g)
          (SD.trees.subtreeCorr (CD.presc l))} ∈ CI.C.V.events ∧
    SD.beta.β (CD.first l) S.τ S.βarg
      = CI.C.V.vol {g | …realizes (CD.presc l)…}
  (keying) CD.first l = SD.beta.entryFirst ∧ RA.tableConv (CD.first l) —
    the leg reads [3]'s table at [3]'s own key, never a re-key;
  (consumption tie) CD.presc l ∈ RA.consumed S hS — the [4]-consumed leg is
    among the prescriptions [3]'s table actually consumes at this key.
EMPTY-PACK CAVEAT (recorded for the audit): at `Leg := Empty` the slot is
vacuous — faithfully so (nothing is consumed until [4] drafts SQ.0–SQ.2); the
IB-G19a falsifier uses a one-leg junk pack (β ≡ 2 against any BoxVol, vol ≤ 1),
so the slot is NOT a tautology.  NON-VACUITY DUTY: IB-G19a.
QUANTIFIER-HYGIENE GATE: IB-G19b (as for IB-G16).
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesU

open MovesRBase

variable (p : ℕ) [Fact p.Prime]

/-- **THE PER-FAMILY DATA ASSIGNMENT** (†20/†21): one `SiteData` pack, one target
`CInterface` (at the site's ABSOLUTE base δ_j and target degree d_j^rel), and the
[3]/MovesS exports (`tableConv` — the first-index convention; `consumed` — the
prescriptions [3]'s tables actually consume, per site) for every member of the
realized family.  CF13/CF14 carried verbatim: the exports are SUPPLIED here,
never chosen by a slot.  Wave-D inhabits this at the real instance. -/
structure RelAssignment (Sp : SpeciesSyntax) (AD : AlphabetData p Sp)
    (Fam : RelSiteFamily p) where
  data : (S : RelSite p) → S ∈ Fam.mem → SiteData p S Sp AD
  tgt : (S : RelSite p) → S ∈ Fam.mem → CInterface p Sp AD S.δabs S.dRel
  tableConv : ℕ → Prop
  consumed : (S : RelSite p) → S ∈ Fam.mem → Set S.PTree

/-- **THE [4]-SIDE CONSUMED-DISPLAY PACK** (†20): the SQ.0–SQ.2 consumption
KEYING, and nothing else — each leg names the site it is consumed at, the
β-table first index it reads, and the prescribed subtree it prices.  NO value
field, NO event field (D-SC principle P3: both are DERIVED at the slot — the
G3 countermodel's junk-value arm and the self-certification arm are both
structurally impossible).  [4]-SUPPLIED; populated when [4] drafts SQ.0–SQ.2
(the note's own acceptance criterion for stating REL.3). -/
structure ConsumedDisplayPack (Fam : RelSiteFamily p) where
  Leg : Type
  site : Leg → RelSite p
  site_mem : ∀ l, site l ∈ Fam.mem
  first : Leg → ℕ
  presc : (l : Leg) → (site l).PTree

/-- IB-G17 — **`SitedSlot_rel3`** (CL-8 REL.3, owner [2r]; the sited re-type of
the BLOCKED `Slot_rel3`): every [4]-consumed leg β_m(p^δ) is CERTIFIED as a
vol_{O_δ} statement at its own site — the β-table read at the leg's key equals
the target `BoxVol` mass of the leg's realization event, `Slot_rel1`-conditional
per site, with the q ↦ q^δ formal substitution excluded by construction (no
value/event fields exist to substitute into — see the file header).  H-phase
fills the displayed Prop behind the Q5 audit; IB-G19b gates the fill. -/
def SitedSlot_rel3 {p : ℕ} [Fact p.Prime] {Sp : SpeciesSyntax}
    {AD : AlphabetData p Sp} (Fam : RelSiteFamily p)
    (RA : RelAssignment p Sp AD Fam) (CD : ConsumedDisplayPack p Fam) : Prop :=
  sorry

end LeanUrat.MovesU
