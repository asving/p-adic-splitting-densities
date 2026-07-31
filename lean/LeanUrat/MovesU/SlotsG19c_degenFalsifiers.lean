/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.MovesU.SlotsG18_relPack

/-!
# IB-G19c — COMPILED DEGENERATE-CARRIER FALSIFIERS (bridge BP1, D-SC REVISION 2)

The REVISE-round verdict on addendum D-SC (5 CRITICAL / 3 GAP, 2026-07-31)
identified SUPPLIED-CARRIER VACUITY as the recurring defect class: the
originally displayed H-phase targets were TRUE at empty/degenerate supplied
carriers (`consumed = ∅`, `tableConv = fun _ => True`, `Leg := Empty`), so the
planned falsifiers (which targeted only NON-degenerate junk) could never fire
against the actual escapes.  D-SC REVISION 2 repaired the targets at the
STATEMENT level (R-16..R-20: the `Tj`-anchored (e3)/(e5), the unique-agreement
(e4), the population + coverage conjuncts of rel3); this unit is the COMPILED
evidence that the repairs bite — each previously escaping degenerate carrier
now REFUTES its target, uniformly (no concrete carrier construction needed:
the refuted conjunct is uniformly false at the degenerate parameter).

PROBE FENCE (as IB-G19b's): the `ProbeTarget_*` definitions below are
PROBE-LOCAL COPIES of the displayed H-phase targets in the IB-G16/IB-G17 file
headers (byte-faithful modulo binder names; IB-G20's closure manifest owes a
drift flag between these copies, the G16/G17 headers, and the G19b probes).
They are NOT the canonical `SitedSlot_*` (whose bodies stay `sorry` behind the
Q5 audit) and NOTHING may consume them as evidence of content — their sole
role is hosting the negation theorems.

WHAT REMAINS AT IB-G19a (after the H-phase fills; value-level falsifiers with
real prerequisites, listed with what each needs): rel2b's inverted-Dirac
countermodel (needs two disjoint cylinder events + a positive-mass junk site);
rel2d's constant `tgtTcan` vs non-constant `nodeCorr ∘ ambTcan` (needs a
constructible non-constant composite); the β ≡ 2 falsifiers for rel2e/rel3
(need a concrete `CInterface` with a proved `vol ≤ 1` bound and a realizable
event).  None of those are claimed here.
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesU

open MovesRBase

section rel2e

variable {p : ℕ} [Fact p.Prime] {Sp : SpeciesSyntax} {AD : AlphabetData p Sp}

/-- PROBE-LOCAL copy of `SitedSlot_rel2e`'s REVISED displayed target (IB-G16
header, D-SC REVISION 2): (e1) ∧ (e4 unique agreement) ∧ (e5 coverage +
determination at `S.Tj`) ∧ (e3 `Slot_rel1` + MASS = ENTRY pinned at `S.Tj`).
Probe fence: consumable by nothing; hosts the negation theorems only. -/
def ProbeTarget_rel2e (S : RelSite p) (SD : SiteData p S Sp AD)
    (tableConv : ℕ → Prop) (consumed : Set S.PTree)
    (CI : CInterface p Sp AD S.δabs S.dRel) : Prop :=
  (∀ s, SD.beta.stateReadsRel (SD.beta.stateDict s)
    = (SD.beta.stateReadsAmb s).map SD.dict.readDict) ∧
  (tableConv SD.beta.entryFirst ∧ ∀ m, tableConv m → m = SD.beta.entryFirst) ∧
  (S.Tj ∈ consumed ∧ ∀ T ∈ consumed, T = S.Tj) ∧
  (Slot_rel1 CI ∧
    {g | SD.trees.TgtRealizes (SD.trees.tgtTcan g) (SD.trees.subtreeCorr S.Tj)}
      ∈ CI.C.V.events ∧
    SD.beta.β SD.beta.entryFirst S.τ S.βarg
      = CI.C.V.vol {g | SD.trees.TgtRealizes (SD.trees.tgtTcan g) (SD.trees.subtreeCorr S.Tj)})

/-- FALSIFIER (REVISE finding 1's adversary, killed at the statement): the
EMPTY supplied `consumed` refutes the revised rel2e target at EVERY site, data
pack, convention, and CI — uniformly, because (e5)'s coverage half demands
`S.Tj ∈ ∅`. -/
theorem rel2e_probe_refuted_at_empty_consumed
    (S : RelSite p) (SD : SiteData p S Sp AD) (tableConv : ℕ → Prop)
    (CI : CInterface p Sp AD S.δabs S.dRel) :
    ¬ ProbeTarget_rel2e S SD tableConv (∅ : Set S.PTree) CI := by
  rintro ⟨-, -, ⟨hmem, -⟩, -⟩
  simp at hmem

/-- FALSIFIER (REVISE finding 5's adversary, killed at the statement): the
free `fun _ => True` convention refutes the revised rel2e target at EVERY
site, data pack, `consumed`, and CI — uniformly, because (e4)'s determination
half forces `entryFirst + 1 = entryFirst`. -/
theorem rel2e_probe_refuted_at_trivial_tableConv
    (S : RelSite p) (SD : SiteData p S Sp AD) (consumed : Set S.PTree)
    (CI : CInterface p Sp AD S.δabs S.dRel) :
    ¬ ProbeTarget_rel2e S SD (fun _ => True) consumed CI := by
  rintro ⟨-, ⟨-, hdet⟩, -, -⟩
  have h := hdet (SD.beta.entryFirst + 1) trivial
  omega

/-- FALSIFIER (the D-SC.3 table's original two-element-`consumed` falsifier,
now UNIFORM — no junk-site construction needed): any two DISTINCT consumed
prescriptions refute (e5)'s determination half. -/
theorem rel2e_probe_refuted_at_two_elements
    (S : RelSite p) (SD : SiteData p S Sp AD) (tableConv : ℕ → Prop)
    (consumed : Set S.PTree) (CI : CInterface p Sp AD S.δabs S.dRel)
    (T T' : S.PTree) (hT : T ∈ consumed) (hT' : T' ∈ consumed) (hne : T ≠ T') :
    ¬ ProbeTarget_rel2e S SD tableConv consumed CI := by
  rintro ⟨-, -, ⟨-, hdet⟩, -⟩
  exact hne ((hdet T hT).trans (hdet T' hT').symm)

end rel2e

section rel3

variable {p : ℕ} [Fact p.Prime] {Sp : SpeciesSyntax} {AD : AlphabetData p Sp}

/-- PROBE-LOCAL copy of `SitedSlot_rel3`'s REVISED displayed target (IB-G17
header, D-SC REVISION 2): population ∧ coverage ∧ per-leg (certification ∧
keying ∧ consumption tie).  Probe fence: consumable by nothing. -/
def ProbeTarget_rel3 (Fam : RelSiteFamily p) (RA : RelAssignment p Sp AD Fam)
    (CD : ConsumedDisplayPack p Fam) : Prop :=
  Nonempty CD.Leg ∧
  (∀ (S : RelSite p) (hS : S ∈ Fam.mem), ∀ T ∈ RA.consumed S hS,
    ∃ l : CD.Leg,
      (⟨CD.site l, CD.presc l⟩ : Σ S' : RelSite p, S'.PTree) = ⟨S, T⟩) ∧
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
      RA.tableConv (CD.site l) (CD.site_mem l) (CD.first l)) ∧
    CD.presc l ∈ RA.consumed (CD.site l) (CD.site_mem l)

/-- FALSIFIER (REVISE finding 2's adversary, killed at the statement): the
EMPTY display pack refutes the revised rel3 target at EVERY family and
assignment — uniformly, via the population conjunct.  The pre-revision
"vacuous-faithfully at `Leg := Empty`" reading is thereby RETIRED: an empty
pack can no longer discharge anything wearing REL.3's name. -/
theorem rel3_probe_refuted_at_empty_pack
    (Fam : RelSiteFamily p) (RA : RelAssignment p Sp AD Fam)
    (CD : ConsumedDisplayPack p Fam) (hE : IsEmpty CD.Leg) :
    ¬ ProbeTarget_rel3 Fam RA CD := by
  rintro ⟨⟨l⟩, -, -⟩
  exact hE.false l

omit [Fact p.Prime] in
/-- WITNESS (REVISE finding 7's rebuttal, compiled): the rel2b positive-cell
guard FIRES at every site the IB-G18 rows quantify over — this is exactly
G14's `RelSiteFamily.mem_pos` family-scope law (CF1/R-8), which the finding's
paste evidently lacked.  A supplied zero-mass site is not a family member, so
no row obligation is vacated by the guard. -/
theorem rel2b_guard_fires_on_family (Fam : RelSiteFamily p)
    (S : RelSite p) (hS : S ∈ Fam.mem) : 0 < S.cellMass :=
  Fam.mem_pos S hS

end rel3

end LeanUrat.MovesU
