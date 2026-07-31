/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.MovesU.SlotsG18_relPack

/-!
# IB-G19d — CANONICAL degenerate-carrier falsifiers (bridge BP1, D-SC H-phase fill)

FALSIFIER RE-POINT after the 2026-07-31 H-phase fill (Q5 Codex re-review ACCEPT,
`/tmp/bridge/ratify/dsc_review2.jsonl`; design record: D-SC REVISION 2 in
`lean/notes/BRIDGE_BP1_INSTANCE_2026-07-30.md`).  `SlotsG19c_degenFalsifiers.lean`
proved the REVISION-2 degenerate-class refutations against PROBE-LOCAL COPIES of
the displayed targets (the canonical bodies were `sorry` at the time; the probe
fence stands — nothing consumes the probes).  This unit re-proves the SAME
refutations at the SAME degenerate carriers against the CANONICAL `SitedSlot_*`
definitions (now filled from the ratified targets), discharging the IB-G19a
non-vacuity duty for the degenerate class, and adds the IB-G18 ROW-LEVEL
corollaries: a `RelCarrierPack` whose supplied exports are degenerate at ANY
family site refutes the whole row — the True-escape is dead at the rows, and a
degenerate pack is the caller's visible, falsifiable liability.

Same four degenerate carriers as G19c (the REVISE-round defect class): empty
`consumed`, the free `fun _ => True` `tableConv`, two distinct consumed
prescriptions, the empty display pack.  What remains at IB-G19a is unchanged
(the value-level falsifiers with real prerequisites, listed in G19c's header).
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesU

open MovesRBase

section rel2e

variable {p : ℕ} [Fact p.Prime] {Sp : SpeciesSyntax} {AD : AlphabetData p Sp}

/-- CANONICAL falsifier (REVISE finding 1's adversary, at the filled
`SitedSlot_rel2e`): the EMPTY supplied `consumed` refutes the slot at EVERY
site, data pack, convention, and CI — (e5)'s coverage half demands
`S.Tj ∈ ∅`. -/
theorem sitedSlot_rel2e_refuted_at_empty_consumed
    (S : RelSite p) (SD : SiteData p S Sp AD) (tableConv : ℕ → Prop)
    (CI : CInterface p Sp AD S.δabs S.dRel) :
    ¬ SitedSlot_rel2e S SD tableConv (∅ : Set S.PTree) CI := by
  intro h
  simpa using h.2.2.1.1

/-- CANONICAL falsifier (REVISE finding 5's adversary, at the filled
`SitedSlot_rel2e`): the free `fun _ => True` convention refutes the slot at
EVERY site, data pack, `consumed`, and CI — (e4)'s determination half forces
`entryFirst + 1 = entryFirst`. -/
theorem sitedSlot_rel2e_refuted_at_trivial_tableConv
    (S : RelSite p) (SD : SiteData p S Sp AD) (consumed : Set S.PTree)
    (CI : CInterface p Sp AD S.δabs S.dRel) :
    ¬ SitedSlot_rel2e S SD (fun _ => True) consumed CI := by
  intro h
  have hdet := h.2.1.2 (SD.beta.entryFirst + 1) trivial
  omega

/-- CANONICAL falsifier (the D-SC.3 table's two-element-`consumed` falsifier,
at the filled `SitedSlot_rel2e`): any two DISTINCT consumed prescriptions
refute (e5)'s determination half. -/
theorem sitedSlot_rel2e_refuted_at_two_elements
    (S : RelSite p) (SD : SiteData p S Sp AD) (tableConv : ℕ → Prop)
    (consumed : Set S.PTree) (CI : CInterface p Sp AD S.δabs S.dRel)
    (T T' : S.PTree) (hT : T ∈ consumed) (hT' : T' ∈ consumed) (hne : T ≠ T') :
    ¬ SitedSlot_rel2e S SD tableConv consumed CI := by
  intro h
  exact hne ((h.2.2.1.2 T hT).trans (h.2.2.1.2 T' hT').symm)

end rel2e

section rel3

variable {p : ℕ} [Fact p.Prime] {Sp : SpeciesSyntax} {AD : AlphabetData p Sp}

/-- CANONICAL falsifier (REVISE finding 2's adversary, at the filled
`SitedSlot_rel3`): the EMPTY display pack refutes the slot at EVERY family and
assignment, via the population conjunct — before [4] populates the pack, REL.3
is an UNDISCHARGED hypothesis, never a vacuous truth. -/
theorem sitedSlot_rel3_refuted_at_empty_pack
    (Fam : RelSiteFamily p) (RA : RelAssignment p Sp AD Fam)
    (CD : ConsumedDisplayPack p Fam) (hE : IsEmpty CD.Leg) :
    ¬ SitedSlot_rel3 Fam RA CD := by
  intro h
  exact hE.false h.1.some

end rel3

section rows

/-- ROW-LEVEL falsifier: a `RelCarrierPack` whose supplied `consumed` export is
EMPTY at any single family site (at any prime) refutes the whole `RelRow_rel2e`
∀-closure — the G18 row is no tautology, and a degenerate supplied pack is the
caller's visible liability. -/
theorem relRow_rel2e_refuted_at_empty_consumed (RP : RelCarrierPack)
    (p : ℕ) [Fact p.Prime] (S : RelSite p) (hS : S ∈ (RP.fam p).mem)
    (h : (RP.assign p).consumed S hS = ∅) : ¬ RelRow_rel2e RP := by
  intro hrow
  have hslot := hrow p S hS
  rw [h] at hslot
  exact sitedSlot_rel2e_refuted_at_empty_consumed S _ _ _ hslot

/-- ROW-LEVEL falsifier: a `RelCarrierPack` whose supplied `tableConv` export is
the free `fun _ => True` at any single family site refutes `RelRow_rel2e`. -/
theorem relRow_rel2e_refuted_at_trivial_tableConv (RP : RelCarrierPack)
    (p : ℕ) [Fact p.Prime] (S : RelSite p) (hS : S ∈ (RP.fam p).mem)
    (h : (RP.assign p).tableConv S hS = fun _ => True) : ¬ RelRow_rel2e RP := by
  intro hrow
  have hslot := hrow p S hS
  rw [h] at hslot
  exact sitedSlot_rel2e_refuted_at_trivial_tableConv S _ _ _ hslot

/-- ROW-LEVEL falsifier: a `RelCarrierPack` whose supplied display pack is EMPTY
at any prime refutes the whole `RelRow_rel3` ∀-closure. -/
theorem relRow_rel3_refuted_at_empty_pack (RP : RelCarrierPack)
    (p : ℕ) [Fact p.Prime] (hE : IsEmpty (RP.display p).Leg) :
    ¬ RelRow_rel3 RP := by
  intro hrow
  exact sitedSlot_rel3_refuted_at_empty_pack (RP.fam p) (RP.assign p)
    (RP.display p) hE (hrow p)

end rows

end LeanUrat.MovesU
