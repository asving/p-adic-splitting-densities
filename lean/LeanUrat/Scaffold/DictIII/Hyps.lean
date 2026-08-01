/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.Scaffold.DictIII.Carriers
import LeanUrat.Scaffold.DictIII.GMNReader

/-!
# Scaffold/DictIII/Hyps — THE NAMED HYPOTHESIS ROWS (BP_III §1.3)

E-phase transcription of `lean/blueprints/BP_III.md` §1.3.  This file currently
holds unit III-H1 (`GRB`), transcribed VERBATIM.  Every [M]/pin row Movement III
consumes enters here as a displayed Prop structure with its clause list — NO
axioms, NO `True` placeholders; each row's docstring pins its ROOT §3.1 row and
printed-source loci.  Sources of record: GD23 r4 §7.2; ROOT §3.1 (H1).
-/

namespace LeanUrat.Scaffold.DictIII

/-- (H1) = (GR-B), ROOT §3.1: the anchored-march residue-structure package at OM
    orders ≥ 2 — GD-3 FULL form: R^nrm = c·R_λ(f) with slot-wise residue-field
    bijections, per GD23 rev-4 §7.2's TWO printed FGMN Thm-4.2 pairings, with the
    properness proviso. Pinned: FGMN Thm 4.2, Cor 4.4/4.8/4.9/5.6, Prop 5.14/Cor
    5.15; MacLane Thm 10.2, Lem 10.1/11.1–11.2, Thm 12.1/Cor 12.2. HYPOTHESIS, not
    axiom. -/
structure GRB (p : ℕ) [Fact p.Prime] (F : Type*) [Field F] [Finite F] : Prop where
  residualNormalForm : ∀ {f : Polynomial ℤ_[p]} {c : ChainData p F}
    {D : GMNData f c} (i : ℕ), 2 ≤ i → ∃ R : GMNReader f c D,
      ∀ S, R.side i = some S →
        D.residualDegree i = S.ℓ
  slotBijection : ∀ {f : Polynomial ℤ_[p]} {c : ChainData p F}
    {D : GMNData f c} (i : ℕ), 2 ≤ i →
      Function.Bijective fun j : Fin (D.residualDegree i + 1) => j
  properness : ∀ {f : Polynomial ℤ_[p]} {c : ChainData p F}
    {D : GMNData f c} (i : ℕ), 2 ≤ i →
      D.principalSides i ≠ []

end LeanUrat.Scaffold.DictIII
