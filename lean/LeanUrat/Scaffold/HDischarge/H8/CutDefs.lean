/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.MovesT.Defs
import LeanUrat.MovesT.D8_pathOrder

/-! # H8-D0 `CutDefs.lean` — the cut vocabulary (Wave 0)

`ProperPrefix` / `ShallowRead` / `FirstEntAbove` / `minEnts` / `shallowReads` /
`blockReads` over `History p F` and `VTree`, plus definitional `mem_*` simp
lemmas.  Statements VERBATIM from `lean/blueprints/HDISCHARGE_H8.md` §4. -/

set_option linter.style.longLine false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace LeanUrat.Scaffold.HDischarge.H8

open LeanUrat.MovesC LeanUrat.MovesD LeanUrat.MovesT

variable {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]

/-- Proper prefix among histories (nodewise list prefix, strict). -/
def ProperPrefix (H' H : History p F) : Prop := H'.IsPrefixOf H ∧ H' ≠ H

/-- SHALLOW READ (the (BDY)-shifted ownership): no PROPER prefix of `H` is an
entrance — `H`'s own entering read is charged to the shallow layer. -/
def ShallowRead (E : History p F → Prop) (H : History p F) : Prop :=
  ∀ H', ProperPrefix H' H → ¬ E H'

/-- `ε` is THE FIRST ENTRANCE strictly above `H`. -/
def FirstEntAbove (E : History p F → Prop) (ε H : History p F) : Prop :=
  E ε ∧ ProperPrefix ε H ∧ ∀ H', E H' → ProperPrefix H' H → ε.IsPrefixOf H'

/-- MINIMAL (first) entrances of the tree — the block roots of the shallow cut. -/
noncomputable def minEnts (Tr : VTree p F) (E : History p F → Prop) :
    Finset (History p F) := by
  classical
  exact Tr.hfin.toFinset.filter (fun ε => E ε ∧ ShallowRead E ε)

/-- The shallow-owned read sites. -/
noncomputable def shallowReads (Tr : VTree p F) (E : History p F → Prop) :
    Finset (History p F) := by
  classical
  exact Tr.hfin.toFinset.filter (ShallowRead E)

/-- The block-`ε`-owned read sites. -/
noncomputable def blockReads (Tr : VTree p F) (E : History p F → Prop)
    (ε : History p F) : Finset (History p F) := by
  classical
  exact Tr.hfin.toFinset.filter (FirstEntAbove E ε)

/-! ## Definitional membership lemmas (unfold the filters) -/

@[simp] lemma mem_minEnts {Tr : VTree p F} {E : History p F → Prop}
    {ε : History p F} :
    ε ∈ minEnts Tr E ↔ ε ∈ Tr.chains ∧ E ε ∧ ShallowRead E ε := by
  classical
  simp [minEnts, Set.Finite.mem_toFinset]

@[simp] lemma mem_shallowReads {Tr : VTree p F} {E : History p F → Prop}
    {H : History p F} :
    H ∈ shallowReads Tr E ↔ H ∈ Tr.chains ∧ ShallowRead E H := by
  classical
  simp [shallowReads, Set.Finite.mem_toFinset]

@[simp] lemma mem_blockReads {Tr : VTree p F} {E : History p F → Prop}
    {ε H : History p F} :
    H ∈ blockReads Tr E ε ↔ H ∈ Tr.chains ∧ FirstEntAbove E ε H := by
  classical
  simp [blockReads, Set.Finite.mem_toFinset]

end LeanUrat.Scaffold.HDischarge.H8
