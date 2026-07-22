/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.OM.ChainMenu

/-!
# ChainMenu6 — Wave W6c-c: the depth-0 widening of the chain menu (scope-#5 menu)

**Provenance.** `notes/WILD_WAVE6C_BLUEPRINT_2026-07-22.md` §0 design-headline point 2,
§2-W6c-c, §3 (the scope-#5 statement design). ADDITIVE module: `OM/ChainMenu.lean` is not
touched.

## The object

Wave 5b's `ChainMenu.chainShapes` emits chain literals `chainLit ms leaf` ONLY for `ms ≠ []`
(the depth-`≥ 1` descent chains); the depth-0 leaf reads of the accepted W6 full model (the
even-height inert/split cluster leaves and the depth-0 ram rungs at the root frame) therefore
have NO menu literal, which is exactly the honest-limits gap recorded at the W6 capstone.
THIS module supplies the missing emission and the widened menu:

* `chainShapes0 n K σ` — the depth-0 leaf literals `chainLit [] leaf`, `leaf ∈ chainLeaves K σ`
  (`n = 2` only, σ-keyed, window `K`) — the `chainShapes` emission WITHOUT the `ms ≠ []`
  filter, at the one depth that filter excludes;
* `omMenu6 n D K σ := ChainMenu.omMenu5 n D K σ ∪ chainShapes0 n K σ` — the Wave-6 σ-keyed
  menu, with `omMenu5_subset_omMenu6` (the scope-#4 → scope-#5 recovery inclusion) and the
  discriminator `mem_omMenu6_cases`;
* `mem_omMenu6_type` / `eq_of_mem_omMenu6` — the `typeOf5`-keying alignment over the widened
  menu (the omMenu5 lemmas' analogues; new members via `ChainMenu.typeOf5_chainLit` +
  `ChainMenu.of_mem_chainLeaves`).

**Facts cited, not reproved** (they hold for ALL `ms`, including `[]`):
`ChainMenu.headOrd_chainLit` (`headOrd (chainLit [] leaf) = 2` — the family discriminator),
`ChainMenu.decodeMs_chainLit` / `ChainMenu.decodeLeaf_chainLit` / `ChainMenu.chainLit_injective`
(exact decode). Consequently `OmLeafFaithful.fiberOf5` already dispatches the new literals to
`ChainMenu.ChainCell [] leaf` = the `ChainPair [] leaf = LeafPair leaf` digit fiber — the
EXACT depth-0 fiber the W6 model counts; the axiom re-scope in `OM/OmLeafFaithful.lean`
(scope #5) is therefore a pure menu widening with `hfib` byte-identical.

Anti-vacuity note (blueprint §3): below the leaf threshold (`L₀ < leafNeed leaf`) the depth-0
fiber is empty via `ChainMenu.chainPair_empty` at `ms = []` (i.e. `leafPair_empty`;
`leafNeed ≥ 1 > 0` = the budget slack), so small-frame instances of the widened axiom are
vacuous exactly as at every depth `≥ 1`.

Discipline: no `sorry`, no new axiom; core-only footprint (`AxCheck`).
-/

set_option linter.style.longLine false
set_option linter.style.header false

namespace LeanUrat.OM.ChainMenu6

open scoped Classical
open LeanUrat LeanUrat.OM Finset
open LeanUrat.OM.CellMenu
open LeanUrat.OM.ChainMenu

/-- **The depth-0 leaf literals** (blueprint §2-W6c-c): the `chainShapes` emission WITHOUT the
`ms ≠ []` filter — `chainLit [] leaf` for each σ-keyed window leaf. `n = 2` ONLY, exactly as
`ChainMenu.chainShapes` (the general-`n` chains stay OPEN-D3/D5 territory). -/
noncomputable def chainShapes0 (n K : ℕ) (σ : FactorizationType) : Finset ClusterShape :=
  if n = 2 then (chainLeaves K σ).image (fun leaf => chainLit [] leaf) else ∅

theorem mem_chainShapes0 {n K : ℕ} {σ : FactorizationType} {T : ClusterShape} :
    T ∈ chainShapes0 n K σ ↔ n = 2 ∧ ∃ leaf ∈ chainLeaves K σ, T = chainLit [] leaf := by
  constructor
  · intro hT
    by_cases hn : n = 2
    · subst hn
      rw [chainShapes0, if_pos rfl, Finset.mem_image] at hT
      obtain ⟨leaf, hleaf, rfl⟩ := hT
      exact ⟨rfl, leaf, hleaf, rfl⟩
    · rw [chainShapes0, if_neg hn] at hT
      exact absurd hT (Finset.notMem_empty T)
  · rintro ⟨rfl, leaf, hleaf, rfl⟩
    rw [chainShapes0, if_pos rfl, Finset.mem_image]
    exact ⟨leaf, hleaf, rfl⟩

/-- **The Wave-6 σ-keyed menu** (the scope-#5 menu): the Wave-5 menu extended by the depth-0
leaf literals. -/
noncomputable def omMenu6 (n D K : ℕ) (σ : FactorizationType) : Finset ClusterShape :=
  ChainMenu.omMenu5 n D K σ ∪ chainShapes0 n K σ

/-- **The recovery inclusion**: every scope-#4 menu shape is a scope-#5 menu shape (the menu
leg of the derived theorem `OmLeafFaithful.om_leaf_faithful_w5`). -/
theorem omMenu5_subset_omMenu6 (n D K : ℕ) (σ : FactorizationType) :
    ChainMenu.omMenu5 n D K σ ⊆ omMenu6 n D K σ :=
  Finset.subset_union_left

/-- Menu case analysis: a Wave-6 menu shape is a Wave-5 menu shape or a depth-0 leaf literal. -/
theorem mem_omMenu6_cases {n D K : ℕ} {σ : FactorizationType} {T : ClusterShape} :
    T ∈ omMenu6 n D K σ
      ↔ T ∈ ChainMenu.omMenu5 n D K σ
        ∨ (n = 2 ∧ ∃ leaf ∈ chainLeaves K σ, T = chainLit [] leaf) := by
  rw [omMenu6, Finset.mem_union, mem_chainShapes0]

/-- **Every Wave-6 menu shape names its type** (the `mem_omMenu5_type` analogue; new members
via `typeOf5_chainLit` + `of_mem_chainLeaves`). -/
theorem mem_omMenu6_type {n D K : ℕ} {σ : FactorizationType} {T : ClusterShape}
    (hT : T ∈ omMenu6 n D K σ) : typeOf5 n T = some σ := by
  rcases mem_omMenu6_cases.mp hT with h | ⟨-, leaf, hleaf, rfl⟩
  · exact mem_omMenu5_type h
  · rw [typeOf5_chainLit, (of_mem_chainLeaves hleaf).2]

/-- Distinct types have disjoint Wave-6 menus — at ANY window bounds (the `eq_of_mem_omMenu5`
analogue). -/
theorem eq_of_mem_omMenu6 {n D D' K K' : ℕ} {σ σ' : FactorizationType} {T : ClusterShape}
    (h : T ∈ omMenu6 n D K σ) (h' : T ∈ omMenu6 n D' K' σ') : σ = σ' := by
  have h1 := mem_omMenu6_type h
  have h2 := mem_omMenu6_type h'
  rw [h1] at h2
  exact Option.some.inj h2

/-! ## Axiom census (this module declares NO axiom; expected footprints: Lean core only) -/

section AxCheck

#print axioms LeanUrat.OM.ChainMenu6.chainShapes0
#print axioms LeanUrat.OM.ChainMenu6.mem_chainShapes0
#print axioms LeanUrat.OM.ChainMenu6.omMenu6
#print axioms LeanUrat.OM.ChainMenu6.omMenu5_subset_omMenu6
#print axioms LeanUrat.OM.ChainMenu6.mem_omMenu6_cases
#print axioms LeanUrat.OM.ChainMenu6.mem_omMenu6_type
#print axioms LeanUrat.OM.ChainMenu6.eq_of_mem_omMenu6

end AxCheck

end LeanUrat.OM.ChainMenu6
