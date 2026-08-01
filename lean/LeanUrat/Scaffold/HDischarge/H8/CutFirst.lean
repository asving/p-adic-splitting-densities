/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.Scaffold.HDischarge.H8.CutDefs
import LeanUrat.Scaffold.Shared.FirstEntrance
import LeanUrat.MovesT.F0_preHalt

/-! # H8-A1 `CutFirst.lean` — (CUT-1), the first-entrance calculus (Wave 1)

`firstEntAbove_unique` / `firstEntAbove_exists` / `firstEntAbove_shallowRead` /
`firstEntAbove_mem_chains`.  Statements VERBATIM from
`lean/blueprints/HDISCHARGE_H8.md` §4 Wave 1.  Kills G-2 falsifier #3 at
level (1a).  Deps: H8-D0.

HOIST RECORD (SYNTHESIS_PASS3 F1, 2026-08-01): the proofs formerly here
(prefix totality via `List.prefix_or_prefix_of_prefix`, antisymmetry via
lengths + `history_ext` exactly as `vtree_pathOrder`'s antisymm leg,
existence by classical choice on the minimal-length entrance prefix — no
decidability of `E` assumed) moved VERBATIM, carrier-generic, to
`Scaffold/Shared/FirstEntrance.lean`.  The statements below are UNCHANGED;
each proof is now the instantiation of the shared lemma at the `Carrier`
instance for `History p F` declared here (prefix = nodewise list prefix,
size = node count) — H8's `ProperPrefix`/`ShallowRead`/`FirstEntAbove`
(`CutDefs.lean`, untouched) are definitionally the shared ones at this
instance. -/

set_option linter.style.longLine false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace LeanUrat.Scaffold.HDischarge.H8

open LeanUrat.MovesC LeanUrat.MovesD LeanUrat.MovesT

variable {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]

/-- The `History p F` carrier of the shared first-entrance calculus
(SYNTHESIS_PASS3 F1): prefix = `History.IsPrefixOf` (nodewise list prefix),
size = `nodes.length`; antisymmetry via `history_ext` +
`List.IsPrefix.eq_of_length`, downward totality via
`List.prefix_or_prefix_of_prefix` — the exact proof stock of the former
in-file proofs. -/
instance : Shared.FirstEntrance.Carrier (History p F) where
  IsPrefixOf := History.IsPrefixOf
  size H := H.nodes.length
  prefix_refl H := List.prefix_refl _
  prefix_trans h1 h2 := List.IsPrefix.trans h1 h2
  size_mono h := List.IsPrefix.length_le h
  eq_of_prefix_of_size_le h hle :=
    history_ext (List.IsPrefix.eq_of_length h
      ((List.IsPrefix.length_le h).antisymm hle))
  prefix_total_of_prefix h1 h2 := List.prefix_or_prefix_of_prefix h1 h2

/-- The `VTree` chain set is prefix-closed in the shared sense: `Tr.hclosed`
with the nonemptiness clause discharged by `History.nonempty`. -/
lemma vtree_prefix_closed (Tr : VTree p F) :
    ∀ H ∈ Tr.chains, ∀ ε : History p F,
      Shared.FirstEntrance.Carrier.IsPrefixOf ε H → ε ∈ Tr.chains :=
  fun H hH ε hpre => Tr.hclosed H hH ε hpre ε.nonempty

/-- Helper (prover's discretion, no content): a proper prefix is strictly
shorter — prefix `length_le` sharpened by `history_ext` antisymmetry. -/
lemma ProperPrefix.length_lt {H' H : History p F} (h : ProperPrefix H' H) :
    H'.nodes.length < H.nodes.length :=
  Shared.FirstEntrance.ProperPrefix.size_lt (α := History p F) h

/-- (CUT-1) uniqueness: two first entrances above the same `H` mutually
prefix each other (each one's clause 3 applied to the other), hence agree. -/
theorem firstEntAbove_unique (E : History p F → Prop) {ε₁ ε₂ H : History p F}
    (h1 : FirstEntAbove E ε₁ H) (h2 : FirstEntAbove E ε₂ H) : ε₁ = ε₂ :=
  Shared.FirstEntrance.firstEntAbove_unique E h1 h2

/-- (CUT-1) existence: a non-shallow read has a first entrance above it —
take the minimal-`nodes.length` entrance proper prefix (classical, via
`Nat.sInf` on the length set; no decidability of `E`); prefix totality
(`List.prefix_or_prefix_of_prefix`, both being prefixes of the LIST
`H.nodes`) + length minimality force it below every other entrance. -/
theorem firstEntAbove_exists (E : History p F → Prop) {H : History p F}
    (h : ¬ ShallowRead E H) : ∃ ε, FirstEntAbove E ε H :=
  Shared.FirstEntrance.firstEntAbove_exists E h

/-- (CUT-1) minimality (first entrances are shallow reads): an entrance
proper prefix `H''` of `ε` would be an entrance proper prefix of `H`
strictly shorter than `ε`, yet clause 3 puts `ε` below it — length
contradiction. -/
theorem firstEntAbove_shallowRead (E : History p F → Prop) {ε H : History p F}
    (h : FirstEntAbove E ε H) : E ε ∧ ShallowRead E ε :=
  Shared.FirstEntrance.firstEntAbove_shallowRead E h

/-- (CUT-1) closure: the first entrance above a chain is itself a chain —
`hclosed` at `H` with `ε ≼ H` and `ε.nodes ≠ []` (= `ε.nonempty`). -/
theorem firstEntAbove_mem_chains (Tr : VTree p F) (E : History p F → Prop)
    {ε H : History p F} (hH : H ∈ Tr.chains) (h : FirstEntAbove E ε H) :
    ε ∈ Tr.chains :=
  Shared.FirstEntrance.firstEntAbove_mem_chains (vtree_prefix_closed Tr) E hH h

end LeanUrat.Scaffold.HDischarge.H8
