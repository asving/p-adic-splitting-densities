/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.Scaffold.HDischarge.H8.CutDefs
import LeanUrat.MovesT.F0_preHalt

/-! # H8-A1 `CutFirst.lean` — (CUT-1), the first-entrance calculus (Wave 1)

`firstEntAbove_unique` / `firstEntAbove_exists` / `firstEntAbove_shallowRead` /
`firstEntAbove_mem_chains`.  Statements VERBATIM from
`lean/blueprints/HDISCHARGE_H8.md` §4 Wave 1; proof stock §3.1 (prefix totality
via `List.prefix_or_prefix_of_prefix`, antisymmetry via lengths + `history_ext`
exactly as `vtree_pathOrder`'s antisymm leg; existence by classical choice on
the minimal-length entrance prefix — no decidability of `E` assumed).
Kills G-2 falsifier #3 at level (1a).  Deps: H8-D0. -/

set_option linter.style.longLine false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace LeanUrat.Scaffold.HDischarge.H8

open LeanUrat.MovesC LeanUrat.MovesD LeanUrat.MovesT

variable {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]

/-- Helper (prover's discretion, no content): a proper prefix is strictly
shorter — prefix `length_le` sharpened by `history_ext` antisymmetry. -/
lemma ProperPrefix.length_lt {H' H : History p F} (h : ProperPrefix H' H) :
    H'.nodes.length < H.nodes.length :=
  lt_of_le_of_ne h.1.length_le
    (fun heq => h.2 (history_ext (h.1.eq_of_length heq)))

/-- (CUT-1) uniqueness: two first entrances above the same `H` mutually
prefix each other (each one's clause 3 applied to the other), hence agree. -/
theorem firstEntAbove_unique (E : History p F → Prop) {ε₁ ε₂ H : History p F}
    (h1 : FirstEntAbove E ε₁ H) (h2 : FirstEntAbove E ε₂ H) : ε₁ = ε₂ := by
  have h12 : ε₁.IsPrefixOf ε₂ := h1.2.2 ε₂ h2.1 h2.2.1
  have h21 : ε₂.IsPrefixOf ε₁ := h2.2.2 ε₁ h1.1 h1.2.1
  exact history_ext (h12.eq_of_length (h12.length_le.antisymm h21.length_le))

/-- (CUT-1) existence: a non-shallow read has a first entrance above it —
take the minimal-`nodes.length` entrance proper prefix (classical, via
`Nat.sInf` on the length set; no decidability of `E`); prefix totality
(`List.prefix_or_prefix_of_prefix`, both being prefixes of the LIST
`H.nodes`) + length minimality force it below every other entrance. -/
theorem firstEntAbove_exists (E : History p F → Prop) {H : History p F}
    (h : ¬ ShallowRead E H) : ∃ ε, FirstEntAbove E ε H := by
  classical
  have hex : ∃ H', ProperPrefix H' H ∧ E H' := by
    by_contra hno
    push Not at hno
    exact h hno
  obtain ⟨H₁, hpp₁, hE₁⟩ := hex
  set S : Set ℕ :=
    {n | ∃ H' : History p F, (E H' ∧ ProperPrefix H' H) ∧ H'.nodes.length = n}
    with hSdef
  have hSne : S.Nonempty := ⟨H₁.nodes.length, H₁, ⟨hE₁, hpp₁⟩, rfl⟩
  obtain ⟨H₀, ⟨hE₀, hpp₀⟩, hlen₀⟩ := Nat.sInf_mem hSne
  refine ⟨H₀, hE₀, hpp₀, ?_⟩
  intro H' hE' hpp'
  rcases List.prefix_or_prefix_of_prefix hpp₀.1 hpp'.1 with hc | hc
  · exact hc
  · -- `H' ≼ H₀`: minimality of `H₀`'s length forces equality
    have hmem : H'.nodes.length ∈ S := ⟨H', ⟨hE', hpp'⟩, rfl⟩
    have hge : sInf S ≤ H'.nodes.length := Nat.sInf_le hmem
    have hle : H'.nodes.length ≤ H₀.nodes.length := hc.length_le
    have heq : H' = H₀ := history_ext (hc.eq_of_length (by omega))
    subst heq
    exact List.prefix_refl _

/-- (CUT-1) minimality (first entrances are shallow reads): an entrance
proper prefix `H''` of `ε` would be an entrance proper prefix of `H`
strictly shorter than `ε`, yet clause 3 puts `ε` below it — length
contradiction. -/
theorem firstEntAbove_shallowRead (E : History p F → Prop) {ε H : History p F}
    (h : FirstEntAbove E ε H) : E ε ∧ ShallowRead E ε := by
  obtain ⟨hEε, hppε, hmin⟩ := h
  refine ⟨hEε, ?_⟩
  intro H'' hpp'' hE''
  have hlt1 : H''.nodes.length < ε.nodes.length := hpp''.length_lt
  have hlt2 : ε.nodes.length < H.nodes.length := hppε.length_lt
  have hppH : ProperPrefix H'' H := by
    refine ⟨hpp''.1.trans hppε.1, ?_⟩
    intro hEq
    rw [hEq] at hlt1
    omega
  have hle : ε.nodes.length ≤ H''.nodes.length :=
    (hmin H'' hE'' hppH).length_le
  omega

/-- (CUT-1) closure: the first entrance above a chain is itself a chain —
`hclosed` at `H` with `ε ≼ H` and `ε.nodes ≠ []` (= `ε.nonempty`). -/
theorem firstEntAbove_mem_chains (Tr : VTree p F) (E : History p F → Prop)
    {ε H : History p F} (hH : H ∈ Tr.chains) (h : FirstEntAbove E ε H) :
    ε ∈ Tr.chains :=
  Tr.hclosed H hH ε h.2.1.1 ε.nonempty

end LeanUrat.Scaffold.HDischarge.H8
