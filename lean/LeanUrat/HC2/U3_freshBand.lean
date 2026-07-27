/-
Unit U3.mkFresh_band  (HC-2 campaign, E-phase — blueprint §5 Layer A)
moves_ref: MovesC `JetSetup.fresh_band` docstring (supports ⊆ the D.11 band, ROUND-6 fine
boundary).
deps: D6.  difficulty: medium.  hypothesis_fields: none.
sketch: strip supports are chosen from the band; value level-set members have height =
slotVal (the band's upper edge) — the in-band condition is D6's own roster selection
(value clauses only at pre-crossing slots), the `< prevRim` from D6's slot range.
-/
import Mathlib
import LeanUrat.HC2.Defs

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesJ
open Polynomial LeanUrat.Moves LeanUrat.MovesC LeanUrat.MovesD

/-- Extract `support = S` from a `C1_TYP_toClause`-shaped existential, matching the whole
existential as a single metavariable (so the private `hcard` proof buried in `valueClause`
never has to be named). -/
private lemma choose_support_eq {p m : ℕ} {S : Finset (Fin m)} {P : LevelClause p m → Prop}
    (h : ∃ cl : LevelClause p m, cl.support = S ∧ P cl) : h.choose.support = S :=
  h.choose_spec.1

/-- Every constructed fresh clause support lies INSIDE the band (verbatim
`JetSetup.fresh_band`'s field type at `mkFresh`). -/
theorem mkFresh_band {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
    (H : History p F) (n N : ℕ) {keys : ℕ → Polynomial ℤ_[p]}
    (S : PresentSeed p F H n N keys) (vOf : VOf p (n * N))
    (i : ℕ) (hi : i < H.nodes.length) :
    ∀ cl ∈ (mkFresh H n N S vOf i hi).clauses, ∀ c ∈ cl.support,
      inFreshBand H n (boxChart n N) i (H.nodes[i]'hi) c := by
  classical
  intro cl hcl c hc
  have hcl' : cl ∈ mkFreshClauses H n N S vOf i hi := hcl
  unfold mkFreshClauses at hcl'
  rw [List.mem_append] at hcl'
  rcases hcl' with hstrip | hval
  · -- STRIP clause: support = {c₀}, and c₀ ∈ stripSet ⇒ in-band by the roster's selection.
    simp only [List.mem_map, Finset.mem_toList] at hstrip
    obtain ⟨c₀, hc₀mem, hc₀eq⟩ := hstrip
    have hspec := (C1_stripClause (p := p) c₀).choose_spec
    rw [← hc₀eq, hspec.1, Finset.mem_singleton] at hc
    subst hc
    unfold stripSet at hc₀mem
    rw [Finset.mem_filter] at hc₀mem
    exact hc₀mem.2.1
  · -- VALUE clause: support = levelSet, and every level-set member is in-band (valueSlots).
    simp only [List.mem_map, Finset.mem_toList, Finset.mem_attach, true_and] at hval
    obtain ⟨jh, hjheq⟩ := hval
    have hsupp : (valueClause H n N S vOf i hi jh.1 (valueSlots_spanSlot jh.2)).support
        = levelSet H n N i (H.nodes[i]'hi) jh.1 := by
      unfold valueClause
      exact choose_support_eq _
    rw [← hjheq, hsupp] at hc
    have hj := jh.2
    unfold valueSlots at hj
    rw [Finset.mem_filter] at hj
    exact hj.2.2.2 c hc

end LeanUrat.MovesJ
