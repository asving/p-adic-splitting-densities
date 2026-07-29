/-
Unit D14c.emptyEvent  (MovesD campaign, ratification repair D4″, 2026-07-29)
[Finding D4 ACCEPTED; round-1 repair FLAGGED by the Codex confirm ("a correct alternative
API does not wire the empty case into the note-designated objects and introduces two
competing event/multiplicity semantics"). D4″: the reads = [] dispatch is now wired INTO
`Presented.event`/`Presented.mult` themselves (Defs.lean, mirroring `Shape.CD`), the
parallel `eventO`/`multO` are DELETED, and this unit states the note's ∅ laws directly on
the designated objects. The unfolding lemmas `event_of_ne`/`mult_of_ne`/
`event_empty_shape`/`mult_empty_shape` live with the definitions (Defs.lean); here sit
the L5 mass law and the combined ∅-shape display.]
moves_ref: L5 (note ~4794–4800): "Fix a realized prefix η — INCLUDING the EMPTY prefix
η = ∅ (k = −1), whose state cylinder is the FULL BOX: … S(∅,⊤) = the box (§C C.0's EMPTY
HISTORY clause T(∅, Z) := Z, at Z = ⊤: no constraint, vol 1) — this empty case is the
base of L6's induction"; L12/D4R.1: Pref(∅) = {∅}, C_∅ = 1, A(∅) = 0, mult_∅ ≡ 1; F3's
deviation record (the History type has no empty chain — WHY the dispatch is definitional).
deps: Defs, D14a (A'_nil, Pref_empty_shape, emptyShape_law's card computation).
sketch: Defs' empty-shape laws + emptyShape_law; A' ∅ = 0 is D14a's A'_nil (VERIFIED,
cited — not forced).  difficulty: easy.
hypothesis_fields: `hm`, `hN` explicit, mirroring D14a (L12's empty-case N(P̂) := 1
convention; the box shape — no jet needed for the count).
-/
import Mathlib
import LeanUrat.MovesD.Defs
import LeanUrat.MovesD.D14a_emptyShape

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesD
open LeanUrat.Moves LeanUrat.MovesC

variable {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F] {n N m : ℕ}
  {pol : CanonPolicy p F} {P : Shape n}

/-- **The ∅-shape event and multiplicity are the note's, ON the designated objects**
(L5, note ~4796): at η = ∅ the event is the FULL BOX and the multiplicity is ≡ 1
(Pref(∅) = {∅}: the one class is the empty chain, present in every T_can(f) by L2's
`root_mem` law). The combined display of Defs' `event_empty_shape`/`mult_empty_shape`. -/
theorem event_mult_empty_shape (S : Presented p F n N m pol P)
    (hP : (P : ShapePrefix).reads = []) :
    S.event = Set.univ ∧ ∀ x : Box p m, S.mult x = 1 :=
  ⟨S.event_empty_shape hP, S.mult_empty_shape hP⟩

/-- **The ∅ mass law in the D4R.1 normal form, on the designated event**:
#S(∅,⊤)·p^{A(∅)} = C_∅·p^{nN} — card univ = p^{nN} (the full box), A(∅) = 0 (D14a's
`A'_nil`, VERIFIED — the per-read sum over an empty read list), C_∅ = 1 (CD's own
dispatch, D14a's `Pref_empty_shape`). -/
theorem event_empty_law (S : Presented p F n N m pol P)
    (hm : m = n * N) (hN : 1 ≤ N) (hP : (P : ShapePrefix).reads = []) :
    Nat.card ↥S.event * p ^ ((P : ShapePrefix).A' n) = P.CD pol * p ^ (n * N) := by
  have hev : S.event = emptyFiber p m := S.event_empty_shape hP
  rw [hev]
  exact emptyShape_law hm hN hP

end LeanUrat.MovesD
