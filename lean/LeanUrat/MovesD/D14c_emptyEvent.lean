/-
Unit D14c.emptyEvent  (MovesD campaign, ratification repair D4, 2026-07-28)
[Finding D4 ACCEPTED: L5 (note ~4796) INCLUDES the empty prefix η = ∅ with S(∅,⊤) = the
FULL BOX (the base of L6), Pref(∅) = {∅}, mult_∅ ≡ 1 — but the Lean `Presented.event`/
`Presented.mult` are PrefIdx-indexed and the History type has no empty chain (F3's
displayed deviation), so at reads = [] they returned ∅/0. `PrefOpt`/`etaDataO`/
`emptyFiber` existed but were unwired. Repair: the ∅-COMPLETE objects `Presented.eventO`/
`Presented.multO` (Defs, dispatching on reads = [] exactly as `Shape.CD` does) + this
unit's laws wiring them to the note's displays. Existing theorems (D2a/D3b/D12/D13/D14b
with their hne guards) are UNTOUCHED.]
moves_ref: L5 (note ~4794–4800): "Fix a realized prefix η — INCLUDING the EMPTY prefix
η = ∅ (k = −1), whose state cylinder is the FULL BOX: … S(∅,⊤) = the box (§C C.0's EMPTY
HISTORY clause T(∅, Z) := Z, at Z = ⊤: no constraint, vol 1) — this empty case is the
base of L6's induction"; L12/D4R.1: Pref(∅) = {∅}, C_∅ = 1, A(∅) = 0, mult_∅ ≡ 1.
deps: Defs, D14a (A'_nil, Pref_empty_shape, emptyShape_law's card computation).
sketch: if_pos/if_neg; card univ = p^{nN}; A' ∅ = 0 is D14a's A'_nil (VERIFIED, cited —
not forced).  difficulty: easy.
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

/-- **The ∅-shape event and multiplicity are the note's** (L5, note ~4796): at η = ∅ the
event is the FULL BOX and the multiplicity is ≡ 1 (Pref(∅) = {∅}: the one class is the
empty chain, present in every T_can(f) by L2's `root_mem` law). -/
theorem eventO_empty_shape (S : Presented p F n N m pol P)
    (hP : (P : ShapePrefix).reads = []) :
    S.eventO = Set.univ ∧ ∀ x : Box p m, S.multO x = 1 := by
  constructor
  · rw [Presented.eventO, if_pos hP]
  · intro x
    rw [Presented.multO, if_pos hP]

/-- On every NONEMPTY shape `eventO` IS `event` (the dispatch changes nothing where the
old object was already the note's). -/
theorem eventO_eq_event (S : Presented p F n N m pol P)
    (hne : (P : ShapePrefix).reads ≠ []) :
    S.eventO = S.event := by
  rw [Presented.eventO, if_neg hne]

/-- On every NONEMPTY shape `multO` IS `mult`. -/
theorem multO_eq_mult (S : Presented p F n N m pol P)
    (hne : (P : ShapePrefix).reads ≠ []) (x : Box p m) :
    S.multO x = S.mult x := by
  rw [Presented.multO, if_neg hne]

/-- **The ∅ mass law in the D4R.1 normal form, on the ∅-complete event**:
#S(∅,⊤)·p^{A(∅)} = C_∅·p^{nN} — card univ = p^{nN} (the full box), A(∅) = 0 (D14a's
`A'_nil`, VERIFIED — the per-read sum over an empty read list), C_∅ = 1 (CD's own
dispatch, D14a's `Pref_empty_shape`). -/
theorem eventO_empty_law (S : Presented p F n N m pol P)
    (hm : m = n * N) (hN : 1 ≤ N) (hP : (P : ShapePrefix).reads = []) :
    Nat.card ↥S.eventO * p ^ ((P : ShapePrefix).A' n) = P.CD pol * p ^ (n * N) := by
  have hev : S.eventO = emptyFiber p m := (eventO_empty_shape S hP).1
  rw [hev]
  exact emptyShape_law hm hN hP

end LeanUrat.MovesD
