/-
Unit D11b.event_iff_mult  (MovesD campaign, E-phase)
moves_ref: "S(P̂,⊤) = {f : mult_P̂(f) ≥ 1}" (L6 corollary).
deps: Defs.
sketch: iUnion membership ↔ nonempty index subtype ↔ positive card.
difficulty: easy.  hypothesis_fields: none.
-/
import Mathlib
import LeanUrat.MovesD.Defs

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesD
open LeanUrat.Moves LeanUrat.MovesC

variable {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F] {n N m : ℕ}
  {pol : CanonPolicy p F} {P : Shape n}

/-- Event membership is positive multiplicity. [D4″ 2026-07-29: statement UNCHANGED — with
the ∅ dispatch wired into `event`/`mult` it now also covers reads = [] (univ ∋ x ↔ 1 ≤ 1);
the proof gains the case split.] -/
theorem event_iff_mult (S : Presented p F n N m pol P) (x : Box p m) :
    x ∈ S.event ↔ 1 ≤ S.mult x := by
  by_cases hP : (P : ShapePrefix).reads = []
  · -- ∅ shape: event = univ, mult ≡ 1 — both sides hold.
    simp [S.event_empty_shape hP, S.mult_empty_shape hP]
  -- `PrefIdx` is a subtype of the finite Pi type `EtaData F P` (D2a's L8-structural fact,
  -- reproduced locally since D11b's only declared dep is `Defs`).
  haveI hfin : Finite (EtaData F P) := by unfold EtaData; infer_instance
  constructor
  · -- membership → a witness class → nonempty index subtype → positive card
    intro hx
    rw [S.event_of_ne hP] at hx
    simp only [Set.mem_iUnion] at hx
    obtain ⟨i, hi⟩ := hx
    haveI : Nonempty {i : PrefIdx n pol P // x ∈ S.fiber i} := ⟨⟨i, hi⟩⟩
    rw [S.mult_of_ne hP]
    exact Nat.card_pos
  · -- positive card → nonempty index subtype → a witness class → membership
    intro hx
    rw [S.mult_of_ne hP] at hx
    obtain ⟨⟨i, hi⟩⟩ := (Nat.card_pos_iff.mp hx).1
    rw [S.event_of_ne hP]
    simp only [Set.mem_iUnion]
    exact ⟨i, hi⟩

end LeanUrat.MovesD
