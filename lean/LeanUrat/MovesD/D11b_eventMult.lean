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

/-- Event membership is positive multiplicity. -/
theorem event_iff_mult (S : Presented p F n N m pol P) (x : Box p m) :
    x ∈ S.event ↔ 1 ≤ S.mult x := by
  -- `PrefIdx` is a subtype of the finite Pi type `EtaData F P` (D2a's L8-structural fact,
  -- reproduced locally since D11b's only declared dep is `Defs`).
  haveI hfin : Finite (EtaData F P) := by unfold EtaData; infer_instance
  constructor
  · -- membership → a witness class → nonempty index subtype → positive card
    intro hx
    simp only [Presented.event, Set.mem_iUnion] at hx
    obtain ⟨i, hi⟩ := hx
    haveI : Nonempty {i : PrefIdx n pol P // x ∈ S.fiber i} := ⟨⟨i, hi⟩⟩
    simp only [Presented.mult]
    exact Nat.card_pos
  · -- positive card → nonempty index subtype → a witness class → membership
    intro hx
    simp only [Presented.mult] at hx
    obtain ⟨⟨i, hi⟩⟩ := (Nat.card_pos_iff.mp hx).1
    simp only [Presented.event, Set.mem_iUnion]
    exact ⟨i, hi⟩

end LeanUrat.MovesD
