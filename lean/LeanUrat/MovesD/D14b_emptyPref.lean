/-
Unit D14b.D4R4_emptyPref  (MovesD campaign, E-phase)
moves_ref: "If Pref(P̂) = ∅ then S(P̂,⊤) = … = ∅ and C_P̂(p) = 0, so for EVERY N ≥ 1:
#{f mod p^N ∈ ∅} = 0 = C_P̂(p)·p^{nN − A(P̂)}" (L12).
deps: Defs, D2a.
sketch: empty iUnion over an empty index; CD_eq + Nat.card of an empty type.
difficulty: easy.
hypothesis_fields: `hN`, `hm` explicit (L12's N(P̂) := 1 convention).
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

/-- L12's empty-Pref clause: empty event, C = 0, and the 0 = 0 law at every N ≥ 1. -/
theorem D4R4_emptyPref (hne : (P : ShapePrefix).reads ≠ [])
    (hemp : IsEmpty (PrefIdx n pol P)) (hN : 1 ≤ N) (hm : m = n * N)
    (S : Presented p F n N m pol P) :
    S.event = ∅ ∧ P.CD pol = 0 ∧
      Nat.card ↥S.event * p ^ ((P : ShapePrefix).A' n) = P.CD pol * p ^ (n * N) := by
  haveI := hemp
  have hev : S.event = ∅ := Set.iUnion_of_empty _
  have hCD : P.CD pol = 0 := by
    unfold Shape.CD
    rw [if_neg hne]
    exact Nat.card_of_isEmpty
  have hcard : Nat.card ↥S.event = 0 := by
    rw [hev]
    haveI : IsEmpty ↥(∅ : Set (Box p m)) := Set.isEmpty_coe_sort.mpr rfl
    exact Nat.card_of_isEmpty
  refine ⟨hev, hCD, ?_⟩
  rw [hcard, hCD, zero_mul, zero_mul]

end LeanUrat.MovesD
