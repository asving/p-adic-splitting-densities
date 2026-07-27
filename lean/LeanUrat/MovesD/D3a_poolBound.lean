/-
Unit D3a.D4R2'  (MovesD campaign, E-phase)
[REV 8, Codex#6 c.3 — stated on `Shape.CD` (the F3/CD bridge): at P̂ = ∅ this IS the
note's C_∅ = 1 ≤ Mfac(∅)·p^{W(∅)} = 1·p⁰ = 1 (empty product/sum); at nonempty shapes
CD = Nat.card PrefIdx (CD_eq) — the former statement exactly.]
moves_ref: "C_P̂(p) ≤ M(P̂)·p^{W(P̂)}" (D4R.2′ display; the M ≤ n^{|P̂|} clause is W2).
deps: E9, D1c, D2a (CD_eq), F3.
sketch: case split on `reads = []`: ∅ — CD = 1, Mfac·p^W = 1; nonempty — CD_eq +
`Nat.card_le_card_of_injective encIdx encIdx_inj` + D1c.  difficulty: easy.
hypothesis_fields: `hnorm : PresentNorm n pol P` (the open dictionary pin, HC-2 — REV 7,
Codex#5 g.4); the INJECTION itself is proved, nothing else assumed.
-/
import Mathlib
import LeanUrat.MovesD.Defs
import LeanUrat.MovesD.D2a_finite
import LeanUrat.MovesD.D1c_encCard
import LeanUrat.MovesD.E9_encInj

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesD
open LeanUrat.Moves LeanUrat.MovesC

variable {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F] {n : ℕ}
  {pol : CanonPolicy p F} {P : Shape n}

/-- D4R.2′: C_P̂(p) ≤ M(P̂)·p^{W(P̂)}, on the CD form (∅ dispatch included). -/
theorem D4R2' (hnorm : PresentNorm n pol P) :
    P.CD pol ≤ (P : ShapePrefix).Mfac * p ^ (P : ShapePrefix).W := by
  by_cases hP : (P : ShapePrefix).reads = []
  · -- ∅ dispatch: CD = 1, and Mfac·p^W = 1·p⁰ = 1 (empty product/sum)
    rw [Shape.CD, if_pos hP]
    simp only [ShapePrefix.Mfac, ShapePrefix.W, hP, List.map_nil, List.prod_nil,
      List.sum_nil, pow_zero, mul_one, le_refl]
  · -- nonempty: CD = #PrefIdx (CD_eq), inject into EncTargetP (encIdx_inj), bound by D1c
    haveI : Finite (EncTargetP p F (P : ShapePrefix)) := by
      unfold EncTargetP; infer_instance
    rw [CD_eq hnorm hP]
    calc Nat.card (PrefIdx n pol P)
        ≤ Nat.card (EncTargetP p F (P : ShapePrefix)) :=
          Nat.card_le_card_of_injective _ encIdx_inj
      _ ≤ (P : ShapePrefix).Mfac * p ^ (P : ShapePrefix).W :=
          encTargetP_card (Nat.Prime.two_le Fact.out)

end LeanUrat.MovesD
