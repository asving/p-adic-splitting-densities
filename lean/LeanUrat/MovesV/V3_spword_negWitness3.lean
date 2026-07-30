/-
Unit V3-3b-NEG — the COMPILED NEGATION WITNESS for `template_total` as stated
(final-ratification V repairs, 2026-07-29; the `U1_negWitness` durability
pattern; the NEW FENCE RULE's mandated construction).

WHAT IS REFUTED.  V3-3b stated (sorried, rev 2)
  `template_total {n} (ε : EntShapeV n) : (ε.template?).isSome`.
The verdict (M1): "the corpus still asserts with `sorry` … the surrounding
source itself records that `SpWordNeg.P3` is a valid `ShapeWF` prefix that
extends to an `EntShapeV`, while `spWordFits_impossible … : ¬ SpWordFits 3 P3
ws`.  For the resulting entrance shape, `spWord 3 P3 = []`, hence
`collapseRuns [] = []`; the first test inside `template?` is `w ≠ []`, so
`template? = none`.  Thus the theorem is semantically false."

* `TTNeg.eps3` — the P3 entrance shape (gsel = musel = 1, selRec = []).
* `TTNeg.eps3_template?_none` — its `template?` IS `none`.
* `TTNeg.template_total_false` — the ∀-sentence of the deleted
  `template_total` is FALSE (at the build target n = 3).

The repair is DELETE-AND-SCOPE (V3_spwordB): the scoped-true form is
`template_total_of_perimeter` under the named `SpWordPerimeter` predicate.

deps: MovesV Defs (`EntShapeV`, `template?`, `spWord`), the P3 witness family
(V3_spwordA_negWitness).  axioms: Lean core only.
-/
import LeanUrat.MovesV.V3_spwordA_negWitness

set_option linter.style.longLine false
set_option linter.style.header false

namespace LeanUrat.MovesV
namespace TTNeg

open SpWordNeg

/-- THE WITNESS ENTRANCE SHAPE over `SpWordNeg.P3`: the last read `R1` has
(g, μ) = (1, 1), no read is a branch slot (m̄ = 1 both), so gsel = musel = 1
and selRec = [] extend P3 to an `EntShapeV 3`. -/
def eps3 : EntShapeV 3 where
  Phat := ⟨P3, hWF3⟩
  hne := List.cons_ne_nil _ _
  gsel := 1
  musel := 1
  hsel_g := le_refl 1
  hsel_μ := le_refl 1
  hentry := by
    intro R hR
    have h2 : ([R0, R1] : List MovesD.ShapeRead).getLast? = some R := hR
    rw [List.getLast?_cons_cons, List.getLast?_singleton] at h2
    cases Option.some.inj h2
    exact ⟨rfl, rfl⟩
  helig := by
    intro R hR
    have h2 : ([R0, R1] : List MovesD.ShapeRead).getLast? = some R := hR
    rw [List.getLast?_cons_cons, List.getLast?_singleton] at h2
    cases Option.some.inj h2
    exact ⟨le_refl 1, le_refl 1, by decide⟩
  selRec := []
  hlen := by decide
  hmenu := by intro i hi; exact absurd hi (Nat.not_lt_zero i)

/-- eps3's spWord is the junk [] (no fitting word exists — the recorded
`spWordFits_impossible`). -/
theorem eps3_spWord_nil :
    spWord 3 (eps3.Phat : MovesD.ShapePrefix) = [] := by
  change spWord 3 P3 = []
  unfold spWord
  rw [dif_neg spWordFits_impossible]

/-- THE COUNTERMODEL VALUE: `template?` is `none` at eps3 (collapseRuns [] =
[] fails the first `w ≠ []` test of the `template?` dite). -/
theorem eps3_template?_none : eps3.template? = none := by
  simp only [EntShapeV.template?]
  exact dif_neg (fun hcond => hcond.1 (by rw [eps3_spWord_nil, MovesSp.collapseRuns]))

/-- THE REFUTATION: the deleted `template_total` ∀-sentence is FALSE. -/
theorem template_total_false :
    ¬ ∀ (n : ℕ) (ε : EntShapeV n), (ε.template?).isSome := by
  intro h
  have h3 := h 3 eps3
  rw [eps3_template?_none] at h3
  simp at h3

end TTNeg
end LeanUrat.MovesV
