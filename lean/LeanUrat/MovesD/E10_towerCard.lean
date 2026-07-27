/-
Unit E10.fieldTower_card  (MovesD campaign, E-phase)  [AUX; REV 9, Fable#7 G-2]
informal: adjoining a root of a degree-g irreducible to a finite subfield raises the
cardinality to the g-th power — the residue-tower card law behind wchain.
deps: Mathlib (minpoly/adjoin degree; `IntermediateField`-to-`Subfield` bridging).
sketch: ψ is (up to the monic normalization) the minpoly of z over K (hirr + hz);
[K(z) : K] = g; card K(z) = (card K)^g; identify K(z) with the subfield closure.
difficulty: medium-hard (the hardest new core step — Fable#7: "E3-grade field theory").
hypothesis_fields: none.
-/
import Mathlib
import LeanUrat.MovesD.Defs

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesD
open LeanUrat.Moves LeanUrat.MovesC

variable {F : Type*} [Field F] [Finite F]

/-- The residue-tower cardinality law: card K(z) = (card K)^g for z a root of a monic
irreducible degree-g ψ over the finite subfield K. -/
theorem fieldTower_card {K : Subfield F} [Finite ↥K] {ψ : Polynomial ↥K}
    (hirr : Irreducible ψ) (hmon : ψ.Monic) {g : ℕ} (hdeg : ψ.natDegree = g) {z : F}
    (hz : Polynomial.eval₂ K.subtype z ψ = 0) :
    Nat.card ↥(Subfield.closure ((K : Set F) ∪ {z})) = (Nat.card ↥K) ^ g := by
  sorry

end LeanUrat.MovesD
