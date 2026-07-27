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
  letI : Algebra ↥K F := K.subtype.toAlgebra
  -- z is integral over K, witnessed by ψ (algebraMap ↥K F = K.subtype by rfl)
  have hint : IsIntegral ↥K z := ⟨ψ, hmon, hz⟩
  have haeval : Polynomial.aeval z ψ = 0 := hz
  -- minpoly of z over K is ψ (irreducible + monic + root)
  have hminpoly : minpoly ↥K z = ψ :=
    (minpoly.eq_of_irreducible_of_monic hirr haeval hmon).symm
  -- K⟮z⟯ has finrank g over K
  have hfinrank : Module.finrank ↥K ↥(IntermediateField.adjoin ↥K {z}) = g := by
    rw [IntermediateField.adjoin.finrank hint, hminpoly, hdeg]
  -- cardinality of a finite K-vector space
  haveI : Fintype ↥K := Fintype.ofFinite _
  haveI : Fintype ↥(IntermediateField.adjoin ↥K {z}) := Fintype.ofFinite _
  have hcard : Fintype.card ↥(IntermediateField.adjoin ↥K {z})
      = Fintype.card ↥K ^ g := by
    rw [Module.card_eq_pow_finrank (K := ↥K), hfinrank]
  -- bridge: the subfield closure equals (the carrier of) K⟮z⟯
  have hrange : Set.range (algebraMap ↥K F) = (K : Set F) := by
    rw [show (algebraMap ↥K F) = K.subtype from rfl, Subfield.coe_subtype]
    exact Subtype.range_coe
  have hmem : ∀ x, x ∈ Subfield.closure ((K : Set F) ∪ {z})
      ↔ x ∈ IntermediateField.adjoin ↥K {z} := by
    intro x
    rw [← IntermediateField.mem_toSubfield, IntermediateField.adjoin_toSubfield, hrange]
  have hequiv : ↥(Subfield.closure ((K : Set F) ∪ {z}))
      ≃ ↥(IntermediateField.adjoin ↥K {z}) := Equiv.subtypeEquivRight hmem
  rw [Nat.card_congr hequiv, Nat.card_eq_fintype_card, hcard, Nat.card_eq_fintype_card]

end LeanUrat.MovesD
