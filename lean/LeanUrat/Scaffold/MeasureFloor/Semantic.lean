/-
BP_I §1.5 — The semantic layer (MeasureFloor): MEAS-BRIDGE at the strict
convention.
Unit I-E1 (DEPENDENCY TRANSCRIPTION, defs only — landed here because the
Semantic.lean file did not yet exist; the I-E1 lemmas `mPoly_monic`,
`mPoly_natDegree` belong to the I-E1 unit and are NOT claimed here):
`mPoly` + `Sep`, verbatim per BP_I §1.5.
Unit I-E2a: `structure TypeData` — the named TYPE-OF and TYPE-OF-ISTYPE
interface rows, verbatim per BP_I §1.5. STATEMENT-ONLY: no canonical
constructor is claimed in this movement (the Movement-III dictionary seam).
-/
import Mathlib
import LeanUrat.Scaffold.MeasureFloor.Space
import LeanUrat.Scaffold.MeasureFloor.Types
import LeanUrat.MovesX.Defs

namespace LeanUrat.Scaffold

variable (p : ℕ) [Fact p.Prime] (n : ℕ)

/-! ## I-E1 (dependency transcription): `mPoly` and `Sep` -/

/-- The monic polynomial of a coefficient tuple (REUSE: `MovesX.polyOfCoeffs`). -/
noncomputable def mPoly (a : Coeff p n) : Polynomial ℚ_[p] :=
  (MovesX.polyOfCoeffs ℤ_[p] n a).map (algebraMap ℤ_[p] ℚ_[p])

/-- Separability over the FIELD ℚ_p (mathlib `Polynomial.Separable` =
IsCoprime f f′; brief Lemma SEP(ii)'s working form). -/
def Sep (a : Coeff p n) : Prop := (mPoly p n a).Separable

/-! ## I-E2a: the `TypeData` interface rows (TYPE-OF, TYPE-OF-ISTYPE) -/

/-- **THE INTERFACE ROW CARRIERS** — the semantic inputs of Dfloor, as NAMED
STRUCTURE FIELDS (never axioms). `TypeData` contains only TYPE-OF and
TYPE-OF-ISTYPE; LOC and NS-NULL are independent structures. Provenance:
* `typeOf`/`typeOf_isType` — brief Thm TYPE (UFD + I-2 e·f = deg; the K-11/M16
  audited bridge). Lean discharge = the Movement-III dictionary seam (the
  concrete OM/QpType-side construction + `SerreLocalFields.AX_integralClosure_dvr`
  footprint); junk value off the separable locus.
* `locality` **(LOC)** — brief import I-1 (M05 Lemma D, V2-upheld, wild-valid):
  the type is constant on a small enough cylinder around every separable point.
  Stated at bare ∃N (the 2v+1 modulus is the RATE refinement, parked).
* **(NS-NULL)** — brief Appendix A / I-3 null clause. Wave H constructs this
  row for every `n`; the stable consumer interface is not deleted or migrated. -/
structure TypeData (p n : ℕ) [Fact p.Prime] where
  typeOf : Coeff p n → FactorizationType
  typeOf_isType : ∀ a, Sep p n a → IsType n (typeOf a)

end LeanUrat.Scaffold
