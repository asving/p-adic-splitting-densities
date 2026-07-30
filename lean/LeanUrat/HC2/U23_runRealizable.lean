/-
Unit U23.readsOf_realizable  (HC-2 campaign, E-phase — blueprint §5 Layer D)
moves_ref: MovesC `Realizable` ("the FULL three-condition class").
deps: U20–U22, assembly over the per-step dichotomy (`s0+w < μ` | `= μ`; the `> μ` case
excluded by coherence's window containment).  difficulty: easy given U20–U22.
hypothesis_fields: none.
-/
import Mathlib
import LeanUrat.HC2.Defs
import LeanUrat.HC2.U20_NA
import LeanUrat.HC2.U21_HV
import LeanUrat.HC2.U22_SAE

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesJ
open Polynomial LeanUrat.Moves LeanUrat.MovesC LeanUrat.MovesD

/-- A classifier run is realizable — (NA)+(HV)+(SAE) at every appended read. -/
theorem readsOf_realizable {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
    {n : ℕ} {f : Polynomial ℤ_[p]} {H : History p F}
    (h : ReadsOf p F n f H) : Realizable H := by
  -- `Realizable H` = at every appended read `ν_{i+1}`, `TransitionAdmissible ν_i ν_{i+1}`;
  -- `TransitionAdmissible` is the (NA)∧(HV)∧(SAE₁)∧(SAE₂) four-tuple.  Assemble it from
  -- U20 (NA), U21 (HV), U22 (SAE, both conjuncts) over the standing pair (blueprint §5 D).
  intro i hi
  exact ⟨readsOf_NA h i hi, readsOf_HV h i hi,
    (readsOf_SAE h i hi).1, (readsOf_SAE h i hi).2⟩

end LeanUrat.MovesJ
