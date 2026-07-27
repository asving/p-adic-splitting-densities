/-
Unit F1.enum  (MovesD campaign, E-phase)
moves_ref: "Pref(P̂) := { η : shape(η) = P̂, η realizable, canonical lifts }, C_P̂(p) :=
#Pref(P̂)" — the enumeration is CONSTRUCTED, completeness/injectivity are definitional
theorems (final-audit finding 3: nothing assumed).  [REV 5, reconciliation (2)]:
"classes ↔ η's" is the TYPED Prop `PresentNorm` (carried by `Presented.hnorm`).
Gate-checked at §0.6 — C_P̂*(2) = 3, C_P̂*(3) = 48, mult ≡ 1.
deps: Defs.
sketch: `Exists.choose_spec` twice; `Nat.card` of a subtype of a set coerced.
difficulty: easy.
hypothesis_fields: `hnorm : PresentNorm n pol P` on `card_classes` (REV 7, Codex#5 g.4);
`reprOf_mem`/`etaData_reprOf` are hypothesis-free.
-/
import Mathlib
import LeanUrat.MovesD.Defs

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesD
open LeanUrat.Moves LeanUrat.MovesC

variable {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F] {n : ℕ}
  {pol : CanonPolicy p F} {P : Shape n}

/-- The classical representative is a member of the literal Pref set. -/
theorem reprOf_mem (i : PrefIdx n pol P) : reprOf i ∈ PrefSet n pol P :=
  i.2.choose_spec.1

/-- The representative's class is the index itself. -/
theorem etaData_reprOf (i : PrefIdx n pol P) :
    etaData (P : ShapePrefix) (reprOf i) = i.1 :=
  i.2.choose_spec.2

/-- The enumeration count IS the image-class count. -/
theorem card_classes (hnorm : PresentNorm n pol P) :
    Nat.card (PrefIdx n pol P)
      = Nat.card ↥(etaData (P : ShapePrefix) '' PrefSet n pol P) :=
  rfl

end LeanUrat.MovesD
