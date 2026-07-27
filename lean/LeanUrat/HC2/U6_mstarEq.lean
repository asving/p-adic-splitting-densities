/-
Unit U6.mkFresh_mstar  (HC-2 campaign, E-phase — blueprint §5 Layer A)
moves_ref: MovesC `mstar_eq` docstring ("the presented fresh codimension sum equals the
FRESH-BAND count computed from node data").
deps: U2–U5.  difficulty: medium.  hypothesis_fields: none.
sketch: mstar = Σ codim = |non-value band| + |value band| (supports PARTITION the band by
U2/U3/U4); finish by `Finset.card_biUnion`.
-/
import Mathlib
import LeanUrat.HC2.Defs

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesJ
open Polynomial LeanUrat.Moves LeanUrat.MovesC LeanUrat.MovesD

/-- `m*` of the constructed fresh data IS the fresh-band count (verbatim
`JetSetup.mstar_eq`'s field type at `mkFresh`). -/
theorem mkFresh_mstar {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
    (H : History p F) (n N : ℕ) {keys : ℕ → Polynomial ℤ_[p]}
    (S : PresentSeed p F H n N keys) (vOf : VOf p (n * N))
    (i : ℕ) (hi : i < H.nodes.length) :
    (mkFresh H n N S vOf i hi).mstar
      = Nat.card {c : Fin (n * N) //
          inFreshBand H n (boxChart n N) i (H.nodes[i]'hi) c} := by
  sorry

end LeanUrat.MovesJ
