/-
Unit U5.mkFresh_assembled  (HC-2 campaign, E-phase — blueprint §5 Layer A)
moves_ref: MovesC round-5 header "exact geometric fresh-clause identification";
`JetSetup.fresh_assembled` field type, verbatim at `mkFresh`.
deps: D6, C1.TYP_toClause (PROVED), IsValueSupport.  difficulty: medium (iff bookkeeping).
hypothesis_fields: the emitted values `vOf` (R4.B.2 boundary — free parameters here).
-/
import Mathlib
import LeanUrat.HC2.Defs

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesJ
open Polynomial LeanUrat.Moves LeanUrat.MovesC LeanUrat.MovesD

/-- The `fresh_assembled` disjunction for `mkFresh` — strips carry the ¬IsValueCoord tag
from their roster; value clauses carry `IsValueSupport`, `codim = card`, and the
TypObject/`v` witnesses of D6's own data. -/
theorem mkFresh_assembled {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
    (H : History p F) (n N : ℕ) {keys : ℕ → Polynomial ℤ_[p]}
    (S : PresentSeed p F H n N keys) (vOf : VOf p (n * N))
    (i : ℕ) (hi : i < H.nodes.length) :
    ∀ cl ∈ (mkFresh H n N S vOf i hi).clauses,
      (∃ c : Fin (n * N), cl.support = {c} ∧ cl.codim = 1 ∧
        (∀ x, (cl.sat x ↔ x c = 0)) ∧
        ¬ IsValueCoord H (boxChart n N) i (H.nodes[i]'hi) c) ∨
      (IsValueSupport H (boxChart n N) i (H.nodes[i]'hi) cl.support ∧
        cl.codim = cl.support.card ∧
        ∃ (T : TypObject p (n * N) cl.support (Fin cl.codim → ZMod p))
          (v : Fin cl.codim → ZMod p), ∀ x, (cl.sat x ↔ T.φ x = v)) := by
  sorry

end LeanUrat.MovesJ
