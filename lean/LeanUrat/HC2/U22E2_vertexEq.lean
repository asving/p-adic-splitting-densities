/-
Unit U22-E2.SAE_vertexEq_endpoint  (HC-2 campaign — blueprint §9 F-4 endpoint of U22;
NEW unit, census +1; statement landed in-file from the proven reduction and
PROVER-REFINABLE — the assembled `readsOf_SAE` in U22_SAE.lean is normative and
byte-unchanged)
moves_ref: §C rev 12 (SAE) display; the F-4 semantic spec — THE ADJACENT-VERTEX EQUALITY
ENDPOINT: "when the new window reaches the vertex, the new side height equals the
standing vertex height (`hLineU` + the vertex anchoring; the u*-tie)".
deps: D4 (`SideReads` at reads i and i+1), `Node.hLineU` (the side line passes through
`(j*, u*)`), `HistoryCoherent` (`Dwidth' = childWidth`, the γ-tie).
difficulty: hard.  hypothesis_fields: none.
CONSUMPTION NOTE: with `hLineU` at the child (`line.at ((s0'+wSide')·Dwidth') = ustar'`)
and coherence's width chain (`Dwidth' = childWidth`), this u*-tie IS the (SAE)
conjunct-4 equality `new-line.at(μ·childWidth) = old-line.at(μ·childWidth)` — the
adjacent case of the assembled unit.  `Node.line` and `Node.ustar` are absolute
v_p-scale, so NO stretch factor appears here (contrast U22-E1).
-/
import Mathlib
import LeanUrat.HC2.Defs

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesJ
open Polynomial LeanUrat.Moves LeanUrat.MovesC LeanUrat.MovesD

/-- (SAE) adjacent-vertex equality endpoint (F-4/U22-E2): at consecutive reads of a run
whose child window REACHES the standing vertex (`s0' + wSide' = μ`), the new side height
`u*'` equals the standing vertex height — the parent line's value at the vertex base
`μ·childWidth`. -/
theorem SAE_vertexEq_endpoint {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
    {n : ℕ} {f : Polynomial ℤ_[p]} {H : History p F}
    (h : ReadsOf p F n f H) (i : ℕ) (hi1 : i + 1 < H.nodes.length)
    (hadj : (H.nodes[i+1]'hi1).s0 + (H.nodes[i+1]'hi1).wSide
      = (H.nodes[i]'(by omega)).μ) :
    (H.nodes[i+1]'hi1).ustar
      = (H.nodes[i]'(by omega)).line.at
          ((H.nodes[i]'(by omega)).μ * (H.nodes[i]'(by omega)).childWidth) := by
  sorry

end LeanUrat.MovesJ
