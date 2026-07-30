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
import LeanUrat.HC2.K1_vertexPin

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesJ
open Polynomial LeanUrat.Moves LeanUrat.MovesC LeanUrat.MovesD

/-- (SAE) adjacent-vertex equality endpoint (F-4/U22-E2): at consecutive reads of a run
whose child window REACHES the standing vertex (`s0' + wSide' = μ`), the new side height
`u*'` equals the standing vertex height — the parent line's value at the vertex base
`μ·childWidth`.

⚠ VACUITY CAVEAT (2026-07-30 verify-2 fold-in; the A16 queued fix; task #44 / A39):
this is a one-line consumer of the K1 kernel (`K1_SAE_vertexEq_endpoint`, resting on
`K1_readVertexPin_nonrec`), whose non-recentering legs at `e·g ≥ 2` close via the V10
INCONSISTENCY finding — `ReadsOf` admits NO such instances (the `HistoryCoherent`
read-pair keying is a flagged FAITHFULNESS BUG, pending sign-off task #44) — so this
endpoint is currently VACUOUS at its intended steep perimeter. Never cite it as
machine-checked transport mathematics there. -/
theorem SAE_vertexEq_endpoint {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
    {n : ℕ} {f : Polynomial ℤ_[p]} {H : History p F}
    (h : ReadsOf p F n f H) (i : ℕ) (hi1 : i + 1 < H.nodes.length)
    (hadj : (H.nodes[i+1]'hi1).s0 + (H.nodes[i+1]'hi1).wSide
      = (H.nodes[i]'(by omega)).μ) :
    (H.nodes[i+1]'hi1).ustar
      = (H.nodes[i]'(by omega)).line.at
          ((H.nodes[i]'(by omega)).μ * (H.nodes[i]'(by omega)).childWidth) := by
  -- U22-E2_final (V-prime endgame): the F-4 u*-tie reduction is complete and machine-checked
  -- in `K1_SAE_vertexEq_endpoint` (K1_vertexPin.lean): SideReads(ii) top-endpoint equality
  -- `e'·σ'.w(B μ) + μ·h' = gam'` + the γ-tie (adjacency) give `σ'.w(B μ) = STR_{i+1}·u*'`,
  -- and the K1 kernel pins the SAME quantity to `STR_{i+1}·line_i.at(μ·childWidth)`; cancel
  -- `STR_{i+1} > 0` and `Node.line`/`Node.ustar` absolute scale leaves the fenced ℚ-form.
  -- The sole residual behind this `exact` is the consolidated non-recentering kernel
  -- `K1_readVertexPin_nonrec` (the read-side carry-algebra vertex pin) — a SEPARATE `_final`
  -- unit; U22-E2 carries no independent obligation.
  exact K1_SAE_vertexEq_endpoint h i hi1 hadj

end LeanUrat.MovesJ
