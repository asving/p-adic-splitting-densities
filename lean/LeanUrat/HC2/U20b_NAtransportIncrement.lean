/-
Unit U20b.NA_transport_increment  (HC-2 campaign — blueprint §9 F-2 pre-split of U20; NEW
unit, census +1; sub-lemma discipline: this statement is PROVER-REFINABLE, the assembled
`readsOf_NA` in U20_NA.lean is normative and byte-unchanged)
moves_ref: §C C.0 (NA) display; the F-2 semantic spec — cross-frame VERTEX-VALUE
TRANSPORT at an INCREMENT parent, routed through the species-specific transition clause:
via `IsNodeLift`/`TransitionCoreL` (coherence's increment leg) + `LandingCylinderL`'s
(BOX)/(VERTEX) clauses (Moves `L5_landTransport_R4`).
deps: D4 (`SideReads` at reads i and i+1), `HistoryCoherent` (the recorded increment
transition at the recorded node data), Moves `LandingCylinderL`/`L5_landTransport_R4`
(PROVED — D.8's two-sided landing).
difficulty: hard-ish.  hypothesis_fields: none.
SCALE NOTE (C.1.0(c)): stage-(i+1) weights are `STR_{i+1} ×` absolute, and `Node.line`
is absolute v_p-scale — the transport equation is stated multiplied through by
`H.strFrame (i+1)`.  Guards as in U20a.
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

/-- (NA) vertex-value transport, INCREMENT parent (F-2/U20b): at consecutive reads of a
run whose parent read `i` is an INCREMENT, the parent's line value at the standing vertex
base `μ·childWidth` is realized as the frame-(i+1) actual slot weight of f's development
at the vertex slot (stage scale: `σ.w = STR ×` absolute), and that vertex coefficient is
nonzero.

⚠ VACUITY CAVEAT (2026-07-30 verify-2 fold-in; task #44 / A16+A39): this is a one-line
consumer of the K1 kernel (`K1_readVertexPin`), whose non-recentering legs at
`e·g ≥ 2` close via the V10 INCONSISTENCY finding — `ReadsOf` admits NO such instances
(the `HistoryCoherent` read-pair keying is a flagged FAITHFULNESS BUG, pending
sign-off task #44) — so this transport is currently VACUOUS at its intended steep
perimeter. Never cite it as machine-checked transport mathematics there. -/
theorem NA_transport_increment {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
    {n : ℕ} {f : Polynomial ℤ_[p]} {H : History p F}
    (h : ReadsOf p F n f H) (i : ℕ) (hi1 : i + 1 < H.nodes.length)
    (hsp : (H.nodes[i]'(by omega)).species = ReadSpecies.increment)
    (B : ℕ → Polynomial ℤ_[p]) (Nd : ℕ)
    (hdev : IsDevelopment (H.nodes[i+1]'hi1).σ.Φ f B Nd)
    (hNd : (H.nodes[i]'(by omega)).μ < Nd) :
    B ((H.nodes[i]'(by omega)).μ) ≠ 0 ∧
      (((H.nodes[i+1]'hi1).σ.w (B ((H.nodes[i]'(by omega)).μ)) : ℚ))
        = (H.strFrame (i+1) : ℚ) *
          (H.nodes[i]'(by omega)).line.at
            ((H.nodes[i]'(by omega)).μ * (H.nodes[i]'(by omega)).childWidth) := by
  -- U20b_final discharge (blueprint §10 V9: "U20a/U20b/U22-E2 close by the staged
  -- one-line consumers"): the increment leg has no independent Lean-core route; it is
  -- the byte-identical fenced statement of `K1_NA_transport_increment`, the one-line
  -- consumer of the read-indexed D.8 vertex-pin kernel `K1_readVertexPin`.
  exact K1_NA_transport_increment h i hi1 hsp B Nd hdev hNd

end LeanUrat.MovesJ

#print axioms LeanUrat.MovesJ.NA_transport_increment
