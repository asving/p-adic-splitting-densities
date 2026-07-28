/-
Unit U20a.NA_transport_root  (HC-2 campaign — blueprint §9 F-2 pre-split of U20; NEW unit,
census +1; sub-lemma discipline: this statement is PROVER-REFINABLE, the assembled
`readsOf_NA` in U20_NA.lean is normative and byte-unchanged)
moves_ref: §C C.0 (NA) display; the F-2 semantic spec — cross-frame VERTEX-VALUE
TRANSPORT at a ROOT parent: "under `ReadsOf` at consecutive reads (i, i+1), the parent's
line value at the standing vertex base `μ·childWidth` is realized as the frame-(i+1)
actual slot weight of f's development at the vertex slot"; parent = the root read
(frame 0: `STR = 1`, `Dwidth = 1` via hroot/hDwidth): D.4 base reading + D.8 at ν₀.
deps: D4 (`SideReads` at reads i and i+1), `HistoryCoherent` (root frame degree 1,
width chain), `IsDevelopment` (Fact A uniqueness for transfer between developments).
difficulty: medium-hard.  hypothesis_fields: none.
SCALE NOTE (C.1.0(c)): stage-(i+1) weights are `STR_{i+1} ×` absolute, and `Node.line`
is absolute v_p-scale — the transport equation is stated multiplied through by
`H.strFrame (i+1)`.  The guard `B νp.μ ≠ 0` is part of the conclusion (the pinned old
vertex digit is PRESENT in f's child-frame development — its weight is what the parent
line's vertex value reads); `hNd` guards the junk truncation `B j = 0` for `j ≥ Nd`.
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

/-- (NA) vertex-value transport, ROOT parent (F-2/U20a): at consecutive reads of a run
whose parent read `i` is the ROOT read, the parent's line value at the standing vertex
base `μ·childWidth` is realized as the frame-(i+1) actual slot weight of f's development
at the vertex slot (stage scale: `σ.w = STR ×` absolute), and that vertex coefficient is
nonzero. -/
theorem NA_transport_root {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
    {n : ℕ} {f : Polynomial ℤ_[p]} {H : History p F}
    (h : ReadsOf p F n f H) (i : ℕ) (hi1 : i + 1 < H.nodes.length)
    (hsp : (H.nodes[i]'(by omega)).species = ReadSpecies.root)
    (B : ℕ → Polynomial ℤ_[p]) (Nd : ℕ)
    (hdev : IsDevelopment (H.nodes[i+1]'hi1).σ.Φ f B Nd)
    (hNd : (H.nodes[i]'(by omega)).μ < Nd) :
    B ((H.nodes[i]'(by omega)).μ) ≠ 0 ∧
      (((H.nodes[i+1]'hi1).σ.w (B ((H.nodes[i]'(by omega)).μ)) : ℚ))
        = (H.strFrame (i+1) : ℚ) *
          (H.nodes[i]'(by omega)).line.at
            ((H.nodes[i]'(by omega)).μ * (H.nodes[i]'(by omega)).childWidth) :=
  K1_NA_transport_root h i hi1 hsp B Nd hdev hNd

end LeanUrat.MovesJ
