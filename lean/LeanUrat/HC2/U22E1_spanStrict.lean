/-
Unit U22-E1.SAE_spanStrict_endpoint  (HC-2 campaign — blueprint §9 F-4 endpoint of U22;
NEW unit, census +1; statement landed in-file from the proven reduction and
PROVER-REFINABLE — the assembled `readsOf_SAE` in U22_SAE.lean is normative and
byte-unchanged)
moves_ref: §C rev 12 (SAE) display; the F-4 semantic spec — THE STRICT SPAN-ENTRY
ENDPOINT: "at every recorded span slot strictly below the parent vertex, f's actual
frame-weight strictly exceeds the parent line's value (the parent's (ZC)-zeroed-strips
content: interior zeros push actual valuations strictly above the old line)".
deps: D4 (`SideReads` at reads i and i+1), the parent's (ZC)-zeroed strips, K1 slot
reading.  difficulty: HARD (the genuine frontier of the F-4 reduction).
hypothesis_fields: none.
SCALE NOTE (C.1.0(c)): stage-(i+1) weights are `STR_{i+1} ×` absolute, and `Node.line`
is absolute v_p-scale — the strict inequality is stated multiplied through by
`H.strFrame (i+1)`.  The guard `B j ≠ 0` keeps the claim statable (`σ.w` of the zero
polynomial is junk; a vanished span coefficient exceeds every finite line value morally,
and the assembled proof consumes this endpoint only at slots SideReads(ii) makes
nonzero).
-/
import Mathlib
import LeanUrat.HC2.Defs

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesJ
open Polynomial LeanUrat.Moves LeanUrat.MovesC LeanUrat.MovesD

/-- (SAE) strict span-entry endpoint (F-4/U22-E1): at consecutive reads of a run, at every
recorded span slot `j` of the child read strictly below the parent vertex (`j < μ`), f's
actual frame-(i+1) weight at slot `j` strictly exceeds the parent line's value at `j`'s
base index (stage scale: `σ.w = STR ×` absolute). -/
theorem SAE_spanStrict_endpoint {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
    {n : ℕ} {f : Polynomial ℤ_[p]} {H : History p F}
    (h : ReadsOf p F n f H) (i : ℕ) (hi1 : i + 1 < H.nodes.length)
    (B : ℕ → Polynomial ℤ_[p]) (Nd : ℕ)
    (hdev : IsDevelopment (H.nodes[i+1]'hi1).σ.Φ f B Nd) :
    ∀ j : ℕ, (H.nodes[i+1]'hi1).s0 ≤ j →
      j ≤ (H.nodes[i+1]'hi1).s0 + (H.nodes[i+1]'hi1).wSide →
      j < (H.nodes[i]'(by omega)).μ → B j ≠ 0 →
      (H.strFrame (i+1) : ℚ) *
          (H.nodes[i]'(by omega)).line.at (j * (H.nodes[i]'(by omega)).childWidth)
        < (((H.nodes[i+1]'hi1).σ.w (B j) : ℚ)) := by
  sorry

end LeanUrat.MovesJ
