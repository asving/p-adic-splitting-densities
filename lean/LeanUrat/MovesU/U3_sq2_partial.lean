/-
Unit U3.sq2_partial  (MovesU campaign)  [conditional]
moves_ref: "decided_σ(N)/p^{nN} is a PARTIAL SUM (the thr ≤ N slice) of RS.1's
           positive tree-fiber series for type σ" (SQ.2 ROUTE); tags
           "(SQ.0/CL-7) … (TREE-N/CL-10)"
deps: U2, DefsLedger.
sketch: the identity IS `FS.finiteness_stack σ N` (re-exposed as the unit's named
        statement so the exact claim is auditable, not hidden — F3); the corollary
        rewrites by it and applies U2 + `mul_le_mul_left'`.
hypothesis_fields: EXACTLY `FinStack` (CL-7 + CL-10 incl. `cl10_vpsound` + the
        TREE-N identity, D12 — REV 5/Codex-FINAL 1: the premise is the SLICE,
        never the full ledger).
-/
import Mathlib
import LeanUrat.MovesU.U2_tonelli
import LeanUrat.MovesU.DefsLedger

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesU
open ENNReal

variable {n p : ℕ} {X : ClassifierSpec n p} {F : FiberSeries n p X} {K : KernelStatements}

/-- SQ.2-partial (F3's repair — the IDENTITY is the claim): the decided count IS the
    thr ≤ N partial sum, scaled by the box cardinality. -/
theorem sq2_partial (FS : FinStack n p X F K) (σ : SplittingType n) (N : ℕ) :
    (X.decided σ N : ℝ≥0∞) = (p : ℝ≥0∞) ^ (n * N) * ∑ T ∈ F.thrSlice σ N, F.mass σ T :=
  sorry

/-- The domination corollary: the decided count is bounded by the scaled full series. -/
theorem sq2_partial_le (FS : FinStack n p X F K) (σ : SplittingType n) (N : ℕ) :
    (X.decided σ N : ℝ≥0∞) ≤ (p : ℝ≥0∞) ^ (n * N) * F.seriesSum σ :=
  sorry

end LeanUrat.MovesU
