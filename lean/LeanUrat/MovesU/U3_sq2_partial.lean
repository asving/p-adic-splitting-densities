/-
Unit U3.sq2_partial  (MovesU campaign)  [RETYPED 2026-07-30 per the ratification]
moves_ref: "decided_σ(N)/p^{nN} is a PARTIAL SUM (the thr ≤ N slice) of RS.1's
           positive tree-fiber series for type σ" (SQ.2 ROUTE); tags
           "(SQ.0/CL-7) … (TREE-N/CL-10)"
deps: U2, DefsLedger.
RETYPE (ratification GAP 1 — "sq2_partial sheds the enlarged hypothesis slice"):
        the premise is now EXACTLY the TREE-N seam (`TreeSeam` — the typed
        canonical-tree assignment + per-tree count tie), from which the identity is
        DERIVED (`TreeSeam.finiteness_stack`), never assumed. VP-SOUND and the CL-7
        mechanics no longer ride this unit's hypothesis surface.
hypothesis_fields: EXACTLY `TreeSeam` (+ `NeZero p` counting scaffolding).
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

variable {n p : ℕ} {X : ClassifierSpec n p} {F : FiberSeries n p X}

/-- SQ.2-partial (RETYPED — the identity is now DERIVED from the typed TREE-N seam):
    the decided count IS the thr ≤ N partial sum, scaled by the box cardinality. -/
theorem sq2_partial [NeZero p] (seam : TreeSeam n p X F) (σ : SplittingType n)
    (N : ℕ) :
    (X.decided σ N : ℝ≥0∞) = (p : ℝ≥0∞) ^ (n * N) * ∑ T ∈ F.thrSlice σ N, F.mass σ T :=
  seam.finiteness_stack σ N

/-- The domination corollary: the decided count is bounded by the scaled full series. -/
theorem sq2_partial_le [NeZero p] (seam : TreeSeam n p X F) (σ : SplittingType n)
    (N : ℕ) :
    (X.decided σ N : ℝ≥0∞) ≤ (p : ℝ≥0∞) ^ (n * N) * F.seriesSum σ := by
  rw [sq2_partial seam σ N]
  exact mul_le_mul_right (tonelli_partial_le F σ N) _

end LeanUrat.MovesU
