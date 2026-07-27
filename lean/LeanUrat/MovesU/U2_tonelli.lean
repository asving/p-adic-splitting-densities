/-
Unit U2.tonelli  (MovesU campaign)  [TAG-FREE step 3]
moves_ref: "the positive series has a well-defined EXTENDED-VALUE sum in [0, ∞]
           unconditionally (nonnegative terms) … FINITENESS … and IDENTIFICATION …
           are NOT Tonelli's" (rev 2, pass-1 critical 7)
deps: Defs.
sketch: `ENNReal.sum_le_tsum` (Topology/Algebra/InfiniteSum/ENNReal.lean); existence
        is the totality of `∑'` in ℝ≥0∞ (`ENNReal.summable`,
        `ENNReal.tsum_eq_iSup_sum` — the extended-value existence is definitional in
        ℝ≥0∞; no separate lemma needed).
hypothesis_fields: none (the FiberSeries DATA is used, no Prop field).
-/
import Mathlib
import LeanUrat.MovesU.Defs

set_option linter.style.longLine false
set_option linter.style.header false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesU
open ENNReal

/-- Tonelli's tag-free content at MovesU granularity: every thr ≤ N partial sum is
    dominated by the extended-value series sum (which exists unconditionally in
    [0,∞]). -/
theorem tonelli_partial_le {n p : ℕ} {X : ClassifierSpec n p} (F : FiberSeries n p X)
    (σ : SplittingType n) (N : ℕ) :
    ∑ T ∈ F.thrSlice σ N, F.mass σ T ≤ F.seriesSum σ :=
  -- `seriesSum σ = ∑' T, F.mass σ T` (`ENNReal.summable`, extended-value existence
  -- is definitional in ℝ≥0∞), so this is a partial-sum ≤ tsum bound.
  ENNReal.sum_le_tsum (F.thrSlice σ N)

end LeanUrat.MovesU
