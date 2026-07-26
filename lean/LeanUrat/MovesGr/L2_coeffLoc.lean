import Mathlib
import LeanUrat.Moves.Defs
import LeanUrat.Moves.DefsT
import LeanUrat.Moves.DefsCore
import LeanUrat.Moves.DefsL
import LeanUrat.MovesGr.Defs
open Polynomial LeanUrat.Moves LeanUrat.MovesGr LeanUrat.MovesGr.SideVal
variable {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

theorem L2_coeffLoc (σ : Stage p F) (M : GenuineStageModel σ) : CoeffLocLaw σ := by
  refine ⟨?_, ?_, ?_⟩
  · -- (L^coeff)₀ ⊆ K.  HARD grading argument: `Subring.closure_induction` over
    -- `coeffLocSR`, tracking the OUTER T-degree of each element. Generators grRes B and
    -- rep-unit-inverses have forced outer degree (e·wPrev B resp. −w rep), and a degree-0
    -- outer-constant `C ℓ` of the closure forces ℓ to be an inner constant. Needs the
    -- graded injectivity (StageCore tie laws) transferred through M — not automatable.
    sorry
  · -- (L^coeff)₀ ⊇ K.  Realizer + unit cancellation: from `σ.hS6b ν a` (any a ∈ Kˣ, ν >
    -- wPrev Φ) get a coefficient B with grRes B = C(C a)·C(T_in(−t·ν))·T_out(e·ν); the
    -- inner-T and outer-T factors must be cancelled by products of the rep-unit inverses
    -- (S₂ generators) whose combined weight matches. Every K-constant then lies in closure.
    sorry
  · -- (P1) z-pinning.  DERIVED REDUCTION (this file): with W i := σ.wPrev (σ.reps.get i),
    -- grRes(rep i) = C(C c_i · T_in(−t·W i))·T_out(e·W i) [hS5+hStretch] and
    -- grRes Φ = C(T_in s)·T_out h [hRΦ+hwΦ], the vector zv = (v, e) works iff
    --   (A) e·∑ v i·W i + e·h = 0,  (B) −t·∑ v i·W i + s·e = 1,  (C) ∏ c_i^{v i} = 1.
    -- Using e·s + h·t = 1 (hbez) both (A),(B) collapse to ∑ v i·W i = −h. So zv = V^{−h}·Y^{e}
    -- with V a representative of parent-weight 1 and trivial scalar (c=1). That "uniformizer
    -- rep exists" is base/TRANS construction data, NOT an abstract `Stage` field — the gap.
    sorry
