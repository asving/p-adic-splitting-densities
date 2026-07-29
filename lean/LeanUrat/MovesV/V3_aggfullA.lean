/-  MovesV unit V3-8a `ent_agg_conv` (SPLIT REV 4, Codex-7; PREMISE RE-KEYED
    REV 7, Codex6-C7) — THE NOTE-EXACT AGGREGATION: convergence GIVEN XHD-s
    on the shallow layer ALONE (summability DERIVED via box_card). NO (ENT-U). -/
import LeanUrat.MovesV.V3_instbijC
import LeanUrat.MovesV.V3_aggfin
import LeanUrat.MovesV.V0_partition

set_option linter.style.longLine false
set_option linter.style.header false

namespace LeanUrat.MovesV

theorem ent_agg_conv {n : ℕ} {C : CtsFamily n} {S : StepSys n}
    (V : CtsMeasured n C S) (XsEnt : XHDsEnt n S V) (DE : XHDdEnt n S V)
    (β₀ : S.Cell) (q₀ : ℚ) (hq : q₀ ∈ V.Pools) :
    ∃ v : ℝ, HasSum
      (fun p : Σ i : V.EntIx β₀,
          {h // ((V.entDom i.1.1).comps.get i.1.2).Mem h} =>
        ιshH V p.1.1.1 p.2.1 β₀ q₀) v := by
  sorry

end LeanUrat.MovesV
