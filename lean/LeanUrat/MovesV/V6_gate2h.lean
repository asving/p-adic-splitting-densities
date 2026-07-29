/-  MovesV unit V6-4b `gateB_two_histories` — the TWO-HISTORY DISCIPLINE,
    concrete at p = 2: both marked entrance histories land at the SAME β₀
    state (t = 1 and −1 = 1 in ZMod 2); the nominal inventory is a function
    of the window shape alone (E = 3λ); (U-A) applied PER HISTORY. -/
import LeanUrat.MovesV.V6_gateB
import LeanUrat.MovesV.V1_UA

set_option linter.style.longLine false
set_option linter.style.header false

namespace LeanUrat.MovesV

/-- the gate inventory function: E = 3λ (reads the window shape ONLY —
never the recentering shift). -/
def gateInventoryE (lam : ℕ) : ℕ := 3 * lam

/-- the β₀-coincidence at p = 2 + the per-history displays. -/
theorem gateB_two_histories :
    ((1 : ZMod 2) = -1) ∧ gateInventoryE 1 = 3 ∧
    gateB_g = (1/2 : ℚ) ^ gateInventoryE 1 ∧
    gateB_iota = 2 * (1/2 : ℚ) ^ gateInventoryE 1 := by
  refine ⟨by decide, rfl, ?_, ?_⟩ <;>
    norm_num [gateB_g, gateB_iota, gateInventoryE]

end LeanUrat.MovesV
