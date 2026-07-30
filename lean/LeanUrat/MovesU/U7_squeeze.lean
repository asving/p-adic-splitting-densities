/-
Unit U7.squeeze  (MovesU campaign)  [TAG-FREE step 4]
moves_ref: "With env(N) → 0 (X.3/CL-4, the QUALITATIVE form …):
           ρ_σ(p) := lim_{N→∞} decided_σ(N)/p^{nN} EXISTS and = R_σ(p)"
deps: Defs.
sketch: divide `hbr` by `p^{nN} > 0` (`div_le_div_of_nonneg_right` forms) to get
        `r − env N ≤ dmass σ N ≤ r`; squeeze with Mathlib's
        `tendsto_of_tendsto_of_tendsto_of_le_of_le` (the `'` eventually-variant if
        convenient); lower leg `r − env N → r − 0 = r` by
        `Filter.Tendsto.const_sub` + `sub_zero`; upper leg `tendsto_const_nhds`.
hypothesis_fields: none (tag-free forcing; the tagged bracket/limit enter as
        arguments, instantiated at U10 from U6 + `cl4_env_tendsto`). `1 < p` =
        arithmetic scaffolding, as at U5 (G6).
-/
import Mathlib
import LeanUrat.MovesU.Defs

set_option linter.style.longLine false
set_option linter.style.header false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesU
open Filter Topology

/-- The limit forcing: a two-sided bracket with vanishing envelope forces
    ρ_σ(p) = lim dmass σ N = r. -/
theorem squeeze_limit {n p : ℕ} (X : ClassifierSpec n p) (hp : 1 < p) (r : ℝ)
    (σ : SplittingType n)
    (hbr : ∀ N, (r - X.env N) * (p : ℝ) ^ (n * N) ≤ (X.decided σ N : ℝ) ∧
      (X.decided σ N : ℝ) ≤ r * (p : ℝ) ^ (n * N))
    (henv : Tendsto X.env atTop (𝓝 0)) :
    Tendsto (X.dmass σ) atTop (𝓝 r) := by
  have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast Nat.zero_lt_one.trans hp
  have hlower : ∀ N, r - X.env N ≤ X.dmass σ N := by
    intro N
    have hP : (0 : ℝ) < (p : ℝ) ^ (n * N) := pow_pos hp0 _
    rw [ClassifierSpec.dmass, le_div_iff₀ hP]
    exact (hbr N).1
  have hupper : ∀ N, X.dmass σ N ≤ r := by
    intro N
    have hP : (0 : ℝ) < (p : ℝ) ^ (n * N) := pow_pos hp0 _
    rw [ClassifierSpec.dmass, div_le_iff₀ hP]
    exact (hbr N).2
  have hg : Tendsto (fun N => r - X.env N) atTop (𝓝 r) := by
    simpa using henv.const_sub r
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le hg tendsto_const_nhds hlower hupper

end LeanUrat.MovesU
