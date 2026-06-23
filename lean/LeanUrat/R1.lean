/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.Interface

/-!
# LeanUrat.R1 — self-similar self-loop exponent (`notes/R1_complete.md`)

**Cleaned 2026-06-15.** The earlier version contained three `(h : P) : P := h` tautologies
(`discriminant_eq_vandermonde_sq`, `vandermonde_constant_on_stratum`, `stratum_volume`) that
assumed their own conclusions and proved nothing — removed. The genuine measure-theoretic content of
R1 (the Vandermonde pushforward `μ_n(W) = (1/n!)∫|∏(α_i-α_j)|`, the constancy `|V| = q^{-d(T)}` on a
cluster-tree stratum, and the self-similar integral `I_m` closing geometrically) is a cited `p`-adic
measure foundation NOT in mathlib v4.31.0; it is **not** faked here. Where the Goal needs it, it
enters through the named `Interface` axioms (the `DensityFoundation.decomposition` structure and
`clusterVolume_rational`); a future module may state it as a real theorem over an explicit measure.

What remains is the one genuinely-proved arithmetic fact: the self-loop exponent values.
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false

namespace LeanUrat.R1

/-- The self-similar self-loop exponent `w(m) = m(m+1)/2 - 1 = C(m,2) + m - 1`
(`notes/HUMAN_PROOF.md §7`; the rescale geometric series `1/(1 - q^{-w(m)})`). -/
def treeDistanceWeight (m : ℕ) : ℕ := m * (m + 1) / 2 - 1

/-- The self-loop exponents are `2, 5, 9, 14` for `m = 2, 3, 4, 5` (PROVED;
`w(3) = 5` ⇒ the `q^5 - 1` denominator `(q-1)·Φ` seen at `n = 3`). -/
theorem treeDistanceWeight_values :
    treeDistanceWeight 2 = 2 ∧ treeDistanceWeight 3 = 5 ∧
    treeDistanceWeight 4 = 9 ∧ treeDistanceWeight 5 = 14 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide

end LeanUrat.R1
