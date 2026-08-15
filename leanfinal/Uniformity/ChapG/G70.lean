/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapG.G64
import Uniformity.ChapG.G66
import Uniformity.ChapG.G69

/-!
# Uniformity.ChapG.G70 — `hex3U_div_tendsto_zero`

**Chapter G, NODE G.70** (`blueprint/CHAP-G_base_cases_menus.md` §9). The normalized
conservative residue vanishes: `(q·u(q,N) : ℝ)/q^(3N) ≤ N/q^(N+1) → 0`.

DEPENDS: G.69 (and transitively G.64, G.66) · mathlib `tendsto_pow_const_div_const_pow_of_one_lt`,
`Filter.Tendsto.div_const`, `squeeze_zero'`.

**PROOF.**
1. for `N ≥ 2`, G.69 gives `q·u(q,N) ≤ N·q^(2N−1)`, so the ratio
   `(q·u(q,N):ℝ)/q^(3N) ≤ N·q^(2N-1)/q^(3N) = N/q^(N+1)` (exponent identity
   `(2N-1)+(N+1) = 3N`, valid for `N ≥ 1`).
2. `N/q^(N+1) → 0`: `tendsto_pow_const_div_const_pow_of_one_lt 1 hq1` gives `n/q^n → 0`
   (for `1 < q`); dividing by the constant `q` (`Filter.Tendsto.div_const`) gives
   `n/q^(n+1) → 0`.
3. `squeeze_zero'` (the eventual-filter version, since the bound in step 1 is only needed
   for `N ≥ 2`) with nonnegativity (all `N`) and the two bounds above.

**⚠ SCOPE FENCE (this is H-1 in Lean form, blueprint's verbatim note carried forward).** This
node is about the **arithmetic function** `hex3U`, not about `undecidedCount O 3 N`. It does
**not** prove `DrainageAt 3`, and it must never be cited as doing so. The missing bridge is
exactly HEX3's LEMMA H-1 partition + H-2 shear + H-3 block re-entry, which chapter G does not
formalise (that bridge is the hypothesis `h` of the next node, G.71).

**TEETH.** none (PROOF-ONLY, as G.69).

## Status

Sorry-free, axiom-free (Lean core only).
-/

set_option linter.style.longLine false

namespace Uniformity.Density.Menu

open Filter

/-- **G.70.** The normalized conservative residue `(q·u(q,N))/q^(3N)` tends to `0` as `N → ∞`,
via the crude majorant `N/q^(N+1)` (itself dominated by G.69's vanishing bound). -/
theorem hex3U_div_tendsto_zero (q : ℕ) (hq : 2 ≤ q) :
    Filter.Tendsto (fun N : ℕ => (q * hex3U q N : ℝ) / (q : ℝ) ^ (3 * N))
      Filter.atTop (nhds 0) := by
  have hq1 : (1 : ℝ) < (q : ℝ) := by exact_mod_cast (by omega : 1 < q)
  have hmaj : Filter.Tendsto (fun N : ℕ => (N : ℝ) / (q : ℝ) ^ (N + 1)) Filter.atTop (nhds 0) := by
    have h := tendsto_pow_const_div_const_pow_of_one_lt 1 hq1
    have h' := h.div_const (q : ℝ)
    simp only [pow_one] at h'
    have heq : ∀ N : ℕ, (N : ℝ) / (q : ℝ) ^ N / (q : ℝ) = (N : ℝ) / (q : ℝ) ^ (N + 1) := by
      intro N
      rw [pow_succ, div_div]
    simpa [heq] using h'
  apply squeeze_zero' (t₀ := Filter.atTop)
  · filter_upwards with N
    exact div_nonneg (by positivity) (by positivity)
  · filter_upwards [Filter.eventually_ge_atTop 2] with N hN
    have hN9 : hex3U q N ≤ N * q ^ (2 * N - 2) := hex3U_le q N hq hN
    have hcast : (q * hex3U q N : ℝ) ≤ (N : ℝ) * (q : ℝ) ^ (2 * N - 1) := by
      have hnat : q * hex3U q N ≤ N * q ^ (2 * N - 1) := by
        have heqp : q * q ^ (2 * N - 2) = q ^ (2 * N - 1) := by
          rw [← pow_succ']
          congr 1
          omega
        calc q * hex3U q N ≤ q * (N * q ^ (2 * N - 2)) := Nat.mul_le_mul_left _ hN9
          _ = N * (q * q ^ (2 * N - 2)) := by ring
          _ = N * q ^ (2 * N - 1) := by rw [heqp]
      exact_mod_cast hnat
    have hqpos : (0 : ℝ) < (q : ℝ) ^ (3 * N) := by positivity
    have hexp : (q : ℝ) ^ (2 * N - 1) * (q : ℝ) ^ (N + 1) = (q : ℝ) ^ (3 * N) := by
      rw [← pow_add]
      congr 1
      omega
    calc (q * hex3U q N : ℝ) / (q : ℝ) ^ (3 * N)
        ≤ (N : ℝ) * (q : ℝ) ^ (2 * N - 1) / (q : ℝ) ^ (3 * N) :=
          div_le_div_of_nonneg_right hcast hqpos.le
      _ = (N : ℝ) / (q : ℝ) ^ (N + 1) := by
          rw [← hexp]
          field_simp
  · exact hmaj

end Uniformity.Density.Menu

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Menu.hex3U_div_tendsto_zero

end AxCheck
