/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.Density.GenuineDensity

/-!
# Uniformity.ChapG.G45 — `tendsto_geom_partial`, the geometric-limit bridge

**Chapter G, NODE G.45** (`blueprint/CHAP-G_base_cases_menus.md` §7). The geometric-limit
bridge: for `c : ℝ` and `q ≥ 2`,
`Tendsto (fun N => ∑_{i < f N} c/q^(2i+d)) atTop (𝓝 (c·q^(−d)·q²/(q²−1)))` whenever `f N → ∞`.

DEPENDS: landed `Uniformity.Density.qR_pos`, `Uniformity.Density.one_lt_residueCard`
(`LocalData.lean:95`) · mathlib `hasSum_geometric_of_lt_one`, `HasSum.tendsto_sum_nat`,
`Filter.Tendsto.comp`.

**PROOF.**
1. rewrite the summand as `(c/q^d) * (q^(−2))^i`.
2. `hasSum_geometric_of_lt_one` at ratio `q^(−2) ∈ [0,1)` (`one_lt_residueCard`), giving the sum
   `1/(1 − q^(−2)) = q²/(q²−1)`.
3. `HasSum.tendsto_sum_nat` for the partial sums along `Finset.range`.
4. compose with `hf`.

## Status

Sorry-free, axiom-free (Lean core only).
-/

set_option linter.style.longLine false

namespace Uniformity.Density.Menu

open Filter Topology

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (IsLocalRing.ResidueField O)]

theorem tendsto_geom_partial (c : ℝ) (d : ℕ) {f : ℕ → ℕ} (hf : Tendsto f atTop atTop) :
    Tendsto (fun N => ∑ i ∈ Finset.range (f N), c / (residueCard O : ℝ) ^ (2 * i + d)) atTop
      (𝓝 (c / (residueCard O : ℝ) ^ d * ((residueCard O : ℝ) ^ 2
        / ((residueCard O : ℝ) ^ 2 - 1)))) := by
  set q : ℝ := (residueCard O : ℝ) with hqdef
  have hq1 : 1 < q := by rw [hqdef]; exact_mod_cast one_lt_residueCard O
  have hqpos : 0 < q := qR_pos
  have hq2pos : (0:ℝ) < q ^ 2 := by positivity
  set r : ℝ := 1 / q ^ 2 with hrdef
  have hr0 : 0 ≤ r := by positivity
  have hr1 : r < 1 := by
    rw [hrdef, div_lt_one hq2pos]
    nlinarith
  have hterm : ∀ i : ℕ, c / q ^ (2 * i + d) = (c / q ^ d) * r ^ i := by
    intro i
    rw [hrdef, div_pow, one_pow, pow_add, pow_mul]
    ring
  have hsum : HasSum (fun i : ℕ => (c / q ^ d) * r ^ i)
      ((c / q ^ d) * (1 - r)⁻¹) := (hasSum_geometric_of_lt_one hr0 hr1).mul_left (c / q ^ d)
  have htend : Tendsto (fun n => ∑ i ∈ Finset.range n, (c / q ^ d) * r ^ i) atTop
      (𝓝 ((c / q ^ d) * (1 - r)⁻¹)) := hsum.tendsto_sum_nat
  have hval : (c / q ^ d) * (1 - r)⁻¹ = c / q ^ d * (q ^ 2 / (q ^ 2 - 1)) := by
    have hr' : (1 : ℝ) - r = (q ^ 2 - 1) / q ^ 2 := by rw [hrdef]; field_simp
    rw [hr', inv_div]
  rw [← hval]
  have hcomp := htend.comp hf
  have hfun : (fun N => ∑ i ∈ Finset.range (f N), c / q ^ (2 * i + d))
      = (fun n => ∑ i ∈ Finset.range n, (c / q ^ d) * r ^ i) ∘ f := by
    funext N
    exact Finset.sum_congr rfl (fun i _ => hterm i)
  rw [hfun]
  exact hcomp

section AxCheck
#print axioms Uniformity.Density.Menu.tendsto_geom_partial
end AxCheck

end Uniformity.Density.Menu
