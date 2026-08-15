/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapG.G44
import Uniformity.ChapG.G45

/-!
# Uniformity.ChapG.G46 — `decidedDensity_two_ram_eq`, the exact ramified density

**Chapter G, NODE G.46** (`blueprint/CHAP-G_base_cases_menus.md` §7). **The exact `n = 2`
ramified density:** `decidedDensity O 2 ramType = 1/(q+1)`, for every complete DVR with finite
residue field, both characteristics, wild residue characteristic included. This replaces the
landed containment check (`gate_bracket_w11_two`/`_three`, `Gates.lean`) by the value itself.

DEPENDS: G.44 (`decidedSeq_two_ram_eq`), G.45 (`Menu.tendsto_geom_partial`) · landed
`decidedSeq_tendsto` (`GenuineDensity.lean:286`), `two_le_residueCard` (`LocalData.lean:84`).

**PROOF.**
1. `decidedSeq_tendsto 2 ramType`: the level-`N` ram-decided proportions converge to
   `decidedDensity O 2 ramType` (they are monotone and bounded, so the `⨆` is the limit).
2. G.44's ram half rewrites that sequence, level by level, as the geometric partial sum
   `∑_{j < N/2} (q−1)/q^(2j+2)`. **Note the index set is `Finset.range (N / 2)`**, which is what
   G.44 actually landed: `{j | 2j+2 ≤ N}`. (The `Finset.range ((N+1)/2)` form is false at odd `N`
   because `decidedSeq O 2 ramType 1 = 0`; see G.44's CORRECTION note.)
3. `N / 2 → ∞` (`Filter.tendsto_atTop_atTop` with the witness `2 * b`), so G.45 applies with
   `c := q − 1`, `d := 2` and gives the limit `((q−1)/q²)·(q²/(q²−1))`.
4. `tendsto_nhds_unique` identifies the two limits, and
   `((q−1)/q²)·(q²/(q²−1)) = (q−1)/(q²−1) = 1/(q+1)` by `field_simp`/`ring`, whose side
   conditions `q ≠ 0`, `q² − 1 ≠ 0`, `q + 1 ≠ 0` all follow from `2 ≤ q`.

**⚠ ARITHMETIC CROSS-CHECK.** `q = 2` gives `1/3` and `q = 3` gives `1/4`, both strictly inside
the landed brackets `[1/16, 1/2]` and `[1/81, 2/3]` of `gate_bracket_padic_two_decided` /
`gate_bracket_padic_three_decided` — exactly the containment asserted by `gate_bracket_w11_two`
and `gate_bracket_w11_three`.

**TEETH.** `W11-EXHAUST` (the classical sandwich, exact rationals) → Lean theorem;
`gate_bracket_w11_two`/`_three` → Lean theorem (this node replaces containment by the value).

## Status

Sorry-free, axiom-free (Lean core only).
-/

set_option linter.style.longLine false

namespace Uniformity.Density

open IsLocalRing Filter Topology

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)]

/-- **G.46, the exact ramified density at `n = 2`.** `decidedDensity O 2 ramType = 1/(q+1)`,
over every complete DVR with finite residue field of cardinality `q` — no characteristic
hypothesis, wild residue characteristic included. -/
theorem decidedDensity_two_ram_eq [IsAdicComplete (maximalIdeal O) O] :
    decidedDensity O 2 ramType = 1 / ((residueCard O : ℝ) + 1) := by
  have hf : Tendsto (fun N : ℕ => N / 2) atTop atTop :=
    Filter.tendsto_atTop_atTop.2 fun b => ⟨2 * b, fun a ha => by omega⟩
  have hgeom := Menu.tendsto_geom_partial (O := O) ((residueCard O : ℝ) - 1) 2 hf
  have hfun : decidedSeq O 2 ramType
      = fun N => ∑ j ∈ Finset.range (N / 2),
          ((residueCard O : ℝ) - 1) / (residueCard O : ℝ) ^ (2 * j + 2) := by
    funext N
    exact decidedSeq_two_ram_eq N
  have hlim : Tendsto (decidedSeq O 2 ramType) atTop
      (𝓝 (((residueCard O : ℝ) - 1) / (residueCard O : ℝ) ^ 2
        * ((residueCard O : ℝ) ^ 2 / ((residueCard O : ℝ) ^ 2 - 1)))) := by
    rw [hfun]; exact hgeom
  rw [tendsto_nhds_unique (decidedSeq_tendsto 2 ramType) hlim]
  have hq : (2 : ℝ) ≤ (residueCard O : ℝ) := by exact_mod_cast two_le_residueCard O
  have hq0 : (residueCard O : ℝ) ≠ 0 := by linarith
  have hq1 : (residueCard O : ℝ) + 1 ≠ 0 := by linarith
  have hq2 : (residueCard O : ℝ) ^ 2 - 1 ≠ 0 := by nlinarith
  field_simp
  ring

section AxCheck

#print axioms Uniformity.Density.decidedDensity_two_ram_eq

end AxCheck

end Uniformity.Density
