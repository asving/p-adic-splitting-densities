/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapG.G43
import Uniformity.ChapG.G46

/-!
# Uniformity.ChapG.G47 — the exact inert and split densities at `n = 2`

**Chapter G, NODE G.47** (`blueprint/CHAP-G_base_cases_menus.md` §7). **The exact `n = 2` inert
and split densities:** both equal `q/(2(q+1))`, for every complete DVR with finite residue field,
both characteristics, wild residue characteristic included.

DEPENDS: G.43 (`decidedCount_split_eq_inert`), G.44 (`decidedSeq_two_inert_eq`),
G.45 (`Menu.tendsto_geom_partial`), G.46 (`decidedDensity_two_ram_eq`) · landed
`decidedSeq_tendsto` (`GenuineDensity.lean:286`), `sum_three_decidedDensities_eq_one`
(`Drainage.lean:962`), `two_le_residueCard` (`LocalData.lean:84`).

**PROOF.**
1. **inert** (`decidedDensity_two_inert_eq`): exactly as G.46. G.44's inert half rewrites the
   level-`N` inert-decided proportion as `∑_{k < (N+1)/2} (q−1)/(2·q^(2k+1))`; one
   `Finset.sum_congr rfl` (via `div_div`) matches that summand to G.45's shape
   `((q−1)/2)/q^(2k+1)`, so G.45 applies with `c := (q−1)/2`, `d := 1`. Its limit
   `((q−1)/2)/q · (q²/(q²−1)) = q/(2(q+1))` closes the goal after `tendsto_nhds_unique` and
   `field_simp`/`ring`. Note the inert index set really is `Finset.range ((N+1)/2)` — unlike the
   ram index set, whose signed `(N+1)/2` form G.44 corrected to `N/2`.
2. **split, ROUTE 1** (`decidedDensity_two_split_eq`, the theorem's proof, and the route the
   blueprint records as NEW): G.43's every-window identity
   `decidedCount O 2 splitType N = decidedCount O 2 inertType N` makes the two *sequences* equal
   as functions of `N`, not merely their limits, so `decidedSeq O 2 splitType` converges to
   `decidedDensity O 2 inertType`; `tendsto_nhds_unique` and part 1 finish.
3. **split, ROUTE 2** (`decidedDensity_two_split_eq_of_total`, the mandatory independent
   cross-check): subtract from the landed total mass. See its own docstring.

**⚠ WHY BOTH ROUTES.** The blueprint requires route 2 to be recorded in this file as a separate
declaration, as a mutual check on disjoint inputs: route 1 rests on the *count* identity G.43
(residue-field combinatorics: `#{anisotropic pairs} = #{separable-split pairs}`), route 2 rests on
the landed *drainage* theorem `sum_three_decidedDensities_eq_one`. Neither uses the other's input.
The corpus (`leancheck`'s `N2Exact.split_decidedDensity_two`) had route 2 only.

**⚠ ARITHMETIC CROSS-CHECK.** `2·q/(2(q+1)) + 1/(q+1) = q/(q+1) + 1/(q+1) = 1` ✓, matching the
landed `sum_three_decidedDensities_eq_one`. At `q = 2` the value is `1/3` and at `q = 3` it is
`3/8`, both strictly inside the landed brackets `[1/4, 11/16]` and `[2/9, 71/81]` (split),
`[1/9, 62/81]` (inert at `q = 3`).

**TEETH.** `W11-EXHAUST` → Lean theorem.

## Status

Sorry-free, axiom-free (Lean core only).
-/

set_option linter.style.longLine false

namespace Uniformity.Density

open IsLocalRing Filter Topology

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)]

/-- **G.47, the exact inert density at `n = 2`.** `decidedDensity O 2 inertType = q/(2(q+1))`,
over every complete DVR with finite residue field of cardinality `q` — no characteristic
hypothesis, wild residue characteristic included. -/
theorem decidedDensity_two_inert_eq [IsAdicComplete (maximalIdeal O) O] :
    decidedDensity O 2 inertType = (residueCard O : ℝ) / (2 * ((residueCard O : ℝ) + 1)) := by
  have hf : Tendsto (fun N : ℕ => (N + 1) / 2) atTop atTop :=
    Filter.tendsto_atTop_atTop.2 fun b => ⟨2 * b, fun a ha => by omega⟩
  have hgeom := Menu.tendsto_geom_partial (O := O) (((residueCard O : ℝ) - 1) / 2) 1 hf
  have hfun : decidedSeq O 2 inertType
      = fun N => ∑ i ∈ Finset.range ((N + 1) / 2),
          ((residueCard O : ℝ) - 1) / 2 / (residueCard O : ℝ) ^ (2 * i + 1) := by
    funext N
    rw [decidedSeq_two_inert_eq N]
    exact Finset.sum_congr rfl fun k _ => (div_div _ _ _).symm
  have hlim : Tendsto (decidedSeq O 2 inertType) atTop
      (𝓝 (((residueCard O : ℝ) - 1) / 2 / (residueCard O : ℝ) ^ 1
        * ((residueCard O : ℝ) ^ 2 / ((residueCard O : ℝ) ^ 2 - 1)))) := by
    rw [hfun]; exact hgeom
  rw [tendsto_nhds_unique (decidedSeq_tendsto 2 inertType) hlim]
  have hq : (2 : ℝ) ≤ (residueCard O : ℝ) := by exact_mod_cast two_le_residueCard O
  have hq0 : (residueCard O : ℝ) ≠ 0 := by linarith
  have hq1 : (residueCard O : ℝ) + 1 ≠ 0 := by linarith
  have hq2 : (residueCard O : ℝ) ^ 2 - 1 ≠ 0 := by nlinarith
  field_simp
  ring

/-- **G.47, the exact split density at `n = 2`, ROUTE 1.** `decidedDensity O 2 splitType
= q/(2(q+1))`, obtained from G.43's *every-window* count identity: split-decided and
inert-decided classes are equinumerous at EVERY level `N`, so the two decided proportions are
equal as sequences and hence have the same limit. This route uses no total-mass (drainage) input
whatsoever — contrast `decidedDensity_two_split_eq_of_total` below. -/
theorem decidedDensity_two_split_eq [IsAdicComplete (maximalIdeal O) O] :
    decidedDensity O 2 splitType = (residueCard O : ℝ) / (2 * ((residueCard O : ℝ) + 1)) := by
  have hfun : decidedSeq O 2 splitType = decidedSeq O 2 inertType := by
    funext N
    simp only [decidedSeq, decidedCount_split_eq_inert N]
  have hlim : Tendsto (decidedSeq O 2 splitType) atTop (𝓝 (decidedDensity O 2 inertType)) := by
    rw [hfun]; exact decidedSeq_tendsto 2 inertType
  rw [tendsto_nhds_unique (decidedSeq_tendsto 2 splitType) hlim, decidedDensity_two_inert_eq]

/-- Route 2, the independent cross-check of `decidedDensity_two_split_eq`: subtraction from the
landed total-mass theorem, using G.46's ram value and route 1's inert value but NOT G.43.

**This proof does not invoke `decidedCount_split_eq_inert` (G.43)** — that is the whole point of
the check. Its only inputs are `sum_three_decidedDensities_eq_one` (the landed `n = 2` drainage
identity `split + inert + ram = 1`), `decidedDensity_two_ram_eq` (G.46) and
`decidedDensity_two_inert_eq` (route 1's inert half, which likewise never touches G.43). The
arithmetic is `1 − 1/(q+1) − q/(2(q+1)) = q/(2(q+1))`. -/
theorem decidedDensity_two_split_eq_of_total [IsAdicComplete (maximalIdeal O) O] :
    decidedDensity O 2 splitType = (residueCard O : ℝ) / (2 * ((residueCard O : ℝ) + 1)) := by
  have hsum := sum_three_decidedDensities_eq_one (O := O)
  rw [decidedDensity_two_inert_eq, decidedDensity_two_ram_eq] at hsum
  have hq : (2 : ℝ) ≤ (residueCard O : ℝ) := by exact_mod_cast two_le_residueCard O
  have hq1 : (residueCard O : ℝ) + 1 ≠ 0 := by linarith
  field_simp at hsum ⊢
  linarith

section AxCheck

#print axioms Uniformity.Density.decidedDensity_two_inert_eq
#print axioms Uniformity.Density.decidedDensity_two_split_eq
#print axioms Uniformity.Density.decidedDensity_two_split_eq_of_total

end AxCheck

end Uniformity.Density
