/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapG.G66
import Uniformity.ChapG.G70
import Uniformity.Density.DensityAPI

/-!
# Uniformity.ChapG.G71 — `drainage_three_of_hex3_bound`, the chapter's frontier interface

**Chapter G, NODE G.71** (`blueprint/CHAP-G_base_cases_menus.md` §9). The chapter's `n = 3`
conditional drainage statement, in the shape the capstone consumes: **if** the undecided
proportion at `n = 3` is eventually bounded by the normalized conservative residue, **then**
every type drains.

DEPENDS: G.66, G.70 · landed `drainage_of_undecided_comp` (CN-11, `DensityAPI.lean`),
`undecidedSeq`, `gapSeq_le_undecidedSeq`, `two_le_residueCard`.

**PROOF.**
1. `undecidedSeq O 3 N = undecidedCount O 3 N / q^(3N) ≤ q·hex3U q N / q^(3N)` by `h`, dividing
   both sides of the hypothesis by the positive `q^(3N)`.
2. the majorant `(q·hex3U q N)/q^(3N)` tends to `0` by G.70, instantiated at `q := residueCard O`
   (`hq := two_le_residueCard O`) — this is *exactly* G.70's statement, no further algebra needed.
3. `squeeze_zero'` (using nonnegativity of `undecidedSeq`, easy from `Nat.cast_nonneg`/
   `qpow_pos`) gives `Tendsto (fun N => undecidedSeq O 3 N) atTop (𝓝 0)`.
4. `drainage_of_undecided_comp (φ := id) tendsto_id this σ` (with `φ = id`, since we have the
   plain sequence, not a genuine subsequence) closes it.

**⚠ THE HYPOTHESIS `h` IS THE CHAPTER'S FRONTIER** (blueprint's verbatim note carried forward).
It is HEX3's THEOREM HEX3.A + the `U₃^σ ≤ U₃^conv` inequality (`EFF.HEX3.06`) in Lean form, and
it is **not proved here**. This node exists so that the frontier has a single named interface:
when the bridge lands, exactly one hypothesis is discharged and `DrainageAt 3` follows. `h` is
not vacuous or accidentally provable: `hex3U q N ≈ q^(2N−2)` while the trivial bound on
`undecidedCount O 3 N` is `q^(3N)`.

**TEETH.** `HEX3-LAW`, `HEX3-SPECIES` → executable regression (they evidence the hypothesis,
not the implication).

## Status

Sorry-free, axiom-free (Lean core only).
-/

set_option linter.style.longLine false

namespace Uniformity.Density

open IsLocalRing Filter

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)]

/-- **G.71, the frontier interface node.** If the `n = 3` undecided count is eventually
bounded by `q · hex3U q N` (the chapter's open frontier, HEX3's THEOREM HEX3.A in Lean form),
then every splitting type drains at `n = 3`. Does not discharge the hypothesis `h`; wires its
consequence via G.70's vanishing bound and the general-`n` drainage extraction
`drainage_of_undecided_comp`. -/
theorem drainage_three_of_hex3_bound [IsAdicComplete (maximalIdeal O) O]
    (h : ∀ N : ℕ, (undecidedCount O 3 N : ℝ)
      ≤ (residueCard O : ℝ) * (Menu.hex3U (residueCard O) N : ℝ))
    (σ : FactorizationType) : UndecidedVanishes O 3 σ := by
  have hq2 : 2 ≤ residueCard O := two_le_residueCard O
  have hzero : Tendsto (fun N => undecidedSeq O 3 N) atTop (nhds 0) := by
    apply squeeze_zero' (t₀ := atTop)
    · filter_upwards with N
      unfold undecidedSeq
      exact div_nonneg (Nat.cast_nonneg _) (qpow_pos _).le
    · filter_upwards with N
      unfold undecidedSeq
      exact div_le_div_of_nonneg_right (h N) (qpow_pos _).le
    · exact Menu.hex3U_div_tendsto_zero (residueCard O) hq2
  exact drainage_of_undecided_comp (φ := id) tendsto_id hzero σ

end Uniformity.Density

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.drainage_three_of_hex3_bound

end AxCheck
