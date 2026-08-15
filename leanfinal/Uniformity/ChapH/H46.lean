/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.Density.Drainage

/-!
# Uniformity.ChapH.H46 — `slotOdd`, `slotEven`, and the ragged band's cardinality

**Chapter H, NODE H.46** (`blueprint/CHAP-H_general_induction.md`, source `EFF.GENH4.17`
§S2.3). At genre E the `A₁` slot string is realized on the **half-integer** `dv` ladder: for
`h = 2t+1` odd and `N ≥ 2t+2`, the odd (`α₁`-borne) heights run over
`{2h+1, 2h+3, …, 2N−2+h}` and the even (`α₀`-borne) heights over `{2h+2, 2h+4, …, 2N−2}`,
together covering every integer of `[2h+1, 2N−2]`. This file lands the two strings and the
**ragged band** count: the heights of the odd string at or above `2N` number exactly
`(h−1)/2 = t`, and the band is **empty at `h = 1`**.

Arithmetic check (the `h = 3`, `N = 7` cell, where the corpus's genre-E drainage CORRECTION
lives — `EFF.GENH4.10`: `512`, not `256`): odd string `[7, 15]` odd, even string `[8, 12]`
even, union covers `[7, 12]`; the band `[14, 15]` holds the single odd height `15` = `t = 1`.

DEPENDS: none · mathlib `Finset.card_image_of_injective`, `Nat.card_Icc`.

## Status

Sorry-free, axiom-free (Lean core only).
-/

set_option linter.style.longLine false

namespace Uniformity.Density.Induction

/-- The odd (`α₁`-borne) `dv`-heights of the `A₁` string at genre E. -/
def slotOdd (N h : ℕ) : Finset ℕ :=
  (Finset.Icc ((h + 1) / 2) (N - 1)).image (fun v => 2 * v + h)

/-- The even (`α₀`-borne) `dv`-heights of the `A₁` string at genre E. -/
def slotEven (N h : ℕ) : Finset ℕ :=
  (Finset.Icc (h + 1) (N - 1)).image (fun v => 2 * v)

/-- The ragged band `{m ∈ slotOdd | 2N ≤ m}` has exactly `t = (h−1)/2` heights at `h = 2t+1`. -/
theorem raggedBand_card (N t : ℕ) (hN : 2 * t + 2 ≤ N) :
    ((slotOdd N (2 * t + 1)).filter (fun m => 2 * N ≤ m)).card = t := by
  have hinj : Function.Injective (fun v : ℕ => 2 * v + (2 * t + 1)) := by
    intro a b hab
    simp only at hab
    omega
  have hband : (slotOdd N (2 * t + 1)).filter (fun m => 2 * N ≤ m)
      = (Finset.Icc (N - t) (N - 1)).image (fun v => 2 * v + (2 * t + 1)) := by
    ext m
    simp only [slotOdd, Finset.mem_filter, Finset.mem_image, Finset.mem_Icc]
    constructor
    · rintro ⟨⟨v, ⟨hv1, hv2⟩, rfl⟩, hm⟩
      exact ⟨v, ⟨by omega, by omega⟩, rfl⟩
    · rintro ⟨v, ⟨hv1, hv2⟩, rfl⟩
      exact ⟨⟨v, ⟨by omega, by omega⟩, rfl⟩, by omega⟩
  rw [hband, Finset.card_image_of_injective _ hinj, Nat.card_Icc]
  omega

/-- The band collapses at `h = 1`: the odd string tops out at `2N − 1`. -/
theorem raggedBand_empty_of_h_one (N : ℕ) (hN : 2 ≤ N) :
    ((slotOdd N 1).filter (fun m => 2 * N ≤ m)) = ∅ := by
  rw [Finset.filter_eq_empty_iff]
  intro m hm
  simp only [slotOdd, Finset.mem_image, Finset.mem_Icc] at hm
  obtain ⟨v, ⟨hv1, hv2⟩, rfl⟩ := hm
  omega

end Uniformity.Density.Induction

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Induction.raggedBand_card
#print axioms Uniformity.Density.Induction.raggedBand_empty_of_h_one

end AxCheck
