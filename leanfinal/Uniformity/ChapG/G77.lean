/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapG.G61

/-!
# Uniformity.ChapG.G77 — the `n = 3` numeric gate at `q = 2`

**Chapter G, NODE G.77** (`blueprint/CHAP-G_base_cases_menus.md` §11). The two numeric gates that
pin node G.61 down at the smallest base, `O = ℤ_[2]`.

`gate_three_padic_two` instantiates `lowers_three` at `q = 2` (`residueCard ℤ_[2] = 2`), giving

| type | general bound | at `q = 2` |
|---|---|---|
| `c3split` | `1/q⁹` | `1/512` |
| `c3linInert` | `(q³−q²)/(2q³)` | `(8−4)/16 = 1/4` |
| `c3inert` | `(q³−q)/(3q³)` | `(8−2)/24 = 1/4` |
| `c3linRam` | `(q−1)²/q⁴` | `1/16` |
| `c3ram` | `(q−1)/q⁴` | `1/16` |

`gate_three_hmenu3_containment_two` then checks the five certified lower bounds against the
corpus's transcribed HMENU3 predictions at `q = 2` — `(4/93, 28/93, 8/31, 22/93, 5/31)`, which are
the HM3.D formulas evaluated at `q = 2` (`Φ = 31`) and which sum to `1`.

## ⚠ WHAT THE SECOND GATE IS, AND WHAT IT IS NOT

`gate_three_hmenu3_containment_two` is a **CONTAINMENT CHECK against transcribed targets**: five
inequalities between explicit rational numbers, discharged by `norm_num`. It says nothing
whatsoever about any density — not that the HMENU3 values are correct, not that they are upper
bounds, not that they are attained. Its only content is that the certified lower bounds of G.61 are
*consistent* with the corpus's own table at `q = 2`, i.e. that no certificate landed in this
chapter contradicts the transcription. A failure here would have falsified either the corpus table
or a G.61 certificate; a success is a consistency check and nothing more.

DEPENDS: G.61 (`lowers_three`) · landed `residueCard_padicInt` (`LocalData.lean:343`) and the
`ℤ_[p]` instance bundle (`Finite (ResidueField ℤ_[p])`, `IsDiscreteValuationRing ℤ_[p]`,
`IsAdicComplete (maximalIdeal ℤ_[p]) ℤ_[p]`, same file).

PROOF sketch. First gate: instantiate `lowers_three` at `O := ℤ_[2]`, rewrite `residueCard ℤ_[2]`
to `2`, and finish numerically. Second gate: `norm_num`.

⚠ RE-DERIVATION TARGET (blueprint H-9): `leancheck/UniformityCheck/N3Gates.lean`'s
`lowers3_padic_two` lands the same five values, and its `gate_bracket3_hmenu3_two` the same five
containments (there in two-sided bracket form, whose upper halves need `bracket_five`, not part of
this node's mandate).

## Status

Sorry-free, axiom-free (Lean core only).
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

namespace Uniformity.Density

/-- **G.77, first gate.** The five certified `n = 3` lower bounds over `ℤ_[2]`.

⚠ LOWER BOUNDS, NOT DENSITIES (see G.61's honesty rider). -/
theorem gate_three_padic_two :
    (1 : ℝ) / 512 ≤ decidedDensity ℤ_[2] 3 c3split
      ∧ (1 : ℝ) / 4 ≤ decidedDensity ℤ_[2] 3 c3linInert
      ∧ (1 : ℝ) / 4 ≤ decidedDensity ℤ_[2] 3 c3inert
      ∧ (1 : ℝ) / 16 ≤ decidedDensity ℤ_[2] 3 c3linRam
      ∧ (1 : ℝ) / 16 ≤ decidedDensity ℤ_[2] 3 c3ram := by
  obtain ⟨hs, hi, hc, hr, ht⟩ := lowers_three (O := ℤ_[2])
  rw [residueCard_padicInt 2] at hs hi hc hr ht
  norm_num at hs hi hc hr ht ⊢
  exact ⟨by linarith, by linarith, by linarith, by linarith, by linarith⟩

/-- **G.77, second gate.** A CONTAINMENT CHECK against HMENU3's transcribed targets at `q = 2`:
the five certified lower bounds of G.61 lie below the corpus's predicted cubic densities
`(4/93, 28/93, 8/31, 22/93, 5/31)`.

⚠ THIS PROVES NOTHING ABOUT DENSITIES. It is five inequalities between explicit rationals; the
HMENU3 values appear only as transcribed numbers, and their correctness is not asserted here. -/
theorem gate_three_hmenu3_containment_two :
    (1 : ℝ) / 512 ≤ 4 / 93 ∧ (1 : ℝ) / 4 ≤ 28 / 93 ∧ (1 : ℝ) / 4 ≤ 8 / 31
      ∧ (1 : ℝ) / 16 ≤ 22 / 93 ∧ (1 : ℝ) / 16 ≤ 5 / 31 := by
  norm_num

end Uniformity.Density

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.gate_three_padic_two
#print axioms Uniformity.Density.gate_three_hmenu3_containment_two

end AxCheck
