/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapG.G61a
import Uniformity.ChapG.G61b
import Uniformity.ChapG.G61c
import Uniformity.ChapG.G61d
import Uniformity.ChapG.G61e

/-!
# Uniformity.ChapG.G61 — `lowers_three`, the five `n = 3` density LOWER BOUNDS

**Chapter G, NODE G.61** (`blueprint/CHAP-G_base_cases_menus.md` §9). The node's headline
conjunction, assembled from the five SPLIT-MANDATED sub-nodes:

| type | sub-node | certificate level | classes | lower bound |
|---|---|---|---|---|
| `c3split` `{(1,1)}³` | G.61a | 3 (deep) | 1 | `1/q⁹` |
| `c3linInert` `{(1,1),(1,2)}` | G.61b | 1 | `q²(q−1)/2` | `(q³−q²)/(2q³)` |
| `c3inert` `{(1,3)}` | G.61c | 1 | `(q³−q)/3` | `(q³−q)/(3q³)` |
| `c3linRam` `{(1,1),(2,1)}` | G.61d | 2 | `q²(q−1)²` | `(q−1)²/q⁴` |
| `c3ram` `{(3,1)}` | G.61e | 2 | `q²(q−1)` | `(q−1)/q⁴` |

## ⚠ HONESTY RIDER — THESE ARE LOWER BOUNDS, NOT THE DENSITIES

Each conjunct of `lowers_three` is an INEQUALITY certified by exhibiting an explicit family of
DECIDED coefficient classes. Nothing here computes a density. In particular the corpus's predicted
cubic densities (`lean/notes/openmath/HMENU3_PROOF_2026-08-08.md`, COROLLARY **HM3.D**), namely

* `c3split`     : `q³(q² − q + 1) / (6(q+1)Φ)`
* `c3linInert`  : `q³(q² + q + 1) / (2(q+1)Φ)`
* `c3inert`     : `q³(q + 1) / (3Φ)`
* `c3linRam`    : `q(q³ + q + 1) / ((q+1)Φ)`
* `c3ram`       : `(q² + 1) / Φ`,   with `Φ = q⁴ + q³ + q² + q + 1`,

are **NOT proved here** — not as equalities, not as upper bounds, not even as the correct order of
magnitude. They enter this chapter only as *transcribed targets* to be sanity-checked for
consistency with the certified bounds (that check is node G.77, `gate_three_hmenu3_containment_two`,
which is pure arithmetic on rationals and asserts nothing about any density). Two of the five
bounds are moreover deliberately crude: `1/q⁹` for the split type (one deep class, forced by
`q = 2`, where no residue cubic has three distinct roots) and the level-2 ramified bounds, which
see only the shallowest stratum of each family.

DEPENDS: G.61a (`gate_split3_lower`), G.61b (`gate_linInert3_lower`), G.61c (`gate_inert3_lower`),
G.61d (`gate_linRam3_lower`), G.61e (`gate_ram3_lower`).

PROOF sketch. Anonymous-constructor assembly of the five sub-node gates.

⚠ RE-DERIVATION TARGET (blueprint H-9): `leancheck/UniformityCheck/N3Gates.lean`'s `lowers_three`
lands the same conjunction with the same five values.

## Status

Sorry-free, axiom-free (Lean core only).
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

namespace Uniformity.Density

open IsLocalRing

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)]

/-- **G.61, THE FIVE `n = 3` LOWER BOUNDS**, every `O`.

⚠ **LOWER BOUNDS, NOT THE DENSITIES.** Each conjunct is certified by an explicit family of decided
level-`N` classes (`N = 3, 1, 1, 2, 2` respectively). The HM3.D target values
`q³(q²−q+1)/(6(q+1)Φ)`, `q³(q²+q+1)/(2(q+1)Φ)`, `q³(q+1)/(3Φ)`, `q(q³+q+1)/((q+1)Φ)`,
`(q²+1)/Φ` with `Φ = q⁴+q³+q²+q+1` are **NOT proved here** in any form. -/
theorem lowers_three [IsAdicComplete (maximalIdeal O) O] :
    1 / (residueCard O : ℝ) ^ 9 ≤ decidedDensity O 3 c3split
    ∧ ((residueCard O : ℝ) ^ 3 - (residueCard O : ℝ) ^ 2) / (2 * (residueCard O : ℝ) ^ 3)
        ≤ decidedDensity O 3 c3linInert
    ∧ ((residueCard O : ℝ) ^ 3 - (residueCard O : ℝ)) / (3 * (residueCard O : ℝ) ^ 3)
        ≤ decidedDensity O 3 c3inert
    ∧ ((residueCard O : ℝ) - 1) ^ 2 / (residueCard O : ℝ) ^ 4 ≤ decidedDensity O 3 c3linRam
    ∧ ((residueCard O : ℝ) - 1) / (residueCard O : ℝ) ^ 4 ≤ decidedDensity O 3 c3ram :=
  ⟨gate_split3_lower, gate_linInert3_lower, gate_inert3_lower, gate_linRam3_lower,
    gate_ram3_lower⟩

end Uniformity.Density

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.lowers_three

end AxCheck
