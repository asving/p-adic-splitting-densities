/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapG.G36

/-!
# Uniformity.ChapG.G37 — `undecidedSeq_two_eq` / `gapSeq_two_le`

**Chapter G, NODE G.37** (`blueprint/CHAP-G_base_cases_menus.md` §6). The exact `n = 2`
drainage RATE: `undecidedSeq O 2 N = (1/q)^N`, and therefore `gapSeq O 2 σ N ≤ (1/q)^N` for
every splitting type `σ`.

DEPENDS: G.36 · landed `undecidedSeq`, `gapSeq_le_undecidedSeq`, `qpow_ne`/`qpow_pos`.

**PROOF.** `undecidedSeq O 2 N = undecidedCount O 2 N / q^(2N)`; by G.36
(`undecidedCount_two_eq`) the numerator is `q^N`, so the ratio is `q^N / q^(2N) = q^N /
(q^N·q^N) = (1/q)^N` (`2N = N + N`, `pow_add`, cross-multiplication with `qpow_ne`).
`gapSeq_two_le` then composes the general bound `gapSeq_le_undecidedSeq` with this equality.

**TEETH.** `W11-T-DRAIN` → Lean theorem.

## Status

Sorry-free, axiom-free (Lean core only).
-/

set_option linter.style.longLine false

namespace Uniformity.Density

open IsLocalRing

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)]

/-- **G.37, the exact `n = 2` drainage rate.** `undecidedSeq O 2 N = (1/q)^N`. -/
theorem undecidedSeq_two_eq [IsAdicComplete (maximalIdeal O) O] (N : ℕ) :
    undecidedSeq O 2 N = (1 / (residueCard O : ℝ)) ^ N := by
  rw [undecidedSeq, undecidedCount_two_eq]
  push_cast
  rw [div_pow, one_pow, div_eq_div_iff (qpow_ne (2 * N)) (qpow_ne N), one_mul,
    show 2 * N = N + N from two_mul N, pow_add]

/-- **G.37, the drainage rate for every type.** `gapSeq O 2 σ N ≤ (1/q)^N`. -/
theorem gapSeq_two_le [IsAdicComplete (maximalIdeal O) O] (σ : FactorizationType) (N : ℕ) :
    gapSeq O 2 σ N ≤ (1 / (residueCard O : ℝ)) ^ N :=
  (gapSeq_le_undecidedSeq 2 N σ).trans_eq (undecidedSeq_two_eq N)

section AxCheck
#print axioms Uniformity.Density.undecidedSeq_two_eq
#print axioms Uniformity.Density.gapSeq_two_le
end AxCheck

end Uniformity.Density
