/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapH.H45

/-!
# Uniformity.ChapH.H91 — `LeafE`, `leafFactorE`: the six genre-E leaf-law factors

**Chapter H, NODE H.91** (`blueprint/CHAP-H_general_induction.md` §12; source `EFF.GENH4.25`,
§S6.1's fixed-width leaf-law table). *The leaf-law exponent shapes (the six genre-E leaves).*

The six leaf laws of `THEOREM GENH4.A` carry the letter/census factors

| leaf | factor |
| --- | --- |
| `RAM(u)` | `q − 1` |
| `2SIDED(w, u−w)` | `(q − 1)²` |
| `SPLITEQ(dμ)` | `splitEqCensus q` |
| `INERT(dμ)` | `inertCensus q` |
| `SPLTAIL(w)` | `q − 1` |
| `UND` | `1` |

and the two tail leaves' exponents both carry the band term `(h−1)/2`, which is H.46's
`raggedBand_card`.  This node lands the **factors** and their positivity; no relation among the
factors (in particular no `splitEqCensus q + inertCensus q + (q−1) = ⋯` identity) is claimed.

**⚠ THE `3 ≤ q` HYPOTHESIS IS HONEST, NOT DEFENSIVE.** `splitEqCensus 2 = 0`: over `F₂` there is
exactly one nonzero element, so the `SPLITEQ` leaf is **empty at `q = 2`** (H.45's note).  Stating
`leafFactorE_pos` at `2 ≤ q` would be **FALSE**.  This is another instance of the `q = 2`
degeneracy the chapter's audit rule is about — here it makes a *hypothesis* mandatory rather than
an audit column.

**⚠ THE EXPONENTS ARE NOT FORMALIZED, AND WHY.** The table's free-slot exponents are counts on the
slot strings of H.46 (`#A₀ slots > u`, `#A₁ slots s : 2s > u`, …), evaluated as affine functions of
`(N, h, param)` on each parity stratum.  Formalizing them means formalizing the strings'
`Finset.filter` counts and then one `Finset.card` computation per leaf — six more nodes with little
content.  The blueprint's decision: land the factors here and the band term at H.46, and leave the
per-leaf exponent evaluation to the count-law assembly (`W12`/`GENH4.A` content, honesty item
H-12; §16 item 5 flags the omission).

DEPENDS: H.45 (`splitEqCensus`, `inertCensus` and their subtraction-free forms).

## Status

Sorry-free, axiom-free (Lean core only).
-/

set_option linter.style.longLine false

namespace Uniformity.Density.Induction

/-- The six decided/undecided leaf labels of a genre-E stage read, and their letter/census factors
(`THEOREM GENH4.A`'s four-slot model, §S6.1's table). -/
inductive LeafE where | ram | twoSided | splitEq | inert | splTail | und
  deriving DecidableEq, Fintype

/-- **NODE H.91.** The letter/census factor attached to each genre-E leaf law. -/
def leafFactorE (q : ℕ) : LeafE → ℕ
  | .ram      => q - 1
  | .twoSided => (q - 1) ^ 2
  | .splitEq  => splitEqCensus q
  | .inert    => inertCensus q
  | .splTail  => q - 1
  | .und      => 1

/-- **NODE H.91.** Every genre-E leaf factor is positive once `3 ≤ q`.  The hypothesis is sharp:
at `q = 2` the `splitEq` factor vanishes (`splitEqCensus 2 = 0`, H.45), so the statement is false
at `2 ≤ q`. -/
theorem leafFactorE_pos {q : ℕ} (hq : 3 ≤ q) (l : LeafE) : 0 < leafFactorE q l := by
  have h1 : 0 < q - 1 := by omega
  have h2 : 0 < q - 2 := by omega
  have hs : 0 < 2 * splitEqCensus q := by
    rw [two_mul_splitEqCensus]; exact Nat.mul_pos h1 h2
  have hi : 0 < 2 * inertCensus q := by
    rw [two_mul_inertCensus]; exact Nat.mul_pos (by omega) h1
  cases l <;> simp only [leafFactorE]
  · exact h1
  · exact Nat.pow_pos h1
  · omega
  · omega
  · exact h1
  · exact Nat.one_pos

/-- **NODE H.91, audit cell.** The `SPLITEQ` leaf is genuinely empty at `q = 2` — the witness that
`leafFactorE_pos` needs `3 ≤ q`. -/
theorem leafFactorE_splitEq_two : leafFactorE 2 .splitEq = 0 := by
  simp [leafFactorE, splitEqCensus]

end Uniformity.Density.Induction

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Induction.leafFactorE
#print axioms Uniformity.Density.Induction.leafFactorE_pos
#print axioms Uniformity.Density.Induction.leafFactorE_splitEq_two

end AxCheck
