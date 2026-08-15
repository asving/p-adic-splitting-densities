/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.Density.Drainage

/-!
# Uniformity.ChapH.H45 — `splitEqCensus`, `inertCensus`: the residual censuses over the stage field

**Chapter H, NODE H.45** (`blueprint/CHAP-H_general_induction.md`, source `EFF.GENH4.07`,
`EFF.GENIND.47`). Over a `Q`-element stage field: the unordered pairs of *distinct nonzero*
elements number `(Q−1)(Q−2)/2` (the `SPLITEQ` residual census), and the monic irreducible
quadratics number `Q(Q−1)/2` (the `INERT` residual census). Both are landed here in
**subtraction-free** form, which is what a ℕ-valued census must be checked in:

    2 * splitEqCensus Q = (Q − 1) * (Q − 2)      2 * inertCensus Q = Q * (Q − 1)

**⚠ THE `SPLITEQ` CENSUS IS THE ORDERED-PAIR-HALVED ONE, AND `Q = 2` IS DEGENERATE.** At
`Q = 2` there is exactly one nonzero element, so `splitEqCensus 2 = 0` — the genre is empty
and the ℕ-truncation is *correct*, not an artifact; the `Q = 3, 4` cells are the ones that
test the formula (`1`, `3`). This is the same trap as chapter G's `q(q−1)/2` vs
`(q−1)(q−2)/2` reconciliation (G.39 and AMENDMENT §A-3): the two censuses count over
different domains — chapter G indexes **all** pairs `(b₀, b₁)`, chapter H only the stage
letters in `K^×` — and must not be conflated.

DEPENDS: none · mathlib `Nat.even_mul_succ_self` (parity of consecutive products).

## Status

Sorry-free, axiom-free (Lean core only).
-/

set_option linter.style.longLine false

namespace Uniformity.Density.Induction

/-- `#{unordered pairs of distinct nonzero elements}` over a `Q`-element field — the `SPLITEQ`
residual census. -/
def splitEqCensus (Q : ℕ) : ℕ := (Q - 1) * (Q - 2) / 2

/-- `#{monic irreducible quadratics}` over a `Q`-element field — the `INERT` residual census. -/
def inertCensus (Q : ℕ) : ℕ := Q * (Q - 1) / 2

/-- The `SPLITEQ` census in subtraction-free form: the halving is exact, because `(Q−1)(Q−2)`
is a product of consecutive naturals (and both sides truncate to `0` at `Q ≤ 1`). -/
theorem two_mul_splitEqCensus (Q : ℕ) : 2 * splitEqCensus Q = (Q - 1) * (Q - 2) := by
  unfold splitEqCensus
  match Q with
  | 0 => rfl
  | 1 => rfl
  | (m + 2) =>
    have h : Even ((m + 1) * m) := by
      rw [Nat.mul_comm]; exact Nat.even_mul_succ_self m
    obtain ⟨k, hk⟩ := h
    have e1 : m + 2 - 1 = m + 1 := by omega
    have e2 : m + 2 - 2 = m := by omega
    rw [e1, e2, hk]
    omega

/-- The `INERT` census in subtraction-free form: `Q(Q−1)` is a product of consecutive
naturals, so the halving is exact. -/
theorem two_mul_inertCensus (Q : ℕ) : 2 * inertCensus Q = Q * (Q - 1) := by
  unfold inertCensus
  match Q with
  | 0 => rfl
  | (m + 1) =>
    have h : Even ((m + 1) * m) := by
      rw [Nat.mul_comm]; exact Nat.even_mul_succ_self m
    obtain ⟨k, hk⟩ := h
    have e1 : m + 1 - 1 = m := by omega
    rw [e1, hk]
    omega

end Uniformity.Density.Induction

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Induction.two_mul_splitEqCensus
#print axioms Uniformity.Density.Induction.two_mul_inertCensus

end AxCheck
