/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring
import Uniformity.ChapH.H18

/-!
# Uniformity.ChapH.H19 — the α-bracket's telescoping step

**Chapter H, NODE H.19** (`blueprint/CHAP-H_general_induction.md` §4). The one-step recursion of
the α-prefix aggregate `alphaBracket` (H.18): for `2 ≤ Q`, `1 ≤ c` and every `μ ≥ 1`,

`alphaBracket Q c (μ + 1) = Q ^ (c + 1) * alphaBracket Q c μ`.

This is the functional equation `B = 1 + A₁·B` of the corpus's generating function read as a
two-term linear recursion; H.20's closed form `b_{m,d}(μ) = (Q−1)·Q^{(c+1)μ−1}` follows from it by
induction.

DEPENDS: H.18 (`alphaBracket`).

SOURCE: `EFF.GENIND.22`'s DERIVATION verbatim: *"one step contributes
`A₁(x) = Σ_{k≥1}(Q−1)Q^{c·k}x^k = (Q−1)Q^c x/(1−Q^c x)`; chains contribute
`A₁/(1−A₁) = (Q−1)Q^c x/(1 − Q^{c+1}x)"* — the denominator `1 − Q^{c+1}x` **is** this node's
one-step recursion, and the spec's own audit re-derives it: *"`(1−Q^c x) − (Q−1)Q^c x = 1 − Q^c
x·(1 + Q − 1) = 1 − Q^{c+1}x` ✓"*.

## The proof, in words

Write `B μ := alphaBracket Q c μ`. Peel the FIRST summand off `B (μ+1)` with
`Finset.sum_range_succ'` (which splits off the `k = 0` term and re-indexes the rest by `k ↦ k+1`):

* the re-indexed tail is `Σ_{k<μ} (Q−1) Q^(c(k+2)) B (μ − 1 − k) = Q^c · Σ_{k<μ} (Q−1) Q^(c(k+1))
  B (μ−1−k) = Q^c · B μ`, using the defining equation of `B μ` (valid because `μ ≥ 1`, which is
  what lets `μ` be written as `ν + 1`);
* the peeled `k = 0` term is `(Q−1) Q^c · B μ`.

Adding, `B (μ+1) = (1 + (Q−1)) · Q^c · B μ = Q^(c+1) · B μ`, where `Q − 1 + 1 = Q` needs `Q ≥ 1`
(supplied by `hQ`). Every `ℕ`-subtraction is guarded: `Q − 1` by `hQ`, and the index shift
`(ν+1) − (k+1) = ν − k` is an identity of truncated subtraction (`omega`).

The blueprint's sanctioned fallback (merge into H.20 and prove the closed form by strong
induction) was NOT needed: the direct re-indexing goes through, so H.19 and H.20 stay separate
nodes as specified. `hc : 1 ≤ c` is part of the frozen contract but is not consumed — the
recursion holds at `c = 0` as well (there `B μ = (Q−1)Q^{μ−1}`), so the hypothesis is a
scope restriction inherited from the corpus, not a proof ingredient.

## Status

Sorry-free, axiom-free (Lean core only).
-/

set_option linter.style.longLine false

namespace Uniformity.Density.Induction

-- `hc` is part of the frozen signature and is not needed by the argument; the linter is silenced
-- rather than the binder renamed (statements are frozen).
set_option linter.unusedVariables false in
/-- **NODE H.19, the telescoping step.** `alphaBracket` satisfies the two-term linear recursion
`b(μ+1) = Q^{c+1} b(μ)` for `μ ≥ 1` — the denominator `1 − Q^{c+1}x` of `GENIND-2(b)`'s generating
function. -/
theorem alphaBracket_succ (Q c : ℕ) (hQ : 2 ≤ Q) (hc : 1 ≤ c) {μ : ℕ} (hμ : 1 ≤ μ) :
    alphaBracket Q c (μ + 1) = Q ^ (c + 1) * alphaBracket Q c μ := by
  -- `μ ≥ 1`: write `μ = ν + 1`, so that the defining equation of `alphaBracket Q c μ` applies.
  obtain ⟨ν, rfl⟩ : ∃ ν, μ = ν + 1 := ⟨μ - 1, by omega⟩
  have hR : alphaBracket Q c (ν + 1)
      = ∑ k ∈ Finset.range (ν + 1), (Q - 1) * Q ^ (c * (k + 1)) * alphaBracket Q c (ν - k) := by
    rw [alphaBracket]
  -- The re-indexed tail of `alphaBracket Q c (ν + 2)` is `Q ^ c` times `alphaBracket Q c (ν + 1)`.
  have htail : ∑ k ∈ Finset.range (ν + 1),
        (Q - 1) * Q ^ (c * (k + 1 + 1)) * alphaBracket Q c (ν + 1 - (k + 1))
      = Q ^ c * alphaBracket Q c (ν + 1) := by
    rw [hR, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    have hidx : ν + 1 - (k + 1) = ν - k := by omega
    have hexp : c * (k + 1 + 1) = c + c * (k + 1) := by ring
    rw [hidx, hexp, pow_add]
    ring
  rw [alphaBracket, Finset.sum_range_succ', htail]
  have hQ1 : Q - 1 + 1 = Q := by omega
  simp only [Nat.sub_zero, Nat.zero_add, Nat.mul_one]
  calc Q ^ c * alphaBracket Q c (ν + 1) + (Q - 1) * Q ^ c * alphaBracket Q c (ν + 1)
      = (Q - 1 + 1) * (Q ^ c * alphaBracket Q c (ν + 1)) := by ring
    _ = Q ^ (c + 1) * alphaBracket Q c (ν + 1) := by rw [hQ1, pow_succ]; ring

end Uniformity.Density.Induction

/-! ## Numeric gate — the recursion against the definition on the stub's grid
(`Q ∈ {2,3,4,5}`, `c ∈ {1,2,3}`, `μ ∈ {1,2,3,4}`), plus the chapter's `q = 3, c = 2` column.
`#guard` fails elaboration when the proposition evaluates to `false`, so these are build-time
checks. Both `Q = 2` and `Q = 3` appear: at `Q = 2` the letter factor `(Q − 1) = 1` disappears, so
a `Q = 2`-only audit cannot see a missing or spurious `(Q − 1)`. -/

section NumericGate

open Uniformity.Density.Induction

#guard [2, 3, 4, 5].all fun Q => [1, 2, 3].all fun c => [1, 2, 3, 4].all fun μ =>
  alphaBracket Q c (μ + 1) == Q ^ (c + 1) * alphaBracket Q c μ

#guard [1, 2, 3, 4].all fun μ => alphaBracket 3 2 (μ + 1) == 3 ^ 3 * alphaBracket 3 2 μ

/-! The step at `μ = 0` is genuinely EXCLUDED (which is why `hμ : 1 ≤ μ` is load-bearing, unlike
`hc`): `b(1) = (Q−1)Q^c` while `Q^{c+1} b(0) = Q^{c+1}`, and these differ for `Q ≥ 2`. -/
#guard [2, 3, 4, 5].all fun Q => [1, 2, 3].all fun c =>
  !(alphaBracket Q c 1 == Q ^ (c + 1) * alphaBracket Q c 0)

end NumericGate

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Induction.alphaBracket_succ

end AxCheck
