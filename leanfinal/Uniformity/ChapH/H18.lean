/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib.Algebra.BigOperators.Intervals

/-!
# Uniformity.ChapH.H18 — `alphaBracket`, the α-prefix aggregate `b_{m,d}(μ)`

**Chapter H, NODE H.18** (`blueprint/CHAP-H_general_induction.md` §4). The α-bracket, defined by
its convolution ("peel the first step") recursion: `alphaBracket Q c 0 = 1` and, for `μ ≥ 1`,

`alphaBracket Q c μ = Σ_{k = 1}^{μ} (Q − 1) * Q ^ (c * k) * alphaBracket Q c (μ − k)`,

which is the sum over all finite sequences `(k₁, …, k_r)` with `kᵢ ≥ 1` and `Σ kᵢ = μ` of
`Π_i (Q − 1) Q ^ (c kᵢ)`.

Definitional, no proof obligation. DEPENDS: none.

SOURCE: `EFF.GENIND.22` (`LEMMA GENIND-2(b)`, verbatim: *"`Σ` over all finite sequences
`(k₁, …, k_r)`, `k_i ≥ 1`, `Σk_i = μ`, of `Π_i (Q−1)Q^{c(m)·k_i} = (Q−1)·Q^{(c(m)+1)μ−1} =:
b_{m,d}(μ)`"*), and its proof's generating function *"one step contributes
`A₁(x) = Σ_{k≥1}(Q−1)Q^{c·k}x^k`; chains contribute `A₁/(1−A₁)`"* — the peel-the-first-step
recursion is that generating function's functional equation `B = 1 + A₁·B`.

**⚠ WHY A RECURSION AND NOT A LITERAL COMPOSITION SUM** (blueprint). A `Finset` of compositions in
Lean is a `Finset (List ℕ)` with two side conditions and no mathlib API; the peel recursion is the
same object (`B = 1 + A₁ B`) and gives H.20's closed form by induction in four lines. The corpus's
own proof is the generating-function identity, i.e. the recursion — so the recursion, not the sum,
is the faithful transcription. **A downstream agent must not "improve" this into a
`Finset (Composition μ)` statement**: that changes the contract and the closed-form proof.

**Repair record [A-H.1/D2].** The committed SIGNATURE displayed the body with no `decreasing_by`
line, so it did not elaborate. The termination goal `μ - k < μ + 1` is unconditionally true (`ℕ`
subtraction only shrinks), but the equation compiler does not discharge it by itself; the missing
`decreasing_by omega` is the whole repair, and it is semantics-free.

## Status

Sorry-free, axiom-free (Lean core only).
-/

set_option linter.style.longLine false

namespace Uniformity.Density.Induction

/-- The α-prefix aggregate `b_{m,d}(μ)`, defined by the composition recursion (peel the first
step).  `alphaBracket Q c μ = Σ over compositions (k₁,…,k_r) of μ with kᵢ ≥ 1 of
Π (Q−1)Q^{c kᵢ}`, and `alphaBracket Q c 0 = 1`. -/
def alphaBracket (Q c : ℕ) : ℕ → ℕ
  | 0 => 1
  | (μ + 1) => ∑ k ∈ Finset.range (μ + 1),
      (Q - 1) * Q ^ (c * (k + 1)) * alphaBracket Q c (μ - k)
  decreasing_by omega

end Uniformity.Density.Induction

/-! ## Numeric sanity (the blueprint's `(CS-2)` certificate column, H.21's values).
`#guard` fails elaboration if the proposition evaluates to `false`, so these are build-time gates,
not print-outs. Two primes minimum (`q = 2` and `q = 3`, plus `Q = 4`), per the chapter's
two-column rule. -/

section NumericGate

open Uniformity.Density.Induction

#guard alphaBracket 4 1 2 == 192
#guard alphaBracket 3 1 2 == 54
#guard alphaBracket 2 1 3 == 32

end NumericGate

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Induction.alphaBracket

end AxCheck
