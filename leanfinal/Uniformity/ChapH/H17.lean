/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib.Algebra.BigOperators.Ring.Finset
import Uniformity.ChapH.H14
import Uniformity.ChapH.H15

/-!
# Uniformity.ChapH.H17 — the α-transport identity (ghost + child = α-locus)

**Chapter H, NODE H.17** (`blueprint/CHAP-H_general_induction.md` §4). Two clauses of exponent
bookkeeping for the α(k)-transport.

* `ghostSlots_eq`: the ghost-slot total `Σ_{j < m} j·k` is exactly `k · c(m)` — the ghost-fibre
  exponent of `GENIND-2(a)`.
* `ghost_add_child_eq_alphaExp`: the α(k)-slice's exponent decomposes as ghost plus child:
  `k · c(m) + m · W = alphaExp m W k`, where `m · W` is the state exponent of the SAME `(m, d)`
  system at the reduced window (whose `N' − 1 = W`).

DEPENDS: H.13 (`clusterC`), H.14 (`clusterC_eq_sum`), H.15 (`alphaExp`).

SOURCE: `EFF.GENIND.21` (`LEMMA GENIND-2(a)`, verbatim: *"each scaled state has exactly
`Q^{k·c(m)}` ghost-fiber preimages (`Σ_{j<m} jk = k·m(m−1)/2` ghost slots), all key-constant. Hence
the α(k)-slice's history-resolved menu = `(Q−1)·Q^{k·c(m)} × the window-(N−mk) menu`"*), with the
spec's own audit *"Ghost-slot total `Σ_{j=0}^{m−1} jk = k·(m−1)m/2 = k·c(m)` ✓"*; `EFF.GENIND.18`
(`GENIND-1(ii)`'s cardinality check
`#slice = (Q−1)·Q^{m(N−1)−k·m(m+1)/2}/(Q−1) = #D_k = Π_{j<m} Q^{N−1−(m−j)k}`).

**⚠ WHAT IS AND IS NOT TRANSPORTED** (blueprint). This node is the **exponent bookkeeping** of the
α-transport, i.e. exactly the part `EFF.GENIND.17`'s cross-check calls *"consistent with `.21`'s
statement"*. The *bijection* (`GENIND-1(ii)`'s recentering `x ↦ x + ẑπ^k` killing the `m` pinned
digits by the binomial identities) is **geometric and has no node** — the honesty item is H-3. What
chapter H delivers is that the two sides' cardinalities agree *identically in `m, W, k`*, which is
the no-over/undercount check, and that they agree with **no characteristic hypothesis** (the
corpus's own claim: *"the binomial identities … valid in every characteristic"*).

In the transported coordinate `W = N − 1 − m·k` of H.15 the second clause is definitional up to
commutativity; that is the point of the coordinate choice (H.15's ⚠), not a weakening — H.16 is
where the reconciliation with the corpus's subtraction-carrying display `m(N−1) − k·m(m+1)/2` is
paid for.

## Status

Sorry-free, axiom-free (Lean core only).
-/

set_option linter.style.longLine false

namespace Uniformity.Density.Induction

/-- **NODE H.17, ghost fibres.** The ghost-slot total of the α(k)-transport at cluster size `m`:
`Σ_{j < m} j·k = k · c(m)`. This is `GENIND-2(a)`'s fibre exponent — each scaled state has exactly
`Q ^ (k · c(m))` ghost-fibre preimages. -/
theorem ghostSlots_eq (m k : ℕ) : ∑ j ∈ Finset.range m, j * k = k * clusterC m := by
  rw [← Finset.sum_mul, ← clusterC_eq_sum, Nat.mul_comm]

/-- **NODE H.17, the transport identity.** The α(k)-locus exponent is the ghost exponent
`k · c(m)` plus the reduced-window system's own state exponent `m · W` (the same `(m, d)` system
at the window with `N' − 1 = W`). -/
theorem ghost_add_child_eq_alphaExp (m W k : ℕ) :
    k * clusterC m + m * W = alphaExp m W k := by
  rw [alphaExp, Nat.add_comm]

end Uniformity.Density.Induction

/-! ## Numeric gate — the two clauses on a grid (`#guard` fails elaboration on `false`, so this is
a build-time check, not a print-out). Both clauses are characteristic-free, so the grid is over the
shape parameters `m, W, k`, per the blueprint's ⚠. -/

section NumericGate

open Uniformity.Density.Induction

#guard (List.range 7).all fun m => (List.range 7).all fun k =>
  ((List.range m).map (fun j => j * k)).sum == k * clusterC m

#guard (List.range 7).all fun m => (List.range 7).all fun W => (List.range 7).all fun k =>
  k * clusterC m + m * W == alphaExp m W k

/-! The `GENIND-2(a)` display itself at `(m, k) = (4, 2)`: `Σ_{j<4} 2j = 12 = 2 · c(4) = 2 · 6`. -/
#guard ((List.range 4).map (fun j => j * 2)).sum == 12

end NumericGate

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Induction.ghostSlots_eq
#print axioms Uniformity.Density.Induction.ghost_add_child_eq_alphaExp

end AxCheck
