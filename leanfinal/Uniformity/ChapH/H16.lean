/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring
import Uniformity.ChapH.H14
import Uniformity.ChapH.H15

/-!
# Uniformity.ChapH.H16 — the α slot count and the closed form

**Chapter H, NODE H.16** (`blueprint/CHAP-H_general_induction.md` §4). Two clauses tying
`alphaExp` (H.15) to the corpus's displayed α-locus exponent.

* `sum_alphaSlots` — the slot count `Σ_{j<m} (W + j·k) = alphaExp m W k`. In the transported
  coordinate `W = N − 1 − mk` the `j`-th summand of the corpus's S2.2 slot count
  `Σ_j (N−1−(m−j)k)` is exactly `W + jk`, so this clause IS the corpus's free-digit sum.
* `two_mul_alphaExp_add` — the closed-form reconciliation, subtraction-free:
  `2·alphaExp m W k + k·(m(m+1)) = 2·(m·(W + m·k))`. Dividing by `2` and substituting
  `N − 1 = W + m·k`, this is the corpus's `m(N−1) − k·m(m+1)/2`.

DEPENDS: H.13 (`clusterC`), H.14 (`clusterC_eq_sum`, `two_mul_clusterC`), H.15 (`alphaExp`).

SOURCE: `EFF.GENIND.17`'s own ARITHMETIC AUDIT, verbatim: *"the free-digit sum is
`Σ_{j=0}^{m−1} (N−1−(m−j)k) = m(N−1) − k·Σ_{j=0}^{m−1}(m−j) = m(N−1) − k·(m + (m−1) + … + 1)
= m(N−1) − k·m(m+1)/2` ✓ — the displayed exponent, recomputed fresh."*

**ARITHMETIC AUDIT (recomputed fresh, at two `Q`)** (blueprint). `m = 2`, `k = 1`, `N = 6`, so
`W = N−1−mk = 3`: `alphaExp = 2·3 + 1·1 = 7`, and the corpus's form is
`m(N−1) − k·m(m+1)/2 = 2·5 − 1·3 = 7` ✓. Against `EFF.GENIND.99`'s preregistered spot
`ALPHA(1) = 1,024` at `(q,N) = (2,6)`, `m = 4`, `d = 1`: `W = 6−1−4 = 1` and
`alphaExp = 4·1 + 1·6 = 10`, so the locus is `(Q−1)Q^{10} = 2^{10} = 1,024` ✓ exactly the
preregistered value. At `q = 3`, `(N, m, k) = (6, 3, 1)`: `W = 2`, `alphaExp = 3·2 + 1·3 = 9`,
locus `2·3^9 = 39,366`; the corpus's form gives `3·5 − 1·6 = 9` ✓ — agreement at `q = 3` as well
as at `q = 2`. (At `q = 3`, `(N, m, k) = (4, 4, 1)` the corpus records ALPHA ABSENT because α needs
`mk ≤ N−1`, i.e. `4 ≤ 3` ✗ — the admissibility bound, not the exponent, is what excludes it, and
`alphaExp` is never evaluated there.)

**⚠ WHY CLAUSE (ii) IS STATED DOUBLED** (blueprint, the subtraction-free discipline): the corpus's
display carries two `ℕ`-subtractions that truncate silently below the admissibility bound
`mk ≤ N−1`. Multiplying through by `2` and moving the `k·m(m+1)/2` term to the left removes both,
so the identity is an honest `ℕ` statement with no floor and no truncation.

## Status

Sorry-free, axiom-free (Lean core only).
-/

set_option linter.style.longLine false

namespace Uniformity.Density.Induction

/-- **NODE H.16(i).** The α slot count: `Σ_{j<m} (W + j·k) = alphaExp m W k`. The constant part
contributes `m·W` and the ghost part `(Σ_{j<m} j)·k = c(m)·k` by H.14(ii). -/
theorem sum_alphaSlots (m W k : ℕ) :
    ∑ j ∈ Finset.range m, (W + j * k) = alphaExp m W k := by
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, Nat.nsmul_eq_mul,
    ← Finset.sum_mul, ← clusterC_eq_sum, alphaExp]
  ring


/-- **NODE H.16(ii).** The closed-form reconciliation, subtraction-free:
`2·alphaExp m W k + k·(m(m+1)) = 2·(m·(W + m·k))`. With `N − 1 = W + m·k` and division by `2`
this is the corpus's displayed exponent `m(N−1) − k·m(m+1)/2`. -/
theorem two_mul_alphaExp_add (m W k : ℕ) :
    2 * alphaExp m W k + k * (m * (m + 1)) = 2 * (m * (W + m * k)) := by
  have h2 := two_mul_clusterC m
  cases m with
  | zero => simp [alphaExp, clusterC]
  | succ n =>
    rw [Nat.add_sub_cancel] at h2
    have hc : 2 * (k * clusterC (n + 1)) = k * ((n + 1) * n) := by
      rw [← h2]; ring
    simp only [alphaExp]
    calc 2 * ((n + 1) * W + k * clusterC (n + 1)) + k * ((n + 1) * (n + 1 + 1))
        = 2 * ((n + 1) * W) + 2 * (k * clusterC (n + 1)) + k * ((n + 1) * (n + 1 + 1)) := by
          ring
      _ = 2 * ((n + 1) * W) + k * ((n + 1) * n) + k * ((n + 1) * (n + 1 + 1)) := by rw [hc]
      _ = 2 * ((n + 1) * (W + (n + 1) * k)) := by ring

end Uniformity.Density.Induction

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Induction.sum_alphaSlots
#print axioms Uniformity.Density.Induction.two_mul_alphaExp_add

end AxCheck
