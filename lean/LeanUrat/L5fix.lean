/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib

/-!
# LeanUrat.L5fix — termination data: depth bound + self-loop pivot (`notes/HUMAN_PROOF.md §9`)

**Cleaned 2026-06-15.** Removed `shapeMenu_finite`, which was vacuously weak: it only asserted that
the finite menu contains *some* shape of the same total degree `n` (satisfied by any singleton
menu), saying nothing about the occurring shapes lying in the menu, nor about `p`-independence. The
genuine content — that the menu of cluster-tree shapes at degree `n` is finite, `p`-independent, and
of ramifying depth `≤ descentBound n p` (GMN termination Thm 4.18 / Cor 4.19) — is a cited fact not
in mathlib; it enters the Goal through the `DensityFoundation.shapes : ... → Finset _` field (which
*is* finite by construction). A future module may state the finiteness-of-occurring-shapes and the
`p`-uniform bound as a real theorem over an explicit OM model.

What remains is genuinely proved: the corrected depth-bound definition and the self-loop pivot
positivity (which guarantees the geometric resummation `1/(1 - q^{-w})` converges with no real-`q`
pole for `q ≥ 2`).
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false

namespace LeanUrat.L5fix

/-- The `p`-uniform depth envelope `B(n,p) = max_{d ≤ n} [(d-1) + d·v_p(d)]` (the CORRECTED
per-leaf-degree bound; the earlier `(n-1)+n·v_p(n)` was wrong for proper leaves). `Nat.factorization
d p = v_p(d)`. -/
def descentBound (n p : ℕ) : ℕ :=
  (Finset.range (n + 1)).sup (fun d => (d - 1) + d * (Nat.factorization d p))

/-- The size-`e` self-loop exponent `e(e+1)/2 - 1` (R1's `w(e)`; `2,5,9,14` for `e = 2,3,4,5`). -/
def selfLoopExponent (e : ℕ) : ℕ := e * (e + 1) / 2 - 1

/-- **Self-loop pivot positivity (PROVED).** For `e ≥ 2` and `q ≥ 2`, the pivot
`1 - q^{-(e(e+1)/2-1)} > 0`, so the geometric self-loop resummation `1/(1 - q^{-w})` converges (no
real pole at `q ≥ 2`). -/
theorem selfLoop_geometric (e q : ℕ) (he : 2 ≤ e) (hq : 2 ≤ q) :
    (0 : ℚ) < 1 - ((q : ℚ) ^ selfLoopExponent e)⁻¹ := by
  have hexp : 1 ≤ selfLoopExponent e := by
    have h6 : 6 ≤ e * (e + 1) := by nlinarith
    unfold selfLoopExponent; omega
  have hgt : (1 : ℚ) < (q : ℚ) ^ selfLoopExponent e :=
    one_lt_pow₀ (by exact_mod_cast (by omega : 1 < q)) (by omega)
  have : ((q : ℚ) ^ selfLoopExponent e)⁻¹ < 1 := by simpa using inv_lt_one_of_one_lt₀ hgt
  linarith

end LeanUrat.L5fix
