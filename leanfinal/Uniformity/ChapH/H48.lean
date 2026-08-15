/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.Density.Drainage

/-!
# Uniformity.ChapH.H48 — `GENH4.B`'s genre-F law: the odd-`N` power, the even-`N` collapse

**Chapter H, NODE H.48** (`blueprint/CHAP-H_general_induction.md` §7, source `EFF.GENH4.10`,
`THEOREM GENH4.B`'s genre-F law
`UND(k; H₂) = (q²−1)^t (q−1)^r · [ q^{2⌊N/2⌋+2k−1} + 1_{2|N}·(q−1)·q^{N+2k−1} ]`). Two clauses:

* `genh4B_F_odd_exp` — at odd `N = 2ℓ + 1` the bracket is the single `q`-power with exponent
  `2⌊N/2⌋ + 2k − 1 = N + 2k − 2` (the band term is absent).
* `genh4B_F_even_sum` — at even `N` the two displayed terms, the main term `q^{N+2k−1}` and the
  `CAP(F)` boundary band `(q−1)·q^{N+2k−1}`, **sum to the single power `q^{N+2k}`**. The `ℕ`
  disjunct `N + 2k = 0` carries the one degenerate index where `ℕ`-subtraction truncates.

⚠ THE COLLAPSE IS AN OBSERVATION, NOT A CORRECTION. `EFF.GENIND.14`'s `[r2, PE2-m1]` granularity
rider exists *because* the corpus displays a two-term law; the two terms have distinct geometric
meanings (main stratum vs. readable-value/unreadable-residual band at `dv0 = N`), so the corpus's
two-term display must not be "simplified away". This node records only that `(CS-EXACT)`'s
"a FINITE SUM of `q`-powers" is met *both* ways: the sum is itself one power.

Arithmetic sanity (blueprint's fresh audit): `(q,N,k) = (2,8,1)` gives `512 + 512 = 1024 = 2^10`;
`(3,8,1)` gives `19683 + 39366 = 59049 = 3^10` — the `q = 3` cell removes the `1 : 1` doubling
degeneracy of `q = 2`.

DEPENDS: none beyond Lean core + `ring`/`omega`.

## Status

Sorry-free, axiom-free (Lean core only).
-/

set_option linter.style.longLine false

namespace Uniformity.Density.Induction

/-- **H.48 (i).** At odd `N = 2ℓ + 1` the genre-F exponent `2⌊N/2⌋ + 2k − 1` is `N + 2k − 2`. -/
theorem genh4B_F_odd_exp {l k : ℕ} (hk : 1 ≤ k) :
    2 * ((2 * l + 1) / 2) + 2 * k - 1 = (2 * l + 1) + 2 * k - 2 := by
  omega

/-- **H.48 (ii).** The even-`N` two-term law collapses: main term `q^{N+2k−1}` plus band term
`(q−1)·q^{N+2k−1}` is the single power `q^{N+2k}` (outside the degenerate index `N + 2k = 0`). -/
theorem genh4B_F_even_sum (q N k : ℕ) (hq : 1 ≤ q) :
    q ^ (N + 2 * k - 1) + (q - 1) * q ^ (N + 2 * k - 1) = q ^ (N + 2 * k) ∨ N + 2 * k = 0 := by
  rcases Nat.eq_zero_or_pos (N + 2 * k) with h | h
  · exact Or.inr h
  refine Or.inl ?_
  obtain ⟨M, hM⟩ : ∃ M, N + 2 * k = M + 1 := ⟨N + 2 * k - 1, by omega⟩
  have hsub : N + 2 * k - 1 = M := by omega
  have hq' : 1 + (q - 1) = q := by omega
  calc q ^ (N + 2 * k - 1) + (q - 1) * q ^ (N + 2 * k - 1)
      = (1 + (q - 1)) * q ^ M := by rw [hsub]; ring
    _ = q ^ M * q := by rw [hq']; ring
    _ = q ^ (M + 1) := (pow_succ q M).symm
    _ = q ^ (N + 2 * k) := by rw [hM]

end Uniformity.Density.Induction

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Induction.genh4B_F_odd_exp
#print axioms Uniformity.Density.Induction.genh4B_F_even_sum

end AxCheck
