/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity

/-!
# Uniformity.ChapH.H35 — `pow_sub_dominance`

**Chapter H, NODE H.35** (`blueprint/CHAP-H_general_induction.md` §6, ENV-H1). The
polynomial-dominance step: for `1 ≤ m ≤ N` and `1 ≤ B`, in `ℕ`,

`(N − m) ^ B + m * (N − m) ^ (B − 1) ≤ N ^ B`.

This is the usable form of the corpus's "`N^B − (N−m)^B` has positive leading coefficient
`m·B·N^{B−1}`": the gap dominates `m·(N−m)^(B−1)`, which is what the `K`-choice needs.

DEPENDS: none (mathlib `Nat.pow_le_pow_left`, `mul_le_mul_right'`).

**SOURCE.** `EFF.GENIND.153` (`GENIND.C′`'s `K`-choice: "`K` large enough that
`K·[N^B − (N−m)^B]` dominates the head + β coefficients (a degree-`(B−1)` polynomial inequality,
satisfiable since `N^B − (N−m)^B` has positive leading coefficient `m·B·N^{B−1}`)").
`EFF.GENIND.153`'s disposition is PROOF-ONLY: no battery row exercises the induction.

**PROOF.** Shorter than the blueprint's binomial route, and it needs only the *lowest* two
binomial terms in disguise. Write `B = k + 1` and `A := N − m`, so `N = A + m`
(`Nat.sub_add_cancel`). Then
`A^(k+1) + m * A^k = A^k * (A + m) ≤ (A + m)^k * (A + m) = (A + m)^(k+1)`,
the middle step by `Nat.pow_le_pow_left (A ≤ A + m)`. No subtraction survives, and `1 ≤ B` enters
only as the destructuring `B = k + 1`.

## Status

Sorry-free, axiom-free (Lean core only).
-/

set_option linter.style.longLine false
-- The signature is frozen by the blueprint/stub gate; `hm` is carried but not consumed by this
-- proof (the bound holds for `m = 0` too), so the unused-variable linter is off.
set_option linter.unusedVariables false

namespace Uniformity.Density.Induction

/-- The polynomial-dominance step: the gap `N^B − (N−m)^B` dominates `m * (N−m)^(B−1)`, stated
subtraction-free as `(N − m)^B + m * (N − m)^(B−1) ≤ N^B`. NODE H.35. -/
theorem pow_sub_dominance {N m B : ℕ} (hm : 1 ≤ m) (hmN : m ≤ N) (hB : 1 ≤ B) :
    (N - m) ^ B + m * (N - m) ^ (B - 1) ≤ N ^ B := by
  obtain ⟨k, rfl⟩ : ∃ k, B = k + 1 := ⟨B - 1, by omega⟩
  have key : ∀ A : ℕ, A ^ (k + 1) + m * A ^ k ≤ (A + m) ^ (k + 1) := by
    intro A
    have h1 : A ^ k ≤ (A + m) ^ k := Nat.pow_le_pow_left (Nat.le_add_right A m) k
    calc A ^ (k + 1) + m * A ^ k = A ^ k * (A + m) := by ring
      _ ≤ (A + m) ^ k * (A + m) := Nat.mul_le_mul h1 le_rfl
      _ = (A + m) ^ (k + 1) := by ring
  have hkey := key (N - m)
  rw [Nat.sub_add_cancel hmN] at hkey
  simpa using hkey

section AxCheck
#print axioms Uniformity.Density.Induction.pow_sub_dominance
end AxCheck

end Uniformity.Density.Induction
