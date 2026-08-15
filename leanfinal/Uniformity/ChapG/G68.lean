/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapG.G64

/-!
# Uniformity.ChapG.G68 — `two_mul_hex3R_le`, the `R`-floor bound

**Chapter G, NODE G.68** (`blueprint/CHAP-G_base_cases_menus.md` §9). `2·R(M) ≤ (M+1)·q^(M−1)`
for `M ≥ 1`.

DEPENDS: G.64 only.

**PROOF.** `2R(M) = 2q^(M−1) + 2⌊(M−1)/2⌋(q−1)q^(M−2) ≤ 2q^(M−1) + (M−1)(q−1)q^(M−2)`, and
`(q−1)q^(M−2) ≤ q^(M−1)`, so `2R(M) ≤ (2 + (M−1))q^(M−1) = (M+1)q^(M−1)`. The `M = 1` case is
handled separately since `M - 2 = 0` there (ℕ-truncated), which would break the identity
`q^(M-1) = q * q^(M-2)` used in the general step.

## Status

Sorry-free, axiom-free (Lean core only).
-/

set_option linter.style.longLine false

namespace Uniformity.Density.Menu

theorem two_mul_hex3R_le (q M : ℕ) (hq : 2 ≤ q) (hM : 1 ≤ M) :
    2 * hex3R q M ≤ (M + 1) * q ^ (M - 1) := by
  match M, hM with
  | 1, _ => simp [hex3R]
  | (M' + 2), _ =>
    have h1 : 2 * ((M' + 2 - 1) / 2) ≤ M' + 2 - 1 := by
      have := Nat.div_mul_le_self (M' + 2 - 1) 2
      omega
    have h2 : (q - 1) * q ^ M' ≤ q * q ^ M' := Nat.mul_le_mul_right _ (by omega)
    have hstep : hex3R q (M' + 2) = q ^ (M' + 1) + ((M' + 1) / 2) * ((q - 1) * q ^ M') := by
      simp [hex3R]
    rw [hstep]
    have hsub : M' + 2 - 1 = M' + 1 := by omega
    rw [hsub] at h1
    calc 2 * (q ^ (M' + 1) + (M' + 1) / 2 * ((q - 1) * q ^ M'))
        = 2 * q ^ (M' + 1) + 2 * ((M' + 1) / 2) * ((q - 1) * q ^ M') := by ring
      _ ≤ 2 * q ^ (M' + 1) + (M' + 1) * ((q - 1) * q ^ M') := by
          have := Nat.mul_le_mul_right ((q - 1) * q ^ M') h1
          omega
      _ ≤ 2 * q ^ (M' + 1) + (M' + 1) * (q * q ^ M') := by
          have := Nat.mul_le_mul_left (M' + 1) h2
          omega
      _ = (M' + 2 + 1) * q ^ (M' + 2 - 1) := by
          rw [hsub]; ring

end Uniformity.Density.Menu

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Menu.two_mul_hex3R_le

end AxCheck
