/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib.Data.Nat.Basic

/-!
# Uniformity.ChapH.H36 — the entry-mass codimension

**Chapter H, NODE H.36** (`blueprint/CHAP-H_general_induction.md` §6). The relative mass of
`{v(a₀) ≥ D}` inside a cluster system's state space is `Q^(−(D−1))`: in exponent form the pinned
digit count is `d*(D−1)` out of `d*(N−1)` at coordinate `0`, so the codimension is `D − 1` in
`Q`-digits. Stated subtraction-free (an additive identity in `ℕ`, no division, no truncation
hazard): for `1 ≤ D ≤ N`,

  `d * (D − 1) + d * (N − D) = d * (N − 1)`.

DEPENDS: none (pure `ℕ` arithmetic).

SOURCE: `EFF.GENIND.152` (`GENIND-C1`(i)): *"the `j = 0` term of the min gives `D_l ≤ v(a₀)`, so
the genre lies inside `{v(a₀) ≥ D_l}`, whose relative mass is exactly `Q^{−(D_l−1)}` (π-levels
`1..D_l−1` of `a₀` pinned to zero — `d·(D_l−1)` q-digits; level 0 is pinned in every state)"*.

⚠ SCOPE. The *geometric* containment `D_l = min_j(v(a_j) + j·k_l) ≤ v(a₀)` is a property of the
polygon's content and is NOT proved here (blueprint honesty item H-3); it enters H.67/H.72 as a
hypothesis on the schema. This node proves only the codimension arithmetic once the containment
is granted.

## Status

Sorry-free, axiom-free (Lean core only).
-/

namespace Uniformity.Density.Induction

/-- **NODE H.36.** The entry-mass codimension, subtraction-free: the `d*(D−1)` digits pinned by
`v(a₀) ≥ D` together with the `d*(N−D)` digits left free at coordinate `0` exhaust the
`d*(N−1)` digits of that coordinate. -/
theorem entry_codim (d D N : ℕ) (hD : 1 ≤ D) (hDN : D ≤ N) :
    d * (D - 1) + d * (N - D) = d * (N - 1) := by
  rw [← Nat.mul_add]
  congr 1
  omega

end Uniformity.Density.Induction

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Induction.entry_codim

end AxCheck
