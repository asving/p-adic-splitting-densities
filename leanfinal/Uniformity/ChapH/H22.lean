/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Tactic.Ring

/-!
# Uniformity.ChapH.H22 — the DRAIN locus exponent, and the window-1 event inventory

**Chapter H, NODE H.22** (`blueprint/CHAP-H_general_induction.md` §4). Two clauses of pure
exponent arithmetic.

* `drain_codim`: `DRAIN`'s locus exponent is `d (m − 1)(N − 1)`, and against the total state
  exponent `d m (N − 1)` its codimension is exactly `d (N − 1)`. Stated subtraction-free as
  `d * (m - 1) * (N - 1) + d * (N - 1) = d * m * (N - 1)` for `1 ≤ m`, so that no `ℕ`-truncation
  can hide in the statement.
* `window_one_exponents`: the `N = 1` boundary. There the state count is `q ^ (d m (1 - 1)) = 1`,
  the DRAIN locus `q ^ (d (m - 1)(1 - 1)) = 1` is therefore the whole space, and α — which needs
  `m k ≤ N − 1 = 0` with `k ≥ 1` — is uninhabited. (`DEC`/`β`/`CS` all need a polygon, i.e.
  `v(a₀) < N = 1`, likewise impossible.) So of the five events exactly one is inhabited; the two
  exponent identities and the α-impossibility are the Lean content.

DEPENDS: none.

**Why the boundary case is a node and not a remark** (blueprint ⚠, the G.31 lesson): `ANNEX R R3`
was filed as a CONFIRMED GAP (`EFF.GENIND.159`, a scope leak) precisely because window-1 systems
arise as transport targets while the `S1` convention said `N ≥ 2`. Chapter H consumes the window-1
boundary at H.24 (`uTwo 1 = 1`), H.71 (`GENIND.C′`'s `N ≥ 1`) and H.71's truncation base case
(`T = 1`); landing it here keeps DEPENDS-completeness at every one of them.

SOURCE: `EFF.GENIND.08` (`GENIND.A`(I): *"DRAIN: `v(a₀) ≥ N`; locus `q^{d(m−1)(N−1)}`"*);
`EFF.GENIND.160` (`ANNEX R R3.1`, the window-1 convention rider).

## Status

Sorry-free, axiom-free (Lean core only).
-/

set_option linter.style.longLine false

namespace Uniformity.Density.Induction

/-- **DRAIN's codimension.** Against the total state exponent `d * m * (N - 1)`, the DRAIN locus
exponent `d * (m - 1) * (N - 1)` has codimension exactly `d * (N - 1)`. Written additively so the
identity is free of `ℕ`-subtraction on the right-hand side. -/
theorem drain_codim (d m N : ℕ) (hm : 1 ≤ m) :
    d * (m - 1) * (N - 1) + d * (N - 1) = d * m * (N - 1) := by
  obtain ⟨m', rfl⟩ := Nat.exists_eq_add_of_le hm
  have h : 1 + m' - 1 = m' := by omega
  rw [h]
  ring

/-- **The window-1 inventory.** At `N = 1`: the total state exponent vanishes (one state), the
DRAIN locus exponent vanishes too (DRAIN is the whole space), and no α-event exists, since α
requires a step `k ≥ 1` with `m * k ≤ N - 1 = 0`. -/
theorem window_one_exponents (d m : ℕ) (hm : 1 ≤ m) :
    d * m * (1 - 1) = 0 ∧ d * (m - 1) * (1 - 1) = 0 ∧ ¬ ∃ k, 1 ≤ k ∧ m * k ≤ 0 := by
  refine ⟨by simp, by simp, ?_⟩
  rintro ⟨k, hk, hmk⟩
  exact absurd hmk (Nat.not_le.mpr (Nat.mul_pos hm hk))

end Uniformity.Density.Induction

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Induction.drain_codim
#print axioms Uniformity.Density.Induction.window_one_exponents

end AxCheck
