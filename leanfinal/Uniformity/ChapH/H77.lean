/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic.Ring

/-!
# Uniformity.ChapH.H77 — the stage-RAM value-group repair (`passPE1 F4`)

**Chapter H, NODE H.77** (`blueprint/CHAP-H_general_induction.md` §11). For `e₁ ≥ 1` and `u` odd,
write `g := gcd(u, e₁)`. Then `g` is odd, and `lcm(e₁, 2e₁ / g) = 2e₁`.

The point of the pair: `v(Y) = u / (2e₁)` **alone** only forces `(2e₁ / g) ∣ e(L)`, which at
`(e₁, u) = (3, 9)` degenerates to `2 ∣ e(L)`. Combined with `(T1)` — which contributes `e₁ ∣ e(L)`
— the value group is pinned at the full `2e₁ ∣ e(L)`, because the two divisors have lcm exactly
`2e₁`. That lcm computation is where the oddness of `g` (inherited from the oddness of `u`) is
consumed: `e₁ = g · m` with `g` odd puts the whole factor `2` into `m`, so `lcm(g·m, 2m) =
m · lcm(g, 2) = m · 2g = 2e₁`. This is the defect `F4` the corpus's `[r2 2026-08-09]` repair names.

DEPENDS: none (mathlib `Nat.gcd_dvd_right`, `Nat.gcd_mul_left`, `Nat.gcd_mul_lcm`,
`Nat.coprime_two_right`).

SOURCE: `EFF.GENHN.38`'s `[r2 2026-08-09]` repair (*"`gcd(u, e₁)` is odd (`u` odd), so
`lcm(e₁, 2e₁/gcd(u, e₁)) = 2e₁` — the value-group argument needs both facts. passPE1 F4"*).

## Status

Sorry-free, axiom-free (Lean core only).
-/

set_option linter.style.longLine false

namespace Uniformity.Density.Induction

/-- A divisor of an odd number is odd: `gcd(u, e)` is odd whenever `u` is. -/
theorem gcd_odd_of_odd {u e : ℕ} (hu : Odd u) : Odd (Nat.gcd u e) := by
  rcases Nat.even_or_odd (Nat.gcd u e) with h | h
  · exact absurd (Nat.odd_iff.mp hu) (by
      have h2 : (2 : ℕ) ∣ u := h.two_dvd.trans (Nat.gcd_dvd_left u e)
      omega)
  · exact h

/-- The stage-RAM value-group repair: with `g := gcd(u, e)` and `u` odd, the two divisibility
constraints `e ∣ e(L)` (from `(T1)`) and `(2e / g) ∣ e(L)` (from `v(Y) = u / (2e)`) combine to
`2e ∣ e(L)`, because `lcm(e, 2e / g) = 2e`. -/
theorem lcm_ram_value_group {u e : ℕ} (he : 1 ≤ e) (hu : Odd u) :
    Nat.lcm e (2 * e / Nat.gcd u e) = 2 * e := by
  have hgodd : Odd (Nat.gcd u e) := gcd_odd_of_odd hu
  have hgdvd : Nat.gcd u e ∣ e := Nat.gcd_dvd_right u e
  have hcop : Nat.gcd (Nat.gcd u e) 2 = 1 := Nat.coprime_two_right.mpr hgodd
  generalize hgdef : Nat.gcd u e = g at hgodd hgdvd hcop ⊢
  -- `e = g * m`, and the whole factor `2` sits in `m` because `g` is odd.
  obtain ⟨m, hm⟩ := hgdvd
  have hgpos : 0 < g := Nat.pos_of_ne_zero (by rintro rfl; simp at hm; omega)
  have hmpos : 0 < m := Nat.pos_of_ne_zero (by rintro rfl; simp at hm; omega)
  have hdiv : 2 * e / g = 2 * m := by
    rw [hm, show 2 * (g * m) = g * (2 * m) from by ring, Nat.mul_div_cancel_left _ hgpos]
  rw [hdiv]
  have hgcd : Nat.gcd e (2 * m) = m := by
    rw [hm, Nat.mul_comm g m, Nat.mul_comm 2 m, Nat.gcd_mul_left, hcop, Nat.mul_one]
  have hkey := Nat.gcd_mul_lcm e (2 * m)
  rw [hgcd] at hkey
  have hfin : m * Nat.lcm e (2 * m) = m * (2 * e) := by rw [hkey, hm]; ring
  exact Nat.eq_of_mul_eq_mul_left hmpos hfin

end Uniformity.Density.Induction

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Induction.gcd_odd_of_odd
#print axioms Uniformity.Density.Induction.lcm_ram_value_group

end AxCheck
