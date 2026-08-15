/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapH.H51

/-!
# Uniformity.ChapH.H52 — the slot-min has no cross-class ties

**Chapter H, NODE H.52** (`blueprint/CHAP-H_general_induction.md` §8, the slot/lift layer).

Fix `h` and `e` coprime and a family of candidate slot heights `m_i = e * v_i + i * h` indexed by
the residue classes `i < e` (one slot per class). Two such heights coincide only if the slots
coincide:

* `slot_height_injective` — `e * v + i * h = e * v' + i' * h` with `i, i' < e` forces `i = i'`
  **and** `v = v'`;
* `slot_min_unique` — hence the minimum of the family is attained at a **unique** index, which is
  what upgrades the ultrametric inequality `dv(A(θ)) ≥ min_i m_i` to an **equality**.

DEPENDS: H.51 (`class_sep`, the coprime class separation mod `e`) · mathlib `Nat.mul_add_mod`,
`Nat.eq_of_mul_eq_mul_left`.

**SOURCE.** `EFF.GENHN.27`'s DERIVATION, verbatim: *"Ultrametric equality when all candidate values
are attained at distinct heights; distinct classes never tie (`dv ≡ ih mod e₁`)"*; `EFF.GENH4.19`
(`LEMMA GENH4-2`) is the `e₁ = 2` instance by parity: *"the min is uniquely attained (`2v(a)+h`
odd, `2v(b)` even: distinct parities, no ties)"*.

**⚠ SCOPE FENCE.** This node is the *across*-class separation only. The *within*-class tie (the
`f₁ ≥ 2` branch, killed by residue-field independence) is NODE H.53 and is deliberately not
touched here; at `f₁ = 1` there is no within-class branch at all, which is why the `e₁ = 2` parity
argument is complete there.

**PROOF.** (1) `slot_height_injective`: reduce the hypothesis mod `e` — `Nat.mul_add_mod` kills
both `e * v` and `e * v'` terms, leaving `i * h % e = i' * h % e`, so `i = i'` by H.51's
`class_sep`; substituting back and cancelling `e > 0` (which follows from `i < e`) gives `v = v'`.
(2) `slot_min_unique`: the first component of (1). Its `0 < e` hypothesis is redundant given
`i < e` and is kept only to match the frozen signature.

## Status

Sorry-free, axiom-free (Lean core only).
-/

set_option linter.style.longLine false
set_option linter.unusedVariables false

namespace Uniformity.Density.Induction

/-- **H.52 (a) — slot heights are injective.** With `h` coprime to `e`, the assignment
`(i, v) ↦ e * v + i * h` is injective on `i < e`: no two distinct residue classes (and no two
distinct heights within one class index) ever tie. -/
theorem slot_height_injective {h e : ℕ} (hcop : Nat.Coprime h e) {i i' v v' : ℕ}
    (hi : i < e) (hi' : i' < e) (heq : e * v + i * h = e * v' + i' * h) :
    i = i' ∧ v = v' := by
  have he : 0 < e := Nat.lt_of_le_of_lt (Nat.zero_le i) hi
  have hmod : i * h % e = i' * h % e := by
    have h1 : (e * v + i * h) % e = (e * v' + i' * h) % e := by rw [heq]
    rwa [Nat.mul_add_mod, Nat.mul_add_mod] at h1
  have hii : i = i' := class_sep hcop hi hi' hmod
  subst hii
  refine ⟨rfl, ?_⟩
  have hmul : e * v = e * v' := by omega
  exact Nat.eq_of_mul_eq_mul_left he hmul

/-- **H.52 (b) — the slot-min is attained at a unique index.** If two candidate slot heights of
the family `i ↦ e * v i + i * h` agree (in particular if both realise the minimum) then their
indices agree. -/
theorem slot_min_unique {h e : ℕ} (hcop : Nat.Coprime h e) (he : 0 < e)
    (v : ℕ → ℕ) {i i' : ℕ} (hi : i < e) (hi' : i' < e)
    (hmin : e * v i + i * h = e * v i' + i' * h) : i = i' :=
  (slot_height_injective hcop hi hi' hmin).1

section AxCheck
#print axioms Uniformity.Density.Induction.slot_height_injective
#print axioms Uniformity.Density.Induction.slot_min_unique
end AxCheck

end Uniformity.Density.Induction
