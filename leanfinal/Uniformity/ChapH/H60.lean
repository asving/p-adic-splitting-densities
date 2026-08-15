/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapH.H59
import Mathlib.Algebra.Group.Units.Basic
import Mathlib.Logic.Function.Basic
import Mathlib.Tactic.Ring

/-!
# Uniformity.ChapH.H60 — unit pivots ⟹ bijective (back-substitution)

**Chapter H, NODE H.60** (`blueprint/CHAP-H_general_induction.md` §9, source `EFF.GENIND.156`'s own
proof: *"back-substitution solves any target slot by slot (`input = c⁻¹·(target − earlier-part)`,
`c⁻¹` existing because units of `O/π^w` invert), so the map is ONTO"*, with `EFF.GENIND.157` (`R2.2`,
the enumerated species check showing every ledger row's pivot is the literal unit `1`)).

If `Φ : (Fin n → R) → (Fin n → R)` is triangular with unit pivots (H.59's `TriangularUnitPivot`)
then `Φ` is bijective.

DEPENDS: H.59 · mathlib `IsUnit.mul_left_cancel`, `Function.update_self`, `Function.update_of_ne`,
`Units.mul_inv`, `Fin.eq_of_val_eq`.

## What this node repairs

`EFF.GENIND.155` (`R2.0`, CODEX F1, a CONFIRMED GAP): `GENIND-6(c)`'s onto-with-constant-fibre is
carried by triangularity alone, and **triangularity alone does NOT give surjectivity over a
truncated DVR**. The missing displayed step is the unit-pivot condition. Its negative half — the
sharpness witness showing the hypothesis cannot be dropped — is H.62.

## The recursion decision (blueprint's `[NEEDS-DERIVATION-EXPANSION]`, §16 item 12)

The blueprint flags that the source supplies **no** recursion scheme (in prose there is nothing to
supply) and offers three Lean-specific routes: (a) recurse on `ℕ` with a `tail`-extension and
restrict, (b) `Fin.strongRecOn`, (c) the `n`-induction fallback. **This file picks none of the
three literally; it uses the prefix-induction refinement of (c), and that choice is recorded here.**

Concretely, both halves are induction on a *prefix length* `k : ℕ` over the FIXED index type
`Fin n`, quantified as `∀ i : Fin n, (i : ℕ) < k → …`, and then instantiated at `k := n` where
`i.isLt` discharges the guard:

* injectivity — `tup_eq_below`: `v` and `w` agree below `k`;
* surjectivity — `exists_sol_below`: some `v` solves every slot below `k`, the successor step
  patching slot `k` by `Function.update` with `(pivot k)⁻¹ * (t k − tail k v)`.

This keeps the index type constant (no `Fin.snoc` transport, no dependent-type rewriting) and needs
**no well-founded recursion at all**: `Function.update` at a single slot is the entire
construction, and `tail_lower` is what makes the patch invisible to the already-solved slots.

## Status

Sorry-free, axiom-free (Lean core only).
-/

set_option linter.style.longLine false

namespace Uniformity.Density.Induction

/-- **Back-substitution, injective half.** If `Φ v = Φ w` then `v` and `w` agree on every slot
below `k`, for every prefix length `k`. Slot `i` is cancelled off the pivot after `tail_lower`
identifies the two tails using the strictly-earlier slots supplied by the induction hypothesis. -/
private theorem tup_eq_below {R : Type*} [CommRing R] {n : ℕ}
    {Φ : (Fin n → R) → (Fin n → R)} (T : TriangularUnitPivot Φ) {v w : Fin n → R}
    (h : Φ v = Φ w) : ∀ k : ℕ, ∀ i : Fin n, (i : ℕ) < k → v i = w i := by
  intro k
  induction k with
  | zero => exact fun i hi => absurd hi (Nat.not_lt_zero _)
  | succ k ih =>
    intro i hi
    by_cases hlt : (i : ℕ) < k
    · exact ih i hlt
    · have heq : (i : ℕ) = k := by omega
      -- The two tails at `i` agree: they read only slots `< i`, all of which are `< k`.
      have htail : T.tail i v = T.tail i w :=
        T.tail_lower i v w fun j hj => by
          have hj' : (j : ℕ) < (i : ℕ) := hj
          exact ih j (by omega)
      have hΦ := congrFun h i
      rw [T.apply_eq v i, T.apply_eq w i, htail] at hΦ
      exact (T.pivot_isUnit i).mul_left_cancel (add_right_cancel hΦ)

/-- **Back-substitution, surjective half.** For every prefix length `k` there is an input solving
every target slot below `k`. The successor step patches exactly one slot, `k`, with
`(pivot k)⁻¹ * (t k − tail k v)`; `tail_lower` shows the patch changes neither the tails of the
already-solved slots nor the tail at `k` itself. -/
private theorem exists_sol_below {R : Type*} [CommRing R] {n : ℕ}
    {Φ : (Fin n → R) → (Fin n → R)} (T : TriangularUnitPivot Φ) (t : Fin n → R) :
    ∀ k : ℕ, ∃ v : Fin n → R, ∀ i : Fin n, (i : ℕ) < k → Φ v i = t i := by
  intro k
  induction k with
  | zero => exact ⟨fun _ => 0, fun i hi => absurd hi (Nat.not_lt_zero _)⟩
  | succ k ih =>
    obtain ⟨v, hv⟩ := ih
    by_cases hk : k < n
    · -- Slot `k` exists; solve it, leaving the earlier slots untouched.
      obtain ⟨i₀, hi₀⟩ : ∃ i₀ : Fin n, (i₀ : ℕ) = k := ⟨⟨k, hk⟩, rfl⟩
      obtain ⟨u, hu⟩ := T.pivot_isUnit i₀
      obtain ⟨w, hw⟩ : ∃ w : Fin n → R,
          w = Function.update v i₀ (((u⁻¹ : Rˣ) : R) * (t i₀ - T.tail i₀ v)) := ⟨_, rfl⟩
      have hbelow : ∀ j : Fin n, (j : ℕ) < k → w j = v j := by
        intro j hj
        have hne : j ≠ i₀ := by
          intro hje
          rw [hje, hi₀] at hj
          exact absurd hj (lt_irrefl k)
        rw [hw]
        exact Function.update_of_ne hne _ _
      have hwi₀ : w i₀ = ((u⁻¹ : Rˣ) : R) * (t i₀ - T.tail i₀ v) := by
        rw [hw]
        exact Function.update_self _ _ _
      have htail0 : T.tail i₀ w = T.tail i₀ v :=
        T.tail_lower i₀ w v fun j hj => by
          have hj' : (j : ℕ) < (i₀ : ℕ) := hj
          exact hbelow j (by omega)
      refine ⟨w, ?_⟩
      intro i hi
      by_cases hlt : (i : ℕ) < k
      · -- An already-solved slot: neither its own coordinate nor its tail moved.
        have hwi : w i = v i := hbelow i hlt
        have htaili : T.tail i w = T.tail i v :=
          T.tail_lower i w v fun j hj => by
            have hj' : (j : ℕ) < (i : ℕ) := hj
            exact hbelow j (by omega)
        rw [T.apply_eq w i, hwi, htaili, ← T.apply_eq v i]
        exact hv i hlt
      · -- The freshly patched slot `k`.
        have heq : i = i₀ := Fin.eq_of_val_eq (by omega)
        rw [heq, T.apply_eq w i₀, htail0, hwi₀, ← hu, ← mul_assoc, Units.mul_inv, one_mul]
        ring
    · -- No slot `k`: every index below `k+1` is already below `k`.
      exact ⟨v, fun i hi => hv i (by have := i.isLt; omega)⟩

/-- **Unit pivots ⟹ bijective** (`ANNEX R R2`, the positive half of the repair). A triangular map
with unit pivots on `Fin n → R` is bijective: injectivity by slot-by-slot cancellation against the
unit pivots, surjectivity by back-substitution
`v i = (pivot i)⁻¹ * (t i − tail i v)`. -/
theorem TriangularUnitPivot.bijective {R : Type*} [CommRing R] {n : ℕ}
    {Φ : (Fin n → R) → (Fin n → R)} (T : TriangularUnitPivot Φ) : Function.Bijective Φ := by
  refine ⟨fun v w h => funext fun i => tup_eq_below T h n i i.isLt, fun t => ?_⟩
  obtain ⟨v, hv⟩ := exists_sol_below T t n
  exact ⟨v, funext fun i => hv i i.isLt⟩

end Uniformity.Density.Induction

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Induction.TriangularUnitPivot.bijective

end AxCheck
