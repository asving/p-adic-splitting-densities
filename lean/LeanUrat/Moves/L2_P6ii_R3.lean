/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.Moves.Defs
import LeanUrat.Moves.DefsT

/-!
# Moves/L2_P6ii_R3 — the unitriangular digit-count factor (D.3(e)(ii), D.11)

`moves_ref`: D.3(e)(ii) unitriangular digit-count factor, MOVES ~2063-2076.

A locus cut by `k` unitriangular digit equations over the `DefsT` `DigitSystem` — each pinned
coordinate a function of strictly earlier ones — has `|α|^{n−k}` solutions.  Proof: the free
(unpinned) coordinates parametrise the whole solution set.  A solution is DETERMINED by its
values on the free coordinates (strong induction: pinned coords are `solve` of earlier ones),
and any free assignment EXTENDS to a solution (`extend`, by well-founded recursion on the
coordinate order).  This bijection gives `Nat.card = |α|^{#free} = |α|^{n − numPinned}`.
-/

set_option linter.style.longLine false

namespace LeanUrat.Moves

variable {α : Type*} {n : ℕ} (D : DigitSystem n α)

/-- Extend a free-coordinate assignment `f` to a full coordinate vector: a free coordinate takes
its `f`-value, a pinned coordinate is `solve` of the (already-built) strictly-earlier values.
Well-founded recursion on the coordinate order. -/
private def extend (f : {i : Fin n // D.pinned i = false} → α) : (i : Fin n) → α
  | i =>
    if h : D.pinned i = false then f ⟨i, h⟩
    else D.solve i (fun j hj => extend f j)
  termination_by i => i.val
  decreasing_by exact hj

private lemma extend_eq (f : {i : Fin n // D.pinned i = false} → α) (i : Fin n) :
    extend D f i =
      if h : D.pinned i = false then f ⟨i, h⟩ else D.solve i (fun j _ => extend D f j) := by
  rw [extend]

/-- The extension of any free assignment is a solution. -/
private lemma extend_isSolution (f : {i : Fin n // D.pinned i = false} → α) :
    D.IsSolution (extend D f) := by
  intro i hi
  rw [extend_eq]
  rw [dif_neg (by simp [hi])]

/-- A free assignment, extended and then restricted to the free coordinates, returns itself. -/
private lemma extend_restrict (f : {i : Fin n // D.pinned i = false} → α)
    (i : {i : Fin n // D.pinned i = false}) : extend D f i.val = f i := by
  rw [extend_eq, dif_pos i.2]

/-- A solution is recovered from its restriction to the free coordinates (strong induction on the
coordinate index `m = i.val`). -/
private lemma restrict_extend (x : Fin n → α) (hx : D.IsSolution x) :
    ∀ (m : ℕ) (i : Fin n), i.val = m → extend D (fun i => x i.val) i = x i := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m IH =>
    intro i hi
    rw [extend_eq]
    by_cases h : D.pinned i = false
    · rw [dif_pos h]
    · rw [dif_neg h]
      have hpin : D.pinned i = true := by
        cases hp : D.pinned i with
        | false => exact absurd hp h
        | true => rfl
      rw [hx i hpin]
      congr 1
      ext j hj
      exact IH j.val (by rw [← hi]; exact hj) j rfl

/-- The solution set is in bijection with free-coordinate assignments. -/
private def solEquiv :
    {x : Fin n → α // D.IsSolution x} ≃ ({i : Fin n // D.pinned i = false} → α) where
  toFun x i := x.val i.val
  invFun f := ⟨extend D f, extend_isSolution D f⟩
  left_inv := by
    rintro ⟨x, hx⟩
    ext i
    simpa using restrict_extend D x hx i.val i rfl
  right_inv := by
    intro f
    ext i
    simpa using extend_restrict D f i

/-- The number of free (unpinned) coordinates is `n − numPinned`. -/
private lemma card_free (D : DigitSystem n α) :
    Nat.card {i : Fin n // D.pinned i = false} = n - D.numPinned := by
  rw [Nat.card_eq_fintype_card]
  have e : {i : Fin n // D.pinned i = false} ≃ {i : Fin n // ¬ (D.pinned i = true)} :=
    Equiv.subtypeEquivRight (fun i => by cases D.pinned i <;> simp)
  rw [Fintype.card_congr e, Fintype.card_subtype_compl, Fintype.card_fin]
  congr 1
  rw [Fintype.card_subtype]
  rfl

theorem L2_P6ii {α : Type*} [Fintype α] (n : ℕ) (D : DigitSystem n α) :
    Nat.card {x : Fin n → α // D.IsSolution x} = (Nat.card α) ^ (n - D.numPinned) := by
  rw [Nat.card_congr (solEquiv D), Nat.card_fun, card_free D]

end LeanUrat.Moves
