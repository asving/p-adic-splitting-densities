/-
Unit C0.pinWelldef — moves_ref: §C.0.5 PIN-WELLDEF (cardinality half)
Same solution set ⟹ same mass (= p^{m−numPinned}); p ≥ 2 (from Fact p.Prime) and
numPinned ≤ m pin the exponent via Nat.pow injectivity.
The counting factor (dep C0.digitSystemMass ≡ Moves.L2_P6ii) is reproduced here as private
helpers, since this unit imports only MovesC.Defs.
-/
import LeanUrat.MovesC.Defs

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false

namespace LeanUrat.MovesC

open LeanUrat.Moves

/-! ## The unitriangular digit-count factor (reproduced from `Moves.L2_P6ii`) -/

section Counting

variable {α : Type*} {n : ℕ} (D : DigitSystem n α)

/-- Extend a free-coordinate assignment `f` to a full coordinate vector: a free coordinate takes
its `f`-value, a pinned coordinate is `solve` of the (already-built) strictly-earlier values. -/
private def extendC (f : {i : Fin n // D.pinned i = false} → α) : (i : Fin n) → α
  | i =>
    if h : D.pinned i = false then f ⟨i, h⟩
    else D.solve i (fun j hj => extendC f j)
  termination_by i => i.val
  decreasing_by exact hj

private lemma extendC_eq (f : {i : Fin n // D.pinned i = false} → α) (i : Fin n) :
    extendC D f i =
      if h : D.pinned i = false then f ⟨i, h⟩ else D.solve i (fun j _ => extendC D f j) := by
  rw [extendC]

private lemma extendC_isSolution (f : {i : Fin n // D.pinned i = false} → α) :
    D.IsSolution (extendC D f) := by
  intro i hi
  rw [extendC_eq, dif_neg (by simp [hi])]

private lemma extendC_restrict (f : {i : Fin n // D.pinned i = false} → α)
    (i : {i : Fin n // D.pinned i = false}) : extendC D f i.val = f i := by
  rw [extendC_eq, dif_pos i.2]

private lemma restrict_extendC (x : Fin n → α) (hx : D.IsSolution x) :
    ∀ (mm : ℕ) (i : Fin n), i.val = mm → extendC D (fun i => x i.val) i = x i := by
  intro mm
  induction mm using Nat.strong_induction_on with
  | _ mm IH =>
    intro i hi
    rw [extendC_eq]
    by_cases h : D.pinned i = false
    · rw [dif_pos h]
    · rw [dif_neg h]
      have hpin : D.pinned i = true := Bool.eq_true_of_not_eq_false h
      rw [hx i hpin]
      congr 1
      ext j hj
      exact IH j.val (by rw [← hi]; exact hj) j rfl

/-- The solution set is in bijection with free-coordinate assignments. -/
private def solEquivC :
    {x : Fin n → α // D.IsSolution x} ≃ ({i : Fin n // D.pinned i = false} → α) where
  toFun x i := x.val i.val
  invFun f := ⟨extendC D f, extendC_isSolution D f⟩
  left_inv := by
    rintro ⟨x, hx⟩
    ext i
    simpa using restrict_extendC D x hx i.val i rfl
  right_inv := by
    intro f
    ext i
    simpa using extendC_restrict D f i

/-- The number of free (unpinned) coordinates is `n − numPinned`. -/
private lemma card_freeC (D : DigitSystem n α) :
    Nat.card {i : Fin n // D.pinned i = false} = n - D.numPinned := by
  rw [Nat.card_eq_fintype_card]
  have e : {i : Fin n // D.pinned i = false} ≃ {i : Fin n // ¬ (D.pinned i = true)} :=
    Equiv.subtypeEquivRight (fun i => by cases D.pinned i <;> simp)
  rw [Fintype.card_congr e, Fintype.card_subtype_compl, Fintype.card_fin]
  congr 1
  rw [Fintype.card_subtype]
  rfl

/-- The unitriangular digit count: `|α|^{n − numPinned}` solutions. -/
private theorem massC {α : Type*} [Fintype α] (n : ℕ) (D : DigitSystem n α) :
    Nat.card {x : Fin n → α // D.IsSolution x} = (Nat.card α) ^ (n - D.numPinned) := by
  rw [Nat.card_congr (solEquivC D), Nat.card_fun, card_freeC D]

end Counting

/-! ## PIN-WELLDEF -/

variable {p : ℕ} [Fact p.Prime]

theorem C0_pinWelldef {m : ℕ} (D D' : Locus p m) (h : ∀ x, D.IsSolution x ↔ D'.IsSolution x) : D.numPinned = D'.numPinned := by
  haveI : NeZero p := ⟨(Fact.out : Nat.Prime p).pos.ne'⟩
  -- Each locus has mass `p ^ (m − numPinned)`.
  have key : ∀ (E : Locus p m),
      Nat.card {x : Fin m → ZMod p // E.IsSolution x} = p ^ (m - E.numPinned) := by
    intro E
    rw [massC m E]
    congr 1
    rw [Nat.card_eq_fintype_card, ZMod.card]
  -- Equal solution sets ⟹ equal masses.
  have hcards : Nat.card {x : Fin m → ZMod p // D.IsSolution x}
      = Nat.card {x : Fin m → ZMod p // D'.IsSolution x} :=
    Nat.card_congr (Equiv.subtypeEquivRight h)
  rw [key D, key D'] at hcards
  -- Injectivity of `p ^ ·` (needs `2 ≤ p`) pins the exponent.
  have hp2 : 2 ≤ p := (Fact.out : Nat.Prime p).two_le
  have hexp : m - D.numPinned = m - D'.numPinned := Nat.pow_right_injective hp2 hcards
  -- Both pin counts are ≤ m, so equal exponents force equal counts.
  have hle : ∀ (E : Locus p m), E.numPinned ≤ m := by
    intro E
    simp only [DigitSystem.numPinned]
    calc (Finset.univ.filter (fun i => E.pinned i)).card
        ≤ (Finset.univ : Finset (Fin m)).card := Finset.card_filter_le _ _
      _ = m := by simp
  have hDle := hle D
  have hD'le := hle D'
  omega

end LeanUrat.MovesC
