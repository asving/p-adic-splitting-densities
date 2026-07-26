/-
Unit C0.solvedGraph — moves_ref: §C.1.5' 'solve Σ_i's system in ≺-order (graph over free coordinates)'

The restriction-to-free-coordinates map is an equivalence between the solution set of a
unitriangular digit system and assignments to its free (unpinned) coordinates: injective
(pinned coordinates are `solve` of strictly-earlier ones — strong induction) and surjective
(extend a free assignment by well-founded recursion on the coordinate order — the `extend`
device of `LeanUrat.Moves.L2_P6ii_R3`). The extra clause pins `E` to BE the restriction map,
which is definitional here since `toFun x j = x.val j.val`.
-/
import LeanUrat.MovesC.Defs

set_option linter.style.longLine false

namespace LeanUrat.MovesC

open LeanUrat.Moves

section Extend
variable {α : Type*} {n : ℕ} (D : DigitSystem n α)

/-- Extend a free-coordinate assignment `f` to a full coordinate vector: a free coordinate takes
its `f`-value, a pinned coordinate is `solve` of the (already-built) strictly-earlier values.
Well-founded recursion on the coordinate order. -/
private def solvedExtend (f : {i : Fin n // D.pinned i = false} → α) : (i : Fin n) → α
  | i =>
    if h : D.pinned i = false then f ⟨i, h⟩
    else D.solve i (fun j hj => solvedExtend f j)
  termination_by i => i.val
  decreasing_by exact hj

private lemma solvedExtend_eq (f : {i : Fin n // D.pinned i = false} → α) (i : Fin n) :
    solvedExtend D f i =
      if h : D.pinned i = false then f ⟨i, h⟩ else D.solve i (fun j _ => solvedExtend D f j) := by
  rw [solvedExtend]

/-- The extension of any free assignment is a solution. -/
private lemma solvedExtend_isSolution (f : {i : Fin n // D.pinned i = false} → α) :
    D.IsSolution (solvedExtend D f) := by
  intro i hi
  rw [solvedExtend_eq]
  rw [dif_neg (by simp [hi])]

/-- A free assignment, extended and then restricted to the free coordinates, returns itself. -/
private lemma solvedExtend_restrict (f : {i : Fin n // D.pinned i = false} → α)
    (i : {i : Fin n // D.pinned i = false}) : solvedExtend D f i.val = f i := by
  rw [solvedExtend_eq, dif_pos i.2]

/-- A solution is recovered from its restriction to the free coordinates (strong induction on the
coordinate index `m = i.val`). -/
private lemma restrict_solvedExtend (x : Fin n → α) (hx : D.IsSolution x) :
    ∀ (m : ℕ) (i : Fin n), i.val = m → solvedExtend D (fun i => x i.val) i = x i := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m IH =>
    intro i hi
    rw [solvedExtend_eq]
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

/-- The solution set is in bijection with free-coordinate assignments, via restriction. -/
private def solvedEquiv :
    {x : Fin n → α // D.IsSolution x} ≃ ({i : Fin n // D.pinned i = false} → α) where
  toFun x i := x.val i.val
  invFun f := ⟨solvedExtend D f, solvedExtend_isSolution D f⟩
  left_inv := by
    rintro ⟨x, hx⟩
    ext i
    simpa using restrict_solvedExtend D x hx i.val i rfl
  right_inv := by
    intro f
    ext i
    simpa using solvedExtend_restrict D f i

end Extend

variable {p : ℕ}

theorem C0_solvedGraph {m : ℕ} (D : Locus p m) : ∃ E : {x : Fin m → ZMod p // D.IsSolution x} ≃ ({j : Fin m // D.pinned j = false} → ZMod p), ∀ (x : {x : Fin m → ZMod p // D.IsSolution x}) (j : {j : Fin m // D.pinned j = false}), E x j = x.1 j.1 :=
  ⟨solvedEquiv D, fun _ _ => rfl⟩

end LeanUrat.MovesC
