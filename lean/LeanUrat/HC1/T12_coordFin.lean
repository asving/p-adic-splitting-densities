/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.HC1.DefsCar

/-!
# HC1.T12_coordFin — bookkeeping: level-N boxes are finite; fibers are level sets

moves_ref: MOVES 2088–2094 (height scales declared once). deps: DefsTower. sketch:
bounded slot vectors, product finiteness. difficulty: easy. hyp: none.
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

namespace LeanUrat.HC1

open Polynomial LeanUrat.Moves

/-- Unit T12: coordinates restricted to any level-N box (p-adic level and top slot
bounded) form a finite set, and the `(blk, ht)`-fibers are exactly the level sets. -/
theorem T12_coordFin {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
    (T : Tower p F) (lmax bmax : ℕ) :
    Set.Finite {c : T.Coord | c.l < lmax ∧ c.slot (Fin.last T.K) < bmax} ∧
    (∀ (b : ℕ) (γ : ℚ), {c : T.Coord | T.blk c = b ∧ T.ht c = γ} = T.levelSet b γ) := by
  -- The second conjunct is definitional (`levelSet` unfolds to exactly this set).
  refine ⟨?_, fun _ _ => rfl⟩
  -- A uniform bound on every slot value on the box: the last slot is `< bmax`, and
  -- each interior slot `r` is `< slotBound r`, hence all are `< B`.
  set B := bmax + ∑ r, T.slotBound r with hB
  -- Forget the `slot_lt` proof field: `c ↦ (c.l, c.slot)` is injective, and its image
  -- on the box sits inside a finite product of finite sets.
  refine Set.Finite.of_finite_image (f := fun c : T.Coord => (c.l, c.slot)) ?_ ?_
  · refine Set.Finite.subset
      (Set.Finite.prod (Set.finite_Iio lmax)
        (Set.Finite.pi (fun _ : Fin (T.K + 1) => Set.finite_Iio B))) ?_
    rw [Set.image_subset_iff]
    rintro c ⟨hl, hb⟩
    refine ⟨hl, fun i _ => ?_⟩
    rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
    · exact lt_of_lt_of_le (c.slot_lt j)
        (le_trans (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ j))
          (Nat.le_add_left _ _))
    · exact lt_of_lt_of_le hb (Nat.le_add_right _ _)
  · rintro ⟨l1, s1, p1⟩ _ ⟨l2, s2, p2⟩ _ h
    simp only [Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    rfl

end LeanUrat.HC1

#print axioms LeanUrat.HC1.T12_coordFin
