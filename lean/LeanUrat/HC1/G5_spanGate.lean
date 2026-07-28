/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.HC1.G4_caseKGate

/-!
# HC1.G5_spanGate — the F₉ a = 2 span-pricing gate (the F3-2 check)

moves_ref: MOVES 9580–9582 ("the full position a = 2 gives each re-based branch
𝔸_δ = F₉, i.e. a_δ = 2 ≠ δ·a = 4"); MOVESR_AUDIT_FABLE3 F3-2. deps: G4's F9
object. The ADDITIVE closure of the two slot-image lines {c·1} ∪ {c·τ} is all of
F₉ (card 9 = 3², aDim = 2), while any single line prices card 3. difficulty: easy.
hyp: none.
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

namespace LeanUrat.HC1

/-- Unit G5: span pricing over F₉ — two independent F₃-lines span the full piece;
one line alone prices 3. -/
theorem G5_spanGate :
    (AddSubgroup.closure ({x : F9 | ∃ c : ZMod 3, x = (c, 0)} ∪
        {x : F9 | ∃ c : ZMod 3, x = (0, c)}) = ⊤) ∧
    Nat.card ↥(AddSubgroup.closure {x : F9 | ∃ c : ZMod 3, x = (c, 0)}) = 3 ∧
    Nat.card ↥(AddSubgroup.closure {x : F9 | ∃ c : ZMod 3, x = (0, c)}) = 3 ∧
    Nat.card F9 = 3 ^ 2 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- span: every (a,b) = (a,0) + (0,b), both slot-images sit in the closure
    rw [AddSubgroup.eq_top_iff']
    rintro ⟨a, b⟩
    have hsum : ((a, b) : F9) = ((a, 0) : F9) + ((0, b) : F9) := by simp
    rw [hsum]
    exact add_mem
      (AddSubgroup.subset_closure (Or.inl ⟨a, rfl⟩))
      (AddSubgroup.subset_closure (Or.inr ⟨b, rfl⟩))
  · -- line 1 = range of inl, injective, so card = card (ZMod 3) = 3
    have hinj : Function.Injective (AddMonoidHom.inl (ZMod 3) (ZMod 3)) := by
      intro x y h
      simpa using congrArg Prod.fst h
    have hset : {x : F9 | ∃ c : ZMod 3, x = (c, 0)}
        = ((AddMonoidHom.inl (ZMod 3) (ZMod 3)).range : Set F9) := by
      ext x
      simp [AddMonoidHom.inl_apply, eq_comm]
    rw [hset, AddSubgroup.closure_eq]
    have hcard : Nat.card ↥(AddMonoidHom.inl (ZMod 3) (ZMod 3)).range
        = Nat.card (ZMod 3) :=
      (Nat.card_congr (AddMonoidHom.ofInjective hinj).toEquiv).symm
    rw [hcard, Nat.card_eq_fintype_card, ZMod.card]
  · -- line 2 = range of inr, symmetric
    have hinj : Function.Injective (AddMonoidHom.inr (ZMod 3) (ZMod 3)) := by
      intro x y h
      simpa using congrArg Prod.snd h
    have hset : {x : F9 | ∃ c : ZMod 3, x = (0, c)}
        = ((AddMonoidHom.inr (ZMod 3) (ZMod 3)).range : Set F9) := by
      ext x
      simp [AddMonoidHom.inr_apply, eq_comm]
    rw [hset, AddSubgroup.closure_eq]
    have hcard : Nat.card ↥(AddMonoidHom.inr (ZMod 3) (ZMod 3)).range
        = Nat.card (ZMod 3) :=
      (Nat.card_congr (AddMonoidHom.ofInjective hinj).toEquiv).symm
    rw [hcard, Nat.card_eq_fintype_card, ZMod.card]
  · -- total: |ZMod 3 × ZMod 3| = 9 = 3²
    rw [Nat.card_eq_fintype_card]
    decide

end LeanUrat.HC1

#print axioms LeanUrat.HC1.G5_spanGate
