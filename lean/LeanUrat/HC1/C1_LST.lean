/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.HC1.DefsCar

/-!
# HC1.C1_LST — Lemma LST over the real carriers

moves_ref: MOVES 3728–3777 (Lemma LST, all legs). deps: T3, T4, T5, T10. The
conjunction (i-a) T3, (i-b) T4, (i-c) T5, (ii) T10, (iii) the floor-set emptiness —
arithmetic from (i)+(ii). difficulty: medium (assembly + (iii)).
hyp: `TowerRealizable` (via T10) — §5's open kernel, carried as `rl`.
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

namespace LeanUrat.HC1

open Polynomial LeanUrat.Moves

/-- Unit C1: **Lemma LST** for a realizable tower — the five legs assembled. -/
theorem C1_LST {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
    (T : Tower p F) (rl : TowerRealizable T) :
    -- (i-a): ht is the K1-chain weight of the basis monomial (T3's form)
    (∀ c : T.Coord, c.MonoNZ →
      (((T.stg (Fin.last T.K)).w (T.mono c) : ℤ) : ℚ) = (T.strTop : ℚ) * T.ht c) ∧
    -- (i-b): the iterated slot minimum (T4's form)
    (∀ (b : ℕ) (y : T.Coord → ↥(T.stg 0).FQ), (Function.support y).Finite →
      (∀ c, y c ≠ 0 → T.blk c = b) → T.slotCoeff b y ≠ 0 →
      ∃ c₀, y c₀ ≠ 0 ∧ T.wQ (T.slotCoeff b y) = (T.ht c₀ : WithTop ℚ) ∧
        ∀ c, y c ≠ 0 → T.ht c₀ ≤ T.ht c) ∧
    -- (i-c): in_γ' is a function of exactly the level set (T5's form)
    (∀ (b : ℕ) (γ' : ℚ) (x y : T.Coord → ↥(T.stg 0).FQ),
      (Function.support x).Finite → (Function.support y).Finite →
      (∀ c ∈ T.levelSet b γ', x c = y c) →
      (∀ c, T.blk c = b → T.ht c < γ' → x c = 0) →
      (∀ c, T.blk c = b → T.ht c < γ' → y c = 0) →
      T.inGr γ' (T.slotCoeff b x) = T.inGr γ' (T.slotCoeff b y)) ∧
    -- (ii): the staircase floor on factor-interior blocks (T10's form)
    (∀ b, rl.interiorB b → ∀ c : T.Coord, T.blk c = b → rl.floorC c = rl.floorB b) ∧
    -- (iii): level sets strictly above the floor avoid the floor set
    (∀ (b : ℕ) (γ' : ℚ), rl.interiorB b → rl.floorB b < γ' →
      T.levelSet b γ' ∩ {c | T.blk c = b ∧ T.ht c ≤ rl.floorB b} = ∅) := by
  sorry

end LeanUrat.HC1

#print axioms LeanUrat.HC1.C1_LST
