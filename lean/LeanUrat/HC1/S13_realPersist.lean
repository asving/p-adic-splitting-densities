/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.HC1.DefsSpine
import LeanUrat.Moves.L5_realRecursion_R3
import LeanUrat.Moves.L5_realCofin_R3
import LeanUrat.Moves.L5_realDomination_R3
import LeanUrat.Moves.L5_realConclusion

/-!
# HC1.S13_realPersist — Lemma REAL along the tower (D.9)

moves_ref: MOVES 2551–2581 (D.9(a)–(d), incl. the induction-order clause: stage-r
quantities before Φ_{r+1} — the Tower's own structural order). deps: S11, S12;
Moves `L5_realRecursion_R3`, `L5_realCofin_R3`, `L5_realDomination_R3`,
`L5_realConclusion` (all clean). difficulty: medium. hyp: none.
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

namespace LeanUrat.HC1

open Polynomial LeanUrat.Moves

/-- Unit S13: per tower level — the weight set is cofinite upward (a tail bound),
the domination h > e·wPrev(Φ) persists, and at every e_read = 1 stage every
weight-set value is realizable with ANY digit scalar at position 0. -/
theorem S13_realPersist {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
    (T : Tower p F) (k : Fin (T.K + 1)) :
    (∃ ν₀ : ℤ, ∀ ν : ℤ, ν₀ ≤ ν → ν ∈ (T.stg k).weightSet) ∧
    (((T.stg k).e : ℤ) * (T.stg k).wPrev (T.stg k).Φ < ((T.stg k).h : ℤ)) ∧
    ((T.stg k).e = 1 → ∀ (ν : ℤ) (c : (↥(T.stg k).K)ˣ), ν ∈ (T.stg k).weightSet →
      ∃ B : Polynomial ℤ_[p], B ≠ 0 ∧ inC (T.stg k).Φ B ∧
        (T.stg k).wPrev B = ν ∧
        (T.stg k).R B = LaurentPolynomial.C ((c : ↥(T.stg k).K)) *
          LaurentPolynomial.T 0) := by
  sorry

end LeanUrat.HC1

#print axioms LeanUrat.HC1.S13_realPersist
