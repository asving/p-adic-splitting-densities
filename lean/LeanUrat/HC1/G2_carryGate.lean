/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.HC1.DefsD

/-!
# HC1.G2_carryGate — the carry-algebra table at e = 2 over F₄ (decide gate)

moves_ref: MOVES 1508–1509. deps: D1, D2. legs: `dOf 1 1 * dOf 1 1 = dOf 0 z̄`,
`dOf 1 c * dOf 0 c' = dOf 1 (c·c')`, and the cocycle identity for all
ρ,σ,τ ∈ ZMod 2. difficulty: easy. hyp: none.
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

namespace LeanUrat.HC1

/-- Unit G2: the e = 2 carry table over F₄ (z̄ a primitive cube root: z̄² = z̄ + 1),
against any D1 ring pack. -/
theorem G2_carryGate :
    ∃ zbar : (GaloisField 2 2)ˣ,
      ((zbar : GaloisField 2 2) ^ 2 = (zbar : GaloisField 2 2) + 1) ∧
      ∀ P : CarryRingPack (GaloisField 2 2) 2 zbar,
        (letI := P.ring;
          dOf (1 : ZMod 2) (1 : GaloisField 2 2) * dOf 1 1
            = dOf 0 ((zbar : GaloisField 2 2))) ∧
        (∀ c c' : GaloisField 2 2, letI := P.ring;
          dOf (1 : ZMod 2) c * dOf 0 c' = dOf 1 (c * c')) ∧
        (∀ ρ σ τ : ZMod 2,
          carryExp ρ σ + carryExp (ρ + σ) τ = carryExp σ τ + carryExp ρ (σ + τ)) := by
  sorry

end LeanUrat.HC1

#print axioms LeanUrat.HC1.G2_carryGate
