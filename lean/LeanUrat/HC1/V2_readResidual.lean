/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.HC1.DefsV
import LeanUrat.HC1.V1_readWPack
import LeanUrat.Moves.L3_K1

/-!
# HC1.V2_readResidual — the lawful regrade carrier exists (blueprint §10, V2)

V′-KERNEL unit (blueprint §10.1) — **THE V′ FRAME CHANGE UNIT**: a lawful regrade
carrier exists (+ w_strict, the S9w-(ii) mirror).

Construction (P-phase route, recorded): RV per (†) — scalars from σ.hS5's monomial
digits (parent coefficients only, so every slot digit IS a monomial), positions
`(j − t★·wV f)/e★ = j·s★ − t★·σ.w(B_j)`, injective in j across minimizing slots
(elementary: the map `j ↦ (j − t★γ)/e★` on the tie set), so RV(f) ≠ 0.  hRmul:
V1's Q-ascent + σ.hRmul on slot products + the position additivity (exact,
carry-free in the total coordinate — the §10 DEMOTION NOTE: the carry cocycle is
INVISIBLE in the evaluated V′ coordinate; the proved D-layer certifies the
alignment, it is not load-bearing here).

moves_ref: D.6/D.7(i)–(iii) read at the level-free stage; D.5's "no coset-splitting"
absence note (MOVES 2291–2292). deps: V0, V1, the L3_K1 pattern.
difficulty: medium-hard (the S9w mirror, EASIER: no field extension).
E-phase: statements per §10.1, `sorry` bodies.  `V2_readFrame` packages the frame
(assembled from V1 + the carrier + V6(a)'s hS6a fill in P-phase).
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 800000

namespace LeanUrat.HC1

open Polynomial LeanUrat.Moves

/-- Unit V2: a lawful regrade carrier exists, plus the wV-only strict law (the
S9w-(ii) mirror at the regrade). -/
theorem V2_readResidual {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
    (σ : Stage p F) (hσ : StageCoreL σ)
    (estar hstar : ℕ) (sstar tstar : ℤ)
    (hrp : ReadPair σ estar hstar sstar tstar) :
    (∃ D : ReadResData σ estar hstar sstar tstar, ReadResLaws D) ∧
    (∀ f g, f ≠ 0 → g ≠ 0 →
        childW σ σ.Φ estar hstar f < childW σ σ.Φ estar hstar g →
        childW σ σ.Φ estar hstar (f + g) = childW σ σ.Φ estar hstar f) := by
  sorry

/-- Unit V2 (frame packaging): the full `ReadFrame` is inhabited — the lawful
carrier (above) + V1's wV laws + V6(a)'s hS6a fill. -/
theorem V2_readFrame {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
    (σ : Stage p F) (hσ : StageCoreL σ)
    (estar hstar : ℕ) (sstar tstar : ℤ)
    (hrp : ReadPair σ estar hstar sstar tstar) :
    Nonempty (ReadFrame σ estar hstar sstar tstar) := by
  sorry

end LeanUrat.HC1

#print axioms LeanUrat.HC1.V2_readResidual
#print axioms LeanUrat.HC1.V2_readFrame
