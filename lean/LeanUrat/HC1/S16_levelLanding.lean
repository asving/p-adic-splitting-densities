/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.HC1.DefsSpine
import LeanUrat.Moves.L5_landBox
import LeanUrat.Moves.L5_landVertex
import LeanUrat.Moves.L5_landVertexDigit
import LeanUrat.Moves.L5_landTransport_R4
import LeanUrat.Moves.L5_landTwoSided_repair
import LeanUrat.Moves.L6_moveAffineBij

/-!
# HC1.S16_levelLanding — the per-level transport bijection (D.8/D.10 at level k)

moves_ref: MOVES 2484–2546 (D.8 proof: BOX/VERTEX both directions + TRANSPORT +
two-sidedness); 2654–2659 (RS-landing, the g = 1 case). deps: S11, S15; Moves
`L5_landBox`, `L5_landVertex`, `L5_landVertexDigit` (CLEAN — §4.4 CLOSED),
`L5_landTransport_R4`, `L5_landTwoSided` from `L5_landTwoSided_repair.lean` (CLEAN,
sorry-free, the hexact-hypothesized theorem at :755 — §4.5 RESOLVED; the superseded
`_R5` file is NOT consumed), `L6_moveAffineBij` (clean). THE STATEMENT THREADS the
anchor-exactness clause (§4.5's landed repair): the explicit hypothesis
`hexact : ¬ X ∣ Σ_{j<N} Cdig j · ψ^j` — the stratum's own a = ord_z pin (part of
the stratum's DATA per D.8), matching `L5_landTwoSided`'s theorem verbatim. Stage
hypotheses are DISCHARGED by the spine (S11) — no StageCore hypothesis rides.
difficulty: medium-hard (assembly). hyp: `hexact` per stratum (threaded, never
dropped); zero dep-sorries.
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

namespace LeanUrat.HC1

open Polynomial LeanUrat.Moves

/-- Unit S16: at tower level k, the move restricts to a bijection stratum ↔
landing cylinder on developments (both directions), with the anchor-exactness
clause threaded. -/
theorem S16_levelLanding {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
    (T : Tower p F) (k : Fin T.K) (lm : LevelMove T k)
    (hg : lm.ψ.natDegree = lm.g) (hgpos : 1 ≤ lm.g) (hmon : lm.ψ.Monic)
    (hψ : Irreducible lm.ψ) (hψz : lm.ψ ≠ Polynomial.X)
    (Φhat : Polynomial ℤ_[p])
    (hlift : IsStandardLift (T.stg k.castSucc) lm.ψ lm.g Φhat)
    (hμN : lm.μ < lm.N)
    (hexact : ¬ Polynomial.X ∣ ∑ j ∈ Finset.range lm.N, lm.Cdig j * lm.ψ ^ j)
    (f : Polynomial ℤ_[p]) (hf : f ≠ 0) (B : ℕ → Polynomial ℤ_[p])
    (hdev : IsDevelopment Φhat f B lm.N) :
    StratumData (T.stg k.castSucc) lm.ψ lm.μ lm.a lm.Cdig lm.N f ↔
      LandingCylinderL (T.stg k.castSucc) lm.ψ lm.g lm.μ lm.a lm.Cdig B lm.N := by
  sorry

end LeanUrat.HC1

#print axioms LeanUrat.HC1.S16_levelLanding
