/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.HC1.DefsTower
import LeanUrat.Moves.L3_DIV

/-!
# HC1.D7_digD_mul — the DIG homomorphism (positions add WITH the carry)

moves_ref: MOVES 2305–2315 (Lemma DIV(iii): dig′(R_dev) = dig′(B)·dig′(B″)) +
1456–1459 (D(BB′ mod Φ) = z̄^κ·D(B)D(B′)). deps: D2, Moves `L3_DIV` (clean, verified
on disk). The product is D1's `cmul` — the pass-7 twist made exact. difficulty:
medium. hyp: the (S5)-shape of the three digits (from `StageCoreL`, rides as the
`IsMonomialUnit` hypotheses).
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

namespace LeanUrat.HC1

open Polynomial LeanUrat.Moves

/-- Unit D7: for monomial-unit-shaped coefficients of the lift space `C_Φ̂` with
monic division `B·B″ = Q·Φ̂ + R_dev`, the DIG map is multiplicative into the carry
algebra at the birth index: `digD R_dev = cmul zbar (digD B) (digD B″)`. -/
theorem D7_digD_mul {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
    (σ : Stage p F) (hσ : StageCoreL σ) (ψ : Polynomial ↥σ.K) (g : ℕ)
    (hg : ψ.natDegree = g) (hψ : Irreducible ψ) (hψz : ψ ≠ Polynomial.X)
    (Φhat : Polynomial ℤ_[p]) (hlift : IsStandardLift σ ψ g Φhat)
    (zbar : Fˣ) (hzbar : Polynomial.eval₂ σ.K.subtype ((zbar : Fˣ) : F) ψ = 0)
    (e_b : ℕ) [NeZero e_b]
    (B B'' Rdev Q : Polynomial ℤ_[p]) (hB : B ≠ 0) (hB'' : B'' ≠ 0)
    (hBd : B.natDegree < σ.e * g * σ.Φ.natDegree)
    (hB''d : B''.natDegree < σ.e * g * σ.Φ.natDegree)
    (hdiv : B * B'' = Q * Φhat + Rdev)
    (hRd : Rdev.natDegree < σ.e * g * σ.Φ.natDegree)
    (h5B : IsMonomialUnit (σ.R B)) (h5B'' : IsMonomialUnit (σ.R B''))
    (h5R : IsMonomialUnit (σ.R Rdev)) :
    σ.digD zbar e_b Rdev = cmul zbar (σ.digD zbar e_b B) (σ.digD zbar e_b B'') := by
  sorry

end LeanUrat.HC1

#print axioms LeanUrat.HC1.D7_digD_mul
