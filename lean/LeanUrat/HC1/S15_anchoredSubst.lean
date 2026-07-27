/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.HC1.DefsSpine
import LeanUrat.Moves.L5_recSubst_R4

/-!
# HC1.S15_anchoredSubst — the anchored substitution display (e_birth/e_read rerun, D6)

moves_ref: MOVES 2644–2653 (the anchored display + "Case J pinned a > 0 at
level 1"); 1488–1497 (the pass-7 e_birth/e_read demand). deps: S10, S14, D8; Moves
`L5_recSubst_R4` (clean). On the stratum `R(f) = z^a·(z − c̃)^μ·h(z)` (ψ′-order μ,
anchor a ≥ 0 by S14), the primed data are `a' = μ` and
`R'_anch(z') = (z' + c̃)^a·h(z' + c̃)` — with the D8 𝒟-leg: the birth cosets ride
as spectators (the digD data of the coefficients transform trivially). difficulty:
medium. hyp: none.
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

namespace LeanUrat.HC1

open Polynomial LeanUrat.Moves

/-- Unit S15: the anchored substitution display through a recentering, plus the
𝒟-form spectator clause. -/
theorem S15_anchoredSubst {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
    (σ σ' : Stage p F) (hσ : StageCoreL σ) (he1 : σ.e = 1)
    (cc : ↥σ.K) (hcc : cc ≠ 0) (tt : Polynomial ℤ_[p])
    (hrec : IsRecenteringCore σ σ' cc tt) (hsub : RecenterSubstCore σ σ' cc)
    (f : Polynomial ℤ_[p]) (hf : f ≠ 0)
    (a : ℤ) (ha : 0 ≤ a) (μ : ℕ) (hpoly : Polynomial ↥σ.K)
    (hanch : HasAnchorK (σ.R f) a ((Polynomial.X - Polynomial.C cc) ^ μ * hpoly))
    (hnd : ¬ (Polynomial.X - Polynomial.C cc) ∣ hpoly)
    (zbar : Fˣ) (e_b : ℕ) [NeZero e_b] :
    (∃ Ranch' : Polynomial ↥σ'.K,
      HasAnchorK (σ'.R f) (μ : ℤ) Ranch' ∧
      Ranch'.map σ'.K.subtype
        = (Polynomial.X + Polynomial.C ((cc : ↥σ.K) : F)) ^ a.toNat *
          (hpoly.map σ.K.subtype).comp
            (Polynomial.X + Polynomial.C ((cc : ↥σ.K) : F))) ∧
    (∀ B : Polynomial ℤ_[p], B ≠ 0 → inC σ.Φ B →
      σ'.digD zbar e_b B = σ.digD zbar e_b B) := by
  sorry

end LeanUrat.HC1

#print axioms LeanUrat.HC1.S15_anchoredSubst
