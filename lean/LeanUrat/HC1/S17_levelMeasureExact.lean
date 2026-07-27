/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.HC1.DefsSpine
import LeanUrat.Moves.L6_ledgerCount
import LeanUrat.Moves.L6_moveReduceCommute_R4
import LeanUrat.Moves.L6_measureExact_R4

/-!
# HC1.S17_levelMeasureExact — D.11 at every level (ONE move; no composition — D8 fence)

moves_ref: MOVES 2672–2718 (D.11 in full, incl. the unit-system clause and the
dichotomy). deps: S16, C3, C5, C6, T11; Moves `L6_ledgerCount`,
`L6_moveReduceCommute_R4` (clean); dep-sorry: `L6_measureExact_R4` (§4.6 — two
sorries :143/:189, the SOLE surviving tail entry; its :143 inline lemma needs the
same hexact clause threaded by restatement — §4.6's spec; sign-off required for
that restatement, carried honestly here). "Admissible stratum" INCLUDES the
anchor-exactness clause `hexact` (threaded from S16 — §4.5's landed repair; the
G-2 threading). The jet chart (code/Θ/E) is §C-side data riding as hypotheses,
exactly as `L6_measureExact` takes `codeN`/`ΘN`/`hcylN`. The inadmissible-pin
empty-locus leg is T11's dichotomy (cited, not restated). difficulty: HARD.
hyp: `hexact` per stratum; dep-sorry §4.6 only.
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

namespace LeanUrat.HC1

open Polynomial LeanUrat.Moves

/-- Unit S17: at tower level k, for an admissible stratum with jet chart at level
N above the largest constrained height + 1, the stratum's box count is EXACTLY the
nominal pinned-digit count: `#stratum · p^ktot = p^{D·N}` (division-free D.11 —
vol = the attainable product over the cylinder's digit equations, each factor
priced by C6's cardinality through `ktot = E.numPinned`). -/
theorem S17_levelMeasureExact {p : ℕ} [Fact p.Prime] {F : Type*} [Field F]
    [Finite F] (T : Tower p F) (k : Fin T.K) (lm : LevelMove T k)
    (hg : lm.ψ.natDegree = lm.g) (hgpos : 1 ≤ lm.g) (hmon : lm.ψ.Monic)
    (hψ : Irreducible lm.ψ) (hψz : lm.ψ ≠ Polynomial.X)
    (Φhat : Polynomial ℤ_[p])
    (hlift : IsStandardLift (T.stg k.castSucc) lm.ψ lm.g Φhat)
    (hμN : lm.μ < lm.N)
    (hexact : ¬ Polynomial.X ∣ ∑ j ∈ Finset.range lm.N, lm.Cdig j * lm.ψ ^ j)
    (D ktot N : ℕ) (hD : D = Φhat.natDegree * lm.N) (hN : 1 ≤ N)
    (hkN : ktot ≤ D * N)
    (strat : (Fin (D * N) → ZMod p) → Prop)
    (code : Polynomial ℤ_[p] → (Fin (D * N) → ZMod p))
    (hcode : ∀ x, ∃ f : Polynomial ℤ_[p], f.natDegree < D ∧ code f = x)
    (hstrat : ∀ f : Polynomial ℤ_[p], f.natDegree < D →
      (strat (code f) ↔
        (f ≠ 0 ∧ StratumData (T.stg k.castSucc) lm.ψ lm.μ lm.a lm.Cdig lm.N f)))
    (hz : ∀ f : Polynomial ℤ_[p], f.natDegree < D → f = 0 → ¬ strat (code f))
    (Θ : (Fin (D * N) → ZMod p) ≃ (Fin (D * N) → ZMod p))
    (hΘ : LeanUrat.MovesC.IsUnitriangular fun x => Θ x)
    (E : DigitSystem (D * N) (ZMod p)) (hEk : E.numPinned = ktot)
    (hcyl : ∀ (f : Polynomial ℤ_[p]) (B : ℕ → Polynomial ℤ_[p]),
      f.natDegree < D → f ≠ 0 → IsDevelopment Φhat f B lm.N →
      (E.IsSolution (Θ (code f)) ↔
        LandingCylinderL (T.stg k.castSucc) lm.ψ lm.g lm.μ lm.a lm.Cdig B lm.N)) :
    Nat.card {x : Fin (D * N) → ZMod p // strat x} * p ^ ktot = p ^ (D * N) := by
  sorry

end LeanUrat.HC1

#print axioms LeanUrat.HC1.S17_levelMeasureExact
