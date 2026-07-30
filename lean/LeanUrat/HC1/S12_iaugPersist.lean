/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.HC1.DefsSpine
import LeanUrat.Moves.L2_iaugRoot
import LeanUrat.Moves.L2_iaugRecenter
import LeanUrat.Moves.L2_iaugStep
import LeanUrat.Moves.L3_liftWeight
import LeanUrat.Moves.L3_liftMonic

/-!
# HC1.S12_iaugPersist — (I-aug) in the D.4 DERIVATION form (audit G-6)

moves_ref: MOVES 2217–2249 (D.4, all three bullets + "by induction along the
history"). deps: DefsTower, S11; Moves `L2_iaugRoot`, `L2_iaugRecenter`,
`L2_iaugStep` (ALL clean — iaugStep proved on disk at 4b29f6e with the
+Irreducible hypothesis, discharged here by the move's `hirr`; §4.2 CLOSED).
QUANTIFIER PIN (G-6): this unit DERIVES that every side of every landing's child
polygon available to the next read is steeper than w(Φ̂) — the per-side chord
inequality — at EVERY tower level (root k = 0, increment landings, recentering
landings: D.4's three bullets ride the ∀ k); TransHyp's own `hiaug` field is the
D4(ii) INTERFACE, merely recording the derived fact per read. difficulty: medium.
hyp: none.
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

namespace LeanUrat.HC1

open Polynomial LeanUrat.Moves

/-- Unit S12: at every tower level, for every legal descend datum, the chord
inequality `e·h·g·(μ − j) < w(B_j) − w(B_μ)` holds on the child polygon below the
vertex, and any (e′,h′) side read off such a chord satisfies `IAug`. -/
theorem S12_iaugPersist {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
    (T : Tower p F) (k : Fin (T.K + 1))
    (ψ : Polynomial ↥(T.stg k).K) (g : ℕ) (hψ : Irreducible ψ)
    (Φhat : Polynomial ℤ_[p]) (hlift : IsStandardLift (T.stg k) ψ g Φhat)
    (f : Polynomial ℤ_[p]) (hf : f ≠ 0) (μ : ℕ) (a : ℤ)
    (Ranch : Polynomial ↥(T.stg k).K) (hanch : HasAnchorK ((T.stg k).R f) a Ranch)
    (hord : OrdPsiPoly ψ Ranch μ) (B : ℕ → Polynomial ℤ_[p]) (N : ℕ)
    (hdev : IsDevelopment Φhat f B N) :
    (∀ j, j < μ → B j ≠ 0 →
      ((T.stg k).e : ℤ) * (T.stg k).h * g * ((μ : ℤ) - j)
        < (T.stg k).w (B j) - (T.stg k).w (B μ)) ∧
    (∀ (e' h' : ℕ) (j : ℕ), 1 ≤ e' → j < μ → B j ≠ 0 →
      (h' : ℤ) * ((μ : ℤ) - (j : ℤ))
          = (e' : ℤ) * ((T.stg k).w (B j) - (T.stg k).w (B μ)) →
      IAug (T.stg k) Φhat e' h') := by
  refine ⟨?_, ?_⟩
  · -- Conjunct 1: the per-side chord inequality — exactly the increment move `L2_iaugStep`.
    intro j hj hjnz
    exact L2_iaugStep (T.stg k) ψ g hψ Φhat hlift f hf μ a Ranch hanch hord B N hdev j hj hjnz
  · -- Conjunct 2: any side `(e',h')` read off such a chord is `IAug` (steeper than `w Φ̂`).
    intro e' h' j he' hj hjnz hchord
    -- `1 ≤ g`, since `g = deg ψ` and `ψ` is irreducible.
    have hgdeg : ψ.natDegree = g := by obtain ⟨-, h, -⟩ := hlift; exact h
    have hg1 : 1 ≤ g := by rw [← hgdeg]; exact hψ.natDegree_pos
    -- `Φ̂ ≠ 0`, from its monicity (L3_liftMonic).
    have hΦne : Φhat ≠ 0 := (L3_liftMonic (T.stg k) ψ g hg1 Φhat hlift).1.ne_zero
    -- The equal-weights theorem: `w Φ̂ = e·h·g` (L3_liftWeight).
    have hw : (T.stg k).w Φhat = ((T.stg k).e : ℤ) * (T.stg k).h * g :=
      L3_liftWeight (T.stg k) ψ g hg1 Φhat hlift hΦne
    -- The step bound at this `j`.
    have hstep := L2_iaugStep (T.stg k) ψ g hψ Φhat hlift f hf μ a Ranch hanch hord B N hdev j hj hjnz
    -- Positivity facts.
    have hΔ : (0 : ℤ) < (μ : ℤ) - (j : ℤ) := by omega
    have he'pos : (0 : ℤ) < (e' : ℤ) := by exact_mod_cast he'
    -- Multiply the step bound by `e' > 0`, then use the chord to rewrite the right side.
    have key : (e' : ℤ) * ((T.stg k).e * (T.stg k).h * g) * ((μ : ℤ) - (j : ℤ))
        < (h' : ℤ) * ((μ : ℤ) - (j : ℤ)) := by
      calc (e' : ℤ) * ((T.stg k).e * (T.stg k).h * g) * ((μ : ℤ) - (j : ℤ))
          = (e' : ℤ) * (((T.stg k).e : ℤ) * (T.stg k).h * g * ((μ : ℤ) - (j : ℤ))) := by ring
        _ < (e' : ℤ) * ((T.stg k).w (B j) - (T.stg k).w (B μ)) :=
              mul_lt_mul_of_pos_left hstep he'pos
        _ = (h' : ℤ) * ((μ : ℤ) - (j : ℤ)) := by rw [← hchord]
    -- Divide by `(μ − j) > 0` to land `IAug`.
    show (h' : ℤ) > (e' : ℤ) * (T.stg k).w Φhat
    rw [hw]
    exact lt_of_mul_lt_mul_right key (le_of_lt hΔ)

end LeanUrat.HC1

#print axioms LeanUrat.HC1.S12_iaugPersist
