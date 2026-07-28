/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.HC1.DefsCar
import LeanUrat.Moves.L5_realCofin_R3
import LeanUrat.Moves.L5_realDomination_R3

/-!
# HC1.C6_alphabetCard — the alphabet cardinality + the fullness DICHOTOMY (G-4)

moves_ref: MOVES 2160–2165 "= [F_{k+1} : F_p] … EXACTLY WHEN every height in γ's
slot tree is attainable … and STRICTLY SMALLER at shallow heights". deps: T7, T8;
Moves `L5_realCofin_R3`, `L5_realDomination_R3` (clean). BOTH directions (audit
G-4): fullness ⟺ every level-set coordinate's slot image is attainable (nonzero),
and STRICTLY SMALLER on the failing side; the D.9(b) clean-threshold regime is the
displayed sufficient INSTANCE of the ⟸ leg, not the statement. Still no
unconditional fullness claim (the rev-D¹¹c fix stands). difficulty: medium.
hyp: none.
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

namespace LeanUrat.HC1

open Polynomial LeanUrat.Moves
open scoped Classical

/-- **The card-K bridge (F-2, sign-off event 2026-07-28, blueprint §9.2):** every
stage residue field of a tower has p-power cardinality, `Nat.card ↥K = p^d` with
`d = [K : F_p] ≥ 1` — the bridge C6's conjuncts 2–3 consume. Underivable before the
F-2 char pin `Tower.hcharF : CharP F p` (round-2 fleet kernel: `Stage p F` carries
no characteristic tie, so `Nat.card K` was a power of char F, junk off char p); the
pin records the note's own setting (F_{k+1}/F_p extensions, MOVES 2148–2165). -/
theorem C6_cardK_bridge {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
    (T : Tower p F) (k : Fin (T.K + 1)) :
    ∃ d : ℕ, 1 ≤ d ∧ Nat.card ↥(T.stg k).K = p ^ d := by
  haveI : CharP F p := T.hcharF
  haveI : Fintype ↥(T.stg k).K := Fintype.ofFinite _
  haveI : CharP ↥(T.stg k).K p :=
    RingHom.charP (T.stg k).K.subtype (T.stg k).K.subtype.injective p
  obtain ⟨n, -, hn⟩ := FiniteField.card ↥(T.stg k).K p
  exact ⟨(n : ℕ), n.2, by rw [Nat.card_eq_fintype_card, hn]⟩

/-- Unit C6: `#𝔸 = p^aDim`; on nonempty level sets, fullness (𝔸 = the full value
field F_{K+1} = the top stage's K, in cardinality) holds EXACTLY WHEN every slot
height is attainable, and is STRICTLY SMALLER when some slot height is
unattainable. -/
theorem C6_alphabetCard {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
    (T : Tower p F) (b : ℕ) (γ : ℚ) (hne : (T.levelSet b γ).Nonempty) :
    Nat.card ↥(T.alphabet b γ) = p ^ T.aDim b γ ∧
    (Nat.card ↥(T.alphabet b γ) = Nat.card ↥(T.stg (Fin.last T.K)).K ↔
      ∀ c : ↥(T.levelSet b γ), ∃ y : ↥(T.stg 0).FQ,
        T.typComposite b γ (Pi.single c y) ≠ 0) ∧
    ((∃ c : ↥(T.levelSet b γ), ∀ y : ↥(T.stg 0).FQ,
        T.typComposite b γ (Pi.single c y) = 0) →
      T.aDim b γ < Nat.log p (Nat.card ↥(T.stg (Fin.last T.K)).K)) := by
  sorry

end LeanUrat.HC1

#print axioms LeanUrat.HC1.C6_cardK_bridge
#print axioms LeanUrat.HC1.C6_alphabetCard
