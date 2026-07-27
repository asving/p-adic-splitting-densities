/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.HC1.DefsCar

/-!
# HC1.R1_LSTStmt — `LSTStmt'` over the re-keyed abstract carriers (MovesR re-key)

moves_ref: MOVES 3728–3749; MOVESR blueprint 602–615 (the rev-4 text being
repaired). REPAIRS BUILT IN: the staircase equation INLINED into leg (ii) via the
`blockEdge` carrier field (F3-3), and the `window` predicate scoping legs
(i-b)/(i-c) (G3-2). difficulty: easy (statement unit). hyp: the statement def
itself is the open REL.1 clause — consumers hypothesize it, never assert it.
Re-audit REQUIRED before MovesR unparks (blueprint layer-R charge).
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

namespace LeanUrat.HC1

/-- **The re-keyed abstract carrier bundle** (HC1's re-declaration of the MovesR
CInterface shapes, pending the MovesR re-key): the graded carrier `G` plus the
history/coordinate vocabulary each §C statement def reads — heights, blocks,
level sets, slot coefficients, alphabets' dimensions, lines, block edges,
interiors, the window scope, basis monomials, and the floor. -/
structure CarrierPackR (p : ℕ) [Fact p.Prime] where
  G : GradedCarrierR p
  Hist : Type
  Coord : Type
  Digit : Type
  [digitAdd : AddCommGroup Digit]
  kIdx : Hist → ℕ
  ht : Hist → Coord → ℚ
  blk : Hist → Coord → ℕ
  lvl : Hist → ℕ → ℚ → Set Coord
  slotCoeff : Hist → ℕ → (Coord → Digit) → G.Coeff
  aDim : Hist → ℕ → ℚ → ℕ
  lines : Hist → ℕ → MovesC.Line
  blockEdge : Hist → ℕ → ℕ
  interiorEnd : Hist → ℕ → ℕ
  window : Hist → ℕ → Prop
  mono : Hist → Coord → G.Coeff
  floorB : Hist → ℕ → ℚ

attribute [instance] CarrierPackR.digitAdd

/-- **`LSTStmt'`** (R1): Lemma LST over the abstract carriers — (i-a) the K1-chain
weight typing `w(mono c) = ht c`; (i-b) the attained slot minimum, WINDOW-scoped
(G3-2); (i-c) the level-set functionality, window-scoped; (ii) the staircase
equation INLINED (F3-3): `floorB H b = (lines H (kIdx H)).at (blockEdge H b)`;
(iii) level sets above the floor avoid the floor set. -/
def LSTStmt' (p : ℕ) [Fact p.Prime] (K : CarrierPackR p) : Prop :=
  ∀ H : K.Hist,
    (∀ c : K.Coord, K.G.w (K.mono H c) = (K.ht H c : WithTop ℚ)) ∧
    (∀ b : ℕ, K.window H b → ∀ y : K.Coord → K.Digit, K.slotCoeff H b y ≠ 0 →
      ∃ c₀ : K.Coord, y c₀ ≠ 0 ∧ K.G.w (K.slotCoeff H b y) = (K.ht H c₀ : WithTop ℚ) ∧
        ∀ c : K.Coord, y c ≠ 0 → K.ht H c₀ ≤ K.ht H c) ∧
    (∀ b : ℕ, K.window H b → ∀ (γ : ℚ) (x y : K.Coord → K.Digit),
      (∀ c ∈ K.lvl H b γ, x c = y c) →
      (∀ c : K.Coord, K.blk H c = b → K.ht H c < γ → x c = 0 ∧ y c = 0) →
      K.G.inγ γ (K.slotCoeff H b x) = K.G.inγ γ (K.slotCoeff H b y)) ∧
    (∀ b : ℕ, K.floorB H b = (K.lines H (K.kIdx H)).at (K.blockEdge H b)) ∧
    (∀ (b : ℕ) (γ' : ℚ), K.floorB H b < γ' →
      ∀ c ∈ K.lvl H b γ', ¬ (K.blk H c = b ∧ K.ht H c ≤ K.floorB H b))

end LeanUrat.HC1

#print axioms LeanUrat.HC1.LSTStmt'
