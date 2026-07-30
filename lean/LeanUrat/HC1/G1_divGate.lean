/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib

/-!
# HC1.G1_divGate — the pass-6/DIV arithmetic gate over F₄ (decide gate; no sorry
allowed at acceptance — body left `sorry` at E-phase, the fleet decides it)

moves_ref: MOVES 2318–2322 (the verifier's value: dig′(Φ) = z̄ ⟹ dig′(Φ² mod Φ̂)
= z̄² = z̄ + 1, checked as the field computation). statement: the two F4-equalities
(AdjoinRoot over ZMod 2; if decide stalls, the recorded E-phase latitude is the
4-element enum field restatement). difficulty: easy. hyp: none.
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

namespace LeanUrat.HC1

open Polynomial

/-- G1's concrete F₄ model: `AdjoinRoot (X² + X + 1)` over F₂. -/
noncomputable def F4gate : Type :=
  AdjoinRoot (Polynomial.X ^ 2 + Polynomial.X + 1 : Polynomial (ZMod 2))

noncomputable instance : CommRing F4gate :=
  inferInstanceAs (CommRing (AdjoinRoot _))

/-- the residue root z̄ of G1's model. -/
noncomputable def zbGate : F4gate :=
  AdjoinRoot.root (Polynomial.X ^ 2 + Polynomial.X + 1 : Polynomial (ZMod 2))

/-- Unit G1: `z̄² = z̄ + 1` (the root equation) and the DIV instance's field
computation `z̄·z̄ = z̄ + 1` — the verifier's value. -/
theorem G1_divGate :
    zbGate ^ 2 = zbGate + 1 ∧ zbGate * zbGate = zbGate + 1 := by
  -- Work in the underlying `AdjoinRoot` type, where the algebra/aeval instances resolve
  -- (`F4gate` is an opaque `def`, so `Algebra (ZMod 2) F4gate` is not found directly).
  have key :
      (AdjoinRoot.root (Polynomial.X ^ 2 + Polynomial.X + 1 : Polynomial (ZMod 2))) ^ 2 =
        (AdjoinRoot.root (Polynomial.X ^ 2 + Polynomial.X + 1 : Polynomial (ZMod 2))) + 1 := by
    -- The defining relation of the root: `aeval z (X²+X+1) = mk f f = 0`, i.e. `z² + z + 1 = 0`.
    have hrel :
        (AdjoinRoot.root (Polynomial.X ^ 2 + Polynomial.X + 1 : Polynomial (ZMod 2))) ^ 2 +
          (AdjoinRoot.root (Polynomial.X ^ 2 + Polynomial.X + 1 : Polynomial (ZMod 2))) + 1 = 0 := by
      have hz :
          aeval (AdjoinRoot.root (Polynomial.X ^ 2 + Polynomial.X + 1 : Polynomial (ZMod 2)))
              (Polynomial.X ^ 2 + Polynomial.X + 1 : Polynomial (ZMod 2)) = 0 := by
        rw [AdjoinRoot.aeval_eq, AdjoinRoot.mk_self]
      simpa only [map_add, map_pow, Polynomial.aeval_X, map_one] using hz
    -- Characteristic two: `(2 : AdjoinRoot f) = algebraMap (2 : ZMod 2) = algebraMap 0 = 0`.
    have h2 : (2 : AdjoinRoot (Polynomial.X ^ 2 + Polynomial.X + 1 : Polynomial (ZMod 2))) = 0 := by
      rw [← map_ofNat
            (algebraMap (ZMod 2)
              (AdjoinRoot (Polynomial.X ^ 2 + Polynomial.X + 1 : Polynomial (ZMod 2)))) 2,
        show (2 : ZMod 2) = 0 from by decide, map_zero]
    -- `z² = z + 1` follows from `z² + z + 1 = 0` and `2 = 0`.
    linear_combination hrel -
      (AdjoinRoot.root (Polynomial.X ^ 2 + Polynomial.X + 1 : Polynomial (ZMod 2)) + 1) * h2
  exact ⟨key, by rw [← pow_two]; exact key⟩

end LeanUrat.HC1

#print axioms LeanUrat.HC1.G1_divGate
