/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapF.F08
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Uniformity.ChapF.F09 — associativity IS the cocycle identity (W-9(i), abstract half)

**Chapter F, NODE F.09** [theorem] (`blueprint/CHAP-F_weld_layer.md` §5), ENV-F1. For a
carry cocycle `cc`, the twisted convolution on `TwistedAlgebra cc` is associative — the
source's own one-liner run in reverse: "the cocycle identity is not an extra hypothesis but
a consequence of the ring being a ring" (`EFF.GRTJC.90`), here used in the direction the
abstract carrier needs (cocycle ⟹ associative). Direction reversal disclosed in the
blueprint (classical algebra, corpus walks it right-to-left).

The STATEMENT's second half ("`single 0 (cc.c 0 0)⁻¹` is a two-sided unit") is carried by
F.08's `One` instance with the unit laws `TwistedAlgebra.one_mul`/`mul_one` below F.08's
contract line (the A-W.1/F-D3 rider's route, executed at A-W.2).

Was an `axiom` stub at stage 0e; PROVED here (unit OM-9, 2026-08-16; certified first by
`om9_weld_cert.py` LEG C1 — the exact BICONDITIONAL assoc ⟺ cocycle over ALL unit tables
at `(F₄,E=2)/(F₃,E=2)/(F₃,E=3)/(F₅,E=2)`, plus the planted non-cocycle counterexample).

Proof: both sides expand to double sums over pairs; the re-indexing `(s, a) ↦ (a, s − a)`
pairs the terms, and the coefficients match by exactly one instance of the cocycle identity
per term (`F.09a`-style auxiliary `conv_assoc_aux`, the sanctioned split).
-/

namespace Uniformity.Density.Weld

open Finset

namespace TwistedAlgebra

variable {E : ℕ} [NeZero E] {K : Type*} [Field K]

/-- The double-sum re-indexing core (the blueprint's `F.09a` split candidate), stated over
plain functions so the opaque carrier never blocks elaboration. -/
private theorem conv_assoc_aux (c : ZMod E → ZMod E → Kˣ)
    (hco : ∀ a b d, c a b * c (a + b) d = c b d * c a (b + d))
    (F G H : ZMod E → K) (t : ZMod E) :
    ∑ s : ZMod E, (c s (t - s) : K)
        * (∑ a : ZMod E, (c a (s - a) : K) * F a * G (s - a)) * H (t - s)
      = ∑ s : ZMod E, (c s (t - s) : K) * F s
        * (∑ b : ZMod E, (c b (t - s - b) : K) * G b * H (t - s - b)) := by
  have lhs_eq : ∀ s : ZMod E,
      (c s (t - s) : K) * (∑ a : ZMod E, (c a (s - a) : K) * F a * G (s - a)) * H (t - s)
        = ∑ a : ZMod E,
            (c s (t - s) : K) * ((c a (s - a) : K) * F a * G (s - a)) * H (t - s) := by
    intro s
    rw [Finset.mul_sum, Finset.sum_mul]
  have rhs_eq : ∀ s : ZMod E,
      (c s (t - s) : K) * F s
          * (∑ b : ZMod E, (c b (t - s - b) : K) * G b * H (t - s - b))
        = ∑ b : ZMod E,
            (c s (t - s) : K) * F s * ((c b (t - s - b) : K) * G b * H (t - s - b)) := by
    intro s
    rw [Finset.mul_sum]
  simp only [lhs_eq, rhs_eq]
  rw [← Finset.sum_product', ← Finset.sum_product']
  refine Finset.sum_nbij' (fun p => (p.2, p.1 - p.2)) (fun q => (q.1 + q.2, q.1))
    (fun p _ => by simp) (fun q _ => by simp) (fun p _ => ?_) (fun q _ => ?_) (fun p _ => ?_)
  · exact Prod.ext (by simp [add_sub_cancel]) rfl
  · exact Prod.ext rfl (by simp [add_sub_cancel_left])
  · obtain ⟨s, a⟩ := p
    have e1 : a + (s - a) = s := add_sub_cancel a s
    have e2 : t - a - (s - a) = t - s := by rw [sub_sub, e1]
    have key := congrArg (Units.val : Kˣ → K) (hco a (s - a) (t - s))
    rw [e1, show s - a + (t - s) = t - a by rw [add_comm]; exact sub_add_sub_cancel t s a]
      at key
    push_cast at key
    -- key : ↑(c a (s−a)) * ↑(c s (t−s)) = ↑(c (s−a) (t−s)) * ↑(c a (t−a))
    show (c s (t - s) : K) * ((c a (s - a) : K) * F a * G (s - a)) * H (t - s)
        = (c a (t - a) : K) * F a
          * ((c (s - a) (t - a - (s - a)) : K) * G (s - a) * H (t - a - (s - a)))
    rw [e2]
    linear_combination (F a * G (s - a) * H (t - s)) * key

set_option linter.unusedVariables false in
/-- W-9(i)'s abstract half: the twisted convolution is associative, from the cocycle
identity alone. -/
theorem mul_assoc (cc : CarryCocycle E K) (f g h : TwistedAlgebra cc) :
    f * g * h = f * (g * h) := by
  funext t
  rw [mul_apply, mul_apply]
  simp only [mul_apply]
  exact conv_assoc_aux cc.c cc.cocycle f g h t

end TwistedAlgebra

end Uniformity.Density.Weld
