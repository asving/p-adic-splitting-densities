/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapF.F08
import Mathlib.Algebra.BigOperators.Intervals

/-!
# Uniformity.ChapF.F10b — the power basis: `v^E = ζ_T • single 0 1` (JC-F1's presentation)

**Chapter F, NODE F.10, split file b of 2** (split-mandated by the blueprint) [theorem]
(`blueprint/CHAP-F_weld_layer.md` §5), ENV-F1. With `v := single 1 1`, the powers walk the
`single`s and `v ^ E = ζ • single 0 1` with `ζ = ∏_{k=1}^{E−1} cc.c 1 k` — `EFF.GRTJC.91`
(FINDING JC-F1)'s display "`𝒜(T) ≅ K[v]/(v^E − ζ_T)` as a K-algebra — at EVERY composite
stage", in its abstract form. The anchor-INDEXED presentation fence (JC-BOX-5,
REVIEW-OWED) is honoured by scope: abstract object only. The `single 0 1` normalization is
a STATEMENT FENCE (the `•`-form is the contract; `single 0 1` is not the unit unless
`cc.c 0 0 = 1`).

Proof route (certified at om9_weld_cert.py LEG C3 over EVERY cocycle at `E ≤ 4`, both
recursions, before proving): `npowRec` recurses on the RIGHT (`v^{n+1} = v^n * v`), which
telescopes the products `cc.c (n : ZMod E) 1`; F.07's `c_one_comm` (`c 1 k = c k 1`, itself
a consequence of the cocycle identity) converts each factor to the SIGNED orbit product
`∏ c 1 k` — so the statement lands byte-identically without a `Monoid` instance.

Was an `axiom` stub at stage 0e; PROVED here (unit OM-9, 2026-08-16; the gate's F.29 leg 4
executed `v² = ζ • single 0 1` at `ζ = ω` (F₄) and `ζ = 2` (F₃)).
-/

namespace Uniformity.Density.Weld

open Finset

namespace TwistedAlgebra

variable {E : ℕ} [NeZero E] {K : Type*} [Field K] {cc : CarryCocycle E K}

/-- `npowRec` unfolding: `v ^ (n+1) = v ^ n * v` for the F-D3 `Pow`. -/
private theorem pow_succ_def (v : TwistedAlgebra cc) (n : ℕ) : v ^ (n + 1) = v ^ n * v := rfl

/-- The walking powers: `v^n = single n (∏_{k=1}^{n−1} c 1 k)` for `1 ≤ n` (JC-F1's
`v^k = β_k·[φ_{γ_k}]`, right-recursion form converted by `c_one_comm`). -/
private theorem pow_single_aux (n : ℕ) (hn : 1 ≤ n) :
    (single 1 1 : TwistedAlgebra cc) ^ n
      = single ((n : ℕ) : ZMod E) (∏ k ∈ Finset.Ico 1 n, (cc.c 1 ((k : ℕ) : ZMod E) : K)) := by
  induction n with
  | zero => omega
  | succ m ih =>
    rcases Nat.lt_or_ge m 1 with h1 | h1
    · -- m = 0: v^1 = 1 * v = v; the Ico is empty
      have hm0 : m = 0 := Nat.lt_one_iff.mp h1
      subst hm0
      have h0 : (single 1 1 : TwistedAlgebra cc) ^ 1 = 1 * single 1 1 := rfl
      rw [h0, TwistedAlgebra.one_mul]
      simp
    · -- the step: v^(m+1) = v^m * v, telescoping through `single_mul_single` + `c_one_comm`
      have hidx : ((m : ℕ) : ZMod E) + 1 = (((m + 1 : ℕ)) : ZMod E) := by push_cast; rfl
      rw [pow_succ_def, ih h1, single_mul_single, mul_one, ← cc.c_one_comm ((m : ℕ) : ZMod E),
        Finset.prod_Ico_succ_top h1, mul_comm ((cc.c 1 ((m : ℕ) : ZMod E)) : K), hidx]

set_option linter.unusedVariables false in
/-- JC-F1's cyclic presentation, abstract half: `v^E = (∏_{k=1}^{E−1} c(1,k)) • single 0 1`
(`EFF.GRTJC.91`; W-9(iv)'s orbit product `ζ_T`). -/
theorem pow_card_single (cc : CarryCocycle E K) :
    (single 1 1 : TwistedAlgebra cc) ^ E
      = (∏ k ∈ Finset.Ico 1 E, (cc.c 1 (k : ZMod E) : K)) • single 0 1 := by
  have hE : 1 ≤ E := Nat.one_le_iff_ne_zero.mpr (NeZero.ne E)
  rw [pow_single_aux E hE, ZMod.natCast_self]
  funext t
  by_cases h : t = 0 <;> simp [smul_apply, single, h]

end TwistedAlgebra

end Uniformity.Density.Weld
