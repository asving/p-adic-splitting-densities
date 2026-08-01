/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib

/-! # Shared ℝ≥0∞ Tonelli Pi-product engine

The dependent-type Tonelli factorization of a `tsum` of finite products over a
Pi type, unconditional in `ℝ≥0∞` (no countability of the factors needed).
Checked absent from Mathlib (loogle `∑' _ : (_ → _), ∏ _, _` and local search,
2026-08-01, per the BP_IV M6b provenance note).

PROVENANCE (SYNTHESIS_PASS3 F4 dedup, 2026-08-01): `tsum_pi_prod` is a
VERBATIM MOVE of the formerly `private` lemma of the same name from
`Scaffold/HDischarge/H8/Lemma33.lean` (H8-A3 generic helpers), de-privatized
here as the single shared engine.  `ValueSide/MassId.lean`'s M6b
`tsum_pi_fin_prod` (the `Fin k → ℕ` form) is re-derived from it as the
constant-family instance. -/

set_option linter.style.longLine false

namespace LeanUrat.Scaffold.Shared

open scoped ENNReal

universe u

/-- Tonelli factorization of a finite product of `ℝ≥0∞` tsums over a Pi type:
`∑'_{g : Π i, α i} ∏_i w_i(g_i) = ∏_i ∑'_{a : α i} w_i(a)`.  Induction on `Fin k`
via `Fin.consEquiv`; unconditional in `ℝ≥0∞` (G-7: no countability needed). -/
lemma tsum_pi_prod : ∀ (k : ℕ) (α : Fin k → Type u) (w : ∀ i, α i → ℝ≥0∞),
    ∑' g : ∀ i, α i, ∏ i, w i (g i) = ∏ i, ∑' a : α i, w i a := by
  intro k
  induction k with
  | zero =>
    intro α w
    have h1 : ∀ g : ∀ i : Fin 0, α i, (∏ i, w i (g i)) = (1 : ℝ≥0∞) := fun g => by simp
    rw [tsum_congr h1, tsum_eq_single (fun i : Fin 0 => i.elim0)
      (fun b' hb' => absurd (funext fun i => i.elim0) hb')]
    simp
  | succ m ih =>
    intro α w
    calc ∑' g : ∀ i, α i, ∏ i, w i (g i)
        = ∑' x : α 0 × ∀ i : Fin m, α i.succ, ∏ i, w i ((Fin.consEquiv α) x i) :=
          ((Fin.consEquiv α).tsum_eq (fun g => ∏ i, w i (g i))).symm
      _ = ∑' x : α 0 × ∀ i : Fin m, α i.succ, w 0 x.1 * ∏ i : Fin m, w i.succ (x.2 i) := by
          refine tsum_congr fun x => ?_
          rw [Fin.prod_univ_succ]
          simp [Fin.consEquiv]
      _ = ∑' a : α 0, ∑' b : ∀ i : Fin m, α i.succ, w 0 a * ∏ i : Fin m, w i.succ (b i) :=
          ENNReal.tsum_prod'
      _ = ∑' a : α 0, w 0 a * ∑' b : ∀ i : Fin m, α i.succ, ∏ i : Fin m, w i.succ (b i) :=
          tsum_congr fun a => ENNReal.tsum_mul_left
      _ = (∑' a : α 0, w 0 a) * ∑' b : ∀ i : Fin m, α i.succ, ∏ i : Fin m, w i.succ (b i) :=
          ENNReal.tsum_mul_right
      _ = (∑' a : α 0, w 0 a) * ∏ i : Fin m, ∑' d : α i.succ, w i.succ d :=
          congrArg (fun z => (∑' a : α 0, w 0 a) * z) (ih (fun i => α i.succ) (fun i => w i.succ))
      _ = ∏ i, ∑' a : α i, w i a := (Fin.prod_univ_succ (fun i => ∑' a : α i, w i a)).symm

end LeanUrat.Scaffold.Shared
