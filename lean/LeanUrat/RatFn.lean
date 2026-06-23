/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib

/-!
# LeanUrat.RatFn — `IsRationalFn`: a function `ℕ → ℚ` is a uniform rational function of `q`

`IsRationalFn f` says there is a single `num/den ∈ ℚ(t)` (denominator nonvanishing at every `q > 1`)
representing `f` at every `q > 1` — the "uniform rational function of `q`" notion at the heart of the
whole program (it matches `Interface.clusterVolume_rational`'s shape). This file collects the
**closure lemmas** the BB3-∞ induction needs: `IsRationalFn` is closed under constants, addition,
multiplication, finite list sums/products, and division by a pole-free rational function. These are
elementary `ℚ[X]` common-denominator facts (the analogue of `L6M4.sum_clusterVol_rational`, factored
out for reuse by the OM-order induction `BB3inf.clusterVol_isRational`).

All lemmas are PROVED sorry-free; no axioms beyond Lean core.
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false

namespace LeanUrat.RatFn

open Polynomial

/-- `f : ℕ → ℚ` is a **uniform rational function of `q`**: one `num/den ∈ ℚ(t)`, denominator
nonvanishing at every `q > 1`, representing `f` there. -/
def IsRationalFn (f : ℕ → ℚ) : Prop :=
  ∃ num den : Polynomial ℚ, den ≠ 0 ∧
    ∀ q : ℕ, 1 < q → den.eval (q : ℚ) ≠ 0 ∧ f q = num.eval (q : ℚ) / den.eval (q : ℚ)

/-- Constants are rational functions (`num = C c`, `den = 1`). -/
theorem isRationalFn_const (c : ℚ) : IsRationalFn (fun _ => c) :=
  ⟨Polynomial.C c, 1, one_ne_zero, fun q _ => ⟨by simp, by simp⟩⟩

/-- The identity `q ↦ q` is a rational function (`num = X`, `den = 1`). -/
theorem isRationalFn_id : IsRationalFn (fun q => (q : ℚ)) :=
  ⟨Polynomial.X, 1, one_ne_zero, fun q _ => ⟨by simp, by simp⟩⟩

/-- The **`q`-power** `q ↦ q^k` is a rational function, represented by the GENUINELY-NON-CONSTANT
fraction `num = X^k`, `den = 1` (so when `k > 0` the numerator polynomial is `Xᵏ`, a real degree-`k`
monomial, not a constant). This is the closure lemma that puts the BB3 residual count `q ↦ (qᵟ)^(d-1)
= q^(δ(d-1))` genuinely onto the rationality path: its representing numerator is `X^(δ(d-1))`, which
varies with `q` whenever `δ(d-1) > 0`. -/
theorem isRationalFn_qpow (k : ℕ) : IsRationalFn (fun q => (q : ℚ) ^ k) :=
  ⟨Polynomial.X ^ k, 1, one_ne_zero, fun q _ => ⟨by simp, by simp⟩⟩

/-- Sum of two rational functions (common denominator `den_f * den_g`). -/
theorem isRationalFn_add {f g : ℕ → ℚ} (hf : IsRationalFn f) (hg : IsRationalFn g) :
    IsRationalFn (fun q => f q + g q) := by
  obtain ⟨nf, df, hdf, hf⟩ := hf
  obtain ⟨ng, dg, hdg, hg⟩ := hg
  refine ⟨nf * dg + ng * df, df * dg, mul_ne_zero hdf hdg, fun q hq => ?_⟩
  obtain ⟨hdfq, hfq⟩ := hf q hq
  obtain ⟨hdgq, hgq⟩ := hg q hq
  refine ⟨?_, ?_⟩
  · simp only [Polynomial.eval_mul]; exact mul_ne_zero hdfq hdgq
  · simp only [hfq, hgq, Polynomial.eval_add, Polynomial.eval_mul]
    field_simp

/-- Product of two rational functions. -/
theorem isRationalFn_mul {f g : ℕ → ℚ} (hf : IsRationalFn f) (hg : IsRationalFn g) :
    IsRationalFn (fun q => f q * g q) := by
  obtain ⟨nf, df, hdf, hf⟩ := hf
  obtain ⟨ng, dg, hdg, hg⟩ := hg
  refine ⟨nf * ng, df * dg, mul_ne_zero hdf hdg, fun q hq => ?_⟩
  obtain ⟨hdfq, hfq⟩ := hf q hq
  obtain ⟨hdgq, hgq⟩ := hg q hq
  refine ⟨?_, ?_⟩
  · simp only [Polynomial.eval_mul]; exact mul_ne_zero hdfq hdgq
  · simp only [hfq, hgq, Polynomial.eval_mul]
    field_simp

/-- Finite list-sum of rational functions. -/
theorem isRationalFn_listSum (L : List (ℕ → ℚ)) (h : ∀ f ∈ L, IsRationalFn f) :
    IsRationalFn (fun q => (L.map (fun f => f q)).sum) := by
  induction L with
  | nil => simpa using isRationalFn_const 0
  | cons a L ih =>
    have ha : IsRationalFn a := h a List.mem_cons_self
    have hL : ∀ f ∈ L, IsRationalFn f := fun f hf => h f (List.mem_cons_of_mem a hf)
    have := isRationalFn_add ha (ih hL)
    simpa [List.map_cons, List.sum_cons] using this

/-- Finite list-product of rational functions. -/
theorem isRationalFn_listProd (L : List (ℕ → ℚ)) (h : ∀ f ∈ L, IsRationalFn f) :
    IsRationalFn (fun q => (L.map (fun f => f q)).prod) := by
  induction L with
  | nil => simpa using isRationalFn_const 1
  | cons a L ih =>
    have ha : IsRationalFn a := h a List.mem_cons_self
    have hL : ∀ f ∈ L, IsRationalFn f := fun f hf => h f (List.mem_cons_of_mem a hf)
    have := isRationalFn_mul ha (ih hL)
    simpa [List.map_cons, List.prod_cons] using this

/-- Quotient of rational functions, when the denominator is pole-free on `q > 1`.
The representing fraction is `(nf * dg) / (df * ng)`; pole-freeness of `df * ng` at `q > 1`
follows from `df` nonvanishing and `g q ≠ 0` forcing `ng.eval q ≠ 0`. -/
theorem isRationalFn_div {f g : ℕ → ℚ} (hf : IsRationalFn f) (hg : IsRationalFn g)
    (hg0 : ∀ q : ℕ, 1 < q → g q ≠ 0) :
    IsRationalFn (fun q => f q / g q) := by
  obtain ⟨nf, df, hdf, hf⟩ := hf
  obtain ⟨ng, dg, hdg, hg⟩ := hg
  refine ⟨nf * dg, df * ng, ?_, fun q hq => ?_⟩
  · -- df * ng ≠ 0: if ng = 0 then g would vanish everywhere on q > 1, contradicting hg0.
    intro hcontra
    rcases mul_eq_zero.mp hcontra with h | h
    · exact hdf h
    · -- ng = 0 forces g q = 0 for some q > 1
      have h2 : g 2 = 0 := by
        obtain ⟨_, hg2⟩ := hg 2 (by norm_num)
        rw [hg2, h]; simp
      exact hg0 2 (by norm_num) h2
  · obtain ⟨hdfq, hfq⟩ := hf q hq
    obtain ⟨hdgq, hgq⟩ := hg q hq
    have hgne : g q ≠ 0 := hg0 q hq
    have hngq : ng.eval (q : ℚ) ≠ 0 := by
      intro h0; apply hgne; rw [hgq, h0]; simp
    refine ⟨?_, ?_⟩
    · simp only [Polynomial.eval_mul]; exact mul_ne_zero hdfq hngq
    · simp only [hfq, hgq, Polynomial.eval_mul]
      rw [div_div_div_eq]

end LeanUrat.RatFn
