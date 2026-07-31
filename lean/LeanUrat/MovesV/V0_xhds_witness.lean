/-  MovesV unit V0-4 `xhds_instance_A2` (RE-KEYED C3) — THE NON-DEGENERACY
    WITNESS for the XHD-s format, in the (t,u) CHART where `EA2` lives. -/
import LeanUrat.MovesV.DefsGate
import LeanUrat.MovesS.EvalAtCoe

set_option linter.style.longLine false
set_option linter.style.header false

namespace LeanUrat.MovesV
open LeanUrat.MovesS (Qq OKat evalAt eval_algebraMap_div)

/-- the cleared rational form X²/((X⁶−1)(X³−1)) — denominators in the
PolyGeom class. -/
noncomputable def GA2 : Qq :=
  algebraMap (Polynomial ℚ) Qq (Polynomial.X ^ 2)
    / algebraMap (Polynomial ℚ) Qq
        ((Polynomial.X ^ 6 - 1) * (Polynomial.X ^ 3 - 1))

/-- the seal's base value: EA2.eval ![1,0] = 7 (E at (h₀,h₂) = (4,1)). -/
theorem EA2_seal : EA2.eval ![1, 0] = 7 := by decide

/- [SYN2-S1 SWEEP-2, 2026-07-31] private eval_algebraMap_div (the cross-corpus
mirror) DELETED — single proof source `MovesS/EvalAtCoe.lean` (public, brought in
through the extended `open LeanUrat.MovesS (...)` clause). -/

/-- the real geometric-value clearing identity (part ⌿(b)). -/
private lemma geomValId (r : ℝ) (hr : 1 < r) :
    r ^ (-7 : ℤ) * ((1 - r ^ (-6 : ℤ))⁻¹ * (1 - r ^ (-3 : ℤ))⁻¹)
      = r ^ 2 / ((r ^ 6 - 1) * (r ^ 3 - 1)) := by
  have hr0 : (0 : ℝ) < r := by linarith
  have hr0' : r ≠ 0 := ne_of_gt hr0
  have h6 : (1 : ℝ) < r ^ 6 := one_lt_pow₀ hr (by norm_num)
  have h3 : (1 : ℝ) < r ^ 3 := one_lt_pow₀ hr (by norm_num)
  rw [zpow_neg, zpow_neg, zpow_neg,
    show (6 : ℤ) = ((6 : ℕ) : ℤ) from rfl, show (3 : ℤ) = ((3 : ℕ) : ℤ) from rfl,
    show (7 : ℤ) = ((7 : ℕ) : ℤ) from rfl, zpow_natCast, zpow_natCast, zpow_natCast]
  have hp6 : (r ^ 6 : ℝ) ≠ 0 := by positivity
  have hp3 : (r ^ 3 : ℝ) ≠ 0 := by positivity
  field_simp

/-- the index bijection ℕ × ℕ ≃ the A2 height domain: `(a,b) ↦ (t,u) = (1+a, b)`
(part ⌿(a)'s reindexing). -/
private noncomputable def A2equiv : ℕ × ℕ ≃ {h : Hpt 2 // A2dom.Mem h} where
  toFun p := ⟨![1 + p.1, p.2], ![p.1, p.2], by
    change (![1 + p.1, p.2] : Hpt 2) = fun i => A2dom.base i
        + ∑ j : Fin 2, (![p.1, p.2] : Fin 2 → ℕ) j * (A2dom.periods.get j) i
    funext i; fin_cases i <;> simp [A2dom, Fin.sum_univ_two]⟩
  invFun h := (h.1 0 - 1, h.1 1)
  left_inv := by rintro ⟨a, b⟩; simp
  right_inv := by
    rintro ⟨h, c, hc⟩
    apply Subtype.ext
    have hb : h 0 = A2dom.base 0 + ∑ j, c j * (A2dom.periods.get j) 0 := by rw [hc]
    rw [show A2dom.base 0 = 1 from rfl] at hb
    have hh : (1 : ℕ) ≤ h 0 := by omega
    change ![1 + (h 0 - 1), h 1] = h
    funext i; fin_cases i <;> simp <;> omega

theorem xhds_instance_A2 (q₀ : ℚ) (hpp : IsPP q₀) (hq : 1 < q₀)
    (hok : GA2 ∈ OKat q₀) :
    HasSum (fun h : {h // A2dom.Mem h} =>
        (q₀ : ℝ) ^ (-(EA2.eval h.1 : ℤ)))
      ((evalAt q₀ ⟨GA2, hok⟩ : ℚ) : ℝ) := by
  -- part ⌿(b): the Qq clearing identity — evalAt GA2 = q₀²/((q₀⁶−1)(q₀³−1)).
  have h6 : (1 : ℚ) < q₀ ^ 6 := one_lt_pow₀ hq (by norm_num)
  have h3 : (1 : ℚ) < q₀ ^ 3 := one_lt_pow₀ hq (by norm_num)
  have hden : ((Polynomial.X ^ 6 - 1) * (Polynomial.X ^ 3 - 1) : Polynomial ℚ).eval q₀ ≠ 0 := by
    simp only [Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_pow,
      Polynomial.eval_X, Polynomial.eval_one]
    have e1 : q₀ ^ 6 - 1 > 0 := by linarith
    have e2 : q₀ ^ 3 - 1 > 0 := by linarith
    positivity
  have hval : (evalAt q₀ ⟨GA2, hok⟩ : ℚ) = q₀ ^ 2 / ((q₀ ^ 6 - 1) * (q₀ ^ 3 - 1)) := by
    show RatFunc.eval (RingHom.id ℚ) q₀ GA2 = _
    rw [GA2, eval_algebraMap_div q₀ _ _ hden]; simp
  have hvalR : ((evalAt q₀ ⟨GA2, hok⟩ : ℚ) : ℝ)
      = (q₀ : ℝ) ^ (-7 : ℤ) * ((1 - (q₀ : ℝ) ^ (-6 : ℤ))⁻¹ * (1 - (q₀ : ℝ) ^ (-3 : ℤ))⁻¹) := by
    rw [hval]; push_cast; rw [geomValId (q₀ : ℝ) (by exact_mod_cast hq)]
  rw [hvalR]
  -- part ⌿(a): the double geometric sum, reindexed through A2equiv.
  set r : ℝ := (q₀ : ℝ) with hr
  have hr1 : (1 : ℝ) < r := by rw [hr]; exact_mod_cast hq
  have hr0 : (0 : ℝ) < r := by linarith
  have hr0' : r ≠ 0 := ne_of_gt hr0
  have hc6 : (0 : ℝ) ≤ r ^ (-6 : ℤ) := by positivity
  have hc6' : r ^ (-6 : ℤ) < 1 := by
    rw [zpow_neg, show (6 : ℤ) = ((6 : ℕ) : ℤ) from rfl, zpow_natCast, inv_lt_one_iff₀]
    right; exact one_lt_pow₀ hr1 (by norm_num)
  have hc3 : (0 : ℝ) ≤ r ^ (-3 : ℤ) := by positivity
  have hc3' : r ^ (-3 : ℤ) < 1 := by
    rw [zpow_neg, show (3 : ℤ) = ((3 : ℕ) : ℤ) from rfl, zpow_natCast, inv_lt_one_iff₀]
    right; exact one_lt_pow₀ hr1 (by norm_num)
  have hs6 := hasSum_geometric_of_lt_one hc6 hc6'
  have hs3 := hasSum_geometric_of_lt_one hc3 hc3'
  have hsumm : Summable (fun p : ℕ × ℕ => (r ^ (-6 : ℤ)) ^ p.1 * (r ^ (-3 : ℤ)) ^ p.2) :=
    hs6.summable.mul_of_nonneg hs3.summable (fun a => by positivity) (fun b => by positivity)
  have hprod := hs6.mul hs3 hsumm
  have hfull := hprod.mul_left (r ^ (-7 : ℤ))
  rw [← Equiv.hasSum_iff A2equiv]
  refine hfull.congr_fun ?_
  intro p
  simp only [A2equiv, Equiv.coe_fn_mk, Function.comp]
  have hev : EA2.eval ![1 + p.1, p.2] = 7 + 6 * p.1 + 3 * p.2 := by
    simp only [EA2, AffineE.eval, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
    ring
  rw [hev, ← zpow_natCast (r ^ (-6 : ℤ)) p.1, ← zpow_natCast (r ^ (-3 : ℤ)) p.2,
    ← zpow_mul, ← zpow_mul, ← zpow_add₀ hr0', ← zpow_add₀ hr0']
  congr 1; push_cast; ring

end LeanUrat.MovesV
