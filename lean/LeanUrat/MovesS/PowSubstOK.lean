/-
Unit U-12b `powSubst_OKat_evalAt` (easy) — OK-membership and evaluation transport
along a base-change leg q₀ ↦ q₀^δ (serves R14).  sketch: the denominator of
`powSubst δ f` divides `f.denom.comp (X^δ)`, and `(f.denom.comp (X^δ)).eval q₀ =
f.denom.eval (q₀^δ) ≠ 0`; `Polynomial.eval_comp` + denominator divisibility under
ring homs.
-/
import LeanUrat.MovesS.Defs
import LeanUrat.MovesS.PowSubst

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesS
open Polynomial

/-- `powSubst δ` on a polynomial image is the polynomial base-change `p ↦ p ∘ X^δ`
(pushed back into `Qq`).  Follows from `powSubst_X`/`powSubst_C` + ring-hom extension. -/
private lemma powSubst_algebraMap (δ : ℕ+) (p : Polynomial ℚ) :
    powSubst δ (algebraMap (Polynomial ℚ) Qq p)
      = algebraMap (Polynomial ℚ) Qq (p.comp (X ^ (δ : ℕ))) := by
  have hFG : (powSubst δ).comp (algebraMap (Polynomial ℚ) Qq)
      = (algebraMap (Polynomial ℚ) Qq).comp
          (Polynomial.eval₂RingHom Polynomial.C (X ^ (δ : ℕ))) := by
    apply Polynomial.ringHom_ext
    · intro a
      simp only [RingHom.comp_apply, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C,
        RatFunc.algebraMap_C, powSubst_C]
    · simp only [RingHom.comp_apply, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X,
        powSubst_X]
  have h := RingHom.congr_fun hFG p
  simpa only [RingHom.comp_apply, Polynomial.coe_eval₂RingHom, Polynomial.comp] using h

/-- Evaluation of a polynomial fraction `p/q` at `x` is `p.eval x / q.eval x`,
whenever `q.eval x ≠ 0`. -/
private lemma eval_algebraMap_div (x : ℚ) (p q : Polynomial ℚ) (hq : q.eval x ≠ 0) :
    RatFunc.eval (RingHom.id ℚ) x
        (algebraMap (Polynomial ℚ) Qq p / algebraMap (Polynomial ℚ) Qq q)
      = p.eval x / q.eval x := by
  have hq0 : q ≠ 0 := fun h0 => hq (by simp [h0])
  have hqne : algebraMap (Polynomial ℚ) Qq q ≠ 0 := RatFunc.algebraMap_ne_zero hq0
  have hdvd : (algebraMap (Polynomial ℚ) Qq p
      / algebraMap (Polynomial ℚ) Qq q).denom ∣ q :=
    (RatFunc.denom_dvd hq0).mpr ⟨p, rfl⟩
  have hgden : Polynomial.eval₂ (RingHom.id ℚ) x
      (algebraMap (Polynomial ℚ) Qq p / algebraMap (Polynomial ℚ) Qq q).denom ≠ 0 := by
    rw [Polynomial.eval₂_id]
    obtain ⟨c, hc⟩ := hdvd
    intro hz
    exact hq (by rw [hc, Polynomial.eval_mul, hz, zero_mul])
  have hden_q : Polynomial.eval₂ (RingHom.id ℚ) x
      (algebraMap (Polynomial ℚ) Qq q).denom ≠ 0 := by
    rw [RatFunc.denom_algebraMap]; simp
  have epq : RatFunc.eval (RingHom.id ℚ) x (algebraMap (Polynomial ℚ) Qq p) = p.eval x := by
    rw [RatFunc.eval_algebraMap]; simp [Polynomial.eval₂_id]
  have eqq : RatFunc.eval (RingHom.id ℚ) x (algebraMap (Polynomial ℚ) Qq q) = q.eval x := by
    rw [RatFunc.eval_algebraMap]; simp [Polynomial.eval₂_id]
  have hmul : (algebraMap (Polynomial ℚ) Qq p / algebraMap (Polynomial ℚ) Qq q)
      * algebraMap (Polynomial ℚ) Qq q = algebraMap (Polynomial ℚ) Qq p :=
    div_mul_cancel₀ _ hqne
  have key := congrArg (RatFunc.eval (RingHom.id ℚ) x) hmul
  rw [RatFunc.eval_mul (RingHom.id ℚ) x hgden hden_q, epq, eqq] at key
  rw [eq_div_iff hq]
  exact key

theorem powSubst_OKat (δ : ℕ+) (q₀ : ℚ) (f : Qq) (h : f ∈ OKat (q₀ ^ (δ : ℕ))) :
    powSubst δ f ∈ OKat q₀ := by
  rw [mem_OKat_iff] at h ⊢
  have hf : powSubst δ f
      = algebraMap (Polynomial ℚ) Qq (f.num.comp (X ^ (δ : ℕ)))
        / algebraMap (Polynomial ℚ) Qq (f.denom.comp (X ^ (δ : ℕ))) := by
    conv_lhs => rw [← RatFunc.num_div_denom f]
    rw [map_div₀, powSubst_algebraMap, powSubst_algebraMap]
  have hDe : (f.denom.comp (X ^ (δ : ℕ))).eval q₀ = f.denom.eval (q₀ ^ (δ : ℕ)) := by
    rw [Polynomial.eval_comp, Polynomial.eval_pow, Polynomial.eval_X]
  have hDe' : (f.denom.comp (X ^ (δ : ℕ))).eval q₀ ≠ 0 := hDe ▸ h
  have hDne : f.denom.comp (X ^ (δ : ℕ)) ≠ 0 := fun h0 => hDe' (by simp [h0])
  have hdvd : (powSubst δ f).denom ∣ f.denom.comp (X ^ (δ : ℕ)) := by
    rw [hf]
    exact (RatFunc.denom_dvd hDne).mpr ⟨f.num.comp (X ^ (δ : ℕ)), rfl⟩
  obtain ⟨c, hc⟩ := hdvd
  intro hzero
  exact hDe' (by rw [hc, Polynomial.eval_mul, hzero, zero_mul])

theorem powSubst_evalAt (δ : ℕ+) (q₀ : ℚ) (f : Qq) (h : f ∈ OKat (q₀ ^ (δ : ℕ))) :
    evalAt q₀ ⟨powSubst δ f, powSubst_OKat δ q₀ f h⟩ = evalAt (q₀ ^ (δ : ℕ)) ⟨f, h⟩ := by
  have hh : f.denom.eval (q₀ ^ (δ : ℕ)) ≠ 0 := mem_OKat_iff.mp h
  have hcoeL : evalAt q₀ ⟨powSubst δ f, powSubst_OKat δ q₀ f h⟩
      = RatFunc.eval (RingHom.id ℚ) q₀ (powSubst δ f) := rfl
  have hcoeR : evalAt (q₀ ^ (δ : ℕ)) ⟨f, h⟩
      = RatFunc.eval (RingHom.id ℚ) (q₀ ^ (δ : ℕ)) f := rfl
  rw [hcoeL, hcoeR]
  have hf : powSubst δ f
      = algebraMap (Polynomial ℚ) Qq (f.num.comp (X ^ (δ : ℕ)))
        / algebraMap (Polynomial ℚ) Qq (f.denom.comp (X ^ (δ : ℕ))) := by
    conv_lhs => rw [← RatFunc.num_div_denom f]
    rw [map_div₀, powSubst_algebraMap, powSubst_algebraMap]
  have hDe : (f.denom.comp (X ^ (δ : ℕ))).eval q₀ = f.denom.eval (q₀ ^ (δ : ℕ)) := by
    rw [Polynomial.eval_comp, Polynomial.eval_pow, Polynomial.eval_X]
  have hNe : (f.num.comp (X ^ (δ : ℕ))).eval q₀ = f.num.eval (q₀ ^ (δ : ℕ)) := by
    rw [Polynomial.eval_comp, Polynomial.eval_pow, Polynomial.eval_X]
  rw [hf, eval_algebraMap_div q₀ (f.num.comp (X ^ (δ : ℕ))) (f.denom.comp (X ^ (δ : ℕ)))
        (by rw [hDe]; exact hh), hNe, hDe]
  conv_rhs => rw [← RatFunc.num_div_denom f]
  rw [eval_algebraMap_div (q₀ ^ (δ : ℕ)) f.num f.denom hh]

end LeanUrat.MovesS
