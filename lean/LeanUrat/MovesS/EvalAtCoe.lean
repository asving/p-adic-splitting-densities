/-
Unit U-19 `evalAt` (medium) — the OKat/evalAt pair lives in Defs.lean (the E-phase
fill of the §2.C skeleton); this unit carries the coe law `evalAt_coe`.
-/
import LeanUrat.MovesS.Defs

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesS

theorem evalAt_coe (q₀ : ℚ) (f : OKat q₀) :
    evalAt q₀ f = RatFunc.eval (RingHom.id ℚ) q₀ (f : Qq) :=
  rfl

open Polynomial in
/-- Evaluation of a polynomial fraction `p/q` at `x` is `p.eval x / q.eval x`,
whenever `q.eval x ≠ 0`.
[SYN2-S1 SWEEP-2 public hoist, queue item 8, 2026-07-31 — single proof source for the
FOUR ex-private byte-identical copies: `PowSubstOK.eval_algebraMap_div` (the source,
proof verbatim below), `N2PolyGeom.eval_algebraMap_div`, `N2Rsh.eval_algebraMap_div'`,
`MovesV/V0_xhds_witness.eval_algebraMap_div` — all deleted and re-pointed here.
RECORDED NON-ITEM: `N2Sigmas.n2_okat_div`/`n2_evalAt_div` are the ADJACENT OKat/evalAt
idiom (Subtype-valued `evalAt`, OKat-membership form), NOT statement-identical — kept,
per the re-point-if-identical-else-record rubric.] -/
lemma eval_algebraMap_div (x : ℚ) (p q : Polynomial ℚ) (hq : q.eval x ≠ 0) :
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

end LeanUrat.MovesS
