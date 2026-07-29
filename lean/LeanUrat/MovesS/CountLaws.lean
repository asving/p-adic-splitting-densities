/-
Unit `count_laws` (ratification 2026-07-28 finding 5) — the (iv)-POLY VALUE-LAW
consumption variants.  moves_ref: "K_e/b_e^{term,fin} entries: T is one polynomial
of degree ≤ W_loc(m) and each cell size one polynomial of degree ≤ W_state(s),
valued correctly at every prime power — CTS-M(iv)-POLY (CL-6, with V.2's
EXPONENT-MAP AUDIT)" (MOVES 12129–12132).

The finding: `PolyGeom`'s two count polynomials were semantically untyped — only
the PRODUCT is interpolated (`tg_interp`), so both counts could be set to 1 and
the whole row mass absorbed into `geom` while every displayed degree bound and
interpolation law held.  `PolyGeomLaws` (Defs.lean) types the missing value laws;
THESE variants are the CL-6-facing consumption sites: the same conclusions as
U-9a `ksub_eval` / U-10 `ksub_pool` (statements untouched there), carrying the
value laws as an ADDITIONAL typed premise so the (iv)-POLY burden rides the
K-SUB chain by TYPE.  The premise is deliberately unused by the proofs (the
conclusions genuinely need only the product laws); its presence records CL-6's
count-semantics conditionality at the consuming units, per the charge.
-/
import LeanUrat.MovesS.KsubEval
import LeanUrat.MovesS.KsubPool

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesS

variable {n : ℕ}

/-- U-9a's evaluated (K-SUB) = 1 with the CL-6 count value laws carried as a typed
premise (`ksub_eval`'s statement is byte-identical without `hPGL`). -/
theorem ksub_eval_counted {T : TableShape n} {M : MeasuredSide T}
    (RB : RatBurdens T M) (hPGL : PolyGeomLaws T M RB)
    (L : LedgerIV T M) (hdc : DegCons T) {e : ℕ} (he : e ∈ Finset.Icc 1 n)
    (τ : T.State e) (hK : KmatHyp T e) :
    ∀ q₀ ∈ M.Pools, M.activeState q₀ e τ →
    ∃ hok : (∑ o : T.Out e τ, routedMass RB e τ o) ∈ OKat q₀,
      evalAt q₀ ⟨∑ o : T.Out e τ, routedMass RB e τ o, hok⟩ = 1 :=
  ksub_eval RB L hdc he τ hK

/-- U-10's sub-stochastic active rows with the CL-6 count value laws carried as a
typed premise (`ksub_pool`'s statement is byte-identical without `hPGL`). -/
theorem ksub_pool_counted {T : TableShape n} {M : MeasuredSide T}
    {RB : RatBurdens T M} (hPGL : PolyGeomLaws T M RB)
    {e : ℕ} (he : e ∈ Finset.Icc 1 n) (L : LedgerIV T M)
    {hK : KmatHyp T e} {q₀ : ℚ} (P : PoolHyp T M RB e hK q₀) (τA : P.Act) :
    (∀ βA : P.Act, 0 ≤ Aℝ P τA βA) ∧ (∑ βA : P.Act, Aℝ P τA βA) ≤ 1 :=
  ksub_pool he L P τA

end LeanUrat.MovesS
