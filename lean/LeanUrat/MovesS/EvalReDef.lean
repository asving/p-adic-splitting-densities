/-
Unit U-16a2 `evalRe_def` (medium) — the per-pool EVALUATED right side of (R_e-lump)
that `recursion_meas` cites: eval-K-row · β̂ + eval-bTerm + the evaluated split
summand with MEASURED legs β̂ at q₀^(δ:ℕ) (well-typed by `pools_closed`; halted legs
the same indicator as U-16a1) — AND `bhatMeas`, its Act-restricted exit-vector face
(consumed by U-24a1/a2 and `ReadOffBundle`).  R25: `bhatMeas` is declared HERE.
E-PHASE NOTE (deviation D-1): `bhatMeas` takes the raw measured β-family (curried)
rather than the RS1Bundle — the bundle is declared later, in Interfaces.lean; use
sites pass `fun e' he' => B.βmeas e' he' h_ent`.
-/
import LeanUrat.MovesS.Defs
import LeanUrat.MovesS.BSplitDef

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesS

variable {n : ℕ}

/-- The evaluated (R_e-lump) right side at pool q₀, with measured legs. -/
noncomputable def evalRe (T : TableShape n) (M : MeasuredSide T)
    (RB : RatBurdens T M) (hdc : DegCons T) (e : ℕ) (he : e ∈ Finset.Icc 1 n)
    (τ : T.State e) (σ' : Multiset T.VType) (q₀ : ℚ)
    (βhat : ∀ e', e' ∈ Finset.Icc 1 n → T.State e' → Multiset T.VType → ℚ → ℝ) : ℝ :=
  sorry

/-- The Act-restricted evaluated exit vector (terminal columns + split summand with
measured legs at q₀^δ); U-24a1's b̂. -/
noncomputable def bhatMeas {T : TableShape n} {M : MeasuredSide T}
    {RB : RatBurdens T M} {e : ℕ} {hK : KmatHyp T e} {q₀ : ℚ}
    (P : PoolHyp T M RB e hK q₀)
    (βhat : ∀ e', e' ∈ Finset.Icc 1 n → T.State e' → Multiset T.VType → ℚ → ℝ)
    (σ' : Multiset T.VType) : P.Act → ℝ :=
  sorry

end LeanUrat.MovesS
