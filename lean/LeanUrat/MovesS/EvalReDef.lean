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

/-- One MEASURED branch-member leg factor (the ℝ analogue of U-16a1's `legFactor`):
verdict-halted members contribute the σ_j-singleton indicator (factor 1 / verdict
convention, §T.4); continuing members contribute the MEASURED value `βhat` of the
smaller block at the pool `q₀ ^ (δ:ℕ)` (DELTA-ABS base-change).  D-2 guard: the
member-size bound `size ∈ Icc 1 n` is a `dite` (else 0) — under `DegCons` + U-2 it
always holds on split outcomes, but threading that in would have made the
DEFINITION depend on U-2, which was still sorried at E-phase (as-built note,
2026-07-30 verify-2 fold-in: `ktri` is now proved sorry-free in Ktri.lean; the
guard shape is kept as the historical D-2 rationale). -/
noncomputable def legFactorMeas (T : TableShape n) (e : ℕ) (τ : T.State e)
    (o : T.Out e τ) (q₀ : ℚ)
    (βhat : ∀ e', e' ∈ Finset.Icc 1 n → T.State e' → Multiset T.VType → ℚ → ℝ)
    (g : Fin (T.odata e τ o).mem.length → Multiset T.VType)
    (j : Fin (T.odata e τ o).mem.length) : ℝ :=
  match ((T.odata e τ o).mem.get j).status with
  | Sum.inl v => if g j = {v} then 1 else 0
  | Sum.inr τ' =>
      if hsz : ((T.odata e τ o).mem.get j).size ∈ Finset.Icc 1 n
      then βhat ((T.odata e τ o).mem.get j).size hsz τ' (g j)
             (q₀ ^ (((T.odata e τ o).mem.get j).δ : ℕ))
      else 0

/-- The evaluated `b_e^{term,fin}(σ′)` at `q₀` (measured value of each terminal
column via `M.rowVal`; the ℝ image of `bTerm`, by `tg_interp`). -/
noncomputable def bTermMeas (T : TableShape n) (M : MeasuredSide T) (e : ℕ)
    (σ' : Multiset T.VType) (q₀ : ℚ) (τ : T.State e) : ℝ :=
  ∑ o : T.Out e τ,
    if routeOf (T.odata e τ o) = .termFin ∧ (T.odata e τ o).verdicts = σ'
    then M.rowVal e τ o q₀ else 0

/-- The evaluated `b_e^{split}(σ′)` at `q₀` with MEASURED legs (the split branching
sum: measured branch weight `M.rowVal` — the ℝ image of `J`, by `j_interp` — times
the decomposition sum of the measured leg products). -/
noncomputable def bSplitMeas (T : TableShape n) (M : MeasuredSide T) (e : ℕ)
    (σ' : Multiset T.VType) (q₀ : ℚ)
    (βhat : ∀ e', e' ∈ Finset.Icc 1 n → T.State e' → Multiset T.VType → ℚ → ℝ)
    (τ : T.State e) : ℝ :=
  ∑ o ∈ splitOuts T e τ, M.rowVal e τ o q₀ *
    ∑ g : {g : Fin (T.odata e τ o).mem.length → Multiset T.VType // σ' = ∑ j, g j},
      ∏ j, legFactorMeas T e τ o q₀ βhat g.1 j

/-- The evaluated (R_e-lump) right side at pool q₀, with measured legs. -/
noncomputable def evalRe (T : TableShape n) (M : MeasuredSide T)
    (RB : RatBurdens T M) (hdc : DegCons T) (e : ℕ) (he : e ∈ Finset.Icc 1 n)
    (τ : T.State e) (σ' : Multiset T.VType) (q₀ : ℚ)
    (βhat : ∀ e', e' ∈ Finset.Icc 1 n → T.State e' → Multiset T.VType → ℚ → ℝ) : ℝ :=
  (∑ β : T.State e, M.kstep 1 e τ β q₀ * βhat e he β σ' q₀)
    + bTermMeas T M e σ' q₀ τ
    + bSplitMeas T M e σ' q₀ βhat τ

/-- The Act-restricted evaluated exit vector (terminal columns + split summand with
measured legs at q₀^δ); U-24a1's b̂. -/
noncomputable def bhatMeas {T : TableShape n} {M : MeasuredSide T}
    {RB : RatBurdens T M} {e : ℕ} {hK : KmatHyp T e} {q₀ : ℚ}
    (P : PoolHyp T M RB e hK q₀)
    (βhat : ∀ e', e' ∈ Finset.Icc 1 n → T.State e' → Multiset T.VType → ℚ → ℝ)
    (σ' : Multiset T.VType) : P.Act → ℝ :=
  fun τA => bTermMeas T M e σ' q₀ τA.1 + bSplitMeas T M e σ' q₀ βhat τA.1

end LeanUrat.MovesS
