/-
Unit `count_laws` (ratification 2026-07-28 finding 5; RESTATED at S5″ 2026-07-29 per the
Codex confirm FLAG).  moves_ref: "K_e/b_e^{term,fin} entries: T is one polynomial
of degree ≤ W_loc(m) and each cell size one polynomial of degree ≤ W_state(s),
valued correctly at every prime power — CTS-M(iv)-POLY (CL-6, with V.2's
EXPONENT-MAP AUDIT)" (MOVES 12129–12132).

Round-1 defect (confirm, 2026-07-29): "both `_counted` variants accept hPGL but do
not use it" — the laws could be bypassed.  S5″: the variants are RESTATED so their
CONCLUSIONS consume the laws — each concludes the COUNT-FACTORED form of the
Kmat/bTerm entry value at q₀: the countT factor evaluates to `hPGL.tCount` AND the
countS factor evaluates to the `cellInst`/`cellLvl` aggregate over the outcome's
cell fiber, ∧ the previous (uncounted) conclusion.  Strictly stronger than the
uncounted forms and derivable only through `hPGL` (the conclusion NAMES
`hPGL.tCount`; the proofs consume `tcount_val`/`scount_val`).  `PolyGeomLaws` also
now carries the CL-6 DEGREE laws (`tcount_deg`/`scount_deg`, Defs.lean).  tCount
stays interim data; its event-side identification with the CTS/[1] count tables +
V.2's exponent-map audit stays the RECORDED MovesV seam duty (Defs.lean
PolyGeomLaws docstring).  `ksub_eval`/`ksub_pool`/`ksub` statements stay untouched
(U-9a/U-10/U-9b); the counted route is THE route to any count-factored conclusion.
-/
import LeanUrat.MovesS.KsubEval
import LeanUrat.MovesS.KsubPool
import LeanUrat.MovesS.Ksub

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesS

variable {n : ℕ}

/-- The CL-6 count-factored form of the routed row at `(e, τ, q₀)`: the countT factor of
every outcome's tg burden evaluates to the T-table count `hPGL.tCount`, and the countS
factor to the measured cell-size aggregate (cellInst/cellLvl over the outcome's cell
fiber). Only constructible through `hPGL` — this is the (iv)-POLY VALUE content. -/
def CountFactored {T : TableShape n} {M : MeasuredSide T} {RB : RatBurdens T M}
    (hPGL : PolyGeomLaws T M RB) (e : ℕ) (τ : T.State e) (q₀ : ℚ) : Prop :=
  ∀ o : T.Out e τ,
    (RB.tgP e τ o).countT.eval q₀ = (hPGL.tCount e τ o q₀ : ℚ) ∧
    (RB.tgP e τ o).countS.eval q₀
      = ∑ c ∈ M.cells e τ o, ((M.cellInst e τ c q₀ (M.cellLvl e τ c)).card : ℚ)

/-- U-9a's evaluated (K-SUB) = 1, COUNT-FACTORED [S5″]: the uncounted conclusion ∧ the
CL-6 count-factored decomposition of every routed entry at q₀. Strictly stronger than
`ksub_eval`; the count clause is derivable only through `hPGL`. -/
theorem ksub_eval_countFactored {T : TableShape n} {M : MeasuredSide T}
    (RB : RatBurdens T M) (hPGL : PolyGeomLaws T M RB)
    (L : LedgerIV T M) (hdc : DegCons T) {e : ℕ} (he : e ∈ Finset.Icc 1 n)
    (τ : T.State e) (hK : KmatHyp T e) :
    ∀ q₀ ∈ M.Pools, M.activeState q₀ e τ →
    (∃ hok : (∑ o : T.Out e τ, routedMass RB e τ o) ∈ OKat q₀,
        evalAt q₀ ⟨∑ o : T.Out e τ, routedMass RB e τ o, hok⟩ = 1) ∧
      CountFactored hPGL e τ q₀ := by
  intro q₀ hq hact
  exact ⟨ksub_eval RB L hdc he τ hK q₀ hq hact,
    fun o => ⟨hPGL.tcount_val e τ o q₀ hq, hPGL.scount_val e τ o q₀ hq hact⟩⟩

/-- U-10's sub-stochastic active rows, COUNT-FACTORED [S5″]: the uncounted conclusion ∧
the CL-6 count-factored decomposition at the pool's own `q₀` and the active state `τA`.
Strictly stronger than `ksub_pool`; the count clause consumes `hPGL`'s value laws at
`P.pool_mem`/`P.act_spec`. -/
theorem ksub_pool_countFactored {T : TableShape n} {M : MeasuredSide T}
    {RB : RatBurdens T M} (hPGL : PolyGeomLaws T M RB)
    {e : ℕ} (he : e ∈ Finset.Icc 1 n) (L : LedgerIV T M)
    {hK : KmatHyp T e} {q₀ : ℚ} (P : PoolHyp T M RB e hK q₀) (τA : P.Act) :
    ((∀ βA : P.Act, 0 ≤ Aℝ P τA βA) ∧ (∑ βA : P.Act, Aℝ P τA βA) ≤ 1) ∧
      CountFactored hPGL e τA.1 q₀ :=
  ⟨ksub_pool he L P τA,
   fun o => ⟨hPGL.tcount_val e τA.1 o q₀ P.pool_mem,
             hPGL.scount_val e τA.1 o q₀ P.pool_mem ((P.act_spec τA.1).mp τA.2)⟩⟩

/-- U-9b's SYMBOLIC (K-SUB) = 1, COUNT-FACTORED [S5″]: the symbolic row law ∧ the CL-6
count-factored decomposition at EVERY active pool point — the counted-premise variant of
the corpus's CL-6/RS.2 consumer chain (`ksub` feeds Kcol/Ktri/the CTS-M assembly). A
MovesV instantiation wanting CL-6's count semantics on the row MUST route through this
(or its evaluated/pool siblings above): no other export mentions `tCount`. -/
theorem ksub_countFactored {T : TableShape n} {M : MeasuredSide T}
    (RB : RatBurdens T M) (hPGL : PolyGeomLaws T M RB)
    (L : LedgerIV T M) (hdc : DegCons T) {e : ℕ} (he : e ∈ Finset.Icc 1 n)
    (τ : T.State e) (hK : KmatHyp T e) :
    (∑ o : T.Out e τ, routedMass RB e τ o = 1) ∧
      ∀ q₀ ∈ M.Pools, M.activeState q₀ e τ → CountFactored hPGL e τ q₀ :=
  ⟨ksub RB L hdc he τ hK,
   fun q₀ hq hact o =>
     ⟨hPGL.tcount_val e τ o q₀ hq, hPGL.scount_val e τ o q₀ hq hact⟩⟩

end LeanUrat.MovesS
