/-
Unit U6.un_bracket  (MovesU campaign)  [RETYPED 2026-07-30 per the ratification]
moves_ref: "(U-n) (R_σ(p) − env(N))·p^{nN} ≤ decided_σ(N) ≤ R_σ(p)·p^{nN}" — "for
           every n, σ, N, and EVERY prime p satisfying (REG-p) … at a p failing
           (REG-p) neither inequality is asserted" (the rev-3 qualifier = the `hreg`
           argument, D8)
deps: U4, U5.
sketch: right leg = U4 (on the typed seams); left leg = U5 applied with
        `R := fun τ => evalℝ S τ p`, `hupper` from U4 at each τ ≠ σ,
        `hsum := ss.rs4_eval P hreg hp hchk` — the DERIVED evaluated checksum
        (ROUND-2 GAP 1: `LowerStack.rs4_eval` retired; only the ℚ(q) checksum
        `hchk` is assumed).
hypothesis_fields: EXACTLY the typed seams (`TreeSeam` + `SolveSeam` + `RegPin`) +
        the ℚ(q) checksum `hchk`; explicit `RegP D`, `p.Prime` (F9).
        CL-2/CL-3 appear NOWHERE (they attach only to the rate form = gate
        SQUEEZE-n3, not a Lean unit).
-/
import Mathlib
import LeanUrat.MovesU.U4_sq2_upper
import LeanUrat.MovesU.U5_sq3_arith

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesU

variable {n p : ℕ} {C : UCarriers n} {X : ClassifierSpec n p} {F : FiberSeries n p X}
  {S : SolveData n} {D : RegData p}

/-- (U-n), the two-sided NON-RATE bracket, on exactly its displayed stacks (now the
    TYPED seams — both operative identities DERIVED, never assumed). -/
theorem un_bracket (seam : TreeSeam n p X F) (ss : SolveSeam n p C F S)
    (P : RegPin C D) (hchk : ∑ σ, S.R σ = 1) (hreg : RegP D) (hp : p.Prime)
    (σ : SplittingType n) (N : ℕ) :
    (evalℝ S σ p - X.env N) * (p : ℝ) ^ (n * N) ≤ (X.decided σ N : ℝ) ∧
    (X.decided σ N : ℝ) ≤ evalℝ S σ p * (p : ℝ) ^ (n * N) := by
  haveI : NeZero p := ⟨hp.pos.ne'⟩
  refine ⟨?_, sq2_upper seam ss P hreg hp σ N⟩
  -- left leg = U5 (SQ.3 arithmetic) with R := evalℝ, hupper from U4,
  -- hsum := the DERIVED evaluated checksum (round-2 GAP 1)
  exact sq3_arith X hp.one_lt (fun τ => evalℝ S τ p) σ N
    (fun τ _ => sq2_upper seam ss P hreg hp τ N) (ss.rs4_eval P hreg hp hchk)

end LeanUrat.MovesU
