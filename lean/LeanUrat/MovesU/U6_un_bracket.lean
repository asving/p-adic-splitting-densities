/-
Unit U6.un_bracket  (MovesU campaign)  [conditional; the note's product]
moves_ref: "(U-n) (R_σ(p) − env(N))·p^{nN} ≤ decided_σ(N) ≤ R_σ(p)·p^{nN}" — "for
           every n, σ, N, and EVERY prime p satisfying (REG-p) … at a p failing
           (REG-p) neither inequality is asserted" (the rev-3 qualifier = the `hreg`
           argument, D8)
deps: U4, U5.
sketch: right leg = U4 (on FS, SS); left leg = U5 applied with
        `R := fun τ => evalℝ S τ p`, `hupper` from U4 at each τ ≠ σ,
        `hsum := LS.rs4_eval hreg`. (`NeZero p`/`1 < p` derived from `hp` inside.)
hypothesis_fields: EXACTLY `FinStack` + `SolveStack` + `LowerStack` (the lower side's
        "additionally GIVEN RS.4's inherited set (X.3/CL-4 included)", D12 —
        REV 5/Codex-FINAL 3: CL-2/CL-3 appear NOWHERE; they attach only to the rate
        form = gate SQUEEZE-n3, not a Lean unit); explicit `RegP S D`, `p.Prime` (F9).
-/
import Mathlib
import LeanUrat.MovesU.U4_sq2_upper
import LeanUrat.MovesU.U5_sq3_arith

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesU

variable {n p : ℕ} {X : ClassifierSpec n p} {F : FiberSeries n p X}
  {S : SolveData n} {D : RegData p} {M : MenuData} {K : KernelStatements}

/-- (U-n), the two-sided NON-RATE bracket, on exactly its displayed stacks. -/
theorem un_bracket (FS : FinStack n p X F K) (SS : SolveStack n p X F S D M K)
    (LS : LowerStack n p S D K) (hreg : RegP S D) (hp : p.Prime)
    (σ : SplittingType n) (N : ℕ) :
    (evalℝ S σ p - X.env N) * (p : ℝ) ^ (n * N) ≤ (X.decided σ N : ℝ) ∧
    (X.decided σ N : ℝ) ≤ evalℝ S σ p * (p : ℝ) ^ (n * N) := by
  haveI : NeZero p := ⟨hp.pos.ne'⟩
  refine ⟨?_, sq2_upper FS SS hreg hp σ N⟩
  -- left leg = U5 (SQ.3 arithmetic) with R := evalℝ, hupper from U4, hsum := RS.4's eval sum
  exact sq3_arith X hp.one_lt (fun τ => evalℝ S τ p) σ N
    (fun τ _ => sq2_upper FS SS hreg hp τ N) (LS.rs4_eval hreg)

end LeanUrat.MovesU
