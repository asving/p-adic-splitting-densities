/-
Unit U-24b `rs2_unique_interp` (medium) — locus = the ALL-ACTIVE primes (R16(ii)).
moves_ref: "at all-active primes (cofinitely many — only finitely many primes are
roots of some not-identically-zero cell-size polynomial)" (S.4(ii)); RS.2's
"every β_{e,τ}(σ′) is ONE FIXED rational function" is claimed exactly there.
COORDINATE COVERAGE: at an all-active pool EVERY (e, τ) is active, so each
coordinate's identification set is ALL of S; the conclusion's family and
`ReadOffBundle`'s coverage quantify identically (e, τ, σ').  hyp: hread (the
per-pool (ii-c) burden, OPEN — provenance W-6).  deps: U-24a1, U-24a2, U-18b, U-27.
-/
import LeanUrat.MovesS.ReadOff
import LeanUrat.MovesS.InterpUnique
import LeanUrat.MovesS.RatfuncEvalInfinite

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesS

variable {n : ℕ}

theorem rs2_unique_interp {T : TableShape n} {M : MeasuredSide T}
    {RB : RatBurdens T M} {hdc : DegCons T}
    {hK : ∀ e, e ∈ Finset.Icc 1 n → KmatHyp T e}
    (S : Set ℚ) (hS : S ⊆ allActivePools M) (hinf : S.Infinite)
    (B : RS1Bundle T M RB hdc hK) (hdet : DetHyp T RB hK)
    (hread : ReadOffBundle S hS B hdet)
    (f : ∀ e, e ∈ Finset.Icc 1 n → T.State e → Multiset T.VType → Qq)
    (hfok : ∀ e (he : e ∈ Finset.Icc 1 n) (τ : T.State e)
      (σ' : Multiset T.VType) (q₀ : ℚ), q₀ ∈ S → f e he τ σ' ∈ OKat q₀)
    (hfin : ∀ e (he : e ∈ Finset.Icc 1 n) (τ : T.State e)
      (σ' : Multiset T.VType) (q₀ : ℚ) (hq : q₀ ∈ S) (h_ent : ℕ),
      ((evalAt q₀ ⟨f e he τ σ', hfok e he τ σ' q₀ hq⟩ : ℚ) : ℝ)
        = B.βmeas e he h_ent τ σ' q₀) :
    ∀ e (he : e ∈ Finset.Icc 1 n) (τ : T.State e) (σ' : Multiset T.VType),
      f e he τ σ' = blockSolve T RB hdc hK hdet e he τ σ' :=
  sorry

end LeanUrat.MovesS
