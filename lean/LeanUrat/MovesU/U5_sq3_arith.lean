/-
Unit U5.sq3_arith  (MovesU campaign)  [TAG-FREE step 2]
moves_ref: "decided_σ(N) = p^{nN} − Σ_{τ≠σ} decided_τ(N) − undec(N) ≥
           p^{nN}·(1 − Σ_{τ≠σ} R_τ(p) − env(N)) = (R_σ(p) − env(N))·p^{nN}" (SQ.3)
deps: U1.
sketch: cast U1's (BOX-N) to ℝ; `Finset.sum_erase_add`/`sub` bookkeeping; `env`
        unfolds to `undec/p^{nN}` with `div_mul_cancel₀` (`p^{nN} ≠ 0` from `hp`);
        finish by `linarith` over the τ ≠ σ sum of `hupper` + `hsum`. Pure ℝ
        arithmetic: no ledger, no RegP — the inputs carry the tags, as the note's
        re-audit says.
hypothesis_fields: none (tag-free as an implication; instantiated at U6 with tagged
        inputs). `1 < p` here is ARITHMETIC SCAFFOLDING — p^{nN} ≠ 0 — not the
        note's quantifier; the note's display is asserted only through U6/U10, at
        primes (G6).
-/
import Mathlib
import LeanUrat.MovesU.U1_boxN

set_option linter.style.longLine false
set_option linter.style.header false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesU

/-- SQ.3's bracket arithmetic AS arithmetic: every tagged input an EXPLICIT argument —
    the tag-free content is the implication. -/
theorem sq3_arith {n p : ℕ} (X : ClassifierSpec n p) [NeZero p] (hp : 1 < p)
    (R : SplittingType n → ℝ) (σ : SplittingType n) (N : ℕ)
    (hupper : ∀ τ, τ ≠ σ → (X.decided τ N : ℝ) ≤ R τ * (p : ℝ) ^ (n * N))
    (hsum : ∑ τ, R τ = 1) :
    (R σ - X.env N) * (p : ℝ) ^ (n * N) ≤ (X.decided σ N : ℝ) :=
  sorry

end LeanUrat.MovesU
