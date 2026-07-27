/-
Unit U9.lmeas  (MovesU campaign)  [conditional on `rs4_eval` only, at consumption]
moves_ref: "(L-meas) … by (BOX-N), for fixed σ this leg is EQUIVALENT to the
           AGGREGATE inequality Σ_{τ≠σ} d_τ ≤ Σ_{τ≠σ} R_τ(p) … It is IMPLIED BY —
           not equivalent to — the conjunction {SQ.2 at every τ ≠ σ} + RS.4's
           checksum" (rev 2, pass-1 critical 5)
deps: U1, U4.
sketch: `lmeas_equiv`: divide U1 by `p^{nN}` and rearrange (`Finset.add_sum_erase`,
        `hsum`); `lmeas_implied`: `Finset.sum_le_sum` — ONE direction only,
        faithfully: no converse is stated anywhere (per-τ violations can cancel;
        the note's honesty).
hypothesis_fields: none as stated (`R : SplittingType n → ℝ` abstract, `hsum`
        explicit); at consumption `R := evalℝ`, `hsum := rs4_eval` — the gate-layer
        reading, recorded for SQUEEZE-n3's (L-meas) leg semantics only (the gate
        itself is NOT a Lean unit). `1 < p` scaffolding as at U5 (G6).
-/
import Mathlib
import LeanUrat.MovesU.U1_boxN
import LeanUrat.MovesU.U4_sq2_upper

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesU

variable {n p : ℕ} {X : ClassifierSpec n p} {R : SplittingType n → ℝ}

/-- (L-meas)'s retype, the EQUIVALENCE leg: for fixed σ, N the lower bracket leg is
    equivalent (by (BOX-N)) to the aggregate τ ≠ σ inequality. -/
theorem lmeas_equiv [NeZero p] (hp : 1 < p) (σ : SplittingType n) (N : ℕ)
    (hsum : ∑ τ, R τ = 1) :
    ((R σ - X.env N) * (p : ℝ) ^ (n * N) ≤ (X.decided σ N : ℝ)) ↔
      (∑ τ ∈ Finset.univ.erase σ, X.dmass τ N ≤ ∑ τ ∈ Finset.univ.erase σ, R τ) :=
  sorry

/-- (L-meas)'s IMPLIED-BY leg — ONE direction only, faithfully (no converse is
    stated anywhere: per-τ violations can cancel). -/
theorem lmeas_implied (σ : SplittingType n) (N : ℕ)
    (hupper : ∀ τ, τ ≠ σ → X.dmass τ N ≤ R τ) :
    ∑ τ ∈ Finset.univ.erase σ, X.dmass τ N ≤ ∑ τ ∈ Finset.univ.erase σ, R τ :=
  sorry

end LeanUrat.MovesU
