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
    (R σ - X.env N) * (p : ℝ) ^ (n * N) ≤ (X.decided σ N : ℝ) := by
  -- Notation: P := p^{nN} (strictly positive, hence nonzero).
  have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast Nat.zero_lt_one.trans hp
  have hP : (0 : ℝ) < (p : ℝ) ^ (n * N) := pow_pos hp0 _
  have hPne : (p : ℝ) ^ (n * N) ≠ 0 := ne_of_gt hP
  -- (BOX-N) from U1, cast to ℝ.
  have hbox := boxN X N
  have hboxR : (∑ τ : SplittingType n, (X.decided τ N : ℝ)) + (X.undec N : ℝ)
      = (p : ℝ) ^ (n * N) := by exact_mod_cast hbox
  -- Split the decided sum at σ.
  have hsplit := Finset.add_sum_erase Finset.univ
    (fun τ => (X.decided τ N : ℝ)) (Finset.mem_univ σ)
  -- Split the R-sum at σ (so ∑_{τ≠σ} R τ = 1 - R σ).
  have hRsplit := Finset.add_sum_erase Finset.univ R (Finset.mem_univ σ)
  rw [hsum] at hRsplit
  -- Bound the erased decided sum by the erased R-sum times P.
  have hbound : (∑ τ ∈ Finset.univ.erase σ, (X.decided τ N : ℝ))
      ≤ (∑ τ ∈ Finset.univ.erase σ, R τ) * (p : ℝ) ^ (n * N) := by
    rw [Finset.sum_mul]
    apply Finset.sum_le_sum
    intro τ hτ
    exact hupper τ (Finset.ne_of_mem_erase hτ)
  -- env(N) · P = undec(N).
  have henv : (X.env N) * (p : ℝ) ^ (n * N) = (X.undec N : ℝ) := by
    unfold ClassifierSpec.env
    exact div_mul_cancel₀ _ hPne
  -- Turn the erased R-sum·P into (1 - R σ)·P.
  have hRr : (∑ τ ∈ Finset.univ.erase σ, R τ) * (p : ℝ) ^ (n * N)
      = (p : ℝ) ^ (n * N) - R σ * (p : ℝ) ^ (n * N) := by
    have : (∑ τ ∈ Finset.univ.erase σ, R τ) = 1 - R σ := by linarith [hRsplit]
    rw [this]; ring
  rw [sub_mul]
  linarith [hboxR, hsplit, hbound, henv, hRr]

end LeanUrat.MovesU
