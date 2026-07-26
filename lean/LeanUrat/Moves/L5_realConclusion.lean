import Mathlib
import LeanUrat.Moves.Defs

set_option linter.style.longLine false
set_option linter.style.header false
set_option maxHeartbeats 400000

open Polynomial LeanUrat.Moves

namespace LeanUrat.Moves

/-! # L5.realConclusion (MANIFEST) — MOVES D.9(d)

Any `e_read = 1` side value `λ″ > wPrev(key)` is realizable with any digit scalar
`cc ∈ Kˣ` at position `0`.

Proof: `hS6b` (full `Kˣ` scalars strictly above the parent key weight `wPrev Φ`, DEF-8
threshold) supplies a realizer `B` at parent weight `lam` with residual
`C cc · T (- t · lam)`. The `e = 1` pinning `he1t` forces `t = 0` (P2, DEF-5), so the
position collapses `- t · lam = 0`. -/
theorem L5_realConclusion {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F] (σ : Stage p F) (he1 : σ.e = 1) (lam : ℤ) (hlam : σ.wPrev σ.Φ < lam) (cc : (↥σ.K)ˣ) : ∃ B : Polynomial ℤ_[p], B ≠ 0 ∧ inC σ.Φ B ∧ σ.wPrev B = lam ∧ σ.R B = LaurentPolynomial.C (cc : ↥σ.K) * LaurentPolynomial.T (0 : ℤ) := by
  have ht : σ.t = 0 := σ.he1t he1
  obtain ⟨B, hBne, hBmem, hBw, hBR⟩ := σ.hS6b lam cc hlam
  refine ⟨B, hBne, hBmem, hBw, ?_⟩
  rw [hBR, ht]
  norm_num

end LeanUrat.Moves
