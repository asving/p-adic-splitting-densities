/-
Unit Sp.lamEncode [REV 4, Codex-10 — the injectivity spelled in full] —
moves_ref: "λ as its multiplicity matrix c : {1..n}² → {0..n} with c(g, μ) := the
number of factors of shape (g, μ) (n² entries; (B4) forces Σ g·μ·c(g,μ) = ℓ ≤ n)".
sketch: Multiset.ext + the (B5) part bound to shift indices into Fin n; counts
≤ card ≤ ℓ ≤ n gives the {0..n} entry range. difficulty: medium.
-/
import LeanUrat.MovesSp.Defs

set_option linter.style.longLine false
set_option linter.style.header false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesSp

def lamMatrix (n : ℕ) (lam : Multiset (ℕ × ℕ)) : Fin n × Fin n → ℕ :=
  fun gm => lam.count (gm.1.val + 1, gm.2.val + 1)

theorem lamMatrix_inj {n : ℕ} {lam lam' : Multiset (ℕ × ℕ)}
    (hbd : ∀ gm ∈ lam, 1 ≤ gm.1 ∧ gm.1 ≤ n ∧ 1 ≤ gm.2 ∧ gm.2 ≤ n)
    (hbd' : ∀ gm ∈ lam', 1 ≤ gm.1 ∧ gm.1 ≤ n ∧ 1 ≤ gm.2 ∧ gm.2 ≤ n)
    (heq : lamMatrix n lam = lamMatrix n lam') : lam = lam' := sorry

end LeanUrat.MovesSp
