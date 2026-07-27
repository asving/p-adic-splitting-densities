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
    (heq : lamMatrix n lam = lamMatrix n lam') : lam = lam' := by
  ext a
  obtain ⟨g, μ⟩ := a
  by_cases hg : 1 ≤ g ∧ g ≤ n ∧ 1 ≤ μ ∧ μ ≤ n
  · obtain ⟨hg1, hgn, hμ1, hμn⟩ := hg
    have hi : g - 1 < n := by omega
    have hj : μ - 1 < n := by omega
    have hcong := congrFun heq (⟨g - 1, hi⟩, ⟨μ - 1, hj⟩)
    simp only [lamMatrix] at hcong
    have e1 : (g - 1) + 1 = g := by omega
    have e2 : (μ - 1) + 1 = μ := by omega
    rw [e1, e2] at hcong
    exact hcong
  · have h1 : (g, μ) ∉ lam := fun hm => hg (hbd _ hm)
    have h2 : (g, μ) ∉ lam' := fun hm => hg (hbd' _ hm)
    rw [Multiset.count_eq_zero.mpr h1, Multiset.count_eq_zero.mpr h2]

end LeanUrat.MovesSp
