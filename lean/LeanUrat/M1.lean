/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.Interface

/-!
# LeanUrat.M1 — the monic → projective density bridge (`notes/M1_bridge.md`)

**Cleaned 2026-06-15.** Removed two vacuous declarations: `symPow_P1_count` (stated as `X = X := rfl`
— the crux `#(Sym^n P^1) = |P^n|` never actually appeared) and `monic_to_projective` (a
`(h : P) : P := h` tautology). The genuine bridge content (`ρ = (1/|P^n(F_q)|)·Σ_D W_D[σ]` and the
crux count `Sym^n P^1 = P^n`) is a cited combinatorial/measure fact; it is **not** faked here, and
the Goal does not depend on it (the Goal's rationality flows through `L6M4` + the named axioms). A
future module may state `Sym^n P^1 = P^n` as a real cardinality theorem.

What remains is genuinely proved: the projective normalization constant and the (definitional)
reciprocal cluster-law identities `L_e^{(δ)}(q) = L_e^{(1)}(q^δ) = α(e; q^{-δ})` (the `q ↦ 1/q`
chart swap that makes monic non-palindromic but projective palindromic).
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false

namespace LeanUrat.M1

open Polynomial

/-- `|P^n(F_q)| = 1 + q + ⋯ + q^n`, the projective normalization constant (a palindromic form). -/
def projPointCount (n q : ℕ) : ℕ := ∑ i ∈ Finset.range (n + 1), q ^ i

/-- `(q - 1)·|P^n(F_q)| = q^{n+1} - 1` (PROVED, over `ℚ`). -/
theorem projPointCount_mul (n q : ℕ) :
    ((q : ℚ) - 1) * (projPointCount n q : ℚ) = (q : ℚ) ^ (n + 1) - 1 := by
  push_cast [projPointCount]
  exact mul_geom_sum (q : ℚ) (n + 1)

/-- `|P^n(F_q)| > 0` (PROVED): the bridge denominator never vanishes at prime powers. -/
theorem projPointCount_pos (n q : ℕ) : 0 < projPointCount n q :=
  Finset.sum_pos' (fun _ _ => Nat.zero_le _)
    ⟨0, Finset.mem_range.mpr n.succ_pos, Nat.one_pos⟩

/-- `|P^n(F_1)| = n + 1` (PROVED): the `q → 1` degeneration `(q^{n+1}-1)/(q-1) → n+1`. -/
theorem projPointCount_one (n : ℕ) : projPointCount n 1 = n + 1 := by
  simp [projPointCount]

/-- The intrinsic cluster law `L_e^{(δ)}(q)[σ] := α(e, σ; (q^δ)⁻¹)` — the monic density family `α`
read at the reciprocal of the base-changed residue size (`notes/M1_bridge.md §2.1`, paper
`eqn: symmetry for alpha` `β(e;q)=α(e;1/q)` composed with unramified descent `q ↦ q^δ`). A
*definition*, so the two identities below are definitional (and honestly so). -/
def clusterLaw (α : ℕ → FactorizationType → ℚ → ℚ) (e δ : ℕ) (σ : FactorizationType) (q : ℚ) : ℚ :=
  α e σ (((q ^ δ))⁻¹)

/-- Base-change of the cluster law: `L_e^{(δ)}(q) = L_e^{(1)}(q^δ)` (definitional identity of
`clusterLaw`). -/
theorem clusterLaw_baseChange (α : ℕ → FactorizationType → ℚ → ℚ)
    (e δ : ℕ) (σ : FactorizationType) (q : ℚ) :
    clusterLaw α e δ σ q = clusterLaw α e 1 σ (q ^ δ) := by
  unfold clusterLaw; rw [pow_one]

/-- The reciprocal read `L_e^{(1)}(q) = α(e, σ; q⁻¹)` (the `q ↦ 1/q` chart swap; definitional). -/
theorem clusterLaw_reciprocal (α : ℕ → FactorizationType → ℚ → ℚ)
    (e : ℕ) (σ : FactorizationType) (q : ℚ) :
    clusterLaw α e 1 σ q = α e σ q⁻¹ := by
  unfold clusterLaw; rw [pow_one]

end LeanUrat.M1
