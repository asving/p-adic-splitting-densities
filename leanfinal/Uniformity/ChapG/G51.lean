/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapG.G48
import Uniformity.ChapG.G50
import Uniformity.Density.Statement

/-!
# Uniformity.ChapG.G51 — `uniformityStatement_two`, THE CAPSTONE AT `n = 2`

**Chapter G, NODE G.51** (`blueprint/CHAP-G_base_cases_menus.md` §7), the chapter's payoff. For
every degree-2 splitting type there is ONE rational function of `q` — a single pair
`(num, den) : Polynomial ℚ × Polynomial ℚ`, chosen before any ring is named — such that
`genuineDensity O 2 σ = num(q)/den(q)` at EVERY complete DVR `O` with finite residue field of
cardinality `q`. That `∃ (num, den)` standing OUTSIDE the `∀ O` *is* the uniformity claim: one
law, all primes, wild ones included, both characteristics.

The three rational functions:

| `σ` | `num` | `den` | value |
| --- | ----- | ----- | ----- |
| `splitType` | `X` | `2*(X + 1)` | `q/(2(q+1))` |
| `inertType` | `X` | `2*(X + 1)` | `q/(2(q+1))` |
| `ramType` | `1` | `X + 1` | `1/(q+1)` |
| any other degree-2 type | `0` | `1` | `0` |

DEPENDS: G.48 (`genuineDensity_two_exact`), G.50 (`degree_two_type_cases`) · landed
`UniformityStatement` (`Statement.lean:71`) for the statement shape, `two_le_residueCard`
(`LocalData.lean:84`).

**PROOF.**
1. `rcases degree_two_type_cases hσ` (G.50) into the four cases.
2. split and inert: `num := X`, `den := 2*(X + 1)`. `den ≠ 0` by evaluating at `0` (it gives
   `2 ≠ 0`); `den.eval q = 2*(q+1) ≠ 0` because `2 ≤ q` (`two_le_residueCard`, cast to `ℚ`); the
   value is G.48's first two conjuncts with the `ℚ → ℝ` coercion pushed by `push_cast`.
3. ram: `num := 1`, `den := X + 1`, same shape.
4. the fourth case: `num := 0`, `den := 1`; the value is `0` by G.50's fourth disjunct applied
   at `O`.

**⚠ THE HONESTY RIDER — WHAT THIS IS AND IS NOT.** This is the `n = 2` slice of the repo's
capstone target, proved: unconditional, no drainage hypothesis, no axiom, Lean core only. It is
**NOT** `UniformityStatement`, which quantifies over ALL `n > 0`; the general statement needs
every degree, and this node supplies exactly one of them. **Nobody may record "the capstone is
proved" on the strength of this node.** The honest sentence is:

> *the uniformity theorem is proved at `n = 1` (landed, `Gates.lean`) and at `n = 2` (this node),
> unconditionally, over every complete DVR with finite residue field.*

**⚠ ARITHMETIC CROSS-CHECK.** `2·q/(2(q+1)) + 1/(q+1) = 1` ✓, matching the landed
`sum_three_densities_eq_one`; at `q = 2` the three values are `1/3, 1/3, 1/3` and at `q = 3` they
are `3/8, 3/8, 1/4`, which is exactly G.49.

**TEETH.** `W11-ORACLE` (per-polynomial PARI on 8,252 polynomials) → executable regression;
`gate_bracket_w11_two`/`_three` → Lean theorem.

## Status

Sorry-free, axiom-free (Lean core only). No section variables: the statement carries its own
`∀ O` binder, as `UniformityStatement` does.
-/

set_option linter.style.longLine false

namespace Uniformity.Density

open IsLocalRing

/-- **`UniformityStatement` at `n = 2`.** One rational function per degree-2 type, valid at every
complete DVR with finite residue field — wild residue characteristic included, both
characteristics. Unconditional: no drainage hypothesis, no axiom, Lean core only. -/
theorem uniformityStatement_two (σ : FactorizationType) (hσ : σ.degree = 2) :
    ∃ num den : Polynomial ℚ, den ≠ 0 ∧
      ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
        [IsAdicComplete (maximalIdeal O) O] [Finite (ResidueField O)],
        den.eval ((residueCard O : ℕ) : ℚ) ≠ 0 ∧
          genuineDensity O 2 σ
            = ((num.eval ((residueCard O : ℕ) : ℚ) / den.eval ((residueCard O : ℕ) : ℚ) : ℚ) : ℝ) := by
  rcases degree_two_type_cases hσ with rfl | rfl | rfl | hzero
  -- `σ = splitType`: `q / (2(q+1))`
  · refine ⟨Polynomial.X, 2 * (Polynomial.X + 1), ?_, ?_⟩
    · intro h
      have h0 := congrArg (Polynomial.eval (0 : ℚ)) h
      simp at h0
    · intro O _ _ _ _ _
      have hq : (2 : ℚ) ≤ ((residueCard O : ℕ) : ℚ) := by exact_mod_cast two_le_residueCard O
      have hden : (2 * (Polynomial.X + 1) : Polynomial ℚ).eval ((residueCard O : ℕ) : ℚ)
          = 2 * (((residueCard O : ℕ) : ℚ) + 1) := by simp
      refine ⟨by rw [hden]; nlinarith, ?_⟩
      rw [(genuineDensity_two_exact (O := O)).1, hden]
      simp only [Polynomial.eval_X]
      push_cast
      ring
  -- `σ = inertType`: the same rational function
  · refine ⟨Polynomial.X, 2 * (Polynomial.X + 1), ?_, ?_⟩
    · intro h
      have h0 := congrArg (Polynomial.eval (0 : ℚ)) h
      simp at h0
    · intro O _ _ _ _ _
      have hq : (2 : ℚ) ≤ ((residueCard O : ℕ) : ℚ) := by exact_mod_cast two_le_residueCard O
      have hden : (2 * (Polynomial.X + 1) : Polynomial ℚ).eval ((residueCard O : ℕ) : ℚ)
          = 2 * (((residueCard O : ℕ) : ℚ) + 1) := by simp
      refine ⟨by rw [hden]; nlinarith, ?_⟩
      rw [(genuineDensity_two_exact (O := O)).2.1, hden]
      simp only [Polynomial.eval_X]
      push_cast
      ring
  -- `σ = ramType`: `1 / (q+1)`
  · refine ⟨1, Polynomial.X + 1, ?_, ?_⟩
    · intro h
      have h0 := congrArg (Polynomial.eval (0 : ℚ)) h
      simp at h0
    · intro O _ _ _ _ _
      have hq : (2 : ℚ) ≤ ((residueCard O : ℕ) : ℚ) := by exact_mod_cast two_le_residueCard O
      have hden : ((Polynomial.X + 1 : Polynomial ℚ)).eval ((residueCard O : ℕ) : ℚ)
          = ((residueCard O : ℕ) : ℚ) + 1 := by simp
      refine ⟨by rw [hden]; nlinarith, ?_⟩
      rw [(genuineDensity_two_exact (O := O)).2.2.1, hden]
      simp only [Polynomial.eval_one]
      push_cast
      ring
  -- every other degree-2 type: density `0`, so `0 / 1`
  · refine ⟨0, 1, one_ne_zero, ?_⟩
    intro O _ _ _ _ _
    refine ⟨by simp, ?_⟩
    rw [hzero O]
    simp

section AxCheck

#print axioms Uniformity.Density.uniformityStatement_two

end AxCheck

end Uniformity.Density
