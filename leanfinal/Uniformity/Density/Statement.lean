/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.Density.GenuineDensity

/-!
# Uniformity.Density.Statement — THE CAPSTONE TARGETS (statements only, pending sign-off)

The two `Prop`s below are the **targets** of the whole repo, phrased over the Part-1
`genuineDensity`. They are *definitions*, not sorried theorems: this repo carries zero
`sorry`s from day one, so a target is a named `Prop` until it is proved.

**`UniformityStatement`** — for each degree `n > 0` and each splitting type `σ` of degree `n`
there is ONE rational function `num/den` such that for EVERY complete DVR `O` with finite
residue field (so: every `ℤ_[p]`, every finite extension of `ℤ_[p]`, every `𝔽_q⟦t⟧`), with
`q = #(residue field)`,

    genuineDensity O n σ = num(q) / den(q).

The `∃ (num, den)` stands OUTSIDE the `∀ O`: that ∃-before-∀ order *is* the uniformity claim
(one law, all primes, wild ones included). The density is the Part-1 limit, so the statement
has content by construction — there is no abstract "counting model" it could be satisfied by
vacuously.

**`UniformityStatementPadic`** — the same law over `ℤ_[p]` only, with `q = p`. It is a
consequence of the general one (`UniformityStatement.toPadic`, proved below).

⚠ **PENDING ASVIN'S STATEMENT SIGN-OFF.** Design points to review are listed in
`notes/GENUINE_DENSITY_2026-08-13.md` §Statement: (i) universe restriction to `Type`;
(ii) rational function evaluated at the *natural number* `q` cast to `ℚ`, with the equality read
in `ℝ`; (iii) `den.eval q ≠ 0` demanded per-`O` rather than globally; (iv) the hypothesis
`σ.degree = n` (which does real work only once `typeOf_degree` is available — see the note's
OPEN list).
-/

set_option linter.style.longLine false

namespace Uniformity.Density

open IsLocalRing Polynomial

/-- **THE CAPSTONE TARGET.** One rational function in `q` per `(n, σ)`, valid at every complete
DVR with finite residue field. See the module docstring. -/
def UniformityStatement : Prop :=
  ∀ (n : ℕ), 0 < n → ∀ σ : FactorizationType, σ.degree = n →
    ∃ num den : Polynomial ℚ, den ≠ 0 ∧
      ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
        [IsAdicComplete (maximalIdeal O) O] [Finite (ResidueField O)],
        den.eval ((residueCard O : ℕ) : ℚ) ≠ 0 ∧
          genuineDensity O n σ
            = ((num.eval ((residueCard O : ℕ) : ℚ) / den.eval ((residueCard O : ℕ) : ℚ) : ℚ) : ℝ)

/-- **THE CAPSTONE TARGET, `ℤ_[p]` form.** The same law at every prime, with `q = p`. -/
def UniformityStatementPadic : Prop :=
  ∀ (n : ℕ), 0 < n → ∀ σ : FactorizationType, σ.degree = n →
    ∃ num den : Polynomial ℚ, den ≠ 0 ∧
      ∀ (p : ℕ) [Fact (Nat.Prime p)],
        den.eval (p : ℚ) ≠ 0 ∧
          genuineDensity ℤ_[p] n σ = ((num.eval (p : ℚ) / den.eval (p : ℚ) : ℚ) : ℝ)

/-- The general target implies the `ℤ_[p]` target: `ℤ_[p]` is an instance of the bundle with
`q = p` (`residueCard_padicInt`). -/
theorem UniformityStatement.toPadic (h : UniformityStatement) : UniformityStatementPadic := by
  intro n hn σ hσ
  obtain ⟨num, den, hden, hlaw⟩ := h n hn σ hσ
  refine ⟨num, den, hden, ?_⟩
  intro p _
  have := hlaw ℤ_[p]
  rwa [residueCard_padicInt p] at this

end Uniformity.Density
