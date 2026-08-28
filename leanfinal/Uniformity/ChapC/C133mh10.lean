/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib

/-!
# Uniformity.ChapC.C133mh10 — `[MH10 2026-08-28]`: Theorem H0, the residual Bézout lemma

**Node MH.10** (`docs/in-progress/HENSEL_ENGINE_2026-08-26.md` §9, plan row **F1.H0**;
statement §2, "Theorem H0 (residual Bézout — F1.H0 verbatim)").

## Statement

`K` a field, `R : Polynomial K` with `R ≠ 0`, `R.coeff 0 ≠ 0`; `r` monic irreducible with
`r.coeff 0 ≠ 0`, `0 < r.natDegree`; `hdvd : r ∣ R`. Then there are unique `m : ℕ` and
`s : Polynomial K` with `R = r ^ m * s`, `¬ r ∣ s`, `0 < m`, `s.coeff 0 ≠ 0`,
`IsCoprime (r ^ m) s`, and (the monic-normalized form used by Theorem A)
`R.Monic → (r ^ m).Monic ∧ s.Monic`.

This is pure UFD/field arithmetic in `K[Z]` — no repo frame content, mathlib only.
`m` is the multiplicity of `r` in `R` (mathlib's `multiplicity`); `s` is the cofactor.
The consumer-facing shape splits existence (`dvResidualBezout`, all six clauses at once)
from uniqueness (`dvResidualBezout_unique`, minimal hypotheses: any `(m', s')` with
`R = r ^ m' * s'` and `¬ r ∣ s'` agrees with any other such pair).

**Status:** sorry-free, zero new axiom, footprint Lean-core only — see the AxCheck footer.
-/

set_option linter.style.longLine false

namespace Uniformity.Density.Tower.C133mh10

open Polynomial

variable {K : Type*} [Field K]

/-- ★ **Theorem H0 (existence half).** The residual Bézout factorization: `R` splits as
`r`'s exact power times a cofactor not divisible by `r`, with the coefficient-0 and
coprimality clauses, and the monic-normalized form. -/
theorem dvResidualBezout {R r : Polynomial K} (hR : R ≠ 0) (hR0 : R.coeff 0 ≠ 0)
    (hr : r.Monic) (hrirr : Irreducible r) (hr0 : r.coeff 0 ≠ 0) (hrdeg : 0 < r.natDegree)
    (hdvd : r ∣ R) :
    ∃ m : ℕ, ∃ s : Polynomial K,
      R = r ^ m * s ∧ ¬ r ∣ s ∧ 0 < m ∧ s.coeff 0 ≠ 0 ∧ IsCoprime (r ^ m) s ∧
      (R.Monic → (r ^ m).Monic ∧ s.Monic) := by
  have hdegpos : (0 : WithBot ℕ) < r.degree := natDegree_pos_iff_degree_pos.mp hrdeg
  have hfin : FiniteMultiplicity r R := finiteMultiplicity_of_degree_pos_of_monic hdegpos hr hR
  obtain ⟨s, hs, hns⟩ := hfin.exists_eq_pow_mul_and_not_dvd
  set m := multiplicity r R with hm
  refine ⟨m, s, hs, hns, Nat.pos_of_ne_zero (multiplicity_ne_zero.2 hdvd), ?_, ?_, ?_⟩
  · have hcoeff : R.coeff 0 = (r ^ m).coeff 0 * s.coeff 0 := by rw [hs, mul_coeff_zero]
    intro hz
    exact hR0 (by rw [hcoeff, hz, mul_zero])
  · exact (hrirr.coprime_iff_not_dvd.mpr hns).pow_left
  · intro hRmonic
    have hrm : (r ^ m).Monic := hr.pow m
    exact ⟨hrm, hrm.of_mul_monic_left (hs ▸ hRmonic)⟩

/-- ★ **Theorem H0 (uniqueness half).** Any two residual-Bézout pairs for the same `R`
agree — stated with the minimal hypotheses a consumer would supply: just the splitting
equation and the non-divisibility of the cofactor. -/
theorem dvResidualBezout_unique {R r s s' : Polynomial K} {m m' : ℕ}
    (hr : r.Monic) (hrdeg : 0 < r.natDegree)
    (heq : R = r ^ m * s) (hns : ¬ r ∣ s)
    (heq' : R = r ^ m' * s') (hns' : ¬ r ∣ s') :
    m = m' ∧ s = s' := by
  have hrne : r ≠ 0 := hr.ne_zero
  have main : ∀ {a b : ℕ} {t u : Polynomial K}, a ≤ b →
      r ^ a * t = r ^ b * u → ¬ r ∣ t → a = b := by
    intro a b t u hab habeq hnt
    by_contra hne
    have hlt : a < b := lt_of_le_of_ne hab hne
    have hcancel : t = r ^ (b - a) * u := by
      refine mul_left_cancel₀ (pow_ne_zero a hrne) ?_
      rw [← mul_assoc, ← pow_add, Nat.add_sub_cancel' hab]
      exact habeq
    exact hnt (dvd_trans (dvd_pow_self r (Nat.sub_ne_zero_of_lt hlt)) ⟨u, hcancel⟩)
  have hmm : m = m' := by
    rcases le_total m m' with h | h
    · exact main h (heq.symm.trans heq') hns
    · exact (main h (heq'.symm.trans heq) hns').symm
  subst hmm
  exact ⟨rfl, mul_left_cancel₀ (pow_ne_zero m hrne) (heq.symm.trans heq')⟩

end Uniformity.Density.Tower.C133mh10

/-! ## AxCheck footer -/

section AxCheck

#print axioms Uniformity.Density.Tower.C133mh10.dvResidualBezout
#print axioms Uniformity.Density.Tower.C133mh10.dvResidualBezout_unique

end AxCheck
