/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.Moves.Defs

/-!
# Moves/L1_gaussVal — the Gauss valuation is multiplicative (§A.1, base of B1.1)

Introduces `gaussVal f = min_i v_p(f.coeff i)` (min p-adic valuation over the support) and proves
it is multiplicative on nonzero polynomials over `ℤ_[p]`.

**Proof idea.** `gaussVal f` equals (the ℤ-coercion of) `emultiplicity (C p) f`, the number of
times the prime `C p` divides `f` in `ℤ_[p][X]`: `(C p)^n ∣ f ↔ n ≤ min valuation`, using that
`p` is prime in the DVR `ℤ_[p]` (`PadicInt.prime_p`, `Polynomial.prime_C_iff`) and the
divisibility-vs-valuation dictionary `PadicInt.mem_span_pow_iff_le_valuation`. Multiplicativity is
then `emultiplicity_mul` for the prime `C p`.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

open Polynomial LeanUrat.Moves

namespace LeanUrat.Moves

/-- The **Gauss valuation** of `f ∈ ℤ_[p][X]`: the minimum of the `p`-adic valuations of the
coefficients over the support (`0` for `f = 0`). -/
noncomputable def gaussVal {p : ℕ} [Fact p.Prime] (f : Polynomial ℤ_[p]) : ℤ :=
  if h : f.support.Nonempty then f.support.inf' h (fun i => (f.coeff i).valuation) else 0

/-- The ℕ-valued content: same as `gaussVal` but before the ℤ-coercion. -/
private noncomputable def natGV {p : ℕ} [Fact p.Prime] (f : Polynomial ℤ_[p]) : ℕ :=
  if h : f.support.Nonempty then f.support.inf' h (fun i => (f.coeff i).valuation) else 0

private lemma gaussVal_eq_cast {p : ℕ} [Fact p.Prime] (f : Polynomial ℤ_[p]) :
    gaussVal f = (natGV f : ℤ) := by
  unfold gaussVal natGV
  by_cases h : f.support.Nonempty
  · rw [dif_pos h, dif_pos h, Nat.cast_finsetInf']
  · rw [dif_neg h, dif_neg h, Nat.cast_zero]

/-- Divisibility-vs-valuation in the DVR `ℤ_[p]`: `p^n ∣ x ↔ n ≤ v_p(x)` for `x ≠ 0`. -/
private lemma padic_pow_dvd_iff {p : ℕ} [Fact p.Prime] {x : ℤ_[p]} (hx : x ≠ 0) (n : ℕ) :
    (p : ℤ_[p]) ^ n ∣ x ↔ n ≤ x.valuation :=
  Ideal.mem_span_singleton.symm.trans (PadicInt.mem_span_pow_iff_le_valuation x hx n)

/-- The core characterization: `(C p)^n ∣ f ↔ n ≤ natGV f` (for `f ≠ 0`). -/
private lemma cpow_dvd_iff {p : ℕ} [Fact p.Prime] {f : Polynomial ℤ_[p]} (hf : f ≠ 0) (n : ℕ) :
    (C (p : ℤ_[p])) ^ n ∣ f ↔ n ≤ natGV f := by
  have hne : f.support.Nonempty := Polynomial.support_nonempty.mpr hf
  rw [← map_pow, Polynomial.C_dvd_iff_dvd_coeff]
  simp only [natGV, dif_pos hne]
  constructor
  · intro h
    apply Finset.le_inf'
    intro i hi
    exact (padic_pow_dvd_iff (Polynomial.mem_support_iff.mp hi) n).mp (h i)
  · intro h i
    by_cases hi : i ∈ f.support
    · exact (padic_pow_dvd_iff (Polynomial.mem_support_iff.mp hi) n).mpr
        (le_trans h (Finset.inf'_le _ hi))
    · rw [Polynomial.mem_support_iff, not_not] at hi
      rw [hi]; exact dvd_zero _

private lemma emult_eq {p : ℕ} [Fact p.Prime] {f : Polynomial ℤ_[p]} (hf : f ≠ 0) :
    emultiplicity (C (p : ℤ_[p])) f = (natGV f : ℕ∞) := by
  rw [emultiplicity_eq_coe]
  exact ⟨(cpow_dvd_iff hf (natGV f)).mpr le_rfl,
    fun hd => absurd ((cpow_dvd_iff hf (natGV f + 1)).mp hd) (by omega)⟩

theorem L1_gaussVal_mul {p : ℕ} [Fact p.Prime] (f g : Polynomial ℤ_[p]) (hf : f ≠ 0) (hg : g ≠ 0) : gaussVal (f * g) = gaussVal f + gaussVal g := by
  have hfg : f * g ≠ 0 := mul_ne_zero hf hg
  have hprime : Prime (C (p : ℤ_[p])) := Polynomial.prime_C_iff.mpr PadicInt.prime_p
  have hmul := emultiplicity_mul (a := f) (b := g) hprime
  rw [emult_eq hfg, emult_eq hf, emult_eq hg] at hmul
  have hnat : natGV (f * g) = natGV f + natGV g := by exact_mod_cast hmul
  rw [gaussVal_eq_cast (f * g), gaussVal_eq_cast f, gaussVal_eq_cast g, hnat]
  push_cast
  ring

end LeanUrat.Moves
