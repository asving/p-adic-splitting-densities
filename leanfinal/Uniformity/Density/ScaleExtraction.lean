/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.Density.TypeOfInvariance

/-!
# Uniformity.Density.ScaleExtraction — the forward `π`-power extraction and its level bookkeeping

Two nodes of `spec/CERTAIN_NODES_2026-08-14.md`:

* **CN-12** `exists_monic_scaleRoots` — the integrality side condition of the FORWARD extraction
  `X = π^m Y`, in the one polygon formulation that is representation-free.
* **CN-13** `dvd_sub_coeff_of_scaleRoots` — how a congruence level survives the extraction.

## Status

Sorry-free, axiom-free (Lean core only).
-/

set_option linter.style.longLine false
-- The two signatures below are frozen contracts (`spec/CERTAIN_NODES_2026-08-14.md`), so the
-- standing `O`-bundle is carried in full even where a weaker one would do.
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Uniformity.Density

open IsLocalRing Polynomial

/-! ## CN-13 — the level bookkeeping across the extraction -/

section Level

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {π : O}

/-- Cancellation kernel of CN-13: if `π^N` divides `a · π^k` and `k ≤ P`, then `π^(N-P)`
divides `a`. Truncated subtraction makes the case `N ≤ P` trivially true. -/
private theorem dvd_of_mul_pow_dvd {O : Type*} [CommRing O] [IsDomain O] {π : O} (hπ0 : π ≠ 0)
    {a : O} {N P k : ℕ} (hkP : k ≤ P) (hdvd : π ^ N ∣ a * π ^ k) : π ^ (N - P) ∣ a := by
  rcases le_or_gt N P with hle | hgt
  · rw [Nat.sub_eq_zero_of_le hle, pow_zero]
    exact one_dvd _
  · obtain ⟨c, hc⟩ := hdvd
    refine ⟨π ^ (P - k) * c, ?_⟩
    have hexp : (N - P) + ((P - k) + k) = N := by omega
    refine mul_right_cancel₀ (pow_ne_zero k hπ0) ?_
    calc a * π ^ k = π ^ N * c := hc
      _ = π ^ ((N - P) + ((P - k) + k)) * c := by rw [hexp]
      _ = π ^ (N - P) * (π ^ (P - k) * c) * π ^ k := by rw [pow_add, pow_add]; ring

/-- **CN-13 — the level drop across the `π`-power extraction.** If the two scaled polynomials
`G'(π^m ·)`-normalised and `G(π^m ·)`-normalised agree coefficientwise mod `π^N`, then `G'` and
`G` themselves agree coefficientwise mod `π^(N - m·deg G)`.

**Read the truncated subtraction carefully.** `N - m * G.natDegree` is `ℕ`-subtraction, so when
`m · deg G ≥ N` the conclusion is `π^0 ∣ …`, i.e. *no information at all*. That is the intended
and correct reading — the extraction has exhausted the level — but a consumer must not quote
this lemma as a nontrivial congruence in that regime. -/
theorem dvd_sub_coeff_of_scaleRoots (hπ : Irreducible π) {G G' : Polynomial O}
    (hG : G.Monic) (hG' : G'.Monic) (hdeg : G'.natDegree = G.natDegree) {m N : ℕ}
    (h : ∀ i, π ^ N ∣ ((G'.scaleRoots (π ^ m)).coeff i - (G.scaleRoots (π ^ m)).coeff i)) :
    ∀ i, π ^ (N - m * G.natDegree) ∣ (G'.coeff i - G.coeff i) := by
  intro i
  have hkey : π ^ N ∣ (G'.coeff i - G.coeff i) * π ^ (m * (G.natDegree - i)) := by
    have hi := h i
    rwa [coeff_scaleRoots, coeff_scaleRoots, hdeg, ← sub_mul, ← pow_mul] at hi
  exact dvd_of_mul_pow_dvd hπ.ne_zero (Nat.mul_le_mul_left m (Nat.sub_le _ _)) hkey

end Level

/-! ## CN-12 — the forward extraction, and its integrality side condition

The substitution `X = π^m Y` sends a monic `f` of degree `n` to `f(π^m Y)`, which is
`π^(m n) · G(Y)` for an *integral* monic `G` exactly when the Newton polygon of `f` — the lower
hull of the points `(i, v(f.coeff i))` — lies on or above the line through `(n, 0)` and
`(0, m n)`, the "slope `m`" line of the source docstring. Written without any polygon
representation, that condition is the coefficient divisibility `π^(m(n-i)) ∣ f.coeff i`
(equivalently `v(f.coeff i) ≥ m(n-i)`) for `i < n`, and the
conclusion is `f = G.scaleRoots (π^m)` — the backward (always integral) form in which the
landed `typeOf_scaleRoots` is stated. -/

section Extract

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {π : O}

/-- **CN-12 — polygon-above-slope-`m` ⟹ integral extraction.** If every coefficient of a monic
`f` of degree `n` satisfies `π^(m(n-i)) ∣ f.coeff i`, then `f` is the `π^m`-rescaling of a monic
`G` of the same degree; equivalently `f(π^m Y) = π^(m n) G(Y)` with `G` integral. The witness is
built coefficientwise from the divisibility quotients. -/
theorem exists_monic_scaleRoots (hπ : Irreducible π) {f : Polynomial O} (hf : f.Monic)
    (m : ℕ) (h : ∀ i < f.natDegree, π ^ (m * (f.natDegree - i)) ∣ f.coeff i) :
    ∃ G : Polynomial O, G.Monic ∧ G.natDegree = f.natDegree ∧ f = G.scaleRoots (π ^ m) := by
  classical
  set n := f.natDegree with hn
  -- The side condition also holds (vacuously) at and above the degree, where the exponent is `0`.
  have hdvd : ∀ i, ∃ d : O, f.coeff i = π ^ (m * (n - i)) * d := by
    intro i
    rcases lt_or_ge i n with hi | hi
    · exact h i hi
    · exact ⟨f.coeff i, by rw [Nat.sub_eq_zero_of_le hi, Nat.mul_zero, pow_zero, one_mul]⟩
  choose c hc using hdvd
  -- `c` vanishes above the degree, so it *is* the coefficient function of the witness.
  have hczero : ∀ j, n < j → c j = 0 := by
    intro j hj
    have hcj := hc j
    rw [Nat.sub_eq_zero_of_le hj.le, Nat.mul_zero, pow_zero, one_mul] at hcj
    rw [← hcj, coeff_eq_zero_of_natDegree_lt (by omega)]
  set G : Polynomial O := ∑ i ∈ Finset.range (n + 1), Polynomial.monomial i (c i) with hGdef
  have hcoeff : ∀ j, G.coeff j = c j := by
    intro j
    rw [hGdef, Polynomial.finsetSum_coeff]
    simp only [Polynomial.coeff_monomial, Finset.sum_ite_eq', Finset.mem_range, Nat.lt_succ_iff]
    split_ifs with hj
    · rfl
    · exact (hczero j (by omega)).symm
  have hcn : c n = 1 := by
    have hcn' := hc n
    rw [Nat.sub_self, Nat.mul_zero, pow_zero, one_mul, hn] at hcn'
    rw [← hcn', hf.coeff_natDegree]
  have hle : G.natDegree ≤ n :=
    Polynomial.natDegree_le_iff_coeff_eq_zero.2 (fun N hN => by rw [hcoeff]; exact hczero N hN)
  have hmonic : G.Monic :=
    Polynomial.monic_of_natDegree_le_of_coeff_eq_one n hle (by rw [hcoeff]; exact hcn)
  have hdeg : G.natDegree = n :=
    le_antisymm hle (Polynomial.le_natDegree_of_ne_zero (by rw [hcoeff, hcn]; exact one_ne_zero))
  refine ⟨G, hmonic, hdeg, ?_⟩
  ext j
  rw [coeff_scaleRoots, hdeg, hcoeff, ← pow_mul, mul_comm]
  exact hc j

/-- **The depth-reduction step in the form the deep-tail recursion consumes.** CN-12 composed
with the landed `typeOf_scaleRoots`: a polygon above slope `m` lets one replace `f` by the
extracted `G`, of the same degree, *without changing the splitting type*. -/
theorem exists_monic_scaleRoots_typeOf (hπ : Irreducible π) {f : Polynomial O} (hf : f.Monic)
    (m : ℕ) (h : ∀ i < f.natDegree, π ^ (m * (f.natDegree - i)) ∣ f.coeff i) :
    ∃ G : Polynomial O, G.Monic ∧ G.natDegree = f.natDegree ∧ f = G.scaleRoots (π ^ m) ∧
      typeOf f = typeOf G := by
  obtain ⟨G, hG, hGdeg, hGeq⟩ := exists_monic_scaleRoots hπ hf m h
  exact ⟨G, hG, hGdeg, hGeq, by rw [hGeq]; exact typeOf_scaleRoots hπ hG m⟩

end Extract

/-! ## Axiom census -/

section AxCheck

#print axioms Uniformity.Density.dvd_sub_coeff_of_scaleRoots
#print axioms Uniformity.Density.exists_monic_scaleRoots
#print axioms Uniformity.Density.exists_monic_scaleRoots_typeOf

end AxCheck

end Uniformity.Density

