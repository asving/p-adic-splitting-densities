/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib

/-!
# LeanUrat.OM.Necklace — necklace counts for an arbitrary alphabet size

For `d ≥ 1` and any natural `q`, the *necklace sum*
```
    necklaceSum d q = ∑_{e ∣ d} μ(e) · q^{d/e}   (an integer)
```
counts the aperiodic words of length `d` over a `q`-letter alphabet.  This file proves,
purely algebraically (no combinatorics on words needed):

* `necklaceSum_nonneg` : `0 ≤ necklaceSum d q`;
* `dvd_necklaceSum`    : `(d : ℤ) ∣ necklaceSum d q` (the **Gauss congruence**), so that
* `necklaceQ d q = necklaceSum d q / d` (the necklace count itself) is a nonnegative
  integer-valued rational: `necklaceQ_nonneg`, `necklaceQ_eq_natCast`.

## Proofs

*Nonnegativity.*  Writing the sum over the divisor-complement (`necklaceSum_flip`),
`necklaceSum d q = q^d + ∑_{e ∣ d, e < d} μ(d/e) q^e`, and since the exponents `e` in the
error sum are *distinct* naturals `< d`, the error is bounded by `∑_{e<d} q^e < q^d` for
`q ≥ 2` (`Nat.geomSum_lt`); the cases `q = 0, 1` are immediate (for `q = 1` the sum is
`∑_{e ∣ d} μ(e) ∈ {0, 1}`).

*Gauss congruence.*  It suffices to prove `p^(k+1) ∣ necklaceSum d q` for every maximal
prime power `p^(k+1) ∥ d` (`Finset.prod_dvd_of_coprime`).  Writing `d = p^(k+1) * m` with
`p ∤ m` and splitting divisors of `d` according to divisibility by `p` (Möbius kills every
divisor with `p² ∣ e`), one gets
`necklaceSum d q = ∑_{e ∣ m} μ(e) (q^{p^(k+1) u} - q^{p^k u})` with `u = m / e`,
and each summand is divisible by `p^(k+1)` because `p ∣ q^p - q` (Fermat, `ZMod.pow_card`),
hence `p^(k+1) ∣ (q^p)^{p^k} - q^{p^k}` (`dvd_sub_pow_of_dvd_sub`), and
`x - y ∣ x^u - y^u` (`sub_dvd_pow_sub_pow`).
-/

namespace LeanUrat.OM.Necklace

open Finset ArithmeticFunction

open scoped ArithmeticFunction.zeta

/-- The necklace sum `∑_{e ∣ d} μ(e) q^{d/e}`: `d` times the number of necklaces (equivalently,
the number of aperiodic words) of length `d` over a `q`-letter alphabet. -/
def necklaceSum (d q : ℕ) : ℤ :=
  ∑ e ∈ d.divisors, moebius e * (q : ℤ) ^ (d / e)

/-- The necklace sum, summed over the complementary divisor:
`necklaceSum d q = ∑_{e ∣ d} μ(d/e) q^e`. -/
lemma necklaceSum_flip (d q : ℕ) (hd : d ≠ 0) :
    necklaceSum d q = ∑ e ∈ d.divisors, moebius (d / e) * (q : ℤ) ^ e := by
  simp only [necklaceSum]
  rw [← Nat.sum_div_divisors d (fun e => moebius e * (q : ℤ) ^ (d / e))]
  exact Finset.sum_congr rfl fun e he => by
    rw [Nat.div_div_self (Nat.mem_divisors.mp he).1 hd]

/-- The classical `∑_{e ∣ d} μ(e) = [d = 1]`, extracted from `μ * ζ = 1`. -/
lemma sum_moebius_divisors (d : ℕ) :
    ∑ e ∈ d.divisors, moebius e = if d = 1 then 1 else 0 := by
  have h : (moebius * ζ : ArithmeticFunction ℤ) d = (1 : ArithmeticFunction ℤ) d := by
    rw [moebius_mul_coe_zeta]
  rwa [coe_mul_zeta_apply, one_apply] at h

/-- **Nonnegativity of the necklace sum**: `0 ≤ ∑_{e ∣ d} μ(e) q^{d/e}` for `d ≥ 1`. -/
theorem necklaceSum_nonneg (d q : ℕ) (hd : 1 ≤ d) : 0 ≤ necklaceSum d q := by
  have hd0 : d ≠ 0 := by omega
  rw [necklaceSum_flip d q hd0]
  rcases Nat.lt_or_ge q 2 with hq | hq
  · interval_cases q
    · -- `q = 0`: every term vanishes since every divisor exponent is positive.
      refine Finset.sum_nonneg fun e he => ?_
      simp [zero_pow (Nat.pos_of_mem_divisors he).ne']
    · -- `q = 1`: the sum is `∑_{e ∣ d} μ(e) ∈ {0, 1}`.
      have h1 : ∀ e ∈ d.divisors, moebius (d / e) * ((1 : ℕ) : ℤ) ^ e = moebius (d / e) :=
        fun e _ => by rw [Nat.cast_one, one_pow, mul_one]
      rw [Finset.sum_congr rfl h1, Nat.sum_div_divisors d (fun e => moebius e),
        sum_moebius_divisors]
      split <;> norm_num
  · -- `q ≥ 2`: the `e = d` term is `q^d`, and the rest is bounded by `∑_{e < d} q^e < q^d`.
    have hdmem : d ∈ d.divisors := Nat.mem_divisors_self d hd0
    rw [← Finset.add_sum_erase _ _ hdmem, Nat.div_self (by omega : 0 < d),
      moebius_apply_one, one_mul]
    have habs : |∑ e ∈ d.divisors.erase d, moebius (d / e) * (q : ℤ) ^ e|
        ≤ ∑ e ∈ d.divisors.erase d, (q : ℤ) ^ e := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun e he => ?_)
      rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℤ) ≤ (q : ℤ) ^ e)]
      calc |moebius (d / e)| * (q : ℤ) ^ e ≤ 1 * (q : ℤ) ^ e := by
            have := abs_moebius_le_one (n := d / e)
            have hqe : (0 : ℤ) ≤ (q : ℤ) ^ e := by positivity
            nlinarith
        _ = (q : ℤ) ^ e := one_mul _
    have hgeom : ∑ e ∈ d.divisors.erase d, (q : ℤ) ^ e ≤ (q : ℤ) ^ d := by
      have hlt : ∀ e ∈ d.divisors.erase d, e < d := fun e he => by
        obtain ⟨hne, hmem⟩ := Finset.mem_erase.mp he
        exact lt_of_le_of_ne (Nat.le_of_dvd (by omega) (Nat.mem_divisors.mp hmem).1) hne
      have h := (Nat.geomSum_lt hq hlt).le
      calc ∑ e ∈ d.divisors.erase d, (q : ℤ) ^ e
          = ((∑ e ∈ d.divisors.erase d, q ^ e : ℕ) : ℤ) := by push_cast; rfl
        _ ≤ ((q ^ d : ℕ) : ℤ) := Nat.cast_le.mpr h
        _ = (q : ℤ) ^ d := by push_cast; rfl
    have hneg := neg_abs_le (∑ e ∈ d.divisors.erase d, moebius (d / e) * (q : ℤ) ^ e)
    linarith

/-- **Fermat-style prime-power congruence**: `p^(k+1) ∣ q^(p^(k+1) t) - q^(p^k t)`. -/
lemma prime_pow_dvd_pow_sub_pow (p : ℕ) (hp : p.Prime) (k t q : ℕ) :
    ((p : ℤ) ^ (k + 1)) ∣ (q : ℤ) ^ (p ^ (k + 1) * t) - (q : ℤ) ^ (p ^ k * t) := by
  haveI : Fact p.Prime := ⟨hp⟩
  -- Fermat: `p ∣ q^p - q`.
  have h1 : (p : ℤ) ∣ (q : ℤ) ^ p - (q : ℤ) := by
    have h0 : (((q : ℤ) ^ p - (q : ℤ) : ℤ) : ZMod p) = 0 := by
      push_cast
      rw [ZMod.pow_card]
      ring
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp h0
  -- Lift to `p^(k+1) ∣ q^(p^(k+1)) - q^(p^k)`.
  have h2 : ((p : ℤ) ^ (k + 1)) ∣ ((q : ℤ) ^ p) ^ p ^ k - (q : ℤ) ^ p ^ k := by
    have h := dvd_sub_pow_of_dvd_sub h1 k
    exact_mod_cast h
  have hexp : ((q : ℤ) ^ p) ^ p ^ k = (q : ℤ) ^ p ^ (k + 1) := by
    rw [← pow_mul]
    congr 1
    ring
  rw [hexp] at h2
  -- Push the exponents up by the coprime factor `t` via `x - y ∣ x^t - y^t`.
  have h3 : (q : ℤ) ^ p ^ (k + 1) - (q : ℤ) ^ p ^ k
      ∣ (q : ℤ) ^ (p ^ (k + 1) * t) - (q : ℤ) ^ (p ^ k * t) := by
    rw [pow_mul, pow_mul]
    exact sub_dvd_pow_sub_pow _ _ t
  exact h2.trans h3

/-- Splitting a divisor sum of `d = p^(k+1) m` (`p ∤ m`) along divisibility by `p`, for a
summand `g` vanishing on non-squarefree arguments:
`∑_{e ∣ d} g e = ∑_{e ∣ m} (g (p e) + g e)`. -/
lemma sum_divisors_eq_sum_coprime_part (d p m k : ℕ) (hp : p.Prime)
    (hd : d = p ^ (k + 1) * m) (hm : ¬p ∣ m) (hm0 : m ≠ 0)
    (g : ℕ → ℤ) (hg : ∀ e, ¬Squarefree e → g e = 0) :
    ∑ e ∈ d.divisors, g e = ∑ e ∈ m.divisors, (g (p * e) + g e) := by
  have hd0 : d ≠ 0 := by
    rw [hd]
    exact Nat.mul_ne_zero (pow_ne_zero _ hp.pos.ne') hm0
  -- The divisors of `d` prime to `p` are exactly the divisors of `m`.
  have hA : d.divisors.filter (fun e => ¬p ∣ e) = m.divisors := by
    ext e
    simp only [Finset.mem_filter, Nat.mem_divisors]
    constructor
    · rintro ⟨⟨hed, -⟩, hpe⟩
      refine ⟨?_, hm0⟩
      have hcop : Nat.Coprime e (p ^ (k + 1)) :=
        Nat.Coprime.pow_right _ ((hp.coprime_iff_not_dvd.mpr hpe).symm)
      exact hcop.dvd_mul_left.mp (hd ▸ hed)
    · rintro ⟨hem, -⟩
      refine ⟨⟨?_, hd0⟩, fun hpe => hm (hpe.trans hem)⟩
      rw [hd]
      exact hem.mul_left _
  -- The divisors of `d` divisible by `p` contribute (via `μ = 0` on non-squarefree numbers)
  -- exactly the sum of `g (p * e)` over divisors `e` of `m`.
  have himg : m.divisors.image (fun e => p * e) ⊆ d.divisors.filter (fun e => p ∣ e) := by
    intro x hx
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨hem, -⟩ := Nat.mem_divisors.mp he
    refine Finset.mem_filter.mpr ⟨Nat.mem_divisors.mpr ⟨?_, hd0⟩, dvd_mul_right p e⟩
    rw [hd]
    exact mul_dvd_mul (dvd_pow_self p k.succ_ne_zero) hem
  have hvanish : ∀ x ∈ d.divisors.filter (fun e => p ∣ e),
      x ∉ m.divisors.image (fun e => p * e) → g x = 0 := by
    intro x hx hnx
    obtain ⟨hxd, hpx⟩ := Finset.mem_filter.mp hx
    obtain ⟨u, rfl⟩ := hpx
    obtain ⟨hxdvd, -⟩ := Nat.mem_divisors.mp hxd
    by_cases hsq : Squarefree (p * u)
    · exfalso
      have hpu : ¬p ∣ u := fun hpu =>
        hp.ne_one (Nat.isUnit_iff.mp (hsq p (mul_dvd_mul_left p hpu)))
      have hum : u ∣ m := by
        have hcop : Nat.Coprime u (p ^ (k + 1)) :=
          Nat.Coprime.pow_right _ ((hp.coprime_iff_not_dvd.mpr hpu).symm)
        exact hcop.dvd_mul_left.mp (hd ▸ (dvd_mul_left u p).trans hxdvd)
      exact hnx (Finset.mem_image.mpr ⟨u, Nat.mem_divisors.mpr ⟨hum, hm0⟩, rfl⟩)
    · exact hg _ hsq
  have hB : ∑ e ∈ d.divisors.filter (fun e => p ∣ e), g e
      = ∑ e ∈ m.divisors, g (p * e) := by
    rw [← Finset.sum_subset himg hvanish]
    exact Finset.sum_image fun x _ y _ h => Nat.eq_of_mul_eq_mul_left hp.pos h
  rw [← Finset.sum_filter_add_sum_filter_not d.divisors (fun e => p ∣ e) g,
    Finset.sum_add_distrib, hA, hB]

/-- **Local Gauss congruence**: if `d = p^(k+1) m` with `p` prime and `p ∤ m`, then
`p^(k+1) ∣ necklaceSum d q`. -/
lemma prime_pow_dvd_necklaceSum {d p m k : ℕ} (q : ℕ) (hp : p.Prime)
    (hd : d = p ^ (k + 1) * m) (hm : ¬p ∣ m) (hm0 : m ≠ 0) :
    ((p : ℤ) ^ (k + 1)) ∣ necklaceSum d q := by
  have hsplit := sum_divisors_eq_sum_coprime_part d p m k hp hd hm hm0
    (fun e => moebius e * (q : ℤ) ^ (d / e))
    (fun e he => by rw [moebius_eq_zero_of_not_squarefree he, zero_mul])
  rw [necklaceSum, hsplit]
  refine Finset.dvd_sum fun e he => ?_
  obtain ⟨hem, -⟩ := Nat.mem_divisors.mp he
  obtain ⟨u, hu⟩ := hem
  have he0 : 0 < e := Nat.pos_of_mem_divisors he
  have hpe : ¬p ∣ e := fun h => hm (h.trans ⟨u, hu⟩)
  have hmu : moebius (p * e) = -moebius e := by
    rw [isMultiplicative_moebius.map_mul_of_coprime (hp.coprime_iff_not_dvd.mpr hpe),
      moebius_apply_prime hp, neg_one_mul]
  have hde : d / e = p ^ (k + 1) * u :=
    Nat.div_eq_of_eq_mul_left he0 (by rw [hd, hu]; ring)
  have hdpe : d / (p * e) = p ^ k * u :=
    Nat.div_eq_of_eq_mul_left (Nat.mul_pos hp.pos he0) (by rw [hd, hu]; ring)
  have hterm : moebius (p * e) * (q : ℤ) ^ (d / (p * e)) + moebius e * (q : ℤ) ^ (d / e)
      = moebius e * ((q : ℤ) ^ (p ^ (k + 1) * u) - (q : ℤ) ^ (p ^ k * u)) := by
    rw [hmu, hde, hdpe]
    ring
  rw [hterm]
  exact (prime_pow_dvd_pow_sub_pow p hp k u q).mul_left _

/-- **Gauss congruence / integrality of the necklace count**:
`d ∣ ∑_{e ∣ d} μ(e) q^{d/e}` for every `d ≥ 1` and every alphabet size `q`. -/
theorem dvd_necklaceSum (d q : ℕ) (hd : 1 ≤ d) : (d : ℤ) ∣ necklaceSum d q := by
  have hd0 : d ≠ 0 := by omega
  -- `d` is the product of its maximal prime-power divisors, which are pairwise coprime.
  have hprod : ∏ p ∈ d.primeFactors, (p : ℤ) ^ d.factorization p = (d : ℤ) := by
    have h1 : ∏ p ∈ d.primeFactors, p ^ d.factorization p = d := by
      rw [← Nat.support_factorization]
      exact Nat.prod_factorization_pow_eq_self hd0
    calc ∏ p ∈ d.primeFactors, (p : ℤ) ^ d.factorization p
        = ((∏ p ∈ d.primeFactors, p ^ d.factorization p : ℕ) : ℤ) := by push_cast; rfl
      _ = (d : ℤ) := by rw [h1]
  rw [← hprod]
  refine Finset.prod_dvd_of_coprime ?_ ?_
  · -- pairwise coprimality of distinct maximal prime powers
    intro a ha b hb hab
    simp only [Function.onFun]
    have hpa := Nat.prime_of_mem_primeFactors ha
    have hpb := Nat.prime_of_mem_primeFactors hb
    exact (Nat.isCoprime_iff_coprime.mpr ((Nat.coprime_primes hpa hpb).mpr hab)).pow
  · -- each maximal prime power divides the necklace sum
    intro p hpmem
    have hp := Nat.prime_of_mem_primeFactors hpmem
    have hkpos : 0 < d.factorization p :=
      hp.factorization_pos_of_dvd hd0 (Nat.dvd_of_mem_primeFactors hpmem)
    obtain ⟨k, hk⟩ : ∃ k, d.factorization p = k + 1 := ⟨d.factorization p - 1, by omega⟩
    rw [hk]
    refine prime_pow_dvd_necklaceSum (m := d / p ^ (k + 1)) q hp ?_ ?_ ?_
    · rw [← hk]
      exact (Nat.ordProj_mul_ordCompl_eq_self d p).symm
    · rw [← hk]
      exact Nat.not_dvd_ordCompl hp hd0
    · rw [← hk]
      exact (Nat.ordCompl_pos p hd0).ne'

/-- The ℚ-valued necklace count `(∑_{e ∣ d} μ(e) q^{d/e}) / d`: the number of necklaces
(= aperiodic words up to rotation) of length `d` over a `q`-letter alphabet. -/
def necklaceQ (d q : ℕ) : ℚ := (necklaceSum d q : ℚ) / d

/-- The necklace count is nonnegative. -/
theorem necklaceQ_nonneg (d q : ℕ) (hd : 1 ≤ d) : 0 ≤ necklaceQ d q := by
  have h1 : (0 : ℚ) ≤ ((necklaceSum d q : ℤ) : ℚ) := by
    exact_mod_cast necklaceSum_nonneg d q hd
  have h2 : (0 : ℚ) ≤ (d : ℚ) := by positivity
  exact div_nonneg h1 h2

/-- The necklace count is a natural number. -/
theorem necklaceQ_eq_natCast (d q : ℕ) (hd : 1 ≤ d) : ∃ m : ℕ, necklaceQ d q = m := by
  obtain ⟨c, hc⟩ := dvd_necklaceSum d q hd
  have hc0 : 0 ≤ c := by
    have h0 : (0 : ℤ) ≤ (d : ℤ) * c := by
      rw [← hc]
      exact necklaceSum_nonneg d q hd
    have hdpos : (0 : ℤ) < (d : ℤ) := by omega
    exact le_of_mul_le_mul_left (by simpa using h0) hdpos
  have hd0' : (d : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  refine ⟨c.toNat, ?_⟩
  have hcm : ((c.toNat : ℕ) : ℚ) = ((c : ℤ) : ℚ) := by
    exact_mod_cast congrArg (Int.cast : ℤ → ℚ) (Int.toNat_of_nonneg hc0)
  rw [necklaceQ, hc, Int.cast_mul, Int.cast_natCast, mul_div_cancel_left₀ _ hd0', ← hcm]

end LeanUrat.OM.Necklace
