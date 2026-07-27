/-
Unit E6.eligible_card_le  (MovesD campaign, E-phase)  [AUX]
informal: R_anch holds at most m̄ = ⌊ℓ/(g·μ)⌋ monic irreducible degree-g ord-μ factors —
L11's "each contributes g_r·μ_r to its degree".
deps: E4.
sketch: distinct monic irreducibles are coprime; the product of q^μ over any k eligible
factors divides Ranch (UFD), so k·g·μ ≤ deg Ranch = ℓ, k ≤ ⌊ℓ/(gμ)⌋.
difficulty: medium-hard.  hypothesis_fields: none.
-/
import Mathlib
import LeanUrat.MovesD.Defs

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesD
open LeanUrat.Moves LeanUrat.MovesC

variable {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]

/-- The coefficient of `Ranch` at position `N`: `pat N` inside the pattern window
`[0, ℓ]` (ℓ = wSide/e), zero beyond it. From `hRanch` (the consecutive-power pattern sum). -/
private lemma ranch_coeff_eq (ν : Node p F) (N : ℕ) :
    ν.Ranch.coeff N = if N ≤ ν.wSide / ν.e then ν.pat N else 0 := by
  rw [ν.hRanch, Polynomial.finsetSum_coeff]
  simp only [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq (Finset.range (ν.wSide / ν.e + 1)) N (fun k => ν.pat k)]
  simp [Finset.mem_range]

/-- `Ranch ≠ 0`: its top pattern coefficient `pat (ℓ)` is nonzero (`hpatTop`). -/
private lemma ranch_ne_zero (ν : Node p F) : ν.Ranch ≠ 0 := by
  intro h
  have hc := ranch_coeff_eq ν (ν.wSide / ν.e)
  rw [if_pos (le_refl _), h, Polynomial.coeff_zero] at hc
  exact ν.hpatTop hc.symm

/-- `deg Ranch ≤ ℓ = wSide/e`: no pattern coefficient sits beyond the window. -/
private lemma ranch_natDegree_le (ν : Node p F) : ν.Ranch.natDegree ≤ ν.wSide / ν.e := by
  rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
  intro N hN
  rw [ranch_coeff_eq ν N, if_neg (by omega)]

/-- Distinct monic irreducible polynomials over a field are coprime (they are non-associate
irreducibles; a divisibility would force an associate, hence — being monic — equality). -/
private lemma coprime_of_distinct_monic_irr {K : Type*} [Field K] {a b : Polynomial K}
    (hma : a.Monic) (hmb : b.Monic) (ha : Irreducible a) (hb : Irreducible b) (hab : a ≠ b) :
    IsCoprime a b := by
  rw [ha.coprime_iff_not_dvd]
  intro hdvd
  exact hab (Polynomial.eq_of_monic_of_associated hma hmb (ha.associated_of_dvd hb hdvd))

/-- The K-side eligible-factor count is bounded by m̄ = ⌊ℓ/(g·μ)⌋. -/
theorem eligible_card_le (ν : Node p F) :
    Nat.card {q : Polynomial ↥ν.σ.K //
        q.Monic ∧ Irreducible q ∧ q.natDegree = ν.g ∧ OrdPsiPoly q ν.Ranch ν.μ}
      ≤ (ν.wSide / ν.e) / (ν.g * ν.μ) := by
  have hgμ : 0 < ν.g * ν.μ := Nat.mul_pos ν.hg ν.hμ
  have hRne : ν.Ranch ≠ 0 := ranch_ne_zero ν
  have hdeg : ν.Ranch.natDegree ≤ ν.wSide / ν.e := ranch_natDegree_le ν
  -- The core bound on any FINITE set of eligible factors: the product of the `q^μ` over the
  -- set is a divisor of `Ranch` (pairwise-coprime prime powers), so its degree `k·g·μ` is at
  -- most `deg Ranch ≤ ℓ`, whence `k ≤ ⌊ℓ/(g·μ)⌋`.
  have key : ∀ t : Finset (Polynomial ↥ν.σ.K),
      (∀ q ∈ t, q.Monic ∧ Irreducible q ∧ q.natDegree = ν.g ∧ OrdPsiPoly q ν.Ranch ν.μ) →
      t.card ≤ (ν.wSide / ν.e) / (ν.g * ν.μ) := by
    intro t ht
    have hprod : (∏ q ∈ t, q ^ ν.μ) ∣ ν.Ranch := by
      apply Finset.prod_dvd_of_coprime
      · intro a ha b hb hab
        simp only [Finset.mem_coe] at ha hb
        simp only [Function.onFun]
        exact (coprime_of_distinct_monic_irr (ht a ha).1 (ht b hb).1
          (ht a ha).2.1 (ht b hb).2.1 hab).pow
      · intro q hq
        exact (ht q hq).2.2.2.1
    have hdegprod : (∏ q ∈ t, q ^ ν.μ).natDegree ≤ ν.Ranch.natDegree :=
      Polynomial.natDegree_le_of_dvd hprod hRne
    have hdegeq : (∏ q ∈ t, q ^ ν.μ).natDegree = t.card * (ν.g * ν.μ) := by
      rw [Polynomial.natDegree_prod t (fun q => q ^ ν.μ)
            (fun q hq => pow_ne_zero _ (ht q hq).1.ne_zero)]
      simp only [Polynomial.natDegree_pow]
      have step : ∀ q ∈ t, ν.μ * q.natDegree = ν.μ * ν.g :=
        fun q hq => by rw [(ht q hq).2.2.1]
      rw [Finset.sum_congr rfl step, Finset.sum_const, smul_eq_mul, Nat.mul_comm ν.μ ν.g]
    rw [hdegeq] at hdegprod
    rw [Nat.le_div_iff_mul_le hgμ]
    exact le_trans hdegprod hdeg
  -- Transfer the Finset bound to `Nat.card`: finite ⇒ apply `key` to `univ.image val`;
  -- infinite ⇒ `Nat.card = 0`.
  by_cases hfin : Finite {q : Polynomial ↥ν.σ.K //
      q.Monic ∧ Irreducible q ∧ q.natDegree = ν.g ∧ OrdPsiPoly q ν.Ranch ν.μ}
  · haveI := hfin
    haveI : Fintype {q : Polynomial ↥ν.σ.K //
        q.Monic ∧ Irreducible q ∧ q.natDegree = ν.g ∧ OrdPsiPoly q ν.Ranch ν.μ} :=
      Fintype.ofFinite _
    classical
    have hc := key (Finset.image (fun x : {q : Polynomial ↥ν.σ.K //
        q.Monic ∧ Irreducible q ∧ q.natDegree = ν.g ∧ OrdPsiPoly q ν.Ranch ν.μ} => x.val)
        Finset.univ) (by
      intro q hq
      rw [Finset.mem_image] at hq
      obtain ⟨x, -, rfl⟩ := hq
      exact x.2)
    rwa [Finset.card_image_of_injective _ Subtype.val_injective, Finset.card_univ,
      ← Nat.card_eq_fintype_card] at hc
  · rw [not_finite_iff_infinite] at hfin
    haveI := hfin
    rw [Nat.card_eq_zero_of_infinite]
    exact Nat.zero_le _

end LeanUrat.MovesD
