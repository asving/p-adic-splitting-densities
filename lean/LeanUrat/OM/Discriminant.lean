/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.OM.QuotientBox
import LeanUrat.OM.ResidualPolynomial
import LeanUrat.OM.ResidueCount

/-!
# F4 (part 1) — Discriminant as a coefficient polynomial (blueprint nodes L-B1, L-B2, L-B3)

This module builds the *static* (B-independent) discriminant-as-coefficient-polynomial stack of
Layer F4, the half of F4 that needs no classifier and no serial spine.

The mathematical content packaged here:

* **L-B1** (`disc_is_coeff_polynomial`): the discriminant of a monic degree-`n` polynomial is a
  *fixed* integer polynomial `Δ_n : MvPolynomial (Fin n) ℤ` (the discriminant of the universal monic
  `X^n + ∑ C(X_i)·X^i`) evaluated at the coefficient tuple, base-changed to any commutative ring.
  The genuine content is the *naturality of the discriminant under a ring hom for monic polynomials*
  (`discr_map_monic`), which mathlib does **not** have (`Polynomial.discr` exists but there is no
  `discr_map`); we derive it from `resultant_deriv` + `resultant_map_map` + `derivative_map`.

* **L-B2** (`Delta_nonzero_mod_p`): `Δ_n` reduced mod `p` is not the zero polynomial for `n ≥ 2`.
  This is the hypothesis Stage-C's local Schwartz–Zippel needs. Proof: a monic *separable* degree-`n`
  polynomial over the field `ZMod p` exists (its discriminant is nonzero, via separable ⟺ coprime ⟺
  resultant nonzero), and `Δ_n mod p` evaluated at its coefficient tuple equals that nonzero
  discriminant, so `Δ_n mod p ≠ 0`.

* **L-B3** (`discZeroCount_eq_eval_card`): the count of monic polynomials in the level-`N` box with
  vanishing discriminant equals the count of coefficient tuples on which `Δ_n mod p^N` vanishes,
  transported across the `degreeLTEquiv` coefficient bijection (the same bijection used in M1's
  `card_monicBox`).

All three are **B-independent** and closed `sorry`-free (core axioms only).

VERIFIED MATHLIB ANCHORS used:
* `Polynomial.discr` (Resultant/Basic.lean:930), `resultant_deriv` (:973),
  `resultant_map_map` (:140), `resultant_eq_zero_iff` (:908).
* `Polynomial.derivative_map`, `Polynomial.Monic.natDegree_map`, `Polynomial.Monic.map`,
  `Polynomial.separable_def`, `PerfectField.separable_iff_squarefree`.
* `Polynomial.degreeLTEquiv` (RingTheory/Polynomial/Basic.lean:111).
* `MvPolynomial.eval`, `MvPolynomial.eval_map`, `MvPolynomial.aeval`.
* `QuotientBox.monicBox`, `QuotientBox.card_monicBox` (M1).
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false

namespace LeanUrat.OM.M_F4

open Polynomial

/-! ## 0. Discriminant of a monic polynomial via the resultant -/

variable {R S : Type*} [CommRing R] [CommRing S]

/-- For a monic polynomial of positive degree, the discriminant is `± resultant f f'`.
This repackages mathlib's `Polynomial.resultant_deriv` for the monic case
(`leadingCoeff = 1`), and is the bridge that lets us transport `discr` through a ring hom
via the (already-natural) resultant. -/
theorem discr_monic_eq_resultant (f : R[X]) (hf : f.Monic) (hpos : 0 < f.natDegree) :
    f.discr =
      (-1) ^ (f.natDegree * (f.natDegree - 1) / 2) *
        resultant f f.derivative f.natDegree (f.natDegree - 1) := by
  have hdeg : 0 < f.degree := natDegree_pos_iff_degree_pos.mp hpos
  have h := resultant_deriv hdeg
  rw [hf.leadingCoeff, mul_one] at h
  -- h : resultant f f' n (n-1) = (-1)^k * discr f, multiply both sides by (-1)^k.
  have hsq : ((-1 : R) ^ (f.natDegree * (f.natDegree - 1) / 2)) *
      ((-1 : R) ^ (f.natDegree * (f.natDegree - 1) / 2)) = 1 := by
    rw [← pow_add, ← two_mul, pow_mul]; simp
  calc f.discr
      = 1 * f.discr := (one_mul _).symm
    _ = ((-1) ^ (f.natDegree * (f.natDegree - 1) / 2) *
          (-1) ^ (f.natDegree * (f.natDegree - 1) / 2)) * f.discr := by rw [hsq]
    _ = (-1) ^ (f.natDegree * (f.natDegree - 1) / 2) *
          ((-1) ^ (f.natDegree * (f.natDegree - 1) / 2) * f.discr) := by ring
    _ = (-1) ^ (f.natDegree * (f.natDegree - 1) / 2) *
          resultant f f.derivative f.natDegree (f.natDegree - 1) := by rw [← h]

/-- **L-B1 core — discriminant naturality for monic polynomials.**
`discr` commutes with any ring hom on monic polynomials. (mathlib has no `discr_map`; this is the
genuine content, derived through the resultant which *is* natural.) -/
theorem discr_map_monic (φ : R →+* S) (f : R[X]) (hf : f.Monic) :
    (f.map φ).discr = φ f.discr := by
  -- Degenerate degree-0 case: a monic constant is `1`, discr = 1.
  rcases Nat.eq_zero_or_pos f.natDegree with hz | hpos
  · have hf1 : f = 1 := eq_one_of_monic_natDegree_zero hf hz
    subst hf1
    have h1R : discr (1 : R[X]) = 1 := by rw [← C_1]; exact discr_C 1
    have h1S : discr (1 : S[X]) = 1 := by rw [← C_1]; exact discr_C 1
    rw [Polynomial.map_one, h1R, h1S, map_one]
  -- Positive degree: use the resultant bridge.
  by_cases hS : Nontrivial S
  · have hmap : (f.map φ).Monic := hf.map φ
    have hdeg : (f.map φ).natDegree = f.natDegree := hf.natDegree_map φ
    have hpos' : 0 < (f.map φ).natDegree := by rw [hdeg]; exact hpos
    rw [discr_monic_eq_resultant f hf hpos,
        discr_monic_eq_resultant (f.map φ) hmap hpos']
    -- derivative commutes with map; resultant_map_map handles the rest.
    have hder : (f.map φ).derivative = f.derivative.map φ := derivative_map f φ
    rw [hder, hdeg]
    rw [resultant_map_map]
    rw [map_mul, map_pow, map_neg, map_one]
  · -- S is trivial: every element of S is equal, so the goal is trivially `0 = 0`-style.
    rw [not_nontrivial_iff_subsingleton] at hS
    exact Subsingleton.elim _ _

/-! ## 1. The universal monic and the universal discriminant `Δ_n` -/

/-- The universal monic polynomial of degree `n` over `MvPolynomial (Fin n) ℤ`:
`X^n + ∑_{i < n} C(X_i) · X^i`, where `X_i` are the `n` free coefficient variables. -/
noncomputable def univMonic (n : ℕ) : (MvPolynomial (Fin n) ℤ)[X] :=
  Polynomial.X ^ n + ∑ i : Fin n, Polynomial.C (MvPolynomial.X i) * Polynomial.X ^ (i : ℕ)

/-- The "tail" `∑_{i<n} C(X_i)·X^i` has degree `< n`. -/
theorem univMonic_tail_degree_lt (n : ℕ) :
    (∑ i : Fin n, Polynomial.C (MvPolynomial.X i) * Polynomial.X ^ (i : ℕ)
      : (MvPolynomial (Fin n) ℤ)[X]).degree < (n : ℕ) := by
  apply lt_of_le_of_lt (degree_sum_le _ _)
  rw [Finset.sup_lt_iff (by exact_mod_cast WithBot.bot_lt_coe n)]
  intro i _
  rw [C_mul_X_pow_eq_monomial]
  exact lt_of_le_of_lt (degree_monomial_le _ _) (by exact_mod_cast i.isLt)

/-- The universal monic is monic. -/
theorem univMonic_monic (n : ℕ) : (univMonic n).Monic := by
  rw [univMonic]
  have h := univMonic_tail_degree_lt n
  rw [← degree_X_pow (R := MvPolynomial (Fin n) ℤ) n] at h
  exact (monic_X_pow n).add_of_left h

/-- The universal monic has degree `n`. -/
theorem univMonic_natDegree (n : ℕ) : (univMonic n).natDegree = n := by
  rw [univMonic]
  have h := univMonic_tail_degree_lt n
  apply natDegree_eq_of_degree_eq_some
  rw [add_comm, degree_add_eq_right_of_degree_lt, degree_X_pow]
  rwa [degree_X_pow]

/-- The `i`-th coefficient of the universal monic (for `i < n`) is the variable `X_i`. -/
theorem univMonic_coeff_lt (n : ℕ) (i : ℕ) (hi : i < n) :
    (univMonic n).coeff i = MvPolynomial.X ⟨i, hi⟩ := by
  rw [univMonic, coeff_add]
  have hXpow : (Polynomial.X ^ n : (MvPolynomial (Fin n) ℤ)[X]).coeff i = 0 := by
    rw [coeff_X_pow]; rw [if_neg (by omega)]
  rw [hXpow, zero_add]
  rw [finsetSum_coeff]
  rw [Finset.sum_eq_single (⟨i, hi⟩ : Fin n)]
  · rw [coeff_C_mul, coeff_X_pow, if_pos rfl, mul_one]
  · intro j _ hj
    rw [coeff_C_mul, coeff_X_pow, if_neg, mul_zero]
    intro hcon
    exact hj (Fin.ext hcon.symm)
  · intro hcon; exact absurd (Finset.mem_univ _) hcon

/-- The **universal discriminant** `Δ_n : MvPolynomial (Fin n) ℤ`, the discriminant of the universal
monic. By `disc_is_coeff_polynomial` this is the fixed integer polynomial in the coefficients whose
value (after base change) is the discriminant of any monic degree-`n` polynomial. -/
noncomputable def Delta (n : ℕ) : MvPolynomial (Fin n) ℤ := (univMonic n).discr

/-! ## 2. L-B1 — discriminant as evaluation of `Δ_n` at the coefficient tuple -/

/-- The coefficient tuple of a polynomial `f` over `R`: the free (non-leading) coefficients
`a i = f.coeff i` for `i : Fin n`. -/
def coeffTuple (n : ℕ) (f : R[X]) : Fin n → R := fun i => f.coeff (i : ℕ)

/-- The ring hom `MvPolynomial (Fin n) ℤ →+* R` given by evaluating the variables at a tuple `a`
(and `ℤ` via its canonical map). This is `MvPolynomial.eval₂Hom (Int.castRingHom R) a`. -/
noncomputable def coeffEval (n : ℕ) (a : Fin n → R) : MvPolynomial (Fin n) ℤ →+* R :=
  MvPolynomial.eval₂Hom (Int.castRingHom R) a

/-- Evaluating the universal monic through `coeffEval n a` (mapped over its coefficients) gives back
the monic polynomial `X^n + ∑ C(a i) X^i` whose free coefficients are `a`. -/
theorem map_coeffEval_univMonic (n : ℕ) (a : Fin n → R) :
    (univMonic n).map (coeffEval n a) =
      Polynomial.X ^ n + ∑ i : Fin n, Polynomial.C (a i) * Polynomial.X ^ (i : ℕ) := by
  rw [univMonic, Polynomial.map_add, Polynomial.map_pow, map_X, Polynomial.map_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [Polynomial.map_mul, map_C, Polynomial.map_pow, map_X]
  congr 2
  rw [coeffEval, MvPolynomial.eval₂Hom_X']

/-- **L-B1 — `disc_is_coeff_polynomial`.**
The discriminant of a monic degree-`n` polynomial `f` over `R` equals `Δ_n` evaluated at the
coefficient tuple of `f` (with `Δ_n`'s integer coefficients base-changed into `R`).

Concretely: `f.discr = (Δ_n.map (Int.castRingHom R)).eval (coeffTuple n f)` for `f` monic of
degree `n`. The fixed integer polynomial `Δ_n` is the discriminant of the universal monic. -/
theorem disc_is_coeff_polynomial (n : ℕ) (f : R[X]) (hf : f.Monic) (hdeg : f.natDegree = n) :
    f.discr = MvPolynomial.eval (coeffTuple n f) ((Delta n).map (Int.castRingHom R)) := by
  -- First: the map of the universal monic through `coeffEval n (coeffTuple n f)` recovers `f`.
  have hrecover : (univMonic n).map (coeffEval n (coeffTuple n f)) = f := by
    rw [map_coeffEval_univMonic]
    -- f = X^n + ∑_{i<n} C(f.coeff i) X^i, since f is monic of degree n.
    have hfsum : f = Polynomial.X ^ n + ∑ i : Fin n, Polynomial.C (f.coeff i) * Polynomial.X ^ (i : ℕ) := by
      conv_lhs =>
        rw [f.as_sum_range_C_mul_X_pow' (n := n + 1) (by rw [← hdeg]; exact Nat.lt_succ_of_le (le_refl _))]
      -- ∑_{i ∈ range(n+1)} C(coeff i) X^i  = lower terms + top term
      rw [Finset.sum_range_succ]
      -- top term: i = n, coeff n = leadingCoeff = 1 (monic, deg n)
      have htop : f.coeff n = 1 := by rw [← hdeg]; exact hf.coeff_natDegree
      rw [htop, map_one, one_mul, add_comm]
      congr 1
      -- ∑_{i : Fin n} C(coeff i) X^i = ∑_{i ∈ range n} C(coeff i) X^i
      exact (Fin.sum_univ_eq_sum_range (fun i => Polynomial.C (f.coeff i) * Polynomial.X ^ i) n).symm
    -- the recovered polynomial uses a = coeffTuple n f, and coeffTuple n f i = f.coeff i
    simp only [coeffTuple]
    exact hfsum.symm
  -- Apply discr naturality (L-B1 core) to the universal monic and the hom coeffEval.
  have hnat := discr_map_monic (coeffEval n (coeffTuple n f)) (univMonic n) (univMonic_monic n)
  rw [hrecover] at hnat
  -- hnat : f.discr = coeffEval n (coeffTuple n f) (univMonic n).discr = coeffEval ... (Delta n)
  rw [hnat, Delta]
  -- LHS: coeffEval n a (univMonic n).discr = eval₂ (Int.castRingHom R) a (univMonic n).discr
  -- RHS: eval a ((univMonic n).discr.map (Int.castRingHom R)) = eval₂ (Int.castRingHom R) a _
  rw [MvPolynomial.eval_map]
  rw [coeffEval]
  rfl

/-! ## 3. L-B2 — `Δ_n` is nonzero mod `p` -/

variable (p : ℕ) [hp : Fact p.Prime]

/-- For a monic polynomial, the resultant with `f'` taken at the (over-specified) degree `n - 1`
equals the default-degree resultant `resultant f f'`. (Overspecifying the second degree multiplies
by `leadingCoeff(f)^k = 1`, via `resultant_add_right_deg`.) -/
theorem resultant_deriv_eq_default {f : R[X]} (hf : f.Monic) :
    resultant f f.derivative f.natDegree (f.natDegree - 1) = resultant f f.derivative := by
  have hle : f.derivative.natDegree ≤ f.natDegree - 1 := natDegree_derivative_le f
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hle  -- n-1 = f'.natDegree + k
  rw [hk]
  -- resultant f f' n (f'.natDegree + k) = f.coeff n ^ k * resultant f f' n f'.natDegree
  rw [resultant_add_right_deg f f.derivative f.natDegree f.derivative.natDegree k (le_refl _)]
  -- f.coeff f.natDegree = leadingCoeff f = 1, and resultant f f' n f'.natDegree = default
  rw [hf.coeff_natDegree, one_pow, one_mul]

/-- A monic separable polynomial over a field has nonzero discriminant.
Separable ⟺ `IsCoprime f f'` (`separable_def`) ⟹ `IsUnit (resultant f f')`
(`isUnit_resultant_iff_isCoprime`, monic) ⟹ `resultant f f' ≠ 0`; and `discr = ± resultant` for
monic (`discr_monic_eq_resultant`). This is char-uniform: it holds for **every** prime `p` and degree
`n` (no `p ∤ n` restriction), because the overspecified-degree resultant is invariant for monic `f`,
dissolving the wild/small-`p` caveat flagged in the blueprint. -/
theorem discr_ne_zero_of_separable_monic {K : Type*} [Field K] (f : K[X]) (hf : f.Monic)
    (hpos : 0 < f.natDegree) (hsep : f.Separable) : f.discr ≠ 0 := by
  have hcop : IsCoprime f f.derivative := (separable_def f).mp hsep
  have hunit : IsUnit (resultant f f.derivative) :=
    (isUnit_resultant_iff_isCoprime hf).mpr hcop
  have hres : resultant f f.derivative f.natDegree (f.natDegree - 1) ≠ 0 := by
    rw [resultant_deriv_eq_default hf]
    exact hunit.ne_zero
  rw [discr_monic_eq_resultant f hf hpos]
  refine mul_ne_zero (pow_ne_zero _ ?_) hres
  norm_num

/-! ### A separable monic witness over `ZMod p`

For `L-B2` we only need a separable monic of degree `n` to *exist* (for `n ≥ 2`). The squarefree
monic count `Q^n - Q^{n-1}` (`L3Squarefree.card_squarefreeMonicDegree`, proved) is positive, so a
squarefree monic of degree `n` exists; over the perfect field `ZMod p`, squarefree ⟺ separable. -/

/-- The squarefree monic count over `ZMod p` is positive for `n ≥ 2`.
(Uses the proved, `sorry`-free squarefree count `M0.card_squarefreeMonicDegree`,
re-exporting `L3Squarefree.card_squarefreeMonicDegree`.) -/
theorem squarefreeMonicCount_pos (n : ℕ) (hn : 2 ≤ n) :
    0 < Nat.card (LeanUrat.L3.squarefreeMonicDegree (ZMod p) n) := by
  haveI : Fact (Nat.Prime p) := hp
  rw [LeanUrat.OM.M0.card_squarefreeMonicDegree (F := ZMod p) n hn]
  have hcard : 2 ≤ Nat.card (ZMod p) := by
    rw [Nat.card_eq_fintype_card, ZMod.card]; exact hp.out.two_le
  -- Q^n - Q^{n-1} > 0  since  Q^{n-1} < Q^n  (Q ≥ 2, n ≥ 1).
  apply Nat.sub_pos_of_lt
  apply Nat.pow_lt_pow_right (by omega)
  omega

/-- **A monic separable polynomial of degree `n` exists over `ZMod p`** for `n ≥ 2`. -/
theorem exists_separable_monic_zmod (n : ℕ) (hn : 2 ≤ n) :
    ∃ f : (ZMod p)[X], f.Monic ∧ f.natDegree = n ∧ f.Separable := by
  haveI : Fact (Nat.Prime p) := hp
  -- nonempty squarefree monic set
  have hpos := squarefreeMonicCount_pos p n hn
  rw [Nat.card_pos_iff] at hpos
  obtain ⟨⟨⟨f, hf⟩⟩, _⟩ := hpos
  obtain ⟨hmonic, hdeg, hsqfree⟩ := hf
  refine ⟨f, hmonic, hdeg, ?_⟩
  -- over the perfect field ZMod p: squarefree ⟺ separable
  rw [PerfectField.separable_iff_squarefree]
  exact hsqfree

/-! ## 4. L-B2 — `Δ_n` is nonzero mod `p` (for `n ≥ 2`) -/

/-- **L-B2 — `Delta_nonzero_mod_p`.**
The universal discriminant `Δ_n` reduced mod `p` is **not** the zero polynomial, for `n ≥ 2`.

Proof: take a monic separable degree-`n` witness `f` over the field `ZMod p`
(`exists_separable_monic_zmod`); its discriminant `f.discr ≠ 0` (`discr_ne_zero_of_separable_monic`).
By L-B1 (`disc_is_coeff_polynomial`), `f.discr = eval (coeffTuple n f) (Δ_n.map (Int.castRingHom ..))`.
If `Δ_n.map (Int.castRingHom (ZMod p))` were `0` then every evaluation, including this one, would be
`0` — contradicting `f.discr ≠ 0`. (Char-uniform: works for every prime `p`, dissolving the
small-`p` wild caveat flagged in the blueprint, since the resultant route used in
`discr_ne_zero_of_separable_monic` needs no `p ∤ n` hypothesis.) -/
theorem Delta_nonzero_mod_p (n : ℕ) (hn : 2 ≤ n) :
    (Delta n).map (Int.castRingHom (ZMod p)) ≠ 0 := by
  haveI : Fact (Nat.Prime p) := hp
  obtain ⟨f, hmonic, hdeg, hsep⟩ := exists_separable_monic_zmod p n hn
  have hpos : 0 < f.natDegree := by rw [hdeg]; omega
  have hne : f.discr ≠ 0 := discr_ne_zero_of_separable_monic f hmonic hpos hsep
  intro hzero
  apply hne
  rw [disc_is_coeff_polynomial n f hmonic hdeg, hzero, map_zero]

/-! ## 5. L-B3 — `discZeroCount = #{coeff tuples with Δ_n-eval = 0}`

The level-`N` "disc-zero" locus is the set of monic degree-`n` polynomials over `ZMod (p^N)` with
vanishing discriminant. Its cardinality equals the count of coefficient tuples on which
`Δ_n mod p^N` vanishes, transported across the coefficient bijection
`(Fin n → ZMod (p^N)) ≃ monicBox p N n` (the same bijection used in M1's `card_monicBox`). -/

open QuotientBox

/-- The disc-zero set: monic degree-`n` polynomials over `ZMod (p^N)` whose discriminant vanishes. -/
def discZeroSet (N n : ℕ) : Set (monicBox p N n) := {f | (f.1).discr = 0}

/-- The disc-zero count (a genuine `Nat.card`, no measure). -/
noncomputable def discZeroCount (N n : ℕ) : ℕ :=
  Nat.card {f : monicBox p N n // (f.1).discr = 0}

/-- The monic obtained from a coefficient tuple: `X^n + ∑_{i<n} C(a i) X^i`.
This is the inverse direction of the coefficient bijection. -/
noncomputable def coeffToMonicVal (N n : ℕ) (a : Fin n → ResidueRing p N) : (ResidueRing p N)[X] :=
  Polynomial.X ^ n + ∑ i : Fin n, Polynomial.C (a i) * Polynomial.X ^ (i : ℕ)

theorem coeffToMonicVal_monic_deg (N n : ℕ) (hN : 0 < N) (a : Fin n → ResidueRing p N) :
    (coeffToMonicVal p N n a).Monic ∧ (coeffToMonicVal p N n a).natDegree = n := by
  haveI : Fact (1 < p ^ N) := ⟨Nat.one_lt_pow hN.ne' hp.out.one_lt⟩
  haveI : Nontrivial (ResidueRing p N) := inferInstance
  have hdlt : (∑ i : Fin n, Polynomial.C (a i) * Polynomial.X ^ (i : ℕ)
      : (ResidueRing p N)[X]).degree < (Polynomial.X ^ n : (ResidueRing p N)[X]).degree := by
    rw [degree_X_pow]
    apply lt_of_le_of_lt (degree_sum_le _ _)
    rw [Finset.sup_lt_iff (by exact_mod_cast WithBot.bot_lt_coe n)]
    intro i _
    rw [C_mul_X_pow_eq_monomial]
    exact lt_of_le_of_lt (degree_monomial_le _ _) (by exact_mod_cast i.isLt)
  refine ⟨(monic_X_pow n).add_of_left hdlt, natDegree_eq_of_degree_eq_some ?_⟩
  rw [coeffToMonicVal, add_comm, degree_add_eq_right_of_degree_lt hdlt, degree_X_pow]

/-- The coefficient of `coeffToMonicVal a` at `i < n` is `a i` (the `X^n` term is degree `n`). -/
theorem coeffToMonicVal_coeff_lt (N n : ℕ) (a : Fin n → ResidueRing p N) (i : ℕ) (hi : i < n) :
    (coeffToMonicVal p N n a).coeff i = a ⟨i, hi⟩ := by
  rw [coeffToMonicVal, coeff_add]
  have hXpow : (Polynomial.X ^ n : (ResidueRing p N)[X]).coeff i = 0 := by
    rw [coeff_X_pow, if_neg (by omega)]
  rw [hXpow, zero_add, finsetSum_coeff, Finset.sum_eq_single (⟨i, hi⟩ : Fin n)]
  · rw [coeff_C_mul, coeff_X_pow, if_pos rfl, mul_one]
  · intro j _ hj
    rw [coeff_C_mul, coeff_X_pow, if_neg, mul_zero]
    intro hcon; exact hj (Fin.ext hcon.symm)
  · intro hcon; exact absurd (Finset.mem_univ _) hcon

/-- The coefficient bijection `(Fin n → ZMod (p^N)) ≃ monicBox p N n`, `a ↦ ⟨X^n + ∑ C(a i) X^i, _⟩`.
Same construction as M1's `card_monicBox` (`degreeLTEquiv` route). -/
noncomputable def coeffEquivMonicBox (N n : ℕ) (hN : 0 < N) :
    (Fin n → ResidueRing p N) ≃ monicBox p N n := by
  haveI : Fact (1 < p ^ N) := ⟨Nat.one_lt_pow hN.ne' hp.out.one_lt⟩
  refine Equiv.ofBijective
    (fun a => ⟨coeffToMonicVal p N n a, coeffToMonicVal_monic_deg p N n hN a⟩) ?_
  constructor
  · -- injective: equal monics ⟹ equal coefficient tuples (compare coeff i for i < n)
    intro a b hab
    funext i
    have h1 := coeffToMonicVal_coeff_lt p N n a i i.isLt
    have h2 := coeffToMonicVal_coeff_lt p N n b i i.isLt
    have hval : coeffToMonicVal p N n a = coeffToMonicVal p N n b :=
      congrArg Subtype.val hab
    have hcoeff : (coeffToMonicVal p N n a).coeff i = (coeffToMonicVal p N n b).coeff i := by
      rw [hval]
    rw [h1, h2] at hcoeff
    simpa using hcoeff
  · -- surjective: a monic of degree n is X^n + (its tail), whose tail coeffs give the tuple
    rintro ⟨q, hqmonic, hqdeg⟩
    refine ⟨coeffTuple n q, ?_⟩
    apply Subtype.ext
    show coeffToMonicVal p N n (coeffTuple n q) = q
    -- q = X^n + ∑_{i<n} C(q.coeff i) X^i since q is monic of degree n
    have hqsum : q = Polynomial.X ^ n
        + ∑ i : Fin n, Polynomial.C (q.coeff i) * Polynomial.X ^ (i : ℕ) := by
      conv_lhs =>
        rw [q.as_sum_range_C_mul_X_pow' (n := n + 1)
          (by rw [hqdeg]; exact Nat.lt_succ_of_le (le_refl _))]
      rw [Finset.sum_range_succ]
      have htop : q.coeff n = 1 := by rw [← hqdeg]; exact hqmonic.coeff_natDegree
      rw [htop, map_one, one_mul, add_comm]
      congr 1
      exact (Fin.sum_univ_eq_sum_range (fun i => Polynomial.C (q.coeff i) * Polynomial.X ^ i) n).symm
    rw [coeffToMonicVal]
    simp only [coeffTuple]
    exact hqsum.symm

/-- **L-B3 — `discZeroCount_eq_eval_card`.**
The disc-zero count equals the count of coefficient tuples on which `Δ_n mod p^N` vanishes.
Transports `discr = 0 ↔ eval (coeffTuple) (Δ_n.map cast) = 0` (L-B1) across the coefficient
bijection. -/
theorem discZeroCount_eq_eval_card (N n : ℕ) (hN : 0 < N) :
    discZeroCount p N n =
      Nat.card {a : Fin n → ResidueRing p N //
        MvPolynomial.eval a ((Delta n).map (Int.castRingHom (ResidueRing p N))) = 0} := by
  rw [discZeroCount]
  -- Build a subtype equiv along coeffEquivMonicBox, matching the two predicates by L-B1.
  let e := coeffEquivMonicBox p N n hN
  symm
  apply Nat.card_congr
  apply Equiv.subtypeEquiv e
  intro a
  -- predicate on a:  eval a (Δ_n.map cast) = 0
  -- predicate on (e a):  (e a).1.discr = 0
  have hmonic := ((e a).2).1
  have hdeg := ((e a).2).2
  -- coeffTuple n (e a).1 = a
  have htuple : coeffTuple n (e a).1 = a := by
    funext i
    show (e a).1.coeff (i : ℕ) = a i
    have : (e a).1 = coeffToMonicVal p N n a := rfl
    rw [this, coeffToMonicVal_coeff_lt p N n a (i : ℕ) i.isLt]
  -- L-B1: (e a).1.discr = eval (coeffTuple n (e a).1) (Δ_n.map cast)
  have hLB1 := disc_is_coeff_polynomial n (e a).1 hmonic hdeg
  rw [htuple] at hLB1
  -- now both predicates: eval a (Δ_n.map cast) = 0  ↔  (e a).1.discr = 0
  rw [hLB1]
  -- goal is now  (eval a ... = 0) ↔ (eval a ... = 0)

end LeanUrat.OM.M_F4
