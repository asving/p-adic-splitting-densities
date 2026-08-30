/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import Uniformity.ChapI.IFCG18

/-!
# Uniformity.ChapI.IFCG19 — [GAUSS2 2026-08-30] the uniform irreducible census and the
e = 1 clause of the single-point kernel

**[GAUSS2 2026-08-30]** (verdict `runs/wave-c/verdict_GAUSS.md`; finisher of the hung
GAUSS unit).  Two deliverables:

* **§1–§2 the uniform Gauss/necklace census** — for EVERY finite field `K` (card `q`) and
  EVERY degree `δ ≥ 1`:

    `Σ_{d ∣ δ} d · N_d = q^δ`   and   `δ · N_δ = Σ_{ab = δ} μ(a) · q^b`,

  where `N_d = Nat.card (IFCG4.IrredOfDeg K d)` is the count of monic irreducible
  polynomials of degree `d` (IFCG4's carrier; also `= (irredFinset K d).card`, IFCG17's
  `Finset`).  Proof: the Frobenius polynomial `Φ_δ = X^(q^δ) − X` is monic of degree
  `q^δ`, separable (`galois_poly_separable`), and its monic irreducible factors are
  EXACTLY the monic irreducibles of degree `d ∣ δ` — the hard divisibility direction is
  mathlib's `Irreducible.natDegree_dvd_of_dvd_X_pow_card_pow_sub_X`, the easy direction
  is `AdjoinRoot` + `FiniteField.pow_card_pow`; reading `natDegree` off the squarefree
  factorization gives the degree-sum identity, and `ArithmeticFunction`'s Möbius
  inversion (`sum_eq_iff_sum_smul_moebius_eq`) gives the closed necklace form.  The
  `ℚ`-polynomial packaging `necklacePoly δ` (one polynomial, evaluated at `q`) is what
  `URLim` consumes.  This closes IFCG4's honestly-left-open general-`δ` gap (its §1
  pinned `δ ≤ 4` only).

* **§3–§4 the e = 1 consumption** — ★ the `E = [1]` clause of IFCG18's
  `SinglePointAggregateLaw` CLOSES, for ALL `δ ≥ 1`, UNCONDITIONALLY (no smaller value
  laws needed, no unramified base-change leg): over an irreducible residue polynomial
  `p` of degree `δ` the whole level-`N` stratum is decided at the inert type
  `⟨{(1, δ)}⟩` (H124's `decidedAt_of_mem_levelZeroStratum_irreducible` — degree-uniform)
  and has exactly `q^(δ(N−1))` classes (H124b's `card_levelZeroStratum`), so
  `stratPoly O δ N p` is the MONOMIAL `single {(1,δ)} q^(δ(N−1))` and the normalized
  single-point aggregate is the CONSTANT `N_δ(q)/q^δ` for every `N ≥ 1` — a `URLim`
  family with numerator `necklacePoly δ` and denominator `X^δ`.
  ⚠ IFCG18's scoping note conjectured a base-change leg at `δ ≥ 2`; H124's one-factor
  base is degree-uniform, so no such leg exists at `e = 1`.  The base change enters only
  at `e ≥ 2` (the deep-cone legs), which this file does NOT touch.

## What this does NOT prove

`SinglePointAggregateLaw` itself: blocks with some exponent `≥ 2` (fractional-slope /
deep-cone censuses) and the mixed lists `E` containing an entry `≥ 2` remain open, as
does `DeepLinearClusterLaw`.  The `E = List.replicate k 1` extension (same point, `k`
coincident unit exponents) is included (§4) since the monomial lemma powers through;
everything else is untouched.

## Axiom fence

Lean core everywhere (`propext`, `Classical.choice`, `Quot.sound`); no new axiom, no
`sorry`.  AxCheck footer at the end of the file.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

noncomputable section

namespace Uniformity.Density.IFCG19

open IsLocalRing Polynomial
open Uniformity.Density.Induction
open Uniformity.Density.IFCG17
open Uniformity.Density.IFCG18
open Uniformity.Density.IFCG14 (DecidedValueLaw)

attribute [local instance] Classical.propDecidable

/-! ## §1 — the Frobenius polynomial `X^(q^δ) − X` and the uniform census -/

section Census

open UniqueFactorizationMonoid

variable {K : Type*} [Field K] [Fintype K]

/-- **The Frobenius polynomial** `Φ_δ = X^(q^δ) − X` over a finite field of cardinality
`q`.  Its monic irreducible factors are exactly the monic irreducibles of degree `d ∣ δ`
(`irred_dvd_frobPoly_iff`), each once (squarefree). -/
def frobPoly (K : Type*) [Field K] [Fintype K] (δ : ℕ) : Polynomial K :=
  X ^ (Fintype.card K ^ δ) - X

theorem monic_frobPoly (δ : ℕ) (hδ : 1 ≤ δ) : (frobPoly K δ).Monic := by
  refine monic_X_pow_sub ?_
  rw [degree_X]
  exact_mod_cast Nat.one_lt_pow (by omega) Fintype.one_lt_card

theorem natDegree_frobPoly (δ : ℕ) (hδ : 1 ≤ δ) :
    (frobPoly K δ).natDegree = Fintype.card K ^ δ :=
  FiniteField.X_pow_card_pow_sub_X_natDegree_eq K (by omega) Fintype.one_lt_card

theorem frobPoly_ne_zero (δ : ℕ) (hδ : 1 ≤ δ) : frobPoly K δ ≠ 0 :=
  (monic_frobPoly δ hδ).ne_zero

/-- `Φ_δ` is squarefree: it is separable (`galois_poly_separable`, since the
characteristic divides `q^δ`). -/
theorem squarefree_frobPoly (δ : ℕ) (hδ : 1 ≤ δ) : Squarefree (frobPoly K δ) := by
  obtain ⟨n, hprime, hcard⟩ := FiniteField.card K (ringChar K)
  have hdvd : ringChar K ∣ Fintype.card K ^ δ := by
    refine dvd_trans ?_ (dvd_pow_self (Fintype.card K) (by omega))
    rw [hcard]
    exact dvd_pow_self (ringChar K) n.ne_zero
  exact (galois_poly_separable (ringChar K) (Fintype.card K ^ δ) hdvd).squarefree

/-- **The easy divisibility direction**: a monic irreducible of degree `d ∣ δ` divides
`Φ_δ`.  In `F = AdjoinRoot g` (a field of cardinality `q^d`) the root satisfies
`α^(q^δ) = α` because `q^δ = (q^d)^(δ/d)` and `x^(#F^c) = x` (`FiniteField.pow_card_pow`);
hence `g ∣ X^(q^δ) − X` by `AdjoinRoot.mk_eq_zero`. -/
theorem dvd_frobPoly_of_natDegree_dvd {g : Polynomial K} (hgm : g.Monic)
    (hgi : Irreducible g) {δ : ℕ} (hdvd : g.natDegree ∣ δ) : g ∣ frobPoly K δ := by
  haveI : Fact (Irreducible g) := ⟨hgi⟩
  obtain ⟨c, hc⟩ := hdvd
  letI : Fintype (AdjoinRoot g) :=
    Fintype.ofEquiv _ (AdjoinRoot.powerBasis (K := K) hgm.ne_zero).basis.equivFun.toEquiv.symm
  have hcard : Fintype.card (AdjoinRoot g) = Fintype.card K ^ g.natDegree := by
    rw [Fintype.card_congr (AdjoinRoot.powerBasis (K := K) hgm.ne_zero).basis.equivFun.toEquiv,
      Fintype.card_fun, Fintype.card_fin, AdjoinRoot.powerBasis_dim]
  have hroot : (AdjoinRoot.root g) ^ (Fintype.card K ^ δ) = AdjoinRoot.root g := by
    rw [hc, pow_mul, ← hcard]
    exact FiniteField.pow_card_pow c _
  rw [← AdjoinRoot.mk_eq_zero, frobPoly, map_sub, map_pow, AdjoinRoot.mk_X, hroot, sub_self]

/-- ★ **The divisibility criterion**: for monic irreducible `g`,
`g ∣ X^(q^δ) − X ↔ deg g ∣ δ`.  Hard direction = mathlib's
`Irreducible.natDegree_dvd_of_dvd_X_pow_card_pow_sub_X`. -/
theorem irred_dvd_frobPoly_iff {g : Polynomial K} (hgm : g.Monic) (hgi : Irreducible g)
    (δ : ℕ) : g ∣ frobPoly K δ ↔ g.natDegree ∣ δ := by
  constructor
  · intro h
    refine hgi.natDegree_dvd_of_dvd_X_pow_card_pow_sub_X (n := δ) ?_
    rwa [Nat.card_eq_fintype_card, ← frobPoly]
  · exact dvd_frobPoly_of_natDegree_dvd hgm hgi

/-- ★ **The degree-sum identity** (Gauss): `Σ_{d ∣ δ} d · #(irredFinset K d) = q^δ`, for
every `δ ≥ 1` and every finite field.  Reading `natDegree` off the squarefree
factorization of `Φ_δ`. -/
theorem sum_divisors_mul_card_irredFinset (δ : ℕ) (hδ : 1 ≤ δ) :
    ∑ d ∈ δ.divisors, d * (irredFinset K d).card = Fintype.card K ^ δ := by
  classical
  have hmonic : (frobPoly K δ).Monic := monic_frobPoly δ hδ
  have hne : frobPoly K δ ≠ 0 := hmonic.ne_zero
  have hnodup : (normalizedFactors (frobPoly K δ)).Nodup :=
    (squarefree_iff_nodup_normalizedFactors hne).mp (squarefree_frobPoly δ hδ)
  -- every normalized factor is monic
  have hfmonic : ∀ p ∈ normalizedFactors (frobPoly K δ), p.Monic := by
    intro p hp
    obtain ⟨hirr, hnorm, -⟩ := (mem_normalizedFactors_iff' hne).mp hp
    rw [← hnorm]
    exact monic_normalize hirr.ne_zero
  -- the product reading: `Φ_δ` IS the product of its normalized factors (both monic)
  have hprod : (normalizedFactors (frobPoly K δ)).prod = frobPoly K δ := by
    refine Polynomial.eq_of_monic_of_associated ?_ hmonic (prod_normalizedFactors hne)
    have := Polynomial.monic_multiset_prod_of_monic
      (normalizedFactors (frobPoly K δ)) id (fun p hp => hfmonic p hp)
    simpa using this
  -- the degree reading: `q^δ` is the sum of the factor degrees
  have hdegsum : ((normalizedFactors (frobPoly K δ)).map natDegree).sum
      = Fintype.card K ^ δ := by
    rw [← Polynomial.natDegree_multiset_prod _
      (fun h0 => (hfmonic 0 h0).ne_zero rfl), hprod, natDegree_frobPoly δ hδ]
  -- the factors as a `Finset`
  set t : Finset (Polynomial K) := ⟨normalizedFactors (frobPoly K δ), hnodup⟩ with ht
  have hmem : ∀ {p : Polynomial K}, p ∈ t ↔ p.Monic ∧ Irreducible p ∧ p.natDegree ∣ δ := by
    intro p
    rw [ht, Finset.mem_mk]
    constructor
    · intro hp
      obtain ⟨hirr, hnorm, hdvd⟩ := (mem_normalizedFactors_iff' hne).mp hp
      have hpm : p.Monic := by rw [← hnorm]; exact monic_normalize hirr.ne_zero
      exact ⟨hpm, hirr, (irred_dvd_frobPoly_iff hpm hirr δ).mp hdvd⟩
    · rintro ⟨hpm, hirr, hdvd⟩
      exact (mem_normalizedFactors_iff' hne).mpr
        ⟨hirr, hpm.normalize_eq_self, dvd_frobPoly_of_natDegree_dvd hpm hirr hdvd⟩
  -- the total degree over `t`
  have htsum : ∑ p ∈ t, p.natDegree = Fintype.card K ^ δ := by
    rw [Finset.sum_eq_multiset_sum]
    exact hdegsum
  -- the degree fibers of `t` are exactly the `irredFinset`s
  have hfilter : ∀ d ∈ δ.divisors,
      t.filter (fun p => p.natDegree = d) = irredFinset K d := by
    intro d hd
    ext p
    rw [Finset.mem_filter, mem_irredFinset_iff]
    constructor
    · rintro ⟨hp, hdeg⟩
      obtain ⟨hpm, hirr, -⟩ := hmem.mp hp
      exact ⟨hpm, hdeg, hirr⟩
    · rintro ⟨hpm, hdeg, hirr⟩
      refine ⟨hmem.mpr ⟨hpm, hirr, ?_⟩, hdeg⟩
      rw [hdeg]
      exact (Nat.mem_divisors.mp hd).1
  -- regroup the degree sum by fibers over the divisors
  have hmaps : ∀ p ∈ t, p.natDegree ∈ δ.divisors := by
    intro p hp
    rw [Nat.mem_divisors]
    exact ⟨(hmem.mp hp).2.2, by omega⟩
  calc ∑ d ∈ δ.divisors, d * (irredFinset K d).card
      = ∑ d ∈ δ.divisors, ∑ p ∈ t.filter (fun p => p.natDegree = d), p.natDegree := by
        refine Finset.sum_congr rfl fun d hd => ?_
        rw [hfilter d hd,
          Finset.sum_congr rfl (fun p hp => (mem_irredFinset_iff.mp hp).2.1),
          Finset.sum_const, smul_eq_mul, mul_comm]
    _ = ∑ p ∈ t, p.natDegree := Finset.sum_fiberwise_of_maps_to hmaps _
    _ = Fintype.card K ^ δ := htsum

/-- IFCG4's carrier and IFCG17's `Finset` count the same set. -/
theorem natCard_irredOfDeg_eq_card_irredFinset (d : ℕ) :
    Nat.card (IFCG4.IrredOfDeg K d) = (irredFinset K d).card := by
  rw [← Nat.card_eq_finsetCard]
  exact Nat.card_congr
    ⟨fun f => ⟨f.1, mem_irredFinset_iff.mpr f.2⟩,
     fun p => ⟨p.1, mem_irredFinset_iff.mp p.2⟩, fun _ => rfl, fun _ => rfl⟩

/-- ★ **The degree-sum identity in IFCG4's interface**:
`Σ_{d ∣ δ} d · Nat.card (IrredOfDeg K d) = q^δ`. -/
theorem sum_divisors_mul_natCard_irred (δ : ℕ) (hδ : 1 ≤ δ) :
    ∑ d ∈ δ.divisors, d * Nat.card (IFCG4.IrredOfDeg K d) = Fintype.card K ^ δ := by
  rw [← sum_divisors_mul_card_irredFinset δ hδ]
  exact Finset.sum_congr rfl fun d _ => by rw [natCard_irredOfDeg_eq_card_irredFinset]

/-- ★★ **The closed necklace form** (Möbius inversion of the degree-sum identity):
`δ · N_δ = Σ_{(a,b) : ab = δ} μ(a) · q^b`, in `ℤ`, for every `δ ≥ 1` and every finite
field. -/
theorem mul_natCard_irred_eq_moebius_sum (δ : ℕ) (hδ : 1 ≤ δ) :
    (δ : ℤ) * (Nat.card (IFCG4.IrredOfDeg K δ) : ℤ)
      = ∑ x ∈ δ.divisorsAntidiagonal,
          (ArithmeticFunction.moebius x.1 : ℤ) * (Fintype.card K : ℤ) ^ x.2 := by
  have key := (ArithmeticFunction.sum_eq_iff_sum_smul_moebius_eq (R := ℤ)
      (f := fun n => (n : ℤ) * (Nat.card (IFCG4.IrredOfDeg K n) : ℤ))
      (g := fun n => (Fintype.card K : ℤ) ^ n)).mp ?_ δ (by omega)
  · rw [← key]
    refine Finset.sum_congr rfl fun x hx => ?_
    rw [zsmul_eq_mul, Int.cast_id]
  · intro n hn
    have h := sum_divisors_mul_natCard_irred (K := K) n hn
    exact_mod_cast congrArg (Nat.cast : ℕ → ℤ) h

end Census

/-! ## §2 — the necklace polynomial (the `URLim`-facing `ℚ[X]` packaging) -/

/-- **The necklace polynomial** `(1/δ) Σ_{(a,b) : ab = δ} μ(a) X^b ∈ ℚ[X]`: the ONE
rational-coefficient polynomial whose value at `q` is `N_δ(q)`, uniformly in the finite
field. -/
def necklacePoly (δ : ℕ) : Polynomial ℚ :=
  Polynomial.C ((δ : ℚ)⁻¹) *
    ∑ x ∈ δ.divisorsAntidiagonal,
      Polynomial.C ((ArithmeticFunction.moebius x.1 : ℤ) : ℚ) * Polynomial.X ^ x.2

/-- ★★ **The uniform census, evaluated**: `necklacePoly δ` at `q = #K` IS the monic
irreducible count `N_δ` — for every finite field `K`, every `δ ≥ 1`. -/
theorem necklacePoly_eval_card (K : Type*) [Field K] [Fintype K] (δ : ℕ) (hδ : 1 ≤ δ) :
    (necklacePoly δ).eval ((Fintype.card K : ℚ))
      = (Nat.card (IFCG4.IrredOfDeg K δ) : ℚ) := by
  have hδQ : (δ : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have keyQ : (δ : ℚ) * (Nat.card (IFCG4.IrredOfDeg K δ) : ℚ)
      = ∑ x ∈ δ.divisorsAntidiagonal,
          ((ArithmeticFunction.moebius x.1 : ℤ) : ℚ) * (Fintype.card K : ℚ) ^ x.2 := by
    exact_mod_cast congrArg (Int.cast : ℤ → ℚ)
      (mul_natCard_irred_eq_moebius_sum (K := K) δ hδ)
  rw [necklacePoly, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_finsetSum]
  simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  rw [← keyQ, inv_mul_cancel_left₀ hδQ]

/-! ## §3 — the monomial reading of an irreducible stratum (H124 × H124b) -/

section Monomial

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [IsAdicComplete (maximalIdeal O) O] [Finite (ResidueField O)]

/-- **The inert cell of an irreducible stratum is the whole stratum**: over an irreducible
residue polynomial the stratum is decided at `⟨{(1, δ)}⟩` (H124, degree-uniform), so the
`⟨{(1, δ)}⟩`-refined count is the stratum census `q^(δ(N−1))` (H124b). -/
theorem stratDecCount_irreducible_inert {δ N : ℕ} (hδ : 0 < δ) (hN : 1 ≤ N)
    {p : Polynomial (ResidueField O)} (hpm : p.Monic) (hpd : p.natDegree = δ)
    (hpi : Irreducible p) :
    stratDecCount O δ ⟨{(1, δ)}⟩ N p = residueCard O ^ (δ * (N - 1)) := by
  have hsub : levelZeroStratum O δ N p ⊆ decidedSet O δ ⟨{(1, δ)}⟩ N := by
    intro c hc
    exact decidedAt_of_mem_levelZeroStratum_irreducible hδ hpi hc
  rw [stratDecCount, Set.inter_eq_right.mpr hsub]
  exact card_levelZeroStratum hN hpm hpd

/-- **Every non-inert cell of an irreducible stratum is empty** (`decidedAt_unique`
against H124's decidedness). -/
theorem stratDecCount_irreducible_ne {δ N : ℕ} (hδ : 0 < δ)
    {p : Polynomial (ResidueField O)}
    (hpi : Irreducible p) {σ : FactorizationType} (hσ : σ ≠ ⟨{(1, δ)}⟩) :
    stratDecCount O δ σ N p = 0 := by
  have hempty : (decidedSet O δ σ N ∩ levelZeroStratum O δ N p : Set (Coeff O δ N)) = ∅ := by
    ext c
    simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false, not_and]
    intro hcdec hcs
    exact hσ (decidedAt_unique hcdec
      (decidedAt_of_mem_levelZeroStratum_irreducible hδ hpi hcs))
  rw [stratDecCount, hempty]
  simp

/-- ★ **The monomial lemma**: over an irreducible residue polynomial of degree `δ` the
type-indexed census is the single monomial `single {(1, δ)} q^(δ(N−1))`. -/
theorem stratPoly_irreducible {δ N : ℕ} (hδ : 0 < δ) (hN : 1 ≤ N)
    {p : Polynomial (ResidueField O)} (hpm : p.Monic) (hpd : p.natDegree = δ)
    (hpi : Irreducible p) :
    stratPoly O δ N p
      = AddMonoidAlgebra.single {(1, δ)} ((residueCard O ^ (δ * (N - 1)) : ℕ) : ℚ) := by
  refine AddMonoidAlgebra.ext fun t => ?_
  rw [stratPoly_apply, AddMonoidAlgebra.single_apply]
  by_cases ht : ({(1, δ)} : Multiset (ℕ × ℕ)) = t
  · rw [if_pos ht, ← ht]
    exact_mod_cast stratDecCount_irreducible_inert hδ hN hpm hpd hpi
  · rw [if_neg ht,
      stratDecCount_irreducible_ne hδ hpi
        (fun hcon => ht (congrArg FactorizationType.data hcon).symm),
      Nat.cast_zero]

end Monomial

/-! ## §4 — ★ the e = 1 consumption: the `E = [1]` clause of the single-point kernel -/

section Consumption

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [IsAdicComplete (maximalIdeal O) O] [Finite (ResidueField O)]

/-- Pointwise evaluation of `TypeAlg` natural scalar multiples (IFCG18 §0's private
helper, re-proved). -/
private theorem typeAlg_nsmul_apply (n : ℕ) (X : TypeAlg) (t : Multiset (ℕ × ℕ)) :
    (n • X) t = (n : ℚ) * X t := by
  induction n with
  | zero =>
      rw [zero_smul, Nat.cast_zero, zero_mul]
      rfl
  | succ k ih =>
      rw [succ_nsmul]
      have happ : ((k • X + X : TypeAlg)) t = (k • X) t + X t := rfl
      rw [happ, ih, Nat.cast_succ]
      ring

/-- **The single-point aggregate of a unit block, exactly**: summing the monomial lemma
over the degree-`δ` irreducible census. -/
theorem SPAgg_unit_block [Fintype (ResidueField O)] {δ N : ℕ} (hδ : 0 < δ) (hN : 1 ≤ N) :
    SPAgg O N ⟨δ, [1]⟩ ∅
      = AddMonoidAlgebra.single {(1, δ)}
          (((irredFinset (ResidueField O) δ).card * residueCard O ^ (δ * (N - 1)) : ℕ) : ℚ) := by
  have hterm : ∀ p ∈ irredFinset (ResidueField O) δ,
      blockPoly O N δ p [1]
        = AddMonoidAlgebra.single {(1, δ)} ((residueCard O ^ (δ * (N - 1)) : ℕ) : ℚ) := by
    intro p hp
    obtain ⟨hpm, hpd, hpi⟩ := mem_irredFinset_iff.mp hp
    have h := blockPoly_singleton (O := O) N δ p 1
    rw [mul_one, pow_one] at h
    rw [h]
    exact stratPoly_irreducible hδ hN hpm hpd hpi
  have hagg : SPAgg O N ⟨δ, [1]⟩ ∅
      = ∑ p ∈ irredFinset (ResidueField O) δ, blockPoly O N δ p [1] := by
    rw [SPAgg, Finset.sdiff_empty]
  rw [hagg, Finset.sum_congr rfl hterm, Finset.sum_const]
  refine AddMonoidAlgebra.ext fun t => ?_
  rw [typeAlg_nsmul_apply, AddMonoidAlgebra.single_apply, AddMonoidAlgebra.single_apply]
  by_cases ht : ({(1, δ)} : Multiset (ℕ × ℕ)) = t
  · rw [if_pos ht, if_pos ht]
    push_cast
    ring
  · rw [if_neg ht, if_neg ht, mul_zero]

/-- ★★ **THE e = 1 CLAUSE CLOSES — unconditionally, all `δ ≥ 1`, every coefficient.**
The normalized unit-block family is constant `N_δ(q)/q^δ` at the inert coefficient
(`0` elsewhere) for `N ≥ 1`, hence a `URLim` family with numerator `necklacePoly δ` and
denominator `X^δ`.  No decided-value-law hypotheses, no unramified base-change leg. -/
theorem spFamily_URLim_unit (b : SBlock) (hδ : 1 ≤ b.δ) (hE : b.E = [1])
    (s : Multiset (ℕ × ℕ)) : URLim (spFamily b s) := by
  obtain ⟨δ, E⟩ := b
  replace hδ : 1 ≤ δ := hδ
  replace hE : E = [1] := hE
  subst hE
  have hmass : (⟨δ, [1]⟩ : SBlock).mass = δ := by simp [SBlock.mass]
  by_cases hs : s = {(1, δ)}
  · -- the inert coefficient: the family is constant `N_δ(q)/q^δ` for `N ≥ 1`
    subst hs
    refine ⟨necklacePoly δ, Polynomial.X ^ δ, pow_ne_zero δ Polynomial.X_ne_zero, ?_⟩
    intro O _ _ _ _ _
    letI : Fintype (ResidueField O) := Fintype.ofFinite (ResidueField O)
    have hq2 : 2 ≤ residueCard O := two_le_residueCard (O := O)
    have hqQ : ((residueCard O : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    have hqR : ((residueCard O : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    have hden : (Polynomial.X ^ δ : Polynomial ℚ).eval ((residueCard O : ℕ) : ℚ) ≠ 0 := by
      rw [Polynomial.eval_pow, Polynomial.eval_X]
      exact pow_ne_zero δ hqQ
    refine ⟨hden, ?_⟩
    -- the census value at this residue field
    have hqcard : residueCard O = Fintype.card (ResidueField O) := Nat.card_eq_fintype_card
    have hnum : (necklacePoly δ).eval ((residueCard O : ℕ) : ℚ)
        = ((irredFinset (ResidueField O) δ).card : ℚ) := by
      rw [hqcard, necklacePoly_eval_card (ResidueField O) δ hδ,
        natCard_irredOfDeg_eq_card_irredFinset]
    have hlim : ((necklacePoly δ).eval ((residueCard O : ℕ) : ℚ)
          / (Polynomial.X ^ δ : Polynomial ℚ).eval ((residueCard O : ℕ) : ℚ) : ℚ)
        = ((irredFinset (ResidueField O) δ).card : ℚ) / ((residueCard O : ℕ) : ℚ) ^ δ := by
      rw [hnum, Polynomial.eval_pow, Polynomial.eval_X]
    rw [hlim]
    refine Filter.Tendsto.congr' ?_ tendsto_const_nhds
    filter_upwards [Filter.eventually_ge_atTop 1] with N hN
    unfold spFamily
    rw [SPAgg_unit_block (O := O) hδ hN, AddMonoidAlgebra.single_apply, if_pos rfl, hmass]
    have hexp : δ * N = δ * (N - 1) + δ := by
      calc δ * N = δ * ((N - 1) + 1) := by rw [Nat.sub_add_cancel hN]
        _ = δ * (N - 1) + δ := by ring
    rw [hexp, pow_add]
    push_cast
    rw [div_eq_div_iff (pow_ne_zero δ hqR)
      (mul_ne_zero (pow_ne_zero _ hqR) (pow_ne_zero δ hqR))]
    ring
  · -- every other coefficient: the family vanishes for `N ≥ 1`
    refine ⟨0, 1, one_ne_zero, ?_⟩
    intro O _ _ _ _ _
    letI : Fintype (ResidueField O) := Fintype.ofFinite (ResidueField O)
    refine ⟨by simp, ?_⟩
    have hzero : (((0 : Polynomial ℚ).eval ((residueCard O : ℕ) : ℚ)
        / (1 : Polynomial ℚ).eval ((residueCard O : ℕ) : ℚ) : ℚ) : ℝ) = 0 := by simp
    rw [hzero]
    refine Filter.Tendsto.congr' ?_ tendsto_const_nhds
    filter_upwards [Filter.eventually_ge_atTop 1] with N hN
    unfold spFamily
    rw [SPAgg_unit_block (O := O) hδ hN, AddMonoidAlgebra.single_apply,
      if_neg (fun hcon => hs hcon.symm), Rat.cast_zero, zero_div]

/-- **The clause, in `SinglePointAggregateLaw`'s exact quantifier shape** (the smaller
value laws and the mass window are accepted and unused — the clause is unconditional). -/
theorem singlePoint_law_unit_clause :
    ∀ m : ℕ, 4 ≤ m →
      (∀ k, k < m → ∀ σ' : FactorizationType, σ'.degree = k → DecidedValueLaw k σ') →
      ∀ b : SBlock, 1 ≤ b.δ → b.E = [1] → b.mass ≤ m → ¬(b.δ = 1 ∧ b.E = [m]) →
        ∀ s : Multiset (ℕ × ℕ), URLim (spFamily b s) :=
  fun _ _ _ b hδ hE _ _ s => spFamily_URLim_unit b hδ hE s

/-! ### The all-ones extension: blocks `E = List.replicate k 1`

These are the shapes IFCG18's collision peel produces when unit blocks of equal degree
merge (`E₁ ++ E₂` with all entries `1`), so the whole all-exponents-one sector of the
kernel closes, not just the singleton lists. -/

/-- **The single-point aggregate of an all-ones block, exactly**: the `k`-th power of the
monomial lemma, summed over the census.  The label is `k` copies of the inert pair. -/
theorem SPAgg_ones_block [Fintype (ResidueField O)] {δ k N : ℕ} (hδ : 0 < δ) (hN : 1 ≤ N) :
    SPAgg O N ⟨δ, List.replicate k 1⟩ ∅
      = AddMonoidAlgebra.single (k • ({(1, δ)} : Multiset (ℕ × ℕ)))
          (((irredFinset (ResidueField O) δ).card
              * (residueCard O ^ (δ * (N - 1))) ^ k : ℕ) : ℚ) := by
  have hterm : ∀ p ∈ irredFinset (ResidueField O) δ,
      blockPoly O N δ p (List.replicate k 1)
        = AddMonoidAlgebra.single (k • ({(1, δ)} : Multiset (ℕ × ℕ)))
            (((residueCard O ^ (δ * (N - 1)) : ℕ) : ℚ) ^ k) := by
    intro p hp
    obtain ⟨hpm, hpd, hpi⟩ := mem_irredFinset_iff.mp hp
    have hb : blockPoly O N δ p (List.replicate k 1) = (stratPoly O δ N p) ^ k := by
      simp only [blockPoly, List.map_replicate, List.prod_replicate, mul_one, pow_one]
    rw [hb, stratPoly_irreducible hδ hN hpm hpd hpi, AddMonoidAlgebra.single_pow]
  have hagg : SPAgg O N ⟨δ, List.replicate k 1⟩ ∅
      = ∑ p ∈ irredFinset (ResidueField O) δ, blockPoly O N δ p (List.replicate k 1) := by
    rw [SPAgg, Finset.sdiff_empty]
  rw [hagg, Finset.sum_congr rfl hterm, Finset.sum_const]
  refine AddMonoidAlgebra.ext fun t => ?_
  rw [typeAlg_nsmul_apply, AddMonoidAlgebra.single_apply, AddMonoidAlgebra.single_apply]
  by_cases ht : k • ({(1, δ)} : Multiset (ℕ × ℕ)) = t
  · rw [if_pos ht, if_pos ht]
    push_cast
    ring
  · rw [if_neg ht, if_neg ht, mul_zero]

/-- ★★ **The all-ones sector of the single-point kernel closes** — for every block
`⟨δ, List.replicate k 1⟩` with `δ, k ≥ 1` the normalized aggregate family is the constant
`N_δ(q)/q^(δk)` at the `k`-fold inert coefficient (`0` elsewhere) for `N ≥ 1`: a `URLim`
family with numerator `necklacePoly δ` and denominator `X^(δk)`. -/
theorem spFamily_URLim_ones (b : SBlock) (hδ : 1 ≤ b.δ) {k : ℕ}
    (hE : b.E = List.replicate k 1) (s : Multiset (ℕ × ℕ)) : URLim (spFamily b s) := by
  obtain ⟨δ, E⟩ := b
  replace hδ : 1 ≤ δ := hδ
  replace hE : E = List.replicate k 1 := hE
  subst hE
  have hmass : (⟨δ, List.replicate k 1⟩ : SBlock).mass = δ * k := by
    simp [SBlock.mass]
  by_cases hs : s = k • ({(1, δ)} : Multiset (ℕ × ℕ))
  · subst hs
    refine ⟨necklacePoly δ, Polynomial.X ^ (δ * k), pow_ne_zero _ Polynomial.X_ne_zero, ?_⟩
    intro O _ _ _ _ _
    letI : Fintype (ResidueField O) := Fintype.ofFinite (ResidueField O)
    have hq2 : 2 ≤ residueCard O := two_le_residueCard (O := O)
    have hqQ : ((residueCard O : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    have hqR : ((residueCard O : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    have hden : (Polynomial.X ^ (δ * k) : Polynomial ℚ).eval ((residueCard O : ℕ) : ℚ) ≠ 0 := by
      rw [Polynomial.eval_pow, Polynomial.eval_X]
      exact pow_ne_zero _ hqQ
    refine ⟨hden, ?_⟩
    have hqcard : residueCard O = Fintype.card (ResidueField O) := Nat.card_eq_fintype_card
    have hnum : (necklacePoly δ).eval ((residueCard O : ℕ) : ℚ)
        = ((irredFinset (ResidueField O) δ).card : ℚ) := by
      rw [hqcard, necklacePoly_eval_card (ResidueField O) δ hδ,
        natCard_irredOfDeg_eq_card_irredFinset]
    have hlim : ((necklacePoly δ).eval ((residueCard O : ℕ) : ℚ)
          / (Polynomial.X ^ (δ * k) : Polynomial ℚ).eval ((residueCard O : ℕ) : ℚ) : ℚ)
        = ((irredFinset (ResidueField O) δ).card : ℚ)
            / ((residueCard O : ℕ) : ℚ) ^ (δ * k) := by
      rw [hnum, Polynomial.eval_pow, Polynomial.eval_X]
    rw [hlim]
    refine Filter.Tendsto.congr' ?_ tendsto_const_nhds
    filter_upwards [Filter.eventually_ge_atTop 1] with N hN
    unfold spFamily
    rw [SPAgg_ones_block (O := O) hδ hN, AddMonoidAlgebra.single_apply, if_pos rfl, hmass]
    have hexp : δ * k * N = k * (δ * (N - 1)) + δ * k := by
      calc δ * k * N = δ * k * ((N - 1) + 1) := by rw [Nat.sub_add_cancel hN]
        _ = k * (δ * (N - 1)) + δ * k := by ring
    rw [hexp, pow_add]
    push_cast
    rw [div_eq_div_iff (pow_ne_zero _ hqR)
      (mul_ne_zero (pow_ne_zero _ hqR) (pow_ne_zero _ hqR))]
    ring
  · refine ⟨0, 1, one_ne_zero, ?_⟩
    intro O _ _ _ _ _
    letI : Fintype (ResidueField O) := Fintype.ofFinite (ResidueField O)
    refine ⟨by simp, ?_⟩
    have hzero : (((0 : Polynomial ℚ).eval ((residueCard O : ℕ) : ℚ)
        / (1 : Polynomial ℚ).eval ((residueCard O : ℕ) : ℚ) : ℚ) : ℝ) = 0 := by simp
    rw [hzero]
    refine Filter.Tendsto.congr' ?_ tendsto_const_nhds
    filter_upwards [Filter.eventually_ge_atTop 1] with N hN
    unfold spFamily
    rw [SPAgg_ones_block (O := O) hδ hN, AddMonoidAlgebra.single_apply,
      if_neg (fun hcon => hs hcon.symm), Rat.cast_zero, zero_div]

/-- **The all-ones clause, in `SinglePointAggregateLaw`'s exact binder shape**: any block
whose exponent list is nonempty with EVERY entry `= 1` (such a list IS
`List.replicate length 1`).  The mass window, the smaller value laws, and the deep-linear
exclusion are accepted and unused — this sector is unconditional. -/
theorem singlePoint_law_ones_clause :
    ∀ m : ℕ, 4 ≤ m →
      (∀ k, k < m → ∀ σ' : FactorizationType, σ'.degree = k → DecidedValueLaw k σ') →
      ∀ b : SBlock, 1 ≤ b.δ → b.E ≠ [] → (∀ e ∈ b.E, e = 1) → b.mass ≤ m →
        ¬(b.δ = 1 ∧ b.E = [m]) →
        ∀ s : Multiset (ℕ × ℕ), URLim (spFamily b s) := by
  intro m _ _ b hδ _hne hones _ _ s
  exact spFamily_URLim_ones b hδ (List.eq_replicate_of_mem hones) s

end Consumption

end Uniformity.Density.IFCG19

end

/-! ## AxCheck footer — Lean core only (`propext`, `Classical.choice`, `Quot.sound`) -/

section AxCheck

#print axioms Uniformity.Density.IFCG19.monic_frobPoly
#print axioms Uniformity.Density.IFCG19.natDegree_frobPoly
#print axioms Uniformity.Density.IFCG19.frobPoly_ne_zero
#print axioms Uniformity.Density.IFCG19.squarefree_frobPoly
#print axioms Uniformity.Density.IFCG19.dvd_frobPoly_of_natDegree_dvd
#print axioms Uniformity.Density.IFCG19.irred_dvd_frobPoly_iff
#print axioms Uniformity.Density.IFCG19.sum_divisors_mul_card_irredFinset
#print axioms Uniformity.Density.IFCG19.natCard_irredOfDeg_eq_card_irredFinset
#print axioms Uniformity.Density.IFCG19.sum_divisors_mul_natCard_irred
#print axioms Uniformity.Density.IFCG19.mul_natCard_irred_eq_moebius_sum
#print axioms Uniformity.Density.IFCG19.necklacePoly_eval_card
#print axioms Uniformity.Density.IFCG19.stratDecCount_irreducible_inert
#print axioms Uniformity.Density.IFCG19.stratDecCount_irreducible_ne
#print axioms Uniformity.Density.IFCG19.stratPoly_irreducible
#print axioms Uniformity.Density.IFCG19.SPAgg_unit_block
#print axioms Uniformity.Density.IFCG19.spFamily_URLim_unit
#print axioms Uniformity.Density.IFCG19.singlePoint_law_unit_clause
#print axioms Uniformity.Density.IFCG19.SPAgg_ones_block
#print axioms Uniformity.Density.IFCG19.spFamily_URLim_ones
#print axioms Uniformity.Density.IFCG19.singlePoint_law_ones_clause

end AxCheck
