/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapH.H124
import Uniformity.ChapH.H63
import Uniformity.ChapH.H66

/-!
# Uniformity.ChapH.H124b — H.124b: the peel step

**Chapter H, NODE H.124** [def+theorem] (`blueprint/CHAP-H_general_induction.md` §17.3 — the T-1
completion layer, dated extension 2026-08-16).  **PART b of the mandated three-way split**
(`H124` / `H124b` / `H124c`): the machinery of the blueprint's PROOF step 3, packaged so that
H.124c is a pure bookkeeping assembly.

* the **stratum census** `card_levelZeroStratum` — a level-`M` stratum over a monic residue
  polynomial of degree `n` has exactly `q ^ (n (M − 1))` classes.  This is the value H.100's
  module note explicitly did NOT claim; it is what converts a GLOBAL undecided count (all the
  induction hypothesis `InductionPackage k` offers) into a PER-STRATUM ratio;
* the **peel step** `card_undecided_le_of_coprime` — H.105's exact composition run through H.63's
  union bound at two factors: per-stratum undecided RATIOS ADD across a coprime split;
* the **factorization dichotomy** `monic_prime_pow_or_coprime_split` — every monic residue
  polynomial of degree `≥ 1` is either a prime power `p ^ m` (the base of step 3) or a coprime
  product of two monic factors of strictly smaller positive degree (the peel);
* the **constant bookkeeping** `rate_const_le` (H.66's `RateSpecies.mono`, scalarised) and
  `stratum_le_of_global` — the induction-hypothesis import, which pays for the normalisation
  mismatch (`q ^ (i M)` against `q ^ (i (M − 1))`) by inflating the exponent offset `c ↦ c + i`.

## ⚠ WHAT THIS NODE IS NOT (the H.98 fence, restated)

Nothing here claims `THEOREM GENIND.B`.  Every statement in this file is unconditional
bookkeeping about strata and counts; the full-cluster rate `FullClusterRateBound` (H.124a) is
never proved, only consumed as a hypothesis at H.124c.

## The peel, in words

Fix a monic residue polynomial `g` of degree `i` and a window `M ≥ 1`.  Write
`u(g) = #(undecided ∩ stratum g)` and `T(g) = #(stratum g)`.

* If `g = g₁ · g₂` with `g₁, g₂` monic coprime of positive degrees, H.102 gives `T(g) = T(g₁)T(g₂)`
  and H.105 gives `u(g) = T(g₁)T(g₂) − (T(g₁) − u(g₁))(T(g₂) − u(g₂))`; H.63's union bound at two
  factors turns the right-hand side into `u(g₁)T(g₂) + T(g₁)u(g₂)`, i.e. the RATIOS `u/T` ADD.
* If `g = p ^ m` with `p` irreducible then either `m = 1` — `u(g) = 0` by H.124a's one-factor base
  — or `m ≥ 2`, and the stratum is a FULL-CLUSTER stratum, exactly the shape
  `FullClusterRateBound` (at the top degree) and the induction hypothesis (below it) speak about.

DEPENDS: H.124a (`FullClusterRateBound`, the one-factor base) · H.100 (`levelZeroStratum`) ·
H.102 (`card_levelZeroStratum_mul`) · H.105 (`card_undecided_mulClass`) · H.63
(`prod_sub_prod_le_sum`) · H.66 (`RateSpecies.mono`) · landed `card_coeff`,
`card_preimage_coeffFactor`, `coeffFactor`, `residueCard`, `two_le_residueCard`, `undecidedSeq`.

## Status

Sorry-free, axiom-free (Lean core only); footprints printed at the end of the file.
-/

set_option linter.style.longLine false

namespace Uniformity.Density.Induction

open IsLocalRing Polynomial

/-! ## 1. The level-1 reading of a class -/

/-- Two coefficient vectors have the same level-`1` class exactly when they have the same
residues.  (`←` is the content: `𝔪 ^ 1 = 𝔪`.) -/
theorem proj_one_eq_iff {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {n : ℕ} (a b : Fin n → O) :
    proj O n 1 a = proj O n 1 b ↔ ∀ i, residue O (a i) = residue O (b i) := by
  constructor
  · intro h i
    exact residue_eq_of_proj_eq le_rfl h i
  · intro h
    funext i
    change Ideal.Quotient.mk ((maximalIdeal O) ^ 1) (a i) = Ideal.Quotient.mk _ (b i)
    refine Ideal.Quotient.eq.2 ?_
    rw [pow_one]
    exact Ideal.Quotient.eq.1 (h i)

/-! ## 2. The stratum census -/

/-- **The stratum census.**  At `1 ≤ M` the level-`0` stratum of a monic degree-`n` residue
polynomial has exactly `q ^ (n (M − 1))` classes: it is a single fibre of the level-`1`
truncation `Coeff O n M → Coeff O n 1`, and that map is a surjective homomorphism of finite
abelian groups.  (H.100's module note flags this value as *not* claimed there; it is claimed
here, and it is what lets the induction hypothesis' GLOBAL count be read per stratum.) -/
theorem card_levelZeroStratum {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Finite (ResidueField O)] {n M : ℕ} (hM : 1 ≤ M) {g : Polynomial (ResidueField O)}
    (hg : g.Monic) (hd : g.natDegree = n) :
    Nat.card (levelZeroStratum O n M g) = residueCard O ^ (n * (M - 1)) := by
  classical
  obtain ⟨b, hb⟩ := exists_monicPoly_eq hg hd
  choose β hβ using fun i : Fin n => IsLocalRing.residue_surjective (R := O) (b i)
  -- the stratum is the fibre of the level-`1` truncation over the class of `β`
  have hset : levelZeroStratum O n M g = (coeffFactor (O := O) n hM) ⁻¹' {proj O n 1 β} := by
    ext c
    constructor
    · intro hc
      obtain ⟨a, ha, hga⟩ := (mem_levelZeroStratum_iff hM g c).1 hc
      have hres : ∀ i : Fin n, residue O (a i) = residue O (β i) := by
        intro i
        have h1 : monicPoly (fun j => residue O (a j)) = monicPoly b := by
          rw [← map_monicPoly, hga, ← hb]
        have h2 := congrArg (fun P => Polynomial.coeff P (i : ℕ)) h1
        simp only [monicPoly_coeff_lt _ i.isLt] at h2
        rw [h2, hβ i]
      change coeffFactor (O := O) n hM c ∈ ({proj O n 1 β} : Set (Coeff O n 1))
      simp only [Set.mem_singleton_iff]
      rw [← ha, coeffFactor_proj]
      exact (proj_one_eq_iff a β).2 hres
    · intro hc
      have hc' : coeffFactor (O := O) n hM c = proj O n 1 β := hc
      obtain ⟨a, ha⟩ := proj_surjective' O n M c
      have hres : ∀ i : Fin n, residue O (a i) = residue O (β i) := by
        refine (proj_one_eq_iff a β).1 ?_
        rw [← coeffFactor_proj (O := O) n hM a, ha, hc']
      refine (mem_levelZeroStratum_iff hM g c).2 ⟨a, ha, ?_⟩
      rw [map_monicPoly, ← hb]
      exact congrArg monicPoly (funext fun i => by rw [hres i, hβ i])
  -- fibre counting
  obtain ⟨M', rfl⟩ : ∃ M', M = M' + 1 := ⟨M - 1, by omega⟩
  have hcard := card_preimage_coeffFactor (O := O) n hM ({proj O n 1 β} : Set (Coeff O n 1))
  rw [card_coeff, card_coeff] at hcard
  have hone : Nat.card ({proj O n 1 β} : Set (Coeff O n 1)) = 1 := by simp
  rw [hone, one_mul, mul_one] at hcard
  rw [hset]
  have hsplit : residueCard O ^ (n * (M' + 1)) = residueCard O ^ (n * (M' + 1 - 1)) * residueCard O ^ n := by
    rw [← pow_add]
    congr 1
  rw [hsplit] at hcard
  exact Nat.eq_of_mul_eq_mul_right (pow_pos (residueCard_pos O) n) hcard

/-! ## 3. The union bound at two factors (H.63, instantiated) -/

/-- **H.63 at `r = 2`.**  The composed undecided mass of a two-factor split is at most the
first-order sum. -/
theorem union_bound_two {u₁ u₂ T₁ T₂ : ℝ} (hu₁ : 0 ≤ u₁) (hu₂ : 0 ≤ u₂)
    (h₁ : u₁ ≤ T₁) (h₂ : u₂ ≤ T₂) :
    T₁ * T₂ - (T₁ - u₁) * (T₂ - u₂) ≤ u₁ * T₂ + T₁ * u₂ := by
  classical
  have h := prod_sub_prod_le_sum (Finset.univ : Finset (Fin 2)) ![u₁, u₂] ![T₁, T₂]
    (by intro i _; fin_cases i <;> simpa) (by intro i _; fin_cases i <;> simpa)
  have e0 : (Finset.univ : Finset (Fin 2)).erase 0 = {1} := by decide
  have e1 : (Finset.univ : Finset (Fin 2)).erase 1 = {0} := by decide
  simp only [Fin.prod_univ_two, Fin.sum_univ_two, e0, e1, Finset.prod_singleton,
    Matrix.cons_val_zero, Matrix.cons_val_one] at h
  linarith [h]

/-! ## 4. The peel step -/

/-- **The peel step.**  Across a coprime split the per-stratum undecided RATIOS add: if the two
factor strata carry ratio bounds `r₁`, `r₂` then the product stratum carries `r₁ + r₂`.  H.102
supplies `T = T₁ T₂`, H.105 the exact composition, H.63 the bound direction. -/
theorem card_undecided_le_of_coprime {O : Type*} [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [Finite (ResidueField O)] [IsAdicComplete (maximalIdeal O) O]
    {n₁ n₂ M : ℕ} (hM : 1 ≤ M) {g₁ g₂ : Polynomial (ResidueField O)} (hg₁ : g₁.Monic)
    (hg₂ : g₂.Monic) (hd₁ : g₁.natDegree = n₁) (hd₂ : g₂.natDegree = n₂) (hcop : IsCoprime g₁ g₂)
    {r₁ r₂ : ℝ} (_hr₁ : 0 ≤ r₁) (_hr₂ : 0 ≤ r₂)
    (h₁ : (Nat.card ((undecidedSet O n₁ M ∩ levelZeroStratum O n₁ M g₁ :
        Set (Coeff O n₁ M))) : ℝ) ≤ r₁ * (Nat.card (levelZeroStratum O n₁ M g₁) : ℝ))
    (h₂ : (Nat.card ((undecidedSet O n₂ M ∩ levelZeroStratum O n₂ M g₂ :
        Set (Coeff O n₂ M))) : ℝ) ≤ r₂ * (Nat.card (levelZeroStratum O n₂ M g₂) : ℝ)) :
    (Nat.card ((undecidedSet O (n₁ + n₂) M ∩ levelZeroStratum O (n₁ + n₂) M (g₁ * g₂) :
        Set (Coeff O (n₁ + n₂) M))) : ℝ)
      ≤ (r₁ + r₂) * (Nat.card (levelZeroStratum O (n₁ + n₂) M (g₁ * g₂)) : ℝ) := by
  classical
  -- the four ℕ-counts
  set u₁ : ℕ := Nat.card ((undecidedSet O n₁ M ∩ levelZeroStratum O n₁ M g₁ :
    Set (Coeff O n₁ M))) with hu₁def
  set u₂ : ℕ := Nat.card ((undecidedSet O n₂ M ∩ levelZeroStratum O n₂ M g₂ :
    Set (Coeff O n₂ M))) with hu₂def
  set T₁ : ℕ := Nat.card (levelZeroStratum O n₁ M g₁) with hT₁def
  set T₂ : ℕ := Nat.card (levelZeroStratum O n₂ M g₂) with hT₂def
  set D₁ : ℕ := Nat.card ((levelZeroStratum O n₁ M g₁ \ undecidedSet O n₁ M :
    Set (Coeff O n₁ M))) with hD₁def
  set D₂ : ℕ := Nat.card ((levelZeroStratum O n₂ M g₂ \ undecidedSet O n₂ M :
    Set (Coeff O n₂ M))) with hD₂def
  -- the complement identities `u + D = T`
  have hsum₁ : u₁ + D₁ = T₁ := by
    rw [hu₁def, hD₁def, hT₁def, Nat.card_coe_set_eq, Nat.card_coe_set_eq, Nat.card_coe_set_eq,
      Set.inter_comm]
    exact Set.ncard_inter_add_ncard_sdiff_eq_ncard _ _ (Set.toFinite _)
  have hsum₂ : u₂ + D₂ = T₂ := by
    rw [hu₂def, hD₂def, hT₂def, Nat.card_coe_set_eq, Nat.card_coe_set_eq, Nat.card_coe_set_eq,
      Set.inter_comm]
    exact Set.ncard_inter_add_ncard_sdiff_eq_ncard _ _ (Set.toFinite _)
  -- H.105's exact composition, in additive form
  have h105 := card_undecided_mulClass hM hg₁ hg₂ hd₁ hd₂ hcop
  have hDT : D₁ * D₂ ≤ T₁ * T₂ := Nat.mul_le_mul (by omega) (by omega)
  have hadd : Nat.card ((undecidedSet O (n₁ + n₂) M ∩ levelZeroStratum O (n₁ + n₂) M (g₁ * g₂) :
      Set (Coeff O (n₁ + n₂) M))) + D₁ * D₂ = T₁ * T₂ := by
    rw [h105]
    exact Nat.sub_add_cancel hDT
  -- H.102's multiplicativity of the census
  have hT := card_levelZeroStratum_mul (O := O) hM hg₁ hg₂ hd₁ hd₂ hcop
  -- move to ℝ
  have hR : ((Nat.card ((undecidedSet O (n₁ + n₂) M ∩ levelZeroStratum O (n₁ + n₂) M (g₁ * g₂) :
      Set (Coeff O (n₁ + n₂) M)))) : ℝ) + (D₁ : ℝ) * (D₂ : ℝ) = (T₁ : ℝ) * (T₂ : ℝ) := by
    exact_mod_cast congrArg (fun k : ℕ => (k : ℝ)) hadd
  have hD₁R : (D₁ : ℝ) = (T₁ : ℝ) - (u₁ : ℝ) := by
    have : ((u₁ + D₁ : ℕ) : ℝ) = (T₁ : ℝ) := by exact_mod_cast congrArg (fun k : ℕ => (k : ℝ)) hsum₁
    push_cast at this
    linarith
  have hD₂R : (D₂ : ℝ) = (T₂ : ℝ) - (u₂ : ℝ) := by
    have : ((u₂ + D₂ : ℕ) : ℝ) = (T₂ : ℝ) := by exact_mod_cast congrArg (fun k : ℕ => (k : ℝ)) hsum₂
    push_cast at this
    linarith
  have hu₁T : (u₁ : ℝ) ≤ (T₁ : ℝ) := by
    have : u₁ ≤ T₁ := by omega
    exact_mod_cast this
  have hu₂T : (u₂ : ℝ) ≤ (T₂ : ℝ) := by
    have : u₂ ≤ T₂ := by omega
    exact_mod_cast this
  have hub := union_bound_two (u₁ := (u₁ : ℝ)) (u₂ := (u₂ : ℝ)) (T₁ := (T₁ : ℝ)) (T₂ := (T₂ : ℝ))
    (Nat.cast_nonneg _) (Nat.cast_nonneg _) hu₁T hu₂T
  have hTR : ((Nat.card (levelZeroStratum O (n₁ + n₂) M (g₁ * g₂))) : ℝ) = (T₁ : ℝ) * (T₂ : ℝ) := by
    exact_mod_cast congrArg (fun k : ℕ => (k : ℝ)) hT
  rw [hTR]
  rw [hD₁R, hD₂R] at hR
  have hT₁0 : (0 : ℝ) ≤ (T₁ : ℝ) := Nat.cast_nonneg _
  have hT₂0 : (0 : ℝ) ≤ (T₂ : ℝ) := Nat.cast_nonneg _
  nlinarith [hub, hR, h₁, h₂, hT₁0, hT₂0, mul_nonneg (sub_nonneg.2 h₁) hT₂0,
    mul_nonneg (sub_nonneg.2 h₂) hT₁0]

/-! ## 5. The monic factorization dichotomy -/

/-- **The dichotomy behind the blueprint's step 3.**  A monic polynomial of degree `i ≥ 1` over a
field is either a power `p ^ m` of a monic irreducible (`m ≥ 1`), or a product of two monic
coprime factors of positive degree — in which case both factors have degree `< i`. -/
theorem monic_prime_pow_or_coprime_split {F : Type*} [Field F] {g : Polynomial F} {i : ℕ}
    (hg : g.Monic) (hd : g.natDegree = i) (hi : 1 ≤ i) :
    (∃ (p : Polynomial F) (m d : ℕ), p.Monic ∧ Irreducible p ∧ 1 ≤ m ∧ p.natDegree = d ∧
        m * d = i ∧ g = p ^ m) ∨
    (∃ (g₁ g₂ : Polynomial F) (n₁ n₂ : ℕ), g₁.Monic ∧ g₂.Monic ∧ 1 ≤ n₁ ∧ 1 ≤ n₂ ∧
        g₁.natDegree = n₁ ∧ g₂.natDegree = n₂ ∧ n₁ + n₂ = i ∧ IsCoprime g₁ g₂ ∧
        g = g₁ * g₂) := by
  classical
  have hg0 : g ≠ 0 := hg.ne_zero
  have hgu : ¬ IsUnit g := by
    intro hu
    have h0 := Polynomial.natDegree_eq_zero_of_isUnit hu
    omega
  obtain ⟨p₀, hp₀, hp₀d⟩ := WfDvdMonoid.exists_irreducible_factor hgu hg0
  have hp₀0 : p₀ ≠ 0 := hp₀.ne_zero
  have huu : IsUnit (Polynomial.C (p₀.leadingCoeff)⁻¹) :=
    Polynomial.isUnit_C.2 (isUnit_iff_ne_zero.2
      (inv_ne_zero (Polynomial.leadingCoeff_ne_zero.2 hp₀0)))
  have hassoc : Associated (p₀ * Polynomial.C (p₀.leadingCoeff)⁻¹) p₀ :=
    associated_mul_unit_left p₀ _ huu
  set p : Polynomial F := p₀ * Polynomial.C (p₀.leadingCoeff)⁻¹ with hpdef
  have hpm : p.Monic := Polynomial.monic_mul_leadingCoeff_inv hp₀0
  have hpi : Irreducible p := hassoc.symm.irreducible hp₀
  have hpd : p ∣ g := hassoc.dvd.trans hp₀d
  have hpdeg1 : 1 ≤ p.natDegree := by
    rcases Nat.eq_zero_or_pos p.natDegree with h0 | h
    · exact absurd (Polynomial.eq_one_of_monic_natDegree_zero hpm h0 ▸ isUnit_one) hpi.not_isUnit
    · exact h
  obtain ⟨m, a, hna, hgeq⟩ := WfDvdMonoid.max_power_factor hg0 hpi
  have hm1 : 1 ≤ m := by
    rcases Nat.eq_zero_or_pos m with h0 | h
    · rw [h0, pow_zero, one_mul] at hgeq
      exact absurd (hgeq ▸ hpd) hna
    · exact h
  have ham : a.Monic := (hpm.pow m).of_mul_monic_left (hgeq ▸ hg)
  by_cases hadeg : a.natDegree = 0
  · left
    have ha1 : a = 1 := Polynomial.eq_one_of_monic_natDegree_zero ham hadeg
    have hgp : g = p ^ m := by rw [hgeq, ha1, mul_one]
    have hdeg : m * p.natDegree = i := by
      rw [← hd, hgp, hpm.natDegree_pow]
    exact ⟨p, m, p.natDegree, hpm, hpi, hm1, rfl, hdeg, hgp⟩
  · right
    have hpmdeg : (p ^ m).natDegree = m * p.natDegree := hpm.natDegree_pow m
    have hn₁ : 1 ≤ (p ^ m).natDegree := by
      rw [hpmdeg]
      exact Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by omega))
    have hn₂ : 1 ≤ a.natDegree := Nat.one_le_iff_ne_zero.2 hadeg
    have hsum : (p ^ m).natDegree + a.natDegree = i := by
      rw [← hd, hgeq, (hpm.pow m).natDegree_mul ham]
    have hcop : IsCoprime (p ^ m) a := (Irreducible.coprime_pow_of_not_dvd m hpi hna).symm
    exact ⟨p ^ m, a, (p ^ m).natDegree, a.natDegree, hpm.pow m, ham, hn₁, hn₂, rfl, rfl, hsum,
      hcop, hgeq⟩

/-! ## 6. Constant bookkeeping -/

/-- **H.66's `RateSpecies.mono`, scalarised.**  The rate value is monotone in each of its three
constants. -/
theorem rate_const_le {Q : ℕ} (hQ : 2 ≤ Q) {K K' : ℝ} {B B' c c' : ℕ} (hK : 0 ≤ K)
    (hKK : K ≤ K') (hB : B ≤ B') (hc : c ≤ c') {M : ℕ} (hM : 1 ≤ M) :
    K * (M : ℝ) ^ B * ((Q : ℝ) ^ (M - c))⁻¹ ≤ K' * (M : ℝ) ^ B' * ((Q : ℝ) ^ (M - c'))⁻¹ := by
  have h : RateSpecies Q K B c (fun M => K * (M : ℝ) ^ B * ((Q : ℝ) ^ (M - c))⁻¹) :=
    fun _ _ => le_rfl
  exact (h.mono hQ hKK hK hB hc) M hM

/-- The rate value is nonnegative. -/
theorem rate_value_nonneg {Q : ℕ} {K : ℝ} {B c M : ℕ} (hK : (0 : ℝ) ≤ K) :
    (0 : ℝ) ≤ K * (M : ℝ) ^ B * ((Q : ℝ) ^ (M - c))⁻¹ := by
  positivity

/-! ## 7. The induction-hypothesis import -/

/-- **The IH import.**  A GLOBAL rate at degree `i` (what `InductionPackage i` supplies) becomes a
PER-STRATUM ratio bound at degree `i`, at the cost of inflating the exponent offset `c ↦ c + i`.
The cost is exactly the normalisation mismatch: the global census divides by `q ^ (i M)` while a
single stratum has only `q ^ (i (M − 1))` classes, a factor `q ^ i`.  In the short window
`M ≤ c + i` the inflated bound is vacuous (`≥ 1`) and the trivial bound `u ≤ T` carries it. -/
theorem stratum_le_of_global {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [IsAdicComplete (maximalIdeal O) O] [Finite (ResidueField O)] {i M : ℕ} (hM : 1 ≤ M)
    {g : Polynomial (ResidueField O)} (hg : g.Monic) (hd : g.natDegree = i)
    {K : ℝ} {B c : ℕ} (hK : 1 ≤ K)
    (h : undecidedSeq O i M ≤ K * (M : ℝ) ^ B * ((residueCard O : ℝ) ^ (M - c))⁻¹) :
    (Nat.card ((undecidedSet O i M ∩ levelZeroStratum O i M g : Set (Coeff O i M))) : ℝ)
      ≤ K * (M : ℝ) ^ B * ((residueCard O : ℝ) ^ (M - (c + i)))⁻¹
        * (Nat.card (levelZeroStratum O i M g) : ℝ) := by
  classical
  have hq2 : 2 ≤ residueCard O := two_le_residueCard O
  have hq0 : (0 : ℝ) < (residueCard O : ℝ) := by
    have : (0 : ℕ) < residueCard O := by omega
    exact_mod_cast this
  have hM1 : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
  have hMB : (1 : ℝ) ≤ (M : ℝ) ^ B := one_le_pow₀ hM1
  -- the census
  have hT : Nat.card (levelZeroStratum O i M g) = residueCard O ^ (i * (M - 1)) :=
    card_levelZeroStratum hM hg hd
  -- `u ≤ T` and `u ≤ undecidedCount`
  have husub : (undecidedSet O i M ∩ levelZeroStratum O i M g : Set (Coeff O i M))
      ⊆ levelZeroStratum O i M g := Set.inter_subset_right
  have huT : Nat.card ((undecidedSet O i M ∩ levelZeroStratum O i M g : Set (Coeff O i M)))
      ≤ Nat.card (levelZeroStratum O i M g) := by
    rw [Nat.card_coe_set_eq, Nat.card_coe_set_eq]
    exact Set.ncard_le_ncard husub (Set.toFinite _)
  have huU : Nat.card ((undecidedSet O i M ∩ levelZeroStratum O i M g : Set (Coeff O i M)))
      ≤ undecidedCount O i M := by
    rw [undecidedCount, Nat.card_coe_set_eq, Nat.card_coe_set_eq]
    exact Set.ncard_le_ncard Set.inter_subset_left (Set.toFinite _)
  set u : ℕ := Nat.card ((undecidedSet O i M ∩ levelZeroStratum O i M g : Set (Coeff O i M)))
    with hudef
  -- the global bound, cleared of `undecidedSeq`'s normalisation
  have hqpow : (0 : ℝ) < (residueCard O : ℝ) ^ (i * M) := by positivity
  have hglob : (undecidedCount O i M : ℝ)
      ≤ K * (M : ℝ) ^ B * ((residueCard O : ℝ) ^ (M - c))⁻¹ * (residueCard O : ℝ) ^ (i * M) := by
    have := h
    rw [undecidedSeq, div_le_iff₀ hqpow] at this
    exact this
  -- `q ^ (i M) = q ^ i · T`
  have hsplit : (residueCard O : ℝ) ^ (i * M)
      = (residueCard O : ℝ) ^ i * (Nat.card (levelZeroStratum O i M g) : ℝ) := by
    rw [hT]
    push_cast
    rw [← pow_add]
    congr 1
    obtain ⟨M', rfl⟩ : ∃ M', M = M' + 1 := ⟨M - 1, by omega⟩
    simp [Nat.mul_succ, Nat.add_comm]
  have hstep : (u : ℝ)
      ≤ K * (M : ℝ) ^ B * ((residueCard O : ℝ) ^ (M - c))⁻¹ * (residueCard O : ℝ) ^ i
        * (Nat.card (levelZeroStratum O i M g) : ℝ) := by
    have h1 : (u : ℝ) ≤ (undecidedCount O i M : ℝ) := by exact_mod_cast huU
    calc (u : ℝ) ≤ (undecidedCount O i M : ℝ) := h1
      _ ≤ K * (M : ℝ) ^ B * ((residueCard O : ℝ) ^ (M - c))⁻¹ * (residueCard O : ℝ) ^ (i * M) :=
          hglob
      _ = _ := by rw [hsplit]; ring
  by_cases hle : i ≤ M - c
  · -- the long window: the `q ^ i` is exactly the offset inflation
    have hexp : M - (c + i) = (M - c) - i := by omega
    have hpow : (residueCard O : ℝ) ^ (M - c)
        = (residueCard O : ℝ) ^ ((M - c) - i) * (residueCard O : ℝ) ^ i := by
      rw [← pow_add]
      congr 1
      omega
    have hne : ((residueCard O : ℝ) ^ i) ≠ 0 := by positivity
    have hne' : ((residueCard O : ℝ) ^ ((M - c) - i)) ≠ 0 := by positivity
    have hrw : ((residueCard O : ℝ) ^ (M - c))⁻¹ * (residueCard O : ℝ) ^ i
        = ((residueCard O : ℝ) ^ ((M - c) - i))⁻¹ := by
      rw [hpow, mul_inv]
      field_simp
    rw [hexp]
    calc (u : ℝ)
        ≤ K * (M : ℝ) ^ B * ((residueCard O : ℝ) ^ (M - c))⁻¹ * (residueCard O : ℝ) ^ i
            * (Nat.card (levelZeroStratum O i M g) : ℝ) := hstep
      _ = K * (M : ℝ) ^ B * (((residueCard O : ℝ) ^ (M - c))⁻¹ * (residueCard O : ℝ) ^ i)
            * (Nat.card (levelZeroStratum O i M g) : ℝ) := by ring
      _ = K * (M : ℝ) ^ B * ((residueCard O : ℝ) ^ ((M - c) - i))⁻¹
            * (Nat.card (levelZeroStratum O i M g) : ℝ) := by rw [hrw]
  · -- the short window: the bound is `≥ T`, and `u ≤ T`
    have hexp : M - (c + i) = 0 := by omega
    rw [hexp, pow_zero, inv_one, mul_one]
    have huTR : (u : ℝ) ≤ (Nat.card (levelZeroStratum O i M g) : ℝ) := by exact_mod_cast huT
    have hTR0 : (0 : ℝ) ≤ (Nat.card (levelZeroStratum O i M g) : ℝ) := Nat.cast_nonneg _
    have hKM : (1 : ℝ) ≤ K * (M : ℝ) ^ B := by nlinarith
    nlinarith

end Uniformity.Density.Induction

/-! ## 8. Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Induction.proj_one_eq_iff
#print axioms Uniformity.Density.Induction.card_levelZeroStratum
#print axioms Uniformity.Density.Induction.union_bound_two
#print axioms Uniformity.Density.Induction.card_undecided_le_of_coprime
#print axioms Uniformity.Density.Induction.monic_prime_pow_or_coprime_split
#print axioms Uniformity.Density.Induction.rate_const_le
#print axioms Uniformity.Density.Induction.rate_value_nonneg
#print axioms Uniformity.Density.Induction.stratum_le_of_global

end AxCheck
