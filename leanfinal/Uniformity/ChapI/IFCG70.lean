/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import Uniformity.ChapI.IFCG68
import Uniformity.ChapI.IFCG19

/-!
# Uniformity.ChapI.IFCG70 — [GNA 2026-08-31] the general-`n` diagonal assembly: the
`n`-ary convolution, the factorization-type grouping, and the depth-density `ZcURLim`
at EVERY `(n₁, n₂)`

Stage GNA of the cone census (design record `runs/wave-c/verdict_GNA.md`).  NA22's
IFCG68 closed route step (d) at `n = 2` (the duo law and the `(2, n₂)` `ZcURLim`);
its §7 docstring names the general-`n` remainder, executed HERE in full:

* **§0 the polynomial mirror of `primo`**: `primoPoly δ e v ∈ ℚ[X]` with
  `primo q δ e v = (primoPoly δ e v).eval q` for every `q ≥ 1` — the `N`-free primary
  values are uniform polynomials in `q`.
* **§1 ★ THE `n`-ARY FOLD** (`card_stratumDepthSet_prod`): over a complete DVR, for any
  finite family of pairwise-coprime monic residual factors with per-factor normalized
  laws, the stratified census at the product residual is the COEFFICIENT OF THE
  `PowerSeries ℕ` PRODUCT of the per-factor laws — the `n`-ary convolution of DGT's
  binary step `card_stratumDepthSet_mul`, by one `Finset` induction carrying the exact
  multiplied normalization (no division anywhere; commutativity and associativity of
  the convolution are the ring axioms of `PowerSeries ℕ`).
* **§2 the per-shape general value** (`card_stratumDepthSet_eq_patRate`): every monic
  degree-`n` residual `g` factors into its primary parts `p^{count p}`; the fold +
  IFCG65's `card_stratumDepthSet_pow` give
  `#strat(n,N,v,g)·q^{v+n} = coeff_v (patRate q (patternOf g)) · q^{n(2N−1)}`, where
  `patRate q λ` is the `PowerSeries ℕ` product of `primo`-series over the pattern
  `λ = patternOf g` (IFCG17's multiset of `(degree, multiplicity)` pairs).
* **§3 ★ THE FIBER-COUNT POLYNOMIAL** (`exists_fiberPoly`): the number of monic
  degree-`n` polynomials with pattern `λ` avoiding a set `A` of monic irreducibles
  depends on the finite field ONLY through `q` and the per-degree avoidance profile —
  a `ℚ[X]` value, by multiset induction on `λ` through IFCG17's landed double count
  `sum_sigma_fiber_eq` (with `F ≡ 1`) and IFCG19's `necklacePoly_eval_card` — the
  necklace-multinomial bookkeeping with NO explicit multinomials.
* **§4 ★★ THE GENERAL DIAGONAL CENSUS** (`card_redDepthPairSet_general`): with
  `zed K n v := Σ_{g ∈ monicFinset K n} coeff_v (patRate q (patternOf g))`,
  `#redDepthPairSet(n,N,v)·q^{v+n} = zed·q^{n(2N−1)}` for `v < N` — exact at every
  level, uniform in `q`, `n`, `N` — via IFCG63's shape partition reindexed along
  `monicPoly`.
* **§5 the polynomiality of the census**: `Zpoly n v ∈ ℚ[X]` with
  `zed K n v = (Zpoly n v).eval q` — the type grouping (`patternUniverse n` indexes the
  finitely many candidate patterns; per-pattern fiber counts from §3, per-pattern
  convolution values from §0).
* **§6 ★★★ THE `ZcURLim`, FIRED AT EVERY `(n₁, n₂)`**: `zcURLim_redDiag` (the reduced
  diagonal density at every `n ≥ 1`, witness `(Zpoly n v, X^{v+2n})`), then through
  IFCG61's transport and swap: **`zcURLim_depthDensity` at ALL `n₁, n₂ ≥ 1`** — VCL's
  axis 1 closes entirely.
* **§7 the regression**: `2·zed K 2 v = duo (#K) v` — the general assembly reproduces
  NA22's independently-derived duo law at `n = 2` (hence inherits its five
  battery-verified IGV rows), and the `(2,2)` instance of §6 is NA22's
  `zcURLim_depthDensity_two_two` statement verbatim.

## THE HONEST FENCE

Everything here is uniform in `q`, `n`, `v`, and the window `N`; no statement is
weakened.  The polynomials `Zpoly n v` are not computed in closed form (IGV's
`Z_m(t)` generating function is the predicted closed form; the regression row §7
verifies the `n = 2` collapse exactly) — closed forms are display work, not census
work, and are NOT needed for the `ZcURLim`.

## Axiom fence (machine-exact at landing)

EVERY row of the AxCheck footer expects PURE Lean core
`{propext, Classical.choice, Quot.sound}`.  B.42, the C.33 cites, and
`AX_cellRecursion` must NOT occur.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

noncomputable section

namespace Uniformity.Density.IFCG70

open IsLocalRing Polynomial Filter Topology
open Uniformity.Density.Induction
open Uniformity.Density.IFCG24 (ZcURLim)
open Uniformity.Density.IFCG56 (depthPairSet)
open Uniformity.Density.IFCG61 (redDepthPairSet zcURLim_depthDensity_of_reduced
  card_depthPairSet_swap)
open Uniformity.Density.IFCG63 (stratumDepthSet card_stratumDepthSet_mul
  card_redDepthPairSet_eq_sum_strata)
open Uniformity.Density.IFCG65 (primo primo_one card_stratumDepthSet_pow
  card_stratumDepthSet_zero)
open Uniformity.Density.IFCG17 (patternOf patternOf_one patternOf_pow_mul
  count_patternOf monicFinset irredFinset fiberFinset mem_monicFinset_iff
  mem_irredFinset_iff mem_fiberFinset_iff fiberFinset_zero sum_sigma_fiber_eq
  prod_normalizedFactors_of_monic mem_normalizedFactors_iff_dvd monicPoly_coeff_eq_self
  monic_of_mem_normalizedFactors monic_prod_of_forall_monic)
open Uniformity.Density.IFCG19 (necklacePoly necklacePoly_eval_card
  natCard_irredOfDeg_eq_card_irredFinset)
open Uniformity.Density.IFCG68 (duo monicPoly_injective isCoprime_X_sub_C_of_ne
  split_or_dbl_of_not_irreducible split_ne_dbl not_irreducible_mul_linear
  not_irreducible_sq_linear card_dblVecs two_mul_card_splitVecs two_mul_card_inertVecs)

attribute [local instance] Classical.propDecidable

/-! ## §0 — the polynomial mirror of `primo` -/

section PrimoPoly

/-- The `ℚ[X]` mirror of IFCG65's `primo` recursion: the SAME well-founded recursion
with the monomial differences `X^a − X^{a−δ}` in place of `q^a − q^{a−δ}`. -/
def primoPoly (δ : ℕ) : ℕ → ℕ → Polynomial ℚ
  | 0, v => if v = 0 then 1 else 0
  | (e + 1), v =>
      (if h : 1 ≤ δ * (e + 1) ∧ δ * (e + 1) ≤ v then
        primoPoly δ (e + 1) (v - δ * (e + 1)) else 0)
      + ∑ j ∈ (Finset.range (e + 1)).attach,
          (Polynomial.X ^ (δ * (e + 1) - δ * (j : ℕ))
              - Polynomial.X ^ (δ * (e + 1) - δ * (j : ℕ) - δ))
            * (if δ * (j : ℕ) ≤ v then primoPoly δ (j : ℕ) (v - δ * (j : ℕ)) else 0)
  termination_by e v => (e, v)
  decreasing_by
  · exact Prod.Lex.right (e + 1) (by omega)
  · exact Prod.Lex.left _ _ (by
      have := j.2
      rw [Finset.mem_range] at this
      omega)

/-- **The cast bridge**: `primo` at any `q ≥ 1` is the evaluation of `primoPoly`. -/
theorem primo_cast {q : ℕ} (hq : 1 ≤ q) (δ e v : ℕ) :
    ((primo q δ e v : ℕ) : ℚ) = (primoPoly δ e v).eval (q : ℚ) := by
  induction e using Nat.strong_induction_on generalizing v with
  | _ e IHe =>
    induction v using Nat.strong_induction_on with
    | _ v IHv =>
      rcases e with _ | e'
      · rw [primo, primoPoly]
        by_cases hv0 : v = 0
        · rw [if_pos hv0, if_pos hv0, Nat.cast_one, Polynomial.eval_one]
        · rw [if_neg hv0, if_neg hv0, Nat.cast_zero, Polynomial.eval_zero]
      · rw [primo, primoPoly, Nat.cast_add, Polynomial.eval_add]
        congr 1
        · -- the self-loop term
          by_cases hself : 1 ≤ δ * (e' + 1) ∧ δ * (e' + 1) ≤ v
          · rw [dif_pos hself, dif_pos hself]
            exact IHv (v - δ * (e' + 1)) (by omega)
          · rw [dif_neg hself, dif_neg hself, Nat.cast_zero, Polynomial.eval_zero]
        · -- the peel sum, termwise
          rw [Nat.cast_sum, Polynomial.eval_finsetSum]
          refine Finset.sum_congr rfl fun j _ => ?_
          have hjlt : (j : ℕ) < e' + 1 := Finset.mem_range.mp j.2
          rw [Nat.cast_mul, Polynomial.eval_mul]
          congr 1
          · have hle : q ^ (δ * (e' + 1) - δ * (j : ℕ) - δ)
                ≤ q ^ (δ * (e' + 1) - δ * (j : ℕ)) :=
              Nat.pow_le_pow_right hq (Nat.sub_le _ _)
            rw [Nat.cast_sub hle, Polynomial.eval_sub, Polynomial.eval_pow,
              Polynomial.eval_pow, Polynomial.eval_X]
            push_cast
            ring
          · by_cases hjv : δ * (j : ℕ) ≤ v
            · rw [if_pos hjv, if_pos hjv]
              exact IHe (j : ℕ) hjlt (v - δ * (j : ℕ))
            · rw [if_neg hjv, if_neg hjv, Nat.cast_zero, Polynomial.eval_zero]

end PrimoPoly

/-! ## §1 — ★ the `n`-ary fold: the stratified census at a coprime product residual -/

section Fold

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)]

/-- ★ **THE `n`-ARY FOLD** (the general-`n` stratum convolution): over a complete DVR,
for a finite family of pairwise-coprime monic residual factors of positive degree with
per-factor normalized census laws `V i`, the stratified census at the product residual
is the coefficient of the `PowerSeries ℕ` product of the per-factor laws — in the exact
multiplied normalization, uniformly in the window.  `Finset` induction over the family;
each step is DGT's binary `card_stratumDepthSet_mul`. -/
theorem card_stratumDepthSet_prod [IsAdicComplete (maximalIdeal O) O] {ι : Type*}
    (T : Finset ι) (h : ι → Polynomial (ResidueField O)) (V : ι → ℕ → ℕ) {N : ℕ}
    (hN : 0 < N)
    (hmon : ∀ i ∈ T, (h i).Monic) (hdeg : ∀ i ∈ T, 0 < (h i).natDegree)
    (hcop : ∀ i ∈ T, ∀ j ∈ T, i ≠ j → IsCoprime (h i) (h j))
    (hlaw : ∀ i ∈ T, ∀ w, w < N →
      Nat.card (stratumDepthSet O (h i).natDegree N w (h i))
          * residueCard O ^ (w + (h i).natDegree)
        = V i w * residueCard O ^ ((h i).natDegree * (2 * N - 1)))
    {v : ℕ} (hv : v < N) :
    Nat.card (stratumDepthSet O (∑ i ∈ T, (h i).natDegree) N v (∏ i ∈ T, h i))
        * residueCard O ^ (v + ∑ i ∈ T, (h i).natDegree)
      = PowerSeries.coeff v (∏ i ∈ T, PowerSeries.mk (V i))
          * residueCard O ^ ((∑ i ∈ T, (h i).natDegree) * (2 * N - 1)) := by
  classical
  induction T using Finset.induction_on generalizing v hv with
  | empty =>
    rw [Finset.sum_empty, Finset.prod_empty, Finset.prod_empty,
      card_stratumDepthSet_zero hN, PowerSeries.coeff_one]
    by_cases hv0 : v = 0
    · subst hv0
      norm_num
    · rw [if_neg hv0, Nat.zero_mul, Nat.zero_mul]
  | insert a s ha IH =>
    have hmona : (h a).Monic := hmon a (Finset.mem_insert_self a s)
    have hdega : 0 < (h a).natDegree := hdeg a (Finset.mem_insert_self a s)
    have hmons : ∀ i ∈ s, (h i).Monic :=
      fun i hi => hmon i (Finset.mem_insert_of_mem hi)
    have hdegs : ∀ i ∈ s, 0 < (h i).natDegree :=
      fun i hi => hdeg i (Finset.mem_insert_of_mem hi)
    have hcops : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → IsCoprime (h i) (h j) :=
      fun i hi j hj => hcop i (Finset.mem_insert_of_mem hi) j (Finset.mem_insert_of_mem hj)
    have hlaws : ∀ i ∈ s, ∀ w, w < N →
        Nat.card (stratumDepthSet O (h i).natDegree N w (h i))
            * residueCard O ^ (w + (h i).natDegree)
          = V i w * residueCard O ^ ((h i).natDegree * (2 * N - 1)) :=
      fun i hi => hlaw i (Finset.mem_insert_of_mem hi)
    rw [Finset.sum_insert ha, Finset.prod_insert ha, Finset.prod_insert ha]
    by_cases hs : s = ∅
    · subst hs
      rw [Finset.sum_empty, Finset.prod_empty, Finset.prod_empty, Nat.add_zero,
        mul_one, mul_one, PowerSeries.coeff_mk]
      exact hlaw a (Finset.mem_insert_self a ∅) v hv
    · have hsne : s.Nonempty := Finset.nonempty_iff_ne_empty.mpr hs
      have hD : 0 < ∑ i ∈ s, (h i).natDegree := Finset.sum_pos hdegs hsne
      have hmonP : (∏ i ∈ s, h i).Monic := Polynomial.monic_prod_of_monic s h hmons
      have hdegP : (∏ i ∈ s, h i).natDegree = ∑ i ∈ s, (h i).natDegree :=
        Polynomial.natDegree_prod_of_monic s h hmons
      have hcopP : IsCoprime (h a) (∏ i ∈ s, h i) :=
        IsCoprime.prod_right fun i hi =>
          hcop a (Finset.mem_insert_self a s) i (Finset.mem_insert_of_mem hi)
            (fun hai => ha (hai ▸ hi))
      have hbin := card_stratumDepthSet_mul (O := O) hdega hD hv hmona hmonP rfl
        hdegP hcopP
      rw [hbin, Finset.sum_mul]
      have hterm : ∀ w ∈ Finset.range (v + 1),
          Nat.card (stratumDepthSet O (h a).natDegree N w (h a))
              * Nat.card (stratumDepthSet O (∑ i ∈ s, (h i).natDegree) N (v - w)
                  (∏ i ∈ s, h i))
              * residueCard O ^ (v + ((h a).natDegree + ∑ i ∈ s, (h i).natDegree))
            = (V a w * residueCard O ^ ((h a).natDegree * (2 * N - 1)))
              * (PowerSeries.coeff (v - w) (∏ i ∈ s, PowerSeries.mk (V i))
                  * residueCard O ^ ((∑ i ∈ s, (h i).natDegree) * (2 * N - 1))) := by
        intro w hw
        rw [Finset.mem_range] at hw
        have hsplit : Nat.card (stratumDepthSet O (h a).natDegree N w (h a))
              * Nat.card (stratumDepthSet O (∑ i ∈ s, (h i).natDegree) N (v - w)
                  (∏ i ∈ s, h i))
              * residueCard O ^ (v + ((h a).natDegree + ∑ i ∈ s, (h i).natDegree))
            = (Nat.card (stratumDepthSet O (h a).natDegree N w (h a))
                  * residueCard O ^ (w + (h a).natDegree))
              * (Nat.card (stratumDepthSet O (∑ i ∈ s, (h i).natDegree) N (v - w)
                    (∏ i ∈ s, h i))
                  * residueCard O ^ ((v - w) + ∑ i ∈ s, (h i).natDegree)) := by
          have hexp : (w + (h a).natDegree)
                + ((v - w) + ∑ i ∈ s, (h i).natDegree)
              = v + ((h a).natDegree + ∑ i ∈ s, (h i).natDegree) := by omega
          rw [← hexp, pow_add]
          ring
        rw [hsplit, hlaw a (Finset.mem_insert_self a s) w (by omega),
          IH hmons hdegs hcops hlaws (by omega : v - w < N)]
      rw [Finset.sum_congr rfl hterm]
      have hcoeff : PowerSeries.coeff v
            (PowerSeries.mk (V a) * ∏ i ∈ s, PowerSeries.mk (V i))
          = ∑ w ∈ Finset.range (v + 1),
              V a w * PowerSeries.coeff (v - w) (∏ i ∈ s, PowerSeries.mk (V i)) := by
        rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
        exact Finset.sum_congr rfl fun w _ => by rw [PowerSeries.coeff_mk]
      have hpow : residueCard O
            ^ (((h a).natDegree + ∑ i ∈ s, (h i).natDegree) * (2 * N - 1))
          = residueCard O ^ ((h a).natDegree * (2 * N - 1))
            * residueCard O ^ ((∑ i ∈ s, (h i).natDegree) * (2 * N - 1)) := by
        rw [← pow_add, ← Nat.add_mul]
      rw [hcoeff, hpow]
      conv_rhs => rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun w _ => ?_
      ring

end Fold

/-! ## §2 — the per-shape general value: the pattern convolution -/

section PatRate

/-- **The pattern rate series**: the `PowerSeries ℕ` product of the `primo` series over
the pattern's `(δ, e)` blocks — the `n`-ary convolution of the primary values. -/
def patRate (q : ℕ) (lam : Multiset (ℕ × ℕ)) : PowerSeries ℕ :=
  (lam.map (fun de => PowerSeries.mk (fun w => primo q de.1 de.2 w))).prod

/-- **The pattern weight**: `Σ δ·e` over the pattern — the degree it accounts for. -/
def patternWeight (lam : Multiset (ℕ × ℕ)) : ℕ :=
  (lam.map (fun de => de.1 * de.2)).sum

variable {K : Type*} [Field K]

open UniqueFactorizationMonoid in
/-- Every block of the pattern of a polynomial has positive degree and positive
multiplicity. -/
theorem one_le_of_mem_patternOf {g : Polynomial K} :
    ∀ de ∈ patternOf g, 1 ≤ de.1 ∧ 1 ≤ de.2 := by
  intro de hde
  unfold Uniformity.Density.IFCG17.patternOf at hde
  rw [Multiset.mem_map] at hde
  obtain ⟨p, hp, rfl⟩ := hde
  rw [Finset.mem_val, Multiset.mem_toFinset] at hp
  exact ⟨(irreducible_of_normalized_factor p hp).natDegree_pos,
    Multiset.count_pos.mpr hp⟩

open UniqueFactorizationMonoid in
/-- The primary decomposition of a monic polynomial, `Finset.prod`-shaped: the product
of `p ^ count p` over the distinct normalized factors. -/
theorem monic_eq_prod_pow_count {g : Polynomial K} (hg : g.Monic) :
    g = ∏ p ∈ (normalizedFactors g).toFinset,
      p ^ ((normalizedFactors g).count p) := by
  conv_lhs => rw [← prod_normalizedFactors_of_monic hg]
  exact Finset.prod_multiset_count (normalizedFactors g)

open UniqueFactorizationMonoid in
/-- The pattern weight of a monic polynomial is its degree. -/
theorem patternWeight_patternOf {g : Polynomial K} (hg : g.Monic) :
    patternWeight (patternOf g) = g.natDegree := by
  conv_rhs => rw [monic_eq_prod_pow_count hg]
  rw [Polynomial.natDegree_prod_of_monic _ _
    (fun p hp => (monic_of_mem_normalizedFactors (Multiset.mem_toFinset.mp hp)).pow _)]
  have hterm : ∀ p ∈ (normalizedFactors g).toFinset,
      (p ^ ((normalizedFactors g).count p)).natDegree
        = p.natDegree * (normalizedFactors g).count p := fun p _ => by
    rw [Polynomial.natDegree_pow, Nat.mul_comm]
  rw [Finset.sum_congr rfl hterm]
  unfold patternWeight Uniformity.Density.IFCG17.patternOf
  rw [Multiset.map_map]
  rfl

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)]

/-- ★ **The per-shape general value**: the stratified census at ANY monic degree-`n`
residual is the pattern convolution of `primo` values, in the exact multiplied
normalization — the fold at the primary decomposition + IFCG65's closed form. -/
theorem card_stratumDepthSet_eq_patRate [IsAdicComplete (maximalIdeal O) O]
    {n N v : ℕ} (hN : 0 < N) (hv : v < N)
    {g : Polynomial (ResidueField O)} (hg : g.Monic) (hgd : g.natDegree = n) :
    Nat.card (stratumDepthSet O n N v g) * residueCard O ^ (v + n)
      = PowerSeries.coeff v (patRate (residueCard O) (patternOf g))
          * residueCard O ^ (n * (2 * N - 1)) := by
  classical
  -- the fold hypotheses at the primary decomposition
  have hmon : ∀ p ∈ (UniqueFactorizationMonoid.normalizedFactors g).toFinset,
      (p ^ ((UniqueFactorizationMonoid.normalizedFactors g).count p)).Monic :=
    fun p hp => (monic_of_mem_normalizedFactors (Multiset.mem_toFinset.mp hp)).pow _
  have hdeg : ∀ p ∈ (UniqueFactorizationMonoid.normalizedFactors g).toFinset,
      0 < (p ^ ((UniqueFactorizationMonoid.normalizedFactors g).count p)).natDegree := by
    intro p hp
    rw [Polynomial.natDegree_pow]
    exact Nat.mul_pos (Multiset.count_pos.mpr (Multiset.mem_toFinset.mp hp))
      (UniqueFactorizationMonoid.irreducible_of_normalized_factor p
        (Multiset.mem_toFinset.mp hp)).natDegree_pos
  have hcop : ∀ p ∈ (UniqueFactorizationMonoid.normalizedFactors g).toFinset,
      ∀ p' ∈ (UniqueFactorizationMonoid.normalizedFactors g).toFinset, p ≠ p' →
        IsCoprime (p ^ ((UniqueFactorizationMonoid.normalizedFactors g).count p))
          (p' ^ ((UniqueFactorizationMonoid.normalizedFactors g).count p')) := by
    intro p hp p' hp' hne
    have hip := UniqueFactorizationMonoid.irreducible_of_normalized_factor p
      (Multiset.mem_toFinset.mp hp)
    have hip' := UniqueFactorizationMonoid.irreducible_of_normalized_factor p'
      (Multiset.mem_toFinset.mp hp')
    have hnd : ¬ p ∣ p' := fun hdvd => hne (eq_of_monic_of_associated
      (monic_of_mem_normalizedFactors (Multiset.mem_toFinset.mp hp))
      (monic_of_mem_normalizedFactors (Multiset.mem_toFinset.mp hp'))
      (hip.associated_of_dvd hip' hdvd))
    exact (hip.coprime_iff_not_dvd.mpr hnd).pow
  have hlaw : ∀ p ∈ (UniqueFactorizationMonoid.normalizedFactors g).toFinset, ∀ w, w < N →
      Nat.card (stratumDepthSet O
            (p ^ ((UniqueFactorizationMonoid.normalizedFactors g).count p)).natDegree N w
            (p ^ ((UniqueFactorizationMonoid.normalizedFactors g).count p)))
          * residueCard O
            ^ (w + (p ^ ((UniqueFactorizationMonoid.normalizedFactors g).count p)).natDegree)
        = primo (residueCard O) p.natDegree
              ((UniqueFactorizationMonoid.normalizedFactors g).count p) w
          * residueCard O
            ^ ((p ^ ((UniqueFactorizationMonoid.normalizedFactors g).count p)).natDegree
                * (2 * N - 1)) := by
    intro p hp w hw
    have hmem := Multiset.mem_toFinset.mp hp
    have hip := UniqueFactorizationMonoid.irreducible_of_normalized_factor p hmem
    rw [Polynomial.natDegree_pow,
      Nat.mul_comm ((UniqueFactorizationMonoid.normalizedFactors g).count p) p.natDegree]
    exact card_stratumDepthSet_pow hN hip.natDegree_pos hw hip
      (monic_of_mem_normalizedFactors hmem) rfl
  -- fire the fold
  have hfold := card_stratumDepthSet_prod (O := O)
    ((UniqueFactorizationMonoid.normalizedFactors g).toFinset)
    (fun p => p ^ ((UniqueFactorizationMonoid.normalizedFactors g).count p))
    (fun p w => primo (residueCard O) p.natDegree
      ((UniqueFactorizationMonoid.normalizedFactors g).count p) w)
    hN hmon hdeg hcop hlaw hv
  -- realign the three product/sum slots
  have hsum : (∑ p ∈ (UniqueFactorizationMonoid.normalizedFactors g).toFinset,
      (p ^ ((UniqueFactorizationMonoid.normalizedFactors g).count p)).natDegree) = n := by
    rw [← hgd]
    conv_rhs => rw [monic_eq_prod_pow_count hg]
    exact (Polynomial.natDegree_prod_of_monic _ _ hmon).symm
  have hprod : (∏ p ∈ (UniqueFactorizationMonoid.normalizedFactors g).toFinset,
      p ^ ((UniqueFactorizationMonoid.normalizedFactors g).count p)) = g :=
    (monic_eq_prod_pow_count hg).symm
  have hser : (∏ p ∈ (UniqueFactorizationMonoid.normalizedFactors g).toFinset,
        PowerSeries.mk (fun w => primo (residueCard O) p.natDegree
          ((UniqueFactorizationMonoid.normalizedFactors g).count p) w))
      = patRate (residueCard O) (patternOf g) := by
    unfold patRate Uniformity.Density.IFCG17.patternOf
    rw [Multiset.map_map]
    rfl
  rw [hsum, hprod, hser] at hfold
  exact hfold

end PatRate

/-! ## §3 — ★ the fiber-count polynomial: the necklace-multinomial layer -/

section FiberPoly

/-- Every block bounds the pattern weight from below. -/
theorem mul_le_patternWeight {lam : Multiset (ℕ × ℕ)} {de : ℕ × ℕ} (h : de ∈ lam) :
    de.1 * de.2 ≤ patternWeight lam :=
  Multiset.single_le_sum (fun x _ => Nat.zero_le x) _
    (Multiset.mem_map_of_mem (fun de => de.1 * de.2) h)

/-- A pattern with all-positive blocks has at most `weight` many blocks. -/
theorem card_le_patternWeight {lam : Multiset (ℕ × ℕ)}
    (h : ∀ de ∈ lam, 1 ≤ de.1 ∧ 1 ≤ de.2) :
    Multiset.card lam ≤ patternWeight lam := by
  induction lam using Multiset.induction_on with
  | empty => simp [patternWeight]
  | cons de s IH =>
    have hde := h de (Multiset.mem_cons_self de s)
    have hs := IH (fun x hx => h x (Multiset.mem_cons_of_mem hx))
    have h1 : 1 ≤ de.1 * de.2 := Nat.one_le_iff_ne_zero.mpr
      (Nat.mul_ne_zero (by omega) (by omega))
    unfold patternWeight at hs ⊢
    rw [Multiset.map_cons, Multiset.sum_cons, Multiset.card_cons]
    omega

/-- Fibers off the pattern weight are empty: a member's degree IS its pattern weight. -/
theorem fiberFinset_eq_empty_of_weight_ne {K : Type*} [Field K] [Fintype K]
    {n : ℕ} {lam : Multiset (ℕ × ℕ)} (A : Finset (Polynomial K))
    (hne : patternWeight lam ≠ n) : fiberFinset K n lam A = ∅ := by
  rw [Finset.eq_empty_iff_forall_notMem]
  intro g hg
  obtain ⟨⟨hm, hd⟩, hpat, -⟩ := mem_fiberFinset_iff.mp hg
  refine hne ?_
  rw [← hpat, patternWeight_patternOf hm, hd]

/-- ★ **THE FIBER-COUNT POLYNOMIAL**: the number of monic degree-`n` polynomials of
pattern `λ` avoiding a set `A` of monic irreducibles depends on the finite field only
through `q = #K` and the per-degree avoidance profile `a` — the value of ONE `ℚ[X]`
polynomial, uniformly.  Multiset induction on `λ` through IFCG17's double count
`sum_sigma_fiber_eq` (`F ≡ 1`) + IFCG19's `necklacePoly_eval_card`. -/
theorem exists_fiberPoly (lam : Multiset (ℕ × ℕ)) :
    ∀ (n : ℕ) (a : ℕ → ℕ), ∃ P : Polynomial ℚ,
      (∀ de ∈ lam, 1 ≤ de.1 ∧ 1 ≤ de.2) →
      ∀ (K : Type) [Field K] [Fintype K] (A : Finset (Polynomial K)),
        (∀ p ∈ A, p.Monic ∧ Irreducible p) →
        (∀ δ, (A.filter (fun p => p.natDegree = δ)).card = a δ) →
        ((fiberFinset K n lam A).card : ℚ) = P.eval ((Fintype.card K : ℚ)) := by
  induction lam using Multiset.induction_on with
  | empty =>
    intro n a
    by_cases hn : n = 0
    · subst hn
      refine ⟨1, fun _ K _ _ A hA _ => ?_⟩
      rw [fiberFinset_zero A (fun q hq => (hA q hq).2), Finset.card_singleton,
        Polynomial.eval_one, Nat.cast_one]
    · refine ⟨0, fun _ K _ _ A _ _ => ?_⟩
      rw [fiberFinset_eq_empty_of_weight_ne A
          (by simpa [patternWeight] using Ne.symm hn),
        Finset.card_empty, Polynomial.eval_zero, Nat.cast_zero]
  | cons de lam' IH =>
    intro n a
    by_cases hw : patternWeight (de ::ₘ lam') = n
    · obtain ⟨δ, e⟩ := de
      obtain ⟨P', hP'⟩ := IH (patternWeight lam') (fun d => if d = δ then a δ + 1 else a d)
      refine ⟨Polynomial.C (((lam'.count (δ, e) : ℚ) + 1)⁻¹)
        * ((necklacePoly δ - Polynomial.C ((a δ : ℚ))) * P'), ?_⟩
      intro hbounds K _ _ A hA hprof
      obtain ⟨hδ1, he1⟩ := hbounds (δ, e) (Multiset.mem_cons_self _ _)
      -- the weight bookkeeping
      have hn' : n = δ * e + patternWeight lam' := by
        rw [← hw]
        unfold patternWeight
        rw [Multiset.map_cons, Multiset.sum_cons]
      -- IFCG17's double count with F ≡ 1 turns into the counting recursion
      have hdc := sum_sigma_fiber_eq (K := K) hδ1 he1 (patternWeight lam') lam' A hA
        (fun _ => (1 : ℕ))
      have hdc' : ∑ p₀ ∈ irredFinset K δ \ A,
            (fiberFinset K (patternWeight lam') lam' (insert p₀ A)).card
          = (lam'.count (δ, e) + 1)
            * (fiberFinset K (δ * e + patternWeight lam') ((δ, e) ::ₘ lam') A).card := by
        calc ∑ p₀ ∈ irredFinset K δ \ A,
              (fiberFinset K (patternWeight lam') lam' (insert p₀ A)).card
            = ∑ p₀ ∈ irredFinset K δ \ A,
                ∑ _g' ∈ fiberFinset K (patternWeight lam') lam' (insert p₀ A), 1 :=
              Finset.sum_congr rfl fun p₀ _ => Finset.card_eq_sum_ones _
          _ = (lam'.count (δ, e) + 1)
                • ∑ _g ∈ fiberFinset K (δ * e + patternWeight lam')
                    ((δ, e) ::ₘ lam') A, (1 : ℕ) := hdc
          _ = (lam'.count (δ, e) + 1)
                * (fiberFinset K (δ * e + patternWeight lam')
                    ((δ, e) ::ₘ lam') A).card := by
              rw [← Finset.card_eq_sum_ones, smul_eq_mul]
      -- every inserted profile is the bumped one, so the IH evaluates each summand
      have hIHval : ∀ p₀ ∈ irredFinset K δ \ A,
          ((fiberFinset K (patternWeight lam') lam' (insert p₀ A)).card : ℚ)
            = P'.eval ((Fintype.card K : ℚ)) := by
        intro p₀ hp₀
        obtain ⟨hp₀i, hp₀A⟩ := Finset.mem_sdiff.mp hp₀
        obtain ⟨hp₀m, hp₀d, hp₀irr⟩ := mem_irredFinset_iff.mp hp₀i
        refine hP' (fun x hx => hbounds x (Multiset.mem_cons_of_mem hx)) K
          (insert p₀ A) ?_ ?_
        · intro p hp
          rcases Finset.mem_insert.mp hp with rfl | hpA
          · exact ⟨hp₀m, hp₀irr⟩
          · exact hA p hpA
        · intro d
          rw [Finset.filter_insert]
          by_cases hd : d = δ
          · subst hd
            rw [if_pos hp₀d, Finset.card_insert_of_notMem
                (fun hc => hp₀A (Finset.mem_filter.mp hc).1), hprof d, if_pos rfl]
          · rw [if_neg (fun hc => hd (by rw [← hc, hp₀d])), hprof d, if_neg hd]
      -- the outer sum has exactly `I_δ(q) − a δ` equal summands
      have hsub : A.filter (fun p => p.natDegree = δ) ⊆ irredFinset K δ := by
        intro p hp
        obtain ⟨hpA, hpd⟩ := Finset.mem_filter.mp hp
        exact mem_irredFinset_iff.mpr ⟨(hA p hpA).1, hpd, (hA p hpA).2⟩
      have hsdiff : irredFinset K δ \ A
          = irredFinset K δ \ (A.filter (fun p => p.natDegree = δ)) := by
        ext p
        simp only [Finset.mem_sdiff, Finset.mem_filter]
        constructor
        · rintro ⟨hpi, hpA⟩
          exact ⟨hpi, fun hc => hpA hc.1⟩
        · rintro ⟨hpi, hpc⟩
          exact ⟨hpi, fun hpA => hpc ⟨hpA, (mem_irredFinset_iff.mp hpi).2.1⟩⟩
      have haδ_le : a δ ≤ (irredFinset K δ).card := by
        rw [← hprof δ]
        exact Finset.card_le_card hsub
      have hcard_sdiff : (irredFinset K δ \ A).card = (irredFinset K δ).card - a δ := by
        rw [hsdiff, Finset.card_sdiff, Finset.inter_eq_left.mpr hsub, hprof δ]
      -- assemble in ℚ
      have hQ : ((lam'.count (δ, e) : ℚ) + 1)
            * ((fiberFinset K n ((δ, e) ::ₘ lam') A).card : ℚ)
          = (((irredFinset K δ).card : ℚ) - (a δ : ℚ))
            * P'.eval ((Fintype.card K : ℚ)) := by
        have hcast := congrArg (fun m : ℕ => (m : ℚ)) hdc'
        simp only [Nat.cast_sum, Nat.cast_mul, Nat.cast_add, Nat.cast_one] at hcast
        rw [Finset.sum_congr rfl hIHval, Finset.sum_const, nsmul_eq_mul,
          hcard_sdiff, Nat.cast_sub haδ_le] at hcast
        rw [← hn'] at hcast
        exact hcast.symm
      have hneck : (necklacePoly δ).eval ((Fintype.card K : ℚ))
          = ((irredFinset K δ).card : ℚ) := by
        rw [necklacePoly_eval_card K δ hδ1, natCard_irredOfDeg_eq_card_irredFinset]
      rw [Polynomial.eval_mul, Polynomial.eval_mul, Polynomial.eval_C,
        Polynomial.eval_sub, Polynomial.eval_C, hneck]
      have hcnt : ((lam'.count (δ, e) : ℚ) + 1) ≠ 0 := by positivity
      field_simp
      linarith [hQ]
    · refine ⟨0, fun _ K _ _ A _ _ => ?_⟩
      rw [fiberFinset_eq_empty_of_weight_ne A hw, Finset.card_empty,
        Polynomial.eval_zero, Nat.cast_zero]

end FiberPoly

/-! ## §4 — ★★ the general diagonal census -/

section Census

/-- **The pattern universe**: a fixed finite set of candidate patterns containing every
pattern of a monic degree-`n` polynomial over EVERY finite field — sub-multisets of
`n` copies of the block box `[1..n] × [1..n]`. -/
def patternUniverse (n : ℕ) : Finset (Multiset (ℕ × ℕ)) :=
  (Multiset.powerset (n • ((Finset.Icc 1 n ×ˢ Finset.Icc 1 n).val))).toFinset

theorem mem_patternUniverse_iff {n : ℕ} {lam : Multiset (ℕ × ℕ)} :
    lam ∈ patternUniverse n ↔ lam ≤ n • ((Finset.Icc 1 n ×ˢ Finset.Icc 1 n).val) := by
  rw [patternUniverse, Multiset.mem_toFinset, Multiset.mem_powerset]

/-- Blocks of a universe pattern are bounded: `1 ≤ δ`, `1 ≤ e`. -/
theorem one_le_of_mem_patternUniverse {n : ℕ} {lam : Multiset (ℕ × ℕ)}
    (h : lam ∈ patternUniverse n) : ∀ de ∈ lam, 1 ≤ de.1 ∧ 1 ≤ de.2 := by
  intro de hde
  rw [mem_patternUniverse_iff] at h
  have hmem := Multiset.mem_of_le h hde
  have hcount : 0 < Multiset.count de (n • ((Finset.Icc 1 n ×ˢ Finset.Icc 1 n).val)) :=
    Multiset.count_pos.mpr hmem
  rw [Multiset.count_nsmul] at hcount
  have hval : de ∈ (Finset.Icc 1 n ×ˢ Finset.Icc 1 n).val := by
    rw [← Multiset.count_pos]
    rcases Nat.eq_zero_or_pos
      (Multiset.count de ((Finset.Icc 1 n ×ˢ Finset.Icc 1 n).val)) with h0 | h0
    · rw [h0, Nat.mul_zero] at hcount
      omega
    · exact h0
  rw [Finset.mem_val, Finset.mem_product, Finset.mem_Icc, Finset.mem_Icc] at hval
  exact ⟨hval.1.1, hval.2.1⟩

/-- The pattern of a monic degree-`n` polynomial lies in the universe. -/
theorem patternOf_mem_patternUniverse {K : Type*} [Field K] [Fintype K] {n : ℕ}
    {g : Polynomial K} (hg : g.Monic) (hgd : g.natDegree = n) :
    patternOf g ∈ patternUniverse n := by
  rw [mem_patternUniverse_iff, Multiset.le_iff_count]
  intro x
  by_cases hx : x ∈ patternOf g
  · obtain ⟨hx1, hx2⟩ := one_le_of_mem_patternOf x hx
    have hxw : x.1 * x.2 ≤ n := by
      rw [← hgd, ← patternWeight_patternOf hg]
      exact mul_le_patternWeight hx
    have hxmem : x ∈ (Finset.Icc 1 n ×ˢ Finset.Icc 1 n) := by
      rw [Finset.mem_product, Finset.mem_Icc, Finset.mem_Icc]
      exact ⟨⟨hx1, le_trans (Nat.le_mul_of_pos_right x.1 (by omega)) hxw⟩,
        ⟨hx2, le_trans (Nat.le_mul_of_pos_left x.2 (by omega)) hxw⟩⟩
    rw [Multiset.count_nsmul,
      Multiset.count_eq_one_of_mem (Finset.Icc 1 n ×ˢ Finset.Icc 1 n).nodup
        (Finset.mem_val.mpr hxmem), Nat.mul_one]
    calc Multiset.count x (patternOf g) ≤ Multiset.card (patternOf g) :=
          Multiset.count_le_card x _
      _ ≤ patternWeight (patternOf g) :=
          card_le_patternWeight one_le_of_mem_patternOf
      _ = n := by rw [patternWeight_patternOf hg, hgd]
  · rw [Multiset.count_eq_zero_of_notMem hx]
    exact Nat.zero_le _

/-- **The general census numerator**: the pattern-convolution values summed over all
monic degree-`n` residuals. -/
def zed (K : Type*) [Field K] [Fintype K] (n v : ℕ) : ℕ :=
  ∑ g ∈ monicFinset K n, PowerSeries.coeff v (patRate (Fintype.card K) (patternOf g))

/-- Coefficient reading below the top degree (IFCG63's private reader, restated). -/
private theorem monicPoly_coeff_lt {S : Type*} [CommRing S] [IsDomain S] {n : ℕ}
    (a : Fin n → S) {i : ℕ} (hi : i < n) : (monicPoly a).coeff i = a ⟨i, hi⟩ := by
  classical
  unfold monicPoly
  rw [Polynomial.coeff_add, Polynomial.coeff_X_pow, if_neg (Nat.ne_of_lt hi), zero_add,
    Polynomial.finsetSum_coeff, Finset.sum_eq_single (⟨i, hi⟩ : Fin n)]
  · rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_pos rfl, mul_one]
  · intro b _ hbi
    rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
      if_neg fun h => hbi (Fin.ext h.symm), mul_zero]
  · simp

/-- `monicPoly` of the coefficient vector of a monic degree-`n` polynomial is the
polynomial itself (the field-usable restatement of IFCG17's DVR-scoped bridge). -/
private theorem monicPoly_coeff_eq_self' {S : Type*} [CommRing S] [IsDomain S] {n : ℕ}
    {P : Polynomial S} (hP : P.Monic) (hd : P.natDegree = n) :
    monicPoly (fun i : Fin n => P.coeff (i : ℕ)) = P := by
  ext j
  rcases lt_trichotomy j n with hj | heq | hj
  · rw [monicPoly_coeff_lt _ hj]
  · have h1 : (monicPoly (fun i : Fin n => P.coeff (i : ℕ))).coeff n = 1 := by
      have h := (monicPoly_monic (fun i : Fin n => P.coeff (i : ℕ))).coeff_natDegree
      rwa [monicPoly_natDegree] at h
    have h2 : P.coeff n = 1 := by
      rw [← hd]
      exact hP.coeff_natDegree
    rw [heq, h1, h2]
  · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [monicPoly_natDegree]; omega),
      Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)]

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)]

/-- ★★ **THE GENERAL DIAGONAL CENSUS** (route step (d) at EVERY `n`): the reduced
diagonal depth census is `zed`, uniformly in `q`, `n`, and the window —
`#redDepthPairSet(n,N,v)·q^{v+n} = zed(K,n,v)·q^{n(2N−1)}` for `v < N`.  (The `Fintype`
instance is an explicit argument to keep `zed`'s carrier canonical; instantiate with
`Fintype.ofFinite`.) -/
theorem card_redDepthPairSet_general [IsAdicComplete (maximalIdeal O) O]
    [Fintype (ResidueField O)] {π : O} (hπ : Irreducible π) {n N v : ℕ} (hv : v < N) :
    Nat.card (redDepthPairSet O π n N v) * residueCard O ^ (v + n)
      = zed (ResidueField O) n v * residueCard O ^ (n * (2 * N - 1)) := by
  classical
  haveI : Fintype (Coeff O n N) := Fintype.ofFinite _
  have hq : (Fintype.card (ResidueField O)) = residueCard O :=
    Nat.card_eq_fintype_card.symm
  rw [card_redDepthPairSet_eq_sum_strata hπ hv, Finset.sum_mul]
  have hterm : ∀ r : Fin n → ResidueField O,
      r ∈ (Finset.univ : Finset (Fin n → ResidueField O)) →
      Nat.card (stratumDepthSet O n N v (monicPoly r)) * residueCard O ^ (v + n)
        = PowerSeries.coeff v (patRate (residueCard O) (patternOf (monicPoly r)))
            * residueCard O ^ (n * (2 * N - 1)) :=
    fun r _ => card_stratumDepthSet_eq_patRate (by omega) hv (monicPoly_monic r)
      (monicPoly_natDegree r)
  rw [Finset.sum_congr rfl hterm, ← Finset.sum_mul]
  congr 1
  unfold zed
  rw [hq]
  refine Finset.sum_nbij' (i := fun r : Fin n → ResidueField O => monicPoly r)
    (j := fun g : Polynomial (ResidueField O) => fun i : Fin n => g.coeff (i : ℕ))
    ?_ ?_ ?_ ?_ ?_
  · intro r _
    exact mem_monicFinset_iff.mpr ⟨monicPoly_monic r, monicPoly_natDegree r⟩
  · intro g _
    exact Finset.mem_univ _
  · intro r _
    funext i
    rw [monicPoly_coeff_lt r i.isLt]
  · intro g hg
    obtain ⟨hm, hd⟩ := mem_monicFinset_iff.mp hg
    exact monicPoly_coeff_eq_self' hm hd
  · intro r _
    rfl

end Census

/-! ## §5 — the polynomiality of the census -/

section Polynomiality

/-- **The pattern numerator polynomial**: the `ℚ[X]`-coefficient mirror of `patRate` —
the coefficient of the `PowerSeries (Polynomial ℚ)` product of `primoPoly` series. -/
def patNum (lam : Multiset (ℕ × ℕ)) (v : ℕ) : Polynomial ℚ :=
  PowerSeries.coeff v
    ((lam.map (fun de => PowerSeries.mk (fun w => primoPoly de.1 de.2 w))).prod)

/-- The cast bridge for the pattern convolution: `patRate` coefficients at `q ≥ 1` are
`patNum` evaluations. -/
theorem patRate_cast {q : ℕ} (hq : 1 ≤ q) (lam : Multiset (ℕ × ℕ)) (v : ℕ) :
    ((PowerSeries.coeff v (patRate q lam) : ℕ) : ℚ) = (patNum lam v).eval (q : ℚ) := by
  have h1 : ((PowerSeries.coeff v (patRate q lam) : ℕ) : ℚ)
      = PowerSeries.coeff v (PowerSeries.map (Nat.castRingHom ℚ) (patRate q lam)) := by
    rw [PowerSeries.coeff_map]
    rfl
  have h2 : (patNum lam v).eval (q : ℚ)
      = PowerSeries.coeff v (PowerSeries.map (Polynomial.evalRingHom ((q : ℕ) : ℚ))
          ((lam.map (fun de => PowerSeries.mk (fun w => primoPoly de.1 de.2 w))).prod)) := by
    rw [PowerSeries.coeff_map]
    rfl
  rw [h1, h2]
  congr 1
  unfold patRate
  rw [map_multiset_prod, map_multiset_prod, Multiset.map_map, Multiset.map_map]
  refine congrArg Multiset.prod (Multiset.map_congr rfl fun de _ => ?_)
  ext w
  simp only [Function.comp_apply, PowerSeries.coeff_map, PowerSeries.coeff_mk,
    Polynomial.coe_evalRingHom, eq_natCast]
  exact primo_cast hq de.1 de.2 w

/-- The chosen fiber polynomial at the empty avoidance profile. -/
def fiberPoly (lam : Multiset (ℕ × ℕ)) (n : ℕ) : Polynomial ℚ :=
  (exists_fiberPoly lam n (fun _ => 0)).choose

/-- The defining property of `fiberPoly`, at `A = ∅`. -/
theorem fiberPoly_spec {lam : Multiset (ℕ × ℕ)} {n : ℕ}
    (hlam : ∀ de ∈ lam, 1 ≤ de.1 ∧ 1 ≤ de.2)
    (K : Type) [Field K] [Fintype K] :
    (((monicFinset K n).filter (fun g => patternOf g = lam)).card : ℚ)
      = (fiberPoly lam n).eval ((Fintype.card K : ℚ)) := by
  classical
  have hspec := (exists_fiberPoly lam n (fun _ => 0)).choose_spec hlam K ∅
    (fun p hp => absurd hp (Finset.notMem_empty p))
    (fun δ => by rw [Finset.filter_empty, Finset.card_empty])
  rw [fiberPoly, ← hspec]
  congr 2
  unfold Uniformity.Density.IFCG17.fiberFinset
  refine (Finset.filter_congr fun g _ => ?_).symm
  constructor
  · rintro ⟨hpat, -⟩
    exact hpat
  · intro hpat
    exact ⟨hpat, fun p hp => absurd hp (Finset.notMem_empty p)⟩

/-- **The general census polynomial**: `Zpoly n v` evaluates to `zed K n v` at every
finite field — the type-grouped assembly. -/
def Zpoly (n v : ℕ) : Polynomial ℚ :=
  ∑ lam ∈ patternUniverse n, fiberPoly lam n * patNum lam v

/-- ★★ **The census is polynomial in `q`**: the type grouping fires. -/
theorem zed_cast (K : Type) [Field K] [Fintype K] (n v : ℕ) :
    ((zed K n v : ℕ) : ℚ) = (Zpoly n v).eval ((Fintype.card K : ℚ)) := by
  classical
  have hq1 : 1 ≤ Fintype.card K := Fintype.card_pos
  unfold zed Zpoly
  rw [Polynomial.eval_finsetSum,
    ← Finset.sum_fiberwise_of_maps_to
      (fun g hg => patternOf_mem_patternUniverse (mem_monicFinset_iff.mp hg).1
        (mem_monicFinset_iff.mp hg).2)
      (fun g => PowerSeries.coeff v (patRate (Fintype.card K) (patternOf g))),
    Nat.cast_sum]
  refine Finset.sum_congr rfl fun lam hlam => ?_
  have hconst : ∀ g ∈ (monicFinset K n).filter (fun g => patternOf g = lam),
      PowerSeries.coeff v (patRate (Fintype.card K) (patternOf g))
        = PowerSeries.coeff v (patRate (Fintype.card K) lam) :=
    fun g hg => by rw [(Finset.mem_filter.mp hg).2]
  rw [Finset.sum_congr rfl hconst, Finset.sum_const, smul_eq_mul, Nat.cast_mul,
    fiberPoly_spec (one_le_of_mem_patternUniverse hlam) K,
    patRate_cast hq1 lam v, Polynomial.eval_mul]

end Polynomiality

/-! ## §6 — ★★★ the `ZcURLim`, fired at every `(n₁, n₂)` -/

section URLim

/-- ★★ **THE REDUCED DIAGONAL DENSITY `ZcURLim` AT EVERY `n`, OUTRIGHT**: the
normalized family is eventually constant with value `zed/q^{v+2n}` — numerator
`Zpoly n v`, denominator `X^{v+2n}`.  (No positivity of `n` needed — the `n = 0`
census degenerates gracefully.) -/
theorem zcURLim_redDiag (n v : ℕ) :
    ZcURLim (fun O _ _ _ _ _ π M =>
      ((Nat.card (redDepthPairSet O π n M v) : ℕ) : ℝ)
        / ((residueCard O : ℕ) : ℝ) ^ (2 * n * M)) := by
  refine ⟨Zpoly n v, Polynomial.X ^ (v + 2 * n),
    pow_ne_zero _ Polynomial.X_ne_zero, ?_⟩
  intro O _ _ _ _ _
  haveI : Fintype (ResidueField O) := Fintype.ofFinite _
  have hq2 : 2 ≤ residueCard O := two_le_residueCard O
  have hq0 : ((residueCard O : ℕ) : ℚ) ≠ 0 := by
    exact_mod_cast (by omega : residueCard O ≠ 0)
  have hqR : (0 : ℝ) < ((residueCard O : ℕ) : ℝ) := by
    exact_mod_cast (by omega : 0 < residueCard O)
  have hden : (Polynomial.X ^ (v + 2 * n) : Polynomial ℚ).eval ((residueCard O : ℕ) : ℚ)
      = ((residueCard O : ℕ) : ℚ) ^ (v + 2 * n) := by
    rw [Polynomial.eval_pow, Polynomial.eval_X]
  refine ⟨by rw [hden]; exact pow_ne_zero _ hq0, ?_⟩
  intro π hπ
  have hqcard : Fintype.card (ResidueField O) = residueCard O :=
    Nat.card_eq_fintype_card.symm
  have hval : (((Zpoly n v).eval ((residueCard O : ℕ) : ℚ)
        / (Polynomial.X ^ (v + 2 * n) : Polynomial ℚ).eval ((residueCard O : ℕ) : ℚ)
          : ℚ) : ℝ)
      = ((zed (ResidueField O) n v : ℕ) : ℝ)
        / ((residueCard O : ℕ) : ℝ) ^ (v + 2 * n) := by
    rw [hden]
    have hz := zed_cast (ResidueField O) n v
    rw [hqcard] at hz
    rw [← hz]
    push_cast
    ring
  rw [hval]
  refine Filter.Tendsto.congr' ?_ tendsto_const_nhds
  refine Filter.eventually_atTop.mpr ⟨v + 1, fun M hM => ?_⟩
  simp only []
  have hcensus := card_redDepthPairSet_general (O := O) (n := n) hπ (by omega : v < M)
  have hcensus' : Nat.card (redDepthPairSet O π n M v) * residueCard O ^ (v + 2 * n)
      = zed (ResidueField O) n v * residueCard O ^ (2 * n * M) := by
    have h1 := congrArg (fun x => x * residueCard O ^ n) hcensus
    rw [mul_assoc, ← pow_add, mul_assoc, ← pow_add] at h1
    have e1 : v + n + n = v + 2 * n := by ring
    have e2 : n * (2 * M - 1) + n = 2 * n * M := by
      obtain ⟨m, rfl⟩ : ∃ m, M = m + 1 := ⟨M - 1, by omega⟩
      have h2m : 2 * (m + 1) - 1 = 2 * m + 1 := by omega
      rw [h2m]
      ring
    rw [e1, e2] at h1
    exact h1
  have hcast : (Nat.card (redDepthPairSet O π n M v) : ℝ)
        * ((residueCard O : ℕ) : ℝ) ^ (v + 2 * n)
      = ((zed (ResidueField O) n v : ℕ) : ℝ)
        * ((residueCard O : ℕ) : ℝ) ^ (2 * n * M) := by
    exact_mod_cast hcensus'
  rw [div_eq_div_iff (ne_of_gt (pow_pos hqR _)) (ne_of_gt (pow_pos hqR _))]
  linarith [hcast]

/-- ★★★ **THE DEPTH-DENSITY `ZcURLim` AT EVERY `(n₁, n₂)`** — VCL's axis 1, closed:
the general diagonal census through IFCG61's reduced-to-general transport (and the
swap for `n₁ > n₂`). -/
theorem zcURLim_depthDensity {n₁ n₂ : ℕ} (h1 : 0 < n₁) (h2 : 0 < n₂) (v : ℕ) :
    ZcURLim (fun O _ _ _ _ _ π M =>
      ((Nat.card (depthPairSet O π n₁ n₂ M v) : ℕ) : ℝ)
        / ((residueCard O : ℕ) : ℝ) ^ ((n₁ + n₂) * M)) := by
  rcases le_total n₁ n₂ with hle | hle
  · exact zcURLim_depthDensity_of_reduced h1 hle (zcURLim_redDiag n₁ v)
  · have h := zcURLim_depthDensity_of_reduced h2 hle (zcURLim_redDiag n₂ v)
    refine h.congr ?_
    intro O _ _ _ _ _ π hπ M
    rw [card_depthPairSet_swap, Nat.add_comm n₂ n₁]

/-- Lean-internal cross-check: the `(2,2)` instance of the general theorem is NA22's
`zcURLim_depthDensity_two_two` statement, verbatim. -/
example (v : ℕ) :
    ZcURLim (fun O _ _ _ _ _ π M =>
      ((Nat.card (depthPairSet O π 2 2 M v) : ℕ) : ℝ)
        / ((residueCard O : ℕ) : ℝ) ^ ((2 + 2) * M)) :=
  zcURLim_depthDensity (by omega) (by omega) v

end URLim

/-! ## §7 — the regression: the general assembly reproduces NA22's duo law at `n = 2` -/

section Regression

variable {K : Type*} [Field K]

/-- The pattern of a monic irreducible: the single block `(deg, 1)`. -/
theorem patternOf_irreducible {p : Polynomial K} (hm : p.Monic) (hirr : Irreducible p) :
    patternOf p = {(p.natDegree, 1)} := by
  have h := patternOf_pow_mul hm hirr le_rfl one_ne_zero
    (fun hdvd => hirr.not_isUnit (isUnit_of_dvd_one hdvd))
  rw [pow_one, mul_one] at h
  rw [h, patternOf_one, Multiset.cons_zero]

/-- The pattern of a squared monic linear: the single block `(1, 2)`. -/
theorem patternOf_sq_linear (a : K) :
    patternOf (((X : Polynomial K) - C a) ^ 2) = {(1, 2)} := by
  have h := patternOf_pow_mul (Polynomial.monic_X_sub_C a)
    (Polynomial.irreducible_X_sub_C a) (by omega : 1 ≤ 2) one_ne_zero
    (fun hdvd => (Polynomial.irreducible_X_sub_C a).not_isUnit (isUnit_of_dvd_one hdvd))
  rw [mul_one] at h
  rw [h, patternOf_one, Polynomial.natDegree_X_sub_C, Multiset.cons_zero]

/-- The pattern of a split quadratic: two blocks `(1, 1)`. -/
theorem patternOf_split {a b : K} (hab : a ≠ b) :
    patternOf (((X : Polynomial K) - C a) * (X - C b)) = (1, 1) ::ₘ {(1, 1)} := by
  have hb : patternOf ((X : Polynomial K) - C b) = {(1, 1)} := by
    have h := patternOf_irreducible (Polynomial.monic_X_sub_C b)
      (Polynomial.irreducible_X_sub_C b)
    rwa [Polynomial.natDegree_X_sub_C] at h
  have hnd : ¬ ((X : Polynomial K) - C a) ∣ (X - C b) := by
    intro hdvd
    have heq := eq_of_monic_of_associated (Polynomial.monic_X_sub_C a)
      (Polynomial.monic_X_sub_C b)
      ((Polynomial.irreducible_X_sub_C a).associated_of_dvd
        (Polynomial.irreducible_X_sub_C b) hdvd)
    have hev := congrArg (Polynomial.eval a) heq
    simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C,
      sub_self] at hev
    exact hab (sub_eq_zero.mp hev.symm)
  have h := patternOf_pow_mul (Polynomial.monic_X_sub_C a)
    (Polynomial.irreducible_X_sub_C a) le_rfl (Polynomial.monic_X_sub_C b).ne_zero hnd
  rw [pow_one] at h
  rw [h, hb, Polynomial.natDegree_X_sub_C]

/-- The pattern-rate coefficient of a single block is the `primo` value. -/
theorem coeff_patRate_singleton (q δ e v : ℕ) :
    PowerSeries.coeff v (patRate q {(δ, e)}) = primo q δ e v := by
  unfold patRate
  rw [Multiset.map_singleton, Multiset.prod_singleton, PowerSeries.coeff_mk]

/-- The pattern-rate coefficient of the split pattern: the flat binary convolution
`(v+1)(q−1)²`. -/
theorem coeff_patRate_split (q v : ℕ) :
    PowerSeries.coeff v (patRate q ((1, 1) ::ₘ {(1, 1)})) = (v + 1) * (q - 1) ^ 2 := by
  unfold patRate
  rw [Multiset.map_cons, Multiset.prod_cons, Multiset.map_singleton,
    Multiset.prod_singleton, PowerSeries.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  have hterm : ∀ w ∈ Finset.range (v + 1),
      PowerSeries.coeff w (PowerSeries.mk (fun t => primo q 1 1 t))
          * PowerSeries.coeff (v - w) (PowerSeries.mk (fun t => primo q 1 1 t))
        = (q - 1) * (q - 1) := by
    intro w _
    rw [PowerSeries.coeff_mk, PowerSeries.coeff_mk, primo_one Nat.one_pos,
      primo_one Nat.one_pos, if_pos (one_dvd _), if_pos (one_dvd _), pow_one]
  rw [Finset.sum_congr rfl hterm, Finset.sum_const, Finset.card_range, smul_eq_mul]
  ring

/-- ★ **The `n = 2` regression**: the general census numerator collapses to NA22's
independently-derived duo law — `2·zed(K,2,v) = duo(#K, v)` over every finite field,
hence the five battery-verified IGV rows are inherited verbatim. -/
theorem two_mul_zed_two (K : Type*) [Field K] [Fintype K] (v : ℕ) :
    2 * zed K 2 v = duo (Fintype.card K) v := by
  classical
  -- reindex the census numerator over coefficient vectors
  have hreindex : ∑ r : Fin 2 → K,
      PowerSeries.coeff v (patRate (Fintype.card K) (patternOf (monicPoly r)))
        = zed K 2 v := by
    unfold zed
    refine Finset.sum_nbij' (i := fun r : Fin 2 → K => monicPoly r)
      (j := fun g : Polynomial K => fun i : Fin 2 => g.coeff (i : ℕ)) ?_ ?_ ?_ ?_ ?_
    · intro r _
      exact mem_monicFinset_iff.mpr ⟨monicPoly_monic r, monicPoly_natDegree r⟩
    · intro g _
      exact Finset.mem_univ _
    · intro r _
      funext i
      rw [monicPoly_coeff_lt r i.isLt]
    · intro g hg
      obtain ⟨hm, hd⟩ := mem_monicFinset_iff.mp hg
      exact monicPoly_coeff_eq_self' hm hd
    · intro r _
      rfl
  rw [← hreindex,
    ← Finset.sum_filter_add_sum_filter_not Finset.univ
      (fun r : Fin 2 → K => Irreducible (monicPoly r))]
  -- the reducible genre is the split ∪ double partition (NA22's §1 exhaustion)
  have hunion : Finset.univ.filter (fun r : Fin 2 → K => ¬ Irreducible (monicPoly r))
      = (Finset.univ.filter (fun r : Fin 2 → K =>
          ∃ a b : K, a ≠ b ∧ monicPoly r = (X - C a) * (X - C b)))
        ∪ (Finset.univ.filter
            (fun r : Fin 2 → K => ∃ a : K, monicPoly r = (X - C a) ^ 2)) := by
    ext r
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
    constructor
    · exact split_or_dbl_of_not_irreducible
    · rintro (⟨a, b, hab, hfac⟩ | ⟨a, hfac⟩)
      · rw [hfac]; exact not_irreducible_mul_linear a b
      · rw [hfac]; exact not_irreducible_sq_linear a
  have hdisj : Disjoint
      (Finset.univ.filter (fun r : Fin 2 → K =>
        ∃ a b : K, a ≠ b ∧ monicPoly r = (X - C a) * (X - C b)))
      (Finset.univ.filter
        (fun r : Fin 2 → K => ∃ a : K, monicPoly r = (X - C a) ^ 2)) := by
    rw [Finset.disjoint_left]
    intro r hrA hrB
    rw [Finset.mem_filter] at hrA hrB
    obtain ⟨-, a, b, hab, hfac⟩ := hrA
    obtain ⟨-, c, hfac'⟩ := hrB
    exact split_ne_dbl hab (hfac.symm.trans hfac')
  rw [hunion, Finset.sum_union hdisj]
  -- per-genre constant coefficient values
  have hI : ∀ r ∈ Finset.univ.filter (fun r : Fin 2 → K => Irreducible (monicPoly r)),
      PowerSeries.coeff v (patRate (Fintype.card K) (patternOf (monicPoly r)))
        = primo (Fintype.card K) 2 1 v := by
    intro r hr
    rw [Finset.mem_filter] at hr
    have hpat := patternOf_irreducible (monicPoly_monic r) hr.2
    rw [monicPoly_natDegree] at hpat
    rw [hpat, coeff_patRate_singleton]
  have hS : ∀ r ∈ Finset.univ.filter (fun r : Fin 2 → K =>
      ∃ a b : K, a ≠ b ∧ monicPoly r = (X - C a) * (X - C b)),
      PowerSeries.coeff v (patRate (Fintype.card K) (patternOf (monicPoly r)))
        = (v + 1) * (Fintype.card K - 1) ^ 2 := by
    intro r hr
    rw [Finset.mem_filter] at hr
    obtain ⟨-, a, b, hab, hfac⟩ := hr
    rw [hfac, patternOf_split hab, coeff_patRate_split]
  have hD : ∀ r ∈ Finset.univ.filter
      (fun r : Fin 2 → K => ∃ a : K, monicPoly r = (X - C a) ^ 2),
      PowerSeries.coeff v (patRate (Fintype.card K) (patternOf (monicPoly r)))
        = primo (Fintype.card K) 1 2 v := by
    intro r hr
    rw [Finset.mem_filter] at hr
    obtain ⟨-, a, hfac⟩ := hr
    rw [hfac, patternOf_sq_linear, coeff_patRate_singleton]
  rw [Finset.sum_congr rfl hI, Finset.sum_congr rfl hS, Finset.sum_congr rfl hD,
    Finset.sum_const, Finset.sum_const, Finset.sum_const]
  simp only [smul_eq_mul]
  -- fire NA22's doubled genre counts and close
  have hSQ : 2 * ((Finset.univ.filter (fun r : Fin 2 → K =>
        ∃ a b : K, a ≠ b ∧ monicPoly r = (X - C a) * (X - C b))).card
          * ((v + 1) * (Fintype.card K - 1) ^ 2))
      = (Fintype.card K ^ 2 - Fintype.card K)
          * ((v + 1) * (Fintype.card K - 1) ^ 2) := by
    rw [← mul_assoc, two_mul_card_splitVecs]
  have hIQ : 2 * ((Finset.univ.filter
        (fun r : Fin 2 → K => Irreducible (monicPoly r))).card
          * primo (Fintype.card K) 2 1 v)
      = (Fintype.card K ^ 2 - Fintype.card K) * primo (Fintype.card K) 2 1 v := by
    rw [← mul_assoc, two_mul_card_inertVecs]
  rw [mul_add, mul_add, hSQ, hIQ, card_dblVecs]
  unfold Uniformity.Density.IFCG68.duo
  ring

end Regression

end Uniformity.Density.IFCG70

end

/-! ## AXCHECK FOOTER — EVERY row expects PURE Lean core
`{propext, Classical.choice, Quot.sound}`.  B.42, the C.33 cites, and
`AX_cellRecursion` must NOT occur. -/
#print axioms Uniformity.Density.IFCG70.primo_cast
#print axioms Uniformity.Density.IFCG70.card_stratumDepthSet_prod
#print axioms Uniformity.Density.IFCG70.card_stratumDepthSet_eq_patRate
#print axioms Uniformity.Density.IFCG70.exists_fiberPoly
#print axioms Uniformity.Density.IFCG70.card_redDepthPairSet_general
#print axioms Uniformity.Density.IFCG70.zed_cast
#print axioms Uniformity.Density.IFCG70.zcURLim_redDiag
#print axioms Uniformity.Density.IFCG70.zcURLim_depthDensity
#print axioms Uniformity.Density.IFCG70.two_mul_zed_two
