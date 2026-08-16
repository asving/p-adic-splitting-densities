/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapH.H124b
import Uniformity.ChapH.H95
import Uniformity.Density.CoveringMenus

/-!
# Uniformity.ChapH.H124c — H.124c: the assembly, `inductionPackage_of_clusterRates`

**Chapter H, NODE H.124** [def+theorem] (`blueprint/CHAP-H_general_induction.md` §17.3 — the T-1
completion layer, dated extension 2026-08-16; provenance OM-2 §4's terminal display
`inductionStep`, *"T-1's honest conditional Lean form — the reduction, never the theorem"*;
sources `EFF.GENIND.13` (`P(k)`), `EFF.GENIND.54` (Step 1), `EFF.GENIND.57` (the `(A2)`
assembly), `EFF.GENIND.60` (Step 5 — NOT re-proved here; H.98 fires it)).
**PART c of the mandated three-way split** (`H124` / `H124b` / `H124c`): the theorem half.

```
theorem inductionPackage_of_clusterRates (n : ℕ) (hn : 2 ≤ n)
    (ih : ∀ k, 2 ≤ k → k < n → InductionPackage k)
    (hfc : ∃ (K : ℝ) (B c : ℕ), 0 ≤ K ∧ FullClusterRateBound n K B c) :
    InductionPackage n
```

## ⚠ WHAT THIS NODE IS NOT (the H.98 fence, restated)

This is **NOT** `THEOREM GENIND.B`.  The full-cluster rate is CARRIED in `hfc`, never claimed.
Its dischargers, by scope: `d = 1, m ≤ 3` — H.122 + H.123; `d = 1, m ≥ 4` — the CS mass rides
`StageInterface` + H.72, gated `HYP.36` / `HYP.32` / `HYP.33` / `HYP.30` (plus `HYP.81` at
`μ ≥ 3` and `HYP.82` at `n ≥ 8`); `d ≥ 2` — the leaf reads are `B-BOX-1`-gated.  Those rows are
the NAMED RESIDUAL of the T-1 layer, and they are the section's recorded CONDITIONALITY EDGES
`BP.H.124 → HYP.36 / HYP.81 / HYP.82`.  Nothing in this file discharges any of them.

## The proof, in words (the blueprint's five steps)

1. **Menu clause.**  `exists_coveringMenu` (S-0, CN-22) — nothing to do.
2. **Stratify.**  H.100's level-0 strata partition `Coeff O n M`, and H.124a's `stratumPoly` makes
   the partition the fibre decomposition of a function, so the census is a `Finset` fibre sum.
3. **Per stratum, induct on the number of irreducible factors.**  H.124b's dichotomy splits a
   monic residue polynomial into `p ^ m` or a coprime product.  At `m = 1` the stratum is DECIDED
   outright (H.124a's one-factor base, undecided count `0`); at `m ≥ 2` it is a FULL-CLUSTER
   stratum — supplied by `hfc` at the top degree `n`, and by `(ih)` below it (H.124b's
   `stratum_le_of_global` clears `undecidedSeq`'s normalisation, at the price `c ↦ c + i`).  On a
   coprime product H.124b's peel makes the per-stratum RATIOS ADD.
4. **Sum over strata.**  The strata are pairwise disjoint, so their totals sum to at most
   `q ^ (n M)`; the per-stratum ratio is the SAME for every stratum, so the sum telescopes into
   one global rate with no `q`-dependent loss.
5. **Package.**  `⟨K, B, c, …⟩` with `RateSpecies`' `M ≥ 1` guard inherited from the per-stratum
   `M ≥ 1` guards.  The constants are assembled OUTSIDE the `∀ O` telescope — the whole content
   of "independent of `O`" (`InductionPackage`'s quantifier shape).

The strengthening that makes step 3 an ordinary `Nat` induction is `StratumRateUpTo j K B c`:
ONE constant triple valid at EVERY degree `≤ j`.  Each step adds at most one new triple (the
full-cluster one at the new degree) and doubles the coefficient (the two-factor peel), so the
maxima stay finite and are taken outside `∀ O`.

DEPENDS: H.95 (`InductionPackage`), H.124a (`FullClusterRateBound`, `stratumPoly`, the one-factor
base), H.124b (the census, the peel, the dichotomy, the IH import), H.63 (through H.124b), H.66
(`RateSpecies.mono`, through H.124b's `rate_const_le`) · landed `exists_coveringMenu` (CN-22),
`card_coeff`, `undecidedSet`, `undecidedCount`, `undecidedSeq`, `residueCard`,
`two_le_residueCard`.

## Status

Sorry-free, axiom-free (Lean core only); footprints printed at the end of the file.
-/

set_option linter.style.longLine false

namespace Uniformity.Density

open IsLocalRing Polynomial

namespace Induction

/-! ## 1. The strengthened induction predicate (non-blueprint auxiliary) -/

/-- **Auxiliary (non-blueprint).** ONE constant triple `(K, B, c)`, chosen outside `∀ O`, bounding
the per-stratum undecided count at EVERY degree `1 ≤ i ≤ j`.  Strengthening the blueprint's
per-degree statement to a "uniform over all degrees `≤ j`" statement is what turns step 3's
"induct on the number of irreducible factors" into an ordinary induction on `j`. -/
def StratumRateUpTo (j : ℕ) (K : ℝ) (B c : ℕ) : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [Finite (IsLocalRing.ResidueField O)],
    ∀ (i : ℕ), 1 ≤ i → i ≤ j → ∀ g : Polynomial (IsLocalRing.ResidueField O), g.Monic →
      g.natDegree = i → ∀ M, 1 ≤ M →
        (Nat.card ((undecidedSet O i M ∩ levelZeroStratum O i M g : Set (Coeff O i M))) : ℝ)
          ≤ K * (M : ℝ) ^ B * ((residueCard O : ℝ) ^ (M - c))⁻¹
            * (Nat.card (levelZeroStratum O i M g) : ℝ)

/-! ## 2. The induction (blueprint PROOF step 3) -/

/-- **Step 3.**  The per-stratum rate exists at every degree `≤ n`, with ONE constant triple.
`hfc` is consumed only at the top degree; below it the induction hypothesis `ih` does the work,
and at `m = 1` H.124a's one-factor base does. -/
theorem exists_stratumRateUpTo (n : ℕ) (hn : 2 ≤ n)
    (ih : ∀ k, 2 ≤ k → k < n → InductionPackage k)
    {K₀ : ℝ} {B₀ c₀ : ℕ} (hK₀ : 0 ≤ K₀) (hfc : FullClusterRateBound n K₀ B₀ c₀) :
    ∀ j, j ≤ n → ∃ (K : ℝ) (B c : ℕ), 1 ≤ K ∧ StratumRateUpTo j K B c := by
  intro j
  induction j with
  | zero =>
    intro _
    refine ⟨1, 0, 0, le_rfl, ?_⟩
    intro O _ _ _ _ _ i h1i hi0 g _ _ M _
    exact absurd hi0 (by omega)
  | succ j ihj =>
    intro hj
    obtain ⟨K, B, c, hK, hprev⟩ := ihj (by omega)
    -- the FULL-CLUSTER triple at the new degree `j + 1`
    obtain ⟨K₂, B₂, c₂, hK₂, hfull⟩ :
        ∃ (K₂ : ℝ) (B₂ c₂ : ℕ), 1 ≤ K₂ ∧
          ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
            [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
            [Finite (IsLocalRing.ResidueField O)],
            ∀ (p : Polynomial (IsLocalRing.ResidueField O)) (m d : ℕ), 2 ≤ m → m * d = j + 1 →
              p.Monic → Irreducible p → p.natDegree = d → ∀ M, 1 ≤ M →
                (Nat.card ((undecidedSet O (j + 1) M ∩ levelZeroStratum O (j + 1) M (p ^ m) :
                    Set (Coeff O (j + 1) M))) : ℝ)
                  ≤ K₂ * (M : ℝ) ^ B₂ * ((residueCard O : ℝ) ^ (M - c₂))⁻¹
                    * (Nat.card (levelZeroStratum O (j + 1) M (p ^ m)) : ℝ) := by
      rcases Nat.lt_or_ge (j + 1) 2 with hsmall | hbig
      · -- degree `1`: there is no `m ≥ 2` factorisation at all, the clause is vacuous
        refine ⟨1, 0, 0, le_rfl, ?_⟩
        intro O _ _ _ _ _ p m d hm hmd _ _ _ M _
        exfalso
        rcases Nat.eq_zero_or_pos d with hd0 | hd0
        · rw [hd0, Nat.mul_zero] at hmd; omega
        · have h2 : 2 ≤ j + 1 := by
            calc (2 : ℕ) = 2 * 1 := by ring
              _ ≤ m * d := Nat.mul_le_mul hm hd0
              _ = j + 1 := hmd
          omega
      · rcases eq_or_lt_of_le hj with heq | hlt
        · -- the TOP degree: this is exactly the carried hypothesis `hfc`
          subst heq
          refine ⟨max K₀ 1, B₀, c₀, le_max_right _ _, ?_⟩
          intro O _ _ _ _ _ p m d hm hmd hpm hpi hpd M hM
          refine (hfc O p m d hm hmd hpm hpi hpd M hM).trans
            (mul_le_mul_of_nonneg_right ?_ (Nat.cast_nonneg _))
          exact rate_const_le (two_le_residueCard O) hK₀ (le_max_left _ _) le_rfl le_rfl hM
        · -- below the top degree: the induction hypothesis, imported per stratum
          obtain ⟨K₁, B₁, c₁, hK₁, hpkg⟩ := ih (j + 1) hbig hlt
          refine ⟨max K₁ 1, B₁, c₁ + (j + 1), le_max_right _ _, ?_⟩
          intro O _ _ _ _ _ p m d hm hmd hpm hpi hpd M hM
          have hrate : undecidedSeq O (j + 1) M
              ≤ max K₁ 1 * (M : ℝ) ^ B₁ * ((residueCard O : ℝ) ^ (M - c₁))⁻¹ :=
            ((hpkg O).2 M hM).trans
              (rate_const_le (two_le_residueCard O) hK₁ (le_max_left _ _) le_rfl le_rfl hM)
          refine stratum_le_of_global hM (hpm.pow m) ?_ (le_max_right _ _) hrate
          rw [hpm.natDegree_pow, hpd, hmd]
    -- the new constants
    have hK'1 : (1 : ℝ) ≤ max (2 * K) K₂ := le_trans (by linarith) (le_max_left _ _)
    have hK'0 : (0 : ℝ) ≤ max (2 * K) K₂ := le_trans zero_le_one hK'1
    refine ⟨max (2 * K) K₂, max B B₂, max c c₂, hK'1, ?_⟩
    intro O _ _ _ _ _ i h1i hij g hg hgd M hM
    have hq2 := two_le_residueCard O
    have hTnn : (0 : ℝ) ≤ (Nat.card (levelZeroStratum O i M g) : ℝ) := Nat.cast_nonneg _
    rcases Nat.lt_or_ge i (j + 1) with hlt | hge
    · -- a degree already covered by the previous triple
      refine (hprev O i h1i (by omega) g hg hgd M hM).trans
        (mul_le_mul_of_nonneg_right ?_ hTnn)
      exact rate_const_le hq2 (by linarith) (le_trans (by linarith) (le_max_left _ _))
        (le_max_left _ _) (le_max_left _ _) hM
    · -- the new degree
      have hi : i = j + 1 := by omega
      subst hi
      rcases monic_prime_pow_or_coprime_split hg hgd h1i with
        ⟨p, m, d, hpm, hpi, hm1, hpd, hmd, hgp⟩ |
        ⟨g₁, g₂, n₁, n₂, hg₁, hg₂, hn₁, hn₂, hd₁, hd₂, hsum, hcop, hgprod⟩
      · rcases Nat.lt_or_ge m 2 with hmlt | hm2
        · -- `m = 1`: H.124a's one-factor base — the stratum is DECIDED outright
          have hm : m = 1 := by omega
          subst hm
          rw [pow_one] at hgp
          have hgi : Irreducible g := hgp ▸ hpi
          have hempty := undecided_inter_levelZeroStratum_irreducible (O := O) (n := j + 1)
            (N := M) (by omega) hgi
          rw [hempty]
          have hz : (Nat.card ((∅ : Set (Coeff O (j + 1) M))) : ℝ) = 0 := by simp
          rw [hz]
          exact mul_nonneg (rate_value_nonneg hK'0) hTnn
        · -- `m ≥ 2`: the full-cluster clause
          subst hgp
          refine (hfull O p m d hm2 hmd hpm hpi hpd M hM).trans
            (mul_le_mul_of_nonneg_right ?_ (Nat.cast_nonneg _))
          exact rate_const_le hq2 (by linarith) (le_max_right _ _) (le_max_right _ _)
            (le_max_right _ _) hM
      · -- the coprime peel
        subst hgprod
        have hb₁ := hprev O n₁ hn₁ (by omega) g₁ hg₁ hd₁ M hM
        have hb₂ := hprev O n₂ hn₂ (by omega) g₂ hg₂ hd₂ M hM
        set r : ℝ := K * (M : ℝ) ^ B * ((residueCard O : ℝ) ^ (M - c))⁻¹ with hr
        have hr0 : (0 : ℝ) ≤ r := rate_value_nonneg (by linarith)
        have hpeel := card_undecided_le_of_coprime (O := O) hM hg₁ hg₂ hd₁ hd₂ hcop hr0 hr0 hb₁ hb₂
        rw [← hsum]
        refine hpeel.trans (mul_le_mul_of_nonneg_right ?_ (Nat.cast_nonneg _))
        have h2 : r + r = 2 * K * (M : ℝ) ^ B * ((residueCard O : ℝ) ^ (M - c))⁻¹ := by
          rw [hr]; ring
        rw [h2]
        exact rate_const_le hq2 (by linarith) (le_max_left _ _) (le_max_left _ _)
          (le_max_left _ _) hM

/-! ## 3. Summation over the strata (blueprint PROOF step 4) -/

/-- **Step 4.**  A per-stratum ratio bound with a stratum-independent ratio `r` sums to the global
census bound.  The strata are the fibres of H.124a's `stratumPoly`, hence pairwise disjoint, so
their totals add up to at most the box count `q ^ (n M)` — no `q`-dependent loss enters. -/
theorem undecidedCount_le_of_stratumRate {O : Type*} [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [IsAdicComplete (maximalIdeal O) O] [Finite (ResidueField O)]
    {n M : ℕ} (hM : 1 ≤ M) {r : ℝ} (hr : 0 ≤ r)
    (h : ∀ g : Polynomial (ResidueField O), g.Monic → g.natDegree = n →
      (Nat.card ((undecidedSet O n M ∩ levelZeroStratum O n M g : Set (Coeff O n M))) : ℝ)
        ≤ r * (Nat.card (levelZeroStratum O n M g) : ℝ)) :
    (undecidedCount O n M : ℝ) ≤ r * (residueCard O : ℝ) ^ (n * M) := by
  classical
  haveI : Fintype (Coeff O n M) := Fintype.ofFinite _
  -- the `Finset`/`Set` census bridge
  have hbridge : ∀ (t : Finset (Coeff O n M)) (s : Set (Coeff O n M)),
      (↑t : Set (Coeff O n M)) = s → t.card = Nat.card s := by
    intro t s hts
    rw [Nat.card_coe_set_eq, ← hts, Set.ncard_coe_finset]
  set Ufin : Finset (Coeff O n M) := Finset.univ.filter (fun c => c ∈ undecidedSet O n M)
    with hUdef
  set Bfin : Polynomial (ResidueField O) → Finset (Coeff O n M) :=
    fun g => Finset.univ.filter (fun c => c ∈ levelZeroStratum O n M g) with hBdef
  set S : Finset (Polynomial (ResidueField O)) := Ufin.image (stratumPoly O n M) with hSdef
  -- every label in `S` is monic of degree `n`
  have hSmem : ∀ g ∈ S, g.Monic ∧ g.natDegree = n := by
    intro g hg
    obtain ⟨x, -, rfl⟩ := Finset.mem_image.1 hg
    exact ⟨stratumPoly_monic x, stratumPoly_natDegree x⟩
  -- the three coercion identities
  have hcoeU : (↑Ufin : Set (Coeff O n M)) = undecidedSet O n M := by
    ext c
    simp only [Finset.mem_coe, hUdef, Finset.mem_filter, Finset.mem_univ, true_and]
  have hcoeB : ∀ g, (↑(Bfin g) : Set (Coeff O n M)) = levelZeroStratum O n M g := by
    intro g
    ext c
    simp only [Finset.mem_coe, hBdef, Finset.mem_filter, Finset.mem_univ, true_and]
  have hcoeF : ∀ g, (↑(Ufin.filter (fun c => stratumPoly O n M c = g)) : Set (Coeff O n M))
      = (undecidedSet O n M ∩ levelZeroStratum O n M g : Set (Coeff O n M)) := by
    intro g
    ext c
    simp only [Finset.mem_coe, Finset.mem_filter, hUdef, Finset.mem_univ, true_and,
      Set.mem_inter_iff]
    exact and_congr_right fun _ => (mem_levelZeroStratum_iff_stratumPoly hM g c).symm
  -- the fibrewise decomposition of the undecided census
  have hfiber := Finset.card_eq_sum_card_fiberwise
    (f := stratumPoly O n M) (s := Ufin) (t := S)
    (fun x hx => Finset.mem_image_of_mem _ hx)
  have hUcard : Ufin.card = undecidedCount O n M := by
    rw [hbridge Ufin _ hcoeU, undecidedCount]
  have hcount : undecidedCount O n M
      = ∑ g ∈ S, Nat.card ((undecidedSet O n M ∩ levelZeroStratum O n M g :
          Set (Coeff O n M))) := by
    rw [← hUcard, hfiber]
    exact Finset.sum_congr rfl fun g _ => hbridge _ _ (hcoeF g)
  -- the strata are pairwise disjoint, so their totals fit in the box
  have hdisj : (↑S : Set (Polynomial (ResidueField O))).PairwiseDisjoint Bfin := by
    intro g₁ _ g₂ _ hne
    simp only [Function.onFun]
    refine Finset.disjoint_left.2 fun c hc1 hc2 => hne ?_
    rw [hBdef] at hc1 hc2
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hc1 hc2
    rw [← stratumPoly_eq_of_mem hc1, ← stratumPoly_eq_of_mem hc2]
  have hTsum : ∑ g ∈ S, Nat.card (levelZeroStratum O n M g) ≤ residueCard O ^ (n * M) := by
    have h4 : ∑ g ∈ S, (Bfin g).card = ∑ g ∈ S, Nat.card (levelZeroStratum O n M g) :=
      Finset.sum_congr rfl fun g _ => hbridge _ _ (hcoeB g)
    calc ∑ g ∈ S, Nat.card (levelZeroStratum O n M g)
        = ∑ g ∈ S, (Bfin g).card := h4.symm
      _ = (S.biUnion Bfin).card := (Finset.card_biUnion hdisj).symm
      _ ≤ Fintype.card (Coeff O n M) := Finset.card_le_univ _
      _ = residueCard O ^ (n * M) := by rw [← Nat.card_eq_fintype_card]; exact card_coeff n M
  -- assemble over ℝ
  have hTsumR : ∑ g ∈ S, (Nat.card (levelZeroStratum O n M g) : ℝ)
      ≤ (residueCard O : ℝ) ^ (n * M) := by
    have hcast := (Nat.cast_le (α := ℝ)).2 hTsum
    push_cast at hcast
    exact hcast
  have hcountR : (undecidedCount O n M : ℝ)
      = ∑ g ∈ S, (Nat.card ((undecidedSet O n M ∩ levelZeroStratum O n M g :
          Set (Coeff O n M))) : ℝ) := by
    rw [hcount, Nat.cast_sum]
  calc (undecidedCount O n M : ℝ)
      = ∑ g ∈ S, (Nat.card ((undecidedSet O n M ∩ levelZeroStratum O n M g :
          Set (Coeff O n M))) : ℝ) := hcountR
    _ ≤ ∑ g ∈ S, r * (Nat.card (levelZeroStratum O n M g) : ℝ) :=
        Finset.sum_le_sum fun g hg => h g (hSmem g hg).1 (hSmem g hg).2
    _ = r * ∑ g ∈ S, (Nat.card (levelZeroStratum O n M g) : ℝ) := by rw [Finset.mul_sum]
    _ ≤ r * (residueCard O : ℝ) ^ (n * M) := mul_le_mul_of_nonneg_left hTsumR hr

end Induction

/-! ## 4. The node — the terminal composed reduction -/

/-- **H.124 (theorem half).**  THE REDUCTION, composed: `(IH) + full-cluster rates ⟹ P(n)`.
This is `GENIND.B` Steps 1 + 4h as a single implication — the menu clause is landed
(`exists_coveringMenu`, S-0), the level-0 transport is H.100–H.105, and the full-cluster
hypothesis is exactly where Steps 2–4's cluster layer (H.106–H.123 at `m ≤ 3, d = 1`;
`HYP.36`/`HYP.81`/`HYP.82`- and `B-BOX-1`-gated beyond) discharges.  **NOT `THEOREM GENIND.B`
itself**: the hypothesis is carried, never claimed (the H.98 fence stands). -/
theorem inductionPackage_of_clusterRates (n : ℕ) (hn : 2 ≤ n)
    (ih : ∀ k, 2 ≤ k → k < n → InductionPackage k)
    (hfc : ∃ (K : ℝ) (B c : ℕ), 0 ≤ K ∧ FullClusterRateBound n K B c) :
    InductionPackage n := by
  obtain ⟨K₀, B₀, c₀, hK₀, hfcb⟩ := hfc
  obtain ⟨K, B, c, hK, hrate⟩ := Induction.exists_stratumRateUpTo n hn ih hK₀ hfcb n le_rfl
  refine ⟨K, B, c, by linarith, ?_⟩
  intro O _ _ _ _ _
  refine ⟨exists_coveringMenu O n, ?_⟩
  intro M hM
  have hq0 : (0 : ℝ) < (residueCard O : ℝ) ^ (n * M) := by
    have h1 : (0 : ℕ) < residueCard O := residueCard_pos O
    have h2 : (0 : ℝ) < (residueCard O : ℝ) := by exact_mod_cast h1
    positivity
  have hr0 : (0 : ℝ) ≤ K * (M : ℝ) ^ B * ((residueCard O : ℝ) ^ (M - c))⁻¹ :=
    Induction.rate_value_nonneg (by linarith)
  have hsum := Induction.undecidedCount_le_of_stratumRate (O := O) (n := n) (M := M) hM hr0
    (fun g hg hgd => hrate O n (by omega) le_rfl g hg hgd M hM)
  rw [undecidedSeq, div_le_iff₀ hq0]
  exact hsum

end Uniformity.Density

/-! ## 5. Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Induction.StratumRateUpTo
#print axioms Uniformity.Density.Induction.exists_stratumRateUpTo
#print axioms Uniformity.Density.Induction.undecidedCount_le_of_stratumRate
#print axioms Uniformity.Density.inductionPackage_of_clusterRates

end AxCheck
