/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.OM.Order0Alpha

/-!
# Order0RealDensity — the HONEST real order-0 separable density theorem (σ-keyed), + the
general-prime per-shape density (audit gaps #2/#3, order-0)

**Purpose (additive; nothing existing changes).** The audit
(`uniform-rationality/notes/AUDIT_FINDINGS_2026-07-12.md`) records that the SEPARATE all-orders
capstone `M9.montes_unconditional` is VACUOUS (degenerate `leafOMTypeOfSize`/`shapeMenu` menu,
`Rr = 0` → empty cells → density ≡ 0), while the GENUINE classify path
`Order0.montes_order0_unconditional` is NON-vacuous (real order-0 separable density over the σ-keyed
menu `sepShapesOf n σ`, real `1/4` gate, strictly-positive certified value). This module presents
that genuine result cleanly as THE real order-0 density theorem and pushes it toward the audit's
gaps.

* `montes_order0_realDensity` (§1) — the PRIMARY deliverable. THE clean, σ-keyed statement of "the
  real order-0 separable density = the engine rational function": for every degree `n > 0` and
  factorization type `σ`, the order-0 separable-stratum density function
  `q' ↦ ∑_{T ∈ sepShapesOf n σ} rootCount T q'` is a uniform rational function of `q'`, the real
  normalized fiber counts (at the real prime `realP`) converge to its value at `realP`, AND that
  value equals the order-0 separable menu sum `∑_{T ∈ sepShapesOf n σ} rootCount T realP` (making
  the "density = engine value" reading explicit). The menu IS `sepShapesOf n σ`, so σ is genuinely
  used (gap #3 closed for order-0). This is a re-presentation/strengthening of the banked
  `montes_order0_unconditional`, with the certified value pinned to the honest per-shape sum.

* `montes_order0_certified_density_pos` (§1) — non-vacuity, re-exported: at the INERT degree-2 type
  the certified value is `≥ 1/4 > 0` (the `1/4` gate of `Order0Alpha`), so this density theorem is
  NOT the vacuous constant `0`.

* GENERAL PRIME (gap #2, order-0). The DENSITY VALUE side (`rootCount`) is prime-agnostic
  (`rootCount_sepShape_eval` holds over any finite field). The counting building block
  `card_classify_fiber` is ALSO stated for a general prime `p`. So the per-shape count identity and
  its limit generalize verbatim to `∀ p, p.Prime`:
  * `stratumCount_sepShape_general` — the level-`N` classifier fiber count of `sepShape n lam` over
    `monicBox p N n`, cast to `ℚ`, is `(∏_d C(avail (ZMod p) d, k_d)) · p^((N-1)·n)`.
  * `montes_order0_perShape_density_general` — for every prime `p`, every menu shape
    `T ∈ sepShapesOf n σ`, the normalized general-prime count
    `#{f ∈ monicBox p N n : classify p n N f = T} / p^(nN)` converges to the engine value
    `rootCount T p`. This is `h_node0` for an ARBITRARY prime.
  * `montes_order0_density_general_prime` — the σ-keyed density theorem for a GENERAL prime `p`:
    same rational function, counts at `p` converge to its value at `p`.

  What does NOT generalize additively: the *top-level* real instance (`M9.rawCount`, `M9.realP`,
  `M9.montes_unconditional`, the Witness/Goal wiring) is hardwired to `realP = 2`; changing it would
  ripple through `RealInstance`/`CountingModel`. The general-prime statements here are STANDALONE
  (they name `p` and `B.classify p n` directly, not `M9.rawCount`/`M9.realP`), so no core def moves.

All sorry-free, axiom-clean (`propext, Classical.choice, Quot.sound`) — the `#print axioms` at the
bottom of this file is the machine-checked footprint witness.
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false

namespace LeanUrat.OM.Order0

open LeanUrat LeanUrat.MontesAxiom RatFn Polynomial Filter Topology

/-! ## 1. The primary deliverable: the honest, σ-keyed real order-0 density theorem -/

/-- **`montes_order0_realDensity` — THE real order-0 separable density theorem (σ-keyed).**

For every degree `n > 0` and factorization type `σ`, there is a uniform rational function
`num/den` (denominator nonvanishing at every `q' > 1`) such that:

1. **(density = engine rational function)** the order-0 separable-stratum density function
   `q' ↦ ∑_{T ∈ sepShapesOf n σ} rootCount T q'` EQUALS `num(q')/den(q')` at every `q' > 1`;
2. **(real counts converge)** the real normalized level-`N` classifier fiber counts of the σ-menu
   strata, `(∑_{T ∈ sepShapesOf n σ} stratumCount (rawCount n) T N) / realP^(nN)`, converge as
   `N → ∞` to the rational value `num(realP)/den(realP)`;
3. **(certified value = the honest per-shape sum)** that limit value equals the order-0 separable
   menu sum `∑_{T ∈ sepShapesOf n σ} rootCount T realP` — the genuine engine value at the real prime.

The menu is literally `sepShapesOf n σ` (the partitions whose unramified type is `σ`), so `σ` is
GENUINELY used — this closes audit gap #3 (σ-decoupling) for the order-0 stratum. Non-vacuous:
`montes_order0_certified_density_pos` exhibits a `σ` whose value is `≥ 1/4 > 0`.

This is the honest re-presentation of `montes_order0_unconditional`, additionally pinning the
certified value to the explicit engine per-shape sum (clause 3). NOTHING in the top-level
Witness/Goal wiring or the vacuous `M9.montes_unconditional` is touched. -/
theorem montes_order0_realDensity (n : ℕ) (hn : 0 < n) (σ : FactorizationType) :
    ∃ (num den : Polynomial ℚ), den ≠ 0 ∧
      (∀ q' : ℕ, 1 < q' → den.eval (q' : ℚ) ≠ 0 ∧
        (∑ T ∈ sepShapesOf n σ,
            rootCount M7.cellsOfShapeWF M6.treeSize M7.cellsOfShapeWF_descend T q')
          = num.eval (q' : ℚ) / den.eval (q' : ℚ)) ∧
      Filter.Tendsto
        (fun N => (∑ T ∈ sepShapesOf n σ, M8.stratumCount (M9.rawCount n) T N)
            / (M9.realP : ℚ) ^ (n * N))
        Filter.atTop
        (nhds (num.eval (M9.realP : ℚ) / den.eval (M9.realP : ℚ)))
      ∧ num.eval (M9.realP : ℚ) / den.eval (M9.realP : ℚ)
          = ∑ T ∈ sepShapesOf n σ,
              rootCount M7.cellsOfShapeWF M6.treeSize M7.cellsOfShapeWF_descend T M9.realP := by
  obtain ⟨num, den, hden, hall, hlim⟩ := montes_order0_unconditional n hn σ
  refine ⟨num, den, hden, hall, hlim, ?_⟩
  -- The certified value = num(realP)/den(realP) equals the engine per-shape sum, because the
  -- `∀ q'` rational identity holds at `q' = realP > 1`.
  have hq : 1 < M9.realP := by unfold M9.realP; norm_num
  exact ((hall M9.realP hq).2).symm

/-- **Non-vacuity of `montes_order0_realDensity` (re-exported `1/4` gate).** At `n = 2` and the
INERT factorization type `σ = unramType 2 (indiscrete 2)`, the certified density value is STRICTLY
POSITIVE (`≥ 1/4`). Together with `montes_order0_realDensity` this witnesses, machine-checked, that
the real order-0 density theorem is NOT the audit's vacuous constant-`0` density. -/
theorem montes_order0_certified_density_pos :
    ∃ (num den : Polynomial ℚ), den ≠ 0 ∧
      (∀ q' : ℕ, 1 < q' → den.eval (q' : ℚ) ≠ 0 ∧
        (∑ T ∈ sepShapesOf 2 (unramType 2 (Nat.Partition.indiscrete 2)),
            rootCount M7.cellsOfShapeWF M6.treeSize M7.cellsOfShapeWF_descend T q')
          = num.eval (q' : ℚ) / den.eval (q' : ℚ)) ∧
      (0 : ℚ) < num.eval (M9.realP : ℚ) / den.eval (M9.realP : ℚ) := by
  obtain ⟨num, den, hden, hall, _, hpos⟩ := montes_order0_certified_value_pos
  exact ⟨num, den, hden, hall, hpos⟩

/-! ## 2. General prime: the per-shape count identity and its normalized limit (gap #2, order-0)

Everything here names the prime `p` and `B.classify p n` DIRECTLY (never `M9.rawCount`/`M9.realP`),
so it is standalone — no core def is touched and nothing existing rebuilds. The counting building
block `card_classify_fiber` is already stated for a general prime; we only re-cast it and take the
constant-sequence limit, exactly as `stratumCount_sepShape` / `h_node0_proved` do at `realP`. -/

/-- **The general-prime stratum count** (`card_classify_fiber` re-cast to `ℚ`, ANY prime `p`). For
`0 < N`, `0 < n`, the ℚ-cast level-`N` classifier fiber count of `sepShape n lam` over
`monicBox p N n` is `(∏_d C(avail (ZMod p) d, k_d)) · p^((N-1)·n)`. -/
theorem stratumCount_sepShape_general (p : ℕ) [Fact p.Prime] (n : ℕ) (hn : 0 < n)
    (lam : Nat.Partition n) (N : ℕ) (hN : 0 < N) :
    (Nat.card {f : QuotientBox.monicBox p N n // B.classify p n N f = sepShape n lam} : ℚ)
      = (((∏ d ∈ lam.parts.toFinset,
            (avail (ZMod p) d).choose (lam.parts.count d))
          * p ^ ((N - 1) * n) : ℕ) : ℚ) := by
  rw [card_classify_fiber p n N hN hn lam]

/-- **The general-prime per-shape density limit** (`h_node0` for an ARBITRARY prime `p`). For every
prime `p`, `0 < n`, factorization type `σ`, and menu shape `T ∈ sepShapesOf n σ`, the normalized
general-prime classifier fiber count
`#{f ∈ monicBox p N n : classify p n N f = T} / p^(nN)`
converges as `N → ∞` to the ENGINE value `rootCount T p`. The sequence is CONSTANT for `N ≥ 1`
(`p^((N-1)n)/p^(nN) = p^(-n)`), equal to `(∏_d C(avail (ZMod p) d, k_d))/p^n =
rootCount (sepShape n lam) p` (`rootCount_sepShape_eval` at `F = ZMod p`). This is the audit's
gap-#2 content for the order-0 per-shape density: prime-uniform, not pinned to `realP = 2`. -/
theorem montes_order0_perShape_density_general (p : ℕ) [Fact p.Prime] (n : ℕ) (hn : 0 < n)
    (σ : FactorizationType) :
    ∀ T ∈ sepShapesOf n σ,
      Filter.Tendsto
        (fun N =>
          (Nat.card {f : QuotientBox.monicBox p N n // B.classify p n N f = T} : ℚ)
            / (p : ℚ) ^ (n * N))
        Filter.atTop
        (nhds (rootCount M7.cellsOfShapeWF M6.treeSize M7.cellsOfShapeWF_descend T p)) := by
  intro T hT
  rw [sepShapesOf, Finset.mem_image] at hT
  obtain ⟨lam, -, rfl⟩ := hT
  have hp2 : (2 : ℕ) ≤ p := (Fact.out (p := p.Prime)).two_le
  have hP0 : (p : ℚ) ≠ 0 := by positivity
  rw [rootCount_sepShape_eval (ZMod p) n hn lam p (Nat.card_zmod p)]
  refine Filter.Tendsto.congr' ?_ tendsto_const_nhds
  filter_upwards [Filter.eventually_ge_atTop 1] with N hN1
  rw [stratumCount_sepShape_general p n hn lam N (by omega)]
  rcases N with _ | M
  · omega
  · have hexp : (p : ℚ) ^ (n * (M + 1))
        = (p : ℚ) ^ ((M + 1 - 1) * n) * (p : ℚ) ^ n := by
      rw [← pow_add]
      congr 1
      have hMn : M + 1 - 1 = M := rfl
      rw [hMn]
      ring
    rw [hexp]
    push_cast
    have hne1 : (p : ℚ) ^ ((M + 1 - 1) * n) ≠ 0 := pow_ne_zero _ hP0
    have hne2 : (p : ℚ) ^ n ≠ 0 := pow_ne_zero _ hP0
    field_simp

/-- **`montes_order0_density_general_prime` — the σ-keyed order-0 density theorem for a GENERAL
prime `p`** (audit gap #2 for order-0). For every prime `p`, degree `n > 0`, and factorization type
`σ`: the SAME order-0 separable-stratum density function
`q' ↦ ∑_{T ∈ sepShapesOf n σ} rootCount T q'` is a uniform rational function of `q'` (one `num/den`,
`p`-INDEPENDENT), and the normalized general-prime classifier fiber counts at `p`,
`(∑_{T ∈ sepShapesOf n σ} #{f ∈ monicBox p N n : classify p n N f = T}) / p^(nN)`, converge to that
rational function's value at `p`. The rational function is exactly the `montes_order0_realDensity`
one; only the counting prime is now free. -/
theorem montes_order0_density_general_prime (p : ℕ) [Fact p.Prime] (n : ℕ) (hn : 0 < n)
    (σ : FactorizationType) :
    ∃ (num den : Polynomial ℚ), den ≠ 0 ∧
      (∀ q' : ℕ, 1 < q' → den.eval (q' : ℚ) ≠ 0 ∧
        (∑ T ∈ sepShapesOf n σ,
            rootCount M7.cellsOfShapeWF M6.treeSize M7.cellsOfShapeWF_descend T q')
          = num.eval (q' : ℚ) / den.eval (q' : ℚ)) ∧
      Filter.Tendsto
        (fun N =>
          (∑ T ∈ sepShapesOf n σ,
            (Nat.card {f : QuotientBox.monicBox p N n // B.classify p n N f = T} : ℚ))
            / (p : ℚ) ^ (n * N))
        Filter.atTop
        (nhds (num.eval (p : ℚ) / den.eval (p : ℚ))) := by
  classical
  -- (1) each menu shape is childless ⟹ its engine coefficient is a uniform rational function.
  have hrat : ∀ T ∈ sepShapesOf n σ,
      IsRationalFn (fun q' =>
        rootCount M7.cellsOfShapeWF M6.treeSize M7.cellsOfShapeWF_descend T q') := by
    intro T hT
    rw [sepShapesOf, Finset.mem_image] at hT
    obtain ⟨lam, _, rfl⟩ := hT
    exact rootCount_isRational_of_leaf _ _ _ _ (sepShape_leaf n lam)
  -- (2) the finite menu sum is a uniform rational function (p-independent).
  obtain ⟨num, den, hden, hall⟩ :=
    isRationalFn_finsetSum (sepShapesOf n σ)
      (fun T q' => rootCount M7.cellsOfShapeWF M6.treeSize M7.cellsOfShapeWF_descend T q') hrat
  refine ⟨num, den, hden, hall, ?_⟩
  -- (3) the value tie at the general prime `p`: sum of the per-shape general-prime limits.
  have hp2 : (2 : ℕ) ≤ p := (Fact.out (p := p.Prime)).two_le
  have hq : 1 < p := by omega
  have hsum : Filter.Tendsto
      (fun N => ∑ T ∈ sepShapesOf n σ,
        (Nat.card {f : QuotientBox.monicBox p N n // B.classify p n N f = T} : ℚ)
          / (p : ℚ) ^ (n * N))
      Filter.atTop
      (nhds (∑ T ∈ sepShapesOf n σ,
        rootCount M7.cellsOfShapeWF M6.treeSize M7.cellsOfShapeWF_descend T p)) :=
    tendsto_finsetSum (sepShapesOf n σ)
      (fun T hT => montes_order0_perShape_density_general p n hn σ T hT)
  have hpush : (fun N => (∑ T ∈ sepShapesOf n σ,
        (Nat.card {f : QuotientBox.monicBox p N n // B.classify p n N f = T} : ℚ))
        / (p : ℚ) ^ (n * N))
      = fun N => ∑ T ∈ sepShapesOf n σ,
          (Nat.card {f : QuotientBox.monicBox p N n // B.classify p n N f = T} : ℚ)
            / (p : ℚ) ^ (n * N) := by
    funext N
    rw [Finset.sum_div]
  rw [hpush]
  have hval := (hall p hq).2
  rw [← hval]
  exact hsum

/-- **Non-vacuity of the general-prime density (the `1/4`-shaped gate at an arbitrary prime).** At
`n = 2` and the INERT type `σ = unramType 2 (indiscrete 2)`, the general-prime certified density
value equals the per-shape sum `∑_{T} rootCount T p ≥ rootCount (sepShape 2 (indiscrete 2)) p`,
which is `(#Irr₂(p))/p² = (p²−p)/2 / p² > 0` for every prime `p`. Concretely: the value is STRICTLY
POSITIVE for every prime — the general-prime density is NOT the vacuous constant `0`. -/
theorem montes_order0_density_general_prime_pos (p : ℕ) [Fact p.Prime] :
    ∃ (num den : Polynomial ℚ), den ≠ 0 ∧
      (∀ q' : ℕ, 1 < q' → den.eval (q' : ℚ) ≠ 0 ∧
        (∑ T ∈ sepShapesOf 2 (unramType 2 (Nat.Partition.indiscrete 2)),
            rootCount M7.cellsOfShapeWF M6.treeSize M7.cellsOfShapeWF_descend T q')
          = num.eval (q' : ℚ) / den.eval (q' : ℚ)) ∧
      (0 : ℚ) < num.eval (p : ℚ) / den.eval (p : ℚ) := by
  obtain ⟨num, den, hden, hall, -⟩ :=
    montes_order0_density_general_prime p 2 (by norm_num)
      (unramType 2 (Nat.Partition.indiscrete 2))
  refine ⟨num, den, hden, hall, ?_⟩
  have hp2 : (2 : ℕ) ≤ p := (Fact.out (p := p.Prime)).two_le
  have hq : 1 < p := by omega
  have hval := (hall p hq).2
  rw [← hval]
  -- the inert term is `#Irr₂(p)/p² > 0`, and every menu term is nonnegative.
  have hpos : (0 : ℚ) < rootCount M7.cellsOfShapeWF M6.treeSize M7.cellsOfShapeWF_descend
      (sepShape 2 (Nat.Partition.indiscrete 2)) p := by
    rw [rootCount_sepShape_eval (ZMod p) 2 (by norm_num) (Nat.Partition.indiscrete 2) p
      (Nat.card_zmod p)]
    have hparts : (Nat.Partition.indiscrete 2).parts = {2} :=
      Nat.Partition.indiscrete_parts (by norm_num)
    rw [hparts]
    simp only [Multiset.toFinset_singleton, Finset.prod_singleton, Multiset.count_singleton_self]
    apply div_pos
    · -- `C(#Irr₂(p), 1) = #Irr₂(p) = (p²−p)/2 > 0` for `p ≥ 2`.
      rw [Nat.choose_one_right]
      have hcard : (avail (ZMod p) 2 : ℚ) = ((p : ℚ) ^ 2 - p) / 2 := by
        rw [avail_of_ne_one _ (by norm_num)]
        have h := necklaceQ_eq_card (ZMod p) 2 (by norm_num)
        rw [Nat.card_zmod, necklaceQ_two] at h
        rw [← h]
      rw [hcard]
      have hp2q : (2 : ℚ) ≤ (p : ℚ) := by exact_mod_cast hp2
      apply div_pos
      · nlinarith [hp2q]
      · norm_num
    · positivity
  calc (0 : ℚ)
      < rootCount M7.cellsOfShapeWF M6.treeSize M7.cellsOfShapeWF_descend
          (sepShape 2 (Nat.Partition.indiscrete 2)) p := hpos
    _ ≤ ∑ T ∈ sepShapesOf 2 (unramType 2 (Nat.Partition.indiscrete 2)),
          rootCount M7.cellsOfShapeWF M6.treeSize M7.cellsOfShapeWF_descend T p := by
        apply Finset.single_le_sum (f := fun T =>
          rootCount M7.cellsOfShapeWF M6.treeSize M7.cellsOfShapeWF_descend T p)
        · intro T hT
          rw [sepShapesOf, Finset.mem_image] at hT
          obtain ⟨lam, _, rfl⟩ := hT
          rw [rootCount_sepShape_eval (ZMod p) 2 (by norm_num) lam p (Nat.card_zmod p)]
          apply div_nonneg
          · exact Finset.prod_nonneg (fun d _ => by positivity)
          · positivity
        · exact inert2_mem_menu

end LeanUrat.OM.Order0

/-! ## 3. Machine-checked footprint witnesses (`#print axioms`)

Each must be exactly `[propext, Classical.choice, Quot.sound]` (Lean core only) — no `sorryAx`, no
declared or custom axioms on any of these order-0 density statements. -/

#print axioms LeanUrat.OM.Order0.montes_order0_realDensity
#print axioms LeanUrat.OM.Order0.montes_order0_certified_density_pos
#print axioms LeanUrat.OM.Order0.montes_order0_density_general_prime
#print axioms LeanUrat.OM.Order0.montes_order0_density_general_prime_pos
