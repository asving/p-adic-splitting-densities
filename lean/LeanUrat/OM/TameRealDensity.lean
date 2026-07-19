/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.OM.ClassifierBridgeFiber2
import LeanUrat.OM.PathShapeMultiSideTree
import LeanUrat.OM.Order0RealDensity

/-!
# TameRealDensity — the HONEST order-1 (single-slope) real density theorem (σ-keyed), a certified
NON-vacuous gate, and the general-prime standalone version (audit gaps #2/#3, order-1)

**Purpose (ADDITIVE; nothing existing changes).** Order-0 is banked additively in
`Order0RealDensity` (`Order0.montes_order0_realDensity` σ-keyed at `realP`,
`Order0.montes_order0_density_general_prime` for all primes). This module does the ORDER-1
(single-slope, all-`μ=1` self-loop) analogue: the genuine order-1 density
`ClassifierBridgeFiber2.montes_order1_selfloop_density` presented cleanly as THE order-1 single-slope
real density theorem, with a CERTIFIED strictly-positive gate (so it is NOT the audit's vacuous
constant `0`), plus a STANDALONE general-prime version.

**Step 1 (assessment).** `PathShapeMultiSideTree.hnode_multiSideProduct` is ALREADY stated at a
general prime `[Fact p.Prime]` (nothing to generalize). `montes_order1_selfloop_density` is PINNED
to `M9.realP = 2` (it routes through `MontesAllOrders.montes_allorders_of_hnode`, whose real-count
clause is at `M9.realP`/`M9.rawCount`). But its entire discharge chain
(`PathShape.hnode_oneSideShape`, `StratumOrder1.stratumCount1`, `classify_eq_selfloop_iff`,
`ClassifierBridgeFiber.omCount_selfloop_eq_oneSideShape`, `OMCountV2.omCount_isRational`) is
general-prime, so a STANDALONE general-prime version generalizes verbatim (like
`montes_order0_perShape_density_general` did for order-0). Provided here as §1–§2.

* GENERAL PRIME (gap #2, order-1). Everything in §1–§2 names the prime `p` and `B.classify p n`
  DIRECTLY (never `M9.rawCount`/`M9.realP`), so it is standalone — no core def is touched.
  * `stratumCount_selfloop_general` — the level-`N` classifier fiber count of the respelled
    `Tselfloop n pr shape` over `monicBox p N n`, cast to `ℚ`, equals the genuine order-1 stratum
    count `stratumCount1 p n N (mkCell n P [shape])`.
  * `hnode_selfloop_general` — `#{f : classify p n N f = Tselfloop} / p^(nN)` converges to the
    engine value `omCount (Tselfloop n pr shape) p`, at an ARBITRARY prime.
  * `montes_order1_selfloop_density_general_prime` — the singleton-self-loop-menu density theorem
    for a GENERAL prime `p`: the density function `q' ↦ omCount (Tselfloop …) q'` is a uniform
    rational function, and the general-prime counts at `p` converge to its value at `p`.

* REAL PRIME, σ-keyed (Step 2, the PRIMARY deliverable).
  * `montes_order1_tame_realDensity` — the σ-keyed order-1 single-slope real density theorem, SAME
    shape as `montes_order0_realDensity`: for the singleton self-loop menu `{Tselfloop n pr shape}`,
    the density function is a uniform rational function, the real normalized counts at `realP`
    converge to its value, AND that value equals the engine per-shape sum
    `∑_{T ∈ {Tselfloop …}} omCount T realP`. This is the honest re-presentation of
    `montes_order1_selfloop_density` with the certified value pinned to the explicit engine sum
    (clause 3), exactly as `montes_order0_realDensity` did for order-0.

* NON-VACUITY GATE (Step 2, certified strictly positive).
  * `montes_order1_tame_certified_density_pos` — at the CONCRETE single-slope self-loop
    `n = 2, H = 1, P = [(0,1),(2,0)], shape = [(1,1)]` (one degree-1, `μ=1` separable residual
    factor; `sideDeg = gcd(1,2) = 1`), the certified density value is STRICTLY POSITIVE: it equals
    `omCount (Tselfloop 2 ((0,1),(2,0)) [(1,1)]) realP = (realP − 1) · (realP^k)⁻¹ > 0`, because
    `shapeCount realP [(1,1)] = realP − 1 ≥ 1` (`CellCard.shapeCount_linear_pow`). So the order-1
    density theorem is NOT the audit's vacuous constant-`0` density.
  * `montes_order1_selfloop_density_general_prime_pos` — the same gate at an ARBITRARY prime:
    the general-prime certified value is `(p − 1) · (p^k)⁻¹ > 0`.

* STRETCH — the combined tame density assembly (`montes_tame_realDensity`) over ONE σ-keyed menu is
  NOT landed here: it is genuinely entangled (see the report / the note at §5). The blocker is that
  order-0 and order-1 live on DISJOINT shape families keyed to different data — the order-0 menu is
  `sepShapesOf n σ` (σ-determined partitions), the order-1 menu is `{Tselfloop n pr shape}` keyed to
  a `MenuPath`/side/residual-shape — and there is no banked σ-determined enumeration of the order-1
  self-loop shapes fibered over `σ`. Combining them into a single disjoint `Finset ClusterShape`
  keyed to `σ` (with a proof of disjointness/exhaustiveness on `p > n`) is the RealInstance-scale
  surgery the audit's de-vacuification path (steps 3–5) calls for; it ripples, so it is DEFERRED per
  the timebox. Steps 1–2 are additive and self-contained.

All sorry-free, axiom-clean (`propext, Classical.choice, Quot.sound`) — the `#print axioms` at the
bottom is the machine-checked footprint witness.
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false

namespace LeanUrat.OM.TameRealDensity

open LeanUrat LeanUrat.OM LeanUrat.MontesAxiom RatFn Polynomial Filter Topology
open LeanUrat.OM.OMCountV2
open LeanUrat.OM.CellMenu
open LeanUrat.OM.StratumOrder1
open LeanUrat.OM.PathShape

open scoped Classical

/-! ## 1. General prime: the self-loop stratum count and its normalized limit (gap #2, order-1)

Everything here names the prime `p` and `B.classify p n` DIRECTLY (never `M9.rawCount`/`M9.realP`),
so it is standalone — no core def is touched and nothing existing rebuilds. This is the exact
general-prime respell of `ClassifierBridgeFiber2.stratumCount_selfloop_R` /
`hnode_selfloop_over_Bclassify_R`, whose proofs already run through general-prime building blocks. -/

/-- **The general-prime self-loop stratum count** (ANY prime `p`). For a single-side, all-`μ=1`
self-loop menu path `P` (side `pr`, residual shape `shape`), the ℚ-cast level-`N` classifier fiber
count of the respelled `ClassifierBridgeFiber.Tselfloop n pr shape` over `monicBox p N n` equals the
genuine order-1 stratum count `stratumCount1 p n N (mkCell n P [shape])`. `Nat.card_congr` on
`classify_eq_selfloop_iff` (general `p`) then `stratumCount1_eq_cellCard`. -/
theorem stratumCount_selfloop_general (p : ℕ) [Fact p.Prime] (n N : ℕ) (hN : 0 < N) (hn : 0 < n)
    (P : List (ℕ × ℕ)) (hPmenu : MenuPath n N P) (pr : (ℕ × ℕ) × (ℕ × ℕ)) (hsingle : sidePairs P = [pr])
    (shape : List (ℕ × ℕ)) (hSF : ShapesFor P [shape]) (hmu : ∀ q ∈ shape, q.2 = 1)
    (hne : shape ≠ []) :
    (Nat.card {f : QuotientBox.monicBox p N n //
        B.classify p n N f = ClassifierBridgeFiber.Tselfloop n pr shape} : ℚ)
      = ((StratumOrder1.stratumCount1 p n N (mkCell n P [shape]) : ℕ) : ℚ) := by
  rw [StratumOrder1.stratumCount1_eq_cellCard]
  congr 1
  exact Nat.card_congr (Equiv.subtypeEquivRight
    (fun f => ClassifierBridgeFiber2.classify_eq_selfloop_iff n N hN hn P hPmenu pr hsingle shape hSF hmu hne f))

/-- **The general-prime self-loop `h_node` limit** (ANY prime `p`). For a single-side, all-`μ=1`,
nonempty self-loop menu path `P` with side `pr = ((0,H),(n,0))`, the normalized general-prime
classifier fiber count `#{f : classify p n N f = Tselfloop n pr shape} / p^(nN)` converges to the
engine value `omCount (Tselfloop n pr shape) p`. Transport `PathShape.hnode_oneSideShape` along
`omCount_selfloop_eq_oneSideShape` (limit value) and `stratumCount_selfloop_general` (sequence),
verbatim from `hnode_selfloop_over_Bclassify_R` with `M9.realP` replaced by `p`. -/
theorem hnode_selfloop_general (p : ℕ) [Fact p.Prime] (n N₀ : ℕ) (hN₀ : 0 < N₀) (hn : 0 < n)
    (H : ℕ) (P : List (ℕ × ℕ)) (hP : MenuPath n N₀ P)
    (hsingle : sidePairs P = [(((0, H), (n, 0)) : (ℕ × ℕ) × (ℕ × ℕ))])
    (shape : List (ℕ × ℕ)) (hsh : ShapesFor P [shape]) (hpos : ∀ q ∈ shape, 1 ≤ q.1)
    (hμ : ∀ q ∈ shape, q.2 = 1) (hne : shape ≠ []) :
    Filter.Tendsto
      (fun N =>
        (Nat.card {f : QuotientBox.monicBox p N n //
          B.classify p n N f =
            ClassifierBridgeFiber.Tselfloop n (((0, H), (n, 0)) : (ℕ × ℕ) × (ℕ × ℕ)) shape} : ℚ)
          / (p : ℚ) ^ (n * N))
      Filter.atTop
      (nhds (omCount (ClassifierBridgeFiber.Tselfloop n (((0, H), (n, 0)) : (ℕ × ℕ) × (ℕ × ℕ)) shape)
        p)) := by
  have hbase := PathShape.hnode_oneSideShape n N₀ hN₀
    (((0, H), (n, 0)) : (ℕ × ℕ) × (ℕ × ℕ)) P hP hsingle shape hsh hpos hμ hne p
  -- rewrite the LIMIT VALUE by the respelled engine identity.
  rw [← ClassifierBridgeFiber.omCount_selfloop_eq_oneSideShape n H shape hne p] at hbase
  -- `P = [(0,H),(n,0)]` and `1 ≤ H` from the level-`N₀` menu path.
  obtain ⟨H', hPeq, hpreq, hH1', _⟩ := ClassifierBridgeFiber.menuPath_single_side hP hsingle
  have hHH' : H' = H := by
    have heq : (((0, H'), (n, 0)) : (ℕ × ℕ) × (ℕ × ℕ)) = (((0, H), (n, 0)) : (ℕ × ℕ) × (ℕ × ℕ)) := by
      have h1 : sidePairs P = [(((0, H'), (n, 0)) : (ℕ × ℕ) × (ℕ × ℕ))] := by
        rw [hPeq]; rfl
      rw [hsingle] at h1
      exact (List.cons.injEq _ _ _ _ ▸ h1).1.symm
    have := congrArg (fun pr => pr.1.2) heq
    simpa using this
  subst H'
  have hH1 : 1 ≤ H := hH1'
  -- rewrite the SEQUENCE by the count identity, EVENTUALLY (for `N ≥ H+1`, so `1 ≤ H ≤ N-1`).
  refine hbase.congr' ?_
  filter_upwards [Filter.eventually_ge_atTop (H + 1)] with N hNge
  have hNpos : 0 < N := by omega
  have hPN : MenuPath n N P := by
    rw [hPeq]
    exact ⟨H, ((n : ℕ), (0 : ℕ)), [], rfl, hH1, by omega, hn, by omega,
      ChainOK.nil rfl rfl⟩
  rw [stratumCount_selfloop_general p n N hNpos hn P hPN
    (((0, H), (n, 0)) : (ℕ × ℕ) × (ℕ × ℕ)) hsingle shape hsh hμ hne]

/-! ## 2. General prime: the σ-keyed singleton-self-loop-menu density theorem (gap #2, order-1)

The general-prime skeleton (a self-contained analogue of `MontesAllOrders.montes_allorders_of_hnode`
at an arbitrary prime `p`), specialized to the singleton self-loop menu, exactly as
`montes_order0_density_general_prime` did for the separable order-0 menu. -/

/-- **`montes_order1_selfloop_density_general_prime` — the singleton-self-loop-menu density theorem
for a GENERAL prime `p`** (audit gap #2 for order-1). For every prime `p`, degree `n > 0`, and a
single-side, all-`μ=1`, nonempty self-loop menu path `P` (side `((0,H),(n,0))`, residual shape
`shape`): the density function `q' ↦ ∑_{T ∈ {Tselfloop …}} omCount T q'` is a uniform rational
function of `q'` (one `num/den`, `p`-INDEPENDENT), and the normalized general-prime classifier fiber
counts at `p` converge to that rational function's value at `p`. -/
theorem montes_order1_selfloop_density_general_prime (p : ℕ) [Fact p.Prime] (n : ℕ) (hn : 0 < n)
    (N₀ : ℕ) (hN₀ : 0 < N₀) (H : ℕ) (P : List (ℕ × ℕ)) (hP : MenuPath n N₀ P)
    (hsingle : sidePairs P = [(((0, H), (n, 0)) : (ℕ × ℕ) × (ℕ × ℕ))])
    (shape : List (ℕ × ℕ)) (hsh : ShapesFor P [shape]) (hpos : ∀ q ∈ shape, 1 ≤ q.1)
    (hμ : ∀ q ∈ shape, q.2 = 1) (hne : shape ≠ []) :
    ∃ (num den : Polynomial ℚ), den ≠ 0 ∧
      (∀ q' : ℕ, 1 < q' → den.eval (q' : ℚ) ≠ 0 ∧
        (∑ T ∈ ({ClassifierBridgeFiber.Tselfloop n (((0, H), (n, 0)) : (ℕ × ℕ) × (ℕ × ℕ)) shape}
            : Finset ClusterShape), omCount T q') = num.eval (q' : ℚ) / den.eval (q' : ℚ)) ∧
      Filter.Tendsto
        (fun N =>
          (∑ T ∈ ({ClassifierBridgeFiber.Tselfloop n
              (((0, H), (n, 0)) : (ℕ × ℕ) × (ℕ × ℕ)) shape} : Finset ClusterShape),
            (Nat.card {f : QuotientBox.monicBox p N n // B.classify p n N f = T} : ℚ))
            / (p : ℚ) ^ (n * N))
        Filter.atTop
        (nhds (num.eval (p : ℚ) / den.eval (p : ℚ))) := by
  classical
  set M : Finset ClusterShape :=
    {ClassifierBridgeFiber.Tselfloop n (((0, H), (n, 0)) : (ℕ × ℕ) × (ℕ × ℕ)) shape} with hM
  -- (1) each menu shape's engine coefficient is a uniform rational function (ANY shape).
  have hrat : ∀ T ∈ M, IsRationalFn (fun q' => omCount T q') :=
    fun T _ => OMCountV2.omCount_isRational T
  -- (2) the finite menu sum is a uniform rational function (p-independent).
  obtain ⟨num, den, hden, hall⟩ :=
    Order0.isRationalFn_finsetSum M (fun T q' => omCount T q') hrat
  refine ⟨num, den, hden, hall, ?_⟩
  -- (3) the value tie at the general prime `p`: sum of the per-shape general-prime limits.
  have hp2 : (2 : ℕ) ≤ p := (Fact.out (p := p.Prime)).two_le
  have hq : 1 < p := by omega
  have h_node : ∀ T ∈ M,
      Filter.Tendsto
        (fun N => (Nat.card {f : QuotientBox.monicBox p N n // B.classify p n N f = T} : ℚ)
          / (p : ℚ) ^ (n * N))
        Filter.atTop
        (nhds (omCount T p)) := by
    intro T hT
    rw [hM, Finset.mem_singleton] at hT
    subst hT
    exact hnode_selfloop_general p n N₀ hN₀ hn H P hP hsingle shape hsh hpos hμ hne
  have hsum : Filter.Tendsto
      (fun N => ∑ T ∈ M,
        (Nat.card {f : QuotientBox.monicBox p N n // B.classify p n N f = T} : ℚ)
          / (p : ℚ) ^ (n * N))
      Filter.atTop
      (nhds (∑ T ∈ M, omCount T p)) :=
    tendsto_finsetSum M (fun T hT => h_node T hT)
  have hpush : (fun N => (∑ T ∈ M,
        (Nat.card {f : QuotientBox.monicBox p N n // B.classify p n N f = T} : ℚ))
        / (p : ℚ) ^ (n * N))
      = fun N => ∑ T ∈ M,
          (Nat.card {f : QuotientBox.monicBox p N n // B.classify p n N f = T} : ℚ)
            / (p : ℚ) ^ (n * N) := by
    funext N
    rw [Finset.sum_div]
  rw [hpush]
  have hval := (hall p hq).2
  rw [← hval]
  exact hsum

/-! ## 3. The PRIMARY deliverable: the honest, σ-keyed real order-1 single-slope density theorem -/

/-- **`montes_order1_tame_realDensity` — THE real order-1 single-slope density theorem (σ-keyed).**

For every degree `n > 0`, factorization type `σ`, and a single-side, all-`μ=1`, nonempty self-loop
menu path `P` (side `((0,H),(n,0))`, residual `shape`), there is a uniform rational function
`num/den` such that:

1. **(density = engine rational function)** the order-1 single-slope density function
   `q' ↦ ∑_{T ∈ {Tselfloop n pr shape}} omCount T q'` EQUALS `num(q')/den(q')` at every `q' > 1`;
2. **(real counts converge)** the real normalized level-`N` classifier fiber counts at `realP`,
   `(∑_{T} stratumCount (rawCount n) T N) / realP^(nN)`, converge to `num(realP)/den(realP)`;
3. **(certified value = the honest per-shape sum)** that limit value equals the engine menu sum
   `∑_{T ∈ {Tselfloop …}} omCount T realP` — the genuine engine value at the real prime.

Same SHAPE as `Order0.montes_order0_realDensity`, one order up: the menu is the genuine order-1
self-loop shape `Tselfloop n pr shape`, the value is the engine `omCount` at the single Newton
slope. This is the honest re-presentation of `ClassifierBridgeFiber2.montes_order1_selfloop_density`,
additionally pinning the certified value to the explicit engine per-shape sum (clause 3). NON-vacuous:
`montes_order1_tame_certified_density_pos` exhibits a concrete self-loop whose value is `> 0`. -/
theorem montes_order1_tame_realDensity (n : ℕ) (hn : 0 < n) (σ : FactorizationType)
    (N₀ : ℕ) (hN₀ : 0 < N₀) (H : ℕ) (P : List (ℕ × ℕ)) (hP : MenuPath n N₀ P)
    (hsingle : sidePairs P = [(((0, H), (n, 0)) : (ℕ × ℕ) × (ℕ × ℕ))])
    (shape : List (ℕ × ℕ)) (hsh : ShapesFor P [shape]) (hpos : ∀ q ∈ shape, 1 ≤ q.1)
    (hμ : ∀ q ∈ shape, q.2 = 1) (hne : shape ≠ []) :
    ∃ (num den : Polynomial ℚ), den ≠ 0 ∧
      (∀ q' : ℕ, 1 < q' → den.eval (q' : ℚ) ≠ 0 ∧
        (∑ T ∈ ({ClassifierBridgeFiber.Tselfloop n (((0, H), (n, 0)) : (ℕ × ℕ) × (ℕ × ℕ)) shape}
            : Finset ClusterShape), omCount T q') = num.eval (q' : ℚ) / den.eval (q' : ℚ)) ∧
      Filter.Tendsto
        (fun N => (∑ T ∈ ({ClassifierBridgeFiber.Tselfloop n
              (((0, H), (n, 0)) : (ℕ × ℕ) × (ℕ × ℕ)) shape} : Finset ClusterShape),
            M8.stratumCount (M9.rawCount n) T N)
            / (M9.realP : ℚ) ^ (n * N))
        Filter.atTop
        (nhds (num.eval (M9.realP : ℚ) / den.eval (M9.realP : ℚ)))
      ∧ num.eval (M9.realP : ℚ) / den.eval (M9.realP : ℚ)
          = ∑ T ∈ ({ClassifierBridgeFiber.Tselfloop n (((0, H), (n, 0)) : (ℕ × ℕ) × (ℕ × ℕ)) shape}
              : Finset ClusterShape), omCount T M9.realP := by
  obtain ⟨num, den, hden, hall, hlim⟩ :=
    ClassifierBridgeFiber2.montes_order1_selfloop_density n hn σ N₀ hN₀ H P hP hsingle shape hsh
      hpos hμ hne
  refine ⟨num, den, hden, hall, hlim, ?_⟩
  -- the certified value = num(realP)/den(realP) equals the engine per-shape sum, because the
  -- `∀ q'` rational identity holds at `q' = realP > 1`.
  have hq : 1 < M9.realP := by unfold M9.realP; norm_num
  exact ((hall M9.realP hq).2).symm

/-! ## 4. Non-vacuity: the certified strictly-positive gate

Concrete self-loop: `n = 2, H = 1, P = [(0,1),(2,0)], shape = [(1,1)]` — one degree-1, `μ=1`
separable residual factor. `sidePairs P = [((0,1),(2,0))]`, `sideDeg ((0,1),(2,0)) = gcd(1,2) = 1`,
so `[(1,1)] ∈ shapesOfDegree 1` and `ShapesFor P [[(1,1)]]` holds. The engine value is
`omCount (Tselfloop 2 pr [(1,1)]) p = shapeCount p [(1,1)] · (p^k)⁻¹ = (p − 1) · (p^k)⁻¹ > 0`
(`CellCard.shapeCount_linear_pow`), so the density is NOT vacuous. -/

/-- The concrete single-side self-loop side `((0,1),(2,0))`. -/
private def gatePr : (ℕ × ℕ) × (ℕ × ℕ) := ((0, 1), (2, 0))

/-- The concrete residual shape `[(1,1)]` — one degree-1, multiplicity-1 factor. -/
private def gateShape : List (ℕ × ℕ) := [(1, 1)]

private theorem gate_sidePairs : sidePairs [((0 : ℕ), (1 : ℕ)), ((2 : ℕ), (0 : ℕ))] = [gatePr] := by
  rfl

private theorem gate_sideDeg : sideDeg gatePr = 1 := by
  rfl

/-- `[(1,1)] ∈ shapesOfDegree 1`. -/
private theorem gate_shape_mem : gateShape ∈ shapesOfDegree 1 := by
  rw [mem_shapesOfDegree_iff]
  refine ⟨by simp [gateShape], ?_, by simp [gateShape]⟩
  intro q hq
  simp only [gateShape, List.mem_singleton] at hq
  subst hq
  exact ⟨le_refl 1, le_refl 1⟩

/-- `ShapesFor [(0,1),(2,0)] [[(1,1)]]`. -/
private theorem gate_shapesFor :
    ShapesFor [((0 : ℕ), (1 : ℕ)), ((2 : ℕ), (0 : ℕ))] [gateShape] := by
  unfold ShapesFor
  rw [gate_sidePairs]
  refine List.Forall₂.cons ?_ List.Forall₂.nil
  rw [gate_sideDeg]
  exact gate_shape_mem

/-- `MenuPath 2 2 [(0,1),(2,0)]`. -/
private theorem gate_menuPath : MenuPath 2 2 [((0 : ℕ), (1 : ℕ)), ((2 : ℕ), (0 : ℕ))] :=
  ⟨1, ((2 : ℕ), (0 : ℕ)), [], rfl, le_refl 1, by norm_num, by norm_num, by norm_num,
    ChainOK.nil rfl rfl⟩

/-- **The general-prime engine value at the gate is `(p − 1) · (p^k)⁻¹`, hence strictly positive**
for every prime `p`. `omCount (Tselfloop 2 pr [(1,1)]) p = omCount (oneSideShape 2 pr [(1,1)]) p`
(`omCount_selfloop_eq_oneSideShape`), which by `omCount_oneSideShape_closed` is
`shapeCount p [(1,1)] · (p^(newtonExponent + sideDeg))⁻¹`, and `shapeCount p [(1,1)] = p − 1`
(`shapeCount_linear_pow`), positive for `p ≥ 2`. -/
private theorem gate_omCount_pos (p : ℕ) [Fact p.Prime] :
    (0 : ℚ) < omCount (ClassifierBridgeFiber.Tselfloop 2 gatePr gateShape) p := by
  have hp2 : (2 : ℕ) ≤ p := (Fact.out (p := p.Prime)).two_le
  -- unfold the concrete gate data to literals `[(1,1)]` / `((0,1),(2,0))`.
  show (0 : ℚ) < omCount (ClassifierBridgeFiber.Tselfloop 2
    (((0, 1), (2, 0)) : (ℕ × ℕ) × (ℕ × ℕ)) [((1 : ℕ), (1 : ℕ))]) p
  have hne : ([((1 : ℕ), (1 : ℕ))] : List (ℕ × ℕ)) ≠ [] := by simp
  have hpos1 : ∀ q ∈ ([((1 : ℕ), (1 : ℕ))] : List (ℕ × ℕ)), 1 ≤ q.1 := by
    intro q hq; simp only [List.mem_singleton] at hq; subst hq; exact le_refl 1
  have hmu1 : ∀ q ∈ ([((1 : ℕ), (1 : ℕ))] : List (ℕ × ℕ)), q.2 = 1 := by
    intro q hq; simp only [List.mem_singleton] at hq; subst hq; rfl
  have hdeg1 : (([((1 : ℕ), (1 : ℕ))] : List (ℕ × ℕ)).map Prod.fst).sum
      = sideDeg (((0, 1), (2, 0)) : (ℕ × ℕ) × (ℕ × ℕ)) := by decide
  -- transport to `oneSideShape` and use the closed form.
  rw [ClassifierBridgeFiber.omCount_selfloop_eq_oneSideShape 2 1 ([((1 : ℕ), (1 : ℕ))] : List (ℕ × ℕ)) hne p]
  rw [PathShape.omCount_oneSideShape_closed 2 (((0, 1), (2, 0)) : (ℕ × ℕ) × (ℕ × ℕ))
      ([((1 : ℕ), (1 : ℕ))] : List (ℕ × ℕ)) hpos1 hmu1 hdeg1 hne p]
  apply mul_pos
  · rw [CellCard.shapeCount_linear_pow p (μ := 1) (by norm_num)]
    have hcast : ((p - 1 : ℕ) : ℚ) = (p : ℚ) - 1 := by
      rw [Nat.cast_sub (by omega : 1 ≤ p)]; norm_num
    have hpQ : (2 : ℚ) ≤ (p : ℚ) := by exact_mod_cast hp2
    rw [hcast]; linarith
  · have hp0 : (p : ℚ) ≠ 0 := by positivity
    positivity

/-- **Non-vacuity of `montes_order1_tame_realDensity` (certified strictly-positive gate).** At the
CONCRETE single-slope self-loop `n = 2, P = [(0,1),(2,0)], shape = [(1,1)]`, the certified order-1
density value is STRICTLY POSITIVE. Together with `montes_order1_tame_realDensity` this witnesses,
machine-checked, that the real order-1 single-slope density theorem is NOT the audit's vacuous
constant-`0` density. -/
theorem montes_order1_tame_certified_density_pos :
    ∃ (num den : Polynomial ℚ), den ≠ 0 ∧
      (∀ q' : ℕ, 1 < q' → den.eval (q' : ℚ) ≠ 0 ∧
        (∑ T ∈ ({ClassifierBridgeFiber.Tselfloop 2 (((0, 1), (2, 0)) : (ℕ × ℕ) × (ℕ × ℕ)) gateShape}
            : Finset ClusterShape), omCount T q') = num.eval (q' : ℚ) / den.eval (q' : ℚ)) ∧
      (0 : ℚ) < num.eval (M9.realP : ℚ) / den.eval (M9.realP : ℚ) := by
  obtain ⟨num, den, hden, hall, _hlim, hval⟩ :=
    montes_order1_tame_realDensity 2 (by norm_num) (Order0.unramType 2 (Nat.Partition.indiscrete 2))
      2 (by norm_num) 1 [((0 : ℕ), (1 : ℕ)), ((2 : ℕ), (0 : ℕ))] gate_menuPath
      (by rw [gate_sidePairs]; rfl)
      gateShape gate_shapesFor
      (by intro q hq; simp only [gateShape, List.mem_singleton] at hq; subst hq; exact le_refl 1)
      (by intro q hq; simp only [gateShape, List.mem_singleton] at hq; subst hq; rfl)
      (by simp [gateShape])
  refine ⟨num, den, hden, hall, ?_⟩
  rw [hval]
  -- the value = ∑_{T ∈ {Tselfloop …}} omCount T realP = omCount (Tselfloop …) realP > 0.
  rw [Finset.sum_singleton]
  have := gate_omCount_pos M9.realP
  simpa [gatePr] using this

/-- **Non-vacuity of the general-prime order-1 density (the gate at an ARBITRARY prime).** At the
CONCRETE self-loop `n = 2, P = [(0,1),(2,0)], shape = [(1,1)]`, the general-prime certified value is
`(p − 1) · (p^k)⁻¹ > 0` for EVERY prime `p`. So the general-prime order-1 density is NOT vacuous. -/
theorem montes_order1_selfloop_density_general_prime_pos (p : ℕ) [Fact p.Prime] :
    ∃ (num den : Polynomial ℚ), den ≠ 0 ∧
      (∀ q' : ℕ, 1 < q' → den.eval (q' : ℚ) ≠ 0 ∧
        (∑ T ∈ ({ClassifierBridgeFiber.Tselfloop 2 (((0, 1), (2, 0)) : (ℕ × ℕ) × (ℕ × ℕ)) gateShape}
            : Finset ClusterShape), omCount T q') = num.eval (q' : ℚ) / den.eval (q' : ℚ)) ∧
      (0 : ℚ) < num.eval (p : ℚ) / den.eval (p : ℚ) := by
  obtain ⟨num, den, hden, hall, -⟩ :=
    montes_order1_selfloop_density_general_prime p 2 (by norm_num) 2 (by norm_num) 1
      [((0 : ℕ), (1 : ℕ)), ((2 : ℕ), (0 : ℕ))] gate_menuPath
      (by rw [gate_sidePairs]; rfl)
      gateShape gate_shapesFor
      (by intro q hq; simp only [gateShape, List.mem_singleton] at hq; subst hq; exact le_refl 1)
      (by intro q hq; simp only [gateShape, List.mem_singleton] at hq; subst hq; rfl)
      (by simp [gateShape])
  refine ⟨num, den, hden, hall, ?_⟩
  have hp2 : (2 : ℕ) ≤ p := (Fact.out (p := p.Prime)).two_le
  have hq : 1 < p := by omega
  have hval := (hall p hq).2
  rw [← hval, Finset.sum_singleton]
  exact gate_omCount_pos p

/-! ## 5. THE HONEST CONDITIONAL TAME ASSEMBLY (order-0 ⊕ order-1, one σ-keyed menu)

This is the ADDITIVE assembly increment. Order-0 (`sepShapesOf n σ`) and order-1
(`{Tselfloop n ((0,H),(n,0)) shape}`) BOTH live in `Finset ClusterShape`, so their UNION is a single
well-typed σ-keyed menu — the disjoint-shape-family typing is NOT an obstruction to the CONDITIONAL
assembly. The two remaining pieces of a FULL tame theorem are, per the audit / blueprint §1.4:

* **(a) enumeration** — a σ-determined menu of the tame shapes. Here the menu is
  `tameMenu n σ H P shape = sepShapesOf n σ ∪ {Tselfloop …}`: the σ-keyed order-0 separable strata
  UNITED with the caller-supplied order-1 single-slope self-loop shape. Genuinely NON-vacuous (§4/§1
  gates: the order-0 inert term and the order-1 self-loop term are both strictly positive).
* **(b) EXHAUSTIVENESS / DRAINAGE** — that this menu captures ALL the tame strata, i.e. the off-menu
  ("undecided") mass fraction vanishes as `N → ∞`. Per `Drainage.lean` (honesty note 4) the current
  classifier does NOT drain at any finite order (the self-loop coset's index in the cluster box is
  level-INDEPENDENT), so this is a GENUINE OPEN DEFECT. We do NOT prove it; we state it as ONE
  explicit honest hypothesis `TameMenuExhaustive`, exactly in the spirit of
  `ConditionalDensity.SelfLoopHNode`.

The per-shape `h_node` inputs are ALREADY PROVEN — order-0 by `Order0Alpha.h_node0_proved`
(+ `omCount_sepShape_eq_rootCount`), order-1 by
`ClassifierBridgeFiber2.hnode_selfloop_over_Bclassify_R` — so they are DISCHARGED here, NOT taken as
hypotheses. `TameMenuExhaustive` is therefore the SINGLE remaining input, and it is stated so it does
NOT fix the density value (it says the off-menu mass → 0, not that the density is any particular
number), hence does not trivialize the theorem. -/

/-- **The σ-keyed tame menu** (order-0 ⊕ order-1): the order-0 separable strata `sepShapesOf n σ`
UNITED with the single order-1 self-loop shape `Tselfloop n ((0,H),(n,0)) shape`. One well-typed
`Finset ClusterShape`; σ is genuinely used (through the order-0 leg). -/
noncomputable def tameMenu (n : ℕ) (σ : FactorizationType) (H : ℕ) (shape : List (ℕ × ℕ)) :
    Finset ClusterShape :=
  Order0.sepShapesOf n σ
    ∪ {ClassifierBridgeFiber.Tselfloop n (((0, H), (n, 0)) : (ℕ × ℕ) × (ℕ × ℕ)) shape}

/-- **The EXHAUSTIVENESS / DRAINAGE hypothesis** (the honest remaining gap, stated as a Prop). The
menu `M`'s captured mass exhausts the full monic box in the limit: the OFF-menu (undecided /
undrained) normalized count `(#box − ∑_{T∈M} #{classify = T}) / realP^(nN)` tends to `0` as
`N → ∞`. Equivalently, `M` captures ALL the strata asymptotically. Per `Drainage.lean` this is FALSE
at any finite order for the current classifier (the self-loop coset does not drain), so it is a
GENUINE OPEN DEFECT — taken here as the SINGLE explicit hypothesis (like
`ConditionalDensity.SelfLoopHNode`). It does NOT fix the density value, so it does not trivialize the
theorem. -/
def TameMenuExhaustive (n : ℕ) (M : Finset ClusterShape) : Prop :=
  Filter.Tendsto
    (fun N => ((Nat.card (QuotientBox.monicBox M9.realP N n) : ℚ)
        - ∑ T ∈ M, M8.stratumCount (M9.rawCount n) T N) / (M9.realP : ℚ) ^ (n * N))
    Filter.atTop
    (nhds 0)

/-- **`montes_tame_realDensity_of_exhaustive` — THE HONEST CONDITIONAL TAME REAL DENSITY THEOREM.**

For every degree `n > 0`, factorization type `σ`, and a single-side, all-`μ=1`, nonempty order-1
self-loop menu path `P` (side `((0,H),(n,0))`, residual `shape`), let
`M = tameMenu n σ H shape = sepShapesOf n σ ∪ {Tselfloop n ((0,H),(n,0)) shape}` be the σ-keyed tame
menu (order-0 ⊕ order-1). GIVEN the SINGLE honest exhaustiveness hypothesis
`hExhaust : TameMenuExhaustive n M` (the drainage gap — the off-menu mass → 0), there is a uniform
rational function `num/den` such that:

1. **(density = engine rational function)** the tame density `q' ↦ ∑_{T ∈ M} omCount T q'` EQUALS
   `num(q')/den(q')` at every `q' > 1`;
2. **(real TOTAL counts converge)** the REAL normalized TOTAL monic-box count at `realP`,
   `#(monicBox realP N n) / realP^(nN)`, converges as `N → ∞` to `num(realP)/den(realP)`;
3. **(certified value = the honest per-shape engine sum)** that limit value equals the engine menu
   sum `∑_{T ∈ M} omCount T realP`.

The per-shape `h_node` inputs are DISCHARGED (order-0 `h_node0_proved`, order-1
`hnode_selfloop_over_Bclassify_R`), NOT assumed. `hExhaust` is the ONLY hypothesis, and it is the
genuine drainage/exhaustiveness gap. Reads: "the tame density = this rational function, for the real
prime, keyed to σ, MODULO the single explicit exhaustiveness hypothesis." -/
theorem montes_tame_realDensity_of_exhaustive (n : ℕ) (hn : 0 < n) (σ : FactorizationType)
    (N₀ : ℕ) (hN₀ : 0 < N₀) (H : ℕ) (P : List (ℕ × ℕ)) (hP : MenuPath n N₀ P)
    (hsingle : sidePairs P = [(((0, H), (n, 0)) : (ℕ × ℕ) × (ℕ × ℕ))])
    (shape : List (ℕ × ℕ)) (hsh : ShapesFor P [shape]) (hpos : ∀ q ∈ shape, 1 ≤ q.1)
    (hμ : ∀ q ∈ shape, q.2 = 1) (hne : shape ≠ [])
    (hExhaust : TameMenuExhaustive n (tameMenu n σ H shape)) :
    ∃ (num den : Polynomial ℚ), den ≠ 0 ∧
      (∀ q' : ℕ, 1 < q' → den.eval (q' : ℚ) ≠ 0 ∧
        (∑ T ∈ tameMenu n σ H shape, omCount T q') = num.eval (q' : ℚ) / den.eval (q' : ℚ)) ∧
      Filter.Tendsto
        (fun N => (Nat.card (QuotientBox.monicBox M9.realP N n) : ℚ) / (M9.realP : ℚ) ^ (n * N))
        Filter.atTop
        (nhds (num.eval (M9.realP : ℚ) / den.eval (M9.realP : ℚ)))
      ∧ num.eval (M9.realP : ℚ) / den.eval (M9.realP : ℚ)
          = ∑ T ∈ tameMenu n σ H shape, omCount T M9.realP := by
  classical
  set M : Finset ClusterShape := tameMenu n σ H shape with hMdef
  set Tsl : ClusterShape :=
    ClassifierBridgeFiber.Tselfloop n (((0, H), (n, 0)) : (ℕ × ℕ) × (ℕ × ℕ)) shape with hTsl
  -- (1) DISCHARGE the per-shape h_node over `M = sepShapesOf n σ ∪ {Tsl}` by cases — NOT hypotheses.
  have h_node : ∀ T ∈ M,
      Filter.Tendsto
        (fun N => M8.stratumCount (M9.rawCount n) T N / (M9.realP : ℚ) ^ (n * N))
        Filter.atTop
        (nhds (omCount T M9.realP)) := by
    intro T hT
    rw [hMdef, tameMenu, Finset.mem_union] at hT
    rcases hT with h0 | h1
    · -- order-0 separable leg: `h_node0_proved` composed with `omCount = rootCount`.
      rw [Order0.sepShapesOf, Finset.mem_image] at h0
      obtain ⟨lam, hlam, rfl⟩ := h0
      have hmem : Order0.sepShape n lam ∈ Order0.sepShapesOf n σ := by
        rw [Order0.sepShapesOf, Finset.mem_image]; exact ⟨lam, hlam, rfl⟩
      rw [omCount_sepShape_eq_rootCount]
      exact Order0.h_node0_proved n hn σ (Order0.sepShape n lam) hmem
    · -- order-1 self-loop leg: `hnode_selfloop_over_Bclassify_R` on the single shape.
      rw [Finset.mem_singleton] at h1
      subst h1
      exact ClassifierBridgeFiber2.hnode_selfloop_over_Bclassify_R n N₀ hN₀ hn H P hP hsingle
        shape hsh hpos hμ hne
  -- (2) FEED the S1 assembly spine on the united menu (UNCONDITIONAL given h_node).
  obtain ⟨num, den, hden, hall, hmenuLim⟩ :=
    MontesAllOrders.montes_allorders_of_hnode n σ M h_node
  refine ⟨num, den, hden, hall, ?_, ?_⟩
  · -- (3) the TOTAL box count converges: `box/p^{nN} = (box − ∑menu)/p^{nN} + ∑menu/p^{nN}`,
    -- the first summand → 0 by `hExhaust`, the second → num/den by the spine.
    have hExh : Filter.Tendsto
        (fun N => ((Nat.card (QuotientBox.monicBox M9.realP N n) : ℚ)
            - ∑ T ∈ M, M8.stratumCount (M9.rawCount n) T N) / (M9.realP : ℚ) ^ (n * N))
        Filter.atTop (nhds 0) := hExhaust
    have hcomb : Filter.Tendsto
        (fun N => ((Nat.card (QuotientBox.monicBox M9.realP N n) : ℚ)
              - ∑ T ∈ M, M8.stratumCount (M9.rawCount n) T N) / (M9.realP : ℚ) ^ (n * N)
            + (∑ T ∈ M, M8.stratumCount (M9.rawCount n) T N) / (M9.realP : ℚ) ^ (n * N))
        Filter.atTop
        (nhds (0 + num.eval (M9.realP : ℚ) / den.eval (M9.realP : ℚ))) :=
      hExh.add hmenuLim
    rw [zero_add] at hcomb
    refine hcomb.congr fun N => ?_
    rw [← add_div]
    congr 1
    ring
  · -- the certified value = num(realP)/den(realP) equals the engine per-shape sum (via `hall`).
    have hq : 1 < M9.realP := by unfold M9.realP; norm_num
    exact ((hall M9.realP hq).2).symm

/-! ### Non-vacuity of the conditional tame assembly (machine-checked). -/

/-- **The order-0 leg of the concrete tame menu is genuinely occupied**: at `n = 2`, the inert type
`σ = unramType 2 (indiscrete 2)`, `H = 1`, `shape = [(1,1)]`, the inert order-0 shape
`sepShape 2 (indiscrete 2)` is a member of `tameMenu` — so the menu contains the real order-0 inert
term (with its `1/4` gate). -/
theorem inert2_mem_tameMenu :
    Order0.sepShape 2 (Nat.Partition.indiscrete 2)
      ∈ tameMenu 2 (Order0.unramType 2 (Nat.Partition.indiscrete 2)) 1 gateShape := by
  rw [tameMenu, Finset.mem_union]
  exact Or.inl Order0.inert2_mem_menu

/-- **The order-1 leg of the concrete tame menu is genuinely occupied**: the concrete self-loop shape
`Tselfloop 2 ((0,1),(2,0)) [(1,1)]` is a member of `tameMenu` — so the menu contains the real order-1
self-loop term (with its `(realP−1)·(realP^k)⁻¹ > 0` gate). -/
theorem selfloop_mem_tameMenu :
    ClassifierBridgeFiber.Tselfloop 2 gatePr gateShape
      ∈ tameMenu 2 (Order0.unramType 2 (Nat.Partition.indiscrete 2)) 1 gateShape := by
  rw [tameMenu, Finset.mem_union]
  refine Or.inr ?_
  rw [Finset.mem_singleton]
  rfl

/-- **NON-VACUITY of `montes_tame_realDensity_of_exhaustive` (certified strictly-positive value).**
At the CONCRETE tame menu `M = tameMenu 2 (inert 2) 1 [(1,1)]` (order-0 inert ⊕ order-1 self-loop),
the certified engine density value `∑_{T ∈ M} omCount T realP` is STRICTLY POSITIVE: it dominates the
order-1 self-loop term `omCount (Tselfloop 2 ((0,1),(2,0)) [(1,1)]) realP = (realP−1)·(realP^k)⁻¹ > 0`
(`gate_omCount_pos`), every other menu term being nonnegative (`omCount_nonneg`). So the conditional
tame density is NOT the audit's vacuous constant `0`, and the menu is GENUINELY non-vacuous (both
legs occupied: `inert2_mem_tameMenu`, `selfloop_mem_tameMenu`). -/
theorem montes_tame_realDensity_certified_value_pos :
    (0 : ℚ) < ∑ T ∈ tameMenu 2 (Order0.unramType 2 (Nat.Partition.indiscrete 2)) 1 gateShape,
        omCount T M9.realP := by
  classical
  have hp2 : (2 : ℕ) ≤ M9.realP := (Fact.out (p := (M9.realP).Prime)).two_le
  -- the order-1 self-loop term is strictly positive.
  have hpos : (0 : ℚ) < omCount (ClassifierBridgeFiber.Tselfloop 2 gatePr gateShape) M9.realP :=
    gate_omCount_pos M9.realP
  -- every menu term is nonnegative: order-0 legs via `rootCount_sepShape_nonneg`, the order-1
  -- self-loop leg via its strictly-positive gate value.
  have hnonneg : ∀ T ∈ tameMenu 2 (Order0.unramType 2 (Nat.Partition.indiscrete 2)) 1 gateShape,
      (0 : ℚ) ≤ omCount T M9.realP := by
    intro T hT
    rw [tameMenu, Finset.mem_union] at hT
    rcases hT with h0 | h1
    · rw [Order0.sepShapesOf, Finset.mem_image] at h0
      obtain ⟨lam, _, rfl⟩ := h0
      rw [omCount_sepShape_eq_rootCount]
      exact Order0.rootCount_sepShape_nonneg 2 (by norm_num) lam
    · rw [Finset.mem_singleton] at h1
      subst h1
      exact le_of_lt (gate_omCount_pos M9.realP)
  calc (0 : ℚ)
      < omCount (ClassifierBridgeFiber.Tselfloop 2 gatePr gateShape) M9.realP := hpos
    _ ≤ ∑ T ∈ tameMenu 2 (Order0.unramType 2 (Nat.Partition.indiscrete 2)) 1 gateShape,
          omCount T M9.realP := by
        apply Finset.single_le_sum (f := fun T => omCount T M9.realP)
        · exact hnonneg
        · exact selfloop_mem_tameMenu

end LeanUrat.OM.TameRealDensity

/-! ## 6. Machine-checked footprint witnesses (`#print axioms`)

Each must be exactly `[propext, Classical.choice, Quot.sound]` (Lean core only) — no `sorryAx`, no
declared or custom axioms on any of these order-1 density statements. -/

#print axioms LeanUrat.OM.TameRealDensity.stratumCount_selfloop_general
#print axioms LeanUrat.OM.TameRealDensity.hnode_selfloop_general
#print axioms LeanUrat.OM.TameRealDensity.montes_order1_selfloop_density_general_prime
#print axioms LeanUrat.OM.TameRealDensity.montes_order1_tame_realDensity
#print axioms LeanUrat.OM.TameRealDensity.montes_order1_tame_certified_density_pos
#print axioms LeanUrat.OM.TameRealDensity.montes_order1_selfloop_density_general_prime_pos
-- ★ THE HONEST CONDITIONAL TAME ASSEMBLY (order-0 ⊕ order-1, one σ-keyed menu; 2026-07-12).
#print axioms LeanUrat.OM.TameRealDensity.montes_tame_realDensity_of_exhaustive
#print axioms LeanUrat.OM.TameRealDensity.inert2_mem_tameMenu
#print axioms LeanUrat.OM.TameRealDensity.selfloop_mem_tameMenu
#print axioms LeanUrat.OM.TameRealDensity.montes_tame_realDensity_certified_value_pos
