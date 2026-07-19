/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.OM.SelfLoopResum
import LeanUrat.OM.SelfLoopTower
import LeanUrat.OM.StratumOrder1
import LeanUrat.OM.Drainage
import LeanUrat.OM.OMCountV2

/-!
# SelfLoopIterate — the k-fold self-loop census and the ORDER-1 `h_node` limit
(S2 sub-pieces (iii) the child-as-fresh-cluster census iteration and (vi) the order-1 `h_node`
limit for the self-loop-bearing engine shape)

**Provenance.** `notes/ASSEMBLY_BLUEPRINT.md` §S2 sub-structure `(iii)`+`(vi)` and the `✅ RE-GATE`
block (`/workspace-vast/asving/tmp/phaseb_s2regate/`, PASS at `p ∈ {2,3}`, `n ∈ {2,3}`).  This
module BANKS the `×q`-exposed self-loop TOWER as a per-depth box-mass census tied to
`SelfLoopResum`'s geometric resummation, and assembles the order-1 `h_node` limit for the minimal
self-loop-bearing shape.  It touches NO existing module (additive; owns this file only).

**The minimal instance.**  `p = q = 2`, `s = 2`: the slope-`−1/2` self-loop-bearing engine shape
(`OMCountV2.halfCluster`), where `(p−1) = 1` so the residual-root count is invisible and the
per-depth box mass is a pure power of `q`.

**The three deliverables.**

* **`selfLoopTowerBoxMass` / `boxMass_step` (deliverable 1, the k-fold census).**  The depth-`k`
  self-loop tower box mass fraction is `depth0 · (slBoxRatio)^k`, and — after the `×q^k`
  residue-translate multiplicity (`SelfLoopResum.xqMultiplicity`) — the `×q`-exposed mass is
  `depth0 · (slExposedRatio)^k`.  The recursion `boxMass (k+1) = boxMass k · slBoxRatio` is the
  per-level self-loop step (`slBoxRatio = q^{−s(s+1)/2}`, the bare Vandermonde ratio); the ×q
  multiplicity converts it to `slExposedRatio = q^{−(s(s+1)/2−1)}` = `countPivot`'s ratio.  The
  per-level step is grounded (`p = 2`) in `SelfLoopTower.two_level_census` (ONE self-loop step =
  recenter' + classify1 of the recentered γ-tuple = a fresh cluster) with the `k ≤ 2` anchor
  `SelfLoopTower.gate_iterated_selfLoop`; the CONCRETE box tower at depths `k = 0,1,2,3` reproduces
  the re-gate box counts `1/4, 1/32, 1/256, 1/2048` (`gate_boxTower_depths`).  The GENERAL-`k`
  box-census-over-`classify1` (recentering a recentered polynomial `k`-fold, the `two_level_census`
  `k`-fold composition identifying each fresh unit) is stated precisely in `REMAINING_STEP1` and is
  NOT proven at the box level here; the geometric TOWER it feeds is proven for all `k`.

* **`aggSelfLoopBoxTower` / `aggSelfLoopBoxTower_eq` (deliverable 2, the aggregate over depth).**
  The finite aggregate `Σ_{k<d} (×q-exposed depth-k mass)` = `depth0 · aggSelfLoopTower s q d`, tying
  the per-depth census (1) to `SelfLoopResum.aggSelfLoopTower` (the finite geometric tower).

* **`hnode_selfloop_order1` (deliverable 3, the LIMIT — the payoff).**  As the readable depth
  `d → ∞`, the aggregated `×q`-exposed self-loop tower mass converges to
  `depth0 · (countPivot s q)⁻¹`, which at the minimal instance is exactly the engine value
  `omChildCount(halfCluster, 2) = 2/3` (child-normalized, `depth0 = (q−1)/q`) resp.
  `1/3` (root-normalized, `depth0 = q^{−2}`).  Built from `SelfLoopResum.tendsto_aggSelfLoopTower`
  (the geometric limit, CLOSED) via `Tendsto.const_mul`.  The tail-drainage input
  `Drainage.tendsto_tailDensity_zero` is recorded as the companion vanishing.  This is the order-1
  `h_node` for the self-loop-bearing engine shape — the first genuine cluster-shape `h_node`
  (contingent on `REMAINING_STEP1`, the box-census wiring of the per-depth mass uniformly in `N`).

**Scope / honesty.**  Banked here: (1) the k-fold self-loop TOWER as a geometric box-mass census
with the `×q` multiplicity and the concrete `k ≤ 3` box gates; (2) the aggregate tied to
`aggSelfLoopTower`; (3) the limit `depth0 · (countPivot)⁻¹` and its exact engine tie
`omChildCount halfCluster 2 = 2/3`.  NOT banked (stated precisely in `REMAINING_STEP1`): the
general-`k` box census over the composed `classify1` self-loop tower (the recenter-of-recenter
identification of the fresh unit at each level) — the one genuinely missing lemma, which is S2
sub-piece (iii)'s `two_level_census` `k`-fold induction.  No `sorry`/`axiom`/`native_decide`.

**Gates** (`p = q = 2, s = 2`): box tower `1/4, 1/32, 1/256, 1/2048` (ratio `slBoxRatio = 1/8`);
`×q`-exposed `1/4, 1/16, 1/64, 1/256` (ratio `slExposedRatio = 1/4`); depth-0 root census `q^{−2} =
1/4`, child census `(q−1)/q = 1/2`; limits `1/4·(4/3) = 1/3` (root) and `1/2·(4/3) = 2/3` (child =
`omChildCount halfCluster 2`).
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 800000

namespace LeanUrat.OM.SelfLoopIterate

open scoped BigOperators
open Filter Topology
open LeanUrat LeanUrat.OM
open LeanUrat.OM.SelfLoopResum
open LeanUrat.OM.OMCountV2 (NodeConfig)

/-! ## 1. Deliverable 1: the k-fold self-loop tower as a per-depth box-mass census

The self-loop tower's depth-`k` BOX mass fraction (of the cluster box) is `depth0 · slBoxRatio^k`
— each self-loop level costs the bare Vandermonde ratio `slBoxRatio = q^{−s(s+1)/2}`
(`SelfLoopResum.slBoxRatio`, grounded per-level in `HNode1.selfLoop_coset_index` and, one level
down, `SelfLoopTower.gate_iterated_selfLoop`).  The `depth0` constant is the root census `q^{−2}`
(resp. child census `(q−1)/q`); with the `×q^k` residue-translate multiplicity
(`SelfLoopResum.xqMultiplicity`) the EXPOSED depth-`k` mass is `depth0 · slExposedRatio^k`. -/

/-- **The depth-`k` self-loop tower box mass** (deliverable 1, box-normalized): `depth0 · slBoxRatio^k`.
`depth0` is the depth-0 census constant (root `q^{−2}` or child `(q−1)/q`); each self-loop level
multiplies by `slBoxRatio s q = q^{−s(s+1)/2}` (the bare box Vandermonde ratio). -/
noncomputable def selfLoopTowerBoxMass (s q : ℕ) (depth0 : ℚ) (k : ℕ) : ℚ :=
  depth0 * (slBoxRatio s q) ^ k

/-- **The `×q`-EXPOSED depth-`k` self-loop tower mass** (deliverable 1, exposed): `depth0 ·
slExposedRatio^k`.  By `SelfLoopResum.xqMultiplicity` this is the depth-`k` box mass times the
`×q^k` residue-translate multiplicity — `countPivot`'s ratio per level. -/
noncomputable def selfLoopTowerExposedMass (s q : ℕ) (depth0 : ℚ) (k : ℕ) : ℚ :=
  depth0 * (slExposedRatio s q) ^ k

/-- **The per-level self-loop STEP** (deliverable 1, the recursion): the depth-`(k+1)` box mass is
the depth-`k` mass times `slBoxRatio` — ONE self-loop level costs the bare Vandermonde ratio.  This
is the `k`-fold recursion whose single step is `SelfLoopTower.two_level_census` (the recentered
γ-tuple = a fresh cluster; its `classify1` at the next level is the depth-`(k+1)` read). -/
theorem boxMass_step (s q : ℕ) (depth0 : ℚ) (k : ℕ) :
    selfLoopTowerBoxMass s q depth0 (k + 1)
      = selfLoopTowerBoxMass s q depth0 k * slBoxRatio s q := by
  unfold selfLoopTowerBoxMass
  rw [pow_succ, mul_assoc]

/-- **THE ×q RESIDUE-TRANSLATE CONVERSION at depth `k`** (deliverable 1): the `×q^k` multiplicity
converts the depth-`k` bare box mass into the exposed mass — `q^k · boxMass k = exposedMass k`.
This is `SelfLoopResum.xqMultiplicity` lifted to the per-depth census: the `q` residue-translate
cosets each self-loop level exposes are counted as distinct box strata, converting the bare box
ratio `slBoxRatio = q^{−s(s+1)/2}` into `countPivot`'s `slExposedRatio = q^{−(s(s+1)/2−1)}`. -/
theorem boxMass_xq (s q : ℕ) (hq : 0 < q) (hs : 1 ≤ s) (depth0 : ℚ) (k : ℕ) :
    (q : ℚ) ^ k * selfLoopTowerBoxMass s q depth0 k = selfLoopTowerExposedMass s q depth0 k := by
  unfold selfLoopTowerBoxMass selfLoopTowerExposedMass
  rw [← mul_left_comm, xqMultiplicity s q hq hs k]

/-- The `×q`-exposed tower also satisfies a clean per-level recursion, with ratio `slExposedRatio`
(`countPivot`'s ratio): `exposedMass (k+1) = exposedMass k · slExposedRatio`. -/
theorem exposedMass_step (s q : ℕ) (depth0 : ℚ) (k : ℕ) :
    selfLoopTowerExposedMass s q depth0 (k + 1)
      = selfLoopTowerExposedMass s q depth0 k * slExposedRatio s q := by
  unfold selfLoopTowerExposedMass
  rw [pow_succ, mul_assoc]

/-! ### The concrete box-tower gates at the minimal instance (deliverable 1, box anchor)

At `p = q = 2, s = 2` the depth-0 ROOT census is `q^{−2} = 1/4` (the re-gate `box_naive` depth-0).
The per-level box ratio is `slBoxRatio 2 2 = 1/8` (`SelfLoopResum.slRatios_q2`), so the box tower is
`1/4, 1/32, 1/256, 1/2048` — reproducing the re-gate `s2_regate_report.txt` box-tower table exactly.
-/

/-- **Depth-0 box census gate** (`p = q = 2, s = 2`, root-normalized): `1/4 = q^{−2}`. -/
theorem gate_boxMass_root_q2 :
    selfLoopTowerBoxMass 2 2 (((2 : ℚ) ^ L5fix.selfLoopExponent 2)⁻¹) 0 = 1 / 4 := by
  unfold selfLoopTowerBoxMass L5fix.selfLoopExponent
  norm_num

/-- **The box tower gate at depths `k = 0,1,2,3`** (`p = q = 2, s = 2`, root-normalized): the
depth-`k` box mass is `1/4, 1/32, 1/256, 1/2048` — the re-gate `s2_regate_report.txt` box-tower
table (ratio `slBoxRatio = 1/8` per level).  This grounds the k-fold census against the numeric
gate at the first four depths. -/
theorem gate_boxTower_depths :
    let d0 : ℚ := ((2 : ℚ) ^ L5fix.selfLoopExponent 2)⁻¹
    selfLoopTowerBoxMass 2 2 d0 0 = 1 / 4
      ∧ selfLoopTowerBoxMass 2 2 d0 1 = 1 / 32
      ∧ selfLoopTowerBoxMass 2 2 d0 2 = 1 / 256
      ∧ selfLoopTowerBoxMass 2 2 d0 3 = 1 / 2048 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    · unfold selfLoopTowerBoxMass slBoxRatio L5fix.selfLoopExponent; norm_num

/-- **The `×q`-EXPOSED tower gate at depths `k = 0,1,2,3`** (`p = q = 2, s = 2`, root-normalized):
`1/4, 1/16, 1/64, 1/256` — the box tower times `×q^k`, ratio `slExposedRatio = 1/4` per level
(`countPivot`'s ratio).  This is the re-gate's `×q`-exposed self-loop series. -/
theorem gate_exposedTower_depths :
    let d0 : ℚ := ((2 : ℚ) ^ L5fix.selfLoopExponent 2)⁻¹
    selfLoopTowerExposedMass 2 2 d0 0 = 1 / 4
      ∧ selfLoopTowerExposedMass 2 2 d0 1 = 1 / 16
      ∧ selfLoopTowerExposedMass 2 2 d0 2 = 1 / 64
      ∧ selfLoopTowerExposedMass 2 2 d0 3 = 1 / 256 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    · unfold selfLoopTowerExposedMass slExposedRatio L5fix.selfLoopExponent; norm_num

/-- **The concrete box tower is grounded, `k ≤ 2`, in `SelfLoopTower.gate_iterated_selfLoop`.**  The
`k = 2` iterated self-loop mass (TWO successive self-loop reads at `(2,2,5)`) has box count `4`, and
`4 · 2^(2·(selfLoopExponent 2 + 1)) = 2^8 = #clusterBox` — so the depth-2 box mass FRACTION is
`slBoxRatio 2 2 ^ 2 = (1/8)^2 = 1/64` of the cluster box (`SelfLoopResum.gate_iterated_selfLoop_k2_exp`,
which reads `gate_iterated_selfLoop`).  The depth-2 tower term `slBoxRatio^2 = 1/64` matches. -/
theorem gate_boxTower_k2_grounded :
    slBoxRatio 2 2 ^ 2 = 1 / 64
      ∧ 2 * (L5fix.selfLoopExponent 2 + 1) = 6 :=
  ⟨(gate_iterated_selfLoop_k2_exp).2, (gate_iterated_selfLoop_k2_exp).1⟩

/-! ## 2. Deliverable 2: the aggregate over depth, tied to `SelfLoopResum.aggSelfLoopTower`

The aggregated `×q`-exposed self-loop tower mass through depth `d` is `depth0 · aggSelfLoopTower s q
d` = `depth0 · Σ_{k<d} slExposedRatio^k` — the per-depth census (1) summed, folding in the
`×q`-per-level multiplicity via `xqMultiplicity` (`SelfLoopResum.aggSelfLoopTower_eq_xq`). -/

/-- **The aggregated `×q`-exposed self-loop tower to depth `d`** (deliverable 2): `Σ_{k<d}
exposedMass k` = `depth0 · Σ_{k<d} slExposedRatio^k`. -/
noncomputable def aggSelfLoopBoxTower (s q : ℕ) (depth0 : ℚ) (d : ℕ) : ℚ :=
  ∑ k ∈ Finset.range d, selfLoopTowerExposedMass s q depth0 k

/-- **Deliverable 2 (the aggregate = `depth0 · aggSelfLoopTower`).**  The aggregated `×q`-exposed
box tower is `depth0` times `SelfLoopResum.aggSelfLoopTower` — tying the per-depth census (1) to the
finite geometric resummation.  The `×q`-per-level multiplicity is folded in via
`selfLoopTowerExposedMass = depth0 · slExposedRatio^k` (each term = `depth0 · q^k · slBoxRatio^k` by
`xqMultiplicity`). -/
theorem aggSelfLoopBoxTower_eq (s q : ℕ) (depth0 : ℚ) (d : ℕ) :
    aggSelfLoopBoxTower s q depth0 d = depth0 * aggSelfLoopTower s q d := by
  unfold aggSelfLoopBoxTower aggSelfLoopTower selfLoopTowerExposedMass
  rw [Finset.mul_sum]

/-- **Deliverable 2 (the `×q`-per-level form).**  The aggregate written as the `×q`-weighted bare
box masses: `Σ_{k<d} q^k · boxMass k` — the per-depth census (1) with the residue-translate
multiplicity `q^k` exposed at each level (`boxMass_xq`). -/
theorem aggSelfLoopBoxTower_eq_xq (s q : ℕ) (hq : 0 < q) (hs : 1 ≤ s) (depth0 : ℚ) (d : ℕ) :
    aggSelfLoopBoxTower s q depth0 d
      = ∑ k ∈ Finset.range d, (q : ℚ) ^ k * selfLoopTowerBoxMass s q depth0 k := by
  unfold aggSelfLoopBoxTower
  exact Finset.sum_congr rfl fun k _ => (boxMass_xq s q hq hs depth0 k).symm

/-- **The aggregate gate at `p = q = 2, s = 2`** (root-normalized, depth `d = 3`): the `×q`-exposed
partial sum is `1/4 + 1/16 + 1/64 = 21/64` — the re-gate `N=6/7 AGG` value. -/
theorem gate_aggBoxTower_d3_q2 :
    aggSelfLoopBoxTower 2 2 (((2 : ℚ) ^ L5fix.selfLoopExponent 2)⁻¹) 3 = 21 / 64 := by
  unfold aggSelfLoopBoxTower selfLoopTowerExposedMass slExposedRatio L5fix.selfLoopExponent
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one]
  norm_num

/-! ## 3. Deliverable 3: the ORDER-1 `h_node` LIMIT for the self-loop-bearing shape (the payoff)

As the readable self-loop depth `d → ∞`, the aggregated `×q`-exposed tower mass
`aggSelfLoopBoxTower s q depth0 d → depth0 · (countPivot s q)⁻¹` — the geometric self-loop
resummation (`SelfLoopResum.tendsto_aggSelfLoopTower`) scaled by the depth-0 census.  At the
minimal instance this lands EXACTLY on the engine value `omChildCount(halfCluster, 2) = 2/3`
(child-normalized) resp. the root value `1/3`. -/

/-- **THE ORDER-1 `h_node` LIMIT (deliverable 3, the payoff).**  The aggregated `×q`-exposed
self-loop tower mass converges to `depth0 · (countPivot s q)⁻¹` as the depth `d → ∞`.  This is the
`×q`-corrected geometric resummation of the self-loop tower (ratio `slExposedRatio =
q^{−(s(s+1)/2−1)}`, NOT the bare box `slBoxRatio`), scaled by the depth-0 census — the order-1
`h_node` density of the self-loop-bearing engine shape.  Built from
`SelfLoopResum.tendsto_aggSelfLoopTower` (CLOSED) via `Filter.Tendsto.const_mul`. -/
theorem hnode_selfloop_order1 {s q : ℕ} (hq : 2 ≤ q) (hs : 2 ≤ s) (depth0 : ℚ) :
    Tendsto (fun d => aggSelfLoopBoxTower s q depth0 d) atTop
      (nhds (depth0 * (MontesAxiom.countPivot s q)⁻¹)) := by
  have h := (tendsto_aggSelfLoopTower hq hs).const_mul depth0
  refine h.congr fun d => ?_
  rw [aggSelfLoopBoxTower_eq]

/-- **THE ENGINE TIE (deliverable 3 gate, child-normalized).**  At the minimal instance `p = q = 2,
s = 2` with the CHILD depth-0 census `depth0 = (q−1)/q = 1/2`, the `h_node` limit is EXACTLY
`omChildCount(halfCluster, 2) = 2/3` — the R0-validated size-2 ram-cluster child density
(`OMCountV2.gate3_cluster_q2`), tied via `SelfLoopResum.resum_eq_omChildCount_q2`.  This lands the
order-1 self-loop `h_node` on an actual engine value, not a free constant. -/
theorem hnode_selfloop_limit_child_q2 :
    Tendsto (fun d => aggSelfLoopBoxTower 2 2 (((2 : ℚ) - 1) / 2) d) atTop
      (nhds (OMCountV2.omChildCount OMCountV2.halfCluster 2)) := by
  have h := hnode_selfloop_order1 (s := 2) (q := 2) (by norm_num) (by norm_num) (((2 : ℚ) - 1) / 2)
  rwa [resum_eq_omChildCount_q2] at h

/-- **THE ENGINE TIE (deliverable 3 gate, root-normalized).**  At the minimal instance with the
ROOT depth-0 census `depth0 = q^{−2} = 1/4`, the `h_node` limit is `1/3` — the re-gate
`omCount(ram_root) = 1/(q+1)` value (`SelfLoopResum.resum_omCount_root_q2`). -/
theorem hnode_selfloop_limit_root_q2 :
    Tendsto (fun d => aggSelfLoopBoxTower 2 2 (((2 : ℚ) ^ L5fix.selfLoopExponent 2)⁻¹) d) atTop
      (nhds (1 / 3)) := by
  have h := hnode_selfloop_order1 (s := 2) (q := 2) (by norm_num) (by norm_num)
    (((2 : ℚ) ^ L5fix.selfLoopExponent 2)⁻¹)
  rwa [resum_omCount_root_q2] at h

/-- **The companion TAIL VANISHING** (the drainage input, deliverable 3): the order-1 undecided TAIL
mass (unreadable `a₀`) tends to `0` as `N → ∞` (`Drainage.tendsto_tailDensity_zero`).  Together with
`hnode_selfloop_order1` (the self-loop tower resummation), the FULL undecided mass drains to the
resummed self-loop value — the tail dies by level refinement, the self-loop tower resums to
`countPivot`.  We record the tail limit here as the drainage half of the limit assembly. -/
theorem tail_drains_q2 :
    Tendsto (fun N => Drainage.tailDensity 2 2 N) atTop (nhds 0) :=
  Drainage.tendsto_tailDensity_zero 2 2 (by norm_num)

/-! ## 4. `REMAINING_STEP1` — the box-census wiring, stated precisely (NOT proven here)

`REMAINING_STEP1` (S2 sub-piece (iii), the general step).  Deliverables 1–3 above bank the
`×q`-exposed self-loop TOWER as a geometric box-mass census (the per-depth mass `slBoxRatio^k`, the
`×q` multiplicity `slExposedRatio^k`, the aggregate `depth0 · aggSelfLoopTower`, and its limit
`depth0 · (countPivot)⁻¹` = `omChildCount halfCluster 2 = 2/3`), with the concrete box tower gated at
depths `k ≤ 3` (`gate_boxTower_depths`) and grounded per-level at `k ≤ 2`
(`gate_boxTower_k2_grounded`, from `SelfLoopTower.gate_iterated_selfLoop`).

What remains to make `hnode_selfloop_order1` a statement about the actual box census
`StratumOrder1.stratumCount1` (rather than the abstract per-depth mass): the UNIFORM-in-`N` box
census identity at every depth `k`,

    Σ_{c : selfLoopDepthOf c = k} stratumCount1 s N c
      = depth0Census · p^(s(N−1)) · (slBoxRatio s p)^k · p^k,

whose SINGLE step (`k → k+1`) is `SelfLoopTower.two_level_census` — the recentered γ-tuple
`gpoly γ = recenter' f` IS a fresh size-`s` cluster box element, and its `classify1` at the next
level gives the depth-`(k+1)` structure.  The general `k` needs `two_level_census` iterated `k`-fold:
recentering a recentered polynomial, identifying the fresh unit `c` at each level (the
"child-as-fresh-cluster" identification).  Currently only `k ≤ 2` is concretely discharged
(`SelfLoopTower.gate_iterated_selfLoop` = the `k = 2` iterate; `SelfLoopTower.gate_threeway_N5` = the
one-level three-way split `decided / self-loop-again / tail`).  The `k`-fold composition is the one
genuinely missing lemma — the tower recursion `SelfLoopTower.two_level_census` applied at every depth,
NOT the geometric limit (which is CLOSED here via `tendsto_aggSelfLoopTower`).

The named INPUTS for the missing lemma (all banked): `SelfLoopTower.two_level_census` (the single
step), `SelfLoopTower.recenter'` / `SelfLoopTower.gpoly` (the recentering into the fresh size-`s`
box), `SelfLoopTower.gate_iterated_selfLoop` (the `k = 2` anchor), `HNode1.selfLoop_coset_index` /
`Drainage.card_selfLoopFiber_index` (the per-level box index `p^{s(s+1)/2}`), `StratumOrder1.stratumCount1`
/ `StratumOrder1.stratumCount1_partition` (the box census + its partition), and
`DevelopTower.card_r_level_census` (the abstract `k`-fold tower recursion, should the concrete
recenter-composition be routed through the tower ring).  Then `hnode_selfloop_order1` (banked) +
`Drainage.tendsto_tailDensity_zero` (banked, `tail_drains_q2`) + `Filter.Tendsto.add` closes the
full box `h_node` limit.

Generalization to general `s`: `slBoxRatio`/`slExposedRatio` are already stated for general `s` (via
`L5fix.selfLoopExponent s`), and `xqMultiplicity`/`hnode_selfloop_order1` hold verbatim for general
`s ≥ 2, q ≥ 2`.  For `p ≥ 3` the `(p−1)^k` residual-root multiplicity re-enters (invisible only at
`p = 2`); it rides along as an extra per-level `(p−1)` factor in the depth-0 census `mCell =
(p−1)`-shaped — the ratios are unchanged. -/

end LeanUrat.OM.SelfLoopIterate
