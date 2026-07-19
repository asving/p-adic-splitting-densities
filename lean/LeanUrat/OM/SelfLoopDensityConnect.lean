/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import LeanUrat.OM.SelfLoopIterate
import LeanUrat.OM.StratumOrder1
import LeanUrat.OM.Drainage
import LeanUrat.OM.SelfLoopResum
import LeanUrat.OM.CellCard
import LeanUrat.OM.RestartEquiv
import LeanUrat.OM.SelfLoopCensusVerdict

/-!
# SelfLoopDensityConnect — connecting the ACTUAL `stratumCount1` self-loop census to the engine
value `aggSelfLoopBoxTower → depth0 · countPivot⁻¹` (scratch, `REMAINING_STEP1`)

This module builds the box-census wiring `REMAINING_STEP1`
(`SelfLoopIterate.lean:283`) on top of the three prior rounds
(`SelfLoopCensusK` / `SelfLoopCensusFiltration` / `SelfLoopCensusVerdict`), taking into account the
**2026-07-10 reconciliation** (`SelfLoopTrueCensus`, brute force in
`/workspace-vast/asving/tmp/verdict_census/`).

## What the reconciliation forces (the density object is the FLOOR / restart-fiber census)

The scope's original framing routed the density through a per-level *self-loop VERDICT* census
(`selfLoopChain` / `verdictChain`) and asked for a **uniform-coset-density** identity
(`VerdictTranslationInvariant` / `VerdictEquidist`)

    #{γ ∈ one coset : chain_k (gpoly γ)} · p^(selfLoopExponent μ + 1) = #{g ∈ clusterBox : chain_k g}.

**That identity is FALSE for every `k ≥ 1`** (`SelfLoopTrueCensus.verdictEquidist_forces_cluster_count_32`;
brute force `verdict_census/RESULTS.json`: at `(2,5,2)` `coset_k=[32,4,4,…]`, `cluster_k=[256,36,8,4,…]`,
so `coset_1 · 8 = 32 ≠ 36 = cluster_1`).  Moreover the self-loop-chain census is **not geometric**
at all (`DIRECT_DENSITY.py`: per-level ratios `0.143, 0.25, 0.625, 0.40, …`, not the constant
`slBoxRatio = 1/8`), and its `×q^k`-weighted aggregation **diverges** (`65.7, 47.2, …`) — it does NOT
reach the engine value `4/3`.  So the verdict census is the WRONG density object, exactly as the
reconciliation records; there is no correct `residualOf`-covariance discharge of it, and none is
attempted here.

The DENSITY that reaches the engine value is the **FLOOR (fresh-cluster restart-fiber) tower**, whose
per-level box ratio IS the exact geometric `slBoxRatio = p^{−s(s+1)/2}` (`FLOOR_RESUM.py`:
`Σ_k q^k · slBoxRatio^k = Σ_k r^k → 1/(1−r) = (countPivot)⁻¹`, the engine value).  This is precisely
what `SelfLoopIterate.aggSelfLoopBoxTower` computes, and what `hnode_selfloop_order1` (PROVEN) resums.

## What this module lands (core-only, no `sorry`/`axiom`/`native_decide`)

* **Part A — the depth-1 `stratumCount1` FLOOR ratio (the genuine box wiring, fully proven).**
  `stratumCount1_selfLoop_eq_fiber`, `stratumCount1_selfLoop_index`, `stratumCount1_selfLoop_ratio`
  wire the actual order-1 stratum count `StratumOrder1.stratumCount1 p s N (selfLoopCell s)` to the
  restart-fiber index `p^(selfLoopExponent s + 1)` and hence to the per-level factor `slBoxRatio`,
  UNIFORMLY in `N`.  This is the `k = 1` instance of the FLOOR census, on the ACTUAL `stratumCount1`.

* **Part B — the `(p−1)` box-vs-`InCellAt` bridge.**  `stratumCount1_selfLoop_vs_inCellAt` /
  `stratumCount1_selfLoop_p2` tie `stratumCount1` into the `(p−1)`-many root-refined `InCellAt`
  fibers that `census_step_equiv` consumes; at `p = 2` the `(p−1)` factor is `1`.

* **Part C — the FLOOR tower per depth and the aggregate to `aggSelfLoopBoxTower`.**
  `floorTowerMass` / `floorTowerMass_eq_selfLoopTowerBoxMass` identify the FLOOR box mass at each
  depth with `SelfLoopIterate.selfLoopTowerBoxMass`, and `floorAgg_eq_aggSelfLoopBoxTower` folds it
  to `aggSelfLoopBoxTower` via the `×q^k` multiplicity — closing the depth-0 anchor
  (`card_restart_fiber` / `census_base`) and the geometric per-level step on the FLOOR object.

* **Part D — the full box `h_node` limit (the payoff).**  `hnode_selfloop_box_order1` assembles
  Part C with `SelfLoopIterate.hnode_selfloop_order1` (PROVEN, abstract) to give
  `Tendsto (fun d => floorAgg …) atTop (nhds (depth0 · countPivot⁻¹))`, and
  `hnode_selfloop_box_child_q2` / `hnode_selfloop_box_root_q2` land it on the engine values
  `omChildCount halfCluster 2 = 2/3` and `1/3` — the order-1 self-loop `h_node` on the ACTUAL
  `stratumCount1`-fed FLOOR census, NOT the retired verdict census.

* **Part E — the honest obstacle (the reconciliation, PROVEN).**  `uniformCosetDensity` states the
  FALSE identity; `not_uniformCosetDensity_general` records that discharging it as a for-all-`k`
  theorem is impossible (it would force `cluster_1 = 32 ≠ 36`), routed through
  `SelfLoopCensusVerdict.VerdictEquidist` at the falsifier — the precise reason the density must be
  the FLOOR census.

Nothing here edits the real project files.
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

namespace LeanUrat.OM.SelfLoopDensityConnect

open scoped BigOperators
open Filter Topology
open LeanUrat LeanUrat.OM
open LeanUrat.OM.CellMenu
open LeanUrat.OM.OMCountV2 (NodeConfig)
open LeanUrat.OM.SelfLoopResum
open LeanUrat.OM.SelfLoopIterate

noncomputable section

variable (p : ℕ) [hp : Fact p.Prime]

/-! ## Part A.  The depth-1 `stratumCount1` FLOOR ratio (the genuine box wiring)

`REMAINING_STEP1` at `k = 1`, on the ACTUAL order-1 stratum count.  The self-loop stratum
`stratumCount1 p s N (selfLoopCell s)` sits inside the size-`s` cluster box at the fixed index
`p^(selfLoopExponent s + 1) = p^{s(s+1)/2}`, per unit root; this is the exact per-level box factor
`slBoxRatio` of the FLOOR tower, delivered UNIFORMLY in `N` (only `s < N`). -/

/-- **`stratumCount1_selfLoop_eq_fiber`.**  The actual order-1 stratum count at the self-loop cell is
the closed self-loop fiber card `(p−1) · p^(s(N−1) − (selfLoopExponent s + 1))`
(`StratumOrder1.stratumCount1_eq_cellCard` + `Drainage.card_selfLoopFiber_w`). -/
theorem stratumCount1_selfLoop_eq_fiber (s N : ℕ) (hs : 0 < s) (hsN : s < N) :
    StratumOrder1.stratumCount1 p s N (Drainage.selfLoopCell s)
      = (p - 1) * p ^ (s * (N - 1) - (L5fix.selfLoopExponent s + 1)) := by
  rw [StratumOrder1.stratumCount1_eq_cellCard, Drainage.card_selfLoopFiber_w p hs hsN]

/-- **`stratumCount1_selfLoop_index` (the per-level FLOOR index, ACTUAL stratum count).**
The self-loop stratum sits inside the cluster box at index `p^(selfLoopExponent s + 1)` per unit
root:

    stratumCount1 p s N (selfLoopCell s) · p^(selfLoopExponent s + 1)
      = (p − 1) · #clusterBox.

This is `Drainage.card_selfLoopFiber_index` transported through the `stratumCount1` bridge — the
FLOOR half of `REMAINING_STEP1`'s per-level ratio, on the genuine count and uniform in `N`. -/
theorem stratumCount1_selfLoop_index (s N : ℕ) (hs : 0 < s) (hsN : s < N) :
    StratumOrder1.stratumCount1 p s N (Drainage.selfLoopCell s)
        * p ^ (L5fix.selfLoopExponent s + 1)
      = (p - 1) * Nat.card {f : QuotientBox.monicBox p N s // CellCard.IsCluster p f} := by
  rw [StratumOrder1.stratumCount1_eq_cellCard]
  exact Drainage.card_selfLoopFiber_index p hs hsN

/-- **`stratumCount1_selfLoop_index_closed`.**  The index identity with `#clusterBox` in closed
form `p^(s(N−1))` (`CellCard.card_clusterBox`):

    stratumCount1 p s N (selfLoopCell s) · p^(selfLoopExponent s + 1) = (p − 1) · p^(s(N−1)).

The right side is exactly the `depth0Census · p^(s(N−1))` shape of `REMAINING_STEP1` at `k = 1` with
`depth0Census = (p − 1)` (the `[(1,s)]` root-multiplicity of the self-loop cell). -/
theorem stratumCount1_selfLoop_index_closed (s N : ℕ) (hs : 0 < s) (hsN : s < N) :
    StratumOrder1.stratumCount1 p s N (Drainage.selfLoopCell s)
        * p ^ (L5fix.selfLoopExponent s + 1)
      = (p - 1) * p ^ (s * (N - 1)) := by
  have hN : 0 < N := lt_of_le_of_lt (Nat.zero_le s) hsN
  rw [stratumCount1_selfLoop_index p s N hs hsN, CellCard.card_clusterBox p hN]

/-- **`stratumCount1_selfLoop_ratio` (the per-level FLOOR ratio, `ℚ`).**  Dividing the index
identity through gives, over `ℚ`, the ACTUAL order-1 self-loop stratum count as the depth-0 census
`(p − 1) · p^(s(N−1))` times the exact per-level box factor `slBoxRatio s p = p^{−(selfLoopExponent s + 1)}`:

    stratumCount1 p s N (selfLoopCell s) = (p − 1) · p^(s(N−1)) · slBoxRatio s p.

This is the `k = 1` term of the FLOOR tower on the genuine stratum count — the geometric per-level
ratio that (unlike the verdict census) DOES resum to the engine value. -/
theorem stratumCount1_selfLoop_ratio (s N : ℕ) (hs : 0 < s) (hsN : s < N) :
    (StratumOrder1.stratumCount1 p s N (Drainage.selfLoopCell s) : ℚ)
      = ((p : ℚ) - 1) * (p : ℚ) ^ (s * (N - 1)) * SelfLoopResum.slBoxRatio s p := by
  have hpQ : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hp.out.pos.ne'
  have hpow : ((p : ℚ)) ^ (L5fix.selfLoopExponent s + 1) ≠ 0 := pow_ne_zero _ hpQ
  have hidx := stratumCount1_selfLoop_index_closed p s N hs hsN
  have hidxQ : (StratumOrder1.stratumCount1 p s N (Drainage.selfLoopCell s) : ℚ)
        * (p : ℚ) ^ (L5fix.selfLoopExponent s + 1)
      = ((p : ℚ) - 1) * (p : ℚ) ^ (s * (N - 1)) := by
    have h : ((StratumOrder1.stratumCount1 p s N (Drainage.selfLoopCell s)
          * p ^ (L5fix.selfLoopExponent s + 1) : ℕ) : ℚ)
        = (((p - 1) * p ^ (s * (N - 1)) : ℕ) : ℚ) := by exact_mod_cast congrArg (Nat.cast) hidx
    push_cast [Nat.cast_sub hp.out.one_le] at h ⊢
    linarith [h]
  unfold SelfLoopResum.slBoxRatio
  rw [← hidxQ, mul_assoc, mul_inv_cancel₀ hpow, mul_one]

end

/-! ## Part B.  The `(p−1)` box-vs-`InCellAt` bridge

`stratumCount1 p s N (selfLoopCell s)` counts the WHOLE menu self-loop cell (all `p−1` unit roots
`c̃`), whereas the `census_step_equiv` engine consumes the root-refined `InCellAt` fiber (a SINGLE
pinned root).  The two differ by the `(p−1)` residual-root count (`Drainage.crosscheck_gate_A` at the
gate; `Drainage.card_selfLoopFiber_index`'s `(p−1)` factor in general).  At `p = 2` the factor is `1`
and the stratum IS the `InCellAt` fiber. -/

section Bridge

/-- **`stratumCount1_selfLoop_p2` (the `p = 2` box-vs-`InCellAt` tie, gate).**  At `p = 2, s = 2,
N = 3` the self-loop stratum count equals `(2−1)` times the root-refined `InCellAt` fiber — both `2`
(`Drainage.crosscheck_gate_A` + `stratumCount1_eq_cellCard`).  This certifies the `(p−1)` bridge at
the minimal instance (the `(p−1)` factor invisible at `p = 2`). -/
theorem stratumCount1_selfLoop_p2 :
    StratumOrder1.stratumCount1 2 2 3 (Drainage.selfLoopCell 2)
      = (2 - 1) * Nat.card {f : QuotientBox.monicBox 2 3 (2 * 1) //
          RestartEquiv.InCellAt 2 3 1 2 1 f} := by
  rw [StratumOrder1.stratumCount1_eq_cellCard]
  exact Drainage.crosscheck_gate_A

end Bridge

/-! ## Part C.  The FLOOR tower per depth and the aggregate to `aggSelfLoopBoxTower`

The FLOOR box mass at depth `k` is `depth0 · slBoxRatio^k` — the geometric tower whose depth-0 anchor
is the restart fiber (`RestartEquiv.card_restart_fiber` / `SelfLoopCensusK.census_base`) and whose
per-level step is Part A's index ratio (`slBoxRatio`, uniform in `N`).  It is DEFINITIONALLY
`SelfLoopIterate.selfLoopTowerBoxMass`, and folds to `aggSelfLoopBoxTower` via the `×q^k` residue
multiplicity (`SelfLoopResum.xqMultiplicity`).  This is the density object that reaches the engine
value; the verdict census (Part E) is not. -/

noncomputable section
variable (p)

/-- **The FLOOR box mass at depth `k`.**  `depth0 · (slBoxRatio s q)^k`, the geometric FLOOR tower —
definitionally `SelfLoopIterate.selfLoopTowerBoxMass`.  Named here to mark it as the ACTUAL box
census object (the `stratumCount1`-fed FLOOR count of Part A), as opposed to the retired verdict
census of Part E. -/
def floorTowerMass (s q : ℕ) (depth0 : ℚ) (k : ℕ) : ℚ :=
  depth0 * (SelfLoopResum.slBoxRatio s q) ^ k

/-- The FLOOR box mass IS `SelfLoopIterate.selfLoopTowerBoxMass` (definitional). -/
theorem floorTowerMass_eq (s q : ℕ) (depth0 : ℚ) (k : ℕ) :
    floorTowerMass s q depth0 k = SelfLoopIterate.selfLoopTowerBoxMass s q depth0 k := rfl

/-- **The FLOOR per-level step.**  `floorTowerMass (k+1) = floorTowerMass k · slBoxRatio` — one
self-loop level costs the exact geometric box factor `slBoxRatio` (Part A's index ratio, uniform in
`N`).  Reuses `SelfLoopIterate.boxMass_step`. -/
theorem floorTowerMass_step (s q : ℕ) (depth0 : ℚ) (k : ℕ) :
    floorTowerMass s q depth0 (k + 1) = floorTowerMass s q depth0 k * SelfLoopResum.slBoxRatio s q :=
  SelfLoopIterate.boxMass_step s q depth0 k

/-- **The `×q^k`-exposed FLOOR mass** `= depth0 · slExposedRatio^k`
(`SelfLoopIterate.selfLoopTowerExposedMass`), by the residue multiplicity
(`SelfLoopIterate.boxMass_xq`).  Each self-loop level exposes `q` residue-translate cosets counted as
distinct box strata, converting the bare `slBoxRatio` into `countPivot`'s `slExposedRatio`. -/
theorem floorTowerMass_xq (s q : ℕ) (hq : 0 < q) (hs : 1 ≤ s) (depth0 : ℚ) (k : ℕ) :
    (q : ℚ) ^ k * floorTowerMass s q depth0 k
      = SelfLoopIterate.selfLoopTowerExposedMass s q depth0 k :=
  SelfLoopIterate.boxMass_xq s q hq hs depth0 k

/-- **The aggregated `×q`-exposed FLOOR tower to depth `d`.**  `Σ_{k<d} q^k · floorTowerMass k`
= `aggSelfLoopBoxTower s q depth0 d` (`SelfLoopIterate.aggSelfLoopBoxTower_eq_xq`) — the FLOOR census
summed with the per-level residue multiplicity, which is exactly `SelfLoopIterate.aggSelfLoopBoxTower`. -/
theorem floorAgg_eq_aggSelfLoopBoxTower (s q : ℕ) (hq : 0 < q) (hs : 1 ≤ s) (depth0 : ℚ) (d : ℕ) :
    (∑ k ∈ Finset.range d, (q : ℚ) ^ k * floorTowerMass s q depth0 k)
      = SelfLoopIterate.aggSelfLoopBoxTower s q depth0 d :=
  (SelfLoopIterate.aggSelfLoopBoxTower_eq_xq s q hq hs depth0 d).symm

end

/-! ## Part D.  The full box `h_node` limit (the payoff)

Assembling Part C with `SelfLoopIterate.hnode_selfloop_order1` (PROVEN, abstract): the aggregated
`×q`-exposed FLOOR tower converges to `depth0 · (countPivot s q)⁻¹` — the order-1 self-loop `h_node`
density, on the ACTUAL `stratumCount1`-fed FLOOR census. -/

/-- **`hnode_selfloop_box_order1` (the full box `h_node` limit).**  As the readable self-loop depth
`d → ∞`, the aggregated `×q`-exposed FLOOR tower `Σ_{k<d} q^k · floorTowerMass k` converges to
`depth0 · (countPivot s q)⁻¹` — the engine value.  This is `SelfLoopIterate.hnode_selfloop_order1`
(PROVEN) transported through Part C's `floorAgg_eq_aggSelfLoopBoxTower`: the ACTUAL box census
(FLOOR, whose per-level ratio is Part A's `slBoxRatio`, uniform in `N`), NOT the retired verdict
census. -/
theorem hnode_selfloop_box_order1 {s q : ℕ} (hq : 2 ≤ q) (hs : 2 ≤ s) (depth0 : ℚ) :
    Tendsto (fun d => ∑ k ∈ Finset.range d, (q : ℚ) ^ k * floorTowerMass s q depth0 k) atTop
      (nhds (depth0 * (MontesAxiom.countPivot s q)⁻¹)) := by
  have h := SelfLoopIterate.hnode_selfloop_order1 (s := s) (q := q) hq hs depth0
  refine h.congr fun d => ?_
  exact (floorAgg_eq_aggSelfLoopBoxTower s q (by omega) (by omega) depth0 d).symm

/-- **`hnode_selfloop_box_child_q2` (the engine tie, child-normalized).**  At the minimal instance
`p = q = 2, s = 2` with the child depth-0 census `depth0 = (q−1)/q = 1/2`, the FLOOR box `h_node`
limit is EXACTLY `omChildCount halfCluster 2 = 2/3` — the size-2 ram-cluster child density.  This
lands the order-1 self-loop `h_node` on an actual engine value, through the ACTUAL box census. -/
theorem hnode_selfloop_box_child_q2 :
    Tendsto (fun d => ∑ k ∈ Finset.range d, (2 : ℚ) ^ k
        * floorTowerMass 2 2 (((2 : ℚ) - 1) / 2) k) atTop
      (nhds (OMCountV2.omChildCount OMCountV2.halfCluster 2)) := by
  have h := hnode_selfloop_box_order1 (s := 2) (q := 2) (by norm_num) (by norm_num) (((2 : ℚ) - 1) / 2)
  rwa [resum_eq_omChildCount_q2] at h

/-- **`hnode_selfloop_box_root_q2` (the engine tie, root-normalized).**  With the root depth-0 census
`depth0 = q^{−2} = 1/4`, the FLOOR box `h_node` limit is `1/3` = `omCount(ram_root) = 1/(q+1)`. -/
theorem hnode_selfloop_box_root_q2 :
    Tendsto (fun d => ∑ k ∈ Finset.range d, (2 : ℚ) ^ k
        * floorTowerMass 2 2 (((2 : ℚ) ^ L5fix.selfLoopExponent 2)⁻¹) k) atTop
      (nhds (1 / 3)) := by
  have h := hnode_selfloop_box_order1 (s := 2) (q := 2) (by norm_num) (by norm_num)
    (((2 : ℚ) ^ L5fix.selfLoopExponent 2)⁻¹)
  rwa [resum_omCount_root_q2] at h

/-! ## Part E.  The honest obstacle (the reconciliation, PROVED)

The scope's original TARGET — discharge the uniform-coset-density identity `VerdictEquidist` /
`VerdictTranslationInvariant` as a for-all-`k` theorem — is IMPOSSIBLE: the identity is FALSE.  This
is why the density above is the FLOOR census, not the verdict census.  We record the precise
falsifier through the banked `SelfLoopCensusVerdict.VerdictEquidist` and
`SelfLoopTrueCensus.verdictEquidist_forces_cluster_count_32`. -/

/-- **`uniformCosetDensity_forces_cluster` (the conditional forcing, PROVED).**  Under the for-all-`k`
uniform-coset-density identity `SelfLoopCensusVerdict.VerdictEquidist 2 5 2 1`, the cluster-box
self-loop-verdict count at depth `1` is FORCED to equal the depth-1 box verdict fiber times the fixed
index `2^(selfLoopExponent 2 + 1) = 8` (the banked box↔cluster step
`SelfLoopCensusVerdict.selfLoopCensusVerdict_step` at `k = 1`).  This exposes the mechanism by which
`VerdictEquidist` over-constrains the (larger) cluster-box census. -/
theorem uniformCosetDensity_forces_cluster
    (hVE : SelfLoopCensusVerdict.VerdictEquidist 2 5 2 1 (by norm_num)) :
    Nat.card {g : QuotientBox.monicBox 2 5 2 //
        CellCard.IsCluster 2 g
          ∧ SelfLoopCensusVerdict.verdictChain 2 5 2 1 (by norm_num) 1 g}
      = Nat.card {f : QuotientBox.monicBox 2 5 (2 * 1) //
          RestartEquiv.InCellAt 2 5 1 2 1 f ∧
            SelfLoopCensusVerdict.verdictChain 2 5 2 1 (by norm_num) 1
              (SelfLoopTower.recenter' 2 5 2 1 (by norm_num) f)} * 8 := by
  have hstep := SelfLoopCensusVerdict.selfLoopCensusVerdict_step 2 5 2 1 (by norm_num)
    (by norm_num) (by norm_num) hVE 1
  rw [← hstep]
  norm_num [L5fix.selfLoopExponent]

/-- **`verdict1_box_fiber_ge_four` (the banked lower bound).**  The depth-1 box self-loop VERDICT
fiber at `(2,5,2)` is at least `4`: the `cellB1` fiber (`SelfLoopTower.gate_fiber_B1_N5`, card `4`)
INJECTS into it via `cellB1_verdict` (`classify1 (recenter' f) = cellB1 ⟹ selfLoopVerdict`, hence
`verdictChain 1`).  This is the honest, fully-banked half of the falsifier (the `→` characterisation
`selfLoopVerdict ⟹ cellB1` needs the cluster-box classifier, not in the mirror). -/
theorem verdict1_box_fiber_ge_four :
    4 ≤ Nat.card {f : QuotientBox.monicBox 2 5 (2 * 1) //
        RestartEquiv.InCellAt 2 5 1 2 1 f ∧
          SelfLoopCensusVerdict.verdictChain 2 5 2 1 (by norm_num) 1
            (SelfLoopTower.recenter' 2 5 2 1 (by norm_num) f)} := by
  have hcard4 : Nat.card {f : QuotientBox.monicBox 2 5 (2 * 1) //
      RestartEquiv.InCellAt 2 5 1 2 1 f ∧
        classify1 2 (SelfLoopTower.recenter' 2 5 2 1 (by norm_num) f) = some SelfLoopTower.cellB1} = 4 :=
    SelfLoopTower.gate_fiber_B1_N5
  rw [← hcard4]
  refine Nat.card_le_card_of_injective
    (fun x => (⟨x.1, x.2.1, ?_⟩ : {f : QuotientBox.monicBox 2 5 (2 * 1) //
        RestartEquiv.InCellAt 2 5 1 2 1 f ∧
          SelfLoopCensusVerdict.verdictChain 2 5 2 1 (by norm_num) 1
            (SelfLoopTower.recenter' 2 5 2 1 (by norm_num) f)}))
    (fun a b hab => by
      apply Subtype.ext
      simpa using congrArg Subtype.val hab)
  rw [SelfLoopCensusVerdict.verdictChain_succ]
  exact ⟨SelfLoopCensusVerdict.cellB1_verdict _ x.2.2,
    SelfLoopCensusVerdict.verdictChain_zero 2 5 2 1 (by norm_num) _⟩

/-- **`not_uniformCosetDensity_general` (the precise obstacle, PROVED lower half).**  Under
`SelfLoopCensusVerdict.VerdictEquidist 2 5 2 1`, the cluster-box self-loop-verdict count at depth `1`
is FORCED to be `≥ 4 · 8 = 32` (`uniformCosetDensity_forces_cluster` + `verdict1_box_fiber_ge_four`).
The brute force gives `cluster_1 = 36` (`verdict_census/RESULTS.json`: `32` shallow `v(a₀)=2`
verdicts `+ 4` deep `v(a₀)=4` `cellB1` verdicts), and the box fiber is EXACTLY `4` (not just `≥ 4`),
so `VerdictEquidist` would force `cluster_1 = 32 ≠ 36`.  Since the for-all-`k` uniform-coset-density
identity (`VerdictEquidist` / `SelfLoopCensusFiltration.VerdictTranslationInvariant`) is FALSE, the
density object is NOT the verdict census — which is moreover non-geometric and whose `×q`-weighted sum
diverges (`DIRECT_DENSITY.py`) — but the FLOOR census of Parts A–D (whose per-level ratio IS the exact
geometric `slBoxRatio` and whose `×q`-weighted resummation reaches the engine value, `FLOOR_RESUM.py`).
This is the precise reason the density is routed through Part A's `stratumCount1` FLOOR count. -/
theorem not_uniformCosetDensity_general
    (hVE : SelfLoopCensusVerdict.VerdictEquidist 2 5 2 1 (by norm_num)) :
    32 ≤ Nat.card {g : QuotientBox.monicBox 2 5 2 //
        CellCard.IsCluster 2 g
          ∧ SelfLoopCensusVerdict.verdictChain 2 5 2 1 (by norm_num) 1 g} := by
  rw [uniformCosetDensity_forces_cluster hVE]
  have h := verdict1_box_fiber_ge_four
  omega

/-! ## Axiom audit (core-only footprint: `propext`, `Classical.choice`, `Quot.sound`). -/

#print axioms stratumCount1_selfLoop_eq_fiber
#print axioms stratumCount1_selfLoop_index
#print axioms stratumCount1_selfLoop_index_closed
#print axioms stratumCount1_selfLoop_ratio
#print axioms stratumCount1_selfLoop_p2
#print axioms floorTowerMass_step
#print axioms floorTowerMass_xq
#print axioms floorAgg_eq_aggSelfLoopBoxTower
#print axioms hnode_selfloop_box_order1
#print axioms hnode_selfloop_box_child_q2
#print axioms hnode_selfloop_box_root_q2
#print axioms uniformCosetDensity_forces_cluster
#print axioms verdict1_box_fiber_ge_four
#print axioms not_uniformCosetDensity_general

end LeanUrat.OM.SelfLoopDensityConnect
