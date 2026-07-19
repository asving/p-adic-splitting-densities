/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.OM.SelfLoopDensityConnect
import LeanUrat.OM.SelfLoopIterate
import LeanUrat.OM.SelfLoopResum
import LeanUrat.OM.OMCountV2

/-!
# SelfLoopFixpoint — the engine self-loop FIXPOINT `b = EFFSEED + r·b` and its closure

**Scope.**  The banked resummation (`SelfLoopResum`, `SelfLoopIterate`, `SelfLoopDensityConnect`)
delivers the self-loop `h_node` density as the ×q-EXPOSED GEOMETRIC DEPTH-SUM
`depth0 · Σ_k (slExposedRatio)^k → depth0 · (countPivot s q)⁻¹`, landing on the engine value
`omChildCount halfCluster 2 = 2/3` at the minimal instance `p = q = 2, s = 2`.

This module banks the DUAL characterization: the same closed value `b = depth0 · (countPivot s q)⁻¹`
is the unique solution of the ENGINE SELF-LOOP FIXPOINT equation

    b = depth0 + slExposedRatio s q · b                               (†)

("self-loop-again is the SAME cluster restarted, weighted by the ×q-exposed per-level ratio
`slExposedRatio = q^{−(s(s+1)/2−1)} = q · slBoxRatio`").  The two are the SAME identity: the
geometric series `Σ_k r^k` is the unique solution of `b = 1 + r·b` (scaled by `depth0`), which is
`(1−r)^{−1} = (countPivot)^{−1}` since `countPivot s q = 1 − slExposedRatio s q`
(`SelfLoopResum.countPivot_eq_one_sub_slExposedRatio`).

**Numerically GATED EXACT** (mu = 2): `EFFSEED = depth0 = (q−1)/q = 1/2`, `slExposedRatio = 1/4`,
fixpoint `1/2 + (1/4)·b = b ⟹ b = 2/3 = omChildCount halfCluster 2` at `p = 2`; `3/4` at `p = 3`.

**What is NEW here (not in the banked modules).**  The banked modules prove the geometric LIMIT but
NOT the self-consistency equation (†).  This module:

* `selfLoopFixpoint_eq` — the closed value satisfies (†): `b = depth0 + r·b`.
* `selfLoopFixpoint_unique` — (†) has a UNIQUE solution for `r ≠ 1` (i.e. `s ≥ 2, q ≥ 2`).
* `selfLoopFixpoint_eq_limit` — the fixpoint value IS the geometric depth-sum limit
  (`SelfLoopResum.tendsto_aggSelfLoopTower` scaled), so `Σ_k` and the fixpoint agree.
* `selfLoopFixpoint_omChild_q2` — the fixpoint value with the CHILD seed `depth0 = (q−1)/q = 1/2`
  is EXACTLY `omChildCount halfCluster 2 = 2/3` (ties to `resum_eq_omChildCount_q2`).
* `stratumCount1_hnode_fixpoint_q2` — the ACTUAL box census `stratumCount1` k = 1 term feeds the
  tower whose limit is the fixpoint value = `omChildCount halfCluster 2` (through the banked Part A
  ratio `stratumCount1_selfLoop_ratio` and the banked full tower limit).

**Honesty.**  This is the mu = 2 discharged instance (both re-gates agree `2/3` at `p = 2`, `3/4` at
`p = 3`; the general-mu seed is NOT re-gated and is NOT formalized).  The FULL box `h_node` still
needs the uniform-in-`(N,k)` per-depth census identity for `k ≥ 2` (the `k`-fold `two_level_census`
induction, `SelfLoopResum.REMAINING_OBLIGATION` item 2) — NOT proven here and NOT proven anywhere in
the banked scripts; the numerics confirm the TARGET but not the induction.  What is landed here is
the fixpoint algebra + its tie to the geometric limit + the k = 1 census anchor.  No
`sorry`/`axiom`/`native_decide`; touches no other module.
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 800000

namespace LeanUrat.OM.SelfLoopFixpoint

open scoped BigOperators
open Filter Topology
open LeanUrat LeanUrat.OM
open LeanUrat.OM.SelfLoopResum

/-! ## 1. The engine self-loop fixpoint value and equation

`selfLoopFixpointValue depth0 s q := depth0 · (countPivot s q)⁻¹` is the closed density value.
The engine self-loop equation is `b = depth0 + slExposedRatio s q · b` (†): the depth-0 seed plus
the self-loop-again term (the SAME cluster restarted, weighted by the ×q-exposed ratio). -/

/-- **The self-loop fixpoint value** `b = depth0 · (countPivot s q)⁻¹` — the closed density of the
self-loop-bearing engine shape (child-normalized with `depth0 = EFFSEED = (q−1)/q` at mu = 2). -/
noncomputable def selfLoopFixpointValue (depth0 : ℚ) (s q : ℕ) : ℚ :=
  depth0 * (MontesAxiom.countPivot s q)⁻¹

/-- **THE ENGINE SELF-LOOP FIXPOINT EQUATION (†), landed.**  The closed value
`b = depth0 · (countPivot s q)⁻¹` satisfies the self-consistency equation

    b = depth0 + slExposedRatio s q · b,

i.e. the density is the depth-0 seed PLUS the self-loop-again term (`slExposedRatio · b` — the SAME
cluster restarted, weighted by the ×q-exposed per-level ratio).  Proof: `countPivot = 1 − r`
(`countPivot_eq_one_sub_slExposedRatio`), so `b = depth0/(1−r)`, and `depth0 + r·b = depth0 + r·depth0/(1−r)
= depth0·(1−r+r)/(1−r) = depth0/(1−r) = b`. -/
theorem selfLoopFixpoint_eq {s q : ℕ} (hq : 2 ≤ q) (hs : 2 ≤ s) (depth0 : ℚ) :
    selfLoopFixpointValue depth0 s q
      = depth0 + slExposedRatio s q * selfLoopFixpointValue depth0 s q := by
  unfold selfLoopFixpointValue
  have hcp : MontesAxiom.countPivot s q = 1 - slExposedRatio s q :=
    countPivot_eq_one_sub_slExposedRatio hs
  have hne : (1 : ℚ) - slExposedRatio s q ≠ 0 :=
    sub_ne_zero.mpr (ne_of_gt (slExposedRatio_lt_one hq hs))
  rw [hcp]
  field_simp
  ring

/-- **UNIQUENESS of the fixpoint (†).**  For `s ≥ 2, q ≥ 2` (so `slExposedRatio < 1 ≠ 1`), the
self-loop equation `b = depth0 + slExposedRatio s q · b` has a UNIQUE solution — necessarily the
closed value `depth0 · (countPivot s q)⁻¹`.  So the fixpoint formulation and the closed density are
one and the same object. -/
theorem selfLoopFixpoint_unique {s q : ℕ} (hq : 2 ≤ q) (hs : 2 ≤ s) (depth0 b : ℚ)
    (hb : b = depth0 + slExposedRatio s q * b) :
    b = selfLoopFixpointValue depth0 s q := by
  unfold selfLoopFixpointValue
  have hcp : MontesAxiom.countPivot s q = 1 - slExposedRatio s q :=
    countPivot_eq_one_sub_slExposedRatio hs
  have hne : (1 : ℚ) - slExposedRatio s q ≠ 0 :=
    sub_ne_zero.mpr (ne_of_gt (slExposedRatio_lt_one hq hs))
  -- b·(1 − r) = depth0
  have hbr : b * (1 - slExposedRatio s q) = depth0 := by linear_combination hb
  rw [hcp]
  field_simp
  linarith [hbr]

/-! ## 2. The fixpoint value IS the geometric depth-sum limit

The banked `SelfLoopResum.tendsto_aggSelfLoopTower` says `Σ_{k<d} r^k → (countPivot)⁻¹`.  Scaling by
`depth0` and identifying with the fixpoint value shows: the geometric self-loop depth-sum and the
self-consistency fixpoint (†) are the SAME identity (S3 core claim: "simultaneously the fixpoint
`b = SEED + r·b` AND the ×q-weighted geometric depth-sum `EFFSEED · Σ_k r^k`"). -/

/-- **THE DUAL IDENTITY (fixpoint = geometric depth-sum).**  The `depth0`-scaled ×q-exposed geometric
self-loop depth-sum `depth0 · Σ_{k<d} (slExposedRatio)^k` converges to the fixpoint value
`selfLoopFixpointValue depth0 s q = depth0 · (countPivot s q)⁻¹`.  This makes precise that the
geometric resummation (banked `tendsto_aggSelfLoopTower`) and the self-consistency fixpoint (†,
`selfLoopFixpoint_eq`) land on the SAME value: the self-loop-again term of (†) is exactly the tail of
the geometric series restarted. -/
theorem selfLoopFixpoint_eq_limit {s q : ℕ} (hq : 2 ≤ q) (hs : 2 ≤ s) (depth0 : ℚ) :
    Tendsto (fun d => depth0 * aggSelfLoopTower s q d) atTop
      (nhds (selfLoopFixpointValue depth0 s q)) := by
  unfold selfLoopFixpointValue
  exact (tendsto_aggSelfLoopTower hq hs).const_mul depth0

/-! ## 3. The minimal-instance ties: fixpoint value = `omChildCount halfCluster 2 = 2/3` -/

/-- **THE ENGINE-VALUE TIE (child-normalized, `2/3`).**  With the CHILD depth-0 seed
`depth0 = EFFSEED = (q−1)/q = 1/2` at `p = q = 2, s = 2`, the self-loop fixpoint value is EXACTLY
`omChildCount halfCluster 2 = 2/3` — the R0-validated size-2 ram-cluster child density.  This lands
the fixpoint (†) on an ACTUAL engine value (`SelfLoopResum.resum_eq_omChildCount_q2`,
`OMCountV2.gate3_cluster_q2`), not a free constant. -/
theorem selfLoopFixpoint_omChild_q2 :
    selfLoopFixpointValue (((2 : ℚ) - 1) / 2) 2 2 = OMCountV2.omChildCount OMCountV2.halfCluster 2 := by
  unfold selfLoopFixpointValue
  exact resum_eq_omChildCount_q2

/-- **The fixpoint (†) at the minimal instance, fully concrete.**  `b = 1/2 + (1/4)·b` at
`depth0 = 1/2`, `slExposedRatio 2 2 = 1/4`, solving to `b = 2/3`.  This is the numerically-gated-exact
self-loop fixpoint the whole S3 structure rests on. -/
theorem selfLoopFixpoint_eq_q2 :
    selfLoopFixpointValue (((2 : ℚ) - 1) / 2) 2 2
      = ((2 : ℚ) - 1) / 2 + slExposedRatio 2 2 * selfLoopFixpointValue (((2 : ℚ) - 1) / 2) 2 2 :=
  selfLoopFixpoint_eq (by norm_num) (by norm_num) (((2 : ℚ) - 1) / 2)

/-- **The fixpoint value is `2/3` explicitly** (the gated numeric).  `depth0 · (countPivot 2 2)⁻¹
= (1/2)·(4/3) = 2/3`. -/
theorem selfLoopFixpointValue_q2 :
    selfLoopFixpointValue (((2 : ℚ) - 1) / 2) 2 2 = 2 / 3 := by
  unfold selfLoopFixpointValue
  rw [gate_resum_q2]; norm_num

/-! ## 4. The ACTUAL box census reaches the fixpoint value = `omChildCount`

`SelfLoopDensityConnect.stratumCount1_selfLoop_ratio` (Part A, banked) gives the ACTUAL order-1 box
census `k = 1` term uniformly in `N`:

    stratumCount1 p s N (selfLoopCell s) = (p−1)·p^{s(N−1)}·slBoxRatio s p.

`SelfLoopDensityConnect.hnode_selfloop_box_order1` (Part D, banked) gives the FULL box-census tower
limit `Σ_k q^k·floorTowerMass k → depth0·(countPivot)⁻¹`.  We package these into the statement that
the ACTUAL box census tower, normalized by the k = 1 census, reaches the FIXPOINT value, which at
mu = 2 is `omChildCount halfCluster 2 = 2/3`. -/

/-- **THE k = 1 CENSUS ANCHOR of the fixpoint seed.**  The ACTUAL box census `stratumCount1` at the
self-loop cell, normalized by the cluster box `p^{s(N−1)}`, is `(p−1)·slBoxRatio s p`, UNIFORMLY in
`N` — the depth-0/depth-1 seed of the fixpoint tower on the genuine count.  At `p = 2, s = 2` this is
`1·(1/8) = 1/8 = slBoxRatio 2 2` (the depth-0 shallow census fraction `sh[0]/ncl` = L2/SHALLOW-to-configs,
gated exact and uniform in `N`).  Reuses `SelfLoopDensityConnect.stratumCount1_selfLoop_ratio`. -/
theorem stratumCount1_seed_ratio {p : ℕ} [Fact (Nat.Prime p)] (s N : ℕ) (hs : 0 < s) (hsN : s < N) :
    (StratumOrder1.stratumCount1 p s N (Drainage.selfLoopCell s) : ℚ) / (p : ℚ) ^ (s * (N - 1))
      = ((p : ℚ) - 1) * slBoxRatio s p := by
  have hpQ : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out (p := Nat.Prime p)).pos.ne'
  have hpow : ((p : ℚ)) ^ (s * (N - 1)) ≠ 0 := pow_ne_zero _ hpQ
  rw [SelfLoopDensityConnect.stratumCount1_selfLoop_ratio p s N hs hsN]
  field_simp

/-- **The k = 1 census anchor at the minimal instance** `p = 2, s = 2`: the normalized self-loop box
census is `1/8` (= `slBoxRatio 2 2`), the (p−1)=1 invisible factor case.  This is the gated-exact
depth-0 shallow census fraction, uniform in `N` (`hsN : 2 < N`). -/
theorem stratumCount1_seed_ratio_q2 {N : ℕ} (hsN : 2 < N) :
    (StratumOrder1.stratumCount1 2 2 N (Drainage.selfLoopCell 2) : ℚ) / ((2 : ℕ) : ℚ) ^ (2 * (N - 1))
      = 1 / 8 := by
  rw [stratumCount1_seed_ratio 2 N (by norm_num) hsN, (slRatios_q2).1]; norm_num

/-- **THE FULL FIXPOINT LIMIT ON THE ACTUAL BOX CENSUS (child-normalized).**  As the readable
self-loop depth `d → ∞`, the ×q-exposed FLOOR box-census tower with the CHILD seed `depth0 = 1/2`
converges to the self-loop FIXPOINT value = `omChildCount halfCluster 2 = 2/3`.  This transports the
banked full box-census tower limit (`SelfLoopDensityConnect.hnode_selfloop_box_child_q2`) through the
fixpoint identification (`selfLoopFixpoint_omChild_q2`): the ACTUAL `stratumCount1`-fed census (whose
per-level ratio is Part A's `slBoxRatio`, uniform in `N`) resums — as the unique fixpoint of (†) — to
the engine value `2/3`.  NOTE: the per-depth mass for `k ≥ 2` still relies on the (unproven) uniform
census induction; what is genuinely closed is the k = 1 anchor + the fixpoint algebra + the abstract
tower limit. -/
theorem stratumCount1_hnode_fixpoint_q2 :
    Tendsto (fun d => ∑ k ∈ Finset.range d, (2 : ℚ) ^ k
        * SelfLoopDensityConnect.floorTowerMass 2 2 (((2 : ℚ) - 1) / 2) k) atTop
      (nhds (selfLoopFixpointValue (((2 : ℚ) - 1) / 2) 2 2)) := by
  rw [selfLoopFixpoint_omChild_q2]
  exact SelfLoopDensityConnect.hnode_selfloop_box_child_q2

/-- **The fixpoint limit reaches `2/3` explicitly** (the genuine engine value, not `1 + r` and not
vacuous): the actual-census fixpoint tower tends to `2/3`. -/
theorem stratumCount1_hnode_fixpoint_q2_value :
    Tendsto (fun d => ∑ k ∈ Finset.range d, (2 : ℚ) ^ k
        * SelfLoopDensityConnect.floorTowerMass 2 2 (((2 : ℚ) - 1) / 2) k) atTop
      (nhds (2 / 3)) := by
  have h := stratumCount1_hnode_fixpoint_q2
  rwa [selfLoopFixpointValue_q2] at h

end LeanUrat.OM.SelfLoopFixpoint
