/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.OM.SelfLoopFixpointGeneralMu
import LeanUrat.OM.SelfLoopDensityConnect
import LeanUrat.OM.SelfLoopIterate
import LeanUrat.OM.SelfLoopResum
import LeanUrat.OM.OMCountV2

/-!
# P4 — SelfLoopCensusReduction: the self-loop census → fixpoint-VALUE reduction

Leaf module (nothing imports it back).  Safe front-facing packaging of already-proved
self-loop lemmas into named, core-only reduction theorems — the analogue of
`FineCellResultant.lean` (build #56).  Every result here is a thin wiring of PROVEN,
core-only lemmas from the imported modules; no new mathematical content, no new axioms.

## What these theorems SAY (and just as importantly, what they do NOT say)

The self-loop-bearing engine shape has a closed density value
`SelfLoopFixpoint.selfLoopFixpointValue depth0 s q := depth0 · (countPivot s q)⁻¹`.  The
`hnode_selfloop_box_order1` engine (PROVEN core-only in `SelfLoopDensityConnect`) shows the
aggregated `×q`-exposed FLOOR tower `Σ_{k<d} q^k · floorTowerMass s q depth0 k` converges,
as the readable self-loop depth `d → ∞`, to exactly this value.  This module names the
depth-limit ↔ fixpoint-value tie for general `s ≥ 2, q ≥ 2, depth0`, restates it on the
`aggSelfLoopBoxTower` census object, and lands one concrete non-vacuous instance at `μ = 3`
(`p = q = 2`), value `20/31`.

* **P4-1** `floorAgg_reduces_to_fixpoint_generalMu`: the `×q`-exposed FLOOR tower census
  `Σ_{k<d} q^k · floorTowerMass s q depth0 k` tends to `selfLoopFixpointValue depth0 s q`.
  This is `hnode_selfloop_box_order1` with its RHS spelled as the named fixpoint value (the
  two are definitionally equal, `selfLoopFixpointValue depth0 s q = depth0 · (countPivot s q)⁻¹`).

* **P4-2** `census_reduces_to_fixpoint_generalMu`: the SAME limit stated on the census object
  `SelfLoopIterate.aggSelfLoopBoxTower s q depth0 d` — `aggSelfLoopBoxTower s q depth0 d →
  selfLoopFixpointValue depth0 s q`.  Obtained from P4-1 by `.congr` through
  `SelfLoopDensityConnect.floorAgg_eq_aggSelfLoopBoxTower` (the two census spellings are
  equal termwise).

* **P4-3** `census_reduction_mu3_value`: the concrete `μ = 3` instance at `p = q = 2` with the
  gated engine seed `depth0 = EFFSEED3 2 = 5/8`; the FLOOR tower census tends to `20/31`.  A
  non-vacuity anchor landing an actual nonzero value.

* **P4-4** `census_reduction_mu2_child_q2`: the `μ = 2` engine tie, child-normalized — at
  `p = q = 2, s = 2, depth0 = (q−1)/q = 1/2` the FLOOR tower census tends to
  `OMCountV2.omChildCount OMCountV2.halfCluster 2` (the size-2 ram-cluster child density
  `2/3`), landing the limit on an actual `omCount`-object value.

## HONEST GUARDRAILS (do not read more into these than is stated)

* These are census → fixpoint-VALUE reduction lemmas.  They do **NOT** prove the `k ≥ 2`
  uniform-in-`N` box census (that the ACTUAL `StratumOrder1.stratumCount1` aggregate equals
  `depth0 · p^…`), which remains **OPEN**.  The `floorTowerMass`/`aggSelfLoopBoxTower` objects
  are the FLOOR census whose per-level ratio (`slBoxRatio`, Part A) is the exponent-proven
  index; the theorems here connect that FLOOR census to the closed value, nothing more.
* They do **NOT** discharge `SelfLoopHNode` or prove `hNodeLimit`.
* `EFFSEED3` is **NOT** derived here; it is the gated engine seed supplied as `depth0` (the
  `μ = 3` SHALLOW_3 const term, harness/PARI-gated), passed in.
* They do **NOT** shrink or eliminate `AX_cellRecursion`; the `×q` per-level transport stays
  the recorded measure axiom (exponent-proven only) inside the imported engine, and these
  reduction lemmas do not touch it — its footprint simply does not appear because the
  transport enters only through the exponent-level `boxMass_xq`, which is core-only.

Non-vacuity: P4-1/P4-2/P4-4 are over general `s ≥ 2, q ≥ 2, depth0` (P4-4 concretized at
`q = 2`); P4-3 lands the concrete nonzero value `20/31`.

No `sorry`, no `axiom`, no `native_decide`; all public results elaborate with core-only
axiom footprints (`propext`, `Classical.choice`, `Quot.sound`) — see `#print axioms` at end.
-/

set_option linter.style.longLine false
set_option linter.style.header false

namespace LeanUrat.OM.SelfLoopCensusReduction

open scoped BigOperators
open Filter Topology
open LeanUrat LeanUrat.OM

/-! ## P4-1 — the `×q`-exposed FLOOR tower census reduces to the fixpoint value (general `μ`) -/

/-- **P4-1 (general `μ` reduction, FLOOR-tower spelling).**  For general `s ≥ 2, q ≥ 2` and any
depth-0 seed `depth0`, the aggregated `×q`-exposed FLOOR tower census
`Σ_{k<d} q^k · floorTowerMass s q depth0 k` converges, as the readable self-loop depth `d → ∞`,
to the closed self-loop fixpoint VALUE `selfLoopFixpointValue depth0 s q`.

This is precisely `SelfLoopDensityConnect.hnode_selfloop_box_order1` (PROVEN, core-only) with its
RHS `depth0 · (countPivot s q)⁻¹` written as the named `SelfLoopFixpoint.selfLoopFixpointValue`
(the two are definitionally equal — `selfLoopFixpointValue depth0 s q := depth0 · (countPivot s q)⁻¹`).

HONEST SCOPE: this is a census → fixpoint-value tie only.  It does NOT prove the `k ≥ 2`
uniform-in-`N` box census; the FLOOR tower object here is the exponent-level FLOOR count, not the
actual `stratumCount1` aggregate. -/
theorem floorAgg_reduces_to_fixpoint_generalMu {s q : ℕ} (hq : 2 ≤ q) (hs : 2 ≤ s) (depth0 : ℚ) :
    Tendsto (fun d => ∑ k ∈ Finset.range d, (q : ℚ) ^ k * SelfLoopDensityConnect.floorTowerMass s q depth0 k)
      atTop (nhds (SelfLoopFixpoint.selfLoopFixpointValue depth0 s q)) := by
  -- `selfLoopFixpointValue depth0 s q` is defeq the RHS of `hnode_selfloop_box_order1`.
  show Tendsto _ atTop (nhds (depth0 * (MontesAxiom.countPivot s q)⁻¹))
  exact SelfLoopDensityConnect.hnode_selfloop_box_order1 hq hs depth0

/-! ## P4-2 — the same reduction stated on the `aggSelfLoopBoxTower` census object -/

/-- **P4-2 (general `μ` reduction, census-object spelling).**  The same limit as P4-1 stated on the
census object `SelfLoopIterate.aggSelfLoopBoxTower s q depth0 d`:
`aggSelfLoopBoxTower s q depth0 d → selfLoopFixpointValue depth0 s q` as `d → ∞`, for general
`s ≥ 2, q ≥ 2` and any `depth0`.

Obtained from P4-1 by `.congr` through `SelfLoopDensityConnect.floorAgg_eq_aggSelfLoopBoxTower`, which
equates the FLOOR-tower sum with `aggSelfLoopBoxTower` termwise.

Same HONEST SCOPE as P4-1: census → fixpoint-value only; the `k ≥ 2` uniform-in-`N` census stays OPEN. -/
theorem census_reduces_to_fixpoint_generalMu {s q : ℕ} (hq : 2 ≤ q) (hs : 2 ≤ s) (depth0 : ℚ) :
    Tendsto (fun d => SelfLoopIterate.aggSelfLoopBoxTower s q depth0 d)
      atTop (nhds (SelfLoopFixpoint.selfLoopFixpointValue depth0 s q)) := by
  refine (floorAgg_reduces_to_fixpoint_generalMu hq hs depth0).congr fun d => ?_
  exact SelfLoopDensityConnect.floorAgg_eq_aggSelfLoopBoxTower s q (by omega) (by omega) depth0 d

/-! ## P4-3 — the concrete `μ = 3` worked instance (`p = q = 2`), value `20/31` -/

/-- **P4-3 (`μ = 3` non-vacuity anchor).**  At `μ = 3, p = q = 2` with the gated engine seed
`depth0 = EFFSEED3 2 = 5/8`, the `×q`-exposed FLOOR tower census
`Σ_{k<d} 2^k · floorTowerMass 3 2 (EFFSEED3 2) k` converges to the concrete self-loop density `20/31`.

Wires P4-1 at `s = 3, q = 2, depth0 = EFFSEED3 2` with `SelfLoopFixpointGeneralMu.selfLoopFixpointValue_mu3_q2`
(`selfLoopFixpointValue (EFFSEED3 2) 3 2 = 20/31`, MC-backed).

HONEST SCOPE: `EFFSEED3` is the gated `μ = 3` engine seed SUPPLIED as `depth0`, not derived here; this
lands the reduction on a concrete nonzero value only. -/
theorem census_reduction_mu3_value :
    Tendsto (fun d => ∑ k ∈ Finset.range d,
        (2 : ℚ) ^ k * SelfLoopDensityConnect.floorTowerMass 3 2 (SelfLoopFixpointGeneralMu.EFFSEED3 2) k)
      atTop (nhds (20 / 31)) := by
  have h := floorAgg_reduces_to_fixpoint_generalMu (s := 3) (q := 2) (by norm_num) (by norm_num)
    (SelfLoopFixpointGeneralMu.EFFSEED3 2)
  rwa [SelfLoopFixpointGeneralMu.selfLoopFixpointValue_mu3_q2] at h

/-! ## P4-4 — the `μ = 2` engine tie (child-normalized, `p = q = 2`), value `omChildCount` -/

/-- **P4-4 (`μ = 2` engine tie, child-normalized).**  At `μ = 2, p = q = 2` with the child depth-0
census `depth0 = (q−1)/q = 1/2`, the `×q`-exposed FLOOR tower census converges to
`OMCountV2.omChildCount OMCountV2.halfCluster 2` — the size-2 ram-cluster child density `2/3`,
an actual `omCount`-object value.

Wires P4-1 at `s = 2, q = 2, depth0 = (2−1)/2` with `SelfLoopResum.resum_eq_omChildCount_q2`
(`((2−1)/2) · (countPivot 2 2)⁻¹ = omChildCount halfCluster 2`), which is defeq the fixpoint value. -/
theorem census_reduction_mu2_child_q2 :
    Tendsto (fun d => ∑ k ∈ Finset.range d,
        (2 : ℚ) ^ k * SelfLoopDensityConnect.floorTowerMass 2 2 (((2 : ℚ) - 1) / 2) k)
      atTop (nhds (OMCountV2.omChildCount OMCountV2.halfCluster 2)) := by
  have h := floorAgg_reduces_to_fixpoint_generalMu (s := 2) (q := 2) (by norm_num) (by norm_num)
    (((2 : ℚ) - 1) / 2)
  -- `selfLoopFixpointValue ((2-1)/2) 2 2` is defeq `((2-1)/2) · (countPivot 2 2)⁻¹`.
  rw [show SelfLoopFixpoint.selfLoopFixpointValue (((2 : ℚ) - 1) / 2) 2 2
        = ((2 : ℚ) - 1) / 2 * (MontesAxiom.countPivot 2 2)⁻¹ from rfl,
    SelfLoopResum.resum_eq_omChildCount_q2] at h
  exact h

#print axioms floorAgg_reduces_to_fixpoint_generalMu
#print axioms census_reduces_to_fixpoint_generalMu
#print axioms census_reduction_mu3_value
#print axioms census_reduction_mu2_child_q2

end LeanUrat.OM.SelfLoopCensusReduction
