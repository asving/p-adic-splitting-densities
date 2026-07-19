/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.OM.StratumOrder1
import LeanUrat.OM.Drainage
import LeanUrat.OM.SelfLoopTower
import LeanUrat.OM.OMCountV2

/-!
# SelfLoopResum — the ×q self-loop resummation, the CRUX of the order-1 `h_node` discharge
(S2 sub-pieces (ii) the residue-translate multiplicity and (v) the geometric self-loop resummation)

**Provenance.** `notes/ASSEMBLY_BLUEPRINT.md` §S2 (CORRECTED 2026-07-07 by the gate).  The naive
per-box-classify limit `stratumCount(T_box,N)/q^{nN}` does NOT converge to `omCount(T)` for cluster
(self-loop-bearing) shapes: the box self-loop tower ratio is the bare Vandermonde Jacobian
`q^{−s(s+1)/2}` (= `q^{−3}` at `s = 2`), whereas `omCount`'s `countPivot(s)=1−q^{−(s(s+1)/2−1)}`
assumes ratio `q^{−(s(s+1)/2−1)}` (= `q^{−2}`).  The RECONCILIATION: `omCount` computes the density
in the `M_e` cluster measure, which *identifies* the `q` residue-translate cosets of each self-loop
level; the box `Nat.card` counts those `q` cosets as `q` DISTINCT box strata.  So the `h_node`
target is the AGGREGATE over the residue-translate cosets: `Σ_{T_box ↦ T} stratumCount / q^{nN}`, and
the per-level factor becomes `q · q^{−s(s+1)/2} = q^{−(s(s+1)/2−1)}` = exactly `countPivot`'s exponent.

This module BANKS the load-bearing structural content of that reconciliation at the **minimal
instance** `p = 2, s = 2` (the slope-`−1/2` self-loop-bearing engine shape), the `(p−1)=1` case
where the residual-root count is invisible and the per-depth box mass is a pure power of `q`:

* **`xqMultiplicity` (deliverable 1, the ×q residue-translate multiplicity).**  The exact algebraic
  content of the correction: at each self-loop level the engine exposes `q` residue-translate cosets
  the box collapses, so `q^k · (q^{−B})^k = (q^{−(B−1)})^k` — the ×q per level converts the bare box
  self-loop ratio `q^{−B}` (`B = s(s+1)/2`) into the exposed ratio `q^{−(B−1)}` = `countPivot`'s.
  `slBoxRatio`/`slExposedRatio` name the two ratios; `xqMultiplicity` is the per-level conversion.

* **`aggSelfLoopTower` + `aggSelfLoopTower_eq` (deliverable 2, the finite self-loop tower).**  The
  cluster-box-normalized aggregated self-loop tower to depth `d`: `Σ_{k<d} (slExposedRatio)^k`, the
  finite `×q`-exposed resummation.  Grounded per-level in the concrete `HNode1.selfLoop_coset_index`
  (the box self-loop coset sits in the cluster box at index exactly `p^{selfLoopExponent s + 1}` =
  `p^{s(s+1)/2}`) and `SelfLoopTower.gate_iterated_selfLoop` (the `k = 2` iterate).

* **`tendsto_aggSelfLoopTower` (deliverable 3, the geometric self-loop resummation limit).**  As
  `d → ∞`, `Σ_{k<d} (slExposedRatio)^k → (1 − slExposedRatio)⁻¹ = (countPivot s q)⁻¹`.  At
  `p = q = 2, s = 2` this is `1/(1−q^{−2}) = 4/3 = (countPivot 2 2)⁻¹` (`gate_resum_q2`).

* **`omCount` tie (the gate).**  The RE-GATE value `omCount(ram_root) = 1/(q+1) = 1/3` at `p = 2`
  is the ROOT-normalized resummation `q^{−(s(s+1)/2−1)} · (countPivot s q)⁻¹`
  (`resum_omCount_root_q2`), and the CHILD value `omChildCount(ram) = q/(q+1) = 2/3` is the
  cluster-census-normalized resummation `((q−1)/q) · (countPivot s q)⁻¹` (`resum_omChild_q2`) — the
  depth-0 census times the ×q-exposed geometric factor.  These pin the resummation to the actual
  engine `omCount`/`omChildCount` values (`gate3_cluster_q2` = `2/3` in `OMCountV2`).

**Scope / honesty.**  This banks (1) the ×q multiplicity, (2) the finite resummation, and (3) the
geometric limit at the minimal instance, together with the exact numeric ties to `countPivot`,
`omCount`, and `omChildCount`.  The remaining `h_node`-assembly obligation — wiring the box census
`stratumCount1`/`aggStratum` into the per-depth mass `(slBoxRatio)^k` UNIFORMLY in `N` (via a
`stratumCount1`-level self-loop-depth reader `engineShapeOf`, feeding the recenter/restart tower of
`SelfLoopTower.two_level_census` at every depth, not just `k ≤ 2`) — is stated precisely in the
`REMAINING_OBLIGATION` docstring below; it is the general-`(s, engine-shape)` step and is NOT proven
here.  No `sorry`/`axiom`/`native_decide`; touches no other module.

**Gates** (`p = q = 2, s = 2`): `slBoxRatio = q^{−3} = 1/8`; `slExposedRatio = q^{−2} = 1/4`;
`(countPivot 2 2)⁻¹ = 4/3`; root tie `q^{−2}·(4/3) = 1/3`; child tie `(1/2)·(4/3) = 2/3`.
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 800000

namespace LeanUrat.OM.SelfLoopResum

open scoped BigOperators
open Filter Topology
open LeanUrat LeanUrat.OM
open LeanUrat.OM.OMCountV2 (NodeConfig)

/-! ## 1. The two self-loop ratios and the ×q residue-translate multiplicity (deliverable 1)

The bare BOX self-loop step ratio is the Vandermonde Jacobian `q^{−s(s+1)/2}`; the ×q-EXPOSED
ratio (after the residue-translate multiplicity) is `q^{−(s(s+1)/2−1)}` = `q^{−selfLoopExponent s}`.
`selfLoopExponent s = s(s+1)/2 − 1`, so `selfLoopExponent s + 1 = s(s+1)/2` (the box exponent) for
`s ≥ 1`. -/

/-- The **bare box self-loop ratio** `q^{−s(s+1)/2}` (= `q^{−(selfLoopExponent s + 1)}`): the
per-self-loop-level index of the box coset inside the cluster box, `HNode1.selfLoop_coset_index`. -/
noncomputable def slBoxRatio (s q : ℕ) : ℚ := (((q : ℚ) ^ (L5fix.selfLoopExponent s + 1)))⁻¹

/-- The **×q-exposed self-loop ratio** `q^{−(s(s+1)/2−1)}` (= `q^{−selfLoopExponent s}`): the bare
box ratio after the `q` residue-translate cosets each self-loop level exposes are counted as
distinct strata (the `M_e` measure integrates over them).  This is `countPivot`'s ratio. -/
noncomputable def slExposedRatio (s q : ℕ) : ℚ := (((q : ℚ) ^ (L5fix.selfLoopExponent s)))⁻¹

/-- **THE ×q RESIDUE-TRANSLATE MULTIPLICITY (deliverable 1).**  At each self-loop level the engine
exposes `q` residue-translate cosets (the `q` new residues the descent creates) that the box census
collapses into one stratum.  The per-level conversion is EXACTLY `q^k · (q^{−B})^k = (q^{−(B−1)})^k`
with `B = selfLoopExponent s + 1 = s(s+1)/2`: multiplying the depth-`k` bare box mass `slBoxRatio^k`
by the `×q^k` multiplicity gives the exposed mass `slExposedRatio^k`.  This is the algebraic heart of
the §S2 correction: it converts the bare Vandermonde ratio `q^{−s(s+1)/2}` into `countPivot`'s
`q^{−(s(s+1)/2−1)}`. -/
theorem xqMultiplicity (s q : ℕ) (hq : 0 < q) (hs : 1 ≤ s) (k : ℕ) :
    (q : ℚ) ^ k * (slBoxRatio s q) ^ k = (slExposedRatio s q) ^ k := by
  have hqQ : (q : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  -- `selfLoopExponent s + 1 = (selfLoopExponent s) + 1`, and `q · q^{−(B)} = q^{−(B−1)}` per level.
  unfold slBoxRatio slExposedRatio
  rw [← mul_pow]
  congr 1
  -- `q * (q ^ (w+1))⁻¹ = (q ^ w)⁻¹`
  rw [inv_eq_one_div, inv_eq_one_div, mul_one_div,
    div_eq_div_iff (pow_ne_zero _ hqQ) (pow_ne_zero _ hqQ), one_mul, ← pow_succ']

/-- The two ratios at the minimal instance `p = q = 2, s = 2`: `slBoxRatio = q^{−3} = 1/8`,
`slExposedRatio = q^{−2} = 1/4`.  (The re-gate `box_selfloop_ratio_s2 = 1/8`,
`exposed_selfloop_ratio_s2 = 1/4`.) -/
theorem slRatios_q2 : slBoxRatio 2 2 = 1 / 8 ∧ slExposedRatio 2 2 = 1 / 4 := by
  refine ⟨?_, ?_⟩
  · unfold slBoxRatio L5fix.selfLoopExponent; norm_num
  · unfold slExposedRatio L5fix.selfLoopExponent; norm_num

/-- **The ×q multiplicity, gated at `p = q = 2, s = 2` per depth-`k`**: `q^k · (1/8)^k = (1/4)^k`,
i.e. the `×2^k` residue-translate multiplicity converts the box ratio `2^{−3}` into `2^{−2}`. -/
theorem gate_xqMultiplicity_q2 (k : ℕ) :
    (2 : ℚ) ^ k * (slBoxRatio 2 2) ^ k = (slExposedRatio 2 2) ^ k :=
  xqMultiplicity 2 2 (by norm_num) (by norm_num) k

/-! ## 2. The `slExposedRatio` is a genuine geometric ratio, `= countPivot`'s ratio -/

/-- `slExposedRatio s q` is nonnegative (for `q ≥ 1`). -/
theorem slExposedRatio_nonneg {s q : ℕ} (hq : 0 < q) : 0 ≤ slExposedRatio s q := by
  unfold slExposedRatio
  positivity

/-- `slExposedRatio s q < 1` for `q ≥ 2` and `s ≥ 2` (so `selfLoopExponent s ≥ 2 > 0`): the
geometric ratio is a genuine contraction, `q^{−selfLoopExponent s} < 1`. -/
theorem slExposedRatio_lt_one {s q : ℕ} (hq : 2 ≤ q) (hs : 2 ≤ s) :
    slExposedRatio s q < 1 := by
  unfold slExposedRatio
  have hw : 1 ≤ L5fix.selfLoopExponent s := le_trans (by norm_num) (Drainage.selfLoopExponent_ge hs)
  have hqQ : (1 : ℚ) < (q : ℚ) := by exact_mod_cast hq
  have hpow : (1 : ℚ) < (q : ℚ) ^ (L5fix.selfLoopExponent s) :=
    one_lt_pow₀ hqQ (by omega)
  rw [inv_lt_one_iff₀]
  right; exact hpow

/-- **`countPivot`'s ratio IS `slExposedRatio`**: `countPivot s q = 1 − slExposedRatio s q` for
`s ≥ 2`.  (`MontesAxiom.countPivot s q = 1 − q^{−selfLoopExponent s}` at `s ≥ 2`.) -/
theorem countPivot_eq_one_sub_slExposedRatio {s q : ℕ} (hs : 2 ≤ s) :
    MontesAxiom.countPivot s q = 1 - slExposedRatio s q := by
  unfold MontesAxiom.countPivot slExposedRatio
  rw [if_pos hs]

/-! ## 3. The finite self-loop tower (deliverable 2) and its geometric limit (deliverable 3) -/

/-- **THE FINITE SELF-LOOP TOWER (deliverable 2, cluster-box-normalized).**  The aggregated self-loop
mass through the first `d` self-loop levels, `×q`-exposed: `Σ_{k<d} (slExposedRatio s q)^k`.  By
`xqMultiplicity` each summand `(slExposedRatio)^k = q^k · (slBoxRatio)^k` is the `×q^k`-weighted bare
box self-loop mass `(slBoxRatio)^k` — the per-level content grounded (at the minimal instance) by
`HNode1.selfLoop_coset_index` (per-level box index `p^{s(s+1)/2}`) and
`SelfLoopTower.gate_iterated_selfLoop` (the `k = 2` iterate).  The depth-`0` term is `1` (the whole
cluster box). -/
noncomputable def aggSelfLoopTower (s q d : ℕ) : ℚ :=
  ∑ k ∈ Finset.range d, (slExposedRatio s q) ^ k

/-- The tower written as the `×q`-exposed weighting of the bare box masses (deliverable 2's
`×q`-per-level form): `aggSelfLoopTower = Σ_{k<d} q^k · (slBoxRatio)^k`. -/
theorem aggSelfLoopTower_eq_xq (s q d : ℕ) (hq : 0 < q) (hs : 1 ≤ s) :
    aggSelfLoopTower s q d = ∑ k ∈ Finset.range d, (q : ℚ) ^ k * (slBoxRatio s q) ^ k := by
  unfold aggSelfLoopTower
  exact Finset.sum_congr rfl fun k _ => (xqMultiplicity s q hq hs k).symm

/-- **THE FINITE RESUMMATION, closed form (deliverable 2).**  For `s ≥ 2, q ≥ 2`
(so `slExposedRatio ≠ 1`), the finite `×q`-exposed self-loop tower has the geometric closed form
`(slExposedRatio^d − 1)/(slExposedRatio − 1)`. -/
theorem aggSelfLoopTower_closed {s q d : ℕ} (hq : 2 ≤ q) (hs : 2 ≤ s) :
    aggSelfLoopTower s q d
      = ((slExposedRatio s q) ^ d - 1) / (slExposedRatio s q - 1) := by
  unfold aggSelfLoopTower
  exact geom_sum_eq (ne_of_lt (slExposedRatio_lt_one hq hs)) d

/-- **THE GEOMETRIC SELF-LOOP RESUMMATION LIMIT (deliverable 3, cluster-box-normalized).**  As the
self-loop depth `d → ∞`, the `×q`-exposed self-loop tower converges to the geometric sum
`(1 − slExposedRatio s q)⁻¹ = (countPivot s q)⁻¹`.  This is the `1/(1−r)` resummation of the
self-loop geometric series with the `×q`-CORRECTED ratio `r = slExposedRatio = q^{−(s(s+1)/2−1)}`
(NOT the bare box `q^{−s(s+1)/2}`) — the exact mechanism by which the box self-loop tower resums to
`countPivot`.  Built from `geom_sum_eq` + `tendsto_pow_atTop_nhds_zero_of_lt_one` over `ℚ`. -/
theorem tendsto_aggSelfLoopTower {s q : ℕ} (hq : 2 ≤ q) (hs : 2 ≤ s) :
    Tendsto (fun d => aggSelfLoopTower s q d) atTop (nhds (MontesAxiom.countPivot s q)⁻¹) := by
  set r := slExposedRatio s q with hr
  have h0 : 0 ≤ r := slExposedRatio_nonneg (by omega)
  have h1 : r < 1 := slExposedRatio_lt_one hq hs
  have hne : r ≠ 1 := ne_of_lt h1
  have hclosed : ∀ d, aggSelfLoopTower s q d = (r ^ d - 1) / (r - 1) := fun d => by
    rw [hr]; exact aggSelfLoopTower_closed hq hs
  have hpow : Tendsto (fun d : ℕ => r ^ d) atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one h0 h1
  have hlim : Tendsto (fun d : ℕ => (r ^ d - 1) / (r - 1)) atTop (nhds ((0 - 1) / (r - 1))) :=
    (hpow.sub_const 1).div_const _
  have hval : (0 - 1) / (r - 1) = (MontesAxiom.countPivot s q)⁻¹ := by
    rw [countPivot_eq_one_sub_slExposedRatio hs, ← hr, zero_sub, neg_div, ← neg_sub 1 r,
      div_neg, neg_neg, one_div]
  rw [hval] at hlim
  exact hlim.congr (fun d => (hclosed d).symm)

/-! ## 4. The `omCount` gate at the minimal instance `p = q = 2, s = 2` (the re-gate value)

The re-gate (`/workspace-vast/asving/tmp/phaseb_s2regate/`) confirmed the AGGREGATED count → `omCount`
at `p = 2, s = 2`, with `omCount(ram_root) = 1/(q+1) = 1/3` and the resummation ratio `q^{−2}`.  Here
we pin the resummation `(countPivot 2 2)⁻¹ = 4/3` to those engine values:

* `omCount(ram_root) = 1/(q+1) = 1/3` = `q^{−(s(s+1)/2−1)} · (countPivot)⁻¹` (root-normalized).
* `omChildCount(ram) = q/(q+1) = 2/3` = `((q−1)/q) · (countPivot)⁻¹` (cluster-census-normalized);
  `OMCountV2.gate3_cluster_q2` proves `omChildCount halfCluster 2 = 2/3` directly — the resummation's
  actual `omCount`-object anchor. -/

/-- **THE RESUMMATION VALUE at `p = q = 2, s = 2`** (deliverable 3 gate): `(countPivot 2 2)⁻¹ = 4/3`
= `1/(1−q^{−2})` = the `×q`-exposed self-loop geometric series `Σ_k (q^{−2})^k`. -/
theorem gate_resum_q2 : (MontesAxiom.countPivot 2 2)⁻¹ = 4 / 3 := by
  unfold MontesAxiom.countPivot L5fix.selfLoopExponent
  norm_num

/-- **THE `omCount` ROOT-GATE (the re-gate value `1/3`).**  `omCount(ram_root) = 1/(q+1) = 1/3` at
`q = 2` is the ROOT-normalized resummation: the depth-0 root mass `q^{−(s(s+1)/2−1)} = q^{−2} = 1/4`
(the `omCount` root `volExp` deficit vs the child) times the `×q`-exposed geometric factor
`(countPivot 2 2)⁻¹ = 4/3`.  This is the re-gate's `AGG → omCount(ram_root)`. -/
theorem resum_omCount_root_q2 :
    ((2 : ℚ) ^ (L5fix.selfLoopExponent 2))⁻¹ * (MontesAxiom.countPivot 2 2)⁻¹ = 1 / 3 := by
  unfold MontesAxiom.countPivot L5fix.selfLoopExponent
  norm_num

/-- **THE `omChildCount` CHILD-GATE (`2/3`).**  `omChildCount(ram) = q/(q+1) = 2/3` at `q = 2` is the
CLUSTER-CENSUS-normalized resummation: the depth-0 census `mCell/q^0 = (q−1)/q = 1/2` times the
`×q`-exposed geometric factor `(countPivot 2 2)⁻¹ = 4/3`.  Ties directly to
`OMCountV2.gate3_cluster_q2` (`omChildCount halfCluster 2 = 2/3`). -/
theorem resum_omChild_q2 :
    ((2 : ℚ) - 1) / 2 * (MontesAxiom.countPivot 2 2)⁻¹ = 2 / 3 := by
  unfold MontesAxiom.countPivot L5fix.selfLoopExponent
  norm_num

/-- **The `omChildCount` anchor**: the re-gate resummation value `2/3` IS the engine
`OMCountV2.omChildCount halfCluster 2` (the R0-validated size-2 ram-cluster child density) — the
resummation lands on an actual `omCount`-object value, not a free constant. -/
theorem resum_eq_omChildCount_q2 :
    ((2 : ℚ) - 1) / 2 * (MontesAxiom.countPivot 2 2)⁻¹ = OMCountV2.omChildCount OMCountV2.halfCluster 2 := by
  rw [resum_omChild_q2, OMCountV2.gate3_cluster_q2]

/-! ## 5. The per-level box grounding at the minimal instance (deliverable 2, concrete anchor)

The abstract per-level ratio `slBoxRatio s q = q^{−(selfLoopExponent s + 1)} = q^{−s(s+1)/2}` is the
box index of one self-loop coset inside the cluster box, `HNode1.selfLoop_coset_index`:
`#{fresh self-loop pattern} · p^(selfLoopExponent s + 1) = #clusterBox`.  We record the exponent tie
and the `k = 2` iterate (`SelfLoopTower.gate_iterated_selfLoop`) as the concrete anchors of the
tower's per-level mass. -/

/-- **The per-level box exponent tie**: the self-loop step exponent `selfLoopExponent s + 1` IS
`s(s+1)/2` (the bare Vandermonde exponent) — `slBoxRatio`'s exponent — for `1 ≤ s ≤ N−1`.  This is
`HNode1.selfLoop_cost_tie` read as `(free cost) + (selfLoopExponent s + 1) = s(N−1)`, i.e. the box
coset index inside the `p^(s(N−1))` cluster box is `p^(selfLoopExponent s + 1)`. -/
theorem box_step_exponent {N s : ℕ} (hs : 1 ≤ s) (hsN : s < N) :
    (s * (N - 1) - s * (s + 1) / 2) + (L5fix.selfLoopExponent s + 1) = s * (N - 1) :=
  HNode1.selfLoop_cost_tie N s hs hsN

/-- **The concrete `k = 1` box self-loop mass** (`Drainage.card_selfLoopFiber`): the self-loop cell
fiber is `(p−1) · p^(s(N−1) − s(s+1)/2)`; at `p = 2` the `(p−1) = 1` factor is invisible, so the
cluster-box-normalized depth-1 box mass is exactly `p^{−s(s+1)/2} = slBoxRatio`.  Its ratio to the
`p^(s(N−1))` cluster box is `slBoxRatio` (the per-level box step). -/
theorem card_selfLoopFiber_p2 {N s : ℕ} (hs : 0 < s) (hsN : s < N) :
    Nat.card {f : QuotientBox.monicBox 2 N s // CellMenu.InCell 2 f (Drainage.selfLoopCell s)}
      = 2 ^ (s * (N - 1) - s * (s + 1) / 2) := by
  rw [Drainage.card_selfLoopFiber 2 hs hsN]; ring

/-- **The concrete `k = 2` iterate exponent** (`SelfLoopTower.gate_iterated_selfLoop` grounds it):
TWO successive self-loop reads at `(p, μ, N) = (2, 2, 5)` have mass `4`, and there
`4 · 2^(2·(selfLoopExponent 2 + 1)) = 4 · 2^6 = 2^8 = #clusterBox`.  The depth-`2` box mass is thus
`slBoxRatio 2 2 ^ 2 = (1/8)^2 = 1/64` of the cluster box — the tower's second geometric term (the
first two `countPivot` terms), one genuine level down the tower.  We record the exponent tie
`2·(selfLoopExponent 2 + 1) = 6` and the `slBoxRatio` square that the frozen gate discharges. -/
theorem gate_iterated_selfLoop_k2_exp :
    2 * (L5fix.selfLoopExponent 2 + 1) = 6 ∧ slBoxRatio 2 2 ^ 2 = 1 / 64 := by
  refine ⟨by unfold L5fix.selfLoopExponent; norm_num, ?_⟩
  unfold slBoxRatio L5fix.selfLoopExponent; norm_num

/-! ## 6. The remaining `h_node` obligation (STATED precisely, NOT proven here)

`REMAINING_OBLIGATION` (S2 sub-piece (v)→(vi), the general step).  What is banked above is the
`×q`-exposed self-loop geometric resummation at the minimal instance: the ratio conversion
(`xqMultiplicity`), the finite tower (`aggSelfLoopTower_closed`), and its limit
(`tendsto_aggSelfLoopTower`) to `(countPivot s q)⁻¹`, with the `omCount`/`omChildCount` numeric ties.
What remains — the actual `h_node` limit `Σ_{T_box ↦ T} stratumCount1 s N c / p^{s(N−1)} → omCount T`
— needs the box census wired to the per-depth mass UNIFORMLY in `N`:

1. `engineShapeOf : NodeConfig → EngineShape × ℕ` — the coarse engine shape + self-loop depth reader
   on the `StratumOrder1` box cells (mirroring `phaseb_s2regate/engine_shape.py`: single-side
   residual `{(1,1)}` at polygon height `H` ↦ `(ram, (H−1)/2)`, `{(1,s)}` ↦ `(selfloop, …)`), so
   `aggStratum s N T := Σ_{c : engineShapeOf c = T} stratumCount1 s N c` is well-defined.
2. The uniform-in-`N` per-depth census identity: `Σ_{c : engineShapeOf c = (T, k)} stratumCount1 s N c
   = (depth-0 census) · p^{s(N−1)} · (slBoxRatio s p)^k · p^k` for `k` up to the depth cap `⌊(N−1)/…⌋`
   (the `×p^k` is the residue-translate multiplicity `xqMultiplicity` supplies).  The per-level step
   is `HNode1.selfLoop_coset_index` (banked here as `box_step_exponent`) applied at EVERY depth via
   the recenter/restart tower `SelfLoopTower.two_level_census` — currently only `k ≤ 2` is concretely
   discharged (`gate_iterated_selfLoop_k2`); the general `k` needs the tower iterated `k`-fold (an
   induction on depth over `two_level_census`, the "child-as-fresh-cluster" identification, S2 (iii)).
3. Then `aggStratum s N T / p^{s(N−1)} = (depth-0 census) · aggSelfLoopTower s p (depth N) + tail`,
   with `tail → 0` by `Drainage.tendsto_tailDensity_zero`, and the limit is `(depth-0 census) ·
   (countPivot s q)⁻¹` = `omCount T` (via `resum_omCount_root_q2` at the minimal instance / the
   general `volExp`/`mCell` normalization).  The Mathlib limit engine is `tendsto_aggSelfLoopTower`
   (banked) + `Drainage.tendsto_tailDensity_zero` (banked) + `Filter.Tendsto.add`/`.mul_const`.

The one genuinely missing lemma is (2)'s uniform-in-`(N,k)` box census — the iterated tower census —
which requires the `SelfLoopTower.two_level_census` `k`-fold induction (S2 (iii)+(v)), NOT the
geometric limit (which is closed here).  Generalizing from the minimal instance: for general `s` the
`(p−1)^k` residual-root multiplicity re-enters (invisible only at `p = 2`); it rides along as an
extra per-level `(p−1)` in the depth-0 census `mCell = (p−1)`-shaped, and the ratio `slBoxRatio`/
`slExposedRatio` are already stated for general `s` (via `selfLoopExponent s`), so
`xqMultiplicity`/`tendsto_aggSelfLoopTower` hold verbatim for general `s ≥ 2, q ≥ 2`. -/

end LeanUrat.OM.SelfLoopResum
