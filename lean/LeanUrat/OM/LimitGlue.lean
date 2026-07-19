/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.OM.LevelNCount
import LeanUrat.OM.LimitRecurrence
import LeanUrat.NestedCollapse
import LeanUrat.L5fix
import LeanUrat.MontesAxiom

/-!
# F3 — LimitGlue: the limit primitives (Bundle 0d, WAVE-0)
(blueprint §"F3 — Limit", FOUNDATION_BLUEPRINT.md nodes F3.L1/L2/L3 + the L4 assembly skeleton)

**B-INDEPENDENT limit machinery.** This module proves the pure-mathlib + proved-OM-asset limit
primitives that, GIVEN the frozen GLUE-1 contracts (`stratumCount_selfLoop_rec`, `nodeTrunc_tendsto`)
and GLUE-2 (`boxScale_share`) as HYPOTHESES, assemble the `nodeMeasure_boxSum` shape. Nothing here
depends on the B classifier proofs or the serial spine; the spine lemmas enter the assembly skeleton
ONLY as named hypotheses (they are proved elsewhere — F2 / serial pole).

Nodes (FOUNDATION_BLUEPRINT.md):
* **F3.L1** `boxVolume_normalized_limit` — the `q`-power ratio collapse: the level-`N` box term
  `bb1Value c.polygon (q^N)·(q^δ)^{dS-1}`, rescaled by the per-cell newton-exponent share
  `q^{A·N}`, tends to the `q`-scale residual weight `(q^δ)^{dS-1}`. (`A = L4.newtonExponent`.)
  Built on the `(1 - (q^N)⁻¹)^V → 1` collapse via `tendsto_pow_atTop_nhds_zero_of_lt_one`.
* **F3.L2** `selfLoop_resummation` — the geometric self-loop resummation, REUSING the PROVED
  `NestedCollapse.geometricLimit_of_selfLoop` at `r = selfLoopRatio = q^{-w} < 1`, giving
  `geomTrunc a r → a / (1 - r) = a / countPivot` via `one_sub_selfLoopRatio_eq_countPivot`.
* **F3.L3** `children_product_limit` — `Filter.Tendsto` of a finite children-list product, via the
  PROVED mathlib `tendsto_list_prod` (Topology/Algebra/Monoid.lean:760).
* **F3.L4 (skeleton)** `node_limit_assembly` — chains GLUE-1's `nodeTrunc_tendsto` (taken as a
  HYPOTHESIS — the serial spine) to the `nodeMeasure_boxSum` conclusion by DEFINITIONAL unfolding of
  `nodeTrunc` / `nodeNum`. The spine lemma is a hypothesis, so this node carries NO `sorry`.
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false

namespace LeanUrat.OM.F3

open LeanUrat LeanUrat.MontesAxiom LeanUrat.CountingModel
open LeanUrat.OM.M8
open Filter Topology

open scoped Classical

/-! ## A reusable `q`-decay primitive (the engine of F3.L1)

For `q > 1`, `(q^N)⁻¹ = (q⁻¹)^N → 0` as `N → ∞`. This is the single analytic input behind the
box-volume collapse: the BB1 vertex factor `(1 - (q^N)⁻¹)^V → 1`. -/

/-- **`(q^N)⁻¹ → 0`** for `q > 1`. The decay engine: `(q^N)⁻¹ = (q⁻¹)^N` with `q⁻¹ < 1`, fed to
`tendsto_pow_atTop_nhds_zero_of_lt_one`. `[core]` -/
theorem invPow_tendsto_zero {q : ℕ} (hq : 1 < q) :
    Filter.Tendsto (fun N => ((q : ℚ) ^ N)⁻¹) Filter.atTop (nhds 0) := by
  have hq0 : (0 : ℚ) < (q : ℚ) := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one (le_of_lt hq)
  have hqinv0 : (0 : ℚ) ≤ (q : ℚ)⁻¹ := le_of_lt (inv_pos.mpr hq0)
  have hqinv1 : (q : ℚ)⁻¹ < 1 := by
    rw [inv_lt_one_iff₀]
    right
    exact_mod_cast hq
  have h := tendsto_pow_atTop_nhds_zero_of_lt_one hqinv0 hqinv1
  refine h.congr ?_
  intro N
  rw [inv_pow]

/-- **The BB1 vertex factor collapses to `1`.** For `q > 1`, `(1 - (q^N)⁻¹)^V → (1 - 0)^V = 1`.
`[core]` -/
theorem vertexFactor_tendsto_one {q : ℕ} (hq : 1 < q) (V : ℕ) :
    Filter.Tendsto (fun N => (1 - ((q : ℚ) ^ N)⁻¹) ^ V) Filter.atTop (nhds 1) := by
  have hbase : Filter.Tendsto (fun N => 1 - ((q : ℚ) ^ N)⁻¹) Filter.atTop (nhds (1 - 0)) :=
    tendsto_const_nhds.sub (invPow_tendsto_zero hq)
  have hpow := hbase.pow V
  simpa using hpow

/-! ## F3.L1 — `boxVolume_normalized_limit` (the `q`-power ratio collapse)

`bb1Value pg Q = (1 - Q⁻¹)^V · Q^{-A}` (`L4.bb1Value`, with `V = newtonVertexCount`,
`A = newtonExponent`). At scale `Q = q^N` this is `(1 - (q^N)⁻¹)^V · q^{-A·N}`. Rescaling by the
per-cell share `q^{A·N}` cancels the `q^{-A·N}` exactly, leaving `(1 - (q^N)⁻¹)^V → 1`. Multiplying
by the (`N`-independent) residual weight `(q^δ)^{dS-1}` gives the `q`-scale residual count. -/

/-- **`bb1Value` rescaled by its newton-exponent share tends to `1`.** For `q > 1`,
`bb1Value pg (q^N) · q^{A·N} = (1 - (q^N)⁻¹)^V → 1` (`A = L4.newtonExponent pg`,
`V = L4.newtonVertexCount pg`). The pure box-volume `q`-power collapse. `[core]` -/
theorem bb1Value_share_tendsto_one {q : ℕ} (hq : 1 < q) (pg : L4.LatticePolygon) :
    Filter.Tendsto
      (fun N => L4.bb1Value pg (q ^ N) * (q : ℚ) ^ (L4.newtonExponent pg * N))
      Filter.atTop (nhds 1) := by
  have hq0 : (0 : ℚ) < (q : ℚ) := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one (le_of_lt hq)
  have hqne : (q : ℚ) ≠ 0 := ne_of_gt hq0
  -- Rewrite the rescaled box term as the vertex factor only.
  have hrw : ∀ N,
      L4.bb1Value pg (q ^ N) * (q : ℚ) ^ (L4.newtonExponent pg * N)
        = (1 - ((q : ℚ) ^ N)⁻¹) ^ L4.newtonVertexCount pg := by
    intro N
    unfold L4.bb1Value
    -- bb1Value pg (q^N) = (1 - ↑(q^N)⁻¹)^V · (↑(q^N)^A)⁻¹.  Push the cast `↑(q^N) = (↑q)^N`.
    push_cast
    -- (1 - (↑q^N)⁻¹)^V * ((↑q^N)^A)⁻¹ * ↑q^{A·N}, and ((↑q^N)^A)⁻¹ · ↑q^{A·N} = 1.
    have hpow : ((q : ℚ) ^ N) ^ L4.newtonExponent pg = (q : ℚ) ^ (L4.newtonExponent pg * N) := by
      rw [← pow_mul, Nat.mul_comm]
    rw [hpow]
    have hcancel : (((q : ℚ) ^ (L4.newtonExponent pg * N))⁻¹) * (q : ℚ) ^ (L4.newtonExponent pg * N) = 1 := by
      rw [inv_mul_cancel₀ (pow_ne_zero _ hqne)]
    rw [mul_assoc, hcancel, mul_one]
  refine (vertexFactor_tendsto_one hq (L4.newtonVertexCount pg)).congr ?_
  intro N
  rw [hrw N]

/-- **F3.L1 `boxVolume_normalized_limit`.** The level-`N` per-cell box × residual term, rescaled by
the per-cell newton-exponent share `q^{A·N}` (`A = L4.newtonExponent c.polygon`), tends to the
`q`-scale residual count `(q^δ)^{dS-1}`:

    (q^δ)^{dS-1} · bb1Value c.polygon (q^N) · q^{A·N}  →  (q^δ)^{dS-1}.

The residual weight is `N`-independent (carried out of the limit); the box volume collapses by
`bb1Value_share_tendsto_one`. GLUE-2 `boxScale_share` is what certifies the shares `A(c.polygon)`
(plus the residual contributions `δ·(dS-1)`) sum to `n` across `cells T`; it enters the assembly,
not this per-cell node. `[core]` -/
theorem boxVolume_normalized_limit {q : ℕ} (hq : 1 < q) (c : CountCell) :
    Filter.Tendsto
      (fun N => ((q : ℚ) ^ c.δ) ^ (c.dS - 1)
        * (L4.bb1Value c.polygon (q ^ N) * (q : ℚ) ^ (L4.newtonExponent c.polygon * N)))
      Filter.atTop (nhds (((q : ℚ) ^ c.δ) ^ (c.dS - 1))) := by
  have h := bb1Value_share_tendsto_one hq c.polygon
  have hmul := (tendsto_const_nhds (x := (((q : ℚ) ^ c.δ) ^ (c.dS - 1)))).mul h
  simpa using hmul

/-! ## F3.L2 — `selfLoop_resummation` (the geometric self-loop limit)

REUSES the PROVED `NestedCollapse.geometricLimit_of_selfLoop`. At a ramifying node
(`2 ≤ treeSize T`), `selfLoopRatio treeSize T q = (q^w)⁻¹` (`w = L5fix.selfLoopExponent (treeSize T)`)
is the per-step contraction `r`, with `0 < r < 1` for `q ≥ 2`, so the finite geometric truncations
`geomTrunc a r → a / (1 - r)`. By `one_sub_selfLoopRatio_eq_countPivot`, `1 - r = countPivot`, hence
the limit is `a / countPivot (treeSize T) q` — EXACTLY the `nodeMeasure_boxSum` self-loop denominator. -/

/-- **The self-loop ratio is in `(0,1)` at a ramifying node.** For `q ≥ 2` and `2 ≤ treeSize T`,
`0 < selfLoopRatio treeSize T q < 1`. This is the `0 < r < 1` hypothesis of
`geometricLimit_of_selfLoop`, proved from `L5fix.selfLoop_geometric` (positivity of `1 - r`) and
`selfLoopExponent ≥ 1` (so `r = (q^w)⁻¹ < 1`). `[core]` -/
theorem selfLoopRatio_mem_Ioo {q : ℕ} (hq : 2 ≤ q) {treeSize : ClusterShape → ℕ} {T : ClusterShape}
    (hT : 2 ≤ treeSize T) :
    0 < M8.selfLoopRatio treeSize T q ∧ M8.selfLoopRatio treeSize T q < 1 := by
  unfold M8.selfLoopRatio
  simp only [hT, if_true]
  have hexp : 1 ≤ L5fix.selfLoopExponent (treeSize T) := by
    have h6 : 6 ≤ treeSize T * (treeSize T + 1) := by nlinarith
    unfold L5fix.selfLoopExponent; omega
  have hgt : (1 : ℚ) < (q : ℚ) ^ L5fix.selfLoopExponent (treeSize T) :=
    one_lt_pow₀ (by exact_mod_cast (by omega : 1 < q)) (by omega)
  have hpos : (0 : ℚ) < (q : ℚ) ^ L5fix.selfLoopExponent (treeSize T) :=
    lt_trans one_pos hgt
  refine ⟨inv_pos.mpr hpos, ?_⟩
  simpa using inv_lt_one_of_one_lt₀ hgt

/-- **F3.L2 `selfLoop_resummation`.** The geometric self-loop resummation at a ramifying node
(`2 ≤ treeSize T`, `q ≥ 2`): the finite truncations `geomTrunc a (selfLoopRatio T q) N` converge to
`a / countPivot (treeSize T) q`. Direct instantiation of the PROVED
`NestedCollapse.geometricLimit_of_selfLoop` at `r = selfLoopRatio`, with `1 - r = countPivot` by
`M8.one_sub_selfLoopRatio_eq_countPivot`. `[core]` -/
theorem selfLoop_resummation {q : ℕ} (hq : 2 ≤ q) {treeSize : ClusterShape → ℕ} {T : ClusterShape}
    (hT : 2 ≤ treeSize T) (a : ℚ) :
    Filter.Tendsto (NestedCollapse.geomTrunc a (M8.selfLoopRatio treeSize T q)) Filter.atTop
      (nhds (a / countPivot (treeSize T) q)) := by
  obtain ⟨hr0, hr1⟩ := selfLoopRatio_mem_Ioo hq hT
  have h := NestedCollapse.geometricLimit_of_selfLoop a (M8.selfLoopRatio treeSize T q) hr0 hr1
  rwa [M8.one_sub_selfLoopRatio_eq_countPivot] at h

/-- **F3.L2 (leaf branch) `selfLoop_resummation_leaf`.** At a leaf node (`treeSize T < 2`),
`selfLoopRatio = 0` and `countPivot = 1`, so `geomTrunc a 0 N = a` for all `N` and the (constant)
sequence trivially converges to `a / 1 = a`. Together with `selfLoop_resummation` this covers every
node. `[core]` -/
theorem selfLoop_resummation_leaf {q : ℕ} {treeSize : ClusterShape → ℕ} {T : ClusterShape}
    (hT : ¬ 2 ≤ treeSize T) (a : ℚ) :
    Filter.Tendsto (NestedCollapse.geomTrunc a (M8.selfLoopRatio treeSize T q)) Filter.atTop
      (nhds (a / countPivot (treeSize T) q)) := by
  have hr : M8.selfLoopRatio treeSize T q = 0 := by
    unfold M8.selfLoopRatio; simp [hT]
  have hpivot : countPivot (treeSize T) q = 1 := by
    unfold countPivot; simp [hT]
  rw [hr, hpivot, div_one]
  -- geomTrunc a 0 N = a * (1 - 0^(N+1)) / (1 - 0) = a, a constant sequence.
  have hconst : ∀ N, NestedCollapse.geomTrunc a 0 N = a := by
    intro N
    unfold NestedCollapse.geomTrunc
    simp
  refine tendsto_const_nhds.congr ?_
  intro N; rw [hconst N]

/-! ## F3.L3 — `children_product_limit` (the finite product limit)

A `Filter.Tendsto` of the children-list product: if each child term converges, the product over the
finite `children` list converges to the product of the limits. Direct from mathlib's
`tendsto_list_prod` (Topology/Algebra/Monoid.lean:760) over `ℚ` (a topological monoid). -/

/-- **F3.L3 `children_product_limit`.** For a finite list `children : List ClusterShape`, if each
per-child term `g ch · N` tends to its limit `L ch`, then the product over the children converges to
the product of the limits:

    (fun N => (children.map (fun ch => g ch N)).prod)  →  (children.map L).prod.

Direct instantiation of the PROVED mathlib `tendsto_list_prod`. `[core]` -/
theorem children_product_limit {ι : Type*} (children : List ι)
    (g : ι → ℕ → ℚ) (L : ι → ℚ)
    (hchild : ∀ ch ∈ children, Filter.Tendsto (fun N => g ch N) Filter.atTop (nhds (L ch))) :
    Filter.Tendsto (fun N => (children.map (fun ch => g ch N)).prod) Filter.atTop
      (nhds ((children.map L).prod)) :=
  tendsto_list_prod children hchild

/-! ## F3.L5 — the ℝ→ℚ cast glue for the first-order recurrence limit (LIMIT_BLUEPRINT §2)

`LimitRecurrence.firstOrder_recurrence_limit` lives over ℝ (the metric-space contraction engine).
`nodeTrunc` is a `ℕ → ℚ` sequence, and the spine recurrence is rational. The bridge is a thin wrapper
that pushes the ℚ recurrence through the ring/topological embedding `Rat.cast : ℚ → ℝ` and pulls the
limit back via `Rat.isEmbedding_coe_real.tendsto_nhds_iff`. This is the cast glue the blueprint
scratch-verified; it is fully autonomous (wall-free) and BANKED here. -/

/-- **F3.L5 — ℝ→ℚ cast glue for `firstOrder_recurrence_limit`** (LIMIT_BLUEPRINT §2). The rational
varying-forcing first-order recurrence limit: if `x (N+1) = r·x N + f (N+1)` over ℚ with `0 ≤ r < 1`
and `f → L`, then `x → L/(1-r)`. PROVED by pushing the recurrence through the ring + topological
embedding `(↑) : ℚ → ℝ`, applying the ℝ-side engine `LimitRecurrence.firstOrder_recurrence_limit`, and
pulling the limit back through `Rat.isEmbedding_coe_real.tendsto_nhds_iff`. Sorry-free, core-only — the
ℝ-side engine is itself `[propext, Classical.choice, Quot.sound]`. `[core]` -/
theorem firstOrder_recurrence_limit_rat (x f : ℕ → ℚ) (r L : ℚ)
    (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hrec : ∀ N, x (N + 1) = r * x N + f (N + 1))
    (hf : Filter.Tendsto f Filter.atTop (nhds L)) :
    Filter.Tendsto x Filter.atTop (nhds (L / (1 - r))) := by
  have hxR : Filter.Tendsto (fun N => ((x N : ℝ))) Filter.atTop (nhds (((L / (1 - r) : ℚ) : ℝ))) := by
    have hr0R : (0 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr0
    have hr1R : (r : ℝ) < 1 := by exact_mod_cast hr1
    have hrecR : ∀ N, (x (N + 1) : ℝ) = (r : ℝ) * (x N : ℝ) + (f (N + 1) : ℝ) := by
      intro N; have := hrec N; push_cast [this]; ring
    have hfR : Filter.Tendsto (fun N => ((f N : ℝ))) Filter.atTop (nhds (L : ℝ)) :=
      (Rat.continuous_coe_real.tendsto L).comp hf
    have hlim := LimitRecurrence.firstOrder_recurrence_limit
      (fun N => (x N : ℝ)) (fun N => (f N : ℝ)) (r : ℝ) (L : ℝ) hr0R hr1R hrecR hfR
    have hcast : (L : ℝ) / (1 - (r : ℝ)) = (((L / (1 - r) : ℚ)) : ℝ) := by push_cast; ring
    rwa [hcast] at hlim
  rw [Rat.isEmbedding_coe_real.tendsto_nhds_iff]
  exact hxR

/-! ## F3.L6 — `nodeTrunc_tendsto` assembly skeleton (LIMIT_BLUEPRINT §4)

The box-scale collapse `nodeTrunc_tendsto` reduces — GIVEN the *corrected* GLUE-1 per-step recurrence
(`nodeTrunc T (N+1) = nonSelfLoopNorm T (N+1) + selfLoopRatio · nodeTrunc T N`, the `q^n`-corrected
form, blueprint §3) and the box-VOLUME-scale collapse (`nonSelfLoopNorm T (N+1) → nodeNum T q`,
obstruction (A3), blueprint §4) — to the rational first-order recurrence limit `firstOrder_recurrence_limit_rat`.
The two inputs are threaded as explicit named hypotheses (`hstep`, `hf`): `hstep` is the corrected
GLUE-1 statement (its arithmetic was scratch-PROVED, blueprint §3; its proof is wall-gated on
`certLevel_stabilizes` via GLUE-1) and `hf` is the box-volume budget collapse A3 (the genuine residual,
a GMN box-volume-scale structural fact, blueprint §6). The assembly itself is sorry-free: it identifies
`1 - selfLoopRatio = countPivot` (`M8.one_sub_selfLoopRatio_eq_countPivot`) and feeds the recurrence
into the cast-glued analytic engine. This BANKS the reduction `nodeTrunc_tendsto ⟸ (corrected hstep) +
(A3 hf)` without fake-closing either residual. -/

/-- **The self-loop ratio is in `[0,1)` at EVERY node** (the `0 ≤ r < 1` hypothesis of the recurrence
limit, covering both leaf and ramifying nodes). At a ramifying node (`2 ≤ treeSize T`) this is
`selfLoopRatio_mem_Ioo`; at a leaf (`treeSize T < 2`) `selfLoopRatio = 0`, so `0 ≤ 0 < 1`. `[core]` -/
theorem selfLoopRatio_mem_Ico {q : ℕ} (hq : 2 ≤ q) {treeSize : ClusterShape → ℕ} {T : ClusterShape} :
    0 ≤ M8.selfLoopRatio treeSize T q ∧ M8.selfLoopRatio treeSize T q < 1 := by
  by_cases hT : 2 ≤ treeSize T
  · obtain ⟨h0, h1⟩ := selfLoopRatio_mem_Ioo hq hT
    exact ⟨le_of_lt h0, h1⟩
  · have hr : M8.selfLoopRatio treeSize T q = 0 := by
      unfold M8.selfLoopRatio; simp [hT]
    rw [hr]; exact ⟨le_refl 0, zero_lt_one⟩

/-- **F3.L6 — `nodeTrunc_tendsto` assembly skeleton** (LIMIT_BLUEPRINT §4). GIVEN the corrected GLUE-1
per-step recurrence `hstep` and the box-volume-scale collapse `hf` (the forcing `f` tends to the
`q`-scale numerator `L`), the normalized truncation `x = nodeTrunc T` converges to `L / countPivot`.
PROVED sorry-free by `firstOrder_recurrence_limit_rat` (the cast-glued ℝ engine) at
`r = selfLoopRatio treeSize T q`, rewriting `1 - selfLoopRatio = countPivot`
(`M8.one_sub_selfLoopRatio_eq_countPivot`). Stated abstractly in the forcing `f` and numerator `L`
(so it composes with `LimitSpine.nonSelfLoopNorm` / `M8.nodeNum` downstream, where this file cannot
reference `LimitSpine`). The two hypotheses are the precise residuals the blueprint flags: `hstep` =
corrected GLUE-1 (§3, wall-gated PROOF), `hf` = box-volume budget A3 (§6, GMN structural CITE). NO
`sorry`; NO fake-close. `[core, modulo hstep + hf]` -/
theorem nodeTrunc_tendsto_of_recurrence {q : ℕ} (hq : 2 ≤ q)
    (treeSize : ClusterShape → ℕ) (T : ClusterShape) (x f : ℕ → ℚ) (L : ℚ)
    (hstep : ∀ N, x (N + 1) = f (N + 1) + M8.selfLoopRatio treeSize T q * x N)
    (hf : Filter.Tendsto f Filter.atTop (nhds L)) :
    Filter.Tendsto x Filter.atTop (nhds (L / countPivot (treeSize T) q)) := by
  obtain ⟨hr0, hr1⟩ := selfLoopRatio_mem_Ico hq (treeSize := treeSize) (T := T)
  -- rewrite the recurrence into the `r·x N + f (N+1)` shape the engine expects:
  have hstep' : ∀ N, x (N + 1) = M8.selfLoopRatio treeSize T q * x N + f (N + 1) := by
    intro N; rw [hstep N]; ring
  have hlim := firstOrder_recurrence_limit_rat x f (M8.selfLoopRatio treeSize T q) L hr0 hr1 hstep' hf
  rwa [M8.one_sub_selfLoopRatio_eq_countPivot] at hlim

/-- **F3.L6 (end-to-end) — `nodeTrunc_tendsto` REDUCED to (corrected GLUE-1) + (box-volume budget A3)**
(LIMIT_BLUEPRINT §4 assembly). This is the concrete reduction skeleton: feeding the CORRECTED GLUE-1
per-step recurrence (`M8.nodeTrunc_step_corrected`, applied at every level via `hrec`, the `q^n`-fixed
self-loop statement) and the box-VOLUME-scale collapse `hf` (obstruction A3 — the normalized
non-self-loop forcing tends to the `q`-scale numerator `L`) into the cast-glued recurrence limit
`nodeTrunc_tendsto_of_recurrence` yields EXACTLY `nodeTrunc_tendsto`'s conclusion
`nodeTrunc T → L / countPivot`. Banked sorry-free: it shows `M8.nodeTrunc_tendsto ⟸ (corrected GLUE-1
`hrec`) + (A3 `hf`)`, the two named residuals the blueprint isolates. The forcing is the explicit
filtered-cell sum at level `N` over `q^{nN}` — definitionally `LimitSpine.nonSelfLoopNorm` shifted
(downstream); `L` is `M8.nodeNum` at the wiring site. `[core, modulo hrec + hf — corrected GLUE-1
statement (wall-gated PROOF) + box-volume budget A3 (GMN CITE)]`. -/
theorem nodeTrunc_tendsto_of_corrected_GLUE1 {n : ℕ} (p : ℕ) [Fact p.Prime] (q : ℕ) (hq : 2 ≤ q)
    (classify : (N : ℕ) → QuotientBox.monicBox p N n → ClusterShape)
    (cells : ClusterShape → List CountCell) (treeSize : ClusterShape → ℕ)
    (T : ClusterShape) (L : ℚ)
    (hrec : ∀ N, M8.stratumCount (M8.shapeFiberCount p n classify) T (N + 1)
      = (((cells T).filter (fun c => decide (∀ ch ∈ c.children, treeSize ch ≠ treeSize T))).map
          (fun c =>
            L4.bb1Value c.polygon (q ^ (N + 1)) * ((q : ℚ) ^ c.δ) ^ (c.dS - 1)
              * (c.children.map (fun ch =>
                  M8.stratumCount (M8.shapeFiberCount p n classify) ch (N + 1))).prod)).sum
        + M8.selfLoopRatio treeSize T q * ((q : ℚ) ^ n)
            * M8.stratumCount (M8.shapeFiberCount p n classify) T N)
    (hf : Filter.Tendsto
      (fun N =>
        (((cells T).filter (fun c => decide (∀ ch ∈ c.children, treeSize ch ≠ treeSize T))).map
            (fun c =>
              L4.bb1Value c.polygon (q ^ N) * ((q : ℚ) ^ c.δ) ^ (c.dS - 1)
                * (c.children.map (fun ch =>
                    M8.stratumCount (M8.shapeFiberCount p n classify) ch N)).prod)).sum
          / (q : ℚ) ^ (n * N))
      Filter.atTop (nhds L)) :
    Filter.Tendsto (M8.nodeTrunc p q classify T) Filter.atTop
      (nhds (L / countPivot (treeSize T) q)) := by
  -- abbreviate the per-level filtered-cell forcing `f N := (filtered sum at N)/q^{nN}`:
  set f : ℕ → ℚ := fun N =>
    (((cells T).filter (fun c => decide (∀ ch ∈ c.children, treeSize ch ≠ treeSize T))).map
        (fun c =>
          L4.bb1Value c.polygon (q ^ N) * ((q : ℚ) ^ c.δ) ^ (c.dS - 1)
            * (c.children.map (fun ch =>
                M8.stratumCount (M8.shapeFiberCount p n classify) ch N)).prod)).sum
      / (q : ℚ) ^ (n * N) with hfdef
  -- the CORRECTED per-step recurrence holds at every level (consumes `hrec`, blueprint §3):
  have hstep : ∀ N, M8.nodeTrunc p q classify T (N + 1)
      = f (N + 1) + M8.selfLoopRatio treeSize T q * M8.nodeTrunc p q classify T N := by
    intro N
    rw [hfdef]
    exact M8.nodeTrunc_step_corrected p q classify cells treeSize (by omega) T N (hrec N)
  -- feed into the cast-glued recurrence-limit assembly skeleton:
  exact nodeTrunc_tendsto_of_recurrence hq treeSize T (M8.nodeTrunc p q classify T) f L hstep hf

/-! ## F3.L4 (skeleton) — `node_limit_assembly`

Chains GLUE-1's `nodeTrunc_tendsto` to the `nodeMeasure_boxSum` conclusion. `nodeTrunc_tendsto` is the
serial-spine consequence of `stratumCount_selfLoop_rec` unrolled to `geomTrunc` and passed through
`selfLoop_resummation` (F3.L2); here it enters ONLY as a HYPOTHESIS `h_spine`. The assembly step
itself is pure DEFINITIONAL unfolding of `nodeTrunc` / `nodeNum` — no `sorry`. -/

/-- **F3.L4 (skeleton) `node_limit_assembly`.** GIVEN the GLUE-1 spine bridge `nodeTrunc_tendsto`
(`h_spine`, proved in the serial pole), the normalized level-`N` stratum measure converges to the
`nodeMeasure_boxSum` RHS. The two are DEFINITIONALLY the same `Filter.Tendsto` statement:
`nodeTrunc` unfolds to `stratumCount / q^{nN}` and `nodeNum / countPivot` is exactly the box-additive
self-loop-resummed sum. This node carries NO `sorry`: it consumes the spine lemma as a hypothesis and
discharges the conclusion by `unfold`. `[core, modulo h_spine]` -/
theorem node_limit_assembly {q n : ℕ} (p : ℕ) [Fact p.Prime]
    (classify : (N : ℕ) → QuotientBox.monicBox p N n → ClusterShape)
    (cells : ClusterShape → List CountCell) (treeSize : ClusterShape → ℕ)
    (cells_descend : ∀ (T : ClusterShape), ∀ c ∈ cells T, ∀ ch ∈ c.children, treeSize ch < treeSize T)
    (_hq : 1 < q) (T : ClusterShape)
    (h_spine : Filter.Tendsto (M8.nodeTrunc p q classify T) Filter.atTop
      (nhds (M8.nodeNum cells treeSize cells_descend T q / countPivot (treeSize T) q))) :
    Filter.Tendsto
      (fun N => M8.stratumCount (M8.shapeFiberCount p n classify) T N / (q : ℚ) ^ (n * N))
      Filter.atTop (nhds
        (((cells T).map (fun c =>
            countCellCoeff c q
              * (c.children.map (fun ch => clusterCount cells treeSize cells_descend ch q)).prod)).sum
          / countPivot (treeSize T) q)) := by
  -- `M8.nodeTrunc p q classify T N` is definitionally `stratumCount … / q^{n·N}`,
  -- and `M8.nodeNum …` is definitionally the box-additive sum numerator.
  have hfun : M8.nodeTrunc p q classify T
      = fun N => M8.stratumCount (M8.shapeFiberCount p n classify) T N / (q : ℚ) ^ (n * N) := by
    funext N; rfl
  have hnum : M8.nodeNum cells treeSize cells_descend T q
      = ((cells T).map (fun c =>
            countCellCoeff c q
              * (c.children.map (fun ch => clusterCount cells treeSize cells_descend ch q)).prod)).sum := rfl
  rw [hfun, hnum] at h_spine
  exact h_spine

/-! ## CRITICAL TYPE-COMPOSITION CHECK

The `node_limit_assembly` skeleton's conclusion must MATCH `M8.nodeMeasure_boxSum`'s goal verbatim
(so the serial-pole closure of `nodeTrunc_tendsto` discharges `nodeMeasure_boxSum` by feeding it into
`node_limit_assembly`). The `example` below derives `nodeMeasure_boxSum`'s exact conclusion from
`node_limit_assembly` applied to the frozen GLUE-1 `nodeTrunc_tendsto` — if the shapes did not
compose, this would fail to elaborate. It elaborates ⟹ the F3 primitives plug into the frozen
contracts by type. (2026-07-04: `M8.nodeTrunc_tendsto` is now hypothesis-threaded — its former axiom
inputs `M8.selfLoop_childFiber_corrected` (A9) / `M8.boxVolumeScale_collapse` (A10) were FALSE-AS-STATED
over free `cells`/`treeSize` and are DELETED — so the composition check carries the same `hA9`/`hA10`
hypotheses, VERBATIM the deleted axioms' conclusions.) -/
example {q n : ℕ} (p : ℕ) [Fact p.Prime]
    (classify : (N : ℕ) → QuotientBox.monicBox p N n → ClusterShape)
    (cells : ClusterShape → List CountCell) (treeSize : ClusterShape → ℕ)
    (cells_descend : ∀ (T : ClusterShape), ∀ c ∈ cells T, ∀ ch ∈ c.children, treeSize ch < treeSize T)
    (hq : 1 < q) (T : ClusterShape)
    (hA9 : ∀ N, M8.stratumCount (M8.shapeFiberCount p n classify) T (N + 1)
      = (((cells T).filter (fun c => decide (∀ ch ∈ c.children, treeSize ch ≠ treeSize T))).map
          (fun c =>
            L4.bb1Value c.polygon (q ^ (N + 1)) * ((q : ℚ) ^ c.δ) ^ (c.dS - 1)
              * (c.children.map (fun ch =>
                  M8.stratumCount (M8.shapeFiberCount p n classify) ch (N + 1))).prod)).sum
        + M8.selfLoopRatio treeSize T q * ((q : ℚ) ^ n)
            * M8.stratumCount (M8.shapeFiberCount p n classify) T N)
    (hA10 : Filter.Tendsto
      (fun N =>
        (((cells T).filter (fun c => decide (∀ ch ∈ c.children, treeSize ch ≠ treeSize T))).map
            (fun c =>
              L4.bb1Value c.polygon (q ^ N) * ((q : ℚ) ^ c.δ) ^ (c.dS - 1)
                * (c.children.map (fun ch =>
                    M8.stratumCount (M8.shapeFiberCount p n classify) ch N)).prod)).sum
          / (q : ℚ) ^ (n * N))
      Filter.atTop (nhds (M8.nodeNum cells treeSize cells_descend T q))) :
    Filter.Tendsto
      (fun N => M8.stratumCount (M8.shapeFiberCount p n classify) T N / (q : ℚ) ^ (n * N))
      Filter.atTop (nhds
        (((cells T).map (fun c =>
            countCellCoeff c q
              * (c.children.map (fun ch => clusterCount cells treeSize cells_descend ch q)).prod)).sum
          / countPivot (treeSize T) q)) :=
  -- Feed the frozen GLUE-1 spine bridge into the F3.L4 assembly skeleton.
  node_limit_assembly p classify cells treeSize cells_descend hq T
    (M8.nodeTrunc_tendsto p classify cells treeSize cells_descend q hq T hA9 hA10)

end LeanUrat.OM.F3
