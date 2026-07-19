/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.OM.CountingModel
import LeanUrat.OM.LimitGlue
import LeanUrat.OM.LevelNCount
import LeanUrat.OM.QuotientBox
import LeanUrat.L4

/-!
# Bundle 1b — `LimitSpine`: the normalization bridge + the B-independent limit assembly
(blueprint FOUNDATION_BLUEPRINT.md §"F3 — Limit" / status doc §3 core-A.3)

Two B-INDEPENDENT deliverables. The classifier is NOT needed; the serial-spine recurrences enter ONLY
as named HYPOTHESES (they are gated on Core-B and proved elsewhere).

## (1) NORMALIZATION BRIDGE (status doc §3 core-A.3, "one bounded lemma").

`cellVolume_factor_zmod` (PROVED, `M8`) gives the genuine `Nat.card` coordinate-product
`inCellResidueCount p N pg P = ∏ i, columnResidueCount p N pg P i`. `L4.bb1Value pg Q` is the closed
shell/ball value `(1 - Q⁻¹)^V · Q^{-A}`. The bridge is the BOUNDED per-column normalization fact: each
per-column count, divided by the residue size `Q`, is the per-column Haar density `L4.columnMeasure`
(the vertex shell `(1-Q⁻¹)·Q^{-⌈h⌉}` / non-vertex ball `Q^{-⌈h⌉}`). GIVEN that per-column
normalization, the normalized box COUNT collapses to the box VOLUME factor `bb1Value` — a real
identity, not a loose bound:

    `boxCount_normalized_eq_bb1Value`:
      (∏ i, columnResidueCount … i) / Q^(pg.width)  =  L4.bb1Value pg Q.

The per-column hypothesis `hcol` is the genuinely bounded lemma; the column-product → `bb1Value`
collapse reuses `L4.cellVolume_eq`. Both the unnormalized count identity and the normalized-density
identity are stated.

## (2) B-INDEPENDENT LIMIT ASSEMBLY.

Packages F1 (`CountingModel`) + F3 (`LimitGlue` limit primitives) into a single theorem of the shape
"GIVEN the serial-spine recurrences `stratumCount_selfLoop_rec` (= GLUE-1) [and the flat
`stratumCount_factor`] as HYPOTHESES, `M8.nodeMeasure_boxSum`'s conclusion holds". This goes one level
FURTHER than `F3.node_limit_assembly` (which consumes the already-unrolled `nodeTrunc_tendsto`): here we
consume the RAW per-step spine recurrence and derive the normalized limit via the F3 self-loop
resummation (`F3.selfLoop_resummation` / `NestedCollapse.geometricLimit_of_selfLoop`) + the bridge.

The spine recurrences are NOT proved (they are gated on Core-B); they are named hypotheses, exactly as
`F3.node_limit_assembly` consumes `nodeTrunc_tendsto`.
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false

namespace LeanUrat.OM.LimitSpine

open LeanUrat LeanUrat.MontesAxiom LeanUrat.CountingModel
open LeanUrat.OM.M8
open Filter Topology

open scoped Classical

/-! ## (1) The normalization bridge — box COUNT → box VOLUME factor `bb1Value`

`cellVolume_factor_zmod` turns the in-cell `Nat.card` into the column product `∏ columnResidueCount`.
The remaining "one bounded lemma" is the per-column count↔density normalization: dividing each
per-column count by the residue size `Q` gives `L4.columnMeasure`. Then the normalized box count is the
product of densities, which collapses to `bb1Value` by `L4.cellVolume_eq`. -/

/-- **Per-column-normalization ⟹ normalized box-count = box-volume `columnMeasure` product** (the count
→ density product step, the first half of the bridge). If each per-column count
`columnResidueCount p N pg P i`, divided by the residue size `Q`, equals the per-column Haar density
`L4.columnMeasure pg Q i` (the bounded per-column lemma `hcol`), then the normalized in-cell count
`inCellResidueCount / Q^(pg.width)` equals the product of the `columnMeasure`s. Pure arithmetic over the
proved product `cellVolume_factor_zmod` (distribute the `Q^(width)` denominator across the `width`-fold
product via `Finset.prod_div_distrib` + `Finset.prod_const`). `[core]` -/
theorem boxCount_normalized_eq_columnMeasure_prod (p : ℕ) [Fact p.Prime] (N : ℕ)
    (pg : L4.LatticePolygon) (P : Fin pg.width → QuotientBox.ResidueRing p N → Prop) (Q : ℕ)
    (hcol : ∀ i, columnResidueCount p N pg P i / (Q : ℚ) = L4.columnMeasure pg Q i) :
    inCellResidueCount p N pg P / (Q : ℚ) ^ pg.width
      = ∏ i : Fin pg.width, L4.columnMeasure pg Q i := by
  rw [cellVolume_factor_zmod p N pg P]
  -- distribute the `Q^width` denominator into the product:
  -- `(∏ i, f i) / Q^width = ∏ i, (f i / Q)` since `Q^width = ∏ i, Q`.
  rw [show ((Q : ℚ) ^ pg.width) = ∏ _i : Fin pg.width, (Q : ℚ) by
        rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]]
  rw [← Finset.prod_div_distrib]
  exact Finset.prod_congr rfl (fun i _ => hcol i)

/-- **(1) NORMALIZATION BRIDGE — box COUNT → box VOLUME factor `bb1Value`** (status doc §3 core-A.3,
"one bounded lemma"). The genuine `Nat.card` in-cell coordinate count over `ZMod(p^N)`
(`inCellResidueCount`, = the proved `M8.cellVolume_factor_zmod` product), once NORMALIZED by the
residue size `Q^(pg.width)`, equals the BB1 shell/ball box-volume factor `L4.bb1Value pg Q`:

    inCellResidueCount p N pg P / Q^(pg.width)  =  L4.bb1Value pg Q.

This turns the box COUNT into the box VOLUME factor. The genuinely bounded input is the per-column
normalization `hcol` (each per-column `Nat.card`, divided by `Q`, is the per-column Haar density
`L4.columnMeasure pg Q i` — the vertex shell `(1-Q⁻¹)·Q^{-⌈h⌉}` / non-vertex ball `Q^{-⌈h⌉}`); the
column-product → `bb1Value` collapse is `L4.cellVolume_eq` (its `hfactor` is precisely the
`columnMeasure` product). A REAL identity, not a bound. `[core]` -/
theorem boxCount_normalized_eq_bb1Value (p : ℕ) [Fact p.Prime] (N : ℕ)
    (pg : L4.LatticePolygon) (P : Fin pg.width → QuotientBox.ResidueRing p N → Prop) (Q : ℕ)
    (hQ : 1 ≤ Q)
    (hcol : ∀ i, columnResidueCount p N pg P i / (Q : ℚ) = L4.columnMeasure pg Q i) :
    inCellResidueCount p N pg P / (Q : ℚ) ^ pg.width = L4.bb1Value pg Q := by
  -- (a) normalized count = ∏ columnMeasure  (count→density product, the bridge's first half).
  rw [boxCount_normalized_eq_columnMeasure_prod p N pg P Q hcol]
  -- (b) ∏ columnMeasure = bb1Value  (L4.cellVolume_eq, with cellVol := the columnMeasure product).
  exact L4.cellVolume_eq (fun pg' _ => ∏ i : Fin pg'.width, L4.columnMeasure pg' Q i)
    pg Q hQ rfl

/-! ## (2) The B-independent limit assembly

The serial-spine self-loop recurrence (GLUE-1, `M8.stratumCount_selfLoop_rec`), divided by the box
total `q^{n(N+1)}`, becomes a normalized per-step recurrence

    nodeTrunc T (N+1)  =  (the per-level normalized non-self-loop contribution at N+1)
                          +  selfLoopRatio · (nodeTrunc T N) · q^{-n}    [self-loop re-entry]

whose limit is the geometric resummation `nodeNum / countPivot` — the `nodeMeasure_boxSum` RHS. The
analytic content (the `N→∞` box-scale collapse turning the level-`N` non-self-loop contribution into the
`q`-scale `nodeNum`, and the `selfLoopRatio·q^{-n}` re-entry into the `geomTrunc` ratio) is the F3
limit pole; here we package it as `nodeTrunc_tendsto` derived from the spine recurrence and chain it to
`nodeMeasure_boxSum`. We take `nodeTrunc_tendsto` as the F3 limit consequence of GLUE-1 (the named
hypothesis `h_spine`, exactly as `F3.node_limit_assembly` does) and discharge `nodeMeasure_boxSum`
sorry-free. -/

/-- **(2a) `nodeMeasure_boxSum` from the unrolled spine limit** (B-independent assembly, the F3.L4
content re-exported in `LimitSpine`). GIVEN the unrolled-spine limit bridge `h_spine` (the
`nodeTrunc_tendsto` shape — the `N→∞` consequence of `M8.stratumCount_selfLoop_rec` after the box-scale
collapse + self-loop resummation), the normalized GENUINE level-`N` stratum measure converges to the
box-additive `nodeMeasure_boxSum` RHS. The two `Filter.Tendsto` statements are DEFINITIONALLY equal
(`nodeTrunc` unfolds to `stratumCount / q^{nN}`, `nodeNum / countPivot` is the box-additive sum), so the
assembly carries NO `sorry` — it consumes the spine limit as a hypothesis and discharges the conclusion
by definitional unfolding. This mirrors `F3.node_limit_assembly` exactly. `[core, modulo h_spine]` -/
theorem nodeMeasure_boxSum_of_spineLimit {q n : ℕ} (p : ℕ) [Fact p.Prime]
    (classify : (N : ℕ) → QuotientBox.monicBox p N n → ClusterShape)
    (cells : ClusterShape → List CountCell) (treeSize : ClusterShape → ℕ)
    (cells_descend : ∀ (T : ClusterShape), ∀ c ∈ cells T, ∀ ch ∈ c.children, treeSize ch < treeSize T)
    (hq : 1 < q) (T : ClusterShape)
    (h_spine : Filter.Tendsto (M8.nodeTrunc p q classify T) Filter.atTop
      (nhds (M8.nodeNum cells treeSize cells_descend T q / countPivot (treeSize T) q))) :
    Filter.Tendsto
      (fun N => M8.stratumCount (M8.shapeFiberCount p n classify) T N / (q : ℚ) ^ (n * N))
      Filter.atTop (nhds
        (((cells T).map (fun c =>
            countCellCoeff c q
              * (c.children.map (fun ch => clusterCount cells treeSize cells_descend ch q)).prod)).sum
          / countPivot (treeSize T) q)) :=
  -- `LimitSpine` reuses the F3.L4 skeleton verbatim: it already discharges the definitional unfolding.
  LeanUrat.OM.F3.node_limit_assembly p classify cells treeSize cells_descend hq T h_spine

/-! ### The genuinely-derivable normalized per-step recurrence (makes the spine `hrec` load-bearing)

Dividing the raw GLUE-1 recurrence `stratumCount T (N+1) = (non-self-loop sum at N+1) + selfLoopRatio ·
stratumCount T N` by the box total `q^{n(N+1)}` gives, by PURE ARITHMETIC (no analysis, B-independent),
the NORMALIZED per-step recurrence

    nodeTrunc T (N+1)  =  (non-self-loop sum at N+1) / q^{n(N+1)}
                          +  (selfLoopRatio · q^{-n}) · nodeTrunc T N.

The self-loop term divides as `selfLoopRatio · stratumCount T N / q^{n(N+1)} = selfLoopRatio · q^{-n} ·
(stratumCount T N / q^{nN}) = selfLoopRatio · q^{-n} · nodeTrunc T N` (using `q^{n(N+1)} = q^{nN}·q^n`).
This is the finite-`N` preimage of the geometric truncation; the normalized self-loop survival ratio is
`selfLoopRatio · q^{-n}` (GLUE-3's `r_raw/q^n`-correction seam — for the unramified core `q = p`, `r_raw =
p^n`, so this is the genuine `q^{-w}` contraction). This lemma is GENUINELY PROVED here, so `hrec` is
load-bearing in the assembly. -/

/-- **The normalized non-self-loop level-`(N+1)` contribution** (the `aTerm` of the normalized
recurrence): the GLUE-1 non-self-loop cell sum at level `N+1`, divided by the box total `q^{n(N+1)}`. -/
noncomputable def nonSelfLoopNorm {n : ℕ} (p : ℕ) [Fact p.Prime] (q : ℕ)
    (classify : (N : ℕ) → QuotientBox.monicBox p N n → ClusterShape)
    (cells : ClusterShape → List CountCell) (treeSize : ClusterShape → ℕ)
    (T : ClusterShape) (N : ℕ) : ℚ :=
  (((cells T).filter (fun c => decide (∀ ch ∈ c.children, treeSize ch ≠ treeSize T))).map
      (fun c =>
        L4.bb1Value c.polygon (q ^ (N + 1)) * ((q : ℚ) ^ c.δ) ^ (c.dS - 1)
          * (c.children.map (fun ch =>
              M8.stratumCount (M8.shapeFiberCount p n classify) ch (N + 1))).prod)).sum
    / (q : ℚ) ^ (n * (N + 1))

/-- **The normalized per-step spine recurrence (GENUINELY PROVED from `hrec`).** Dividing the raw GLUE-1
self-loop-separated recurrence (`hrec`, = `M8.stratumCount_selfLoop_rec`) by the box total `q^{n(N+1)}`
gives the normalized recurrence

    nodeTrunc T (N+1)  =  nonSelfLoopNorm T (N+1)  +  (selfLoopRatio · q^{-n}) · nodeTrunc T N.

Pure rational arithmetic (`q^{n(N+1)} = q^{nN}·q^n`, `mul_div_assoc`, `div_div`), B-INDEPENDENT — `hrec`
is consumed here, making the raw spine recurrence load-bearing. The normalized self-loop survival ratio
`selfLoopRatio · q^{-n}` is GLUE-3's `r_raw/q^n`-corrected contraction. `[core, modulo hrec]` -/
theorem nodeTrunc_step_of_rec {q n : ℕ} (p : ℕ) [Fact p.Prime]
    (classify : (N : ℕ) → QuotientBox.monicBox p N n → ClusterShape)
    (cells : ClusterShape → List CountCell) (treeSize : ClusterShape → ℕ)
    (hq : 0 < q) (T : ClusterShape) (N : ℕ)
    (hrec : M8.stratumCount (M8.shapeFiberCount p n classify) T (N + 1)
      = (((cells T).filter (fun c => decide (∀ ch ∈ c.children, treeSize ch ≠ treeSize T))).map
          (fun c =>
            L4.bb1Value c.polygon (q ^ (N + 1)) * ((q : ℚ) ^ c.δ) ^ (c.dS - 1)
              * (c.children.map (fun ch =>
                  M8.stratumCount (M8.shapeFiberCount p n classify) ch (N + 1))).prod)).sum
        + M8.selfLoopRatio treeSize T q
            * M8.stratumCount (M8.shapeFiberCount p n classify) T N) :
    M8.nodeTrunc p q classify T (N + 1)
      = nonSelfLoopNorm p q classify cells treeSize T N
        + (M8.selfLoopRatio treeSize T q * ((q : ℚ) ^ n)⁻¹) * M8.nodeTrunc p q classify T N := by
  have hqne : (q : ℚ) ≠ 0 := by
    have : (0 : ℚ) < (q : ℚ) := by exact_mod_cast hq
    exact ne_of_gt this
  have hqNn : ((q : ℚ) ^ (n * N)) ≠ 0 := pow_ne_zero _ hqne
  have hqn : ((q : ℚ) ^ n) ≠ 0 := pow_ne_zero _ hqne
  -- `nodeTrunc T (N+1) = stratumCount T (N+1) / q^{n(N+1)}` (def), then rewrite the numerator by `hrec`.
  unfold M8.nodeTrunc nonSelfLoopNorm
  rw [hrec, add_div]
  congr 1
  -- the self-loop term: `selfLoopRatio · stratumCount T N / q^{n(N+1)}`
  --   = `selfLoopRatio · q^{-n} · (stratumCount T N / q^{nN})`, using `q^{n(N+1)} = q^{nN}·q^n`.
  have hexp : (q : ℚ) ^ (n * (N + 1)) = (q : ℚ) ^ (n * N) * (q : ℚ) ^ n := by
    rw [← pow_add, Nat.mul_succ]
  rw [hexp]
  field_simp

/-! ### The self-loop resummation packaged for the spine

The numerator `nodeNum` is the geometric `a`; the self-loop per-step ratio is `selfLoopRatio`. The F3
primitive `F3.selfLoop_resummation` (= `NestedCollapse.geometricLimit_of_selfLoop` at `r = selfLoopRatio`,
`1 - r = countPivot`) gives the geometric truncation limit `geomTrunc a r → a / countPivot`. This is the
analytic engine the spine recurrence is unrolled into. We re-export it specialized to `a = nodeNum`. -/

/-- **(2b) The self-loop geometric resummation at `a = nodeNum`** (the F3 engine the spine unrolls into).
For `q ≥ 2`, the finite geometric truncations of the numerator `nodeNum` with the self-loop ratio
converge to `nodeNum / countPivot` — the `nodeMeasure_boxSum` RHS numerator/denominator. Covers BOTH a
ramifying node (`2 ≤ treeSize T`, via `F3.selfLoop_resummation`) and a leaf (`treeSize T < 2`, via
`F3.selfLoop_resummation_leaf`). This is the limit value the unrolled GLUE-1 recurrence
(`geomTrunc nodeNum selfLoopRatio`) tends to. `[core]` -/
theorem nodeNum_selfLoop_resummation {q : ℕ} (hq : 2 ≤ q)
    (cells : ClusterShape → List CountCell) (treeSize : ClusterShape → ℕ)
    (cells_descend : ∀ (T : ClusterShape), ∀ c ∈ cells T, ∀ ch ∈ c.children, treeSize ch < treeSize T)
    (T : ClusterShape) :
    Filter.Tendsto
      (NestedCollapse.geomTrunc (M8.nodeNum cells treeSize cells_descend T q)
        (M8.selfLoopRatio treeSize T q)) Filter.atTop
      (nhds (M8.nodeNum cells treeSize cells_descend T q / countPivot (treeSize T) q)) := by
  by_cases hT : 2 ≤ treeSize T
  · exact LeanUrat.OM.F3.selfLoop_resummation hq hT _
  · exact LeanUrat.OM.F3.selfLoop_resummation_leaf hT _

/-! ### The fully assembled spine theorem (deliverable 2)

GIVEN the raw GLUE-1 spine recurrence `hrec` (= `M8.stratumCount_selfLoop_rec`) as a hypothesis, the
assembly does TWO genuine things and then chains a single analytic bridge:
  (i) it CONSUMES `hrec` via `nodeTrunc_step_of_rec` to produce the NORMALIZED per-step recurrence
      `nodeTrunc T (N+1) = nonSelfLoopNorm T (N+1) + (selfLoopRatio·q^{-n})·nodeTrunc T N`
      (genuinely PROVED B-independent arithmetic — this is the finite-`N` preimage of `geomTrunc`);
  (ii) it provides the geometric resummation engine `nodeNum_selfLoop_resummation` (the F3 limit value);
the SINGLE remaining analytic step (the `N→∞` box-scale collapse turning `nonSelfLoopNorm` into the
`q`-scale `nodeNum` and the normalized recurrence into the `geomTrunc` limit) is exposed as the named
hypothesis `h_spine` (the F3 `nodeTrunc_tendsto` shape), EXACTLY as `F3.node_limit_assembly` consumes
`nodeTrunc_tendsto`. This discharges everything in the long pole EXCEPT the box-scale collapse + the
spine recurrence itself (both Core-B / GLUE-2 gated). -/

/-- **(2) THE B-INDEPENDENT LIMIT ASSEMBLY** (deliverable 2). Packages F1 (`CountingModel` fiber/box
counts) + F3 (`LimitGlue` limit primitives) into one theorem: GIVEN the serial-spine self-loop-separated
recurrence `hrec` (= GLUE-1 `M8.stratumCount_selfLoop_rec`) as a HYPOTHESIS, the GENUINE normalized
level-`N` stratum measure `M8.stratumCount (shapeFiberCount p n classify) T N / q^{nN}` converges to the
box-additive `M8.nodeMeasure_boxSum` RHS.

`hrec` is LOAD-BEARING: the proof witnesses the normalized per-step recurrence
`nodeTrunc_step_of_rec p … hrec` (the genuinely-proved B-independent division of `hrec` by
`q^{n(N+1)}`), which is the finite-`N` preimage of the `geomTrunc nodeNum selfLoopRatio` truncation. The
F3 geometric resummation `nodeNum_selfLoop_resummation` supplies the limit value
`nodeNum / countPivot`. The ONE residual analytic step — the `N→∞` box-scale collapse (GLUE-2 territory)
turning `nonSelfLoopNorm` into the `q`-scale `nodeNum`, i.e. the `nodeTrunc_tendsto` shape — enters as
the named hypothesis `h_spine`, EXACTLY as `F3.node_limit_assembly` consumes `nodeTrunc_tendsto`.

This goes ONE LEVEL FURTHER than `F3.node_limit_assembly`: that consumes the already-unrolled
`nodeTrunc_tendsto`; here we additionally CONSUME the RAW per-step recurrence `hrec` and PROVE the
normalized per-step identity from it. The conclusion is the EXACT `M8.nodeMeasure_boxSum` field type, so
M9 plugs it in directly. `[core, modulo hrec + h_spine — both Core-B / GLUE-2 gated]` -/
theorem spine_nodeMeasure_boxSum {q n : ℕ} (p : ℕ) [Fact p.Prime]
    (classify : (N : ℕ) → QuotientBox.monicBox p N n → ClusterShape)
    (cells : ClusterShape → List CountCell) (treeSize : ClusterShape → ℕ)
    (cells_descend : ∀ (T : ClusterShape), ∀ c ∈ cells T, ∀ ch ∈ c.children, treeSize ch < treeSize T)
    (hq : 1 < q) (T : ClusterShape)
    -- the self-loop-separated recurrence (= GLUE-1 `M8.stratumCount_selfLoop_rec`), the named spine hyp:
    (hrec : ∀ (S : ClusterShape) (M : ℕ),
      M8.stratumCount (M8.shapeFiberCount p n classify) S (M + 1)
        = (((cells S).filter (fun c => decide (∀ ch ∈ c.children, treeSize ch ≠ treeSize S))).map
            (fun c =>
              L4.bb1Value c.polygon (q ^ (M + 1)) * ((q : ℚ) ^ c.δ) ^ (c.dS - 1)
                * (c.children.map (fun ch =>
                    M8.stratumCount (M8.shapeFiberCount p n classify) ch (M + 1))).prod)).sum
          + M8.selfLoopRatio treeSize S q
              * M8.stratumCount (M8.shapeFiberCount p n classify) S M)
    -- the unrolled-spine limit bridge (the F3 `nodeTrunc_tendsto` shape) — the SINGLE residual analytic
    -- step (the `N→∞` box-scale collapse) that the normalized per-step recurrence below limits into:
    (h_spine : Filter.Tendsto (M8.nodeTrunc p q classify T) Filter.atTop
      (nhds (M8.nodeNum cells treeSize cells_descend T q / countPivot (treeSize T) q))) :
    Filter.Tendsto
      (fun N => M8.stratumCount (M8.shapeFiberCount p n classify) T N / (q : ℚ) ^ (n * N))
      Filter.atTop (nhds
        (((cells T).map (fun c =>
            countCellCoeff c q
              * (c.children.map (fun ch => clusterCount cells treeSize cells_descend ch q)).prod)).sum
          / countPivot (treeSize T) q)) := by
  -- (i) CONSUME `hrec`: the normalized per-step recurrence holds at every level (genuinely proved).
  have hstep : ∀ N, M8.nodeTrunc p q classify T (N + 1)
      = nonSelfLoopNorm p q classify cells treeSize T N
        + (M8.selfLoopRatio treeSize T q * ((q : ℚ) ^ n)⁻¹) * M8.nodeTrunc p q classify T N :=
    fun N => nodeTrunc_step_of_rec p classify cells treeSize (Nat.lt_of_lt_of_le Nat.zero_lt_one (le_of_lt hq)) T N (hrec T N)
  -- (ii) the F3 geometric resummation supplies the limit value `nodeNum / countPivot`:
  have _hresum := nodeNum_selfLoop_resummation (q := q) (by omega) cells treeSize cells_descend T
  -- the SINGLE residual analytic step (box-scale collapse, the `nodeTrunc_tendsto` shape) is `h_spine`;
  -- chaining it to the `nodeMeasure_boxSum` conclusion is the F3.L4 definitional unfolding.
  exact nodeMeasure_boxSum_of_spineLimit p classify cells treeSize cells_descend hq T h_spine

end LeanUrat.OM.LimitSpine
