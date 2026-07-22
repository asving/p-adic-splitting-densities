/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.OM.RealInstanceW4
import LeanUrat.OM.RealInstanceWGates

/-!
# OM/RealInstanceW4Gates — the Wave-4 MIXED-e gates (G1 mixed value, G2 σ-separation)
(blueprint `notes/WILD_WAVE4_BLUEPRINT_2026-07-22.md` §2-W4b)

Machine-checked gates pinned to the Wave-4 instance's own density
`g_σ(q') := ∑_{T ∈ omMenu4 n K σ} C4 T q'` — the exact sum in the conclusion of
`RealInstanceW4.montes_unconditional_w4`.

* **G1 (mixed value).** At the mixed type `σ₅ = ⟨{(2,1),(3,1)}⟩` (`n = 5`, one `e = 2` factor,
  one `e = 3` factor — TWO distinct ramification indices, the first genuinely multi-slope menu
  entry): `mixedOK 5 σ₅` holds, the Wave-4 menu is the canonical SINGLETON
  `{multiSideLit 5 [(0,2),(2,1),(5,0)] [[(1,1)],[(1,1)]]}` (`gate_w4_menu` — canonical path
  `(0,2) → (2,1) → (5,0)`, ascending `e`, slopes `−1/2` then `−1/3`, steepest first — the
  erratum-corrected F4 order). Per-side closed values at every prime (each through
  `omCount_oneSideShape_closed` on the re-scoped `sideSubShape`):
  side `e = 2`: `(p−1)·p⁻⁵` (Newton exponent `4` + `sideDeg 1`; `= 1/32` at `realP = 2`);
  side `e = 3`: `(p−1)·p⁻⁴` (Newton exponent `3` + `sideDeg 1`; `= 1/16` at `realP = 2`).
  Product `(p−1)²·p⁻⁹ = 1/512` at `p = 2` (`gate_w4_value` — the blueprint's EXTERNALLY
  verified exact value). Volume reconciliation `gate_w4_volume_reconciliation`: the per-side
  exponent sum `5 + 4 = 9` IS the whole-path `newtonExponent 7 + Σ sideDeg 2` (the blueprint's
  `V = 9` with cross-term `p⁻²`). Instance pin `gate_w4_countingDensity`: the genuine
  DECIDED-LIMIT density of `realMW4` at `(n, K) = (5, 3)` is `1/512` — via `realDW4`'s
  decomposition theorem, so this consumes the instance's `partition` + `stratum_tendsto_C`
  discharges INCLUDING the genuine order-1 mixed counting leg (`stratum_tendsto_C4_mixed` ←
  `hnode_multiSideProduct`).
* **G2 (σ-separation).** The mixed value differs from the constant-e5 type's value at the same
  degree and prime: `value(σ₅) = 1/512 ≠ 1/64 = value(⟨{(5,1)}⟩ at K = 1)` — both through the
  REAL Wave-4 instances (`gate_w4_separation`; the e5 leg routes through the recovery gate
  `montes_w4_recovers`, so it also exercises the Wave-3 branch of the Wave-4 instance).
* **G4 (mutation evidence)** — see the comment block before the `AxCheck` section.

**Honest scope** (inherited from the capstone, blueprint §0/§3): the mixed value below is the
density of the ONE canonical mixed stratum (per-side minimal height `k = 1`, all-μ=1) — the
leading term of the type's density, NOT any tower/window resummation; no exhaustiveness claim.

Leaf module: no existing file is modified. No axiom, no sorry. Footprints must be Lean core
ONLY (`AxCheck` section).
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false

namespace LeanUrat.OM.RealInstanceW4Gates

open LeanUrat LeanUrat.MontesAxiom Polynomial
open LeanUrat.OM
open LeanUrat.OM.CellMenu

/-! ## 0. The gate types and the canonical mixed data of σ₅ -/

/-- **The gate mixed type** `σ₅ = ⟨{(2,1),(3,1)}⟩`: degree `5 = 2·1 + 3·1`, ramification
indices `{2, 3}` — two distinct `e`'s, the minimal genuinely mixed-e example. -/
def sigma5 : FactorizationType := ⟨{(2, 1), (3, 1)}⟩

/-- **The comparison constant-e type** `⟨{(5,1)}⟩`: totally ramified quintic (`e = 5`,
`F = fSum = 1`), same degree `5`. -/
def ramType5 : FactorizationType := ⟨{(5, 1)}⟩

/-- σ₅ is mixed-OK: nonempty, all `e ≥ 2`, `f ≥ 1`, degree `5`, TWO distinct `e`-values. -/
theorem mixedOK_sigma5 : MultiSlopeMenu.mixedOK 5 sigma5 :=
  ⟨by decide, by decide, by decide, by decide⟩

theorem fSum_sigma5 : WildMenu.fSum sigma5 = 2 := by decide

/-- The ascending `e`-list of σ₅ is `[2, 3]`. (`Finset.sort` does not kernel-reduce — the sort
is discharged by `Finset.sort_insert`/`sort_singleton`, not `decide`; mirror of the
`wShape_ramType2` precedent.) -/
theorem eVals_sigma5 : MultiSlopeMenu.eVals sigma5 = [2, 3] := by
  rw [MultiSlopeMenu.eVals,
    show (sigma5.data.map Prod.fst).toFinset = ({2, 3} : Finset ℕ) from by decide]
  rw [Finset.sort_insert]
  · rw [Finset.sort_singleton]
  · intro b hb
    rw [Finset.mem_singleton] at hb
    omega
  · decide

theorem Fof_sigma5_two : MultiSlopeMenu.Fof sigma5 2 = 1 := by decide

theorem Fof_sigma5_three : MultiSlopeMenu.Fof sigma5 3 = 1 := by decide

theorem shapeOf_sigma5_two : MultiSlopeMenu.shapeOf sigma5 2 = [(1, 1)] := by
  rw [MultiSlopeMenu.shapeOf,
    show (sigma5.data.filter (fun pr => pr.1 = 2)).map Prod.snd = ({1} : Multiset ℕ) from by
      decide,
    Multiset.sort_singleton]
  rfl

theorem shapeOf_sigma5_three : MultiSlopeMenu.shapeOf sigma5 3 = [(1, 1)] := by
  rw [MultiSlopeMenu.shapeOf,
    show (sigma5.data.filter (fun pr => pr.1 = 3)).map Prod.snd = ({1} : Multiset ℕ) from by
      decide,
    Multiset.sort_singleton]
  rfl

/-- **The canonical mixed path of σ₅** is `(0,2) → (2,1) → (5,0)`: total height
`H = F₂ + F₃ = 2`, then the `e = 2` side (run `2`, drop `1`, slope `−1/2`) FIRST, then the
`e = 3` side (run `3`, drop `1`, slope `−1/3`) — ascending `e` = ascending slope, the
erratum-corrected F4-admissible steepest-first order (blueprint §0). -/
theorem mixedPath_sigma5 :
    MultiSlopeMenu.mixedPath sigma5 = [(0, 2), (2, 1), (5, 0)] := by
  rw [show MultiSlopeMenu.mixedPath sigma5
      = ((0 : ℕ), WildMenu.fSum sigma5)
        :: MultiSlopeMenu.vertsFrom sigma5 (MultiSlopeMenu.eVals sigma5) 0
            (WildMenu.fSum sigma5) from rfl,
    eVals_sigma5, fSum_sigma5]
  rw [show MultiSlopeMenu.vertsFrom sigma5 [2, 3] 0 2
      = (0 + 2 * MultiSlopeMenu.Fof sigma5 2, 2 - MultiSlopeMenu.Fof sigma5 2)
        :: MultiSlopeMenu.vertsFrom sigma5 [3] (0 + 2 * MultiSlopeMenu.Fof sigma5 2)
            (2 - MultiSlopeMenu.Fof sigma5 2) from rfl,
    Fof_sigma5_two]
  rw [show MultiSlopeMenu.vertsFrom sigma5 [3] (0 + 2 * 1) (2 - 1)
      = (0 + 2 * 1 + 3 * MultiSlopeMenu.Fof sigma5 3, 2 - 1 - MultiSlopeMenu.Fof sigma5 3)
        :: MultiSlopeMenu.vertsFrom sigma5 []
            (0 + 2 * 1 + 3 * MultiSlopeMenu.Fof sigma5 3)
            (2 - 1 - MultiSlopeMenu.Fof sigma5 3) from rfl,
    Fof_sigma5_three]
  rfl

/-- The canonical per-side shapes of σ₅: one degree-1 residual factor per side. -/
theorem mixedSh_sigma5 :
    MultiSlopeMenu.mixedSh sigma5 = [[(1, 1)], [(1, 1)]] := by
  rw [MultiSlopeMenu.mixedSh, eVals_sigma5]
  rw [List.map_cons, List.map_cons, List.map_nil, shapeOf_sigma5_two, shapeOf_sigma5_three]

/-- **The Wave-4 menu of σ₅ is EXACTLY the canonical mixed singleton** — both Wave-3 legs are
EMPTY on a mixed type (σ₅ is neither unramified nor constant-e), at EVERY window bound `K`
(here the gate's `K = 3`). -/
theorem gate_w4_menu :
    MultiSlopeMenu.omMenu4 5 3 sigma5
      = {MultiSlopeMenu.multiSideLit 5 (MultiSlopeMenu.mixedPath sigma5)
          (MultiSlopeMenu.mixedSh sigma5)} :=
  MultiSlopeMenu.omMenu4_of_mixed mixedOK_sigma5

/-! ## 1. G1 — the per-side closed values and the mixed product 1/512 -/

/-- **The `e = 2` side factor at every prime**: `(p − 1)·p⁻⁵` — pool `p − 1` (one degree-1
unit-constant residual factor, `shapeCount_one_one`), volume exponent
`newtonExponent (mkPoly 2 [(0,2),(2,1)]) + sideDeg = 4 + 1 = 5` (the side re-scoped to its own
sub-width `2`, heights `2 → 1` UNCHANGED — `sideSubShape`). `= 1/32` at `p = 2`. -/
theorem gate_w4_side_e2 (p : ℕ) [Fact p.Prime] :
    OMCountV2.omCount (PathShapeMultiSideTree.sideSubShape
        ((((0 : ℕ), (2 : ℕ)), ((2 : ℕ), (1 : ℕ))) : (ℕ × ℕ) × (ℕ × ℕ)) [((1 : ℕ), (1 : ℕ))]) p
      = ((p : ℚ) - 1) * ((p : ℚ) ^ 5)⁻¹ := by
  rw [show PathShapeMultiSideTree.sideSubShape
        ((((0 : ℕ), (2 : ℕ)), ((2 : ℕ), (1 : ℕ))) : (ℕ × ℕ) × (ℕ × ℕ)) [((1 : ℕ), (1 : ℕ))]
      = PathShape.oneSideShape 2 ((((0 : ℕ), (2 : ℕ)), ((2 : ℕ), (1 : ℕ))) : (ℕ × ℕ) × (ℕ × ℕ))
          [((1 : ℕ), (1 : ℕ))] from rfl]
  rw [PathShape.omCount_oneSideShape_closed 2
      ((((0 : ℕ), (2 : ℕ)), ((2 : ℕ), (1 : ℕ))) : (ℕ × ℕ) × (ℕ × ℕ))
      [((1 : ℕ), (1 : ℕ))] (by decide) (by decide) (by decide) (by decide) p]
  rw [CellCard.shapeCount_one_one]
  rw [show L4.newtonExponent (mkPoly 2 [((0 : ℕ), (2 : ℕ)), ((2 : ℕ), (1 : ℕ))])
      + sideDeg ((((0 : ℕ), (2 : ℕ)), ((2 : ℕ), (1 : ℕ))) : (ℕ × ℕ) × (ℕ × ℕ)) = 5 from by
    decide]
  have hp2 : 2 ≤ p := (Fact.out (p := p.Prime)).two_le
  rw [Nat.cast_sub (by omega : 1 ≤ p), Nat.cast_one]

/-- **The `e = 3` side factor at every prime**: `(p − 1)·p⁻⁴` — the side `(2,1) → (5,0)`
re-scoped to sub-width `3` with left endpoint translated to `(0,1)`: volume exponent
`newtonExponent (mkPoly 3 [(0,1),(3,0)]) + sideDeg = 3 + 1 = 4`. `= 1/16` at `p = 2`. -/
theorem gate_w4_side_e3 (p : ℕ) [Fact p.Prime] :
    OMCountV2.omCount (PathShapeMultiSideTree.sideSubShape
        ((((2 : ℕ), (1 : ℕ)), ((5 : ℕ), (0 : ℕ))) : (ℕ × ℕ) × (ℕ × ℕ)) [((1 : ℕ), (1 : ℕ))]) p
      = ((p : ℚ) - 1) * ((p : ℚ) ^ 4)⁻¹ := by
  rw [show PathShapeMultiSideTree.sideSubShape
        ((((2 : ℕ), (1 : ℕ)), ((5 : ℕ), (0 : ℕ))) : (ℕ × ℕ) × (ℕ × ℕ)) [((1 : ℕ), (1 : ℕ))]
      = PathShape.oneSideShape 3 ((((0 : ℕ), (1 : ℕ)), ((3 : ℕ), (0 : ℕ))) : (ℕ × ℕ) × (ℕ × ℕ))
          [((1 : ℕ), (1 : ℕ))] from rfl]
  rw [PathShape.omCount_oneSideShape_closed 3
      ((((0 : ℕ), (1 : ℕ)), ((3 : ℕ), (0 : ℕ))) : (ℕ × ℕ) × (ℕ × ℕ))
      [((1 : ℕ), (1 : ℕ))] (by decide) (by decide) (by decide) (by decide) p]
  rw [CellCard.shapeCount_one_one]
  rw [show L4.newtonExponent (mkPoly 3 [((0 : ℕ), (1 : ℕ)), ((3 : ℕ), (0 : ℕ))])
      + sideDeg ((((0 : ℕ), (1 : ℕ)), ((3 : ℕ), (0 : ℕ))) : (ℕ × ℕ) × (ℕ × ℕ)) = 4 from by
    decide]
  have hp2 : 2 ≤ p := (Fact.out (p := p.Prime)).two_le
  rw [Nat.cast_sub (by omega : 1 ≤ p), Nat.cast_one]

/-- **Volume reconciliation** (the blueprint's `V = 9` pin): the per-side exponent sum
`5 + 4 = 9` IS the whole-path box exponent `newtonExponent (mkPoly 5 path) + Σ sideDeg
= 7 + 2 = 9` — the per-side Newton exponents `4 + 3` re-assemble the whole-path `7` and the
`Σ sideDeg = 2` is the blueprint's cross-term `p⁻²` (the `prod_omCount_eq_blockCardinality`
factorization, pinned numerically at the gate path). -/
theorem gate_w4_volume_reconciliation :
    L4.newtonExponent (mkPoly 5 [((0 : ℕ), (2 : ℕ)), ((2 : ℕ), (1 : ℕ)), ((5 : ℕ), (0 : ℕ))])
        + ((sidePairs [((0 : ℕ), (2 : ℕ)), ((2 : ℕ), (1 : ℕ)), ((5 : ℕ), (0 : ℕ))]).map
            sideDeg).sum
      = 9 := by decide

/-- **G1, exact mixed value.** The Wave-4 capstone's own menu-sum density at the mixed type σ₅
and the real prime is EXACTLY `1/512 = (1/32)·(1/16) = (p−1)²·p⁻⁹` at `p = 2` — the per-side
product, the blueprint's EXTERNALLY verified value. -/
theorem gate_w4_value :
    (∑ T ∈ MultiSlopeMenu.omMenu4 5 3 sigma5, MultiSlopeMenu.C4 T M9.realP) = 1 / 512 := by
  rw [gate_w4_menu, Finset.sum_singleton,
    RealInstanceW4.C4_multiSideLit 5 sigma5 M9.realP, mixedPath_sigma5, mixedSh_sigma5]
  rw [show sidePairs [((0 : ℕ), (2 : ℕ)), ((2 : ℕ), (1 : ℕ)), ((5 : ℕ), (0 : ℕ))]
      = [((((0 : ℕ), (2 : ℕ)), ((2 : ℕ), (1 : ℕ))) : (ℕ × ℕ) × (ℕ × ℕ)),
         ((((2 : ℕ), (1 : ℕ)), ((5 : ℕ), (0 : ℕ))) : (ℕ × ℕ) × (ℕ × ℕ))] from rfl]
  simp only [List.zipWith_cons_cons, List.zipWith_nil_right,
    List.prod_cons, List.prod_nil, mul_one]
  rw [gate_w4_side_e2 M9.realP, gate_w4_side_e3 M9.realP]
  norm_num [M9.realP]

/-- **G1, pinned to the REAL instance**: the genuine DECIDED-LIMIT density of the Wave-4
counting model `realMW4` at the mixed type σ₅ equals `1/512` — via `realDW4`'s decomposition
theorem, so this consumes the instance's `partition` + `stratum_tendsto_C` discharges,
INCLUDING the genuine order-1 mixed counting leg (`stratum_tendsto_C4_mixed` ←
`hnode_multiSideProduct` over `classify1` fibers), not just the engine evaluator. -/
theorem gate_w4_countingDensity :
    (RealInstanceW4.realMW4 5 3 (by norm_num)).countingDensity sigma5 = 1 / 512 := by
  rw [LeanUrat.MontesV2.MontesDataV2.countingDensity_eq_sum_coeff
    (RealInstanceW4.realDW4 5 3 (by norm_num))]
  exact gate_w4_value

/-! ## 2. G2 — σ-separation (mixed 1/512 vs constant-e5 1/64 at the same degree and prime) -/

theorem not_mixedOK_ramType5 : ¬ MultiSlopeMenu.mixedOK 5 ramType5 := by
  rintro ⟨-, -, -, hcard⟩
  have h1 : (ramType5.data.map Prod.fst).toFinset.card = 1 := by decide
  omega

theorem constERam_ramType5 : WildMenu.constERam 5 ramType5 :=
  ⟨5, by norm_num, by decide, by decide, by decide⟩

theorem fSum_ramType5 : WildMenu.fSum ramType5 = 1 := by decide

theorem wShape_ramType5 : WildMenu.wShape ramType5 = [((1 : ℕ), (1 : ℕ))] := by
  rw [WildMenu.wShape, show ramType5.data.map Prod.snd = ({1} : Multiset ℕ) from rfl,
    Multiset.sort_singleton]
  rfl

/-- The window-1 Wave-3 menu of the constant-e5 type is the single `k = 1` leg. -/
theorem gate_w4_e5_menu :
    WildMenuW3.omMenuW3 5 1 ramType5 = {WildMenuW3.ramShapeAt 5 ramType5 1} := by
  rw [WildMenuW3.omMenuW3_ram_of_constE constERam_ramType5, WildMenuW3.admissibleK_one,
    Finset.image_singleton]

/-- The constant-e5 leg's closed value at every prime: `(p − 1)·p⁻⁶` (Newton exponent
`5` + `sideDeg 1`; `= 1/64` at `p = 2`). -/
theorem gate_w4_e5_omCount (p : ℕ) [Fact p.Prime] :
    OMCountV2.omCount (ClassifierBridgeFiber.Tselfloop 5
        (((0, 1), (5, 0)) : (ℕ × ℕ) × (ℕ × ℕ)) [((1 : ℕ), (1 : ℕ))]) p
      = ((p : ℚ) - 1) * ((p : ℚ) ^ 6)⁻¹ := by
  rw [RealInstanceWGates.omCount_Tselfloop_closed 5 1 [((1 : ℕ), (1 : ℕ))]
      (by decide) (by decide) (by decide) (by decide) p]
  rw [CellCard.shapeCount_one_one]
  rw [show L4.newtonExponent (mkPoly 5 [((0 : ℕ), (1 : ℕ)), ((5 : ℕ), (0 : ℕ))])
      + sideDeg (((0, 1), (5, 0)) : (ℕ × ℕ) × (ℕ × ℕ)) = 6 from by decide]
  have hp2 : 2 ≤ p := (Fact.out (p := p.Prime)).two_le
  rw [Nat.cast_sub (by omega : 1 ≤ p), Nat.cast_one]

/-- The Wave-4 instance's decided-limit density at the constant-e5 type (window `K = 1`) is
`1/64` — routed through the RECOVERY gate `montes_w4_recovers` (so this leg also exercises the
Wave-3 branch of the Wave-4 instance). -/
theorem gate_w4_e5_countingDensity :
    (RealInstanceW4.realMW4 5 1 (by norm_num)).countingDensity ramType5 = 1 / 64 := by
  rw [RealInstanceW4.montes_w4_recovers 5 1 (by norm_num) ramType5 not_mixedOK_ramType5]
  show (∑ T ∈ WildMenuW3.omMenuW3 5 1 ramType5, OMCountV2.omCount T M9.realP) = 1 / 64
  rw [gate_w4_e5_menu, Finset.sum_singleton, WildMenuW3.ramShapeAt_one, fSum_ramType5,
    wShape_ramType5, gate_w4_e5_omCount M9.realP]
  norm_num [M9.realP]

/-- **G2 (σ-separation).** At degree `5` and the real prime, the mixed type σ₅ and the
constant-e5 type get DIFFERENT certified densities through the real Wave-4 instances:
`1/512 ≠ 1/64` — the mixed product coefficient is not a relabeling of any constant-e value. -/
theorem gate_w4_separation :
    (RealInstanceW4.realMW4 5 3 (by norm_num)).countingDensity sigma5
      ≠ (RealInstanceW4.realMW4 5 1 (by norm_num)).countingDensity ramType5 := by
  rw [gate_w4_countingDensity, gate_w4_e5_countingDensity]
  norm_num

end LeanUrat.OM.RealInstanceW4Gates

/-! ## G4 — mutation evidence (blueprint §2-W4b)

A scratch copy of `realDW4` with the per-shape coefficient mutated to the constant `0`
(`C := fun _ _ => 0`, all other fields verbatim, `stratum_tendsto_C` discharged by the same
`hNodeLimit_omMenu4`) FAILS to compile: the banked counting legs prove convergence to
`C4 T realP` (on the mixed leg, the genuine order-1 product limit), not to `0`, so the mutated
field demands a limit the legs do not supply. Verbatim compiler output (`lake env lean` on the
scratch `OM/ScratchG4W4.lean`, 2026-07-22; scratch deleted after capture):

```
LeanUrat/OM/ScratchG4W4.lean:16:37: error: Type mismatch
  RealInstanceW4.hNodeLimit_omMenu4 n K hn σ T hT
has type
  Filter.Tendsto (fun N => stratumCount4 n T N / ↑M9.realP ^ (n * N)) Filter.atTop (nhds (C4 T M9.realP))
but is expected to have type
  Filter.Tendsto (fun N => stratumCount4 n T N / ↑M9.realP ^ (n * N)) Filter.atTop (nhds 0)
```

The mutation gate certifies the instance's value tie is load-bearing, not decorative. -/

section AxCheck

-- Wave-4 gates: every gate must be Lean core ONLY
-- (`propext, Classical.choice, Quot.sound` — fewer is fine, MORE is a stop-the-line event).
#print axioms LeanUrat.OM.RealInstanceW4Gates.mixedOK_sigma5
#print axioms LeanUrat.OM.RealInstanceW4Gates.eVals_sigma5
#print axioms LeanUrat.OM.RealInstanceW4Gates.mixedPath_sigma5
#print axioms LeanUrat.OM.RealInstanceW4Gates.mixedSh_sigma5
#print axioms LeanUrat.OM.RealInstanceW4Gates.gate_w4_menu
#print axioms LeanUrat.OM.RealInstanceW4Gates.gate_w4_side_e2
#print axioms LeanUrat.OM.RealInstanceW4Gates.gate_w4_side_e3
#print axioms LeanUrat.OM.RealInstanceW4Gates.gate_w4_volume_reconciliation
#print axioms LeanUrat.OM.RealInstanceW4Gates.gate_w4_value
#print axioms LeanUrat.OM.RealInstanceW4Gates.gate_w4_countingDensity
#print axioms LeanUrat.OM.RealInstanceW4Gates.gate_w4_e5_menu
#print axioms LeanUrat.OM.RealInstanceW4Gates.gate_w4_e5_omCount
#print axioms LeanUrat.OM.RealInstanceW4Gates.gate_w4_e5_countingDensity
#print axioms LeanUrat.OM.RealInstanceW4Gates.gate_w4_separation
-- The Wave-4 capstones + recovery gate, re-censused from the gate module (the instance the
-- gates pin):
#print axioms LeanUrat.OM.RealInstanceW4.montes_unconditional_w4
#print axioms LeanUrat.OM.RealInstanceW4.montes_unconditional_w4_exhaustive
#print axioms LeanUrat.OM.RealInstanceW4.montes_w4_recovers

end AxCheck
