/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.OM.RealInstanceW
import LeanUrat.OM.RealInstanceV2Gates

/-!
# OM/RealInstanceWGates — the Wave-1 WILD gates (G1W non-vacuity, G2W σ-separation)
(blueprint `notes/WILD_WAVE1_BLUEPRINT_2026-07-21.md` §2 item 4)

Machine-checked gates pinned to the Wave-1 WILD instance's own density
`g_σ(q') := ∑_{T ∈ omMenuW n σ} omCount T q'` — the exact sum in the conclusion of
`RealInstanceW.montes_unconditional_w`.

* **G1W (FIRST WILD NON-VACUITY).** The totally ramified quadratic type
  `ramType2 = ⟨{(2,1)}⟩` (n = 2, e = 2, fSum = 1, canonical stratum
  `Tselfloop 2 ((0,1),(2,0)) [(1,1)]` — exactly `TameRealDensity`'s gate cell) has Wave-1
  menu-sum density EXACTLY `(p−1)·(p³)⁻¹` at every prime (`gate_w1_omCount_value`), hence
  `1/8` at `realP = 2` (`gate_w1_value`) — STRICTLY POSITIVE (`gate_w1_nonvacuous`). Under the
  V2 (order-0-only) menu this same type's value was `0` (`RealInstanceV2Gates.gate_v2_ramified_zero`):
  the Wave-1 menu genuinely de-vacuifies the wild leg. Instance pin: the genuine DECIDED-LIMIT
  density of `realMW` at `ramType2` is `1/8` (`gate_w1_countingDensity`, via `realDW`'s
  decomposition theorem — consumes the instance's `partition` + `stratum_tendsto_C` discharges).
* **G2W (WILD σ-SEPARATION).** (i) The ramified value `1/8` ≠ the inert unramified value `1/4`
  at `realP` (`gate_w2_ram_vs_inert`). (ii) At n = 4 the two DISTINCT constant-e ramified types
  `sigmaA = ⟨{(2,1),(2,1)}⟩` and `sigmaB = ⟨{(2,2)}⟩` (both e = 2, fSum = 2, same side
  `((0,2),(4,0))`, residual shapes `[(1,1),(1,1)]` vs `[(2,1)]`) get DISTINCT values at `realP`:
  `0` vs `1/256` (`gate_w2_wild_sigma_separation`). The `sigmaA` value is the blueprint §3
  HONEST-EMPTY pattern, machine-checked: two DISTINCT degree-1 residual factors demanded from a
  pool of size `p − 1 = 1` over `F₂` (`CellCard.shapeCount_split_two`) — the certified `0` is
  the genuine emptiness of the canonical stratum at `p = 2`, not a vacuous decode.
* **G4W (mutation evidence)** — see the comment block before the `AxCheck` section.

**Honest scope** (inherited from the capstone, blueprint §1): every wild value below is the
density of the CANONICAL MINIMAL-H stratum of its type — the leading term of the type's density,
NOT the H-tower sum; no exhaustiveness claim.

Leaf module: no existing file is modified. No axiom, no sorry. Footprints must be Lean core
ONLY (`AxCheck` section).
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false

namespace LeanUrat.OM.RealInstanceWGates

open scoped Classical
open LeanUrat LeanUrat.MontesAxiom Polynomial
open LeanUrat.OM
open LeanUrat.OM.CellMenu

/-! ## 0. The closed value of a canonical wild stratum -/

/-- **The closed engine value of a single-side all-μ=1 `Tselfloop` stratum**:
`shapeCount p shape · p^{−(newtonExponent + sideDeg)}` — the respell identity
`omCount_selfloop_eq_oneSideShape` composed with the banked closed form
`PathShape.omCount_oneSideShape_closed`. -/
theorem omCount_Tselfloop_closed (n H : ℕ) (shape : List (ℕ × ℕ))
    (hpos : ∀ q ∈ shape, 1 ≤ q.1) (hμ : ∀ q ∈ shape, q.2 = 1)
    (hdeg : (shape.map Prod.fst).sum = sideDeg (((0, H), (n, 0)) : (ℕ × ℕ) × (ℕ × ℕ)))
    (hne : shape ≠ []) (p : ℕ) [Fact p.Prime] :
    OMCountV2.omCount
        (ClassifierBridgeFiber.Tselfloop n (((0, H), (n, 0)) : (ℕ × ℕ) × (ℕ × ℕ)) shape) p
      = (CellCard.shapeCount p shape : ℚ)
          * ((p : ℚ) ^ (L4.newtonExponent (mkPoly n [((0 : ℕ), H), ((n : ℕ), (0 : ℕ))])
              + sideDeg (((0, H), (n, 0)) : (ℕ × ℕ) × (ℕ × ℕ))))⁻¹ := by
  rw [ClassifierBridgeFiber.omCount_selfloop_eq_oneSideShape n H shape hne p]
  exact PathShape.omCount_oneSideShape_closed n (((0, H), (n, 0)) : (ℕ × ℕ) × (ℕ × ℕ)) shape
    hpos hμ hdeg hne p

/-! ## 1. G1W — the first wild non-vacuity -/

/-- `fSum` of the totally ramified quadratic type `⟨{(2,1)}⟩` is `1`. -/
theorem fSum_ramType2 : WildMenu.fSum RealInstanceV2Gates.ramType2 = 1 := by decide

/-- The canonical residual shape of `⟨{(2,1)}⟩` is `[(1,1)]`. (`Multiset.sort` does not
kernel-reduce — merge sort is well-founded recursion — so the sort is discharged by
`sort_singleton`, not `decide`.) -/
theorem wShape_ramType2 :
    WildMenu.wShape RealInstanceV2Gates.ramType2 = [((1 : ℕ), (1 : ℕ))] := by
  rw [WildMenu.wShape,
    show RealInstanceV2Gates.ramType2.data.map Prod.snd = ({1} : Multiset ℕ) from rfl,
    Multiset.sort_singleton]
  rfl

/-- `⟨{(2,1)}⟩` IS constant-e ramified at degree 2 (e = 2, one f-part = 1, 2·1 = 2). -/
theorem constERam_ramType2 : WildMenu.constERam 2 RealInstanceV2Gates.ramType2 :=
  ⟨2, le_refl 2, by decide, by decide, by decide⟩

/-- **The Wave-1 wild menu of `⟨{(2,1)}⟩` is EXACTLY the canonical stratum singleton**
`{Tselfloop 2 ((0,1),(2,0)) [(1,1)]}` — the same shape as `TameRealDensity`'s gate cell.
(Contrast `RealInstanceV2Gates.omMenu_ramified_empty`: the order-0 menu of this type is ∅.) -/
theorem omMenuW_ramType2 :
    WildMenu.omMenuW 2 RealInstanceV2Gates.ramType2
      = {ClassifierBridgeFiber.Tselfloop 2 (((0, 1), (2, 0)) : (ℕ × ℕ) × (ℕ × ℕ))
          [((1 : ℕ), (1 : ℕ))]} := by
  rw [WildMenu.omMenuW_ram_of_constE constERam_ramType2, fSum_ramType2, wShape_ramType2]

/-- **The general-prime closed value of the G1W stratum**: `(p − 1)·(p³)⁻¹` — pool `p − 1`
(one degree-1 unit-constant residual factor, `shapeCount_one_one`), volume exponent
`newtonExponent (mkPoly 2 [(0,1),(2,0)]) + sideDeg = 2 + 1 = 3`. -/
theorem gate_w1_omCount_value (p : ℕ) [Fact p.Prime] :
    OMCountV2.omCount (ClassifierBridgeFiber.Tselfloop 2
        (((0, 1), (2, 0)) : (ℕ × ℕ) × (ℕ × ℕ)) [((1 : ℕ), (1 : ℕ))]) p
      = ((p : ℚ) - 1) * ((p : ℚ) ^ 3)⁻¹ := by
  rw [omCount_Tselfloop_closed 2 1 [((1 : ℕ), (1 : ℕ))]
      (by decide) (by decide) (by decide) (by decide) p]
  rw [CellCard.shapeCount_one_one]
  rw [show L4.newtonExponent (mkPoly 2 [((0 : ℕ), (1 : ℕ)), ((2 : ℕ), (0 : ℕ))])
      + sideDeg (((0, 1), (2, 0)) : (ℕ × ℕ) × (ℕ × ℕ)) = 3 from by decide]
  have hp2 : 2 ≤ p := (Fact.out (p := p.Prime)).two_le
  rw [Nat.cast_sub (by omega : 1 ≤ p), Nat.cast_one]

/-- **G1W, exact value.** The Wave-1 capstone's own menu-sum density at the totally ramified
quadratic type and the real prime is EXACTLY `1/8` — the FIRST machine-checked non-vacuous
WILD value in the capstone menu (the same type's order-0/V2 value is `0`,
`RealInstanceV2Gates.gate_v2_ramified_zero`). -/
theorem gate_w1_value :
    (∑ T ∈ WildMenu.omMenuW 2 RealInstanceV2Gates.ramType2, OMCountV2.omCount T M9.realP)
      = 1 / 8 := by
  rw [omMenuW_ramType2, Finset.sum_singleton, gate_w1_omCount_value M9.realP]
  norm_num [M9.realP]

/-- **G1W (first wild non-vacuity).** The Wave-1 menu-sum density is STRICTLY POSITIVE at a
concrete RAMIFIED type: the wild leg of `montes_unconditional_w` is not the vacuous `0`. -/
theorem gate_w1_nonvacuous :
    (0 : ℚ) < ∑ T ∈ WildMenu.omMenuW 2 RealInstanceV2Gates.ramType2,
        OMCountV2.omCount T M9.realP := by
  rw [gate_w1_value]
  norm_num

/-- **G1W, pinned to the REAL instance**: the genuine DECIDED-LIMIT density of the Wave-1
counting model `realMW` at the totally ramified quadratic type equals `1/8` — via `realDW`'s
decomposition theorem, so this consumes the instance's `partition` + `stratum_tendsto_C`
discharges (including the banked wild self-loop counting leg), not just the engine evaluator. -/
theorem gate_w1_countingDensity :
    (RealInstanceW.realMW 2 (by norm_num)).countingDensity RealInstanceV2Gates.ramType2
      = 1 / 8 := by
  rw [LeanUrat.MontesV2.MontesDataV2.countingDensity_eq_sum_coeff
    (RealInstanceW.realDW 2 (by norm_num))]
  exact gate_w1_value

/-! ## 2. G2W — wild σ-separation, ramified vs unramified -/

/-- The inert unramified Wave-1 value is the V2 value `1/4` (the inert type is NOT constant-e
ramified, so its Wave-1 menu IS the order-0 menu). -/
theorem gate_w2_inert_value :
    (∑ T ∈ WildMenu.omMenuW 2 (Order0.unramType 2 (Nat.Partition.indiscrete 2)),
        OMCountV2.omCount T M9.realP) = 1 / 4 := by
  have hmem : Order0.unramType 2 (Nat.Partition.indiscrete 2)
      ∈ RealInstanceV2Prep.unramTypeMenu 2 :=
    Finset.mem_image_of_mem _ (Finset.mem_univ _)
  rw [WildMenu.omMenuW_unram (WildMenuPrep.unramTypeMenu_not_constERam hmem)]
  exact RealInstanceV2Gates.gate_v2_value_inert2

/-- **G2W, ramified/unramified separation**: the totally ramified quadratic and the inert
quadratic are DISTINCT degree-2 types with DISTINCT Wave-1 values at the real prime
(`1/8` vs `1/4`) — σ-dependence is visible ACROSS the ramified/unramified split with both
values now non-vacuous. -/
theorem gate_w2_ram_vs_inert :
    RealInstanceV2Gates.ramType2 ≠ Order0.unramType 2 (Nat.Partition.indiscrete 2)
      ∧ (∑ T ∈ WildMenu.omMenuW 2 RealInstanceV2Gates.ramType2, OMCountV2.omCount T M9.realP)
        ≠ (∑ T ∈ WildMenu.omMenuW 2 (Order0.unramType 2 (Nat.Partition.indiscrete 2)),
            OMCountV2.omCount T M9.realP) := by
  constructor
  · intro h
    have hmem : ((2 : ℕ), (1 : ℕ))
        ∈ (Nat.Partition.indiscrete 2).parts.map (fun d => ((1 : ℕ), d)) := by
      rw [show (Nat.Partition.indiscrete 2).parts.map (fun d => ((1 : ℕ), d))
          = (Order0.unramType 2 (Nat.Partition.indiscrete 2)).data from rfl, ← h]
      simp [RealInstanceV2Gates.ramType2]
    rw [Multiset.mem_map] at hmem
    obtain ⟨d, -, hd⟩ := hmem
    exact absurd (congrArg Prod.fst hd) (by norm_num)
  · rw [gate_w1_value, gate_w2_inert_value]
    norm_num

/-! ## 3. G2W — wild σ-separation between two ramified types (n = 4), the honest-empty case -/

/-- The n = 4 constant-e type with SPLIT residual: `{(2,1),(2,1)}` (e = 2, two f-parts 1). -/
def sigmaA : FactorizationType := ⟨{(2, 1), (2, 1)}⟩

/-- The n = 4 constant-e type with INERT residual: `{(2,2)}` (e = 2, one f-part 2). -/
def sigmaB : FactorizationType := ⟨{(2, 2)}⟩

theorem constERam_sigmaA : WildMenu.constERam 4 sigmaA :=
  ⟨2, le_refl 2, by decide, by decide, by decide⟩

theorem constERam_sigmaB : WildMenu.constERam 4 sigmaB :=
  ⟨2, le_refl 2, by decide, by decide, by decide⟩

theorem fSum_sigmaA : WildMenu.fSum sigmaA = 2 := by decide

/-- Sorting the two-element multiset `{1, 1}` (via `sort_cons` + `sort_singleton`;
`Multiset.sort` does not kernel-reduce). -/
theorem sort_one_one : Multiset.sort ({1, 1} : Multiset ℕ) (· ≤ ·) = [1, 1] := by
  have h := Multiset.sort_cons (a := (1 : ℕ)) (s := ({1} : Multiset ℕ)) (r := (· ≤ ·))
    (fun b hb => by rw [Multiset.mem_singleton] at hb; omega)
  rw [show ({1, 1} : Multiset ℕ) = ((1 : ℕ) ::ₘ {1} : Multiset ℕ) from rfl, h,
    Multiset.sort_singleton]

theorem wShape_sigmaA :
    WildMenu.wShape sigmaA = [((1 : ℕ), (1 : ℕ)), ((1 : ℕ), (1 : ℕ))] := by
  rw [WildMenu.wShape, show sigmaA.data.map Prod.snd = ({1, 1} : Multiset ℕ) from rfl,
    sort_one_one]
  rfl

theorem fSum_sigmaB : WildMenu.fSum sigmaB = 2 := by decide

theorem wShape_sigmaB : WildMenu.wShape sigmaB = [((2 : ℕ), (1 : ℕ))] := by
  rw [WildMenu.wShape, show sigmaB.data.map Prod.snd = ({2} : Multiset ℕ) from rfl,
    Multiset.sort_singleton]
  rfl

/-- The Wave-1 menu of `sigmaA`: the canonical stratum on side `((0,2),(4,0))` with the SPLIT
residual shape `[(1,1),(1,1)]`. -/
theorem omMenuW_sigmaA :
    WildMenu.omMenuW 4 sigmaA
      = {ClassifierBridgeFiber.Tselfloop 4 (((0, 2), (4, 0)) : (ℕ × ℕ) × (ℕ × ℕ))
          [((1 : ℕ), (1 : ℕ)), ((1 : ℕ), (1 : ℕ))]} := by
  rw [WildMenu.omMenuW_ram_of_constE constERam_sigmaA, fSum_sigmaA, wShape_sigmaA]

/-- The Wave-1 menu of `sigmaB`: the canonical stratum on the SAME side with the INERT residual
shape `[(2,1)]`. -/
theorem omMenuW_sigmaB :
    WildMenu.omMenuW 4 sigmaB
      = {ClassifierBridgeFiber.Tselfloop 4 (((0, 2), (4, 0)) : (ℕ × ℕ) × (ℕ × ℕ))
          [((2 : ℕ), (1 : ℕ))]} := by
  rw [WildMenu.omMenuW_ram_of_constE constERam_sigmaB, fSum_sigmaB, wShape_sigmaB]

/-- **G2W, the HONEST-EMPTY value (blueprint §3), machine-checked.** The `sigmaA` Wave-1 value
at `realP = 2` is `0` — NOT a vacuous decode but the genuine emptiness of the canonical
stratum: its residual shape demands two DISTINCT degree-1 unit-constant factors from a pool of
size `p − 1 = 1` over `F₂` (`CellCard.shapeCount_split_two`). -/
theorem gate_w2_sigmaA_value :
    (∑ T ∈ WildMenu.omMenuW 4 sigmaA, OMCountV2.omCount T M9.realP) = 0 := by
  rw [omMenuW_sigmaA, Finset.sum_singleton]
  rw [omCount_Tselfloop_closed 4 2 [((1 : ℕ), (1 : ℕ)), ((1 : ℕ), (1 : ℕ))]
      (by decide) (by decide) (by decide) (by decide) M9.realP]
  -- `realP = 2` definitionally, and `Fact` instances are proof-irrelevant, so the literal-2
  -- count lemma coerces to the `realP` application:
  rw [show CellCard.shapeCount M9.realP [((1 : ℕ), (1 : ℕ)), ((1 : ℕ), (1 : ℕ))] = 0 from
    CellCard.shapeCount_split_two]
  norm_num

/-- **G2W, the inert-residual value.** The `sigmaB` Wave-1 value at `realP = 2` is `1/256`:
ONE monic irreducible quadratic over `F₂` (`card_irred_quad_two`), volume exponent
`newtonExponent (mkPoly 4 [(0,2),(4,0)]) + sideDeg = 6 + 2 = 8`. -/
theorem gate_w2_sigmaB_value :
    (∑ T ∈ WildMenu.omMenuW 4 sigmaB, OMCountV2.omCount T M9.realP) = 1 / 256 := by
  rw [omMenuW_sigmaB, Finset.sum_singleton]
  rw [omCount_Tselfloop_closed 4 2 [((2 : ℕ), (1 : ℕ))]
      (by decide) (by decide) (by decide) (by decide) M9.realP]
  have hsc : CellCard.shapeCount M9.realP [((2 : ℕ), (1 : ℕ))] = 1 := by
    have h2 : CellCard.shapeCount 2 [((2 : ℕ), (1 : ℕ))] = 1 := by
      rw [CellCard.shapeCount_irred_two, CellCard.card_irred_quad_two]
    exact h2
  rw [hsc]
  rw [show L4.newtonExponent (mkPoly 4 [((0 : ℕ), (2 : ℕ)), ((4 : ℕ), (0 : ℕ))])
      + sideDeg (((0, 2), (4, 0)) : (ℕ × ℕ) × (ℕ × ℕ)) = 8 from by decide]
  norm_num [M9.realP]

/-- **G2W (wild σ-separation between ramified types).** Two DISTINCT n = 4 constant-e ramified
types get DISTINCT Wave-1 values at the real prime (`0` vs `1/256`): the wild leg of the
certified density is genuinely σ-DEPENDENT, and the `0` side is the machine-checked
honest-empty pattern, not a decode artifact. -/
theorem gate_w2_wild_sigma_separation :
    sigmaA ≠ sigmaB
      ∧ (∑ T ∈ WildMenu.omMenuW 4 sigmaA, OMCountV2.omCount T M9.realP)
        ≠ (∑ T ∈ WildMenu.omMenuW 4 sigmaB, OMCountV2.omCount T M9.realP) := by
  constructor
  · intro h
    have hd : sigmaA.data = sigmaB.data := congrArg FactorizationType.data h
    exact absurd hd (by decide)
  · rw [gate_w2_sigmaA_value, gate_w2_sigmaB_value]
    norm_num

end LeanUrat.OM.RealInstanceWGates

/-! ## G4W — mutation evidence (blueprint §2 item 4)

A scratch copy of `realDW` with the per-shape coefficient mutated to the constant `0`
(`C := fun _ _ => 0`, all other fields verbatim, `stratum_tendsto_C` discharged by the same
`hNodeLimit_omMenuW`) FAILS to compile: the banked counting legs prove convergence to
`omCount T realP`, not to `0`, so the mutated field demands a limit the legs do not supply.
Verbatim compiler output (`lake env lean` on the scratch `OM/ScratchG4W.lean`, 2026-07-21;
scratch deleted after capture):

```
LeanUrat/OM/ScratchG4W.lean:19:37: error: Type mismatch
  RealInstanceW.hNodeLimit_omMenuW n hn σ T hT
has type
  Filter.Tendsto (fun N => M8.stratumCount (M9.rawCount n) T N / ↑M9.realP ^ (n * N)) Filter.atTop
    (nhds (OMCountV2.omCount T M9.realP))
but is expected to have type
  Filter.Tendsto (fun N => M8.stratumCount (M9.rawCount n) T N / ↑M9.realP ^ (n * N)) Filter.atTop (nhds 0)
```

The mutation gate certifies the instance's value tie is load-bearing, not decorative. -/

section AxCheck

-- Wave-1 W gates: every gate must be Lean core ONLY
-- (`propext, Classical.choice, Quot.sound` — fewer is fine, MORE is a stop-the-line event).
#print axioms LeanUrat.OM.RealInstanceWGates.omCount_Tselfloop_closed
#print axioms LeanUrat.OM.RealInstanceWGates.constERam_ramType2
#print axioms LeanUrat.OM.RealInstanceWGates.omMenuW_ramType2
#print axioms LeanUrat.OM.RealInstanceWGates.gate_w1_omCount_value
#print axioms LeanUrat.OM.RealInstanceWGates.gate_w1_value
#print axioms LeanUrat.OM.RealInstanceWGates.gate_w1_nonvacuous
#print axioms LeanUrat.OM.RealInstanceWGates.gate_w1_countingDensity
#print axioms LeanUrat.OM.RealInstanceWGates.gate_w2_inert_value
#print axioms LeanUrat.OM.RealInstanceWGates.gate_w2_ram_vs_inert
#print axioms LeanUrat.OM.RealInstanceWGates.gate_w2_sigmaA_value
#print axioms LeanUrat.OM.RealInstanceWGates.gate_w2_sigmaB_value
#print axioms LeanUrat.OM.RealInstanceWGates.gate_w2_wild_sigma_separation
-- The Wave-1 capstones, re-censused from the gate module (the instance the gates pin):
#print axioms LeanUrat.OM.RealInstanceW.montes_unconditional_w
#print axioms LeanUrat.OM.RealInstanceW.montes_unconditional_w_exhaustive

end AxCheck
