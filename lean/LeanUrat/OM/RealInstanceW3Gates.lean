/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.OM.RealInstanceW3
import LeanUrat.OM.RealInstanceWGates

/-!
# OM/RealInstanceW3Gates — the Wave-3 H-WINDOW gates (G1 window value, G2 strict growth)
(blueprint `notes/WILD_WAVE3_BLUEPRINT_2026-07-21.md` §2 item 3)

Machine-checked gates pinned to the window-K instance's own density
`g_σ(q') := ∑_{T ∈ omMenuW3 n K σ} omCount T q'` — the exact sum in the conclusion of
`RealInstanceW3.montes_unconditional_w3`.

* **G1 (window value).** At the totally ramified quadratic type `ramType2 = ⟨{(2,1)}⟩` (n = 2,
  e = 2, F = fSum = 1) with window `K = 3`: the admissible multipliers are
  `admissibleK 2 3 = {1, 3}` (`k ∈ {1,2,3}`, `gcd(k, 2) = 1` keeps `{1, 3}`), so the menu is
  the TWO-leg window `{ramShapeAt 2 σ 1, ramShapeAt 2 σ 3}` (`gate_w3_menu`) — heights
  `H = 1` and `H = 3`. Per-leg closed values at every prime: `H = 1` is Wave 1's
  `(p−1)·(p³)⁻¹` (`RealInstanceWGates.gate_w1_omCount_value`, = `1/8` at `realP = 2`); `H = 3`
  is `(p−1)·(p⁶)⁻¹` (`gate_w3_omCount_H3`, = `1/64` at `realP = 2` — blueprint §1 engine
  formula `(p−1)·p^{−(H+1+⌈H/2⌉)}` at `H = 3`). Window sum `1/8 + 1/64 = 9/64`
  (`gate_w3_value`; the EXTERNAL Python gate `verification/` pinned 1/8, 1/64, sum 9/64).
  Instance pin: the genuine DECIDED-LIMIT density of `realMW3` at `(n, K) = (2, 3)` is `9/64`
  (`gate_w3_countingDensity`, via `realDW3`'s decomposition theorem — consumes the instance's
  `partition` + `stratum_tendsto_C` discharges, including BOTH banked window counting legs).
* **G2 (strict window growth).** `value(K = 1) = 1/8 < 9/64 = value(K = 3)` at the SAME type
  and prime, both through the real instances (`gate_w3_growth`) — the deeper window certifies
  STRICTLY MORE of the type's density, machine-checked: the monotone-toward-the-tower
  narrative (`1/8 < 9/64 < 1/7 =` the tower wall value, which no window claims).
* **G4 (mutation evidence)** — see the comment block before the `AxCheck` section.

**Honest scope** (inherited from the capstone, blueprint §3): every window value below is the
K-TRUNCATED decided density of its type — a strictly larger leading sum than Wave 1, NOT the
full type density (the geometric tail = the recursive self-loop wall); no exhaustiveness claim.

Leaf module: no existing file is modified. No axiom, no sorry. Footprints must be Lean core
ONLY (`AxCheck` section).
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false

namespace LeanUrat.OM.RealInstanceW3Gates

open scoped Classical
open LeanUrat LeanUrat.MontesAxiom Polynomial
open LeanUrat.OM
open LeanUrat.OM.CellMenu

/-! ## 0. The K = 3 admissible window at e = 2 and the two window legs -/

/-- **The admissible multiplier window at `e = 2`, `K = 3` is `{1, 3}`**: of `k ∈ {1, 2, 3}`,
`gcd(k, 2) = 1` keeps `k = 1` and `k = 3` (blueprint §2 item 3: G1). -/
theorem admissibleK_two_three : WildMenuW3.admissibleK 2 3 = {1, 3} := by decide

/-- The `k = 1` window leg of `ramType2` is EXACTLY Wave 1's canonical stratum literal
(height `H = fSum · 1 = 1`). -/
theorem ramShapeAt_ramType2_one :
    WildMenuW3.ramShapeAt 2 RealInstanceV2Gates.ramType2 1
      = ClassifierBridgeFiber.Tselfloop 2 (((0, 1), (2, 0)) : (ℕ × ℕ) × (ℕ × ℕ))
          [((1 : ℕ), (1 : ℕ))] := by
  rw [WildMenuW3.ramShapeAt_one, RealInstanceWGates.fSum_ramType2,
    RealInstanceWGates.wShape_ramType2]

/-- The `k = 3` window leg of `ramType2`: the height-`3` self-loop stratum
(`H = fSum · 3 = 3`), SAME residual shape `[(1,1)]`. -/
theorem ramShapeAt_ramType2_three :
    WildMenuW3.ramShapeAt 2 RealInstanceV2Gates.ramType2 3
      = ClassifierBridgeFiber.Tselfloop 2 (((0, 3), (2, 0)) : (ℕ × ℕ) × (ℕ × ℕ))
          [((1 : ℕ), (1 : ℕ))] := by
  rw [WildMenuW3.ramShapeAt_def, RealInstanceWGates.fSum_ramType2,
    RealInstanceWGates.wShape_ramType2]

/-- **The window-3 menu of `ramType2` is EXACTLY the two-leg window**
`{ramShapeAt 2 σ 1, ramShapeAt 2 σ 3}` (contrast Wave 1's singleton `{ramShapeAt 2 σ 1}`,
`RealInstanceWGates.omMenuW_ramType2` + `WildMenuW3.omMenuW3_one`). -/
theorem gate_w3_menu :
    WildMenuW3.omMenuW3 2 3 RealInstanceV2Gates.ramType2
      = {WildMenuW3.ramShapeAt 2 RealInstanceV2Gates.ramType2 1,
         WildMenuW3.ramShapeAt 2 RealInstanceV2Gates.ramType2 3} := by
  rw [WildMenuW3.omMenuW3_ram_of_constE RealInstanceWGates.constERam_ramType2,
    RealInstanceWGates.fSum_ramType2,
    show ((2 : ℕ) / 1) = 2 from rfl, admissibleK_two_three,
    Finset.image_insert, Finset.image_singleton]

/-! ## 1. G1 — the per-leg closed values and the window value 9/64 -/

/-- **The general-prime closed value of the `H = 3` window leg**: `(p − 1)·(p⁶)⁻¹` — pool
`p − 1` (one degree-1 unit-constant residual factor, `shapeCount_one_one`), volume exponent
`newtonExponent (mkPoly 2 [(0,3),(2,0)]) + sideDeg = 5 + 1 = 6` (blueprint §1: `H+1+⌈H/2⌉ = 6`
at `H = 3`; the EXTERNAL Python gate pinned `(p−1)/p⁶` at `p ∈ {2,3}`). Mirrors
`RealInstanceWGates.gate_w1_omCount_value` (`H = 1`: exponent `3`). -/
theorem gate_w3_omCount_H3 (p : ℕ) [Fact p.Prime] :
    OMCountV2.omCount (ClassifierBridgeFiber.Tselfloop 2
        (((0, 3), (2, 0)) : (ℕ × ℕ) × (ℕ × ℕ)) [((1 : ℕ), (1 : ℕ))]) p
      = ((p : ℚ) - 1) * ((p : ℚ) ^ 6)⁻¹ := by
  rw [RealInstanceWGates.omCount_Tselfloop_closed 2 3 [((1 : ℕ), (1 : ℕ))]
      (by decide) (by decide) (by decide) (by decide) p]
  rw [CellCard.shapeCount_one_one]
  rw [show L4.newtonExponent (mkPoly 2 [((0 : ℕ), (3 : ℕ)), ((2 : ℕ), (0 : ℕ))])
      + sideDeg (((0, 3), (2, 0)) : (ℕ × ℕ) × (ℕ × ℕ)) = 6 from by decide]
  have hp2 : 2 ≤ p := (Fact.out (p := p.Prime)).two_le
  rw [Nat.cast_sub (by omega : 1 ≤ p), Nat.cast_one]

/-- The two window legs are DISTINCT shapes (disjoint fibers): heights `1 ≠ 3`, read back
through `ramShapeAt_injective_k`. -/
theorem ramShapeAt_ramType2_one_ne_three :
    WildMenuW3.ramShapeAt 2 RealInstanceV2Gates.ramType2 1
      ≠ WildMenuW3.ramShapeAt 2 RealInstanceV2Gates.ramType2 3 := by
  intro h
  exact absurd
    (WildMenuW3.ramShapeAt_injective_k RealInstanceWGates.constERam_ramType2 h)
    (by norm_num)

/-- **G1, exact window value.** The window-3 capstone's own menu-sum density at the totally
ramified quadratic type and the real prime is EXACTLY `9/64 = 1/8 + 1/64` (legs `H = 1` and
`H = 3`) — STRICTLY MORE than Wave 1's `1/8` (the `H = 1` leading term alone). The EXTERNAL
Python gate pinned all three values (1/8, 1/64, 9/64). -/
theorem gate_w3_value :
    (∑ T ∈ WildMenuW3.omMenuW3 2 3 RealInstanceV2Gates.ramType2,
        OMCountV2.omCount T M9.realP) = 9 / 64 := by
  rw [gate_w3_menu, Finset.sum_pair ramShapeAt_ramType2_one_ne_three,
    ramShapeAt_ramType2_one, ramShapeAt_ramType2_three,
    RealInstanceWGates.gate_w1_omCount_value M9.realP, gate_w3_omCount_H3 M9.realP]
  norm_num [M9.realP]

/-- **G1, pinned to the REAL instance**: the genuine DECIDED-LIMIT density of the window-3
counting model `realMW3` at the totally ramified quadratic type equals `9/64` — via `realDW3`'s
decomposition theorem, so this consumes the instance's `partition` + `stratum_tendsto_C`
discharges (including BOTH banked window counting legs `H = 1` and `H = 3`), not just the
engine evaluator. -/
theorem gate_w3_countingDensity :
    (RealInstanceW3.realMW3 2 3 (by norm_num)).countingDensity RealInstanceV2Gates.ramType2
      = 9 / 64 := by
  rw [LeanUrat.MontesV2.MontesDataV2.countingDensity_eq_sum_coeff
    (RealInstanceW3.realDW3 2 3 (by norm_num))]
  exact gate_w3_value

/-! ## 2. G2 — strict window growth -/

/-- The window-1 instance's decided-limit density at `ramType2` is Wave 1's `1/8` (the
recovery gate `montes_w3_one_recovers` composed with the Wave-1 value pin
`gate_w1_countingDensity`). -/
theorem gate_w3_one_countingDensity :
    (RealInstanceW3.realMW3 2 1 (by norm_num)).countingDensity RealInstanceV2Gates.ramType2
      = 1 / 8 := by
  have h := RealInstanceW3.montes_w3_one_recovers 2 (by norm_num) RealInstanceV2Gates.ramType2
  rw [h]
  exact RealInstanceWGates.gate_w1_countingDensity

/-- **G2 (strict window growth).** The deeper window certifies STRICTLY MORE of the type's
decided density, through the real instances: `value(K = 1) = 1/8 < 9/64 = value(K = 3)` at the
totally ramified quadratic type and the real prime — the machine-checked
monotone-toward-the-tower narrative (`1/8 < 9/64 < 1/7`, the tower wall value, which no finite
window claims). -/
theorem gate_w3_growth :
    (RealInstanceW3.realMW3 2 1 (by norm_num)).countingDensity RealInstanceV2Gates.ramType2
      < (RealInstanceW3.realMW3 2 3 (by norm_num)).countingDensity
          RealInstanceV2Gates.ramType2 := by
  rw [gate_w3_one_countingDensity, gate_w3_countingDensity]
  norm_num

end LeanUrat.OM.RealInstanceW3Gates

/-! ## G4 — mutation evidence (blueprint §2 item 3)

A scratch copy of `realDW3` with the per-shape coefficient mutated to the constant `0`
(`C := fun _ _ => 0`, all other fields verbatim, `stratum_tendsto_C` discharged by the same
`hNodeLimit_omMenuW3`) FAILS to compile: the banked counting legs prove convergence to
`omCount T realP`, not to `0`, so the mutated field demands a limit the legs do not supply.
Verbatim compiler output (`lake env lean` on the scratch `OM/ScratchG4W3.lean`, 2026-07-21;
scratch deleted after capture):

```
LeanUrat/OM/ScratchG4W3.lean:20:37: error: Type mismatch
  RealInstanceW3.hNodeLimit_omMenuW3 n K hn σ T hT
has type
  Filter.Tendsto (fun N => M8.stratumCount (M9.rawCount n) T N / ↑M9.realP ^ (n * N)) Filter.atTop
    (nhds (OMCountV2.omCount T M9.realP))
but is expected to have type
  Filter.Tendsto (fun N => M8.stratumCount (M9.rawCount n) T N / ↑M9.realP ^ (n * N)) Filter.atTop (nhds 0)
```

The mutation gate certifies the instance's value tie is load-bearing, not decorative. -/

section AxCheck

-- Wave-3 W gates: every gate must be Lean core ONLY
-- (`propext, Classical.choice, Quot.sound` — fewer is fine, MORE is a stop-the-line event).
#print axioms LeanUrat.OM.RealInstanceW3Gates.admissibleK_two_three
#print axioms LeanUrat.OM.RealInstanceW3Gates.ramShapeAt_ramType2_one
#print axioms LeanUrat.OM.RealInstanceW3Gates.ramShapeAt_ramType2_three
#print axioms LeanUrat.OM.RealInstanceW3Gates.gate_w3_menu
#print axioms LeanUrat.OM.RealInstanceW3Gates.gate_w3_omCount_H3
#print axioms LeanUrat.OM.RealInstanceW3Gates.ramShapeAt_ramType2_one_ne_three
#print axioms LeanUrat.OM.RealInstanceW3Gates.gate_w3_value
#print axioms LeanUrat.OM.RealInstanceW3Gates.gate_w3_countingDensity
#print axioms LeanUrat.OM.RealInstanceW3Gates.gate_w3_one_countingDensity
#print axioms LeanUrat.OM.RealInstanceW3Gates.gate_w3_growth
-- The Wave-3 capstones + recovery gate, re-censused from the gate module (the instance the
-- gates pin):
#print axioms LeanUrat.OM.RealInstanceW3.montes_unconditional_w3
#print axioms LeanUrat.OM.RealInstanceW3.montes_unconditional_w3_exhaustive
#print axioms LeanUrat.OM.RealInstanceW3.montes_w3_one_recovers

end AxCheck
