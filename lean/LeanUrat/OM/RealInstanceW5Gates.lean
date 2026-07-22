/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.OM.RealInstanceW5
import LeanUrat.OM.RealInstanceWGates

/-!
# OM/RealInstanceW5Gates — the Wave-5 DESCENT-CHAIN gates
(blueprint `notes/WILD_WAVE56_BLUEPRINT_2026-07-22.md` §2-W5b)

Machine-checked gates pinned to the Wave-5 instance's own density
`g_σ(q') := ∑_{T ∈ omMenu5 n D K σ} C5 T q'` — the exact sum in the conclusion of
`RealInstanceW5.montes_unconditional_w5`.

## G1 — the §7 Case-A ledger, ABSOLUTE (full-box) values at `p = 2`, through depth 2

The note's ledger is CLUSTER-CONDITIONAL (cluster box `p^{2N−2}`); the Lean chain masses are
FULL-BOX (`p^{2N}`), so ledger values pick up the one-time factor `p^{−2} = 1/4`
(the normalization resolution: `RecenterBox.massCond_descendStratum` vs
`mass_descendStratum`; the task card's "depth-1 descend-then-ram-H=1 = 1/16 absolute" is the
ledger's CLUSTER-CONDITIONAL 1/16 — the absolute value is `1/64`, the note's own Case C).

| chain (ms → leaf)      | ledger (cluster-cond)      | absolute = ledger/4 | gate |
|------------------------|----------------------------|---------------------|------|
| (1) → ram 1            | `(1/8)·(1/2) = 1/16` (Case C, `x²−12`) | `1/64`  | `gate_w5_ledger_caseC` |
| (1,1) → ram 1          | `(1/8)²·(1/2) = 1/128` (depth-2 row)   | `1/512` | `gate_w5_ledger_depth2` |
| (1) → ram 3            | `(1/8)·(1/16) = 1/128` (H=3 rung)      | `1/512` | `gate_w5_ledger_ram3` |
| (1) → inert 1          | `(1/8)·(1/8) = 1/64` (inert row)       | `1/256` | `gate_w5_ledger_inert` |
| (1) → split 1          | `(1/8)·(1/8) = 1/64` (two-sided row)   | `1/256` | `gate_w5_ledger_split` |

Depth-0 anchors (quoted, already Lean-certified in Waves 1/3): H=1 rung `1/8` absolute,
K=3 window `9/64` — reproduced here as the D=0 recovery value (`gate_w5_D0`).

`gate_w5_count_at_threshold` pins the COUNT itself (not just the coefficient): the depth-1
`(1) → ram 1` chain fiber has EXACTLY `4` points in the level-4 box (`4/2⁸ = 1/64`).

## G2 — depth-window growth

`gate_w5_window_growth`: at `(n, K) = (2, 1)` the ramified type's certified density GROWS
strictly from `D = 0` to `D = 1`: `1/8 < 1/8 + 1/64 = 9/64` — the depth window is
load-bearing, pinned through the REAL instances' `countingDensity` (so it consumes
`realDW5`'s `partition` + `stratum_tendsto_C` discharges, including the genuine `ChainCell`
fiber-count leg).

## G4 — mutation evidence: see the comment block before `AxCheck`.

Leaf module: no existing file is modified. No axiom, no sorry. Footprints must be Lean core
ONLY (`AxCheck`).
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false

namespace LeanUrat.OM.RealInstanceW5Gates

open LeanUrat LeanUrat.MontesAxiom Polynomial
open LeanUrat.OM
open LeanUrat.OM.CellMenu
open LeanUrat.OM.ChainMenu
open LeanUrat.OM.RealInstanceW5

/-! ## 0. Small facts about the gate data -/

theorem leafOK_ram1 : leafOK (ChainLeaf.ram 1) := ⟨⟨0, rfl⟩, le_refl 1⟩

theorem leafOK_ram3 : leafOK (ChainLeaf.ram 3) := ⟨⟨1, rfl⟩, by norm_num⟩

theorem ms1_window : ∀ m ∈ [1], 1 ≤ m := by
  intro m hm
  rw [List.mem_singleton] at hm
  omega

theorem ms11_window : ∀ m ∈ [1, 1], 1 ≤ m := by
  intro m hm
  rcases List.mem_cons.mp hm with rfl | hm'
  · exact le_refl 1
  · rw [List.mem_singleton] at hm'
    omega

/-! ## 1. G1 — the Case-A ledger values (chain coefficients at `p = 2`) -/

/-- **Case C (the note's `x² − 12` stratum)**: depth-1 descend at `m = 1` then the `H = 1`
ramified rung — cluster-conditional `(1/8)·(1/2) = 1/16`, ABSOLUTE `1/64`. -/
theorem gate_w5_ledger_caseC : chainC [1] (ChainLeaf.ram 1) 2 = 1 / 64 := by
  rw [chainC, eval_chainMult]
  norm_num [leafPoolQ, chainVolExp, eLeaf]

/-- **Depth-2 all-descend then `H = 1`**: ledger `(1/8)²·(1/2) = 1/128` cluster-conditional,
ABSOLUTE `1/512`. -/
theorem gate_w5_ledger_depth2 : chainC [1, 1] (ChainLeaf.ram 1) 2 = 1 / 512 := by
  rw [chainC, eval_chainMult]
  norm_num [leafPoolQ, chainVolExp, eLeaf]

/-- **Depth-1 then the `H = 3` rung**: ledger `(1/8)·(1/16) = 1/128` cluster-conditional,
ABSOLUTE `1/512`. -/
theorem gate_w5_ledger_ram3 : chainC [1] (ChainLeaf.ram 3) 2 = 1 / 512 := by
  rw [chainC, eval_chainMult]
  norm_num [leafPoolQ, chainVolExp, eLeaf]

/-- **Depth-1 then the inert leaf at `m = 1`** (pool `= (4−2)/2 = 1` at `p = 2`, the single
irreducible `y²+y+1`): ledger `(1/8)·(1/8) = 1/64` cluster-conditional, ABSOLUTE `1/256`. -/
theorem gate_w5_ledger_inert : chainC [1] (ChainLeaf.inert 1) 2 = 1 / 256 := by
  rw [chainC, eval_chainMult]
  norm_num [leafPoolQ, chainVolExp, eLeaf]

/-- **Depth-1 then the two-sided split leaf at `k = 1`**: ledger `(1/8)·(1/8) = 1/64`
cluster-conditional, ABSOLUTE `1/256`. -/
theorem gate_w5_ledger_split : chainC [1] (ChainLeaf.split 1) 2 = 1 / 256 := by
  rw [chainC, eval_chainMult]
  norm_num [leafPoolQ, chainVolExp, eLeaf]

/-- The inert pool at `p = 2` is the SINGLETON `{(1, 1)}` (`y² + y + 1`), pool count `1` —
the ledger's "inert at q=2" (and the split-residual pool `(q−1)(q−2)/2 = 0` is honest-empty,
which is why the even-height separable row is inert-only at `p = 2`). -/
theorem gate_w5_inert_pool : (noRootPairs 2).card = 1 := by
  have h := two_mul_card_noRootPairs 2
  omega

/-- **The COUNT gate at the threshold**: the depth-1 `(1) → ram 1` chain stratum has EXACTLY
`4` points in the level-`4` box of `2^8 = 256` monic quadratics — mass `1/64`, the Case-C
absolute value, as a genuine `Nat.card` (this consumes `card_chainCell` ←
`stratumPairEquiv`, the W5a staircase bijection). -/
theorem gate_w5_count_at_threshold :
    stratumCount5 2 (chainLit [1] (ChainLeaf.ram 1)) 4 = 4 := by
  rw [stratumCount5_chainLit,
    card_chainCell M9.realP [1] (ChainLeaf.ram 1) ms1_window leafOK_ram1
      (by norm_num [leafNeed] : 2 * ([1] : List ℕ).sum + leafNeed (ChainLeaf.ram 1) ≤ 4)]
  norm_num [leafCount, M9.realP]

/-! ## 2. The explicit gate menus at `(n, D, K) = (2, D, 1)`, σ = ramified -/

theorem fSum_ramType2 : WildMenu.fSum ramType2 = 1 := by decide

theorem wShape_ramType2 : WildMenu.wShape ramType2 = [((1 : ℕ), (1 : ℕ))] := by
  rw [WildMenu.wShape, show ramType2.data.map Prod.snd = ({1} : Multiset ℕ) from rfl,
    Multiset.sort_singleton]
  rfl

/-- The W4 (= W3) part of the gate menu: the single `k = 1` window leg. -/
theorem gate_w5_menu_old :
    MultiSlopeMenu.omMenu4 2 1 ramType2 = {WildMenuW3.ramShapeAt 2 ramType2 1} := by
  rw [MultiSlopeMenu.omMenu4_eq_of_not_mixed (not_mixedOK_two ramType2),
    WildMenuW3.omMenuW3_ram_of_constE constERam_ramType2, fSum_ramType2]
  rw [show (2 : ℕ) / 1 = 2 from rfl, WildMenuW3.admissibleK_one, Finset.image_singleton]

/-- The chain part of the gate menu at `D = K = 1`: the single depth-1 Case-C chain. -/
theorem gate_w5_menu_chains :
    chainShapes 2 1 1 ramType2 = {chainLit [1] (ChainLeaf.ram 1)} := by
  have hms : (msMenu 1 1).filter (fun ms => ms ≠ []) = {[1]} := by
    ext ms
    rw [Finset.mem_filter, mem_msMenu, Finset.mem_singleton]
    constructor
    · rintro ⟨⟨hlen, hall⟩, hne⟩
      cases ms with
      | nil => exact absurd rfl hne
      | cons m tl =>
          cases tl with
          | nil =>
              have := (hall m List.mem_cons_self)
              have hm1 : m = 1 := by omega
              rw [hm1]
          | cons m' tl' => simp at hlen
    · rintro rfl
      refine ⟨⟨by norm_num, fun m hm => ?_⟩, by simp⟩
      rw [List.mem_singleton] at hm
      omega
  have hleaves : chainLeaves 1 ramType2 = {ChainLeaf.ram 1} := by
    rw [chainLeaves, if_pos rfl, Finset.Icc_self, Finset.image_singleton]
  rw [chainShapes, if_pos rfl, hms, hleaves, Finset.singleton_product_singleton,
    Finset.image_singleton]

/-- The full `D = 1` gate menu: the W1 rung PLUS the Case-C chain. -/
theorem gate_w5_menu :
    omMenu5 2 1 1 ramType2
      = {WildMenuW3.ramShapeAt 2 ramType2 1, chainLit [1] (ChainLeaf.ram 1)} := by
  rw [omMenu5, gate_w5_menu_old, gate_w5_menu_chains]
  rfl

/-! ## 3. The certified density values through the REAL instances -/

/-- The W1 rung's engine value at every prime: `(p−1)·p⁻³` (`= 1/8` at `p = 2` — the
Lean-certified Wave-1 anchor, reproduced through the Wave-5 coefficient). -/
theorem gate_w5_rung_value (p : ℕ) [Fact p.Prime] :
    OMCountV2.omCount (ClassifierBridgeFiber.Tselfloop 2
        (((0, 1), (2, 0)) : (ℕ × ℕ) × (ℕ × ℕ)) [((1 : ℕ), (1 : ℕ))]) p
      = ((p : ℚ) - 1) * ((p : ℚ) ^ 3)⁻¹ := by
  rw [RealInstanceWGates.omCount_Tselfloop_closed 2 1 [((1 : ℕ), (1 : ℕ))]
      (by decide) (by decide) (by decide) (by decide) p]
  rw [CellCard.shapeCount_one_one]
  rw [show L4.newtonExponent (mkPoly 2 [((0 : ℕ), (1 : ℕ)), ((2 : ℕ), (0 : ℕ))])
      + sideDeg (((0, 1), (2, 0)) : (ℕ × ℕ) × (ℕ × ℕ)) = 3 from by decide]
  have hp2 : 2 ≤ p := (Fact.out (p := p.Prime)).two_le
  rw [Nat.cast_sub (by omega : 1 ≤ p), Nat.cast_one]

/-- `C5` on the W1 rung is its `omCount` (`= 1/8` at the real prime). -/
theorem gate_w5_C5_rung :
    C5 (WildMenuW3.ramShapeAt 2 ramType2 1) M9.realP = 1 / 8 := by
  have h0 : MultiSlopeMenu.headOrd (WildMenuW3.ramShapeAt 2 ramType2 1) = 0 := rfl
  rw [C5_of_headOrd_ne (by rw [h0]; omega),
    MultiSlopeMenu.C4_of_headOrd_ne (by rw [h0]; omega)]
  rw [WildMenuW3.ramShapeAt_one, fSum_ramType2, wShape_ramType2]
  rw [gate_w5_rung_value M9.realP]
  norm_num [M9.realP]

/-- **`D = 0` recovery value**: the Wave-5 instance at depth window `0` certifies the Wave-1/3
anchor `1/8` for the ramified type at `(n, K) = (2, 1)`. -/
theorem gate_w5_D0 :
    (realMW5 2 0 1 (by norm_num)).countingDensity ramType2 = 1 / 8 := by
  rw [LeanUrat.MontesV2.MontesDataV2.countingDensity_eq_sum_coeff
    (realDW5 2 0 1 (by norm_num))]
  show (∑ T ∈ omMenu5 2 0 1 ramType2, C5 T M9.realP) = 1 / 8
  rw [omMenu5_zero, gate_w5_menu_old, Finset.sum_singleton, gate_w5_C5_rung]

/-- **`D = 1` value**: the Wave-5 instance at depth window `1` certifies
`1/8 + 1/64 = 9/64` — the W1 rung PLUS the first genuine depth-1 descent-chain mass (the
note's Case C), through the REAL instance's decided limit. -/
theorem gate_w5_D1 :
    (realMW5 2 1 1 (by norm_num)).countingDensity ramType2 = 9 / 64 := by
  rw [LeanUrat.MontesV2.MontesDataV2.countingDensity_eq_sum_coeff
    (realDW5 2 1 1 (by norm_num))]
  show (∑ T ∈ omMenu5 2 1 1 ramType2, C5 T M9.realP) = 9 / 64
  rw [gate_w5_menu]
  have hne : WildMenuW3.ramShapeAt 2 ramType2 1 ≠ chainLit [1] (ChainLeaf.ram 1) := by
    intro hc
    have h0 : MultiSlopeMenu.headOrd (WildMenuW3.ramShapeAt 2 ramType2 1) = 0 := rfl
    have h2 : MultiSlopeMenu.headOrd (chainLit [1] (ChainLeaf.ram 1)) = 2 :=
      headOrd_chainLit _ _
    rw [hc, h2] at h0
    exact absurd h0 (by norm_num)
  rw [Finset.sum_insert (by rwa [Finset.mem_singleton]), Finset.sum_singleton]
  rw [gate_w5_C5_rung, C5_chainLit]
  rw [show chainC [1] (ChainLeaf.ram 1) M9.realP = chainC [1] (ChainLeaf.ram 1) 2 from rfl,
    gate_w5_ledger_caseC]
  norm_num

/-- **G2 (depth-window growth).** The ramified type's certified density STRICTLY GROWS with
the depth window: `value(D=1) = 9/64 > 1/8 = value(D=0)` — the chain stratum adds genuine
decided mass; the depth window is load-bearing. -/
theorem gate_w5_window_growth :
    (realMW5 2 0 1 (by norm_num)).countingDensity ramType2
      < (realMW5 2 1 1 (by norm_num)).countingDensity ramType2 := by
  rw [gate_w5_D0, gate_w5_D1]
  norm_num

end LeanUrat.OM.RealInstanceW5Gates

/-! ## G4 — mutation evidence (blueprint §2-W5b)

A scratch copy of `realDW5` with the per-shape coefficient mutated to the constant `0`
(`C := fun _ _ => 0`, all other fields verbatim, `stratum_tendsto_C` discharged by the same
`hNodeLimit_omMenu5`) FAILS to compile: the banked counting legs prove convergence to
`C5 T realP` (on the chain legs, the genuine `ChainCell` fiber-count staircase limit), not to
`0`. Verbatim compiler output (`lake env lean` on the scratch `OM/ScratchG4W5.lean`,
2026-07-22; scratch deleted after capture):

```
LeanUrat/OM/ScratchG4W5.lean:17:37: error: Type mismatch
  hNodeLimit_omMenu5 n D K hn σ T hT
has type
  Filter.Tendsto (fun N => stratumCount5 n T N / ↑M9.realP ^ (n * N)) Filter.atTop (nhds (C5 T M9.realP))
but is expected to have type
  Filter.Tendsto (fun N => stratumCount5 n T N / ↑M9.realP ^ (n * N)) Filter.atTop (nhds 0)
```

The mutation gate certifies the instance's value tie is load-bearing, not decorative. -/

section AxCheck

-- Wave-5 gates: every gate must be Lean core ONLY
-- (`propext, Classical.choice, Quot.sound` — fewer is fine, MORE is a stop-the-line event).
#print axioms LeanUrat.OM.RealInstanceW5Gates.gate_w5_ledger_caseC
#print axioms LeanUrat.OM.RealInstanceW5Gates.gate_w5_ledger_depth2
#print axioms LeanUrat.OM.RealInstanceW5Gates.gate_w5_ledger_ram3
#print axioms LeanUrat.OM.RealInstanceW5Gates.gate_w5_ledger_inert
#print axioms LeanUrat.OM.RealInstanceW5Gates.gate_w5_ledger_split
#print axioms LeanUrat.OM.RealInstanceW5Gates.gate_w5_inert_pool
#print axioms LeanUrat.OM.RealInstanceW5Gates.gate_w5_count_at_threshold
#print axioms LeanUrat.OM.RealInstanceW5Gates.gate_w5_menu_old
#print axioms LeanUrat.OM.RealInstanceW5Gates.gate_w5_menu_chains
#print axioms LeanUrat.OM.RealInstanceW5Gates.gate_w5_menu
#print axioms LeanUrat.OM.RealInstanceW5Gates.gate_w5_rung_value
#print axioms LeanUrat.OM.RealInstanceW5Gates.gate_w5_C5_rung
#print axioms LeanUrat.OM.RealInstanceW5Gates.gate_w5_D0
#print axioms LeanUrat.OM.RealInstanceW5Gates.gate_w5_D1
#print axioms LeanUrat.OM.RealInstanceW5Gates.gate_w5_window_growth
-- The Wave-5 capstones + recovery gate, re-censused from the gate module (the instance the
-- gates pin):
#print axioms LeanUrat.OM.RealInstanceW5.montes_unconditional_w5
#print axioms LeanUrat.OM.RealInstanceW5.montes_unconditional_w5_exhaustive
#print axioms LeanUrat.OM.RealInstanceW5.montes_w5_recovers

end AxCheck
