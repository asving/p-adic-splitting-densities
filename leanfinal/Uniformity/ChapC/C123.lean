/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapC.C52
import Uniformity.ChapC.C53c
import Uniformity.ChapC.C80

/-!
# Uniformity.ChapC.C123 — the `q = 2` gate (HONEST PARTIAL)

**Chapter C, NODE C.123** [gate] [fresh] (`blueprint/CHAP-C_tower_grammar.md` §13; signature
[signed: A-C.1 — the D14 cure]: machine-form expected-value tables in
`leanspec/Leanspec/ChapC.lean`'s gate-hygiene block).  **ENV-C3**, concrete `O`-instances
(the leancheck `ℤ₂`-idiom).

## Disposition — HONEST PARTIAL

This gate file fires ONLY the rows whose objects are LANDED in `leanfinal` today; every
other row of the blueprint's list is explicitly deferred below with its named missing
object.  The signed expected-value TABLES are transcribed BYTE-FROZEN from the leanspec
gate-hygiene block (leanfinal cannot import leanspec), together with the numeric mirrors
`budgetFloorN` / `htSpot` they are `#guard`-diffed through; the D22 discriminating third
frame `(e₁, e₂, E₂) = (2, 1, 10)` is included, per the signature's mandate that every
budget-table gate row set carry it.

## Fired vs deferred (the blueprint row list, in order)

| row | status |
| --- | ------ |
| S2 tower witness values (`u₂ = 5, u₃ = 21`, ladder `[4,10,21]`, `n̂₂(21) = 16Φ′`) | **FIRED** — C.97's `s2Witness`/`s2Witness_values`/`towerSolve` |
| budget-table rows (C.52's floors — sixteen recomputed entries) | **FIRED** — `budgetFloor` (C.52) recomputed at the two LANDED towers, C.80's `s2Tower` `(2,1,5)` and C.53c's `linTower` `(2,1,3)`: 4 pins × 2 offsets × 2 towers = 16 entries, each diffed against the transcribed mirror; plus the signed-table `#guard`s at the leanspec gate frames |
| node floors `[21,11]/[29,15]/[13,7]` | ROW DEFERRED: the generating NODE-EQ anchor frames are C.54's (no `C54.lean`); the leanspec table itself carries no `#guard` derivation, so there is nothing landed to diff |
| `E₂`-vs-`dv₂(x^{D₂})` splits `10/14/6 > 8/8/4` | **FIRED** — the table guard (pure arithmetic) + C.50's landed `E₂_gt_xfloor` instantiated at `s2Tower` (`10 > 8`) and `linTower` (`6 > 4`); the middle entry `(14, 8)` fires arithmetic-only (its FAM-A7 frame is not landed) |
| refine row A5-R1 (`p₀ = 2λ = 26`, the `q = 2` vanishing of the `j = 1` pin) | ROW DEFERRED: the C.56/C.57 refine-row carrier is not landed (no `C56.lean`/`C57.lean`; `C56a` is the K₂-digit lift, not the refine row) |
| FAM-B BAND-2/3 window rows | ROW DEFERRED: C.72's `shadow_faithful_band` is OPEN (statement carrier only; the BAND rows are explicitly OWED in `C72.lean`) |
| the `(1,2)`-genre bite (`EFF.HE6.20`(3): live at `q = 2`, σ `{(2,2),(2,2)}`) | ROW DEFERRED: the σ-genre member carrier C.119/C.120/C.122 is not landed (no such files) |
| FR5X (the C.96 negative control: attainment FAILS at `m = 4, p = 2`) | ROW DEFERRED: C.96 is not landed (no `C96.lean`) |
| HT spot values at `q = 2` (`(q−1)((q−1)(q−2)/2)q^{2N−8}` = 0 — the degenerate census) | **FIRED** — the transcribed `htSpot` mirror, as a ∀-`N` theorem plus the signed `N < 12` guard; the landed formula carrier is C.115's `ht_obstruction_instance` (tree-level instantiation stays behind C.114's BLOCK and is NOT claimed) |
| depth-3 `(SLOT₃)` spot value on the S4 chain (`n̂₃(85) = 2⁸Φ₂`) | **FIRED** — `s2Witness.towerNorm 2 85 = (8, 0, ![0, 1])` (i.e. `π⁸·x⁰·Φ′⁰·Φ₂¹` at `π = 2`) + the rung solves `towerSolve 21 2 85 = 1`, `towerSolve 85 2 341 = 1` on C.93's chain `u = 5, 21, 85, 341` |

**DEPENDS.** C.52 (`budgetFloor`) · C.50 (`E₂_gt_xfloor`, via C.52) · C.53c (`linTower`) ·
C.80 (`s2Tower`) · C.97 (`s2Witness`, via C.80) · C.83 (`towerSolve`/`towerNorm`, via C.97).

## Status

Sorry-free, axiom-free (Lean core only; AxCheck footer).
-/

set_option linter.style.longLine false

namespace Uniformity.Density.Tower.C123

open Uniformity.Density.Tower Uniformity.Density.Tower.C80
open IsLocalRing

/-! ## 1. The signed expected-value tables and their numeric mirrors
(BYTE-FROZEN transcription from `leanspec/Leanspec/ChapC.lean`'s A-C.1 gate-hygiene block —
leanfinal cannot import leanspec, so the gate diffs against the transcribed tables). -/

/-- leanspec's numeric budget-floor mirror (C.52's display
`⌈((μ₂−j)E₂ − w)/(e₁e₂)⌉ + [pin]`), transcribed byte-frozen. -/
def budgetFloorN (e₁ e₂ E₂ μ₂ j w : ℕ) : ℕ :=
  let tgt := μ₂ * E₂ - j * E₂ - w
  let d := e₁ * e₂
  if (μ₂ - j) * E₂ < w then 0
  else (tgt + d - 1) / d + (if tgt % d == 0 then 1 else 0)

/-- the HT spot-value family (the D15-decided FULL-coefficient reading), transcribed. -/
def htSpot (q N : ℕ) : ℕ := (q - 1) * ((q - 1) * (q - 2) / 2) * q ^ (2 * N - 8)

/-- the DEAD factor-`(q−1)`-smaller reading, kept as the negative control (D15). -/
def htSpotAlt (q N : ℕ) : ℕ := ((q - 1) * (q - 2) / 2) * q ^ (2 * N - 8)

/-- C.123's machine-form expected values (`q = 2`), transcribed. -/
def gateC_q2_budget_w0 : List ℕ := [7, 5, 3, 1]
def gateC_q2_budget_w5 : List ℕ := [5, 3, 1, 0]
/-- ROW DEFERRED: the table is transcribed (signature obligation), but its generating
NODE-EQ anchor frames are C.54's, not landed (no `C54.lean`) — no diff is possible today. -/
def gateC_q2_nodeFloors : List (List ℕ) := [[21, 11], [29, 15], [13, 7]]
def gateC_q2_E2_splits : List (ℕ × ℕ) := [(10, 8), (14, 8), (6, 4)]
def gateC_q2_s2Ladder : List ℕ := [4, 10, 21]
def gateC_q2_htSpot : ℕ := 0    -- the degenerate census at q = 2, every N

/-- the D22 cure: the discriminating third frame's `w = 0` row, transcribed. -/
def gateC_frame3_budget_w0 : List ℕ := [16, 11, 6, 1]

/-! ### The signed `#guard` diffs (the leanspec gate-hygiene block, executed here) -/

#guard (List.range 4).map (fun j => budgetFloorN 2 2 8 3 j 0) == gateC_q2_budget_w0
#guard (List.range 4).map (fun j => budgetFloorN 2 2 8 3 j 5) == gateC_q2_budget_w5
#guard gateC_q2_E2_splits.all (fun p => p.2 < p.1)
#guard (List.range 12).all (fun N => htSpot 2 N == gateC_q2_htSpot)
#guard (List.range 12).all (fun N => htSpotAlt 2 N == gateC_q2_htSpot)
#guard (List.range 4).map (fun j => budgetFloorN 2 1 10 3 j 0) == gateC_frame3_budget_w0
#guard gateC_frame3_budget_w0 ≠ gateC_q2_budget_w0

/-! ## 2. The HT spot row at `q = 2` — the degenerate census, as a ∀-`N` theorem
(strictly stronger than the signed `N < 12` guard above).  The landed FORMULA carrier is
C.115's `ht_obstruction_instance`; the spot VALUE row is this gate's, per C.115's own
docstring.  Tree-level instantiation (concrete polygon data realizing the budgets) inherits
C.114's BLOCK and is not claimed. -/

/-- **the `q = 2` HT spot row**: the D15-decided count `(q−1)·((q−1)(q−2)/2)·q^{2N−8}`
vanishes identically at `q = 2` — the degenerate census, itself a check. -/
theorem htSpot_q2 (N : ℕ) : htSpot 2 N = 0 := by
  simp [htSpot]

/-- the negative-control reading also vanishes at `q = 2` (both readings are blind here;
the `q = 3` row is the deciding witness — C.124's business, not this gate's). -/
theorem htSpotAlt_q2 (N : ℕ) : htSpotAlt 2 N = 0 := by
  simp [htSpotAlt]

/-! ## 3. The S4-chain rung solves (`towerSolve`, C.83) — the `(SLOT₃)` row's arithmetic
legs on C.93's chain `u = 5, 21, 85, 341`. -/

example : towerSolve 5 2 21 = 1 := by decide
example : towerSolve 21 2 85 = 1 := by decide
example : towerSolve 85 2 341 = 1 := by decide

/-! ## 4. The budget-table rows — sixteen entries RECOMPUTED at the two LANDED towers
(C.52's `budgetFloor`, fired at C.80's `s2Tower` `(e₂,f₂,u₂) = (2,1,5)` over `s2Frame`
(`e₁ = 2`, so `d = e₁e₂ = 4`, `E₂ = 10`) and C.53c's `linTower` `(2,1,3)` over `linFrame`
(`e₁ = 1`, so `d = 2`, `E₂ = 6`); 4 pins `j < 4` × 2 slot offsets `w ∈ {0, 5}` × 2 towers
= 16 entries).  Each row is diffed against the transcribed numeric mirror `budgetFloorN`
at the same numerals by the `#guard`s that follow — landed `budgetFloor` = numerals =
mirror.  NOTE the leanspec gate frames `(2,2,8)`/`(2,1,10)` themselves have no landed
`TowerDatum` today; their rows fire mirror-only in §1 above. -/

section TowerRows

open Uniformity.Density.Tower.C53c

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)] {π : O}

/-- **the `s2Tower` budget rows** (`μ₂ = 3`): slot `(a,b) = (0,0)` has offset `w = 0` and row
`[8, 6, 3, 1]`; slot `(0,1)` has offset `w = 5` (`= u₂`) and row `[7, 4, 2, 0]`. -/
theorem s2Tower_budget_rows (h2 : Irreducible (2 : O)) (hq : residueCard O = 2) :
    slotOffset (s2Tower h2 hq) 0 0 = 0 ∧
      (List.range 4).map (fun j => budgetFloor (s2Tower h2 hq) 3 j 0 0) = [8, 6, 3, 1] ∧
      slotOffset (s2Tower h2 hq) 0 1 = 5 ∧
      (List.range 4).map (fun j => budgetFloor (s2Tower h2 hq) 3 j 0 1) = [7, 4, 2, 0] := by
  have hE : (s2Tower h2 hq).E₂ = 10 := rfl
  have he₂ : (s2Tower h2 hq).e₂ = 2 := rfl
  have hu₂ : (s2Tower h2 hq).u₂ = 5 := rfl
  have he₁ : (s2Frame h2 hq).e₁ = 2 := rfl
  have hh : (s2Frame h2 hq).h = 1 := rfl
  refine ⟨rfl, ?_, rfl, ?_⟩ <;>
    · simp only [budgetFloor, slotOffset, hE, he₂, hu₂, he₁, hh]
      decide

omit [Finite (ResidueField O)] in
/-- **the `linTower` budget rows** (`μ₂ = 3`): slot `(0,0)` has offset `w = 0` and row
`[10, 7, 4, 1]`; slot `(1,1)` has offset `w = 5` (`= e₂h + u₂ = 2 + 3`) and row
`[7, 4, 1, 0]`. -/
theorem linTower_budget_rows (hπ : Irreducible π) :
    slotOffset (linTower hπ) 0 0 = 0 ∧
      (List.range 4).map (fun j => budgetFloor (linTower hπ) 3 j 0 0) = [10, 7, 4, 1] ∧
      slotOffset (linTower hπ) 1 1 = 5 ∧
      (List.range 4).map (fun j => budgetFloor (linTower hπ) 3 j 1 1) = [7, 4, 1, 0] := by
  have hE : (linTower hπ).E₂ = 6 := rfl
  have he₂ : (linTower hπ).e₂ = 2 := rfl
  have hu₂ : (linTower hπ).u₂ = 3 := rfl
  have he₁ : (linFrame hπ).e₁ = 1 := rfl
  have hh : (linFrame hπ).h = 1 := rfl
  refine ⟨rfl, ?_, rfl, ?_⟩ <;>
    · simp only [budgetFloor, slotOffset, hE, he₂, hu₂, he₁, hh]
      decide

/-! ### 5. The `E₂`-vs-`dv₂(x^{D₂})` split at the landed towers
C.50's landed `E₂_gt_xfloor` (`T.D₂·(e₂h) < T.E₂`), instantiated: `s2Tower` gives
`8 < 10` and `linTower` gives `4 < 6` — the first and third entries of
`gateC_q2_E2_splits`.  The middle entry `(14, 8)` has no landed frame (FAM-A7) and fires
arithmetic-only through the §1 table guard. -/

/-- `10 > 8` at `s2Tower`: `dv₂(x^{D₂}) = D₂·e₂h = 4·2·1 = 8 < 10 = E₂`. -/
theorem E₂_split_s2 (h2 : Irreducible (2 : O)) (hq : residueCard O = 2) : (8 : ℕ) < 10 :=
  E₂_gt_xfloor (s2Tower h2 hq)

omit [Finite (ResidueField O)] in
/-- `6 > 4` at `linTower`: `dv₂(x^{D₂}) = D₂·e₂h = 2·2·1 = 4 < 6 = E₂`. -/
theorem E₂_split_lin (hπ : Irreducible π) : (4 : ℕ) < 6 :=
  E₂_gt_xfloor (linTower hπ)

/-! ### 6. The S2 tower witness row (C.97's landed objects) and the `(SLOT₃)` row -/

/-- **the S2 witness row**: `u₂ = 5`, `u₃ = 21`, and the normalizer read `n̂₂(21) = 16Φ′`
(exponent form `towerNorm 1 21 = (4, 0, ![1])`, i.e. `2⁴·x⁰·Φ′¹`) — all CONSUMED from
C.97's landed `s2Witness_values`, not re-proved. -/
theorem s2_witness_row (h2 : Irreducible (2 : O)) (hq : residueCard O = 2)
    (H₀ : ℕ) (hpin : (s2Frame h2 hq).Pin H₀) :
    (s2Witness h2 hq H₀ hpin).u 2 = 5 ∧ (s2Witness h2 hq H₀ hpin).u 3 = 21 ∧
      (s2Witness h2 hq H₀ hpin).towerNorm 1 21 = (4, 0, fun _ => 1) :=
  ⟨(s2Witness_values h2 hq H₀ hpin).2.2.1, (s2Witness_values h2 hq H₀ hpin).2.2.2.2.2.1,
    (s2Witness_values h2 hq H₀ hpin).2.2.2.2.2.2⟩

/-- **the ladder row, diffed against THE TABLE**: the witness's own bookkeeping
`[ê₂, E₂, u₃] = [4, 10, 21] = gateC_q2_s2Ladder`. -/
theorem s2_ladder_row (h2 : Irreducible (2 : O)) (hq : residueCard O = 2)
    (H₀ : ℕ) (hpin : (s2Frame h2 hq).Pin H₀) :
    [(s2Witness h2 hq H₀ hpin).ehat 2, (s2Witness h2 hq H₀ hpin).Econst 2,
      (s2Witness h2 hq H₀ hpin).u 3] = gateC_q2_s2Ladder := by
  have h4 : (s2Witness h2 hq H₀ hpin).ehat 2 = 4 := by
    change ∏ _j ∈ Finset.Icc 1 2, (2 : ℕ) = 4
    decide
  simp only [h4]
  rfl

/-- **the depth-3 `(SLOT₃)` spot value on the S4 chain** (C.88's owed gate row):
`n̂₃(85) = 2⁸Φ₂`, in exponent form `towerNorm 2 85 = (8, 0, ![0, 1])` — `π⁸·x⁰·Φ′⁰·Φ₂¹`
at `π = 2`.  The rung ledger: `towerSolve 21 2 85 = 1` (`b₂ = 1`), carried remainder
`(85 − 21)/2 = 32`; `towerSolve 5 2 32 = 0` (`b₁ = 0`), remainder `32/2 = 16`; frame slot
`slotIdx 16 = 0`; `π`-exponent `(16 − 0)/2 = 8`. -/
theorem s4_slot3_row (h2 : Irreducible (2 : O)) (hq : residueCard O = 2)
    (H₀ : ℕ) (hpin : (s2Frame h2 hq).Pin H₀) :
    (s2Witness h2 hq H₀ hpin).towerNorm 2 85 = (8, 0, ![0, 1]) := by
  have hu3 : (s2Witness h2 hq H₀ hpin).u (1 + 2) = 21 := rfl
  have he3 : (s2Witness h2 hq H₀ hpin).e (1 + 2) = 2 := rfl
  have hu2 : (s2Witness h2 hq H₀ hpin).u (0 + 2) = 5 := rfl
  have he2 : (s2Witness h2 hq H₀ hpin).e (0 + 2) = 2 := rfl
  have hh : (s2Frame h2 hq).h = 1 := rfl
  have he1 : (s2Frame h2 hq).e₁ = 2 := rfl
  have hb2 : towerSolve 21 2 85 = 1 := rfl
  have hb1 : towerSolve 5 2 32 = 0 := rfl
  have hsl : (s2Frame h2 hq).slotIdx 16 = 0 := by
    change ((List.range 2).find? (fun i => (i * 1) % 2 == 16 % 2)).getD 0 = 0
    rfl
  simp only [DeepTower.towerNorm, hu3, he3, hb2, hu2, he2, hb1, hh, he1]
  norm_num [hsl, Prod.ext_iff]
  funext j
  fin_cases j <;> rfl

end TowerRows

/-! ### The mirror diffs for §4's sixteen entries (`budgetFloorN` at the landed towers'
numerals — the same values, read off the transcribed mirror) -/

#guard (List.range 4).map (fun j => budgetFloorN 2 2 10 3 j 0) == [8, 6, 3, 1]
#guard (List.range 4).map (fun j => budgetFloorN 2 2 10 3 j 5) == [7, 4, 2, 0]
#guard (List.range 4).map (fun j => budgetFloorN 1 2 6 3 j 0) == [10, 7, 4, 1]
#guard (List.range 4).map (fun j => budgetFloorN 1 2 6 3 j 5) == [7, 4, 1, 0]

end Uniformity.Density.Tower.C123

/-! ## AxCheck footer -/

#print axioms Uniformity.Density.Tower.C123.htSpot_q2
#print axioms Uniformity.Density.Tower.C123.htSpotAlt_q2
#print axioms Uniformity.Density.Tower.C123.s2Tower_budget_rows
#print axioms Uniformity.Density.Tower.C123.linTower_budget_rows
#print axioms Uniformity.Density.Tower.C123.E₂_split_s2
#print axioms Uniformity.Density.Tower.C123.E₂_split_lin
#print axioms Uniformity.Density.Tower.C123.s2_witness_row
#print axioms Uniformity.Density.Tower.C123.s2_ladder_row
#print axioms Uniformity.Density.Tower.C123.s4_slot3_row
