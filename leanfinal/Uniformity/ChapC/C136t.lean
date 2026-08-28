/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapC.C130pk
import Uniformity.ChapC.C132rp10b
import Uniformity.ChapC.C132kp3

/-!
# Uniformity.ChapC.C136t — DWC tower/key carriers, nodes T1–T5 [TSTK 2026-08-28]

**Unit TSTK** of the deep-witness campaign
(`docs/in-progress/DEEP_WITNESS_CAMPAIGN_2026-08-28.md` §6.1, rows T1–T5; T0 the numeric
certificate `verification/dwc_tower_cert.py` is already green).  This file lands the tower
and key CARRIER rows only — pure data extensions and exponent/degree pins.  Per the GCW-6
fence, everything here is DATA (a `DeepTower` extension, a `KeyChain`, exponent
bookkeeping): no `RealizedInput`, no wired witness, no socket is touched.

* **T1 — the depth-three S2 occurrence alias.**  `s2DepthThree` is C.97's landed
  `s2Witness` at its unique pin `(1, s2Frame_pin)` — the same occurrence C130s2's
  `s2DepthTwo` truncates.  `s2DepthThreeKeyAt` extends the landed depth-two chain
  function with `keyAt 3 = g8` (M3-RP10b's landed `g₈ = Φ₂² − 2⁴Φ′`), with the degree
  pins `2 / 4 / 8` and monicity at all three live levels.
* **T2 — the `g8` key proof and the depth-three `KeyChain`.**  `s2Mu3KeyPoly_g8` proves
  `S2Mu3KeyPoly (g8)` from the landed criterion (`C132kp3.s2Mu3_key_criterion`) fed the
  landed residual facts (`C132rp10b.s2Mu3NormRes_g8` = `X + 1`,
  `C132rp10.s2Mu3_X_add_one_irreducible`); `s2DepthThreeKeyChain` packages the chain.
* **T3 — the depth-four tower datum.**  `s2WitnessFour` extends the landed witness with
  stage `(e₄, f₄, u₄) = (2, 1, 85)`, `ψ₃ = T − 1`, constant residue tower — the worked
  continuation `5, 21, 85` the C.97 module record names.  Pins: the floor `84 < 85` (read
  off the datum's own `hfloor`) and `Dcum 4 = 16`.  §3.1's conjectural fourth row becomes
  a Lean datum here.  `s2DepthFour` is its pinned occurrence.
* **T4 — depth-three normalizer pins** (operator triple `(2, 1, 85)` at `s2DepthThree`).
  The exponent solve `towerNorm 2 85 = (8, 0, ![0, 1])`, the A-C.18 normalizer polynomial
  `chainNormBelow 3 85 = 2⁸ · Φ₂` at any calculus carrying the T2 chain (the C132rp9
  genre), and its degree `4 < 8 = deg (keyAt 3)`.
  **Recorded split:** the μ₄ exact-grade supply — that this tooth has exact μ₄ grade
  `170 = 2·85` — WAITS on the D3 stack's grade bank (D3-05/D3-13); no μ₄ operator is
  invented here.
* **T5 — depth-four normalizer pins** (refinement triple `(1, 1, 171)` at `s2DepthFour`;
  NOT a fifth tower stage — C.83's `hproper` excludes `e′f′ = 1` stages, and no such
  stage is constructed).  The PURE EXPONENT theorem
  `towerNorm 3 171 = (1, 1, ![1, 1, 1])` lands now, together with the polynomial value
  `s2Mu5Lambda = 2 · x · Φ′ · Φ₂ · g₈` of `chainNormBelow 4 171` at any calculus whose
  keys `1..3` are the T1 keys (pointwise premises — only keys `1..3` occur in
  `chainNorm 3`), its degree `15 < 16`, and its nonvanishing.
  **Recorded split (the blueprint's intentional two-part row):** the chain-level form —
  `hkey : I.keyAt = (depth-four chain).keyAt` against a depth-four `KeyChain` — WAITS on
  D3-19's `keyAt 4 = g16`, since no depth-four `KeyChain` exists before the μ₄
  normalized-existence leaf; likewise the μ₅ exact-grade supply (grade `171`) waits on
  D4-03/D4-10.

## Status

Zero `sorry`; axiom footprint Lean-core only for every declaration (AxCheck footer — in
particular the μ₃ key-criterion path carries no literature cite).  No landed statement is
touched; the two deferred halves above are recorded, not stubbed.  Verdict:
`runs/wave-c/verdict_TSTK.md`.
-/

set_option linter.style.longLine false

namespace Uniformity.Density.Tower.C136t

open Polynomial IsLocalRing IsDiscreteValuationRing Uniformity.Density
open Uniformity.Density.Leaf Uniformity.Density.Tower
open Uniformity.Density.Tower.C35b Uniformity.Density.Tower.C80
open Uniformity.Density.Tower.C130s2
open Uniformity.Density.Tower.C132nv1 Uniformity.Density.Tower.C132rp7
open Uniformity.Density.Tower.C132rp10 Uniformity.Density.Tower.C132rp10b
open Uniformity.Density.Tower.C132kp0 Uniformity.Density.Tower.C132kp3

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)] (h2 : Irreducible (2 : O)) (hq : residueCard O = 2)

/-! ## T1 — the depth-three S2 occurrence alias and its key function -/

/-- **T1 — the depth-three S2 occurrence**: C.97's landed `s2Witness` at its unique pin
`(1, s2Frame_pin)`, aliased in the style of C130s2's `s2DepthTwo` (which is this datum's
depth-two truncation). -/
noncomputable def s2DepthThree : DeepTower (s2Frame h2 hq) 1 (s2Frame_pin h2 hq) 3 :=
  s2Witness h2 hq 1 (s2Frame_pin h2 hq)

/-- Anti-drift pin: `s2DepthThree` IS the landed witness, definitionally. -/
theorem s2DepthThree_eq_witness :
    s2DepthThree h2 hq = s2Witness h2 hq 1 (s2Frame_pin h2 hq) := rfl

/-- Anti-drift pin: its depth-two truncation IS C130s2's `s2DepthTwo`, definitionally. -/
theorem s2DepthThree_trunc_two :
    (s2DepthThree h2 hq).trunc 2 (by omega) = s2DepthTwo h2 hq := rfl

/-- `D₁ = e₁f₁ = 2` at the depth-three occurrence. -/
theorem s2DepthThree_Dcum_one : (s2DepthThree h2 hq).Dcum 1 = 2 := by
  rw [DeepTower.Dcum, show (Finset.Icc 1 1 : Finset ℕ) = {1} by decide,
    Finset.prod_singleton]
  rfl

/-- `D₂ = (e₁f₁)(e₂f₂) = 4` at the depth-three occurrence. -/
theorem s2DepthThree_Dcum_two : (s2DepthThree h2 hq).Dcum 2 = 4 := by
  rw [DeepTower.Dcum, show (Finset.Icc 1 2 : Finset ℕ) = {1, 2} by decide,
    Finset.prod_insert (by decide), Finset.prod_singleton]
  rfl

/-- `D₃ = (e₁f₁)(e₂f₂)(e₃f₃) = 8` at the depth-three occurrence. -/
theorem s2DepthThree_Dcum_three : (s2DepthThree h2 hq).Dcum 3 = 8 := by
  rw [DeepTower.Dcum, show (Finset.Icc 1 3 : Finset ℕ) = {1, 2, 3} by decide,
    Finset.prod_insert (by decide), Finset.prod_insert (by decide),
    Finset.prod_singleton]
  rfl

/-- **T1 — the depth-three key function**: the landed depth-two chain function at levels
`≤ 2` (`Φ′ = x² − 2`, `Φ₂ = composedKey (s2Tower)`), M3-RP10b's landed
`g₈ = Φ₂² − 2⁴Φ′` at every higher index (only level `3` is ever read — `KeyChain`'s laws
are `StageLive`-fenced). -/
noncomputable def s2DepthThreeKeyAt (i : ℕ) : Polynomial O :=
  if i ≤ 2 then s2DepthTwoKeyAt h2 hq i else g8 h2 hq

/-- Level 1 of the depth-three key function is the frame key `Φ′`. -/
theorem s2DepthThreeKeyAt_one :
    s2DepthThreeKeyAt h2 hq 1 = (s2Frame h2 hq).key := rfl

/-- Level 2 of the depth-three key function is the landed depth-two chain's level 2.
(Proved by `if_pos` rather than `rfl`: the bare kernel defeq check lazy-delta-compares the
unequal `ite` branches `g8` vs the landed key definitions argument-wise and times out.) -/
theorem s2DepthThreeKeyAt_two :
    s2DepthThreeKeyAt h2 hq 2 = s2DepthTwoKeyAt h2 hq 2 := by
  show (if (2 : ℕ) ≤ 2 then s2DepthTwoKeyAt h2 hq 2 else g8 h2 hq)
    = s2DepthTwoKeyAt h2 hq 2
  rw [if_pos (by norm_num : (2 : ℕ) ≤ 2)]

/-- **`keyAt 3 = g8`** — the campaign's depth-three key assignment. -/
theorem s2DepthThreeKeyAt_three :
    s2DepthThreeKeyAt h2 hq 3 = g8 h2 hq := rfl

/-- monicity pin, level 1 (the frame key). -/
theorem s2DepthThreeKeyAt_monic_one : (s2DepthThreeKeyAt h2 hq 1).Monic := by
  rw [s2DepthThreeKeyAt_one h2 hq]
  exact (s2Frame h2 hq).hmonic

/-- monicity pin, level 2 (`Φ₂`, C132nv1's `s2Φ₂_monic`). -/
theorem s2DepthThreeKeyAt_monic_two : (s2DepthThreeKeyAt h2 hq 2).Monic := by
  rw [s2DepthThreeKeyAt_two h2 hq]
  exact s2Φ₂_monic h2 hq

/-- monicity pin, level 3 (`g₈`, M3-RP10's landed monicity). -/
theorem s2DepthThreeKeyAt_monic_three : (s2DepthThreeKeyAt h2 hq 3).Monic := by
  rw [s2DepthThreeKeyAt_three h2 hq]
  exact s2Mu3_gEight_monic h2 hq

/-- degree pin `2`, level 1. -/
theorem s2DepthThreeKeyAt_natDegree_one :
    (s2DepthThreeKeyAt h2 hq 1).natDegree = 2 := by
  rw [s2DepthThreeKeyAt_one h2 hq, (s2Frame h2 hq).hdeg, e1_eq h2 hq, f1_eq h2 hq]

/-- degree pin `4`, level 2. -/
theorem s2DepthThreeKeyAt_natDegree_two :
    (s2DepthThreeKeyAt h2 hq 2).natDegree = 4 := by
  rw [s2DepthThreeKeyAt_two h2 hq]
  exact s2Φ₂_natDegree h2 hq

/-- degree pin `8`, level 3 (M3-RP10's landed degree). -/
theorem s2DepthThreeKeyAt_natDegree_three :
    (s2DepthThreeKeyAt h2 hq 3).natDegree = 8 := by
  rw [s2DepthThreeKeyAt_three h2 hq]
  exact s2Mu3_gEight_natDegree h2 hq

/-! ## T2 — the `g8` key proof and the depth-three `KeyChain` -/

/-- **T2 — `g₈` is a μ₃ key polynomial.**  The landed criterion
(`C132kp3.s2Mu3_key_criterion`) fed the landed facts: monic (M3-RP10), degree
`8 = 2·1·deg Φ₂` (M3-RP10), normalized μ₃ residual `X + 1` (M3-RP10b's
`s2Mu3NormRes_g8`), which is irreducible of degree one with nonzero constant term
(M3-RP10's `s2Mu3_X_add_one_irreducible` and the two-element-field numerals). -/
theorem s2Mu3KeyPoly_g8 : S2Mu3KeyPoly h2 hq (g8 h2 hq) := by
  refine s2Mu3_key_criterion h2 hq (g8 h2 hq) (s2Mu3_gEight_monic h2 hq) ?_ ?_ ?_ ?_
  · rw [s2Mu3KeyChain_keyAt_two_natDegree h2 hq]
    exact s2Mu3_gEight_natDegree h2 hq
  · rw [s2Mu3NormRes_g8 h2 hq]
    exact s2Mu3_X_add_one_irreducible h2 hq
  · rw [s2Mu3NormRes_g8 h2 hq, ← Polynomial.C_1, Polynomial.natDegree_X_add_C]
  · rw [s2Mu3NormRes_g8 h2 hq]
    simp

/-- ★ **T2 — the depth-three S2 `KeyChain`**: `Φ′ / Φ₂ / g₈` over `s2DepthThree`, every
C.130k field discharged from the T1 pins.  This is the carrier consumed by the campaign's
depth-three `(2, 1, 85)` calculus rows (D3-18/D3-19). -/
noncomputable def s2DepthThreeKeyChain : KeyChain (s2DepthThree h2 hq) where
  keyAt := s2DepthThreeKeyAt h2 hq
  keyAt_one := s2DepthThreeKeyAt_one h2 hq
  keyAt_monic := by
    intro i hi
    obtain ⟨hi1, hi2⟩ := hi
    interval_cases i
    · exact s2DepthThreeKeyAt_monic_one h2 hq
    · exact s2DepthThreeKeyAt_monic_two h2 hq
    · exact s2DepthThreeKeyAt_monic_three h2 hq
  keyAt_degree := by
    intro i hi
    obtain ⟨hi1, hi2⟩ := hi
    interval_cases i
    · rw [s2DepthThreeKeyAt_natDegree_one h2 hq, s2DepthThree_Dcum_one h2 hq]
    · rw [s2DepthThreeKeyAt_natDegree_two h2 hq, s2DepthThree_Dcum_two h2 hq]
    · rw [s2DepthThreeKeyAt_natDegree_three h2 hq, s2DepthThree_Dcum_three h2 hq]

/-! ## T3 — the depth-four tower datum -/

/-- **T3 — THE DEPTH-FOUR S2 TOWER DATUM**: C.97's witness extended by the worked stage
`(e₄, f₄, u₄) = (2, 1, 85)` with `ψ₃ = T − 1` and constant residue tower (all upper
stages totally ramified, `f = 1`).  The floor chain is the datum's `hfloor` at the
numerals `4 < 5`, `20 < 21`, `84 < 85` (the last is the T3 pin).  §3.1's stage-four row —
an examples-first conjecture until this datum — is a Lean witness from here on.

GCW-6 fence: this is DATA (a `DeepTower`), not a wired capstone witness; no
`RealizedInput` or socket consumes it in this file. -/
noncomputable def s2WitnessFour (H₀ : ℕ) (hpin : (s2Frame h2 hq).Pin H₀) :
    DeepTower (s2Frame h2 hq) H₀ hpin 4 :=
  letI : Field ((s2Frame h2 hq).stageField H₀ hpin) := s2StageFieldInst h2 hq H₀ hpin
  { e := fun _ => 2
    f := fun _ => 1
    u := fun i => if i = 1 then 1 else if i = 2 then 5 else if i = 3 then 21 else 85
    fld := fun _ => (s2Frame h2 hq).stageField H₀ hpin
    fldField := fun _ => s2StageFieldInst h2 hq H₀ hpin
    ψ := fun _ => Polynomial.X - Polynomial.C 1
    he1 := rfl
    hf1 := rfl
    hu1 := rfl
    he := fun i _ _ => by norm_num
    hf := fun i _ _ => by norm_num
    hproper := fun i _ _ => by norm_num
    hcop := fun i hi hi' => by interval_cases i <;> decide
    hfloor := fun i hi hi' => by interval_cases i <;> norm_num
    hψ := fun i _ _ => ⟨monic_X_sub_C 1, irreducible_X_sub_C 1, natDegree_X_sub_C 1, by
      simp only [coeff_sub, coeff_X_zero, coeff_C_zero, zero_sub, ne_eq, neg_eq_zero]
      exact one_ne_zero⟩
    base := RingEquiv.refl _
    step := fun i _ _ => (Polynomial.quotientSpanXSubCAlgEquiv (1 : _)).toRingEquiv.symm }

/-- **the depth-four occurrence**: `s2WitnessFour` at the frame's unique pin, the datum the
campaign's depth-four `(1, 1, 171)` refinement rows (D4 stack) run on. -/
noncomputable def s2DepthFour : DeepTower (s2Frame h2 hq) 1 (s2Frame_pin h2 hq) 4 :=
  s2WitnessFour h2 hq 1 (s2Frame_pin h2 hq)

/-- The extension's signed stage values: `(e, f, u) = (2,1,5), (2,1,21), (2,1,85)` at
stages `2, 3, 4`. -/
theorem s2WitnessFour_values (H₀ : ℕ) (hpin : (s2Frame h2 hq).Pin H₀) :
    (s2WitnessFour h2 hq H₀ hpin).e 2 = 2 ∧ (s2WitnessFour h2 hq H₀ hpin).f 2 = 1 ∧
      (s2WitnessFour h2 hq H₀ hpin).u 2 = 5 ∧
      (s2WitnessFour h2 hq H₀ hpin).e 3 = 2 ∧ (s2WitnessFour h2 hq H₀ hpin).f 3 = 1 ∧
      (s2WitnessFour h2 hq H₀ hpin).u 3 = 21 ∧
      (s2WitnessFour h2 hq H₀ hpin).e 4 = 2 ∧ (s2WitnessFour h2 hq H₀ hpin).f 4 = 1 ∧
      (s2WitnessFour h2 hq H₀ hpin).u 4 = 85 :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- `ψ₃ = T − 1` (the stage-4 residual over the constant residue tower). -/
theorem s2WitnessFour_psi_three (H₀ : ℕ) (hpin : (s2Frame h2 hq).Pin H₀) :
    (s2WitnessFour h2 hq H₀ hpin).ψ 3 = Polynomial.X - Polynomial.C 1 := rfl

/-- Anti-drift pin: on the live range of the landed witness (`1 ≤ i ≤ 3`), the extension's
stage data agree with `s2Witness`'s. -/
theorem s2WitnessFour_agrees (H₀ : ℕ) (hpin : (s2Frame h2 hq).Pin H₀) :
    ∀ i, 1 ≤ i → i ≤ 3 →
      (s2WitnessFour h2 hq H₀ hpin).e i = (s2Witness h2 hq H₀ hpin).e i ∧
      (s2WitnessFour h2 hq H₀ hpin).f i = (s2Witness h2 hq H₀ hpin).f i ∧
      (s2WitnessFour h2 hq H₀ hpin).u i = (s2Witness h2 hq H₀ hpin).u i := by
  intro i hi1 hi3
  interval_cases i
  · exact ⟨rfl, rfl, rfl⟩
  · exact ⟨rfl, rfl, rfl⟩
  · exact ⟨rfl, rfl, rfl⟩

/-- **T3 pin — the new floor `84 < 85`**, read off the datum's own `hfloor` field at the
new rung (`e₄·E₃ = 2·(2·1·21) = 84 < 85 = u₄`). -/
theorem s2WitnessFour_floor_four (H₀ : ℕ) (hpin : (s2Frame h2 hq).Pin H₀) :
    (84 : ℕ) < 85 :=
  (s2WitnessFour h2 hq H₀ hpin).hfloor 3 (by norm_num) (by norm_num)

/-- **T3 pin — `Dcum 4 = 16`**: the cumulative degree of the depth-four tower. -/
theorem s2WitnessFour_Dcum_four (H₀ : ℕ) (hpin : (s2Frame h2 hq).Pin H₀) :
    (s2WitnessFour h2 hq H₀ hpin).Dcum 4 = 16 := by
  rw [DeepTower.Dcum, show (Finset.Icc 1 4 : Finset ℕ) = {1, 2, 3, 4} by decide,
    Finset.prod_insert (by decide), Finset.prod_insert (by decide),
    Finset.prod_insert (by decide), Finset.prod_singleton]
  rfl

/-! ## T4 — the depth-three normalizer pins (operator triple `(2, 1, 85)`)

The μ₄ EXACT-GRADE half of this row — that the tooth below has exact μ₄ grade
`170 = 2·85` — is deliberately NOT stated here: the μ₄ grade bank is the D3 stack
(D3-05/D3-13).  Only the exponent solve, the polynomial value, and the degree pins land
now (the blueprint's "exact-grade waits D3"). -/

/-- **T4 — the exponent pin `n̂₃(85)`**: `towerNorm 2 85 = (8, 0, ![0, 1])` at the
depth-three occurrence — i.e. `n̂₃(85) = 2⁸·x⁰·Φ′⁰·Φ₂¹ = 2⁸Φ₂`, EFF.GENTOW5.21's worked
regression value.  The rung solves: `towerSolve 21 2 85 = 1`, carried remainder
`(85 − 21)/2 = 32`; `towerSolve 5 2 32 = 0`, carried remainder `16`; frame slot
`slotIdx 16 = 0`, `π`-exponent `16/2 = 8`. -/
theorem s2DepthThree_towerNorm_two_eighty_five :
    (s2DepthThree h2 hq).towerNorm 2 85 = (8, 0, ![0, 1]) := by
  have hu3 : (s2DepthThree h2 hq).u (1 + 2) = 21 := rfl
  have he3 : (s2DepthThree h2 hq).e (1 + 2) = 2 := rfl
  have hu2 : (s2DepthThree h2 hq).u (0 + 2) = 5 := rfl
  have he2 : (s2DepthThree h2 hq).e (0 + 2) = 2 := rfl
  have hh : (s2Frame h2 hq).h = 1 := rfl
  have he1 : (s2Frame h2 hq).e₁ = 2 := rfl
  have hb2 : towerSolve 21 2 85 = 1 := rfl
  have hb1 : towerSolve 5 2 32 = 0 := rfl
  have hsl : (s2Frame h2 hq).slotIdx 16 = 0 := by
    change ((List.range 2).find? (fun i => (i * 1) % 2 == 16 % 2)).getD 0 = 0
    rfl
  simp only [DeepTower.towerNorm, hu3, he3, hu2, he2, hh, he1, hb2, hb1]
  norm_num [hsl, Prod.ext_iff]
  funext j
  fin_cases j <;> rfl

/-- **T4 — the normalizer polynomial**: A-C.18's below-current normalizer at the
depth-three occurrence computes to `2⁸ · Φ₂` whenever the calculus carries the T2 chain
(the C132rp9 genre, one level up). -/
theorem s2Mu4_chainNormBelow_three_eighty_five
    (I : FGMNCalculus (s2DepthThree h2 hq) 2 1 85)
    (hkey : I.keyAt = (s2DepthThreeKeyChain h2 hq).keyAt) :
    I.chainNormBelow 3 85 =
      Polynomial.C ((2 : O) ^ 8) * (s2DepthThreeKeyChain h2 hq).keyAt 2 := by
  rw [FGMNCalculus.chainNormBelow, FGMNCalculus.chainNorm,
    s2DepthThree_towerNorm_two_eighty_five h2 hq, hkey]
  simp [Fin.prod_univ_two]

/-- **T4 — the tooth's degree is `4`.** -/
theorem s2Mu4_chainNormBelow_tooth_natDegree :
    (Polynomial.C ((2 : O) ^ 8) * (s2DepthThreeKeyChain h2 hq).keyAt 2).natDegree = 4 := by
  rw [Polynomial.natDegree_C_mul (pow_ne_zero 8 h2.ne_zero)]
  exact s2DepthThreeKeyAt_natDegree_two h2 hq

/-- **T4 — `4 < 8 = deg (keyAt 3)`**: the tooth's degree is strictly below the carried
depth-three key's. -/
theorem s2Mu4_chainNormBelow_tooth_degree_lt_key :
    (Polynomial.C ((2 : O) ^ 8) * (s2DepthThreeKeyChain h2 hq).keyAt 2).natDegree <
      ((s2DepthThreeKeyChain h2 hq).keyAt 3).natDegree := by
  have h3 : ((s2DepthThreeKeyChain h2 hq).keyAt 3).natDegree = 8 :=
    s2DepthThreeKeyAt_natDegree_three h2 hq
  rw [s2Mu4_chainNormBelow_tooth_natDegree h2 hq, h3]
  norm_num

/-! ## T5 — the depth-four normalizer pins (refinement triple `(1, 1, 171)`)

The blueprint's ONE intentional two-part row.  What lands now: the pure exponent theorem,
the polynomial value at pointwise key premises (only keys `1..3` occur in `chainNorm 3`),
degree `15 < 16`, and nonvanishing.  What waits: the chain-level restatement with
`hkey : I.keyAt = (depth-four chain).keyAt` — no depth-four `KeyChain` exists before
D3-19 constructs `keyAt 4 = g16` — and the μ₅ exact-grade supply (grade `171`,
D4-03/D4-10). -/

/-- **T5 — the pure exponent theorem `n̂₄(171)`**: `towerNorm 3 171 = (1, 1, ![1, 1, 1])`
at the depth-four datum — i.e. `n̂₄(171) = 2¹·x¹·Φ′·Φ₂·Φ₃`.  The rung solves:
`towerSolve 85 2 171 = 1`, remainder `(171 − 85)/2 = 43`; `towerSolve 21 2 43 = 1`,
remainder `11`; `towerSolve 5 2 11 = 1`, remainder `3`; frame slot `slotIdx 3 = 1`,
`π`-exponent `(3 − 1)/2 = 1`. -/
theorem s2WitnessFour_towerNorm_three_one_seventy_one (H₀ : ℕ)
    (hpin : (s2Frame h2 hq).Pin H₀) :
    (s2WitnessFour h2 hq H₀ hpin).towerNorm 3 171 = (1, 1, ![1, 1, 1]) := by
  have hu4 : (s2WitnessFour h2 hq H₀ hpin).u (2 + 2) = 85 := rfl
  have he4 : (s2WitnessFour h2 hq H₀ hpin).e (2 + 2) = 2 := rfl
  have hu3 : (s2WitnessFour h2 hq H₀ hpin).u (1 + 2) = 21 := rfl
  have he3 : (s2WitnessFour h2 hq H₀ hpin).e (1 + 2) = 2 := rfl
  have hu2 : (s2WitnessFour h2 hq H₀ hpin).u (0 + 2) = 5 := rfl
  have he2 : (s2WitnessFour h2 hq H₀ hpin).e (0 + 2) = 2 := rfl
  have hh : (s2Frame h2 hq).h = 1 := rfl
  have he1 : (s2Frame h2 hq).e₁ = 2 := rfl
  have hb3 : towerSolve 85 2 171 = 1 := rfl
  have hb2 : towerSolve 21 2 43 = 1 := rfl
  have hb1 : towerSolve 5 2 11 = 1 := rfl
  have hsl : (s2Frame h2 hq).slotIdx 3 = 1 := by
    change ((List.range 2).find? (fun i => (i * 1) % 2 == 3 % 2)).getD 0 = 1
    rfl
  simp only [DeepTower.towerNorm, hu4, he4, hu3, he3, hu2, he2, hh, he1, hb3, hb2, hb1]
  norm_num [hsl, Prod.ext_iff]
  funext j
  fin_cases j <;> rfl

/-- The pure exponent theorem at the pinned depth-four occurrence. -/
theorem s2DepthFour_towerNorm_three_one_seventy_one :
    (s2DepthFour h2 hq).towerNorm 3 171 = (1, 1, ![1, 1, 1]) :=
  s2WitnessFour_towerNorm_three_one_seventy_one h2 hq 1 (s2Frame_pin h2 hq)

/-- **T5 — the μ₅ correction `Λ`** (§3.3's `Λ = chainNormBelow 4 171` as a literal
polynomial): `2 · x · Φ′ · Φ₂ · g₈`, the product of the exponent row `(1, 1, [1, 1, 1])`
over the T1 keys. -/
noncomputable def s2Mu5Lambda : Polynomial O :=
  Polynomial.C (2 : O) * Polynomial.X *
    (s2DepthThreeKeyAt h2 hq 1 * s2DepthThreeKeyAt h2 hq 2 * s2DepthThreeKeyAt h2 hq 3)

/-- **T5 — the normalizer polynomial, pointwise-key form**: at the depth-four occurrence,
any calculus whose keys `1..3` are the T1 keys computes `chainNormBelow 4 171 = Λ`.
(`chainNorm 3` multiplies keys `1..3` only, so no `keyAt 4` premise is needed; the
chain-level `hkey` restatement is the recorded deferred half, D3-19.) -/
theorem s2Mu5_chainNormBelow_four_one_seventy_one
    (I : FGMNCalculus (s2DepthFour h2 hq) 1 1 171)
    (hk1 : I.keyAt 1 = s2DepthThreeKeyAt h2 hq 1)
    (hk2 : I.keyAt 2 = s2DepthThreeKeyAt h2 hq 2)
    (hk3 : I.keyAt 3 = s2DepthThreeKeyAt h2 hq 3) :
    I.chainNormBelow 4 171 = s2Mu5Lambda h2 hq := by
  rw [FGMNCalculus.chainNormBelow, FGMNCalculus.chainNorm,
    s2DepthFour_towerNorm_three_one_seventy_one h2 hq]
  rw [s2Mu5Lambda]
  simp [Fin.prod_univ_three, hk1, hk2, hk3]

/-- the three key factors of `Λ` are nonzero (they are monic over a nontrivial ring). -/
private theorem s2Mu5Lambda_factors_ne_zero :
    s2DepthThreeKeyAt h2 hq 1 ≠ 0 ∧ s2DepthThreeKeyAt h2 hq 2 ≠ 0 ∧
      s2DepthThreeKeyAt h2 hq 3 ≠ 0 :=
  ⟨(s2DepthThreeKeyAt_monic_one h2 hq).ne_zero,
    (s2DepthThreeKeyAt_monic_two h2 hq).ne_zero,
    (s2DepthThreeKeyAt_monic_three h2 hq).ne_zero⟩

/-- **T5 — `deg Λ = 15`** (`= 0 + 1 + 2 + 4 + 8`). -/
theorem s2Mu5Lambda_natDegree : (s2Mu5Lambda h2 hq).natDegree = 15 := by
  obtain ⟨hk1, hk2, hk3⟩ := s2Mu5Lambda_factors_ne_zero h2 hq
  have hCX : (Polynomial.C (2 : O) * Polynomial.X : Polynomial O) ≠ 0 :=
    mul_ne_zero (Polynomial.C_ne_zero.mpr h2.ne_zero) Polynomial.X_ne_zero
  rw [s2Mu5Lambda,
    Polynomial.natDegree_mul hCX (mul_ne_zero (mul_ne_zero hk1 hk2) hk3),
    Polynomial.natDegree_mul (mul_ne_zero hk1 hk2) hk3,
    Polynomial.natDegree_mul hk1 hk2,
    Polynomial.natDegree_C_mul h2.ne_zero, Polynomial.natDegree_X,
    s2DepthThreeKeyAt_natDegree_one h2 hq, s2DepthThreeKeyAt_natDegree_two h2 hq,
    s2DepthThreeKeyAt_natDegree_three h2 hq]

/-- **T5 — `deg Λ < 16`**: the correction clears the depth-four recipe degree
`e′f′·D₄ = 16`. -/
theorem s2Mu5Lambda_natDegree_lt : (s2Mu5Lambda h2 hq).natDegree < 16 := by
  rw [s2Mu5Lambda_natDegree h2 hq]
  norm_num

/-- **T5 — `Λ ≠ 0`**: the recentering is not the trivial one. -/
theorem s2Mu5Lambda_ne_zero : s2Mu5Lambda h2 hq ≠ 0 := by
  obtain ⟨hk1, hk2, hk3⟩ := s2Mu5Lambda_factors_ne_zero h2 hq
  exact mul_ne_zero
    (mul_ne_zero (Polynomial.C_ne_zero.mpr h2.ne_zero) Polynomial.X_ne_zero)
    (mul_ne_zero (mul_ne_zero hk1 hk2) hk3)

end Uniformity.Density.Tower.C136t

/-! ## Teeth — the campaign numerals, read off the landed data

The cleared exact-grade TARGET at the depth-three operator is `170 = (2·1)·85 = e′·u′`
(D3-13's future supply; recorded here as the numeral identity only — no μ₄ grade is
asserted).  The depth-four recipe degree is `16 = 1·1·16 = e′f′·D₄`. -/

section Teeth

open IsLocalRing Uniformity.Density Uniformity.Density.Tower
open Uniformity.Density.Tower.C136t

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)] (h2 : Irreducible (2 : O)) (hq : residueCard O = 2)

-- the T4 exact-grade target numeral (the μ₄ grade itself waits on the D3 stack)
example : 2 * 1 * 85 = 170 := rfl

-- the rung solves of the extended chain, at the `towerSolve` level
example : towerSolve 21 2 85 = 1 := by decide
example : towerSolve 85 2 171 = 1 := by decide

-- the chain's three live degrees, read off the T2 chain
example : ((s2DepthThreeKeyChain h2 hq).keyAt 1).natDegree = 2 :=
  s2DepthThreeKeyAt_natDegree_one h2 hq
example : ((s2DepthThreeKeyChain h2 hq).keyAt 2).natDegree = 4 :=
  s2DepthThreeKeyAt_natDegree_two h2 hq
example : ((s2DepthThreeKeyChain h2 hq).keyAt 3).natDegree = 8 :=
  s2DepthThreeKeyAt_natDegree_three h2 hq

-- the depth-four floor chain, all three rungs off the datum's own `hfloor`
example (H₀ : ℕ) (hpin : (s2Frame h2 hq).Pin H₀) :
    (4 : ℕ) < 5 ∧ (20 : ℕ) < 21 ∧ (84 : ℕ) < 85 :=
  ⟨(s2WitnessFour h2 hq H₀ hpin).hfloor 1 (by norm_num) (by norm_num),
    (s2WitnessFour h2 hq H₀ hpin).hfloor 2 (by norm_num) (by norm_num),
    (s2WitnessFour h2 hq H₀ hpin).hfloor 3 (by norm_num) (by norm_num)⟩

end Teeth

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Tower.C136t.s2DepthThree
#print axioms Uniformity.Density.Tower.C136t.s2DepthThree_eq_witness
#print axioms Uniformity.Density.Tower.C136t.s2DepthThree_trunc_two
#print axioms Uniformity.Density.Tower.C136t.s2DepthThree_Dcum_one
#print axioms Uniformity.Density.Tower.C136t.s2DepthThree_Dcum_two
#print axioms Uniformity.Density.Tower.C136t.s2DepthThree_Dcum_three
#print axioms Uniformity.Density.Tower.C136t.s2DepthThreeKeyAt
#print axioms Uniformity.Density.Tower.C136t.s2DepthThreeKeyAt_one
#print axioms Uniformity.Density.Tower.C136t.s2DepthThreeKeyAt_two
#print axioms Uniformity.Density.Tower.C136t.s2DepthThreeKeyAt_three
#print axioms Uniformity.Density.Tower.C136t.s2DepthThreeKeyAt_monic_one
#print axioms Uniformity.Density.Tower.C136t.s2DepthThreeKeyAt_monic_two
#print axioms Uniformity.Density.Tower.C136t.s2DepthThreeKeyAt_monic_three
#print axioms Uniformity.Density.Tower.C136t.s2DepthThreeKeyAt_natDegree_one
#print axioms Uniformity.Density.Tower.C136t.s2DepthThreeKeyAt_natDegree_two
#print axioms Uniformity.Density.Tower.C136t.s2DepthThreeKeyAt_natDegree_three
#print axioms Uniformity.Density.Tower.C136t.s2Mu3KeyPoly_g8
#print axioms Uniformity.Density.Tower.C136t.s2DepthThreeKeyChain
#print axioms Uniformity.Density.Tower.C136t.s2WitnessFour
#print axioms Uniformity.Density.Tower.C136t.s2DepthFour
#print axioms Uniformity.Density.Tower.C136t.s2WitnessFour_values
#print axioms Uniformity.Density.Tower.C136t.s2WitnessFour_psi_three
#print axioms Uniformity.Density.Tower.C136t.s2WitnessFour_agrees
#print axioms Uniformity.Density.Tower.C136t.s2WitnessFour_floor_four
#print axioms Uniformity.Density.Tower.C136t.s2WitnessFour_Dcum_four
#print axioms Uniformity.Density.Tower.C136t.s2DepthThree_towerNorm_two_eighty_five
#print axioms Uniformity.Density.Tower.C136t.s2Mu4_chainNormBelow_three_eighty_five
#print axioms Uniformity.Density.Tower.C136t.s2Mu4_chainNormBelow_tooth_natDegree
#print axioms Uniformity.Density.Tower.C136t.s2Mu4_chainNormBelow_tooth_degree_lt_key
#print axioms Uniformity.Density.Tower.C136t.s2WitnessFour_towerNorm_three_one_seventy_one
#print axioms Uniformity.Density.Tower.C136t.s2DepthFour_towerNorm_three_one_seventy_one
#print axioms Uniformity.Density.Tower.C136t.s2Mu5Lambda
#print axioms Uniformity.Density.Tower.C136t.s2Mu5_chainNormBelow_four_one_seventy_one
#print axioms Uniformity.Density.Tower.C136t.s2Mu5Lambda_natDegree
#print axioms Uniformity.Density.Tower.C136t.s2Mu5Lambda_natDegree_lt
#print axioms Uniformity.Density.Tower.C136t.s2Mu5Lambda_ne_zero

end AxCheck
