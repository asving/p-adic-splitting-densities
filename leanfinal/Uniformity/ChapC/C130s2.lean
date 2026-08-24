/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapC.C130k
import Uniformity.ChapC.C53b
import Uniformity.ChapC.C80
import Uniformity.ChapC.C97

/-!
# Uniformity.ChapC.C130s2 — the S2 depth-two key chain and tower bridge (CC-2)

**Chain-carrier node CC-2** of `CHAIN_CARRIER_DESIGN_2026-08-24.md` (§6, the depth-two
instantiability check; §10 row CC-2): promote U11's elaboration-checked `s2DepthTwoKeyChain`
(`leanfinal/scratch/U11_carrier_check.lean`) into production against the **landed** `KeyChain`
of C.130k, and prove the full `(e, f, u, ψ, step)` bridge between the two landed S2 depth-two
occurrences:

* `s2DepthTwo := (s2Witness h2 hq 1 (s2Frame_pin h2 hq)).trunc 2` — C.97's depth-3 `DeepTower`
  witness truncated to depth two (C.83's `trunc`), the occurrence design §6 fixes;
* `s2Tower h2 hq : TowerDatum (s2Frame h2 hq) 1 (s2Frame_pin h2 hq)` — C.80's standalone
  depth-2 tower datum `(e₂, f₂, u₂, ψ₂) = (2, 1, 5, T − 1)`.

Design §6's non-conflation warning is respected: `s2Tower` is a `TowerDatum`, NOT a
`DeepTower`, and the unlanded `TowerDatum.deepTower` leanspec bridge is neither used nor
duplicated here.  The bridge below is the datum-wise identification of the truncated
`DeepTower`'s live data with the `TowerDatum`'s fields, over the SAME literal frame
`s2Frame h2 hq` at the SAME pin `(1, s2Frame_pin)`:

* `s2Bridge_e` / `s2Bridge_f` / `s2Bridge_u` — stage-2 arithmetic data `= (e₂, f₂, u₂)`;
* `s2Bridge_ψ` — the live residual `ψ 1 = ψ₂` (both `T − 1` over the stage field, which is
  well-typed because `fld 1` of the witness IS the frame's stage field);
* `s2BridgeStep` — the truncation's live `step` datum, RETYPED against `AdjoinRoot ψ₂` (the
  retyping compiling is the type-level content of the ψ-bridge), with `s2BridgeStep_eq_step`
  pinning that no new equivalence is invented and `s2BridgeStep_canonical` pinning the term to
  the canonical `X − C 1` quotient equivalence C.97 installed;
* `s2Bridge_Dcum` / `s2Bridge_Econst` — the derived bookkeeping ties `D₂ = Dcum 2 = 4` and
  `E₂ = Econst 2 = 10` that the key-chain degree law consumes.

On top of the bridge, the promoted carrier instance (OPEN-DICT-1's depth-two non-vacuity
check, design §6):

* `s2DepthTwoKeyAt` — `keyAt 1 = Φ′ = x² − 2` (the frame key), `keyAt 2 = composedKey
  (s2Tower h2 hq)` (EFF.HETOW.13's wrap-corrected composed key, C.43);
* `s2DepthTwoKeyChain : KeyChain (s2DepthTwo h2 hq)` — every C.130k field discharged:
  `keyAt_one` by definition, monicity at both live levels (frame `hmonic`; C.47's
  `composedKey_monic`), and the `Dcum` degree law at both live levels (frame `hdeg` at
  `Dcum 1 = 2`; C.53b's `composedKey_natDegree_D₂` at `Dcum 2 = D₂ = 4`).

## What this node does NOT claim (design §6's honest ledger)

Only the `KeyChain` row of §6's full-instance ledger is closed here.  The stage
`hgt`/`dig`/`Full` family, the Laurent normalizer, legal node points, the threshold/WINDOW,
the terminal receiver, and all FGMN source data/laws remain open constructor obligations of
the later CC nodes; no `NodePointSource`, `LaurentNormalizer`, or consumer structure is
instantiated or mentioned.  `linTower` receives nothing here (no landed `DeepTower` bridge —
design §6's last paragraph).

**DEPENDS.** C.130k (`KeyChain`, the landed CC-1 skeleton) · C.97 (`s2Frame`, `s2Frame_pin`,
`s2Witness`) · C.80 (`s2Tower`) · C.83 (`DeepTower.trunc`, `Dcum`, `Econst`) · C.43
(`composedKey`) · C.47 (`composedKey_monic`) · C.53b (`composedKey_natDegree_D₂`) — imported
(C.43/C.83 transitively).

## Status

Zero `sorry`; axiom footprint Lean-core only (AxCheck footer).  No cite.
-/

set_option linter.style.longLine false

namespace Uniformity.Density.Tower.C130s2

open Polynomial IsLocalRing IsDiscreteValuationRing Uniformity.Density
open Uniformity.Density.Leaf Uniformity.Density.Tower Uniformity.Density.Tower.C35b
open Uniformity.Density.Tower.C80

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)] (h2 : Irreducible (2 : O)) (hq : residueCard O = 2)

/-! ## 1. The S2 depth-two tower — the occurrence design §6 fixes -/

/-- **The S2 depth-two tower**: C.97's landed depth-3 witness truncated to depth two.  This is
the design §6 occurrence (`s2Witness … .trunc 2`), NOT a `TowerDatum.deepTower` image — that
bridge is unlanded and deliberately not reinvented here. -/
noncomputable def s2DepthTwo : DeepTower (s2Frame h2 hq) 1 (s2Frame_pin h2 hq) 2 :=
  (s2Witness h2 hq 1 (s2Frame_pin h2 hq)).trunc 2 (by omega)

/-- Anti-drift pin: `s2DepthTwo` IS the truncation of the landed witness, definitionally. -/
theorem s2DepthTwo_eq_trunc :
    s2DepthTwo h2 hq = (s2Witness h2 hq 1 (s2Frame_pin h2 hq)).trunc 2 (by omega) := rfl

/-- Stage-1 data = the frame's, as numerals: `(e₁, f₁, h) = (2, 1, 1)`.  Stage 1 is shared
verbatim between the two bridge sides (both are over the literal `s2Frame h2 hq`). -/
theorem s2DepthTwo_stage1 :
    (s2DepthTwo h2 hq).e 1 = 2 ∧ (s2DepthTwo h2 hq).f 1 = 1 ∧ (s2DepthTwo h2 hq).u 1 = 1 :=
  ⟨rfl, rfl, rfl⟩

/-- Stage-2 data as numerals: `(e₂, f₂, u₂) = (2, 1, 5)`. -/
theorem s2DepthTwo_stage2 :
    (s2DepthTwo h2 hq).e 2 = 2 ∧ (s2DepthTwo h2 hq).f 2 = 1 ∧ (s2DepthTwo h2 hq).u 2 = 5 :=
  ⟨rfl, rfl, rfl⟩

/-! ## 2. The `(e, f, u)` bridge -/

/-- **Bridge, `e`**: the truncation's stage-2 ramification index is `s2Tower`'s `e₂`. -/
theorem s2Bridge_e : (s2DepthTwo h2 hq).e 2 = (s2Tower h2 hq).e₂ := rfl

/-- **Bridge, `f`**: the truncation's stage-2 residual degree is `s2Tower`'s `f₂`. -/
theorem s2Bridge_f : (s2DepthTwo h2 hq).f 2 = (s2Tower h2 hq).f₂ := rfl

/-- **Bridge, `u`**: the truncation's stage-2 height is `s2Tower`'s `u₂`. -/
theorem s2Bridge_u : (s2DepthTwo h2 hq).u 2 = (s2Tower h2 hq).u₂ := rfl

/-! ## 3. The `ψ` and `step` bridge

`(s2DepthTwo h2 hq).fld 1` is definitionally the frame's stage field, so the equality
`ψ 1 = ψ₂` is well-typed as stated — that this elaborates is itself part of the bridge. -/

/-- **Bridge, `ψ`**: the truncation's live residual `ψ 1` is `s2Tower`'s inner residual `ψ₂`
(both `T − 1` over the stage field `K₁`). -/
theorem s2Bridge_ψ : (s2DepthTwo h2 hq).ψ 1 = (s2Tower h2 hq).ψ₂ := rfl

/-- **Bridge, `step`**: the truncation's live `step` datum, retyped against
`AdjoinRoot ((s2Tower h2 hq).ψ₂)`.  The body is EXACTLY the tower's own `step 1` — the
content is that this retyping typechecks, which is the ψ-bridge at the type level. -/
noncomputable def s2BridgeStep :
    (s2DepthTwo h2 hq).fld 2 ≃+* AdjoinRoot ((s2Tower h2 hq).ψ₂) :=
  (s2DepthTwo h2 hq).step 1 (by omega) (by omega)

/-- Anti-drift pin: `s2BridgeStep` invents no new equivalence — it IS the truncated witness's
own `step` at the unique live rung. -/
theorem s2BridgeStep_eq_step :
    s2BridgeStep h2 hq = (s2DepthTwo h2 hq).step 1 (by omega) (by omega) := rfl

/-- The step term pinned: it is the canonical `X − C 1` quotient equivalence that C.97
installed (`K₁ ≃+* K₁[T]⧸(T − 1)`, inverted). -/
theorem s2BridgeStep_canonical :
    s2BridgeStep h2 hq =
      (Polynomial.quotientSpanXSubCAlgEquiv
        (1 : (s2Frame h2 hq).stageField 1 (s2Frame_pin h2 hq))).toRingEquiv.symm := rfl

/-! ## 4. The bookkeeping bridge — `Dcum` vs `D₂`, `Econst` vs `E₂` -/

/-- `D₁ = e₁f₁ = 2` at the truncation. -/
theorem s2DepthTwo_Dcum_one : (s2DepthTwo h2 hq).Dcum 1 = 2 := by
  rw [DeepTower.Dcum, show (Finset.Icc 1 1 : Finset ℕ) = {1} by decide,
    Finset.prod_singleton, (s2DepthTwo h2 hq).he1, (s2DepthTwo h2 hq).hf1]
  rfl

/-- `D₂ = (e₁f₁)(e₂f₂) = 4` at the truncation. -/
theorem s2DepthTwo_Dcum_two : (s2DepthTwo h2 hq).Dcum 2 = 4 := by
  rw [DeepTower.Dcum, show (Finset.Icc 1 2 : Finset ℕ) = {1, 2} by decide,
    Finset.prod_insert (by decide), Finset.prod_singleton,
    (s2DepthTwo h2 hq).he1, (s2DepthTwo h2 hq).hf1]
  rfl

/-- **Bridge, degrees**: the truncation's cumulative degree `Dcum 2` is `s2Tower`'s composed
degree `D₂` (both `4`) — the equation the key-chain degree law runs through. -/
theorem s2Bridge_Dcum : (s2DepthTwo h2 hq).Dcum 2 = (s2Tower h2 hq).D₂ := by
  rw [s2DepthTwo_Dcum_two]
  show (4 : ℕ) = (s2Frame h2 hq).e₁ * (s2Frame h2 hq).f₁ * (2 * 1)
  rw [e1_eq h2 hq, f1_eq h2 hq]

/-- **Bridge, side constants**: the truncation's stage-2 side constant `Econst 2 = e₂f₂u₂` is
`s2Tower`'s `E₂` (both `10`). -/
theorem s2Bridge_Econst : (s2DepthTwo h2 hq).Econst 2 = (s2Tower h2 hq).E₂ := rfl

/-! ## 5. The promoted key chain — OPEN-DICT-1's depth-two instance (design §6) -/

/-- The S2 depth-two polynomial key chain: the frame key `Φ′ = x² − 2` at level 1, the
wrap-corrected composed key `Φ₂ = composedKey (s2Tower h2 hq)` (C.43) at level 2; junk at
every other index (nothing reads it — `KeyChain`'s laws are `StageLive`-fenced except
`keyAt_one`, which reads exactly the level-1 value). -/
noncomputable def s2DepthTwoKeyAt (i : ℕ) : Polynomial O :=
  if i = 1 then (s2Frame h2 hq).key else composedKey (s2Tower h2 hq)

/-- Level 1 of the chain is the frame key. -/
theorem s2DepthTwoKeyAt_one : s2DepthTwoKeyAt h2 hq 1 = (s2Frame h2 hq).key := rfl

/-- Level 2 of the chain is C.43's wrap-corrected composed key at `s2Tower`. -/
theorem s2DepthTwoKeyAt_two : s2DepthTwoKeyAt h2 hq 2 = composedKey (s2Tower h2 hq) := rfl

/-- ★ **NODE CC-2 — the promoted S2 depth-two `KeyChain`** (design §6's structural
non-vacuity check, now against the LANDED C.130k structure).  All four fields are discharged
with no `sorry` and no axiom: `keyAt_one` by definition; monicity at level 1 from the frame,
at level 2 from C.47's `composedKey_monic`; the `Dcum` degree law at level 1 from the frame's
`hdeg` (`deg Φ′ = e₁f₁ = Dcum 1`), at level 2 from C.53b's `composedKey_natDegree_D₂`
(`deg Φ₂ = D₂`) through the bridge `s2Bridge_Dcum` (`D₂ = Dcum 2`). -/
noncomputable def s2DepthTwoKeyChain : KeyChain (s2DepthTwo h2 hq) where
  keyAt := s2DepthTwoKeyAt h2 hq
  keyAt_one := s2DepthTwoKeyAt_one h2 hq
  keyAt_monic := by
    intro i hi
    obtain ⟨hi1, hi2⟩ := hi
    interval_cases i
    · simpa [s2DepthTwoKeyAt] using (s2Frame h2 hq).hmonic
    · simpa [s2DepthTwoKeyAt] using composedKey_monic (s2Tower h2 hq)
  keyAt_degree := by
    intro i hi
    obtain ⟨hi1, hi2⟩ := hi
    interval_cases i
    · rw [s2DepthTwoKeyAt_one h2 hq, (s2Frame h2 hq).hdeg, s2DepthTwo_Dcum_one h2 hq,
        e1_eq h2 hq, f1_eq h2 hq]
    · rw [s2DepthTwoKeyAt_two h2 hq, composedKey_natDegree_D₂ (s2Tower h2 hq) h2,
        ← s2Bridge_Dcum h2 hq]

end Uniformity.Density.Tower.C130s2

/-! ## Teeth — the §6 regression numerals, read off the promoted chain

The chain's two live degrees are the S2 numerals `2` and `4`, and the level-2 degree agrees
with `s2Tower`'s `D₂` — the checks design §6 calls "the non-vacuity check for the structural
front". -/

section Teeth

open IsLocalRing Uniformity.Density Uniformity.Density.Tower
open Uniformity.Density.Tower.C80 Uniformity.Density.Tower.C130s2

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)] (h2 : Irreducible (2 : O)) (hq : residueCard O = 2)

example : ((s2DepthTwoKeyChain h2 hq).keyAt 1).natDegree = 2 :=
  ((s2DepthTwoKeyChain h2 hq).keyAt_degree 1 ⟨le_refl 1, by omega⟩).trans
    (s2DepthTwo_Dcum_one h2 hq)

example : ((s2DepthTwoKeyChain h2 hq).keyAt 2).natDegree = 4 :=
  ((s2DepthTwoKeyChain h2 hq).keyAt_degree 2 ⟨by omega, le_refl 2⟩).trans
    (s2DepthTwo_Dcum_two h2 hq)

example : ((s2DepthTwoKeyChain h2 hq).keyAt 2).natDegree = (s2Tower h2 hq).D₂ :=
  ((s2DepthTwoKeyChain h2 hq).keyAt_degree 2 ⟨by omega, le_refl 2⟩).trans
    (s2Bridge_Dcum h2 hq)

end Teeth

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Tower.C130s2.s2DepthTwo
#print axioms Uniformity.Density.Tower.C130s2.s2DepthTwo_eq_trunc
#print axioms Uniformity.Density.Tower.C130s2.s2DepthTwo_stage1
#print axioms Uniformity.Density.Tower.C130s2.s2DepthTwo_stage2
#print axioms Uniformity.Density.Tower.C130s2.s2Bridge_e
#print axioms Uniformity.Density.Tower.C130s2.s2Bridge_f
#print axioms Uniformity.Density.Tower.C130s2.s2Bridge_u
#print axioms Uniformity.Density.Tower.C130s2.s2Bridge_ψ
#print axioms Uniformity.Density.Tower.C130s2.s2BridgeStep
#print axioms Uniformity.Density.Tower.C130s2.s2BridgeStep_eq_step
#print axioms Uniformity.Density.Tower.C130s2.s2BridgeStep_canonical
#print axioms Uniformity.Density.Tower.C130s2.s2DepthTwo_Dcum_one
#print axioms Uniformity.Density.Tower.C130s2.s2DepthTwo_Dcum_two
#print axioms Uniformity.Density.Tower.C130s2.s2Bridge_Dcum
#print axioms Uniformity.Density.Tower.C130s2.s2Bridge_Econst
#print axioms Uniformity.Density.Tower.C130s2.s2DepthTwoKeyAt
#print axioms Uniformity.Density.Tower.C130s2.s2DepthTwoKeyAt_one
#print axioms Uniformity.Density.Tower.C130s2.s2DepthTwoKeyAt_two
#print axioms Uniformity.Density.Tower.C130s2.s2DepthTwoKeyChain

end AxCheck
