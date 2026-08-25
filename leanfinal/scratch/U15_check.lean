/-
U15 — packaging-route elaboration checks (Route A: retype the packaging).
Scratch authority for `docs/in-progress/PACKAGING_ROUTE_2026-08-25.md`.
No sorry, no axiom, no corpus edit.  Run: `lake env lean scratch/U15_check.lean`.

Contents:
  §1 the parameter adjudication numerals (machine pins for the (2,1,5)-vs-(2,1,21) finding);
  §2 the refactored FGMN packaging map (`fgmnCalculusOf`) and ★ the first NON-VACUOUS class
     discharge `Nonempty (FGMNCalculus (s2DepthOne h2 hq) 2 1 5)` — unconditional, ev/lf-free;
  §3 the proposed retyped carrier (`ChainRealizationV2`: node-side only, split ambient,
     no (e',f',u') parameters) + its S2 inhabitation from the SG-0 frontier with NO
     LegacyEvaluation and NO LegacyFGMN premise, and the V2 `RealizedInput` twin.
-/
import Uniformity.ChapC.C130sg

set_option linter.style.longLine false

noncomputable section

namespace U15Check

open Polynomial IsLocalRing IsDiscreteValuationRing Uniformity.Density
open Uniformity.Density.Leaf Uniformity.Density.Tower
open Uniformity.Density.Tower.C130s2 Uniformity.Density.Tower.C130s6
open Uniformity.Density.Tower.C130s17 Uniformity.Density.Tower.C130s18
open Uniformity.Density.Tower.C130fd0 Uniformity.Density.Tower.C130sg
open Uniformity.Density.Tower.C130rp6
open Uniformity.Density.Tower.C130kp0 Uniformity.Density.Tower.C130rp8

universe uE uG uKt uL

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
variable {π : O}

section Numerals

variable [Finite (ResidueField O)] (h2 : Irreducible (2 : O)) (hq : residueCard O = 2)

/-! ## §1 The parameter adjudication numerals

The landed witness's stage data: `(e,f,u) = (2,1,1), (2,1,5), (2,1,21)`.  Per U9 Q1 (the
class at repo depth `r` is the calculus of the NEXT augmentation, data `(e_{r+1}, f_{r+1},
u_{r+1})`), the honest class parameters are `(2,1,5)` at DEPTH 1 and `(2,1,21)` at DEPTH 2.
The depth-2 consumers' own floor hypothesis (`gentow5w_two`/`gentow2_Bpp` `hfloor :
e' * W.Econst 2 < u'`; `gentow2_A` `hκ : e₂f₂u₂ < u'`) REJECTS `u' = 5` and ACCEPTS
`u' = 21`; the depth-1 floor accepts `(2,1,5)`. -/

example : (s2Witness h2 hq 1 (s2Frame_pin h2 hq)).u 2 = 5 := rfl
example : (s2Witness h2 hq 1 (s2Frame_pin h2 hq)).u 3 = 21 := rfl

/-- the depth-2 floor constant: `Econst 2 = e₂f₂u₂ = 10`. -/
theorem s2DepthTwo_Econst_two : (s2DepthTwo h2 hq).Econst 2 = 10 := rfl

/-- the depth-1 floor constant: `Econst 1 = e₁f₁u₁ = 2`. -/
theorem s2DepthOne_Econst_one : (s2DepthOne h2 hq).Econst 1 = 2 := rfl

/-- ★ the depth-2 consumer floor REJECTS the CC-17 parameter choice `u' = 5`. -/
theorem depthTwo_floor_rejects_five : ¬ (2 * (s2DepthTwo h2 hq).Econst 2 < 5) := by
  rw [s2DepthTwo_Econst_two]; omega

/-- ★ the depth-2 consumer floor ACCEPTS the honest next-augmentation value `u₃ = 21`. -/
theorem depthTwo_floor_accepts_u3 : 2 * (s2DepthTwo h2 hq).Econst 2 < 21 := by
  rw [s2DepthTwo_Econst_two]; omega

/-- the depth-1 consumer floor accepts `(2,1,5)` — the landed records' typing. -/
theorem depthOne_floor_accepts_five : 2 * (s2DepthOne h2 hq).Econst 1 < 5 := by
  rw [s2DepthOne_Econst_one]; omega

/-- both candidate `u'` values satisfy the consumers' coprimality leg. -/
example : Nat.Coprime 5 2 ∧ Nat.Coprime 21 2 := by decide

/-- FLAG (not resolved here): the landed `PrevGrade` realization (RP-6's evenness) rejects
BOTH odd `u'` values, so `hprev : I.PrevGrade u'` is unsatisfiable at any evenness-realized
instance — the consumer supply's clearing question (U14 §8.1 / OPEN-DICT-2), recorded for
the review list. -/
example : ¬ S2PrevGrade 5 ∧ ¬ S2PrevGrade 21 := by
  constructor <;> · intro ⟨k, hk⟩; omega

end Numerals

/-! ## §2 The refactored packaging map (PK-B shape) and ★ the class discharge

CC-16's `toCalculus` never consumed the carrier's `node`, `receiver`, `normalizer`,
`grade_compat`, or `letter_compat` — only `keys`, `fgmn`, `fgmnLaws`.  So the class
packaging factors through the FGMN pair alone; this is that factored map, field-for-field
the C130pk projection. -/

/-- The design-§7 projection map, factored through the FGMN pair (no carrier needed):
every A-C.11 field is filled from `FGMNSourceData` + `FGMNSourceLaws` + the key chain.
Deliberately a `def`, not an `instance` (C130pk's rule: no silent binder satisfaction). -/
@[implicit_reducible] def fgmnCalculusOf {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀}
    {r : ℕ} {W : DeepTower.{0, uKt} F H₀ hpin r} (K : KeyChain W) {e' f' u' : ℕ}
    (S : FGMNSourceData W K e' f' u') (hL : FGMNSourceLaws W K e' f' u' S) :
    FGMNCalculus W e' f' u' where
  keyAt := K.keyAt
  keyAt_one := K.keyAt_one
  keyAt_deg := fun i hi hir => K.keyAt_degree i ⟨hi, hir⟩
  ExactGrade := S.ExactGrade
  AboveGrade := S.AboveGrade
  PrevGrade := S.PrevGrade
  Rgr := S.Rgr
  Rres := S.normalizedResidual
  KP := S.keyPolynomial
  nuEquiv := S.initialEquiv
  letterZ := S.letter
  Rgr_zero_of_above := hL.Rgr_zero_of_above
  Rgr_add := hL.Rgr_add
  Rgr_mul := hL.Rgr_mul
  Rgr_ne_zero := hL.Rgr_ne_zero
  Rres_mul := hL.Rres_mul
  Rres_recipe := hL.Rres_recipe
  Rres_exists := hL.Rres_exists
  KP_criterion := hL.KP_criterion
  KP_irred := hL.KP_irred
  KP_keyAt := hL.KP_keyAt
  Rres_keyAt := hL.Rres_keyAt
  nuEquiv_iff_Rres := hL.nuEquiv_iff_Rres
  letterZ_ne_zero := hL.letterZ_ne_zero

section Discharge

variable [Finite (ResidueField O)] (h2 : Irreducible (2 : O)) (hq : residueCard O = 2)

/-- ★★ **the first non-vacuous `FGMNCalculus` instance** — the landed FD-0 records
(`s2SourceDataOne`/`s2SourceLawsOne`, all thirteen laws by named landed theorems) packaged
at the honest `r = 1` anchoring.  UNCONDITIONAL (no `w`, no `ev`, no `lf`). -/
@[implicit_reducible] def s2AnchorCalculus : FGMNCalculus (s2DepthOne h2 hq) 2 1 5 :=
  fgmnCalculusOf (s2DepthOneKeyChain h2 hq) (s2SourceDataOne h2 hq)
    (s2SourceLawsOne h2 hq)

/-- ★★ **the class discharge, non-vacuous and unconditional** — what SG-1's
`calculusNonempty` could only state behind the provably-empty `ev`/`lf` premises. -/
theorem s2_calculus_discharge :
    Nonempty (FGMNCalculus (s2DepthOne h2 hq) 2 1 5) :=
  ⟨s2AnchorCalculus h2 hq⟩

/-- anti-drift: the discharged instance's operators ARE the landed S2 operators. -/
example : (s2AnchorCalculus h2 hq).Rres = s2NormRes h2 hq := rfl
example : (s2AnchorCalculus h2 hq).KP = S2KeyPoly h2 hq := rfl

end Discharge

/-! ## §3 The retyped carrier (PK-A shape) and its S2 inhabitation, `ev`/`lf`-FREE

`ChainRealizationV2`: the node-side carrier only — receiver, keys, normalizer, and the
SPLIT node.  The FGMN legs and the `(e',f',u')` parameters are GONE (they fed only
`toCalculus`, now factored as §2's `fgmnCalculusOf`; the socket views never consumed them
— verified: no `fgmn`/`coeffHom`/`valueOn`/`pointHgt_eval` occurrence in
C130vw/C130ar/C130pt/C130st).  The evaluation ambient `E` is a parameter here (the
enacting node may instead bundle it as a field; both elaborate — see V2b below). -/

section CarrierV2

variable {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀} {r : ℕ}

/-- The proposed SF-3 carrier: node-side only, split-ambient, parameter-free in
`(e',f',u')`. -/
structure ChainRealizationV2 (W : DeepTower.{0, uKt} F H₀ hpin r)
    (Kt : Type uKt) [Field Kt] (E : Type uE) [Field E]
    (L : Type uL) [Field L] [Algebra Kt L] where
  receiver : TerminalReceiver F H₀ hpin r W Kt
  keys : KeyChain W
  normalizer : LaurentNormalizer W
  node : SplitNodePointSource (L := L) W E receiver keys

/-- Variant with the evaluation ambient as a FIELD (arity-stable at consumers); the
enacting node picks one of the two shapes. -/
structure ChainRealizationV2b (W : DeepTower.{0, uKt} F H₀ hpin r)
    (Kt : Type uKt) [Field Kt] (L : Type uL) [Field L] [Algebra Kt L] where
  receiver : TerminalReceiver F H₀ hpin r W Kt
  keys : KeyChain W
  normalizer : LaurentNormalizer W
  E : Type uE
  [fieldE : Field E]
  node : SplitNodePointSource (L := L) W E receiver keys

end CarrierV2

/-- The `RealizedInput` twin at the V2 carrier — fields byte-parallel to C130in's
(none of them touched the FGMN legs or the evaluation ambient). -/
structure RealizedInputV2 {Kt : Type uKt} [Field Kt] {E : Type uE} [Field E]
    {L : Type uL} [Field L] [Algebra Kt L] {n : ℕ}
    (core : ArisingCore (O := O) Kt L n)
    (A : ChainRealizationV2 (O := O) (π := core.π) (F := core.F)
      (H₀ := core.H₀) (hpin := core.hpin) core.T Kt E L) where
  receiver_eq : A.receiver = core.receiver
  stageKey_eq : core.stageKey = A.keys.keyAt core.i
  stageDeg_eq : core.stageDeg = core.T.Dcum core.i
  point : A.node.Point
  point_mem : A.node.Pt core.i point

section S2V2

variable [Finite (ResidueField O)] (h2 : Irreducible (2 : O)) (hq : residueCard O = 2)
variable (L : Type uL) [Field L] [Algebra ((S2DepthTwo h2 hq).fld 2) L]

/-- ★★ **the S2 V2 carrier, inhabited with NO quarantined premise**: the SG-0 frontier's
split node slots in directly — no `LegacyEvaluation`, no `LegacyFGMN`.  Conditional on
exactly the one open source datum `w` (the level-1 threshold), like the frontier itself. -/
def s2CarrierV2 (w : S2LevelOneThreshold) :
    ChainRealizationV2 (S2DepthTwo h2 hq) ((S2DepthTwo h2 hq).fld 2)
      (FractionRing (Polynomial O)) L where
  receiver := (s2RepositoryRealization h2 hq).receiver
  keys := (s2RepositoryRealization h2 hq).keys
  normalizer := (s2RepositoryRealization h2 hq).normalizer
  node := (s2Frontier h2 hq L w).node

/-- ★★ **the S2 V2 realized input, `ev`/`lf`-free**: the concrete `keyAt 2 + 1` arising
occurrence realized on the V2 carrier — SG-1 stage 3 with both quarantined premises
DELETED. -/
def s2RealizedInputV2 [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    (w : S2LevelOneThreshold) :
    RealizedInputV2 (s2ArisingCore h2 hq L) (s2CarrierV2 h2 hq L w) where
  receiver_eq := rfl
  stageKey_eq := rfl
  stageDeg_eq := rfl
  point := (s2Frontier h2 hq L w).point
  point_mem := (s2Frontier h2 hq L w).point_mem

/-- the V2 carrier still derives the level-two slot carrier (the socket views' feedstock)
through the landed split `stageCarrier` — the view layer's inputs are all present. -/
example (w : S2LevelOneThreshold) :
    Ladder.SlotCarrier O ((S2DepthTwo h2 hq).fld 2) :=
  (s2CarrierV2 h2 hq L w).node.stageCarrier 2 ⟨by decide, by decide⟩

end S2V2

end U15Check

end

section AxCheck

#print axioms U15Check.fgmnCalculusOf
#print axioms U15Check.s2AnchorCalculus
#print axioms U15Check.s2_calculus_discharge
#print axioms U15Check.depthTwo_floor_rejects_five
#print axioms U15Check.depthTwo_floor_accepts_u3
#print axioms U15Check.depthOne_floor_accepts_five
#print axioms U15Check.ChainRealizationV2
#print axioms U15Check.ChainRealizationV2b
#print axioms U15Check.RealizedInputV2
#print axioms U15Check.s2CarrierV2
#print axioms U15Check.s2RealizedInputV2

end AxCheck
