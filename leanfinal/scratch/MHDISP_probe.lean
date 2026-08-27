import Uniformity.ChapC.C35
import Uniformity.ChapC.C130nv3
import Uniformity.ChapC.C131f
import Uniformity.ChapC.C132nv3
import Uniformity.ChapC.C141defs

/-!
# MHDISP probe

Zero-`sorry`, zero-`axiom` checks used by the 2026-08-27 disposition of `verdict_VHENS`.
The declarations below check:

* the current A-C.20 C.34/C.35 degree-pinned signatures and the historical `*Leaky` names;
* the generic C130nv3 endpoint theorem's explicit survival premise and the landed S2-only
  survival theorem in C132nv3;
* the public C131f lift pins and C.14 exact-`twistRead` preimage API;
* local reconstruction of the intentionally non-global stage-field `Field` structure; and
* the `(e₁,f₁,h)=(2,2,3)` slot-window carry: bare slot reads are not multiplicative, while
  the C.22 inverse-twist normalization cancels the carry in the executable `F9` gate model.
-/

set_option linter.style.longLine false

namespace MHDISPCheck

open Polynomial IsLocalRing IsDiscreteValuationRing Uniformity.Density
open Uniformity.Density.Leaf Uniformity.Density.Tower
open Uniformity.Density.Weld

#check Uniformity.Density.Tower.exists_dv_residual_dissection_of_frontier
#check Uniformity.Density.Tower.blockFactorLeaky
#check Uniformity.Density.Tower.mult₂Leaky
#check Uniformity.Density.Tower.blockFactor
#check Uniformity.Density.Tower.mult₂
#check Uniformity.Density.Tower.BlockFrontier
#check Uniformity.Density.Tower.C130nv3.stageHeight_dev_endpoint_le_of_surv
#check Uniformity.Density.Tower.C132nv3.s2_dvSupp_mul_modByComposedKey_le
#check Uniformity.Density.Tower.KeyFrame.natDegree_stageLiftO_lt
#check Uniformity.Density.Tower.KeyFrame.slotRes_stageLiftO
#check Uniformity.Density.Tower.KeyFrame.stageHeight_stageLiftO
#check Uniformity.Density.Tower.KeyFrame.exists_twistRead_preimage

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {π : O}

/-- The current `BlockFrontier` maximality competitor is degree-pinned. -/
theorem blockFrontier_current_pin {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀}
    (L : LevelDatum F H₀ hpin) (f : Polynomial O) (h : BlockFrontier L f) :
    ∃ fS : Polynomial O, HasLabel L fS ∧ fS ∣ f ∧
      (F.e₁ * F.f₁) ∣ fS.natDegree ∧
      ∀ fS' : Polynomial O,
        (HasLabel L fS' ∧ (F.e₁ * F.f₁) ∣ fS'.natDegree) → fS' ∣ f → fS' ∣ fS :=
  h

/-- Local D9 reconstruction used by consumers; C.04 deliberately exports no global instance. -/
private theorem isKey_X : IsKey (Polynomial.X : Polynomial O) where
  monic := Polynomial.monic_X
  pos := by simp
  irred := by
    simpa using (Polynomial.irreducible_X (R := IsLocalRing.ResidueField O))

@[reducible] noncomputable def localFieldStageField (F : KeyFrame O π) (H₀ : ℕ)
    (hpin : F.Pin H₀) : Field (F.stageField H₀ hpin) :=
  letI : Field (resField (Polynomial.X : Polynomial O)) := instFieldResField isKey_X
  haveI : Fact (Irreducible (F.frameRes H₀ hpin)) := ⟨(F.hresirr H₀ hpin).1⟩
  AdjoinRoot.instField

example (F : KeyFrame O π) (H₀ : ℕ) (hpin : F.Pin H₀) :
    Nonempty (Field (F.stageField H₀ hpin)) :=
  ⟨localFieldStageField F H₀ hpin⟩

/-- The public exact-`twistRead` lift is consumable without naming C.46/C.47 private helpers. -/
example [Finite (ResidueField O)] (hπ : Irreducible π) (F : KeyFrame O π)
    (H₀ : ℕ) (hpin : F.Pin H₀) {M : ℕ} (hM : F.e₁ * F.f₁ * F.h < M)
    {c : F.stageField H₀ hpin} (hc : c ≠ 0) :
    ∃ B : Polynomial O, B.natDegree < F.e₁ * F.f₁ ∧
      F.stageHeight B = (M : ℕ∞) ∧ F.twistRead H₀ hpin M B = c :=
  F.exists_twistRead_preimage hπ H₀ hpin hM hc

/-- The explicit C131f route gives the same exact twist lift without a finiteness instance. -/
theorem exists_explicit_twist_lift (hπ : Irreducible π) (F : KeyFrame O π)
    (H₀ : ℕ) (hpin : F.Pin H₀) {M : ℕ} (hM : F.e₁ * F.f₁ * F.h < M)
    {c : F.stageField H₀ hpin} (hc : c ≠ 0) :
    ∃ B : Polynomial O, B.natDegree < F.e₁ * F.f₁ ∧
      F.stageHeight B = (M : ℕ∞) ∧ F.twistRead H₀ hpin M B = c := by
  classical
  letI : Field (F.stageField H₀ hpin) := localFieldStageField F H₀ hpin
  set eta : F.stageField H₀ hpin := F.stageLetter H₀ hpin with heta
  have heta0 : eta ≠ 0 := F.stageLetter_ne_zero hπ H₀ hpin
  have htarget : eta ^ F.twistExp M * c ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ heta0) hc
  refine ⟨F.stageLiftO H₀ hpin M (eta ^ F.twistExp M * c),
    F.natDegree_stageLiftO_lt H₀ hpin M _,
    F.stageHeight_stageLiftO hπ H₀ hpin hM htarget, ?_⟩
  rw [KeyFrame.twistRead, F.slotRes_stageLiftO hπ H₀ hpin hM, ← heta, inv_pow]
  field_simp

/-! ## Executable carry check

This is the relevant specialization of C.21's displayed `slotRes` sum for coefficients that
are either zero or units at their live slot.  It uses the repository's numeral mirrors
`slotIdxN`/`slotWindowN` and its table-built `F9`, where `eta = (0,1)` and `eta^2 = -1`.
-/

private def eta : F9 := (0, 1)

private def embedF3 (x : ZMod 3) : F9 := (x, 0)

private def coeffX (n : ℕ) : ZMod 3 := if n = 1 then 1 else 0

private def coeffX2 (n : ℕ) : ZMod 3 := if n = 2 then 1 else 0

private def bareSlotRead (k : ℕ) (coeff : ℕ → ZMod 3) : F9 :=
  ((slotWindowN 2 2 3 k).map fun t =>
      embedF3 (coeff (slotIdxN 2 3 k + 2 * t)) * eta ^ t).sum

private def twistReadModel (k : ℕ) (coeff : ℕ → ZMod 3) : F9 :=
  eta⁻¹ ^ (twistExpN 2 3 k) * bareSlotRead k coeff

example : slotIdxN 2 3 3 = 1 := by decide
example : slotIdxN 2 3 6 = 0 := by decide
example : slotWindowN 2 2 3 3 = [0] := by decide
example : slotWindowN 2 2 3 6 = [0, 1] := by decide
example : twistExpN 2 3 3 = 1 := by decide
example : twistExpN 2 3 6 = 3 := by decide

example : bareSlotRead 3 coeffX = 1 := by decide
example : bareSlotRead 6 coeffX2 = eta := by decide

/-- M1(2)'s bare equality specializes to a false equality: `eta != 1 * 1`. -/
theorem bare_slot_product_fails :
    bareSlotRead 6 coeffX2 ≠ bareSlotRead 3 coeffX * bareSlotRead 3 coeffX := by
  decide

/-- The landed inverse-twist exponents cancel that carry in the same model. -/
theorem twist_slot_product_holds :
    twistReadModel 6 coeffX2 = twistReadModel 3 coeffX * twistReadModel 3 coeffX := by
  decide

end MHDISPCheck

section AxCheck

#print axioms MHDISPCheck.blockFrontier_current_pin
#print axioms MHDISPCheck.localFieldStageField
#print axioms MHDISPCheck.exists_explicit_twist_lift
#print axioms MHDISPCheck.bare_slot_product_fails
#print axioms MHDISPCheck.twist_slot_product_holds

end AxCheck
