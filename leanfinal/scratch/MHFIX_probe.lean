import Uniformity.ChapC.C35
import Uniformity.ChapC.C130nv3
import Uniformity.ChapC.C131f
import Uniformity.ChapC.C141defs

/-!
# MHFIX probe (2026-08-27) — the CORRECTED Theorem M root

Companion to the [MHFIX 2026-08-27] amendment of
`docs/in-progress/HENSEL_ENGINE_2026-08-26.md` and `verification/mhfix_cert.py`
(473,961 checks, 0 fails).  Zero `sorry`, zero `axiom`.  Contents:

* **PROVED, generic:** `twistExp_add_carry` — the TW-δ cocycle arithmetic
  `q(k) + q(k') + δ = q(k+k')` with `e₁·δ = i(k) + i(k') − i(k+k')` and `δ ≤ 1`,
  from C.16's `slotIdx_spec`/`twistExp_spec` alone.  This is the exponent law of the
  slot carry that refuted M1(2).
* **PROVED, generic:** `twistRead_mul_of_slotRes_carry` — the slot-carry form of the
  corrected M1 implies the twist-read product form (the C.22 inverse twist cancels the
  carry `η^δ` exactly).
* **STATEMENT SHAPES** (C35b `D13Statement` pattern, no assertion): the corrected M1
  twist/carry/faithfulness laws and the τ = 1 mixed residual law, plus a PROVED
  implication to the MHENS-probe's ∃-τ shape (τ := 1).
* **Executable teeth** at the `(e₁,f₁,h) = (2,2,3)`/`F₉` gate model: the δ = 1 carry
  row `(3,3)` (the MHDISP refutation pair, now as an INSTANCE of the carry law) and a
  δ = 0 contrast row `(6,3)`; numeral-mirror δ-grids at `(e₁,h) = (2,3), (3,2), (5,3)`.
-/

set_option linter.style.longLine false

namespace MHFIXCheck

open Polynomial IsLocalRing IsDiscreteValuationRing Uniformity.Density
open Uniformity.Density.Leaf Uniformity.Density.Tower
open Uniformity.Density.Weld

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {π : O}

/-- ★ **PROVED — TW-δ, the twist-exponent cocycle** (the generic exponent law behind the
slot carry): `q(k) + q(k') + δ = q(k + k')` for a δ ∈ {0,1} that is exactly the slot-index
carry bit, `e₁·δ = i(k) + i(k') − i(k+k')`.  Pure ℕ arithmetic from C.16's specs. -/
theorem twistExp_add_carry (F : KeyFrame O π) (k k' : ℕ) :
    ∃ δ : ℕ, δ ≤ 1 ∧
      F.twistExp k + F.twistExp k' + δ = F.twistExp (k + k') ∧
      F.slotIdx k + F.slotIdx k' = F.slotIdx (k + k') + F.e₁ * δ := by
  have h1 := F.twistExp_spec k
  have h2 := F.twistExp_spec k'
  have h3 := F.twistExp_spec (k + k')
  have hi1 := (F.slotIdx_spec k).1
  have hi2 := (F.slotIdx_spec k').1
  have hi3 := (F.slotIdx_spec (k + k')).1
  have he := F.he₁
  have hadd : F.slotIdx 1 * (k + k') = F.slotIdx 1 * k + F.slotIdx 1 * k' :=
    Nat.mul_add _ _ _
  -- the E-scaled key identity: i₁ + i₂ + (e₁q₁ + e₁q₂) = i₃ + e₁q₃
  have hkey : F.slotIdx k + F.slotIdx k' + (F.e₁ * F.twistExp k + F.e₁ * F.twistExp k')
      = F.slotIdx (k + k') + F.e₁ * F.twistExp (k + k') := by omega
  rcases Nat.le_total (F.twistExp k + F.twistExp k') (F.twistExp (k + k')) with hle | hgt
  · obtain ⟨δ, hδ⟩ := Nat.exists_eq_add_of_le hle
    have hsplit : F.e₁ * F.twistExp (k + k')
        = F.e₁ * F.twistExp k + F.e₁ * F.twistExp k' + F.e₁ * δ := by
      rw [hδ, Nat.mul_add, Nat.mul_add]
    refine ⟨δ, ?_, hδ.symm, by omega⟩
    by_contra h2le
    have h2le' : 2 ≤ δ := by omega
    have h2E : F.e₁ * 2 ≤ F.e₁ * δ := Nat.mul_le_mul (Nat.le_refl F.e₁) h2le'
    omega
  · -- q₃ ≤ q₁ + q₂ forces equality: a strict gap would put e₁ ≤ i₃, against C.16(i)
    obtain ⟨ε, hε⟩ := Nat.exists_eq_add_of_le hgt
    have hsplit : F.e₁ * F.twistExp k + F.e₁ * F.twistExp k'
        = F.e₁ * F.twistExp (k + k') + F.e₁ * ε := by
      rw [← Nat.mul_add, hε, Nat.mul_add]
    have hε0 : ε = 0 := by
      by_contra hne
      have h1E : F.e₁ * 1 ≤ F.e₁ * ε :=
        Nat.mul_le_mul (Nat.le_refl F.e₁) (Nat.one_le_iff_ne_zero.mpr hne)
      omega
    subst hε0
    exact ⟨0, Nat.zero_le 1, by omega, by omega⟩

/-- Local D9 reconstruction (MHDISP finding 8 pattern); C.04 exports no global instance. -/
private theorem isKey_X : IsKey (Polynomial.X : Polynomial O) where
  monic := Polynomial.monic_X
  pos := by simp
  irred := by
    simpa using (Polynomial.irreducible_X (R := IsLocalRing.ResidueField O))

@[reducible] private noncomputable def localFieldStageField (F : KeyFrame O π) (H₀ : ℕ)
    (hpin : F.Pin H₀) : Field (F.stageField H₀ hpin) :=
  letI : Field (resField (Polynomial.X : Polynomial O)) := instFieldResField isKey_X
  haveI : Fact (Irreducible (F.frameRes H₀ hpin)) := ⟨(F.hresirr H₀ hpin).1⟩
  AdjoinRoot.instField

/-- ★ **PROVED — the twist normalization cancels the carry**: the slot-carry form of the
corrected M1 implies the twist-read product form, given the TW-δ exponent identity.  The
inverse-twist exponents absorb `η^δ` exactly; this is why the engine-facing law is
`τ = 1`. -/
theorem twistRead_mul_of_slotRes_carry (F : KeyFrame O π) (hπ : Irreducible π)
    (H₀ : ℕ) (hpin : F.Pin H₀) {E a b : Polynomial O} {ka kb δ : ℕ}
    (hq : F.twistExp ka + F.twistExp kb + δ = F.twistExp (ka + kb))
    (hcarry : F.slotRes H₀ hpin (ka + kb) E
      = F.stageLetter H₀ hpin ^ δ
        * (F.slotRes H₀ hpin ka a * F.slotRes H₀ hpin kb b)) :
    F.twistRead H₀ hpin (ka + kb) E
      = F.twistRead H₀ hpin ka a * F.twistRead H₀ hpin kb b := by
  letI : Field (F.stageField H₀ hpin) := localFieldStageField F H₀ hpin
  have hη := F.stageLetter_ne_zero hπ H₀ hpin
  rw [KeyFrame.twistRead, KeyFrame.twistRead, KeyFrame.twistRead, hcarry, ← hq,
    pow_add, pow_add, inv_pow, inv_pow, inv_pow]
  field_simp

/-! ## Statement shapes (Prop-valued defs; nothing asserted) -/

/-- ★ STATEMENT SHAPE — **the corrected M1 root, twist form** (replaces withdrawn M1(2)):
the ϖ-read is multiplicative on digit products modulo the key, at any height floors. -/
def M1TwistProductLawStatement (O : Type*) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] : Prop :=
  ∀ (π : O) (F : KeyFrame O π), Irreducible π → 0 < F.h →
  ∀ (H₀ : ℕ) (hpin : F.Pin H₀),
  ∀ a b : Polynomial O, a.natDegree < F.e₁ * F.f₁ → b.natDegree < F.e₁ * F.f₁ →
  ∀ ka kb : ℕ, (ka : ℕ∞) ≤ F.stageHeight a → (kb : ℕ∞) ≤ F.stageHeight b →
    F.twistRead H₀ hpin (ka + kb) ((a * b) %ₘ F.key)
      = F.twistRead H₀ hpin ka a * F.twistRead H₀ hpin kb b

/-- ★ STATEMENT SHAPE — **the corrected M1 root, slot-carry form**: bare slot reads
multiply up to the stage-letter carry `η^δ`, δ the TW-δ defect. -/
def M1SlotCarryLawStatement (O : Type*) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] : Prop :=
  ∀ (π : O) (F : KeyFrame O π), Irreducible π → 0 < F.h →
  ∀ (H₀ : ℕ) (hpin : F.Pin H₀),
  ∀ a b : Polynomial O, a.natDegree < F.e₁ * F.f₁ → b.natDegree < F.e₁ * F.f₁ →
  ∀ ka kb δ : ℕ, (ka : ℕ∞) ≤ F.stageHeight a → (kb : ℕ∞) ≤ F.stageHeight b →
    F.twistExp ka + F.twistExp kb + δ = F.twistExp (ka + kb) →
    F.slotRes H₀ hpin (ka + kb) ((a * b) %ₘ F.key)
      = F.stageLetter H₀ hpin ^ δ
        * (F.slotRes H₀ hpin ka a * F.slotRes H₀ hpin kb b)

/-- ★ STATEMENT SHAPE — **digit read faithfulness** (subsumes old M1(1) through the carry
law): a digit at exact finite height has a nonzero ϖ-read there. -/
def M1DigitFaithfulStatement (O : Type*) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] : Prop :=
  ∀ (π : O) (F : KeyFrame O π), Irreducible π → 0 < F.h →
  ∀ (H₀ : ℕ) (hpin : F.Pin H₀),
  ∀ a : Polynomial O, a.natDegree < F.e₁ * F.f₁ →
  ∀ ka : ℕ, F.stageHeight a = (ka : ℕ∞) →
    F.twistRead H₀ hpin ka a ≠ 0

/-- ★ STATEMENT SHAPE — **Theorem M clause 3, corrected: τ = 1** (the mixed residual
product law is EXACTLY multiplicative in the C.25 twist normalization). -/
def MixedResidualLawTauOneStatement (O : Type*) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] : Prop :=
  ∀ (π : O) (F : KeyFrame O π), Irreducible π → 0 < F.h →
  ∀ (H₀ : ℕ) (hpin : F.Pin H₀),
  ∀ u ℓ : ℕ, 0 < ℓ → Nat.Coprime u ℓ → ℓ * ((F.e₁ * F.f₁) * F.h) < u →
  ∀ g z : Polynomial O, g ≠ 0 → z ≠ 0 →
  ∀ (hng : (dvSideSet F g u ℓ).Nonempty) (hnz : (dvSideSet F z u ℓ).Nonempty)
    (hngz : (dvSideSet F (g * z) u ℓ).Nonempty) (Mg Mz Mgz : ℕ)
    (hpg : dvHgt F g (dvSideMin F g u ℓ hng) = (Mg : ℕ∞))
    (hpz : dvHgt F z (dvSideMin F z u ℓ hnz) = (Mz : ℕ∞))
    (hpgz : dvHgt F (g * z) (dvSideMin F (g * z) u ℓ hngz) = (Mgz : ℕ∞)),
    dvResPoly F H₀ hpin (g * z) u ℓ hngz Mgz hpgz
      = dvResPoly F H₀ hpin g u ℓ hng Mg hpg * dvResPoly F H₀ hpin z u ℓ hnz Mz hpz

/-- The MHENS-probe ∃-τ shape, restated here so the implication below is self-contained. -/
def MixedResidualLawExistsUnitStatement (O : Type*) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] : Prop :=
  ∀ (π : O) (F : KeyFrame O π), Irreducible π → 0 < F.h →
  ∀ (H₀ : ℕ) (hpin : F.Pin H₀),
  ∀ u ℓ : ℕ, 0 < ℓ → Nat.Coprime u ℓ → ℓ * ((F.e₁ * F.f₁) * F.h) < u →
  ∀ g z : Polynomial O, g ≠ 0 → z ≠ 0 →
  ∀ (hng : (dvSideSet F g u ℓ).Nonempty) (hnz : (dvSideSet F z u ℓ).Nonempty)
    (hngz : (dvSideSet F (g * z) u ℓ).Nonempty) (Mg Mz Mgz : ℕ)
    (hpg : dvHgt F g (dvSideMin F g u ℓ hng) = (Mg : ℕ∞))
    (hpz : dvHgt F z (dvSideMin F z u ℓ hnz) = (Mz : ℕ∞))
    (hpgz : dvHgt F (g * z) (dvSideMin F (g * z) u ℓ hngz) = (Mgz : ℕ∞)),
    ∃ τ : (F.stageField H₀ hpin)ˣ,
      dvResPoly F H₀ hpin (g * z) u ℓ hngz Mgz hpgz
        = Polynomial.C (τ : F.stageField H₀ hpin)
          * (dvResPoly F H₀ hpin g u ℓ hng Mg hpg
             * dvResPoly F H₀ hpin z u ℓ hnz Mz hpz)

/-- ★ PROVED — τ = 1 refines the ∃-τ shape (witness τ := 1). -/
theorem existsUnit_of_tauOne (O : Type*) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] (h : MixedResidualLawTauOneStatement O) :
    MixedResidualLawExistsUnitStatement O := by
  intro π F hπ hh H₀ hpin u ℓ hℓ hcop hfloor g z hg hz hng hnz hngz Mg Mz Mgz hpg hpz hpgz
  exact ⟨1, by
    rw [h π F hπ hh H₀ hpin u ℓ hℓ hcop hfloor g z hg hz hng hnz hngz Mg Mz Mgz hpg hpz hpgz]
    simp⟩

/-! ## Executable teeth — the `(2,2,3)`/`F₉` gate model and numeral-mirror δ-grids -/

/-- the TW-δ instance behind the MHDISP refutation pair: δ(3,3) = 1 at `(e₁,h) = (2,3)`. -/
private theorem delta_row_refutation_pair :
    twistExpN 2 3 6 = twistExpN 2 3 3 + twistExpN 2 3 3 + 1 := by decide

/-- a δ = 0 contrast instance at the same frame: δ(6,3) = 0. -/
private theorem delta_row_contrast :
    twistExpN 2 3 9 = twistExpN 2 3 6 + twistExpN 2 3 3 + 0 := by decide

private def eta : F9 := (0, 1)

private def embedF3 (x : ZMod 3) : F9 := (x, 0)

private def coeffX (n : ℕ) : ZMod 3 := if n = 1 then 1 else 0

private def coeffX2 (n : ℕ) : ZMod 3 := if n = 2 then 1 else 0

private def coeffX3 (n : ℕ) : ZMod 3 := if n = 3 then 1 else 0

private def bareSlotRead (k : ℕ) (coeff : ℕ → ZMod 3) : F9 :=
  ((slotWindowN 2 2 3 k).map fun t =>
      embedF3 (coeff (slotIdxN 2 3 k + 2 * t)) * eta ^ t).sum

/-- ★ the δ = 1 carry row — the MHDISP refutation pair `(X, X)` at heights `(3,3)` is an
INSTANCE of the corrected carry law: `γ₆(X²) = η¹ · γ₃(X) · γ₃(X)`. -/
private theorem carry_law_row_delta_one :
    bareSlotRead 6 coeffX2 = eta ^ 1 * (bareSlotRead 3 coeffX * bareSlotRead 3 coeffX) := by
  decide

/-- ★ the δ = 0 row — `(X², X)` at heights `(6,3)`: bare reads multiply with NO carry,
exactly as the law predicts (`γ₉(X³) = η⁰ · γ₆(X²) · γ₃(X)`). -/
private theorem carry_law_row_delta_zero :
    bareSlotRead 9 coeffX3 = eta ^ 0 * (bareSlotRead 6 coeffX2 * bareSlotRead 3 coeffX) := by
  decide

/-- numeral-mirror δ-grid: TW-δ holds for `slotIdxN`/`twistExpN` on a `(e₁,h)`-list and
`k, k' < 15` (cross-checks the mirrors against the generic PROVED `twistExp_add_carry`). -/
private def deltaGridOK (e₁ h bound : ℕ) : Bool :=
  (List.range bound).all fun k => (List.range bound).all fun k' =>
    decide (twistExpN e₁ h k + twistExpN e₁ h k' ≤ twistExpN e₁ h (k + k')) &&
    decide (twistExpN e₁ h (k + k') - twistExpN e₁ h k - twistExpN e₁ h k' ≤ 1) &&
    (slotIdxN e₁ h k + slotIdxN e₁ h k'
      == slotIdxN e₁ h (k + k')
          + e₁ * (twistExpN e₁ h (k + k') - twistExpN e₁ h k - twistExpN e₁ h k'))

private theorem delta_grid_2_3 : deltaGridOK 2 3 15 = true := by decide
private theorem delta_grid_3_2 : deltaGridOK 3 2 15 = true := by decide
private theorem delta_grid_5_3 : deltaGridOK 5 3 15 = true := by decide

end MHFIXCheck

section AxCheck

#print axioms MHFIXCheck.twistExp_add_carry
#print axioms MHFIXCheck.twistRead_mul_of_slotRes_carry
#print axioms MHFIXCheck.M1TwistProductLawStatement
#print axioms MHFIXCheck.M1SlotCarryLawStatement
#print axioms MHFIXCheck.M1DigitFaithfulStatement
#print axioms MHFIXCheck.MixedResidualLawTauOneStatement
#print axioms MHFIXCheck.existsUnit_of_tauOne
#print axioms MHFIXCheck.carry_law_row_delta_one
#print axioms MHFIXCheck.carry_law_row_delta_zero
#print axioms MHFIXCheck.delta_grid_2_3
#print axioms MHFIXCheck.delta_grid_3_2
#print axioms MHFIXCheck.delta_grid_5_3

end AxCheck
