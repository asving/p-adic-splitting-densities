/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapC.C35
import Uniformity.ChapC.C130nv3
import Uniformity.ChapC.C131f
import Uniformity.ChapC.C141defs

/-!
# Uniformity.ChapC.C133mh1 — `[MH.1, 2026-08-27]`: the corrected Hensel-engine root, promoted

**Node MH.1** (`docs/in-progress/HENSEL_ENGINE_2026-08-26.md` §3.1′, the `[MHFIX 2026-08-27]`
amendment; regrade `runs/wave-b/verdict_MHFIX.md`; source `leanfinal/scratch/MHFIX_probe.lean`,
green, Lean-core). The MH series opens the C133 prefix. Promotes the probe's GENERIC content —
the two PROVED theorems and the corrected root's STATEMENT SHAPES — byte-identical apart from
plumbing (namespace, opens, import path).

## What M1′ is, and what lands here

M1(2)'s bare `slotRes` multiplicativity is FALSE (MHDISP finding 3, refuted at the
`(e₁,f₁,h) = (2,2,3)`/`F₉` mirror). The corrected root **M1′** replaces it with a
stage-letter-carried product law, `η^δ` for a twist-exponent cocycle defect
`δ = δ(k,k') ∈ {0,1}`: (1) twist product `twistRead(ka+kb)E = twistRead ka a·twistRead kb b`
(**`τ = 1`**); (2) slot carry `slotRes(ka+kb)E = η^δ·slotRes ka a·slotRes kb b`; (3)
faithfulness/exactness — at exact finite heights both right reads are nonzero, hence
`w(E) = ka+kb` exactly (old M1(1), recovered WITHOUT the M1a stability step).

Landed here, **PROVED**: `twistExp_add_carry` (**Lemma TW-δ**, the carry-exponent cocycle
`q(k)+q(k')+δ = q(k+k')`, `e₁·δ = i(k)+i(k')−i(k+k')`, `δ ≤ 1`, pure ℕ arithmetic from C.16's
`slotIdx_spec`/`twistExp_spec` alone) and `twistRead_mul_of_slotRes_carry` (the carry ⟹ twist
bridge: clause (2) implies clause (1) given TW-δ, the C.22 inverse twist cancelling `η^δ`
exactly). Landed here as **STATEMENT SHAPES** (`Prop`-valued defs, nothing asserted — the
C35b `D13Statement` pattern), per the doc's §3.1′ naming: `M1TwistProductLawStatement`
(clause 1), `M1SlotCarryLawStatement` (clause 2, the "corrected slot product"),
`M1DigitFaithfulStatement` (clause 3, subsumes old M1(1)).

## Honest scope: what does NOT land here

The full M1′ proof (doc §3.1′ Steps 1–6: the associated-graded model `gr_w(O[x]) ≅ k_r[Π,X̄]`,
the reading homomorphism `ρ̃`, and the assembly discharging the three statement shapes above)
is **MATH-PROVED but Lean-transcription OPEN**, sized 250–450 lines (coefficientwise route on
the C.21 window, `s2GradedRes_mul_of_exact` as the pattern, no `gr` construction in Lean) —
this node's separately-scoped remaining work, NOT a "plumbing adjustment" on the probe. Also
out of scope: `MixedResidualLawTauOneStatement`/`MixedResidualLawExistsUnitStatement`/
`existsUnit_of_tauOne` (Theorem M clause 3, node **MH.3**) and the probe's executable
F₉-gate/numeral-mirror teeth (cert sanity instances, covered by `verification/mhfix_cert.py`).

## Plumbing (D9) and DEPENDS

`twistRead_mul_of_slotRes_carry` needs `Field (F.stageField H₀ hpin)`. Per the standing D9
convention (C.04/C.12/C.26/C.47/C.80/C.97: public cure unlanded; the private cure is
re-declared byte-identical at every consuming node since `private` does not cross files),
`isKey_X`/`localFieldStageField` are re-declared rather than imported. DEPENDS: C.16
(`slotIdx_spec`, `twistExp_spec`) · C.01 (`KeyFrame`) · C.19/C.22/C.25 (`stageLetter`,
`stageLetter_ne_zero`, `twistRead`, `slotRes`) · B.25 — import chain (`C35`, `C130nv3`,
`C131f`, `C141defs`) is the probe's, reused verbatim. **Status:** sorry-free, zero new
axiom, footprint Lean-core only — see the AxCheck footer.
-/

set_option linter.style.longLine false

namespace Uniformity.Density.Tower.C133mh1

open Polynomial IsLocalRing IsDiscreteValuationRing Uniformity.Density
open Uniformity.Density.Leaf Uniformity.Density.Tower
open Uniformity.Density.Weld

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {π : O}

/-! ## D9 plumbing (private; re-declared per the standing convention — see above) -/

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

/-! ## Lemma TW-δ — the twist-exponent cocycle (PROVED) -/

/-- ★ **PROVED — TW-δ, the twist-exponent cocycle** (the generic exponent law behind the
slot carry): `q(k) + q(k') + δ = q(k + k')` for a δ ∈ {0,1} that is exactly the slot-index
carry bit, `e₁·δ = i(k) + i(k') − i(k+k')`. Pure ℕ arithmetic from C.16's specs. -/
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

/-! ## The carry ⟹ twist bridge (PROVED) -/

/-- ★ **PROVED — the twist normalization cancels the carry**: the slot-carry form of the
corrected M1 implies the twist-read product form, given the TW-δ exponent identity. The
inverse-twist exponents absorb `η^δ` exactly; this is why the engine-facing law is `τ = 1`. -/
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

/-! ## M1′ — statement shapes (`Prop`-valued defs; nothing asserted) -/

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

end Uniformity.Density.Tower.C133mh1

/-! ## AxCheck footer -/

section AxCheck

#print axioms Uniformity.Density.Tower.C133mh1.twistExp_add_carry
#print axioms Uniformity.Density.Tower.C133mh1.twistRead_mul_of_slotRes_carry
#print axioms Uniformity.Density.Tower.C133mh1.M1TwistProductLawStatement
#print axioms Uniformity.Density.Tower.C133mh1.M1SlotCarryLawStatement
#print axioms Uniformity.Density.Tower.C133mh1.M1DigitFaithfulStatement

end AxCheck
