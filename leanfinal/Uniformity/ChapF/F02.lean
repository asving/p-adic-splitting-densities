/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapF.F01
import Mathlib.SetTheory.Cardinal.Finite

/-!
# Uniformity.ChapF.F02 — `slotScaleEquiv`, `card_image_slotScale`: counts are gauge-blind

**Chapter F, NODE F.02** [lemma] (`blueprint/CHAP-F_weld_layer.md` §4), ENV-F1 + `[Field K]`.
The abstract mechanism shadow of LEMMA J-D0's clause (i) (`EFF.JD0.06`): a unit-character
gauge acts by a bijection, hence stratum counts computed through the gauged read equal
direct counts *wherever the stratum is carried onto itself* — which closure is exactly what
each consuming site verifies in-note (HYP.74's fold route). Deliberately WEAKER than LEMMA
J-D0 (blueprint FAITHFULNESS): count-blindness of the abstract action, not of the stratum
count of a decided shape.

Was an `axiom` stub at stage 0e; PROVED here (unit OM-9, 2026-08-16; certified first by
`verification/openmath/om9_weld_cert.py` LEG A1, both primes, with the NONCHAR
additive-shift negative control).
-/

namespace Uniformity.Density.Weld

/-- Slot-wise unit scaling is an equivalence (`EFF.JD0.06` clause (i)'s mechanism shadow). -/
def slotScaleEquiv {Γ : Type*} {K : Type*} [Field K] (u : Γ → Kˣ) :
    (Γ → K) ≃ (Γ → K) where
  toFun := slotScale u
  invFun := slotScale u⁻¹
  left_inv := by intro v; funext γ; simp [slotScale]
  right_inv := by intro v; funext γ; simp [slotScale]

theorem card_image_slotScale {Γ K : Type*} [Field K] (u : Γ → Kˣ) (S : Set (Γ → K)) :
    Nat.card ↥(slotScale u '' S) = Nat.card ↥S :=
  Nat.card_image_of_injective (slotScaleEquiv u).injective S

end Uniformity.Density.Weld
