/-
Unit Sp.shEquiv [REV 2, F11 — the spurious hypothesis struck; both statements in
full] — moves_ref: "Sh_{t,γ} is an affine bijection carrying the geometric slot set
onto the census slot set and a^geo onto a, ALL OTHER FIELDS FIXED".
deps: Sp.shSlots (for sh_geo_slots). sketch: sh_image by
`Finset.image_add_right_Icc`; sh_geo_slots: rewrite each image point by Sp.shSlots,
then Fin-indexed image of k ↦ a + k is the Icc. difficulty: easy.
-/
import LeanUrat.MovesSp.Defs

set_option linter.style.longLine false
set_option linter.style.header false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesSp

def shEquiv (σ : ℤ) : ℤ ≃ ℤ := Equiv.addRight σ

/-- pure interval translation — NO extra hypothesis. -/
theorem sh_image (t γ e ag : ℤ) (ℓ : ℕ) :
    (Finset.Icc ag (ag + ℓ)).image (Sh t γ e) =
      Finset.Icc (ag + shSigma t γ e) (ag + shSigma t γ e + ℓ) := sorry

/-- the census identification: the geometric slot set carried onto the census
slot set. -/
theorem sh_geo_slots (e h s t γ u0 s0 : ℤ)
    (he : 1 ≤ e) (hbez : e * s + h * t = 1) (hγ : γ = e * u0 + s0 * h) (ℓ : ℕ) :
    (Finset.image (fun k : Fin (ℓ + 1) => Sh t γ e (geoPos e t γ (s0 + k * e)))
      Finset.univ) = Finset.Icc (s0.fdiv e) (s0.fdiv e + ℓ) := sorry

end LeanUrat.MovesSp
