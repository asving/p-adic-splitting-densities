/-
[M3-RP10b, 2026-08-27] — the non-recipe `normalized_exists` discharge (orchestrator
landing; the calibrated route of `runs/wave-b/launch_wave_20260827_2207.sh`'s MRP10B
brief).  STAGE A: the exact μ₃ grade of the recipe candidate.

The candidate is RP-10's own `g₈ := Φ₂² − 2⁴·Φ′` (`C132rp10.lean` — monic and degree 8
are landed there).  The correction `2⁴Φ′` has inner μ₂-height
`4·h₂(C 2) + h₂(Φ′) = 4·4 + 5 = 21`, so BOTH development slots of `g₈` sit on the μ₃
grade-42 line (`j = 0`: `2·21 + 21·0`; `j = 2`: `2·0 + 21·2`) — grade `42 = e′·u′` is the
honest corrected grade (the printed `21` is machine-impossible: RP-10's
`s2Mu3_recipe_correction_input_impossible`).
-/
import Uniformity.ChapC.C132sg

set_option linter.style.longLine false

namespace Uniformity.Density.Tower.C132rp10b

open Polynomial IsLocalRing IsDiscreteValuationRing Uniformity.Density
open Uniformity.Density.Leaf Uniformity.Density.Tower
open Uniformity.Density.Tower.C130s2 Uniformity.Density.Tower.C130s6
open Uniformity.Density.Tower.C130np0 Uniformity.Density.Tower.C130nv2
open Uniformity.Density.Tower.C130nv3
open Uniformity.Density.Tower.C132nv0 Uniformity.Density.Tower.C132nv1
open Uniformity.Density.Tower.C132nv6
open Uniformity.Density.Tower.C132rp0

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)] (h2 : Irreducible (2 : O)) (hq : residueCard O = 2)

/-- the recipe candidate, RP-10's own `g₈ = Φ₂² − 2⁴Φ′`. -/
noncomputable def g8 : Polynomial O :=
  (s2DepthTwoKeyAt h2 hq 2 : Polynomial O) ^ 2 -
    Polynomial.C ((2 : O) ^ 4) * (s2DepthTwoKeyChain h2 hq).keyAt 1

/-- the correction summand. -/
noncomputable def corr : Polynomial O :=
  Polynomial.C ((2 : O) ^ 4) * (s2DepthTwoKeyChain h2 hq).keyAt 1

theorem g8_eq : g8 h2 hq =
    (s2DepthTwoKeyAt h2 hq 2 : Polynomial O) ^ 2 - corr h2 hq := rfl

/-- `keyAt 1` of the depth-two chain is the frame key. -/
theorem corr_eq : corr h2 hq =
    Polynomial.C ((2 : O) ^ 4) * ((s2Frame h2 hq).key : Polynomial O) := rfl

/-- **the inner μ₂ height of the correction is `21`**: `4·4 + 5`. -/
theorem s2Hgt₂_corr : s2Hgt₂ h2 hq (corr h2 hq) = ((21 : ℤ) : WithTop ℤ) := by
  rw [corr_eq, show ((2 : O) ^ 4) = 2 * 2 * 2 * 2 by ring, map_mul, map_mul, map_mul]
  rw [s2Hgt₂_mul h2 hq, s2Hgt₂_mul h2 hq, s2Hgt₂_mul h2 hq, s2Hgt₂_mul h2 hq,
    s2Hgt₂_C_two h2 hq, s2Hgt₂_key h2 hq]
  norm_num

end Uniformity.Density.Tower.C132rp10b

section AxCheck

#print axioms Uniformity.Density.Tower.C132rp10b.s2Hgt₂_corr

end AxCheck
