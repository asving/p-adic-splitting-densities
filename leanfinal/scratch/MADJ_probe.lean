/-
MADJ — machine pin for the Dv2ResSurv numeral adjudication.
Run from leanfinal/ with:
  lake env lean scratch/MADJ_probe.lean
-/
import Uniformity.ChapC.C80 -- s2Tower (orchestrator repair: the probe's own imports didn't reach it)
import Uniformity.ChapC.C132nv2
import Uniformity.ChapC.C132nv3b

set_option linter.style.longLine false

noncomputable section

namespace MADJProbe

open Polynomial IsLocalRing IsDiscreteValuationRing Uniformity.Density
open Uniformity.Density.Leaf Uniformity.Density.Tower
open Uniformity.Density.Tower.C130nv (toZ_add)
open Uniformity.Density.Tower.C130s2 Uniformity.Density.Tower.C130s6
open Uniformity.Density.Tower.C132nv1 Uniformity.Density.Tower.C132nv2
open Uniformity.Density.Tower.C132nv3b
open Uniformity.Density.Tower.C80 -- s2Tower (orchestrator repair)

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)] (h2 : Irreducible (2 : O)) (hq : residueCard O = 2)

private abbrev L := (s2Tower h2 hq).levelDatum h2
private abbrev Φ₂ := s2DepthTwoKeyAt h2 hq 2

/-- The two landed C132nv3b clauses assemble the hypothesis at the OUTER pair `(21,2)`.
The digit height inside `Dv2ResSurv` is still `dv2Hgt L`, hence the inner `(5,2)` read
encoded by `L`; those are different parameter layers. -/
theorem s2_dv2ResSurv_at_21 : Dv2ResSurv (L h2 hq) (Φ₂ h2 hq) 21 2 := by
  intro A B Ha Hb hA hB hHa hHb
  exact ⟨dv2Hgt_dev_composedKey_mod_eq h2 hq hA hB hHa hHb,
    s2_dv2ResSurv_slot1_at_21 h2 hq hA hB hHa hHb⟩

/-- The literal C132nv2 theorem marked "NV-4 consumption shape" elaborates with the
`(21,2)` survival package, and its conclusion is priced at that same outer pair. -/
theorem nv4_endpoint_fires_at_21 {g z : Polynomial O}
    (hng : (C132nv2.dv2SideSet (L h2 hq) (Φ₂ h2 hq) g 21 2).Nonempty)
    (hnz : (C132nv2.dv2SideSet (L h2 hq) (Φ₂ h2 hq) z 21 2).Nonempty)
    {Hg Hz : ℕ}
    (hHg : dv2Pin (L h2 hq) (Φ₂ h2 hq) g
      (C132nv2.dv2SideMin (L h2 hq) (Φ₂ h2 hq) g 21 2 hng) = (Hg : ℕ∞))
    (hHz : dv2Pin (L h2 hq) (Φ₂ h2 hq) z
      (C132nv2.dv2SideMin (L h2 hq) (Φ₂ h2 hq) z 21 2 hnz) = (Hz : ℕ∞)) :
    dv2Supp (L h2 hq) (Φ₂ h2 hq) (g * z) 21 2 =
      dv2Supp (L h2 hq) (Φ₂ h2 hq) g 21 2 +
        dv2Supp (L h2 hq) (Φ₂ h2 hq) z 21 2 :=
  dv2Supp_mul_eq_add_of_endpoint_le (L h2 hq) (s2Φ₂_monic h2 hq)
    (by rw [s2Φ₂_natDegree h2 hq]; norm_num) (by norm_num)
    (s2_dv2ResSurv_at_21 h2 hq) hng hnz hHg hHz

/-- After unfolding the value table, the same application has exactly M3-NV4's advertised
carrier conclusion `s2Hgt₃ (g*z) = s2Hgt₃ g + s2Hgt₃ z`. -/
theorem nv4_value_fires_at_21 {g z : Polynomial O}
    (hng : (C132nv2.dv2SideSet (L h2 hq) (Φ₂ h2 hq) g 21 2).Nonempty)
    (hnz : (C132nv2.dv2SideSet (L h2 hq) (Φ₂ h2 hq) z 21 2).Nonempty)
    {Hg Hz : ℕ}
    (hHg : dv2Pin (L h2 hq) (Φ₂ h2 hq) g
      (C132nv2.dv2SideMin (L h2 hq) (Φ₂ h2 hq) g 21 2 hng) = (Hg : ℕ∞))
    (hHz : dv2Pin (L h2 hq) (Φ₂ h2 hq) z
      (C132nv2.dv2SideMin (L h2 hq) (Φ₂ h2 hq) z 21 2 hnz) = (Hz : ℕ∞)) :
    s2Hgt₃ h2 hq (g * z) = s2Hgt₃ h2 hq g + s2Hgt₃ h2 hq z := by
  rw [s2Hgt₃, s2Hgt₃, s2Hgt₃, ← toZ_add]
  exact congrArg toZ (nv4_endpoint_fires_at_21 h2 hq hng hnz hHg hHz)

end MADJProbe
