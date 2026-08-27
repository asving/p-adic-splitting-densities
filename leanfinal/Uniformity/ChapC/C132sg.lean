/-
[M3-SG (conditional core), 2026-08-27] — the μ₃ calculus packaging, CONDITIONAL on the
campaign's two remaining math opens (orchestrator landing; blueprint row
`docs/in-progress/MU3_CAMPAIGN_2026-08-26.md` §6 M3-SG, first half).

`s2Mu3_calculus_nonempty_of` fires CC-16's factored packaging theorem
(`fgmn_model_calculus_nonempty`, `C130pk.lean`) through M3-FD0's records: given the two
open suppliers (M3-RP10b's `hex`, M3-KP6b's `hconv` — see `C132fd0.lean`'s header), the
depth-2 calculus `FGMNCalculus (s2DepthTwo h2 hq) 2 1 21` is inhabited — the corrected
(2,1,21) sibling of the landed depth-1 star `C130sg.s2_calculus_discharge` (which is
UNCONDITIONAL at (2,1,5)).  When RP10b/KP6b land, the final SG node plugs them in here
and fires the amended GENTOW consumers (`gentow5w_two` at (2,1,21) per A-C.17/A-C.18).
-/
import Uniformity.ChapC.C132fd0

set_option linter.style.longLine false

namespace Uniformity.Density.Tower.C132sg

open Polynomial IsLocalRing IsDiscreteValuationRing Uniformity.Density
open Uniformity.Density.Leaf Uniformity.Density.Tower
open Uniformity.Density.Tower.C130s2 Uniformity.Density.Tower.C132kp0
open Uniformity.Density.Tower.C132nv1 Uniformity.Density.Tower.C132rp8
open Uniformity.Density.Tower.C132fd0

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)] (h2 : Irreducible (2 : O)) (hq : residueCard O = 2)

/-- ★★ **M3-SG (conditional core)**: the depth-2 μ₃ calculus at the corrected `(2,1,21)`
triple, conditional on exactly the two open suppliers of `s2SourceLawsTwo_of`. -/
theorem s2Mu3_calculus_nonempty_of
    (hex : ∀ ψ : Polynomial ((s2DepthTwo h2 hq).fld 2),
      ψ.Monic → Irreducible ψ → ψ.natDegree = 1 → ψ.coeff 0 ≠ 0 →
        ∃ g : Polynomial O, g.Monic ∧
          g.natDegree = 2 * 1 * (((s2DepthTwoKeyChain h2 hq).keyAt 2).natDegree) ∧
          s2Mu3NormRes h2 hq g = ψ)
    (hconv : ∀ g h : Polynomial O,
      S2Mu3KeyPoly h2 hq g → S2Mu3KeyPoly h2 hq h →
        s2Mu3NormRes h2 hq g = s2Mu3NormRes h2 hq h → S2Mu3InitialEquiv h2 hq g h) :
    Nonempty (FGMNCalculus (s2DepthTwo h2 hq) 2 1 21) :=
  fgmn_model_calculus_nonempty (s2DepthTwoKeyChain h2 hq) (s2SourceDataTwo h2 hq)
    (s2SourceLawsTwo_of h2 hq hex hconv)

end Uniformity.Density.Tower.C132sg

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Tower.C132sg.s2Mu3_calculus_nonempty_of

end AxCheck
