import Uniformity.ChapC.C34
import Uniformity.ChapC.C35
import Uniformity.ChapC.C99r
import Uniformity.ChapC.C107ac14
import Uniformity.ChapC.C74

/-!
# AMND amendment checks

Small elaboration teeth for A-C.17--A-C.20.  The arithmetic/refutation evidence remains in
`DEC3_probe.lean`, `rb3_bridge_cert.py`, and `dv_hensel_cert.py`; this file checks the enacted
consumer shapes against the landed vocabulary.
-/

namespace AMNDCheck

open Polynomial IsLocalRing IsDiscreteValuationRing Uniformity.Density
open Uniformity.Density.Leaf Uniformity.Density.Tower

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {π : O}

/-- A-C.18's positive-depth indexing tooth. -/
theorem chainNormBelow_succ {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀} {r : ℕ}
    {W : DeepTower F H₀ hpin r} {e' f' u' : ℕ} (I : FGMNCalculus W e' f' u')
    (i k : ℕ) : I.chainNormBelow (i + 1) k = I.chainNorm i k := by
  simp [FGMNCalculus.chainNormBelow]

/-- A-C.19's repaired closure, with the degree fence before the budget family. -/
def ShadowPersistenceAmended : Prop :=
  ∀ {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {π : O}
    {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀}
    (T : TowerDatum F H₀ hpin) (hπ : Irreducible π) (_hh : 1 ≤ F.h)
    [Finite (ResidueField O)] {μ₂ j : ℕ} (_hj : j < μ₂) (_hc : TouchCert T hπ μ₂ j)
    {g : Polynomial O} (_hdeg : g.natDegree < μ₂ * T.D₂)
    (_hbudget : ∀ j' a b : ℕ, j' < μ₂ → a < F.e₁ * F.f₁ → b < T.e₂ * T.f₂ →
      (budgetFloor T μ₂ j' a b : ℕ∞)
        ≤ addVal O ((dev F.key (dev (composedKey T) g j') b).coeff a)),
    ((T.theta μ₂ j + 1 : ℕ) : ℕ∞)
        ≤ dv2Hgt (T.levelDatum hπ) (shadowDev T g j - dev (composedKey T) g j) ∧
    dv2Hgt (T.levelDatum hπ)
        (shadowDev T ((composedKey T) ^ μ₂ + g) j
          - dev (composedKey T) ((composedKey T) ^ μ₂ + g) j)
      = (T.theta μ₂ j : ℕ∞)

#check @C99r.gentow2_Bpp
#check @C107ac14.gentow5w_two
#check @C107ac14.gentow5w_one_shape_of_letter_tie
#check @exists_dv_residual_dissection_of_frontier
#check @blockFactor_spec_of_frontier

end AMNDCheck

#print axioms AMNDCheck.chainNormBelow_succ
#print axioms AMNDCheck.ShadowPersistenceAmended
#print axioms Uniformity.Density.Tower.C99r.gentow2_Bpp
#print axioms Uniformity.Density.Tower.C107ac14.gentow5w_two
#print axioms Uniformity.Density.Tower.C107ac14.gentow5w_one_shape_of_letter_tie
#print axioms Uniformity.Density.Tower.exists_dv_residual_dissection_of_frontier
#print axioms Uniformity.Density.Tower.blockFactor_spec_of_frontier
