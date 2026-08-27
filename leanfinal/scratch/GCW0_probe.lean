import Uniformity.ChapI.IFC2

set_option linter.style.longLine false

noncomputable section

namespace GCW0Probe

open Uniformity.Density Uniformity.Density.Gauge Uniformity.Density.Tower

universe uT

/-- GC-13's read/normalizer dictionary at one D.44 site. -/
structure GC13Wiring {G : Type*} [CommGroup G] {Kt : Type*} [Field Kt]
    (N : NormSection G) (q : ℤ) (R : G → Kt)
    {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {π : O}
    {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀} {r : ℕ}
    {W : DeepTower.{0, uT} F H₀ hpin r} {e' f' u' : ℕ}
    (I : FGMNCalculus W e' f' u') (φ : W.fld r →+* Kt) : Prop where
  read_norm : ∀ s : ℕ, 1 ≤ s → s ≤ f' →
    R (N.n (s * q)) =
      φ (I.Rgr (e' * (s * u')) (I.chainNormBelow r (s * u')))

section S2

open IsLocalRing Uniformity.Density.IFC1 Uniformity.Density.IFC2
open Uniformity.Density.Tower.C130s2 Uniformity.Density.Tower.C132sg2

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)] (h2 : Irreducible (2 : O)) (hq : residueCard O = 2)

/-- The signed law's projection is byte-for-byte IFC2's remaining `hread` binder. -/
theorem s2_consumer_shape {G : Type*} [CommGroup G] {Kt : Type*} [Field Kt]
    {N : NormSection G} (A : GaugeArena G Kt N) (q : ℤ) (R : G → Kt)
    (φ : (s2DepthTwo h2 hq).fld 2 →+* Kt)
    (hwire : GC13Wiring N q R (s2Mu3Calculus h2 hq) φ) :
    ∃ w : Ktˣ, GentowWWindow A q R w 1 :=
  s2Mu3_gentowWWindow_of_hread h2 hq A q R φ
    (hwire.read_norm 1 le_rfl le_rfl)

end S2

end GCW0Probe

end

#print axioms GCW0Probe.GC13Wiring
#print axioms GCW0Probe.s2_consumer_shape
