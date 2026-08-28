/- CC-18 scratch: defeq sanity checks for the refl-transport design. Not part of any build. -/
import Uniformity.ChapC.C130vw

open Uniformity.Density Uniformity.Density.Gauge Uniformity.Density.Tower

universe uG

section Checks

variable {G : Type uG} [CommGroup G] {K : Type} [Field K]

-- (1) NormSection transport along refl is the identity, definitionally
example (N : NormSection G) : N.transport (MulEquiv.refl G) = N := rfl

-- (2) composing a height hom with refl.symm is the identity, definitionally
example (v : G →* Multiplicative ℤ) : v.comp (MulEquiv.refl G).symm.toMonoidHom = v := rfl

-- (3) GaugeArena transport along refl is the identity, definitionally
example {N : NormSection G} (A : GaugeArena G K N) : A.transport (MulEquiv.refl G) = A := rfl

-- (4) the kernel comap along refl is the identity, definitionally
def kerComapAlong {G : Type uG} {H : Type*} [CommGroup G] [CommGroup H]
    (e : G ≃* H) (v : G →* Multiplicative ℤ) :
    MonoidHom.ker (v.comp e.symm.toMonoidHom) →* MonoidHom.ker v where
  toFun x := ⟨e.symm x.1, x.2⟩
  map_one' := Subtype.ext (map_one e.symm)
  map_mul' x y := Subtype.ext (map_mul e.symm x.1 y.1)

example (v : G →* Multiplicative ℤ) {L : Type} [Field L]
    (ρ : MonoidHom.ker v →* Lˣ) :
    ρ.comp (kerComapAlong (MulEquiv.refl G) v) = ρ := rfl

-- (5) lambda-eta on the read family
example {L : Type} [Field L] (ρ : ℕ → G → Lˣ) : (fun j g => ρ j g) = ρ := rfl

-- (6) pointwise product of monoid homs composes distributively, definitionally
example {M : Type*} [CommGroup M] {L : Type} [Field L]
    (f g : M →* Lˣ) (h : G →* M) : (f * g).comp h = f.comp h * g.comp h := rfl

end Checks
