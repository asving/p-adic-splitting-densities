import Uniformity.ChapC.C83
import Mathlib.RingTheory.Polynomial.GaussLemma

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Uniformity.Density.Tower

open Uniformity.Density.Leaf

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {π : O}

/- The leanspec has this convenience abbreviation; the landed C.83 writes it out. -/
abbrev KeyFrame.Pin (F : KeyFrame O π) (H₀ : ℕ) : Prop :=
  npHgt Polynomial.X F.key (sideMin Polynomial.X F.key F.h F.e₁ F.hne) = (H₀ : ℕ∞)

class FGMNCalculus {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀} {r : ℕ}
    (W : DeepTower F H₀ hpin r) (e' f' u' : ℕ) where
  keyAt : ℕ → Polynomial O
  keyAt_one : keyAt 1 = F.key
  keyAt_deg : ∀ i, 1 ≤ i → i ≤ r → (keyAt i).natDegree = W.Dcum i

  ExactGrade : ℕ → Polynomial O → Prop
  AboveGrade : ℕ → Polynomial O → Prop

  Rgr : ℕ → Polynomial O → W.fld r
  Rres : Polynomial O → Polynomial (W.fld r)
  KP : Polynomial O → Prop
  nuEquiv : Polynomial O → Polynomial O → Prop
  letterZ : ℕ → W.fld r

  Rgr_zero_of_above : ∀ β (g : Polynomial O),
    AboveGrade β g → Rgr β g = 0
  Rgr_add : ∀ β (g h : Polynomial O),
    ExactGrade β g → ExactGrade β h → ExactGrade β (g + h) →
      Rgr β (g + h) = Rgr β g + Rgr β h
  Rgr_mul : ∀ β β' (g h : Polynomial O),
    ExactGrade β g → ExactGrade β' h →
      ExactGrade (β + β') (g * h) ∧
      Rgr (β + β') (g * h) = Rgr β g * Rgr β' h
  Rgr_ne_zero : ∀ β (g : Polynomial O),
    ExactGrade β g → g.natDegree < (keyAt r).natDegree → g ≠ 0 → Rgr β g ≠ 0
  Rres_mul : ∀ g h : Polynomial O,
    Rres (g * h) = Rres g * Rres h
  Rres_recipe : ∀ (khat : ℕ → Polynomial O),
    (∀ t, t < f' → ExactGrade ((f' - t) * u') (khat t)) →
    (∀ t, t < f' → (khat t).natDegree < (keyAt r).natDegree) →
    Rres ((keyAt r) ^ (e' * f') -
        ∑ t ∈ Finset.range f', khat t * (keyAt r) ^ (e' * t)) =
      Polynomial.X ^ f' -
        ∑ t ∈ Finset.range f',
          Polynomial.C (Rgr ((f' - t) * u') (khat t)) * Polynomial.X ^ t
  Rres_exists : 0 < r → ∀ ψ : Polynomial (W.fld r),
    ψ.Monic → Irreducible ψ → ψ.natDegree = f' → ψ.coeff 0 ≠ 0 →
      ∃ g : Polynomial O,
        g.Monic ∧
        g.natDegree = e' * f' * (keyAt r).natDegree ∧
        Rres g = ψ
  KP_criterion : ∀ g : Polynomial O,
    g.Monic →
    g.natDegree = e' * f' * (keyAt r).natDegree →
    Irreducible (Rres g) →
    (Rres g).natDegree = f' →
    (Rres g).coeff 0 ≠ 0 →
      KP g
  KP_irred : ∀ g : Polynomial O, KP g → g.Monic → Irreducible g
  KP_keyAt : 0 < r → KP (keyAt r)
  Rres_keyAt : 0 < r → Rres (keyAt r) = 1
  nuEquiv_iff_Rres : ∀ g h : Polynomial O,
    KP g → KP h → (nuEquiv g h ↔ Rres g = Rres h)
  letterZ_ne_zero : ∀ i, 1 ≤ i → i ≤ r → letterZ i ≠ 0

section GaussProbe

variable {K : Type*} [Field K] [Algebra O K] [IsFractionRing O K]

example (g : Polynomial O) (hg : g.Monic) :
    Irreducible g ↔ Irreducible (g.map (algebraMap O K)) :=
  hg.irreducible_iff_irreducible_map_fraction_map (K := K)

end GaussProbe

end Uniformity.Density.Tower
