import Mathlib
import LeanUrat.Scaffold.DictIII.Carriers
import LeanUrat.Scaffold.DictIII.GMNReader
import LeanUrat.MovesT.Defs

namespace LeanUrat.Scaffold.DictIII

variable {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]

-- probe 1: the accE application exactly as displayed in BP_III §1.3 line 350
example (H : EHist p F) : ℕ := MovesT.accE H.nodes

-- probe 2: GMNCor120_38 verbatim (expects DecIrr/ConsF unknown)
structure GMNCor120_38 (p : ℕ) [Fact p.Prime]
    (F : Type*) [Field F] [Finite F] : Prop where
  irrationalBranch : ∀ {f : Polynomial ℤ_[p]} {H : EHist p F}
    {D : GMNData f (Theta H)} {R : GMNReader f (Theta H) D},
    DecIrr H → ConsF f H D R →
    MovesT.accE H.nodes * MovesT.accF H.nodes = f.natDegree
  positiveResidualDegree : ∀ {f : Polynomial ℤ_[p]} {H : EHist p F}
    {D : GMNData f (Theta H)}, DecIrr H →
    ∀ i, i < H.nodes.length → 1 ≤ D.residualDegree i

-- probe 3: Lit3Hensel verbatim (Mathlib-only deps)
structure Lit3Hensel (p : ℕ) [Fact p.Prime] : Prop where
  lift : ∀ {R : Type*} [CommRing R] [IsDomain R]
    (f g₀ h₀ : Polynomial R) (I : Ideal R),
    f.Monic → g₀.Monic → h₀.Monic →
    Ideal.IsMaximal I → IsCoprime g₀ h₀ →
    Polynomial.map (Ideal.Quotient.mk I) f =
      Polynomial.map (Ideal.Quotient.mk I) (g₀ * h₀) →
    ∃ g h : Polynomial R, g.Monic ∧ h.Monic ∧ f = g * h

end LeanUrat.Scaffold.DictIII
