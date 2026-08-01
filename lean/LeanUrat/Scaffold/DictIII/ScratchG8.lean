import LeanUrat.Scaffold.DictIII.GDOrder1
import LeanUrat.Scaffold.DictIII.Devid

namespace LeanUrat.Scaffold.DictIII

-- probe A: the §1.4 displayed `w1` verbatim — does it elaborate in-project?
noncomputable def w1_probe {O} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (Φ₀ : Polynomial O) (e h : ℕ) (B : Polynomial (FractionRing O)) :
    WithTop ℤ :=
  Finset.inf' (Finset.range (B.natDegree + 1)) (by simp) fun t =>
    (e : ℤ) • gaussW (devCoeff (Polynomial.map (algebraMap O (FractionRing O)) Φ₀) B t) +
      ((t : ℤ) * (h : ℤ))

end LeanUrat.Scaffold.DictIII
