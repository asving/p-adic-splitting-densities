import LeanUrat.Scaffold.DictIII.GDOrder1

namespace LeanUrat.Scaffold.DictIII

-- Probe A: the §1.4 displayed `w1` VERBATIM — exact error capture.
def w1 {O} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (Φ₀ : Polynomial O) (e h : ℕ) (B : Polynomial (FractionRing O)) :
    WithTop ℤ :=
  Finset.inf' (Finset.range (B.natDegree + 1)) (by simp) fun t =>
    (e : ℤ) • gaussW (devCoeff (Polynomial.map (algebraMap O (FractionRing O)) Φ₀) B t) +
      ((t : ℤ) * (h : ℤ))

-- Probe B: the §1.4 displayed `w1_posg` VERBATIM — exact error capture.
theorem w1_posg {O} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (Φ₀ : Polynomial O) (e h : ℕ) (B : Polynomial (FractionRing O)) :
    0 ≤ w1 Φ₀ e h B ∨ w1 Φ₀ e h B = ⊤ := sorry

-- Probe C: instance landscape for the display's arithmetic.
#synth SMul ℤ (WithTop ℤ)
#synth Mul (WithTop ℤ)
#synth SubNegMonoid (WithTop ℤ)

-- Probe D: even a compiling gaussW with the DISPLAYED signature
-- (over a DVR carrier) could not serve w1: FractionRing O is a field.
example {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] :
    ¬ IsDiscreteValuationRing (FractionRing O) :=
  fun h => h.not_isField (Field.toIsField _)

end LeanUrat.Scaffold.DictIII
