import Mathlib

/- CTS2 probe: the four mechanical joints for the IFCG48 M3+ increments.
   1. AdjoinRoot tower instances (Algebra O (AdjoinRoot H), IsScalarTower)
   2. Algebra.norm_norm unification in the AdjoinRoot tower
   3. Algebra.norm_eq_of_algEquiv shape
   4. finrank tower law through the AdjoinRoot tower (with StrongRankCondition) -/

noncomputable section

-- probe 1: instances resolve
example {O : Type*} [CommRing O] (f : Polynomial O) (H : Polynomial (AdjoinRoot f)) :
    True := by
  haveI h1 : Algebra O (AdjoinRoot H) := inferInstance
  haveI h2 : IsScalarTower O (AdjoinRoot f) (AdjoinRoot H) := inferInstance
  trivial

-- probe 2: norm_norm fires
example {O : Type*} [CommRing O] {f : Polynomial O} (hf : f.Monic)
    {H : Polynomial (AdjoinRoot f)} (hH : H.Monic) (z : AdjoinRoot H) :
    Algebra.norm O (Algebra.norm (AdjoinRoot f) z) = Algebra.norm O z := by
  haveI : Module.Free O (AdjoinRoot f) :=
    Module.Free.of_basis (AdjoinRoot.powerBasis' hf).basis
  haveI : Module.Free (AdjoinRoot f) (AdjoinRoot H) :=
    Module.Free.of_basis (AdjoinRoot.powerBasis' hH).basis
  exact Algebra.norm_norm

-- probe 3: norm invariance under an O-algebra iso
example {O : Type*} [CommRing O] {A B : Type*} [CommRing A] [CommRing B]
    [Algebra O A] [Algebra O B] (ψ : A ≃ₐ[O] B) (x : A) :
    Algebra.norm O (ψ x) = Algebra.norm O x :=
  Algebra.norm_eq_of_algEquiv ψ x

-- probe 4: the finrank tower law through AdjoinRoot, DVR base
example {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {f : Polynomial O} (hf : f.Monic) (hfd : 0 < f.natDegree)
    {H : Polynomial (AdjoinRoot f)} (hH : H.Monic) (hHd : 0 < H.natDegree)
    [IsDomain (AdjoinRoot f)] [IsDiscreteValuationRing (AdjoinRoot f)]
    {h : Polynomial O} (hh : h.Monic)
    (ψ : AdjoinRoot h ≃ₐ[O] AdjoinRoot H) :
    h.natDegree = f.natDegree * H.natDegree := by
  haveI : Module.Free O (AdjoinRoot f) :=
    Module.Free.of_basis (AdjoinRoot.powerBasis' hf).basis
  haveI : Module.Free (AdjoinRoot f) (AdjoinRoot H) :=
    Module.Free.of_basis (AdjoinRoot.powerBasis' hH).basis
  have h1 : Module.finrank O (AdjoinRoot h) = h.natDegree := by
    rw [(AdjoinRoot.powerBasis' hh).finrank]; rfl
  have h2 : Module.finrank O (AdjoinRoot f) = f.natDegree := by
    rw [(AdjoinRoot.powerBasis' hf).finrank]; rfl
  have h3 : Module.finrank (AdjoinRoot f) (AdjoinRoot H) = H.natDegree := by
    rw [(AdjoinRoot.powerBasis' hH).finrank]; rfl
  have h4 : Module.finrank O (AdjoinRoot f) * Module.finrank (AdjoinRoot f) (AdjoinRoot H)
      = Module.finrank O (AdjoinRoot H) :=
    Module.finrank_mul_finrank O (AdjoinRoot f) (AdjoinRoot H)
  have h5 : Module.finrank O (AdjoinRoot h) = Module.finrank O (AdjoinRoot H) :=
    ψ.toLinearEquiv.finrank_eq
  rw [← h1, h5, ← h4, h2, h3]
