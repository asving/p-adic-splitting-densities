import Uniformity.ChapB.B82

namespace Uniformity.Density.Leaf
open Polynomial IsLocalRing

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {π : O}

example {K : Type*} [Field K] {ψ : Polynomial K} (h : Irreducible ψ) : 1 ≤ ψ.natDegree := by
  exact?
