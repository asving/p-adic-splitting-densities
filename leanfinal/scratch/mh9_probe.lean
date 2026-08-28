import Uniformity.ChapC.C133mh9

/-! MH9L smoke test: the payoff composition — `BlockContext` + the LANDED `theoremA`
fire the signed `BlockFrontier` with no carried hypothesis. -/

open Polynomial IsLocalRing Uniformity.Density Uniformity.Density.Tower

example {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O] {π : O}
    (hπ : Irreducible π) {F : KeyFrame O π} (hh : 0 < F.h)
    {H₀ hpin} (L : LevelDatum F H₀ hpin) {f : Polynomial O}
    (hctx : BlockContext L f) : BlockFrontier L f :=
  C133mh14.blockFrontier_of_context_of_theoremA hπ hh L hctx C133mh9.theoremA
