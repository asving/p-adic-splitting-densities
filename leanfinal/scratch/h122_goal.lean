import Uniformity.ChapH.H122

namespace Uniformity.Density.Induction

open IsLocalRing

set_option linter.unusedVariables false in
example {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Finite (ResidueField O)] [IsAdicComplete (maximalIdeal O) O] {π : O}
    (hπ : Irreducible π) {m : ℕ} (hm : 2 ≤ m) (hm3 : m ≤ 3) :
    RateSpecies (residueCard O) 1 1 1 (fun N => uClusterNorm O π m N) := by
  refine uClusterNorm_rateSpecies_of_betaLeg hπ hm hm3 ?_
  trace_state
  sorry

end Uniformity.Density.Induction
