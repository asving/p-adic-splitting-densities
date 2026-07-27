/-
Unit U1.boxN  (MovesU campaign)  [TAG-FREE step 1]
moves_ref: "(BOX-N) p^{nN} = Σ_τ decided_τ(N) + undec(N) — the box partition,
           EXACT and tag-free as an identity of counts"
deps: U0, U0b.
sketch: partition the Fintype `Box p n N` by the value of `X.canonical N` in
        `Option (SplittingType n)`: `Finset.card_eq_sum_card_fiberwise` over
        `Finset.univ`; fibers of `some σ` are `decided`, fiber of `none` is `undec`
        (`Nat.card_eq_fintype_card` + subtype/filter card transfer); close with U0.
        Tag-free BECAUSE it is a count identity for the interface's canonical map —
        the map's fidelity Props (`canonical_stable`; VP-SOUND as the ledger's
        `cl10_vpsound`) are carried elsewhere, not consumed here.
hypothesis_fields: none consumed (F1's repair: the verdict is now the pinned
        classifier interface, D2; no arbitrary labeling is an instance).
-/
import Mathlib
import LeanUrat.MovesU.U0_boxCard
import LeanUrat.MovesU.U0b_splitTypeFintype

set_option linter.style.longLine false
set_option linter.style.header false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesU

/-- (BOX-N), the exact count identity: the box partitions into the decided-τ classes
    and the undecided complement. -/
theorem boxN {n p : ℕ} (X : ClassifierSpec n p) [NeZero p] (N : ℕ) :
    (∑ σ : SplittingType n, X.decided σ N) + X.undec N = p ^ (n * N) :=
  sorry

end LeanUrat.MovesU
