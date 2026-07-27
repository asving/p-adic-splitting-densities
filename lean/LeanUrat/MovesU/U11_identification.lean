/-
Unit U11.identification  (MovesU campaign)  [derived; inputs explicit]
moves_ref: "and ρ_σ(p) IS the splitting density of type σ over ℤ_p — the undecided
           complement has mass 0 and the classifier verdicts are the true
           factorization types (X.3/CL-4 + [3t] VP, with VP-SOUND's citation duty)"
deps: U7 (DefsLedger in the import chain for the ledger-facing consumption at U10;
      `VPSound` itself lives in Defs).
sketch: sandwich `decided σ N ≤ trueCount σ N ≤ decided σ N + undec N`. Left: `hvs`
        injects {f // canonical = some σ} ⊆ {f // trueType = some σ}
        (`Nat.card_le_card_of_injective` on subtype inclusion). Right: a true-σ
        class is decided-σ or undecided — if `canonical N f = some τ` then `hvs`
        gives `trueType = some τ = some σ`, so `τ = σ` (`Option.some.inj`; trueType
        is single-valued); else `canonical N f = none` (undec). So {true-σ} ⊆
        {decided-σ} ⊎ {undec}, card ≤. Divide by p^{nN}: `dmass ≤ trueDmass ≤
        dmass + env`; squeeze (`tendsto_of_tendsto_of_tendsto_of_le_of_le`, upper
        leg `hd.add henv` + `add_zero`).
hypothesis_fields: none as stated (`VPSound X` explicit — instantiated at U10 from
        `cl10_vpsound`); the derivation itself is unconditional arithmetic +
        counting, NOT a fifth tag-free note-step (the note carries this clause
        inside Theorem U's conditional sentence, and it rides VP-SOUND/CL-4's tags
        at U10).
-/
import Mathlib
import LeanUrat.MovesU.U7_squeeze
import LeanUrat.MovesU.DefsLedger

set_option linter.style.longLine false
set_option linter.style.header false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesU
open Filter Topology

/-- Clause (ii), the identification corollary (D10, ruling (B)): under VP-SOUND and
    env → 0, the TRUE-type density is the same limit — the second squeeze. -/
theorem identification {n p : ℕ} (X : ClassifierSpec n p) [NeZero p] (hp : 1 < p)
    (r : ℝ) (σ : SplittingType n) (hvs : VPSound X)
    (hd : Tendsto (X.dmass σ) atTop (𝓝 r))
    (henv : Tendsto X.env atTop (𝓝 0)) :
    Tendsto (X.trueDmass σ) atTop (𝓝 r) :=
  sorry

end LeanUrat.MovesU
