/-
Unit XG.4 x3Series — the per-σ series identity, DERIVED (finding 12: `hσ` deleted;
`densityOf` DEFINED)  [E-phase: stated, body sorry]
moves_ref: "for each type σ the tree-fiber series sums the full density … [(ns-null)
tag displayed]" + "(3e)-style regrouping (Tonelli, positive terms) yields the per-σ
series identity"; VP-SOUND consumed exactly at the typemult identification (note
finding 13).
sketch: E_σ := {f | S.splitType f = σ} ∖ (⋂Undec ∪ discZero); `decided_covered` +
`fiber_disjoint` + VP show E_σ is exactly the union of the σ-typemult fibers minus null
sets; ADD gives HasSum to frac E_σ; frac(⋂Undec) = 0 (XG.3's chain) and
frac(discZero) = 0 (XF.10) + union_le/mono give frac E_σ = densityOf S σ.
deps: XG.3, XF.10. difficulty: HARD.
hyp_fields: VPSoundP, CountableFiberAdditive (Tonelli, owed), SeriesData's three
coverage fields (blueprint §4) + the XG.3 riders.
-/
import LeanUrat.MovesX.Defs
import LeanUrat.MovesX.XF10
import LeanUrat.MovesX.XG3

namespace LeanUrat.MovesX
set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

theorem x3Series {n : ℕ} (X : XFamily n) (K : XConsts n) (hn : 2 ≤ n)
    (R : X3aRouteP n X K) (NS : NsNullP n X)
    (p : ℕ) [Fact p.Prime] (S : SeriesData n p (X.ctx p))
    (VP : VPSoundP S) (ADD : CountableFiberAdditive S) (σ : SplitType n) :
    HasSum (fun T : { T // S.typemult T = σ } => (X.ctx p).frac (S.fiber T))
      (densityOf S σ) := by
  sorry

end LeanUrat.MovesX
