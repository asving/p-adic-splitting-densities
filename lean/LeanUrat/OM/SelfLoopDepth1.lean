/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import LeanUrat.OM.SelfLoopCensusK

/-!
# SelfLoopDepth1 — the depth-1 (k = 1) self-loop census as a genuine `stratumCount1`

**HONEST: this is the k = 1 BASE CASE (general N), an additive anchor; it is NOT progress toward
the OPEN k ≥ 2 census (which is FALSE as a finite-N identity and reduces to `AX_cellRecursion`).**

This leaf wires three already-PROVED lemmas — `StratumOrder1.stratumCount1_eq_cellCard`,
`SelfLoopCensusK.selfLoopChain_succ` / `selfLoopChain_zero`, and
`SelfLoopTower.two_level_census` — into the single depth-1 identity, phrased so the LHS is an actual
`StratumOrder1.stratumCount1` (the genuine order-1 stratum count over `CellMenu.classify1`).

Contents (no `sorry`/`axiom`; every step is a congruence on proven bridges):

* `selfLoopChain_one_iff` — the recursion base: `selfLoopChain 1 g ↔ classify1 g = SL μ`
  (from `selfLoopChain_succ` at `k = 0` and the vacuity of `selfLoopChain 0`).
* `stratumCount1_selfLoop_eq_chain1` — the genuine order-1 self-loop stratum count equals the
  depth-1 chain census over the plain size-`μ` box:
  `stratumCount1 p μ N (selfLoopCell μ) = #{g : monicBox p N μ | selfLoopChain 1 g}`.
* `stratumCount1_selfLoop_eq_inCell` — the same count as the `CellCard.InCell`-fiber card (via
  `stratumCount1_eq_cellCard`), the `CellCard` reading of the depth-1 anchor.
* `two_level_census_depth1_stratum` — the **anchor identity**: the k = 1 specialization of
  `SelfLoopTower.two_level_census` to `c' = some (selfLoopCell μ)`, with the coset-side count
  rewritten back to `stratumCount1`.  It states that the depth-1 (root-pinned, second-level)
  self-loop box fiber has the SAME card as the self-loop-conditioned `GammaPattern` coset — the
  banked two-level census — with the plain single-level count named as `stratumCount1`.

None of these introduce a new hypothesis (in particular NOT `VerdictTranslationInvariant`, which is
provably FALSE for every `k ≥ 1`).  They are pure compositions of proven lemmas.  The step from k = 1
to the general-k chain is exactly the OPEN obligation and is NOT touched here.
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.style.setOption false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

namespace LeanUrat.OM.SelfLoopDepth1

open LeanUrat LeanUrat.OM
open LeanUrat.OM.CellMenu
open LeanUrat.OM.OMCountV2 (NodeConfig)
open LeanUrat.OM.SelfLoopTower
open LeanUrat.OM.SelfLoopCensusK
open LeanUrat.OM.StratumOrder1
open LeanUrat.OM.RestartEquiv (InCellAt)

noncomputable section

variable (p N μ : ℕ) [hp : Fact p.Prime] (c : (ZMod (p ^ N))ˣ) (hN : 0 < N)

/-- **The recursion base (`selfLoopChain_one_iff`).**  A box element has a depth-`1` self-loop chain
iff its order-1 classifier reads the self-loop cell: `selfLoopChain 1 g ↔ classify1 g = SL μ`.
Immediate from `selfLoopChain_succ` at `k = 0` (which peels the level-0 read) and the vacuity of
`selfLoopChain 0` (`selfLoopChain_zero`). -/
theorem selfLoopChain_one_iff (g : QuotientBox.monicBox p N μ) :
    selfLoopChain p N μ c hN 1 g
      ↔ classify1 p g = some (Drainage.selfLoopCell μ) := by
  rw [selfLoopChain_succ p N μ c hN 0 g]
  exact and_iff_left (selfLoopChain_zero p N μ c hN _)

/-- **The depth-1 anchor as a genuine `stratumCount1` (`stratumCount1_selfLoop_eq_chain1`).**  The
genuine order-1 self-loop stratum count over the size-`μ` box equals the depth-`1` self-loop chain
census over the SAME plain box:

    stratumCount1 p μ N (selfLoopCell μ) = #{g : monicBox p N μ | selfLoopChain 1 g}.

HONEST: this is the k = 1 base case; it is NOT the k ≥ 2 census.  Both sides count exactly
`{g | classify1 g = SL μ}` — the LHS by definition of `stratumCount1`, the RHS by
`selfLoopChain_one_iff`. -/
theorem stratumCount1_selfLoop_eq_chain1 :
    stratumCount1 p μ N (Drainage.selfLoopCell μ)
      = Nat.card {g : QuotientBox.monicBox p N μ // selfLoopChain p N μ c hN 1 g} := by
  unfold stratumCount1
  exact Nat.card_congr (Equiv.subtypeEquivRight fun g => (selfLoopChain_one_iff p N μ c hN g).symm)

/-- **The depth-1 anchor as a `CellCard.InCell` fiber (`stratumCount1_selfLoop_eq_inCell`).**  Via
`StratumOrder1.stratumCount1_eq_cellCard`, the genuine order-1 self-loop stratum count is the
`CellCard.InCell`-fiber card of the self-loop cell.  This is the `CellCard` reading of the same
k = 1 base case (still NOT the k ≥ 2 census). -/
theorem stratumCount1_selfLoop_eq_inCell :
    stratumCount1 p μ N (Drainage.selfLoopCell μ)
      = Nat.card {g : QuotientBox.monicBox p N μ // InCell p g (Drainage.selfLoopCell μ)} :=
  stratumCount1_eq_cellCard p μ N (Drainage.selfLoopCell μ)

/-- **THE DEPTH-1 CENSUS ANCHOR (`two_level_census_depth1_stratum`).**

**HONEST: this is the k = 1 BASE CASE (general N), an additive anchor; it is NOT progress toward the
OPEN k ≥ 2 census (which is FALSE as a finite-N identity and reduces to `AX_cellRecursion`).**

The k = 1 specialization of `SelfLoopTower.two_level_census` to the self-loop verdict
`c' = some (selfLoopCell μ)`, with the coset-side count rewritten back to the genuine order-1
`stratumCount1` via `stratumCount1_selfLoop_eq_chain1`.  It states: the depth-1 (root-pinned,
second-level) self-loop box fiber has the SAME cardinality as the self-loop-conditioned
`GammaPattern` coset — the banked two-level census.  The `stratumCount1` on the LHS makes the
"depth-1 self-loop count" an actual `StratumOrder1` stratum count, per the scope's anchor shape.

No new hypothesis is introduced; in particular NOT `VerdictTranslationInvariant` (FALSE for k ≥ 1).
Wired purely from `two_level_census` (PROVED) + the base-case congruences above. -/
theorem two_level_census_depth1_stratum (hμ2 : 2 ≤ μ) (hμN : μ < N) :
    Nat.card {f : QuotientBox.monicBox p N (μ * 1) //
        InCellAt p N 1 μ c f ∧ classify1 p (recenter' p N μ c hN f) = some (Drainage.selfLoopCell μ)}
      = Nat.card {γ : Fin μ → ZMod (p ^ N) //
          GammaPattern p N μ γ ∧ classify1 p (gpoly p N μ hN γ) = some (Drainage.selfLoopCell μ)} :=
  two_level_census p N μ c hN hμ2 hμN (some (Drainage.selfLoopCell μ))

end

end LeanUrat.OM.SelfLoopDepth1
