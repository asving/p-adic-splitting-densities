/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.OM.UniformModelN2
import LeanUrat.OM.SeriesAssembly

/-!
# UniformModelN2Recovery — the `p = 2` recovery gate (W6q-b consistency tie)

**Provenance.** `notes/WILD_WAVE6Q_BLUEPRINT_2026-07-22.md` §2-W6q-b (the W6-consistency
gate). At `p = 2` the general-`p` model of `OM/UniformModelN2.lean` collapses EXACTLY onto
the machine-checked W6 model of `OM/SeriesAssembly.lean`:

* the splitU sums VANISH (`chainCountUTot_two`, from the honest-empty pool
  `rootedPairs 2 = ∅` — the blueprint's `(q−1)(q−2)/2 = 0` at `q = 2`);
* the order-0 residual-SHAPE cells decode to W6's digit cells (`ord0Split_two_iff` /
  `ord0Inert_two_iff`);
* the residue points `Finset.range 2 = {0, 1}` are W6's two translates, and the translated
  fibers agree definitionally (`transMapP 2 = transMap`, both `affineEquiv` at `(N, N)`).

Capstone: `decidedCountP_two_eq` (+ `undecidedCountP_two_eq`). This module exists SEPARATELY
so that `UniformModelN2`'s import cone stays light (no `SeriesAssembly`/`RealInstanceW5`).

No `sorry`, no axiom; core-only footprint (`AxCheck`).
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

namespace LeanUrat.OM.UniformModelN2

open scoped Classical
open LeanUrat LeanUrat.OM Finset
open LeanUrat.OM.QuotientBox LeanUrat.OM.CellCard
open LeanUrat.OM.RecenterBox
open LeanUrat.OM.ChainMenu
open LeanUrat.OM.ChainMenuU

/-- At `p = 2` the translated main-chain counts are DEFINITIONALLY W6's (`transMapP 2` IS
`SeriesAssembly.transMap`: both are `affineEquiv` at levels `(N, N)`, `M9.realP ≡ 2`). -/
theorem transChainCountP_two (c : ℕ) (ms : List ℕ) (leaf : ChainLeaf) (N : ℕ) :
    transChainCountP 2 c ms leaf N = SeriesAssembly.transChainCount c ms leaf N := rfl

/-- The order-0 residual-shape cells at `p = 2` count exactly W6's digit cells. -/
theorem ord0Count_two_eq (σ : FactorizationType) (N : ℕ) :
    ord0Count 2 σ N = SeriesAssembly.sepCount6 σ N := by
  unfold ord0Count SeriesAssembly.sepCount6
  by_cases h1 : σ = splitType2
  · rw [if_pos h1, if_pos h1]
    have hcard : Nat.card {a : pairBoxP 2 N // Ord0SplitCell 2 N a}
        = Nat.card {a : SeriesAssembly.pairBox N // SeriesAssembly.SepSplitCell N a} :=
      Nat.card_congr (Equiv.subtypeEquivRight (fun a => ord0Split_two_iff N a))
    rw [hcard]
  · rw [if_neg h1, if_neg h1]
    by_cases h2 : σ = inertType2
    · rw [if_pos h2, if_pos h2]
      have hcard : Nat.card {a : pairBoxP 2 N // Ord0InertCell 2 N a}
          = Nat.card {a : SeriesAssembly.pairBox N // SeriesAssembly.SepInertCell N a} :=
        Nat.card_congr (Equiv.subtypeEquivRight (fun a => ord0Inert_two_iff N a))
      rw [hcard]
    · rw [if_neg h2, if_neg h2]

/-- The chain counts at `p = 2`: the splitU family vanishes and the main double sum is
W6's over the two residue points `{0, 1} = range 2`. -/
theorem chainCountP_two_eq (σ : FactorizationType) (N : ℕ) :
    chainCountP 2 σ N = SeriesAssembly.chainCount6 σ N := by
  have hU : (if σ = splitType2 then chainCountUTot 2 N else 0) = 0 := by
    split_ifs
    · exact chainCountUTot_two N
    · rfl
  unfold chainCountP
  rw [hU, add_zero]
  unfold chainCountMain SeriesAssembly.chainCount6
  rw [show (Finset.range 2 : Finset ℕ) = {0, 1} from by decide]
  refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun x _ => ?_
  rw [transChainCountP_two]

/-- **THE `p = 2` RECOVERY GATE** (blueprint §2-W6q-b): at the wild prime the general-`p`
model's decided count IS the machine-checked W6 decided count, per type and level. -/
theorem decidedCountP_two_eq (σ : FactorizationType) (N : ℕ) :
    decidedCountP 2 σ N = SeriesAssembly.decidedCount6 σ N := by
  unfold decidedCountP SeriesAssembly.decidedCount6
  rw [ord0Count_two_eq, chainCountP_two_eq]

/-- The undecided counts also agree at `p = 2` (box + the three decided ties). -/
theorem undecidedCountP_two_eq (N : ℕ) :
    undecidedCountP 2 N = SeriesAssembly.undecidedCount6 N := by
  unfold undecidedCountP SeriesAssembly.undecidedCount6
  rw [sum_typeMenuP, SeriesAssembly.sum_typeMenu6,
    decidedCountP_two_eq, decidedCountP_two_eq, decidedCountP_two_eq,
    show ((M9.realP : ℕ) : ℚ) = 2 from by norm_num [M9.realP]]
  norm_num

section AxCheck
#print axioms transChainCountP_two
#print axioms ord0Count_two_eq
#print axioms chainCountP_two_eq
#print axioms decidedCountP_two_eq
#print axioms undecidedCountP_two_eq
end AxCheck

end LeanUrat.OM.UniformModelN2
