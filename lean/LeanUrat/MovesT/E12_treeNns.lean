/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.MovesT.Defs

/-! # T-E12 `treeN_ns` — for (ns)-leaf trees TREE-N is REPLACED by the NORMALIZED
capped bound (MOVES 7574–7576): domination + T-C7's vanishing ratio; the raw count
need NOT tend to 0 (§0 refutation record). -/

set_option linter.style.longLine false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesT

open Polynomial LeanUrat.Moves LeanUrat.MovesC LeanUrat.MovesD

variable {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
variable {n : ℕ} {pol : CanonPolicy p F}

theorem treeN_ns (Tr : VTree p F) (H : History p F)
    (hns : H ∈ Tr.chains ∧ Tr.nsLeaf H) (N₀ : ℕ)
    (Tat : ∀ N', N₀ ≤ N' → TreeModel p F n N' (n * N') pol)
    (χat : ∀ N', Fin n → Fin (n * N'))
    (Jat : ∀ N' (h : N₀ ≤ N'), JetSetup H n N' (n * N'))
    (Lat : ∀ N' (h : N₀ ≤ N'), NsLumpFamily (Tat N' h) (Jat N' h))
    (htw : JetTower Jat)
    (hzc : ∀ N' h, ZCPack (Jat N' h))
    (hM₀ : ∀ N' h, M₀ (Jat N' h) ≤ Mlev (Jat N' h) N')
    (hMgrow : Filter.Tendsto
      (fun N' : {k // N₀ ≤ k} => Mlev (Jat N'.1 N'.2) N'.1 - M₀ (Jat N'.1 N'.2))
      Filter.atTop Filter.atTop)
    (hne : ∀ N' (h : N₀ ≤ N'), (stateTruncAt Jat N').Nonempty)
    (hdom : ∀ N' (h : N₀ ≤ N'),
      {x : Box p (n * N') | Tr.fiberAt (Tat N' h) (χat N') x}
      ⊆ nsTruncAt Jat Lat N') :
    Filter.Tendsto
      (fun N' : {k // N₀ ≤ k} => (Nat.card ↥{x : Box p (n * N'.1) |
          Tr.fiberAt (Tat N'.1 N'.2) (χat N'.1) x} : ℝ) / (p : ℝ) ^ (n * N'.1))
      Filter.atTop (nhds 0) := by
  sorry

end LeanUrat.MovesT
