/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.MovesT.Defs

/-! # T-C7 `ns_null` — THE FINITE-LEVEL FACE of (ns-null) (MOVES 7210–7231). SCOPE
RIDER (binding on every consumer, quoted in T-D12's S-2 row): this corpus states ONLY
the truncated-ratio limit; continuity-from-above and the profinite class NEVER enter.
`Mlev`/`JetTower`/`stateTruncAt`/`nsTruncAt` are Defs §2.5a/§2.10 carriers (the
stateTruncAt/nsTruncAt junk-total `dite` is an E-DEV, MANIFEST). -/

set_option linter.style.longLine false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesT

open Polynomial LeanUrat.Moves LeanUrat.MovesC LeanUrat.MovesD

variable {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
variable {n : ℕ} {pol : CanonPolicy p F}

theorem ns_null {H : History p F} (N₀ : ℕ)
    (Tat : ∀ N', N₀ ≤ N' → TreeModel p F n N' (n * N') pol)
    (Jat : ∀ N' (h : N₀ ≤ N'), JetSetup H n N' (n * N'))
    (Lat : ∀ N' (h : N₀ ≤ N'), NsLumpFamily (Tat N' h) (Jat N' h))
    (htw : JetTower Jat)
    (hzc : ∀ N' h, ZCPack (Jat N' h))
    (hM₀ : ∀ N' h, M₀ (Jat N' h) ≤ Mlev (Jat N' h) N')
    (hMgrow : Filter.Tendsto
      (fun N' : {k // N₀ ≤ k} => Mlev (Jat N'.1 N'.2) N'.1 - M₀ (Jat N'.1 N'.2))
      Filter.atTop Filter.atTop)
    (hne : ∀ N' (h : N₀ ≤ N'), (stateTruncAt Jat N').Nonempty) :
    Filter.Tendsto
      (fun N' : {k // N₀ ≤ k} => (Nat.card ↥(nsTruncAt Jat Lat N'.1) : ℝ)
        / (Nat.card ↥(stateTruncAt Jat N'.1)))
      Filter.atTop (nhds 0) := by
  sorry

end LeanUrat.MovesT
