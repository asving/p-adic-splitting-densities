/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.Moves.Defs
import LeanUrat.Moves.ResVal

/-!
# Moves/L3_liftWeight — EQUAL WEIGHTS: `w(Φ̂) = e·h·g` (§B2-DEF D.5, DEF-9)

`moves_ref`: D.5 EQUAL WEIGHTS; MOVES ~2121-2122.

The standard lift develops in `Φ` in its own displayed slots:
`Φ̂ = Φ^{eg} + Σ_{0≤k<g} t_k·Φ^{ek}`.  Each PRESENT slot `t_k·Φ^{ek}` has
`w(t_k) + ek·h = e·wPrev(t_k) + ek·h = eh(g−k) + ekh = ehg`
(using `hStretch` and the lift's `wPrev(t_k) = h(g−k)`), and the leading slot
`Φ^{eg}` has `w(1) + eg·h = ehg`.  All present slots are tied at `ehg`, so by
`Stage.hK1` (Lemma K1 at the current key `Φ`) the attained slot-minimum — which
is `w(Φ̂)` — equals `ehg`.

The proof provides the explicit `Φ`-adic development `B j = Σ_{k≤g} [j = e·k] c_k`
(`c_k = t_k` for `k<g`, `c_g = 1`), feeds it to `σ.hK1`, and reads the tie off the
existence witness of the slot-minimum.
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace LeanUrat.Moves

open Polynomial

/-- SYN-M5 record (2026-07-30, C1 cluster): this theorem was a verbatim duplicate of
`L3_K1`'s private `w_Phat` (golf Moves#4); the shared proof now lives at
`Moves/ResVal.lean` (`ResVal.w_Phat`, statement-identical) and this unit delegates.
Public statement byte-identical. -/
theorem L3_liftWeight {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F] (σ : Stage p F) (ψ : Polynomial ↥σ.K) (g : ℕ) (hg1 : 1 ≤ g) (Φhat : Polynomial ℤ_[p]) (hlift : IsStandardLift σ ψ g Φhat) (hΦne : Φhat ≠ 0) : σ.w Φhat = (σ.e : ℤ) * σ.h * g :=
  ResVal.w_Phat σ ψ g hg1 Φhat hlift hΦne

end LeanUrat.Moves
