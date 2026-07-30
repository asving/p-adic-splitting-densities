/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.HC2.Defs

/-!
# HC1.V11_minimalCore — HK-02: the 5-clause minimal incompatibility core

Bridge campaign BP2 (`lean/notes/BRIDGE_BP2_HC2K1_2026-07-30.md`, Block K, unit HK-02).
E-PHASE SKELETON: statement + `sorry` body; P-phase proves (routine-opus, est. ~50 lines,
V10 helper patterns copy).

**Unit HK-02 `V11_minimalIncompat`** (blueprint file prescription: NEW file
`HC1/V11_minimalCore.lean` — honored; the E-phase charge's default `HC2/` location is
overridden by the blueprint's explicit prescription, recorded here).

INFORMAL STATEMENT: the 5-clause core — `child_h` (`σ'.h = h★`) + `child_wPrev`
(`σ'.wPrev = σ.w`) + the child's own Stage laws `hStretch`/`hwmul`/`hwult` (free with
`σ' : Stage`, entering through `child_key`/`child_e` so they read at the recorded key and
stretch) + the read-lift τ-bound (the slot weights `σ.w (t_k) = h★·(g−k)` of
`IsReadLift`) — is already CONTRADICTORY at any truly-steep pair, `h★ > e★²·g·σ.h`.

SKETCH (blueprint HK-02): `σ'.w (Φ^{e★g}) = e★²·g·σ.h` by `hwmul` + `hStretch` (through
`child_e`/`child_wPrev`; `Φ ∈ C_{Φ̂}` from the non-corner degree bookkeeping, `e★·g ≥ 2`);
the ultrametric on `Φ^{e★g} = Φ̂ − τ` gives `σ'.w (Φ^{e★g}) ≥ min (h★, σ'.w τ)` with
`σ'.w Φ̂ = h★` (`child_key` + `child_h` + `hwΦ`) and `σ'.w τ ≥ e★·h★ ≥ h★` (the read-lift
τ-bound through `hStretch`, per-slot `e★·h★·(g−k) + e★²·k·σ.h ≥ h★` at `k < g`), so
`e★²·g·σ.h ≥ h★` — contradicting truly-steep.

PURPOSE: extends V10's refuted perimeter (NO `child_slotmin`, NO s/t ties needed); pins
WHICH `TransitionData` fields must change in the task-#44 repair — fences the (S-c)-lite
"drop the ties only" non-candidate (the ties are not the only contradictory clauses).

deps: — (V10 helper patterns copy: `v10_w_one/v10_w_neg/v10_w_pow/v10_w_sum_ge` in
`HC1/V10_transportWindow.lean`, private — re-derive locally in P-phase).
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 400000

namespace LeanUrat.HC1

open Polynomial LeanUrat.Moves LeanUrat.MovesJ

/-- **HK-02 `V11_minimalIncompat`** — the 5-clause minimal incompatibility core: at a
truly-steep read-lift transition (`h★ > e★²·g·σ.h`, non-corner `e★·g ≥ 2`), the clauses
`child_key` (`σ'.Φ = Φ̂`), `child_e` (`σ'.e = e★`), `child_h` (`σ'.h = h★`),
`child_wPrev` (`σ'.wPrev = σ.w`) plus the child's OWN Stage laws
(`hStretch`/`hwmul`/`hwult`/`hwΦ`) and the read-lift slot weights are contradictory
outright — no slot-min, no Bézout ties consumed.  Hypothesis shape = `V10_forcedKeyWeight`
minus `hslot`, plus `child_h`, with steepness strengthened to truly-steep.
[Blueprint BP2 HK-02; deps: — (V10 helper patterns copy); sketch in the module header.] -/
theorem V11_minimalIncompat {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
    (σ σ' : Stage p F) (estar hstar : ℕ) (g : ℕ)
    (ψ : Polynomial ↥σ.K) (Φhat : Polynomial ℤ_[p])
    (hsteep : (estar : ℤ) * (estar : ℤ) * (g : ℤ) * (σ.h : ℤ) < (hstar : ℤ))
    (hEG : 2 ≤ estar * g)
    (hlift : IsReadLift σ ψ g estar hstar Φhat)
    (hkey : σ'.Φ = Φhat) (hce : σ'.e = estar) (hch : σ'.h = hstar)
    (hcw : ∀ x, σ'.wPrev x = σ.w x) :
    False := by
  sorry

end LeanUrat.HC1
