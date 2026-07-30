/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.MovesS.Defs

/-!
# IB-B3 — `bridgeAct`: the tautological ACT operation (bridge campaign BP1)

E-phase skeleton per `lean/notes/BRIDGE_BP1_INSTANCE_2026-07-30.md` §3.3 (the
`act` line of the `bridgeRegData` display) / §4 group B (IB-B3).

UNIT: the ACT active-value operation of the tautological roster,
`bridgeAct g q₀ := if h : g ∈ OKat (q₀ : ℚ) then evalAt (q₀ : ℚ) ⟨g, h⟩ else 0`
(Classical decidability on the OKat membership), plus `bridgeAct_ok` — on the
OKat locus the operation IS the real `MovesS.evalAt` semantics, in EXACTLY
`RegPin.act_pin`'s sentence shape (DefsLedger.lean `act_pin`), so the pin at
the tautological roster is this lemma verbatim.

DEPS: none.  CONSUMERS: IB-B8 (`bridgeRegData.act := bridgeAct`), IB-B10
(`act_pin := bridgeAct_ok`), IB-B15a ((r2)-transport on the active locus).

PROOF SKETCH (R, ~8): `bridgeAct_ok` is `dif_pos hok`; the two membership
witnesses (`h` from the dite, `hok` from the binder) agree by proof
irrelevance, definitional for the `Prop`-valued subtype component.
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesU

open scoped Classical in
/-- IB-B3 (def): the tautological ACT operation — the literal `evalAt` value on
    the OKat locus, junk `0` off it (§3.3's `act` display, verbatim). -/
noncomputable def bridgeAct (g : RatFunc ℚ) (q₀ : ℕ) : ℚ :=
  if h : g ∈ MovesS.OKat (q₀ : ℚ) then MovesS.evalAt (q₀ : ℚ) ⟨g, h⟩ else 0

/-- IB-B3 (law): on the OKat locus `bridgeAct` IS the real active-value
    semantics — `RegPin.act_pin`'s sentence at the tautological roster.
    Sketch: `dif_pos` + proof irrelevance of the membership witness. -/
theorem bridgeAct_ok (g : RatFunc ℚ) (q₀ : ℕ) (hok : g ∈ MovesS.OKat (q₀ : ℚ)) :
    bridgeAct g q₀ = MovesS.evalAt (q₀ : ℚ) ⟨g, hok⟩ := by
  sorry

end LeanUrat.MovesU
