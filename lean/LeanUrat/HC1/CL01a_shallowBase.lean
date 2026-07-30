/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.HC1.DefsTower
import LeanUrat.HC1.S1_transHypGate

/-!
# HC1.CL01a_shallowBase — Tshallow stage 0: the shallow-instance base stage (BP5 CL-01a)

**Unit CL-01a** (blueprint `lean/notes/BRIDGE_BP5_CLEANUP_2026-07-30.md` §4 CL-01, split
per REVISION 2 finding 11: CL-01a base stage / CL-01b move witness / CL-01c assembly +
card computation). E-PHASE SKELETON: statements + `sorry` bodies; the def bodies are the
unit's construction slots.

**Informal statement.** Stage 0 of ScratchC6's shallow instance: a degree-1 faithfully
based stage over the prime subfield F₂ = ⊥ of the ambient F = GaloisField 2 2 (= F₄),
with (e₀, h₀) = (1, 1), key Φ = X, parent valuation = the Gauss valuation, K = F_Q = ⊥,
together with its round-5 core (`StageCoreL`).

**Deps.** DefsTower (`IsBaseStage`), Moves DefsL (`StageCoreL`), S1_transHypGate
(the recommended proof route). No prerequisites among BP5 units (CL-01 runs first,
SIDE BRANCH).

**Proof sketch.** RECOMMENDED ROUTE: `S1_transHypGate_a` (PROVED Lean-core in this
corpus) already exhibits exactly this stage — take `TshallowBase :=
S1_transHypGate_a.choose` and read the base/core/pin conjuncts off
`S1_transHypGate_a.choose_spec` (its conjuncts are `IsBaseStage σ ∧ StageCoreL σ ∧
σ.Φ = X ∧ σ.e = 1 ∧ σ.h = 1 ∧ σ.K = ⊥ ∧ TransHyp …`; the TransHyp component is
consumed by CL-01b, not here). FALLBACK (if the choose-route pins prove awkward
downstream): re-home `S1Work.σpin` (S1_transHypGate.lean §F — `private` there, so it
cannot be imported; copy the construction verbatim, do not re-derive).

**E-phase resolutions recorded.**
* The blueprint's "base stage + StageCoreL data" is rendered as one data def
  (`TshallowBase`) plus two Prop certificates (`TshallowBase_isBase`,
  `TshallowBase_pins`); the pins fix exactly what CL-01c's card computation reads
  (key degree 1 via Φ = X, (e,h) = (1,1), residue field = the prime subfield).
* `FQ = ⊥` is NOT pinned separately: `IsBaseStage` carries `σ.K = σ.FQ`, so it follows
  from the `K = ⊥` pin.

**LANDING GATE (§3.1, BINDING).** CL-01a/b/c are SIDE-BRANCH units: while
`C6_alphabetCard`'s sorry is live, nothing negation-shaped — conservatively including
the PROVED `Tshallow` + card-certificate composite (escalation E-2) — lands in the live
tree. This skeleton contains no compiled negation (all bodies `sorry`); the unit's
PROOF develops on a side branch / scratch build, and the compiled artifact lands
atomically with CL-02's fence transition, retargeted at the frozen
`C6_stmt_pre_repair` copy. difficulty: hard-fable (portfolio cap ~400 lines across
CL-01a/b/c). PERMITTED OUTCOME: BLOCKED + the exact missing-constructor list (feeds
adjudication Q-2). hyp: none.
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

namespace LeanUrat.HC1

open Polynomial LeanUrat.Moves

/-- **Tshallow stage 0** (CL-01a construction slot): the degree-1 pinned base stage of
the shallow instance — (e,h) = (1,1), Φ = X, wPrev = gaussVal, K = F_Q = ⊥ ⊆ F₄.
Recommended body: `S1_transHypGate_a.choose` (see the module docstring). -/
noncomputable def TshallowBase : Stage 2 (GaloisField 2 2) :=
  sorry

/-- CL-01a certificate 1: `TshallowBase` is faithfully based (Gauss-valuation base pin,
reps = [C 2], K = F_Q) and carries its round-5 stage core. -/
theorem TshallowBase_isBase : IsBaseStage TshallowBase ∧ StageCoreL TshallowBase := by
  sorry

/-- CL-01a certificate 2: the shallow-instance pins CL-01b/CL-01c consume — key X
(degree 1), (e, h) = (1, 1), residue field the prime subfield F₂ = ⊥. (`FQ = ⊥`
follows via `TshallowBase_isBase.1.2.2`.) -/
theorem TshallowBase_pins :
    TshallowBase.Φ = Polynomial.X ∧ TshallowBase.e = 1 ∧ TshallowBase.h = 1 ∧
    TshallowBase.K = ⊥ := by
  sorry

end LeanUrat.HC1

#print axioms LeanUrat.HC1.TshallowBase_isBase
#print axioms LeanUrat.HC1.TshallowBase_pins
