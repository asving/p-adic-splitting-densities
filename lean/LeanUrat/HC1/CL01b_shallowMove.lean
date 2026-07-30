/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.HC1.CL01a_shallowBase
import LeanUrat.HC1.S9_transStage

/-!
# HC1.CL01b_shallowMove — Tshallow's one increment move (BP5 CL-01b)

**Unit CL-01b** (blueprint `lean/notes/BRIDGE_BP5_CLEANUP_2026-07-30.md` §4 CL-01, split
per REVISION 2 finding 11). E-PHASE SKELETON: statements + `sorry` bodies; the def
bodies are the unit's construction slots.

**Informal statement.** The single g = 2 increment of ScratchC6's shallow instance,
read at `TshallowBase`: descend polynomial ψ = z² + z + 1 (genuinely irreducible over
K₀ = F₂), z̄ = a primitive cube root of unity in F₄ˣ, (e′, h′) = (1, h′) with h′ from
(I-aug) — packaged as the child stage `TshallowChild` (K₁ = F₄ = ⊤, e = 1,
deg Φ₁ = 2) and the full `MoveWitness.inc` (TransHyp + TransitionCoreL + child
`StageCoreL`), exactly what `Tower.move` consumes at CL-01c.

**Deps.** CL-01a (`TshallowBase`), DefsTower (`TransHyp`, `MoveWitness`), Moves DefsL
(`TransitionCoreL`, `StageCoreL`), S9_transStage (the recommended proof route).

**Proof sketch.** RECOMMENDED ROUTE: `S1_transHypGate_a.choose_spec` supplies a
TransHyp at ψ = X² + X + 1, g = 2, e′ = 1 for the chosen base stage (CL-01a's
recommended body); `S9_transStage TshallowBase core hyp hEG` (hEG : 1 < e·g = 2,
`by norm_num` after the e-pin) then produces the enriched child
`⟨σ', TransitionCoreL, StageCoreL σ', σ'.K = nextField z̄, σ'.e = e', σ'.h = h'⟩` —
take `TshallowChild := (S9_transStage …).choose` and assemble
`TshallowMove := .inc ψ 2 Φhat 1 h' z̄ hyp core core'`. The K-pin `TshallowChild.K = ⊤`
reduces to `nextField z̄ = ⊤` (F₂(ω) = F₄: the adjoined primitive cube root generates —
a 4-element ambient forces it); the degree pin `deg Φ₁ = 2` is
`TransitionData.child_key` (deg Φ′ = e′·g·deg Φ = 1·2·1).

**E-phase resolutions recorded.**
* e′ = 1 is PINNED in `TshallowMove_spec` (ScratchC6's shallow spec and S1's gate data);
  h′ is left existential (any h′ with (I-aug) works — S1's gate realizes h′ = 3; the
  CL-01c height computation only needs κ₁ > 0, i.e. h′ ≥ 1, which `Stage.hh` gives).
* `TshallowChild.h` is deliberately NOT pinned (same reason).
* The blueprint's "child core′" is carried inside the `MoveWitness.inc` constructor
  (the F-5 enrichment), not as a separate certificate.

**LANDING GATE (§3.1, BINDING).** SIDE-BRANCH unit — see CL01a_shallowBase's module
docstring; the same gate discipline applies verbatim. difficulty: hard-fable
(portfolio cap shared with CL-01a/c). PERMITTED OUTCOME: BLOCKED + the exact
missing-constructor list (feeds Q-2). hyp: none.
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

namespace LeanUrat.HC1

open Polynomial LeanUrat.Moves

/-- **Tshallow stage 1** (CL-01b construction slot): the child stage of the one g = 2
increment — K₁ = F₄ = ⊤, e = e′ = 1, key degree 2. Recommended body: the
`S9_transStage` witness (see the module docstring). -/
noncomputable def TshallowChild : Stage 2 (GaloisField 2 2) :=
  sorry

/-- CL-01b certificate 1: the child pins CL-01c's card computation reads — full residue
field F₄ (card 4), unramified read e = 1, key degree 2 (so `slotBound 0 = 2/1 = 2`). -/
theorem TshallowChild_pins :
    TshallowChild.K = ⊤ ∧ TshallowChild.e = 1 ∧ TshallowChild.Φ.natDegree = 2 := by
  sorry

/-- **Tshallow's move witness** (CL-01b construction slot): the fully certified
increment `TshallowBase → TshallowChild` — the term `Tower.move` consumes at CL-01c. -/
noncomputable def TshallowMove : MoveWitness TshallowBase TshallowChild :=
  sorry

/-- CL-01b certificate 2: `TshallowMove` IS the shallow increment — an `inc` at
ψ = z² + z + 1, g = 2, e′ = 1 (h′, Φ̂, z̄ existential), carrying the full TransHyp,
the transition core, and the child stage core. -/
theorem TshallowMove_spec :
    ∃ (Φhat : Polynomial ℤ_[2]) (h' : ℕ) (zbar : (GaloisField 2 2)ˣ)
      (hyp : TransHyp TshallowBase (Polynomial.X ^ 2 + Polynomial.X + 1) 2 Φhat 1 h' zbar)
      (core : TransitionCoreL TshallowBase TshallowChild Φhat 1 h' zbar)
      (core' : StageCoreL TshallowChild),
      TshallowMove = MoveWitness.inc (Polynomial.X ^ 2 + Polynomial.X + 1) 2 Φhat 1 h'
        zbar hyp core core' := by
  sorry

end LeanUrat.HC1

#print axioms LeanUrat.HC1.TshallowChild_pins
#print axioms LeanUrat.HC1.TshallowMove_spec
