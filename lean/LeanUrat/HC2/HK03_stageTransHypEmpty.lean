/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.HC1.V10_transportWindow

/-!
# HC2.HK03_stageTransHypEmpty — HK-03: `StageTransHyp`'s steep perimeter is EMPTY

Bridge campaign BP2 (`lean/notes/BRIDGE_BP2_HC2K1_2026-07-30.md`, Block K, unit HK-03).
E-PHASE SKELETON: statement + `sorry` body; P-phase proves (routine-opus, est. ~60 lines).

**Unit HK-03 `stageTransHyp_steep_empty`**.

INFORMAL STATEMENT (blueprint §3.1(d)): `StageTransHyp p F` (HC2/Defs l.200 — the (OLD)
configuration: read-pair lift shape + NEXT-pair steepness `IAug` at the SAME `(e', h')`,
concluding `TransitionCoreL` at that pair + the s/t ties) implies that NO `StageCoreL`
stage admits ANY lawful `(ψ, g, z̄, e', h', s', t', Φ̂)` read instance with `IsReadLift`,
`IAug`, and `2 ≤ e'·g` — the hypothesis is conditionally FALSE at the steep perimeter its
consumers (U17a/U17c) need.

SKETCH (blueprint HK-03): apply the hypothesis at the given instance, get `σ'` +
`TransitionCoreL σ σ' Φ̂ e' h'` with the ties; `V10_forcedKeyWeight` forces
`h' = e'²·g·σ.h`; `σ.w Φ̂ = e'·g·σ.h` for the read lift (the steepness computation,
V10's `hτbound` pattern); then `IAug` reads `h' > e'·σ.w Φ̂ = e'²·g·σ.h` — strict —
contradiction with the forced equality: `False`.

TRANSCRIPTION RESOLUTIONS (recorded per the E-phase charge):
* the blueprint display's `∃ (ψ g e' h' s' t' Φ̂), (binders) ∧ …` gloss is transcribed as
  `StageTransHyp`'s own binder telescope, which includes the recorded residue root
  `z̄ : Fˣ` with `eval₂ σ.K.subtype z̄ ψ = 0` — `zbar` is therefore ADDED to the ∃-list
  (without a root the hypothesis cannot fire; minimal resolution);
* the Bézout-range clause is copied byte-faithfully from `StageTransHyp`
  (`0 ≤ t' ∧ t' < e'`).

ARCHIVAL DISCIPLINE (REVISION 2, finding 7): this theorem is proved PRE-WAVE against the
CURRENT `StageTransHyp`; the HK-06 migration wave renames the subject to
`StageTransHypOld` and mechanically re-points this file — the theorem is the permanent
refuted-shape record of WHY the re-key happened, and is NEVER re-interpreted against the
re-keyed definition.

deps: HK-02 patterns (`HC1/V11_minimalCore.lean`); supply: `V10_forcedKeyWeight`
(`HC1/V10_transportWindow.lean`, PROVED Lean-core).
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 400000

namespace LeanUrat.MovesJ

open Polynomial LeanUrat.Moves

/-- **HK-03 `stageTransHyp_steep_empty`** — the emptiness record: under `StageTransHyp p F`
(the (OLD) same-pair configuration), no `StageCoreL` stage admits a lawful steep read
instance — every `(ψ, g, z̄, e', h', s', t', Φ̂)` with the `StageTransHyp` binder laws,
`IsReadLift`, `IAug`, and `2 ≤ e'·g` is refuted.  Proof route: fire the hypothesis, then
`V10_forcedKeyWeight` + the read-lift key-slot computation force `h' = e'²·g·σ.h` while
`IAug` demands `h' > e'²·g·σ.h`.
[Blueprint BP2 HK-03; deps: HK-02 patterns, `V10_forcedKeyWeight`; sketch + the recorded
∃-list resolution (zbar included) in the module header.] -/
theorem stageTransHyp_steep_empty {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
    (hst : StageTransHyp p F) :
    ∀ σ : Stage p F, StageCoreL σ →
      ¬ ∃ (ψ : Polynomial ↥σ.K) (g : ℕ) (zbar : Fˣ) (e' h' : ℕ) (s' t' : ℤ)
          (Φhat : Polynomial ℤ_[p]),
        (ψ.Monic ∧ ψ.natDegree = g ∧ Irreducible ψ ∧ ψ ≠ Polynomial.X ∧ 1 ≤ g) ∧
        Polynomial.eval₂ σ.K.subtype ((zbar : Fˣ) : F) ψ = 0 ∧
        (1 ≤ e' ∧ 1 ≤ h' ∧ Nat.gcd e' h' = 1 ∧
          (e' : ℤ) * s' + (h' : ℤ) * t' = 1 ∧ 0 ≤ t' ∧ t' < (e' : ℤ)) ∧
        IsReadLift σ ψ g e' h' Φhat ∧ IAug σ Φhat e' h' ∧ 2 ≤ e' * g := by
  sorry

end LeanUrat.MovesJ
