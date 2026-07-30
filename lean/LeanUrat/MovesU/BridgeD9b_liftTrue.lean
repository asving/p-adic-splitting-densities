/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.MovesU.BridgeD9a_trueTypeDef
import LeanUrat.MovesU.BridgeD10_trueTypeLevel0

/-!
# IB-D9b — (†8u) UNIQUENESS + `lift_true` AT ALL N (bridge campaign BP1, cluster c9)

E-phase skeleton per `lean/notes/BRIDGE_BP1_INSTANCE_2026-07-30.md` §3.4 (†8),
(†8u), the corrected †8 tail (post-Codex finding 6) / §4 group D (IB-D9b) / §5 R5.

INFORMAL STATEMENT: (i) uniqueness — with ONE monic degree-n lift of `f` in hand
(lift-existence, IB-E8's law), any two σ's read at `f` by `ZpReads` agree; (ii)
`lift_true` — `bridgeTrueType n p zf N f = some σ ↔ ZpReads n p zf N f σ`, at
EVERY N INCLUDING 0 (the corrected †8 tail: `ZpReads` is the ∀-lift predicate,
DefsLedger.lean:686–689, re-verified compiled at IB-D10's `zpReads_forall_lift`;
uniqueness rides ONE lift, which lift-existence supplies at every N — at N = 0
the map-to-trivial-ring condition is automatic — so lift_true's N = 0 instance
holds whether or not the "trueType 0 = none" edge is settled).  This is the
`ZpBridge.lift_true` field supply (DefsLedger.lean:734) at the constructed
classifier (IB-D11 / IB-E9).

DEPS: IB-D9a (`bridgeTrueType`), IB-D10 (GATE — ran first, landed:
BridgeD10_trueTypeLevel0.lean; its `zpReads_unique_of_lift` is the consumed
uniqueness core), IB-E8 (`lift_exists`), IB-E10 (zfType-determines-σ transport).
TRANSCRIPTION RESOLUTION (recorded): IB-E8/E10 are Group-E units (another
cluster), not landed — the lift-existence law is a BINDER `hlift` with
`ZpBridge.lift_exists`'s verbatim field type (DefsLedger.lean:732–733); at
consumption (IB-E9) it is instantiated at IB-E8's theorem.  E10's Subtype.ext
transport is absorbed into the sketch (it is how the `zf g = σ.1` equalities
close to `σ = σ'`), exactly as IB-D10's compiled `zpReads_unique_of_lift`
already displays.

PROOF SKETCH (H, ~25): uniqueness = `zpReads_unique_of_lift` at the lift `hlift
N f` provides.  lift_true: unfold `bridgeTrueType`'s dite.  Forward, `some`
branch: `h.choose_spec` reads σ₀ := h.choose; `some σ₀ = some σ` gives σ₀ = σ
by `Option.some.inj`, transport the read.  Forward, `none` branch:
contradiction.  Backward: the read σ witnesses the ∃, so the dite fires `some
h.choose`; `zpReads_unique_of_lift` (at the single lift) forces h.choose = σ.
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesU

/-- (†8u) UNIQUENESS at the instance shape D9b consumes: given lift-EXISTENCE
    (IB-E8's binder, verbatim `ZpBridge.lift_exists`), any two σ's read at `f`
    agree.  Core: IB-D10's compiled `zpReads_unique_of_lift` at the supplied
    lift. -/
theorem bridgeZpReads_unique {n p : ℕ} [Fact p.Prime]
    (zf : Polynomial ℤ_[p] → Multiset (ℕ × ℕ))
    (hlift : ∀ (N : ℕ) (f : Box p n N), ∃ g : Polynomial ℤ_[p],
      g.Monic ∧ g.natDegree = n ∧ g.map (PadicInt.toZModPow N) = f.toPoly)
    (N : ℕ) (f : Box p n N) {σ σ' : SplittingType n}
    (h : ZpReads n p zf N f σ) (h' : ZpReads n p zf N f σ') : σ = σ' := by
  sorry

/-- (†8) `lift_true` AT ALL N (N = 0 included via the single-lift route — the
    corrected †8 tail): the dite-defined `bridgeTrueType` emits σ IFF `ZpReads`
    reads σ.  THE `ZpBridge.lift_true` FIELD SUPPLY (DefsLedger.lean:734) at the
    constructed classifier — wired by IB-E9/IB-D11 with `zf := zfType` (IB-E11)
    and `hlift := lift_exists` (IB-E8). -/
theorem bridgeTrueType_lift_true {n p : ℕ} [Fact p.Prime]
    (zf : Polynomial ℤ_[p] → Multiset (ℕ × ℕ))
    (hlift : ∀ (N : ℕ) (f : Box p n N), ∃ g : Polynomial ℤ_[p],
      g.Monic ∧ g.natDegree = n ∧ g.map (PadicInt.toZModPow N) = f.toPoly)
    (N : ℕ) (f : Box p n N) (σ : SplittingType n) :
    bridgeTrueType n p zf N f = some σ ↔ ZpReads n p zf N f σ := by
  sorry

end LeanUrat.MovesU
