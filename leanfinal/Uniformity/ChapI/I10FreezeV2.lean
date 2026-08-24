/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapC.C14a
import Uniformity.ChapC.C83
import Uniformity.ChapC.C130a
import Uniformity.ChapE.E63

/-!
# The I.10 tower-instantiation freeze v2: landed carrier core

This file lands exactly the parts of D-TIF-3/D-TIF-4 that are fixed by
`TOWER_INSTANTIATION_FREEZE_V2_2026-08-24.md` and already have source-level Lean types:

* the three live ranges;
* the one terminal receiving field and its compatible level embeddings;
* the input polynomial, multiplicity, stage-key, and exact degree/key-free bindings;
* the finite-live-range correction of E.63's deep-twist target.

Re-home note (CC-0 of `CHAIN_CARRIER_DESIGN_2026-08-24.md`): the first three bullets'
declarations — `StageLive`, `GaugeLive`, `DeepLive`, `TerminalReceiver`, `ArisingCore` —
now live byte-identically in `Uniformity.ChapC.C130a` (same names, same namespace), so the
chapter-C chain-realization carrier can reuse them without importing chapter I.  They are
re-exported here through the import; this file keeps `DeepTwistConjunctLive` and its
anti-drift pin, retargeted (trivially, same fully-qualified names) to the imported copies.

It deliberately does **not** declare `ArisingInput`, `CanonicalLadderConfig`, or
`CanonicalDeepTwistConfig`.  The freeze itself marks the threshold predicate, legal P-locus,
canonical node-point residue homomorphism, synchronized lattice export, separate arena read,
cross-universe transports, four view equalities, and the full non-vacuity witness OPEN.  Giving
any of those an empty or `True` interface would weaken D-TIF-4 and recreate the placeholder this
resolution pass is meant to remove.
-/

set_option linter.style.longLine false

namespace Uniformity.Density.Ladder

open Uniformity.Density.Gauge

/-- The range-corrected local form forced by freeze-v2 finding 2.  Unlike signed E.63, this
does not demand facts at C.83's junk-total off-range indices. -/
def DeepTwistConjunctLive (r : ℕ) {G : Type*} [CommGroup G] {K : Type*} [Field K]
    {L : Type*} [Field L] [Algebra K L] {N : NormSection G}
    (v : ℕ → (G →* Multiplicative ℤ))
    (ρ : ∀ j : ℕ, MonoidHom.ker (v j) →* Lˣ) (q : ℕ → ℤ)
    (A : ℕ → GaugeArena G K N) (R : ℕ → G → K) (w : ℕ → Kˣ) : Prop :=
  ∀ i, Tower.DeepLive r i → VarthetaRes G K L N v ρ q i ∧ WFrame A q R w i

/-- Anti-drift pin: the corrected form is definitionally the freeze's `3 ≤ i ∧ i < r` matrix. -/
theorem deepTwistConjunctLive_iff {r : ℕ} {G : Type*} [CommGroup G] {K : Type*} [Field K]
    {L : Type*} [Field L] [Algebra K L] {N : NormSection G}
    {v : ℕ → (G →* Multiplicative ℤ)}
    {ρ : ∀ j : ℕ, MonoidHom.ker (v j) →* Lˣ} {q : ℕ → ℤ}
    {A : ℕ → GaugeArena G K N} {R : ℕ → G → K} {w : ℕ → Kˣ} :
    DeepTwistConjunctLive r v ρ q A R w ↔
      ∀ i, (3 ≤ i ∧ i < r) → VarthetaRes G K L N v ρ q i ∧ WFrame A q R w i :=
  Iff.rfl

end Uniformity.Density.Ladder

section AxCheck

#print axioms Uniformity.Density.Tower.StageLive
#print axioms Uniformity.Density.Tower.GaugeLive
#print axioms Uniformity.Density.Tower.DeepLive
#print axioms Uniformity.Density.Tower.TerminalReceiver
#print axioms Uniformity.Density.Tower.ArisingCore
#print axioms Uniformity.Density.Ladder.DeepTwistConjunctLive
#print axioms Uniformity.Density.Ladder.deepTwistConjunctLive_iff

end AxCheck
