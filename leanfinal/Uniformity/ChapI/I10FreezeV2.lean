/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapC.C14a
import Uniformity.ChapC.C83
import Uniformity.ChapE.E63

/-!
# The I.10 tower-instantiation freeze v2: landed carrier core

This file lands exactly the parts of D-TIF-3/D-TIF-4 that are fixed by
`TOWER_INSTANTIATION_FREEZE_V2_2026-08-24.md` and already have source-level Lean types:

* the three live ranges;
* the one terminal receiving field and its compatible level embeddings;
* the input polynomial, multiplicity, stage-key, and exact degree/key-free bindings;
* the finite-live-range correction of E.63's deep-twist target.

It deliberately does **not** declare `ArisingInput`, `CanonicalLadderConfig`, or
`CanonicalDeepTwistConfig`.  The freeze itself marks the threshold predicate, legal P-locus,
canonical node-point residue homomorphism, synchronized lattice export, separate arena read,
cross-universe transports, four view equalities, and the full non-vacuity witness OPEN.  Giving
any of those an empty or `True` interface would weaken D-TIF-4 and recreate the placeholder this
resolution pass is meant to remove.
-/

set_option linter.style.longLine false

namespace Uniformity.Density.Tower

open Uniformity.Density.Leaf

universe uKt uL

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
variable {π : O} {Kt : Type uKt} [Field Kt] {L : Type uL} [Field L] [Algebra Kt L]

/-- D-TIF-4's range on which stage data may be read. -/
def StageLive (r j : ℕ) : Prop := 1 ≤ j ∧ j ≤ r

/-- D-TIF-4's range on which a gauge read may use `u_(j+1)`. -/
def GaugeLive (r j : ℕ) : Prop := 1 ≤ j ∧ j < r

/-- D-TIF-4's genuinely deep live range. -/
def DeepLive (r j : ℕ) : Prop := 3 ≤ j ∧ j < r

/-- D-TIF-3's single coherent interpretation of the frozen `Kt`: `Kt` is equivalent to the
terminal field `K_r`, while every live `K_j` maps into it through a chain-compatible embedding.

The family `levelHom` is total only because C.83's `DeepTower.fld` is total with junk outside
the live range.  Every law that reads tower data is explicitly range guarded. -/
structure TerminalReceiver (F : KeyFrame O π) (H₀ : ℕ) (hpin : F.Pin H₀) (r : ℕ)
    (T : DeepTower.{0, uKt} F H₀ hpin r) (Kt : Type uKt) [Field Kt] where
  topEquiv : T.fld r ≃+* Kt
  levelHom : (j : ℕ) → T.fld j →+* Kt
  levelHom_terminal : levelHom r = topEquiv.toRingHom
  levelHom_step : ∀ (j : ℕ) (hj1 : 1 ≤ j) (hjr : j < r),
    levelHom j = (levelHom (j + 1)).comp
      ((T.step j hj1 hjr).symm.toRingHom.comp (AdjoinRoot.of (T.ψ j)))

/-- The already-typeable, non-residue part of D-TIF-4's legal GENTOW5-1 instance.

This is named `ArisingCore`, not `ArisingInput`: the latter name is reserved for the full
C.130j carrier after the OPEN C.130d/C.130g--C.130k layers and the §9 witness land. -/
structure ArisingCore (Kt : Type uKt) [Field Kt] (L : Type uL) [Field L] [Algebra Kt L]
    (n : ℕ) where
  π : O
  hπ : Irreducible π
  complete : IsAdicComplete (IsLocalRing.maximalIdeal O) O
  finite : Finite (IsLocalRing.ResidueField O)
  F : KeyFrame O π
  H₀ : ℕ
  hpin : F.Pin H₀
  r : ℕ
  i : ℕ
  hi : StageLive r i
  T : DeepTower.{0, uKt} F H₀ hpin r
  receiver : TerminalReceiver F H₀ hpin r T Kt
  stageKey : Polynomial O
  stageDeg : ℕ
  stageKey_monic : stageKey.Monic
  stageKey_degree : stageKey.natDegree = stageDeg
  F₀ : Polynomial O
  F₀_monic : F₀.Monic
  μ : ℕ
  hμ : 1 ≤ μ
  degree_input : F₀.natDegree = n
  degree_block : n = μ * stageDeg
  keyfree : IsCoprime
    (F₀.map (algebraMap O (FractionRing O)))
    (stageKey.map (algebraMap O (FractionRing O)))

end Uniformity.Density.Tower

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
