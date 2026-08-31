/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapC.C130s17
import Uniformity.ChapD.D62w

/-!
# Uniformity.ChapC.C130s18 — the socket gate (chain-carrier node CC-18)

**Chain-carrier node CC-18** (`docs/in-progress/CHAIN_CARRIER_DESIGN_2026-08-24.md` §8 row
C.130gate, §10 row CC-18: *"Land both literal I.10 socket applications, I.10b-to-I.10a
refinement, non-swallowing audit, and live-range lint"*), the SECOND serial acceptance gate
after CC-17.

## What this file lands

1. **The two INTENDED socket bodies as chapter-C data-carriers** —
   `CanonicalLadderConfigData` (the I.10a body of freeze v2 §8, at the landed CC-12 views)
   and `CanonicalDeepTwistConfigData` (the I.10b body: the same ladder clause AND one JOINT
   witness exporting both the ladder and the arena data, with the tower depth `r` pinned to
   that witness per A-I.2(b)).  Both are typed at the EXACT leanspec I.10a/I.10b binder
   blocks (`leanspec/Leanspec/ChapI.lean`, NODES I.10a/I.10b — including I.10b's `r`).  The
   leanspec sockets themselves are READ-ONLY here and their `True` bodies are NOT touched;
   re-signing them at these bodies is a later recorded amendment, gated on this file.
2. **The two LITERAL socket applications** — `realizedInput_ladderConfigData` and
   `realizedInput_deepTwistConfigData`: given a `ChainRealization` and a `RealizedInput` on
   it (CC-17's carrier pair), the exported socket arguments satisfy the intended bodies.
   These are CONDITIONAL in exactly CC-17's sense: no unconditional inhabitant of
   `ChainRealization` is claimed; at the S2 instance the applications fire from CC-17's
   named blocker bundle, never from a `True` body.  **Corrected conditionality
   (2026-08-24, unit SF1):** U13 machine-refuted the original single-ambient
   `S2SourceFrontier` (`leanfinal/scratch/U13_probe.lean` — char-2 `IsEmpty` at the `C 2`
   slot), so CC-17's bundle was re-typed at the SPLIT ambient of
   `S2_SOURCE_PLAN_2026-08-24.md` §2 (valued evaluation ambient `E` / residue-letter
   ambient `L`).  The S2 applications (`s2_ladder_socket_application`,
   `s2_deepTwist_socket_application`) now take the split bundle `S` PLUS the quarantined
   premise `ev : S.LegacyEvaluation` — exactly the U13-refuted single-ambient evaluation
   half, which the packaging into the still-un-split `ChainRealization` requires until the
   plan's SF-3 carrier ripple, and which is UNINHABITABLE at S2.  **[SG-1, 2026-08-25]:**
   after FD-0 machine-refuted the frontier's original depth-two FGMN legs
   (`C130fd0.s2SourceLaws_depthTwo_unsatisfiable`) and SG-0 re-typed them at the honest
   `r = 1` anchoring, the packaging additionally takes the SECOND quarantined premise
   `lf : S.LegacyFGMN` — the depth-two FGMN half, empty at the landed operator readings
   (`C130sg.s2LegacyFGMN_landed_empty`).  The S2 gate's remaining vacuity is therefore
   concentrated in the two named arguments `ev`/`lf`, no longer hidden in the bundle (whose
   split re-type carries CC-17's SF-4 non-vacuity tooth, and whose SG-0 instance
   `C130sg.s2Frontier` is inhabited conditional only on the level-1 threshold source
   datum).
3. **The I.10b → I.10a refinement** at these shapes: `And.left`, mirroring the leanspec §4
   gate item (5a) byte-shape (`canonicalDeepTwistConfigData_to_ladder`).
4. **The NON-SWALLOWING audit**, mechanized: the canonical read is a FREE field of the
   carrier (`twistNode`/`twistRealization`/`twistRealizedInput` — a χ-twist of
   `canonicalRead` is again a full carrier, `rfl`-preserving every other supplied socket
   argument), and therefore NO derivation uniform in the supplied context can produce either
   landed discharge trap's residue hypothesis: `arenaAgreement_not_uniform` defeats
   `Gauge.hvarthetaRes_of_arena_agree`'s agreement clause, `embeddedValue_not_uniform`
   defeats the embedded-`Kt`-unit clause genre of `Gauge.hvarthetaRes_of_tau_letters`.
   Unpacking a socket still leaves exactly the OM-8 L3 descent/agreement goal, as freeze v2
   §8 requires.
5. **The live-range lint**: the bodies assert nothing off the gauge-live range —
   `canonicalLadderConfigData_update_q_zero` (the always-off index `0`),
   `canonicalDeepTwistConfigData_update_offRange` (arbitrary `¬ GaugeLive r j` updates of
   `(A, R, w)`, externally meaningful precisely because the body pins `core.r = r`), and
   `canonicalDeepTwistConfigData_update_q_zero`.

## Non-swallowing grep-tooth (mechanical; run from the repo root — the character classes
keep this documented command itself out of its own sed range)

  sed -n '/SOCKET BODY [S]ECTION/,/NON-SWALLOWING AUDIT [S]ECTION/p' \
    leanfinal/Uniformity/ChapC/C130s18.lean | rg "hvartheta|HVartheta"

MUST return no output (rg exit 1): between the two real markers — the socket bodies, both
literal applications, the refinement, and the S2 gate — neither trap-lemma name nor the
sitewise ϑ-carrier occurs; the traps are consumed ONLY inside the audit section, as audit
subjects.  (The module docstring above names them, which is why the tooth is scoped to the
declaration region.)

## [PK-2/U15, 2026-08-25] — the SF-3 carrier ripple ENACTED

Per `PACKAGING_ROUTE_2026-08-25.md` §4.4: the socket bodies' `∃ (e' f' u' : ℕ) …
ChainRealization … e' f' u'` witness block is replaced by `∃ (E : Type uE) (fE : Field E)
… ChainRealization core.T Kt E L` (the PK-1 retyped carrier — split node, no FGMN legs);
the view conjuncts are UNCHANGED.  The S2 gate theorems drop the two quarantined premises
`ev`/`lf` entirely (their structures survive in C130s17 as the refutation record), so the
S2 applications are conditional on exactly `S : S2SourceFrontier` (+ `IsAdicComplete`) —
at the SG-0 instance, on `w : S2LevelOneThreshold` alone.  The non-swallowing audit
re-runs at the split node (`twistNode` retyped; the χ-freedom argument is unchanged).
Prose above this note describing `ev`/`lf`-conditionality is the pre-ripple record.

## [A-I.9 (O-TAU-2), 2026-08-31] — the normalizer-pinning socket conjunct ENACTED

`DeepTwistRealizationData` gains the conjunct `Aℛ.normalizer = core.T.laurentNormalizer`
(TAU's `NormalizerPinned`, definitionally) right after the `core.r = r` pin, and
`realizedInput_deepTwistConfigData` gains the matching `hN` hypothesis (`rfl` at every
landed witness).  Forced by TAU's index-2 refutation (`I10TauRows.lean`:
`s2Four_not_universalKernelSpan`); enactment record + owner authorization:
`runs/wave-c/verdict_OTAU.md`; boundary consequences: `Uniformity/ChapI/I10PinnedBoundary.lean`.
The LADDER body (`LadderRealizationData`) is deliberately NOT amended — the ladder
vartheta chain's receive point is `IFC5.CanonicalLadderLiveAt` (amended in
`I10LadderLive.lean`), and no other ladder-side leg consumes the normalizer.

## Cite ledger

CITES CONSUMED BY THIS FILE: **none**.  No owner hypothesis, no `sorry`, no new axiom, no
`unsafe`, no `True`-bodied interface.  Axiom footprint Lean-core only (AxCheck footer).
-/

set_option linter.style.longLine false

noncomputable section

namespace Uniformity.Density.Tower.C130s18

open Polynomial IsLocalRing IsDiscreteValuationRing Uniformity.Density
open Uniformity.Density.Leaf Uniformity.Density.Tower
open Uniformity.Density.Tower.C130s2 Uniformity.Density.Tower.C130s17

universe uE uG uKt uL

/-! ## §0 Kernel transport helper

The freeze-§8 bodies quantify the socket's abstract gauge group `G` against the exported
synchronized lattice through an explicit equivalence.  `kerComapAlong` transports an abstract
kernel read along that identification; along `MulEquiv.refl` it is the identity
DEFINITIONALLY, which is what lets the literal applications below close by the CC-12 view
lemmas verbatim. -/

/-- Comap of the kernel of `v ∘ e.symm` into the kernel of `v`, as a monoid hom. -/
def kerComapAlong {G : Type uG} {H : Type*} [CommGroup G] [CommGroup H]
    (e : G ≃* H) (v : G →* Multiplicative ℤ) :
    MonoidHom.ker (v.comp e.symm.toMonoidHom) →* MonoidHom.ker v where
  toFun x := ⟨e.symm x.1, x.2⟩
  map_one' := Subtype.ext (map_one e.symm)
  map_mul' x y := Subtype.ext (map_mul e.symm x.1 y.1)

/-- Anti-drift pin: along `refl` the comap is the identity, definitionally. -/
theorem kerComapAlong_refl {G : Type uG} [CommGroup G] (v : G →* Multiplicative ℤ)
    {L : Type uL} [Field L] (ρ : MonoidHom.ker v →* Lˣ) :
    ρ.comp (kerComapAlong (MulEquiv.refl G) v) = ρ := rfl

/-! ## §1 SOCKET BODY SECTION — the intended I.10a/I.10b bodies at the leanspec binder blocks

The two public `Prop`s below carry the leanspec sockets' EXACT binder blocks
(`{O : Type} [CommRing O] {K : Type} [Field K]`, the block pair, the level data
`(G, Kt, L, N, v, ρ, q)`, the degree `n`; I.10b additionally `(A, R, w)` and `(r n)`).
Because the landed carrier requires `O` to be a DVR domain — data the socket binders do not
carry — those two `Prop`-class facts are part of the existential content, delegated to the
instance-full `...RealizationData` forms.

Per design §8 (post-table note), the bodies quantify over `RealizedInput` and pin the socket
arguments through the four CC-12 live views: `SlotViewEq`, `BlockViewEq` (through the carrier
identification, exactly as CC-12's `CanonicalExportWitness` spells it), `GaugeFamilyViewEq`,
and — for I.10b's joint witness only — `ArenaFamilyViewEq`.  No conjunct is a socket
conclusion, an `HVR`-shaped carrier, or an off-range assertion; the two residue reads stay
unrelated. -/

/-- The instance-full I.10a body: some arising occurrence, realized by the chain carrier,
exports exactly the socket data `(C, B, G, N, v, ρ, q)` at degree `n`. -/
def LadderRealizationData.{uE', uG', uKt', uL'} {O : Type} [CommRing O] [dom : IsDomain O]
    [dvr : IsDiscreteValuationRing O] {K : Type} [Field K]
    (C : Ladder.SlotCarrier O K) (B : Ladder.BlockData C)
    (G : Type uG') [CommGroup G] (Kt : Type uKt') [Field Kt] (L : Type uL') [Field L]
    [Algebra Kt L] (N : Gauge.NormSection G) (v : ℕ → (G →* Multiplicative ℤ))
    (ρ : ∀ j : ℕ, MonoidHom.ker (v j) →* Lˣ) (q : ℕ → ℤ) (n : ℕ) : Prop :=
  ∃ (E : Type uE') (fE : Field E) (core : ArisingCore (O := O) Kt L n)
    (Aℛ : ChainRealization (O := O) (π := core.π) (F := core.F) (H₀ := core.H₀)
      (hpin := core.hpin) (fieldE := fE) core.T Kt E L)
    (X : RealizedInput core Aℛ)
    (eK : core.T.fld core.i ≃+* K) (eG : G ≃* GaugeLattice.{uG'} core.r),
    SlotViewEq X eK C ∧
    (∃ hC : C = X.stageCarrierTransport eK, BlockViewEq X eK (hC ▸ B)) ∧
    GaugeFamilyViewEq X (N.transport eG)
      (fun j => (v j).comp eG.symm.toMonoidHom)
      (fun j => (ρ j).comp (kerComapAlong eG (v j))) q

/-- **The intended NODE I.10a body** (freeze v2 §8, at the landed CC-12 views), typed at the
leanspec `CanonicalLadderConfig` binder block.  The leanspec socket's `True` body is NOT
touched; re-signing it at this body is a later recorded amendment gated on this file. -/
def CanonicalLadderConfigData.{uE', uG', uKt', uL'} {O : Type} [CommRing O] {K : Type} [Field K]
    (C : Ladder.SlotCarrier O K) (B : Ladder.BlockData C)
    (G : Type uG') [CommGroup G] (Kt : Type uKt') [Field Kt] (L : Type uL') [Field L]
    [Algebra Kt L] (N : Gauge.NormSection G) (v : ℕ → (G →* Multiplicative ℤ))
    (ρ : ∀ j : ℕ, MonoidHom.ker (v j) →* Lˣ) (q : ℕ → ℤ) (n : ℕ) : Prop :=
  ∃ (dom : IsDomain O) (dvr : IsDiscreteValuationRing O),
    LadderRealizationData.{uE', uG', uKt', uL'} (dom := dom) (dvr := dvr) C B G Kt L N v ρ q n

/-- The instance-full I.10b joint-witness clause: ONE realized input exports BOTH the ladder
data and the separate arena data, and the socket's tower depth `r` is pinned to that same
witness (`core.r = r`) — A-I.2(b)'s "never a free numeral" rule.

**[A-I.9 (O-TAU-2), 2026-08-31 — STATEMENT CHANGE (socket-body conjunct)]** the existential
additionally pins the received witness's normalizer to the CC-4 canonical Laurent solve:
`Aℛ.normalizer = core.T.laurentNormalizer` (= TAU's `NormalizerPinned Aℛ`, definitionally —
`Iff.rfl` pin in `I10PinnedBoundary.lean`).  FORCED by TAU's machine refutation
(`I10TauRows.lean`, 2026-08-31): the socket previously RECEIVED the normalizer abstractly,
the index-2 twist (`s2FourTwistedRealization`) satisfied every view conjunct yet refuted
`KernelSpanAt` (★★ `s2Four_not_universalKernelSpan`), so TWD's universal lattice row was
provably undischargeable through the received witnesses.  Every LANDED witness is pinned
by `rfl` (TWD `s2Four_normalizer_eq_laurent`; C130s17 `s2RepositoryRealization_normalizer`);
the twist now fails the socket, as designed.  A conjunct added to a premise-position socket
WEAKENS the capstone `deepTwist` field, hence STRENGTHENS the conditional capstone;
`UniformityStatement` and I.15–I.18 are byte-unchanged.  Pre-amendment state archived at
commit `2b834da9`; owner authorization + record: `runs/wave-c/verdict_OTAU.md`. -/
def DeepTwistRealizationData.{uE', uG', uKt', uL'} {O : Type} [CommRing O] [dom : IsDomain O]
    [dvr : IsDiscreteValuationRing O] {K : Type} [Field K]
    (C : Ladder.SlotCarrier O K) (B : Ladder.BlockData C)
    (G : Type uG') [CommGroup G] (Kt : Type uKt') [Field Kt] (L : Type uL') [Field L]
    [Algebra Kt L] (N : Gauge.NormSection G) (v : ℕ → (G →* Multiplicative ℤ))
    (ρ : ∀ j : ℕ, MonoidHom.ker (v j) →* Lˣ) (q : ℕ → ℤ)
    (A : ℕ → Gauge.GaugeArena G Kt N) (R : ℕ → G → Kt) (w : ℕ → Ktˣ)
    (r n : ℕ) : Prop :=
  ∃ (E : Type uE') (fE : Field E) (core : ArisingCore (O := O) Kt L n)
    (Aℛ : ChainRealization (O := O) (π := core.π) (F := core.F) (H₀ := core.H₀)
      (hpin := core.hpin) (fieldE := fE) core.T Kt E L)
    (X : RealizedInput core Aℛ)
    (eK : core.T.fld core.i ≃+* K) (eG : G ≃* GaugeLattice.{uG'} core.r),
    core.r = r ∧
    Aℛ.normalizer = core.T.laurentNormalizer ∧
    SlotViewEq X eK C ∧
    (∃ hC : C = X.stageCarrierTransport eK, BlockViewEq X eK (hC ▸ B)) ∧
    GaugeFamilyViewEq X (N.transport eG)
      (fun j => (v j).comp eG.symm.toMonoidHom)
      (fun j => (ρ j).comp (kerComapAlong eG (v j))) q ∧
    ArenaFamilyViewEq X (N.transport eG)
      (fun j => (A j).transport eG)
      (fun j g => R j (eG.symm g)) w

/-- **The intended NODE I.10b body** (freeze v2 §8 + A-I.2(b)), typed at the leanspec
`CanonicalDeepTwistConfig` binder block INCLUDING the `r` binder.  The first conjunct is the
frozen refinement shape (I.10b → I.10a is `And.left`, by construction); the second is one
JOINT witness certifying the same external `(C, B, G, N, v, ρ, q)` together with the arena
family — so the arena cannot come from a tower unrelated to the input.  The leanspec socket's
`CanonicalLadderConfig ∧ True` body is NOT touched. -/
def CanonicalDeepTwistConfigData.{uE', uG', uKt', uL'} {O : Type} [CommRing O] {K : Type} [Field K]
    (C : Ladder.SlotCarrier O K) (B : Ladder.BlockData C)
    (G : Type uG') [CommGroup G] (Kt : Type uKt') [Field Kt] (L : Type uL') [Field L]
    [Algebra Kt L] (N : Gauge.NormSection G) (v : ℕ → (G →* Multiplicative ℤ))
    (ρ : ∀ j : ℕ, MonoidHom.ker (v j) →* Lˣ) (q : ℕ → ℤ)
    (A : ℕ → Gauge.GaugeArena G Kt N) (R : ℕ → G → Kt) (w : ℕ → Ktˣ)
    (r n : ℕ) : Prop :=
  CanonicalLadderConfigData.{uE', uG', uKt', uL'} C B G Kt L N v ρ q n ∧
  ∃ (dom : IsDomain O) (dvr : IsDiscreteValuationRing O),
    DeepTwistRealizationData.{uE', uG', uKt', uL'} (dom := dom) (dvr := dvr) C B G Kt L N v ρ q A R w r n

/-! ## §2 The two literal socket applications (general carrier form)

The design-§8 C.130gate shape: GIVEN a `ChainRealization` and a `RealizedInput` on it, the
exported socket arguments — CC-12's transported carrier/block and the four export families,
with `G` the genuine `ULift`ed synchronized lattice — satisfy the intended bodies.  The
witness equivalence is `MulEquiv.refl`, under which every transport in the bodies is
DEFINITIONALLY the identity, so the proofs are exactly the CC-12 view lemmas.  Nothing here
claims the carrier pair exists unconditionally: that is CC-17's honestly-blocked frontier. -/

section Applications

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
variable {Kt : Type uKt} [Field Kt] {E : Type uE} [Field E] {L : Type uL} [Field L]
variable [Algebra Kt L]
variable {n : ℕ} {core : ArisingCore (O := O) Kt L n}
variable {Aℛ : ChainRealization (O := O) (π := core.π) (F := core.F)
  (H₀ := core.H₀) (hpin := core.hpin) core.T Kt E L}

/-- ★ **CC-18, literal socket application (I.10a shape)**: the realized input's exported
socket arguments satisfy the intended `CanonicalLadderConfig` body. -/
theorem realizedInput_ladderConfigData (X : RealizedInput core Aℛ)
    {K : Type} [Field K] (eK : core.T.fld core.i ≃+* K) :
    CanonicalLadderConfigData.{uE, uG, uKt, uL} (X.stageCarrierTransport eK) (X.inputBlockTransport eK)
      (GaugeLattice.{uG} core.r) Kt L
      (Aℛ.normalizer.arenaNormSection0.transport (gaugeLatticeEquiv core.r).symm)
      (gaugeHeightFamily X) (canonicalResFamily X) (useHeightFamily X) n :=
  ⟨inferInstance, inferInstance, E, inferInstance, core, Aℛ, X, eK, MulEquiv.refl _,
    X.slotViewEq eK, ⟨rfl, X.blockViewEq eK⟩, X.gaugeFamilyViewEq⟩

/-- ★ **CC-18, literal socket application (I.10b shape, with the A-I.2 `r` binder)**: the
same realized input additionally exports the separate arena family, and the socket depth is
the witness's own `core.r` — pinned, not a numeral.

[A-I.9 (O-TAU-2), 2026-08-31] the application now additionally requires the witness to be
canonically normalized (`hN`) — `rfl` at every landed witness; NOT suppliable at TAU's
index-2 twisted witness, by design (`I10TauRows.s2FourTwisted_not_pinned`). -/
theorem realizedInput_deepTwistConfigData (X : RealizedInput core Aℛ)
    {K : Type} [Field K] (eK : core.T.fld core.i ≃+* K) (hr : 1 < core.r)
    (hN : Aℛ.normalizer = core.T.laurentNormalizer) :
    CanonicalDeepTwistConfigData.{uE, uG, uKt, uL} (X.stageCarrierTransport eK) (X.inputBlockTransport eK)
      (GaugeLattice.{uG} core.r) Kt L
      (Aℛ.normalizer.arenaNormSection0.transport (gaugeLatticeEquiv core.r).symm)
      (gaugeHeightFamily X) (canonicalResFamily X) (useHeightFamily X)
      (arenaFamily X hr) (towerReadFamily X) Aℛ.node.peelUnitFamily core.r n :=
  ⟨realizedInput_ladderConfigData X eK,
    inferInstance, inferInstance, E, inferInstance, core, Aℛ, X, eK, MulEquiv.refl _,
    rfl, hN, X.slotViewEq eK, ⟨rfl, X.blockViewEq eK⟩, X.gaugeFamilyViewEq,
    X.arenaFamilyViewEq hr⟩

end Applications

/-! ## §3 The I.10b → I.10a refinement (leanspec §4 gate item (5a), mirrored) -/

/-- The refinement at the intended bodies: a deep-twist configuration IS a ladder
configuration, by construction (`And.left`) — the machine-checked mirror of the leanspec §4
gate item (5a), at the same implicit-binder shape including `{r : ℕ}`. -/
theorem canonicalDeepTwistConfigData_to_ladder {O : Type} [CommRing O] {K : Type} [Field K]
    {C : Ladder.SlotCarrier O K} {B : Ladder.BlockData C}
    {G : Type uG} [CommGroup G] {Kt : Type uKt} [Field Kt] {L : Type uL} [Field L]
    [Algebra Kt L] {N : Gauge.NormSection G} {v : ℕ → (G →* Multiplicative ℤ)}
    {ρ : ∀ j : ℕ, MonoidHom.ker (v j) →* Lˣ} {q : ℕ → ℤ}
    {A : ℕ → Gauge.GaugeArena G Kt N} {R : ℕ → G → Kt} {w : ℕ → Ktˣ} {n : ℕ}
    {r : ℕ} (hcfg : CanonicalDeepTwistConfigData.{uE, uG, uKt, uL} C B G Kt L N v ρ q A R w r n) :
    CanonicalLadderConfigData.{uE, uG, uKt, uL} C B G Kt L N v ρ q n := hcfg.1

/-! ## §4 The S2 socket applications — conditional on CC-17's split `S2SourceFrontier`
     AND the two quarantined premises `LegacyEvaluation`/`LegacyFGMN`

The gate's S2 instance: the CC-17 conditional constructors feed the general applications.
Everything below inherits EXACTLY CC-17's corrected conditionality (SF1 re-type,
2026-08-24; SG-0 leg re-type, 2026-08-25): `S2SourceFrontier` is the SPLIT-ambient source
frontier with `r = 1`-anchored FGMN legs (inhabited by `C130sg.s2Frontier`, conditional
only on the level-1 threshold source datum), and the packaging into the still-un-split
`ChainRealization` additionally consumes the two quarantined premises
`ev : S.LegacyEvaluation` — the U13-refuted single-ambient evaluation half, empty at S2 —
and `lf : S.LegacyFGMN` — the FD-0-refuted depth-two FGMN half, empty at the landed
operator readings — so every theorem below is explicitly empty-premised at S2 IN `ev`/`lf`
until the plan's SF-3 carrier ripple removes those arguments.  The depth pin is the
witness's own `(s2ArisingCore).r = 2` (definitional), and the S2 gauge-live range is the
single level `j = 1` (the depth-two witness has no live DEEP index — `DeepLive 2 j` is empty
— exactly freeze v2 §9's disclosed limitation; a positive deep regression needs a landed
depth-≥4 witness). -/

section S2Gate

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)] (h2 : Irreducible (2 : O)) (hq : residueCard O = 2)
variable {E : Type uE} [Field E]
variable {L : Type uL} [Field L] [Algebra ((S2DepthTwo h2 hq).fld 2) L]

/-- Depth pin: the S2 arising core's tower depth is `2`, definitionally — the `r` fed to the
I.10b shape below is the witness's own depth, not an unrelated numeral. -/
theorem s2ArisingCore_r [IsAdicComplete (IsLocalRing.maximalIdeal O) O] :
    (s2ArisingCore h2 hq L).r = 2 := rfl

/-- Stage pin: the S2 arising core's live stage is `2`, definitionally. -/
theorem s2ArisingCore_i [IsAdicComplete (IsLocalRing.maximalIdeal O) O] :
    (s2ArisingCore h2 hq L).i = 2 := rfl

/-- ★ **The S2 I.10a socket application, `ev`/`lf`-FREE** ([PK-2/U15, 2026-08-25]:
the two quarantined premises are DELETED with the carrier retype) — conditional on the
CC-17 split frontier ALONE: given `S : S2SourceFrontier`, the concrete `keyAt 2 + 1`
arising occurrence's exported socket arguments satisfy the intended
`CanonicalLadderConfig` body at degree `4`.  At the SG-0 instance (`C130sg.s2Frontier`)
this is the first I.10a-shaped statement of the campaign with NO provably-empty premise —
conditional on exactly `w : S2LevelOneThreshold` + `IsAdicComplete`. -/
theorem s2_ladder_socket_application [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    (S : S2SourceFrontier h2 hq E L) :
    CanonicalLadderConfigData.{uE, uG, 0, uL}
      (S.s2RealizedInput.stageCarrierTransport
        (RingEquiv.refl ((S2DepthTwo h2 hq).fld 2)))
      (S.s2RealizedInput.inputBlockTransport
        (RingEquiv.refl ((S2DepthTwo h2 hq).fld 2)))
      (GaugeLattice.{uG} 2) ((S2DepthTwo h2 hq).fld 2) L
      (S.toCarrier.normalizer.arenaNormSection0.transport
        (gaugeLatticeEquiv 2).symm)
      (gaugeHeightFamily S.s2RealizedInput)
      (canonicalResFamily S.s2RealizedInput)
      (useHeightFamily S.s2RealizedInput) 4 :=
  realizedInput_ladderConfigData S.s2RealizedInput (RingEquiv.refl _)

/-- ★ **The S2 I.10b socket application, `ev`/`lf`-FREE** ([PK-2/U15]) — conditional on
the CC-17 split frontier alone, with the depth binder pinned to the witness's own
`r = 2`. -/
theorem s2_deepTwist_socket_application [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    (S : S2SourceFrontier h2 hq E L) :
    CanonicalDeepTwistConfigData.{uE, uG, 0, uL}
      (S.s2RealizedInput.stageCarrierTransport
        (RingEquiv.refl ((S2DepthTwo h2 hq).fld 2)))
      (S.s2RealizedInput.inputBlockTransport
        (RingEquiv.refl ((S2DepthTwo h2 hq).fld 2)))
      (GaugeLattice.{uG} 2) ((S2DepthTwo h2 hq).fld 2) L
      (S.toCarrier.normalizer.arenaNormSection0.transport
        (gaugeLatticeEquiv 2).symm)
      (gaugeHeightFamily S.s2RealizedInput)
      (canonicalResFamily S.s2RealizedInput)
      (useHeightFamily S.s2RealizedInput)
      (arenaFamily S.s2RealizedInput Nat.one_lt_two)
      (towerReadFamily S.s2RealizedInput)
      S.toCarrier.node.peelUnitFamily 2 4 :=
  realizedInput_deepTwistConfigData S.s2RealizedInput (RingEquiv.refl _)
    Nat.one_lt_two rfl

/-- The S2 refinement fires end-to-end (gate item (5a) at the S2 instance, `ev`/`lf`-free
[PK-2/U15]). -/
example [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    (S : S2SourceFrontier h2 hq E L) :
    CanonicalLadderConfigData.{uE, uG, 0, uL}
      (S.s2RealizedInput.stageCarrierTransport
        (RingEquiv.refl ((S2DepthTwo h2 hq).fld 2)))
      (S.s2RealizedInput.inputBlockTransport
        (RingEquiv.refl ((S2DepthTwo h2 hq).fld 2)))
      (GaugeLattice.{uG} 2) ((S2DepthTwo h2 hq).fld 2) L
      (S.toCarrier.normalizer.arenaNormSection0.transport
        (gaugeLatticeEquiv 2).symm)
      (gaugeHeightFamily S.s2RealizedInput)
      (canonicalResFamily S.s2RealizedInput)
      (useHeightFamily S.s2RealizedInput) 4 :=
  canonicalDeepTwistConfigData_to_ladder (s2_deepTwist_socket_application h2 hq S)

end S2Gate

/-! ## §5 NON-SWALLOWING AUDIT SECTION

The I.10a fence (leanspec, A-I.1): *"The socket may NOT be typed at any condition that
already implies its own carrier"*, naming the two landed traps
`Gauge.hvarthetaRes_of_arena_agree` (D.62: an arena whose residue read agrees with the given
ambient `ρ` through the `Kt → L` embedding discharges `HVarthetaRes` outright) and
`Gauge.hvarthetaRes_of_tau_letters` (D62w: the τ-letter law — the pinned read's values at the
cocycle points are embedded `Kt`-units — does the same).

The audit is MECHANIZED, not prose: the supplied context leaves the canonical read FREE
relative to the arena read.  `twistNode` replaces `canonicalRead` by a χ-twist and everything
else — the realization, the realized input, and every exported socket argument EXCEPT the
pinned ρ — survives unchanged (`rfl` pins below; `twist_supplies_ladderConfigData` re-runs
the literal socket application on the twisted context).  Consequently any derivation of
either trap hypothesis UNIFORM in the supplied context is refuted outright
(`arenaAgreement_not_uniform`, `embeddedValue_not_uniform`): the untwisted and twisted
contexts supply identical socket data up to the ρ-pin, and their two pinned reads cannot both
satisfy the trap clause unless the twist is trivial (resp. embedded).  What remains after
unpacking a socket is exactly the OM-8 L3 descent/agreement goal — reachable (the two
`example`s consuming the traps below) but NOT supplied. -/

section Audit

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
variable {π : O} {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀} {r : ℕ}
variable {W : DeepTower.{0, uKt} F H₀ hpin r}
variable {Kt : Type uKt} [Field Kt] {E : Type uE} [Field E] {L : Type uL} [Field L]
variable [Algebra Kt L]
variable {receiver : TerminalReceiver F H₀ hpin r W Kt} {K : KeyChain W}

/-- AUDIT ([PK-2/U15]: re-run at the SPLIT node, the retyped carrier's leg): replace the
carrier's ambient canonical read by a χ-twisted read.  This
typechecks precisely because `SplitNodePointSource` carries NO law tying `canonicalRead` to
`arenaRead` (or to anything else) — the freedom the non-swallowing fence protects. -/
def twistNode (S : SplitNodePointSource (L := L) W E receiver K)
    (χ : (i : ℕ) → MonoidHom.ker (levelExponentHeight W i) →* Lˣ) :
    SplitNodePointSource (L := L) W E receiver K :=
  { S with canonicalRead := fun i => S.canonicalRead i * χ i }

@[simp] theorem twistNode_canonicalRead (S : SplitNodePointSource (L := L) W E receiver K)
    (χ : (i : ℕ) → MonoidHom.ker (levelExponentHeight W i) →* Lˣ) (i : ℕ) :
    (twistNode S χ).canonicalRead i = S.canonicalRead i * χ i := rfl

/-- The twist does not move the SEPARATE arena read (nor any other field). -/
@[simp] theorem twistNode_arenaRead (S : SplitNodePointSource (L := L) W E receiver K)
    (χ : (i : ℕ) → MonoidHom.ker (levelExponentHeight W i) →* Lˣ) :
    (twistNode S χ).arenaRead = S.arenaRead := rfl

/-- The level-χ character read through the synchronized `ULift` kernel at a gauge-live
level — the exact factor by which the twist shifts the pinned canonical export. -/
def liftKerHom (T : DeepTower.{0, uKt} F H₀ hpin r) {j : ℕ} (hj : GaugeLive r j) :
    MonoidHom.ker (levelHeight T ⟨j, hj⟩ : GaugeLattice.{uG} r →* Multiplicative ℤ) →*
      MonoidHom.ker (levelExponentHeight T j) :=
  (kerLevelProj0 T ⟨j, hj⟩).comp (kerGaugeEquiv T ⟨j, hj⟩).toMonoidHom

end Audit

section AuditRealization

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
variable {Kt : Type uKt} [Field Kt] {E : Type uE} [Field E] {L : Type uL} [Field L]
variable [Algebra Kt L]
variable {n : ℕ} {core : ArisingCore (O := O) Kt L n}
variable {Aℛ : ChainRealization (O := O) (π := core.π) (F := core.F)
  (H₀ := core.H₀) (hpin := core.hpin) core.T Kt E L}

/-- AUDIT ([PK-2/U15]: re-run at the retyped carrier — the deleted FGMN legs consumed no
canonical read either, so the audit only gets STRONGER): the χ-twisted node still assembles
into a full `ChainRealization` — no law of the realization mentions the canonical read. -/
def twistRealization
    (Aℛ : ChainRealization (O := O) (π := core.π) (F := core.F)
      (H₀ := core.H₀) (hpin := core.hpin) core.T Kt E L)
    (χ : (i : ℕ) → MonoidHom.ker (levelExponentHeight core.T i) →* Lˣ) :
    ChainRealization (O := O) (π := core.π) (F := core.F)
      (H₀ := core.H₀) (hpin := core.hpin) core.T Kt E L where
  receiver := Aℛ.receiver
  keys := Aℛ.keys
  normalizer := Aℛ.normalizer
  node := twistNode Aℛ.node χ

/-- AUDIT: the realized input survives the twist verbatim. -/
def twistRealizedInput (X : RealizedInput core Aℛ)
    (χ : (i : ℕ) → MonoidHom.ker (levelExponentHeight core.T i) →* Lˣ) :
    RealizedInput core (twistRealization Aℛ χ) where
  receiver_eq := X.receiver_eq
  stageKey_eq := X.stageKey_eq
  stageDeg_eq := X.stageDeg_eq
  point := X.point
  point_mem := X.point_mem

/-- The twist moves the pinned canonical export by EXACTLY the lifted χ-factor. -/
theorem canonicalResAt_twist (X : RealizedInput core Aℛ)
    (χ : (i : ℕ) → MonoidHom.ker (levelExponentHeight core.T i) →* Lˣ)
    {j : ℕ} (hj : GaugeLive core.r j) :
    canonicalResAt (twistRealizedInput X χ) hj
      = (canonicalResAt X hj : MonoidHom.ker (levelHeight core.T ⟨j, hj⟩ :
            GaugeLattice.{uG} core.r →* Multiplicative ℤ) →* Lˣ)
          * ((χ j).comp (liftKerHom core.T hj)) := rfl

/-- The twist does NOT move the pinned arena export. -/
theorem arenaReadAt_twist (X : RealizedInput core Aℛ)
    (χ : (i : ℕ) → MonoidHom.ker (levelExponentHeight core.T i) →* Lˣ)
    {j : ℕ} (hj : GaugeLive core.r j) :
    arenaReadAt (twistRealizedInput X χ) hj
      = (arenaReadAt X hj : MonoidHom.ker (levelHeight core.T ⟨j, hj⟩ :
            GaugeLattice.{uG} core.r →* Multiplicative ℤ) →* Ktˣ) := rfl

/-- AUDIT: the twisted context supplies the SAME literal I.10a socket data — identical
`(C, B, G, N, v, q)` exports; only the pinned ρ becomes the twisted read.  Together with the
defeat theorems below this is the mechanized non-swallowing statement: the socket data do not
determine any relation between the pinned ρ and the arena read. -/
theorem twist_supplies_ladderConfigData (X : RealizedInput core Aℛ)
    (χ : (i : ℕ) → MonoidHom.ker (levelExponentHeight core.T i) →* Lˣ)
    {K : Type} [Field K] (eK : core.T.fld core.i ≃+* K) :
    CanonicalLadderConfigData.{uE, uG, uKt, uL} (X.stageCarrierTransport eK) (X.inputBlockTransport eK)
      (GaugeLattice.{uG} core.r) Kt L
      (Aℛ.normalizer.arenaNormSection0.transport (gaugeLatticeEquiv core.r).symm)
      (gaugeHeightFamily X) (canonicalResFamily (twistRealizedInput X χ))
      (useHeightFamily X) n :=
  realizedInput_ladderConfigData (twistRealizedInput X χ) eK

/-- ★ **NON-SWALLOWING, trap 1 defeated** (`Gauge.hvarthetaRes_of_arena_agree`).  No
derivation UNIFORM in the supplied context can produce the trap's canonical/arena agreement
hypothesis: the untwisted and χ-twisted contexts are both instances of the supplied context,
and their pinned reads cannot both agree with the (unchanged) arena read unless the lifted
χ-factor is trivial at every kernel point. -/
theorem arenaAgreement_not_uniform (X : RealizedInput core Aℛ) {j : ℕ}
    (hj : GaugeLive core.r j)
    (χ : (i : ℕ) → MonoidHom.ker (levelExponentHeight core.T i) →* Lˣ)
    (x₀ : MonoidHom.ker (levelHeight core.T ⟨j, hj⟩ :
      GaugeLattice.{uG} core.r →* Multiplicative ℤ))
    (hχ : (χ j) (liftKerHom core.T hj x₀) ≠ 1)
    (hagree : ∀ (A' : ChainRealization (O := O) (π := core.π) (F := core.F)
        (H₀ := core.H₀) (hpin := core.hpin) core.T Kt E L)
      (X' : RealizedInput core A')
      (x : MonoidHom.ker (levelHeight core.T ⟨j, hj⟩ :
        GaugeLattice.{uG} core.r →* Multiplicative ℤ)),
      ((canonicalResAt X' hj x : Lˣ) : L)
        = algebraMap Kt L ((arenaReadAt X' hj x : Ktˣ) : Kt)) :
    False := by
  have h1 := hagree Aℛ X x₀
  have h2 := hagree (twistRealization Aℛ χ) (twistRealizedInput X χ) x₀
  rw [canonicalResAt_twist X χ hj, arenaReadAt_twist X χ hj,
    MonoidHom.mul_apply, MonoidHom.comp_apply, Units.val_mul] at h2
  have hu : canonicalResAt X hj x₀ * (χ j) (liftKerHom core.T hj x₀)
      = canonicalResAt X hj x₀ * 1 := by
    rw [mul_one]
    exact Units.ext (by rw [Units.val_mul]; exact h2.trans h1.symm)
  exact hχ (mul_left_cancel hu)

/-- ★ **NON-SWALLOWING, trap 2 defeated** (the `Gauge.hvarthetaRes_of_tau_letters` genre).
The τ-trap consumes, at each cocycle point, the clause that the pinned read's value there is
an EMBEDDED `Kt`-unit.  No uniform-in-the-context derivation of that clause exists either:
if the lifted χ-factor's value at the point avoids the embedded subfield, the untwisted and
twisted contexts cannot both satisfy it. -/
theorem embeddedValue_not_uniform (X : RealizedInput core Aℛ) {j : ℕ}
    (hj : GaugeLive core.r j)
    (χ : (i : ℕ) → MonoidHom.ker (levelExponentHeight core.T i) →* Lˣ)
    (x₀ : MonoidHom.ker (levelHeight core.T ⟨j, hj⟩ :
      GaugeLattice.{uG} core.r →* Multiplicative ℤ))
    (hχ : ∀ y : Kt, (((χ j) (liftKerHom core.T hj x₀) : Lˣ) : L)
      ≠ algebraMap Kt L y)
    (hemb : ∀ (A' : ChainRealization (O := O) (π := core.π) (F := core.F)
        (H₀ := core.H₀) (hpin := core.hpin) core.T Kt E L)
      (X' : RealizedInput core A'),
      ∃ u : Ktˣ, ((canonicalResAt X' hj x₀ : Lˣ) : L) = algebraMap Kt L (u : Kt)) :
    False := by
  obtain ⟨u₁, hu₁⟩ := hemb Aℛ X
  obtain ⟨u₂, hu₂⟩ := hemb (twistRealization Aℛ χ) (twistRealizedInput X χ)
  rw [canonicalResAt_twist X χ hj, MonoidHom.mul_apply, MonoidHom.comp_apply,
    Units.val_mul] at hu₂
  refine hχ ((u₂ : Kt) * (u₁ : Kt)⁻¹) ?_
  rw [map_mul, map_inv₀, ← hu₁]
  refine (eq_mul_inv_iff_mul_eq₀ (Units.ne_zero _)).mpr ?_
  rw [mul_comm]
  exact hu₂

/-- The exact residual, exhibited: WERE the agreement clause ever supplied, the landed trap
would fire at the exported arena family.  The theorems above prove it is NOT supplied — this
example only pins the shape of the OM-8 L3 goal a socket unpack leaves open. -/
example (X : RealizedInput core Aℛ) (hr : 1 < core.r) (j : ℕ) (qz : ℤ)
    (ρ' : MonoidHom.ker ((arenaFamily X hr j :
      Gauge.GaugeArena (GaugeLattice.{uG} core.r) Kt
        (Aℛ.normalizer.arenaNormSection0.transport (gaugeLatticeEquiv core.r).symm))).v →* Lˣ)
    (hagree : ∀ x, ((ρ' x : Lˣ) : L)
      = algebraMap Kt L (((arenaFamily X hr j).res x : Ktˣ) : Kt)) :
    Gauge.HVarthetaRes (GaugeLattice.{uG} core.r) Kt L
      (Aℛ.normalizer.arenaNormSection0.transport (gaugeLatticeEquiv core.r).symm)
      (arenaFamily X hr j).v ρ' qz :=
  Gauge.hvarthetaRes_of_arena_agree (arenaFamily X hr j) ρ' hagree qz

/-- The τ-trap's residual at the supplied data, exhibited the same way: only the embedded
τ-letter clause is missing, and the defeat theorem above shows the supplied context cannot
be made to yield it uniformly. -/
example (X : RealizedInput core Aℛ) {j : ℕ} (hj : GaugeLive core.r j) (qz : ℤ)
    (hτker : ∀ s : ℕ,
      (Aℛ.normalizer.arenaNormSection0.transport (gaugeLatticeEquiv core.r).symm).tau
          ((s : ℤ) * qz) qz
        ∈ MonoidHom.ker (levelHeight core.T ⟨j, hj⟩ :
            GaugeLattice.{uG} core.r →* Multiplicative ℤ))
    (hτK : ∀ s : ℕ, ∃ u : Ktˣ,
      ((canonicalResAt X hj ⟨_, hτker s⟩ : Lˣ) : L) = algebraMap Kt L (u : Kt)) :
    Gauge.HVarthetaRes (GaugeLattice.{uG} core.r) Kt L
      (Aℛ.normalizer.arenaNormSection0.transport (gaugeLatticeEquiv core.r).symm)
      (levelHeight core.T ⟨j, hj⟩) (canonicalResAt X hj) qz :=
  Gauge.hvarthetaRes_of_tau_letters _ _ qz hτker hτK

end AuditRealization

/-! ### The audit at the S2 instance

Conditional on CC-17's split frontier alone ([PK-2/U15]: the quarantined legacy premises
are deleted with the carrier retype) — the S2 socket application's ϑ-conjunct
cannot be discharged by the arena-agreement trap from the supplied data: the defeat fires at
the single S2 gauge-live level `j = 1`. -/

section AuditS2

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)] (h2 : Irreducible (2 : O)) (hq : residueCard O = 2)
variable {E : Type uE} [Field E]
variable {L : Type uL} [Field L] [Algebra ((S2DepthTwo h2 hq).fld 2) L]

/-- The non-swallowing defeat at the S2 gate instance, `ev`/`lf`-FREE ([PK-2/U15]):
conditional on the CC-17 split frontier alone, no uniform derivation over the S2
supplied context yields the arena-agreement clause at any gauge-live level (`j = 1` is the
only one at depth two). -/
theorem s2_arenaAgreement_not_uniform [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    (S : S2SourceFrontier h2 hq E L)
    {j : ℕ} (hj : GaugeLive 2 j)
    (χ : (i : ℕ) → MonoidHom.ker (levelExponentHeight (S2DepthTwo h2 hq) i) →* Lˣ)
    (x₀ : MonoidHom.ker (levelHeight (S2DepthTwo h2 hq) ⟨j, hj⟩ :
      GaugeLattice.{uG} 2 →* Multiplicative ℤ))
    (hχ : (χ j) (liftKerHom (S2DepthTwo h2 hq) hj x₀) ≠ 1)
    (hagree : ∀ (A' : ChainRealization (s2DepthTwo h2 hq) ((S2DepthTwo h2 hq).fld 2) E L)
      (X' : RealizedInput (s2ArisingCore h2 hq L) A')
      (x : MonoidHom.ker (levelHeight (S2DepthTwo h2 hq) ⟨j, hj⟩ :
        GaugeLattice.{uG} 2 →* Multiplicative ℤ)),
      ((canonicalResAt X' hj x : Lˣ) : L)
        = algebraMap ((S2DepthTwo h2 hq).fld 2) L
            ((arenaReadAt X' hj x : ((S2DepthTwo h2 hq).fld 2)ˣ) :
              (S2DepthTwo h2 hq).fld 2)) :
    False :=
  arenaAgreement_not_uniform S.s2RealizedInput hj χ x₀ hχ hagree

end AuditS2

/-! ## §6 Live-range lint — off-range assertions absent

The bodies pin the export families only at gauge-live indices, so off-range updates are
invisible.  For the I.10a body the tower depth is existential, so the externally checkable
off-range index is `0` (gauge-live for NO depth); for the I.10b body the `core.r = r` pin
makes EVERY `¬ GaugeLive r j` index externally off-range for the `(A, R, w)` families. -/

section Lint

variable {O : Type} [CommRing O] {K : Type} [Field K]
variable {C : Ladder.SlotCarrier O K} {B : Ladder.BlockData C}
variable {G : Type uG} [CommGroup G] {Kt : Type uKt} [Field Kt] {L : Type uL} [Field L]
variable [Algebra Kt L] {N : Gauge.NormSection G} {v : ℕ → (G →* Multiplicative ℤ)}
variable {ρ : ∀ j : ℕ, MonoidHom.ker (v j) →* Lˣ} {q : ℕ → ℤ} {n : ℕ}

/-- LINT (I.10a): index `0` is gauge-live at no depth; updating `q` there is invisible. -/
theorem canonicalLadderConfigData_update_q_zero (q₀ : ℤ) :
    CanonicalLadderConfigData.{uE, uG, uKt, uL} C B G Kt L N v ρ q n ↔
      CanonicalLadderConfigData.{uE, uG, uKt, uL} C B G Kt L N v ρ (Function.update q 0 q₀) n := by
  constructor
  · rintro ⟨dom, dvr, E, fE, core, Aℛ, X, eK, eG, hslot, hblock, hgauge⟩
    exact ⟨dom, dvr, E, fE, core, Aℛ, X, eK, eG, hslot, hblock,
      (gaugeFamilyViewEq_offRange_unconstrained X _ _ _ _
        (fun h => Nat.not_succ_le_zero 0 h.1) q₀).mp hgauge⟩
  · rintro ⟨dom, dvr, E, fE, core, Aℛ, X, eK, eG, hslot, hblock, hgauge⟩
    exact ⟨dom, dvr, E, fE, core, Aℛ, X, eK, eG, hslot, hblock,
      (gaugeFamilyViewEq_offRange_unconstrained X _ _ _ _
        (fun h => Nat.not_succ_le_zero 0 h.1) q₀).mpr hgauge⟩

variable {A : ℕ → Gauge.GaugeArena G Kt N} {R : ℕ → G → Kt} {w : ℕ → Ktˣ} {r : ℕ}

/-- LINT (I.10b): at any index off the `r`-live gauge range — externally meaningful because
the body pins `core.r = r` — updates of the arena, tower-read, and peel-unit families are
invisible. -/
theorem canonicalDeepTwistConfigData_update_offRange {j : ℕ} (hj : ¬ GaugeLive r j)
    (Aj : Gauge.GaugeArena G Kt N) (Rj : G → Kt) (wj : Ktˣ) :
    CanonicalDeepTwistConfigData.{uE, uG, uKt, uL} C B G Kt L N v ρ q A R w r n ↔
      CanonicalDeepTwistConfigData.{uE, uG, uKt, uL} C B G Kt L N v ρ q
        (Function.update A j Aj) (Function.update R j Rj) (Function.update w j wj) r n := by
  constructor
  · rintro ⟨hl, dom, dvr, E, fE, core, Aℛ, X, eK, eG, hrpin, hNpin, hslot, hblock, hgauge,
      harena⟩
    subst hrpin
    refine ⟨hl, dom, dvr, E, fE, core, Aℛ, X, eK, eG, rfl, hNpin, hslot, hblock, hgauge, ?_⟩
    intro k hk
    have hkj : k ≠ j := fun e => hj (e ▸ hk)
    beta_reduce
    rw [Function.update_of_ne hkj, Function.update_of_ne hkj, Function.update_of_ne hkj]
    exact harena k hk
  · rintro ⟨hl, dom, dvr, E, fE, core, Aℛ, X, eK, eG, hrpin, hNpin, hslot, hblock, hgauge,
      harena⟩
    subst hrpin
    refine ⟨hl, dom, dvr, E, fE, core, Aℛ, X, eK, eG, rfl, hNpin, hslot, hblock, hgauge, ?_⟩
    intro k hk
    have hkj : k ≠ j := fun e => hj (e ▸ hk)
    have h := harena k hk
    beta_reduce at h
    rwa [Function.update_of_ne hkj, Function.update_of_ne hkj,
      Function.update_of_ne hkj] at h

/-- LINT (I.10b): the `q`-update at the always-off index `0` is invisible in BOTH the ladder
conjunct and the joint witness. -/
theorem canonicalDeepTwistConfigData_update_q_zero (q₀ : ℤ) :
    CanonicalDeepTwistConfigData.{uE, uG, uKt, uL} C B G Kt L N v ρ q A R w r n ↔
      CanonicalDeepTwistConfigData.{uE, uG, uKt, uL} C B G Kt L N v ρ (Function.update q 0 q₀) A R w r n := by
  constructor
  · rintro ⟨hl, dom, dvr, E, fE, core, Aℛ, X, eK, eG, hrpin, hNpin, hslot, hblock, hgauge,
      harena⟩
    exact ⟨(canonicalLadderConfigData_update_q_zero q₀).mp hl,
      dom, dvr, E, fE, core, Aℛ, X, eK, eG, hrpin, hNpin, hslot, hblock,
      (gaugeFamilyViewEq_offRange_unconstrained X _ _ _ _
        (fun h => Nat.not_succ_le_zero 0 h.1) q₀).mp hgauge, harena⟩
  · rintro ⟨hl, dom, dvr, E, fE, core, Aℛ, X, eK, eG, hrpin, hNpin, hslot, hblock, hgauge,
      harena⟩
    exact ⟨(canonicalLadderConfigData_update_q_zero q₀).mpr hl,
      dom, dvr, E, fE, core, Aℛ, X, eK, eG, hrpin, hNpin, hslot, hblock,
      (gaugeFamilyViewEq_offRange_unconstrained X _ _ _ _
        (fun h => Nat.not_succ_le_zero 0 h.1) q₀).mpr hgauge, harena⟩

end Lint

end Uniformity.Density.Tower.C130s18

/-! ## Axiom footprint and cite ledger

CITES CONSUMED BY THIS FILE: **none**. -/

section AxCheck

#print axioms Uniformity.Density.Tower.C130s18.kerComapAlong
#print axioms Uniformity.Density.Tower.C130s18.kerComapAlong_refl
#print axioms Uniformity.Density.Tower.C130s18.LadderRealizationData
#print axioms Uniformity.Density.Tower.C130s18.CanonicalLadderConfigData
#print axioms Uniformity.Density.Tower.C130s18.DeepTwistRealizationData
#print axioms Uniformity.Density.Tower.C130s18.CanonicalDeepTwistConfigData
#print axioms Uniformity.Density.Tower.C130s18.realizedInput_ladderConfigData
#print axioms Uniformity.Density.Tower.C130s18.realizedInput_deepTwistConfigData
#print axioms Uniformity.Density.Tower.C130s18.canonicalDeepTwistConfigData_to_ladder
#print axioms Uniformity.Density.Tower.C130s18.s2ArisingCore_r
#print axioms Uniformity.Density.Tower.C130s18.s2ArisingCore_i
#print axioms Uniformity.Density.Tower.C130s18.s2_ladder_socket_application
#print axioms Uniformity.Density.Tower.C130s18.s2_deepTwist_socket_application
#print axioms Uniformity.Density.Tower.C130s18.twistNode
#print axioms Uniformity.Density.Tower.C130s18.twistNode_canonicalRead
#print axioms Uniformity.Density.Tower.C130s18.twistNode_arenaRead
#print axioms Uniformity.Density.Tower.C130s18.twistRealization
#print axioms Uniformity.Density.Tower.C130s18.twistRealizedInput
#print axioms Uniformity.Density.Tower.C130s18.liftKerHom
#print axioms Uniformity.Density.Tower.C130s18.canonicalResAt_twist
#print axioms Uniformity.Density.Tower.C130s18.arenaReadAt_twist
#print axioms Uniformity.Density.Tower.C130s18.twist_supplies_ladderConfigData
#print axioms Uniformity.Density.Tower.C130s18.arenaAgreement_not_uniform
#print axioms Uniformity.Density.Tower.C130s18.embeddedValue_not_uniform
#print axioms Uniformity.Density.Tower.C130s18.s2_arenaAgreement_not_uniform
#print axioms Uniformity.Density.Tower.C130s18.canonicalLadderConfigData_update_q_zero
#print axioms Uniformity.Density.Tower.C130s18.canonicalDeepTwistConfigData_update_offRange
#print axioms Uniformity.Density.Tower.C130s18.canonicalDeepTwistConfigData_update_q_zero

end AxCheck
