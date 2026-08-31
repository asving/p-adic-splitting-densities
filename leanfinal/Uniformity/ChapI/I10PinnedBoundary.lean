/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapI.I10TauRows
import Uniformity.ChapI.I10LadderLegs

/-!
# Uniformity.ChapI.I10PinnedBoundary — AMENDMENT A-I.9 (O-TAU-2): the normalizer-pinning
socket conjunct, ENACTED, and the collapsed tau boundary [OTAU 2026-08-31]

## AMENDMENT A-I.9 (2026-08-31) — the record

**THE REBIND.**  Two socket-genre bodies gain the `NormalizerPinned` conjunct
(`Aℛ.normalizer = core.T.laurentNormalizer` — TAU's exact `Prop`, definitionally; `Iff.rfl`
pin in the gate below):

* `Uniformity.Density.Tower.C130s18.DeepTwistRealizationData` — the capstone I.10b socket
  body (`CanonicalDeepTwistConfig`'s joint-witness half), conjunct inserted directly after
  the `core.r = r` depth pin; the general application
  `realizedInput_deepTwistConfigData` gains the matching `hN` hypothesis (`rfl` at every
  landed witness).
* `Uniformity.Density.IFC5.CanonicalLadderLiveAt` — the ladder `vartheta` leg's live guard
  (the receive point of the ladder half of the shared vartheta chain), conjunct inserted
  as the first view conjunct.

The LADDER socket body itself (`LadderRealizationData`/`CanonicalLadderConfig`) is
deliberately NOT amended: the ladder vartheta chain receives its witness through
`CanonicalLadderLiveAt`, not through the config (LDR's proof discards the config guard),
and no other ladder-side leg consumes the normalizer — the minimal enactment touches
exactly the two receive points of the vartheta chain.

**THE REFUTATION THAT FORCED IT** (unit TAU, `I10TauRows.lean` +
`runs/wave-c/verdict_TAU2.md`, 2026-08-31): the sockets RECEIVED the normalizer
abstractly; `LaurentNormalizer` carries no coherence law in the height, so the index-2
twist (`DeepTower.topTwistedNormalizer` — the canonical normalizer twisted at the single
top-letter height input by `Λ_top⁻¹`) yields a legal received witness that satisfies
EVERY view conjunct of the pre-amendment socket
(the removed theorem `s2FourTwisted_canonicalDeepTwistConfig`, archived) yet refutes
`KernelSpanAt` at the deep-live level (★ `s2FourTwisted_not_kernelSpanAt`), whence
★★ `s2Four_not_universalKernelSpan`: TWD's universal lattice row was FALSE as stated, and
the only landed general-depth route to the capstone vartheta halves (span + descent) was
provably closed.  The pinning itself is refuted as a free supply
(`s2Four_not_universalPinning`), so it can only enter as a structural guard — exactly
O-TAU-2.

**OWNER AUTHORIZATION** (Asvin, 2026-08-31, mid-session message, verbatim):

> "for row 10, if I understand right, I dont think that is gated on me. If this
> ammendment closes the proof, then it must have been right after all since this is all
> internal stuff"

— i.e. the compile-is-the-validator doctrine (standing sign-off scope, 2026-08-26)
applies to internal socket structure; O-TAU-2 is enacted without further sign-off.
Review row: `docs/REVIEW_QUEUE_2026-08-26.md` row 10, ENACTED (owner-authorized
2026-08-31).

**THE ARCHIVED PRE-AMENDMENT STATE**: commit `2b834da9` (repo HEAD at enactment) — the
un-pinned socket bodies, the retired G10U converses
(`universalVartheta_of_deepTwistField`/`universalGentow_of_deepTwistField`), the retired
exit gate `deepTwistField_iff_universalPerWitness`, and TAU's
`s2FourTwisted_canonicalDeepTwistConfig` are all byte-recoverable there.

**THE DIRECTION (verified explicitly, gate §1)**: both amended `Prop`s sit in PREMISE
position of the signed capstone fields (`deepTwist`'s socket; the `vartheta` leg's guard
inside the `ladder` field's result record), and each amended body IMPLIES its
pre-amendment body verbatim (the `forget` pins below drop the conjunct).  So the
amendment strengthens two premises, i.e. WEAKENS the hypothesis block
`CapstoneHypotheses`, i.e. STRENGTHENS the conditional capstone I.17.
`UniformityStatement`, the `CapstoneHypotheses` field list, and I.15–I.18 are
byte-unchanged (`I10_I15_I18.lean` changes in comments only; its `Iff.rfl` gate pins
re-fire against the amended carrier).

## What this file lands (the FIRED chain — charge 3)

* **§1 gate**: the conjunct IS TAU's `NormalizerPinned` (`Iff.rfl`); the two `forget`
  direction pins (amended body ⟹ pre-amendment body).
* **§2 the collapsed deepTwist boundary**: `UniversalPinnedWiredSiteSupply` (the gentow
  half at pinned witnesses) and ★★ `deepTwistField_of_pinned_descent_site` — the capstone
  `deepTwist` field from `UniversalPinnedGeneratorDescent` (row R5 at pinned witnesses,
  via TAU's ★ `universalPinnedTauSupply_of_descent`: the kernel-span leg is FREE under the
  pin) + the pinned wired-site supply.  **The tau boundary of the deepTwist vartheta half
  is row R5 alone.**
* **§3 the collapsed ladder boundary**: ★★ `ladderVarthetaSupplierLive_of_pinned_descent`
  — the ladder `vartheta` leg from `UniversalPinnedGeneratorDescent` alone (the amended
  guard hands a pinned witness), and `ladderFieldLive₃_of_pinned_boundary` — the signed
  `ladder` field from {package supplier, lb1 supplier, pinned descent}.  **The ladder
  vartheta leg's tau boundary is the SAME row R5 — the two vartheta halves now share one
  tau remainder.**
* **§4 keystone re-fire teeth** (the landed instances ARE pinned, by `rfl`): the depth-4
  keystone fires the AMENDED leanspec-typed I.10b socket
  (`s2Four_canonicalDeepTwistConfig` — the untwisted analogue of TAU's removed theorem),
  and the AMENDED ladder live guard is inhabited at the keystone's own exports at the
  deep-live index 3 (`s2Four_canonicalLadderLiveAt` — the guard's first landed
  inhabitant).  The depth-2 S2 gate instances re-fire upstream
  (`C130s18.s2_deepTwist_socket_application`, `C130sg.s2Frontier_deepTwist_socket`,
  `I10_I15_I18` gate items (d)/(e) — all recompiled byte-unchanged except the one `rfl`
  pin argument).  The twist witness now FAILS the socket at exactly the pin conjunct
  (`s2FourTwisted_not_pinned`), as designed.

## Honesty scope

Nothing here discharges row R5 (`UniversalPinnedGeneratorDescent` — wrap descent +
letter-receiver equalities at pinned witnesses, OPEN-LETTERS) or the gentow/site half
(`UniversalPinnedWiredSiteSupply` — rows C0/C1/C2 at pinned witnesses); both remain open
at general witnesses, inhabited at the wired keystone genre.  The conclusion side of
every signed statement is untouched — the amendment restricts what the capstone DEMANDS,
never what it CONCLUDES.

Cite ledger: **empty** — Lean core over the landed corpus; `#print axioms` footer is the
audit.  Verdict: `runs/wave-c/verdict_OTAU.md`.
-/

set_option linter.style.longLine false
set_option linter.unusedVariables false

noncomputable section

namespace Uniformity.Density.DeepExport

open Uniformity.Density Uniformity.Density.Gauge Uniformity.Density.Tower

universe uE uW uG uKt uL

/-! ## §1 Gate: the conjunct is TAU's exact Prop; the direction pins -/

section Gate

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  {Kt : Type uKt} [Field Kt] {E : Type} [Field E]
  {L : Type uL} [Field L] [Algebra Kt L] {n : ℕ}
  {core : ArisingCore (O := O) Kt L n}

-- (a) [A-I.9 anti-drift] the enacted socket conjunct IS TAU's `NormalizerPinned`,
-- definitionally — no invented strengthening.
example (Aℛ : ChainRealization (O := O) (π := core.π) (F := core.F) (H₀ := core.H₀)
    (hpin := core.hpin) core.T Kt E L) :
    NormalizerPinned Aℛ ↔ Aℛ.normalizer = core.T.laurentNormalizer := Iff.rfl

end Gate

section ForgetPins

variable {O : Type} [CommRing O] [dom : IsDomain O] [dvr : IsDiscreteValuationRing O]
  {K : Type} [Field K]
  {C : Ladder.SlotCarrier O K} {B : Ladder.BlockData C}
  {G : Type uG} [CommGroup G] {Kt : Type uKt} [Field Kt] {L : Type uL} [Field L]
  [Algebra Kt L] {N : Gauge.NormSection G} {v : ℕ → (G →* Multiplicative ℤ)}
  {ρ : ∀ j : ℕ, MonoidHom.ker (v j) →* Lˣ} {q : ℕ → ℤ}

/-- (b) [A-I.9 direction pin, deepTwist half] **the amended socket body implies the
archived pre-amendment body verbatim** (drop the pin conjunct).  Since the socket sits in
PREMISE position of the signed `deepTwist` field, this is the machine half of the
direction check: the amendment weakens the hypothesis block and strengthens the
conditional capstone. -/
theorem deepTwistRealizationData_forget
    {A : ℕ → Gauge.GaugeArena G Kt N} {R : ℕ → G → Kt} {w : ℕ → Ktˣ} {r n : ℕ}
    (h : C130s18.DeepTwistRealizationData.{uE, uG, uKt, uL}
      (dom := dom) (dvr := dvr) C B G Kt L N v ρ q A R w r n) :
    ∃ (E : Type uE) (fE : Field E) (core : ArisingCore (O := O) Kt L n)
      (Aℛ : ChainRealization (O := O) (π := core.π) (F := core.F) (H₀ := core.H₀)
        (hpin := core.hpin) (fieldE := fE) core.T Kt E L)
      (X : RealizedInput core Aℛ)
      (eK : core.T.fld core.i ≃+* K) (eG : G ≃* GaugeLattice.{uG} core.r),
      core.r = r ∧
      SlotViewEq X eK C ∧
      (∃ hC : C = X.stageCarrierTransport eK, BlockViewEq X eK (hC ▸ B)) ∧
      GaugeFamilyViewEq X (N.transport eG)
        (fun j => (v j).comp eG.symm.toMonoidHom)
        (fun j => (ρ j).comp (C130s18.kerComapAlong eG (v j))) q ∧
      ArenaFamilyViewEq X (N.transport eG)
        (fun j => (A j).transport eG)
        (fun j g => R j (eG.symm g)) w := by
  obtain ⟨E, fE, core, Aℛ, X, eK, eG, hr, _hN, hs, hb, hg, ha⟩ := h
  exact ⟨E, fE, core, Aℛ, X, eK, eG, hr, hs, hb, hg, ha⟩

omit dom dvr in
/-- (c) [A-I.9 direction pin, ladder half] the amended live guard implies the archived
pre-amendment guard verbatim (drop the pin conjunct) — same premise-position direction
argument for the `ladder` field's result record. -/
theorem canonicalLadderLiveAt_forget {n i : ℕ}
    (h : IFC5.CanonicalLadderLiveAt.{uG, uKt, uL} C B G Kt L N v ρ q n i) :
    ∃ (_dom : IsDomain O) (_dvr : IsDiscreteValuationRing O)
      (E : Type) (fE : Field E) (core : ArisingCore (O := O) Kt L n)
      (A : ChainRealization (O := O) (π := core.π) (F := core.F)
        (H₀ := core.H₀) (hpin := core.hpin) (fieldE := fE) core.T Kt E L)
      (X : RealizedInput core A)
      (eK : core.T.fld core.i ≃+* K) (eG : G ≃* GaugeLattice.{uG} core.r),
      SlotViewEq X eK C ∧
      (∃ hC : C = X.stageCarrierTransport eK, BlockViewEq X eK (hC ▸ B)) ∧
      GaugeFamilyViewEq X (N.transport eG)
        (fun j => (v j).comp eG.symm.toMonoidHom)
        (fun j => (ρ j).comp (C130s18.kerComapAlong eG (v j))) q ∧
      GaugeLive core.r i := by
  obtain ⟨dom', dvr', E, fE, core, A, X, eK, eG, _hN, hs, hb, hg, hlive⟩ := h
  exact ⟨dom', dvr', E, fE, core, A, X, eK, eG, hs, hb, hg, hlive⟩

end ForgetPins

/-! ## §2 The collapsed deepTwist boundary: row R5 (pinned) + the pinned site supply -/

/-- **[A-I.9] The pinned universal wired-site supply** — the `GentowW` half (rows
C0/C1/C2) at every canonically-normalized arising realization: what the amended socket
demands of the site half.  NEW STATEMENT (review). -/
def UniversalPinnedWiredSiteSupply (n : ℕ) : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (Kt : Type uKt) [Field Kt] (E : Type) [Field E]
    (L : Type uL) [Field L] [Algebra Kt L]
    (core : ArisingCore (O := O) Kt L n)
    (Aℛ : ChainRealization (O := O) (π := core.π) (F := core.F) (H₀ := core.H₀)
      (hpin := core.hpin) core.T Kt E L)
    (X : RealizedInput core Aℛ),
    Aℛ.normalizer = core.T.laurentNormalizer →
    WiredSiteSupply.{uG, uKt, uL} X

/-- Supersession-direction pin: the unpinned site supply implies the pinned one. -/
theorem universalPinnedWiredSiteSupply_of_universal {n : ℕ}
    (h : UniversalWiredSiteSupply.{uG, uKt, uL} n) :
    UniversalPinnedWiredSiteSupply.{uG, uKt, uL} n :=
  fun O _ _ _ Kt _ E _ L _ _ core Aℛ X _ => h O Kt E L core Aℛ X

/-- The pinned tau supply compiles to the pinned universal vartheta supplier (USUP's
reduction at the pinned range). -/
theorem universalPinnedVartheta_of_pinnedTauSupply {n : ℕ}
    (h : UniversalPinnedTauWordDescentSupply.{uG, uKt, uL} n) :
    UniversalPinnedVarthetaSupplier.{uG, uKt, uL} n := by
  intro O _ _ _ Kt _ E _ L _ _ core Aℛ X hN
  exact varthetaPerWitnessExporter_of_tauWordDescent X (h O Kt E L core Aℛ X hN)

/-- The pinned site supply compiles to the pinned universal `GentowW` supplier. -/
theorem universalPinnedGentow_of_pinnedSiteSupply {n : ℕ}
    (h : UniversalPinnedWiredSiteSupply.{uG, uKt, uL} n) :
    UniversalPinnedGentowSupplier.{uG, uKt, uL} n := by
  intro O _ _ _ Kt _ E _ L _ _ core Aℛ X hN
  exact gentowPerWitnessExporter_of_wiredSiteSupply X (h O Kt E L core Aℛ X hN)

/-- ★ **[A-I.9] The capstone `deepTwist` field from the two PINNED supplies** — USUP's
capstone reduction, recomputed at the amended socket. -/
theorem deepTwistField_of_pinned_supplies {n : ℕ}
    (hv : UniversalPinnedTauWordDescentSupply.{uG, uKt, uL} n)
    (hw : UniversalPinnedWiredSiteSupply.{uG, uKt, uL} n) :
    IFC0.DeepTwistField.{uG, uKt, uL} n :=
  deepTwistField_of_pinnedPerWitness
    (universalPinnedVartheta_of_pinnedTauSupply hv)
    (universalPinnedGentow_of_pinnedSiteSupply hw)

/-- ★★ **[A-I.9] THE COLLAPSED deepTwist TAU BOUNDARY — row R5 alone**: the capstone
`deepTwist` field from `UniversalPinnedGeneratorDescent` (row R5 at pinned witnesses:
wrap descent + letter clauses) + the pinned wired-site supply.  The kernel-span row C3 is
GONE from the boundary — free under the pin (TAU's ★
`universalPinnedTauSupply_of_descent`, whose span leg is `kernelSpanAt_of_laurent`).  This
is exactly the reduction TAU promised for the enacted amendment. -/
theorem deepTwistField_of_pinned_descent_site {n : ℕ}
    (hd : UniversalPinnedGeneratorDescent.{uKt, uL} n)
    (hw : UniversalPinnedWiredSiteSupply.{uG, uKt, uL} n) :
    IFC0.DeepTwistField.{uG, uKt, uL} n :=
  deepTwistField_of_pinned_supplies (universalPinnedTauSupply_of_descent hd) hw

end Uniformity.Density.DeepExport

/-! ## §3 The collapsed ladder boundary: the vartheta leg shares row R5 -/

namespace Uniformity.Density.IFC5

open Uniformity.Density
open Uniformity.Density.Tower

universe uW uG uKt uL

/-- ★ **[A-I.9] The ladder vartheta leg from the PINNED universal vartheta supplier** —
the amended guard hands the consumer a PINNED witness, so the pinned supplier fires at it
and G10U's view transport carries the conclusion to the external socket datum.  (LDR's
pre-amendment route needed the UNPINNED supplier for exactly this step.) -/
theorem ladderVarthetaSupplierLive_of_pinnedUniversal {n : ℕ}
    (h : DeepExport.UniversalPinnedVarthetaSupplier.{uG, uKt, uL} n) :
    LadderVarthetaSupplierLive.{uG, uKt, uL} n := by
  intro O _ K _ C B G _ Kt _ L _ _ N v ρ q _hcfg i hi hlive
  obtain ⟨dom, dvr, E, fE, core, Aℛ, X, eK, eG, hN, _hslot, _hblock, hgauge, hilive⟩ :=
    hlive
  letI := dom
  letI := dvr
  letI := fE
  exact DeepExport.varthetaRes_of_perWitness_view X eG hgauge hilive
    (h O Kt E L core Aℛ X hN i ⟨hi, hilive.2⟩)

/-- The ladder vartheta leg from the pinned tau supply (one step further down). -/
theorem ladderVarthetaSupplierLive_of_pinnedTauSupply {n : ℕ}
    (h : DeepExport.UniversalPinnedTauWordDescentSupply.{uG, uKt, uL} n) :
    LadderVarthetaSupplierLive.{uG, uKt, uL} n :=
  ladderVarthetaSupplierLive_of_pinnedUniversal
    (DeepExport.universalPinnedVartheta_of_pinnedTauSupply h)

/-- ★★ **[A-I.9] THE COLLAPSED LADDER TAU BOUNDARY — the same row R5**: the ladder
`vartheta` leg from `UniversalPinnedGeneratorDescent` ALONE.  Post-amendment the two
capstone vartheta halves (deepTwist's and the ladder record's) rest on ONE shared tau
remainder: row R5 at pinned witnesses.  (LDR's span leg — `UniversalKernelSpan`, refuted
by TAU — is gone from the boundary.) -/
theorem ladderVarthetaSupplierLive_of_pinned_descent {n : ℕ}
    (hd : DeepExport.UniversalPinnedGeneratorDescent.{uKt, uL} n) :
    LadderVarthetaSupplierLive.{uG, uKt, uL} n :=
  ladderVarthetaSupplierLive_of_pinnedTauSupply
    (DeepExport.universalPinnedTauSupply_of_descent hd)

/-- ★ **[A-I.9] The signed `ladder` field's post-amendment assembly**: package supplier +
lb1 supplier + row R5 (pinned descent) give the SIGNED field's exact type — the ladder
field's full open content is now `{package, lb1, UniversalPinnedGeneratorDescent}`. -/
theorem ladderFieldLive₃_of_pinned_boundary {n : ℕ}
    (hp : IFC0.LadderPackageSupplier.{uW, uG, uKt, uL} n)
    (hl : IFC0.LadderLB1Supplier.{uW, uG, uKt, uL} n)
    (hd : DeepExport.UniversalPinnedGeneratorDescent.{uKt, uL} n) :
    LadderFieldLive₃.{uW, uG, uKt, uL} n :=
  ladderFieldLive₃_of_suppliers hp hl (ladderVarthetaSupplierLive_of_pinned_descent hd)

end Uniformity.Density.IFC5

/-! ## §4 Keystone re-fire teeth: the landed instances ARE pinned -/

namespace Uniformity.Density.DeepExport

open Uniformity.Density Uniformity.Density.Gauge Uniformity.Density.Tower

universe uG uL

section Wired

open Polynomial IsLocalRing IsDiscreteValuationRing
open Uniformity.Density.Leaf
open Uniformity.Density.Tower.C35b Uniformity.Density.Tower.C80
open Uniformity.Density.Tower.C130s2 Uniformity.Density.Tower.C130s6
open Uniformity.Density.Tower.C130nv Uniformity.Density.Tower.C130np0
open Uniformity.Density.Tower.C130np1 Uniformity.Density.Tower.C130sg
open Uniformity.Density.Tower.C130s17 Uniformity.Density.Tower.C130s18
open Uniformity.Density.Tower.C132nv1 Uniformity.Density.Tower.C132rp10b
open Uniformity.Density.Tower.C136d0 Uniformity.Density.Tower.C136d1
open Uniformity.Density.Tower.C136d2 Uniformity.Density.Tower.C136d3
open Uniformity.Density.Tower.C136e0 Uniformity.Density.Tower.C136t
open Uniformity.Density.Tower.C136r0 Uniformity.Density.Tower.C136r1
open Uniformity.Density.Tower.C136r2 Uniformity.Density.Tower.C136r3
open Uniformity.Density.Tower.C136r4 Uniformity.Density.Tower.C136c0

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)] (h2 : Irreducible (2 : O)) (hq : residueCard O = 2)
variable (L : Type uL) [Field L] [Algebra ((s2DepthFour h2 hq).fld 4) L]
variable [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
variable (w₁ : S2LevelOneThreshold) (w₂ : S2LevelTwoThresholdFour)
  (w₃ : S2LevelThreeThresholdFour) (w₄ : S2LevelFourThresholdFour)
variable {n : ℕ} (F₀ : Polynomial O) (hF₀ : F₀.Monic) (μ : ℕ) (hμ : 1 ≤ μ)
  (hdeg : F₀.natDegree = n) (hblock : n = μ * 16)
  (hcop : IsCoprime (F₀.map (algebraMap O (FractionRing O)))
    ((g16 h2 hq).map (algebraMap O (FractionRing O))))

/-- ★ **[A-I.9 re-fire, deepTwist socket] THE AMENDED SOCKET FIRES AT THE DEPTH-4
KEYSTONE** — the LITERAL capstone I.10b socket body `CanonicalDeepTwistConfig`
(leanspec-typed, `uE = 0` profile, NOW carrying the normalizer pin) holds at the
keystone witness's own exports; the pin argument is `rfl` (TWD's
`s2Four_normalizer_eq_laurent`).  This is the untwisted analogue of TAU's removed
pre-amendment theorem: the canonical witness passes the amended socket where the twisted
witness now fails it (`s2FourTwisted_not_pinned`).  Conditionality: exactly the landed
keystone theorems'. -/
theorem s2Four_canonicalDeepTwistConfig :
    CanonicalDeepTwistConfig.{uG, 0, uL}
      ((s2FourRealizedInputOf h2 hq L w₁ w₂ w₃ w₄
          F₀ hF₀ μ hμ hdeg hblock hcop).stageCarrierTransport
        (RingEquiv.refl ((s2DepthFour h2 hq).fld 4)))
      ((s2FourRealizedInputOf h2 hq L w₁ w₂ w₃ w₄
          F₀ hF₀ μ hμ hdeg hblock hcop).inputBlockTransport
        (RingEquiv.refl ((s2DepthFour h2 hq).fld 4)))
      (GaugeLattice.{uG} 4) ((s2DepthFour h2 hq).fld 4) L
      ((s2FourChainRealization h2 hq L w₁ w₂ w₃ w₄).normalizer.arenaNormSection0.transport
        (gaugeLatticeEquiv 4).symm)
      (gaugeHeightFamily (s2FourRealizedInputOf h2 hq L w₁ w₂ w₃ w₄
        F₀ hF₀ μ hμ hdeg hblock hcop))
      (canonicalResFamily (s2FourRealizedInputOf h2 hq L w₁ w₂ w₃ w₄
        F₀ hF₀ μ hμ hdeg hblock hcop))
      (useHeightFamily (s2FourRealizedInputOf h2 hq L w₁ w₂ w₃ w₄
        F₀ hF₀ μ hμ hdeg hblock hcop))
      (arenaFamily (s2FourRealizedInputOf h2 hq L w₁ w₂ w₃ w₄
        F₀ hF₀ μ hμ hdeg hblock hcop)
        (s2FourCore_one_lt_r h2 hq L F₀ hF₀ μ hμ hdeg hblock hcop))
      (towerReadFamily (s2FourRealizedInputOf h2 hq L w₁ w₂ w₃ w₄
        F₀ hF₀ μ hμ hdeg hblock hcop))
      ((s2FourChainRealization h2 hq L w₁ w₂ w₃ w₄).node.peelUnitFamily) 4 n :=
  realizedInput_deepTwistConfigData
    (s2FourRealizedInputOf h2 hq L w₁ w₂ w₃ w₄ F₀ hF₀ μ hμ hdeg hblock hcop)
    (RingEquiv.refl ((s2DepthFour h2 hq).fld 4))
    (s2FourCore_one_lt_r h2 hq L F₀ hF₀ μ hμ hdeg hblock hcop) rfl

/-- ★ **[A-I.9 re-fire, ladder guard] THE AMENDED LIVE GUARD IS INHABITED AT THE DEPTH-4
KEYSTONE, at the deep-live index `3`** — its first landed inhabitant: the keystone
witness realizes its own exported socket data with the normalizer pin (`rfl`) and
`GaugeLive 4 3`.  So the amended `vartheta` leg's premise is non-vacuous exactly where
the campaign needs it.  Conditionality: exactly the landed keystone theorems'. -/
theorem s2Four_canonicalLadderLiveAt (hj : GaugeLive 4 3) :
    IFC5.CanonicalLadderLiveAt.{uG, 0, uL}
      ((s2FourRealizedInputOf h2 hq L w₁ w₂ w₃ w₄
          F₀ hF₀ μ hμ hdeg hblock hcop).stageCarrierTransport
        (RingEquiv.refl ((s2DepthFour h2 hq).fld 4)))
      ((s2FourRealizedInputOf h2 hq L w₁ w₂ w₃ w₄
          F₀ hF₀ μ hμ hdeg hblock hcop).inputBlockTransport
        (RingEquiv.refl ((s2DepthFour h2 hq).fld 4)))
      (GaugeLattice.{uG} 4) ((s2DepthFour h2 hq).fld 4) L
      ((s2FourChainRealization h2 hq L w₁ w₂ w₃ w₄).normalizer.arenaNormSection0.transport
        (gaugeLatticeEquiv 4).symm)
      (gaugeHeightFamily (s2FourRealizedInputOf h2 hq L w₁ w₂ w₃ w₄
        F₀ hF₀ μ hμ hdeg hblock hcop))
      (canonicalResFamily (s2FourRealizedInputOf h2 hq L w₁ w₂ w₃ w₄
        F₀ hF₀ μ hμ hdeg hblock hcop))
      (useHeightFamily (s2FourRealizedInputOf h2 hq L w₁ w₂ w₃ w₄
        F₀ hF₀ μ hμ hdeg hblock hcop)) n 3 :=
  ⟨inferInstance, inferInstance, FractionRing (Polynomial O), inferInstance,
    s2FourArisingCoreOf h2 hq L F₀ hF₀ μ hμ hdeg hblock hcop,
    s2FourChainRealization h2 hq L w₁ w₂ w₃ w₄,
    s2FourRealizedInputOf h2 hq L w₁ w₂ w₃ w₄ F₀ hF₀ μ hμ hdeg hblock hcop,
    RingEquiv.refl ((s2DepthFour h2 hq).fld 4), MulEquiv.refl _, rfl,
    (s2FourRealizedInputOf h2 hq L w₁ w₂ w₃ w₄
      F₀ hF₀ μ hμ hdeg hblock hcop).slotViewEq _,
    ⟨rfl, (s2FourRealizedInputOf h2 hq L w₁ w₂ w₃ w₄
      F₀ hF₀ μ hμ hdeg hblock hcop).blockViewEq _⟩,
    (s2FourRealizedInputOf h2 hq L w₁ w₂ w₃ w₄
      F₀ hF₀ μ hμ hdeg hblock hcop).gaugeFamilyViewEq, hj⟩

end Wired

end Uniformity.Density.DeepExport

end

/-! ## Axiom footprint — expect Lean core `{propext, Classical.choice, Quot.sound}` only.
Cites consumed: none (everything rests on the Lean-core landed corpus). -/

section AxCheck

#print axioms Uniformity.Density.DeepExport.deepTwistRealizationData_forget
#print axioms Uniformity.Density.DeepExport.canonicalLadderLiveAt_forget
#print axioms Uniformity.Density.DeepExport.UniversalPinnedWiredSiteSupply
#print axioms Uniformity.Density.DeepExport.universalPinnedWiredSiteSupply_of_universal
#print axioms Uniformity.Density.DeepExport.universalPinnedVartheta_of_pinnedTauSupply
#print axioms Uniformity.Density.DeepExport.universalPinnedGentow_of_pinnedSiteSupply
#print axioms Uniformity.Density.DeepExport.deepTwistField_of_pinned_supplies
#print axioms Uniformity.Density.DeepExport.deepTwistField_of_pinned_descent_site
#print axioms Uniformity.Density.IFC5.ladderVarthetaSupplierLive_of_pinnedUniversal
#print axioms Uniformity.Density.IFC5.ladderVarthetaSupplierLive_of_pinnedTauSupply
#print axioms Uniformity.Density.IFC5.ladderVarthetaSupplierLive_of_pinned_descent
#print axioms Uniformity.Density.IFC5.ladderFieldLive₃_of_pinned_boundary
#print axioms Uniformity.Density.DeepExport.s2Four_canonicalDeepTwistConfig
#print axioms Uniformity.Density.DeepExport.s2Four_canonicalLadderLiveAt

end AxCheck
