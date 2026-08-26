/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapI.I01
import Uniformity.ChapI.I02
import Uniformity.ChapI.I03
import Uniformity.ChapI.I05
import Uniformity.ChapI.I06
import Uniformity.ChapI.I07
import Uniformity.ChapI.I10FreezeV2
import Uniformity.ChapE.E24
import Uniformity.ChapC.C130sg
import Uniformity.Density.Statement

/-!
# Uniformity.ChapI.I10_I15_I18 — the capstone hypothesis block and its four assembly
projections — **STATEMENT CARRIERS + BOOKKEEPING THEOREMS**

**Chapter I, NODES I.10a / I.10b / I.10 / I.15–I.18** (`blueprint/
CHAP-I_capstone_conditionality.md` §4 and §6; SIGNED twin `leanspec/Leanspec/ChapI.lean`, the
`### NODES I.10a / I.10b`, `### NODE I.10` and `## §6` blocks, **as amended by A-I.3,
2026-08-26**).  **ENV-I1**.  Statements transcribed BYTE-FROZEN from the amended leanspec;
re-namespaced only (`LeanspecI` → `Uniformity.Density`, GC-6.2: chapter I gets no
sub-namespace).  Unit RSGN (the capstone-gate unit), 2026-08-26.

## ⚠ DISPOSITION — READ THIS FIRST

**This file proves no mathematics** (blueprint honesty I-1).  It lands the Display-A hypothesis
STRUCTURE and the four assembly theorems whose proofs are projections and one term application.
The landing became possible — and honest — exactly at AMENDMENT A-I.3: the I.10a/I.10b socket
bodies are now TYPED at chapter C's enacted carriers
(`Uniformity/ChapC/C130s18.lean`'s `CanonicalLadderConfigData`/`CanonicalDeepTwistConfigData`,
the PK-2/U15 split-carrier `∃ (E : Type uE) (fE : Field E) … ChainRealization … (fieldE := fE)`
shapes; `runs/wave-b/verdict_PK12.md`; `docs/in-progress/PACKAGING_ROUTE_2026-08-25.md` §4.4),
which LIFTS defect I-D13 (the pre-A-I.3 block was PROVABLY uninhabited through its `True`
sockets — leanspec §4 gate item (10), now struck with its text preserved).

**The block's honest state is OPEN: not provably empty, NOT claimed inhabited.**  Nobody can
supply `∀ n, CapstoneHypotheses n` today: `a0`/`a1` are open at `n ≥ 3`, the `ladder`/
`deepTwist` fields demand supply at the arising configurations (the typed sockets), and the
weld debts are untouched.  I.17's value is its FOOTPRINT: every open input is a HYPOTHESIS,
never an axiom, so the capstone assembly adds nothing to the trusted base (AxCheck footer).

## What is carried, NOT discharged (the honesty fence, verbatim obligations)

* `jd0 : True` and `genhnBox2 : 6 ≤ n → True` — the FORBIDDEN-TO-SIGN placeholders (leanspec
  defect I-D7), ruled by A-I.1 to stay `True` until the weld site-supply socket exists (the
  `∀`-over-all-sites shapes are refutable — leanspec gate item (13)).  NOT typed here.
* the `w1` field — A-I.1's NAMED DEBT (defect I-D8): no field at all; the OM-9 note (a typed
  instantiation discharges NOTHING of HYP.139) travels with it.  NOT added here.
* `WindowPinningAt`/`GenhnHEAt`/`GenhnTow1At`/`TypeOfFaithful` — landed `True`-bodied
  statement carriers (I05/I06/I07/I21, defect I-D12).  Consumed by name only.
* defect I-D10 (`a0` over-demanded at `n = 0`) — recorded, unchanged.
* `ns7 : NS7Termination` binds leanfinal's I01 carrier, whose body was RESOLVED (2026-08-24)
  against the A-C.6 redraft; the theorems below do NOT consume `ns7Termination_of_cite`, so
  their footprints carry no cite.

## Statement provenance

The two socket defs and the structure are byte-identical to the A-I.3-amended leanspec forms
(`leanspec/Leanspec/ChapI.lean`, NODES I.10a/I.10b/I.10) including the field-list comments;
the four theorems are byte-identical to leanspec's I.15–I.18 (which land REAL there and here —
same keyword, same statements, same proofs; the `towerLocus_iff_budget` precedent's
byte-discipline, with nothing to convert since the signed forms are theorems already).
Anti-drift: gate section below (`Iff.rfl` body pins + the S2 non-vacuity teeth via
`C130sg.s2Frontier_ladder_socket`/`s2Frontier_deepTwist_socket`).

## Cite ledger

CITES CONSUMED BY THIS FILE: **none**.  No `sorry`, no new axiom, no `unsafe`.  Axiom footprint
Lean-core only (AxCheck footer).
-/

set_option linter.style.longLine false

noncomputable section

namespace Uniformity.Density

open IsLocalRing Polynomial

/-! E.12's three universes plus E.61's threaded tower universes, bound explicitly (A-E.1/E-D6,
honesty E-12): `uW` occurs only inside the `ladder` field's `Prop`, so `CapstoneHypotheses` must
name it.  Same declaration order as the leanspec, so the explicit universe lists
`CapstoneHypotheses.{uW, uG, uKt, uL}` are byte-portable. -/
universe uW uG uKt uL

/-! ## §1 NODES I.10a / I.10b — the arising-configuration sockets, TYPED (A-I.3) -/

/-- **NODE I.10a** [A-I.1; body TYPED at A-I.3, 2026-08-26] — *the arising ladder configuration
at chapter C's canonical residue read.*  The body is chapter C's enacted I.10a data-carrier
`Uniformity.Density.Tower.C130s18.CanonicalLadderConfigData` (freeze v2 §8 at the landed CC-12
views, PK-2/U15-amended split-carrier shape), ambient universe pinned to `0` (the leanspec
A-I.3 disclosure: a `Prop` cannot quantify over universes, and a socket universe parameter
would un-elaborate `CapstoneHypotheses`' byte-frozen field sites; `0` is the universe of every
arising instance — at S2, `E := FractionRing (Polynomial O)`).

[A-I.2(a), 2026-08-24 — interpretive rider, no statement change.] The frozen single `K_t` is
the terminal common receiver: every arising witness carries `T.fld r ≃+* K_t` and compatible
live maps `T.fld i →+* K_t` (freeze v2's `TerminalReceiver`). -/
def CanonicalLadderConfig {O : Type} [CommRing O] {K : Type} [Field K]
    (C : Ladder.SlotCarrier O K) (B : Ladder.BlockData C)
    (G : Type uG) [CommGroup G] (Kt : Type uKt) [Field Kt] (L : Type uL) [Field L]
    [Algebra Kt L] (N : Gauge.NormSection G) (v : ℕ → (G →* Multiplicative ℤ))
    (ρ : ∀ j : ℕ, MonoidHom.ker (v j) →* Lˣ) (q : ℕ → ℤ) (n : ℕ) : Prop :=
  -- [A-I.3, 2026-08-26] the typed body (was the `True` placeholder): some arising occurrence,
  -- realized by the PK-1 split-node chain carrier, exports exactly `(C, B, G, N, v, ρ, q)` at
  -- degree `n` through the CC-12 views. Cites: verdict_PK12.md + PACKAGING_ROUTE §4.4.
  Uniformity.Density.Tower.C130s18.CanonicalLadderConfigData.{0, uG, uKt, uL}
    C B G Kt L N v ρ q n

/-- **NODE I.10b** [A-I.1; body TYPED at A-I.3, 2026-08-26] — *the arising deep-twist
configuration*: I.10a's configuration TOGETHER with the level-indexed gauge-arena family
`(A, R, w)` chapter D's `𝒲` leg reads.  The frozen refinement shape is byte-preserved: the
first conjunct is still literally `CanonicalLadderConfig …`, so I.10b → I.10a stays `And.left`
by construction; the arena-half conjunct is chapter C's enacted joint-witness carrier, so the
whole body is definitionally C130s18's `CanonicalDeepTwistConfigData` (`Iff.rfl` pin below). -/
def CanonicalDeepTwistConfig {O : Type} [CommRing O] {K : Type} [Field K]
    (C : Ladder.SlotCarrier O K) (B : Ladder.BlockData C)
    (G : Type uG) [CommGroup G] (Kt : Type uKt) [Field Kt] (L : Type uL) [Field L]
    [Algebra Kt L] (N : Gauge.NormSection G) (v : ℕ → (G →* Multiplicative ℤ))
    (ρ : ∀ j : ℕ, MonoidHom.ker (v j) →* Lˣ) (q : ℕ → ℤ)
    (A : ℕ → Gauge.GaugeArena G Kt N) (R : ℕ → G → Kt) (w : ℕ → Ktˣ)
    (r n : ℕ) : Prop :=
  -- [A-I.2(b)] `r` is the tower depth the deep-twist conjunct is read at; the final real body
  -- must pin it to the same joint arising witness the arena export uses (never a free numeral).
  -- [A-I.3, 2026-08-26] the pin is now REAL: the joint witness carries `core.r = r` inside
  -- `DeepTwistRealizationData` (A-I.2(b)'s "never a free numeral" rule, discharged).
  CanonicalLadderConfig C B G Kt L N v ρ q n ∧
    ∃ (dom : IsDomain O) (dvr : IsDiscreteValuationRing O),
      Uniformity.Density.Tower.C130s18.DeepTwistRealizationData.{0, uG, uKt, uL}
        (dom := dom) (dvr := dvr) C B G Kt L N v ρ q A R w r n

/-! ## §2 NODE I.10 — the capstone hypothesis structure -/

/-- **Display A** (`spec/HYPOTHESIS_LEDGER.md`, FROZEN v5), one field per conjunct, at ledger
strength, degree-indexed where the display is.  Field-list changes are owner gate-(a) events
(CONVENTIONS Part V); the list below is BYTE-UNCHANGED from A-I.1's signed form (A-I.3 typed
the two socket BODIES only).

Consumption rules in force (I.10's 2026-08-16 dated note): `ladder`'s `.lb1`/`.mp1` projections
are the **A-E.2** forms (`Nonempty (BlockSuite I)` / `Nonempty (MidPeelEmission B B')`), consumed
universe-polymorphically in `uW`; `.vartheta` is E.61's typed socket at chapter D's **A-D.2**
sitewise `HVarthetaRes`.  The voided shadows (`OM4Shadow.*`, `HVarthetaResVoided`) are FENCED.

⚠ The `AllOInterfaces` conjunct is NOT a field — leanspec §4.3's signed reconciliation.
⚠ `jd0`/`genhnBox2` are the FORBIDDEN-TO-SIGN placeholders (defect I-D7); `w1` has no field at
all (defect I-D8).  A-I.1 RULES both open rather than typing them; A-I.3 changes NEITHER. -/
structure CapstoneHypotheses (n : ℕ) : Prop where
  ns7 : NS7Termination
  -- [A-I.1] the repaired E.24 application, guarded by I.10a's arising-configuration socket.
  ladder : ∀ (O : Type) [CommRing O] (K : Type) [Field K]
      (C : Ladder.SlotCarrier O K) (B : Ladder.BlockData C)
      (G : Type uG) [CommGroup G] (Kt : Type uKt) [Field Kt] (L : Type uL) [Field L]
      [Algebra Kt L] (N : Gauge.NormSection G) (v : ℕ → (G →* Multiplicative ℤ))
      (ρ : ∀ j : ℕ, MonoidHom.ker (v j) →* Lˣ) (q : ℕ → ℤ),
      CanonicalLadderConfig C B G Kt L N v ρ q n →
      Ladder.LadderSupply.{0, 0, uW, uG, uKt, uL} C B G Kt L N v ρ q
  -- [A-I.1, defect I-D4] Display A's `∀ i ≥ 3` conjunct, BOTH halves, at E.63's packaging.
  -- [A-I.2(b), 2026-08-24] re-signed at the freeze-v2 LIVE RANGE: the conjunct is read at the
  -- arising tower depth `r` through `DeepTwistConjunctLive` (unbounded form undischargeable).
  deepTwist : ∀ (O : Type) [CommRing O] (K : Type) [Field K]
      (C : Ladder.SlotCarrier O K) (B : Ladder.BlockData C)
      (G : Type uG) [CommGroup G] (Kt : Type uKt) [Field Kt] (L : Type uL) [Field L]
      [Algebra Kt L] (N : Gauge.NormSection G) (v : ℕ → (G →* Multiplicative ℤ))
      (ρ : ∀ j : ℕ, MonoidHom.ker (v j) →* Lˣ) (q : ℕ → ℤ)
      (A : ℕ → Gauge.GaugeArena G Kt N) (R : ℕ → G → Kt) (w : ℕ → Ktˣ) (r : ℕ),
      CanonicalDeepTwistConfig C B G Kt L N v ρ q A R w r n →
      Ladder.DeepTwistConjunctLive r v ρ q A R w
  a0 : DecidedSliceAt n
  a1 : MenuLawAt n
  a2 : DrainageAt n
  jd0 : True                            -- ⚠ LATE-BINDING F (I.08); defect I-D7
  genhnBox2 : 6 ≤ n → True              -- ⚠ LATE-BINDING F (I.09); defects I-D7, I-D8
  windowPinning : WindowPinningAt n
  genhnHE : 6 ≤ n → GenhnHEAt n
  genhnTow1 : 8 ≤ n → GenhnTow1At n

/-! ## §3 NODES I.15–I.18 — the assembly (bookkeeping; honesty I-1)

Everything here is projections of I.10 and applications of landed
`UniformityStatement.ofDecided` / `totalMassOne_of_drainage`.  **No theorem in this section
makes the capstone less conditional; each makes the conditionality machine-readable.** -/

/-- **I.15** — the drainage projection. -/
theorem drainage_of_capstoneHypotheses
    (h : ∀ n, CapstoneHypotheses.{uW, uG, uKt, uL} n) : ∀ n, DrainageAt n :=
  fun n => (h n).a2

/-- **I.16** — the decided-target projection. The content: the `a0` fields ARE the degree-slices
of the decided target, so re-indexing is the whole proof. This is where the count layer's
openness is made visible — nobody can supply `∀ n, CapstoneHypotheses n` today precisely because
`a0`/`a1` are open at `n ≥ 3`.

The one-line `exact` closes because I.02's body was COPIED from the landed target's body rather
than re-typed; the `Iff.rfl` pin in I02's gate is the standing regression on that copy. -/
theorem decided_of_capstoneHypotheses
    (h : ∀ n, CapstoneHypotheses.{uW, uG, uKt, uL} n) : UniformityStatementDecided := by
  intro n _hn σ hσ
  exact (h n).a0 σ hσ

/-- **I.17 — THE HONEST CAPSTONE ASSEMBLY.** `UniformityStatement` follows from the ledger's
frozen hypothesis block and nothing else. What remains open is exactly the block's fields: see
the chapter-I disposition table (leanspec §3, 36 OPEN-MATH rows + the gate-(b) cites).

**This proves no mathematics** (honesty I-1). Its value is the footprint: every open input is a
HYPOTHESIS, never an axiom, so this declaration's `#print axioms` is Lean-core — printed in the
AxCheck footer and enforced at leanspec gate I.24. -/
theorem uniformity_of_capstoneHypotheses
    (h : ∀ n, CapstoneHypotheses.{uW, uG, uKt, uL} n) : UniformityStatement :=
  UniformityStatement.ofDecided (drainage_of_capstoneHypotheses h)
    (decided_of_capstoneHypotheses h)

/-- **I.18** — `TotalMassOne`, not double-counted: from the same structure, via the `a2` fields
and landed `totalMassOne_of_drainage` ONLY (honesty I-4 — the mass law is the drainage leg
wearing a different hat and gets no field of its own). -/
theorem totalMassOne_of_capstoneHypotheses
    (h : ∀ n, CapstoneHypotheses.{uW, uG, uKt, uL} n) : TotalMassOne :=
  totalMassOne_of_drainage (drainage_of_capstoneHypotheses h)

/-! ## §4 GATE (executed; mirrors the A-I.3-amended leanspec §4 gate items (5a)/(15)/(16)/(17)) -/

section GateI10

-- (a) the a2 field binds the LANDED `DrainageAt` (leanspec gate item (1)).
example (n : ℕ) (h : CapstoneHypotheses.{uW, uG, uKt, uL} n) : DrainageAt n := h.a2

-- (b) the I.10b → I.10a refinement, by construction (leanspec gate item (5a)): a deep-twist
-- configuration IS a ladder configuration, so the two guarded fields can never drift onto
-- different data.
example {K : Type} [Field K] {C : Ladder.SlotCarrier ℤ K} {B : Ladder.BlockData C}
    {G : Type uG} [CommGroup G] {Kt : Type uKt} [Field Kt] {L : Type uL} [Field L]
    [Algebra Kt L] {N : Gauge.NormSection G} {v : ℕ → (G →* Multiplicative ℤ)}
    {ρ : ∀ j : ℕ, MonoidHom.ker (v j) →* Lˣ} {q : ℕ → ℤ}
    {A : ℕ → Gauge.GaugeArena G Kt N} {R : ℕ → G → Kt} {w : ℕ → Ktˣ} {n : ℕ}
    {r : ℕ} (hcfg : CanonicalDeepTwistConfig C B G Kt L N v ρ q A R w r n) :
    CanonicalLadderConfig C B G Kt L N v ρ q n := hcfg.1

-- (c) [A-I.3 item (15)] anti-drift pins: the socket bodies ARE chapter C's enacted
-- I.10a/I.10b data-carriers, DEFINITIONALLY (`Iff.rfl` — fails the build on any drift).
example {O : Type} [CommRing O] {K : Type} [Field K]
    (C : Ladder.SlotCarrier O K) (B : Ladder.BlockData C)
    (G : Type uG) [CommGroup G] (Kt : Type uKt) [Field Kt] (L : Type uL) [Field L]
    [Algebra Kt L] (N : Gauge.NormSection G) (v : ℕ → (G →* Multiplicative ℤ))
    (ρ : ∀ j : ℕ, MonoidHom.ker (v j) →* Lˣ) (q : ℕ → ℤ) (n : ℕ) :
    CanonicalLadderConfig C B G Kt L N v ρ q n ↔
      Uniformity.Density.Tower.C130s18.CanonicalLadderConfigData.{0, uG, uKt, uL}
        C B G Kt L N v ρ q n := Iff.rfl
example {O : Type} [CommRing O] {K : Type} [Field K]
    (C : Ladder.SlotCarrier O K) (B : Ladder.BlockData C)
    (G : Type uG) [CommGroup G] (Kt : Type uKt) [Field Kt] (L : Type uL) [Field L]
    [Algebra Kt L] (N : Gauge.NormSection G) (v : ℕ → (G →* Multiplicative ℤ))
    (ρ : ∀ j : ℕ, MonoidHom.ker (v j) →* Lˣ) (q : ℕ → ℤ)
    (A : ℕ → Gauge.GaugeArena G Kt N) (R : ℕ → G → Kt) (w : ℕ → Ktˣ) (r n : ℕ) :
    CanonicalDeepTwistConfig C B G Kt L N v ρ q A R w r n ↔
      Uniformity.Density.Tower.C130s18.CanonicalDeepTwistConfigData.{0, uG, uKt, uL}
        C B G Kt L N v ρ q A R w r n := Iff.rfl

end GateI10

section GateS2Teeth
open Uniformity.Density.Tower
open Uniformity.Density.Tower.C130s17 Uniformity.Density.Tower.C130sg

-- (d) [A-I.3 item (16)] NON-VACUITY of the typed I.10a socket at the arising S2 instance:
-- the landed SG-1 stage-4a application (`C130sg.s2Frontier_ladder_socket`, `ev`/`lf`-FREE per
-- PK-2/U15) inhabits the socket at the concrete `keyAt 2 + 1` occurrence, degree 4,
-- conditional on exactly `w : S2LevelOneThreshold` + `IsAdicComplete`.
example {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Finite (IsLocalRing.ResidueField O)]
    (h2 : Irreducible (2 : O)) (hq : residueCard O = 2)
    (L : Type uL) [Field L] [Algebra ((S2DepthTwo h2 hq).fld 2) L]
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O] (w : S2LevelOneThreshold) :
    CanonicalLadderConfig
      ((s2Frontier h2 hq L w).s2RealizedInput.stageCarrierTransport
        (RingEquiv.refl ((S2DepthTwo h2 hq).fld 2)))
      ((s2Frontier h2 hq L w).s2RealizedInput.inputBlockTransport
        (RingEquiv.refl ((S2DepthTwo h2 hq).fld 2)))
      (GaugeLattice.{uG} 2) ((S2DepthTwo h2 hq).fld 2) L
      ((s2Frontier h2 hq L w).toCarrier.normalizer.arenaNormSection0.transport
        (gaugeLatticeEquiv 2).symm)
      (gaugeHeightFamily (s2Frontier h2 hq L w).s2RealizedInput)
      (canonicalResFamily (s2Frontier h2 hq L w).s2RealizedInput)
      (useHeightFamily (s2Frontier h2 hq L w).s2RealizedInput) 4 :=
  s2Frontier_ladder_socket h2 hq L w

-- (e) [A-I.3 item (17)] NON-VACUITY of the typed I.10b socket at the same instance, depth
-- binder pinned to the witness's own `r = 2` (the A-I.2(b) rule, machine-real via the joint
-- witness's `core.r = r` conjunct).
example {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Finite (IsLocalRing.ResidueField O)]
    (h2 : Irreducible (2 : O)) (hq : residueCard O = 2)
    (L : Type uL) [Field L] [Algebra ((S2DepthTwo h2 hq).fld 2) L]
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O] (w : S2LevelOneThreshold) :
    CanonicalDeepTwistConfig
      ((s2Frontier h2 hq L w).s2RealizedInput.stageCarrierTransport
        (RingEquiv.refl ((S2DepthTwo h2 hq).fld 2)))
      ((s2Frontier h2 hq L w).s2RealizedInput.inputBlockTransport
        (RingEquiv.refl ((S2DepthTwo h2 hq).fld 2)))
      (GaugeLattice.{uG} 2) ((S2DepthTwo h2 hq).fld 2) L
      ((s2Frontier h2 hq L w).toCarrier.normalizer.arenaNormSection0.transport
        (gaugeLatticeEquiv 2).symm)
      (gaugeHeightFamily (s2Frontier h2 hq L w).s2RealizedInput)
      (canonicalResFamily (s2Frontier h2 hq L w).s2RealizedInput)
      (useHeightFamily (s2Frontier h2 hq L w).s2RealizedInput)
      (arenaFamily (s2Frontier h2 hq L w).s2RealizedInput Nat.one_lt_two)
      (towerReadFamily (s2Frontier h2 hq L w).s2RealizedInput)
      (s2Frontier h2 hq L w).toCarrier.node.peelUnitFamily 2 4 :=
  s2Frontier_deepTwist_socket h2 hq L w

end GateS2Teeth

end Uniformity.Density

end

/-! ## AXCHECK FOOTER — expect Lean core `{propext, Classical.choice, Quot.sound}` only.
In particular I.17's footprint is the design point: every open input is a HYPOTHESIS, never an
axiom (the `ns7` field's cite lives in `ns7Termination_of_cite`'s footprint, NOT here — these
theorems never consume it). -/

#print axioms Uniformity.Density.CanonicalLadderConfig
#print axioms Uniformity.Density.CanonicalDeepTwistConfig
#print axioms Uniformity.Density.CapstoneHypotheses
#print axioms Uniformity.Density.drainage_of_capstoneHypotheses
#print axioms Uniformity.Density.decided_of_capstoneHypotheses
#print axioms Uniformity.Density.uniformity_of_capstoneHypotheses
#print axioms Uniformity.Density.totalMassOne_of_capstoneHypotheses
