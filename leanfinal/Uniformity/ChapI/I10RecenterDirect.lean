/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapI.I10RecenterLive

/-!
# Uniformity.ChapI.I10RecenterDirect — the DIRECT-route recenter-step export surface and
the A-I.8 supply record (AMENDMENT A-I.8, 2026-08-28)

**[A-I.8 ENACTMENT, 2026-08-28 — unit AI8E; forcing stop-line `runs/wave-c/verdict_DWR.md`,
adjudication `runs/wave-c/verdict_A8D.md`.]**  The five declarations `DirectKeyPayload` /
`RecenterStepDirect` / `midPeelEmission_of_recenterStepDirect` / `MP1CarrierLiveDirect` /
`mp1CarrierLiveDirect_of_steps` are PROMOTED from the machine-verified probe
`scratch/A8D_probe.lean` (Lean-core, exit 0, orchestrator re-verified pre-enactment;
pre-enactment state archived at commit `3d545e6e`) — declaration bytes identical, one
docstring word changed (`draft` → `live`; machine diff recorded in
`runs/wave-c/verdict_AI8E.md`).  `LadderSupplyLive₃` is the superseding supply record —
the capstone `ladder` field's result record (`I10_I15_I18.lean`, NODE I.10, as amended by
A-I.8).  Acyclic import home: this file imports only `Uniformity.ChapI.I10RecenterLive`
(A-I.7's export surface, and through it `I10LadderLive → {C130s18, E24}`), which sits
below I.10 — `I10_I15_I18 → I10RecenterDirect → I10RecenterLive → I10LadderLive`, no
cycle.  The C132/C134 operator banks are NOT imported: the generic
`IsMuKey → Irreducible` bridge stays shape-validated in `scratch/A8D_probe.lean`
(`A8DProbe.irreducible_of_isMuKey`) and enters production with the D3-16/D4-15 key tails,
per A8D's placement clause — so the capstone import graph stays free of the deep banks.

## Why the retirement is forced (the record — an HONESTY stop-line, not an emptiness one)

Unlike A-I.6/A-I.7, the superseded surface is NOT machine-refuted.  DWR's stop-line
(`runs/wave-c/verdict_DWR.md`, "Stop-line finding"): `GNCitePayload` receives
`phi := B'.Φ`; its `exactLeaf` identifies the theorem-selected `g_{λ,ψ}` with that same
`phi`, while `leaf_dvd_input` and `RecenterStep` require `phi ∣ B.F`.  In GN's
factorization, literal `phi` divisors form the separate key-power term; `phi` itself has
no finite principal Newton side relative to its own `phi`-development, so it cannot
simultaneously be a finite-slope selected `g_{λ,ψ}`.  This defeats EVERY input under the
identification, for ANY tower: no source-faithful occurrence of the payload exists.  The
Prop stays formally inhabitable by dishonest instances — which is exactly why the repair
is an A-I.8 statement amendment, not a refutation pin.  A8D adjudicated fork (β): retire
the GN payload from the live surface and demand the recentered polynomial's key-hood for
its concrete deep valuation, with the key-irreducibility law proved DIRECTLY — E.40's
`MidPeelEmission` needs only `MP1StepCore` + `hirr` + `hef`, and `hirr` follows from
`Monic ∧ MuMinimal ∧ MuPrime` via the monic Gauss equivalence (A8D §1; leg-by-leg
generalization table: NO ROW BLOCKED).

## Trust boundary

**Every `def`/`structure` here is a NEW statement**, flagged for the standing review
(`docs/REVIEW_QUEUE_2026-08-26.md`, Tier 1 row A-I.8).  `DirectKeyPayload` deliberately
does NOT demand the other `FGMNSourceLaws` fields, and it is NOT an authorization to
install a literature axiom: at the deep instances its `key_irreducible` law must be
filled by the direct `IsMuKey → Irreducible` theorems (D3-16 at μ₄, D4-15 at μ₅ — the
A8D consumer/supplier table), never by citation.  **No cite is consumed here.**

## The mp1 leg is now DISCHARGED (the honest content relocation)

`mp1CarrierLiveDirect_of_steps` proves `MP1CarrierLiveDirect` OUTRIGHT: the direct
payload plus the peel core already compile to E.40's exact conclusion, so the supply
record's `mp1` field is a theorem, not an open obligation.  The honest mathematical
content moves to PRODUCING `RecenterStepDirect` occurrences (A8D's C4d/C5d nonvacuity
teeth, resting on the D3/D4 key tails) — one occurrence yields nonvacuity only, and the
`package`/`lb1`/`vartheta` legs remain open exactly as before.

## Supersession/adapter analysis (machine pins in §3)

* **Payload level, OLD ⟹ NEW holds**: a `GNCitePayload`'s `source`/`keyPolynomial`
  clauses plus its `sourceLaws` field's `key_irreducible` law assemble a
  `DirectKeyPayload` (`directKeyPayload_of_gnCitePayload`) — the direct demand is
  strictly weaker than key-hood-plus-full-source-laws.
* **Step level, NO adapter exists — recorded**: old `RecenterStep` ⟹ new
  `RecenterStepDirect` FAILS.  The new step carries DWR's anti-splicing bindings
  `step.quot.F = B'.F`, `B'.T = B.T`, `step.quot.T = B.T`, `B.F = B'.Φ * B'.F`; the old
  step's `Nonempty (MP1StepCore B B')` ties none of the exported quotient's data to `B'`
  (only `step.quot.T = B.T` and `B.F = B'.Φ * step.quot.F` are derivable — `quot.F = B'.F`
  and `B'.T = B.T` are strictly new producer content, DWR "Files and rules" table).  The
  converse also fails (the direct payload cannot manufacture GN's slope/residual/leaf
  fields).  Neither absence weakens the record-level supersession below.
* **Record level, OLD ⟹ NEW holds**: `ladderSupplyLive₃_of_live₂` — `package`/`lb1`/
  `vartheta` pass through unchanged and the new `mp1` leg is filled by the generic
  compiler.

Statement provenance: the five promoted declarations byte-identical to
`scratch/A8D_probe.lean` modulo the recorded one-word docstring change (machine diff at
enactment: `runs/wave-c/verdict_AI8E.md`); `LadderSupplyLive₃`'s `package`/`lb1`/
`vartheta` fields byte-identical to A-I.7's `LadderSupplyLive₂` (hence to E.24's/A-I.6's),
ONLY `mp1` replaced.  `LadderSupplyLive₂` and the whole GN export surface
(`GNCitePayload`/`RecenterStep`/`MP1CarrierLive`) stay byte-frozen in
`I10RecenterLive.lean` as the A-I.7 tension record.  Zero `sorry`, zero new axiom;
AxChk footer expects Lean core only.
-/

set_option linter.style.longLine false

noncomputable section

namespace Uniformity.Density.IFC5

open Polynomial IsLocalRing
open Uniformity.Density
open Uniformity.Density.Ladder
open Uniformity.Density.Tower

universe uW uG uKt uL uR

/-! ## §1 The direct recenter-step export surface (A8D probe byte-shapes) -/

/-- The direct replacement for the GN payload.  It retains the same-chain provenance but
asks only for the key predicate and its directly proved irreducibility law. -/
structure DirectKeyPayload {O : Type} [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O]
    {Kt : Type uKt} [Field Kt] {E : Type} [Field E]
    {L : Type uL} [Field L] [Algebra Kt L] {n : ℕ}
    {core : Tower.ArisingCore (O := O) Kt L n}
    (A : Tower.ChainRealization (O := O) (π := core.π) (F := core.F)
      (H₀ := core.H₀) (hpin := core.hpin) core.T Kt E L)
    (phi : Polynomial O) where
  e' : ℕ
  f' : ℕ
  u' : ℕ
  source : Tower.FGMNSourceData core.T A.keys e' f' u'
  keyPolynomial : source.keyPolynomial phi
  key_irreducible : ∀ g : Polynomial O,
    source.keyPolynomial g → g.Monic → Irreducible g

/-- The A-I.8 live surface.  In addition to replacing the GN payload, this incorporates the
DWR provenance equalities tying the successor block to the quotient exported by the step. -/
def RecenterStepDirect
    {O : Type} [CommRing O] {K : Type} [Field K]
    (C : Ladder.SlotCarrier O K) (B B' : Ladder.BlockData C)
    (G : Type uG) [CommGroup G] (Kt : Type uKt) [Field Kt]
    (L : Type uL) [Field L] [Algebra Kt L]
    (N : Gauge.NormSection G) (v : ℕ → (G →* Multiplicative ℤ))
    (rho : ∀ j : ℕ, MonoidHom.ker (v j) →* Lˣ) (q : ℕ → ℤ)
    (n : ℕ) (Lambda : Polynomial O) : Prop :=
  ∃ (_dom : IsDomain O) (_dvr : IsDiscreteValuationRing O)
    (E : Type) (fE : Field E) (core : Tower.ArisingCore (O := O) Kt L n)
    (A : Tower.ChainRealization (O := O) (π := core.π) (F := core.F)
      (H₀ := core.H₀) (hpin := core.hpin) (fieldE := fE) core.T Kt E L)
    (X : Tower.RealizedInput core A)
    (eK : core.T.fld core.i ≃+* K) (eG : G ≃* Tower.GaugeLattice.{uG} core.r),
    Tower.SlotViewEq X eK C ∧
    (∃ hC : C = X.stageCarrierTransport eK,
      Tower.BlockViewEq X eK (hC ▸ B)) ∧
    Tower.GaugeFamilyViewEq X (N.transport eG)
      (fun j => (v j).comp eG.symm.toMonoidHom)
      (fun j => (rho j).comp (Tower.C130s18.kerComapAlong eG (v j))) q ∧
    Lambda ≠ 0 ∧ Lambda.natDegree < C.D ∧
    B'.Φ = B.Φ - Lambda ∧ B'.Φ ∣ B.F ∧
    B'.T = B.T ∧
    Nonempty (DirectKeyPayload (Kt := Kt) (L := L) A B'.Φ) ∧
    ∃ step : IFC5.MP1StepCore.{uW} B B',
      step.quot.F = B'.F ∧
      step.quot.T = B.T ∧
      B.F = B'.Φ * B'.F

/-- The direct payload plus the peel core compiles to the exact E.40 conclusion. -/
theorem midPeelEmission_of_recenterStepDirect
    {O : Type} [CommRing O] {K : Type} [Field K]
    {C : Ladder.SlotCarrier O K} {B B' : Ladder.BlockData C}
    {G : Type uG} [CommGroup G] {Kt : Type uKt} [Field Kt]
    {L : Type uL} [Field L] [Algebra Kt L]
    {N : Gauge.NormSection G} {v : ℕ → (G →* Multiplicative ℤ)}
    {rho : ∀ j : ℕ, MonoidHom.ker (v j) →* Lˣ} {q : ℕ → ℤ}
    {n : ℕ} {Lambda : Polynomial O}
    (hstep : RecenterStepDirect.{uW, uG, uKt, uL}
      C B B' G Kt L N v rho q n Lambda) :
    Nonempty (Ladder.MidPeelEmission.{0, 0, uW} B B') := by
  rcases hstep with
    ⟨dom, dvr, E, fE, core, A, X, eK, eG, _hslot, _hblock, _hgauge,
      _hLambda0, _hLambdaDeg, _hrecenter, _hdvd, _hT, ⟨direct⟩, step,
      _hquotF, _hquotT, _hpeelBound⟩
  letI : IsDomain O := dom
  letI : IsDiscreteValuationRing O := dvr
  have hirrO : Irreducible B'.Φ :=
    direct.key_irreducible B'.Φ direct.keyPolynomial B'.hΦ
  have hirr : Irreducible (B'.Φ.map (algebraMap O (FractionRing O))) :=
    (B'.hΦ.irreducible_iff_irreducible_map_fraction_map
      (K := FractionRing O)).mp hirrO
  exact ⟨{
    quot := step.quot
    hkey := step.hkey
    hpeel := step.hpeel
    hmass := step.hmass
    hthr := step.hthr
    iface := step.iface
    hirr := hirr
    hef := B'.hΦdeg.trans C.hef }⟩

/-- The A-I.8 live carrier differs only in the producer premise. -/
def MP1CarrierLiveDirect
    {O : Type} [CommRing O] {K : Type} [Field K]
    (C : Ladder.SlotCarrier O K) (B : Ladder.BlockData C)
    (G : Type uG) [CommGroup G] (Kt : Type uKt) [Field Kt]
    (L : Type uL) [Field L] [Algebra Kt L]
    (N : Gauge.NormSection G) (v : ℕ → (G →* Multiplicative ℤ))
    (rho : ∀ j : ℕ, MonoidHom.ker (v j) →* Lˣ) (q : ℕ → ℤ) (n : ℕ) : Prop :=
  ∀ (Lambda : Polynomial O), Lambda ≠ 0 → Lambda.natDegree < C.D →
    ∀ (B' : Ladder.BlockData C), B'.Φ = B.Φ - Lambda → B'.Φ ∣ B.F →
      RecenterStepDirect.{uW, uG, uKt, uL} C B B' G Kt L N v rho q n Lambda →
      Nonempty (Ladder.MidPeelEmission.{0, 0, uW} B B')

theorem mp1CarrierLiveDirect_of_steps
    {O : Type} [CommRing O] {K : Type} [Field K]
    (C : Ladder.SlotCarrier O K) (B : Ladder.BlockData C)
    (G : Type uG) [CommGroup G] (Kt : Type uKt) [Field Kt]
    (L : Type uL) [Field L] [Algebra Kt L]
    (N : Gauge.NormSection G) (v : ℕ → (G →* Multiplicative ℤ))
    (rho : ∀ j : ℕ, MonoidHom.ker (v j) →* Lˣ) (q : ℕ → ℤ) (n : ℕ) :
    MP1CarrierLiveDirect.{uW, uG, uKt, uL} C B G Kt L N v rho q n := by
  intro Lambda _ _ B' _ _ hstep
  exact midPeelEmission_of_recenterStepDirect hstep

/-! ## §2 The A-I.8 superseding supply record -/

/-- The A-I.8 supply record.  `package`/`lb1` are byte-identical to E.24's `LadderSupply`
fields, `vartheta` to A-I.6's live field — all three carried through A-I.7's
`LadderSupplyLive₂` unchanged; ONLY `mp1` is replaced by the DIRECT-route
`MP1CarrierLiveDirect` (GNCitePayload retired from the live surface per DWR's stop-line +
A8D's (β) adjudication).  NOTE the honest asymmetry: this record's `mp1` field is
DISCHARGED generically by `mp1CarrierLiveDirect_of_steps`, so the record's open content is
exactly `package`/`lb1`/`vartheta`.  Supersedes `LadderSupplyLive₂` as the capstone
`ladder` field's result record; that record stays byte-frozen as the A-I.7 tension record.
NEW STATEMENT (review). -/
structure LadderSupplyLive₃ {O : Type} [CommRing O] {K : Type} [Field K]
    (C : Ladder.SlotCarrier O K) (B : Ladder.BlockData C)
    (G : Type uG) [CommGroup G] (Kt : Type uKt) [Field Kt]
    (L : Type uL) [Field L] [Algebra Kt L]
    (N : Gauge.NormSection G) (v : ℕ → (G →* Multiplicative ℤ))
    (ρ : ∀ j : ℕ, MonoidHom.ker (v j) →* Lˣ) (q : ℕ → ℤ) (n : ℕ) : Prop where
  package : Ladder.HE7APackage.{0, 0, uW} C B
  lb1 : Ladder.LB1Carrier.{0, 0, uW} C B
  mp1 : MP1CarrierLiveDirect.{uW, uG, uKt, uL} C B G Kt L N v ρ q n
  vartheta : ∀ i ≥ 3,
    CanonicalLadderLiveAt.{uG, uKt, uL} C B G Kt L N v ρ q n i →
      Ladder.VarthetaRes G Kt L N v ρ q i

/-! ## §3 Supersession-direction pins (nothing strengthened, machine-visible)

⚠ NO STEP-LEVEL ADAPTER EXISTS, by design: `RecenterStep → RecenterStepDirect` fails
because the new step carries DWR's anti-splicing bindings (`step.quot.F = B'.F`,
`B'.T = B.T`, `step.quot.T = B.T`, `B.F = B'.Φ * B'.F`) which the old step's bare
`Nonempty (MP1StepCore B B')` never recorded — only `step.quot.T = B.T` (`hthr`) and
`B.F = B'.Φ * step.quot.F` (`hpeel`) are derivable from the old core; the ties to `B'.F`
and `B'.T` are strictly new producer content.  The converse fails too (the direct payload
carries no GN slope/residual/leaf data).  The payload-level and record-level directions
below are the ones that hold. -/

/-- ★ SUPERSESSION PIN (payload level): the OLD GN payload's key-hood clause plus its
`sourceLaws` field's `key_irreducible` law assemble the NEW direct payload — the direct
demand asks strictly less than key-hood-plus-full-source-laws.  It smuggles no
strengthening. -/
theorem directKeyPayload_of_gnCitePayload
    {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {Kt : Type uKt} [Field Kt] {E : Type} [Field E]
    {L : Type uL} [Field L] [Algebra Kt L] {n : ℕ}
    {core : Tower.ArisingCore (O := O) Kt L n}
    {A : Tower.ChainRealization (O := O) (π := core.π) (F := core.F)
      (H₀ := core.H₀) (hpin := core.hpin) core.T Kt E L}
    {g phi : Polynomial O} {kRes : Type uR} [Field kRes]
    (P : GNCitePayload (Kt := Kt) (L := L) A g phi kRes) :
    Nonempty (DirectKeyPayload (Kt := Kt) (L := L) A phi) := by
  obtain ⟨laws⟩ := P.sourceLaws
  -- fields in declaration order: e', f', u', source, keyPolynomial, key_irreducible
  exact ⟨⟨P.e', P.f', P.u', P.source, P.keyPolynomial, laws.key_irreducible⟩⟩

/-- ★ SUPERSESSION PIN (record level): A-I.7's record implies the A-I.8 record —
`package`/`lb1`/`vartheta` pass through unchanged and the new `mp1` leg is filled by the
generic compiler `mp1CarrierLiveDirect_of_steps` (it needs nothing from the old leg). -/
theorem ladderSupplyLive₃_of_live₂
    {O : Type} [CommRing O] {K : Type} [Field K]
    {C : Ladder.SlotCarrier O K} {B : Ladder.BlockData C}
    {G : Type uG} [CommGroup G] {Kt : Type uKt} [Field Kt]
    {L : Type uL} [Field L] [Algebra Kt L]
    {N : Gauge.NormSection G} {v : ℕ → (G →* Multiplicative ℤ)}
    {ρ : ∀ j : ℕ, MonoidHom.ker (v j) →* Lˣ} {q : ℕ → ℤ} {n : ℕ}
    (h : LadderSupplyLive₂.{uW, uG, uKt, uL} C B G Kt L N v ρ q n) :
    LadderSupplyLive₃.{uW, uG, uKt, uL} C B G Kt L N v ρ q n :=
  ⟨h.package, h.lb1, mp1CarrierLiveDirect_of_steps C B G Kt L N v ρ q n, h.vartheta⟩

end Uniformity.Density.IFC5

end

/-! ## AXCHECK FOOTER — expect Lean core `{propext, Classical.choice, Quot.sound}` only.
Statement carriers + the generic compiler + supersession bookkeeping; nothing here may add
to the trusted base. -/

#print axioms Uniformity.Density.IFC5.DirectKeyPayload
#print axioms Uniformity.Density.IFC5.RecenterStepDirect
#print axioms Uniformity.Density.IFC5.midPeelEmission_of_recenterStepDirect
#print axioms Uniformity.Density.IFC5.MP1CarrierLiveDirect
#print axioms Uniformity.Density.IFC5.mp1CarrierLiveDirect_of_steps
#print axioms Uniformity.Density.IFC5.LadderSupplyLive₃
#print axioms Uniformity.Density.IFC5.directKeyPayload_of_gnCitePayload
#print axioms Uniformity.Density.IFC5.ladderSupplyLive₃_of_live₂
