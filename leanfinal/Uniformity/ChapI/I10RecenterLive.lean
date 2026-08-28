/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapI.I10LadderLive

/-!
# Uniformity.ChapI.I10RecenterLive — the recenter-step export surface and the live-MP1
supply record (AMENDMENT A-I.7, 2026-08-28)

**[A-I.7 ENACTMENT, 2026-08-28 — unit AI7E; forcing adjudication
`runs/wave-c/verdict_REX.md`.]**  The four declarations `MP1StepCore` / `GNCitePayload` /
`RecenterStep` / `MP1CarrierLive` are PROMOTED byte-for-byte from the machine-verified
probe `scratch/REX_probe.lean` (Lean-core, exit 0; the forcing refutation is archived at
commit `05f067b7`); `LadderSupplyLive₂` is the superseding supply record — the capstone
`ladder` field's result record (`I10_I15_I18.lean`, NODE I.10, as amended by A-I.7).
This file is the acyclic home: it imports only `Uniformity.ChapI.I10LadderLive` (A-I.6's
live record, and through it chapter C's realization/view carriers `C130s18` + chapter E's
ladder vocabulary `E24`), which sits below I.10 in the import order —
`I10_I15_I18 → I10RecenterLive → I10LadderLive → {C130s18, E24}`, no cycle.

## Why the rebind is forced (the machine record)

A-I.6's `IFC5.LadderSupplyLive.mp1` still demands the UNRESTRICTED `Ladder.MP1Carrier`
(the conclusion at EVERY legal recentering `B'` with `B'.Φ = B.Φ − Λ` and `B'.Φ ∣ B.F`),
and `scratch/REX_probe.lean` proves at the landed degree-4 S2 socket (Lean-core, exit 0,
orchestrator re-verified pre-enactment):

* `REXProbe.s2_unrestricted_mp1_false : ¬ Ladder.MP1Carrier C2 B2`
* `REXProbe.s2_ladderSupplyLive_false : ¬ IFC5.LadderSupplyLive C2 B2 … 4`
* `REXProbe.capstoneHypotheses_four_refuted_via_mp1 : ¬ CapstoneHypotheses 4`
  (stated pre-A-I.7; re-pinned at enactment to the probe's retired verbatim copy)

— the S2 producer's own data (`B2.μ = 1`, `B2.F = B2.Φ + 1`) admit `Λ = −1` with the
legal successor `B2'.Φ = B2.F`, whose demanded `MidPeelEmission` quotient is
degree-impossible at the length-one parent (`hmass` forces `deg quot.F + D = D` against
`D > 0`).  So the signed block's bytes were machine-EMPTY at degree 4 again, and an
interpretive rider is impossible (the A-I.5/A-I.6 precedent: the signed field must remain
inhabitable in principle).  The honest repair (REX "Export design"): demand MP1's
conclusion ONLY for successors exported by a recentering step of the SAME realization
witnessing the socket.

## Trust boundary

**Every `def`/`structure` here is a NEW statement**, flagged for the standing review
(`docs/REVIEW_QUEUE_2026-08-26.md`, Tier 1 row A-I.7).  `GNCitePayload` is one-to-one
with the exact hypothesis list of Guàrdia–Nart, *Genetics of polynomials over local
fields*, Contemp. Math. 637 (2015), Theorem 2.3 (REX verdict, "Exact source hypothesis
list") — it is a STATEMENT CARRIER; **no cite is consumed here** and nothing is asserted
about GN15's theorem.  Residual multiplicity one is spelled
`residual = psi * residualQuot` + `¬ psi ∣ residualQuot` (with `Irreducible psi`), never
conflated with input divisibility.

Statement provenance: the four promoted bodies byte-identical to `scratch/REX_probe.lean`
(machine byte-diff at enactment: `runs/wave-c/verdict_AI7E.md`); `LadderSupplyLive₂`'s
`package`/`lb1` fields byte-identical to A-I.6's `LadderSupplyLive` (hence to E.24's),
its `vartheta` field byte-identical to A-I.6's live field, ONLY `mp1` replaced.
`LadderSupplyLive` stays byte-frozen in `I10LadderLive.lean` as the refuted tension
record.  Zero `sorry`, zero new axiom; AxChk footer expects Lean core only.
-/

set_option linter.style.longLine false

noncomputable section

namespace Uniformity.Density.IFC5

open Polynomial IsLocalRing
open Uniformity.Density
open Uniformity.Density.Ladder
open Uniformity.Density.Tower

universe uW uG uKt uL uR

/-! ## §1 The recenter-step export surface (REX probe byte-shapes) -/

/-- Items 2--4 of `MidPeelEmission`; the cite-produced irreducibility field is absent. -/
structure MP1StepCore {O : Type} [CommRing O] {K : Type} [Field K]
    {C : Ladder.SlotCarrier O K} (B B' : Ladder.BlockData C) where
  quot : Ladder.BlockData C
  hkey : quot.Φ = B'.Φ
  hpeel : B.F = B'.Φ * quot.F
  hmass : quot.F.natDegree + C.D = B.F.natDegree
  hthr : quot.T = B.T
  iface : Ladder.RungInterface.{0, 0, uW} C quot

/-- The GN15-Theorem-2.3 payload exported by one actual recentering step.

`residual = psi * residualQuot` and `¬ psi ∣ residualQuot` is the producer-side spelling of
`ord_psi(residual) = 1`, once `psi` is irreducible.  `exactLeaf` is the indispensable
identification of the theorem-selected factor with the exact key exported to `B'`.
-/
structure GNCitePayload {O : Type} [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O]
    {Kt : Type uKt} [Field Kt] {E : Type} [Field E]
    {L : Type uL} [Field L] [Algebra Kt L] {n : ℕ}
    {core : Tower.ArisingCore (O := O) Kt L n}
    (A : Tower.ChainRealization (O := O) (π := core.π) (F := core.F)
      (H₀ := core.H₀) (hpin := core.hpin) core.T Kt E L)
    (g phi : Polynomial O) (kRes : Type uR) [Field kRes] where
  e' : ℕ
  f' : ℕ
  u' : ℕ
  source : Tower.FGMNSourceData core.T A.keys e' f' u'
  sourceLaws : Nonempty (Tower.FGMNSourceLaws core.T A.keys e' f' u' source)
  keyPolynomial : source.keyPolynomial phi
  tangentClass : ¬ source.initialEquiv phi (A.keys.keyAt core.r)
  monicInput : g.Monic
  slope : ℚ
  slope_pos : 0 < slope
  residual : Polynomial kRes
  psi : Polynomial kRes
  psi_monic : psi.Monic
  psi_irreducible : Irreducible psi
  residualQuot : Polynomial kRes
  residual_factorization : residual = psi * residualQuot
  residual_multiplicity_one : ¬ psi ∣ residualQuot
  leaf : Polynomial O
  leaf_monic : leaf.Monic
  leaf_dvd_input : leaf ∣ g
  exactLeaf : leaf = phi

/-- External same-socket recenter-step export.  All realization views and all cite data occur
under one existential witness, preventing a step from a different realization being spliced
into the socket. -/
def RecenterStep
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
    (∃ (kRes : Type) (_fRes : Field kRes),
      Nonempty (GNCitePayload (Kt := Kt) (L := L) A B.F B'.Φ kRes)) ∧
    Nonempty (MP1StepCore.{uW} B B')

/-- Honest MP1: only successors actually exported by the same realization are quantified. -/
def MP1CarrierLive
    {O : Type} [CommRing O] {K : Type} [Field K]
    (C : Ladder.SlotCarrier O K) (B : Ladder.BlockData C)
    (G : Type uG) [CommGroup G] (Kt : Type uKt) [Field Kt]
    (L : Type uL) [Field L] [Algebra Kt L]
    (N : Gauge.NormSection G) (v : ℕ → (G →* Multiplicative ℤ))
    (rho : ∀ j : ℕ, MonoidHom.ker (v j) →* Lˣ) (q : ℕ → ℤ) (n : ℕ) : Prop :=
  ∀ (Lambda : Polynomial O), Lambda ≠ 0 → Lambda.natDegree < C.D →
    ∀ (B' : Ladder.BlockData C), B'.Φ = B.Φ - Lambda → B'.Φ ∣ B.F →
      RecenterStep.{uW, uG, uKt, uL} C B B' G Kt L N v rho q n Lambda →
      Nonempty (Ladder.MidPeelEmission.{0, 0, uW} B B')

/-! ## §2 The A-I.7 superseding supply record -/

/-- The A-I.7 supply record.  `package`/`lb1` are byte-identical to E.24's `LadderSupply`
fields; `vartheta` is byte-identical to A-I.6's live field (`LadderSupplyLive`,
`I10LadderLive.lean`); ONLY `mp1` is replaced by the same-realization `MP1CarrierLive`
(the REX export design).  Supersedes `LadderSupplyLive` as the capstone `ladder` field's
result record; that record stays byte-frozen as the refuted tension record.
NEW STATEMENT (review). -/
structure LadderSupplyLive₂ {O : Type} [CommRing O] {K : Type} [Field K]
    (C : Ladder.SlotCarrier O K) (B : Ladder.BlockData C)
    (G : Type uG) [CommGroup G] (Kt : Type uKt) [Field Kt]
    (L : Type uL) [Field L] [Algebra Kt L]
    (N : Gauge.NormSection G) (v : ℕ → (G →* Multiplicative ℤ))
    (ρ : ∀ j : ℕ, MonoidHom.ker (v j) →* Lˣ) (q : ℕ → ℤ) (n : ℕ) : Prop where
  package : Ladder.HE7APackage.{0, 0, uW} C B
  lb1 : Ladder.LB1Carrier.{0, 0, uW} C B
  mp1 : MP1CarrierLive.{uW, uG, uKt, uL} C B G Kt L N v ρ q n
  vartheta : ∀ i ≥ 3,
    CanonicalLadderLiveAt.{uG, uKt, uL} C B G Kt L N v ρ q n i →
      Ladder.VarthetaRes G Kt L N v ρ q i

/-! ## §3 Supersession-direction pins (nothing strengthened, machine-visible) -/

/-- ★ SUPERSESSION PIN (mp1 level): the OLD unrestricted `MP1Carrier` implies the live
carrier — the amendment only RESTRICTS the demanded successors (adds the `RecenterStep`
premise); it smuggles no strengthening.  The CONVERSE is exactly what REX refuted at the
landed degree-4 S2 socket, and is deliberately absent. -/
theorem mp1CarrierLive_of_mp1
    {O : Type} [CommRing O] {K : Type} [Field K]
    {C : Ladder.SlotCarrier O K} {B : Ladder.BlockData C}
    (G : Type uG) [CommGroup G] (Kt : Type uKt) [Field Kt]
    (L : Type uL) [Field L] [Algebra Kt L]
    (N : Gauge.NormSection G) (v : ℕ → (G →* Multiplicative ℤ))
    (ρ : ∀ j : ℕ, MonoidHom.ker (v j) →* Lˣ) (q : ℕ → ℤ) (n : ℕ)
    (h : Ladder.MP1Carrier.{0, 0, uW} C B) :
    MP1CarrierLive.{uW, uG, uKt, uL} C B G Kt L N v ρ q n :=
  fun Lambda hne hdeg B' hkey hdvd _ => h Lambda hne hdeg B' hkey hdvd

/-- ★ SUPERSESSION PIN (record level): A-I.6's record implies the A-I.7 record —
`package`/`lb1`/`vartheta` pass through unchanged and the `mp1` leg forgets its new
premise. -/
theorem ladderSupplyLive₂_of_live
    {O : Type} [CommRing O] {K : Type} [Field K]
    {C : Ladder.SlotCarrier O K} {B : Ladder.BlockData C}
    {G : Type uG} [CommGroup G] {Kt : Type uKt} [Field Kt]
    {L : Type uL} [Field L] [Algebra Kt L]
    {N : Gauge.NormSection G} {v : ℕ → (G →* Multiplicative ℤ)}
    {ρ : ∀ j : ℕ, MonoidHom.ker (v j) →* Lˣ} {q : ℕ → ℤ} {n : ℕ}
    (h : LadderSupplyLive.{uW, uG, uKt, uL} C B G Kt L N v ρ q n) :
    LadderSupplyLive₂.{uW, uG, uKt, uL} C B G Kt L N v ρ q n :=
  ⟨h.package, h.lb1, mp1CarrierLive_of_mp1 G Kt L N v ρ q n h.mp1, h.vartheta⟩

end Uniformity.Density.IFC5

end

/-! ## AXCHECK FOOTER — expect Lean core `{propext, Classical.choice, Quot.sound}` only.
Statement carriers + supersession bookkeeping; nothing here may add to the trusted base. -/

#print axioms Uniformity.Density.IFC5.MP1StepCore
#print axioms Uniformity.Density.IFC5.GNCitePayload
#print axioms Uniformity.Density.IFC5.RecenterStep
#print axioms Uniformity.Density.IFC5.MP1CarrierLive
#print axioms Uniformity.Density.IFC5.LadderSupplyLive₂
#print axioms Uniformity.Density.IFC5.mp1CarrierLive_of_mp1
#print axioms Uniformity.Density.IFC5.ladderSupplyLive₂_of_live
