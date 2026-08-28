/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapC.C130s18
import Uniformity.ChapE.E24

/-!
# Uniformity.ChapI.I10LadderLive — the live-range ladder record, promoted ahead of I.10
(AMENDMENT A-I.6, 2026-08-28)

**[A-I.6 ENACTMENT, 2026-08-28 — unit AI6E; adjudication `runs/wave-c/verdict_AI6.md`.]**
The two declarations below are MOVED byte-for-byte from `Uniformity/ChapI/IFC5.lean`
(namespace unchanged: `Uniformity.Density.IFC5`), so that the signed capstone `ladder`
field (`I10_I15_I18.lean`, NODE I.10) can return `LadderSupplyLive` without the import
cycle `I10_I15_I18 → IFC5 → IFC0 → I10_I15_I18`.  This file is the acyclic home: it
imports only chapter C's `C130s18` (the realization/view carriers) and chapter E's
`E24` (the ladder record vocabulary), both already below I.10 in the import order.

## Why the rebind is forced (the machine record)

The pre-A-I.6 signed field returned E.24's unbounded `LadderSupply`, and
`scratch/AI6_probe.lean` (Lean-core, exit 0; the pre-rebind refutation is archived at
commit `ce301df1`) proves

* `AI6Probe.ladderField_four_refuted : ¬ IFC0.LadderField 4`
* `AI6Probe.capstoneHypotheses_four_refuted : ¬ CapstoneHypotheses 4`

— the signed block's bytes were machine-EMPTY at degree 4, so an interpretive rider was
impossible (the A-I.5 rider precedent requires the signed field to remain inhabitable in
principle).  IFC0's `LadderField`, `LadderVarthetaSupplier`, and their exact split stay
byte-frozen there as the refuted tension record; `IFC5.LadderFieldLive` remains the
corrected campaign target.

Statement provenance: both bodies byte-identical to the LVT landing (`IFC5.lean`,
2026-08-28; probe shapes `scratch/VAUD_probe.lean`).  Zero `sorry`, zero new axiom;
AxChk footer expects Lean core only.
-/

set_option linter.style.longLine false

noncomputable section

namespace Uniformity.Density.IFC5

open Uniformity.Density

universe uW uG uKt uL

/-- **The live-index predicate** (the owner-amendment carrier, `scratch/VAUD_probe.lean`
byte-shape): the socket data `(C, B, N, v, ρ, q)` admit a realization witnessing the
SAME external views demanded by `CanonicalLadderConfig` — slot view, block view, gauge
family view — whose gauge range contains `i` (`GaugeLive core.r i`).  Liveness and the
family views belong to ONE witness, so a junk witness cannot buy liveness the views do
not see (the D-D12 anti-cook guard).  NEW STATEMENT (review). -/
def CanonicalLadderLiveAt.{uG', uKt', uL'}
    {O : Type} [CommRing O] {K : Type} [Field K]
    (C : Ladder.SlotCarrier O K) (B : Ladder.BlockData C)
    (G : Type uG') [CommGroup G] (Kt : Type uKt') [Field Kt]
    (L : Type uL') [Field L] [Algebra Kt L]
    (N : Gauge.NormSection G) (v : ℕ → (G →* Multiplicative ℤ))
    (ρ : ∀ j : ℕ, MonoidHom.ker (v j) →* Lˣ) (q : ℕ → ℤ) (n i : ℕ) : Prop :=
  ∃ (_dom : IsDomain O) (_dvr : IsDiscreteValuationRing O)
    (E : Type) (fE : Field E) (core : Tower.ArisingCore (O := O) Kt L n)
    (A : Tower.ChainRealization (O := O) (π := core.π) (F := core.F)
      (H₀ := core.H₀) (hpin := core.hpin) (fieldE := fE) core.T Kt E L)
    (X : Tower.RealizedInput core A)
    (eK : core.T.fld core.i ≃+* K) (eG : G ≃* Tower.GaugeLattice.{uG'} core.r),
    Tower.SlotViewEq X eK C ∧
    (∃ hC : C = X.stageCarrierTransport eK, Tower.BlockViewEq X eK (hC ▸ B)) ∧
    Tower.GaugeFamilyViewEq X (N.transport eG)
      (fun j => (v j).comp eG.symm.toMonoidHom)
      (fun j => (ρ j).comp (Tower.C130s18.kerComapAlong eG (v j))) q ∧
    Tower.GaugeLive core.r i

/-- The repaired result record.  Its first three fields are byte-identical to E.24's
`LadderSupply`; ONLY the vartheta field receives the live-index premise.
NEW STATEMENT (review). -/
structure LadderSupplyLive {O : Type} [CommRing O] {K : Type} [Field K]
    (C : Ladder.SlotCarrier O K) (B : Ladder.BlockData C)
    (G : Type uG) [CommGroup G] (Kt : Type uKt) [Field Kt]
    (L : Type uL) [Field L] [Algebra Kt L]
    (N : Gauge.NormSection G) (v : ℕ → (G →* Multiplicative ℤ))
    (ρ : ∀ j : ℕ, MonoidHom.ker (v j) →* Lˣ) (q : ℕ → ℤ) (n : ℕ) : Prop where
  package : Ladder.HE7APackage.{0, 0, uW} C B
  lb1 : Ladder.LB1Carrier.{0, 0, uW} C B
  mp1 : Ladder.MP1Carrier.{0, 0, uW} C B
  vartheta : ∀ i ≥ 3,
    CanonicalLadderLiveAt.{uG, uKt, uL} C B G Kt L N v ρ q n i →
      Ladder.VarthetaRes G Kt L N v ρ q i

end Uniformity.Density.IFC5

end

/-! ## AXCHECK FOOTER — expect Lean core `{propext, Classical.choice, Quot.sound}` only.
Statement carriers; nothing here may add to the trusted base. -/

#print axioms Uniformity.Density.IFC5.CanonicalLadderLiveAt
#print axioms Uniformity.Density.IFC5.LadderSupplyLive
