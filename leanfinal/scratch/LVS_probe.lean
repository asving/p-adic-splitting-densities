import Uniformity.ChapI.IFC5
import Uniformity.ChapD.D62w

/-!
# LVS statement probe

This file validates the live-vartheta supplier surface.  It deliberately separates:

* the proved arithmetic vacuity at a realization of depth `2`;
* the non-circular, witness-attached tau-residue export sufficient for `VarthetaRes`;
* the exact bridge to `IFC5.LadderSupplyLive.vartheta`.

There is no `sorry` and no new axiom.
-/

set_option linter.style.longLine false
set_option linter.unusedVariables false

noncomputable section

namespace Uniformity.Density.LVSProbe

open Uniformity.Density Uniformity.Density.Gauge Uniformity.Density.Tower

universe uG uKt uL

/-! ## 1. The depth-two arithmetic discharge -/

/-- At depth two, no index can be both demanded (`i ≥ 3`) and gauge-live
(`1 ≤ i < 2`).  The result family is arbitrary: the proof uses no vartheta mathematics. -/
theorem vartheta_live_r_two_vacuous
    {G : Type uG} [CommGroup G] {Kt : Type uKt} [Field Kt]
    {L : Type uL} [Field L] [Algebra Kt L]
    (N : NormSection G) (v : ℕ → (G →* Multiplicative ℤ))
    (ρ : ∀ j : ℕ, MonoidHom.ker (v j) →* Lˣ) (q : ℕ → ℤ) :
    ∀ i, 3 ≤ i → GaugeLive 2 i → Ladder.VarthetaRes G Kt L N v ρ q i := by
  intro i hi hLive
  rcases hLive with ⟨hi1, hi2⟩
  exfalso
  exact (by omega : False)

/-- The same vacuity in the shape naturally obtained after unpacking an explicit arising
realization whose depth is known to be two. -/
theorem vartheta_live_of_realization_depth_two
    {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {Kt : Type uKt} [Field Kt] {E : Type} [Field E]
    {L : Type uL} [Field L] [Algebra Kt L] {n : ℕ}
    {core : ArisingCore (O := O) Kt L n}
    {Aℛ : ChainRealization (O := O) (π := core.π) (F := core.F) (H₀ := core.H₀)
      (hpin := core.hpin) core.T Kt E L}
    (X : RealizedInput core Aℛ) (hr : core.r = 2)
    {G : Type uG} [CommGroup G]
    (N : NormSection G) (v : ℕ → (G →* Multiplicative ℤ))
    (ρ : ∀ j : ℕ, MonoidHom.ker (v j) →* Lˣ) (q : ℕ → ℤ) :
    ∀ i, 3 ≤ i → GaugeLive core.r i → Ladder.VarthetaRes G Kt L N v ρ q i := by
  intro i hi hLive
  exfalso
  rw [hr] at hLive
  rcases hLive with ⟨hi1, hi2⟩
  omega

/-! ## 2. The witness-attached export and the general supplier -/

/-- The exact non-circular per-level datum sufficient for the vartheta socket.  It is
attached after an explicit `RealizedInput X`, its gauge equivalence, and the exact
`GaugeFamilyViewEq` matching the external socket.  Its mathematical fields are the two
tau-letter conclusions used by D62w's landed reduction: kernel membership and embedded
`Kt`-unit residue.  It does not contain `HVarthetaRes` or `VarthetaRes`.

The `view` field is intentionally present: it prevents a free tau package belonging to a
different realization or different external `(N,v,ρ,q)` from being used at this site. -/
structure VarthetaTauLevelExport
    {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {Kt : Type uKt} [Field Kt] {E : Type} [Field E]
    {L : Type uL} [Field L] [Algebra Kt L] {n : ℕ}
    {core : ArisingCore (O := O) Kt L n}
    {Aℛ : ChainRealization (O := O) (π := core.π) (F := core.F) (H₀ := core.H₀)
      (hpin := core.hpin) core.T Kt E L}
    (X : RealizedInput core Aℛ)
    (G : Type uG) [CommGroup G] (eG : G ≃* GaugeLattice.{uG} core.r)
    (N : NormSection G) (v : ℕ → (G →* Multiplicative ℤ))
    (ρ : ∀ j : ℕ, MonoidHom.ker (v j) →* Lˣ) (q : ℕ → ℤ)
    (j : ℕ) (hj : GaugeLive core.r j) : Prop where
  view : GaugeFamilyViewEq X (N.transport eG)
    (fun k => (v k).comp eG.symm.toMonoidHom)
    (fun k => (ρ k).comp (Tower.C130s18.kerComapAlong eG (v k))) q
  tau_mem : ∀ s : ℕ,
    N.tau ((s : ℤ) * q j) (q j) ∈ MonoidHom.ker (v j)
  tau_value : ∀ s : ℕ, ∃ u : Ktˣ,
    (((ρ j) ⟨N.tau ((s : ℤ) * q j) (q j), tau_mem s⟩ : Lˣ) : L) =
      algebraMap Kt L (u : Kt)

/-- General live-site supplier from the exact per-level export.  This is D62w's tau
reduction followed by E.61's one-field constructor. -/
theorem varthetaRes_of_live_of_exports
    {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {Kt : Type uKt} [Field Kt] {E : Type} [Field E]
    {L : Type uL} [Field L] [Algebra Kt L] {n : ℕ}
    {core : ArisingCore (O := O) Kt L n}
    {Aℛ : ChainRealization (O := O) (π := core.π) (F := core.F) (H₀ := core.H₀)
      (hpin := core.hpin) core.T Kt E L}
    {X : RealizedInput core Aℛ}
    {G : Type uG} [CommGroup G] {eG : G ≃* GaugeLattice.{uG} core.r}
    {N : NormSection G} {v : ℕ → (G →* Multiplicative ℤ)}
    {ρ : ∀ j : ℕ, MonoidHom.ker (v j) →* Lˣ} {q : ℕ → ℤ}
    {j : ℕ} {hj : GaugeLive core.r j}
    (S : VarthetaTauLevelExport X G eG N v ρ q j hj) :
    Ladder.VarthetaRes G Kt L N v ρ q j := by
  exact ⟨hvarthetaRes_of_tau_letters (v j) (ρ j) (q j) S.tau_mem S.tau_value⟩

/-- WLE-style owner exporter: explicit arising witness first, then its gauge-family view,
then exactly the signed intersection `3 ≤ j ∧ GaugeLive core.r j`.  This does not demand
irrelevant exports at the shallow live indices `1` and `2`. -/
def VarthetaTauLiveExporter (n : ℕ) : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (Kt : Type uKt) [Field Kt] (E : Type) [Field E]
    (L : Type uL) [Field L] [Algebra Kt L]
    (core : ArisingCore (O := O) Kt L n)
    (Aℛ : ChainRealization (O := O) (π := core.π) (F := core.F) (H₀ := core.H₀)
      (hpin := core.hpin) core.T Kt E L)
    (X : RealizedInput core Aℛ)
    (G : Type uG) [CommGroup G] (eG : G ≃* GaugeLattice.{uG} core.r)
    (N : NormSection G) (v : ℕ → (G →* Multiplicative ℤ))
    (ρ : ∀ j : ℕ, MonoidHom.ker (v j) →* Lˣ) (q : ℕ → ℤ),
    GaugeFamilyViewEq X (N.transport eG)
      (fun k => (v k).comp eG.symm.toMonoidHom)
      (fun k => (ρ k).comp (Tower.C130s18.kerComapAlong eG (v k))) q →
    ∀ j, 3 ≤ j → (hj : GaugeLive core.r j) →
      Nonempty (VarthetaTauLevelExport X G eG N v ρ q j hj)

/-- Exact bridge to the signed `LadderSupplyLive.vartheta` field shape.  The realization
unpacked here is the very witness inside `CanonicalLadderLiveAt`; the exporter is applied to
that same `core/Aℛ/X/eG` and to its own `GaugeFamilyViewEq` proof. -/
theorem ladderSupplyLive_vartheta_of_exports {n : ℕ}
    (hExports : VarthetaTauLiveExporter.{uG, uKt, uL} n)
    {O : Type} [CommRing O] {K : Type} [Field K]
    (C : Ladder.SlotCarrier O K) (B : Ladder.BlockData C)
    (G : Type uG) [CommGroup G] (Kt : Type uKt) [Field Kt]
    (L : Type uL) [Field L] [Algebra Kt L]
    (N : NormSection G) (v : ℕ → (G →* Multiplicative ℤ))
    (ρ : ∀ j : ℕ, MonoidHom.ker (v j) →* Lˣ) (q : ℕ → ℤ) :
    ∀ i ≥ 3,
      IFC5.CanonicalLadderLiveAt.{uG, uKt, uL} C B G Kt L N v ρ q n i →
        Ladder.VarthetaRes G Kt L N v ρ q i := by
  intro i hi hLive
  rcases hLive with
    ⟨dom, dvr, E, fE, core, Aℛ, X, eK, eG, hslot, hblock, hview, hgi⟩
  letI : IsDomain O := dom
  letI : IsDiscreteValuationRing O := dvr
  letI : Field E := fE
  obtain ⟨S⟩ := hExports O Kt E L core Aℛ X G eG N v ρ q hview i hi hgi
  exact varthetaRes_of_live_of_exports S

/-! ## 3. A field-constructor pin -/

/-- Constructor pin showing that the preceding theorem has literally the fourth-field
shape of `LadderSupplyLive`; no adapter or strengthening is hidden at assembly. -/
def ladderSupplyLive_of_vartheta_exports {n : ℕ}
    (hExports : VarthetaTauLiveExporter.{uG, uKt, uL} n)
    {O : Type} [CommRing O] {K : Type} [Field K]
    (C : Ladder.SlotCarrier O K) (B : Ladder.BlockData C)
    (G : Type uG) [CommGroup G] (Kt : Type uKt) [Field Kt]
    (L : Type uL) [Field L] [Algebra Kt L]
    (N : NormSection G) (v : ℕ → (G →* Multiplicative ℤ))
    (ρ : ∀ j : ℕ, MonoidHom.ker (v j) →* Lˣ) (q : ℕ → ℤ)
    (package : Ladder.HE7APackage.{0, 0, 0} C B)
    (lb1 : Ladder.LB1Carrier.{0, 0, 0} C B)
    (mp1 : Ladder.MP1Carrier.{0, 0, 0} C B) :
    IFC5.LadderSupplyLive.{0, uG, uKt, uL} C B G Kt L N v ρ q n :=
  ⟨package, lb1, mp1,
    ladderSupplyLive_vartheta_of_exports hExports C B G Kt L N v ρ q⟩

end Uniformity.Density.LVSProbe

end

/-! ## Axiom audit -/

#print axioms Uniformity.Density.LVSProbe.vartheta_live_r_two_vacuous
#print axioms Uniformity.Density.LVSProbe.vartheta_live_of_realization_depth_two
#print axioms Uniformity.Density.LVSProbe.VarthetaTauLevelExport
#print axioms Uniformity.Density.LVSProbe.varthetaRes_of_live_of_exports
#print axioms Uniformity.Density.LVSProbe.VarthetaTauLiveExporter
#print axioms Uniformity.Density.LVSProbe.ladderSupplyLive_vartheta_of_exports
#print axioms Uniformity.Density.LVSProbe.ladderSupplyLive_of_vartheta_exports
