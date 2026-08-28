import Uniformity.ChapI.IFC5
import Uniformity.ChapD.D62w
import Uniformity.ChapC.C130cr

/-!
# TAU source-faithful tau-export probe

This scratch file does not alter a landed interface.  It validates the minimal owner-attached
source surface selected by TAU: a tau-to-generator-word law for the realization's own
canonical read, together with descent of the existing canonical wrap/letter values to the
embedded terminal field.  The consumer record below is byte-for-byte the mathematical part
of `LVSProbe.VarthetaTauLevelExport`.
-/

set_option linter.style.longLine false
set_option linter.unusedVariables false

noncomputable section

namespace Uniformity.Density.TAUProbe

open Uniformity.Density Uniformity.Density.Gauge Uniformity.Density.Tower

universe uG uKt uL

/-- The unit-group map induced by the specified terminal-field embedding. -/
abbrev unitAlgebraMap {Kt : Type uKt} [Field Kt] {L : Type uL} [Field L]
    [Algebra Kt L] : Ktˣ →* Lˣ :=
  Units.map (algebraMap Kt L)

/-- Tau membership is not new source data: at the realization's own canonical normalizer and
height it follows from the landed exact-height arena. -/
theorem canonical_tau_mem
    {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {Kt : Type uKt} [Field Kt] {E : Type} [Field E]
    {L : Type uL} [Field L] [Algebra Kt L] {n : ℕ}
    {core : ArisingCore (O := O) Kt L n}
    {Aℛ : ChainRealization (O := O) (π := core.π) (F := core.F) (H₀ := core.H₀)
      (hpin := core.hpin) core.T Kt E L}
    (X : RealizedInput core Aℛ) {j : ℕ} (hj : GaugeLive core.r j) (a b : ℤ) :
    (Aℛ.normalizer.arenaNormSection0.transport (gaugeLatticeEquiv core.r).symm).tau a b ∈
      MonoidHom.ker (levelHeight core.T ⟨j, hj⟩ :
        GaugeLattice.{uG} core.r →* Multiplicative ℤ) := by
  have hr : 1 < core.r := by rcases hj with ⟨hj1, hjr⟩; omega
  have hexact (k : ℤ) :
      levelHeight core.T ⟨j, hj⟩
        ((Aℛ.normalizer.arenaNormSection0.transport
          (gaugeLatticeEquiv core.r).symm).n k) = Multiplicative.ofAdd k := by
    simpa [NormSection.transport, LaurentNormalizer.arenaNormSection0,
      levelHeight, levelHeight0] using
        Aℛ.normalizer.exact_height j hj.stageLive k
  rw [MonoidHom.mem_ker, NormSection.tau, map_mul, map_mul, map_inv,
    hexact, hexact, hexact, ← ofAdd_add]
  simp

/-- Local mirror of LVS's exact consumer record.  It is repeated because scratch files are
not importable modules of the `Uniformity` library. -/
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
    (fun k ↦ (v k).comp eG.symm.toMonoidHom)
    (fun k ↦ (ρ k).comp (Tower.C130s18.kerComapAlong eG (v k))) q
  tau_mem : ∀ s : ℕ,
    N.tau ((s : ℤ) * q j) (q j) ∈ MonoidHom.ker (v j)
  tau_value : ∀ s : ℕ, ∃ u : Ktˣ,
    (((ρ j) ⟨N.tau ((s : ℤ) * q j) (q j), tau_mem s⟩ : Lˣ) : L) =
      algebraMap Kt L (u : Kt)

/-- The minimal genuinely new source field.  It identifies the values of the already-landed
canonical generators with units of the specified terminal field.  The generators themselves
and their canonical values are not copied: they are C130cr's `wrapValue`/`letterValue` from
the realization's own node and normalizer. -/
structure CanonicalGeneratorDescent
    {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {Kt : Type uKt} [Field Kt] {E : Type} [Field E]
    {L : Type uL} [Field L] [Algebra Kt L] {n : ℕ}
    {core : ArisingCore (O := O) Kt L n}
    (Aℛ : ChainRealization (O := O) (π := core.π) (F := core.F) (H₀ := core.H₀)
      (hpin := core.hpin) core.T Kt E L)
    (j : ℕ) (hj : GaugeLive core.r j) : Prop where
  wrap : ∃ u : Ktˣ,
    Aℛ.node.wrapValue hj.stageLive = unitAlgebraMap u
  letter : ∀ a : Fin (j - 1), ∃ u : Ktˣ,
    Aℛ.node.letterValue Aℛ.normalizer hj.stageLive a = unitAlgebraMap u

/-- The source-faithful per-level mechanism.  `tau_word` is the general-depth exponent
descent, stated at the exact external view but with the right side fixed to this
realization's existing canonical wrap and letter values.  The final field is the
minimal new source dictionary: those canonical generator values descend through the
specified `Kt → L` embedding.  No field mentions `HVarthetaRes`, `VarthetaRes`, or the
desired embedded value of the tau word itself. -/
structure CanonicalTauLetterSource
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
    (fun k ↦ (v k).comp eG.symm.toMonoidHom)
    (fun k ↦ (ρ k).comp (Tower.C130s18.kerComapAlong eG (v k))) q
  tau_mem : ∀ s : ℕ,
    N.tau ((s : ℤ) * q j) (q j) ∈ MonoidHom.ker (v j)
  tau_word : ∀ s : ℕ, ∃ (m : ℤ) (t : Fin (j - 1) → ℤ),
    ρ j ⟨N.tau ((s : ℤ) * q j) (q j), tau_mem s⟩ =
      Aℛ.node.wrapValue hj.stageLive ^ m *
        ∏ a, Aℛ.node.letterValue Aℛ.normalizer hj.stageLive a ^ t a
  generator_descent : CanonicalGeneratorDescent Aℛ j hj

/-- The chosen source mechanism discharges LVS's exact per-level export.  The proof is only
multiplicativity: once tau is a word in canonical generators and each generator descends,
the whole tau word descends. -/
theorem varthetaTauLevelExport_of_canonicalTauLetterSource
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
    (S : CanonicalTauLetterSource X G eG N v ρ q j hj) :
    VarthetaTauLevelExport X G eG N v ρ q j hj where
  view := S.view
  tau_mem := S.tau_mem
  tau_value := by
    intro s
    obtain ⟨m, t, hword⟩ := S.tau_word s
    obtain ⟨u₀, hu₀⟩ := S.generator_descent.wrap
    choose u hu using S.generator_descent.letter
    refine ⟨u₀ ^ m * ∏ a, u a ^ t a, ?_⟩
    have hUnits :
        ρ j ⟨N.tau ((s : ℤ) * q j) (q j), S.tau_mem s⟩ =
          unitAlgebraMap (u₀ ^ m * ∏ a, u a ^ t a) := by
      rw [hword, hu₀]
      simp_rw [hu]
      rw [map_mul, map_zpow, map_prod]
      simp only [map_zpow]
    exact congrArg Units.val hUnits

/-- The universal source supplier, with exactly LVS's owner and signed live-range binders. -/
def CanonicalTauLiveSource (n : ℕ) : Prop :=
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
      (fun k ↦ (v k).comp eG.symm.toMonoidHom)
      (fun k ↦ (ρ k).comp (Tower.C130s18.kerComapAlong eG (v k))) q →
    ∀ j, 3 ≤ j → (hj : GaugeLive core.r j) →
      Nonempty (CanonicalTauLetterSource X G eG N v ρ q j hj)

/-- Local mirror of LVS's WLE-style target exporter. -/
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
      (fun k ↦ (v k).comp eG.symm.toMonoidHom)
      (fun k ↦ (ρ k).comp (Tower.C130s18.kerComapAlong eG (v k))) q →
    ∀ j, 3 ≤ j → (hj : GaugeLive core.r j) →
      Nonempty (VarthetaTauLevelExport X G eG N v ρ q j hj)

/-- End-to-end owner bridge: the source-faithful supplier inhabits LVS's exporter without
changing any quantifier or choosing a different realization/view. -/
theorem varthetaTauLiveExporter_of_canonicalTauLiveSource {n : ℕ}
    (hSource : CanonicalTauLiveSource.{uG, uKt, uL} n) :
    VarthetaTauLiveExporter.{uG, uKt, uL} n := by
  intro O _ _ _ Kt _ E _ L _ _ core Aℛ X G _ eG N v ρ q hview j hj3 hj
  obtain ⟨S⟩ := hSource O Kt E L core Aℛ X G eG N v ρ q hview j hj3 hj
  exact ⟨varthetaTauLevelExport_of_canonicalTauLetterSource S⟩

/-- The final consumer is exactly D62w's landed tau reduction; no additional hypothesis is
used after the source record has been converted to the LVS record. -/
theorem varthetaRes_of_canonicalTauLetterSource
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
    (S : CanonicalTauLetterSource X G eG N v ρ q j hj) :
    Ladder.VarthetaRes G Kt L N v ρ q j := by
  let T := varthetaTauLevelExport_of_canonicalTauLetterSource S
  exact ⟨hvarthetaRes_of_tau_letters (v j) (ρ j) (q j) T.tau_mem T.tau_value⟩

end Uniformity.Density.TAUProbe

end

/-! ## Axiom audit -/

#print axioms Uniformity.Density.TAUProbe.VarthetaTauLevelExport
#print axioms Uniformity.Density.TAUProbe.canonical_tau_mem
#print axioms Uniformity.Density.TAUProbe.CanonicalGeneratorDescent
#print axioms Uniformity.Density.TAUProbe.CanonicalTauLetterSource
#print axioms Uniformity.Density.TAUProbe.varthetaTauLevelExport_of_canonicalTauLetterSource
#print axioms Uniformity.Density.TAUProbe.CanonicalTauLiveSource
#print axioms Uniformity.Density.TAUProbe.VarthetaTauLiveExporter
#print axioms Uniformity.Density.TAUProbe.varthetaTauLiveExporter_of_canonicalTauLiveSource
#print axioms Uniformity.Density.TAUProbe.varthetaRes_of_canonicalTauLetterSource
