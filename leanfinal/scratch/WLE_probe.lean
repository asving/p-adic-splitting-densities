import Uniformity.ChapI.IFC4

/-!
Statement-level probe for unit WLE.  It checks the dependent statement shapes proposed by
the design verdict and contains no `sorry`.
-/

set_option linter.style.longLine false

noncomputable section

namespace Uniformity.Density.WLEProbe

open Uniformity.Density Uniformity.Density.Gauge Uniformity.Density.Tower

universe uE uG uKt uL

/-- A positive, witness-dependent `WleCleared` site at level `j`.  The calculus family,
top receiver, and GC-13 law all depend on the explicit realized witness `X`; in particular
there is no free site family outside the arising-witness binder. -/
structure WleClearedLevelExport
    {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {Kt : Type uKt} [Field Kt] {E : Type uE} [Field E]
    {L : Type uL} [Field L] [Algebra Kt L] {n : ℕ}
    {core : ArisingCore (O := O) Kt L n}
    {Aℛ : ChainRealization (O := O) (π := core.π) (F := core.F) (H₀ := core.H₀)
      (hpin := core.hpin) core.T Kt E L}
    (X : RealizedInput core Aℛ) (j : ℕ) (hjr : j ≤ core.r) : Type (max uE uG uKt uL) where
  e' : ℕ
  f' : ℕ
  u' : ℕ
  f_pos : 0 < f'
  calculus : ∀ i, (hi : i ≤ core.r) → FGMNCalculus (core.T.trunc i hi) e' f' u'
  cleared : WleCleared core.T e' f' u' calculus j
  wiring : IFC3.GC13Wiring
    (Aℛ.normalizer.arenaNormSection0.transport
      (show GaugeLattice.{uG} core.r ≃* GaugeLattice0 core.r from
        gaugeLatticeEquiv core.r).symm)
    (useHeightFamily X j) (towerReadFamily X j) (calculus j hjr)
    (Aℛ.receiver.levelHom j)

/-- The missing per-level exporter: after the witness is explicit, every deep-live level
exports a positive, canonical `WleCleared` site. -/
def WleClearedPerLevelExporter
    {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {Kt : Type uKt} [Field Kt] {E : Type uE} [Field E]
    {L : Type uL} [Field L] [Algebra Kt L] {n : ℕ}
    {core : ArisingCore (O := O) Kt L n}
    {Aℛ : ChainRealization (O := O) (π := core.π) (F := core.F) (H₀ := core.H₀)
      (hpin := core.hpin) core.T Kt E L}
    (X : RealizedInput core Aℛ) : Prop :=
  ∀ j, (hj : DeepLive core.r j) →
    Nonempty (WleClearedLevelExport.{uE, uG, uKt, uL} X j hj.2.le)

/-- Universal wired supplier at explicit arising witnesses.  Its conclusion is evaluated
only at `X`'s own arena/use-height/read/peel-unit exports, and its calculus/receiver are
the ones in the level export. -/
def UniversalWiredDeepGentowSupplier (n : ℕ) : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (Kt : Type uKt) [Field Kt] (E : Type uE) [Field E]
    (L : Type uL) [Field L] [Algebra Kt L]
    (core : ArisingCore (O := O) Kt L n)
    (Aℛ : ChainRealization (O := O) (π := core.π) (F := core.F) (H₀ := core.H₀)
      (hpin := core.hpin) core.T Kt E L)
    (X : RealizedInput core Aℛ),
    WleClearedPerLevelExporter.{uE, uG, uKt, uL} X →
      ∀ j, (hj : DeepLive core.r j) →
        ∃ S : WleClearedLevelExport.{uE, uG, uKt, uL} X j hj.2.le,
          IFC3.WiredGentowDemand
            (arenaFamily.{uE, uG, uKt, uL} X
              (by rcases hj with ⟨hj3, hjr⟩; omega) j)
            (useHeightFamily X j) (towerReadFamily X j)
            (Aℛ.node.peelUnitFamily j) (S.calculus j hj.2.le)
            (Aℛ.receiver.levelHom j)

/-- The exported cumulative datum supplies its top `GENTOW5WCleared` instance at a deep
level. -/
theorem WleClearedLevelExport.top_cleared
    {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {Kt : Type uKt} [Field Kt] {E : Type uE} [Field E]
    {L : Type uL} [Field L] [Algebra Kt L] {n : ℕ}
    {core : ArisingCore (O := O) Kt L n}
    {Aℛ : ChainRealization (O := O) (π := core.π) (F := core.F) (H₀ := core.H₀)
      (hpin := core.hpin) core.T Kt E L}
    {X : RealizedInput core Aℛ} {j : ℕ} (hj : DeepLive core.r j)
    (S : WleClearedLevelExport.{uE, uG, uKt, uL} X j hj.2.le) :
    GENTOW5WCleared (core.T.trunc j hj.2.le) S.e' S.f' S.u'
      (S.calculus j hj.2.le) := by
  exact S.cleared j hj.1 le_rfl hj.2.le

/-- OPEN-MATH probe: the general theta dictionary at the exported site. -/
def ThetaCompatibleAt
    {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {Kt : Type uKt} [Field Kt] {E : Type uE} [Field E]
    {L : Type uL} [Field L] [Algebra Kt L] {n : ℕ}
    {core : ArisingCore (O := O) Kt L n}
    {Aℛ : ChainRealization (O := O) (π := core.π) (F := core.F) (H₀ := core.H₀)
      (hpin := core.hpin) core.T Kt E L}
    (X : RealizedInput core Aℛ) (hr : 1 < core.r) {j : ℕ} {hjr : j ≤ core.r}
    (S : WleClearedLevelExport.{uE, uG, uKt, uL} X j hjr) : Prop :=
  ∀ s, 1 ≤ s → s ≤ S.f' →
    ((arenaFamily.{uE, uG, uKt, uL} X hr j).theta (useHeightFamily X j) s : Kt) *
      Aℛ.receiver.levelHom j ((S.calculus j hjr).thetaRatioCleared s) = 1

/-- OPEN-MATH probe: the cleared witness is the witness's own exported peel unit. -/
def PeelCompatibleAt
    {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {Kt : Type uKt} [Field Kt] {E : Type uE} [Field E]
    {L : Type uL} [Field L] [Algebra Kt L] {n : ℕ}
    {core : ArisingCore (O := O) Kt L n}
    {Aℛ : ChainRealization (O := O) (π := core.π) (F := core.F) (H₀ := core.H₀)
      (hpin := core.hpin) core.T Kt E L}
    (X : RealizedInput core Aℛ) {j : ℕ} {hjr : j ≤ core.r}
    (S : WleClearedLevelExport.{uE, uG, uKt, uL} X j hjr) : Prop :=
  ∃ wC : (core.T.trunc j hjr).fld j, wC ≠ 0 ∧
    (∀ t, t < S.f' →
      (S.calculus j hjr).Rgr (S.e' * ((S.f' - t) * S.u'))
          ((S.calculus j hjr).chainNormBelow j ((S.f' - t) * S.u')) *
          (S.calculus j hjr).thetaRatioCleared (S.f' - t) = wC ^ (S.f' - t)) ∧
    ((Aℛ.node.peelUnitFamily j : Ktˣ) : Kt) = Aℛ.receiver.levelHom j wC

/-- OPEN-MATH probe: D.44's clauses outside the cleared exponent window. -/
def RangeCompleteAt
    {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {Kt : Type uKt} [Field Kt] {E : Type uE} [Field E]
    {L : Type uL} [Field L] [Algebra Kt L] {n : ℕ}
    {core : ArisingCore (O := O) Kt L n}
    {Aℛ : ChainRealization (O := O) (π := core.π) (F := core.F) (H₀ := core.H₀)
      (hpin := core.hpin) core.T Kt E L}
    (X : RealizedInput core Aℛ) (hr : 1 < core.r) {j : ℕ} {hjr : j ≤ core.r}
    (S : WleClearedLevelExport.{uE, uG, uKt, uL} X j hjr) : Prop :=
  towerReadFamily.{uE, uG, uKt, uL} X j
      ((Aℛ.normalizer.arenaNormSection0.transport
        (show GaugeLattice.{uG} core.r ≃* GaugeLattice0 core.r from
          gaugeLatticeEquiv core.r).symm).n 0) =
      ((arenaFamily.{uE, uG, uKt, uL} X hr j).theta (useHeightFamily X j) 0 : Kt) ∧
    ∀ s : ℕ, S.f' < s →
      towerReadFamily.{uE, uG, uKt, uL} X j
          ((Aℛ.normalizer.arenaNormSection0.transport
            (show GaugeLattice.{uG} core.r ≃* GaugeLattice0 core.r from
              gaugeLatticeEquiv core.r).symm).n
            ((s : ℤ) * useHeightFamily X j)) =
        ((arenaFamily.{uE, uG, uKt, uL} X hr j).theta (useHeightFamily X j) s : Kt) *
          (((Aℛ.node.peelUnitFamily j : Ktˣ) : Kt) ^ s)

/-- The intended assembly from the four genuinely distinct ingredients. -/
theorem wiredDemand_of_level_export
    {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {Kt : Type uKt} [Field Kt] {E : Type uE} [Field E]
    {L : Type uL} [Field L] [Algebra Kt L] {n : ℕ}
    {core : ArisingCore (O := O) Kt L n}
    {Aℛ : ChainRealization (O := O) (π := core.π) (F := core.F) (H₀ := core.H₀)
      (hpin := core.hpin) core.T Kt E L}
    {X : RealizedInput core Aℛ} {j : ℕ} (hj : DeepLive core.r j)
    (S : WleClearedLevelExport.{uE, uG, uKt, uL} X j hj.2.le)
    (hθ : ThetaCompatibleAt X (by rcases hj with ⟨hj3, hjr⟩; omega) S)
    (hw : PeelCompatibleAt X S)
    (hrange : RangeCompleteAt X (by rcases hj with ⟨hj3, hjr⟩; omega) S) :
    IFC3.WiredGentowDemand
      (arenaFamily.{uE, uG, uKt, uL} X
        (by rcases hj with ⟨hj3, hjr⟩; omega) j)
      (useHeightFamily X j) (towerReadFamily X j) (Aℛ.node.peelUnitFamily j)
      (S.calculus j hj.2.le) (Aℛ.receiver.levelHom j) := by
  rcases hw with ⟨wC, hwC, hlaw, hunit⟩
  have hwin : IFC1.GentowWWindow
      (arenaFamily.{uE, uG, uKt, uL} X
        (by rcases hj with ⟨hj3, hjr⟩; omega) j)
      (useHeightFamily X j) (towerReadFamily X j) (Aℛ.node.peelUnitFamily j) S.f' :=
    IFC1.gentowWWindow_of_cleared_law
      (arenaFamily.{uE, uG, uKt, uL} X
        (by rcases hj with ⟨hj3, hjr⟩; omega) j)
      (useHeightFamily X j) (towerReadFamily X j) (S.calculus j hj.2.le)
      (Aℛ.receiver.levelHom j) wC (Aℛ.node.peelUnitFamily j) hlaw hunit
      S.wiring.read_norm hθ
  refine ⟨S.wiring, ?_⟩
  exact (IFC1.gentowW_iff_zero_window_tail
    (arenaFamily.{uE, uG, uKt, uL} X
      (by rcases hj with ⟨hj3, hjr⟩; omega) j)
    (useHeightFamily X j) (towerReadFamily X j) (Aℛ.node.peelUnitFamily j) S.f').mpr
      ⟨hrange.1, hwin, hrange.2⟩

/-! The two machine pins explaining why IFC4's S2 theorem is a base/shape tooth rather
than an instance of the deep exporter above. -/

theorem no_s2_deep_level (j : ℕ) : ¬ DeepLive 2 j := by
  rintro ⟨h3, hj2⟩
  omega

theorem wleCleared_two_vacuous
    {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {π : O}
    {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀} {r : ℕ}
    {W : DeepTower.{0, uKt} F H₀ hpin r} {e' f' u' : ℕ}
    (I : ∀ i, (hi : i ≤ r) → FGMNCalculus (W.trunc i hi) e' f' u') :
    WleCleared W e' f' u' I 2 := by
  intro i hi3 hi2
  omega

end Uniformity.Density.WLEProbe
