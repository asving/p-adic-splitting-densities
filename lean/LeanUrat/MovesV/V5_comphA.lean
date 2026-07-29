/-  MovesV units V5-2a `comp_h_one` — (COMP-h)'s ONE-STEP case; the marked
    (ε, γ)-event value carrier `CompCarrier` DISPLAYED.  [E-PHASE NOTE: the
    composite marked-event values ride the typed data pack `CompCarrier`
    (μhatN/ιN with their counting laws) — the entrance-extended history
    carrier is V7-4a's instance duty; MANIFEST deviations.] -/
import LeanUrat.MovesV.V5_event
import LeanUrat.MovesV.V2_valB
import LeanUrat.MovesV.V1_UA

set_option linter.style.longLine false
set_option linter.style.header false

namespace LeanUrat.MovesV

/-- the (vi) marked-event VALUE pack: level-N counting-native masses of the
(ε, γ, h) events and the entrance masses, with their |Box|-normalization
laws ([tie]-grade, discharged at the real instance). -/
structure CompCarrier {n : ℕ} {C : CtsFamily n} {S : StepSys n}
    (V : CtsMeasured n C S) (TE : TmplEvents n S) where
  μhatN : ∀ (ε : EntShapeV n) (β₀ : S.Cell) {α} (γ : Template n S α),
    Hpt γ.D → ℚ → ℕ → ℝ
  ιN : EntShapeV n → S.Cell → ℚ → ℕ → ℝ
  ιN_card : ∀ (ε : EntShapeV n) (β₀ : S.Cell) (q₀ : ℚ), q₀ ∈ V.Pools →
    ∀ N ≥ (ε.template?).elim 0 V.entLvl,
    ιN ε β₀ q₀ N * ((@Fintype.card _ (V.finB q₀ N)) : ℝ)
      = ((V.entEvt ε β₀ q₀ N).card : ℝ)

/-- the stabilization level of the (ε, γ) pair (NAME→HOME: `compLvl`). -/
noncomputable def compLvl {n : ℕ} {C : CtsFamily n} {S : StepSys n}
    (V : CtsMeasured n C S) (TE : TmplEvents n S) (ε : EntShapeV n)
    {α} (γ : Template n S α) : ℕ :=
  max ((ε.template?).elim 0 V.entLvl) (TE.tmplLvl γ)

theorem comp_h_one {n : ℕ} {C : CtsFamily n} {S : StepSys n}
    {V : CtsMeasured n C S} {TE : TmplEvents n S}
    (cc : CompCarrier V TE) (P : C15Pack n S) (X : XHDw n S) (U : XHDu n S)
    (ε : EntShapeV n) (β₀ : S.Cell) {αc βc : S.Cell} (mv : S.Move αc βc)
    (h : Hpt (S.dim mv)) {q₀ : ℚ} (hq : q₀ ∈ V.Pools) :
    ∀ N ≥ compLvl V TE ε (.last mv),
      cc.μhatN ε β₀ (.last mv) h q₀ N
        = cc.ιN ε β₀ q₀ N * (((tblOf V mv).eval q₀ : ℚ) : ℝ) * X.g mv h q₀ := by
  sorry

end LeanUrat.MovesV
