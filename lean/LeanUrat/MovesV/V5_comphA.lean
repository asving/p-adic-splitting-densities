/-  MovesV units V5-2a `comp_h_one` — (COMP-h)'s ONE-STEP case; the marked
    (ε, γ)-event value carrier `CompCarrier` DISPLAYED.  [E-PHASE NOTE: the
    composite marked-event values ride the typed data pack `CompCarrier`
    (μhatN/ιN with their counting laws) — the entrance-extended history
    carrier is V7-4a's instance duty; MANIFEST deviations.]
    ADJUDICATED STATEMENT REPAIR 2026-07-30: `CompCarrier.μhatN` was LAWLESS
    (only `ιN_card` had landed, so the fleet could not prove
    comp_h_one/comp_h_step) — the μhatN counting law `μhatN_law` is ADDED
    per DEV D16 ("the composite marked-event VALUES ride the typed data pack
    CompCarrier (muHatN/iotaN + the |Box| normalization law)") and the
    blueprint V5-1 row (MOVESV_LEAN_BLUEPRINT_2026-07-28.md): "The (vi)
    marked event, typed: the (ε, γ, h) event's carrier is the pair (entrance
    mark family, per-mark tevt from the entrance-extended histories)" — the
    law ties μhatN to the census carrier (ιN, `ιN_card`'s object) and the
    mass carriers (the table polynomials `pathProdPoly` + the XHD-w one-step
    weights `gProd`), i.e. V5-2c's "Group the marked event by its entrance
    prefix … Per entrance mark, the continuation mass along γ at h is the
    C.1.5 conditional chain".  ALSO ADDED (adjudicated item 4, the
    comp_agg lands-leakage): `ιN_lands` — non-landing templates carry NO
    entrance mass (their instantiations' ιN vanishes identically), closing
    the leak between `aggMass`'s all-εT sum and the `entLands`-filtered
    `iotaValV`. -/
import LeanUrat.MovesV.V5_event
import LeanUrat.MovesV.V2_valB
import LeanUrat.MovesV.V1_UA

set_option linter.style.longLine false
set_option linter.style.header false

namespace LeanUrat.MovesV

/-- the stabilization level of the (ε, γ) pair (NAME→HOME: `compLvl`) —
HOISTED above `CompCarrier` (2026-07-30: the μhatN counting law reads it). -/
noncomputable def compLvl {n : ℕ} {C : CtsFamily n} {S : StepSys n}
    (V : CtsMeasured n C S) (TE : TmplEvents n S) (ε : EntShapeV n)
    {α} (γ : Template n S α) : ℕ :=
  max ((ε.template?).elim 0 V.entLvl) (TE.tmplLvl γ)

/-- the (vi) marked-event VALUE pack: level-N counting-native masses of the
(ε, γ, h) events and the entrance masses, with their counting laws
([tie]-grade, discharged at the real instance).
* `ιN_card` — the |Box|-normalization of the entrance mass (F-1's
  division-free entrance counting law, value side).
* `μhatN_law` (ADJUDICATED 2026-07-30) — THE μhatN COUNTING LAW: at
  stabilized levels the composite marked-event value factors through the
  census carrier ιN times the C.1.5 conditional chain (table polynomial ×
  fixed-height weight per step) — the blueprint V5-1 row's pair carrier
  ("entrance mark family, per-mark tevt"), value side.  Stated over every
  XHD-w face X (the weight face `w_eq` pins `gProd X` at realized points;
  the ∀-X headline shape and its off-domain scope are FLAGGED in the
  MANIFEST for the V7-4a instance-discharge pass).
* `ιN_lands` (ADJUDICATED 2026-07-30, comp_agg's lands law) — non-landing
  templates contribute 0: for εT with ¬ entLands εT β₀, every
  instantiation's entrance mass vanishes at every level (V.1(vi)'s ENT-AGG
  aggregates over the LANDING index; XHDdEnt.lands_of_realizable is the
  event-level face of the same law). -/
structure CompCarrier {n : ℕ} {C : CtsFamily n} {S : StepSys n}
    (V : CtsMeasured n C S) (TE : TmplEvents n S) where
  μhatN : ∀ (ε : EntShapeV n) (β₀ : S.Cell) {α} (γ : Template n S α),
    Hpt γ.D → ℚ → ℕ → ℝ
  ιN : EntShapeV n → S.Cell → ℚ → ℕ → ℝ
  ιN_card : ∀ (ε : EntShapeV n) (β₀ : S.Cell) (q₀ : ℚ), q₀ ∈ V.Pools →
    ∀ N ≥ (ε.template?).elim 0 V.entLvl,
    ιN ε β₀ q₀ N * ((@Fintype.card _ (V.finB q₀ N)) : ℝ)
      = ((V.entEvt ε β₀ q₀ N).card : ℝ)
  μhatN_law : ∀ (X : XHDw n S) (ε : EntShapeV n) (β₀ : S.Cell) {α}
    (γ : Template n S α) (h : Hpt γ.D) {q₀ : ℚ}, q₀ ∈ V.Pools →
    ∀ N ≥ compLvl V TE ε γ,
      μhatN ε β₀ γ h q₀ N
        = ιN ε β₀ q₀ N * (((pathProdPoly V γ).eval q₀ : ℚ) : ℝ)
            * gProd X γ h q₀
  ιN_lands : ∀ (εT : EntTemplate n) (hp : Hpt εT.entDim) (β₀ : S.Cell)
    {q₀ : ℚ}, q₀ ∈ V.Pools → ¬ V.entLands εT β₀ →
    ∀ ε ∈ writeHeights? εT hp, ∀ N, ιN ε β₀ q₀ N = 0

theorem comp_h_one {n : ℕ} {C : CtsFamily n} {S : StepSys n}
    {V : CtsMeasured n C S} {TE : TmplEvents n S}
    (cc : CompCarrier V TE) (P : C15Pack n S) (X : XHDw n S) (U : XHDu n S)
    (ε : EntShapeV n) (β₀ : S.Cell) {αc βc : S.Cell} (mv : S.Move αc βc)
    (h : Hpt (S.dim mv)) {q₀ : ℚ} (hq : q₀ ∈ V.Pools) :
    ∀ N ≥ compLvl V TE ε (.last mv),
      cc.μhatN ε β₀ (.last mv) h q₀ N
        = cc.ιN ε β₀ q₀ N * (((tblOf V mv).eval q₀ : ℚ) : ℝ) * X.g mv h q₀ := by
  intro N hN
  simpa [pathProdPoly, gProd, XHDw.g] using
    cc.μhatN_law X ε β₀ (.last mv) h hq N hN

end LeanUrat.MovesV
