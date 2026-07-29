/-  MovesV units V5-2a `comp_h_one` — (COMP-h)'s ONE-STEP case; the marked
    (ε, γ)-event value carrier `CompCarrier` DISPLAYED.  [E-PHASE NOTE: the
    composite marked-event values ride the typed data pack `CompCarrier`
    (μhatN/ιN with their counting laws) — the entrance-extended history
    carrier is V7-4a's instance duty; MANIFEST deviations.]
    M3 RETYPE (final-ratification verdict, 2026-07-29 — "COMP-h remains
    circular … the carrier field is the finite-level COMP-h conclusion
    itself"): the 2026-07-30 `μhatN_law` product FIELD is DELETED.  The
    carrier now holds MEASURE-DEFINITION laws only — `cevt` (the composite
    marked event), `μhatN_card` (μhatN := its |Box|-normalized mass), and
    `cevt_fiber` (the census groups by entrance mark with per-mark `tevt`
    fibers, the blueprint V5-1 pair carrier).  The multiplicative identity
    is the NAMED OPEN ROW `CompProduct` (derivation attempt recorded at its
    docstring; genuinely Phase-B — the tevt per-chain decomposition along
    `ext` has no corpus law), and the cross-level entrance-mass tie is the
    NAMED OPEN ROW `IotaLvlStable`.  `ιN_lands` (adjudicated 2026-07-30,
    comp_agg's lands law) is retained. -/
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
(ε, γ, h) events and the entrance masses, with their MEASURE-DEFINITION
laws ([tie]-grade, discharged at the real instance).
M3 RETYPE (final-ratification verdict, 2026-07-29: "the carrier field is
the finite-level COMP-h conclusion itself … its statement contains the
complete multiplicative identity and mentions neither `tevt`, a fiber
decomposition, nor an assignment-chain bijection" — the old `μhatN_law`
product field is DELETED; the product identity is now the NAMED OPEN ROW
`CompProduct` below, never a carrier field):
* `cevt` — the composite (ε, γ, h) MARKED EVENT at level N (the blueprint
  V5-1 pair carrier: entrance mark family + per-mark tevt continuation).
* `μhatN_card` — THE μhatN MEASURE DEFINITION: μhatN is the |Box|-normalized
  mass of `cevt` (mirrors `ιN_card`/F-1, division-free).
* `cevt_fiber` — THE MARK-FIBER LAW (mentions `tevt`): at stabilized levels
  the composite event's census GROUPS BY the entrance mark — per mark b of
  the ε-instance census there is an entrance-extended zc history x_b whose
  `TE.tevt γ x_b h N` fiber carries the mark's share (V5-2c's "Group the
  marked event by its entrance prefix").
* `ιN_card` — the |Box|-normalization of the entrance mass (F-1's
  division-free entrance counting law, value side).
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
  cevt : ∀ (ε : EntShapeV n) (β₀ : S.Cell) {α} (γ : Template n S α),
    Hpt γ.D → ∀ (q₀ : ℚ) (N : ℕ), Finset (V.Box q₀ N)
  ιN_card : ∀ (ε : EntShapeV n) (β₀ : S.Cell) (q₀ : ℚ), q₀ ∈ V.Pools →
    ∀ N ≥ (ε.template?).elim 0 V.entLvl,
    ιN ε β₀ q₀ N * ((@Fintype.card _ (V.finB q₀ N)) : ℝ)
      = ((V.entEvt ε β₀ q₀ N).card : ℝ)
  μhatN_card : ∀ (ε : EntShapeV n) (β₀ : S.Cell) {α} (γ : Template n S α)
    (h : Hpt γ.D) {q₀ : ℚ}, q₀ ∈ V.Pools → ∀ N,
    μhatN ε β₀ γ h q₀ N * ((@Fintype.card _ (V.finB q₀ N)) : ℝ)
      = ((cevt ε β₀ γ h q₀ N).card : ℝ)
  cevt_fiber : ∀ (ε : EntShapeV n) (β₀ : S.Cell) {α} (γ : Template n S α)
    (h : Hpt γ.D) {q₀ : ℚ}, q₀ ∈ V.Pools → ∀ N ≥ compLvl V TE ε γ,
    ∃ xe : {b // b ∈ V.entInst ε β₀ q₀ ((ε.template?).elim 0 V.entLvl)} →
        {x : S.Hist q₀ α // S.zc x},
      (cevt ε β₀ γ h q₀ N).card
        = ∑ b ∈ (V.entInst ε β₀ q₀ ((ε.template?).elim 0 V.entLvl)).attach,
            (TE.tevt γ (xe b).1 h N).card
  ιN_lands : ∀ (εT : EntTemplate n) (hp : Hpt εT.entDim) (β₀ : S.Cell)
    {q₀ : ℚ}, q₀ ∈ V.Pools → ¬ V.entLands εT β₀ →
    ∀ ε ∈ writeHeights? εT hp, ∀ N, ιN ε β₀ q₀ N = 0

/-- THE (COMP-h) PRODUCT ROW (M3 adjudication: a NAMED OPEN ROW, never a
carrier field): at stabilized levels the composite marked-event value
factors as ιN × (path product) × (fixed-height weight).  DERIVATION ATTEMPT
(recorded, 2026-07-29): `μhatN_card` + `cevt_fiber` reduce the claim to
valuing each entrance mark's continuation fiber `(TE.tevt γ x_b h N).card`
as `chainCount × ∏ mass × |Box|` — the per-chain decomposition of `tevt`
along `ext` (the C.1.5 conditional chain).  The corpus' tevt laws are
nonemptiness ties only (`tevt_last_iff`/`marks_realize`), and the one-step
census `evt_card` (V.evtOf) has no composite-template analogue, so the
decomposition is genuinely Phase-B: C15Pack/XHDw/XHDu value the FACTORS
(`mass_factors`/`w_eq`/`u_T`) but cannot split the composite event.  Owner:
V7-4a (the instance's cevt is BUILT as the entrance-extended biUnion, where
the split is definitional). -/
def CompProduct {n : ℕ} {C : CtsFamily n} {S : StepSys n}
    {V : CtsMeasured n C S} {TE : TmplEvents n S}
    (cc : CompCarrier V TE) (X : XHDw n S) : Prop :=
  ∀ (ε : EntShapeV n) (β₀ : S.Cell) {α} (γ : Template n S α) (h : Hpt γ.D)
    {q₀ : ℚ}, q₀ ∈ V.Pools → ∀ N ≥ compLvl V TE ε γ,
    cc.μhatN ε β₀ γ h q₀ N
      = cc.ιN ε β₀ q₀ N * (((pathProdPoly V γ).eval q₀ : ℚ) : ℝ)
          * gProd X γ h q₀

/-- THE ιN CROSS-LEVEL STABILIZATION ROW (M3: the series disconnect —
`comp_hsum`'s total reads ιN at `compLvl` while `iotaEps` reads it at the
entrance level; no theorem equated them).  A NAMED OPEN ROW: entrance
masses are level-stable at and beyond the defining level.  Owner: V7-4a
(the instance's ιN is the |Box|-normalized entEvt census, stable by
`ent_card`). -/
def IotaLvlStable {n : ℕ} {C : CtsFamily n} {S : StepSys n}
    {V : CtsMeasured n C S} {TE : TmplEvents n S}
    (cc : CompCarrier V TE) : Prop :=
  ∀ (ε : EntShapeV n) (β₀ : S.Cell) (q₀ : ℚ), q₀ ∈ V.Pools →
    ∀ N ≥ (ε.template?).elim 0 V.entLvl,
    cc.ιN ε β₀ q₀ N = cc.ιN ε β₀ q₀ ((ε.template?).elim 0 V.entLvl)

theorem comp_h_one {n : ℕ} {C : CtsFamily n} {S : StepSys n}
    {V : CtsMeasured n C S} {TE : TmplEvents n S}
    (cc : CompCarrier V TE) (P : C15Pack n S) (X : XHDw n S) (U : XHDu n S)
    (hcp : CompProduct cc X)
    (ε : EntShapeV n) (β₀ : S.Cell) {αc βc : S.Cell} (mv : S.Move αc βc)
    (h : Hpt (S.dim mv)) {q₀ : ℚ} (hq : q₀ ∈ V.Pools) :
    ∀ N ≥ compLvl V TE ε (.last mv),
      cc.μhatN ε β₀ (.last mv) h q₀ N
        = cc.ιN ε β₀ q₀ N * (((tblOf V mv).eval q₀ : ℚ) : ℝ) * X.g mv h q₀ := by
  intro N hN
  simpa [pathProdPoly, gProd, XHDw.g] using
    hcp ε β₀ (.last mv) h hq N hN

end LeanUrat.MovesV
