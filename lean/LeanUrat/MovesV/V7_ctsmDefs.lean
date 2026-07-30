/-  MovesV unit V7-2a `ctsm_conclusions_decl` (SPLIT Codex-19; CLOSED
    Codex-18/C22) — `CtsmConclusions`: one field per ledgered deliverable,
    each a named `*_Stmt` def = the VERBATIM ∀-closure of the named unit's
    displayed conclusion.  [E-PHASE FORM: the fields whose NAME→HOME objects
    ride the V7-4 instance (Tri/StepRow/Part1/Part2/Rep/CompH/CountShadow/
    SolveCond legs) are transcribed at the built unit-level objects
    (μcellH/markedRow/measuredRow/CompCarrier/stepProdVal); MANIFEST
    deviations record the per-field transcription base.] -/
import LeanUrat.MovesV.V7_ledger
import LeanUrat.MovesV.V2_meet
import LeanUrat.MovesV.V2_valB
import LeanUrat.MovesV.V4_part2
import LeanUrat.MovesV.V4_rep
import LeanUrat.MovesV.V4_meas
import LeanUrat.MovesV.V5_compagg
import LeanUrat.MovesV.V3_aggfin
import LeanUrat.MovesV.V3_initrat
import LeanUrat.MovesV.V4_n3surplus

set_option linter.style.longLine false
set_option linter.style.header false

namespace LeanUrat.MovesV
open LeanUrat.MovesS (OKat evalAt)

variable {n : ℕ}

def Part_Stmt (L : CtsmLedger n) : Prop :=
  ∀ (s : Skeleton n) (q₀ : ℚ), IsPP q₀ →
    (∀ x : (L.C.bd s).Carrier q₀,
      ∃! a : ∀ g : (L.C.bd s).Gen, ((L.C.bd s).gen g).idx,
        ∀ g, ((L.C.bd s).gen g).part q₀ x = a g) ∧
    Finite (∀ g : (L.C.bd s).Gen, ((L.C.bd s).gen g).idx)

def ValA_Stmt (L : CtsmLedger n) : Prop := ValA n L.C L.S L.V

/-- (VAL-b), M2 RE-KEY (round-4 ratification verdict, 2026-07-29 — "CTS-M
still exports only table-side `chainCount`"): the capstone row is now the
note's REALIZED linked count — `Tgam`-keyed — discharged through the
ledger's `hRC : RealizationComplete` field (`val_b`, V2-5); the
`chainCount` product (`val_b_table`) is DEMOTED to the internal table-side
lemma. -/
def ValB_Stmt (L : CtsmLedger n) : Prop :=
  ∀ {α} (γ : Template n L.S α) {q₀} (x : L.S.Hist q₀ α),
    L.S.zc x → q₀ ∈ L.V.Pools → ∀ h : Hpt γ.D, (L.D.dom γ).Mem h →
    (Tgam L.TE γ x h : ℚ) = (pathProdPoly L.V γ).eval q₀

def NoEntry_Stmt (L : CtsmLedger n) : Prop :=
  ∀ (d : MoveData n L.C) {q₀ : ℚ}, q₀ ∈ L.V.Pools →
    (L.V.mdom d).comps ≠ [] →
    L.V.activeState q₀ (L.V.toStepCells.symm d.src) →
    ¬ L.V.activeState q₀ (L.V.toStepCells.symm d.tgt) →
    ((L.C.T d.s d.m d.o d.α d.tix).eval q₀ : ℚ) = 0

def IotaSupp_Stmt (L : CtsmLedger n) : Prop :=
  ∀ (β₀ : L.S.Cell) {q₀ : ℚ}, q₀ ∈ L.V.Pools →
    ¬ L.V.activeState q₀ β₀ → iotaValV L.V L.X.sEnt β₀ q₀ = 0

def AVRec_Stmt (L : CtsmLedger n) : Prop :=
  ActiveValueAgree L.T L.M L.RB L.hK

def EntTyping_Stmt (L : CtsmLedger n) : Prop :=
  (∀ ε ε' : EntShapeV n, ε.selRec ≠ ε'.selRec → ε ≠ ε') ∧
  (∀ ε ε' : EntShapeV n, ε.hent ≠ ε'.hent → ε ≠ ε')

def EntAggFin_Stmt (L : CtsmLedger n) : Prop :=
  ∀ (ε : EntShapeV n) {p : ℕ} {F : Type} (_ : Fact p.Prime) (_ : Field F)
    (_ : Finite F), ∀ {pol : MovesD.CanonPolicy p F}
    (cs : List (EntranceCut n ε p F pol)), CutsDisj cs →
    ∀ {N m : ℕ} (Pr : MovesD.Presented p F n N m pol ε.Phat),
    iotaCount ε (unionCut cs) Pr = (cs.map (fun c => iotaCount ε c Pr)).sum

def EntCountNamed_Stmt (L : CtsmLedger n) : Prop := EntCount L.V

def EntAggFull_Stmt (L : CtsmLedger n) : Prop :=
  ∀ (β₀ : L.S.Cell) {q₀ : ℚ}, q₀ ∈ L.V.Pools →
    (∃ v : ℝ, HasSum (fun p : Σ i : L.V.EntIx β₀,
        {h // ((L.V.entDom i.1.1).comps.get i.1.2).Mem h} =>
      ιshH L.V p.1.1.1 p.2.1 β₀ q₀) v) ∧
    (EntU L.V → HasSum (fun p : Σ i : L.V.EntIx β₀,
        {h // ((L.V.entDom i.1.1).comps.get i.1.2).Mem h} =>
      ιshH L.V p.1.1.1 p.2.1 β₀ q₀) (iotaValV L.V L.X.sEnt β₀ q₀))

def InitRat_Stmt (L : CtsmLedger n) : Prop :=
  ∀ (β₀ : L.S.Cell) (i : L.V.EntIx β₀),
    ∃ P : MovesS.PolyGeom, P.countS = 1 ∧ P.geom = L.X.sEnt.Gent β₀ i ∧
      ∀ q₀ (hq : q₀ ∈ L.V.Pools), ∃ hok : P.val ∈ OKat q₀,
        ((evalAt q₀ ⟨P.val, hok⟩ : ℚ) : ℝ) = iotaShV L.V L.X.sEnt i q₀

def Part1_Stmt (L : CtsmLedger n) : Prop :=
  ∀ (τ : L.S.Cell) {q₀ : ℚ} (x : L.S.Hist q₀ τ), L.S.zc x →
    q₀ ∈ L.V.Pools → L.V.activeState q₀ τ →
    HasSum (fun ch : Σ c : DCellAll L.V τ, Σ D : ℕ, Hpt D =>
      μcellH L.V L.X.w x ch.1 ch.2) 1

def Part2_Stmt (L : CtsmLedger n) : Prop :=
  ∀ (τ : L.S.Cell) {q₀ : ℚ} (x : L.S.Hist q₀ τ), L.S.zc x →
    q₀ ∈ L.V.Pools → L.V.activeState q₀ τ →
    markedRow L.V L.X.w x + terminalRow L.V L.X.w x
      = 1 + surplusRow L.V L.X.w x

def SurplusN3_Stmt (L : CtsmLedger n) : Prop :=
  ∀ hn : n = 3, ContTwo L.T → ∀ e ∈ Finset.Icc 1 n, ∀ (τ : L.T.State e)
    (o : L.T.Out e τ),
    ((L.T.odata e τ o).mem.filter (fun μ => μ.status.isRight)).length ≤ 1

def Rep_Stmt (L : CtsmLedger n) : Prop :=
  ∀ (τ : L.S.Cell) {q₀ : ℚ}, q₀ ∈ L.V.Pools →
    ∀ (x x' : L.S.Hist q₀ τ), L.S.zc x → L.S.zc x' →
    measuredRow L.V L.X.w x = measuredRow L.V L.X.w x'

def Meas_Stmt (L : CtsmLedger n) : Prop :=
  (∀ {αc : L.S.Cell} {q₀ : ℚ} (x : L.S.Hist q₀ αc) (N : ℕ)
    (mp mp' : MStep L.V αc x), L.V.mReading mp ≠ L.V.mReading mp' →
    Disjoint (L.V.mEvt mp N) (L.V.mEvt mp' N)) ∧
  (∀ {αc : L.S.Cell} {q₀ : ℚ} (x : L.S.Hist q₀ αc) (N : ℕ)
    (mp mp' : MStep L.V αc x), mp ≠ mp' →
    Disjoint (L.V.mEvt mp N) (L.V.mEvt mp' N)) ∧
  EqualProjInstance

def CompH_Stmt (L : CtsmLedger n) : Prop :=
  ∀ (ε : EntShapeV n) (β₀ : L.S.Cell) {α} (γ : Template n L.S α)
    (h : Hpt γ.D), (L.D.dom γ).Mem h → ∀ {q₀ : ℚ}, q₀ ∈ L.V.Pools →
    ∀ N ≥ compLvl L.V L.TE ε γ,
    L.cc.μhatN ε β₀ γ h q₀ N
      = L.cc.ιN ε β₀ q₀ N * (((pathProdPoly L.V γ).eval q₀ : ℚ) : ℝ)
          * gProd L.X.w γ h q₀

/-- (COMP-Σ), M3-REPAIRED (final-ratification verdict 2026-07-29): the
algebraic collapse AND the note's MARKED-EVENT HasSum identity — the
stabilized marked-event values sum over H(γ) to ι_ε × the stepwise
product (`comp_sigma_hasSum`, V5_compsig). -/
def CompSigma_Stmt (L : CtsmLedger n) : Prop :=
  HMC L.TE L.D → ∀ (ε : EntShapeV n) (β₀ : L.S.Cell) {α}
    (γ : Template n L.S α) {q₀ : ℚ}, q₀ ∈ L.V.Pools →
    (iotaEps L.cc ε β₀ q₀ * (((pathProdPoly L.V γ).eval q₀ : ℚ) : ℝ)
        * gcVal L.X.s γ q₀
      = iotaEps L.cc ε β₀ q₀ * stepProdVal L.V L.X.s γ q₀) ∧
    HasSum (fun h : {h // (L.D.dom γ).Mem h} => μhatVal L.cc ε β₀ γ h.1 q₀)
      (iotaEps L.cc ε β₀ q₀ * stepProdVal L.V L.X.s γ q₀)

def CompAgg_Stmt (L : CtsmLedger n) : Prop :=
  HMC L.TE L.D → ∀ hdom : EntDomOrder0 L.V,
    ∀ (β₀ : L.S.Cell) {α} (γ : Template n L.S α) {q₀ : ℚ},
    q₀ ∈ L.V.Pools →
    aggMass L.cc L.X.s hdom β₀ γ q₀
      = iotaValV L.V L.X.sEnt β₀ q₀ * stepProdVal L.V L.X.s γ q₀

/-- the [3]-owned ESCAPE(E0) premise, ledger-typed (blueprint V7-2a
NAME→HOME: "the [3]-owned ESCAPE(E0) premise … a def whose body cites the
named MovesS object"): at every pool a per-block `MovesS.PoolHyp` package
exists — its `e0` field IS `MovesS.EscapeE0` at the evaluated active
kernel. -/
def EscapeE0Rec (L : CtsmLedger n) : Prop :=
  ∀ (e : ℕ) (he : e ∈ Finset.Icc 1 n) (q₀ : ℚ), q₀ ∈ L.M.Pools →
    Nonempty (MovesS.PoolHyp L.T L.M L.RB e (L.hK e he) q₀)

/-- the ρ(A) < 1-at-pools / Neumann-convergence conclusion, ledger-typed
(blueprint V7-2a NAME→HOME; the named MovesS objects are
`MovesS.pow_entry_tendsto` / `MovesS.e0_inv_nonneg`, U-23c/U-23d — "the
Neumann series converges, and (I − A(q₀))⁻¹ ≥ 0"): at every pool package
the active-kernel powers vanish entrywise and the Neumann inverse is
entrywise nonnegative. -/
def NeumannRec (L : CtsmLedger n) : Prop :=
  ∀ (e : ℕ) (he : e ∈ Finset.Icc 1 n) (q₀ : ℚ), q₀ ∈ L.M.Pools →
    ∀ (P : MovesS.PoolHyp L.T L.M L.RB e (L.hK e he) q₀) (i j : P.Act),
      Filter.Tendsto (fun k => (P.A ^ k) i j) Filter.atTop (nhds 0)
      ∧ 0 ≤ (1 - P.A)⁻¹ i j

/-- M3 STATEMENT REPAIR (ratification verdict, 2026-07-29): the E-phase
`→ True` conclusion (discharged by `trivial`, proving none of the note's
solve content) is REPLACED by the blueprint V7-2a display — the (vi) solve
sentence: GIVEN ESCAPE(E0), (ii-c) active-value agreement, HMC, ENT-COUNT
and INIT-RAT, the frozen determinant hypothesis `MovesS.DetHyp` holds and
the Neumann conclusion follows.  The factored solve is HMC-conditional
(MOVES 8005 + 8222–8224); the (RB, hK) quantifiers are the ledger's OWN
`L.RB`/`L.hK`, never a ∀-closure.  Consumed by `ctsM` as an explicit
hypothesis (the honest perimeter cost — a sorried universal here could be
FALSE for adversarial ledgers, the exact M1 failure mode). -/
def SolveCond_Stmt (L : CtsmLedger n) : Prop :=
  EscapeE0Rec L → ActiveValueAgree L.T L.M L.RB L.hK → HMC L.TE L.D →
  EntCount L.V → InitRat_Stmt L →
  MovesS.DetHyp L.T L.RB L.hK ∧ NeumannRec L

/-- the conclusions record — (v) has NO field (the kernel stays a LEDGER
line; every consumer above takes HMC as an antecedent). -/
structure CtsmConclusions (L : CtsmLedger n) : Prop where
  syntax_partition : Part_Stmt L
  val_a : ValA_Stmt L
  val_b_chain : ValB_Stmt L
  no_entry : NoEntry_Stmt L
  iota_supp : IotaSupp_Stmt L
  /-- VACUITY DISCLOSURE (2026-07-30 verify-2 fold-in): this field is a
  P → P TAUTOLOGY — `AVRec_Stmt L → AVRec_Stmt L`, discharged by `id` in
  `ctsM` (V7_ctsm.lean) — and carries NO content.  The blueprint
  (MOVESV_LEAN_BLUEPRINT_2026-07-28.md V7-2a display) shows the bare Prop
  `AVRec_Stmt L` ("the (ii-c) Prop CARRIED, never concluded"); the P → P
  retype is a transcription deviation now recorded as MANIFEST D27.  What
  this field certifies: nothing — ActiveValueAgree survives in `ctsM` only
  as an antecedent inside `SolveCond_Stmt`, never as a carried conclusion.
  Retype-to-bare-Prop or deletion is queued for sign-off
  (GOLF_CAMPAIGN_2026-07-30.md SIGN-OFF QUEUE). -/
  active_value_recorded : AVRec_Stmt L → AVRec_Stmt L
  ent_typing : EntTyping_Stmt L
  ent_agg_fin : EntAggFin_Stmt L
  ent_agg_full : EntAggFull_Stmt L
  /-- VACUITY DISCLOSURE (2026-07-30 verify-2 fold-in): P → P TAUTOLOGY —
  `EntCountNamed_Stmt L → EntCountNamed_Stmt L`, discharged by `id` in
  `ctsM` (V7_ctsm.lean); carries NO content.  The blueprint V7-2a display
  shows the bare carried Prop.  EntCount itself does survive as the
  ledger field `L.hEC` (and as a `SolveCond_Stmt` antecedent), but THIS
  field certifies nothing.  Retype-to-bare-Prop or deletion is queued for
  sign-off (GOLF_CAMPAIGN_2026-07-30.md SIGN-OFF QUEUE); deviation
  recorded as MANIFEST D27. -/
  ent_count_named : EntCountNamed_Stmt L → EntCountNamed_Stmt L
  init_rat : InitRat_Stmt L
  part1 : Part1_Stmt L
  part2 : Part2_Stmt L
  surplus_n3 : SurplusN3_Stmt L
  rep : Rep_Stmt L
  meas : Meas_Stmt L
  comp_h : CompH_Stmt L
  comp_sigma : CompSigma_Stmt L
  comp_agg : CompAgg_Stmt L
  solve_conditional : SolveCond_Stmt L

end LeanUrat.MovesV
