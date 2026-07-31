/-  TV-E6 (BRIDGE BP3, cluster c4; E-phase skeleton) — LedgerIV GROUPS
    (8)-(9) at the measuredOf witness: init_agg / init_count /
    ent_count_card / comp_once.
    Blueprint: lean/notes/BRIDGE_BP3_TV_2026-07-30.md §3.E + §4 (TV-E6).
    deps: TV-E1, TV-E2.  Consumer: TV-E7 (assembly).
    Statements = the `MovesS.LedgerIV` fields (MovesS/Defs:249-262)
    transcribed VERBATIM at M := measuredOf V X cp hfin.
    Sketch: init_agg from hEU + semilin_sum_exact + the finite EntIx
    re-index (the V5-6 comp_agg machinery, V5_compagg); init_count from
    V.ent_card (division-free form → the card form via V.box_card);
    ent_count_card rfl-genre (the V7-6a2 / V7_livA2 precedent) at the
    TV-E2 entrance-block field map; comp_once via the V7_livB
    HasSum.mul_left pattern at the ιshH weights.
    HYPOTHESIS-ROW RESOLUTION: ledgerIV_inst's own row verbatim + hfin
    (see the TV-E3 header record).  If the ιsh legs turn out to need
    AffEnt/EntDomOrder0 (the V7_rbB iota route's premises, NOT in
    ledgerIV_inst's row), that is a named-hypothesis fence event to
    surface, not to improvise. -/
import LeanUrat.MovesV.TV_E2
import LeanUrat.MovesV.V7_livC

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedVariables false
set_option linter.style.openClassical false

namespace LeanUrat.MovesV
open scoped Classical

/-- TV-E6(a) [LedgerIV group (8), init_agg]: the state entrance value is the
finite entrance-shape aggregate (verbatim `MovesS.LedgerIV.init_agg` at
measuredOf). -/
theorem measuredOf_init_agg {n : ℕ} {C : CtsFamily n} {S : StepSys n}
    (V : CtsMeasured n C S) {TE : TmplEvents n S}
    (X : XHD n S TE V) (cp : CellPolyPack n C S V) (hVA : ValA n C S V)
    (hHMC : HMC TE X.d)
    (hb : P1CtblAdd V X.w) (hc : P1NullRem V X.w)
    (hd : P1FixedHeightExact V X.w)
    (hEC : EntCount V) (hEU : EntU V) (hfin : Finite (Skeleton n)) :
    ∀ (e : ℕ) (τ : (ctsTable C hfin).State e) (q₀ : ℚ),
      q₀ ∈ (measuredOf V X cp hfin).Pools →
      (measuredOf V X cp hfin).activeState q₀ e τ →
      (measuredOf V X cp hfin).ιval e τ q₀
        = ∑ ε : (measuredOf V X cp hfin).EntShape e τ,
            (measuredOf V X cp hfin).ιsh e τ ε q₀ := by
  intro e τ q₀ hq hact
  show iotaValV V X.sEnt (V.toStepCells.symm τ.1) q₀ = _
  unfold iotaValV
  refine Finset.sum_congr ?_ (fun _ _ => rfl)
  congr 1

/-- TV-E6(b) [LedgerIV group (8), init_count]: the fixed-height entrance
weight counts its event, eventually (verbatim `MovesS.LedgerIV.init_count`
at measuredOf; V.ent_card → card form via box_card). -/
theorem measuredOf_init_count {n : ℕ} {C : CtsFamily n} {S : StepSys n}
    (V : CtsMeasured n C S) {TE : TmplEvents n S}
    (X : XHD n S TE V) (cp : CellPolyPack n C S V) (hVA : ValA n C S V)
    (hHMC : HMC TE X.d)
    (hb : P1CtblAdd V X.w) (hc : P1NullRem V X.w)
    (hd : P1FixedHeightExact V X.w)
    (hEC : EntCount V) (hEU : EntU V) (hfin : Finite (Skeleton n)) :
    ∀ (e : ℕ) (τ : (ctsTable C hfin).State e)
      (ε : (measuredOf V X cp hfin).EntShape e τ)
      (h : (measuredOf V X cp hfin).Hgt),
      h ∈ (measuredOf V X cp hfin).ιDom e τ ε →
      ∀ q₀ ∈ (measuredOf V X cp hfin).Pools,
      (measuredOf V X cp hfin).activeState q₀ e τ → ∃ N₀, ∀ N ≥ N₀,
      (measuredOf V X cp hfin).ιshH e τ ε h q₀
          * (Fintype.card ((measuredOf V X cp hfin).Box q₀ N) : ℝ)
        = (((measuredOf V X cp hfin).entEvtH e τ ε h q₀ N).card : ℝ) := by
  intro e τ ε h hdom q₀ hq hact
  obtain ⟨he, hmem⟩ := hdom
  rcases hw : writeHeights? ε.1.1 (castHpt he h.2) with _ | εs
  · -- no instantiation at this point: both sides are zero at every level
    refine ⟨0, fun N _ => ?_⟩
    show ishHOf V ε h q₀
        * ((@Fintype.card _ (V.finB q₀ N) : ℕ) : ℝ)
      = ((entEvtHOf V ε h q₀ N).card : ℝ)
    unfold ishHOf entEvtHOf
    rw [dif_pos he, dif_pos he]
    unfold ιshH CtsMeasured.instCensus
    rw [hw]
    simp
  · -- the instantiated point: V.ent_card + V.box_card
    refine ⟨(εs.template?).elim 0 V.entLvl, fun N hN => ?_⟩
    have hec := V.ent_card εs (V.toStepCells.symm τ.1) q₀ hq N hN
    have hbox := V.box_card q₀ hq N
    have hq1 : (1 : ℚ) < q₀ := S.pools_gt_one q₀ (V.pools_sub hq)
    have hq0R : (0 : ℝ) < (q₀ : ℝ) := by
      exact_mod_cast lt_trans one_pos hq1
    have hqne : (q₀ : ℝ) ≠ 0 := ne_of_gt hq0R
    show ishHOf V ε h q₀
        * ((@Fintype.card _ (V.finB q₀ N) : ℕ) : ℝ)
      = ((entEvtHOf V ε h q₀ N).card : ℝ)
    unfold ishHOf entEvtHOf
    rw [dif_pos he, dif_pos he]
    unfold ιshH CtsMeasured.instCensus instA
    rw [hw]
    simp only [Option.map_some, Option.getD_some]
    have hecR : (((V.entEvt εs (V.toStepCells.symm τ.1) q₀ N).card : ℕ) : ℝ)
          * (q₀ : ℝ) ^ ((εs.A : ℕ))
        = ((V.entCensus εs (V.toStepCells.symm τ.1) q₀ : ℕ) : ℝ)
          * (q₀ : ℝ) ^ (n * N) := by
      exact_mod_cast hec
    have hboxR : ((@Fintype.card _ (V.finB q₀ N) : ℕ) : ℝ) = (q₀ : ℝ) ^ (n * N) := by
      exact_mod_cast hbox
    rw [hboxR]
    rw [show (q₀ : ℝ) ^ (-((εs.A : ℕ) : ℤ)) = ((q₀ : ℝ) ^ ((εs.A : ℕ)))⁻¹ by
      rw [zpow_neg, zpow_natCast]]
    have hpne : ((q₀ : ℝ) ^ ((εs.A : ℕ))) ≠ 0 := pow_ne_zero _ hqne
    field_simp
    linear_combination -hecR

/-- TV-E6(c) [LedgerIV group (8), ent_count_card]: the entrance census at its
own level IS the entrance count (verbatim `MovesS.LedgerIV.ent_count_card`
at measuredOf; rfl-genre at the TV-E2 field map — the V7_livA2 precedent). -/
theorem measuredOf_ent_count_card {n : ℕ} {C : CtsFamily n} {S : StepSys n}
    (V : CtsMeasured n C S) {TE : TmplEvents n S}
    (X : XHD n S TE V) (cp : CellPolyPack n C S V) (hVA : ValA n C S V)
    (hHMC : HMC TE X.d)
    (hb : P1CtblAdd V X.w) (hc : P1NullRem V X.w)
    (hd : P1FixedHeightExact V X.w)
    (hEC : EntCount V) (hEU : EntU V) (hfin : Finite (Skeleton n)) :
    ∀ (e : ℕ) (τ : (ctsTable C hfin).State e)
      (ε : (measuredOf V X cp hfin).EntShape e τ) (q₀ : ℚ),
      q₀ ∈ (measuredOf V X cp hfin).Pools →
      (measuredOf V X cp hfin).activeState q₀ e τ →
      ((measuredOf V X cp hfin).entInst e τ ε q₀
          ((measuredOf V X cp hfin).entLvl e τ ε)).card
        = (measuredOf V X cp hfin).entCount e τ ε q₀ := by
  intro e τ ε q₀ hq hact
  show (entInstOf V ε q₀ (entLvlOf V ε)).card = V.entCount ε q₀
  unfold entInstOf entLvlOf CtsMeasured.entCount CtsMeasured.instCensus
  rcases hw : writeHeights? ε.1.1 ((V.entDom ε.1.1).comps.get ε.1.2).base
    with _ | εs
  · rfl
  · rfl

section Item11Helpers

/-- [item-11 helper] recollapsing a `castHpt`-transported Σ-point. -/
private theorem sigma_castHpt_eq {D D' : ℕ} (e : D = D') (x : Hpt D) :
    (⟨D', castHpt e x⟩ : Σ D : ℕ, Hpt D) = ⟨D, x⟩ := by
  subst e
  rw [castHpt_self]

/-- [item-11 helper] the Σ-embedding into `iDomOf` at the index's own
dimension. -/
private theorem mem_iDomOf_own_dim {n : ℕ} {C : CtsFamily n} {S : StepSys n}
    (V : CtsMeasured n C S) {β₀ : S.Cell} (i : V.EntIx β₀)
    (h : Hpt i.1.1.entDim)
    (hm : ((V.entDom i.1.1).comps.get i.1.2).Mem h) :
    (⟨i.1.1.entDim, h⟩ : Σ D : ℕ, Hpt D) ∈ iDomOf V i := by
  simp only [iDomOf, Set.mem_setOf_eq]
  exact ⟨trivial, by rw [castHpt_self]; exact hm⟩

/-- [item-11 helper] THE Σ-collapse equiv: the Σ-embedded `iDomOf` domain
(E2's `ιDom` carrier) is the component-membership subtype at the entrance
index's own dimension. -/
private def iDomEquiv {n : ℕ} {C : CtsFamily n} {S : StepSys n}
    (V : CtsMeasured n C S) {β₀ : S.Cell} (i : V.EntIx β₀) :
    {h : Hpt i.1.1.entDim // ((V.entDom i.1.1).comps.get i.1.2).Mem h}
      ≃ {p : Σ D : ℕ, Hpt D // p ∈ iDomOf V i} where
  toFun h := ⟨⟨i.1.1.entDim, h.1⟩, mem_iDomOf_own_dim V i h.1 h.2⟩
  invFun p := ⟨castHpt p.2.choose p.1.2, p.2.choose_spec⟩
  left_inv h := Subtype.ext (castHpt_self rfl h.1)
  right_inv p := Subtype.ext (sigma_castHpt_eq p.2.choose p.1.2)

private theorem iDomEquiv_apply_val {n : ℕ} {C : CtsFamily n} {S : StepSys n}
    (V : CtsMeasured n C S) {β₀ : S.Cell} (i : V.EntIx β₀)
    (h : {h : Hpt i.1.1.entDim // ((V.entDom i.1.1).comps.get i.1.2).Mem h}) :
    ((iDomEquiv V i) h).1 = ⟨i.1.1.entDim, h.1⟩ :=
  rfl

end Item11Helpers

/-- TV-E6(d) [LedgerIV group (9), comp_once]: THE one entrance height sum
(verbatim `MovesS.LedgerIV.comp_once` at measuredOf; the V7_livB
HasSum.mul_left pattern).
[PROVER RECORD, 2026-07-30 — BLOCKED, the file-header's anticipated
named-hypothesis fence event fires: comp_once at the blueprint field map IS
`ledgerIV_comp_once` (V7_livB) modulo the Σ-collapse equiv, and that
producer's own premise row carries `hdom : EntDomOrder0 V` — required to
mint the `Order0Perimeter` certificates that hEU's census-constancy clause
demands at every component point (`writeHeights` is total ONLY on the
order-0 perimeter; the unscoped form is REFUTED,
V3_spword_negWitness2).  `ledgerIV_inst`'s row has no such member, and no
in-corpus law supplies instCensus-constancy without it: init_count pins
ιshH to the PER-POINT census (V.ent_card), while comp_once + init_agg +
the FENCED ιval pin (iotaValV) jointly force the h-sum to the BASE census
— their conjunction IS the constancy.  Swapping ιshH to the entCount-based
weight relocates the same gap into init_count (the per-point event card is
census-at-h).  ESCALATION per the header: add the named warranted
hypothesis `hdom : EntDomOrder0 V` to ledgerIV_inst's row (statement
change — orchestrator ratification required; V7_rbB/V3_initrat already
carry hdom for the SAME reason on the RatBurdens side, so the row addition
is the established genre).
[QUEUE ITEM 11 EXECUTED, 2026-07-31 (Asvin sign-off; ledger
lean/notes/BRIDGE_ADJUDICATIONS_2026-07-30.md item 11): the row below
gains `hdom : EntDomOrder0 V` as escalated, and the sorry is DISCHARGED —
the proof is `ledgerIV_comp_once` (V7_livB) transported across the
Σ-collapse equiv between the Σ-embedded `iDomOf` domain and the
component-membership subtype (proof-irrelevant `castHpt` legs).] -/
theorem measuredOf_comp_once {n : ℕ} {C : CtsFamily n} {S : StepSys n}
    (V : CtsMeasured n C S) {TE : TmplEvents n S}
    (X : XHD n S TE V) (cp : CellPolyPack n C S V) (hVA : ValA n C S V)
    (hHMC : HMC TE X.d)
    (hb : P1CtblAdd V X.w) (hc : P1NullRem V X.w)
    (hd : P1FixedHeightExact V X.w)
    (hEC : EntCount V) (hEU : EntU V) (hdom : EntDomOrder0 V)
    (hfin : Finite (Skeleton n)) :
    ∀ (e : ℕ) (τ : (ctsTable C hfin).State e)
      (ε : (measuredOf V X cp hfin).EntShape e τ) (q₀ : ℚ),
      q₀ ∈ (measuredOf V X cp hfin).Pools →
      (measuredOf V X cp hfin).activeState q₀ e τ →
      HasSum (fun h : (measuredOf V X cp hfin).ιDom e τ ε =>
          (measuredOf V X cp hfin).ιshH e τ ε h q₀)
        ((measuredOf V X cp hfin).ιsh e τ ε q₀) := by
  intro e τ ε q₀ hq hact
  show HasSum (fun p : {p : Σ D : ℕ, Hpt D // p ∈ iDomOf V ε} =>
      ishHOf V ε p.1 q₀) (iotaShV V X.sEnt ε q₀)
  have base := ledgerIV_comp_once V X hdom hEU (V.toStepCells.symm τ.1) ε
    (show q₀ ∈ V.Pools from hq)
  refine ((iDomEquiv V ε).hasSum_iff).mp ?_
  show HasSum (fun h => ishHOf V ε ((iDomEquiv V ε) h).1 q₀)
    (iotaShV V X.sEnt ε q₀)
  have hfun : (fun h : {h : Hpt ε.1.1.entDim //
        ((V.entDom ε.1.1).comps.get ε.1.2).Mem h} =>
        ishHOf V ε ((iDomEquiv V ε) h).1 q₀)
      = fun h => ιshH V ε.1.1 h.1 (V.toStepCells.symm τ.1) q₀ := by
    funext h
    rw [iDomEquiv_apply_val]
    unfold ishHOf
    rw [dif_pos rfl, castHpt_self]
  rw [hfun]
  exact base

end LeanUrat.MovesV
