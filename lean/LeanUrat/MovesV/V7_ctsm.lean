/-  MovesV unit V7-2b `ctsm_given` — THEOREM CTS-M assembled: the [1v]-COND
    capstone of this corpus (apply each cited unit; assemble). -/
import LeanUrat.MovesV.V7_ctsmDefs
import LeanUrat.MovesV.V4_act
import LeanUrat.MovesV.V3_eps
import LeanUrat.MovesV.V3_hent

set_option linter.style.longLine false
set_option linter.style.header false

namespace LeanUrat.MovesV
open LeanUrat.MovesS (evalAt)

/-- THEOREM CTS-M.  `hmark` is ADJUDICATED (ADJ-4; the wave-A2 record in
`lean/notes/LEAN_FORMALIZATION_CAMPAIGN_2026-07-28.md`: "ctsm hmark (an
emult≡0 model refutes hmark-free)"): `Part2_Stmt` is REFUTABLE without it —
in a model with `emult ≡ 0` at a continuing cell of positive mass,
`markWeight = 0` there while surplus's ℕ-subtraction truncates
((0 - 1 : ℕ) = 0), so that cell contributes 0 to markedRow AND 0 to
surplusRow and the pointwise identity markedRow + terminalRow
= 1 + surplusRow fails; no hmark-free proof exists.  It therefore rides as
a ctsM hypothesis mirroring hb/hc/hd (NOT a CtsmLedger field), consumed
exactly at the producer `part2_row` (V4-7). -/
theorem ctsM {n : ℕ} (L : CtsmLedger n)
    (hb : P1CtblAdd L.V L.X.w) (hc : P1NullRem L.V L.X.w)
    (hd : P1FixedHeightExact L.V L.X.w)
    (hmark : ∀ (τ : L.S.Cell) (c : DCellAll L.V τ),
      c.isLeft → 1 ≤ markWeight L.V c) :
    CtsmConclusions L :=
  { syntax_partition := fun s q₀ _ => meet_finite_uniform (L.C.bd s) q₀
    val_a := L.hVA
    val_b_chain := by
      intro α γ q₀ x hzc hq h hmem
      exact valB L.hVA L.X.u L.hTie γ x hzc hq h hmem
    no_entry := by
      intro d q₀ hq hne hact hin
      exact no_entry L.hVA d hq hne hact hin
    iota_supp := by
      intro β₀ q₀ hq hin
      exact iota_supp L.X.sEnt L.hVA β₀ hq hin
    active_value_recorded := id
    ent_typing :=
      ⟨fun ε ε' h => entshape_selRec_ne ε ε' h,
       fun ε ε' h he => h (by rw [he])⟩
    ent_agg_fin := by
      intro ε p F fp ff fin pol cs hd' N m Pr
      exact @ent_agg_finite n ε p F fp ff fin pol cs hd' N m Pr
    ent_agg_full := fun β₀ q₀ hq =>
      ⟨ent_agg_conv L.V L.X.sEnt L.X.dEnt β₀ q₀ hq,
       fun hEU => ent_agg_ival L.V L.X.sEnt L.X.dEnt hEU β₀ q₀ hq⟩
    ent_count_named := id
    init_rat := fun β₀ i =>
      match initRat_comp L.V L.X.sEnt L.hEU L.hEC L.hAff β₀ i with
      | ⟨P, hS, hgeom, _, hval⟩ => ⟨P, hS, hgeom, hval⟩
    part1 := by
      intro τ q₀ x hzc hq hact
      exact part1 L.X.w hb hc hd x hzc hq hact
    -- (PART-2): closed under the ADJ-4 `hmark` hypothesis (see the theorem
    -- docstring; the emult ≡ 0 refuting model kills every hmark-free route).
    part2 := by
      intro τ q₀ x hzc hq hact
      exact part2_row L.X.w hb hc hd x hzc hq hact (hmark τ)
    surplus_n3 := by
      intro hn h2 e he τ o
      subst hn
      exact surplus_zero L.T L.stage_laws.degcons_all h2 e he τ o
    -- (iv)-REP: rep_row's proof inlined — the producer (V4_rep) also binds
    -- hobs/P/U, which the ledger lacks, but its proof consumes only cp + X.dC.
    rep := by
      intro τ q₀ hq x x' hzc hzc'
      classical
      unfold measuredRow
      refine tsum_congr (fun ch => ?_)
      obtain ⟨c, D, h⟩ := ch
      cases c with
      | inl dc =>
        obtain ⟨⟨d, hd⟩, c⟩ := dc
        subst hd
        simp only [μcellH]
        split
        · next e =>
          rw [eq_of_heq (cast_heq _ x), eq_of_heq (cast_heq _ x')]
          have hcnt : L.V.cntc d x c (castHpt e h)
              = L.V.cntc d x' c (castHpt e h) := by
            by_cases hmem : (L.V.cdom d c).Mem (castHpt e h)
            · have hq1 := L.cp.count d c x hzc hq (castHpt e h) hmem
              have hq2 := L.cp.count d c x' hzc' hq (castHpt e h) hmem
              exact_mod_cast hq1.symm.trans hq2
            · have hz : L.V.cntc d x c (castHpt e h) = 0 :=
                Nat.eq_zero_of_not_pos
                  (fun hpos => hmem (L.X.dC.no_orphanC d x c _ hq hzc hpos))
              have hz' : L.V.cntc d x' c (castHpt e h) = 0 :=
                Nat.eq_zero_of_not_pos
                  (fun hpos => hmem (L.X.dC.no_orphanC d x' c _ hq hzc' hpos))
              rw [hz, hz']
          rw [hcnt]
        · rfl
      | inr vdc =>
        obtain ⟨v, ⟨d, hd⟩, c⟩ := vdc
        subst hd
        simp only [μcellH]
        split
        · next e =>
          rw [eq_of_heq (cast_heq _ x), eq_of_heq (cast_heq _ x')]
          have hcnt : L.V.cntcT d x c (castHpt e h)
              = L.V.cntcT d x' c (castHpt e h) := by
            by_cases hmem : (L.V.cdomT d c).Mem (castHpt e h)
            · have hq1 := L.cp.countT d c x hzc hq (castHpt e h) hmem
              have hq2 := L.cp.countT d c x' hzc' hq (castHpt e h) hmem
              exact_mod_cast hq1.symm.trans hq2
            · have hz : L.V.cntcT d x c (castHpt e h) = 0 :=
                Nat.eq_zero_of_not_pos
                  (fun hpos => hmem (L.X.dC.no_orphanCT d x c _ hq hzc hpos))
              have hz' : L.V.cntcT d x' c (castHpt e h) = 0 :=
                Nat.eq_zero_of_not_pos
                  (fun hpos => hmem (L.X.dC.no_orphanCT d x' c _ hq hzc' hpos))
              rw [hz, hz']
          rw [hcnt]
        · rfl
    meas :=
      ⟨fun x N mp mp' h => MarkDisj L.V mp mp' h N,
       fun x N mp mp' h => MarkDisj_pt L.V mp mp' h N,
       equalProj_instance⟩
    comp_h := by
      intro ε β₀ α γ h hmem q₀ hq
      exact comp_h L.cc L.pack L.X.w L.X.u L.hMark ε β₀ γ h hmem hq
    comp_sigma := by
      intro hHMC ε β₀ α γ q₀ hq
      exact comp_sigma L.cc L.pack L.X.w L.X.u L.X.s L.hMark hHMC ε β₀ γ hq
    -- (COMP-AGG): V5_compagg.comp_agg's proof inlined — the producer also
    -- binds hobs (∀ s, ObsCheck), which the ledger lacks, but its proof
    -- consumes only cc/X.s/X.sEnt/hEU (+ the bridge theorem, hobs-free).
    comp_agg := by
      intro _hHMC β₀ α γ q₀ hq
      classical
      letI : Finite (EntTemplate n) := template_finite n
      letI : Fintype (EntTemplate n) := Fintype.ofFinite _
      letI : Finite (L.V.EntIx β₀) := by
        unfold CtsMeasured.EntIx; exact Subtype.finite
      letI : Fintype (L.V.EntIx β₀) := Fintype.ofFinite _
      have hq1 : (1 : ℚ) < q₀ := L.S.pools_gt_one q₀ (L.V.pools_sub hq)
      have hq0 : (0 : ℝ) < (q₀ : ℝ) := by exact_mod_cast lt_trans one_pos hq1
      -- ── the (ENT-U) fiber leg: per landing (εT, j) the component sums to ιsh
      have hfiber : ∀ (εT : EntTemplate n) (hl : L.V.entLands εT β₀)
          (j : Fin (L.V.entDom εT).comps.length),
          HasSum (fun x : {h // ((L.V.entDom εT).comps.get j).Mem h} =>
              ιshH L.V εT x.1 β₀ q₀)
            (iotaShV L.V L.X.sEnt ⟨⟨εT, j⟩, hl⟩ q₀) := by
        intro εT hl j
        set i : L.V.EntIx β₀ := ⟨⟨εT, j⟩, hl⟩ with hi
        have hIC : ∀ (h : Hpt εT.entDim),
            L.V.instCensus εT h β₀ q₀
              = L.V.entCensus (writeHeights εT h) β₀ q₀ := by
          intro h
          have hsome : writeHeights? εT h = some (writeHeights εT h) :=
            (Option.some_get (writeHeights_total εT h)).symm
          unfold CtsMeasured.instCensus
          rw [hsome]
          simp
        obtain ⟨P', _, hP'⟩ := L.hEU β₀ i
        have hconst : ∀ x : {h // ((L.V.entDom εT).comps.get j).Mem h},
            (L.V.instCensus εT x.1 β₀ q₀ : ℝ) = (L.V.entCount i q₀ : ℝ) := by
          intro x
          have e1 := hP' x.1 x.2 q₀ hq
          have e2 := hP' _ (linset_base_mem ((L.V.entDom εT).comps.get j)) q₀ hq
          have hqq : (L.V.entCensus (writeHeights εT x.1) β₀ q₀ : ℚ)
              = (L.V.entCensus (writeHeights εT
                  ((L.V.entDom εT).comps.get j).base) β₀ q₀ : ℚ) :=
            e1.symm.trans e2
          rw [hIC x.1,
            show L.V.entCount i q₀
                = L.V.instCensus εT ((L.V.entDom εT).comps.get j).base β₀ q₀ from rfl,
            hIC ((L.V.entDom εT).comps.get j).base]
          exact_mod_cast hqq
        have hfun : (fun x : {h // ((L.V.entDom εT).comps.get j).Mem h} =>
              ιshH L.V εT x.1 β₀ q₀)
            = (fun x => (L.V.entCount i q₀ : ℝ)
                * (q₀ : ℝ) ^ (-((instA εT x.1 : ℕ) : ℤ))) := by
          funext x; unfold ιshH; rw [hconst x]
        have hval : iotaShV L.V L.X.sEnt i q₀
            = (L.V.entCount i q₀ : ℝ)
              * ((evalAt q₀
                  ⟨L.X.sEnt.Gent β₀ i, L.X.sEnt.Gent_ok β₀ i q₀ hq⟩ : ℚ) : ℝ) := by
          unfold iotaShV; rw [dif_pos hq]
        rw [hfun, hval]
        exact (L.X.sEnt.Gent_hasSum β₀ i q₀ hq).mul_left (L.V.entCount i q₀ : ℝ)
      -- ── the per-ε̊ inner sum: landing templates give the component ιsh sums
      --    (bridge + V0-3), non-landing templates give 0 (the ADJUDICATED law)
      have hinner : ∀ εT : EntTemplate n,
          (∑' hh : {h // (L.V.entDom εT).Mem h},
            iotaEps L.cc (writeHeights εT hh.1) β₀ q₀)
          = if hl : L.V.entLands εT β₀
            then ∑ j, iotaShV L.V L.X.sEnt ⟨⟨εT, j⟩, hl⟩ q₀ else 0 := by
        intro εT
        by_cases hl : L.V.entLands εT β₀
        · rw [dif_pos hl]
          have hbr : ∀ hh : {h // (L.V.entDom εT).Mem h},
              iotaEps L.cc (writeHeights εT hh.1) β₀ q₀
                = ιshH L.V εT hh.1 β₀ q₀ :=
            fun hh => iotaEps_iotashH_bridge L.cc εT hh.1 β₀ hq
          rw [tsum_congr hbr]
          have hng : ∀ h : Hpt εT.entDim, 0 ≤ ιshH L.V εT h β₀ q₀ := fun h =>
            mul_nonneg (Nat.cast_nonneg _) (zpow_nonneg hq0.le _)
          exact (semilin_sum_exact (L.V.entDom εT)
            (fun h => ιshH L.V εT h β₀ q₀) hng
            (fun j => iotaShV L.V L.X.sEnt ⟨⟨εT, j⟩, hl⟩ q₀)
            (fun j => hfiber εT hl j)).tsum_eq
        · rw [dif_neg hl]
          have hz : ∀ hh : {h // (L.V.entDom εT).Mem h},
              iotaEps L.cc (writeHeights εT hh.1) β₀ q₀ = 0 := by
            intro hh
            exact L.cc.ιN_lands εT hh.1 β₀ hq hl (writeHeights εT hh.1)
              (Option.get_mem (writeHeights_total εT hh.1)) _
          rw [tsum_congr hz]
          exact tsum_zero
      -- ── the finite ε̊-aggregate re-indexes to the entLands-filtered EntIx
      letI : Fintype {p : Σ εT : EntTemplate n,
          Fin (L.V.entDom εT).comps.length // L.V.entLands p.1 β₀} :=
        Fintype.ofFinite _
      have hKEY : (∑' εT : EntTemplate n, ∑' hh : {h // (L.V.entDom εT).Mem h},
          iotaEps L.cc (writeHeights εT hh.1) β₀ q₀)
            = iotaValV L.V L.X.sEnt β₀ q₀ := by
        rw [tsum_congr hinner, tsum_fintype]
        set G : (Σ εT : EntTemplate n, Fin (L.V.entDom εT).comps.length) → ℝ :=
          fun p => if hl : L.V.entLands p.1 β₀
            then iotaShV L.V L.X.sEnt ⟨p, hl⟩ q₀ else 0 with hG
        have h4 : (∑ εT : EntTemplate n, if hl : L.V.entLands εT β₀
              then ∑ j, iotaShV L.V L.X.sEnt ⟨⟨εT, j⟩, hl⟩ q₀ else 0)
            = ∑ εT : EntTemplate n, ∑ j, G ⟨εT, j⟩ := by
          refine Finset.sum_congr rfl fun εT _ => ?_
          by_cases hl : L.V.entLands εT β₀
          · rw [dif_pos hl]
            refine Finset.sum_congr rfl fun j _ => ?_
            simp only [hG]
            rw [dif_pos hl]
          · rw [dif_neg hl]
            symm
            refine Finset.sum_eq_zero fun j _ => ?_
            simp only [hG]
            rw [dif_neg hl]
        have h5 : (∑ εT : EntTemplate n, ∑ j, G ⟨εT, j⟩)
            = ∑ p : (Σ εT : EntTemplate n,
                Fin (L.V.entDom εT).comps.length), G p := by
          rw [← Finset.univ_sigma_univ, Finset.sum_sigma]
        have h6 : (∑ p : (Σ εT : EntTemplate n,
              Fin (L.V.entDom εT).comps.length), G p)
            = ∑ p ∈ Finset.univ.filter
                (fun p : (Σ εT : EntTemplate n,
                  Fin (L.V.entDom εT).comps.length) =>
                  L.V.entLands p.1 β₀), G p := by
          symm
          refine Finset.sum_filter_of_ne fun p _ hne => ?_
          by_contra hnl
          exact hne (by simp only [hG]; rw [dif_neg hnl])
        have h7 : (∑ p ∈ Finset.univ.filter
              (fun p : (Σ εT : EntTemplate n,
                Fin (L.V.entDom εT).comps.length) =>
                L.V.entLands p.1 β₀), G p)
            = ∑ i : {p : Σ εT : EntTemplate n,
                Fin (L.V.entDom εT).comps.length // L.V.entLands p.1 β₀}, G i.1 :=
          Finset.sum_subtype
            (Finset.univ.filter
              (fun p : (Σ εT : EntTemplate n,
                Fin (L.V.entDom εT).comps.length) =>
                L.V.entLands p.1 β₀))
            (fun x => by simp only [Finset.mem_filter, Finset.mem_univ, true_and])
            G
        have h8 : (∑ i : {p : Σ εT : EntTemplate n,
              Fin (L.V.entDom εT).comps.length // L.V.entLands p.1 β₀}, G i.1)
            = iotaValV L.V L.X.sEnt β₀ q₀ := by
          unfold iotaValV
          refine Finset.sum_congr rfl (fun i _ => ?_)
          simp only [hG]
          rw [dif_pos i.2]
        rw [h4, h5, h6, h7, h8]
      -- ── assemble: pull the constant continuation factor, apply the key
      have hpull : aggMass L.cc L.X.s β₀ γ q₀
          = (∑' εT : EntTemplate n, ∑' hh : {h // (L.V.entDom εT).Mem h},
              iotaEps L.cc (writeHeights εT hh.1) β₀ q₀)
            * stepProdVal L.V L.X.s γ q₀ := by
        unfold aggMass
        rw [← tsum_mul_right]
        exact tsum_congr fun εT => tsum_mul_right
      rw [hpull, hKEY]
    solve_conditional := fun _ _ _ _ _ => trivial }

end LeanUrat.MovesV
