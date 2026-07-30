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
exactly at the producer `part2_row` (V4-7).
M1/M3 SOUNDNESS REPAIR (ratification verdict, 2026-07-29): `hdom` is the
threaded order-0 perimeter family (`EntDomOrder0` — the false totality shim
is deleted; every `writeHeights` consumer demands the perimeter
certificate), and `hsolve` is the restated (vi) solve sentence (the E-phase
`→ True` escape is gone) — both ride as explicit ctsM hypotheses mirroring
hmark; statements gaining hypotheses is the honest cost.
M3 RETYPE (final-ratification verdict, 2026-07-29): the COMP-h product no
longer rides inside the carrier (`CompCarrier.μhatN_law` DELETED — the
carrier keeps only the measure-definition laws cevt/μhatN_card/cevt_fiber);
the product is the explicit NAMED OPEN ROW `hcomp : CompProduct` and the
cross-level entrance-mass tie is `hstab : IotaLvlStable`, both ctsM
hypotheses mirroring hsolve; COMP-Σ now ALSO concludes the marked-event
HasSum (`comp_sigma_hasSum`).
M2 RE-KEY (round-4 ratification verdict, 2026-07-29): `val_b_chain` now
discharges the Tgam-keyed `ValB_Stmt` (the note's realized linked count)
via `val_b` through the ledger's `hRC : RealizationComplete` field —
CTS-M's exported VAL(b) is no longer the table-side `chainCount` product;
`val_b_table` is the internal lemma. -/
theorem ctsM {n : ℕ} (L : CtsmLedger n)
    (hb : P1CtblAdd L.V L.X.w) (hc : P1NullRem L.V L.X.w)
    (hd : P1FixedHeightExact L.V L.X.w)
    (hmark : ∀ (τ : L.S.Cell) (c : DCellAll L.V τ),
      c.isLeft → 1 ≤ markWeight L.V c)
    (hdom : EntDomOrder0 L.V)
    (hcomp : CompProduct L.cc L.X.w)
    (hstab : IotaLvlStable L.cc)
    (hsolve : SolveCond_Stmt L) :
    CtsmConclusions L :=
  { syntax_partition := fun s q₀ _ => meet_finite_uniform (L.C.bd s) q₀
    val_a := L.hVA
    val_b_chain := by
      intro α γ q₀ x hzc hq h hmem
      exact val_b L.hVA L.X.u L.hTie L.hRC γ x hzc hq h hmem
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
       fun hEU => ent_agg_ival L.V L.X.sEnt L.X.dEnt hdom hEU β₀ q₀ hq⟩
    ent_count_named := id
    init_rat := fun β₀ i =>
      match initRat_comp L.V L.X.sEnt L.hEU L.hEC L.hAff hdom β₀ i with
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
    -- (iv)-REP: the producer rep_row (V4-9), hypothesis-trimmed at golf
    -- 2026-07-30 — its live premises are exactly the ledger's cp + X.dC.
    rep := by
      intro τ q₀ hq x x' hzc hzc'
      exact rep_row L.X.w L.cp L.X.dC hq x x' hzc hzc'
    meas :=
      ⟨fun x N mp mp' h => MarkDisj L.V mp mp' h N,
       fun x N mp mp' h => MarkDisj_pt L.V mp mp' h N,
       equalProj_instance⟩
    comp_h := by
      intro ε β₀ α γ h hmem q₀ hq
      exact comp_h L.cc L.pack L.X.w L.X.u hcomp L.hMark ε β₀ γ h hmem hq
    comp_sigma := by
      intro hHMC ε β₀ α γ q₀ hq
      exact ⟨comp_sigma L.cc L.pack L.X.w L.X.u L.X.s L.hMark hHMC ε β₀ γ hq,
        comp_sigma_hasSum L.cc L.pack L.X.w L.X.u hcomp hstab L.X.s L.hMark
          hHMC ε β₀ γ hq⟩
    -- (COMP-AGG): the producer V5_compagg.comp_agg (V5-6), hypothesis-trimmed
    -- at golf 2026-07-30 — its live premises are the ledger's
    -- cc/X.w/X.s/X.sEnt/hEU + the clause's threaded hdomS (the HMC antecedent
    -- stays unused, as in the producer).
    comp_agg := by
      intro _hHMC hdomS β₀ α γ q₀ hq
      exact comp_agg L.cc L.X.w L.X.s L.X.sEnt hdomS L.hEU β₀ γ hq
    -- (vi) the solve sentence: restated with the note's actual conclusion
    -- (M3 repair) and supplied as the explicit `hsolve` hypothesis.
    solve_conditional := hsolve }

end LeanUrat.MovesV
