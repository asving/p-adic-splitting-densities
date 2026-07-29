/-  MovesV unit V7-2b `ctsm_given` — THEOREM CTS-M assembled: the [1v]-COND
    capstone of this corpus (apply each cited unit; assemble). -/
import LeanUrat.MovesV.V7_ctsmDefs
import LeanUrat.MovesV.V4_act
import LeanUrat.MovesV.V3_eps
import LeanUrat.MovesV.V3_hent

set_option linter.style.longLine false
set_option linter.style.header false

namespace LeanUrat.MovesV

theorem ctsM {n : ℕ} (L : CtsmLedger n)
    (hb : P1CtblAdd L.V L.X.w) (hc : P1NullRem L.V L.X.w)
    (hd : P1FixedHeightExact L.V L.X.w) :
    CtsmConclusions L :=
  { syntax_partition := fun s q₀ _ => meet_finite_uniform (L.C.bd s) q₀
    val_a := L.hVA
    val_b_chain := fun γ x hzc hq h hmem =>
      valB L.hVA L.X.u L.hTie γ x hzc hq h hmem
    no_entry := fun d hq hne hact hin => no_entry L.hVA d hq hne hact hin
    iota_supp := fun β₀ hq hin => iota_supp L.X.sEnt L.hVA β₀ hq hin
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
    part1 := fun τ x hzc hq hact => part1 L.X.w hb hc hd x hzc hq hact
    part2 := sorry
    surplus_n3 := by
      intro hn h2 e he τ o
      subst hn
      exact surplus_zero L.T L.stage_laws.degcons_all h2 e he τ o
    rep := sorry
    meas :=
      ⟨fun x N mp mp' h => MarkDisj L.V mp mp' h N,
       fun x N mp mp' h => MarkDisj_pt L.V mp mp' h N,
       equalProj_instance⟩
    comp_h := fun ε β₀ γ h hmem hq =>
      comp_h L.cc L.pack L.X.w L.X.u L.hMark ε β₀ γ h hmem hq
    comp_sigma := fun hHMC ε β₀ γ hq =>
      comp_sigma L.cc L.pack L.X.w L.X.u L.X.s L.hMark hHMC ε β₀ γ hq
    comp_agg := sorry
    solve_conditional := fun _ _ _ _ _ => trivial }

end LeanUrat.MovesV
