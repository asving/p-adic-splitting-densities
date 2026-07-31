/-  TV-E5a (BRIDGE BP3, cluster c4; E-phase skeleton) — THE no_entry/rowVal
    VOCABULARY-BRIDGE PROBE GATE (runs BEFORE the TV-E5b prover).
    Blueprint: lean/notes/BRIDGE_BP3_TV_2026-07-30.md §3.E + §4 (TV-E5a);
    [REV 2, finding 10 — NEW probe gate]; risk R5.
    deps: TV-E1, TV-E2, TV-F1 (cp packs — the F1 pack layer is the
    vocabulary the bridge crosses; the statement below needs only cp).
    Consumer: TV-E5b (act_target).
    THE PROBE'S CHARGE (blueprint, verbatim): "state (as a standalone lemma
    attempt, no LedgerIV assembly) the bridge `Σ_{o targeting β, kcol}
    (μcell-sum rowVal) = (the no_entry T-poly evaluation)` at inactive β,
    via cp's count laws + rep_indep, and either PROVE it or record the
    exact vocabulary gap (which cp law is missing, at which route case)."
    E-PHASE RESOLUTION (recorded): at inactive β the RHS T-poly evaluations
    vanish by `no_entry` (V4_act:11 — ValA.tbl_count + ValA.tgt_supported),
    so the bridge's Lean face is the VANISHING of the β-targeting rowVal
    sum — exactly what act_target's discharge consumes; the intermediate
    "rowVal = count-poly × geometry" identification is the proof route
    (μcellH = cntc·q₀^(−E) pointwise; cp.count reads cntc as cp.P eval;
    tgt_supported kills the counts at an inactive target), not a separate
    typed claim.  GUARDS (recorded): source-activity (hact) IS carried —
    it is no_entry's own guard AND the guard kstep_one supplies in the
    guarded-kstep fallback; the bridge stated here is the COMMON content
    both kstep definitions need (finding 4: the fallback relocates, never
    avoids, this bridge).  The inactive-SOURCE case of act_target is NOT
    probed here — it is the residual the E5b prover resolves via the
    kstep-1 co-design pin (TV-E2), escalating per R5 if neither definition
    closes.  no_entry's `hne : (V.mdom d).comps ≠ []` premise is NOT
    pre-added: if the probe needs it, THAT is a recordable vocabulary gap
    (named-hypothesis escalation, never a silent statement weakening). -/
import LeanUrat.MovesV.TV_E2
import LeanUrat.MovesV.TV_F1
import LeanUrat.MovesV.V7_livC

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedVariables false
set_option linter.style.openClassical false

namespace LeanUrat.MovesV
open scoped Classical

/-- [E5a helper] the selected-member/target-cell tie at a SINGLETON roster
(the kcol case): `memberTgtCell` at the unique member IS `tcell` — via
`tcellM_sel` + the Fin-1 position collapse + proof irrelevance. -/
private theorem memberTgtCell_eq_tcell {n : ℕ} (C : CtsFamily n)
    {s : Skeleton n} {m : (C.bd s).Letter} {o : (C.bd s).Outc m}
    (α : (C.bd s).CellIdx) (mu : OMember n)
    (hmem : mu ∈ (C.bd s).omem m o) (hc : (C.bd s).cont m o)
    (hlen : ((C.bd s).omem m o).length = 1)
    (hs : mu.status = Sum.inr ((C.bd s).tgtSk m o hc)) :
    memberTgtCell C α mu hmem hs = C.tcell s m o hc α := by
  obtain ⟨i, hs', htc⟩ := C.tcellM_sel s m o hc
  have key : ∀ (j : Fin ((C.bd s).omem m o).length)
      (pf : (((C.bd s).omem m o).get j).status
        = Sum.inr ((C.bd s).tgtSk m o hc)),
      C.tcellM s m o j _ pf α = C.tcell s m o hc α := by
    intro j pf
    have hji : j = i := by
      apply Fin.ext
      have h1 := j.isLt
      have h2 := i.isLt
      omega
    subst hji
    exact congrFun htc α
  exact key _ _

/-- [E5a helper] every member of a length-1 list equals every other. -/
private theorem mem_singleton_eq {α : Type*} {l : List α}
    (hlen : l.length = 1) {a b : α} (ha : a ∈ l) (hb : b ∈ l) : a = b := by
  obtain ⟨x, rfl⟩ := List.length_eq_one_iff.mp hlen
  rw [List.eq_of_mem_singleton ha, List.eq_of_mem_singleton hb]

/-- TV-E5a [the bridge probe]: at a pool point with ACTIVE source τ and
INACTIVE target β (V-side activity, standalone — no dependence on the E2
activity pin), the β-targeting kcol rowVal sum vanishes.  PROBE DISCIPLINE:
prove OR record the exact vocabulary gap; if the gap survives both kstep
readings, TV-E5b escalates (named hypothesis on ledgerIV_inst, risk R5) —
never weaken LedgerIV. -/
theorem measuredOf_act_bridge {n : ℕ} {C : CtsFamily n} {S : StepSys n}
    (V : CtsMeasured n C S) {TE : TmplEvents n S}
    (X : XHD n S TE V) (cp : CellPolyPack n C S V) (hVA : ValA n C S V)
    (hfin : Finite (Skeleton n)) :
    ∀ (e : ℕ) (τ β : (ctsTable C hfin).State e) (q₀ : ℚ),
      q₀ ∈ V.Pools →
      V.activeState q₀ (V.toStepCells.symm τ.1) →
      ¬ V.activeState q₀ (V.toStepCells.symm β.1) →
      ∑ o ∈ {o : (ctsTable C hfin).Out e τ |
            MovesS.routeOf ((ctsTable C hfin).odata e τ o) = .kcol ∧
            ∃ μ ∈ ((ctsTable C hfin).odata e τ o).mem,
              ∃ h : μ.size = e, h ▸ μ.status = Sum.inr β
          }.toFinset,
          (measuredOf V X cp hfin).rowVal e τ o q₀ = 0 := by
  intro e τ β q₀ hq hact hin
  refine Finset.sum_eq_zero (fun o ho => ?_)
  rw [Set.mem_toFinset] at ho
  obtain ⟨hroute, μt, hμmem, hsz, hstat⟩ := ho
  -- (1) the member behind μt (before any size subst: β's type rides e)
  obtain ⟨xat, hxat, hfx⟩ := List.mem_map.mp hμmem
  subst hfx
  obtain ⟨mu, hmu⟩ := xat
  have hsz' : mu.size = e := hsz
  subst hsz'
  have hstat' : ((⟨mu.size, mu.δ,
        match hs : mu.status with
        | Sum.inl v => Sum.inl v
        | Sum.inr sk => Sum.inr
            ⟨⟨sk, memberTgtCell C τ.1.2 mu hmu hs⟩,
              (C.bd τ.1.1).omem_size o.1 o.2 mu hmu sk hs⟩⟩ :
        MovesS.Member (VLabel n) (StateOf n C)).status) = Sum.inr β := hstat
  -- (2) the kcol route pins the SINGLETON roster
  unfold MovesS.routeOf at hroute
  split_ifs at hroute with h1 h2
  have homlen : ((C.bd τ.1.1).omem o.1 o.2).length = 1 := by
    have hmlen : ((ctsTable C hfin).odata mu.size τ o).mem.length = 1 := h2
    have hml : ((ctsTable C hfin).odata mu.size τ o).mem.length
        = ((C.bd τ.1.1).omem o.1 o.2).length := by
      show ((((C.bd τ.1.1).omem o.1 o.2).attach.map _)).length = _
      rw [List.length_map, List.length_attach]
    omega
  -- (3) the β identification through the status match
  split at hstat'
  · exact absurd hstat' (by simp)

  next sk heq =>
    have hβ := Sum.inr.inj hstat'
    -- (3) continuing + the selected-target tie
    have hcont : (C.bd τ.1.1).cont o.1 o.2 :=
      ((C.bd τ.1.1).cont_iff o.1 o.2).mpr ⟨mu, hmu, by rw [heq]; rfl⟩
    have hsk : sk = (C.bd τ.1.1).tgtSk o.1 o.2 hcont := by
      obtain ⟨mu', hmu', hmust⟩ := (C.bd τ.1.1).omem_sel o.1 o.2 hcont
      have hxm : mu = mu' := mem_singleton_eq homlen hmu hmu'
      rw [← hxm] at hmust
      exact Sum.inr.inj (heq.symm.trans hmust)
    subst hsk
    have hmtc : memberTgtCell C τ.1.2 mu hmu heq
        = C.tcell τ.1.1 o.1 o.2 hcont τ.1.2 :=
      memberTgtCell_eq_tcell C τ.1.2 mu hmu hcont homlen heq
    -- (4) the target-state inactivity transported to the datum's target
    have htgt : (MoveData.tgt ⟨τ.1.1, o.1, o.2, hcont, τ.1.2⟩ : Σ s, (C.bd s).CellIdx)
        = β.1 := by
      rw [← hβ]
      show (⟨(C.bd τ.1.1).tgtSk o.1 o.2 hcont,
          C.tcell τ.1.1 o.1 o.2 hcont τ.1.2⟩ : Σ s, (C.bd s).CellIdx) = _
      rw [hmtc]
    have hintgt : ¬ V.activeState q₀
        (V.toStepCells.symm (MoveData.tgt ⟨τ.1.1, o.1, o.2, hcont, τ.1.2⟩)) := by
      rw [htgt]; exact hin
    -- (5) the vanishing of every cell mass over o
    refine Finset.sum_eq_zero (fun c hcmem => ?_)
    rw [Set.mem_toFinset] at hcmem
    obtain ⟨oc, cc⟩ := c
    have hco : oc = o := hcmem
    subst hco
    show μcellOf V X.w cp hfin τ ⟨oc, cc⟩ q₀ = 0
    unfold μcellOf
    rw [dif_pos hq]
    have hkey : toCellAll V hfin τ ⟨oc, cc⟩
        = Sum.inl ⟨⟨⟨τ.1.1, oc.1, oc.2, hcont, τ.1.2⟩, rfl⟩, cc⟩ := by
      unfold toCellAll
      rw [dif_pos hcont]
    have hzero : ∀ h : {h : Σ D : ℕ, Hpt D //
        h ∈ hdomOf V hfin τ ⟨oc, cc⟩},
        gwtAll V X.w cp (toCellAll V hfin τ ⟨oc, cc⟩) h.1 q₀ = 0 := by
      rintro ⟨⟨D, hh⟩, hd⟩
      have hd' : cdomAllMem V (toCellAll V hfin τ ⟨oc, cc⟩) ⟨D, hh⟩ := hd
      rw [hkey] at hd'
      obtain ⟨e', hmm'⟩ := hd'
      rw [hkey]
      simp only [gwtAll, dif_pos e']
      obtain ⟨x0, hzc0⟩ := S.zc_ne q₀ (V.pools_sub hq)
        (V.toStepCells.symm (MoveData.src ⟨τ.1.1, oc.1, oc.2, hcont, τ.1.2⟩))
      have hcnt0 : S.cntraw (V.moveOf ⟨τ.1.1, oc.1, oc.2, hcont, τ.1.2⟩) x0
          (castHpt e' hh) = 0 :=
        hVA.tgt_supported ⟨τ.1.1, oc.1, oc.2, hcont, τ.1.2⟩ x0 hzc0
          (castHpt e' hh) hq hact hintgt
      have hcle : V.cntc ⟨τ.1.1, oc.1, oc.2, hcont, τ.1.2⟩ x0 cc
          (castHpt e' hh) = 0 := by
        have hle : V.cntc ⟨τ.1.1, oc.1, oc.2, hcont, τ.1.2⟩ x0 cc (castHpt e' hh)
            ≤ S.cntraw (V.moveOf ⟨τ.1.1, oc.1, oc.2, hcont, τ.1.2⟩) x0
              (castHpt e' hh) := by
          letI := S.finA (V.moveOf
            (⟨τ.1.1, oc.1, oc.2, hcont, τ.1.2⟩ : MoveData n C)) x0 (castHpt e' hh)
          unfold CtsMeasured.cntc StepSys.cntraw
          rw [← Finset.card_univ]
          exact Finset.card_filter_le _ _
        omega
      have hpz : ((cp.P τ.1.1 oc.1 oc.2 τ.1.2 cc).eval q₀ : ℚ) = 0 := by
        rw [cp.count ⟨τ.1.1, oc.1, oc.2, hcont, τ.1.2⟩ cc x0 hzc0 hq
          (castHpt e' hh) hmm']
        exact_mod_cast hcle
      rw [show (((cp.P τ.1.1 oc.1 oc.2 τ.1.2 cc).eval q₀ : ℚ) : ℝ) = 0 by
        exact_mod_cast hpz]
      ring
    rw [tsum_congr hzero, tsum_zero]

end LeanUrat.MovesV
