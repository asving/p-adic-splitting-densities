/-  MovesV unit V5-8 `cell_refine` (NEW REV 3, F-4 + Codex-9) — the DERIVED
    count-bearing refinement identity: Σ_c P_c·ΣGcell = T·ΣGc — the COUNT
    FACTOR ON BOTH SIDES, displayed; nothing collapsed, nothing decided. -/
import LeanUrat.MovesV.V2_valB
import LeanUrat.MovesV.V5_comphs
import LeanUrat.MovesV.V0_linset
import LeanUrat.MovesV.V0_partition
import LeanUrat.MovesV.V1_xhds

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.style.maxHeartbeats false

namespace LeanUrat.MovesV
open LeanUrat.MovesS (OKat evalAt)
open Classical

/-- the cell-face weight-sum value (dite-eval). -/
noncomputable def gcellVal {n : ℕ} {C : CtsFamily n} {S : StepSys n}
    {V : CtsMeasured n C S} {W : XHDw n S} {TE : TmplEvents n S}
    {D : XHDd n S TE} {Xs : XHDs n S W D} (XsC : XHDsC n S W D V Xs)
    (d : MoveData n C) (c : V.DCellO d.s d.m d.o d.α) (q₀ : ℚ) : ℝ :=
  ∑ j, if hok : XsC.Gcell d c j ∈ OKat q₀
    then ((evalAt q₀ ⟨XsC.Gcell d c j, hok⟩ : ℚ) : ℝ) else 0

/-- extend a nonneg-supported HasSum from a listed subdomain to a larger one:
outside the small domain the summand vanishes (abstract in the height dim, so the
subtype/index whnf stays cheap). -/
theorem hasSum_semilin_extend {D₀ : ℕ} (A B : SemilinPart D₀) (Ψ : Hpt D₀ → ℝ)
    (hAB : ∀ h, A.Mem h → B.Mem h) (hz : ∀ h, ¬ A.Mem h → Ψ h = 0)
    {v : ℝ} (hv : HasSum (fun h : {h // A.Mem h} => Ψ h.1) v) :
    HasSum (fun h : {h // B.Mem h} => Ψ h.1) v := by
  have hvi := (hasSum_subtype_iff_indicator (f := Ψ) (s := {h | A.Mem h})).mp hv
  refine (hasSum_subtype_iff_indicator (f := Ψ) (s := {h | B.Mem h})).mpr ?_
  have hind : Set.indicator {h | A.Mem h} Ψ = Set.indicator {h | B.Mem h} Ψ := by
    funext h
    simp only [Set.indicator_apply, Set.mem_setOf_eq]
    by_cases hA : A.Mem h
    · rw [if_pos hA, if_pos (hAB h hA)]
    · rw [if_neg hA]
      by_cases hB : B.Mem h
      · rw [if_pos hB, hz h hA]
      · rw [if_neg hB]
  rw [← hind]; exact hvi

set_option maxHeartbeats 1000000 in
theorem cell_refine {n : ℕ} {C : CtsFamily n} {S : StepSys n}
    {V : CtsMeasured n C S} {W : XHDw n S} {TE : TmplEvents n S}
    {D : XHDd n S TE} {Xs : XHDs n S W D}
    (hVA : ValA n C S V) (U : XHDu n S) (DC : XHDdC n S V)
    (hTie : MDomTie V TE D) (XsC : XHDsC n S W D V Xs)
    (hcell : CellPolyPack n C S V) (d : MoveData n C) {q₀ : ℚ}
    (x : S.Hist q₀ (V.toStepCells.symm d.src)) (hzc : S.zc x)
    (hq : q₀ ∈ V.Pools) :
    (letI := V.finDO d.s d.m d.o d.α
     ∑ c : V.DCellO d.s d.m d.o d.α,
       (((hcell.P d.s d.m d.o d.α c).eval q₀ : ℚ) : ℝ) * gcellVal XsC d c q₀)
      = (((C.T d.s d.m d.o d.α d.tix).eval q₀ : ℚ) : ℝ)
          * gcVal Xs (.last (V.moveOf d)) q₀ := by
  classical
  letI := V.finDO d.s d.m d.o d.α
  have hqS : q₀ ∈ S.Pools := V.pools_sub hq
  have h1lt : (1 : ℝ) < (q₀ : ℝ) := by exact_mod_cast S.pools_gt_one q₀ hqS
  have hq0 : (0 : ℝ) ≤ (q₀ : ℝ) := by linarith
  -- the partition identity Σ_c cntc = cntraw (definitional, card-fiberwise)
  have hpart : ∀ h, ∑ c, V.cntc d x c h = S.cntraw (V.moveOf d) x h := by
    intro h
    letI := S.finA (V.moveOf d) x h
    simp only [CtsMeasured.cntc, StepSys.cntraw, Fintype.card]
    exact (Finset.card_eq_sum_card_fiberwise
      (fun (a : S.Assign (V.moveOf d) x h) _ => Finset.mem_univ (V.cellOfA d x h a))).symm
  -- tbl_count transported to D.dom(.last (moveOf d)) components
  have htbl : ∀ j : Fin (D.dom (.last (V.moveOf d))).comps.length,
      ((C.T d.s d.m d.o d.α d.tix).eval q₀ : ℚ)
        = (S.cntraw (V.moveOf d) x ((D.dom (.last (V.moveOf d))).comps.get j).base : ℚ) := by
    rw [hTie.mdom_eq d]
    intro j
    exact hVA.tbl_count d x hzc hq j
  -- RHS: the count-weighted HasSum over each component (u-T uniformity)
  have hRcomp : ∀ j : Fin (D.dom (.last (V.moveOf d))).comps.length,
      HasSum (fun h : {h // ((D.dom (.last (V.moveOf d))).comps.get j).Mem h} =>
          (S.cntraw (V.moveOf d) x h.1 : ℝ) * W.g (V.moveOf d) h.1 q₀)
        ((S.cntraw (V.moveOf d) x ((D.dom (.last (V.moveOf d))).comps.get j).base : ℝ)
          * ((evalAt q₀ ⟨Xs.Gc (.last (V.moveOf d)) j,
              Xs.Gc_ok (.last (V.moveOf d)) j q₀ hqS⟩ : ℚ) : ℝ)) := by
    intro j
    have hG := Xs.Gc_hasSum (.last (V.moveOf d)) j q₀ hqS
    have hM := hG.mul_left
      (S.cntraw (V.moveOf d) x ((D.dom (.last (V.moveOf d))).comps.get j).base : ℝ)
    have hmem_base : (D.dom (.last (V.moveOf d))).Mem
        ((D.dom (.last (V.moveOf d))).comps.get j).base :=
      ⟨(D.dom (.last (V.moveOf d))).comps.get j, List.get_mem _ _, linset_base_mem _⟩
    have pos_base := mem_chainCount_pos D (.last (V.moveOf d)) _ hmem_base hqS x hzc
    have hfun : (fun h : {h // ((D.dom (.last (V.moveOf d))).comps.get j).Mem h} =>
          (S.cntraw (V.moveOf d) x h.1 : ℝ) * W.g (V.moveOf d) h.1 q₀)
        = (fun h : {h // ((D.dom (.last (V.moveOf d))).comps.get j).Mem h} =>
          (S.cntraw (V.moveOf d) x ((D.dom (.last (V.moveOf d))).comps.get j).base : ℝ)
            * gProd W (.last (V.moveOf d)) h.1 q₀) := by
      funext h
      have hmem_h : (D.dom (.last (V.moveOf d))).Mem h.1 :=
        ⟨(D.dom (.last (V.moveOf d))).comps.get j, List.get_mem _ _, h.2⟩
      have pos_h := mem_chainCount_pos D (.last (V.moveOf d)) _ hmem_h hqS x hzc
      have hcnt := U.u_T (V.moveOf d) x h.1 _ hqS hzc pos_h pos_base
      rw [hcnt]; rfl
    rw [hfun]; exact hM
  have hRfull := semilin_sum_exact (D.dom (.last (V.moveOf d)))
    (fun h => (S.cntraw (V.moveOf d) x h : ℝ) * W.g (V.moveOf d) h q₀)
    (fun h => mul_nonneg (Nat.cast_nonneg _)
      (gProd_nonneg W (.last (V.moveOf d)) h q₀ hq0))
    _ hRcomp
  -- the RHS value collapses to T·gcVal
  have hRval : (∑ j, (S.cntraw (V.moveOf d) x
        ((D.dom (.last (V.moveOf d))).comps.get j).base : ℝ)
        * ((evalAt q₀ ⟨Xs.Gc (.last (V.moveOf d)) j,
            Xs.Gc_ok (.last (V.moveOf d)) j q₀ hqS⟩ : ℚ) : ℝ))
      = (((C.T d.s d.m d.o d.α d.tix).eval q₀ : ℚ) : ℝ)
          * gcVal Xs (.last (V.moveOf d)) q₀ := by
    rw [gcVal, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [dif_pos (Xs.Gc_ok (.last (V.moveOf d)) j q₀ hqS)]
    congr 1
    exact_mod_cast (htbl j).symm
  rw [hRval] at hRfull
  -- LHS: per-cell weight-only HasSum over the cell face
  have hgc : ∀ c : V.DCellO d.s d.m d.o d.α,
      HasSum (fun h : {h // (V.cdom d c).Mem h} => W.g (V.moveOf d) h.1 q₀)
        (gcellVal XsC d c q₀) := by
    intro c
    have h0 := semilin_sum_exact (V.cdom d c) (fun h => W.g (V.moveOf d) h q₀)
      (fun h => gProd_nonneg W (.last (V.moveOf d)) h q₀ hq0)
      (fun j => ((evalAt q₀ ⟨XsC.Gcell d c j, XsC.Gcell_ok d c j q₀ hqS⟩ : ℚ) : ℝ))
      (fun j => XsC.Gcell_hasSum d c j q₀ hqS)
    have hval : (∑ j, ((evalAt q₀ ⟨XsC.Gcell d c j,
          XsC.Gcell_ok d c j q₀ hqS⟩ : ℚ) : ℝ)) = gcellVal XsC d c q₀ := by
      rw [gcellVal]
      apply Finset.sum_congr rfl
      intro j _
      rw [dif_pos (XsC.Gcell_ok d c j q₀ hqS)]
    rwa [hval] at h0
  -- cdom ⊆ dom(.last (moveOf d))
  have hsub : ∀ (c : V.DCellO d.s d.m d.o d.α) h, (V.cdom d c).Mem h →
      (D.dom (.last (V.moveOf d))).Mem h := by
    intro c h hmemc
    have hpos : 0 < V.cntc d x c h := DC.no_strayC d c h hmemc hq x hzc
    have hle : V.cntc d x c h ≤ S.cntraw (V.moveOf d) x h := by
      letI := S.finA (V.moveOf d) x h
      simp only [CtsMeasured.cntc, StepSys.cntraw, Fintype.card]
      exact Finset.card_filter_le _ _
    have hposraw : 0 < S.cntraw (V.moveOf d) x h := lt_of_lt_of_le hpos hle
    exact D.no_orphan (.last (V.moveOf d)) x h hqS hzc
      (by rw [tgam_last TE (V.moveOf d) x h hqS hzc]; exact hposraw)
  -- extend each cell sum to dom, count-weighted
  have hcellDom : ∀ c : V.DCellO d.s d.m d.o d.α,
      HasSum (fun h : {h // (D.dom (.last (V.moveOf d))).Mem h} =>
          (V.cntc d x c h.1 : ℝ) * W.g (V.moveOf d) h.1 q₀)
        ((((hcell.P d.s d.m d.o d.α c).eval q₀ : ℚ) : ℝ) * gcellVal XsC d c q₀) := by
    intro c
    have h1 := (hgc c).mul_left (((hcell.P d.s d.m d.o d.α c).eval q₀ : ℚ) : ℝ)
    have hfe : (fun h : {h // (V.cdom d c).Mem h} =>
          (((hcell.P d.s d.m d.o d.α c).eval q₀ : ℚ) : ℝ) * W.g (V.moveOf d) h.1 q₀)
        = (fun h : {h // (V.cdom d c).Mem h} =>
          (V.cntc d x c h.1 : ℝ) * W.g (V.moveOf d) h.1 q₀) := by
      funext h
      have hc := hcell.count d c x hzc hq h.1 h.2
      simp only [hc, Rat.cast_natCast]
    rw [hfe] at h1
    exact hasSum_semilin_extend (V.cdom d c) (D.dom (.last (V.moveOf d)))
      (fun h => (V.cntc d x c h : ℝ) * W.g (V.moveOf d) h q₀)
      (fun h hh => hsub c h hh)
      (fun h hh => by
        have hz : V.cntc d x c h = 0 := by
          by_contra hne
          exact hh (DC.no_orphanC d x c h hq hzc (Nat.pos_of_ne_zero hne))
        simp [hz])
      h1
  -- sum over cells, then rewrite Σ_c cntc = cntraw
  have hLfull := hasSum_sum (s := (Finset.univ : Finset (V.DCellO d.s d.m d.o d.α)))
    (fun c _ => hcellDom c)
  have hLfun : (fun h : {h // (D.dom (.last (V.moveOf d))).Mem h} =>
        ∑ c, (V.cntc d x c h.1 : ℝ) * W.g (V.moveOf d) h.1 q₀)
      = (fun h : {h // (D.dom (.last (V.moveOf d))).Mem h} =>
        (S.cntraw (V.moveOf d) x h.1 : ℝ) * W.g (V.moveOf d) h.1 q₀) := by
    funext h
    rw [← Finset.sum_mul, ← Nat.cast_sum, hpart h.1]
  rw [hLfun] at hLfull
  exact hLfull.unique hRfull

end LeanUrat.MovesV
