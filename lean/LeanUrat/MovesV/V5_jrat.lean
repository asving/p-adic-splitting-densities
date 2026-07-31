/-  MovesV unit V5-7b `j_rat` (PER-(τ,o) C8; OUTCOME-LEVEL quantifier REV 5;
    PER-CELL clause REV 7, C15) — (J-RAT) = CL-18: the deliverable, with the
    per-cell `jcellPG` clauses and the symbolic fiber sum. -/
import LeanUrat.MovesV.V5_jdef
import LeanUrat.MovesV.V0_partition
import LeanUrat.MovesV.V1_xhds

set_option linter.style.longLine false
set_option linter.style.header false

namespace LeanUrat.MovesV
open LeanUrat.MovesS (OKat evalAt)

/-- `algebraMap` of a polynomial is regular at every base point. -/
private theorem jrat_okat_alg (q₀ : ℚ) (p : Polynomial ℚ) :
    algebraMap (Polynomial ℚ) MovesS.Qq p ∈ OKat q₀ := by
  rw [MovesS.mem_OKat_iff, RatFunc.denom_algebraMap]; simp

/-- and `evalAt` of it is ordinary polynomial evaluation. -/
private theorem jrat_evalAt_alg (q₀ : ℚ) (p : Polynomial ℚ)
    (h : algebraMap (Polynomial ℚ) MovesS.Qq p ∈ OKat q₀) :
    evalAt q₀ ⟨algebraMap (Polynomial ℚ) MovesS.Qq p, h⟩ = p.eval q₀ := by
  change RatFunc.eval (RingHom.id ℚ) q₀ (algebraMap (Polynomial ℚ) MovesS.Qq p) = p.eval q₀
  rw [RatFunc.eval_algebraMap]; simp [Polynomial.eval₂_id]

/-- the geometric-class denominator is nonzero. -/
private theorem jrat_geomClass_ne_zero (b : ℕ) (as : Finset ℕ+) :
    (Polynomial.X ^ b * ∏ a ∈ as, (1 - Polynomial.X ^ (a : ℕ)) : Polynomial ℚ) ≠ 0 := by
  apply mul_ne_zero (pow_ne_zero _ Polynomial.X_ne_zero)
  rw [Finset.prod_ne_zero_iff]
  intro a _ h
  have hc : (1 - Polynomial.X ^ (a : ℕ) : Polynomial ℚ).coeff (a : ℕ) = 0 := by
    rw [h]; simp
  rw [Polynomial.coeff_sub, Polynomial.coeff_one, Polynomial.coeff_X_pow] at hc
  simp at hc

/- [SYN2-S1 SWEEP-3, 2026-07-31] denom_dvd_of_add / denom_sum_dvd DELETED —
single proof source = the de-privatized MovesV/Defs pair; uses re-pointed. -/

/-- THE PER-CELL CLAUSE (`jcell_interp`'s exact shape at the instance). -/
theorem jRat_cell {n : ℕ} {C : CtsFamily n} {S : StepSys n}
    {V : CtsMeasured n C S} {W : XHDw n S} {TE : TmplEvents n S}
    {D : XHDd n S TE} {Xs : XHDs n S W D}
    (J : JCells n C S V) (XsC : XHDsC n S W D V Xs)
    (hcell : CellPolyPack n C S V) (s : Skeleton n) (m : (C.bd s).Letter)
    (o : (C.bd s).Outc m) (α : (C.bd s).CellIdx)
    (hr : J.route s m o = .split)
    (c : V.DCellO s m o α) :
    ∀ q₀ ∈ S.Pools,
      ∃ hok : (jcellPG hcell XsC ⟨s, m, o, J.route_cont s m o hr, α⟩ c).val
          ∈ OKat q₀,
      ((evalAt q₀ ⟨_, hok⟩ : ℚ) : ℝ)
        = μcellVal hcell XsC ⟨s, m, o, J.route_cont s m o hr, α⟩ c q₀ := by
  intro q₀ hq
  set d : MoveData n C := ⟨s, m, o, J.route_cont s m o hr, α⟩ with hd
  have hAlg : algebraMap (Polynomial ℚ) MovesS.Qq (hcell.P d.s d.m d.o d.α c * 1)
      ∈ OKat q₀ := jrat_okat_alg q₀ _
  have hG : (∑ j, XsC.Gcell d c j) ∈ OKat q₀ :=
    Subring.sum_mem _ (fun j _ => XsC.Gcell_ok d c j q₀ hq)
  have hval : (jcellPG hcell XsC d c).val
      = algebraMap (Polynomial ℚ) MovesS.Qq (hcell.P d.s d.m d.o d.α c * 1)
        * (∑ j, XsC.Gcell d c j) := rfl
  have hok : (jcellPG hcell XsC d c).val ∈ OKat q₀ := by
    rw [hval]; exact Subring.mul_mem _ hAlg hG
  refine ⟨hok, ?_⟩
  rw [show (⟨(jcellPG hcell XsC d c).val, hok⟩ : OKat q₀)
        = (⟨algebraMap (Polynomial ℚ) MovesS.Qq (hcell.P d.s d.m d.o d.α c * 1), hAlg⟩
            : OKat q₀) * ⟨∑ j, XsC.Gcell d c j, hG⟩ from Subtype.ext hval, map_mul,
      jrat_evalAt_alg,
      show (⟨∑ j, XsC.Gcell d c j, hG⟩ : OKat q₀)
          = ∑ j, (⟨XsC.Gcell d c j, XsC.Gcell_ok d c j q₀ hq⟩ : OKat q₀)
        from Subtype.ext (by simp only [AddSubmonoidClass.coe_finsetSum]), map_sum]
  simp only [μcellVal, dif_pos hq, mul_one]
  push_cast
  ring

theorem jRat {n : ℕ} {C : CtsFamily n} {S : StepSys n}
    {V : CtsMeasured n C S} {W : XHDw n S} {TE : TmplEvents n S}
    {D : XHDd n S TE} {Xs : XHDs n S W D}
    (J : JCells n C S V) (XsC : XHDsC n S W D V Xs)
    (hcell : CellPolyPack n C S V) (s : Skeleton n) (m : (C.bd s).Letter)
    (o : (C.bd s).Outc m) (α : (C.bd s).CellIdx)
    (hr : J.route s m o = .split) :
    ∃ P : MovesS.PolyGeom, P.degBoundT = C.Wloc s m ∧
      P.degBoundS = (C.bd s).Wstate ∧
      (∑ c ∈ J.bcells s m o α,
        (jcellPG hcell XsC ⟨s, m, o, J.route_cont s m o hr, α⟩ c).val
          = P.val) ∧
      ∀ q₀ ∈ S.Pools, ∃ hok : P.val ∈ OKat q₀,
        ((evalAt q₀ ⟨P.val, hok⟩ : ℚ) : ℝ)
          = Jval J hcell XsC ⟨s, m, o, J.route_cont s m o hr, α⟩ q₀ := by
  classical
  have hdvd : ∀ c ∈ J.bcells s m o α,
      ((jcellPG hcell XsC ⟨s, m, o, J.route_cont s m o hr, α⟩ c).val).denom ∣
        Polynomial.X ^ ((J.bcells s m o α).sup
            (fun c => (jcellPG hcell XsC ⟨s, m, o, J.route_cont s m o hr, α⟩ c).qpow))
          * ∏ a ∈ (J.bcells s m o α).biUnion
              (fun c => (jcellPG hcell XsC ⟨s, m, o, J.route_cont s m o hr, α⟩ c).geomDenoms),
              (1 - Polynomial.X ^ (a : ℕ)) := by
    intro c hc
    refine dvd_trans (dvd_trans ?_
      (jcellPG hcell XsC ⟨s, m, o, J.route_cont s m o hr, α⟩ c).geom_denom_dvd) ?_
    · have hh := RatFunc.denom_mul_dvd
        (algebraMap (Polynomial ℚ) MovesS.Qq (hcell.P s m o α c * 1))
        (jcellPG hcell XsC ⟨s, m, o, J.route_cont s m o hr, α⟩ c).geom
      rw [RatFunc.denom_algebraMap, one_mul] at hh
      exact hh
    · exact mul_dvd_mul (pow_dvd_pow _ (Finset.le_sup
          (f := fun c => (jcellPG hcell XsC ⟨s, m, o, J.route_cont s m o hr, α⟩ c).qpow) hc))
        (Finset.prod_dvd_prod_of_subset _ _ _ (Finset.subset_biUnion_of_mem
          (fun c => (jcellPG hcell XsC ⟨s, m, o, J.route_cont s m o hr, α⟩ c).geomDenoms) hc))
  refine ⟨{ countT := 1, degBoundT := C.Wloc s m, degT_le := by simp,
            countS := 1, degBoundS := (C.bd s).Wstate, degS_le := by simp,
            geom := ∑ c ∈ J.bcells s m o α,
              (jcellPG hcell XsC ⟨s, m, o, J.route_cont s m o hr, α⟩ c).val,
            qpow := (J.bcells s m o α).sup
              (fun c => (jcellPG hcell XsC ⟨s, m, o, J.route_cont s m o hr, α⟩ c).qpow),
            geomDenoms := (J.bcells s m o α).biUnion
              (fun c => (jcellPG hcell XsC ⟨s, m, o, J.route_cont s m o hr, α⟩ c).geomDenoms),
            geom_denom_dvd := denom_sum_dvd (jrat_geomClass_ne_zero _ _) _ _ hdvd },
        rfl, rfl, ?_, ?_⟩
  · simp only [MovesS.PolyGeom.val, mul_one, map_one, one_mul]
  · intro q₀ hq
    have hgok : (∑ c ∈ J.bcells s m o α,
        (jcellPG hcell XsC ⟨s, m, o, J.route_cont s m o hr, α⟩ c).val) ∈ OKat q₀ :=
      Subring.sum_mem _ (fun c _ => (jRat_cell J XsC hcell s m o α hr c q₀ hq).choose)
    have hAlg1 : algebraMap (Polynomial ℚ) MovesS.Qq (1 * 1 : Polynomial ℚ) ∈ OKat q₀ :=
      jrat_okat_alg q₀ _
    change ∃ hok : algebraMap (Polynomial ℚ) MovesS.Qq (1 * 1)
          * (∑ c ∈ J.bcells s m o α,
              (jcellPG hcell XsC ⟨s, m, o, J.route_cont s m o hr, α⟩ c).val) ∈ OKat q₀,
        ((evalAt q₀ ⟨algebraMap (Polynomial ℚ) MovesS.Qq (1 * 1)
          * (∑ c ∈ J.bcells s m o α,
              (jcellPG hcell XsC ⟨s, m, o, J.route_cont s m o hr, α⟩ c).val), hok⟩ : ℚ) : ℝ)
          = Jval J hcell XsC ⟨s, m, o, J.route_cont s m o hr, α⟩ q₀
    refine ⟨Subring.mul_mem _ hAlg1 hgok, ?_⟩
    rw [show (⟨_, Subring.mul_mem _ hAlg1 hgok⟩ : OKat q₀)
          = (⟨algebraMap (Polynomial ℚ) MovesS.Qq (1 * 1), hAlg1⟩ : OKat q₀)
            * ⟨∑ c ∈ J.bcells s m o α,
                (jcellPG hcell XsC ⟨s, m, o, J.route_cont s m o hr, α⟩ c).val, hgok⟩
        from Subtype.ext rfl, map_mul, jrat_evalAt_alg,
        show (⟨∑ c ∈ J.bcells s m o α,
              (jcellPG hcell XsC ⟨s, m, o, J.route_cont s m o hr, α⟩ c).val, hgok⟩ : OKat q₀)
            = ∑ c ∈ J.bcells s m o α,
                (⟨(jcellPG hcell XsC ⟨s, m, o, J.route_cont s m o hr, α⟩ c).val,
                  (jRat_cell J XsC hcell s m o α hr c q₀ hq).choose⟩ : OKat q₀)
          from Subtype.ext (by simp only [AddSubmonoidClass.coe_finsetSum]), map_sum]
    simp only [mul_one, Polynomial.eval_one, one_mul]
    push_cast
    refine (Finset.sum_congr rfl (fun c _ =>
      (jRat_cell J XsC hcell s m o α hr c q₀ hq).choose_spec)).trans rfl

end LeanUrat.MovesV
