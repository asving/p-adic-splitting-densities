/-  MovesV unit V3-9c `init_rat` (RESTATED C23/A-1(3); double-count killed
    REV 3) — INIT-RAT as a THEOREM under its displayed burdens: per
    (template, component) the PolyGeom with countT = the (ENT-U) census
    polynomial, countS = 1, geom = the WEIGHT-ONLY Gent. -/
import LeanUrat.MovesV.V3_aggfullB
import LeanUrat.MovesV.V3_entcount

set_option linter.style.longLine false
set_option linter.style.header false

namespace LeanUrat.MovesV
open LeanUrat.MovesS (Qq OKat evalAt PolyGeom)

/-- `algebraMap` of a polynomial is always regular at every base point. -/
private theorem initRat_okat_alg (q₀ : ℚ) (p : Polynomial ℚ) :
    algebraMap (Polynomial ℚ) Qq p ∈ OKat q₀ := by
  rw [MovesS.mem_OKat_iff, RatFunc.denom_algebraMap]; simp

/-- and `evalAt` of it is ordinary polynomial evaluation. -/
private theorem initRat_evalAt_alg (q₀ : ℚ) (p : Polynomial ℚ)
    (h : algebraMap (Polynomial ℚ) Qq p ∈ OKat q₀) :
    evalAt q₀ ⟨algebraMap (Polynomial ℚ) Qq p, h⟩ = p.eval q₀ := by
  change RatFunc.eval (RingHom.id ℚ) q₀ (algebraMap (Polynomial ℚ) Qq p) = p.eval q₀
  rw [RatFunc.eval_algebraMap]; simp [Polynomial.eval₂_id]

/-- `instCensus` collapses to `entCensus` of the total instantiation. -/
private theorem initRat_instCensus_eq {n : ℕ} {C : CtsFamily n} {S : StepSys n}
    (V : CtsMeasured n C S) (εT : EntTemplate n) (h : Hpt εT.entDim)
    (β₀ : S.Cell) (q₀ : ℚ) :
    V.instCensus εT h β₀ q₀ = V.entCensus (writeHeights εT h) β₀ q₀ := by
  have hs : writeHeights? εT h = some (writeHeights εT h) :=
    (Option.some_get (writeHeights_total εT h)).symm
  unfold CtsMeasured.instCensus
  rw [hs]; rfl

theorem initRat_comp {n : ℕ} {C : CtsFamily n} {S : StepSys n}
    (V : CtsMeasured n C S) (XsEnt : XHDsEnt n S V) (hEU : EntU V)
    (hEC : EntCount V) (hA : AffEnt n) (β₀ : S.Cell) (i : V.EntIx β₀) :
    ∃ P : MovesS.PolyGeom,
      P.countS = 1 ∧ P.geom = XsEnt.Gent β₀ i ∧
      (∀ h : Hpt i.1.1.entDim, ((V.entDom i.1.1).comps.get i.1.2).Mem h →
        ∀ q₀ ∈ V.Pools, (P.countT.eval q₀ : ℚ)
          = V.entCensus (writeHeights i.1.1 h) β₀ q₀) ∧
      ∀ q₀ (hq : q₀ ∈ V.Pools), ∃ hok : P.val ∈ OKat q₀,
        ((evalAt q₀ ⟨P.val, hok⟩ : ℚ) : ℝ) = iotaShV V XsEnt i q₀ := by
  -- the common census polynomial from (ENT-U)
  obtain ⟨Pp, _hdeg, hP⟩ := hEU β₀ i
  obtain ⟨b, as, hdvd⟩ := XsEnt.Gent_denom β₀ i
  -- the component and its base (a member of itself, coeffs ≡ 0)
  set comp := (V.entDom i.1.1).comps.get i.1.2 with hcomp
  have hbase : comp.Mem comp.base := ⟨fun _ => 0, by funext j; simp⟩
  -- the census polynomial interpolates the base count = entCount
  have hPval : ∀ q₀ ∈ V.Pools, Pp.eval q₀ = (V.entCount i q₀ : ℚ) := by
    intro q₀ hq
    rw [hP comp.base hbase q₀ hq,
        show V.entCount i q₀ = V.instCensus i.1.1 comp.base β₀ q₀ from rfl,
        initRat_instCensus_eq]
  set myPG : PolyGeom :=
    ⟨Pp, Pp.natDegree, le_refl _, 1, 0, by simp,
     XsEnt.Gent β₀ i, b, as, hdvd⟩ with hPGdef
  have hval : myPG.val = algebraMap (Polynomial ℚ) Qq (Pp * 1) * XsEnt.Gent β₀ i := rfl
  refine ⟨myPG, rfl, rfl, ?_, ?_⟩
  · -- census interpolation clause (countT = Pp)
    intro h hmem q₀ hq; exact hP h hmem q₀ hq
  · -- the value clause
    intro q₀ hq
    have hAlg : algebraMap (Polynomial ℚ) Qq (Pp * 1) ∈ OKat q₀ :=
      initRat_okat_alg q₀ _
    have hG : XsEnt.Gent β₀ i ∈ OKat q₀ := XsEnt.Gent_ok β₀ i q₀ hq
    have hok : myPG.val ∈ OKat q₀ := by rw [hval]; exact Subring.mul_mem _ hAlg hG
    refine ⟨hok, ?_⟩
    rw [show (⟨myPG.val, hok⟩ : OKat q₀)
          = (⟨algebraMap (Polynomial ℚ) Qq (Pp * 1), hAlg⟩ : OKat q₀)
            * ⟨XsEnt.Gent β₀ i, hG⟩
          from Subtype.ext hval, map_mul, initRat_evalAt_alg]
    simp only [iotaShV, dif_pos hq, mul_one]
    rw [hPval q₀ hq]
    push_cast
    ring

theorem initRat_agg {n : ℕ} {C : CtsFamily n} {S : StepSys n}
    (V : CtsMeasured n C S) (XsEnt : XHDsEnt n S V) (hEU : EntU V)
    (hEC : EntCount V) (hA : AffEnt n) (β₀ : S.Cell) :
    ∃ G : Qq, ∀ q₀ (hq : q₀ ∈ V.Pools), ∃ hok : G ∈ OKat q₀,
      ((evalAt q₀ ⟨G, hok⟩ : ℚ) : ℝ) = iotaValV V XsEnt β₀ q₀ := by
  haveI : Finite (EntTemplate n) := template_finite n
  haveI : Finite (V.EntIx β₀) := by unfold CtsMeasured.EntIx; exact Subtype.finite
  haveI : Fintype (V.EntIx β₀) := Fintype.ofFinite _
  choose Pf hPf using fun i => initRat_comp V XsEnt hEU hEC hA β₀ i
  refine ⟨∑ i : V.EntIx β₀, (Pf i).val, ?_⟩
  intro q₀ hq
  choose hokf heqf using fun i => (hPf i).2.2.2 q₀ hq
  have hok : (∑ i : V.EntIx β₀, (Pf i).val) ∈ OKat q₀ :=
    Subring.sum_mem _ (fun i _ => hokf i)
  refine ⟨hok, ?_⟩
  have hcoe : (⟨∑ i : V.EntIx β₀, (Pf i).val, hok⟩ : OKat q₀)
      = ∑ i : V.EntIx β₀, (⟨(Pf i).val, hokf i⟩ : OKat q₀) := by
    apply Subtype.ext; simp only [AddSubmonoidClass.coe_finsetSum]
  rw [hcoe, map_sum]
  push_cast
  unfold iotaValV
  exact Finset.sum_congr (by ext j; simp) (fun i _ => heqf i)

end LeanUrat.MovesV
