/-  MovesV unit V3-8b `ent_agg_ival` — THE ιval IDENTIFICATION, GIVEN
    additionally (ENT-U) — the note's own INIT-RAT line's entry point.
    (`iotaValV`/`iotaShV` — the ledger-level ιval/ιsh defs, one definition,
    two homes recorded per the NAME→HOME table.) -/
import LeanUrat.MovesV.V3_aggfullA
import LeanUrat.MovesV.V3_entu
import LeanUrat.MovesV.V0_linset

set_option linter.style.longLine false
set_option linter.style.header false

namespace LeanUrat.MovesV
open LeanUrat.MovesS (Qq OKat evalAt)

open Classical in
/-- ιsh per EntIx member: count × WEIGHT-ONLY sum (Codex-8's split). -/
noncomputable def iotaShV {n : ℕ} {C : CtsFamily n} {S : StepSys n}
    (V : CtsMeasured n C S) (XsEnt : XHDsEnt n S V) {β₀ : S.Cell}
    (i : V.EntIx β₀) (q₀ : ℚ) : ℝ :=
  if hq : q₀ ∈ V.Pools then
    (V.entCount i q₀ : ℝ) * ((evalAt q₀ ⟨XsEnt.Gent β₀ i, XsEnt.Gent_ok β₀ i q₀ hq⟩ : ℚ) : ℝ)
  else 0

open Classical in
/-- ιval: the finite EntIx aggregate (finiteness via V3-4 × list length). -/
noncomputable def iotaValV {n : ℕ} {C : CtsFamily n} {S : StepSys n}
    (V : CtsMeasured n C S) (XsEnt : XHDsEnt n S V) (β₀ : S.Cell)
    (q₀ : ℚ) : ℝ :=
  haveI : Finite (EntTemplate n) := template_finite n
  haveI : Finite (V.EntIx β₀) := by unfold CtsMeasured.EntIx; exact
    Subtype.finite
  haveI : Fintype (V.EntIx β₀) := Fintype.ofFinite _
  ∑ i : V.EntIx β₀, iotaShV V XsEnt i q₀

theorem ent_agg_ival {n : ℕ} {C : CtsFamily n} {S : StepSys n}
    (V : CtsMeasured n C S) (XsEnt : XHDsEnt n S V) (DE : XHDdEnt n S V)
    (hdom : EntDomOrder0 V) (hEU : EntU V) (β₀ : S.Cell) (q₀ : ℚ)
    (hq : q₀ ∈ V.Pools) :
    HasSum
      (fun p : Σ i : V.EntIx β₀,
          {h // ((V.entDom i.1.1).comps.get i.1.2).Mem h} =>
        ιshH V p.1.1.1 p.2.1 β₀ q₀) (iotaValV V XsEnt β₀ q₀) := by
  classical
  haveI : Finite (EntTemplate n) := template_finite n
  haveI : Finite (V.EntIx β₀) := by unfold CtsMeasured.EntIx; exact Subtype.finite
  haveI : Fintype (V.EntIx β₀) := Fintype.ofFinite _
  -- instCensus IS the scoped-writeHeights census at perimeter points (M1 repair).
  have hIC : ∀ (εT : EntTemplate n) (h : Hpt εT.entDim)
      (hs : Order0Perimeter εT h),
      V.instCensus εT h β₀ q₀ = V.entCensus (writeHeights εT h hs) β₀ q₀ := by
    intro εT h hs
    unfold CtsMeasured.instCensus
    have hsome : writeHeights? εT h = some (writeHeights εT h hs) :=
      (Option.some_get (writeHeights_total_of_perimeter εT h hs)).symm
    rw [hsome]; simp
  -- PER-FIBER: the census is constant on the component (ENT-U), so the fibre
  -- mass is entCount · (weight-only Gent sum).
  have hfiber : ∀ i : V.EntIx β₀,
      HasSum (fun x : {h // ((V.entDom i.1.1).comps.get i.1.2).Mem h} =>
        ιshH V i.1.1 x.1 β₀ q₀) (iotaShV V XsEnt i q₀) := by
    intro i
    obtain ⟨P, _, hP⟩ := hEU β₀ i
    have hconst : ∀ x : {h // ((V.entDom i.1.1).comps.get i.1.2).Mem h},
        (V.instCensus i.1.1 x.1 β₀ q₀ : ℝ) = (V.entCount i q₀ : ℝ) := by
      intro x
      have hsx : Order0Perimeter i.1.1 x.1 := hdom.comp i.1.1 i.1.2 x.2
      have hsb : Order0Perimeter i.1.1 ((V.entDom i.1.1).comps.get i.1.2).base :=
        hdom.comp i.1.1 i.1.2
          (linset_base_mem ((V.entDom i.1.1).comps.get i.1.2))
      have e1 := hP x.1 x.2 hsx q₀ hq
      have e2 := hP _ (linset_base_mem ((V.entDom i.1.1).comps.get i.1.2))
        hsb q₀ hq
      have hqq : (V.entCensus (writeHeights i.1.1 x.1 hsx) β₀ q₀ : ℚ)
          = (V.entCensus (writeHeights i.1.1
              ((V.entDom i.1.1).comps.get i.1.2).base hsb) β₀ q₀ : ℚ) :=
        e1.symm.trans e2
      rw [hIC i.1.1 x.1 hsx,
        show V.entCount i q₀
            = V.instCensus i.1.1 ((V.entDom i.1.1).comps.get i.1.2).base β₀ q₀ from rfl,
        hIC i.1.1 ((V.entDom i.1.1).comps.get i.1.2).base hsb]
      exact_mod_cast hqq
    have hfun : (fun x : {h // ((V.entDom i.1.1).comps.get i.1.2).Mem h} =>
          ιshH V i.1.1 x.1 β₀ q₀)
        = (fun x => (V.entCount i q₀ : ℝ)
            * (q₀ : ℝ) ^ (-((instA i.1.1 x.1 : ℕ) : ℤ))) := by
      funext x; unfold ιshH; rw [hconst x]
    have hval : iotaShV V XsEnt i q₀
        = (V.entCount i q₀ : ℝ)
          * ((evalAt q₀ ⟨XsEnt.Gent β₀ i, XsEnt.Gent_ok β₀ i q₀ hq⟩ : ℚ) : ℝ) := by
      unfold iotaShV; rw [dif_pos hq]
    rw [hfun, hval]
    exact (XsEnt.Gent_hasSum β₀ i q₀ hq).mul_left (V.entCount i q₀ : ℝ)
  -- OUTER: finite EntIx aggregate.  Combine via the finite-base sigma sum.
  set f : (Σ i : V.EntIx β₀, {h // ((V.entDom i.1.1).comps.get i.1.2).Mem h}) → ℝ :=
    fun p => ιshH V p.1.1.1 p.2.1 β₀ q₀ with hf_def
  have hIV : (∑ i : V.EntIx β₀, iotaShV V XsEnt i q₀) = iotaValV V XsEnt β₀ q₀ := by
    unfold iotaValV
    exact Finset.sum_congr (Finset.ext (fun x => by simp)) (fun x _ => rfl)
  have ha : HasSum (fun i : V.EntIx β₀ => iotaShV V XsEnt i q₀)
      (iotaValV V XsEnt β₀ q₀) := by
    rw [← hIV]; exact hasSum_fintype _
  have hnn : ∀ p, 0 ≤ f p := by
    intro p
    have hpos : (0 : ℝ) ≤ (q₀ : ℝ) := by
      have h1 : (1 : ℚ) < q₀ := S.pools_gt_one q₀ (V.pools_sub hq)
      exact_mod_cast le_of_lt (lt_trans one_pos h1)
    show 0 ≤ ιshH V p.1.1.1 p.2.1 β₀ q₀
    unfold ιshH
    exact mul_nonneg (Nat.cast_nonneg _) (zpow_nonneg hpos _)
  have hf' : Summable f := by
    rw [summable_sigma_of_nonneg hnn]
    exact ⟨fun i => (hfiber i).summable, (hasSum_fintype _).summable⟩
  exact HasSum.sigma_of_hasSum ha hfiber hf'

end LeanUrat.MovesV
