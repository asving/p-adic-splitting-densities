/-  MovesV unit V5-5 `comp_sigma` — (COMP-Σ) GIVEN additionally HMC (the tag
    rides — every consumer carries hHMC).  `stepProdVal` (NAME→HOME). -/
import LeanUrat.MovesV.V5_comphs
import LeanUrat.MovesV.V4_naming

set_option linter.style.longLine false
set_option linter.style.header false

namespace LeanUrat.MovesV
open LeanUrat.MovesS (OKat evalAt)

/-- ∏ᵢ Tᵢ.eval·ΣGᵢ over the template's step decomposition. -/
noncomputable def stepProdVal {n : ℕ} {C : CtsFamily n} {S : StepSys n}
    (V : CtsMeasured n C S) {TE : TmplEvents n S} {X : XHDw n S}
    {D : XHDd n S TE} (Xs : XHDs n S X D) :
    ∀ {α}, Template n S α → ℚ → ℝ
  | _, .last mv, q₀ =>
      (((tblOf V mv).eval q₀ : ℚ) : ℝ) * gcVal Xs (.last mv) q₀
  | _, .lastT mv, q₀ =>
      (((tblOfT V mv).eval q₀ : ℚ) : ℝ) * gcVal Xs (.lastT mv) q₀
  | _, .cons mv γ, q₀ =>
      (((tblOf V mv).eval q₀ : ℚ) : ℝ) * gcVal Xs (.last mv) q₀
        * stepProdVal V Xs γ q₀

theorem comp_sigma {n : ℕ} {C : CtsFamily n} {S : StepSys n}
    {V : CtsMeasured n C S} {TE : TmplEvents n S} {D : XHDd n S TE}
    (cc : CompCarrier V TE) (P : C15Pack n S) (X : XHDw n S) (U : XHDu n S)
    (Xs : XHDs n S X D) (hTie : MarkFiberTie TE) (hHMC : HMC TE D)
    (ε : EntShapeV n) (β₀ : S.Cell) {α} (γ : Template n S α) {q₀ : ℚ}
    (hq : q₀ ∈ V.Pools) :
    iotaEps cc ε β₀ q₀ * (((pathProdPoly V γ).eval q₀ : ℚ) : ℝ)
        * gcVal Xs γ q₀
      = iotaEps cc ε β₀ q₀ * stepProdVal V Xs γ q₀ := by
  classical
  have hqS : q₀ ∈ S.Pools := V.pools_sub hq
  have hq0 : (0 : ℝ) ≤ (q₀ : ℝ) := by
    have h1 := S.pools_gt_one q₀ hqS
    exact_mod_cast le_of_lt (lt_trans one_pos h1)
  -- gcVal is the TOTAL gProd sum over the domain (V0-3 partition + Gc_hasSum).
  have hgc : ∀ {ρ} (δ : Template n S ρ),
      HasSum (fun h : {h // (D.dom δ).Mem h} => gProd X δ h.1 q₀)
        (gcVal Xs δ q₀) := by
    intro ρ δ
    have hval : gcVal Xs δ q₀
        = ∑ j, ((evalAt q₀ ⟨Xs.Gc δ j, Xs.Gc_ok δ j q₀ hqS⟩ : ℚ) : ℝ) := by
      unfold gcVal
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [dif_pos (Xs.Gc_ok δ j q₀ hqS)]
    rw [hval]
    exact semilin_sum_exact (D.dom δ) (fun h => gProd X δ h q₀)
      (fun h => gProd_nonneg X δ h q₀ hq0)
      (fun j => ((evalAt q₀ ⟨Xs.Gc δ j, Xs.Gc_ok δ j q₀ hqS⟩ : ℚ) : ℝ))
      (fun j => Xs.Gc_hasSum δ j q₀ hqS)
  -- HMC upgrades to the factorization identity (V4-12(a)).
  have hFact : Factorizes X D := comp_upgrade X D Xs hHMC
  -- pathProd·gcVal collapses to the stepwise product, by induction along γ.
  have key : ∀ {ρ} (δ : Template n S ρ),
      (((pathProdPoly V δ).eval q₀ : ℚ) : ℝ) * gcVal Xs δ q₀
        = stepProdVal V Xs δ q₀ := by
    intro ρ δ
    induction δ with
    | last mv => simp only [stepProdVal, pathProdPoly]
    | lastT mv => simp only [stepProdVal, pathProdPoly]
    | cons mv δ ih =>
      have hcons : gcVal Xs (.cons mv δ) q₀
          = gcVal Xs (.last mv) q₀ * gcVal Xs δ q₀ :=
        hFact mv δ q₀ hqS _ _ _ (hgc (.cons mv δ)) (hgc (.last mv)) (hgc δ)
      simp only [stepProdVal, pathProdPoly, Polynomial.eval_mul, hcons]
      push_cast
      rw [← ih]
      ring
  rw [mul_assoc, key γ]

/-- (COMP-Σ), MARKED-EVENT HasSum FORM (M3 adjudication, final-ratification
verdict 2026-07-29: "CompSigma_Stmt contains only the algebraic equality …
and no marked-event HasSum" — the capstone's COMP-Σ leg now states the
note's series identity): the stabilized marked-event values μ̂(ε, γ, h) SUM
over H(γ) to ι_ε × the stepwise product.  Derived from `comp_hsum` (the
unfactored series) + the `IotaLvlStable` row (the cross-level ιN tie) + the
HMC-conditional algebraic collapse (`comp_sigma`). -/
theorem comp_sigma_hasSum {n : ℕ} {C : CtsFamily n} {S : StepSys n}
    {V : CtsMeasured n C S} {TE : TmplEvents n S} {D : XHDd n S TE}
    (cc : CompCarrier V TE) (P : C15Pack n S) (X : XHDw n S) (U : XHDu n S)
    (hcp : CompProduct cc X) (hstab : IotaLvlStable cc)
    (Xs : XHDs n S X D) (hTie : MarkFiberTie TE) (hHMC : HMC TE D)
    (ε : EntShapeV n) (β₀ : S.Cell) {α} (γ : Template n S α) {q₀ : ℚ}
    (hq : q₀ ∈ V.Pools) :
    HasSum (fun h : {h // (D.dom γ).Mem h} => μhatVal cc ε β₀ γ h.1 q₀)
      (iotaEps cc ε β₀ q₀ * stepProdVal V Xs γ q₀) := by
  have hsum := comp_hsum cc P X U hcp Xs hTie ε β₀ γ hq
  have hlvl : cc.ιN ε β₀ q₀ (compLvl V TE ε γ)
      = iotaEps cc ε β₀ q₀ :=
    hstab ε β₀ q₀ hq (compLvl V TE ε γ) (le_max_left _ _)
  rwa [hlvl, comp_sigma cc P X U Xs hTie hHMC ε β₀ γ hq] at hsum

end LeanUrat.MovesV
