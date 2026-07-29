/-  MovesV unit V5-4 `comp_hsum` — (COMP-hΣ) GIVEN XHD-d/s, NO HMC: the
    unfactored per-template series, via V0-3 over the listed components.
    STATEMENT REPAIR 2026-07-29 (adjudicated; machine-verified refutation from
    the prover fleet): the E-phase RHS hardcoded `iotaEps` = ιN at the entrance
    level, where the value law (V5-2c `comp_h`, stabilized at `compLvl`) forces
    ιN AT `compLvl V TE ε γ` — the statement was off by exactly
    q₀^(−n·(compLvl − entLvl)). RHS re-keyed to
    `cc.ιN ε β₀ q₀ (compLvl V TE ε γ)` (localized fix; V5-5 `comp_sigma` is
    internally consistent and untouched). Blueprint row
    (MOVESV_LEAN_BLUEPRINT_2026-07-28.md V5-4): "(COMP-hΣ), GIVEN XHD-d/s, NO
    HMC: HasSum (fun h : {h // (dom γ).Mem h} => μ̂(ε, γ, h) q₀)
    (ι_{e,ε,β₀} q₀ * Σ_{h∈H(γ)} ∏ (T·g(h_i)))" — the ι symbol is read at the
    stabilized composite level, exactly as `comp_h`'s display fixes it. -/
import LeanUrat.MovesV.V5_comphC
import LeanUrat.MovesV.V0_partition
import LeanUrat.MovesV.V1_xhds

set_option linter.style.longLine false
set_option linter.style.header false

namespace LeanUrat.MovesV
open LeanUrat.MovesS (OKat evalAt)
open Classical

/-- the template weight-sum value (dite-eval over the listed components). -/
noncomputable def gcVal {n : ℕ} {S : StepSys n} {TE : TmplEvents n S}
    {X : XHDw n S} {D : XHDd n S TE} (Xs : XHDs n S X D) {α}
    (γ : Template n S α) (q₀ : ℚ) : ℝ :=
  ∑ j, if hok : Xs.Gc γ j ∈ OKat q₀
    then ((evalAt q₀ ⟨Xs.Gc γ j, hok⟩ : ℚ) : ℝ) else 0

theorem comp_hsum {n : ℕ} {C : CtsFamily n} {S : StepSys n}
    {V : CtsMeasured n C S} {TE : TmplEvents n S} {D : XHDd n S TE}
    (cc : CompCarrier V TE) (P : C15Pack n S) (X : XHDw n S) (U : XHDu n S)
    (hcp : CompProduct cc X)
    (Xs : XHDs n S X D) (hTie : MarkFiberTie TE) (ε : EntShapeV n)
    (β₀ : S.Cell) {α} (γ : Template n S α) {q₀ : ℚ} (hq : q₀ ∈ V.Pools) :
    HasSum (fun h : {h // (D.dom γ).Mem h} => μhatVal cc ε β₀ γ h.1 q₀)
      (cc.ιN ε β₀ q₀ (compLvl V TE ε γ)
        * (((pathProdPoly V γ).eval q₀ : ℚ) : ℝ)
        * gcVal Xs γ q₀) := by
  classical
  have hqS : q₀ ∈ S.Pools := V.toCtsCells.pools_sub hq
  have hpos : (0 : ℝ) ≤ (q₀ : ℝ) := by
    have h1 : (1 : ℝ) < (q₀ : ℝ) := by exact_mod_cast S.pools_gt_one q₀ hqS
    linarith
  have hkey : HasSum (fun h : {h // (D.dom γ).Mem h} => gProd X γ h.1 q₀)
      (gcVal Xs γ q₀) := by
    have H := semilin_sum_exact (D.dom γ) (fun h => gProd X γ h q₀)
      (fun h => gProd_nonneg X γ h q₀ hpos)
      (fun j => ((evalAt q₀ ⟨Xs.Gc γ j, Xs.Gc_ok γ j q₀ hqS⟩ : ℚ) : ℝ))
      (fun j => Xs.Gc_hasSum γ j q₀ hqS)
    have hval : (∑ j, ((evalAt q₀ ⟨Xs.Gc γ j, Xs.Gc_ok γ j q₀ hqS⟩ : ℚ) : ℝ))
        = gcVal Xs γ q₀ := by
      unfold gcVal
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [dif_pos (Xs.Gc_ok γ j q₀ hqS)]
    rw [hval] at H
    exact H
  have hmul := hkey.mul_left
    (cc.ιN ε β₀ q₀ (compLvl V TE ε γ)
      * (((pathProdPoly V γ).eval q₀ : ℚ) : ℝ))
  have hfun : (fun h : {h // (D.dom γ).Mem h} => μhatVal cc ε β₀ γ h.1 q₀)
      = (fun h : {h // (D.dom γ).Mem h} =>
          cc.ιN ε β₀ q₀ (compLvl V TE ε γ)
            * (((pathProdPoly V γ).eval q₀ : ℚ) : ℝ)
            * gProd X γ h.1 q₀) := by
    funext h
    have hcomp := comp_h cc P X U hcp hTie ε β₀ γ h.1 h.2 hq
      (compLvl V TE ε γ) (le_refl _)
    rw [μhatVal, hcomp]
  rw [hfun]; exact hmul

end LeanUrat.MovesV
