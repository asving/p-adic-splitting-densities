/-
Unit U-10 `ksub_pool` (medium) — sub-stochastic active rows over Aℝ (D11/R22);
nonnegativity DERIVED and ROUTED (R2-12); `he` binder (Fable2-G3).
moves_ref: "K_e's rows are genuine sub-distributions … every summand ≥ 0 (the
ns-bound tail rides INSIDE the K_e term)".  hyp: LedgerIV + RatBurdens ONLY — for
non-split o, eval TG = rowVal = Σ μcell ≥ 0 (tg_interp + rep_indep + μcell-nonneg
from meas_card's card ratios + xhd_sum); split o likewise via j_interp.  NO
hypothesis about TG on split or J on non-split exists anywhere.

Proof structure (ledger-only; NO ksub_eval / DegCons needed):
* `gwt_nonneg`  : height weights ≥ 0 from the counting identity `meas_card`.
* `mucell_nonneg` : `μcell = ∑_h gwt ≥ 0` via `xhd_sum` + `tsum_nonneg`.
* `rowVal_nonneg` : `rowVal = ∑_{c∈cells} μcell ≥ 0` via `rep_indep`.
* `sum_rowVal_eq_one` : `∑_o rowVal = ∑_c μcell = 1` via `rep_indep` + the
  cellOut-fiber partition + `part1`.
* `evalKmat_real` : the ℝ-value of an evaluated `Kmat`-entry is the kcol-fiber
  `rowVal`-sum (`tg_interp`; the K-column terms are non-split).
The active row-sum equals (via `inactive_vanish`) the full row-sum
`∑_{o kcol} rowVal ≤ ∑_o rowVal = 1`; every entry is ≥ 0.
-/
import LeanUrat.MovesS.Defs
import LeanUrat.MovesS.KsubEval

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesS
open Matrix

variable {n : ℕ}

section Helpers
variable {T : TableShape n} {M : MeasuredSide T}

/-- Height weights are nonneg: `gwt · card(Box) = card(cellEvt) ≥ 0` and `card(Box) > 0`. -/
private lemma gwt_nonneg (L : LedgerIV T M) {e : ℕ} {τ : T.State e}
    {c : M.Cell e τ} (x : M.Rep e τ) {h : M.Hgt} (hh : h ∈ M.HDom e τ c)
    {q₀ : ℚ} (hq : q₀ ∈ M.Pools) (hact : M.activeState q₀ e τ) :
    0 ≤ M.gwt e τ c h q₀ := by
  obtain ⟨N₀, hN₀⟩ := L.meas_card e τ x c h hh q₀ hq hact
  have hcard := hN₀ N₀ le_rfl
  haveI := M.boxpos q₀ N₀
  have hbox : (0 : ℝ) < (Fintype.card (M.Box q₀ N₀) : ℝ) := by
    exact_mod_cast Fintype.card_pos
  have hnn : 0 ≤ M.gwt e τ c h q₀ * (Fintype.card (M.Box q₀ N₀) : ℝ) := by
    rw [hcard]; positivity
  exact nonneg_of_mul_nonneg_left hnn hbox

/-- `μcell ≥ 0`: it is the sum of the nonneg height weights (`xhd_sum`). -/
private lemma mucell_nonneg (L : LedgerIV T M) {e : ℕ} {τ : T.State e}
    (x : M.Rep e τ) (c : M.Cell e τ) {q₀ : ℚ}
    (hq : q₀ ∈ M.Pools) (hact : M.activeState q₀ e τ) :
    0 ≤ M.μcell e τ x c q₀ := by
  have hs := L.xhd_sum e τ x c q₀ hq hact
  rw [← hs.tsum_eq]
  exact tsum_nonneg (fun h => gwt_nonneg L x h.2 hq hact)

/-- `rowVal ≥ 0`: it is the cell-sum of nonneg `μcell` (`rep_indep`). -/
private lemma rowVal_nonneg (L : LedgerIV T M) {e : ℕ} (he : e ∈ Finset.Icc 1 n)
    (τ : T.State e) (o : T.Out e τ) {q₀ : ℚ}
    (hq : q₀ ∈ M.Pools) (hact : M.activeState q₀ e τ) :
    0 ≤ M.rowVal e τ o q₀ := by
  obtain ⟨x⟩ := M.rep_ne e he τ
  rw [L.rep_indep e τ o x q₀ hq hact]
  exact Finset.sum_nonneg (fun c _ => mucell_nonneg L x c hq hact)

/-- Total one-step mass is 1: `∑_o rowVal = ∑_o ∑_{c∈cells o} μcell = ∑_c μcell = 1`
via the `cellOut`-fiber partition and `part1`. -/
private lemma sum_rowVal_eq_one (L : LedgerIV T M) {e : ℕ} (he : e ∈ Finset.Icc 1 n)
    (τ : T.State e) {q₀ : ℚ} (hq : q₀ ∈ M.Pools) (hact : M.activeState q₀ e τ) :
    ∑ o : T.Out e τ, M.rowVal e τ o q₀ = 1 := by
  classical
  obtain ⟨x⟩ := M.rep_ne e he τ
  have hrep : ∀ o, M.rowVal e τ o q₀ = ∑ c ∈ M.cells e τ o, M.μcell e τ x c q₀ :=
    fun o => L.rep_indep e τ o x q₀ hq hact
  simp_rw [hrep]
  have hce : ∀ o : T.Out e τ,
      M.cells e τ o = Finset.univ.filter (fun c => M.cellOut e τ c = o) := by
    intro o; simp only [MeasuredSide.cells]; exact Set.toFinset_setOf _
  simp_rw [hce]
  rw [Finset.sum_fiberwise Finset.univ (M.cellOut e τ) (fun c => M.μcell e τ x c q₀)]
  exact L.part1 e he τ x q₀ hq hact

/-- Per-outcome evaluation of a `Kmat`-summand, cast to ℝ: the kcol term at target `β`
evaluates to `rowVal` (`tg_interp`, non-split), everything else to `0`. -/
private lemma evalAt_kmatTerm (RB : RatBurdens T M) {e : ℕ} {τ : T.State e}
    {q₀ : ℚ} (hq : q₀ ∈ M.Pools) (β : T.State e) (hK : KmatHyp T e)
    (o : T.Out e τ) (w : OKat q₀)
    (hw : w = if h : routeOf (T.odata e τ o) = .kcol
              then (if kTarget T e τ o h (hK τ o h) = β
                    then (⟨RB.TG e τ o, RB.tg_ok e τ o q₀ hq⟩ : OKat q₀) else 0) else 0) :
    ((evalAt q₀ w : ℚ) : ℝ)
      = (if h : routeOf (T.odata e τ o) = .kcol
          then (if kTarget T e τ o h (hK τ o h) = β then M.rowVal e τ o q₀ else 0)
          else 0) := by
  subst hw
  by_cases hk : routeOf (T.odata e τ o) = .kcol
  · rw [dif_pos hk, dif_pos hk]
    by_cases hb : kTarget T e τ o hk (hK τ o hk) = β
    · rw [if_pos hb, if_pos hb]
      have hns : routeOf (T.odata e τ o) ≠ .split := by rw [hk]; decide
      exact RB.tg_interp e τ o q₀ hq hns
    · rw [if_neg hb, if_neg hb, map_zero]; norm_num
  · rw [dif_neg hk, dif_neg hk, map_zero]; norm_num

/-- The ℝ-value of an evaluated `Kmat`-entry is the kcol-fiber `rowVal`-sum. -/
private lemma evalKmat_real (RB : RatBurdens T M) {e : ℕ} {τ : T.State e}
    (hK : KmatHyp T e) {q₀ : ℚ} (hq : q₀ ∈ M.Pools) (β : T.State e)
    (hmem : Kmat T RB e hK τ β ∈ OKat q₀) :
    ((evalAt q₀ ⟨Kmat T RB e hK τ β, hmem⟩ : ℚ) : ℝ)
      = ∑ o : T.Out e τ, (if h : routeOf (T.odata e τ o) = .kcol
          then (if kTarget T e τ o h (hK τ o h) = β then M.rowVal e τ o q₀ else 0)
          else 0) := by
  set g : T.Out e τ → OKat q₀ := fun o =>
    if h : routeOf (T.odata e τ o) = .kcol
    then (if kTarget T e τ o h (hK τ o h) = β
          then (⟨RB.TG e τ o, RB.tg_ok e τ o q₀ hq⟩ : OKat q₀) else 0)
    else 0 with hgdef
  have hKmateq : Kmat T RB e hK τ β = ∑ o, (g o : Qq) := by
    simp only [Kmat, hgdef]
    refine Finset.sum_congr rfl (fun o _ => ?_)
    split_ifs <;> rfl
  have hstep : evalAt q₀ ⟨Kmat T RB e hK τ β, hmem⟩ = ∑ o, evalAt q₀ (g o) := by
    have h1 : (⟨Kmat T RB e hK τ β, hmem⟩ : OKat q₀) = ∑ o, g o := by
      apply Subtype.ext
      rw [AddSubmonoidClass.coe_finsetSum]
      exact hKmateq
    rw [h1, map_sum]
  rw [hstep]
  push_cast
  refine Finset.sum_congr rfl (fun o _ => ?_)
  exact evalAt_kmatTerm RB hq β hK o (g o) (by rw [hgdef])

end Helpers

theorem ksub_pool {T : TableShape n} {M : MeasuredSide T} {RB : RatBurdens T M}
    {e : ℕ} (he : e ∈ Finset.Icc 1 n) (L : LedgerIV T M)
    {hK : KmatHyp T e} {q₀ : ℚ} (P : PoolHyp T M RB e hK q₀) (τA : P.Act) :
    (∀ βA : P.Act, 0 ≤ Aℝ P τA βA) ∧ (∑ βA : P.Act, Aℝ P τA βA) ≤ 1 := by
  have hq : q₀ ∈ M.Pools := P.pool_mem
  have hact : M.activeState q₀ e τA.1 := (P.act_spec τA.1).mp τA.2
  -- Every Kmat entry is evaluation-regular at q₀ (subring closure over `tg_ok`).
  have hmem : ∀ β : T.State e, Kmat T RB e hK τA.1 β ∈ OKat q₀ := by
    intro β
    simp only [Kmat]
    refine Subring.sum_mem _ (fun o _ => ?_)
    by_cases hk : routeOf (T.odata e τA.1 o) = .kcol
    · rw [dif_pos hk]
      by_cases hb : kTarget T e τA.1 o hk (hK τA.1 o hk) = β
      · rw [if_pos hb]; exact RB.tg_ok e τA.1 o q₀ hq
      · rw [if_neg hb]; exact Subring.zero_mem _
    · rw [dif_neg hk]; exact Subring.zero_mem _
  -- The total ℝ-valued row function on all states.
  set F : T.State e → ℝ :=
    fun β => ((evalAt q₀ ⟨Kmat T RB e hK τA.1 β, hmem β⟩ : ℚ) : ℝ) with hF
  have hrow : ∀ o : T.Out e τA.1, 0 ≤ M.rowVal e τA.1 o q₀ :=
    fun o => rowVal_nonneg L he τA.1 o hq hact
  have hsum1 : ∑ o : T.Out e τA.1, M.rowVal e τA.1 o q₀ = 1 :=
    sum_rowVal_eq_one L he τA.1 hq hact
  have hAentry : ∀ β : T.State e, F β
      = ∑ o : T.Out e τA.1, (if h : routeOf (T.odata e τA.1 o) = .kcol
          then (if kTarget T e τA.1 o h (hK τA.1 o h) = β then M.rowVal e τA.1 o q₀ else 0)
          else 0) := by
    intro β
    simp only [hF]
    exact evalKmat_real RB hK hq β (hmem β)
  have hAeq_active : ∀ βA : P.Act, Aℝ P τA βA = F (βA : T.State e) := by
    intro βA
    simp only [hF, Aℝ, Matrix.map_apply, P.A_eval]
    norm_cast
  have hFvanish : ∀ β : T.State e, β ∉ P.Act → F β = 0 := by
    intro β hβ
    simp only [hF]
    rw [P.inactive_vanish τA.1 β (hmem β) τA.2 hβ]; norm_num
  refine ⟨?_, ?_⟩
  · -- Nonnegativity of every active entry.
    intro βA
    rw [hAeq_active βA, hAentry (βA : T.State e)]
    refine Finset.sum_nonneg (fun o _ => ?_)
    split_ifs with h hb
    · exact hrow o
    · exact le_refl 0
    · exact le_refl 0
  · -- Sub-stochastic row sum.
    have e1 : ∑ βA : P.Act, Aℝ P τA βA = ∑ β : T.State e, F β := by
      rw [Finset.sum_congr rfl (fun βA (_ : βA ∈ Finset.univ) => hAeq_active βA)]
      rw [Finset.sum_coe_sort P.Act F]
      exact Finset.sum_subset (Finset.subset_univ P.Act) (fun β _ hβ => hFvanish β hβ)
    have e2 : ∑ β : T.State e, F β
        = ∑ o : T.Out e τA.1, (if routeOf (T.odata e τA.1 o) = .kcol
            then M.rowVal e τA.1 o q₀ else 0) := by
      simp_rw [hAentry]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun o _ => ?_)
      by_cases hk : routeOf (T.odata e τA.1 o) = .kcol
      · simp only [dif_pos hk, if_pos hk]
        rw [Finset.sum_ite_eq Finset.univ (kTarget T e τA.1 o hk (hK τA.1 o hk))
          (fun _ => M.rowVal e τA.1 o q₀)]
        simp
      · simp only [dif_neg hk, if_neg hk, Finset.sum_const_zero]
    rw [e1, e2]
    calc ∑ o : T.Out e τA.1, (if routeOf (T.odata e τA.1 o) = .kcol
              then M.rowVal e τA.1 o q₀ else 0)
        ≤ ∑ o : T.Out e τA.1, M.rowVal e τA.1 o q₀ := by
          refine Finset.sum_le_sum (fun o _ => ?_)
          split_ifs with h
          · exact le_refl _
          · exact hrow o
      _ = 1 := hsum1

end LeanUrat.MovesS
