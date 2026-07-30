/-
Unit U-8 `ksub_regroup` (medium) — the symbolic (K-SUB) regrouping over
verdictImage (R9, R2-10).  moves_ref: "(K-SUB) Σ_β K_e(τ,β) + Σ_{σ′}
b_e^{term,fin}(τ)(σ′) + (branching-cell one-step mass, per cell once) = 1"
— here the LEFT regrouping identity; the `= 1` evaluation is U-9a/U-9b.
verdictImage is exhaustive for the terminal columns BY CONSTRUCTION.
sketch: partition by routeOf; fiberwise regrouping by kTarget / by verdicts.
-/
import LeanUrat.MovesS.Defs
import LeanUrat.MovesS.Dispatch
import LeanUrat.MovesS.Scs

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesS

variable {n : ℕ}

/-- The route-dispatched one-step mass: J on split, TG otherwise. -/
noncomputable def routedMass {T : TableShape n} {M : MeasuredSide T}
    (RB : RatBurdens T M) (e : ℕ) (τ : T.State e) (o : T.Out e τ) : Qq :=
  if routeOf (T.odata e τ o) = .split then RB.J e τ o else RB.TG e τ o

theorem ksub_regroup {T : TableShape n} {M : MeasuredSide T} (RB : RatBurdens T M)
    {e : ℕ} (he : e ∈ Finset.Icc 1 n) (τ : T.State e) (hK : KmatHyp T e) :
    (∑ β : T.State e, Kmat T RB e hK τ β)
      + (∑ σ' ∈ verdictImage T e τ, bTerm T RB e σ' τ)
      + (∑ o ∈ splitOuts T e τ, RB.J e τ o)
    = ∑ o : T.Out e τ, routedMass RB e τ o := by
  -- First term: the K-matrix row sum collapses to the kcol indicator.
  have h1 : (∑ β : T.State e, Kmat T RB e hK τ β)
      = ∑ o : T.Out e τ, (if routeOf (T.odata e τ o) = .kcol then RB.TG e τ o else 0) := by
    simp only [Kmat]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun o _ => ?_)
    by_cases hk : routeOf (T.odata e τ o) = .kcol
    · rw [if_pos hk,
        Finset.sum_congr rfl (fun β (_ : β ∈ (Finset.univ : Finset (T.State e))) => dif_pos hk),
        Finset.sum_ite_eq]
      simp
    · rw [if_neg hk,
        Finset.sum_congr rfl (fun β (_ : β ∈ (Finset.univ : Finset (T.State e))) => dif_neg hk)]
      simp
  -- Second term: the verdict-image sum collapses to the termFin indicator.
  have h2 : (∑ σ' ∈ verdictImage T e τ, bTerm T RB e σ' τ)
      = ∑ o : T.Out e τ, (if routeOf (T.odata e τ o) = .termFin then RB.TG e τ o else 0) := by
    simp only [bTerm]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun o _ => ?_)
    by_cases ht : routeOf (T.odata e τ o) = .termFin
    · have hmem : (T.odata e τ o).verdicts ∈ verdictImage T e τ := by
        rw [verdictImage]
        exact Finset.mem_image.mpr ⟨o, Set.mem_toFinset.mpr ht, rfl⟩
      rw [if_pos ht]
      have hcongr : ∀ σ' ∈ verdictImage T e τ,
          (if routeOf (T.odata e τ o) = .termFin ∧ (T.odata e τ o).verdicts = σ'
            then RB.TG e τ o else 0)
          = (if (T.odata e τ o).verdicts = σ' then RB.TG e τ o else 0) := by
        intro σ' _
        simp [ht]
      rw [Finset.sum_congr rfl hcongr, Finset.sum_ite_eq, if_pos hmem]
    · rw [if_neg ht]
      apply Finset.sum_eq_zero
      intro σ' _
      exact if_neg (by rintro ⟨h, _⟩; exact ht h)
  -- Third term: the split-outs sum is the split indicator over all outcomes.
  have h3 : (∑ o ∈ splitOuts T e τ, RB.J e τ o)
      = ∑ o : T.Out e τ, (if routeOf (T.odata e τ o) = .split then RB.J e τ o else 0) := by
    simp only [splitOuts, Set.toFinset_setOf, Finset.sum_filter]
  -- Combine: route dispatch is exhaustive and exclusive, so per outcome the summands agree.
  rw [h1, h2, h3, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun o _ => ?_)
  simp only [routedMass]
  cases hr : routeOf (T.odata e τ o) <;> simp

end LeanUrat.MovesS
