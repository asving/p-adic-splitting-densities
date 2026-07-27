/-
Unit U-9a `ksub_eval` (medium) — ACTIVITY-GUARDED evaluated (K-SUB) = 1 (R13).
hyp: LedgerIV.part1 + rep_indep (both guarded) + RB.tg_interp/j_interp — the
note's bracket "GIVEN the (iv) ledger + DEG-CONS + the (m, c) CLASSIFICATION with
its (SCS) clause", scoped "restricted per CTS-M(ii) to the ACTIVE block".
sketch: interp → rowVal; rep_indep → x-grouped cell sum; Finset.sum_fiberwise
over cellOut; part1 → 1.  The OKat membership of the routed sum is subring
closure over tg_ok/j_ok (existential-packaged here).
-/
import LeanUrat.MovesS.Defs
import LeanUrat.MovesS.KsubRegroup

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesS

variable {n : ℕ}

theorem ksub_eval {T : TableShape n} {M : MeasuredSide T} (RB : RatBurdens T M)
    (L : LedgerIV T M) (hdc : DegCons T) {e : ℕ} (he : e ∈ Finset.Icc 1 n)
    (τ : T.State e) (hK : KmatHyp T e) :
    ∀ q₀ ∈ M.Pools, M.activeState q₀ e τ →
    ∃ hok : (∑ o : T.Out e τ, routedMass RB e τ o) ∈ OKat q₀,
      evalAt q₀ ⟨∑ o : T.Out e τ, routedMass RB e τ o, hok⟩ = 1 := by
  classical
  intro q₀ hq hact
  -- per-outcome membership in the evaluation-regular subring OKat q₀
  have hmem : ∀ o : T.Out e τ, routedMass RB e τ o ∈ OKat q₀ := by
    intro o
    unfold routedMass
    split
    · exact RB.j_ok e τ o q₀ hq
    · exact RB.tg_ok e τ o q₀ hq
  refine ⟨sum_mem (fun o _ => hmem o), ?_⟩
  -- rewrite the OKat-element ⟨Σ, hok⟩ as a subring sum, then push evalAt through it
  have hsum : (⟨∑ o : T.Out e τ, routedMass RB e τ o, sum_mem (fun o _ => hmem o)⟩ :
        OKat q₀)
      = ∑ o : T.Out e τ, (⟨routedMass RB e τ o, hmem o⟩ : OKat q₀) := by
    apply Subtype.ext
    simp only [AddSubmonoidClass.coe_finsetSum]
  rw [hsum, map_sum]
  -- per-outcome: the evaluated burden, cast to ℝ, is the measured row value
  have per_o : ∀ o : T.Out e τ,
      ((evalAt q₀ (⟨routedMass RB e τ o, hmem o⟩ : OKat q₀) : ℚ) : ℝ)
        = M.rowVal e τ o q₀ := by
    intro o
    by_cases hsplit : routeOf (T.odata e τ o) = .split
    · have hv : (⟨routedMass RB e τ o, hmem o⟩ : OKat q₀)
          = ⟨(RB.jP e τ o).val, RB.j_ok e τ o q₀ hq⟩ := by
        apply Subtype.ext
        show routedMass RB e τ o = (RB.jP e τ o).val
        unfold routedMass; rw [if_pos hsplit]
      rw [hv]; exact RB.j_interp e τ o q₀ hq hsplit
    · have hv : (⟨routedMass RB e τ o, hmem o⟩ : OKat q₀)
          = ⟨(RB.tgP e τ o).val, RB.tg_ok e τ o q₀ hq⟩ := by
        apply Subtype.ext
        show routedMass RB e τ o = (RB.tgP e τ o).val
        unfold routedMass; rw [if_neg hsplit]
      rw [hv]; exact RB.tg_interp e τ o q₀ hq hsplit
  -- reduce the ℚ-goal to ℝ, replace each summand by its row value
  apply Rat.cast_injective (α := ℝ)
  push_cast
  rw [Finset.sum_congr rfl (fun o _ => per_o o)]
  -- Σ_o rowVal = 1, via representative-independence + fiberwise regroup + part1
  obtain ⟨x⟩ := M.rep_ne e he τ
  rw [Finset.sum_congr rfl (fun o _ => L.rep_indep e τ o x q₀ hq hact)]
  have key : (∑ o : T.Out e τ, ∑ c ∈ M.cells e τ o, M.μcell e τ x c q₀)
      = ∑ c : M.Cell e τ, M.μcell e τ x c q₀ := by
    conv_rhs => rw [← Finset.sum_fiberwise_of_maps_to
      (fun (c : M.Cell e τ) (_ : c ∈ (Finset.univ : Finset (M.Cell e τ))) =>
        Finset.mem_univ (M.cellOut e τ c))
      (fun c => M.μcell e τ x c q₀)]
    refine Finset.sum_congr rfl (fun o _ => ?_)
    refine Finset.sum_congr ?_ (fun c _ => rfl)
    ext c
    simp [MeasuredSide.cells]
  rw [key]
  exact_mod_cast L.part1 e he τ x q₀ hq hact

end LeanUrat.MovesS
