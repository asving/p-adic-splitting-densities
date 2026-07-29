/-  MovesV unit V0-3 `semilin_sum_exact` — the finitely many component sums ADD
    EXACTLY to the H(γ)-sum (no overlap terms — the SemilinPart disj TYPE field). -/
import LeanUrat.MovesV.Defs

set_option linter.style.longLine false
set_option linter.style.header false

namespace LeanUrat.MovesV

theorem semilin_sum_exact {D : ℕ} (S : SemilinPart D) (f : Hpt D → ℝ)
    (hf : ∀ h, 0 ≤ f h) (v : Fin S.comps.length → ℝ)
    (hv : ∀ j, HasSum (fun h : {h // (S.comps.get j).Mem h} => f h.1) (v j)) :
    HasSum (fun h : {h // S.Mem h} => f h.1) (∑ j, v j) := by
  classical
  set U : Fin S.comps.length → Set (Hpt D) :=
    fun j => {h | (S.comps.get j).Mem h} with hU
  have hdisj : ((Finset.univ : Finset (Fin S.comps.length)) :
      Set (Fin S.comps.length)).PairwiseDisjoint U := by
    intro i _ j _ hij
    change Disjoint (U i) (U j)
    rw [Set.disjoint_left]
    intro h hi hj
    have hpw := List.pairwise_iff_get.mp S.disj
    rcases lt_or_gt_of_ne hij with hlt | hlt
    · exact hpw i j hlt h ⟨hi, hj⟩
    · exact hpw j i hlt h ⟨hj, hi⟩
  have hunion : (⋃ i ∈ (Finset.univ : Finset (Fin S.comps.length)), U i)
      = {h | S.Mem h} := by
    ext h
    simp only [Set.mem_iUnion, Finset.mem_univ, exists_prop, true_and,
      Set.mem_setOf_eq, hU]
    constructor
    · rintro ⟨i, hi⟩
      exact ⟨S.comps.get i, List.get_mem _ _, hi⟩
    · rintro ⟨L, hL, hmem⟩
      obtain ⟨i, hi⟩ := List.mem_iff_get.mp hL
      exact ⟨i, hi ▸ hmem⟩
  have hv' : ∀ j, HasSum ((U j).indicator f) (v j) := fun j =>
    hasSum_subtype_iff_indicator.mp (hv j)
  have hsum : HasSum
      (fun x => ∑ j ∈ (Finset.univ : Finset (Fin S.comps.length)), (U j).indicator f x)
      (∑ j, v j) := hasSum_sum (fun j _ => hv' j)
  have heq : (fun x => ∑ j ∈ (Finset.univ : Finset (Fin S.comps.length)),
        (U j).indicator f x) = ({h | S.Mem h}).indicator f := by
    funext x
    rw [← Finset.indicator_biUnion_apply _ _ hdisj, hunion]
  rw [heq] at hsum
  exact hasSum_subtype_iff_indicator.mpr hsum

end LeanUrat.MovesV
