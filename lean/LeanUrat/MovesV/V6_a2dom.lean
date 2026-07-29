/-  MovesV unit V6-2a `a2_domain_chart` (RE-KEYED C3) — the A2 height-domain
    normal form THROUGH THE CHART. -/
import LeanUrat.MovesV.DefsGate

set_option linter.style.longLine false
set_option linter.style.header false

namespace LeanUrat.MovesV

theorem A2chart_image :
    A2chart '' {h | A2dom.Mem h}
      = {h : Hpt 2 | 1 ≤ h 1 ∧ 3 * h 1 < h 0 ∧ Odd (h 0 - h 1)} := by
  have memiff : ∀ h : Hpt 2, A2dom.Mem h ↔ 1 ≤ h 0 := by
    intro h
    constructor
    · rintro ⟨c, hc⟩
      have hb : h 0 = A2dom.base 0 + ∑ j, c j * (A2dom.periods.get j) 0 := by rw [hc]
      rw [show A2dom.base 0 = 1 from rfl] at hb
      omega
    · intro hh
      refine ⟨![h 0 - 1, h 1], ?_⟩
      change h = fun i => A2dom.base i
          + ∑ j : Fin 2, (![h 0 - 1, h 1] : Fin 2 → ℕ) j * (A2dom.periods.get j) i
      funext i; fin_cases i <;> simp [A2dom, Fin.sum_univ_two] <;> omega
  ext H
  simp only [Set.mem_image, Set.mem_setOf_eq]
  constructor
  · rintro ⟨h, hmem, rfl⟩
    rw [memiff] at hmem
    simp only [A2chart, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
    refine ⟨hmem, by omega, ?_⟩
    rw [Nat.odd_iff]; omega
  · rintro ⟨h1, h2, hodd⟩
    rw [Nat.odd_iff] at hodd
    refine ⟨![H 1, (H 0 - 3 * H 1 - 1) / 2], ?_, ?_⟩
    · rw [memiff]; simpa using h1
    · simp only [A2chart, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
      funext i
      fin_cases i <;> simp <;> omega

theorem A2chart_inj : Set.InjOn A2chart {h | A2dom.Mem h} := by
  intro h _ h' _ heq
  have e0 := congrFun heq 0
  have e1 := congrFun heq 1
  simp only [A2chart, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] at e0 e1
  funext i
  fin_cases i
  · exact e1
  · show h 1 = h' 1; omega

/-- one component ⟹ the disjointness convention holds VACUOUSLY. -/
theorem a2_one_component :
    ([A2dom] : List (LinSet 2)).Pairwise
      (fun L L' => ∀ h, ¬(L.Mem h ∧ L'.Mem h)) :=
  List.pairwise_singleton _ _

end LeanUrat.MovesV
