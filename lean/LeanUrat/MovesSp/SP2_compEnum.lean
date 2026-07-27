/-
Unit Sp.compEnumComplete — moves_ref: "each flank is a composition of its span"
(G1).
sketch: strong induction on span; compEnum span = [[]] at 0, else first-part
split. difficulty: medium. [REV 4, Codex-11 — compEnum_nodup spelled.]
-/
import LeanUrat.MovesSp.DefsEnum

set_option linter.style.longLine false
set_option linter.style.header false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesSp

theorem compEnum_complete {span : ℕ} {c : List ℕ} :
    IsComposition c span ↔ c ∈ compEnum span := by
  induction span using Nat.strong_induction_on generalizing c with
  | _ span ih =>
    match span with
    | 0 =>
      simp only [compEnum, List.mem_singleton, IsComposition]
      constructor
      · rintro ⟨hpos, hsum⟩
        cases c with
        | nil => rfl
        | cons a c' =>
          have ha := hpos a (by simp)
          simp only [List.sum_cons] at hsum
          omega
      · rintro rfl
        exact ⟨by simp, rfl⟩
    | n + 1 =>
      simp only [compEnum, List.mem_flatMap, List.mem_map, List.mem_range, IsComposition]
      constructor
      · rintro ⟨hpos, hsum⟩
        cases c with
        | nil => simp only [List.sum_nil] at hsum; exact absurd hsum (by omega)
        | cons a c' =>
          have ha : 1 ≤ a := hpos a (by simp)
          simp only [List.sum_cons] at hsum
          refine ⟨a - 1, by omega, c', ?_, by rw [Nat.sub_add_cancel ha]⟩
          have hc'comp : IsComposition c' c'.sum :=
            ⟨fun x hx => hpos x (List.mem_cons_of_mem a hx), rfl⟩
          have hlt : c'.sum < n + 1 := by omega
          have hmem := (ih c'.sum hlt).mp hc'comp
          have heq : n - (a - 1) = c'.sum := by omega
          rw [heq]; exact hmem
      · rintro ⟨k, hk, c', hc', rfl⟩
        have hlt : n - k < n + 1 := by omega
        obtain ⟨hpos', hsum'⟩ := (ih (n - k) hlt).mpr hc'
        refine ⟨?_, ?_⟩
        · intro x hx
          simp only [List.mem_cons] at hx
          rcases hx with rfl | hx
          · omega
          · exact hpos' x hx
        · simp only [List.sum_cons]
          omega

theorem compEnum_nodup (span : ℕ) : (compEnum span).Nodup := by
  induction span using Nat.strong_induction_on with
  | _ span ih =>
    match span with
    | 0 => simp [compEnum]
    | n + 1 =>
      simp only [compEnum]
      rw [List.nodup_flatMap]
      refine ⟨?_, ?_⟩
      · intro k hk
        apply List.Nodup.map
        · intro a b h
          simpa only [List.cons.injEq, true_and] using h
        · simp only [List.mem_range] at hk
          exact ih (n - k) (by omega)
      · have hnd : (List.range (n + 1)).Nodup := List.nodup_range
        refine hnd.imp ?_
        intro a b hab x hx1 hx2
        simp only [List.mem_map] at hx1 hx2
        obtain ⟨c1, _, hc1⟩ := hx1
        obtain ⟨c2, _, hc2⟩ := hx2
        have heq : (a + 1) :: c1 = (b + 1) :: c2 := hc1.trans hc2.symm
        simp only [List.cons.injEq] at heq
        obtain ⟨h1, _⟩ := heq
        exact hab (by omega)

end LeanUrat.MovesSp
