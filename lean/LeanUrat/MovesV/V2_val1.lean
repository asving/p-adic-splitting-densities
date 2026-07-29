/-  MovesV unit V2-7 `val1_worked` (CELLS CORRECTED Codex-12) — the VAL.1
    worked instance, stated generically: three disjoint cells partitioning the
    NONZERO target; fiber counts 1/0/0. -/
import LeanUrat.MovesV.Defs

set_option linter.style.longLine false
set_option linter.style.header false

namespace LeanUrat.MovesV

theorem val1_cells {F : Type*} [Field F] :
    (∀ p : F × F, p ≠ (0, 0) →
      ((p.1 ≠ 0 ∧ p.2 ≠ 0) ∨ (p.1 ≠ 0 ∧ p.2 = 0) ∨ (p.1 = 0 ∧ p.2 ≠ 0))) ∧
    (∀ p : F × F, ¬((p.1 ≠ 0 ∧ p.2 ≠ 0) ∧ (p.1 ≠ 0 ∧ p.2 = 0))) ∧
    (∀ p : F × F, ¬((p.1 ≠ 0 ∧ p.2 ≠ 0) ∧ (p.1 = 0 ∧ p.2 ≠ 0))) ∧
    (∀ p : F × F, ¬((p.1 ≠ 0 ∧ p.2 = 0) ∧ (p.1 = 0 ∧ p.2 ≠ 0))) := by
  refine ⟨fun p hp => ?_, fun p => by tauto, fun p => by tauto,
    fun p => by tauto⟩
  by_cases h1 : p.1 = 0 <;> by_cases h2 : p.2 = 0
  · exact absurd (by cases p; simp_all) hp
  · exact Or.inr (Or.inr ⟨h1, h2⟩)
  · exact Or.inr (Or.inl ⟨h1, h2⟩)
  · exact Or.inl ⟨h1, h2⟩

open Classical in
theorem val1_fiber_count {F : Type*} [Field F] [Fintype F] (p : F × F) :
    (Finset.univ.filter
        (fun t : Fˣ × Fˣ => (((t.1 : F), (t.2 : F)) : F × F) = p)).card
      = if p.1 ≠ 0 ∧ p.2 ≠ 0 then 1 else 0 := by
  sorry

open Classical in
/-- the origin is no cell's member and carries fiber count 0. -/
theorem val1_origin {F : Type*} [Field F] [Fintype F] :
    (Finset.univ.filter
        (fun t : Fˣ × Fˣ => (((t.1 : F), (t.2 : F)) : F × F) = (0, 0))).card
      = 0 := by
  sorry

end LeanUrat.MovesV
