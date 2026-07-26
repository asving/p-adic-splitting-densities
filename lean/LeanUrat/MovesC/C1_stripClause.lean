/-
Unit C1.stripClause — moves_ref: §C.1.5'(1) fresh STRIP clauses: literal zeros, each cuts
p⁻¹; the strip branch of JetSetup.fresh_assembled.
Non-vacuity witness for LevelClause and for fresh_assembled's first branch.
-/
import LeanUrat.MovesC.Defs

set_option linter.style.longLine false
set_option linter.style.header false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesC

variable {p : ℕ}

theorem C1_stripClause {m : ℕ} (c : Fin m) : ∃ cl : LevelClause p m, cl.support = {c} ∧ cl.codim = 1 ∧ ∀ x : Fin m → ZMod p, cl.sat x ↔ x c = 0 := by
  refine ⟨⟨{c}, 1, fun x => x c = 0, ?_, ?_⟩, ?_, ?_, ?_⟩
  · -- dep: sat reads only the support coordinate c
    intro x y h
    have hxy : x c = y c := h c (Finset.mem_singleton_self c)
    rw [hxy]
  · -- count: #{y | y c = 0 ∧ y ≡ 0 off {c}} · p^1 = p^|{c}|; the set is the singleton {0}
    have hcard :
        Nat.card {y : Fin m → ZMod p // y c = 0 ∧ ∀ c' ∉ ({c} : Finset (Fin m)), y c' = 0} = 1 := by
      haveI : Unique {y : Fin m → ZMod p // y c = 0 ∧ ∀ c' ∉ ({c} : Finset (Fin m)), y c' = 0} :=
        { default := ⟨0, by simp, fun c' _ => rfl⟩
          uniq := by
            rintro ⟨y, hy1, hy2⟩
            apply Subtype.ext
            funext i
            by_cases hi : i = c
            · subst hi; exact hy1
            · exact hy2 i (by simp [hi]) }
      exact Nat.card_unique
    rw [hcard, Finset.card_singleton, one_mul]
  · -- cl.support = {c}
    rfl
  · -- cl.codim = 1
    rfl
  · -- cl.sat x ↔ x c = 0
    intro x
    exact Iff.rfl

end LeanUrat.MovesC
