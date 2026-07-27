/-
Unit Sp.collapseEqSelf — moves_ref: "self-loop repetition counts (DEPTHS —
run-lengths of equal-species consecutive reads)" (collapse is identity exactly on
run-free words).
deps: Sp.collapseSublist. sketch: Mathlib `List.destutter_eq_self_iff` (the Defs
identity collapseRuns = destutter (· ≠ ·)), or direct induction.
difficulty: medium.
-/
import LeanUrat.MovesSp.Defs
import LeanUrat.MovesSp.SP3_collapseSublist

set_option linter.style.longLine false
set_option linter.style.header false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesSp

theorem collapseRuns_eq_self_iff (l : List Species) :
    collapseRuns l = l ↔ l.Chain' (· ≠ ·) := by
  -- `List.Chain'` is definitionally `List.IsChain`; work with the latter.
  change collapseRuns l = l ↔ List.IsChain (· ≠ ·) l
  induction l using collapseRuns.induct with
  | case1 => simp [collapseRuns]
  | case2 s => simp [collapseRuns]
  | case3 s rest ih =>
      -- list `s :: s :: rest`: both sides are false.
      simp only [collapseRuns, if_true]
      constructor
      · -- collapse dropped the leading duplicate, so it is strictly shorter.
        intro hEq
        exfalso
        have hlen := (collapseRuns_sublist (s :: rest)).length_le
        rw [hEq] at hlen
        simp only [List.length_cons] at hlen
        omega
      · -- a run `s, s` can never be a `(· ≠ ·)`-chain.
        intro hCh
        rw [List.isChain_cons_cons] at hCh
        exact absurd rfl hCh.1
  | case4 s s' rest h ih =>
      -- boundary edge `s ≠ s'`: peel one head and recurse via `ih`.
      simp only [collapseRuns, if_neg h]
      constructor
      · intro hEq
        injection hEq with _ hTail
        rw [List.isChain_cons_cons]
        exact ⟨h, ih.mp hTail⟩
      · intro hCh
        rw [List.isChain_cons_cons] at hCh
        rw [ih.mpr hCh.2]

end LeanUrat.MovesSp
