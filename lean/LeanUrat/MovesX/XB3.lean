/-
Unit XB.3 fourPop  [E-phase: stated, body sorry]
moves_ref: "{T1/T2 increments} ⊔ {T1 recenterings} ⊔ {T3} ⊔ {T4}" (coherence fields make
it typecheck). deps: XA.1. difficulty: MEDIUM.
-/
import LeanUrat.MovesX.Defs
import LeanUrat.MovesX.XA1

namespace LeanUrat.MovesX
set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

/-- Per-node partition identity: a node contributes 1 to `dTotal` (it is continuing) iff
it lands in exactly one of the four populations. -/
private lemma pop_partition {n : ℕ} (ν : XNode n) :
    (if ν.continuing then (1 : ℕ) else 0) =
      (if popOf? ν = some Pop.incT12 then 1 else 0) +
      (if popOf? ν = some Pop.recT1 then 1 else 0) +
      (if popOf? ν = some Pop.t3 then 1 else 0) +
      (if popOf? ν = some Pop.t4 then 1 else 0) := by
  have h : (popOf? ν).isSome = ν.continuing := by
    unfold popOf?; split <;> simp_all
  rw [← h]
  rcases hp : popOf? ν with _ | c
  · decide
  · cases c <;> decide

theorem fourPop {n : ℕ} (H : XHistory n) :
    dTotal H = countPop H .incT12 + countPop H .recT1 + countPop H .t3 + countPop H .t4 := by
  simp only [dTotal, countPop, ← List.countP_eq_length_filter]
  induction H with
  | nil => rfl
  | cons ν H' ih =>
    rw [List.countP_cons, List.countP_cons, List.countP_cons, List.countP_cons,
      List.countP_cons, ih]
    have key := pop_partition ν
    simp only [decide_eq_true_eq]
    omega

end LeanUrat.MovesX
