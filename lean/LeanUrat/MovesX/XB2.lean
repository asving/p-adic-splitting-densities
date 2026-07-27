/-
Unit XB.2 dCertMono  [PROVED, fleet 2026-07-28]
moves_ref: "given (ALIGN-inc): d_cert = #T1-increments + #T2; given both: also the T1
recenterings". deps: Defs. difficulty: MEDIUM.
-/
import LeanUrat.MovesX.Defs

namespace LeanUrat.MovesX
set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

/-- `certified` at the `inc`-only discharge state is exactly the `incT12` population
predicate: a continuing T1-increment or a continuing T2 node. -/
private theorem cert_tf {m : ℕ} (ν : XNode m) :
    certified ⟨true, false⟩ ν = decide (popOf? ν = some Pop.incT12) := by
  simp only [certified, popOf?, XNode.continuing]
  by_cases hc : ν.sel.isSome = true
  · simp only [hc, Bool.true_and, not_true, if_false]
    rcases hrow : rowOf ν with _ | _ | _ | _ | _ <;>
      rcases hi : ν.isIncrement <;> simp_all [rowOf]
  · rw [Bool.not_eq_true] at hc; simp [hc]

/-- `certified` at the full discharge state splits as the disjoint union of the `incT12`
and `recT1` population predicates (a continuing T1 or T2 node). -/
private theorem cert_tt {m : ℕ} (ν : XNode m) :
    certified ⟨true, true⟩ ν =
      (decide (popOf? ν = some Pop.incT12) || decide (popOf? ν = some Pop.recT1)) := by
  simp only [certified, popOf?, XNode.continuing]
  by_cases hc : ν.sel.isSome = true
  · simp only [hc, Bool.true_and, not_true, if_false]
    rcases hrow : rowOf ν with _ | _ | _ | _ | _ <;>
      rcases hi : ν.isIncrement <;> simp_all [rowOf]
  · rw [Bool.not_eq_true] at hc; simp [hc]

/-- The length of a filter by a disjunction of mutually exclusive predicates splits as
the sum of the two filter lengths. -/
private theorem len_filter_or {m : ℕ} (p q : XNode m → Bool) (l : List (XNode m))
    (hpq : ∀ a, ¬ (p a = true ∧ q a = true)) :
    (l.filter (fun a => p a || q a)).length =
      (l.filter p).length + (l.filter q).length := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    by_cases hp : p x = true <;> by_cases hq : q x = true <;>
      simp_all <;> omega

/-- The `incT12` and `recT1` population predicates are mutually exclusive: a node has at
most one population. -/
private theorem pop_excl {m : ℕ} (ν : XNode m) :
    ¬ (decide (popOf? ν = some Pop.incT12) = true ∧
       decide (popOf? ν = some Pop.recT1) = true) := by
  rintro ⟨h1, h2⟩
  simp only [decide_eq_true_eq] at h1 h2
  rw [h1] at h2
  exact absurd h2 (by decide)

theorem dCertMono {n : ℕ} (H : XHistory n) :
    dCert ⟨true, false⟩ H = countPop H .incT12 ∧
    dCert ⟨true, true⟩ H = countPop H .incT12 + countPop H .recT1 := by
  refine ⟨?_, ?_⟩
  · simp only [dCert, countPop]
    rw [show (certified ⟨true, false⟩ : XNode n → Bool)
          = (fun ν => decide (popOf? ν = some Pop.incT12)) from funext cert_tf]
  · simp only [dCert, countPop]
    rw [show (certified ⟨true, true⟩ : XNode n → Bool)
          = (fun ν => decide (popOf? ν = some Pop.incT12) ||
                      decide (popOf? ν = some Pop.recT1)) from funext cert_tt]
    exact len_filter_or _ _ H (fun a => pop_excl a)

end LeanUrat.MovesX
