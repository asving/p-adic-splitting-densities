/-
Unit XB.4 t3Charge  [PROVED, fleet 2026-07-28]
moves_ref: "each T3 node multiplies the key degree by e ≥ 2, so #T3 per branch ≤ ⌊log₂ n⌋
(derived…)"; exponential step proved in-unit, only Πe ≤ n rides (`HistWF.degProd`,
MovesSp-discharged). deps: XA.1. difficulty: MEDIUM.
AS-BUILT (2026-07-30 verify-2 fold-in): t3Charge's `hn : 1 ≤ n` is UNUSED in the body
(machine-confirmed removable via lean_minimal_hypotheses; also mathematically redundant
given W — each e ≥ 1 via epos, so W.degProd forces 1 ≤ n). Statement-fenced: kept,
inventory only (Class B, notes/GOLF_CAMPAIGN_2026-07-30.md). Consumers XC3/XC4/XG1/XG2d
thread hn solely to feed this dead slot — treat the whole thread as one unit in any
future signed-off de-noising.
-/
import LeanUrat.MovesX.Defs
import LeanUrat.MovesX.XA1

namespace LeanUrat.MovesX
set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

private lemma rowT3_facts {n : ℕ} (ν : XNode n) (h : rowOf ν = Row.T3) :
    ν.sel ≠ none ∧ ν.ell = 1 ∧ 2 ≤ ν.e ∧ ν.h = 1 := by
  have hep := ν.ellpos
  have hhp := ν.hpos
  unfold rowOf at h
  split_ifs at h with h1 h2 h3 h4
  all_goals simp_all
  all_goals omega

private lemma t3_facts {n : ℕ} (ν : XNode n) (h : popOf? ν = some Pop.t3) :
    (ν.continuing && ν.isIncrement) = true ∧ 2 ≤ ν.e := by
  have hrow : rowOf ν = Row.T3 ∧ ν.continuing = true := by
    rw [popOf?] at h
    rcases hc : ν.continuing with _ | _ <;>
      rcases hi : ν.isIncrement with _ | _ <;>
      rcases hr : rowOf ν with _ | _ | _ | _ | _ <;>
      simp_all [XNode.continuing]
  obtain ⟨hrow, hcont⟩ := hrow
  obtain ⟨hsel, hell, he, hh⟩ := rowT3_facts ν hrow
  have hinc : ν.isIncrement = true := ν.t3inc hell he hh hcont
  exact ⟨by simp [hcont, hinc], he⟩

private lemma t3_pow_le_prod {n : ℕ} (H : XHistory n) :
    2 ^ (countPop H .t3) ≤
      ((H.filter (fun ν => ν.continuing && ν.isIncrement)).map (·.e)).prod := by
  induction H with
  | nil => simp [countPop]
  | cons ν t ih =>
    simp only [countPop, List.filter_cons] at ih ⊢
    split_ifs with hp3 hp2 hp2
    · -- ν is T3 and passes the increment filter
      have he : 2 ≤ ν.e := (t3_facts ν (of_decide_eq_true hp3)).2
      simp only [List.length_cons, List.map_cons, List.prod_cons, pow_succ]
      calc 2 ^ (List.filter (fun ν => decide (popOf? ν = some Pop.t3)) t).length * 2
          ≤ (List.map (fun x => x.e)
              (List.filter (fun ν => ν.continuing && ν.isIncrement) t)).prod * ν.e :=
            Nat.mul_le_mul ih he
        _ = ν.e * (List.map (fun x => x.e)
              (List.filter (fun ν => ν.continuing && ν.isIncrement) t)).prod :=
            Nat.mul_comm _ _
    · -- ν is T3 but does not pass the increment filter: impossible
      exact absurd (t3_facts ν (of_decide_eq_true hp3)).1 hp2
    · -- ν is not T3 but passes the increment filter
      simp only [List.map_cons, List.prod_cons]
      exact le_trans ih (Nat.le_mul_of_pos_left _ ν.epos)
    · -- ν is neither T3 nor an increment
      exact ih

theorem t3Charge {n : ℕ} (H : XHistory n) (W : HistWF n H) (hn : 1 ≤ n) :
    countPop H .t3 ≤ Nat.log 2 n := by
  apply Nat.le_log_of_pow_le (by norm_num : 1 < 2)
  calc 2 ^ (countPop H .t3)
      ≤ ((H.filter (fun ν => ν.continuing && ν.isIncrement)).map (·.e)).prod :=
        t3_pow_le_prod H
    _ ≤ n := W.degProd

end LeanUrat.MovesX
