/-
MovesGr HELD-UNIT ROUND (2026-07-27), part 2: the `L5_recTRANSRS` certificate.
Companion to `HeldUnits_certs.lean` (which carries the L4-held certificates); NEW
statements only (statement fence untouched); flagged for semantic-guardian review.

`L5_recTRANSRS` as held states: `IsRecentering σ σ' cc tt` + `GenuineStageModel σ` ⊢
`Nonempty (GenuineStageModel σ') ∧ StageCoreL σ'`. The audit (#GR §D) called it FAITHLESS.
Here that is sharpened to a MACHINE-CHECKED non-provability-in-good-faith certificate:
`σ'.reps`/`σ'.Tvec` are invisible to BOTH hypotheses — `stripReps σ'` (the same stage with
`reps := []`) satisfies the same `IsRecentering` relation, but `StageCoreL` fails on it
(`reps_nonempty`). So the held statement is provable ONLY if no recentering parent ever
has a genuine model (vacuity), and its faithful repair must pin `σ'.reps`/`σ'.Tvec`
(e.g. by consuming `IsRecenteringCore`'s `reps_eq`/`Tvec_eq` instead of bare
`IsRecentering`) — proposed restatement in the blueprint round-2 record.
-/
import Mathlib
import LeanUrat.Moves.Defs
import LeanUrat.Moves.DefsT
import LeanUrat.Moves.DefsCore
import LeanUrat.Moves.DefsL
import LeanUrat.MovesGr.Defs

open Polynomial LeanUrat.Moves LeanUrat.MovesGr LeanUrat.MovesGr.SideVal

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

variable {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]

/-- The reps-stripped clone of a stage: identical in every field except `reps := []`,
`Tvec := []`. Witnesses that `Stage`'s laws never force the representative list. -/
noncomputable def stripReps (σ' : Stage p F) : Stage p F :=
  { σ' with
    reps := []
    Tvec := []
    hreps := by intro ũ h; simp at h
    hTvec := rfl }

/-- `IsRecentering` cannot see `reps`/`Tvec`: the stripped clone recenters iff the
original does (every clause reads only fields the strip preserves). -/
theorem stripReps_recentering (σ σ' : Stage p F) (cc : ↥σ.K) (tt : Polynomial ℤ_[p])
    (hrec : IsRecentering σ σ' cc tt) : IsRecentering σ (stripReps σ') cc tt := hrec

/-- `StageCore` (hence `StageCoreL`) FAILS on the stripped clone: `reps_nonempty`. -/
theorem stripReps_not_stageCore (σ' : Stage p F) : ¬ StageCore (stripReps σ') :=
  fun h => h.reps_nonempty rfl

/-- CERT (held unit `L5_recTRANSRS`): if the held statement were provable as stated, then
NO recentering parent has a genuine model — i.e. it can only ever be proved vacuously.
(Apply the statement to the stripped clone and hit `reps_nonempty`.) -/
theorem recTRANSRS_only_vacuous
    (H : ∀ (σ σ' : Stage p F), GenuineStageModel σ → ∀ (cc : ↥σ.K) (tt : Polynomial ℤ_[p]),
      IsRecentering σ σ' cc tt → Nonempty (GenuineStageModel σ') ∧ StageCoreL σ')
    (σ σ' : Stage p F) (M : GenuineStageModel σ) (cc : ↥σ.K) (tt : Polynomial ℤ_[p])
    (hrec : IsRecentering σ σ' cc tt) : False :=
  stripReps_not_stageCore σ'
    ((H σ (stripReps σ') M cc tt (stripReps_recentering σ σ' cc tt hrec)).2.core)

#print axioms stripReps_recentering
#print axioms stripReps_not_stageCore
#print axioms recTRANSRS_only_vacuous
