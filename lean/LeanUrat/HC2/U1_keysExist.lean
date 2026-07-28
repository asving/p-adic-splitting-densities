/-
Unit U1.keys_exist_of_run  (HC-2 campaign — blueprint §5 Layer A, RE-KEYED at N-1)
moves_ref: MovesC `JetSetup.keys_mid`/`landing` docstrings ("ALL reads incl. the FINAL one
obey the recorded-data landing law"); D4's clause (iv) ("the landing key is realized at
EVERY read, incl. the final one — the designated final key").
deps: D4 `ReadsOf`/`SideReads` (clause (iv) + the interior `Φnext` pin), D5 `KeysLawful`.
difficulty: easy (post-re-key).  hypothesis_fields: none beyond the run predicate.
F10 GUARD: L3's lift is at the STAGE pair and must NEVER be conflated with the node pair.

N-1 RE-KEY RECORD (2026-07-28, sign-off round — §9 F-1's adjudication executed):
the former `keys_exist : HistoryCoherent H → ∃ keys, KeysLawful H keys` is REFUTED as
stated and RETIRED — LAST-READ RECORD FREEDOM:
  * Recentering leg: `HistoryCoherent`'s only `.lift` access is the parent-side
    `IsRecenteringCore` clause under the `i+1 < len` guard; the last node's `lift` is a
    free record field — the `{ν with lift := 0}` record update preserves coherence and
    `root_iff` while making `ν.lift ≠ 0` false for EVERY key choice (key-independent;
    Codex-confirmed, fresh context).
  * Increment leg: the final `IsNodeLift` witness needs U1b's D.5 side conditions
    (`hdvd`/`hthr`), which `hcoh` ties to the final read pair by NOTHING (e.g. σ.e = 2,
    h' = 1, g = 1 leaves the required weight odd) — the blueprint U1b NAMED RISK realized.
  * `StageTransHyp` does NOT rescue it (F-1 adjudication): the counterexample is H-side;
    `StageTransHyp` is H-independent and TRUE in the intended model, so conditionalizing
    would produce a FALSE conditional, not an honest one.
THE CERTIFIED ROUTE (this file): D4's clause (iv) records `LandingKey ν Φnext` at every
read INCLUDING the final one, and the interior `Φnext`-pinning clause gives `KeysLawful`'s
conjunct 1 — the run predicate is the honest carrier of final-read lawfulness (a named
`FinalReadLawful` shadow definition was REJECTED). Consumers unaffected: U13/U15 consume
keys through `hseed`'s `∃ keys, KeysLawful` (SEED-EXIST rev-2 form), never through U1;
this unit's surviving role is run-side (MovesT wave-4 + HC-1 run constructions).
FLEET DUTY (queued, not this round): land the compiled negation witness of the retired
`hcoh`-keyed form beside this unit (the `U27_OBSTRUCTION` pattern) so the refutation is
durable — it needs a concrete 2-node coherent history (HC-1 S9-adjacent construction).
-/
import Mathlib
import LeanUrat.HC2.Defs

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesJ
open Polynomial LeanUrat.Moves LeanUrat.MovesC LeanUrat.MovesD

/-- A lawful key tower exists for every classifier RUN (N-1 re-key): D4's clause (iv)
records the landing law at every read — the final one included — and the interior
`Φnext` pin makes the designated keys the recorded child keys. -/
theorem keys_exist_of_run {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
    {n : ℕ} {f : Polynomial ℤ_[p]} {H : History p F}
    (h : ReadsOf p F n f H) :
    ∃ keys : ℕ → Polynomial ℤ_[p], KeysLawful H keys := by
  classical
  obtain ⟨-, -, -, hreads⟩ := h
  -- the designated key of read i: the run's own `Φnext` witness (junk 0 beyond the run)
  refine ⟨fun i => if hi : i < H.nodes.length then
      ((hreads i hi).choose_spec.choose_spec).choose else 0, ?_, ?_⟩
  · -- conjunct 1 (interior keys = recorded child keys): the `Φnext` pin
    intro i hi1
    have hi : i < H.nodes.length := by omega
    have hpin := ((hreads i hi).choose_spec.choose_spec).choose_spec.2.1
    simp only [dif_pos hi]
    exact hpin hi1
  · -- conjunct 2 (landing at EVERY read): SideReads clause (iv)
    intro i hi
    have hland := ((hreads i hi).choose_spec.choose_spec).choose_spec.2.2.2.2.2.1
    simp only [dif_pos hi]
    exact hland

end LeanUrat.MovesJ
