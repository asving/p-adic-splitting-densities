/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.HC1.DefsSpine
import LeanUrat.HC1.S9c_coreAssembly
import LeanUrat.HC1.S9d_pinVerify
import LeanUrat.Moves.L3_liftMonic

/-!
# HC1.S9_transStage — the D.7 capstone: the child stage ASSEMBLED

moves_ref: MOVES 2464–2465 "The stage axioms (S1′)–(S5′), (S6a′), (S6b′) all hold:
the induction closes with the split axiom." deps: S2–S8, S9a–S9d (the §9.5
decomposition). The honest replacement for MovesGr's fenced `L4_TRANSstage`, now
with the full hypothesis interface (D4(ii)).

**RESTATED (2026-07-28, mechanical-closer round — the S9a adjudication + the
S9b/S9c precedent applied verbatim): the increment guard `e·g > 1`.** The
unguarded statement is refuted at the `σ.e * g = 1` corner by EXACTLY S9a's
kernel argument: S9's ∃ contains `TransitionCoreL`, whose `base.child_reps`
puts the outgoing key `σ.Φ` on the child list, `hreps` forces it into `C_Φ̂`,
and at `e·g = 1` the degrees collide (`S9_ungated_corner_refuted` below, the
in-file machine-checked kernel — standalone, since S9's conclusion does not
carry the pin/tie conjuncts S9a's kernel statement consumes). ADJUDICATION
(S9a's, verbatim): the note's LST tower-induction step carries the guard
EXPLICITLY — MOVES 3755–3757: "STEP at an INCREMENT ν_{i+1} (stage data
(e_{i+1}, h_{i+1}), **e·g > 1**)" — and the `e·g = 1` corner is the note's
OTHER species, MOVES 3766–3767 (RECENTERING, `Φ̂ ↦ Φ̂ + t`), handled by the
PROVED S10_recStage, not by S9. The statement gains the hypothesis
`hEG : 1 < σ.e * g`; the refutation corner fails the guard by
`S9a_corner_fails_guard`.

**PROVED (same round): `S9 = ⟨S9c, S9d⟩`** exactly as blueprint §9.5 planned:
S9c (guarded, PROVED) supplies the literal with `TransitionCoreL`, the
`VertexPin`, the childW tie, and `StageCore`; S9d (PROVED) closes `StageCoreL`
from the pin (`S9d_stageCoreL`: TvecUnitLaw + CoeffLocLaw via the K1 bridges);
the K/e/h pins are the transition record's own fields. The `hΦin` interface of
S9d (the outgoing key is a child coefficient) is the guard's degree consequence
via `L3_liftMonic`. difficulty: closed. hyp: hEG (the adjudicated note guard).
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

namespace LeanUrat.HC1

open Polynomial LeanUrat.Moves

/-- **The refutation kernel, machine-checked** (the S9a kernel, standalone at S9's
conclusion shape): at `σ.e * g = 1` — the recentering species, `deg Φ̂ = deg σ.Φ`
— NO child stage can carry the S9 record: `TransitionCoreL.base.child_reps` puts
the outgoing key on the child list, `hreps` forces it into `C_Φ̂`, and the
degrees collide. -/
theorem S9_ungated_corner_refuted {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
    (σ : Stage p F) {ψ : Polynomial ↥σ.K} {g : ℕ}
    {Φhat : Polynomial ℤ_[p]} {e' h' : ℕ} {zbar : Fˣ}
    (th : TransHyp σ ψ g Φhat e' h' zbar) (hcorner : σ.e * g = 1) :
    ¬ ∃ σ' : Stage p F, TransitionCoreL σ σ' Φhat e' h' zbar ∧ StageCoreL σ' ∧
        σ'.K = σ.nextField zbar ∧ σ'.e = e' ∧ σ'.h = h' := by
  rintro ⟨σ', tc, -, -, -, -⟩
  obtain ⟨hmonΦ, hdegΦ⟩ := L3_liftMonic σ ψ g th.hg Φhat th.hlift
  have hΦmem : σ.Φ ∈ σ'.reps := by
    rw [tc.base.child_reps]
    exact List.mem_append_right _ (List.mem_singleton_self _)
  have h1 : σ.Φ.degree < σ'.Φ.degree := (σ'.hreps σ.Φ hΦmem).2
  rw [tc.base.child_key] at h1
  have h2 : Φhat.natDegree = σ.Φ.natDegree := by rw [hdegΦ, hcorner, one_mul]
  rw [Polynomial.degree_eq_natDegree σ.hmonic.ne_zero,
    Polynomial.degree_eq_natDegree hmonΦ.ne_zero, h2] at h1
  exact lt_irrefl _ h1

/-- Unit S9 (RESTATED 2026-07-28 with the adjudicated note guard `e·g > 1`,
MOVES 3755–3757, per the S9a/S9b/S9c precedent — see the header): every legal
INCREMENT read (`1 < σ.e * g`) of a cored stage produces a cored child stage
with the recorded transition data. -/
theorem S9_transStage {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
    (σ : Stage p F) (hσ : StageCoreL σ) {ψ : Polynomial ↥σ.K} {g : ℕ}
    {Φhat : Polynomial ℤ_[p]} {e' h' : ℕ} {zbar : Fˣ}
    (th : TransHyp σ ψ g Φhat e' h' zbar) (hEG : 1 < σ.e * g) :
    ∃ σ' : Stage p F, TransitionCoreL σ σ' Φhat e' h' zbar ∧ StageCoreL σ' ∧
      σ'.K = σ.nextField zbar ∧ σ'.e = e' ∧ σ'.h = h' := by
  obtain ⟨σ', tc, pin, htie, hcore⟩ := S9c_coreAssembly σ hσ th hEG
  -- the S9d interface: the outgoing key is a child coefficient (the guard's
  -- degree consequence through the L3 lift facts)
  obtain ⟨hmonΦ, hdegΦ⟩ := L3_liftMonic σ ψ g th.hg Φhat th.hlift
  have hΦnatlt : σ.Φ.natDegree < Φhat.natDegree := by
    rw [hdegΦ]
    exact lt_mul_of_one_lt_left σ.hdeg hEG
  have hΦin : inC Φhat σ.Φ := by
    change σ.Φ.degree < Φhat.degree
    rw [Polynomial.degree_eq_natDegree σ.hmonic.ne_zero,
      Polynomial.degree_eq_natDegree hmonΦ.ne_zero]
    exact_mod_cast hΦnatlt
  exact ⟨σ', tc, S9d_stageCoreL σ σ' hσ th tc pin hΦin hcore,
    tc.base.child_field, tc.base.child_e, tc.base.child_h⟩

end LeanUrat.HC1

#print axioms LeanUrat.HC1.S9_transStage
#print axioms LeanUrat.HC1.S9_ungated_corner_refuted
