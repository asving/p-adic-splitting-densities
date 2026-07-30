/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.HC1.DefsChild
import LeanUrat.HC1.K1_vertexPin
import LeanUrat.HC1.S2_childW
import LeanUrat.HC1.S3_childK1
import LeanUrat.HC1.S5_childValuation
import LeanUrat.HC1.S9_builder
import LeanUrat.HC1.S9w_residualLaws
import LeanUrat.HC1.V7_stripDischarge
import LeanUrat.Moves.L3_liftMonic
import LeanUrat.Moves.L4_TRANSii
import LeanUrat.Moves.L4_TRANSviii_b_R4

/-!
# HC1.S9a_stageLiteral — the child Stage literal with its arithmetic/valuation legs

S9 DECOMPOSITION unit (blueprint §9.5): "the Stage literal + arithmetic/valuation
legs (data + he..he1t, hmonic/hdeg, hwΦ, hStretch, hK1, hreps, hTvec, hWS)" — the
`Stage` type itself carries those fields, so the unit statement is the ∃ of a
child Stage whose construction is RECORDED: `TransitionData` (the K/e/h/reps/
threshold/slot-min records), the K1 `VertexPin` (σ'.R agrees with the
D.7(vi)-normalized `childR` on C_Φ̂ — the F-frame recording of the residual tie;
the ↥K/↥K′ cast wall stays inside this unit's proof, per the blueprint's own
escalation surface), and the childW valuation tie. Consumes the S9 residual
block's data (the literal sets `w := childW`, `R := (cast of) childR`,
`K := σ.nextField z̄`, `reps := σ.reps ++ [σ.Φ]`, Tvec := the transported
vector) — post the 2026-07-28 unbundle, `childR`'s pins + law pack come through
S9w (`S9w_residualLaws` for the lawful carrier, `childR_laws` for the
choice-projected `(childW, childR)` form; S9r supplies the carrier seed).
SUPPLIED legs per the §9.5 re-census: w-laws from S5/S4/S2/S3, hStretch
definitional at j = 0 slots, arithmetic from th + the (vii) Bézout split,
hmonic/hdeg from `L3_liftMonic`.

**RESTATED (2026-07-28, adjudicated restate-after-refutation): the increment
guard `e·g > 1`.** The acceptance-fleet prover REFUTED the unguarded statement at
the `σ.e * g = 1` corner: there `deg Φ̂ = σ.e·g·deg σ.Φ = deg σ.Φ`, while
`TransitionData.child_reps` puts the outgoing key `σ.Φ` on the child's
representative list, whose entries `hreps` forces into the child coefficient
space `C_Φ̂` (`deg σ.Φ < deg Φ̂`) — contradiction (`S9a_ungated_corner_refuted`
below, the machine-checked kernel). ADJUDICATION (note-read): the note's LST
tower-induction step carries the guard EXPLICITLY — MOVES 3755–3757:
"STEP at an INCREMENT ν_{i+1} (stage data (e_{i+1}, h_{i+1}), **e·g > 1**): the
frame-(i+2) tower adds exactly ONE inner level — the just-read key Φ̂_{i+1}" —
and the `e·g = 1` corner is the note's OTHER species, MOVES 3766–3767: "STEP at
a RECENTERING ν_{i+1} (e_read = 1, degree unchanged): the key is REPLACED
(Φ̂ ↦ Φ̂ + t)" — handled by the PROVED S10_recStage, not by S9. The blueprint had
dropped the guard in transcription; the statement gains the hypothesis
`hEG : 1 < σ.e * g` (D.3's degree ratio `deg Φ̂ / deg Φ = e·g`, `slotBound`'s
increment value). The refutation corner now fails the hypotheses:
`S9a_corner_fails_guard` (`σ.e * g = 1 → ¬ 1 < σ.e * g`).

**RESIDUAL OBLIGATION — DISCHARGED (S9a_final escalation, 2026-07-28): the strip
leg now closes by `V7_stripDischarge` (proved, core axioms only; the planned
V6(b)+TRANSviii_a route was found CIRCULAR — TRANSviii_a consumes a full child
Stage — and V7 was reproved σ′-free from the parent (S6a) coset realizers +
the carrier's hS5' pin; see V7's header). This file is now `sorry`-free; the
paragraph below is the historical census record.**

**RESIDUAL OBLIGATION (census re-run 2026-07-28, this file's single `sorry`).**
Under the guard the construction census closes EXCEPT the (S6a′) BELOW-THRESHOLD
STRIP: the Stage field `hS6a` at child weights `ν ≤ σ.w Φ̂` (above the threshold
it is proved here via `L4_TRANSviii_b`). On the strip, the D.7(vi) pin
(`hS5'`/`VertexPin`, scalar = the RAW parent ψ-digit `digPrime`, `mfun ≡ 0`)
forces the realizable digit set at `ν = e·w̃ + j·h` to be the TWISTED orbit
`⋃_slots D(w̃)·z̄^{j·s − t·w̃}` (parent Bézout `(s,t)`; the twist `= (s·ν − w̃)/h`,
so the twist-0 slot is `(j,w̃) = (t·ν, s·ν)`, out of window range on most of the
strip), while `hS6a` demands the UNTWISTED base orbit `F_Qˣ` — the exact `∃ m`
twist `L4_TRANSviii_a` records. The two are jointly satisfiable iff the strip
twists are `F_Q`-absorbable, which the hypotheses do not supply. ROBUST
COUNTEREXAMPLE NUMERICS (semantic; concrete instance not yet built): depth-2
parent `K = 𝔽₉, F_Q = 𝔽₃` (unramified `g = 2` root read, so its weight-0 digit
set is exactly `𝔽₃ˣ`), parent side `(e,h) = (3,2)` with Bézout `(s,t) = (1,−1)`,
any `g ≥ 1` read on top (guard `3g > 1` PASSES): at `ν = 2 = 3·0 + 1·2` the
window is the single slot `(j,w̃) = (1,0)` (`j = 4` needs `w̃ = −2`), pinned
digit set `𝔽₃ˣ·z̄`, disjoint from `𝔽₃ˣ` for every root `z̄ ∉ 𝔽₃` — so `hS6a`
fails at `(ν, c) = (2, 1)` for EVERY stage carrying the raw pin. The note's own (S6a′) lives in the V′-NORMALIZED child
coordinate (MOVES 2395–2418), where the transported orbit lands untwisted; the
K1 faithfulness flag (K1_vertexPin header) anticipated exactly this: "if S9's
construction realizes a different explicit exponent, the bridges re-instantiate
at the corrected pin".

**ADJUDICATION RESOLVED (V5 sign-off, 2026-07-28 — blueprint §10 Key Finding 2):**
neither queued option. `mfun ≡ 0` IS the note's V′ normalization (the raw pin is
CORRECT), and the mismatch was `Stage.hS6a`'s own over-transcription: the note's
(S6a) is the orbit group AT ITS FIXED POINT (MOVES 1964–1971; D.7(viii)'s
realizers 2431–2435), i.e. the digit coset `F_Qˣ·b(ν)` with ONE base per weight —
not the untwisted `F_Qˣ`. `Stage.hS6a` restated to the coset form (∃ b before
∀ c); this file's `hS6a'` follows it. The strip sorry is now the V7 discharge
(V6(b)'s minimizing-slot base + `L4_TRANSviii_a` conjunct 2), no longer a
normalization mismatch. difficulty: HARD (assembly; the known type wall).
hyp: hEG (the adjudicated note guard).
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 800000

namespace LeanUrat.HC1

open Polynomial LeanUrat.Moves

/-- **The refutation kernel, machine-checked** (the corner the restated guard
excludes): at `σ.e * g = 1` — the recentering species, `deg Φ̂ = deg σ.Φ` — NO
child stage can carry the S9a record: `TransitionData.child_reps` puts the
outgoing key on the child list, `hreps` forces it into `C_Φ̂`, and the degrees
collide. -/
theorem S9a_ungated_corner_refuted {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
    (σ : Stage p F) {ψ : Polynomial ↥σ.K} {g : ℕ}
    {Φhat : Polynomial ℤ_[p]} {e' h' : ℕ} {zbar : Fˣ}
    (th : TransHyp σ ψ g Φhat e' h' zbar) (hcorner : σ.e * g = 1) :
    ¬ ∃ σ' : Stage p F,
        TransitionData σ σ' Φhat e' h' zbar ∧
        VertexPin σ σ' Φhat zbar ∧
        (∀ f, f ≠ 0 → σ'.w f = childW σ Φhat e' h' f) := by
  rintro ⟨σ', td, -, -⟩
  obtain ⟨hmonΦ, hdegΦ⟩ := L3_liftMonic σ ψ g th.hg Φhat th.hlift
  have hΦmem : σ.Φ ∈ σ'.reps := by
    rw [td.child_reps]
    exact List.mem_append_right _ (List.mem_singleton_self _)
  have h1 : σ.Φ.degree < σ'.Φ.degree := (σ'.hreps σ.Φ hΦmem).2
  rw [td.child_key] at h1
  have h2 : Φhat.natDegree = σ.Φ.natDegree := by rw [hdegΦ, hcorner, one_mul]
  rw [Polynomial.degree_eq_natDegree σ.hmonic.ne_zero,
    Polynomial.degree_eq_natDegree hmonΦ.ne_zero, h2] at h1
  exact lt_irrefl _ h1

/-- The corner-exclusion verification: the refutation instance (`σ.e * g = 1`)
fails the restated statement's guard hypothesis `hEG : 1 < σ.e * g`. -/
theorem S9a_corner_fails_guard {e g : ℕ} (hcorner : e * g = 1) : ¬ 1 < e * g := by omega

/-- Unit S9a (RESTATED 2026-07-28 with the adjudicated note guard `e·g > 1`,
MOVES 3755–3757 — see the header): at every INCREMENT read (`1 < σ.e * g`), the
child Stage literal exists with its construction recorded — transition data, the
D.7(vi) vertex pin, and the childW valuation tie. -/
theorem S9a_stageLiteral {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
    (σ : Stage p F) (hσ : StageCoreL σ) {ψ : Polynomial ↥σ.K} {g : ℕ}
    {Φhat : Polynomial ℤ_[p]} {e' h' : ℕ} {zbar : Fˣ}
    (th : TransHyp σ ψ g Φhat e' h' zbar) (hEG : 1 < σ.e * g) :
    ∃ σ' : Stage p F,
      TransitionData σ σ' Φhat e' h' zbar ∧
      VertexPin σ σ' Φhat zbar ∧
      (∀ f, f ≠ 0 → σ'.w f = childW σ Φhat e' h' f) := by
  -- C4 HOIST (2026-07-30, SYNTHESIS_PASS1 C4b; golf HC1#96): the former in-file
  -- construction (Bézout split → S9w carrier → S2/S3/S5 plumbing → hwult tower →
  -- TRANSviii_b/V7 realizers → the Stage literal) now lives ONCE in
  -- `LeanUrat.HC1.S9_builder` (verbatim body hoist — see that file's per-conjunct
  -- record); this main is its projection (conjuncts 1-3; TransitionData = `.base`
  -- of the round-5 record). Statement byte-identical to the pre-hoist form.
  obtain ⟨σ', tc, pin, htie, -, -⟩ := S9_builder σ hσ th hEG
  exact ⟨σ', tc.base, pin, htie⟩
end LeanUrat.HC1

#print axioms LeanUrat.HC1.S9a_stageLiteral
#print axioms LeanUrat.HC1.S9a_ungated_corner_refuted
#print axioms LeanUrat.HC1.S9a_corner_fails_guard
