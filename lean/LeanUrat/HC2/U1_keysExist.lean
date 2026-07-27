/-
Unit U1.keys_exist  (HC-2 campaign, E-phase — blueprint §5 Layer A)
moves_ref: MovesC `JetSetup.keys_mid`/`landing` docstrings ("ALL reads incl. the FINAL one
obey the recorded-data landing law").
deps: Moves L3_liftExists (proof SHAPE only), IsRecenteringCore, U1b (final-read landing),
D8 `isNodeLift_iff`.  difficulty: medium.  hypothesis_fields: none.
F10 GUARD: L3's lift is at the STAGE pair and must NEVER be conflated with the node pair.
-/
import Mathlib
import LeanUrat.HC2.Defs

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesJ
open Polynomial LeanUrat.Moves LeanUrat.MovesC LeanUrat.MovesD

/-- A lawful key tower exists for every coherent history: interior keys are the recorded
child keys (coherence's `IsNodeLift`/`IsRecenteringCore` clauses ARE the landing law
there); the FINAL key is `Φ − lift` at a recentering, else U1b's read-pair lift. -/
theorem keys_exist {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
    {H : History p F} (hcoh : HistoryCoherent H) :
    ∃ keys : ℕ → Polynomial ℤ_[p],
      (∀ (i : ℕ) (hi : i + 1 < H.nodes.length), keys i = (H.nodes[i+1]'hi).σ.Φ) ∧
      (∀ (i : ℕ) (hi : i < H.nodes.length), LandingKey (H.nodes[i]'hi) (keys i)) := by
  classical
  obtain ⟨_hroot, _hslope, _hgam, htrans⟩ := hcoh
  refine ⟨fun i => if h : i + 1 < H.nodes.length then (H.nodes[i+1]'h).σ.Φ else 0, ?_, ?_⟩
  · -- interior key law: keys i is the child Φ by definition
    intro i hi
    simp only [dif_pos hi]
  · -- landing law
    intro i hi
    by_cases hlast : i + 1 < H.nodes.length
    · -- INTERIOR node: keys i = (nodes[i+1]).σ.Φ; landing comes straight from coherence
      simp only [dif_pos hlast]
      have hstep := htrans i hlast
      refine ⟨?_, ?_⟩
      · -- recentering branch: extract the realizer clauses from IsRecenteringCore.base
        intro hrec
        have hrc := hstep.1 hrec
        obtain ⟨_, _, _, hinC, hne, hw, hR, hΦ, _⟩ := hrc.base
        exact ⟨hinC, hne, hw, hR, hΦ⟩
      · -- non-recentering branch: coherence records IsNodeLift at the child key
        intro hnrec
        exact (hstep.2.1 hnrec).1
    · -- FINAL node (index `len-1`): THE OBSTRUCTION.
      -- `HistoryCoherent H` places NO constraint on the last node's landing data:
      --   * (recentering) `LandingKey` demands `RecenterLiftSpec ν ν.lift`, i.e.
      --     `inC σ.Φ lift ∧ lift ≠ 0 ∧ w lift = w Φ ∧ R lift = C center · T 0`.
      --     `ν.lift` is a FREE `Node` field; coherence mentions any node's `.lift` ONLY
      --     inside `htrans`, guarded by `i+1 < len` — unavailable here (`hlast`). No key
      --     choice repairs this: the four conjuncts never mention `Φtop = keys i`.
      --     (Record-updating a final recentering node's `lift` to `0` keeps H coherent
      --     yet forces `0 ≠ 0` — a genuine refutation, not merely a missing lemma.)
      --   * (increment) `LandingKey` demands `IsNodeLift ν (keys i)`, whose realizers need
      --     `StageCoreL ν.σ` + D.5 thresholds (the `nodeLift_exists`/`L3_liftExists`
      --     hypotheses). `TransitionCoreL` carries no `StageCoreL`; coherence yields
      --     `StageCoreL` for no stage in the tower.
      -- Codex-confirmed (fresh context, decorrelated). Unprovable from `hcoh` alone:
      -- the statement needs a FINAL-NODE landing hypothesis (or `keys` as a `PresentSeed`
      -- parameter carrying `KeysLawful`, the rev-2 D5 route).
      --
      -- ESCALATION VERDICT (Fable, independent re-derivation from the Defs — CONFIRMS):
      --   * Recentering leg: `HistoryCoherent`'s only `.lift` access is the parent-side
      --     `IsRecenteringCore` clause under the `i+1 < len` guard; NO `Node` Prop field
      --     mentions `lift`, so the last node's `lift` is a free record field — the
      --     `{ν with lift := 0}` record update preserves coherence and `root_iff` while
      --     making `ν.lift ≠ 0` false for EVERY key. Key-independent; no route exists.
      --   * Increment leg SHARPENED: `Stage.hS6b` (a Stage FIELD, no `StageCoreL` needed)
      --     + U1b `nodeLift_exists` (PROVED, sorry-free) DO supply the final `IsNodeLift`
      --     witness — but only under U1b's named D.5 side conditions
      --     `hdvd : σ.e ∣ h'·(g−k)` (hStretch confines C-weights to `σ.e·ℤ`) and
      --     `hthr : σ.e·wPrev Φ < h'·(g−k)`; `hcoh` ties the FINAL node's read pair
      --     `(e', h')` to its frame σ by NOTHING (e.g. σ.e = 2, h' = 1, g = 1 leaves the
      --     required weight odd). Exactly the blueprint U1b NAMED RISK, realized.
      --   * CERTIFIED REPAIR ROUTE (scratch-verified against this corpus, ~15 lines):
      --     `ReadsOf p F n f H → ∃ keys, KeysLawful H keys` PROVES — D4's clause (iv)
      --     records `LandingKey ν Φnext` at EVERY read incl. the final one, and the
      --     interior `Φnext`-pinning clause gives conjunct 1 (`choose` + project
      --     `.2.2.2.1`). The D4-fold deviation note ("the designated final key stays
      --     existential at the last read") is exactly the missing datum. Statement-fence:
      --     re-keying U1 to `ReadsOf` (or to D5's `KeysLawful` seed route) needs sign-off.
      simp only [dif_neg hlast]
      sorry

end LeanUrat.MovesJ
