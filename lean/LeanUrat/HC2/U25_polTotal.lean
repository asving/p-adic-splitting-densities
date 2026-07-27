/-
Unit U25.polOM_total  (HC-2 campaign, E-phase — blueprint §5 Layer D; escalation risk #1
for arithmetic: the D.10 scale bookkeeping)
moves_ref: §D4-R L1 (canonical-choice totality, kernel (a) — DUAL-VERIFIED at the math
level: PROJECT_STATE "kernel parts (a)+(b) DISCHARGED"); §B2-DEF (S6b′) consumers item
(ii) "the recentering lift (D.10): W = λ″ > w(Φ̂) — (I-aug) is literally the hypothesis".
deps: Stage.hS6b + coherence's (I-aug) chain.  difficulty: HARD.
NAMED RISK (blueprint; resolve FIRST at E-phase, before any prover runs): the scale
bookkeeping — `RecenterLiftSpec` wants `σ.w tL = σ.w σ.Φ` while `hStretch` puts C-weights
in `e·ℤ`; the note's D.10 resolves this with the eligibility side conditions (e_read = 1
reads). If the Lean node vocabulary admits ineligible recentering nodes that the note
excludes, this unit's hypothesis must name the eligibility predicate (statement-fence:
hypothesis NARROWING, needs sign-off + a note-line citation — MOVES 2583–2671). The U30
gate is the day-one tripwire for exactly this risk.
hypothesis_fields: none (target), or the named eligibility predicate (fallback).
-/
import Mathlib
import LeanUrat.HC2.Defs

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesJ
open Polynomial LeanUrat.Moves LeanUrat.MovesC LeanUrat.MovesD

/-- **NECESSITY (the exact obstruction, machine-checked).** Any `RecenterLiftSpec` realizer at
a node forces the node's FRAME to be UNRAMIFIED (`ν.σ.e = 1`). This is precisely the D.10
eligibility side condition the blueprint's NAMED RISK anticipated: `hStretch` puts every
`C_Φ`-weight in `ν.σ.e·ℤ` (`w tL = e·wPrev tL`), while the spec demands `w tL = w Φ = h`
(`hwΦ`); with `gcd(e,h) = 1` (`hcop`) this is solvable ONLY when `e = 1`. Note this is the
FRAME's `ν.σ.e` (the frame-creating read's index), NOT the node's own read index `ν.e` (which
`hspecRec` forces to `1` at every recentering) — the two are distinct, and the node-intrinsic
`ν.e = 1` does NOT supply `ν.σ.e = 1`. -/
private theorem recenterLiftSpec_forces_frame_e_one {p : ℕ} [Fact p.Prime] {F : Type*}
    [Field F] [Finite F] (ν : Node p F) (tL : Polynomial ℤ_[p]) (h : RecenterLiftSpec ν tL) :
    ν.σ.e = 1 := by
  obtain ⟨hinC, hne, hw, _hR⟩ := h
  have hwΦ := ν.σ.hwΦ
  have hstr := ν.σ.hStretch tL hne hinC
  rw [hwΦ, hstr] at hw
  -- `hw : ν.σ.e * ν.σ.wPrev tL = ν.σ.h`, so `ν.σ.e ∣ ν.σ.h`; coprimality forces `e = 1`.
  have hdvd : (ν.σ.e : ℤ) ∣ (ν.σ.h : ℤ) := ⟨ν.σ.wPrev tL, hw.symm⟩
  have hdvdN : ν.σ.e ∣ ν.σ.h := by exact_mod_cast hdvd
  have hcop : Nat.Coprime ν.σ.e ν.σ.h := ν.σ.hcop
  exact hcop.eq_one_of_dvd hdvdN

/-- **NECESSITY 2 (escalation pass — NEW, machine-checked).** Any realizer ALSO forces the
node's recorded `center` to be NONZERO: the spec's digit clause reads `R tL = C center · T 0`,
and the stage law `hRne` (`tL ≠ 0 → R tL ≠ 0`) kills `center = 0`. Interior recenterings get
`center ≠ 0` from coherence (`IsRecentering`'s `cc ≠ 0` conjunct at their OWN index `i`,
guarded by `i+1 < len`); the FINAL node's `center` is an unconstrained record field.
CONSEQUENCE: the blueprint's pre-declared fallback narrowing (`ν.σ.e = 1` alone) is STILL
insufficient — the eligibility predicate must also carry `ν.center ≠ 0` and the (S6b)
threshold (see `recenterLiftSpec_of_eligible`). -/
private theorem recenterLiftSpec_forces_center_ne_zero {p : ℕ} [Fact p.Prime] {F : Type*}
    [Field F] [Finite F] (ν : Node p F) (tL : Polynomial ℤ_[p]) (h : RecenterLiftSpec ν tL) :
    ν.center ≠ 0 := by
  obtain ⟨_, hne, _, hR⟩ := h
  intro hc
  have hRne := ν.σ.hRne tL hne
  rw [hR, hc] at hRne
  simp at hRne

/-- **SUFFICIENCY (escalation pass — machine-checked): the EXACT eligibility predicate.**
The three conditions {`ν.σ.e = 1`, `ν.center ≠ 0`, `ν.σ.wPrev ν.σ.Φ < ν.σ.h`} JOINTLY
suffice: with `e = 1` the pinning `he1t` gives `t = 0`; the (S6b) full-scalar realizer
`hS6b` at parent weight `ν := h` (legal by the threshold — this is (I-aug) at `e = 1`,
`StageCore.prevIaug`'s clause, which `HistoryCoherent` does NOT carry for the final frame)
produces `B ∈ C_Φ`, `B ≠ 0`, `wPrev B = h`, `R B = C center · T 0`; `hStretch` + `hwΦ` give
`w B = 1·h = w Φ`. The first two conditions are NECESSARY (`recenterLiftSpec_forces_frame_e_one`,
`recenterLiftSpec_forces_center_ne_zero`); the third is the only stage law that can source a
realizer weight (`hS6a` would need `h ∈ weightSet` + `center ∈ F_Q`, neither available). This
is D.10's eligibility transcribed complete — the fallback hypothesis set U25 must name. -/
private theorem recenterLiftSpec_of_eligible {p : ℕ} [Fact p.Prime] {F : Type*}
    [Field F] [Finite F] (ν : Node p F) (he1 : ν.σ.e = 1) (hcen : ν.center ≠ 0)
    (hthr : ν.σ.wPrev ν.σ.Φ < (ν.σ.h : ℤ)) :
    ∃ tL : Polynomial ℤ_[p], RecenterLiftSpec ν tL := by
  obtain ⟨B, hB0, hBC, hBw, hBR⟩ := ν.σ.hS6b (ν.σ.h : ℤ) (Units.mk0 ν.center hcen) hthr
  refine ⟨B, hBC, hB0, ?_, ?_⟩
  · rw [ν.σ.hStretch B hB0 hBC, hBw, ν.σ.hwΦ, he1]
    simp
  · rw [hBR, ν.σ.he1t he1]
    simp

/-- POL-TOTALITY (L1 kernel-(a)): at every recentering node of a coherent realizable
history, a `RecenterLiftSpec` realizer exists.

INTERIOR nodes (`i+1 < len`) close cleanly: coherence's `IsRecenteringCore.base` is literally
`RecenterLiftSpec ν ν.lift`. The FINAL recentering node is the genuine obstruction — see the
`sorry` comment below and `recenterLiftSpec_forces_frame_e_one`. -/
theorem polOM_total {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
    {H : History p F} (hcoh : HistoryCoherent H) (hreal : Realizable H)
    (i : ℕ) (hi : i < H.nodes.length)
    (hrec : (H.nodes[i]'hi).species = ReadSpecies.recentering) :
    ∃ tL : Polynomial ℤ_[p], RecenterLiftSpec (H.nodes[i]'hi) tL := by
  obtain ⟨_hroot, _hslope, _hgam, htrans⟩ := hcoh
  by_cases hlast : i + 1 < H.nodes.length
  · -- INTERIOR recentering node: coherence records the transition, whose recentering branch
    -- (`IsRecenteringCore ν.σ (child).σ ν.center ν.lift`) unfolds — through `.base` — to the
    -- four `RecenterLiftSpec` conjuncts at `tL := ν.lift`.
    have hrc := (htrans i hlast).1 hrec
    obtain ⟨_, _, _, hinC, hne, hw, hR, _⟩ := hrc.base
    exact ⟨(H.nodes[i]'hi).lift, hinC, hne, hw, hR⟩
  · -- FINAL recentering node (`i = len - 1`): THE OBSTRUCTION (unprovable from `hcoh`/`hreal`).
    --
    -- `recenterLiftSpec_forces_frame_e_one` shows any realizer forces `ν.σ.e = 1` (D.10
    -- eligibility). Coherence supplies `ν.σ.e = 1` ONLY through the recentering branch of its
    -- transition conjunct, which is guarded by `i+1 < len` (`htrans`, unavailable here). The
    -- transition INTO this node (coherence at `i-1`) sets `ν.σ.e` via `TransitionData.child_e`
    -- to the PREDECESSOR's read index; when the predecessor is an increment with `e ≥ 2`
    -- (a legal, coherent, realizable configuration) `ν.σ.e = 2 ≠ 1`, so NO `tL` satisfies the
    -- spec (necessity above). `hreal`/`TransitionAdmissible` constrain lines & pattern-lead
    -- digits only, never `ν.σ.e`; the node fields give `ν.e = 1` (read), never `ν.σ.e = 1`
    -- (frame). Interior copies of this configuration are coherence-INFEASIBLE (the `i`-indexed
    -- recentering branch would force `ν.σ.e = 1`, clashing with the inherited `2`); ONLY the
    -- final node escapes that clash — the identical last-node freedom refuted at `U1.keys_exist`
    -- (Codex-confirmed there). RESOLUTION = the blueprint's pre-declared FALLBACK: narrow the
    -- hypothesis to the eligibility predicate `(H.nodes[i]'hi).σ.e = 1` (a statement-fence
    -- NARROWING needing designer sign-off + note-line cite, MOVES 2583–2671).
    --
    -- ESCALATION PASS (second prover), obstruction SHARPENED — the `σ.e = 1` narrowing alone
    -- is NOT enough; the final-recentering case is unprovable in EVERY frame:
    --  (O1) frame eligibility `ν.σ.e = 1` — necessity machine-checked above; unavailable when
    --       the predecessor is a root/increment with read `e ≥ 2` (`TransitionData.child_e`;
    --       `hspecInc` needs only `e·g > 1`). A RECENTERING predecessor does supply it
    --       (`IsRecentering`'s `σ'.e = 1` conjunct) — but (O2)/(O3) still block:
    --  (O2) `ν.center ≠ 0` — NEW necessity, machine-checked
    --       (`recenterLiftSpec_forces_center_ne_zero`): the final node's `center` is an
    --       unconstrained record field (interior nodes get `cc ≠ 0` from `IsRecentering` at
    --       their own index; no clause exists at the final index).
    --  (O3) the (S6b)/(I-aug) threshold `ν.σ.wPrev ν.σ.Φ < ν.σ.h` — the ONLY realizer source
    --       in `Stage` is `hS6b`, gated by this inequality; it lives in `StageCore.prevIaug`,
    --       which `HistoryCoherent` does not carry for the final frame.
    -- CONVERSELY the three conditions SUFFICE (`recenterLiftSpec_of_eligible`, machine-checked):
    -- under the sign-off narrowing {σ.e = 1, center ≠ 0, wPrev Φ < h} this branch closes as
    --   `exact recenterLiftSpec_of_eligible _ he1 hcen hthr`
    -- and the whole unit is sorry-free. That triple (not `σ.e = 1` alone) is the complete
    -- D.10 eligibility the fallback must name.
    sorry

/-- Hence `polOM.liftOf` itself satisfies the spec at such nodes (choice reading): once a
realizer exists (`polOM_total`), `polOM.liftOf` unfolds to `Classical.choose` of that
existence, whose spec is the goal. Inherits `polOM_total`'s final-node obstruction. -/
theorem polOM_liftOf_spec {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
    {H : History p F} (hcoh : HistoryCoherent H) (hreal : Realizable H)
    (i : ℕ) (hi : i < H.nodes.length)
    (hrec : (H.nodes[i]'hi).species = ReadSpecies.recentering) :
    RecenterLiftSpec (H.nodes[i]'hi) ((polOM p F).liftOf (H.nodes[i]'hi)) := by
  classical
  have hex : ∃ tL : Polynomial ℤ_[p], RecenterLiftSpec (H.nodes[i]'hi) tL :=
    polOM_total hcoh hreal i hi hrec
  have hlift : (polOM p F).liftOf (H.nodes[i]'hi) = hex.choose := by
    simp only [polOM]
    exact dif_pos hex
  rw [hlift]
  exact hex.choose_spec

end LeanUrat.MovesJ
