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
N-2 RESTATEMENT (2026-07-28, sign-off round — §9 F-1 executed): `polOM_total` and
`polOM_liftOf_spec` gain the GUARDED hypothesis
`helig : i + 1 = H.nodes.length → D10Eligible (H.nodes[i]'hi)` (Defs N-2 addendum: the
complete D.10 eligibility triple {σ.e = 1, center ≠ 0, wPrev Φ < h}; MOVES 2583–2671).
The blueprint's pre-declared fallback (`σ.e = 1` alone) was INSUFFICIENT (escalation
necessity 2); necessity of all three legs + joint sufficiency are the machine-checked
lemmas below. Unit now SORRY-FREE (interior from coherence; final from the guard).
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

/-- POL-TOTALITY (L1 kernel-(a); RESTATED AT N-2, 2026-07-28 — §9 F-1's pre-analyzed
eligibility narrowing, sign-off executed): at every recentering node of a coherent
realizable history, a `RecenterLiftSpec` realizer exists — under the GUARDED hypothesis
`helig` naming the complete D.10 eligibility (`D10Eligible`, Defs N-2 addendum; MOVES
2583–2671) at the FINAL read only.

INTERIOR nodes (`i+1 < len`) close from coherence: `IsRecenteringCore.base` is literally
`RecenterLiftSpec ν ν.lift` — the guard is interior-invisible. The FINAL recentering node
was the machine-checked obstruction (the escalation records preserved below the proof);
`recenterLiftSpec_of_eligible` closes it from the guard. RUN-SIDE DISCHARGE (so the guard
is never mistaken for dead weight): under `ReadsOf`, clause (iv)'s final `LandingKey`
contains `RecenterLiftSpec ν ν.lift` at a final recentering — runs supply the realizer
outright and `D10Eligible` follows from the necessity lemmas. -/
theorem polOM_total {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
    {H : History p F} (hcoh : HistoryCoherent H) (hreal : Realizable H)
    (i : ℕ) (hi : i < H.nodes.length)
    (hrec : (H.nodes[i]'hi).species = ReadSpecies.recentering)
    (helig : i + 1 = H.nodes.length → D10Eligible (H.nodes[i]'hi)) :
    ∃ tL : Polynomial ℤ_[p], RecenterLiftSpec (H.nodes[i]'hi) tL := by
  obtain ⟨_hroot, _hslope, _hgam, htrans⟩ := hcoh
  by_cases hlast : i + 1 < H.nodes.length
  · -- INTERIOR recentering node: coherence records the transition, whose recentering branch
    -- (`IsRecenteringCore ν.σ (child).σ ν.center ν.lift`) unfolds — through `.base` — to the
    -- four `RecenterLiftSpec` conjuncts at `tL := ν.lift`.
    have hrc := (htrans i hlast).1 hrec
    obtain ⟨_, _, _, hinC, hne, hw, hR, _⟩ := hrc.base
    exact ⟨(H.nodes[i]'hi).lift, hinC, hne, hw, hR⟩
  · -- FINAL recentering node: the D10Eligible guard fires; joint sufficiency is
    -- `recenterLiftSpec_of_eligible` (machine-checked above). The pre-restatement
    -- obstruction records (both escalation passes) are preserved verbatim below.
    obtain ⟨he1, hcen, hthr⟩ := helig (by omega)
    exact recenterLiftSpec_of_eligible _ he1 hcen hthr

/- PRE-RESTATEMENT ESCALATION RECORDS (historical; the N-2 guard resolves them):
   FIRST PASS — `recenterLiftSpec_forces_frame_e_one` shows any realizer forces `ν.σ.e = 1`
   (D.10 eligibility). Coherence supplies `ν.σ.e = 1` ONLY through the recentering branch of
   its transition conjunct, guarded by `i+1 < len` (unavailable at the final read); the
   transition INTO the node sets `ν.σ.e` via `TransitionData.child_e` to the PREDECESSOR's
   read index — an `e = 2` increment predecessor is legal, coherent, realizable, and kills
   every realizer (necessity). Interior copies of the configuration are coherence-INFEASIBLE;
   ONLY the final node escapes — the identical last-node freedom refuted at U1 (N-1).
   SECOND PASS (obstruction SHARPENED — `σ.e = 1` alone is NOT enough):
    (O1) frame eligibility `ν.σ.e = 1` — necessity machine-checked; unavailable when the
         predecessor is a root/increment with read `e ≥ 2`.
    (O2) `ν.center ≠ 0` — necessity machine-checked (`recenterLiftSpec_forces_center_ne_zero`);
         the final node's `center` is an unconstrained record field.
    (O3) the (S6b)/(I-aug) threshold `ν.σ.wPrev ν.σ.Φ < ν.σ.h` — the ONLY realizer source in
         `Stage` is `hS6b`, gated by this inequality (`StageCore.prevIaug`, which
         `HistoryCoherent` does not carry for the final frame).
   The triple {σ.e = 1, center ≠ 0, wPrev Φ < h} = `D10Eligible` is the complete D.10
   eligibility; necessity of each leg + joint sufficiency machine-checked in this file. -/

/-- Hence `polOM.liftOf` itself satisfies the spec at such nodes (choice reading; carries
the N-2 `helig` guard through): once a realizer exists (`polOM_total`), `polOM.liftOf`
unfolds to `Classical.choose` of that existence, whose spec is the goal. -/
theorem polOM_liftOf_spec {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
    {H : History p F} (hcoh : HistoryCoherent H) (hreal : Realizable H)
    (i : ℕ) (hi : i < H.nodes.length)
    (hrec : (H.nodes[i]'hi).species = ReadSpecies.recentering)
    (helig : i + 1 = H.nodes.length → D10Eligible (H.nodes[i]'hi)) :
    RecenterLiftSpec (H.nodes[i]'hi) ((polOM p F).liftOf (H.nodes[i]'hi)) := by
  classical
  have hex : ∃ tL : Polynomial ℤ_[p], RecenterLiftSpec (H.nodes[i]'hi) tL :=
    polOM_total hcoh hreal i hi hrec helig
  have hlift : (polOM p F).liftOf (H.nodes[i]'hi) = hex.choose := by
    simp only [polOM]
    exact dif_pos hex
  rw [hlift]
  exact hex.choose_spec

end LeanUrat.MovesJ
