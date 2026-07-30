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
  classical
  -- ## Lift facts (L3) and the guard's degree consequence
  obtain ⟨hmonΦ, hdegΦ⟩ := L3_liftMonic σ ψ g th.hg Φhat th.hlift
  have hΦne : Φhat ≠ 0 := hmonΦ.ne_zero
  have hdeg1 : 1 ≤ Φhat.natDegree := by
    rw [hdegΦ]
    exact Nat.mul_pos (by omega : 0 < σ.e * g) σ.hdeg
  have hΦnatlt : σ.Φ.natDegree < Φhat.natDegree := by
    rw [hdegΦ]
    exact lt_mul_of_one_lt_left σ.hdeg hEG
  have hΦlt : σ.Φ.degree < Φhat.degree := by
    rw [Polynomial.degree_eq_natDegree σ.hmonic.ne_zero,
      Polynomial.degree_eq_natDegree hΦne]
    exact_mod_cast hΦnatlt
  -- ## The child Bézout pair, P2-pinned at e′ = 1 (the (vii) split)
  obtain ⟨s', t', hbez', ht'0⟩ :
      ∃ s' t' : ℤ, (e' : ℤ) * s' + (h' : ℤ) * t' = 1 ∧ (e' = 1 → t' = 0) := by
    by_cases he1 : e' = 1
    · exact ⟨1, 0, by rw [he1]; push_cast; ring, fun _ => rfl⟩
    · refine ⟨Nat.gcdA e' h', Nat.gcdB e' h', ?_, fun h => absurd h he1⟩
      have hg := Nat.gcd_eq_gcd_ab e' h'
      rw [th.hcop] at hg
      exact_mod_cast hg.symm
  -- ## The lawful D.7(vi)-normalized residual carrier (S9w)
  obtain ⟨hexD, hwstrict⟩ := S9w_residualLaws σ hσ th s' t' hbez' ht'0
  obtain ⟨hR0, hRne, hRmul, hRadd, hRlt, hWjump, hRneg⟩ := hexD.choose_spec
  -- ## The childW plumbing (S2/S3/S5) + parent basics
  obtain ⟨hdevMin, hSMW⟩ := S2_childW σ Φhat hmonΦ hdeg1 e' h'
  have hw1 : σ.w 1 = 0 := by
    have h := σ.hwmul 1 1 one_ne_zero one_ne_zero
    rw [mul_one] at h
    omega
  obtain ⟨hwPhi, hK1c⟩ := S3_childK1 σ Φhat hmonΦ hdeg1 e' h' th.he' th.hh' hw1
  obtain ⟨hwmulc, hvalgrpc⟩ := S5_childValuation σ hσ th
  have hzbar : Polynomial.eval₂ σ.K.subtype (zbar : F) ψ = 0 := by
    have h := th.hroot
    rw [Polynomial.aeval_def, Polynomial.eval₂_map, Algebra.algebraMap_self,
      RingHom.id_comp] at h
    exact h
  -- ## The child ultrametric law (developments add slotwise; parent hwult per slot)
  have hwult : ∀ f g', f ≠ 0 → g' ≠ 0 → f + g' ≠ 0 →
      min (childW σ Φhat e' h' f) (childW σ Φhat e' h' g') ≤
        childW σ Φhat e' h' (f + g') := by
    intro f g' hf hg' hfg
    obtain ⟨Bf, Nf, hdf, hmf⟩ := hdevMin f hf
    obtain ⟨Bg, Ng, hdg, hmg⟩ := hdevMin g' hg'
    set N := max Nf Ng with hN
    -- the slotwise sum is a development of f + g' at length N
    have hsub_f : Finset.range Nf ⊆ Finset.range N := fun x hx =>
      Finset.mem_range.mpr (lt_of_lt_of_le (Finset.mem_range.mp hx) (le_max_left _ _))
    have hsub_g : Finset.range Ng ⊆ Finset.range N := fun x hx =>
      Finset.mem_range.mpr (lt_of_lt_of_le (Finset.mem_range.mp hx) (le_max_right _ _))
    have hsum_f : f = ∑ j ∈ Finset.range N, Bf j * Φhat ^ j := by
      rw [hdf.2.2]
      refine Finset.sum_subset hsub_f ?_
      intro j hjN hjNf
      rw [hdf.2.1 j (by simpa using hjNf), zero_mul]
    have hsum_g : g' = ∑ j ∈ Finset.range N, Bg j * Φhat ^ j := by
      rw [hdg.2.2]
      refine Finset.sum_subset hsub_g ?_
      intro j hjN hjNg
      rw [hdg.2.1 j (by simpa using hjNg), zero_mul]
    have hdevS : IsDevelopment Φhat (f + g') (fun j => Bf j + Bg j) N := by
      refine ⟨?_, ?_, ?_⟩
      · intro j
        exact lt_of_le_of_lt (Polynomial.degree_add_le _ _) (max_lt (hdf.1 j) (hdg.1 j))
      · intro j hj
        show Bf j + Bg j = 0
        rw [hdf.2.1 j (le_trans (le_max_left _ _) hj),
          hdg.2.1 j (le_trans (le_max_right _ _) hj), add_zero]
      · rw [hsum_f, hsum_g, ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun j _ => (add_mul (Bf j) (Bg j) (Φhat ^ j)).symm
    obtain ⟨hlow, jS, hjSN, hjSnz, hjSeq⟩ := hSMW (f + g') _ N hfg hdevS
    rw [hjSeq]
    -- per-slot case split on which side is present
    by_cases hBf : Bf jS = 0
    · have hBg : Bg jS ≠ 0 := by
        intro hBg
        exact hjSnz (by rw [hBf, hBg, add_zero])
      have hjNg : jS < Ng := by
        by_contra hge
        exact hBg (hdg.2.1 jS (le_of_not_gt hge))
      have hle := (hmg.1) jS hjNg hBg
      have hval : σ.w (Bf jS + Bg jS) = σ.w (Bg jS) := by rw [hBf, zero_add]
      calc min (childW σ Φhat e' h' f) (childW σ Φhat e' h' g')
          ≤ childW σ Φhat e' h' g' := min_le_right _ _
        _ ≤ (e' : ℤ) * σ.w (Bg jS) + (jS : ℤ) * (h' : ℤ) := hle
        _ = (e' : ℤ) * σ.w (Bf jS + Bg jS) + (jS : ℤ) * (h' : ℤ) := by rw [hval]
    · by_cases hBg : Bg jS = 0
      · have hjNf : jS < Nf := by
          by_contra hge
          exact hBf (hdf.2.1 jS (le_of_not_gt hge))
        have hle := (hmf.1) jS hjNf hBf
        have hval : σ.w (Bf jS + Bg jS) = σ.w (Bf jS) := by rw [hBg, add_zero]
        calc min (childW σ Φhat e' h' f) (childW σ Φhat e' h' g')
            ≤ childW σ Φhat e' h' f := min_le_left _ _
          _ ≤ (e' : ℤ) * σ.w (Bf jS) + (jS : ℤ) * (h' : ℤ) := hle
          _ = (e' : ℤ) * σ.w (Bf jS + Bg jS) + (jS : ℤ) * (h' : ℤ) := by rw [hval]
      · -- both slots present: the parent ultrametric law
        have hjNf : jS < Nf := by
          by_contra hge
          exact hBf (hdf.2.1 jS (le_of_not_gt hge))
        have hjNg : jS < Ng := by
          by_contra hge
          exact hBg (hdg.2.1 jS (le_of_not_gt hge))
        have hult := σ.hwult (Bf jS) (Bg jS) hBf hBg hjSnz
        have hlef := (hmf.1) jS hjNf hBf
        have hleg := (hmg.1) jS hjNg hBg
        have he'nn : (0 : ℤ) ≤ (e' : ℤ) := Int.natCast_nonneg e'
        rcases min_cases (σ.w (Bf jS)) (σ.w (Bg jS)) with ⟨hmin, hcmp⟩ | ⟨hmin, hcmp⟩
        · have : childW σ Φhat e' h' f ≤ (e' : ℤ) * σ.w (Bf jS + Bg jS) + (jS : ℤ) * (h' : ℤ) := by
            have h2 : σ.w (Bf jS) ≤ σ.w (Bf jS + Bg jS) := by rw [← hmin]; exact hult
            have h3 := mul_le_mul_of_nonneg_left h2 he'nn
            linarith
          exact le_trans (min_le_left _ _) this
        · have : childW σ Φhat e' h' g' ≤ (e' : ℤ) * σ.w (Bf jS + Bg jS) + (jS : ℤ) * (h' : ℤ) := by
            have h2 : σ.w (Bg jS) ≤ σ.w (Bf jS + Bg jS) := by rw [← hmin]; exact hult
            have h3 := mul_le_mul_of_nonneg_left h2 he'nn
            linarith
          exact le_trans (min_le_right _ _) this
  -- ## (S6b′): full scalars above the key weight, via the Moves final `L4_TRANSviii_b`
  have hS6b' : ∀ (ν : ℤ) (a : (↥(σ.nextField zbar))ˣ), σ.w Φhat < ν →
      ∃ B, B ≠ 0 ∧ inC Φhat B ∧ σ.w B = ν ∧
        hexD.choose.Rc B = LaurentPolynomial.C ((a : ↥(σ.nextField zbar))) *
          LaurentPolynomial.T (- t' * ν) := by
    intro ν a hν
    obtain ⟨B, hBc, hdig, hnz⟩ := L4_TRANSviii_b σ hσ.core ψ g th.hdeg th.hmonic th.hirr
      th.hne_z Φhat th.hlift zbar hzbar ν hν ((a : ↥(σ.nextField zbar)) : F)
      (SetLike.coe_mem _)
    have hane : ((a : ↥(σ.nextField zbar)) : F) ≠ 0 := by
      have := a.ne_zero
      exact fun h => this (Subtype.ext h)
    obtain ⟨hB0, hBw⟩ := hnz hane
    obtain ⟨c', hc'R, hc'F⟩ := hexD.choose.hS5' B hB0 hBc
    have hcs : (c' : ↥(σ.nextField zbar)) = (a : ↥(σ.nextField zbar)) := by
      apply Subtype.ext
      rw [hc'F, hdig]
    refine ⟨B, hB0, hBc, hBw, ?_⟩
    rw [hc'R, hcs, hBw]
  -- ## (S6a′): the coset-orbit realizers (V5 fixed-point coset form, blueprint §10
  -- Key Finding 2).  Above the threshold: hS6b′ with base b = 1 (exact scalars).
  -- Below (the strip): V7's obligation — V6(b)'s minimizing-slot base +
  -- TRANSviii_a conjunct 2 verbatim (the fenced V′-kernel discharge).
  have hS6a' : ∀ ν ∈ childWeightSet σ Φhat, ∃ b : (↥(σ.nextField zbar))ˣ,
      ∀ c : (↥(σ.nextField zbar))ˣ,
      ((c : ↥(σ.nextField zbar)) : F) ∈ σ.FQ →
      ∃ B, B ≠ 0 ∧ inC Φhat B ∧ σ.w B = ν ∧
        hexD.choose.Rc B
          = LaurentPolynomial.C ((c * b : (↥(σ.nextField zbar))ˣ) : ↥(σ.nextField zbar)) *
            LaurentPolynomial.T (- t' * ν) := by
    intro ν hν
    rcases lt_or_ge (σ.w Φhat) ν with hgt | hle
    · exact ⟨1, fun c _ => by rw [mul_one]; exact hS6b' ν c hgt⟩
    · -- BELOW-THRESHOLD STRIP (ν ≤ σ.w Φ̂): the V7 discharge — PROVED (S9a_final
      -- escalation, 2026-07-28). NOT the planned "V6(b) + TRANSviii_a conjunct 2
      -- verbatim" (that route is CIRCULAR: TRANSviii_a consumes a full child Stage σ'
      -- whose hS6a field IS this obligation). V7's executed proof is σ'-free: the
      -- parent (S6a) coset realizer ridden up the K1 minimizing slot (L2_strideRule,
      -- digit linear in the orbit scalar), pinned into Rc through the carrier's own
      -- hS5' (raw digPrime, mfun ≡ 0). Same kernel in Moves-lemma form:
      -- `Moves.L4_TRANSviii_c` (threshold-free).
      exact V7_stripDischarge σ hσ th s' t' hbez' ht'0 hexD.choose hexD.choose_spec ν hν
  -- ## The literal
  refine ⟨{
      e := e', h := h', s := s', t := t',
      he := th.he', hh := th.hh', hcop := th.hcop, hbez := hbez', he1t := ht'0,
      Φ := Φhat, hmonic := hmonΦ, hdeg := hdeg1,
      w := childW σ Φhat e' h',
      wPrev := σ.w,
      K := σ.nextField zbar, FQ := σ.FQ,
      hFQ_le := le_trans σ.hFQ_le (σ.le_nextField zbar),
      R := hexD.choose.Rc,
      hwmul := hwmulc,
      hwult := hwult,
      hvalgrp := hvalgrpc,
      hwΦ := hwPhi,
      hStretch := fun B hB hBc => L4_TRANSii σ Φhat e' h' _ hSMW B hB hBc,
      hR0 := hR0, hRne := hRne, hRmul := hRmul, hRadd := hRadd, hRlt := hRlt,
      hRΦ := hexD.choose.hRPhi,
      hK1 := by rw [hwPhi]; exact hK1c,
      hS5 := fun B hB hBc =>
        ⟨(hexD.choose.hS5' B hB hBc).choose, (hexD.choose.hS5' B hB hBc).choose_spec.1⟩,
      reps := σ.reps ++ [σ.Φ],
      hreps := fun ũ hũ => by
        rcases List.mem_append.mp hũ with h | h
        · exact ⟨(σ.hreps ũ h).1, lt_trans (σ.hreps ũ h).2 hΦlt⟩
        · rw [List.mem_singleton] at h
          subst h
          exact ⟨σ.hmonic.ne_zero, hΦlt⟩,
      Tvec := σ.Tvec.map (fun q => (q.1, s' * q.2)) ++ [(σ.Φ, s' * σ.t)],
      hTvec := by
        rw [List.map_append, List.map_map]
        simp only [Function.comp_def, List.map_cons, List.map_nil]
        rw [σ.hTvec],
      weightSet := childWeightSet σ Φhat,
      hWS := fun B hB hBc => ⟨B, hB, hBc, rfl⟩,
      hS6a := hS6a',
      hS6b := hS6b' }, ?_, ?_, ?_⟩
  · -- TransitionData: the construction records, all definitional on the literal
    exact { child_key := rfl, child_e := rfl, child_h := rfl,
            child_field := rfl, field_grow := σ.le_nextField zbar,
            child_base := rfl, child_wPrev := fun f => rfl, threshold := rfl,
            child_slotmin := hSMW, child_reps := rfl }
  · -- VertexPin: exactly the carrier's S5′ pinned shape (mfun ≡ 0)
    exact hexD.choose.hS5'
  · -- the childW tie: definitional on the literal
    exact fun f _ => rfl

end LeanUrat.HC1

#print axioms LeanUrat.HC1.S9a_stageLiteral
#print axioms LeanUrat.HC1.S9a_ungated_corner_refuted
#print axioms LeanUrat.HC1.S9a_corner_fails_guard
