/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.HC1.V10_transportWindow
import LeanUrat.HC1.V11_minimalCore

/-!
# HC2.HK03_stageTransHypEmpty — HK-03: `StageTransHypOld`'s steep perimeter is EMPTY

Bridge campaign BP2 (`lean/notes/BRIDGE_BP2_HC2K1_2026-07-30.md`, Block K, unit HK-03).
E-PHASE SKELETON: statement + `sorry` body; P-phase proves (routine-opus, est. ~60 lines).

**Unit HK-03 `stageTransHyp_steep_empty`**.

INFORMAL STATEMENT (blueprint §3.1(d)): `StageTransHypOld p F` (HC2/Defs l.200 — the (OLD)
configuration: read-pair lift shape + NEXT-pair steepness `IAug` at the SAME `(e', h')`,
concluding `TransitionCoreL` at that pair + the s/t ties) implies that NO `StageCoreL`
stage admits ANY lawful `(ψ, g, z̄, e', h', s', t', Φ̂)` read instance with `IsReadLift`,
`IAug`, and `2 ≤ e'·g` — the hypothesis is conditionally FALSE at the steep perimeter its
consumers (U17a/U17c) need.

SKETCH (blueprint HK-03): apply the hypothesis at the given instance, get `σ'` +
`TransitionCoreL σ σ' Φ̂ e' h'` with the ties; `V10_forcedKeyWeight` forces
`h' = e'²·g·σ.h`; `σ.w Φ̂ = e'·g·σ.h` for the read lift (the steepness computation,
V10's `hτbound` pattern); then `IAug` reads `h' > e'·σ.w Φ̂ = e'²·g·σ.h` — strict —
contradiction with the forced equality: `False`.

TRANSCRIPTION RESOLUTIONS (recorded per the E-phase charge):
* the blueprint display's `∃ (ψ g e' h' s' t' Φ̂), (binders) ∧ …` gloss is transcribed as
  `StageTransHypOld`'s own binder telescope, which includes the recorded residue root
  `z̄ : Fˣ` with `eval₂ σ.K.subtype z̄ ψ = 0` — `zbar` is therefore ADDED to the ∃-list
  (without a root the hypothesis cannot fire; minimal resolution);
* the Bézout-range clause is copied byte-faithfully from `StageTransHypOld`
  (`0 ≤ t' ∧ t' < e'`).

ARCHIVAL DISCIPLINE (REVISION 2, finding 7): this theorem is proved PRE-WAVE against the
CURRENT `StageTransHypOld`; the HK-06 migration wave renames the subject to
`StageTransHypOld` and mechanically re-points this file — the theorem is the permanent
refuted-shape record of WHY the re-key happened, and is NEVER re-interpreted against the
re-keyed definition.

deps: HK-02 patterns (`HC1/V11_minimalCore.lean`); supply: `V10_forcedKeyWeight`
(`HC1/V10_transportWindow.lean`, PROVED Lean-core).
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 400000

namespace LeanUrat.MovesJ

open Polynomial LeanUrat.Moves

/-- **HK-03 `stageTransHyp_steep_empty`** — the emptiness record: under `StageTransHypOld p F`
(the (OLD) same-pair configuration), no `StageCoreL` stage admits a lawful steep read
instance — every `(ψ, g, z̄, e', h', s', t', Φ̂)` with the `StageTransHypOld` binder laws,
`IsReadLift`, `IAug`, and `2 ≤ e'·g` is refuted.  Proof route: fire the hypothesis, then
`V10_forcedKeyWeight` + the read-lift key-slot computation force `h' = e'²·g·σ.h` while
`IAug` demands `h' > e'²·g·σ.h`.
[Blueprint BP2 HK-03; deps: HK-02 patterns, `V10_forcedKeyWeight`; sketch + the recorded
∃-list resolution (zbar included) in the module header.] -/
theorem stageTransHyp_steep_empty {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
    (hst : StageTransHypOld p F) :
    ∀ σ : Stage p F, StageCoreL σ →
      ¬ ∃ (ψ : Polynomial ↥σ.K) (g : ℕ) (zbar : Fˣ) (e' h' : ℕ) (s' t' : ℤ)
          (Φhat : Polynomial ℤ_[p]),
        (ψ.Monic ∧ ψ.natDegree = g ∧ Irreducible ψ ∧ ψ ≠ Polynomial.X ∧ 1 ≤ g) ∧
        Polynomial.eval₂ σ.K.subtype ((zbar : Fˣ) : F) ψ = 0 ∧
        (1 ≤ e' ∧ 1 ≤ h' ∧ Nat.gcd e' h' = 1 ∧
          (e' : ℤ) * s' + (h' : ℤ) * t' = 1 ∧ 0 ≤ t' ∧ t' < (e' : ℤ)) ∧
        IsReadLift σ ψ g e' h' Φhat ∧ IAug σ Φhat e' h' ∧ 2 ≤ e' * g := by
  intro σ hσ
  rintro ⟨ψ, g, zbar, e', h', s', t', Φhat, ⟨hmon, hdeg, hirr, hne, hg1⟩, hroot,
    ⟨he', hh', hcop, hbez, ht0, htlt⟩, hlift, hIAug, hEG⟩
  -- fire the (OLD) transition hypothesis at this instance
  obtain ⟨σ', hΦ, he_tie, hh_tie, hs_tie, ht_tie, hTC, hσ'⟩ :=
    hst σ hσ ψ g hmon hdeg hirr hne hg1 zbar hroot e' h' s' t' he' hh' hcop hbez ⟨ht0, htlt⟩
      Φhat hlift hIAug
  have hcw := hTC.base.child_wPrev
  have hΦne : σ.Φ ≠ 0 := σ.hmonic.ne_zero
  have hh0 : (0 : ℤ) ≤ (h' : ℤ) := Int.natCast_nonneg _
  have he'Z : (1 : ℤ) ≤ (e' : ℤ) := by exact_mod_cast he'
  have hIAug' : (h' : ℤ) > (e' : ℤ) * σ.w Φhat := hIAug
  -- crude lower bound: `min (e'·g·σ.h) h' ≤ σ.w Φ̂` (the read-lift τ-slots each weigh ≥ h')
  have hlb : min ((e' : ℤ) * (g : ℤ) * (σ.h : ℤ)) (h' : ℤ) ≤ σ.w Φhat := by
    obtain ⟨tt, htt0, httk, hPhi⟩ := hlift
    set τ : Polynomial ℤ_[p] := ∑ k ∈ Finset.range g, tt k * σ.Φ ^ (e' * k) with hτdef
    have hpowne : σ.Φ ^ (e' * g) ≠ 0 := pow_ne_zero _ hΦne
    have hwpow : σ.w (σ.Φ ^ (e' * g)) = (e' : ℤ) * (g : ℤ) * (σ.h : ℤ) := by
      rw [ResVal.w_pow σ σ.Φ hΦne (e' * g), σ.hwΦ]; push_cast; ring
    by_cases hτ0 : τ = 0
    · have hval : σ.w Φhat = (e' : ℤ) * (g : ℤ) * (σ.h : ℤ) := by
        rw [hPhi, hτ0, add_zero, hwpow]
      rw [hval]; exact min_le_left _ _
    · have hτbound : (h' : ℤ) ≤ σ.w τ := by
        refine ResVal.w_sum_ge σ (Finset.range g) _ (h' : ℤ) ?_ (by rw [← hτdef]; exact hτ0)
        intro k hk htermne
        have hkG : k < g := Finset.mem_range.mp hk
        have htk : tt k ≠ 0 := fun h0 => htermne (by rw [h0, zero_mul])
        have hψk : ψ.coeff k ≠ 0 := fun h0 => htk (htt0 k h0)
        obtain ⟨-, -, htkw, -⟩ := httk k hkG hψk
        rw [σ.hwmul _ _ htk (pow_ne_zero _ hΦne), htkw, ResVal.w_pow σ σ.Φ hΦne (e' * k), σ.hwΦ]
        have hGk1 : (1 : ℤ) ≤ (g : ℤ) - (k : ℤ) := by
          have : (k : ℤ) < (g : ℤ) := by exact_mod_cast hkG
          omega
        have hp1 : (0 : ℤ) ≤ (h' : ℤ) * (((g : ℤ) - (k : ℤ)) - 1) := mul_nonneg hh0 (by linarith)
        have hp2 : (0 : ℤ) ≤ ((e' * k : ℕ) : ℤ) * (σ.h : ℤ) := by positivity
        push_cast at hp2 ⊢
        nlinarith [hp1, hp2]
      have hΦhatne : Φhat ≠ 0 := by rw [← hΦ]; exact σ'.hmonic.ne_zero
      have hne0 : σ.Φ ^ (e' * g) + τ ≠ 0 := by rw [← hPhi]; exact hΦhatne
      have hult := σ.hwult (σ.Φ ^ (e' * g)) τ hpowne hτ0 hne0
      rw [hwpow, ← hPhi] at hult
      calc min ((e' : ℤ) * (g : ℤ) * (σ.h : ℤ)) (h' : ℤ)
          ≤ min ((e' : ℤ) * (g : ℤ) * (σ.h : ℤ)) (σ.w τ) := min_le_min (le_refl _) hτbound
        _ ≤ σ.w Φhat := hult
  -- IAug forces `h' > e'·min`; the two min-cases each refute
  have key : (h' : ℤ) > (e' : ℤ) * min ((e' : ℤ) * (g : ℤ) * (σ.h : ℤ)) (h' : ℤ) :=
    lt_of_le_of_lt (mul_le_mul_of_nonneg_left hlb (by positivity)) hIAug'
  rcases le_total ((e' : ℤ) * (g : ℤ) * (σ.h : ℤ)) (h' : ℤ) with hle | hle
  · -- min = e'·g·σ.h ⟹ truly steep ⟹ HK-02's minimal core fires
    rw [min_eq_left hle] at key
    have hsteep : (e' : ℤ) * (e' : ℤ) * (g : ℤ) * (σ.h : ℤ) < (h' : ℤ) := by nlinarith [key]
    exact LeanUrat.HC1.V11_minimalIncompat σ σ' e' h' g ψ Φhat hsteep hEG hlift hΦ
      he_tie hh_tie hcw
  · -- min = h' ⟹ h' > e'·h' ≥ h', immediate contradiction
    rw [min_eq_right hle] at key
    have hle2 : (h' : ℤ) ≤ (e' : ℤ) * (h' : ℤ) := le_mul_of_one_le_left hh0 he'Z
    linarith [key, hle2]

end LeanUrat.MovesJ
