/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.HC1.V10_transportWindow
import LeanUrat.Moves.ResVal

/-!
# HC2.HK05_countermodelGate — HK-05: the COUNTERMODEL GATE on the (NEW) clause set

Bridge campaign BP2 (`lean/notes/BRIDGE_BP2_HC2K1_2026-07-30.md`, Block K, unit HK-05;
adjudications: `lean/notes/BRIDGE_ADJUDICATIONS_2026-07-30.md`, BP2/Q1 — candidate (S-a)
ratified, GATED by HK-05 + HK-22).

**THE CHARGE** (unit spec, quoted): "run the V10/V11 refutation machinery against the
ratified clause set at a steep instance (e = 1, g = 2, h★ = 3 over a (1,1)-Gauss shape),
against the STAGED copy: the derivation must STOP (report the exact blocking clause), NOT
close. Deliverable: a scratch file + record; if False closes, HK-01 REOPENS
(stop-the-line). Runs BEFORE HK-06."

## ⚠ STAGING DISPOSITION (read before consuming)

* HK-04's staged copy (`HC2/StagingRegrade.lean`) is NOT yet on disk at gate time
  (2026-07-30; no `RegradeOf` token exists anywhere under `lean/LeanUrat/`). This file
  therefore carries its OWN staged copy `StagedRegradeOf` of the §3.1(c) display's core
  clause list, byte-per the display (`RegradeOf σ ν σV` pins
  `σV.Φ = σ.Φ ∧ σV.e = ν.e ∧ σV.h = ν.h ∧ σV.K = σ.K ∧ σV.FQ = σ.FQ ∧ σV.reps = σ.reps ∧
  (∀ f, σV.wPrev f = σ.w f) ∧ IsSlotMinWeight σV.w σ.Φ ν.e ν.h σ.w`).  STAGING — deleted
  by the HK-06 wave; when HK-04 lands, either hoist this def there or re-point these
  theorems (mechanical).
* HK-01's ratified residual-law clause list (the D.7(i)–(v) σV.R ties at the READ's
  Bézout positions) does NOT yet exist; those clauses are OMITTED here.  Direction of
  the omission: extra clauses only ADD refutation power, so the STALL certified below is
  conditional on the ratified residual clauses not opening a NEW residual-position clash
  route (they constrain σV.R, which the V10/V11 machinery reaches only through the
  `hRlt`/`hRadd` entries blocked in `hk05_find2_residual_entries_blocked`).  RE-RUN
  TRIGGER: when HK-01's package lands, re-run this gate against the full clause list.
* The steepening datum is GRANTED to the refuter in its strongest form — `IAug σV Φ̂ e' h'`
  at the NEXT pair — although the (NEW) leg records only the strict slope-steepening
  clause (§3.2 item 1: "no literal IAug clause").  Conservative for a stall verdict.

## THE GATE VERDICT (2026-07-30): the derivation STOPS — the statement survives

The V10/V11 refutation machinery (`V10_forcedKeyWeight` → `V10_readTransition_incompatible`,
and V11's 5-clause core, whose hypothesis shape is forcedKeyWeight minus slot-min plus
`child_h`) is run against the staged (NEW) record at the charged steep instance
(read pair (e★, h★) = (1, 3), g = 2, over a (1,1)-Gauss parent σ: σ.h = 1).  Every
instantiation route is BLOCKED, each at a compiled clause:

1. **CONTROL ARM** (`hk05_machinery_fires_on_OLD`): at the SAME instance the machinery
   fires on the (OLD) keying (TransitionCoreL at the read pair over σ.w + the OLD s/t
   ties) — False closes through the PROVED `V10_readTransition_incompatible`.  The
   instance is genuinely inside the refuted perimeter (`hk05_instance_truly_steep`:
   it satisfies V11's truly-steep inequality h★ > e★²·g·σ.h, i.e. 3 > 2).
2. **THE PRIMARY BLOCKING CLAUSE** (`hk05_hlift_blocked`): the direct re-run at the
   (NEW) STEP-2 transition (σV → σ' at the next pair (e', h')) is IMPOSSIBLE — the
   machinery's entry hypothesis `hlift : IsReadLift σV ψV g' e' h' Φ̂` (the read-lift
   slot weights keyed at the SAME pair as the transition — consumed by BOTH
   `V10_forcedKeyWeight` and `V11_minimalIncompat`) is UNSATISFIABLE against the staged
   record together with IAug: the recorded lift is σV-equal-weight (frame-pair shape,
   every Φ̂-slot at σV-weight 6), so any transition-pair read-lift rendering forces
   h' ∈ {3, 6} while IAug forces h' > 6e' ≥ 6.  The (NEW) keying DECOUPLES the lift
   pair from the transition pair — exactly the repair's design content.
3. **The OLD-shape re-instantiation** (`hk05_oldshape_hcw_blocked`): re-running the
   machinery at (σ, σ') is blocked at `hcw : ∀ x, σ'.wPrev x = σ.w x` — the (NEW)
   record's `child_wPrev` lands on σV.w, and σV.w σ.Φ = 3 ≠ 1 = σ.w σ.Φ; the clause is
   REFUTED, not merely unsupplied.  (`hce`/`hslot`/the s/t ties are likewise re-keyed.)
4. **The STEP-1 re-instantiation** (`hk05_step1_regrade_blocked`): running the machinery
   on the regrade σ → σV is blocked at the non-corner perimeter `hEG : 2 ≤ e·g` — the
   regrade is key-preserving (`σV.Φ = σ.Φ`), and any read lift landing ON σ.Φ has
   e·g = 1 (degree computation).
5. **Finding-2's residual-clash route** (`hk05_find2_residual_entries_blocked`): at the
   staged record the child weighs the two Φ̂-development parts EQUALLY
   (σ'.w(σ.Φ²) = 6e' = σ'.w(Φ̂ − σ.Φ²)) while the key is STRICTLY heavier
   (σ'.w Φ̂ = h' > 6e') — so `hRlt`'s entry (strict slot inequality) and `hRadd`'s entry
   (sum weight = slot weight) BOTH fail: no residual law computes σ'.R Φ̂ from the slots.
   This is the genuine cancellation (ψ-divisibility) configuration — D.7's hypothesis
   class, the S9-consistent carrier ("S9's genuine transitions are untouched", V10
   header).  NOTE the tie is FORCED, not lucky: with unequal slot weights the two-sided
   ultrametric argument would pin σ'.w Φ̂ to the minimum, clashing with IAug.

**False does NOT close: HK-01 does NOT reopen.**  Consequence for the pending
adjudication (BP2/Q1, the HK-06 wave): pre-gate (g2) of HK-06 is GREEN; the wave still
waits on (g1) the ratified HK-01 package (incl. Q2-extension/Q5/Q9 rulings, now
logic-dictates per the 2026-07-30 authority update) and (g3) HK-21 (the staged 2-node
instance — the CONSISTENCY side, which this stall gate deliberately does not claim).

moves_ref: §B2-DEF D.7 head (next-side keying); BP2 §3.1(b)–(d) (the off-by-one and the
(NEW) display); V10 header findings 1–2.
deps: HK-02 (V11's clause shape, `HC1/V11_minimalCore.lean` — NOT imported: it is a
sorried E-phase skeleton; its hypothesis set is blocked by the same `hlift` certificate),
`HC1/V10_transportWindow.lean` (PROVED machinery, imported for the control arm).
ZERO axioms; zero sorry; `#print axioms` tail below.
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.show false

namespace LeanUrat.MovesJ

open Polynomial LeanUrat.Moves LeanUrat.MovesC

section HK05

variable {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]

/-- **STAGED copy of `RegradeOf`'s core clause list** [HK-05 STAGING — HK-04's
`HC2/StagingRegrade.lean` was not on disk at gate time; DELETED BY THE HK-06 WAVE, whose
compiled def goes into MovesC/Defs per §3.1(c) LAYERING].  Byte-per the BP2 §3.1(c)
display.  The D.7(i)–(v) residual-law clauses (σV.R ties) are HK-01-package content, NOT
YET RATIFIED — omitted, recorded as this gate's perimeter (module header). -/
def StagedRegradeOf (σ : Stage p F) (ν : Node p F) (σV : Stage p F) : Prop :=
  σV.Φ = σ.Φ ∧ σV.e = ν.e ∧ σV.h = ν.h ∧ σV.K = σ.K ∧ σV.FQ = σ.FQ ∧
  σV.reps = σ.reps ∧ (∀ f, σV.wPrev f = σ.w f) ∧ IsSlotMinWeight σV.w σ.Φ ν.e ν.h σ.w

/- [SYN2-S1 SWEEP-1, 2026-07-31] ResVal.w_one/ResVal.w_pow DELETED — single proof
source `Moves/ResVal.lean` (α-identical; the SYN-E0 concurrent-agent hold on this
file is lifted, per P2-C1); uses re-pointed to ResVal.w_one/w_pow. -/

/-- The τ-part of any read lift has degree `< e·g·deg Φ` (V10's `hτdeg` pattern,
extracted; only the degree facts of the slot coefficients are consumed). -/
private lemma hk05_sum_degree_lt (σ : Stage p F) (e g : ℕ) (he : 1 ≤ e)
    (tt : ℕ → Polynomial ℤ_[p])
    (hdegk : ∀ k, k < g → (tt k).degree < σ.Φ.degree) :
    (∑ k ∈ Finset.range g, tt k * σ.Φ ^ (e * k)).degree
      < ((e * g * σ.Φ.natDegree : ℕ) : WithBot ℕ) := by
  have hΦne : σ.Φ ≠ 0 := σ.hmonic.ne_zero
  refine lt_of_le_of_lt (Polynomial.degree_sum_le _ _) ?_
  rw [Finset.sup_lt_iff (WithBot.bot_lt_coe _)]
  intro k hk
  have hkG : k < g := Finset.mem_range.mp hk
  by_cases htk : tt k = 0
  · rw [htk, zero_mul, Polynomial.degree_zero]; exact WithBot.bot_lt_coe _
  · have htermne : tt k * σ.Φ ^ (e * k) ≠ 0 := mul_ne_zero htk (pow_ne_zero _ hΦne)
    refine (Polynomial.natDegree_lt_iff_degree_lt htermne).mp ?_
    rw [Polynomial.natDegree_mul htk (pow_ne_zero _ hΦne), Polynomial.natDegree_pow]
    have httdeg : (tt k).natDegree < σ.Φ.natDegree :=
      Polynomial.natDegree_lt_natDegree htk (hdegk k hkG)
    have h1 : e * k + 1 ≤ e * g := by
      have hEk : e * k + 1 ≤ e * (k + 1) := by
        rw [Nat.mul_succ]; exact Nat.add_le_add_left he (e * k)
      exact le_trans hEk (Nat.mul_le_mul_left e hkG)
    have hb : σ.Φ.natDegree + e * k * σ.Φ.natDegree ≤ e * g * σ.Φ.natDegree := by
      have h2 : (e * k + 1) * σ.Φ.natDegree ≤ (e * g) * σ.Φ.natDegree :=
        Nat.mul_le_mul_right σ.Φ.natDegree h1
      calc σ.Φ.natDegree + e * k * σ.Φ.natDegree
          = (e * k + 1) * σ.Φ.natDegree := by ring
        _ ≤ e * g * σ.Φ.natDegree := h2
    exact lt_of_lt_of_le (Nat.add_lt_add_right httdeg _) hb

/-- Any read lift `Φ̂` over `σ` is monic of degree `e·g·deg Φ` (the shared degree
bookkeeping; consumed on BOTH the recorded and the attempted side). -/
private lemma hk05_lift_monic_natDegree (σ : Stage p F) (ψ : Polynomial ↥σ.K)
    (g e h : ℕ) (he : 1 ≤ e) (Φhat : Polynomial ℤ_[p])
    (hl : IsReadLift σ ψ g e h Φhat) :
    Φhat.Monic ∧ Φhat.natDegree = e * g * σ.Φ.natDegree := by
  obtain ⟨tt, htt0, httk, hPhi⟩ := hl
  have hΦne : σ.Φ ≠ 0 := σ.hmonic.ne_zero
  have hdegk : ∀ k, k < g → (tt k).degree < σ.Φ.degree := by
    intro k hkG
    by_cases hψk : ψ.coeff k = 0
    · rw [htt0 k hψk, Polynomial.degree_zero]
      exact Ne.bot_lt (fun hbot => hΦne (Polynomial.degree_eq_bot.mp hbot))
    · exact (httk k hkG hψk).2.1
  have hτdeg := hk05_sum_degree_lt σ e g he tt hdegk
  have hpowne : σ.Φ ^ (e * g) ≠ 0 := pow_ne_zero _ hΦne
  have hdegpow : (σ.Φ ^ (e * g)).degree = ((e * g * σ.Φ.natDegree : ℕ) : WithBot ℕ) := by
    rw [Polynomial.degree_eq_natDegree hpowne, Polynomial.natDegree_pow]
  have hpowmon : (σ.Φ ^ (e * g)).Monic := σ.hmonic.pow _
  have hmon : Φhat.Monic := by
    rw [hPhi]
    exact hpowmon.add_of_left (by rw [hdegpow]; exact hτdeg)
  refine ⟨hmon, ?_⟩
  have hdeg : Φhat.degree = ((e * g * σ.Φ.natDegree : ℕ) : WithBot ℕ) := by
    rw [hPhi,
      Polynomial.degree_add_eq_left_of_degree_lt (by rw [hdegpow]; exact hτdeg), hdegpow]
  exact Polynomial.natDegree_eq_of_degree_eq_some hdeg

/-- `ψ.coeff 0 ≠ 0` at the gate instance (g = 2): irreducibility + monicity + degree 2
exclude the `X ∣ ψ` case (V10's derivation, keyed to the Node laws). -/
private lemma hk05_psi0_ne (ν : Node p F) (hνg : ν.g = 2) : ν.ψ.coeff 0 ≠ 0 := by
  intro h0
  obtain ⟨u, hu⟩ := Polynomial.X_dvd_iff.mpr h0
  rcases ν.hψirr.isUnit_or_isUnit hu with hX | hUnit
  · exact Polynomial.not_isUnit_X hX
  · obtain ⟨c, hc⟩ := Polynomial.isUnit_iff.mp hUnit
    have hcne : c ≠ 0 := by
      intro hc0
      apply ν.hψmonic.ne_zero
      rw [hu, ← hc.2, hc0, map_zero, mul_zero]
    have hdeg2 : ν.ψ.natDegree = 2 := by rw [ν.hψdeg, hνg]
    rw [hu, ← hc.2,
      Polynomial.natDegree_mul Polynomial.X_ne_zero (by simpa using hcne)] at hdeg2
    simp [Polynomial.natDegree_X, Polynomial.natDegree_C] at hdeg2

/-- **The recorded-side computations at the gate instance** (shared supply): at the
staged regrade of the recorded read ((e★, h★) = (1, 3), g = 2), the recorded lift is
σV-EQUAL-WEIGHT — `Φ̂` is monic of degree `2·deg Φ`, its τ-part `Φ̂ − Φ²` is nonzero of
σV-weight EXACTLY 6 (every slot of the recorded lift weighs 6 at σV: the frame-pair
shape), coefficient-spaced for the child key, and `σV.w Φ̂ ≥ 6`. -/
private lemma hk05_recorded (ν : Node p F) (hνe : ν.e = 1) (hνh : ν.h = 3) (hνg : ν.g = 2)
    (σV : Stage p F) (hreg : StagedRegradeOf ν.σ ν σV)
    (Φhat : Polynomial ℤ_[p]) (hlift : IsNodeLift ν Φhat) :
    Φhat.Monic ∧ Φhat.natDegree = 2 * ν.σ.Φ.natDegree ∧
      Φhat - ν.σ.Φ ^ 2 ≠ 0 ∧
      σV.w (Φhat - ν.σ.Φ ^ 2) = 6 ∧
      (Φhat - ν.σ.Φ ^ 2).degree < Φhat.degree ∧
      (6 : ℤ) ≤ σV.w Φhat := by
  obtain ⟨hVΦ, hVe, hVh, -, -, -, hVwPrev, -⟩ := hreg
  rw [hνe] at hVe
  rw [hνh] at hVh
  have hΦne : ν.σ.Φ ≠ 0 := ν.σ.hmonic.ne_zero
  have hψ0 := hk05_psi0_ne ν hνg
  have hlift' : IsReadLift ν.σ ν.ψ 2 1 3 Φhat := by
    have h := (isNodeLift_iff ν Φhat).mp hlift
    rw [hνe, hνh, hνg] at h
    exact h
  obtain ⟨mon, hdeg⟩ := hk05_lift_monic_natDegree ν.σ ν.ψ 2 1 3 (le_refl 1) Φhat hlift'
  rw [(by norm_num : 1 * 2 * ν.σ.Φ.natDegree = 2 * ν.σ.Φ.natDegree)] at hdeg
  obtain ⟨tt, htt0, httk, hPhi⟩ := hlift'
  have htt0ne : tt 0 ≠ 0 := (httk 0 (by norm_num) hψ0).1
  -- the τ-part is the two recorded τ-slots
  have hτ : Φhat - ν.σ.Φ ^ 2 = tt 0 + tt 1 * ν.σ.Φ := by
    rw [hPhi]
    simp [Finset.sum_range_succ]
  -- τ ≠ 0 (degree separation of the two slots)
  have hτne : Φhat - ν.σ.Φ ^ 2 ≠ 0 := by
    rw [hτ]
    intro h0
    by_cases ht1 : tt 1 = 0
    · rw [ht1, zero_mul, add_zero] at h0; exact htt0ne h0
    · have hd0 : (tt 0).degree < ν.σ.Φ.degree := (httk 0 (by norm_num) hψ0).2.1
      have h1 : tt 0 = -(tt 1 * ν.σ.Φ) := eq_neg_of_add_eq_zero_left h0
      have h2 : (tt 0).degree = (tt 1).degree + ν.σ.Φ.degree := by
        rw [h1, Polynomial.degree_neg, Polynomial.degree_mul]
      have h3 : ν.σ.Φ.degree ≤ (tt 0).degree := by
        rw [h2]
        calc ν.σ.Φ.degree = 0 + ν.σ.Φ.degree := (zero_add _).symm
          _ ≤ (tt 1).degree + ν.σ.Φ.degree :=
              add_le_add (Polynomial.zero_le_degree_iff.mpr ht1) le_rfl
      exact absurd hd0 (not_lt.mpr h3)
  -- σV-weights of the recorded slots (hStretch at σV.e = 1 through σV.wPrev = σ.w)
  have hkΦ : σV.w σV.Φ = 3 := by
    rw [σV.hwΦ, hVh]; norm_num
  have hw0 : σV.w (tt 0) = 6 := by
    have hin : inC σV.Φ (tt 0) := by
      show (tt 0).degree < σV.Φ.degree
      rw [hVΦ]
      exact (httk 0 (by norm_num) hψ0).2.1
    rw [σV.hStretch (tt 0) htt0ne hin, hVe, hVwPrev, (httk 0 (by norm_num) hψ0).2.2.1]
    norm_num
  have hw1 : ν.ψ.coeff 1 ≠ 0 → σV.w (tt 1) = 3 := by
    intro hc1
    have h1 := httk 1 (by norm_num) hc1
    have hin : inC σV.Φ (tt 1) := by
      show (tt 1).degree < σV.Φ.degree
      rw [hVΦ]
      exact h1.2.1
    rw [σV.hStretch (tt 1) h1.1 hin, hVe, hVwPrev, h1.2.2.1]
    norm_num
  -- the K1 development of τ at σV's key
  set Bτ : ℕ → Polynomial ℤ_[p] := fun j => if j = 0 then tt 0 else if j = 1 then tt 1 else 0
    with hBτ
  have hdev : IsDevelopment σV.Φ (Φhat - ν.σ.Φ ^ 2) Bτ 2 := by
    refine ⟨?_, ?_, ?_⟩
    · intro j
      simp only [hBτ]
      split_ifs with h1 h2
      · rw [hVΦ]; exact (httk 0 (by norm_num) hψ0).2.1
      · rw [hVΦ]
        by_cases hc1 : ν.ψ.coeff 1 = 0
        · rw [htt0 1 hc1, Polynomial.degree_zero]
          exact Ne.bot_lt (fun hbot => hΦne (Polynomial.degree_eq_bot.mp hbot))
        · exact (httk 1 (by norm_num) hc1).2.1
      · rw [Polynomial.degree_zero]
        exact Ne.bot_lt (fun hbot => by
          rw [hVΦ] at hbot
          exact hΦne (Polynomial.degree_eq_bot.mp hbot))
    · intro j hj
      have hj0 : j ≠ 0 := by omega
      have hj1 : j ≠ 1 := by omega
      simp [hBτ, hj0, hj1]
    · rw [hτ, hVΦ]
      simp [hBτ, Finset.sum_range_succ]
  obtain ⟨-, j₀, hj₀2, hj₀ne, hj₀eq⟩ := σV.hK1 (Φhat - ν.σ.Φ ^ 2) Bτ 2 hτne hdev
  -- the attained slot value is 6 in EITHER slot (the equal-weight shape)
  have hτval : σV.w (Φhat - ν.σ.Φ ^ 2) = 6 := by
    interval_cases j₀
    · have hval : σV.w (Φhat - ν.σ.Φ ^ 2) = σV.w (Bτ 0) + ((0 : ℕ) : ℤ) * σV.w σV.Φ := hj₀eq
      have hB0 : Bτ 0 = tt 0 := by simp [hBτ]
      rw [hB0, hw0, hkΦ] at hval
      rw [hval]; norm_num
    · have hval : σV.w (Φhat - ν.σ.Φ ^ 2) = σV.w (Bτ 1) + ((1 : ℕ) : ℤ) * σV.w σV.Φ := hj₀eq
      have hB1 : Bτ 1 = tt 1 := by simp [hBτ]
      have hc1 : ν.ψ.coeff 1 ≠ 0 := by
        intro hc
        apply hj₀ne
        rw [hB1, htt0 1 hc]
      rw [hB1, hw1 hc1, hkΦ] at hval
      rw [hval]; norm_num
  -- degree of τ below the child key's degree
  have hτdeglt : (Φhat - ν.σ.Φ ^ 2).degree < Φhat.degree := by
    have hdegk : ∀ k, k < 2 → (tt k).degree < ν.σ.Φ.degree := by
      intro k hkG
      by_cases hψk : ν.ψ.coeff k = 0
      · rw [htt0 k hψk, Polynomial.degree_zero]
        exact Ne.bot_lt (fun hbot => hΦne (Polynomial.degree_eq_bot.mp hbot))
      · exact (httk k hkG hψk).2.1
    have hsum := hk05_sum_degree_lt ν.σ 1 2 (le_refl 1) tt hdegk
    have hτsum : Φhat - ν.σ.Φ ^ 2 = ∑ k ∈ Finset.range 2, tt k * ν.σ.Φ ^ (1 * k) := by
      rw [hPhi]
      have h12 : ν.σ.Φ ^ (1 * 2) = ν.σ.Φ ^ 2 := by norm_num
      rw [h12]; ring
    rw [hτsum, Polynomial.degree_eq_natDegree mon.ne_zero, hdeg]
    have h122 : 1 * 2 * ν.σ.Φ.natDegree = 2 * ν.σ.Φ.natDegree := by norm_num
    rw [h122] at hsum
    exact hsum
  -- σV.w Φ̂ ≥ 6 (both development parts weigh 6)
  have hwpow : σV.w (ν.σ.Φ ^ 2) = 6 := by
    have hwΦσ : σV.w ν.σ.Φ = 3 := by rw [← hVΦ]; exact hkΦ
    rw [ResVal.w_pow σV ν.σ.Φ hΦne 2, hwΦσ]; norm_num
  have hwhat : (6 : ℤ) ≤ σV.w Φhat := by
    have hsplit : ν.σ.Φ ^ 2 + (Φhat - ν.σ.Φ ^ 2) = Φhat := by ring
    have hne' : ν.σ.Φ ^ 2 + (Φhat - ν.σ.Φ ^ 2) ≠ 0 := by
      rw [hsplit]; exact mon.ne_zero
    have h := σV.hwult (ν.σ.Φ ^ 2) (Φhat - ν.σ.Φ ^ 2) (pow_ne_zero _ hΦne) hτne hne'
    rw [hsplit, hwpow, hτval] at h
    simpa using h
  exact ⟨mon, hdeg, hτne, hτval, hτdeglt, hwhat⟩

/-- **Instance classification** — the charged instance ((e★, h★) = (1, 3), g = 2, over a
(1,1)-Gauss parent) satisfies V11's TRULY-STEEP inequality `h★ > e★²·g·σ.h` (3 > 2): it
lies inside the (OLD) refuted-shape perimeter, so the stall below is about the KEYING,
not about the instance being outside the machinery's range. -/
theorem hk05_instance_truly_steep (ν : Node p F) (hνe : ν.e = 1) (hνh : ν.h = 3)
    (hνg : ν.g = 2) (hGauss : ν.σ.h = 1) :
    (ν.e : ℤ) * (ν.e : ℤ) * (ν.g : ℤ) * (ν.σ.h : ℤ) < (ν.h : ℤ) := by
  rw [hνe, hνh, hνg, hGauss]; norm_num

/-- **CONTROL ARM — the machinery FIRES on the (OLD) keying at the charged instance**:
with the transition keyed at the READ pair over σ.w and the (OLD) s/t ties (the current
`HistoryCoherent` non-recentering leg), `V10_readTransition_incompatible` closes False.
This certifies the refutation machinery is LIVE at this instance, so the (NEW)-side
stall below is evidence about the clause set, not about a dead instrument. -/
theorem hk05_machinery_fires_on_OLD
    (ν : Node p F) (hνe : ν.e = 1) (hνh : ν.h = 3) (hνg : ν.g = 2)
    (hGauss : ν.σ.h = 1)
    (Φhat : Polynomial ℤ_[p]) (hlift : IsNodeLift ν Φhat)
    (σ' : Stage p F)
    (hkey : σ'.Φ = Φhat) (hce : σ'.e = ν.e) (hcw : ∀ x, σ'.wPrev x = ν.σ.w x)
    (hslot : IsSlotMinWeight σ'.w Φhat ν.e ν.h ν.σ.w)
    (hs_tie : σ'.s = ν.s) (ht_tie : σ'.t = ν.t) :
    False := by
  have hψ0 := hk05_psi0_ne ν hνg
  have hlift' : IsReadLift ν.σ ν.ψ 2 1 3 Φhat := by
    have h := (isNodeLift_iff ν Φhat).mp hlift
    rw [hνe, hνh, hνg] at h
    exact h
  have ht0 : ν.t = 0 := by
    have h := ν.hbezCanon
    rw [hνe] at h
    omega
  have hbez' : (1 : ℤ) * ν.s + (3 : ℤ) * ν.t = 1 := by
    have h := ν.hbez
    rw [hνe, hνh] at h
    push_cast at h ⊢
    linarith
  have hce' : σ'.e = 1 := by rw [hce, hνe]
  have hslot' : IsSlotMinWeight σ'.w Φhat 1 3 ν.σ.w := by
    rw [hνe, hνh] at hslot
    exact hslot
  have hs_tie' : σ'.s = ν.s := hs_tie
  have ht_tie' : σ'.t = ν.t := ht_tie
  exact LeanUrat.HC1.V10_readTransition_incompatible ν.σ σ' 1 3 ν.s ν.t 2 ν.ψ Φhat
    (by rw [hGauss]; norm_num) (by norm_num) (by norm_num)
    (by push_cast; linarith [hbez']) (fun _ => ht0) hψ0 hlift'
    hkey hce' hcw hslot' hs_tie' ht_tie'

/-- **THE PRIMARY BLOCKING CLAUSE — `hlift` at the transition pair is UNSATISFIABLE
against the staged (NEW) record.**  Both `V10_forcedKeyWeight`/`V10_readTransition_incompatible`
and V11's `V11_minimalIncompat` consume a read-lift hypothesis `IsReadLift · ψ g e★ h★ Φ̂`
whose slot weights are keyed at the SAME pair as the transition.  Under the staged (NEW)
clause set the transition runs σV → σ' at the NEXT pair (e', h'), while the recorded lift
is σV-equal-weight (every Φ̂-slot at σV-weight 6 — `hk05_recorded`).  ANY transition-pair
read-lift rendering (any g', any ψV, σ' and the child record not even consulted) forces
`σV.w(τ-slot) ∈ {2h', h' + 3, h'}` = 6 — i.e. h' ∈ {3, 6} — while the granted steepening
`IAug σV Φ̂ e' h'` forces `h' > 6e' ≥ 6`.  The derivation STOPS HERE: the machinery
cannot state its entry hypothesis.  [The (NEW) keying decouples the lift pair from the
transition pair — the repair's design content, compiled.] -/
theorem hk05_hlift_blocked
    (ν : Node p F) (hνe : ν.e = 1) (hνh : ν.h = 3) (hνg : ν.g = 2)
    (σV : Stage p F) (hreg : StagedRegradeOf ν.σ ν σV)
    (Φhat : Polynomial ℤ_[p]) (hlift : IsNodeLift ν Φhat)
    (e' h' g' : ℕ) (he' : 1 ≤ e')
    (hiaug : IAug σV Φhat e' h')
    (ψV : Polynomial ↥σV.K) (hliftV : IsReadLift σV ψV g' e' h' Φhat) :
    False := by
  obtain ⟨mon, hdeg, hτne, hτval, hτdeglt, hwhat⟩ :=
    hk05_recorded ν hνe hνh hνg σV hreg Φhat hlift
  obtain ⟨hVΦ, hVe, hVh, -, -, -, hVwPrev, -⟩ := hreg
  rw [hνh] at hVh
  have hΦne : ν.σ.Φ ≠ 0 := ν.σ.hmonic.ne_zero
  have hD1 : 1 ≤ ν.σ.Φ.natDegree := ν.σ.hdeg
  -- the granted steepening: h' > 6e'
  have hiaug' : (h' : ℤ) > (e' : ℤ) * σV.w Φhat := hiaug
  have hIA : (6 : ℤ) * (e' : ℤ) < (h' : ℤ) := by
    have h6 : (6 : ℤ) * (e' : ℤ) ≤ (e' : ℤ) * σV.w Φhat := by
      calc (6 : ℤ) * (e' : ℤ) = (e' : ℤ) * 6 := by ring
        _ ≤ (e' : ℤ) * σV.w Φhat :=
            mul_le_mul_of_nonneg_left hwhat (Int.natCast_nonneg e')
    linarith
  -- the degree bookkeeping pins e'·g' = 2
  obtain ⟨monV, hdegV⟩ := hk05_lift_monic_natDegree σV ψV g' e' h' he' Φhat hliftV
  have hDeq : σV.Φ.natDegree = ν.σ.Φ.natDegree := by rw [hVΦ]
  rw [hDeq] at hdegV
  have hEG2 : e' * g' = 2 := by
    have h2 : 2 * ν.σ.Φ.natDegree = e' * g' * ν.σ.Φ.natDegree := by
      rw [← hdeg, ← hdegV]
    exact (Nat.eq_of_mul_eq_mul_right (by omega) h2).symm
  -- σV's key weight
  have hkΦ : σV.w σV.Φ = 3 := by rw [σV.hwΦ, hVh]; norm_num
  -- unpack the ATTEMPTED transition-pair lift
  obtain ⟨ttV, httV0, httVk, hPhiV⟩ := hliftV
  have hcases : (e' = 1 ∧ g' = 2) ∨ (e' = 2 ∧ g' = 1) := by
    have he'le : e' ≤ 2 := Nat.le_of_dvd (by norm_num) ⟨g', hEG2.symm⟩
    interval_cases e' <;> omega
  rcases hcases with ⟨he1, hg2⟩ | ⟨he2, hg1⟩
  · -- (e', g') = (1, 2): the attempted τ-slots weigh 2h' and h'+3, both > 6 = σV.w τ
    subst he1; subst hg2
    have hτsumV : Φhat - ν.σ.Φ ^ 2 = ttV 0 + ttV 1 * σV.Φ := by
      rw [hPhiV, hVΦ]
      simp [Finset.sum_range_succ]
    set BV : ℕ → Polynomial ℤ_[p] := fun j => if j = 0 then ttV 0 else if j = 1 then ttV 1 else 0
      with hBV
    have hdevV : IsDevelopment σV.Φ (Φhat - ν.σ.Φ ^ 2) BV 2 := by
      refine ⟨?_, ?_, ?_⟩
      · intro j
        simp only [hBV]
        split_ifs with h1 h2
        · by_cases hc0 : ψV.coeff 0 = 0
          · rw [httV0 0 hc0, Polynomial.degree_zero]
            exact Ne.bot_lt (fun hbot => by
              rw [hVΦ] at hbot
              exact hΦne (Polynomial.degree_eq_bot.mp hbot))
          · exact (httVk 0 (by norm_num) hc0).2.1
        · by_cases hc1 : ψV.coeff 1 = 0
          · rw [httV0 1 hc1, Polynomial.degree_zero]
            exact Ne.bot_lt (fun hbot => by
              rw [hVΦ] at hbot
              exact hΦne (Polynomial.degree_eq_bot.mp hbot))
          · exact (httVk 1 (by norm_num) hc1).2.1
        · rw [Polynomial.degree_zero]
          exact Ne.bot_lt (fun hbot => by
            rw [hVΦ] at hbot
            exact hΦne (Polynomial.degree_eq_bot.mp hbot))
      · intro j hj
        have hj0 : j ≠ 0 := by omega
        have hj1 : j ≠ 1 := by omega
        simp [hBV, hj0, hj1]
      · rw [hτsumV]
        simp [hBV, Finset.sum_range_succ]
    obtain ⟨-, j₀, hj₀2, hj₀ne, hj₀eq⟩ := σV.hK1 (Φhat - ν.σ.Φ ^ 2) BV 2 hτne hdevV
    interval_cases j₀
    · -- attained at slot 0: 6 = 2h', so h' = 3, against h' > 6
      have hval : σV.w (Φhat - ν.σ.Φ ^ 2) = σV.w (BV 0) + ((0 : ℕ) : ℤ) * σV.w σV.Φ := hj₀eq
      have hB0 : BV 0 = ttV 0 := by simp [hBV]
      have httV0ne : ttV 0 ≠ 0 := by rw [← hB0]; exact hj₀ne
      have hc0 : ψV.coeff 0 ≠ 0 := fun hc => httV0ne (httV0 0 hc)
      have hwv0 : σV.w (ttV 0) = (h' : ℤ) * 2 := by
        have h := (httVk 0 (by norm_num) hc0).2.2.1
        push_cast at h
        linarith [h]
      rw [hτval, hB0, hwv0, hkΦ] at hval
      push_cast at hval hIA
      linarith
    · -- attained at slot 1: 6 = h' + 3, so h' = 3, against h' > 6
      have hval : σV.w (Φhat - ν.σ.Φ ^ 2) = σV.w (BV 1) + ((1 : ℕ) : ℤ) * σV.w σV.Φ := hj₀eq
      have hB1 : BV 1 = ttV 1 := by simp [hBV]
      have httV1ne : ttV 1 ≠ 0 := by rw [← hB1]; exact hj₀ne
      have hc1 : ψV.coeff 1 ≠ 0 := fun hc => httV1ne (httV0 1 hc)
      have hwv1 : σV.w (ttV 1) = (h' : ℤ) := by
        have h := (httVk 1 (by norm_num) hc1).2.2.1
        push_cast at h
        linarith [h]
      rw [hτval, hB1, hwv1, hkΦ] at hval
      push_cast at hval hIA
      linarith
  · -- (e', g') = (2, 1): the attempted τ IS the single slot, weight h' = 6, against h' > 12
    subst he2; subst hg1
    have hτV : Φhat - ν.σ.Φ ^ 2 = ttV 0 := by
      rw [hPhiV, hVΦ]
      simp
    have httV0ne : ttV 0 ≠ 0 := by rw [← hτV]; exact hτne
    have hc0 : ψV.coeff 0 ≠ 0 := fun hc => httV0ne (httV0 0 hc)
    have hwv0 : σV.w (ttV 0) = (h' : ℤ) := by
      have h := (httVk 0 (by norm_num) hc0).2.2.1
      push_cast at h
      linarith [h]
    have h6 : (6 : ℤ) = (h' : ℤ) := by
      rw [← hτval, hτV, hwv0]
    push_cast at hIA
    linarith

/-- **The OLD-shape re-instantiation is blocked at `hcw`** — re-running the machinery
with (σ, σ') (the pre-repair configuration) needs `hcw : ∀ x, σ'.wPrev x = σ.w x`; under
the staged (NEW) record `child_wPrev` lands on σV.w instead, and the two are SEPARATED
on the parent key itself: `σ'.wPrev σ.Φ = σV.w σ.Φ = 3 ≠ 1 = σ.w σ.Φ` (at the
(1,1)-Gauss parent).  The clause is REFUTED by the record, not merely unsupplied.
(`hce : σ'.e = ν.e` and the read-pair `hslot`/ties are likewise re-keyed to the next
pair — this theorem compiles the sharpest single-clause block.) -/
theorem hk05_oldshape_hcw_blocked
    (ν : Node p F) (hνh : ν.h = 3) (hGauss : ν.σ.h = 1)
    (σV : Stage p F) (hreg : StagedRegradeOf ν.σ ν σV)
    (σ' : Stage p F) (Φhat : Polynomial ℤ_[p]) (e' h' : ℕ) (zbar : Fˣ)
    (htrans : TransitionCoreL σV σ' Φhat e' h' zbar) :
    ¬ (∀ x, σ'.wPrev x = ν.σ.w x) := by
  obtain ⟨hVΦ, -, hVh, -, -, -, -, -⟩ := hreg
  rw [hνh] at hVh
  intro hcw
  have h1 : σ'.wPrev ν.σ.Φ = σV.w ν.σ.Φ := htrans.base.child_wPrev ν.σ.Φ
  have h2 : σV.w ν.σ.Φ = 3 := by
    rw [← hVΦ, σV.hwΦ, hVh]; norm_num
  have h3 : ν.σ.w ν.σ.Φ = 1 := by
    rw [ν.σ.hwΦ, hGauss]; norm_num
  have h := hcw ν.σ.Φ
  rw [h1, h2, h3] at h
  norm_num at h

/-- **The STEP-1 re-instantiation (machinery on the regrade σ → σV) is blocked at the
non-corner perimeter `hEG`** — the regrade is KEY-PRESERVING (`σV.Φ = σ.Φ`, the §3.1(c)
display's first clause), and any read lift landing ON the parent key has `e·g = 1` by
the degree computation, so `2 ≤ e·g` (required by every V10/V11 theorem) is
unsatisfiable there. -/
theorem hk05_step1_regrade_blocked (σ : Stage p F) (ψ : Polynomial ↥σ.K)
    (g e h : ℕ) (he : 1 ≤ e) (hl : IsReadLift σ ψ g e h σ.Φ) :
    e * g = 1 := by
  obtain ⟨-, hdeg⟩ := hk05_lift_monic_natDegree σ ψ g e h he σ.Φ hl
  have hD1 : 1 ≤ σ.Φ.natDegree := σ.hdeg
  have h1 : 1 ≤ e * g := by
    rcases Nat.eq_zero_or_pos (e * g) with h0 | h1
    · rw [h0, zero_mul] at hdeg; omega
    · exact h1
  by_contra hne
  have h2 : 2 ≤ e * g := by omega
  have h3 : 2 * σ.Φ.natDegree ≤ e * g * σ.Φ.natDegree := Nat.mul_le_mul_right _ h2
  rw [← hdeg] at h3
  omega

/-- **Finding-2's residual-clash route is blocked at the `hRlt`/`hRadd` entries** — at
the staged (NEW) record the child σ' weighs the two parts of the recorded Φ̂-development
EQUALLY, `σ'.w(σ.Φ²) = 6e' = σ'.w(Φ̂ − σ.Φ²)`, while the child key is STRICTLY heavier,
`σ'.w Φ̂ = h' > 6e'` (IAug + hwΦ).  So `hRlt` (needs a STRICT slot inequality) and
`hRadd` (needs sum weight = slot weight) both refuse: no Stage residual law computes
`σ'.R Φ̂` from the development slots, and V10-finding-2's position clash
(`T s` vs `C(c^{eg})`) cannot be assembled.  This is the genuine CANCELLATION
(ψ-divisibility) configuration — D.7's hypothesis class, the S9-consistent carrier.
The tie is FORCED by the recorded lift shape, not chosen: with unequal slot weights the
two-sided ultrametric argument would pin `σ'.w Φ̂` to the minimum, clashing with IAug. -/
theorem hk05_find2_residual_entries_blocked
    (ν : Node p F) (hνe : ν.e = 1) (hνh : ν.h = 3) (hνg : ν.g = 2)
    (σV : Stage p F) (hreg : StagedRegradeOf ν.σ ν σV)
    (Φhat : Polynomial ℤ_[p]) (hlift : IsNodeLift ν Φhat)
    (σ' : Stage p F) (e' h' : ℕ) (zbar : Fˣ)
    (htrans : TransitionCoreL σV σ' Φhat e' h' zbar)
    (hiaug : IAug σV Φhat e' h') :
    σ'.w (ν.σ.Φ ^ 2) = 6 * (e' : ℤ) ∧
    σ'.w (Φhat - ν.σ.Φ ^ 2) = 6 * (e' : ℤ) ∧
    6 * (e' : ℤ) < σ'.w Φhat := by
  obtain ⟨mon, hdeg, hτne, hτval, hτdeglt, hwhat⟩ :=
    hk05_recorded ν hνe hνh hνg σV hreg Φhat hlift
  obtain ⟨hVΦ, hVe, hVh, -, -, -, hVwPrev, -⟩ := hreg
  rw [hνh] at hVh
  have hΦne : ν.σ.Φ ≠ 0 := ν.σ.hmonic.ne_zero
  have hD1 : 1 ≤ ν.σ.Φ.natDegree := ν.σ.hdeg
  -- σ.Φ sits in the child key's coefficient space
  have hinPhi : inC σ'.Φ ν.σ.Φ := by
    show ν.σ.Φ.degree < σ'.Φ.degree
    rw [htrans.base.child_key, Polynomial.degree_eq_natDegree hΦne,
      Polynomial.degree_eq_natDegree mon.ne_zero, hdeg]
    exact_mod_cast (by omega : ν.σ.Φ.natDegree < 2 * ν.σ.Φ.natDegree)
  have hwPhi' : σ'.w ν.σ.Φ = (e' : ℤ) * 3 := by
    rw [σ'.hStretch ν.σ.Φ hΦne hinPhi, htrans.base.child_e, htrans.base.child_wPrev,
      ← hVΦ, σV.hwΦ, hVh]
    norm_num
  refine ⟨?_, ?_, ?_⟩
  · rw [ResVal.w_pow σ' ν.σ.Φ hΦne 2, hwPhi']; ring
  · have hinτ : inC σ'.Φ (Φhat - ν.σ.Φ ^ 2) := by
      show (Φhat - ν.σ.Φ ^ 2).degree < σ'.Φ.degree
      rw [htrans.base.child_key]
      exact hτdeglt
    rw [σ'.hStretch _ hτne hinτ, htrans.base.child_e, htrans.base.child_wPrev, hτval]
    ring
  · have h1 : σ'.w Φhat = (h' : ℤ) := by
      rw [← htrans.base.child_key, σ'.hwΦ, htrans.base.child_h]
    rw [h1]
    have hiaug' : (h' : ℤ) > (e' : ℤ) * σV.w Φhat := hiaug
    have h6 : (e' : ℤ) * 6 ≤ (e' : ℤ) * σV.w Φhat :=
      mul_le_mul_of_nonneg_left hwhat (Int.natCast_nonneg e')
    linarith

end HK05

end LeanUrat.MovesJ

#print axioms LeanUrat.MovesJ.hk05_instance_truly_steep
#print axioms LeanUrat.MovesJ.hk05_machinery_fires_on_OLD
#print axioms LeanUrat.MovesJ.hk05_hlift_blocked
#print axioms LeanUrat.MovesJ.hk05_oldshape_hcw_blocked
#print axioms LeanUrat.MovesJ.hk05_step1_regrade_blocked
#print axioms LeanUrat.MovesJ.hk05_find2_residual_entries_blocked
