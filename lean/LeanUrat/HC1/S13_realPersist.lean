/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.HC1.DefsSpine
import LeanUrat.Moves.L5_realRecursion_R3
import LeanUrat.Moves.L5_realCofin_R3
import LeanUrat.Moves.L5_realDomination_R3
import LeanUrat.Moves.L5_realConclusion

/-!
# HC1.S13_realPersist — Lemma REAL along the tower (D.9)

moves_ref: MOVES 2551–2581 (D.9(a)–(d), incl. the induction-order clause: stage-r
quantities before Φ_{r+1} — the Tower's own structural order). deps: S11, S12;
Moves `L5_realRecursion_R3`, `L5_realCofin_R3`, `L5_realDomination_R3`,
`L5_realConclusion` (all clean). difficulty: medium. hyp: none.

REV (2026-07-28, S13 ADJUDICATION — campaign ledger
`LEAN_FORMALIZATION_CAMPAIGN_2026-07-28.md`, orchestrator direct read of D.9(d),
MOVES 2573–2581): conjunct 3 RESTATED with the display's own scope. The note
scopes any-scalar realizability to e_read = 1 READS — the side values λ″, i.e.
values strictly above the current key's parent weight (the (S6b)/DEF-8
threshold) — persisting along histories. The E-phase conjunct claimed it at
EVERY weight-set value (where the note supplies only the (S6a) base orbit):
BLUEPRINT OVER-STRENGTH (type i), the note intact; XE-precedent (statement
repair post-refutation).
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

namespace LeanUrat.HC1

open Polynomial LeanUrat.Moves

/-- `v 1 = 0` for any multiplicative valuation-shaped map. -/
private lemma val_one_zero {p : ℕ} [Fact p.Prime] (v : Polynomial ℤ_[p] → ℤ)
    (hmul : ∀ f g : Polynomial ℤ_[p], f ≠ 0 → g ≠ 0 → v (f * g) = v f + v g) :
    v 1 = 0 := by
  have h := hmul 1 1 one_ne_zero one_ne_zero
  rw [mul_one] at h
  omega

/-- `v (-f) = v f` for any multiplicative valuation-shaped map. -/
private lemma val_neg {p : ℕ} [Fact p.Prime] (v : Polynomial ℤ_[p] → ℤ)
    (hmul : ∀ f g : Polynomial ℤ_[p], f ≠ 0 → g ≠ 0 → v (f * g) = v f + v g)
    (f : Polynomial ℤ_[p]) (hf : f ≠ 0) : v (-f) = v f := by
  have hn1 : v (-1 : Polynomial ℤ_[p]) = 0 := by
    have h := hmul (-1) (-1) (neg_ne_zero.mpr one_ne_zero) (neg_ne_zero.mpr one_ne_zero)
    rw [neg_mul_neg, mul_one, val_one_zero v hmul] at h
    omega
  have heq : (-f) = (-1 : Polynomial ℤ_[p]) * f := by ring
  rw [heq, hmul (-1) f (neg_ne_zero.mpr one_ne_zero) hf, hn1, zero_add]

/-- Strict triangle inequality: for a multiplicative ultrametric-shaped map, if `v a < v b`
then `v (a + b) = v a` (no cancellation jump when the two weights differ). -/
private lemma val_strict {p : ℕ} [Fact p.Prime] (v : Polynomial ℤ_[p] → ℤ)
    (hmul : ∀ f g : Polynomial ℤ_[p], f ≠ 0 → g ≠ 0 → v (f * g) = v f + v g)
    (hult : ∀ f g : Polynomial ℤ_[p], f ≠ 0 → g ≠ 0 → f + g ≠ 0 →
        min (v f) (v g) ≤ v (f + g))
    (a b : Polynomial ℤ_[p]) (ha : a ≠ 0) (hb : b ≠ 0) (hab : a + b ≠ 0)
    (hlt : v a < v b) : v (a + b) = v a := by
  have h1 : v a ≤ v (a + b) := by
    have h := hult a b ha hb hab
    rwa [min_eq_left (le_of_lt hlt)] at h
  by_contra hne
  have h2 : v a < v (a + b) := lt_of_le_of_ne h1 (fun h => hne h.symm)
  have hnegb : (-b) ≠ 0 := neg_ne_zero.mpr hb
  have hsum2 : (a + b) + (-b) = a := by ring
  have hsum2ne : (a + b) + (-b) ≠ 0 := by rw [hsum2]; exact ha
  have h3 := hult (a + b) (-b) hab hnegb hsum2ne
  rw [hsum2, val_neg v hmul b hb] at h3
  have h4 : v a < min (v (a + b)) (v b) := lt_min h2 hlt
  linarith

/-- Unit S13: per tower level — the weight set is cofinite upward (a tail bound),
the domination h > e·wPrev(Φ) persists, and the D.9(d) conclusion IN ITS OWN
SCOPE: at an e_read = 1 read, every value strictly above the current key's
parent weight (the display's side values λ″ > w(current key) ≥ bound; the
(S6b)/DEF-8 threshold) lies in the weight set and is realizable with ANY digit
scalar at position 0. Quantified over every level of every tower — the
display's "persists along every history".

**The D.9(d) display, MOVES 2573–2581, quoted verbatim (the S13 ADJUDICATION
scope, campaign ledger 2026-07-28):** "At any e_read = 1 read, the side value
λ″ satisfies λ″ > w(current key) ≥ (current bound) by (c), and λ″ lies in the
coefficient value group (that IS e_read = 1); by (b), λ″ ∈ the coefficient
weight set. Position 0 is automatic at e_read = 1 stages ((P2): T
coefficient-pure ⟹ all coefficient digits position-0), and any digit scalar
c̃ ∈ F'ˣ is realizable ((S6b): zero-class — the stretch is trivial at
e_read = 1 — and above the bound by (c)). Inside a RECENTERED frame the
coefficient space and weight are unchanged (D.10: v = v'), and subsequent side
values only grow (convexity within the frame + (I-aug)); so (d) persists along
every history. ∎"

Any-scalar realizability is NOT claimed at weight-set values ≤ wPrev Φ (there
the note supplies only the (S6a) base orbit). The S10 consumer's `hlift` needs
ν = h, which is in scope: wPrev Φ < h at e = 1 by conjunct 2. -/
theorem S13_realPersist {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
    (T : Tower p F) (k : Fin (T.K + 1)) :
    (∃ ν₀ : ℤ, ∀ ν : ℤ, ν₀ ≤ ν → ν ∈ (T.stg k).weightSet) ∧
    (((T.stg k).e : ℤ) * (T.stg k).wPrev (T.stg k).Φ < ((T.stg k).h : ℤ)) ∧
    ((T.stg k).e = 1 → ∀ ν : ℤ, (T.stg k).wPrev (T.stg k).Φ < ν →
      ν ∈ (T.stg k).weightSet ∧
      ∀ c : (↥(T.stg k).K)ˣ,
        ∃ B : Polynomial ℤ_[p], B ≠ 0 ∧ inC (T.stg k).Φ B ∧
          (T.stg k).wPrev B = ν ∧
          (T.stg k).R B = LaurentPolynomial.C ((c : ↥(T.stg k).K)) *
            LaurentPolynomial.T 0) := by
  -- The domination `e·wPrev Φ < h` (= `StageCore.prevIaug`), together with the two
  -- parent-valuation laws it needs, threaded along the tower.  We carry ONLY these
  -- (not the full `StageCoreL`, which is underdetermined at children): the increment
  -- child's `wPrev` IS the parent's `w` (a Stage axiom), the recentering child's
  -- `wPrev` IS the parent's `wPrev` (from the IH).
  have hQ : ∀ j : Fin (T.K + 1),
      ((T.stg j).e : ℤ) * (T.stg j).wPrev (T.stg j).Φ < ((T.stg j).h : ℤ) ∧
      (∀ f g : Polynomial ℤ_[p], f ≠ 0 → g ≠ 0 →
        (T.stg j).wPrev (f * g) = (T.stg j).wPrev f + (T.stg j).wPrev g) ∧
      (∀ f g : Polynomial ℤ_[p], f ≠ 0 → g ≠ 0 → f + g ≠ 0 →
        min ((T.stg j).wPrev f) ((T.stg j).wPrev g) ≤ (T.stg j).wPrev (f + g)) := by
    intro j
    induction j using Fin.induction with
    | zero =>
        exact ⟨T.base.2.core.prevIaug, T.base.2.core.wPrev_mul, T.base.2.core.wPrev_ult⟩
    | succ i IH =>
        cases T.move i with
        | inc ψ g Φhat e' h' zbar hyp core =>
            have hkey := core.base.child_key
            have hce := core.base.child_e
            have hch := core.base.child_h
            have hcw := core.base.child_wPrev
            refine ⟨?_, ?_, ?_⟩
            · -- child prevIaug is exactly `IAug` (the move's own `hiaug`)
              rw [hce, hch, hkey, hcw Φhat]
              exact hyp.hiaug
            · intro f g hf hg
              rw [hcw (f * g), hcw f, hcw g]
              exact (T.stg i.castSucc).hwmul f g hf hg
            · intro f g hf hg hfg
              rw [hcw (f + g), hcw f, hcw g]
              exact (T.stg i.castSucc).hwult f g hf hg hfg
        | recenter cc tt core =>
            obtain ⟨IHiaug, IHmul, IHult⟩ := IH
            obtain ⟨he1, he1', _, htin, httne, hwtt, _, hΦ', hwf, hwpf, _, _, _, _⟩ :=
              core.base
            set σ := T.stg i.castSucc with hσ
            set σ' := T.stg i.succ with hσ'
            have hσe1 : (σ.e : ℤ) = 1 := by exact_mod_cast he1
            have hΦne : σ.Φ ≠ 0 := σ.hmonic.ne_zero
            have hnegtt : (-tt) ≠ 0 := neg_ne_zero.mpr httne
            have hΦsubne : σ.Φ - tt ≠ 0 := by
              rw [sub_ne_zero]; rintro rfl; exact lt_irrefl _ htin
            have hΦaddne : σ.Φ + (-tt) ≠ 0 := by rw [← sub_eq_add_neg]; exact hΦsubne
            -- `wPrev tt = h` (via the `e = 1` stretch), so `wPrev tt > wPrev Φ` (the IH bound)
            have hwtt_h : σ.w tt = (σ.h : ℤ) := by rw [hwtt]; exact σ.hwΦ
            have hwPrevtt : σ.wPrev tt = (σ.h : ℤ) := by
              have h := σ.hStretch tt httne htin
              rw [hwtt_h, hσe1, one_mul] at h
              exact h.symm
            have hIH : σ.wPrev σ.Φ < (σ.h : ℤ) := by
              have h := IHiaug
              rw [hσe1, one_mul] at h
              exact h
            -- `wPrev (Φ - tt) = wPrev Φ` by the strict triangle (`wPrev tt > wPrev Φ`)
            have hlt' : σ.wPrev σ.Φ < σ.wPrev (-tt) := by
              rw [val_neg σ.wPrev IHmul tt httne, hwPrevtt]; exact hIH
            have hstrict : σ.wPrev (σ.Φ - tt) = σ.wPrev σ.Φ := by
              have h := val_strict σ.wPrev IHmul IHult σ.Φ (-tt) hΦne hnegtt hΦaddne hlt'
              rwa [← sub_eq_add_neg] at h
            -- `w (Φ - tt) ≥ w Φ = h` by the ultrametric (equal weights, no drop)
            have hwge : (σ.h : ℤ) ≤ σ.w (σ.Φ - tt) := by
              have hult := σ.hwult σ.Φ (-tt) hΦne hnegtt hΦaddne
              rw [val_neg σ.w σ.hwmul tt httne, hwtt, min_self, ← sub_eq_add_neg,
                σ.hwΦ] at hult
              exact hult
            refine ⟨?_, ?_, ?_⟩
            · -- child prevIaug
              have hσ'e1 : (σ'.e : ℤ) = 1 := by exact_mod_cast he1'
              have hgoalL : σ'.wPrev σ'.Φ = σ.wPrev (σ.Φ - tt) := by rw [hwpf, hΦ']
              have hgoalR : (σ'.h : ℤ) = σ.w (σ.Φ - tt) := by rw [← σ'.hwΦ, hwf, hΦ']
              rw [hσ'e1, one_mul, hgoalL, hgoalR, hstrict]
              linarith [hIH, hwge]
            · intro f g hf hg
              rw [hwpf (f * g), hwpf f, hwpf g]
              exact IHmul f g hf hg
            · intro f g hf hg hfg
              rw [hwpf (f + g), hwpf f, hwpf g]
              exact IHult f g hf hg hfg
  refine ⟨?_, (hQ k).1, ?_⟩
  · -- conjunct 1: cofinite weight set — `hS6b` (any scalar above the key weight) + `hWS`
    refine ⟨(T.stg k).wPrev (T.stg k).Φ + 1, ?_⟩
    intro ν hν
    have hlt : (T.stg k).wPrev (T.stg k).Φ < ν := by linarith
    obtain ⟨B, hBne, hBc, hBw, _⟩ := (T.stg k).hS6b ν 1 hlt
    have hmem := (T.stg k).hWS B hBne hBc
    rw [hBw] at hmem
    exact hmem
  · -- conjunct 3: at `e = 1`, every side value above the key weight is in the weight set
    -- and realizable with any digit scalar at position 0 (`L5_realConclusion`)
    intro he1 ν hν
    refine ⟨?_, ?_⟩
    · obtain ⟨B, hBne, hBc, hBw, _⟩ := (T.stg k).hS6b ν 1 hν
      have hmem := (T.stg k).hWS B hBne hBc
      rw [hBw] at hmem
      exact hmem
    · intro c
      exact L5_realConclusion (T.stg k) he1 ν hν c

end LeanUrat.HC1

#print axioms LeanUrat.HC1.S13_realPersist
