/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.HC2.Defs
import LeanUrat.Moves.ResVal

/-!
# HC1.V11_minimalCore — HK-02: the 5-clause minimal incompatibility core

Bridge campaign BP2 (`lean/notes/BRIDGE_BP2_HC2K1_2026-07-30.md`, Block K, unit HK-02).
E-PHASE SKELETON: statement + `sorry` body; P-phase proves (routine-opus, est. ~50 lines,
V10 helper patterns copy).

**Unit HK-02 `V11_minimalIncompat`** (blueprint file prescription: NEW file
`HC1/V11_minimalCore.lean` — honored; the E-phase charge's default `HC2/` location is
overridden by the blueprint's explicit prescription, recorded here).

INFORMAL STATEMENT: the 5-clause core — `child_h` (`σ'.h = h★`) + `child_wPrev`
(`σ'.wPrev = σ.w`) + the child's own Stage laws `hStretch`/`hwmul`/`hwult` (free with
`σ' : Stage`, entering through `child_key`/`child_e` so they read at the recorded key and
stretch) + the read-lift τ-bound (the slot weights `σ.w (t_k) = h★·(g−k)` of
`IsReadLift`) — is already CONTRADICTORY at any truly-steep pair, `h★ > e★²·g·σ.h`.

SKETCH (blueprint HK-02): `σ'.w (Φ^{e★g}) = e★²·g·σ.h` by `hwmul` + `hStretch` (through
`child_e`/`child_wPrev`; `Φ ∈ C_{Φ̂}` from the non-corner degree bookkeeping, `e★·g ≥ 2`);
the ultrametric on `Φ^{e★g} = Φ̂ − τ` gives `σ'.w (Φ^{e★g}) ≥ min (h★, σ'.w τ)` with
`σ'.w Φ̂ = h★` (`child_key` + `child_h` + `hwΦ`) and `σ'.w τ ≥ e★·h★ ≥ h★` (the read-lift
τ-bound through `hStretch`, per-slot `e★·h★·(g−k) + e★²·k·σ.h ≥ h★` at `k < g`), so
`e★²·g·σ.h ≥ h★` — contradicting truly-steep.

PURPOSE: extends V10's refuted perimeter (NO `child_slotmin`, NO s/t ties needed); pins
WHICH `TransitionData` fields must change in the task-#44 repair — fences the (S-c)-lite
"drop the ties only" non-candidate (the ties are not the only contradictory clauses).

deps: — (V10 helper patterns copy: `v10_w_one/v10_w_neg/v10_w_pow/v10_w_sum_ge` in
`HC1/V10_transportWindow.lean`, private — re-derive locally in P-phase).
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 400000

namespace LeanUrat.HC1

open Polynomial LeanUrat.Moves LeanUrat.MovesJ

/-- **HK-02 `V11_minimalIncompat`** — the 5-clause minimal incompatibility core: at a
truly-steep read-lift transition (`h★ > e★²·g·σ.h`, non-corner `e★·g ≥ 2`), the clauses
`child_key` (`σ'.Φ = Φ̂`), `child_e` (`σ'.e = e★`), `child_h` (`σ'.h = h★`),
`child_wPrev` (`σ'.wPrev = σ.w`) plus the child's OWN Stage laws
(`hStretch`/`hwmul`/`hwult`/`hwΦ`) and the read-lift slot weights are contradictory
outright — no slot-min, no Bézout ties consumed.  Hypothesis shape = `V10_forcedKeyWeight`
minus `hslot`, plus `child_h`, with steepness strengthened to truly-steep.
[Blueprint BP2 HK-02; deps: — (V10 helper patterns copy); sketch in the module header.] -/
theorem V11_minimalIncompat {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
    (σ σ' : Stage p F) (estar hstar : ℕ) (g : ℕ)
    (ψ : Polynomial ↥σ.K) (Φhat : Polynomial ℤ_[p])
    (hsteep : (estar : ℤ) * (estar : ℤ) * (g : ℤ) * (σ.h : ℤ) < (hstar : ℤ))
    (hEG : 2 ≤ estar * g)
    (hlift : IsReadLift σ ψ g estar hstar Φhat)
    (hkey : σ'.Φ = Φhat) (hce : σ'.e = estar) (hch : σ'.h = hstar)
    (hcw : ∀ x, σ'.wPrev x = σ.w x) :
    False := by
  classical
  obtain ⟨tt, htt0, httk, hPhi⟩ := hlift
  have hΦne : σ.Φ ≠ 0 := σ.hmonic.ne_zero
  set E : ℕ := estar with hE
  set G : ℕ := g with hG
  have hE1 : 1 ≤ E := by
    rcases Nat.eq_zero_or_pos E with h0 | h1
    · rw [h0] at hEG; omega
    · exact h1
  have hG1 : 1 ≤ G := by
    rcases Nat.eq_zero_or_pos G with h0 | h1
    · rw [h0] at hEG; omega
    · exact h1
  have hD1 : 1 ≤ σ.Φ.natDegree := σ.hdeg
  set D : ℕ := σ.Φ.natDegree with hD
  set τ : Polynomial ℤ_[p] := ∑ k ∈ Finset.range G, tt k * σ.Φ ^ (E * k) with hτdef
  have hpowne : σ.Φ ^ (E * G) ≠ 0 := pow_ne_zero _ hΦne
  -- degree bookkeeping (transplanted from `V10_forcedKeyWeight`)
  have hdegpow : (σ.Φ ^ (E * G)).degree = ((E * G * D : ℕ) : WithBot ℕ) := by
    rw [Polynomial.degree_eq_natDegree hpowne, Polynomial.natDegree_pow]
  have hτdeg : τ.degree < ((E * G * D : ℕ) : WithBot ℕ) := by
    refine lt_of_le_of_lt (Polynomial.degree_sum_le _ _) ?_
    rw [Finset.sup_lt_iff (WithBot.bot_lt_coe _)]
    intro k hk
    by_cases htk : tt k = 0
    · rw [htk, zero_mul, Polynomial.degree_zero]; exact WithBot.bot_lt_coe _
    · have hkG : k < G := Finset.mem_range.mp hk
      have hψk : ψ.coeff k ≠ 0 := fun h0 => htk (htt0 k h0)
      obtain ⟨-, htkC, -, -⟩ := httk k hkG hψk
      have htermne : tt k * σ.Φ ^ (E * k) ≠ 0 := mul_ne_zero htk (pow_ne_zero _ hΦne)
      refine (Polynomial.natDegree_lt_iff_degree_lt htermne).mp ?_
      rw [Polynomial.natDegree_mul htk (pow_ne_zero _ hΦne), Polynomial.natDegree_pow]
      have httdeg : (tt k).natDegree < D := Polynomial.natDegree_lt_natDegree htk htkC
      have h1 : E * k + 1 ≤ E * G := by
        have hEk : E * k + 1 ≤ E * (k + 1) := by
          rw [Nat.mul_succ]
          exact Nat.add_le_add_left hE1 (E * k)
        exact le_trans hEk (Nat.mul_le_mul_left E hkG)
      have hb : D + E * k * D ≤ E * G * D := by
        have h2 : (E * k + 1) * D ≤ (E * G) * D := Nat.mul_le_mul_right D h1
        calc D + E * k * D = (E * k + 1) * D := by ring
          _ ≤ E * G * D := h2
      exact lt_of_lt_of_le (Nat.add_lt_add_right httdeg _) hb
  have hΦhatdeg : Φhat.degree = ((E * G * D : ℕ) : WithBot ℕ) := by
    rw [hPhi,
      Polynomial.degree_add_eq_left_of_degree_lt (by rw [hdegpow]; exact hτdeg), hdegpow]
  have hinC : inC σ'.Φ σ.Φ := by
    show σ.Φ.degree < σ'.Φ.degree
    rw [hkey, hΦhatdeg, Polynomial.degree_eq_natDegree hΦne, ← hD]
    have hlt : D < E * G * D := by
      have h2 : 2 * D ≤ E * G * D := Nat.mul_le_mul_right D hEG
      omega
    exact_mod_cast hlt
  -- key weights at σ′
  have hwΦhat : σ'.w Φhat = (hstar : ℤ) := by rw [← hkey, σ'.hwΦ, hch]
  have hwPhi' : σ'.w σ.Φ = (E : ℤ) * (σ.h : ℤ) := by
    rw [σ'.hStretch σ.Φ hΦne hinC, hcw, σ.hwΦ, hce]
  have hwpow : σ'.w (σ.Φ ^ (E * G)) = (E : ℤ) * (E : ℤ) * (G : ℤ) * (σ.h : ℤ) := by
    rw [ResVal.w_pow σ' σ.Φ hΦne (E * G), hwPhi']; push_cast; ring
  by_cases hτ0 : τ = 0
  · -- τ = 0: Φ̂ = Φ^{E·G}, so h★ = E²·G·σ.h, against truly-steep
    rw [hPhi, hτ0, add_zero] at hwΦhat
    rw [hwpow] at hwΦhat
    exact absurd (hwΦhat ▸ hsteep) (lt_irrefl _)
  · -- τ ≠ 0: the read-lift slot weights give σ′.w τ ≥ h★
    have hstar0 : (0 : ℤ) ≤ (hstar : ℤ) := Int.natCast_nonneg _
    have hσh0 : (0 : ℤ) ≤ (σ.h : ℤ) := Int.natCast_nonneg _
    have hE1Z : (1 : ℤ) ≤ (E : ℤ) := by exact_mod_cast hE1
    have hτbound : (hstar : ℤ) ≤ σ'.w τ := by
      refine ResVal.w_sum_ge σ' (Finset.range G) _ (hstar : ℤ) ?_ (by rw [← hτdef]; exact hτ0)
      intro k hk htermne
      have hkG : k < G := Finset.mem_range.mp hk
      have htk : tt k ≠ 0 := fun h0 => htermne (by rw [h0, zero_mul])
      have hψk : ψ.coeff k ≠ 0 := fun h0 => htk (htt0 k h0)
      obtain ⟨-, hinCk, htkw, -⟩ := httk k hkG hψk
      have hinCk' : inC σ'.Φ (tt k) := lt_trans hinCk hinC
      rw [σ'.hwmul _ _ htk (pow_ne_zero _ hΦne), σ'.hStretch (tt k) htk hinCk', hcw, htkw,
        hce, ResVal.w_pow σ' σ.Φ hΦne (E * k), hwPhi']
      have hGk1 : (1 : ℤ) ≤ (G : ℤ) - (k : ℤ) := by
        have : (k : ℤ) < (G : ℤ) := by exact_mod_cast hkG
        omega
      have t1 : (hstar : ℤ) ≤ (E : ℤ) * ((hstar : ℤ) * ((G : ℤ) - (k : ℤ))) := by
        have ha : (hstar : ℤ) * 1 ≤ (hstar : ℤ) * ((G : ℤ) - (k : ℤ)) :=
          mul_le_mul_of_nonneg_left hGk1 hstar0
        have hpos : (0 : ℤ) ≤ (hstar : ℤ) * ((G : ℤ) - (k : ℤ)) := by
          apply mul_nonneg hstar0; linarith
        have hb : (hstar : ℤ) * ((G : ℤ) - (k : ℤ))
            ≤ (E : ℤ) * ((hstar : ℤ) * ((G : ℤ) - (k : ℤ))) := by
          calc (hstar : ℤ) * ((G : ℤ) - (k : ℤ))
              = 1 * ((hstar : ℤ) * ((G : ℤ) - (k : ℤ))) := (one_mul _).symm
            _ ≤ (E : ℤ) * ((hstar : ℤ) * ((G : ℤ) - (k : ℤ))) :=
                mul_le_mul_of_nonneg_right hE1Z hpos
        linarith
      have t2 : (0 : ℤ) ≤ ((E * k : ℕ) : ℤ) * ((E : ℤ) * (σ.h : ℤ)) := by positivity
      push_cast at t2 ⊢
      nlinarith [t1, t2]
    -- ultrametric on Φ̂ + (−τ) = Φ^{E·G}
    have hΦhatne : Φhat ≠ 0 := by rw [← hkey]; exact σ'.hmonic.ne_zero
    have hsumeq : Φhat + (-τ) = σ.Φ ^ (E * G) := by rw [hPhi]; ring
    have hsumne : Φhat + (-τ) ≠ 0 := by rw [hsumeq]; exact hpowne
    have hult := σ'.hwult Φhat (-τ) hΦhatne (neg_ne_zero.mpr hτ0) hsumne
    rw [hwΦhat, ResVal.w_neg σ' τ hτ0, hsumeq, hwpow] at hult
    rw [min_eq_left hτbound] at hult
    exact absurd (lt_of_lt_of_le hsteep hult) (lt_irrefl _)

end LeanUrat.HC1
