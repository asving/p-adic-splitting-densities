/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.Moves.Defs
import LeanUrat.Moves.DefsT

/-!
**DEPRECATED — M=0 branch is machine-checked FALSE (`L6_moveReduceCommute_statement_false`
in-file). Superseded by `L6_moveReduceCommute_R4.lean` (sorry-free, adds `1 ≤ M` per
machine-checked finding 3). Do not import.**

# Moves/L6_moveReduceCommute_R3 — development commutes with reduction mod p^M (§0 Fact A / D.11)

STATUS: the manifest statement is **false at `M = 0`** (target ring `ZMod (p^0) = ZMod 1` is
trivial, so both mapped polynomials vanish and clause 1 of `IsDevelopment` demands `⊥ < ⊥`).
This file contains:
* `L6_moveReduceCommute_of_nontrivial` — the FULLY PROVEN content, for any nontrivial target;
* `L6_moveReduceCommute_of_one_le` — the FULLY PROVEN corrected statement (adds `1 ≤ M`);
* `L6_moveReduceCommute` — the fenced manifest statement, with a single `sorry` confined to
  the genuinely false `M = 0` branch (statement NOT weakened, per the statement fence);
* `L6_moveReduceCommute_statement_false` — a machine-checked disproof of the manifest
  statement's universal closure, certifying that the `sorry` is unfixable as stated.
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option maxHeartbeats 400000

open Polynomial LeanUrat.Moves

namespace LeanUrat.Moves

/-- Core content (fully proven): over any NONTRIVIAL target `ZMod (p^M)`, a `Φhat`-development
of `f` maps to a development of the reductions. Monicity of `Φhat` keeps its degree under the
map (leading coeff `1 ↦ 1 ≠ 0`), while the `B j` degrees can only drop, so the coefficient-space
bounds `inC` survive; the vanishing and sum clauses are ring-hom pushforward. -/
theorem L6_moveReduceCommute_of_nontrivial {p : ℕ} [Fact p.Prime] (Φhat f : Polynomial ℤ_[p])
    (hmon : Φhat.Monic) (B : ℕ → Polynomial ℤ_[p]) (N M : ℕ)
    (hdev : IsDevelopment Φhat f B N) [Nontrivial (ZMod (p ^ M))] :
    IsDevelopment (Φhat.map (PadicInt.toZModPow M)) (f.map (PadicInt.toZModPow M))
      (fun j => (B j).map (PadicInt.toZModPow M)) N := by
  obtain ⟨hBdeg, hBzero, hBsum⟩ := hdev
  set φ := PadicInt.toZModPow (p := p) M with hφ
  refine ⟨?_, ?_, ?_⟩
  · -- clause 1: degree bounds survive — monic key keeps its degree, digits can only drop
    intro j
    have hd : (Φhat.map φ).degree = Φhat.degree := by
      apply Polynomial.degree_map_eq_of_leadingCoeff_ne_zero
      rw [hmon.leadingCoeff, map_one]
      exact one_ne_zero
    calc ((B j).map φ).degree ≤ (B j).degree := Polynomial.degree_map_le
      _ < Φhat.degree := hBdeg j
      _ = (Φhat.map φ).degree := hd.symm
  · -- clause 2: vanishing above N
    intro j hj
    show (B j).map φ = 0
    rw [hBzero j hj, Polynomial.map_zero]
  · -- clause 3: the sum identity pushes forward along the ring hom
    rw [hBsum, Polynomial.map_sum]
    exact Finset.sum_congr rfl fun j _ => by
      simp only [Polynomial.map_mul, Polynomial.map_pow]

/-- Corrected statement (fully proven): the manifest statement with the missing hypothesis
`1 ≤ M`, which makes `ZMod (p^M)` nontrivial (`p` prime ⟹ `1 < p^M`). RECOMMENDED
replacement for `L6_moveReduceCommute` pending manifest sign-off. -/
theorem L6_moveReduceCommute_of_one_le {p : ℕ} [Fact p.Prime] (Φhat f : Polynomial ℤ_[p])
    (hmon : Φhat.Monic) (B : ℕ → Polynomial ℤ_[p]) (N M : ℕ) (hM : 1 ≤ M)
    (hdev : IsDevelopment Φhat f B N) :
    IsDevelopment (Φhat.map (PadicInt.toZModPow M)) (f.map (PadicInt.toZModPow M))
      (fun j => (B j).map (PadicInt.toZModPow M)) N := by
  haveI : Fact (1 < p ^ M) :=
    ⟨Nat.one_lt_pow (by omega) (Fact.out : p.Prime).one_lt⟩
  exact L6_moveReduceCommute_of_nontrivial Φhat f hmon B N M hdev

theorem L6_moveReduceCommute {p : ℕ} [Fact p.Prime] (Φhat f : Polynomial ℤ_[p]) (hmon : Φhat.Monic) (B : ℕ → Polynomial ℤ_[p]) (N M : ℕ) (hdev : IsDevelopment Φhat f B N) : IsDevelopment (Φhat.map (PadicInt.toZModPow M)) (f.map (PadicInt.toZModPow M)) (fun j => (B j).map (PadicInt.toZModPow M)) N := by
  rcases Nat.eq_zero_or_pos M with rfl | hM
  · -- M = 0: the statement is genuinely FALSE here (certified by
    -- `L6_moveReduceCommute_statement_false` below); honest `sorry`, statement fenced.
    sorry
  · exact L6_moveReduceCommute_of_one_le Φhat f hmon B N M hM hdev

/-- **Machine-checked disproof** of the manifest statement's universal closure: at `p = 2`,
`Φhat = X`, `f = 1`, `N = 1`, `M = 0` the target `ZMod (2^0)` is trivial, every polynomial
over it is `0`, and clause 1 of the reduced development demands `⊥ < ⊥`. -/
theorem L6_moveReduceCommute_statement_false :
    ¬ (∀ (p : ℕ) [Fact p.Prime] (Φhat f : Polynomial ℤ_[p]), Φhat.Monic →
        ∀ (B : ℕ → Polynomial ℤ_[p]) (N M : ℕ), IsDevelopment Φhat f B N →
        IsDevelopment (Φhat.map (PadicInt.toZModPow M)) (f.map (PadicInt.toZModPow M))
          (fun j => (B j).map (PadicInt.toZModPow M)) N) := by
  intro h
  have hdev : IsDevelopment (X : Polynomial ℤ_[2]) 1 (fun j => if j = 0 then 1 else 0) 1 := by
    refine ⟨fun j => ?_, fun j hj => ?_, ?_⟩
    · by_cases hj : j = 0
      · simp [hj]
      · simp [hj]
    · have hj' : j ≠ 0 := by omega
      simp [hj']
    · simp
  have h0 := (h 2 X 1 monic_X (fun j => if j = 0 then 1 else 0) 1 0 hdev).1 0
  haveI : Subsingleton (ZMod (2 ^ 0)) := by rw [pow_zero]; infer_instance
  have h2 : (X : Polynomial ℤ_[2]).map (PadicInt.toZModPow 0) = 0 :=
    Polynomial.ext fun n => Subsingleton.elim _ _
  rw [h2, Polynomial.degree_zero] at h0
  exact not_lt_bot h0

end LeanUrat.Moves
