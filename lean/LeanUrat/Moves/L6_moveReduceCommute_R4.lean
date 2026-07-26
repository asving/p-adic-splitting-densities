/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.Moves.Defs
import LeanUrat.Moves.DefsT
import LeanUrat.Moves.DefsCore

/-!
# Moves/L6_moveReduceCommute_R4 — development commutes with reduction mod p^M (§0 Fact A / D.11)

ROUND-4 unit. The R3 manifest statement was machine-checked FALSE at `M = 0` (target ring
`ZMod (p^0) = ZMod 1` is trivial, so both mapped polynomials vanish and clause 1 of
`IsDevelopment` demands `⊥ < ⊥`). The corrected R4 statement adds `hM : 1 ≤ M`, which makes
`ZMod (p^M)` nontrivial (`p` prime ⟹ `1 < p^M`). Fully proven, no `sorry`, no new axioms.
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option maxHeartbeats 400000

open Polynomial LeanUrat.Moves

namespace LeanUrat.Moves

theorem L6_moveReduceCommute {p : ℕ} [Fact p.Prime] (Φhat f : Polynomial ℤ_[p]) (hmon : Φhat.Monic) (B : ℕ → Polynomial ℤ_[p]) (N M : ℕ) (hM : 1 ≤ M) (hdev : IsDevelopment Φhat f B N) : IsDevelopment (Φhat.map (PadicInt.toZModPow M)) (f.map (PadicInt.toZModPow M)) (fun j => (B j).map (PadicInt.toZModPow M)) N := by
  haveI : Fact (1 < p ^ M) :=
    ⟨Nat.one_lt_pow (by omega) (Fact.out : p.Prime).one_lt⟩
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

end LeanUrat.Moves
