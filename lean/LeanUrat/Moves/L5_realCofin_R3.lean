/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.Moves.Defs
import LeanUrat.Moves.DefsT

/-!
# Moves/L5 — real cofiniteness (MOVES §D.9(b), ~2388-2391)  [ROUND 3]

Weaker (audit-relabeled) cofiniteness: threshold `W₀ + e·h`, not the sharp
`W₀ + (e-1)·h`.  For `gcd(e,h)=1` the residues `{j·h mod e : 0 ≤ j < e}` are all
residues mod `e`, so every `W ≥ W₀ + e·h` decomposes as `e·m + j·h` with `j < e`
and `e·m ≥ W₀`.  Pure number theory (Bézout / `ZMod e` inversion).
-/

open Polynomial LeanUrat.Moves

namespace LeanUrat.Moves

set_option linter.style.longLine false
set_option linter.style.header false
set_option maxHeartbeats 400000

theorem L5_realCofin (e h : ℕ) (hcop : Nat.gcd e h = 1) (he : 1 ≤ e) (W₀ W : ℤ) (hW : W₀ + (e : ℤ) * (h : ℤ) ≤ W) : ∃ (j : ℕ) (m : ℤ), j < e ∧ W₀ ≤ (e : ℤ) * m ∧ W = (e : ℤ) * m + (j : ℤ) * (h : ℤ) := by
  have he0 : e ≠ 0 := by omega
  haveI : NeZero e := ⟨he0⟩
  have hcop' : Nat.Coprime h e := Nat.Coprime.symm hcop
  have hunit : IsUnit (h : ZMod e) := (ZMod.isUnit_iff_coprime h e).mpr hcop'
  set jbar : ZMod e := (W : ZMod e) * (h : ZMod e)⁻¹ with hjbar
  have hjlt : jbar.val < e := ZMod.val_lt jbar
  have hcast : ((jbar.val : ℕ) : ZMod e) = jbar := ZMod.natCast_zmod_val jbar
  have hWeq : (W : ZMod e) = (jbar.val : ZMod e) * (h : ZMod e) := by
    rw [hcast, hjbar, mul_assoc, ZMod.inv_mul_of_unit _ hunit, mul_one]
  have hdvd : (e : ℤ) ∣ (W - (jbar.val : ℤ) * (h : ℤ)) := by
    have hz : ((W - (jbar.val : ℤ) * (h : ℤ) : ℤ) : ZMod e) = 0 := by
      push_cast
      rw [hWeq]; ring
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ e).mp hz
  obtain ⟨m, hm⟩ := hdvd
  refine ⟨jbar.val, m, hjlt, ?_, ?_⟩
  · have hjle : (jbar.val : ℤ) ≤ (e : ℤ) := by exact_mod_cast (le_of_lt hjlt)
    have hh0 : (0 : ℤ) ≤ (h : ℤ) := Int.natCast_nonneg h
    have hjh : (jbar.val : ℤ) * (h : ℤ) ≤ (e : ℤ) * (h : ℤ) :=
      mul_le_mul_of_nonneg_right hjle hh0
    linarith [hm, hjh, hW]
  · linarith [hm]

end LeanUrat.Moves
