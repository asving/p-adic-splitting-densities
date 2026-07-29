/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.MovesT.Defs

/-! # T-V7 `vdAt_finite` — W4-2's `hVfin` instantiable at V := VdAt n, AND the
singleton-V degeneracy REJECTED (W4-2(b)(i)): at d ≥ 2, {(1,d)} ≠ {(d,1)}. -/

set_option linter.style.longLine false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesT

open Polynomial LeanUrat.Moves LeanUrat.MovesC LeanUrat.MovesD

/-- a verdict of deg d has ≤ d pairs, each in [1,d]²; inject into a finite carrier. -/
instance vdAt_finite (d : ℕ) : Finite (VdAt d) := by
  -- each pair of a deg-d verdict lands in the box [1,d]²
  have hbound : ∀ (v : VdAt d) (a : ℕ × ℕ), a ∈ v.1.1 → a.1 ≤ d ∧ a.2 ≤ d := by
    intro v a ha
    have hverd := v.1.2 a ha
    have hdeg : (v.1.1.map fun ef => ef.1 * ef.2).sum = d := v.2
    have hmem : a.1 * a.2 ∈ v.1.1.map fun ef => ef.1 * ef.2 :=
      Multiset.mem_map.mpr ⟨a, ha, rfl⟩
    have hle : a.1 * a.2 ≤ (v.1.1.map fun ef => ef.1 * ef.2).sum :=
      Multiset.single_le_sum (fun x _ => Nat.zero_le x) _ hmem
    rw [hdeg] at hle
    refine ⟨?_, ?_⟩
    · nlinarith [hle, hverd.2, Nat.zero_le a.1]
    · nlinarith [hle, hverd.1, Nat.zero_le a.2]
  -- a deg-d verdict carries at most d pairs
  have hcard : ∀ (v : VdAt d), v.1.1.card ≤ d := by
    intro v
    have hdeg : (v.1.1.map fun ef => ef.1 * ef.2).sum = d := v.2
    have hmpos : ∀ x ∈ v.1.1.map fun ef => ef.1 * ef.2, 1 ≤ x := by
      intro x hx
      rw [Multiset.mem_map] at hx
      obtain ⟨gm, hgm, rfl⟩ := hx
      have := v.1.2 gm hgm
      exact Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
    have hcs := Multiset.card_nsmul_le_sum hmpos
    rw [hdeg, Multiset.card_map] at hcs
    simpa using hcs
  -- hence each pair-count is < d + 1
  have hlt : ∀ (v : VdAt d) (p : Fin (d + 1) × Fin (d + 1)),
      v.1.1.count (p.1.val, p.2.val) < d + 1 := by
    intro v p
    have h1 : v.1.1.count (p.1.val, p.2.val) ≤ v.1.1.card := Multiset.count_le_card _ _
    have h2 := hcard v
    omega
  -- inject into the finite function type of box-counts
  refine Finite.of_injective
    (fun (v : VdAt d) (p : Fin (d + 1) × Fin (d + 1)) =>
      (⟨v.1.1.count (p.1.val, p.2.val), hlt v p⟩ : Fin (d + 1))) ?_
  intro v w hvw
  have hcount : ∀ (a : ℕ × ℕ), a.1 ≤ d → a.2 ≤ d →
      v.1.1.count a = w.1.1.count a := by
    intro a ha1 ha2
    have hq := congrFun hvw (⟨a.1, by omega⟩, ⟨a.2, by omega⟩)
    have hval := congrArg Fin.val hq
    simpa using hval
  have hmeq : v.1.1 = w.1.1 := by
    refine Multiset.ext.mpr ?_
    intro a
    by_cases hbox : a.1 ≤ d ∧ a.2 ≤ d
    · exact hcount a hbox.1 hbox.2
    · have hv0 : v.1.1.count a = 0 := by
        rw [Multiset.count_eq_zero]; intro ha; exact hbox (hbound v a ha)
      have hw0 : w.1.1.count a = 0 := by
        rw [Multiset.count_eq_zero]; intro ha; exact hbox (hbound w a ha)
      rw [hv0, hw0]
  exact Subtype.ext (Subtype.ext hmeq)

theorem vdAt_nontrivial (d : ℕ) (hd : 2 ≤ d) : 1 < Nat.card (VdAt d) := by
  have hd1 : (1 : ℕ) ≤ d := by omega
  -- the two displayed witnesses {(1,d)} and {(d,1)}
  have hdeg1 : (henVerdict d hd1).deg = d := by
    simp [Vd.deg, henVerdict]
  have hdeg2 : (irrVerdict d 1 hd1 le_rfl).deg = d := by
    simp [Vd.deg, irrVerdict]
  let v1 : VdAt d := ⟨henVerdict d hd1, hdeg1⟩
  let v2 : VdAt d := ⟨irrVerdict d 1 hd1 le_rfl, hdeg2⟩
  have hne : v1 ≠ v2 := by
    intro h
    have hm : ({(1, d)} : Multiset (ℕ × ℕ)) = {(d, 1)} := congrArg (fun x => x.1.1) h
    have hpair : ((1, d) : ℕ × ℕ) = (d, 1) := Multiset.singleton_inj.mp hm
    have : (1 : ℕ) = d := (Prod.ext_iff.mp hpair).1
    omega
  have : Nontrivial (VdAt d) := ⟨v1, v2, hne⟩
  exact Finite.one_lt_card_iff_nontrivial.mpr this

end LeanUrat.MovesT
