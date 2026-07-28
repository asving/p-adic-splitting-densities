/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.HC1.DefsCar
import LeanUrat.HC1.C2_TYPa

/-!
# HC1.T11_attainDichotomy — pinning the composite is solvable iff on-alphabet

moves_ref: MOVES 2165–2168 "Pinning d_γ(B) = X is solvable iff X ∈ 𝔸(γ) — an
off-alphabet pin EMPTIES the locus". deps: T7, T8. difficulty: easy. hyp: none.
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

namespace LeanUrat.HC1

open Polynomial LeanUrat.Moves
open scoped Classical

/-- The level set `L_γ(b)` is finite: the top slot is pinned to `b`, the interior
slots are bounded by the key-degree ratios, and the p-adic level `l` is then forced
by `ht c = γ`, so `c ↦ c.slot` is injective on `L_γ(b)` with finite image. -/
theorem levelSet_finite {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
    (T : Tower p F) (b : ℕ) (γ : ℚ) : (T.levelSet b γ).Finite := by
  refine Set.Finite.of_finite_image (f := fun c : T.Coord => c.slot) ?_ ?_
  · -- the slot vectors of the level set live in a finite product of `Iio`
    refine Set.Finite.subset (Set.Finite.pi (fun _ : Fin (T.K + 1) =>
      Set.finite_Iio (b + 1 + ∑ r, T.slotBound r))) ?_
    rw [Set.image_subset_iff]
    rintro c ⟨hblk, _hht⟩
    simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, Set.mem_Iio, forall_true_left]
    intro i
    rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
    · calc c.slot j.castSucc < T.slotBound j := c.slot_lt j
        _ ≤ ∑ r, T.slotBound r :=
              Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
        _ ≤ b + 1 + ∑ r, T.slotBound r := Nat.le_add_left _ _
    · have hb : c.slot (Fin.last T.K) = b := hblk
      rw [hb]
      calc b < b + 1 := Nat.lt_succ_self b
        _ ≤ b + 1 + ∑ r, T.slotBound r := Nat.le_add_right _ _
  · -- `c ↦ c.slot` is injective on the level set: `ht = γ` forces `l`
    rintro c hc c' hc' hslot
    have hl : c.l = c'.l := by
      have key : T.ht c = T.ht c' := hc.2.trans hc'.2.symm
      simp only [Tower.ht, hslot] at key
      exact_mod_cast add_right_cancel key
    obtain ⟨l1, s1, p1⟩ := c
    obtain ⟨l2, s2, p2⟩ := c'
    dsimp only at hl hslot
    subst hl; subst hslot; rfl

/-- Unit T11: the attainability dichotomy. Since `typComposite` is additive in the
digit tuple (C2/TYP(a)), it is an additive homomorphism whose range is exactly the
alphabet (the additive closure of the single-coordinate slot images): a pin is
solvable iff its value lies in the alphabet, an off-alphabet pin empties the locus,
and a zero pin is always solvable (`0 ∈ 𝔸`). -/
theorem T11_attainDichotomy {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
    (T : Tower p F) (b : ℕ) (γ : ℚ) (X : T.grQ γ) :
    ((∃ y : ↥(T.levelSet b γ) → ↥(T.stg 0).FQ, T.typComposite b γ y = X) ↔
      X ∈ T.alphabet b γ) ∧
    (X ∉ T.alphabet b γ →
      {y : ↥(T.levelSet b γ) → ↥(T.stg 0).FQ | T.typComposite b γ y = X} = ∅) ∧
    (0 : T.grQ γ) ∈ T.alphabet b γ := by
  -- Additivity of the composite in the digit tuple (C2/TYP(a), second leg).
  have hadd := (C2_TYPa T b γ).2
  -- Bundle it as an additive homomorphism.
  set φ : (↥(T.levelSet b γ) → ↥(T.stg 0).FQ) →+ T.grQ γ :=
    AddMonoidHom.mk' (T.typComposite b γ) hadd with hφ
  -- The level set is finite, so every assignment is a finite sum of single-slot ones.
  haveI : Fintype ↥(T.levelSet b γ) := (levelSet_finite T b γ).fintype
  -- Each single-coordinate image is a generator of the alphabet.
  have hgen : ∀ (c : ↥(T.levelSet b γ)) (v : ↥(T.stg 0).FQ),
      T.typComposite b γ (Pi.single c v) ∈ T.alphabet b γ := by
    intro c v
    apply AddSubgroup.subset_closure
    exact Set.mem_iUnion.mpr ⟨c, Set.mem_range.mpr ⟨v, rfl⟩⟩
  -- Forward: every attained value lies in the alphabet.
  have hfwd : ∀ y : ↥(T.levelSet b γ) → ↥(T.stg 0).FQ,
      T.typComposite b γ y ∈ T.alphabet b γ := by
    intro y
    have decomp : T.typComposite b γ y
        = ∑ c, T.typComposite b γ (Pi.single c (y c)) := by
      conv_lhs => rw [← Finset.univ_sum_single y]
      exact map_sum φ (fun c => Pi.single c (y c)) Finset.univ
    rw [decomp]
    exact AddSubgroup.sum_mem _ (fun c _ => hgen c (y c))
  -- Backward: the alphabet sits inside the range of the homomorphism.
  have hbwd : X ∈ T.alphabet b γ → ∃ y, T.typComposite b γ y = X := by
    intro hX
    have hsub : T.alphabet b γ ≤ φ.range := by
      apply (AddSubgroup.closure_le _).mpr
      rintro x hx
      simp only [Set.mem_iUnion, Set.mem_range] at hx
      obtain ⟨c, v, rfl⟩ := hx
      exact ⟨Pi.single c v, rfl⟩
    exact AddMonoidHom.mem_range.mp (hsub hX)
  refine ⟨⟨?_, hbwd⟩, ?_, (T.alphabet b γ).zero_mem⟩
  · rintro ⟨y, rfl⟩
    exact hfwd y
  · intro hX
    rw [Set.eq_empty_iff_forall_notMem]
    intro y hy
    exact hX (hy ▸ hfwd y)

end LeanUrat.HC1

#print axioms LeanUrat.HC1.T11_attainDichotomy
