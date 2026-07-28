/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.HC1.DefsCar
import LeanUrat.HC1.C2_TYPa
import LeanUrat.HC1.T12_coordFin

/-!
# HC1.C3_TYPb — TYP(b): image = alphabet, equipotent fibers, exact |𝔸|⁻¹ cut

moves_ref: MOVES 3813–3824 "additive with image = the additive span of the slot
images … An additive surjection onto its image has equal-size fibers (kernel
cosets), so the clause cuts exactly (alphabet)^{−1}". deps: C2, T7, T8.
difficulty: medium. hyp: none.
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

namespace LeanUrat.HC1

open Polynomial LeanUrat.Moves

/-- Unit C3: the composite's image is the alphabet; fibers over the image are
equipotent; a fresh value clause at exact valuation γ' cuts exactly |𝔸|⁻¹ among
level-set assignments (division-free). -/
theorem C3_TYPb {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
    (T : Tower p F) (b : ℕ) (γ' : ℚ) :
    (Set.range (T.typComposite b γ') = ↑(T.alphabet b γ')) ∧
    (∀ X X' : T.grQ γ', X ∈ T.alphabet b γ' → X' ∈ T.alphabet b γ' →
      Nat.card {y : ↥(T.levelSet b γ') → ↥(T.stg 0).FQ // T.typComposite b γ' y = X}
        = Nat.card {y : ↥(T.levelSet b γ') → ↥(T.stg 0).FQ // T.typComposite b γ' y = X'}) ∧
    (∀ X : T.grQ γ', X ∈ T.alphabet b γ' →
      Nat.card {y : ↥(T.levelSet b γ') → ↥(T.stg 0).FQ // T.typComposite b γ' y = X}
          * Nat.card ↥(T.alphabet b γ')
        = Nat.card (↥(T.levelSet b γ') → ↥(T.stg 0).FQ)) := by
  classical
  -- (0) The level set is finite: `blk = b` pins the top slot, and `ht = γ'` bounds
  -- the p-adic level `l` (all inner slots are already bounded by `slot_lt`).  So it
  -- sits inside one of T12's finite level-N boxes.
  have hfin : (T.levelSet b γ').Finite := by
    apply Set.Finite.subset (T12_coordFin T (⌊γ'⌋₊ + 1) (b + 1)).1
    rintro c ⟨hblk, hht⟩
    refine ⟨?_, ?_⟩
    · -- `c.l < ⌊γ'⌋₊ + 1` from `ht c = γ'` and the nonnegative slot sum
      have hht' : (c.l : ℚ) + ∑ r, (c.slot r : ℚ) * T.kappa r = γ' := hht
      have hS : (0 : ℚ) ≤ ∑ r, (c.slot r : ℚ) * T.kappa r :=
        Finset.sum_nonneg fun r _ =>
          mul_nonneg (Nat.cast_nonneg _)
            (by
              have hk : T.kappa r
                  = ((T.stg r).h : ℚ) / (((T.stg r).e : ℚ) * (T.str r : ℚ)) := rfl
              rw [hk]
              exact div_nonneg (Nat.cast_nonneg _)
                (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)))
      have hle : (c.l : ℚ) ≤ γ' := by linarith
      exact Nat.lt_succ_of_le (Nat.le_floor hle)
    · -- the top slot equals `b`, hence `< b + 1`
      have hb : c.slot (Fin.last T.K) = b := hblk
      omega
  haveI : Finite ↥(T.levelSet b γ') := hfin.to_subtype
  haveI : Fintype ↥(T.levelSet b γ') := Fintype.ofFinite _
  -- (1) The composite is a genuine additive homomorphism (C2's additivity leg).
  have hadd := (C2_TYPa T b γ').2
  let φ : (↥(T.levelSet b γ') → ↥(T.stg 0).FQ) →+ T.grQ γ' :=
    AddMonoidHom.mk' (T.typComposite b γ') hadd
  have hcoe : ⇑φ = T.typComposite b γ' := AddMonoidHom.mk'_apply _ _
  -- (2) The range of `φ` is exactly the alphabet subgroup.
  have hrange : φ.range = T.alphabet b γ' := by
    apply le_antisymm
    · -- `range ⊆ alphabet`: any `y` is the finite sum of its single-coordinate parts
      rintro x hx
      obtain ⟨y, rfl⟩ := AddMonoidHom.mem_range.mp hx
      have hy : (∑ c, Pi.single c (y c)) = y := Finset.univ_sum_single y
      rw [← hy, map_sum]
      apply AddSubgroup.sum_mem
      intro c _
      have hmem : φ (Pi.single c (y c))
          ∈ (⋃ c' : ↥(T.levelSet b γ'),
              Set.range fun v : ↥(T.stg 0).FQ => T.typComposite b γ' (Pi.single c' v)) := by
        rw [Set.mem_iUnion]
        exact ⟨c, y c, rfl⟩
      exact AddSubgroup.subset_closure hmem
    · -- `alphabet ⊆ range`: each generator is manifestly a value of `φ`
      show AddSubgroup.closure _ ≤ φ.range
      refine (AddSubgroup.closure_le _).mpr ?_
      rintro x hx
      rw [Set.mem_iUnion] at hx
      obtain ⟨c, v, rfl⟩ := hx
      rw [SetLike.mem_coe, AddMonoidHom.mem_range]
      exact ⟨Pi.single c v, rfl⟩
  -- (3) Every fiber over the range is a coset of the kernel, hence ≃ the kernel.
  have fiber_ker : ∀ X : T.grQ γ', X ∈ φ.range →
      Nat.card {y : ↥(T.levelSet b γ') → ↥(T.stg 0).FQ // T.typComposite b γ' y = X}
        = Nat.card ↥φ.ker := by
    intro X hX
    obtain ⟨y0, hy0⟩ := AddMonoidHom.mem_range.mp hX
    refine Nat.card_congr ?_
    refine ⟨fun y => ⟨y.1 - y0, ?_⟩, fun k => ⟨k.1 + y0, ?_⟩, ?_, ?_⟩
    · rw [AddMonoidHom.mem_ker, map_sub]
      have hyX : φ y.1 = X := y.2
      rw [hyX, hy0, sub_self]
    · show φ (k.1 + y0) = X
      rw [map_add, (AddMonoidHom.mem_ker.mp k.2), hy0, zero_add]
    · intro y
      apply Subtype.ext
      show (y.1 - y0) + y0 = y.1
      rw [sub_add_cancel]
    · intro k
      apply Subtype.ext
      show (k.1 + y0) - y0 = k.1
      rw [add_sub_cancel_right]
  refine ⟨by rw [← hcoe, ← AddMonoidHom.coe_range, hrange], ?_, ?_⟩
  · -- equipotent fibers: both cards equal `#ker`
    intro X X' hX hX'
    rw [fiber_ker X (by rw [hrange]; exact hX), fiber_ker X' (by rw [hrange]; exact hX')]
  · -- the exact cut: `#fiber · #alphabet = #domain` (kernel × range Lagrange)
    intro X hX
    rw [fiber_ker X (by rw [hrange]; exact hX), ← hrange,
      ← Nat.card_congr (QuotientAddGroup.quotientKerEquivRange φ).toEquiv, mul_comm,
      ← AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup]

end LeanUrat.HC1

#print axioms LeanUrat.HC1.C3_TYPb
