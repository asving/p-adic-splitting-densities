/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.HC1.DefsD

/-!
# HC1.D1_carryRing — 𝒟 is a commutative ring under the twisted convolution

moves_ref: MOVES 1508–1511 "𝒟 ≅ F_{r+1}[u]/(u^e − z̄), a strongly graded twisted
algebra". The ring structure (product `cmul zbar`, pointwise addition, unit
`dOf 0 1`) packaged as `CarryRingPack` (DefsD); associativity reduces to the cocycle
identity `carryExp ρ σ + carryExp (ρ+σ) τ = carryExp σ τ + carryExp ρ (σ+τ)`.
difficulty: medium. hyp: none.
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

namespace LeanUrat.HC1

open scoped BigOperators

variable {F : Type*} [Field F] {e : ℕ} [NeZero e]

/-- the child valuation `(a+b).val` recovered from `a.val + b.val` and the carry
indicator: `(a+b).val + e · carry = a.val + b.val` (no ℕ-subtraction on the face). -/
private lemma val_add_carry (a b : ZMod e) :
    (a + b).val + e * (if e ≤ a.val + b.val then 1 else 0) = a.val + b.val := by
  rw [ZMod.val_add]
  have ha := ZMod.val_lt a
  have hb := ZMod.val_lt b
  split_ifs with h
  · rw [Nat.mod_eq_sub_mod h, Nat.mod_eq_of_lt (by omega)]; omega
  · rw [Nat.mod_eq_of_lt (by omega)]; omega

/-- `carryExp` is symmetric (it depends only on `ρ.val + σ.val`). -/
private lemma carryExp_comm (ρ σ : ZMod e) : carryExp ρ σ = carryExp σ ρ := by
  unfold carryExp; rw [Nat.add_comm]

/-- the 2-cocycle identity — the heart of associativity. -/
private lemma carryExp_cocycle (a b c : ZMod e) :
    carryExp a b + carryExp (a + b) c = carryExp b c + carryExp a (b + c) := by
  have hab := val_add_carry a b
  have hbc := val_add_carry b c
  have ha := ZMod.val_lt a
  have hb := ZMod.val_lt b
  have hc := ZMod.val_lt c
  have hab2 := ZMod.val_lt (a + b)
  have hbc2 := ZMod.val_lt (b + c)
  unfold carryExp
  split_ifs at hab hbc ⊢ <;> omega

/-- `carryExp ρ (τ - ρ) = 0` when the "carry" cannot fire (used for the unit). -/
private lemma carryExp_zero_left (τ : ZMod e) : carryExp (0 : ZMod e) τ = 0 := by
  have hlt := ZMod.val_lt τ
  unfold carryExp
  simp only [ZMod.val_zero, Nat.zero_add]
  split_ifs with h
  · omega
  · rfl

/-- twisted convolution is commutative. -/
private lemma cmul_comm (zbar : Fˣ) (x y : CarryAlg F e) :
    cmul zbar x y = cmul zbar y x := by
  funext τ
  simp only [cmul]
  refine Fintype.sum_equiv (Equiv.subLeft τ) _ _ (fun ρ => ?_)
  simp only [Equiv.subLeft_apply, sub_sub_cancel]
  rw [carryExp_comm ρ (τ - ρ)]
  ring

/-- `dOf 0 1` is a left unit for the twisted convolution. -/
private lemma one_cmul (zbar : Fˣ) (y : CarryAlg F e) :
    cmul zbar (dOf (0 : ZMod e) 1) y = y := by
  funext τ
  simp only [cmul]
  rw [Fintype.sum_eq_single (0 : ZMod e)]
  · simp only [dOf, Pi.single_eq_same, sub_zero, one_mul, carryExp_zero_left, pow_zero, mul_one]
  · intro ρ hρ
    simp only [dOf, Pi.single_eq_of_ne hρ, zero_mul]

/-- `dOf 0 1` is a right unit. -/
private lemma cmul_one (zbar : Fˣ) (y : CarryAlg F e) :
    cmul zbar y (dOf (0 : ZMod e) 1) = y := by
  rw [cmul_comm]; exact one_cmul zbar y

/-- left distributivity. -/
private lemma cmul_add (zbar : Fˣ) (x y z : CarryAlg F e) :
    cmul zbar x (y + z) = cmul zbar x y + cmul zbar x z := by
  funext τ
  have hadd : ∀ w : ZMod e, (y + z) w = y w + z w := fun _ => rfl
  show cmul zbar x (y + z) τ = cmul zbar x y τ + cmul zbar x z τ
  simp only [cmul, hadd]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro ρ _
  ring

/-- right distributivity. -/
private lemma add_cmul (zbar : Fˣ) (x y z : CarryAlg F e) :
    cmul zbar (x + y) z = cmul zbar x z + cmul zbar y z := by
  rw [cmul_comm, cmul_add, cmul_comm zbar z x, cmul_comm zbar z y]

/-- left annihilator. -/
private lemma zero_cmul (zbar : Fˣ) (y : CarryAlg F e) :
    cmul zbar 0 y = 0 := by
  funext τ
  have hz : ∀ w : ZMod e, (0 : CarryAlg F e) w = 0 := fun _ => rfl
  show cmul zbar 0 y τ = (0 : F)
  simp only [cmul, hz, zero_mul, Finset.sum_const_zero]

/-- right annihilator. -/
private lemma cmul_zero (zbar : Fˣ) (x : CarryAlg F e) :
    cmul zbar x 0 = 0 := by
  rw [cmul_comm]; exact zero_cmul zbar x

/-- the reindexing bijection `(ρ, σ) ↦ (σ, ρ - σ)` used for associativity. -/
private def reidx (e : ℕ) : ZMod e × ZMod e ≃ ZMod e × ZMod e :=
  { toFun := fun p => (p.2, p.1 - p.2)
    invFun := fun q => (q.1 + q.2, q.1)
    left_inv := by rintro ⟨a, b⟩; simp only [Prod.mk.injEq, and_true]; abel
    right_inv := by rintro ⟨a, b⟩; simp only [Prod.mk.injEq, true_and]; abel }

/-- twisted convolution is associative — via the cocycle identity + the reindex. -/
private lemma cmul_assoc (zbar : Fˣ) (x y z : CarryAlg F e) :
    cmul zbar (cmul zbar x y) z = cmul zbar x (cmul zbar y z) := by
  funext τ
  simp only [cmul]
  simp only [Finset.sum_mul, Finset.mul_sum]
  rw [← Fintype.sum_prod_type', ← Fintype.sum_prod_type']
  refine Fintype.sum_equiv (reidx e) _ _ (fun p => ?_)
  obtain ⟨ρ, σ⟩ := p
  simp only [reidx, Equiv.coe_fn_mk]
  rw [sub_sub_sub_cancel_right]
  have h1 : σ + (ρ - σ) = ρ := by abel
  have h2 : (ρ - σ) + (τ - ρ) = τ - σ := by abel
  have hcoc := carryExp_cocycle σ (ρ - σ) (τ - ρ)
  rw [h1, h2] at hcoc
  calc x σ * y (ρ - σ) * (zbar : F) ^ carryExp σ (ρ - σ) * z (τ - ρ)
          * (zbar : F) ^ carryExp ρ (τ - ρ)
      = (x σ * y (ρ - σ) * z (τ - ρ))
          * ((zbar : F) ^ carryExp σ (ρ - σ) * (zbar : F) ^ carryExp ρ (τ - ρ)) := by ring
    _ = (x σ * y (ρ - σ) * z (τ - ρ))
          * ((zbar : F) ^ carryExp (ρ - σ) (τ - ρ) * (zbar : F) ^ carryExp σ (τ - σ)) := by
        rw [← pow_add, ← pow_add, hcoc]
    _ = x σ * (y (ρ - σ) * z (τ - ρ) * (zbar : F) ^ carryExp (ρ - σ) (τ - ρ))
          * (zbar : F) ^ carryExp σ (τ - σ) := by ring

/-- Unit D1: the carry algebra carries a commutative ring structure whose product is
the twisted convolution, addition pointwise, unit `dOf 0 1` (the ring depends on
`zbar`). -/
theorem D1_carryRing (F : Type*) [Field F] (e : ℕ) [NeZero e] (zbar : Fˣ) :
    Nonempty (CarryRingPack F e zbar) := by
  letI ring : CommRing (CarryAlg F e) :=
    { (inferInstance : AddCommGroup (CarryAlg F e)) with
      mul := cmul zbar
      one := dOf 0 1
      mul_assoc := cmul_assoc zbar
      one_mul := one_cmul zbar
      mul_one := cmul_one zbar
      left_distrib := cmul_add zbar
      right_distrib := add_cmul zbar
      mul_comm := cmul_comm zbar
      zero_mul := zero_cmul zbar
      mul_zero := cmul_zero zbar }
  exact ⟨{ ring := ring
           mul_def := fun _ _ => rfl
           add_def := fun _ _ _ => rfl
           one_def := rfl }⟩

end LeanUrat.HC1

#print axioms LeanUrat.HC1.D1_carryRing
