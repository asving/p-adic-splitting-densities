/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.HC1.DefsD

/-!
# HC1.D4_carryAdjoinRoot — 𝒟 ≃+* F[u]/(u^e − z̄)

moves_ref: MOVES 1509 "𝒟 ≅ F_{r+1}[u]/(u^e − z̄)". deps: D1, D2.
difficulty: medium. hyp: none.
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

namespace LeanUrat.HC1

open Polynomial

variable {F : Type*} [Field F] {e : ℕ} [NeZero e] {zbar : Fˣ}

/-- The homogeneous product law of `𝒟`, derived directly from the carry-ring
interface (D2's first conjunct, re-proved here so D4 does not depend on D2's file). -/
private theorem dOf_mul (P : CarryRingPack F e zbar) (ρ σ : ZMod e) (c c' : F) :
    (letI := P.ring; dOf ρ c * dOf σ c')
      = dOf (ρ + σ) (c * c' * (zbar : F) ^ carryExp ρ σ) := by
  letI := P.ring
  rw [P.mul_def]
  funext τ
  simp only [cmul, dOf]
  rw [Finset.sum_eq_single ρ]
  · simp only [Pi.single_eq_same]
    by_cases hτ : τ = ρ + σ
    · subst hτ; simp only [add_sub_cancel_left, Pi.single_eq_same]
    · rw [Pi.single_eq_of_ne (show τ - ρ ≠ σ from fun h => hτ (sub_eq_iff_eq_add'.mp h)),
        Pi.single_eq_of_ne hτ]
      ring
  · intro b _ hb
    rw [Pi.single_eq_of_ne hb]; ring
  · intro h; exact absurd (Finset.mem_univ ρ) h

/-- Powers of the graded generator `u = dOf 1 z̄^{⌊1/e⌋}`: `u^n = z̄^{⌊n/e⌋}·u_{n mod e}`.
The carry exponent identity `n/e + 1/e + carry = (n+1)/e` is exactly `Nat.add_div`
(the choice of scalar `z̄^{⌊1/e⌋}` makes the formula uniform, including `e = 1`). -/
private theorem powU (P : CarryRingPack F e zbar) :
    ∀ n : ℕ, (letI := P.ring;
      (dOf (1 : ZMod e) ((zbar : F) ^ (1 / e))) ^ n
        = dOf (↑n) ((zbar : F) ^ (n / e))) := by
  letI := P.ring
  have e_pos : 0 < e := Nat.pos_of_ne_zero (NeZero.ne e)
  intro n
  induction n with
  | zero => simp only [pow_zero, Nat.cast_zero, Nat.zero_div]; exact P.one_def
  | succ n ih =>
    rw [pow_succ, ih, dOf_mul]
    have hpos : ((n + 1 : ℕ) : ZMod e) = (↑n + 1) := by push_cast; ring
    rw [hpos]
    congr 1
    rw [← pow_add, ← pow_add]
    congr 1
    have hcarry : carryExp (↑n : ZMod e) (1 : ZMod e)
        = if e ≤ n % e + 1 % e then 1 else 0 := by
      simp only [carryExp, ZMod.val_natCast, ZMod.val_one_eq_one_mod]
    rw [hcarry, Nat.add_div e_pos]

/-- Unit D4: the ring iso `CarryAlg F e ≃+* AdjoinRoot (X^e − C z̄)` sending
`dOf ρ c ↦ c·u^{ρ.val}` (e ≥ 1). -/
theorem D4_carryAdjoinRoot {F : Type*} [Field F] {e : ℕ} [NeZero e] {zbar : Fˣ}
    (P : CarryRingPack F e zbar) :
    ∃ Θ : (letI := P.ring;
        CarryAlg F e ≃+* AdjoinRoot (Polynomial.X ^ e - Polynomial.C ((zbar : F)))),
      ∀ (ρ : ZMod e) (c : F),
        Θ (dOf ρ c) = algebraMap F _ c *
          AdjoinRoot.root (Polynomial.X ^ e - Polynomial.C ((zbar : F))) ^ ρ.val := by
  letI := P.ring
  have e_pos : 0 < e := Nat.pos_of_ne_zero (NeZero.ne e)
  set f : F[X] := X ^ e - C ((zbar : F)) with hf
  -- carry with 0 on the left vanishes
  have cz : ∀ σ : ZMod e, carryExp (0 : ZMod e) σ = 0 := by
    intro σ
    simp only [carryExp, ZMod.val_zero, zero_add]
    exact if_neg (Nat.not_le.mpr (ZMod.val_lt σ))
  -- P.ring's zero is the zero function
  have hz : ∀ τ : ZMod e, (0 : CarryAlg F e) τ = 0 := by
    intro τ
    have h := P.add_def 0 0 τ
    simp only [add_zero] at h
    exact left_eq_add.mp h
  -- the generator u and its powers
  set U : CarryAlg F e := dOf (1 : ZMod e) ((zbar : F) ^ (1 / e)) with hU
  have hpow : ∀ n : ℕ, U ^ n = dOf (↑n) ((zbar : F) ^ (n / e)) := by
    intro n; rw [hU]; exact powU P n
  have hA : U ^ e = dOf (0 : ZMod e) ((zbar : F)) := by
    rw [hpow e, ZMod.natCast_self, Nat.div_self e_pos, pow_one]
  have hB : ∀ ρ : ZMod e, U ^ ρ.val = dOf ρ (1 : F) := by
    intro ρ
    rw [hpow ρ.val, ZMod.natCast_zmod_val, Nat.div_eq_of_lt (ZMod.val_lt ρ), pow_zero]
  -- root^e = algebraMap z̄  (the defining relation)
  have hroot : (AdjoinRoot.root f) ^ e = algebraMap F (AdjoinRoot f) ((zbar : F)) := by
    have h : AdjoinRoot.mk f (X ^ e - C ((zbar : F))) = 0 := by
      rw [← hf]; exact AdjoinRoot.mk_self
    rw [map_sub, map_pow, AdjoinRoot.mk_X, sub_eq_zero] at h
    rw [h]; rfl
  -- image of a monomial under `mk`
  have hmk : ∀ (n : ℕ) (a : F),
      AdjoinRoot.mk f (monomial n a)
        = algebraMap F (AdjoinRoot f) a * (AdjoinRoot.root f) ^ n := by
    intro n a
    rw [← AdjoinRoot.aeval_eq, aeval_monomial]
  -- the scalar embedding i : F →+* CarryAlg  (c ↦ dOf 0 c)
  let i : F →+* CarryAlg F e :=
    { toFun := fun c => dOf 0 c
      map_one' := P.one_def.symm
      map_mul' := fun c c' => by
        rw [dOf_mul P]; simp only [cz, add_zero, pow_zero, mul_one]
      map_zero' := by
        funext τ; rw [hz τ]; simp only [dOf, Pi.single_apply, ite_self]
      map_add' := fun c c' => by
        funext τ; rw [P.add_def]; simp only [dOf, Pi.single_apply]
        split <;> simp }
  have hi : ∀ c : F, i c = dOf 0 c := fun _ => rfl
  -- the lift condition: eval₂ i U (X^e − C z̄) = U^e − i z̄ = 0
  have hlift : f.eval₂ i U = 0 := by
    rw [hf, eval₂_sub, eval₂_X_pow, eval₂_C, hA, hi]
    exact sub_self _
  -- forward ring hom (via the universal property) and the backward function on the u-basis
  let φ : AdjoinRoot f →+* CarryAlg F e := AdjoinRoot.lift i U hlift
  let ψ : CarryAlg F e → AdjoinRoot f :=
    fun x => ∑ σ : ZMod e, algebraMap F (AdjoinRoot f) (x σ) * (AdjoinRoot.root f) ^ σ.val
  have ψ_def : ∀ x, ψ x = ∑ σ : ZMod e,
      algebraMap F (AdjoinRoot f) (x σ) * (AdjoinRoot.root f) ^ σ.val := fun _ => rfl
  have φ_root : φ (AdjoinRoot.root f) = U := AdjoinRoot.lift_root hlift
  have φ_alg : ∀ c : F, φ (algebraMap F (AdjoinRoot f) c) = dOf 0 c := by
    intro c; rw [AdjoinRoot.algebraMap_eq]
    exact RingHom.congr_fun (AdjoinRoot.lift_comp_of hlift) c
  -- ψ is additive
  have ψ_add : ∀ w1 w2 : CarryAlg F e, ψ (w1 + w2) = ψ w1 + ψ w2 := by
    intro w1 w2
    rw [ψ_def, ψ_def, ψ_def, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro σ _
    rw [P.add_def, map_add, add_mul]
  -- RIGHT inverse: φ (ψ y) = y
  have hrinv : Function.RightInverse ψ φ := by
    intro y
    show φ (ψ y) = y
    rw [ψ_def, map_sum]
    have hterm : ∀ σ : ZMod e,
        φ (algebraMap F (AdjoinRoot f) (y σ) * (AdjoinRoot.root f) ^ σ.val) = dOf σ (y σ) := by
      intro σ
      rw [map_mul, map_pow, φ_alg, φ_root, hB σ, dOf_mul P, cz]
      simp only [zero_add, pow_zero, mul_one]
    rw [Finset.sum_congr rfl (fun σ _ => hterm σ)]
    -- ∑ σ, dOf σ (y σ) = y, checked pointwise via evaluation-at-τ (an additive hom out of P.ring)
    funext τ
    let evalAt : CarryAlg F e →+ F :=
      AddMonoidHom.mk' (fun x => x τ) (fun x z => P.add_def x z τ)
    have hmap := map_sum evalAt (fun ρ => dOf ρ (y ρ)) Finset.univ
    simp only [evalAt, AddMonoidHom.mk'_apply] at hmap
    rw [hmap]
    simp only [dOf, Pi.single_apply]
    rw [Finset.sum_ite_eq Finset.univ τ (fun ρ => y ρ)]
    simp
  -- LEFT inverse: ψ (φ a) = a, by induction over the polynomial presentation
  have hlinv : Function.LeftInverse ψ φ := by
    have key : ∀ g : F[X], ψ (φ (AdjoinRoot.mk f g)) = AdjoinRoot.mk f g := by
      intro g
      induction g using Polynomial.induction_on' with
      | add p q ih1 ih2 =>
        have hpq : AdjoinRoot.mk f (p + q) = AdjoinRoot.mk f p + AdjoinRoot.mk f q := map_add _ _ _
        rw [hpq, map_add, ψ_add, ih1, ih2]
      | monomial n a =>
        show ψ (φ (AdjoinRoot.mk f (monomial n a))) = AdjoinRoot.mk f (monomial n a)
        rw [show φ (AdjoinRoot.mk f (monomial n a)) = i a * U ^ n from by
              rw [AdjoinRoot.lift_mk, eval₂_monomial], hi, hpow n, dOf_mul P, cz]
        simp only [zero_add, pow_zero, mul_one]
        rw [ψ_def, Finset.sum_eq_single (↑n : ZMod e)]
        · rw [dOf, Pi.single_eq_same, ZMod.val_natCast, hmk, map_mul, map_pow, ← hroot,
            ← pow_mul, mul_assoc, ← pow_add, Nat.div_add_mod]
        · intro b _ hb; rw [dOf, Pi.single_eq_of_ne hb, map_zero, zero_mul]
        · intro h; exact absurd (Finset.mem_univ _) h
    intro a
    obtain ⟨g, rfl⟩ := AdjoinRoot.mk_surjective a
    exact key g
  -- assemble the ring equivalence; Θ = E.symm carries the required action on `dOf`
  let E : AdjoinRoot f ≃+* CarryAlg F e :=
    { toFun := φ, invFun := ψ, left_inv := hlinv, right_inv := hrinv,
      map_mul' := map_mul φ, map_add' := map_add φ }
  refine ⟨E.symm, fun ρ c => ?_⟩
  show ψ (dOf ρ c) = algebraMap F (AdjoinRoot f) c * (AdjoinRoot.root f) ^ ρ.val
  rw [ψ_def, Finset.sum_eq_single ρ]
  · rw [dOf, Pi.single_eq_same]
  · intro b _ hb; rw [dOf, Pi.single_eq_of_ne hb, map_zero, zero_mul]
  · intro h; exact absurd (Finset.mem_univ ρ) h

end LeanUrat.HC1

#print axioms LeanUrat.HC1.D4_carryAdjoinRoot
