/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapH.H116b2
import Uniformity.ChapH.H116b3i
import Uniformity.ChapH.H116b3ii
import Uniformity.ChapH.H120
import Uniformity.ChapB.B77a
import Uniformity.ChapB.B77b

/-!
# Uniformity.ChapH.H116b3iii — the ∀-over-lifts bridge (NODE H.116b3-iii, part 1 of 2)

**Chapter H, NODE H.116b3-iii (1/2)** (`blueprint/CHAP-H_general_induction.md`, AMENDMENT
**A-H.8** §5), the lifts bridge of the `¬ IsCSState` transport — block record step (3f)'s
plumbing, signed as its own declaration because `IsCSState` quantifies over EVERY lift of the
class while the planted swap can only exhibit ONE.

`isCSState_of_exists_lift`: one lift with a CS witness suffices. Two lifts of one level-`N`
class differ by `π ^ N` coefficientwise (H.109's `pow_dvd_coeff_comp_sub` at `q = X`), the
witness lift is `Visible` at `N` because the state is not a drain (H.120's
`visible_of_not_isDrainState`), so B.77's congruence package transports the side set, the
pinned height and the residual polynomial verbatim to every other lift.

The `1 ≤ N` needed by the window principle is NOT a binder: at `N = 0` the coefficient ring
`Coeff O m 0` is trivial (`𝔪 ^ 0 = ⊤`), every state is a drain state, and `h0` is absurd —
so the bound is derived, not assumed (the same reason the signed statement carries no `hN`).

The assembly half (`not_isCSState_plantedPoly_swap`, steps (3b)/(3c)/(3e)) is part 2, in a
separate landing.
-/

namespace Uniformity.Density.Induction

open IsLocalRing Polynomial Uniformity.Density.Leaf

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

/-- `ℕ∞`-scalar cancellation: `ℓ • x = ℓ • y → x = y` at `0 < ℓ` (the same shape of private
helper the b3-i/b3-ii modules carry; replicated because they keep theirs `private`). -/
private theorem enat_smul_cancel {ℓ : ℕ} (hℓ : 0 < ℓ) :
    ∀ {x y : ℕ∞}, ℓ • x = ℓ • y → x = y := by
  have hℓ0 : (ℓ : ℕ∞) ≠ 0 := by exact_mod_cast hℓ.ne'
  intro x y h
  rw [nsmul_eq_mul, nsmul_eq_mul] at h
  induction x using ENat.recTopCoe with
  | top =>
    induction y using ENat.recTopCoe with
    | top => rfl
    | coe y =>
      rw [ENat.mul_top hℓ0] at h
      exact absurd h.symm (WithTop.mul_ne_top (ENat.coe_ne_top _) (ENat.coe_ne_top _))
  | coe x =>
    induction y using ENat.recTopCoe with
    | top =>
      rw [ENat.mul_top hℓ0] at h
      exact absurd h (WithTop.mul_ne_top (ENat.coe_ne_top _) (ENat.coe_ne_top _))
    | coe y =>
      rw [← Nat.cast_mul, ← Nat.cast_mul] at h
      have hnat : ℓ * x = ℓ * y := by exact_mod_cast h
      exact_mod_cast Nat.eq_of_mul_eq_mul_left hℓ hnat

/-- **H.116b3-iii (1/2) [NEW NODE: A-H.8].** THE `∀`-OVER-LIFTS BRIDGE — one lift with a CS
witness makes the state a CS state. Statement byte-identical to the A-H.8 leanspec stub. -/
theorem isCSState_of_exists_lift {π : O} (hπ : Irreducible π) {m N : ℕ} (hm : 0 < m)
    {c : ClusterState O m N} (h0 : ¬ IsDrainState c)
    (h : ∃ (a : Fin m → O) (_ : proj O m N a = c.1),
      ∃ (u ℓ : ℕ) (hne : (sideSet X (monicPoly a) u ℓ).Nonempty) (H₀ : ℕ),
        0 < ℓ ∧ Nat.Coprime u ℓ ∧
        npHgt X (monicPoly a) (sideMin X (monicPoly a) u ℓ hne) = (H₀ : ℕ∞) ∧
        ∃ ψ : Polynomial (resField (X : Polynomial O)),
          Irreducible ψ ∧ 2 ≤ ℓ * ψ.natDegree ∧
          ψ ^ 2 ∣ resPoly π X (monicPoly a) u ℓ hne H₀) :
    IsCSState π c := by
  classical
  obtain ⟨a₀, ha₀, u, ℓ, hne, H₀, hℓ, hcop, hpin, ψ, hψirr, hψblk, hψdvd⟩ := h
  -- `N = 0` is impossible: the level-0 coefficient ring is trivial, so every state drains.
  have hN : 1 ≤ N := by
    by_contra hN0
    have hNz : N = 0 := by omega
    apply h0
    intro hm'
    subst hNz
    have hsub : Subsingleton (Res O 0) := Ideal.Quotient.subsingleton_iff.2 (by simp)
    exact Subsingleton.elim _ _
  refine ⟨h0, ?_⟩
  intro a ha
  -- the two lifts are `π ^ N`-congruent coefficientwise
  have hcong : ∀ j, π ^ N ∣ (monicPoly a₀ - monicPoly a).coeff j := by
    intro j
    have := pow_dvd_coeff_comp_sub hπ (ha₀.trans ha.symm) X j
    rwa [Polynomial.comp_X, Polynomial.comp_X] at this
  have hdeg : (monicPoly a).natDegree = (monicPoly a₀).natDegree := by
    rw [monicPoly_natDegree, monicPoly_natDegree]
  have hdX : 0 < (X : Polynomial O).natDegree := by simp [natDegree_X]
  -- the witness lift is visible at the window
  have hvis₀ : Visible π X (monicPoly a₀) N :=
    visible_of_not_isDrainState hπ hm h0 ha₀
  -- transport the side set and the support value
  have hset : sideSet X (monicPoly a) u ℓ = sideSet X (monicPoly a₀) u ℓ :=
    sideSet_congr hπ monic_X hdX hcong hdeg hvis₀ u ℓ
  have hne' : (sideSet X (monicPoly a) u ℓ).Nonempty := by rw [hset]; exact hne
  have hsupp : suppVal X (monicPoly a) u ℓ = suppVal X (monicPoly a₀) u ℓ :=
    suppVal_congr hπ monic_X hdX hcong hdeg hvis₀ u ℓ
  -- the side minima agree (min' of equal sets, proof irrelevance)
  set j₀ := sideMin X (monicPoly a₀) u ℓ hne with hj₀
  have hmin : sideMin X (monicPoly a) u ℓ hne' = j₀ := by
    have key : ∀ (h₁ : (sideSet X (monicPoly a) u ℓ).Nonempty)
        (h₂ : (sideSet X (monicPoly a₀) u ℓ).Nonempty),
        (sideSet X (monicPoly a) u ℓ).min' h₁ = (sideSet X (monicPoly a₀) u ℓ).min' h₂ := by
      rw [hset]
      intro h₁ h₂
      rfl
    exact key hne' hne
  -- both minima are on-side; the pinned height transports by cancellation
  have hOn₀ : OnSide X (monicPoly a₀) u ℓ j₀ :=
    onSide_of_mem_sideSet (Finset.min'_mem _ hne)
  have hOn : OnSide X (monicPoly a) u ℓ j₀ := by
    have hmem : j₀ ∈ sideSet X (monicPoly a) u ℓ := by
      rw [hset]; exact Finset.min'_mem _ hne
    exact onSide_of_mem_sideSet hmem
  have hpin' : npHgt X (monicPoly a) (sideMin X (monicPoly a) u ℓ hne') = (H₀ : ℕ∞) := by
    rw [hmin]
    have h₁ : ℓ • npHgt X (monicPoly a) j₀ + ((u * j₀ : ℕ) : ℕ∞)
        = suppVal X (monicPoly a) u ℓ := hOn
    have h₂ : ℓ • npHgt X (monicPoly a₀) j₀ + ((u * j₀ : ℕ) : ℕ∞)
        = suppVal X (monicPoly a₀) u ℓ := hOn₀
    have heq : ℓ • npHgt X (monicPoly a) j₀ + ((u * j₀ : ℕ) : ℕ∞)
        = ℓ • npHgt X (monicPoly a₀) j₀ + ((u * j₀ : ℕ) : ℕ∞) :=
      (h₁.trans hsupp).trans h₂.symm
    have hfin : ((u * j₀ : ℕ) : ℕ∞) ≠ ⊤ := ENat.coe_ne_top _
    have hcancel : ℓ • npHgt X (monicPoly a) j₀ = ℓ • npHgt X (monicPoly a₀) j₀ :=
      WithTop.add_right_cancel hfin heq
    rw [enat_smul_cancel hℓ hcancel]
    exact hpin
  -- the pinned height is inside the window
  have hH₀N : H₀ < N := by
    have hlt : suppVal X (monicPoly a₀) u ℓ < ((ℓ * N : ℕ) : ℕ∞) :=
      suppVal_lt_window hπ hm hN h0 ha₀ hℓ
    have hle : ((ℓ * H₀ : ℕ) : ℕ∞) ≤ suppVal X (monicPoly a₀) u ℓ := by
      calc ((ℓ * H₀ : ℕ) : ℕ∞) = ℓ • ((H₀ : ℕ) : ℕ∞) := by
            rw [nsmul_eq_mul, Nat.cast_mul]
        _ = ℓ • npHgt X (monicPoly a₀) j₀ := by rw [hpin]
        _ ≤ ℓ • npHgt X (monicPoly a₀) j₀ + ((u * j₀ : ℕ) : ℕ∞) := le_self_add
        _ = suppVal X (monicPoly a₀) u ℓ := hOn₀
    have hcast : ((ℓ * H₀ : ℕ) : ℕ∞) < ((ℓ * N : ℕ) : ℕ∞) := lt_of_le_of_lt hle hlt
    have hnat : ℓ * H₀ < ℓ * N := by exact_mod_cast hcast
    exact Nat.lt_of_mul_lt_mul_left hnat
  -- the residual polynomial transports (the `hne` argument is proof-irrelevant)
  refine ⟨u, ℓ, hne', H₀, hℓ, hcop, hpin', ψ, hψirr, hψblk, ?_⟩
  have hres : resPoly π X (monicPoly a) u ℓ hne' H₀
      = resPoly π X (monicPoly a₀) u ℓ hne H₀ :=
    resPoly_congr hπ monic_X hdX hcong hdeg hvis₀ (u := u) (ℓ := ℓ) hne hH₀N
  rw [hres]
  exact hψdvd

end Uniformity.Density.Induction

/-! ## Axiom footprint -/

section AxCheck
#print axioms Uniformity.Density.Induction.isCSState_of_exists_lift
end AxCheck
