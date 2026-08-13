/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import UniformityCheck.Counting
import UniformityCheck.FiniteFieldQuad

/-!
# UniformityCheck.AniCount — counting the INERT certificate's admissible `(V, D)` pairs

The INERT certificate at parameter `k` admits exactly the level-`N` pairs
`(V, D) = (π ^ (2k) b₀, π ^ k b₁)` whose residual binary form `![b₀, b₁]` is anisotropic.

* `anisotropic_iff_aniK` — anisotropy of `![b₀, b₁]` over `O` is the residue-field condition
  `AniK (b̄₀, b̄₁)`;
* `card_aniPairSet` — at level `N = 2k+1+r` the admissible pairs number `A · q^r · q^(k+r)`
  with `2A + q = q²`, i.e. `2 · #pairs + q ^ (k+2r+1) = q ^ (k+2r+2)`.

## Status

Sorry-free, axiom-free (Lean core only).
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

namespace UniformityCheck

open Uniformity Uniformity.Density IsLocalRing

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)] {π : O}

/-- The admissible `(value, derivative)` pairs for the INERT certificate with parameter `k`:
`V = π^(2k) b₀`, `D = π^k b₁` with the residual binary form `![b₀, b₁]` anisotropic. -/
def aniPairSet (π : O) (k N : ℕ) : Set (Res O N × Res O N) :=
  {p | ∃ b₀ b₁ : O, p.1 = resPi π N ^ (2 * k) * (Ideal.Quotient.mk _ b₀) ∧
        p.2 = resPi π N ^ k * (Ideal.Quotient.mk _ b₁) ∧ Anisotropic ![b₀, b₁]}

/-! ## 1. Anisotropy is a residue-field condition -/

theorem residue_quadForm (b₀ b₁ u v : O) :
    IsLocalRing.residue O (quadForm ![b₀, b₁] u v)
      = (IsLocalRing.residue O u) ^ 2
        - IsLocalRing.residue O b₁ * IsLocalRing.residue O u * IsLocalRing.residue O v
        + IsLocalRing.residue O b₀ * (IsLocalRing.residue O v) ^ 2 := by
  simp [quadForm]

/-- Anisotropy is a residue-field condition. -/
theorem anisotropic_iff_aniK (b₀ b₁ : O) :
    Anisotropic ![b₀, b₁] ↔ AniK (IsLocalRing.residue O b₀, IsLocalRing.residue O b₁) := by
  rw [← aniK_iff]
  constructor
  · intro h u v huv
    obtain ⟨u', rfl⟩ := IsLocalRing.residue_surjective u
    obtain ⟨v', rfl⟩ := IsLocalRing.residue_surjective v
    have hq : quadForm ![b₀, b₁] u' v' ∈ maximalIdeal O := by
      rw [← IsLocalRing.residue_eq_zero_iff, residue_quadForm]
      exact huv
    obtain ⟨hu, hv⟩ := h u' v' hq
    exact ⟨(IsLocalRing.residue_eq_zero_iff _).2 hu, (IsLocalRing.residue_eq_zero_iff _).2 hv⟩
  · intro h u v huv
    have hz : IsLocalRing.residue O (quadForm ![b₀, b₁] u v) = 0 :=
      (IsLocalRing.residue_eq_zero_iff _).2 huv
    rw [residue_quadForm] at hz
    obtain ⟨hu, hv⟩ := h _ _ hz
    exact ⟨(IsLocalRing.residue_eq_zero_iff _).1 hu, (IsLocalRing.residue_eq_zero_iff _).1 hv⟩

/-! ## 2. Residue bookkeeping and the cancellation lemma -/

/-- A set-theoretic section of the residue map. -/
noncomputable def resLift (O : Type*) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] :
    ResidueField O → O :=
  Function.surjInv (IsLocalRing.residue_surjective (R := O))

theorem residue_resLift (x : ResidueField O) : IsLocalRing.residue O (resLift O x) = x :=
  Function.surjInv_eq _ x

theorem residue_pi (hπ : Irreducible π) : IsLocalRing.residue O π = 0 := by
  rw [IsLocalRing.residue_eq_zero_iff, hπ.maximalIdeal_eq, Ideal.mem_span_singleton]

theorem dvd_of_residue_eq (hπ : Irreducible π) {x y : O}
    (h : IsLocalRing.residue O x = IsLocalRing.residue O y) : π ∣ x - y := by
  have hm : x - y ∈ maximalIdeal O := by
    rw [← IsLocalRing.residue_eq_zero_iff, map_sub, h, sub_self]
  rwa [hπ.maximalIdeal_eq, Ideal.mem_span_singleton] at hm

theorem residue_eq_of_dvd (hπ : Irreducible π) {x y : O} (h : π ∣ x - y) :
    IsLocalRing.residue O x = IsLocalRing.residue O y := by
  have hm : x - y ∈ maximalIdeal O := by
    rw [hπ.maximalIdeal_eq, Ideal.mem_span_singleton]; exact h
  have h2 : IsLocalRing.residue O (x - y) = 0 := (IsLocalRing.residue_eq_zero_iff _).2 hm
  rw [map_sub, sub_eq_zero] at h2
  exact h2

/-- `π^m` acting on a level-`N` class, read upstairs. -/
theorem resPi_smul_mk {N : ℕ} (m : ℕ) (b : O) :
    resPi π N ^ m * (Ideal.Quotient.mk _ b : Res O N) = Ideal.Quotient.mk _ (π ^ m * b) := by
  rw [resPi_pow, ← map_mul]

/-- **CANCELLATION.** If `π^m · b` is divisible by `π^(m+1)` inside the window, then `π ∣ b`. -/
theorem pi_dvd_of_mem_dvdSet (hπ : Irreducible π) {m N : ℕ} (hm : m + 1 ≤ N) (b : O)
    (h : resPi π N ^ m * (Ideal.Quotient.mk _ b : Res O N) ∈ dvdSet π (m + 1) N) : π ∣ b := by
  rw [dvdSet, Set.mem_setOf_eq, resPi_smul_mk, dvd_res_iff hπ hm, pow_succ] at h
  exact (mul_dvd_mul_iff_left (pow_ne_zero m hπ.ne_zero)).mp h

/-! ## 3. The parametrisation of the admissible pairs -/

/-- The parametrising map lands in `aniPairSet`. -/
theorem aniPair_mem (hπ : Irreducible π) {k N : ℕ}
    (p : {p : ResidueField O × ResidueField O // AniK p})
    (s : dvdSet π (2 * k + 1) N) (t : dvdSet π (k + 1) N) :
    (resPi π N ^ (2 * k) * (Ideal.Quotient.mk _ (resLift O p.1.1)) + (s : Res O N),
      resPi π N ^ k * (Ideal.Quotient.mk _ (resLift O p.1.2)) + (t : Res O N))
        ∈ aniPairSet π k N := by
  obtain ⟨w, hw⟩ := s.2
  obtain ⟨w', rfl⟩ := Ideal.Quotient.mk_surjective (I := (maximalIdeal O) ^ N) w
  obtain ⟨u, hu⟩ := t.2
  obtain ⟨u', rfl⟩ := Ideal.Quotient.mk_surjective (I := (maximalIdeal O) ^ N) u
  refine ⟨resLift O p.1.1 + π * w', resLift O p.1.2 + π * u', ?_, ?_, ?_⟩
  · show _ + (s : Res O N) = _
    rw [hw, resPi_smul_mk, resPi_smul_mk, resPi_smul_mk, ← map_add]
    congr 1
    ring
  · show _ + (t : Res O N) = _
    rw [hu, resPi_smul_mk, resPi_smul_mk, resPi_smul_mk, ← map_add]
    congr 1
    ring
  · rw [anisotropic_iff_aniK]
    have e0 : IsLocalRing.residue O (resLift O p.1.1 + π * w') = p.1.1 := by
      rw [map_add, map_mul, residue_pi hπ, zero_mul, add_zero, residue_resLift]
    have e1 : IsLocalRing.residue O (resLift O p.1.2 + π * u') = p.1.2 := by
      rw [map_add, map_mul, residue_pi hπ, zero_mul, add_zero, residue_resLift]
    rw [e0, e1]
    exact p.2

/-- **THE PARAMETRISATION.** Anisotropic residue pair × two divisibility strata ≃ admissible
pairs. -/
theorem card_aniPairSet_eq (hπ : Irreducible π) (k r : ℕ) :
    Nat.card ({p : ResidueField O × ResidueField O // AniK p} ×
        (dvdSet π (2 * k + 1) (2 * k + 1 + r)) × (dvdSet π (k + 1) (2 * k + 1 + r)))
      = Nat.card (aniPairSet π k (2 * k + 1 + r)) := by
  classical
  refine Nat.card_eq_of_bijective
    (fun z => ⟨_, aniPair_mem (k := k) (N := 2 * k + 1 + r) hπ z.1 z.2.1 z.2.2⟩) ?_
  constructor
  · rintro ⟨⟨⟨x, y⟩, hxy⟩, ⟨s, hs⟩, ⟨t, ht⟩⟩ ⟨⟨⟨x', y'⟩, hxy'⟩, ⟨s', hs'⟩, ⟨t', ht'⟩⟩ heq
    simp only [Subtype.mk.injEq, Prod.mk.injEq] at heq
    obtain ⟨h1, h2⟩ := heq
    -- first component: `x = x'` then `s = s'`
    have hx : x = x' := by
      have hsub : resPi π (2 * k + 1 + r) ^ (2 * k) *
          (Ideal.Quotient.mk _ (resLift O x - resLift O x') : Res O (2 * k + 1 + r))
            ∈ dvdSet π (2 * k + 1) (2 * k + 1 + r) := by
        have : resPi π (2 * k + 1 + r) ^ (2 * k) *
            (Ideal.Quotient.mk _ (resLift O x - resLift O x') : Res O (2 * k + 1 + r))
              = s' - s := by
          rw [map_sub, mul_sub]
          linear_combination h1
        rw [this]
        exact dvd_sub hs' hs
      have hd := pi_dvd_of_mem_dvdSet (m := 2 * k) hπ (by omega) _ hsub
      have := residue_eq_of_dvd hπ hd
      rwa [residue_resLift, residue_resLift] at this
    have hs2 : s = s' := by
      rw [hx] at h1
      exact add_left_cancel h1
    -- second component: `y = y'` then `t = t'`
    have hy : y = y' := by
      have hsub : resPi π (2 * k + 1 + r) ^ k *
          (Ideal.Quotient.mk _ (resLift O y - resLift O y') : Res O (2 * k + 1 + r))
            ∈ dvdSet π (k + 1) (2 * k + 1 + r) := by
        have : resPi π (2 * k + 1 + r) ^ k *
            (Ideal.Quotient.mk _ (resLift O y - resLift O y') : Res O (2 * k + 1 + r))
              = t' - t := by
          rw [map_sub, mul_sub]
          linear_combination h2
        rw [this]
        exact dvd_sub ht' ht
      have hd := pi_dvd_of_mem_dvdSet (m := k) hπ (by omega) _ hsub
      have := residue_eq_of_dvd hπ hd
      rwa [residue_resLift, residue_resLift] at this
    have ht2 : t = t' := by
      rw [hy] at h2
      exact add_left_cancel h2
    subst hx; subst hy; subst hs2; subst ht2
    rfl
  · rintro ⟨⟨V, D⟩, b₀, b₁, hV, hD, hani⟩
    have hxy : AniK (IsLocalRing.residue O b₀, IsLocalRing.residue O b₁) :=
      (anisotropic_iff_aniK b₀ b₁).1 hani
    have hV' : V = resPi π (2 * k + 1 + r) ^ (2 * k) *
      (Ideal.Quotient.mk _ b₀ : Res O (2 * k + 1 + r)) := hV
    have hD' : D = resPi π (2 * k + 1 + r) ^ k *
      (Ideal.Quotient.mk _ b₁ : Res O (2 * k + 1 + r)) := hD
    obtain ⟨c₀, hc₀⟩ : π ∣ b₀ - resLift O (IsLocalRing.residue O b₀) :=
      dvd_of_residue_eq hπ (by rw [residue_resLift])
    obtain ⟨c₁, hc₁⟩ : π ∣ b₁ - resLift O (IsLocalRing.residue O b₁) :=
      dvd_of_residue_eq hπ (by rw [residue_resLift])
    have hs : V - resPi π (2 * k + 1 + r) ^ (2 * k) *
        (Ideal.Quotient.mk _ (resLift O (IsLocalRing.residue O b₀)) : Res O (2 * k + 1 + r))
          ∈ dvdSet π (2 * k + 1) (2 * k + 1 + r) := by
      refine ⟨Ideal.Quotient.mk _ c₀, ?_⟩
      rw [hV', resPi_smul_mk, resPi_smul_mk, resPi_smul_mk, ← map_sub]
      congr 1
      linear_combination (π ^ (2 * k)) * hc₀
    have ht : D - resPi π (2 * k + 1 + r) ^ k *
        (Ideal.Quotient.mk _ (resLift O (IsLocalRing.residue O b₁)) : Res O (2 * k + 1 + r))
          ∈ dvdSet π (k + 1) (2 * k + 1 + r) := by
      refine ⟨Ideal.Quotient.mk _ c₁, ?_⟩
      rw [hD', resPi_smul_mk, resPi_smul_mk, resPi_smul_mk, ← map_sub]
      congr 1
      linear_combination (π ^ k) * hc₁
    refine ⟨⟨⟨(IsLocalRing.residue O b₀, IsLocalRing.residue O b₁), hxy⟩, ⟨_, hs⟩, ⟨_, ht⟩⟩, ?_⟩
    apply Subtype.ext
    simp only [Prod.mk.injEq]
    exact ⟨by ring, by ring⟩

/-! ## 4. The count -/

/-- **THE ANISOTROPIC-PAIR COUNT.** At level `N = 2k+1+r` there are exactly
`A · q^r · q^(k+r)` admissible pairs, where `A = #{anisotropic residue pairs}` satisfies
`2A + q = q²`; stated subtraction-free. -/
theorem card_aniPairSet (hπ : Irreducible π) (k r : ℕ) :
    2 * Nat.card (aniPairSet π k (2 * k + 1 + r)) + residueCard O ^ (k + 2 * r + 1)
      = residueCard O ^ (k + 2 * r + 2) := by
  classical
  have hd1 : Nat.card (dvdSet π (2 * k + 1) (2 * k + 1 + r)) = residueCard O ^ r :=
    card_dvdSet (π := π) hπ (k := 2 * k + 1) (r := r)
  have hd2 : Nat.card (dvdSet π (k + 1) (2 * k + 1 + r)) = residueCard O ^ (k + r) := by
    have h := card_dvdSet (π := π) hπ (k := k + 1) (r := k + r)
    rwa [show k + 1 + (k + r) = 2 * k + 1 + r from by omega] at h
  have hcard : Nat.card (aniPairSet π k (2 * k + 1 + r))
      = Nat.card {p : ResidueField O × ResidueField O // AniK p} *
          (residueCard O ^ r * residueCard O ^ (k + r)) := by
    rw [← card_aniPairSet_eq hπ k r, Nat.card_prod, Nat.card_prod, hd1, hd2]
  have hA : 2 * Nat.card {p : ResidueField O × ResidueField O // AniK p} + residueCard O
      = residueCard O * residueCard O := two_mul_card_aniK (ResidueField O)
  have hpow : residueCard O ^ r * residueCard O ^ (k + r) = residueCard O ^ (k + 2 * r) := by
    rw [← pow_add]; congr 1; omega
  have e1 : residueCard O ^ (k + 2 * r + 1) = residueCard O ^ (k + 2 * r) * residueCard O :=
    pow_succ _ _
  have e2 : residueCard O ^ (k + 2 * r + 2)
      = residueCard O ^ (k + 2 * r) * (residueCard O * residueCard O) := by
    rw [pow_succ, pow_succ, mul_assoc]
  rw [hcard, hpow, e1, e2]
  calc 2 * (Nat.card {p : ResidueField O × ResidueField O // AniK p} *
        residueCard O ^ (k + 2 * r)) + residueCard O ^ (k + 2 * r) * residueCard O
      = residueCard O ^ (k + 2 * r) *
          (2 * Nat.card {p : ResidueField O × ResidueField O // AniK p} + residueCard O) := by
        ring
    _ = residueCard O ^ (k + 2 * r) * (residueCard O * residueCard O) := by rw [hA]

-- Sanity check of the shape: at `k = r = 0` the level is `N = 1`, `aniPairSet π 0 1` is the set
-- of anisotropic residue pairs, and the statement reads `2A + q = q ^ 2` — exactly
-- `two_mul_card_aniK` for the residue field.

#print axioms UniformityCheck.anisotropic_iff_aniK
#print axioms UniformityCheck.card_aniPairSet

end UniformityCheck
