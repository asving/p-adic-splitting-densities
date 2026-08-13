/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import UniformityCheck.InertShift
import UniformityCheck.AniCount
import UniformityCheck.N2Base

/-!
# UniformityCheck.InertCensus — the exact level-`N` count of the INERT classes

Same shape as `RamCensus.lean`, with the anisotropic residual reading in place of the odd exact
valuation. At level `N = 2k+1+r` the classes carrying an INERT certificate with parameter `k`
number exactly `A · q^(2k+2r)`, where `A = #{anisotropic residue pairs} = q(q-1)/2`
(`AniCount.card_aniPairSet`): the centre contributes `q^k` (it is pinned mod `𝔪 ^ k`,
`InertShift.InertAt_uniq`) and the admissible `(value, derivative)` pairs `A q^r q^(k+r)`.

Note the window condition `2k+1 ≤ N` is part of the CLASS-level certificate: without it the
degenerate pair `(0,0)` would satisfy the residual condition vacuously at every `k ≥ N`, and the
family would not be empty outside the window.

## Status

Sorry-free, axiom-free (Lean core only).
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

namespace UniformityCheck

open Uniformity Uniformity.Density IsLocalRing

section Census

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)] {π : O}

/-- Reading a `π ^ m`-multiple relation downstairs. -/
theorem mk_eq_pow_mul_iff (hπ : Irreducible π) {N : ℕ} (m : ℕ) (x b : O) :
    (Ideal.Quotient.mk _ x : Res O N) = resPi π N ^ m * (Ideal.Quotient.mk _ b)
      ↔ π ^ N ∣ (x - π ^ m * b) := by
  rw [resPi_pow, ← map_mul, Ideal.Quotient.eq, mem_maximalIdeal_pow_iff_dvd hπ]

/-- **The INERT certificate as a property of the level-`N` class**, window condition included. -/
def InertCert (π : O) (k N : ℕ) (γ : Res O N) (c : Coeff O 2 N) : Prop :=
  2 * k + 1 ≤ N ∧ readEquiv γ c ∈ aniPairSet π k N

/-- The set of level-`N` classes carrying an INERT certificate with parameter `k`. -/
def inertSet (π : O) (k N : ℕ) : Set (Coeff O 2 N) := {c | ∃ γ, InertCert π k N γ c}

theorem inertSet_param_le {k N : ℕ} {c : Coeff O 2 N} (hc : c ∈ inertSet π k N) :
    2 * k + 1 ≤ N := by
  obtain ⟨-, h, -⟩ := hc
  exact h

theorem inertSet_eq_empty (π : O) {k N : ℕ} (hN : N < 2 * k + 1) : inertSet π k N = ∅ := by
  ext c
  simp only [Set.mem_empty_iff_false, iff_false]
  intro hc
  exact absurd (inertSet_param_le hc) (by omega)

/-- Downstairs and upstairs agree, inside the window. -/
theorem inertCert_iff (hπ : Irreducible π) {k N : ℕ} (hN : 2 * k + 1 ≤ N) (a : Fin 2 → O) (γ : O) :
    InertCert π k N (Ideal.Quotient.mk _ γ) (proj O 2 N a) ↔ InertAt π k a γ := by
  obtain ⟨r, rfl⟩ : ∃ r, N = 2 * k + 1 + r := ⟨N - (2 * k + 1), by omega⟩
  rw [InertCert, readEquiv_proj]
  simp only [aniPairSet, Set.mem_setOf_eq]
  constructor
  · rintro ⟨-, b₀, b₁, hV, hD, han⟩
    rw [mk_eq_pow_mul_iff hπ] at hV hD
    obtain ⟨t, ht⟩ := hV
    obtain ⟨s, hs⟩ := hD
    refine ⟨b₀ + π ^ (1 + r) * t, b₁ + π ^ (k + 1 + r) * s, ?_, ?_, ?_⟩
    · have : qval a γ = π ^ (2 * k) * b₀ + π ^ (2 * k + 1 + r) * t := by linear_combination ht
      rw [this, show 2 * k + 1 + r = 2 * k + (1 + r) from by omega, pow_add]
      ring
    · have : qder a γ = π ^ k * b₁ + π ^ (2 * k + 1 + r) * s := by linear_combination hs
      rw [this, show 2 * k + 1 + r = k + (k + 1 + r) from by omega, pow_add]
      ring
    · refine Anisotropic_congr hπ han ?_ ?_
      · show π ∣ (b₀ + π ^ (1 + r) * t - b₀)
        exact ⟨π ^ r * t, by rw [pow_add]; ring⟩
      · show π ∣ (b₁ + π ^ (k + 1 + r) * s - b₁)
        exact ⟨π ^ (k + r) * s, by rw [show k + 1 + r = 1 + (k + r) from by omega, pow_add]; ring⟩
  · rintro ⟨b₀, b₁, hV, hD, han⟩
    refine ⟨by omega, b₀, b₁, ?_, ?_, han⟩
    · rw [mk_eq_pow_mul_iff hπ, hV]
      exact ⟨0, by ring⟩
    · rw [mk_eq_pow_mul_iff hπ, hD]
      exact ⟨0, by ring⟩

/-- **The parameter is determined by the class**: the INERT families are pairwise disjoint. -/
theorem inertSet_param_unique (hπ : Irreducible π) {k k' N : ℕ} {c : Coeff O 2 N}
    (hc : c ∈ inertSet π k N) (hc' : c ∈ inertSet π k' N) : k = k' := by
  have hk := inertSet_param_le hc
  have hk' := inertSet_param_le hc'
  obtain ⟨γ, hγ⟩ := hc
  obtain ⟨γ', hγ'⟩ := hc'
  obtain ⟨a, rfl⟩ := proj_surjective O 2 N c
  obtain ⟨g, rfl⟩ := Ideal.Quotient.mk_surjective (I := (maximalIdeal O) ^ N) γ
  obtain ⟨g', rfl⟩ := Ideal.Quotient.mk_surjective (I := (maximalIdeal O) ^ N) γ'
  rw [inertCert_iff hπ hk] at hγ
  rw [inertCert_iff hπ hk'] at hγ'
  exact (InertAt_uniq hπ hγ hγ').1

/-- **THE INERT CENSUS.** At level `N = 2k+1+r` exactly `A q^(2k+2r)` classes carry the INERT
certificate with parameter `k`, where `2A + q = q²`; stated subtraction-free. -/
theorem card_inertSet (hπ : Irreducible π) (k r : ℕ) :
    2 * Nat.card (inertSet π k (2 * k + 1 + r)) + residueCard O ^ (2 * k + 2 * r + 1)
      = residueCard O ^ (2 * k + 2 * r + 2) := by
  classical
  have hm : k ≤ 2 * k + 1 + r := by omega
  have hcard : Nat.card (inertSet π k (2 * k + 1 + r))
      = residueCard O ^ k * Nat.card (aniPairSet π k (2 * k + 1 + r)) := by
    refine card_certSet hm _ (InertCert π k (2 * k + 1 + r))
      (fun γ c => ⟨fun h => h.2, fun h => ⟨by omega, h⟩⟩) ?_ ?_
    · intro γ γ' c hc hgg
      obtain ⟨a, rfl⟩ := proj_surjective O 2 (2 * k + 1 + r) c
      obtain ⟨g, rfl⟩ := Ideal.Quotient.mk_surjective (I := (maximalIdeal O) ^ (2 * k + 1 + r)) γ
      obtain ⟨g', rfl⟩ := Ideal.Quotient.mk_surjective (I := (maximalIdeal O) ^ (2 * k + 1 + r)) γ'
      rw [inertCert_iff hπ (by omega)] at hc ⊢
      exact InertAt_shift hc (dvd_sub_comm.1 ((resFactor_eq_iff_dvd hπ hm g' g).1 hgg))
    · intro γ γ' c hc hc'
      obtain ⟨a, rfl⟩ := proj_surjective O 2 (2 * k + 1 + r) c
      obtain ⟨g, rfl⟩ := Ideal.Quotient.mk_surjective (I := (maximalIdeal O) ^ (2 * k + 1 + r)) γ
      obtain ⟨g', rfl⟩ := Ideal.Quotient.mk_surjective (I := (maximalIdeal O) ^ (2 * k + 1 + r)) γ'
      rw [inertCert_iff hπ (by omega)] at hc hc'
      exact (resFactor_eq_iff_dvd hπ hm g' g).2 (dvd_sub_comm.1 (InertAt_uniq hπ hc hc').2)
  have hani := card_aniPairSet (π := π) hπ k r
  have e1 : residueCard O ^ (2 * k + 2 * r + 1)
      = residueCard O ^ k * residueCard O ^ (k + 2 * r + 1) := by
    rw [← pow_add]; congr 1; omega
  have e2 : residueCard O ^ (2 * k + 2 * r + 2)
      = residueCard O ^ k * residueCard O ^ (k + 2 * r + 2) := by
    rw [← pow_add]; congr 1; omega
  rw [hcard, e1, e2,
    show 2 * (residueCard O ^ k * Nat.card (aniPairSet π k (2 * k + 1 + r)))
      = residueCard O ^ k * (2 * Nat.card (aniPairSet π k (2 * k + 1 + r))) from by ring,
    ← Nat.mul_add, hani]

end Census

end UniformityCheck
