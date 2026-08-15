/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapG.G11
import Uniformity.ChapG.G12
import Uniformity.ChapG.G19
import Uniformity.ChapG.G23R3
import Uniformity.ChapG.G23R4

/-!
# Uniformity.ChapG.G23R11 — `resClassSet_subset_depthSet`: a double-root-free class sits in the
stratum of depth EXACTLY `2k`

**Chapter G, NODE G.23R11** (`blueprint/CHAP-G_base_cases_menus.md` AMENDMENT §A-8, the
REPLACEMENT ROUTE for the refuted G.23a). `resClassSet π P k N` certifies depth `≥ 2k`; the
route needs depth *exactly* `2k`, i.e. membership in `depthSet π N (2k)` (G.19), and that is
where the residual class must avoid the double-root pairs.

The mechanism, verbatim from A-1's orbit picture: if the class also had a centre `γ'` of depth
`2k+1`, then `γ'` is inside `γ`'s coset mod `π^k` (G.11), write `γ' = γ + π^k·d`; the deeper
divisibility forces `b̄₀ + b̄₁d̄ + d̄² = 0` and `b̄₁ + 2d̄ = 0`, hence `b̄₁ = −2d̄` and `b̄₀ = d̄²`,
i.e. the residual pair is `((−d̄)(−d̄), (−d̄)+(−d̄))` — a `DblPair`. Excluded by hypothesis.

Combined with G.23R3's `aniForm_not_dblPair` / `sepPair_not_dblPair`, this is what lets G.41 and
G.42 read the count of `resClassSet` as a count inside an even DEPTH stratum.

DEPENDS: G.11 (`tang_centre_unique`), G.12 (`tang_of_proj_eq`), G.19 (`depthSet`), G.23R3
(`DblPair` exclusion), G.23R4 (`resClassSet`) · landed `Tang_mono`, `qval_shift`, `qder_shift`,
`mem_maximalIdeal_iff_dvd`.

## Status

Sorry-free, axiom-free (Lean core only).
-/

set_option linter.style.longLine false

namespace Uniformity.Density.Menu

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (IsLocalRing.ResidueField O)] {π : O}

theorem resClassSet_subset_depthSet (hπ : Irreducible π)
    {P : Set (IsLocalRing.ResidueField O × IsLocalRing.ResidueField O)}
    (hP : ∀ p ∈ P, ¬ DblPair p) {k N : ℕ} (hN : 2 * k + 1 ≤ N) :
    resClassSet π P k N ⊆ depthSet π N (2 * k) := by
  rintro c ⟨a, γ, b₀, b₁, ha, e0, e1, hpair⟩
  have hhalf : (2 * k + 1) / 2 = k := by omega
  have ht : Tang π a (2 * k) γ := ⟨⟨b₀, e0⟩, by rw [hhalf]; exact ⟨b₁, e1⟩⟩
  refine ⟨⟨a, ha, γ, ht⟩, ?_⟩
  rintro ⟨a', ha', γ', ht'⟩
  have ht'' : Tang π a (2 * k + 1) γ' :=
    tang_of_proj_eq hπ (by omega) (ha'.trans ha.symm) ht'
  have hdvd := tang_centre_unique hπ ht (Tang_mono (by omega) ht'')
  rw [hhalf] at hdvd
  obtain ⟨d, hd⟩ := hdvd
  have hγ'eq : γ' = γ + π ^ k * d := by linear_combination hd
  have hv : qval a γ' = π ^ (2 * k) * (b₀ + b₁ * d + d * d) := by
    rw [hγ'eq, qval_shift, e0, e1]; ring
  have hw : qder a γ' = π ^ k * (b₁ + 2 * d) := by
    rw [hγ'eq, qder_shift, e1]; ring
  obtain ⟨s, hs⟩ := ht''.1
  have hb0 : π ∣ (b₀ + b₁ * d + d * d) := by
    refine (mul_dvd_mul_iff_left (pow_ne_zero (2 * k) hπ.ne_zero)).1 ⟨s, ?_⟩
    rw [← hv, hs]; ring
  have hd1 : π ^ (k + 1) ∣ qder a γ' := by
    have h := ht''.2
    rwa [show (2 * k + 1 + 1) / 2 = k + 1 by omega] at h
  obtain ⟨t, htt⟩ := hd1
  have hb1 : π ∣ (b₁ + 2 * d) := by
    refine (mul_dvd_mul_iff_left (pow_ne_zero k hπ.ne_zero)).1 ⟨t, ?_⟩
    rw [← hw, htt]; ring
  have hz0 : IsLocalRing.residue O b₀ + IsLocalRing.residue O b₁ * IsLocalRing.residue O d
      + IsLocalRing.residue O d * IsLocalRing.residue O d = 0 := by
    have h : IsLocalRing.residue O (b₀ + b₁ * d + d * d) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.2 ((mem_maximalIdeal_iff_dvd hπ _).2 hb0)
    rwa [map_add, map_add, map_mul, map_mul] at h
  have hz1 : IsLocalRing.residue O b₁ + 2 * IsLocalRing.residue O d = 0 := by
    have h : IsLocalRing.residue O (b₁ + 2 * d) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.2 ((mem_maximalIdeal_iff_dvd hπ _).2 hb1)
    rw [map_add, show (2 : O) * d = d + d by ring, map_add] at h
    linear_combination h
  have hb0e : IsLocalRing.residue O b₀
      = (-IsLocalRing.residue O d) * (-IsLocalRing.residue O d) := by
    linear_combination hz0 - IsLocalRing.residue O d * hz1
  have hb1e : IsLocalRing.residue O b₁
      = (-IsLocalRing.residue O d) + (-IsLocalRing.residue O d) := by
    linear_combination hz1
  exact hP _ hpair ⟨-IsLocalRing.residue O d, Prod.ext_iff.2 ⟨hb0e, hb1e⟩⟩

end Uniformity.Density.Menu

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Menu.resClassSet_subset_depthSet

end AxCheck
