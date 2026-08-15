/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapG.G40
import Uniformity.Density.Drainage

/-!
# Uniformity.ChapG.G23R12 — the two `O ↔ K` bridges the route's instantiations need

**Chapter G, NODE G.23R12** (`blueprint/CHAP-G_base_cases_menus.md` AMENDMENT §A-8, the
REPLACEMENT ROUTE for the refuted G.23a). The route certifies a residual class `P ⊆ K × K` over
the residue field `K`; the landed even-depth machinery (G.26 `depth_even_dichotomy`, G.27
`decidedAt_inert_of_ani`, G.28 `decidedAt_split_of_sep`) speaks in `O`-level predicates. These
two bridges are the translation, and they are what makes A-1's "instantiate `P := AniForm`" a
one-step move:

* `aniso_iff_aniForm` — the `O`-level `Anisotropic ![b₀, b₁]` (the binary form `u² − b₁uv + b₀v²`
  has only the trivial zero mod `𝔪`) is exactly `AniForm` of the residual pair. Nothing here
  assumes `2 ≠ 0`; the proof is characteristic-free.
* `sepPair_iff_exists_simple_root` — `SepPair` of the residual pair (two distinct roots of
  `X² − b̄₁X + b̄₀`) is exactly the existence of a lift `z` with `π ∣ z² + b₁z + b₀` and
  `π ∤ b₁ + 2z`, i.e. G.28's hypothesis pair. The sign flip is the standard one: the residual
  quadratic read by `qval`/`qder` is `R(y) = y² + b₁y + b₀`, whose roots are the negatives of
  `AniForm`/`SepPair`'s convention, and both predicates are invariant under `y ↦ −y`.

DEPENDS: landed `Anisotropic`, `quadForm` (`QuadCert.lean:336,340`), `AniForm`, `aniForm_iff`
(`AnisotropicForms.lean:55,59`), `SepPair` (G.39), `mem_maximalIdeal_iff_dvd`,
`not_dvd_of_isUnit` (`Drainage.lean:192,~630`).

## Status

Sorry-free, axiom-free (Lean core only).
-/

set_option linter.style.longLine false

namespace Uniformity.Density.Menu

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (IsLocalRing.ResidueField O)] {π : O}

omit [Finite (IsLocalRing.ResidueField O)] in
theorem residue_eq_zero_iff_dvd (hπ : Irreducible π) (x : O) :
    IsLocalRing.residue O x = 0 ↔ π ∣ x :=
  Iff.trans Ideal.Quotient.eq_zero_iff_mem (mem_maximalIdeal_iff_dvd hπ x)

omit [Finite (IsLocalRing.ResidueField O)] in
/-- **The anisotropy bridge.** -/
theorem aniso_iff_aniForm (hπ : Irreducible π) (b₀ b₁ : O) :
    Anisotropic ![b₀, b₁]
      ↔ AniForm (IsLocalRing.residue O b₀, IsLocalRing.residue O b₁) := by
  constructor
  · intro h y hy
    obtain ⟨u, hu⟩ := IsLocalRing.residue_surjective (R := O) y
    have hq : IsLocalRing.residue O (quadForm ![b₀, b₁] u 1) = 0 := by
      rw [quadForm]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, map_add, map_sub, map_mul, map_pow,
        map_one]
      rw [hu]
      linear_combination hy
    have hmem := h u 1 (Ideal.Quotient.eq_zero_iff_mem.1 hq)
    exact not_dvd_of_isUnit hπ isUnit_one ((mem_maximalIdeal_iff_dvd hπ 1).1 hmem.2)
  · intro h u v huv
    have h0 : IsLocalRing.residue O (quadForm ![b₀, b₁] u v) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.2 huv
    have key : (IsLocalRing.residue O u) ^ 2
        - (IsLocalRing.residue O b₁) * (IsLocalRing.residue O u) * (IsLocalRing.residue O v)
        + (IsLocalRing.residue O b₀) * (IsLocalRing.residue O v) ^ 2 = 0 := by
      rw [← h0, quadForm]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, map_add, map_sub, map_mul, map_pow]
    obtain ⟨hu, hv⟩ :=
      (aniForm_iff (IsLocalRing.residue O b₀) (IsLocalRing.residue O b₁)).2 h _ _ key
    exact ⟨Ideal.Quotient.eq_zero_iff_mem.1 hu, Ideal.Quotient.eq_zero_iff_mem.1 hv⟩

omit [Finite (IsLocalRing.ResidueField O)] in
/-- **The separable-split bridge**: `SepPair` of the residual pair is G.28's hypothesis pair. -/
theorem sepPair_iff_exists_simple_root (hπ : Irreducible π) (b₀ b₁ : O) :
    SepPair (IsLocalRing.residue O b₀, IsLocalRing.residue O b₁)
      ↔ ∃ z : O, π ∣ (z ^ 2 + b₁ * z + b₀) ∧ ¬ π ∣ (b₁ + 2 * z) := by
  constructor
  · rintro ⟨u, v, huv, hp⟩
    have hb0 : IsLocalRing.residue O b₀ = u * v := congrArg Prod.fst hp
    have hb1 : IsLocalRing.residue O b₁ = u + v := congrArg Prod.snd hp
    obtain ⟨z, hz⟩ := IsLocalRing.residue_surjective (R := O) (-u)
    refine ⟨z, ?_, ?_⟩
    · refine (residue_eq_zero_iff_dvd hπ _).1 ?_
      rw [map_add, map_add, map_pow, map_mul, hz, hb0, hb1]
      ring
    · intro hcon
      have h := (residue_eq_zero_iff_dvd hπ _).2 hcon
      rw [map_add, show (2 : O) * z = z + z by ring, map_add, hz, hb1] at h
      exact huv (by linear_combination -h)
  · rintro ⟨z, hroot, hsimp⟩
    have hr : IsLocalRing.residue O z ^ 2
        + IsLocalRing.residue O b₁ * IsLocalRing.residue O z + IsLocalRing.residue O b₀ = 0 := by
      have h := (residue_eq_zero_iff_dvd hπ _).2 hroot
      rwa [map_add, map_add, map_pow, map_mul] at h
    refine ⟨-IsLocalRing.residue O z, IsLocalRing.residue O b₁ + IsLocalRing.residue O z, ?_, ?_⟩
    · intro hcon
      refine hsimp ((residue_eq_zero_iff_dvd hπ _).1 ?_)
      rw [map_add, show (2 : O) * z = z + z by ring, map_add]
      linear_combination -hcon
    · have h1 : IsLocalRing.residue O b₀
          = (-IsLocalRing.residue O z) * (IsLocalRing.residue O b₁ + IsLocalRing.residue O z) := by
        linear_combination hr
      have h2 : IsLocalRing.residue O b₁
          = (-IsLocalRing.residue O z) + (IsLocalRing.residue O b₁ + IsLocalRing.residue O z) := by
        ring
      exact Prod.ext_iff.2 ⟨h1, h2⟩

end Uniformity.Density.Menu

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Menu.residue_eq_zero_iff_dvd
#print axioms Uniformity.Density.Menu.aniso_iff_aniForm
#print axioms Uniformity.Density.Menu.sepPair_iff_exists_simple_root

end AxCheck
