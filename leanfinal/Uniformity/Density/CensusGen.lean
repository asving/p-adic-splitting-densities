/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.Density.LocalData

/-!
# Uniformity.Density.CensusGen — THE CENSUS LEMMA at general degree and general read

**CN-16** of `spec/CERTAIN_NODES_2026-08-14.md`: the general-`n`, general-read form of
`UniformityCheck.card_certSet` (`leancheck/UniformityCheck/Counting.lean:228`).

If a "certificate at a centre" `cert γ c` for level-`N` coefficient classes

* reads only through a fixed bijective re-coordinatisation `read γ : Coeff O n N ≃ D`, via an
  admissible set `S : Set D` (`hcert`);
* survives every move of the centre inside its coset mod `𝔪 ^ m` (`hshift`);
* forces all its centres into one such coset (`huniq`);

then the certified classes number exactly `q ^ m * #S`: the centre contributes `q ^ m`, the
admissible data `#S`. The landed `n = 2` lemma is the instance
`card_certSet = card_certSet_gen (n := 2) readEquiv` — its proof never unfolds the
`(F(γ), F'(γ))` reading, which is precisely why this generalization is free.

**Placement.** The declaration keeps its contract name `UniformityCheck.card_certSet_gen` while
living in `leanfinal` (which `leancheck` imports), so every census downstream can consume it. The
section helper is named `towerSection`, not `resSection`, to avoid colliding with the identically
built map in `leancheck/UniformityCheck/Counting.lean`.

## Status

Sorry-free, axiom-free (Lean core only).
-/

set_option linter.style.longLine false

namespace UniformityCheck

open Uniformity Uniformity.Density IsLocalRing Polynomial

section Census

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)]

/-- A set-theoretic section of the level-`N` → level-`m` truncation `resFactor`. -/
noncomputable def towerSection {m N : ℕ} (h : m ≤ N) : Res O m → Res O N :=
  Function.surjInv (resFactor_surjective (O := O) h)

theorem resFactor_towerSection {m N : ℕ} (h : m ≤ N) (x : Res O m) :
    resFactor (O := O) h (towerSection h x) = x :=
  Function.surjInv_eq _ x

/-- **CN-16 — THE CENSUS LEMMA, general `n`, general read.**

The count is proved by exhibiting the bijection

  `(γ̄, d) ↦ (read (section γ̄)).symm d : Res O m × S ≃ {c | ∃ γ, cert γ c}`

— injective because `huniq` recovers the centre's class `γ̄` from the certified class and `read`
is a bijection, surjective because `hshift` lets one move any witnessing centre to the section
representative of its class. -/
theorem card_certSet_gen {n N m : ℕ} (hm : m ≤ N) {D : Type*}
    (read : Res O N → (Coeff O n N ≃ D)) (S : Set D)
    (cert : Res O N → Coeff O n N → Prop)
    (hcert : ∀ γ c, cert γ c ↔ read γ c ∈ S)
    (hshift : ∀ γ γ' c, cert γ c → resFactor (O := O) hm γ' = resFactor hm γ → cert γ' c)
    (huniq : ∀ γ γ' c, cert γ c → cert γ' c → resFactor (O := O) hm γ' = resFactor hm γ) :
    Nat.card {c : Coeff O n N | ∃ γ, cert γ c} = residueCard O ^ m * Nat.card S := by
  classical
  -- the parametrisation `(γ̄, d) ↦ the class read at the section representative of γ̄`
  set Ξ : Res O m × S → {c : Coeff O n N | ∃ γ, cert γ c} := fun p =>
    ⟨(read (towerSection hm p.1)).symm p.2,
      ⟨towerSection hm p.1, (hcert _ _).2 (by rw [Equiv.apply_symm_apply]; exact p.2.2)⟩⟩ with hΞ
  have hbij : Function.Bijective Ξ := by
    constructor
    · rintro ⟨g, p⟩ ⟨g', p'⟩ hpp
      have hc : (read (towerSection hm g)).symm (p : D)
          = (read (towerSection hm g')).symm (p' : D) := congrArg Subtype.val hpp
      have hcert1 : cert (towerSection hm g) ((read (towerSection hm g)).symm (p : D)) :=
        (hcert _ _).2 (by rw [Equiv.apply_symm_apply]; exact p.2)
      have hcert2 : cert (towerSection hm g') ((read (towerSection hm g)).symm (p : D)) := by
        refine (hcert _ _).2 ?_
        rw [hc, Equiv.apply_symm_apply]
        exact p'.2
      have hgg : g' = g := by
        have h := huniq _ _ _ hcert1 hcert2
        rwa [resFactor_towerSection, resFactor_towerSection] at h
      rw [hgg] at hc
      simp only [Prod.mk.injEq]
      exact ⟨hgg.symm, Subtype.ext ((read (towerSection hm g)).symm.injective hc)⟩
    · rintro ⟨c, γ, hγ⟩
      refine ⟨(resFactor hm γ, ⟨read (towerSection hm (resFactor hm γ)) c, ?_⟩), ?_⟩
      · refine (hcert _ _).1 (hshift γ _ c hγ ?_)
        rw [resFactor_towerSection]
      · exact Subtype.ext (by simp only [hΞ, Equiv.symm_apply_apply])
  rw [← Nat.card_eq_of_bijective Ξ hbij, Nat.card_prod, card_res]

end Census

/-! ## Axiom footprint -/

section AxCheck

#print axioms UniformityCheck.card_certSet_gen

end AxCheck

end UniformityCheck
