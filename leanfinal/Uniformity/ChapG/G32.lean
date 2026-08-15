/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.Density.AnisotropicForms

/-!
# Uniformity.ChapG.G32 — `exists_aniForm_of_ne_zero`

**Chapter G, NODE G.32** (`blueprint/CHAP-G_base_cases_menus.md` §6). Over a finite field, for
every nonzero `b₁` there is a `b₀` making `X² − b₁X + b₀` irreducible. (False for `b₁ = 0` in
characteristic 2 — every element is a square there — which is exactly why G.34 must choose the
depth at the *exact* valuation of the derivative.)

DEPENDS: landed `Uniformity.Density.AniForm` (`AnisotropicForms.lean:55`).

**⚠ THIS NODE IS THE LEAN FORM OF W-11's `[r1, F6]` CORRECTION.** The struck text claimed the
undecided residue contains split, inert *and* ram lifts per member; the corrected text says
split and inert always exist and ram can be absent. G.33 + G.34 prove exactly the corrected
statement, and this node is why the inert half survives in characteristic 2.

**PROOF (independent route, shorter than the blueprint's fibre-counting sketch).** Let
`φ y = b₁ * y − y²`. `¬ AniForm (b₀, b₁)` says exactly `b₀ ∈ Set.range φ`, so if no `b₀` worked,
`φ` would be surjective; on a finite type `α → α`, surjective ⟺ injective
(`Finite.injective_iff_surjective`). But `φ` is not injective: since `b₁ ≠ 0`, taking `y₀ = 0`
already shows `2 * y₀ ≠ b₁` (else `b₁ = 2 * 0 = 0`), so `y₀ ≠ b₁ − y₀`, yet
`φ y₀ = φ (b₁ − y₀)` by a direct `ring` identity. Characteristic-uniform: nothing here assumes
`2 ≠ 0`.

## Status

Sorry-free, axiom-free (Lean core only).
-/

set_option linter.style.longLine false

namespace Uniformity.Density.Menu

theorem exists_aniForm_of_ne_zero (K : Type*) [Field K] [Finite K] {b₁ : K} (hb : b₁ ≠ 0) :
    ∃ b₀ : K, AniForm (b₀, b₁) := by
  by_contra hcon
  push_neg at hcon
  set φ : K → K := fun y => b₁ * y - y ^ 2 with hφdef
  have hsurj : Function.Surjective φ := by
    intro z
    have hz := hcon z
    simp only [AniForm, not_forall, not_not] at hz
    obtain ⟨y, hy⟩ := hz
    exact ⟨y, by simp only [hφdef]; linear_combination -hy⟩
  obtain ⟨y0, hy0⟩ : ∃ y0 : K, 2 * y0 ≠ b₁ := by
    by_contra h
    push_neg at h
    exact hb (by simpa using (h 0).symm)
  have hne : y0 ≠ b₁ - y0 := by
    intro heq
    apply hy0
    linear_combination heq
  have heqφ : φ y0 = φ (b₁ - y0) := by simp only [hφdef]; ring
  have hninj : ¬ Function.Injective φ := fun hinj => hne (hinj heqφ)
  exact hninj (Finite.injective_iff_surjective.mpr hsurj)

section AxCheck
#print axioms Uniformity.Density.Menu.exists_aniForm_of_ne_zero
end AxCheck

end Uniformity.Density.Menu
