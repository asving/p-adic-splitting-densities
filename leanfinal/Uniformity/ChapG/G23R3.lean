/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapG.G40

/-!
# Uniformity.ChapG.G23R3 — `transPair` / `TransInvariant`, and the two invariant residual classes

**Chapter G, NODE G.23R3** (`blueprint/CHAP-G_base_cases_menus.md` AMENDMENT §A-8, the
REPLACEMENT ROUTE for the refuted G.23a). A-1's finding is that the residual PAIR is not a class
invariant: recentring `γ ↦ γ + π^k·d` moves it by `(b₀, b₁) ↦ (b₀ + b₁d + d², b₁ + 2d)`, i.e. by
the substitution `y ↦ y + d` on the residual quadratic `R(y) = y² + b₁y + b₀`. That action is
`transPair`; a residual CLASS closed under it (`TransInvariant`) *is* a class invariant, and is
what the replacement route certifies.

The two classes the chapter needs are invariant because `y ↦ y + d` does not change how `R`
factors: `aniForm_transInvariant` (no root) and `sepPair_transInvariant` (two distinct roots).
Both are also disjoint from the double-root pairs — the exclusion G.23R11 needs to place the
certified classes inside `depthSet π N (2k)` rather than merely inside `tangSet π N (2k)`.

DEPENDS: landed `AniForm` (`AnisotropicForms.lean:55`), `SepPair` (G.39), `DblPair` (G.40).

## Status

Sorry-free, axiom-free (Lean core only).
-/

set_option linter.style.longLine false

namespace Uniformity.Density.Menu

/-- The residue-field translation `y ↦ y + d` read on residual pairs `(b₀, b₁)`: the coefficient
pair of `R(y + d)` where `R(y) = y² + b₁y + b₀`. -/
def transPair {K : Type*} [CommRing K] (d : K) (p : K × K) : K × K :=
  (p.1 + p.2 * d + d * d, p.2 + 2 * d)

/-- A residual class is *translation-invariant* when it is closed under `transPair` — the
property that makes membership a function of the CLASS rather than of the centre. -/
def TransInvariant {K : Type*} [CommRing K] (P : Set (K × K)) : Prop :=
  ∀ (d : K) (p : K × K), p ∈ P → transPair d p ∈ P

theorem aniForm_transInvariant {K : Type*} [Field K] :
    TransInvariant {p : K × K | AniForm p} := by
  intro d p hp y hy
  exact hp (y - d) (by simp only [transPair] at hy; linear_combination hy)

theorem sepPair_transInvariant {K : Type*} [Field K] :
    TransInvariant {p : K × K | SepPair p} := by
  rintro d p ⟨u, v, huv, rfl⟩
  refine ⟨u + d, v + d, fun h => huv (add_right_cancel h), ?_⟩
  simp only [transPair, Prod.mk.injEq]
  constructor <;> ring

theorem aniForm_not_dblPair {K : Type*} [Field K] {p : K × K} (h : AniForm p) : ¬ DblPair p := by
  rintro ⟨y, rfl⟩
  exact h y (by simp; ring)

theorem sepPair_not_dblPair {K : Type*} [Field K] {p : K × K} (h : SepPair p) : ¬ DblPair p := by
  rintro ⟨y, hy⟩
  obtain ⟨u, v, huv, rfl⟩ := h
  have h1 : u * v = y * y := congrArg Prod.fst hy
  have h2 : u + v = y + y := congrArg Prod.snd hy
  have key : (u - y) * (v - y) = 0 := by linear_combination h1 - y * h2
  rcases mul_eq_zero.1 key with hk | hk
  · exact huv (by linear_combination 2 * (sub_eq_zero.1 hk) - h2)
  · exact huv (by linear_combination h2 - 2 * (sub_eq_zero.1 hk))

end Uniformity.Density.Menu

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Menu.transPair
#print axioms Uniformity.Density.Menu.TransInvariant
#print axioms Uniformity.Density.Menu.aniForm_transInvariant
#print axioms Uniformity.Density.Menu.sepPair_transInvariant
#print axioms Uniformity.Density.Menu.aniForm_not_dblPair
#print axioms Uniformity.Density.Menu.sepPair_not_dblPair

end AxCheck
