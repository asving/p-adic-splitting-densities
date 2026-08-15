/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapG.G38
import Uniformity.ChapG.G39

/-!
# Uniformity.ChapG.G40 — `card_dblPair` / `pair_trichotomy`

**Chapter G, NODE G.40** (`blueprint/CHAP-G_base_cases_menus.md` §7). The double-root pairs
number exactly `q`, and the three classes (anisotropic, separable-split, double-root) partition
`K × K`.

DEPENDS: G.38, G.39 · landed `AniForm`, `exists_rootPairMap_iff`.

**On `card_dblPair`'s injectivity.** The blueprint's own recommended route: two pairs
`(y,y)`-images agreeing means `z` is a root of `X² − (y+y)X + y·y = (X−y)²` (a pure ring
identity from the two agreement equations, char-independent), hence `z = y`. Landed as the
private helper `dblPair_inj`.

## Status

Sorry-free, axiom-free (Lean core only).
-/

set_option linter.style.longLine false

namespace Uniformity.Density.Menu

variable {K : Type*} [Field K]

def DblPair (p : K × K) : Prop := ∃ y : K, p = (y * y, y + y)

/-- Two elements with the same square and the same double are equal: `z` is a root of the
double root `(X − y)²`, char-independent. -/
theorem dblPair_inj {y z : K} (h1 : y * y = z * z) (h2 : y + y = z + z) : y = z := by
  have hz : (z - y) ^ 2 = 0 := by linear_combination h1 - z * h2
  have hzy : z - y = 0 := by
    have h2ne : (2 : ℕ) ≠ 0 := by norm_num
    exact (pow_eq_zero_iff h2ne).1 hz
  exact (sub_eq_zero.1 hzy).symm

theorem card_dblPair (K : Type*) [Field K] [Finite K] :
    Nat.card {p : K × K // DblPair p} = Nat.card K := by
  refine (Nat.card_congr (Equiv.ofBijective (fun y : K => (⟨(y * y, y + y), y, rfl⟩ :
    {p : K × K // DblPair p})) ⟨?_, ?_⟩)).symm
  · intro y z hyz
    have h12 : ((y * y, y + y) : K × K) = (z * z, z + z) := congrArg Subtype.val hyz
    exact dblPair_inj (congrArg Prod.fst h12) (congrArg Prod.snd h12)
  · rintro ⟨p, y, rfl⟩
    exact ⟨y, rfl⟩

theorem pair_trichotomy {K : Type*} [Field K] (p : K × K) :
    AniForm p ∨ SepPair p ∨ DblPair p := by
  by_cases h : AniForm p
  · exact Or.inl h
  · right
    simp only [AniForm, not_forall] at h
    obtain ⟨y, hy⟩ := h
    push_neg at hy
    by_cases hyz : y = p.2 - y
    · right
      refine ⟨y, ?_⟩
      ext
      · show p.1 = y * y
        linear_combination hy - y * hyz
      · show p.2 = y + y
        linear_combination -hyz
    · left
      refine ⟨y, p.2 - y, hyz, ?_⟩
      ext
      · show p.1 = y * (p.2 - y)
        linear_combination hy
      · show p.2 = y + (p.2 - y)
        ring

end Uniformity.Density.Menu

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Menu.dblPair_inj
#print axioms Uniformity.Density.Menu.card_dblPair
#print axioms Uniformity.Density.Menu.pair_trichotomy

end AxCheck
