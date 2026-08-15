/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapG.G09
import Uniformity.ChapG.G12

/-!
# Uniformity.ChapG.G13 — `mem_tangSet_iff` / `tangSet_antitone`

**Chapter G, NODE G.13** (`blueprint/CHAP-G_base_cases_menus.md` §4). For `t ≤ N`, membership in
`tangSet π N t` is equivalent to the `∀`-form: every lift has a centre of depth `≥ t`.
Consequently `tangSet` is antitone in `t`.

DEPENDS: G.09, G.12 · landed `proj_surjective`, `Tang_mono` (`Drainage.lean:517`).

## Status

Sorry-free, axiom-free (Lean core only).
-/

set_option linter.style.longLine false

namespace Uniformity.Density.Menu

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (IsLocalRing.ResidueField O)] {π : O}

theorem mem_tangSet_iff (hπ : Irreducible π) {N t : ℕ} (ht : t ≤ N) {c : Coeff O 2 N} :
    c ∈ tangSet π N t ↔ ∀ a : Fin 2 → O, proj O 2 N a = c → ∃ γ : O, Tang π a t γ := by
  constructor
  · rintro ⟨a, ha, γ, hγ⟩ b hb
    exact ⟨γ, tang_of_proj_eq hπ ht (ha.trans hb.symm) hγ⟩
  · intro h
    obtain ⟨a, ha⟩ := proj_surjective O 2 N c
    exact ⟨a, ha, h a ha⟩

omit [Finite (IsLocalRing.ResidueField O)] in
theorem tangSet_antitone (hπ : Irreducible π) {N t t' : ℕ} (h : t ≤ t') :
    tangSet π N t' ⊆ tangSet π N t := by
  rintro c ⟨a, ha, γ, hγ⟩
  exact ⟨a, ha, γ, Tang_mono h hγ⟩

end Uniformity.Density.Menu

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Menu.mem_tangSet_iff
#print axioms Uniformity.Density.Menu.tangSet_antitone

end AxCheck
