/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapG.G03

/-!
# Uniformity.ChapG.G04 — `readEquiv_proj`

**Chapter G, NODE G.04** (`blueprint/CHAP-G_base_cases_menus.md` §3). `readEquiv` computes the
value and derivative of any lift: if `proj O 2 N a = c` and `γ` is the class of `g : O`, then the
two coordinates of `readEquiv γ c` are the classes of `qval a g` and `qder a g`.

DEPENDS: G.03 · landed `Uniformity.Density.qval`, `Uniformity.Density.qder`
(`Drainage.lean:206,209`), `Uniformity.Density.proj` (`LocalData.lean:136`).

## Status

Sorry-free, axiom-free (Lean core only).
-/

set_option linter.style.longLine false

namespace Uniformity.Density.Menu

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (IsLocalRing.ResidueField O)]

omit [Finite (IsLocalRing.ResidueField O)] in
theorem readEquiv_proj {N : ℕ} (g : O) (a : Fin 2 → O) :
    readEquiv (Ideal.Quotient.mk _ g) (proj O 2 N a)
      = (Ideal.Quotient.mk _ (qval a g), Ideal.Quotient.mk _ (qder a g)) := by
  have h0 : proj O 2 N a 0 = Ideal.Quotient.mk _ (a 0) := rfl
  have h1 : proj O 2 N a 1 = Ideal.Quotient.mk _ (a 1) := rfl
  simp only [readEquiv, Equiv.coe_fn_mk, Prod.mk.injEq, h0, h1]
  refine ⟨?_, ?_⟩
  · rw [qval, map_add, map_add, map_mul, map_pow]; ring
  · rw [qder, map_add, map_mul, map_ofNat]

end Uniformity.Density.Menu

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Menu.readEquiv_proj

end AxCheck
