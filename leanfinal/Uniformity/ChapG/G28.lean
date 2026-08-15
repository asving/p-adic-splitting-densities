/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapG.G26

/-!
# Uniformity.ChapG.G28 — `decidedAt_split_of_sep`

**Chapter G, NODE G.28** (`blueprint/CHAP-G_base_cases_menus.md` §5). A simple residual root at
an even-depth centre ⟹ the SPLIT certificate at window `2k+1`; hence the class is
`splitType`-decided at every level `N ≥ 2k+1`.

**⚠ SIGNATURE AMENDED 2026-08-15 (blueprint AMENDMENT §A-2): `hN : 2 * k + 1 ≤ N`** (was
`2 * k + 2 ≤ N`, which is one stronger than the proof uses). `CertSplit` itself only asks
`2*w+1 ≤ N`, `CertSplit_congr` transports at equality, and `typeOf_of_certSplit` discards the
window bound entirely, so the top even stratum `t = N − 1` is covered and G.42 is provable at
`r = 0`.

DEPENDS: G.26 · landed `CertSplit` (`Drainage.lean:245`), `typeOf_of_certSplit`
(`Drainage.lean:407`), `CertSplit_congr` (`Drainage.lean:455`), `qval_shift`, `qder_shift`,
`congAt_of_proj_eq`.

## Status

Sorry-free, axiom-free (Lean core only).
-/

set_option linter.style.longLine false

namespace Uniformity.Density.Menu

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (IsLocalRing.ResidueField O)] {π : O}

theorem decidedAt_split_of_sep (hπ : Irreducible π)
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O] {N k : ℕ} {a : Fin 2 → O} {γ z : O}
    {b₀ b₁ : O} (hN : 2 * k + 1 ≤ N)
    (h0 : qval a γ = π ^ (2 * k) * b₀) (h1 : qder a γ = π ^ k * b₁)
    (hz : π ∣ (z ^ 2 + b₁ * z + b₀)) (hs : ¬ π ∣ (b₁ + 2 * z)) :
    DecidedAt O 2 splitType N (proj O 2 N a) := by
  have hder' : qder a (γ + π ^ k * z) = π ^ k * (b₁ + 2 * z) := by
    rw [qder_shift, h1]; ring
  have hval' : π ^ (2 * k + 1) ∣ qval a (γ + π ^ k * z) := by
    rw [qval_shift, h0, h1]
    obtain ⟨c, hc⟩ := hz
    exact ⟨c, by linear_combination (π ^ (2 * k)) * hc⟩
  have hcert : CertSplit π a N := by
    refine ⟨γ + π ^ k * z, k, hN, ?_, ?_, hval'⟩
    · rw [hder']; exact ⟨b₁ + 2 * z, rfl⟩
    · rw [hder']
      intro hcon
      refine hs ?_
      obtain ⟨c, hc⟩ := hcon
      refine ⟨c, mul_left_cancel₀ (pow_ne_zero k hπ.ne_zero) ?_⟩
      rw [hc, pow_succ]; ring
  intro b hb
  exact typeOf_of_certSplit hπ (CertSplit_congr (congAt_of_proj_eq hπ hb.symm) hcert)

end Uniformity.Density.Menu

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Menu.decidedAt_split_of_sep

end AxCheck
