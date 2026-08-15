/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapG.G22
import Uniformity.ChapG.G23R4

/-!
# Uniformity.ChapG.G23R10 — `residualPair_eq`, and `resClassSet` in `residualPair` coordinates

**Chapter G, NODE G.23R10** (`blueprint/CHAP-G_base_cases_menus.md` AMENDMENT §A-8, the
REPLACEMENT ROUTE for the refuted G.23a). The blueprint's G.21 PROOF note asks for the two
computation rules of `residualPair`; this node lands them in the single usable form: whenever
the value and derivative factor *explicitly* as `π^(2k)·b₀` and `π^k·b₁`, the `Classical.choose`
witnesses inside `residualPair` are `b₀` and `b₁` on the nose (cancel `π^(2k)`, `π^k` — `O` is a
domain and `π ≠ 0`), so `residualPair h0 h1 = (b̄₀, b̄₁)`.

That makes `resClassSet` (G.23R4, stated with explicit `b₀ b₁` for workability) interchangeable
with the `residualPair` phrasing G.21/G.22 use, which is the form a consumer keyed to
`resStratum` will reach for.

DEPENDS: G.21 (`residualPair`), G.23R4 (`resClassSet`).

## Status

Sorry-free, axiom-free (Lean core only).
-/

set_option linter.style.longLine false

namespace Uniformity.Density.Menu

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (IsLocalRing.ResidueField O)] {π : O}

omit [Finite (IsLocalRing.ResidueField O)] in
/-- **The `residualPair` computation rule.** -/
theorem residualPair_eq (hπ : Irreducible π) {k : ℕ} {a : Fin 2 → O} {γ b₀ b₁ : O}
    (h0 : π ^ (2 * k) ∣ qval a γ) (h1 : π ^ k ∣ qder a γ)
    (e0 : qval a γ = π ^ (2 * k) * b₀) (e1 : qder a γ = π ^ k * b₁) :
    residualPair h0 h1 = (IsLocalRing.residue O b₀, IsLocalRing.residue O b₁) := by
  have hc0 : h0.choose = b₀ :=
    mul_left_cancel₀ (pow_ne_zero (2 * k) hπ.ne_zero) (by rw [← h0.choose_spec, e0])
  have hc1 : h1.choose = b₁ :=
    mul_left_cancel₀ (pow_ne_zero k hπ.ne_zero) (by rw [← h1.choose_spec, e1])
  simp only [residualPair, hc0, hc1]

omit [Finite (IsLocalRing.ResidueField O)] in
theorem mem_resClassSet_iff_residualPair (hπ : Irreducible π)
    {P : Set (IsLocalRing.ResidueField O × IsLocalRing.ResidueField O)} {k N : ℕ}
    {c : Coeff O 2 N} :
    c ∈ resClassSet π P k N
      ↔ ∃ (a : Fin 2 → O) (γ : O) (h0 : π ^ (2 * k) ∣ qval a γ) (h1 : π ^ k ∣ qder a γ),
          proj O 2 N a = c ∧ residualPair h0 h1 ∈ P := by
  constructor
  · rintro ⟨a, γ, b₀, b₁, ha, e0, e1, hpair⟩
    exact ⟨a, γ, ⟨b₀, e0⟩, ⟨b₁, e1⟩, ha, by rw [residualPair_eq hπ _ _ e0 e1]; exact hpair⟩
  · rintro ⟨a, γ, h0, h1, ha, hpair⟩
    refine ⟨a, γ, h0.choose, h1.choose, ha, h0.choose_spec, h1.choose_spec, ?_⟩
    rwa [← residualPair_eq hπ h0 h1 h0.choose_spec h1.choose_spec]

end Uniformity.Density.Menu

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Menu.residualPair_eq
#print axioms Uniformity.Density.Menu.mem_resClassSet_iff_residualPair

end AxCheck
