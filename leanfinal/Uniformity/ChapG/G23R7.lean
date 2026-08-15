/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapG.G04
import Uniformity.ChapG.G23R4

/-!
# Uniformity.ChapG.G23R7 — `resAdm_read_iff`, the certificate bridge

**Chapter G, NODE G.23R7** (`blueprint/CHAP-G_base_cases_menus.md` AMENDMENT §A-8, the
REPLACEMENT ROUTE for the refuted G.23a). The route's analogue of G.18's `cert_iff_tang`:
reading the class `proj O 2 N a` at the centre class `⟦γ⟧` lands in `resAdm π P k N` exactly
when the *integral* value and derivative factor as `π^(2k)·b₀` and `π^k·b₁` with residual pair
in `P`.

The forward direction is where the two hypotheses `2k < N`, `k < N` are used: the level-`N`
class of `π^(2k)·y₀` forces `π^(2k) ∣ qval a γ` (because `2k ≤ N`), and then G.23R2's digit
uniqueness identifies the resulting `b₀` with `y₀` mod `𝔪`.

DEPENDS: G.04 (`readEquiv_proj`), G.23R2, G.23R4 · landed `mem_maximalIdeal_pow_iff_dvd`.

## Status

Sorry-free, axiom-free (Lean core only).
-/

set_option linter.style.longLine false

namespace Uniformity.Density.Menu

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (IsLocalRing.ResidueField O)] {π : O}

theorem resAdm_read_iff (hπ : Irreducible π)
    {P : Set (IsLocalRing.ResidueField O × IsLocalRing.ResidueField O)} {k N : ℕ}
    (h₀ : 2 * k < N) (h₁ : k < N) (γ : O) (a : Fin 2 → O) :
    readEquiv (Ideal.Quotient.mk _ γ) (proj O 2 N a) ∈ resAdm π P k N
      ↔ ∃ b₀ b₁ : O, qval a γ = π ^ (2 * k) * b₀ ∧ qder a γ = π ^ k * b₁ ∧
          (IsLocalRing.residue O b₀, IsLocalRing.residue O b₁) ∈ P := by
  rw [readEquiv_proj]
  constructor
  · rintro ⟨y₀, y₁, heq, hP⟩
    rw [Prod.ext_iff] at heq
    have hd0 : π ^ (2 * k) ∣ qval a γ := by
      have h := (mem_maximalIdeal_pow_iff_dvd hπ N _).1 (Ideal.Quotient.eq.1 heq.1)
      have h' : π ^ (2 * k) ∣ qval a γ - π ^ (2 * k) * y₀ :=
        dvd_trans (pow_dvd_pow π (by omega)) h
      have hsum : qval a γ = (qval a γ - π ^ (2 * k) * y₀) + π ^ (2 * k) * y₀ := by ring
      rw [hsum]
      exact dvd_add h' (dvd_mul_right _ _)
    have hd1 : π ^ k ∣ qder a γ := by
      have h := (mem_maximalIdeal_pow_iff_dvd hπ N _).1 (Ideal.Quotient.eq.1 heq.2)
      have h' : π ^ k ∣ qder a γ - π ^ k * y₁ := dvd_trans (pow_dvd_pow π (by omega)) h
      have hsum : qder a γ = (qder a γ - π ^ k * y₁) + π ^ k * y₁ := by ring
      rw [hsum]
      exact dvd_add h' (dvd_mul_right _ _)
    obtain ⟨b₀, hb₀⟩ := hd0
    obtain ⟨b₁, hb₁⟩ := hd1
    refine ⟨b₀, b₁, hb₀, hb₁, ?_⟩
    have e0 : IsLocalRing.residue O b₀ = IsLocalRing.residue O y₀ :=
      residue_eq_of_mk_pow_mul_eq hπ h₀ (by rw [← hb₀]; exact heq.1)
    have e1 : IsLocalRing.residue O b₁ = IsLocalRing.residue O y₁ :=
      residue_eq_of_mk_pow_mul_eq hπ h₁ (by rw [← hb₁]; exact heq.2)
    rw [e0, e1]
    exact hP
  · rintro ⟨b₀, b₁, e0, e1, hP⟩
    exact ⟨b₀, b₁, by rw [e0, e1], hP⟩

end Uniformity.Density.Menu

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Menu.resAdm_read_iff

end AxCheck
