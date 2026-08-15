/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapG.G02
import Uniformity.ChapG.G32
import Uniformity.ChapG.G33
import Uniformity.StrongHensel

/-!
# Uniformity.ChapG.G34 — `exists_inert_lift`

**Chapter G, NODE G.34** (`blueprint/CHAP-G_base_cases_menus.md` §6). A class with a depth-`N`
centre has an `inertType` lift. Construction: read the derivative's exact valuation `m` at the
centre (or manufacture `m = N` by moving `a₁` inside the class when the derivative vanishes),
note `2m ≥ N`, and perturb `a₀` by `π^(2m)·u` with `u` chosen so that the residual pair
`(u, qder/π^m)` is anisotropic — possible by G.32, because `qder/π^m` is a **unit**.

DEPENDS: G.02, G.32, G.33 · landed `typeOf_of_certInert` (`Drainage.lean:329`), `CertInert`,
`Anisotropic`, `aniForm_iff` (`AnisotropicForms.lean:59`), `proj_eq_iff_dvd`,
`IsLocalRing.residue_surjective`, `exists_addVal_eq`.

The blueprint's Case A ("`qder a γ ≠ 0`") is landed as the private helper
`exists_inert_lift_of_ne_zero`; Case B reduces to it by moving `a₁` inside the level-`N` class so
that the derivative becomes the unit-free `π^N` exactly, matching `leancheck`'s own two-case
split (`G.34a`/`G.34b`) without promoting a second public name.

## Status

Sorry-free, axiom-free (Lean core only).
-/

set_option linter.style.longLine false

namespace Uniformity.Density.Menu

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (IsLocalRing.ResidueField O)] {π : O}

/-- **Case A of G.34.** A depth-`N` centre with nonzero derivative gives an `inertType` lift. -/
theorem exists_inert_lift_of_ne_zero (hπ : Irreducible π) {N : ℕ} {a : Fin 2 → O} {γ : O}
    (hT : Tang π a N γ) (hne : qder a γ ≠ 0) :
    ∃ b : Fin 2 → O, proj O 2 N b = proj O 2 N a ∧ typeOf (monicPoly b) = inertType := by
  obtain ⟨m, hm⟩ := exists_addVal_eq hne
  obtain ⟨v, hv⟩ := Uniformity.Hensel.exists_unit_mul_pow_of_addVal_eq hπ hm
  have hmge : (N + 1) / 2 ≤ m := (pow_dvd_iff_le hπ hm ((N + 1) / 2)).1 hT.2
  have h2m : N ≤ 2 * m := by omega
  have hvne : IsLocalRing.residue O (v : O) ≠ 0 :=
    (IsLocalRing.residue_ne_zero_iff_isUnit (v : O)).2 v.isUnit
  obtain ⟨bbar0, hbbar0⟩ := exists_aniForm_of_ne_zero (IsLocalRing.ResidueField O)
    (b₁ := IsLocalRing.residue O (v : O)) hvne
  obtain ⟨u, hu⟩ := IsLocalRing.residue_surjective (R := O) bbar0
  set b : Fin 2 → O := ![a 0 - qval a γ + π ^ (2 * m) * u, a 1] with hbdef
  have hqvalb : qval b γ = π ^ (2 * m) * u := by
    simp only [qval, hbdef, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
    ring
  have hqderb : qder b γ = π ^ m * (v : O) := by
    simp only [qder, hbdef, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_zero]
    exact hv
  have haniso : Anisotropic ![u, (v : O)] := by
    intro p q hpq
    have h0 : IsLocalRing.residue O (quadForm ![u, (v : O)] p q) = 0 :=
      (Ideal.Quotient.eq_zero_iff_mem).2 hpq
    have key : (IsLocalRing.residue O p) ^ 2 - (IsLocalRing.residue O (v : O))
        * (IsLocalRing.residue O p) * (IsLocalRing.residue O q)
        + (IsLocalRing.residue O u) * (IsLocalRing.residue O q) ^ 2 = 0 := by
      rw [← h0, quadForm]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, map_add, map_sub, map_mul, map_pow]
    rw [hu] at key
    obtain ⟨hp, hq⟩ := (aniForm_iff bbar0 (IsLocalRing.residue O (v : O))).2 hbbar0
      (IsLocalRing.residue O p) (IsLocalRing.residue O q) key
    exact ⟨(Ideal.Quotient.eq_zero_iff_mem).1 hp, (Ideal.Quotient.eq_zero_iff_mem).1 hq⟩
  have hcert : CertInert π b (2 * m + 1) := ⟨γ, m, u, (v : O), le_refl _, hqvalb, hqderb, haniso⟩
  refine ⟨b, ?_, typeOf_of_certInert hπ hcert⟩
  rw [proj_eq_iff_dvd hπ]
  intro i
  fin_cases i
  · show π ^ N ∣ (a 0 - b 0)
    have hstep : a 0 - b 0 = qval a γ - π ^ (2 * m) * u := by
      simp only [hbdef, Matrix.cons_val_zero]; ring
    rw [hstep]
    exact dvd_sub hT.1 ((pow_dvd_pow π h2m).mul_right u)
  · show π ^ N ∣ (a 1 - b 1)
    simp only [hbdef, Matrix.cons_val_one, Matrix.cons_val_zero, Matrix.head_cons, sub_self]
    exact dvd_zero _

/-- **G.34.** A depth-`N` centre has an `inertType` lift, both when the derivative is a unit
(Case A, `exists_inert_lift_of_ne_zero`) and when it vanishes (Case B: recentre `a₁` inside the
level-`N` class so the derivative becomes exactly `π^N`, then apply Case A). -/
theorem exists_inert_lift (hπ : Irreducible π) {N : ℕ} {a : Fin 2 → O} {γ : O}
    (hT : Tang π a N γ) :
    ∃ b : Fin 2 → O, proj O 2 N b = proj O 2 N a ∧ typeOf (monicPoly b) = inertType := by
  by_cases hzero : qder a γ = 0
  · set a' : Fin 2 → O := ![a 0, a 1 + π ^ N] with ha'def
    have hproja' : proj O 2 N a' = proj O 2 N a := by
      rw [proj_eq_iff_dvd hπ]
      intro i
      fin_cases i
      · show π ^ N ∣ (a 0 - a' 0); simp [ha'def]
      · show π ^ N ∣ (a 1 - a' 1)
        simp only [ha'def, Matrix.cons_val_one, Matrix.cons_val_zero, Matrix.head_cons]
        exact ⟨-1, by ring⟩
    have hqder'eq : qder a' γ = qder a γ + π ^ N := by
      simp only [qder, ha'def, Matrix.cons_val_one, Matrix.cons_val_zero, Matrix.head_cons]; ring
    have hqder' : qder a' γ = π ^ N := by rw [hqder'eq, hzero, zero_add]
    have hqval'eq : qval a' γ = qval a γ + π ^ N * γ := by
      simp only [qval, ha'def, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]; ring
    have hTa' : Tang π a' N γ := by
      refine ⟨?_, ?_⟩
      · rw [hqval'eq]; exact dvd_add hT.1 (dvd_mul_right _ γ)
      · rw [hqder']; exact pow_dvd_pow π (by omega)
    have hne' : qder a' γ ≠ 0 := by rw [hqder']; exact pow_ne_zero N hπ.ne_zero
    obtain ⟨b, hbproj, hbtype⟩ := exists_inert_lift_of_ne_zero hπ hTa' hne'
    exact ⟨b, hbproj.trans hproja', hbtype⟩
  · exact exists_inert_lift_of_ne_zero hπ hT hzero

end Uniformity.Density.Menu

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Menu.exists_inert_lift_of_ne_zero
#print axioms Uniformity.Density.Menu.exists_inert_lift

end AxCheck
