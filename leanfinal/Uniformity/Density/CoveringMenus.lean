/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.Density.GenuineDensity
import Uniformity.Density.TypePositivity

/-!
# Uniformity.Density.CoveringMenus — only finitely many types occur in degree `n`

**CN-22** of `spec/CERTAIN_NODES_2026-08-14.md`.

`CoveringMenu O n S` (`GenuineDensity.lean:458`) says the finite set `S` of splitting types
contains the type of *every* monic degree-`n` polynomial over `O`. Its docstring asserts, without
proof, that such an `S` exists — `FactorizationType` itself is infinite, and the whole
`Σ_σ R_σ = 1` layer (`TotalMassOne`, `sum_genuineDensity_eq_one_of_drainage`) is contentless
without it. Landed so far only at `n = 1` and `n = 2` (`coveringMenu_two`). This file supplies it
at every `n`.

## Proof

Every pair `(e, f)` occurring in an occurring type has `1 ≤ e`, `1 ≤ f` (CN-04
`efPair_pos_of_mem`) and `e * f ≤ n` (`efPair_mul_le_natDegree` with `typeOf_degree`), hence
`e ≤ n` and `f ≤ n`; and since every summand of `∑ eᵢ fᵢ = n` is at least `1`, the type has at
most `n` pairs. So every occurring type is the image of an element of the **finite** type

  `(k : Fin (n+1)) × Sym (Fin (n+1) × Fin (n+1)) k`

under "read the coordinates as naturals", and the menu is that image. Clamping (`min · n`) is
what makes the witness construction free of dependent-type bookkeeping: the clamp is the identity
on the pairs that actually occur.

This node deliberately does **not** name the menu (spec REJECTED R8): only its existence is
contracted.

## Status

Sorry-free, axiom-free (Lean core only).
-/

set_option linter.style.longLine false
-- The contract signature (`spec/CERTAIN_NODES_2026-08-14.md`, CN-22) carries the standing bundle
-- in full; `[Finite (ResidueField O)]` is part of `CoveringMenu`'s own signature but is not
-- consumed by the finiteness argument.
set_option linter.unusedSectionVars false

namespace Uniformity.Density

open IsLocalRing Polynomial

section Menu

variable (O : Type*) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)]

/-- **CN-22 — a covering menu exists at every degree.** There is a finite set of splitting types
containing the type of every monic degree-`n` polynomial over `O`. -/
theorem exists_coveringMenu (n : ℕ) : ∃ S : Finset FactorizationType, CoveringMenu O n S := by
  classical
  -- the clamp of a pair of naturals into the `(n+1) × (n+1)` grid
  set φ : ℕ × ℕ → Fin (n + 1) × Fin (n + 1) :=
    fun p => (⟨min p.1 n, by omega⟩, ⟨min p.2 n, by omega⟩) with hφ
  refine ⟨Finset.image
    (fun s : (k : Fin (n + 1)) × Sym (Fin (n + 1) × Fin (n + 1)) (k : ℕ) =>
      (⟨(s.2 : Multiset (Fin (n + 1) × Fin (n + 1))).map
        (fun q => ((q.1 : ℕ), (q.2 : ℕ)))⟩ : FactorizationType))
    Finset.univ, ?_⟩
  intro a
  have hmon : (monicPoly a).Monic := monicPoly_monic a
  have hdeg : (monicPoly a).natDegree = n := monicPoly_natDegree a
  set M : Multiset (ℕ × ℕ) := (typeOf (monicPoly a)).data with hM
  -- the pairs occurring in the type are positive and bounded by `n`
  have hbound : ∀ p ∈ M, p.1 ≤ n ∧ p.2 ≤ n := by
    intro p hp
    obtain ⟨h1, h2⟩ := efPair_pos_of_mem hmon hp
    have hle : p.1 * p.2 ≤ n := by
      have h := efPair_mul_le_natDegree hmon hp
      rwa [hdeg] at h
    refine ⟨le_trans (Nat.le_mul_of_pos_right _ h2) hle, ?_⟩
    exact le_trans (le_trans (Nat.le_mul_of_pos_right _ h1) (le_of_eq (Nat.mul_comm _ _))) hle
  -- and there are at most `n` of them, since each contributes at least `1` to the degree
  have hsum : (M.map (fun p : ℕ × ℕ => p.1 * p.2)).sum = n := by
    have h := typeOf_degree hmon
    rw [hdeg] at h
    simp only [FactorizationType.degree] at h
    rwa [← hM] at h
  have hcard : Multiset.card M ≤ n := by
    have h1 : ∀ x ∈ M.map (fun p : ℕ × ℕ => p.1 * p.2), 1 ≤ x := by
      rintro x hx
      obtain ⟨p, hp, rfl⟩ := Multiset.mem_map.1 hx
      obtain ⟨h1, h2⟩ := efPair_pos_of_mem hmon hp
      exact Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by omega))
    have h2 := Multiset.card_nsmul_le_sum h1
    rw [Multiset.card_map, smul_eq_mul, mul_one, hsum] at h2
    exact h2
  -- the type is the image of the clamped multiset
  refine Finset.mem_image.2 ⟨⟨⟨Multiset.card M, by omega⟩, ⟨M.map φ, by simp⟩⟩,
    Finset.mem_univ _, ?_⟩
  refine FactorizationType.ext ?_
  show (M.map φ).map (fun q : Fin (n + 1) × Fin (n + 1) => ((q.1 : ℕ), (q.2 : ℕ))) = M
  have hstep : ∀ p ∈ M, (((φ p).1 : ℕ), ((φ p).2 : ℕ)) = id p := by
    intro p hp
    obtain ⟨h1, h2⟩ := hbound p hp
    simp [hφ, min_eq_left h1, min_eq_left h2]
  calc (M.map φ).map (fun q : Fin (n + 1) × Fin (n + 1) => ((q.1 : ℕ), (q.2 : ℕ)))
      = M.map (fun p => (((φ p).1 : ℕ), ((φ p).2 : ℕ))) := by rw [Multiset.map_map]; rfl
    _ = M.map id := Multiset.map_congr rfl hstep
    _ = M := Multiset.map_id M

end Menu

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.exists_coveringMenu

end AxCheck

end Uniformity.Density
