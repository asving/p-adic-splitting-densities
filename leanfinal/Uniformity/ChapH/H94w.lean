/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapH.H94

/-!
# Uniformity.ChapH.H94w — the SET-LEVEL 2SIDED dominance split, and the 1-parameter trichotomy

**A witness/law file adjacent to NODE H.94, not a blueprint node** (the H09w precedent; landed by
the OM-3 count-layer unit, 2026-08-16).  H.94(iii) lands the δ-substitution `A1Cell.deltaSubst`
as a FORM transport and its ⚠ declares the dominance-region split itself OPEN (blueprint §16
item 6).  This file lands the two *set-level* pieces that are cheap with the landed vocabulary,
without claiming the general split:

* **The 2SIDED split as sets** (the instance the corpus consumes at `n ≤ 3`: `W-12` §S3.4's
  2SIDED handling and HM3.B's B-families, per `EFF.GENIND.30`'s consumption note):
  `ℕ²` (as `Fin 2 → ℕ`) is the DISJOINT union of the two dominance regions
  `{p | p 0 + 1 ≤ p 1}` and `{p | p 1 ≤ p 0}`, each region is the image of an INJECTIVE affine
  parameterization (`mapGE`, `mapLE`), and on the first region the exponent of any `A1Cell 2`
  transports through `deltaSubst` (`exp_transport_GE`, citing H.94's `deltaSubst_exp`).
* **The 1-parameter dominance trichotomy at GENERAL ℕ-coefficients** (`dominance_split_dim1`):
  for affine forms `ν₁ t = c + a·t`, `ν₂ t = d + b·t`, the region `{t | ν₂ t ≤ ν₁ t}` is either
  an upper set `Set.Ici T` (a shifted copy of `ℕ` — one cell) or `Set.Iio T` (a finite union of
  points).  This is the `r = 1` case of the general dominance split with NO restriction on the
  coefficients, proved by `Nat.find` (no division, no uniform-`N` claim).

**⚠ THE GENERAL SPLIT STAYS OPEN IN LEAN.** Nothing here proves the arbitrary-`r`,
arbitrary-coefficient dominance split (`{ν₁ ≥ ν₂} ∩ (shifted product)` = finite disjoint union of
reparameterized shifted products).  A complete elementary MATH proof, with its decomposition
algorithm certified exhaustively (87/87 exact cells), is at
`docs/openmath-campaign/OM-3_count-layer_2026-08-16.md` §A and
`verification/om3_dominance_split_check.py`; §16 item 6's Lean side remains open by the
blueprint's own cost ruling.

DEPENDS: H.94 (`A1Cell.deltaSubst`, `deltaSubst_exp`) · mathlib `Nat.find`.

## Status

Sorry-free, axiom-free (Lean core only).
-/

set_option linter.style.longLine false

namespace Uniformity.Density.Induction

/-! ## The 2SIDED split, set level -/

/-- The strict dominance region `w₂ ≥ w₁ + 1` of the 2SIDED read. -/
def sideGE : Set (Fin 2 → ℕ) := {p | p 0 + 1 ≤ p 1}

/-- The complementary region `w₂ ≤ w₁`. -/
def sideLE : Set (Fin 2 → ℕ) := {p | p 1 ≤ p 0}

/-- The affine parameterization of `sideGE`: `(w, δ) ↦ (w, w + 1 + δ)` — the `δ`-coordinate trick
of `W-12` §S3.4, as a MAP (H.94c transports the forms; this is the set side). -/
def mapGE (t : Fin 2 → ℕ) : Fin 2 → ℕ := ![t 0, t 0 + 1 + t 1]

/-- The affine parameterization of `sideLE`: `(x, δ) ↦ (x + δ, x)`. -/
def mapLE (t : Fin 2 → ℕ) : Fin 2 → ℕ := ![t 0 + t 1, t 0]

theorem mapGE_injective : Function.Injective mapGE := by
  intro s t h
  have h0 : s 0 = t 0 := by simpa [mapGE] using congrFun h 0
  have h1 : s 0 + 1 + s 1 = t 0 + 1 + t 1 := by simpa [mapGE] using congrFun h 1
  funext i
  fin_cases i
  · exact h0
  · show s 1 = t 1
    omega

theorem mapLE_injective : Function.Injective mapLE := by
  intro s t h
  have h0 : s 0 + s 1 = t 0 + t 1 := by simpa [mapLE] using congrFun h 0
  have h1 : s 0 = t 0 := by simpa [mapLE] using congrFun h 1
  funext i
  fin_cases i
  · exact h1
  · show s 1 = t 1
    omega

theorem range_mapGE : Set.range mapGE = sideGE := by
  ext p
  constructor
  · rintro ⟨t, rfl⟩
    show mapGE t 0 + 1 ≤ mapGE t 1
    simp [mapGE]
  · intro hp
    refine ⟨![p 0, p 1 - (p 0 + 1)], ?_⟩
    have h : p 0 + 1 ≤ p 1 := hp
    funext i
    fin_cases i
    · simp [mapGE]
    · simp only [mapGE]
      show p 0 + 1 + (p 1 - (p 0 + 1)) = p 1
      omega

theorem range_mapLE : Set.range mapLE = sideLE := by
  ext p
  constructor
  · rintro ⟨t, rfl⟩
    show mapLE t 1 ≤ mapLE t 0
    simp [mapLE]
  · intro hp
    refine ⟨![p 1, p 0 - p 1], ?_⟩
    have h : p 1 ≤ p 0 := hp
    funext i
    fin_cases i
    · simp only [mapLE]
      show p 1 + (p 0 - p 1) = p 0
      omega
    · simp [mapLE]

/-- The two dominance regions are disjoint. -/
theorem sideGE_disjoint_sideLE : Disjoint sideGE sideLE := by
  rw [Set.disjoint_left]
  intro p hGE hLE
  have h1 : p 0 + 1 ≤ p 1 := hGE
  have h2 : p 1 ≤ p 0 := hLE
  omega

/-- The two dominance regions cover the parameter space. -/
theorem sideGE_union_sideLE : sideGE ∪ sideLE = Set.univ := by
  ext p
  simp only [Set.mem_union, Set.mem_univ, iff_true]
  rcases Nat.lt_or_ge (p 0) (p 1) with h | h
  · exact Or.inl h
  · exact Or.inr h

/-- On `sideGE`, the exponent of any `A1Cell 2` transports through the landed `deltaSubst`:
every point of the region is `mapGE ![w, δ]` for unique `(w, δ)`, and there the original
exponent equals the transported cell's exponent — H.94(iii)'s "same locus image" clause, at set
level. -/
theorem exp_transport_GE (C : A1Cell 2) {p : Fin 2 → ℕ} (hp : p ∈ sideGE) :
    ∃ w δ, p = mapGE ![w, δ] ∧ C.exp p = (C.deltaSubst).exp ![w, δ] := by
  have hpr : p ∈ Set.range mapGE := range_mapGE ▸ hp
  obtain ⟨t, rfl⟩ := hpr
  have hmap : mapGE ![t 0, t 1] = mapGE t := by
    funext i
    fin_cases i <;> simp [mapGE]
  refine ⟨t 0, t 1, hmap.symm, ?_⟩
  show C.exp ![t 0, t 0 + 1 + t 1] = (C.deltaSubst).exp ![t 0, t 1]
  exact (C.deltaSubst_exp (t 0) (t 1)).symm

/-! ## The 1-parameter dominance trichotomy, general coefficients -/

/-- **The `r = 1` dominance split at general ℕ-coefficients.** The region
`{t | d + b·t ≤ c + a·t}` is an upper set `Ici T` (one shifted-`ℕ` cell) or a lower set `Iio T`
(a finite union of points).  No coefficient restriction, no division: `Nat.find` supplies the
threshold. -/
theorem dominance_split_dim1 (a b c d : ℕ) :
    (∃ T, {t : ℕ | d + b * t ≤ c + a * t} = Set.Ici T) ∨
    (∃ T, {t : ℕ | d + b * t ≤ c + a * t} = Set.Iio T) := by
  rcases (Nat.lt_or_ge a b).symm with hab | hab
  · -- `b ≤ a`, upward-closed: `P t → t ≤ t' → P t'`
    have hmono : ∀ t t' : ℕ, t ≤ t' → d + b * t ≤ c + a * t → d + b * t' ≤ c + a * t' := by
      intro t t' htt hP
      have hb : b * t' = b * t + b * (t' - t) := by
        rw [← Nat.mul_add]
        congr 1
        omega
      have ha : a * t' = a * t + a * (t' - t) := by
        rw [← Nat.mul_add]
        congr 1
        omega
      have hba : b * (t' - t) ≤ a * (t' - t) := Nat.mul_le_mul_right _ hab
      omega
    by_cases hex : ∃ t, d + b * t ≤ c + a * t
    · left
      refine ⟨Nat.find hex, ?_⟩
      ext t
      simp only [Set.mem_setOf_eq, Set.mem_Ici]
      constructor
      · intro ht
        exact Nat.find_min' hex ht
      · intro hT
        exact hmono _ _ hT (Nat.find_spec hex)
    · right
      refine ⟨0, ?_⟩
      ext t
      simp only [Set.mem_setOf_eq, Set.mem_Iio]
      have hex' : ∀ s : ℕ, ¬(d + b * s ≤ c + a * s) := fun s hs => hex ⟨s, hs⟩
      exact ⟨fun ht => absurd ht (hex' t), fun h => absurd h (Nat.not_lt_zero t)⟩
  · -- `b > a`: downward-closed, i.e. the complement is upward-closed
    have hanti : ∀ t t' : ℕ, t ≤ t' → ¬(d + b * t ≤ c + a * t) → ¬(d + b * t' ≤ c + a * t') := by
      intro t t' htt hnP hP'
      have hb : b * t' = b * t + b * (t' - t) := by
        rw [← Nat.mul_add]
        congr 1
        omega
      have ha : a * t' = a * t + a * (t' - t) := by
        rw [← Nat.mul_add]
        congr 1
        omega
      have hba : a * (t' - t) ≤ b * (t' - t) := Nat.mul_le_mul_right _ (le_of_lt hab)
      omega
    by_cases hex : ∃ t, ¬(d + b * t ≤ c + a * t)
    · right
      refine ⟨Nat.find hex, ?_⟩
      ext t
      simp only [Set.mem_setOf_eq, Set.mem_Iio]
      constructor
      · intro ht
        by_contra hT
        have hT' : Nat.find hex ≤ t := by omega
        exact hanti _ _ hT' (Nat.find_spec hex) ht
      · intro ht
        have hmin := Nat.find_min hex ht
        by_contra hP
        exact hmin hP
    · left
      refine ⟨0, ?_⟩
      ext t
      simp only [Set.mem_setOf_eq, Set.mem_Ici]
      have hex' : ∀ s : ℕ, d + b * s ≤ c + a * s := by
        intro s
        by_contra hs
        exact hex ⟨s, hs⟩
      exact ⟨fun _ => Nat.zero_le t, fun _ => hex' t⟩

end Uniformity.Density.Induction

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Induction.range_mapGE
#print axioms Uniformity.Density.Induction.range_mapLE
#print axioms Uniformity.Density.Induction.mapGE_injective
#print axioms Uniformity.Density.Induction.mapLE_injective
#print axioms Uniformity.Density.Induction.sideGE_disjoint_sideLE
#print axioms Uniformity.Density.Induction.sideGE_union_sideLE
#print axioms Uniformity.Density.Induction.exp_transport_GE
#print axioms Uniformity.Density.Induction.dominance_split_dim1

end AxCheck
