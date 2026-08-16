/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapH.H115b
import Uniformity.ChapH.H115c
import Uniformity.ChapB.B39b

/-!
# Uniformity.ChapH.H116b3i — the planted polygon package (NODE H.116b3-i)

**Chapter H, NODE H.116b3-i** (`blueprint/CHAP-H_general_induction.md`, AMENDMENT **A-H.8**
§3.1), the first of the three sub-nodes A-H.8 split `H.116b3` into.  Four declarations, all at
the frozen A-H.8 signatures:

* `suppVal_alphaParent` — the planted factor's cleared support value at the slope `−u/ℓ` is
  EXACTLY `μ · min (ℓk, u)`;
* `sideMin_alphaParent` — the side's left endpoint is `0` in the shallow branch `ℓk ≤ u` and
  `μ` in the steep branch;
* `npHgt_sideMin_alphaParent` — the polygon height there, as a NAT (this is what `B39a`'s
  `hHf`/`hHz` binders demand);
* `pow_grade_succ_dvd_coeff_alphaParent_sub` — **THE GRADED SWAP BOUND** (A-H.8 finding
  **F-1**): `π ^ (k(μ−j) + 1)` divides the `j`-th coefficient of a planted difference.

plus the export A-H.8 finding **F-3** asks for:

* `pow_dvd_coeff_alphaFrame_sub` — `π ∣ (alphaFrame b' ŵ − alphaFrame b ŵ).coeff i`, which
  lived in the corpus only as the internal `have hframe` inside `H116bR.lean`'s proof of
  `pow_min_succ_dvd_coeff_recentre_alphaParent_sub` (`H116bR.lean:374`).  Its proof here is
  that `have`, copied out verbatim; `H116bR.lean` is untouched.

## Why F-1 is a NEW statement and not a re-reading of a landed one

A-H.7 §6's PROOF step 1 cited `pow_min_succ_dvd_coeff_recentre_alphaParent_sub` for the graded
bound.  Read at the trivial frame `(k', w') = (0, 0)` that lemma's exponent is
`μ · min k 0 + 1 = 1`: it gives only the UNGRADED `π ¹ ∣ δ_j`.  The graded bound below is a
different statement, and it is the one the perturbation estimate of H.116b3-iii needs.  No new
mathematics is involved — `alphaParent_coeff` grades the frame difference by
`(π ^ k) ^ (μ − j)`, and `pow_dvd_coeff_alphaFrame_sub` supplies the extra digit.

## The hull, in one line

`alphaParent_npHgt_ge` puts the polygon on or above the segment from `(0, μk)` to `(μ, 0)`, and
`alphaParent_npHgt_zero` / `alphaParent_npHgt_natDegree` pin BOTH endpoints exactly.  The
cleared weight `j ↦ ℓ·k·(μ−j) + u·j` is affine on `[0, μ]`, so its minimum is at an endpoint:
`0` when `ℓk ≤ u`, `μ` when `u < ℓk`.  The tie `ℓk = u` belongs with the SHALLOW branch (the
whole segment is then the side and `Finset.min'` returns `0`) — that is A-H.8 §3.1 design note
(b), and it is why the `if` tests `ℓ * k ≤ u` and not `ℓ * k < u`.

There is deliberately **no `hk : 1 ≤ k` binder** (A-H.8 §3.1 design note (a)): all four
statements are true at `k = 0` as well.

DEPENDS: H.115b (`alphaParent`, `alphaFrame`, `alphaParent_coeff`, `alphaParent_natDegree`,
`alphaParent_npHgt_ge`, `alphaParent_npHgt_zero`, `alphaParent_npHgt_natDegree`) · H.115c
(`pow_dvd_coeff_comp_X_add_C`) · H.107 (`mem_maximalIdeal_pow_iff_dvd_of_irr`) · CHAP-B B.11
(`npHgt`), B.14 (`suppVal`), B.15 (`npHgt_X`), B.16 (`OnSide`, `sideSet`), B.20 (`sideMin`,
`onSide_of_mem_sideSet`), B39b (`sideSet_nonempty_gen`, imported for the consumer).

**ENVIRONMENT — ENV-H17**; no `[IsAdicComplete]`, no `[Finite (ResidueField O)]`.

## Status

Sorry-free, axiom-free (Lean core only); footprint printed at the end of the file.
-/

namespace Uniformity.Density.Induction

open IsLocalRing Polynomial Uniformity.Density.Leaf

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

/-! ## 0. `ℕ∞` bookkeeping (`private` in H.115b, so re-derived) -/

private theorem enat_smul_nat' (ℓ t : ℕ) : ℓ • ((t : ℕ) : ℕ∞) = ((ℓ * t : ℕ) : ℕ∞) := by
  simp [nsmul_eq_mul]

private theorem enat_smul_mono' {ℓ : ℕ} {x y : ℕ∞} (h : x ≤ y) : ℓ • x ≤ ℓ • y := by
  simp only [nsmul_eq_mul]
  gcongr

/-! ## 1. H.116b3-i (1/4) — the planted factor's support value, exactly -/

/-- **H.116b3-i (1/4).**  The planted factor's cleared support value at the slope `−u/ℓ` is
exactly `μ · min (ℓk, u)`.

`≥` is pointwise off `alphaParent_npHgt_ge` (the affine bound
`ℓk(μ−j) + uj ≥ μ·min(ℓk, u)` for `j ≤ μ`); `≤` is `Finset.inf_le` at whichever endpoint
realises the `min`, and both endpoints are ATTAINED — `alphaParent_npHgt_zero` at `j = 0`
(this is where `hb`, `hz`, `hŵ` enter, through `alphaFrame_coeff_zero_not_dvd`) and monicity
at `j = μ`. -/
theorem suppVal_alphaParent {π : O} (hπ : Irreducible π) {μ k : ℕ} {b : Fin μ → O}
    (hb : ∀ i, b i ∈ maximalIdeal O) {z : ResidueField O} (hz : z ≠ 0) {ŵ : O}
    (hŵ : residue O ŵ = z) (u ℓ : ℕ) :
    suppVal X (alphaParent π b k ŵ) u ℓ = ((μ * min (ℓ * k) u : ℕ) : ℕ∞) := by
  classical
  have hdeg : (alphaParent π b k ŵ).natDegree = μ := alphaParent_natDegree π b k ŵ
  have hmem0 : (0 : ℕ) ∈ Finset.range ((alphaParent π b k ŵ).natDegree + 1) :=
    Finset.mem_range.2 (Nat.succ_pos _)
  have hmemμ : μ ∈ Finset.range ((alphaParent π b k ŵ).natDegree + 1) :=
    Finset.mem_range.2 (by rw [hdeg]; omega)
  refine le_antisymm ?_ ?_
  · by_cases hcase : ℓ * k ≤ u
    · have hle : suppVal X (alphaParent π b k ŵ) u ℓ
          ≤ ℓ • npHgt X (alphaParent π b k ŵ) 0 + ((u * 0 : ℕ) : ℕ∞) := Finset.inf_le hmem0
      rw [alphaParent_npHgt_zero hπ hb hz k hŵ, enat_smul_nat'] at hle
      refine le_trans hle ?_
      rw [← Nat.cast_add, min_eq_left hcase]
      exact_mod_cast Nat.le_of_eq (by ring)
    · have hle : suppVal X (alphaParent π b k ŵ) u ℓ
          ≤ ℓ • npHgt X (alphaParent π b k ŵ) μ + ((u * μ : ℕ) : ℕ∞) := Finset.inf_le hmemμ
      rw [alphaParent_npHgt_natDegree π b k ŵ, smul_zero, zero_add] at hle
      refine le_trans hle ?_
      rw [min_eq_right (by omega : u ≤ ℓ * k)]
      exact_mod_cast Nat.le_of_eq (by ring)
  · refine Finset.le_inf ?_
    intro j hj
    have hjμ : j ≤ μ := by
      have := Finset.mem_range.1 hj
      omega
    calc ((μ * min (ℓ * k) u : ℕ) : ℕ∞)
        ≤ ((ℓ * ((μ - j) * k) + u * j : ℕ) : ℕ∞) := by
          refine Nat.cast_le.2 ?_
          have h1 : min (ℓ * k) u * (μ - j) ≤ (ℓ * k) * (μ - j) :=
            Nat.mul_le_mul_right _ (min_le_left _ _)
          have h2 : min (ℓ * k) u * j ≤ u * j := Nat.mul_le_mul_right _ (min_le_right _ _)
          calc μ * min (ℓ * k) u
              = min (ℓ * k) u * (μ - j) + min (ℓ * k) u * j := by
                rw [← Nat.mul_add, Nat.sub_add_cancel hjμ, Nat.mul_comm]
            _ ≤ (ℓ * k) * (μ - j) + u * j := Nat.add_le_add h1 h2
            _ = ℓ * ((μ - j) * k) + u * j := by ring
      _ = ℓ • ((((μ - j) * k : ℕ)) : ℕ∞) + ((u * j : ℕ) : ℕ∞) := by
          rw [enat_smul_nat']; push_cast; ring
      _ ≤ ℓ • npHgt X (alphaParent π b k ŵ) j + ((u * j : ℕ) : ℕ∞) :=
          add_le_add (enat_smul_mono' (alphaParent_npHgt_ge hπ b k ŵ j)) le_rfl

/-! ## 2. H.116b3-i (2/4) and (3/4) — the side's left endpoint and its height -/

/-- **H.116b3-i (2/4).**  The side's left endpoint of a planted factor: `0` in the shallow
branch `ℓk ≤ u` (where abscissa `0` realises the support value, hence is on the side and is
trivially the `min'`), and `μ` in the steep branch `u < ℓk` (where every `j < μ` is strictly
above the supporting line, so the side is `{μ}`).

The TIE `ℓk = u` goes with the SHALLOW branch: the whole segment `[0, μ]` is then the side and
`Finset.min'` returns `0`. -/
theorem sideMin_alphaParent {π : O} (hπ : Irreducible π) {μ k : ℕ} {b : Fin μ → O}
    (hb : ∀ i, b i ∈ maximalIdeal O) {z : ResidueField O} (hz : z ≠ 0) {ŵ : O}
    (hŵ : residue O ŵ = z) {u ℓ : ℕ}
    (hne : (sideSet X (alphaParent π b k ŵ) u ℓ).Nonempty) :
    sideMin X (alphaParent π b k ŵ) u ℓ hne = if ℓ * k ≤ u then 0 else μ := by
  classical
  have hS := suppVal_alphaParent (k := k) hπ hb hz hŵ u ℓ
  have hdeg : (alphaParent π b k ŵ).natDegree = μ := alphaParent_natDegree π b k ŵ
  split_ifs with hcase
  · -- SHALLOW: abscissa `0` is on the side
    have hon0 : OnSide X (alphaParent π b k ŵ) u ℓ 0 := by
      change ℓ • npHgt X (alphaParent π b k ŵ) 0 + ((u * 0 : ℕ) : ℕ∞)
        = suppVal X (alphaParent π b k ŵ) u ℓ
      rw [alphaParent_npHgt_zero hπ hb hz k hŵ, enat_smul_nat', hS, ← Nat.cast_add,
        min_eq_left hcase]
      exact_mod_cast congrArg (Nat.cast : ℕ → ℕ∞) (by ring)
    have hmem : (0 : ℕ) ∈ sideSet X (alphaParent π b k ŵ) u ℓ :=
      Finset.mem_filter.2 ⟨Finset.mem_range.2 (Nat.succ_pos _), hon0⟩
    change (sideSet X (alphaParent π b k ŵ) u ℓ).min' hne = 0
    exact Nat.le_zero.mp (Finset.min'_le _ _ hmem)
  · -- STEEP: every on-side abscissa is `μ`
    replace hcase : u < ℓ * k := by omega
    have hall : ∀ j ∈ sideSet X (alphaParent π b k ŵ) u ℓ, j = μ := by
      intro j hj
      by_contra hjm
      have hjr : j < μ := by
        have hj' : j ∈ Finset.filter (OnSide X (alphaParent π b k ŵ) u ℓ)
            (Finset.range ((alphaParent π b k ŵ).natDegree + 1)) := hj
        have := Finset.mem_range.1 (Finset.mem_filter.1 hj').1
        omega
      have hon : OnSide X (alphaParent π b k ŵ) u ℓ j := onSide_of_mem_sideSet hj
      have hchain : ((ℓ * ((μ - j) * k) + u * j : ℕ) : ℕ∞) ≤ ((μ * u : ℕ) : ℕ∞) := by
        calc ((ℓ * ((μ - j) * k) + u * j : ℕ) : ℕ∞)
            = ℓ • ((((μ - j) * k : ℕ)) : ℕ∞) + ((u * j : ℕ) : ℕ∞) := by
              rw [enat_smul_nat']; push_cast; ring
          _ ≤ ℓ • npHgt X (alphaParent π b k ŵ) j + ((u * j : ℕ) : ℕ∞) :=
              add_le_add (enat_smul_mono' (alphaParent_npHgt_ge hπ b k ŵ j)) le_rfl
          _ = suppVal X (alphaParent π b k ŵ) u ℓ := hon
          _ = ((μ * min (ℓ * k) u : ℕ) : ℕ∞) := hS
          _ = ((μ * u : ℕ) : ℕ∞) := by rw [min_eq_right (le_of_lt hcase)]
      have hnat : ℓ * ((μ - j) * k) + u * j ≤ μ * u := by exact_mod_cast hchain
      have hgt : u * (μ - j) < (ℓ * k) * (μ - j) :=
        mul_lt_mul_of_pos_right hcase (by omega : 0 < μ - j)
      have heq : u * (μ - j) + u * j = μ * u := by
        rw [← Nat.mul_add, Nat.sub_add_cancel (le_of_lt hjr), Nat.mul_comm]
      have hL : ℓ * ((μ - j) * k) = (ℓ * k) * (μ - j) := by ring
      rw [hL] at hnat
      refine absurd hnat (not_le.2 ?_)
      calc μ * u = u * (μ - j) + u * j := heq.symm
        _ < (ℓ * k) * (μ - j) + u * j := Nat.add_lt_add_right hgt _
    change (sideSet X (alphaParent π b k ŵ) u ℓ).min' hne = μ
    exact hall _ (Finset.min'_mem _ hne)

/-- **H.116b3-i (3/4).**  The polygon height at the side's left endpoint, as a NAT — the shape
`B39a`'s `hHf`/`hHz` binders demand.  Rewrite along (2/4) and read the two pinned endpoints:
`alphaParent_npHgt_zero` in the shallow branch, monicity (`alphaParent_npHgt_natDegree`) in the
steep one. -/
theorem npHgt_sideMin_alphaParent {π : O} (hπ : Irreducible π) {μ k : ℕ} {b : Fin μ → O}
    (hb : ∀ i, b i ∈ maximalIdeal O) {z : ResidueField O} (hz : z ≠ 0) {ŵ : O}
    (hŵ : residue O ŵ = z) {u ℓ : ℕ}
    (hne : (sideSet X (alphaParent π b k ŵ) u ℓ).Nonempty) :
    npHgt X (alphaParent π b k ŵ) (sideMin X (alphaParent π b k ŵ) u ℓ hne)
      = ((if ℓ * k ≤ u then μ * k else 0 : ℕ) : ℕ∞) := by
  rw [sideMin_alphaParent hπ hb hz hŵ hne]
  split_ifs with hcase
  · exact alphaParent_npHgt_zero hπ hb hz k hŵ
  · rw [alphaParent_npHgt_natDegree π b k ŵ, Nat.cast_zero]

/-! ## 3. H.116b3-i (4/4) — the GRADED swap bound, and the exported frame step -/

/-- **A-H.8 finding F-3, EXPORTED.**  `π` divides every coefficient of the difference of two
planted FRAMES whose child lifts agree mod `𝔪`.

This is the internal `have hframe` of `H116bR.lean`'s
`pow_min_succ_dvd_coeff_recentre_alphaParent_sub` (`H116bR.lean:374`), copied out verbatim as a
public declaration; `H116bR.lean` itself is untouched.  The frame difference is
`(monicPoly b' − monicPoly b).comp (X + C (−ŵ))`, `hbb` puts every coefficient of
`monicPoly b' − monicPoly b` in `𝔪`, and H.115c's `pow_dvd_coeff_comp_X_add_C` carries the
divisibility through the recentring. -/
theorem pow_dvd_coeff_alphaFrame_sub {π : O} (hπ : Irreducible π) {μ : ℕ} {b b' : Fin μ → O}
    (hbb : ∀ i, b' i - b i ∈ maximalIdeal O) (ŵ : O) (i : ℕ) :
    π ∣ (alphaFrame b' ŵ - alphaFrame b ŵ).coeff i := by
  have hπd : ∀ x : O, x ∈ maximalIdeal O → π ∣ x := by
    intro x hx
    have h := (mem_maximalIdeal_pow_iff_dvd_of_irr hπ 1 x).1 (by rwa [pow_one])
    rwa [pow_one] at h
  have he : alphaFrame b' ŵ - alphaFrame b ŵ
      = (monicPoly b' - monicPoly b).comp (X + C (-ŵ)) := by
    rw [alphaFrame, alphaFrame, ← sub_comp]
    congr 1
    rw [map_neg, sub_eq_add_neg]
  have hmb : ∀ i, π ^ 1 ∣ (monicPoly b' - monicPoly b).coeff i := by
    intro i
    rw [pow_one, coeff_sub]
    rcases lt_trichotomy i μ with hi | hi | hi
    · rw [monicPoly_coeff_lt b' hi, monicPoly_coeff_lt b hi]
      exact hπd _ (hbb ⟨i, hi⟩)
    · have h1 := (monicPoly_monic b').coeff_natDegree
      have h2 := (monicPoly_monic b).coeff_natDegree
      rw [monicPoly_natDegree] at h1 h2
      rw [hi, h1, h2, sub_self]
      exact dvd_zero _
    · rw [coeff_eq_zero_of_natDegree_lt (by rw [monicPoly_natDegree]; omega),
        coeff_eq_zero_of_natDegree_lt (by rw [monicPoly_natDegree]; omega), sub_self]
      exact dvd_zero _
  have := pow_dvd_coeff_comp_X_add_C (n := fun _ => 1) monotone_const hmb (-ŵ) i
  rw [← he, pow_one] at this
  exact this

/-- **H.116b3-i (4/4) — THE GRADED SWAP BOUND (A-H.8 finding F-1).**  The `j`-th coefficient of
a planted difference carries `π ^ (k(μ − j) + 1)`: one digit past the planted floor AT ITS OWN
GRADE, not merely `π ¹`.

`alphaParent_coeff` grades both terms by `(π ^ k) ^ (μ − j)`; `sub_mul` collects them; the
extra digit is `pow_dvd_coeff_alphaFrame_sub`. -/
theorem pow_grade_succ_dvd_coeff_alphaParent_sub {π : O} (hπ : Irreducible π) {μ : ℕ}
    {b b' : Fin μ → O} (hbb : ∀ i, b' i - b i ∈ maximalIdeal O) (k : ℕ) (ŵ : O) (j : ℕ) :
    π ^ (k * (μ - j) + 1) ∣ (alphaParent π b' k ŵ - alphaParent π b k ŵ).coeff j := by
  have hco : (alphaParent π b' k ŵ - alphaParent π b k ŵ).coeff j
      = (alphaFrame b' ŵ - alphaFrame b ŵ).coeff j * (π ^ k) ^ (μ - j) := by
    rw [coeff_sub, coeff_sub, alphaParent_coeff, alphaParent_coeff, sub_mul]
  obtain ⟨y, hy⟩ := pow_dvd_coeff_alphaFrame_sub hπ hbb ŵ j
  refine ⟨y, ?_⟩
  rw [hco, hy, ← pow_mul, pow_succ]
  ring

end Uniformity.Density.Induction

/-! ## 4. Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Induction.suppVal_alphaParent
#print axioms Uniformity.Density.Induction.sideMin_alphaParent
#print axioms Uniformity.Density.Induction.npHgt_sideMin_alphaParent
#print axioms Uniformity.Density.Induction.pow_dvd_coeff_alphaFrame_sub
#print axioms Uniformity.Density.Induction.pow_grade_succ_dvd_coeff_alphaParent_sub

end AxCheck
