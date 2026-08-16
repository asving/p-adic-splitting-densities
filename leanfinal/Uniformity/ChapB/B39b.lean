/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapB.B39a

/-!
# Uniformity.ChapB.B39b — the residual lift and the graded solve at one weight

**Chapter B, NODE B.39** `exists_graded_solve` (`blueprint/CHAP-B_leaf_layer.md` §6), ENV-A′
(no completeness, no residue finiteness: the solve is a single step).

**⚠ THE SIGNATURE PROVED HERE IS THE `R3`-REPAIRED ONE, NOT THE A-F.8 FORM.** The A-F.8
re-signed signature is machine-REFUTED — see `B39_REFUTATION_2.lean.txt` in this directory
(`b39_signature_refuted_level`, compiled at the pin). This file adds the one missing
hypothesis

```lean
    (hc : suppVal φ (g * h) u ℓ ≤ ((c : ℕ) : ℕ∞))
```

and proves the result. Authority: the standing statement-change authority (2026-08-05) — the
change is an added hypothesis on a refuted statement, the A-F.6/A-F.8 pattern. **The blueprint
and `leanspec/Leanspec/ChapB.lean` must be re-signed to match** (the orchestrator's adjudication
`A-F.10`); until then the 0e type diff for this node is expected to report the added hypothesis,
and that report is the intended signal, not a defect of this file.

Why `hc` is exactly right, and free downstream: the level-`c` line of slope `−u/ℓ` has lattice
points `(r + ℓk, H* − u·k)` with `r < ℓ` the least abscissa in `c`'s class mod `ℓ` and
`ℓ·H* = c − u·r`. The residual Bézout solve needs `a` slots for `U` and `b` for `V`
(`a = sideDeg g`, `b = sideDeg h`), i.e. `H* ≥ u·(a+b−1)`. From `hc`, `c ≥ u·ℓ·(a+b)` and
`r ≤ ℓ−1` give `ℓ·H* ≥ ℓ·u·(a+b−1) + u`, so every slot has a nonnegative height. At B.41's call
sites `c = suppVal φ f u ℓ + k + 1` and `suppVal φ (g_k h_k) u ℓ = suppVal φ f u ℓ`, so `hc`
holds with room to spare.

## Contents

* `addVal_pow_uniformizer`, `gaussVal_C_pow`, `gaussVal_eq_zero_of_resMk_ne_zero` — small
  valuation facts.
* `exists_resRep` — B.39's step-3 coefficient lift: every element of `resField φ` is
  `resMk π φ 0 P` for a `P` of degree `< φ.degree` (**the RE-PLAN booking "B.39a `resLift`"**,
  in its per-coefficient form; the assembled lift is `resLift` below).
* `dev_mono`, `npHgt_mono`, `suppVal_mono`, `sideSet_mono`, `sideMin_mono`, `sideDeg_mono`,
  `resPoly_mono` — the side data of a single lift term `C (π^K) * P * φ^J`.
* `lineDigit_mul_mono` — the digit of `w * (single lift term)` on the level line, via the
  general product law of `B39a`.
* `resLift` + `dev_resLift`, `degree_resLift_lt`, `suppVal_resLift_ge`, `lineDigit_resLift`,
  `lineDigit_mul_resLift` — the assembled lift and its specification.
* `exists_graded_solve` — the contract (R3-repaired).

## Status

Sorry-free, axiom-free (Lean core only).
-/

namespace Uniformity.Density.Leaf

open Polynomial IsLocalRing

-- ENV-A (blueprint §0.1) plus `hπ : Irreducible π` per signature (ENV-A′).
variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {π : O}

/-! ## 1. Small valuation facts -/

/-- The additive valuation of a power of the uniformizer. -/
theorem addVal_pow_uniformizer (hπ : Irreducible π) :
    ∀ K : ℕ, IsDiscreteValuationRing.addVal O (π ^ K) = (K : ℕ∞)
  | 0 => by simp
  | (K + 1) => by
      rw [pow_succ, IsDiscreteValuationRing.addVal_mul, addVal_pow_uniformizer hπ K,
        IsDiscreteValuationRing.addVal_uniformizer hπ]
      push_cast
      ring

/-- The Gauss valuation of the constant `π ^ K`. -/
theorem gaussVal_C_pow (hπ : Irreducible π) (K : ℕ) :
    gaussVal (Polynomial.C (π ^ K) : Polynomial O) = (K : ℕ∞) := by
  rw [gaussVal, Polynomial.natDegree_C, Finset.range_one, Finset.inf_singleton,
    Polynomial.coeff_C_zero, addVal_pow_uniformizer hπ]

/-- A nonzero residual reduction at height `0` forces Gauss valuation `0`. -/
theorem gaussVal_eq_zero_of_resMk_ne_zero (hπ : Irreducible π) {φ P : Polynomial O}
    (h : resMk π φ 0 P ≠ 0) : gaussVal P = 0 := by
  by_contra hcon
  refine h (resMk_eq_zero_of_lt hπ ?_)
  rcases eq_or_ne (gaussVal P) ⊤ with hT | hT
  · rw [hT]; exact le_top
  obtain ⟨V, hV⟩ := ENat.ne_top_iff_exists.1 hT
  rw [← hV]
  have hVpos : 0 < V := by
    rcases Nat.eq_zero_or_pos V with hz | hp
    · exact absurd (by rw [← hV, hz]; rfl) hcon
    · exact hp
  exact_mod_cast (by omega : 0 + 1 ≤ V)

/-! ## 2. The coefficient lift (B.39's step 3, per coefficient) -/

/-- **The residual representative.** Every element of `resField φ` is the height-`0` residual
reduction of a polynomial of degree `< φ.degree`. -/
theorem exists_resRep (hπ : Irreducible π) {φ : Polynomial O} (hφ : IsKey φ)
    (γ : resField φ) : ∃ P : Polynomial O, P.degree < φ.degree ∧ resMk π φ 0 P = γ := by
  classical
  obtain ⟨Y, hY⟩ := AdjoinRoot.mk_surjective γ
  obtain ⟨Q, hQ⟩ := Polynomial.map_surjective (IsLocalRing.residue O)
    IsLocalRing.residue_surjective Y
  refine ⟨Q %ₘ φ, Polynomial.degree_modByMonic_lt Q hφ.monic, ?_⟩
  have hdig : digPoly π 0 (Q %ₘ φ) = (Q %ₘ φ).map (IsLocalRing.residue O) :=
    digPoly_eq_map hπ (a := Q %ₘ φ) (b := Q %ₘ φ) (by simp)
  have hmap : (Q %ₘ φ).map (IsLocalRing.residue O)
      = Q.map (IsLocalRing.residue O) %ₘ φ.map (IsLocalRing.residue O) :=
    Polynomial.map_modByMonic _ hφ.monic
  have hsplit : Q.map (IsLocalRing.residue O) %ₘ φ.map (IsLocalRing.residue O)
      + φ.map (IsLocalRing.residue O)
        * (Q.map (IsLocalRing.residue O) /ₘ φ.map (IsLocalRing.residue O))
      = Q.map (IsLocalRing.residue O) :=
    Polynomial.modByMonic_add_div (Q.map (IsLocalRing.residue O))
      (φ.map (IsLocalRing.residue O))
  have hkey : AdjoinRoot.mk (φ.map (IsLocalRing.residue O))
      (Q.map (IsLocalRing.residue O) %ₘ φ.map (IsLocalRing.residue O))
      = AdjoinRoot.mk (φ.map (IsLocalRing.residue O)) (Q.map (IsLocalRing.residue O)) := by
    have hc := congrArg (AdjoinRoot.mk (φ.map (IsLocalRing.residue O))) hsplit
    rwa [map_add, map_mul, AdjoinRoot.mk_self, zero_mul, add_zero] at hc
  rw [resMk, hdig, hmap, hkey, hQ, hY]

/-! ## 3. The side data of a single lift term `C (π^K) * P * φ^J` -/

section Mono

variable {φ : Polynomial O} {u ℓ : ℕ}

/-- The development of a single lift term is concentrated at the abscissa `J`. -/
theorem dev_mono (hφ : φ.Monic) (hd : 0 < φ.natDegree) {P : Polynomial O}
    (hP : P.degree < φ.degree) (K J j : ℕ) :
    dev φ (Polynomial.C (π ^ K) * P * φ ^ J) j
      = if j = J then Polynomial.C (π ^ K) * P else 0 := by
  have hw : (Polynomial.C (π ^ K) * P).degree < φ.degree :=
    lt_of_le_of_lt (by rw [← Polynomial.smul_eq_C_mul]; exact Polynomial.degree_smul_le _ _) hP
  have hwn : (Polynomial.C (π ^ K) * P).natDegree < φ.natDegree := by
    by_cases hz : Polynomial.C (π ^ K) * P = 0
    · rw [hz, Polynomial.natDegree_zero]; exact hd
    · refine (Polynomial.natDegree_lt_iff_degree_lt hz).2 ?_
      rwa [Polynomial.degree_eq_natDegree hφ.ne_zero] at hw
  by_cases hj : j = J
  · subst hj
    have hshift := dev_mul_pow hφ j (Polynomial.C (π ^ K) * P) 0
    rw [Nat.add_zero] at hshift
    rw [hshift, if_pos rfl, dev]
    exact (Polynomial.modByMonic_eq_self_iff hφ).2 hw
  · rw [if_neg hj]
    rcases lt_or_gt_of_ne hj with hlt | hgt
    · exact dev_mul_pow_of_lt hφ J _ j hlt
    · obtain ⟨s, hs⟩ := Nat.exists_eq_add_of_lt hgt
      have hshift := dev_mul_pow hφ J (Polynomial.C (π ^ K) * P) (s + 1)
      rw [hs, show J + s + 1 = J + (s + 1) by ring, hshift]
      refine dev_eq_zero_of_lt hφ hd _ (s + 1) ?_
      exact lt_of_lt_of_le hwn (Nat.le_mul_of_pos_left _ (Nat.succ_pos s))

/-- The polygon of a single lift term: height `K` at `J`, empty elsewhere. -/
theorem npHgt_mono (hπ : Irreducible π) (hφ : φ.Monic) (hd : 0 < φ.natDegree)
    {P : Polynomial O} (hP : P.degree < φ.degree) (hP0 : gaussVal P = 0) (K J j : ℕ) :
    npHgt φ (Polynomial.C (π ^ K) * P * φ ^ J) j = if j = J then (K : ℕ∞) else ⊤ := by
  rw [npHgt, dev_mono hφ hd hP K J j]
  by_cases hj : j = J
  · rw [if_pos hj, if_pos hj, gaussVal_mul hπ, gaussVal_C_pow hπ, hP0, add_zero]
  · rw [if_neg hj, if_neg hj, gaussVal_eq_top_iff]

/-- The support value of a single lift term. -/
theorem suppVal_mono (hπ : Irreducible π) (hφ : φ.Monic) (hd : 0 < φ.natDegree)
    (hℓ : 0 < ℓ) {P : Polynomial O} (hP : P.degree < φ.degree) (hP0 : gaussVal P = 0)
    (hPne : P ≠ 0) (K J : ℕ) :
    suppVal φ (Polynomial.C (π ^ K) * P * φ ^ J) u ℓ = ((ℓ * K + u * J : ℕ) : ℕ∞) := by
  have hCne : (Polynomial.C (π ^ K) : Polynomial O) ≠ 0 :=
    Polynomial.C_ne_zero.2 (pow_ne_zero K hπ.ne_zero)
  have hprodne : Polynomial.C (π ^ K) * P * φ ^ J ≠ 0 :=
    mul_ne_zero (mul_ne_zero hCne hPne) (pow_ne_zero J hφ.ne_zero)
  have hJmem : J ∈ Finset.range ((Polynomial.C (π ^ K) * P * φ ^ J).natDegree + 1) := by
    refine Finset.mem_range.2 (Nat.lt_succ_of_le ?_)
    rw [Polynomial.natDegree_mul (mul_ne_zero hCne hPne) (pow_ne_zero J hφ.ne_zero),
      Polynomial.natDegree_pow]
    exact le_trans (Nat.le_mul_of_pos_right J hd) (Nat.le_add_left _ _)
  rw [suppVal]
  refine le_antisymm ?_ (Finset.le_inf fun j _ => ?_)
  · refine le_trans (Finset.inf_le hJmem) ?_
    rw [npHgt_mono hπ hφ hd hP hP0 K J J, if_pos rfl, nsmul_add_cast_gen]
  · by_cases hj : j = J
    · subst hj
      rw [npHgt_mono hπ hφ hd hP hP0 K j j, if_pos rfl, nsmul_add_cast_gen]
    · rw [npHgt_mono hπ hφ hd hP hP0 K J j, if_neg hj]
      simp [hℓ.ne']

/-- The side of a single lift term is the singleton `{J}`. -/
theorem sideSet_mono (hπ : Irreducible π) (hφ : φ.Monic) (hd : 0 < φ.natDegree)
    (hℓ : 0 < ℓ) {P : Polynomial O} (hP : P.degree < φ.degree) (hP0 : gaussVal P = 0)
    (hPne : P ≠ 0) (K J : ℕ) :
    sideSet φ (Polynomial.C (π ^ K) * P * φ ^ J) u ℓ = {J} := by
  classical
  have hsupp := suppVal_mono hπ hφ hd hℓ hP hP0 hPne (u := u) K J
  have hCne : (Polynomial.C (π ^ K) : Polynomial O) ≠ 0 :=
    Polynomial.C_ne_zero.2 (pow_ne_zero K hπ.ne_zero)
  refine Finset.eq_singleton_iff_unique_mem.2 ⟨?_, ?_⟩
  · show J ∈ Finset.filter (OnSide φ (Polynomial.C (π ^ K) * P * φ ^ J) u ℓ)
      (Finset.range ((Polynomial.C (π ^ K) * P * φ ^ J).natDegree + 1))
    refine Finset.mem_filter.2 ⟨Finset.mem_range.2 (Nat.lt_succ_of_le ?_), ?_⟩
    · rw [Polynomial.natDegree_mul (mul_ne_zero hCne hPne) (pow_ne_zero J hφ.ne_zero),
        Polynomial.natDegree_pow]
      exact le_trans (Nat.le_mul_of_pos_right J hd) (Nat.le_add_left _ _)
    · show ℓ • npHgt φ (Polynomial.C (π ^ K) * P * φ ^ J) J + ((u * J : ℕ) : ℕ∞) = _
      rw [npHgt_mono hπ hφ hd hP hP0 K J J, if_pos rfl, nsmul_add_cast_gen, hsupp]
  · intro j hj
    have hon := onSide_of_mem_sideSet hj
    by_contra hne
    have hfin := npHgt_ne_top_of_onSide hℓ (by rw [hsupp]; exact ENat.coe_ne_top _) hon
    rw [npHgt_mono hπ hφ hd hP hP0 K J j, if_neg hne] at hfin
    exact hfin rfl

/-- The left endpoint of a single lift term's side. -/
theorem sideMin_mono (hπ : Irreducible π) (hφ : φ.Monic) (hd : 0 < φ.natDegree)
    (hℓ : 0 < ℓ) {P : Polynomial O} (hP : P.degree < φ.degree) (hP0 : gaussVal P = 0)
    (hPne : P ≠ 0) (K J : ℕ)
    (hne : (sideSet φ (Polynomial.C (π ^ K) * P * φ ^ J) u ℓ).Nonempty) :
    sideMin φ (Polynomial.C (π ^ K) * P * φ ^ J) u ℓ hne = J := by
  have hs := sideSet_mono hπ hφ hd hℓ hP hP0 hPne (u := u) K J
  have hall : ∀ x ∈ sideSet φ (Polynomial.C (π ^ K) * P * φ ^ J) u ℓ, x = J := by
    intro x hx
    rw [hs, Finset.mem_singleton] at hx
    exact hx
  refine le_antisymm (Finset.min'_le _ _ (by rw [hs]; exact Finset.mem_singleton_self J)) ?_
  exact le_of_eq (hall _ (Finset.min'_mem _ hne)).symm

/-- A single lift term's side has residual degree `0`. -/
theorem sideDeg_mono (hπ : Irreducible π) (hφ : φ.Monic) (hd : 0 < φ.natDegree)
    (hℓ : 0 < ℓ) {P : Polynomial O} (hP : P.degree < φ.degree) (hP0 : gaussVal P = 0)
    (hPne : P ≠ 0) (K J : ℕ)
    (hne : (sideSet φ (Polynomial.C (π ^ K) * P * φ ^ J) u ℓ).Nonempty) :
    sideDeg φ (Polynomial.C (π ^ K) * P * φ ^ J) u ℓ hne = 0 := by
  have hs := sideSet_mono hπ hφ hd hℓ hP hP0 hPne (u := u) K J
  have hall : ∀ x ∈ sideSet φ (Polynomial.C (π ^ K) * P * φ ^ J) u ℓ, x = J := by
    intro x hx
    rw [hs, Finset.mem_singleton] at hx
    exact hx
  have hmax : sideMax φ (Polynomial.C (π ^ K) * P * φ ^ J) u ℓ hne = J := by
    refine le_antisymm ?_ (Finset.le_max' _ _ (by rw [hs]; exact Finset.mem_singleton_self J))
    exact le_of_eq (hall _ (Finset.max'_mem _ hne))
  rw [sideDeg, hmax, sideMin_mono hπ hφ hd hℓ hP hP0 hPne K J hne]
  simp

end Mono

/-- Shifting the reading height by an exact power of `π`. -/
theorem resMk_C_pow_mul (hπ : Irreducible π) {φ : Polynomial O} (K : ℕ) (P : Polynomial O) :
    resMk π φ K (Polynomial.C (π ^ K) * P) = resMk π φ 0 P := by
  rw [resMk, resMk, digPoly_eq_map hπ (a := Polynomial.C (π ^ K) * P) (b := P) rfl,
    digPoly_eq_map hπ (a := P) (b := P) (by simp)]

section MonoRes

variable {φ : Polynomial O} {u ℓ : ℕ}

/-- The residual polynomial of a single lift term is the constant `resMk π φ 0 P`. -/
theorem resPoly_mono (hπ : Irreducible π) (hφ : φ.Monic) (hd : 0 < φ.natDegree)
    (hℓ : 0 < ℓ) {P : Polynomial O} (hP : P.degree < φ.degree) (hP0 : gaussVal P = 0)
    (hPne : P ≠ 0) (K J : ℕ)
    (hne : (sideSet φ (Polynomial.C (π ^ K) * P * φ ^ J) u ℓ).Nonempty) :
    resPoly π φ (Polynomial.C (π ^ K) * P * φ ^ J) u ℓ hne K
      = Polynomial.C (resMk π φ 0 P) := by
  rw [resPoly, sideDeg_mono hπ hφ hd hℓ hP hP0 hPne K J hne, Finset.sum_range_one, pow_zero,
    mul_one, resCoeff, sideMin_mono hπ hφ hd hℓ hP hP0 hPne K J hne]
  congr 1
  show resMk π φ (K - u * 0) (dev φ (Polynomial.C (π ^ K) * P * φ ^ J) (J + ℓ * 0)) = _
  simp only [Nat.mul_zero, Nat.sub_zero, Nat.add_zero]
  rw [dev_mono hφ hd hP K J J, if_pos rfl, resMk_C_pow_mul hπ]

/-! ## 4. The digit of `w * (single lift term)` on the level line -/

/-- **The one-sided digit law.** For `w` whose side starts at abscissa `0` with height `H_w`, and
a single lift term `z = C (π^K) * P * φ^J` with `resMk π φ 0 P ≠ 0`, the digit of `w * z` at the
lattice abscissa `J + ℓ·t` and height `H_w + K − u·t` is `(resPoly w).coeff t · resMk π φ 0 P`.
Both cases of `t` are covered: inside `w`'s side by the general master identity of `B39a`, past
it by the off-side vanishing. -/
theorem lineDigit_mul_mono (hπ : Irreducible π) (hφ : IsKey φ) (hu : 0 < u) (hℓ : 0 < ℓ)
    (hcop : Nat.Coprime u ℓ) {w : Polynomial O} (htw : suppVal φ w u ℓ ≠ ⊤)
    (hnw : (sideSet φ w u ℓ).Nonempty) (hwmin : sideMin φ w u ℓ hnw = 0) {Hw : ℕ}
    (hHw : npHgt φ w (sideMin φ w u ℓ hnw) = (Hw : ℕ∞))
    {P : Polynomial O} (hP : P.degree < φ.degree) (hPne : resMk π φ 0 P ≠ 0)
    (K J t : ℕ) (ht : u * t ≤ Hw + K) :
    resMk π φ (Hw + K - u * t)
        (dev φ (w * (Polynomial.C (π ^ K) * P * φ ^ J)) (J + ℓ * t))
      = (resPoly π φ w u ℓ hnw Hw).coeff t * resMk π φ 0 P := by
  classical
  have hP0 : gaussVal P = 0 := gaussVal_eq_zero_of_resMk_ne_zero hπ hPne
  have hPne0 : P ≠ 0 := by
    intro hz0
    rw [hz0, gaussVal_eq_top_iff.2 rfl] at hP0
    exact (ENat.top_ne_zero) hP0
  have hzsupp : suppVal φ (Polynomial.C (π ^ K) * P * φ ^ J) u ℓ
      = ((ℓ * K + u * J : ℕ) : ℕ∞) :=
    suppVal_mono hπ hφ.monic hφ.pos hℓ hP hP0 hPne0 K J
  have htz : suppVal φ (Polynomial.C (π ^ K) * P * φ ^ J) u ℓ ≠ ⊤ := by
    rw [hzsupp]; exact ENat.coe_ne_top _
  have hnz : (sideSet φ (Polynomial.C (π ^ K) * P * φ ^ J) u ℓ).Nonempty := by
    rw [sideSet_mono hπ hφ.monic hφ.pos hℓ hP hP0 hPne0 K J]
    exact ⟨J, Finset.mem_singleton_self J⟩
  have hzmin : sideMin φ (Polynomial.C (π ^ K) * P * φ ^ J) u ℓ hnz = J :=
    sideMin_mono hπ hφ.monic hφ.pos hℓ hP hP0 hPne0 K J hnz
  have hzdeg : sideDeg φ (Polynomial.C (π ^ K) * P * φ ^ J) u ℓ hnz = 0 :=
    sideDeg_mono hπ hφ.monic hφ.pos hℓ hP hP0 hPne0 K J hnz
  have hHz : npHgt φ (Polynomial.C (π ^ K) * P * φ ^ J)
      (sideMin φ (Polynomial.C (π ^ K) * P * φ ^ J) u ℓ hnz) = (K : ℕ∞) := by
    rw [hzmin, npHgt_mono hπ hφ.monic hφ.pos hP hP0 K J J, if_pos rfl]
  have hzres : resPoly π φ (Polynomial.C (π ^ K) * P * φ ^ J) u ℓ hnz K
      = Polynomial.C (resMk π φ 0 P) :=
    resPoly_mono hπ hφ.monic hφ.pos hℓ hP hP0 hPne0 K J hnz
  have habs : sideMin φ w u ℓ hnw + sideMin φ (Polynomial.C (π ^ K) * P * φ ^ J) u ℓ hnz + ℓ * t
      = J + ℓ * t := by rw [hwmin, hzmin]; omega
  by_cases hcase : t ≤ sideDeg φ w u ℓ hnw
  · have hmaster := resMk_dev_mul_gen hπ hφ.monic hφ.pos hu hℓ hcop htw htz hnw hnz hHw hHz
      (k := t) (by omega)
    have hsum : ∑ k₁ ∈ Finset.range (t + 1),
        (resPoly π φ w u ℓ hnw Hw).coeff k₁ * (Polynomial.C (resMk π φ 0 P)).coeff (t - k₁)
        = (resPoly π φ w u ℓ hnw Hw).coeff t * resMk π φ 0 P := by
      rw [Finset.sum_eq_single_of_mem t (Finset.mem_range.2 (Nat.lt_succ_self t)) ?_]
      · rw [Nat.sub_self, Polynomial.coeff_C_zero]
      · intro b hb hbne
        rw [Finset.mem_range] at hb
        rw [Polynomial.coeff_C, if_neg (by omega), mul_zero]
    rw [habs, hzres] at hmaster
    rw [hmaster, hsum]
  · rw [Nat.not_le] at hcase
    have hcoeff : (resPoly π φ w u ℓ hnw Hw).coeff t = 0 :=
      Polynomial.coeff_eq_zero_of_natDegree_lt (by
        rw [(natDegree_resPoly hπ hφ hℓ hcop htw hnw hHw).1]; exact hcase)
    rw [hcoeff, zero_mul]
    have hprodsupp := suppVal_mul_gen hπ hφ hu hℓ hcop htw htz hnw hnz hHw hHz
    have hnpprod := npHgt_mul_gen hπ hφ hu hℓ hcop htw htz hnw hnz hHw hHz
    have htprod : suppVal φ (w * (Polynomial.C (π ^ K) * P * φ ^ J)) u ℓ ≠ ⊤ := by
      rw [hprodsupp]; exact ENat.coe_ne_top _
    have honprod : OnSide φ (w * (Polynomial.C (π ^ K) * P * φ ^ J)) u ℓ
        (sideMin φ w u ℓ hnw + sideMin φ (Polynomial.C (π ^ K) * P * φ ^ J) u ℓ hnz) := by
      show ℓ • npHgt φ (w * (Polynomial.C (π ^ K) * P * φ ^ J))
        (sideMin φ w u ℓ hnw + sideMin φ (Polynomial.C (π ^ K) * P * φ ^ J) u ℓ hnz)
        + ((u * (sideMin φ w u ℓ hnw
            + sideMin φ (Polynomial.C (π ^ K) * P * φ ^ J) u ℓ hnz) : ℕ) : ℕ∞) = _
      rw [hnpprod, nsmul_add_cast_gen, hprodsupp]
    have hnprod : (sideSet φ (w * (Polynomial.C (π ^ K) * P * φ ^ J)) u ℓ).Nonempty :=
      ⟨_, mem_sideSet_of_onSide hφ.monic hφ.pos hℓ htprod honprod⟩
    have hminprod := sideMin_mul_gen hπ hφ hu hℓ hcop htw htz hnw hnz hHw hHz hnprod
    have hdegprod := sideDeg_mul_gen hπ hφ hu hℓ hcop htw htz hnw hnz hHw hHz hnprod
    have hline : ℓ * (Hw + K - u * t) + u * (J + ℓ * t)
        = ℓ * (Hw + K) + u * (sideMin φ w u ℓ hnw
            + sideMin φ (Polynomial.C (π ^ K) * P * φ ^ J) u ℓ hnz) := by
      obtain ⟨W, hW⟩ := Nat.exists_eq_add_of_le ht
      rw [hwmin, hzmin, hW, Nat.add_sub_cancel_left]
      ring
    by_contra hne
    have honS := onSide_of_resMk_ne_zero hπ hφ.monic hφ.pos hℓ hprodsupp hline hne
    obtain ⟨t', ht'le, ht'eq⟩ := onSide_lattice hφ.monic hφ.pos hℓ hcop htprod hnprod honS
    rw [hminprod, hwmin, hzmin] at ht'eq
    have htt' : t = t' := Nat.eq_of_mul_eq_mul_left hℓ (by omega)
    rw [hdegprod, hzdeg] at ht'le
    omega

end MonoRes

end Uniformity.Density.Leaf
