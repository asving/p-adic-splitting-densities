/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapB.B35c
import Uniformity.ChapB.B35d
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
* `le_suppVal_mono`, `le_suppVal_resLift`, `degree_resLift_lt`, `le_lineDigit_gaussVal`,
  `lineDigit_mul_resLift` — the assembled lift `∑_{k<n} C (π^(H−u·k)) · rep k · φ^(r+ℓ·k)`:
  its weight, its degree window, and the convolution law for its digits against a pure `w`.
* `exists_line_base` — the level line's base lattice point `(r, H*)` with `r < ℓ`, and the fact
  that *every* lattice point of the line is `r + ℓ·t`.
* `gaussVal_neg`, `dev_neg`, `suppVal_neg`, `resMk_neg`, `sideSet_nonempty_gen`, `resMk_one`.
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

/-! ## 5. The assembled lift -/

/-- Any single lift term carries at least the weight of its base lattice point. -/
theorem le_suppVal_mono (hπ : Irreducible π) (hφ : φ.Monic) (hd : 0 < φ.natDegree)
    (hℓ : 0 < ℓ) (P : Polynomial O) (K J : ℕ) :
    ((ℓ * K + u * J : ℕ) : ℕ∞) ≤ suppVal φ (Polynomial.C (π ^ K) * P * φ ^ J) u ℓ := by
  refine le_trans ?_ (weight_le_suppVal_mul_pow hπ hφ hd hℓ u (Polynomial.C (π ^ K) * P) J)
  have hgv : ((K : ℕ) : ℕ∞) ≤ gaussVal (Polynomial.C (π ^ K) * P) := by
    rw [gaussVal_mul hπ, gaussVal_C_pow hπ]
    exact le_self_add
  have hsmul : ℓ • ((K : ℕ) : ℕ∞) ≤ ℓ • gaussVal (Polynomial.C (π ^ K) * P) :=
    nsmul_le_nsmul_right hgv ℓ
  calc ((ℓ * K + u * J : ℕ) : ℕ∞) = ℓ • ((K : ℕ) : ℕ∞) + ((u * J : ℕ) : ℕ∞) := by
        rw [nsmul_add_cast_gen]
    _ ≤ ℓ • gaussVal (Polynomial.C (π ^ K) * P) + ((u * J : ℕ) : ℕ∞) :=
        add_le_add hsmul le_rfl

/-- **The assembled lift carries the base weight.** -/
theorem le_suppVal_resLift (hπ : Irreducible π) (hφ : φ.Monic) (hd : 0 < φ.natDegree)
    (hℓ : 0 < ℓ) (rep : ℕ → Polynomial O) {n r H : ℕ} (hslots : ∀ k, k < n → u * k ≤ H) :
    ((ℓ * H + u * r : ℕ) : ℕ∞)
      ≤ suppVal φ (∑ k ∈ Finset.range n,
          Polynomial.C (π ^ (H - u * k)) * rep k * φ ^ (r + ℓ * k)) u ℓ := by
  classical
  refine le_trans (Finset.le_inf ?_)
    (inf_suppVal_le_suppVal_sum hφ hd hℓ u
      (fun k => Polynomial.C (π ^ (H - u * k)) * rep k * φ ^ (r + ℓ * k)) n)
  intro k hk
  rw [Finset.mem_range] at hk
  refine le_trans ?_ (le_suppVal_mono hπ hφ hd hℓ (rep k) (H - u * k) (r + ℓ * k))
  have hkH := hslots k hk
  refine le_of_eq ?_
  congr 1
  obtain ⟨W, hW⟩ := Nat.exists_eq_add_of_le hkH
  rw [hW, Nat.add_sub_cancel_left]
  ring

/-- **The assembled lift stays inside the degree window.** -/
theorem degree_resLift_lt (hφ : φ.Monic) (hd : 0 < φ.natDegree) (hℓ : 0 < ℓ)
    (rep : ℕ → Polynomial O) (hrepdeg : ∀ k, (rep k).degree < φ.degree) {n r H : ℕ}
    (hr : r < ℓ) :
    (∑ k ∈ Finset.range n,
        Polynomial.C (π ^ (H - u * k)) * rep k * φ ^ (r + ℓ * k)).degree
      < ((ℓ * n * φ.natDegree : ℕ) : WithBot ℕ) := by
  classical
  refine (Polynomial.degree_lt_iff_coeff_zero _ _).2 fun i hi => ?_
  rw [Polynomial.finsetSum_coeff]
  refine Finset.sum_eq_zero fun k hk => ?_
  rw [Finset.mem_range] at hk
  have hrepn : (rep k).natDegree < φ.natDegree := by
    by_cases hz : rep k = 0
    · rw [hz, Polynomial.natDegree_zero]; exact hd
    · refine (Polynomial.natDegree_lt_iff_degree_lt hz).2 ?_
      have := hrepdeg k
      rwa [Polynomial.degree_eq_natDegree hφ.ne_zero] at this
  have hterm : (Polynomial.C (π ^ (H - u * k)) * rep k * φ ^ (r + ℓ * k)).natDegree
      < ℓ * n * φ.natDegree := by
    have h1 : (Polynomial.C (π ^ (H - u * k)) * rep k).natDegree ≤ (rep k).natDegree := by
      refine le_trans Polynomial.natDegree_mul_le ?_
      rw [Polynomial.natDegree_C]
      omega
    have h2 : (Polynomial.C (π ^ (H - u * k)) * rep k * φ ^ (r + ℓ * k)).natDegree
        ≤ (rep k).natDegree + (r + ℓ * k) * φ.natDegree := by
      refine le_trans Polynomial.natDegree_mul_le ?_
      rw [Polynomial.natDegree_pow]
      exact Nat.add_le_add h1 le_rfl
    refine lt_of_le_of_lt h2 ?_
    · have hbound : r + ℓ * k ≤ ℓ * n - 1 := by
        have : ℓ * k + ℓ ≤ ℓ * n := by
          have : ℓ * (k + 1) ≤ ℓ * n := Nat.mul_le_mul_left ℓ (by omega)
          calc ℓ * k + ℓ = ℓ * (k + 1) := by ring
            _ ≤ ℓ * n := this
        omega
      have hn : 1 ≤ ℓ * n := by
        have : ℓ * 1 ≤ ℓ * n := Nat.mul_le_mul_left ℓ (by omega)
        omega
      calc (rep k).natDegree + (r + ℓ * k) * φ.natDegree
          ≤ (φ.natDegree - 1) + (ℓ * n - 1) * φ.natDegree := by
            exact Nat.add_le_add (by omega) (Nat.mul_le_mul_right _ hbound)
        _ < ℓ * n * φ.natDegree := by
            have hexp : (ℓ * n - 1) * φ.natDegree + φ.natDegree = ℓ * n * φ.natDegree := by
              have : (ℓ * n - 1) + 1 = ℓ * n := by omega
              calc (ℓ * n - 1) * φ.natDegree + φ.natDegree
                  = ((ℓ * n - 1) + 1) * φ.natDegree := by ring
                _ = ℓ * n * φ.natDegree := by rw [this]
            omega
  exact Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_lt_of_le hterm (by exact_mod_cast hi))

/-- A weight bound on `x` bounds its digits along the level line from below. -/
theorem le_lineDigit_gaussVal (hφ : φ.Monic) (hd : 0 < φ.natDegree) (hℓ : 0 < ℓ)
    {x : Polynomial O} {A r : ℕ} (hS : ((ℓ * A + u * r : ℕ) : ℕ∞) ≤ suppVal φ x u ℓ) (t : ℕ) :
    ((A - u * t : ℕ) : ℕ∞) ≤ gaussVal (dev φ x (r + ℓ * t)) := by
  rcases eq_or_ne (gaussVal (dev φ x (r + ℓ * t))) ⊤ with hT | hT
  · rw [hT]; exact le_top
  obtain ⟨V, hV⟩ := ENat.ne_top_iff_exists.1 hT
  have hw : suppVal φ x u ℓ ≤ ℓ • npHgt φ x (r + ℓ * t) + ((u * (r + ℓ * t) : ℕ) : ℕ∞) :=
    suppVal_le_weight hφ hd hℓ u x (r + ℓ * t)
  have hnp : npHgt φ x (r + ℓ * t) = (V : ℕ∞) := hV.symm
  rw [hnp, nsmul_add_cast_gen] at hw
  have hnat : ℓ * A + u * r ≤ ℓ * V + u * (r + ℓ * t) := by exact_mod_cast le_trans hS hw
  have hstep : ℓ * A ≤ ℓ * (V + u * t) := by
    have hexp : u * (r + ℓ * t) = u * r + ℓ * (u * t) := by ring
    have hexp2 : ℓ * (V + u * t) = ℓ * V + ℓ * (u * t) := by ring
    omega
  have hle : A ≤ V + u * t := Nat.le_of_mul_le_mul_left hstep hℓ
  rw [← hV]
  exact_mod_cast (by omega : A - u * t ≤ V)

/-- **The digit of `w * (assembled lift)` on the level line is the convolution.** -/
theorem lineDigit_mul_resLift (hπ : Irreducible π) (hφ : IsKey φ) (hu : 0 < u) (hℓ : 0 < ℓ)
    (hcop : Nat.Coprime u ℓ) {w : Polynomial O} (htw : suppVal φ w u ℓ ≠ ⊤)
    (hnw : (sideSet φ w u ℓ).Nonempty) (hwmin : sideMin φ w u ℓ hnw = 0) {Hw : ℕ}
    (hHw : npHgt φ w (sideMin φ w u ℓ hnw) = (Hw : ℕ∞))
    {T : Polynomial (resField φ)} {rep : ℕ → Polynomial O}
    (hrepdeg : ∀ k, (rep k).degree < φ.degree)
    (hrepval : ∀ k, resMk π φ 0 (rep k) = T.coeff k)
    (hrep0 : ∀ k, T.coeff k = 0 → rep k = 0)
    {n r H t : ℕ} (hTvan : ∀ k, n ≤ k → T.coeff k = 0) (hslots : ∀ k, k < n → u * k ≤ H)
    (ht : u * t ≤ Hw + H) :
    resMk π φ (Hw + H - u * t)
        (dev φ (w * ∑ k ∈ Finset.range n,
          Polynomial.C (π ^ (H - u * k)) * rep k * φ ^ (r + ℓ * k)) (r + ℓ * t))
      = (T * resPoly π φ w u ℓ hnw Hw).coeff t := by
  classical
  set A := resPoly π φ w u ℓ hnw Hw with hAdef
  set term : ℕ → Polynomial O := fun k =>
    Polynomial.C (π ^ (H - u * k)) * rep k * φ ^ (r + ℓ * k) with htermdef
  -- the weight of `w`
  have hSw : ((ℓ * Hw + u * 0 : ℕ) : ℕ∞) ≤ suppVal φ w u ℓ := by
    refine le_of_eq ?_
    rw [← hwmin] at *
    exact (suppVal_eq_of_onSide hHw (onSide_of_mem_sideSet (Finset.min'_mem _ hnw))).symm
  -- each summand's weight
  have hSterm : ∀ k, k < n → ((ℓ * (Hw + H) + u * r : ℕ) : ℕ∞) ≤ suppVal φ (w * term k) u ℓ := by
    intro k hk
    refine le_trans ?_ (suppVal_add_le_suppVal_mul hπ hφ.monic hφ.pos hℓ u w (term k))
    have h2 : ((ℓ * (H - u * k) + u * (r + ℓ * k) : ℕ) : ℕ∞) ≤ suppVal φ (term k) u ℓ :=
      le_suppVal_mono hπ hφ.monic hφ.pos hℓ (rep k) (H - u * k) (r + ℓ * k)
    have harith : ℓ * (Hw + H) + u * r
        = (ℓ * Hw + u * 0) + (ℓ * (H - u * k) + u * (r + ℓ * k)) := by
      obtain ⟨W, hW⟩ := Nat.exists_eq_add_of_le (hslots k hk)
      rw [hW, Nat.add_sub_cancel_left]
      ring
    rw [harith]
    push_cast
    exact add_le_add (by exact_mod_cast hSw) (by exact_mod_cast h2)
  -- distribute
  rw [Finset.mul_sum, dev_finsetSum hφ.monic,
    resMk_finsetSum hπ _ _ (fun k hk => by
      exact le_lineDigit_gaussVal hφ.monic hφ.pos hℓ
        (hSterm k (Finset.mem_range.1 hk)) t)]
  -- the per-term evaluation
  set F : ℕ → resField φ := fun k => if k ≤ t then T.coeff k * A.coeff (t - k) else 0 with hFdef
  have hterms : ∀ k ∈ Finset.range n,
      resMk π φ (Hw + H - u * t) (dev φ (w * term k) (r + ℓ * t)) = F k := by
    intro k hk
    rw [Finset.mem_range] at hk
    by_cases hT0 : T.coeff k = 0
    · rw [htermdef]
      simp only
      rw [hrep0 k hT0, mul_zero, zero_mul, mul_zero, dev_of_zero, resMk_of_zero hπ, hFdef]
      simp only
      by_cases hkt : k ≤ t
      · rw [if_pos hkt, hT0, zero_mul]
      · rw [if_neg hkt]
    · by_cases hkt : k ≤ t
      · have hukt : u * k + u * (t - k) = u * t := by
          rw [← Nat.mul_add, Nat.add_sub_cancel' hkt]
        have hlkt : ℓ * k + ℓ * (t - k) = ℓ * t := by
          rw [← Nat.mul_add, Nat.add_sub_cancel' hkt]
        have hkH := hslots k hk
        have hPne : resMk π φ 0 (rep k) ≠ 0 := by rw [hrepval k]; exact hT0
        have hmono := lineDigit_mul_mono hπ hφ hu hℓ hcop htw hnw hwmin hHw
          (hrepdeg k) hPne (H - u * k) (r + ℓ * k) (t - k) (by omega)
        rw [hrepval k] at hmono
        have habs : r + ℓ * k + ℓ * (t - k) = r + ℓ * t := by omega
        have hhgt : Hw + (H - u * k) - u * (t - k) = Hw + H - u * t := by omega
        rw [habs, hhgt] at hmono
        rw [htermdef]
        simp only
        rw [hmono, hFdef]
        simp only
        rw [if_pos hkt, mul_comm]
      · -- the term's base abscissa is beyond the read abscissa
        have hlt : r + ℓ * t < r + ℓ * k := by
          have : ℓ * t < ℓ * k := mul_lt_mul_of_pos_left (by omega) hℓ
          omega
        have hzero : dev φ (w * term k) (r + ℓ * t) = 0 := by
          rw [htermdef]
          simp only
          rw [show w * (Polynomial.C (π ^ (H - u * k)) * rep k * φ ^ (r + ℓ * k))
              = (w * (Polynomial.C (π ^ (H - u * k)) * rep k)) * φ ^ (r + ℓ * k) from by ring]
          exact dev_mul_pow_of_lt hφ.monic (r + ℓ * k) _ (r + ℓ * t) hlt
        rw [hzero, resMk_of_zero hπ, hFdef]
        simp only
        rw [if_neg hkt]
  rw [Finset.sum_congr rfl hterms]
  -- and the convolution
  have hcoeff : (T * A).coeff t = ∑ k ∈ Finset.range (t + 1), T.coeff k * A.coeff (t - k) := by
    rw [Polynomial.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  have hFvan : ∀ k, n ≤ k → F k = 0 := by
    intro k hk
    rw [hFdef]
    simp only
    by_cases hkt : k ≤ t
    · rw [if_pos hkt, hTvan k hk, zero_mul]
    · rw [if_neg hkt]
  have hsub1 : Finset.range n ⊆ Finset.range (max n (t + 1)) := by
    intro x hx
    rw [Finset.mem_range] at hx ⊢
    omega
  have hsub2 : Finset.range (t + 1) ⊆ Finset.range (max n (t + 1)) := by
    intro x hx
    rw [Finset.mem_range] at hx ⊢
    omega
  have h1 : ∑ k ∈ Finset.range n, F k = ∑ k ∈ Finset.range (max n (t + 1)), F k := by
    refine Finset.sum_subset hsub1 fun x _ hxn => ?_
    rw [Finset.mem_range] at hxn
    exact hFvan x (Nat.not_lt.1 hxn)
  have h2 : ∑ k ∈ Finset.range (t + 1), F k = ∑ k ∈ Finset.range (max n (t + 1)), F k := by
    refine Finset.sum_subset hsub2 fun x _ hxn => ?_
    rw [Finset.mem_range] at hxn
    have hxt : ¬ x ≤ t := by omega
    rw [hFdef]
    simp only
    rw [if_neg hxt]
  have h3 : ∑ k ∈ Finset.range (t + 1), F k
      = ∑ k ∈ Finset.range (t + 1), T.coeff k * A.coeff (t - k) := by
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [Finset.mem_range] at hk
    rw [hFdef]
    simp only
    rw [if_pos (by omega)]
  rw [hcoeff, ← h3, h2, ← h1]

end MonoRes

/-! ## 6. The base lattice point of the level line -/

/-- **The level line's base.** For a weight `c` at least `u * ℓ` and a slope `−u/ℓ` in lowest
terms, the line of weight `c` has a least lattice abscissa `r < ℓ`, at height `H`; and *every*
lattice point of that line sits at `r + ℓ·t`. -/
theorem exists_line_base {u ℓ : ℕ} (hℓ : 0 < ℓ) (hcop : Nat.Coprime u ℓ) {c : ℕ}
    (hc : u * ℓ ≤ c) :
    ∃ r H : ℕ, r < ℓ ∧ ℓ * H + u * r = c ∧
      ∀ j H' : ℕ, ℓ * H' + u * j = c → ∃ t : ℕ, j = r + ℓ * t := by
  haveI : NeZero ℓ := ⟨hℓ.ne'⟩
  classical
  set r : ℕ := ((c : ZMod ℓ) * ((ZMod.unitOfCoprime u hcop)⁻¹ : (ZMod ℓ)ˣ)).val with hrdef
  have hrlt : r < ℓ := ZMod.val_lt _
  have hmod : u * r ≡ c [MOD ℓ] := by
    rw [← ZMod.natCast_eq_natCast_iff]
    push_cast
    rw [hrdef, ZMod.natCast_val, ZMod.cast_id]
    have hunit : ((ZMod.unitOfCoprime u hcop : (ZMod ℓ)ˣ) : ZMod ℓ) = (u : ZMod ℓ) := rfl
    calc (u : ZMod ℓ) * ((c : ZMod ℓ) * ((ZMod.unitOfCoprime u hcop)⁻¹ : (ZMod ℓ)ˣ))
        = ((ZMod.unitOfCoprime u hcop : (ZMod ℓ)ˣ) : ZMod ℓ)
            * (((ZMod.unitOfCoprime u hcop)⁻¹ : (ZMod ℓ)ˣ) : ZMod ℓ) * (c : ZMod ℓ) := by
          rw [hunit]; ring
      _ = (c : ZMod ℓ) := by
          rw [← Units.val_mul, mul_inv_cancel, Units.val_one, one_mul]
  have hurle : u * r ≤ c := by
    have h1 : u * r ≤ u * ℓ := Nat.mul_le_mul_left u (by omega)
    omega
  have hdvd : ℓ ∣ c - u * r := (Nat.modEq_iff_dvd' hurle).1 hmod
  refine ⟨r, (c - u * r) / ℓ, hrlt, ?_, ?_⟩
  · rw [Nat.mul_div_cancel' hdvd]
    omega
  · intro j H' hj
    have hjmod : u * j ≡ u * r [MOD ℓ] := by
      have h1 : u * j ≡ c [MOD ℓ] := by
        refine (Nat.modEq_iff_dvd' (by omega)).2 ⟨H', by omega⟩
      exact h1.trans hmod.symm
    have hjr : j ≡ r [MOD ℓ] :=
      Nat.ModEq.cancel_left_of_coprime (by simpa [Nat.Coprime] using hcop.symm) hjmod
    have hrr : r % ℓ = r := Nat.mod_eq_of_lt hrlt
    have hjmodl : j % ℓ = r := by
      have := hjr
      rw [Nat.ModEq] at this
      omega
    exact ⟨j / ℓ, by
      have := Nat.div_add_mod j ℓ
      omega⟩

/-! ## 7. Sign flips and unconditional nonemptiness -/

/-- The Gauss valuation is insensitive to sign. -/
theorem gaussVal_neg (z : Polynomial O) : gaussVal (-z) = gaussVal z := by
  rw [gaussVal, gaussVal, Polynomial.natDegree_neg]
  refine Finset.inf_congr rfl fun i _ => ?_
  rw [Polynomial.coeff_neg]
  exact AddValuation.map_neg _ _

/-- The `φ`-development is additive, hence sign-reversing. -/
theorem dev_neg {φ : Polynomial O} (hφ : φ.Monic) (x : Polynomial O) (j : ℕ) :
    dev φ (-x) j = - dev φ x j := by
  have hz := dev_add_of_monic hφ x (-x) j
  rw [add_neg_cancel, dev_of_zero φ j] at hz
  linear_combination -hz

/-- The support value is insensitive to sign. -/
theorem suppVal_neg {φ : Polynomial O} (hφ : φ.Monic) (x : Polynomial O) (u ℓ : ℕ) :
    suppVal φ (-x) u ℓ = suppVal φ x u ℓ := by
  rw [suppVal, suppVal, Polynomial.natDegree_neg]
  refine Finset.inf_congr rfl fun j _ => ?_
  rw [npHgt, npHgt, dev_neg hφ, gaussVal_neg]

/-- **The side is never empty.** The `inf` defining `suppVal` is taken over a nonempty range, so
it is attained; the attaining abscissa is on the side. (The landed `sideSet_nonempty` carries
monicity and a degree hypothesis it does not use; this is the general form.) -/
theorem sideSet_nonempty_gen (φ f : Polynomial O) (u ℓ : ℕ) : (sideSet φ f u ℓ).Nonempty := by
  classical
  obtain ⟨j, hj, hval⟩ := Finset.exists_mem_eq_inf (Finset.range (f.natDegree + 1))
    ⟨0, Finset.mem_range.2 (Nat.succ_pos _)⟩
    (fun j => ℓ • npHgt φ f j + ((u * j : ℕ) : ℕ∞))
  exact ⟨j, Finset.mem_filter.2 ⟨hj, hval.symm⟩⟩

/-- `resMk` of `1` at height `0` is `1`. -/
theorem resMk_one (hπ : Irreducible π) (φ : Polynomial O) :
    resMk π φ 0 (1 : Polynomial O) = 1 := by
  rw [resMk, digPoly_eq_map hπ (a := (1 : Polynomial O)) (b := 1) (by simp), Polynomial.map_one,
    map_one]

/-- `resMk` reverses sign on arguments it can read. -/
theorem resMk_neg (hπ : Irreducible π) {φ : Polynomial O} {K : ℕ} {z : Polynomial O}
    (h : (K : ℕ∞) ≤ gaussVal z) : resMk π φ K (-z) = - resMk π φ K z := by
  have hn : (K : ℕ∞) ≤ gaussVal (-z) := by rw [gaussVal_neg]; exact h
  have hz := resMk_add hπ (φ := φ) (a := z) (b := -z) h hn
  rw [add_neg_cancel, resMk_of_zero hπ] at hz
  linear_combination -hz

/-! ## 8. NODE B.39 — the graded solve at one weight (R3-repaired) -/

/-- **B.39 (R3-repaired) — the graded solve at one weight.** For `g`, `h` monic, `(u,ℓ)`-pure of
`φ.natDegree`-divisible degrees and `(u,ℓ)`-coprime, and `e` of degree `< deg (g*h)` whose weight
is at least `c`, where `c` is at least the weight of `g*h`: there are corrections `U`, `V` inside
the degree windows of `g`, `h` with `suppVal φ (e − (h*U + g*V)) u ℓ ≥ c + 1`.

**`hc` is the A-F.10 repair**: without it the statement is false (`B39_REFUTATION_2.lean.txt`).

**The conclusion also records the two SPLIT weights** `c ≤ suppVal φ h u ℓ + suppVal φ U u ℓ` and
`c ≤ suppVal φ g u ℓ + suppVal φ V u ℓ` — proof-free (the proof establishes them on the way to the
product bounds `c ≤ suppVal φ (h*U) u ℓ`, `c ≤ suppVal φ (g*V) u ℓ`, which are what the error
estimate consumes). They are load-bearing at B.41: its perturbation law `pure_add_of_lt` needs a
weight bound on `U` **alone**, and superadditivity of `suppVal` makes the product bound useless for
that; the split form gives `suppVal φ U u ℓ ≥ c − suppVal φ h u ℓ` by cancellation in `ℕ∞`. -/
theorem exists_graded_solve (hπ : Irreducible π) {φ : Polynomial O} (hφ : IsKey φ)
    {u ℓ : ℕ} (hu : 0 < u) (hℓ : 0 < ℓ) (hcop : Nat.Coprime u ℓ) {g h : Polynomial O}
    (hg : g.Monic) (hh : h.Monic)
    (hgd : φ.natDegree ∣ g.natDegree) (hhd : φ.natDegree ∣ h.natDegree)
    (hgh : GradedCoprime π φ u ℓ g h)
    {c : ℕ} {e : Polynomial O} (hdeg : e.natDegree < (g * h).natDegree)
    (hc : suppVal φ (g * h) u ℓ ≤ ((c : ℕ) : ℕ∞))
    (he : ((c : ℕ) : ℕ∞) ≤ suppVal φ e u ℓ) :
    ∃ U V : Polynomial O, U.degree < g.degree ∧ V.degree < h.degree ∧
      ((c : ℕ) : ℕ∞) ≤ suppVal φ h u ℓ + suppVal φ U u ℓ ∧
      ((c : ℕ) : ℕ∞) ≤ suppVal φ g u ℓ + suppVal φ V u ℓ ∧
      ((c + 1 : ℕ) : ℕ∞) ≤ suppVal φ (e - (h * U + g * V)) u ℓ := by
  classical
  letI : Field (resField φ) := instFieldResField hφ
  obtain ⟨Hg, Hh, hg', hh', hHg0, hHh0, hgp, hhp, hcopGH⟩ := hgh
  -- ## the two factors' side data
  have hgdeg0 : g.natDegree = (g.natDegree / φ.natDegree) * φ.natDegree :=
    (Nat.div_mul_cancel hgd).symm
  have hhdeg0 : h.natDegree = (h.natDegree / φ.natDegree) * φ.natDegree :=
    (Nat.div_mul_cancel hhd).symm
  set a := sideDeg φ g u ℓ hg' with hadef
  set b := sideDeg φ h u ℓ hh' with hbdef
  have hna : ℓ * a = g.natDegree / φ.natDegree :=
    sideDeg_of_pure hφ.monic hφ.pos hg hgdeg0 hℓ hcop hgp hg'
  have hnb : ℓ * b = h.natDegree / φ.natDegree :=
    sideDeg_of_pure hφ.monic hφ.pos hh hhdeg0 hℓ hcop hhp hh'
  have hgdeg : g.natDegree = ℓ * a * φ.natDegree := by rw [hna]; exact hgdeg0
  have hhdeg : h.natDegree = ℓ * b * φ.natDegree := by rw [hnb]; exact hhdeg0
  have hgsupp : suppVal φ g u ℓ = ((u * (ℓ * a) : ℕ) : ℕ∞) :=
    suppVal_of_pure hφ.monic hφ.pos hg hgdeg hgp
  have hhsupp : suppVal φ h u ℓ = ((u * (ℓ * b) : ℕ) : ℕ∞) :=
    suppVal_of_pure hφ.monic hφ.pos hh hhdeg hhp
  have htg : suppVal φ g u ℓ ≠ ⊤ := by rw [hgsupp]; exact ENat.coe_ne_top _
  have hth : suppVal φ h u ℓ ≠ ⊤ := by rw [hhsupp]; exact ENat.coe_ne_top _
  have hHga : Hg = u * a := height_eq_of_pure hφ.monic hφ.pos hg hgdeg hℓ hcop hgp hg' hHg0
  have hHhb : Hh = u * b := height_eq_of_pure hφ.monic hφ.pos hh hhdeg hℓ hcop hhp hh' hHh0
  have hgmin : sideMin φ g u ℓ hg' = 0 := sideMin_of_pure hgp hg'
  have hhmin : sideMin φ h u ℓ hh' = 0 := sideMin_of_pure hhp hh'
  have hHg : npHgt φ g (sideMin φ g u ℓ hg') = (Hg : ℕ∞) := by rw [hgmin]; exact hHg0
  have hHh : npHgt φ h (sideMin φ h u ℓ hh') = (Hh : ℕ∞) := by rw [hhmin]; exact hHh0
  set G := resPoly π φ g u ℓ hg' Hg with hGdef
  set H := resPoly π φ h u ℓ hh' Hh with hHdef
  have hGdeg : G.natDegree = a := (natDegree_resPoly hπ hφ hℓ hcop htg hg' hHg).1
  have hHdeg : H.natDegree = b := (natDegree_resPoly hπ hφ hℓ hcop hth hh' hHh).1
  have hGmonic : G.Monic := by
    show G.coeff G.natDegree = 1
    rw [hGdeg, hGdef,
      resPoly_coeff_of_pure hπ hφ.monic hφ.pos hg hgdeg hℓ hcop hgp hg' Hg a, hHga,
      Nat.sub_self, dev_top hφ.monic hφ.pos hg (μ := ℓ * a) hgdeg, resMk_one hπ]
  have hHmonic : H.Monic := by
    show H.coeff H.natDegree = 1
    rw [hHdeg, hHdef,
      resPoly_coeff_of_pure hπ hφ.monic hφ.pos hh hhdeg hℓ hcop hhp hh' Hh b, hHhb,
      Nat.sub_self, dev_top hφ.monic hφ.pos hh (μ := ℓ * b) hhdeg, resMk_one hπ]
  -- ## the product's degree and weight
  have hghdeg : (g * h).natDegree = ℓ * (a + b) * φ.natDegree := by
    rw [Polynomial.natDegree_mul hg.ne_zero hh.ne_zero, hgdeg, hhdeg]; ring
  have hab : 1 ≤ a + b := by
    rcases Nat.eq_zero_or_pos (a + b) with hz | hp
    · rw [hz] at hghdeg; simp at hghdeg; omega
    · exact hp
  have hghsupp : suppVal φ (g * h) u ℓ = ((u * (ℓ * a) + u * (ℓ * b) : ℕ) : ℕ∞) := by
    rw [(suppVal_mul_of_pure hπ hφ hu hℓ hcop hg hh hgd hhd hgp hhp).1, hgsupp, hhsupp]
    push_cast
    ring
  have hcnat : u * (ℓ * a) + u * (ℓ * b) ≤ c := by
    rw [hghsupp] at hc
    exact_mod_cast hc
  -- ## the level line
  have hcbig : u * ℓ ≤ c := by
    have h1 : u * ℓ * 1 ≤ u * ℓ * (a + b) := Nat.mul_le_mul_left _ hab
    have h2 : u * ℓ * (a + b) = u * (ℓ * a) + u * (ℓ * b) := by ring
    omega
  obtain ⟨r, Hs, hrlt, hline, hlat⟩ := exists_line_base hℓ hcop hcbig
  -- ## the slot bound: `u * (a + b - 1) < Hs`
  have hslot : u * (a + b - 1) < Hs := by
    by_contra hcon
    rw [Nat.not_lt] at hcon
    have h1 : ℓ * Hs ≤ ℓ * (u * (a + b - 1)) := Nat.mul_le_mul_left ℓ hcon
    have h2 : ℓ * (u * (a + b - 1)) = u * ℓ * (a + b - 1) := by ring
    have h3 : u * ℓ * (a + b) = u * ℓ * (a + b - 1) + u * ℓ := by
      have : a + b = (a + b - 1) + 1 := by omega
      calc u * ℓ * (a + b) = u * ℓ * ((a + b - 1) + 1) := by rw [← this]
        _ = u * ℓ * (a + b - 1) + u * ℓ := by ring
    have h4 : u * ℓ * (a + b) = u * (ℓ * a) + u * (ℓ * b) := by ring
    have h5 : u * (r + 1) ≤ u * ℓ := Nat.mul_le_mul_left u (by omega)
    have h6 : u * (r + 1) = u * r + u := by ring
    omega
  -- ## the residual polynomial of `e` read from the line's base
  set E : Polynomial (resField φ) := ∑ t ∈ Finset.range (a + b),
    Polynomial.C (resMk π φ (Hs - u * t) (dev φ e (r + ℓ * t))) * Polynomial.X ^ t with hEdef
  have hEcoeff : ∀ t, E.coeff t = resMk π φ (Hs - u * t) (dev φ e (r + ℓ * t)) := by
    intro t
    rw [hEdef, Uniformity.Hensel.coeff_sum_range_C_mul_X_pow]
    by_cases hlt : t < a + b
    · rw [if_pos hlt]
    · rw [if_neg hlt]
      have hz : dev φ e (r + ℓ * t) = 0 := by
        refine (dev_eq_zero_of_lt hφ.monic hφ.pos e (r + ℓ * t) ?_).symm ▸ rfl
        refine lt_of_lt_of_le hdeg ?_
        rw [hghdeg]
        refine Nat.mul_le_mul_right _ ?_
        have : ℓ * (a + b) ≤ ℓ * t := Nat.mul_le_mul_left ℓ (by omega)
        omega
      rw [hz, resMk_of_zero hπ]
  have hEdegree : E.degree < ((G.natDegree + H.natDegree : ℕ) : WithBot ℕ) := by
    rw [hGdeg, hHdeg]
    refine (Polynomial.degree_lt_iff_coeff_zero _ _).2 fun i hi => ?_
    rw [hEdef, Uniformity.Hensel.coeff_sum_range_C_mul_X_pow, if_neg ?_]
    exact fun hlt => absurd (by exact_mod_cast hi) (by omega)
  -- ## the residual Bézout solve (B.38 = landed `Uniformity.Hensel.exists_solve_field`)
  obtain ⟨U₀, V₀, hU₀deg, hV₀deg, hbezout⟩ :=
    Uniformity.Hensel.exists_solve_field hGmonic hHmonic hcopGH hEdegree
  rw [hGdeg] at hU₀deg
  rw [hHdeg] at hV₀deg
  have hU₀van : ∀ k, a ≤ k → U₀.coeff k = 0 := fun k hk =>
    Polynomial.coeff_eq_zero_of_degree_lt (lt_of_lt_of_le hU₀deg (by exact_mod_cast hk))
  have hV₀van : ∀ k, b ≤ k → V₀.coeff k = 0 := fun k hk =>
    Polynomial.coeff_eq_zero_of_degree_lt (lt_of_lt_of_le hV₀deg (by exact_mod_cast hk))
  -- ## the coefficient representatives
  have hbot : (⊥ : WithBot ℕ) < φ.degree :=
    bot_lt_iff_ne_bot.2 fun hb => hφ.monic.ne_zero (Polynomial.degree_eq_bot.1 hb)
  obtain ⟨repU, hrepUdeg, hrepUval, hrepU0⟩ : ∃ rep : ℕ → Polynomial O,
      (∀ k, (rep k).degree < φ.degree) ∧ (∀ k, resMk π φ 0 (rep k) = U₀.coeff k) ∧
      (∀ k, U₀.coeff k = 0 → rep k = 0) := by
    choose F hF1 hF2 using fun k => exists_resRep hπ hφ (U₀.coeff k)
    refine ⟨fun k => if U₀.coeff k = 0 then 0 else F k, fun k => ?_, fun k => ?_, fun k hz => ?_⟩
    · by_cases hz : U₀.coeff k = 0
      · simp only [if_pos hz, Polynomial.degree_zero]; exact hbot
      · simp only [if_neg hz]; exact hF1 k
    · by_cases hz : U₀.coeff k = 0
      · simp only [if_pos hz]; rw [resMk_of_zero hπ, hz]
      · simp only [if_neg hz]; exact hF2 k
    · simp only [if_pos hz]
  obtain ⟨repV, hrepVdeg, hrepVval, hrepV0⟩ : ∃ rep : ℕ → Polynomial O,
      (∀ k, (rep k).degree < φ.degree) ∧ (∀ k, resMk π φ 0 (rep k) = V₀.coeff k) ∧
      (∀ k, V₀.coeff k = 0 → rep k = 0) := by
    choose F hF1 hF2 using fun k => exists_resRep hπ hφ (V₀.coeff k)
    refine ⟨fun k => if V₀.coeff k = 0 then 0 else F k, fun k => ?_, fun k => ?_, fun k hz => ?_⟩
    · by_cases hz : V₀.coeff k = 0
      · simp only [if_pos hz, Polynomial.degree_zero]; exact hbot
      · simp only [if_neg hz]; exact hF1 k
    · by_cases hz : V₀.coeff k = 0
      · simp only [if_pos hz]; rw [resMk_of_zero hπ, hz]
      · simp only [if_neg hz]; exact hF2 k
    · simp only [if_pos hz]
  -- ## the two lifts
  set HU := Hs - u * b with hHUdef
  set HV := Hs - u * a with hHVdef
  set U := ∑ k ∈ Finset.range a,
    Polynomial.C (π ^ (HU - u * k)) * repU k * φ ^ (r + ℓ * k) with hUdef
  set V := ∑ k ∈ Finset.range b,
    Polynomial.C (π ^ (HV - u * k)) * repV k * φ ^ (r + ℓ * k) with hVdef
  have hslotsU : ∀ k, k < a → u * k ≤ HU := by
    intro k hk
    have h1 : u * (k + b) ≤ u * (a + b - 1) := Nat.mul_le_mul_left u (by omega)
    have h2 : u * (k + b) = u * k + u * b := by ring
    omega
  have hslotsV : ∀ k, k < b → u * k ≤ HV := by
    intro k hk
    have h1 : u * (k + a) ≤ u * (a + b - 1) := Nat.mul_le_mul_left u (by omega)
    have h2 : u * (k + a) = u * k + u * a := by ring
    omega
  have hUdegree : U.degree < g.degree := by
    rw [Polynomial.degree_eq_natDegree hg.ne_zero, hgdeg]
    exact degree_resLift_lt hφ.monic hφ.pos hℓ repU hrepUdeg hrlt
  have hVdegree : V.degree < h.degree := by
    rw [Polynomial.degree_eq_natDegree hh.ne_zero, hhdeg]
    exact degree_resLift_lt hφ.monic hφ.pos hℓ repV hrepVdeg hrlt
  -- ## the two correction terms carry weight `c`
  have hUw : ((c : ℕ) : ℕ∞) ≤ suppVal φ h u ℓ + suppVal φ U u ℓ := by
    have h2 : ((ℓ * HU + u * r : ℕ) : ℕ∞) ≤ suppVal φ U u ℓ :=
      le_suppVal_resLift hπ hφ.monic hφ.pos hℓ repU hslotsU
    rw [hhsupp]
    have harith : c ≤ u * (ℓ * b) + (ℓ * HU + u * r) := by
      have h3 : ℓ * Hs ≤ ℓ * HU + ℓ * (u * b) := by
        rw [hHUdef, ← Nat.mul_add]; exact Nat.mul_le_mul_left ℓ (by omega)
      have h4 : u * (ℓ * b) = ℓ * (u * b) := by ring
      omega
    calc ((c : ℕ) : ℕ∞) ≤ ((u * (ℓ * b) + (ℓ * HU + u * r) : ℕ) : ℕ∞) := by exact_mod_cast harith
      _ = ((u * (ℓ * b) : ℕ) : ℕ∞) + ((ℓ * HU + u * r : ℕ) : ℕ∞) := by push_cast; ring
      _ ≤ ((u * (ℓ * b) : ℕ) : ℕ∞) + suppVal φ U u ℓ := add_le_add le_rfl h2
  have hcU : ((c : ℕ) : ℕ∞) ≤ suppVal φ (h * U) u ℓ :=
    le_trans hUw (suppVal_add_le_suppVal_mul hπ hφ.monic hφ.pos hℓ u h U)
  have hVw : ((c : ℕ) : ℕ∞) ≤ suppVal φ g u ℓ + suppVal φ V u ℓ := by
    have h2 : ((ℓ * HV + u * r : ℕ) : ℕ∞) ≤ suppVal φ V u ℓ :=
      le_suppVal_resLift hπ hφ.monic hφ.pos hℓ repV hslotsV
    rw [hgsupp]
    have harith : c ≤ u * (ℓ * a) + (ℓ * HV + u * r) := by
      have h3 : ℓ * Hs ≤ ℓ * HV + ℓ * (u * a) := by
        rw [hHVdef, ← Nat.mul_add]; exact Nat.mul_le_mul_left ℓ (by omega)
      have h4 : u * (ℓ * a) = ℓ * (u * a) := by ring
      omega
    calc ((c : ℕ) : ℕ∞) ≤ ((u * (ℓ * a) + (ℓ * HV + u * r) : ℕ) : ℕ∞) := by exact_mod_cast harith
      _ = ((u * (ℓ * a) : ℕ) : ℕ∞) + ((ℓ * HV + u * r : ℕ) : ℕ∞) := by push_cast; ring
      _ ≤ ((u * (ℓ * a) : ℕ) : ℕ∞) + suppVal φ V u ℓ := add_le_add le_rfl h2
  have hcV : ((c : ℕ) : ℕ∞) ≤ suppVal φ (g * V) u ℓ :=
    le_trans hVw (suppVal_add_le_suppVal_mul hπ hφ.monic hφ.pos hℓ u g V)
  -- ## the two line-digit identities
  have hLDU : ∀ t : ℕ, u * t ≤ Hs →
      resMk π φ (Hs - u * t) (dev φ (h * U) (r + ℓ * t)) = (U₀ * H).coeff t := by
    intro t ht
    rcases Nat.eq_zero_or_pos a with ha0 | hapos
    · have hU0 : U = 0 := by rw [hUdef, ha0]; simp
      have hU₀0 : U₀ = 0 := by
        refine Polynomial.ext fun i => ?_
        rw [Polynomial.coeff_zero]
        exact hU₀van i (by omega)
      rw [hU0, mul_zero, dev_of_zero, resMk_of_zero hπ, hU₀0, zero_mul, Polynomial.coeff_zero]
    · have hub : u * b ≤ Hs := by
        have h1 : u * b ≤ u * (a + b - 1) := Nat.mul_le_mul_left u (by omega)
        omega
      have hht : Hh + HU = Hs := by rw [hHhb, hHUdef]; omega
      have := lineDigit_mul_resLift hπ hφ hu hℓ hcop hth hh' hhmin hHh hrepUdeg hrepUval hrepU0
        (n := a) (r := r) (H := HU) (t := t) hU₀van hslotsU (by omega)
      rw [hht] at this
      rw [← hUdef] at this
      exact this
  have hLDV : ∀ t : ℕ, u * t ≤ Hs →
      resMk π φ (Hs - u * t) (dev φ (g * V) (r + ℓ * t)) = (V₀ * G).coeff t := by
    intro t ht
    rcases Nat.eq_zero_or_pos b with hb0 | hbpos
    · have hV0 : V = 0 := by rw [hVdef, hb0]; simp
      have hV₀0 : V₀ = 0 := by
        refine Polynomial.ext fun i => ?_
        rw [Polynomial.coeff_zero]
        exact hV₀van i (by omega)
      rw [hV0, mul_zero, dev_of_zero, resMk_of_zero hπ, hV₀0, zero_mul, Polynomial.coeff_zero]
    · have hua : u * a ≤ Hs := by
        have h1 : u * a ≤ u * (a + b - 1) := Nat.mul_le_mul_left u (by omega)
        omega
      have hgt : Hg + HV = Hs := by rw [hHga, hHVdef]; omega
      have := lineDigit_mul_resLift hπ hφ hu hℓ hcop htg hg' hgmin hHg hrepVdeg hrepVval hrepV0
        (n := b) (r := r) (H := HV) (t := t) hV₀van hslotsV (by omega)
      rw [hgt] at this
      rw [← hVdef] at this
      exact this
  -- ## the error's weight
  refine ⟨U, V, hUdegree, hVdegree, hUw, hVw, ?_⟩
  have hlineS : ((ℓ * Hs + u * r : ℕ) : ℕ∞) ≤ suppVal φ e u ℓ := by rw [hline]; exact he
  have hlineU : ((ℓ * Hs + u * r : ℕ) : ℕ∞) ≤ suppVal φ (h * U) u ℓ := by rw [hline]; exact hcU
  have hlineV : ((ℓ * Hs + u * r : ℕ) : ℕ∞) ≤ suppVal φ (g * V) u ℓ := by rw [hline]; exact hcV
  -- the error carries at least weight `c`
  have hcD : ((c : ℕ) : ℕ∞) ≤ suppVal φ (e - (h * U + g * V)) u ℓ := by
    have hsum : ((c : ℕ) : ℕ∞) ≤ suppVal φ (h * U + g * V) u ℓ :=
      le_trans (le_min hcU hcV) (min_suppVal_le_suppVal_add hφ.monic hφ.pos hℓ u _ _)
    have hneg : ((c : ℕ) : ℕ∞) ≤ suppVal φ (-(h * U + g * V)) u ℓ := by
      rw [suppVal_neg hφ.monic]; exact hsum
    rw [sub_eq_add_neg]
    exact le_trans (le_min he hneg) (min_suppVal_le_suppVal_add hφ.monic hφ.pos hℓ u _ _)
  by_contra hcon
  rw [not_le] at hcon
  -- the error's support value is exactly `c`
  have hDne : suppVal φ (e - (h * U + g * V)) u ℓ ≠ ⊤ := by
    intro hT
    rw [hT] at hcon
    exact absurd hcon (by simp)
  obtain ⟨vD, hvD⟩ := ENat.ne_top_iff_exists.1 hDne
  have hvDlt : vD < c + 1 := by
    rw [← hvD] at hcon
    exact_mod_cast hcon
  have hvDge : c ≤ vD := by
    rw [← hvD] at hcD
    exact_mod_cast hcD
  have hDsupp : suppVal φ (e - (h * U + g * V)) u ℓ = ((c : ℕ) : ℕ∞) := by
    rw [← hvD]
    exact_mod_cast (by omega : vD = c)
  -- read the digit at the side's left endpoint
  have hnD : (sideSet φ (e - (h * U + g * V)) u ℓ).Nonempty :=
    sideSet_nonempty_gen φ (e - (h * U + g * V)) u ℓ
  have honD := onSide_of_mem_sideSet (Finset.min'_mem (sideSet φ (e - (h * U + g * V)) u ℓ) hnD)
  obtain ⟨HD, hHDv⟩ := ENat.ne_top_iff_exists.1 (npHgt_ne_top_of_onSide hℓ hDne honD)
  have hHD : npHgt φ (e - (h * U + g * V))
      (sideMin φ (e - (h * U + g * V)) u ℓ hnD) = (HD : ℕ∞) := hHDv.symm
  have hDline : ℓ * HD + u * (sideMin φ (e - (h * U + g * V)) u ℓ hnD) = c := by
    have hq := suppVal_eq_of_onSide hHD honD
    rw [hDsupp] at hq
    exact_mod_cast hq.symm
  obtain ⟨t, htq⟩ := hlat (sideMin φ (e - (h * U + g * V)) u ℓ hnD) HD hDline
  have hHDt : HD + u * t = Hs := by
    rw [htq] at hDline
    refine Nat.eq_of_mul_eq_mul_left hℓ ?_
    have hexp : u * (r + ℓ * t) = u * r + ℓ * (u * t) := by ring
    have h1 : ℓ * (HD + u * t) = ℓ * HD + ℓ * (u * t) := by ring
    omega
  have hut : u * t ≤ Hs := by omega
  have hne0 := (natDegree_resPoly hπ hφ hℓ hcop hDne hnD hHD).2
  -- the digit at the left endpoint vanishes, contradicting B.30
  have hzero : resMk π φ (Hs - u * t) (dev φ (e - (h * U + g * V)) (r + ℓ * t)) = 0 := by
    have bE : ((Hs - u * t : ℕ) : ℕ∞) ≤ gaussVal (dev φ e (r + ℓ * t)) :=
      le_lineDigit_gaussVal hφ.monic hφ.pos hℓ hlineS t
    have bU : ((Hs - u * t : ℕ) : ℕ∞) ≤ gaussVal (dev φ (h * U) (r + ℓ * t)) :=
      le_lineDigit_gaussVal hφ.monic hφ.pos hℓ hlineU t
    have bV : ((Hs - u * t : ℕ) : ℕ∞) ≤ gaussVal (dev φ (g * V) (r + ℓ * t)) :=
      le_lineDigit_gaussVal hφ.monic hφ.pos hℓ hlineV t
    have bUn : ((Hs - u * t : ℕ) : ℕ∞) ≤ gaussVal (-dev φ (h * U) (r + ℓ * t)) := by
      rw [gaussVal_neg]; exact bU
    have bVn : ((Hs - u * t : ℕ) : ℕ∞) ≤ gaussVal (-dev φ (g * V) (r + ℓ * t)) := by
      rw [gaussVal_neg]; exact bV
    have bsum : ((Hs - u * t : ℕ) : ℕ∞)
        ≤ gaussVal (-dev φ (h * U) (r + ℓ * t) + -dev φ (g * V) (r + ℓ * t)) :=
      le_trans (le_min bUn bVn) (min_gaussVal_le_gaussVal_add _ _)
    have hsplit : dev φ (e - (h * U + g * V)) (r + ℓ * t)
        = dev φ e (r + ℓ * t)
          + (-dev φ (h * U) (r + ℓ * t) + -dev φ (g * V) (r + ℓ * t)) := by
      rw [sub_eq_add_neg, dev_add_of_monic hφ.monic, dev_neg hφ.monic,
        dev_add_of_monic hφ.monic]
      ring
    rw [hsplit, resMk_add hπ bE bsum, resMk_add hπ bUn bVn, resMk_neg hπ bU, resMk_neg hπ bV,
      hLDU t hut, hLDV t hut, ← hEcoeff t, hbezout, Polynomial.coeff_add,
      mul_comm H U₀, mul_comm G V₀]
    ring
  refine hne0 ?_
  rw [resPoly_coeff hnD, if_pos (Nat.succ_pos _)]
  show resMk π φ (HD - u * 0)
    (dev φ (e - (h * U + g * V)) (sideMin φ (e - (h * U + g * V)) u ℓ hnD + ℓ * 0)) = 0
  simp only [Nat.mul_zero, Nat.sub_zero, Nat.add_zero]
  rw [htq, show HD = Hs - u * t from by omega]
  exact hzero

end Uniformity.Density.Leaf



/-! ## Axiom footprint -/

section AxCheck
#print axioms Uniformity.Density.Leaf.addVal_pow_uniformizer
#print axioms Uniformity.Density.Leaf.gaussVal_C_pow
#print axioms Uniformity.Density.Leaf.gaussVal_eq_zero_of_resMk_ne_zero
#print axioms Uniformity.Density.Leaf.exists_resRep
#print axioms Uniformity.Density.Leaf.dev_mono
#print axioms Uniformity.Density.Leaf.npHgt_mono
#print axioms Uniformity.Density.Leaf.suppVal_mono
#print axioms Uniformity.Density.Leaf.sideSet_mono
#print axioms Uniformity.Density.Leaf.sideMin_mono
#print axioms Uniformity.Density.Leaf.sideDeg_mono
#print axioms Uniformity.Density.Leaf.resMk_C_pow_mul
#print axioms Uniformity.Density.Leaf.resPoly_mono
#print axioms Uniformity.Density.Leaf.lineDigit_mul_mono
#print axioms Uniformity.Density.Leaf.le_suppVal_mono
#print axioms Uniformity.Density.Leaf.le_suppVal_resLift
#print axioms Uniformity.Density.Leaf.degree_resLift_lt
#print axioms Uniformity.Density.Leaf.le_lineDigit_gaussVal
#print axioms Uniformity.Density.Leaf.lineDigit_mul_resLift
#print axioms Uniformity.Density.Leaf.exists_line_base
#print axioms Uniformity.Density.Leaf.gaussVal_neg
#print axioms Uniformity.Density.Leaf.dev_neg
#print axioms Uniformity.Density.Leaf.suppVal_neg
#print axioms Uniformity.Density.Leaf.sideSet_nonempty_gen
#print axioms Uniformity.Density.Leaf.resMk_one
#print axioms Uniformity.Density.Leaf.resMk_neg
#print axioms Uniformity.Density.Leaf.exists_graded_solve
end AxCheck
