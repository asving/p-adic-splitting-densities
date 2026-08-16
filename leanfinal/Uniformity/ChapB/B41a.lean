/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapB.B39b

/-!
# Uniformity.ChapB.B41a — the initial approximation and the perturbation law

**Chapter B, NODE B.41** step 1 (`blueprint/CHAP-B_leaf_layer.md` §6), ENV-A′.

Two ingredients the graded Hensel iteration of B.41 needs and which are not in the landed
kernel:

* **the level detector** `le_suppVal_succ_of_lineDigits_zero` — a polynomial of weight `≥ S`
  all of whose digits on the level-`S` line vanish has weight `≥ S + 1` (the converse
  direction of B.30's `resCoeff_eq_zero_iff`, read off the side's left endpoint);
* **the perturbation law** `pure_add_of_lt` — adding to a monic full-degree `(u,ℓ)`-pure `x`
  a `y` of smaller degree and *strictly larger weight* changes nothing about the side:
  `x + y` is monic of the same degree, `(u,ℓ)`-pure, with the same left height and the *same*
  residual polynomial.  This is what keeps the residual data of the Hensel iterates fixed.
* **the initial approximation** `exists_monic_pure_lift` — every monic `G ∈ (resField φ)[Y]`
  with nonzero constant term is the residual polynomial of a monic `(u,ℓ)`-pure `g ∈ O[X]` of
  degree `ℓ · deg G · φ.natDegree`.  Built from B39b's assembled lift, with the top
  coefficient's representative pinned to `1` so that the lift comes out monic.

Also here: `eq_zero_of_suppVal_eq_top` (weight `⊤` means zero — the landed
`suppVal_zero_eq_top` is only the easy direction) and `gaussVal_one_add_of_le`.

**Flagged for human review**: new general statements, none of them a signed §-node.

## Status

Sorry-free, axiom-free (Lean core only).
-/

namespace Uniformity.Density.Leaf

open Polynomial IsLocalRing

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {π : O}

/-! ## 1. Weight `⊤` means zero -/

/-- **A polynomial of infinite weight is zero.** -/
theorem eq_zero_of_suppVal_eq_top {φ : Polynomial O} (hφ : φ.Monic) (hd : 0 < φ.natDegree)
    {u ℓ : ℕ} {x : Polynomial O} (h : suppVal φ x u ℓ = ⊤) : x = 0 := by
  classical
  have hall : ∀ j ∈ Finset.range (x.natDegree + 1), dev φ x j = 0 := by
    intro j hj
    have hterm : ℓ • npHgt φ x j + ((u * j : ℕ) : ℕ∞) = ⊤ := by
      rw [suppVal] at h
      have hle := Finset.inf_le (f := fun j => ℓ • npHgt φ x j + ((u * j : ℕ) : ℕ∞)) hj
      rw [h] at hle
      exact top_le_iff.1 hle
    have hnp : npHgt φ x j = ⊤ := by
      by_contra hc
      obtain ⟨V, hV⟩ := ENat.ne_top_iff_exists.1 hc
      rw [← hV, nsmul_add_cast_gen] at hterm
      exact (ENat.coe_ne_top _) hterm
    exact npHgt_eq_top_iff.1 hnp
  have hrep : ∑ j ∈ Finset.range (x.natDegree + 1), dev φ x j * φ ^ j = x :=
    sum_dev_eq hφ hd x (by
      calc x.natDegree < x.natDegree + 1 := Nat.lt_succ_self _
        _ ≤ (x.natDegree + 1) * φ.natDegree := Nat.le_mul_of_pos_right _ hd)
  rw [← hrep]
  refine Finset.sum_eq_zero fun j hj => ?_
  rw [hall j hj, zero_mul]

/-! ## 2. The level detector -/

/-- **The level detector.** If `x` has weight at least `S` and every digit of `x` at a lattice
point of the level-`S` line vanishes, then `x` has weight at least `S + 1`. -/
theorem le_suppVal_succ_of_lineDigits_zero (hπ : Irreducible π) {φ : Polynomial O}
    (hφ : IsKey φ) {u ℓ : ℕ} (hℓ : 0 < ℓ) (hcop : Nat.Coprime u ℓ) {x : Polynomial O} {S : ℕ}
    (hS : ((S : ℕ) : ℕ∞) ≤ suppVal φ x u ℓ)
    (hdig : ∀ j Hj : ℕ, ℓ * Hj + u * j = S → resMk π φ Hj (dev φ x j) = 0) :
    ((S + 1 : ℕ) : ℕ∞) ≤ suppVal φ x u ℓ := by
  classical
  by_contra hcon
  rw [not_le] at hcon
  have hne : suppVal φ x u ℓ ≠ ⊤ := by
    intro hT
    rw [hT] at hcon
    exact absurd hcon (by simp)
  obtain ⟨v, hv⟩ := ENat.ne_top_iff_exists.1 hne
  have hvS : v = S := by
    have h1 : v < S + 1 := by rw [← hv] at hcon; exact_mod_cast hcon
    have h2 : S ≤ v := by rw [← hv] at hS; exact_mod_cast hS
    omega
  have hsupp : suppVal φ x u ℓ = ((S : ℕ) : ℕ∞) := by rw [← hv, hvS]
  have hn : (sideSet φ x u ℓ).Nonempty := sideSet_nonempty_gen φ x u ℓ
  have hon := onSide_of_mem_sideSet (Finset.min'_mem (sideSet φ x u ℓ) hn)
  obtain ⟨Hj, hHjv⟩ := ENat.ne_top_iff_exists.1 (npHgt_ne_top_of_onSide hℓ hne hon)
  have hHj : npHgt φ x (sideMin φ x u ℓ hn) = (Hj : ℕ∞) := hHjv.symm
  have hline : ℓ * Hj + u * (sideMin φ x u ℓ hn) = S := by
    have hq := suppVal_eq_of_onSide hHj hon
    rw [hsupp] at hq
    exact_mod_cast hq.symm
  have hne0 := (natDegree_resPoly hπ hφ hℓ hcop hne hn hHj).2
  refine hne0 ?_
  rw [resPoly_coeff hn, if_pos (Nat.succ_pos _)]
  show resMk π φ (Hj - u * 0) (dev φ x (sideMin φ x u ℓ hn + ℓ * 0)) = 0
  simp only [Nat.mul_zero, Nat.sub_zero, Nat.add_zero]
  exact hdig _ Hj hline

/-! ## 3. A unit plus a small perturbation -/

/-- `1 + z` has Gauss valuation `0` as soon as `z` has Gauss valuation `≥ 1`. -/
theorem gaussVal_one_add_of_le (hπ : Irreducible π) {z : Polynomial O}
    (hz : (1 : ℕ∞) ≤ gaussVal z) : gaussVal ((1 : Polynomial O) + z) = 0 := by
  refine le_antisymm ?_ (by simp)
  by_contra hcon
  rw [not_le] at hcon
  have h1 : ((0 + 1 : ℕ) : ℕ∞) ≤ gaussVal ((1 : Polynomial O) + z) := by
    simpa using Order.add_one_le_of_lt hcon
  have hdvd := (le_gaussVal_iff hπ (k := 1)).1 (by simpa using h1) 0
  have hdvdz := (le_gaussVal_iff hπ (k := 1)).1 (by simpa using hz) 0
  rw [pow_one] at hdvd hdvdz
  rw [Polynomial.coeff_add, Polynomial.coeff_one_zero] at hdvd
  exact hπ.not_isUnit (isUnit_of_dvd_one (by simpa using Dvd.dvd.sub hdvd hdvdz))

/-! ## 4. The perturbation law -/

section Perturb

variable {φ : Polynomial O} {u ℓ : ℕ}

/-- **A higher-weight perturbation leaves the side alone.** For `x` monic, `(u,ℓ)`-pure of
degree `ℓ·n·m` with left height `Hx`, and `y` of smaller degree and weight `> ℓ·Hx`: `x + y` is
monic of the same degree, `(u,ℓ)`-pure with the same left height, and has the *same* residual
polynomial. -/
theorem pure_add_of_lt (hπ : Irreducible π) (hφ : IsKey φ) (hℓ : 0 < ℓ)
    (hcop : Nat.Coprime u ℓ) {x y : Polynomial O} {n : ℕ}
    (hx : x.Monic) (hxdeg : x.natDegree = ℓ * n * φ.natDegree) (hxp : IsPure φ x u ℓ)
    (hxne : (sideSet φ x u ℓ).Nonempty) {Hx : ℕ} (hHx : npHgt φ x 0 = (Hx : ℕ∞))
    (hydeg : y.degree < x.degree)
    (hy : ((ℓ * Hx + 1 : ℕ) : ℕ∞) ≤ suppVal φ y u ℓ) :
    (x + y).Monic ∧ (x + y).natDegree = x.natDegree ∧ IsPure φ (x + y) u ℓ ∧
      npHgt φ (x + y) 0 = (Hx : ℕ∞) ∧
      ∀ hne : (sideSet φ (x + y) u ℓ).Nonempty,
        resPoly π φ (x + y) u ℓ hne Hx = resPoly π φ x u ℓ hxne Hx := by
  classical
  have hxsupp : suppVal φ x u ℓ = ((ℓ * Hx : ℕ) : ℕ∞) := by
    have h := suppVal_eq_of_onSide (u := u) (ℓ := ℓ) (j := 0) hHx hxp.1
    simpa using h
  have hHxn : Hx = u * n := by
    have hd := sideDeg_of_pure hφ.monic hφ.pos hx hxdeg hℓ hcop hxp hxne
    have := height_eq_of_pure hφ.monic hφ.pos hx hxdeg hℓ hcop hxp hxne hHx
    rw [this]
    refine congrArg (fun t => u * t) ?_
    exact Nat.eq_of_mul_eq_mul_left hℓ hd
  -- monicity and the degree
  have hmon : (x + y).Monic := hx.add_of_left hydeg
  have hdegeq : (x + y).natDegree = x.natDegree :=
    Polynomial.natDegree_eq_of_degree_eq (Polynomial.degree_add_eq_left_of_degree_lt hydeg)
  -- the digits on the level line agree
  have hdig : ∀ j Hj : ℕ, ℓ * Hj + u * j = ℓ * Hx →
      resMk π φ Hj (dev φ (x + y) j) = resMk π φ Hj (dev φ x j) := by
    intro j Hj hj
    have bx : ((Hj : ℕ) : ℕ∞) ≤ gaussVal (dev φ x j) := by
      have := le_lineDigit_gaussVal (u := u) hφ.monic hφ.pos hℓ (A := Hj) (r := j)
        (x := x) (t := 0) (by rw [hj, hxsupp])
      simpa using this
    have by' : ((Hj : ℕ) : ℕ∞) ≤ gaussVal (dev φ y j) := by
      have hys : ((ℓ * Hj + u * j : ℕ) : ℕ∞) ≤ suppVal φ y u ℓ := by
        rw [hj]; exact le_trans (by exact_mod_cast (by omega : ℓ * Hx ≤ ℓ * Hx + 1)) hy
      have := le_lineDigit_gaussVal (u := u) hφ.monic hφ.pos hℓ (A := Hj) (r := j)
        (x := y) (t := 0) hys
      simpa using this
    have hyzero : resMk π φ Hj (dev φ y j) = 0 := by
      refine resMk_eq_zero_of_lt hπ ?_
      rcases eq_or_ne (gaussVal (dev φ y j)) ⊤ with hT | hT
      · rw [hT]; exact le_top
      obtain ⟨V, hV⟩ := ENat.ne_top_iff_exists.1 hT
      have hw : suppVal φ y u ℓ ≤ ℓ • npHgt φ y j + ((u * j : ℕ) : ℕ∞) :=
        suppVal_le_weight hφ.monic hφ.pos hℓ u y j
      have hnp : npHgt φ y j = (V : ℕ∞) := hV.symm
      rw [hnp, nsmul_add_cast_gen] at hw
      have hnat : ℓ * Hx + 1 ≤ ℓ * V + u * j := by exact_mod_cast le_trans hy hw
      have hstep : ℓ * Hj < ℓ * V := by omega
      have hlt : Hj < V := Nat.lt_of_mul_lt_mul_left hstep
      rw [← hV]
      exact_mod_cast (by omega : Hj + 1 ≤ V)
    rw [dev_add_of_monic hφ.monic, resMk_add hπ bx by', hyzero, add_zero]
  -- the left height and the weight
  have hnz0 : resMk π φ Hx (dev φ x 0) ≠ 0 := by
    have hne0 := (natDegree_resPoly hπ hφ hℓ hcop (by rw [hxsupp]; exact ENat.coe_ne_top _)
      hxne (by rw [sideMin_of_pure hxp hxne]; exact hHx)).2
    rw [resPoly_coeff hxne, if_pos (Nat.succ_pos _)] at hne0
    intro hz
    refine hne0 ?_
    show resMk π φ (Hx - u * 0) (dev φ x (sideMin φ x u ℓ hxne + ℓ * 0)) = 0
    simp only [Nat.mul_zero, Nat.sub_zero, Nat.add_zero]
    rw [sideMin_of_pure hxp hxne]
    exact hz
  have hnzsum : resMk π φ Hx (dev φ (x + y) 0) ≠ 0 := by
    rw [hdig 0 Hx (by omega)]; exact hnz0
  have hsumsupp : suppVal φ (x + y) u ℓ = ((ℓ * Hx : ℕ) : ℕ∞) := by
    refine le_antisymm ?_ ?_
    · have hnple : npHgt φ (x + y) 0 ≤ ((Hx : ℕ) : ℕ∞) := by
        by_contra hc
        rw [not_le] at hc
        refine hnzsum (resMk_eq_zero_of_lt hπ ?_)
        have h1 : ((Hx : ℕ) : ℕ∞) + 1 ≤ npHgt φ (x + y) 0 := Order.add_one_le_of_lt hc
        calc ((Hx + 1 : ℕ) : ℕ∞) = ((Hx : ℕ) : ℕ∞) + 1 := by push_cast; ring
          _ ≤ npHgt φ (x + y) 0 := h1
      refine le_trans (suppVal_le_weight hφ.monic hφ.pos hℓ u (x + y) 0) ?_
      obtain ⟨V, hV⟩ := ENat.ne_top_iff_exists.1
        (ne_top_of_le_ne_top (ENat.coe_ne_top _) hnple)
      rw [← hV, nsmul_add_cast_gen]
      have hVle : V ≤ Hx := by rw [← hV] at hnple; exact_mod_cast hnple
      have : ℓ * V ≤ ℓ * Hx := Nat.mul_le_mul_left ℓ hVle
      exact_mod_cast (by omega : ℓ * V + u * 0 ≤ ℓ * Hx)
    · refine le_trans (le_min (le_of_eq hxsupp.symm) ?_)
        (min_suppVal_le_suppVal_add hφ.monic hφ.pos hℓ u x y)
      exact le_trans (by exact_mod_cast (by omega : ℓ * Hx ≤ ℓ * Hx + 1)) hy
  have hnpsum : npHgt φ (x + y) 0 = ((Hx : ℕ) : ℕ∞) := by
    have hw : suppVal φ (x + y) u ℓ ≤ ℓ • npHgt φ (x + y) 0 + ((u * 0 : ℕ) : ℕ∞) :=
      suppVal_le_weight hφ.monic hφ.pos hℓ u (x + y) 0
    have hnple : npHgt φ (x + y) 0 ≤ ((Hx : ℕ) : ℕ∞) := by
      by_contra hc
      rw [not_le] at hc
      refine hnzsum (resMk_eq_zero_of_lt hπ ?_)
      have h1 : ((Hx : ℕ) : ℕ∞) + 1 ≤ npHgt φ (x + y) 0 := Order.add_one_le_of_lt hc
      calc ((Hx + 1 : ℕ) : ℕ∞) = ((Hx : ℕ) : ℕ∞) + 1 := by push_cast; ring
        _ ≤ npHgt φ (x + y) 0 := h1
    obtain ⟨V, hV⟩ := ENat.ne_top_iff_exists.1 (ne_top_of_le_ne_top (ENat.coe_ne_top _) hnple)
    have hVle : V ≤ Hx := by rw [← hV] at hnple; exact_mod_cast hnple
    rw [hsumsupp, ← hV, nsmul_add_cast_gen] at hw
    have hnat : ℓ * Hx ≤ ℓ * V + u * 0 := by exact_mod_cast hw
    have hge : Hx ≤ V := Nat.le_of_mul_le_mul_left (by omega) hℓ
    rw [← hV]
    exact_mod_cast (by omega : V = Hx)
  -- purity
  have hon0 : OnSide φ (x + y) u ℓ 0 := by
    show ℓ • npHgt φ (x + y) 0 + ((u * 0 : ℕ) : ℕ∞) = suppVal φ (x + y) u ℓ
    rw [hnpsum, nsmul_add_cast_gen, hsumsupp]
    simp
  have hontop : OnSide φ (x + y) u ℓ (ℓ * n) := by
    have hdx : dev φ x (ℓ * n) = 1 := dev_top hφ.monic hφ.pos hx (μ := ℓ * n) hxdeg
    have hdy : (1 : ℕ∞) ≤ gaussVal (dev φ y (ℓ * n)) := by
      rcases eq_or_ne (gaussVal (dev φ y (ℓ * n))) ⊤ with hT | hT
      · rw [hT]; exact le_top
      obtain ⟨V, hV⟩ := ENat.ne_top_iff_exists.1 hT
      have hw : suppVal φ y u ℓ ≤ ℓ • npHgt φ y (ℓ * n) + ((u * (ℓ * n) : ℕ) : ℕ∞) :=
        suppVal_le_weight hφ.monic hφ.pos hℓ u y (ℓ * n)
      have hnp : npHgt φ y (ℓ * n) = (V : ℕ∞) := hV.symm
      rw [hnp, nsmul_add_cast_gen] at hw
      have hnat : ℓ * Hx + 1 ≤ ℓ * V + u * (ℓ * n) := by exact_mod_cast le_trans hy hw
      have harith : u * (ℓ * n) = ℓ * Hx := by rw [hHxn]; ring
      have hpos : 0 < ℓ * V := by omega
      have hVpos : 0 < V := by
        rcases Nat.eq_zero_or_pos V with hz | hp
        · rw [hz] at hpos; omega
        · exact hp
      rw [← hV]
      exact_mod_cast hVpos
    have hnptop : npHgt φ (x + y) (ℓ * n) = 0 := by
      rw [npHgt, dev_add_of_monic hφ.monic, hdx]
      exact gaussVal_one_add_of_le hπ hdy
    have hidx : (x + y).natDegree / φ.natDegree = ℓ * n := by
      rw [hdegeq, hxdeg]; exact Nat.mul_div_cancel _ hφ.pos
    show ℓ • npHgt φ (x + y) (ℓ * n) + ((u * (ℓ * n) : ℕ) : ℕ∞) = suppVal φ (x + y) u ℓ
    rw [hnptop, hsumsupp]
    have harith : u * (ℓ * n) = ℓ * Hx := by rw [hHxn]; ring
    simp [harith]
  have hpure : IsPure φ (x + y) u ℓ := by
    refine ⟨hon0, ?_⟩
    have hidx : (x + y).natDegree / φ.natDegree = ℓ * n := by
      rw [hdegeq, hxdeg]; exact Nat.mul_div_cancel _ hφ.pos
    rw [hidx]
    exact hontop
  refine ⟨hmon, hdegeq, hpure, hnpsum, fun hne => ?_⟩
  -- the residual polynomials agree, coefficient by coefficient
  refine Polynomial.ext fun k => ?_
  rw [resPoly_coeff_of_pure hπ hφ.monic hφ.pos hmon (by rw [hdegeq, hxdeg]) hℓ hcop hpure hne Hx k,
    resPoly_coeff_of_pure hπ hφ.monic hφ.pos hx hxdeg hℓ hcop hxp hxne Hx k]
  by_cases hk : u * k ≤ Hx
  · exact hdig (ℓ * k) (Hx - u * k) (by
      have h1 : ℓ * (Hx - u * k) + ℓ * (u * k) = ℓ * Hx := by
        rw [← Nat.mul_add]
        exact congrArg (fun t => ℓ * t) (by omega)
      have h2 : u * (ℓ * k) = ℓ * (u * k) := by ring
      omega)
  · have hkn : n < k := by
      by_contra hc
      rw [Nat.not_lt] at hc
      exact hk (le_trans (Nat.mul_le_mul_left u hc) (le_of_eq hHxn.symm))
    have hz1 : dev φ x (ℓ * k) = 0 := by
      refine dev_eq_zero_of_lt hφ.monic hφ.pos x (ℓ * k) ?_
      rw [hxdeg]
      exact mul_lt_mul_of_pos_right (mul_lt_mul_of_pos_left hkn hℓ) hφ.pos
    have hz2 : dev φ (x + y) (ℓ * k) = 0 := by
      refine dev_eq_zero_of_lt hφ.monic hφ.pos (x + y) (ℓ * k) ?_
      rw [hdegeq, hxdeg]
      exact mul_lt_mul_of_pos_right (mul_lt_mul_of_pos_left hkn hℓ) hφ.pos
    rw [hz1, hz2]

end Perturb

/-! ## 5. The initial approximation -/

/-- **The monic pure lift (B.41's step 1).** Every monic `G ∈ (resField φ)[Y]` with nonzero
constant term is the residual polynomial of a monic `(u,ℓ)`-pure `g ∈ O[X]` of degree
`ℓ · deg G · φ.natDegree` and left height `u · deg G`. -/
theorem exists_monic_pure_lift (hπ : Irreducible π) {φ : Polynomial O} (hφ : IsKey φ)
    {u ℓ : ℕ} (hℓ : 0 < ℓ) (hcop : Nat.Coprime u ℓ)
    {G : Polynomial (resField φ)} (hG : G.Monic) (hG0 : G.coeff 0 ≠ 0) :
    ∃ g : Polynomial O, g.Monic ∧ g.natDegree = ℓ * G.natDegree * φ.natDegree ∧
      IsPure φ g u ℓ ∧ npHgt φ g 0 = ((u * G.natDegree : ℕ) : ℕ∞) ∧
      ∀ hne : (sideSet φ g u ℓ).Nonempty,
        resPoly π φ g u ℓ hne (u * G.natDegree) = G := by
  classical
  set n := G.natDegree with hndef
  have hbot : (0 : WithBot ℕ) < φ.degree := Polynomial.natDegree_pos_iff_degree_pos.1 hφ.pos
  -- the coefficient representatives, with the top one pinned to `1`
  obtain ⟨rep, hrepdeg, hrepval, hrepn⟩ : ∃ rep : ℕ → Polynomial O,
      (∀ k, (rep k).degree < φ.degree) ∧ (∀ k, resMk π φ 0 (rep k) = G.coeff k) ∧
      rep n = 1 := by
    choose F hF1 hF2 using fun k => exists_resRep hπ hφ (G.coeff k)
    refine ⟨fun k => if k = n then 1 else F k, fun k => ?_, fun k => ?_, ?_⟩
    · by_cases hk : k = n
      · simp only [if_pos hk, Polynomial.degree_one]; exact hbot
      · simp only [if_neg hk]; exact hF1 k
    · by_cases hk : k = n
      · simp only [if_pos hk]
        rw [resMk_one hπ, hk, hndef]
        exact hG.coeff_natDegree.symm
      · simp only [if_neg hk]; exact hF2 k
    · simp
  have hrep0 : gaussVal (rep 0) = 0 := by
    refine gaussVal_eq_zero_of_resMk_ne_zero hπ (φ := φ) ?_
    rw [hrepval 0]; exact hG0
  set g : Polynomial O := ∑ k ∈ Finset.range (n + 1),
    Polynomial.C (π ^ (u * n - u * k)) * rep k * φ ^ (0 + ℓ * k) with hgdef
  -- the top term is `φ ^ (ℓ * n)` and the tail has smaller degree
  have htop : Polynomial.C (π ^ (u * n - u * n)) * rep n * φ ^ (0 + ℓ * n) = φ ^ (ℓ * n) := by
    rw [hrepn, Nat.sub_self, pow_zero, Polynomial.C_1]
    simp
  have htail : (∑ k ∈ Finset.range n,
      Polynomial.C (π ^ (u * n - u * k)) * rep k * φ ^ (0 + ℓ * k)).degree
      < ((ℓ * n * φ.natDegree : ℕ) : WithBot ℕ) :=
    degree_resLift_lt hφ.monic hφ.pos hℓ rep hrepdeg hℓ
  have hpowdeg : (φ ^ (ℓ * n)).degree = ((ℓ * n * φ.natDegree : ℕ) : WithBot ℕ) := by
    rw [Polynomial.degree_pow, Polynomial.degree_eq_natDegree hφ.monic.ne_zero]
    push_cast
    ring
  have hgsplit : g = φ ^ (ℓ * n) + ∑ k ∈ Finset.range n,
      Polynomial.C (π ^ (u * n - u * k)) * rep k * φ ^ (0 + ℓ * k) := by
    rw [hgdef, Finset.sum_range_succ, htop, add_comm]
  have hgm : g.Monic := by
    rw [hgsplit]
    exact (hφ.monic.pow (ℓ * n)).add_of_left (by rw [hpowdeg]; exact htail)
  have hgdeg : g.natDegree = ℓ * n * φ.natDegree := by
    have hd : g.degree = ((ℓ * n * φ.natDegree : ℕ) : WithBot ℕ) := by
      rw [hgsplit, Polynomial.degree_add_eq_left_of_degree_lt (by rw [hpowdeg]; exact htail),
        hpowdeg]
    exact Polynomial.natDegree_eq_of_degree_eq_some hd
  -- the developments on the lattice
  have hdevg : ∀ k₀, k₀ ≤ n →
      dev φ g (ℓ * k₀) = Polynomial.C (π ^ (u * n - u * k₀)) * rep k₀ := by
    intro k₀ hk₀
    rw [hgdef, dev_finsetSum hφ.monic,
      Finset.sum_eq_single_of_mem k₀ (Finset.mem_range.2 (by omega)) ?_]
    · rw [dev_mono hφ.monic hφ.pos (hrepdeg k₀), if_pos (by omega)]
    · intro b _ hbne
      rw [dev_mono hφ.monic hφ.pos (hrepdeg b), if_neg ?_]
      intro hc
      exact hbne (Nat.eq_of_mul_eq_mul_left hℓ (by omega)).symm
  have hnp0 : npHgt φ g 0 = ((u * n : ℕ) : ℕ∞) := by
    have h := hdevg 0 (Nat.zero_le n)
    rw [Nat.mul_zero] at h
    rw [npHgt, h, gaussVal_mul hπ, gaussVal_C_pow hπ, hrep0, add_zero, Nat.mul_zero,
      Nat.sub_zero]
  have hnptop : npHgt φ g (ℓ * n) = 0 := by
    have h := hdevg n le_rfl
    rw [npHgt, h, hrepn, mul_one, Nat.sub_self, gaussVal_C_pow hπ]
    simp
  have hgsupp : suppVal φ g u ℓ = ((ℓ * (u * n) : ℕ) : ℕ∞) := by
    refine le_antisymm ?_ ?_
    · refine le_trans (suppVal_le_weight hφ.monic hφ.pos hℓ u g 0) ?_
      rw [hnp0, nsmul_add_cast_gen]
      simp
    · have := le_suppVal_resLift (u := u) hπ hφ.monic hφ.pos hℓ rep
        (n := n + 1) (r := 0) (H := u * n) (fun k hk => Nat.mul_le_mul_left u (by omega))
      rw [← hgdef] at this
      refine le_trans ?_ this
      simp
  have hon0 : OnSide φ g u ℓ 0 := by
    show ℓ • npHgt φ g 0 + ((u * 0 : ℕ) : ℕ∞) = suppVal φ g u ℓ
    rw [hnp0, nsmul_add_cast_gen, hgsupp]
    simp
  have hpure : IsPure φ g u ℓ := by
    refine ⟨hon0, ?_⟩
    have hidx : g.natDegree / φ.natDegree = ℓ * n := by
      rw [hgdeg]; exact Nat.mul_div_cancel _ hφ.pos
    rw [hidx]
    show ℓ • npHgt φ g (ℓ * n) + ((u * (ℓ * n) : ℕ) : ℕ∞) = suppVal φ g u ℓ
    rw [hnptop, hgsupp]
    have harith : u * (ℓ * n) = ℓ * (u * n) := by ring
    simp [harith]
  refine ⟨g, hgm, hgdeg, hpure, hnp0, fun hne => ?_⟩
  refine Polynomial.ext fun k => ?_
  rw [resPoly_coeff_of_pure hπ hφ.monic hφ.pos hgm hgdeg hℓ hcop hpure hne (u * n) k]
  by_cases hk : k ≤ n
  · rw [hdevg k hk, resMk_C_pow_mul hπ, hrepval k]
  · have hkn : n < k := by omega
    have hz : dev φ g (ℓ * k) = 0 := by
      refine dev_eq_zero_of_lt hφ.monic hφ.pos g (ℓ * k) ?_
      rw [hgdeg]
      exact mul_lt_mul_of_pos_right (mul_lt_mul_of_pos_left hkn hℓ) hφ.pos
    rw [hz, resMk_of_zero hπ]
    exact (Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)).symm

end Uniformity.Density.Leaf

/-! ## Axiom footprint -/

section AxCheck
#print axioms Uniformity.Density.Leaf.eq_zero_of_suppVal_eq_top
#print axioms Uniformity.Density.Leaf.le_suppVal_succ_of_lineDigits_zero
#print axioms Uniformity.Density.Leaf.gaussVal_one_add_of_le
#print axioms Uniformity.Density.Leaf.pure_add_of_lt
#print axioms Uniformity.Density.Leaf.exists_monic_pure_lift
end AxCheck
