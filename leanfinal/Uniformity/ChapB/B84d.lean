/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapB.B15
import Uniformity.ChapB.B80
import Uniformity.ChapB.B83Kit

/-!
# Uniformity.ChapB.B84d — the `q = 3` SPLIT gate (two blocks, fires B.80)

**Chapter B, NODE B.84 instance (iv)** [gate] (`blueprint/CHAP-B_leaf_layer.md` §10), ENV-C
concrete. One signed declaration: `gate_split_three`.

*The instance* (blueprint's row (iv)): `O := ℤ_[3]`, `π := 3`, `a = ![3, 1, 3]`, so
`f = monicPoly a = X³ + 3X² + X + 3 = (X + 3)(X² + 1)`; two order-0 blocks `φ₁ = X`,
`φ₂ = X² + 4` with peel `g₁ = X + 3`, `g₂ = X² + 1`, both `e = 1`; `N = 2`.

As at `q = 2`, the second key is a **lift**: `dev φ₂ g₂ 0 = −3 ≠ 0`, so that block is `Visible`.
Taking `φ₂ = g₂` would make `dev = 0` and nothing could fire (B.75's junk direction).

| block | key `φ` | peel `g` | `dev₀` | heights | side | `sideDeg` | `order1Type` |
|---|---|---|---|---|---|---|---|
| 1 | `X` (`m = 1`) | `X + 3` | `3` | `(1, 0)` | `(1,1)`, argmin `{0,1}` | `1` | `⟨{(1,1)}⟩` |
| 2 | `X² + 4` (`m = 2`) | `X² + 1` | `−3` | `(1, 0)` | `(1,1)`, argmin `{0,1}` | `1` | `⟨{(1,2)}⟩` |

`⟨{(1,1)}⟩.data + ⟨{(1,2)}⟩.data = {(1,1),(1,2)}`. The `𝔽₃`-irreducibility of `X² + 1` is the
same new leg as B.84 (i)'s, here reached through `residue ℤ_[3] 4 = 1`.

## The A-F.12 discharge, per block, with the arithmetic displayed

```
block 1 :  m = 1, deg g₁ = 1  ⟹  1 · 1 · deg ψ ≤ ℓ · 1 · deg ψ = gS.natDegree ≤ 1  ⟹  deg ψ = 1
block 2 :  m = 2, deg g₂ = 2  ⟹  1 · 2 · deg ψ ≤ ℓ · 2 · deg ψ = gS.natDegree ≤ 2  ⟹  deg ψ = 1
```

— the SECOND disjunct in both blocks, uniform in the window-class member, `B-BOX-1`-free.

DEPENDS (direct): B.08 · B.15 · B.20 · B.30 · B.46 · B.63a · B.66 · B.66a · B.73 · B.75 ·
**B.80** · `B83Kit` · landed `LocalData.lean` §6 · mathlib `PadicInt.prime_p`,
`PadicInt.residueField`, `PadicInt.pow_p_dvd_int_iff`.

**TEETH.** `W12-T-SIGMA` (`EFF.W12.27`) → **Lean theorem**; `W12-ORACLE` → **executable
regression** retained. With B.83 this node closes GC-11's two-prime obligation for all four
leaf genres.

SOURCE: `EFF.W12.29`; `blueprint/CONVENTIONS_2026-08-15.md` GC-11.

## Status

Sorry-free. **Footprint: `propext`, `Classical.choice`, `Quot.sound` plus
`Uniformity.Density.Leaf.exists_slope_factorization`.** No new axiom.
-/

set_option linter.style.longLine false
set_option maxHeartbeats 1000000

open Polynomial IsLocalRing IsDiscreteValuationRing

namespace Uniformity.Density.Leaf

private theorem hpi3 : Irreducible (3 : ℤ_[3]) := (PadicInt.prime_p (p := 3)).irreducible

private theorem hresp : IsLocalRing.residue ℤ_[3] 3 = 0 := by
  refine Ideal.Quotient.eq_zero_iff_mem.2 ?_
  rw [hpi3.maximalIdeal_eq, Ideal.mem_span_singleton]

private theorem hresmp : IsLocalRing.residue ℤ_[3] (-3) = 0 := by
  rw [map_neg, hresp, neg_zero]

private theorem hres4 : IsLocalRing.residue ℤ_[3] 4 = 1 := by
  have h : (4 : ℤ_[3]) = 1 + 3 := by norm_num
  rw [h, map_add, hresp, map_one, add_zero]

/-! ### block 1 : `φ = X`, `g = X + 2` -/

private noncomputable abbrev gA : Polynomial ℤ_[3] := X + C 3

private theorem hgAmon : gA.Monic := by unfold gA; monicity!
private theorem hgAdeg : gA.natDegree = 1 := by unfold gA; compute_degree!
private theorem hgAdegmu : gA.natDegree = 1 * (X : Polynomial ℤ_[3]).natDegree := by
  rw [hgAdeg, Polynomial.natDegree_X]

private theorem hgAc0 : gA.coeff 0 = 3 := by unfold gA; simp
private theorem hgAc1 : gA.coeff 1 = 1 := by unfold gA; simp

private theorem hgAres : gA.map (IsLocalRing.residue ℤ_[3])
    = ((X : Polynomial ℤ_[3]).map (IsLocalRing.residue ℤ_[3])) ^ 1 := by
  unfold gA; simp [hresp]

private theorem hfinA : ∀ j, j ≤ 1 →
    npHgt (X : Polynomial ℤ_[3]) gA j = ((if j = 0 then 1 else 0 : ℕ) : ℕ∞) := by
  intro j hj
  rw [npHgt_X]
  interval_cases j
  · rw [hgAc0, GateKit.padic_addVal (p := 3) (k := 1) (a := 3) (by norm_num) (by norm_num)
      (by norm_num)]
    norm_num
  · rw [hgAc1, GateKit.padic_addVal (p := 3) (k := 0) (a := 1) (by norm_num) (by norm_num)
      (by norm_num)]
    norm_num

private theorem htopA : ∀ j, 1 < j → npHgt (X : Polynomial ℤ_[3]) gA j = ⊤ := by
  intro j hj
  refine GateKit.npHgt_eq_top_of_lt Polynomial.monic_X (by rw [Polynomial.natDegree_X]; norm_num)
    gA ?_
  rw [hgAdeg, Polynomial.natDegree_X]; omega

private theorem hBA : ∀ j, j ≤ gA.natDegree → (npHgt (X : Polynomial ℤ_[3]) gA j).toNat ≤ 1 := by
  intro j hj
  rw [hgAdeg] at hj
  rw [hfinA j hj]
  by_cases h : j = 0 <;> simp [h]

private theorem hreadA : suppVal (X : Polynomial ℤ_[3]) gA 1 1 = ((1 : ℕ) : ℕ∞) ∧
    ∀ j, (j ∈ sideSet (X : Polynomial ℤ_[3]) gA 1 1 ↔
      (j ≤ 1 ∧ 1 * (if j = 0 then 1 else 0) + 1 * j = 1)) :=
  GateKit.polygon_read (n := 1) (m := 1) hgAdeg (by norm_num) hfinA htopA (by norm_num)
    (M := 1) (by intro j hj; interval_cases j <;> norm_num) ⟨0, by norm_num⟩

private theorem hsideA : sideSet (X : Polynomial ℤ_[3]) gA 1 1 = {0, 1} := by
  ext j
  rw [hreadA.2 j]
  constructor
  · rintro ⟨hj, hv⟩
    interval_cases j <;> simp
  · intro hj
    simp only [Finset.mem_insert, Finset.mem_singleton] at hj
    rcases hj with rfl | rfl <;> exact ⟨by norm_num, by norm_num⟩

private theorem hcardA : 1 < (sideSet (X : Polynomial ℤ_[3]) gA 1 1).card := by
  rw [hsideA]; decide

private theorem hsdegA : ∀ hne : (sideSet (X : Polynomial ℤ_[3]) gA 1 1).Nonempty,
    sideDeg (X : Polynomial ℤ_[3]) gA 1 1 hne = 1 := by
  intro hne
  rw [sideDeg, GateKit.sideMin_eq hne (a := 0) (by rw [hsideA]; decide)
      (by intro j hj; rw [hsideA] at hj; simp only [Finset.mem_insert,
        Finset.mem_singleton] at hj; omega),
    GateKit.sideMax_eq' hne (b := 1) (by rw [hsideA]; decide)
      (by intro j hj; rw [hsideA] at hj; simp only [Finset.mem_insert,
        Finset.mem_singleton] at hj; omega)]

private theorem hslopeA : ∀ u ℓ : ℕ, 0 < ℓ → Nat.Coprime u ℓ →
    1 < (sideSet (X : Polynomial ℤ_[3]) gA u ℓ).card → u = 1 ∧ ℓ = 1 := by
  intro u ℓ hℓ hcop hcard
  obtain ⟨hℓle, hule⟩ :=
    GateKit.slope_bounds_of_le GateKit.isKey_X hgAmon hgAdegmu hℓ hcop hcard hBA
  rw [hgAdeg] at hℓle
  interval_cases ℓ
  interval_cases u
  · exfalso
    have hread := GateKit.polygon_read (n := 1) (m := 1) hgAdeg (by norm_num) hfinA htopA
      (u := 0) (ℓ := 1) (by norm_num) (M := 0) (by intro j hj; exact Nat.zero_le _)
      ⟨1, by norm_num⟩
    have huniq : ∀ j ∈ sideSet (X : Polynomial ℤ_[3]) gA 0 1, j = 1 := by
      intro j hj
      obtain ⟨hjm, hval⟩ := (hread.2 j).1 hj
      interval_cases j <;> revert hval <;> decide
    have : (sideSet (X : Polynomial ℤ_[3]) gA 0 1).card ≤ 1 :=
      Finset.card_le_one.2 fun a ha b hb => by rw [huniq a ha, huniq b hb]
    omega
  · exact ⟨rfl, rfl⟩

private theorem hslopeFinsetA : slopeFinset (3 : ℤ_[3]) (X : Polynomial ℤ_[3]) gA = {(1, 1)} := by
  ext p
  rw [mem_slopeFinset GateKit.isKey_X hgAmon hgAdegmu]
  constructor
  · rintro ⟨hℓ, hcop, hcard⟩
    obtain ⟨hu, hl⟩ := hslopeA p.1 p.2 hℓ hcop hcard
    simp only [Finset.mem_singleton, Prod.ext_iff]
    exact ⟨hu, hl⟩
  · intro hp
    simp only [Finset.mem_singleton] at hp
    subst hp
    exact ⟨by norm_num, by norm_num, hcardA⟩

private theorem hordA : order1Type (3 : ℤ_[3]) (X : Polynomial ℤ_[3]) gA = ⟨{(1, 1)}⟩ := by
  have h := GateKit.order1Type_of_sideDeg_one hpi3 GateKit.isKey_X hgAmon hgAdegmu (by
    intro p hp hne
    rw [hslopeFinsetA, Finset.mem_singleton] at hp
    subst hp
    exact hsdegA hne)
  rw [hslopeFinsetA, Polynomial.natDegree_X] at h
  rw [h]
  rfl

private theorem htermA : ¬ NeedsDescent (3 : ℤ_[3]) (X : Polynomial ℤ_[3]) gA := by
  refine GateKit.not_needsDescent_of_sideDeg_one hpi3 GateKit.isKey_X hgAmon hgAdegmu ?_
  intro u ℓ hℓ hcop hcard hne
  obtain ⟨hu, hl⟩ := hslopeA u ℓ hℓ hcop hcard
  subst hu; subst hl
  exact hsdegA hne

private theorem hvisA : Visible (3 : ℤ_[3]) (X : Polynomial ℤ_[3]) gA 2 := by
  refine ⟨0, ?_⟩
  rw [dev_X, Polynomial.coeff_C_zero, hgAc0]
  exact GateKit.padic_not_dvd (p := 3) (a := 3) (by norm_num) (by norm_num)

/-! ### block 2 : `φ = X² + X + 3`, `g = X² + X + 1` -/

private noncomputable abbrev kB : Polynomial ℤ_[3] := X ^ 2 + C 4
private noncomputable abbrev gB : Polynomial ℤ_[3] := X ^ 2 + 1

private theorem hkBmon : kB.Monic := by unfold kB; monicity!
private theorem hkBdeg : kB.natDegree = 2 := by unfold kB; compute_degree!
private theorem hkBdegW : kB.degree = 2 := by
  rw [Polynomial.degree_eq_natDegree hkBmon.ne_zero, hkBdeg]; rfl

private theorem hgBmon : gB.Monic := by unfold gB; monicity!
private theorem hgBdeg : gB.natDegree = 2 := by unfold gB; compute_degree!
private theorem hgBdegmu : gB.natDegree = 1 * kB.natDegree := by rw [hgBdeg, hkBdeg]

private theorem hkBmapres : kB.map (IsLocalRing.residue ℤ_[3])
    = X ^ 2 + 1 := by
  unfold kB
  simp [hres4]

private theorem hkBirr : Irreducible (kB.map (IsLocalRing.residue ℤ_[3])) := by
  set e := PadicInt.residueField (p := 3) with he
  have hmap : (kB.map (IsLocalRing.residue ℤ_[3])).map (e : ResidueField ℤ_[3] →+* ZMod 3)
      = X ^ 2 + 1 := by
    rw [hkBmapres]; simp
  refine Polynomial.irreducible_of_degree_le_three_of_not_isRoot ?_ ?_
  · rw [hkBmon.natDegree_map, hkBdeg]; decide
  · intro x hx
    have h1 : ((kB.map (IsLocalRing.residue ℤ_[3])).map
        (e : ResidueField ℤ_[3] →+* ZMod 3)).eval (e x)
        = e ((kB.map (IsLocalRing.residue ℤ_[3])).eval x) := by
      rw [Polynomial.eval_map]
      exact Polynomial.eval₂_hom (e : ResidueField ℤ_[3] →+* ZMod 3) x
    rw [hmap, hx] at h1
    simp only [Polynomial.eval_add, Polynomial.eval_pow, Polynomial.eval_X,
      Polynomial.eval_one, map_zero] at h1
    revert h1
    generalize (e x) = y
    revert y
    decide

private theorem hkeyB : IsKey kB := ⟨hkBmon, by rw [hkBdeg]; norm_num, hkBirr⟩

private theorem hgBeq : gB = C (-3) + 1 * kB := by
  unfold gB kB
  have h4 : (C (4 : ℤ_[3]) : Polynomial ℤ_[3]) = C 3 + 1 := by
    rw [← Polynomial.C_1, ← Polynomial.C_add]; norm_num
  have h3 : (C (-3 : ℤ_[3]) : Polynomial ℤ_[3]) = - C 3 := by rw [← Polynomial.C_neg]
  rw [h4, h3]
  ring

private theorem hgBeq' : gB = C (-3) + kB := by rw [hgBeq, one_mul]

private theorem hgBres : gB.map (IsLocalRing.residue ℤ_[3])
    = (kB.map (IsLocalRing.residue ℤ_[3])) ^ 1 := by
  rw [pow_one, hgBeq', Polynomial.map_add, Polynomial.map_C, hresmp, Polynomial.C_0, zero_add]

private theorem hdevB : dev kB gB 0 = C (-3) ∧ dev kB gB 1 = 1 :=
  GateKit.dev_two hkBmon (by rw [hkBdeg]; norm_num)
    (lt_of_le_of_lt Polynomial.degree_C_le (by rw [hkBdegW]; decide))
    (by rw [Polynomial.degree_one, hkBdegW]; decide) hgBeq

private theorem hfinB : ∀ j, j ≤ 1 → npHgt kB gB j = ((if j = 0 then 1 else 0 : ℕ) : ℕ∞) := by
  intro j hj
  interval_cases j
  · rw [npHgt, hdevB.1, GateKit.gaussVal_C,
      GateKit.padic_addVal (p := 3) (k := 1) (a := -3) (by norm_num) (by norm_num) (by norm_num)]
    norm_num
  · rw [npHgt, hdevB.2, show (1 : Polynomial ℤ_[3]) = C 1 from (Polynomial.C_1).symm,
      GateKit.gaussVal_C, GateKit.addVal_one hpi3]
    norm_num

private theorem htopB : ∀ j, 1 < j → npHgt kB gB j = ⊤ := by
  intro j hj
  refine GateKit.npHgt_eq_top_of_lt hkBmon (by rw [hkBdeg]; norm_num) gB ?_
  rw [hgBdeg, hkBdeg]; omega

private theorem hBB : ∀ j, j ≤ gB.natDegree → (npHgt kB gB j).toNat ≤ 1 := by
  intro j hj
  by_cases h : j ≤ 1
  · rw [hfinB j h]
    by_cases h0 : j = 0 <;> simp [h0]
  · rw [htopB j (by omega)]; decide

private theorem hreadB : suppVal kB gB 1 1 = ((1 : ℕ) : ℕ∞) ∧
    ∀ j, (j ∈ sideSet kB gB 1 1 ↔ (j ≤ 1 ∧ 1 * (if j = 0 then 1 else 0) + 1 * j = 1)) :=
  GateKit.polygon_read (n := 2) (m := 1) hgBdeg (by norm_num) hfinB htopB (by norm_num)
    (M := 1) (by intro j hj; interval_cases j <;> norm_num) ⟨0, by norm_num⟩

private theorem hsideB : sideSet kB gB 1 1 = {0, 1} := by
  ext j
  rw [hreadB.2 j]
  constructor
  · rintro ⟨hj, hv⟩
    interval_cases j <;> simp
  · intro hj
    simp only [Finset.mem_insert, Finset.mem_singleton] at hj
    rcases hj with rfl | rfl <;> exact ⟨by norm_num, by norm_num⟩

private theorem hcardB : 1 < (sideSet kB gB 1 1).card := by rw [hsideB]; decide

private theorem hsdegB : ∀ hne : (sideSet kB gB 1 1).Nonempty, sideDeg kB gB 1 1 hne = 1 := by
  intro hne
  rw [sideDeg, GateKit.sideMin_eq hne (a := 0) (by rw [hsideB]; decide)
      (by intro j hj; rw [hsideB] at hj; simp only [Finset.mem_insert,
        Finset.mem_singleton] at hj; omega),
    GateKit.sideMax_eq' hne (b := 1) (by rw [hsideB]; decide)
      (by intro j hj; rw [hsideB] at hj; simp only [Finset.mem_insert,
        Finset.mem_singleton] at hj; omega)]

private theorem hslopeB : ∀ u ℓ : ℕ, 0 < ℓ → Nat.Coprime u ℓ →
    1 < (sideSet kB gB u ℓ).card → u = 1 ∧ ℓ = 1 := by
  intro u ℓ hℓ hcop hcard
  obtain ⟨hℓle, hule⟩ := GateKit.slope_bounds_of_le hkeyB hgBmon hgBdegmu hℓ hcop hcard hBB
  rw [hgBdeg] at hℓle
  have kill : ∀ (u ℓ M j₀ : ℕ), 0 < ℓ →
      (∀ j, j ≤ 1 → M ≤ ℓ * (if j = 0 then 1 else 0) + u * j) →
      (∃ j, j ≤ 1 ∧ ℓ * (if j = 0 then 1 else 0) + u * j = M) →
      (∀ j, j ≤ 1 → ℓ * (if j = 0 then 1 else 0) + u * j = M → j = j₀) →
      (sideSet kB gB u ℓ).card ≤ 1 := by
    intro u ℓ M j₀ hl hle hmem huniq
    have hread := GateKit.polygon_read (n := 2) (m := 1) hgBdeg (by norm_num) hfinB htopB
      hl (M := M) hle hmem
    exact Finset.card_le_one.2 fun a ha b hb => by
      obtain ⟨ha1, ha2⟩ := (hread.2 a).1 ha
      obtain ⟨hb1, hb2⟩ := (hread.2 b).1 hb
      rw [huniq a ha1 ha2, huniq b hb1 hb2]
  interval_cases ℓ
  · interval_cases u
    · exfalso
      have hle1 := kill 0 1 0 1 (by norm_num) (by intro j hj; exact Nat.zero_le _)
        ⟨1, by norm_num⟩ (by intro j hj hv; interval_cases j <;> revert hv <;> decide)
      omega
    · exact ⟨rfl, rfl⟩
  · interval_cases u
    · exact absurd hcop (by decide)
    · exfalso
      have hle1 := kill 1 2 1 1 (by norm_num)
        (by intro j hj; interval_cases j <;> norm_num) ⟨1, by norm_num⟩
        (by intro j hj hv; interval_cases j <;> revert hv <;> decide)
      omega

private theorem hslopeFinsetB : slopeFinset (3 : ℤ_[3]) kB gB = {(1, 1)} := by
  ext p
  rw [mem_slopeFinset hkeyB hgBmon hgBdegmu]
  constructor
  · rintro ⟨hℓ, hcop, hcard⟩
    obtain ⟨hu, hl⟩ := hslopeB p.1 p.2 hℓ hcop hcard
    simp only [Finset.mem_singleton, Prod.ext_iff]
    exact ⟨hu, hl⟩
  · intro hp
    simp only [Finset.mem_singleton] at hp
    subst hp
    exact ⟨by norm_num, by norm_num, hcardB⟩

private theorem hordB : order1Type (3 : ℤ_[3]) kB gB = ⟨{(1, 2)}⟩ := by
  have h := GateKit.order1Type_of_sideDeg_one hpi3 hkeyB hgBmon hgBdegmu (by
    intro p hp hne
    rw [hslopeFinsetB, Finset.mem_singleton] at hp
    subst hp
    exact hsdegB hne)
  rw [hslopeFinsetB, hkBdeg] at h
  rw [h]
  rfl

private theorem htermB : ¬ NeedsDescent (3 : ℤ_[3]) kB gB := by
  refine GateKit.not_needsDescent_of_sideDeg_one hpi3 hkeyB hgBmon hgBdegmu ?_
  intro u ℓ hℓ hcop hcard hne
  obtain ⟨hu, hl⟩ := hslopeB u ℓ hℓ hcop hcard
  subst hu; subst hl
  exact hsdegB hne

private theorem hvisB : Visible (3 : ℤ_[3]) kB gB 2 := by
  refine ⟨0, ?_⟩
  rw [hdevB.1, Polynomial.coeff_C_zero]
  exact GateKit.padic_not_dvd (p := 3) (a := -3) (by norm_num) (by norm_num)

/-! ### the two-block assembly -/

private noncomputable abbrev aIV : Fin 3 → ℤ_[3] := ![3, 1, 3]
private noncomputable abbrev phiIV : Fin 2 → Polynomial ℤ_[3] := ![X, kB]
private noncomputable abbrev gfIV : Fin 2 → Polynomial ℤ_[3] := ![gA, gB]
private noncomputable abbrev eIV : Fin 2 → ℕ := ![1, 1]

private theorem hfnormIV : Uniformity.Density.monicPoly aIV
    = X ^ 3 + C 3 * X ^ 2 + X + C 3 := by
  simp [Uniformity.Density.monicPoly, aIV, Fin.sum_univ_three]
  ring

private theorem hgprodIV : Uniformity.Density.monicPoly aIV = ∏ i : Fin 2, gfIV i := by
  rw [Fin.prod_univ_two, hfnormIV]
  show _ = gA * gB
  unfold gA gB
  ring

/-! ### the two blocks' perimeter closures, and the distinctness of the two keys -/

private theorem hne01 : (X : Polynomial ℤ_[3]).map (IsLocalRing.residue ℤ_[3])
    ≠ kB.map (IsLocalRing.residue ℤ_[3]) := by
  intro h
  have hdX : ((X : Polynomial ℤ_[3]).map (IsLocalRing.residue ℤ_[3])).natDegree = 1 := by
    rw [Polynomial.monic_X.natDegree_map, Polynomial.natDegree_X]
  have hdB : (kB.map (IsLocalRing.residue ℤ_[3])).natDegree = 2 := by
    rw [hkBmon.natDegree_map, hkBdeg]
  rw [h, hdB] at hdX
  omega

private theorem hperim0 : ∀ gT : Polynomial ℤ_[3], gT.Monic →
    gT.natDegree = gA.natDegree →
    (∀ k, (3 : ℤ_[3]) ^ 2 ∣ (gA - gT).coeff k) →
    ∀ u ℓ : ℕ, 0 < ℓ → Nat.Coprime u ℓ →
    ∀ gS : Polynomial ℤ_[3], gS.Monic → gS ∣ gT → IsPure (X : Polynomial ℤ_[3]) gS u ℓ →
    ∀ hne' : (sideSet (X : Polynomial ℤ_[3]) gS u ℓ).Nonempty, ∀ H₀ : ℕ,
      npHgt (X : Polynomial ℤ_[3]) gS (sideMin (X : Polynomial ℤ_[3]) gS u ℓ hne') = (H₀ : ℕ∞) →
      ∀ ψ : Polynomial (resField (X : Polynomial ℤ_[3])), ψ.Monic → Irreducible ψ →
        (∃ c : (resField (X : Polynomial ℤ_[3]))ˣ,
          resPoly (3 : ℤ_[3]) (X : Polynomial ℤ_[3]) gS u ℓ hne' H₀ = c • ψ) →
        ((ℓ = 1 ∧ (X : Polynomial ℤ_[3]).natDegree = 1) ∨ ψ.natDegree = 1 ∨
          ∀ g'' ∈ monicFactors gS,
            (X : Polynomial ℤ_[3]).natDegree * ψ.natDegree ∣ inertiaDegOf g'') := by
  intro gT hgTm hdegT hcongT u ℓ hℓ hcop gS hgSm hdvd hpure hne' H₀ hH₀ ψ hψm hψi hc
  refine Or.inr (Or.inl ?_)
  letI : Field (resField (X : Polynomial ℤ_[3])) := instFieldResField GateKit.isKey_X
  have hbound := GateKit.perim_degree_bound hpi3 GateKit.isKey_X (N := 2) (by norm_num)
    hgAres hgTm hdegT hcongT hℓ hcop hgSm hdvd hpure hne' hH₀ hc
  rw [Polynomial.natDegree_X, hgAdeg] at hbound
  have h1 := GateKit.one_le_natDegree_of_monic_irreducible hψm hψi
  have h2 : 1 * 1 * ψ.natDegree ≤ ℓ * 1 * ψ.natDegree :=
    Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hℓ)
  omega

private theorem hperim1 : ∀ gT : Polynomial ℤ_[3], gT.Monic →
    gT.natDegree = gB.natDegree →
    (∀ k, (3 : ℤ_[3]) ^ 2 ∣ (gB - gT).coeff k) →
    ∀ u ℓ : ℕ, 0 < ℓ → Nat.Coprime u ℓ →
    ∀ gS : Polynomial ℤ_[3], gS.Monic → gS ∣ gT → IsPure kB gS u ℓ →
    ∀ hne' : (sideSet kB gS u ℓ).Nonempty, ∀ H₀ : ℕ,
      npHgt kB gS (sideMin kB gS u ℓ hne') = (H₀ : ℕ∞) →
      ∀ ψ : Polynomial (resField kB), ψ.Monic → Irreducible ψ →
        (∃ c : (resField kB)ˣ, resPoly (3 : ℤ_[3]) kB gS u ℓ hne' H₀ = c • ψ) →
        ((ℓ = 1 ∧ kB.natDegree = 1) ∨ ψ.natDegree = 1 ∨
          ∀ g'' ∈ monicFactors gS, kB.natDegree * ψ.natDegree ∣ inertiaDegOf g'') := by
  intro gT hgTm hdegT hcongT u ℓ hℓ hcop gS hgSm hdvd hpure hne' H₀ hH₀ ψ hψm hψi hc
  refine Or.inr (Or.inl ?_)
  letI : Field (resField kB) := instFieldResField hkeyB
  have hbound := GateKit.perim_degree_bound hpi3 hkeyB (N := 2) (by norm_num)
    hgBres hgTm hdegT hcongT hℓ hcop hgSm hdvd hpure hne' hH₀ hc
  rw [hkBdeg, hgBdeg] at hbound
  have h1 := GateKit.one_le_natDegree_of_monic_irreducible hψm hψi
  have h2 : 1 * 2 * ψ.natDegree ≤ ℓ * 2 * ψ.natDegree :=
    Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hℓ)
  omega

/-- **B.83 (iv) — the `q = 2` split gate.** The level-2 class of `![2, 3, 3]` over `ℤ_[3]` is
decided at `⟨{(1,1),(1,2)}⟩`: a linear factor and an unramified quadratic. Two order-0 blocks,
fired through B.80; the second key is a *lift* `X² + X + 3 ≠ X² + X + 1`, which is what makes
its block `Visible`. -/
theorem gate_split_three :
    Uniformity.Density.DecidedAt ℤ_[3] 3 ⟨{(1, 1), (1, 2)}⟩ 2
      (Uniformity.Density.proj ℤ_[3] 3 2 ![3, 1, 3]) := by
  have h := decidedAt_of_order1_certificate (O := ℤ_[3]) (π := (3 : ℤ_[3])) hpi3 (n := 3)
    (N := 2) (by norm_num) aIV (ι := Fin 2) (s := Finset.univ) (φ := phiIV) (e := eIV)
    (fun i _ => by fin_cases i; exacts [GateKit.isKey_X, hkeyB])
    (fun i _ => by fin_cases i <;> norm_num)
    (by
      intro i _ j _ hij
      fin_cases i <;> fin_cases j
      · exact absurd rfl hij
      · exact hne01
      · exact hne01.symm
      · exact absurd rfl hij)
    (g := gfIV)
    (fun i _ => by fin_cases i; exacts [hgAmon, hgBmon])
    hgprodIV
    (fun i _ => by fin_cases i; exacts [hgAres, hgBres])
    (fun i _ => by fin_cases i; exacts [hvisA, hvisB])
    (fun i _ => by fin_cases i; exacts [htermA, htermB])
    (fun i _ => by fin_cases i; exacts [hperim0, hperim1])
  have hsum : ∑ i : Fin 2, (order1Type (3 : ℤ_[3]) (phiIV i) (gfIV i)).data
      = {(1, 1), (1, 2)} := by
    rw [Fin.sum_univ_two]
    show (order1Type (3 : ℤ_[3]) (X : Polynomial ℤ_[3]) gA).data
      + (order1Type (3 : ℤ_[3]) kB gB).data = _
    rw [hordA, hordB]
    rfl
  rwa [hsum] at h

end Uniformity.Density.Leaf

/-! ## Axiom footprint -/

section AxCheck
#print axioms Uniformity.Density.Leaf.gate_split_three
end AxCheck
