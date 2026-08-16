/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapB.B05
import Uniformity.ChapB.B12
import Uniformity.ChapB.B13b
import Uniformity.ChapB.B17
import Uniformity.ChapB.B20
import Uniformity.ChapB.B32b
import Uniformity.ChapB.B34
import Uniformity.ChapB.B35a

/-!
# Uniformity.ChapB.B35b — the carry does not reach the minimal weight

**Chapter B, NODE B.35, part (b) of the mandated 4-way split**
(`blueprint/CHAP-B_leaf_layer.md` §5), ENV-A′. The delicate step: the blueprint's PROOF step 3,
i.e. the statement that the `φ`-carry of the convolution lands at *strictly* larger weight than the
digit that is being read, so the product's development digit is the uncarried convolution digit.
`hu : 0 < u` is exactly what makes that strict — the second counterexample of amendment A-F.6
(`f = g = X² + X + 1` at `u = 0` over `ℤ₃`, `φ = X² + 1`) is the failure at `u = 0`.

## The landed route

The blueprint reads the product's development coefficient at abscissa `t` as "the convolution
`c t = Σ_{j+i=t} dev φ f j · dev φ g i` **after carrying**" and then estimates the carry
`(c (t−1)) /ₘ φ`. The route below never forms `c` and never carries: it expands
`f · g = Σ_{j,i} (dev φ f j · dev φ g i) · φ^(j+i)` (B.05 twice), and applies the **height-`K`
residual reduction** `resMk π φ K` (B35a's graded ring laws) to that sum term by term. Each term
`x · φ^t` has development `x %ₘ φ` at abscissa `t`, `x /ₘ φ` at `t + 1` and `0` elsewhere
(B35a's `dev_mul_pow`), and B35a's `resMk_modByMonic` erases the `%ₘ φ`, so the *only* thing to
check is which terms survive the height:

* purity of `f` and `g` gives, in `ℕ`, `u·ℓ·d_f ≤ ℓ·H_j + u·j` and `u·ℓ·d_g ≤ ℓ·H_i + u·i`
  (`le_weight_of_pure`); adding and dividing by `ℓ` gives
  `u·(d_f + d_g) ≤ (H_j + H_i) + u·k` whenever `j + i ≤ ℓ·k`, i.e. the term's Gauss valuation is
  at least the read height `K₀ = u·(d_f+d_g) − u·k` (`le_gaussVal_dev_mul`);
* the inequality is **strict** — so the digit at `K₀` vanishes — as soon as either `j + i < ℓ·k`
  (this is the carry: `0 < u` is what turns `u·(j+i) < u·ℓ·k` into a strict weight gap) or
  `j + i = ℓ·k` with `ℓ ∤ j` (an off-side abscissa: on a `(u,ℓ)`-side in lowest terms every
  on-side abscissa is `≡ 0 mod ℓ` by B.17, and `0` is on-side by purity)
  (`lt_gaussVal_dev_mul`).

What is left is a bookkeeping identity: the surviving terms are exactly the pairs
`(ℓ·k₁, ℓ·k₂)` with `k₁ + k₂ = k`, and on those `resMk` is multiplicative with the heights adding
(B35a's `resMk_mul`). That is `resMk_dev_mul`, the file's contract for B35c/B35d:

```
resMk π φ (u·(d_f+d_g) − u·k) (dev φ (f*g) (ℓ·k))
  = Σ_{k₁ ≤ k} resMk π φ (u·d_f − u·k₁) (dev φ f (ℓ·k₁))
              · resMk π φ (u·d_g − u·(k−k₁)) (dev φ g (ℓ·(k−k₁)))
```

The first half of the file is the **normal form of a full-degree pure polynomial**, which is what
makes the heights above computable: for monic `f` of degree `n·m` that is `(u,ℓ)`-pure,
`suppVal φ f u ℓ = u·n`, `sideMin = 0`, `sideMax = n` and `ℓ·sideDeg = n` — so the side's left
height satisfies `ℓ·H₀ = u·n = u·ℓ·d`, i.e. `H₀ = u·d`, and the line height at position `k` is
`u·(d − k)`. (This is also where the A-F.6 divisibility hypotheses `hfd`/`hgd` do their work: they
are what make `f.natDegree / φ.natDegree` exact, so that `IsPure`'s right endpoint really is the
polygon's terminal point `(n, 0)`.)

DEPENDS: B.05 (`sum_dev_eq`) · B.12 (`npHgt_eq_top_iff`) · B.13 (`npHgt_top`) ·
B.17 (`npHgt_ne_top_of_onSide`, `onSide_modEq`) · B.18 (`sideSet_nonempty` at the call sites) ·
B.20 (`sideMin`, `sideMax`, `sideDeg`, `sideMax_eq`, `onSide_of_mem_sideSet`) ·
B.32 (b) (`suppVal_eq_inf_range`) · B.34 (`IsPure`) · B35a (the digit calculus).

## Status

Sorry-free, axiom-free (Lean core only).
-/

namespace Uniformity.Density.Leaf

open Polynomial

-- ENV-A′ (blueprint §0.1): the polynomial arena, plus `hπ : Irreducible π` carried per signature.
variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {π : O}

/-! ### The normal form of a full-degree pure polynomial -/

/-- The cleared support value is a lower bound for the weight at *every* abscissa, not only the
ones inside `suppVal`'s own range. -/
theorem suppVal_le_weight {φ : Polynomial O} (hφ : φ.Monic) (hd : 0 < φ.natDegree) {ℓ : ℕ}
    (hℓ : 0 < ℓ) (u : ℕ) (f : Polynomial O) (j : ℕ) :
    suppVal φ f u ℓ ≤ ℓ • npHgt φ f j + ((u * j : ℕ) : ℕ∞) := by
  have hlt : f.natDegree < max (f.natDegree + 1) (j + 1) :=
    lt_of_lt_of_le (Nat.lt_succ_self _) (le_max_left _ _)
  rw [suppVal_eq_inf_range hφ hd hℓ u f hlt]
  exact Finset.inf_le
    (Finset.mem_range.2 (lt_of_lt_of_le (Nat.lt_succ_self j) (le_max_right _ _)))

/-- **The support value of a full-degree pure polynomial.** For monic `f` of degree `n · m` that is
`(u,ℓ)`-pure, `suppVal φ f u ℓ = u · n`: the polygon's terminal point `(n, 0)` is on the side. -/
theorem suppVal_of_pure {φ : Polynomial O} (hφ : φ.Monic) (hd : 0 < φ.natDegree)
    {f : Polynomial O} (hf : f.Monic) {n : ℕ} (hdeg : f.natDegree = n * φ.natDegree) {u ℓ : ℕ}
    (hpure : IsPure φ f u ℓ) : suppVal φ f u ℓ = ((u * n : ℕ) : ℕ∞) := by
  have hn : f.natDegree / φ.natDegree = n := by rw [hdeg]; exact Nat.mul_div_cancel _ hd
  have h2 : ℓ • npHgt φ f n + ((u * n : ℕ) : ℕ∞) = suppVal φ f u ℓ := by
    have := hpure.2
    rwa [hn] at this
  rw [npHgt_top hφ hd hf hdeg] at h2
  simpa using h2.symm

/-- The left endpoint of a pure polygon is the abscissa `0`. -/
theorem sideMin_of_pure {φ f : Polynomial O} {u ℓ : ℕ} (hpure : IsPure φ f u ℓ)
    (h : (sideSet φ f u ℓ).Nonempty) : sideMin φ f u ℓ h = 0 := by
  classical
  have h0 : (0 : ℕ) ∈ sideSet φ f u ℓ := by
    have : (0 : ℕ) ∈ Finset.filter (OnSide φ f u ℓ) (Finset.range (f.natDegree + 1)) :=
      Finset.mem_filter.2 ⟨Finset.mem_range.2 (Nat.succ_pos _), hpure.1⟩
    exact this
  exact Nat.le_zero.1 (Finset.min'_le _ _ h0)

/-- The right endpoint of a full-degree pure polygon is the abscissa `n`. -/
theorem sideMax_of_pure {φ : Polynomial O} (hφ : φ.Monic)
    (hd : 0 < φ.natDegree) {f : Polynomial O} (hf : f.Monic) {n : ℕ}
    (hdeg : f.natDegree = n * φ.natDegree) {u ℓ : ℕ} (hℓ : 0 < ℓ) (hpure : IsPure φ f u ℓ)
    (h : (sideSet φ f u ℓ).Nonempty) : sideMax φ f u ℓ h = n := by
  classical
  have htop : suppVal φ f u ℓ ≠ ⊤ := by
    rw [suppVal_of_pure hφ hd hf hdeg hpure]; exact ENat.coe_ne_top _
  have hn : f.natDegree / φ.natDegree = n := by rw [hdeg]; exact Nat.mul_div_cancel _ hd
  have hnmem : n ∈ sideSet φ f u ℓ := by
    have honside : OnSide φ f u ℓ n := by have := hpure.2; rwa [hn] at this
    have : n ∈ Finset.filter (OnSide φ f u ℓ) (Finset.range (f.natDegree + 1)) :=
      Finset.mem_filter.2
        ⟨Finset.mem_range.2 (by rw [hdeg]; exact Nat.lt_succ_of_le (Nat.le_mul_of_pos_right n hd)),
          honside⟩
    exact this
  refine le_antisymm (Finset.max'_le _ _ _ fun j hj => ?_) (Finset.le_max' _ _ hnmem)
  -- every on-side abscissa carries a nonzero development coefficient, hence sits at `≤ n`
  have hjT : npHgt φ f j ≠ ⊤ :=
    npHgt_ne_top_of_onSide hℓ htop (onSide_of_mem_sideSet hj)
  have hdevne : dev φ f j ≠ 0 := fun hz => hjT (npHgt_eq_top_iff.2 hz)
  rcases Nat.lt_or_ge n j with hlt | hge
  · exact absurd (dev_eq_zero_of_lt hφ hd f j (by
      rw [hdeg]; exact mul_lt_mul_of_pos_right hlt hd)) hdevne
  · exact hge

/-- The side of a full-degree pure polygon has length `n`: `ℓ · sideDeg = n`. -/
theorem sideDeg_of_pure {φ : Polynomial O} (hφ : φ.Monic)
    (hd : 0 < φ.natDegree) {f : Polynomial O} (hf : f.Monic) {n : ℕ}
    (hdeg : f.natDegree = n * φ.natDegree) {u ℓ : ℕ} (hℓ : 0 < ℓ) (hcop : Nat.Coprime u ℓ)
    (hpure : IsPure φ f u ℓ) (h : (sideSet φ f u ℓ).Nonempty) :
    ℓ * sideDeg φ f u ℓ h = n := by
  have htop : suppVal φ f u ℓ ≠ ⊤ := by
    rw [suppVal_of_pure hφ hd hf hdeg hpure]; exact ENat.coe_ne_top _
  have hmax := sideMax_eq hℓ hcop htop h
  rw [sideMin_of_pure hpure h, Nat.zero_add,
    sideMax_of_pure hφ hd hf hdeg hℓ hpure h] at hmax
  exact hmax.symm

/-- **`ℓ`-spacing on a pure polygon.** Every on-side abscissa of a `(u,ℓ)`-pure polynomial is a
multiple of `ℓ`, because `0` is on-side (purity) and B.17 makes any two on-side abscissae congruent
mod `ℓ`. -/
theorem dvd_of_onSide_of_pure {φ : Polynomial O} (hφ : φ.Monic) (hd : 0 < φ.natDegree)
    {f : Polynomial O} (hf : f.Monic) {n : ℕ} (hdeg : f.natDegree = n * φ.natDegree) {u ℓ : ℕ}
    (hℓ : 0 < ℓ) (hcop : Nat.Coprime u ℓ) (hpure : IsPure φ f u ℓ) {j : ℕ}
    (hj : OnSide φ f u ℓ j) : ℓ ∣ j := by
  have htop : suppVal φ f u ℓ ≠ ⊤ := by
    rw [suppVal_of_pure hφ hd hf hdeg hpure]; exact ENat.coe_ne_top _
  exact (Nat.modEq_zero_iff_dvd).1 (onSide_modEq hℓ hcop htop hj hpure.1)

/-- **The purity bound, in `ℕ`.** At every abscissa `j` of finite height `H`, the weight
`ℓ·H + u·j` is at least the side's value `u·n`. -/
theorem le_weight_of_pure {φ : Polynomial O} (hφ : φ.Monic) (hd : 0 < φ.natDegree)
    {f : Polynomial O} (hf : f.Monic) {n : ℕ} (hdeg : f.natDegree = n * φ.natDegree) {u ℓ : ℕ}
    (hℓ : 0 < ℓ) (hpure : IsPure φ f u ℓ) {j H : ℕ} (hH : npHgt φ f j = (H : ℕ∞)) :
    u * n ≤ ℓ * H + u * j := by
  have h := suppVal_le_weight hφ hd hℓ u f j
  rw [suppVal_of_pure hφ hd hf hdeg hpure, hH] at h
  have hcast : ℓ • ((H : ℕ) : ℕ∞) + ((u * j : ℕ) : ℕ∞) = ((ℓ * H + u * j : ℕ) : ℕ∞) := by
    push_cast
    simp [nsmul_eq_mul]
  rw [hcast] at h
  exact_mod_cast h

/-- **The purity bound is strict off the side.** -/
theorem lt_weight_of_pure {φ : Polynomial O} (hφ : φ.Monic) (hd : 0 < φ.natDegree)
    {f : Polynomial O} (hf : f.Monic) {n : ℕ} (hdeg : f.natDegree = n * φ.natDegree) {u ℓ : ℕ}
    (hℓ : 0 < ℓ) (hpure : IsPure φ f u ℓ) {j H : ℕ} (hH : npHgt φ f j = (H : ℕ∞))
    (hns : ¬ OnSide φ f u ℓ j) : u * n < ℓ * H + u * j := by
  have hle := le_weight_of_pure hφ hd hf hdeg hℓ hpure hH
  rcases Nat.lt_or_ge (u * n) (ℓ * H + u * j) with h | h
  · exact h
  · exfalso
    refine hns ?_
    have heq : ℓ * H + u * j = u * n := le_antisymm h hle
    show ℓ • npHgt φ f j + ((u * j : ℕ) : ℕ∞) = suppVal φ f u ℓ
    rw [suppVal_of_pure hφ hd hf hdeg hpure, hH]
    have hcast : ℓ • ((H : ℕ) : ℕ∞) + ((u * j : ℕ) : ℕ∞) = ((ℓ * H + u * j : ℕ) : ℕ∞) := by
      push_cast
      simp [nsmul_eq_mul]
    rw [hcast, heq]

/-! ### The two weight estimates for a convolution term -/

section Estimates

variable {φ : Polynomial O} {u ℓ : ℕ} {f g : Polynomial O} {df dg : ℕ}

/-- **The convolution term carries enough valuation.** If `j + i ≤ ℓ·k` then the Gauss valuation of
`dev φ f j · dev φ g i` is at least the read height `u·(d_f+d_g) − u·k`. -/
theorem le_gaussVal_dev_mul (hπ : Irreducible π) (hφ : φ.Monic) (hd : 0 < φ.natDegree)
    (hf : f.Monic) (hg : g.Monic) (hfdeg : f.natDegree = ℓ * df * φ.natDegree)
    (hgdeg : g.natDegree = ℓ * dg * φ.natDegree) (hℓ : 0 < ℓ) (hfp : IsPure φ f u ℓ)
    (hgp : IsPure φ g u ℓ) {k j i : ℕ} (hji : j + i ≤ ℓ * k) :
    ((u * (df + dg) - u * k : ℕ) : ℕ∞) ≤ gaussVal (dev φ f j * dev φ g i) := by
  rcases eq_or_ne (gaussVal (dev φ f j)) ⊤ with hfT | hfT
  · rw [gaussVal_eq_top_iff.1 hfT, zero_mul, gaussVal_eq_top_iff.2 rfl]; exact le_top
  rcases eq_or_ne (gaussVal (dev φ g i)) ⊤ with hgT | hgT
  · rw [gaussVal_eq_top_iff.1 hgT, mul_zero, gaussVal_eq_top_iff.2 rfl]; exact le_top
  obtain ⟨Hj, hHj⟩ := ENat.ne_top_iff_exists.1 hfT
  obtain ⟨Hi, hHi⟩ := ENat.ne_top_iff_exists.1 hgT
  have h1 : u * (ℓ * df) ≤ ℓ * Hj + u * j :=
    le_weight_of_pure hφ hd hf hfdeg hℓ hfp (j := j) (H := Hj) hHj.symm
  have h2 : u * (ℓ * dg) ≤ ℓ * Hi + u * i :=
    le_weight_of_pure hφ hd hg hgdeg hℓ hgp (j := i) (H := Hi) hHi.symm
  have hcalc : ℓ * (u * (df + dg)) ≤ ℓ * (Hj + Hi + u * k) := by
    calc ℓ * (u * (df + dg)) = u * (ℓ * df) + u * (ℓ * dg) := by ring
      _ ≤ (ℓ * Hj + u * j) + (ℓ * Hi + u * i) := Nat.add_le_add h1 h2
      _ = ℓ * (Hj + Hi) + u * (j + i) := by ring
      _ ≤ ℓ * (Hj + Hi) + u * (ℓ * k) := by
          exact Nat.add_le_add_left (Nat.mul_le_mul_left u hji) _
      _ = ℓ * (Hj + Hi + u * k) := by ring
  have h3 : u * (df + dg) ≤ Hj + Hi + u * k := Nat.le_of_mul_le_mul_left hcalc hℓ
  have h4 : u * (df + dg) - u * k ≤ Hj + Hi := Nat.sub_le_iff_le_add.2 h3
  have hprod : gaussVal (dev φ f j * dev φ g i) = ((Hj + Hi : ℕ) : ℕ∞) := by
    rw [gaussVal_mul hπ, ← hHj, ← hHi]
    push_cast
    ring
  rw [hprod]
  exact_mod_cast h4

/-- **The carry and the off-side terms carry strictly more valuation.** If `j + i < ℓ·k`, or
`j + i = ℓ·k` with `ℓ ∤ j`, the Gauss valuation of `dev φ f j · dev φ g i` strictly exceeds the read
height, so its digit there vanishes. `0 < u` is what makes the first case strict — the A-F.6
counterexample at `u = 0`. -/
theorem lt_gaussVal_dev_mul (hπ : Irreducible π) (hφ : φ.Monic) (hd : 0 < φ.natDegree)
    (hf : f.Monic) (hg : g.Monic) (hfdeg : f.natDegree = ℓ * df * φ.natDegree)
    (hgdeg : g.natDegree = ℓ * dg * φ.natDegree) (hu : 0 < u) (hℓ : 0 < ℓ)
    (hcop : Nat.Coprime u ℓ) (hfp : IsPure φ f u ℓ) (hgp : IsPure φ g u ℓ) {k j i : ℕ}
    (hk : k ≤ df + dg) (hbad : j + i < ℓ * k ∨ (j + i = ℓ * k ∧ ¬ ℓ ∣ j)) :
    ((u * (df + dg) - u * k + 1 : ℕ) : ℕ∞) ≤ gaussVal (dev φ f j * dev φ g i) := by
  rcases eq_or_ne (gaussVal (dev φ f j)) ⊤ with hfT | hfT
  · rw [gaussVal_eq_top_iff.1 hfT, zero_mul, gaussVal_eq_top_iff.2 rfl]; exact le_top
  rcases eq_or_ne (gaussVal (dev φ g i)) ⊤ with hgT | hgT
  · rw [gaussVal_eq_top_iff.1 hgT, mul_zero, gaussVal_eq_top_iff.2 rfl]; exact le_top
  obtain ⟨Hj, hHj⟩ := ENat.ne_top_iff_exists.1 hfT
  obtain ⟨Hi, hHi⟩ := ENat.ne_top_iff_exists.1 hgT
  have h2 : u * (ℓ * dg) ≤ ℓ * Hi + u * i :=
    le_weight_of_pure hφ hd hg hgdeg hℓ hgp (j := i) (H := Hi) hHi.symm
  -- in both cases, `ℓ · (u·(d_f+d_g)) < ℓ · (H_j + H_i + u·k)`
  have hstrict : ℓ * (u * (df + dg)) < ℓ * (Hj + Hi + u * k) := by
    rcases hbad with hlt | ⟨heq, hnd⟩
    · have h1 : u * (ℓ * df) ≤ ℓ * Hj + u * j :=
        le_weight_of_pure hφ hd hf hfdeg hℓ hfp (j := j) (H := Hj) hHj.symm
      have hui : u * (j + i) < u * (ℓ * k) := mul_lt_mul_of_pos_left hlt hu
      calc ℓ * (u * (df + dg)) = u * (ℓ * df) + u * (ℓ * dg) := by ring
        _ ≤ (ℓ * Hj + u * j) + (ℓ * Hi + u * i) := Nat.add_le_add h1 h2
        _ = ℓ * (Hj + Hi) + u * (j + i) := by ring
        _ < ℓ * (Hj + Hi) + u * (ℓ * k) := by exact Nat.add_lt_add_left hui _
        _ = ℓ * (Hj + Hi + u * k) := by ring
    · have hns : ¬ OnSide φ f u ℓ j := fun hon =>
        hnd (dvd_of_onSide_of_pure hφ hd hf hfdeg hℓ hcop hfp hon)
      have h1 : u * (ℓ * df) < ℓ * Hj + u * j :=
        lt_weight_of_pure hφ hd hf hfdeg hℓ hfp (j := j) (H := Hj) hHj.symm hns
      calc ℓ * (u * (df + dg)) = u * (ℓ * df) + u * (ℓ * dg) := by ring
        _ < (ℓ * Hj + u * j) + (ℓ * Hi + u * i) := by
            exact Nat.add_lt_add_of_lt_of_le h1 h2
        _ = ℓ * (Hj + Hi) + u * (j + i) := by ring
        _ = ℓ * (Hj + Hi) + u * (ℓ * k) := by rw [heq]
        _ = ℓ * (Hj + Hi + u * k) := by ring
  have h3 : u * (df + dg) < Hj + Hi + u * k := Nat.lt_of_mul_lt_mul_left hstrict
  have hkle : u * k ≤ u * (df + dg) := Nat.mul_le_mul_left u hk
  have h4 : u * (df + dg) - u * k + 1 ≤ Hj + Hi := by omega
  have hprod : gaussVal (dev φ f j * dev φ g i) = ((Hj + Hi : ℕ) : ℕ∞) := by
    rw [gaussVal_mul hπ, ← hHj, ← hHi]
    push_cast
    ring
  rw [hprod]
  exact_mod_cast h4

end Estimates

/-! ### The term-by-term evaluation -/

section Terms

variable {φ : Polynomial O} {u ℓ : ℕ} {f g : Polynomial O} {df dg : ℕ}

/-- Every convolution term of the product's development at abscissa `ℓ·k` has Gauss valuation at
least the read height (the side condition of B35a's `resMk_finsetSum`). -/
theorem le_gaussVal_dev_term (hπ : Irreducible π) (hφ : φ.Monic) (hd : 0 < φ.natDegree)
    (hf : f.Monic) (hg : g.Monic) (hfdeg : f.natDegree = ℓ * df * φ.natDegree)
    (hgdeg : g.natDegree = ℓ * dg * φ.natDegree) (hℓ : 0 < ℓ) (hfp : IsPure φ f u ℓ)
    (hgp : IsPure φ g u ℓ) (k j i : ℕ) :
    ((u * (df + dg) - u * k : ℕ) : ℕ∞)
      ≤ gaussVal (dev φ (dev φ f j * dev φ g i * φ ^ (j + i)) (ℓ * k)) := by
  rcases Nat.lt_or_ge (ℓ * k) (j + i) with hlt | hge
  · rw [dev_mul_pow_of_lt hφ (j + i) _ (ℓ * k) hlt, gaussVal_eq_top_iff.2 rfl]
    exact le_top
  · obtain ⟨s, hs⟩ := Nat.exists_eq_add_of_le hge
    rw [hs, dev_mul_pow hφ (j + i) _ s]
    exact le_trans
      (le_gaussVal_dev_mul hπ hφ hd hf hg hfdeg hgdeg hℓ hfp hgp hge)
      (gaussVal_le_npHgt hπ hφ _ s)

/-- **The vanishing terms.** Unless `j + i = ℓ·k` with `ℓ ∣ j`, the term's digit at the read height
is `0`: either the development is `0` outright (the term sits to the right of `ℓ·k`), or the
strict estimate applies (the carry, and the off-side abscissae). -/
theorem resMk_dev_term_eq_zero (hπ : Irreducible π) (hφ : φ.Monic) (hd : 0 < φ.natDegree)
    (hf : f.Monic) (hg : g.Monic) (hfdeg : f.natDegree = ℓ * df * φ.natDegree)
    (hgdeg : g.natDegree = ℓ * dg * φ.natDegree) (hu : 0 < u) (hℓ : 0 < ℓ)
    (hcop : Nat.Coprime u ℓ) (hfp : IsPure φ f u ℓ) (hgp : IsPure φ g u ℓ) {k : ℕ}
    (hk : k ≤ df + dg) {j i : ℕ} (hbad : ¬ (j + i = ℓ * k ∧ ℓ ∣ j)) :
    resMk π φ (u * (df + dg) - u * k) (dev φ (dev φ f j * dev φ g i * φ ^ (j + i)) (ℓ * k))
      = 0 := by
  rcases Nat.lt_or_ge (ℓ * k) (j + i) with hlt | hge
  · rw [dev_mul_pow_of_lt hφ (j + i) _ (ℓ * k) hlt]
    exact resMk_of_zero hπ φ _
  · obtain ⟨s, hs⟩ := Nat.exists_eq_add_of_le hge
    have hbad' : j + i < ℓ * k ∨ (j + i = ℓ * k ∧ ¬ ℓ ∣ j) := by
      rcases Nat.lt_or_ge (j + i) (ℓ * k) with h | h
      · exact Or.inl h
      · have heq : j + i = ℓ * k := le_antisymm hge h
        exact Or.inr ⟨heq, fun hdvd => hbad ⟨heq, hdvd⟩⟩
    have hstrict := lt_gaussVal_dev_mul hπ hφ hd hf hg hfdeg hgdeg hu hℓ hcop hfp hgp hk hbad'
    rw [hs, dev_mul_pow hφ (j + i) _ s]
    refine resMk_eq_zero_of_lt hπ (le_trans ?_ (gaussVal_le_npHgt hπ hφ _ s))
    exact hstrict

/-- **The surviving terms.** At `j = ℓ·k₁`, `i = ℓ·k₂` with `k₁ + k₂ = k`, the term's digit is the
product of the two side digits, the heights adding. -/
theorem resMk_dev_term_eq_mul (hπ : Irreducible π) (hφ : φ.Monic) (hd : 0 < φ.natDegree)
    (hf : f.Monic) (hg : g.Monic) (hfdeg : f.natDegree = ℓ * df * φ.natDegree)
    (hgdeg : g.natDegree = ℓ * dg * φ.natDegree) (hℓ : 0 < ℓ) (hfp : IsPure φ f u ℓ)
    (hgp : IsPure φ g u ℓ) {k k₁ : ℕ} (hk₁ : k₁ ≤ k) :
    resMk π φ (u * (df + dg) - u * k)
        (dev φ (dev φ f (ℓ * k₁) * dev φ g (ℓ * (k - k₁)) * φ ^ (ℓ * k₁ + ℓ * (k - k₁))) (ℓ * k))
      = resMk π φ (u * df - u * k₁) (dev φ f (ℓ * k₁))
          * resMk π φ (u * dg - u * (k - k₁)) (dev φ g (ℓ * (k - k₁))) := by
  have habs : ℓ * k₁ + ℓ * (k - k₁) = ℓ * k := by
    rw [← Nat.mul_add, Nat.add_sub_cancel' hk₁]
  -- the term's development at `ℓ·k` is the convolution product mod `φ`
  have hdevterm : dev φ (dev φ f (ℓ * k₁) * dev φ g (ℓ * (k - k₁)) * φ ^ (ℓ * k₁ + ℓ * (k - k₁)))
      (ℓ * k) = (dev φ f (ℓ * k₁) * dev φ g (ℓ * (k - k₁))) %ₘ φ := by
    rw [habs]
    have := dev_mul_pow hφ (ℓ * k) (dev φ f (ℓ * k₁) * dev φ g (ℓ * (k - k₁))) 0
    rw [Nat.add_zero] at this
    rw [this, dev]
  rw [hdevterm]
  -- the two on-side digit bounds
  by_cases hdf : df < k₁
  · -- `f`'s development already vanishes at this abscissa
    have hz : dev φ f (ℓ * k₁) = 0 := by
      refine dev_eq_zero_of_lt hφ hd f (ℓ * k₁) ?_
      rw [hfdeg]
      exact mul_lt_mul_of_pos_right (mul_lt_mul_of_pos_left hdf hℓ) hd
    rw [hz, zero_mul, Polynomial.zero_modByMonic, resMk_of_zero hπ, resMk_of_zero hπ, zero_mul]
  by_cases hdg : dg < k - k₁
  · have hz : dev φ g (ℓ * (k - k₁)) = 0 := by
      refine dev_eq_zero_of_lt hφ hd g (ℓ * (k - k₁)) ?_
      rw [hgdeg]
      exact mul_lt_mul_of_pos_right (mul_lt_mul_of_pos_left hdg hℓ) hd
    rw [hz, mul_zero, Polynomial.zero_modByMonic, resMk_of_zero hπ, resMk_of_zero hπ, mul_zero]
  have hdf' : k₁ ≤ df := Nat.not_lt.1 hdf
  have hdg' : k - k₁ ≤ dg := Nat.not_lt.1 hdg
  -- both positions are inside their sides: the heights add exactly
  have hheights : (u * df - u * k₁) + (u * dg - u * (k - k₁)) = u * (df + dg) - u * k := by
    have e1 : u * k₁ ≤ u * df := Nat.mul_le_mul_left u hdf'
    have e2 : u * (k - k₁) ≤ u * dg := Nat.mul_le_mul_left u hdg'
    have e3 : u * k₁ + u * (k - k₁) = u * k := by
      rw [← Nat.mul_add, Nat.add_sub_cancel' hk₁]
    have e4 : u * df + u * dg = u * (df + dg) := by ring
    omega
  have hbf : ((u * df - u * k₁ : ℕ) : ℕ∞) ≤ gaussVal (dev φ f (ℓ * k₁)) := by
    rcases eq_or_ne (gaussVal (dev φ f (ℓ * k₁))) ⊤ with hT | hT
    · rw [hT]; exact le_top
    obtain ⟨H, hH⟩ := ENat.ne_top_iff_exists.1 hT
    have h1 : u * (ℓ * df) ≤ ℓ * H + u * (ℓ * k₁) :=
      le_weight_of_pure hφ hd hf hfdeg hℓ hfp (j := ℓ * k₁) (H := H) hH.symm
    have h2 : ℓ * (u * df) ≤ ℓ * (H + u * k₁) := by
      calc ℓ * (u * df) = u * (ℓ * df) := by ring
        _ ≤ ℓ * H + u * (ℓ * k₁) := h1
        _ = ℓ * (H + u * k₁) := by ring
    have h3 : u * df ≤ H + u * k₁ := Nat.le_of_mul_le_mul_left h2 hℓ
    have h4 : u * df - u * k₁ ≤ H := Nat.sub_le_iff_le_add.2 h3
    rw [← hH]
    exact_mod_cast h4
  have hbg : ((u * dg - u * (k - k₁) : ℕ) : ℕ∞) ≤ gaussVal (dev φ g (ℓ * (k - k₁))) := by
    rcases eq_or_ne (gaussVal (dev φ g (ℓ * (k - k₁)))) ⊤ with hT | hT
    · rw [hT]; exact le_top
    obtain ⟨H, hH⟩ := ENat.ne_top_iff_exists.1 hT
    have h1 : u * (ℓ * dg) ≤ ℓ * H + u * (ℓ * (k - k₁)) :=
      le_weight_of_pure hφ hd hg hgdeg hℓ hgp (j := ℓ * (k - k₁)) (H := H) hH.symm
    have h2 : ℓ * (u * dg) ≤ ℓ * (H + u * (k - k₁)) := by
      calc ℓ * (u * dg) = u * (ℓ * dg) := by ring
        _ ≤ ℓ * H + u * (ℓ * (k - k₁)) := h1
        _ = ℓ * (H + u * (k - k₁)) := by ring
    have h3 : u * dg ≤ H + u * (k - k₁) := Nat.le_of_mul_le_mul_left h2 hℓ
    have h4 : u * dg - u * (k - k₁) ≤ H := Nat.sub_le_iff_le_add.2 h3
    rw [← hH]
    exact_mod_cast h4
  have hmulval : ((u * (df + dg) - u * k : ℕ) : ℕ∞)
      ≤ gaussVal (dev φ f (ℓ * k₁) * dev φ g (ℓ * (k - k₁))) := by
    rw [gaussVal_mul hπ, ← hheights]
    push_cast
    exact add_le_add hbf hbg
  rw [resMk_modByMonic hπ hφ hmulval, ← hheights, resMk_mul hπ hbf hbg]

end Terms

/-! ### The master identity -/

/-- **B.35, PROOF step 3–5 (the file's contract).** For `f`, `g` monic and `(u,ℓ)`-pure of full
degrees `ℓ·d_f·m`, `ℓ·d_g·m`, the digit of the product's development at abscissa `ℓ·k` and the
side's line height is the convolution of the two side digit families:

```
resMk π φ (u·(d_f+d_g) − u·k) (dev φ (f*g) (ℓ·k))
  = Σ_{k₁ ≤ k} resMk π φ (u·d_f − u·k₁) (dev φ f (ℓ·k₁))
              · resMk π φ (u·d_g − u·(k−k₁)) (dev φ g (ℓ·(k−k₁)))
```

`0 < u` is load-bearing (the carry estimate); at `u = 0` the identity is false (amendment
A-F.6). -/
theorem resMk_dev_mul (hπ : Irreducible π) {φ : Polynomial O} (hφ : φ.Monic)
    (hd : 0 < φ.natDegree) {u ℓ : ℕ} (hu : 0 < u) (hℓ : 0 < ℓ) (hcop : Nat.Coprime u ℓ)
    {f g : Polynomial O} (hf : f.Monic) (hg : g.Monic) {df dg : ℕ}
    (hfdeg : f.natDegree = ℓ * df * φ.natDegree) (hgdeg : g.natDegree = ℓ * dg * φ.natDegree)
    (hfp : IsPure φ f u ℓ) (hgp : IsPure φ g u ℓ) {k : ℕ} (hk : k ≤ df + dg) :
    resMk π φ (u * (df + dg) - u * k) (dev φ (f * g) (ℓ * k))
      = ∑ k₁ ∈ Finset.range (k + 1),
          resMk π φ (u * df - u * k₁) (dev φ f (ℓ * k₁))
            * resMk π φ (u * dg - u * (k - k₁)) (dev φ g (ℓ * (k - k₁))) := by
  classical
  set N := ℓ * k + ℓ * df + ℓ * dg + 1 with hN
  -- Step 1: the double representation of the product.
  have hfN : f.natDegree < N * φ.natDegree := by
    rw [hfdeg]
    exact mul_lt_mul_of_pos_right (by omega) hd
  have hgN : g.natDegree < N * φ.natDegree := by
    rw [hgdeg]
    exact mul_lt_mul_of_pos_right (by omega) hd
  have hfrep : ∑ j ∈ Finset.range N, dev φ f j * φ ^ j = f := sum_dev_eq hφ hd f hfN
  have hgrep : ∑ i ∈ Finset.range N, dev φ g i * φ ^ i = g := sum_dev_eq hφ hd g hgN
  have hrep : f * g = ∑ p ∈ Finset.range N ×ˢ Finset.range N,
      dev φ f p.1 * dev φ g p.2 * φ ^ (p.1 + p.2) := by
    have h1 : f * g = (∑ j ∈ Finset.range N, dev φ f j * φ ^ j)
        * (∑ i ∈ Finset.range N, dev φ g i * φ ^ i) := by rw [hfrep, hgrep]
    rw [h1, Finset.sum_mul_sum, Finset.sum_product]
    exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => by
      rw [pow_add]; ring
  -- Step 2: the development, then the digit, distribute over the double sum.
  have hdev : dev φ (f * g) (ℓ * k)
      = ∑ p ∈ Finset.range N ×ˢ Finset.range N,
          dev φ (dev φ f p.1 * dev φ g p.2 * φ ^ (p.1 + p.2)) (ℓ * k) := by
    rw [hrep, dev_finsetSum hφ]
  have hval : ∀ p ∈ Finset.range N ×ˢ Finset.range N,
      ((u * (df + dg) - u * k : ℕ) : ℕ∞)
        ≤ gaussVal (dev φ (dev φ f p.1 * dev φ g p.2 * φ ^ (p.1 + p.2)) (ℓ * k)) := by
    intro p _
    exact le_gaussVal_dev_term hπ hφ hd hf hg hfdeg hgdeg hℓ hfp hgp (ℓ := ℓ) k p.1 p.2
  rw [hdev, resMk_finsetSum hπ _ _ hval]
  -- Step 3: only the lattice pairs `(ℓ·k₁, ℓ·(k−k₁))` survive.
  set G : Finset (ℕ × ℕ) :=
    (Finset.range (k + 1)).image (fun k₁ => ((ℓ * k₁, ℓ * (k - k₁)) : ℕ × ℕ)) with hG
  have hGsub : G ⊆ Finset.range N ×ˢ Finset.range N := by
    intro p hp
    rw [hG, Finset.mem_image] at hp
    obtain ⟨k₁, hk₁, rfl⟩ := hp
    rw [Finset.mem_range] at hk₁
    refine Finset.mem_product.2 ⟨Finset.mem_range.2 ?_, Finset.mem_range.2 ?_⟩
    · have : ℓ * k₁ ≤ ℓ * k := Nat.mul_le_mul_left ℓ (by omega)
      omega
    · have : ℓ * (k - k₁) ≤ ℓ * k := Nat.mul_le_mul_left ℓ (by omega)
      omega
  have hvanish : ∀ p ∈ Finset.range N ×ˢ Finset.range N, p ∉ G →
      resMk π φ (u * (df + dg) - u * k)
        (dev φ (dev φ f p.1 * dev φ g p.2 * φ ^ (p.1 + p.2)) (ℓ * k)) = 0 := by
    intro p _ hpG
    refine resMk_dev_term_eq_zero hπ hφ hd hf hg hfdeg hgdeg hu hℓ hcop hfp hgp hk ?_
    rintro ⟨hsum, k₁, hk₁eq⟩
    refine hpG ?_
    have hk₁le : k₁ ≤ k := by
      rcases Nat.lt_or_ge k k₁ with hcon | hcon
      · have hlt : ℓ * k < ℓ * k₁ := mul_lt_mul_of_pos_left hcon hℓ
        omega
      · exact hcon
    have hsplit : ℓ * k₁ + ℓ * (k - k₁) = ℓ * k := by
      rw [← Nat.mul_add, Nat.add_sub_cancel' hk₁le]
    have hp2 : p.2 = ℓ * (k - k₁) := by omega
    rw [hG, Finset.mem_image]
    exact ⟨k₁, Finset.mem_range.2 (by omega),
      by rw [Prod.ext_iff]; exact ⟨hk₁eq.symm, hp2.symm⟩⟩
  rw [← Finset.sum_subset hGsub hvanish]
  -- Step 4: reindex the surviving pairs by `k₁`, and evaluate each.
  rw [hG, Finset.sum_image (by
    intro a ha b hb hab
    have : ℓ * a = ℓ * b := (Prod.ext_iff.1 hab).1
    exact Nat.eq_of_mul_eq_mul_left hℓ this)]
  refine Finset.sum_congr rfl fun k₁ hk₁ => ?_
  rw [Finset.mem_range] at hk₁
  exact resMk_dev_term_eq_mul hπ hφ hd hf hg hfdeg hgdeg hℓ hfp hgp (by omega)

end Uniformity.Density.Leaf

/-! ## Axiom footprint -/

section AxCheck
#print axioms Uniformity.Density.Leaf.suppVal_le_weight
#print axioms Uniformity.Density.Leaf.suppVal_of_pure
#print axioms Uniformity.Density.Leaf.sideMin_of_pure
#print axioms Uniformity.Density.Leaf.sideMax_of_pure
#print axioms Uniformity.Density.Leaf.sideDeg_of_pure
#print axioms Uniformity.Density.Leaf.dvd_of_onSide_of_pure
#print axioms Uniformity.Density.Leaf.le_weight_of_pure
#print axioms Uniformity.Density.Leaf.lt_weight_of_pure
#print axioms Uniformity.Density.Leaf.le_gaussVal_dev_mul
#print axioms Uniformity.Density.Leaf.lt_gaussVal_dev_mul
#print axioms Uniformity.Density.Leaf.le_gaussVal_dev_term
#print axioms Uniformity.Density.Leaf.resMk_dev_term_eq_zero
#print axioms Uniformity.Density.Leaf.resMk_dev_term_eq_mul
#print axioms Uniformity.Density.Leaf.resMk_dev_mul
end AxCheck
