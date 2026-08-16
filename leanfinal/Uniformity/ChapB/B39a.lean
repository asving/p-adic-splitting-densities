/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapB.B30
import Uniformity.ChapB.B33
import Uniformity.ChapB.B35a
import Uniformity.ChapB.B35b
import Uniformity.ChapB.B37

/-!
# Uniformity.ChapB.B39a — the general graded product law

**Chapter B, infrastructure for NODE B.39** (`blueprint/CHAP-B_leaf_layer.md` §6, PROOF steps
1–5), ENV-A′.  **B.39 itself is NOT landed: its frozen signature is machine-refuted a third
time** — see `B39_REFUTATION_2.lean.txt` in this directory (the missing level hypothesis
`suppVal φ (g*h) u ℓ ≤ c`).  What this file lands is the reusable half of B.39's route, which
the refutation does not impugn.

The landed B.35 cluster (`B35a`–`B35d`) proves the product law only for factors that
are *monic, `(u,ℓ)`-pure and of `φ.natDegree`-divisible degree*; the Hensel correction terms
`h * U` of B.39/B.41 are none of those (`U` is a lift of a residual polynomial: not monic, its
side does not start at abscissa `0`, its degree is not a multiple of `φ.natDegree`).  The
generalisation below replaces every use of purity by the *weight identity* it was standing in
for — `suppVal φ f u ℓ = ℓ·H_f + u·j_f` at the side's left endpoint `j_f = sideMin` — which is
what the landed proofs actually consume (through `le_weight_of_pure`, `lt_weight_of_pure`,
`dvd_of_onSide_of_pure`).  The landed general tools it rests on are already stated without
purity: `suppVal_le_weight` (B35b), `onSide_eq_add_mul`/`onSide_modEq` (B.17/B.20),
`sideMax_eq` (B.20), `resCoeff_eq_zero_iff`/`natDegree_resPoly` (B.30),
`suppVal_add_le_suppVal_mul` (B.33).

## What is proved here

* `nsmul_add_cast_gen`, `suppVal_eq_of_onSide`, `le_weight_gen`, `lt_weight_gen`,
  `le_gaussVal_dev_lattice` — the weight dictionary at a side's left endpoint.
* `resPoly_coeff` — B.29's sum, coefficientwise.
* `le_gaussVal_dev_mul_gen`, `lt_gaussVal_dev_mul_gen`, `le_gaussVal_dev_term_gen`,
  `resMk_dev_term_eq_zero_gen`, `resMk_dev_term_eq_mul_gen` — the two convolution estimates and
  the term evaluation, purity-free.
* `resMk_dev_mul_gen` — **the general master identity**: the digit of `(f*z)`'s development at
  the lattice abscissa `j_f + j_z + ℓ·k` and the line height `H_f + H_z − u·k` is the `k`-th
  coefficient of the product of the two residual polynomials.
* `resMk_dev_mul_left_ne_zero`, `npHgt_mul_gen`, `suppVal_mul_gen`, `sideMin_mul_gen`,
  `sideDeg_mul_gen`, `resPoly_mul_gen` — **the general product law**: `suppVal` is additive,
  the sides' left endpoints and their residual degrees add, and `resPoly` is multiplicative.
  (`onSide_mul_decomp` is the engine: an on-side abscissa of a product splits.)

**Flagged for human review** (new general statements, parent CLAUDE.md trust boundary): the
product law is asserted here in a strictly stronger form than the signed B.35 — no purity, no
monicity, no degree divisibility, only finiteness of the two support values.  Nothing in this
file is a signed §-node statement; every declaration is infrastructure.

## Status

Sorry-free, axiom-free (Lean core only).
-/

namespace Uniformity.Density.Leaf

open Polynomial IsLocalRing

-- ENV-A (blueprint §0.1) plus `hπ : Irreducible π` per signature (ENV-A′).
variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {π : O}

/-! ## 1. The weight dictionary at a side's left endpoint -/

section Weights

variable {φ : Polynomial O} {u ℓ : ℕ}

/-- The cleared `ℕ∞`-weight of a polygon point at a finite height is the cast of its
`ℕ`-value (B.30's private `nsmul_add_cast`, re-proved here). -/
theorem nsmul_add_cast_gen (ℓ a b : ℕ) :
    ℓ • (a : ℕ∞) + ((b : ℕ) : ℕ∞) = ((ℓ * a + b : ℕ) : ℕ∞) := by
  push_cast [nsmul_eq_mul]
  ring

/-- **The support value, read off any on-side abscissa.** -/
theorem suppVal_eq_of_onSide {f : Polynomial O} {j H : ℕ}
    (hH : npHgt φ f j = (H : ℕ∞)) (hj : OnSide φ f u ℓ j) :
    suppVal φ f u ℓ = ((ℓ * H + u * j : ℕ) : ℕ∞) := by
  have h : ℓ • npHgt φ f j + ((u * j : ℕ) : ℕ∞) = suppVal φ f u ℓ := hj
  rw [← h, hH, nsmul_add_cast_gen]

/-- **The side's line lies below the polygon** (the purity-free form of `le_weight_of_pure`). -/
theorem le_weight_gen (hφ : φ.Monic) (hd : 0 < φ.natDegree) (hℓ : 0 < ℓ)
    {f : Polynomial O} {S : ℕ} (hS : suppVal φ f u ℓ = (S : ℕ∞))
    {j H : ℕ} (hH : npHgt φ f j = (H : ℕ∞)) : S ≤ ℓ * H + u * j := by
  have h := suppVal_le_weight hφ hd hℓ u f j
  rw [hS, hH, nsmul_add_cast_gen] at h
  exact_mod_cast h

/-- **Off the side the line is strictly below the polygon** (the purity-free form of
`lt_weight_of_pure`). -/
theorem lt_weight_gen (hφ : φ.Monic) (hd : 0 < φ.natDegree) (hℓ : 0 < ℓ)
    {f : Polynomial O} {S : ℕ} (hS : suppVal φ f u ℓ = (S : ℕ∞))
    {j H : ℕ} (hH : npHgt φ f j = (H : ℕ∞)) (hns : ¬ OnSide φ f u ℓ j) :
    S < ℓ * H + u * j := by
  rcases eq_or_lt_of_le (le_weight_gen hφ hd hℓ hS hH) with heq | hlt
  · refine absurd ?_ hns
    show ℓ • npHgt φ f j + ((u * j : ℕ) : ℕ∞) = suppVal φ f u ℓ
    rw [hH, nsmul_add_cast_gen, hS, heq]
  · exact hlt

/-- **The line height at a lattice abscissa bounds the development's Gauss valuation.** -/
theorem le_gaussVal_dev_lattice (hφ : φ.Monic) (hd : 0 < φ.natDegree) (hℓ : 0 < ℓ)
    {f : Polynomial O} {jf Hf : ℕ}
    (hS : suppVal φ f u ℓ = ((ℓ * Hf + u * jf : ℕ) : ℕ∞)) (k : ℕ) :
    ((Hf - u * k : ℕ) : ℕ∞) ≤ gaussVal (dev φ f (jf + ℓ * k)) := by
  rcases eq_or_ne (gaussVal (dev φ f (jf + ℓ * k))) ⊤ with hT | hT
  · rw [hT]; exact le_top
  obtain ⟨H, hH⟩ := ENat.ne_top_iff_exists.1 hT
  have hnp : npHgt φ f (jf + ℓ * k) = (H : ℕ∞) := hH.symm
  have h1 := le_weight_gen hφ hd hℓ hS hnp
  have h2 : ℓ * Hf ≤ ℓ * (H + u * k) := by
    calc ℓ * Hf = (ℓ * Hf + u * jf) - u * jf := by omega
      _ ≤ (ℓ * H + u * (jf + ℓ * k)) - u * jf := by omega
      _ = ℓ * (H + u * k) := by ring_nf; omega
  have h3 : Hf ≤ H + u * k := Nat.le_of_mul_le_mul_left h2 hℓ
  rw [← hH]
  exact_mod_cast (by omega : Hf - u * k ≤ H)

end Weights

/-! ## 2. B.29's residual polynomial, coefficientwise -/

/-- **B.29's sum, coefficientwise.** -/
theorem resPoly_coeff {φ f : Polynomial O} {u ℓ : ℕ} (h : (sideSet φ f u ℓ).Nonempty)
    (H₀ i : ℕ) :
    (resPoly π φ f u ℓ h H₀).coeff i =
      if i < sideDeg φ f u ℓ h + 1 then resCoeff π φ f u ℓ h H₀ i else 0 := by
  rw [resPoly, Uniformity.Hensel.coeff_sum_range_C_mul_X_pow]

/-! ## 3. The two convolution estimates, purity-free -/

section Estimates

variable {φ : Polynomial O} {u ℓ : ℕ} {f z : Polynomial O} {jf Hf jz Hz : ℕ}

/-- **The convolution term carries enough valuation** (the purity-free `le_gaussVal_dev_mul`).
If the term `dev φ f j · dev φ z i` can reach the lattice abscissa `j_f + j_z + ℓ·k` at all, its
Gauss valuation is at least the read height `H_f + H_z − u·k`. -/
theorem le_gaussVal_dev_mul_gen (hπ : Irreducible π) (hφ : φ.Monic) (hd : 0 < φ.natDegree)
    (hℓ : 0 < ℓ)
    (hSf : suppVal φ f u ℓ = ((ℓ * Hf + u * jf : ℕ) : ℕ∞))
    (hSz : suppVal φ z u ℓ = ((ℓ * Hz + u * jz : ℕ) : ℕ∞))
    {k j i : ℕ} (hji : j + i ≤ jf + jz + ℓ * k) :
    ((Hf + Hz - u * k : ℕ) : ℕ∞) ≤ gaussVal (dev φ f j * dev φ z i) := by
  rcases eq_or_ne (gaussVal (dev φ f j)) ⊤ with hfT | hfT
  · rw [gaussVal_eq_top_iff.1 hfT, zero_mul, gaussVal_eq_top_iff.2 rfl]; exact le_top
  rcases eq_or_ne (gaussVal (dev φ z i)) ⊤ with hzT | hzT
  · rw [gaussVal_eq_top_iff.1 hzT, mul_zero, gaussVal_eq_top_iff.2 rfl]; exact le_top
  obtain ⟨Hj, hHj⟩ := ENat.ne_top_iff_exists.1 hfT
  obtain ⟨Hi, hHi⟩ := ENat.ne_top_iff_exists.1 hzT
  have h1 : ℓ * Hf + u * jf ≤ ℓ * Hj + u * j := le_weight_gen hφ hd hℓ hSf hHj.symm
  have h2 : ℓ * Hz + u * jz ≤ ℓ * Hi + u * i := le_weight_gen hφ hd hℓ hSz hHi.symm
  have hui : u * (j + i) ≤ u * (jf + jz + ℓ * k) := Nat.mul_le_mul_left u hji
  have hstep : ℓ * (Hf + Hz) + u * (jf + jz) ≤ ℓ * (Hj + Hi + u * k) + u * (jf + jz) := by
    calc ℓ * (Hf + Hz) + u * (jf + jz)
        = (ℓ * Hf + u * jf) + (ℓ * Hz + u * jz) := by ring
      _ ≤ (ℓ * Hj + u * j) + (ℓ * Hi + u * i) := Nat.add_le_add h1 h2
      _ = ℓ * (Hj + Hi) + u * (j + i) := by ring
      _ ≤ ℓ * (Hj + Hi) + u * (jf + jz + ℓ * k) := Nat.add_le_add_left hui _
      _ = ℓ * (Hj + Hi + u * k) + u * (jf + jz) := by ring
  have h3 : Hf + Hz ≤ Hj + Hi + u * k :=
    Nat.le_of_mul_le_mul_left (Nat.le_of_add_le_add_right hstep) hℓ
  have hprod : gaussVal (dev φ f j * dev φ z i) = ((Hj + Hi : ℕ) : ℕ∞) := by
    rw [gaussVal_mul hπ, ← hHj, ← hHi]
    push_cast
    ring
  rw [hprod]
  exact_mod_cast (by omega : Hf + Hz - u * k ≤ Hj + Hi)

/-- **The carry and the off-side terms carry strictly more valuation** (the purity-free
`lt_gaussVal_dev_mul`). `0 < u` is what makes the carry case strict. -/
theorem lt_gaussVal_dev_mul_gen (hπ : Irreducible π) (hφ : φ.Monic) (hd : 0 < φ.natDegree)
    (hu : 0 < u) (hℓ : 0 < ℓ)
    (hSf : suppVal φ f u ℓ = ((ℓ * Hf + u * jf : ℕ) : ℕ∞))
    (hSz : suppVal φ z u ℓ = ((ℓ * Hz + u * jz : ℕ) : ℕ∞))
    {k j i : ℕ} (hk : u * k ≤ Hf + Hz)
    (hbad : j + i < jf + jz + ℓ * k ∨
      (j + i = jf + jz + ℓ * k ∧ (¬ OnSide φ f u ℓ j ∨ ¬ OnSide φ z u ℓ i))) :
    ((Hf + Hz - u * k + 1 : ℕ) : ℕ∞) ≤ gaussVal (dev φ f j * dev φ z i) := by
  rcases eq_or_ne (gaussVal (dev φ f j)) ⊤ with hfT | hfT
  · rw [gaussVal_eq_top_iff.1 hfT, zero_mul, gaussVal_eq_top_iff.2 rfl]; exact le_top
  rcases eq_or_ne (gaussVal (dev φ z i)) ⊤ with hzT | hzT
  · rw [gaussVal_eq_top_iff.1 hzT, mul_zero, gaussVal_eq_top_iff.2 rfl]; exact le_top
  obtain ⟨Hj, hHj⟩ := ENat.ne_top_iff_exists.1 hfT
  obtain ⟨Hi, hHi⟩ := ENat.ne_top_iff_exists.1 hzT
  have hstrict : ℓ * (Hf + Hz) + u * (jf + jz) < ℓ * (Hj + Hi + u * k) + u * (jf + jz) := by
    rcases hbad with hlt | ⟨heq, hoff⟩
    · have h1 : ℓ * Hf + u * jf ≤ ℓ * Hj + u * j := le_weight_gen hφ hd hℓ hSf hHj.symm
      have h2 : ℓ * Hz + u * jz ≤ ℓ * Hi + u * i := le_weight_gen hφ hd hℓ hSz hHi.symm
      have hui : u * (j + i) < u * (jf + jz + ℓ * k) := mul_lt_mul_of_pos_left hlt hu
      calc ℓ * (Hf + Hz) + u * (jf + jz)
          = (ℓ * Hf + u * jf) + (ℓ * Hz + u * jz) := by ring
        _ ≤ (ℓ * Hj + u * j) + (ℓ * Hi + u * i) := Nat.add_le_add h1 h2
        _ = ℓ * (Hj + Hi) + u * (j + i) := by ring
        _ < ℓ * (Hj + Hi) + u * (jf + jz + ℓ * k) := Nat.add_lt_add_left hui _
        _ = ℓ * (Hj + Hi + u * k) + u * (jf + jz) := by ring
    · have hsum : (ℓ * Hf + u * jf) + (ℓ * Hz + u * jz)
          < (ℓ * Hj + u * j) + (ℓ * Hi + u * i) := by
        rcases hoff with hnf | hnz
        · exact Nat.add_lt_add_of_lt_of_le (lt_weight_gen hφ hd hℓ hSf hHj.symm hnf)
            (le_weight_gen hφ hd hℓ hSz hHi.symm)
        · exact Nat.add_lt_add_of_le_of_lt (le_weight_gen hφ hd hℓ hSf hHj.symm)
            (lt_weight_gen hφ hd hℓ hSz hHi.symm hnz)
      calc ℓ * (Hf + Hz) + u * (jf + jz)
          = (ℓ * Hf + u * jf) + (ℓ * Hz + u * jz) := by ring
        _ < (ℓ * Hj + u * j) + (ℓ * Hi + u * i) := hsum
        _ = ℓ * (Hj + Hi) + u * (j + i) := by ring
        _ = ℓ * (Hj + Hi) + u * (jf + jz + ℓ * k) := by rw [heq]
        _ = ℓ * (Hj + Hi + u * k) + u * (jf + jz) := by ring
  have h3 : Hf + Hz < Hj + Hi + u * k :=
    Nat.lt_of_mul_lt_mul_left (Nat.lt_of_add_lt_add_right hstrict)
  have hprod : gaussVal (dev φ f j * dev φ z i) = ((Hj + Hi : ℕ) : ℕ∞) := by
    rw [gaussVal_mul hπ, ← hHj, ← hHi]
    push_cast
    ring
  rw [hprod]
  exact_mod_cast (by omega : Hf + Hz - u * k + 1 ≤ Hj + Hi)

/-- Every convolution term of the product's development at the lattice abscissa has Gauss
valuation at least the read height (the side condition of B35a's `resMk_finsetSum`). -/
theorem le_gaussVal_dev_term_gen (hπ : Irreducible π) (hφ : φ.Monic) (hd : 0 < φ.natDegree)
    (hℓ : 0 < ℓ)
    (hSf : suppVal φ f u ℓ = ((ℓ * Hf + u * jf : ℕ) : ℕ∞))
    (hSz : suppVal φ z u ℓ = ((ℓ * Hz + u * jz : ℕ) : ℕ∞)) (k j i : ℕ) :
    ((Hf + Hz - u * k : ℕ) : ℕ∞)
      ≤ gaussVal (dev φ (dev φ f j * dev φ z i * φ ^ (j + i)) (jf + jz + ℓ * k)) := by
  rcases Nat.lt_or_ge (jf + jz + ℓ * k) (j + i) with hlt | hge
  · rw [dev_mul_pow_of_lt hφ (j + i) _ (jf + jz + ℓ * k) hlt, gaussVal_eq_top_iff.2 rfl]
    exact le_top
  · obtain ⟨s, hs⟩ := Nat.exists_eq_add_of_le hge
    rw [hs, dev_mul_pow hφ (j + i) _ s]
    exact le_trans (le_gaussVal_dev_mul_gen hπ hφ hd hℓ hSf hSz hge)
      (gaussVal_le_npHgt hπ hφ _ s)

/-- **The vanishing terms.** Unless the term sits exactly at the lattice abscissa with *both*
factors on their sides, its digit at the read height is `0`. -/
theorem resMk_dev_term_eq_zero_gen (hπ : Irreducible π) (hφ : φ.Monic) (hd : 0 < φ.natDegree)
    (hu : 0 < u) (hℓ : 0 < ℓ)
    (hSf : suppVal φ f u ℓ = ((ℓ * Hf + u * jf : ℕ) : ℕ∞))
    (hSz : suppVal φ z u ℓ = ((ℓ * Hz + u * jz : ℕ) : ℕ∞))
    {k : ℕ} (hk : u * k ≤ Hf + Hz) {j i : ℕ}
    (hbad : ¬ (j + i = jf + jz + ℓ * k ∧ OnSide φ f u ℓ j ∧ OnSide φ z u ℓ i)) :
    resMk π φ (Hf + Hz - u * k)
        (dev φ (dev φ f j * dev φ z i * φ ^ (j + i)) (jf + jz + ℓ * k)) = 0 := by
  classical
  rcases Nat.lt_or_ge (jf + jz + ℓ * k) (j + i) with hlt | hge
  · rw [dev_mul_pow_of_lt hφ (j + i) _ (jf + jz + ℓ * k) hlt]
    exact resMk_of_zero hπ φ _
  · obtain ⟨s, hs⟩ := Nat.exists_eq_add_of_le hge
    have hbad' : j + i < jf + jz + ℓ * k ∨
        (j + i = jf + jz + ℓ * k ∧ (¬ OnSide φ f u ℓ j ∨ ¬ OnSide φ z u ℓ i)) := by
      rcases Nat.lt_or_ge (j + i) (jf + jz + ℓ * k) with h | h
      · exact Or.inl h
      · have heq : j + i = jf + jz + ℓ * k := le_antisymm hge h
        refine Or.inr ⟨heq, ?_⟩
        by_cases honf : OnSide φ f u ℓ j
        · by_cases honz : OnSide φ z u ℓ i
          · exact absurd ⟨heq, honf, honz⟩ hbad
          · exact Or.inr honz
        · exact Or.inl honf
    have hstrict := lt_gaussVal_dev_mul_gen hπ hφ hd hu hℓ hSf hSz hk hbad'
    rw [hs, dev_mul_pow hφ (j + i) _ s]
    exact resMk_eq_zero_of_lt hπ (le_trans hstrict (gaussVal_le_npHgt hπ hφ _ s))

/-- **The surviving terms.** At the lattice pair `(j_f + ℓ·k₁, j_z + ℓ·k₂)` with `k₁ + k₂ = k`
the term's digit is the product of the two side digits, the heights adding. -/
theorem resMk_dev_term_eq_mul_gen (hπ : Irreducible π) (hφ : φ.Monic) (hd : 0 < φ.natDegree)
    (hℓ : 0 < ℓ)
    (hSf : suppVal φ f u ℓ = ((ℓ * Hf + u * jf : ℕ) : ℕ∞))
    (hSz : suppVal φ z u ℓ = ((ℓ * Hz + u * jz : ℕ) : ℕ∞))
    {k k₁ : ℕ} (hk₁ : k₁ ≤ k) (hkf : u * k₁ ≤ Hf) (hkz : u * (k - k₁) ≤ Hz) :
    resMk π φ (Hf + Hz - u * k)
        (dev φ (dev φ f (jf + ℓ * k₁) * dev φ z (jz + ℓ * (k - k₁))
          * φ ^ ((jf + ℓ * k₁) + (jz + ℓ * (k - k₁)))) (jf + jz + ℓ * k))
      = resMk π φ (Hf - u * k₁) (dev φ f (jf + ℓ * k₁))
          * resMk π φ (Hz - u * (k - k₁)) (dev φ z (jz + ℓ * (k - k₁))) := by
  have habs : (jf + ℓ * k₁) + (jz + ℓ * (k - k₁)) = jf + jz + ℓ * k := by
    have : ℓ * k₁ + ℓ * (k - k₁) = ℓ * k := by
      rw [← Nat.mul_add, Nat.add_sub_cancel' hk₁]
    omega
  have hdevterm : dev φ (dev φ f (jf + ℓ * k₁) * dev φ z (jz + ℓ * (k - k₁))
      * φ ^ ((jf + ℓ * k₁) + (jz + ℓ * (k - k₁)))) (jf + jz + ℓ * k)
      = (dev φ f (jf + ℓ * k₁) * dev φ z (jz + ℓ * (k - k₁))) %ₘ φ := by
    rw [habs]
    have h := dev_mul_pow hφ (jf + jz + ℓ * k)
      (dev φ f (jf + ℓ * k₁) * dev φ z (jz + ℓ * (k - k₁))) 0
    rw [Nat.add_zero] at h
    rw [h, dev]
  rw [hdevterm]
  have hheights : (Hf - u * k₁) + (Hz - u * (k - k₁)) = Hf + Hz - u * k := by
    have e3 : u * k₁ + u * (k - k₁) = u * k := by
      rw [← Nat.mul_add, Nat.add_sub_cancel' hk₁]
    omega
  have hbf : ((Hf - u * k₁ : ℕ) : ℕ∞) ≤ gaussVal (dev φ f (jf + ℓ * k₁)) :=
    le_gaussVal_dev_lattice hφ hd hℓ hSf k₁
  have hbz : ((Hz - u * (k - k₁) : ℕ) : ℕ∞) ≤ gaussVal (dev φ z (jz + ℓ * (k - k₁))) :=
    le_gaussVal_dev_lattice hφ hd hℓ hSz (k - k₁)
  have hmulval : ((Hf + Hz - u * k : ℕ) : ℕ∞)
      ≤ gaussVal (dev φ f (jf + ℓ * k₁) * dev φ z (jz + ℓ * (k - k₁))) := by
    rw [gaussVal_mul hπ, ← hheights]
    push_cast
    exact add_le_add hbf hbz
  rw [resMk_modByMonic hπ hφ hmulval, ← hheights, resMk_mul hπ hbf hbz]

end Estimates

/-! ## 4. Side bookkeeping: membership, the right endpoint's height -/

section SideData

variable {φ : Polynomial O} {u ℓ : ℕ}

/-- An on-side abscissa of a side of finite support value lies in `sideSet`. -/
theorem mem_sideSet_of_onSide (hφ : φ.Monic) (hd : 0 < φ.natDegree) (hℓ : 0 < ℓ)
    {f : Polynomial O} (htop : suppVal φ f u ℓ ≠ ⊤) {j : ℕ} (hj : OnSide φ f u ℓ j) :
    j ∈ sideSet φ f u ℓ := by
  classical
  have hne : npHgt φ f j ≠ ⊤ := npHgt_ne_top_of_onSide hℓ htop hj
  have hdev : dev φ f j ≠ 0 := fun h => hne (npHgt_eq_top_iff.2 h)
  have hle : j * φ.natDegree ≤ f.natDegree := by
    by_contra hcon
    exact hdev (dev_eq_zero_of_lt hφ hd f j (Nat.lt_of_not_le hcon))
  have hj' : j ≤ f.natDegree := le_trans (Nat.le_mul_of_pos_right j hd) hle
  show j ∈ Finset.filter (OnSide φ f u ℓ) (Finset.range (f.natDegree + 1))
  exact Finset.mem_filter.2 ⟨Finset.mem_range.2 (Nat.lt_succ_of_le hj'), hj⟩

/-- Every on-side abscissa is a lattice abscissa `sideMin + ℓ·k` with `k ≤ sideDeg`. -/
theorem onSide_lattice (hφ : φ.Monic) (hd : 0 < φ.natDegree) (hℓ : 0 < ℓ)
    (hcop : Nat.Coprime u ℓ) {f : Polynomial O} (htop : suppVal φ f u ℓ ≠ ⊤)
    (hnf : (sideSet φ f u ℓ).Nonempty) {j : ℕ} (hj : OnSide φ f u ℓ j) :
    ∃ k ≤ sideDeg φ f u ℓ hnf, j = sideMin φ f u ℓ hnf + ℓ * k :=
  onSide_eq_add_mul hℓ hcop htop hnf (mem_sideSet_of_onSide hφ hd hℓ htop hj)

/-- **The side descends by `u` per lattice step**: `u · sideDeg ≤ H₀`, the honest form of the
`ℕ`-subtraction `H₀ − u·k` for `k ≤ sideDeg`. -/
theorem u_mul_sideDeg_le (hℓ : 0 < ℓ) (hcop : Nat.Coprime u ℓ) {f : Polynomial O}
    (htop : suppVal φ f u ℓ ≠ ⊤) (hnf : (sideSet φ f u ℓ).Nonempty) {Hf : ℕ}
    (hHf : npHgt φ f (sideMin φ f u ℓ hnf) = (Hf : ℕ∞)) :
    u * sideDeg φ f u ℓ hnf ≤ Hf := by
  have hmax : sideMax φ f u ℓ hnf ∈ sideSet φ f u ℓ := Finset.max'_mem _ _
  have honmax := onSide_of_mem_sideSet hmax
  obtain ⟨Hd, hHd⟩ := ENat.ne_top_iff_exists.1 (npHgt_ne_top_of_onSide hℓ htop honmax)
  have honmin := onSide_of_mem_sideSet (Finset.min'_mem (sideSet φ f u ℓ) hnf)
  have hnat : ℓ * Hf + u * sideMin φ f u ℓ hnf = ℓ * Hd + u * sideMax φ f u ℓ hnf :=
    onSide_nat_eq hHf hHd.symm honmin honmax
  rw [sideMax_eq hℓ hcop htop hnf] at hnat
  have key : ℓ * Hf + u * sideMin φ f u ℓ hnf
      = ℓ * (Hd + u * sideDeg φ f u ℓ hnf) + u * sideMin φ f u ℓ hnf := by
    rw [hnat]; ring
  have hHf' : Hf = Hd + u * sideDeg φ f u ℓ hnf :=
    Nat.eq_of_mul_eq_mul_left hℓ (Nat.add_right_cancel key)
  omega

end SideData

/-! ## 5. The general master identity -/

/-- **The general master identity (the purity-free `resMk_dev_mul`).** For `f`, `z` with finite
support values at the slope `−u/ℓ`, the digit of `(f*z)`'s development at the lattice abscissa
`j_f + j_z + ℓ·k` and the line height `H_f + H_z − u·k` is the `k`-th coefficient of the product
of the two residual polynomials. -/
theorem resMk_dev_mul_gen (hπ : Irreducible π) {φ : Polynomial O} (hφ : φ.Monic)
    (hd : 0 < φ.natDegree) {u ℓ : ℕ} (hu : 0 < u) (hℓ : 0 < ℓ) (hcop : Nat.Coprime u ℓ)
    {f z : Polynomial O} (htf : suppVal φ f u ℓ ≠ ⊤) (htz : suppVal φ z u ℓ ≠ ⊤)
    (hnf : (sideSet φ f u ℓ).Nonempty) (hnz : (sideSet φ z u ℓ).Nonempty)
    {Hf Hz : ℕ} (hHf : npHgt φ f (sideMin φ f u ℓ hnf) = (Hf : ℕ∞))
    (hHz : npHgt φ z (sideMin φ z u ℓ hnz) = (Hz : ℕ∞))
    {k : ℕ} (hk : k ≤ sideDeg φ f u ℓ hnf + sideDeg φ z u ℓ hnz) :
    resMk π φ (Hf + Hz - u * k)
        (dev φ (f * z) (sideMin φ f u ℓ hnf + sideMin φ z u ℓ hnz + ℓ * k))
      = ∑ k₁ ∈ Finset.range (k + 1),
          (resPoly π φ f u ℓ hnf Hf).coeff k₁
            * (resPoly π φ z u ℓ hnz Hz).coeff (k - k₁) := by
  classical
  set jf := sideMin φ f u ℓ hnf with hjfdef
  set jz := sideMin φ z u ℓ hnz with hjzdef
  set df := sideDeg φ f u ℓ hnf with hdfdef
  set dz := sideDeg φ z u ℓ hnz with hdzdef
  -- the two weight identities, read at the sides' left endpoints
  have hSf : suppVal φ f u ℓ = ((ℓ * Hf + u * jf : ℕ) : ℕ∞) :=
    suppVal_eq_of_onSide hHf (onSide_of_mem_sideSet (Finset.min'_mem _ hnf))
  have hSz : suppVal φ z u ℓ = ((ℓ * Hz + u * jz : ℕ) : ℕ∞) :=
    suppVal_eq_of_onSide hHz (onSide_of_mem_sideSet (Finset.min'_mem _ hnz))
  have hudf : u * df ≤ Hf := u_mul_sideDeg_le hℓ hcop htf hnf hHf
  have hudz : u * dz ≤ Hz := u_mul_sideDeg_le hℓ hcop htz hnz hHz
  have hkH : u * k ≤ Hf + Hz := by
    calc u * k ≤ u * (df + dz) := Nat.mul_le_mul_left u hk
      _ = u * df + u * dz := by ring
      _ ≤ Hf + Hz := Nat.add_le_add hudf hudz
  -- Step 1: the double representation of the product
  set N := jf + jz + ℓ * k + f.natDegree + z.natDegree + 1 with hN
  have hfN : f.natDegree < N * φ.natDegree :=
    lt_of_lt_of_le (by omega) (Nat.le_mul_of_pos_right N hd)
  have hzN : z.natDegree < N * φ.natDegree :=
    lt_of_lt_of_le (by omega) (Nat.le_mul_of_pos_right N hd)
  have hfrep : ∑ j ∈ Finset.range N, dev φ f j * φ ^ j = f := sum_dev_eq hφ hd f hfN
  have hzrep : ∑ i ∈ Finset.range N, dev φ z i * φ ^ i = z := sum_dev_eq hφ hd z hzN
  have hrep : f * z = ∑ p ∈ Finset.range N ×ˢ Finset.range N,
      dev φ f p.1 * dev φ z p.2 * φ ^ (p.1 + p.2) := by
    have h1 : f * z = (∑ j ∈ Finset.range N, dev φ f j * φ ^ j)
        * (∑ i ∈ Finset.range N, dev φ z i * φ ^ i) := by rw [hfrep, hzrep]
    rw [h1, Finset.sum_mul_sum, Finset.sum_product]
    exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => by
      rw [pow_add]; ring
  -- Step 2: development and digit distribute over the double sum
  have hdev : dev φ (f * z) (jf + jz + ℓ * k)
      = ∑ p ∈ Finset.range N ×ˢ Finset.range N,
          dev φ (dev φ f p.1 * dev φ z p.2 * φ ^ (p.1 + p.2)) (jf + jz + ℓ * k) := by
    rw [hrep, dev_finsetSum hφ]
  have hval : ∀ p ∈ Finset.range N ×ˢ Finset.range N,
      ((Hf + Hz - u * k : ℕ) : ℕ∞)
        ≤ gaussVal (dev φ (dev φ f p.1 * dev φ z p.2 * φ ^ (p.1 + p.2)) (jf + jz + ℓ * k)) := by
    intro p _
    exact le_gaussVal_dev_term_gen hπ hφ hd hℓ hSf hSz k p.1 p.2
  rw [hdev, resMk_finsetSum hπ _ _ hval]
  -- Step 3: only the lattice pairs survive
  set G : Finset (ℕ × ℕ) :=
    (Finset.range (k + 1)).image (fun k₁ => ((jf + ℓ * k₁, jz + ℓ * (k - k₁)) : ℕ × ℕ)) with hG
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
      resMk π φ (Hf + Hz - u * k)
        (dev φ (dev φ f p.1 * dev φ z p.2 * φ ^ (p.1 + p.2)) (jf + jz + ℓ * k)) = 0 := by
    intro p _ hpG
    refine resMk_dev_term_eq_zero_gen hπ hφ hd hu hℓ hSf hSz hkH ?_
    rintro ⟨hsum, honf, honz⟩
    refine hpG ?_
    obtain ⟨k₁, hk₁df, hk₁eq⟩ := onSide_lattice hφ hd hℓ hcop htf hnf honf
    obtain ⟨k₂, hk₂dz, hk₂eq⟩ := onSide_lattice hφ hd hℓ hcop htz hnz honz
    have hsplit : ℓ * k₁ + ℓ * k₂ = ℓ * k := by omega
    have hk₁₂ : k₁ + k₂ = k := by
      refine Nat.eq_of_mul_eq_mul_left hℓ ?_
      rw [Nat.mul_add]; exact hsplit
    have hk₂ : k₂ = k - k₁ := by omega
    rw [hG, Finset.mem_image]
    refine ⟨k₁, Finset.mem_range.2 (by omega), ?_⟩
    rw [Prod.ext_iff]
    exact ⟨hk₁eq.symm, by rw [hk₂eq, hk₂]⟩
  rw [← Finset.sum_subset hGsub hvanish]
  -- Step 4: reindex and evaluate
  rw [hG, Finset.sum_image (by
    intro a _ b _ hab
    have h1 : jf + ℓ * a = jf + ℓ * b := (Prod.ext_iff.1 hab).1
    exact Nat.eq_of_mul_eq_mul_left hℓ (by omega))]
  refine Finset.sum_congr rfl fun k₁ hk₁ => ?_
  rw [Finset.mem_range] at hk₁
  have hk₁k : k₁ ≤ k := by omega
  rw [resPoly_coeff, resPoly_coeff]
  by_cases hcf : k₁ < df + 1
  · by_cases hcz : k - k₁ < dz + 1
    · rw [if_pos hcf, if_pos hcz]
      have hkf : u * k₁ ≤ Hf := le_trans (Nat.mul_le_mul_left u (by omega)) hudf
      have hkz : u * (k - k₁) ≤ Hz := le_trans (Nat.mul_le_mul_left u (by omega)) hudz
      exact resMk_dev_term_eq_mul_gen hπ hφ hd hℓ hSf hSz hk₁k hkf hkz
    · rw [if_neg hcz, mul_zero]
      refine resMk_dev_term_eq_zero_gen hπ hφ hd hu hℓ hSf hSz hkH ?_
      rintro ⟨_, _, honz⟩
      obtain ⟨k₂, hk₂dz, hk₂eq⟩ := onSide_lattice hφ hd hℓ hcop htz hnz honz
      have : k₂ = k - k₁ := Nat.eq_of_mul_eq_mul_left hℓ (by omega)
      omega
  · rw [if_neg hcf, zero_mul]
    refine resMk_dev_term_eq_zero_gen hπ hφ hd hu hℓ hSf hSz hkH ?_
    rintro ⟨_, honf, _⟩
    obtain ⟨k₂, hk₂df, hk₂eq⟩ := onSide_lattice hφ hd hℓ hcop htf hnf honf
    have : k₂ = k₁ := Nat.eq_of_mul_eq_mul_left hℓ (by omega)
    omega

/-! ## 6. The convolution estimates at an arbitrary line -/

section LineEstimates

variable {φ : Polynomial O} {u ℓ : ℕ} {f z : Polynomial O} {Sf Sz : ℕ}

/-- The convolution estimate at an arbitrary lattice point `(J, H)` of the line of weight
`S_f + S_z`. -/
theorem le_gaussVal_dev_mul_line (hπ : Irreducible π) (hφ : φ.Monic) (hd : 0 < φ.natDegree)
    (hℓ : 0 < ℓ) (hSf : suppVal φ f u ℓ = (Sf : ℕ∞)) (hSz : suppVal φ z u ℓ = (Sz : ℕ∞))
    {H J : ℕ} (hline : ℓ * H + u * J = Sf + Sz) {j i : ℕ} (hji : j + i ≤ J) :
    ((H : ℕ) : ℕ∞) ≤ gaussVal (dev φ f j * dev φ z i) := by
  rcases eq_or_ne (gaussVal (dev φ f j)) ⊤ with hfT | hfT
  · rw [gaussVal_eq_top_iff.1 hfT, zero_mul, gaussVal_eq_top_iff.2 rfl]; exact le_top
  rcases eq_or_ne (gaussVal (dev φ z i)) ⊤ with hzT | hzT
  · rw [gaussVal_eq_top_iff.1 hzT, mul_zero, gaussVal_eq_top_iff.2 rfl]; exact le_top
  obtain ⟨Hj, hHj⟩ := ENat.ne_top_iff_exists.1 hfT
  obtain ⟨Hi, hHi⟩ := ENat.ne_top_iff_exists.1 hzT
  have h1 : Sf ≤ ℓ * Hj + u * j := le_weight_gen hφ hd hℓ hSf hHj.symm
  have h2 : Sz ≤ ℓ * Hi + u * i := le_weight_gen hφ hd hℓ hSz hHi.symm
  have hui : u * (j + i) ≤ u * J := Nat.mul_le_mul_left u hji
  have hstep : ℓ * H + u * J ≤ ℓ * (Hj + Hi) + u * J := by
    calc ℓ * H + u * J = Sf + Sz := hline
      _ ≤ (ℓ * Hj + u * j) + (ℓ * Hi + u * i) := Nat.add_le_add h1 h2
      _ = ℓ * (Hj + Hi) + u * (j + i) := by ring
      _ ≤ ℓ * (Hj + Hi) + u * J := Nat.add_le_add_left hui _
  have h3 : H ≤ Hj + Hi :=
    Nat.le_of_mul_le_mul_left (Nat.le_of_add_le_add_right hstep) hℓ
  have hprod : gaussVal (dev φ f j * dev φ z i) = ((Hj + Hi : ℕ) : ℕ∞) := by
    rw [gaussVal_mul hπ, ← hHj, ← hHi]; push_cast; ring
  rw [hprod]
  exact_mod_cast h3

/-- The strict convolution estimate at an arbitrary lattice point of the line. -/
theorem lt_gaussVal_dev_mul_line (hπ : Irreducible π) (hφ : φ.Monic) (hd : 0 < φ.natDegree)
    (hu : 0 < u) (hℓ : 0 < ℓ) (hSf : suppVal φ f u ℓ = (Sf : ℕ∞))
    (hSz : suppVal φ z u ℓ = (Sz : ℕ∞))
    {H J : ℕ} (hline : ℓ * H + u * J = Sf + Sz) {j i : ℕ} (hji : j + i ≤ J)
    (hbad : j + i < J ∨ ¬ OnSide φ f u ℓ j ∨ ¬ OnSide φ z u ℓ i) :
    ((H + 1 : ℕ) : ℕ∞) ≤ gaussVal (dev φ f j * dev φ z i) := by
  rcases eq_or_ne (gaussVal (dev φ f j)) ⊤ with hfT | hfT
  · rw [gaussVal_eq_top_iff.1 hfT, zero_mul, gaussVal_eq_top_iff.2 rfl]; exact le_top
  rcases eq_or_ne (gaussVal (dev φ z i)) ⊤ with hzT | hzT
  · rw [gaussVal_eq_top_iff.1 hzT, mul_zero, gaussVal_eq_top_iff.2 rfl]; exact le_top
  obtain ⟨Hj, hHj⟩ := ENat.ne_top_iff_exists.1 hfT
  obtain ⟨Hi, hHi⟩ := ENat.ne_top_iff_exists.1 hzT
  have hstrict : ℓ * H + u * J < ℓ * (Hj + Hi) + u * J := by
    rcases hbad with hlt | hoff
    · have h1 : Sf ≤ ℓ * Hj + u * j := le_weight_gen hφ hd hℓ hSf hHj.symm
      have h2 : Sz ≤ ℓ * Hi + u * i := le_weight_gen hφ hd hℓ hSz hHi.symm
      have hui : u * (j + i) < u * J := mul_lt_mul_of_pos_left hlt hu
      calc ℓ * H + u * J = Sf + Sz := hline
        _ ≤ (ℓ * Hj + u * j) + (ℓ * Hi + u * i) := Nat.add_le_add h1 h2
        _ = ℓ * (Hj + Hi) + u * (j + i) := by ring
        _ < ℓ * (Hj + Hi) + u * J := Nat.add_lt_add_left hui _
    · have hsum : Sf + Sz < (ℓ * Hj + u * j) + (ℓ * Hi + u * i) := by
        rcases hoff with hnf | hnz
        · exact Nat.add_lt_add_of_lt_of_le (lt_weight_gen hφ hd hℓ hSf hHj.symm hnf)
            (le_weight_gen hφ hd hℓ hSz hHi.symm)
        · exact Nat.add_lt_add_of_le_of_lt (le_weight_gen hφ hd hℓ hSf hHj.symm)
            (lt_weight_gen hφ hd hℓ hSz hHi.symm hnz)
      have hui : u * (j + i) ≤ u * J := Nat.mul_le_mul_left u hji
      calc ℓ * H + u * J = Sf + Sz := hline
        _ < (ℓ * Hj + u * j) + (ℓ * Hi + u * i) := hsum
        _ = ℓ * (Hj + Hi) + u * (j + i) := by ring
        _ ≤ ℓ * (Hj + Hi) + u * J := Nat.add_le_add_left hui _
  have h3 : H < Hj + Hi :=
    Nat.lt_of_mul_lt_mul_left (Nat.lt_of_add_lt_add_right hstrict)
  have hprod : gaussVal (dev φ f j * dev φ z i) = ((Hj + Hi : ℕ) : ℕ∞) := by
    rw [gaussVal_mul hπ, ← hHj, ← hHi]; push_cast; ring
  rw [hprod]
  exact_mod_cast h3

/-- **The double representation of the product's digit at an arbitrary lattice point.** -/
theorem resMk_dev_mul_line (hπ : Irreducible π) (hφ : φ.Monic) (hd : 0 < φ.natDegree)
    (hℓ : 0 < ℓ) (hSf : suppVal φ f u ℓ = (Sf : ℕ∞)) (hSz : suppVal φ z u ℓ = (Sz : ℕ∞))
    {H J : ℕ} (hline : ℓ * H + u * J = Sf + Sz) {N : ℕ}
    (hfN : f.natDegree < N * φ.natDegree) (hzN : z.natDegree < N * φ.natDegree) :
    resMk π φ H (dev φ (f * z) J)
      = ∑ p ∈ Finset.range N ×ˢ Finset.range N,
          resMk π φ H (dev φ (dev φ f p.1 * dev φ z p.2 * φ ^ (p.1 + p.2)) J) := by
  classical
  have hfrep : ∑ j ∈ Finset.range N, dev φ f j * φ ^ j = f := sum_dev_eq hφ hd f hfN
  have hzrep : ∑ i ∈ Finset.range N, dev φ z i * φ ^ i = z := sum_dev_eq hφ hd z hzN
  have hrep : f * z = ∑ p ∈ Finset.range N ×ˢ Finset.range N,
      dev φ f p.1 * dev φ z p.2 * φ ^ (p.1 + p.2) := by
    have h1 : f * z = (∑ j ∈ Finset.range N, dev φ f j * φ ^ j)
        * (∑ i ∈ Finset.range N, dev φ z i * φ ^ i) := by rw [hfrep, hzrep]
    rw [h1, Finset.sum_mul_sum, Finset.sum_product]
    exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => by
      rw [pow_add]; ring
  have hval : ∀ p ∈ Finset.range N ×ˢ Finset.range N,
      ((H : ℕ) : ℕ∞)
        ≤ gaussVal (dev φ (dev φ f p.1 * dev φ z p.2 * φ ^ (p.1 + p.2)) J) := by
    intro p _
    rcases Nat.lt_or_ge J (p.1 + p.2) with hlt | hge
    · rw [dev_mul_pow_of_lt hφ (p.1 + p.2) _ J hlt, gaussVal_eq_top_iff.2 rfl]; exact le_top
    · obtain ⟨s, hs⟩ := Nat.exists_eq_add_of_le hge
      rw [hs, dev_mul_pow hφ (p.1 + p.2) _ s]
      exact le_trans (le_gaussVal_dev_mul_line hπ hφ hd hℓ hSf hSz hline hge)
        (gaussVal_le_npHgt hπ hφ _ s)
  rw [hrep, dev_finsetSum hφ, resMk_finsetSum hπ _ _ hval]

/-- **An on-side abscissa of a product decomposes into on-side abscissae of the factors.** -/
theorem onSide_mul_decomp (hπ : Irreducible π) {φ : Polynomial O} (hφ : IsKey φ)
    {u ℓ : ℕ} (hu : 0 < u) (hℓ : 0 < ℓ) {f z : Polynomial O} {Sf Sz : ℕ}
    (hSf : suppVal φ f u ℓ = (Sf : ℕ∞)) (hSz : suppVal φ z u ℓ = (Sz : ℕ∞))
    (hprod : suppVal φ (f * z) u ℓ = ((Sf + Sz : ℕ) : ℕ∞))
    {J : ℕ} (hon : OnSide φ (f * z) u ℓ J) :
    ∃ j i : ℕ, j + i = J ∧ OnSide φ f u ℓ j ∧ OnSide φ z u ℓ i := by
  classical
  by_contra hJ
  have htop : suppVal φ (f * z) u ℓ ≠ ⊤ := by rw [hprod]; exact ENat.coe_ne_top _
  obtain ⟨H, hH⟩ := ENat.ne_top_iff_exists.1 (npHgt_ne_top_of_onSide hℓ htop hon)
  have hnp : npHgt φ (f * z) J = (H : ℕ∞) := hH.symm
  have hline : ℓ * H + u * J = Sf + Sz := by
    have := suppVal_eq_of_onSide hnp hon
    rw [hprod] at this
    exact_mod_cast this.symm
  -- the digit at the on-side abscissa is nonzero
  have hdev : dev φ (f * z) J ≠ 0 := fun h => by
    rw [npHgt_eq_top_iff.2 h] at hnp; exact (ENat.coe_ne_top H) hnp.symm
  have hne : resMk π φ H (dev φ (f * z) J) ≠ 0 :=
    resMk_ne_zero hπ hφ (degree_dev_lt hφ.monic hφ.pos _ _) hdev hnp
  -- but every term of the double sum vanishes
  set N := J + f.natDegree + z.natDegree + 1 with hN
  have hfN : f.natDegree < N * φ.natDegree :=
    lt_of_lt_of_le (by omega) (Nat.le_mul_of_pos_right N hφ.pos)
  have hzN : z.natDegree < N * φ.natDegree :=
    lt_of_lt_of_le (by omega) (Nat.le_mul_of_pos_right N hφ.pos)
  rw [resMk_dev_mul_line hπ hφ.monic hφ.pos hℓ hSf hSz hline hfN hzN] at hne
  refine hne (Finset.sum_eq_zero fun p _ => ?_)
  rcases Nat.lt_or_ge J (p.1 + p.2) with hlt | hge
  · rw [dev_mul_pow_of_lt hφ.monic (p.1 + p.2) _ J hlt]
    exact resMk_of_zero hπ φ _
  · obtain ⟨s, hs⟩ := Nat.exists_eq_add_of_le hge
    have hbad : p.1 + p.2 < J ∨ ¬ OnSide φ f u ℓ p.1 ∨ ¬ OnSide φ z u ℓ p.2 := by
      rcases Nat.lt_or_ge (p.1 + p.2) J with h | h
      · exact Or.inl h
      · have heq : p.1 + p.2 = J := le_antisymm hge h
        by_cases h1 : OnSide φ f u ℓ p.1
        · by_cases h2 : OnSide φ z u ℓ p.2
          · exact absurd ⟨p.1, p.2, heq, h1, h2⟩ hJ
          · exact Or.inr (Or.inr h2)
        · exact Or.inr (Or.inl h1)
    have hstrict := lt_gaussVal_dev_mul_line hπ hφ.monic hφ.pos hu hℓ hSf hSz hline hge hbad
    rw [hs, dev_mul_pow hφ.monic (p.1 + p.2) _ s]
    exact resMk_eq_zero_of_lt hπ (le_trans hstrict (gaussVal_le_npHgt hπ hφ.monic _ s))

/-- A nonvanishing digit at a lattice point of the side's line puts that abscissa on the
side. -/
theorem onSide_of_resMk_ne_zero (hπ : Irreducible π) (hφ : φ.Monic) (hd : 0 < φ.natDegree)
    (hℓ : 0 < ℓ) {S H J : ℕ} (hS : suppVal φ f u ℓ = (S : ℕ∞)) (hline : ℓ * H + u * J = S)
    (hne : resMk π φ H (dev φ f J) ≠ 0) : OnSide φ f u ℓ J := by
  have hnple : npHgt φ f J ≤ (H : ℕ∞) := by
    by_contra hcon
    rw [not_le] at hcon
    refine hne (resMk_eq_zero_of_lt hπ ?_)
    have h1 : (H : ℕ∞) + 1 ≤ npHgt φ f J := Order.add_one_le_of_lt hcon
    calc ((H + 1 : ℕ) : ℕ∞) = (H : ℕ∞) + 1 := by push_cast; ring
      _ ≤ npHgt φ f J := h1
  obtain ⟨V, hV⟩ := ENat.ne_top_iff_exists.1 (ne_top_of_le_ne_top (ENat.coe_ne_top H) hnple)
  have hVle : V ≤ H := by rw [← hV] at hnple; exact_mod_cast hnple
  have hmul : ℓ * V ≤ ℓ * H := Nat.mul_le_mul_left ℓ hVle
  have hupper : ℓ • npHgt φ f J + ((u * J : ℕ) : ℕ∞) ≤ suppVal φ f u ℓ := by
    rw [← hV, nsmul_add_cast_gen, hS]
    exact_mod_cast (by omega : ℓ * V + u * J ≤ S)
  exact le_antisymm hupper (suppVal_le_weight hφ hd hℓ u f J)

end LineEstimates

/-! ## 7. The general product law -/

section ProductLaw

variable {φ : Polynomial O} {u ℓ : ℕ} {f z : Polynomial O}

/-- The digit at the left endpoint of the product's side is nonzero: the product of the two
factors' nonzero residual constant terms, in the field `resField φ`. -/
theorem resMk_dev_mul_left_ne_zero (hπ : Irreducible π) (hφ : IsKey φ) (hu : 0 < u)
    (hℓ : 0 < ℓ) (hcop : Nat.Coprime u ℓ) (htf : suppVal φ f u ℓ ≠ ⊤)
    (htz : suppVal φ z u ℓ ≠ ⊤) (hnf : (sideSet φ f u ℓ).Nonempty)
    (hnz : (sideSet φ z u ℓ).Nonempty) {Hf Hz : ℕ}
    (hHf : npHgt φ f (sideMin φ f u ℓ hnf) = (Hf : ℕ∞))
    (hHz : npHgt φ z (sideMin φ z u ℓ hnz) = (Hz : ℕ∞)) :
    resMk π φ (Hf + Hz)
      (dev φ (f * z) (sideMin φ f u ℓ hnf + sideMin φ z u ℓ hnz)) ≠ 0 := by
  classical
  letI : Field (resField φ) := instFieldResField hφ
  have hmaster := resMk_dev_mul_gen hπ hφ.monic hφ.pos hu hℓ hcop htf htz hnf hnz hHf hHz
    (k := 0) (Nat.zero_le _)
  simp only [Nat.mul_zero, Nat.sub_zero, Nat.add_zero, Nat.zero_add,
    Finset.sum_range_one] at hmaster
  rw [hmaster]
  exact mul_ne_zero (natDegree_resPoly hπ hφ hℓ hcop htf hnf hHf).2
    (natDegree_resPoly hπ hφ hℓ hcop htz hnz hHz).2

/-- **The product's height at the left endpoint of its side is `H_f + H_z`.** -/
theorem npHgt_mul_gen (hπ : Irreducible π) (hφ : IsKey φ) (hu : 0 < u)
    (hℓ : 0 < ℓ) (hcop : Nat.Coprime u ℓ) (htf : suppVal φ f u ℓ ≠ ⊤)
    (htz : suppVal φ z u ℓ ≠ ⊤) (hnf : (sideSet φ f u ℓ).Nonempty)
    (hnz : (sideSet φ z u ℓ).Nonempty) {Hf Hz : ℕ}
    (hHf : npHgt φ f (sideMin φ f u ℓ hnf) = (Hf : ℕ∞))
    (hHz : npHgt φ z (sideMin φ z u ℓ hnz) = (Hz : ℕ∞)) :
    npHgt φ (f * z) (sideMin φ f u ℓ hnf + sideMin φ z u ℓ hnz) = ((Hf + Hz : ℕ) : ℕ∞) := by
  set jf := sideMin φ f u ℓ hnf with hjf
  set jz := sideMin φ z u ℓ hnz with hjz
  have hSf : suppVal φ f u ℓ = ((ℓ * Hf + u * jf : ℕ) : ℕ∞) :=
    suppVal_eq_of_onSide hHf (onSide_of_mem_sideSet (Finset.min'_mem _ hnf))
  have hSz : suppVal φ z u ℓ = ((ℓ * Hz + u * jz : ℕ) : ℕ∞) :=
    suppVal_eq_of_onSide hHz (onSide_of_mem_sideSet (Finset.min'_mem _ hnz))
  have hne := resMk_dev_mul_left_ne_zero hπ hφ hu hℓ hcop htf htz hnf hnz hHf hHz
  have hle : npHgt φ (f * z) (jf + jz) ≤ ((Hf + Hz : ℕ) : ℕ∞) := by
    by_contra hcon
    rw [not_le] at hcon
    refine hne (resMk_eq_zero_of_lt hπ ?_)
    have h1 : ((Hf + Hz : ℕ) : ℕ∞) + 1 ≤ npHgt φ (f * z) (jf + jz) := Order.add_one_le_of_lt hcon
    calc ((Hf + Hz + 1 : ℕ) : ℕ∞) = ((Hf + Hz : ℕ) : ℕ∞) + 1 := by push_cast; ring
      _ ≤ npHgt φ (f * z) (jf + jz) := h1
  obtain ⟨V, hV⟩ := ENat.ne_top_iff_exists.1 (ne_top_of_le_ne_top (ENat.coe_ne_top _) hle)
  have hVle : V ≤ Hf + Hz := by rw [← hV] at hle; exact_mod_cast hle
  have hge : ((ℓ * Hf + u * jf : ℕ) : ℕ∞) + ((ℓ * Hz + u * jz : ℕ) : ℕ∞)
      ≤ suppVal φ (f * z) u ℓ := by
    rw [← hSf, ← hSz]
    exact suppVal_add_le_suppVal_mul hπ hφ.monic hφ.pos hℓ u f z
  have hw : suppVal φ (f * z) u ℓ ≤ ℓ • npHgt φ (f * z) (jf + jz) + ((u * (jf + jz) : ℕ) : ℕ∞) :=
    suppVal_le_weight hφ.monic hφ.pos hℓ u (f * z) (jf + jz)
  rw [← hV, nsmul_add_cast_gen] at hw
  have hchain : ((ℓ * Hf + u * jf + (ℓ * Hz + u * jz) : ℕ) : ℕ∞)
      ≤ ((ℓ * V + u * (jf + jz) : ℕ) : ℕ∞) := by
    refine le_trans ?_ (le_trans hge hw)
    push_cast
    ring_nf
    exact le_rfl
  have hnat : ℓ * Hf + u * jf + (ℓ * Hz + u * jz) ≤ ℓ * V + u * (jf + jz) := by
    exact_mod_cast hchain
  have hVge : Hf + Hz ≤ V := by
    refine Nat.le_of_mul_le_mul_left ?_ hℓ
    have hexp : ℓ * Hf + u * jf + (ℓ * Hz + u * jz) = ℓ * (Hf + Hz) + u * (jf + jz) := by ring
    omega
  rw [← hV]
  exact_mod_cast (by omega : V = Hf + Hz)

/-- **`suppVal` is additive on products** (the general product law, clause 1). -/
theorem suppVal_mul_gen (hπ : Irreducible π) (hφ : IsKey φ) (hu : 0 < u)
    (hℓ : 0 < ℓ) (hcop : Nat.Coprime u ℓ) (htf : suppVal φ f u ℓ ≠ ⊤)
    (htz : suppVal φ z u ℓ ≠ ⊤) (hnf : (sideSet φ f u ℓ).Nonempty)
    (hnz : (sideSet φ z u ℓ).Nonempty) {Hf Hz : ℕ}
    (hHf : npHgt φ f (sideMin φ f u ℓ hnf) = (Hf : ℕ∞))
    (hHz : npHgt φ z (sideMin φ z u ℓ hnz) = (Hz : ℕ∞)) :
    suppVal φ (f * z) u ℓ
      = ((ℓ * (Hf + Hz) + u * (sideMin φ f u ℓ hnf + sideMin φ z u ℓ hnz) : ℕ) : ℕ∞) := by
  set jf := sideMin φ f u ℓ hnf with hjf
  set jz := sideMin φ z u ℓ hnz with hjz
  have hSf : suppVal φ f u ℓ = ((ℓ * Hf + u * jf : ℕ) : ℕ∞) :=
    suppVal_eq_of_onSide hHf (onSide_of_mem_sideSet (Finset.min'_mem _ hnf))
  have hSz : suppVal φ z u ℓ = ((ℓ * Hz + u * jz : ℕ) : ℕ∞) :=
    suppVal_eq_of_onSide hHz (onSide_of_mem_sideSet (Finset.min'_mem _ hnz))
  have hnp := npHgt_mul_gen hπ hφ hu hℓ hcop htf htz hnf hnz hHf hHz
  have hge : ((ℓ * Hf + u * jf : ℕ) : ℕ∞) + ((ℓ * Hz + u * jz : ℕ) : ℕ∞)
      ≤ suppVal φ (f * z) u ℓ := by
    rw [← hSf, ← hSz]
    exact suppVal_add_le_suppVal_mul hπ hφ.monic hφ.pos hℓ u f z
  have hw : suppVal φ (f * z) u ℓ ≤ ℓ • npHgt φ (f * z) (jf + jz) + ((u * (jf + jz) : ℕ) : ℕ∞) :=
    suppVal_le_weight hφ.monic hφ.pos hℓ u (f * z) (jf + jz)
  rw [hnp, nsmul_add_cast_gen] at hw
  refine le_antisymm hw (le_trans ?_ hge)
  push_cast
  ring_nf
  exact le_rfl

/-- **The left endpoints of the sides add** (the general product law, clause 2). -/
theorem sideMin_mul_gen (hπ : Irreducible π) (hφ : IsKey φ) (hu : 0 < u)
    (hℓ : 0 < ℓ) (hcop : Nat.Coprime u ℓ) (htf : suppVal φ f u ℓ ≠ ⊤)
    (htz : suppVal φ z u ℓ ≠ ⊤) (hnf : (sideSet φ f u ℓ).Nonempty)
    (hnz : (sideSet φ z u ℓ).Nonempty) {Hf Hz : ℕ}
    (hHf : npHgt φ f (sideMin φ f u ℓ hnf) = (Hf : ℕ∞))
    (hHz : npHgt φ z (sideMin φ z u ℓ hnz) = (Hz : ℕ∞))
    (hnfz : (sideSet φ (f * z) u ℓ).Nonempty) :
    sideMin φ (f * z) u ℓ hnfz = sideMin φ f u ℓ hnf + sideMin φ z u ℓ hnz := by
  set jf := sideMin φ f u ℓ hnf with hjf
  set jz := sideMin φ z u ℓ hnz with hjz
  have hSf : suppVal φ f u ℓ = ((ℓ * Hf + u * jf : ℕ) : ℕ∞) :=
    suppVal_eq_of_onSide hHf (onSide_of_mem_sideSet (Finset.min'_mem _ hnf))
  have hSz : suppVal φ z u ℓ = ((ℓ * Hz + u * jz : ℕ) : ℕ∞) :=
    suppVal_eq_of_onSide hHz (onSide_of_mem_sideSet (Finset.min'_mem _ hnz))
  have hprodval := suppVal_mul_gen hπ hφ hu hℓ hcop htf htz hnf hnz hHf hHz
  have hprod' : suppVal φ (f * z) u ℓ
      = (((ℓ * Hf + u * jf) + (ℓ * Hz + u * jz) : ℕ) : ℕ∞) := by
    rw [hprodval]; congr 1; ring
  have hnp := npHgt_mul_gen hπ hφ hu hℓ hcop htf htz hnf hnz hHf hHz
  have honfz : OnSide φ (f * z) u ℓ (jf + jz) := by
    show ℓ • npHgt φ (f * z) (jf + jz) + ((u * (jf + jz) : ℕ) : ℕ∞) = suppVal φ (f * z) u ℓ
    rw [hnp, nsmul_add_cast_gen, hprodval]
  refine le_antisymm ?_ ?_
  · exact Finset.min'_le _ _ (mem_sideSet_of_onSide hφ.monic hφ.pos hℓ
      (by rw [hprodval]; exact ENat.coe_ne_top _) honfz)
  · have hmem : sideMin φ (f * z) u ℓ hnfz ∈ sideSet φ (f * z) u ℓ := Finset.min'_mem _ _
    obtain ⟨j, i, hji, honj, honi⟩ := onSide_mul_decomp hπ hφ hu hℓ hSf hSz hprod'
      (onSide_of_mem_sideSet hmem)
    have h1 : jf ≤ j := Finset.min'_le _ _ (mem_sideSet_of_onSide hφ.monic hφ.pos hℓ htf honj)
    have h2 : jz ≤ i := Finset.min'_le _ _ (mem_sideSet_of_onSide hφ.monic hφ.pos hℓ htz honi)
    omega

/-- **The residual degrees add** (the general product law, clause 3). -/
theorem sideDeg_mul_gen (hπ : Irreducible π) (hφ : IsKey φ) (hu : 0 < u)
    (hℓ : 0 < ℓ) (hcop : Nat.Coprime u ℓ) (htf : suppVal φ f u ℓ ≠ ⊤)
    (htz : suppVal φ z u ℓ ≠ ⊤) (hnf : (sideSet φ f u ℓ).Nonempty)
    (hnz : (sideSet φ z u ℓ).Nonempty) {Hf Hz : ℕ}
    (hHf : npHgt φ f (sideMin φ f u ℓ hnf) = (Hf : ℕ∞))
    (hHz : npHgt φ z (sideMin φ z u ℓ hnz) = (Hz : ℕ∞))
    (hnfz : (sideSet φ (f * z) u ℓ).Nonempty) :
    sideDeg φ (f * z) u ℓ hnfz = sideDeg φ f u ℓ hnf + sideDeg φ z u ℓ hnz := by
  classical
  letI : Field (resField φ) := instFieldResField hφ
  set jf := sideMin φ f u ℓ hnf with hjf
  set jz := sideMin φ z u ℓ hnz with hjz
  set df := sideDeg φ f u ℓ hnf with hdf
  set dz := sideDeg φ z u ℓ hnz with hdz
  have hSf : suppVal φ f u ℓ = ((ℓ * Hf + u * jf : ℕ) : ℕ∞) :=
    suppVal_eq_of_onSide hHf (onSide_of_mem_sideSet (Finset.min'_mem _ hnf))
  have hSz : suppVal φ z u ℓ = ((ℓ * Hz + u * jz : ℕ) : ℕ∞) :=
    suppVal_eq_of_onSide hHz (onSide_of_mem_sideSet (Finset.min'_mem _ hnz))
  have hprodval := suppVal_mul_gen hπ hφ hu hℓ hcop htf htz hnf hnz hHf hHz
  have hprod' : suppVal φ (f * z) u ℓ
      = (((ℓ * Hf + u * jf) + (ℓ * Hz + u * jz) : ℕ) : ℕ∞) := by
    rw [hprodval]; congr 1; ring
  have htfz : suppVal φ (f * z) u ℓ ≠ ⊤ := by rw [hprodval]; exact ENat.coe_ne_top _
  have hminfz : sideMin φ (f * z) u ℓ hnfz = jf + jz :=
    sideMin_mul_gen hπ hφ hu hℓ hcop htf htz hnf hnz hHf hHz hnfz
  have hmaxfz : sideMax φ (f * z) u ℓ hnfz = jf + jz + ℓ * sideDeg φ (f * z) u ℓ hnfz := by
    rw [sideMax_eq hℓ hcop htfz hnfz, hminfz]
  have hudf : u * df ≤ Hf := u_mul_sideDeg_le hℓ hcop htf hnf hHf
  have hudz : u * dz ≤ Hz := u_mul_sideDeg_le hℓ hcop htz hnz hHz
  have hD : u * (df + dz) ≤ Hf + Hz := by
    calc u * (df + dz) = u * df + u * dz := by ring
      _ ≤ Hf + Hz := Nat.add_le_add hudf hudz
  -- upper bound: the product's right endpoint splits
  have hupper : sideDeg φ (f * z) u ℓ hnfz ≤ df + dz := by
    obtain ⟨j, i, hji, honj, honi⟩ := onSide_mul_decomp hπ hφ hu hℓ hSf hSz hprod'
      (onSide_of_mem_sideSet (Finset.max'_mem _ hnfz))
    have hji' : j + i = sideMax φ (f * z) u ℓ hnfz := hji
    have h1 : j ≤ jf + ℓ * df := by
      have hj : j ≤ sideMax φ f u ℓ hnf :=
        Finset.le_max' _ j (mem_sideSet_of_onSide hφ.monic hφ.pos hℓ htf honj)
      rwa [sideMax_eq hℓ hcop htf hnf] at hj
    have h2 : i ≤ jz + ℓ * dz := by
      have hi : i ≤ sideMax φ z u ℓ hnz :=
        Finset.le_max' _ i (mem_sideSet_of_onSide hφ.monic hφ.pos hℓ htz honi)
      rwa [sideMax_eq hℓ hcop htz hnz] at hi
    have hbig : ℓ * sideDeg φ (f * z) u ℓ hnfz ≤ ℓ * (df + dz) := by
      have hexp : ℓ * (df + dz) = ℓ * df + ℓ * dz := by ring
      omega
    exact Nat.le_of_mul_le_mul_left hbig hℓ
  -- lower bound: the top lattice abscissa carries a nonzero digit
  have hlower : df + dz ≤ sideDeg φ (f * z) u ℓ hnfz := by
    have hmaster := resMk_dev_mul_gen hπ hφ.monic hφ.pos hu hℓ hcop htf htz hnf hnz hHf hHz
      (k := df + dz) le_rfl
    have hsingle : ∑ k₁ ∈ Finset.range (df + dz + 1),
        (resPoly π φ f u ℓ hnf Hf).coeff k₁ * (resPoly π φ z u ℓ hnz Hz).coeff (df + dz - k₁)
        = (resPoly π φ f u ℓ hnf Hf).coeff df * (resPoly π φ z u ℓ hnz Hz).coeff dz := by
      rw [Finset.sum_eq_single_of_mem df (Finset.mem_range.2 (by omega)) ?_]
      · rw [Nat.add_sub_cancel_left]
      · intro b hb hbne
        rw [Finset.mem_range] at hb
        rcases Nat.lt_or_ge df b with hlt | hge
        · rw [show (resPoly π φ f u ℓ hnf Hf).coeff b = 0 from
            Polynomial.coeff_eq_zero_of_natDegree_lt
              (by rw [(natDegree_resPoly hπ hφ hℓ hcop htf hnf hHf).1]; exact hlt), zero_mul]
        · rw [show (resPoly π φ z u ℓ hnz Hz).coeff (df + dz - b) = 0 from
            Polynomial.coeff_eq_zero_of_natDegree_lt
              (by rw [(natDegree_resPoly hπ hφ hℓ hcop htz hnz hHz).1]; omega), mul_zero]
    rw [hsingle] at hmaster
    have hFne : resPoly π φ f u ℓ hnf Hf ≠ 0 := fun h0 => by
      simpa [h0] using (natDegree_resPoly hπ hφ hℓ hcop htf hnf hHf).2
    have hZne : resPoly π φ z u ℓ hnz Hz ≠ 0 := fun h0 => by
      simpa [h0] using (natDegree_resPoly hπ hφ hℓ hcop htz hnz hHz).2
    have hFdeg : (resPoly π φ f u ℓ hnf Hf).natDegree = df :=
      (natDegree_resPoly hπ hφ hℓ hcop htf hnf hHf).1
    have hZdeg : (resPoly π φ z u ℓ hnz Hz).natDegree = dz :=
      (natDegree_resPoly hπ hφ hℓ hcop htz hnz hHz).1
    have hlead : (resPoly π φ f u ℓ hnf Hf).coeff df * (resPoly π φ z u ℓ hnz Hz).coeff dz ≠ 0 := by
      refine mul_ne_zero ?_ ?_
      · rw [← hFdeg]; exact Polynomial.leadingCoeff_ne_zero.2 hFne
      · rw [← hZdeg]; exact Polynomial.leadingCoeff_ne_zero.2 hZne
    have hne : resMk π φ (Hf + Hz - u * (df + dz))
        (dev φ (f * z) (jf + jz + ℓ * (df + dz))) ≠ 0 := by rw [hmaster]; exact hlead
    have hline : ℓ * (Hf + Hz - u * (df + dz)) + u * (jf + jz + ℓ * (df + dz))
        = ℓ * (Hf + Hz) + u * (jf + jz) := by
      obtain ⟨W, hW⟩ := Nat.exists_eq_add_of_le hD
      rw [hW, Nat.add_sub_cancel_left]
      ring
    have honfz := onSide_of_resMk_ne_zero hπ hφ.monic hφ.pos hℓ hprodval hline hne
    have hmem := mem_sideSet_of_onSide hφ.monic hφ.pos hℓ htfz honfz
    have hle : jf + jz + ℓ * (df + dz) ≤ sideMax φ (f * z) u ℓ hnfz :=
      Finset.le_max' _ _ hmem
    rw [hmaxfz] at hle
    have hbig : ℓ * (df + dz) ≤ ℓ * sideDeg φ (f * z) u ℓ hnfz := by omega
    exact Nat.le_of_mul_le_mul_left hbig hℓ
  omega

/-- **`resPoly` is multiplicative** (the general product law, clause 4). -/
theorem resPoly_mul_gen (hπ : Irreducible π) (hφ : IsKey φ) (hu : 0 < u)
    (hℓ : 0 < ℓ) (hcop : Nat.Coprime u ℓ) (htf : suppVal φ f u ℓ ≠ ⊤)
    (htz : suppVal φ z u ℓ ≠ ⊤) (hnf : (sideSet φ f u ℓ).Nonempty)
    (hnz : (sideSet φ z u ℓ).Nonempty) {Hf Hz : ℕ}
    (hHf : npHgt φ f (sideMin φ f u ℓ hnf) = (Hf : ℕ∞))
    (hHz : npHgt φ z (sideMin φ z u ℓ hnz) = (Hz : ℕ∞))
    (hnfz : (sideSet φ (f * z) u ℓ).Nonempty) :
    resPoly π φ (f * z) u ℓ hnfz (Hf + Hz)
      = resPoly π φ f u ℓ hnf Hf * resPoly π φ z u ℓ hnz Hz := by
  classical
  letI : Field (resField φ) := instFieldResField hφ
  set jf := sideMin φ f u ℓ hnf with hjf
  set jz := sideMin φ z u ℓ hnz with hjz
  set df := sideDeg φ f u ℓ hnf with hdf
  set dz := sideDeg φ z u ℓ hnz with hdz
  have hminfz : sideMin φ (f * z) u ℓ hnfz = jf + jz :=
    sideMin_mul_gen hπ hφ hu hℓ hcop htf htz hnf hnz hHf hHz hnfz
  have hdegfz : sideDeg φ (f * z) u ℓ hnfz = df + dz :=
    sideDeg_mul_gen hπ hφ hu hℓ hcop htf htz hnf hnz hHf hHz hnfz
  have hFne : resPoly π φ f u ℓ hnf Hf ≠ 0 := fun h0 => by
    simpa [h0] using (natDegree_resPoly hπ hφ hℓ hcop htf hnf hHf).2
  have hZne : resPoly π φ z u ℓ hnz Hz ≠ 0 := fun h0 => by
    simpa [h0] using (natDegree_resPoly hπ hφ hℓ hcop htz hnz hHz).2
  have hprodDeg : (resPoly π φ f u ℓ hnf Hf * resPoly π φ z u ℓ hnz Hz).natDegree = df + dz := by
    rw [Polynomial.natDegree_mul hFne hZne,
      (natDegree_resPoly hπ hφ hℓ hcop htf hnf hHf).1,
      (natDegree_resPoly hπ hφ hℓ hcop htz hnz hHz).1]
  refine Polynomial.ext fun i => ?_
  rw [resPoly_coeff, hdegfz]
  by_cases hi : i < df + dz + 1
  · rw [if_pos hi]
    have hmaster := resMk_dev_mul_gen hπ hφ.monic hφ.pos hu hℓ hcop htf htz hnf hnz hHf hHz
      (k := i) (by omega)
    calc resCoeff π φ (f * z) u ℓ hnfz (Hf + Hz) i
        = resMk π φ (Hf + Hz - u * i) (dev φ (f * z) (jf + jz + ℓ * i)) := by
          rw [resCoeff, hminfz]
      _ = ∑ k₁ ∈ Finset.range (i + 1),
            (resPoly π φ f u ℓ hnf Hf).coeff k₁
              * (resPoly π φ z u ℓ hnz Hz).coeff (i - k₁) := hmaster
      _ = (resPoly π φ f u ℓ hnf Hf * resPoly π φ z u ℓ hnz Hz).coeff i := by
          rw [Polynomial.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  · rw [if_neg hi]
    exact (Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [hprodDeg]; omega)).symm

end ProductLaw

end Uniformity.Density.Leaf

/-! ## Axiom footprint -/

section AxCheck
#print axioms Uniformity.Density.Leaf.suppVal_eq_of_onSide
#print axioms Uniformity.Density.Leaf.le_weight_gen
#print axioms Uniformity.Density.Leaf.lt_weight_gen
#print axioms Uniformity.Density.Leaf.le_gaussVal_dev_lattice
#print axioms Uniformity.Density.Leaf.resPoly_coeff
#print axioms Uniformity.Density.Leaf.le_gaussVal_dev_mul_gen
#print axioms Uniformity.Density.Leaf.lt_gaussVal_dev_mul_gen
#print axioms Uniformity.Density.Leaf.le_gaussVal_dev_term_gen
#print axioms Uniformity.Density.Leaf.resMk_dev_term_eq_zero_gen
#print axioms Uniformity.Density.Leaf.resMk_dev_term_eq_mul_gen
#print axioms Uniformity.Density.Leaf.mem_sideSet_of_onSide
#print axioms Uniformity.Density.Leaf.onSide_lattice
#print axioms Uniformity.Density.Leaf.u_mul_sideDeg_le
#print axioms Uniformity.Density.Leaf.resMk_dev_mul_gen
#print axioms Uniformity.Density.Leaf.le_gaussVal_dev_mul_line
#print axioms Uniformity.Density.Leaf.lt_gaussVal_dev_mul_line
#print axioms Uniformity.Density.Leaf.resMk_dev_mul_line
#print axioms Uniformity.Density.Leaf.onSide_mul_decomp
#print axioms Uniformity.Density.Leaf.onSide_of_resMk_ne_zero
#print axioms Uniformity.Density.Leaf.resMk_dev_mul_left_ne_zero
#print axioms Uniformity.Density.Leaf.npHgt_mul_gen
#print axioms Uniformity.Density.Leaf.suppVal_mul_gen
#print axioms Uniformity.Density.Leaf.sideMin_mul_gen
#print axioms Uniformity.Density.Leaf.sideDeg_mul_gen
#print axioms Uniformity.Density.Leaf.resPoly_mul_gen
end AxCheck
