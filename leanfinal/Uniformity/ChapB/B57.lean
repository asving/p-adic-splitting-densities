/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapB.B35d

/-!
# Uniformity.ChapB.B57 — every monic factor of a pure polynomial is pure

**Chapter B, NODE B.57** [lemma] (`blueprint/CHAP-B_leaf_layer.md` §7, the leaf layer), ENV-C.
One signed declaration, `isPure_of_monic_factor`, at the **[repaired: A-F.6]** signature.

*Every monic factor of a pure polynomial is pure of the same slope, with additive residual
degree.* For `φ` an order-1 key, `0 < u`, `0 < ℓ`, `u` coprime to `ℓ`, and `g` monic
`(u,ℓ)`-pure whose degree is divisible by `m = φ.natDegree`: if `g = g₁ * g₂` with `g₁`, `g₂`
monic then both factors are `(u,ℓ)`-pure, their residual degrees add to `sideDeg g`, and
`ḡ₁ = φ̄ ^ (ℓ · sideDeg g₁)`.

## Route note: the blueprint's step-1 squeeze does not close, and what replaces it

The signed PROOF's step 1 proposes to get purity of the factors from B.33 (superadditivity,
`suppVal f + suppVal g ≤ suppVal (f*g)`) together with B.18's terminal-point bound
(`suppVal g₁ ≤ u·n₁`) — "a two-line squeeze". **Those two inequalities point the same way.**
Both bound the factors' polygon data from *above*, and purity of a factor is a statement that its
polygon lies *above* the `(u,ℓ)`-line; no combination of upper bounds can force it. Concretely,
`ℓ·h₀(g₁) + ℓ·h₀(g₂) = ℓ·h₀(g) = u·n` (height additivity at abscissa `0`) together with
`suppVal gᵢ ≤ min (ℓ·hᵢ₀) (u·nᵢ)` is satisfied by `g₁ = X + a`, `g₂ = X + b` with `v(a) = 0`,
`v(b) = 2` at `φ = X`, `u = ℓ = 1` — a *non-pure* factor pair. What excludes it is the height of
the product at the *middle* abscissa, i.e. the missing half of the product law.

So this file proves that missing half first, in general (no purity anywhere):

* `npHgt_mul_of_corner` — **no cancellation at a strict corner.** If the pair `(i₀, j₀)` strictly
  minimises `gaussVal (dev φ f i · dev φ g j)` among all pairs with `i + j ≤ i₀ + j₀`, then the
  product's height at `i₀ + j₀` is exactly `npHgt φ f i₀ + npHgt φ g j₀`. The proof expands
  `f*g = ∑ dev φ f i · dev φ g j · φ^(i+j)` (B.05 twice, as in B.35), applies the height-`A+B`
  digit `resMk` term by term (B35a), and observes that the corner term survives —
  `resMk_modByMonic` erases its `φ`-carry, `resMk_mul` splits it, and B.36's exactness clause
  makes each half nonzero in the *field* `resField φ` — while every other term is killed by
  `resMk_eq_zero_of_lt`. **No purity, no `hu`, no `hcop`.**
* `npHgt_zero_mul` — height additivity at abscissa `0`: the corner lemma at `i₀ = j₀ = 0`, where
  the strictness hypothesis is vacuous (no pair other than `(0,0)` has `i + j ≤ 0`) and the
  degenerate branch `φ ∣ f` is handled directly.
* `suppVal_mul_le` — **the hard half of the product law, unconditionally.** Take `i₀`, `j₀` the
  two `sideMin`s. Then `(i₀, j₀)` *is* a strict corner: a pair with `i + j = i₀ + j₀` other than
  `(i₀,j₀)` has one coordinate strictly left of that factor's `sideMin`, hence off its side, hence
  weight `≥ W + 1`; and a pair with `i + j < i₀ + j₀` pays the carry gap `u ≥ 1` (this is where
  `0 < u` enters, exactly as in B.35). Reading the product's weight at `i₀ + j₀` gives
  `suppVal (f*g) ≤ suppVal f + suppVal g`; with B.33 this is an equality, for *arbitrary*
  `f`, `g` of finite support value.

With that, B.57 is short: `suppVal g₁ = u·n₁` and `suppVal g₂ = u·n₂` are forced by
`u·n = suppVal g ≤ suppVal g₁ + suppVal g₂ ≤ u·n₁ + u·n₂`, which puts each factor's terminal
point on its side, and `npHgt_zero_mul` plus purity of `g` at abscissa `0` puts each factor's
abscissa-`0` point on its side.

## The A-F.6 hypothesis `hgd`

`(hgd : φ.natDegree ∣ g.natDegree)` is load-bearing and its absence is what refuted the frozen
form (`g = X = X * 1` at `φ = X²+1` over `ℤ₃`, `u = ℓ = 1`: the residue clause forces
`X̄ = φ̄⁰ = 1`). It enters through PROOF step 0, `map_residue_eq_key_pow_of_pure`: purity plus
`hgd` make every development coefficient below the terminal one divisible by `π`, so
`ḡ = φ̄ ^ n`; unique factorisation in `(ResidueField O)[X]` then gives `ḡᵢ = φ̄ ^ nᵢ` with
`n₁ + n₂ = n`, which is what makes `mᵢ ∣ gᵢ.natDegree` — i.e. what makes `IsPure`'s *truncated*
right endpoint `gᵢ.natDegree / m` the polygon's terminal point. `hu : 0 < u` is used twice: in
step 0 (it is what forces the sub-terminal heights up) and in the carry gap of `suppVal_mul_le`.

DEPENDS: B.05 (`sum_dev_eq`) · B.08 (`le_gaussVal_iff`, `gaussVal_eq_top_iff`) · B.09
(`gaussVal_mul`) · B.12 (`npHgt_eq_top_iff`) · B.13 (`dev_top`, `npHgt_top`) · B.16
(`OnSide`, `sideSet`) · B.17 (`npHgt_ne_top_of_onSide`) · B.18 (`suppVal_ne_top`,
`sideSet_nonempty`) · B.20 (`sideMin`, `sideDeg`, `onSide_of_mem_sideSet`) · B.25 (`resMk`,
`instFieldResField`) · B.31 (`gaussVal_le_npHgt`) · B.34 (`IsPure`) · B.36 (`resMk_ne_zero`) ·
B35a (`dev_mul_pow`, `dev_mul_pow_of_lt`, `dev_finsetSum`, the `resMk` graded laws) · B35b
(`suppVal_le_weight`, `suppVal_of_pure`, `sideDeg_of_pure`) · mathlib `dvd_prime_pow`,
`Polynomial.eq_of_monic_of_associated`.

**No new axioms; no `sorry`.**

## Status

Sorry-free, axiom-free (Lean core only).
-/

namespace Uniformity.Density.Leaf

open Polynomial IsLocalRing

-- ENV-A′ (blueprint §0.1): the polynomial arena, plus `hπ : Irreducible π` carried per signature.
variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {π : O}

/-! ### Small arithmetic and reduction helpers -/

/-- The cleared weight, as a single `ℕ`-cast (B35c's private helper, re-derived). -/
private theorem weight_cast' (ℓ u H j : ℕ) :
    ℓ • ((H : ℕ) : ℕ∞) + ((u * j : ℕ) : ℕ∞) = ((ℓ * H + u * j : ℕ) : ℕ∞) := by
  push_cast
  simp [nsmul_eq_mul]

/-- A polynomial all of whose coefficients are divisible by `π` reduces to `0`. -/
private theorem map_residue_eq_zero_of_one_le_gaussVal (hπ : Irreducible π) {a : Polynomial O}
    (h : ((1 : ℕ) : ℕ∞) ≤ gaussVal a) : a.map (residue O) = 0 := by
  have hdvd : ∀ i, π ^ 1 ∣ a.coeff i := (le_gaussVal_iff hπ).1 h
  refine Polynomial.ext fun i => ?_
  rw [Polynomial.coeff_map, Polynomial.coeff_zero, IsLocalRing.residue_eq_zero_iff,
    hπ.maximalIdeal_eq, Ideal.mem_span_singleton]
  simpa using hdvd i

/-- The support value is a lower bound for the weight at every abscissa, in `ℕ`. -/
private theorem le_weight_nat {φ f : Polynomial O} (hφ : φ.Monic) (hd : 0 < φ.natDegree)
    {u ℓ : ℕ} (hℓ : 0 < ℓ) {W H j : ℕ} (hW : suppVal φ f u ℓ = ((W : ℕ) : ℕ∞))
    (hH : npHgt φ f j = ((H : ℕ) : ℕ∞)) : W ≤ ℓ * H + u * j := by
  have h := suppVal_le_weight hφ hd hℓ u f j
  rw [hW, hH, weight_cast'] at h
  exact_mod_cast h

/-- On-side abscissae attain the support value, in `ℕ`. -/
private theorem onSide_weight_nat {φ f : Polynomial O} {u ℓ : ℕ} {W H j : ℕ}
    (hW : suppVal φ f u ℓ = ((W : ℕ) : ℕ∞)) (hH : npHgt φ f j = ((H : ℕ) : ℕ∞))
    (hon : OnSide φ f u ℓ j) : ℓ * H + u * j = W := by
  have h : ℓ • npHgt φ f j + ((u * j : ℕ) : ℕ∞) = suppVal φ f u ℓ := hon
  rw [hH, weight_cast', hW] at h
  exact_mod_cast h

/-- Off the side the weight bound is strict, in `ℕ`. -/
private theorem lt_weight_nat {φ f : Polynomial O} (hφ : φ.Monic) (hd : 0 < φ.natDegree)
    {u ℓ : ℕ} (hℓ : 0 < ℓ) {W H j : ℕ} (hW : suppVal φ f u ℓ = ((W : ℕ) : ℕ∞))
    (hH : npHgt φ f j = ((H : ℕ) : ℕ∞)) (hns : ¬ OnSide φ f u ℓ j) : W + 1 ≤ ℓ * H + u * j := by
  have hle := le_weight_nat hφ hd hℓ hW hH
  rcases Nat.lt_or_ge W (ℓ * H + u * j) with h | h
  · omega
  · exact absurd (show OnSide φ f u ℓ j from by
      show ℓ • npHgt φ f j + ((u * j : ℕ) : ℕ∞) = suppVal φ f u ℓ
      rw [hH, weight_cast', hW, le_antisymm h hle]) hns

/-- The side's left endpoint is at most the degree. -/
private theorem sideMin_le_natDegree {φ f : Polynomial O} {u ℓ : ℕ}
    (h : (sideSet φ f u ℓ).Nonempty) : sideMin φ f u ℓ h ≤ f.natDegree := by
  classical
  have hmem : sideMin φ f u ℓ h ∈ sideSet φ f u ℓ := Finset.min'_mem _ _
  have hmem' : sideMin φ f u ℓ h ∈ Finset.filter (OnSide φ f u ℓ)
      (Finset.range (f.natDegree + 1)) := hmem
  exact Nat.lt_succ_iff.1 (Finset.mem_range.1 (Finset.mem_filter.1 hmem').1)

/-- Left of the side's left endpoint nothing is on the side. -/
private theorem not_onSide_of_lt_sideMin {φ f : Polynomial O} {u ℓ : ℕ}
    (h : (sideSet φ f u ℓ).Nonempty) {i : ℕ} (hi : i < sideMin φ f u ℓ h) :
    ¬ OnSide φ f u ℓ i := by
  classical
  intro hon
  have hrange : i ∈ Finset.range (f.natDegree + 1) :=
    Finset.mem_range.2 (Nat.lt_succ_of_le (le_trans hi.le (sideMin_le_natDegree h)))
  have hmem' : i ∈ Finset.filter (OnSide φ f u ℓ) (Finset.range (f.natDegree + 1)) :=
    Finset.mem_filter.2 ⟨hrange, hon⟩
  have hmem : i ∈ sideSet φ f u ℓ := hmem'
  have hle : sideMin φ f u ℓ h ≤ i := Finset.min'_le _ _ hmem
  omega

/-! ### The product's development, term by term -/

/-- **The double expansion of a product's development.** `f * g` is the double sum of the
convolution terms `dev φ f i · dev φ g j · φ^(i+j)` (B.05 twice), and `dev` is additive
(B35a's `dev_finsetSum`), so every development coefficient of the product is the corresponding
sum of the terms' development coefficients. This is B.35's route note, with the abscissa and the
range left free. -/
theorem dev_mul_eq_sum_grid {φ : Polynomial O} (hφ : φ.Monic) (hd : 0 < φ.natDegree)
    (f g : Polynomial O) (k N : ℕ) (hfN : f.natDegree < N * φ.natDegree)
    (hgN : g.natDegree < N * φ.natDegree) :
    dev φ (f * g) k
      = ∑ p ∈ Finset.range N ×ˢ Finset.range N,
          dev φ (dev φ f p.1 * dev φ g p.2 * φ ^ (p.1 + p.2)) k := by
  have hfrep : ∑ j ∈ Finset.range N, dev φ f j * φ ^ j = f := sum_dev_eq hφ hd f hfN
  have hgrep : ∑ i ∈ Finset.range N, dev φ g i * φ ^ i = g := sum_dev_eq hφ hd g hgN
  have hrep : f * g = ∑ p ∈ Finset.range N ×ˢ Finset.range N,
      dev φ f p.1 * dev φ g p.2 * φ ^ (p.1 + p.2) := by
    have h1 : f * g = (∑ j ∈ Finset.range N, dev φ f j * φ ^ j)
        * (∑ i ∈ Finset.range N, dev φ g i * φ ^ i) := by rw [hfrep, hgrep]
    rw [h1, Finset.sum_mul_sum, Finset.sum_product]
    exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => by
      rw [pow_add]; ring
  rw [hrep, dev_finsetSum hφ]

/-! ### No cancellation at a strict corner -/

/-- **The corner lemma.** If the pair `(i₀, j₀)` is a *strict* minimiser of the Gauss valuation
of the convolution terms among all pairs with `i + j ≤ i₀ + j₀` — every other such pair carrying
at least one more unit of valuation — then the product's polygon height at `i₀ + j₀` is exactly
the sum of the two heights.

The corner term is `(dev φ f i₀ · dev φ g j₀) %ₘ φ`, whose digit at height `A + B` is
`resMk A (dev φ f i₀) · resMk B (dev φ g j₀)`: `resMk_modByMonic` erases the `φ`-carry,
`resMk_mul` splits the product, and B.36's exactness clause makes each factor nonzero in
`resField φ`, a field. Every other term's digit vanishes by `resMk_eq_zero_of_lt`. No purity is
involved, and neither `0 < u` nor `Nat.Coprime u ℓ` is needed — the slope enters only through
the caller's proof of `hstrict`. -/
theorem npHgt_mul_of_corner (hπ : Irreducible π) {φ : Polynomial O} (hφ : IsKey φ)
    {f g : Polynomial O} {i₀ j₀ A B : ℕ} (hA : npHgt φ f i₀ = ((A : ℕ) : ℕ∞))
    (hB : npHgt φ g j₀ = ((B : ℕ) : ℕ∞))
    (hstrict : ∀ p : ℕ × ℕ, p.1 + p.2 ≤ i₀ + j₀ → p ≠ (i₀, j₀) →
      ((A + B + 1 : ℕ) : ℕ∞) ≤ gaussVal (dev φ f p.1 * dev φ g p.2)) :
    npHgt φ (f * g) (i₀ + j₀) = ((A + B : ℕ) : ℕ∞) := by
  classical
  letI : Field (resField φ) := instFieldResField hφ
  -- the two corner digits are nonzero, and their product has Gauss valuation exactly `A + B`
  have hAgv : gaussVal (dev φ f i₀) = ((A : ℕ) : ℕ∞) := hA
  have hBgv : gaussVal (dev φ g j₀) = ((B : ℕ) : ℕ∞) := hB
  have hfne : dev φ f i₀ ≠ 0 := fun hz => by
    rw [hz, gaussVal_eq_top_iff.2 rfl] at hAgv; exact (ENat.coe_ne_top A) hAgv.symm
  have hgne : dev φ g j₀ ≠ 0 := fun hz => by
    rw [hz, gaussVal_eq_top_iff.2 rfl] at hBgv; exact (ENat.coe_ne_top B) hBgv.symm
  have hAB : gaussVal (dev φ f i₀ * dev φ g j₀) = ((A + B : ℕ) : ℕ∞) := by
    rw [gaussVal_mul hπ, hAgv, hBgv]
    push_cast
    ring
  set k := i₀ + j₀ with hk
  set N := k + f.natDegree + g.natDegree + 1 with hN
  have hfN : f.natDegree < N * φ.natDegree :=
    lt_of_lt_of_le (Nat.lt_succ_self _)
      (le_trans (by omega) (Nat.le_mul_of_pos_right N hφ.pos))
  have hgN : g.natDegree < N * φ.natDegree :=
    lt_of_lt_of_le (Nat.lt_succ_self _)
      (le_trans (by omega) (Nat.le_mul_of_pos_right N hφ.pos))
  have hgrid := dev_mul_eq_sum_grid hφ.monic hφ.pos f g k N hfN hgN
  -- terms to the right of the abscissa contribute nothing
  have hzero : ∀ p : ℕ × ℕ, k < p.1 + p.2 →
      dev φ (dev φ f p.1 * dev φ g p.2 * φ ^ (p.1 + p.2)) k = 0 :=
    fun p hp => dev_mul_pow_of_lt hφ.monic (p.1 + p.2) _ k hp
  -- every other term's valuation is at least the convolution product's
  have hlow : ∀ p : ℕ × ℕ, p.1 + p.2 ≤ k →
      gaussVal (dev φ f p.1 * dev φ g p.2)
        ≤ gaussVal (dev φ (dev φ f p.1 * dev φ g p.2 * φ ^ (p.1 + p.2)) k) := by
    intro p hp
    obtain ⟨s, hs⟩ := Nat.exists_eq_add_of_le hp
    rw [hs, dev_mul_pow hφ.monic (p.1 + p.2) _ s]
    exact gaussVal_le_npHgt hπ hφ.monic _ s
  -- the side condition of `resMk_finsetSum`
  have hTval : ∀ p ∈ Finset.range N ×ˢ Finset.range N,
      ((A + B : ℕ) : ℕ∞)
        ≤ gaussVal (dev φ (dev φ f p.1 * dev φ g p.2 * φ ^ (p.1 + p.2)) k) := by
    intro p _
    rcases Nat.lt_or_ge k (p.1 + p.2) with hp | hp
    · rw [hzero p hp, gaussVal_eq_top_iff.2 rfl]
      exact le_top
    · refine le_trans ?_ (hlow p hp)
      by_cases hpe : p = (i₀, j₀)
      · rw [hpe]
        exact le_of_eq hAB.symm
      · exact le_trans (by exact_mod_cast Nat.le_succ (A + B)) (hstrict p hp hpe)
  -- the corner term, and its digit
  have hcorner : dev φ (dev φ f i₀ * dev φ g j₀ * φ ^ k) k
      = (dev φ f i₀ * dev φ g j₀) %ₘ φ := by
    have h := dev_mul_pow hφ.monic k (dev φ f i₀ * dev φ g j₀) 0
    rw [Nat.add_zero] at h
    rw [h, dev]
  have hmem : ((i₀, j₀) : ℕ × ℕ) ∈ Finset.range N ×ˢ Finset.range N :=
    Finset.mem_product.2 ⟨Finset.mem_range.2 (by omega), Finset.mem_range.2 (by omega)⟩
  have hother : ∀ p ∈ Finset.range N ×ˢ Finset.range N, p ≠ (i₀, j₀) →
      resMk π φ (A + B) (dev φ (dev φ f p.1 * dev φ g p.2 * φ ^ (p.1 + p.2)) k) = 0 := by
    intro p _ hpne
    rcases Nat.lt_or_ge k (p.1 + p.2) with hp | hp
    · rw [hzero p hp]
      exact resMk_of_zero hπ φ _
    · exact resMk_eq_zero_of_lt hπ (le_trans (hstrict p hp hpne) (hlow p hp))
  have hresne : resMk π φ (A + B) (dev φ (f * g) k) ≠ 0 := by
    rw [hgrid, resMk_finsetSum hπ _ _ hTval, Finset.sum_eq_single_of_mem _ hmem hother, hcorner,
      resMk_modByMonic hπ hφ.monic (le_of_eq hAB.symm),
      resMk_mul hπ (le_of_eq hAgv.symm) (le_of_eq hBgv.symm)]
    exact mul_ne_zero (resMk_ne_zero hπ hφ (degree_dev_lt hφ.monic hφ.pos f i₀) hfne hA)
      (resMk_ne_zero hπ hφ (degree_dev_lt hφ.monic hφ.pos g j₀) hgne hB)
  -- the two halves of the value
  have hge : ((A + B : ℕ) : ℕ∞) ≤ npHgt φ (f * g) k := by
    show ((A + B : ℕ) : ℕ∞) ≤ gaussVal (dev φ (f * g) k)
    rw [hgrid]
    exact le_gaussVal_finsetSum hπ _ _ hTval
  rcases lt_or_ge ((A + B : ℕ) : ℕ∞) (npHgt φ (f * g) k) with hlt | hle
  · exfalso
    refine hresne (resMk_eq_zero_of_lt hπ ?_)
    have hcast : ((A + B + 1 : ℕ) : ℕ∞) = ((A + B : ℕ) : ℕ∞) + 1 := by push_cast; ring
    rw [hcast]
    exact Order.add_one_le_of_lt hlt
  · exact le_antisymm hle hge

/-- **Height additivity at abscissa `0`**, unconditionally: `dev φ (f*g) 0` is
`(dev φ f 0 · dev φ g 0) %ₘ φ`, and mod `φ` no cancellation is possible because `φ̄` is
irreducible of degree `m` while the two digits have degree `< m`. This is the corner lemma at
`i₀ = j₀ = 0`, where the strictness hypothesis is vacuous. -/
theorem npHgt_zero_mul (hπ : Irreducible π) {φ : Polynomial O} (hφ : IsKey φ)
    (f g : Polynomial O) : npHgt φ (f * g) 0 = npHgt φ f 0 + npHgt φ g 0 := by
  rcases eq_or_ne (npHgt φ f 0) ⊤ with hT | hT
  · have hz : dev φ f 0 = 0 := npHgt_eq_top_iff.1 hT
    have hdvd : φ ∣ f := (Polynomial.modByMonic_eq_zero_iff_dvd hφ.monic).1 hz
    have hzz : dev φ (f * g) 0 = 0 :=
      (Polynomial.modByMonic_eq_zero_iff_dvd hφ.monic).2 (hdvd.mul_right g)
    rw [npHgt_eq_top_iff.2 hzz, hT, top_add]
  rcases eq_or_ne (npHgt φ g 0) ⊤ with hT' | hT'
  · have hz : dev φ g 0 = 0 := npHgt_eq_top_iff.1 hT'
    have hdvd : φ ∣ g := (Polynomial.modByMonic_eq_zero_iff_dvd hφ.monic).1 hz
    have hzz : dev φ (f * g) 0 = 0 :=
      (Polynomial.modByMonic_eq_zero_iff_dvd hφ.monic).2 (hdvd.mul_left f)
    rw [npHgt_eq_top_iff.2 hzz, hT', add_top]
  obtain ⟨A, hA⟩ := ENat.ne_top_iff_exists.1 hT
  obtain ⟨B, hB⟩ := ENat.ne_top_iff_exists.1 hT'
  have h := npHgt_mul_of_corner hπ hφ (i₀ := 0) (j₀ := 0) hA.symm hB.symm (by
    intro p hple hpne
    exfalso
    exact hpne (Prod.ext_iff.2 ⟨by omega, by omega⟩))
  rw [← hA, ← hB]
  simpa using h

/-! ### The hard half of the product law -/

/-- **The support value is subadditive on products**, for arbitrary `f`, `g` of finite support
value at the slope `−u/ℓ`. Together with B.33 (`suppVal_add_le_suppVal_mul`) this makes
`suppVal` a valuation at every slope — with **no purity hypothesis**, which is what B.57's
step 1 needs and what B.35's pure-only contract cannot supply.

The witness abscissa is `sideMin f + sideMin g`. It is a strict corner: for `i + j` equal to it
but `(i,j)` different, one coordinate sits strictly left of that factor's `sideMin`, hence off
its side, hence its weight exceeds the support value by at least `1`; for `i + j` smaller, the
carry gap `u ≥ 1` does it (`0 < u` is used exactly here). -/
theorem suppVal_mul_le (hπ : Irreducible π) {φ : Polynomial O} (hφ : IsKey φ) {u ℓ : ℕ}
    (hu : 0 < u) (hℓ : 0 < ℓ) {f g : Polynomial O} (hf' : (sideSet φ f u ℓ).Nonempty)
    (hg' : (sideSet φ g u ℓ).Nonempty) {W₁ W₂ : ℕ}
    (hW₁ : suppVal φ f u ℓ = ((W₁ : ℕ) : ℕ∞)) (hW₂ : suppVal φ g u ℓ = ((W₂ : ℕ) : ℕ∞)) :
    suppVal φ (f * g) u ℓ ≤ ((W₁ + W₂ : ℕ) : ℕ∞) := by
  classical
  have hftop : suppVal φ f u ℓ ≠ ⊤ := by rw [hW₁]; exact ENat.coe_ne_top _
  have hgtop : suppVal φ g u ℓ ≠ ⊤ := by rw [hW₂]; exact ENat.coe_ne_top _
  have honi : OnSide φ f u ℓ (sideMin φ f u ℓ hf') :=
    onSide_of_mem_sideSet (Finset.min'_mem _ _)
  have honj : OnSide φ g u ℓ (sideMin φ g u ℓ hg') :=
    onSide_of_mem_sideSet (Finset.min'_mem _ _)
  obtain ⟨A, hA⟩ := ENat.ne_top_iff_exists.1 (npHgt_ne_top_of_onSide hℓ hftop honi)
  obtain ⟨B, hB⟩ := ENat.ne_top_iff_exists.1 (npHgt_ne_top_of_onSide hℓ hgtop honj)
  have hAeq : ℓ * A + u * sideMin φ f u ℓ hf' = W₁ := onSide_weight_nat hW₁ hA.symm honi
  have hBeq : ℓ * B + u * sideMin φ g u ℓ hg' = W₂ := onSide_weight_nat hW₂ hB.symm honj
  -- the corner: no cancellation at `sideMin f + sideMin g`
  have hcorner : npHgt φ (f * g) (sideMin φ f u ℓ hf' + sideMin φ g u ℓ hg')
      = ((A + B : ℕ) : ℕ∞) := by
    refine npHgt_mul_of_corner hπ hφ hA.symm hB.symm ?_
    intro p hple hpne
    obtain ⟨i, j⟩ := p
    simp only at hple hpne ⊢
    -- vanishing digits are harmless
    rcases eq_or_ne (dev φ f i) 0 with hz | hfi
    · rw [hz, zero_mul, gaussVal_eq_top_iff.2 rfl]
      exact le_top
    rcases eq_or_ne (dev φ g j) 0 with hz | hgj
    · rw [hz, mul_zero, gaussVal_eq_top_iff.2 rfl]
      exact le_top
    obtain ⟨Hi, hHi⟩ := ENat.ne_top_iff_exists.1 (fun h => hfi (gaussVal_eq_top_iff.1 h))
    obtain ⟨Hj, hHj⟩ := ENat.ne_top_iff_exists.1 (fun h => hgj (gaussVal_eq_top_iff.1 h))
    have hgv : gaussVal (dev φ f i * dev φ g j) = ((Hi + Hj : ℕ) : ℕ∞) := by
      rw [gaussVal_mul hπ, ← hHi, ← hHj]
      push_cast
      ring
    rw [hgv]
    have hbi : W₁ ≤ ℓ * Hi + u * i := le_weight_nat hφ.monic hφ.pos hℓ hW₁ hHi.symm
    have hbj : W₂ ≤ ℓ * Hj + u * j := le_weight_nat hφ.monic hφ.pos hℓ hW₂ hHj.symm
    have hmul : ℓ * (A + B) < ℓ * (Hi + Hj) := by
      rcases Nat.lt_or_ge (i + j) (sideMin φ f u ℓ hf' + sideMin φ g u ℓ hg') with hlt | hge
      · -- the carry gap: `0 < u`
        have hstep : u * (i + j) + u
            ≤ u * (sideMin φ f u ℓ hf' + sideMin φ g u ℓ hg') := by
          have h1 : u * (i + j + 1)
              ≤ u * (sideMin φ f u ℓ hf' + sideMin φ g u ℓ hg') :=
            Nat.mul_le_mul_left u hlt
          calc u * (i + j) + u = u * (i + j + 1) := by ring
            _ ≤ _ := h1
        have := hu
        nlinarith [hbi, hbj, hAeq, hBeq, hstep]
      · -- on the same anti-diagonal: one coordinate is off its own side
        have heqij : i + j = sideMin φ f u ℓ hf' + sideMin φ g u ℓ hg' := le_antisymm hple hge
        rcases Nat.lt_trichotomy i (sideMin φ f u ℓ hf') with hi | hi | hi
        · have hns : ¬ OnSide φ f u ℓ i := not_onSide_of_lt_sideMin hf' hi
          have hstrictf : W₁ + 1 ≤ ℓ * Hi + u * i :=
            lt_weight_nat hφ.monic hφ.pos hℓ hW₁ hHi.symm hns
          have hstep : u * (i + j) = u * (sideMin φ f u ℓ hf' + sideMin φ g u ℓ hg') := by
            rw [heqij]
          nlinarith [hbj, hAeq, hBeq, hstrictf, hstep]
        · exact absurd (Prod.ext_iff.2 ⟨hi, by omega⟩) hpne
        · have hj : j < sideMin φ g u ℓ hg' := by omega
          have hns : ¬ OnSide φ g u ℓ j := not_onSide_of_lt_sideMin hg' hj
          have hstrictg : W₂ + 1 ≤ ℓ * Hj + u * j :=
            lt_weight_nat hφ.monic hφ.pos hℓ hW₂ hHj.symm hns
          have hstep : u * (i + j) = u * (sideMin φ f u ℓ hf' + sideMin φ g u ℓ hg') := by
            rw [heqij]
          nlinarith [hbi, hAeq, hBeq, hstrictg, hstep]
    have : A + B < Hi + Hj := Nat.lt_of_mul_lt_mul_left hmul
    exact_mod_cast this
  calc suppVal φ (f * g) u ℓ
      ≤ ℓ • npHgt φ (f * g) (sideMin φ f u ℓ hf' + sideMin φ g u ℓ hg')
          + ((u * (sideMin φ f u ℓ hf' + sideMin φ g u ℓ hg') : ℕ) : ℕ∞) :=
        suppVal_le_weight hφ.monic hφ.pos hℓ u (f * g) _
    _ = ((W₁ + W₂ : ℕ) : ℕ∞) := by
        rw [hcorner, weight_cast']
        congr 1
        rw [← hAeq, ← hBeq]
        ring

/-! ### PROOF step 0: the reduction of a full-degree pure polynomial -/

/-- **Step 0 (A-F.6).** A monic `(u,ℓ)`-pure `f` of degree `n · m` reduces to `φ̄ ^ n`: purity
puts the terminal point `(n, 0)` on the side, so every abscissa `j < n` has
`ℓ · npHgt φ f j ≥ u · (n − j) > 0` (here `0 < u` pays), i.e. `π ∣ dev φ f j`, while
`dev φ f n = 1` (B.13's `dev_top`). -/
theorem map_residue_eq_key_pow_of_pure (hπ : Irreducible π) {φ : Polynomial O} (hφ : IsKey φ)
    {u ℓ : ℕ} (hu : 0 < u) (hℓ : 0 < ℓ) {f : Polynomial O} (hf : f.Monic) {n : ℕ}
    (hdeg : f.natDegree = n * φ.natDegree) (hpure : IsPure φ f u ℓ) :
    f.map (residue O) = (φ.map (residue O)) ^ n := by
  have hsupp : suppVal φ f u ℓ = ((u * n : ℕ) : ℕ∞) :=
    suppVal_of_pure hφ.monic hφ.pos hf hdeg hpure
  have hrep : ∑ j ∈ Finset.range (n + 1), dev φ f j * φ ^ j = f := by
    refine sum_dev_eq hφ.monic hφ.pos f ?_
    rw [hdeg]
    exact mul_lt_mul_of_pos_right (Nat.lt_succ_self n) hφ.pos
  have hzero : ∀ j ∈ Finset.range n, (dev φ f j).map (residue O) = 0 := by
    intro j hj
    have hjlt : j < n := Finset.mem_range.1 hj
    rcases eq_or_ne (dev φ f j) 0 with hz | hnz
    · rw [hz, Polynomial.map_zero]
    refine map_residue_eq_zero_of_one_le_gaussVal hπ ?_
    obtain ⟨H, hH⟩ := ENat.ne_top_iff_exists.1 (fun h => hnz (gaussVal_eq_top_iff.1 h))
    have hb : u * n ≤ ℓ * H + u * j := le_weight_nat hφ.monic hφ.pos hℓ hsupp hH.symm
    have hHpos : 1 ≤ H := by
      rcases Nat.eq_zero_or_pos H with h0 | h0
      · exact absurd hb (Nat.not_le.2 (by
          rw [h0, Nat.mul_zero, Nat.zero_add]
          exact mul_lt_mul_of_pos_left hjlt hu))
      · exact h0
    rw [← hH]
    exact_mod_cast hHpos
  calc f.map (residue O)
      = (∑ j ∈ Finset.range (n + 1), dev φ f j * φ ^ j).map (residue O) := by rw [hrep]
    _ = ∑ j ∈ Finset.range (n + 1),
          (dev φ f j).map (residue O) * (φ.map (residue O)) ^ j := by
        rw [Polynomial.map_sum]
        exact Finset.sum_congr rfl fun j _ => by rw [Polynomial.map_mul, Polynomial.map_pow]
    _ = (φ.map (residue O)) ^ n := by
        rw [Finset.sum_range_succ,
          Finset.sum_eq_zero (fun j hj => by rw [hzero j hj, zero_mul]), zero_add,
          dev_top hφ.monic hφ.pos hf hdeg, Polynomial.map_one, one_mul]

/-! ### The signed contract -/

section ENVC

-- ENV-C (blueprint §0.1): ENV-B plus residue finiteness. Neither instance is consumed; they are
-- declared to reproduce the frozen stub's elaborated type (`[Finite (ResidueField O)]` is trimmed
-- there, so it is `omit`ted here — the B59b/B60 pattern).
variable [IsAdicComplete (maximalIdeal O) O] [Finite (ResidueField O)]

set_option linter.unusedSectionVars false in
omit [Finite (ResidueField O)] in
/-- **B.57 — every monic factor of a pure polynomial is pure** (the signed contract theorem;
signature frozen at the A-F.6 form). For `φ` an order-1 key, `0 < u`, `0 < ℓ`, `u` coprime to
`ℓ`, and `g` monic `(u,ℓ)`-pure with `φ.natDegree ∣ g.natDegree`: if `g = g₁ * g₂` with both
factors monic then both are `(u,ℓ)`-pure, `sideDeg g₁ + sideDeg g₂ = sideDeg g`, and
`ḡ₁ = φ̄ ^ (ℓ · sideDeg g₁)`.

`(hgd)` is load-bearing: without it the frozen form is refuted (`g = X = X * 1` at `φ = X²+1`
over `ℤ₃`), because `IsPure`'s right endpoint is the *truncated* `g.natDegree / φ.natDegree`. -/
theorem isPure_of_monic_factor (hπ : Irreducible π) {φ : Polynomial O} (hφ : IsKey φ)
    {u ℓ : ℕ} (hu : 0 < u) (hℓ : 0 < ℓ) (hcop : Nat.Coprime u ℓ) {g g₁ g₂ : Polynomial O}
    (hg : g.Monic) (hg₁ : g₁.Monic) (hg₂ : g₂.Monic)
    (hgd : φ.natDegree ∣ g.natDegree) (heq : g = g₁ * g₂)
    (hpure : IsPure φ g u ℓ) (hne : (sideSet φ g u ℓ).Nonempty) :
    ∃ (hne₁ : (sideSet φ g₁ u ℓ).Nonempty) (hne₂ : (sideSet φ g₂ u ℓ).Nonempty),
      IsPure φ g₁ u ℓ ∧ IsPure φ g₂ u ℓ ∧
      sideDeg φ g₁ u ℓ hne₁ + sideDeg φ g₂ u ℓ hne₂ = sideDeg φ g u ℓ hne ∧
      g₁.map (IsLocalRing.residue O)
        = (φ.map (IsLocalRing.residue O)) ^ (ℓ * sideDeg φ g₁ u ℓ hne₁) := by
  classical
  obtain ⟨n, hn⟩ := hgd
  have hdeg : g.natDegree = n * φ.natDegree := by rw [hn]; ring
  -- STEP 0: the reductions are key powers, so the factors have `m`-divisible degrees
  have hmapg : g.map (residue O) = (φ.map (residue O)) ^ n :=
    map_residue_eq_key_pow_of_pure hπ hφ hu hℓ hg hdeg hpure
  have hmapmul : (g₁.map (residue O)) * (g₂.map (residue O)) = (φ.map (residue O)) ^ n := by
    rw [← Polynomial.map_mul, ← heq, hmapg]
  have hprime : Prime (φ.map (residue O)) := hφ.irred.prime
  have hpowmonic : ∀ t : ℕ, ((φ.map (residue O)) ^ t).Monic := fun t =>
    (hφ.monic.map (residue O)).pow t
  have hmapmul' : (g₂.map (residue O)) * (g₁.map (residue O)) = (φ.map (residue O)) ^ n := by
    rw [mul_comm]
    exact hmapmul
  obtain ⟨n₁, hn₁le, hass₁⟩ := (dvd_prime_pow hprime n).1
    ⟨g₂.map (residue O), hmapmul.symm⟩
  obtain ⟨n₂, hn₂le, hass₂⟩ := (dvd_prime_pow hprime n).1
    ⟨g₁.map (residue O), hmapmul'.symm⟩
  have hmap₁ : g₁.map (residue O) = (φ.map (residue O)) ^ n₁ :=
    eq_of_monic_of_associated (hg₁.map (residue O)) (hpowmonic n₁) hass₁
  have hmap₂ : g₂.map (residue O) = (φ.map (residue O)) ^ n₂ :=
    eq_of_monic_of_associated (hg₂.map (residue O)) (hpowmonic n₂) hass₂
  have hdegpow : ∀ t : ℕ, ((φ.map (residue O)) ^ t).natDegree = t * φ.natDegree := by
    intro t
    rw [Polynomial.natDegree_pow, hφ.monic.natDegree_map (residue O)]
  have hdeg₁ : g₁.natDegree = n₁ * φ.natDegree := by
    rw [← hg₁.natDegree_map (residue O), hmap₁, hdegpow]
  have hdeg₂ : g₂.natDegree = n₂ * φ.natDegree := by
    rw [← hg₂.natDegree_map (residue O), hmap₂, hdegpow]
  have hn12 : n₁ + n₂ = n := by
    have hsum : g.natDegree = g₁.natDegree + g₂.natDegree := by
      rw [heq, Polynomial.natDegree_mul hg₁.ne_zero hg₂.ne_zero]
    rw [hdeg, hdeg₁, hdeg₂] at hsum
    refine Nat.eq_of_mul_eq_mul_right hφ.pos ?_
    rw [hsum]
    ring
  -- the two sides are nonempty, and the two support values are finite
  have hne₁ : (sideSet φ g₁ u ℓ).Nonempty := sideSet_nonempty hφ.monic hφ.pos hg₁ hdeg₁ u ℓ
  have hne₂ : (sideSet φ g₂ u ℓ).Nonempty := sideSet_nonempty hφ.monic hφ.pos hg₂ hdeg₂ u ℓ
  have hub₁ : suppVal φ g₁ u ℓ ≤ ((u * n₁ : ℕ) : ℕ∞) :=
    suppVal_ne_top hφ.monic hφ.pos hg₁ hdeg₁ u ℓ
  have hub₂ : suppVal φ g₂ u ℓ ≤ ((u * n₂ : ℕ) : ℕ∞) :=
    suppVal_ne_top hφ.monic hφ.pos hg₂ hdeg₂ u ℓ
  obtain ⟨W₁, hW₁⟩ := ENat.ne_top_iff_exists.1
    (fun h => (ENat.coe_ne_top (u * n₁)) (le_antisymm le_top (h ▸ hub₁)))
  obtain ⟨W₂, hW₂⟩ := ENat.ne_top_iff_exists.1
    (fun h => (ENat.coe_ne_top (u * n₂)) (le_antisymm le_top (h ▸ hub₂)))
  have hW₁le : W₁ ≤ u * n₁ := by rw [← hW₁] at hub₁; exact_mod_cast hub₁
  have hW₂le : W₂ ≤ u * n₂ := by rw [← hW₂] at hub₂; exact_mod_cast hub₂
  -- STEP 1: the product law forces both terminal points onto their sides
  have hgsupp : suppVal φ g u ℓ = ((u * n : ℕ) : ℕ∞) :=
    suppVal_of_pure hφ.monic hφ.pos hg hdeg hpure
  have hprod : suppVal φ g u ℓ ≤ ((W₁ + W₂ : ℕ) : ℕ∞) := by
    rw [heq]
    exact suppVal_mul_le hπ hφ hu hℓ hne₁ hne₂ hW₁.symm hW₂.symm
  have hsum : u * n ≤ W₁ + W₂ := by
    rw [hgsupp] at hprod
    exact_mod_cast hprod
  have hXY : W₁ + W₂ = u * n₁ + u * n₂ := by
    refine le_antisymm (Nat.add_le_add hW₁le hW₂le) ?_
    calc u * n₁ + u * n₂ = u * n := by rw [← hn12]; ring
      _ ≤ W₁ + W₂ := hsum
  have hW₁eq : W₁ = u * n₁ := by
    have hstep : u * n₁ + W₂ ≤ W₁ + W₂ := by
      calc u * n₁ + W₂ ≤ u * n₁ + u * n₂ := Nat.add_le_add_left hW₂le _
        _ = W₁ + W₂ := hXY.symm
    exact le_antisymm hW₁le (Nat.le_of_add_le_add_right hstep)
  have hW₂eq : W₂ = u * n₂ := by omega
  -- STEP 1': height additivity at abscissa `0` puts both left endpoints onto their sides
  have h0g : OnSide φ g u ℓ 0 := hpure.1
  have hgtop : suppVal φ g u ℓ ≠ ⊤ := by rw [hgsupp]; exact ENat.coe_ne_top _
  have h0fin : npHgt φ g 0 ≠ ⊤ := npHgt_ne_top_of_onSide hℓ hgtop h0g
  have hsplit : npHgt φ g 0 = npHgt φ g₁ 0 + npHgt φ g₂ 0 := by
    rw [heq]
    exact npHgt_zero_mul hπ hφ g₁ g₂
  have h1fin : npHgt φ g₁ 0 ≠ ⊤ := by
    intro h
    rw [hsplit, h, top_add] at h0fin
    exact h0fin rfl
  have h2fin : npHgt φ g₂ 0 ≠ ⊤ := by
    intro h
    rw [hsplit, h, add_top] at h0fin
    exact h0fin rfl
  obtain ⟨a₀, ha₀⟩ := ENat.ne_top_iff_exists.1 h1fin
  obtain ⟨b₀, hb₀⟩ := ENat.ne_top_iff_exists.1 h2fin
  have hc₀ : npHgt φ g 0 = ((a₀ + b₀ : ℕ) : ℕ∞) := by
    rw [hsplit, ← ha₀, ← hb₀]
    push_cast
    ring
  have hc₀eq : ℓ * (a₀ + b₀) + u * 0 = u * n := onSide_weight_nat hgsupp hc₀ h0g
  have hbi : W₁ ≤ ℓ * a₀ + u * 0 := le_weight_nat hφ.monic hφ.pos hℓ hW₁.symm ha₀.symm
  have hbj : W₂ ≤ ℓ * b₀ + u * 0 := le_weight_nat hφ.monic hφ.pos hℓ hW₂.symm hb₀.symm
  have hleft₁ : ℓ * a₀ + u * 0 = W₁ := by
    have hzero : ℓ * (a₀ + b₀) = ℓ * a₀ + ℓ * b₀ := by ring
    have hnn : u * n = u * n₁ + u * n₂ := by rw [← hn12]; ring
    refine le_antisymm ?_ hbi
    have hle : ℓ * a₀ + ℓ * b₀ ≤ W₁ + W₂ := by
      rw [← hzero]
      omega
    have : ℓ * a₀ + W₂ ≤ W₁ + W₂ :=
      le_trans (Nat.add_le_add_left (by omega : W₂ ≤ ℓ * b₀) _) hle
    have := Nat.le_of_add_le_add_right this
    omega
  have hleft₂ : ℓ * b₀ + u * 0 = W₂ := by
    have hzero : ℓ * (a₀ + b₀) = ℓ * a₀ + ℓ * b₀ := by ring
    omega
  -- purity of the two factors
  have hquot₁ : g₁.natDegree / φ.natDegree = n₁ := by
    rw [hdeg₁]
    exact Nat.mul_div_cancel _ hφ.pos
  have hquot₂ : g₂.natDegree / φ.natDegree = n₂ := by
    rw [hdeg₂]
    exact Nat.mul_div_cancel _ hφ.pos
  have hpure₁ : IsPure φ g₁ u ℓ := by
    constructor
    · show ℓ • npHgt φ g₁ 0 + ((u * 0 : ℕ) : ℕ∞) = suppVal φ g₁ u ℓ
      rw [← ha₀, weight_cast', hleft₁, hW₁]
    · rw [hquot₁]
      show ℓ • npHgt φ g₁ n₁ + ((u * n₁ : ℕ) : ℕ∞) = suppVal φ g₁ u ℓ
      rw [npHgt_top hφ.monic hφ.pos hg₁ hdeg₁, ← hW₁, hW₁eq]
      simp
  have hpure₂ : IsPure φ g₂ u ℓ := by
    constructor
    · show ℓ • npHgt φ g₂ 0 + ((u * 0 : ℕ) : ℕ∞) = suppVal φ g₂ u ℓ
      rw [← hb₀, weight_cast', hleft₂, hW₂]
    · rw [hquot₂]
      show ℓ • npHgt φ g₂ n₂ + ((u * n₂ : ℕ) : ℕ∞) = suppVal φ g₂ u ℓ
      rw [npHgt_top hφ.monic hφ.pos hg₂ hdeg₂, ← hW₂, hW₂eq]
      simp
  -- the residual degrees add, and the reduction clause
  have hsd₁ : ℓ * sideDeg φ g₁ u ℓ hne₁ = n₁ :=
    sideDeg_of_pure hφ.monic hφ.pos hg₁ hdeg₁ hℓ hcop hpure₁ hne₁
  have hsd₂ : ℓ * sideDeg φ g₂ u ℓ hne₂ = n₂ :=
    sideDeg_of_pure hφ.monic hφ.pos hg₂ hdeg₂ hℓ hcop hpure₂ hne₂
  have hsd : ℓ * sideDeg φ g u ℓ hne = n :=
    sideDeg_of_pure hφ.monic hφ.pos hg hdeg hℓ hcop hpure hne
  refine ⟨hne₁, hne₂, hpure₁, hpure₂, ?_, ?_⟩
  · refine Nat.eq_of_mul_eq_mul_left hℓ ?_
    rw [hsd, Nat.mul_add, hsd₁, hsd₂, hn12]
  · rw [hmap₁, hsd₁]

end ENVC

end Uniformity.Density.Leaf

/-! ## Axiom footprint -/

section AxCheck
#print axioms Uniformity.Density.Leaf.dev_mul_eq_sum_grid
#print axioms Uniformity.Density.Leaf.npHgt_mul_of_corner
#print axioms Uniformity.Density.Leaf.npHgt_zero_mul
#print axioms Uniformity.Density.Leaf.suppVal_mul_le
#print axioms Uniformity.Density.Leaf.map_residue_eq_key_pow_of_pure
#print axioms Uniformity.Density.Leaf.isPure_of_monic_factor
end AxCheck
