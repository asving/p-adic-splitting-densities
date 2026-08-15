/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.Density.LocalData

/-!
# Uniformity.ChapB.B56 — the singleton lemma

**Chapter B, NODE B.56** (`blueprint/CHAP-B_leaf_layer.md`, the leaf / order-1 layer).

*The singleton lemma.* If every member `(e', f')` of a factorization type of degree `n > 0`
already accounts for the whole degree (`n ≤ e' * f'`), then there is exactly one member and it
accounts for it exactly. If moreover a fixed `a` divides every `e'`, a fixed `b` divides every
`f'`, and `a * b` is the degree, the type is forced to be `⟨{(a, b)}⟩`.

**This node replaces the corpus's Galois-orbit argument.** `EFF.HE3.34`'s base step concludes
irreducibility from "a Galois-stable set of size `N` all of whose elements have orbit size `≥ N`
is a single orbit of size exactly `N`", and `EFF.HE6.32` step 3 from the sandwich
`Σ_r |S_{λ,r}| = Σ_r N_r` with `|S_{λ,r}| ≥ N_r`. Both are counting arguments over `K̄₀`; this is
the same pigeonhole run on `FactorizationType.data` instead, which is why the chapter needs no
algebraic closure and no Galois action.

DEPENDS: landed `Uniformity.FactorizationType.degree` (`Density/LocalData.lean:49`),
`Uniformity.FactorizationType.ext` (ibid. `:52`) · mathlib `Multiset.card_nsmul_le_sum`,
`Multiset.card_eq_one`.

**PROOF.** `σ.degree` is the sum of the multiset `σ.data.map (fun p => p.1 * p.2)`, every entry
of which is `≥ n`; hence `card • n ≤ n`, so `card ≤ 1`, and `card ≠ 0` because the sum is
`n > 0`. `Multiset.card_eq_one` then gives the singleton and its product. For the second
statement, `a ∣ e'` and `b ∣ f'` with positivity give `a * b ≤ e' * f'`, feeding the first
statement with `n = a * b`; writing `e₀ = a * s`, `f₀ = b * t` and cancelling `a * b > 0` in
`a * s * (b * t) = a * b` gives `s * t = 1`, so `s = t = 1`. `FactorizationType.ext` closes.

SOURCE: `EFF.HE3.34` (the orbit argument); `EFF.HE6.32` (the sandwich); landed
`Density/TypePositivity.lean`.

## Status

Sorry-free, axiom-free (Lean core only).
-/

namespace Uniformity.Density.Leaf

/-- **B.56 (a) — the singleton lemma.** A factorization type of degree `n > 0` all of whose
`(e, f)` members satisfy `n ≤ e * f` has exactly one member, and that member satisfies
`e * f = n`. -/
theorem factorizationType_singleton {σ : FactorizationType} {n : ℕ} (hn : 0 < n)
    (hdeg : σ.degree = n) (hge : ∀ p ∈ σ.data, n ≤ p.1 * p.2) :
    ∃ p, σ.data = {p} ∧ p.1 * p.2 = n := by
  classical
  set s : Multiset ℕ := σ.data.map (fun p => p.1 * p.2) with hs
  have hsum : s.sum = n := hdeg
  have hmem : ∀ x ∈ s, n ≤ x := by
    intro x hx
    rw [hs, Multiset.mem_map] at hx
    obtain ⟨p, hp, rfl⟩ := hx
    exact hge p hp
  -- the pigeonhole: `card • n ≤ sum = n` forces `card ≤ 1`
  have hle : Multiset.card s • n ≤ n := by
    have := Multiset.card_nsmul_le_sum hmem
    rwa [hsum] at this
  have hcards : Multiset.card s ≤ 1 := by
    rw [smul_eq_mul] at hle
    rcases Nat.lt_or_ge (Multiset.card s) 2 with hc | hc
    · omega
    · have : 2 * n ≤ Multiset.card s * n := Nat.mul_le_mul_right n hc
      omega
  have hcard0 : Multiset.card s ≠ 0 := by
    intro h0
    rw [Multiset.card_eq_zero] at h0
    rw [h0, Multiset.sum_zero] at hsum
    omega
  have hcard : Multiset.card σ.data = 1 := by
    have : Multiset.card s = Multiset.card σ.data := by rw [hs, Multiset.card_map]
    omega
  obtain ⟨p, hp⟩ := Multiset.card_eq_one.1 hcard
  refine ⟨p, hp, ?_⟩
  have : (Multiset.map (fun p : ℕ × ℕ => p.1 * p.2) σ.data).sum = n := hdeg
  rw [hp] at this
  simpa using this

/-- **B.56 (b) — the type is pinned by divisibility.** If `a ∣ e` and `b ∣ f` for every member
`(e, f)` (all positive) of a factorization type of degree `a * b`, then the type is the singleton
`{(a, b)}`. -/
theorem factorizationType_eq_of_dvd {σ : FactorizationType} {a b : ℕ} (ha : 0 < a) (hb : 0 < b)
    (hdeg : σ.degree = a * b) (hpos : ∀ p ∈ σ.data, 0 < p.1 ∧ 0 < p.2)
    (hA : ∀ p ∈ σ.data, a ∣ p.1) (hB : ∀ p ∈ σ.data, b ∣ p.2) :
    σ = ⟨{(a, b)}⟩ := by
  have hab : 0 < a * b := Nat.mul_pos ha hb
  have hge : ∀ p ∈ σ.data, a * b ≤ p.1 * p.2 := by
    intro p hp
    exact Nat.le_of_dvd (Nat.mul_pos (hpos p hp).1 (hpos p hp).2)
      (mul_dvd_mul (hA p hp) (hB p hp))
  obtain ⟨p, hp, hpe⟩ := factorizationType_singleton hab hdeg hge
  have hmem : p ∈ σ.data := by rw [hp]; exact Multiset.mem_singleton_self p
  obtain ⟨s, hs⟩ := hA p hmem
  obtain ⟨t, ht⟩ := hB p hmem
  have hst : s * t = 1 := by
    have hfac : p.1 * p.2 = (a * b) * (s * t) := by rw [hs, ht]; ring
    have h1 : (a * b) * (s * t) = (a * b) * 1 := by rw [mul_one, ← hfac, hpe]
    exact Nat.eq_of_mul_eq_mul_left hab h1
  have hs1 : s = 1 := Nat.dvd_one.1 ⟨t, hst.symm⟩
  have ht1 : t = 1 := Nat.dvd_one.1 ⟨s, by rw [← hst]; ring⟩
  have hpa : p = (a, b) := by
    have h1 : p.1 = a := by rw [hs, hs1, mul_one]
    have h2 : p.2 = b := by rw [ht, ht1, mul_one]
    exact Prod.ext h1 h2
  exact FactorizationType.ext (by rw [hp, hpa])

section AxCheck
#print axioms Uniformity.Density.Leaf.factorizationType_singleton
#print axioms Uniformity.Density.Leaf.factorizationType_eq_of_dvd
end AxCheck

end Uniformity.Density.Leaf
