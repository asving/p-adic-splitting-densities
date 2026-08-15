/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapB.B05
import Uniformity.ChapB.B09
import Uniformity.ChapB.B32b
import Uniformity.HenselFactorization

/-!
# Uniformity.ChapB.B40 — the graded adic limit

**Chapter B, NODE B.40** [lemma] (`blueprint/CHAP-B_leaf_layer.md` §6, the Hensel/graded engine),
ENV-B (ENV-A plus `[IsAdicComplete (maximalIdeal O) O]`, plus the explicit `hπ : Irreducible π`).

*The graded adic limit.* Let `d : ℕ`, and let `p : ℕ → O[X]` be a sequence of polynomials of
`natDegree < d` whose successive differences grow in the **`suppVal` filtration**:
`(k : ℕ∞) ≤ suppVal φ (p (k+1) - p k) u ℓ` for every `k`. Then the sequence has a limit inside the
same degree window: some `P` with `P.natDegree < d` and `(k : ℕ∞) ≤ suppVal φ (P - p k) u ℓ` for
every `k`.

The point of the node is that the `suppVal` filtration (the weighted `φ`-adic polygon filtration
at slope `−u/ℓ`) is **comparable in both directions** to the coefficientwise `π`-adic filtration,
so completeness of `O` — which only knows the latter — supplies the limit. The two comparisons are

* **downward** (`le_gaussVal_of_le_suppVal`, the blueprint's `gaussVal_ge_of_suppVal_ge`, and the
  node's only real content): a `suppVal` bound of `ℓ * N + u * D` on a polynomial of degree `< D`
  forces `gaussVal ≥ N`, because `gaussVal a` dominates the infimum of the polygon heights
  `npHgt φ a j` (B.05 writes `a = Σ_j dev φ a j * φ ^ j`, B.09 kills the `φ ^ j` factors, and
  `gaussVal` is ultrametric on the sum), while `suppVal` is that same infimum weighted by `ℓ` and
  shifted by at most `u * D`;
* **upward** (B32b's `weight_le_suppVal_mul_pow` at `t = 0`): `ℓ • gaussVal a ≤ suppVal φ a u ℓ`.

DEPENDS: B.05 (`sum_dev_eq`) · B.07 (`gaussVal`) · B.08 (`le_gaussVal_iff`, `gaussVal_eq_top_iff`) ·
B.09 (`gaussVal_mul`) · B.11 (`npHgt`) · B.14 (`suppVal`) · B.31 (`gaussVal_le_npHgt`, through
B32b) · B32a (`min_gaussVal_le_gaussVal_add`, `gaussVal_le_addVal_coeff`) · B32b
(`suppVal_eq_inf_range`, `suppVal_zero_eq_top`, `min_suppVal_le_suppVal_add`,
`weight_le_suppVal_mul_pow`) · landed `Uniformity.Hensel.exists_adicLimit_of_degree_lt`
(`HenselFactorization.lean:306`), `Uniformity.Hensel.mem_coeffIdeal`,
`Uniformity.Hensel.maximalIdeal_pow_eq_span` (`StrongHensel.lean:213`) · mathlib
`Polynomial.natDegree_lt_iff_degree_lt`, `Polynomial.natDegree_sub_le`, `ENat.add_le_add_iff_right`.

**PROOF.**
1. `le_gaussVal_of_le_suppVal` (step 1 of the blueprint, landed as a standalone private helper as
   the blueprint demands): for `a.natDegree < D` and
   `((ℓ * N + u * D : ℕ) : ℕ∞) ≤ suppVal φ a u ℓ`, one gets `(N : ℕ∞) ≤ gaussVal a`. Compute
   `suppVal` over the range `D + 1` (B32b's `suppVal_eq_inf_range`); at each abscissa `j ≤ D` the
   weight `u * j` is at most `u * D`, so cancelling it (`ENat.add_le_add_iff_right`) leaves
   `ℓ • (N : ℕ∞) ≤ ℓ • npHgt φ a j`, hence `(N : ℕ∞) ≤ npHgt φ a j` since `0 < ℓ`. Then
   `inf_npHgt_le_gaussVal` finishes.
2. **The subsequence.** `q j := p (ℓ * j + u * d)`. Telescoping `hstep`
   (`le_suppVal_sub`, an induction on the gap through B32b's ultrametric law) gives
   `((ℓ * j + u * d : ℕ) : ℕ∞) ≤ suppVal φ (q (j+1) - q j) u ℓ`, which is exactly the hypothesis
   of step 1 at `N := j`, `D := d`. So `gaussVal (q (j+1) - q j) ≥ j`, i.e.
   `q (j+1) - q j ∈ coeffIdeal (maximalIdeal O ^ j)`.
3. **The limit.** Landed `exists_adicLimit_of_degree_lt` returns `P` of degree `< d` with
   `P - q j ∈ coeffIdeal (maximalIdeal O ^ j)`.
4. **Back to `suppVal`.** `P - p k = (P - q k) + (q k - p k)`. The first summand has
   `gaussVal ≥ k`, hence `suppVal ≥ ℓ • k ≥ k` by the upward comparison; the second is the
   telescoped block from `k` up to `ℓ * k + u * d ≥ k`, hence `suppVal ≥ k`. B32b's
   `min_suppVal_le_suppVal_add` combines them.

The blueprint's step-4 sketch routes through B.33 (`suppVal_add_le_suppVal_mul`); that node is not
yet landed and is not needed — B32b's ultrametric law `min_suppVal_le_suppVal_add` is the
inequality actually used, and it is strictly weaker than B.33.

## Faithfulness

`EFF.HE3.27`(c) — the in-window, upward clause, the corpus's form of "the approximation converges
inside the window": the limit stays in the same degree window `d` and its distance to the `k`-th
approximant is measured by the same weighted polygon functional. The landed
`HenselFactorization.lean:306` is the template for the completeness step and is used verbatim.

**TEETH.** signed non-applicable.

SOURCE: landed `HenselFactorization.lean:306`; `EFF.HE3.27`(c).

## Status

Sorry-free, axiom-free (Lean core only).
-/

namespace Uniformity.Density.Leaf

open Polynomial IsLocalRing
open IsDiscreteValuationRing hiding maximalIdeal

-- ENV-A′ (blueprint §0.1): the polynomial arena, plus `hπ : Irreducible π` carried per
-- signature. ENV-B's completeness instance is entered in its own section below.
variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {π : O}

/-! ### The two comparisons between `suppVal` and `gaussVal` -/

/-- A monic polynomial has Gauss valuation `0`: its leading coefficient is a unit. Private
helper. -/
private theorem gaussVal_eq_zero_of_monic {p : Polynomial O} (hp : p.Monic) : gaussVal p = 0 := by
  refine le_antisymm ?_ (by simp)
  have h := gaussVal_le_addVal_coeff p p.natDegree
  rwa [hp.coeff_natDegree, addVal_one] at h

/-- **`gaussVal` is ultrametric on finite sums** — the `Finset.range` form of B32a's
`min_gaussVal_le_gaussVal_add`. Private helper. -/
private theorem inf_gaussVal_le_gaussVal_sum (F : ℕ → Polynomial O) (K : ℕ) :
    (Finset.range K).inf (fun t => gaussVal (F t))
      ≤ gaussVal (∑ t ∈ Finset.range K, F t) := by
  induction K with
  | zero =>
    simp only [Finset.range_zero, Finset.inf_empty, Finset.sum_empty]
    exact le_of_eq (gaussVal_eq_top_iff.2 rfl).symm
  | succ K ih =>
    rw [Finset.sum_range_succ, Finset.range_add_one, Finset.inf_insert]
    refine le_trans ?_ (min_gaussVal_le_gaussVal_add (∑ t ∈ Finset.range K, F t) (F K))
    rw [min_comm]
    exact min_le_min ih le_rfl

/-- **The Gauss valuation dominates the infimum of the polygon heights.** `a` is the sum of its
`φ`-adic monomials `dev φ a j * φ ^ j` (B.05); each has Gauss valuation `npHgt φ a j` (B.09, since
`φ ^ j` is monic hence of Gauss valuation `0`); `gaussVal` is ultrametric on the sum. Private
helper. -/
private theorem inf_npHgt_le_gaussVal (hπ : Irreducible π) {φ : Polynomial O} (hφ : φ.Monic)
    (hd : 0 < φ.natDegree) (a : Polynomial O) {K : ℕ} (hK : a.natDegree < K * φ.natDegree) :
    (Finset.range K).inf (fun j => npHgt φ a j) ≤ gaussVal a := by
  have hterm : ∀ j, npHgt φ a j = gaussVal (dev φ a j * φ ^ j) := by
    intro j
    show gaussVal (dev φ a j) = _
    rw [gaussVal_mul hπ, gaussVal_eq_zero_of_monic (hφ.pow j), add_zero]
  calc (Finset.range K).inf (fun j => npHgt φ a j)
      = (Finset.range K).inf (fun j => gaussVal (dev φ a j * φ ^ j)) := by
        simp only [hterm]
    _ ≤ gaussVal (∑ j ∈ Finset.range K, dev φ a j * φ ^ j) :=
        inf_gaussVal_le_gaussVal_sum _ K
    _ = gaussVal a := by rw [sum_dev_eq hφ hd a hK]

/-- The `ℓ`-cancellation in `ℕ∞`, for `0 < ℓ`. Private helper. -/
private theorem le_of_nsmul_le_nsmul {ℓ N : ℕ} (hℓ : 0 < ℓ) {y : ℕ∞}
    (h : ℓ • ((N : ℕ) : ℕ∞) ≤ ℓ • y) : ((N : ℕ) : ℕ∞) ≤ y := by
  rcases eq_or_ne y ⊤ with rfl | hy
  · exact le_top
  · lift y to ℕ using hy with n
    rw [nsmul_eq_mul, nsmul_eq_mul] at h
    have hnat : ℓ * N ≤ ℓ * n := by exact_mod_cast h
    exact_mod_cast Nat.le_of_mul_le_mul_left hnat hℓ

/-- **Step 1 of the blueprint — the weight-to-coefficient conversion, the node's only content.**
A `suppVal` bound of `ℓ * N + u * D` on a polynomial of degree `< D` forces `gaussVal ≥ N`. -/
private theorem le_gaussVal_of_le_suppVal (hπ : Irreducible π) {φ : Polynomial O} (hφ : φ.Monic)
    (hd : 0 < φ.natDegree) {ℓ : ℕ} (hℓ : 0 < ℓ) (u : ℕ) {a : Polynomial O} {D N : ℕ}
    (haD : a.natDegree < D) (h : ((ℓ * N + u * D : ℕ) : ℕ∞) ≤ suppVal φ a u ℓ) :
    ((N : ℕ) : ℕ∞) ≤ gaussVal a := by
  have hcast : ℓ • ((N : ℕ) : ℕ∞) = ((ℓ * N : ℕ) : ℕ∞) := by
    rw [nsmul_eq_mul]; norm_cast
  refine le_trans ?_ (inf_npHgt_le_gaussVal hπ hφ hd a (K := D + 1) ?_)
  · refine Finset.le_inf fun j hj => ?_
    have hjD : j ≤ D := by have := Finset.mem_range.1 hj; omega
    have hle : ℓ • ((N : ℕ) : ℕ∞) + ((u * j : ℕ) : ℕ∞)
        ≤ ℓ • npHgt φ a j + ((u * j : ℕ) : ℕ∞) := by
      calc ℓ • ((N : ℕ) : ℕ∞) + ((u * j : ℕ) : ℕ∞)
          = ((ℓ * N + u * j : ℕ) : ℕ∞) := by rw [hcast]; norm_cast
        _ ≤ ((ℓ * N + u * D : ℕ) : ℕ∞) := by
            have hnat : ℓ * N + u * j ≤ ℓ * N + u * D :=
              Nat.add_le_add_left (Nat.mul_le_mul_left u hjD) _
            exact_mod_cast hnat
        _ ≤ suppVal φ a u ℓ := h
        _ ≤ ℓ • npHgt φ a j + ((u * j : ℕ) : ℕ∞) := by
            rw [suppVal_eq_inf_range hφ hd hℓ u a (M := D + 1) (by omega)]
            exact Finset.inf_le hj
    exact le_of_nsmul_le_nsmul hℓ
      ((ENat.add_le_add_iff_right (ENat.coe_ne_top (u * j))).1 hle)
  · calc a.natDegree < D + 1 := by omega
      _ ≤ (D + 1) * φ.natDegree := Nat.le_mul_of_pos_right _ hd

/-! ### Telescoping the hypothesis -/

/-- Telescoping `hstep`: the whole block from `a` to `a + c` still has `suppVal ≥ a`. Private
helper. -/
private theorem le_suppVal_sub {φ : Polynomial O} (hφ : φ.Monic) (hd : 0 < φ.natDegree) {ℓ : ℕ}
    (hℓ : 0 < ℓ) (u : ℕ) (p : ℕ → Polynomial O)
    (hstep : ∀ k, ((k : ℕ) : ℕ∞) ≤ suppVal φ (p (k + 1) - p k) u ℓ) (a c : ℕ) :
    ((a : ℕ) : ℕ∞) ≤ suppVal φ (p (a + c) - p a) u ℓ := by
  induction c with
  | zero =>
    simp only [Nat.add_zero, sub_self, suppVal_zero_eq_top hℓ]
    exact le_top
  | succ c ih =>
    have hsplit : p (a + (c + 1)) - p a
        = (p (a + c + 1) - p (a + c)) + (p (a + c) - p a) := by
      rw [show a + (c + 1) = a + c + 1 from rfl]; ring
    rw [hsplit]
    refine le_trans ?_ (min_suppVal_le_suppVal_add hφ hd hℓ u _ _)
    refine le_min ?_ ih
    exact le_trans (Nat.cast_le.2 (Nat.le_add_right a c)) (hstep (a + c))

/-! ### The contract -/

section ENVB

-- ENV-B (blueprint §0.1): ENV-A plus completeness of `O` for its maximal ideal.
variable [IsAdicComplete (maximalIdeal O) O]

/-- **B.40 — the graded adic limit.** A sequence of polynomials of `natDegree < d` that is Cauchy
for the weighted `φ`-adic polygon filtration converges, inside the same degree window. -/
theorem exists_graded_limit (hπ : Irreducible π) {φ : Polynomial O} (hφ : φ.Monic)
    (hd0 : 0 < φ.natDegree) {u ℓ : ℕ} (hℓ : 0 < ℓ) (d : ℕ) (p : ℕ → Polynomial O)
    (hdeg : ∀ k, (p k).natDegree < d)
    (hstep : ∀ k, ((k : ℕ) : ℕ∞) ≤ suppVal φ (p (k + 1) - p k) u ℓ) :
    ∃ P : Polynomial O, P.natDegree < d ∧ ∀ k, ((k : ℕ) : ℕ∞) ≤ suppVal φ (P - p k) u ℓ := by
  classical
  have hd1 : 0 < d := lt_of_le_of_lt (Nat.zero_le _) (hdeg 0)
  -- the reindexed subsequence
  have hqdeg : ∀ j : ℕ, (p (ℓ * j + u * d)).degree < (d : WithBot ℕ) := by
    intro j
    by_cases hp : p (ℓ * j + u * d) = 0
    · rw [hp]; simp
    · exact (Polynomial.natDegree_lt_iff_degree_lt hp).1 (hdeg _)
  have hqstep : ∀ j : ℕ, p (ℓ * (j + 1) + u * d) - p (ℓ * j + u * d)
      ∈ Uniformity.Hensel.coeffIdeal (maximalIdeal O ^ j) := by
    intro j
    have hsplit : ℓ * (j + 1) + u * d = (ℓ * j + u * d) + ℓ := by ring
    have h1 : ((ℓ * j + u * d : ℕ) : ℕ∞)
        ≤ suppVal φ (p (ℓ * (j + 1) + u * d) - p (ℓ * j + u * d)) u ℓ := by
      rw [hsplit]
      exact le_suppVal_sub hφ hd0 hℓ u p hstep (ℓ * j + u * d) ℓ
    have hDdeg : (p (ℓ * (j + 1) + u * d) - p (ℓ * j + u * d)).natDegree < d :=
      lt_of_le_of_lt (Polynomial.natDegree_sub_le _ _)
        (max_lt (hdeg _) (hdeg _))
    have h2 : ((j : ℕ) : ℕ∞) ≤ gaussVal (p (ℓ * (j + 1) + u * d) - p (ℓ * j + u * d)) :=
      le_gaussVal_of_le_suppVal hπ hφ hd0 hℓ u (D := d) (N := j) hDdeg h1
    rw [Uniformity.Hensel.mem_coeffIdeal]
    intro i
    rw [Uniformity.Hensel.maximalIdeal_pow_eq_span hπ, Ideal.mem_span_singleton]
    exact (le_gaussVal_iff hπ).1 h2 i
  obtain ⟨P, hPdeg, hPlim⟩ :=
    Uniformity.Hensel.exists_adicLimit_of_degree_lt d (fun j => p (ℓ * j + u * d)) hqdeg hqstep
  refine ⟨P, ?_, ?_⟩
  · by_cases hP : P = 0
    · rw [hP]; simpa using hd1
    · exact (Polynomial.natDegree_lt_iff_degree_lt hP).2 hPdeg
  · intro k
    -- the tail `P - q k`: a `gaussVal` bound, pushed up to `suppVal`
    have hg : ((k : ℕ) : ℕ∞) ≤ gaussVal (P - p (ℓ * k + u * d)) := by
      refine (le_gaussVal_iff hπ).2 fun i => ?_
      have hmem := Uniformity.Hensel.mem_coeffIdeal.1 (hPlim k) i
      rwa [Uniformity.Hensel.maximalIdeal_pow_eq_span hπ, Ideal.mem_span_singleton] at hmem
    have hPq : ((k : ℕ) : ℕ∞) ≤ suppVal φ (P - p (ℓ * k + u * d)) u ℓ := by
      calc ((k : ℕ) : ℕ∞) ≤ ((ℓ * k : ℕ) : ℕ∞) :=
            Nat.cast_le.2 (Nat.le_mul_of_pos_left k hℓ)
        _ = ℓ • ((k : ℕ) : ℕ∞) := by rw [nsmul_eq_mul]; norm_cast
        _ ≤ ℓ • gaussVal (P - p (ℓ * k + u * d)) := by gcongr
        _ ≤ suppVal φ (P - p (ℓ * k + u * d)) u ℓ := by
            simpa using weight_le_suppVal_mul_pow hπ hφ hd0 hℓ u (P - p (ℓ * k + u * d)) 0
    -- the head `q k - p k`: the telescoped block from `k` up to `ℓ * k + u * d`
    have hkle : k ≤ ℓ * k + u * d :=
      le_trans (Nat.le_mul_of_pos_left k hℓ) (Nat.le_add_right _ _)
    obtain ⟨c, hc⟩ := Nat.exists_eq_add_of_le hkle
    have hqk : ((k : ℕ) : ℕ∞) ≤ suppVal φ (p (ℓ * k + u * d) - p k) u ℓ := by
      rw [hc]
      exact le_suppVal_sub hφ hd0 hℓ u p hstep k c
    have hdecomp : P - p k = (P - p (ℓ * k + u * d)) + (p (ℓ * k + u * d) - p k) := by ring
    rw [hdecomp]
    exact le_trans (le_min hPq hqk) (min_suppVal_le_suppVal_add hφ hd0 hℓ u _ _)

end ENVB

end Uniformity.Density.Leaf

/-! ## Axiom footprint -/

section AxCheck
#print axioms Uniformity.Density.Leaf.exists_graded_limit
end AxCheck
