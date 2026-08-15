/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapG.G64
import Uniformity.ChapG.G66

/-!
# Uniformity.ChapG.G67 — `hex3U_rec`, the telescoping theorem

**Chapter G, NODE G.67** (`blueprint/CHAP-G_base_cases_menus.md` §9). *The telescoping
theorem.* `hex3U` satisfies HEX3's first-step recursion — stated additively, so no
ℕ-subtraction appears:

    u(N) + ∑_k (q−1)q^(3k)·q^(2(N−3k)−2)
      = q^(2N−2) + ∑_k (q−1)q^(3k)·( u(N−3k) + (q^(N−3k) − 1)·R(N−3k) ).

DEPENDS: G.64, G.66.

**⚠ SOURCE-EVIDENCE NOTE** (blueprint's verbatim note carried forward). `EFF.HEX3.30` records
that the coefficient identity of the "step 4" collapse was verified by the 0a compiler
**numerically** (`q ∈ {2,3,5}`, `l = 1..8`, 24 cases) and by PE2's fresh route only up to
`N ≤ 40`. **This node supplies the first symbolic proof for all `l`.**

**PROOF STRATEGY (SPLIT MANDATED by the blueprint into "G.67a" + assembly).** Substituting
`hex3U`'s own definition (G.66) into each `hex3U q (N−3k)` on the RHS produces a double sum;
after cancelling the common `q^(2N−2)` and `∑_k (q−1)q^(3k)q^(2(N−3k)−2)` terms (which appear
literally identically on both sides once `hex3U` is unfolded on the LHS too), the remaining
identity is a pure coefficient-matching statement, independent of `hex3R`/`hex3U`'s
arithmetic content:

* **`coeff_collapse`, the "G.67a" node**: the coefficient of `t(N−3l) := (q^(N−3l)−1)R(N−3l)`
  collapses, i.e. `q^(3l) + (q−1)·∑_{k=1}^{l−1} q^(4l−k−1) = q^(4l−1)`. Proved via a
  self-reflection reindexing `k ↦ l − k` on `Finset.Icc 1 (l−1)` (`Finset.sum_bij'`) reducing
  it to the standard finite geometric series `(q−1)·∑_{j=1}^{n} q^j + q = q^(n+1)`
  (`geom_sum_icc`, itself a two-line induction).
* **`double_sum_collapse`**: `coeff_collapse` lifted through a sum over `l`, for an *arbitrary*
  function `g : ℕ → ℕ` in place of `t`, by induction on the sum's upper bound `K` — peeling the
  top term of three `Finset.Icc` sums at once and applying `coeff_collapse` (scaled by `q−1`)
  at each step. This isolates the whole double-sum reindexing (the blueprint's "`l = k+j`"
  substitution) into a single clean induction, decoupled from `hex3U`'s specifics.
* **Assembly (`hex3U_rec` itself)**: `unfold hex3U` on both occurrences (the outer `hex3U q N`
  and the nested `hex3U q (N−3k)`), translate the inner sum's bound
  `(N−3k−1)/3 = (N−1)/3 − k` and its summand's argument `N−3k−3j = N−3(k+j)` (both `omega`
  facts, valid since `k` ranges over `Finset.Icc 1 ((N−1)/3)`), distribute
  `(q−1)q^(3k)·(A+B+C)` into three sums (`Finset.sum_add_distrib`), and close the remaining
  piece with `double_sum_collapse` at `g l := (q^(N−3l)−1)·hex3R q (N−3l)`.

**TEETH.** `HEX3-LAW` → executable regression (aggregate only; `EFF.HEX3` §6.2 classes this
step as "weakly guarded" prior to this node).

## Status

Sorry-free, axiom-free (Lean core only).
-/

set_option linter.style.longLine false

namespace Uniformity.Density.Menu

/-- Finite geometric series in ℕ, addition form (no ℕ-truncated subtraction on the RHS):
`(q−1) · ∑_{j=1}^{n} q^j + q = q^(n+1)`. The base case of `coeff_collapse`. -/
private lemma geom_sum_icc (q : ℕ) (hq : 1 ≤ q) (n : ℕ) :
    (q - 1) * ∑ j ∈ Finset.Icc 1 n, q ^ j + q = q ^ (n + 1) := by
  have hkey : ∀ X : ℕ, (q - 1) * X + X = X * q := by
    intro X
    have h1 : q - 1 + 1 = q := by omega
    calc (q - 1) * X + X = (q - 1 + 1) * X := by ring
      _ = q * X := by rw [h1]
      _ = X * q := by ring
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ n + 1), Nat.mul_add]
    have hcol := hkey (q ^ (n + 1))
    have hpow : q ^ (n + 1) * q = q ^ (n + 1 + 1) := by ring
    omega

/-- **G.67a, the coefficient collapse.** The coefficient of `t(N−3l)` in `hex3U_rec`'s
telescoped double sum matches on both sides: `q^(3l) + (q−1)·∑_{k=1}^{l−1} q^(4l−k−1) =
q^(4l−1)`. Reduced via the self-reflection `k ↦ l − k` (a bijection `Finset.Icc 1 (l−1) →
Finset.Icc 1 (l−1)`) to `geom_sum_icc`. -/
private lemma coeff_collapse (q l : ℕ) (hq : 1 ≤ q) (hl : 1 ≤ l) :
    q ^ (3 * l) + (q - 1) * ∑ k ∈ Finset.Icc 1 (l - 1), q ^ (4 * l - k - 1) = q ^ (4 * l - 1) := by
  have hreindex : ∑ k ∈ Finset.Icc 1 (l - 1), q ^ (4 * l - k - 1)
      = ∑ k ∈ Finset.Icc 1 (l - 1), q ^ (3 * l - 1 + k) := by
    apply Finset.sum_bij' (i := fun k _ => l - k) (j := fun k _ => l - k)
    · intro k hk
      simp only [Finset.mem_Icc] at hk ⊢
      omega
    · intro k hk
      simp only [Finset.mem_Icc] at hk ⊢
      omega
    · intro k hk
      simp only [Finset.mem_Icc] at hk
      omega
    · intro k hk
      simp only [Finset.mem_Icc] at hk
      omega
    · intro k hk
      simp only [Finset.mem_Icc] at hk
      congr 1
      omega
  rw [hreindex]
  have hfactor : ∑ k ∈ Finset.Icc 1 (l - 1), q ^ (3 * l - 1 + k)
      = q ^ (3 * l - 1) * ∑ k ∈ Finset.Icc 1 (l - 1), q ^ k := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    rw [pow_add]
  rw [hfactor]
  have hgeom := geom_sum_icc q hq (l - 1)
  rw [show l - 1 + 1 = l from by omega] at hgeom
  have hmul : ((q - 1) * ∑ k ∈ Finset.Icc 1 (l - 1), q ^ k + q) * q ^ (3 * l - 1)
      = q ^ l * q ^ (3 * l - 1) := by rw [hgeom]
  rw [Nat.add_mul] at hmul
  have he1 : q ^ l * q ^ (3 * l - 1) = q ^ (4 * l - 1) := by
    rw [← pow_add]; congr 1; omega
  have he2 : q * q ^ (3 * l - 1) = q ^ (3 * l) := by
    rw [← pow_succ']; congr 1; omega
  rw [he1, he2] at hmul
  have hassoc : (q - 1) * (∑ k ∈ Finset.Icc 1 (l - 1), q ^ k) * q ^ (3 * l - 1)
      = (q - 1) * (q ^ (3 * l - 1) * ∑ k ∈ Finset.Icc 1 (l - 1), q ^ k) := by ring
  rw [hassoc] at hmul
  omega

/-- The general double-sum collapse driving `hex3U_rec`'s assembly: for any `g : ℕ → ℕ`,
`coeff_collapse` lifted through a sum over `l ∈ Finset.Icc 1 K`, by induction on `K`. This
isolates the blueprint's "`l = k+j`" double-sum reindexing into a clean induction, decoupled
from any `hex3R`/`hex3U`-specific content. -/
private lemma double_sum_collapse (q : ℕ) (hq : 1 ≤ q) (g : ℕ → ℕ) (K : ℕ) :
    (∑ k ∈ Finset.Icc 1 K, (q - 1) ^ 2 * q ^ (3 * k)
        * ∑ j ∈ Finset.Icc 1 (K - k), q ^ (4 * j - 1) * g (k + j))
      + ∑ k ∈ Finset.Icc 1 K, (q - 1) * q ^ (3 * k) * g k
    = ∑ l ∈ Finset.Icc 1 K, (q - 1) * q ^ (4 * l - 1) * g l := by
  induction K with
  | zero => simp
  | succ K ih =>
    -- peel the RHS sum
    rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ K + 1) (fun l => (q - 1) * q ^ (4 * l - 1) * g l)]
    -- peel the second LHS sum
    rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ K + 1) (fun k => (q - 1) * q ^ (3 * k) * g k)]
    -- relate the first LHS sum at K+1 to the one at K
    have hfirst : ∑ k ∈ Finset.Icc 1 (K + 1), (q - 1) ^ 2 * q ^ (3 * k)
          * ∑ j ∈ Finset.Icc 1 (K + 1 - k), q ^ (4 * j - 1) * g (k + j)
        = (∑ k ∈ Finset.Icc 1 K, (q - 1) ^ 2 * q ^ (3 * k)
            * ∑ j ∈ Finset.Icc 1 (K - k), q ^ (4 * j - 1) * g (k + j))
          + (q - 1) ^ 2 * g (K + 1) * ∑ k ∈ Finset.Icc 1 K, q ^ (4 * (K + 1) - k - 1) := by
      rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ K + 1)
        (fun k => (q - 1) ^ 2 * q ^ (3 * k) * ∑ j ∈ Finset.Icc 1 (K + 1 - k), q ^ (4 * j - 1) * g (k + j))]
      have htop : (q - 1) ^ 2 * q ^ (3 * (K + 1))
          * ∑ j ∈ Finset.Icc 1 (K + 1 - (K + 1)), q ^ (4 * j - 1) * g (K + 1 + j) = 0 := by
        simp
      rw [htop, add_zero]
      have hpointwise : ∀ k ∈ Finset.Icc 1 K,
          (q - 1) ^ 2 * q ^ (3 * k) * ∑ j ∈ Finset.Icc 1 (K + 1 - k), q ^ (4 * j - 1) * g (k + j)
            = (q - 1) ^ 2 * q ^ (3 * k) * ∑ j ∈ Finset.Icc 1 (K - k), q ^ (4 * j - 1) * g (k + j)
              + (q - 1) ^ 2 * q ^ (3 * k) * (q ^ (4 * (K - k + 1) - 1) * g (K + 1)) := by
        intro k hk
        simp only [Finset.mem_Icc] at hk
        rw [show K + 1 - k = (K - k) + 1 from by omega,
          Finset.sum_Icc_succ_top (by omega : 1 ≤ (K - k) + 1)]
        rw [show k + (K - k + 1) = K + 1 from by omega, mul_add]
      rw [Finset.sum_congr rfl hpointwise, Finset.sum_add_distrib]
      congr 1
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      simp only [Finset.mem_Icc] at hk
      rw [show K - k + 1 = K + 1 - k from by omega]
      have hexp : 3 * k + (4 * (K + 1 - k) - 1) = 4 * (K + 1) - k - 1 := by omega
      calc (q - 1) ^ 2 * q ^ (3 * k) * (q ^ (4 * (K + 1 - k) - 1) * g (K + 1))
          = (q - 1) ^ 2 * g (K + 1) * (q ^ (3 * k) * q ^ (4 * (K + 1 - k) - 1)) := by ring
        _ = (q - 1) ^ 2 * g (K + 1) * q ^ (3 * k + (4 * (K + 1 - k) - 1)) := by rw [pow_add]
        _ = (q - 1) ^ 2 * g (K + 1) * q ^ (4 * (K + 1) - k - 1) := by rw [hexp]
    rw [hfirst]
    have hcc := coeff_collapse q (K + 1) hq (by omega)
    have hcc2 : (q - 1) * q ^ (3 * (K + 1)) + (q - 1) ^ 2 * ∑ k ∈ Finset.Icc 1 K, q ^ (4 * (K + 1) - k - 1)
        = (q - 1) * q ^ (4 * (K + 1) - 1) := by
      have := congrArg (fun x => (q - 1) * x) hcc
      simp only [show K + 1 - 1 = K from by omega] at this
      rw [Nat.mul_add] at this
      have hsq : (q - 1) * ((q - 1) * ∑ k ∈ Finset.Icc 1 K, q ^ (4 * (K + 1) - k - 1))
          = (q - 1) ^ 2 * ∑ k ∈ Finset.Icc 1 K, q ^ (4 * (K + 1) - k - 1) := by ring
      rw [hsq] at this
      exact this
    have hihe := ih
    nlinarith [hihe, hcc2]

/-- **G.67, the telescoping theorem.** `hex3U` satisfies HEX3's first-step recursion, stated
additively so no ℕ-truncated subtraction appears bare. Assembled from `double_sum_collapse`
(hence `coeff_collapse`, "G.67a") after unfolding `hex3U`'s own definition on both the outer
and the nested occurrence. -/
theorem hex3U_rec (q N : ℕ) (hq : 2 ≤ q) (hN : 2 ≤ N) :
    hex3U q N + ∑ k ∈ Finset.Icc 1 ((N - 1) / 3),
        (q - 1) * q ^ (3 * k) * q ^ (2 * (N - 3 * k) - 2)
      = q ^ (2 * N - 2) + ∑ k ∈ Finset.Icc 1 ((N - 1) / 3),
          (q - 1) * q ^ (3 * k) * (hex3U q (N - 3 * k)
            + (q ^ (N - 3 * k) - 1) * hex3R q (N - 3 * k)) := by
  unfold hex3U
  set K := (N - 1) / 3 with hKdef
  -- distribute (q-1)*q^(3k)*(A + B + C) into three sums on the RHS
  have hdistrib : ∀ k ∈ Finset.Icc 1 K,
      (q - 1) * q ^ (3 * k) *
        (q ^ (2 * (N - 3 * k) - 2)
            + (q - 1) * ∑ j ∈ Finset.Icc 1 ((N - 3 * k - 1) / 3),
                q ^ (4 * j - 1) * ((q ^ (N - 3 * k - 3 * j) - 1) * hex3R q (N - 3 * k - 3 * j))
          + (q ^ (N - 3 * k) - 1) * hex3R q (N - 3 * k))
        = (q - 1) * q ^ (3 * k) * q ^ (2 * (N - 3 * k) - 2)
          + ((q - 1) ^ 2 * q ^ (3 * k)
              * ∑ j ∈ Finset.Icc 1 (K - k),
                  q ^ (4 * j - 1) * ((q ^ (N - 3 * (k + j)) - 1) * hex3R q (N - 3 * (k + j)))
            + (q - 1) * q ^ (3 * k) * ((q ^ (N - 3 * k) - 1) * hex3R q (N - 3 * k))) := by
    intro k hk
    simp only [Finset.mem_Icc] at hk
    have hbound : (N - 3 * k - 1) / 3 = K - k := by
      rw [hKdef]; omega
    have harg : ∀ j ∈ Finset.Icc 1 (K - k), N - 3 * k - 3 * j = N - 3 * (k + j) := by
      intro j hj
      simp only [Finset.mem_Icc] at hj
      rw [hKdef] at hj
      omega
    rw [hbound, Finset.sum_congr rfl (fun j hj => by rw [harg j hj])]
    ring
  rw [Finset.sum_congr rfl hdistrib]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  have hdsc := double_sum_collapse q (by omega) (fun l => (q ^ (N - 3 * l) - 1) * hex3R q (N - 3 * l)) K
  have hmulsum : (q - 1) * ∑ k ∈ Finset.Icc 1 K, q ^ (4 * k - 1) * ((q ^ (N - 3 * k) - 1) * hex3R q (N - 3 * k))
      = ∑ k ∈ Finset.Icc 1 K, (q - 1) * q ^ (4 * k - 1) * ((q ^ (N - 3 * k) - 1) * hex3R q (N - 3 * k)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    ring
  omega

end Uniformity.Density.Menu

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Menu.hex3U_rec

end AxCheck
