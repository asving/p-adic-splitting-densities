/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapH.H114
import Uniformity.ChapH.H118
import Uniformity.ChapG.G14

/-!
# Uniformity.ChapH.H121d — the content-weighted β census

**Chapter H, NODE H.121d** [theorem] (`blueprint/CHAP-H_general_induction.md`, AMENDMENT A-H.6
§5 — the node this amendment adds, replacing the committed step 3's unquantified *"genre
bookkeeping (slopes × windows ≤ polynomial in `N`)"*, which is exactly what finding F-H17.2
killed).  The PRICING step of H.121 clause (iii):

    Σ_{c : β state at window N}  Q^(betaContent c k(c))   ≤   (1/3) · Q^(m(N−1)) .

Stated (per the frozen signature) as a sum over the content `D` of the number of β states
admitting SOME child of content `D` — an upper bound on the amendment's per-state sum, so the
form proved here is the stronger one.

## The proof, and how it differs from the amendment's sketch

A-H.6 §5's sketch prices the census by the EXHAUSTIVE β polygon classification at `m = 3`
(shapes A/B/C, closed value `Q/(Q²+Q+1) ≤ 2/7`).  This file proves the signed bound by a
CHEAPER route that needs no polygon classification at all — only the child event's own
divisibility clauses, read on the three coefficient digits:

1. **§3.** At `m = 3` a β child has multiplicity `μ = 2` (H.118's `betaChild_mult_lt`, plus
   H.109's `2 ≤ μ`).  Write `W := π^k·w` for the centre (any lift `w` of `z`; `HasChildAt`
   quantifies over ALL lifts, which is what lets one `w` serve a whole cell).  The recentred
   coefficients factor as `b_j = π^(jk)·t_j` with `t₂ = a₂ + 3W`, `t₁ = a₁ + 2a₂W + 3W²`,
   `t₀ = a₀ + a₁W + a₂W² + W³` (§2), so the event `π^D ∣ b₂`, `π^(D+1) ∤ b₂`,
   `π^(D+1) ∣ b₁`, `π^(D+1) ∣ b₀` becomes
   `v(t₂) = D − 2k` EXACTLY, `π^(D+1−k) ∣ t₁`, `π^(D+1) ∣ t₀`.
2. **The structural constraint `D ≥ 2k + 1`** falls out of the same clause: `a₂ ∈ 𝔪` and
   `π ∣ W` give `v(b₂) ≥ 2k + 1`, while `π^(D+1) ∤ b₂` gives `v(b₂) ≤ D`.  (This is what
   replaces the polygon case list: it is the only relation between `D` and `k` the count
   needs.)
3. **§4.** The three conditions are TRIANGULAR, so `c ↦ (t₂, t₁, t₀)` is injective and lands
   in `exactSet(D−2k) × dvdSet(D+1−k) × dvdSet(D+1)`; ChapG's G.14 counts give the cell
   `(Q−1)·Q^(N−(D−2k)−1) · Q^(N−(D+1−k)) · Q^(N−(D+1)) = (Q−1)·Q^(3(N−1))·Q^(3k)·Q^(−3D)`.
4. **§1.** Summing over the `Q − 1` centres and over `1 ≤ k`, `2k + 1 ≤ D` and weighting by
   `Q^D` gives `Σ (Q−1)²Q^(3k)Q^(−2D) = 1/(Q+1) ≤ 1/3`.

`1/(Q+1)` is the constant this route certifies; the SHARP value is A-H.6's `Q/(Q²+Q+1) ≤ 2/7`
(the two agree in order and the crude one is TIGHT at `Q = 2`, where it equals the signed
`1/3` exactly).  Both are `≤ 1/3`, so the signed literal is proved with the margin the
amendment intended, and no unsigned support lemma and no new axiom were needed.

At `m = 2` the β set is EMPTY (H.118's `betaChild_mult_lt` plus `2 ≤ μ` would need
`2 ≤ μ < 2`) and every summand is `0` — the same emptiness `H122m2.not_isBetaState_two`
records, re-derived here from H.118 as the signed DEPENDS prescribes (this file does NOT
import the `m = 2` H.122 leg).

⚠ **Why `Q − 1` twice.**  The bound `1/3` is TIGHT at `Q = 2`: relaxing the centre count from
`Q − 1` to `Q`, or the top digit's EXACT-valuation count `(Q−1)Q^r` to the merely-divisible
`Q^(r+1)`, each pushes the total to `2/3 > 1/3`.  Both refinements are therefore load-bearing.

⚠ **S-1 fence.**  Everything here is the CONSERVATIVE cluster carrier (`u_{m,1}`'s bucket
census), never the semantic `undecidedCount` (finding F-2).

DEPENDS: H.106 (`ClusterState`), H.107/H.108 (`betaContent`, `betaContent_le`,
`IsDrainState`), H.109 (`HasChildAt`), H.110/H.111 (`IsBetaState`), H.112
(`exists_proj_eq`, `residue_surj`, `one_le_window_of_not_drain`, `mult_le_of_hasChildAt` via
H.118), H.114 (`instFiniteClusterState`), H.118 (`betaChild_mult_lt`) · ChapG G.14
(`dvdSet`, `exactSet`, `card_dvdSet`, `card_exactSet_add`) · landed `monicPoly`, `proj`,
`residueCard`, `two_le_residueCard`, `mem_maximalIdeal_pow_iff_dvd`.

**ENVIRONMENT — ENV-H17** + `[Finite (ResidueField O)]` + `[IsAdicComplete (maximalIdeal O) O]`
+ `π` explicit, every binder INLINE; `(O : Type)` in the signed statement (the universe the
H.121/H.122 stubs pin).  `hN` is part of the FROZEN signature and is not consumed (the bound
is trivially true at `N = 0`, where the sum is empty).

## TEETH (GC-8)

`verification/AH6_beta_envelope_check.py` (54/54, exit 0, re-run 2026-08-16 at landing):
check `C4` (the finite-`N` census never exceeds `Q/(Q²+Q+1)`, `q ∈ {2,3}`, `N ≤ 40`, exact),
`D1–D4` (the closed form, per polygon shape) and `D5` (`Q`-monotonicity to `Q = 199`).  §6
reproduces the two constant comparisons this file's proof actually turns on.

## Status

Sorry-free, axiom-free (Lean core only); footprint printed at the end of the file.
-/

set_option linter.style.longLine false

namespace Uniformity.Density.Induction

open IsLocalRing Uniformity.Density.Menu

/-! ## 1. The arithmetic core: a coupled double geometric sum -/

/-- Every partial geometric sum is below the limit `(1 − t)⁻¹`. -/
private theorem geom_partial_le (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t < 1) (n : ℕ) :
    ∑ i ∈ Finset.range n, t ^ i ≤ (1 - t)⁻¹ := by
  have hpos : (0:ℝ) < 1 - t := by linarith
  have key : ∀ j : ℕ, (∑ i ∈ Finset.range j, t ^ i) * (1 - t) = 1 - t ^ j := by
    intro j
    induction j with
    | zero => simp
    | succ j ih => rw [Finset.sum_range_succ, add_mul, ih]; ring
  have h1 : (∑ i ∈ Finset.range n, t ^ i) * (1 - t) ≤ 1 := by
    rw [key n]
    have : (0:ℝ) ≤ t ^ n := pow_nonneg ht0 n
    linarith
  rw [inv_eq_one_div, le_div_iff₀ hpos]
  linarith

/-- The tail of a geometric sum with ratio `Q^(−p)`, from `e` up. -/
private theorem geom_tail_le (Q : ℕ) (hQ : 2 ≤ Q) (p e n : ℕ) (hp : 1 ≤ p) :
    ∑ D ∈ Finset.Ico e n, ((Q:ℝ) ^ (p * D))⁻¹
      ≤ ((Q:ℝ) ^ (p * e))⁻¹ * (1 - ((Q:ℝ) ^ p)⁻¹)⁻¹ := by
  have hQR : (2:ℝ) ≤ (Q:ℝ) := by exact_mod_cast hQ
  have hQ0 : (0:ℝ) < (Q:ℝ) := by linarith
  have hpp : (1:ℝ) < (Q:ℝ) ^ p := by
    calc (1:ℝ) < (Q:ℝ) ^ 1 := by rw [pow_one]; linarith
      _ ≤ (Q:ℝ) ^ p := pow_le_pow_right₀ (by linarith) hp
  set t : ℝ := ((Q:ℝ) ^ p)⁻¹ with ht
  have ht0 : 0 ≤ t := by rw [ht]; positivity
  have ht1 : t < 1 := by
    rw [ht, inv_lt_one_iff₀]
    exact Or.inr hpp
  have hterm : ∀ i : ℕ, ((Q:ℝ) ^ (p * (e + i)))⁻¹ = ((Q:ℝ) ^ (p * e))⁻¹ * t ^ i := by
    intro i
    rw [ht, Nat.mul_add, pow_add, mul_inv, inv_pow, ← pow_mul]
  rw [Finset.sum_Ico_eq_sum_range]
  calc ∑ i ∈ Finset.range (n - e), ((Q:ℝ) ^ (p * (e + i)))⁻¹
      = ∑ i ∈ Finset.range (n - e), ((Q:ℝ) ^ (p * e))⁻¹ * t ^ i :=
        Finset.sum_congr rfl fun i _ => hterm i
    _ = ((Q:ℝ) ^ (p * e))⁻¹ * ∑ i ∈ Finset.range (n - e), t ^ i := by
        rw [Finset.mul_sum]
    _ ≤ ((Q:ℝ) ^ (p * e))⁻¹ * (1 - t)⁻¹ := by
        refine mul_le_mul_of_nonneg_left (geom_partial_le t ht0 ht1 _) (by positivity)

/-- **The coupled double geometric sum.**  Exactly the shape the census assembles to: the
slope `k` runs from `1`, the content `D` runs from `2k + 1` (which is the structural constraint
`D ≥ 2k + 1` proved in §3), and the summand is the per-cell digit count times `Q^D`.  The
closed value is `1/(Q+1)`, so the bound `1/3` is TIGHT at `Q = 2` (which is why the `z ≠ 0`
count `Q − 1` and the EXACT-digit factor `Q − 1` on the top coefficient are both indispensable:
either one relaxed to `Q` overshoots `1/3` at `Q = 2`). -/
private theorem census_geom_le (Q : ℕ) (hQ : 2 ≤ Q) (N : ℕ) :
    ∑ k ∈ Finset.Ico 1 N, ∑ D ∈ Finset.Ico (2 * k + 1) N,
        ((Q:ℝ) - 1) ^ 2 * (Q:ℝ) ^ (3 * k) * ((Q:ℝ) ^ (2 * D))⁻¹ ≤ 1 / 3 := by
  have hQR : (2:ℝ) ≤ (Q:ℝ) := by exact_mod_cast hQ
  have hQ0 : (0:ℝ) < (Q:ℝ) := by linarith
  have hQ1 : (0:ℝ) < (Q:ℝ) - 1 := by linarith
  have hQ2 : (0:ℝ) < (Q:ℝ) ^ 2 - 1 := by nlinarith
  set A : ℝ := (1 - ((Q:ℝ) ^ 2)⁻¹)⁻¹ with hA
  set B : ℝ := (1 - ((Q:ℝ) ^ 1)⁻¹)⁻¹ with hB
  have hQ0' : (Q:ℝ) ≠ 0 := ne_of_gt hQ0
  have hAv : A = (Q:ℝ) ^ 2 / ((Q:ℝ) ^ 2 - 1) := by
    have hstep : (1 - ((Q:ℝ) ^ 2)⁻¹) = ((Q:ℝ) ^ 2 - 1) / (Q:ℝ) ^ 2 := by field_simp
    rw [hA, hstep, inv_div]
  have hBv : B = (Q:ℝ) / ((Q:ℝ) - 1) := by
    have hstep : (1 - ((Q:ℝ) ^ 1)⁻¹) = ((Q:ℝ) - 1) / (Q:ℝ) := by
      rw [pow_one]; field_simp
    rw [hB, hstep, inv_div]
  have hA0 : 0 ≤ A := by rw [hAv]; positivity
  -- the inner (content) sum, per slope
  have hinner : ∀ k : ℕ, ∑ D ∈ Finset.Ico (2 * k + 1) N,
        ((Q:ℝ) - 1) ^ 2 * (Q:ℝ) ^ (3 * k) * ((Q:ℝ) ^ (2 * D))⁻¹
      ≤ ((Q:ℝ) - 1) ^ 2 * A * ((Q:ℝ) ^ (k + 2))⁻¹ := by
    intro k
    have hc0 : (0:ℝ) ≤ ((Q:ℝ) - 1) ^ 2 * (Q:ℝ) ^ (3 * k) := by positivity
    have hsplit : (Q:ℝ) ^ (2 * (2 * k + 1)) = (Q:ℝ) ^ (3 * k) * (Q:ℝ) ^ (k + 2) := by
      rw [← pow_add]; congr 1; omega
    have hpow : (Q:ℝ) ^ (3 * k) * ((Q:ℝ) ^ (2 * (2 * k + 1)))⁻¹ = ((Q:ℝ) ^ (k + 2))⁻¹ := by
      rw [hsplit, mul_inv, ← mul_assoc, mul_inv_cancel₀ (ne_of_gt (pow_pos hQ0 (3 * k))),
        one_mul]
    calc ∑ D ∈ Finset.Ico (2 * k + 1) N,
          ((Q:ℝ) - 1) ^ 2 * (Q:ℝ) ^ (3 * k) * ((Q:ℝ) ^ (2 * D))⁻¹
        = (((Q:ℝ) - 1) ^ 2 * (Q:ℝ) ^ (3 * k))
            * ∑ D ∈ Finset.Ico (2 * k + 1) N, ((Q:ℝ) ^ (2 * D))⁻¹ := by
          rw [Finset.mul_sum]
      _ ≤ (((Q:ℝ) - 1) ^ 2 * (Q:ℝ) ^ (3 * k))
            * (((Q:ℝ) ^ (2 * (2 * k + 1)))⁻¹ * A) :=
          mul_le_mul_of_nonneg_left (geom_tail_le Q hQ 2 (2 * k + 1) N (by omega)) hc0
      _ = ((Q:ℝ) - 1) ^ 2 * A * ((Q:ℝ) ^ (k + 2))⁻¹ := by
          rw [← hpow]; ring
  -- the outer (slope) sum
  have houter : ∑ k ∈ Finset.Ico 1 N, ((Q:ℝ) - 1) ^ 2 * A * ((Q:ℝ) ^ (k + 2))⁻¹
      = (((Q:ℝ) - 1) ^ 2 * A * ((Q:ℝ) ^ 2)⁻¹)
          * ∑ k ∈ Finset.Ico 1 N, ((Q:ℝ) ^ (1 * k))⁻¹ := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [pow_add, mul_inv, one_mul]
    ring
  have hc1 : (0:ℝ) ≤ ((Q:ℝ) - 1) ^ 2 * A * ((Q:ℝ) ^ 2)⁻¹ := by positivity
  calc ∑ k ∈ Finset.Ico 1 N, ∑ D ∈ Finset.Ico (2 * k + 1) N,
        ((Q:ℝ) - 1) ^ 2 * (Q:ℝ) ^ (3 * k) * ((Q:ℝ) ^ (2 * D))⁻¹
      ≤ ∑ k ∈ Finset.Ico 1 N, ((Q:ℝ) - 1) ^ 2 * A * ((Q:ℝ) ^ (k + 2))⁻¹ :=
        Finset.sum_le_sum fun k _ => hinner k
    _ = (((Q:ℝ) - 1) ^ 2 * A * ((Q:ℝ) ^ 2)⁻¹)
          * ∑ k ∈ Finset.Ico 1 N, ((Q:ℝ) ^ (1 * k))⁻¹ := houter
    _ ≤ (((Q:ℝ) - 1) ^ 2 * A * ((Q:ℝ) ^ 2)⁻¹) * (((Q:ℝ) ^ (1 * 1))⁻¹ * B) :=
        mul_le_mul_of_nonneg_left (geom_tail_le Q hQ 1 1 N (by omega)) hc1
    _ = 1 / ((Q:ℝ) + 1) := by
        rw [hAv, hBv]
        field_simp
        ring
    _ ≤ 1 / 3 := one_div_le_one_div_of_le (by norm_num) (by linarith)

/-! ## 2. The cubic recentring, coefficient by coefficient

At `m = 3` the recentring `x ↦ π^k (y + w)` of `f = X³ + a₂X² + a₁X + a₀` is computed once and
for all.  Writing `W := π^k · w` for the (valuation-`k`) CENTRE, the four coefficients are

    b₀ = a₀ + a₁W + a₂W² + W³,   b₁ = π^k·(a₁ + 2a₂W + 3W²),
    b₂ = π^(2k)·(a₂ + 3W),       b₃ = π^(3k),

i.e. `b_j = π^(jk) · t_j` with `t_j` the coefficients of the plain Taylor shift by `W`.  The
`π^(jk)` is H.112's ghost divisibility made explicit; the `t_j` are what the census counts. -/

section Cubic

variable {O : Type*} [CommRing O]

open Polynomial

/-- The cubic recentring, expanded. -/
private theorem comp_cubic_eq (a : Fin 3 → O) (u w : O) :
    (monicPoly a).comp (C u * (X + C w))
      = C (a 0 + a 1 * (u * w) + a 2 * (u * w) ^ 2 + (u * w) ^ 3)
        + C (u * (a 1 + 2 * a 2 * (u * w) + 3 * (u * w) ^ 2)) * X
        + C (u ^ 2 * (a 2 + 3 * (u * w))) * X ^ 2
        + C (u ^ 3) * X ^ 3 := by
  simp only [monicPoly, Fin.sum_univ_three, add_comp, mul_comp, pow_comp, C_comp, X_comp,
    C_add, C_mul, C_pow, map_ofNat, Fin.isValue, Fin.val_zero, Fin.val_one, Fin.val_two,
    pow_zero, pow_one, mul_one]
  ring

private theorem comp_cubic_coeff_zero (a : Fin 3 → O) (u w : O) :
    ((monicPoly a).comp (C u * (X + C w))).coeff 0
      = a 0 + a 1 * (u * w) + a 2 * (u * w) ^ 2 + (u * w) ^ 3 := by
  rw [comp_cubic_eq]
  simp only [coeff_add, coeff_C_mul, coeff_C, coeff_X, coeff_X_pow]
  norm_num

private theorem comp_cubic_coeff_one (a : Fin 3 → O) (u w : O) :
    ((monicPoly a).comp (C u * (X + C w))).coeff 1
      = u * (a 1 + 2 * a 2 * (u * w) + 3 * (u * w) ^ 2) := by
  rw [comp_cubic_eq]
  simp only [coeff_add, coeff_C_mul, coeff_C, coeff_X, coeff_X_pow]
  norm_num

private theorem comp_cubic_coeff_two (a : Fin 3 → O) (u w : O) :
    ((monicPoly a).comp (C u * (X + C w))).coeff 2
      = u ^ 2 * (a 2 + 3 * (u * w)) := by
  rw [comp_cubic_eq]
  simp only [coeff_add, coeff_C_mul, coeff_C, coeff_X, coeff_X_pow]
  norm_num

end Cubic

/-! ## 3. The cell data: what a β child event says about the three digits

Fix a slope `k`, a centre residue `z ≠ 0` and a LIFT `w` of `z` — any lift, because
`HasChildAt` quantifies over all of them (H.109), which is exactly why one `w` can be chosen
per `(k, z)` and reused for every state in the cell.  At `m = 3` a β state's child has
multiplicity `μ = 2` (H.118's `betaChild_mult_lt` plus `2 ≤ μ`), so the event reads

    π^D ∣ b₂ and π^(D+1) ∤ b₂,     π^(D+1) ∣ b₁,     π^(D+1) ∣ b₀,

with `D = betaContent c k`.  Dividing out the ghost factors `b_j = π^(jk)·t_j` (§2) this is a
congruence for each of the three digits — and `π^(D+1) ∤ π^(2k)·t₂` with `π ∣ t₂` (both `a₂`
and `3W` are in `𝔪`) forces `D ≥ 2k + 1`, the structural constraint the arithmetic of §1
consumes. -/

section Cell

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)]

open Polynomial

/-- The three shifted digits of a state at centre `A`: `(t₂, t₁, t₀)` read on classes.  This
is the census map — §4 shows it is injective and lands in a product of valuation strata. -/
private def betaKey {N : ℕ} (c : ClusterState O 3 N) (A : Res O N) :
    Res O N × Res O N × Res O N :=
  (c.1 2 + 3 * A, c.1 1 + 2 * c.1 2 * A + 3 * A ^ 2,
    c.1 0 + c.1 1 * A + c.1 2 * A ^ 2 + A ^ 3)

/-- The centre class `π^k · w` at level `N`. -/
private def ctr (π : O) (N k : ℕ) (w : O) : Res O N :=
  Ideal.Quotient.mk _ (π ^ k * w)

omit [Finite (ResidueField O)] in
/-- Every cluster state has a lift whose coordinates lie in `𝔪` (its defining property). -/
private theorem exists_lift_mem {m N : ℕ} (c : ClusterState O m N) :
    ∃ a : Fin m → O, proj O m N a = c.1 ∧ ∀ i, a i ∈ maximalIdeal O := by
  classical
  have h : ∀ i : Fin m, ∃ x : O, x ∈ maximalIdeal O ∧
      Ideal.Quotient.mk ((maximalIdeal O) ^ N) x = c.1 i := by
    intro i
    obtain ⟨b, hb, hbe⟩ :=
      (Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).1 (c.2 i)
    exact ⟨b, hb, hbe⟩
  choose a ha hae using h
  exact ⟨a, funext hae, ha⟩

omit [Finite (ResidueField O)] in
private theorem mem_dvdSet_of_dvd {π : O} {N s : ℕ} {x : O} (h : π ^ s ∣ x) :
    (Ideal.Quotient.mk ((maximalIdeal O) ^ N) x) ∈ dvdSet π s N := by
  obtain ⟨y, rfl⟩ := h
  exact ⟨y, rfl⟩

private theorem dvd_of_mem_dvdSet {π : O} (hπ : Irreducible π) {N s : ℕ} (hs : s ≤ N) {x : O}
    (h : (Ideal.Quotient.mk ((maximalIdeal O) ^ N) x) ∈ dvdSet π s N) : π ^ s ∣ x := by
  obtain ⟨y, hy⟩ := h
  have hsub : x - π ^ s * y ∈ (maximalIdeal O) ^ N := Ideal.Quotient.eq.1 hy.symm
  have hN : π ^ N ∣ (x - π ^ s * y) := (mem_maximalIdeal_pow_iff_dvd hπ N _).1 hsub
  have h2 : π ^ s ∣ (x - π ^ s * y) := dvd_trans (pow_dvd_pow π hs) hN
  have h3 : π ^ s ∣ (x - π ^ s * y) + π ^ s * y := dvd_add h2 (Dvd.intro y rfl)
  simpa using h3

/-- **The β cell data.**  Everything §4 needs about a β state with a child at `(k, z)` and
content `D`, read at an arbitrary lift `w` of `z`. -/
private theorem beta_cell_facts {π : O} (hπ : Irreducible π) {N : ℕ}
    {c : ClusterState O 3 N} (hβ : IsBetaState π c) {μ k : ℕ} {z : ResidueField O}
    (hch : HasChildAt π c μ k z) {D : ℕ} (hD : betaContent c k = D)
    (w : O) (hw : residue O w = z) :
    1 ≤ k ∧ 2 * k + 1 ≤ D ∧ D + 1 ≤ N ∧
      (betaKey c (ctr π N k w)).1 ∈ exactSet π (D - 2 * k) N ∧
      (betaKey c (ctr π N k w)).2.1 ∈ dvdSet π (D + 1 - k) N ∧
      (betaKey c (ctr π N k w)).2.2 ∈ dvdSet π (D + 1) N := by
  classical
  obtain ⟨a, ha, hmem⟩ := exists_lift_mem c
  have hπ0 : π ≠ 0 := hπ.ne_zero
  -- the child multiplicity is exactly `2` at `m = 3`
  have hμ3 : μ < 3 := betaChild_mult_lt hβ hch
  have hμ2 : μ = 2 := by have := hch.1; omega
  subst hμ2
  obtain ⟨-, hk, -, hall⟩ := hch
  obtain ⟨h1, h2, h3⟩ := hall a w ha hw
  rw [hD] at h1 h2 h3
  -- the window
  have hN : 1 ≤ N := one_le_window_of_not_drain c hβ.1
  have hDN : D + 1 ≤ N := by
    have := betaContent_le (by omega : 1 ≤ 3) hN c hβ.1 k
    omega
  -- the three shifted digits, as ring elements
  set W : O := π ^ k * w with hWdef
  set t2 : O := a 2 + 3 * W with ht2
  set t1 : O := a 1 + 2 * a 2 * W + 3 * W ^ 2 with ht1
  set t0 : O := a 0 + a 1 * W + a 2 * W ^ 2 + W ^ 3 with ht0
  have hb2 : ((monicPoly a).comp (C (π ^ k) * (X + C w))).coeff 2 = π ^ (2 * k) * t2 := by
    rw [comp_cubic_coeff_two a (π ^ k) w, ht2, hWdef, ← pow_mul, Nat.mul_comm k 2]
  have hb1 : ((monicPoly a).comp (C (π ^ k) * (X + C w))).coeff 1 = π ^ k * t1 := by
    rw [comp_cubic_coeff_one a (π ^ k) w, ht1, hWdef]
  have hb0 : ((monicPoly a).comp (C (π ^ k) * (X + C w))).coeff 0 = t0 := by
    rw [comp_cubic_coeff_zero a (π ^ k) w, ht0, hWdef]
  -- `π ∣ t₂`: both `a₂` and `3W` are in `𝔪`
  have hdvd_a2 : π ∣ a 2 := by
    have := hmem 2
    rw [← pow_one (maximalIdeal O)] at this
    simpa using (mem_maximalIdeal_pow_iff_dvd hπ 1 (a 2)).1 this
  have hdvd_W : π ∣ W := by
    rw [hWdef]
    exact Dvd.dvd.mul_right (dvd_pow_self π (by omega : k ≠ 0)) w
  have hdvd_t2 : π ∣ t2 := by
    rw [ht2]
    exact dvd_add hdvd_a2 (Dvd.dvd.mul_left hdvd_W 3)
  -- STRUCTURE: `D ≥ 2k + 1`
  have hlow : 2 * k + 1 ≤ D := by
    by_contra hcon
    apply h3
    rw [hb2]
    refine dvd_trans (pow_dvd_pow π (by omega : D + 1 ≤ 2 * k + 1)) ?_
    rw [pow_succ]
    exact mul_dvd_mul (dvd_refl _) hdvd_t2
  refine ⟨hk, hlow, hDN, ?_, ?_, ?_⟩
  · -- the top digit sits at valuation EXACTLY `D − 2k`
    have hcanc : π ^ (D - 2 * k) ∣ t2 := by
      have hsplit : π ^ D = π ^ (2 * k) * π ^ (D - 2 * k) := by
        rw [← pow_add]; congr 1; omega
      have := h1 2
      rw [hb2, hsplit] at this
      exact (mul_dvd_mul_iff_left (pow_ne_zero (2 * k) hπ0)).1 this
    have hexact : ¬ π ^ (D - 2 * k + 1) ∣ t2 := by
      intro hcon
      apply h3
      rw [hb2]
      have hsplit : π ^ (D + 1) = π ^ (2 * k) * π ^ (D - 2 * k + 1) := by
        rw [← pow_add]; congr 1; omega
      rw [hsplit]
      exact mul_dvd_mul (dvd_refl _) hcon
    have hkey : (betaKey c (ctr π N k w)).1 = Ideal.Quotient.mk ((maximalIdeal O) ^ N) t2 := by
      have hc2 : c.1 2 = Ideal.Quotient.mk ((maximalIdeal O) ^ N) (a 2) := by rw [← ha]; rfl
      simp [betaKey, ctr, ht2, hWdef, hc2, map_add, map_mul, map_ofNat]
    rw [hkey]
    refine ⟨mem_dvdSet_of_dvd hcanc, ?_⟩
    intro hcon
    exact hexact (dvd_of_mem_dvdSet hπ (by omega) hcon)
  · -- the middle digit
    have hcanc : π ^ (D + 1 - k) ∣ t1 := by
      have hsplit : π ^ (D + 1) = π ^ k * π ^ (D + 1 - k) := by
        rw [← pow_add]; congr 1; omega
      have := h2 1 (by omega)
      rw [hb1, hsplit] at this
      exact (mul_dvd_mul_iff_left (pow_ne_zero k hπ0)).1 this
    have hkey : (betaKey c (ctr π N k w)).2.1
        = Ideal.Quotient.mk ((maximalIdeal O) ^ N) t1 := by
      have hc1 : c.1 1 = Ideal.Quotient.mk ((maximalIdeal O) ^ N) (a 1) := by rw [← ha]; rfl
      have hc2 : c.1 2 = Ideal.Quotient.mk ((maximalIdeal O) ^ N) (a 2) := by rw [← ha]; rfl
      simp [betaKey, ctr, ht1, hWdef, hc1, hc2, map_add, map_mul, map_pow, map_ofNat]
    rw [hkey]
    exact mem_dvdSet_of_dvd hcanc
  · -- the bottom digit
    have hcanc : π ^ (D + 1) ∣ t0 := by
      have := h2 0 (by omega)
      rwa [hb0] at this
    have hkey : (betaKey c (ctr π N k w)).2.2
        = Ideal.Quotient.mk ((maximalIdeal O) ^ N) t0 := by
      have hc0 : c.1 0 = Ideal.Quotient.mk ((maximalIdeal O) ^ N) (a 0) := by rw [← ha]; rfl
      have hc1 : c.1 1 = Ideal.Quotient.mk ((maximalIdeal O) ^ N) (a 1) := by rw [← ha]; rfl
      have hc2 : c.1 2 = Ideal.Quotient.mk ((maximalIdeal O) ^ N) (a 2) := by rw [← ha]; rfl
      simp [betaKey, ctr, ht0, hWdef, hc0, hc1, hc2, map_add, map_mul, map_pow]
    rw [hkey]
    exact mem_dvdSet_of_dvd hcanc

end Cell

/-! ## 4. The cell count: one slope, one centre

The three conditions of §3 are TRIANGULAR — the top digit's coset is absolute, the middle
digit's depends on the top one, the bottom digit's on both — so the census map
`c ↦ (t₂, t₁, t₀)` is injective (read the coordinates back in that order) and lands in a
PRODUCT of valuation strata.  Hence the cell is at most

    #exactSet(D − 2k) · #dvdSet(D + 1 − k) · #dvdSet(D + 1)
      = (Q − 1)·Q^(N−(D−2k)−1) · Q^(N−(D+1−k)) · Q^(N−(D+1)),

which is `(Q − 1)·Q^(3(N−1))·Q^(3k)·Q^(−3D)`. -/

section Count

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)]

private theorem card_dvdSet' {π : O} (hπ : Irreducible π) {s N : ℕ} (h : s ≤ N) :
    Nat.card (dvdSet π s N) = residueCard O ^ (N - s) := by
  have h2 := card_dvdSet (O := O) (π := π) hπ (k := s) (r := N - s)
  rwa [show s + (N - s) = N by omega] at h2

private theorem card_exactSet' {π : O} (hπ : Irreducible π) {s N : ℕ} (h : s + 1 ≤ N) :
    Nat.card (exactSet π s N) = (residueCard O - 1) * residueCard O ^ (N - s - 1) := by
  have h2 := card_exactSet_add (O := O) (π := π) hπ (k := s) (r := N - s - 1)
  rw [show s + (N - s - 1) + 1 = N by omega] at h2
  have hQ : 1 ≤ residueCard O := residueCard_pos O
  have hrw : residueCard O ^ (N - s - 1 + 1)
      = (residueCard O - 1) * residueCard O ^ (N - s - 1) + residueCard O ^ (N - s - 1) := by
    rw [pow_succ]
    have hs : residueCard O - 1 + 1 = residueCard O := by omega
    calc residueCard O ^ (N - s - 1) * residueCard O
        = (residueCard O - 1 + 1) * residueCard O ^ (N - s - 1) := by rw [hs]; ring
      _ = (residueCard O - 1) * residueCard O ^ (N - s - 1) + residueCard O ^ (N - s - 1) := by
          ring
  rw [hrw] at h2
  exact Nat.add_right_cancel h2

/-- **The cell bound.**  One slope `k`, one centre `z`: at most
`(Q−1)·Q^(N−(D−2k)−1) · Q^(N−(D+1−k)) · Q^(N−(D+1))` states. -/
private theorem card_beta_cell_le {π : O} (hπ : Irreducible π) {N k D : ℕ}
    (hkD : 2 * k + 1 ≤ D) (hDN : D + 1 ≤ N) (z : ResidueField O) :
    Nat.card {c : ClusterState O 3 N //
        IsBetaState π c ∧ ∃ μ, HasChildAt π c μ k z ∧ betaContent c k = D}
      ≤ (residueCard O - 1) * residueCard O ^ (N - (D - 2 * k) - 1)
          * residueCard O ^ (N - (D + 1 - k)) * residueCard O ^ (N - (D + 1)) := by
  classical
  obtain ⟨w, hw⟩ := residue_surj (O := O) z
  have hmem : ∀ c : {c : ClusterState O 3 N //
      IsBetaState π c ∧ ∃ μ, HasChildAt π c μ k z ∧ betaContent c k = D},
      (betaKey c.1 (ctr π N k w)).1 ∈ exactSet π (D - 2 * k) N ∧
      (betaKey c.1 (ctr π N k w)).2.1 ∈ dvdSet π (D + 1 - k) N ∧
      (betaKey c.1 (ctr π N k w)).2.2 ∈ dvdSet π (D + 1) N := by
    rintro ⟨c, hβ, μ, hch, hDc⟩
    obtain ⟨-, -, -, e2, e1, e0⟩ := beta_cell_facts hπ hβ hch hDc w hw
    exact ⟨e2, e1, e0⟩
  set f : {c : ClusterState O 3 N //
      IsBetaState π c ∧ ∃ μ, HasChildAt π c μ k z ∧ betaContent c k = D} →
      (exactSet π (D - 2 * k) N) × (dvdSet π (D + 1 - k) N) × (dvdSet π (D + 1) N) :=
    fun c => (⟨_, (hmem c).1⟩, ⟨_, (hmem c).2.1⟩, ⟨_, (hmem c).2.2⟩) with hf
  have hinj : Function.Injective f := by
    intro x y hxy
    have e2 : (betaKey x.1 (ctr π N k w)).1 = (betaKey y.1 (ctr π N k w)).1 := by
      have h := congrArg (fun p => (p.1 : Res O N)) hxy
      simpa [hf] using h
    have e1 : (betaKey x.1 (ctr π N k w)).2.1 = (betaKey y.1 (ctr π N k w)).2.1 := by
      have h := congrArg (fun p => (p.2.1 : Res O N)) hxy
      simpa [hf] using h
    have e0 : (betaKey x.1 (ctr π N k w)).2.2 = (betaKey y.1 (ctr π N k w)).2.2 := by
      have h := congrArg (fun p => (p.2.2 : Res O N)) hxy
      simpa [hf] using h
    simp only [betaKey] at e2 e1 e0
    have h2 : x.1.1 2 = y.1.1 2 := add_right_cancel e2
    have h1 : x.1.1 1 = y.1.1 1 := by
      have h := add_right_cancel e1
      rw [h2] at h
      exact add_right_cancel h
    have h0 : x.1.1 0 = y.1.1 0 := by
      have h := add_right_cancel e0
      rw [h2] at h
      have h' := add_right_cancel h
      rw [h1] at h'
      exact add_right_cancel h'
    exact Subtype.ext (Subtype.ext (funext fun i => by fin_cases i <;> [exact h0; exact h1;
      exact h2]))
  calc Nat.card {c : ClusterState O 3 N //
        IsBetaState π c ∧ ∃ μ, HasChildAt π c μ k z ∧ betaContent c k = D}
      ≤ Nat.card ((exactSet π (D - 2 * k) N) × (dvdSet π (D + 1 - k) N)
          × (dvdSet π (D + 1) N)) := Nat.card_le_card_of_injective f hinj
    _ = (residueCard O - 1) * residueCard O ^ (N - (D - 2 * k) - 1)
          * residueCard O ^ (N - (D + 1 - k)) * residueCard O ^ (N - (D + 1)) := by
        rw [Nat.card_prod, Nat.card_prod, card_exactSet' hπ (by omega),
          card_dvdSet' hπ (by omega), card_dvdSet' hπ (by omega)]
        ring

/-- **The bucket bound.**  Summing the cells over the realized `(k, z)`: the slope runs over
`1 ≤ k` with `2k + 1 ≤ D` (§3), the centre over the `Q − 1` nonzero residues. -/
private theorem card_bucket_le {π : O} (hπ : Irreducible π) {N D : ℕ} (hDN : D + 1 ≤ N) :
    Nat.card {c : ClusterState O 3 N // IsBetaState π c ∧ ∃ (μ k : ℕ) (z : ResidueField O),
        HasChildAt π c μ k z ∧ betaContent c k = D}
      ≤ ∑ k ∈ (Finset.Ico 1 N).filter (fun k => 2 * k + 1 ≤ D),
          (residueCard O - 1) * ((residueCard O - 1) * residueCard O ^ (N - (D - 2 * k) - 1)
            * residueCard O ^ (N - (D + 1 - k)) * residueCard O ^ (N - (D + 1))) := by
  classical
  haveI : Fintype (ClusterState O 3 N) := Fintype.ofFinite _
  haveI : Fintype (ResidueField O) := Fintype.ofFinite _
  set K := (Finset.Ico 1 N).filter (fun k => 2 * k + 1 ≤ D) with hK
  have hsub : Finset.univ.filter (fun c : ClusterState O 3 N =>
        IsBetaState π c ∧ ∃ (μ k : ℕ) (z : ResidueField O),
          HasChildAt π c μ k z ∧ betaContent c k = D)
      ⊆ (K ×ˢ (Finset.univ.erase (0 : ResidueField O))).biUnion
          (fun p => Finset.univ.filter (fun c : ClusterState O 3 N =>
            IsBetaState π c ∧ ∃ μ, HasChildAt π c μ p.1 p.2 ∧ betaContent c p.1 = D)) := by
    intro c hc
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hc
    obtain ⟨hβ, μ, k, z, hch, hDc⟩ := hc
    obtain ⟨w, hw⟩ := residue_surj (O := O) z
    obtain ⟨hk, hlow, -, -, -, -⟩ := beta_cell_facts hπ hβ hch hDc w hw
    refine Finset.mem_biUnion.2 ⟨(k, z), ?_, ?_⟩
    · simp only [Finset.mem_product, hK, Finset.mem_filter, Finset.mem_Ico, Finset.mem_erase,
        Finset.mem_univ, and_true]
      exact ⟨⟨⟨hk, by omega⟩, hlow⟩, hch.2.2.1⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨hβ, μ, hch, hDc⟩
  have hz : (Finset.univ.erase (0 : ResidueField O)).card = residueCard O - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
      ← Nat.card_eq_fintype_card]
    rfl
  calc Nat.card {c : ClusterState O 3 N // IsBetaState π c ∧ ∃ (μ k : ℕ) (z : ResidueField O),
          HasChildAt π c μ k z ∧ betaContent c k = D}
      = (Finset.univ.filter (fun c : ClusterState O 3 N =>
          IsBetaState π c ∧ ∃ (μ k : ℕ) (z : ResidueField O),
            HasChildAt π c μ k z ∧ betaContent c k = D)).card := by
        rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    _ ≤ ((K ×ˢ (Finset.univ.erase (0 : ResidueField O))).biUnion
          (fun p => Finset.univ.filter (fun c : ClusterState O 3 N =>
            IsBetaState π c ∧ ∃ μ, HasChildAt π c μ p.1 p.2 ∧ betaContent c p.1 = D))).card :=
        Finset.card_le_card hsub
    _ ≤ ∑ p ∈ K ×ˢ (Finset.univ.erase (0 : ResidueField O)),
          (Finset.univ.filter (fun c : ClusterState O 3 N =>
            IsBetaState π c ∧ ∃ μ, HasChildAt π c μ p.1 p.2 ∧ betaContent c p.1 = D)).card :=
        Finset.card_biUnion_le
    _ = ∑ k ∈ K, ∑ z ∈ Finset.univ.erase (0 : ResidueField O),
          (Finset.univ.filter (fun c : ClusterState O 3 N =>
            IsBetaState π c ∧ ∃ μ, HasChildAt π c μ k z ∧ betaContent c k = D)).card := by
        rw [Finset.sum_product]
    _ ≤ ∑ k ∈ K, ∑ _z ∈ Finset.univ.erase (0 : ResidueField O),
          ((residueCard O - 1) * residueCard O ^ (N - (D - 2 * k) - 1)
            * residueCard O ^ (N - (D + 1 - k)) * residueCard O ^ (N - (D + 1))) := by
        refine Finset.sum_le_sum fun k hkm => Finset.sum_le_sum fun z _ => ?_
        rw [hK, Finset.mem_filter] at hkm
        rw [← Fintype.card_subtype, ← Nat.card_eq_fintype_card]
        exact card_beta_cell_le hπ hkm.2 hDN z
    _ = ∑ k ∈ K, (residueCard O - 1) * ((residueCard O - 1)
          * residueCard O ^ (N - (D - 2 * k) - 1)
          * residueCard O ^ (N - (D + 1 - k)) * residueCard O ^ (N - (D + 1))) := by
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [Finset.sum_const, hz, smul_eq_mul]

end Count

/-! ## 5. NODE H.121d — the content-weighted β census -/

section Census

/-- **H.121d [A-H.6 §5].**  *The pricing step of the β leg.*  At `2 ≤ m ≤ 3`, weighting each
β state by `Q^D` at its own child content `D = betaContent c k` costs at most a third of the
state census:

    Σ_{c : β state at window N} Q^(betaContent c k(c))  ≤  (1/3)·Q^(m(N−1)).

At `m = 2` the β set is EMPTY (H.118's `betaChild_mult_lt` plus H.109's `2 ≤ μ` would need
`2 ≤ μ < 2`), so every summand is `0`.  At `m = 3` the child multiplicity is `μ = 2` and the
cell count is the triangular digit count of §§3–4; the resulting double sum is §1's, with
closed value `1/(Q+1) ≤ 1/3`.

The `Finset.range N` range is exact: `betaContent c k ≤ N − 1` on non-drain states (H.108's
`betaContent_le`) and β states are non-drain. -/
theorem beta_content_census {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Finite (ResidueField O)] [IsAdicComplete (maximalIdeal O) O] {π : O}
    (hπ : Irreducible π) {m : ℕ} (hm : 2 ≤ m) (hm3 : m ≤ 3) (N : ℕ) (hN : 1 ≤ N) :
    ∑ D ∈ Finset.range N,
        (Nat.card {c : ClusterState O m N //
            IsBetaState π c ∧ ∃ (μ k : ℕ) (z : ResidueField O),
              HasChildAt π c μ k z ∧ betaContent c k = D} : ℝ)
          * (residueCard O : ℝ) ^ D
      ≤ (1 / 3 : ℝ) * (residueCard O : ℝ) ^ (m * (N - 1)) := by
  classical
  have hQ2 : 2 ≤ residueCard O := two_le_residueCard O
  have hQR : (2:ℝ) ≤ (residueCard O : ℝ) := by exact_mod_cast hQ2
  have hQ0 : (0:ℝ) < (residueCard O : ℝ) := by linarith
  have hcast1 : ((residueCard O - 1 : ℕ) : ℝ) = (residueCard O : ℝ) - 1 := by
    have h1 : (1:ℕ) ≤ residueCard O := residueCard_pos O
    push_cast [Nat.cast_sub h1]
    ring
  interval_cases m
  · -- `m = 2`: the β bucket is empty, so every summand vanishes
    have hzero : ∀ D : ℕ, Nat.card {c : ClusterState O 2 N //
        IsBetaState π c ∧ ∃ (μ k : ℕ) (z : ResidueField O),
          HasChildAt π c μ k z ∧ betaContent c k = D} = 0 := by
      intro D
      have hempty : IsEmpty {c : ClusterState O 2 N //
          IsBetaState π c ∧ ∃ (μ k : ℕ) (z : ResidueField O),
            HasChildAt π c μ k z ∧ betaContent c k = D} := by
        constructor
        rintro ⟨c, hβ, μ, k, z, hch, -⟩
        have h1 : μ < 2 := betaChild_mult_lt hβ hch
        have h2 : 2 ≤ μ := hch.1
        omega
      exact Nat.card_of_isEmpty
    simp only [hzero, Nat.cast_zero, zero_mul, Finset.sum_const_zero]
    positivity
  · -- `m = 3`: the census proper
    have hterm : ∀ k D : ℕ, 1 ≤ k → 2 * k + 1 ≤ D → D + 1 ≤ N →
        ((residueCard O : ℝ) - 1) * (((residueCard O : ℝ) - 1)
            * (residueCard O : ℝ) ^ (N - (D - 2 * k) - 1)
            * (residueCard O : ℝ) ^ (N - (D + 1 - k))
            * (residueCard O : ℝ) ^ (N - (D + 1))) * (residueCard O : ℝ) ^ D
          = ((residueCard O : ℝ) - 1) ^ 2 * (residueCard O : ℝ) ^ (3 * k)
              * ((residueCard O : ℝ) ^ (2 * D))⁻¹ * (residueCard O : ℝ) ^ (3 * (N - 1)) := by
      intro k D hk hkD hDN
      have hid : (N - (D - 2 * k) - 1) + (N - (D + 1 - k)) + (N - (D + 1)) + D + 2 * D
          = 3 * (N - 1) + 3 * k := by omega
      have hcomb : (residueCard O : ℝ) ^ (N - (D - 2 * k) - 1)
            * (residueCard O : ℝ) ^ (N - (D + 1 - k))
            * (residueCard O : ℝ) ^ (N - (D + 1)) * (residueCard O : ℝ) ^ D
          = (residueCard O : ℝ) ^ (3 * (N - 1)) * (residueCard O : ℝ) ^ (3 * k)
              * ((residueCard O : ℝ) ^ (2 * D))⁻¹ := by
        rw [eq_comm, mul_inv_eq_iff_eq_mul₀ (ne_of_gt (pow_pos hQ0 (2 * D))), ← pow_add,
          ← pow_add, ← pow_add, ← pow_add, ← pow_add]
        congr 1
        omega
      calc ((residueCard O : ℝ) - 1) * (((residueCard O : ℝ) - 1)
              * (residueCard O : ℝ) ^ (N - (D - 2 * k) - 1)
              * (residueCard O : ℝ) ^ (N - (D + 1 - k))
              * (residueCard O : ℝ) ^ (N - (D + 1))) * (residueCard O : ℝ) ^ D
          = ((residueCard O : ℝ) - 1) ^ 2
              * ((residueCard O : ℝ) ^ (N - (D - 2 * k) - 1)
                * (residueCard O : ℝ) ^ (N - (D + 1 - k))
                * (residueCard O : ℝ) ^ (N - (D + 1)) * (residueCard O : ℝ) ^ D) := by ring
        _ = ((residueCard O : ℝ) - 1) ^ 2 * (residueCard O : ℝ) ^ (3 * k)
              * ((residueCard O : ℝ) ^ (2 * D))⁻¹ * (residueCard O : ℝ) ^ (3 * (N - 1)) := by
            rw [hcomb]; ring
    -- the per-bucket bound, in ℝ
    have hbucket : ∀ D ∈ Finset.range N,
        (Nat.card {c : ClusterState O 3 N //
            IsBetaState π c ∧ ∃ (μ k : ℕ) (z : ResidueField O),
              HasChildAt π c μ k z ∧ betaContent c k = D} : ℝ) * (residueCard O : ℝ) ^ D
          ≤ ∑ k ∈ (Finset.Ico 1 N).filter (fun k => 2 * k + 1 ≤ D),
              ((residueCard O : ℝ) - 1) ^ 2 * (residueCard O : ℝ) ^ (3 * k)
                * ((residueCard O : ℝ) ^ (2 * D))⁻¹ * (residueCard O : ℝ) ^ (3 * (N - 1)) := by
      intro D hD
      rw [Finset.mem_range] at hD
      have hDN : D + 1 ≤ N := hD
      have hnat := card_bucket_le hπ hDN
      have hreal : (Nat.card {c : ClusterState O 3 N //
          IsBetaState π c ∧ ∃ (μ k : ℕ) (z : ResidueField O),
            HasChildAt π c μ k z ∧ betaContent c k = D} : ℝ)
          ≤ ∑ k ∈ (Finset.Ico 1 N).filter (fun k => 2 * k + 1 ≤ D),
              ((residueCard O : ℝ) - 1) * (((residueCard O : ℝ) - 1)
                * (residueCard O : ℝ) ^ (N - (D - 2 * k) - 1)
                * (residueCard O : ℝ) ^ (N - (D + 1 - k))
                * (residueCard O : ℝ) ^ (N - (D + 1))) := by
        have := (Nat.cast_le (α := ℝ)).2 hnat
        refine le_trans this (le_of_eq ?_)
        rw [Nat.cast_sum]
        refine Finset.sum_congr rfl fun k _ => ?_
        push_cast [hcast1]
        ring
      calc (Nat.card {c : ClusterState O 3 N //
            IsBetaState π c ∧ ∃ (μ k : ℕ) (z : ResidueField O),
              HasChildAt π c μ k z ∧ betaContent c k = D} : ℝ) * (residueCard O : ℝ) ^ D
          ≤ (∑ k ∈ (Finset.Ico 1 N).filter (fun k => 2 * k + 1 ≤ D),
              ((residueCard O : ℝ) - 1) * (((residueCard O : ℝ) - 1)
                * (residueCard O : ℝ) ^ (N - (D - 2 * k) - 1)
                * (residueCard O : ℝ) ^ (N - (D + 1 - k))
                * (residueCard O : ℝ) ^ (N - (D + 1)))) * (residueCard O : ℝ) ^ D :=
            mul_le_mul_of_nonneg_right hreal (by positivity)
        _ = ∑ k ∈ (Finset.Ico 1 N).filter (fun k => 2 * k + 1 ≤ D),
              (((residueCard O : ℝ) - 1) * (((residueCard O : ℝ) - 1)
                * (residueCard O : ℝ) ^ (N - (D - 2 * k) - 1)
                * (residueCard O : ℝ) ^ (N - (D + 1 - k))
                * (residueCard O : ℝ) ^ (N - (D + 1))) * (residueCard O : ℝ) ^ D) := by
            rw [Finset.sum_mul]
        _ = ∑ k ∈ (Finset.Ico 1 N).filter (fun k => 2 * k + 1 ≤ D),
              ((residueCard O : ℝ) - 1) ^ 2 * (residueCard O : ℝ) ^ (3 * k)
                * ((residueCard O : ℝ) ^ (2 * D))⁻¹
                * (residueCard O : ℝ) ^ (3 * (N - 1)) := by
            refine Finset.sum_congr rfl fun k hk => ?_
            rw [Finset.mem_filter, Finset.mem_Ico] at hk
            exact hterm k D hk.1.1 hk.2 hDN
    -- the swap and the geometric estimate
    have hswap := Finset.sum_comm' (s := Finset.range N)
      (t := fun D => (Finset.Ico 1 N).filter (fun k => 2 * k + 1 ≤ D))
      (t' := Finset.Ico 1 N)
      (s' := fun k => (Finset.range N).filter (fun D => 2 * k + 1 ≤ D))
      (f := fun D k => ((residueCard O : ℝ) - 1) ^ 2 * (residueCard O : ℝ) ^ (3 * k)
        * ((residueCard O : ℝ) ^ (2 * D))⁻¹ * (residueCard O : ℝ) ^ (3 * (N - 1)))
      (by
        intro D k
        simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
        constructor
        · rintro ⟨hD, ⟨hk1, hk2⟩, hkD⟩
          exact ⟨⟨hD, hkD⟩, hk1, hk2⟩
        · rintro ⟨⟨hD, hkD⟩, hk1, hk2⟩
          exact ⟨hD, ⟨hk1, hk2⟩, hkD⟩)
    have hfil : ∀ k : ℕ, (Finset.range N).filter (fun D => 2 * k + 1 ≤ D)
        = Finset.Ico (2 * k + 1) N := by
      intro k
      ext D
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
      omega
    calc ∑ D ∈ Finset.range N,
          (Nat.card {c : ClusterState O 3 N //
            IsBetaState π c ∧ ∃ (μ k : ℕ) (z : ResidueField O),
              HasChildAt π c μ k z ∧ betaContent c k = D} : ℝ) * (residueCard O : ℝ) ^ D
        ≤ ∑ D ∈ Finset.range N, ∑ k ∈ (Finset.Ico 1 N).filter (fun k => 2 * k + 1 ≤ D),
            ((residueCard O : ℝ) - 1) ^ 2 * (residueCard O : ℝ) ^ (3 * k)
              * ((residueCard O : ℝ) ^ (2 * D))⁻¹ * (residueCard O : ℝ) ^ (3 * (N - 1)) :=
          Finset.sum_le_sum hbucket
      _ = ∑ k ∈ Finset.Ico 1 N, ∑ D ∈ (Finset.range N).filter (fun D => 2 * k + 1 ≤ D),
            ((residueCard O : ℝ) - 1) ^ 2 * (residueCard O : ℝ) ^ (3 * k)
              * ((residueCard O : ℝ) ^ (2 * D))⁻¹ * (residueCard O : ℝ) ^ (3 * (N - 1)) := hswap
      _ = (∑ k ∈ Finset.Ico 1 N, ∑ D ∈ Finset.Ico (2 * k + 1) N,
            ((residueCard O : ℝ) - 1) ^ 2 * (residueCard O : ℝ) ^ (3 * k)
              * ((residueCard O : ℝ) ^ (2 * D))⁻¹) * (residueCard O : ℝ) ^ (3 * (N - 1)) := by
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [Finset.sum_mul, hfil k]
      _ ≤ (1 / 3 : ℝ) * (residueCard O : ℝ) ^ (3 * (N - 1)) :=
          mul_le_mul_of_nonneg_right (census_geom_le (residueCard O) hQ2 N) (by positivity)

end Census

end Uniformity.Density.Induction

/-! ## 6. TEETH — the two constants, pinned

The battery's `D5` says the SHARP census value `Q/(Q²+Q+1)` is maximized at `Q = 2` with value
`2/7`; this file's route certifies the CRUDER `1/(Q+1)`, maximized at `Q = 2` with value `1/3`
— exactly the signed literal, i.e. the proof has zero slack at `q = 2` and the sharp value has
the `2/7 < 1/3` margin A-H.6 measured.  Both comparisons are integer identities, transcribed
here in the additive form (`3·num ≤ den`) so they hold verbatim in every characteristic. -/

section NumericGate

-- `Q/(Q² + Q + 1) ≤ 1/3` (A-H.6's SHARP value, checks `C4`/`D1–D5`)
#guard ([2, 3, 5, 7, 11, 199] : List ℕ).all fun q => 3 * q ≤ q ^ 2 + q + 1

-- `1/(Q + 1) ≤ 1/3` (THIS file's certified value, tight at `q = 2`)
#guard ([2, 3, 5, 7, 11, 199] : List ℕ).all fun q => 3 ≤ q + 1

-- the two are ordered `sharp ≤ crude ≤ 1/3`: `Q(Q+1) ≤ Q² + Q + 1`
#guard ([2, 3, 5, 7, 11, 199] : List ℕ).all fun q => q * (q + 1) ≤ q ^ 2 + q + 1

-- the defeat the `Q − 1` factors avert: relaxing EITHER to `Q` gives `Q/(Q² − 1)`, which at
-- `q = 2` is `2/3 > 1/3` (`3 * 2 > 4 - 1`)
#guard !(3 * 2 ≤ 2 ^ 2 - 1)

end NumericGate

/-! ## 7. Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Induction.beta_content_census

end AxCheck
