/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import Uniformity.ChapI.IFCG65

/-!
# Uniformity.ChapI.IFCG68 — [NA2 2026-08-31] the first diagonal assembly: the `n = 2`
depth census in closed form and the `(2, n₂)` depth-density `ZcURLim`, OUTRIGHT

Stage NA2 of the cone census (design record `runs/wave-c/verdict_NA2.md`).  PSP's
IFCG65 closed DGT route step (c): every primary-shape census value is the `N`-free
finite computation `primo`.  THIS file performs route step (d) at `n = 2` — the first
full diagonal assembly:

* **§0 the quadratic residual kit**: the two-coefficient representation
  `monicPoly r = X² + C (r 1)·X + C (r 0)`, injectivity of `monicPoly` in the
  coefficient vector, and the two parametrized shapes
  `monicPoly ![a·b, −(a+b)] = (X − C a)(X − C b)`,
  `monicPoly ![a·a, −(a+a)] = (X − C a)²`.
* **§1 the genre trichotomy** over a field: every monic quadratic residual is EXACTLY
  ONE of — split `(X − C a)(X − C b)` with `a ≠ b`, double `(X − C a)²`, or
  irreducible (inert); disjointness by root evaluation, exhaustion through
  `Polynomial.Monic.not_irreducible_iff_exists_add_mul_eq_coeff`.
* **§2 the genre counts** over a finite field `K`, `q := #K` (elementary double
  counting, uniform in `q` — the `n = 2` instance of the Gauss/necklace counts;
  IFCG19's `necklacePoly` machinery is the general-`δ` supplier, not needed here):
  `#double = q`, `2·#split = q² − q`, `2·#inert = q² − q`
  (so `q(q−1)/2 + q + (q²−q)/2 = q²`, verified as the doubled partition identity).
* **§3 the per-shape census values** (all in the `primo` normalization of IFCG65,
  multiplied form — no division anywhere):
  linear `#strat(1,N,j,X−Ca)·q^{j+1} = (q−1)·q^{2N−1}`;
  split `#strat(2,N,v,(X−Ca)(X−Cb))·q^{v+2} = (v+1)(q−1)²·q^{2(2N−1)}` (the binary
  convolution `card_stratumDepthSet_mul` collapses termwise:
  `q^{j+1}·q^{(v−j)+1} = q^{v+2}`);
  double `= primo(q,1,2,v)·q^{2(2N−1)}`; inert `= primo(q,2,1,v)·q^{2(2N−1)}`.
* **§4 ★★ THE `n = 2` DIAGONAL CENSUS, CLOSED**: with
  `duo q v := 2q·primo(q,1,2,v) + (q²−q)·((v+1)(q−1)² + primo(q,2,1,v))`,
  `2·#redDepthPairSet(2,N,v)·q^{v+2} = duo q v · q^{2(2N−1)}` for `v < N` —
  the assembly over IFCG63's shape partition `card_redDepthPairSet_eq_sum_strata`.
  Plus the `primo(q,1,2,·)` closed form
  `primo q 1 2 v = [2∣v](q²−q) + ⌈v/2⌉(q−1)²`.
* **§5 ★★★ THE `ZcURLim`, FIRED AT `n = 2`**: the normalized reduced diagonal
  density is eventually constant `duo q v / (2q^{v+4})`, a fixed rational function of
  `q` — `zcURLim_redDiag_two` outright, then through IFCG61's
  `zcURLim_depthDensity_of_reduced`: `zcURLim_depthDensity_two_two` (the `(2,2)`
  depth-density `ZcURLim`, UNCONDITIONAL) and `zcURLim_depthDensity_two_right`
  (every `(2, n₂)`, `n₂ ≥ 2`).
* **§6 the regression rows**: the assembled density matches IGV's battery-verified
  `Z₂(t)` law `[t^v]Z₂ = s^v`-forms at `v = 0..4` (`s = 1/q`):
  `(1−s)`, `s(1−s)²`, `(1−s)s²(2−s)`, `2(1−s)²s³`, `(1−s)s⁴(3−2s)` — stated and
  proved as exact `ℚ`-identities `duo q v = ...`.

## THE HONEST FENCE

The general-`n` assembly (the type-grouping engine: the sum over factorization types
`λ ⊢ n` weighted by products of Gauss counts `I_δ(q)` and multiset multiplicities,
with the `n`-ary `primo` convolution per type) is NOT here; `n = 2` needs only the
three genres and the landed binary convolution.  The named remainder for general `n`
is stated precisely in §7's docstring.  Everything landed here is uniform in `q` and
in the window `N`; no statement is weakened.

## Axiom fence (machine-exact at landing)

EVERY row of the AxCheck footer expects PURE Lean core
`{propext, Classical.choice, Quot.sound}`.  B.42, the C.33 cites, and
`AX_cellRecursion` must NOT occur.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

noncomputable section

namespace Uniformity.Density.IFCG68

open IsLocalRing Polynomial Filter Topology
open Uniformity.Density.Induction
open Uniformity.Density.IFCG24 (ZcURLim)
open Uniformity.Density.IFCG56 (depthPairSet)
open Uniformity.Density.IFCG61 (redDepthPairSet zcURLim_depthDensity_of_reduced)
open Uniformity.Density.IFCG63 (stratumDepthSet card_stratumDepthSet_mul
  card_redDepthPairSet_eq_sum_strata)
open Uniformity.Density.IFCG65 (primo primo_one card_stratumDepthSet_pow)

/-! ## §0 — the quadratic residual kit -/

section QuadKit

variable {S : Type*} [CommRing S]

/-- Coefficient reading below the top degree (IFCG63's private reader, restated). -/
private theorem monicPoly_coeff_lt {n : ℕ} (a : Fin n → S) {i : ℕ} (hi : i < n) :
    (monicPoly a).coeff i = a ⟨i, hi⟩ := by
  classical
  unfold monicPoly
  rw [Polynomial.coeff_add, Polynomial.coeff_X_pow, if_neg (Nat.ne_of_lt hi), zero_add,
    Polynomial.finsetSum_coeff, Finset.sum_eq_single (⟨i, hi⟩ : Fin n)]
  · rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_pos rfl, mul_one]
  · intro b _ hbi
    rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
      if_neg fun h => hbi (Fin.ext h.symm), mul_zero]
  · simp

/-- `monicPoly` is injective in the coefficient vector. -/
theorem monicPoly_injective {n : ℕ} : Function.Injective (monicPoly : (Fin n → S) → _) := by
  intro r r' h
  funext i
  have hc := congrArg (fun p => Polynomial.coeff p (i : ℕ)) h
  simpa [monicPoly_coeff_lt _ i.isLt] using hc

/-- The two-coefficient representation of a monic quadratic. -/
theorem monicPoly_two (r : Fin 2 → S) :
    monicPoly r = X ^ 2 + C (r 1) * X + C (r 0) := by
  unfold monicPoly
  rw [Fin.sum_univ_two]
  simp only [Fin.val_zero, Fin.val_one, pow_zero, pow_one]
  ring

/-- The split shape: the coefficient vector of `(X − C a)(X − C b)`. -/
theorem monicPoly_splitVec (a b : S) :
    monicPoly (![a * b, -(a + b)] : Fin 2 → S) = (X - C a) * (X - C b) := by
  rw [monicPoly_two]
  simp only [Matrix.cons_val_one, Matrix.cons_val_zero, map_neg, map_add, map_mul]
  ring

/-- The double shape: the coefficient vector of `(X − C a)²`. -/
theorem monicPoly_dblVec (a : S) :
    monicPoly (![a * a, -(a + a)] : Fin 2 → S) = (X - C a) ^ 2 := by
  rw [monicPoly_two]
  simp only [Matrix.cons_val_one, Matrix.cons_val_zero, map_neg, map_add, map_mul]
  ring

end QuadKit

/-! ## §1 — the genre trichotomy over a field -/

section Trichotomy

variable {K : Type*} [Field K]

/-- `X − C a` and `X − C b` are coprime for `a ≠ b` (IFCG29's private lemma, restated). -/
theorem isCoprime_X_sub_C_of_ne {a b : K} (hab : a ≠ b) :
    IsCoprime ((X : Polynomial K) - C a) (X - C b) :=
  Polynomial.isCoprime_X_sub_C_of_isUnit_sub
    (isUnit_iff_ne_zero.mpr (sub_ne_zero.mpr hab))

/-- A product of two monic linears is not irreducible. -/
theorem not_irreducible_mul_linear (a b : K) :
    ¬ Irreducible (((X : Polynomial K) - C a) * (X - C b)) := by
  intro h
  rcases h.isUnit_or_isUnit rfl with hu | hu
  · exact (Polynomial.not_isUnit_of_natDegree_pos _
      (by rw [Polynomial.natDegree_X_sub_C]; omega)) hu
  · exact (Polynomial.not_isUnit_of_natDegree_pos _
      (by rw [Polynomial.natDegree_X_sub_C]; omega)) hu

/-- A monic linear square is not irreducible. -/
theorem not_irreducible_sq_linear (a : K) :
    ¬ Irreducible (((X : Polynomial K) - C a) ^ 2) := by
  rw [sq]
  exact not_irreducible_mul_linear a a

/-- Disjointness: a split quadratic is not a double one (root evaluation). -/
theorem split_ne_dbl {a b c : K} (hab : a ≠ b) :
    ((X : Polynomial K) - C a) * (X - C b) ≠ (X - C c) ^ 2 := by
  intro h
  have ha : (a - c) ^ 2 = 0 := by
    have := congrArg (Polynomial.eval a) h
    simpa using this.symm
  have hb : (b - c) ^ 2 = 0 := by
    have := congrArg (Polynomial.eval b) h
    simpa using this.symm
  have ha' : a = c := by
    have := pow_eq_zero_iff (n := 2) (by omega) |>.mp ha
    exact sub_eq_zero.mp this
  have hb' : b = c := by
    have := pow_eq_zero_iff (n := 2) (by omega) |>.mp hb
    exact sub_eq_zero.mp this
  exact hab (ha'.trans hb'.symm)

/-- Exhaustion: a reducible monic quadratic residual is split or double. -/
theorem split_or_dbl_of_not_irreducible {r : Fin 2 → K}
    (h : ¬ Irreducible (monicPoly r)) :
    (∃ a b : K, a ≠ b ∧ monicPoly r = (X - C a) * (X - C b))
      ∨ ∃ a : K, monicPoly r = (X - C a) ^ 2 := by
  obtain ⟨c₁, c₂, h0, h1⟩ :=
    ((monicPoly_monic r).not_irreducible_iff_exists_add_mul_eq_coeff
      (monicPoly_natDegree r)).mp h
  rw [monicPoly_coeff_lt _ (by omega : (0:ℕ) < 2)] at h0
  rw [monicPoly_coeff_lt _ (by omega : (1:ℕ) < 2)] at h1
  have hfac : monicPoly r = (X - C (-c₁)) * (X - C (-c₂)) := by
    rw [monicPoly_two]
    have h0' : r 0 = c₁ * c₂ := h0
    have h1' : r 1 = c₁ + c₂ := h1
    rw [h0', h1', map_add, map_neg, map_neg, map_mul]
    ring
  by_cases hc : (-c₁ : K) = -c₂
  · exact Or.inr ⟨-c₁, by rw [hfac, hc, sq]⟩
  · exact Or.inl ⟨-c₁, -c₂, hc, hfac⟩

end Trichotomy

/-! ## §2 — the genre counts over a finite field -/

section Counts

attribute [local instance] Classical.propDecidable

variable {K : Type*} [Field K] [Fintype K]

/-- **The double count**: exactly `q` monic quadratics are squares of linears. -/
theorem card_dblVecs :
    (Finset.univ.filter
      (fun r : Fin 2 → K => ∃ a : K, monicPoly r = (X - C a) ^ 2)).card
      = Fintype.card K := by
  have hinj : Function.Injective (fun a : K => (![a * a, -(a + a)] : Fin 2 → K)) := by
    intro a b hab
    have h : ((X : Polynomial K) - C a) ^ 2 = (X - C b) ^ 2 := by
      rw [← monicPoly_dblVec a, ← monicPoly_dblVec b]
      exact congrArg monicPoly hab
    have h0 : (a - b) ^ 2 = 0 := by
      have hev := congrArg (Polynomial.eval a) h
      simpa using hev.symm
    exact sub_eq_zero.mp (pow_eq_zero_iff (n := 2) (by omega) |>.mp h0)
  have himg : Finset.univ.filter
      (fun r : Fin 2 → K => ∃ a : K, monicPoly r = (X - C a) ^ 2)
      = Finset.univ.image (fun a : K => (![a * a, -(a + a)] : Fin 2 → K)) := by
    ext r
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    constructor
    · rintro ⟨a, ha⟩
      exact ⟨a, monicPoly_injective ((monicPoly_dblVec a).trans ha.symm)⟩
    · rintro ⟨a, rfl⟩
      exact ⟨a, monicPoly_dblVec a⟩
  rw [himg, Finset.card_image_of_injective _ hinj, Finset.card_univ]

/-- **The split count, doubled**: `2·#split = q² − q` (the `(a,b) ↦ {a,b}` double
counting over the off-diagonal). -/
theorem two_mul_card_splitVecs :
    2 * (Finset.univ.filter (fun r : Fin 2 → K =>
        ∃ a b : K, a ≠ b ∧ monicPoly r = (X - C a) * (X - C b))).card
      = Fintype.card K ^ 2 - Fintype.card K := by
  classical
  set T := Finset.univ.filter (fun r : Fin 2 → K =>
    ∃ a b : K, a ≠ b ∧ monicPoly r = (X - C a) * (X - C b)) with hT
  set S := (Finset.univ : Finset (K × K)).filter (fun p => p.1 ≠ p.2) with hS
  set φ : K × K → (Fin 2 → K) := fun p => ![p.1 * p.2, -(p.1 + p.2)] with hφ
  have hφpoly : ∀ p : K × K, monicPoly (φ p) = (X - C p.1) * (X - C p.2) :=
    fun p => monicPoly_splitVec p.1 p.2
  have hmaps : ∀ p ∈ S, φ p ∈ T := by
    intro p hp
    rw [hS, Finset.mem_filter] at hp
    rw [hT, Finset.mem_filter]
    exact ⟨Finset.mem_univ _, p.1, p.2, hp.2, hφpoly p⟩
  have hcard := Finset.card_eq_sum_card_fiberwise hmaps
  have hfiber : ∀ t ∈ T, (S.filter (fun p => φ p = t)).card = 2 := by
    intro t ht
    rw [hT, Finset.mem_filter] at ht
    obtain ⟨-, a, b, hab, hfac⟩ := ht
    have hset : S.filter (fun p => φ p = t) = {(a, b), (b, a)} := by
      ext ⟨x, y⟩
      simp only [hS, Finset.filter_filter, Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq]
      constructor
      · rintro ⟨hxy, hφt⟩
        have hpoly : ((X : Polynomial K) - C x) * (X - C y) = (X - C a) * (X - C b) := by
          rw [← hφpoly (x, y), hφt]
          exact hfac
        have hx : x = a ∨ x = b := by
          have hev := congrArg (Polynomial.eval x) hpoly
          simp only [Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_X,
            Polynomial.eval_C, sub_self, zero_mul] at hev
          rcases mul_eq_zero.mp hev.symm with h | h
          · exact Or.inl (sub_eq_zero.mp h)
          · exact Or.inr (sub_eq_zero.mp h)
        have hy : y = a ∨ y = b := by
          have hev := congrArg (Polynomial.eval y) hpoly
          simp only [Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_X,
            Polynomial.eval_C, sub_self, mul_zero] at hev
          rcases mul_eq_zero.mp hev.symm with h | h
          · exact Or.inl (sub_eq_zero.mp h)
          · exact Or.inr (sub_eq_zero.mp h)
        rcases hx with hxa | hxb
        · refine Or.inl ⟨hxa, ?_⟩
          rcases hy with hya | hyb
          · exact absurd (hxa.trans hya.symm) hxy
          · exact hyb
        · refine Or.inr ⟨hxb, ?_⟩
          rcases hy with hya | hyb
          · exact hya
          · exact absurd (hxb.trans hyb.symm) hxy
      · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
        · refine ⟨hab, monicPoly_injective ?_⟩
          rw [hφpoly (x, y)]
          exact hfac.symm
        · refine ⟨hab.symm, monicPoly_injective ?_⟩
          rw [hφpoly (x, y)]
          rw [hfac]
          exact mul_comm _ _
    rw [hset]
    exact Finset.card_pair_eq_two_iff.mpr (fun h => hab (congrArg Prod.fst h))
  have hSum : S.card = 2 * T.card := by
    rw [hcard, Finset.sum_congr rfl hfiber, Finset.sum_const, smul_eq_mul, mul_comm]
  have hsq : Fintype.card K ^ 2 = Fintype.card K * Fintype.card K := by ring
  have hScard : S.card = Fintype.card K ^ 2 - Fintype.card K := by
    have hoff : S = (Finset.univ : Finset K).offDiag := by
      ext p
      simp [hS, Finset.mem_offDiag]
    rw [hoff, Finset.offDiag_card, Finset.card_univ, hsq]
  rw [← hSum, hScard]

/-- The reducible monic quadratics are EXACTLY the split ∪ double vectors (the genre
partition of the complement of the inert set; exhaustion `split_or_dbl_of_not_irreducible`
+ the §1 non-irreducibility of both reducible shapes). -/
private theorem filter_not_irreducible_eq :
    Finset.univ.filter (fun r : Fin 2 → K => ¬ Irreducible (monicPoly r))
      = (Finset.univ.filter (fun r : Fin 2 → K =>
          ∃ a b : K, a ≠ b ∧ monicPoly r = (X - C a) * (X - C b)))
        ∪ (Finset.univ.filter
            (fun r : Fin 2 → K => ∃ a : K, monicPoly r = (X - C a) ^ 2)) := by
  ext r
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
  constructor
  · exact split_or_dbl_of_not_irreducible
  · rintro (⟨a, b, hab, hfac⟩ | ⟨a, hfac⟩)
    · rw [hfac]; exact not_irreducible_mul_linear a b
    · rw [hfac]; exact not_irreducible_sq_linear a

/-- The split and double genres are disjoint (`split_ne_dbl`, filtered). -/
private theorem disjoint_split_dbl :
    Disjoint
      (Finset.univ.filter (fun r : Fin 2 → K =>
        ∃ a b : K, a ≠ b ∧ monicPoly r = (X - C a) * (X - C b)))
      (Finset.univ.filter
        (fun r : Fin 2 → K => ∃ a : K, monicPoly r = (X - C a) ^ 2)) := by
  rw [Finset.disjoint_left]
  intro r hrA hrB
  rw [Finset.mem_filter] at hrA hrB
  obtain ⟨-, a, b, hab, hfac⟩ := hrA
  obtain ⟨-, c, hfac'⟩ := hrB
  exact split_ne_dbl hab (hfac.symm.trans hfac')

/-- **The inert count, doubled**: `2·#inert = q² − q`, by complementation in the
partition `#split + #double + #inert = q²` (the honest verification of
`q(q−1)/2 + q + (q²−q)/2 = q²`). -/
theorem two_mul_card_inertVecs :
    2 * (Finset.univ.filter
        (fun r : Fin 2 → K => Irreducible (monicPoly r))).card
      = Fintype.card K ^ 2 - Fintype.card K := by
  have hpart := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (Fin 2 → K)))
    (fun r => Irreducible (monicPoly r))
  rw [filter_not_irreducible_eq, Finset.card_union_of_disjoint disjoint_split_dbl,
    Finset.card_univ, Fintype.card_fun, Fintype.card_fin] at hpart
  have hsplit := two_mul_card_splitVecs (K := K)
  have hdbl := card_dblVecs (K := K)
  have hq1 : 1 ≤ Fintype.card K := Fintype.card_pos
  have hqq : Fintype.card K ≤ Fintype.card K ^ 2 := by
    calc Fintype.card K = Fintype.card K ^ 1 := (pow_one _).symm
    _ ≤ Fintype.card K ^ 2 := Nat.pow_le_pow_right hq1 (by omega)
  omega

end Counts

/-! ## §3 — the per-shape census values, `primo`-normalized -/

section ShapeValues

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)]

/-- The linear-shape stratum value: the `(δ, e) = (1, 1)` instance of the closed form. -/
theorem card_stratumDepthSet_linear {N j : ℕ} (hj : j < N) (a : ResidueField O) :
    Nat.card (stratumDepthSet O 1 N j (X - C a)) * residueCard O ^ (j + 1)
      = (residueCard O - 1) * residueCard O ^ (2 * N - 1) := by
  have h := card_stratumDepthSet_pow (O := O) (δ := 1) (e := 1) (N := N) (v := j)
    (by omega) (by omega) hj (Polynomial.irreducible_X_sub_C a)
    (Polynomial.monic_X_sub_C a) (Polynomial.natDegree_X_sub_C a)
  rw [primo_one (by omega : 0 < 1), if_pos (one_dvd j)] at h
  simpa [pow_one] using h

/-- The double-shape stratum value: the `(δ, e) = (1, 2)` instance. -/
theorem card_stratumDepthSet_double {N v : ℕ} (hv : v < N) (a : ResidueField O) :
    Nat.card (stratumDepthSet O 2 N v ((X - C a) ^ 2)) * residueCard O ^ (v + 2)
      = primo (residueCard O) 1 2 v * residueCard O ^ (2 * (2 * N - 1)) := by
  have h := card_stratumDepthSet_pow (O := O) (δ := 1) (e := 2) (N := N) (v := v)
    (by omega) (by omega) hv (Polynomial.irreducible_X_sub_C a)
    (Polynomial.monic_X_sub_C a) (Polynomial.natDegree_X_sub_C a)
  simpa [one_mul] using h

/-- The inert-shape stratum value: the `(δ, e) = (2, 1)` instance. -/
theorem card_stratumDepthSet_inert {N v : ℕ} (hv : v < N)
    {g : Polynomial (ResidueField O)} (hg : Irreducible g) (hgm : g.Monic)
    (hgd : g.natDegree = 2) :
    Nat.card (stratumDepthSet O 2 N v g) * residueCard O ^ (v + 2)
      = primo (residueCard O) 2 1 v * residueCard O ^ (2 * (2 * N - 1)) := by
  have h := card_stratumDepthSet_pow (O := O) (δ := 2) (e := 1) (N := N) (v := v)
    (by omega) (by omega) hv hg hgm hgd
  simpa [pow_one, mul_one] using h

/-- The split-shape stratum value: the binary convolution collapses termwise in the
`primo` normalization (`q^{j+1}·q^{(v−j)+1} = q^{v+2}`). -/
theorem card_stratumDepthSet_split [IsAdicComplete (maximalIdeal O) O] {N v : ℕ}
    (hv : v < N) {a b : ResidueField O} (hab : a ≠ b) :
    Nat.card (stratumDepthSet O 2 N v ((X - C a) * (X - C b)))
        * residueCard O ^ (v + 2)
      = (v + 1) * (residueCard O - 1) ^ 2 * residueCard O ^ (2 * (2 * N - 1)) := by
  have h : Nat.card (stratumDepthSet O 2 N v ((X - C a) * (X - C b)))
      = ∑ j ∈ Finset.range (v + 1),
          Nat.card (stratumDepthSet O 1 N j (X - C a))
            * Nat.card (stratumDepthSet O 1 N (v - j) (X - C b)) :=
    card_stratumDepthSet_mul (by omega) (by omega) hv (Polynomial.monic_X_sub_C a)
      (Polynomial.monic_X_sub_C b) (Polynomial.natDegree_X_sub_C a)
      (Polynomial.natDegree_X_sub_C b) (isCoprime_X_sub_C_of_ne hab)
  rw [h, Finset.sum_mul]
  have hterm : ∀ j ∈ Finset.range (v + 1),
      Nat.card (stratumDepthSet O 1 N j (X - C a))
          * Nat.card (stratumDepthSet O 1 N (v - j) (X - C b)) * residueCard O ^ (v + 2)
        = ((residueCard O - 1) * residueCard O ^ (2 * N - 1))
            * ((residueCard O - 1) * residueCard O ^ (2 * N - 1)) := by
    intro j hj
    rw [Finset.mem_range] at hj
    have hstep : Nat.card (stratumDepthSet O 1 N j (X - C a))
          * Nat.card (stratumDepthSet O 1 N (v - j) (X - C b)) * residueCard O ^ (v + 2)
        = (Nat.card (stratumDepthSet O 1 N j (X - C a)) * residueCard O ^ (j + 1))
            * (Nat.card (stratumDepthSet O 1 N (v - j) (X - C b))
                * residueCard O ^ ((v - j) + 1)) := by
      have hexp : (j + 1) + ((v - j) + 1) = v + 2 := by omega
      rw [← hexp, pow_add]
      ring
    rw [hstep, card_stratumDepthSet_linear (by omega : j < N) a,
      card_stratumDepthSet_linear (by omega : v - j < N) b]
  rw [Finset.sum_congr rfl hterm, Finset.sum_const, Finset.card_range, smul_eq_mul]
  have hpow : residueCard O ^ (2 * (2 * N - 1))
      = residueCard O ^ (2 * N - 1) * residueCard O ^ (2 * N - 1) := by
    rw [two_mul, pow_add]
  rw [hpow]
  ring

end ShapeValues

/-! ## §4 — ★★ the `n = 2` diagonal census, closed -/

section Census

attribute [local instance] Classical.propDecidable

/-- The `primo(q,1,2,·)` one-step recursion, isolated: peel `v ↦ v − 2` plus the
boundary reader (`q² − q` exactly at `v = 0`, `(q−1)²` for `v ≥ 1`). -/
private theorem primo_two_step (q v : ℕ) :
    primo q 1 2 v
      = (if 2 ≤ v then primo q 1 2 (v - 2) else 0)
        + ((q ^ 2 - q) * (if v = 0 then 1 else 0)
            + (q - 1) * (if 1 ≤ v then q - 1 else 0)) := by
  have hp0 : ∀ w, primo q 1 0 w = if w = 0 then 1 else 0 := fun w => by rw [primo]
  rw [primo]
  have hsum := Finset.sum_attach (Finset.range 2)
    (fun j => (q ^ (1 * 2 - 1 * j) - q ^ (1 * 2 - 1 * j - 1))
      * (if 1 * j ≤ v then primo q 1 j (v - 1 * j) else 0))
  rw [hsum, Finset.sum_range_succ, Finset.sum_range_one]
  simp only [Nat.mul_zero, Nat.mul_one, Nat.sub_zero, Nat.zero_le, if_true, hp0,
    primo_one (by omega : 0 < 1), one_dvd, pow_one]
  norm_num

/-- The `primo(q, 1, 2, ·)` closed form: `[2 ∣ v]·(q² − q) + ⌈v/2⌉·(q − 1)²`
(`⌈v/2⌉ = (v+1)/2` in `ℕ`-division). -/
theorem primo_two_closed (q v : ℕ) :
    primo q 1 2 v
      = (if 2 ∣ v then q ^ 2 - q else 0) + (v + 1) / 2 * (q - 1) ^ 2 := by
  induction v using Nat.strong_induction_on with
  | _ v IH =>
    rw [primo_two_step]
    rcases Nat.lt_or_ge v 2 with hv2 | hv2
    · interval_cases v
      · norm_num
      · norm_num [pow_two]
    · rw [if_pos hv2, IH (v - 2) (by omega), if_neg (by omega : ¬ v = 0),
        if_pos (by omega : 1 ≤ v), mul_zero, zero_add, ← pow_two (q - 1)]
      have hdiv : (v + 1) / 2 = (v - 2 + 1) / 2 + 1 := by omega
      rw [hdiv, add_mul, one_mul]
      by_cases hd : 2 ∣ v
      · rw [if_pos (by omega : 2 ∣ v - 2), if_pos hd]
        omega
      · rw [if_neg (by omega : ¬ 2 ∣ v - 2), if_neg hd]
        omega

/-- **The `n = 2` diagonal census numerator**: the three-genre assembly,
`2q·primo(q,1,2,v)` (double, count `q`, doubled) plus
`(q²−q)·((v+1)(q−1)² + primo(q,2,1,v))` (split + inert, each count `(q²−q)/2`,
doubled). -/
def duo (q v : ℕ) : ℕ :=
  2 * q * primo q 1 2 v + (q ^ 2 - q) * ((v + 1) * (q - 1) ^ 2 + primo q 2 1 v)

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)]

/-- ★★ **THE `n = 2` DIAGONAL CENSUS, CLOSED** (route step (d) at `n = 2`): the
reduced diagonal depth census at `n = 2` is `duo`, uniformly in `q` and the window —
`2·#redDepthPairSet(2,N,v)·q^{v+2} = duo(q,v)·q^{2(2N−1)}` for `v < N`. -/
theorem two_mul_card_redDepthPairSet_two [IsAdicComplete (maximalIdeal O) O]
    {π : O} (hπ : Irreducible π) {N v : ℕ} (hv : v < N) :
    2 * Nat.card (redDepthPairSet O π 2 N v) * residueCard O ^ (v + 2)
      = duo (residueCard O) v * residueCard O ^ (2 * (2 * N - 1)) := by
  haveI : Fintype (ResidueField O) := Fintype.ofFinite _
  haveI : Fintype (Coeff O 2 N) := Fintype.ofFinite _
  -- the shape partition, then the genre split of the residual sum
  rw [card_redDepthPairSet_eq_sum_strata hπ hv, mul_assoc, Finset.sum_mul,
    ← Finset.sum_filter_add_sum_filter_not Finset.univ
      (fun r : Fin 2 → ResidueField O => Irreducible (monicPoly r)),
    filter_not_irreducible_eq, Finset.sum_union disjoint_split_dbl]
  -- per-genre census values (§3)
  have hIval : ∀ r ∈ Finset.univ.filter (fun r : Fin 2 → ResidueField O =>
      Irreducible (monicPoly r)),
      Nat.card (stratumDepthSet O 2 N v (monicPoly r)) * residueCard O ^ (v + 2)
        = primo (residueCard O) 2 1 v * residueCard O ^ (2 * (2 * N - 1)) := by
    intro r hr
    rw [Finset.mem_filter] at hr
    exact card_stratumDepthSet_inert hv hr.2 (monicPoly_monic r) (monicPoly_natDegree r)
  have hSval : ∀ r ∈ Finset.univ.filter (fun r : Fin 2 → ResidueField O =>
      ∃ a b : ResidueField O, a ≠ b ∧ monicPoly r = (X - C a) * (X - C b)),
      Nat.card (stratumDepthSet O 2 N v (monicPoly r)) * residueCard O ^ (v + 2)
        = (v + 1) * (residueCard O - 1) ^ 2 * residueCard O ^ (2 * (2 * N - 1)) := by
    intro r hr
    rw [Finset.mem_filter] at hr
    obtain ⟨-, a, b, hab, hfac⟩ := hr
    rw [hfac]
    exact card_stratumDepthSet_split hv hab
  have hDval : ∀ r ∈ Finset.univ.filter (fun r : Fin 2 → ResidueField O =>
      ∃ a : ResidueField O, monicPoly r = (X - C a) ^ 2),
      Nat.card (stratumDepthSet O 2 N v (monicPoly r)) * residueCard O ^ (v + 2)
        = primo (residueCard O) 1 2 v * residueCard O ^ (2 * (2 * N - 1)) := by
    intro r hr
    rw [Finset.mem_filter] at hr
    obtain ⟨-, a, hfac⟩ := hr
    rw [hfac]
    exact card_stratumDepthSet_double hv a
  rw [Finset.sum_congr rfl hIval, Finset.sum_congr rfl hSval, Finset.sum_congr rfl hDval,
    Finset.sum_const, Finset.sum_const, Finset.sum_const]
  simp only [smul_eq_mul]
  -- the three genre counts (§2), read at `q = residueCard O`
  have hqcard : Fintype.card (ResidueField O) = residueCard O :=
    Nat.card_eq_fintype_card.symm
  have hdblc : (Finset.univ.filter (fun r : Fin 2 → ResidueField O =>
      ∃ a : ResidueField O, monicPoly r = (X - C a) ^ 2)).card = residueCard O :=
    (card_dblVecs (K := ResidueField O)).trans hqcard
  have hsplitc : 2 * (Finset.univ.filter (fun r : Fin 2 → ResidueField O =>
      ∃ a b : ResidueField O, a ≠ b ∧ monicPoly r = (X - C a) * (X - C b))).card
      = residueCard O ^ 2 - residueCard O := by
    rw [two_mul_card_splitVecs (K := ResidueField O), hqcard]
  have hinertc : 2 * (Finset.univ.filter (fun r : Fin 2 → ResidueField O =>
      Irreducible (monicPoly r))).card = residueCard O ^ 2 - residueCard O := by
    rw [two_mul_card_inertVecs (K := ResidueField O), hqcard]
  -- assemble: distribute the 2, fire the counts, close by ring
  have hIQ : 2 * ((Finset.univ.filter (fun r : Fin 2 → ResidueField O =>
      Irreducible (monicPoly r))).card
        * (primo (residueCard O) 2 1 v * residueCard O ^ (2 * (2 * N - 1))))
      = (residueCard O ^ 2 - residueCard O)
        * (primo (residueCard O) 2 1 v * residueCard O ^ (2 * (2 * N - 1))) := by
    rw [← mul_assoc, hinertc]
  have hSQ : 2 * ((Finset.univ.filter (fun r : Fin 2 → ResidueField O =>
      ∃ a b : ResidueField O, a ≠ b ∧ monicPoly r = (X - C a) * (X - C b))).card
        * ((v + 1) * (residueCard O - 1) ^ 2 * residueCard O ^ (2 * (2 * N - 1))))
      = (residueCard O ^ 2 - residueCard O)
        * ((v + 1) * (residueCard O - 1) ^ 2 * residueCard O ^ (2 * (2 * N - 1))) := by
    rw [← mul_assoc, hsplitc]
  rw [mul_add, mul_add, hIQ, hSQ, hdblc]
  simp only [duo]
  ring

end Census

/-! ## §5 — ★★★ the `ZcURLim`, fired at `n = 2` -/

section URLim

/-- The limit numerator polynomial: `duo q v = (duoNum v).eval q` for `q ≥ 1`. -/
def duoNum (v : ℕ) : Polynomial ℚ :=
  Polynomial.C ((2 * ((v + 1) / 2) : ℕ) : ℚ) * Polynomial.X * (Polynomial.X - 1) ^ 2
    + Polynomial.C ((v + 1 : ℕ) : ℚ) * (Polynomial.X ^ 2 - Polynomial.X)
        * (Polynomial.X - 1) ^ 2
    + (if 2 ∣ v then
        Polynomial.C 2 * Polynomial.X ^ 2 * (Polynomial.X - 1)
          + (Polynomial.X ^ 2 - Polynomial.X) * (Polynomial.X ^ 2 - 1)
      else 0)

/-- The cast bridge: `duo` is the evaluation of `duoNum`. -/
theorem duo_cast {q : ℕ} (hq : 1 ≤ q) (v : ℕ) :
    ((duo q v : ℕ) : ℚ) = (duoNum v).eval (q : ℚ) := by
  have hqq : q ≤ q ^ 2 := by
    calc q = q ^ 1 := (pow_one q).symm
    _ ≤ q ^ 2 := Nat.pow_le_pow_right hq (by omega)
  have h1q : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ (by omega)
  simp only [duo, duoNum, primo_two_closed, primo_one (by omega : 0 < 2)]
  by_cases hd : 2 ∣ v
  · rw [if_pos hd, if_pos hd, if_pos hd]
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
      Polynomial.eval_sub, Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_one]
    push_cast [Nat.cast_sub hq, Nat.cast_sub hqq, Nat.cast_sub h1q]
    ring
  · rw [if_neg hd, if_neg hd, if_neg hd]
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
      Polynomial.eval_sub, Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_one,
      add_zero]
    push_cast [Nat.cast_sub hq, Nat.cast_sub hqq]
    ring

/-- ★★ **THE REDUCED DIAGONAL DENSITY `ZcURLim` AT `n = 2`, OUTRIGHT**: the
normalized family is eventually constant with value `duo(q,v)/(2q^{v+4})` — numerator
`duoNum v`, denominator `2X^{v+4}`. -/
theorem zcURLim_redDiag_two (v : ℕ) :
    ZcURLim (fun O _ _ _ _ _ π M =>
      ((Nat.card (redDepthPairSet O π 2 M v) : ℕ) : ℝ)
        / ((residueCard O : ℕ) : ℝ) ^ (2 * 2 * M)) := by
  refine ⟨duoNum v, Polynomial.C 2 * Polynomial.X ^ (v + 4),
    mul_ne_zero (Polynomial.C_ne_zero.mpr two_ne_zero)
      (pow_ne_zero _ Polynomial.X_ne_zero), ?_⟩
  intro O _ _ _ _ _
  have hq2 : 2 ≤ residueCard O := two_le_residueCard O
  have hq0 : ((residueCard O : ℕ) : ℚ) ≠ 0 := by
    exact_mod_cast (by omega : residueCard O ≠ 0)
  have hqR : (0 : ℝ) < ((residueCard O : ℕ) : ℝ) := by
    exact_mod_cast (by omega : 0 < residueCard O)
  have hden : (Polynomial.C 2 * Polynomial.X ^ (v + 4) : Polynomial ℚ).eval
      ((residueCard O : ℕ) : ℚ) = 2 * ((residueCard O : ℕ) : ℚ) ^ (v + 4) := by
    rw [Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X]
  refine ⟨by rw [hden]; exact mul_ne_zero two_ne_zero (pow_ne_zero _ hq0), ?_⟩
  intro π hπ
  have hval : (((duoNum v).eval ((residueCard O : ℕ) : ℚ)
        / (Polynomial.C 2 * Polynomial.X ^ (v + 4) : Polynomial ℚ).eval
            ((residueCard O : ℕ) : ℚ) : ℚ) : ℝ)
      = ((duo (residueCard O) v : ℕ) : ℝ)
        / (2 * ((residueCard O : ℕ) : ℝ) ^ (v + 4)) := by
    rw [hden, ← duo_cast (by omega : 1 ≤ residueCard O)]
    push_cast
    ring
  rw [hval]
  refine Filter.Tendsto.congr' ?_ tendsto_const_nhds
  refine Filter.eventually_atTop.mpr ⟨v + 1, fun M hM => ?_⟩
  simp only []
  have hcensus := two_mul_card_redDepthPairSet_two (O := O) hπ (by omega : v < M)
  have hcast : (2 : ℝ) * (Nat.card (redDepthPairSet O π 2 M v) : ℝ)
        * ((residueCard O : ℕ) : ℝ) ^ (v + 2)
      = ((duo (residueCard O) v : ℕ) : ℝ)
        * ((residueCard O : ℕ) : ℝ) ^ (2 * (2 * M - 1)) := by
    exact_mod_cast hcensus
  rw [div_eq_div_iff (ne_of_gt (mul_pos two_pos (pow_pos hqR _)))
    (ne_of_gt (pow_pos hqR _))]
  have hpow2 : ((residueCard O : ℕ) : ℝ) ^ (2 * 2 * M)
      = ((residueCard O : ℕ) : ℝ) ^ (2 * (2 * M - 1))
        * ((residueCard O : ℕ) : ℝ) ^ 2 := by
    rw [← pow_add]
    congr 1
    omega
  rw [hpow2]
  linear_combination (-((residueCard O : ℕ) : ℝ) ^ 2) * hcast

/-- ★★★ **THE `(2,2)` DEPTH-DENSITY `ZcURLim`, UNCONDITIONAL** — the first diagonal
firing of IFCG61's reduced-to-general transport beyond `min = 1`. -/
theorem zcURLim_depthDensity_two_two (v : ℕ) :
    ZcURLim (fun O _ _ _ _ _ π M =>
      ((Nat.card (depthPairSet O π 2 2 M v) : ℕ) : ℝ)
        / ((residueCard O : ℕ) : ℝ) ^ ((2 + 2) * M)) :=
  zcURLim_depthDensity_of_reduced (by omega) (le_refl 2) (zcURLim_redDiag_two v)

/-- ★★ The `(2, n₂)` depth-density `ZcURLim` at every `n₂ ≥ 2`. -/
theorem zcURLim_depthDensity_two_right {n₂ : ℕ} (hn : 2 ≤ n₂) (v : ℕ) :
    ZcURLim (fun O _ _ _ _ _ π M =>
      ((Nat.card (depthPairSet O π 2 n₂ M v) : ℕ) : ℝ)
        / ((residueCard O : ℕ) : ℝ) ^ ((2 + n₂) * M)) :=
  zcURLim_depthDensity_of_reduced (by omega) hn (zcURLim_redDiag_two v)

end URLim

/-! ## §6 — the regression rows: IGV's battery-verified `Z₂(t)` law

The assembled density is `duo(q,v)/(2q^{v+4})`; IGV's `m = 2` law
(`runs/wave-c/verdict_IGV.md`, 17/17 integer-exact battery) gives, with `s = 1/q`:
`P₀ = 1 − s`, `P₁ = s(1−s)²`, `P₂ = (1−s)s²(2−s)`, `P₃ = 2(1−s)²s³`,
`P₄ = (1−s)s⁴(3−2s)`.  Cleared of denominators (`duo q v = 2q^{v+4}·P_v`), these are
the five `ℚ`-identities below — the `n = 2` assembly and the independently-derived
generating function agree exactly.  (Analytically the full law also passes the mass
check `Σ_v duo(q,v)/(2q^{v+4}) = 1/q + (q−1)/(2q) + (q−1)/(2q) = 1`, the three genre
probabilities — an infinite sum, recorded here as documentation.) -/

section Regression

theorem duo_regression_v0 {q : ℕ} (hq : 1 ≤ q) :
    ((duo q 0 : ℕ) : ℚ) = 2 * (q : ℚ) ^ 3 * ((q : ℚ) - 1) := by
  have hqq : q ≤ q ^ 2 := by
    calc q = q ^ 1 := (pow_one q).symm
    _ ≤ q ^ 2 := Nat.pow_le_pow_right hq (by omega)
  have h1q : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ (by omega)
  simp only [duo, primo_two_closed, primo_one (by omega : 0 < 2)]
  norm_num
  push_cast [Nat.cast_sub hq, Nat.cast_sub hqq, Nat.cast_sub h1q]
  ring

theorem duo_regression_v1 {q : ℕ} (hq : 1 ≤ q) :
    ((duo q 1 : ℕ) : ℚ) = 2 * (q : ℚ) ^ 2 * ((q : ℚ) - 1) ^ 2 := by
  have hqq : q ≤ q ^ 2 := by
    calc q = q ^ 1 := (pow_one q).symm
    _ ≤ q ^ 2 := Nat.pow_le_pow_right hq (by omega)
  have h1q : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ (by omega)
  simp only [duo, primo_two_closed, primo_one (by omega : 0 < 2)]
  norm_num
  push_cast [Nat.cast_sub hq, Nat.cast_sub hqq, Nat.cast_sub h1q]
  ring

theorem duo_regression_v2 {q : ℕ} (hq : 1 ≤ q) :
    ((duo q 2 : ℕ) : ℚ) = 2 * (q : ℚ) ^ 2 * ((q : ℚ) - 1) * (2 * (q : ℚ) - 1) := by
  have hqq : q ≤ q ^ 2 := by
    calc q = q ^ 1 := (pow_one q).symm
    _ ≤ q ^ 2 := Nat.pow_le_pow_right hq (by omega)
  have h1q : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ (by omega)
  simp only [duo, primo_two_closed, primo_one (by omega : 0 < 2)]
  norm_num
  push_cast [Nat.cast_sub hq, Nat.cast_sub hqq, Nat.cast_sub h1q]
  ring

theorem duo_regression_v3 {q : ℕ} (hq : 1 ≤ q) :
    ((duo q 3 : ℕ) : ℚ) = 4 * (q : ℚ) ^ 2 * ((q : ℚ) - 1) ^ 2 := by
  have hqq : q ≤ q ^ 2 := by
    calc q = q ^ 1 := (pow_one q).symm
    _ ≤ q ^ 2 := Nat.pow_le_pow_right hq (by omega)
  have h1q : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ (by omega)
  simp only [duo, primo_two_closed, primo_one (by omega : 0 < 2)]
  norm_num
  push_cast [Nat.cast_sub hq, Nat.cast_sub hqq, Nat.cast_sub h1q]
  ring

theorem duo_regression_v4 {q : ℕ} (hq : 1 ≤ q) :
    ((duo q 4 : ℕ) : ℚ) = 2 * (q : ℚ) ^ 2 * ((q : ℚ) - 1) * (3 * (q : ℚ) - 2) := by
  have hqq : q ≤ q ^ 2 := by
    calc q = q ^ 1 := (pow_one q).symm
    _ ≤ q ^ 2 := Nat.pow_le_pow_right hq (by omega)
  have h1q : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ (by omega)
  simp only [duo, primo_two_closed, primo_one (by omega : 0 < 2)]
  norm_num
  push_cast [Nat.cast_sub hq, Nat.cast_sub hqq, Nat.cast_sub h1q]
  ring

end Regression

/-! ## §7 — THE NAMED REMAINDER: the general-`n` type-grouping engine

What remains of route step (d) at general `n` (none of it consumed by the `n = 2`
results above):

1. **The `n`-ary convolution**: for pairwise-coprime monic residuals `g₁, …, g_k`
   with `Σ deg gᵢ = n`, iterate `card_stratumDepthSet_mul` to
   `#strat(n, N, v, Πgᵢ) = Σ_{a₁+⋯+a_k = v} Π #strat(deg gᵢ, N, aᵢ, gᵢ)` — a list
   induction over IFCG63's landed binary step.
2. **The type grouping**: group the `q^n` summands of
   `card_redDepthPairSet_eq_sum_strata` by factorization type `λ ⊢ n` (finitely many
   per `n`); the number of monic residuals of type `λ = (δ₁^{e₁}⋯)` is the multiset
   count `Π_δ multichoose(I_δ(q), #parts of size δ)` in the Gauss counts
   `I_δ(q) = (1/δ)Σ_{d∣δ} μ(d) q^{δ/d}` — IFCG19's `necklacePoly` /
   `necklacePoly_eval_card` is the landed supplier of `I_δ` as a `ℚ`-polynomial
   value; the multiset-count bookkeeping (the analogue of §2's doubled counts, with
   `Π eᵢ!`-type multiplicities) is the genuinely new combinatorial layer.
3. **The per-type value**: each type-`λ` summand is the `λ`-convolution of `primo`
   values (step 1 + IFCG65's `card_stratumDepthSet_pow`), so the analogue of `duo` is
   `zed_n(q, v) := Σ_{λ ⊢ n} count_λ(q) · (convolution of primo's over λ's parts)(v)`
   and the general census is
   `n_λ-normalized: #redDepthPairSet(n,N,v)·q^{v+n}·(common denominator of the
   count_λ) = zed_n(q,v)·q^{n(2N−1)}`; the `ZcURLim` at every `n` follows exactly as
   in §5 (eventual constancy in the window).

Each step is finite-field combinatorics at level 1 — no new valuation theory.  IGV's
generating function `Z_m(t) = ∏_{j≤m}(1−s^j t^{j−1})/(1−s^j t^j)` is the predicted
closed form of `zed_n/(2q^{v+n+2})`-type normalizations and supplies the regression
battery per `n`, as §6 did at `n = 2`. -/

end Uniformity.Density.IFCG68

end

/-! ## AXCHECK FOOTER — EVERY row expects PURE Lean core
`{propext, Classical.choice, Quot.sound}`.  B.42, the C.33 cites, and
`AX_cellRecursion` must NOT occur. -/
#print axioms Uniformity.Density.IFCG68.monicPoly_injective
#print axioms Uniformity.Density.IFCG68.monicPoly_splitVec
#print axioms Uniformity.Density.IFCG68.monicPoly_dblVec
#print axioms Uniformity.Density.IFCG68.isCoprime_X_sub_C_of_ne
#print axioms Uniformity.Density.IFCG68.split_or_dbl_of_not_irreducible
#print axioms Uniformity.Density.IFCG68.card_dblVecs
#print axioms Uniformity.Density.IFCG68.two_mul_card_splitVecs
#print axioms Uniformity.Density.IFCG68.two_mul_card_inertVecs
#print axioms Uniformity.Density.IFCG68.card_stratumDepthSet_linear
#print axioms Uniformity.Density.IFCG68.card_stratumDepthSet_double
#print axioms Uniformity.Density.IFCG68.card_stratumDepthSet_inert
#print axioms Uniformity.Density.IFCG68.card_stratumDepthSet_split
#print axioms Uniformity.Density.IFCG68.primo_two_closed
#print axioms Uniformity.Density.IFCG68.two_mul_card_redDepthPairSet_two
#print axioms Uniformity.Density.IFCG68.duo_cast
#print axioms Uniformity.Density.IFCG68.zcURLim_redDiag_two
#print axioms Uniformity.Density.IFCG68.zcURLim_depthDensity_two_two
#print axioms Uniformity.Density.IFCG68.zcURLim_depthDensity_two_right
#print axioms Uniformity.Density.IFCG68.duo_regression_v0
#print axioms Uniformity.Density.IFCG68.duo_regression_v1
#print axioms Uniformity.Density.IFCG68.duo_regression_v2
#print axioms Uniformity.Density.IFCG68.duo_regression_v3
#print axioms Uniformity.Density.IFCG68.duo_regression_v4
