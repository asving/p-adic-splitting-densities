/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.Density.Gates

/-!
# Uniformity.Density.Drainage — the `n = 2` DRAINAGE THEOREM

**What this file proves.** For every complete DVR `O` with finite residue field, every
splitting type `σ` and degree `n = 2`, the undecided mass drains:

    UndecidedVanishes O 2 σ                    (`drainage_two`)

hence, by the tie already in `GenuineDensity.lean`, `upperDensity O 2 σ = genuineDensity O 2 σ`
(`upperDensity_eq_two`) — the bracket closes and the level-`N` decided proportion converges to
*the* density. The exact-value payoff that follows is

    genuineDensity O 2 split + genuineDensity O 2 inert + genuineDensity O 2 ram = 1
                                               (`sum_three_densities_eq_one`)

— an EXACT `n = 2` identity over an arbitrary `O`, which is W-11 clause (iii)'s exhaustiveness
(`Σ = 1`) in the Part-1 language.

## The mechanism (the mathematics, before the Lean)

Write `F(γ) = γ² + a₁γ + a₀` for the value of the monic quadratic `X² + a₁X + a₀` at `γ` and
`F'(γ) = 2γ + a₁` for its derivative (`qval`, `qder`). The single invariant that governs
decidedness is the **tangency depth**

    T(a) = sup_γ min ( v(F(γ)), 2·v(F'(γ)) )        (`Tang`: `Tang π a t γ` says `min ≥ t`)

* **`T(a) < N` ⟹ the level-`N` class of `a` is decided** (`decidedAt_of_not_tang`). Choose `γ`
  attaining the sup. The Newton polygon of the recentred `X² + F'(γ)X + F(γ)` then falls into
  exactly three readable shapes — and the fourth, "residual double root", is impossible
  *because it would push the sup up*. The three shapes are the three certificates below:
  `CertSplit` (a simple Newton root: `v(F) > 2v(F')`, Hensel gives a root of `f` in `O`, so `f`
  is reducible and `typeOf f = split`), `CertRam` (`v(F)` ODD and `≤ 2v(F')`: irreducible with a
  norm of odd valuation, so `f(g) = gcd(2, odd) = 1` and `e = 2`), `CertInert` (`v(F) = 2k` even,
  `v(F') ≥ k`, residual binary form anisotropic: every norm valuation is even, so `f(g) = 2`).
  Each certificate reads only data below the window, so it transfers verbatim to every other
  lift of the class (`CertSplit_congr` &c.) — that is what "decided" means.
* **`T(a) ≥ N` costs `q^{-N}`.** If `π^{2M} ∣ F(γ)` and `π^M ∣ F'(γ)` then `γ` matters only mod
  `π^M` (changing `γ` by `π^M t` moves `F(γ)` by `π^M t F'(γ) + π^{2M}t² ∈ π^{2M}`), and the
  class is pinned by `(γ mod π^M, a₁ mod π^{2M})` — because `a₀ ≡ -γ² - a₁γ (mod π^{2M})`. So at
  most `q^M · q^{2M} = q^{3M}` of the `q^{4M}` classes at level `2M` are undecided
  (`undecidedCount_le`), i.e. the undecided proportion is `≤ q^{-M} → 0`.

The count `q^{3M}` is deliberately lossy: W-11's exact law is `q^N` undecided classes at level
`N` (here `q^{2M}`, so the bound is off by the factor `q^M`). Drainage only needs a bound that
beats `q^{2N}`, and the lossy one is `q^{-M}` — a proof of the exact law would need the
per-centre census, which is not needed for anything downstream.

## Status

Sorry-free, axiom-free (Lean core only).
-/

set_option linter.style.longLine false

namespace Uniformity.Density

open IsLocalRing Polynomial Filter Topology IsDiscreteValuationRing

/-! ## 1. A `ℕ`-valued valuation API: `π ^ k ∣ x` -/

section Val

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {π : O}

theorem pow_dvd_iff_le_addVal (hπ : Irreducible π) (k : ℕ) (x : O) :
    π ^ k ∣ x ↔ (k : ℕ∞) ≤ addVal O x := by
  rw [← addVal_le_iff_dvd, hπ.addVal_pow]

/-- Every nonzero element has a `ℕ`-valued valuation. -/
theorem exists_addVal_eq {x : O} (hx : x ≠ 0) : ∃ n : ℕ, addVal O x = (n : ℕ∞) := by
  obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.1 (fun h => hx (addVal_eq_top_iff.1 h))
  exact ⟨n, hn.symm⟩

/-- Divisibility by `π ^ k` read off the `ℕ`-valued valuation. -/
theorem pow_dvd_iff_le {x : O} {n : ℕ} (hπ : Irreducible π) (hx : addVal O x = (n : ℕ∞))
    (k : ℕ) : π ^ k ∣ x ↔ k ≤ n := by
  rw [pow_dvd_iff_le_addVal hπ, hx]
  exact_mod_cast Iff.rfl

/-- Exact divisibility pins the valuation. -/
theorem addVal_eq_of_dvd_not_dvd (hπ : Irreducible π) {x : O} {n : ℕ} (h1 : π ^ n ∣ x)
    (h2 : ¬ π ^ (n + 1) ∣ x) : addVal O x = (n : ℕ∞) := by
  have hx : x ≠ 0 := by rintro rfl; exact h2 (dvd_zero _)
  obtain ⟨m, hm⟩ := exists_addVal_eq hx
  rw [pow_dvd_iff_le hπ hm] at h1 h2
  rw [hm]
  congr 1
  omega

theorem ne_zero_of_not_dvd {x : O} {n : ℕ} (h : ¬ π ^ n ∣ x) : x ≠ 0 := by
  rintro rfl; exact h (dvd_zero _)

/-- **The splitting lemma.** If `π ^ (m + n)` divides a product and `π ^ (m+1)` misses the left
factor, then `π ^ n` divides the right one. -/
theorem pow_dvd_right_of_mul (hπ : Irreducible π) {x y : O} {m n : ℕ}
    (h : π ^ (m + n) ∣ x * y) (hx : ¬ π ^ (m + 1) ∣ x) : π ^ n ∣ y := by
  rcases eq_or_ne y 0 with rfl | hy
  · exact dvd_zero _
  have hx0 : x ≠ 0 := ne_zero_of_not_dvd hx
  obtain ⟨α, hα⟩ := exists_addVal_eq hx0
  obtain ⟨β, hβ⟩ := exists_addVal_eq hy
  have hxy : addVal O (x * y) = ((α + β : ℕ) : ℕ∞) := by
    rw [AddValuation.map_mul, hα, hβ]; push_cast; ring
  rw [pow_dvd_iff_le hπ hxy] at h
  rw [pow_dvd_iff_le hπ hα] at hx
  rw [pow_dvd_iff_le hπ hβ]
  omega

/-- An odd exact valuation on a product forbids a deep common divisor of the sum: this is why
a Newton polygon with one side of odd slope-numerator is irreducible. -/
theorem no_odd_exact_of_split (hπ : Irreducible π) {x y : O} {j : ℕ}
    (h1 : π ^ (2 * j + 1) ∣ x * y) (h2 : ¬ π ^ (2 * j + 2) ∣ x * y)
    (h3 : π ^ (j + 1) ∣ x + y) : False := by
  by_cases hx : π ^ (j + 1) ∣ x
  · have hy : π ^ (j + 1) ∣ y := by
      have : y = (x + y) - x := by ring
      rw [this]; exact dvd_sub h3 hx
    refine h2 ?_
    have := mul_dvd_mul hx hy
    rwa [← pow_add, show j + 1 + (j + 1) = 2 * j + 2 by ring] at this
  · have hy : π ^ (j + 1) ∣ y :=
      pow_dvd_right_of_mul hπ (by rwa [show j + (j + 1) = 2 * j + 1 by ring]) hx
    refine hx ?_
    have : x = (x + y) - y := by ring
    rw [this]; exact dvd_sub h3 hy

/-- If a product has exact even valuation `2k` and the sum has valuation `≥ k`, then both
factors have valuation exactly `k`. (The "equal-valuation roots" case of the polygon read.) -/
theorem pow_dvd_both_of_even (hπ : Irreducible π) {x y : O} {k : ℕ}
    (h1 : π ^ (2 * k) ∣ x * y) (h2 : ¬ π ^ (2 * k + 1) ∣ x * y) (h3 : π ^ k ∣ x + y) :
    π ^ k ∣ x ∧ π ^ k ∣ y := by
  have hxy0 : x * y ≠ 0 := ne_zero_of_not_dvd h2
  have hx0 : x ≠ 0 := fun h => hxy0 (by rw [h]; ring)
  have hy0 : y ≠ 0 := fun h => hxy0 (by rw [h]; ring)
  obtain ⟨α, hα⟩ := exists_addVal_eq hx0
  obtain ⟨β, hβ⟩ := exists_addVal_eq hy0
  have hprod : addVal O (x * y) = ((α + β : ℕ) : ℕ∞) := by
    rw [AddValuation.map_mul, hα, hβ]; push_cast; ring
  rw [pow_dvd_iff_le hπ hprod] at h1 h2
  have hsum : α + β = 2 * k := by omega
  -- if one of them dipped below `k`, the other would exceed `k` and the sum would dip too
  have hxk : k ≤ α := by
    by_contra hlt
    have hyk : π ^ k ∣ y := (pow_dvd_iff_le hπ hβ k).2 (by omega)
    have : π ^ k ∣ x := by
      have hxe : x = (x + y) - y := by ring
      rw [hxe]; exact dvd_sub h3 hyk
    rw [pow_dvd_iff_le hπ hα] at this
    omega
  have hyk : k ≤ β := by
    by_contra hlt
    have hxk' : π ^ k ∣ x := (pow_dvd_iff_le hπ hα k).2 (by omega)
    have : π ^ k ∣ y := by
      have hye : y = (x + y) - x := by ring
      rw [hye]; exact dvd_sub h3 hxk'
    rw [pow_dvd_iff_le hπ hβ] at this
    omega
  exact ⟨(pow_dvd_iff_le hπ hα k).2 hxk, (pow_dvd_iff_le hπ hβ k).2 hyk⟩

/-- `π ∤ u` means `u` is a unit (the residue ring is a field). -/
theorem isUnit_of_not_dvd (hπ : Irreducible π) {u : O} (h : ¬ π ∣ u) : IsUnit u := by
  by_contra hu
  refine h ?_
  have hmem : u ∈ IsLocalRing.maximalIdeal O :=
    (IsLocalRing.mem_maximalIdeal _).2 (mem_nonunits_iff.2 hu)
  rwa [hπ.maximalIdeal_eq, Ideal.mem_span_singleton] at hmem

theorem not_dvd_of_isUnit (hπ : Irreducible π) {u : O} (h : IsUnit u) : ¬ π ∣ u := by
  rintro ⟨c, rfl⟩
  exact hπ.not_isUnit (isUnit_of_mul_isUnit_left h)

theorem mem_maximalIdeal_iff_dvd (hπ : Irreducible π) (x : O) :
    x ∈ IsLocalRing.maximalIdeal O ↔ π ∣ x := by
  rw [hπ.maximalIdeal_eq, Ideal.mem_span_singleton]

end Val

/-! ## 2. The value and the derivative of a monic quadratic at a centre -/

section Quad

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

/-- `F(γ) = γ² + a₁γ + a₀` — the value of `monicPoly a` at `γ`, i.e. the constant term of the
polynomial recentred at `γ`. -/
def qval (a : Fin 2 → O) (γ : O) : O := γ ^ 2 + a 1 * γ + a 0

/-- `F'(γ) = 2γ + a₁` — the linear coefficient of `monicPoly a` recentred at `γ`. -/
def qder (a : Fin 2 → O) (γ : O) : O := 2 * γ + a 1

theorem qval_eq_eval (a : Fin 2 → O) (γ : O) : qval a γ = (monicPoly a).eval γ := by
  rw [monicPoly_two_eval, qval]; ring

theorem qval_shift (a : Fin 2 → O) (γ δ : O) :
    qval a (γ + δ) = qval a γ + qder a γ * δ + δ ^ 2 := by
  simp only [qval, qder]; ring

theorem qder_shift (a : Fin 2 → O) (γ δ : O) : qder a (γ + δ) = qder a γ + 2 * δ := by
  simp only [qder]; ring

/-- `F(γ) = (γ - r)(γ - s)` when the quadratic splits as `(X-r)(X-s)`. -/
theorem qval_of_roots {a : Fin 2 → O} {r s : O} (h1 : a 1 = -(r + s)) (h0 : a 0 = r * s)
    (γ : O) : qval a γ = (γ - r) * (γ - s) := by
  simp only [qval, h0, h1]; ring

theorem qder_of_roots {a : Fin 2 → O} {r s : O} (h1 : a 1 = -(r + s)) (γ : O) :
    qder a γ = (γ - r) + (γ - s) := by
  simp only [qder, h1]; ring

/-- The norm form evaluated at `(γ, -1)` is the value `F(γ)`. -/
theorem quadForm_centre (a : Fin 2 → O) (γ : O) : quadForm a γ (-1) = qval a γ := by
  simp only [quadForm, qval]; ring

end Quad

/-! ## 3. The three decidedness certificates and the types they force -/

section Cert

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

/-- **SPLIT certificate at window `N`.** At the centre `γ` the derivative has EXACT valuation
`w` with `2w < N`, and the value has valuation `> 2w`: the Newton polygon has a side of length
one at a simple root, so Hensel produces a root of `f` in `O`. -/
def CertSplit (π : O) (a : Fin 2 → O) (N : ℕ) : Prop :=
  ∃ (γ : O) (w : ℕ), 2 * w + 1 ≤ N ∧ π ^ w ∣ qder a γ ∧ ¬ π ^ (w + 1) ∣ qder a γ ∧
    π ^ (2 * w + 1) ∣ qval a γ

/-- **RAM certificate at window `N`.** At the centre `γ` the value has EXACT ODD valuation
`2j+1 < N` and the derivative has valuation `≥ j+1`: one polygon side of denominator `2`. -/
def CertRam (π : O) (a : Fin 2 → O) (N : ℕ) : Prop :=
  ∃ (γ : O) (j : ℕ), 2 * j + 2 ≤ N ∧ π ^ (2 * j + 1) ∣ qval a γ ∧
    ¬ π ^ (2 * j + 2) ∣ qval a γ ∧ π ^ (j + 1) ∣ qder a γ

/-- **INERT certificate at window `N`.** At the centre `γ` the value has valuation `2k` with
`2k < N`, the derivative valuation `≥ k`, and the residual binary form `![b₀, b₁]` is
anisotropic. (Anisotropy forces `b₀` to be a unit, so the valuation `2k` is exact.) -/
def CertInert (π : O) (a : Fin 2 → O) (N : ℕ) : Prop :=
  ∃ (γ : O) (k : ℕ) (b₀ b₁ : O), 2 * k + 1 ≤ N ∧ qval a γ = π ^ (2 * k) * b₀ ∧
    qder a γ = π ^ k * b₁ ∧ Anisotropic ![b₀, b₁]

/-- A monic quadratic with a root in `O` has the SPLIT type (the second root is `-a₁ - R`). -/
theorem typeOf_split_of_root {a : Fin 2 → O} {R : O} (h : qval a R = 0) :
    typeOf (monicPoly a) = splitType := by
  have ha0 : a 0 = -(R ^ 2) - a 1 * R := by
    simp only [qval] at h; linear_combination h
  have hfac : monicPoly a = (X - C R) * (X - C (-(a 1) - R)) := by
    rw [monicPoly_two_expand, ha0]
    simp only [map_sub, map_neg, map_mul, map_pow]
    ring
  rw [hfac]
  exact typeOf_mul_linear R _

/-- Anisotropy makes `b₀` a unit: `quadForm ![b₀,b₁] 0 1 = b₀`. -/
theorem not_dvd_of_anisotropic {π : O} (hπ : Irreducible π) {b₀ b₁ : O}
    (h : Anisotropic ![b₀, b₁]) : ¬ π ∣ b₀ := by
  intro hdvd
  have hmem : quadForm ![b₀, b₁] 0 1 ∈ IsLocalRing.maximalIdeal O := by
    rw [show quadForm ![b₀, b₁] (0 : O) 1 = b₀ by simp [quadForm]]
    exact (mem_maximalIdeal_iff_dvd hπ b₀).2 hdvd
  exact (IsLocalRing.maximalIdeal.isMaximal O).ne_top ((Ideal.eq_top_iff_one _).2 (h 0 1 hmem).2)

/-- **RAM.** The odd-exact-valuation certificate forces `typeOf = {(2,1)}`: the polynomial is
irreducible, `2` and the odd `2j+1` are both norm valuations, and their gcd — the residue
degree — is `1`, so `e = 2/1 = 2`. -/
theorem typeOf_of_certRam {π : O} (hπ : Irreducible π) {a : Fin 2 → O} {N : ℕ}
    (h : CertRam π a N) : typeOf (monicPoly a) = ramType := by
  obtain ⟨γ, j, -, hv1, hv2, hd⟩ := h
  have hirr : Irreducible (monicPoly a) := by
    by_contra hcon
    obtain ⟨r, s, h1, h0⟩ := exists_roots_of_not_irreducible hcon
    rw [qval_of_roots h1 h0] at hv1 hv2
    rw [qder_of_roots h1] at hd
    exact no_odd_exact_of_split hπ hv1 hv2 hd
  -- the element `γ - α` has norm `F(γ)`, of exact odd valuation `2j+1`
  have hnorm : Algebra.norm O (algebraMap O (AdjoinRoot (monicPoly a)) γ
      + algebraMap O (AdjoinRoot (monicPoly a)) (-1) * AdjoinRoot.root (monicPoly a))
      = qval a γ := by
    rw [norm_quad]; simp only [qval]; ring
  have hqne : qval a γ ≠ 0 := ne_zero_of_not_dvd hv2
  have hxne : algebraMap O (AdjoinRoot (monicPoly a)) γ
      + algebraMap O (AdjoinRoot (monicPoly a)) (-1) * AdjoinRoot.root (monicPoly a) ≠ 0 := by
    intro hz
    rw [hz, norm_zero_quad] at hnorm
    exact hqne hnorm.symm
  have hmem1 : (2 * j + 1) ∈ normValues (monicPoly a) :=
    ⟨by omega, _, hxne, by rw [hnorm]; exact addVal_eq_of_dvd_not_dvd hπ hv1 hv2⟩
  have hmem2 : (2 : ℕ) ∈ normValues (monicPoly a) := by
    have := natDegree_mem_normValues (monicPoly_monic a) (by rw [monicPoly_natDegree]; omega) hπ
    rwa [monicPoly_natDegree] at this
  have hcop : Nat.gcd 2 (2 * j + 1) = 1 := by
    have hg1 := Nat.gcd_dvd_left 2 (2 * j + 1)
    have hg2 := Nat.gcd_dvd_right 2 (2 * j + 1)
    rcases (Nat.dvd_prime Nat.prime_two).1 hg1 with h3 | h3
    · exact h3
    · rw [h3] at hg2; omega
  have hinf : inertiaDegOf (monicPoly a) = 1 :=
    inertiaDegOf_eq_one_of_coprime hmem2 hmem1 hcop
  have hF : IsMonicFactorization (monicPoly a) {monicPoly a} :=
    ⟨by intro g hg; rw [Multiset.mem_singleton.1 hg]; exact ⟨monicPoly_monic a, hirr⟩, by simp⟩
  ext
  rw [typeOf_data, monicFactors_eq hF]
  simp [ramType, efPair, ramIndexOf, hinf, monicPoly_natDegree]

/-- **INERT.** The even-valuation certificate with anisotropic residual form: the change of
variables `(U,V) ↦ (U + γV, π^k V)` carries `quadForm a` into `quadForm ![b₀,b₁]`, so EVERY
norm valuation of `a` is even (`two_dvd_of_val_quadForm`), and `2 = deg` is attained: the
residue degree is `2` and `e = 1`. -/
theorem typeOf_of_certInert {π : O} (hπ : Irreducible π) {a : Fin 2 → O} {N : ℕ}
    (h : CertInert π a N) : typeOf (monicPoly a) = inertType := by
  obtain ⟨γ, k, b₀, b₁, -, hval, hder, haniso⟩ := h
  simp only [qval] at hval
  simp only [qder] at hder
  -- the unimodular-in-`U` change of variables
  have hform : ∀ U V : O, quadForm a U V = quadForm ![b₀, b₁] (U + γ * V) (π ^ k * V) := by
    intro U V
    simp only [quadForm, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
    linear_combination (V ^ 2) * hval - ((U + γ * V) * V) * hder
  have hdvd : ∀ m ∈ normValues (monicPoly a), 2 ∣ m := by
    rintro m ⟨-, x, -, hx⟩
    obtain ⟨u, v, rfl⟩ := exists_quad_repr a x
    rw [norm_quad] at hx
    rw [show u ^ 2 - a 1 * u * v + a 0 * v ^ 2 = quadForm a u v from rfl, hform u v] at hx
    exact two_dvd_of_val_quadForm haniso hπ m _ _ hx
  have hmem2 : (2 : ℕ) ∈ normValues (monicPoly a) := by
    have := natDegree_mem_normValues (monicPoly_monic a) (by rw [monicPoly_natDegree]; omega) hπ
    rwa [monicPoly_natDegree] at this
  have hinf : inertiaDegOf (monicPoly a) = 2 := inertiaDegOf_eq_of hmem2 hdvd
  -- irreducibility: two roots would have equal valuation `k`, giving the residual form a zero
  have hb₀ : ¬ π ∣ b₀ := not_dvd_of_anisotropic hπ haniso
  have hirr : Irreducible (monicPoly a) := by
    by_contra hcon
    obtain ⟨r, s, h1, h0⟩ := exists_roots_of_not_irreducible hcon
    have hxy : (γ - r) * (γ - s) = π ^ (2 * k) * b₀ := by
      rw [← qval_of_roots h1 h0 γ]; simp only [qval]; linear_combination hval
    have hsum : (γ - r) + (γ - s) = π ^ k * b₁ := by
      rw [← qder_of_roots h1 γ]; simp only [qder]; linear_combination hder
    have hd1 : π ^ (2 * k) ∣ (γ - r) * (γ - s) := ⟨b₀, hxy⟩
    have hd2 : ¬ π ^ (2 * k + 1) ∣ (γ - r) * (γ - s) := by
      rw [hxy]
      rintro ⟨t, ht⟩
      refine hb₀ ⟨t, ?_⟩
      refine mul_left_cancel₀ (pow_ne_zero (2 * k) hπ.ne_zero) ?_
      rw [ht]; ring
    have hd3 : π ^ k ∣ (γ - r) + (γ - s) := ⟨b₁, hsum⟩
    obtain ⟨⟨x', hx'⟩, ⟨y', hy'⟩⟩ := pow_dvd_both_of_even hπ hd1 hd2 hd3
    have hb₀eq : b₀ = x' * y' := by
      refine mul_left_cancel₀ (pow_ne_zero (2 * k) hπ.ne_zero) ?_
      rw [← hxy, hx', hy']; ring
    have hb₁eq : b₁ = x' + y' := by
      refine mul_left_cancel₀ (pow_ne_zero k hπ.ne_zero) ?_
      rw [← hsum, hx', hy']; ring
    have hzero : quadForm ![b₀, b₁] x' 1 = 0 := by
      simp only [quadForm, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
        hb₀eq, hb₁eq]
      ring
    have hmem : quadForm ![b₀, b₁] x' 1 ∈ IsLocalRing.maximalIdeal O := by
      rw [hzero]; exact Ideal.zero_mem _
    exact (IsLocalRing.maximalIdeal.isMaximal O).ne_top
      ((Ideal.eq_top_iff_one _).2 (haniso x' 1 hmem).2)
  have hF : IsMonicFactorization (monicPoly a) {monicPoly a} :=
    ⟨by intro g hg; rw [Multiset.mem_singleton.1 hg]; exact ⟨monicPoly_monic a, hirr⟩, by simp⟩
  ext
  rw [typeOf_data, monicFactors_eq hF]
  simp [inertType, efPair, ramIndexOf, hinf, monicPoly_natDegree]

end Cert

/-! ### The SPLIT certificate needs Hensel, hence completeness -/

section CertSplitComplete

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [IsAdicComplete (IsLocalRing.maximalIdeal O) O]

/-- Hensel at a simple residue root: `y² + c₁y + c₀` with `c₁` a unit and `c₀ ∈ 𝔪` has a root. -/
theorem exists_root_of_unit_deriv {c : Fin 2 → O} (h0 : c 0 ∈ IsLocalRing.maximalIdeal O)
    (h1 : IsUnit (c 1)) : ∃ r : O, qval c r = 0 := by
  obtain ⟨r, hr, -⟩ :=
    HenselianLocalRing.is_henselian (monicPoly c) (monicPoly_monic c) 0
      (by rw [monicPoly_two_eval]; simpa using h0)
      (by rw [monicPoly_two_deriv_eval]; simpa using h1)
  exact ⟨r, by rw [qval_eq_eval]; exact hr⟩

/-- **SPLIT.** Newton's condition `v(F(γ)) > 2 v(F'(γ))` produces a root of `f` in `O`, so `f`
is reducible and `typeOf f = {(1,1),(1,1)}`. -/
theorem typeOf_of_certSplit {π : O} (hπ : Irreducible π) {a : Fin 2 → O} {N : ℕ}
    (h : CertSplit π a N) : typeOf (monicPoly a) = splitType := by
  obtain ⟨γ, w, -, hd1, hd2, hv⟩ := h
  obtain ⟨e, he⟩ := hd1
  obtain ⟨d, hd⟩ := hv
  have heu : IsUnit e := by
    refine isUnit_of_not_dvd hπ (fun hdvd => hd2 ?_)
    obtain ⟨e', he'⟩ := hdvd
    exact ⟨e', by rw [he, he']; ring⟩
  obtain ⟨y, hy⟩ := exists_root_of_unit_deriv (c := ![π * d, e])
    (by simpa using (mem_maximalIdeal_iff_dvd hπ (π * d)).2 ⟨d, rfl⟩) (by simpa using heu)
  simp only [qval, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] at hy
  refine typeOf_split_of_root (R := γ + π ^ w * y) ?_
  rw [qval_shift, he, hd]
  linear_combination (π ^ (2 * w)) * hy

end CertSplitComplete

end Uniformity.Density
