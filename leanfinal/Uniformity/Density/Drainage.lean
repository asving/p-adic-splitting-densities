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

hence, by the tie already in `GenuineDensity.lean`,

    genuineDensity O 2 σ = decidedDensity O 2 σ    (`genuineDensity_eq_decidedDensity_two`)

— the outer approximation of the type-σ locus (possible cylinders) and the inner one (decided
cylinders) have the same limit. *(Read that as stated: it identifies two limits of cylinder
counts. It is NOT a formal statement that the common value is the Haar measure of the type-σ
locus — that bridge needs measurability of the locus and of the approximations, and is not
formalized here. Nothing downstream needs it: `genuineDensity`, the outer limit, is what the
capstone quantifies over, and it is a first-class object either way.)*

**This tie is what licenses the whole `n = 2` re-key.** `Gates.lean` sits below this file and
can therefore only state its `n = 2` gates over `decidedDensity` (all suffixed `_decided`);
§9 at the end of this file transfers every one of them to THE density `genuineDensity` under
the unsuffixed name. The exact-value payoff is

    genuineDensity O 2 split + genuineDensity O 2 inert + genuineDensity O 2 ram = 1
                                               (`sum_three_densities_eq_one`)

— an EXACT `n = 2` identity over an arbitrary `O`, which is W-11 clause (iii)'s exhaustiveness
(`Σ = 1`) in the Part-1 language, and the `n = 2` instance of the named general-`n` target
`TotalMassOne` (`totalMass_two`).

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

/-! ## 4. The certificates are properties of the CLASS, not of the lift -/

section Invariance

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {π : O}

/-- `a` and `b` agree modulo `π ^ N` coefficientwise. -/
def CongAt (π : O) (N : ℕ) (a b : Fin 2 → O) : Prop := ∀ i, π ^ N ∣ (b i - a i)

theorem CongAt_symm {N : ℕ} {a b : Fin 2 → O} (h : CongAt π N a b) : CongAt π N b a :=
  fun i => (dvd_sub_comm).1 (h i)

theorem qval_congr {N : ℕ} {a b : Fin 2 → O} (h : CongAt π N a b) (γ : O) :
    π ^ N ∣ (qval b γ - qval a γ) := by
  have hexp : qval b γ - qval a γ = (b 0 - a 0) + (b 1 - a 1) * γ := by simp only [qval]; ring
  rw [hexp]
  exact dvd_add (h 0) ((h 1).mul_right γ)

theorem qder_congr {N : ℕ} {a b : Fin 2 → O} (h : CongAt π N a b) (γ : O) :
    π ^ N ∣ (qder b γ - qder a γ) := by
  have hexp : qder b γ - qder a γ = b 1 - a 1 := by simp only [qder]; ring
  rw [hexp]; exact h 1

/-- Transfer a divisibility across a congruence, provided the exponent is inside the window. -/
theorem dvd_transfer {N j : ℕ} {x y : O} (hj : j ≤ N) (hd : π ^ N ∣ (y - x)) (h : π ^ j ∣ x) :
    π ^ j ∣ y := by
  have hy : y = x + (y - x) := by ring
  rw [hy]
  exact dvd_add h (dvd_trans (pow_dvd_pow π hj) hd)

theorem CertSplit_congr {N : ℕ} {a b : Fin 2 → O} (hab : CongAt π N a b) (h : CertSplit π a N) :
    CertSplit π b N := by
  obtain ⟨γ, w, hw, hd1, hd2, hv⟩ := h
  refine ⟨γ, w, hw, dvd_transfer (by omega) (qder_congr hab γ) hd1, ?_,
    dvd_transfer (by omega) (qval_congr hab γ) hv⟩
  intro hcon
  exact hd2 (dvd_transfer (N := N) (by omega) (qder_congr (CongAt_symm hab) γ) hcon)

theorem CertRam_congr {N : ℕ} {a b : Fin 2 → O} (hab : CongAt π N a b) (h : CertRam π a N) :
    CertRam π b N := by
  obtain ⟨γ, j, hj, hv1, hv2, hd⟩ := h
  refine ⟨γ, j, hj, dvd_transfer (by omega) (qval_congr hab γ) hv1, ?_,
    dvd_transfer (N := N) (by omega) (qder_congr hab γ) hd⟩
  intro hcon
  exact hv2 (dvd_transfer (N := N) (by omega) (qval_congr (CongAt_symm hab) γ) hcon)

/-- Anisotropy only reads the residual form mod `π`. -/
theorem Anisotropic_congr (hπ : Irreducible π) {c c' : Fin 2 → O} (h : Anisotropic c)
    (h0 : π ∣ (c' 0 - c 0)) (h1 : π ∣ (c' 1 - c 1)) : Anisotropic c' := by
  intro u v huv
  refine h u v ?_
  have hexp : quadForm c u v
      = quadForm c' u v + ((c' 1 - c 1) * u * v - (c' 0 - c 0) * v ^ 2) := by
    simp only [quadForm]; ring
  rw [hexp]
  refine Ideal.add_mem _ huv (Ideal.sub_mem _ ?_ ?_)
  · exact (mem_maximalIdeal_iff_dvd hπ _).2 (((h1.mul_right u).mul_right v))
  · exact (mem_maximalIdeal_iff_dvd hπ _).2 (h0.mul_right (v ^ 2))

theorem CertInert_congr (hπ : Irreducible π) {N : ℕ} {a b : Fin 2 → O} (hab : CongAt π N a b)
    (h : CertInert π a N) : CertInert π b N := by
  obtain ⟨γ, k, b₀, b₁, hk, hval, hder, haniso⟩ := h
  obtain ⟨t₀, ht₀⟩ : π ^ (2 * k + 1) ∣ (qval b γ - qval a γ) :=
    dvd_trans (pow_dvd_pow π hk) (qval_congr hab γ)
  obtain ⟨t₁, ht₁⟩ : π ^ (k + 1) ∣ (qder b γ - qder a γ) :=
    dvd_trans (pow_dvd_pow π (by omega)) (qder_congr hab γ)
  refine ⟨γ, k, b₀ + π * t₀, b₁ + π * t₁, hk, ?_, ?_, ?_⟩
  · have hb : qval b γ = qval a γ + π ^ (2 * k + 1) * t₀ := by linear_combination ht₀
    rw [hb, hval]; ring
  · have hb : qder b γ = qder a γ + π ^ (k + 1) * t₁ := by linear_combination ht₁
    rw [hb, hder]; ring
  · refine Anisotropic_congr hπ haniso ?_ ?_ <;> simp

end Invariance

/-! ## 5. The tangency depth and the DICHOTOMY

`Tang π a t γ` says `min ( v(F(γ)), 2 v(F'(γ)) ) ≥ t`. If no centre reaches depth `N`, then the
deepest centre carries one of the three certificates: the fourth polygon shape (residual double
root) is excluded *because it would reach depth `t + 1`*. -/

section Dichotomy

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {π : O}

/-- **Tangency of depth `t` at the centre `γ`**: `π ^ t ∣ F(γ)` and `π ^ ⌈t/2⌉ ∣ F'(γ)`. -/
def Tang (π : O) (a : Fin 2 → O) (t : ℕ) (γ : O) : Prop :=
  π ^ t ∣ qval a γ ∧ π ^ ((t + 1) / 2) ∣ qder a γ

theorem Tang_zero (π : O) (a : Fin 2 → O) (γ : O) : Tang π a 0 γ := by
  constructor <;> simp

theorem Tang_mono {a : Fin 2 → O} {t t' : ℕ} {γ : O} (h : t ≤ t') (ht : Tang π a t' γ) :
    Tang π a t γ :=
  ⟨dvd_trans (pow_dvd_pow π h) ht.1, dvd_trans (pow_dvd_pow π (by omega)) ht.2⟩

/-- If the residual binary form is not anisotropic, the residual quadratic has a root mod `π`
(the coordinate `v` of a nontrivial zero must be a unit, and `z = -u/v` is the root). -/
theorem exists_residual_root (hπ : Irreducible π) {b₀ b₁ : O} (h : ¬ Anisotropic ![b₀, b₁]) :
    ∃ z : O, π ∣ (z ^ 2 + b₁ * z + b₀) := by
  have h' : ∃ u v : O, quadForm ![b₀, b₁] u v ∈ IsLocalRing.maximalIdeal O ∧
      ¬(u ∈ IsLocalRing.maximalIdeal O ∧ v ∈ IsLocalRing.maximalIdeal O) := by
    by_contra hcon
    refine h (fun u v huv => ?_)
    by_contra hnb
    exact hcon ⟨u, v, huv, hnb⟩
  obtain ⟨u, v, huv, hnot⟩ := h'
  simp only [quadForm, Matrix.cons_val_zero, Matrix.cons_val_one] at huv
  have huv' : π ∣ (u ^ 2 - b₁ * u * v + b₀ * v ^ 2) := (mem_maximalIdeal_iff_dvd hπ _).1 huv
  have hvunit : IsUnit v := by
    by_contra hvn
    have hvd : π ∣ v :=
      (mem_maximalIdeal_iff_dvd hπ v).1 ((IsLocalRing.mem_maximalIdeal _).2 (mem_nonunits_iff.2 hvn))
    have hu2 : π ∣ u ^ 2 := by
      have hsplit : u ^ 2 = (u ^ 2 - b₁ * u * v + b₀ * v ^ 2) + (b₁ * u * v - b₀ * v ^ 2) := by ring
      rw [hsplit]
      refine dvd_add huv' (dvd_sub (hvd.mul_left (b₁ * u)) ?_)
      rw [pow_two]
      exact (hvd.mul_left v).mul_left b₀
    exact hnot ⟨(mem_maximalIdeal_iff_dvd hπ u).2 (hπ.prime.dvd_of_dvd_pow hu2),
      (mem_maximalIdeal_iff_dvd hπ v).2 hvd⟩
  obtain ⟨V, hV⟩ := hvunit
  refine ⟨-(u * (↑V⁻¹ : O)), ?_⟩
  have hw : (↑V⁻¹ : O) * v = 1 := by rw [← hV]; exact V.inv_mul
  have hkey : (-(u * (↑V⁻¹ : O))) ^ 2 + b₁ * (-(u * (↑V⁻¹ : O))) + b₀
      = (↑V⁻¹ : O) ^ 2 * (u ^ 2 - b₁ * u * v + b₀ * v ^ 2) := by
    linear_combination (b₁ * u * (↑V⁻¹ : O) - b₀ * (v * (↑V⁻¹ : O) + 1)) * hw
  rw [hkey]
  exact huv'.mul_left _

/-- The last step before a predicate first fails (no monotonicity needed). -/
theorem exists_max_step {Q : ℕ → Prop} (hQ0 : Q 0) : ∀ N : ℕ, ¬ Q N →
    ∃ t, t < N ∧ Q t ∧ ¬ Q (t + 1) := by
  intro N
  induction N with
  | zero => exact fun hN => absurd hQ0 hN
  | succ n ih =>
    intro hN
    by_cases hn : Q n
    · exact ⟨n, by omega, hn, hN⟩
    · obtain ⟨t, ht1, ht2, ht3⟩ := ih hn
      exact ⟨t, by omega, ht2, ht3⟩

/-- **THE DICHOTOMY.** If no centre has tangency depth `N`, one of the three window-`N`
certificates holds. -/
theorem cert_of_not_tang (hπ : Irreducible π) (a : Fin 2 → O) (N : ℕ)
    (hN : ¬ ∃ γ, Tang π a N γ) :
    CertSplit π a N ∨ CertRam π a N ∨ CertInert π a N := by
  obtain ⟨t, htlt, hPt, hmax⟩ :=
    exists_max_step (Q := fun t => ∃ γ, Tang π a t γ) ⟨0, Tang_zero π a 0⟩ N hN
  obtain ⟨γ, hval, hder⟩ := hPt
  by_cases hnext : π ^ (t + 1) ∣ qval a γ
  · -- the value goes deeper, so the DERIVATIVE must be what blocks depth `t + 1`
    have hderfail : ¬ π ^ ((t + 1 + 1) / 2) ∣ qder a γ := fun hcon => hmax ⟨γ, hnext, hcon⟩
    rcases Nat.even_or_odd t with ⟨k, hk⟩ | ⟨j, hj⟩
    · -- `t = 2k`, derivative valuation exactly `k`: a Newton root, SPLIT
      left
      refine ⟨γ, k, by omega, ?_, ?_, ?_⟩
      · rw [show k = (t + 1) / 2 by omega]; exact hder
      · rw [show k + 1 = (t + 1 + 1) / 2 by omega]; exact hderfail
      · rw [show 2 * k + 1 = t + 1 by omega]; exact hnext
    · -- `t` odd: `⌈(t+1)/2⌉ = ⌈t/2⌉`, so the derivative cannot be what blocks — impossible
      exact absurd (by rw [show (t + 1 + 1) / 2 = (t + 1) / 2 by omega]; exact hder) hderfail
  · -- the value has EXACT valuation `t`
    rcases Nat.even_or_odd t with ⟨k, hk⟩ | ⟨j, hj⟩
    · -- `t = 2k` even: read the residual quadratic
      have hderk : π ^ k ∣ qder a γ := by rw [show k = (t + 1) / 2 by omega]; exact hder
      have hvalk : π ^ (2 * k) ∣ qval a γ := by rw [show 2 * k = t by omega]; exact hval
      have hvalk' : ¬ π ^ (2 * k + 1) ∣ qval a γ := by
        rw [show 2 * k + 1 = t + 1 by omega]; exact hnext
      obtain ⟨b₀, hb₀⟩ := hvalk
      obtain ⟨b₁, hb₁⟩ := hderk
      by_cases haniso : Anisotropic ![b₀, b₁]
      · exact Or.inr (Or.inr ⟨γ, k, b₀, b₁, by omega, hb₀, hb₁, haniso⟩)
      · -- a residual root: recentre at `γ + π^k z`
        obtain ⟨z, hz⟩ := exists_residual_root hπ haniso
        have hval' : π ^ (2 * k + 1) ∣ qval a (γ + π ^ k * z) := by
          rw [qval_shift, hb₀, hb₁]
          obtain ⟨c, hc⟩ := hz
          exact ⟨c, by linear_combination (π ^ (2 * k)) * hc⟩
        have hder' : qder a (γ + π ^ k * z) = π ^ k * (b₁ + 2 * z) := by
          rw [qder_shift, hb₁]; ring
        by_cases hdd : π ∣ (b₁ + 2 * z)
        · -- residual DOUBLE root: depth `t + 1` is reached, contradicting maximality
          refine absurd ⟨γ + π ^ k * z, ?_, ?_⟩ hmax
          · rw [show t + 1 = 2 * k + 1 by omega]; exact hval'
          · rw [show (t + 1 + 1) / 2 = k + 1 by omega, hder']
            obtain ⟨c, hc⟩ := hdd
            exact ⟨c, by rw [hc]; ring⟩
        · -- residual SIMPLE root: a Newton root at the new centre, SPLIT
          refine Or.inl ⟨γ + π ^ k * z, k, by omega, ⟨b₁ + 2 * z, hder'⟩, ?_, hval'⟩
          rintro ⟨c, hc⟩
          refine hdd ⟨c, ?_⟩
          refine mul_left_cancel₀ (pow_ne_zero k hπ.ne_zero) ?_
          rw [← hder', hc]; ring
    · -- `t = 2j+1` odd and exact: RAM
      refine Or.inr (Or.inl ⟨γ, j, by omega, ?_, ?_, ?_⟩)
      · rw [show 2 * j + 1 = t by omega]; exact hval
      · rw [show 2 * j + 2 = t + 1 by omega]; exact hnext
      · rw [show j + 1 = (t + 1) / 2 by omega]; exact hder

end Dichotomy

/-! ## 6. Decidedness below the tangency depth -/

section Decided

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)] {π : O}

theorem mem_maximalIdeal_pow_iff_dvd (hπ : Irreducible π) (N : ℕ) (x : O) :
    x ∈ (IsLocalRing.maximalIdeal O) ^ N ↔ π ^ N ∣ x := by
  rw [hπ.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton]

theorem congAt_of_proj_eq (hπ : Irreducible π) {N : ℕ} {a b : Fin 2 → O}
    (h : proj O 2 N a = proj O 2 N b) : CongAt π N a b := by
  intro i
  have hi := congrFun h i
  rw [proj, proj, Ideal.Quotient.eq] at hi
  exact dvd_sub_comm.1 ((mem_maximalIdeal_pow_iff_dvd hπ N _).1 hi)

variable [IsAdicComplete (IsLocalRing.maximalIdeal O) O]

/-- **THE DECIDEDNESS THEOREM.** If no centre reaches tangency depth `N`, the level-`N` class of
`a` is `σ`-decided for `σ = typeOf (monicPoly a)`: the certificate produced by the dichotomy
reads only data strictly inside the window, so every other lift of the class carries the same
certificate and therefore the same type. -/
theorem decidedAt_of_not_tang (hπ : Irreducible π) {a : Fin 2 → O} {N : ℕ}
    (hN : ¬ ∃ γ, Tang π a N γ) :
    DecidedAt O 2 (typeOf (monicPoly a)) N (proj O 2 N a) := by
  intro b hb
  have hab : CongAt π N a b := congAt_of_proj_eq hπ hb.symm
  rcases cert_of_not_tang hπ a N hN with h | h | h
  · rw [typeOf_of_certSplit hπ (CertSplit_congr hab h), typeOf_of_certSplit hπ h]
  · rw [typeOf_of_certRam hπ (CertRam_congr hab h), typeOf_of_certRam hπ h]
  · rw [typeOf_of_certInert hπ (CertInert_congr hπ hab h), typeOf_of_certInert hπ h]

end Decided

/-! ## 7. The undecided set, and the general gap bound

`gapSeq σ N ≤ undecidedSeq N` for EVERY `n` and `σ`: a class that is `σ`-possible but not
`σ`-decided cannot be decided for any other type either (it has a lift of type `σ`). So one
bound on the undecided mass drains every type at once. -/

section Undecided

variable (O : Type*) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)]

/-- A class is **UNDECIDED** at level `N` when no type at all is decided on it. -/
def UndecidedAt (n N : ℕ) (c : Coeff O n N) : Prop :=
  ∀ σ : FactorizationType, ¬ DecidedAt O n σ N c

/-- The set of undecided level-`N` classes. -/
def undecidedSet (n N : ℕ) : Set (Coeff O n N) := {c | UndecidedAt O n N c}

/-- `#{undecided level-N classes}`. -/
noncomputable def undecidedCount (n N : ℕ) : ℕ := Nat.card (undecidedSet O n N)

/-- The undecided proportion at level `N`. -/
noncomputable def undecidedSeq (n N : ℕ) : ℝ :=
  (undecidedCount O n N : ℝ) / (residueCard O : ℝ) ^ (n * N)

variable {O}

theorem possibleSet_subset_union (n N : ℕ) (σ : FactorizationType) :
    possibleSet O n σ N ⊆ decidedSet O n σ N ∪ undecidedSet O n N := by
  intro c hc
  by_cases hd : DecidedAt O n σ N c
  · exact Or.inl hd
  · refine Or.inr (fun τ hτ => hd ?_)
    obtain ⟨a, ha, hta⟩ := hc
    have hστ : τ = σ := by rw [← hτ a ha, hta]
    exact hστ ▸ hτ

theorem possibleCount_le_add (n N : ℕ) (σ : FactorizationType) :
    possibleCount O n σ N ≤ decidedCount O n σ N + undecidedCount O n N := by
  classical
  have h1 : possibleCount O n σ N
      ≤ Nat.card ((decidedSet O n σ N ∪ undecidedSet O n N : Set (Coeff O n N))) :=
    Nat.card_le_card_of_injective (Set.inclusion (possibleSet_subset_union n N σ))
      (Set.inclusion_injective _)
  have h2 : Nat.card ((decidedSet O n σ N ∪ undecidedSet O n N : Set (Coeff O n N)))
      ≤ decidedCount O n σ N + undecidedCount O n N := by
    rw [Nat.card_coe_set_eq, decidedCount, undecidedCount, Nat.card_coe_set_eq,
      Nat.card_coe_set_eq]
    exact Set.ncard_union_le _ _
  exact h1.trans h2

/-- **One bound drains every type.** -/
theorem gapSeq_le_undecidedSeq (n N : ℕ) (σ : FactorizationType) :
    gapSeq O n σ N ≤ undecidedSeq O n N := by
  have h := possibleCount_le_add (O := O) n N σ
  have hq : (0 : ℝ) < (residueCard O : ℝ) ^ (n * N) := qpow_pos _
  have hcast : (possibleCount O n σ N : ℝ) ≤ (decidedCount O n σ N : ℝ) + undecidedCount O n N := by
    exact_mod_cast h
  rw [gapSeq, possibleSeq, decidedSeq, undecidedSeq, div_sub_div_same, div_le_div_iff₀ hq hq]
  nlinarith [hcast, hq]

end Undecided

/-! ## 8. Counting the undecided classes: `q ^ (3M)` out of `q ^ (4M)` at level `2M` -/

section Counting

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)] [IsAdicComplete (IsLocalRing.maximalIdeal O) O] {π : O}

/-- **The class is pinned by `(γ mod π^M, a₁ mod π^{2M})`.** Two deeply-tangent data with the
same centre mod `π ^ M` and the same `a₁` mod `π ^ {2M}` have the same `a₀` mod `π ^ {2M}` —
because moving the centre by `π ^ M s` moves the value by `π ^ M s F'(γ) + π^{2M}s² ∈ π^{2M}`. -/
theorem class_pinned {M : ℕ} {a a' : Fin 2 → O} {γ γ' : O}
    (hT : Tang π a (2 * M) γ) (hT' : Tang π a' (2 * M) γ')
    (hγ : π ^ M ∣ (γ' - γ)) (h1 : π ^ (2 * M) ∣ (a' 1 - a 1)) :
    π ^ (2 * M) ∣ (a' 0 - a 0) := by
  obtain ⟨s, hs⟩ := hγ
  obtain ⟨d, hd⟩ := h1
  obtain ⟨e, he⟩ := hT.1
  obtain ⟨e', he'⟩ := hT'.1
  obtain ⟨g, hg⟩ := (show π ^ M ∣ qder a γ by
    have := hT.2; rwa [show (2 * M + 1) / 2 = M by omega] at this)
  simp only [qval] at he he'
  simp only [qder] at hg
  have hs' : γ' = γ + π ^ M * s := by linear_combination hs
  have hd' : a' 1 = a 1 + π ^ (2 * M) * d := by linear_combination hd
  rw [hs', hd'] at he'
  exact ⟨e' - e - s * g - s ^ 2 - d * γ - π ^ M * d * s,
    by linear_combination he' - he - (π ^ M * s) * hg⟩

/-- **THE UNDECIDED BOUND.** At level `2M` at most `q ^ (3M)` of the `q ^ (4M)` classes are
undecided. -/
theorem undecidedCount_le (hπ : Irreducible π) (M : ℕ) :
    undecidedCount O 2 (2 * M) ≤ residueCard O ^ (3 * M) := by
  classical
  have key : ∀ c : undecidedSet O 2 (2 * M), ∃ p : (Fin 2 → O) × O,
      proj O 2 (2 * M) p.1 = (c : Coeff O 2 (2 * M)) ∧ Tang π p.1 (2 * M) p.2 := by
    rintro ⟨c, hc⟩
    obtain ⟨a, ha⟩ := proj_surjective O 2 (2 * M) c
    by_cases hT : ∃ γ, Tang π a (2 * M) γ
    · obtain ⟨γ, hγ⟩ := hT
      exact ⟨(a, γ), ha, hγ⟩
    · exact absurd (ha ▸ decidedAt_of_not_tang hπ hT) (hc _)
  choose f hf1 hf2 using key
  have hinj : Function.Injective (fun c : undecidedSet O 2 (2 * M) =>
      ((Ideal.Quotient.mk ((IsLocalRing.maximalIdeal O) ^ M) (f c).2,
        (c : Coeff O 2 (2 * M)) 1) : Res O M × Res O (2 * M))) := by
    intro c c' hcc
    have h1 : Ideal.Quotient.mk ((IsLocalRing.maximalIdeal O) ^ M) (f c).2
        = Ideal.Quotient.mk _ (f c').2 := congrArg Prod.fst hcc
    have h2 : (c : Coeff O 2 (2 * M)) 1 = (c' : Coeff O 2 (2 * M)) 1 := congrArg Prod.snd hcc
    have hγ : π ^ M ∣ ((f c').2 - (f c).2) :=
      (mem_maximalIdeal_pow_iff_dvd hπ M _).1 (Ideal.Quotient.eq.1 h1.symm)
    have e1 : (c : Coeff O 2 (2 * M)) 1 = Ideal.Quotient.mk _ ((f c).1 1) := by rw [← hf1 c]; rfl
    have e2 : (c' : Coeff O 2 (2 * M)) 1 = Ideal.Quotient.mk _ ((f c').1 1) := by rw [← hf1 c']; rfl
    have ha1 : π ^ (2 * M) ∣ ((f c').1 1 - (f c).1 1) :=
      (mem_maximalIdeal_pow_iff_dvd hπ (2 * M) _).1 (Ideal.Quotient.eq.1 (by rw [← e1, ← e2, h2]))
    have ha0 : π ^ (2 * M) ∣ ((f c').1 0 - (f c).1 0) := class_pinned (hf2 c) (hf2 c') hγ ha1
    refine Subtype.ext (funext fun i => ?_)
    fin_cases i
    · show (c : Coeff O 2 (2 * M)) 0 = (c' : Coeff O 2 (2 * M)) 0
      rw [← hf1 c, ← hf1 c']
      exact Ideal.Quotient.eq.2
        ((mem_maximalIdeal_pow_iff_dvd hπ (2 * M) _).2 (dvd_sub_comm.1 ha0))
    · exact h2
  have hle := Nat.card_le_card_of_injective _ hinj
  rw [Nat.card_prod, card_res, card_res] at hle
  calc undecidedCount O 2 (2 * M) ≤ residueCard O ^ M * residueCard O ^ (2 * M) := hle
    _ = residueCard O ^ (3 * M) := by rw [← pow_add]; ring_nf

/-- The undecided proportion at level `2M` is at most `q ^ (-M)`. -/
theorem undecidedSeq_le (hπ : Irreducible π) (M : ℕ) :
    undecidedSeq O 2 (2 * M) ≤ (1 / (residueCard O : ℝ)) ^ M := by
  have hcount : (undecidedCount O 2 (2 * M) : ℝ) ≤ (residueCard O : ℝ) ^ (3 * M) := by
    exact_mod_cast undecidedCount_le hπ M
  have hq : (0 : ℝ) < (residueCard O : ℝ) := qR_pos
  rw [undecidedSeq, div_pow, one_pow, show 2 * (2 * M) = 4 * M from by ring,
    div_le_div_iff₀ (by positivity) (by positivity)]
  calc (undecidedCount O 2 (2 * M) : ℝ) * (residueCard O : ℝ) ^ M
      ≤ (residueCard O : ℝ) ^ (3 * M) * (residueCard O : ℝ) ^ M := by
        exact mul_le_mul_of_nonneg_right hcount (by positivity)
    _ = 1 * (residueCard O : ℝ) ^ (4 * M) := by rw [one_mul, ← pow_add]; ring_nf

end Counting

/-! ## 9. THE DRAINAGE THEOREM, and the exact `n = 2` identity it unlocks -/

section Drainage

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)] [IsAdicComplete (IsLocalRing.maximalIdeal O) O]

theorem tendsto_two_mul_atTop : Tendsto (fun M : ℕ => 2 * M) atTop atTop :=
  Filter.tendsto_atTop_atTop.2 (fun b => ⟨b, fun a ha => by omega⟩)

theorem undecidedSeq_tendsto_zero :
    Tendsto (fun M : ℕ => undecidedSeq O 2 (2 * M)) atTop (𝓝 0) := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible O
  refine squeeze_zero (fun M => ?_) (fun M => undecidedSeq_le hπ M) ?_
  · exact div_nonneg (Nat.cast_nonneg _) (le_of_lt (qpow_pos _))
  · refine tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity) ?_
    rw [div_lt_one qR_pos]
    exact_mod_cast one_lt_residueCard O

theorem gapSeq_antitone (σ : FactorizationType) : Antitone (gapSeq O 2 σ) := by
  intro N M h
  simp only [gapSeq]
  have h1 := possibleSeq_antitone (O := O) 2 σ h
  have h2 := decidedSeq_mono (O := O) 2 σ h
  linarith

/-- **THE `n = 2` DRAINAGE THEOREM.** For every complete DVR `O` with finite residue field and
every splitting type `σ`, the level-`N` ambiguity gap of monic quadratics drains to `0`. -/
theorem drainage_two (σ : FactorizationType) : UndecidedVanishes O 2 σ := by
  have hbdd : BddBelow (Set.range (gapSeq O 2 σ)) := by
    refine ⟨0, ?_⟩
    rintro x ⟨N, rfl⟩
    exact gapSeq_nonneg 2 σ N
  have hlim : Tendsto (gapSeq O 2 σ) atTop (𝓝 (⨅ N, gapSeq O 2 σ N)) :=
    tendsto_atTop_ciInf (gapSeq_antitone σ) hbdd
  have hsub : Tendsto (fun M : ℕ => gapSeq O 2 σ (2 * M)) atTop (𝓝 (⨅ N, gapSeq O 2 σ N)) :=
    hlim.comp tendsto_two_mul_atTop
  have hzero : Tendsto (fun M : ℕ => gapSeq O 2 σ (2 * M)) atTop (𝓝 0) :=
    squeeze_zero (fun M => gapSeq_nonneg 2 σ (2 * M))
      (fun M => gapSeq_le_undecidedSeq 2 (2 * M) σ) undecidedSeq_tendsto_zero
  have hL : (⨅ N, gapSeq O 2 σ N) = 0 := tendsto_nhds_unique hsub hzero
  rw [UndecidedVanishes, ← hL]
  exact hlim

/-- **THE `n = 2` TIE — the bracket closes.** THE density (the limit of the proportion of
classes consistent with `σ`) equals the certified one (the limit of the proportion on which `σ`
is forced), unconditionally, for every complete DVR with finite residue field and every type.
Every `_decided` gate of `Gates.lean` transfers through this equation; §9 does exactly that. -/
theorem genuineDensity_eq_decidedDensity_two (σ : FactorizationType) :
    genuineDensity O 2 σ = decidedDensity O 2 σ :=
  genuineDensity_eq_of_drainage (drainage_two σ)

/-! ### The exact identity: the three degree-2 types carry ALL the mass -/

/-- A monic quadratic has one of exactly three types: `e·f = 2` leaves only `(1,1)+(1,1)`,
`(1,2)` and `(2,1)`. -/
theorem typeOf_two_cases (a : Fin 2 → O) :
    typeOf (monicPoly a) = splitType ∨ typeOf (monicPoly a) = inertType
      ∨ typeOf (monicPoly a) = ramType := by
  by_cases hirr : Irreducible (monicPoly a)
  · right
    have hF : IsMonicFactorization (monicPoly a) {monicPoly a} :=
      ⟨by intro g hg; rw [Multiset.mem_singleton.1 hg]; exact ⟨monicPoly_monic a, hirr⟩, by simp⟩
    have hd2 : (monicPoly a).natDegree = 2 := monicPoly_natDegree a
    have hdvd : inertiaDegOf (monicPoly a) ∣ 2 := by
      have := inertiaDegOf_dvd_natDegree (monicPoly_monic a) (by rw [hd2]; omega)
      rwa [hd2] at this
    have hpos : 0 < inertiaDegOf (monicPoly a) :=
      inertiaDegOf_pos (normValues_nonempty (monicPoly_monic a) (by rw [hd2]; omega))
    have hmul : ramIndexOf (monicPoly a) * inertiaDegOf (monicPoly a) = 2 := by
      have := ramIndexOf_mul_inertiaDegOf (monicPoly_monic a) (by rw [hd2]; omega)
      rwa [hd2] at this
    rcases (Nat.dvd_prime Nat.prime_two).1 hdvd with h1 | h1
    · right
      have he : ramIndexOf (monicPoly a) = 2 := by rw [h1, mul_one] at hmul; exact hmul
      ext
      rw [typeOf_data, monicFactors_eq hF]
      simp [ramType, efPair, he, h1]
    · left
      have he : ramIndexOf (monicPoly a) = 1 := by rw [h1] at hmul; omega
      ext
      rw [typeOf_data, monicFactors_eq hF]
      simp [inertType, efPair, he, h1]
  · left
    obtain ⟨r, s, h1, h0⟩ := exists_roots_of_not_irreducible hirr
    refine typeOf_split_of_root (R := r) ?_
    simp only [qval, h1, h0]; ring

/-- The four sets — decided split, decided inert, decided ram, undecided — cover everything. -/
theorem coeff_subset_union (N : ℕ) :
    (Set.univ : Set (Coeff O 2 N)) ⊆
      decidedSet O 2 splitType N ∪ decidedSet O 2 inertType N ∪ decidedSet O 2 ramType N
        ∪ undecidedSet O 2 N := by
  intro c _
  by_cases hu : UndecidedAt O 2 N c
  · exact Or.inr hu
  · rw [UndecidedAt] at hu
    push_neg at hu
    obtain ⟨σ, hσ⟩ := hu
    obtain ⟨a, ha⟩ := proj_surjective O 2 N c
    have hty : typeOf (monicPoly a) = σ := hσ a ha
    rcases typeOf_two_cases a with h | h | h <;> rw [h] at hty
    · exact Or.inl (Or.inl (Or.inl (hty ▸ hσ)))
    · exact Or.inl (Or.inl (Or.inr (hty ▸ hσ)))
    · exact Or.inl (Or.inr (hty ▸ hσ))

theorem card_le_sum_counts (N : ℕ) :
    residueCard O ^ (2 * N) ≤ decidedCount O 2 splitType N + decidedCount O 2 inertType N
      + decidedCount O 2 ramType N + undecidedCount O 2 N := by
  classical
  have hcov := coeff_subset_union (O := O) N
  have h1 : residueCard O ^ (2 * N) = (Set.univ : Set (Coeff O 2 N)).ncard := by
    rw [Set.ncard_univ, ← card_coeff (O := O) 2 N]
  rw [h1]
  calc (Set.univ : Set (Coeff O 2 N)).ncard
      ≤ (decidedSet O 2 splitType N ∪ decidedSet O 2 inertType N ∪ decidedSet O 2 ramType N
          ∪ undecidedSet O 2 N).ncard := Set.ncard_le_ncard hcov (Set.toFinite _)
    _ ≤ (decidedSet O 2 splitType N ∪ decidedSet O 2 inertType N
          ∪ decidedSet O 2 ramType N).ncard + (undecidedSet O 2 N).ncard :=
        Set.ncard_union_le _ _
    _ ≤ ((decidedSet O 2 splitType N ∪ decidedSet O 2 inertType N).ncard
          + (decidedSet O 2 ramType N).ncard) + (undecidedSet O 2 N).ncard := by
        gcongr; exact Set.ncard_union_le _ _
    _ ≤ (((decidedSet O 2 splitType N).ncard + (decidedSet O 2 inertType N).ncard)
          + (decidedSet O 2 ramType N).ncard) + (undecidedSet O 2 N).ncard := by
        gcongr; exact Set.ncard_union_le _ _
    _ = decidedCount O 2 splitType N + decidedCount O 2 inertType N
          + decidedCount O 2 ramType N + undecidedCount O 2 N := by
        rw [decidedCount, decidedCount, decidedCount, undecidedCount, Nat.card_coe_set_eq,
          Nat.card_coe_set_eq, Nat.card_coe_set_eq, Nat.card_coe_set_eq]

theorem one_le_sum_seqs (N : ℕ) :
    1 ≤ decidedSeq O 2 splitType N + decidedSeq O 2 inertType N + decidedSeq O 2 ramType N
      + undecidedSeq O 2 N := by
  have h := card_le_sum_counts (O := O) N
  have hq : (0 : ℝ) < (residueCard O : ℝ) ^ (2 * N) := qpow_pos _
  have hcast : ((residueCard O : ℝ)) ^ (2 * N)
      ≤ (decidedCount O 2 splitType N : ℝ) + (decidedCount O 2 inertType N : ℝ)
        + (decidedCount O 2 ramType N : ℝ) + (undecidedCount O 2 N : ℝ) := by
    exact_mod_cast h
  rw [decidedSeq, decidedSeq, decidedSeq, undecidedSeq, ← add_div, ← add_div, ← add_div,
    le_div_iff₀ hq, one_mul]
  exact hcast

/-- **THE EXACT `n = 2` IDENTITY.** The three degree-2 splitting types carry all the mass:

    decidedDensity O 2 split + decidedDensity O 2 inert + decidedDensity O 2 ram = 1

for EVERY complete DVR `O` with finite residue field (wild residue characteristic included).
This is W-11 clause (iii)'s exhaustiveness `Σ = 1`, proved here about the Part-1 density
itself. `≤` is the general total-mass bound; `≥` is drainage — without it the decided
proportions could leave mass behind forever. -/
theorem sum_three_decidedDensities_eq_one :
    decidedDensity O 2 splitType + decidedDensity O 2 inertType + decidedDensity O 2 ramType
      = 1 := by
  classical
  refine le_antisymm ?_ ?_
  · have hsum : ∑ τ ∈ ({splitType, inertType, ramType} : Finset FactorizationType),
        decidedDensity O 2 τ ≤ 1 := sum_decidedDensity_le_one 2 _
    rw [Finset.sum_insert (by simp [splitType_ne_inertType, splitType_ne_ramType]),
      Finset.sum_insert (by simp [inertType_ne_ramType]), Finset.sum_singleton] at hsum
    linarith
  · -- pass to the limit along the even levels, where the undecided mass is bounded by `q^{-M}`
    have hlim : Tendsto (fun M : ℕ =>
        decidedSeq O 2 splitType (2 * M) + decidedSeq O 2 inertType (2 * M)
          + decidedSeq O 2 ramType (2 * M) + undecidedSeq O 2 (2 * M)) atTop
        (𝓝 (decidedDensity O 2 splitType + decidedDensity O 2 inertType
          + decidedDensity O 2 ramType + 0)) := by
      refine Tendsto.add (Tendsto.add (Tendsto.add ?_ ?_) ?_) undecidedSeq_tendsto_zero
      · exact (decidedSeq_tendsto 2 splitType).comp tendsto_two_mul_atTop
      · exact (decidedSeq_tendsto 2 inertType).comp tendsto_two_mul_atTop
      · exact (decidedSeq_tendsto 2 ramType).comp tendsto_two_mul_atTop
    rw [add_zero] at hlim
    exact ge_of_tendsto hlim (Eventually.of_forall (fun M => one_le_sum_seqs (2 * M)))

/-- **Every other type has density exactly `0` at `n = 2`.** Together with G11 this pins the
whole degree-2 density function except for the split between the three surviving types: the
menu is `{split, inert, ram}` and nothing else carries mass. (Generalises
`decidedDensity_two_linType_eq_zero`, which is the case `σ = {(1,1)}`.) -/
theorem decidedDensity_two_eq_zero {σ : FactorizationType} (hs : σ ≠ splitType)
    (hi : σ ≠ inertType) (hr : σ ≠ ramType) : decidedDensity O 2 σ = 0 := by
  have hempty : ∀ N, decidedSet O 2 σ N = ∅ := by
    intro N
    ext c
    simp only [Set.mem_empty_iff_false, iff_false]
    intro hc
    obtain ⟨a, ha⟩ := proj_surjective O 2 N c
    have hty : typeOf (monicPoly a) = σ := hc a ha
    rcases typeOf_two_cases a with h | h | h <;> rw [h] at hty
    · exact hs hty.symm
    · exact hi hty.symm
    · exact hr hty.symm
  have hzero : ∀ N, decidedSeq O 2 σ N = 0 := by
    intro N
    rw [decidedSeq, decidedCount, hempty N]
    simp
  rw [decidedDensity]
  simp [hzero]

end Drainage

/-! ## 9. THE HEADLINE `n = 2` STATEMENTS, over THE density `genuineDensity`

Everything in `Gates.lean` and in §8 above is stated over the CERTIFIED density
`decidedDensity` — `Gates.lean` has no access to `drainage_two`, and §8 builds towards it. This
section re-keys the whole `n = 2` picture to THE density (the limit of the proportion of
coefficient classes consistent with `σ`), which `genuineDensity_eq_decidedDensity_two` licenses
**unconditionally**: at `n = 2` the two limits are equal, for every complete DVR with finite
residue field, wild residue characteristic included.

Naming convention established by the 2026-08-13 rewire: the unsuffixed name always carries the
statement about THE density; the `_decided` suffix marks the certified-density version that the
proof actually goes through. The *numbers* are identical — only the object they describe
changes, from "mass certified at some finite level" to "mass of the locus".
-/

section HeadlineTwo

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)] [IsAdicComplete (IsLocalRing.maximalIdeal O) O]

/-- **G4 re-keyed.** The degree-1 type has THE density exactly `0` among monic quadratics. -/
theorem genuineDensity_two_linType_eq_zero : genuineDensity O 2 linType = 0 := by
  rw [genuineDensity_eq_decidedDensity_two, decidedDensity_two_linType_eq_zero]

/-- **Every other type has THE density exactly `0` at `n = 2`.** The menu is
`{split, inert, ram}` and nothing else carries mass. -/
theorem genuineDensity_two_eq_zero {σ : FactorizationType} (hs : σ ≠ splitType)
    (hi : σ ≠ inertType) (hr : σ ≠ ramType) : genuineDensity O 2 σ = 0 := by
  rw [genuineDensity_eq_decidedDensity_two, decidedDensity_two_eq_zero hs hi hr]

/-- **G3 re-keyed.** `1 / q² ≤ genuineDensity O 2 splitType`, every `O`. -/
theorem gate_split_lower : 1 / (residueCard O : ℝ) ^ 2 ≤ genuineDensity O 2 splitType := by
  rw [genuineDensity_eq_decidedDensity_two]; exact gate_split_lower_decided

/-- **G3-sharp re-keyed.** `(q-1) / q² ≤ genuineDensity O 2 splitType`, every `O`. -/
theorem gate_split_lower_sharp :
    ((residueCard O : ℝ) - 1) / (residueCard O : ℝ) ^ 2 ≤ genuineDensity O 2 splitType := by
  rw [genuineDensity_eq_decidedDensity_two]; exact gate_split_lower_sharp_decided

/-- **G5 re-keyed.** `1 / q⁴ ≤ genuineDensity O 2 ramType`, every `O`. -/
theorem gate_ram_lower : 1 / (residueCard O : ℝ) ^ 4 ≤ genuineDensity O 2 ramType := by
  rw [genuineDensity_eq_decidedDensity_two]; exact gate_ram_lower_decided

/-- **G4 σ-separation re-keyed**, over THE density. -/
theorem gate_sigma_separation_two :
    genuineDensity O 2 linType < genuineDensity O 2 splitType := by
  rw [genuineDensity_eq_decidedDensity_two, genuineDensity_eq_decidedDensity_two]
  exact gate_sigma_separation_two_decided

/-- **The bracket engine re-keyed.** Lower bounds on the three degree-2 types turn into upper
bounds on each one, now for THE density. -/
theorem bracket_two {ls li lr : ℝ}
    (hs : ls ≤ genuineDensity O 2 splitType)
    (hi : li ≤ genuineDensity O 2 inertType)
    (hr : lr ≤ genuineDensity O 2 ramType) :
    (ls ≤ genuineDensity O 2 splitType ∧ genuineDensity O 2 splitType ≤ 1 - li - lr)
    ∧ (li ≤ genuineDensity O 2 inertType ∧ genuineDensity O 2 inertType ≤ 1 - ls - lr)
    ∧ (lr ≤ genuineDensity O 2 ramType ∧ genuineDensity O 2 ramType ≤ 1 - ls - li) := by
  simp only [genuineDensity_eq_decidedDensity_two] at hs hi hr ⊢
  exact bracket_two_decided hs hi hr

/-- **THE EXACT `n = 2` IDENTITY, over THE density.** The three degree-2 splitting types carry
all the mass:

    genuineDensity O 2 split + genuineDensity O 2 inert + genuineDensity O 2 ram = 1

for EVERY complete DVR `O` with finite residue field. This is Asvin's `Σ_σ R_σ = 1` at `n = 2`,
over the density defined as the limit of the consistent-class proportions. `≥` is free
(`one_le_sum_genuineDensity`: the possible sets cover); `≤` is drainage. -/
theorem sum_three_densities_eq_one :
    genuineDensity O 2 splitType + genuineDensity O 2 inertType + genuineDensity O 2 ramType
      = 1 := by
  simp only [genuineDensity_eq_decidedDensity_two]
  exact sum_three_decidedDensities_eq_one

/-- `{split, inert, ram}` is a covering menu at degree 2 (`typeOf_two_cases`). -/
theorem coveringMenu_two :
    CoveringMenu O 2 ({splitType, inertType, ramType} : Finset FactorizationType) := by
  intro a
  rcases typeOf_two_cases a with h | h | h <;> simp [h]

/-- **`Σ_σ R_σ = 1` at `n = 2` for ANY covering menu** — the `n = 2` instance of the named
general-`n` target `TotalMassOne` (`Statement.lean`), proved unconditionally because
`drainage_two` is a theorem. -/
theorem totalMass_two (S : Finset FactorizationType) (hS : CoveringMenu O 2 S) :
    ∑ σ ∈ S, genuineDensity O 2 σ = 1 :=
  sum_genuineDensity_eq_one_of_drainage hS (fun σ _ => drainage_two σ)

/-- **The `n = 2` picture, packaged, over THE density.** The three types carry mass summing to
exactly `1`, every other type has density exactly `0`, and for each type THE density coincides
with the certified one (the bracket is closed). The individual values are not here: they are
proved in the companion `leancheck` repo (`N2Exact`). -/
theorem density_two_summary :
    (genuineDensity O 2 splitType + genuineDensity O 2 inertType + genuineDensity O 2 ramType
      = 1)
    ∧ (∀ σ : FactorizationType, σ ≠ splitType → σ ≠ inertType → σ ≠ ramType →
        genuineDensity O 2 σ = 0)
    ∧ (∀ σ : FactorizationType, genuineDensity O 2 σ = decidedDensity O 2 σ) :=
  ⟨sum_three_densities_eq_one, fun _ hs hi hr => genuineDensity_two_eq_zero hs hi hr,
    genuineDensity_eq_decidedDensity_two⟩

end HeadlineTwo

section HeadlinePadic

/-- **G3 at `ℤ_[2]` re-keyed.** -/
theorem gate_padic_two : 1 / (2 : ℝ) ^ 2 ≤ genuineDensity ℤ_[2] 2 splitType := by
  rw [genuineDensity_eq_decidedDensity_two]; exact gate_padic_two_decided

/-- The three certified lower bounds at `q = 2`, re-keyed to THE density. -/
theorem lowers_padic_two :
    (1 : ℝ) / 4 ≤ genuineDensity ℤ_[2] 2 splitType
    ∧ (1 : ℝ) / 4 ≤ genuineDensity ℤ_[2] 2 inertType
    ∧ (1 : ℝ) / 16 ≤ genuineDensity ℤ_[2] 2 ramType := by
  simpa only [genuineDensity_eq_decidedDensity_two] using lowers_padic_two_decided

/-- The three certified lower bounds at `q = 3`, re-keyed to THE density. -/
theorem lowers_padic_three :
    (2 : ℝ) / 9 ≤ genuineDensity ℤ_[3] 2 splitType
    ∧ (1 : ℝ) / 9 ≤ genuineDensity ℤ_[3] 2 inertType
    ∧ (1 : ℝ) / 81 ≤ genuineDensity ℤ_[3] 2 ramType := by
  simpa only [genuineDensity_eq_decidedDensity_two] using lowers_padic_three_decided

/-- **GATE BRACKET, q = 2, over THE density.** W-11's exact values are
`split = inert = ram = 1/3`, all inside these brackets (`gate_bracket_w11_two`). -/
theorem gate_bracket_padic_two :
    ((1 : ℝ) / 4 ≤ genuineDensity ℤ_[2] 2 splitType
        ∧ genuineDensity ℤ_[2] 2 splitType ≤ 11 / 16)
    ∧ ((1 : ℝ) / 4 ≤ genuineDensity ℤ_[2] 2 inertType
        ∧ genuineDensity ℤ_[2] 2 inertType ≤ 11 / 16)
    ∧ ((1 : ℝ) / 16 ≤ genuineDensity ℤ_[2] 2 ramType
        ∧ genuineDensity ℤ_[2] 2 ramType ≤ 1 / 2) := by
  simpa only [genuineDensity_eq_decidedDensity_two] using gate_bracket_padic_two_decided

/-- **GATE BRACKET, q = 3, over THE density.** W-11's exact values are `split = inert = 3/8`,
`ram = 1/4` (`gate_bracket_w11_three`). -/
theorem gate_bracket_padic_three :
    ((2 : ℝ) / 9 ≤ genuineDensity ℤ_[3] 2 splitType
        ∧ genuineDensity ℤ_[3] 2 splitType ≤ 71 / 81)
    ∧ ((1 : ℝ) / 9 ≤ genuineDensity ℤ_[3] 2 inertType
        ∧ genuineDensity ℤ_[3] 2 inertType ≤ 62 / 81)
    ∧ ((1 : ℝ) / 81 ≤ genuineDensity ℤ_[3] 2 ramType
        ∧ genuineDensity ℤ_[3] 2 ramType ≤ 2 / 3) := by
  simpa only [genuineDensity_eq_decidedDensity_two] using gate_bracket_padic_three_decided

end HeadlinePadic

/-! ## 10. Axiom footprints -/

section AxCheck

#print axioms Uniformity.Density.typeOf_of_certSplit
#print axioms Uniformity.Density.typeOf_of_certRam
#print axioms Uniformity.Density.typeOf_of_certInert
#print axioms Uniformity.Density.cert_of_not_tang
#print axioms Uniformity.Density.decidedAt_of_not_tang
#print axioms Uniformity.Density.gapSeq_le_undecidedSeq
#print axioms Uniformity.Density.class_pinned
#print axioms Uniformity.Density.undecidedCount_le
#print axioms Uniformity.Density.drainage_two
#print axioms Uniformity.Density.genuineDensity_eq_decidedDensity_two
#print axioms Uniformity.Density.typeOf_two_cases
#print axioms Uniformity.Density.sum_three_decidedDensities_eq_one
#print axioms Uniformity.Density.decidedDensity_two_eq_zero
-- unit UNIFORMITY-P4 (2026-08-13): the `n = 2` headlines, over THE density
#print axioms Uniformity.Density.genuineDensity_two_linType_eq_zero
#print axioms Uniformity.Density.genuineDensity_two_eq_zero
#print axioms Uniformity.Density.gate_split_lower
#print axioms Uniformity.Density.gate_split_lower_sharp
#print axioms Uniformity.Density.gate_ram_lower
#print axioms Uniformity.Density.gate_sigma_separation_two
#print axioms Uniformity.Density.bracket_two
#print axioms Uniformity.Density.sum_three_densities_eq_one
#print axioms Uniformity.Density.coveringMenu_two
#print axioms Uniformity.Density.totalMass_two
#print axioms Uniformity.Density.density_two_summary
#print axioms Uniformity.Density.gate_padic_two
#print axioms Uniformity.Density.lowers_padic_two
#print axioms Uniformity.Density.lowers_padic_three
#print axioms Uniformity.Density.gate_bracket_padic_two
#print axioms Uniformity.Density.gate_bracket_padic_three

end AxCheck

end Uniformity.Density
