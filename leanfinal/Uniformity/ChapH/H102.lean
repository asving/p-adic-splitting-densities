/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapH.H101
import Uniformity.Density.Transport
import Uniformity.HenselFactorization

/-!
# Uniformity.ChapH.H102 — the Hensel class bijection, with NO precision loss (N-1a)

**Chapter H, NODE H.102** (`blueprint/CHAP-H_general_induction.md` §17.1, the dated extension of
2026-08-16, unit T-1 / provenance OM-2). The third node of **N-1, the level-0 class transport**.

Over coprime monic residue factors `g₁, g₂` of degrees `n₁, n₂`, class multiplication
(`mulClass`, H.101) is a **bijection**

  `levelZeroStratum g₁ × levelZeroStratum g₂  ≃  levelZeroStratum (g₁ * g₂)`,

and the stratum census therefore multiplies:

* `bijOn_mulClass : Set.BijOn (fun p => mulClass p.1 p.2) (stratum g₁ ×ˢ stratum g₂)
  (stratum (g₁ * g₂))`;
* `card_levelZeroStratum_mul : Nat.card (stratum (g₁ * g₂))
  = Nat.card (stratum g₁) * Nat.card (stratum g₂)`.

The `r`-factor form follows by peeling one factor at a time (the cofactor product stays coprime);
per the blueprint no separate node is opened for it — H.124's PROOF field performs the peel.

## The genuinely new step: NO precision loss

The content of the node is `Set.InjOn`, exported separately as **`eq_of_mulClass_eq`**: two
factorizations of the *same class mod `𝔪 ^ N`* agree mod `𝔪 ^ N` **factorwise** — not mod
`𝔪 ^ (N − C)` for some resultant-dependent loss `C`. The route taken here is the second of the
two the blueprint offers ("*the `monic_factorization_unique` argument replayed mod `𝔪 ^ N`*"),
executed as follows, entirely inside the truncation ring `R = Res O N`:

1. lift the two class-pairs to `a₁, a₂` and `b₁, b₂` over `O`;
2. over `O`, the **cross pair** `monicPoly a₁`, `monicPoly b₂` is coprime — landed
   `Hensel.isCoprime_of_map_eq` turns the residue-level `IsCoprime g₁ g₂` into an honest Bézout
   identity in `O[X]` (this is where `[IsAdicComplete]` and the level-0 resultant unit enter);
3. push that Bézout identity along `Polynomial.mapRingHom (Ideal.Quotient.mk (𝔪 ^ N))`, so the
   cross pair stays coprime **in `R[X]`**;
4. in `R[X]` the two products are *equal on the nose* (the class equality gives all coefficients
   below the top; monicity of both sides supplies the rest — `ext_of_monic_of_coeff_lt`);
5. `eq_of_mul_eq_mul_of_monic` — the pure-algebra core of the landed
   `Hensel.monic_factorization_unique`, restated over an arbitrary nontrivial `CommRing` with the
   coprimality of the cross pair as a *hypothesis* rather than a Hensel consequence — concludes
   `monicPoly c₁ = monicPoly c₁'` and `monicPoly c₂ = monicPoly c₂'`, hence `c₁ = c₁'`, `c₂ = c₂'`.

No level-by-level correction loop appears: there is nothing to correct, because the whole
argument already happens at the finite level `N`. The blueprint's instruction (*"a failed
transcription here must return the precise level at which correction fails, not weaken to
`𝔪^{N−C}`"*) is therefore vacuous for this route — the statement is proved at the frozen
precision `N`.

DEPENDS: H.100 (`levelZeroStratum`, `mem_levelZeroStratum_iff`, `proj_surjective'`,
`map_monicPoly`) · H.101 (`mulClass`, `mulClass_apply`, `mulClass_proj`) · landed
`Uniformity.Hensel.exists_monic_factorization`, `Hensel.isCoprime_of_map_eq`,
`Uniformity.Density.exists_monicPoly_eq`, `monicPoly_coeff_lt` · mathlib `Nat.card_prod`,
`Equiv.Set.prod`, `Set.BijOn.equiv`.

**Recorded route deviation (no statement change).** The blueprint's DEPENDS names the `Finset`
form `Hensel.exists_monic_factorization_finset` (HYP.03's discharger) and its "two-element index";
this file calls the *binary* `Hensel.exists_monic_factorization` (`HenselFactorization.lean:393`)
that the `Finset` form is itself built from by induction. Same theorem, one fewer
`Finset.induction` unfolding, identical axiom footprint.

**ENVIRONMENT — ENV-H17 + `[IsAdicComplete (maximalIdeal O) O]`** (blueprint §17.0): all binders
inline, no section variables, **no `Finite (ResidueField O)`**. Completeness is the intended
route's binder (blueprint: a completeness-free finite-level route exists — successive
approximation — and dropping the binder is a recorded strengthening OPTION, forced by no consumer,
since every §17 consumer is ENV-H3). It is genuinely used twice: `isCoprime_of_map_eq` (InjOn) and
`exists_monic_factorization` (SurjOn).

## Four exported auxiliaries (non-blueprint, declared rather than smuggled)

The landed `monicPoly_monic` / `monicPoly_natDegree` / `monicPoly_coeff_lt` all carry
`[IsDomain O]` (section-variable auto-inclusion in `Density/LocalData.lean`'s `section Poly` and
`Density/Transport.lean`), and `Res O N` is **not** a domain for `N ≥ 2`. Rather than duplicate
their proofs domain-free, this file transports them along `Polynomial.map`:
`monicPoly_class_monic`, `monicPoly_class_natDegree`, `coeff_monicPoly_class` are the three
class-side facts, each proved from an arbitrary integral lift, and `map_monicPoly_proj` is the
transport itself. `nontrivial_res`, `ext_of_monic_of_coeff_lt` and `eq_of_mul_eq_mul_of_monic` are
the three ring-level auxiliaries. All are exported: H.103–H.105 need them.

SOURCE: OM-2 §3.1 N-1a (displayed statement, *"with NO precision loss (the level-0 resultants are
units)"*); `EFF.GENIND.54`.

**TEETH** (`verification/openmath/OM2_genindb_battery.py`, RESULTS run 2026-08-16, 612/612):
`P2(i,ii) stratum counts + Hensel class bijection` — per residue configuration the factor-tuple
map is a bijection onto the predicted product of factor class spaces, `cnt == pred` **and**
`len(tup_seen[config]) == pred` (the second conjunct is exactly injectivity, i.e. no precision
loss: distinct factor-class tuples stay distinct mod `π ^ N`), 12 cells × 2 rings, exhaustive —
plus `P2(vii) both-characteristics census equality`. GC-8 disposition: **Lean theorems here**
(`bijOn_mulClass` is the bijection, `card_levelZeroStratum_mul` is `cnt == pred`'s
multiplicativity); **executable regression retained** for the exhaustive enumeration. §3 records
the battery's own product prediction `pred = ∏ q ^ (deg p̄ · mlt · (N − 1))` as kernel `#guard`s:
the prediction is *by construction* a product over the configuration's blocks, and what makes that
legitimate is precisely `card_levelZeroStratum_mul`.

## Status

Sorry-free, axiom-free (Lean core only: `propext`, `Classical.choice`, `Quot.sound`). The B.42
axiom does not enter §17 before H.123.
-/

set_option linter.style.longLine false

namespace Uniformity.Density.Induction

open IsLocalRing Polynomial

/-! ## 1. Ring-level auxiliaries -/

/-- **The truncation ring is nontrivial at `1 ≤ N`.** `𝔪 ^ N ≤ 𝔪 ≠ ⊤`. Needed for the monic
degree bookkeeping in `R = Res O N` (`Monic.ne_zero`, `Polynomial.modByMonic_eq_self_iff`). -/
theorem nontrivial_res (O : Type*) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {N : ℕ} (hN : 1 ≤ N) : Nontrivial (Res O N) := by
  refine Ideal.Quotient.nontrivial_iff.2 ?_
  intro h
  have h2 : (maximalIdeal O) ^ N ≤ maximalIdeal O := Ideal.pow_le_self (by omega)
  rw [h] at h2
  exact (maximalIdeal.isMaximal O).ne_top (top_le_iff.mp h2)

/-- Two monic polynomials of the same `natDegree` that agree in every coefficient *below* that
degree are equal (at the top both are `1`, above both vanish). This is what upgrades an equality
of coefficient CLASSES — a statement about `Fin n` many coefficients — to an equality of
polynomials over the truncation ring. -/
theorem ext_of_monic_of_coeff_lt {R : Type*} [CommRing R] {n : ℕ} {P Q : Polynomial R}
    (hP : P.Monic) (hQ : Q.Monic) (hPd : P.natDegree = n) (hQd : Q.natDegree = n)
    (h : ∀ i < n, P.coeff i = Q.coeff i) : P = Q := by
  refine Polynomial.ext fun i => ?_
  rcases lt_trichotomy i n with hi | hi | hi
  · exact h i hi
  · have h1 : P.coeff i = 1 := by
      have := hP.coeff_natDegree; rwa [hPd, ← hi] at this
    have h2 : Q.coeff i = 1 := by
      have := hQ.coeff_natDegree; rwa [hQd, ← hi] at this
    rw [h1, h2]
  · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega),
      Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)]

/-- **The uniqueness core, coprimality-as-hypothesis.** The pure-algebra half of the landed
`Uniformity.Hensel.monic_factorization_unique`: over ANY nontrivial commutative ring, two monic
factorizations of the same element with equal leading degrees agree, provided the *cross pair*
`g, h'` is coprime. (The landed theorem derives that coprimality from Hensel data over a complete
local ring; here it is supplied, so the lemma applies over `Res O N`, which is neither a domain
nor — as far as this file is concerned — equipped with any Hensel structure.) -/
theorem eq_of_mul_eq_mul_of_monic {R : Type*} [CommRing R] [Nontrivial R]
    {g h g' h' : Polynomial R} (hg : g.Monic) (hg' : g'.Monic)
    (hdeg : g.natDegree = g'.natDegree) (hcop : IsCoprime g h')
    (heq : g * h = g' * h') : g = g' ∧ h = h' := by
  have hdvd : g ∣ (g' - g) * h' := ⟨h - h', by linear_combination -heq⟩
  have hgU : g ∣ g' - g := hcop.dvd_of_dvd_mul_right hdvd
  have hdd : g'.degree = g.degree := by
    rw [Polynomial.degree_eq_natDegree hg'.ne_zero, Polynomial.degree_eq_natDegree hg.ne_zero,
      hdeg]
  have hdlt : (g' - g).degree < g.degree := by
    have := Polynomial.degree_sub_lt hdd hg'.ne_zero (by rw [hg'.leadingCoeff, hg.leadingCoeff])
    rwa [hdd] at this
  have hU0 : g' - g = 0 := by
    have e1 : (g' - g) %ₘ g = 0 := (Polynomial.modByMonic_eq_zero_iff_dvd hg).mpr hgU
    have e2 : (g' - g) %ₘ g = g' - g := (Polynomial.modByMonic_eq_self_iff hg).mpr hdlt
    rw [← e2, e1]
  have hgg' : g = g' := by linear_combination -hU0
  refine ⟨hgg', ?_⟩
  have hcancel : g * h = g * h' := by rw [heq, hgg']
  exact hg.isRegular.left hcancel

/-! ## 2. The class-side transport of the `monicPoly` facts -/

/-- **The truncation of a monic lift is the class's own `monicPoly`.** -/
theorem map_monicPoly_proj {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {n N : ℕ} (a : Fin n → O) :
    (monicPoly a).map (Ideal.Quotient.mk ((maximalIdeal O) ^ N)) = monicPoly (proj O n N a) := by
  rw [map_monicPoly]
  rfl

/-- `monicPoly c` is monic over the truncation ring, for every class `c` (no `IsDomain` on
`Res O N` — the fact is transported from an integral lift). -/
theorem monicPoly_class_monic {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {n N : ℕ} (c : Coeff O n N) : (monicPoly c).Monic := by
  obtain ⟨a, ha⟩ := proj_surjective' O n N c
  rw [← ha, ← map_monicPoly_proj a]
  exact (monicPoly_monic a).map _

/-- `monicPoly c` has degree `n` over the truncation ring, at `1 ≤ N`. -/
theorem monicPoly_class_natDegree {O : Type*} [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] {n N : ℕ} (hN : 1 ≤ N) (c : Coeff O n N) :
    (monicPoly c).natDegree = n := by
  haveI := nontrivial_res O hN
  obtain ⟨a, ha⟩ := proj_surjective' O n N c
  rw [← ha, ← map_monicPoly_proj a, (monicPoly_monic a).natDegree_map, monicPoly_natDegree]

/-- The coefficients of `monicPoly c` below degree `n` are exactly `c` — the class-side
`monicPoly_coeff_lt`. This is how a polynomial identity in `(Res O N)[X]` is read back as an
identity of coefficient classes. -/
theorem coeff_monicPoly_class {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {n N : ℕ} (c : Coeff O n N) (i : Fin n) :
    (monicPoly c).coeff (i : ℕ) = c i := by
  obtain ⟨a, ha⟩ := proj_surjective' O n N c
  rw [← ha, ← map_monicPoly_proj a, Polynomial.coeff_map, monicPoly_coeff_lt a i.isLt]
  rfl

/-! ## 3. The node -/

/-- **H.102, MapsTo half.** The product of two stratum classes lands in the product stratum.
No completeness is used here. -/
theorem mulClass_mem_levelZeroStratum {O : Type*} [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [IsAdicComplete (maximalIdeal O) O] {n₁ n₂ N : ℕ}
    (hN : 1 ≤ N) {g₁ g₂ : Polynomial (ResidueField O)} {c₁ : Coeff O n₁ N} {c₂ : Coeff O n₂ N}
    (h₁ : c₁ ∈ levelZeroStratum O n₁ N g₁) (h₂ : c₂ ∈ levelZeroStratum O n₂ N g₂) :
    mulClass c₁ c₂ ∈ levelZeroStratum O (n₁ + n₂) N (g₁ * g₂) := by
  obtain ⟨a₁, ha₁⟩ := proj_surjective' O n₁ N c₁
  obtain ⟨a₂, ha₂⟩ := proj_surjective' O n₂ N c₂
  obtain ⟨a, hEq⟩ := exists_monicPoly_eq ((monicPoly_monic a₁).mul (monicPoly_monic a₂))
    (by rw [(monicPoly_monic a₁).natDegree_mul (monicPoly_monic a₂), monicPoly_natDegree,
      monicPoly_natDegree])
  have hfe : a = fun i : Fin (n₁ + n₂) => (monicPoly a₁ * monicPoly a₂).coeff (i : ℕ) := by
    funext i
    rw [← hEq, monicPoly_coeff_lt a i.isLt]
  refine (mem_levelZeroStratum_iff hN _ _).2 ⟨a, ?_, ?_⟩
  · rw [hfe, mulClass_proj, ha₁, ha₂]
  · rw [hEq, Polynomial.map_mul, h₁ a₁ ha₁, h₂ a₂ ha₂]

set_option linter.unusedVariables false in
/-- **H.102, the no-precision-loss clause (`Set.InjOn`), exported.** Two factorizations of the
same level-`N` class into stratum classes of the SAME coprime residue factors agree factorwise
**mod `𝔪 ^ N` exactly** — the precision of the factors is the precision of the product.

(`h₁'` and `h₂` are kept for symmetry of the statement — the proof needs only the CROSS pair
`h₁`, `h₂'`, since coprimality is asked of `monicPoly c₁` against `monicPoly c₂'`. The landed
`Hensel.monic_factorization_unique` carries the same asymmetry, and records it the same way.) -/
theorem eq_of_mulClass_eq {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [IsAdicComplete (maximalIdeal O) O] {n₁ n₂ N : ℕ} (hN : 1 ≤ N)
    {g₁ g₂ : Polynomial (ResidueField O)} (hg₁ : g₁.Monic) (hg₂ : g₂.Monic)
    (hcop : IsCoprime g₁ g₂) {c₁ c₁' : Coeff O n₁ N} {c₂ c₂' : Coeff O n₂ N}
    (h₁ : c₁ ∈ levelZeroStratum O n₁ N g₁) (h₁' : c₁' ∈ levelZeroStratum O n₁ N g₁)
    (h₂ : c₂ ∈ levelZeroStratum O n₂ N g₂) (h₂' : c₂' ∈ levelZeroStratum O n₂ N g₂)
    (heq : mulClass c₁ c₂ = mulClass c₁' c₂') : c₁ = c₁' ∧ c₂ = c₂' := by
  haveI := nontrivial_res O hN
  obtain ⟨a₁, ha₁⟩ := proj_surjective' O n₁ N c₁
  obtain ⟨b₂, hb₂⟩ := proj_surjective' O n₂ N c₂'
  -- (2) the CROSS pair is coprime over `O`: the level-0 resultant is a unit
  have hcopO : IsCoprime (monicPoly a₁) (monicPoly b₂) :=
    Uniformity.Hensel.isCoprime_of_map_eq (monicPoly_monic a₁) (monicPoly_monic b₂) hg₁ hg₂ hcop
      (h₁ a₁ ha₁) (h₂' b₂ hb₂)
  -- (3) push the Bézout identity into the truncation ring
  have hcopR : IsCoprime (monicPoly c₁) (monicPoly c₂') := by
    have hmap := hcopO.map (Polynomial.mapRingHom (Ideal.Quotient.mk ((maximalIdeal O) ^ N)))
    simpa only [Polynomial.coe_mapRingHom, map_monicPoly_proj, ha₁, hb₂] using hmap
  -- (4) the two products are equal on the nose in `(Res O N)[X]`
  have hM₁ := monicPoly_class_monic c₁
  have hM₂ := monicPoly_class_monic c₂
  have hM₁' := monicPoly_class_monic c₁'
  have hM₂' := monicPoly_class_monic c₂'
  have hprod : monicPoly c₁ * monicPoly c₂ = monicPoly c₁' * monicPoly c₂' := by
    refine ext_of_monic_of_coeff_lt (n := n₁ + n₂) (hM₁.mul hM₂) (hM₁'.mul hM₂') ?_ ?_ ?_
    · rw [hM₁.natDegree_mul hM₂, monicPoly_class_natDegree hN, monicPoly_class_natDegree hN]
    · rw [hM₁'.natDegree_mul hM₂', monicPoly_class_natDegree hN, monicPoly_class_natDegree hN]
    · intro i hi
      have hc := congrFun heq ⟨i, hi⟩
      simpa only [mulClass_apply] using hc
  -- (5) the uniqueness core, then read the coefficients back
  obtain ⟨e₁, e₂⟩ := eq_of_mul_eq_mul_of_monic hM₁ hM₁'
    (by rw [monicPoly_class_natDegree hN, monicPoly_class_natDegree hN]) hcopR hprod
  refine ⟨funext fun i => ?_, funext fun i => ?_⟩
  · rw [← coeff_monicPoly_class c₁ i, ← coeff_monicPoly_class c₁' i, e₁]
  · rw [← coeff_monicPoly_class c₂ i, ← coeff_monicPoly_class c₂' i, e₂]

/-- **H.102 (bijection). The Hensel class bijection, N-1a.** Over coprime monic residue factors
`g₁, g₂` of degrees `n₁, n₂`, class multiplication is a bijection of the product of the factor
strata onto the product stratum — with NO precision loss. -/
theorem bijOn_mulClass {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [IsAdicComplete (maximalIdeal O) O] {n₁ n₂ N : ℕ} (hN : 1 ≤ N)
    {g₁ g₂ : Polynomial (ResidueField O)} (hg₁ : g₁.Monic) (hg₂ : g₂.Monic)
    (hd₁ : g₁.natDegree = n₁) (hd₂ : g₂.natDegree = n₂) (hcop : IsCoprime g₁ g₂) :
    Set.BijOn (fun p : Coeff O n₁ N × Coeff O n₂ N => mulClass p.1 p.2)
      ((levelZeroStratum O n₁ N g₁) ×ˢ (levelZeroStratum O n₂ N g₂))
      (levelZeroStratum O (n₁ + n₂) N (g₁ * g₂)) := by
  refine ⟨?_, ?_, ?_⟩
  · -- MapsTo
    rintro ⟨c₁, c₂⟩ ⟨h₁, h₂⟩
    exact mulClass_mem_levelZeroStratum hN h₁ h₂
  · -- InjOn: the no-precision-loss clause
    rintro ⟨c₁, c₂⟩ ⟨h₁, h₂⟩ ⟨c₁', c₂'⟩ ⟨h₁', h₂'⟩ heq
    obtain ⟨e₁, e₂⟩ := eq_of_mulClass_eq hN hg₁ hg₂ hcop h₁ h₁' h₂ h₂' heq
    exact Prod.ext e₁ e₂
  · -- SurjOn: Hensel on one lift of the product class
    intro c hc
    obtain ⟨a, ha⟩ := proj_surjective' O (n₁ + n₂) N c
    obtain ⟨f₁, f₂, hf₁, hf₂, hfa, hr₁, hr₂, hdf₁, hdf₂⟩ :=
      Uniformity.Hensel.exists_monic_factorization (monicPoly_monic a) hg₁ hg₂ hcop (hc a ha)
    obtain ⟨b₁, hb₁⟩ := exists_monicPoly_eq hf₁ (by rw [hdf₁, hd₁])
    obtain ⟨b₂, hb₂⟩ := exists_monicPoly_eq hf₂ (by rw [hdf₂, hd₂])
    refine ⟨(proj O n₁ N b₁, proj O n₂ N b₂), ⟨?_, ?_⟩, ?_⟩
    · exact (mem_levelZeroStratum_iff hN _ _).2 ⟨b₁, rfl, by rw [hb₁, hr₁]⟩
    · exact (mem_levelZeroStratum_iff hN _ _).2 ⟨b₂, rfl, by rw [hb₂, hr₂]⟩
    · change mulClass (proj O n₁ N b₁) (proj O n₂ N b₂) = c
      rw [← mulClass_proj b₁ b₂, hb₁, hb₂, ← hfa,
        show (fun i : Fin (n₁ + n₂) => (monicPoly a).coeff (i : ℕ)) = a from
          funext fun i => monicPoly_coeff_lt a i.isLt, ha]

/-- **H.102 (count corollary).** The stratum census multiplies over a coprime residue
factorization. (Unconditional in finiteness: `Nat.card` is `0` on infinite strata, and the
identity survives — but the intended reading is the finite one, `[Finite (ResidueField O)]`,
supplied by every consumer.) -/
theorem card_levelZeroStratum_mul {O : Type*} [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [IsAdicComplete (maximalIdeal O) O] {n₁ n₂ N : ℕ} (hN : 1 ≤ N)
    {g₁ g₂ : Polynomial (ResidueField O)} (hg₁ : g₁.Monic) (hg₂ : g₂.Monic)
    (hd₁ : g₁.natDegree = n₁) (hd₂ : g₂.natDegree = n₂) (hcop : IsCoprime g₁ g₂) :
    Nat.card (levelZeroStratum O (n₁ + n₂) N (g₁ * g₂))
      = Nat.card (levelZeroStratum O n₁ N g₁) * Nat.card (levelZeroStratum O n₂ N g₂) := by
  have hbij := bijOn_mulClass hN hg₁ hg₂ hd₁ hd₂ hcop
  calc Nat.card (levelZeroStratum O (n₁ + n₂) N (g₁ * g₂))
      = Nat.card ((levelZeroStratum O n₁ N g₁) ×ˢ (levelZeroStratum O n₂ N g₂) :
          Set (Coeff O n₁ N × Coeff O n₂ N)) :=
        (Nat.card_congr (Set.BijOn.equiv _ hbij)).symm
    _ = Nat.card ((levelZeroStratum O n₁ N g₁) × (levelZeroStratum O n₂ N g₂)) :=
        Nat.card_congr (Equiv.Set.prod _ _)
    _ = _ := Nat.card_prod _ _

end Uniformity.Density.Induction

/-! ## 4. TEETH, Lean half — the two halves of `P2(i,ii)` in the battery's own phrasing

`OM2_genindb_battery.py:889` checks, per residue configuration and per cell,

```python
if cnt != pred or len(tup_seen[config]) != pred: ok_i = False
```

where `pred = ∏_blocks q ** ((deg p̄) * mlt * (N-1))` is a PRODUCT over the configuration's blocks.
The two conjuncts are the two halves of this node: `cnt == pred` is the count corollary
(multiplicativity of the census), and `len(tup_seen[config]) == pred` is injectivity of the
factor-tuple map — *no precision loss*. Both are recorded below as `example`s in the battery's
phrasing: distinct factor-class tuples give distinct product classes, and every product class is
hit. -/

section Teeth

open Uniformity Uniformity.Density Uniformity.Density.Induction IsLocalRing Polynomial

/-- TEETH (a) — `len(tup_seen[config]) == pred`: distinct factor-class *tuples* stay distinct after
multiplication, at full precision `N`. -/
example {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [IsAdicComplete (maximalIdeal O) O] {n₁ n₂ N : ℕ} (hN : 1 ≤ N)
    {g₁ g₂ : Polynomial (ResidueField O)} (hg₁ : g₁.Monic) (hg₂ : g₂.Monic)
    (hcop : IsCoprime g₁ g₂) {c₁ c₁' : Coeff O n₁ N} {c₂ c₂' : Coeff O n₂ N}
    (h₁ : c₁ ∈ levelZeroStratum O n₁ N g₁) (h₁' : c₁' ∈ levelZeroStratum O n₁ N g₁)
    (h₂ : c₂ ∈ levelZeroStratum O n₂ N g₂) (h₂' : c₂' ∈ levelZeroStratum O n₂ N g₂)
    (hne : (c₁, c₂) ≠ (c₁', c₂')) : mulClass c₁ c₂ ≠ mulClass c₁' c₂' := by
  intro heq
  obtain ⟨e₁, e₂⟩ := eq_of_mulClass_eq hN hg₁ hg₂ hcop h₁ h₁' h₂ h₂' heq
  exact hne (by rw [e₁, e₂])

/-- TEETH (b) — the surjective half: every class of the product stratum IS a product of factor
classes (the battery reaches every `config` cell by reading factor tuples off lifts). -/
example {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [IsAdicComplete (maximalIdeal O) O] {n₁ n₂ N : ℕ} (hN : 1 ≤ N)
    {g₁ g₂ : Polynomial (ResidueField O)} (hg₁ : g₁.Monic) (hg₂ : g₂.Monic)
    (hd₁ : g₁.natDegree = n₁) (hd₂ : g₂.natDegree = n₂) (hcop : IsCoprime g₁ g₂)
    {c : Coeff O (n₁ + n₂) N} (hc : c ∈ levelZeroStratum O (n₁ + n₂) N (g₁ * g₂)) :
    ∃ c₁ ∈ levelZeroStratum O n₁ N g₁, ∃ c₂ ∈ levelZeroStratum O n₂ N g₂,
      mulClass c₁ c₂ = c := by
  obtain ⟨p, hp, hpc⟩ := (bijOn_mulClass hN hg₁ hg₂ hd₁ hd₂ hcop).surjOn hc
  exact ⟨p.1, hp.1, p.2, hp.2, hpc⟩

end Teeth

/-! ## 5. TEETH, numeric half — the battery's product prediction

`pred = ∏_blocks q ** ((deg p̄) * mlt * (N-1))` is legitimate as a PRODUCT exactly because the
census multiplies (`card_levelZeroStratum_mul`). The kernel checks below verify that the per-block
factors compose to the whole-stratum value `q ^ (n (N − 1))` — i.e. that the battery's product form
and its total agree — at every one of the 12 battery cells `[(n,q,Ns)] = [(2,2,[1,2,3]),
(2,3,[1,2,3]), (3,2,[2,3]), (3,3,[2]), (4,2,[2,3]), (4,3,[2])]`, split at every degree
`n = n₁ + n₂`. A consistency check on the battery's predictions, NOT a re-execution of its
exhaustive enumeration (GC-8). -/

section NumericGate

/-- Multiplicativity of the battery's `pred` under a degree split `n = n₁ + n₂`. -/
private def predSplit (q n₁ n₂ N : ℕ) : Prop :=
  q ^ (n₁ * (N - 1)) * q ^ (n₂ * (N - 1)) = q ^ ((n₁ + n₂) * (N - 1))

instance (q n₁ n₂ N : ℕ) : Decidable (predSplit q n₁ n₂ N) := by
  unfold predSplit; infer_instance

-- n = 2 = 1 + 1, q = 2, N ∈ {1, 2, 3}
#guard predSplit 2 1 1 1
#guard predSplit 2 1 1 2
#guard predSplit 2 1 1 3
-- n = 2 = 1 + 1, q = 3, N ∈ {1, 2, 3}
#guard predSplit 3 1 1 1
#guard predSplit 3 1 1 2
#guard predSplit 3 1 1 3
-- n = 3 = 1 + 2, q = 2, N ∈ {2, 3}
#guard predSplit 2 1 2 2
#guard predSplit 2 1 2 3
-- n = 3 = 1 + 2, q = 3, N = 2
#guard predSplit 3 1 2 2
-- n = 4 = 1 + 3 and 2 + 2, q = 2, N ∈ {2, 3}
#guard predSplit 2 1 3 2
#guard predSplit 2 1 3 3
#guard predSplit 2 2 2 2
#guard predSplit 2 2 2 3
-- n = 4 = 1 + 3 and 2 + 2, q = 3, N = 2
#guard predSplit 3 1 3 2
#guard predSplit 3 2 2 2

end NumericGate

/-! ## 6. Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Induction.nontrivial_res
#print axioms Uniformity.Density.Induction.ext_of_monic_of_coeff_lt
#print axioms Uniformity.Density.Induction.eq_of_mul_eq_mul_of_monic
#print axioms Uniformity.Density.Induction.map_monicPoly_proj
#print axioms Uniformity.Density.Induction.monicPoly_class_monic
#print axioms Uniformity.Density.Induction.monicPoly_class_natDegree
#print axioms Uniformity.Density.Induction.coeff_monicPoly_class
#print axioms Uniformity.Density.Induction.mulClass_mem_levelZeroStratum
#print axioms Uniformity.Density.Induction.eq_of_mulClass_eq
#print axioms Uniformity.Density.Induction.bijOn_mulClass
#print axioms Uniformity.Density.Induction.card_levelZeroStratum_mul

end AxCheck
