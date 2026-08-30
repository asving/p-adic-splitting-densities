/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import Uniformity.ChapI.IFCG44

/-!
# Uniformity.ChapI.IFCG47 — UNIT DTR: decision transport across the recentring
(the OM tower step), the scaled-type calculus, and the prime-mass full-span fire

Stage DTR of the cone census (design record `runs/wave-c/verdict_DTR.md`; the fence is
PSL4's verdict `runs/wave-c/verdict_PSL4.md` §item-3 and ER4's `runs/wave-c/verdict_ER4.md`).
PSL4 named the ONE missing leg of `PowerFullSpanLaw m σ`: **the decision transport across
the recentring** — `DecidedAt` over `O` at a full-span pure class ⟺ `DecidedAt` over
`O' = AdjoinRoot (eisKey π w e')` of the transported class at the `e'`-rescaled type.
This file:

* **§0 the scaled-type calculus** (`scaleType`): the tower bookkeeping
  `(e, f) ↦ (e'·e, f)` of the classical multiplicativity `e(L/K) = e(L/K')·e(K'/K)`,
  `f(L/K) = f(L/K')` for the totally ramified Eisenstein step `e(K'/K) = e'`,
  `f(K'/K) = 1` (`eis_residueCard`): degree scaling, `scaleType 1 = id`, tower
  composition `scaleType e₁ ∘ scaleType e₂ = scaleType (e₁·e₂)`, and injectivity at
  `e' > 0` (what lets ONE pointwise scaling law drive BOTH transport directions).
* **§1 THE NAMED REMAINDER** (`CellTypeScalingAt D`): the pointwise OM tower step —
  a monic block `g` of degree `e'·D` on the full-span lattice (raw purity: on or above
  the slope-`1/e'` line) whose `eisKey`-adic transform lies in the DEEP recentred box
  (`α^{e'(D−t)+1} ∣ mk (dev g t)`, the `alphaBox` divisibilities) has
  `typeOf g = scaleType e' (typeOf (devT g))`.  This is the exact pointwise content of
  the Montes/Okutsu induction step at the `(h, d) = (1, 1)` frame; it is NOT proved
  here for `D ≥ 2` (the deep-wild tower — C136's territory) and is the unit's honest
  named remainder.  **The naive alternative is FALSE**: `devT` is NOT multiplicative
  (`devT(x)·devT(x) = α² = −wπ` vs `devT(x²) = Y − wπ` at `eisKey = x² + wπ` — carry
  terms), so no unconditional "factorizations pull back through the bijection" exists;
  the correspondence is a cell theorem, exactly as stated.
* **§2 THE DECISION TRANSPORT, PROVED both ways from the ONE pointwise law**:
  at a minimal-face class `c` (`MinFaceAt c 1 e'`, the full-span frame) whose transport
  lies in the `alphaBox`,
  `DecidedAt O' D σ' (e'·N) (cellTransport c) ⟺ DecidedAt O (e'·D) (scaleType e' σ') N c`.
  Outbound: every `O`-lift's transform is an `O'`-lift of the transported class
  (`cellTransport_apply` + IFCG39's outbound level exactness), the `O'`-decision fires,
  and the pointwise law converts.  Inbound: every `O'`-lift's reassembly is an `O`-lift
  of `c` (`cellTransport_symm_apply`), the `O`-decision fires, the pointwise law applied
  to the reassembly reads `devT (reassT G) = G`, and `scaleType`-injectivity converts.
  The level scales by EXACTLY `e'` (`fScale = e'`), the type by `(e,f) ↦ (e'e, f)` —
  the two bookkeepings of the same tower step.
* **§3 THE PRIME-MASS FIRE** (`powerFullSpanLaw_of_prime`, UNCONDITIONAL): the
  full-span power sector at prime mass is EMPTY — full span forces `m = e'·(k·deg ψ)`
  with `e' ≥ 2` (fractional face) AND `k ≥ 2` (proper power residual), a factorization
  of `m` into two factors `≥ 2` — so `PowerFullSpanLaw m σ` holds with rational pair
  `(0, 1)` at EVERY prime `m` and EVERY `σ`.  (PSL4's census row left this on the
  premise list at all masses; at the ramified-remainder masses `m = 5, 7, 11, …` the
  full-span law is now CLOSED.)

## Honest scope (the exact remainder)

`CellTypeScalingAt D` for `D ≥ 2` is the surviving open mathematics (`D = k·deg ψ ≥ 2`
is the only shape `powerSectorFull` produces).  With it, §2 transports the decided
intersection; the face/centre partition assembly + `recentred_decidedSeq_tendsto`
summation (PSL4's consumption plan) remain a separate unit.  ER4's dd-recursion terms
(`e1DdDecFam σ`: mass 4, `e' = 2`, `D = 2`, key `X² − bπ`) are the first census
consumers of the `D = 2` instance.

## Axiom fence

Everything here composes landed Lean-core material (IFCG35/39/43/44 instruments);
expected footprint: pure Lean core `{propext, Classical.choice, Quot.sound}` on §0–§2
and on the §3 emptiness; the §3 law wrappers may inherit B.42
(`Uniformity.Density.Leaf.exists_slope_factorization`) ONLY through `powerSector`'s
carrier (IFCG35's front) if it occurs there — the C.33 cites must NOT occur.
Zero sorries at landing.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

noncomputable section

namespace Uniformity.Density.IFCG47

open IsLocalRing Polynomial Filter Topology
open Uniformity.Density.Induction
open Uniformity.Density.Leaf
open Uniformity.Density.IFCG24 (ZcURLim)
open Uniformity.Density.IFCG35 (MinFaceAt minFaceAt_unique classResidualPoly powerSector
  ResidualLeafLaw residualLeafLaw_one)
open Uniformity.Density.IFCG39 (powerSector_data eisKey eisKey_monic eisKey_natDegree
  devT devT_coeff devT_monic reassT reassT_monic devT_reassT reassT_devT
  eis_root_pow_dvd_mk_iff)
open Uniformity.Density.IFCG43 (cellTransport cellTransport_apply cellTransport_symm_apply
  devVec reassVec eis_root_irreducible)
open Uniformity.Density.IFCG44 (alphaBox cellTransport_mem_alphaBox_iff fullSpan_raw_dvd
  powerSectorFull PowerFullSpanLaw)

attribute [local instance] Classical.propDecidable

/-! ## §0 — the scaled-type calculus (the tower bookkeeping `(e, f) ↦ (e'·e, f)`) -/

section ScaleType

/-- **The `e'`-scaled factorization type**: each `(e, f)` member becomes `(e'·e, f)` —
the classical tower multiplicativity `e(L/K) = e(L/K')·e(K'/K)`, `f(L/K) = f(L/K')`
along a totally ramified step `e(K'/K) = e'`, `f(K'/K) = 1` (the Eisenstein recentring:
`eis_residueCard` pins `q' = q`). -/
def scaleType (e' : ℕ) (σ : FactorizationType) : FactorizationType :=
  ⟨σ.data.map fun p => (e' * p.1, p.2)⟩

theorem scaleType_data (e' : ℕ) (σ : FactorizationType) :
    (scaleType e' σ).data = σ.data.map fun p => (e' * p.1, p.2) := rfl

/-- Degree scales by exactly `e'` — the same `fScale = e'` as the level bookkeeping. -/
theorem scaleType_degree (e' : ℕ) (σ : FactorizationType) :
    (scaleType e' σ).degree = e' * σ.degree := by
  unfold FactorizationType.degree
  rw [scaleType_data, Multiset.map_map]
  have h1 : ((fun p : ℕ × ℕ => p.1 * p.2) ∘ fun p : ℕ × ℕ => (e' * p.1, p.2))
      = fun p : ℕ × ℕ => e' * (p.1 * p.2) := by
    funext p
    simp [Function.comp, Nat.mul_assoc]
  rw [h1, ← Multiset.sum_map_mul_left]

@[simp] theorem scaleType_one (σ : FactorizationType) : scaleType 1 σ = σ := by
  ext
  rw [scaleType_data]
  have h1 : (fun p : ℕ × ℕ => (1 * p.1, p.2)) = id := by
    funext p
    simp
  rw [h1, Multiset.map_id]

/-- Tower composition: scaling by `e₁` after `e₂` is scaling by `e₁·e₂` — the
associativity of `e(L/K) = e(L/K'')·e(K''/K')·e(K'/K)` in the bookkeeping. -/
theorem scaleType_scaleType (e₁ e₂ : ℕ) (σ : FactorizationType) :
    scaleType e₁ (scaleType e₂ σ) = scaleType (e₁ * e₂) σ := by
  apply FactorizationType.ext
  rw [scaleType_data, scaleType_data, scaleType_data, Multiset.map_map]
  refine Multiset.map_congr rfl fun p _ => ?_
  simp [Function.comp, Nat.mul_assoc]

/-- Scaling is injective at `e' > 0` — the lever that lets the ONE pointwise scaling
law drive BOTH directions of the decision transport. -/
theorem scaleType_injective {e' : ℕ} (he' : 0 < e') :
    Function.Injective (scaleType e') := by
  intro σ τ h
  apply FactorizationType.ext
  have hinj : Function.Injective fun p : ℕ × ℕ => (e' * p.1, p.2) := by
    intro p q hpq
    obtain ⟨h1, h2⟩ := Prod.mk.injEq .. ▸ hpq
    exact Prod.ext (Nat.eq_of_mul_eq_mul_left he' h1) h2
  have hdata : σ.data.map (fun p : ℕ × ℕ => (e' * p.1, p.2))
      = τ.data.map (fun p : ℕ × ℕ => (e' * p.1, p.2)) := by
    rw [← scaleType_data, ← scaleType_data, h]
  exact Multiset.map_injective hinj hdata

end ScaleType

/-! ## §0b — kit (private replicas of the established supply) -/

section Kit

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]

/-- The canonical key `X` (B83Kit/IFCG35 idiom, private copy). -/
private theorem isKey_X : IsKey (Polynomial.X : Polynomial R) where
  monic := Polynomial.monic_X
  pos := by simp
  irred := by rw [Polynomial.map_X]; exact Polynomial.irreducible_X

omit [IsDiscreteValuationRing R] in
/-- A monic polynomial of degree `n` is `monicPoly` of its own low coefficient vector
(C53b's idiom, private copy). -/
private theorem monicPoly_coeff_self {n : ℕ} {f : Polynomial R} (hf : f.Monic)
    (hn : f.natDegree = n) : monicPoly (fun i : Fin n => f.coeff i.1) = f := by
  classical
  have hlead : f.coeff n = 1 := by rw [← hn]; exact hf.coeff_natDegree
  refine Polynomial.ext fun m => ?_
  rcases lt_trichotomy m n with h | h | h
  · rw [monicPoly_coeff_lt _ h]
  · have h1 : (monicPoly (fun i : Fin n => f.coeff i.1)).coeff n = 1 := by
      have h2 := (monicPoly_monic (fun i : Fin n => f.coeff i.1)).coeff_natDegree
      rwa [monicPoly_natDegree] at h2
    rw [h, h1, hlead]
  · have h1 : (monicPoly (fun i : Fin n => f.coeff i.1)).natDegree = n :=
      monicPoly_natDegree _
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt
        (by omega : (monicPoly (fun i : Fin n => f.coeff i.1)).natDegree < m),
      Polynomial.coeff_eq_zero_of_natDegree_lt (by omega : f.natDegree < m)]

/-- B83Kit's membership unfolding for the Classical `sideSet` filter (private copy). -/
private theorem mem_sideSet_iff' {φ f : Polynomial R} {u ℓ j : ℕ} :
    j ∈ sideSet φ f u ℓ ↔ (j < f.natDegree + 1 ∧ OnSide φ f u ℓ j) := by
  classical
  constructor
  · intro hj
    have hj' : j ∈ Finset.filter (OnSide φ f u ℓ) (Finset.range (f.natDegree + 1)) := hj
    obtain ⟨h1, h2⟩ := Finset.mem_filter.mp hj'
    exact ⟨Finset.mem_range.mp h1, h2⟩
  · rintro ⟨h1, h2⟩
    show j ∈ Finset.filter (OnSide φ f u ℓ) (Finset.range (f.natDegree + 1))
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr h1, h2⟩

/-- The Eisenstein key's degree, `WithBot` form (IFCG39's private lemma, replica). -/
private theorem eisKey_degree' {π c : R} {e' : ℕ} (he' : 0 < e') :
    (eisKey π c e').degree = ((e' : ℕ) : WithBot ℕ) := by
  rw [Polynomial.degree_eq_natDegree (eisKey_monic he').ne_zero, eisKey_natDegree he']

end Kit

/-! ## §1 — THE NAMED REMAINDER: the pointwise cell type-scaling (the OM tower step) -/

section CellTypeScaling

/-- **THE POINTWISE OM TOWER STEP at `(h, d) = (1, 1)`, mass `e'·D`** — the named
remainder Prop of the decision transport: a monic block `g` of degree `e'·D` whose
coefficients sit on or above the slope-`1/e'` full-span line (the raw purity lattice,
`fullSpan_raw_dvd`'s shape at `h = 1`) and whose `eisKey`-adic digits lie in the DEEP
recentred box (`α^{e'(D−t)+1} ∣ mk (dev g t)` — `alphaBox`'s divisibilities, one notch
strictly above the `e'`-scaled Eisenstein line) has its splitting type equal to the
`e'`-scaling of the splitting type of its dev transform over the recentring ring
`O' = AdjoinRoot (eisKey π w e')`:

    typeOf g = scaleType e' (typeOf (devT (eisKey π w e') D g)).

This is the exact pointwise content of the Montes/Okutsu induction step: the monic
irreducible factors of `g` over `O` correspond to the monic irreducible factors of the
transform over `O'`, each `(e, f)` composing through the totally ramified step to
`(e'·e, f)`.  It is TRUE by the classical OM theory (FGMN; the corpus's cited
literature) and NOT YET provable from the landed corpus at `D ≥ 2` — the deep-wild
tower.  `devT` is provably NOT multiplicative (carry terms), so this cell statement is
the correct — and only — general form. -/
def CellTypeScalingAt (D : ℕ) : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [IsAdicComplete (maximalIdeal O) O] [Finite (ResidueField O)],
  ∀ π w : O, Irreducible π → IsLocalRing.residue O w ≠ 0 →
  ∀ e' : ℕ, 2 ≤ e' →
  ∀ [IsDomain (AdjoinRoot (eisKey π w e'))]
    [IsDiscreteValuationRing (AdjoinRoot (eisKey π w e'))],
  ∀ g : Polynomial O, g.Monic → g.natDegree = e' * D →
    (∀ j, j < e' * D → π ^ ((e' * D - j + (e' - 1)) / e') ∣ g.coeff j) →
    (∀ t, t < D → (AdjoinRoot.root (eisKey π w e')) ^ (e' * (D - t) + 1)
        ∣ AdjoinRoot.mk (eisKey π w e') (dev (eisKey π w e') g t)) →
    typeOf g = scaleType e' (typeOf (devT (eisKey π w e') D g))

/-- The full pointwise law: every recentred residual degree `D`. -/
def CellTypeScaling : Prop := ∀ D : ℕ, CellTypeScalingAt D

/-- ★ **THE DEPTH-1 WITNESS: the pointwise scaling law HOLDS at `D = 1`** — the
Eisenstein leaf, machine-checking the statement's bookkeeping (centre sign, level
scale, `(e, f) ↦ (e'·e, f)`).  At `D = 1` the raw lattice + the deep box force `g`
Eisenstein at `π` with `v(g₀) = 1` EXACTLY (`v(g₀ − wπ) ≥ 2` and `w` a unit), the
x-frame polygon is the single slope-`1/e'` side spanning `[0, e']` with linear
residual, and IFCG35's UNCONDITIONAL `d = 1` leaf law reads `typeOf g = ⟨{(e', 1)}⟩`
= `scaleType e' ⟨{(1, 1)}⟩` — the transform is monic linear, of type `⟨{(1, 1)}⟩`.
(`powerSectorFull` only produces `D ≥ 2`, so this instance carries no census weight;
it is the statement-correctness witness.) -/
theorem cellTypeScalingAt_one : CellTypeScalingAt 1 := by
  intro O _ _ _ _ _ π w hπ hw e' he' _ _ g hg hdeg hlat hbox
  have he'' : 0 < e' := by omega
  have hdeg' : g.natDegree = e' := by rw [hdeg, Nat.mul_one]
  have hπm : π ∈ maximalIdeal O :=
    (IsLocalRing.mem_maximalIdeal π).mpr (mem_nonunits_iff.mpr hπ.not_isUnit)
  -- A. the Eisenstein data: `π ∣ gⱼ` below the top, `v(g₀) = 1` exactly
  have hE1 : ∀ j, j < e' → π ∣ g.coeff j := by
    intro j hj
    have h1 := hlat j (by omega)
    have hq : 1 ≤ (e' * 1 - j + (e' - 1)) / e' := by
      rw [Nat.le_div_iff_mul_le he'']
      omega
    exact dvd_trans (by simpa using pow_dvd_pow π hq) h1
  have hkey_deg : (eisKey π w e').natDegree = e' := eisKey_natDegree he''
  have hDpos : 0 < (eisKey π w e').natDegree := by rw [hkey_deg]; omega
  -- the zeroth digit is `g − eisKey`
  have hd : g.degree = (eisKey π w e').degree := by
    rw [Polynomial.degree_eq_natDegree hg.ne_zero,
      Polynomial.degree_eq_natDegree (eisKey_monic he'').ne_zero, hdeg', hkey_deg]
  have hlc : g.leadingCoeff = (eisKey π w e').leadingCoeff := by
    rw [hg.leadingCoeff, (eisKey_monic he'').leadingCoeff]
  have hdegsub : (g - eisKey π w e').degree < (eisKey π w e').degree := by
    have h1 := Polynomial.degree_sub_lt hd hg.ne_zero hlc
    rwa [hd] at h1
  have hsplit' : (g - eisKey π w e') + eisKey π w e' = g := by ring
  have hdev0 : dev (eisKey π w e') g 0 = g - eisKey π w e' := by
    show g %ₘ eisKey π w e' = g - eisKey π w e'
    conv_lhs => rw [← hsplit']
    rw [Polynomial.add_modByMonic,
      (Polynomial.modByMonic_eq_self_iff (eisKey_monic he'')).mpr hdegsub,
      Polynomial.modByMonic_self, add_zero]
    exact eisKey_monic he''
  have hkey_c0 : (eisKey π w e').coeff 0 = w * π := by
    show (Polynomial.X ^ e' + Polynomial.C (w * π)).coeff 0 = w * π
    rw [Polynomial.coeff_add, Polynomial.coeff_X_pow, if_neg (by omega : ¬ (0 : ℕ) = e'),
      Polynomial.coeff_C, if_pos rfl, zero_add]
  have hc00 : (dev (eisKey π w e') g 0).coeff 0 = g.coeff 0 - w * π := by
    rw [hdev0, Polynomial.coeff_sub, hkey_c0]
  -- the deep box at `t = 0` reads `π² ∣ g₀ − wπ`
  have hdevdeg : (dev (eisKey π w e') g 0).degree < ((e' : ℕ) : WithBot ℕ) := by
    have h1 := degree_dev_lt (eisKey_monic he'') hDpos g 0
    rwa [eisKey_degree' he''] at h1
  have hb0 := hbox 0 (by omega)
  have hb0' : (AdjoinRoot.root (eisKey π w e')) ^ (e' + 1)
      ∣ AdjoinRoot.mk (eisKey π w e') (dev (eisKey π w e') g 0) := by
    have hexp0 : e' * (1 - 0) + 1 = e' + 1 := by omega
    rwa [hexp0] at hb0
  have hread := (eis_root_pow_dvd_mk_iff hπ hw he'' hdevdeg (e' + 1)).mp hb0' 0 he''
  have hexp2 : (e' + 1 + e' - 1 - 0) / e' = 2 := by
    have h : e' + 1 + e' - 1 - 0 = 2 * e' := by omega
    rw [h]
    exact Nat.mul_div_cancel 2 he''
  rw [hexp2] at hread
  have hpi2 : π ^ 2 ∣ g.coeff 0 - w * π := hc00 ▸ hread
  have hne2 : ¬ π ^ 2 ∣ g.coeff 0 := by
    intro hcon
    have hwpi : π ^ 2 ∣ w * π := by
      have hsub := dvd_sub hcon hpi2
      simpa using hsub
    have h2 : π ∣ w := by
      have h3 : π * π ∣ w * π := by rwa [pow_two] at hwpi
      exact (mul_dvd_mul_iff_right hπ.ne_zero).mp h3
    obtain ⟨y, hy⟩ := h2
    apply hw
    rw [hy]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mul_mem_right y _ hπm)
  -- the exact valuation `v(g₀) = 1`
  have hv1le : ((1 : ℕ) : ℕ∞) ≤ IsDiscreteValuationRing.addVal O (g.coeff 0) :=
    (le_addVal_iff_pow_dvd hπ 1 _).mpr (by simpa using hE1 0 he'')
  have hv2not : ¬ ((2 : ℕ) : ℕ∞) ≤ IsDiscreteValuationRing.addVal O (g.coeff 0) :=
    fun hcon => hne2 ((le_addVal_iff_pow_dvd hπ 2 _).mp hcon)
  have hv0 : IsDiscreteValuationRing.addVal O (g.coeff 0) = ((1 : ℕ) : ℕ∞) := by
    refine le_antisymm ?_ hv1le
    by_contra h3
    refine hv2not ?_
    have h4 : ((1 : ℕ) : ℕ∞) < IsDiscreteValuationRing.addVal O (g.coeff 0) := not_le.mp h3
    have h5 := (ENat.add_one_le_iff (ENat.coe_ne_top 1)).mpr h4
    have h6 : ((1 : ℕ) : ℕ∞) + 1 = ((2 : ℕ) : ℕ∞) := by norm_cast
    rwa [h6] at h5
  have hcoefftop : g.coeff e' = 1 := by
    rw [← hdeg']
    exact hg.coeff_natDegree
  have haddone : IsDiscreteValuationRing.addVal O (1 : O) = 0 :=
    (IsDiscreteValuationRing.addVal O).map_one
  -- B. the support value: `suppVal = e'`, attained at `0` and `e'`
  have hsupp : suppVal X g 1 e' = ((e' : ℕ) : ℕ∞) := by
    apply le_antisymm
    · have hmem : g.natDegree ∈ Finset.range (g.natDegree + 1) :=
        Finset.self_mem_range_succ g.natDegree
      have h1 : suppVal X g 1 e'
          ≤ e' • npHgt X g g.natDegree + ((1 * g.natDegree : ℕ) : ℕ∞) :=
        Finset.inf_le hmem
      have h2 : e' • npHgt X g g.natDegree + ((1 * g.natDegree : ℕ) : ℕ∞)
          = ((e' : ℕ) : ℕ∞) := by
        rw [npHgt_X, hg.coeff_natDegree, haddone, smul_zero, zero_add, Nat.one_mul, hdeg']
      exact h2 ▸ h1
    · refine Finset.le_inf fun j hj => ?_
      have hj' : j < g.natDegree + 1 := Finset.mem_range.mp hj
      rcases Nat.lt_or_ge j e' with hje | hje
      · have h1' : (1 : ℕ∞) ≤ npHgt X g j := by
          rw [npHgt_X]
          exact_mod_cast (le_addVal_iff_pow_dvd hπ 1 _).mpr (by simpa using hE1 j hje)
        calc ((e' : ℕ) : ℕ∞) = (e' : ℕ∞) * 1 := by rw [mul_one]
          _ ≤ (e' : ℕ∞) * npHgt X g j := mul_le_mul' le_rfl h1'
          _ = e' • npHgt X g j := (nsmul_eq_mul _ _).symm
          _ ≤ e' • npHgt X g j + ((1 * j : ℕ) : ℕ∞) := le_self_add
      · have hje' : j = e' := by omega
        rw [hje', Nat.one_mul]
        exact le_add_self
  -- C. the two on-side endpoints, purity, and the side pins
  have hOn0 : OnSide X g 1 e' 0 := by
    show e' • npHgt X g 0 + ((1 * 0 : ℕ) : ℕ∞) = suppVal X g 1 e'
    rw [hsupp, npHgt_X, hv0, Nat.mul_zero, Nat.cast_zero, add_zero, Nat.cast_one,
      nsmul_eq_mul, mul_one]
  have hOnTop : OnSide X g 1 e' e' := by
    show e' • npHgt X g e' + ((1 * e' : ℕ) : ℕ∞) = suppVal X g 1 e'
    rw [hsupp, npHgt_X, hcoefftop, haddone, smul_zero, zero_add, Nat.one_mul]
  have hpure : IsPure X g 1 e' := by
    refine ⟨hOn0, ?_⟩
    rw [Polynomial.natDegree_X, Nat.div_one, hdeg']
    exact hOnTop
  have h0mem : 0 ∈ sideSet X g 1 e' := mem_sideSet_iff'.mpr ⟨by omega, hOn0⟩
  have hemem : e' ∈ sideSet X g 1 e' := mem_sideSet_iff'.mpr ⟨by omega, hOnTop⟩
  have hne : (sideSet X g 1 e').Nonempty := ⟨0, h0mem⟩
  have hmin' : sideMin X g 1 e' hne = 0 := by
    unfold sideMin
    exact Nat.le_zero.mp (Finset.min'_le _ 0 h0mem)
  have hmax' : sideMax X g 1 e' hne = e' := by
    unfold sideMax
    refine le_antisymm ?_ (Finset.le_max' _ e' hemem)
    refine Finset.max'_le _ _ _ fun j hj => ?_
    have h1 := (mem_sideSet_iff'.mp hj).1
    omega
  have hsd : sideDeg X g 1 e' hne = 1 := by
    unfold sideDeg
    rw [hmax', hmin', Nat.sub_zero]
    exact Nat.div_self he''
  -- D. the residue pin `ḡ = X^{e'}`
  have hres : g.map (IsLocalRing.residue O) = X ^ (e' * 1) := by
    rw [Nat.mul_one]
    refine Polynomial.ext fun i => ?_
    rw [Polynomial.coeff_map, Polynomial.coeff_X_pow]
    rcases lt_trichotomy i e' with hi | hi | hi
    · rw [if_neg (by omega)]
      obtain ⟨y, hy⟩ := hE1 i hi
      rw [hy]
      exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mul_mem_right y _ hπm)
    · rw [if_pos hi]
      rw [hi, hcoefftop, map_one]
    · rw [if_neg (by omega), Polynomial.coeff_eq_zero_of_natDegree_lt (by omega), map_zero]
  -- E. the residual polynomial is linear, hence irreducible
  have htop : suppVal X g 1 e' ≠ ⊤ := by
    rw [hsupp]
    exact ENat.coe_ne_top e'
  have hH₀ : npHgt X g (sideMin X g 1 e' hne) = ((1 : ℕ) : ℕ∞) := by
    rw [hmin', npHgt_X, hv0]
  have hnd := natDegree_resPoly hπ isKey_X he'' (Nat.coprime_one_left e') htop hne hH₀
  letI : Field (resField (X : Polynomial O)) := instFieldResField isKey_X
  have hRne : resPoly π X g 1 e' hne 1 ≠ 0 := by
    intro hcon
    have h2 := hnd.2
    rw [hcon] at h2
    simp at h2
  have hdeg1 : (resPoly π X g 1 e' hne 1).natDegree = 1 := by
    rw [hnd.1, hsd]
  have hirr : Irreducible (resPoly π X g 1 e' hne 1) :=
    Polynomial.irreducible_of_degree_eq_one
      ((Polynomial.degree_eq_iff_natDegree_eq hRne).mpr hdeg1)
  -- F. the unconditional `d = 1` leaf law fires
  have htyg : typeOf g = ⟨{(e', 1)}⟩ :=
    residualLeafLaw_one he'' O π hπ 1 one_pos (Nat.coprime_one_left e') g hg hpure hne
      hsd hres 1 hH₀ hirr
  -- G. the transform is monic linear: type `⟨{(1, 1)}⟩`
  have hTdeg : g.natDegree = (eisKey π w e').natDegree * 1 := by
    rw [hdeg', hkey_deg, Nat.mul_one]
  obtain ⟨hTmon, hTdeg'⟩ := devT_monic (eisKey_monic he'') hDpos hg hTdeg
  have htyT : typeOf (devT (eisKey π w e') 1 g) = ⟨{(1, 1)}⟩ :=
    typeOf_of_natDegree_one hTmon hTdeg'
  rw [htyg, htyT]
  apply FactorizationType.ext
  rw [scaleType_data]
  simp

end CellTypeScaling

/-! ## §2 — THE DECISION TRANSPORT (both directions from the one pointwise law) -/

section Transport

-- NOTE (ER4's universe fence, second contact): the named Prop quantifies `O : Type`
-- (ZcURLim's convention), so its consumers live in a `{O : Type}` section.
variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [IsAdicComplete (maximalIdeal O) O] [Finite (ResidueField O)]
variable {π w : O} {e' D : ℕ}
variable [IsDomain (AdjoinRoot (eisKey π w e'))]
  [IsDiscreteValuationRing (AdjoinRoot (eisKey π w e'))]
  [Finite (ResidueField (AdjoinRoot (eisKey π w e')))]

/-- ★★ **THE DECISION TRANSPORT, INBOUND** (the OM tower step, decided form): at a
minimal-face class `c` (`MinFaceAt c 1 e'`, the full-span Eisenstein frame) whose
transport lies in the deep recentred box, an `O'`-decision at type `σ'` and level
`e'·N` PULLS BACK to an `O`-decision at the `e'`-scaled type and level `N` —
conditional on exactly the pointwise scaling law at `D`.  Mechanism: every `O`-lift's
transform is an `O'`-lift of the transported class (`cellTransport_apply`), the
`O'`-decision types the transform, and `CellTypeScalingAt D` converts. -/
theorem decidedAt_of_transport_decidedAt (hCTS : CellTypeScalingAt D)
    (hπ : Irreducible π) (hw : IsLocalRing.residue O w ≠ 0) (he' : 2 ≤ e')
    {N : ℕ} (hDN : D < N) {c : Coeff O (e' * D) N}
    (hF : MinFaceAt c 1 e')
    (hbox : cellTransport hπ hw he' D N c ∈ alphaBox π w e' D (e' * N))
    {σ' : FactorizationType}
    (hdec : DecidedAt (AdjoinRoot (eisKey π w e')) D σ' (e' * N)
      (cellTransport hπ hw he' D N c)) :
    DecidedAt O (e' * D) (scaleType e' σ') N c := by
  intro a ha
  have he'' : 0 < e' := by omega
  -- (i) the raw purity lattice on the lift (slope minimality of the face)
  have hlat := fullSpan_raw_dvd hπ hF ha
  -- (ii) the deep-box divisibilities on the lift (the transported class's box read)
  have hbox' := (cellTransport_mem_alphaBox_iff hπ hw he' hDN a).mp
    (by rw [ha]; exact hbox)
  -- the pointwise scaling law at the lift
  have hscale := hCTS O π w hπ hw e' he' (monicPoly a) (monicPoly_monic a)
    (monicPoly_natDegree a)
    (fun j hj => by
      have h1 := hlat j hj
      rwa [one_mul] at h1) hbox'
  -- the transform is an `O'`-lift of the transported class
  have hb : proj (AdjoinRoot (eisKey π w e')) D (e' * N) (devVec π w e' D a)
      = cellTransport hπ hw he' D N c := by
    rw [← ha, cellTransport_apply]
  have hdev := hdec (devVec π w e' D a) hb
  -- `monicPoly (devVec a) = devT (monicPoly a)`
  have hDpos : 0 < (eisKey π w e').natDegree := by
    rw [eisKey_natDegree he'']
    omega
  have hadeg : (monicPoly a).natDegree = (eisKey π w e').natDegree * D := by
    rw [monicPoly_natDegree, eisKey_natDegree he'']
  obtain ⟨hmon, hdeg⟩ := devT_monic (eisKey_monic he'') hDpos (monicPoly_monic a) hadeg
  have hveq : devVec π w e' D a
      = fun i : Fin D => (devT (eisKey π w e') D (monicPoly a)).coeff i.1 := rfl
  rw [hveq, monicPoly_coeff_self hmon hdeg] at hdev
  rw [hscale, hdev]

/-- ★★ **THE DECISION TRANSPORT, OUTBOUND** (the converse): at the same frame, an
`O`-decision at the `e'`-scaled type PUSHES FORWARD to an `O'`-decision at `σ'` and
level `e'·N` — the same pointwise law, driven through `scaleType`-injectivity.
Mechanism: every `O'`-lift's reassembly is an `O`-lift of `c`
(`cellTransport_symm_apply`), the `O`-decision types the reassembly, the pointwise law
applied to the reassembly reads `devT (reassT G) = G`, and injectivity converts. -/
theorem transport_decidedAt_of_decidedAt (hCTS : CellTypeScalingAt D)
    (hπ : Irreducible π) (hw : IsLocalRing.residue O w ≠ 0) (he' : 2 ≤ e')
    {N : ℕ} (hDN : D < N) {c : Coeff O (e' * D) N}
    (hF : MinFaceAt c 1 e')
    (hbox : cellTransport hπ hw he' D N c ∈ alphaBox π w e' D (e' * N))
    {σ' : FactorizationType}
    (hdec : DecidedAt O (e' * D) (scaleType e' σ') N c) :
    DecidedAt (AdjoinRoot (eisKey π w e')) D σ' (e' * N)
      (cellTransport hπ hw he' D N c) := by
  intro b hb
  have he'' : 0 < e' := by omega
  -- the reassembly is an `O`-lift of `c`
  have ha : proj O (e' * D) N (reassVec π w (Nat.zero_lt_two.trans_le he') D b) = c := by
    have h1 := cellTransport_symm_apply hπ hw he' D N b
    rw [hb, Equiv.symm_apply_apply] at h1
    exact h1.symm
  -- (i) the raw purity lattice on the reassembled lift
  have hlat := fullSpan_raw_dvd hπ hF ha
  -- (ii) the deep-box divisibilities on the reassembled lift
  have hbox' := (cellTransport_mem_alphaBox_iff hπ hw he' hDN
    (reassVec π w (Nat.zero_lt_two.trans_le he') D b)).mp (by rw [ha]; exact hbox)
  -- the pointwise scaling law at the reassembled lift
  have hscale := hCTS O π w hπ hw e' he'
    (monicPoly (reassVec π w (Nat.zero_lt_two.trans_le he') D b))
    (monicPoly_monic _) (monicPoly_natDegree _)
    (fun j hj => by
      have h1 := hlat j hj
      rwa [one_mul] at h1) hbox'
  -- `monicPoly (reassVec b) = reassT (monicPoly b)`, hence its transform is `monicPoly b`
  have hDpos : 0 < (eisKey π w e').natDegree := by
    rw [eisKey_natDegree he'']
    omega
  obtain ⟨hrmon, hrdeg⟩ := reassT_monic (eisKey_monic (Nat.zero_lt_two.trans_le he'))
    hDpos (monicPoly_monic b) (monicPoly_natDegree b)
  have hrdeg' : (reassT (eisKey π w e') (eisKey_monic (Nat.zero_lt_two.trans_le he')) D
      (monicPoly b)).natDegree = e' * D := by
    rw [hrdeg, eisKey_natDegree he'']
  have hveq : reassVec π w (Nat.zero_lt_two.trans_le he') D b
      = fun i : Fin (e' * D) =>
          (reassT (eisKey π w e') (eisKey_monic (Nat.zero_lt_two.trans_le he')) D
            (monicPoly b)).coeff i.1 := rfl
  have hre : monicPoly (reassVec π w (Nat.zero_lt_two.trans_le he') D b)
      = reassT (eisKey π w e') (eisKey_monic (Nat.zero_lt_two.trans_le he')) D
          (monicPoly b) := by
    rw [hveq]
    exact monicPoly_coeff_self hrmon hrdeg'
  have hkey : devT (eisKey π w e') D
      (monicPoly (reassVec π w (Nat.zero_lt_two.trans_le he') D b)) = monicPoly b := by
    rw [hre]
    exact devT_reassT (eisKey_monic (Nat.zero_lt_two.trans_le he')) hDpos
      (le_of_eq (monicPoly_natDegree b))
  -- the `O`-decision on the reassembly, converted through the law + injectivity
  have hdec' := hdec (reassVec π w (Nat.zero_lt_two.trans_le he') D b) ha
  rw [hscale, hkey] at hdec'
  exact scaleType_injective he'' hdec'

/-- ★★★ **THE TRANSPORT, IFF FORM** — PSL4's precisely-supplied discharge target:
at the full-span frame, the transported class is `σ'`-decided over the recentring ring
at level `e'·N` IF AND ONLY IF the class is `scaleType e' σ'`-decided over the base at
level `N` — conditional on exactly `CellTypeScalingAt D`, uniform in `q, e', D, σ', N`,
every complete DVR. -/
theorem transport_decidedAt_iff (hCTS : CellTypeScalingAt D)
    (hπ : Irreducible π) (hw : IsLocalRing.residue O w ≠ 0) (he' : 2 ≤ e')
    {N : ℕ} (hDN : D < N) {c : Coeff O (e' * D) N}
    (hF : MinFaceAt c 1 e')
    (hbox : cellTransport hπ hw he' D N c ∈ alphaBox π w e' D (e' * N))
    (σ' : FactorizationType) :
    DecidedAt (AdjoinRoot (eisKey π w e')) D σ' (e' * N)
        (cellTransport hπ hw he' D N c)
      ↔ DecidedAt O (e' * D) (scaleType e' σ') N c :=
  ⟨fun hdec => decidedAt_of_transport_decidedAt hCTS hπ hw he' hDN hF hbox hdec,
   fun hdec => transport_decidedAt_of_decidedAt hCTS hπ hw he' hDN hF hbox hdec⟩

end Transport

/-! ## §3 — THE PRIME-MASS FIRE: the full-span power sector is EMPTY at prime mass -/

section PrimeFire

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)] [IsAdicComplete (maximalIdeal O) O]

/-- ★ **Full span forces a composite mass**: a full-span power class factors its mass
as `m = e'·(k·deg ψ)` with `e' ≥ 2` (the face is fractional: `1 ≤ h < e'`) and
`k ≥ 2` (the residual is a PROPER prime power) — so at prime `m` the full-span power
sector is EMPTY, at every level, every centre, every `σ`, every complete DVR. -/
theorem powerSectorFull_eq_empty_of_prime {m : ℕ} (hm : m.Prime) {π : O}
    (hπ : Irreducible π) (σ : FactorizationType) (M : ℕ) :
    powerSectorFull O π m σ M = ∅ := by
  ext c
  simp only [Set.mem_empty_iff_false, iff_false]
  rintro ⟨hc, h, e', hF, hfull⟩
  obtain ⟨h₀, e₀, k, ψ, hF₀, he₀, hψm, hψirr, hψ0, hk, heq, hd1, hle⟩ :=
    powerSector_data σ hπ hc
  obtain ⟨hh, he⟩ := minFaceAt_unique hF hF₀
  subst hh
  subst he
  letI : Field (resField (X : Polynomial O)) := instFieldResField isKey_X
  rw [heq, Polynomial.natDegree_pow] at hfull
  -- `m = e'·(k·deg ψ)`, `e' ≥ 2`, `k ≥ 2`, `deg ψ ≥ 1`: refute primality
  rcases hm.eq_one_or_self_of_dvd e' ⟨k * ψ.natDegree, hfull.symm⟩ with h1 | h1
  · omega
  · have h2 : k * ψ.natDegree = 1 := by
      have h3 : m * (k * ψ.natDegree) = m * 1 := by
        rw [Nat.mul_one]
        rw [h1] at hfull
        exact hfull
      exact Nat.eq_of_mul_eq_mul_left hm.pos h3
    have h4 : k * 1 ≤ k * ψ.natDegree := Nat.mul_le_mul_left k hd1
    rw [Nat.mul_one] at h4
    omega

end PrimeFire

section PrimeFireLaw

/-- ★★★ **THE PRIME-MASS FULL-SPAN LAW, UNCONDITIONAL** — the census fire: at every
prime mass `m` and every `σ`, `PowerFullSpanLaw m σ` holds with the rational pair
`(0, 1)` (the full-span sector is empty, §3's structural emptiness).  On the census
front this removes the full-span premise at the prime ramified-remainder masses
(`m = 5, 7, 11, …`); the composite masses stay behind `CellTypeScalingAt` + the
face/centre assembly. -/
theorem powerFullSpanLaw_of_prime {m : ℕ} (hm : m.Prime) (σ : FactorizationType) :
    PowerFullSpanLaw m σ := by
  refine ⟨0, 1, one_ne_zero, ?_⟩
  intro O _ _ _ _ _
  refine ⟨by simp, ?_⟩
  intro π hπ
  have hval : (((0 : Polynomial ℚ).eval ((residueCard O : ℕ) : ℚ)
      / (1 : Polynomial ℚ).eval ((residueCard O : ℕ) : ℚ) : ℚ) : ℝ) = 0 := by simp
  rw [hval]
  have h0 : Filter.Tendsto (fun _ : ℕ => (0 : ℝ)) Filter.atTop (nhds 0) :=
    tendsto_const_nhds
  refine h0.congr fun M => ?_
  show (0 : ℝ) = (Nat.card (powerSectorFull O π m σ M) : ℝ)
    / ((residueCard O : ℕ) : ℝ) ^ (m * (M + m))
  rw [powerSectorFull_eq_empty_of_prime hm hπ σ M]
  simp

end PrimeFireLaw

end Uniformity.Density.IFCG47

/-! ## Axiom footprint -/

section AxCheck
#print axioms Uniformity.Density.IFCG47.scaleType_degree
#print axioms Uniformity.Density.IFCG47.scaleType_one
#print axioms Uniformity.Density.IFCG47.scaleType_scaleType
#print axioms Uniformity.Density.IFCG47.scaleType_injective
#print axioms Uniformity.Density.IFCG47.decidedAt_of_transport_decidedAt
#print axioms Uniformity.Density.IFCG47.transport_decidedAt_of_decidedAt
#print axioms Uniformity.Density.IFCG47.transport_decidedAt_iff
#print axioms Uniformity.Density.IFCG47.cellTypeScalingAt_one
#print axioms Uniformity.Density.IFCG47.powerSectorFull_eq_empty_of_prime
#print axioms Uniformity.Density.IFCG47.powerFullSpanLaw_of_prime
end AxCheck
