/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import Uniformity.ChapI.IFCG19
import Uniformity.ChapI.IFCG20

/-!
# Uniformity.ChapI.IFCG21 — [ECONE 2026-08-30] the fractional-slope cone census:
THE INTERFACE and the point-law reduction

IFCG18 reduced the all-degree decided slice to TWO kernels; IFCG19 closed the
`e = 1` sector of `SinglePointAggregateLaw`; IFCG20 proved `DeepLinearClusterLaw`
equivalent to its strictly-fractional cell (`DeepFractionalCellLaw`).  Both remaining
objects are fractional-slope Okutsu–Montes cone censuses — "one open heart, two entry
points".  This file names the heart and wires both entry points to it:

* **§1 the point-uniform limit calculus** `PtURLim`: `URLim` families carrying one extra
  monic-irreducible-point parameter, with ONE `Polynomial ℚ` pair uniform over the DVR
  AND the point — closed under constants, `+`, `×`, `Finset` sums.  Point-uniformity is
  the interface-level statement of the unramified base change: every degree-`δ` point
  has the SAME census pair.
* **§2 ★ THE POINT CONE LAW** `PointConeLaw`: for every base degree `δ ≥ 1` and exponent
  `e ≥ 2` with `δ·e ≤ m` — excluding the self-referential `(δ, e) = (1, m)` — the
  normalized per-point stratum census `N ↦ (stratPoly O (δe) N (p^e)) s / q^(δeN)` is a
  point-uniform rational limit family, conditionally on the value laws below `m`.  This
  is the `e ≥ 2` atom: the type-indexed count of decided classes over ONE ramified
  residual point.
* **§3 ★★ THE REDUCTION** `singlePointAggregateLaw_of_pointCone`: `PointConeLaw` fires
  ALL of `SinglePointAggregateLaw` — the per-point block census is the `TypeAlg`
  convolution of its exponent factors (`mul_apply_powerset`, list induction), the `e = 1`
  factors are IFCG19's monomials, the `e ≥ 2` factors are the law's, and the point sum
  collapses through point-uniformity to the irreducible count `N_δ(q)` = IFCG19's
  `necklacePoly`.  With IFCG20, the whole census front reduces to `PointConeLaw` AND
  `DeepFractionalCellLaw`.
* **§4 the centred cone** `zeroConeCount`: the per-centre carrier of IFCG20's fractional
  cell — decided classes in the stratum of `X^m` outside the centre-`0` full recentering
  range — and `CenteredConeLaw`, its value law.  The shift symmetry `fracCellCount =
  q · zeroConeCount` (the translation bijection) is the remaining bridge; its statement
  and stage plan are recorded here and in the unit verdict.

## ⚠ Scoping disposition

`PointConeLaw` and `CenteredConeLaw` are OPEN — they are the named fractional-slope
cone censuses (the campaign's hardest remaining object).  This file adds NO new counting
theorems about them; it proves the REDUCTIONS, so that a future cone-census unit
discharges the whole front at once.  Honesty fences: the `(1, m)` exclusion mirrors the
kernel's `(1, [m])` (the full-mass linear stratum census contains the degree-`m`
self-call); both laws stay conditional on the smaller value laws, so neither is stronger
than the remainder it refines.

## Axiom fence

Lean core everywhere (`propext`, `Classical.choice`, `Quot.sound`); the C.33 cite does
not occur.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.overlappingInstances false

noncomputable section

namespace Uniformity.Density.IFCG21

open IsLocalRing Polynomial
open Uniformity.Density.Induction
open Uniformity.Density.IFCG17
open Uniformity.Density.IFCG18
open Uniformity.Density.IFCG19 (necklacePoly necklacePoly_eval_card
  natCard_irredOfDeg_eq_card_irredFinset stratPoly_irreducible)
open Uniformity.Density.IFCG14 (DecidedValueLaw Witnessed)

attribute [local instance] Classical.propDecidable

/-! ## §1 — the point-uniform rational limit calculus -/

section PtURLim

/-- **A point-uniform rational limit family**: a real sequence for every complete DVR
with finite residue field AND every monic irreducible residual point of degree `δ`,
converging — at EVERY such DVR and EVERY such point — to the value of ONE rational
function of the residue cardinality (one `Polynomial ℚ` pair chosen before the DVR and
the point, with both denominator obligations).  The point-uniformity is the
interface-level unramified base change: all degree-`δ` points share one pair. -/
def PtURLim (δ : ℕ)
    (F : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
      [IsAdicComplete (maximalIdeal O) O] [Finite (ResidueField O)],
      Polynomial (ResidueField O) → ℕ → ℝ) : Prop :=
  ∃ n d : Polynomial ℚ, d ≠ 0 ∧
    ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
      [IsAdicComplete (maximalIdeal O) O] [Finite (ResidueField O)],
      d.eval ((residueCard O : ℕ) : ℚ) ≠ 0 ∧
        ∀ p : Polynomial (ResidueField O), p.Monic → p.natDegree = δ → Irreducible p →
          Filter.Tendsto (F O p) Filter.atTop
            (nhds ((n.eval ((residueCard O : ℕ) : ℚ)
              / d.eval ((residueCard O : ℕ) : ℚ) : ℚ) : ℝ))

theorem PtURLim_const (δ : ℕ) (c : ℚ) :
    PtURLim δ (fun _ _ _ _ _ _ _ _ => (c : ℝ)) := by
  refine ⟨Polynomial.C c, 1, one_ne_zero, ?_⟩
  intro O _ _ _ _ _
  refine ⟨by simp, ?_⟩
  intro p _ _ _
  have hval : ((Polynomial.C c).eval ((residueCard O : ℕ) : ℚ)
      / (1 : Polynomial ℚ).eval ((residueCard O : ℕ) : ℚ) : ℚ) = c := by
    simp
  rw [hval]
  exact tendsto_const_nhds

/-- `PtURLim` transfers along families that agree at all levels `≥ 1` (at every point). -/
theorem PtURLim.congr {δ : ℕ}
    {F G : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
      [IsAdicComplete (maximalIdeal O) O] [Finite (ResidueField O)],
      Polynomial (ResidueField O) → ℕ → ℝ}
    (h : PtURLim δ F)
    (hFG : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
      [IsAdicComplete (maximalIdeal O) O] [Finite (ResidueField O)],
      ∀ p : Polynomial (ResidueField O), p.Monic → p.natDegree = δ → Irreducible p →
        ∀ N, 1 ≤ N → F O p N = G O p N) : PtURLim δ G := by
  obtain ⟨n, d, hd, hval⟩ := h
  refine ⟨n, d, hd, ?_⟩
  intro O _ _ _ _ _
  obtain ⟨hne, hlim⟩ := hval O
  refine ⟨hne, ?_⟩
  intro p hpm hpd hpi
  refine (hlim p hpm hpd hpi).congr' ?_
  filter_upwards [Filter.eventually_ge_atTop 1] with N hN1
  exact hFG O p hpm hpd hpi N hN1

theorem PtURLim.add {δ : ℕ}
    {F G : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
      [IsAdicComplete (maximalIdeal O) O] [Finite (ResidueField O)],
      Polynomial (ResidueField O) → ℕ → ℝ}
    (hF : PtURLim δ F) (hG : PtURLim δ G) :
    PtURLim δ (fun O _ _ _ _ _ p N => F O p N + G O p N) := by
  obtain ⟨n₁, d₁, hd₁, hval₁⟩ := hF
  obtain ⟨n₂, d₂, hd₂, hval₂⟩ := hG
  refine ⟨n₁ * d₂ + d₁ * n₂, d₁ * d₂, mul_ne_zero hd₁ hd₂, ?_⟩
  intro O _ _ _ _ _
  obtain ⟨hne₁, hlim₁⟩ := hval₁ O
  obtain ⟨hne₂, hlim₂⟩ := hval₂ O
  refine ⟨by rw [Polynomial.eval_mul]; exact mul_ne_zero hne₁ hne₂, ?_⟩
  intro p hpm hpd hpi
  have hq : (n₁.eval ((residueCard O : ℕ) : ℚ) / d₁.eval ((residueCard O : ℕ) : ℚ)
        + n₂.eval ((residueCard O : ℕ) : ℚ) / d₂.eval ((residueCard O : ℕ) : ℚ) : ℚ)
      = ((n₁ * d₂ + d₁ * n₂).eval ((residueCard O : ℕ) : ℚ)
          / (d₁ * d₂).eval ((residueCard O : ℕ) : ℚ) : ℚ) := by
    rw [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_mul, Polynomial.eval_mul,
      div_add_div _ _ hne₁ hne₂]
  have hlim := (hlim₁ p hpm hpd hpi).add (hlim₂ p hpm hpd hpi)
  rw [← Rat.cast_add, hq] at hlim
  exact hlim

theorem PtURLim.mul {δ : ℕ}
    {F G : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
      [IsAdicComplete (maximalIdeal O) O] [Finite (ResidueField O)],
      Polynomial (ResidueField O) → ℕ → ℝ}
    (hF : PtURLim δ F) (hG : PtURLim δ G) :
    PtURLim δ (fun O _ _ _ _ _ p N => F O p N * G O p N) := by
  obtain ⟨n₁, d₁, hd₁, hval₁⟩ := hF
  obtain ⟨n₂, d₂, hd₂, hval₂⟩ := hG
  refine ⟨n₁ * n₂, d₁ * d₂, mul_ne_zero hd₁ hd₂, ?_⟩
  intro O _ _ _ _ _
  obtain ⟨hne₁, hlim₁⟩ := hval₁ O
  obtain ⟨hne₂, hlim₂⟩ := hval₂ O
  refine ⟨by rw [Polynomial.eval_mul]; exact mul_ne_zero hne₁ hne₂, ?_⟩
  intro p hpm hpd hpi
  have hq : (n₁.eval ((residueCard O : ℕ) : ℚ) / d₁.eval ((residueCard O : ℕ) : ℚ)
        * (n₂.eval ((residueCard O : ℕ) : ℚ) / d₂.eval ((residueCard O : ℕ) : ℚ)) : ℚ)
      = ((n₁ * n₂).eval ((residueCard O : ℕ) : ℚ)
          / (d₁ * d₂).eval ((residueCard O : ℕ) : ℚ) : ℚ) := by
    rw [Polynomial.eval_mul, Polynomial.eval_mul, div_mul_div_comm]
  have hlim := (hlim₁ p hpm hpd hpi).mul (hlim₂ p hpm hpd hpi)
  rw [← Rat.cast_mul, hq] at hlim
  exact hlim

theorem PtURLim_sum {δ : ℕ} {ι : Type*} (s : Finset ι)
    (F : ι → ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
      [IsAdicComplete (maximalIdeal O) O] [Finite (ResidueField O)],
      Polynomial (ResidueField O) → ℕ → ℝ)
    (h : ∀ i ∈ s, PtURLim δ (F i)) :
    PtURLim δ (fun O _ _ _ _ _ p N => ∑ i ∈ s, F i O p N) := by
  classical
  induction s using Finset.cons_induction with
  | empty =>
      refine (PtURLim_const δ 0).congr ?_
      intro O _ _ _ _ _ p _ _ _ N _
      simp
  | cons a s ha ih =>
      refine ((h a (Finset.mem_cons_self a s)).add
        (ih (fun i hi => h i (Finset.mem_cons_of_mem hi)))).congr ?_
      intro O _ _ _ _ _ p _ _ _ N _
      rw [Finset.sum_cons]

end PtURLim

/-! ## §2 — ★ THE POINT CONE LAW (the fractional-slope census atom) -/

section PointCone

/-- **The per-point stratum census family**: at base degree `δ` and exponent `e`, over a
residual point `p`, the normalized `s`-coefficient of the type-indexed census of the
level-`N` stratum of `p^e` — `stratPoly O (δe) N (p^e) s / q^(δeN)`.  For `e ≥ 2` this is
the fractional-slope Okutsu–Montes cone census over the point `p`. -/
def pointStratFamily (δ e : ℕ) (s : Multiset (ℕ × ℕ)) :
    ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
      [IsAdicComplete (maximalIdeal O) O] [Finite (ResidueField O)],
      Polynomial (ResidueField O) → ℕ → ℝ :=
  fun O _ _ _ _ _ p N =>
    ((stratPoly O (δ * e) N (p ^ e)) s : ℝ) / (residueCard O : ℝ) ^ (δ * e * N)

/-- ★ **THE POINT CONE LAW** — the named fractional-slope cone census, the census
front's ONE open heart at the single-point level.  For every mass window `m ≥ 4`, GIVEN
the decided value laws at all degrees `< m` (the kernel's own conditionality), every base
degree `δ ≥ 1` and exponent `e ≥ 2` with `δ·e ≤ m` — EXCLUDING the self-referential
`(δ, e) = (1, m)` (the full-mass linear stratum census contains the degree-`m`
self-call; it enters only loop-corrected, through `DeepFractionalCellLaw`) — and every
coefficient `s`: the per-point stratum census family is a POINT-UNIFORM rational limit
(one `Polynomial ℚ` pair for the DVR AND the point; point-uniformity is the
interface-level unramified base change).

Open mathematical content (the blueprint's rows): the coefficient classifier over
finite-precision classes (GC0), the `q^(−skeletonExp)` cell measure (RW0), the cone
geometric sums (RW1, landed as formulas), the residual-pattern census instances (FF1),
the unramified base change `q ↦ q^δ` (CL1), and the fractional-slope-forces-ramification
leg (C61's open `ℓ`-half). -/
def PointConeLaw : Prop :=
  ∀ m : ℕ, 4 ≤ m →
    (∀ k, k < m → ∀ σ' : FactorizationType, σ'.degree = k → DecidedValueLaw k σ') →
    ∀ δ e : ℕ, 1 ≤ δ → 2 ≤ e → δ * e ≤ m → ¬(δ = 1 ∧ e = m) →
      ∀ s : Multiset (ℕ × ℕ), PtURLim δ (pointStratFamily δ e s)

/-- **The `e = 1` factor is a point-uniform limit, unconditionally** (IFCG19's monomial
lemma, read per point): the normalized census over any degree-`δ` irreducible point is
the constant `q^(−δ)` at the inert coefficient `{(1, δ)}`, `0` elsewhere. -/
theorem ptURLim_unit_factor (δ : ℕ) (hδ : 1 ≤ δ) (s : Multiset (ℕ × ℕ)) :
    PtURLim δ (pointStratFamily δ 1 s) := by
  by_cases hs : s = ({(1, δ)} : Multiset (ℕ × ℕ))
  · subst hs
    refine ⟨1, Polynomial.X ^ δ, pow_ne_zero δ Polynomial.X_ne_zero, ?_⟩
    intro O _ _ _ _ _
    have hq2 : 2 ≤ residueCard O := two_le_residueCard (O := O)
    have hqQ : ((residueCard O : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    have hqR : ((residueCard O : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    have hden : (Polynomial.X ^ δ : Polynomial ℚ).eval ((residueCard O : ℕ) : ℚ) ≠ 0 := by
      rw [Polynomial.eval_pow, Polynomial.eval_X]
      exact pow_ne_zero δ hqQ
    refine ⟨hden, ?_⟩
    intro p hpm hpd hpi
    have hval : (((1 : Polynomial ℚ).eval ((residueCard O : ℕ) : ℚ)
          / (Polynomial.X ^ δ : Polynomial ℚ).eval ((residueCard O : ℕ) : ℚ) : ℚ) : ℝ)
        = 1 / ((residueCard O : ℕ) : ℝ) ^ δ := by
      rw [Polynomial.eval_one, Polynomial.eval_pow, Polynomial.eval_X]
      push_cast
      ring
    rw [hval]
    refine Filter.Tendsto.congr' ?_ tendsto_const_nhds
    filter_upwards [Filter.eventually_ge_atTop 1] with N hN
    unfold pointStratFamily
    simp only [Nat.mul_one, pow_one]
    rw [stratPoly_irreducible (by omega) hN hpm hpd hpi, AddMonoidAlgebra.single_apply,
      if_pos rfl]
    have hexp : δ * N = δ * (N - 1) + δ := by
      calc δ * N = δ * ((N - 1) + 1) := by rw [Nat.sub_add_cancel hN]
        _ = δ * (N - 1) + δ := by ring
    rw [hexp, pow_add]
    push_cast
    rw [div_eq_div_iff (pow_ne_zero _ hqR)
      (mul_ne_zero (pow_ne_zero _ hqR) (pow_ne_zero _ hqR))]
    ring
  · refine ⟨0, 1, one_ne_zero, ?_⟩
    intro O _ _ _ _ _
    refine ⟨by simp, ?_⟩
    intro p hpm hpd hpi
    have hq2 : 2 ≤ residueCard O := two_le_residueCard (O := O)
    have hzero : (((0 : Polynomial ℚ).eval ((residueCard O : ℕ) : ℚ)
        / (1 : Polynomial ℚ).eval ((residueCard O : ℕ) : ℚ) : ℚ) : ℝ) = 0 := by simp
    rw [hzero]
    refine Filter.Tendsto.congr' ?_ tendsto_const_nhds
    filter_upwards [Filter.eventually_ge_atTop 1] with N hN
    unfold pointStratFamily
    simp only [Nat.mul_one, pow_one]
    rw [stratPoly_irreducible (by omega) hN hpm hpd hpi, AddMonoidAlgebra.single_apply,
      if_neg (fun hcon => hs hcon.symm), Rat.cast_zero, zero_div]

end PointCone

/-! ## §3 — ★★ THE REDUCTION: the point cone law fires the single-point kernel -/

section Reduction

/-- Pointwise evaluation of `TypeAlg` finset sums (IFCG18 §0's private helper,
re-proved). -/
private theorem typeAlg_sum_apply {ι : Type*} (S : Finset ι) (f : ι → TypeAlg)
    (t : Multiset (ℕ × ℕ)) : (∑ i ∈ S, f i) t = ∑ i ∈ S, f i t := by
  classical
  induction S using Finset.cons_induction with
  | empty => rw [Finset.sum_empty, Finset.sum_empty]; rfl
  | cons a s ha ih => rw [Finset.sum_cons, Finset.sum_cons, ← ih]; rfl

/-- **The normalized per-point block census family** of an exponent list: the
`s`-coefficient of `blockPoly` (the product of the per-exponent stratum censuses at ONE
point), normalized at the block's mass. -/
def pointBlockFamily (δ : ℕ) (E : List ℕ) (s : Multiset (ℕ × ℕ)) :
    ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
      [IsAdicComplete (maximalIdeal O) O] [Finite (ResidueField O)],
      Polynomial (ResidueField O) → ℕ → ℝ :=
  fun O _ _ _ _ _ p N =>
    ((blockPoly O N δ p E) s : ℝ) / (residueCard O : ℝ) ^ (δ * E.sum * N)

/-- **The block convolution**: if every exponent factor is a point-uniform limit at every
coefficient, so is the block family — list induction through the `TypeAlg` convolution
`mul_apply_powerset` (no coprimality: the factors share the point). -/
theorem ptURLim_blockPoly (δ : ℕ) (E : List ℕ)
    (hfac : ∀ e ∈ E, ∀ s' : Multiset (ℕ × ℕ), PtURLim δ (pointStratFamily δ e s')) :
    ∀ s : Multiset (ℕ × ℕ), PtURLim δ (pointBlockFamily δ E s) := by
  induction E with
  | nil =>
      intro s
      refine (PtURLim_const δ (if (0 : Multiset (ℕ × ℕ)) = s then 1 else 0)).congr ?_
      intro O _ _ _ _ _ p hpm hpd hpi N hN
      unfold pointBlockFamily
      have hb : blockPoly O N δ p [] = (1 : TypeAlg) := by
        simp [blockPoly]
      rw [hb, AddMonoidAlgebra.one_def, AddMonoidAlgebra.single_apply]
      simp only [List.sum_nil, Nat.mul_zero, Nat.zero_mul, pow_zero, div_one]
  | cons e E' ih =>
      intro s
      have hhead : ∀ s' : Multiset (ℕ × ℕ), PtURLim δ (pointStratFamily δ e s') :=
        fun s' => hfac e List.mem_cons_self s'
      have htail : ∀ s' : Multiset (ℕ × ℕ), PtURLim δ (pointBlockFamily δ E' s') :=
        ih (fun e' he' s' => hfac e' (List.mem_cons_of_mem e he') s')
      refine (PtURLim_sum s.powerset.toFinset
        (fun s' O _ _ _ _ _ p N =>
          pointStratFamily δ e s' O p N * pointBlockFamily δ E' (s - s') O p N)
        (fun s' _ => (hhead s').mul (htail (s - s')))).congr ?_
      intro O _ _ _ _ _ p hpm hpd hpi N hN
      unfold pointBlockFamily pointStratFamily
      have hb : blockPoly O N δ p (e :: E')
          = stratPoly O (δ * e) N (p ^ e) * blockPoly O N δ p E' := by
        simp [blockPoly]
      have hL : ((blockPoly O N δ p (e :: E')) s : ℝ)
          = ∑ s' ∈ s.powerset.toFinset,
              ((stratPoly O (δ * e) N (p ^ e)) s' : ℝ)
                * ((blockPoly O N δ p E') (s - s') : ℝ) := by
        rw [hb, mul_apply_powerset]
        push_cast
        rfl
      have hexp : δ * (e :: E').sum * N = δ * e * N + δ * E'.sum * N := by
        rw [List.sum_cons]
        ring
      rw [hL, hexp, pow_add, Finset.sum_div]
      refine Finset.sum_congr rfl fun s' _ => ?_
      rw [div_mul_div_comm]

/-- **The point-sum collapse**: a point-uniform block limit assembles to `URLim` of the
single-point aggregate family — the aggregate is the sum of the per-point families over
the degree-`δ` irreducible bank, each tending to the SAME pair value (point-uniformity),
so the limit is `N_δ(q)` times it, and `N_δ` is IFCG19's `necklacePoly`. -/
theorem uRLim_spFamily_of_ptURLim {δ : ℕ} (hδ : 1 ≤ δ) {E : List ℕ}
    {s : Multiset (ℕ × ℕ)} (h : PtURLim δ (pointBlockFamily δ E s)) :
    URLim (spFamily ⟨δ, E⟩ s) := by
  obtain ⟨n, d, hd, hval⟩ := h
  refine ⟨necklacePoly δ * n, d, hd, ?_⟩
  intro O _ _ _ _ _
  obtain ⟨hne, hlim⟩ := hval O
  refine ⟨hne, ?_⟩
  letI : Fintype (ResidueField O) := Fintype.ofFinite (ResidueField O)
  have hqcard : residueCard O = Fintype.card (ResidueField O) := Nat.card_eq_fintype_card
  have hcount : (necklacePoly δ).eval ((residueCard O : ℕ) : ℚ)
      = ((irredFinset (ResidueField O) δ).card : ℚ) := by
    rw [hqcard, necklacePoly_eval_card (ResidueField O) δ hδ,
      natCard_irredOfDeg_eq_card_irredFinset]
  have hpt : ∀ p ∈ irredFinset (ResidueField O) δ,
      Filter.Tendsto (pointBlockFamily δ E s O p) Filter.atTop
        (nhds ((n.eval ((residueCard O : ℕ) : ℚ)
          / d.eval ((residueCard O : ℕ) : ℚ) : ℚ) : ℝ)) := by
    intro p hp
    obtain ⟨hpm, hpd, hpi⟩ := mem_irredFinset_iff.mp hp
    exact hlim p hpm hpd hpi
  have hsum := tendsto_finsetSum (irredFinset (ResidueField O) δ) hpt
  rw [Finset.sum_const, nsmul_eq_mul] at hsum
  have hvalue : ((((necklacePoly δ * n).eval ((residueCard O : ℕ) : ℚ)
        / d.eval ((residueCard O : ℕ) : ℚ)) : ℚ) : ℝ)
      = ((irredFinset (ResidueField O) δ).card : ℝ)
          * ((n.eval ((residueCard O : ℕ) : ℚ)
            / d.eval ((residueCard O : ℕ) : ℚ) : ℚ) : ℝ) := by
    rw [Polynomial.eval_mul, hcount]
    push_cast
    ring
  rw [hvalue]
  refine hsum.congr fun N => ?_
  have hagg : SPAgg O N ⟨δ, E⟩ ∅
      = ∑ p ∈ irredFinset (ResidueField O) δ, blockPoly O N δ p E := by
    rw [SPAgg, Finset.sdiff_empty]
  unfold spFamily pointBlockFamily
  rw [hagg, typeAlg_sum_apply]
  push_cast
  rw [Finset.sum_div]
  rfl

/-- A positive-entry list summing within `m` that contains `m` IS `[m]`. -/
private theorem list_eq_singleton_of_mem_sum_le {E : List ℕ} {m : ℕ}
    (hpos : ∀ e ∈ E, 1 ≤ e) (hsum : E.sum ≤ m) (hmem : m ∈ E) :
    E = [m] := by
  obtain ⟨A, B, rfl⟩ := List.append_of_mem hmem
  have hsplit : A.sum + (m + B.sum) ≤ m := by
    rw [← List.sum_cons, ← List.sum_append]
    exact hsum
  have hA0 : A.sum = 0 := by omega
  have hB0 : B.sum = 0 := by omega
  have hA : A = [] := by
    cases A with
    | nil => rfl
    | cons a A' =>
        have ha : 1 ≤ a := hpos a (by simp)
        rw [List.sum_cons] at hA0
        omega
  have hB : B = [] := by
    cases B with
    | nil => rfl
    | cons b B' =>
        have hb : 1 ≤ b := hpos b (by simp)
        rw [List.sum_cons] at hB0
        omega
  rw [hA, hB, List.nil_append]

/-- ★★ **THE REDUCTION**: the point cone law fires the WHOLE single-point kernel.  Every
factor of a legal block is either an `e = 1` monomial (IFCG19, unconditional) or an
`e ≥ 2` cone census within the law's window — the `(1, m)` factor shape is unreachable
outside the excluded block `(1, [m])` — and the block convolution plus the point-sum
collapse assemble the `URLim` pair. -/
theorem singlePointAggregateLaw_of_pointCone (hPC : PointConeLaw) :
    SinglePointAggregateLaw := by
  intro m hm hsm b hδ hEne hE1 hmass hdeep s
  obtain ⟨δ, E⟩ := b
  replace hδ : 1 ≤ δ := hδ
  replace hE1 : ∀ e ∈ E, 1 ≤ e := hE1
  replace hdeep : ¬(δ = 1 ∧ E = [m]) := hdeep
  have hmass' : δ * E.sum ≤ m := hmass
  have hfac : ∀ e ∈ E, ∀ s' : Multiset (ℕ × ℕ), PtURLim δ (pointStratFamily δ e s') := by
    intro e heE s'
    rcases Nat.lt_or_ge e 2 with he1 | he2
    · have he : e = 1 := by
        have := hE1 e heE
        omega
      subst he
      exact ptURLim_unit_factor δ hδ s'
    · have hesum : e ≤ E.sum := List.single_le_sum (fun x _ => Nat.zero_le x) e heE
      have hδe : δ * e ≤ m := le_trans (Nat.mul_le_mul_left δ hesum) hmass'
      have hexcl : ¬(δ = 1 ∧ e = m) := by
        rintro ⟨hδ1, hem⟩
        subst hδ1
        subst hem
        refine hdeep ⟨rfl, ?_⟩
        exact list_eq_singleton_of_mem_sum_le hE1 (by omega) heE
      exact hPC m hm hsm δ e hδ he2 hδe hexcl s'
  exact uRLim_spFamily_of_ptURLim hδ (ptURLim_blockPoly δ E hfac s)

/-- ★★ **THE CAPSTONE REDUCTION, cone form**: the point cone law and the fractional cell
law — the two named fractional-slope censuses — fire the all-degree decided slice. -/
theorem decidedSliceAt_all_of_pointCone_fractional (hPC : PointConeLaw)
    (hDF : Uniformity.Density.IFCG20.DeepFractionalCellLaw) :
    ∀ n : ℕ, Uniformity.Density.DecidedSliceAt n :=
  Uniformity.Density.IFCG20.decidedSliceAt_all_of_singlePoint_fractional
    (singlePointAggregateLaw_of_pointCone hPC) hDF

end Reduction

/-! ## §4 — the centred cone and the fractional-cell reduction -/

section CenteredCone

open UniqueFactorizationMonoid
open Uniformity.Density.IFCG1 (MBoxN)
open Uniformity.Density.IFCG15 (nonloopDecidedSet loopClassN)
open Uniformity.Density.IFCG20 (fracCellCount fullLoopClassN DeepFractionalCellLaw
  range_loopClassN_subset_fullRange)

/-- **The deep-pattern classification**: a monic polynomial with primary pattern
`{(1, m)}`, `m ≥ 1`, is a linear power `(X + C γ)^m` — one distinct normalized factor,
linear, with multiplicity `m`. -/
theorem eq_addC_pow_of_patternOf {K : Type*} [Field K] {m : ℕ} (hm : 1 ≤ m)
    {f : Polynomial K} (hf : f.Monic)
    (hpat : patternOf f = ({(1, m)} : Multiset (ℕ × ℕ))) :
    ∃ γ : K, f = (X + C γ) ^ m := by
  classical
  have hfne : f ≠ 0 := hf.ne_zero
  -- the factor set is a singleton
  have hcard1 : (normalizedFactors f).toFinset.val.card = 1 := by
    have hc := congrArg Multiset.card hpat
    rw [patternOf, Multiset.card_map] at hc
    simpa using hc
  obtain ⟨ℓ, hℓ⟩ := Multiset.card_eq_one.mp hcard1
  -- read the pattern entry
  have hentry : ((ℓ.natDegree, (normalizedFactors f).count ℓ) : ℕ × ℕ) = ((1 : ℕ), m) := by
    have hp := hpat
    rw [patternOf, hℓ, Multiset.map_singleton, Multiset.singleton_inj] at hp
    exact hp
  simp only [Prod.mk.injEq] at hentry
  obtain ⟨hdeg, hcount⟩ := hentry
  -- every factor is ℓ
  have hmem : ∀ x ∈ normalizedFactors f, x = ℓ := by
    intro x hx
    have hxT : x ∈ (normalizedFactors f).toFinset.val :=
      Finset.mem_def.mp (Multiset.mem_toFinset.mpr hx)
    rw [hℓ, Multiset.mem_singleton] at hxT
    exact hxT
  -- the factor multiset is `replicate m ℓ`
  have hcards : (normalizedFactors f).card = m := by
    rw [← hcount]
    exact (Multiset.count_eq_card.mpr (fun x hx => (hmem x hx).symm)).symm
  have hrep : normalizedFactors f = Multiset.replicate m ℓ := by
    rw [← hcards]
    exact Multiset.eq_replicate_card.mpr hmem
  -- ℓ is monic of degree one
  have hℓmem : ℓ ∈ normalizedFactors f := by
    refine Multiset.count_pos.mp ?_
    omega
  obtain ⟨hℓirr, hℓnorm, -⟩ := (mem_normalizedFactors_iff' hfne).mp hℓmem
  have hℓmonic : ℓ.Monic := by
    rw [← hℓnorm]
    exact monic_normalize hℓirr.ne_zero
  have hγ : ℓ = X + C (ℓ.coeff 0) := hℓmonic.eq_X_add_C hdeg
  refine ⟨ℓ.coeff 0, ?_⟩
  calc f = (normalizedFactors f).prod := (prod_normalizedFactors_of_monic hf).symm
    _ = ℓ ^ m := by rw [hrep, Multiset.prod_replicate]
    _ = (X + C (ℓ.coeff 0)) ^ m := by rw [← hγ]

/-- **Centre injectivity**: equal linear powers share the centre (characteristic-free:
evaluate at `−γ`). -/
theorem addC_pow_centre_inj {K : Type*} [Field K] {m : ℕ} (hm : 1 ≤ m)
    {γ γ' : K} (h : ((X + C γ) ^ m : Polynomial K) = (X + C γ') ^ m) : γ = γ' := by
  have hev := congrArg (Polynomial.eval (-γ)) h
  simp only [Polynomial.eval_pow, Polynomial.eval_add, Polynomial.eval_X,
    Polynomial.eval_C, neg_add_cancel] at hev
  have hz : (-γ + γ' : K) = 0 := by
    have hzero : ((0 : K)) ^ m = 0 := zero_pow (by omega)
    rw [hzero] at hev
    exact (pow_eq_zero_iff (by omega)).mp hev.symm
  exact neg_add_eq_zero.mp hz

/-- Counting bridge (IFCG18 §0's private helper, re-proved). -/
private theorem natCard_set_eq_card_filter {α : Type*} [Fintype α] (s : Set α) :
    Nat.card s = (Finset.univ.filter (fun a => a ∈ s)).card := by
  rw [Nat.card_coe_set_eq, ← Set.ncard_coe_finset (Finset.univ.filter (fun a => a ∈ s))]
  congr 1
  ext a
  simp

/-- Fibre partition of a set count (IFCG18 §0's private helper, re-proved). -/
private theorem natCard_eq_sum_fiber {α β : Type*} [Fintype α] (s : Set α) (φ : α → β)
    (T : Finset β) (hT : ∀ a ∈ s, φ a ∈ T) :
    Nat.card s = ∑ b ∈ T, Nat.card ((s ∩ φ ⁻¹' {b} : Set α)) := by
  rw [natCard_set_eq_card_filter,
    Finset.card_eq_sum_card_fiberwise (f := φ) (t := T)
      (fun a ha => hT a (by simpa using (Finset.mem_filter.1 ha).2))]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [natCard_set_eq_card_filter, Finset.filter_filter]
  congr 1
  ext a
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Set.mem_inter_iff,
    Set.mem_preimage, Set.mem_singleton_iff]

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)]

/-- **The centred cone cell count**: the `σ`-decided classes in the stratum of
`(X + C γ)^m` that lie OUTSIDE the centre-`γ` full recentering range — the per-centre
carrier of IFCG20's fractional cell.  Mathematically: the deep classes over the centre
`γ` whose recentred Newton polygon shows a visibly fractional slope. -/
def coneCellCount (O : Type*) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Finite (ResidueField O)] (π : O) (m : ℕ) (σ : FactorizationType) (M : ℕ)
    (γ : ResidueField O) : ℕ :=
  Nat.card (((decidedSet O m σ (M + m)
      ∩ levelZeroStratum O m (M + m) ((X + C γ) ^ m))
    \ Set.range (fun d : MBoxN O m M => fullLoopClassN π (γ, d))) : Set (Coeff O m (M + m)))

/-- ★ **THE CENTRED CONE LAW** — the fractional cell's per-centre value law, in the
kernel's verbatim conditional shape, CENTRE-UNIFORM (one `Polynomial ℚ` pair for the DVR,
the uniformizer, AND the centre — the translation symmetry stated at the interface
level, exactly as `PtURLim` states the base change). -/
def CenteredConeLaw : Prop :=
  ∀ m : ℕ, 4 ≤ m →
    (∀ k, k < m → ∀ σ' : FactorizationType, σ'.degree = k → DecidedValueLaw k σ') →
    ∀ σ : FactorizationType, σ.degree = m → Witnessed m σ →
      ∃ n d : Polynomial ℚ, d ≠ 0 ∧
        ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
          [IsAdicComplete (maximalIdeal O) O] [Finite (ResidueField O)],
          d.eval ((residueCard O : ℕ) : ℚ) ≠ 0 ∧
            ∀ π : O, Irreducible π → ∀ γ : ResidueField O,
              Filter.Tendsto
                (fun M => (coneCellCount O π m σ M γ : ℝ)
                  / (residueCard O : ℝ) ^ (m * (M + m)))
                Filter.atTop
                (nhds ((n.eval ((residueCard O : ℕ) : ℚ)
                  / d.eval ((residueCard O : ℕ) : ℚ) : ℚ) : ℝ))

/-- The centre read off a class (junk value `0` off the deep cell). -/
noncomputable def centreOf (O : Type*) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] (m N : ℕ) (c : Coeff O m N) : ResidueField O :=
  if h : ∃ γ : ResidueField O, stratumPoly O m N c = (X + C γ) ^ m then h.choose else 0

theorem centreOf_eq {m N : ℕ} (hm : 1 ≤ m) {c : Coeff O m N} {γ : ResidueField O}
    (hc : stratumPoly O m N c = (X + C γ) ^ m) : centreOf O m N c = γ := by
  have hex : ∃ γ' : ResidueField O, stratumPoly O m N c = (X + C γ') ^ m := ⟨γ, hc⟩
  rw [centreOf, dif_pos hex]
  exact addC_pow_centre_inj hm (hex.choose_spec.symm.trans hc)

/-- Every full-recentring lands in the stratum of its centre's linear power (IFCG20 §1's
inline fact, exported). -/
theorem fullLoopClassN_mem_stratum {π : O} (hπ : Irreducible π) {m M : ℕ} (hm : 1 ≤ m)
    (p : ResidueField O × MBoxN O m M) :
    fullLoopClassN π p ∈ levelZeroStratum O m (M + m) ((X + C p.1) ^ m) := by
  rw [mem_levelZeroStratum_iff (by omega)]
  exact ⟨Uniformity.Density.IFCG3.loopMapN p.1 π p.2, rfl,
    Uniformity.Density.IFCG3.map_residue_monicPoly_loopMapN hπ p.1 p.2⟩

/-- ★ **THE CENTRE PARTITION**: the fractional cell splits EXACTLY over the centres —
the loop subtraction is absorbed (the constrained loop range sits inside the full range),
the deep pattern cell is classified by `eq_addC_pow_of_patternOf`, distinct centres have
disjoint strata, and each centre's full-range piece is exactly its own recentering
range. -/
theorem fracCellCount_eq_sum_coneCellCount [Fintype (ResidueField O)] {π : O}
    (hπ : Irreducible π) {m : ℕ} (hm : 1 ≤ m) (σ : FactorizationType) (M : ℕ) :
    fracCellCount O π m σ M = ∑ γ : ResidueField O, coneCellCount O π m σ M γ := by
  haveI : Fintype (Coeff O m (M + m)) := Fintype.ofFinite _
  -- STEP 0: absorb the loop subtraction into the full-range removal
  have hset : ((nonloopDecidedSet π m σ M
        ∩ {c | patternOf (stratumPoly O m (M + m) c) = ({(1, m)} : Multiset (ℕ × ℕ))})
        \ Set.range (fullLoopClassN π (m := m) (M := M)) : Set (Coeff O m (M + m)))
      = ((decidedSet O m σ (M + m)
          ∩ {c | patternOf (stratumPoly O m (M + m) c) = ({(1, m)} : Multiset (ℕ × ℕ))})
          \ Set.range (fullLoopClassN π (m := m) (M := M))) := by
    ext c
    simp only [nonloopDecidedSet, Set.mem_sdiff, Set.mem_inter_iff, Set.mem_setOf_eq]
    constructor
    · rintro ⟨⟨⟨hD, -⟩, hP⟩, hF⟩
      exact ⟨⟨hD, hP⟩, hF⟩
    · rintro ⟨⟨hD, hP⟩, hF⟩
      exact ⟨⟨⟨hD, fun hL => hF (range_loopClassN_subset_fullRange hL)⟩, hP⟩, hF⟩
  -- STEP 1: fibre the decided deep cell over the centre
  have hpart := natCard_eq_sum_fiber
    (((decidedSet O m σ (M + m)
        ∩ {c | patternOf (stratumPoly O m (M + m) c) = ({(1, m)} : Multiset (ℕ × ℕ))})
        \ Set.range (fullLoopClassN π (m := m) (M := M))) : Set (Coeff O m (M + m)))
    (fun c => centreOf O m (M + m) c) Finset.univ (fun c _ => Finset.mem_univ _)
  -- STEP 2: each fibre is the centre's cone cell
  have hfiber : ∀ γ : ResidueField O,
      ((((decidedSet O m σ (M + m)
          ∩ {c | patternOf (stratumPoly O m (M + m) c) = ({(1, m)} : Multiset (ℕ × ℕ))})
          \ Set.range (fullLoopClassN π (m := m) (M := M)))
        ∩ (fun c => centreOf O m (M + m) c) ⁻¹' {γ}) : Set (Coeff O m (M + m)))
      = ((decidedSet O m σ (M + m)
          ∩ levelZeroStratum O m (M + m) ((X + C γ) ^ m))
          \ Set.range (fun d : MBoxN O m M => fullLoopClassN π (γ, d))) := by
    intro γ
    ext c
    simp only [Set.mem_inter_iff, Set.mem_sdiff, Set.mem_setOf_eq, Set.mem_preimage,
      Set.mem_singleton_iff, Set.mem_range]
    constructor
    · rintro ⟨⟨⟨hD, hP⟩, hF⟩, hγ⟩
      obtain ⟨γ', hγ'⟩ := eq_addC_pow_of_patternOf hm (stratumPoly_monic c) hP
      have hγγ : γ' = γ := (centreOf_eq hm hγ').symm.trans hγ
      subst hγγ
      refine ⟨⟨hD, (mem_levelZeroStratum_iff_stratumPoly (by omega) _ c).mpr hγ'⟩, ?_⟩
      rintro ⟨d, hd⟩
      exact hF ⟨(γ', d), hd⟩
    · rintro ⟨⟨hD, hS⟩, hR⟩
      have hsp : stratumPoly O m (M + m) c = (X + C γ) ^ m := stratumPoly_eq_of_mem hS
      refine ⟨⟨⟨hD, ?_⟩, ?_⟩, centreOf_eq hm hsp⟩
      · rw [hsp]
        exact patternOf_addC_pow γ hm
      · rintro ⟨pp, hfull⟩
        have hspp : stratumPoly O m (M + m) c = (X + C pp.1) ^ m := by
          rw [← hfull]
          exact stratumPoly_eq_of_mem (fullLoopClassN_mem_stratum hπ hm pp)
        have hcen : pp.1 = γ := addC_pow_centre_inj hm (by rw [← hspp, ← hsp])
        refine hR ⟨pp.2, ?_⟩
        rw [← hcen]
        exact hfull
  -- assemble
  calc fracCellCount O π m σ M
      = Nat.card (((decidedSet O m σ (M + m)
          ∩ {c | patternOf (stratumPoly O m (M + m) c) = ({(1, m)} : Multiset (ℕ × ℕ))})
          \ Set.range (fullLoopClassN π (m := m) (M := M))) : Set (Coeff O m (M + m))) := by
        rw [fracCellCount, hset]
    _ = ∑ γ ∈ Finset.univ, Nat.card
          ((((decidedSet O m σ (M + m)
            ∩ {c | patternOf (stratumPoly O m (M + m) c) = ({(1, m)} : Multiset (ℕ × ℕ))})
            \ Set.range (fullLoopClassN π (m := m) (M := M)))
            ∩ (fun c => centreOf O m (M + m) c) ⁻¹' {γ}) : Set (Coeff O m (M + m))) :=
        hpart
    _ = ∑ γ : ResidueField O, coneCellCount O π m σ M γ := by
        refine Finset.sum_congr rfl fun γ _ => ?_
        rw [hfiber γ]
        rfl

/-- ★★ **THE FRACTIONAL-CELL REDUCTION**: the centred cone law fires
`DeepFractionalCellLaw` — the fractional cell is the centre partition's sum, every
centre tends to the SAME pair value (centre-uniformity), and the `q` centres contribute
the factor `X`. -/
theorem deepFractionalCellLaw_of_centeredCone (hCC : CenteredConeLaw) :
    DeepFractionalCellLaw := by
  intro m hm hsm σ hσ hwit
  obtain ⟨n, d, hd, hval⟩ := hCC m hm hsm σ hσ hwit
  refine ⟨Polynomial.X * n, d, hd, ?_⟩
  intro O _ _ _ _ _
  obtain ⟨hne, hlim⟩ := hval O
  refine ⟨hne, ?_⟩
  intro π hπ
  letI : Fintype (ResidueField O) := Fintype.ofFinite (ResidueField O)
  have hsum := tendsto_finsetSum (Finset.univ : Finset (ResidueField O))
    (fun γ _ => hlim π hπ γ)
  rw [Finset.sum_const, nsmul_eq_mul] at hsum
  have hqcard : ((Finset.univ : Finset (ResidueField O)).card : ℝ)
      = ((residueCard O : ℕ) : ℝ) := by
    rw [Finset.card_univ]
    norm_cast
    exact (Nat.card_eq_fintype_card (α := ResidueField O)).symm
  have hvalue : (((Polynomial.X * n).eval ((residueCard O : ℕ) : ℚ)
        / d.eval ((residueCard O : ℕ) : ℚ) : ℚ) : ℝ)
      = ((Finset.univ : Finset (ResidueField O)).card : ℝ)
          * ((n.eval ((residueCard O : ℕ) : ℚ)
            / d.eval ((residueCard O : ℕ) : ℚ) : ℚ) : ℝ) := by
    rw [hqcard, Polynomial.eval_mul, Polynomial.eval_X]
    push_cast
    ring
  rw [hvalue]
  refine hsum.congr fun M => ?_
  rw [fracCellCount_eq_sum_coneCellCount hπ (by omega) σ M]
  push_cast
  rw [Finset.sum_div]

/-- ★★★ **THE TWO-CONE CAPSTONE**: the point cone law and the centred cone law — the two
faces of the ONE fractional-slope census heart — fire the all-degree decided slice.
The census front's remaining open content is exactly these two `Prop`s. -/
theorem decidedSliceAt_all_of_cones (hPC : PointConeLaw) (hCC : CenteredConeLaw) :
    ∀ n : ℕ, Uniformity.Density.DecidedSliceAt n :=
  decidedSliceAt_all_of_pointCone_fractional hPC
    (deepFractionalCellLaw_of_centeredCone hCC)

end CenteredCone

end Uniformity.Density.IFCG21

end

/-! ## AXCHECK FOOTER — expect Lean core `{propext, Classical.choice, Quot.sound}`
everywhere; the C.33 cite must NOT occur. -/

#print axioms Uniformity.Density.IFCG21.ptURLim_unit_factor
#print axioms Uniformity.Density.IFCG21.ptURLim_blockPoly
#print axioms Uniformity.Density.IFCG21.uRLim_spFamily_of_ptURLim
#print axioms Uniformity.Density.IFCG21.singlePointAggregateLaw_of_pointCone
#print axioms Uniformity.Density.IFCG21.decidedSliceAt_all_of_pointCone_fractional
#print axioms Uniformity.Density.IFCG21.eq_addC_pow_of_patternOf
#print axioms Uniformity.Density.IFCG21.addC_pow_centre_inj
#print axioms Uniformity.Density.IFCG21.centreOf_eq
#print axioms Uniformity.Density.IFCG21.fullLoopClassN_mem_stratum
#print axioms Uniformity.Density.IFCG21.fracCellCount_eq_sum_coneCellCount
#print axioms Uniformity.Density.IFCG21.deepFractionalCellLaw_of_centeredCone
#print axioms Uniformity.Density.IFCG21.decidedSliceAt_all_of_cones
