/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import Uniformity.ChapI.IFCG63

/-!
# Uniformity.ChapI.IFCG65 — [PSP 2026-08-31] the primary-shape Weierstrass peel:
DGT route step (c), the `e = 1` case and the peel recursion

Stage PSP of the cone census (design record `runs/wave-c/verdict_PSP.md`).  DGT's
IFCG63 made the diagonal reduced census a sum over residual factor shapes
(`card_redDepthPairSet_eq_sum_strata` + `card_stratumDepthSet_mul`); the named
remainder was the PRIMARY-shape values `#stratumDepthSet(n, N, v, r^e)` for `r`
irreducible residual of degree `δ` (`δe = n`).  THIS file lands the primary values:

* **§0 the residue-reading kit**: `resMap` (the level-`N` → residue-field ring map),
  `resVec`/`map_polyOf` (residual coefficient vectors), the stratum membership reader
  `mem_levelZeroStratum_iff_monicPoly_resVec`, the `resOrd` complements
  (`resOrd_mk_pow`, `resOrd_isUnit_mul`, the `resMap_eq_zero_iff` reader), and the
  fibre-counting workhorse `card_preimage_of_subset_range`.
* **§1 the two peel legs at a general monic residual `g`**:
  `resOrd_redRes_eq_zero_of_coprime` — a box with residual coprime to the frame's
  residual has reduced-resultant depth 0 (the resultant reads through `resMap` by
  `resultant_map_map`, and a coprime resultant over the residue field is nonzero);
  `redRes_scaleBox` — scaling the box by `π` multiplies the reduced resultant by
  `π^n` (`resultant_C_mul_right`), the finite-level Weierstrass π-pullout.
* **§2 ★★ the `e = 1` primary law**: at an irreducible residual `r` of degree `δ`,
  the per-frame depth census is the `(1,1)` law at scale `q^δ`:
  `#frameDepthSet(δ, N, v, c) = (q^δ − 1)·q^{δ(N − v/δ − 1)}` if `δ ∣ v` else `0`
  (`v < N`), and the stratum census is `q^{δ(N−1)}` times that
  (`card_stratumDepthSet_irreducible`).
* **§3 the peel recursion at `e ≥ 2`** (the content decomposition): the box
  partitions by the `r`-adic content of its residual; the content-`j` piece is the
  bijective image of (monic `r^j`-stratum) × (`r`-coprime box); the census reads
  through the swap + division to the exponent-`j` stratum census at depth `v − δj`.
* **§4 the closed form**: the `ℕ`-valued `primo` recursion and
  `#stratumDepthSet(δe, N, v, r^e) · q^{v+δe} = primo(e,v) · q^{δe(2N−1)}` — every
  primary value is a FINITE computation, uniform in `q`, `N`-free after normalizing.

## THE HONEST FENCE

The Euler/zeta assembly (route step (d)) is NOT here: summing IFCG63's shape
partition over all residual shapes to `[t^v]Z_n · q^{2nN}` requires grouping shapes
by factorization type and the `F_q[x]` irreducible counts (Gauss/necklace values) —
the shape count grows with `q`, so per-`n` this is a genuine (finite, but
`q`-uniform-input) assembly.  Consequently the `ZcURLim` premise of IFCG61's
`zcURLim_depthDensity_of_reduced` at `n ≥ 2` is NOT yet fired here.

## Axiom fence (machine-exact at landing)

EVERY row of the AxCheck footer expects PURE Lean core
`{propext, Classical.choice, Quot.sound}`.  B.42, the C.33 cites, and
`AX_cellRecursion` must NOT occur.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

noncomputable section

namespace Uniformity.Density.IFCG65

open IsLocalRing Polynomial
open Uniformity.Density.Induction
open Uniformity.Density.IFCG61 (polyOf polyOf_coeff_lt polyOf_degree_lt polyOf_eq_self
  redRes redDepthPairSet)
open Uniformity.Density.IFCG63 (frameDepthSet stratumDepthSet resOrd_mul
  resOrd_mul_eq_iff resultant_modByMonic_right card_stratumDepthSet_eq_sum
  polyOf_eq_self_of_degree_lt)

/-! ## §0a — the residue reading of a level-`N` class -/

section ResMap

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

/-- The residue reading `Res O N → 𝔽_q` (defined for `0 < N`). -/
def resMap (O : Type*) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {N : ℕ} (hN : 0 < N) : Res O N →+* ResidueField O :=
  Ideal.Quotient.lift ((maximalIdeal O) ^ N) (residue O)
    (fun a ha => (residue_eq_zero_iff a).2 (Ideal.pow_le_self (by omega) ha))

@[simp] theorem resMap_mk {N : ℕ} (hN : 0 < N) (a : O) :
    resMap O hN (Ideal.Quotient.mk ((maximalIdeal O) ^ N) a) = residue O a :=
  rfl

theorem resMap_surjective {N : ℕ} (hN : 0 < N) :
    Function.Surjective (resMap O hN) := by
  intro y
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective (I := maximalIdeal O) y
  exact ⟨Ideal.Quotient.mk _ a, rfl⟩

/-- The kernel reader: the residue reading vanishes iff the windowed valuation is `≥ 1`. -/
theorem resMap_eq_zero_iff {N : ℕ} (hN : 0 < N) (x : Res O N) :
    resMap O hN x = 0 ↔ 1 ≤ resOrd x := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible O
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [resMap_mk, resOrd_ge_iff hπ (by omega : 1 ≤ N), pow_one, residue_eq_zero_iff,
    hπ.maximalIdeal_eq, Ideal.mem_span_singleton]

/-- Every class with vanishing residue reading is `π` times a class. -/
theorem exists_eq_mk_mul_of_resMap_eq_zero {N : ℕ} (hN : 0 < N) {π : O}
    (hπ : Irreducible π) {x : Res O N} (hx : resMap O hN x = 0) :
    ∃ y : Res O N, x = Ideal.Quotient.mk ((maximalIdeal O) ^ N) π * y := by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [resMap_mk, residue_eq_zero_iff] at hx
  rw [hπ.maximalIdeal_eq, Ideal.mem_span_singleton] at hx
  obtain ⟨c, rfl⟩ := hx
  exact ⟨Ideal.Quotient.mk _ c, by rw [map_mul]⟩

end ResMap

/-! ## §0b — residual vectors and polynomials -/

section ResVec

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

/-- The residual coefficient vector of a level-`N` box. -/
def resVec {n N : ℕ} (hN : 0 < N) (b : Coeff O n N) : Fin n → ResidueField O :=
  fun i => resMap O hN (b i)

/-- `polyOf` commutes with coefficientwise ring maps. -/
theorem map_polyOf {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) {n : ℕ}
    (b : Fin n → R) : (polyOf b).map φ = polyOf (fun i => φ (b i)) := by
  unfold Uniformity.Density.IFCG61.polyOf
  simp only [Polynomial.map_sum, Polynomial.map_mul, Polynomial.map_C, Polynomial.map_pow,
    Polynomial.map_X]

theorem map_polyOf_resVec {n N : ℕ} (hN : 0 < N) (b : Coeff O n N) :
    (polyOf b).map (resMap O hN) = polyOf (resVec hN b) :=
  map_polyOf _ b

/-- A nonzero residual vector gives a nonzero residual polynomial. -/
theorem polyOf_resVec_ne_zero {n N : ℕ} (hN : 0 < N) {b : Coeff O n N}
    (hb : resVec hN b ≠ 0) : polyOf (resVec hN b) ≠ 0 := by
  intro h
  apply hb
  funext i
  have := polyOf_coeff_lt (resVec hN b) i.isLt
  rw [h, Polynomial.coeff_zero] at this
  simpa using this.symm

/-- The stratum membership reader: `c ∈ levelZeroStratum O n N g` iff the monic residual
polynomial of `c`'s residue vector is `g`. -/
theorem mem_levelZeroStratum_iff_monicPoly_resVec {n N : ℕ} (hN : 0 < N)
    (g : Polynomial (ResidueField O)) (c : Coeff O n N) :
    c ∈ levelZeroStratum O n N g ↔ monicPoly (resVec hN c) = g := by
  rw [mem_levelZeroStratum_iff (by omega : 1 ≤ N)]
  constructor
  · rintro ⟨a, rfl, hg⟩
    rw [map_monicPoly] at hg
    convert hg using 2
    funext i
    rfl
  · intro hg
    obtain ⟨a, ha⟩ := proj_surjective' O n N c
    refine ⟨a, ha, ?_⟩
    rw [map_monicPoly, ← hg]
    congr 1
    funext i
    rw [resVec, ← ha]
    rfl

end ResVec

/-! ## §0c — `resOrd` complements -/

section ResOrdKit

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

/-- `resOrd` of the class of `π^k` is `min N k`. -/
theorem resOrd_mk_pow {π : O} (hπ : Irreducible π) {N : ℕ} (k : ℕ) :
    resOrd (Ideal.Quotient.mk ((maximalIdeal O) ^ N) (π ^ k)) = min N k := by
  rcases Nat.lt_or_ge k N with h | h
  · have h1 : k ≤ resOrd (Ideal.Quotient.mk ((maximalIdeal O) ^ N) (π ^ k)) :=
      (resOrd_ge_iff hπ h.le _).2 dvd_rfl
    have h2 : ¬ k + 1 ≤ resOrd (Ideal.Quotient.mk ((maximalIdeal O) ^ N) (π ^ k)) := by
      intro hc
      have hdvd : π ^ (k + 1) ∣ π ^ k := (resOrd_ge_iff hπ (by omega) _).1 hc
      have := (pow_dvd_pow_iff hπ.ne_zero hπ.not_isUnit).1 hdvd
      omega
    omega
  · rw [min_eq_left h]
    refine (resOrd_eq_iff _).2 ?_
    refine Ideal.Quotient.eq_zero_iff_mem.2 ?_
    have hmem : π ^ k ∈ (maximalIdeal O) ^ k := by
      rw [hπ.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    exact Ideal.pow_le_pow_right h hmem

/-- `resOrd` is invariant under multiplication by a unit. -/
theorem resOrd_isUnit_mul {N : ℕ} {u : Res O N} (hu : IsUnit u) (x : Res O N) :
    resOrd (u * x) = resOrd x := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · have h1 := resOrd_le (u * x)
    have h2 := resOrd_le x
    omega
  · have hu0 : resOrd u = 0 := by
      by_contra hc
      have h1 : resMap O hN u = 0 := (resMap_eq_zero_iff hN u).2 (by omega)
      have h2 : IsUnit (resMap O hN u) := hu.map (resMap O hN)
      rw [h1] at h2
      exact h2.ne_zero rfl
  -- additivity below the cap
    rw [resOrd_mul, hu0, zero_add, min_eq_right (resOrd_le x)]

/-- The exact-depth reader for `π^k`-scaled elements below the cap. -/
theorem resOrd_mk_pow_mul_eq_iff {π : O} (hπ : Irreducible π) {N v : ℕ} (hv : v < N)
    (k : ℕ) (y : Res O N) :
    resOrd (Ideal.Quotient.mk ((maximalIdeal O) ^ N) (π ^ k) * y) = v ↔
      k + resOrd y = v := by
  rw [resOrd_mul, resOrd_mk_pow hπ]
  have := resOrd_le y
  omega

end ResOrdKit

/-! ## §0d — the fibre-counting workhorse -/

section FibreCount

/-- Fibre counting through an additive map, over a subset of the range: the preimage of
`S ⊆ range φ` has `#ker φ` points over each point of `S`. -/
theorem card_preimage_of_subset_range {A B : Type*} [AddCommGroup A] [AddCommGroup B]
    [Finite A] (φ : A →+ B) (S : Set B) (hS : S ⊆ Set.range φ) :
    Nat.card (φ ⁻¹' S) = Nat.card φ.ker * Nat.card S := by
  classical
  have hres : Function.Surjective φ.rangeRestrict := φ.rangeRestrict_surjective
  have hpre : φ ⁻¹' S = φ.rangeRestrict ⁻¹' ((↑) ⁻¹' S : Set φ.range) := by
    ext a
    simp [AddMonoidHom.rangeRestrict]
  have hker : φ.rangeRestrict.ker = φ.ker := AddMonoidHom.ker_rangeRestrict φ
  have hcard : Nat.card ((↑) ⁻¹' S : Set φ.range) = Nat.card S := by
    refine Nat.card_congr ⟨fun x => ⟨(x : φ.range), x.2⟩, fun y => ⟨⟨y, hS y.2⟩, y.2⟩,
      fun x => rfl, fun y => rfl⟩
  rw [hpre, card_preimage_of_surjective φ.rangeRestrict hres ((↑) ⁻¹' S : Set φ.range),
    hker, hcard]

end FibreCount

/-! ## §0e — the `π`-scaling of the box and its counting -/

section ScaleBox

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)]

/-- Coordinatewise multiplication of the box by (the class of) `π`, as an additive map. -/
def scaleBox (π : O) (n N : ℕ) : Coeff O n N →+ Coeff O n N where
  toFun b := fun i => Ideal.Quotient.mk ((maximalIdeal O) ^ N) π * b i
  map_zero' := by funext i; simp
  map_add' b b' := by funext i; simp [mul_add]

theorem scaleBox_apply (π : O) {n N : ℕ} (b : Coeff O n N) (i : Fin n) :
    scaleBox π n N b i = Ideal.Quotient.mk ((maximalIdeal O) ^ N) π * b i := rfl

theorem polyOf_scaleBox (π : O) {n N : ℕ} (b : Coeff O n N) :
    polyOf (scaleBox π n N b)
      = Polynomial.C (Ideal.Quotient.mk ((maximalIdeal O) ^ N) π) * polyOf b := by
  unfold Uniformity.Density.IFCG61.polyOf
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by rw [scaleBox_apply, map_mul]; ring

/-- **The finite-level Weierstrass π-pullout**: scaling the box by `π` multiplies the
reduced resultant by `π^n`. -/
theorem redRes_scaleBox (π : O) {n N : ℕ} (c b : Coeff O n N) :
    redRes c (scaleBox π n N b)
      = Ideal.Quotient.mk ((maximalIdeal O) ^ N) (π ^ n) * redRes c b := by
  rw [Uniformity.Density.IFCG61.redRes, Uniformity.Density.IFCG61.redRes, polyOf_scaleBox,
    Polynomial.resultant_C_mul_right, map_pow]

/-- The range of `scaleBox` is the residual-zero box. -/
theorem range_scaleBox {π : O} (hπ : Irreducible π) {n N : ℕ} (hN : 0 < N) :
    Set.range (scaleBox π n N) = {b : Coeff O n N | resVec hN b = 0} := by
  ext b
  constructor
  · rintro ⟨b', rfl⟩
    funext i
    rw [Pi.zero_apply, resVec, scaleBox_apply, map_mul]
    obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (b' i)
    rw [← ha, resMap_mk]
    have : residue O π = 0 := Ideal.Quotient.eq_zero_iff_mem.2 (hπ.maximalIdeal_eq ▸
      Ideal.mem_span_singleton.2 dvd_rfl)
    rw [this, zero_mul]
  · intro hb
    have h : ∀ i, ∃ y, b i = Ideal.Quotient.mk ((maximalIdeal O) ^ N) π * y := by
      intro i
      exact exists_eq_mk_mul_of_resMap_eq_zero hN hπ (congrFun hb i)
    choose y hy using h
    exact ⟨y, funext fun i => (hy i).symm⟩

/-- The kernel of one-coordinate `π`-scaling has exactly `q` elements (`0 < N`). -/
theorem card_ker_scale_one {π : O} (hπ : Irreducible π) {N : ℕ} (hN : 0 < N) :
    Nat.card {x : Res O N | Ideal.Quotient.mk ((maximalIdeal O) ^ N) π * x = 0}
      = residueCard O := by
  classical
  set μ : Res O N →+ Res O N :=
    { toFun := fun x => Ideal.Quotient.mk ((maximalIdeal O) ^ N) π * x
      map_zero' := mul_zero _
      map_add' := fun x y => mul_add _ x y } with hμ
  -- the range of `μ` is the valuation-`≥ 1` set of `card_res_ge_of_ge`
  have hrange : Nat.card (Set.range μ) = residueCard O ^ (N - 1) := by
    rw [← card_res_ge_of_ge hπ (by omega : 1 ≤ N)]
    refine Nat.card_congr (Equiv.subtypeEquivRight fun r => ?_)
    constructor
    · rintro ⟨y, rfl⟩
      obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective y
      refine ⟨π * b, by rw [hμ]; simp [map_mul], ?_⟩
      exact (le_addVal_iff_pow_dvd hπ 1 _).2 (by rw [pow_one]; exact dvd_mul_right π b)
    · rintro ⟨x, rfl, hx⟩
      obtain ⟨c, rfl⟩ := (pow_one π ▸ (le_addVal_iff_pow_dvd hπ 1 x).1 hx : π ∣ x)
      exact ⟨Ideal.Quotient.mk _ c, by rw [hμ]; simp [map_mul]⟩
  -- `#Res = #ker μ * #range μ`
  have htotal : Nat.card (Res O N) = Nat.card μ.ker * Nat.card (Set.range μ) := by
    have h := card_preimage_of_subset_range μ (Set.range μ) le_rfl
    rw [Set.preimage_range] at h
    rw [← h, Nat.card_coe_set_eq, Set.ncard_univ]
  -- read off the kernel count
  have hker : Nat.card μ.ker * residueCard O ^ (N - 1) = residueCard O ^ N := by
    rw [← hrange, ← htotal, card_res]
  have hpow : residueCard O ^ N = residueCard O * residueCard O ^ (N - 1) := by
    rw [← pow_succ']
    congr 1
    omega
  have hpos : 0 < residueCard O ^ (N - 1) := pow_pos (residueCard_pos O) _
  have hcard : Nat.card μ.ker = residueCard O :=
    Nat.eq_of_mul_eq_mul_right hpos (hker.trans hpow)
  rw [← hcard]
  refine Nat.card_congr (Equiv.subtypeEquivRight fun x => ?_)
  rw [Set.mem_setOf_eq, AddMonoidHom.mem_ker, hμ]
  exact Iff.rfl

/-- The kernel of the box `π`-scaling has `q^n` elements (`0 < N`). -/
theorem card_ker_scaleBox {π : O} (hπ : Irreducible π) {n N : ℕ} (hN : 0 < N) :
    Nat.card (scaleBox π n N).ker = residueCard O ^ n := by
  classical
  have he : ((scaleBox π n N).ker : Type _)
      ≃ (Fin n → {x : Res O N | Ideal.Quotient.mk ((maximalIdeal O) ^ N) π * x = 0}) :=
    { toFun := fun b => fun i => ⟨b.1 i, congrFun b.2 i⟩
      invFun := fun f => ⟨fun i => (f i).1, funext fun i => (f i).2⟩
      left_inv := fun b => rfl
      right_inv := fun f => rfl }
  rw [Nat.card_congr he, Nat.card_fun, card_ker_scale_one hπ hN,
    Nat.card_eq_fintype_card (α := Fin n), Fintype.card_fin]

/-- **The scaling census transport**: a census set supported on residual-zero boxes is
`q^n`-covered by its `scaleBox` preimage. -/
theorem card_scaleBox_preimage {π : O} (hπ : Irreducible π) {n N : ℕ} (hN : 0 < N)
    (S : Set (Coeff O n N)) (hS : ∀ b ∈ S, resVec hN b = 0) :
    Nat.card ((scaleBox π n N) ⁻¹' S) = residueCard O ^ n * Nat.card S := by
  rw [card_preimage_of_subset_range (scaleBox π n N) S
    (fun b hb => (range_scaleBox hπ hN).symm ▸ hS b hb), card_ker_scaleBox hπ hN]

end ScaleBox

/-! ## §0f — counting the stratum and the residual fibres -/

section StratumCount

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)]

/-- The residual-vector reading of the box, as an additive map. -/
def resVecHom (O : Type*) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (n : ℕ) {N : ℕ} (hN : 0 < N) : Coeff O n N →+ (Fin n → ResidueField O) where
  toFun b := resVec hN b
  map_zero' := by funext i; simp [resVec]
  map_add' b b' := by funext i; simp [resVec]

theorem resVecHom_surjective {n N : ℕ} (hN : 0 < N) :
    Function.Surjective (resVecHom O n hN) := by
  intro w
  choose a ha using fun i => resMap_surjective (O := O) hN (w i)
  exact ⟨a, funext ha⟩

/-- The kernel of the residual reading has `q^{n(N−1)}` classes. -/
theorem card_ker_resVecHom {n N : ℕ} (hN : 0 < N) :
    Nat.card (resVecHom O n hN).ker = residueCard O ^ (n * (N - 1)) := by
  classical
  have htotal : Nat.card (Coeff O n N)
      = Nat.card (resVecHom O n hN).ker * Nat.card (Fin n → ResidueField O) := by
    have h := card_preimage_of_surjective (resVecHom O n hN) (resVecHom_surjective hN)
      Set.univ
    rw [Set.preimage_univ, Nat.card_coe_set_eq, Set.ncard_univ, Nat.card_coe_set_eq,
      Set.ncard_univ] at h
    exact h
  have hfun : Nat.card (Fin n → ResidueField O) = residueCard O ^ n := by
    rw [Nat.card_fun, Nat.card_eq_fintype_card (α := Fin n), Fintype.card_fin]
    rfl
  rw [card_coeff, hfun] at htotal
  have hpow : residueCard O ^ (n * N) = residueCard O ^ (n * (N - 1)) * residueCard O ^ n := by
    obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := ⟨N - 1, by omega⟩
    rw [← pow_add, Nat.add_sub_cancel]
    congr 1
  have hpos : 0 < residueCard O ^ n := pow_pos (residueCard_pos O) _
  exact Nat.eq_of_mul_eq_mul_right hpos (by omega)

/-- The residual fibres of the box each have `q^{n(N−1)}` classes. -/
theorem card_resVec_fiber {n N : ℕ} (hN : 0 < N) (w : Fin n → ResidueField O) :
    Nat.card {b : Coeff O n N | resVec hN b = w} = residueCard O ^ (n * (N - 1)) := by
  classical
  have hset : {b : Coeff O n N | resVec hN b = w} = (resVecHom O n hN) ⁻¹' {w} := rfl
  rw [hset, card_preimage_of_surjective (resVecHom O n hN) (resVecHom_surjective hN) {w},
    card_ker_resVecHom hN]
  simp

/-- **The stratum count**: the level-`N` stratum at a monic degree-`n` residual has
`q^{n(N−1)}` classes. -/
theorem card_levelZeroStratum {n N : ℕ} (hN : 0 < N) {g : Polynomial (ResidueField O)}
    (hg : g.Monic) (hd : g.natDegree = n) :
    Nat.card (levelZeroStratum O n N g) = residueCard O ^ (n * (N - 1)) := by
  have hset : levelZeroStratum O n N g
      = {c : Coeff O n N | resVec hN c = fun i : Fin n => g.coeff (i : ℕ)} := by
    ext c
    rw [Set.mem_setOf_eq, mem_levelZeroStratum_iff_monicPoly_resVec hN]
    constructor
    · intro hg'
      funext i
      rw [← hg', monicPoly_coeff_lt_ring _ i.isLt]
    · intro hvec
      rw [hvec]
      exact monicPoly_coeff_self_ring hg hd
  rw [hset, card_resVec_fiber hN]

end StratumCount

/-! ## §1 — the two peel legs at a general monic residual -/

section PeelLegs

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)]

/-- The residue reading of the reduced resultant IS the residual resultant at pinned
sizes, for a stratified frame. -/
theorem resMap_redRes {n N : ℕ} (hN : 0 < N) {g : Polynomial (ResidueField O)}
    {c : Coeff O n N} (hc : c ∈ levelZeroStratum O n N g) (b : Coeff O n N) :
    resMap O hN (redRes c b)
      = Polynomial.resultant g (polyOf (resVec hN b)) n n := by
  rw [Uniformity.Density.IFCG61.redRes,
    ← Polynomial.resultant_map_map (monicPoly c) (polyOf b) n n (resMap O hN),
    map_monicPoly, map_polyOf]
  rw [show (monicPoly fun i => resMap O hN (c i)) = monicPoly (resVec hN c) from rfl,
    (mem_levelZeroStratum_iff_monicPoly_resVec hN g c).1 hc]
  rfl

/-- **Peel leg 1**: a box whose residual is coprime to the frame's residual has
reduced-resultant depth `0`. -/
theorem resOrd_redRes_eq_zero_of_coprime {n N : ℕ} (hN : 0 < N)
    {g : Polynomial (ResidueField O)} (hg : g.Monic) (hd : g.natDegree = n)
    {c : Coeff O n N} (hc : c ∈ levelZeroStratum O n N g) {b : Coeff O n N}
    (hcop : IsCoprime g (polyOf (resVec hN b))) :
    resOrd (redRes c b) = 0 := by
  set ρ : Polynomial (ResidueField O) := polyOf (resVec hN b) with hρ
  have hρd : ρ.natDegree ≤ n :=
    Polynomial.natDegree_le_iff_degree_le.mpr (le_of_lt (polyOf_degree_lt _))
  have hwin : Polynomial.resultant g ρ n n = Polynomial.resultant g ρ n ρ.natDegree := by
    have h := Polynomial.resultant_add_right_deg (f := g) (g := ρ) (m := n)
      (n := ρ.natDegree) (n - ρ.natDegree) le_rfl
    rw [show ρ.natDegree + (n - ρ.natDegree) = n by omega] at h
    rw [h, ← hd, hg.coeff_natDegree, one_pow, one_mul]
  have hne : resMap O hN (redRes c b) ≠ 0 := by
    rw [resMap_redRes hN hc b, ← hρ, hwin, ← hd]
    exact Polynomial.resultant_ne_zero g ρ hcop
  have h1 := resMap_eq_zero_iff hN (redRes c b)
  by_contra h0
  exact hne (h1.2 (by omega))

/-- The residual resultant vanishes on a residual-zero box (`0 < n`). -/
theorem resMap_redRes_eq_zero_of_resVec_zero {n N : ℕ} (hN : 0 < N) (h0 : 0 < n)
    {g : Polynomial (ResidueField O)} {c : Coeff O n N}
    (hc : c ∈ levelZeroStratum O n N g) {b : Coeff O n N}
    (hb : resVec hN b = 0) :
    resMap O hN (redRes c b) = 0 := by
  have hzero : polyOf (resVec hN b) = 0 := by
    rw [hb]
    unfold Uniformity.Density.IFCG61.polyOf
    simp
  rw [resMap_redRes hN hc b, hzero, Polynomial.resultant_zero_right,
    zero_pow (by omega : n ≠ 0), zero_mul]

end PeelLegs

/-! ## §2 — ★★ THE `e = 1` PRIMARY LAW: the `(1,1)` law at scale `q^δ` -/

section PrimaryOne

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)]

/-- At an irreducible residual, a nonzero box residual is coprime to it (the residual
has smaller degree). -/
theorem isCoprime_of_resVec_ne_zero {δ N : ℕ} (hN : 0 < N)
    {r : Polynomial (ResidueField O)} (hr : Irreducible r) (hrd : r.natDegree = δ)
    {b : Coeff O δ N} (hb : resVec hN b ≠ 0) :
    IsCoprime r (polyOf (resVec hN b)) := by
  have hρ : polyOf (resVec hN b) ≠ 0 := polyOf_resVec_ne_zero hN hb
  refine hr.coprime_iff_not_dvd.2 fun hdvd => ?_
  have hle : r.natDegree ≤ (polyOf (resVec hN b)).natDegree :=
    Polynomial.natDegree_le_of_dvd hdvd hρ
  have hlt : (polyOf (resVec hN b)).natDegree < δ :=
    (Polynomial.natDegree_lt_iff_degree_lt hρ).2 (polyOf_degree_lt _)
  omega

/-- ★ **The per-frame `e = 1` census** (`v < N`, `c` in the stratum of an irreducible
residual `r` of degree `δ`): the `(1,1)` law at scale `q^δ` —
`(q^δ − 1)·q^{δ(N − v/δ − 1)}` at multiples of `δ`, `0` off multiples. -/
theorem card_frameDepthSet_irreducible {δ N v : ℕ} (h0 : 0 < δ) (hv : v < N)
    {r : Polynomial (ResidueField O)} (hr : Irreducible r) (hrm : r.Monic)
    (hrd : r.natDegree = δ) {c : Coeff O δ N} (hc : c ∈ levelZeroStratum O δ N r) :
    Nat.card (frameDepthSet O δ N v c)
      = if δ ∣ v then (residueCard O ^ δ - 1) * residueCard O ^ (δ * (N - v / δ - 1))
        else 0 := by
  classical
  have hN : 0 < N := by omega
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible O
  revert hv
  induction v using Nat.strong_induction_on with
  | _ v IH =>
    intro hv
    rcases Nat.eq_zero_or_pos v with rfl | hvpos
    · -- the `v = 0` fibre: exactly the nonzero-residual boxes
      rw [if_pos (dvd_zero δ)]
      have hset : frameDepthSet O δ N 0 c = {b : Coeff O δ N | resVec hN b = 0}ᶜ := by
        ext b
        simp only [frameDepthSet, Set.mem_setOf_eq, Set.mem_compl_iff]
        constructor
        · intro hb hb0
          have h1 := resMap_redRes_eq_zero_of_resVec_zero hN h0 hc hb0
          have h2 := (resMap_eq_zero_iff hN _).1 h1
          omega
        · intro hb
          exact resOrd_redRes_eq_zero_of_coprime hN hrm hrd hc
            (isCoprime_of_resVec_ne_zero hN hr hrd hb)
      rw [hset]
      have htot := Set.ncard_add_ncard_compl {b : Coeff O δ N | resVec hN b = 0}
      rw [← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq, card_resVec_fiber hN 0,
        card_coeff] at htot
      rw [Nat.zero_div, Nat.sub_zero]
      obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := ⟨N - 1, by omega⟩
      rw [Nat.add_sub_cancel] at htot ⊢
      have harith : (residueCard O ^ δ - 1) * residueCard O ^ (δ * M)
          = residueCard O ^ (δ * (M + 1)) - residueCard O ^ (δ * M) := by
        have he : δ + δ * M = δ * (M + 1) := by ring
        rw [Nat.sub_mul, one_mul, ← pow_add, he]
      rw [harith]
      omega
    · -- the `v ≥ 1` fibre: every member has zero residual; peel one `π`
      have hsub : ∀ b ∈ frameDepthSet O δ N v c, resVec hN b = 0 := by
        intro b hb
        by_contra hbne
        have h1 := resOrd_redRes_eq_zero_of_coprime hN hrm hrd hc
          (isCoprime_of_resVec_ne_zero hN hr hrd hbne)
        have hb' : resOrd (redRes c b) = v := hb
        omega
      have hpre : (scaleBox π δ N) ⁻¹' (frameDepthSet O δ N v c)
          = {b' : Coeff O δ N | δ + resOrd (redRes c b') = v} := by
        ext b'
        simp only [Set.mem_preimage, frameDepthSet, Set.mem_setOf_eq]
        rw [redRes_scaleBox, resOrd_mk_pow_mul_eq_iff hπ hv]
      have hcount := card_scaleBox_preimage hπ hN (frameDepthSet O δ N v c) hsub
      rcases Nat.lt_or_ge v δ with hvd | hvd
      · -- `1 ≤ v < δ`: the peeled window is empty
        have hempty : {b' : Coeff O δ N | δ + resOrd (redRes c b') = v} = ∅ := by
          ext b'
          simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
          omega
        rw [hpre, hempty, Nat.card_coe_set_eq, Set.ncard_empty] at hcount
        have hq : residueCard O ^ δ ≠ 0 := (pow_pos (residueCard_pos O) δ).ne'
        rcases Nat.mul_eq_zero.1 hcount.symm with h | h
        · exact absurd h hq
        · rw [h, if_neg]
          intro hdvd
          have := Nat.le_of_dvd hvpos hdvd
          omega
      · -- `δ ≤ v`: the peeled window is the depth-`(v−δ)` census
        have heq : {b' : Coeff O δ N | δ + resOrd (redRes c b') = v}
            = frameDepthSet O δ N (v - δ) c := by
          ext b'
          simp only [Set.mem_setOf_eq, frameDepthSet]
          omega
        rw [hpre, heq, IH (v - δ) (by omega) (by omega)] at hcount
        by_cases hdvd : δ ∣ v
        · rw [if_pos hdvd]
          obtain ⟨w, rfl⟩ := hdvd
          have hw1 : 1 ≤ w := by
            rcases Nat.eq_zero_or_pos w with rfl | h
            · omega
            · exact h
          have hwN : w < N := by
            have : w ≤ δ * w := Nat.le_mul_of_pos_left w h0
            omega
          have hsub' : δ * w - δ = δ * (w - 1) := by
            rcases Nat.exists_eq_add_of_le hw1 with ⟨w', rfl⟩
            have h1 : δ * (1 + w') = δ + δ * w' := by ring
            have h2 : 1 + w' - 1 = w' := by omega
            rw [h1, h2, Nat.add_sub_cancel_left]
          rw [hsub', if_pos (dvd_mul_right δ (w - 1)), Nat.mul_div_cancel_left _ h0] at hcount
          rw [Nat.mul_div_cancel_left _ h0]
          -- cancel `q^δ` on both sides
          refine Nat.eq_of_mul_eq_mul_left (pow_pos (residueCard_pos O) δ) ?_
          rw [← hcount, mul_left_comm, ← pow_add]
          have e1 : N - (w - 1) - 1 = (N - w - 1) + 1 := by omega
          have e2 : δ * ((N - w - 1) + 1) = δ + δ * (N - w - 1) := by ring
          rw [e1, e2]
        · rw [if_neg hdvd]
          have hnd : ¬ δ ∣ (v - δ) := by
            intro hdd
            exact hdvd (by
              have := Nat.dvd_add hdd (dvd_refl δ)
              rwa [Nat.sub_add_cancel hvd] at this)
          rw [if_neg hnd] at hcount
          have hq : residueCard O ^ δ ≠ 0 := (pow_pos (residueCard_pos O) δ).ne'
          rcases Nat.mul_eq_zero.1 hcount.symm with h | h
          · exact absurd h hq
          · exact h

/-- ★★ **THE `e = 1` PRIMARY STRATUM CENSUS**: for `r` irreducible of degree `δ`,
`v < N`:
`#stratumDepthSet(δ, N, v, r) = q^{δ(N−1)} · (q^δ − 1) · q^{δ(N − v/δ − 1)}` at
multiples of `δ`, and `0` off multiples of `δ` — the `(1,1)` law at scale `q^δ`. -/
theorem card_stratumDepthSet_irreducible {δ N v : ℕ} (h0 : 0 < δ) (hv : v < N)
    {r : Polynomial (ResidueField O)} (hr : Irreducible r) (hrm : r.Monic)
    (hrd : r.natDegree = δ) :
    Nat.card (stratumDepthSet O δ N v r)
      = if δ ∣ v then
          residueCard O ^ (δ * (N - 1))
            * ((residueCard O ^ δ - 1) * residueCard O ^ (δ * (N - v / δ - 1)))
        else 0 := by
  classical
  have hN : 0 < N := by omega
  haveI : Fintype (Coeff O δ N) := Fintype.ofFinite _
  rw [card_stratumDepthSet_eq_sum,
    Finset.sum_congr rfl (fun c hc => card_frameDepthSet_irreducible h0 hv hr hrm hrd
      (Set.mem_toFinset.1 hc)),
    Finset.sum_const, smul_eq_mul, ← Set.ncard_eq_toFinset_card', ← Nat.card_coe_set_eq,
    card_levelZeroStratum hN hrm hrd, mul_ite, mul_zero]

end PrimaryOne

/-! ## §3a — the content counts: residual divisibility censuses -/

section ContentCount

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)]

/-- Census transport through the residual reading: a residual predicate's box count is
`q^{n(N−1)}` times its residual count. -/
theorem card_box_residual_pred {n N : ℕ} (hN : 0 < N)
    (P : (Fin n → ResidueField O) → Prop) :
    Nat.card {b : Coeff O n N | P (resVec hN b)}
      = residueCard O ^ (n * (N - 1)) * Nat.card {w : Fin n → ResidueField O | P w} := by
  have hset : {b : Coeff O n N | P (resVec hN b)}
      = (resVecHom O n hN) ⁻¹' {w | P w} := rfl
  rw [hset, card_preimage_of_surjective (resVecHom O n hN) (resVecHom_surjective hN) _,
    card_ker_resVecHom hN]

/-- The multiples of a fixed monic `s` of degree `d ≤ m` among size-`m` residual vectors
number `q^{m−d}`. -/
theorem card_dvd_residual {m d : ℕ} (hdm : d ≤ m) {s : Polynomial (ResidueField O)}
    (hs : s.Monic) (hsd : s.natDegree = d) :
    Nat.card {w : Fin m → ResidueField O | s ∣ polyOf w}
      = residueCard O ^ (m - d) := by
  classical
  set f : (Fin (m - d) → ResidueField O) → (Fin m → ResidueField O) :=
    fun τ => fun i : Fin m => (s * polyOf τ).coeff (i : ℕ) with hf
  have himg : ∀ τ, polyOf (f τ) = s * polyOf τ := by
    intro τ
    refine polyOf_eq_self_of_degree_lt ?_
    rcases eq_or_ne (polyOf τ) 0 with h0 | h0
    · rw [h0, mul_zero, Polynomial.degree_zero]
      exact WithBot.bot_lt_coe m
    · rw [Polynomial.degree_mul, Polynomial.degree_eq_natDegree hs.ne_zero, hsd]
      have hτ : (polyOf τ).degree < ((m - d : ℕ) : WithBot ℕ) := polyOf_degree_lt τ
      rcases Polynomial.degree_eq_natDegree h0 ▸ hτ with hτ'
      have hτd : (polyOf τ).natDegree < m - d := by exact_mod_cast hτ'
      rw [Polynomial.degree_eq_natDegree h0]
      exact_mod_cast (by omega : d + (polyOf τ).natDegree < m)
  have hbij : Set.BijOn f Set.univ {w : Fin m → ResidueField O | s ∣ polyOf w} := by
    refine ⟨fun τ _ => ⟨polyOf τ, himg τ⟩, ?_, ?_⟩
    · intro τ₁ _ τ₂ _ heq
      have h1 : polyOf (f τ₁) = polyOf (f τ₂) := by rw [heq]
      rw [himg, himg] at h1
      have h2 : polyOf τ₁ = polyOf τ₂ := mul_left_cancel₀ hs.ne_zero h1
      funext i
      have := congrArg (fun p => Polynomial.coeff p (i : ℕ)) h2
      simpa [polyOf_coeff_lt _ i.isLt] using this
    · intro w hw
      obtain ⟨t, ht⟩ := hw
      have htd : t.degree < ((m - d : ℕ) : WithBot ℕ) := by
        rcases eq_or_ne t 0 with rfl | ht0
        · rw [Polynomial.degree_zero]
          exact WithBot.bot_lt_coe _
        · have hw0 : polyOf w ≠ 0 := by
            rw [ht]
            exact mul_ne_zero hs.ne_zero ht0
          have hdeg : (polyOf w).degree < (m : WithBot ℕ) := polyOf_degree_lt w
          rw [ht, Polynomial.degree_mul, Polynomial.degree_eq_natDegree hs.ne_zero, hsd,
            Polynomial.degree_eq_natDegree ht0] at hdeg
          rw [Polynomial.degree_eq_natDegree ht0]
          have : d + t.natDegree < m := by exact_mod_cast hdeg
          exact_mod_cast (by omega : t.natDegree < m - d)
      refine ⟨fun i => t.coeff (i : ℕ), Set.mem_univ _, ?_⟩
      have hpt : polyOf (fun i : Fin (m - d) => t.coeff (i : ℕ)) = t :=
        polyOf_eq_self_of_degree_lt htd
      funext i
      rw [hf]
      simp only [hpt]
      rw [← ht, polyOf_coeff_lt _ i.isLt]
  have hcard := Nat.card_congr (Set.BijOn.equiv f hbij)
  rw [← hcard, Nat.card_coe_set_eq, Set.ncard_univ, Nat.card_fun,
    Nat.card_eq_fintype_card (α := Fin (m - d)), Fintype.card_fin]
  rfl

/-- The exact-content residual census at any window `m ≥ δ(j+1)`:
`q^{m−δj} − q^{m−δ(j+1)}` vectors whose polynomial has `r`-content exactly `j`. -/
theorem card_content_residual {δ m j : ℕ} (hjm : δ * (j + 1) ≤ m)
    {r : Polynomial (ResidueField O)} (hrm : r.Monic) (hrd : r.natDegree = δ) :
    Nat.card {w : Fin m → ResidueField O |
        r ^ j ∣ polyOf w ∧ ¬ r ^ (j + 1) ∣ polyOf w}
      = residueCard O ^ (m - δ * j) - residueCard O ^ (m - δ * (j + 1)) := by
  classical
  have hsubset : {w : Fin m → ResidueField O | r ^ (j + 1) ∣ polyOf w}
      ⊆ {w : Fin m → ResidueField O | r ^ j ∣ polyOf w} :=
    fun w hw => dvd_trans (pow_dvd_pow r (by omega)) hw
  have hdiff : {w : Fin m → ResidueField O | r ^ j ∣ polyOf w ∧ ¬ r ^ (j + 1) ∣ polyOf w}
      = {w : Fin m → ResidueField O | r ^ j ∣ polyOf w}
        \ {w : Fin m → ResidueField O | r ^ (j + 1) ∣ polyOf w} := by
    ext w
    simp
  have hdeg : ∀ k : ℕ, (r ^ k).natDegree = δ * k := by
    intro k
    rw [Polynomial.natDegree_pow, hrd, Nat.mul_comm]
  have hjm' : δ * j ≤ m := le_trans (Nat.mul_le_mul_left δ (by omega)) hjm
  rw [hdiff, Nat.card_coe_set_eq, Set.ncard_sdiff hsubset, ← Nat.card_coe_set_eq,
    ← Nat.card_coe_set_eq,
    card_dvd_residual hjm' (hrm.pow j) (hdeg j),
    card_dvd_residual hjm (hrm.pow (j + 1)) (hdeg (j + 1))]

/-- The coprime residual census at any window `m ≥ δ`: `q^m − q^{m−δ}` vectors whose
polynomial is not divisible by `r`. -/
theorem card_coprime_residual {δ m : ℕ} (hδm : δ ≤ m)
    {r : Polynomial (ResidueField O)} (hrm : r.Monic) (hrd : r.natDegree = δ) :
    Nat.card {w : Fin m → ResidueField O | ¬ r ∣ polyOf w}
      = residueCard O ^ m - residueCard O ^ (m - δ) := by
  classical
  have hcompl : {w : Fin m → ResidueField O | ¬ r ∣ polyOf w}
      = {w : Fin m → ResidueField O | r ∣ polyOf w}ᶜ := by
    ext w
    simp
  have htot := Set.ncard_add_ncard_compl {w : Fin m → ResidueField O | r ∣ polyOf w}
  rw [← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq, card_dvd_residual hδm hrm hrd] at htot
  have hfun : Nat.card (Fin m → ResidueField O) = residueCard O ^ m := by
    rw [Nat.card_fun, Nat.card_eq_fintype_card (α := Fin m), Fintype.card_fin]
    rfl
  rw [hfun] at htot
  rw [hcompl]
  omega

end ContentCount

/-! ## §3b — the Bézout lift and the primary–coprime product parametrization -/

section PrimaryFactor

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)]

/-- Classes with vanishing residue reading are nilpotent (`x^N = 0`). -/
theorem isNilpotent_of_resMap_eq_zero {N : ℕ} (hN : 0 < N) {x : Res O N}
    (hx : resMap O hN x = 0) : IsNilpotent x := by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [resMap_mk, residue_eq_zero_iff] at hx
  refine ⟨N, ?_⟩
  rw [← map_pow]
  exact Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.pow_mem_pow hx N)

/-- **The Bézout lift**: residual coprimality over the residue field lifts to the
truncation ring (the defect polynomial has nilpotent coefficients, so the lifted Bézout
combination is a unit). -/
theorem isCoprime_of_isCoprime_resMap {N : ℕ} (hN : 0 < N)
    {F H : Polynomial (Res O N)}
    (hcop : IsCoprime (F.map (resMap O hN)) (H.map (resMap O hN))) :
    IsCoprime F H := by
  obtain ⟨a, b, hab⟩ := hcop
  obtain ⟨a', ha'⟩ := Polynomial.map_surjective _ (resMap_surjective hN) a
  obtain ⟨b', hb'⟩ := Polynomial.map_surjective _ (resMap_surjective hN) b
  set z : Polynomial (Res O N) := 1 - (a' * F + b' * H) with hz
  have hmap : z.map (resMap O hN) = 0 := by
    rw [hz, Polynomial.map_sub, Polynomial.map_one, Polynomial.map_add, Polynomial.map_mul,
      Polynomial.map_mul, ha', hb', hab, sub_self]
  have hznil : IsNilpotent z := by
    rw [Polynomial.isNilpotent_iff]
    intro i
    refine isNilpotent_of_resMap_eq_zero hN ?_
    have : (z.map (resMap O hN)).coeff i = 0 := by rw [hmap]; simp
    rwa [Polynomial.coeff_map] at this
  have hunit : IsUnit (a' * F + b' * H) := by
    have h1 : a' * F + b' * H = 1 - z := by rw [hz]; ring
    rw [h1]
    exact hznil.isUnit_one_sub
  obtain ⟨u, hu⟩ := hunit
  refine ⟨(↑u⁻¹ : Polynomial (Res O N)) * a', (↑u⁻¹ : Polynomial (Res O N)) * b', ?_⟩
  calc (↑u⁻¹ : Polynomial (Res O N)) * a' * F + (↑u⁻¹ : Polynomial (Res O N)) * b' * H
      = (↑u⁻¹ : Polynomial (Res O N)) * (a' * F + b' * H) := by ring
    _ = (↑u⁻¹ : Polynomial (Res O N)) * ↑u := by rw [hu]
    _ = 1 := u.inv_mul

/-- A monic divisor of a monic polynomial of the same `natDegree` equals it (any
nontrivial commutative ring). -/
private theorem monic_dvd_monic_eq {R : Type*} [CommRing R] [Nontrivial R]
    {P Q : Polynomial R} (hP : P.Monic) (hQ : Q.Monic)
    (hd : P.natDegree = Q.natDegree) (hdvd : P ∣ Q) : P = Q := by
  obtain ⟨T, hT⟩ := hdvd
  have hT0 : T ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hT
    exact hQ.ne_zero hT
  have hdeg : Q.natDegree = P.natDegree + T.natDegree := by
    rw [hT, Polynomial.natDegree_mul' (by
      rw [hP.leadingCoeff, one_mul]
      exact Polynomial.leadingCoeff_ne_zero.mpr hT0)]
  have hTd : T.natDegree = 0 := by omega
  have hTC : T = Polynomial.C (T.coeff 0) := Polynomial.eq_C_of_natDegree_eq_zero hTd
  have hco : Q.coeff Q.natDegree = P.coeff Q.natDegree * T.coeff 0 := by
    have h1 : Q.coeff Q.natDegree = (P * Polynomial.C (T.coeff 0)).coeff Q.natDegree := by
      rw [← hTC, ← hT]
    rw [h1, Polynomial.coeff_mul_C]
  rw [hQ.coeff_natDegree, ← hd, hP.coeff_natDegree, one_mul] at hco
  rw [hT, hTC, ← hco, map_one, mul_one]

/-- The product parametrization into a fixed coefficient window: the coefficients of
`monicPoly P · polyOf U`, read in `Coeff O n N`. -/
def prodVecAt {n₁ n₂ N : ℕ} (n : ℕ) (P : Coeff O n₁ N) (U : Coeff O n₂ N) :
    Coeff O n N :=
  fun i => (monicPoly P * polyOf U).coeff (i : ℕ)

theorem polyOf_prodVecAt {n₁ n₂ n N : ℕ} (hN : 0 < N) (hsum : n₁ + n₂ ≤ n)
    (P : Coeff O n₁ N) (U : Coeff O n₂ N) :
    polyOf (prodVecAt n P U) = monicPoly P * polyOf U := by
  letI : Nontrivial (Res O N) := nontrivial_res O hN
  refine polyOf_eq_self_of_degree_lt ?_
  rcases eq_or_ne (polyOf U) 0 with h0 | h0
  · rw [h0, mul_zero, Polynomial.degree_zero]
    exact WithBot.bot_lt_coe n
  · have hne : monicPoly P * polyOf U ≠ 0 := fun hc =>
      h0 ((monicPoly_monic_ring P).isRegular.left
        (show monicPoly P * polyOf U = monicPoly P * 0 by rw [hc, mul_zero]))
    have hPU : (monicPoly P * polyOf U).natDegree = n₁ + (polyOf U).natDegree := by
      rw [Polynomial.natDegree_mul' (by
        rw [(monicPoly_monic_ring P).leadingCoeff, one_mul]
        exact Polynomial.leadingCoeff_ne_zero.mpr h0), monicPoly_natDegree_ring]
    refine (Polynomial.natDegree_lt_iff_degree_lt hne).mp ?_
    have hU : (polyOf U).natDegree < n₂ :=
      (Polynomial.natDegree_lt_iff_degree_lt h0).mpr (polyOf_degree_lt U)
    omega

private theorem natCard_prod_set {α β : Type*} (s : Set α) (t : Set β) :
    Nat.card (s ×ˢ t : Set (α × β)) = Nat.card s * Nat.card t := by
  rw [← Nat.card_prod]
  exact Nat.card_congr (Equiv.Set.prod s t)

/-- ★ **THE PRIMARY–COPRIME FACTORIZATION BIJECTION** (finite-level coprime Hensel, by
injectivity + counting — no completeness): the content-`j` boxes are exactly the
products (monic `r^j`-stratum class) × (`r`-coprime box). -/
theorem bijOn_prodVecAt {N n j δ : ℕ} (hN : 0 < N) (h0 : 0 < δ) (hjn : δ * (j + 1) ≤ n)
    {r : Polynomial (ResidueField O)} (hr : Irreducible r) (hrm : r.Monic)
    (hrd : r.natDegree = δ) :
    Set.BijOn (fun p : Coeff O (δ * j) N × Coeff O (n - δ * j) N => prodVecAt n p.1 p.2)
      ((levelZeroStratum O (δ * j) N (r ^ j)) ×ˢ
        {U : Coeff O (n - δ * j) N | ¬ r ∣ polyOf (resVec hN U)})
      {ρ : Coeff O n N | r ^ j ∣ polyOf (resVec hN ρ)
        ∧ ¬ r ^ (j + 1) ∣ polyOf (resVec hN ρ)} := by
  classical
  letI : Nontrivial (Res O N) := nontrivial_res O hN
  have he : δ * (j + 1) = δ * j + δ := by ring
  have hle : δ * j + (n - δ * j) ≤ n := by omega
  have hdegj : (r ^ j).natDegree = δ * j := by
    rw [Polynomial.natDegree_pow, hrd, Nat.mul_comm]
  -- the residual of a parametrized product
  have hres : ∀ P : Coeff O (δ * j) N, P ∈ levelZeroStratum O (δ * j) N (r ^ j) →
      ∀ U : Coeff O (n - δ * j) N,
      polyOf (resVec hN (prodVecAt n P U)) = r ^ j * polyOf (resVec hN U) := by
    intro P hP U
    rw [← map_polyOf_resVec, polyOf_prodVecAt hN hle, Polynomial.map_mul, map_monicPoly,
      map_polyOf,
      show (monicPoly fun i => resMap O hN (P i)) = monicPoly (resVec hN P) from rfl,
      show (polyOf fun i => resMap O hN (U i)) = polyOf (resVec hN U) from rfl,
      (mem_levelZeroStratum_iff_monicPoly_resVec hN _ P).1 hP]
  have hmapsTo : Set.MapsTo
      (fun p : Coeff O (δ * j) N × Coeff O (n - δ * j) N => prodVecAt n p.1 p.2)
      ((levelZeroStratum O (δ * j) N (r ^ j)) ×ˢ
        {U : Coeff O (n - δ * j) N | ¬ r ∣ polyOf (resVec hN U)})
      {ρ : Coeff O n N | r ^ j ∣ polyOf (resVec hN ρ)
        ∧ ¬ r ^ (j + 1) ∣ polyOf (resVec hN ρ)} := by
    rintro ⟨P, U⟩ ⟨hP, hU⟩
    have h1 := hres P hP U
    refine ⟨⟨polyOf (resVec hN U), h1⟩, fun hdvd => ?_⟩
    rw [h1, pow_succ] at hdvd
    exact hU ((mul_dvd_mul_iff_left (pow_ne_zero j hr.ne_zero)).1 hdvd)
  have hinjOn : Set.InjOn
      (fun p : Coeff O (δ * j) N × Coeff O (n - δ * j) N => prodVecAt n p.1 p.2)
      ((levelZeroStratum O (δ * j) N (r ^ j)) ×ˢ
        {U : Coeff O (n - δ * j) N | ¬ r ∣ polyOf (resVec hN U)}) := by
    rintro ⟨P₁, U₁⟩ ⟨hP₁, hU₁⟩ ⟨P₂, U₂⟩ ⟨hP₂, hU₂⟩ heq
    simp only at heq
    have hpoly : monicPoly P₁ * polyOf U₁ = monicPoly P₂ * polyOf U₂ := by
      rw [← polyOf_prodVecAt hN hle P₁ U₁, ← polyOf_prodVecAt hN hle P₂ U₂, heq]
    have hcop : IsCoprime (monicPoly P₁) (polyOf U₂) := by
      refine isCoprime_of_isCoprime_resMap hN ?_
      rw [map_monicPoly, map_polyOf,
        show (monicPoly fun i => resMap O hN (P₁ i)) = monicPoly (resVec hN P₁) from rfl,
        show (polyOf fun i => resMap O hN (U₂ i)) = polyOf (resVec hN U₂) from rfl,
        (mem_levelZeroStratum_iff_monicPoly_resVec hN _ P₁).1 hP₁]
      exact IsCoprime.pow_left (hr.coprime_iff_not_dvd.2 hU₂)
    have hdvd : monicPoly P₁ ∣ monicPoly P₂ * polyOf U₂ := ⟨polyOf U₁, hpoly.symm⟩
    have hPP : monicPoly P₁ = monicPoly P₂ :=
      monic_dvd_monic_eq (monicPoly_monic_ring P₁) (monicPoly_monic_ring P₂)
        (by rw [monicPoly_natDegree_ring, monicPoly_natDegree_ring])
        (hcop.dvd_of_dvd_mul_right hdvd)
    have hP12 : P₁ = P₂ := by
      funext i
      have hco := congrArg (fun p => Polynomial.coeff p (i : ℕ)) hPP
      simpa [monicPoly_coeff_lt_ring _ i.isLt] using hco
    have hV : polyOf U₁ = polyOf U₂ := by
      rw [hPP] at hpoly
      exact (monicPoly_monic_ring P₂).isRegular.left hpoly
    have hU12 : U₁ = U₂ := by
      funext i
      have hco := congrArg (fun p => Polynomial.coeff p (i : ℕ)) hV
      simpa [polyOf_coeff_lt _ i.isLt] using hco
    rw [hP12, hU12]
  refine ⟨hmapsTo, hinjOn, ?_⟩
  -- SurjOn by counting
  have hS₁ : Nat.card (levelZeroStratum O (δ * j) N (r ^ j))
      = residueCard O ^ (δ * j * (N - 1)) :=
    card_levelZeroStratum hN (hrm.pow j) hdegj
  have hS₂ : Nat.card {U : Coeff O (n - δ * j) N | ¬ r ∣ polyOf (resVec hN U)}
      = residueCard O ^ ((n - δ * j) * (N - 1))
        * Nat.card {w : Fin (n - δ * j) → ResidueField O | ¬ r ∣ polyOf w} :=
    card_box_residual_pred hN (fun w => ¬ r ∣ polyOf w)
  have hS₂' : Nat.card {w : Fin (n - δ * j) → ResidueField O | ¬ r ∣ polyOf w}
      = residueCard O ^ (n - δ * j) - residueCard O ^ (n - δ * j - δ) :=
    card_coprime_residual (by omega) hrm hrd
  have hT : Nat.card {ρ : Coeff O n N | r ^ j ∣ polyOf (resVec hN ρ)
        ∧ ¬ r ^ (j + 1) ∣ polyOf (resVec hN ρ)}
      = residueCard O ^ (n * (N - 1))
        * Nat.card {w : Fin n → ResidueField O |
            r ^ j ∣ polyOf w ∧ ¬ r ^ (j + 1) ∣ polyOf w} :=
    card_box_residual_pred hN (fun w => r ^ j ∣ polyOf w ∧ ¬ r ^ (j + 1) ∣ polyOf w)
  have hT' : Nat.card {w : Fin n → ResidueField O |
        r ^ j ∣ polyOf w ∧ ¬ r ^ (j + 1) ∣ polyOf w}
      = residueCard O ^ (n - δ * j) - residueCard O ^ (n - δ * (j + 1)) :=
    card_content_residual hjn hrm hrd
  intro ρ hρ
  have himage : ((fun p : Coeff O (δ * j) N × Coeff O (n - δ * j) N =>
        prodVecAt n p.1 p.2) ''
      ((levelZeroStratum O (δ * j) N (r ^ j)) ×ˢ
        {U : Coeff O (n - δ * j) N | ¬ r ∣ polyOf (resVec hN U)}))
      = {ρ : Coeff O n N | r ^ j ∣ polyOf (resVec hN ρ)
          ∧ ¬ r ^ (j + 1) ∣ polyOf (resVec hN ρ)} := by
    refine Set.eq_of_subset_of_ncard_le (Set.image_subset_iff.mpr hmapsTo) ?_
      (Set.toFinite _)
    rw [Set.InjOn.ncard_image hinjOn, ← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq,
      natCard_prod_set, hS₁, hS₂, hS₂', hT, hT']
    apply le_of_eq
    have e2 : n - δ * (j + 1) = n - δ * j - δ := by omega
    have e3 : δ * j * (N - 1) + (n - δ * j) * (N - 1) = n * (N - 1) := by
      rw [← Nat.add_mul]
      congr 1
      omega
    rw [← mul_assoc, ← pow_add, e3, e2]
  rw [← himage] at hρ
  exact hρ

end PrimaryFactor

/-! ## §3c — the frame division bijection at a stratified monic divisor -/

section FrameDivision

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)]

/-- The quotient coefficient window of `monicPoly F` by `monicPoly P`. -/
def quotVecAt {d n N : ℕ} (P : Coeff O d N) (F : Coeff O n N) : Coeff O (n - d) N :=
  fun i => (monicPoly F /ₘ monicPoly P).coeff (i : ℕ)

/-- The remainder coefficient window of `monicPoly F` by `monicPoly P`. -/
def remVecAt {d n N : ℕ} (P : Coeff O d N) (F : Coeff O n N) : Coeff O d N :=
  fun i => (monicPoly F %ₘ monicPoly P).coeff (i : ℕ)

theorem polyOf_remVecAt {d n N : ℕ} (hN : 0 < N) (h0 : 0 < d)
    (P : Coeff O d N) (F : Coeff O n N) :
    polyOf (remVecAt P F) = monicPoly F %ₘ monicPoly P := by
  letI : Nontrivial (Res O N) := nontrivial_res O hN
  have hne1 : monicPoly P ≠ 1 := by
    intro h
    have hd := monicPoly_natDegree_ring (R := Res O N) P
    rw [h, Polynomial.natDegree_one] at hd
    omega
  have hdeg : (monicPoly F %ₘ monicPoly P).natDegree < d := by
    have h := Polynomial.natDegree_modByMonic_lt (monicPoly F) (monicPoly_monic_ring P) hne1
    rwa [monicPoly_natDegree_ring] at h
  exact polyOf_eq_self hdeg

/-- The quotient of stratified monic frames is monic of the full complementary degree. -/
theorem quot_monic_natDegree {d n N : ℕ} (hN : 0 < N) (h0 : 0 < d) (hdn : d ≤ n)
    (P : Coeff O d N) (F : Coeff O n N) :
    (monicPoly F /ₘ monicPoly P).Monic
      ∧ (monicPoly F /ₘ monicPoly P).natDegree = n - d := by
  letI : Nontrivial (Res O N) := nontrivial_res O hN
  have hPm : (monicPoly P).Monic := monicPoly_monic_ring P
  have hPd : (monicPoly P).natDegree = d := monicPoly_natDegree_ring P
  have hFd : (monicPoly F).natDegree = n := monicPoly_natDegree_ring F
  have hQd : (monicPoly F /ₘ monicPoly P).natDegree = n - d := by
    rw [Polynomial.natDegree_divByMonic _ hPm, hPd, hFd]
  have hne1 : monicPoly P ≠ 1 := by
    intro h
    rw [h, Polynomial.natDegree_one] at hPd
    omega
  -- the leading coefficient of the quotient is the top coefficient of `F`
  have hsplit := Polynomial.modByMonic_add_div (monicPoly F) (monicPoly P)
  have hcoeffn : (monicPoly P * (monicPoly F /ₘ monicPoly P)).coeff n = 1 := by
    have h1 : (monicPoly F).coeff n = 1 := by
      have := (monicPoly_monic_ring (R := Res O N) F).coeff_natDegree
      rwa [hFd] at this
    have h2 : (monicPoly F %ₘ monicPoly P).coeff n = 0 := by
      refine Polynomial.coeff_eq_zero_of_natDegree_lt ?_
      have h := Polynomial.natDegree_modByMonic_lt (monicPoly F) hPm hne1
      rw [hPd] at h
      omega
    have h3 := congrArg (fun p => Polynomial.coeff p n) hsplit
    simp only [Polynomial.coeff_add] at h3
    rw [h1] at h3
    rw [h2, zero_add] at h3
    exact h3
  have hlead : (monicPoly F /ₘ monicPoly P).leadingCoeff = 1 := by
    have h4 := Polynomial.coeff_mul_degree_add_degree (monicPoly P)
      (monicPoly F /ₘ monicPoly P)
    rw [hPd, hQd, (by omega : d + (n - d) = n), hcoeffn, hPm.leadingCoeff, one_mul] at h4
    exact h4.symm
  exact ⟨hlead, hQd⟩

theorem monicPoly_quotVecAt {d n N : ℕ} (hN : 0 < N) (h0 : 0 < d) (hdn : d ≤ n)
    (P : Coeff O d N) (F : Coeff O n N) :
    monicPoly (quotVecAt P F) = monicPoly F /ₘ monicPoly P := by
  letI : Nontrivial (Res O N) := nontrivial_res O hN
  obtain ⟨hm, hd⟩ := quot_monic_natDegree hN h0 hdn P F
  exact monicPoly_coeff_self_ring hm hd

/-- ★ **THE FRAME DIVISION BIJECTION**: division by a stratified monic `P` (residual `s`)
identifies the `s·t`-stratum frames with (monic `t`-stratum quotients) × (zero-residual
remainders). -/
theorem bijOn_divVecAt {d n N : ℕ} (hN : 0 < N) (h0 : 0 < d) (hdn : d ≤ n)
    {s t : Polynomial (ResidueField O)} (hs : s.Monic) (hsd : s.natDegree = d)
    {P : Coeff O d N} (hP : P ∈ levelZeroStratum O d N s) :
    Set.BijOn (fun F : Coeff O n N => (quotVecAt P F, remVecAt P F))
      (levelZeroStratum O n N (s * t))
      ((levelZeroStratum O (n - d) N t) ×ˢ
        {R : Coeff O d N | resVec hN R = 0}) := by
  classical
  letI : Nontrivial (Res O N) := nontrivial_res O hN
  have hPm : (monicPoly P).Monic := monicPoly_monic_ring P
  have hPd : (monicPoly P).natDegree = d := monicPoly_natDegree_ring P
  have hPres : monicPoly (resVec hN P) = s :=
    (mem_levelZeroStratum_iff_monicPoly_resVec hN s P).1 hP
  have hmapP : (monicPoly P).map (resMap O hN) = s := by
    rw [map_monicPoly,
      show (monicPoly fun i => resMap O hN (P i)) = monicPoly (resVec hN P) from rfl,
      hPres]
  have hbotlt : (0 : Polynomial (ResidueField O)).degree < s.degree := by
    rw [Polynomial.degree_zero]
    exact bot_lt_iff_ne_bot.mpr fun hbot => hs.ne_zero (Polynomial.degree_eq_bot.1 hbot)
  -- the residual division reader
  have hkey : ∀ F : Coeff O n N,
      F ∈ levelZeroStratum O n N (s * t) ↔
        (monicPoly F /ₘ monicPoly P).map (resMap O hN) = t
          ∧ (monicPoly F %ₘ monicPoly P).map (resMap O hN) = 0 := by
    intro F
    have hsplit := Polynomial.modByMonic_add_div (monicPoly F) (monicPoly P)
    have hmapsplit : (monicPoly F).map (resMap O hN)
        = (monicPoly F %ₘ monicPoly P).map (resMap O hN)
          + s * (monicPoly F /ₘ monicPoly P).map (resMap O hN) := by
      conv_lhs => rw [← hsplit]
      rw [Polynomial.map_add, Polynomial.map_mul, hmapP]
    have hdegrem : ((monicPoly F %ₘ monicPoly P).map (resMap O hN)).degree < s.degree := by
      have h1 : (monicPoly F %ₘ monicPoly P).degree < (monicPoly P).degree :=
        Polynomial.degree_modByMonic_lt _ hPm
      have h2 : ((monicPoly F %ₘ monicPoly P).map (resMap O hN)).degree
          ≤ (monicPoly F %ₘ monicPoly P).degree := Polynomial.degree_map_le
      have h3 : (monicPoly P).degree = s.degree := by
        rw [Polynomial.degree_eq_natDegree hPm.ne_zero,
          Polynomial.degree_eq_natDegree hs.ne_zero, hPd, hsd]
      exact lt_of_le_of_lt h2 (h3 ▸ h1)
    rw [mem_levelZeroStratum_iff_monicPoly_resVec hN]
    constructor
    · intro hF
      have hmapF : (monicPoly F).map (resMap O hN) = s * t := by
        rw [map_monicPoly,
          show (monicPoly fun i => resMap O hN (F i)) = monicPoly (resVec hN F) from rfl,
          hF]
      have huniq := Polynomial.div_modByMonic_unique
        ((monicPoly F /ₘ monicPoly P).map (resMap O hN))
        ((monicPoly F %ₘ monicPoly P).map (resMap O hN)) hs
        ⟨by rw [← hmapsplit, hmapF], hdegrem⟩
      have hst := Polynomial.div_modByMonic_unique t 0 hs ⟨by rw [zero_add], hbotlt⟩
      exact ⟨huniq.1.symm.trans hst.1, huniq.2.symm.trans hst.2⟩
    · rintro ⟨hq, hr⟩
      have hthis : (monicPoly F).map (resMap O hN) = s * t := by
        rw [hmapsplit, hq, hr, zero_add]
      rw [map_monicPoly,
        show (monicPoly fun i => resMap O hN (F i)) = monicPoly (resVec hN F) from rfl]
        at hthis
      exact hthis
  refine ⟨?_, ?_, ?_⟩
  · -- MapsTo
    intro F hF
    have h1 := (hkey F).1 hF
    constructor
    · rw [mem_levelZeroStratum_iff_monicPoly_resVec hN]
      rw [show monicPoly (resVec hN (quotVecAt P F))
            = (monicPoly (quotVecAt P F)).map (resMap O hN) from (map_monicPoly _ _).symm,
        monicPoly_quotVecAt hN h0 hdn]
      exact h1.1
    · show resVec hN (remVecAt P F) = 0
      have h2 : polyOf (resVec hN (remVecAt P F)) = 0 := by
        rw [← map_polyOf_resVec, polyOf_remVecAt hN h0]
        exact h1.2
      by_contra hne
      exact polyOf_resVec_ne_zero hN hne h2
  · -- InjOn
    intro F₁ hF₁ F₂ hF₂ heq
    simp only [Prod.mk.injEq] at heq
    have hpoly : monicPoly F₁ = monicPoly F₂ := by
      have e1 := Polynomial.modByMonic_add_div (monicPoly F₁) (monicPoly P)
      have e2 := Polynomial.modByMonic_add_div (monicPoly F₂) (monicPoly P)
      have hq' : monicPoly F₁ /ₘ monicPoly P = monicPoly F₂ /ₘ monicPoly P := by
        rw [← monicPoly_quotVecAt hN h0 hdn P F₁, ← monicPoly_quotVecAt hN h0 hdn P F₂,
          heq.1]
      have hr' : monicPoly F₁ %ₘ monicPoly P = monicPoly F₂ %ₘ monicPoly P := by
        rw [← polyOf_remVecAt hN h0 P F₁, ← polyOf_remVecAt hN h0 P F₂, heq.2]
      rw [← e1, ← e2, hq', hr']
    funext i
    have hco := congrArg (fun p => Polynomial.coeff p (i : ℕ)) hpoly
    simpa [monicPoly_coeff_lt_ring _ i.isLt] using hco
  · -- SurjOn: direct construction by recomposition
    rintro ⟨Q, R⟩ ⟨hQ, hR⟩
    have hR0 : resVec hN R = 0 := hR
    have hQm : (monicPoly Q).Monic := monicPoly_monic_ring Q
    have hQd : (monicPoly Q).natDegree = n - d := monicPoly_natDegree_ring Q
    set X : Polynomial (Res O N) := polyOf R + monicPoly P * monicPoly Q with hX
    have hPQm : (monicPoly P * monicPoly Q).Monic := hPm.mul hQm
    have hPQd : (monicPoly P * monicPoly Q).natDegree = n := by
      rw [hPm.natDegree_mul hQm, hPd, hQd]
      omega
    have hRdeg : (polyOf R).degree < (monicPoly P * monicPoly Q).degree := by
      refine lt_of_lt_of_le (polyOf_degree_lt R) ?_
      rw [Polynomial.degree_eq_natDegree hPQm.ne_zero, hPQd]
      exact_mod_cast hdn
    have hXm : X.Monic := by
      rw [hX, add_comm (polyOf R) (monicPoly P * monicPoly Q)]
      exact hPQm.add_of_left hRdeg
    have hXd : X.natDegree = n := by
      have hdeg : X.degree = (monicPoly P * monicPoly Q).degree := by
        rw [hX, add_comm (polyOf R) (monicPoly P * monicPoly Q)]
        exact Polynomial.degree_add_eq_left_of_degree_lt hRdeg
      have hnd := Polynomial.natDegree_eq_of_degree_eq hdeg
      rw [hnd, hPQd]
    set F : Coeff O n N := fun i => X.coeff (i : ℕ) with hF
    have hXF : monicPoly F = X := monicPoly_coeff_self_ring hXm hXd
    have hdiv := Polynomial.div_modByMonic_unique (f := X) (monicPoly Q) (polyOf R) hPm
      ⟨hX.symm, by
        refine lt_of_lt_of_le (polyOf_degree_lt R) ?_
        rw [Polynomial.degree_eq_natDegree hPm.ne_zero, hPd]⟩
    refine ⟨F, ?_, ?_⟩
    · -- F lies in the (s·t)-stratum
      refine (hkey F).2 ⟨?_, ?_⟩
      · rw [hXF, hdiv.1, map_monicPoly,
          show (monicPoly fun i => resMap O hN (Q i)) = monicPoly (resVec hN Q) from rfl]
        exact (mem_levelZeroStratum_iff_monicPoly_resVec hN t Q).1 hQ
      · rw [hXF, hdiv.2, map_polyOf_resVec, hR0]
        unfold Uniformity.Density.IFCG61.polyOf
        simp
    · -- the division data recovers (Q, R)
      have hq : quotVecAt P F = Q := by
        funext i
        show (monicPoly F /ₘ monicPoly P).coeff (i : ℕ) = Q i
        rw [hXF, hdiv.1, monicPoly_coeff_lt_ring _ i.isLt]
      have hr : remVecAt P F = R := by
        funext i
        show (monicPoly F %ₘ monicPoly P).coeff (i : ℕ) = R i
        rw [hXF, hdiv.2, polyOf_coeff_lt _ i.isLt]
      show (quotVecAt P F, remVecAt P F) = (Q, R)
      rw [hq, hr]


end FrameDivision

/-! ## §3d — counting helpers and the zero-residual depth shift -/

section PeelCounting

attribute [local instance] Classical.propDecidable

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)]

/-- Census transport along a `BijOn`: a condition read through the map counts the same
on both sides. -/
private theorem card_setOf_bijOn {α β : Type*} {f : α → β} {s : Set α} {t : Set β}
    (h : Set.BijOn f s t) (Q : β → Prop) :
    Nat.card {x : α | x ∈ s ∧ Q (f x)} = Nat.card {y : β | y ∈ t ∧ Q y} := by
  refine Nat.card_congr (Set.BijOn.equiv f ⟨?_, ?_, ?_⟩)
  · rintro x ⟨hx, hQ⟩
    exact ⟨h.mapsTo hx, hQ⟩
  · exact h.injOn.mono fun x hx => hx.1
  · rintro y ⟨hy, hQ⟩
    obtain ⟨x, hxs, rfl⟩ := h.surjOn hy
    exact ⟨x, ⟨hxs, hQ⟩, rfl⟩

/-- The fibre decomposition of a pair census over its first coordinate. -/
private theorem card_pairSet_fiber {α β : Type*} [Fintype α] [Finite β]
    (S : Set α) (T : α → Set β) :
    Nat.card {d : α × β | d.1 ∈ S ∧ d.2 ∈ T d.1}
      = ∑ c ∈ S.toFinset, Nat.card (T c) := by
  classical
  have e : {d : α × β | d.1 ∈ S ∧ d.2 ∈ T d.1}
      ≃ Σ c : ↥S.toFinset, ↥(T (c : α)) :=
    { toFun := fun d => ⟨⟨d.val.1, Set.mem_toFinset.mpr d.prop.1⟩, ⟨d.val.2, d.prop.2⟩⟩
      invFun := fun p => ⟨(p.1.val, p.2.val), ⟨Set.mem_toFinset.mp p.1.prop, p.2.prop⟩⟩
      left_inv := fun d => rfl
      right_inv := fun p => rfl }
  rw [Nat.card_congr e, Nat.card_sigma, ← Finset.sum_coe_sort S.toFinset
    (fun c => Nat.card (T c))]

/-- Fubini for conditioned pair censuses. -/
private theorem sum_card_fiber_comm {α β : Type*} [Fintype α] [Fintype β]
    (S : Set α) (T : Set β) (Q : α → β → Prop) :
    ∑ a ∈ S.toFinset, Nat.card {b : β | b ∈ T ∧ Q a b}
      = ∑ b ∈ T.toFinset, Nat.card {a : α | a ∈ S ∧ Q a b} := by
  have h1 := card_pairSet_fiber S (fun a => {b : β | b ∈ T ∧ Q a b})
  have h2 := card_pairSet_fiber T (fun b => {a : α | a ∈ S ∧ Q a b})
  have h3 : Nat.card {d : α × β | d.1 ∈ S ∧ d.2 ∈ {b : β | b ∈ T ∧ Q d.1 b}}
      = Nat.card {d : β × α | d.1 ∈ T ∧ d.2 ∈ {a : α | a ∈ S ∧ Q a d.1}} := by
    refine Nat.card_congr
      ⟨fun d => ⟨(d.val.2, d.val.1), ⟨d.prop.2.1, d.prop.1, d.prop.2.2⟩⟩,
       fun d => ⟨(d.val.2, d.val.1), ⟨d.prop.2.1, d.prop.1, d.prop.2.2⟩⟩,
       fun d => rfl, fun d => rfl⟩
  rw [← h1, ← h2, h3]

/-- ★ **THE ZERO-RESIDUAL DEPTH SHIFT** (the finite-level Weierstrass peel engine): the
zero-residual slice of the stratified pair census at depth `v` is `q^{−m}` times the full
stratified census at depth `v − m` (`v < N`). -/
theorem card_zeroRes_stratumDepth {m N v : ℕ} (hN : 0 < N) (hv : v < N)
    (g : Polynomial (ResidueField O)) :
    residueCard O ^ m
        * Nat.card {p : Coeff O m N × Coeff O m N |
            p.1 ∈ levelZeroStratum O m N g
              ∧ (resVec hN p.2 = 0 ∧ resOrd (redRes p.1 p.2) = v)}
      = if m ≤ v then Nat.card (stratumDepthSet O m N (v - m) g) else 0 := by
  classical
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible O
  haveI : Fintype (Coeff O m N) := Fintype.ofFinite _
  have hsets : {p : Coeff O m N × Coeff O m N |
      p.1 ∈ levelZeroStratum O m N g ∧ (resVec hN p.2 = 0 ∧ resOrd (redRes p.1 p.2) = v)}
      = {d : Coeff O m N × Coeff O m N | d.1 ∈ levelZeroStratum O m N g
          ∧ d.2 ∈ {b : Coeff O m N | resVec hN b = 0 ∧ resOrd (redRes d.1 b) = v}} := rfl
  rw [hsets, card_pairSet_fiber (levelZeroStratum O m N g)
    (fun c => {b : Coeff O m N | resVec hN b = 0 ∧ resOrd (redRes c b) = v}),
    Finset.mul_sum]
  -- the per-frame scale transport
  have hper : ∀ c : Coeff O m N,
      residueCard O ^ m
          * Nat.card {b : Coeff O m N | resVec hN b = 0 ∧ resOrd (redRes c b) = v}
        = if m ≤ v then Nat.card (frameDepthSet O m N (v - m) c) else 0 := by
    intro c
    have htrans := card_scaleBox_preimage hπ hN
      {b : Coeff O m N | resVec hN b = 0 ∧ resOrd (redRes c b) = v}
      (fun b hb => hb.1)
    have hpre : (scaleBox π m N) ⁻¹'
        {b : Coeff O m N | resVec hN b = 0 ∧ resOrd (redRes c b) = v}
        = {b' : Coeff O m N | m + resOrd (redRes c b') = v} := by
      ext b'
      simp only [Set.mem_preimage, Set.mem_setOf_eq]
      constructor
      · rintro ⟨-, hord⟩
        rw [redRes_scaleBox, resOrd_mk_pow_mul_eq_iff hπ hv] at hord
        exact hord
      · intro hord
        refine ⟨?_, ?_⟩
        · have : scaleBox π m N b' ∈ Set.range (scaleBox π m N) := ⟨b', rfl⟩
          rw [range_scaleBox hπ hN] at this
          exact this
        · rw [redRes_scaleBox, resOrd_mk_pow_mul_eq_iff hπ hv]
          exact hord
    rw [← htrans, hpre]
    rcases Nat.lt_or_ge v m with hvm | hvm
    · rw [if_neg (by omega)]
      have hempty : {b' : Coeff O m N | m + resOrd (redRes c b') = v} = ∅ := by
        ext b'
        simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
        omega
      rw [hempty, Nat.card_coe_set_eq, Set.ncard_empty]
    · rw [if_pos hvm]
      have heq : {b' : Coeff O m N | m + resOrd (redRes c b') = v}
          = frameDepthSet O m N (v - m) c := by
        ext b'
        simp only [Set.mem_setOf_eq, frameDepthSet]
        omega
      rw [heq]
  by_cases hvm : m ≤ v
  · rw [Finset.sum_congr rfl fun c _ => (hper c).trans (if_pos hvm), if_pos hvm,
      card_stratumDepthSet_eq_sum]
  · rw [Finset.sum_congr rfl fun c _ => (hper c).trans (if_neg hvm), if_neg hvm,
      Finset.sum_const_zero]

/-- The size-`0` base census: the empty frame–box pair has reduced resultant `1`, so the
census is `1` at depth `0` and empty otherwise. -/
theorem card_stratumDepthSet_zero {N v : ℕ} (hN : 0 < N) :
    Nat.card (stratumDepthSet O 0 N v (1 : Polynomial (ResidueField O)))
      = if v = 0 then 1 else 0 := by
  classical
  letI : Nontrivial (Res O N) := nontrivial_res O hN
  have hres : ∀ c b : Coeff O 0 N, redRes c b = 1 := by
    intro c b
    show Polynomial.resultant (monicPoly c) (polyOf b) 0 0 = 1
    have hb : polyOf b = 0 := by
      unfold Uniformity.Density.IFCG61.polyOf
      simp
    rw [hb, Polynomial.resultant_zero_right, pow_zero, pow_zero, one_mul]
  have hord : ∀ c b : Coeff O 0 N, resOrd (redRes c b) = 0 := by
    intro c b
    rw [hres]
    by_contra hne
    have h1 : resMap O hN (1 : Res O N) = 0 := (resMap_eq_zero_iff hN 1).2 (by omega)
    rw [map_one] at h1
    exact one_ne_zero h1
  have hmem : ∀ c : Coeff O 0 N,
      c ∈ levelZeroStratum O 0 N (1 : Polynomial (ResidueField O)) := by
    intro c
    rw [mem_levelZeroStratum_iff_monicPoly_resVec hN]
    show monicPoly (resVec hN c) = 1
    unfold monicPoly
    simp
  by_cases hv : v = 0
  · subst hv
    rw [if_pos rfl]
    have hset : stratumDepthSet O 0 N 0 (1 : Polynomial (ResidueField O)) = Set.univ := by
      ext p
      simp only [Uniformity.Density.IFCG63.stratumDepthSet, Set.mem_setOf_eq, Set.mem_univ,
        iff_true]
      exact ⟨hmem p.1, hord p.1 p.2⟩
    rw [hset, Nat.card_coe_set_eq, Set.ncard_univ, Nat.card_prod, card_coeff]
    simp
  · rw [if_neg hv]
    have hset : stratumDepthSet O 0 N v (1 : Polynomial (ResidueField O)) = ∅ := by
      ext p
      simp only [Uniformity.Density.IFCG63.stratumDepthSet, Set.mem_setOf_eq,
        Set.mem_empty_iff_false, iff_false]
      rintro ⟨-, hfd⟩
      have hfd' : resOrd (redRes p.1 p.2) = v := hfd
      exact hv (hfd'.symm.trans (hord p.1 p.2))
    rw [hset, Nat.card_coe_set_eq, Set.ncard_empty]

end PeelCounting

/-! ## §3e — the swap–peel: the census condition at a content box localizes to the
`(divisor, remainder)` pair -/

section SwapPeel

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)]

/-- ★ **THE SWAP–PEEL**: for a box `P·U` with `U` of residual coprime to the frame's
residual, the reduced-resultant depth against the frame `F` equals the depth of the
`(P, F mod P)` pair — the `U`-factor is a depth-`0` unit; the swap and the monic
size-drop localize the census to the divisor. -/
theorem resOrd_redRes_prodVecAt {N n d : ℕ} (hN : 0 < N) (hdn : d ≤ n)
    (F : Coeff O n N) (P : Coeff O d N) (U : Coeff O (n - d) N)
    (hcop : IsCoprime (monicPoly (resVec hN F)) (polyOf (resVec hN U))) :
    resOrd (redRes F (prodVecAt n P U)) = resOrd (redRes P (remVecAt P F)) := by
  classical
  letI : Nontrivial (Res O N) := nontrivial_res O hN
  have hMFm : (monicPoly F).Monic := monicPoly_monic_ring F
  have hMFd : (monicPoly F).natDegree = n := monicPoly_natDegree_ring F
  have hMPm : (monicPoly P).Monic := monicPoly_monic_ring P
  have hMPd : (monicPoly P).natDegree = d := monicPoly_natDegree_ring P
  have hUd : (polyOf U).natDegree ≤ n - d :=
    Polynomial.natDegree_le_iff_degree_le.mpr (le_of_lt (polyOf_degree_lt U))
  have hcoF : (monicPoly F).coeff n = 1 := by
    have h := hMFm.coeff_natDegree
    rwa [hMFd] at h
  -- the depth-0 unit leg: the U-factor's residual resultant is nonzero
  have hres0 : resOrd (Polynomial.resultant (monicPoly F) (polyOf U) n
      ((polyOf U).natDegree)) = 0 := by
    have hmap : resMap O hN (Polynomial.resultant (monicPoly F) (polyOf U) n
        ((polyOf U).natDegree))
        = Polynomial.resultant (monicPoly (resVec hN F)) (polyOf (resVec hN U)) n
            ((polyOf U).natDegree) := by
      rw [← Polynomial.resultant_map_map (monicPoly F) (polyOf U) n _ (resMap O hN),
        map_monicPoly, map_polyOf]
      rfl
    have hGm : (monicPoly (resVec hN F)).Monic := monicPoly_monic_ring _
    have hGd : (monicPoly (resVec hN F)).natDegree = n := monicPoly_natDegree_ring _
    have hWle : (polyOf (resVec hN U)).natDegree ≤ (polyOf U).natDegree := by
      rw [← map_polyOf_resVec hN]
      exact Polynomial.natDegree_map_le
    have hcoG : (monicPoly (resVec hN F)).coeff n = 1 := by
      have h := hGm.coeff_natDegree
      rwa [hGd] at h
    have hbridge : Polynomial.resultant (monicPoly (resVec hN F)) (polyOf (resVec hN U))
        n ((polyOf U).natDegree)
        = Polynomial.resultant (monicPoly (resVec hN F)) (polyOf (resVec hN U))
            n ((polyOf (resVec hN U)).natDegree) := by
      have hb := Polynomial.resultant_add_right_deg (f := monicPoly (resVec hN F))
        (g := polyOf (resVec hN U)) (m := n) (n := (polyOf (resVec hN U)).natDegree)
        ((polyOf U).natDegree - (polyOf (resVec hN U)).natDegree) le_rfl
      rw [show (polyOf (resVec hN U)).natDegree
          + ((polyOf U).natDegree - (polyOf (resVec hN U)).natDegree)
          = (polyOf U).natDegree from by omega] at hb
      rw [hb, hcoG, one_pow, one_mul]
    have hne : Polynomial.resultant (monicPoly (resVec hN F)) (polyOf (resVec hN U))
        n ((polyOf (resVec hN U)).natDegree) ≠ 0 := by
      have hne0 := Polynomial.resultant_ne_zero (monicPoly (resVec hN F))
        (polyOf (resVec hN U)) hcop
      rwa [hGd] at hne0
    have hmapne : resMap O hN (Polynomial.resultant (monicPoly F) (polyOf U) n
        ((polyOf U).natDegree)) ≠ 0 := by
      rw [hmap, hbridge]
      exact hne
    by_contra hc
    exact hmapne ((resMap_eq_zero_iff hN _).2 (by omega))
  have hR0 : resOrd ((1 : Res O N)) = 0 := by
    by_contra hc
    have h1 : resMap O hN (1 : Res O N) = 0 := (resMap_eq_zero_iff hN 1).2 (by omega)
    rw [map_one] at h1
    exact one_ne_zero h1
  rcases Nat.eq_zero_or_pos d with rfl | hd0
  · -- the degree-0 divisor: both sides are depth 0
    have hP1 : monicPoly P = 1 := by
      unfold monicPoly
      simp
    have hL : redRes F (prodVecAt n P U)
        = Polynomial.resultant (monicPoly F) (polyOf U) n n := by
      show Polynomial.resultant (monicPoly F) (polyOf (prodVecAt n P U)) n n = _
      rw [polyOf_prodVecAt hN (by omega), hP1, one_mul]
    have hLbridge : Polynomial.resultant (monicPoly F) (polyOf U) n n
        = Polynomial.resultant (monicPoly F) (polyOf U) n ((polyOf U).natDegree) := by
      have hb := Polynomial.resultant_add_right_deg (f := monicPoly F) (g := polyOf U)
        (m := n) (n := (polyOf U).natDegree) (n - (polyOf U).natDegree) le_rfl
      rw [show (polyOf U).natDegree + (n - (polyOf U).natDegree) = n from by omega] at hb
      rw [hb, hcoF, one_pow, one_mul]
    have hR : redRes P (remVecAt P F) = 1 := by
      show Polynomial.resultant (monicPoly P) (polyOf (remVecAt P F)) 0 0 = 1
      have hb : polyOf (remVecAt P F) = 0 := by
        unfold Uniformity.Density.IFCG61.polyOf
        simp
      rw [hb, Polynomial.resultant_zero_right, pow_zero, pow_zero, one_mul]
    rw [hL, hLbridge, hres0, hR, hR0]
  · -- the main chain: window drop, split, swap, monic size drop
    have hle : d + (n - d) ≤ n := by omega
    have h1 : redRes F (prodVecAt n P U)
        = Polynomial.resultant (monicPoly F) (monicPoly P * polyOf U) n n := by
      show Polynomial.resultant (monicPoly F) (polyOf (prodVecAt n P U)) n n = _
      rw [polyOf_prodVecAt hN hle]
    have h2 : Polynomial.resultant (monicPoly F) (monicPoly P * polyOf U) n n
        = Polynomial.resultant (monicPoly F) (monicPoly P * polyOf U) n
            ((monicPoly P).natDegree + (polyOf U).natDegree) := by
      have hb := Polynomial.resultant_add_right_deg (f := monicPoly F)
        (g := monicPoly P * polyOf U) (m := n)
        (n := (monicPoly P).natDegree + (polyOf U).natDegree)
        (n - ((monicPoly P).natDegree + (polyOf U).natDegree))
        Polynomial.natDegree_mul_le
      rw [show (monicPoly P).natDegree + (polyOf U).natDegree
          + (n - ((monicPoly P).natDegree + (polyOf U).natDegree)) = n from by
        rw [hMPd]; omega] at hb
      rw [hb, hcoF, one_pow, one_mul]
    have h3 := Polynomial.resultant_mul_right (monicPoly F) (monicPoly P) (polyOf U) n
      (le_of_eq hMFd)
    have h4 := Polynomial.resultant_comm (monicPoly F) (monicPoly P) n
      ((monicPoly P).natDegree)
    have h5 : Polynomial.resultant (monicPoly P) (monicPoly F) ((monicPoly P).natDegree) n
        = Polynomial.resultant (monicPoly P) (monicPoly F %ₘ monicPoly P)
            ((monicPoly P).natDegree) ((monicPoly P).natDegree) :=
      resultant_modByMonic_right hMPm (by rw [hMPd]; omega) (le_of_eq hMFd)
        (by rw [hMPd]; omega)
    have h6 : Polynomial.resultant (monicPoly P) (monicPoly F %ₘ monicPoly P)
          ((monicPoly P).natDegree) ((monicPoly P).natDegree)
        = redRes P (remVecAt P F) := by
      rw [hMPd]
      show _ = Polynomial.resultant (monicPoly P) (polyOf (remVecAt P F)) d d
      rw [polyOf_remVecAt hN hd0]
    have hchain : redRes F (prodVecAt n P U)
        = (-1) ^ (n * d)
            * (redRes P (remVecAt P F)
              * Polynomial.resultant (monicPoly F) (polyOf U) n ((polyOf U).natDegree)) := by
      rw [h1, h2, h3, h4, h5, h6, hMPd]
      ring
    rw [hchain, resOrd_isUnit_mul ((isUnit_one.neg : IsUnit (-1 : Res O N)).pow (n * d)),
      resOrd_mul, hres0, Nat.add_zero, min_eq_right (resOrd_le _)]

end SwapPeel

/-! ## §3f — the content-slice localization: the per-`j` term of the peel -/

section ContentSlice

attribute [local instance] Classical.propDecidable

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)]

/-- The empty pair reads depth `0`. -/
private theorem resOrd_redRes_size_zero {N : ℕ} (hN : 0 < N) (c b : Coeff O 0 N) :
    resOrd (redRes c b) = 0 := by
  letI : Nontrivial (Res O N) := nontrivial_res O hN
  have hres : redRes c b = 1 := by
    show Polynomial.resultant (monicPoly c) (polyOf b) 0 0 = 1
    have hb : polyOf b = 0 := by
      unfold Uniformity.Density.IFCG61.polyOf
      simp
    rw [hb, Polynomial.resultant_zero_right, pow_zero, pow_zero, one_mul]
  rw [hres]
  by_contra hc
  have h1 : resMap O hN (1 : Res O N) = 0 := (resMap_eq_zero_iff hN 1).2 (by omega)
  rw [map_one] at h1
  exact one_ne_zero h1

/-- Per-frame localization: the content-`j` box census at depth `v` factors as
(the divisor census at the frame's remainder) × (the coprime box count). -/
private theorem card_content_perF {δ e j N v : ℕ} (hN : 0 < N) (h0 : 0 < δ) (hj : j < e)
    {r : Polynomial (ResidueField O)} (hr : Irreducible r) (hrm : r.Monic)
    (hrd : r.natDegree = δ) {F : Coeff O (δ * e) N}
    (hF : F ∈ levelZeroStratum O (δ * e) N (r ^ e)) :
    Nat.card {ρ : Coeff O (δ * e) N |
        (r ^ j ∣ polyOf (resVec hN ρ) ∧ ¬ r ^ (j + 1) ∣ polyOf (resVec hN ρ))
          ∧ resOrd (redRes F ρ) = v}
      = Nat.card {P : Coeff O (δ * j) N | P ∈ levelZeroStratum O (δ * j) N (r ^ j)
            ∧ resOrd (redRes P (remVecAt P F)) = v}
        * Nat.card {U : Coeff O (δ * e - δ * j) N | ¬ r ∣ polyOf (resVec hN U)} := by
  classical
  have hjn : δ * (j + 1) ≤ δ * e := Nat.mul_le_mul_left δ (by omega)
  have hdn : δ * j ≤ δ * e := Nat.mul_le_mul_left δ (by omega)
  have hFres : monicPoly (resVec hN F) = r ^ e :=
    (mem_levelZeroStratum_iff_monicPoly_resVec hN _ F).1 hF
  -- transport along the product parametrization
  have h1 : Nat.card {ρ : Coeff O (δ * e) N |
        ρ ∈ {ρ : Coeff O (δ * e) N | r ^ j ∣ polyOf (resVec hN ρ)
          ∧ ¬ r ^ (j + 1) ∣ polyOf (resVec hN ρ)}
          ∧ resOrd (redRes F ρ) = v}
      = Nat.card {p : Coeff O (δ * j) N × Coeff O (δ * e - δ * j) N |
          p ∈ (levelZeroStratum O (δ * j) N (r ^ j)) ×ˢ
              {U : Coeff O (δ * e - δ * j) N | ¬ r ∣ polyOf (resVec hN U)}
            ∧ resOrd (redRes F (prodVecAt (δ * e) p.1 p.2)) = v} :=
    (card_setOf_bijOn (bijOn_prodVecAt hN h0 hjn hr hrm hrd)
      (fun ρ => resOrd (redRes F ρ) = v)).symm
  -- the condition localizes to the divisor pair
  have h2 : {p : Coeff O (δ * j) N × Coeff O (δ * e - δ * j) N |
        p ∈ (levelZeroStratum O (δ * j) N (r ^ j)) ×ˢ
            {U : Coeff O (δ * e - δ * j) N | ¬ r ∣ polyOf (resVec hN U)}
          ∧ resOrd (redRes F (prodVecAt (δ * e) p.1 p.2)) = v}
      = {P : Coeff O (δ * j) N | P ∈ levelZeroStratum O (δ * j) N (r ^ j)
            ∧ resOrd (redRes P (remVecAt P F)) = v} ×ˢ
          {U : Coeff O (δ * e - δ * j) N | ¬ r ∣ polyOf (resVec hN U)} := by
    ext ⟨P, U⟩
    simp only [Set.mem_setOf_eq, Set.mem_prod]
    constructor
    · rintro ⟨⟨hP, hU⟩, hord⟩
      rw [resOrd_redRes_prodVecAt hN hdn F P U (hFres ▸
        IsCoprime.pow_left (hr.coprime_iff_not_dvd.2 hU))] at hord
      exact ⟨⟨hP, hord⟩, hU⟩
    · rintro ⟨⟨hP, hord⟩, hU⟩
      refine ⟨⟨hP, hU⟩, ?_⟩
      rw [resOrd_redRes_prodVecAt hN hdn F P U (hFres ▸
        IsCoprime.pow_left (hr.coprime_iff_not_dvd.2 hU))]
      exact hord
  have h0eq : {ρ : Coeff O (δ * e) N |
        (r ^ j ∣ polyOf (resVec hN ρ) ∧ ¬ r ^ (j + 1) ∣ polyOf (resVec hN ρ))
          ∧ resOrd (redRes F ρ) = v}
      = {ρ : Coeff O (δ * e) N |
          ρ ∈ {ρ : Coeff O (δ * e) N | r ^ j ∣ polyOf (resVec hN ρ)
            ∧ ¬ r ^ (j + 1) ∣ polyOf (resVec hN ρ)}
            ∧ resOrd (redRes F ρ) = v} := rfl
  rw [h0eq, h1, h2, natCard_prod_set]

/-- Per-divisor localization: the frames whose remainder census hits depth `v` factor as
(the exponent-`(e−j)` stratum) × (the zero-residual divisor census). -/
private theorem card_content_perP {δ e j N v : ℕ} (hN : 0 < N) (h0 : 0 < δ) (hj : j < e)
    {r : Polynomial (ResidueField O)} (hrm : r.Monic) (hrd : r.natDegree = δ)
    {P : Coeff O (δ * j) N} (hP : P ∈ levelZeroStratum O (δ * j) N (r ^ j)) :
    Nat.card {F : Coeff O (δ * e) N | F ∈ levelZeroStratum O (δ * e) N (r ^ e)
          ∧ resOrd (redRes P (remVecAt P F)) = v}
      = Nat.card (levelZeroStratum O (δ * e - δ * j) N (r ^ (e - j)))
        * Nat.card {R : Coeff O (δ * j) N |
            resVec hN R = 0 ∧ resOrd (redRes P R) = v} := by
  classical
  have hdn : δ * j ≤ δ * e := Nat.mul_le_mul_left δ (by omega)
  have hpow : r ^ j * r ^ (e - j) = r ^ e := by
    rw [← pow_add]
    congr 1
    omega
  rcases Nat.eq_zero_or_pos j with rfl | hj0
  · -- degree-0 divisor: the remainder census is the constant depth-0 reader
    show Nat.card {F : Coeff O (δ * e) N | F ∈ levelZeroStratum O (δ * e) N (r ^ e)
          ∧ resOrd (redRes P (remVecAt P F)) = v}
      = Nat.card (levelZeroStratum O (δ * e) N (r ^ e))
        * Nat.card {R : Coeff O (δ * 0) N | resVec hN R = 0 ∧ resOrd (redRes P R) = v}
    have hord : ∀ F : Coeff O (δ * e) N, resOrd (redRes P (remVecAt P F)) = 0 :=
      fun F => resOrd_redRes_size_zero hN P (remVecAt P F)
    have hR0 : ∀ R : Coeff O (δ * 0) N, resVec hN R = 0 := by
      intro R
      funext i
      exact absurd i.isLt (by omega)
    by_cases hv0 : v = 0
    · subst hv0
      have hL : {F : Coeff O (δ * e) N | F ∈ levelZeroStratum O (δ * e) N (r ^ e)
            ∧ resOrd (redRes P (remVecAt P F)) = 0}
          = levelZeroStratum O (δ * e) N (r ^ e) := by
        ext F
        simp only [Set.mem_setOf_eq, and_iff_left_iff_imp]
        exact fun _ => hord F
      have hRset : {R : Coeff O (δ * 0) N | resVec hN R = 0 ∧ resOrd (redRes P R) = 0}
          = Set.univ := by
        ext R
        simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]
        exact ⟨hR0 R, resOrd_redRes_size_zero hN P R⟩
      rw [hL, hRset, Nat.card_coe_set_eq (s := (Set.univ : Set (Coeff O (δ * 0) N))),
        Set.ncard_univ, card_coeff]
      simp
    · have hL : {F : Coeff O (δ * e) N | F ∈ levelZeroStratum O (δ * e) N (r ^ e)
            ∧ resOrd (redRes P (remVecAt P F)) = v} = ∅ := by
        ext F
        simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
        rintro ⟨-, hcon⟩
        exact hv0 (hcon.symm.trans (hord F))
      have hRset : {R : Coeff O (δ * 0) N | resVec hN R = 0 ∧ resOrd (redRes P R) = v}
          = ∅ := by
        ext R
        simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
        rintro ⟨-, hcon⟩
        exact hv0 (hcon.symm.trans (resOrd_redRes_size_zero hN P R))
      rw [hL, hRset, Nat.card_coe_set_eq (s := (∅ : Set (Coeff O (δ * e) N))),
        Set.ncard_empty, Nat.card_coe_set_eq (s := (∅ : Set (Coeff O (δ * 0) N))),
        Set.ncard_empty, mul_zero]
  · -- positive-degree divisor: the frame division bijection
    have hd0 : 0 < δ * j := by positivity
    have h1 : Nat.card {F : Coeff O (δ * e) N |
          F ∈ levelZeroStratum O (δ * e) N (r ^ j * r ^ (e - j))
            ∧ resOrd (redRes P ((quotVecAt P F, remVecAt P F).2)) = v}
        = Nat.card {y : Coeff O (δ * e - δ * j) N × Coeff O (δ * j) N |
            y ∈ (levelZeroStratum O (δ * e - δ * j) N (r ^ (e - j))) ×ˢ
                {R : Coeff O (δ * j) N | resVec hN R = 0}
              ∧ resOrd (redRes P y.2) = v} :=
      card_setOf_bijOn
        (bijOn_divVecAt hN hd0 hdn (hrm.pow j)
          (by rw [Polynomial.natDegree_pow, hrd, Nat.mul_comm]) hP)
        (fun y => resOrd (redRes P y.2) = v)
    have h2 : {y : Coeff O (δ * e - δ * j) N × Coeff O (δ * j) N |
          y ∈ (levelZeroStratum O (δ * e - δ * j) N (r ^ (e - j))) ×ˢ
              {R : Coeff O (δ * j) N | resVec hN R = 0}
            ∧ resOrd (redRes P y.2) = v}
        = (levelZeroStratum O (δ * e - δ * j) N (r ^ (e - j))) ×ˢ
            {R : Coeff O (δ * j) N | resVec hN R = 0 ∧ resOrd (redRes P R) = v} := by
      ext ⟨Q, R⟩
      simp only [Set.mem_setOf_eq, Set.mem_prod]
      tauto
    rw [← hpow, h1, h2, natCard_prod_set]

/-- ★ **THE CONTENT-`j` SLICE** of the primary pair census, at its natural `q^{δj}`
scale: localizes through the product parametrization, the swap–peel, the frame
division, and the zero-residual shift to the exponent-`j` primary census at depth
`v − δj`, with the coprime-box and complementary-stratum multiplicities. -/
theorem card_content_slice {δ e j N v : ℕ} (hN : 0 < N) (h0 : 0 < δ) (hj : j < e)
    (hv : v < N) {r : Polynomial (ResidueField O)} (hr : Irreducible r) (hrm : r.Monic)
    (hrd : r.natDegree = δ) :
    residueCard O ^ (δ * j)
        * Nat.card {p : Coeff O (δ * e) N × Coeff O (δ * e) N |
            p.1 ∈ levelZeroStratum O (δ * e) N (r ^ e)
              ∧ ((r ^ j ∣ polyOf (resVec hN p.2) ∧ ¬ r ^ (j + 1) ∣ polyOf (resVec hN p.2))
                ∧ resOrd (redRes p.1 p.2) = v)}
      = (residueCard O ^ (δ * e - δ * j) - residueCard O ^ (δ * e - δ * j - δ))
          * residueCard O ^ (2 * ((δ * e - δ * j) * (N - 1)))
          * (if δ * j ≤ v then Nat.card (stratumDepthSet O (δ * j) N (v - δ * j) (r ^ j))
             else 0) := by
  classical
  haveI : Fintype (Coeff O (δ * e) N) := Fintype.ofFinite _
  haveI : Fintype (Coeff O (δ * j) N) := Fintype.ofFinite _
  have hδm : δ ≤ δ * e - δ * j := by
    have h1 := Nat.mul_sub δ e j
    have h2 : δ * 1 ≤ δ * (e - j) := Nat.mul_le_mul_left δ (by omega)
    have h3 : δ * 1 = δ := Nat.mul_one δ
    omega
  -- fibre over the frame
  have hfib : Nat.card {p : Coeff O (δ * e) N × Coeff O (δ * e) N |
        p.1 ∈ levelZeroStratum O (δ * e) N (r ^ e)
          ∧ ((r ^ j ∣ polyOf (resVec hN p.2) ∧ ¬ r ^ (j + 1) ∣ polyOf (resVec hN p.2))
            ∧ resOrd (redRes p.1 p.2) = v)}
      = ∑ F ∈ (levelZeroStratum O (δ * e) N (r ^ e)).toFinset,
          Nat.card {ρ : Coeff O (δ * e) N |
            (r ^ j ∣ polyOf (resVec hN ρ) ∧ ¬ r ^ (j + 1) ∣ polyOf (resVec hN ρ))
              ∧ resOrd (redRes F ρ) = v} :=
    card_pairSet_fiber (levelZeroStratum O (δ * e) N (r ^ e))
      (fun F => {ρ : Coeff O (δ * e) N |
        (r ^ j ∣ polyOf (resVec hN ρ) ∧ ¬ r ^ (j + 1) ∣ polyOf (resVec hN ρ))
          ∧ resOrd (redRes F ρ) = v})
  -- per-frame localization
  have hperF : ∀ F ∈ (levelZeroStratum O (δ * e) N (r ^ e)).toFinset,
      Nat.card {ρ : Coeff O (δ * e) N |
          (r ^ j ∣ polyOf (resVec hN ρ) ∧ ¬ r ^ (j + 1) ∣ polyOf (resVec hN ρ))
            ∧ resOrd (redRes F ρ) = v}
        = Nat.card {P : Coeff O (δ * j) N | P ∈ levelZeroStratum O (δ * j) N (r ^ j)
              ∧ resOrd (redRes P (remVecAt P F)) = v}
          * Nat.card {U : Coeff O (δ * e - δ * j) N | ¬ r ∣ polyOf (resVec hN U)} :=
    fun F hF => card_content_perF hN h0 hj hr hrm hrd (Set.mem_toFinset.1 hF)
  -- Fubini
  have hfub := sum_card_fiber_comm (levelZeroStratum O (δ * e) N (r ^ e))
    (levelZeroStratum O (δ * j) N (r ^ j))
    (fun F P => resOrd (redRes P (remVecAt P F)) = v)
  -- per-divisor localization
  have hperP : ∀ P ∈ (levelZeroStratum O (δ * j) N (r ^ j)).toFinset,
      Nat.card {F : Coeff O (δ * e) N | F ∈ levelZeroStratum O (δ * e) N (r ^ e)
            ∧ resOrd (redRes P (remVecAt P F)) = v}
        = Nat.card (levelZeroStratum O (δ * e - δ * j) N (r ^ (e - j)))
          * Nat.card {R : Coeff O (δ * j) N |
              resVec hN R = 0 ∧ resOrd (redRes P R) = v} :=
    fun P hP => card_content_perP hN h0 hj hrm hrd (Set.mem_toFinset.1 hP)
  -- back to the zero-residual pair census
  have hpair : Nat.card {p : Coeff O (δ * j) N × Coeff O (δ * j) N |
        p.1 ∈ levelZeroStratum O (δ * j) N (r ^ j)
          ∧ (resVec hN p.2 = 0 ∧ resOrd (redRes p.1 p.2) = v)}
      = ∑ P ∈ (levelZeroStratum O (δ * j) N (r ^ j)).toFinset,
          Nat.card {R : Coeff O (δ * j) N |
            resVec hN R = 0 ∧ resOrd (redRes P R) = v} :=
    card_pairSet_fiber (levelZeroStratum O (δ * j) N (r ^ j))
      (fun P => {R : Coeff O (δ * j) N | resVec hN R = 0 ∧ resOrd (redRes P R) = v})
  have hzero := card_zeroRes_stratumDepth (m := δ * j) hN hv (r ^ j)
  -- the coprime-box and complementary-stratum counts
  have hCB : Nat.card {U : Coeff O (δ * e - δ * j) N | ¬ r ∣ polyOf (resVec hN U)}
      = residueCard O ^ ((δ * e - δ * j) * (N - 1))
        * (residueCard O ^ (δ * e - δ * j) - residueCard O ^ (δ * e - δ * j - δ)) := by
    have h1 : Nat.card {U : Coeff O (δ * e - δ * j) N | ¬ r ∣ polyOf (resVec hN U)}
        = residueCard O ^ ((δ * e - δ * j) * (N - 1))
          * Nat.card {w : Fin (δ * e - δ * j) → ResidueField O | ¬ r ∣ polyOf w} :=
      card_box_residual_pred hN (fun w => ¬ r ∣ polyOf w)
    rw [h1, card_coprime_residual hδm hrm hrd]
  have hSem : Nat.card (levelZeroStratum O (δ * e - δ * j) N (r ^ (e - j)))
      = residueCard O ^ ((δ * e - δ * j) * (N - 1)) := by
    refine card_levelZeroStratum hN (hrm.pow _) ?_
    rw [Polynomial.natDegree_pow, hrd, Nat.mul_comm, Nat.mul_sub]
  -- assemble
  rw [hfib, Finset.sum_congr rfl hperF, ← Finset.sum_mul, hfub,
    Finset.sum_congr rfl hperP, ← Finset.mul_sum, ← hpair]
  have harr : residueCard O ^ (δ * j)
      * (Nat.card (levelZeroStratum O (δ * e - δ * j) N (r ^ (e - j)))
          * Nat.card {p : Coeff O (δ * j) N × Coeff O (δ * j) N |
              p.1 ∈ levelZeroStratum O (δ * j) N (r ^ j)
                ∧ (resVec hN p.2 = 0 ∧ resOrd (redRes p.1 p.2) = v)}
        * Nat.card {U : Coeff O (δ * e - δ * j) N | ¬ r ∣ polyOf (resVec hN U)})
      = Nat.card (levelZeroStratum O (δ * e - δ * j) N (r ^ (e - j)))
        * Nat.card {U : Coeff O (δ * e - δ * j) N | ¬ r ∣ polyOf (resVec hN U)}
        * (residueCard O ^ (δ * j)
          * Nat.card {p : Coeff O (δ * j) N × Coeff O (δ * j) N |
              p.1 ∈ levelZeroStratum O (δ * j) N (r ^ j)
                ∧ (resVec hN p.2 = 0 ∧ resOrd (redRes p.1 p.2) = v)}) := by
    ring
  rw [harr, hzero, hSem, hCB, two_mul, pow_add]
  ring

end ContentSlice

/-! ## §3g — ★★ THE PEEL RECURSION -/

section PeelRecursion

attribute [local instance] Classical.propDecidable

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)]

/-- The `r`-adic content classifier, capped at `e`. -/
noncomputable def contentOf (r : Polynomial (ResidueField O)) (e : ℕ)
    (w : Polynomial (ResidueField O)) : ℕ :=
  Nat.findGreatest (fun k => r ^ k ∣ w) e

theorem contentOf_le (r : Polynomial (ResidueField O)) (e w) :
    contentOf r e w ≤ e :=
  Nat.findGreatest_le e

theorem contentOf_eq_iff_of_lt {e j : ℕ} (hj : j < e) (r w : Polynomial (ResidueField O)) :
    contentOf r e w = j ↔ r ^ j ∣ w ∧ ¬ r ^ (j + 1) ∣ w := by
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · rcases Nat.eq_zero_or_pos j with rfl | hj0
      · rw [pow_zero]
        exact one_dvd w
      · exact Nat.findGreatest_of_ne_zero h (by omega)
    · have h1 : Nat.findGreatest (fun k => r ^ k ∣ w) e < j + 1 := by
        rw [contentOf] at h
        omega
      exact Nat.findGreatest_is_greatest h1 (by omega)
  · rintro ⟨h1, h2⟩
    have hle : j ≤ Nat.findGreatest (fun k => r ^ k ∣ w) e :=
      Nat.le_findGreatest (by omega) h1
    have hlt : Nat.findGreatest (fun k => r ^ k ∣ w) e < j + 1 := by
      by_contra hc
      push Not at hc
      have hne : Nat.findGreatest (fun k => r ^ k ∣ w) e ≠ 0 := by omega
      have hfg : r ^ (Nat.findGreatest (fun k => r ^ k ∣ w) e) ∣ w :=
        Nat.findGreatest_of_ne_zero rfl hne
      exact h2 (dvd_trans (pow_dvd_pow r hc) hfg)
    rw [contentOf]
    omega

theorem contentOf_eq_top_iff {e : ℕ} (he : 0 < e) (r w : Polynomial (ResidueField O)) :
    contentOf r e w = e ↔ r ^ e ∣ w := by
  constructor
  · intro h
    exact Nat.findGreatest_of_ne_zero h (by omega)
  · intro h
    exact le_antisymm (Nat.findGreatest_le e) (Nat.le_findGreatest le_rfl h)

/-- Below the window, full-power divisibility of the residual is exactly residual
vanishing. -/
theorem pow_dvd_iff_resVec_zero {δ e N : ℕ} (hN : 0 < N)
    {r : Polynomial (ResidueField O)} (hrd : r.natDegree = δ) {ρ : Coeff O (δ * e) N} :
    r ^ e ∣ polyOf (resVec hN ρ) ↔ resVec hN ρ = 0 := by
  constructor
  · intro hdvd
    by_contra hne
    have hpoly := polyOf_resVec_ne_zero hN hne
    have hd1 := Polynomial.natDegree_le_of_dvd hdvd hpoly
    have hd2 : (polyOf (resVec hN ρ)).natDegree < δ * e :=
      (Polynomial.natDegree_lt_iff_degree_lt hpoly).2 (polyOf_degree_lt _)
    have hd3 : (r ^ e).natDegree = e * δ := by
      rw [Polynomial.natDegree_pow, hrd]
    have hd4 : e * δ = δ * e := Nat.mul_comm e δ
    omega
  · intro h
    rw [h]
    have hz : polyOf (fun _ : Fin (δ * e) => (0 : ResidueField O)) = 0 := by
      unfold Uniformity.Density.IFCG61.polyOf
      simp
    rw [show (0 : Fin (δ * e) → ResidueField O) = fun _ => 0 from rfl, hz]
    exact dvd_zero _

/-- ★★ **THE PEEL RECURSION** (DGT route step (c), IGV's `B_e` recursion at finite
level): the `q^{δe}`-scaled primary census at exponent `e` peels into its own value at
depth `v − δe` (the zero-residual self-loop) plus the exponent-`j` censuses at depths
`v − δj`, with the coprime-box × complementary-stratum coefficients.  Uniform in `q`,
every level `N > v`. -/
theorem card_stratumDepthSet_pow_rec {δ e N v : ℕ} (hN : 0 < N) (h0 : 0 < δ) (he : 0 < e)
    (hv : v < N) {r : Polynomial (ResidueField O)} (hr : Irreducible r) (hrm : r.Monic)
    (hrd : r.natDegree = δ) :
    residueCard O ^ (δ * e) * Nat.card (stratumDepthSet O (δ * e) N v (r ^ e))
      = (if δ * e ≤ v then
            Nat.card (stratumDepthSet O (δ * e) N (v - δ * e) (r ^ e)) else 0)
        + ∑ j ∈ Finset.range e,
            (residueCard O ^ (δ * e - δ * j) - residueCard O ^ (δ * e - δ * j - δ))
              * residueCard O ^ ((δ * e - δ * j) * (2 * N - 1))
              * (if δ * j ≤ v then
                  Nat.card (stratumDepthSet O (δ * j) N (v - δ * j) (r ^ j)) else 0) := by
  classical
  haveI : Fintype (Coeff O (δ * e) N) := Fintype.ofFinite _
  haveI : Fintype (Coeff O (δ * e) N × Coeff O (δ * e) N) := Fintype.ofFinite _
  -- the content partition of the census
  have hcard : Nat.card (stratumDepthSet O (δ * e) N v (r ^ e))
      = ∑ j ∈ Finset.range (e + 1),
          Nat.card {p : Coeff O (δ * e) N × Coeff O (δ * e) N |
            p ∈ stratumDepthSet O (δ * e) N v (r ^ e)
              ∧ contentOf r e (polyOf (resVec hN p.2)) = j} := by
    rw [Nat.card_coe_set_eq, Set.ncard_eq_toFinset_card',
      Finset.card_eq_sum_card_fiberwise
        (f := fun p => contentOf r e (polyOf (resVec hN p.2)))
        (t := Finset.range (e + 1))
        (fun p _ => Finset.mem_range.2 (by
          show contentOf r e (polyOf (resVec hN p.2)) < e + 1
          have := contentOf_le r e (polyOf (resVec hN p.2))
          omega))]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Nat.card_coe_set_eq, Set.ncard_eq_toFinset_card']
    congr 1
    ext p
    simp [Set.mem_toFinset]
  -- the top fiber is the zero-residual slice
  have hfe : {p : Coeff O (δ * e) N × Coeff O (δ * e) N |
        p ∈ stratumDepthSet O (δ * e) N v (r ^ e)
          ∧ contentOf r e (polyOf (resVec hN p.2)) = e}
      = {p : Coeff O (δ * e) N × Coeff O (δ * e) N |
          p.1 ∈ levelZeroStratum O (δ * e) N (r ^ e)
            ∧ (resVec hN p.2 = 0 ∧ resOrd (redRes p.1 p.2) = v)} := by
    ext p
    simp only [Uniformity.Density.IFCG63.stratumDepthSet,
      Uniformity.Density.IFCG63.frameDepthSet, Set.mem_setOf_eq,
      contentOf_eq_top_iff he, pow_dvd_iff_resVec_zero hN hrd]
    tauto
  -- the `j < e` fibers are the content slices
  have hfj : ∀ j, j < e → {p : Coeff O (δ * e) N × Coeff O (δ * e) N |
        p ∈ stratumDepthSet O (δ * e) N v (r ^ e)
          ∧ contentOf r e (polyOf (resVec hN p.2)) = j}
      = {p : Coeff O (δ * e) N × Coeff O (δ * e) N |
          p.1 ∈ levelZeroStratum O (δ * e) N (r ^ e)
            ∧ ((r ^ j ∣ polyOf (resVec hN p.2) ∧ ¬ r ^ (j + 1) ∣ polyOf (resVec hN p.2))
              ∧ resOrd (redRes p.1 p.2) = v)} := by
    intro j hj
    ext p
    simp only [Uniformity.Density.IFCG63.stratumDepthSet,
      Uniformity.Density.IFCG63.frameDepthSet, Set.mem_setOf_eq,
      contentOf_eq_iff_of_lt hj]
    tauto
  -- assemble
  rw [hcard, Finset.mul_sum, Finset.sum_range_succ, hfe,
    card_zeroRes_stratumDepth hN hv (r ^ e)]
  have hterm : ∀ j ∈ Finset.range e,
      residueCard O ^ (δ * e)
          * Nat.card {p : Coeff O (δ * e) N × Coeff O (δ * e) N |
              p ∈ stratumDepthSet O (δ * e) N v (r ^ e)
                ∧ contentOf r e (polyOf (resVec hN p.2)) = j}
        = (residueCard O ^ (δ * e - δ * j) - residueCard O ^ (δ * e - δ * j - δ))
            * residueCard O ^ ((δ * e - δ * j) * (2 * N - 1))
            * (if δ * j ≤ v then
                Nat.card (stratumDepthSet O (δ * j) N (v - δ * j) (r ^ j)) else 0) := by
    intro j hjmem
    have hj : j < e := Finset.mem_range.1 hjmem
    have hdn : δ * j ≤ δ * e := Nat.mul_le_mul_left δ (by omega)
    have hpow : residueCard O ^ (δ * e)
        = residueCard O ^ (δ * e - δ * j) * residueCard O ^ (δ * j) := by
      rw [← pow_add]
      congr 1
      omega
    rw [hfj j hj, hpow, mul_assoc, card_content_slice hN h0 hj hv hr hrm hrd]
    have hexp : (δ * e - δ * j) * (2 * N - 1)
        = (δ * e - δ * j) + 2 * ((δ * e - δ * j) * (N - 1)) := by
      obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := ⟨N - 1, by omega⟩
      rw [Nat.add_sub_cancel, show 2 * (M + 1) - 1 = 2 * M + 1 from by omega]
      ring
    rw [hexp, pow_add]
    ring
  rw [Finset.sum_congr rfl hterm]
  omega

end PeelRecursion

/-! ## §4 — the closed form: the `N`-free normalized values -/

section ClosedForm

/-- **The normalized primary census values**, as a `ℕ`-recursion (IGV's `B_e`
solved at finite level): `primo q δ e v` will equal
`#stratumDepthSet(δe, N, v, r^e) · q^{v+δe} / q^{δe(2N−1)}` for every window `N > v` —
an `N`-FREE finite computation for every `(e, v)`. -/
def primo (q δ : ℕ) : ℕ → ℕ → ℕ
  | 0, v => if v = 0 then 1 else 0
  | (e + 1), v =>
      (if h : 1 ≤ δ * (e + 1) ∧ δ * (e + 1) ≤ v then
        primo q δ (e + 1) (v - δ * (e + 1)) else 0)
      + ∑ j ∈ (Finset.range (e + 1)).attach,
          (q ^ (δ * (e + 1) - δ * (j : ℕ)) - q ^ (δ * (e + 1) - δ * (j : ℕ) - δ))
            * (if δ * (j : ℕ) ≤ v then primo q δ (j : ℕ) (v - δ * (j : ℕ)) else 0)
  termination_by e v => (e, v)
  decreasing_by
  · exact Prod.Lex.right (e + 1) (by omega)
  · exact Prod.Lex.left _ _ (by
      have := j.2
      rw [Finset.mem_range] at this
      omega)

/-- The `e = 1` value of the normalized recursion: the flat geometric reader
`(q^δ − 1)` on multiples of `δ` — the `(1,1)` law at scale `q^δ`, `N`-free.  (Internal
cross-check: `card_stratumDepthSet_irreducible` proves the same value by the direct
per-frame induction.) -/
theorem primo_one {q δ : ℕ} (h0 : 0 < δ) (v : ℕ) :
    primo q δ 1 v = if δ ∣ v then q ^ δ - 1 else 0 := by
  have hp0 : ∀ w, primo q δ 0 w = if w = 0 then 1 else 0 := fun w => by rw [primo]
  induction v using Nat.strong_induction_on with
  | _ v IH =>
    rw [primo]
    have hsum := Finset.sum_attach (Finset.range 1)
      (fun j => (q ^ (δ * 1 - δ * j) - q ^ (δ * 1 - δ * j - δ))
        * (if δ * j ≤ v then primo q δ j (v - δ * j) else 0))
    rw [hsum, Finset.sum_range_one, hp0]
    simp only [Nat.zero_add, Nat.mul_one, Nat.mul_zero, Nat.sub_zero, Nat.sub_self,
      pow_zero, Nat.zero_le, if_true]
    by_cases hle : δ ≤ v
    · have hv1 : ¬ v = 0 := by omega
      rw [dif_pos ⟨by omega, hle⟩, IH (v - δ) (by omega), if_neg hv1, mul_zero, add_zero]
      by_cases hdvd : δ ∣ v
      · rw [if_pos (Nat.dvd_sub hdvd dvd_rfl), if_pos hdvd]
      · rw [if_neg (fun hc => hdvd (by
          have h := Nat.dvd_add hc (dvd_refl δ)
          rwa [Nat.sub_add_cancel hle] at h)), if_neg hdvd]
    · rw [dif_neg (fun hc => hle hc.2), zero_add]
      by_cases hv0 : v = 0
      · subst hv0
        rw [if_pos rfl, mul_one, if_pos (dvd_zero δ)]
      · rw [if_neg hv0, mul_zero, if_neg (fun hdvd => hle (Nat.le_of_dvd (by omega) hdvd))]

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)]

/-- ★★★ **THE PRIMARY CLOSED FORM** (DGT route step (c), CLOSED): every primary-shape
census value is the `N`-free finite computation `primo`, up to the exact normalizing
powers — uniform in `q`, every degree `δ`, every exponent `e`, every level `N > v`. -/
theorem card_stratumDepthSet_pow {δ e N v : ℕ} (hN : 0 < N) (h0 : 0 < δ) (hv : v < N)
    {r : Polynomial (ResidueField O)} (hr : Irreducible r) (hrm : r.Monic)
    (hrd : r.natDegree = δ) :
    Nat.card (stratumDepthSet O (δ * e) N v (r ^ e)) * residueCard O ^ (v + δ * e)
      = primo (residueCard O) δ e v * residueCard O ^ (δ * e * (2 * N - 1)) := by
  classical
  induction e using Nat.strong_induction_on generalizing v hv with
  | _ e IHe =>
    revert hv
    induction v using Nat.strong_induction_on with
    | _ v IHv =>
      intro hv
      rcases e with _ | e'
      · -- exponent 0: the empty census
        have hz : Nat.card (stratumDepthSet O (δ * 0) N v (r ^ 0))
            = if v = 0 then 1 else 0 := by
          rw [pow_zero]
          exact card_stratumDepthSet_zero hN
        rw [hz, primo]
        by_cases hv0 : v = 0
        · subst hv0
          simp
        · rw [if_neg hv0, zero_mul, zero_mul]
      · -- exponent e'+1: the peel recursion, times `q^v`
        have hE0 : 0 < δ * (e' + 1) := Nat.mul_pos h0 (by omega)
        have hrec := card_stratumDepthSet_pow_rec (e := e' + 1) hN h0 (by omega) hv hr
          hrm hrd
        have hgoal1 : Nat.card (stratumDepthSet O (δ * (e' + 1)) N v (r ^ (e' + 1)))
            * residueCard O ^ (v + δ * (e' + 1))
            = (residueCard O ^ (δ * (e' + 1))
                * Nat.card (stratumDepthSet O (δ * (e' + 1)) N v (r ^ (e' + 1))))
              * residueCard O ^ v := by
          rw [pow_add]
          ring
        rw [hgoal1, hrec, add_mul, Finset.sum_mul]
        -- the self-loop term normalizes by the inner induction
        have hself : (if δ * (e' + 1) ≤ v then
              Nat.card (stratumDepthSet O (δ * (e' + 1)) N (v - δ * (e' + 1))
                (r ^ (e' + 1))) else 0) * residueCard O ^ v
            = (if h : 1 ≤ δ * (e' + 1) ∧ δ * (e' + 1) ≤ v then
                primo (residueCard O) δ (e' + 1) (v - δ * (e' + 1)) else 0)
              * residueCard O ^ (δ * (e' + 1) * (2 * N - 1)) := by
          by_cases hle : δ * (e' + 1) ≤ v
          · rw [if_pos hle, dif_pos ⟨by omega, hle⟩]
            have hIH := IHv (v - δ * (e' + 1)) (by omega) (by omega)
            rw [show (v - δ * (e' + 1)) + δ * (e' + 1) = v from by omega] at hIH
            exact hIH
          · rw [if_neg hle, dif_neg (by tauto), zero_mul, zero_mul]
        -- each peel term normalizes by the outer induction
        have hsum : ∀ j ∈ Finset.range (e' + 1),
            ((residueCard O ^ (δ * (e' + 1) - δ * j)
                - residueCard O ^ (δ * (e' + 1) - δ * j - δ))
              * residueCard O ^ ((δ * (e' + 1) - δ * j) * (2 * N - 1))
              * (if δ * j ≤ v then
                  Nat.card (stratumDepthSet O (δ * j) N (v - δ * j) (r ^ j)) else 0))
              * residueCard O ^ v
            = ((residueCard O ^ (δ * (e' + 1) - δ * j)
                  - residueCard O ^ (δ * (e' + 1) - δ * j - δ))
                * (if δ * j ≤ v then primo (residueCard O) δ j (v - δ * j) else 0))
              * residueCard O ^ (δ * (e' + 1) * (2 * N - 1)) := by
          intro j hj
          rw [Finset.mem_range] at hj
          have hdn : δ * j ≤ δ * (e' + 1) := Nat.mul_le_mul_left δ (by omega)
          by_cases hle : δ * j ≤ v
          · rw [if_pos hle, if_pos hle]
            have hIH := IHe j (by omega) (v := v - δ * j) (by omega)
            rw [show (v - δ * j) + δ * j = v from by omega] at hIH
            have hBe : (δ * (e' + 1) - δ * j) * (2 * N - 1) + δ * j * (2 * N - 1)
                = δ * (e' + 1) * (2 * N - 1) := by
              rw [← Nat.add_mul]
              congr 1
              omega
            calc ((residueCard O ^ (δ * (e' + 1) - δ * j)
                    - residueCard O ^ (δ * (e' + 1) - δ * j - δ))
                  * residueCard O ^ ((δ * (e' + 1) - δ * j) * (2 * N - 1))
                  * Nat.card (stratumDepthSet O (δ * j) N (v - δ * j) (r ^ j)))
                  * residueCard O ^ v
                = (residueCard O ^ (δ * (e' + 1) - δ * j)
                    - residueCard O ^ (δ * (e' + 1) - δ * j - δ))
                  * residueCard O ^ ((δ * (e' + 1) - δ * j) * (2 * N - 1))
                  * (Nat.card (stratumDepthSet O (δ * j) N (v - δ * j) (r ^ j))
                    * residueCard O ^ (v - δ * j + δ * j)) := by
                  rw [show v - δ * j + δ * j = v from by omega]
                  ring
              _ = (residueCard O ^ (δ * (e' + 1) - δ * j)
                    - residueCard O ^ (δ * (e' + 1) - δ * j - δ))
                  * residueCard O ^ ((δ * (e' + 1) - δ * j) * (2 * N - 1))
                  * (primo (residueCard O) δ j (v - δ * j)
                    * residueCard O ^ (δ * j * (2 * N - 1))) := by
                  rw [show v - δ * j + δ * j = v from by omega, hIH]
              _ = ((residueCard O ^ (δ * (e' + 1) - δ * j)
                    - residueCard O ^ (δ * (e' + 1) - δ * j - δ))
                  * primo (residueCard O) δ j (v - δ * j))
                  * (residueCard O ^ ((δ * (e' + 1) - δ * j) * (2 * N - 1))
                    * residueCard O ^ (δ * j * (2 * N - 1))) := by
                  ring
              _ = ((residueCard O ^ (δ * (e' + 1) - δ * j)
                    - residueCard O ^ (δ * (e' + 1) - δ * j - δ))
                  * primo (residueCard O) δ j (v - δ * j))
                  * residueCard O ^ (δ * (e' + 1) * (2 * N - 1)) := by
                  rw [← pow_add, hBe]
          · rw [if_neg hle, if_neg hle, mul_zero, zero_mul, mul_zero, zero_mul]
        rw [Finset.sum_congr rfl hsum, hself, ← Finset.sum_mul, ← add_mul]
        congr 1
        conv_rhs => rw [primo]
        rw [← Finset.sum_attach (Finset.range (e' + 1))]


end ClosedForm

end Uniformity.Density.IFCG65

end

/-! ## AXCHECK FOOTER — EVERY row expects PURE Lean core
`{propext, Classical.choice, Quot.sound}`. -/
#print axioms Uniformity.Density.IFCG65.resMap_eq_zero_iff
#print axioms Uniformity.Density.IFCG65.mem_levelZeroStratum_iff_monicPoly_resVec
#print axioms Uniformity.Density.IFCG65.resOrd_mk_pow
#print axioms Uniformity.Density.IFCG65.resOrd_isUnit_mul
#print axioms Uniformity.Density.IFCG65.card_preimage_of_subset_range
#print axioms Uniformity.Density.IFCG65.redRes_scaleBox
#print axioms Uniformity.Density.IFCG65.card_scaleBox_preimage
#print axioms Uniformity.Density.IFCG65.card_levelZeroStratum
#print axioms Uniformity.Density.IFCG65.resOrd_redRes_eq_zero_of_coprime
#print axioms Uniformity.Density.IFCG65.card_frameDepthSet_irreducible
#print axioms Uniformity.Density.IFCG65.card_stratumDepthSet_irreducible
#print axioms Uniformity.Density.IFCG65.card_box_residual_pred
#print axioms Uniformity.Density.IFCG65.card_dvd_residual
#print axioms Uniformity.Density.IFCG65.card_content_residual
#print axioms Uniformity.Density.IFCG65.card_coprime_residual
#print axioms Uniformity.Density.IFCG65.isCoprime_of_isCoprime_resMap
#print axioms Uniformity.Density.IFCG65.polyOf_prodVecAt
#print axioms Uniformity.Density.IFCG65.bijOn_prodVecAt
#print axioms Uniformity.Density.IFCG65.bijOn_divVecAt
#print axioms Uniformity.Density.IFCG65.card_zeroRes_stratumDepth
#print axioms Uniformity.Density.IFCG65.card_stratumDepthSet_zero
#print axioms Uniformity.Density.IFCG65.resOrd_redRes_prodVecAt
#print axioms Uniformity.Density.IFCG65.card_content_slice
#print axioms Uniformity.Density.IFCG65.card_stratumDepthSet_pow_rec
#print axioms Uniformity.Density.IFCG65.primo_one
#print axioms Uniformity.Density.IFCG65.card_stratumDepthSet_pow
