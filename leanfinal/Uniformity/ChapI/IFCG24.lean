/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import Uniformity.ChapI.IFCG23

/-!
# Uniformity.ChapI.IFCG24 — [CN4 2026-08-30] the cone geometric sums: counting the
criterion-decided strata

Stage CN4 of the cone census.  CN2 (`IFCG23`) proved the fractional-face decidedness
criterion and reduced the e = 2 stratum to (criterion slices) ∪ (deep `v₀ ≥ 2`) ∪
(trivial window); CN0/CN1 (`IFCG22`) pinned the fractional-cell obligation to the ONE
zero-centred cone (`ZeroConeLaw`).  This file counts.

## ★ The structural theorem (uniform in `m`): the zero-centre recentring range IS the deep box

`range_fullLoopClassN_zero`: the centre-`0` full recentring range equals EXACTLY the
deep coefficient box `{c | ∀ i, m − i ≤ resOrd (c i)}`.  (⊆ is the binomial law
`shiftVecN_apply` — the shift `resSect O 0` lies in `𝔪`, and coordinate `i` of the
rescale carries `π^(m−j)·w^(j−i)`, total exponent ≥ `m − i`; equality is by counting —
both sides have `q^(mM + κ_m)` elements, and `fullLoopClassN` is injective.)  Hence
`coneCellCount O π m σ M 0 = #(decided ∩ stratum(X^m) ∩ SHALLOW)` where shallow means
some coefficient dips strictly below the Eisenstein corner: `∃ i, resOrd (c i) < m − i`
(`coneCellCount_zero_eq`).  The cone is the immediate-face part; the ENTIRE deep part is
the recentred copy, removed by construction — IFCG20's recursion territory.

## ★★ The e = 2 count — FIRST BLOOD, exact at every finite level

* `coneCellCount_two_ram`: `coneCellCount O π 2 ⟨{(2,1)}⟩ M 0 = (q−1)·q^(2M+1)` — the
  shallow stratum classes are exactly `{v₀ = 1, v₁ ≥ 1}` and each is decided ramified
  (CN2's `decidedAt_of_stratum_vzero_one`); the count is ECONE's depth-0 monomial
  `(q−1)q^(2N−3)` at `N = M+2`, EXACTLY.
* `coneCellCount_two_ne`: for every OTHER `σ` the e = 2 zero cone VANISHES
  (`decidedAt_unique`) — split/inert/unramified quadratic content lives entirely in the
  recentred copy.
* `zeroConeClause_two`: the m = 2 instance of the `ZeroConeLaw` clause body fires for
  EVERY `σ`, unconditionally: pair `(X − 1, X³)` (value `(q−1)/q³`) at `⟨{(2,1)}⟩`,
  pair `(0, 1)` otherwise.  (`m = 2` sits below `ZeroConeLaw`'s `m ≥ 4` quantifier; this
  is the instrument clause in the law's verbatim shape.)

## ⚠ The recorded correction (to CN2's correction, machine-checked here)

CN2's verdict recorded that ECONE's geometric sum `Σ_j (q−1)q^(2N−3(j+1))` counts the
loop-subtracted cone.  The truth is one step MORE drastic: the loop subtraction removes
EVERY depth `j ≥ 1` slice as well (`quadDepthSlice_subset_range` — the depth-`j ≥ 1`
criterion boxes lie in the deep box), so the cone is the SINGLE depth-0 monomial.  The
geometric series is the FULL decided density, resummed by the architecture's fixed-point
recursion at ratio `q^(−T₂) = q^(−3)`: `quad_cone_geometric_regression` checks
`Σ_j (q−1)/q^(3(j+1)) = 1/(q²+q+1)` — ECONE's instrument value — as a `HasSum` in ℝ.
`card_quadDepthSlice` gives every depth-`j` monomial its exact finite-level counting
meaning (the RW1-row monomials at e = 2).

## General `e`: the pure-face boxes, the partition, THE NAMED REMAINDER

* `faceBox m K h` (`1 ≤ h < m`, `gcd(h,m) = 1`): the pure-face criterion box
  `{v₀ = h, m·v_i ≥ h(m−i)}` — decided `⟨{(m,1)}⟩` by CN2's criterion
  (`faceBox_subset_decided`), inside the stratum and the shallow cone, pairwise
  disjoint, of EXACT count `(q−1)·q^(mK − wFace m h)` with the `K`-independent weight
  `wFace m h = 1 + h + Σ_{0<i<m} ⌈h(m−i)/m⌉` (`card_faceBox`).
* ★ `coneCellCount_partition_ram`: at every finite level,
  `coneCellCount O π m ⟨{(m,1)}⟩ M 0 = Σ_{h} (q−1)q^(m(M+m) − wFace m h)
  + coneRemainderCount` — the cone count = the geometric monomial bank + the remainder.
* `ConeRemainderLaw m σ` — THE NAMED REMAINDER the census now rests on: a rational pair
  for the normalized count of the decided shallow classes OUTSIDE the pure-face boxes
  (CN2 §7's strata: general-position fractional faces, and pure faces with `e' < m`
  whose residual dissects further).  `coneRemainder_two_ram_eq_zero`: at m = 2 it is
  EMPTY — how the first blood closes.
* ★★ the wiring: `zeroConeClause_of_remainderLaw` (per-clause),
  `zeroConeLaw_of_remainderLaws : (remainder laws) → ZeroConeLaw`,
  `centeredConeLaw_of_remainderLaws`, and the composite
  `decidedSliceAt_all_of_pointCone_remainder : PointConeLaw → (remainder laws) →
  ∀ n, DecidedSliceAt n`.

## Honesty fences

Everything uniform in `q` (and in `m` where stated; the e = 2 value is the regression
instrument, not the deliverable).  `PointConeLaw` remains OPEN (CN3/CN5 territory);
`CenteredConeLaw`/`ZeroConeLaw` are NOT discharged — they are reduced: the pure-face
(endpoint-spanning Eisenstein) sector is now closed unconditionally, and the exact
open residue is `ConeRemainderLaw` at each `(m ≥ 4, σ)`.  No statement weakened; the
remainder is named, not hidden.

## Axiom fence

Lean core everywhere (`propext`, `Classical.choice`, `Quot.sound`); the C.33 cite does
not occur; zero sorries.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.overlappingInstances false

noncomputable section

namespace Uniformity.Density.IFCG24

open IsLocalRing Polynomial Filter Topology
open Uniformity.Density.Induction
open Uniformity.Density.IFCG1 (MBoxN shiftVecN shiftVecN_apply)
open Uniformity.Density.IFCG3 (loopMapN loopVecN scaleVecN kappaLoop kappaLoop_eq_sum
  card_MBoxN_kappaLoop map_residue_monicPoly_congr)
open Uniformity.Density.IFCG14 (DecidedValueLaw Witnessed)
open Uniformity.Density.IFCG17 (decidedAt_unique)
open Uniformity.Density.IFCG20 (fullLoopClassN fullLoopClassN_injective)
open Uniformity.Density.IFCG21 (coneCellCount CenteredConeLaw PointConeLaw
  decidedSliceAt_all_of_cones)
open Uniformity.Density.IFCG22 (ZeroConeLaw classCoeffVal npHeight classNPSupport
  NPAttains ClassNPFace NPVisibleAt classNPSupport_le_apply le_classNPSupport
  one_le_classCoeffVal_of_mem_stratum centeredConeLaw_of_zeroCone resOrd_resFactor)
open Uniformity.Density.IFCG23 (decidedAt_of_eisenstein_face
  decidedAt_of_stratum_vzero_one monicPoly_zero)
open Uniformity.Density.IFC7 (resOut)

attribute [local instance] Classical.propDecidable

/-! ## §1 — the uniformizer-parametrized rational limit calculus

`ZeroConeLaw`'s clause quantifies the uniformizer INSIDE the DVR clause; the calculus
mirrors IFCG21's `PtURLim` with the point parameter replaced by the uniformizer. -/

section ZcURLim

/-- **A uniformizer-uniform rational limit family**: one `Polynomial ℚ` pair, valid at
every complete DVR with finite residue field and EVERY uniformizer — the exact shape of
`ZeroConeLaw`'s clause body. -/
def ZcURLim
    (F : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
      [IsAdicComplete (maximalIdeal O) O] [Finite (ResidueField O)],
      O → ℕ → ℝ) : Prop :=
  ∃ n d : Polynomial ℚ, d ≠ 0 ∧
    ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
      [IsAdicComplete (maximalIdeal O) O] [Finite (ResidueField O)],
      d.eval ((residueCard O : ℕ) : ℚ) ≠ 0 ∧
        ∀ π : O, Irreducible π →
          Filter.Tendsto (F O π) Filter.atTop
            (nhds ((n.eval ((residueCard O : ℕ) : ℚ)
              / d.eval ((residueCard O : ℕ) : ℚ) : ℚ) : ℝ))

/-- `ZcURLim` transfers along families that agree everywhere. -/
theorem ZcURLim.congr
    {F G : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
      [IsAdicComplete (maximalIdeal O) O] [Finite (ResidueField O)], O → ℕ → ℝ}
    (h : ZcURLim F)
    (hFG : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
      [IsAdicComplete (maximalIdeal O) O] [Finite (ResidueField O)],
      ∀ π : O, Irreducible π → ∀ M, F O π M = G O π M) : ZcURLim G := by
  obtain ⟨n, d, hd, hval⟩ := h
  refine ⟨n, d, hd, ?_⟩
  intro O _ _ _ _ _
  obtain ⟨hne, hlim⟩ := hval O
  refine ⟨hne, ?_⟩
  intro π hπ
  exact (hlim π hπ).congr (hFG O π hπ)

theorem ZcURLim.add
    {F G : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
      [IsAdicComplete (maximalIdeal O) O] [Finite (ResidueField O)], O → ℕ → ℝ}
    (hF : ZcURLim F) (hG : ZcURLim G) :
    ZcURLim (fun O _ _ _ _ _ π M => F O π M + G O π M) := by
  obtain ⟨n₁, d₁, hd₁, hval₁⟩ := hF
  obtain ⟨n₂, d₂, hd₂, hval₂⟩ := hG
  refine ⟨n₁ * d₂ + d₁ * n₂, d₁ * d₂, mul_ne_zero hd₁ hd₂, ?_⟩
  intro O _ _ _ _ _
  obtain ⟨hne₁, hlim₁⟩ := hval₁ O
  obtain ⟨hne₂, hlim₂⟩ := hval₂ O
  refine ⟨by rw [Polynomial.eval_mul]; exact mul_ne_zero hne₁ hne₂, ?_⟩
  intro π hπ
  have hq : (n₁.eval ((residueCard O : ℕ) : ℚ) / d₁.eval ((residueCard O : ℕ) : ℚ)
        + n₂.eval ((residueCard O : ℕ) : ℚ) / d₂.eval ((residueCard O : ℕ) : ℚ) : ℚ)
      = ((n₁ * d₂ + d₁ * n₂).eval ((residueCard O : ℕ) : ℚ)
          / (d₁ * d₂).eval ((residueCard O : ℕ) : ℚ) : ℚ) := by
    rw [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_mul, Polynomial.eval_mul,
      div_add_div _ _ hne₁ hne₂]
  have hlim := (hlim₁ π hπ).add (hlim₂ π hπ)
  rw [← Rat.cast_add, hq] at hlim
  exact hlim

/-- The constant-`0` family. -/
theorem ZcURLim_zero : ZcURLim (fun _ _ _ _ _ _ _ _ => (0 : ℝ)) := by
  refine ⟨0, 1, one_ne_zero, ?_⟩
  intro O _ _ _ _ _
  refine ⟨by simp, ?_⟩
  intro π hπ
  have hval : (((0 : Polynomial ℚ).eval ((residueCard O : ℕ) : ℚ)
      / (1 : Polynomial ℚ).eval ((residueCard O : ℕ) : ℚ) : ℚ) : ℝ) = 0 := by simp
  rw [hval]
  exact tendsto_const_nhds

theorem ZcURLim_sum {ι : Type*} (s : Finset ι)
    (F : ι → ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
      [IsAdicComplete (maximalIdeal O) O] [Finite (ResidueField O)], O → ℕ → ℝ)
    (h : ∀ i ∈ s, ZcURLim (F i)) :
    ZcURLim (fun O _ _ _ _ _ π M => ∑ i ∈ s, F i O π M) := by
  classical
  induction s using Finset.cons_induction with
  | empty =>
      refine ZcURLim_zero.congr ?_
      intro O _ _ _ _ _ π _ M
      simp
  | cons a s ha ih =>
      refine ((h a (Finset.mem_cons_self a s)).add
        (ih (fun i hi => h i (Finset.mem_cons_of_mem hi)))).congr ?_
      intro O _ _ _ _ _ π _ M
      rw [Finset.sum_cons]

/-- **The geometric monomial**: the constant family `(q−1)/q^w` is a `ZcURLim` family
with the pair `(X − 1, X^w)` — the counting shape of every pure-face box. -/
theorem ZcURLim_qmonomial (w : ℕ) :
    ZcURLim (fun O _ _ _ _ _ _ _ =>
      (((residueCard O : ℕ) : ℝ) - 1) / ((residueCard O : ℕ) : ℝ) ^ w) := by
  refine ⟨Polynomial.X - 1, Polynomial.X ^ w, pow_ne_zero _ Polynomial.X_ne_zero, ?_⟩
  intro O _ _ _ _ _
  have hq2 : 2 ≤ residueCard O := two_le_residueCard O
  have hq0 : ((residueCard O : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  refine ⟨by rw [Polynomial.eval_pow, Polynomial.eval_X]; exact pow_ne_zero _ hq0, ?_⟩
  intro π hπ
  have hval : ((((Polynomial.X - 1 : Polynomial ℚ).eval ((residueCard O : ℕ) : ℚ))
      / ((Polynomial.X ^ w : Polynomial ℚ).eval ((residueCard O : ℕ) : ℚ)) : ℚ) : ℝ)
      = (((residueCard O : ℕ) : ℝ) - 1) / ((residueCard O : ℕ) : ℝ) ^ w := by
    rw [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_one]
    push_cast
    ring
  rw [hval]
  exact tendsto_const_nhds

end ZcURLim

/-! ## §2 — the box-counting toolkit -/

section Toolkit

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)]

/-- Truncation to the level-`k` window kills exactly the classes of windowed valuation
`≥ k` (the kernel reading of CN1's min-law). -/
theorem resFactor_eq_zero_iff {K k : ℕ} (hk : k ≤ K) (x : Res O K) :
    resFactor (O := O) hk x = 0 ↔ k ≤ resOrd x := by
  constructor
  · intro h0
    have h1 := resOrd_resFactor hk x
    rw [h0] at h1
    have h2 : resOrd (0 : Res O k) = k := (resOrd_eq_iff _).mpr rfl
    rw [h2] at h1
    omega
  · intro hk2
    have h1 := resOrd_resFactor hk x
    rw [min_eq_left hk2] at h1
    exact (resOrd_eq_iff _).mp h1

/-- **The upper-set count**: `#{x : Res O K | k ≤ resOrd x} = q^(K−k)`. -/
theorem card_setOf_le_resOrd {K k : ℕ} (hk : k ≤ K) :
    Nat.card ({x : Res O K | k ≤ resOrd x} : Set (Res O K))
      = residueCard O ^ (K - k) := by
  classical
  set f : Res O K →+ Res O k := (resFactor (O := O) hk).toAddMonoidHom with hf
  have hsurj : Function.Surjective f := resFactor_surjective (O := O) hk
  have h1 := card_preimage_of_surjective f hsurj ({0} : Set (Res O k))
  have h2 := card_preimage_of_surjective f hsurj (Set.univ : Set (Res O k))
  rw [Set.preimage_univ, Nat.card_coe_set_eq, Set.ncard_univ,
    Nat.card_coe_set_eq (Set.univ : Set (Res O k)), Set.ncard_univ] at h2
  rw [card_res, card_res] at h2
  have hker : Nat.card f.ker = residueCard O ^ (K - k) := by
    have hq : 0 < residueCard O ^ k := pow_pos (residueCard_pos O) k
    refine Nat.eq_of_mul_eq_mul_right hq ?_
    rw [← h2, ← pow_add]
    congr 1
    omega
  have hset : ({x : Res O K | k ≤ resOrd x} : Set (Res O K)) = f ⁻¹' {0} := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_preimage, Set.mem_singleton_iff]
    exact (resFactor_eq_zero_iff hk x).symm
  rw [hset, h1, hker]
  have h0 : Nat.card ({0} : Set (Res O k)) = 1 := by
    rw [Nat.card_coe_set_eq, Set.ncard_singleton]
  rw [h0, mul_one]

/-- **The level-set count**: `#{x : Res O K | resOrd x = k} = (q−1)·q^(K−k−1)` for
`k < K`. -/
theorem card_setOf_resOrd_eq {K k : ℕ} (hk : k < K) :
    Nat.card ({x : Res O K | resOrd x = k} : Set (Res O K))
      = (residueCard O - 1) * residueCard O ^ (K - k - 1) := by
  classical
  have hsub : ({x : Res O K | k + 1 ≤ resOrd x} : Set (Res O K))
      ⊆ {x : Res O K | k ≤ resOrd x} := fun x hx => by
    simp only [Set.mem_setOf_eq] at *
    omega
  have hset : ({x : Res O K | resOrd x = k} : Set (Res O K))
      = {x : Res O K | k ≤ resOrd x} \ {x : Res O K | k + 1 ≤ resOrd x} := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_sdiff]
    omega
  rw [hset, Nat.card_coe_set_eq, Set.ncard_sdiff hsub]
  rw [← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq,
    card_setOf_le_resOrd (by omega : k ≤ K), card_setOf_le_resOrd (by omega : k + 1 ≤ K)]
  have h1 : K - k = (K - k - 1) + 1 := by omega
  have h2 : K - (k + 1) = K - k - 1 := by omega
  rw [h1, h2, pow_succ, Nat.sub_one_mul,
    Nat.mul_comm (residueCard O ^ (K - k - 1)) (residueCard O), Nat.add_sub_cancel]

/-- **The product-box count**: coordinatewise constraints multiply. -/
theorem card_pi_set {m K : ℕ} (S : Fin m → Set (Res O K)) :
    Nat.card ({c : Coeff O m K | ∀ i, c i ∈ S i} : Set (Coeff O m K))
      = ∏ i, Nat.card (S i) := by
  have hset : ({c : Coeff O m K | ∀ i, c i ∈ S i} : Set (Coeff O m K)) = Set.univ.pi S := by
    ext c
    simp
  rw [hset]
  rw [Nat.card_congr (α := (Set.univ.pi S : Set (Coeff O m K))) (β := ∀ i, S i)
    ⟨fun c i => ⟨c.1 i, c.2 i (Set.mem_univ i)⟩,
     fun f => ⟨fun i => (f i).1, fun i _ => (f i).2⟩,
     fun c => rfl, fun f => rfl⟩]
  exact Nat.card_pi

/-- Counting bridge (IFCG18 §0's private helper, re-proved). -/
private theorem natCard_set_eq_card_filter {α : Type*} [Fintype α] (s : Set α) :
    Nat.card s = (Finset.univ.filter (fun a => a ∈ s)).card := by
  rw [Nat.card_coe_set_eq, ← Set.ncard_coe_finset (Finset.univ.filter (fun a => a ∈ s))]
  congr 1
  ext a
  simp

/-- The fibre-partition helper (IFCG21's private helper, reproduced). -/
private theorem natCard_eq_sum_fiber {α β : Type*} [Fintype α] (s : Set α) (φ : α → β)
    (T : Finset β) (hT : ∀ a ∈ s, φ a ∈ T) :
    Nat.card s = ∑ b ∈ T, Nat.card ((s ∩ φ ⁻¹' {b}) : Set α) := by
  rw [natCard_set_eq_card_filter,
    Finset.card_eq_sum_card_fiberwise (f := φ) (t := T)
      (fun a ha => hT a (by simpa using (Finset.mem_filter.1 ha).2))]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [natCard_set_eq_card_filter, Finset.filter_filter]
  congr 1
  ext a
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Set.mem_inter_iff,
    Set.mem_preimage, Set.mem_singleton_iff]

end Toolkit

/-! ## §3 — ★ THE ZERO-CENTRE RANGE THEOREM: the recentring range is the deep box -/

section ZeroRange

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)]

/-- **The deep coefficient box**: every coefficient sits at or above the Eisenstein
corner heights `m − i` — the classes whose polygon admits the unit-slope recentring. -/
def deepBox (O : Type*) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (m K : ℕ) : Set (Coeff O m K) :=
  {c | ∀ i : Fin m, m - (i : ℕ) ≤ resOrd (c i)}

/-- **The shallow set** — the complement carrier: some coefficient dips strictly below
its Eisenstein corner.  The cone lives here. -/
def shallowSet (O : Type*) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (m K : ℕ) : Set (Coeff O m K) :=
  {c | ∃ i : Fin m, resOrd (c i) < m - (i : ℕ)}

/-- The canonical lift of the zero centre is divisible by any uniformizer. -/
theorem dvd_resSect_zero {π : O} (hπ : Irreducible π) :
    π ∣ resSect O (0 : ResidueField O) := by
  have h0 : residue O (resSect O (0 : ResidueField O)) = 0 := residue_resSect O 0
  have hmem : resSect O (0 : ResidueField O) ∈ maximalIdeal O :=
    (IsLocalRing.residue_eq_zero_iff _).1 h0
  exact (mem_maximalIdeal_iff_dvd hπ _).1 hmem

/-- **The divisibility heart of the range inclusion**: coordinate `i` of the
zero-centred rescale-recentre vector is divisible by `π^(m−i)` (binomial law:
every term carries `π^(m−j)·w^(j−i)` with `w ∈ 𝔪`). -/
theorem dvd_loopMapN_zero {π : O} (hπ : Irreducible π) {m M : ℕ} (d : MBoxN O m M)
    (i : Fin m) : π ^ (m - (i : ℕ)) ∣ loopMapN (0 : ResidueField O) π d i := by
  have hπw : π ∣ resSect O (0 : ResidueField O) := dvd_resSect_zero hπ
  have happ : loopMapN (0 : ResidueField O) π d i
      = ((m.choose (i : ℕ) : O) * resSect O (0 : ResidueField O) ^ (m - (i : ℕ)))
        + ∑ j : Fin m, (((j : ℕ).choose (i : ℕ) : O) * loopVecN π d j
            * resSect O (0 : ResidueField O) ^ ((j : ℕ) - (i : ℕ))) :=
    shiftVecN_apply (loopVecN π d) (resSect O (0 : ResidueField O)) i
  rw [happ]
  refine dvd_add ((pow_dvd_pow_of_dvd hπw (m - (i : ℕ))).mul_left _) (Finset.dvd_sum ?_)
  intro j _
  rcases Nat.lt_or_ge (j : ℕ) (i : ℕ) with hji | hij
  · rw [Nat.choose_eq_zero_of_lt hji]
    simp
  · have hj := j.isLt
    have hlv : π ^ (m - (j : ℕ)) ∣ loopVecN π d j := ⟨resOut (d j), rfl⟩
    have h1 : π ^ (m - (j : ℕ)) ∣ ((j : ℕ).choose (i : ℕ) : O) * loopVecN π d j :=
      hlv.mul_left _
    have h2 : π ^ ((j : ℕ) - (i : ℕ))
        ∣ resSect O (0 : ResidueField O) ^ ((j : ℕ) - (i : ℕ)) :=
      pow_dvd_pow_of_dvd hπw _
    have hexp : m - (i : ℕ) = (m - (j : ℕ)) + ((j : ℕ) - (i : ℕ)) := by omega
    rw [hexp, pow_add]
    exact mul_dvd_mul h1 h2

/-- The zero-centred full recentring range sits inside the deep box. -/
theorem range_zero_subset_deepBox {π : O} (hπ : Irreducible π) {m M : ℕ} :
    Set.range (fun d : MBoxN O m M => fullLoopClassN π ((0 : ResidueField O), d))
      ⊆ deepBox O m (M + m) := by
  rintro c ⟨d, rfl⟩
  simp only [deepBox, Set.mem_setOf_eq]
  intro i
  have hc : fullLoopClassN π ((0 : ResidueField O), d) i
      = Ideal.Quotient.mk ((maximalIdeal O) ^ (M + m))
          (loopMapN (0 : ResidueField O) π d i) := rfl
  rw [hc]
  exact (resOrd_ge_iff hπ (by omega : m - (i : ℕ) ≤ M + m) _).2 (dvd_loopMapN_zero hπ d i)

/-- The deep box has exactly `q^(mM + κ_m)` classes — the mixed box's cardinality. -/
theorem card_deepBox (m M : ℕ) :
    Nat.card (deepBox O m (M + m) : Set (Coeff O m (M + m)))
      = residueCard O ^ (m * M + kappaLoop m) := by
  have hset : (deepBox O m (M + m) : Set (Coeff O m (M + m)))
      = {c : Coeff O m (M + m) |
          ∀ i : Fin m, c i ∈ {x : Res O (M + m) | m - (i : ℕ) ≤ resOrd x}} :=
    rfl
  rw [hset, card_pi_set]
  have hfac : ∀ i : Fin m,
      Nat.card ({x : Res O (M + m) | m - (i : ℕ) ≤ resOrd x} : Set (Res O (M + m)))
        = residueCard O ^ (M + (i : ℕ)) := by
    intro i
    rw [card_setOf_le_resOrd (by omega : m - (i : ℕ) ≤ M + m)]
    congr 1
    have := i.isLt
    omega
  rw [Finset.prod_congr rfl (fun i _ => hfac i), Finset.prod_pow_eq_pow_sum]
  congr 1
  rw [Fin.sum_univ_eq_sum_range (fun i => M + i) m, Finset.sum_add_distrib,
    Finset.sum_const, Finset.card_range, smul_eq_mul, kappaLoop_eq_sum]

/-- ★ **THE ZERO-CENTRE RANGE THEOREM** (uniform in `m`): the centre-`0` full recentring
range is EXACTLY the deep box.  Inclusion by the binomial law; equality by counting
(`card_MBoxN_kappaLoop` + injectivity). -/
theorem range_fullLoopClassN_zero {π : O} (hπ : Irreducible π) {m : ℕ} (hm : 0 < m)
    (M : ℕ) :
    Set.range (fun d : MBoxN O m M => fullLoopClassN π ((0 : ResidueField O), d))
      = deepBox O m (M + m) := by
  have hinj : Function.Injective
      (fun d : MBoxN O m M => fullLoopClassN π ((0 : ResidueField O), d)) := by
    intro d d' hdd'
    have h2 := fullLoopClassN_injective hπ hm hdd'
    exact congrArg Prod.snd h2
  have hcard : Nat.card (Set.range
        (fun d : MBoxN O m M => fullLoopClassN π ((0 : ResidueField O), d)))
      = residueCard O ^ (m * M + kappaLoop m) := by
    rw [Nat.card_range_of_injective hinj, card_MBoxN_kappaLoop]
  refine Set.eq_of_subset_of_ncard_le (range_zero_subset_deepBox hπ)
    (le_of_eq ?_) (Set.toFinite _)
  rw [← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq, hcard, card_deepBox]

end ZeroRange

/-! ## §4 — the stratum membership bridge and the general cone carrier -/

section ConeCarrier

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)]

/-- `monicPoly 0 = X^m` (IFCG23's lemma, restated adic-free — the original sits in a
section whose `IsAdicComplete` variable is baked in). -/
private theorem monicPoly_zero' (m : ℕ) :
    monicPoly (fun _ : Fin m => (0 : O)) = X ^ m := by
  unfold monicPoly
  simp

/-- Membership in the stratum of `X^m` is exactly "all windowed valuations `≥ 1`"
(the converse of CN1's `one_le_classCoeffVal_of_mem_stratum`). -/
theorem mem_stratum_X_pow_iff {m K : ℕ} (hK : 1 ≤ K) (c : Coeff O m K) :
    c ∈ levelZeroStratum O m K (X ^ m) ↔ ∀ i : Fin m, 1 ≤ resOrd (c i) := by
  constructor
  · intro hc i
    exact one_le_classCoeffVal_of_mem_stratum hK hc i
  · intro h
    obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible O
    obtain ⟨a, rfl⟩ := proj_surjective O m K c
    refine (mem_levelZeroStratum_iff hK _ _).2 ⟨a, rfl, ?_⟩
    have hcong : ∀ i : Fin m, π ∣ (a i - (fun _ : Fin m => (0 : O)) i) := by
      intro i
      have h1 : π ^ 1 ∣ a i := (resOrd_ge_iff hπ (by omega : 1 ≤ K) (a i)).1 (h i)
      rw [pow_one] at h1
      simpa using h1
    have hres := map_residue_monicPoly_congr hπ hcong
    rw [hres, monicPoly_zero', Polynomial.map_pow, Polynomial.map_X]

/-- ★ **The cone carrier** (uniform in `m`): the zero-centred cone count is the count of
the decided SHALLOW stratum classes — the deep part is the recentred copy, removed
exactly (`range_fullLoopClassN_zero`). -/
theorem coneCellCount_zero_eq {π : O} (hπ : Irreducible π) {m : ℕ} (hm : 0 < m)
    (σ : FactorizationType) (M : ℕ) :
    coneCellCount O π m σ M 0
      = Nat.card ((decidedSet O m σ (M + m)
          ∩ levelZeroStratum O m (M + m) (X ^ m)
          ∩ shallowSet O m (M + m)) : Set (Coeff O m (M + m))) := by
  have hstr : ((X + C (0 : ResidueField O)) ^ m : Polynomial (ResidueField O)) = X ^ m := by
    rw [map_zero, add_zero]
  have hset : ((decidedSet O m σ (M + m)
        ∩ levelZeroStratum O m (M + m) ((X + C (0 : ResidueField O)) ^ m))
      \ Set.range (fun d : MBoxN O m M => fullLoopClassN π ((0 : ResidueField O), d)))
      = (decidedSet O m σ (M + m) ∩ levelZeroStratum O m (M + m) (X ^ m)
          ∩ shallowSet O m (M + m)) := by
    rw [hstr, range_fullLoopClassN_zero hπ hm M]
    ext c
    simp only [Set.mem_sdiff, Set.mem_inter_iff, deepBox, shallowSet, Set.mem_setOf_eq]
    constructor
    · rintro ⟨⟨hA, hS⟩, hD⟩
      refine ⟨⟨hA, hS⟩, ?_⟩
      by_contra hno
      push Not at hno
      exact hD hno
    · rintro ⟨⟨hA, hS⟩, i, hi⟩
      exact ⟨⟨hA, hS⟩, fun hall => by have := hall i; omega⟩
  calc coneCellCount O π m σ M 0
      = Nat.card (((decidedSet O m σ (M + m)
          ∩ levelZeroStratum O m (M + m) ((X + C (0 : ResidueField O)) ^ m))
        \ Set.range (fun d : MBoxN O m M => fullLoopClassN π ((0 : ResidueField O), d)))
          : Set (Coeff O m (M + m))) := rfl
    _ = _ := by rw [hset]

end ConeCarrier

/-! ## §5 — ★★ THE e = 2 COUNT: first blood, exact at every level -/

section FirstBlood

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [IsAdicComplete (maximalIdeal O) O] [Finite (ResidueField O)]

/-- The e = 2 cone set is exactly the depth-0 box `{v₀ = 1, v₁ ≥ 1}`: shallow ∩ stratum
forces `v₀ = 1`, and every such class is decided ramified
(`decidedAt_of_stratum_vzero_one`). -/
theorem coneSet_two_ram (M : ℕ) :
    (decidedSet O 2 ⟨{(2, 1)}⟩ (M + 2)
        ∩ levelZeroStratum O 2 (M + 2) (X ^ 2)
        ∩ shallowSet O 2 (M + 2))
      = {c : Coeff O 2 (M + 2) | resOrd (c 0) = 1 ∧ 1 ≤ resOrd (c 1)} := by
  ext c
  simp only [Set.mem_inter_iff, Set.mem_setOf_eq, shallowSet]
  constructor
  · rintro ⟨⟨hA, hS⟩, i, hi⟩
    have hv := (mem_stratum_X_pow_iff (by omega) c).1 hS
    have hv0 := hv 0
    have hv1 := hv 1
    refine ⟨?_, hv1⟩
    fin_cases i <;>
      simp only [Fin.zero_eta, Fin.mk_one] at hi <;> omega
  · rintro ⟨h0, h1⟩
    have hS : c ∈ levelZeroStratum O 2 (M + 2) (X ^ 2) := by
      refine (mem_stratum_X_pow_iff (by omega) c).2 fun i => ?_
      fin_cases i <;> simp only [Fin.zero_eta, Fin.mk_one] <;> omega
    refine ⟨⟨?_, hS⟩, ⟨0, ?_⟩⟩
    · show DecidedAt O 2 ⟨{(2, 1)}⟩ (M + 2) c
      exact decidedAt_of_stratum_vzero_one (by omega) hS h0
    · have h2 : resOrd (c 0) < 2 := by omega
      simpa using h2

/-- ★★ **THE e = 2 CONE COUNT** — exact at every finite level, uniform in `q`:
`(q−1)·q^(2M+1)` = ECONE's depth-0 monomial `(q−1)q^(2N−3)` at `N = M+2`.  The
depth-`j ≥ 1` slices are recentrings and are REMOVED (see
`quadDepthSlice_subset_range`). -/
theorem coneCellCount_two_ram {π : O} (hπ : Irreducible π) (M : ℕ) :
    coneCellCount O π 2 ⟨{(2, 1)}⟩ M 0
      = (residueCard O - 1) * residueCard O ^ (2 * M + 1) := by
  rw [coneCellCount_zero_eq hπ (by norm_num) ⟨{(2, 1)}⟩ M, coneSet_two_ram M]
  have hset : ({c : Coeff O 2 (M + 2) | resOrd (c 0) = 1 ∧ 1 ≤ resOrd (c 1)}
        : Set (Coeff O 2 (M + 2)))
      = {c : Coeff O 2 (M + 2) | ∀ i : Fin 2, c i ∈
          (if (i : ℕ) = 0 then {x : Res O (M + 2) | resOrd x = 1}
           else {x : Res O (M + 2) | 1 ≤ resOrd x})} := by
    ext c
    simp only [Set.mem_setOf_eq]
    constructor
    · rintro ⟨h0, h1⟩ i
      fin_cases i
      · simpa using h0
      · simpa using h1
    · intro hall
      have h0 := hall 0
      have h1 := hall 1
      rw [if_pos (show ((0 : Fin 2) : ℕ) = 0 from rfl)] at h0
      rw [if_neg (show ¬(((1 : Fin 2) : ℕ) = 0) by norm_num)] at h1
      exact ⟨h0, h1⟩
  rw [hset, card_pi_set, Fin.prod_univ_two]
  rw [if_pos (show ((0 : Fin 2) : ℕ) = 0 from rfl),
    if_neg (show ¬(((1 : Fin 2) : ℕ) = 0) by norm_num)]
  rw [card_setOf_resOrd_eq (by omega : 1 < M + 2), card_setOf_le_resOrd (by omega : 1 ≤ M + 2)]
  rw [mul_assoc, ← pow_add]
  congr 2
  omega

/-- ★ For every OTHER type the e = 2 zero cone VANISHES: the shallow stratum classes are
all `⟨{(2,1)}⟩`-decided, and decidedness is unique. -/
theorem coneCellCount_two_ne {π : O} (hπ : Irreducible π) {σ : FactorizationType}
    (hσ : σ ≠ ⟨{(2, 1)}⟩) (M : ℕ) :
    coneCellCount O π 2 σ M 0 = 0 := by
  rw [coneCellCount_zero_eq hπ (by norm_num) σ M]
  have hset : (decidedSet O 2 σ (M + 2) ∩ levelZeroStratum O 2 (M + 2) (X ^ 2)
      ∩ shallowSet O 2 (M + 2)) = (∅ : Set (Coeff O 2 (M + 2))) := by
    ext c
    simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false, shallowSet,
      Set.mem_setOf_eq]
    rintro ⟨⟨hA, hS⟩, i, hi⟩
    have hv := (mem_stratum_X_pow_iff (by omega) c).1 hS
    have hv0 := hv 0
    have hv1 := hv 1
    have h0 : resOrd (c 0) = 1 := by
      fin_cases i <;>
        simp only [Fin.zero_eta, Fin.mk_one] at hi <;> omega
    have hram : DecidedAt O 2 ⟨{(2, 1)}⟩ (M + 2) c :=
      decidedAt_of_stratum_vzero_one (by omega) hS h0
    exact hσ (decidedAt_unique hA hram)
  rw [hset, Nat.card_coe_set_eq, Set.ncard_empty]

end FirstBlood

/-! ## §6 — the clause family and the m = 2 value law -/

section ClauseTwo

/-- The normalized zero-cone family at `(m, σ)` — `ZeroConeLaw`'s clause body carrier. -/
def coneFamily (m : ℕ) (σ : FactorizationType) :
    ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
      [IsAdicComplete (maximalIdeal O) O] [Finite (ResidueField O)], O → ℕ → ℝ :=
  fun O _ _ _ _ _ π M =>
    (coneCellCount O π m σ M 0 : ℝ) / ((residueCard O : ℕ) : ℝ) ^ (m * (M + m))

/-- **The `(m, σ)` clause of the zero-cone law** — exactly `ZeroConeLaw`'s inner
existential, one degree-and-type at a time. -/
def ZeroConeClause (m : ℕ) (σ : FactorizationType) : Prop :=
  ZcURLim (coneFamily m σ)

/-- ★★ the m = 2 ramified clause: value `(q−1)/q³`, pair `(X − 1, X³)`. -/
theorem zeroConeClause_two_ram : ZeroConeClause 2 ⟨{(2, 1)}⟩ := by
  refine ⟨Polynomial.X - 1, Polynomial.X ^ 3, pow_ne_zero _ Polynomial.X_ne_zero, ?_⟩
  intro O _ _ _ _ _
  have hq2 : 2 ≤ residueCard O := two_le_residueCard O
  have hq0 : ((residueCard O : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  refine ⟨by rw [Polynomial.eval_pow, Polynomial.eval_X]; exact pow_ne_zero _ hq0, ?_⟩
  intro π hπ
  have hqR : ((residueCard O : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hval : ((((Polynomial.X - 1 : Polynomial ℚ).eval ((residueCard O : ℕ) : ℚ))
      / ((Polynomial.X ^ 3 : Polynomial ℚ).eval ((residueCard O : ℕ) : ℚ)) : ℚ) : ℝ)
      = (((residueCard O : ℕ) : ℝ) - 1) / ((residueCard O : ℕ) : ℝ) ^ 3 := by
    rw [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_one]
    push_cast
    ring
  rw [hval]
  refine tendsto_const_nhds.congr fun M => ?_
  show (((residueCard O : ℕ) : ℝ) - 1) / ((residueCard O : ℕ) : ℝ) ^ 3
      = (coneCellCount O π 2 ⟨{(2, 1)}⟩ M 0 : ℝ)
          / ((residueCard O : ℕ) : ℝ) ^ (2 * (M + 2))
  rw [coneCellCount_two_ram hπ M]
  rw [Nat.cast_mul, Nat.cast_pow, Nat.cast_sub (by omega : 1 ≤ residueCard O), Nat.cast_one]
  rw [show 2 * (M + 2) = (2 * M + 1) + 3 by omega, pow_add]
  have h1 : ((residueCard O : ℕ) : ℝ) ^ (2 * M + 1) ≠ 0 := pow_ne_zero _ hqR
  have h3 : ((residueCard O : ℕ) : ℝ) ^ 3 ≠ 0 := pow_ne_zero _ hqR
  field_simp
  ring

/-- the m = 2 clause at every other type: value `0`, pair `(0, 1)`. -/
theorem zeroConeClause_two_ne {σ : FactorizationType} (hσ : σ ≠ ⟨{(2, 1)}⟩) :
    ZeroConeClause 2 σ := by
  refine ⟨0, 1, one_ne_zero, ?_⟩
  intro O _ _ _ _ _
  refine ⟨by simp, ?_⟩
  intro π hπ
  have hval : (((0 : Polynomial ℚ).eval ((residueCard O : ℕ) : ℚ)
      / (1 : Polynomial ℚ).eval ((residueCard O : ℕ) : ℚ) : ℚ) : ℝ) = 0 := by simp
  rw [hval]
  refine tendsto_const_nhds.congr fun M => ?_
  show (0 : ℝ) = (coneCellCount O π 2 σ M 0 : ℝ)
      / ((residueCard O : ℕ) : ℝ) ^ (2 * (M + 2))
  rw [coneCellCount_two_ne hπ hσ M]
  simp

/-- ★★ **THE e = 2 CLAUSE FIRES FOR EVERY TYPE** — the m = 2 instance of `ZeroConeLaw`'s
clause body, unconditional (no smaller-law premises needed at the instrument degree). -/
theorem zeroConeClause_two (σ : FactorizationType) : ZeroConeClause 2 σ := by
  by_cases hσ : σ = ⟨{(2, 1)}⟩
  · subst hσ
    exact zeroConeClause_two_ram
  · exact zeroConeClause_two_ne hσ

end ClauseTwo

/-! ## §7 — the regression bank: the depth monomials, the correction, the series -/

section Regression

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)]

/-- **The depth-`j` slice count** (ECONE's geometric monomials, exact): the depth-`j`
criterion box `{v₀ = 2j+1, v₁ ≥ j+1}` has `(q−1)·q^(2K−3(j+1))` classes.  Each is
`⟨{(2,1)}⟩`-decided (CN2's `decidedAt_quad_ram`). -/
theorem card_quadDepthSlice {K j : ℕ} (hj : 2 * j + 1 < K) :
    Nat.card ({c : Coeff O 2 K | resOrd (c 0) = 2 * j + 1 ∧ j + 1 ≤ resOrd (c 1)}
        : Set (Coeff O 2 K))
      = (residueCard O - 1) * residueCard O ^ (2 * K - (3 * j + 3)) := by
  have hset : ({c : Coeff O 2 K | resOrd (c 0) = 2 * j + 1 ∧ j + 1 ≤ resOrd (c 1)}
        : Set (Coeff O 2 K))
      = {c : Coeff O 2 K | ∀ i : Fin 2, c i ∈
          (if (i : ℕ) = 0 then {x : Res O K | resOrd x = 2 * j + 1}
           else {x : Res O K | j + 1 ≤ resOrd x})} := by
    ext c
    simp only [Set.mem_setOf_eq]
    constructor
    · rintro ⟨h0, h1⟩ i
      fin_cases i
      · simpa using h0
      · simpa using h1
    · intro hall
      have h0 := hall 0
      have h1 := hall 1
      rw [if_pos (show ((0 : Fin 2) : ℕ) = 0 from rfl)] at h0
      rw [if_neg (show ¬(((1 : Fin 2) : ℕ) = 0) by norm_num)] at h1
      exact ⟨h0, h1⟩
  rw [hset, card_pi_set, Fin.prod_univ_two]
  rw [if_pos (show ((0 : Fin 2) : ℕ) = 0 from rfl),
    if_neg (show ¬(((1 : Fin 2) : ℕ) = 0) by norm_num)]
  rw [card_setOf_resOrd_eq (by omega : 2 * j + 1 < K),
    card_setOf_le_resOrd (by omega : j + 1 ≤ K)]
  rw [mul_assoc, ← pow_add]
  congr 2
  omega

/-- ⚠ **THE CORRECTION, machine-checked**: every depth-`j ≥ 1` criterion slice lies
INSIDE the zero-centre recentring range — the loop subtraction removes ALL deeper
slices, so the cone keeps only depth 0.  (CN2's verdict had recorded the cone as the
full geometric sum; the sum is the FULL density, via the recursion.) -/
theorem quadDepthSlice_subset_range {π : O} (hπ : Irreducible π) {M j : ℕ}
    (hj : 1 ≤ j) :
    ({c : Coeff O 2 (M + 2) | resOrd (c 0) = 2 * j + 1 ∧ j + 1 ≤ resOrd (c 1)}
        : Set (Coeff O 2 (M + 2)))
      ⊆ Set.range (fun d : MBoxN O 2 M => fullLoopClassN π ((0 : ResidueField O), d)) := by
  rw [range_fullLoopClassN_zero hπ (by norm_num) M]
  rintro c ⟨h0, h1⟩
  simp only [deepBox, Set.mem_setOf_eq]
  intro i
  fin_cases i <;> simp only [Fin.zero_eta, Fin.mk_one] <;> omega

/-- **The regression identity** (ECONE's instrument value recovered): the depth
monomials, resummed by the architecture's fixed-point recursion at ratio
`q^(−T₂) = q^(−3)`, give `Σ_j (q−1)/q^(3(j+1)) = 1/(q²+q+1)`. -/
theorem quad_cone_geometric_regression {q : ℝ} (hq : 2 ≤ q) :
    HasSum (fun j : ℕ => (q - 1) / q ^ (3 * (j + 1))) (1 / (q ^ 2 + q + 1)) := by
  have hq0 : (0 : ℝ) < q := by linarith
  have hq3 : (0 : ℝ) < q ^ 3 := by positivity
  have h8 : (8 : ℝ) ≤ q ^ 3 := by
    calc (8 : ℝ) = 2 ^ 3 := by norm_num
      _ ≤ q ^ 3 := by gcongr
  have hr : |1 / q ^ 3| < 1 := by
    rw [abs_of_pos (by positivity), div_lt_one hq3]
    linarith
  have hgeo := (hasSum_geometric_of_abs_lt_one hr).mul_left ((q - 1) / q ^ 3)
  have hfun : ∀ j : ℕ, (q - 1) / q ^ 3 * (1 / q ^ 3) ^ j = (q - 1) / q ^ (3 * (j + 1)) := by
    intro j
    rw [show (3 : ℕ) * (j + 1) = 3 + 3 * j from by ring, pow_add, pow_mul]
    rw [div_pow, one_pow, div_mul_div_comm, mul_one]
  have hval : (q - 1) / q ^ 3 * (1 - 1 / q ^ 3)⁻¹ = 1 / (q ^ 2 + q + 1) := by
    have h1 : q ^ 3 - 1 ≠ 0 := by intro h; linarith
    have h2 : q ^ 2 + q + 1 ≠ 0 := by positivity
    have h3 : (1 : ℝ) - 1 / q ^ 3 ≠ 0 := by
      have hlt : 1 / q ^ 3 < 1 := by rw [div_lt_one hq3]; linarith
      intro h
      linarith
    field_simp
    ring
  simp only [hfun] at hgeo
  rw [hval] at hgeo
  exact hgeo

end Regression

/-! ## §8 — general `e`: the pure-face boxes and their monomials -/

section FaceBox

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)]

/-- The ceiling threshold `⌈h(m−i)/m⌉` of the slope-`h/m` face at abscissa `i`. -/
def tF (m h i : ℕ) : ℕ := (h * (m - i) + (m - 1)) / m

theorem tF_le_iff {m : ℕ} (hm : 0 < m) (h i v : ℕ) :
    tF m h i ≤ v ↔ h * (m - i) ≤ m * v := by
  unfold tF
  rw [Nat.div_le_iff_le_mul_add_pred hm]
  omega

theorem tF_le_self {m : ℕ} (hm : 0 < m) (h i : ℕ) : tF m h i ≤ h := by
  unfold tF
  rw [Nat.div_le_iff_le_mul_add_pred hm]
  have h1 : h * (m - i) ≤ h * m := Nat.mul_le_mul_left h (Nat.sub_le m i)
  have h2 : h * m = m * h := Nat.mul_comm h m
  omega

/-- `npHeight` below the degree reads the coordinate's windowed valuation. -/
theorem npHeight_coe {m K : ℕ} (c : Coeff O m K) (i : Fin m) :
    npHeight c (i : ℕ) = resOrd (c i) := by
  unfold npHeight
  rw [dif_pos i.isLt]
  show resOrd (c ⟨(i : ℕ), i.isLt⟩) = resOrd (c i)
  rw [Fin.eta]

/-- **The pure-face box at slope `h/m`**: `v₀ = h` and the whole polygon at or above the
`(0,h)–(m,0)` face.  For `1 ≤ h < m` coprime to `m` these are the criterion-decided
shallow boxes; for `h ≥ m` (deep Eisenstein classes) they sit in the recentred copy. -/
def faceBox (O : Type*) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (m K h : ℕ) : Set (Coeff O m K) :=
  {c | npHeight c 0 = h ∧ ∀ i : Fin m, h * (m - (i : ℕ)) ≤ m * npHeight c (i : ℕ)}

theorem faceBox_subset_stratum {m K h : ℕ} (_hm : 0 < m) (hh : 1 ≤ h) (hK : 1 ≤ K) :
    faceBox O m K h ⊆ levelZeroStratum O m K (X ^ m) := by
  rintro c ⟨h0, hface⟩
  refine (mem_stratum_X_pow_iff hK c).2 fun i => ?_
  have hf := hface i
  rw [npHeight_coe] at hf
  rcases Nat.eq_zero_or_pos (resOrd (c i)) with h0' | h1'
  · rw [h0', Nat.mul_zero] at hf
    have hpos : 0 < h * (m - (i : ℕ)) :=
      Nat.mul_pos (by omega) (by have := i.isLt; omega)
    omega
  · exact h1'

theorem faceBox_subset_shallow {m K h : ℕ} (hm : 0 < m) (hh : h < m) :
    faceBox O m K h ⊆ shallowSet O m K := by
  rintro c ⟨h0, hface⟩
  simp only [shallowSet, Set.mem_setOf_eq]
  refine ⟨⟨0, hm⟩, ?_⟩
  have hnp : npHeight c 0 = resOrd (c ⟨0, hm⟩) := by
    unfold npHeight
    rw [dif_pos hm]
    rfl
  have hv : ((⟨0, hm⟩ : Fin m) : ℕ) = 0 := rfl
  rw [hv, Nat.sub_zero, ← hnp, h0]
  exact hh

/-- ★ **The pure-face boxes are criterion-decided** (`decidedAt_of_eisenstein_face`
consumed): a visible endpoint-spanning face of coprime slope `h/m` decides the class
totally ramified. -/
theorem faceBox_subset_decided [IsAdicComplete (maximalIdeal O) O] {m K h : ℕ}
    (hm : 0 < m) (hcop : Nat.Coprime h m) (hhK : h < K) :
    faceBox O m K h ⊆ decidedSet O m ⟨{(m, 1)}⟩ K := by
  rintro c ⟨h0, hface⟩
  have hm0 : npHeight c m = 0 := by
    unfold npHeight
    rw [dif_neg (lt_irrefl m)]
  have hsup : classNPSupport c h m = h * m := by
    refine le_antisymm ?_ (le_classNPSupport ?_)
    · have h2 := classNPSupport_le_apply c h m (le_refl m)
      rw [hm0] at h2
      omega
    · intro i hi
      rcases eq_or_lt_of_le hi with rfl | hilt
      · rw [hm0]
        omega
      · have hf := hface ⟨i, hilt⟩
        rw [npHeight_coe] at hf
        have hnp : npHeight c i = resOrd (c ⟨i, hilt⟩) := by
          unfold npHeight
          rw [dif_pos hilt]
          rfl
        rw [hnp]
        have hv : ((⟨i, hilt⟩ : Fin m) : ℕ) = i := rfl
        rw [hv] at hf
        have hdist : h * (m - i) + h * i = h * m := by
          rw [← Nat.mul_add, Nat.sub_add_cancel (le_of_lt hilt)]
        omega
  have h0att : NPAttains c h m 0 := by
    refine ⟨Nat.zero_le m, ?_⟩
    rw [h0, hsup]
    ring
  have hmatt : NPAttains c h m m := by
    refine ⟨le_refl m, ?_⟩
    rw [hm0, hsup]
    ring
  have hvis : NPVisibleAt c h m := by
    show classNPSupport c h m < m * K
    rw [hsup]
    calc h * m = m * h := Nat.mul_comm h m
      _ < m * K := mul_lt_mul_of_pos_left hhK hm
  exact decidedAt_of_eisenstein_face hm hcop h0att hmatt hvis

/-- The `K`-independent weight of the slope-`h/m` face box:
`wFace m h = 1 + h + Σ_{0<i<m} ⌈h(m−i)/m⌉` (the RW1-row exponent). -/
def wFace (m h : ℕ) : ℕ := 1 + h + ∑ i ∈ Finset.range (m - 1), tF m h (i + 1)

theorem wFace_le {m K h : ℕ} (hm : 0 < m) (hhK : h < K) : wFace m h ≤ m * K := by
  unfold wFace
  have hsum : ∑ i ∈ Finset.range (m - 1), tF m h (i + 1) ≤ (m - 1) * h := by
    calc ∑ i ∈ Finset.range (m - 1), tF m h (i + 1)
        ≤ ∑ _i ∈ Finset.range (m - 1), h :=
          Finset.sum_le_sum fun i _ => tF_le_self hm h (i + 1)
      _ = (m - 1) * h := by rw [Finset.sum_const, Finset.card_range, smul_eq_mul]
  have h1 : (m - 1) * h ≤ (m - 1) * K := Nat.mul_le_mul_left _ (le_of_lt hhK)
  have h2 : K + (m - 1) * K = m * K := by
    have h3 : m = (m - 1) + 1 := by omega
    calc K + (m - 1) * K = ((m - 1) + 1) * K := by ring
      _ = m * K := by rw [← h3]
  omega

/-- ★ **The face-box monomial** (exact, every finite level, uniform in `q, m, h`):
`#faceBox = (q−1)·q^(mK − wFace m h)`. -/
theorem card_faceBox {m K h : ℕ} (hm : 0 < m) (_hh : 1 ≤ h) (hhK : h < K) :
    Nat.card (faceBox O m K h : Set (Coeff O m K))
      = (residueCard O - 1) * residueCard O ^ (m * K - wFace m h) := by
  classical
  have htFK : ∀ i : ℕ, tF m h i ≤ K := fun i => le_trans (tF_le_self hm h i) (le_of_lt hhK)
  -- STEP 1: the pi-box form
  have hset : (faceBox O m K h : Set (Coeff O m K))
      = {c : Coeff O m K | ∀ i : Fin m, c i ∈
          (if (i : ℕ) = 0 then {x : Res O K | resOrd x = h}
           else {x : Res O K | tF m h (i : ℕ) ≤ resOrd x})} := by
    ext c
    simp only [faceBox, Set.mem_setOf_eq]
    constructor
    · rintro ⟨h0, hface⟩ i
      by_cases hi : (i : ℕ) = 0
      · rw [if_pos hi]
        have hieq : i = ⟨0, hm⟩ := Fin.ext hi
        have hnp : npHeight c 0 = resOrd (c ⟨0, hm⟩) := by
          unfold npHeight
          rw [dif_pos hm]
          rfl
        show resOrd (c i) = h
        rw [hieq, ← hnp, h0]
      · rw [if_neg hi]
        have hf := hface i
        rw [npHeight_coe] at hf
        exact (tF_le_iff hm h (i : ℕ) _).2 hf
    · intro hall
      have h0mem := hall ⟨0, hm⟩
      rw [if_pos (show ((⟨0, hm⟩ : Fin m) : ℕ) = 0 from rfl)] at h0mem
      have hnp : npHeight c 0 = resOrd (c ⟨0, hm⟩) := by
        unfold npHeight
        rw [dif_pos hm]
        rfl
      have h0 : npHeight c 0 = h := by rw [hnp]; exact h0mem
      refine ⟨h0, fun i => ?_⟩
      rw [npHeight_coe]
      by_cases hi : (i : ℕ) = 0
      · have hieq : i = ⟨0, hm⟩ := Fin.ext hi
        rw [hieq]
        have hv : ((⟨0, hm⟩ : Fin m) : ℕ) = 0 := rfl
        rw [hv, Nat.sub_zero, ← hnp, h0]
        exact le_of_eq (Nat.mul_comm h m)
      · have himem := hall i
        rw [if_neg hi] at himem
        exact (tF_le_iff hm h (i : ℕ) _).1 himem
  rw [hset, card_pi_set]
  -- STEP 2: per-factor cards
  have hfac : ∀ i : Fin m,
      Nat.card ((if (i : ℕ) = 0 then {x : Res O K | resOrd x = h}
          else {x : Res O K | tF m h (i : ℕ) ≤ resOrd x}) : Set (Res O K))
        = (if (i : ℕ) = 0 then (residueCard O - 1) * residueCard O ^ (K - h - 1)
           else residueCard O ^ (K - tF m h (i : ℕ))) := by
    intro i
    by_cases hi : (i : ℕ) = 0
    · rw [if_pos hi, if_pos hi, card_setOf_resOrd_eq hhK]
    · rw [if_neg hi, if_neg hi, card_setOf_le_resOrd (htFK (i : ℕ))]
  rw [Finset.prod_congr rfl (fun i _ => hfac i)]
  -- STEP 3: to a range product and split off the abscissa 0
  have hprod : (∏ i : Fin m, (if (i : ℕ) = 0
        then (residueCard O - 1) * residueCard O ^ (K - h - 1)
        else residueCard O ^ (K - tF m h (i : ℕ))))
      = ∏ i ∈ Finset.range m, (if i = 0
          then (residueCard O - 1) * residueCard O ^ (K - h - 1)
          else residueCard O ^ (K - tF m h i)) :=
    Fin.prod_univ_eq_prod_range
      (fun i => if i = 0 then (residueCard O - 1) * residueCard O ^ (K - h - 1)
        else residueCard O ^ (K - tF m h i)) m
  rw [hprod]
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  rw [Finset.prod_range_succ', if_pos (rfl : (0 : ℕ) = 0)]
  have hstep : ∀ i, (if i + 1 = 0
      then (residueCard O - 1) * residueCard O ^ (K - h - 1)
      else residueCard O ^ (K - tF (m' + 1) h (i + 1)))
      = residueCard O ^ (K - tF (m' + 1) h (i + 1)) := fun i => if_neg (Nat.succ_ne_zero i)
  rw [Finset.prod_congr rfl (fun i _ => hstep i), Finset.prod_pow_eq_pow_sum]
  -- STEP 4: exponent bookkeeping
  have hSadd : (∑ i ∈ Finset.range m', (K - tF (m' + 1) h (i + 1)))
      + (∑ i ∈ Finset.range m', tF (m' + 1) h (i + 1)) = m' * K := by
    rw [← Finset.sum_add_distrib,
      Finset.sum_congr rfl (fun i _ => Nat.sub_add_cancel (htFK (i + 1))),
      Finset.sum_const, Finset.card_range, smul_eq_mul]
  have hw : wFace (m' + 1) h = 1 + h + ∑ i ∈ Finset.range m', tF (m' + 1) h (i + 1) := rfl
  have hmK : (m' + 1) * K = m' * K + K := by ring
  have hexp : (∑ i ∈ Finset.range m', (K - tF (m' + 1) h (i + 1))) + (K - h - 1)
      = (m' + 1) * K - wFace (m' + 1) h := by
    rw [hw, hmK]
    omega
  calc residueCard O ^ (∑ i ∈ Finset.range m', (K - tF (m' + 1) h (i + 1)))
        * ((residueCard O - 1) * residueCard O ^ (K - h - 1))
      = (residueCard O - 1)
          * (residueCard O ^ (∑ i ∈ Finset.range m', (K - tF (m' + 1) h (i + 1)))
            * residueCard O ^ (K - h - 1)) := by ring
    _ = (residueCard O - 1) * residueCard O
          ^ ((∑ i ∈ Finset.range m', (K - tF (m' + 1) h (i + 1))) + (K - h - 1)) := by
        rw [pow_add]
    _ = (residueCard O - 1) * residueCard O ^ ((m' + 1) * K - wFace (m' + 1) h) := by
        rw [hexp]

end FaceBox

/-! ## §9 — the partition, THE NAMED REMAINDER, and the wiring -/

section Partition

/-- The admissible pure-face slopes at degree `m`: `1 ≤ h < m`, `gcd(h, m) = 1`. -/
def faceH (m : ℕ) : Finset ℕ := (Finset.range m).filter (fun h => 1 ≤ h ∧ Nat.Coprime h m)

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)]

/-- The union of the admissible pure-face boxes. -/
def pureFaceSet (O : Type*) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (m K : ℕ) : Set (Coeff O m K) :=
  {c | ∃ h ∈ faceH m, c ∈ faceBox O m K h}

/-- **THE NAMED REMAINDER COUNT**: the decided shallow stratum classes OUTSIDE every
admissible pure-face box — the general-position faces and the `e' < m` residual
refinements (CN2 §7's exact remainder).  `π`-free: the carrier is the cone set after
`range_fullLoopClassN_zero`. -/
def coneRemainderCount (O : Type*) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Finite (ResidueField O)] (m : ℕ) (σ : FactorizationType) (M : ℕ) : ℕ :=
  Nat.card (((decidedSet O m σ (M + m)
      ∩ levelZeroStratum O m (M + m) (X ^ m)
      ∩ shallowSet O m (M + m))
    \ pureFaceSet O m (M + m)) : Set (Coeff O m (M + m)))

variable [IsAdicComplete (maximalIdeal O) O]

/-- ★ **THE FINITE-LEVEL PARTITION** at the totally-ramified type: cone count = the
geometric monomial bank (one term per admissible slope) + the named remainder. -/
theorem coneCellCount_partition_ram {π : O} (hπ : Irreducible π) {m : ℕ} (hm : 0 < m)
    (M : ℕ) :
    coneCellCount O π m ⟨{(m, 1)}⟩ M 0
      = (∑ h ∈ faceH m, (residueCard O - 1) * residueCard O ^ (m * (M + m) - wFace m h))
        + coneRemainderCount O m ⟨{(m, 1)}⟩ M := by
  classical
  haveI : Fintype (Coeff O m (M + m)) := Fintype.ofFinite _
  rw [coneCellCount_zero_eq hπ hm ⟨{(m, 1)}⟩ M]
  have hPsub : pureFaceSet O m (M + m)
      ⊆ (decidedSet O m ⟨{(m, 1)}⟩ (M + m) ∩ levelZeroStratum O m (M + m) (X ^ m)
          ∩ shallowSet O m (M + m)) := by
    rintro c ⟨h, hh, hc⟩
    simp only [faceH, Finset.mem_filter, Finset.mem_range] at hh
    exact ⟨⟨faceBox_subset_decided hm hh.2.2 (by omega : h < M + m) hc,
      faceBox_subset_stratum hm hh.2.1 (by omega : 1 ≤ M + m) hc⟩,
      faceBox_subset_shallow hm hh.1 hc⟩
  have hsplit : Nat.card ((decidedSet O m ⟨{(m, 1)}⟩ (M + m)
        ∩ levelZeroStratum O m (M + m) (X ^ m) ∩ shallowSet O m (M + m))
          : Set (Coeff O m (M + m)))
      = Nat.card (pureFaceSet O m (M + m) : Set (Coeff O m (M + m)))
        + coneRemainderCount O m ⟨{(m, 1)}⟩ M := by
    unfold coneRemainderCount
    rw [Nat.card_coe_set_eq, Nat.card_coe_set_eq, Nat.card_coe_set_eq,
      Set.ncard_sdiff hPsub]
    have hle : (pureFaceSet O m (M + m)).ncard
        ≤ ((decidedSet O m ⟨{(m, 1)}⟩ (M + m) ∩ levelZeroStratum O m (M + m) (X ^ m)
            ∩ shallowSet O m (M + m)) : Set (Coeff O m (M + m))).ncard :=
      Set.ncard_le_ncard hPsub (Set.toFinite _)
    omega
  rw [hsplit]
  congr 1
  rw [natCard_eq_sum_fiber (pureFaceSet O m (M + m)) (fun c => npHeight c 0)
    (faceH m) ?hmem]
  case hmem =>
    rintro c ⟨h, hh, hc⟩
    rw [hc.1]
    exact hh
  refine Finset.sum_congr rfl fun h hh => ?_
  have hfibre : (pureFaceSet O m (M + m) ∩ (fun c => npHeight c 0) ⁻¹' {h}
      : Set (Coeff O m (M + m))) = faceBox O m (M + m) h := by
    ext c
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff,
      pureFaceSet, Set.mem_setOf_eq]
    constructor
    · rintro ⟨⟨h', hh', hc⟩, hφ⟩
      have hEq : h' = h := by rw [← hc.1]; exact hφ
      subst hEq
      exact hc
    · intro hc
      exact ⟨⟨h, hh, hc⟩, hc.1⟩
  rw [hfibre]
  simp only [faceH, Finset.mem_filter, Finset.mem_range] at hh
  exact card_faceBox hm hh.2.1 (by omega : h < M + m)

/-- At every other type the pure-face boxes contribute nothing (`decidedAt_unique`):
the cone IS the remainder. -/
theorem coneCellCount_eq_remainder_of_ne {π : O} (hπ : Irreducible π) {m : ℕ}
    (hm : 0 < m) {σ : FactorizationType} (hσ : σ ≠ ⟨{(m, 1)}⟩) (M : ℕ) :
    coneCellCount O π m σ M 0 = coneRemainderCount O m σ M := by
  have hset : (decidedSet O m σ (M + m) ∩ levelZeroStratum O m (M + m) (X ^ m)
        ∩ shallowSet O m (M + m))
      = ((decidedSet O m σ (M + m) ∩ levelZeroStratum O m (M + m) (X ^ m)
          ∩ shallowSet O m (M + m)) \ pureFaceSet O m (M + m)) := by
    ext c
    simp only [Set.mem_sdiff, Set.mem_inter_iff]
    constructor
    · rintro ⟨⟨hA, hS⟩, hsh⟩
      refine ⟨⟨⟨hA, hS⟩, hsh⟩, ?_⟩
      rintro ⟨h, hh, hbox⟩
      simp only [faceH, Finset.mem_filter, Finset.mem_range] at hh
      have hdec2 := faceBox_subset_decided hm hh.2.2 (by omega : h < M + m) hbox
      exact hσ (decidedAt_unique hA hdec2)
    · rintro ⟨⟨⟨hA, hS⟩, hsh⟩, -⟩
      exact ⟨⟨hA, hS⟩, hsh⟩
  rw [coneCellCount_zero_eq hπ hm σ M, hset]
  rfl

/-- Consistency with the first blood: at `m = 2`, ramified type, the remainder is
EMPTY — the sole admissible face box (`h = 1`) exhausts the cone. -/
theorem coneRemainder_two_ram_eq_zero (M : ℕ) :
    coneRemainderCount O 2 ⟨{(2, 1)}⟩ M = 0 := by
  unfold coneRemainderCount
  have hsub : (decidedSet O 2 ⟨{(2, 1)}⟩ (M + 2)
        ∩ levelZeroStratum O 2 (M + 2) (X ^ 2) ∩ shallowSet O 2 (M + 2))
      ⊆ pureFaceSet O 2 (M + 2) := by
    rw [coneSet_two_ram M]
    rintro c ⟨h0, h1⟩
    have hnp0 : npHeight c 0 = resOrd (c 0) := by
      have h2 := npHeight_coe c (0 : Fin 2)
      simpa using h2
    have hnp1 : npHeight c 1 = resOrd (c 1) := by
      have h2 := npHeight_coe c (1 : Fin 2)
      simpa using h2
    refine ⟨1, ?_, ?_, ?_⟩
    · simp only [faceH, Finset.mem_filter, Finset.mem_range]
      exact ⟨by omega, by omega, Nat.coprime_one_left 2⟩
    · rw [hnp0]
      exact h0
    · intro i
      fin_cases i
      · rw [hnp0, h0]
        omega
      · rw [hnp1]
        omega
  have hempty : ((decidedSet O 2 ⟨{(2, 1)}⟩ (M + 2)
        ∩ levelZeroStratum O 2 (M + 2) (X ^ 2) ∩ shallowSet O 2 (M + 2))
      \ pureFaceSet O 2 (M + 2)) = (∅ : Set (Coeff O 2 (M + 2))) :=
    Set.sdiff_eq_empty.mpr hsub
  rw [hempty, Nat.card_coe_set_eq, Set.ncard_empty]

end Partition

/-! ## §10 — ★★ the wiring: remainder laws ⟹ the cone laws ⟹ the census front -/

section Wiring

/-- **THE NAMED REMAINDER LAW at `(m, σ)`** — the input Prop the census now rests on: a
uniform rational pair for the normalized remainder count.  (Discharge territory:
general-position fractional faces via the NP face factorization — C61's open `ℓ`-half /
FP1's GC0 — and the `e' < m` pure faces via the residual-polynomial refinement, where
C.33/C133mh genuinely enter.) -/
def ConeRemainderLaw (m : ℕ) (σ : FactorizationType) : Prop :=
  ZcURLim (fun O _ _ _ _ _ _ M =>
    (coneRemainderCount O m σ M : ℝ) / ((residueCard O : ℕ) : ℝ) ^ (m * (M + m)))

/-- ★★ **The per-clause wiring**: the remainder law fires the `(m, σ)` clause — the
pure-face monomial bank is a closed `ZcURLim` sum, and the partition is exact at every
level. -/
theorem zeroConeClause_of_remainderLaw {m : ℕ} (hm : 0 < m) (σ : FactorizationType)
    (hR : ConeRemainderLaw m σ) : ZeroConeClause m σ := by
  by_cases hσ : σ = ⟨{(m, 1)}⟩
  · subst hσ
    have hface : ZcURLim (fun O _ _ _ _ _ _ M => ∑ h ∈ faceH m,
        ((((residueCard O : ℕ) : ℝ) - 1) / ((residueCard O : ℕ) : ℝ) ^ (wFace m h))) :=
      ZcURLim_sum (faceH m)
        (fun h => fun O _ _ _ _ _ _ _ =>
          (((residueCard O : ℕ) : ℝ) - 1) / ((residueCard O : ℕ) : ℝ) ^ (wFace m h))
        (fun h _ => ZcURLim_qmonomial (wFace m h))
    refine (hface.add hR).congr ?_
    intro O _ _ _ _ _ π hπ M
    show (∑ h ∈ faceH m, ((((residueCard O : ℕ) : ℝ) - 1)
          / ((residueCard O : ℕ) : ℝ) ^ (wFace m h)))
        + (coneRemainderCount O m ⟨{(m, 1)}⟩ M : ℝ)
            / ((residueCard O : ℕ) : ℝ) ^ (m * (M + m))
      = (coneCellCount O π m ⟨{(m, 1)}⟩ M 0 : ℝ)
          / ((residueCard O : ℕ) : ℝ) ^ (m * (M + m))
    rw [coneCellCount_partition_ram hπ hm M]
    have hq2 : 2 ≤ residueCard O := two_le_residueCard O
    have hqR : ((residueCard O : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    push_cast [Nat.cast_sub (by omega : 1 ≤ residueCard O)]
    rw [add_div, Finset.sum_div]
    congr 1
    refine Finset.sum_congr rfl fun h hh => ?_
    have hhm : h < m := by
      simp only [faceH, Finset.mem_filter, Finset.mem_range] at hh
      exact hh.1
    have hwle : wFace m h ≤ m * (M + m) := wFace_le hm (by omega : h < M + m)
    have hsplit2 : ((residueCard O : ℕ) : ℝ) ^ (m * (M + m))
        = ((residueCard O : ℕ) : ℝ) ^ (m * (M + m) - wFace m h)
          * ((residueCard O : ℕ) : ℝ) ^ (wFace m h) := by
      rw [← pow_add, Nat.sub_add_cancel hwle]
    rw [hsplit2]
    have hA : ((residueCard O : ℕ) : ℝ) ^ (m * (M + m) - wFace m h) ≠ 0 :=
      pow_ne_zero _ hqR
    have hw : ((residueCard O : ℕ) : ℝ) ^ (wFace m h) ≠ 0 := pow_ne_zero _ hqR
    field_simp
  · refine hR.congr ?_
    intro O _ _ _ _ _ π hπ M
    show (coneRemainderCount O m σ M : ℝ)
        / ((residueCard O : ℕ) : ℝ) ^ (m * (M + m))
      = (coneCellCount O π m σ M 0 : ℝ)
          / ((residueCard O : ℕ) : ℝ) ^ (m * (M + m))
    rw [coneCellCount_eq_remainder_of_ne hπ hm hσ M]

/-- ★★★ **The law-level wiring**: remainder laws at every `(m ≥ 4, σ)` — with the same
conditional supply `ZeroConeLaw` itself carries — fire the WHOLE zero-cone law. -/
theorem zeroConeLaw_of_remainderLaws
    (hR : ∀ m : ℕ, 4 ≤ m →
      (∀ k, k < m → ∀ σ' : FactorizationType, σ'.degree = k → DecidedValueLaw k σ') →
      ∀ σ : FactorizationType, σ.degree = m → Witnessed m σ → ConeRemainderLaw m σ) :
    ZeroConeLaw := by
  intro m hm hsm σ hσ hwit
  exact zeroConeClause_of_remainderLaw (by omega) σ (hR m hm hsm σ hσ hwit)

/-- The centred cone law from the remainder laws (CN0's bridge composed). -/
theorem centeredConeLaw_of_remainderLaws
    (hR : ∀ m : ℕ, 4 ≤ m →
      (∀ k, k < m → ∀ σ' : FactorizationType, σ'.degree = k → DecidedValueLaw k σ') →
      ∀ σ : FactorizationType, σ.degree = m → Witnessed m σ → ConeRemainderLaw m σ) :
    CenteredConeLaw :=
  centeredConeLaw_of_zeroCone (zeroConeLaw_of_remainderLaws hR)

/-- ★★★ **THE CENSUS FRONT, re-based**: the point cone law and the REMAINDER laws fire
the all-degree decided slice.  The fractional-cell obligation's pure-face sector is now
CLOSED; the open content is exactly `PointConeLaw` and `ConeRemainderLaw` at each
`(m ≥ 4, σ)`. -/
theorem decidedSliceAt_all_of_pointCone_remainder (hPC : PointConeLaw)
    (hR : ∀ m : ℕ, 4 ≤ m →
      (∀ k, k < m → ∀ σ' : FactorizationType, σ'.degree = k → DecidedValueLaw k σ') →
      ∀ σ : FactorizationType, σ.degree = m → Witnessed m σ → ConeRemainderLaw m σ) :
    ∀ n : ℕ, Uniformity.Density.DecidedSliceAt n :=
  decidedSliceAt_all_of_cones hPC (centeredConeLaw_of_remainderLaws hR)

end Wiring

end Uniformity.Density.IFCG24

end

/-! ## AXCHECK FOOTER — expect Lean core `{propext, Classical.choice, Quot.sound}`
everywhere; the C.33 cite must NOT occur. -/

#print axioms Uniformity.Density.IFCG24.range_fullLoopClassN_zero
#print axioms Uniformity.Density.IFCG24.coneCellCount_zero_eq
#print axioms Uniformity.Density.IFCG24.coneCellCount_two_ram
#print axioms Uniformity.Density.IFCG24.coneCellCount_two_ne
#print axioms Uniformity.Density.IFCG24.zeroConeClause_two
#print axioms Uniformity.Density.IFCG24.card_quadDepthSlice
#print axioms Uniformity.Density.IFCG24.quadDepthSlice_subset_range
#print axioms Uniformity.Density.IFCG24.quad_cone_geometric_regression
#print axioms Uniformity.Density.IFCG24.card_faceBox
#print axioms Uniformity.Density.IFCG24.coneCellCount_partition_ram
#print axioms Uniformity.Density.IFCG24.coneRemainder_two_ram_eq_zero
#print axioms Uniformity.Density.IFCG24.zeroConeClause_of_remainderLaw
#print axioms Uniformity.Density.IFCG24.zeroConeLaw_of_remainderLaws
#print axioms Uniformity.Density.IFCG24.decidedSliceAt_all_of_pointCone_remainder
