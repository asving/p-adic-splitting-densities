/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import Uniformity.ChapI.IFCG40

/-!
# Uniformity.ChapI.IFCG41 — [RDC 2026-08-30] the resultant-depth-graded fiber census:
the depth instrument, the exact graded count identities, the depth-`v` gap engine,
and the reduction of the split defect law to two named census laws

Stage RDC of the cone census (design record `runs/wave-c/verdict_RDC.md`; consumes SDL =
`IFCG40`).  SDL decomposed the split-sector convolution defect EXACTLY —
`convCount = #vis + [Σ_vis (multCount − 1) + Σ_stray multCount]` — and identified the
remaining `m ≥ 4` content as the mixing-graded census rationality plus the
decidedness-transfer criterion.  This file lands the census's INSTRUMENTS and the
transfer's UNIQUENESS ENGINE:

* **§1 THE DEPTH INSTRUMENT.**  `classRes` — the LIFT-FREE class-level resultant
  (mathlib's `Polynomial.resultant` of the class polynomials over the truncation ring;
  `classRes_proj` computes it as the truncation of any lift resultant, so the truncated
  resultant valuation is well-defined on classes).  `mixDepth` — the resultant depth of
  a pair of classes (the greatest `v ≤ N` with `π^v ∣ classRes`), with its exact-`v`
  lift bridge `mk_pow_dvd_classRes_iff`.
* **§2 THE EXACT GRADED COUNT IDENTITIES.**  `pairDepthFiber` — SDL's `multCount`
  fibers, graded by `mixDepth` — with ★ `pairFiber_eq_sum_pairDepthFiber` and
  ★ `multCount_eq_sum_pairDepthFiber` (the resultant-depth census of the convolution
  table, exact at every finite level).  On the cell side the collision sum grades by
  MULTIPLICITY — the exact shape SDL's decomposition dictates without the (open) fiber
  law `multCount = q^{depth}`: ★ `collisionTotal_graded`
  (`Σ_vis (multCount − 1) = Σ_k (k−1)·#{c ∈ vis : multCount c = k}`),
  `strayTotal_graded`, and ★★ `convCount_graded_census` — the fully graded exact
  census.  (The charged `Σ_v (strata)·(q^v − 1)` SHAPE is exactly this identity PLUS
  the fiber law; the fiber law is the named remainder, not silently assumed.)
* **§3 ★★ THE DEPTH-`v` GAP ENGINE** (the decidedness-transfer criterion's uniqueness
  mechanism).  `factor_perturbation_gap`: two monic factorizations of the same product
  mod `π^N` whose factors agree mod `π^{v+1}`, with a depth-`v` Bezout witness
  (`g·p + h·q = C(π^v)` — supplied from the resultant by
  `exists_bezout_of_not_dvd_resultant`), have factors agreeing mod `π^{N−v}` — the
  factors are determined mod `π^{N−v}` EXACTLY (ultrametric bootstrap: each round the
  quadratic error doubles the agreement level and the Bezout witness prices `v` of it
  away; the monic-leading-coefficient kill from SDL's cancellation genre runs the
  linear step).  Class-level: ★ `mulClass_fiber_gap` (the fiber separation at depth
  `v`), `mulClass_inj_of_coprime` (the `v = 0` firing: LEVEL-EXACT injectivity on
  residually pinned coprime pairs — the unit-corner genre, recovered as the depth-`0`
  instance).  ★ `decidedAt_mulClass_of_liftsFactor` — THE DECIDEDNESS-TRANSFER
  CRITERION at depth `v`: if every lift of the product class factors through the pair
  mod `π^{v+1}` (the `LiftsFactor` leg — the polygon-block HENSEL gap, the honest named
  existence remainder) and the factors are decided at the SHIFTED level `N − v`, then
  the product class is `(σ₁ + σ₂)`-decided at full level `N`.
* **§4 THE REDUCTION.**  `CollisionLaw m σ` / `StrayLaw m σ` — the two named census
  laws (the normalized collision excess and stray mass are uniform rational limits) —
  and ★★ `splitConvolutionDefectLaw_of_censusLaws`: they imply
  `SplitConvolutionDefectLaw m σ` at EVERY mass and type; with SSL's assembly,
  ★ `splitSectorLaw_of_censusLaws` closes `SplitSectorLaw m σ` under the `< m` value
  laws.  The `m ≥ 4` split leg is therefore OFFICIALLY: discharge `CollisionLaw` and
  `StrayLaw` (the Igusa-genre mixing census — via the fiber law `multCount = q^{depth}`
  whose instruments are §1–§3, or the measure route's declared `AX_cellRecursion`).

## THE HONEST FENCE

NOT proved here (the named remainder, exactly as SDL's fence predicted): (i) the
`q`-power fiber law (`pairDepthFiber` at depth `v` has size `q^v` per true
factorization — Smith normal form over the DVR / Igusa genre), hence the rationality of
`CollisionLaw`/`StrayLaw`; (ii) the Hensel existence leg `LiftsFactor` (polygon-block
factor lifting at depth `v` — completeness enters HERE, not in the uniqueness engine).
Everything named in §1–§4 above is machine-checked, uniform in `q`, `m`, `σ`, `N`.

## Axiom fence

Lean-core everywhere EXCEPT the four declarations that consume SDL's B.42-citing legs
(`one_le_multCount_of_vis` / `convCount_eq_card_vis_add_defect`):
`convCount_eq_card_vis_add_totals`, `convCount_graded_census`,
`splitConvolutionDefectLaw_of_censusLaws`, `splitSectorLaw_of_censusLaws` — Lean core +
the owner-signed B.42 cite `Uniformity.Density.Leaf.exists_slope_factorization`.  The
C.33 cites and `AX_cellRecursion` do NOT occur.  Zero sorries at landing.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

noncomputable section

namespace Uniformity.Density.IFCG41

open IsLocalRing Polynomial
open Uniformity.Density.Induction
open Uniformity.Density.IFCG14 (DecidedValueLaw)
open Uniformity.Density.IFCG24 (ZcURLim)
open Uniformity.Density.IFCG35 (SplitSectorLaw)
open Uniformity.Density.IFCG38 (splitSectorVis convPairs convCount mulClassAt
  SplitConvolutionDefectLaw splitSectorLaw_of_defectLaw)
open Uniformity.Density.IFCG40 (pairFiber multCount convCount_eq_sum_multCount
  one_le_multCount_of_vis convCount_eq_card_vis_add_defect)

/-! ## §0 — supply (private copies of landed idioms + small bridges) -/

section Supply

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

open Classical in
/-- `Nat.card` of a set in a finite type, as a `Finset.filter` card (IFCG40's private
bridge, copied). -/
private theorem natCard_set_eq_card_filter {α : Type*} [Fintype α] (s : Set α) :
    Nat.card s = (Finset.univ.filter (fun a => a ∈ s)).card := by
  rw [Nat.card_coe_set_eq, ← Set.ncard_coe_finset (Finset.univ.filter (fun a => a ∈ s))]
  congr 1
  ext a
  simp

open Classical in
/-- Fiberwise decomposition of a set count along a `ℕ`-valued map bounded on the set:
the range-indexed refinement of IFCG40's `natCard_eq_sum_fiber`. -/
private theorem natCard_eq_sum_range_fiber {α : Type*} [Finite α] (s : Set α)
    (φ : α → ℕ) (B : ℕ) (hφ : ∀ a ∈ s, φ a ≤ B) :
    Nat.card s = ∑ v ∈ Finset.range (B + 1), Nat.card ((s ∩ φ ⁻¹' {v} : Set α)) := by
  classical
  letI : Fintype α := Fintype.ofFinite α
  rw [natCard_set_eq_card_filter,
    Finset.card_eq_sum_card_fiberwise (f := φ) (t := Finset.range (B + 1))
      (fun a ha => Finset.mem_range.2 (by
        have := hφ a (Finset.mem_filter.mp ha).2
        omega))]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [natCard_set_eq_card_filter, Finset.filter_filter]
  congr 1
  ext a
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Set.mem_inter_iff,
    Set.mem_preimage, Set.mem_singleton_iff]

/-- Monotone weakening of constant-coefficient divisibility. -/
private theorem C_pow_dvd_mono {π : O} {s' s : ℕ} (hle : s' ≤ s) {f : Polynomial O}
    (h : Polynomial.C (π ^ s) ∣ f) : Polynomial.C (π ^ s') ∣ f :=
  dvd_trans (map_dvd Polynomial.C (pow_dvd_pow π hle)) h

end Supply

/-! ## §1 — THE DEPTH INSTRUMENT: the lift-free class resultant and the mixing depth -/

section DepthInstrument

attribute [local instance] Classical.propDecidable

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

/-- **The class-level resultant** — the resultant of the two class polynomials, computed
entirely over the truncation ring `Res O N` at the pinned sizes `(n₁, n₂)`; NO lift is
consulted, so well-definedness on classes is by construction. -/
noncomputable def classRes {n₁ n₂ N : ℕ} (c₁ : Coeff O n₁ N) (c₂ : Coeff O n₂ N) :
    Res O N :=
  Polynomial.resultant (monicPoly c₁) (monicPoly c₂) n₁ n₂

/-- `classRes` computes the truncation of ANY lift pair's resultant (mathlib's
`resultant_map_map` through the truncation map): the truncated resultant valuation is a
class invariant. -/
theorem classRes_proj {n₁ n₂ N : ℕ} (a₁ : Fin n₁ → O) (a₂ : Fin n₂ → O) :
    classRes (proj O n₁ N a₁) (proj O n₂ N a₂)
      = Ideal.Quotient.mk ((maximalIdeal O) ^ N)
          (Polynomial.resultant (monicPoly a₁) (monicPoly a₂) n₁ n₂) := by
  unfold classRes
  rw [← map_monicPoly_proj a₁, ← map_monicPoly_proj a₂, Polynomial.resultant_map_map]

/-- Divisibility by `mk (π^v)` in the truncation ring reads exactly as divisibility by
`π^v` on lifts, for `v ≤ N` (the correction `π^N z` is absorbed: `π^v ∣ π^N`). -/
theorem mk_pow_dvd_mk_iff {π : O} (hπ : Irreducible π) {v N : ℕ} (hvN : v ≤ N) (y : O) :
    (Ideal.Quotient.mk ((maximalIdeal O) ^ N) (π ^ v))
        ∣ Ideal.Quotient.mk ((maximalIdeal O) ^ N) y
      ↔ π ^ v ∣ y := by
  constructor
  · rintro ⟨z, hz⟩
    obtain ⟨w, rfl⟩ := Ideal.Quotient.mk_surjective z
    have hz' : Ideal.Quotient.mk ((maximalIdeal O) ^ N) y
        = Ideal.Quotient.mk ((maximalIdeal O) ^ N) (π ^ v * w) := by
      rw [map_mul]; exact hz
    have hmem : y - π ^ v * w ∈ (maximalIdeal O) ^ N :=
      (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mp hz'
    have hspan : (maximalIdeal O) ^ N = Ideal.span {π ^ N} := by
      rw [hπ.maximalIdeal_eq, Ideal.span_singleton_pow]
    rw [hspan, Ideal.mem_span_singleton] at hmem
    obtain ⟨u, hu⟩ := hmem
    refine ⟨w + π ^ (N - v) * u, ?_⟩
    have hsplit : π ^ N = π ^ v * π ^ (N - v) := by
      rw [← pow_add]; congr 1; omega
    have h1 : y = π ^ v * w + π ^ N * u := by rw [← hu]; ring
    rw [h1, hsplit]; ring
  · rintro ⟨z, rfl⟩
    exact ⟨Ideal.Quotient.mk _ z, by rw [← map_mul]⟩

/-- **The mixing depth of a pair of classes**: the greatest `v ≤ N` with
`π^v ∣ classRes` in the truncation ring — the class-level resultant valuation, capped at
the frame level.  (`v = 0` always holds; the cap `N` collects the provably-deep and the
genuinely-degenerate pairs alike.) -/
noncomputable def mixDepth (π : O) {n₁ n₂ N : ℕ} (c₁ : Coeff O n₁ N)
    (c₂ : Coeff O n₂ N) : ℕ :=
  Nat.findGreatest
    (fun v => (Ideal.Quotient.mk ((maximalIdeal O) ^ N) (π ^ v)) ∣ classRes c₁ c₂) N

theorem mixDepth_le (π : O) {n₁ n₂ N : ℕ} (c₁ : Coeff O n₁ N) (c₂ : Coeff O n₂ N) :
    mixDepth π c₁ c₂ ≤ N :=
  Nat.findGreatest_le N

theorem mixDepth_dvd (π : O) {n₁ n₂ N : ℕ} (c₁ : Coeff O n₁ N) (c₂ : Coeff O n₂ N) :
    (Ideal.Quotient.mk ((maximalIdeal O) ^ N) (π ^ mixDepth π c₁ c₂))
      ∣ classRes c₁ c₂ := by
  exact Nat.findGreatest_spec
    (P := fun v => (Ideal.Quotient.mk ((maximalIdeal O) ^ N) (π ^ v)) ∣ classRes c₁ c₂)
    (Nat.zero_le N) (by simp)

theorem le_mixDepth (π : O) {n₁ n₂ N v : ℕ} (hvN : v ≤ N) {c₁ : Coeff O n₁ N}
    {c₂ : Coeff O n₂ N}
    (hdvd : (Ideal.Quotient.mk ((maximalIdeal O) ^ N) (π ^ v)) ∣ classRes c₁ c₂) :
    v ≤ mixDepth π c₁ c₂ :=
  Nat.le_findGreatest hvN hdvd

end DepthInstrument

/-! ## §2 — THE EXACT GRADED COUNT IDENTITIES -/

section GradedCensus

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)]

/-- **The depth-graded pair fiber**: SDL's `multCount` fiber of one convolution-table
entry over a product cell, refined by the mixing depth of the pair. -/
noncomputable def pairDepthFiber (O : Type*) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [Finite (ResidueField O)] (π : O)
    (m : ℕ) (σ : FactorizationType) (M : ℕ)
    (p : (ℕ × ℕ) × Multiset (ℕ × ℕ)) (c : Coeff O m (M + m)) (v : ℕ) : ℕ :=
  if hpm : p.1.1 + p.1.2 = m then
    Nat.card ((((decidedSet O p.1.1 ⟨p.2⟩ (M + m))
        ×ˢ (decidedSet O p.1.2 ⟨σ.data - p.2⟩ (M + m)))
      ∩ (fun q : Coeff O p.1.1 (M + m) × Coeff O p.1.2 (M + m) =>
          mulClassAt hpm q.1 q.2) ⁻¹' {c}
      ∩ (fun q : Coeff O p.1.1 (M + m) × Coeff O p.1.2 (M + m) =>
          mixDepth π q.1 q.2) ⁻¹' {v} : Set _))
  else 0

/-- ★ **The depth-graded fiber census** — exact at every finite level: each pair fiber
partitions by the mixing depth `v ≤ M + m`. -/
theorem pairFiber_eq_sum_pairDepthFiber (π : O) (m : ℕ) (σ : FactorizationType) (M : ℕ)
    (p : (ℕ × ℕ) × Multiset (ℕ × ℕ)) (c : Coeff O m (M + m)) :
    pairFiber O m σ M p c
      = ∑ v ∈ Finset.range (M + m + 1), pairDepthFiber O π m σ M p c v := by
  unfold pairFiber pairDepthFiber
  by_cases hpm : p.1.1 + p.1.2 = m
  · simp only [dif_pos hpm]
    exact natCard_eq_sum_range_fiber
      (α := Coeff O p.1.1 (M + m) × Coeff O p.1.2 (M + m))
      (decidedSet O p.1.1 ⟨p.2⟩ (M + m) ×ˢ decidedSet O p.1.2 ⟨σ.data - p.2⟩ (M + m)
        ∩ (fun q => mulClassAt hpm q.1 q.2) ⁻¹' {c})
      (fun q => mixDepth π q.1 q.2) (M + m) (fun q _ => mixDepth_le π q.1 q.2)
  · simp only [dif_neg hpm]
    simp

/-- ★ **The resultant-depth census of the convolution table**: the multiplicity of every
product cell is the double sum of its depth-graded pair fibers — the collision sum is a
census over resultant-depth strata, exactly. -/
theorem multCount_eq_sum_pairDepthFiber (π : O) (m : ℕ) (σ : FactorizationType) (M : ℕ)
    (c : Coeff O m (M + m)) :
    multCount O m σ M c
      = ∑ p ∈ convPairs m σ, ∑ v ∈ Finset.range (M + m + 1),
          pairDepthFiber O π m σ M p c v := by
  unfold multCount
  exact Finset.sum_congr rfl fun p _ => pairFiber_eq_sum_pairDepthFiber π m σ M p c

/-- The multiplicity strata of the visible split sector: the visible cells hit exactly
`k` times by SDL's convolution table. -/
def visStrata (π : O) (m : ℕ) (σ : FactorizationType) (M : ℕ) (k : ℕ) :
    Set (Coeff O m (M + m)) :=
  {c | c ∈ splitSectorVis O π m σ M ∧ multCount O m σ M c = k}

noncomputable def visStrataCount (π : O) (m : ℕ) (σ : FactorizationType) (M : ℕ)
    (k : ℕ) : ℕ :=
  Nat.card (visStrata π m σ M k)

/-- The multiplicity strata of the stray sector (product cells outside the visible
split sector). -/
def strayStrata (π : O) (m : ℕ) (σ : FactorizationType) (M : ℕ) (k : ℕ) :
    Set (Coeff O m (M + m)) :=
  {c | c ∉ splitSectorVis O π m σ M ∧ multCount O m σ M c = k}

noncomputable def strayStrataCount (π : O) (m : ℕ) (σ : FactorizationType) (M : ℕ)
    (k : ℕ) : ℕ :=
  Nat.card (strayStrata π m σ M k)

/-- **The collision total** — SDL's collision excess `Σ_{c ∈ vis} (multCount c − 1)`,
as one instance-free `ℕ` (summed over the `Set.Finite` finset, so no `Fintype`
transport ever enters a statement). -/
noncomputable def collisionTotal (O : Type*) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [Finite (ResidueField O)] (π : O)
    (m : ℕ) (σ : FactorizationType) (M : ℕ) : ℕ :=
  ∑ c ∈ (Set.toFinite (splitSectorVis O π m σ M)).toFinset, (multCount O m σ M c - 1)

/-- **The stray total** — SDL's stray mass `Σ_{c ∉ vis} multCount c`. -/
noncomputable def strayTotal (O : Type*) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [Finite (ResidueField O)] (π : O)
    (m : ℕ) (σ : FactorizationType) (M : ℕ) : ℕ :=
  ∑ c ∈ (Set.toFinite ((splitSectorVis O π m σ M)ᶜ)).toFinset, multCount O m σ M c

/-- Every multiplicity is bounded by the table total (the grading's uniform range). -/
theorem multCount_le_convCount (m : ℕ) (σ : FactorizationType) (M : ℕ)
    [Fintype (Coeff O m (M + m))] (c : Coeff O m (M + m)) :
    multCount O m σ M c ≤ convCount O m σ M := by
  rw [convCount_eq_sum_multCount]
  exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ c)

/-- ★ **The graded collision identity** — the exact shape SDL's decomposition dictates:
the collision excess is the multiplicity-graded census
`Σ_k (k − 1) · #{c ∈ vis : multCount c = k}`.  (The charged `(q^v − 1)`-shape is this
identity composed with the OPEN fiber law `multCount = q^{depth}`; the composition is
deliberately not asserted.) -/
theorem collisionTotal_graded (π : O) {m : ℕ} (σ : FactorizationType) (M : ℕ)
    [Fintype (Coeff O m (M + m))] :
    collisionTotal O π m σ M
      = ∑ k ∈ Finset.range (convCount O m σ M + 1),
          (k - 1) * visStrataCount π m σ M k := by
  classical
  calc collisionTotal O π m σ M
      = ∑ c ∈ Finset.univ.filter (· ∈ splitSectorVis O π m σ M),
          (multCount O m σ M c - 1) := by
        unfold collisionTotal
        apply Finset.sum_congr _ (fun _ _ => rfl)
        ext c
        simp
    _ = ∑ k ∈ Finset.range (convCount O m σ M + 1),
          ∑ c ∈ (Finset.univ.filter (· ∈ splitSectorVis O π m σ M)).filter
            (fun c => multCount O m σ M c = k), (multCount O m σ M c - 1) :=
        (Finset.sum_fiberwise_of_maps_to
          (fun c _ => Finset.mem_range.2 (by
            have h1 := multCount_le_convCount (O := O) m σ M c
            omega)) _).symm
    _ = ∑ k ∈ Finset.range (convCount O m σ M + 1),
          (k - 1) * visStrataCount π m σ M k := by
        refine Finset.sum_congr rfl fun k _ => ?_
        have hconst : ∀ c ∈ (Finset.univ.filter (· ∈ splitSectorVis O π m σ M)).filter
            (fun c => multCount O m σ M c = k), multCount O m σ M c - 1 = k - 1 := by
          intro c hc
          rw [(Finset.mem_filter.mp hc).2]
        rw [Finset.sum_congr rfl hconst, Finset.sum_const, smul_eq_mul, mul_comm]
        congr 1
        rw [visStrataCount, natCard_set_eq_card_filter, Finset.filter_filter]
        congr 1
        ext c
        simp [visStrata]

/-- ★ The graded stray identity: the stray mass is `Σ_k k · #{c ∉ vis : multCount c = k}`. -/
theorem strayTotal_graded (π : O) {m : ℕ} (σ : FactorizationType) (M : ℕ)
    [Fintype (Coeff O m (M + m))] :
    strayTotal O π m σ M
      = ∑ k ∈ Finset.range (convCount O m σ M + 1),
          k * strayStrataCount π m σ M k := by
  classical
  calc strayTotal O π m σ M
      = ∑ c ∈ Finset.univ.filter (· ∉ splitSectorVis O π m σ M), multCount O m σ M c := by
        unfold strayTotal
        apply Finset.sum_congr _ (fun _ _ => rfl)
        ext c
        simp
    _ = ∑ k ∈ Finset.range (convCount O m σ M + 1),
          ∑ c ∈ (Finset.univ.filter (· ∉ splitSectorVis O π m σ M)).filter
            (fun c => multCount O m σ M c = k), multCount O m σ M c :=
        (Finset.sum_fiberwise_of_maps_to
          (fun c _ => Finset.mem_range.2 (by
            have h1 := multCount_le_convCount (O := O) m σ M c
            omega)) _).symm
    _ = ∑ k ∈ Finset.range (convCount O m σ M + 1),
          k * strayStrataCount π m σ M k := by
        refine Finset.sum_congr rfl fun k _ => ?_
        have hconst : ∀ c ∈ (Finset.univ.filter (· ∉ splitSectorVis O π m σ M)).filter
            (fun c => multCount O m σ M c = k), multCount O m σ M c = k := by
          intro c hc
          exact (Finset.mem_filter.mp hc).2
        rw [Finset.sum_congr rfl hconst, Finset.sum_const, smul_eq_mul, mul_comm]
        congr 1
        rw [strayStrataCount, natCard_set_eq_card_filter, Finset.filter_filter]
        congr 1
        ext c
        simp [strayStrata]

variable [IsAdicComplete (maximalIdeal O) O]

/-- SDL's exact defect decomposition, restated on the instance-free totals: the defect
IS `collisionTotal + strayTotal`, at every finite level. -/
theorem convCount_eq_card_vis_add_totals {π : O} (hπ : Irreducible π) {m : ℕ}
    (hm : 0 < m) (σ : FactorizationType) (M : ℕ) :
    convCount O m σ M
      = Nat.card (splitSectorVis O π m σ M)
        + (collisionTotal O π m σ M + strayTotal O π m σ M) := by
  classical
  letI : Fintype (Coeff O m (M + m)) := Fintype.ofFinite _
  have hcoll : collisionTotal O π m σ M
      = ∑ c ∈ Finset.univ.filter (· ∈ splitSectorVis O π m σ M),
          (multCount O m σ M c - 1) := by
    unfold collisionTotal
    apply Finset.sum_congr _ (fun _ _ => rfl)
    ext c
    simp
  have hstray : strayTotal O π m σ M
      = ∑ c ∈ Finset.univ.filter (· ∉ splitSectorVis O π m σ M), multCount O m σ M c := by
    unfold strayTotal
    apply Finset.sum_congr _ (fun _ _ => rfl)
    ext c
    simp
  rw [hcoll, hstray]
  exact convCount_eq_card_vis_add_defect hπ hm σ M

/-- ★★ **THE FULLY GRADED EXACT CENSUS** — at every finite level, every mass, every
type, every uniformizer:

    convCount = #vis + [ Σ_k (k−1)·#visStrata_k  +  Σ_k k·#strayStrata_k ]

— SDL's defect decomposition with both legs graded by table multiplicity.  The open
content of `SplitConvolutionDefectLaw` at `m ≥ 4` is exactly the rationality of the
normalized limits of these graded strata sums. -/
theorem convCount_graded_census {π : O} (hπ : Irreducible π) {m : ℕ}
    (hm : 0 < m) (σ : FactorizationType) (M : ℕ) [Fintype (Coeff O m (M + m))] :
    convCount O m σ M
      = Nat.card (splitSectorVis O π m σ M)
        + ((∑ k ∈ Finset.range (convCount O m σ M + 1),
              (k - 1) * visStrataCount π m σ M k)
          + ∑ k ∈ Finset.range (convCount O m σ M + 1),
              k * strayStrataCount π m σ M k) := by
  rw [← collisionTotal_graded π σ M, ← strayTotal_graded π σ M]
  exact convCount_eq_card_vis_add_totals hπ hm σ M

end GradedCensus

/-! ## §3 — ★★ THE DEPTH-`v` GAP ENGINE (the transfer criterion's uniqueness mechanism) -/

section GapEngine

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

/-- **The Bezout witness at depth `v`** from the resultant: if `π^{v+1}` does NOT divide
the pinned-size resultant, the elimination ideal reaches `π^v` (DVR factorization of the
resultant + mathlib's Sylvester-adjugate Bezout identity). -/
theorem exists_bezout_of_not_dvd_resultant {π : O} (hπ : Irreducible π)
    {g h : Polynomial O} {n₁ n₂ : ℕ} (hgd : g.natDegree ≤ n₁) (hhd : h.natDegree ≤ n₂)
    (hpos : n₁ ≠ 0 ∨ n₂ ≠ 0) {v : ℕ}
    (hv : ¬ π ^ (v + 1) ∣ Polynomial.resultant g h n₁ n₂) :
    ∃ p q : Polynomial O, g * p + h * q = Polynomial.C (π ^ v) := by
  have hres0 : Polynomial.resultant g h n₁ n₂ ≠ 0 := by
    intro h0
    exact hv (h0 ▸ dvd_zero _)
  obtain ⟨w, u, hwu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hres0 hπ
  have hwv : w ≤ v := by
    by_contra hcon
    exact hv (hwu ▸ ((pow_dvd_pow π (by omega : v + 1 ≤ w)).trans (dvd_mul_left _ _)))
  obtain ⟨p0, q0, hp0, hq0, hkey⟩ :=
    Polynomial.exists_mul_add_mul_eq_C_resultant g h hgd hhd hpos
  refine ⟨p0 * Polynomial.C ((↑u⁻¹ : O) * π ^ (v - w)),
    q0 * Polynomial.C ((↑u⁻¹ : O) * π ^ (v - w)), ?_⟩
  have hexp : (↑u : O) * π ^ w * ((↑u⁻¹ : O) * π ^ (v - w)) = π ^ v := by
    rw [mul_mul_mul_comm, Units.mul_inv, one_mul, ← pow_add]
    congr 1
    omega
  have hmain : (g * p0 + h * q0) * Polynomial.C ((↑u⁻¹ : O) * π ^ (v - w))
      = Polynomial.C (π ^ v) := by
    rw [hkey, ← Polynomial.C_mul, hwu, hexp]
  calc g * (p0 * Polynomial.C ((↑u⁻¹ : O) * π ^ (v - w)))
        + h * (q0 * Polynomial.C ((↑u⁻¹ : O) * π ^ (v - w)))
      = (g * p0 + h * q0) * Polynomial.C ((↑u⁻¹ : O) * π ^ (v - w)) := by ring
    _ = Polynomial.C (π ^ v) := hmain

/-- The monic kill (SDL's cancellation genre, run at an arbitrary modulus): if
`C(π^w)·α ≡ g·φ mod π^r` with `g` monic and `deg α < deg g`, then `π^{r−w}` divides
every coefficient of `α`.  (Map to `O ⧸ (π^r)`: a nonzero `φ̄` would give `ḡ·φ̄` a
nonvanishing coefficient at degree `≥ deg g`, where `C(π^w)·α` has none.) -/
private theorem C_pow_dvd_of_dvd_sub_monic_mul {π : O} (hπ : Irreducible π)
    {r w : ℕ} (hwr : w ≤ r) {g α φ : Polynomial O} (hg : g.Monic)
    (hdeg : α.degree < g.degree)
    (hE : Polynomial.C (π ^ r) ∣ Polynomial.C (π ^ w) * α - g * φ) :
    Polynomial.C (π ^ (r - w)) ∣ α := by
  rcases Nat.eq_zero_or_pos r with rfl | hr
  · have hw0 : w = 0 := Nat.le_zero.mp hwr
    subst hw0
    simp
  set ψ : O →+* O ⧸ Ideal.span {π ^ r} := Ideal.Quotient.mk (Ideal.span {π ^ r}) with hψ
  haveI : Nontrivial (O ⧸ Ideal.span {π ^ r}) := by
    refine Ideal.Quotient.nontrivial_iff.mpr ?_
    rw [Ne, Ideal.span_singleton_eq_top]
    intro hu
    exact hπ.not_isUnit ((isUnit_pow_iff hr.ne').mp hu)
  have hcoeffE := (Polynomial.C_dvd_iff_dvd_coeff _ _).mp hE
  have hmap : (Polynomial.C (π ^ w) * α).map ψ = (g * φ).map ψ := by
    have h0 : ((Polynomial.C (π ^ w) * α - g * φ).map ψ) = 0 := by
      refine Polynomial.ext fun i => ?_
      rw [Polynomial.coeff_map, Polynomial.coeff_zero]
      exact Ideal.Quotient.eq_zero_iff_mem.mpr
        (Ideal.mem_span_singleton.mpr (hcoeffE i))
    rw [Polynomial.map_sub, sub_eq_zero] at h0
    exact h0
  by_cases hφ : φ.map ψ = 0
  · -- the linear step: `π^w · α ≡ 0 mod π^r`, cancel `π^w`
    have hz : (Polynomial.C (π ^ w) * α).map ψ = 0 := by
      rw [hmap, Polynomial.map_mul, hφ, mul_zero]
    refine (Polynomial.C_dvd_iff_dvd_coeff _ _).mpr fun i => ?_
    have hzi : ψ (π ^ w * α.coeff i) = 0 := by
      have h1 := congrArg (fun f : Polynomial (O ⧸ Ideal.span {π ^ r}) => f.coeff i) hz
      simp only [Polynomial.coeff_map, Polynomial.coeff_zero] at h1
      rw [Polynomial.coeff_C_mul] at h1
      exact h1
    have hmem : π ^ r ∣ π ^ w * α.coeff i :=
      Ideal.mem_span_singleton.mp (Ideal.Quotient.eq_zero_iff_mem.mp hzi)
    have hsplit : π ^ r = π ^ w * π ^ (r - w) := by
      rw [← pow_add]; congr 1; omega
    rw [hsplit] at hmem
    exact (mul_dvd_mul_iff_left (pow_ne_zero w hπ.ne_zero)).mp hmem
  · -- the monic kill: the product's top coefficient survives where the LHS has none
    exfalso
    have hgm : (g.map ψ).Monic := hg.map ψ
    have hnd : (g.map ψ).natDegree = g.natDegree := hg.natDegree_map ψ
    have hcoeq := congrArg (fun f : Polynomial (O ⧸ Ideal.span {π ^ r}) =>
      f.coeff ((g.map ψ).natDegree + (φ.map ψ).natDegree)) hmap
    have hα0 : α.coeff ((g.map ψ).natDegree + (φ.map ψ).natDegree) = 0 := by
      refine Polynomial.coeff_eq_zero_of_degree_lt (lt_of_lt_of_le hdeg ?_)
      rw [Polynomial.degree_eq_natDegree hg.ne_zero]
      have hle : g.natDegree ≤ (g.map ψ).natDegree + (φ.map ψ).natDegree := by
        rw [hnd]; exact Nat.le_add_right _ _
      exact_mod_cast hle
    have hL : ((Polynomial.C (π ^ w) * α).map ψ).coeff
        ((g.map ψ).natDegree + (φ.map ψ).natDegree) = 0 := by
      rw [Polynomial.coeff_map, Polynomial.coeff_C_mul, hα0, mul_zero, map_zero]
    have hR : ((g * φ).map ψ).coeff ((g.map ψ).natDegree + (φ.map ψ).natDegree)
        = (φ.map ψ).leadingCoeff := by
      rw [Polynomial.map_mul, Polynomial.coeff_mul_degree_add_degree,
        hgm.leadingCoeff, one_mul]
    rw [hL, hR] at hcoeq
    exact Polynomial.leadingCoeff_ne_zero.mpr hφ hcoeq.symm

/-- ★★ **THE DEPTH-`v` GAP ENGINE** — finite-precision factorization uniqueness at the
shifted level: two monic factorizations of the same product mod `π^N`, with factors
agreeing mod `π^{v+1}` and a depth-`v` Bezout witness, have factors agreeing mod
`π^{N−v}`.  The factors are determined mod `π^{N−v}` EXACTLY — at `v = 0` this is
level-exact unit-corner injectivity; at `v > 0` it is the correct replacement for the
(refuted) two-sided level exactness. -/
theorem factor_perturbation_gap {π : O} (hπ : Irreducible π) {v N : ℕ}
    {g h g' h' : Polynomial O} (hg : g.Monic) (hh : h.Monic)
    (hg' : g'.Monic) (hh' : h'.Monic)
    (hdg : g'.natDegree = g.natDegree) (hdh : h'.natDegree = h.natDegree)
    (hbez : ∃ p q : Polynomial O, g * p + h * q = Polynomial.C (π ^ v))
    (hprod : Polynomial.C (π ^ N) ∣ g' * h' - g * h)
    (ha : Polynomial.C (π ^ (v + 1)) ∣ g' - g)
    (hb : Polynomial.C (π ^ (v + 1)) ∣ h' - h) :
    Polynomial.C (π ^ (N - v)) ∣ g' - g ∧ Polynomial.C (π ^ (N - v)) ∣ h' - h := by
  rcases Nat.lt_or_ge (v + 1) (N - v) with hNv | hNv
  case inr => exact ⟨C_pow_dvd_mono hNv ha, C_pow_dvd_mono hNv hb⟩
  obtain ⟨p, q, hpq⟩ := hbez
  -- the perturbations have degree strictly below their monic frames
  have hdeqg : g'.degree = g.degree := by
    rw [Polynomial.degree_eq_natDegree hg'.ne_zero,
      Polynomial.degree_eq_natDegree hg.ne_zero, hdg]
  have hda : (g' - g).degree < g.degree := by
    have h1 := Polynomial.degree_sub_lt hdeqg hg'.ne_zero
      (by rw [hg'.leadingCoeff, hg.leadingCoeff])
    rwa [hdeqg] at h1
  have hdeqh : h'.degree = h.degree := by
    rw [Polynomial.degree_eq_natDegree hh'.ne_zero,
      Polynomial.degree_eq_natDegree hh.ne_zero, hdh]
  have hdb : (h' - h).degree < h.degree := by
    have h1 := Polynomial.degree_sub_lt hdeqh hh'.ne_zero
      (by rw [hh'.leadingCoeff, hh.leadingCoeff])
    rwa [hdeqh] at h1
  -- ★ the bootstrap step: agreement at level `s ≥ v+1` upgrades to `min(2s, N) − v`
  have step : ∀ s, v + 1 ≤ s →
      Polynomial.C (π ^ s) ∣ g' - g → Polynomial.C (π ^ s) ∣ h' - h →
      Polynomial.C (π ^ (min (2 * s) N - v)) ∣ g' - g
        ∧ Polynomial.C (π ^ (min (2 * s) N - v)) ∣ h' - h := by
    intro s hs hsa hsb
    have hr2s : min (2 * s) N ≤ 2 * s := Nat.min_le_left _ _
    have hrN : min (2 * s) N ≤ N := Nat.min_le_right _ _
    have hvr : v ≤ min (2 * s) N := by omega
    -- the quadratic error is divisible at doubled level
    have hab : Polynomial.C (π ^ (2 * s)) ∣ (g' - g) * (h' - h) := by
      have h1 := mul_dvd_mul hsa hsb
      rwa [← Polynomial.C_mul, ← pow_add, ← two_mul] at h1
    have hDab : Polynomial.C (π ^ (min (2 * s) N))
        ∣ (g' * h' - g * h) - (g' - g) * (h' - h) :=
      dvd_sub (C_pow_dvd_mono hrN hprod) (C_pow_dvd_mono hr2s hab)
    -- the Bezout witness prices `π^v` of the linearized equation (left leg)
    have idA : Polynomial.C (π ^ v) * (g' - g) - g * (p * (g' - g) - q * (h' - h))
        = q * ((g' * h' - g * h) - (g' - g) * (h' - h)) := by
      rw [← hpq]; ring
    have hEA : Polynomial.C (π ^ (min (2 * s) N))
        ∣ Polynomial.C (π ^ v) * (g' - g) - g * (p * (g' - g) - q * (h' - h)) := by
      rw [idA]; exact hDab.mul_left q
    have hA := C_pow_dvd_of_dvd_sub_monic_mul hπ hvr hg hda hEA
    -- the mirror (right leg)
    have idB : Polynomial.C (π ^ v) * (h' - h) - h * (q * (h' - h) - p * (g' - g))
        = p * ((g' * h' - g * h) - (g' - g) * (h' - h)) := by
      rw [← hpq]; ring
    have hEB : Polynomial.C (π ^ (min (2 * s) N))
        ∣ Polynomial.C (π ^ v) * (h' - h) - h * (q * (h' - h) - p * (g' - g)) := by
      rw [idB]; exact hDab.mul_left p
    have hB := C_pow_dvd_of_dvd_sub_monic_mul hπ hvr hh hdb hEB
    exact ⟨hA, hB⟩
  -- iterate the step: the agreement level climbs to the shifted frame `N − v`
  have iter : ∀ k, Polynomial.C (π ^ min (v + 1 + k) (N - v)) ∣ g' - g
      ∧ Polynomial.C (π ^ min (v + 1 + k) (N - v)) ∣ h' - h := by
    intro k
    induction k with
    | zero => exact ⟨C_pow_dvd_mono (by omega) ha, C_pow_dvd_mono (by omega) hb⟩
    | succ k ih =>
      have hsge : v + 1 ≤ min (v + 1 + k) (N - v) := by omega
      have hstep := step (min (v + 1 + k) (N - v)) hsge ih.1 ih.2
      have harith : min (v + 1 + (k + 1)) (N - v)
          ≤ min (2 * min (v + 1 + k) (N - v)) N - v := by omega
      exact ⟨C_pow_dvd_mono harith hstep.1, C_pow_dvd_mono harith hstep.2⟩
  have hfin := iter N
  have harith2 : min (v + 1 + N) (N - v) = N - v := by omega
  rw [harith2] at hfin
  exact hfin

/-- Coefficientwise divisibility of the vectors transfers to the monic frames (the top
coefficients agree identically). -/
private theorem C_dvd_monicPoly_sub {n : ℕ} {a b : Fin n → O} {d : O}
    (hc : ∀ i, d ∣ (b i - a i)) : Polynomial.C d ∣ monicPoly b - monicPoly a := by
  refine (Polynomial.C_dvd_iff_dvd_coeff _ _).mpr fun i => ?_
  rcases Nat.lt_or_ge i n with hi | hi
  · rw [Polynomial.coeff_sub, monicPoly_coeff_lt b hi, monicPoly_coeff_lt a hi]
    exact hc ⟨i, hi⟩
  · have e1 : (monicPoly b).coeff i = (monicPoly a).coeff i := by
      rcases eq_or_lt_of_le hi with heqi | hlt
      · rw [← heqi]
        have hb1 : (monicPoly b).coeff n = 1 := by
          have h1 := (monicPoly_monic b).coeff_natDegree
          rwa [monicPoly_natDegree] at h1
        have ha1 : (monicPoly a).coeff n = 1 := by
          have h1 := (monicPoly_monic a).coeff_natDegree
          rwa [monicPoly_natDegree] at h1
        rw [hb1, ha1]
      · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [monicPoly_natDegree]; exact hlt),
          Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [monicPoly_natDegree]; exact hlt)]
    rw [Polynomial.coeff_sub, e1, sub_self]
    exact dvd_zero d

/-- Equality of `mulClass` products at level `N` is exactly `π^N`-divisibility of the
lift-product difference (below the top degree from the class equality; at and above it
from monicity — IFCG40's cancellation-genre case analysis). -/
private theorem C_pow_dvd_mul_sub_of_mulClass_eq {π : O} (hπ : Irreducible π)
    {n₁ n₂ N : ℕ} {a₁ b₁ : Fin n₁ → O} {a₂ b₂ : Fin n₂ → O}
    (heq : mulClass (proj O n₁ N a₁) (proj O n₂ N a₂)
         = mulClass (proj O n₁ N b₁) (proj O n₂ N b₂)) :
    Polynomial.C (π ^ N) ∣ monicPoly b₁ * monicPoly b₂ - monicPoly a₁ * monicPoly a₂ := by
  refine (Polynomial.C_dvd_iff_dvd_coeff _ _).mpr fun i => ?_
  have hspan : (maximalIdeal O) ^ N = Ideal.span {π ^ N} := by
    rw [hπ.maximalIdeal_eq, Ideal.span_singleton_pow]
  rcases Nat.lt_or_ge i (n₁ + n₂) with hi | hi
  · have h1 : proj O (n₁ + n₂) N (fun j => (monicPoly a₁ * monicPoly a₂).coeff (j : ℕ))
        = proj O (n₁ + n₂) N (fun j => (monicPoly b₁ * monicPoly b₂).coeff (j : ℕ)) := by
      rw [mulClass_proj, mulClass_proj, heq]
    have h2 := congrFun h1 ⟨i, hi⟩
    have h3 : (monicPoly b₁ * monicPoly b₂).coeff i - (monicPoly a₁ * monicPoly a₂).coeff i
        ∈ (maximalIdeal O) ^ N := (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mp h2.symm
    rw [hspan, Ideal.mem_span_singleton] at h3
    rw [Polynomial.coeff_sub]
    exact h3
  · have hd : (monicPoly a₁ * monicPoly a₂).natDegree = n₁ + n₂ := by
      rw [(monicPoly_monic a₁).natDegree_mul (monicPoly_monic a₂),
        monicPoly_natDegree, monicPoly_natDegree]
    have hd' : (monicPoly b₁ * monicPoly b₂).natDegree = n₁ + n₂ := by
      rw [(monicPoly_monic b₁).natDegree_mul (monicPoly_monic b₂),
        monicPoly_natDegree, monicPoly_natDegree]
    have e1 : (monicPoly b₁ * monicPoly b₂).coeff i
        = (monicPoly a₁ * monicPoly a₂).coeff i := by
      rcases eq_or_lt_of_le hi with heqi | hlt
      · rw [← heqi]
        have hb1 : (monicPoly b₁ * monicPoly b₂).coeff (n₁ + n₂) = 1 := by
          rw [← hd']
          exact ((monicPoly_monic b₁).mul (monicPoly_monic b₂)).coeff_natDegree
        have ha1 : (monicPoly a₁ * monicPoly a₂).coeff (n₁ + n₂) = 1 := by
          rw [← hd]
          exact ((monicPoly_monic a₁).mul (monicPoly_monic a₂)).coeff_natDegree
        rw [hb1, ha1]
      · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [hd']; exact hlt),
          Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [hd]; exact hlt)]
    rw [Polynomial.coeff_sub, e1, sub_self]
    exact dvd_zero _

/-- ★ **The class-level fiber separation at depth `v`**: two lift pairs of the same
`mulClass` product at level `N`, agreeing coefficientwise mod `π^{v+1}`, with a
depth-`v` Bezout witness on the first pair, agree coefficientwise mod `π^{N−v}` — the
pair-map fiber through a depth-`v` pair is discrete at radius `π^{N−v}`. -/
theorem mulClass_fiber_gap {π : O} (hπ : Irreducible π) {n₁ n₂ N v : ℕ}
    {a₁ b₁ : Fin n₁ → O} {a₂ b₂ : Fin n₂ → O}
    (hbez : ∃ p q : Polynomial O,
      monicPoly a₁ * p + monicPoly a₂ * q = Polynomial.C (π ^ v))
    (hc₁ : ∀ i, π ^ (v + 1) ∣ (b₁ i - a₁ i)) (hc₂ : ∀ i, π ^ (v + 1) ∣ (b₂ i - a₂ i))
    (heq : mulClass (proj O n₁ N a₁) (proj O n₂ N a₂)
         = mulClass (proj O n₁ N b₁) (proj O n₂ N b₂)) :
    (∀ i, π ^ (N - v) ∣ (b₁ i - a₁ i)) ∧ (∀ i, π ^ (N - v) ∣ (b₂ i - a₂ i)) := by
  have hprod := C_pow_dvd_mul_sub_of_mulClass_eq hπ heq
  have ha' : Polynomial.C (π ^ (v + 1)) ∣ monicPoly b₁ - monicPoly a₁ :=
    C_dvd_monicPoly_sub hc₁
  have hb' : Polynomial.C (π ^ (v + 1)) ∣ monicPoly b₂ - monicPoly a₂ :=
    C_dvd_monicPoly_sub hc₂
  have hgap := factor_perturbation_gap hπ (monicPoly_monic a₁) (monicPoly_monic a₂)
    (monicPoly_monic b₁) (monicPoly_monic b₂)
    (by rw [monicPoly_natDegree, monicPoly_natDegree])
    (by rw [monicPoly_natDegree, monicPoly_natDegree]) hbez hprod ha' hb'
  constructor
  · intro i
    have h1 := (Polynomial.C_dvd_iff_dvd_coeff _ _).mp hgap.1 (i : ℕ)
    rwa [Polynomial.coeff_sub, monicPoly_coeff_lt b₁ i.isLt,
      monicPoly_coeff_lt a₁ i.isLt] at h1
  · intro i
    have h1 := (Polynomial.C_dvd_iff_dvd_coeff _ _).mp hgap.2 (i : ℕ)
    rwa [Polynomial.coeff_sub, monicPoly_coeff_lt b₂ i.isLt,
      monicPoly_coeff_lt a₂ i.isLt] at h1

/-- ★ **The `v = 0` firing — level-exact injectivity at the unit corner**: coprime lift
pairs pinned residually (factors agreeing mod `π`) are determined LEVEL-EXACTLY by
their product class — IFCG16 §6/XHS §3's genre, recovered as the depth-`0` instance of
the gap engine. -/
theorem mulClass_inj_of_coprime {π : O} (hπ : Irreducible π) {n₁ n₂ N : ℕ}
    {a₁ b₁ : Fin n₁ → O} {a₂ b₂ : Fin n₂ → O}
    (hcop : IsCoprime (monicPoly a₁) (monicPoly a₂))
    (hc₁ : ∀ i, π ∣ (b₁ i - a₁ i)) (hc₂ : ∀ i, π ∣ (b₂ i - a₂ i))
    (heq : mulClass (proj O n₁ N a₁) (proj O n₂ N a₂)
         = mulClass (proj O n₁ N b₁) (proj O n₂ N b₂)) :
    proj O n₁ N a₁ = proj O n₁ N b₁ ∧ proj O n₂ N a₂ = proj O n₂ N b₂ := by
  obtain ⟨u, w, huw⟩ := hcop
  have hbez : ∃ p q : Polynomial O,
      monicPoly a₁ * p + monicPoly a₂ * q = Polynomial.C (π ^ 0) := by
    refine ⟨u, w, ?_⟩
    rw [pow_zero, map_one, mul_comm (monicPoly a₁) u, mul_comm (monicPoly a₂) w]
    exact huw
  have hgap := mulClass_fiber_gap hπ hbez
    (fun i => by simpa using hc₁ i) (fun i => by simpa using hc₂ i) heq
  have hspan : (maximalIdeal O) ^ N = Ideal.span {π ^ N} := by
    rw [hπ.maximalIdeal_eq, Ideal.span_singleton_pow]
  constructor
  · funext i
    have h1 : π ^ N ∣ (b₁ i - a₁ i) := by simpa using hgap.1 i
    have h2 : π ^ N ∣ (a₁ i - b₁ i) := dvd_sub_comm.mp h1
    show Ideal.Quotient.mk ((maximalIdeal O) ^ N) (a₁ i)
        = Ideal.Quotient.mk ((maximalIdeal O) ^ N) (b₁ i)
    exact (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mpr
      (by rw [hspan]; exact Ideal.mem_span_singleton.mpr h2)
  · funext i
    have h1 : π ^ N ∣ (b₂ i - a₂ i) := by simpa using hgap.2 i
    have h2 : π ^ N ∣ (a₂ i - b₂ i) := dvd_sub_comm.mp h1
    show Ideal.Quotient.mk ((maximalIdeal O) ^ N) (a₂ i)
        = Ideal.Quotient.mk ((maximalIdeal O) ^ N) (b₂ i)
    exact (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mpr
      (by rw [hspan]; exact Ideal.mem_span_singleton.mpr h2)

/-- **The Hensel existence leg** (the honest named remainder of the transfer): every
monic lift of the product class factors through the pair mod `π^{v+1}`.  Its discharge
is the polygon-block factor-lifting engine (completeness enters here); the uniqueness
engine above is its exact complement. -/
def LiftsFactor (π : O) (v : ℕ) {n₁ n₂ : ℕ} (N : ℕ)
    (a₁ : Fin n₁ → O) (a₂ : Fin n₂ → O) : Prop :=
  ∀ F : Fin (n₁ + n₂) → O,
    proj O (n₁ + n₂) N F = mulClass (proj O n₁ N a₁) (proj O n₂ N a₂) →
    ∃ (b₁ : Fin n₁ → O) (b₂ : Fin n₂ → O),
      monicPoly F = monicPoly b₁ * monicPoly b₂
      ∧ (∀ i, π ^ (v + 1) ∣ (b₁ i - a₁ i)) ∧ (∀ i, π ^ (v + 1) ∣ (b₂ i - a₂ i))

/-- ★ **THE DECIDEDNESS-TRANSFER CRITERION AT DEPTH `v`**: given the depth-`v` Bezout
witness, the Hensel existence leg, and the factors DECIDED AT THE SHIFTED LEVEL `N − v`,
the product class is `(σ₁ + σ₂)`-decided at full level `N` — the gap engine pins every
lift's factors mod `π^{N−v}` where the shifted decidedness reads their types. -/
theorem decidedAt_mulClass_of_liftsFactor {π : O} (hπ : Irreducible π)
    {n₁ n₂ N v : ℕ}
    {a₁ : Fin n₁ → O} {a₂ : Fin n₂ → O} {σ₁ σ₂ : FactorizationType}
    (hbez : ∃ p q : Polynomial O,
      monicPoly a₁ * p + monicPoly a₂ * q = Polynomial.C (π ^ v))
    (hE : LiftsFactor π v N a₁ a₂)
    (hd₁ : DecidedAt O n₁ σ₁ (N - v) (proj O n₁ (N - v) a₁))
    (hd₂ : DecidedAt O n₂ σ₂ (N - v) (proj O n₂ (N - v) a₂)) :
    DecidedAt O (n₁ + n₂) ⟨σ₁.data + σ₂.data⟩ N
      (mulClass (proj O n₁ N a₁) (proj O n₂ N a₂)) := by
  intro F hF
  obtain ⟨b₁, b₂, hfac, hcb₁, hcb₂⟩ := hE F hF
  -- the two pairs produce the same level-`N` product class
  have heqc : mulClass (proj O n₁ N a₁) (proj O n₂ N a₂)
      = mulClass (proj O n₁ N b₁) (proj O n₂ N b₂) := by
    rw [← hF, ← mulClass_proj]
    congr 1
    funext i
    rw [← hfac]
    exact (monicPoly_coeff_lt F i.isLt).symm
  -- the gap engine pins the factors at the shifted level
  have hgap := mulClass_fiber_gap hπ hbez hcb₁ hcb₂ heqc
  have hp₁ : proj O n₁ (N - v) b₁ = proj O n₁ (N - v) a₁ := by
    funext i
    show Ideal.Quotient.mk ((maximalIdeal O) ^ (N - v)) (b₁ i)
        = Ideal.Quotient.mk ((maximalIdeal O) ^ (N - v)) (a₁ i)
    refine (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mpr ?_
    rw [hπ.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    exact hgap.1 i
  have hp₂ : proj O n₂ (N - v) b₂ = proj O n₂ (N - v) a₂ := by
    funext i
    show Ideal.Quotient.mk ((maximalIdeal O) ^ (N - v)) (b₂ i)
        = Ideal.Quotient.mk ((maximalIdeal O) ^ (N - v)) (a₂ i)
    refine (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mpr ?_
    rw [hπ.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    exact hgap.2 i
  -- the shifted decidedness reads off the factor types
  have ht₁ : typeOf (monicPoly b₁) = σ₁ := hd₁ b₁ hp₁
  have ht₂ : typeOf (monicPoly b₂) = σ₂ := hd₂ b₂ hp₂
  rw [hfac]
  refine FactorizationType.ext ?_
  rw [typeOf_mul (monicPoly_monic b₁) (monicPoly_monic b₂), ht₁, ht₂]

end GapEngine

/-! ## §4 — THE REDUCTION: the defect law rests on two named census laws -/

section Reduction

/-- **THE COLLISION LAW at `(m, σ)`** — the first named census remainder: the normalized
collision excess of the convolution table over the visible split sector is a uniform
rational limit. -/
def CollisionLaw (m : ℕ) (σ : FactorizationType) : Prop :=
  ZcURLim (fun O _ _ _ _ _ π M =>
    (collisionTotal O π m σ M : ℝ) / ((residueCard O : ℕ) : ℝ) ^ (m * (M + m)))

/-- **THE STRAY LAW at `(m, σ)`** — the second named census remainder: the normalized
stray mass of the convolution table is a uniform rational limit. -/
def StrayLaw (m : ℕ) (σ : FactorizationType) : Prop :=
  ZcURLim (fun O _ _ _ _ _ π M =>
    (strayTotal O π m σ M : ℝ) / ((residueCard O : ℕ) : ℝ) ^ (m * (M + m)))

/-- ★★ **THE REDUCTION** — at every mass and every type: the collision and stray census
laws imply the convolution defect law.  With SDL's equivalence, the `m ≥ 4` split leg
is OFFICIALLY the discharge of `CollisionLaw` and `StrayLaw`. -/
theorem splitConvolutionDefectLaw_of_censusLaws {m : ℕ} (hm : 0 < m)
    (σ : FactorizationType) (hcoll : CollisionLaw m σ) (hstray : StrayLaw m σ) :
    SplitConvolutionDefectLaw m σ := by
  unfold CollisionLaw at hcoll
  unfold StrayLaw at hstray
  unfold SplitConvolutionDefectLaw
  refine (Uniformity.Density.IFCG24.ZcURLim.add hcoll hstray).congr ?_
  intro O _ _ _ _ _ π hπ M
  show (collisionTotal O π m σ M : ℝ) / ((residueCard O : ℕ) : ℝ) ^ (m * (M + m))
      + (strayTotal O π m σ M : ℝ) / ((residueCard O : ℕ) : ℝ) ^ (m * (M + m))
    = ((convCount O m σ M : ℝ) - (Nat.card (splitSectorVis O π m σ M) : ℝ))
        / ((residueCard O : ℕ) : ℝ) ^ (m * (M + m))
  rw [← add_div]
  congr 1
  have hid := convCount_eq_card_vis_add_totals (O := O) hπ hm σ M
  rw [hid]
  push_cast
  ring

/-- ★ The socket closure: under the `< m` decided value laws (the recursion's own
supply), the two census laws close `SplitSectorLaw m σ` outright — at EVERY mass,
including the open `m ≥ 4` ramified strata. -/
theorem splitSectorLaw_of_censusLaws {m : ℕ} (hm : 0 < m) (σ : FactorizationType)
    (hDV : ∀ k, k < m → ∀ σ' : FactorizationType, σ'.degree = k → DecidedValueLaw k σ')
    (hcoll : CollisionLaw m σ) (hstray : StrayLaw m σ) :
    SplitSectorLaw m σ :=
  splitSectorLaw_of_defectLaw hm σ hDV
    (splitConvolutionDefectLaw_of_censusLaws hm σ hcoll hstray)

end Reduction

end Uniformity.Density.IFCG41

end

/-! ## AXCHECK FOOTER — everything expects Lean core `{propext, Classical.choice,
Quot.sound}` EXCEPT `convCount_eq_card_vis_add_totals`, `convCount_graded_census`,
`splitConvolutionDefectLaw_of_censusLaws`, `splitSectorLaw_of_censusLaws` (Lean core +
the owner-signed B.42 cite `Uniformity.Density.Leaf.exists_slope_factorization`, through
SDL's refinement map).  C.33 and `AX_cellRecursion` must NOT occur. -/
#print axioms Uniformity.Density.IFCG41.classRes_proj
#print axioms Uniformity.Density.IFCG41.mk_pow_dvd_mk_iff
#print axioms Uniformity.Density.IFCG41.mixDepth_dvd
#print axioms Uniformity.Density.IFCG41.pairFiber_eq_sum_pairDepthFiber
#print axioms Uniformity.Density.IFCG41.multCount_eq_sum_pairDepthFiber
#print axioms Uniformity.Density.IFCG41.multCount_le_convCount
#print axioms Uniformity.Density.IFCG41.collisionTotal_graded
#print axioms Uniformity.Density.IFCG41.strayTotal_graded
#print axioms Uniformity.Density.IFCG41.convCount_eq_card_vis_add_totals
#print axioms Uniformity.Density.IFCG41.convCount_graded_census
#print axioms Uniformity.Density.IFCG41.exists_bezout_of_not_dvd_resultant
#print axioms Uniformity.Density.IFCG41.factor_perturbation_gap
#print axioms Uniformity.Density.IFCG41.mulClass_fiber_gap
#print axioms Uniformity.Density.IFCG41.mulClass_inj_of_coprime
#print axioms Uniformity.Density.IFCG41.decidedAt_mulClass_of_liftsFactor
#print axioms Uniformity.Density.IFCG41.splitConvolutionDefectLaw_of_censusLaws
#print axioms Uniformity.Density.IFCG41.splitSectorLaw_of_censusLaws
