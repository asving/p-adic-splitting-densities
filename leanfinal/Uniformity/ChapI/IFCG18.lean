/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import Uniformity.ChapI.IFCG17

/-!
# Uniformity.ChapI.IFCG18 — [FP3 2026-08-29] the multi-point census, the reduction, and
THE SINGLE-POINT KERNEL

FP2 (`IFCG17.lean`, `runs/wave-c/verdict_FP2.md`) landed the whole multi-point machine
room: the stratum-refined decided counts, the decided-refinement, the binary count
convolution, the `TypeAlg` product law `stratPoly_mul`, the primary-pattern layer with the
double count `sum_sigma_fiber_eq`, and the exact collision peel `VAgg_cons_eq`.  This file
finishes the campaign's reduction:

* **§1 the labelled/unlabelled exchange** (`VAgg_eq_fiber`): on SIMPLE block systems (one
  exponent per residual point) the distinct-tuple aggregate is exactly
  `multPattern π • Σ_{g ∈ fiber(π, A)} stratPoly g` — induction through the avoidance
  head-peel, the coprime `stratPoly_mul`, and §5b's double count.  `multPattern π` is the
  labelling multiplicity `∏_{(δ,e)} (count (δ,e))!`.
* **§2 the uniform-rational-limit calculus** `URLim`: families of real sequences indexed
  by the complete DVR with ONE `Polynomial ℚ` pair as limit (both denominator
  obligations), closed under constants, `+`, `−`, `×`, and `Finset` sums — the assembly
  algebra for everything below.
* **§3 ★ THE NAMED KERNELS — the campaign's LAST statements.**
  `SinglePointAggregateLaw`: for every super-block `b` of mass ≤ m — EXCLUDING the
  self-referential pure deep-linear block `(1, [m])` — and every type-coefficient `s`,
  the normalized single-point aggregate `(SPAgg O N b ∅) s / q^(b.mass·N)` is a `URLim`
  family, conditionally on the value laws below `m`.  `DeepLinearClusterLaw`: the
  loop-corrected `{(1, m)}` pattern cell of `nonloopDecidedSet` has one uniform rational
  limit.  Everything else in the census is PROVED from these two.
* **§4 the limit propagation** (`vaggFamily_URLim` = the stub's `V_tendsto`): by the
  collision peel, every admissible `VAgg` family is a `URLim`; by §1, so is every
  non-deep pattern-fiber census family (`fiberFamily_URLim`).
* **§5 the genre bank** `patternBank m`: the finite, `O`-independent `Finset` of primary
  patterns of mass `m`; every monic degree-`m` residual's pattern lands in it.
* **§6 the pattern-cell partition**: the loop image's stratum label is `(X + Cγ)^m`
  (IFCG3), so its pattern is `{(1, m)}` — the loop is CONFINED to the deep-linear cell;
  the cells partition `nonloopDecidedSet` exactly, and every non-deep cell count is the
  fiber sum of `stratDecCount`.
* **§7 ★★ THE REDUCTION**: `rationalNonloopCensusAt_of_kernels` fires IFCG16's per-genre
  census from the two kernels (bank = non-deep patterns + the deep genre; children lists
  empty — the census's own smaller-laws input rationalizes all children), hence
  `decidedSliceAt_all_of_singlePoint : SinglePointAggregateLaw → DeepLinearClusterLaw →
  ∀ n, DecidedSliceAt n`.

## ⚠ Scoping disposition

★★★ `decidedSliceAt_all` is **NOT declared**.  The two kernels are genuinely open:
discharging `SinglePointAggregateLaw` at a block `(δ, [e])` with `δ ≥ 2` needs the
unramified base-change recentering (density over the degree-`δ` unramified extension read
at `q^δ`), which no landed theorem exports; at `e ≥ 2` it needs the fractional-slope
stratum censuses (the deep OM cones); even at `e = 1` it needs Gauss's count of monic
irreducibles (known math, not landed).  `DeepLinearClusterLaw` is the loop-corrected
fractional-slope remainder at the maximal-depth linear point — IFCG3's loop bijection
covers exactly the INTEGER-slope self-call that is already subtracted, not the cell that
remains.  The reduction here is honest: both kernels are stated conditionally on the
smaller value laws, so neither is stronger than the remainder they refine (IFCG16 §3's
audit pattern).

## Axiom fence

Lean core everywhere (`propext`, `Classical.choice`, `Quot.sound`); the C.33 cite does
not occur.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.overlappingInstances false

noncomputable section

namespace Uniformity.Density.IFCG18

open IsLocalRing Polynomial
open Uniformity.Density.Induction
open Uniformity.Density.IFCG17
open Uniformity.Density.IFCG15 (nonloopDecidedSet loopClassN LoopParamsN)
open Uniformity.Density.IFCG14 (DecidedValueLaw Witnessed)

attribute [local instance] Classical.propDecidable

/-! ## §0 — counting bridges (local copies of IFCG17's private helpers) -/

section Bridges

private theorem natCard_set_eq_card_filter {α : Type*} [Fintype α] (s : Set α) :
    Nat.card s = (Finset.univ.filter (fun a => a ∈ s)).card := by
  rw [Nat.card_coe_set_eq, ← Set.ncard_coe_finset (Finset.univ.filter (fun a => a ∈ s))]
  congr 1
  ext a
  simp

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

/-- Pointwise evaluation of `TypeAlg` finset sums (IFCG17's private helper, re-proved). -/
private theorem typeAlg_sum_apply {ι : Type*} (S : Finset ι) (f : ι → TypeAlg)
    (t : Multiset (ℕ × ℕ)) : (∑ i ∈ S, f i) t = ∑ i ∈ S, f i t := by
  classical
  induction S using Finset.cons_induction with
  | empty => rw [Finset.sum_empty, Finset.sum_empty]; rfl
  | cons a s ha ih => rw [Finset.sum_cons, Finset.sum_cons, ← ih]; rfl

/-- Pointwise evaluation of `TypeAlg` natural scalar multiples. -/
private theorem typeAlg_nsmul_apply (n : ℕ) (X : TypeAlg) (t : Multiset (ℕ × ℕ)) :
    (n • X) t = (n : ℚ) * X t := by
  induction n with
  | zero =>
      rw [zero_smul, Nat.cast_zero, zero_mul]
      rfl
  | succ k ih =>
      rw [succ_nsmul]
      have happ : ((k • X + X : TypeAlg)) t = (k • X) t + X t := rfl
      rw [happ, ih, Nat.cast_succ]
      ring

end Bridges

/-! ## §1 — the labelled/unlabelled exchange -/

section Exchange

/-- **The labelling multiplicity** of a primary pattern: the number of ordered distinct
tuples realizing one unlabelled polynomial — `∏_{(δ,e)} (count (δ,e))!`. -/
def multPattern (π : Multiset (ℕ × ℕ)) : ℕ :=
  ∏ x ∈ π.toFinset, (π.count x).factorial

@[simp] theorem multPattern_zero : multPattern 0 = 1 := by
  simp [multPattern]

theorem multPattern_pos (π : Multiset (ℕ × ℕ)) : 0 < multPattern π :=
  Finset.prod_pos fun x _ => Nat.factorial_pos _

/-- The cons law of the multiplicity: one fresh `(δ,e)` block multiplies by the new count. -/
theorem multPattern_cons (x : ℕ × ℕ) (π : Multiset (ℕ × ℕ)) :
    multPattern (x ::ₘ π) = (π.count x + 1) * multPattern π := by
  classical
  rw [multPattern, multPattern, Multiset.toFinset_cons]
  by_cases hx : x ∈ π.toFinset
  · have hL : ∏ y ∈ π.toFinset, ((x ::ₘ π).count y).factorial
        = ((x ::ₘ π).count x).factorial
            * ∏ y ∈ π.toFinset.erase x, ((x ::ₘ π).count y).factorial :=
      (Finset.mul_prod_erase _ (fun y => ((x ::ₘ π).count y).factorial) hx).symm
    have hR : ∏ y ∈ π.toFinset, (π.count y).factorial
        = (π.count x).factorial * ∏ y ∈ π.toFinset.erase x, (π.count y).factorial :=
      (Finset.mul_prod_erase _ (fun y => (π.count y).factorial) hx).symm
    have hprod : ∏ y ∈ π.toFinset.erase x, ((x ::ₘ π).count y).factorial
        = ∏ y ∈ π.toFinset.erase x, (π.count y).factorial :=
      Finset.prod_congr rfl fun y hy => by
        rw [Multiset.count_cons_of_ne (Finset.ne_of_mem_erase hy)]
    rw [Finset.insert_eq_self.2 hx, hL, hR, hprod, Multiset.count_cons_self,
      Nat.factorial_succ, mul_assoc]
  · have hcnt : π.count x = 0 :=
      Multiset.count_eq_zero.2 (fun hmem => hx (Multiset.mem_toFinset.2 hmem))
    rw [Finset.prod_insert hx, Multiset.count_cons_self, hcnt]
    have hrest : ∀ y ∈ π.toFinset, ((x ::ₘ π).count y).factorial = (π.count y).factorial := by
      intro y hy
      have hyx : y ≠ x := fun hcon => hx (hcon ▸ hy)
      rw [Multiset.count_cons_of_ne hyx]
    rw [Finset.prod_congr rfl hrest]
    norm_num

/-- The simple block system of a degree/exponent listing. -/
def simpleSys {r : ℕ} (D : Fin r → ℕ × ℕ) : Fin r → SBlock :=
  fun i => ⟨(D i).1, [(D i).2]⟩

/-- The pattern of a listing: the multiset of its values. -/
def sysPattern {r : ℕ} (D : Fin r → ℕ × ℕ) : Multiset (ℕ × ℕ) :=
  (List.ofFn D : List (ℕ × ℕ))

/-- The total mass of a listing. -/
def sysMass {r : ℕ} (D : Fin r → ℕ × ℕ) : ℕ :=
  ∑ i, (D i).1 * (D i).2

theorem sysPattern_succ {r : ℕ} (D : Fin (r + 1) → ℕ × ℕ) :
    sysPattern D = D 0 ::ₘ sysPattern (Fin.tail D) := by
  rw [sysPattern, sysPattern, List.ofFn_succ, ← Multiset.cons_coe]
  rfl

theorem sysMass_succ {r : ℕ} (D : Fin (r + 1) → ℕ × ℕ) :
    sysMass D = (D 0).1 * (D 0).2 + sysMass (Fin.tail D) := by
  rw [sysMass, sysMass, Fin.sum_univ_succ]
  rfl

/-- The mass of a listing is the mass of its pattern. -/
theorem sysMass_eq_pattern_mass {r : ℕ} (D : Fin r → ℕ × ℕ) :
    sysMass D = ((sysPattern D).map (fun p => p.1 * p.2)).sum := by
  rw [sysMass, sysPattern, Multiset.map_coe, Multiset.sum_coe, List.map_ofFn,
    List.sum_ofFn]
  rfl

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [IsAdicComplete (maximalIdeal O) O] [Finite (ResidueField O)] [Fintype (ResidueField O)]

/-- The empty aggregate is `1`. -/
theorem VAgg_zero (N : ℕ) (B : Fin 0 → SBlock) (A : Finset (Polynomial (ResidueField O))) :
    VAgg O N B A = 1 := by
  have htup : tupleFinset (ResidueField O) 0 B A
      = {fun i : Fin 0 => (i.elim0 : Polynomial (ResidueField O))} := by
    ext t
    rw [mem_tupleFinset_iff, Finset.mem_singleton]
    constructor
    · intro _
      funext i
      exact i.elim0
    · intro _
      exact ⟨fun i => i.elim0, fun i₁ _ _ => i₁.elim0⟩
  rw [VAgg, htup, Finset.sum_singleton, Finset.univ_eq_empty, Finset.prod_empty]

set_option maxHeartbeats 2000000 in
/-- ★ **THE LABELLED/UNLABELLED EXCHANGE** (the stub's §6b): on a simple block system the
distinct-tuple aggregate is the labelling multiplicity times the pattern fiber's census
sum.  Induction through `tuple_sum_succ`, the coprime `stratPoly_mul` at the fresh head
point, and §5b's double count `sum_sigma_fiber_eq`. -/
theorem VAgg_eq_fiber {N : ℕ} (hN : 1 ≤ N) :
    ∀ {r : ℕ} (D : Fin r → ℕ × ℕ), (∀ i, 1 ≤ (D i).1) → (∀ i, 1 ≤ (D i).2) →
      ∀ A : Finset (Polynomial (ResidueField O)), (∀ q ∈ A, q.Monic ∧ Irreducible q) →
      VAgg O N (simpleSys D) A
        = multPattern (sysPattern D)
            • ∑ g ∈ fiberFinset (ResidueField O) (sysMass D) (sysPattern D) A,
                stratPoly O (sysMass D) N g := by
  intro r
  induction r with
  | zero =>
      intro D hδ he A hA
      have hpat : sysPattern D = 0 := by
        rw [sysPattern, List.ofFn_zero]
        rfl
      have hmass : sysMass D = 0 := by
        simp [sysMass]
      rw [VAgg_zero, hpat, hmass, multPattern_zero,
        fiberFinset_zero A (fun q hq => (hA q hq).2), Finset.sum_singleton,
        stratPoly_zero_one, one_smul]
  | succ r ih =>
      intro D hδ he A hA
      have hsys : simpleSys D
          = Fin.cons (⟨(D 0).1, [(D 0).2]⟩ : SBlock) (simpleSys (Fin.tail D)) := by
        funext i
        refine Fin.cases rfl (fun j => rfl) i
      -- STEP 1: the head peel + product collapse
      have h1 : VAgg O N (simpleSys D) A
          = ∑ p₀ ∈ irredFinset (ResidueField O) (D 0).1 \ A,
              stratPoly O ((D 0).1 * (D 0).2) N (p₀ ^ (D 0).2)
                * VAgg O N (simpleSys (Fin.tail D)) (insert p₀ A) := by
        rw [hsys, VAgg, tuple_sum_succ]
        refine Finset.sum_congr rfl fun p₀ _ => ?_
        rw [VAgg, Finset.mul_sum]
        refine Finset.sum_congr rfl fun t' _ => ?_
        rw [Fin.prod_univ_succ]
        simp only [Fin.cons_zero, Fin.cons_succ]
        congr 1
        exact blockPoly_singleton N (D 0).1 p₀ (D 0).2
      -- STEP 2: the tail IH per head point, then the coprime product law
      have h2 : ∀ p₀ ∈ irredFinset (ResidueField O) (D 0).1 \ A,
          stratPoly O ((D 0).1 * (D 0).2) N (p₀ ^ (D 0).2)
              * VAgg O N (simpleSys (Fin.tail D)) (insert p₀ A)
            = multPattern (sysPattern (Fin.tail D)) •
                ∑ g' ∈ fiberFinset (ResidueField O) (sysMass (Fin.tail D))
                    (sysPattern (Fin.tail D)) (insert p₀ A),
                  stratPoly O ((D 0).1 * (D 0).2 + sysMass (Fin.tail D)) N
                    (p₀ ^ (D 0).2 * g') := by
        intro p₀ hp₀
        obtain ⟨hp₀i, hp₀A⟩ := Finset.mem_sdiff.1 hp₀
        obtain ⟨hp₀m, hp₀d, hp₀irr⟩ := mem_irredFinset_iff.1 hp₀i
        have hA' : ∀ q ∈ insert p₀ A, q.Monic ∧ Irreducible q := by
          intro q hq
          rcases Finset.mem_insert.1 hq with rfl | hqA
          · exact ⟨hp₀m, hp₀irr⟩
          · exact hA q hqA
        rw [ih (Fin.tail D) (fun i => hδ i.succ) (fun i => he i.succ) (insert p₀ A) hA',
          mul_smul_comm, Finset.mul_sum]
        refine congrArg (fun z => multPattern (sysPattern (Fin.tail D)) • z) ?_
        refine Finset.sum_congr rfl fun g' hg' => ?_
        obtain ⟨⟨hg'm, hg'd⟩, -, hg'avoid⟩ := mem_fiberFinset_iff.1 hg'
        have hnd : ¬ p₀ ∣ g' := hg'avoid p₀ (Finset.mem_insert_self _ _)
        have hcop : IsCoprime (p₀ ^ (D 0).2) g' :=
          (hp₀irr.coprime_iff_not_dvd.2 hnd).pow_left
        rw [← stratPoly_mul hN (hp₀m.pow _) hg'm
          (by rw [Polynomial.natDegree_pow, hp₀d, Nat.mul_comm]) hg'd hcop]
      -- STEP 3: swap the scalar out and fire the double count
      rw [h1, Finset.sum_congr rfl h2, ← Finset.smul_sum,
        sum_sigma_fiber_eq (hδ 0) (he 0) (sysMass (Fin.tail D)) (sysPattern (Fin.tail D))
          A hA (stratPoly O ((D 0).1 * (D 0).2 + sysMass (Fin.tail D)) N),
        smul_smul, sysPattern_succ, sysMass_succ, multPattern_cons, Prod.mk.eta,
        Nat.mul_comm (multPattern (sysPattern (Fin.tail D)))]

end Exchange

/-! ## §2 — the uniform-rational-limit calculus (the stub's `URseq` closure) -/

section URLim

/-- **A uniform rational limit family**: a real sequence for every complete DVR with
finite residue field, converging — at EVERY such DVR — to the value of ONE rational
function of the residue cardinality (one `Polynomial ℚ` pair chosen before the DVR, with
both denominator obligations). -/
def URLim (F : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [IsAdicComplete (maximalIdeal O) O] [Finite (ResidueField O)], ℕ → ℝ) : Prop :=
  ∃ n d : Polynomial ℚ, d ≠ 0 ∧
    ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
      [IsAdicComplete (maximalIdeal O) O] [Finite (ResidueField O)],
      d.eval ((residueCard O : ℕ) : ℚ) ≠ 0 ∧
        Filter.Tendsto (F O) Filter.atTop
          (nhds ((n.eval ((residueCard O : ℕ) : ℚ)
            / d.eval ((residueCard O : ℕ) : ℚ) : ℚ) : ℝ))

theorem URLim_const (c : ℚ) :
    URLim (fun _ _ _ _ _ _ _ => (c : ℝ)) := by
  refine ⟨Polynomial.C c, 1, one_ne_zero, ?_⟩
  intro O _ _ _ _ _
  refine ⟨by simp, ?_⟩
  have hval : ((Polynomial.C c).eval ((residueCard O : ℕ) : ℚ)
      / (1 : Polynomial ℚ).eval ((residueCard O : ℕ) : ℚ) : ℚ) = c := by
    simp
  rw [hval]
  exact tendsto_const_nhds

/-- `URLim` transfers along families that agree at all levels `≥ 1`. -/
theorem URLim.congr
    {F G : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
      [IsAdicComplete (maximalIdeal O) O] [Finite (ResidueField O)], ℕ → ℝ}
    (h : URLim F)
    (hFG : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
      [IsAdicComplete (maximalIdeal O) O] [Finite (ResidueField O)],
      ∀ N, 1 ≤ N → F O N = G O N) : URLim G := by
  obtain ⟨n, d, hd, hval⟩ := h
  refine ⟨n, d, hd, ?_⟩
  intro O _ _ _ _ _
  obtain ⟨hne, hlim⟩ := hval O
  refine ⟨hne, ?_⟩
  refine hlim.congr' ?_
  filter_upwards [Filter.eventually_ge_atTop 1] with N hN1
  exact hFG O N hN1

theorem URLim.add
    {F G : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
      [IsAdicComplete (maximalIdeal O) O] [Finite (ResidueField O)], ℕ → ℝ}
    (hF : URLim F) (hG : URLim G) :
    URLim (fun O _ _ _ _ _ N => F O N + G O N) := by
  obtain ⟨n₁, d₁, hd₁, hval₁⟩ := hF
  obtain ⟨n₂, d₂, hd₂, hval₂⟩ := hG
  refine ⟨n₁ * d₂ + d₁ * n₂, d₁ * d₂, mul_ne_zero hd₁ hd₂, ?_⟩
  intro O _ _ _ _ _
  obtain ⟨hne₁, hlim₁⟩ := hval₁ O
  obtain ⟨hne₂, hlim₂⟩ := hval₂ O
  refine ⟨by rw [Polynomial.eval_mul]; exact mul_ne_zero hne₁ hne₂, ?_⟩
  have hq : (n₁.eval ((residueCard O : ℕ) : ℚ) / d₁.eval ((residueCard O : ℕ) : ℚ)
        + n₂.eval ((residueCard O : ℕ) : ℚ) / d₂.eval ((residueCard O : ℕ) : ℚ) : ℚ)
      = ((n₁ * d₂ + d₁ * n₂).eval ((residueCard O : ℕ) : ℚ)
          / (d₁ * d₂).eval ((residueCard O : ℕ) : ℚ) : ℚ) := by
    rw [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_mul, Polynomial.eval_mul,
      div_add_div _ _ hne₁ hne₂]
  have hlim := hlim₁.add hlim₂
  rw [← Rat.cast_add, hq] at hlim
  exact hlim

theorem URLim.mul
    {F G : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
      [IsAdicComplete (maximalIdeal O) O] [Finite (ResidueField O)], ℕ → ℝ}
    (hF : URLim F) (hG : URLim G) :
    URLim (fun O _ _ _ _ _ N => F O N * G O N) := by
  obtain ⟨n₁, d₁, hd₁, hval₁⟩ := hF
  obtain ⟨n₂, d₂, hd₂, hval₂⟩ := hG
  refine ⟨n₁ * n₂, d₁ * d₂, mul_ne_zero hd₁ hd₂, ?_⟩
  intro O _ _ _ _ _
  obtain ⟨hne₁, hlim₁⟩ := hval₁ O
  obtain ⟨hne₂, hlim₂⟩ := hval₂ O
  refine ⟨by rw [Polynomial.eval_mul]; exact mul_ne_zero hne₁ hne₂, ?_⟩
  have hq : (n₁.eval ((residueCard O : ℕ) : ℚ) / d₁.eval ((residueCard O : ℕ) : ℚ)
        * (n₂.eval ((residueCard O : ℕ) : ℚ) / d₂.eval ((residueCard O : ℕ) : ℚ)) : ℚ)
      = ((n₁ * n₂).eval ((residueCard O : ℕ) : ℚ)
          / (d₁ * d₂).eval ((residueCard O : ℕ) : ℚ) : ℚ) := by
    rw [Polynomial.eval_mul, Polynomial.eval_mul, div_mul_div_comm]
  have hlim := hlim₁.mul hlim₂
  rw [← Rat.cast_mul, hq] at hlim
  exact hlim

theorem URLim.sub
    {F G : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
      [IsAdicComplete (maximalIdeal O) O] [Finite (ResidueField O)], ℕ → ℝ}
    (hF : URLim F) (hG : URLim G) :
    URLim (fun O _ _ _ _ _ N => F O N - G O N) := by
  obtain ⟨n₁, d₁, hd₁, hval₁⟩ := hF
  obtain ⟨n₂, d₂, hd₂, hval₂⟩ := hG
  refine ⟨n₁ * d₂ - d₁ * n₂, d₁ * d₂, mul_ne_zero hd₁ hd₂, ?_⟩
  intro O _ _ _ _ _
  obtain ⟨hne₁, hlim₁⟩ := hval₁ O
  obtain ⟨hne₂, hlim₂⟩ := hval₂ O
  refine ⟨by rw [Polynomial.eval_mul]; exact mul_ne_zero hne₁ hne₂, ?_⟩
  have hq : (n₁.eval ((residueCard O : ℕ) : ℚ) / d₁.eval ((residueCard O : ℕ) : ℚ)
        - n₂.eval ((residueCard O : ℕ) : ℚ) / d₂.eval ((residueCard O : ℕ) : ℚ) : ℚ)
      = ((n₁ * d₂ - d₁ * n₂).eval ((residueCard O : ℕ) : ℚ)
          / (d₁ * d₂).eval ((residueCard O : ℕ) : ℚ) : ℚ) := by
    rw [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_mul, Polynomial.eval_mul,
      div_sub_div _ _ hne₁ hne₂]
  have hlim := hlim₁.sub hlim₂
  rw [← Rat.cast_sub, hq] at hlim
  exact hlim

theorem URLim_sum {ι : Type*} (s : Finset ι)
    (F : ι → ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
      [IsAdicComplete (maximalIdeal O) O] [Finite (ResidueField O)], ℕ → ℝ)
    (h : ∀ i ∈ s, URLim (F i)) :
    URLim (fun O _ _ _ _ _ N => ∑ i ∈ s, F i O N) := by
  classical
  induction s using Finset.cons_induction with
  | empty =>
      refine (URLim_const 0).congr ?_
      intro O _ _ _ _ _ N _
      simp
  | cons a s ha ih =>
      refine ((h a (Finset.mem_cons_self a s)).add
        (ih (fun i hi => h i (Finset.mem_cons_of_mem hi)))).congr ?_
      intro O _ _ _ _ _ N _
      rw [Finset.sum_cons]

end URLim

/-! ## §3 — ★ THE NAMED KERNELS (the campaign's last statements) -/

section Kernels

/-- The normalized single-point aggregate family of a super-block: the `s`-coefficient of
`SPAgg` over the FULL point range (empty avoidance), normalized at the block's mass. -/
def spFamily (b : SBlock) (s : Multiset (ℕ × ℕ)) :
    ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
      [IsAdicComplete (maximalIdeal O) O] [Finite (ResidueField O)], ℕ → ℝ :=
  fun O _ _ _ _ _ N =>
    letI : Fintype (ResidueField O) := Fintype.ofFinite _
    ((SPAgg O N b ∅ : TypeAlg) s : ℝ) / (residueCard O : ℝ) ^ (b.mass * N)

/-- The normalized distinct-tuple aggregate family of a block system (empty avoidance),
normalized at the system's total mass. -/
def vaggFamily {r : ℕ} (B : Fin r → SBlock) (s : Multiset (ℕ × ℕ)) :
    ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
      [IsAdicComplete (maximalIdeal O) O] [Finite (ResidueField O)], ℕ → ℝ :=
  fun O _ _ _ _ _ N =>
    letI : Fintype (ResidueField O) := Fintype.ofFinite _
    ((VAgg O N B ∅ : TypeAlg) s : ℝ) / (residueCard O : ℝ) ^ ((∑ i, (B i).mass) * N)

/-- The normalized pattern-fiber census family at a fixed label `σ`. -/
def fiberFamily (m : ℕ) (σ : FactorizationType) (t : Multiset (ℕ × ℕ)) :
    ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
      [IsAdicComplete (maximalIdeal O) O] [Finite (ResidueField O)], ℕ → ℝ :=
  fun O _ _ _ _ _ N =>
    letI : Fintype (ResidueField O) := Fintype.ofFinite _
    ((∑ f ∈ fiberFinset (ResidueField O) m t ∅, stratDecCount O m σ N f : ℕ) : ℝ)
      / (residueCard O : ℝ) ^ (m * N)

/-- ★ **THE SINGLE-POINT FRACTIONAL-SLOPE KERNEL — the campaign's LAST named statement.**

For every mass window `m ≥ 4`, GIVEN the decided value laws at all degrees `< m` (the
census's own conditionality — this law is NOT stronger than the remainder it refines):
for every super-block `b = (δ, E)` — a single residual point of degree `δ ≥ 1` carrying
finitely many exponent constraints `E ≠ []`, all `≥ 1`, of total mass `δ·ΣE ≤ m` —
EXCLUDING the pure deep-linear block `(δ, E) = (1, [m])` (whose raw aggregate contains
the full degree-`m` self-call; it enters only loop-corrected, as
`DeepLinearClusterLaw`), and for every type-data coefficient `s`: the normalized
aggregate

    `N ↦ (Σ_{p monic irreducible, deg p = δ} Π_{e ∈ E} #dec_⟨·⟩(strat(p^e)))_s / q^(δ·ΣE·N)`

is ONE rational function of `q = #(residue field)` in the limit `N → ∞`, uniformly over
every complete DVR with finite residue field (one `Polynomial ℚ` pair, both denominator
obligations).  The open mathematical content: the Gauss point count at `e = 1`, the
unramified base change at `δ ≥ 2`, and the fractional-slope (deep Okutsu–Montes cone)
censuses at `e ≥ 2`. -/
def SinglePointAggregateLaw : Prop :=
  ∀ m : ℕ, 4 ≤ m →
    (∀ k, k < m → ∀ σ' : FactorizationType, σ'.degree = k → DecidedValueLaw k σ') →
    ∀ b : SBlock, 1 ≤ b.δ → b.E ≠ [] → (∀ e ∈ b.E, 1 ≤ e) → b.mass ≤ m →
      ¬(b.δ = 1 ∧ b.E = [m]) →
      ∀ s : Multiset (ℕ × ℕ), URLim (spFamily b s)

/-- The pattern cell of the non-loop decided set: the classes whose level-0 stratum label
has primary pattern `t`. -/
def pcellCount (O : Type*) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Finite (ResidueField O)] (π : O) (m : ℕ) (σ : FactorizationType) (M : ℕ)
    (t : Multiset (ℕ × ℕ)) : ℕ :=
  Nat.card ((nonloopDecidedSet π m σ M
    ∩ {c | patternOf (stratumPoly O m (M + m) c) = t} : Set (Coeff O m (M + m))))

/-- ★ **THE DEEP-LINEAR CLUSTER KERNEL** — the second and last named remainder: the
loop-corrected `{(1, m)}` (maximal-depth linear point) pattern cell of the non-loop
decided set has ONE uniform rational limit, given the smaller value laws.  This is the
fractional-slope content of the deep linear cluster: IFCG15's loop subtraction has
already removed the integer-slope self-call `q^{-(T_m-1)}·(density at level M)`. -/
def DeepLinearClusterLaw : Prop :=
  ∀ m : ℕ, 4 ≤ m →
    (∀ k, k < m → ∀ σ' : FactorizationType, σ'.degree = k → DecidedValueLaw k σ') →
    ∀ σ : FactorizationType, σ.degree = m → Witnessed m σ →
      ∃ n d : Polynomial ℚ, d ≠ 0 ∧
        ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
          [IsAdicComplete (maximalIdeal O) O] [Finite (ResidueField O)],
          d.eval ((residueCard O : ℕ) : ℚ) ≠ 0 ∧
            ∀ π : O, Irreducible π →
              Filter.Tendsto
                (fun M => (pcellCount O π m σ M {(1, m)} : ℝ)
                  / (residueCard O : ℝ) ^ (m * (M + m)))
                Filter.atTop
                (nhds ((n.eval ((residueCard O : ℕ) : ℚ)
                  / d.eval ((residueCard O : ℕ) : ℚ) : ℚ) : ℝ))

end Kernels

/-! ## §4 — the limit propagation through the peel (the stub's `V_tendsto`) -/

section Propagation

/-- Mass accounting of one merge: appending the head's exponents into the `j`-th block
adds exactly the head's mass to the system total (the degrees match on the collision). -/
private theorem sum_mass_update {r : ℕ} (C : Fin r → SBlock) (j : Fin r) (b : SBlock)
    (hδ : (C j).δ = b.δ) :
    (∑ i, ((Function.update C j ⟨(C j).δ, (C j).E ++ b.E⟩ : Fin r → SBlock) i).mass)
      = (∑ i, (C i).mass) + b.mass := by
  classical
  have hcomp : (fun i =>
        ((Function.update C j ⟨(C j).δ, (C j).E ++ b.E⟩ : Fin r → SBlock) i).mass)
      = Function.update (fun i => (C i).mass) j ((C j).δ * ((C j).E ++ b.E).sum) := by
    funext i
    by_cases hij : i = j
    · subst hij
      rw [Function.update_self, Function.update_self]
      rfl
    · rw [Function.update_of_ne hij, Function.update_of_ne hij]
  calc (∑ i, ((Function.update C j ⟨(C j).δ, (C j).E ++ b.E⟩ : Fin r → SBlock) i).mass)
      = ∑ i, Function.update (fun i => (C i).mass) j ((C j).δ * ((C j).E ++ b.E).sum) i := by
        rw [hcomp]
    _ = (C j).δ * ((C j).E ++ b.E).sum + ∑ i ∈ Finset.univ.erase j, (C i).mass := by
        rw [Finset.sum_update_of_mem (Finset.mem_univ j),
          Finset.sdiff_singleton_eq_erase]
    _ = ((C j).δ * (C j).E.sum + b.δ * b.E.sum) + ∑ i ∈ Finset.univ.erase j, (C i).mass := by
        rw [List.sum_append, Nat.mul_add, hδ]
    _ = (∑ i, (C i).mass) + b.mass := by
        rw [add_right_comm ((C j).δ * (C j).E.sum) (b.δ * b.E.sum)
            (∑ i ∈ Finset.univ.erase j, (C i).mass)]
        rw [show (C j).δ * (C j).E.sum = (C j).mass from rfl]
        rw [Finset.add_sum_erase Finset.univ (fun i => (C i).mass) (Finset.mem_univ j)]
        rfl

/-- **The peel propagation**: given the single-point kernel, every admissible block
system's aggregate family is a uniform rational limit — induction on the number of
blocks through the exact collision peel `VAgg_cons_eq`, the convolution
`mul_apply_powerset`, and the `URLim` closure calculus. -/
theorem vaggFamily_URLim (hSP : SinglePointAggregateLaw) {m : ℕ} (hm : 4 ≤ m)
    (hsm : ∀ k, k < m → ∀ σ' : FactorizationType, σ'.degree = k → DecidedValueLaw k σ') :
    ∀ (r : ℕ) (B : Fin r → SBlock),
      (∀ i, 1 ≤ (B i).δ ∧ (B i).E ≠ [] ∧ ∀ e ∈ (B i).E, 1 ≤ e) →
      (∀ i, ¬((B i).δ = 1 ∧ (B i).E = [m])) →
      (∑ i, (B i).mass) ≤ m →
      ∀ s : Multiset (ℕ × ℕ), URLim (vaggFamily B s) := by
  intro r
  induction r with
  | zero =>
      intro B hblk hdeep hmass s
      refine (URLim_const ((1 : TypeAlg) s)).congr ?_
      intro O _ _ _ _ _ N _
      letI : Fintype (ResidueField O) := Fintype.ofFinite (ResidueField O)
      unfold vaggFamily
      have hzero : (∑ i, (B i).mass) = 0 := by simp
      rw [VAgg_zero, hzero, Nat.zero_mul, pow_zero, div_one]
  | succ r ih =>
      intro B hblk hdeep hmass s
      -- head and tail admissibility
      have hb0 := hblk 0
      have hb0mass : (B 0).mass ≤ m :=
        le_trans (Finset.single_le_sum (f := fun i => (B i).mass)
          (fun i _ => Nat.zero_le _) (Finset.mem_univ 0)) hmass
      have htail_blk : ∀ i, 1 ≤ ((Fin.tail B) i).δ ∧ ((Fin.tail B) i).E ≠ []
          ∧ ∀ e ∈ ((Fin.tail B) i).E, 1 ≤ e := fun i => hblk i.succ
      have htail_deep : ∀ i, ¬(((Fin.tail B) i).δ = 1 ∧ ((Fin.tail B) i).E = [m]) :=
        fun i => hdeep i.succ
      have hsum_succ : (∑ i, (B i).mass) = (B 0).mass + ∑ i, ((Fin.tail B) i).mass := by
        rw [Fin.sum_univ_succ]
        rfl
      have htail_mass : (∑ i, ((Fin.tail B) i).mass) ≤ m := by omega
      -- the convolution part is URLim
      have hconv : URLim (fun O _ _ _ _ _ N => ∑ s' ∈ s.powerset.toFinset,
          spFamily (B 0) s' O N * vaggFamily (Fin.tail B) (s - s') O N) := by
        refine URLim_sum _ _ (fun s' _ => ?_)
        exact (hSP m hm hsm (B 0) hb0.1 hb0.2.1 hb0.2.2 hb0mass (hdeep 0) s').mul
          (ih (Fin.tail B) htail_blk htail_deep htail_mass (s - s'))
      -- the merge corrections are URLim
      have hmerge : URLim (fun O _ _ _ _ _ N =>
          ∑ j ∈ Finset.univ.filter (fun j : Fin r => ((Fin.tail B) j).δ = (B 0).δ),
            vaggFamily (Function.update (Fin.tail B) j
              ⟨((Fin.tail B) j).δ, ((Fin.tail B) j).E ++ (B 0).E⟩) s O N) := by
        refine URLim_sum _ _ (fun j hj => ?_)
        have hδj : ((Fin.tail B) j).δ = (B 0).δ := (Finset.mem_filter.1 hj).2
        refine ih _ ?_ ?_ ?_ s
        · intro i
          by_cases hij : i = j
          · subst hij
            rw [Function.update_self]
            refine ⟨(htail_blk i).1, ?_, ?_⟩
            · intro hcon
              exact (htail_blk i).2.1 (List.append_eq_nil_iff.1 hcon).1
            · intro e he
              rcases List.mem_append.1 he with h | h
              · exact (htail_blk i).2.2 e h
              · exact hb0.2.2 e h
          · rw [Function.update_of_ne hij]
            exact htail_blk i
        · intro i
          by_cases hij : i = j
          · subst hij
            rw [Function.update_self]
            rintro ⟨-, hE⟩
            have hlen := congrArg List.length hE
            rw [List.length_append] at hlen
            have h₁ : ((Fin.tail B) i).E.length ≠ 0 := fun h =>
              (htail_blk i).2.1 (List.length_eq_zero_iff.1 h)
            have h₂ : (B 0).E.length ≠ 0 := fun h =>
              hb0.2.1 (List.length_eq_zero_iff.1 h)
            simp only [List.length_cons, List.length_nil] at hlen
            omega
          · rw [Function.update_of_ne hij]
            exact htail_deep i
        · rw [sum_mass_update (Fin.tail B) j (B 0) hδj]
          omega
      -- combine and transfer along the exact collision peel
      refine (hconv.sub hmerge).congr ?_
      intro O _ _ _ _ _ N _
      letI : Fintype (ResidueField O) := Fintype.ofFinite (ResidueField O)
      -- the ℚ-level peel at coefficient s
      have hpeel := VAgg_cons_eq (O := O) N (B 0) (Fin.tail B)
        (∅ : Finset (Polynomial (ResidueField O)))
      rw [Fin.cons_self_tail] at hpeel
      have hcoef : (∑ s' ∈ s.powerset.toFinset,
            (SPAgg O N (B 0) ∅) s' * (VAgg O N (Fin.tail B) ∅) (s - s'))
          = (VAgg O N B ∅) s
            + ∑ j ∈ Finset.univ.filter (fun j : Fin r => ((Fin.tail B) j).δ = (B 0).δ),
              (VAgg O N (Function.update (Fin.tail B) j
                ⟨((Fin.tail B) j).δ, ((Fin.tail B) j).E ++ (B 0).E⟩) ∅) s := by
        rw [← typeAlg_sum_apply, ← mul_apply_powerset, hpeel]
        rfl
      -- unfold the families and align the normalizations
      unfold spFamily vaggFamily
      have hEsplit : (∑ i, (B i).mass) * N
          = (B 0).mass * N + (∑ i, ((Fin.tail B) i).mass) * N := by
        rw [hsum_succ, Nat.add_mul]
      have hconvterm : ∀ s' ∈ s.powerset.toFinset,
          ((SPAgg O N (B 0) ∅) s' : ℝ) / (residueCard O : ℝ) ^ ((B 0).mass * N)
              * (((VAgg O N (Fin.tail B) ∅) (s - s') : ℝ)
                / (residueCard O : ℝ) ^ ((∑ i, ((Fin.tail B) i).mass) * N))
            = (((SPAgg O N (B 0) ∅) s' * (VAgg O N (Fin.tail B) ∅) (s - s') : ℚ) : ℝ)
                / (residueCard O : ℝ) ^ ((∑ i, (B i).mass) * N) := by
        intro s' _
        rw [div_mul_div_comm, ← pow_add, ← hEsplit]
        push_cast
        rfl
      have hmergeterm : ∀ j ∈ Finset.univ.filter
            (fun j : Fin r => ((Fin.tail B) j).δ = (B 0).δ),
          ((VAgg O N (Function.update (Fin.tail B) j
                ⟨((Fin.tail B) j).δ, ((Fin.tail B) j).E ++ (B 0).E⟩) ∅) s : ℝ)
              / (residueCard O : ℝ)
                ^ ((∑ i, ((Function.update (Fin.tail B) j
                    ⟨((Fin.tail B) j).δ, ((Fin.tail B) j).E ++ (B 0).E⟩
                    : Fin r → SBlock) i).mass) * N)
            = ((VAgg O N (Function.update (Fin.tail B) j
                ⟨((Fin.tail B) j).δ, ((Fin.tail B) j).E ++ (B 0).E⟩) ∅) s : ℝ)
                / (residueCard O : ℝ) ^ ((∑ i, (B i).mass) * N) := by
        intro j hj
        have hδj : ((Fin.tail B) j).δ = (B 0).δ := (Finset.mem_filter.1 hj).2
        have hexp : (∑ i, ((Function.update (Fin.tail B) j
              ⟨((Fin.tail B) j).δ, ((Fin.tail B) j).E ++ (B 0).E⟩
              : Fin r → SBlock) i).mass) = ∑ i, (B i).mass := by
          rw [sum_mass_update (Fin.tail B) j (B 0) hδj]
          omega
        rw [hexp]
      rw [Finset.sum_congr rfl hconvterm, Finset.sum_congr rfl hmergeterm,
        ← Finset.sum_div, ← Finset.sum_div, div_sub_div_same]
      congr 1
      have hcoefR : (∑ s' ∈ s.powerset.toFinset,
            (((SPAgg O N (B 0) ∅) s' * (VAgg O N (Fin.tail B) ∅) (s - s') : ℚ) : ℝ))
          = ((VAgg O N B ∅) s : ℝ)
            + ∑ j ∈ Finset.univ.filter (fun j : Fin r => ((Fin.tail B) j).δ = (B 0).δ),
              ((VAgg O N (Function.update (Fin.tail B) j
                ⟨((Fin.tail B) j).δ, ((Fin.tail B) j).E ++ (B 0).E⟩) ∅) s : ℝ) := by
        exact_mod_cast congrArg (fun x : ℚ => (x : ℝ)) hcoef
      linarith [hcoefR]

end Propagation

/-! ## §5 — the genre bank -/

section Bank

open UniqueFactorizationMonoid

/-- **The genre bank at mass `m`**: the finite, `O`-independent `Finset` of primary
patterns (multisets of `(δ, e)` pairs, all entries positive) of total mass `m`. -/
def patternBank (m : ℕ) : Finset (Multiset (ℕ × ℕ)) :=
  ((m • ((Finset.range (m + 1)) ×ˢ (Finset.range (m + 1))).val).powerset.toFinset).filter
    (fun π => (π.map (fun p => p.1 * p.2)).sum = m ∧ ∀ p ∈ π, 1 ≤ p.1 ∧ 1 ≤ p.2)

theorem mem_patternBank_iff {m : ℕ} {π : Multiset (ℕ × ℕ)} :
    π ∈ patternBank m
      ↔ (π.map (fun p => p.1 * p.2)).sum = m ∧ ∀ p ∈ π, 1 ≤ p.1 ∧ 1 ≤ p.2 := by
  rw [patternBank, Finset.mem_filter]
  constructor
  · rintro ⟨-, h⟩
    exact h
  · intro h
    refine ⟨?_, h⟩
    rw [Multiset.mem_toFinset, Multiset.mem_powerset, Multiset.le_iff_count]
    intro x
    by_cases hx : x ∈ π
    · have hxpos := h.2 x hx
      have hle : x.1 * x.2 ≤ m := by
        rw [← h.1]
        exact Multiset.single_le_sum (fun y _ => Nat.zero_le y) _
          (Multiset.mem_map_of_mem _ hx)
      have hx1 : x.1 ≤ x.1 * x.2 := by
        calc x.1 = x.1 * 1 := (Nat.mul_one _).symm
          _ ≤ x.1 * x.2 := Nat.mul_le_mul_left _ hxpos.2
      have hx2 : x.2 ≤ x.1 * x.2 := by
        calc x.2 = 1 * x.2 := (Nat.one_mul _).symm
          _ ≤ x.1 * x.2 := Nat.mul_le_mul_right _ hxpos.1
      have hxS : x ∈ (Finset.range (m + 1)) ×ˢ (Finset.range (m + 1)) := by
        rw [Finset.mem_product, Finset.mem_range, Finset.mem_range]
        omega
      have hcard : π.card ≤ m := by
        have h2 : (π.map (fun p => p.1 * p.2)).card • 1
            ≤ (π.map (fun p => p.1 * p.2)).sum := by
          refine Multiset.card_nsmul_le_sum fun y hy => ?_
          obtain ⟨p, hp, rfl⟩ := Multiset.mem_map.1 hy
          have := h.2 p hp
          exact Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by omega))
        rw [Multiset.card_map, smul_eq_mul, Nat.mul_one, h.1] at h2
        exact h2
      have hcount1 : ((Finset.range (m + 1)) ×ˢ (Finset.range (m + 1))).val.count x = 1 :=
        Multiset.count_eq_one_of_mem ((Finset.range (m + 1)) ×ˢ (Finset.range (m + 1))).nodup
          (Finset.mem_val.symm ▸ hxS)
      rw [Multiset.count_nsmul, hcount1, Nat.mul_one]
      calc π.count x ≤ π.card := Multiset.count_le_card x π
        _ ≤ m := hcard
    · rw [Multiset.count_eq_zero.2 hx]
      exact Nat.zero_le _

/-- The deep-linear pattern is in the bank at every positive mass. -/
theorem deep_mem_patternBank {m : ℕ} (hm : 1 ≤ m) :
    ({(1, m)} : Multiset (ℕ × ℕ)) ∈ patternBank m := by
  rw [mem_patternBank_iff]
  refine ⟨by simp, ?_⟩
  intro p hp
  rw [Multiset.mem_singleton] at hp
  subst hp
  exact ⟨le_refl 1, hm⟩

/-- The mass of the primary pattern is the degree. -/
theorem patternOf_mass {K : Type*} [Field K] {f : Polynomial K} (hf : f.Monic) :
    ((patternOf f).map (fun p => p.1 * p.2)).sum = f.natDegree := by
  classical
  rw [patternOf, Multiset.map_map]
  have hL : (Multiset.map ((fun p : ℕ × ℕ => p.1 * p.2)
        ∘ fun p => (p.natDegree, (normalizedFactors f).count p))
        (normalizedFactors f).toFinset.val).sum
      = ∑ p ∈ (normalizedFactors f).toFinset,
          p.natDegree * (normalizedFactors f).count p := rfl
  rw [hL]
  conv_rhs => rw [← prod_normalizedFactors_of_monic hf]
  rw [Polynomial.natDegree_multiset_prod _ (zero_notMem_normalizedFactors f),
    Finset.sum_multiset_map_count]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [smul_eq_mul, Nat.mul_comm]

/-- Pattern entries are positive. -/
theorem patternOf_entries_pos {K : Type*} [Field K] {f : Polynomial K} {p : ℕ × ℕ}
    (hp : p ∈ patternOf f) : 1 ≤ p.1 ∧ 1 ≤ p.2 := by
  rw [patternOf] at hp
  obtain ⟨q, hq, rfl⟩ := Multiset.mem_map.1 hp
  have hqmem : q ∈ normalizedFactors f :=
    Multiset.mem_toFinset.1 (Finset.mem_val ▸ hq)
  constructor
  · exact (irreducible_of_normalized_factor q hqmem).natDegree_pos
  · exact Multiset.one_le_count_iff_mem.2 hqmem

/-- Every monic degree-`m` residual's pattern lands in the bank. -/
theorem patternOf_mem_patternBank {K : Type*} [Field K] {m : ℕ} {f : Polynomial K}
    (hf : f.Monic) (hd : f.natDegree = m) : patternOf f ∈ patternBank m := by
  rw [mem_patternBank_iff]
  exact ⟨by rw [patternOf_mass hf, hd], fun p hp => patternOf_entries_pos hp⟩

end Bank

/-! ## §6 — the pattern-cell partition and the loop confinement -/

section Partition

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)]

/-- The primary pattern of `(X + Cγ)^m` is the deep-linear `{(1, m)}`. -/
theorem patternOf_addC_pow {K : Type*} [Field K] (γ : K) {m : ℕ} (hm : 1 ≤ m) :
    patternOf ((X + C γ) ^ m) = ({(1, m)} : Multiset (ℕ × ℕ)) := by
  have hmono : (X + C γ).Monic := Polynomial.monic_X_add_C γ
  have hirr : Irreducible (X + C γ) :=
    Polynomial.irreducible_of_degree_eq_one (Polynomial.degree_X_add_C γ)
  have hnd : ¬ (X + C γ) ∣ (1 : Polynomial K) := fun hdvd =>
    hirr.not_isUnit (isUnit_of_dvd_one hdvd)
  have h1 : (X + C γ) ^ m = (X + C γ) ^ m * 1 := (mul_one _).symm
  rw [h1, patternOf_pow_mul hmono hirr hm one_ne_zero hnd, patternOf_one,
    Polynomial.natDegree_X_add_C]
  rfl

/-- **The loop confinement**: the stratum label of every loop-image class is
`(X + Cγ)^m`, so its pattern is the deep-linear `{(1, m)}` — the loop image never meets a
non-deep pattern cell. -/
theorem patternOf_stratumPoly_loopClassN {π : O} (hπ : Irreducible π)
    {m M : ℕ} (hm : 1 ≤ m) {σ : FactorizationType} (p : LoopParamsN O m σ M) :
    patternOf (stratumPoly O m (M + m) (loopClassN π p)) = ({(1, m)} : Multiset (ℕ × ℕ)) := by
  have hmem : loopClassN π p ∈ levelZeroStratum O m (M + m) ((X + C p.1) ^ m) := by
    rw [mem_levelZeroStratum_iff (by omega)]
    exact ⟨IFCG3.loopMapN p.1 π p.2.1, rfl,
      IFCG3.map_residue_monicPoly_loopMapN hπ p.1 p.2.1⟩
  rw [stratumPoly_eq_of_mem hmem, patternOf_addC_pow p.1 hm]

/-- **The exact pattern-cell partition** of the non-loop decided set over the bank. -/
theorem card_nonloopDecidedSet_eq_sum_pcellCount {π : O} {m : ℕ} (hm : 1 ≤ m)
    (σ : FactorizationType) (M : ℕ) :
    Nat.card (nonloopDecidedSet π m σ M)
      = ∑ t ∈ patternBank m, pcellCount O π m σ M t := by
  haveI : Fintype (Coeff O m (M + m)) := Fintype.ofFinite _
  have hpart := natCard_eq_sum_fiber (nonloopDecidedSet π m σ M)
    (fun c => patternOf (stratumPoly O m (M + m) c)) (patternBank m)
    (fun c _ => patternOf_mem_patternBank (stratumPoly_monic c) (stratumPoly_natDegree c))
  rw [hpart]
  rfl

/-- **Every non-deep cell count is the pattern fiber's census sum** — the loop image is
confined to the deep cell (`patternOf_stratumPoly_loopClassN`), and the cell splits over
the strata of the fiber's residuals. -/
theorem pcellCount_eq_fiber_sum [Fintype (ResidueField O)] {π : O} (hπ : Irreducible π)
    {m : ℕ} (hm : 1 ≤ m) (σ : FactorizationType) (M : ℕ)
    {t : Multiset (ℕ × ℕ)} (htne : t ≠ ({(1, m)} : Multiset (ℕ × ℕ))) :
    pcellCount O π m σ M t
      = ∑ f ∈ fiberFinset (ResidueField O) m t ∅, stratDecCount O m σ (M + m) f := by
  haveI : Fintype (Coeff O m (M + m)) := Fintype.ofFinite _
  -- A: the loop image avoids every non-deep pattern cell
  have hcell : (nonloopDecidedSet π m σ M
        ∩ {c | patternOf (stratumPoly O m (M + m) c) = t} : Set (Coeff O m (M + m)))
      = (decidedSet O m σ (M + m)
          ∩ {c | patternOf (stratumPoly O m (M + m) c) = t}) := by
    ext c
    simp only [nonloopDecidedSet, Set.mem_inter_iff, Set.mem_sdiff, Set.mem_setOf_eq]
    constructor
    · rintro ⟨⟨hd, -⟩, hp⟩
      exact ⟨hd, hp⟩
    · rintro ⟨hd, hp⟩
      refine ⟨⟨hd, ?_⟩, hp⟩
      rintro ⟨q, rfl⟩
      exact htne (hp.symm.trans (patternOf_stratumPoly_loopClassN hπ hm q))
  -- B: the cell splits over the strata of the fiber's residuals
  have hcover : ∀ c ∈ (decidedSet O m σ (M + m)
      ∩ {c | patternOf (stratumPoly O m (M + m) c) = t} : Set (Coeff O m (M + m))),
      stratumPoly O m (M + m) c ∈ fiberFinset (ResidueField O) m t ∅ := by
    intro c hc
    rw [mem_fiberFinset_iff]
    exact ⟨⟨stratumPoly_monic c, stratumPoly_natDegree c⟩, hc.2,
      fun p hp => absurd hp (Finset.notMem_empty p)⟩
  have hsplit := natCard_eq_sum_fiber _ (fun c => stratumPoly O m (M + m) c)
    (fiberFinset (ResidueField O) m t ∅) hcover
  rw [pcellCount, hcell, hsplit]
  refine Finset.sum_congr rfl fun f hf => ?_
  obtain ⟨⟨hfm, hfd⟩, hfpat, -⟩ := mem_fiberFinset_iff.1 hf
  have hset : ((decidedSet O m σ (M + m)
        ∩ {c | patternOf (stratumPoly O m (M + m) c) = t})
        ∩ (fun c => stratumPoly O m (M + m) c) ⁻¹' {f} : Set (Coeff O m (M + m)))
      = (decidedSet O m σ (M + m) ∩ levelZeroStratum O m (M + m) f) := by
    ext c
    simp only [Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_preimage,
      Set.mem_singleton_iff]
    constructor
    · rintro ⟨⟨hd, -⟩, hsp⟩
      exact ⟨hd, (mem_levelZeroStratum_iff_stratumPoly (by omega) f c).2 hsp⟩
    · rintro ⟨hd, hstrat⟩
      have hsp := (mem_levelZeroStratum_iff_stratumPoly (by omega) f c).1 hstrat
      exact ⟨⟨hd, by rw [hsp, hfpat]⟩, hsp⟩
  rw [hset]
  rfl

end Partition

/-! ## §7 — ★★ THE REDUCTION -/

section Reduction

/-- **The non-deep fiber families are uniform rational limits**: §1's exchange divides the
`VAgg` coefficient by the labelling multiplicity, and §4 propagates the kernel through
the peel. -/
theorem fiberFamily_URLim (hSP : SinglePointAggregateLaw) {m : ℕ} (hm : 4 ≤ m)
    (hsm : ∀ k, k < m → ∀ σ' : FactorizationType, σ'.degree = k → DecidedValueLaw k σ')
    (σ : FactorizationType) {t : Multiset (ℕ × ℕ)} (ht : t ∈ patternBank m)
    (htne : t ≠ ({(1, m)} : Multiset (ℕ × ℕ))) :
    URLim (fiberFamily m σ t) := by
  obtain ⟨htmass, htpos⟩ := mem_patternBank_iff.1 ht
  -- enumerate the pattern as a listing
  have hmem : ∀ i : Fin t.toList.length, t.toList.get i ∈ t := fun i =>
    Multiset.mem_toList.1 (List.get_mem t.toList i)
  have hpat : sysPattern (fun i => t.toList.get i) = t := by
    rw [sysPattern, List.ofFn_get, Multiset.coe_toList]
  have hmass : sysMass (fun i => t.toList.get i) = m := by
    rw [sysMass_eq_pattern_mass, hpat, htmass]
  have hδ : ∀ i, 1 ≤ (t.toList.get i).1 := fun i => (htpos _ (hmem i)).1
  have he : ∀ i, 1 ≤ (t.toList.get i).2 := fun i => (htpos _ (hmem i)).2
  -- block admissibility for the peel propagation
  have hblk : ∀ i, 1 ≤ ((simpleSys (fun i => t.toList.get i)) i).δ
      ∧ ((simpleSys (fun i => t.toList.get i)) i).E ≠ []
      ∧ ∀ e ∈ ((simpleSys (fun i => t.toList.get i)) i).E, 1 ≤ e := by
    intro i
    refine ⟨hδ i, by simp [simpleSys], ?_⟩
    intro e hee
    rw [simpleSys, List.mem_singleton] at hee
    subst hee
    exact he i
  have hdeep : ∀ i, ¬(((simpleSys (fun i => t.toList.get i)) i).δ = 1
      ∧ ((simpleSys (fun i => t.toList.get i)) i).E = [m]) := by
    rintro i ⟨h1, h2⟩
    have h1' : (t.toList.get i).1 = 1 := h1
    have h2' : [(t.toList.get i).2] = [m] := h2
    have h2'' : (t.toList.get i).2 = m := List.singleton_inj.1 h2'
    have hin : ((1 : ℕ), m) ∈ t := by
      have := hmem i
      rwa [show t.toList.get i = (1, m) from Prod.ext h1' h2''] at this
    -- the deep entry forces the whole pattern to be the deep singleton
    have hsplit : t = ((1 : ℕ), m) ::ₘ t.erase ((1 : ℕ), m) := (Multiset.cons_erase hin).symm
    have hrest : ((t.erase ((1 : ℕ), m)).map (fun p => p.1 * p.2)).sum = 0 := by
      have := htmass
      rw [hsplit, Multiset.map_cons, Multiset.sum_cons] at this
      omega
    have hrest0 : t.erase ((1 : ℕ), m) = 0 := by
      by_contra hcon
      obtain ⟨x, hx⟩ := Multiset.exists_mem_of_ne_zero hcon
      have hxt : x ∈ t := Multiset.mem_of_mem_erase hx
      have hxpos := htpos x hxt
      have hxle : x.1 * x.2 ≤ 0 := by
        rw [← hrest]
        exact Multiset.single_le_sum (fun y _ => Nat.zero_le y) _
          (Multiset.mem_map_of_mem _ hx)
      have : 1 ≤ x.1 * x.2 :=
        Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by omega))
      omega
    exact htne (by rw [hsplit, hrest0]; rfl)
  have hsysmass : (∑ i, ((simpleSys (fun i => t.toList.get i)) i).mass) = m := by
    rw [← hmass, sysMass]
    exact Finset.sum_congr rfl fun i _ => rfl
  -- the peel propagation at the label's data
  have hUR := vaggFamily_URLim hSP hm hsm _ (simpleSys (fun i => t.toList.get i))
    hblk hdeep (le_of_eq hsysmass) σ.data
  -- transfer through the labelled/unlabelled exchange
  refine ((URLim_const (1 / multPattern t)).mul hUR).congr ?_
  intro O _ _ _ _ _ N hN1
  letI : Fintype (ResidueField O) := Fintype.ofFinite (ResidueField O)
  unfold vaggFamily fiberFamily
  have hexch := VAgg_eq_fiber (O := O) hN1 (fun i => t.toList.get i) hδ he ∅
    (fun q hq => absurd hq (Finset.notMem_empty q))
  rw [hpat, hmass] at hexch
  have hcoefQ : (VAgg O N (simpleSys (fun i => t.toList.get i)) ∅) σ.data
      = (multPattern t : ℚ)
          * ∑ f ∈ fiberFinset (ResidueField O) m t ∅, (stratDecCount O m σ N f : ℚ) := by
    rw [hexch, typeAlg_nsmul_apply, typeAlg_sum_apply]
    congr 1
    refine Finset.sum_congr rfl fun f _ => ?_
    exact stratPoly_apply m N f σ.data
  rw [hsysmass, hcoefQ]
  push_cast
  have hc : ((multPattern t : ℝ)) ≠ 0 := by
    exact_mod_cast (multPattern_pos t).ne'
  rw [one_div, inv_mul_eq_div, div_right_comm, mul_div_cancel_left₀ _ hc]

/-- ★★ **THE REDUCTION** (the census clause): the two named kernels fire IFCG16's
per-genre census at every mass `m ≥ 4`.  The bank: one genre per non-deep pattern of mass
`m` (weights = the `URLim` pairs of the fiber families; children empty) plus the deep
genre (weight = the deep-linear kernel's pair).  The partition is §6's exact pattern-cell
partition; the limits are §7's fiber limits read along `M ↦ M + m`. -/
theorem rationalNonloopCensusAt_of_kernels (hSP : SinglePointAggregateLaw)
    (hDL : DeepLinearClusterLaw) {m : ℕ} (hm : 4 ≤ m) :
    IFCG16.RationalNonloopCensusAt m := by
  intro hsmaller σ hσ hwit
  have hm1 : 1 ≤ m := by omega
  -- the deep-linear kernel's pair
  obtain ⟨nD, dD, hdD, hDlaw⟩ := hDL m hm hsmaller σ hσ hwit
  -- the non-deep genres' pairs, chosen before the DVR
  have hUR : ∀ j : Fin ((patternBank m).erase ({(1, m)} : Multiset (ℕ × ℕ))).card,
      URLim (fiberFamily m σ
        ((((patternBank m).erase ({(1, m)} : Multiset (ℕ × ℕ))).equivFin.symm j
          : Multiset (ℕ × ℕ)))) := by
    intro j
    have hjB := (((patternBank m).erase ({(1, m)} : Multiset (ℕ × ℕ))).equivFin.symm j).2
    exact fiberFamily_URLim hSP hm hsmaller σ
      (Finset.mem_of_mem_erase hjB) (Finset.ne_of_mem_erase hjB)
  choose nP dP hdP hPval using hUR
  refine ⟨((patternBank m).erase ({(1, m)} : Multiset (ℕ × ℕ))).card + 1,
    Fin.snoc (fun j => (nP j, dP j)) (nD, dD), fun _ => [], ?_, ?_, ?_⟩
  · -- polynomial denominators nonzero
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · rw [Fin.snoc_last]
      exact hdD
    · rw [Fin.snoc_castSucc]
      exact hdP j
  · -- children lists are empty
    intro i p hp
    simp at hp
  · intro O _ _ _ _ _
    refine ⟨?_, ?_⟩
    · -- evaluated denominators nonzero
      intro i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · rw [Fin.snoc_last]
        exact (hDlaw O).1
      · rw [Fin.snoc_castSucc]
        exact (hPval j O).1
    · intro π hπ
      letI : Fintype (ResidueField O) := Fintype.ofFinite (ResidueField O)
      refine ⟨fun i M => pcellCount O π m σ M
        (Fin.snoc (α := fun _ => Multiset (ℕ × ℕ))
          (fun j => ((((patternBank m).erase ({(1, m)} : Multiset (ℕ × ℕ))).equivFin.symm j
            : Multiset (ℕ × ℕ)))) ({(1, m)} : Multiset (ℕ × ℕ)) i), ?_, ?_⟩
      · -- THE EXACT FINITE-LEVEL PARTITION
        intro M
        calc Nat.card (nonloopDecidedSet π m σ M)
            = ∑ t ∈ patternBank m, pcellCount O π m σ M t :=
              card_nonloopDecidedSet_eq_sum_pcellCount hm1 σ M
          _ = pcellCount O π m σ M ({(1, m)} : Multiset (ℕ × ℕ))
              + ∑ t ∈ (patternBank m).erase ({(1, m)} : Multiset (ℕ × ℕ)),
                  pcellCount O π m σ M t := by
              conv_lhs => rw [← Finset.insert_erase (deep_mem_patternBank hm1)]
              rw [Finset.sum_insert (Finset.notMem_erase _ _)]
          _ = pcellCount O π m σ M ({(1, m)} : Multiset (ℕ × ℕ))
              + ∑ j : Fin ((patternBank m).erase ({(1, m)} : Multiset (ℕ × ℕ))).card,
                  pcellCount O π m σ M
                    ((((patternBank m).erase ({(1, m)} : Multiset (ℕ × ℕ))).equivFin.symm j
                      : Multiset (ℕ × ℕ))) := by
              congr 1
              rw [← Finset.sum_coe_sort
                ((patternBank m).erase ({(1, m)} : Multiset (ℕ × ℕ)))
                (fun t => pcellCount O π m σ M t)]
              exact (Equiv.sum_comp
                (((patternBank m).erase ({(1, m)} : Multiset (ℕ × ℕ))).equivFin.symm)
                (fun x => pcellCount O π m σ M ↑x)).symm
          _ = ∑ i, pcellCount O π m σ M
                (Fin.snoc (α := fun _ => Multiset (ℕ × ℕ))
                  (fun j =>
                    ((((patternBank m).erase ({(1, m)} : Multiset (ℕ × ℕ))).equivFin.symm j
                      : Multiset (ℕ × ℕ))))
                  ({(1, m)} : Multiset (ℕ × ℕ)) i) := by
              rw [Fin.sum_univ_castSucc]
              simp only [Fin.snoc_castSucc, Fin.snoc_last]
              exact Nat.add_comm _ _
      · -- THE PER-GENRE LIMITS
        intro i
        refine Fin.lastCases ?_ (fun j => ?_) i
        · -- the deep-linear genre: the second kernel, verbatim
          simp only [Fin.snoc_last, List.map_nil, List.prod_nil, mul_one]
          exact (hDlaw O).2 π hπ
        · -- a non-deep genre: the fiber family's limit read along `M ↦ M + m`
          simp only [Fin.snoc_castSucc, List.map_nil, List.prod_nil, mul_one]
          have htmem := (((patternBank m).erase ({(1, m)} : Multiset (ℕ × ℕ))).equivFin.symm j).2
          have hlim := ((hPval j O).2).comp (Filter.tendsto_add_atTop_nat m)
          refine hlim.congr ?_
          intro M
          show fiberFamily m σ _ O (M + m) = _
          unfold fiberFamily
          rw [← pcellCount_eq_fiber_sum hπ hm1 σ M (Finset.ne_of_mem_erase htmem)]

/-- The uniform census from the two kernels. -/
theorem uniformCensus_of_kernels (hSP : SinglePointAggregateLaw)
    (hDL : DeepLinearClusterLaw) : IFCG16.UniformRationalNonloopCensus :=
  fun _ hm => rationalNonloopCensusAt_of_kernels hSP hDL hm

/-- ★★ **THE CAPSTONE REDUCTION**: the single-point fractional-slope kernel and the
deep-linear cluster kernel — the campaign's TWO last named statements — fire the
all-degree decided slice through IFCG16's census, IFCG15's remainder equivalence, and
IFCG14's assembly. -/
theorem decidedSliceAt_all_of_singlePoint (hSP : SinglePointAggregateLaw)
    (hDL : DeepLinearClusterLaw) :
    ∀ n : ℕ, Uniformity.Density.DecidedSliceAt n :=
  IFCG16.decidedSliceAt_all_of_census (uniformCensus_of_kernels hSP hDL)

end Reduction

end Uniformity.Density.IFCG18

end

/-! ## AXCHECK FOOTER — expect Lean core `{propext, Classical.choice, Quot.sound}`
everywhere; the C.33 cite must NOT occur. -/

#print axioms Uniformity.Density.IFCG18.VAgg_eq_fiber
#print axioms Uniformity.Density.IFCG18.vaggFamily_URLim
#print axioms Uniformity.Density.IFCG18.fiberFamily_URLim
#print axioms Uniformity.Density.IFCG18.card_nonloopDecidedSet_eq_sum_pcellCount
#print axioms Uniformity.Density.IFCG18.pcellCount_eq_fiber_sum
#print axioms Uniformity.Density.IFCG18.rationalNonloopCensusAt_of_kernels
#print axioms Uniformity.Density.IFCG18.decidedSliceAt_all_of_singlePoint
