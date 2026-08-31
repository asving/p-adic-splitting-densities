/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import Uniformity.ChapI.IFCG60
import Uniformity.ChapI.IFCG61

/-!
# Uniformity.ChapI.IFCG71 — [VA23 2026-08-31] VisCensusLaw's axes 2–3: the summed
rationality (the Tannery/geometric-tail assembly) and the cluster/collision assembly

Stage VA23 of the cone census (design record `runs/wave-c/verdict_VA23.md`; consumes
VCL = `IFCG60`, IGV = `IFCG61`, RCD = `IFCG56`, and through them the whole spine).
VCL factored the open convolution row `VisCensusLaw g m σ` (σ ramified,
`2 ≤ card σ.data`) into three axes; GNA's `IFCG70` closed axis 1 (the per-depth
full-box values).  THIS file closes the ANALYTIC content of axes 2 and 3 — the depth
summation and the cluster/collision assembly — and re-bases the row onto exactly-named
value inputs:

* **§1 THE DOMINATION/ENVELOPE LAYER** (Lean-core): the vis-restricted depth masses
  are termwise dominated by the FULL depth strata (`sum_pairDepthFiber_vis_le`); the
  `≥ w` stratum partitions into the exact strata (`card_depthPairSetGE_eq_sum`); the
  finite-level partial sums are bounded by the full box
  (`sum_card_depthPairSet_le`); and ★ THE DEEP-BOX ENVELOPE
  (`sum_pairDepthFiber_vis_tail_le`): the depth tail `v > V` of the visible pair
  census is bounded by the N-FREE level-`(V+2)` deep box — RCD's GE-cylinder
  (`card_depthPairSetGE_levels`) makes the envelope independent of the window.
* **§2 ★ THE TANNERY INSTRUMENT** (`tendsto_depthSum_of_env`, pure real analysis):
  a depth-indexed family with per-depth limits, partial sums bounded by `1`, and an
  N-free vanishing tail envelope has summable limits and the SUMMED census converges
  to the summed limit — the `Σ_v`/`M → ∞` interchange, uniform in everything.
* **§3 ★ THE GEOMETRIC-TAIL VALUE** (`tsum_of_geom_ratio`): if the per-depth limits
  are eventually geometric (`L (v+1) = L v / q^a` from `v₀` on), the summed value is
  the RATIONAL function `Σ_{v<v₀} L v + L v₀ · q^a/(q^a − 1)` — the key subtlety of
  VCL's fence (an infinite sum of rationals need not be rational) is discharged by
  the geometric structure, exactly as the charge prescribed.
* **§4 ★★ THE PER-ENTRY ASSEMBLY** (`zcURLim_visEntry_depthSum`): for one convolution
  table entry, per-depth `ZcVal` value data (explicit witness polynomials), the
  polynomial-level geometric ratio `X^a · (n_{v+1}·d_v) = n_v·d_{v+1}`, and the
  deep-box drain `DeepStratumDrain n₁ n₂` produce the `ZcURLim` of the FULL
  depth-summed visible pair census at that entry.  ★★ the cluster form
  (`zcVal_visEntry_of_clusters` + `zcURLim_visEntry_depthSum_of_clusters`): the same
  from CLUSTER census values, through VCL's landed drainage bridge
  (`tendsto_visDepth_sub_clusters`) — axis 3's `q^v`-corrected assembly.
* **§5 ★ THE DRAIN FIRES AT `min = 1`** (`deepStratumDrain_one_right`/`_left`):
  through IGV's `min = 1` law the deep box at `(1, n₂)` is EXACTLY `q^{(1+n₂)L − w}`
  (`card_depthPairSetGE_one_right`), so the envelope is the exact geometric
  `q^{−(V+1)}` and the drain holds OUTRIGHT — the drain hypothesis survives only at
  `2 ≤ min(n₁, n₂)` mass splits (`deepStratumDrain_of_min_two`).
* **§6 ★★★ THE GENRE ASSEMBLY AND THE ROW RE-BASED**:
  `zcURLim_visWeight_of_entryGeom` (the genre weight census from per-entry geometric
  data — `VisWeightLaw`/`PowerVisWeightLaw` instances, PURE Lean-core), and ★★★
  `visCensusLaw_of_clusterGeom_collisions`:
  **`VisCensusLaw g m σ` at EVERY mass and type, both genres, rests on exactly
  {per-entry geometric CLUSTER values, the `min ≥ 2` deep-box drains, the two
  collision limits}** — the analytic axes are CLOSED, the remaining content is the
  named value/collision inputs.
* **§7 ★★★ THE MASTERS RECOMPUTED**: `decidedSliceAt_all_of_clusterGeom` /
  `capstoneHypotheses_of_clusterGeom` — the census master with the convolution row's
  premise replaced by {geometric cluster values, `min ≥ 2` drains, collision limits}
  (the other rows byte-identical to VCL's masters).

## THE HONEST FENCE

The charge's item 3 (fire `VisCensusLaw` OUTRIGHT at all ramified multi-σ) is NOT
reachable, and is not claimed: the per-depth CLUSTER censuses restricted to the
genre's visible cells (which visible cells the clusters land on — the sector-membership
× depth joint census) and the two COLLISION limits (B.42's block-grouping genre) are
the exact named remainder, together with the `min ≥ 2` deep-box drains
(`DeepStratumDrain n₁ n₂` ⟺ the full-box strata masses sum to `1` — at `min = 1`
proved here; at `min ≥ 2` it is the `Σ_v zed(K,n,v)·q^{−v} = q^{2n}` identity of
GNA's value stack, not yet landed).  GNA's landed axis-1 values are the FULL-box
strata; the genre restriction is new content.  Nothing is weakened; every consumed
statement is byte-untouched.

## Axiom fence (machine-exact at landing)

Everything in §§1–4 and §6 expects PURE Lean core
`{propext, Classical.choice, Quot.sound}`.  §5's genre assembly and §7's masters
inherit exactly the owner-signed B.42 cite
`Uniformity.Density.Leaf.exists_slope_factorization` (through VCL's graded census
identities and the masters) — never re-consumed — and the capstone master
additionally inherits `Uniformity.Density.Tower.agnprw_termination` (ID12's).
C.33 and `AX_cellRecursion` must NOT occur.  Zero sorries, zero new axioms; the new
definitions are the explicit-witness reader `ZcVal`, the two bundled value Props
(`VisEntryGeom`, `VisEntryClusterGeom`), and the named drain Prop
(`DeepStratumDrain`) — hypothesis-currency only, no new trust surface.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.overlappingInstances false

noncomputable section

namespace Uniformity.Density.IFCG71

open IsLocalRing Polynomial Filter Topology
open Uniformity.Density.Induction
open Uniformity.Density.IFCG14 (DecidedValueLaw Witnessed)
open Uniformity.Density.IFCG24 (ZcURLim ZcURLim_zero ZcURLim_sum ConeRemainderLaw)
open Uniformity.Density.IFCG38 (convPairs mulClassAt)
open Uniformity.Density.IFCG40 (multCount)
open Uniformity.Density.IFCG41 (mixDepth mixDepth_le pairDepthFiber CollisionLaw)
open Uniformity.Density.IFCG44 (PowerFullSpanLaw)
open Uniformity.Density.IFCG48 (FactorCorrespondenceAt)
open Uniformity.Density.IFCG51 (EisFullSpanRemainderLaw)
open Uniformity.Density.IFCG56 (VisCountLaw VisWeightLaw visWeight depthPairSet
  depthPairSetGE card_depthPairSet_levels card_depthPairSetGE_levels
  pairDepthFiber_eq_natCard decidedPairSet pairFactor shiftedDepthFiber)
open Uniformity.Density.IFCG57 (LeafSubfaceLaw)
open Uniformity.Density.IFCG58 (VisGenre visGenreSet VisCensusLaw
  visCensusLaw_split_iff visCensusLaw_power_iff PowerVisWeightLaw powerVisWeight
  powerCollisionTotal)
open Uniformity.Density.IFCG60 (visDepthMass sum_multCount_eq_sum_visDepthMass
  visWeight_eq_sum_visDepthMass powerVisWeight_eq_sum_visDepthMass
  visCensusLaw_of_weights_collisions sum_card_depthPairSet_eq
  tendsto_visDepth_sub_clusters)
open Uniformity.Density.IFCG61 (mixDepth_swap card_depthPairSet_one_right)

/-! ## §0 — the kit: counting spines, the explicit-witness value reader, and the
depth-cap vanishing -/

section Kit

open Classical in
/-- `Nat.card` of a set in a finite type, as a `Finset.filter` card (the corpus's
counting bridge, reproduced). -/
private theorem natCard_set_eq_card_filter {α : Type*} [Fintype α] (s : Set α) :
    Nat.card s = (Finset.univ.filter (fun a => a ∈ s)).card := by
  rw [Nat.card_coe_set_eq, ← Set.ncard_coe_finset (Finset.univ.filter (fun a => a ∈ s))]
  congr 1
  ext a
  simp

open Classical in
/-- Fiberwise decomposition of a set count along any map, over any `Finset` containing
the image of the set (VCL's counting spine, reproduced). -/
private theorem natCard_eq_sum_fiber_of_mem {α β : Type*} [Finite α]
    (s : Set α) (φ : α → β) (T : Finset β) (hT : ∀ a ∈ s, φ a ∈ T) :
    Nat.card s = ∑ b ∈ T, Nat.card ((s ∩ φ ⁻¹' {b} : Set α)) := by
  classical
  letI : Fintype α := Fintype.ofFinite α
  rw [natCard_set_eq_card_filter s,
    Finset.card_eq_sum_card_fiberwise (f := φ) (t := T)
      (fun a ha => hT a (Finset.mem_filter.mp ha).2)]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [natCard_set_eq_card_filter, Finset.filter_filter]
  congr 1
  ext a
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Set.mem_inter_iff,
    Set.mem_preimage, Set.mem_singleton_iff]

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)]

/-- Above the level cap the depth strata are empty (`mixDepth ≤ N`). -/
theorem depthPairSet_eq_empty_of_lt (π : O) (n₁ n₂ : ℕ) {N v : ℕ} (hv : N < v) :
    depthPairSet O π n₁ n₂ N v = ∅ := by
  ext d
  simp only [depthPairSet, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
  intro h
  exact absurd (h ▸ mixDepth_le π d.1 d.2) (by omega)

/-- Above the level cap the depth-graded pair fibers vanish. -/
theorem pairDepthFiber_eq_zero_of_lt (π : O) {m : ℕ} (σ : FactorizationType) (M : ℕ)
    (p : (ℕ × ℕ) × Multiset (ℕ × ℕ)) (c : Coeff O m (M + m)) {v : ℕ}
    (hv : M + m < v) : pairDepthFiber O π m σ M p c v = 0 := by
  by_cases hpm : p.1.1 + p.1.2 = m
  · rw [pairDepthFiber_eq_natCard π σ M p hpm c v,
      depthPairSet_eq_empty_of_lt π p.1.1 p.1.2 hv, Set.inter_empty,
      Nat.card_coe_set_eq, Set.ncard_empty]
  · unfold pairDepthFiber
    rw [dif_neg hpm]

/-- **The explicit-witness rational-limit reader**: the body of `ZcURLim` at a GIVEN
numerator/denominator pair — the currency in which per-depth value data enters the
assembly (the existential `ZcURLim` cannot carry the cross-depth geometric relation;
the explicit pair can). -/
def ZcVal
    (F : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
      [IsAdicComplete (maximalIdeal O) O] [Finite (ResidueField O)],
      O → ℕ → ℝ) (n d : Polynomial ℚ) : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [IsAdicComplete (maximalIdeal O) O] [Finite (ResidueField O)],
    d.eval ((residueCard O : ℕ) : ℚ) ≠ 0 ∧
      ∀ π : O, Irreducible π →
        Filter.Tendsto (F O π) Filter.atTop
          (nhds ((n.eval ((residueCard O : ℕ) : ℚ)
            / d.eval ((residueCard O : ℕ) : ℚ) : ℚ) : ℝ))

/-- An explicit-witness value packages into the existential `ZcURLim`. -/
theorem ZcVal.zcURLim
    {F : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
      [IsAdicComplete (maximalIdeal O) O] [Finite (ResidueField O)],
      O → ℕ → ℝ} {n d : Polynomial ℚ} (hd : d ≠ 0) (h : ZcVal F n d) :
    ZcURLim F := ⟨n, d, hd, h⟩

/-- The split of a capped depth sum at any `v₀`, given vanishing above the cap: the
head is the FIXED window `range v₀`, the tail the moving `Ico v₀ (K + 1)` (for
`K + 1 < v₀` the head's extra terms vanish and the tail is empty). -/
private theorem sum_range_split {K v₀ : ℕ} (f : ℕ → ℝ) (h0 : ∀ v, K < v → f v = 0) :
    ∑ v ∈ Finset.range (K + 1), f v
      = ∑ v ∈ Finset.range v₀, f v + ∑ v ∈ Finset.Ico v₀ (K + 1), f v := by
  rcases Nat.lt_or_ge (K + 1) v₀ with hlt | hle
  swap
  · rw [Finset.sum_range_add_sum_Ico f hle]
  · rw [Finset.Ico_eq_empty (by omega), Finset.sum_empty, add_zero]
    refine Finset.sum_subset (Finset.range_subset_range.mpr (by omega)) ?_
    intro v hv hnv
    exact h0 v (by simpa using (Finset.mem_range.not.mp hnv))

end Kit

/-! ## §1 — THE DOMINATION/ENVELOPE LAYER (Lean-core): the visible depth masses under
the full strata, and the N-free deep-box envelope -/

section Domination

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)]

/-- **The vis-restricted depth mass is dominated by the FULL depth stratum**: the
depth-`v` visible pair mass at one table entry — summed over ANY `Finset` of product
cells — is at most the full depth-`v` stratum count (the per-cell fibers are disjoint
sub-sets of the stratum). -/
theorem sum_pairDepthFiber_le_card_depthPairSet {π : O} {n₁ n₂ M v : ℕ}
    (σ : FactorizationType) (part : Multiset (ℕ × ℕ))
    (T : Finset (Coeff O (n₁ + n₂) (M + (n₁ + n₂)))) :
    ∑ c ∈ T, pairDepthFiber O π (n₁ + n₂) σ M ((n₁, n₂), part) c v
      ≤ Nat.card (depthPairSet O π n₁ n₂ (M + (n₁ + n₂)) v) := by
  classical
  letI : Fintype (Coeff O (n₁ + n₂) (M + (n₁ + n₂))) := Fintype.ofFinite _
  rw [natCard_eq_sum_fiber_of_mem (depthPairSet O π n₁ n₂ (M + (n₁ + n₂)) v)
    (fun q => mulClassAt rfl q.1 q.2) Finset.univ (fun q _ => Finset.mem_univ _)]
  refine le_trans (Finset.sum_le_sum fun c _ => ?_)
    (Finset.sum_le_sum_of_subset (Finset.subset_univ T))
  rw [pairDepthFiber_eq_natCard π σ M ((n₁, n₂), part) rfl c v,
    Nat.card_coe_set_eq, Nat.card_coe_set_eq]
  refine Set.ncard_le_ncard ?_ (Set.toFinite _)
  rintro q ⟨⟨-, hmul⟩, hdep⟩
  exact ⟨hdep, hmul⟩

/-- **The `≥ w` stratum partitions into the exact strata** at every level. -/
theorem card_depthPairSetGE_eq_sum (π : O) {n₁ n₂ L w : ℕ} :
    Nat.card (depthPairSetGE O π n₁ n₂ L w)
      = ∑ v ∈ Finset.Ico w (L + 1), Nat.card (depthPairSet O π n₁ n₂ L v) := by
  classical
  rw [natCard_eq_sum_fiber_of_mem (depthPairSetGE O π n₁ n₂ L w)
    (fun q => mixDepth π q.1 q.2) (Finset.Ico w (L + 1))
    (fun q hq => Finset.mem_Ico.mpr ⟨hq, Nat.lt_succ_of_le (mixDepth_le π q.1 q.2)⟩)]
  refine Finset.sum_congr rfl fun v hv => ?_
  obtain ⟨hwv, -⟩ := Finset.mem_Ico.mp hv
  refine congrArg Nat.card (congrArg Set.Elem ?_)
  ext q
  simp only [depthPairSetGE, depthPairSet, Set.mem_inter_iff, Set.mem_setOf_eq,
    Set.mem_preimage, Set.mem_singleton_iff]
  constructor
  · rintro ⟨-, h⟩
    exact h
  · intro h
    exact ⟨h ▸ hwv, h⟩

/-- **The finite-level partial sums are bounded by the full box** (the strata
partition, truncated to any window). -/
theorem sum_card_depthPairSet_le (π : O) (n₁ n₂ N V : ℕ) :
    ∑ v ∈ Finset.range (V + 1), Nat.card (depthPairSet O π n₁ n₂ N v)
      ≤ residueCard O ^ ((n₁ + n₂) * N) := by
  rcases Nat.lt_or_ge (N + 1) (V + 1) with hlt | hle
  swap
  · rw [← sum_card_depthPairSet_eq π n₁ n₂ N]
    exact Finset.sum_le_sum_of_subset (Finset.range_subset_range.mpr hle)
  · calc ∑ v ∈ Finset.range (V + 1), Nat.card (depthPairSet O π n₁ n₂ N v)
        = ∑ v ∈ Finset.range (N + 1), Nat.card (depthPairSet O π n₁ n₂ N v) := by
          refine (Finset.sum_subset
            (Finset.range_subset_range.mpr (by omega : N + 1 ≤ V + 1)) ?_).symm
          intro v hv hnv
          rw [depthPairSet_eq_empty_of_lt π n₁ n₂
            (by simpa using (Finset.mem_range.not.mp hnv)),
            Nat.card_coe_set_eq, Set.ncard_empty]
      _ ≤ residueCard O ^ ((n₁ + n₂) * N) := le_of_eq (sum_card_depthPairSet_eq π n₁ n₂ N)

/-- ★ **THE DEEP-BOX ENVELOPE** (the tail bound, N-free): the depth tail `v > V` of
the visible pair census at one table entry is dominated by the level-`(V + 2)` deep
box times the exact cylinder factor — RCD's GE-cylinder makes the envelope
independent of the window `M`. -/
theorem sum_pairDepthFiber_vis_tail_le {π : O} (hπ : Irreducible π) {n₁ n₂ M V : ℕ}
    (hV : V + 2 ≤ M + (n₁ + n₂)) (σ : FactorizationType) (part : Multiset (ℕ × ℕ))
    (T : Finset (Coeff O (n₁ + n₂) (M + (n₁ + n₂)))) :
    ∑ v ∈ Finset.Ico (V + 1) (M + (n₁ + n₂) + 1),
        ∑ c ∈ T, pairDepthFiber O π (n₁ + n₂) σ M ((n₁, n₂), part) c v
      ≤ Nat.card (depthPairSetGE O π n₁ n₂ (V + 2) (V + 1))
          * residueCard O ^ ((n₁ + n₂) * (M + (n₁ + n₂) - (V + 2))) := by
  calc ∑ v ∈ Finset.Ico (V + 1) (M + (n₁ + n₂) + 1),
        ∑ c ∈ T, pairDepthFiber O π (n₁ + n₂) σ M ((n₁, n₂), part) c v
      ≤ ∑ v ∈ Finset.Ico (V + 1) (M + (n₁ + n₂) + 1),
          Nat.card (depthPairSet O π n₁ n₂ (M + (n₁ + n₂)) v) :=
        Finset.sum_le_sum fun v _ =>
          sum_pairDepthFiber_le_card_depthPairSet σ part T
    _ = Nat.card (depthPairSetGE O π n₁ n₂ (M + (n₁ + n₂)) (V + 1)) :=
        (card_depthPairSetGE_eq_sum π).symm
    _ = Nat.card (depthPairSetGE O π n₁ n₂ (V + 2) (V + 1))
          * residueCard O ^ ((n₁ + n₂) * (M + (n₁ + n₂) - (V + 2))) :=
        card_depthPairSetGE_levels hπ n₁ n₂ (by omega) hV

end Domination

/-! ## §2 — ★ THE TANNERY INSTRUMENT: the `Σ_v` / `M → ∞` interchange from an N-free
vanishing tail envelope (pure real analysis; the census enters only through the three
inequality hypotheses, all discharged by §1) -/

section Tannery

/-- ★ **The depth-sum limit interchange**: a depth-indexed nonnegative family `f v M`
with per-depth limits `L v`, partial sums bounded by `1`, and a depth tail dominated
by an `M`-free envelope `env V → 0`, has summable limits and its capped depth sums
converge to the summed limit.  (The cap `M + m` may exceed the envelope's validity
window only on the tail side, which the envelope hypothesis guards via
`V + 2 ≤ M + m`.) -/
theorem tendsto_depthSum_of_env {m : ℕ} {f : ℕ → ℕ → ℝ} {L : ℕ → ℝ} {env : ℕ → ℝ}
    (hf0 : ∀ v M, 0 ≤ f v M)
    (hL : ∀ v, Filter.Tendsto (fun M => f v M) Filter.atTop (nhds (L v)))
    (hpart : ∀ V M, ∑ v ∈ Finset.range (V + 1), f v M ≤ 1)
    (htail : ∀ V M, V + 2 ≤ M + m →
      ∑ v ∈ Finset.Ico (V + 1) (M + m + 1), f v M ≤ env V)
    (henv : Filter.Tendsto env Filter.atTop (nhds 0)) :
    Summable L ∧
      Filter.Tendsto (fun M => ∑ v ∈ Finset.range (M + m + 1), f v M)
        Filter.atTop (nhds (∑' v, L v)) := by
  -- the limits are nonnegative and have partial sums bounded by 1
  have hL0 : ∀ v, 0 ≤ L v := fun v =>
    ge_of_tendsto (hL v) (Filter.Eventually.of_forall fun M => hf0 v M)
  have hLpart : ∀ n : ℕ, ∑ v ∈ Finset.range n, L v ≤ 1 := by
    intro n
    have hlim : Filter.Tendsto (fun M => ∑ v ∈ Finset.range n, f v M)
        Filter.atTop (nhds (∑ v ∈ Finset.range n, L v)) :=
      tendsto_finsetSum _ fun v _ => hL v
    refine le_of_tendsto hlim (Filter.Eventually.of_forall fun M => ?_)
    rcases n with - | V
    · simp
    · exact hpart V M
  have hsum : Summable L := summable_of_sum_range_le hL0 hLpart
  refine ⟨hsum, ?_⟩
  -- the limit tail is dominated by the envelope
  have hLtail : ∀ V, ∑' k, L (V + 1 + k) ≤ env V := by
    intro V
    have hsub : Summable (fun k => L (V + 1 + k)) :=
      ((summable_nat_add_iff (V + 1)).mpr hsum).congr fun k => by
        rw [Nat.add_comm k (V + 1)]
    refine Real.tsum_le_of_sum_range_le (fun k => hL0 _) fun K => ?_
    -- each partial tail sum is a limit of eventual partial tails ≤ env V
    have hlim : Filter.Tendsto
        (fun M => ∑ k ∈ Finset.range K, f (V + 1 + k) M) Filter.atTop
        (nhds (∑ k ∈ Finset.range K, L (V + 1 + k))) :=
      tendsto_finsetSum _ fun k _ => hL _
    refine le_of_tendsto hlim ?_
    refine Filter.eventually_atTop.mpr ⟨V + K + 2, fun M hM => ?_⟩
    have hVM : V + 2 ≤ M + m := by omega
    calc ∑ k ∈ Finset.range K, f (V + 1 + k) M
        = ∑ v ∈ Finset.Ico (V + 1) (V + 1 + K), f v M := by
          rw [Finset.sum_Ico_eq_sum_range, Nat.add_sub_cancel_left]
      _ ≤ ∑ v ∈ Finset.Ico (V + 1) (M + m + 1), f v M := by
          refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun v _ _ => hf0 v M
          exact Finset.Ico_subset_Ico le_rfl (by omega)
      _ ≤ env V := htail V M hVM
  -- the main ε-argument
  rw [Metric.tendsto_atTop]
  intro ε hε
  -- choose a window where the envelope is small
  obtain ⟨V, hVenv⟩ := Metric.tendsto_atTop.mp henv (ε / 3) (by linarith)
  have henvV : env V < ε / 3 := by
    have := hVenv V le_rfl
    rw [Real.dist_eq, sub_zero] at this
    exact lt_of_le_of_lt (le_abs_self _) this
  -- the head converges
  have hhead : Filter.Tendsto (fun M => ∑ v ∈ Finset.range (V + 1), f v M)
      Filter.atTop (nhds (∑ v ∈ Finset.range (V + 1), L v)) :=
    tendsto_finsetSum _ fun v _ => hL v
  obtain ⟨M₀, hM₀⟩ := Metric.tendsto_atTop.mp hhead (ε / 3) (by linarith)
  refine ⟨max M₀ (V + 2), fun M hM => ?_⟩
  have hMM₀ : M₀ ≤ M := le_trans (le_max_left _ _) hM
  have hMV : V + 2 ≤ M + m := by
    have := le_trans (le_max_right M₀ (V + 2)) hM
    omega
  -- split the capped sum at the window
  have hsplit : ∑ v ∈ Finset.range (M + m + 1), f v M
      = ∑ v ∈ Finset.range (V + 1), f v M
        + ∑ v ∈ Finset.Ico (V + 1) (M + m + 1), f v M :=
    (Finset.sum_range_add_sum_Ico _ (by omega)).symm
  -- split the limit sum at the window
  have hLsplit : ∑' v, L v
      = ∑ v ∈ Finset.range (V + 1), L v + ∑' k, L (V + 1 + k) := by
    rw [← hsum.sum_add_tsum_nat_add (V + 1)]
    congr 1
    exact tsum_congr fun k => by rw [Nat.add_comm k (V + 1)]
  -- assemble
  have hheadM := hM₀ M hMM₀
  rw [Real.dist_eq] at hheadM ⊢
  have htailf0 : 0 ≤ ∑ v ∈ Finset.Ico (V + 1) (M + m + 1), f v M :=
    Finset.sum_nonneg fun v _ => hf0 v M
  have htailL0 : 0 ≤ ∑' k, L (V + 1 + k) := by
    refine tsum_nonneg fun k => hL0 _
  have htailfM := htail V M hMV
  have htailLV := hLtail V
  rw [hsplit, hLsplit]
  have habs : |∑ v ∈ Finset.range (V + 1), f v M
        + ∑ v ∈ Finset.Ico (V + 1) (M + m + 1), f v M
        - (∑ v ∈ Finset.range (V + 1), L v + ∑' k, L (V + 1 + k))|
      ≤ |∑ v ∈ Finset.range (V + 1), f v M - ∑ v ∈ Finset.range (V + 1), L v|
        + |∑ v ∈ Finset.Ico (V + 1) (M + m + 1), f v M - ∑' k, L (V + 1 + k)| := by
    have : ∑ v ∈ Finset.range (V + 1), f v M
        + ∑ v ∈ Finset.Ico (V + 1) (M + m + 1), f v M
        - (∑ v ∈ Finset.range (V + 1), L v + ∑' k, L (V + 1 + k))
      = (∑ v ∈ Finset.range (V + 1), f v M - ∑ v ∈ Finset.range (V + 1), L v)
        + (∑ v ∈ Finset.Ico (V + 1) (M + m + 1), f v M - ∑' k, L (V + 1 + k)) := by
      ring
    rw [this]
    exact abs_add_le _ _
  have htaildiff : |∑ v ∈ Finset.Ico (V + 1) (M + m + 1), f v M
      - ∑' k, L (V + 1 + k)| < ε / 3 := by
    rw [abs_sub_lt_iff]
    constructor <;> linarith
  linarith [habs, hheadM, htaildiff]

end Tannery

/-! ## §3 — ★ THE GEOMETRIC-TAIL VALUE: an eventually-geometric limit sequence sums
to the rational function `Σ_{v<v₀} L v + L v₀ · q^a/(q^a − 1)` (the discharge of
VCL's rationality subtlety) -/

section GeomValue

/-- The eventually-geometric closed form of the limit values. -/
private theorem L_geom_pow {q : ℝ} (hq : 2 ≤ q) {L : ℕ → ℝ} {v₀ a : ℕ}
    (hgeom : ∀ v, v₀ ≤ v → L (v + 1) = L v / q ^ a) (k : ℕ) :
    L (v₀ + k) = L v₀ * (1 / q ^ a) ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
      have hq0 : (0 : ℝ) < q ^ a := by positivity
      rw [← Nat.add_assoc, hgeom (v₀ + k) (by omega), ih, pow_succ]
      field_simp

/-- ★ **The geometric-tail sum**: a summable sequence that is geometric with ratio
`q^{−a}` from `v₀` on sums to `Σ_{v<v₀} L v + L v₀ · q^a/(q^a − 1)`. -/
theorem tsum_of_geom_ratio {q : ℝ} (hq : 2 ≤ q) {L : ℕ → ℝ} (hsum : Summable L)
    {v₀ a : ℕ} (ha : 1 ≤ a)
    (hgeom : ∀ v, v₀ ≤ v → L (v + 1) = L v / q ^ a) :
    ∑' v, L v = ∑ v ∈ Finset.range v₀, L v + L v₀ * q ^ a / (q ^ a - 1) := by
  have hq1 : (1 : ℝ) < q ^ a :=
    one_lt_pow₀ (by linarith) (by omega)
  have hr0 : (0 : ℝ) ≤ 1 / q ^ a := by positivity
  have hr1 : 1 / q ^ a < 1 := by
    rw [div_lt_one (by positivity)]
    exact hq1
  have htail : ∑' k, L (v₀ + k) = L v₀ * q ^ a / (q ^ a - 1) := by
    have h1 : ∑' k, L (v₀ + k) = ∑' k : ℕ, L v₀ * (1 / q ^ a) ^ k :=
      tsum_congr fun k => L_geom_pow hq hgeom k
    rw [h1, tsum_mul_left, tsum_geometric_of_lt_one hr0 hr1]
    have hne : q ^ a - 1 ≠ 0 := by linarith
    have hqa : (q : ℝ) ^ a ≠ 0 := by positivity
    field_simp
  rw [← hsum.sum_add_tsum_nat_add v₀, ← htail]
  congr 1
  exact tsum_congr fun k => by rw [Nat.add_comm k v₀]

end GeomValue

/-! ## §4 — ★★ THE PER-ENTRY ASSEMBLY: per-depth value data + geometric ratio +
deep-box drain ⟹ the `ZcURLim` of the depth-summed visible pair census at one
convolution-table entry (and the cluster-census form, through VCL's drainage bridge) -/

section EntryAssembly

/-- **The per-depth visible pair-mass family at one table entry** — the normalized
depth-`v` visible pair census of genre `g` at mass split `(n₁, n₂)` and type part
`part` (the conclusion family of VCL's `zcURLim_visDepth_of_clusters`). -/
noncomputable def visEntryFam (g : VisGenre) (n₁ n₂ : ℕ) (σ : FactorizationType)
    (part : Multiset (ℕ × ℕ)) (v : ℕ) :
    ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
      [IsAdicComplete (maximalIdeal O) O] [Finite (ResidueField O)], O → ℕ → ℝ :=
  fun O _ _ _ _ _ π M =>
    ((∑ c ∈ (Set.toFinite (visGenreSet g O π (n₁ + n₂) σ M)).toFinset,
        pairDepthFiber O π (n₁ + n₂) σ M ((n₁, n₂), part) c v : ℕ) : ℝ)
      / ((residueCard O : ℕ) : ℝ) ^ ((n₁ + n₂) * (M + (n₁ + n₂)))

/-- **The per-depth cluster-census family at one table entry** — `q^v` times the
cluster-root count on the genre's visible cells, normalized (the hypothesis family of
VCL's `zcURLim_visDepth_of_clusters`; the carrier lives at the N-free shifted
level). -/
noncomputable def clusterEntryFam (g : VisGenre) (n₁ n₂ : ℕ) (σ : FactorizationType)
    (part : Multiset (ℕ × ℕ)) (v : ℕ) :
    ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
      [IsAdicComplete (maximalIdeal O) O] [Finite (ResidueField O)], O → ℕ → ℝ :=
  fun O _ _ _ _ _ π M =>
    ((residueCard O ^ v
        * ∑ c ∈ (Set.toFinite (visGenreSet g O π (n₁ + n₂) σ M)).toFinset,
            Nat.card ((pairFactor n₁ n₂ (Nat.sub_le (M + (n₁ + n₂)) v)) ''
              (shiftedDepthFiber O π n₁ n₂ ⟨part⟩ ⟨σ.data - part⟩
                (M + (n₁ + n₂)) v c)) : ℕ) : ℝ)
      / ((residueCard O : ℕ) : ℝ) ^ ((n₁ + n₂) * (M + (n₁ + n₂)))

/-- ★ **THE DEEP-BOX DRAIN at mass split `(n₁, n₂)`** — the named analytic input of
the depth-summed census: the normalized level-`(V+2)` deep box at depth `≥ V + 1`
drains as the depth threshold diverges.  Equivalent to the full-box strata masses
summing to `1`; proved OUTRIGHT at `min(n₁, n₂) = 1` in §6 (`deepStratumDrain_one_*`),
open at `2 ≤ min` (the `Σ_v zed·q^{−v} = q^{2n}` identity of GNA's value stack). -/
def DeepStratumDrain (n₁ n₂ : ℕ) : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [IsAdicComplete (maximalIdeal O) O] [Finite (ResidueField O)],
    ∀ π : O, Irreducible π →
      Filter.Tendsto (fun V : ℕ =>
        (Nat.card (depthPairSetGE O π n₁ n₂ (V + 2) (V + 1)) : ℝ)
          / ((residueCard O : ℕ) : ℝ) ^ ((n₁ + n₂) * (V + 2)))
        Filter.atTop (nhds 0)

/-- ★ **The cluster→vis value transfer** (VCL's drainage bridge at the explicit-witness
level): a per-depth value for the CLUSTER census is a per-depth value for the visible
pair-mass census — the gap drains unconditionally
(`tendsto_visDepth_sub_clusters`). -/
theorem zcVal_visEntry_of_clusters {n₁ n₂ : ℕ} (hpos : n₁ ≠ 0 ∨ n₂ ≠ 0)
    (g : VisGenre) (σ : FactorizationType) (part : Multiset (ℕ × ℕ)) (v : ℕ)
    {nn dd : Polynomial ℚ}
    (h : ZcVal (clusterEntryFam g n₁ n₂ σ part v) nn dd) :
    ZcVal (visEntryFam g n₁ n₂ σ part v) nn dd := by
  intro O _ _ _ _ _
  obtain ⟨hne, hlim⟩ := h O
  refine ⟨hne, fun π hπ => ?_⟩
  have hgap := tendsto_visDepth_sub_clusters O hπ n₁ n₂ hpos g σ part v
  have hadd := (hlim π hπ).add hgap
  rw [add_zero] at hadd
  refine hadd.congr fun M => ?_
  simp only [clusterEntryFam, visEntryFam]
  rw [← add_div]
  congr 1
  ring

variable {O : Type*}

/-- ★★ **THE PER-ENTRY DEPTH-SUM ASSEMBLY** (axes 2 + 3 at one table entry): given
per-depth explicit values `(nn v, dd v)` for the visible pair-mass census, the
polynomial-level geometric ratio `X^a · (nn_{v+1}·dd_v) = nn_v·dd_{v+1}` from `v₀`
on, and the deep-box drain, the FULL depth-summed visible pair census at the entry
is a `ZcURLim` — witness `(head) + (nn v₀·X^a) / (dd v₀·(X^a − 1))`, i.e. the finite
head plus the geometric tail, ONE rational function of `q`. -/
theorem zcURLim_visEntry_depthSum {n₁ n₂ : ℕ} (g : VisGenre) (σ : FactorizationType)
    (part : Multiset (ℕ × ℕ)) {nn dd : ℕ → Polynomial ℚ} (hdd : ∀ v, dd v ≠ 0)
    (hval : ∀ v, ZcVal (visEntryFam g n₁ n₂ σ part v) (nn v) (dd v))
    {v₀ a : ℕ} (ha : 1 ≤ a)
    (hgeom : ∀ v, v₀ ≤ v →
      Polynomial.X ^ a * (nn (v + 1) * dd v) = nn v * dd (v + 1))
    (hdrain : DeepStratumDrain n₁ n₂) :
    ZcURLim (fun O _ _ _ _ _ π M =>
      ((∑ v ∈ Finset.range (M + (n₁ + n₂) + 1),
          ∑ c ∈ (Set.toFinite (visGenreSet g O π (n₁ + n₂) σ M)).toFinset,
            pairDepthFiber O π (n₁ + n₂) σ M ((n₁, n₂), part) c v : ℕ) : ℝ)
        / ((residueCard O : ℕ) : ℝ) ^ ((n₁ + n₂) * (M + (n₁ + n₂)))) := by
  -- the finite head is a `ZcURLim` by the per-depth values
  have hhead : ZcURLim (fun O _ _ _ _ _ π M =>
      ∑ v ∈ Finset.range v₀, visEntryFam g n₁ n₂ σ part v O π M) :=
    ZcURLim_sum (Finset.range v₀) _ (fun v _ => (hval v).zcURLim (hdd v))
  -- the geometric tail is a `ZcURLim` with the explicit closed-form witness
  have hXa : (Polynomial.X ^ a - 1 : Polynomial ℚ) ≠ 0 := by
    intro hcon
    have h2 := congrArg (Polynomial.eval (2 : ℚ)) hcon
    rw [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X,
      Polynomial.eval_one, Polynomial.eval_zero, sub_eq_zero] at h2
    have : (1 : ℚ) < 2 ^ a := one_lt_pow₀ (by norm_num) (by omega)
    rw [← h2] at this
    exact absurd this (lt_irrefl _)
  have htailZ : ZcURLim (fun O _ _ _ _ _ π M =>
      ∑ v ∈ Finset.Ico v₀ (M + (n₁ + n₂) + 1),
        visEntryFam g n₁ n₂ σ part v O π M) := by
    refine ⟨nn v₀ * Polynomial.X ^ a, dd v₀ * (Polynomial.X ^ a - 1),
      mul_ne_zero (hdd v₀) hXa, ?_⟩
    intro O _ _ _ _ _
    -- per-O data
    have hq2 : 2 ≤ residueCard O := two_le_residueCard O
    have hQ2 : (2 : ℚ) ≤ ((residueCard O : ℕ) : ℚ) := by exact_mod_cast hq2
    have hq2R : (2 : ℝ) ≤ ((residueCard O : ℕ) : ℝ) := by exact_mod_cast hq2
    have hq0R : (0 : ℝ) < ((residueCard O : ℕ) : ℝ) := by linarith
    have hQa1 : (1 : ℚ) < ((residueCard O : ℕ) : ℚ) ^ a :=
      one_lt_pow₀ (by linarith) (by omega)
    have hQane : ((residueCard O : ℕ) : ℚ) ^ a - 1 ≠ 0 := by linarith
    -- the denominator does not vanish at q
    refine ⟨?_, ?_⟩
    · rw [Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_pow,
        Polynomial.eval_X, Polynomial.eval_one]
      exact mul_ne_zero (hval v₀ O).1 hQane
    intro π hπ
    -- the Tannery interchange for the full depth sum
    have hzero : ∀ M v, M + (n₁ + n₂) < v →
        visEntryFam g n₁ n₂ σ part v O π M = 0 := by
      intro M v hv
      simp only [visEntryFam]
      rw [Finset.sum_eq_zero fun c _ =>
        pairDepthFiber_eq_zero_of_lt π σ M ((n₁, n₂), part) c hv]
      simp
    have hf0 : ∀ v M, 0 ≤ visEntryFam g n₁ n₂ σ part v O π M := by
      intro v M
      simp only [visEntryFam]
      positivity
    have hL : ∀ v, Filter.Tendsto (fun M => visEntryFam g n₁ n₂ σ part v O π M)
        Filter.atTop (nhds (((nn v).eval ((residueCard O : ℕ) : ℚ)
          / (dd v).eval ((residueCard O : ℕ) : ℚ) : ℚ) : ℝ)) :=
      fun v => (hval v O).2 π hπ
    have hpart : ∀ V M, ∑ v ∈ Finset.range (V + 1),
        visEntryFam g n₁ n₂ σ part v O π M ≤ 1 := by
      intro V M
      have hN : ∑ v ∈ Finset.range (V + 1),
          ∑ c ∈ (Set.toFinite (visGenreSet g O π (n₁ + n₂) σ M)).toFinset,
            pairDepthFiber O π (n₁ + n₂) σ M ((n₁, n₂), part) c v
          ≤ residueCard O ^ ((n₁ + n₂) * (M + (n₁ + n₂))) :=
        le_trans (Finset.sum_le_sum fun v _ =>
            sum_pairDepthFiber_le_card_depthPairSet σ part _)
          (sum_card_depthPairSet_le π n₁ n₂ (M + (n₁ + n₂)) V)
      simp only [visEntryFam]
      rw [← Finset.sum_div, ← Nat.cast_sum, div_le_one (by positivity)]
      exact_mod_cast hN
    have htail : ∀ V M, V + 2 ≤ M + (n₁ + n₂) →
        ∑ v ∈ Finset.Ico (V + 1) (M + (n₁ + n₂) + 1),
          visEntryFam g n₁ n₂ σ part v O π M
        ≤ (Nat.card (depthPairSetGE O π n₁ n₂ (V + 2) (V + 1)) : ℝ)
            / ((residueCard O : ℕ) : ℝ) ^ ((n₁ + n₂) * (V + 2)) := by
      intro V M hVM
      have hN := sum_pairDepthFiber_vis_tail_le hπ hVM σ part
        (Set.toFinite (visGenreSet g O π (n₁ + n₂) σ M)).toFinset
      have hexp : (n₁ + n₂) * (V + 2) + (n₁ + n₂) * (M + (n₁ + n₂) - (V + 2))
          = (n₁ + n₂) * (M + (n₁ + n₂)) := by
        rw [← Nat.mul_add, Nat.add_sub_cancel' hVM]
      simp only [visEntryFam]
      rw [← Finset.sum_div, ← Nat.cast_sum]
      calc ((∑ v ∈ Finset.Ico (V + 1) (M + (n₁ + n₂) + 1),
              ∑ c ∈ (Set.toFinite (visGenreSet g O π (n₁ + n₂) σ M)).toFinset,
                pairDepthFiber O π (n₁ + n₂) σ M ((n₁, n₂), part) c v : ℕ) : ℝ)
            / ((residueCard O : ℕ) : ℝ) ^ ((n₁ + n₂) * (M + (n₁ + n₂)))
          ≤ ((Nat.card (depthPairSetGE O π n₁ n₂ (V + 2) (V + 1))
                * residueCard O ^ ((n₁ + n₂) * (M + (n₁ + n₂) - (V + 2))) : ℕ) : ℝ)
              / ((residueCard O : ℕ) : ℝ) ^ ((n₁ + n₂) * (M + (n₁ + n₂))) := by
            gcongr
        _ = (Nat.card (depthPairSetGE O π n₁ n₂ (V + 2) (V + 1)) : ℝ)
              / ((residueCard O : ℕ) : ℝ) ^ ((n₁ + n₂) * (V + 2)) := by
            rw [← hexp, pow_add]
            push_cast
            rw [mul_div_mul_right _ _ (by positivity :
              ((residueCard O : ℕ) : ℝ) ^ ((n₁ + n₂) * (M + (n₁ + n₂) - (V + 2))) ≠ 0)]
    obtain ⟨hsum, htot⟩ := tendsto_depthSum_of_env (m := n₁ + n₂)
      (L := fun v => (((nn v).eval ((residueCard O : ℕ) : ℚ)
        / (dd v).eval ((residueCard O : ℕ) : ℚ) : ℚ) : ℝ))
      hf0 hL hpart htail (hdrain O π hπ)
    -- the limits are eventually geometric
    have hLgeom : ∀ v, v₀ ≤ v →
        (((nn (v + 1)).eval ((residueCard O : ℕ) : ℚ)
          / (dd (v + 1)).eval ((residueCard O : ℕ) : ℚ) : ℚ) : ℝ)
        = (((nn v).eval ((residueCard O : ℕ) : ℚ)
            / (dd v).eval ((residueCard O : ℕ) : ℚ) : ℚ) : ℝ)
          / ((residueCard O : ℕ) : ℝ) ^ a := by
      intro v hv
      have hpoly := congrArg (Polynomial.eval ((residueCard O : ℕ) : ℚ)) (hgeom v hv)
      rw [Polynomial.eval_mul, Polynomial.eval_mul, Polynomial.eval_mul,
        Polynomial.eval_pow, Polynomial.eval_X] at hpoly
      have hddv : (dd v).eval ((residueCard O : ℕ) : ℚ) ≠ 0 := (hval v O).1
      have hddv1 : (dd (v + 1)).eval ((residueCard O : ℕ) : ℚ) ≠ 0 :=
        (hval (v + 1) O).1
      have hQ0 : ((residueCard O : ℕ) : ℚ) ≠ 0 := by linarith
      have hq : (nn (v + 1)).eval ((residueCard O : ℕ) : ℚ)
            / (dd (v + 1)).eval ((residueCard O : ℕ) : ℚ)
          = (nn v).eval ((residueCard O : ℕ) : ℚ)
              / (dd v).eval ((residueCard O : ℕ) : ℚ)
            / ((residueCard O : ℕ) : ℚ) ^ a := by
        rw [div_div]
        rw [div_eq_div_iff hddv1 (by positivity)]
        linear_combination hpoly
      rw [hq]
      push_cast
      ring
    -- the geometric closed form of the summed value
    have htsum := tsum_of_geom_ratio hq2R hsum ha hLgeom
    -- the tail family converges to the geometric tail value
    have hheadT : Filter.Tendsto
        (fun M => ∑ v ∈ Finset.range v₀, visEntryFam g n₁ n₂ σ part v O π M)
        Filter.atTop (nhds (∑ v ∈ Finset.range v₀,
          (((nn v).eval ((residueCard O : ℕ) : ℚ)
            / (dd v).eval ((residueCard O : ℕ) : ℚ) : ℚ) : ℝ))) :=
      tendsto_finsetSum _ fun v _ => hL v
    have hpoint : ∀ M, ∑ v ∈ Finset.Ico v₀ (M + (n₁ + n₂) + 1),
          visEntryFam g n₁ n₂ σ part v O π M
        = (∑ v ∈ Finset.range (M + (n₁ + n₂) + 1),
            visEntryFam g n₁ n₂ σ part v O π M)
          - ∑ v ∈ Finset.range v₀, visEntryFam g n₁ n₂ σ part v O π M := by
      intro M
      rw [sum_range_split (fun v => visEntryFam g n₁ n₂ σ part v O π M)
        (fun v hv => hzero M v hv)]
      ring
    have htailT := (htot.sub hheadT).congr fun M => (hpoint M).symm
    -- identify the limit with the witness value
    have hvalue : (∑' v, (((nn v).eval ((residueCard O : ℕ) : ℚ)
          / (dd v).eval ((residueCard O : ℕ) : ℚ) : ℚ) : ℝ))
        - (∑ v ∈ Finset.range v₀,
            (((nn v).eval ((residueCard O : ℕ) : ℚ)
              / (dd v).eval ((residueCard O : ℕ) : ℚ) : ℚ) : ℝ))
        = (((nn v₀ * Polynomial.X ^ a).eval ((residueCard O : ℕ) : ℚ)
            / (dd v₀ * (Polynomial.X ^ a - 1)).eval ((residueCard O : ℕ) : ℚ)
            : ℚ) : ℝ) := by
      rw [htsum]
      rw [Polynomial.eval_mul, Polynomial.eval_mul, Polynomial.eval_sub,
        Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_one]
      have hddv₀ : (dd v₀).eval ((residueCard O : ℕ) : ℚ) ≠ 0 := (hval v₀ O).1
      have hQaR : (1 : ℝ) < ((residueCard O : ℕ) : ℝ) ^ a := by
        exact_mod_cast hQa1
      have hQaneR : ((residueCard O : ℕ) : ℝ) ^ a - 1 ≠ 0 := by linarith
      have hddv₀R : (((dd v₀).eval ((residueCard O : ℕ) : ℚ) : ℚ) : ℝ) ≠ 0 := by
        exact_mod_cast hddv₀
      push_cast
      field_simp
      ring
    rw [← hvalue]
    exact htailT
  -- combine head and tail into the full depth sum
  refine (hhead.add htailZ).congr ?_
  intro O _ _ _ _ _ π hπ M
  have hzero : ∀ v, M + (n₁ + n₂) < v →
      visEntryFam g n₁ n₂ σ part v O π M = 0 := by
    intro v hv
    simp only [visEntryFam]
    rw [Finset.sum_eq_zero fun c _ =>
      pairDepthFiber_eq_zero_of_lt π σ M ((n₁, n₂), part) c hv]
    simp
  rw [← sum_range_split (fun v => visEntryFam g n₁ n₂ σ part v O π M) hzero]
  simp only [visEntryFam]
  rw [← Finset.sum_div, ← Nat.cast_sum]

end EntryAssembly

/-! ## §5 — ★ THE DRAIN FIRES AT `min = 1`: through IGV's exact law the deep box is
the exact geometric `q^{−w}`, so `DeepStratumDrain` holds OUTRIGHT at every mass
split touching mass 1 -/

section DrainFires

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)]

/-- The ℕ-telescope of the geometric census values: partial sums of
`(q−1)·q^{K−v−1}` complement the deep box exactly (stated additively — no
truncated subtraction anywhere). -/
private theorem sum_geom_nat {q : ℕ} (hq : 1 ≤ q) (K : ℕ) {w : ℕ} (hw : w ≤ K) :
    ∑ v ∈ Finset.range w, (q - 1) * q ^ (K - v - 1) + q ^ (K - w) = q ^ K := by
  induction w with
  | zero => simp
  | succ w ih =>
      have hwK : w ≤ K := by omega
      have hstep : (q - 1) * q ^ (K - w - 1) + q ^ (K - (w + 1)) = q ^ (K - w) := by
        have hsub : K - (w + 1) = K - w - 1 := by omega
        have hpow : q * q ^ (K - w - 1) = q ^ (K - w) := by
          rw [← pow_succ']
          congr 1
          omega
        rw [hsub, ← hpow, Nat.sub_mul, one_mul]
        have hle : q ^ (K - w - 1) ≤ q * q ^ (K - w - 1) :=
          Nat.le_mul_of_pos_left _ (by omega)
        omega
      rw [Finset.sum_range_succ, add_assoc, hstep]
      exact ih hwK

/-- ★ **THE `min = 1` DEEP BOX, EXACT** (right form): at mass split `(1, n₂)` the
depth-`≥ w` box at level `L` counts EXACTLY `q^{(1+n₂)L − w}` — normalized mass
`q^{−w}`, the exact geometric envelope (IGV's `min = 1` law summed through the
telescope; additively, no subtraction). -/
theorem card_depthPairSetGE_one_right {π : O} (hπ : Irreducible π) {n₂ : ℕ}
    (hn : 1 ≤ n₂) {L w : ℕ} (hw : w ≤ L) :
    Nat.card (depthPairSetGE O π 1 n₂ L w)
      = residueCard O ^ ((1 + n₂) * L - w) := by
  have hq : 1 ≤ residueCard O := residueCard_pos O
  have hwK : w ≤ (1 + n₂) * L := le_trans hw (Nat.le_mul_of_pos_left L (by omega))
  -- the box partition: head strata + deep box = full box
  have hpartition : ∑ v ∈ Finset.range w, Nat.card (depthPairSet O π 1 n₂ L v)
      + Nat.card (depthPairSetGE O π 1 n₂ L w)
      = residueCard O ^ ((1 + n₂) * L) := by
    rw [card_depthPairSetGE_eq_sum π,
      Finset.sum_range_add_sum_Ico _ (by omega : w ≤ L + 1)]
    exact sum_card_depthPairSet_eq π 1 n₂ L
  -- the head strata carry IGV's exact values
  have hvalues : ∑ v ∈ Finset.range w, Nat.card (depthPairSet O π 1 n₂ L v)
      = ∑ v ∈ Finset.range w,
          (residueCard O - 1) * residueCard O ^ ((1 + n₂) * L - v - 1) :=
    Finset.sum_congr rfl fun v hv =>
      card_depthPairSet_one_right hπ hn (lt_of_lt_of_le (Finset.mem_range.mp hv) hw)
  have htele := sum_geom_nat hq ((1 + n₂) * L) hwK
  omega

/-- The deep boxes are symmetric in the mass split (`mixDepth_swap`). -/
theorem card_depthPairSetGE_swap (π : O) (n₁ n₂ L w : ℕ) :
    Nat.card (depthPairSetGE O π n₁ n₂ L w)
      = Nat.card (depthPairSetGE O π n₂ n₁ L w) := by
  refine Nat.card_congr (Equiv.subtypeEquiv
    (Equiv.prodComm (Coeff O n₁ L) (Coeff O n₂ L)) ?_)
  rintro ⟨c₁, c₂⟩
  show w ≤ mixDepth π c₁ c₂ ↔ w ≤ mixDepth π c₂ c₁
  rw [mixDepth_swap]

end DrainFires

section DrainFiresGlobal

/-- ★ **THE DRAIN FIRES at `(1, n₂)`**: the deep-box envelope is the exact geometric
`q^{−(V+1)}`, which drains — `DeepStratumDrain 1 n₂` holds OUTRIGHT. -/
theorem deepStratumDrain_one_right (n₂ : ℕ) (hn : 1 ≤ n₂) : DeepStratumDrain 1 n₂ := by
  intro O _ _ _ _ _ π hπ
  have hq2 : 2 ≤ residueCard O := two_le_residueCard O
  have hq2R : (2 : ℝ) ≤ ((residueCard O : ℕ) : ℝ) := by exact_mod_cast hq2
  have hq0R : (0 : ℝ) < ((residueCard O : ℕ) : ℝ) := by linarith
  have hfun : ∀ V : ℕ,
      (Nat.card (depthPairSetGE O π 1 n₂ (V + 2) (V + 1)) : ℝ)
          / ((residueCard O : ℕ) : ℝ) ^ ((1 + n₂) * (V + 2))
        = (1 / ((residueCard O : ℕ) : ℝ)) ^ (V + 1) := by
    intro V
    have hw : V + 1 ≤ V + 2 := by omega
    have hwK : V + 1 ≤ (1 + n₂) * (V + 2) :=
      le_trans hw (Nat.le_mul_of_pos_left _ (by omega))
    rw [card_depthPairSetGE_one_right hπ hn hw]
    have hexp : (1 + n₂) * (V + 2) - (V + 1) + (V + 1) = (1 + n₂) * (V + 2) :=
      Nat.sub_add_cancel hwK
    rw [div_pow, one_pow, div_eq_div_iff (by positivity) (by positivity)]
    push_cast
    rw [one_mul, ← pow_add, hexp]
  have hlim : Filter.Tendsto (fun V : ℕ => (1 / ((residueCard O : ℕ) : ℝ)) ^ (V + 1))
      Filter.atTop (nhds 0) := by
    have h0 : (0 : ℝ) ≤ 1 / ((residueCard O : ℕ) : ℝ) := by positivity
    have h1 : 1 / ((residueCard O : ℕ) : ℝ) < 1 := by
      rw [div_lt_one hq0R]
      linarith
    exact (tendsto_pow_atTop_nhds_zero_of_lt_one h0 h1).comp (tendsto_add_atTop_nat 1)
  exact hlim.congr fun V => (hfun V).symm

/-- ★ The drain, left form (`(n₁, 1)`), via the deep-box swap. -/
theorem deepStratumDrain_one_left (n₁ : ℕ) (hn : 1 ≤ n₁) : DeepStratumDrain n₁ 1 := by
  intro O _ _ _ _ _ π hπ
  have h := deepStratumDrain_one_right n₁ hn O π hπ
  refine h.congr fun V => ?_
  rw [card_depthPairSetGE_swap, Nat.add_comm 1 n₁]

/-- **The drain at every mass split touching `1`** — the packaging consumed by the
genre assembly: only `2 ≤ min(n₁, n₂)` splits need the drain hypothesis. -/
theorem deepStratumDrain_of_min_two {n₁ n₂ : ℕ} (h₁ : 0 < n₁) (h₂ : 0 < n₂)
    (hdrain : 2 ≤ n₁ → 2 ≤ n₂ → DeepStratumDrain n₁ n₂) :
    DeepStratumDrain n₁ n₂ := by
  rcases Nat.lt_or_ge n₁ 2 with hl | hge₁
  · have h1 : n₁ = 1 := by omega
    subst h1
    exact deepStratumDrain_one_right n₂ h₂
  rcases Nat.lt_or_ge n₂ 2 with hl | hge₂
  · have h2 : n₂ = 1 := by omega
    subst h2
    exact deepStratumDrain_one_left n₁ h₁
  · exact hdrain hge₁ hge₂

end DrainFiresGlobal

/-! ## §6 — ★★★ THE GENRE ASSEMBLY AND THE ROW RE-BASED: the weight censuses from
per-entry geometric value data, and `VisCensusLaw` from cluster values + drains +
collisions -/

section GenreAssembly

/-- **The bundled per-entry value data** (vis-mass form): explicit per-depth witness
polynomials with the polynomial-level geometric ratio from some `v₀` on. -/
def VisEntryGeom (g : VisGenre) (n₁ n₂ : ℕ) (σ : FactorizationType)
    (part : Multiset (ℕ × ℕ)) : Prop :=
  ∃ (nn dd : ℕ → Polynomial ℚ) (v₀ a : ℕ), 1 ≤ a ∧ (∀ v, dd v ≠ 0) ∧
    (∀ v, ZcVal (visEntryFam g n₁ n₂ σ part v) (nn v) (dd v)) ∧
    ∀ v, v₀ ≤ v → Polynomial.X ^ a * (nn (v + 1) * dd v) = nn v * dd (v + 1)

/-- **The bundled per-entry value data** (CLUSTER form — the canonical re-base
currency per VCL's fence: the carrier lives at the N-free shifted level). -/
def VisEntryClusterGeom (g : VisGenre) (n₁ n₂ : ℕ) (σ : FactorizationType)
    (part : Multiset (ℕ × ℕ)) : Prop :=
  ∃ (nn dd : ℕ → Polynomial ℚ) (v₀ a : ℕ), 1 ≤ a ∧ (∀ v, dd v ≠ 0) ∧
    (∀ v, ZcVal (clusterEntryFam g n₁ n₂ σ part v) (nn v) (dd v)) ∧
    ∀ v, v₀ ≤ v → Polynomial.X ^ a * (nn (v + 1) * dd v) = nn v * dd (v + 1)

/-- ★ Cluster value data transfers to vis-mass value data (the drainage bridge,
bundled). -/
theorem visEntryGeom_of_cluster {g : VisGenre} {n₁ n₂ : ℕ} {σ : FactorizationType}
    {part : Multiset (ℕ × ℕ)} (hpos : n₁ ≠ 0 ∨ n₂ ≠ 0)
    (h : VisEntryClusterGeom g n₁ n₂ σ part) : VisEntryGeom g n₁ n₂ σ part := by
  obtain ⟨nn, dd, v₀, a, ha, hdd, hval, hgeom⟩ := h
  exact ⟨nn, dd, v₀, a, ha, hdd,
    fun v => zcVal_visEntry_of_clusters hpos g σ part v (hval v), hgeom⟩

/-- ★★★ **THE GENRE WEIGHT CENSUS from per-entry geometric data** — genre-uniform:
per-entry bundled values at every admissible mass split and type part, plus the
`min ≥ 2` deep-box drains (the `min = 1` drains are §5's fires), give the `ZcURLim`
of the genre's full multiplicity-weighted visible census. -/
theorem zcURLim_visWeight_of_entryGeom (g : VisGenre) {m : ℕ} (σ : FactorizationType)
    (hentry : ∀ n₁ n₂ : ℕ, ∀ part : Multiset (ℕ × ℕ), 0 < n₁ → 0 < n₂ →
      n₁ + n₂ = m → part ∈ σ.data.powerset.toFinset → VisEntryGeom g n₁ n₂ σ part)
    (hdrain : ∀ n₁ n₂ : ℕ, n₁ + n₂ = m → 2 ≤ n₁ → 2 ≤ n₂ → DeepStratumDrain n₁ n₂) :
    ZcURLim (fun O _ _ _ _ _ π M =>
      ((∑ c ∈ (Set.toFinite (visGenreSet g O π m σ M)).toFinset,
          multCount O m σ M c : ℕ) : ℝ)
        / ((residueCard O : ℕ) : ℝ) ^ (m * (M + m))) := by
  -- each table entry's depth-summed census is a `ZcURLim`
  have hentryZ : ∀ p ∈ convPairs m σ, ZcURLim (fun O _ _ _ _ _ π M =>
      ((∑ v ∈ Finset.range (M + m + 1),
          ∑ c ∈ (Set.toFinite (visGenreSet g O π m σ M)).toFinset,
            pairDepthFiber O π m σ M p c v : ℕ) : ℝ)
        / ((residueCard O : ℕ) : ℝ) ^ (m * (M + m))) := by
    rintro ⟨⟨n₁, n₂⟩, part⟩ hp
    obtain ⟨hp1, hp2⟩ := Finset.mem_product.mp hp
    obtain ⟨-, hsum, hpos1, hpos2⟩ := Finset.mem_filter.mp hp1
    subst hsum
    obtain ⟨nn, dd, v₀, a, ha, hdd, hval, hgeom⟩ :=
      hentry n₁ n₂ part hpos1 hpos2 rfl hp2
    exact zcURLim_visEntry_depthSum g σ part hdd hval ha hgeom
      (deepStratumDrain_of_min_two hpos1 hpos2 (hdrain n₁ n₂ rfl))
  -- sum the table and identify with the weight census
  refine (ZcURLim_sum (convPairs m σ) _ hentryZ).congr ?_
  intro O _ _ _ _ _ π hπ M
  rw [← Finset.sum_div, ← Nat.cast_sum]
  refine congrArg (fun x : ℕ =>
    (x : ℝ) / ((residueCard O : ℕ) : ℝ) ^ (m * (M + m))) ?_
  calc ∑ p ∈ convPairs m σ, ∑ v ∈ Finset.range (M + m + 1),
        ∑ c ∈ (Set.toFinite (visGenreSet g O π m σ M)).toFinset,
          pairDepthFiber O π m σ M p c v
      = ∑ v ∈ Finset.range (M + m + 1), ∑ p ∈ convPairs m σ,
          ∑ c ∈ (Set.toFinite (visGenreSet g O π m σ M)).toFinset,
            pairDepthFiber O π m σ M p c v := Finset.sum_comm
    _ = ∑ v ∈ Finset.range (M + m + 1),
          ∑ c ∈ (Set.toFinite (visGenreSet g O π m σ M)).toFinset,
            ∑ p ∈ convPairs m σ, pairDepthFiber O π m σ M p c v :=
        Finset.sum_congr rfl fun v _ => Finset.sum_comm
    _ = ∑ v ∈ Finset.range (M + m + 1), visDepthMass g O π m σ M v := by
        simp only [visDepthMass]
    _ = ∑ c ∈ (Set.toFinite (visGenreSet g O π m σ M)).toFinset,
          multCount O m σ M c :=
        (sum_multCount_eq_sum_visDepthMass g π m σ M).symm

/-- ★★ **`VisWeightLaw` from per-entry geometric data** (the split instance). -/
theorem visWeightLaw_of_entryGeom {m : ℕ} (σ : FactorizationType)
    (hentry : ∀ n₁ n₂ : ℕ, ∀ part : Multiset (ℕ × ℕ), 0 < n₁ → 0 < n₂ →
      n₁ + n₂ = m → part ∈ σ.data.powerset.toFinset →
        VisEntryGeom .split n₁ n₂ σ part)
    (hdrain : ∀ n₁ n₂ : ℕ, n₁ + n₂ = m → 2 ≤ n₁ → 2 ≤ n₂ → DeepStratumDrain n₁ n₂) :
    VisWeightLaw m σ :=
  zcURLim_visWeight_of_entryGeom .split σ hentry hdrain

/-- ★★ **`PowerVisWeightLaw` from per-entry geometric data** (the power instance). -/
theorem powerVisWeightLaw_of_entryGeom {m : ℕ} (σ : FactorizationType)
    (hentry : ∀ n₁ n₂ : ℕ, ∀ part : Multiset (ℕ × ℕ), 0 < n₁ → 0 < n₂ →
      n₁ + n₂ = m → part ∈ σ.data.powerset.toFinset →
        VisEntryGeom .power n₁ n₂ σ part)
    (hdrain : ∀ n₁ n₂ : ℕ, n₁ + n₂ = m → 2 ≤ n₁ → 2 ≤ n₂ → DeepStratumDrain n₁ n₂) :
    PowerVisWeightLaw m σ :=
  zcURLim_visWeight_of_entryGeom .power σ hentry hdrain

/-- ★★★ **THE UNIFIED CENSUS FROM GEOMETRIC VALUES + COLLISIONS** (vis-mass form):
the master's convolution premise `∀ g, VisCensusLaw g m σ` rests on {per-entry
geometric value data for both genres, the `min ≥ 2` deep-box drains, the two
collision limits} — the analytic axes (2: summed rationality, 3: assembly) are
CLOSED. -/
theorem visCensusLaw_of_entryGeom_collisions {m : ℕ} (hm : 0 < m)
    (σ : FactorizationType)
    (hentry : ∀ g : VisGenre, ∀ n₁ n₂ : ℕ, ∀ part : Multiset (ℕ × ℕ),
      0 < n₁ → 0 < n₂ → n₁ + n₂ = m → part ∈ σ.data.powerset.toFinset →
        VisEntryGeom g n₁ n₂ σ part)
    (hdrain : ∀ n₁ n₂ : ℕ, n₁ + n₂ = m → 2 ≤ n₁ → 2 ≤ n₂ → DeepStratumDrain n₁ n₂)
    (hC : CollisionLaw m σ)
    (hPC : ZcURLim (fun O _ _ _ _ _ π M =>
      (powerCollisionTotal O π m σ M : ℝ)
        / ((residueCard O : ℕ) : ℝ) ^ (m * (M + m)))) :
    ∀ g, VisCensusLaw g m σ :=
  visCensusLaw_of_weights_collisions hm σ
    (visWeightLaw_of_entryGeom σ (hentry .split) hdrain) hC
    (powerVisWeightLaw_of_entryGeom σ (hentry .power) hdrain) hPC

/-- ★★★ **THE CONVOLUTION ROW'S NEW BASE** (CLUSTER form — the headline): after this
file, `VisCensusLaw g m σ` at EVERY mass and type, both genres, rests on exactly

  {per-entry geometric CLUSTER census values (`VisEntryClusterGeom`),
   the `min ≥ 2` deep-box drains (`DeepStratumDrain`),
   the two collision limits (`CollisionLaw` + the power collision `ZcURLim`)}.

The depth summation, its rationality, the `q^v`-cluster correction, and the deep
tail are no longer remainders. -/
theorem visCensusLaw_of_clusterGeom_collisions {m : ℕ} (hm : 0 < m)
    (σ : FactorizationType)
    (hentry : ∀ g : VisGenre, ∀ n₁ n₂ : ℕ, ∀ part : Multiset (ℕ × ℕ),
      0 < n₁ → 0 < n₂ → n₁ + n₂ = m → part ∈ σ.data.powerset.toFinset →
        VisEntryClusterGeom g n₁ n₂ σ part)
    (hdrain : ∀ n₁ n₂ : ℕ, n₁ + n₂ = m → 2 ≤ n₁ → 2 ≤ n₂ → DeepStratumDrain n₁ n₂)
    (hC : CollisionLaw m σ)
    (hPC : ZcURLim (fun O _ _ _ _ _ π M =>
      (powerCollisionTotal O π m σ M : ℝ)
        / ((residueCard O : ℕ) : ℝ) ^ (m * (M + m)))) :
    ∀ g, VisCensusLaw g m σ :=
  visCensusLaw_of_entryGeom_collisions hm σ
    (fun g n₁ n₂ part h₁ h₂ hsum hpart =>
      visEntryGeom_of_cluster (Or.inl (Nat.pos_iff_ne_zero.mp h₁))
        (hentry g n₁ n₂ part h₁ h₂ hsum hpart))
    hdrain hC hPC

end GenreAssembly

/-! ## §7 — ★★★ THE MASTERS RECOMPUTED: the convolution row's premise replaced by
{geometric cluster values, `min ≥ 2` drains, collision limits}; every other row
byte-identical to VCL's masters -/

section Masters

open Uniformity.Density.IFCG58 (splitConvolutionDefectLaw_of_visCensus
  powerConvolutionDefectLaw_of_visCensus)

/-- ★★★ **THE CENSUS MASTER, CONVOLUTION ROW RE-BASED ONTO THE CLUSTER VALUES**: VCL's
`decidedSliceAt_all_of_visCensus''` with the unified-census premise replaced by
{per-entry geometric CLUSTER value data (row-guarded), the GLOBAL `min ≥ 2` deep-box
drains (σ-free!), the two collision limits (row-guarded)}.  The all-degree decided
slice now rests on {cluster values + drains + collisions, `PowerFullSpanLaw`,
`LeafSubfaceLaw` at non-singleton σ, the `e = 4` remainder laws}. -/
theorem decidedSliceAt_all_of_clusterGeom
    (hCG : ∀ e : ℕ, 5 ≤ e →
      (∀ k, k < e → ∀ σ' : FactorizationType, σ'.degree = k → DecidedValueLaw k σ') →
      ∀ σ : FactorizationType, σ.degree = e → Witnessed e σ →
        (∃ p ∈ σ.data, p.1 ≠ 1) → 2 ≤ Multiset.card σ.data →
        ∀ g : VisGenre, ∀ n₁ n₂ : ℕ, ∀ part : Multiset (ℕ × ℕ),
          0 < n₁ → 0 < n₂ → n₁ + n₂ = e → part ∈ σ.data.powerset.toFinset →
            VisEntryClusterGeom g n₁ n₂ σ part)
    (hDR : ∀ n₁ n₂ : ℕ, 2 ≤ n₁ → 2 ≤ n₂ → DeepStratumDrain n₁ n₂)
    (hCL : ∀ e : ℕ, 5 ≤ e →
      (∀ k, k < e → ∀ σ' : FactorizationType, σ'.degree = k → DecidedValueLaw k σ') →
      ∀ σ : FactorizationType, σ.degree = e → Witnessed e σ →
        (∃ p ∈ σ.data, p.1 ≠ 1) → 2 ≤ Multiset.card σ.data → CollisionLaw e σ)
    (hPCL : ∀ e : ℕ, 5 ≤ e →
      (∀ k, k < e → ∀ σ' : FactorizationType, σ'.degree = k → DecidedValueLaw k σ') →
      ∀ σ : FactorizationType, σ.degree = e → Witnessed e σ →
        (∃ p ∈ σ.data, p.1 ≠ 1) → 2 ≤ Multiset.card σ.data →
        ZcURLim (fun O _ _ _ _ _ π M =>
          (powerCollisionTotal O π e σ M : ℝ)
            / ((residueCard O : ℕ) : ℝ) ^ (e * (M + e))))
    (hPF : ∀ e : ℕ, 5 ≤ e →
      (∀ k, k < e → ∀ σ' : FactorizationType, σ'.degree = k → DecidedValueLaw k σ') →
      ∀ σ : FactorizationType, σ.degree = e → Witnessed e σ →
        (∃ p ∈ σ.data, p.1 ≠ 1) → PowerFullSpanLaw e σ)
    (hLeafSub : ∀ e : ℕ, 5 ≤ e →
      (∀ k, k < e → ∀ σ' : FactorizationType, σ'.degree = k → DecidedValueLaw k σ') →
      ∀ σ : FactorizationType, σ.degree = e → Witnessed e σ →
        (∃ p ∈ σ.data, p.1 ≠ 1) → 2 ≤ Multiset.card σ.data → LeafSubfaceLaw e σ)
    (hR4 : ∀ σ : FactorizationType, σ.degree = 4 → Witnessed 4 σ →
      (∃ p ∈ σ.data, 2 ∣ p.1) → ConeRemainderLaw 4 σ) :
    ∀ n : ℕ, Uniformity.Density.DecidedSliceAt n :=
  Uniformity.Density.IFCG60.decidedSliceAt_all_of_visCensus''
    (fun e he hsm σ hσ hwit hram hcard =>
      visCensusLaw_of_clusterGeom_collisions (by omega) σ
        (hCG e he hsm σ hσ hwit hram hcard)
        (fun n₁ n₂ _ h₁ h₂ => hDR n₁ n₂ h₁ h₂)
        (hCL e he hsm σ hσ hwit hram hcard)
        (hPCL e he hsm σ hσ hwit hram hcard))
    hPF hLeafSub hR4

universe uW uG uKt uL

/-- ★★★ **THE CAPSTONE MASTER, CONVOLUTION ROWS RE-BASED ONTO THE CLUSTER VALUES**:
VCL's `capstoneHypotheses_of_MASTER'''` with BOTH convolution-defect premises
discharged from {cluster values, drains, collisions} through the `< e` value laws
(ID12's honesty frame applies verbatim). -/
theorem capstoneHypotheses_of_clusterGeom (n : ℕ)
    (hladder : ∀ (O : Type) [CommRing O] (K : Type) [Field K]
      (C : Ladder.SlotCarrier O K) (B : Ladder.BlockData C)
      (G : Type uG) [CommGroup G] (Kt : Type uKt) [Field Kt] (L : Type uL) [Field L]
      [Algebra Kt L] (N : Gauge.NormSection G) (v : ℕ → (G →* Multiplicative ℤ))
      (ρ : ∀ j : ℕ, MonoidHom.ker (v j) →* Lˣ) (q : ℕ → ℤ),
      CanonicalLadderConfig C B G Kt L N v ρ q n →
      Uniformity.Density.IFC5.LadderSupplyLive₃.{uW, uG, uKt, uL}
        C B G Kt L N v ρ q n)
    (hdeepTwist : ∀ (O : Type) [CommRing O] (K : Type) [Field K]
      (C : Ladder.SlotCarrier O K) (B : Ladder.BlockData C)
      (G : Type uG) [CommGroup G] (Kt : Type uKt) [Field Kt] (L : Type uL) [Field L]
      [Algebra Kt L] (N : Gauge.NormSection G) (v : ℕ → (G →* Multiplicative ℤ))
      (ρ : ∀ j : ℕ, MonoidHom.ker (v j) →* Lˣ) (q : ℕ → ℤ)
      (A : ℕ → Gauge.GaugeArena G Kt N) (R : ℕ → G → Kt) (w : ℕ → Ktˣ) (r : ℕ),
      CanonicalDeepTwistConfig C B G Kt L N v ρ q A R w r n →
      Ladder.DeepTwistConjunctLive r v ρ q A R w)
    (hFC : ∀ D : ℕ, 2 ≤ D → FactorCorrespondenceAt D)
    (hEis : ∀ m : ℕ, 6 ≤ m → ¬ m.Prime →
      (∀ k, k < m → ∀ σ' : FactorizationType, σ'.degree = k → DecidedValueLaw k σ') →
      ∀ σ : FactorizationType, σ.degree = m → Witnessed m σ →
        (∃ p ∈ σ.data, p.1 ≠ 1) → EisFullSpanRemainderLaw m σ)
    (hCG : ∀ e : ℕ, 5 ≤ e →
      (∀ k, k < e → ∀ σ' : FactorizationType, σ'.degree = k → DecidedValueLaw k σ') →
      ∀ σ : FactorizationType, σ.degree = e → Witnessed e σ →
        (∃ p ∈ σ.data, p.1 ≠ 1) → 2 ≤ Multiset.card σ.data →
        ∀ g : VisGenre, ∀ n₁ n₂ : ℕ, ∀ part : Multiset (ℕ × ℕ),
          0 < n₁ → 0 < n₂ → n₁ + n₂ = e → part ∈ σ.data.powerset.toFinset →
            VisEntryClusterGeom g n₁ n₂ σ part)
    (hDR : ∀ n₁ n₂ : ℕ, 2 ≤ n₁ → 2 ≤ n₂ → DeepStratumDrain n₁ n₂)
    (hCL : ∀ e : ℕ, 5 ≤ e →
      (∀ k, k < e → ∀ σ' : FactorizationType, σ'.degree = k → DecidedValueLaw k σ') →
      ∀ σ : FactorizationType, σ.degree = e → Witnessed e σ →
        (∃ p ∈ σ.data, p.1 ≠ 1) → 2 ≤ Multiset.card σ.data → CollisionLaw e σ)
    (hPCL : ∀ e : ℕ, 5 ≤ e →
      (∀ k, k < e → ∀ σ' : FactorizationType, σ'.degree = k → DecidedValueLaw k σ') →
      ∀ σ : FactorizationType, σ.degree = e → Witnessed e σ →
        (∃ p ∈ σ.data, p.1 ≠ 1) → 2 ≤ Multiset.card σ.data →
        ZcURLim (fun O _ _ _ _ _ π M =>
          (powerCollisionTotal O π e σ M : ℝ)
            / ((residueCard O : ℕ) : ℝ) ^ (e * (M + e))))
    (hLeafSub : ∀ e : ℕ, 5 ≤ e →
      (∀ k, k < e → ∀ σ' : FactorizationType, σ'.degree = k → DecidedValueLaw k σ') →
      ∀ σ : FactorizationType, σ.degree = e → Witnessed e σ →
        (∃ p ∈ σ.data, p.1 ≠ 1) → 2 ≤ Multiset.card σ.data → LeafSubfaceLaw e σ) :
    CapstoneHypotheses.{uW, uG, uKt, uL} n :=
  Uniformity.Density.IFCG60.capstoneHypotheses_of_MASTER''' n hladder hdeepTwist hFC
    hEis
    (fun e he hsm σ hσ hwit hram hcard =>
      splitConvolutionDefectLaw_of_visCensus σ hsm
        (visCensusLaw_of_clusterGeom_collisions (by omega) σ
          (hCG e he hsm σ hσ hwit hram hcard)
          (fun n₁ n₂ _ h₁ h₂ => hDR n₁ n₂ h₁ h₂)
          (hCL e he hsm σ hσ hwit hram hcard)
          (hPCL e he hsm σ hσ hwit hram hcard)))
    (fun e he hsm σ hσ hwit hram hcard =>
      powerConvolutionDefectLaw_of_visCensus σ hsm
        (visCensusLaw_of_clusterGeom_collisions (by omega) σ
          (hCG e he hsm σ hσ hwit hram hcard)
          (fun n₁ n₂ _ h₁ h₂ => hDR n₁ n₂ h₁ h₂)
          (hCL e he hsm σ hσ hwit hram hcard)
          (hPCL e he hsm σ hσ hwit hram hcard)))
    hLeafSub

end Masters

end Uniformity.Density.IFCG71

end

/-! ## AXCHECK FOOTER — §§1–5 (the domination/envelope layer, the Tannery
instrument, the geometric-tail value, the per-entry assembly, the drain fires)
expect PURE Lean core `{propext, Classical.choice, Quot.sound}`.  §6's genre
assembly inherits exactly the owner-signed B.42 cite
`Uniformity.Density.Leaf.exists_slope_factorization` (through VCL's graded census
identities — never re-consumed); §7's census master carries B.42 +
`Uniformity.Density.Tower.agnprw_termination` (ID12's, previously declared), and
the capstone master the same.  C.33 and `AX_cellRecursion` must NOT occur. -/
#print axioms Uniformity.Density.IFCG71.depthPairSet_eq_empty_of_lt
#print axioms Uniformity.Density.IFCG71.pairDepthFiber_eq_zero_of_lt
#print axioms Uniformity.Density.IFCG71.ZcVal.zcURLim
#print axioms Uniformity.Density.IFCG71.sum_pairDepthFiber_le_card_depthPairSet
#print axioms Uniformity.Density.IFCG71.card_depthPairSetGE_eq_sum
#print axioms Uniformity.Density.IFCG71.sum_card_depthPairSet_le
#print axioms Uniformity.Density.IFCG71.sum_pairDepthFiber_vis_tail_le
#print axioms Uniformity.Density.IFCG71.tendsto_depthSum_of_env
#print axioms Uniformity.Density.IFCG71.tsum_of_geom_ratio
#print axioms Uniformity.Density.IFCG71.zcVal_visEntry_of_clusters
#print axioms Uniformity.Density.IFCG71.zcURLim_visEntry_depthSum
#print axioms Uniformity.Density.IFCG71.card_depthPairSetGE_one_right
#print axioms Uniformity.Density.IFCG71.card_depthPairSetGE_swap
#print axioms Uniformity.Density.IFCG71.deepStratumDrain_one_right
#print axioms Uniformity.Density.IFCG71.deepStratumDrain_one_left
#print axioms Uniformity.Density.IFCG71.deepStratumDrain_of_min_two
#print axioms Uniformity.Density.IFCG71.visEntryGeom_of_cluster
#print axioms Uniformity.Density.IFCG71.zcURLim_visWeight_of_entryGeom
#print axioms Uniformity.Density.IFCG71.visWeightLaw_of_entryGeom
#print axioms Uniformity.Density.IFCG71.powerVisWeightLaw_of_entryGeom
#print axioms Uniformity.Density.IFCG71.visCensusLaw_of_entryGeom_collisions
#print axioms Uniformity.Density.IFCG71.visCensusLaw_of_clusterGeom_collisions
#print axioms Uniformity.Density.IFCG71.decidedSliceAt_all_of_clusterGeom
#print axioms Uniformity.Density.IFCG71.capstoneHypotheses_of_clusterGeom
