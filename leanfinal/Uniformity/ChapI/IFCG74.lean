/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import Uniformity.ChapI.IFCG73

/-!
# Uniformity.ChapI.IFCG74 — [SDJ 2026-08-31] THE SECTOR × DEPTH JOINT CENSUS AND THE
BLOCK-GROUPING CENSUS: the convolution row's cluster values re-based onto the
decided-type-pinned joint census, and the collision total graded in cluster currency

Stage SDJ of the cone census (design record `runs/wave-c/verdict_SDJ.md`; consumes
GCV = `IFCG73`, VA23 = `IFCG71`, and through them KDW = `IFCG56`, VCL = `IFCG60`,
RDC = `IFCG41`, SDL = `IFCG40`, PCD = `IFCG58`).  GCV left the convolution row on
exactly {`VisEntryClusterGeom` (the sector × depth joint census), the two collision
limits}, and refuted two framings: the residual-pattern sub-sum for the sector census
(sector membership is DECIDED-TYPE data of the product cell, not the mod-`π` pattern)
and the one-cluster-per-cell collision formula (a visible cell admits MULTIPLE
mass-decompositions).  THIS file lands the honest structure both refutations point
to:

* **§1 THE JOINT CENSUS CARRIER** — the decided-type-pinned depth census is KDW's
  `tableSlice` (decided × decided pairs at fixed types, graded by `mixDepth`), and
  ★ `sum_card_tableSlice`: summed over the depth it factorizes EXACTLY as the
  product of the two decided counts — the "product of decided counts × conditional
  depth distribution" shape of the joint census, exact at every level.
* **§2 ★★ THE JOINT-CENSUS/CLUSTER BRIDGE** (`sum_clusterCount_univ`): summed over
  ALL product cells, `q^v` times the cluster-root count of one table entry IS the
  decided joint census at the shifted level: `q^v·Σ_c #clusters(c) =
  #tableSlice(N−v, v)·q^{mv}` — the census over decided × decided at fixed types
  graded by depth is exactly the assembly's own currency.
* **§3 ★★ THE SECTOR SPLIT** — `clusterEntryFam g + strayClusterFam g = jointSliceFam`
  (exact for `2v+1 ≤ N`): the per-entry CLUSTER census of the row splits as the
  type-pinned joint census MINUS the stray-cluster census; sector membership enters
  ONLY through the strays.
* **§4 THE FIRES** — ★ `visEntryClusterGeom_of_degree_ne` (weight-mismatched parts
  have EMPTY decided sets — the entry family is identically 0, so the row's entry
  premise holds OUTRIGHT there) and ★ `visEntryClusterGeom_of_card_le_one` (the
  singleton-type fire, through VCL's type-support forcing).
* **§5 ★★ THE REDUCTION** — `visEntryClusterGeom_of_joint_stray`: explicit per-depth
  values for the joint census and the stray census (shared geometric modulus) give
  `VisEntryClusterGeom` outright — the row's cluster axis re-based onto the two
  named censuses.
* **§6 THE BLOCK-GROUPING CENSUS** — ★ `pairDepthFiber_eq_cluster_add_late`
  (per-cell: `pairDepthFiber = q^v·#clusters + #late`, exact at `2v+1 ≤ N`), its
  vis-summed form, ★ `pairFiber_eq_cluster_late_deep` (the per-entry grouping
  decomposition with the named deep remainder), and ★ `genreCollisionTotal_add_card`
  (the exact collision identity over the double count: `collision + #vis =
  Σ_v visDepthMass`) — the collision total is exact bookkeeping over the same
  cluster censuses, never a one-cluster-per-cell formula.
* **§7 THE MASTERS RECOMPUTED** — the row (`visCensusLaw_of_clusterGeom_matched`),
  the census master, and the capstone master with the cluster-value premise trimmed
  to the WEIGHT-MATCHED parts (`⟨part⟩.degree = n₁`, `⟨σ.data − part⟩.degree = n₂`);
  every other premise byte-identical to GCV's.

## THE HONEST FENCE

The VALUES of the two new named censuses do NOT land here and are not claimed:
* the joint census `#tableSlice(τ₁, τ₂, L, v)` at ramified types — the conditional
  gcd-filtration at fixed decided types (the deep-tower analogue of GNA's
  pattern-graded assembly; the two gradings differ exactly as GCV's refutation
  records);
* the stray-cluster census (which clusters land OUTSIDE the genre's visible cells —
  decidedness-transfer/sector-membership content).
`VisCensusLaw` at ramified non-singleton types therefore does NOT fire here; what
this file does is re-base its cluster axis onto the two named censuses with EXACT
identities, trim its entry premise to the weight-matched parts, and grade the
collision axis in the same cluster currency.  Nothing weakened; every consumed
statement byte-untouched; GCV's two refuted framings are NOT re-attempted.

## Axiom fence (machine-exact at landing: 19 footer rows)

FOURTEEN rows PURE Lean core `{propext, Classical.choice, Quot.sound}`: all of
§§1–3, the weight-mismatch/type-degree fires, §5's reduction, and §6's
per-cell/per-entry cluster-late layer.  FOUR rows Lean core + exactly the
owner-signed B.42 cite `Uniformity.Density.Leaf.exists_slope_factorization`
(inherited, never re-consumed): `visEntryClusterGeom_of_card_le_one` (through VCL's
type-support forcing), `genreCollisionTotal_add_card` (through SDL's/PCD's
`1 ≤ multCount` on visible cells), and the row/census masters (through GCV's).  The
capstone master additionally inherits `Uniformity.Density.Tower.agnprw_termination`
(ID12's, previously declared).  C.33 and `AX_cellRecursion` do NOT occur.  Zero
sorries, zero new axioms.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.overlappingInstances false

noncomputable section

namespace Uniformity.Density.IFCG74

open IsLocalRing Polynomial Filter Topology
open Uniformity.Density.Induction
open Uniformity.Density.IFCG14 (DecidedValueLaw Witnessed)
open Uniformity.Density.IFCG24 (ZcURLim ZcURLim_zero ConeRemainderLaw)
open Uniformity.Density.IFCG38 (splitSectorVis convPairs convCount mulClassAt)
open Uniformity.Density.IFCG40 (pairFiber multCount one_le_multCount_of_vis)
open Uniformity.Density.IFCG41 (mixDepth mixDepth_le pairDepthFiber CollisionLaw
  multCount_eq_sum_pairDepthFiber pairFiber_eq_sum_pairDepthFiber)
open Uniformity.Density.IFCG44 (powerSectorProperVis PowerFullSpanLaw)
open Uniformity.Density.IFCG48 (FactorCorrespondenceAt)
open Uniformity.Density.IFCG49 (decidedAt_of_coeffFactor)
open Uniformity.Density.IFCG51 (EisFullSpanRemainderLaw)
open Uniformity.Density.IFCG56 (depthPairSet decidedPairSet pairFactor
  shiftedDepthFiber tableSlice shiftedSlice natCard_shiftedDepthFiber
  card_shiftedSlice shiftedSlice_eq_preimage shiftedSlice_subset_tableSlice
  pairDepthFiber_eq_natCard card_preimage_pairFactor)
open Uniformity.Density.IFCG57 (LeafSubfaceLaw)
open Uniformity.Density.IFCG58 (VisGenre visGenreSet VisCensusLaw
  powerCollisionTotal one_le_multCount_of_powerVis)
open Uniformity.Density.IFCG60 (visDepthMass genreCollisionTotal
  sum_multCount_eq_sum_visDepthMass visGenreSet_eq_empty_of_card_le_one)
open Uniformity.Density.IFCG71 (ZcVal VisEntryClusterGeom clusterEntryFam
  DeepStratumDrain)

/-! ## §0 — the kit: the corpus's counting spines, reproduced -/

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

/-- The count of a set-product is the product of the counts (the corpus's private
copy, reproduced). -/
private theorem natCard_prod_set {α β : Type*} (s : Set α) (t : Set β) :
    Nat.card (s ×ˢ t : Set (α × β)) = Nat.card s * Nat.card t := by
  rw [← Nat.card_prod]
  exact Nat.card_congr (Equiv.Set.prod s t)

/-- Bridge: a finite set's `toFinset` card is its `Nat.card` (the corpus's private
copy, reproduced). -/
private theorem toFinset_card_eq_natCard {α : Type*} (s : Set α) (hs : s.Finite) :
    hs.toFinset.card = Nat.card s := by
  rw [Nat.card_coe_set_eq, Set.ncard_eq_toFinset_card s hs]

end Kit

/-! ## §1 — THE JOINT CENSUS CARRIER: the decided-type-pinned depth census is KDW's
`tableSlice`, it partitions the decided box (the "product of decided counts" side of
the joint census), and it is dominated by the full depth stratum -/

section JointCensus

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)]

/-- ★ **THE DEPTH PARTITION OF THE DECIDED BOX** (exact at every level): the
decided-type-pinned depth strata `tableSlice(τ₁, τ₂, L, v)` partition the decided
pair box, so the joint census summed over the depth IS the product of the two
decided counts — the exact "product of decided counts × conditional depth
distribution" factorization of the sector × depth joint census. -/
theorem sum_card_tableSlice (π : O) (n₁ n₂ : ℕ) (σ₁ σ₂ : FactorizationType)
    (L : ℕ) :
    ∑ v ∈ Finset.range (L + 1), Nat.card (tableSlice O π n₁ n₂ σ₁ σ₂ L v)
      = decidedCount O n₁ σ₁ L * decidedCount O n₂ σ₂ L := by
  have hprod : Nat.card (decidedPairSet O n₁ n₂ σ₁ σ₂ L)
      = decidedCount O n₁ σ₁ L * decidedCount O n₂ σ₂ L := by
    rw [decidedPairSet, natCard_prod_set, decidedCount, decidedCount]
  rw [← hprod,
    natCard_eq_sum_fiber_of_mem (decidedPairSet O n₁ n₂ σ₁ σ₂ L)
      (fun q => mixDepth π q.1 q.2) (Finset.range (L + 1))
      (fun q _ => Finset.mem_range.mpr (Nat.lt_succ_of_le (mixDepth_le π q.1 q.2)))]
  exact Finset.sum_congr rfl fun v _ => by congr 1

/-- The joint census is dominated by the FULL depth stratum (the drain transport:
GCV's `deepStratumDrain_all` bounds the decided deep tail as well). -/
theorem card_tableSlice_le_card_depthPairSet (π : O) (n₁ n₂ : ℕ)
    (σ₁ σ₂ : FactorizationType) (L v : ℕ) :
    Nat.card (tableSlice O π n₁ n₂ σ₁ σ₂ L v)
      ≤ Nat.card (depthPairSet O π n₁ n₂ L v) := by
  rw [Nat.card_coe_set_eq, Nat.card_coe_set_eq]
  exact Set.ncard_le_ncard Set.inter_subset_right (Set.toFinite _)

/-- **The weight-mismatch emptiness**: a decided set at a type of the WRONG degree is
empty (every class has a monic lift, and the lift's type has the class's degree). -/
theorem decidedSet_eq_empty_of_degree_ne {n : ℕ} {σ : FactorizationType}
    (hσ : σ.degree ≠ n) (L : ℕ) : decidedSet O n σ L = ∅ := by
  ext c
  simp only [decidedSet, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
  intro hc
  obtain ⟨a, ha⟩ := proj_surjective O n L c
  have htype := hc a ha
  have hdeg : (typeOf (monicPoly a)).degree = n := by
    rw [typeOf_degree (monicPoly_monic a), monicPoly_natDegree]
  rw [htype] at hdeg
  exact hσ hdeg

end JointCensus

/-! ## §2 — ★★ THE JOINT-CENSUS/CLUSTER BRIDGE: summed over ALL product cells, the
cluster census of one table entry IS the decided-type-pinned joint census at the
shifted level — the assembly's own currency -/

section ClusterBridge

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)]

/-- The shifted slice partitions along the product class into the shifted-decided
depth fibers (the univ-partition of the cluster carrier). -/
theorem card_shiftedSlice_eq_sum_fiber {π : O} {n₁ n₂ N v : ℕ}
    [Fintype (Coeff O (n₁ + n₂) N)] (σ₁ σ₂ : FactorizationType) :
    Nat.card (shiftedSlice O π n₁ n₂ σ₁ σ₂ N v)
      = ∑ c : Coeff O (n₁ + n₂) N,
          Nat.card (shiftedDepthFiber O π n₁ n₂ σ₁ σ₂ N v c) := by
  rw [natCard_eq_sum_fiber_of_mem (shiftedSlice O π n₁ n₂ σ₁ σ₂ N v)
    (fun q => mulClass q.1 q.2) Finset.univ (fun q _ => Finset.mem_univ _)]
  refine Finset.sum_congr rfl fun c _ => ?_
  have hset : shiftedSlice O π n₁ n₂ σ₁ σ₂ N v
        ∩ (fun q : Coeff O n₁ N × Coeff O n₂ N => mulClass q.1 q.2) ⁻¹' {c}
      = shiftedDepthFiber O π n₁ n₂ σ₁ σ₂ N v c := by
    ext q
    simp only [shiftedSlice, shiftedDepthFiber, Set.mem_inter_iff, Set.mem_setOf_eq,
      Set.mem_preimage, Set.mem_singleton_iff]
    tauto
  rw [hset]

/-- ★★ **THE JOINT-CENSUS/CLUSTER BRIDGE** (exact, every level with `2v + 1 ≤ N`):
`q^v` times the FULL cluster-root census of one table entry — summed over ALL product
cells — is the decided-type-pinned joint census at the shifted level `N − v`, times
the exact cylinder factor:

    q^v · Σ_c #clusters(c)  =  #tableSlice(σ₁, σ₂, N − v, v) · q^{(n₁+n₂)·v}.

(Per-cell tiling `natCard_shiftedDepthFiber` + the univ partition + KDW's
`card_shiftedSlice`.) -/
theorem qpow_mul_sum_clusterCount_univ {π : O} (hπ : Irreducible π) {n₁ n₂ N v : ℕ}
    (hN : 2 * v + 1 ≤ N) (hpos : n₁ ≠ 0 ∨ n₂ ≠ 0) (σ₁ σ₂ : FactorizationType)
    [Fintype (Coeff O (n₁ + n₂) N)] :
    residueCard O ^ v
        * ∑ c : Coeff O (n₁ + n₂) N,
            Nat.card ((pairFactor n₁ n₂ (Nat.sub_le N v)) ''
              (shiftedDepthFiber O π n₁ n₂ σ₁ σ₂ N v c))
      = Nat.card (tableSlice O π n₁ n₂ σ₁ σ₂ (N - v) v)
          * residueCard O ^ ((n₁ + n₂) * v) := by
  rw [← card_shiftedSlice hπ hN σ₁ σ₂, card_shiftedSlice_eq_sum_fiber σ₁ σ₂,
    Finset.mul_sum]
  exact Finset.sum_congr rfl fun c _ =>
    (natCard_shiftedDepthFiber hπ hN hpos σ₁ σ₂ c).symm

/-- **The stray-cluster count** of one table entry: the cluster roots landing OUTSIDE
the genre's visible cells (one instance-free `ℕ`) — the sector-membership content of
the cluster census. -/
noncomputable def strayClusterCount (g : VisGenre) (O : Type*) [CommRing O]
    [IsDomain O] [IsDiscreteValuationRing O] [Finite (ResidueField O)] (π : O)
    (n₁ n₂ : ℕ) (σ : FactorizationType) (part : Multiset (ℕ × ℕ)) (M v : ℕ) : ℕ :=
  ∑ c ∈ (Set.toFinite ((visGenreSet g O π (n₁ + n₂) σ M)ᶜ)).toFinset,
    Nat.card ((pairFactor n₁ n₂ (Nat.sub_le (M + (n₁ + n₂)) v)) ''
      (shiftedDepthFiber O π n₁ n₂ ⟨part⟩ ⟨σ.data - part⟩ (M + (n₁ + n₂)) v c))

/-- ★★ **THE SECTOR SPLIT** (exact, every level with `2v + 1 ≤ N`): the vis-restricted
cluster census of one table entry plus its stray-cluster census is the type-pinned
joint census at the shifted level — sector membership enters the cluster values ONLY
through the strays:

    q^v · (Σ_{c ∈ vis} #clusters(c) + stray)
      = #tableSlice(⟨part⟩, ⟨σ.data − part⟩, N − v, v) · q^{(n₁+n₂)·v}. -/
theorem qpow_mul_cluster_split {π : O} (hπ : Irreducible π) {n₁ n₂ M v : ℕ}
    (hN : 2 * v + 1 ≤ M + (n₁ + n₂)) (hpos : n₁ ≠ 0 ∨ n₂ ≠ 0) (g : VisGenre)
    (σ : FactorizationType) (part : Multiset (ℕ × ℕ)) :
    residueCard O ^ v
        * ((∑ c ∈ (Set.toFinite (visGenreSet g O π (n₁ + n₂) σ M)).toFinset,
              Nat.card ((pairFactor n₁ n₂ (Nat.sub_le (M + (n₁ + n₂)) v)) ''
                (shiftedDepthFiber O π n₁ n₂ ⟨part⟩ ⟨σ.data - part⟩
                  (M + (n₁ + n₂)) v c)))
            + strayClusterCount g O π n₁ n₂ σ part M v)
      = Nat.card (tableSlice O π n₁ n₂ ⟨part⟩ ⟨σ.data - part⟩ (M + (n₁ + n₂) - v) v)
          * residueCard O ^ ((n₁ + n₂) * v) := by
  classical
  letI : Fintype (Coeff O (n₁ + n₂) (M + (n₁ + n₂))) := Fintype.ofFinite _
  rw [← qpow_mul_sum_clusterCount_univ hπ hN hpos ⟨part⟩ ⟨σ.data - part⟩]
  congr 1
  rw [strayClusterCount]
  have hdisj : Disjoint
      (Set.toFinite (visGenreSet g O π (n₁ + n₂) σ M)).toFinset
      (Set.toFinite ((visGenreSet g O π (n₁ + n₂) σ M)ᶜ)).toFinset := by
    rw [Finset.disjoint_left]
    intro c hcA hcB
    rw [Set.Finite.mem_toFinset] at hcA hcB
    exact hcB hcA
  have hunion : (Set.toFinite (visGenreSet g O π (n₁ + n₂) σ M)).toFinset
      ∪ (Set.toFinite ((visGenreSet g O π (n₁ + n₂) σ M)ᶜ)).toFinset
      = Finset.univ := by
    ext c
    simp only [Finset.mem_union, Set.Finite.mem_toFinset, Set.mem_compl_iff,
      Finset.mem_univ, iff_true]
    tauto
  rw [← Finset.sum_union hdisj, hunion]

end ClusterBridge

/-! ## §3 — THE NORMALIZED FAMILIES AND THE EXACT SECTOR-SPLIT IDENTITY: the row's
per-entry cluster family = the joint-census family − the stray-cluster family -/

section Families

/-- **The joint-census family** at fixed types `(σ₁, σ₂)` and depth `v`: the
decided-type-pinned depth census at the shifted level `N − v = M + m − v`, in its own
natural normalization `q^{(n₁+n₂)(N−v)}` (the level-free currency of the conditional
gcd-filtration). -/
noncomputable def jointSliceFam (n₁ n₂ : ℕ) (σ₁ σ₂ : FactorizationType) (v : ℕ) :
    ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
      [IsAdicComplete (maximalIdeal O) O] [Finite (ResidueField O)], O → ℕ → ℝ :=
  fun O _ _ _ _ _ π M =>
    (Nat.card (tableSlice O π n₁ n₂ σ₁ σ₂ (M + (n₁ + n₂) - v) v) : ℝ)
      / ((residueCard O : ℕ) : ℝ) ^ ((n₁ + n₂) * (M + (n₁ + n₂) - v))

/-- **The stray-cluster family** of one table entry at depth `v`: `q^v` times the
stray cluster-root count, normalized like the entry family (the sector-membership
content of the cluster census). -/
noncomputable def strayClusterFam (g : VisGenre) (n₁ n₂ : ℕ) (σ : FactorizationType)
    (part : Multiset (ℕ × ℕ)) (v : ℕ) :
    ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
      [IsAdicComplete (maximalIdeal O) O] [Finite (ResidueField O)], O → ℕ → ℝ :=
  fun O _ _ _ _ _ π M =>
    ((residueCard O ^ v * strayClusterCount g O π n₁ n₂ σ part M v : ℕ) : ℝ)
      / ((residueCard O : ℕ) : ℝ) ^ ((n₁ + n₂) * (M + (n₁ + n₂)))

/-- ★★ **THE EXACT SECTOR-SPLIT IDENTITY of the row's cluster family** (every level
with `2v + 1 ≤ M + m`): VA23's per-entry cluster family is EXACTLY the joint-census
family minus the stray-cluster family —

    clusterEntryFam g + strayClusterFam g = jointSliceFam ⟨part⟩ ⟨σ.data − part⟩.

The sector × depth joint census splits into decided-type content (`tableSlice`, the
conditional gcd-filtration at fixed types) and sector-membership content (the
strays); GCV's refuted residual-pattern framing is nowhere consumed. -/
theorem clusterEntryFam_add_stray {n₁ n₂ : ℕ} (hpos : n₁ ≠ 0 ∨ n₂ ≠ 0)
    (g : VisGenre) (σ : FactorizationType) (part : Multiset (ℕ × ℕ)) (v : ℕ)
    (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [IsAdicComplete (maximalIdeal O) O] [Finite (ResidueField O)]
    {π : O} (hπ : Irreducible π) (M : ℕ) (hM : 2 * v + 1 ≤ M + (n₁ + n₂)) :
    clusterEntryFam g n₁ n₂ σ part v O π M
        + strayClusterFam g n₁ n₂ σ part v O π M
      = jointSliceFam n₁ n₂ ⟨part⟩ ⟨σ.data - part⟩ v O π M := by
  have hkey := qpow_mul_cluster_split hπ hM hpos g σ part
  have hvN : v ≤ M + (n₁ + n₂) := by omega
  have hexp : (n₁ + n₂) * (M + (n₁ + n₂))
      = (n₁ + n₂) * (M + (n₁ + n₂) - v) + (n₁ + n₂) * v := by
    rw [← Nat.mul_add, Nat.sub_add_cancel hvN]
  have hQ : (0 : ℝ) < ((residueCard O : ℕ) : ℝ) := by
    exact_mod_cast residueCard_pos O
  have hpow : ((residueCard O : ℕ) : ℝ) ^ ((n₁ + n₂) * (M + (n₁ + n₂)))
      = ((residueCard O : ℕ) : ℝ) ^ ((n₁ + n₂) * (M + (n₁ + n₂) - v))
        * ((residueCard O : ℕ) : ℝ) ^ ((n₁ + n₂) * v) := by
    rw [← pow_add, ← hexp]
  simp only [clusterEntryFam, strayClusterFam, jointSliceFam]
  rw [← add_div, div_eq_div_iff (pow_pos hQ _).ne' (pow_pos hQ _).ne', hpow]
  have hkeyR := congrArg (Nat.cast (R := ℝ)) hkey
  push_cast at hkeyR ⊢
  linear_combination
    (((residueCard O : ℕ) : ℝ)) ^ ((n₁ + n₂) * (M + (n₁ + n₂) - v)) * hkeyR

end Families

/-! ## §4 — THE FIRES: the entries whose cluster family is identically zero — the
weight-mismatched parts (empty decided sets) and the singleton types (empty sector) -/

section Fires

/-- The zero-family fire (private spine): an entry whose cluster family vanishes
identically satisfies `VisEntryClusterGeom` with witness `(0, 1)`. -/
private theorem visEntryClusterGeom_of_zero {g : VisGenre} {n₁ n₂ : ℕ}
    {σ : FactorizationType} {part : Multiset (ℕ × ℕ)}
    (h0 : ∀ (v : ℕ) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
      [IsAdicComplete (maximalIdeal O) O] [Finite (ResidueField O)] (π : O),
        Irreducible π → ∀ M, clusterEntryFam g n₁ n₂ σ part v O π M = 0) :
    VisEntryClusterGeom g n₁ n₂ σ part := by
  refine ⟨fun _ => 0, fun _ => 1, 0, 1, le_rfl, fun _ => one_ne_zero, fun v => ?_,
    fun v _ => by simp⟩
  intro O _ _ _ _ _
  refine ⟨by simp, fun π hπ => ?_⟩
  have hz : Filter.Tendsto (clusterEntryFam g n₁ n₂ σ part v O π)
      Filter.atTop (nhds 0) := by
    refine Filter.Tendsto.congr (fun M => ?_) tendsto_const_nhds
    exact (h0 v O π hπ M).symm
  simpa using hz

/-- ★ **THE WEIGHT-MISMATCH FIRE**: at a part whose type degrees do not match the
mass split, BOTH decided sets cannot be nonempty — the entry's cluster family is
identically zero and `VisEntryClusterGeom` holds OUTRIGHT.  (This trims the row's
entry premise to the weight-matched parts.) -/
theorem visEntryClusterGeom_of_degree_ne {n₁ n₂ : ℕ} (σ : FactorizationType)
    (part : Multiset (ℕ × ℕ))
    (h : (⟨part⟩ : FactorizationType).degree ≠ n₁
       ∨ (⟨σ.data - part⟩ : FactorizationType).degree ≠ n₂) (g : VisGenre) :
    VisEntryClusterGeom g n₁ n₂ σ part := by
  refine visEntryClusterGeom_of_zero fun v O _ _ _ _ _ π hπ M => ?_
  have hempty : decidedPairSet O n₁ n₂ ⟨part⟩ ⟨σ.data - part⟩
      (M + (n₁ + n₂) - v) = ∅ := by
    rcases h with h | h
    · rw [decidedPairSet, decidedSet_eq_empty_of_degree_ne h, Set.empty_prod]
    · rw [decidedPairSet, decidedSet_eq_empty_of_degree_ne h, Set.prod_empty]
  have hfib : ∀ c : Coeff O (n₁ + n₂) (M + (n₁ + n₂)),
      shiftedDepthFiber O π n₁ n₂ ⟨part⟩ ⟨σ.data - part⟩ (M + (n₁ + n₂)) v c = ∅ := by
    intro c
    ext q
    simp only [shiftedDepthFiber, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
    rintro ⟨hdec, -, -⟩
    rw [hempty] at hdec
    exact hdec
  simp only [clusterEntryFam]
  have hsum : ∀ c ∈ (Set.toFinite (visGenreSet g O π (n₁ + n₂) σ M)).toFinset,
      Nat.card ((pairFactor n₁ n₂ (Nat.sub_le (M + (n₁ + n₂)) v)) ''
        (shiftedDepthFiber O π n₁ n₂ ⟨part⟩ ⟨σ.data - part⟩ (M + (n₁ + n₂)) v c))
      = 0 := by
    intro c _
    rw [hfib c, Set.image_empty, Nat.card_coe_set_eq, Set.ncard_empty]
  rw [Finset.sum_congr rfl hsum, Finset.sum_const, smul_eq_mul, mul_zero, mul_zero]
  simp

/-- ★ **THE SINGLETON-TYPE FIRE of the cluster values**: at `card σ.data ≤ 1` the
genre's visible sector is empty (VCL's type-support forcing), so every entry's
cluster family is identically zero — `VisEntryClusterGeom` holds OUTRIGHT at every
singleton type, both genres, every entry. -/
theorem visEntryClusterGeom_of_card_le_one {n₁ n₂ : ℕ} (h₁ : 0 < n₁) (h₂ : 0 < n₂)
    {σ : FactorizationType} (hcard : Multiset.card σ.data ≤ 1)
    (part : Multiset (ℕ × ℕ)) (g : VisGenre) :
    VisEntryClusterGeom g n₁ n₂ σ part := by
  refine visEntryClusterGeom_of_zero fun v O _ _ _ _ _ π hπ M => ?_
  simp only [clusterEntryFam]
  have hset := visGenreSet_eq_empty_of_card_le_one hπ (by omega : 0 < n₁ + n₂)
    hcard g M
  have hfin : (Set.toFinite (visGenreSet g O π (n₁ + n₂) σ M)).toFinset = ∅ :=
    Set.Finite.toFinset_eq_empty.mpr hset
  rw [hfin, Finset.sum_empty, mul_zero]
  simp

end Fires

/-! ## §5 — ★★ THE REDUCTION: per-depth explicit values for the joint census and the
stray census (shared geometric modulus) give the row's `VisEntryClusterGeom` outright -/

section Reduction

/-- ★★ **THE ROW'S CLUSTER AXIS, RE-BASED** — per-depth explicit rational values for
the two named censuses of the sector split, with ONE shared geometric modulus `X^a`
from `v₀` on, assemble to `VisEntryClusterGeom` (witnesses: the difference
`(nnJ·ddS − nnS·ddJ) / (ddJ·ddS)`).  After this theorem the convolution row's
cluster-value premise rests on exactly

  {the decided-type-pinned joint census values (`jointSliceFam` — the conditional
   gcd-filtration at fixed types), the stray-cluster census values
   (`strayClusterFam` — the sector-membership content)}. -/
theorem visEntryClusterGeom_of_joint_stray {n₁ n₂ : ℕ} (h₁ : 0 < n₁) (h₂ : 0 < n₂)
    (g : VisGenre) (σ : FactorizationType) (part : Multiset (ℕ × ℕ))
    {nnJ ddJ nnS ddS : ℕ → Polynomial ℚ} {v₀ a : ℕ} (ha : 1 ≤ a)
    (hddJ : ∀ v, ddJ v ≠ 0) (hddS : ∀ v, ddS v ≠ 0)
    (hvalJ : ∀ v, ZcVal (jointSliceFam n₁ n₂ ⟨part⟩ ⟨σ.data - part⟩ v)
      (nnJ v) (ddJ v))
    (hvalS : ∀ v, ZcVal (strayClusterFam g n₁ n₂ σ part v) (nnS v) (ddS v))
    (hgeomJ : ∀ v, v₀ ≤ v →
      Polynomial.X ^ a * (nnJ (v + 1) * ddJ v) = nnJ v * ddJ (v + 1))
    (hgeomS : ∀ v, v₀ ≤ v →
      Polynomial.X ^ a * (nnS (v + 1) * ddS v) = nnS v * ddS (v + 1)) :
    VisEntryClusterGeom g n₁ n₂ σ part := by
  refine ⟨fun v => nnJ v * ddS v - nnS v * ddJ v, fun v => ddJ v * ddS v, v₀, a, ha,
    fun v => mul_ne_zero (hddJ v) (hddS v), fun v => ?_, fun v hv => ?_⟩
  · -- the per-depth value of the difference
    intro O _ _ _ _ _
    obtain ⟨hneJ, hlimJ⟩ := hvalJ v O
    obtain ⟨hneS, hlimS⟩ := hvalS v O
    refine ⟨by rw [Polynomial.eval_mul]; exact mul_ne_zero hneJ hneS, fun π hπ => ?_⟩
    have hsub := (hlimJ π hπ).sub (hlimS π hπ)
    have hev : (fun M => jointSliceFam n₁ n₂ ⟨part⟩ ⟨σ.data - part⟩ v O π M
          - strayClusterFam g n₁ n₂ σ part v O π M)
        =ᶠ[Filter.atTop] clusterEntryFam g n₁ n₂ σ part v O π := by
      refine Filter.eventually_atTop.mpr ⟨2 * v + 1, fun M hM => ?_⟩
      have hid := clusterEntryFam_add_stray (Or.inl h₁.ne') g σ part v O hπ M
        (by omega : 2 * v + 1 ≤ M + (n₁ + n₂))
      linarith
    have hvalQ : ((nnJ v * ddS v - nnS v * ddJ v).eval ((residueCard O : ℕ) : ℚ)
          / ((ddJ v * ddS v).eval ((residueCard O : ℕ) : ℚ)) : ℚ)
        = ((nnJ v).eval ((residueCard O : ℕ) : ℚ)
              / (ddJ v).eval ((residueCard O : ℕ) : ℚ) : ℚ)
          - ((nnS v).eval ((residueCard O : ℕ) : ℚ)
              / (ddS v).eval ((residueCard O : ℕ) : ℚ) : ℚ) := by
      rw [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_mul,
        Polynomial.eval_mul]
      field_simp
    rw [hvalQ, Rat.cast_sub]
    exact Filter.Tendsto.congr' hev hsub
  · -- the shared geometric relation transports to the difference
    have hJ := hgeomJ v hv
    have hS := hgeomS v hv
    linear_combination (ddS (v + 1) * ddS v) * hJ - (ddJ (v + 1) * ddJ v) * hS

end Reduction

/-! ## §6 — THE BLOCK-GROUPING CENSUS: the per-cell cluster/late decomposition of the
depth-graded fiber, and the exact collision identity over the double count -/

section Grouping

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)]

/-- **The late fiber** over a product cell: the decided depth-`v` pairs whose
truncation at the shifted level is NOT yet decided (the level-stabilization gap —
drains as `M → ∞` by KDW's ambiguity bound). -/
def lateFiber (O : Type*) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Finite (ResidueField O)] (π : O) (n₁ n₂ : ℕ) (σ₁ σ₂ : FactorizationType)
    (N v : ℕ) (c : Coeff O (n₁ + n₂) N) : Set (Coeff O n₁ N × Coeff O n₂ N) :=
  {q | q ∈ decidedPairSet O n₁ n₂ σ₁ σ₂ N ∧ mulClass q.1 q.2 = c
      ∧ mixDepth π q.1 q.2 = v
      ∧ pairFactor n₁ n₂ (Nat.sub_le N v) q ∉ decidedPairSet O n₁ n₂ σ₁ σ₂ (N - v)}

/-- ★ **THE PER-CELL CLUSTER/LATE DECOMPOSITION** (exact, every level with
`2v + 1 ≤ N`): the depth-`v` graded fiber over ANY product cell is `q^v` times its
cluster-root count plus its late count —

    pairDepthFiber p c v = q^v · #clusters(c) + #late(c).

This is the per-cell block-grouping instrument: a cell hit by several
`(mass split, part)`-groupings carries each hit as its own cluster, and the exact
multiplicity is the (grouping, cluster-root) incidence count weighted `q^v` — never
the one-cluster-per-cell formula GCV refuted. -/
theorem pairDepthFiber_eq_cluster_add_late {π : O} (hπ : Irreducible π)
    (σ : FactorizationType) (M : ℕ) {n₁ n₂ : ℕ} (part : Multiset (ℕ × ℕ))
    (c : Coeff O (n₁ + n₂) (M + (n₁ + n₂))) {v : ℕ}
    (hN : 2 * v + 1 ≤ M + (n₁ + n₂)) (hpos : n₁ ≠ 0 ∨ n₂ ≠ 0) :
    pairDepthFiber O π (n₁ + n₂) σ M ((n₁, n₂), part) c v
      = residueCard O ^ v
          * Nat.card ((pairFactor n₁ n₂ (Nat.sub_le (M + (n₁ + n₂)) v)) ''
              (shiftedDepthFiber O π n₁ n₂ ⟨part⟩ ⟨σ.data - part⟩
                (M + (n₁ + n₂)) v c))
        + Nat.card (lateFiber O π n₁ n₂ ⟨part⟩ ⟨σ.data - part⟩
            (M + (n₁ + n₂)) v c) := by
  rw [pairDepthFiber_eq_natCard π σ M ((n₁, n₂), part) rfl c v,
    ← natCard_shiftedDepthFiber hπ hN hpos ⟨part⟩ ⟨σ.data - part⟩ c]
  have hpart : (decidedPairSet O n₁ n₂ ⟨part⟩ ⟨σ.data - part⟩ (M + (n₁ + n₂))
        ∩ {q | mulClassAt rfl q.1 q.2 = c}
        ∩ depthPairSet O π n₁ n₂ (M + (n₁ + n₂)) v)
      = shiftedDepthFiber O π n₁ n₂ ⟨part⟩ ⟨σ.data - part⟩ (M + (n₁ + n₂)) v c
        ∪ lateFiber O π n₁ n₂ ⟨part⟩ ⟨σ.data - part⟩ (M + (n₁ + n₂)) v c := by
    ext q
    constructor
    · rintro ⟨⟨hdec, hmul⟩, hdep⟩
      by_cases hsh : pairFactor n₁ n₂ (Nat.sub_le (M + (n₁ + n₂)) v) q
          ∈ decidedPairSet O n₁ n₂ ⟨part⟩ ⟨σ.data - part⟩ (M + (n₁ + n₂) - v)
      · exact Or.inl ⟨hsh, hmul, hdep⟩
      · exact Or.inr ⟨hdec, hmul, hdep, hsh⟩
    · rintro (⟨hsh, hmul, hdep⟩ | ⟨hdec, hmul, hdep, -⟩)
      · exact ⟨⟨⟨decidedAt_of_coeffFactor (Nat.sub_le _ v) hsh.1,
          decidedAt_of_coeffFactor (Nat.sub_le _ v) hsh.2⟩, hmul⟩, hdep⟩
      · exact ⟨⟨hdec, hmul⟩, hdep⟩
  have hdisj : Disjoint
      (shiftedDepthFiber O π n₁ n₂ ⟨part⟩ ⟨σ.data - part⟩ (M + (n₁ + n₂)) v c)
      (lateFiber O π n₁ n₂ ⟨part⟩ ⟨σ.data - part⟩ (M + (n₁ + n₂)) v c) := by
    rw [Set.disjoint_left]
    rintro q ⟨hsh, -, -⟩ ⟨-, -, -, hnot⟩
    exact hnot hsh
  rw [hpart, Nat.card_coe_set_eq,
    Set.ncard_union_eq hdisj (Set.toFinite _) (Set.toFinite _),
    ← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq]

/-- ★ **The vis-summed cluster/late decomposition** (one table entry, one depth,
exact with `2v + 1 ≤ N`): the depth-`v` visible pair mass at the entry is `q^v`
times its visible cluster-root count plus its visible late mass. -/
theorem sum_pairDepthFiber_vis_eq_cluster_add_late {π : O} (hπ : Irreducible π)
    {n₁ n₂ M v : ℕ} (hN : 2 * v + 1 ≤ M + (n₁ + n₂)) (hpos : n₁ ≠ 0 ∨ n₂ ≠ 0)
    (g : VisGenre) (σ : FactorizationType) (part : Multiset (ℕ × ℕ)) :
    ∑ c ∈ (Set.toFinite (visGenreSet g O π (n₁ + n₂) σ M)).toFinset,
        pairDepthFiber O π (n₁ + n₂) σ M ((n₁, n₂), part) c v
      = residueCard O ^ v
          * (∑ c ∈ (Set.toFinite (visGenreSet g O π (n₁ + n₂) σ M)).toFinset,
              Nat.card ((pairFactor n₁ n₂ (Nat.sub_le (M + (n₁ + n₂)) v)) ''
                (shiftedDepthFiber O π n₁ n₂ ⟨part⟩ ⟨σ.data - part⟩
                  (M + (n₁ + n₂)) v c)))
        + ∑ c ∈ (Set.toFinite (visGenreSet g O π (n₁ + n₂) σ M)).toFinset,
            Nat.card (lateFiber O π n₁ n₂ ⟨part⟩ ⟨σ.data - part⟩
              (M + (n₁ + n₂)) v c) := by
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun c _ =>
    pairDepthFiber_eq_cluster_add_late hπ σ M part c hN hpos

/-- ★ **THE PER-ENTRY GROUPING DECOMPOSITION** (exact, every level): the FULL pair
fiber of one table entry over a product cell splits into the shallow depths — where
each hit is `q^v` cluster roots plus the late mass — and the named deep remainder
(`2v + 1 > N`, dominated by GCV's draining deep box):

    pairFiber p c = Σ_{2v+1 ≤ N} (q^v·#clusters + #late) + Σ_{2v+1 > N} pairDepthFiber.

This is the per-cell block-grouping census: `multCount c = Σ_p pairFiber p c` counts
each `(mass split, part)`-grouping of the cell with exactly this weight. -/
theorem pairFiber_eq_cluster_late_deep {π : O} (hπ : Irreducible π)
    {n₁ n₂ M : ℕ} (hpos : n₁ ≠ 0 ∨ n₂ ≠ 0) (σ : FactorizationType)
    (part : Multiset (ℕ × ℕ)) (c : Coeff O (n₁ + n₂) (M + (n₁ + n₂))) :
    pairFiber O (n₁ + n₂) σ M ((n₁, n₂), part) c
      = (∑ v ∈ Finset.range ((M + (n₁ + n₂) - 1) / 2 + 1),
          (residueCard O ^ v
              * Nat.card ((pairFactor n₁ n₂ (Nat.sub_le (M + (n₁ + n₂)) v)) ''
                  (shiftedDepthFiber O π n₁ n₂ ⟨part⟩ ⟨σ.data - part⟩
                    (M + (n₁ + n₂)) v c))
            + Nat.card (lateFiber O π n₁ n₂ ⟨part⟩ ⟨σ.data - part⟩
                (M + (n₁ + n₂)) v c)))
        + ∑ v ∈ Finset.Ico ((M + (n₁ + n₂) - 1) / 2 + 1) (M + (n₁ + n₂) + 1),
            pairDepthFiber O π (n₁ + n₂) σ M ((n₁, n₂), part) c v := by
  have hm : n₁ + n₂ ≠ 0 := by rcases hpos with h | h <;> omega
  rw [pairFiber_eq_sum_pairDepthFiber π (n₁ + n₂) σ M ((n₁, n₂), part) c,
    ← Finset.sum_range_add_sum_Ico _ (by omega :
      (M + (n₁ + n₂) - 1) / 2 + 1 ≤ M + (n₁ + n₂) + 1)]
  congr 1
  refine Finset.sum_congr rfl fun v hv => ?_
  have hvS := Finset.mem_range.mp hv
  exact pairDepthFiber_eq_cluster_add_late hπ σ M part c (by omega) hpos

variable [IsAdicComplete (maximalIdeal O) O]

/-- ★ **THE EXACT COLLISION IDENTITY OVER THE DOUBLE COUNT** (genre-uniform, exact
at every finite level): the genre's collision total plus its visible CELL count is
the depth-graded visible pair mass — the double count `Σ_{c ∈ vis} multCount c`
in RDC's grading.  With the cluster/late decomposition above, the collision total
is exact bookkeeping over the same cluster censuses the row's entry values consume
(B.42 through SDL's/PCD's `1 ≤ multCount` on visible cells). -/
theorem genreCollisionTotal_add_card {π : O} (hπ : Irreducible π) {m : ℕ}
    (hm : 0 < m) (g : VisGenre) (σ : FactorizationType) (M : ℕ) :
    genreCollisionTotal g O π m σ M + Nat.card (visGenreSet g O π m σ M)
      = ∑ v ∈ Finset.range (M + m + 1), visDepthMass g O π m σ M v := by
  rw [← sum_multCount_eq_sum_visDepthMass g π m σ M]
  have hone : ∀ c ∈ (Set.toFinite (visGenreSet g O π m σ M)).toFinset,
      1 ≤ multCount O m σ M c := by
    intro c hc
    rw [Set.Finite.mem_toFinset] at hc
    cases g with
    | split => exact one_le_multCount_of_vis hπ hm hc
    | power => exact one_le_multCount_of_powerVis hπ hm hc
  have hcard : Nat.card (visGenreSet g O π m σ M)
      = ∑ _c ∈ (Set.toFinite (visGenreSet g O π m σ M)).toFinset, 1 := by
    rw [Finset.sum_const, smul_eq_mul, mul_one,
      toFinset_card_eq_natCard (visGenreSet g O π m σ M) (Set.toFinite _)]
  have hgc : genreCollisionTotal g O π m σ M
      = ∑ c ∈ (Set.toFinite (visGenreSet g O π m σ M)).toFinset,
          (multCount O m σ M c - 1) := by
    cases g with
    | split => rfl
    | power => rfl
  rw [hgc, hcard, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun c hc => Nat.sub_add_cancel (hone c hc)

end Grouping

/-! ## §7 — THE MASTERS RECOMPUTED: the entry premise trimmed to the WEIGHT-MATCHED
parts (the mismatched entries fire outright) -/

section Masters

/-- Type degrees add along a sub-multiset split of the data. -/
theorem typeDegree_add_of_le {σ : FactorizationType} {part : Multiset (ℕ × ℕ)}
    (h : part ≤ σ.data) :
    (⟨part⟩ : FactorizationType).degree
        + (⟨σ.data - part⟩ : FactorizationType).degree = σ.degree := by
  show (part.map fun p => p.1 * p.2).sum
      + ((σ.data - part).map fun p => p.1 * p.2).sum
    = (σ.data.map fun p => p.1 * p.2).sum
  conv_rhs => rw [← add_tsub_cancel_of_le h]
  rw [Multiset.map_add, Multiset.sum_add]

/-- ★ The type-degree fire: at `σ.degree ≠ n₁ + n₂` EVERY part of the table entry is
weight-mismatched, so `VisEntryClusterGeom` holds outright. -/
theorem visEntryClusterGeom_of_type_degree_ne {n₁ n₂ : ℕ} {σ : FactorizationType}
    {part : Multiset (ℕ × ℕ)} (hmem : part ∈ σ.data.powerset.toFinset)
    (hne : σ.degree ≠ n₁ + n₂) (g : VisGenre) : VisEntryClusterGeom g n₁ n₂ σ part := by
  have hle : part ≤ σ.data := Multiset.mem_powerset.mp (Multiset.mem_toFinset.mp hmem)
  by_cases hd₁ : (⟨part⟩ : FactorizationType).degree = n₁
  · refine visEntryClusterGeom_of_degree_ne σ part (Or.inr fun hd₂ => hne ?_) g
    rw [← typeDegree_add_of_le hle, hd₁, hd₂]
  · exact visEntryClusterGeom_of_degree_ne σ part (Or.inl hd₁) g

/-- ★★ **THE CONVOLUTION ROW, WEIGHT-TRIMMED**: GCV's row base with the entry premise
required ONLY at the weight-matched parts (`⟨part⟩.degree = n₁` and
`⟨σ.data − part⟩.degree = n₂`) — every mismatched entry fires by the empty decided
sets.  The row now rests on exactly

  {weight-matched per-entry cluster values, `CollisionLaw`, the power collision
   `ZcURLim`}. -/
theorem visCensusLaw_of_clusterGeom_matched {m : ℕ} (hm : 0 < m)
    (σ : FactorizationType)
    (hentry : ∀ g : VisGenre, ∀ n₁ n₂ : ℕ, ∀ part : Multiset (ℕ × ℕ),
      0 < n₁ → 0 < n₂ → n₁ + n₂ = m → part ∈ σ.data.powerset.toFinset →
      (⟨part⟩ : FactorizationType).degree = n₁ →
      (⟨σ.data - part⟩ : FactorizationType).degree = n₂ →
        VisEntryClusterGeom g n₁ n₂ σ part)
    (hC : CollisionLaw m σ)
    (hPC : ZcURLim (fun O _ _ _ _ _ π M =>
      (powerCollisionTotal O π m σ M : ℝ)
        / ((residueCard O : ℕ) : ℝ) ^ (m * (M + m)))) :
    ∀ g, VisCensusLaw g m σ := by
  refine Uniformity.Density.IFCG73.visCensusLaw_of_clusterGeom_collisions hm σ
    ?_ hC hPC
  intro g n₁ n₂ part h₁ h₂ hsum hmem
  by_cases hd₁ : (⟨part⟩ : FactorizationType).degree = n₁
  · by_cases hd₂ : (⟨σ.data - part⟩ : FactorizationType).degree = n₂
    · exact hentry g n₁ n₂ part h₁ h₂ hsum hmem hd₁ hd₂
    · exact visEntryClusterGeom_of_degree_ne σ part (Or.inr hd₂) g
  · exact visEntryClusterGeom_of_degree_ne σ part (Or.inl hd₁) g

/-- ★★ **THE CENSUS MASTER, WEIGHT-TRIMMED**: GCV's drain-free census master with the
cluster-value premise required only at the weight-matched parts; every other premise
byte-identical. -/
theorem decidedSliceAt_all_of_clusterGeom_matched
    (hCG : ∀ e : ℕ, 5 ≤ e →
      (∀ k, k < e → ∀ σ' : FactorizationType, σ'.degree = k → DecidedValueLaw k σ') →
      ∀ σ : FactorizationType, σ.degree = e → Witnessed e σ →
        (∃ p ∈ σ.data, p.1 ≠ 1) → 2 ≤ Multiset.card σ.data →
        ∀ g : VisGenre, ∀ n₁ n₂ : ℕ, ∀ part : Multiset (ℕ × ℕ),
          0 < n₁ → 0 < n₂ → n₁ + n₂ = e → part ∈ σ.data.powerset.toFinset →
          (⟨part⟩ : FactorizationType).degree = n₁ →
          (⟨σ.data - part⟩ : FactorizationType).degree = n₂ →
            VisEntryClusterGeom g n₁ n₂ σ part)
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
    ∀ n : ℕ, Uniformity.Density.DecidedSliceAt n := by
  refine Uniformity.Density.IFCG73.decidedSliceAt_all_of_clusterGeom
    ?_ hCL hPCL hPF hLeafSub hR4
  intro e he hDV σ hσ hW hram hcard g n₁ n₂ part h₁ h₂ hsum hmem
  by_cases hd₁ : (⟨part⟩ : FactorizationType).degree = n₁
  · by_cases hd₂ : (⟨σ.data - part⟩ : FactorizationType).degree = n₂
    · exact hCG e he hDV σ hσ hW hram hcard g n₁ n₂ part h₁ h₂ hsum hmem hd₁ hd₂
    · exact visEntryClusterGeom_of_degree_ne σ part (Or.inr hd₂) g
  · exact visEntryClusterGeom_of_degree_ne σ part (Or.inl hd₁) g

universe uW uG uKt uL

/-- ★★ **THE CAPSTONE MASTER, WEIGHT-TRIMMED**: GCV's drain-free capstone master with
the cluster-value premise required only at the weight-matched parts; every other
premise byte-identical. -/
theorem capstoneHypotheses_of_clusterGeom_matched (n : ℕ)
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
          (⟨part⟩ : FactorizationType).degree = n₁ →
          (⟨σ.data - part⟩ : FactorizationType).degree = n₂ →
            VisEntryClusterGeom g n₁ n₂ σ part)
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
    CapstoneHypotheses.{uW, uG, uKt, uL} n := by
  refine Uniformity.Density.IFCG73.capstoneHypotheses_of_clusterGeom n hladder
    hdeepTwist hFC hEis ?_ hCL hPCL hLeafSub
  intro e he hDV σ hσ hW hram hcard g n₁ n₂ part h₁ h₂ hsum hmem
  by_cases hd₁ : (⟨part⟩ : FactorizationType).degree = n₁
  · by_cases hd₂ : (⟨σ.data - part⟩ : FactorizationType).degree = n₂
    · exact hCG e he hDV σ hσ hW hram hcard g n₁ n₂ part h₁ h₂ hsum hmem hd₁ hd₂
    · exact visEntryClusterGeom_of_degree_ne σ part (Or.inr hd₂) g
  · exact visEntryClusterGeom_of_degree_ne σ part (Or.inl hd₁) g

end Masters

end Uniformity.Density.IFCG74

end

/-! ## AXCHECK FOOTER — §§1–3, §5's reduction, the degree fires, and §6's per-cell
layer expect PURE Lean core `{propext, Classical.choice, Quot.sound}`.
`visEntryClusterGeom_of_card_le_one` (through VCL's type-support forcing),
`genreCollisionTotal_add_card` (through SDL's/PCD's `1 ≤ multCount`), and the three
recomputed masters inherit Lean core + exactly the owner-signed B.42 cite
`Uniformity.Density.Leaf.exists_slope_factorization`; the capstone master
additionally inherits `Uniformity.Density.Tower.agnprw_termination` (ID12's,
previously declared).  C.33 and `AX_cellRecursion` must NOT occur. -/
#print axioms Uniformity.Density.IFCG74.sum_card_tableSlice
#print axioms Uniformity.Density.IFCG74.card_tableSlice_le_card_depthPairSet
#print axioms Uniformity.Density.IFCG74.decidedSet_eq_empty_of_degree_ne
#print axioms Uniformity.Density.IFCG74.card_shiftedSlice_eq_sum_fiber
#print axioms Uniformity.Density.IFCG74.qpow_mul_sum_clusterCount_univ
#print axioms Uniformity.Density.IFCG74.qpow_mul_cluster_split
#print axioms Uniformity.Density.IFCG74.clusterEntryFam_add_stray
#print axioms Uniformity.Density.IFCG74.visEntryClusterGeom_of_degree_ne
#print axioms Uniformity.Density.IFCG74.visEntryClusterGeom_of_card_le_one
#print axioms Uniformity.Density.IFCG74.visEntryClusterGeom_of_joint_stray
#print axioms Uniformity.Density.IFCG74.pairDepthFiber_eq_cluster_add_late
#print axioms Uniformity.Density.IFCG74.sum_pairDepthFiber_vis_eq_cluster_add_late
#print axioms Uniformity.Density.IFCG74.pairFiber_eq_cluster_late_deep
#print axioms Uniformity.Density.IFCG74.genreCollisionTotal_add_card
#print axioms Uniformity.Density.IFCG74.typeDegree_add_of_le
#print axioms Uniformity.Density.IFCG74.visEntryClusterGeom_of_type_degree_ne
#print axioms Uniformity.Density.IFCG74.visCensusLaw_of_clusterGeom_matched
#print axioms Uniformity.Density.IFCG74.decidedSliceAt_all_of_clusterGeom_matched
#print axioms Uniformity.Density.IFCG74.capstoneHypotheses_of_clusterGeom_matched
