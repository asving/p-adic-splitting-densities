/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import Uniformity.ChapI.IFCG42
import Uniformity.ChapI.IFCG52

/-!
# Uniformity.ChapI.IFCG56 — [RCD 2026-08-31] the split-defect census: the drainage
tiling, the depth-stratum root counts, and the re-base of `CollisionLaw`/`StrayLaw`
onto the visible-sector censuses

Stage RCD of the cone census (design record `runs/wave-c/verdict_RCD.md`; consumes
CSL = `IFCG42` and KDW = `IFCG52`).  CSL's fence left `CollisionLaw`/`StrayLaw` (hence
`SplitConvolutionDefectLaw` at `m ≥ 4` ramified, hence `SplitSectorLaw` via SDL's iff)
resting on exactly two census-side items: (i) the depth-stratum ROOT COUNTS (the
level-`(v+1)` digit-box measure of the depth-`v` strata) and (ii) the DRAINAGE premise
(fiber members decided at the shifted level `N − v`).  This file lands both
mechanisms and re-bases the laws:

* **§1 THE DEPTH TRANSPORT KIT.**  `mixDepth_proj_eq_iff` (the exact-depth reader on
  lifts), `le_mixDepth_proj_iff`, `mixDepth_proj_levels` (the SAME-LIFT cylinder
  transport: the depth-`v` condition at any two levels `> v` reads the same lift
  conditions `π^v ∣ Res ∧ π^{v+1} ∤ Res`) — hence ★ `depthPairSet_eq_preimage`: the
  depth-`v` pair stratum at level `N` is the FULL truncation cylinder over the
  level-`L` stratum for every `v < L ≤ N`, and ★ `card_depthPairSet_levels` /
  `card_depthPairSetGE_levels`: the ROOT COUNTS are level-`(v+1)` digit-box
  quantities, N-FREE (`#stratum(N) = #stratum(L) · q^{(n₁+n₂)(N−L)}`) — CSL's named
  remainder (i), the elementary route into the `|Res|` Igusa distribution.
  Nonvacuity value: ★ `card_depthPairSet_one_one` — at `(n₁, n₂) = (1, 1)` the
  level-`(v+1)` stratum count is EXACTLY `(q−1)·q^{v+1}`, i.e.
  `P[v(Res) = v] = (1 − 1/q)·q^{−v}`, the classical `|Res|` law (via
  `resultant_monicPoly_one_one`: the `(1,1)` pinned resultant is the difference of
  the constant digits).
* **§2 ★★ THE DRAINAGE TILING** (`natCard_shiftedDepthFiber`): at exact mixing depth
  `v` with `2v + 1 ≤ N`, the SHIFTED-DECIDED fiber over a product class `c` — pairs
  whose level-`(N−v)` truncations are decided, with `mulClass = c` and
  `mixDepth = v` — is a DISJOINT UNION of `pairNbhd`s, each of size exactly `q^v`
  (CSL's fiber law): its cardinality is `q^v · #(truncation image)`.  The clusters
  are exactly the fibers of the level-`(N−v)` truncation, and every census attribute
  (product class, mixing depth, shifted decidedness) is constant on each cluster.
  Keyed to RDC's named fiber: `pairDepthFiber_eq_natCard` (the set-currency bridge,
  cast-free) and ★ `qpow_mul_card_le_pairDepthFiber` — `pairDepthFiber` DOMINATES
  `q^v · (cluster roots)`, with §4 certifying that the tiled carrier exhausts it in
  the limit: the charge's "tiling where it closes", on the named object.
* **§3 THE SLICE LAYER.**  ★ `card_shiftedSlice` (the summed tiling): the
  shifted-decided depth-`v` table slice at level `N` is the FULL cylinder over the
  decided depth-`v` slice at level `N − v` — `#slice_S(N) = #(decided ∩ depth-v at
  N−v) · q^{(n₁+n₂)v}`, the level stabilization of the decided census, EXACT.
  `card_tableSlice_le`: the unshifted decided slice exceeds the shifted one by at
  most the two one-sided AMBIGUITY GAPS (possible-not-decided counts at level `N−v`,
  refined up).
* **§4 ★★ THE DRAINAGE PREMISE, CLOSED** (`tendsto_slice_drainage_of_complete`): the
  normalized difference between the decided depth-`v` slice and its shifted-decided
  part tends to `0` — with NO drainage hypothesis: KDW's unconditional
  `drainageAt_all` (IFCG52) supplies `UndecidedVanishes` for both factor types.
  CSL's fence item (ii) is discharged.
* **§5 THE RE-BASE OF THE CENSUS LAWS.**  `VisCountLaw m σ` (the visible-sector cell
  census) and `VisWeightLaw m σ` (the visible-sector multiplicity-weighted census)
  are the two named remaining Props; ★ `collisionLaw_of_visLaws`,
  ★ `strayLaw_of_visWeightLaw`, ★★ `splitConvolutionDefectLaw_of_visCountLaw`,
  ★★ `splitSectorLaw_of_visCountLaw`: `SplitSectorLaw m σ` (every mass, every type)
  now rests on the `< m` decided value laws plus the SINGLE Prop `VisCountLaw m σ`;
  `CollisionLaw`/`StrayLaw` rest on the pair.  FIRST FIRES of the charged Props:
  `collisionLaw_of_mass_le_three` (unconditional), `collisionLaw_unramified`
  (unconditional), `strayLaw_of_mass_le_three`, `strayLaw_unramified` (under the
  `< m` value laws) — every `(m, σ)` except `m ≥ 4` ramified.

## THE HONEST FENCE

NOT proved here: the two named visible-sector censuses `VisCountLaw m σ` /
`VisWeightLaw m σ` at `4 ≤ m`, σ ramified — the exact remaining content of the split
front.  After this file their discharge toolkit is complete on the pair side: the
weight census grades through `pairDepthFiber` (RDC), each depth-`v` graded fiber is
`q^v · (cluster roots)` on its shifted-decided part (§2), the shifted part exhausts
the fiber in the limit (§4), and the cluster roots are N-free level-`(v+1)` box
quantities (§1).  What the two Props still need is the CELL-side structure of the
visible sector (which cells carry how many clusters — the block-decomposition census
of B.42's genre).  The `Σ_v`-interchange (Tannery) for the assembled census is also
deliberately not asserted here.

## Axiom fence (machine-exact at landing)

§§1–4 (the tiling, the root counts, the drainage closure) are PURE Lean core
`{propext, Classical.choice, Quot.sound}` — the fiber law, the gap engine, and KDW's
drainage are all Lean-core.  In §5: `splitConvolutionDefectLaw_of_visCountLaw`,
`splitSectorLaw_of_visCountLaw`, `splitSectorVis_eq_empty_of_mass_le_three`, and
`collisionLaw_of_mass_le_three` are ALSO pure Lean core; exactly the declarations
touching `one_le_multCount_of_vis` / `convCount_eq_card_vis_add_totals` / the
IFCG33 unramified-emptiness route (`collisionTotal_cast`, `strayTotal_cast`,
`collisionLaw_of_visLaws`, `strayLaw_of_visWeightLaw`, `strayLaw_of_mass_le_three`,
`splitSectorVis_eq_empty_unramified`, the two `*_unramified` fires) carry Lean core
+ the owner-signed B.42 cite `Uniformity.Density.Leaf.exists_slope_factorization`
(through SDL/IFCG33) — never re-consumed, inherited only.  The C.33 cites and
`AX_cellRecursion` must NOT occur.  Zero sorries at landing.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

noncomputable section

namespace Uniformity.Density.IFCG56

open IsLocalRing Polynomial Filter Topology
open Uniformity.Density.Induction
open Uniformity.Density.IFCG14 (DecidedValueLaw)
open Uniformity.Density.IFCG24 (ZcURLim ZcURLim_zero card_setOf_resOrd_eq)
open Uniformity.Density.IFCG35 (SplitSectorLaw splitSector)
open Uniformity.Density.IFCG38 (splitSectorVis convPairs convCount mulClassAt
  SplitConvolutionDefectLaw splitSectorLaw_of_defectLaw zcURLim_mul zcURLim_sub
  zcURLim_conv)
open Uniformity.Density.IFCG40 (pairFiber multCount
  splitSector_eq_empty_of_mass_le_three one_le_multCount_of_vis)
open Uniformity.Density.IFCG41 (classRes classRes_proj mixDepth mixDepth_le
  mixDepth_dvd le_mixDepth mk_pow_dvd_mk_iff pairDepthFiber CollisionLaw StrayLaw
  collisionTotal strayTotal convCount_eq_card_vis_add_totals
  exists_bezout_of_not_dvd_resultant mulClass_fiber_gap)
open Uniformity.Density.IFCG42 (pairNbhd natCard_pairNbhd_of_mixDepth
  dvd_resultant_of_mixDepth not_dvd_resultant_of_mixDepth_lt)
open Uniformity.Density.IFCG49 (decidedAt_of_coeffFactor)

/-! ## §0 — supply: the pair truncation map and the counting helpers -/

section Supply

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)]

/-- **The pair truncation map**: both coordinates of a class pair truncated from level
`N` to level `L` — the census's shift map, as one additive homomorphism (so that all
its fibres have the same size). -/
def pairFactor (n₁ n₂ : ℕ) {L N : ℕ} (h : L ≤ N) :
    Coeff O n₁ N × Coeff O n₂ N →+ Coeff O n₁ L × Coeff O n₂ L :=
  AddMonoidHom.prodMap (coeffFactor (O := O) n₁ h) (coeffFactor (O := O) n₂ h)

theorem pairFactor_apply (n₁ n₂ : ℕ) {L N : ℕ} (h : L ≤ N)
    (q : Coeff O n₁ N × Coeff O n₂ N) :
    pairFactor n₁ n₂ h q
      = (coeffFactor (O := O) n₁ h q.1, coeffFactor (O := O) n₂ h q.2) := rfl

theorem pairFactor_proj (n₁ n₂ : ℕ) {L N : ℕ} (h : L ≤ N)
    (a₁ : Fin n₁ → O) (a₂ : Fin n₂ → O) :
    pairFactor n₁ n₂ h (proj O n₁ N a₁, proj O n₂ N a₂)
      = (proj O n₁ L a₁, proj O n₂ L a₂) := rfl

theorem pairFactor_surjective (n₁ n₂ : ℕ) {L N : ℕ} (h : L ≤ N) :
    Function.Surjective (pairFactor (O := O) n₁ n₂ h) := by
  rintro ⟨y₁, y₂⟩
  obtain ⟨x₁, hx₁⟩ := coeffFactor_surjective (O := O) n₁ h y₁
  obtain ⟨x₂, hx₂⟩ := coeffFactor_surjective (O := O) n₂ h y₂
  exact ⟨(x₁, x₂), by rw [pairFactor_apply, hx₁, hx₂]⟩

/-- **The pair-cylinder count**: the `pairFactor`-preimage of a set of level-`L` pairs
is exactly `q^{(n₁+n₂)(N−L)}` times its size. -/
theorem card_preimage_pairFactor (n₁ n₂ : ℕ) {L N : ℕ} (h : L ≤ N)
    (t : Set (Coeff O n₁ L × Coeff O n₂ L)) :
    Nat.card ((pairFactor (O := O) n₁ n₂ h) ⁻¹' t)
      = Nat.card t * residueCard O ^ ((n₁ + n₂) * (N - L)) := by
  have hsurj := pairFactor_surjective (O := O) n₁ n₂ h
  have h1 := card_preimage_of_surjective (pairFactor (O := O) n₁ n₂ h) hsurj t
  have h2 := card_preimage_of_surjective (pairFactor (O := O) n₁ n₂ h) hsurj Set.univ
  rw [Set.preimage_univ, Nat.card_coe_set_eq, Set.ncard_univ,
    Nat.card_coe_set_eq (Set.univ : Set (Coeff O n₁ L × Coeff O n₂ L)),
    Set.ncard_univ] at h2
  rw [Nat.card_prod, Nat.card_prod, card_coeff, card_coeff, card_coeff, card_coeff] at h2
  have hsplit₁ : n₁ * N = n₁ * (N - L) + n₁ * L := by
    rw [← Nat.mul_add, Nat.sub_add_cancel h]
  have hsplit₂ : n₂ * N = n₂ * (N - L) + n₂ * L := by
    rw [← Nat.mul_add, Nat.sub_add_cancel h]
  have hker : Nat.card (pairFactor (O := O) n₁ n₂ h).ker
      = residueCard O ^ ((n₁ + n₂) * (N - L)) := by
    have hqpos : 0 < residueCard O ^ (n₁ * L) * residueCard O ^ (n₂ * L) := by
      have hq := residueCard_pos O
      positivity
    refine Nat.eq_of_mul_eq_mul_right hqpos ?_
    calc Nat.card (pairFactor (O := O) n₁ n₂ h).ker
          * (residueCard O ^ (n₁ * L) * residueCard O ^ (n₂ * L))
        = residueCard O ^ (n₁ * N) * residueCard O ^ (n₂ * N) := by
          rw [h2]
      _ = residueCard O ^ ((n₁ + n₂) * (N - L))
          * (residueCard O ^ (n₁ * L) * residueCard O ^ (n₂ * L)) := by
          rw [hsplit₁, hsplit₂, pow_add, pow_add, add_mul, pow_add]
          ring
  rw [h1, hker, mul_comm]

/-- Level-`s` class equality of lift vectors reads as coefficientwise
`π^s`-divisibility. -/
theorem proj_eq_proj_iff {π : O} (hπ : Irreducible π) {n s : ℕ} (a b : Fin n → O) :
    proj O n s a = proj O n s b ↔ ∀ i, π ^ s ∣ (b i - a i) := by
  have hspan : (maximalIdeal O) ^ s = Ideal.span {π ^ s} := by
    rw [hπ.maximalIdeal_eq, Ideal.span_singleton_pow]
  constructor
  · intro h i
    have h1 : proj O n s a i = proj O n s b i := congrFun h i
    have h2 : a i - b i ∈ (maximalIdeal O) ^ s :=
      (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mp h1
    rw [hspan, Ideal.mem_span_singleton] at h2
    exact dvd_sub_comm.mp h2
  · intro h
    funext i
    show Ideal.Quotient.mk ((maximalIdeal O) ^ s) (a i)
        = Ideal.Quotient.mk ((maximalIdeal O) ^ s) (b i)
    refine (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mpr ?_
    rw [hspan, Ideal.mem_span_singleton]
    exact dvd_sub_comm.mp (h i)

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
/-- Fiberwise decomposition of a set count along any map, indexed by the IMAGE (the
cluster decomposition's counting spine). -/
private theorem natCard_eq_sum_image_fiber {α β : Type*} [Finite α] [Finite β]
    (s : Set α) (φ : α → β) :
    Nat.card s
      = ∑ b ∈ (Set.toFinite (φ '' s)).toFinset, Nat.card ((s ∩ φ ⁻¹' {b} : Set α)) := by
  classical
  letI : Fintype α := Fintype.ofFinite α
  rw [natCard_set_eq_card_filter,
    Finset.card_eq_sum_card_fiberwise (f := φ) (t := (Set.toFinite (φ '' s)).toFinset)
      (fun a ha => (Set.Finite.mem_toFinset _).mpr
        ⟨a, (Finset.mem_filter.mp ha).2, rfl⟩)]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [natCard_set_eq_card_filter, Finset.filter_filter]
  congr 1
  ext a
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Set.mem_inter_iff,
    Set.mem_preimage, Set.mem_singleton_iff]

/-- The count of a set-product is the product of the counts. -/
private theorem natCard_prod_set {α β : Type*} (s : Set α) (t : Set β) :
    Nat.card (s ×ˢ t : Set (α × β)) = Nat.card s * Nat.card t := by
  rw [← Nat.card_prod]
  exact Nat.card_congr (Equiv.Set.prod s t)

/-- The three-set covering bound (finite ambient type). -/
private theorem natCard_le_of_subset_union {α : Type*} [Finite α] {s t u w : Set α}
    (h : s ⊆ t ∪ (u ∪ w)) :
    Nat.card s ≤ Nat.card t + (Nat.card u + Nat.card w) := by
  simp only [Nat.card_coe_set_eq]
  calc s.ncard ≤ (t ∪ (u ∪ w)).ncard := Set.ncard_le_ncard h (Set.toFinite _)
    _ ≤ t.ncard + (u ∪ w).ncard := Set.ncard_union_le _ _
    _ ≤ t.ncard + (u.ncard + w.ncard) :=
        Nat.add_le_add_left (Set.ncard_union_le _ _) _

end Supply

/-! ## §1 — the depth transport kit and the N-FREE root counts (CSL remainder (i)) -/

section DepthTransport

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)]

/-- **The exact-depth reader on lifts**: below the frame cap, `mixDepth = v` is
EXACTLY the pair of lift conditions `π^v ∣ Res ∧ π^{v+1} ∤ Res` — for ANY lift pair.
(This is what makes the depth a digit-box condition.) -/
theorem mixDepth_proj_eq_iff {π : O} (hπ : Irreducible π) {n₁ n₂ N v : ℕ}
    (hvN : v < N) (a₁ : Fin n₁ → O) (a₂ : Fin n₂ → O) :
    mixDepth π (proj O n₁ N a₁) (proj O n₂ N a₂) = v
      ↔ (π ^ v ∣ Polynomial.resultant (monicPoly a₁) (monicPoly a₂) n₁ n₂
          ∧ ¬ π ^ (v + 1) ∣ Polynomial.resultant (monicPoly a₁) (monicPoly a₂) n₁ n₂) := by
  constructor
  · intro hd
    exact ⟨by rw [← hd]; exact dvd_resultant_of_mixDepth hπ a₁ a₂,
      not_dvd_resultant_of_mixDepth_lt hπ hd hvN⟩
  · rintro ⟨h1, h2⟩
    have hle : v ≤ mixDepth π (proj O n₁ N a₁) (proj O n₂ N a₂) := by
      apply le_mixDepth π (le_of_lt hvN)
      rw [classRes_proj]
      exact (mk_pow_dvd_mk_iff hπ (le_of_lt hvN) _).mpr h1
    have hge : mixDepth π (proj O n₁ N a₁) (proj O n₂ N a₂) ≤ v := by
      by_contra hcon
      rw [not_le] at hcon
      exact h2 ((pow_dvd_pow π hcon).trans (dvd_resultant_of_mixDepth hπ a₁ a₂))
    omega

/-- The `≥`-form: at or below the frame cap, `v ≤ mixDepth` is exactly
`π^v ∣ Res` on lifts. -/
theorem le_mixDepth_proj_iff {π : O} (hπ : Irreducible π) {n₁ n₂ N v : ℕ}
    (hvN : v ≤ N) (a₁ : Fin n₁ → O) (a₂ : Fin n₂ → O) :
    v ≤ mixDepth π (proj O n₁ N a₁) (proj O n₂ N a₂)
      ↔ π ^ v ∣ Polynomial.resultant (monicPoly a₁) (monicPoly a₂) n₁ n₂ := by
  constructor
  · intro hle
    exact (pow_dvd_pow π hle).trans (dvd_resultant_of_mixDepth hπ a₁ a₂)
  · intro h1
    apply le_mixDepth π hvN
    rw [classRes_proj]
    exact (mk_pow_dvd_mk_iff hπ hvN _).mpr h1

/-- **The same-lift cylinder transport**: the exact-depth condition reads identically
at every level strictly above `v` — through the SAME lift. -/
theorem mixDepth_proj_levels {π : O} (hπ : Irreducible π) {n₁ n₂ L N v : ℕ}
    (hvL : v < L) (hLN : L ≤ N) (a₁ : Fin n₁ → O) (a₂ : Fin n₂ → O) :
    mixDepth π (proj O n₁ N a₁) (proj O n₂ N a₂) = v
      ↔ mixDepth π (proj O n₁ L a₁) (proj O n₂ L a₂) = v := by
  rw [mixDepth_proj_eq_iff hπ (lt_of_lt_of_le hvL hLN), mixDepth_proj_eq_iff hπ hvL]

/-- The `≥`-form of the cylinder transport. -/
theorem le_mixDepth_proj_levels {π : O} (hπ : Irreducible π) {n₁ n₂ L N v : ℕ}
    (hvL : v ≤ L) (hLN : L ≤ N) (a₁ : Fin n₁ → O) (a₂ : Fin n₂ → O) :
    v ≤ mixDepth π (proj O n₁ N a₁) (proj O n₂ N a₂)
      ↔ v ≤ mixDepth π (proj O n₁ L a₁) (proj O n₂ L a₂) := by
  rw [le_mixDepth_proj_iff hπ (le_trans hvL hLN), le_mixDepth_proj_iff hπ hvL]

/-- **The depth-`v` pair stratum** at level `L`: the class pairs at exact mixing
depth `v` — the ROOT-COUNT carrier. -/
def depthPairSet (O : Type*) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Finite (ResidueField O)] (π : O) (n₁ n₂ L v : ℕ) :
    Set (Coeff O n₁ L × Coeff O n₂ L) :=
  {d | mixDepth π d.1 d.2 = v}

/-- The depth-`≥ v` pair stratum (the tail carrier). -/
def depthPairSetGE (O : Type*) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Finite (ResidueField O)] (π : O) (n₁ n₂ L v : ℕ) :
    Set (Coeff O n₁ L × Coeff O n₂ L) :=
  {d | v ≤ mixDepth π d.1 d.2}

/-- ★ **The depth stratum is a FULL truncation cylinder** over any level `> v`. -/
theorem depthPairSet_eq_preimage {π : O} (hπ : Irreducible π) (n₁ n₂ : ℕ)
    {L N v : ℕ} (hvL : v < L) (hLN : L ≤ N) :
    depthPairSet O π n₁ n₂ N v
      = (pairFactor n₁ n₂ hLN) ⁻¹' (depthPairSet O π n₁ n₂ L v) := by
  ext ⟨q₁, q₂⟩
  obtain ⟨a₁, ha₁⟩ := proj_surjective O n₁ N q₁
  obtain ⟨a₂, ha₂⟩ := proj_surjective O n₂ N q₂
  subst ha₁
  subst ha₂
  simp only [depthPairSet, Set.mem_setOf_eq, Set.mem_preimage, pairFactor_proj]
  exact mixDepth_proj_levels hπ hvL hLN a₁ a₂

/-- The `≥`-form. -/
theorem depthPairSetGE_eq_preimage {π : O} (hπ : Irreducible π) (n₁ n₂ : ℕ)
    {L N v : ℕ} (hvL : v ≤ L) (hLN : L ≤ N) :
    depthPairSetGE O π n₁ n₂ N v
      = (pairFactor n₁ n₂ hLN) ⁻¹' (depthPairSetGE O π n₁ n₂ L v) := by
  ext ⟨q₁, q₂⟩
  obtain ⟨a₁, ha₁⟩ := proj_surjective O n₁ N q₁
  obtain ⟨a₂, ha₂⟩ := proj_surjective O n₂ N q₂
  subst ha₁
  subst ha₂
  simp only [depthPairSetGE, Set.mem_setOf_eq, Set.mem_preimage, pairFactor_proj]
  exact le_mixDepth_proj_levels hπ hvL hLN a₁ a₂

/-- ★ **THE ROOT COUNTS ARE N-FREE** (CSL's named remainder (i), the digit-box form):
the depth-`v` stratum count at any level `N ≥ L > v` is the level-`L` count times the
full cylinder factor — in particular the level-`(v+1)` digit box determines every
level.  This is the elementary route into the `|Res|` Igusa distribution: the
remaining census inputs are the FIXED-LEVEL box counts `#depthPairSet(v+1, v)`. -/
theorem card_depthPairSet_levels {π : O} (hπ : Irreducible π) (n₁ n₂ : ℕ)
    {L N v : ℕ} (hvL : v < L) (hLN : L ≤ N) :
    Nat.card (depthPairSet O π n₁ n₂ N v)
      = Nat.card (depthPairSet O π n₁ n₂ L v) * residueCard O ^ ((n₁ + n₂) * (N - L)) := by
  rw [depthPairSet_eq_preimage hπ n₁ n₂ hvL hLN, card_preimage_pairFactor]

/-- The `≥`-form (the tail instrument). -/
theorem card_depthPairSetGE_levels {π : O} (hπ : Irreducible π) (n₁ n₂ : ℕ)
    {L N v : ℕ} (hvL : v ≤ L) (hLN : L ≤ N) :
    Nat.card (depthPairSetGE O π n₁ n₂ N v)
      = Nat.card (depthPairSetGE O π n₁ n₂ L v)
        * residueCard O ^ ((n₁ + n₂) * (N - L)) := by
  rw [depthPairSetGE_eq_preimage hπ n₁ n₂ hvL hLN, card_preimage_pairFactor]

/-- The degree-one monic frame is a linear polynomial. -/
private theorem monicPoly_one_eq (z : Fin 1 → O) :
    monicPoly z = Polynomial.X - Polynomial.C (-(z 0)) := by
  unfold monicPoly
  rw [map_neg, sub_neg_eq_add, pow_one, Fin.sum_univ_one]
  norm_num

/-- The pinned-size `(1,1)` resultant of two monic linears is the difference of the
constant coefficients. -/
theorem resultant_monicPoly_one_one (a b : Fin 1 → O) :
    Polynomial.resultant (monicPoly a) (monicPoly b) 1 1 = b 0 - a 0 := by
  rw [monicPoly_one_eq a, ← pow_one (Polynomial.X - Polynomial.C (-(a 0)))]
  rw [Polynomial.resultant_X_sub_C_pow_left (-(a 0)) (monicPoly b) 1 1
    (le_of_eq (monicPoly_natDegree b))]
  rw [pow_one, monicPoly_one_eq b]
  simp
  ring

/-- ★ **THE `(1,1)` ROOT-COUNT VALUE** (the nonvacuity witness of the instrument
genre): at the pinned level `v + 1`, the depth-`v` stratum of monic-linear pairs has
EXACTLY `(q − 1) · q^{v+1}` members — the classical `|Res|`-distribution
`P[v(Res) = v] = (1 − 1/q) · q^{−v}`, read as a digit-box count (every level then
follows by `card_depthPairSet_levels`). -/
theorem card_depthPairSet_one_one {π : O} (hπ : Irreducible π) (v : ℕ) :
    Nat.card (depthPairSet O π 1 1 (v + 1) v)
      = (residueCard O - 1) * residueCard O ^ (v + 1) := by
  classical
  -- the constant-coefficient difference map
  set φ : (Coeff O 1 (v + 1) × Coeff O 1 (v + 1)) →+ Res O (v + 1) :=
    { toFun := fun q => q.2 0 - q.1 0
      map_zero' := by simp
      map_add' := by
        intro x y
        show (x.2 + y.2) 0 - (x.1 + y.1) 0 = _
        rw [Pi.add_apply, Pi.add_apply]
        ring }
  have hφ_apply : ∀ q : Coeff O 1 (v + 1) × Coeff O 1 (v + 1),
      φ q = q.2 0 - q.1 0 := fun _ => rfl
  have hsurj : Function.Surjective φ := by
    intro z
    exact ⟨((fun _ => 0 : Coeff O 1 (v + 1)), (fun _ => z : Coeff O 1 (v + 1))), by
      rw [hφ_apply]; exact sub_zero z⟩
  -- the stratum is the `φ`-preimage of the exact-order digit set
  have hset : depthPairSet O π 1 1 (v + 1) v
      = φ ⁻¹' {z : Res O (v + 1) | resOrd z = v} := by
    ext ⟨c₁, c₂⟩
    obtain ⟨a, ha⟩ := proj_surjective O 1 (v + 1) c₁
    obtain ⟨b, hb⟩ := proj_surjective O 1 (v + 1) c₂
    subst ha
    subst hb
    simp only [depthPairSet, Set.mem_setOf_eq, Set.mem_preimage]
    rw [mixDepth_proj_eq_iff hπ (Nat.lt_succ_self v),
      resultant_monicPoly_one_one a b]
    have hφab : φ (proj O 1 (v + 1) a, proj O 1 (v + 1) b)
        = Ideal.Quotient.mk ((maximalIdeal O) ^ (v + 1)) (b 0 - a 0) := by
      rw [hφ_apply]
      exact (map_sub (Ideal.Quotient.mk ((maximalIdeal O) ^ (v + 1))) (b 0) (a 0)).symm
    rw [hφab]
    have hle := resOrd_le (Ideal.Quotient.mk ((maximalIdeal O) ^ (v + 1)) (b 0 - a 0))
    constructor
    · rintro ⟨h1, h2⟩
      have hge : v ≤ resOrd (Ideal.Quotient.mk ((maximalIdeal O) ^ (v + 1)) (b 0 - a 0)) :=
        (resOrd_ge_iff hπ (by omega) _).mpr h1
      have hlt : ¬ (v + 1 ≤ resOrd (Ideal.Quotient.mk ((maximalIdeal O) ^ (v + 1)) (b 0 - a 0))) :=
        fun hcon => h2 ((resOrd_ge_iff hπ le_rfl _).mp hcon)
      omega
    · intro h
      refine ⟨(resOrd_ge_iff hπ (by omega) _).mp (le_of_eq h.symm), fun hcon => ?_⟩
      have := (resOrd_ge_iff hπ le_rfl _).mpr hcon
      omega
  rw [hset, card_preimage_of_surjective φ hsurj,
    card_setOf_resOrd_eq (by omega : v < v + 1)]
  -- the kernel size: solve against the full box
  have h2 := card_preimage_of_surjective φ hsurj Set.univ
  rw [Set.preimage_univ, Nat.card_coe_set_eq, Set.ncard_univ,
    Nat.card_coe_set_eq (Set.univ : Set (Res O (v + 1))), Set.ncard_univ,
    Nat.card_prod, card_coeff, card_res] at h2
  have hker : Nat.card φ.ker = residueCard O ^ (v + 1) := by
    have hqpos : 0 < residueCard O ^ (v + 1) := pow_pos (residueCard_pos O) _
    refine Nat.eq_of_mul_eq_mul_right hqpos ?_
    rw [← h2, one_mul]
  rw [hker]
  have hexp : v + 1 - v - 1 = 0 := by omega
  rw [hexp, pow_zero, mul_one]
  ring

end DepthTransport

/-! ## §2 — ★★ THE DRAINAGE TILING (the per-cell cluster decomposition) -/

section Tiling

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)]

/-- The `(σ₁, σ₂)`-decided pair set at level `L`. -/
def decidedPairSet (O : Type*) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Finite (ResidueField O)] (n₁ n₂ : ℕ) (σ₁ σ₂ : FactorizationType) (L : ℕ) :
    Set (Coeff O n₁ L × Coeff O n₂ L) :=
  (decidedSet O n₁ σ₁ L) ×ˢ (decidedSet O n₂ σ₂ L)

/-- **The shifted-decided depth-`v` fiber over a product class `c`**: the level-`N`
pairs whose level-`(N−v)` truncations are `(σ₁, σ₂)`-decided, with product class `c`
and mixing depth exactly `v` — `pairDepthFiber`'s carrier with the decidedness read
at the SHIFTED level (the drainage-premise form; shifted decidedness implies full
decidedness by `decidedAt_of_coeffFactor`). -/
def shiftedDepthFiber (O : Type*) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [Finite (ResidueField O)] (π : O) (n₁ n₂ : ℕ)
    (σ₁ σ₂ : FactorizationType) (N v : ℕ) (c : Coeff O (n₁ + n₂) N) :
    Set (Coeff O n₁ N × Coeff O n₂ N) :=
  {q | pairFactor n₁ n₂ (Nat.sub_le N v) q
        ∈ decidedPairSet O n₁ n₂ σ₁ σ₂ (N - v)
      ∧ mulClass q.1 q.2 = c ∧ mixDepth π q.1 q.2 = v}

/-- **The cluster identification**: within the shifted-decided depth-`v` fiber over
`c`, the truncation fiber through any member IS that member's `pairNbhd` — the
`q^v`-cluster of CSL's fiber law.  (Forward: truncation agreement at `N−v` refines to
`π^{v+1}`-congruence since `v+1 ≤ N−v`; backward: the gap engine pins `pairNbhd`
members mod `π^{N−v}`, and every census attribute transports along the same-lift
cylinder.) -/
theorem shiftedDepthFiber_inter_eq_pairNbhd {π : O} (hπ : Irreducible π)
    {n₁ n₂ N v : ℕ} (hN : 2 * v + 1 ≤ N) (hpos : n₁ ≠ 0 ∨ n₂ ≠ 0)
    {σ₁ σ₂ : FactorizationType} {c : Coeff O (n₁ + n₂) N}
    {q₀ : Coeff O n₁ N × Coeff O n₂ N}
    (hq₀ : q₀ ∈ shiftedDepthFiber O π n₁ n₂ σ₁ σ₂ N v c)
    {a₁ : Fin n₁ → O} {a₂ : Fin n₂ → O}
    (ha₁ : proj O n₁ N a₁ = q₀.1) (ha₂ : proj O n₂ N a₂ = q₀.2) :
    shiftedDepthFiber O π n₁ n₂ σ₁ σ₂ N v c
        ∩ (pairFactor n₁ n₂ (Nat.sub_le N v)) ⁻¹'
            {pairFactor n₁ n₂ (Nat.sub_le N v) q₀}
      = pairNbhd π N v a₁ a₂ := by
  obtain ⟨hq₀dec, hq₀mul, hq₀dep⟩ := hq₀
  -- the base pair's depth data, read on the chosen lifts
  have hdepa : mixDepth π (proj O n₁ N a₁) (proj O n₂ N a₂) = v := by
    rw [ha₁, ha₂]; exact hq₀dep
  have hres : ¬ π ^ (v + 1)
      ∣ Polynomial.resultant (monicPoly a₁) (monicPoly a₂) n₁ n₂ :=
    not_dvd_resultant_of_mixDepth_lt hπ hdepa (by omega)
  have hbez := exists_bezout_of_not_dvd_resultant hπ
    (monicPoly_natDegree a₁).le (monicPoly_natDegree a₂).le hpos hres
  have hdepaL : mixDepth π (proj O n₁ (N - v) a₁) (proj O n₂ (N - v) a₂) = v :=
    (mixDepth_proj_levels hπ (by omega) (Nat.sub_le N v) a₁ a₂).mp hdepa
  have hprodA : mulClass (proj O n₁ N a₁) (proj O n₂ N a₂) = c := by
    rw [ha₁, ha₂]; exact hq₀mul
  have hq₀eq : q₀ = (proj O n₁ N a₁, proj O n₂ N a₂) := by rw [ha₁, ha₂]
  have hPq₀ : pairFactor n₁ n₂ (Nat.sub_le N v) q₀
      = (proj O n₁ (N - v) a₁, proj O n₂ (N - v) a₂) := by
    rw [hq₀eq, pairFactor_proj]
  ext ⟨q₁, q₂⟩
  constructor
  · -- the truncation fiber refines into the `π^{v+1}` neighborhood
    rintro ⟨⟨hdec, hmul, hdep⟩, hproj⟩
    have hprojEq : pairFactor n₁ n₂ (Nat.sub_le N v) (q₁, q₂)
        = pairFactor n₁ n₂ (Nat.sub_le N v) q₀ := hproj
    obtain ⟨b₁, hb₁⟩ := proj_surjective O n₁ N q₁
    obtain ⟨b₂, hb₂⟩ := proj_surjective O n₂ N q₂
    have hPq : pairFactor n₁ n₂ (Nat.sub_le N v) (q₁, q₂)
        = (proj O n₁ (N - v) b₁, proj O n₂ (N - v) b₂) := by
      rw [← hb₁, ← hb₂, pairFactor_proj]
    rw [hPq, hPq₀, Prod.mk.injEq] at hprojEq
    have hc₁ : ∀ i, π ^ (v + 1) ∣ (b₁ i - a₁ i) := fun i =>
      (pow_dvd_pow π (by omega : v + 1 ≤ N - v)).trans
        (dvd_sub_comm.mp ((proj_eq_proj_iff hπ b₁ a₁).mp hprojEq.1 i))
    have hc₂ : ∀ i, π ^ (v + 1) ∣ (b₂ i - a₂ i) := fun i =>
      (pow_dvd_pow π (by omega : v + 1 ≤ N - v)).trans
        (dvd_sub_comm.mp ((proj_eq_proj_iff hπ b₂ a₂).mp hprojEq.2 i))
    exact ⟨hmul.trans hprodA.symm, ⟨b₁, hb₁, hc₁⟩, ⟨b₂, hb₂, hc₂⟩⟩
  · -- the gap engine pins neighborhood members inside the truncation fiber
    rintro ⟨hmulEq, ⟨b₁, hb₁, hcong₁⟩, ⟨b₂, hb₂, hcong₂⟩⟩
    have hb₁' : proj O n₁ N b₁ = q₁ := hb₁
    have hb₂' : proj O n₂ N b₂ = q₂ := hb₂
    have hmulEq' : mulClass q₁ q₂ = mulClass (proj O n₁ N a₁) (proj O n₂ N a₂) := hmulEq
    have heq : mulClass (proj O n₁ N a₁) (proj O n₂ N a₂)
        = mulClass (proj O n₁ N b₁) (proj O n₂ N b₂) := by
      rw [hb₁', hb₂']; exact hmulEq'.symm
    have hgap := mulClass_fiber_gap hπ hbez hcong₁ hcong₂ heq
    have htrunc₁ : proj O n₁ (N - v) a₁ = proj O n₁ (N - v) b₁ :=
      (proj_eq_proj_iff hπ a₁ b₁).mpr hgap.1
    have htrunc₂ : proj O n₂ (N - v) a₂ = proj O n₂ (N - v) b₂ :=
      (proj_eq_proj_iff hπ a₂ b₂).mpr hgap.2
    have hkey : pairFactor n₁ n₂ (Nat.sub_le N v) (q₁, q₂)
        = pairFactor n₁ n₂ (Nat.sub_le N v) q₀ := by
      rw [← hb₁', ← hb₂', pairFactor_proj, hPq₀, ← htrunc₁, ← htrunc₂]
    refine ⟨⟨?_, ?_, ?_⟩, hkey⟩
    · show pairFactor n₁ n₂ (Nat.sub_le N v) (q₁, q₂) ∈ decidedPairSet O n₁ n₂ σ₁ σ₂ (N - v)
      rw [hkey]
      exact hq₀dec
    · exact hmulEq'.trans hprodA
    · show mixDepth π q₁ q₂ = v
      rw [← hb₁', ← hb₂']
      refine (mixDepth_proj_levels hπ (by omega : v < N - v) (Nat.sub_le N v) b₁ b₂).mpr ?_
      rw [← htrunc₁, ← htrunc₂]
      exact hdepaL

/-- ★★ **THE DRAINAGE TILING** (CSL's fence, both items in one stroke on the shifted
carrier): at exact mixing depth `v` with `2v + 1 ≤ N`, the shifted-decided fiber over
any product class is a disjoint union of `q^v`-clusters — one per level-`(N−v)`
truncation image point — so its count is EXACTLY `q^v` times the cluster-root count. -/
theorem natCard_shiftedDepthFiber {π : O} (hπ : Irreducible π) {n₁ n₂ N v : ℕ}
    (hN : 2 * v + 1 ≤ N) (hpos : n₁ ≠ 0 ∨ n₂ ≠ 0)
    (σ₁ σ₂ : FactorizationType) (c : Coeff O (n₁ + n₂) N) :
    Nat.card (shiftedDepthFiber O π n₁ n₂ σ₁ σ₂ N v c)
      = residueCard O ^ v
        * Nat.card ((pairFactor n₁ n₂ (Nat.sub_le N v)) ''
            (shiftedDepthFiber O π n₁ n₂ σ₁ σ₂ N v c)) := by
  classical
  rw [natCard_eq_sum_image_fiber (shiftedDepthFiber O π n₁ n₂ σ₁ σ₂ N v c)
    (pairFactor n₁ n₂ (Nat.sub_le N v))]
  have hsum : ∀ b ∈ (Set.toFinite ((pairFactor n₁ n₂ (Nat.sub_le N v)) ''
      (shiftedDepthFiber O π n₁ n₂ σ₁ σ₂ N v c))).toFinset,
      Nat.card ((shiftedDepthFiber O π n₁ n₂ σ₁ σ₂ N v c
          ∩ (pairFactor n₁ n₂ (Nat.sub_le N v)) ⁻¹' {b} : Set _))
        = residueCard O ^ v := by
    intro b hb
    obtain ⟨q₀, hq₀S, hq₀b⟩ := (Set.Finite.mem_toFinset _).mp hb
    obtain ⟨a₁, ha₁⟩ := proj_surjective O n₁ N q₀.1
    obtain ⟨a₂, ha₂⟩ := proj_surjective O n₂ N q₀.2
    rw [← hq₀b,
      shiftedDepthFiber_inter_eq_pairNbhd hπ hN hpos hq₀S ha₁ ha₂]
    refine natCard_pairNbhd_of_mixDepth hπ hN hpos ?_
    rw [ha₁, ha₂]
    exact hq₀S.2.2
  rw [Finset.sum_congr rfl hsum, Finset.sum_const, smul_eq_mul, mul_comm]
  congr 1
  rw [Nat.card_coe_set_eq, Set.ncard_eq_toFinset_card]

/-- **The keyed bridge to RDC's `pairDepthFiber`**: the depth-graded pair fiber is the
count of the decided depth-`v` `mulClass` fiber, in this file's set currency. -/
theorem pairDepthFiber_eq_natCard (π : O) {m : ℕ} (σ : FactorizationType) (M : ℕ)
    (p : (ℕ × ℕ) × Multiset (ℕ × ℕ)) (hpm : p.1.1 + p.1.2 = m)
    (c : Coeff O m (M + m)) (v : ℕ) :
    pairDepthFiber O π m σ M p c v
      = Nat.card ((decidedPairSet O p.1.1 p.1.2 ⟨p.2⟩ ⟨σ.data - p.2⟩ (M + m)
          ∩ {q | mulClassAt hpm q.1 q.2 = c}
          ∩ depthPairSet O π p.1.1 p.1.2 (M + m) v
          : Set (Coeff O p.1.1 (M + m) × Coeff O p.1.2 (M + m)))) := by
  unfold pairDepthFiber
  rw [dif_pos hpm]
  congr 1

/-- ★ **THE TILED LOWER BOUND ON `pairDepthFiber`** (the drainage tiling read on RDC's
named fiber, cast-free at the pinned mass split `m = n₁ + n₂`): the graded fiber
DOMINATES `q^v` times its shifted-decided cluster-root count — the tiling closes on
the shifted carrier, and §4's drainage limit certifies that the shifted carrier
exhausts the fiber as `M → ∞`. -/
theorem qpow_mul_card_le_pairDepthFiber {π : O} (hπ : Irreducible π)
    (σ : FactorizationType) (M : ℕ) {n₁ n₂ : ℕ} (part : Multiset (ℕ × ℕ))
    (c : Coeff O (n₁ + n₂) (M + (n₁ + n₂))) {v : ℕ}
    (hN : 2 * v + 1 ≤ M + (n₁ + n₂)) (hpos : n₁ ≠ 0 ∨ n₂ ≠ 0) :
    residueCard O ^ v
        * Nat.card ((pairFactor n₁ n₂ (Nat.sub_le (M + (n₁ + n₂)) v)) ''
            (shiftedDepthFiber O π n₁ n₂ ⟨part⟩ ⟨σ.data - part⟩ (M + (n₁ + n₂)) v c))
      ≤ pairDepthFiber O π (n₁ + n₂) σ M ((n₁, n₂), part) c v := by
  rw [pairDepthFiber_eq_natCard π σ M ((n₁, n₂), part) rfl c v,
    ← natCard_shiftedDepthFiber hπ hN hpos ⟨part⟩ ⟨σ.data - part⟩ c]
  have hsub : shiftedDepthFiber O π n₁ n₂ ⟨part⟩ ⟨σ.data - part⟩ (M + (n₁ + n₂)) v c
      ⊆ (decidedPairSet O n₁ n₂ ⟨part⟩ ⟨σ.data - part⟩ (M + (n₁ + n₂))
          ∩ {q | mulClassAt rfl q.1 q.2 = c}
          ∩ depthPairSet O π n₁ n₂ (M + (n₁ + n₂)) v) := by
    rintro q ⟨hdec, hmul, hdep⟩
    exact ⟨⟨⟨decidedAt_of_coeffFactor (Nat.sub_le _ v) hdec.1,
      decidedAt_of_coeffFactor (Nat.sub_le _ v) hdec.2⟩, hmul⟩, hdep⟩
  rw [Nat.card_coe_set_eq, Nat.card_coe_set_eq]
  exact Set.ncard_le_ncard hsub (Set.toFinite _)

end Tiling

/-! ## §3 — the slice layer: the summed tiling and the gap bound -/

section Slices

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)]

/-- **The decided depth-`v` table slice** at level `N`: decided pairs at exact mixing
depth `v` — the depth-`v` grade of the convolution table (one `convPairs` entry). -/
def tableSlice (O : Type*) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Finite (ResidueField O)] (π : O) (n₁ n₂ : ℕ) (σ₁ σ₂ : FactorizationType)
    (N v : ℕ) : Set (Coeff O n₁ N × Coeff O n₂ N) :=
  decidedPairSet O n₁ n₂ σ₁ σ₂ N ∩ depthPairSet O π n₁ n₂ N v

/-- **The shifted-decided depth-`v` table slice** at level `N` (decidedness read at
level `N − v`). -/
def shiftedSlice (O : Type*) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Finite (ResidueField O)] (π : O) (n₁ n₂ : ℕ) (σ₁ σ₂ : FactorizationType)
    (N v : ℕ) : Set (Coeff O n₁ N × Coeff O n₂ N) :=
  {q | pairFactor n₁ n₂ (Nat.sub_le N v) q ∈ decidedPairSet O n₁ n₂ σ₁ σ₂ (N - v)
      ∧ mixDepth π q.1 q.2 = v}

/-- The shifted slice is the FULL truncation cylinder over the level-`(N−v)` decided
depth-`v` slice. -/
theorem shiftedSlice_eq_preimage {π : O} (hπ : Irreducible π) {n₁ n₂ N v : ℕ}
    (hN : 2 * v + 1 ≤ N) (σ₁ σ₂ : FactorizationType) :
    shiftedSlice O π n₁ n₂ σ₁ σ₂ N v
      = (pairFactor n₁ n₂ (Nat.sub_le N v)) ⁻¹'
          (decidedPairSet O n₁ n₂ σ₁ σ₂ (N - v) ∩ depthPairSet O π n₁ n₂ (N - v) v) := by
  ext ⟨q₁, q₂⟩
  obtain ⟨a₁, ha₁⟩ := proj_surjective O n₁ N q₁
  obtain ⟨a₂, ha₂⟩ := proj_surjective O n₂ N q₂
  subst ha₁
  subst ha₂
  simp only [shiftedSlice, depthPairSet, Set.mem_setOf_eq, Set.mem_preimage,
    Set.mem_inter_iff, pairFactor_proj]
  exact and_congr_right fun _ =>
    mixDepth_proj_levels hπ (by omega : v < N - v) (Nat.sub_le N v) a₁ a₂

/-- ★ **THE SUMMED TILING — the level stabilization of the decided census**: the
shifted-decided depth-`v` slice at level `N` counts the decided depth-`v` slice at
level `N − v`, times the exact cylinder factor. -/
theorem card_shiftedSlice {π : O} (hπ : Irreducible π) {n₁ n₂ N v : ℕ}
    (hN : 2 * v + 1 ≤ N) (σ₁ σ₂ : FactorizationType) :
    Nat.card (shiftedSlice O π n₁ n₂ σ₁ σ₂ N v)
      = Nat.card (tableSlice O π n₁ n₂ σ₁ σ₂ (N - v) v)
        * residueCard O ^ ((n₁ + n₂) * v) := by
  rw [shiftedSlice_eq_preimage hπ hN σ₁ σ₂, card_preimage_pairFactor]
  have hexp : N - (N - v) = v := by omega
  rw [hexp]
  rfl

/-- Shifted decidedness implies full decidedness (`decidedAt_of_coeffFactor`): the
shifted slice sits inside the table slice. -/
theorem shiftedSlice_subset_tableSlice {π : O} {n₁ n₂ N v : ℕ}
    (σ₁ σ₂ : FactorizationType) :
    shiftedSlice O π n₁ n₂ σ₁ σ₂ N v ⊆ tableSlice O π n₁ n₂ σ₁ σ₂ N v := by
  rintro q ⟨hdec, hdep⟩
  exact ⟨⟨decidedAt_of_coeffFactor (Nat.sub_le N v) hdec.1,
    decidedAt_of_coeffFactor (Nat.sub_le N v) hdec.2⟩, hdep⟩

/-- **The gap bound**: the table slice exceeds its shifted part by at most the two
one-sided ambiguity gaps at level `N − v`, refined up — the count of level-`N`
decided classes whose truncation is still ambiguous. -/
theorem card_tableSlice_le {π : O} {n₁ n₂ N v : ℕ}
    (hvN : v ≤ N) (σ₁ σ₂ : FactorizationType) :
    Nat.card (tableSlice O π n₁ n₂ σ₁ σ₂ N v)
      ≤ Nat.card (shiftedSlice O π n₁ n₂ σ₁ σ₂ N v)
        + ((possibleCount O n₁ σ₁ (N - v) - decidedCount O n₁ σ₁ (N - v))
              * residueCard O ^ (n₁ * v) * residueCard O ^ (n₂ * N)
          + (possibleCount O n₂ σ₂ (N - v) - decidedCount O n₂ σ₂ (N - v))
              * residueCard O ^ (n₂ * v) * residueCard O ^ (n₁ * N)) := by
  classical
  -- the two one-sided ambiguity carriers
  have hsub : tableSlice O π n₁ n₂ σ₁ σ₂ N v
      ⊆ shiftedSlice O π n₁ n₂ σ₁ σ₂ N v
        ∪ ((((coeffFactor (O := O) n₁ (Nat.sub_le N v)) ⁻¹'
              (possibleSet O n₁ σ₁ (N - v) \ decidedSet O n₁ σ₁ (N - v))) ×ˢ Set.univ)
          ∪ (Set.univ ×ˢ ((coeffFactor (O := O) n₂ (Nat.sub_le N v)) ⁻¹'
              (possibleSet O n₂ σ₂ (N - v) \ decidedSet O n₂ σ₂ (N - v))))) := by
    rintro ⟨q₁, q₂⟩ ⟨⟨hd₁, hd₂⟩, hdep⟩
    by_cases hs : (⟨q₁, q₂⟩ : Coeff O n₁ N × Coeff O n₂ N)
        ∈ shiftedSlice O π n₁ n₂ σ₁ σ₂ N v
    · exact Or.inl hs
    · right
      have hnot : ¬ (coeffFactor (O := O) n₁ (Nat.sub_le N v) q₁
            ∈ decidedSet O n₁ σ₁ (N - v)
          ∧ coeffFactor (O := O) n₂ (Nat.sub_le N v) q₂
            ∈ decidedSet O n₂ σ₂ (N - v)) := by
        intro hcon
        exact hs ⟨hcon, hdep⟩
      have hp₁ : coeffFactor (O := O) n₁ (Nat.sub_le N v) q₁
          ∈ possibleSet O n₁ σ₁ (N - v) := by
        obtain ⟨a, ha⟩ := proj_surjective O n₁ N q₁
        refine ⟨a, ?_, hd₁ a ha⟩
        rw [← ha]
        rfl
      have hp₂ : coeffFactor (O := O) n₂ (Nat.sub_le N v) q₂
          ∈ possibleSet O n₂ σ₂ (N - v) := by
        obtain ⟨a, ha⟩ := proj_surjective O n₂ N q₂
        refine ⟨a, ?_, hd₂ a ha⟩
        rw [← ha]
        rfl
      rcases not_and_or.mp hnot with h1 | h1
      · exact Or.inl ⟨⟨hp₁, h1⟩, Set.mem_univ _⟩
      · exact Or.inr ⟨Set.mem_univ _, ⟨hp₂, h1⟩⟩
  -- count the covering
  have hgap₁ : Nat.card ((possibleSet O n₁ σ₁ (N - v) \ decidedSet O n₁ σ₁ (N - v)
      : Set (Coeff O n₁ (N - v))))
      = possibleCount O n₁ σ₁ (N - v) - decidedCount O n₁ σ₁ (N - v) := by
    rw [Nat.card_coe_set_eq,
      Set.ncard_sdiff (decidedSet_subset_possibleSet n₁ σ₁ (N - v)),
      ← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq]
    rfl
  have hgap₂ : Nat.card ((possibleSet O n₂ σ₂ (N - v) \ decidedSet O n₂ σ₂ (N - v)
      : Set (Coeff O n₂ (N - v))))
      = possibleCount O n₂ σ₂ (N - v) - decidedCount O n₂ σ₂ (N - v) := by
    rw [Nat.card_coe_set_eq,
      Set.ncard_sdiff (decidedSet_subset_possibleSet n₂ σ₂ (N - v)),
      ← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq]
    rfl
  have hB₁ : Nat.card ((((coeffFactor (O := O) n₁ (Nat.sub_le N v)) ⁻¹'
        (possibleSet O n₁ σ₁ (N - v) \ decidedSet O n₁ σ₁ (N - v))) ×ˢ
        (Set.univ : Set (Coeff O n₂ N)) : Set (Coeff O n₁ N × Coeff O n₂ N)))
      = (possibleCount O n₁ σ₁ (N - v) - decidedCount O n₁ σ₁ (N - v))
          * residueCard O ^ (n₁ * v) * residueCard O ^ (n₂ * N) := by
    rw [natCard_prod_set, Uniformity.Density.IFCG46.card_preimage_coeffFactor_eq,
      hgap₁]
    have hexp : N - (N - v) = v := by omega
    rw [hexp, Nat.card_coe_set_eq, Set.ncard_univ, card_coeff]
  have hB₂ : Nat.card (((Set.univ : Set (Coeff O n₁ N)) ×ˢ
        ((coeffFactor (O := O) n₂ (Nat.sub_le N v)) ⁻¹'
          (possibleSet O n₂ σ₂ (N - v) \ decidedSet O n₂ σ₂ (N - v)))
        : Set (Coeff O n₁ N × Coeff O n₂ N)))
      = (possibleCount O n₂ σ₂ (N - v) - decidedCount O n₂ σ₂ (N - v))
          * residueCard O ^ (n₂ * v) * residueCard O ^ (n₁ * N) := by
    rw [natCard_prod_set, Uniformity.Density.IFCG46.card_preimage_coeffFactor_eq,
      hgap₂]
    have hexp : N - (N - v) = v := by omega
    rw [hexp, Nat.card_coe_set_eq, Set.ncard_univ, card_coeff]
    ring
  refine le_trans (natCard_le_of_subset_union hsub) ?_
  rw [hB₁, hB₂]

end Slices

/-! ## §4 — ★★ THE DRAINAGE PREMISE, CLOSED -/

section Drainage

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)]

/-- **The drainage limit** (hypothesis form): under `UndecidedVanishes` for both
factor types, the normalized gap between the decided depth-`v` slice and its
shifted-decided part drains to `0` as the level diverges (depth `v` fixed). -/
theorem tendsto_slice_drainage {π : O} (n₁ n₂ : ℕ)
    (σ₁ σ₂ : FactorizationType) (v : ℕ)
    (hUV₁ : UndecidedVanishes O n₁ σ₁) (hUV₂ : UndecidedVanishes O n₂ σ₂) :
    Tendsto (fun N =>
        ((Nat.card (tableSlice O π n₁ n₂ σ₁ σ₂ N v) : ℝ)
            - (Nat.card (shiftedSlice O π n₁ n₂ σ₁ σ₂ N v) : ℝ))
          / (residueCard O : ℝ) ^ ((n₁ + n₂) * N))
      atTop (nhds 0) := by
  have hq2 : 2 ≤ residueCard O := two_le_residueCard O
  have hq0 : (0 : ℝ) < (residueCard O : ℝ) := by exact_mod_cast (by omega : 0 < residueCard O)
  -- the drained bounding sequence
  have hbound : Tendsto (fun N : ℕ => gapSeq O n₁ σ₁ (N - v) + gapSeq O n₂ σ₂ (N - v))
      atTop (nhds 0) := by
    have h1 := hUV₁.comp (tendsto_sub_atTop_nat v)
    have h2 := hUV₂.comp (tendsto_sub_atTop_nat v)
    simpa using h1.add h2
  refine squeeze_zero' ?_ ?_ hbound
  · -- nonnegativity: the shifted slice sits inside the table slice
    refine Filter.Eventually.of_forall fun N => ?_
    apply div_nonneg _ (by positivity)
    rw [sub_nonneg]
    have hle : Nat.card (shiftedSlice O π n₁ n₂ σ₁ σ₂ N v)
        ≤ Nat.card (tableSlice O π n₁ n₂ σ₁ σ₂ N v) := by
      rw [Nat.card_coe_set_eq, Nat.card_coe_set_eq]
      exact Set.ncard_le_ncard (shiftedSlice_subset_tableSlice σ₁ σ₂) (Set.toFinite _)
    exact_mod_cast hle
  · -- the gap bound, eventually (`N ≥ v`)
    refine Filter.eventually_atTop.mpr ⟨v, fun N hvN => ?_⟩
    have hdle₁ := decidedCount_le_possibleCount (O := O) n₁ σ₁ (N - v)
    have hdle₂ := decidedCount_le_possibleCount (O := O) n₂ σ₂ (N - v)
    have hsplit₁ : n₁ * N = n₁ * (N - v) + n₁ * v := by
      rw [← Nat.mul_add, Nat.sub_add_cancel hvN]
    have hsplit₂ : n₂ * N = n₂ * (N - v) + n₂ * v := by
      rw [← Nat.mul_add, Nat.sub_add_cancel hvN]
    -- the two normalized error terms ARE the ambiguity gaps at the shifted level
    have hE₁ : ((possibleCount O n₁ σ₁ (N - v) - decidedCount O n₁ σ₁ (N - v))
          * residueCard O ^ (n₁ * v) * residueCard O ^ (n₂ * N) : ℝ)
          / (residueCard O : ℝ) ^ ((n₁ + n₂) * N)
        = gapSeq O n₁ σ₁ (N - v) := by
      unfold gapSeq possibleSeq decidedSeq
      rw [div_sub_div_same, div_eq_div_iff (by positivity) (by positivity)]
      rw [add_mul, hsplit₁]
      ring
    have hE₂ : ((possibleCount O n₂ σ₂ (N - v) - decidedCount O n₂ σ₂ (N - v))
          * residueCard O ^ (n₂ * v) * residueCard O ^ (n₁ * N) : ℝ)
          / (residueCard O : ℝ) ^ ((n₁ + n₂) * N)
        = gapSeq O n₂ σ₂ (N - v) := by
      unfold gapSeq possibleSeq decidedSeq
      rw [div_sub_div_same, div_eq_div_iff (by positivity) (by positivity)]
      rw [add_mul, hsplit₂]
      ring
    have hmain := card_tableSlice_le (O := O) (π := π) (n₁ := n₁) (n₂ := n₂)
      (N := N) (v := v) hvN σ₁ σ₂
    have hcast : (Nat.card (tableSlice O π n₁ n₂ σ₁ σ₂ N v) : ℝ)
        ≤ (Nat.card (shiftedSlice O π n₁ n₂ σ₁ σ₂ N v) : ℝ)
          + (((possibleCount O n₁ σ₁ (N - v) - decidedCount O n₁ σ₁ (N - v) : ℕ) : ℝ)
                * (residueCard O : ℝ) ^ (n₁ * v) * (residueCard O : ℝ) ^ (n₂ * N)
            + ((possibleCount O n₂ σ₂ (N - v) - decidedCount O n₂ σ₂ (N - v) : ℕ) : ℝ)
                * (residueCard O : ℝ) ^ (n₂ * v) * (residueCard O : ℝ) ^ (n₁ * N)) := by
      exact_mod_cast hmain
    calc ((Nat.card (tableSlice O π n₁ n₂ σ₁ σ₂ N v) : ℝ)
            - (Nat.card (shiftedSlice O π n₁ n₂ σ₁ σ₂ N v) : ℝ))
          / (residueCard O : ℝ) ^ ((n₁ + n₂) * N)
        ≤ (((possibleCount O n₁ σ₁ (N - v) - decidedCount O n₁ σ₁ (N - v) : ℕ) : ℝ)
                * (residueCard O : ℝ) ^ (n₁ * v) * (residueCard O : ℝ) ^ (n₂ * N)
            + ((possibleCount O n₂ σ₂ (N - v) - decidedCount O n₂ σ₂ (N - v) : ℕ) : ℝ)
                * (residueCard O : ℝ) ^ (n₂ * v) * (residueCard O : ℝ) ^ (n₁ * N))
          / (residueCard O : ℝ) ^ ((n₁ + n₂) * N) := by
          gcongr
          linarith
      _ = gapSeq O n₁ σ₁ (N - v) + gapSeq O n₂ σ₂ (N - v) := by
          rw [add_div, ← hE₁, ← hE₂, Nat.cast_sub hdle₁, Nat.cast_sub hdle₂]

end Drainage

section DrainageComplete

/-- ★★ **THE DRAINAGE PREMISE, CLOSED UNCONDITIONALLY** (CSL's fence item (ii)): over
every complete DVR with finite residue field, the decided depth-`v` census stabilizes
at the shifted level — with NO drainage hypothesis, by KDW's unconditional
`drainageAt_all` (IFCG52). -/
theorem tendsto_slice_drainage_of_complete (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [IsAdicComplete (maximalIdeal O) O]
    [Finite (ResidueField O)] (π : O) (n₁ n₂ : ℕ)
    (σ₁ σ₂ : FactorizationType) (v : ℕ) :
    Tendsto (fun N =>
        ((Nat.card (tableSlice O π n₁ n₂ σ₁ σ₂ N v) : ℝ)
            - (Nat.card (shiftedSlice O π n₁ n₂ σ₁ σ₂ N v) : ℝ))
          / (residueCard O : ℝ) ^ ((n₁ + n₂) * N))
      atTop (nhds 0) :=
  tendsto_slice_drainage n₁ n₂ σ₁ σ₂ v
    (Uniformity.Density.IFCG52.drainageAt_all n₁ O σ₁)
    (Uniformity.Density.IFCG52.drainageAt_all n₂ O σ₂)

end DrainageComplete

/-! ## §5 — the re-base: `CollisionLaw`/`StrayLaw` rest on the visible-sector censuses -/

section ReBase

/-- **The visible-sector weight**: the multiplicity-weighted count of the visible
split cells — SDL's collision sum plus the cell count. -/
noncomputable def visWeight (O : Type*) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [Finite (ResidueField O)] (π : O) (m : ℕ)
    (σ : FactorizationType) (M : ℕ) : ℕ :=
  ∑ c ∈ (Set.toFinite (splitSectorVis O π m σ M)).toFinset, multCount O m σ M c

/-- **THE VISIBLE-SECTOR CELL CENSUS at `(m, σ)`** — the first named remaining Prop:
the normalized count of visible split cells is a uniform rational limit. -/
def VisCountLaw (m : ℕ) (σ : FactorizationType) : Prop :=
  ZcURLim (fun O _ _ _ _ _ π M =>
    (Nat.card (splitSectorVis O π m σ M) : ℝ)
      / ((residueCard O : ℕ) : ℝ) ^ (m * (M + m)))

/-- **THE VISIBLE-SECTOR WEIGHT CENSUS at `(m, σ)`** — the second named remaining
Prop: the normalized multiplicity-weighted count of visible split cells is a uniform
rational limit. -/
def VisWeightLaw (m : ℕ) (σ : FactorizationType) : Prop :=
  ZcURLim (fun O _ _ _ _ _ π M =>
    (visWeight O π m σ M : ℝ) / ((residueCard O : ℕ) : ℝ) ^ (m * (M + m)))

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [IsAdicComplete (maximalIdeal O) O] [Finite (ResidueField O)]

/-- Bridge: a finite set's `toFinset` card is its `Nat.card`. -/
private theorem toFinset_card_eq_natCard {α : Type*} (s : Set α) (hs : s.Finite) :
    hs.toFinset.card = Nat.card s := by
  rw [Nat.card_coe_set_eq, Set.ncard_eq_toFinset_card s hs]

/-- The collision total is the visible weight minus the visible cell count (exact;
every visible cell is hit at least once — SDL's B.42-citing leg). -/
theorem collisionTotal_cast {π : O} (hπ : Irreducible π) {m : ℕ} (hm : 0 < m)
    (σ : FactorizationType) (M : ℕ) :
    (collisionTotal O π m σ M : ℝ)
      = (visWeight O π m σ M : ℝ) - (Nat.card (splitSectorVis O π m σ M) : ℝ) := by
  classical
  unfold collisionTotal visWeight
  rw [Nat.cast_sum, Nat.cast_sum]
  rw [Finset.sum_congr rfl (fun c hc => Nat.cast_sub
    (one_le_multCount_of_vis hπ hm ((Set.Finite.mem_toFinset _).mp hc)))]
  rw [Finset.sum_sub_distrib]
  congr 1
  rw [Finset.sum_const, nsmul_eq_mul, Nat.cast_one, mul_one]
  exact_mod_cast congrArg (Nat.cast : ℕ → ℝ)
    (toFinset_card_eq_natCard (splitSectorVis O π m σ M) (Set.toFinite _))

/-- The stray total is the table minus the visible weight (exact). -/
theorem strayTotal_cast {π : O} (hπ : Irreducible π) {m : ℕ} (hm : 0 < m)
    (σ : FactorizationType) (M : ℕ) :
    (strayTotal O π m σ M : ℝ)
      = (convCount O m σ M : ℝ) - (visWeight O π m σ M : ℝ) := by
  have h1 := collisionTotal_cast hπ hm σ M
  have h2 : (convCount O m σ M : ℝ)
      = (Nat.card (splitSectorVis O π m σ M) : ℝ)
        + ((collisionTotal O π m σ M : ℝ) + (strayTotal O π m σ M : ℝ)) := by
    exact_mod_cast convCount_eq_card_vis_add_totals (O := O) hπ hm σ M
  linarith

/-- The visible weight vanishes on an empty visible sector. -/
theorem visWeight_eq_zero_of_empty {π : O} {m : ℕ} {σ : FactorizationType} {M : ℕ}
    (h : splitSectorVis O π m σ M = ∅) : visWeight O π m σ M = 0 := by
  unfold visWeight
  rw [Set.Finite.toFinset_eq_empty.mpr h, Finset.sum_empty]

/-- The collision total vanishes on an empty visible sector. -/
theorem collisionTotal_eq_zero_of_empty {π : O} {m : ℕ} {σ : FactorizationType}
    {M : ℕ} (h : splitSectorVis O π m σ M = ∅) : collisionTotal O π m σ M = 0 := by
  unfold collisionTotal
  rw [Set.Finite.toFinset_eq_empty.mpr h, Finset.sum_empty]

/-- At mass `≤ 3` the visible split sector is empty (SDL's sector emptiness). -/
theorem splitSectorVis_eq_empty_of_mass_le_three {π : O} (hπ : Irreducible π)
    {m : ℕ} (hm3 : m ≤ 3) (σ : FactorizationType) (M : ℕ) :
    splitSectorVis O π m σ M = ∅ := by
  refine Set.subset_empty_iff.mp ?_
  have hsub : splitSectorVis O π m σ M ⊆ splitSector O π m σ M := fun c hc => hc.1
  rw [splitSector_eq_empty_of_mass_le_three hπ hm3 σ M] at hsub
  exact hsub

/-- At every unramified type the visible split sector is empty (UZL's forcing through
IFCG33, exactly as IFCG38's `defectLaw_unramified`). -/
theorem splitSectorVis_eq_empty_unramified {π : O} {m : ℕ}
    (σ : FactorizationType) (hunr : ∀ p ∈ σ.data, p.1 = 1) (M : ℕ) :
    splitSectorVis O π m σ M = ∅ := by
  ext c
  simp only [Set.mem_empty_iff_false, iff_false]
  rintro ⟨⟨hcarr, -⟩, -⟩
  obtain ⟨⟨⟨hdec, hstr⟩, hsh⟩, -⟩ := hcarr
  exact Uniformity.Density.IFCG33.not_decidedAt_unramified_of_shallow
    (by omega : m ≤ M + m) hstr hsh hunr hdec

end ReBase

section Fires

/-- ★ **`CollisionLaw` rests on the two visible-sector censuses** — at every mass and
type. -/
theorem collisionLaw_of_visLaws {m : ℕ} (hm : 0 < m) (σ : FactorizationType)
    (hW : VisWeightLaw m σ) (hV : VisCountLaw m σ) : CollisionLaw m σ := by
  unfold CollisionLaw
  refine (zcURLim_sub hW hV).congr ?_
  intro O _ _ _ _ _ π hπ M
  show (visWeight O π m σ M : ℝ) / ((residueCard O : ℕ) : ℝ) ^ (m * (M + m))
      - (Nat.card (splitSectorVis O π m σ M) : ℝ)
          / ((residueCard O : ℕ) : ℝ) ^ (m * (M + m))
    = (collisionTotal O π m σ M : ℝ) / ((residueCard O : ℕ) : ℝ) ^ (m * (M + m))
  rw [div_sub_div_same, collisionTotal_cast hπ hm σ M]

/-- ★ **`StrayLaw` rests on the weight census** (under the `< m` decided value laws,
which supply the table law). -/
theorem strayLaw_of_visWeightLaw {m : ℕ} (hm : 0 < m) (σ : FactorizationType)
    (hDV : ∀ k, k < m → ∀ σ' : FactorizationType, σ'.degree = k → DecidedValueLaw k σ')
    (hW : VisWeightLaw m σ) : StrayLaw m σ := by
  unfold StrayLaw
  refine (zcURLim_sub (zcURLim_conv σ hDV) hW).congr ?_
  intro O _ _ _ _ _ π hπ M
  show (convCount O m σ M : ℝ) / ((residueCard O : ℕ) : ℝ) ^ (m * (M + m))
      - (visWeight O π m σ M : ℝ) / ((residueCard O : ℕ) : ℝ) ^ (m * (M + m))
    = (strayTotal O π m σ M : ℝ) / ((residueCard O : ℕ) : ℝ) ^ (m * (M + m))
  rw [div_sub_div_same, strayTotal_cast hπ hm σ M]

/-- ★★ **The defect law rests on the cell census ALONE** (under the `< m` decided
value laws): `defect = conv − #vis` pointwise, and the table law is landed. -/
theorem splitConvolutionDefectLaw_of_visCountLaw {m : ℕ} (σ : FactorizationType)
    (hDV : ∀ k, k < m → ∀ σ' : FactorizationType, σ'.degree = k → DecidedValueLaw k σ')
    (hV : VisCountLaw m σ) : SplitConvolutionDefectLaw m σ := by
  unfold SplitConvolutionDefectLaw
  refine (zcURLim_sub (zcURLim_conv σ hDV) hV).congr ?_
  intro O _ _ _ _ _ π hπ M
  show (convCount O m σ M : ℝ) / ((residueCard O : ℕ) : ℝ) ^ (m * (M + m))
      - (Nat.card (splitSectorVis O π m σ M) : ℝ)
          / ((residueCard O : ℕ) : ℝ) ^ (m * (M + m))
    = ((convCount O m σ M : ℝ) - (Nat.card (splitSectorVis O π m σ M) : ℝ))
        / ((residueCard O : ℕ) : ℝ) ^ (m * (M + m))
  rw [div_sub_div_same]

/-- ★★ **THE OFFICIAL SPLIT FRONT** — `SplitSectorLaw m σ` at EVERY mass and type
rests on the `< m` decided value laws plus the SINGLE named Prop `VisCountLaw m σ`. -/
theorem splitSectorLaw_of_visCountLaw {m : ℕ} (hm : 0 < m) (σ : FactorizationType)
    (hDV : ∀ k, k < m → ∀ σ' : FactorizationType, σ'.degree = k → DecidedValueLaw k σ')
    (hV : VisCountLaw m σ) : SplitSectorLaw m σ :=
  splitSectorLaw_of_defectLaw hm σ hDV (splitConvolutionDefectLaw_of_visCountLaw σ hDV hV)

/-- ★ **FIRST FIRE of `CollisionLaw`** — unconditional at mass `≤ 3`: the split
sector is empty (SDL), so the collision total vanishes identically. -/
theorem collisionLaw_of_mass_le_three {m : ℕ} (hm3 : m ≤ 3) (σ : FactorizationType) :
    CollisionLaw m σ := by
  unfold CollisionLaw
  refine ZcURLim_zero.congr ?_
  intro O _ _ _ _ _ π hπ M
  rw [collisionTotal_eq_zero_of_empty
    (splitSectorVis_eq_empty_of_mass_le_three hπ hm3 σ M)]
  simp

/-- ★ **FIRST FIRE of `StrayLaw`** — at mass `≤ 3` under the `< m` value laws: the
stray mass is the whole table. -/
theorem strayLaw_of_mass_le_three {m : ℕ} (hm : 0 < m) (hm3 : m ≤ 3)
    (σ : FactorizationType)
    (hDV : ∀ k, k < m → ∀ σ' : FactorizationType, σ'.degree = k → DecidedValueLaw k σ') :
    StrayLaw m σ := by
  unfold StrayLaw
  refine (zcURLim_conv σ hDV).congr ?_
  intro O _ _ _ _ _ π hπ M
  have hst := strayTotal_cast hπ hm σ M
  rw [visWeight_eq_zero_of_empty
    (splitSectorVis_eq_empty_of_mass_le_three hπ hm3 σ M)] at hst
  show (convCount O m σ M : ℝ) / ((residueCard O : ℕ) : ℝ) ^ (m * (M + m))
      = (strayTotal O π m σ M : ℝ) / ((residueCard O : ℕ) : ℝ) ^ (m * (M + m))
  rw [hst]
  norm_num

/-- ★ `CollisionLaw` fires unconditionally at every UNRAMIFIED type (the visible
split sector is empty on the shallow stratum — UZL's forcing through IFCG33). -/
theorem collisionLaw_unramified {m : ℕ} (σ : FactorizationType)
    (hunr : ∀ p ∈ σ.data, p.1 = 1) : CollisionLaw m σ := by
  unfold CollisionLaw
  refine ZcURLim_zero.congr ?_
  intro O _ _ _ _ _ π hπ M
  rw [collisionTotal_eq_zero_of_empty (splitSectorVis_eq_empty_unramified σ hunr M)]
  simp

/-- ★ `StrayLaw` fires at every unramified type under the `< m` value laws. -/
theorem strayLaw_unramified {m : ℕ} (hm : 0 < m) (σ : FactorizationType)
    (hunr : ∀ p ∈ σ.data, p.1 = 1)
    (hDV : ∀ k, k < m → ∀ σ' : FactorizationType, σ'.degree = k → DecidedValueLaw k σ') :
    StrayLaw m σ := by
  unfold StrayLaw
  refine (zcURLim_conv σ hDV).congr ?_
  intro O _ _ _ _ _ π hπ M
  have hst := strayTotal_cast hπ hm σ M
  rw [visWeight_eq_zero_of_empty (splitSectorVis_eq_empty_unramified σ hunr M)] at hst
  show (convCount O m σ M : ℝ) / ((residueCard O : ℕ) : ℝ) ^ (m * (M + m))
      = (strayTotal O π m σ M : ℝ) / ((residueCard O : ℕ) : ℝ) ^ (m * (M + m))
  rw [hst]
  norm_num

end Fires

end Uniformity.Density.IFCG56

end

/-! ## AXCHECK FOOTER — §§1–4 expect PURE Lean core `{propext, Classical.choice,
Quot.sound}` (fiber law, gap engine, and KDW's drainage are all Lean-core); the §5
declarations touching the sector identities/emptiness expect Lean core + the
owner-signed B.42 cite `Uniformity.Density.Leaf.exists_slope_factorization` (through
SDL).  C.33 and `AX_cellRecursion` must NOT occur. -/
#print axioms Uniformity.Density.IFCG56.card_preimage_pairFactor
#print axioms Uniformity.Density.IFCG56.mixDepth_proj_eq_iff
#print axioms Uniformity.Density.IFCG56.mixDepth_proj_levels
#print axioms Uniformity.Density.IFCG56.depthPairSet_eq_preimage
#print axioms Uniformity.Density.IFCG56.card_depthPairSet_levels
#print axioms Uniformity.Density.IFCG56.card_depthPairSetGE_levels
#print axioms Uniformity.Density.IFCG56.resultant_monicPoly_one_one
#print axioms Uniformity.Density.IFCG56.card_depthPairSet_one_one
#print axioms Uniformity.Density.IFCG56.shiftedDepthFiber_inter_eq_pairNbhd
#print axioms Uniformity.Density.IFCG56.natCard_shiftedDepthFiber
#print axioms Uniformity.Density.IFCG56.pairDepthFiber_eq_natCard
#print axioms Uniformity.Density.IFCG56.qpow_mul_card_le_pairDepthFiber
#print axioms Uniformity.Density.IFCG56.card_shiftedSlice
#print axioms Uniformity.Density.IFCG56.card_tableSlice_le
#print axioms Uniformity.Density.IFCG56.tendsto_slice_drainage
#print axioms Uniformity.Density.IFCG56.tendsto_slice_drainage_of_complete
#print axioms Uniformity.Density.IFCG56.collisionTotal_cast
#print axioms Uniformity.Density.IFCG56.strayTotal_cast
#print axioms Uniformity.Density.IFCG56.splitSectorVis_eq_empty_of_mass_le_three
#print axioms Uniformity.Density.IFCG56.splitSectorVis_eq_empty_unramified
#print axioms Uniformity.Density.IFCG56.collisionLaw_of_visLaws
#print axioms Uniformity.Density.IFCG56.strayLaw_of_visWeightLaw
#print axioms Uniformity.Density.IFCG56.splitConvolutionDefectLaw_of_visCountLaw
#print axioms Uniformity.Density.IFCG56.splitSectorLaw_of_visCountLaw
#print axioms Uniformity.Density.IFCG56.collisionLaw_of_mass_le_three
#print axioms Uniformity.Density.IFCG56.strayLaw_of_mass_le_three
#print axioms Uniformity.Density.IFCG56.collisionLaw_unramified
#print axioms Uniformity.Density.IFCG56.strayLaw_unramified
