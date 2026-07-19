/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.OM.Order0Alpha

/-!
# RealInstanceV2Prep — Wave-2 lemma bank for the σ-keyed order-0 menu
(`notes/M9_REBASE_BLUEPRINT_2026-07-19.md` §1 "CountingModel fields" / §2 `realM2`)

Standalone facts about the σ-keyed order-0 separable menu `Order0.sepShapesOf n σ`, needed to
discharge the `CountingModel` fields of the Wave-2 real instance `realM2`
(`decidedCount σ N := ∑ T ∈ sepShapesOf n σ, M8.stratumCount (M9.rawCount n) T N`):

* `sepShape_injective` — the shape literal determines the partition (its `dS`-list is the sorted
  parts list);
* `eq_of_mem_sepShapesOf` — cross-σ menu DISJOINTNESS: a shape names its type (feeds
  `box_partition` / `undecidedCount ≥ 0`);
* `unramTypeMenu` + `sum_unramTypeMenu_eq_sum_partitions` — the double sum over the σ-menu
  re-indexes as a single sum over ALL partitions of `n` (each partition appears in exactly one
  σ-menu, namely its own `unramType`);
* `sum_stratumCount_le_box` — the total decided count at level `N ≥ 1` is at most the box count
  `realP^(nN)` (distinct shapes have disjoint classifier fibers inside the SAME finite box);
* `normSum_sepShapesOf_levelConst` — level-≥1 CONSTANCY of the normalized per-σ decided count
  (feeds `decided_mono` / `decided_tendsto`); `normSum_sepShapesOf_zero_le` covers the `N = 0`
  edge (the level-0 box over the trivial ring `ZMod 1` is EMPTY for `n > 0`, so the level-0
  normalized count is `0`).

Independent of the V2 interface; a leaf module (no existing file is modified).
-/

set_option linter.style.longLine false
set_option linter.style.header false

namespace LeanUrat.OM.RealInstanceV2Prep

open scoped Classical
open LeanUrat LeanUrat.OM Finset

/-! ## 1. `sepShape` is injective in the partition -/

/-- **The order-0 leaf shape determines the partition.** The payload's `dS`-list of
`Order0.sepShape n lam` is the sorted parts list of `lam` (`Order0.dSList_sepShape`), and the
sorted parts determine the parts multiset, which determines the partition. -/
theorem sepShape_injective (n : ℕ) : Function.Injective (Order0.sepShape n) := by
  intro lam lam' h
  have hsort : lam.parts.sort (· ≤ ·) = lam'.parts.sort (· ≤ ·) := by
    rw [← Order0.dSList_sepShape n lam, ← Order0.dSList_sepShape n lam', h]
  have hparts : lam.parts = lam'.parts := by
    have := congrArg (fun l : List ℕ => (l : Multiset ℕ)) hsort
    simpa [Multiset.sort_eq] using this
  exact Nat.Partition.ext hparts

/-! ## 2. Cross-σ menu disjointness -/

/-- **A menu shape names its type**: if `T` lies in the σ-menu and in the σ′-menu then `σ = σ′`.
(Both memberships name partitions with the same `sepShape`; injectivity identifies them; their
common `unramType` is both `σ` and `σ′`.) -/
theorem eq_of_mem_sepShapesOf {n : ℕ} {σ σ' : FactorizationType} {T : ClusterShape}
    (h : T ∈ Order0.sepShapesOf n σ) (h' : T ∈ Order0.sepShapesOf n σ') : σ = σ' := by
  simp only [Order0.sepShapesOf, Finset.mem_image, Finset.mem_filter, Finset.mem_univ,
    true_and] at h h'
  obtain ⟨lam, hσ, hT⟩ := h
  obtain ⟨lam', hσ', hT'⟩ := h'
  rw [hσ, hσ', sepShape_injective n (hT.trans hT'.symm)]

/-! ## 3. The finite type menu and the re-indexing identity -/

/-- **The degree-`n` unramified type menu**: the image of all partitions of `n` under
`Order0.unramType n`. The finite σ-menu for the Wave-2 `CountingModel.typeMenu` field. -/
noncomputable def unramTypeMenu (n : ℕ) : Finset FactorizationType :=
  (Finset.univ : Finset (Nat.Partition n)).image (Order0.unramType n)

/-- The per-σ menu sum is the sum over the σ-fiber of partitions (the `sepShape` image is
summed back through `Finset.sum_image` via injectivity). -/
theorem sum_sepShapesOf {n : ℕ} {M : Type*} [AddCommMonoid M] (σ : FactorizationType)
    (f : ClusterShape → M) :
    ∑ T ∈ Order0.sepShapesOf n σ, f T
      = ∑ lam ∈ Finset.univ.filter (fun lam : Nat.Partition n => Order0.unramType n lam = σ),
          f (Order0.sepShape n lam) := by
  unfold Order0.sepShapesOf
  rw [Finset.sum_image (fun x _ y _ h => sepShape_injective n h)]
  congr 1
  ext lam
  simp [eq_comm]

/-- **The re-indexing identity** (Wave-2 `box_partition` feed): the double sum over the type menu
and its σ-keyed shape menus is the single sum over ALL partitions of `n` — each partition `lam`
appears in exactly one σ-menu, namely `σ = unramType n lam`. -/
theorem sum_unramTypeMenu_eq_sum_partitions (n : ℕ) {M : Type*} [AddCommMonoid M]
    (f : ClusterShape → M) :
    ∑ σ ∈ unramTypeMenu n, ∑ T ∈ Order0.sepShapesOf n σ, f T
      = ∑ lam : Nat.Partition n, f (Order0.sepShape n lam) := by
  calc ∑ σ ∈ unramTypeMenu n, ∑ T ∈ Order0.sepShapesOf n σ, f T
      = ∑ σ ∈ unramTypeMenu n,
          ∑ lam ∈ Finset.univ.filter (fun lam : Nat.Partition n => Order0.unramType n lam = σ),
            f (Order0.sepShape n lam) :=
        Finset.sum_congr rfl fun σ _ => sum_sepShapesOf σ f
    _ = ∑ lam : Nat.Partition n, f (Order0.sepShape n lam) :=
        Finset.sum_fiberwise_of_maps_to
          (fun lam _ => Finset.mem_image_of_mem _ (Finset.mem_univ lam)) _

/-! ## 4. The box bound -/

/-- Distinct fibers of a function into a finite domain: the fiber counts over an injective family
of values sum to at most the domain cardinality. -/
theorem sum_card_fibers_le {α β ι : Type*} [Finite α] [Fintype ι]
    (g : α → β) (v : ι → β) (hv : Function.Injective v) :
    ∑ i : ι, Nat.card {a : α // g a = v i} ≤ Nat.card α := by
  classical
  cases nonempty_fintype α
  calc ∑ i : ι, Nat.card {a : α // g a = v i}
      = ∑ i : ι, (Finset.univ.filter (fun a : α => g a = v i)).card :=
        Finset.sum_congr rfl fun i _ => by
          rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    _ = (Finset.univ.biUnion (fun i : ι => Finset.univ.filter (fun a : α => g a = v i))).card := by
        refine (Finset.card_biUnion ?_).symm
        intro i _ j _ hij
        refine Finset.disjoint_left.mpr fun a ha ha' => hij (hv ?_)
        rw [← (Finset.mem_filter.mp ha).2, ← (Finset.mem_filter.mp ha').2]
    _ ≤ Fintype.card α := Finset.card_le_univ _
    _ = Nat.card α := (Nat.card_eq_fintype_card).symm

/-- **The box bound** (Wave-2 `undecidedCount ≥ 0` feed): at every level `N ≥ 1` the total decided
count over the whole type menu is at most the box count `realP^(nN)` — distinct shapes have
disjoint classifier fibers inside the same finite box `monicBox realP N n`. -/
theorem sum_stratumCount_le_box (n N : ℕ) (hN : 0 < N) :
    (∑ σ ∈ unramTypeMenu n, ∑ T ∈ Order0.sepShapesOf n σ, M8.stratumCount (M9.rawCount n) T N)
      ≤ (M9.realP : ℚ) ^ (n * N) := by
  rw [sum_unramTypeMenu_eq_sum_partitions]
  haveI hfin : Finite (QuotientBox.monicBox M9.realP N n) := by
    have hpos : 0 < Nat.card (QuotientBox.monicBox M9.realP N n) := by
      rw [QuotientBox.card_monicBox M9.realP N n hN]
      exact pow_pos (pow_pos (by norm_num [M9.realP]) N) n
    exact (Nat.card_pos_iff.mp hpos).2
  have key : (∑ lam : Nat.Partition n, M9.rawCount n (Order0.sepShape n lam) N)
      ≤ M9.realP ^ (n * N) := by
    have hle := sum_card_fibers_le (M9.realClassify n N) (Order0.sepShape n)
      (sepShape_injective n)
    rw [QuotientBox.card_monicBox M9.realP N n hN] at hle
    calc ∑ lam : Nat.Partition n, M9.rawCount n (Order0.sepShape n lam) N
        = ∑ lam : Nat.Partition n,
            Nat.card {f : QuotientBox.monicBox M9.realP N n //
              M9.realClassify n N f = Order0.sepShape n lam} := rfl
      _ ≤ (M9.realP ^ N) ^ n := hle
      _ = M9.realP ^ (n * N) := by rw [← pow_mul, Nat.mul_comm]
  calc (∑ lam : Nat.Partition n, M8.stratumCount (M9.rawCount n) (Order0.sepShape n lam) N)
      = ((∑ lam : Nat.Partition n, M9.rawCount n (Order0.sepShape n lam) N : ℕ) : ℚ) := by
        rw [Nat.cast_sum]
        rfl
    _ ≤ ((M9.realP ^ (n * N) : ℕ) : ℚ) := by exact_mod_cast key
    _ = (M9.realP : ℚ) ^ (n * N) := by push_cast; ring

/-! ## 5. Level-≥1 constancy of the normalized menu sum -/

/-- **Level-≥1 constancy** (Wave-2 `decided_mono`/`decided_tendsto` feed): for `N ≥ 1` the
normalized per-σ decided count equals its level-1 value — each menu summand is
`m_λ · realP^((N−1)n)` (`Order0.stratumCount_sepShape`), and the normalization
`realP^(nN)` absorbs the growth exactly. -/
theorem normSum_sepShapesOf_levelConst (n : ℕ) (hn : 0 < n) (σ : FactorizationType)
    (N : ℕ) (hN : 0 < N) :
    (∑ T ∈ Order0.sepShapesOf n σ, M8.stratumCount (M9.rawCount n) T N) / (M9.realP : ℚ) ^ (n * N)
      = (∑ T ∈ Order0.sepShapesOf n σ, M8.stratumCount (M9.rawCount n) T 1)
          / (M9.realP : ℚ) ^ (n * 1) := by
  obtain ⟨N', rfl⟩ : ∃ N', N = N' + 1 := ⟨N - 1, by omega⟩
  have hP0 : (M9.realP : ℚ) ≠ 0 := by norm_num [M9.realP]
  -- the per-shape count at level `M ≥ 1`, split as (finite-field choice count) × growth factor
  have hterm : ∀ (M : ℕ), 0 < M → ∀ lam : Nat.Partition n,
      M8.stratumCount (M9.rawCount n) (Order0.sepShape n lam) M
        = ((∏ d ∈ lam.parts.toFinset,
              (Order0.avail (ZMod M9.realP) d).choose (lam.parts.count d) : ℕ) : ℚ)
            * (M9.realP : ℚ) ^ ((M - 1) * n) := by
    intro M hM lam
    rw [Order0.stratumCount_sepShape n hn lam M hM]
    push_cast
    ring
  rw [sum_sepShapesOf σ (fun T => M8.stratumCount (M9.rawCount n) T (N' + 1)),
    sum_sepShapesOf σ (fun T => M8.stratumCount (M9.rawCount n) T 1)]
  set filt := Finset.univ.filter (fun lam : Nat.Partition n => Order0.unramType n lam = σ)
  set m : Nat.Partition n → ℚ := fun lam =>
    ((∏ d ∈ lam.parts.toFinset,
        (Order0.avail (ZMod M9.realP) d).choose (lam.parts.count d) : ℕ) : ℚ)
  have hsumN : ∑ lam ∈ filt, M8.stratumCount (M9.rawCount n) (Order0.sepShape n lam) (N' + 1)
      = (∑ lam ∈ filt, m lam) * (M9.realP : ℚ) ^ (N' * n) := by
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun lam _ => ?_
    rw [hterm (N' + 1) (Nat.succ_pos _) lam, Nat.add_sub_cancel]
  have hsum1 : ∑ lam ∈ filt, M8.stratumCount (M9.rawCount n) (Order0.sepShape n lam) 1
      = ∑ lam ∈ filt, m lam := by
    refine Finset.sum_congr rfl fun lam _ => ?_
    rw [hterm 1 Nat.one_pos lam, Nat.sub_self, zero_mul, pow_zero, mul_one]
  rw [hsumN, hsum1]
  field_simp
  ring

/-- **The `N = 0` edge** (Wave-2 `decided_mono` feed): the level-0 box is the monic degree-`n`
box over `ZMod (realP^0) = ZMod 1`, the trivial ring — EMPTY for `n > 0` (every polynomial over a
subsingleton ring is `0`, of `natDegree 0 ≠ n`). So the level-0 normalized menu sum is `0`, which
is at most the (nonnegative) level-1 value. -/
theorem normSum_sepShapesOf_zero_le (n : ℕ) (hn : 0 < n) (σ : FactorizationType) :
    (∑ T ∈ Order0.sepShapesOf n σ, M8.stratumCount (M9.rawCount n) T 0) / (M9.realP : ℚ) ^ (n * 0)
      ≤ (∑ T ∈ Order0.sepShapesOf n σ, M8.stratumCount (M9.rawCount n) T 1)
          / (M9.realP : ℚ) ^ (n * 1) := by
  have hzero : ∀ T : ClusterShape, M8.stratumCount (M9.rawCount n) T 0 = 0 := by
    intro T
    haveI : IsEmpty {f : QuotientBox.monicBox M9.realP 0 n // M9.realClassify n 0 f = T} := by
      constructor
      rintro ⟨⟨f, hmon, hdeg⟩, -⟩
      haveI : Subsingleton (ZMod (M9.realP ^ 0)) := ZMod.subsingleton_iff.mpr (pow_zero _)
      have hf : f = 0 := Polynomial.ext fun k => Subsingleton.elim _ _
      rw [hf, Polynomial.natDegree_zero] at hdeg
      omega
    show ((M9.rawCount n T 0 : ℕ) : ℚ) = 0
    rw [show M9.rawCount n T 0
        = Nat.card {f : QuotientBox.monicBox M9.realP 0 n // M9.realClassify n 0 f = T} from rfl,
      Nat.card_of_isEmpty]
    norm_num
  rw [Finset.sum_eq_zero fun T _ => hzero T, zero_div]
  apply div_nonneg
  · exact Finset.sum_nonneg fun T _ => M8.stratumCount_nonneg _ T 1
  · positivity

end LeanUrat.OM.RealInstanceV2Prep
