/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.OM.ClassifierBridgeFiber
import LeanUrat.OM.Order0Capstone

/-!
# WildMenu — the σ-keyed wild (constant-e ramified) shape menu (Wave 1a,
`notes/WILD_WAVE1_BLUEPRINT_2026-07-21.md` §2 item 1)

**Scope (blueprint §1).** Covered: **constant-e ramified types** `σ = {(e,f₁),…,(e,f_k)}` with
`e ≥ 2`, all `fᵢ ≥ 1`, `e·Σfᵢ = n` — ONE canonical stratum per σ: the minimal-H single-slope
terminating `Tselfloop` stratum (side `((0,H),(n,0))` with `H = Σfᵢ = n/e`, slope `−1/e`,
all-μ=1 residual with parts `(fᵢ)`). NOT covered (unchanged, documented): the per-type H-tower
resummation (the recursive self-loop wall), mixed-e types, order ≥ 2, exhaustiveness.

Contents:
* `constERam n σ` — the constant-e ramified predicate. ⚠ Two side conditions BEYOND the
  blueprint's one-line gloss are load-bearing and included: `σ.data ≠ 0` (else the canonical
  shape is `[]`, violating the banked legs' `hne`) and `∀ (e,f) ∈ σ, 1 ≤ f` (else the shape
  entry `(f,1)` violates `shapesOfDegree`'s positivity). Both hold for every genuine
  factorization type.
* `wShape σ` / `wPath n σ` — the canonical all-μ=1 residual shape (sorted `(fᵢ,1)` entries) and
  the minimal-H self-loop menu path `[(0, fSum σ), (n, 0)]`; the full admissibility bank
  (`MenuPath` at `N₀ = fSum σ + 1`, `ShapesFor`, `hpos`/`hμ`/`hne`), and the MINIMALITY theorem
  `wPath_H_min` (any admissible single-slope path for this shape has `H ≥ fSum σ`; the
  `ShapesFor` sum condition forces `gcd H n = fSum σ`, hence `fSum σ ∣ H`).
* `ramShape n σ : Option ClusterShape` — the canonical `Tselfloop` literal for constant-e σ,
  `none` otherwise; `SelfLoopWitness`/`ramShapeWitness` — the packaged witness bundle whose
  fields are EXACTLY the hypotheses of the banked counting legs
  (`ClassifierBridgeFiber2.hnode_selfloop_over_Bclassify_R`, `stratumCount_selfloop_R`,
  `classify_eq_selfloop_iff`), so W1b consumes them without re-derivation.
* `typeOfW n T` — the σ-decoder off the shape literal (head tree + `dS` payload):
  `typeOfW_sepShape` (recovers `unramType` on the order-0 image) and `typeOfW_ramShape`
  (recovers σ on the `ramShape` image).
* `omMenuW n σ := sepShapesOf n σ ∪ (ramShape n σ).toFinset` and the disjointness bank:
  `ramShape_not_mem_sepShapesOf` (distinct head trees: `[(0,n,n)]` vs `[(0,n,fSum σ)]`,
  `fSum σ < n`), `ramShape_injective`, `mem_omMenuW_type` (the cross-σ disjointness lever),
  `eq_of_mem_omMenuW`, `omMenuW_unram`, `omMenuW_ram_of_constE`, `treeSize_of_mem_omMenuW`.

Leaf module: no existing file is modified. No axiom, no sorry.
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false

namespace LeanUrat.OM.WildMenu

open scoped Classical
open LeanUrat LeanUrat.OM
open LeanUrat.OM.CellMenu

/-! ## 1. Constant-e ramified types -/

/-- The residual-degree sum `Σ fᵢ` of a factorization type. For a constant-e type this is `n/e`
(the canonical self-loop height `H`). -/
def fSum (σ : FactorizationType) : ℕ := (σ.data.map Prod.snd).sum

/-- **The constant-e ramified predicate**: σ is nonempty, all its pairs share ONE `e ≥ 2`, all
residual degrees are `≥ 1`, and `e·Σfᵢ = n`. The nonemptiness and `1 ≤ f` conditions are the
load-bearing side conditions of the canonical stratum (see the module docstring). -/
def constERam (n : ℕ) (σ : FactorizationType) : Prop :=
  ∃ e : ℕ, 2 ≤ e ∧ σ.data ≠ 0 ∧ (∀ pr ∈ σ.data, pr.1 = e ∧ 1 ≤ pr.2) ∧ e * fSum σ = n

theorem constERam_fSum_pos {n : ℕ} {σ : FactorizationType} (h : constERam n σ) :
    0 < fSum σ := by
  obtain ⟨e, -, hne, hall, -⟩ := h
  obtain ⟨pr, hpr⟩ := Multiset.exists_mem_of_ne_zero hne
  have h2 := (hall pr hpr).2
  have hmem : pr.2 ∈ σ.data.map Prod.snd := Multiset.mem_map_of_mem _ hpr
  have hle : pr.2 ≤ (σ.data.map Prod.snd).sum :=
    Multiset.single_le_sum (fun x _ => Nat.zero_le x) _ hmem
  unfold fSum
  omega

theorem constERam_n_pos {n : ℕ} {σ : FactorizationType} (h : constERam n σ) : 0 < n := by
  have hf := constERam_fSum_pos h
  obtain ⟨e, he2, -, -, hprod⟩ := h
  have h21 : 2 * 1 ≤ e * fSum σ := Nat.mul_le_mul he2 hf
  omega

theorem constERam_fSum_dvd {n : ℕ} {σ : FactorizationType} (h : constERam n σ) :
    fSum σ ∣ n := by
  obtain ⟨e, -, -, -, hprod⟩ := h
  exact ⟨e, by rw [← hprod, Nat.mul_comm]⟩

theorem constERam_fSum_lt {n : ℕ} {σ : FactorizationType} (h : constERam n σ) :
    fSum σ < n := by
  have hf := constERam_fSum_pos h
  obtain ⟨e, he2, -, -, hprod⟩ := h
  have h2 : 2 * fSum σ ≤ e * fSum σ := Nat.mul_le_mul_right _ he2
  omega

/-- The common `e` is recoverable as `n / fSum σ`. -/
theorem constERam_e_eq {n e : ℕ} {σ : FactorizationType} (_h2 : 2 ≤ e)
    (hprod : e * fSum σ = n) (hpos : 0 < fSum σ) : n / fSum σ = e :=
  Nat.div_eq_of_eq_mul_left hpos hprod.symm

/-- Rebuilding the data multiset from its `f`-parts when all pairs share the first component. -/
theorem data_eq_map_snd {e : ℕ} {σ : FactorizationType}
    (h : ∀ pr ∈ σ.data, pr.1 = e) :
    (σ.data.map Prod.snd).map (fun f => (e, f)) = σ.data := by
  rw [Multiset.map_map]
  conv_rhs => rw [← Multiset.map_id σ.data]
  refine Multiset.map_congr rfl ?_
  intro pr hpr
  simp only [Function.comp_apply, id_eq]
  exact Prod.ext ((h pr hpr).symm) rfl

/-- A constant-e ramified type has degree `n`: `Σ e·fᵢ = e·Σfᵢ = n`. -/
theorem constERam_degree {n : ℕ} {σ : FactorizationType} (h : constERam n σ) :
    σ.degree = n := by
  obtain ⟨e, -, -, hall, hprod⟩ := h
  unfold FactorizationType.degree
  have hmap : σ.data.map (fun p : ℕ × ℕ => p.1 * p.2)
      = σ.data.map (fun p : ℕ × ℕ => e * Prod.snd p) :=
    Multiset.map_congr rfl (fun pr hpr => by rw [(hall pr hpr).1])
  rw [hmap, Multiset.sum_map_mul_left]
  exact hprod

/-! ## 2. The canonical residual shape and menu path -/

/-- **The canonical all-μ=1 residual shape of σ**: the `f`-parts in canonical (sorted ascending)
order, each as a `(fᵢ, 1)` entry. -/
def wShape (σ : FactorizationType) : List (ℕ × ℕ) :=
  ((σ.data.map Prod.snd).sort (· ≤ ·)).map (fun f => (f, 1))

/-- **The canonical minimal-H self-loop menu path**: `[(0, fSum σ), (n, 0)]` — left height
`H = fSum σ = n/e` (the MINIMAL admissible H, `wPath_H_min`), slope `−fSum σ/n = −1/e`. -/
def wPath (n : ℕ) (σ : FactorizationType) : List (ℕ × ℕ) := [(0, fSum σ), (n, 0)]

theorem wShape_mu (σ : FactorizationType) : ∀ q ∈ wShape σ, q.2 = 1 := by
  intro q hq
  rw [wShape, List.mem_map] at hq
  obtain ⟨f, -, rfl⟩ := hq
  rfl

theorem wShape_fst_sum (σ : FactorizationType) :
    ((wShape σ).map Prod.fst).sum = fSum σ := by
  rw [wShape, List.map_map]
  rw [show (Prod.fst ∘ fun f : ℕ => ((f, 1) : ℕ × ℕ)) = id from rfl, List.map_id]
  rw [show ((σ.data.map Prod.snd).sort (· ≤ ·)).sum
      = ((((σ.data.map Prod.snd).sort (· ≤ ·)) : List ℕ) : Multiset ℕ).sum from
    (Multiset.sum_coe _).symm]
  rw [Multiset.sort_eq]
  rfl

theorem wShape_pos {n : ℕ} {σ : FactorizationType} (h : constERam n σ) :
    ∀ q ∈ wShape σ, 1 ≤ q.1 := by
  intro q hq
  rw [wShape, List.mem_map] at hq
  obtain ⟨f, hf, rfl⟩ := hq
  rw [Multiset.mem_sort, Multiset.mem_map] at hf
  obtain ⟨pr, hpr, rfl⟩ := hf
  obtain ⟨e, -, -, hall, -⟩ := h
  exact (hall pr hpr).2

theorem wShape_ne {n : ℕ} {σ : FactorizationType} (h : constERam n σ) : wShape σ ≠ [] := by
  obtain ⟨e, -, hne, -, -⟩ := h
  intro hnil
  rw [wShape, List.map_eq_nil_iff] at hnil
  have hzero : (σ.data.map Prod.snd) = 0 := by
    have := congrArg (fun l : List ℕ => (l : Multiset ℕ)) hnil
    simpa [Multiset.sort_eq] using this
  rw [Multiset.map_eq_zero] at hzero
  exact hne hzero

theorem wShape_pairwise (σ : FactorizationType) : (wShape σ).Pairwise shapeLE := by
  rw [wShape]
  refine List.Pairwise.map _ ?_ (Multiset.pairwise_sort _ (· ≤ ·))
  intro a b hab
  rcases Nat.lt_or_ge a b with hlt | hge
  · exact Or.inl hlt
  · exact Or.inr ⟨show a = b by omega, le_refl 1⟩

/-- The canonical shape is a genuine residual shape of degree `fSum σ`. -/
theorem wShape_mem_shapesOfDegree {n : ℕ} {σ : FactorizationType} (h : constERam n σ) :
    wShape σ ∈ shapesOfDegree (fSum σ) := by
  rw [mem_shapesOfDegree_iff]
  refine ⟨wShape_pairwise σ, ?_, ?_⟩
  · intro q hq
    exact ⟨wShape_pos h q hq, le_of_eq (wShape_mu σ q hq).symm⟩
  · rw [List.map_congr_left (fun q hq => by
      rw [wShape_mu σ q hq, Nat.mul_one] : ∀ q ∈ wShape σ, q.1 * q.2 = Prod.fst q)]
    exact wShape_fst_sum σ

/-- The single side of the canonical path. -/
theorem sidePairs_wPath (n : ℕ) (σ : FactorizationType) :
    sidePairs (wPath n σ) = [(((0, fSum σ), (n, 0)) : (ℕ × ℕ) × (ℕ × ℕ))] := rfl

/-- The side degree of the canonical side is `gcd (fSum σ) n = fSum σ` (as `fSum σ ∣ n`). -/
theorem sideDeg_wPath {n : ℕ} {σ : FactorizationType} (h : constERam n σ) :
    sideDeg (((0, fSum σ), (n, 0)) : (ℕ × ℕ) × (ℕ × ℕ)) = fSum σ := by
  change Nat.gcd (fSum σ - 0) (n - 0) = fSum σ
  rw [Nat.sub_zero, Nat.sub_zero]
  exact Nat.gcd_eq_left (constERam_fSum_dvd h)

/-- The canonical path is a valid menu path at the base level `N₀ = fSum σ + 1` (the minimal
level admitting the height `H = fSum σ ≤ N₀ − 1`). -/
theorem menuPath_wPath {n : ℕ} {σ : FactorizationType} (h : constERam n σ) :
    MenuPath n (fSum σ + 1) (wPath n σ) := by
  have hn := constERam_n_pos h
  have hf := constERam_fSum_pos h
  exact ⟨fSum σ, ((n : ℕ), (0 : ℕ)), [], rfl, hf, by omega, hn, hf, ChainOK.nil rfl rfl⟩

/-- The canonical shape assignment is valid for the canonical path. -/
theorem shapesFor_wPath {n : ℕ} {σ : FactorizationType} (h : constERam n σ) :
    ShapesFor (wPath n σ) [wShape σ] := by
  unfold ShapesFor
  rw [sidePairs_wPath]
  refine List.Forall₂.cons ?_ List.Forall₂.nil
  rw [sideDeg_wPath h]
  exact wShape_mem_shapesOfDegree h

/-- **Minimality of the canonical height.** Any single-slope self-loop path `[(0,H),(n,0)]`
admitting the canonical shape (`ShapesFor`, i.e. `wShape σ ∈ shapesOfDegree (gcd H n)`) has
`H ≥ fSum σ`: the shape's degree sum pins `gcd H n = fSum σ`, so `fSum σ ∣ H` and `H ≥ 1`. -/
theorem wPath_H_min {n H N : ℕ} {σ : FactorizationType} (_h : constERam n σ)
    (hP : MenuPath n N [((0 : ℕ), H), ((n : ℕ), (0 : ℕ))])
    (hsh : ShapesFor [((0 : ℕ), H), ((n : ℕ), (0 : ℕ))] [wShape σ]) :
    fSum σ ≤ H := by
  -- `ShapesFor` pins the shape to the side degree `gcd H n`
  have hmem : wShape σ ∈ shapesOfDegree
      (sideDeg (((0, H), (n, 0)) : (ℕ × ℕ) × (ℕ × ℕ))) := by
    have hsh' := hsh
    unfold ShapesFor at hsh'
    rw [show sidePairs [((0 : ℕ), H), ((n : ℕ), (0 : ℕ))]
        = [(((0, H), (n, 0)) : (ℕ × ℕ) × (ℕ × ℕ))] from rfl] at hsh'
    cases hsh' with
    | cons hh _ => exact hh
  have hsum := (mem_shapesOfDegree_iff.mp hmem).2.2
  -- the shape's degree sum is `fSum σ`
  have hws : ((wShape σ).map (fun q => q.1 * q.2)).sum = fSum σ := by
    rw [List.map_congr_left (fun q hq => by
      rw [wShape_mu σ q hq, Nat.mul_one] : ∀ q ∈ wShape σ, q.1 * q.2 = Prod.fst q)]
    exact wShape_fst_sum σ
  -- hence `gcd H n = fSum σ`, so `fSum σ ∣ H`
  have hgcd : Nat.gcd H n = fSum σ := by
    have h1 : sideDeg (((0, H), (n, 0)) : (ℕ × ℕ) × (ℕ × ℕ)) = Nat.gcd H n := by
      change Nat.gcd (H - 0) (n - 0) = Nat.gcd H n
      rw [Nat.sub_zero, Nat.sub_zero]
    rw [← h1, ← hsum]
    exact hws
  have hdvd : fSum σ ∣ H := hgcd ▸ Nat.gcd_dvd_left H n
  -- `H ≥ 1` from the menu-path height bound
  have hH1 : 1 ≤ H := by
    obtain ⟨H', p1, T, heq, hH1', -, -, -, -⟩ := hP
    have h0 : ((0 : ℕ), H) = ((0 : ℕ), H') := by
      have := congrArg List.head? heq
      simpa using this
    have hHH : H = H' := congrArg Prod.snd h0
    omega
  exact Nat.le_of_dvd (by omega) hdvd

/-! ## 3. `ramShape` — the canonical `Tselfloop` literal -/

/-- **The canonical wild stratum shape of σ** (blueprint §2 item 1): for constant-e ramified σ,
the `Tselfloop` literal on the minimal-H self-loop side `((0, fSum σ), (n, 0))` with the
canonical all-μ=1 residual shape; `none` otherwise. -/
noncomputable def ramShape (n : ℕ) (σ : FactorizationType) : Option ClusterShape :=
  if constERam n σ then
    some (ClassifierBridgeFiber.Tselfloop n
      (((0, fSum σ), (n, 0)) : (ℕ × ℕ) × (ℕ × ℕ)) (wShape σ))
  else none

theorem ramShape_of_constERam {n : ℕ} {σ : FactorizationType} (h : constERam n σ) :
    ramShape n σ = some (ClassifierBridgeFiber.Tselfloop n
      (((0, fSum σ), (n, 0)) : (ℕ × ℕ) × (ℕ × ℕ)) (wShape σ)) := by
  rw [ramShape, if_pos h]

theorem ramShape_of_not_constERam {n : ℕ} {σ : FactorizationType} (h : ¬ constERam n σ) :
    ramShape n σ = none := by
  rw [ramShape, if_neg h]

theorem constERam_of_ramShape {n : ℕ} {σ : FactorizationType} {T : ClusterShape}
    (h : ramShape n σ = some T) : constERam n σ := by
  by_contra hc
  rw [ramShape_of_not_constERam hc] at h
  simp at h

theorem ramShape_some_eq {n : ℕ} {σ : FactorizationType} {T : ClusterShape}
    (h : ramShape n σ = some T) :
    T = ClassifierBridgeFiber.Tselfloop n
      (((0, fSum σ), (n, 0)) : (ℕ × ℕ) × (ℕ × ℕ)) (wShape σ) := by
  have hc := constERam_of_ramShape h
  rw [ramShape_of_constERam hc] at h
  exact (Option.some.inj h).symm

/-! ## 4. The witness bundle (the banked legs' hypothesis package) -/

/-- **A single-slope self-loop witness for a shape `T`**: exactly the side-condition package of
the banked order-1 counting legs (`ClassifierBridgeFiber2.hnode_selfloop_over_Bclassify_R`,
`stratumCount_selfloop_R`, `classify_eq_selfloop_iff`). W1b consumes this bundle without
re-deriving anything. `hHN₀` pins the base level to `H + 1` — the eventual-constancy threshold
of the normalized ramified stratum count (see `WildMenuPrep`). -/
structure SelfLoopWitness (n : ℕ) (T : ClusterShape) where
  /-- the self-loop height (left endpoint `(0,H)`). -/
  H : ℕ
  /-- the base menu level. -/
  N₀ : ℕ
  /-- the menu path. -/
  P : List (ℕ × ℕ)
  /-- the all-μ=1 residual shape. -/
  shape : List (ℕ × ℕ)
  hN₀ : 0 < N₀
  /-- the base level is pinned to `H + 1`. -/
  hHN₀ : N₀ = H + 1
  hn : 0 < n
  hP : MenuPath n N₀ P
  hsingle : sidePairs P = [(((0, H), (n, 0)) : (ℕ × ℕ) × (ℕ × ℕ))]
  hsh : ShapesFor P [shape]
  hpos : ∀ q ∈ shape, 1 ≤ q.1
  hμ : ∀ q ∈ shape, q.2 = 1
  hne : shape ≠ []
  /-- `T` is the `Tselfloop` literal of this data. -/
  hT : T = ClassifierBridgeFiber.Tselfloop n
    (((0, H), (n, 0)) : (ℕ × ℕ) × (ℕ × ℕ)) shape

/-- **The canonical witness of a `ramShape` output**: `H = fSum σ`, `N₀ = fSum σ + 1`,
`P = wPath n σ`, `shape = wShape σ`, all side conditions discharged from the §2 bank. -/
noncomputable def ramShapeWitness {n : ℕ} {σ : FactorizationType} {T : ClusterShape}
    (h : ramShape n σ = some T) : SelfLoopWitness n T where
  H := fSum σ
  N₀ := fSum σ + 1
  P := wPath n σ
  shape := wShape σ
  hN₀ := Nat.succ_pos _
  hHN₀ := rfl
  hn := constERam_n_pos (constERam_of_ramShape h)
  hP := menuPath_wPath (constERam_of_ramShape h)
  hsingle := sidePairs_wPath n σ
  hsh := shapesFor_wPath (constERam_of_ramShape h)
  hpos := wShape_pos (constERam_of_ramShape h)
  hμ := wShape_mu σ
  hne := wShape_ne (constERam_of_ramShape h)
  hT := ramShape_some_eq h

/-! ## 5. `typeOfW` — reading the type off the shape literal -/

/-- The `dS`-list of a shape's payload cells. -/
def dSListOf (T : ClusterShape) : List ℕ := T.cells.map (fun c => c.dS)

/-- The head residual degree of a shape's tree (the `dr` slot of the root tuple; `0` for the
empty tree). -/
def headDr (T : ClusterShape) : ℕ := ((T.tree.head?).map (fun t => t.2.2)).getD 0

/-- **The wild σ-decoder**: reads the factorization type off the shape literal.
* Order-0 separable head `[(0, n, n)]` (the `sepShape` family): unramified type, `(1, d)` per
  payload `dS`.
* Order-0 head `[(0, n, dr)]` with `0 < dr < n` (the `Tselfloop` family): constant-e ramified
  type with `e = n/dr`, `(n/dr, f)` per payload `dS`.
* Anything else: `none`. -/
noncomputable def typeOfW (n : ℕ) (T : ClusterShape) : Option FactorizationType :=
  if T.tree = [((0 : ℕ), n, n)] then
    some ⟨((dSListOf T : List ℕ) : Multiset ℕ).map (fun d => ((1 : ℕ), d))⟩
  else if T.tree = [((0 : ℕ), n, headDr T)] ∧ 0 < headDr T ∧ headDr T < n then
    some ⟨((dSListOf T : List ℕ) : Multiset ℕ).map (fun f => (n / headDr T, f))⟩
  else none

/-- The head tree of an order-0 separable shape (the discriminating invariant, unram side). -/
theorem tree_sepShape (n : ℕ) (lam : Nat.Partition n) :
    (Order0.sepShape n lam).tree = [((0 : ℕ), n, n)] := rfl

/-- The head tree of a `ramShape` output (the discriminating invariant, wild side):
`[(0, n, fSum σ)]` with `fSum σ < n`. -/
theorem tree_ramShape {n : ℕ} {σ : FactorizationType} {T : ClusterShape}
    (h : ramShape n σ = some T) : T.tree = [((0 : ℕ), n, fSum σ)] := by
  rw [ramShape_some_eq h]
  change [((0 : ℕ), n, ((wShape σ).map Prod.fst).sum)] = [((0 : ℕ), n, fSum σ)]
  rw [wShape_fst_sum]

/-- On the order-0 separable image, `typeOfW` recovers the `unramType` keying. -/
theorem typeOfW_sepShape (n : ℕ) (lam : Nat.Partition n) :
    typeOfW n (Order0.sepShape n lam) = some (Order0.unramType n lam) := by
  have hds : ((dSListOf (Order0.sepShape n lam) : List ℕ) : Multiset ℕ) = lam.parts := by
    unfold dSListOf Order0.sepShape
    rw [List.map_map]
    rw [show ((fun c : ShapeCell => c.dS)
        ∘ fun d : ℕ => (⟨d, 1, Order0.flatFace n, []⟩ : ShapeCell)) = id from rfl]
    rw [List.map_id]
    exact Multiset.sort_eq _ _
  rw [typeOfW, if_pos (tree_sepShape n lam), hds]
  rfl

/-- On the `ramShape` image, `typeOfW` recovers σ. -/
theorem typeOfW_ramShape {n : ℕ} {σ : FactorizationType} {T : ClusterShape}
    (h : ramShape n σ = some T) : typeOfW n T = some σ := by
  have hc := constERam_of_ramShape h
  obtain ⟨e, he2, hne, hall, hprod⟩ := hc
  have hc' : constERam n σ := ⟨e, he2, hne, hall, hprod⟩
  have hfpos := constERam_fSum_pos hc'
  have hflt := constERam_fSum_lt hc'
  have htree := tree_ramShape h
  have hdr : headDr T = fSum σ := by rw [headDr, htree]; rfl
  -- the unramified branch does not fire (`fSum σ < n`)
  have hne1 : ¬ (T.tree = [((0 : ℕ), n, n)]) := by
    rw [htree]
    intro heq
    have hhead := List.head_eq_of_cons_eq heq
    have hval : fSum σ = n := by
      have := congrArg (fun t : ℕ × ℕ × ℕ => t.2.2) hhead
      simpa using this
    omega
  -- the payload `dS`-multiset is the `f`-parts multiset
  have hcells : ((dSListOf T : List ℕ) : Multiset ℕ) = σ.data.map Prod.snd := by
    rw [ramShape_some_eq h]
    unfold dSListOf
    rw [show (ClassifierBridgeFiber.Tselfloop n
        (((0, fSum σ), (n, 0)) : (ℕ × ℕ) × (ℕ × ℕ)) (wShape σ)).cells
        = (wShape σ).map (fun q => (⟨q.1, 1,
            M7.toSideFace (mkSide (((0, fSum σ), (n, 0)) : (ℕ × ℕ) × (ℕ × ℕ))), []⟩
              : ShapeCell)) from rfl]
    rw [List.map_map]
    rw [show ((fun c : ShapeCell => c.dS) ∘ fun q : ℕ × ℕ => (⟨q.1, 1,
        M7.toSideFace (mkSide (((0, fSum σ), (n, 0)) : (ℕ × ℕ) × (ℕ × ℕ))), []⟩
          : ShapeCell)) = Prod.fst from rfl]
    rw [wShape, List.map_map]
    rw [show (Prod.fst ∘ fun f : ℕ => ((f, 1) : ℕ × ℕ)) = id from rfl]
    rw [List.map_id]
    exact Multiset.sort_eq _ _
  rw [typeOfW, if_neg hne1, if_pos ⟨by rw [htree, hdr], by omega, by omega⟩]
  rw [hdr, hcells, constERam_e_eq he2 hprod hfpos,
    data_eq_map_snd (fun pr hpr => (hall pr hpr).1)]

/-! ## 6. `omMenuW` — the extended σ-keyed menu and its disjointness bank -/

/-- **The Wave-1 σ-keyed menu**: the order-0 separable menu extended by the canonical wild
stratum (when σ is constant-e ramified). -/
noncomputable def omMenuW (n : ℕ) (σ : FactorizationType) : Finset ClusterShape :=
  Order0.sepShapesOf n σ ∪ (ramShape n σ).toFinset

/-- **Cross-family disjointness**: a `ramShape` output is never an order-0 separable menu shape
— the head trees differ (`dr = fSum σ < n` vs `dr = n`). -/
theorem ramShape_not_mem_sepShapesOf {n : ℕ} {σ σ' : FactorizationType} {T : ClusterShape}
    (h : ramShape n σ = some T) : T ∉ Order0.sepShapesOf n σ' := by
  intro hmem
  simp only [Order0.sepShapesOf, Finset.mem_image, Finset.mem_filter, Finset.mem_univ,
    true_and] at hmem
  obtain ⟨lam, -, hT⟩ := hmem
  have h1 := tree_ramShape h
  rw [← hT] at h1
  rw [tree_sepShape n lam] at h1
  have hval : n = fSum σ := by
    have hhead := List.head_eq_of_cons_eq h1
    have := congrArg (fun t : ℕ × ℕ × ℕ => t.2.2) hhead
    simpa using this
  have := constERam_fSum_lt (constERam_of_ramShape h)
  omega

/-- **`ramShape` is injective in σ** (on its `some`-domain): the shape names its type through
`typeOfW`. -/
theorem ramShape_injective {n : ℕ} {σ σ' : FactorizationType} {T : ClusterShape}
    (h : ramShape n σ = some T) (h' : ramShape n σ' = some T) : σ = σ' := by
  have h1 := typeOfW_ramShape h
  have h2 := typeOfW_ramShape h'
  rw [h1] at h2
  exact Option.some.inj h2

/-- **The cross-σ disjointness lever**: every menu shape names its type. -/
theorem mem_omMenuW_type {n : ℕ} {σ : FactorizationType} {T : ClusterShape}
    (hT : T ∈ omMenuW n σ) : typeOfW n T = some σ := by
  rw [omMenuW, Finset.mem_union] at hT
  rcases hT with h | h
  · simp only [Order0.sepShapesOf, Finset.mem_image, Finset.mem_filter, Finset.mem_univ,
      true_and] at h
    obtain ⟨lam, hσ, rfl⟩ := h
    rw [typeOfW_sepShape n lam, hσ]
  · rw [Option.mem_toFinset, Option.mem_def] at h
    exact typeOfW_ramShape h

/-- Distinct types have disjoint menus. -/
theorem eq_of_mem_omMenuW {n : ℕ} {σ σ' : FactorizationType} {T : ClusterShape}
    (h : T ∈ omMenuW n σ) (h' : T ∈ omMenuW n σ') : σ = σ' := by
  have h1 := mem_omMenuW_type h
  have h2 := mem_omMenuW_type h'
  rw [h1] at h2
  exact Option.some.inj h2

/-- For non-constant-e σ (in particular every unramified σ) the menu is the order-0 menu. -/
theorem omMenuW_unram {n : ℕ} {σ : FactorizationType} (h : ¬ constERam n σ) :
    omMenuW n σ = Order0.sepShapesOf n σ := by
  rw [omMenuW, ramShape_of_not_constERam h, Option.toFinset_none, Finset.union_empty]

/-- A constant-e ramified σ has an EMPTY order-0 separable menu (no partition's `unramType`
has a pair with `e ≥ 2`). -/
theorem sepShapesOf_empty_of_constERam {n : ℕ} {σ : FactorizationType} (h : constERam n σ) :
    Order0.sepShapesOf n σ = ∅ := by
  rw [Order0.sepShapesOf, Finset.image_eq_empty, Finset.filter_eq_empty_iff]
  intro lam _ heq
  obtain ⟨e, he2, hne, hall, -⟩ := h
  subst heq
  obtain ⟨pr, hpr⟩ := Multiset.exists_mem_of_ne_zero hne
  have h1 : pr.1 = 1 := by
    have hpr' : pr ∈ lam.parts.map (fun d => ((1 : ℕ), d)) := hpr
    rw [Multiset.mem_map] at hpr'
    obtain ⟨d, -, rfl⟩ := hpr'
    rfl
  have := (hall pr hpr).1
  omega

/-- For constant-e ramified σ the menu is EXACTLY the canonical wild stratum singleton. -/
theorem omMenuW_ram_of_constE {n : ℕ} {σ : FactorizationType} (h : constERam n σ) :
    omMenuW n σ = {ClassifierBridgeFiber.Tselfloop n
      (((0, fSum σ), (n, 0)) : (ℕ × ℕ) × (ℕ × ℕ)) (wShape σ)} := by
  rw [omMenuW, sepShapesOf_empty_of_constERam h, ramShape_of_constERam h,
    Option.toFinset_some, Finset.empty_union]

/-- Every menu shape has tree size `n` (degree read-back off the root slot). -/
theorem treeSize_of_mem_omMenuW {n : ℕ} {σ : FactorizationType} {T : ClusterShape}
    (hT : T ∈ omMenuW n σ) : M6.treeSize T = n := by
  rw [omMenuW, Finset.mem_union] at hT
  rcases hT with h | h
  · simp only [Order0.sepShapesOf, Finset.mem_image, Finset.mem_filter, Finset.mem_univ,
      true_and] at h
    obtain ⟨lam, -, rfl⟩ := h
    rfl
  · rw [Option.mem_toFinset, Option.mem_def] at h
    unfold M6.treeSize
    rw [tree_ramShape h]

end LeanUrat.OM.WildMenu
