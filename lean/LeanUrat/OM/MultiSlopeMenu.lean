/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.OM.WildMenuW3
import LeanUrat.OM.PathShapeMultiSideTree
import LeanUrat.OM.Order0Fiber
import LeanUrat.RatFn

/-!
# MultiSlopeMenu — mixed-e types via multi-slope strata with product coefficients (Wave 4a,
`notes/WILD_WAVE4_BLUEPRINT_2026-07-22.md` §2-W4a items 1–5)

**Scope (blueprint §0).** Mixed-e factorization types: all side-`e`'s ≥ 2, pairwise DISTINCT
(one Newton side per distinct `e`, canonical minimal height `k = 1` per side), all-μ=1 per-side
residuals, order ≤ 1. NOT covered (deferred, named in the blueprint): `e = 1` mixing (flat
sides), same-`e` multi-side, per-side K-windows, order ≥ 2.

**ERRATUM APPLIED (coordinator, 2026-07-22, externally gated).** The blueprint's side ordering
gloss "increasing slope = decreasing e" is WRONG: the side of the `e`-group has run `e·F_e`,
drop `F_e`, hence slope `−1/e`, which INCREASES with `e`. F4 (strictly increasing slopes left
to right) therefore forces the canonical `mixedShape` to order the groups by INCREASING `e`
(steepest side first). For σ = {(2,1),(3,1)} at `n = 5` the canonical path is
`(0,2) → (2,1) → (5,0)` (`e = 2` side first). The admissibility bank below verifies F4 for this
ascending order (`chainOK_vertsFrom`).

Contents (blueprint §2-W4a items 1–5):
1. `multiSideLit n P sh` — the multi-slope `ClusterShape` literal: the TREE carries the full
   path numerically (`(1, n, #sides) :: P`, order-slot `1` ≠ every order-0 head), the CELLS
   carry the per-side parts δ-TAGGED by side index (`δ = j + 1`); `decodePath`/`decodeShapes`
   invert it; `multiSideLit_injective` (on the all-μ=1, length-matched domain — see the
   encoding note below).
2. Family discriminators: `multiSideLit_ne_sepShape`, `multiSideLit_ne_Tselfloop` (head
   order-slot `1` vs `0`).
3. `typeOf4` — the σ-decoder: on multi-slope heads reads, per side `j`, `e_j = run_j/sideDeg_j`
   and the δ-tagged `dS` payloads; on all other heads defers to `WildMenu.typeOfW`.
   `typeOf4_multiSideLit` (recovery on the canonical family), `typeOf4_typeOfW_compat`.
4. `mixedOK n σ` + `mixedTypes n` (the finite Finset characterization `mem_mixedTypes`);
   `mixedShape n σ` — the canonical minimal literal; the admissibility bank
   (`menuPath_mixedPath_of_le`, `shapesFor_mixedPath`, `allMuOne_mixedSh`,
   `allNonempty_mixedSh`); `omMenu4 = omMenuW3 ∪ mixedShape.toFinset` with the recovery gate
   `omMenu4_eq_of_not_mixed`.
5. `stratumCount4` (genuine order-1 `stratumCount1`-count on the mixed leg, `M8.stratumCount`
   on the old legs) and `C4` (per-side `omCount (sideSubShape …)` PRODUCT on the mixed leg,
   `omCount` on the old legs); `C4_isRational` (product closure) and `stratum_tendsto_C4_mixed`
   (via `hnode_multiSideProduct` at `M9.realP`).
6. The keystone disjointness bank at the box-subset level (`inCell_sep_disjoint`,
   `inCell_mixed_selfloop_disjoint`, `mixedCell_injective`) and the box bound
   `sum_stratumCount4_le_box` over the enlarged type menu `typeMenu4 = typeMenuW ∪ mixedTypes`;
   small-N vanishing (`stratumCount4_mixed_smallN`), level constancy
   (`normStratumCount4_mixed_levelConst`), full monotonicity (`normSum_omMenu4_mono`).

**Encoding note (blueprint §3 risk item, resolved).** `ShapeCell` carries `dS`, `δ`, `polygon`,
`children`; the part `(f, μ)` of side `j` is encoded as `⟨dS := f, δ := j + 1,
polygon := toSideFace (mkSide pr_j), children := []⟩`. The `δ` slot serves as the SIDE TAG as
preferred by the blueprint; the multiplicity μ is NOT encoded (there is no free slot), so the
decode reads parts back as `(dS, 1)` and injectivity is stated on the all-μ=1 domain
(`AllMuOne`) — exact for this wave's whole canonical family, whose parts are all `(f, 1)`.

Leaf module: no existing file is modified. No axiom, no sorry.
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

namespace LeanUrat.OM.MultiSlopeMenu

open scoped Classical
open LeanUrat LeanUrat.OM Finset
open LeanUrat.OM.CellMenu
open LeanUrat.OM.OMCountV2 (omCount NodeConfig omCount_isRational)
open LeanUrat.OM.PathShapeMultiSideTree (sideSubShape AllMuOne AllNonempty)
open LeanUrat.RatFn

/-! ## 1. The multi-slope literal and its decode -/

/-- The head order slot of a shape's tree (`0` for every order-0 family head, `1` for the
multi-slope literal family; `0` for the empty tree). -/
def headOrd (T : ClusterShape) : ℕ := ((T.tree.head?).map (fun t => t.1)).getD 0

/-- The δ-tagged per-side cell blocks: side `j` (0-based; tag `δ = j + 1`) contributes one
childless cell per part `(f, μ)` of its shape — `dS := f`, polygon the side's own face. The μ
slot is NOT encoded (all-μ=1 regime; see the module docstring). -/
noncomputable def cellsAux : ℕ → List ((ℕ × ℕ) × (ℕ × ℕ)) → List (List (ℕ × ℕ)) → List ShapeCell
  | _, [], _ => []
  | _, _ :: _, [] => []
  | j, pr :: prs, shape :: shs =>
      shape.map (fun q => (⟨q.1, j + 1, M7.toSideFace (mkSide pr), []⟩ : ShapeCell))
        ++ cellsAux (j + 1) prs shs

/-- **The multi-slope literal** (blueprint §2-W4a item 1): the tree carries the full path
numerically — head `(1, n, #sides)` (order-slot `1`, discriminating from every order-0 head),
then one `(0, j, v)` entry per vertex — and the cells carry the per-side parts δ-tagged by
side index. -/
noncomputable def multiSideLit (n : ℕ) (P : List (ℕ × ℕ)) (sh : List (List (ℕ × ℕ))) :
    ClusterShape :=
  ⟨((1 : ℕ), n, (sidePairs P).length) :: P.map (fun v => ((0 : ℕ), v.1, v.2)),
   cellsAux 0 (sidePairs P) sh⟩

theorem headOrd_multiSideLit (n : ℕ) (P : List (ℕ × ℕ)) (sh : List (List (ℕ × ℕ))) :
    headOrd (multiSideLit n P sh) = 1 := rfl

/-- Decode the path off the tree tail (exact — no admissibility needed). -/
def decodePath (T : ClusterShape) : List (ℕ × ℕ) := T.tree.tail.map (fun t => (t.2.1, t.2.2))

theorem decodePath_multiSideLit (n : ℕ) (P : List (ℕ × ℕ)) (sh : List (List (ℕ × ℕ))) :
    decodePath (multiSideLit n P sh) = P := by
  show (P.map (fun v => ((0 : ℕ), v.1, v.2))).map (fun t => (t.2.1, t.2.2)) = P
  rw [List.map_map]
  induction P with
  | nil => rfl
  | cons v P ih => rw [List.map_cons, ih]; rfl

/-- Decode the per-side shapes off the δ-tagged cells; parts read back as `(dS, 1)` (the
all-μ=1 regime of this wave). -/
def decodeShapes (T : ClusterShape) : List (List (ℕ × ℕ)) :=
  (List.range (sidePairs (decodePath T)).length).map
    (fun j => (T.cells.filter (fun c => c.δ == j + 1)).map (fun c => (c.dS, 1)))

/-- Every cell of `cellsAux j₀ …` carries a tag `δ ≥ j₀ + 1`. -/
theorem cellsAux_delta_le :
    ∀ (prs : List ((ℕ × ℕ) × (ℕ × ℕ))) (shs : List (List (ℕ × ℕ))) (j₀ : ℕ),
      ∀ c ∈ cellsAux j₀ prs shs, j₀ + 1 ≤ c.δ := by
  intro prs
  induction prs with
  | nil => intro shs j₀ c hc; simp [cellsAux] at hc
  | cons pr prs ih =>
      intro shs j₀ c hc
      cases shs with
      | nil => simp [cellsAux] at hc
      | cons shape shs =>
          simp only [cellsAux, List.mem_append] at hc
          rcases hc with hc | hc
          · rw [List.mem_map] at hc
            obtain ⟨q, -, rfl⟩ := hc
            exact le_refl _
          · have := ih shs (j₀ + 1) c hc
            omega

/-- The head block passes its own δ-filter unchanged. -/
theorem filter_block_self (j : ℕ) (pr : (ℕ × ℕ) × (ℕ × ℕ)) (shape : List (ℕ × ℕ)) :
    (shape.map (fun q => (⟨q.1, j + 1, M7.toSideFace (mkSide pr), []⟩ : ShapeCell))).filter
        (fun c => c.δ == j + 1)
      = shape.map (fun q => (⟨q.1, j + 1, M7.toSideFace (mkSide pr), []⟩ : ShapeCell)) := by
  rw [List.filter_eq_self]
  intro c hc
  rw [List.mem_map] at hc
  obtain ⟨q, -, rfl⟩ := hc
  simp

/-- Deeper blocks are invisible to lower δ-filters. -/
theorem filter_cellsAux_lower (prs : List ((ℕ × ℕ) × (ℕ × ℕ))) (shs : List (List (ℕ × ℕ)))
    (j₀ j : ℕ) (hj : j + 1 < j₀ + 1) :
    (cellsAux j₀ prs shs).filter (fun c => c.δ == j + 1) = [] := by
  rw [List.filter_eq_nil_iff]
  intro c hc
  have := cellsAux_delta_le prs shs j₀ c hc
  simp only [beq_iff_eq]
  omega

/-- **The decode core**: the δ-filter read-back over the tagged cell blocks returns the shape
list exactly (all-μ=1). -/
theorem decode_aux :
    ∀ (prs : List ((ℕ × ℕ) × (ℕ × ℕ))) (shs : List (List (ℕ × ℕ))) (j₀ : ℕ),
      shs.length = prs.length →
      (∀ shape ∈ shs, ∀ q ∈ shape, q.2 = 1) →
      (List.range prs.length).map
          (fun j => ((cellsAux j₀ prs shs).filter (fun c => c.δ == j₀ + j + 1)).map
            (fun c => (c.dS, 1))) = shs := by
  intro prs
  induction prs with
  | nil =>
      intro shs j₀ hlen _
      have : shs = [] := List.length_eq_zero_iff.mp hlen
      subst this
      rfl
  | cons pr prs ih =>
      intro shs j₀ hlen hμ
      cases shs with
      | nil => simp at hlen
      | cons shape shs =>
          rw [List.length_cons, List.range_succ_eq_map, List.map_cons, List.map_map]
          congr 1
          · -- the j = 0 slot: the head block
            simp only [cellsAux, List.filter_append]
            have h1 : (shape.map (fun q =>
                (⟨q.1, j₀ + 1, M7.toSideFace (mkSide pr), []⟩ : ShapeCell))).filter
                  (fun c => c.δ == j₀ + 0 + 1)
                = shape.map (fun q =>
                    (⟨q.1, j₀ + 1, M7.toSideFace (mkSide pr), []⟩ : ShapeCell)) := by
              rw [show j₀ + 0 + 1 = j₀ + 1 from by omega]
              exact filter_block_self j₀ pr shape
            have h2 : (cellsAux (j₀ + 1) prs shs).filter (fun c => c.δ == j₀ + 0 + 1) = [] :=
              filter_cellsAux_lower prs shs (j₀ + 1) (j₀ + 0) (by omega)
            rw [h1, h2, List.append_nil, List.map_map]
            have hμ0 := hμ shape List.mem_cons_self
            calc shape.map ((fun c : ShapeCell => (c.dS, 1)) ∘ (fun q =>
                    (⟨q.1, j₀ + 1, M7.toSideFace (mkSide pr), []⟩ : ShapeCell)))
                = shape.map (fun q => (q.1, 1)) := rfl
              _ = shape.map id := by
                  refine List.map_congr_left fun q hq => ?_
                  have := hμ0 q hq
                  simp only [id_eq]
                  exact Prod.ext rfl this.symm
              _ = shape := List.map_id shape
          · -- the j ≥ 1 slots: drop the head block, reindex, apply the IH at j₀ + 1
            have htail := ih shs (j₀ + 1) (by simpa using hlen)
              (fun s hs q hq => hμ s (List.mem_cons_of_mem _ hs) q hq)
            refine Eq.trans ?_ htail
            refine List.map_congr_left fun j _ => ?_
            simp only [Function.comp_apply]
            congr 1
            simp only [cellsAux, List.filter_append]
            have h3 : (shape.map (fun q =>
                (⟨q.1, j₀ + 1, M7.toSideFace (mkSide pr), []⟩ : ShapeCell))).filter
                  (fun c => c.δ == j₀ + (j + 1) + 1) = [] := by
              rw [List.filter_eq_nil_iff]
              intro c hc
              rw [List.mem_map] at hc
              obtain ⟨q, -, rfl⟩ := hc
              simp only [beq_iff_eq]
              omega
            rw [h3, List.nil_append]
            refine List.filter_congr fun c _ => ?_
            rw [show j₀ + (j + 1) + 1 = j₀ + 1 + j + 1 from by omega]

theorem decodeShapes_multiSideLit {n : ℕ} {P : List (ℕ × ℕ)} {sh : List (List (ℕ × ℕ))}
    (hlen : sh.length = (sidePairs P).length) (hμ : AllMuOne sh) :
    decodeShapes (multiSideLit n P sh) = sh := by
  unfold decodeShapes
  rw [decodePath_multiSideLit]
  have hcells : (multiSideLit n P sh).cells = cellsAux 0 (sidePairs P) sh := rfl
  rw [hcells]
  have h := decode_aux (sidePairs P) sh 0 hlen (fun s hs q hq => hμ s hs q hq)
  refine Eq.trans ?_ h
  refine List.map_congr_left fun j _ => ?_
  congr 1
  refine List.filter_congr fun c _ => ?_
  rw [Nat.zero_add]

/-- **Injectivity of the literal** on the admissible domain (per-side length match + all-μ=1):
the tree recovers `n` and `P` exactly, the δ-tagged cells recover `sh`. -/
theorem multiSideLit_injective {n n' : ℕ} {P P' : List (ℕ × ℕ)}
    {sh sh' : List (List (ℕ × ℕ))}
    (hlen : sh.length = (sidePairs P).length) (hlen' : sh'.length = (sidePairs P').length)
    (hμ : AllMuOne sh) (hμ' : AllMuOne sh')
    (heq : multiSideLit n P sh = multiSideLit n' P' sh') : n = n' ∧ P = P' ∧ sh = sh' := by
  have htree := congrArg ClusterShape.tree heq
  have hhead : ((1 : ℕ), n, (sidePairs P).length) = ((1 : ℕ), n', (sidePairs P').length) :=
    List.head_eq_of_cons_eq htree
  have hn : n = n' := congrArg (fun t : ℕ × ℕ × ℕ => t.2.1) hhead
  have hP : P = P' := by
    have h1 := decodePath_multiSideLit n P sh
    rw [heq, decodePath_multiSideLit] at h1
    exact h1.symm
  have hsh : sh = sh' := by
    have h1 := decodeShapes_multiSideLit (n := n) hlen hμ
    rw [heq, decodeShapes_multiSideLit hlen' hμ'] at h1
    exact h1.symm
  exact ⟨hn, hP, hsh⟩

/-! ## 2. Family discriminators (head order-slot `1` vs `0`) -/

theorem headOrd_sepShape (n : ℕ) (lam : Nat.Partition n) :
    headOrd (Order0.sepShape n lam) = 0 := rfl

theorem headOrd_Tselfloop (s : ℕ) (pr : (ℕ × ℕ) × (ℕ × ℕ)) (shape : List (ℕ × ℕ)) :
    headOrd (ClassifierBridgeFiber.Tselfloop s pr shape) = 0 := rfl

/-- **Discriminator 1**: a multi-slope literal is never an order-0 separable shape. -/
theorem multiSideLit_ne_sepShape (n m : ℕ) (P : List (ℕ × ℕ)) (sh : List (List (ℕ × ℕ)))
    (lam : Nat.Partition m) : multiSideLit n P sh ≠ Order0.sepShape m lam := by
  intro h
  have h1 := headOrd_multiSideLit n P sh
  rw [h, headOrd_sepShape] at h1
  exact absurd h1 zero_ne_one

/-- **Discriminator 2**: a multi-slope literal is never a `Tselfloop` shape. -/
theorem multiSideLit_ne_Tselfloop (n m : ℕ) (P : List (ℕ × ℕ)) (sh : List (List (ℕ × ℕ)))
    (pr : (ℕ × ℕ) × (ℕ × ℕ)) (shape : List (ℕ × ℕ)) :
    multiSideLit n P sh ≠ ClassifierBridgeFiber.Tselfloop m pr shape := by
  intro h
  have h1 := headOrd_multiSideLit n P sh
  rw [h, headOrd_Tselfloop] at h1
  exact absurd h1 zero_ne_one

/-- Every Wave-3 menu shape has an order-0 head (`sepShape` or `Tselfloop` family). -/
theorem headOrd_of_mem_omMenuW3 {n K : ℕ} {σ : FactorizationType} {T : ClusterShape}
    (hT : T ∈ WildMenuW3.omMenuW3 n K σ) : headOrd T = 0 := by
  rw [WildMenuW3.omMenuW3, Finset.mem_union] at hT
  rcases hT with h | h
  · simp only [Order0.sepShapesOf, Finset.mem_image, Finset.mem_filter, Finset.mem_univ,
      true_and] at h
    obtain ⟨lam, -, rfl⟩ := h
    rfl
  · rw [WildMenuW3.mem_ramShapes3] at h
    obtain ⟨hc, k, -, rfl⟩ := h
    rfl

/-! ## 3. σ-keying: `typeOf4` -/

/-- The ramification index of a side, read off its geometry: `e = run / d_S`
(on a canonical side of the `e`-group, `run = e·F_e` and `d_S = F_e`, so this is `e`). -/
def sideE (pr : (ℕ × ℕ) × (ℕ × ℕ)) : ℕ := (pr.2.1 - pr.1.1) / sideDeg pr

/-- The multi-slope σ-reader: per side `j` (left to right), one `(e_j, f)` pair per δ-tagged
payload cell. -/
def typeListAux : ℕ → List ((ℕ × ℕ) × (ℕ × ℕ)) → List ShapeCell → List (ℕ × ℕ)
  | _, [], _ => []
  | j, pr :: prs, cells =>
      ((cells.filter (fun c => c.δ == j + 1)).map (fun c => (sideE pr, c.dS)))
        ++ typeListAux (j + 1) prs cells

/-- **The Wave-4 σ-decoder** (blueprint §2-W4a item 2): on multi-slope heads (order-slot `1`)
assemble the multiset `⋃_j {(e_j, f) : f a δ-tagged payload of side j}`; on every other head
defer to the Wave-1/3 decoder `WildMenu.typeOfW`. -/
noncomputable def typeOf4 (n : ℕ) (T : ClusterShape) : Option FactorizationType :=
  if headOrd T = 1 then
    some ⟨((typeListAux 0 (sidePairs (decodePath T)) T.cells : List (ℕ × ℕ)) : Multiset (ℕ × ℕ))⟩
  else WildMenu.typeOfW n T

/-- **Compatibility with the Wave-1/3 decoder** on every non-multi-slope head. -/
theorem typeOf4_typeOfW_compat {n : ℕ} {T : ClusterShape} (h : headOrd T ≠ 1) :
    typeOf4 n T = WildMenu.typeOfW n T := by
  rw [typeOf4, if_neg h]

/-- The decoder keys every Wave-3 menu shape to its σ (compat + `mem_omMenuW3_type`). -/
theorem typeOf4_of_mem_omMenuW3 {n K : ℕ} {σ : FactorizationType} {T : ClusterShape}
    (hT : T ∈ WildMenuW3.omMenuW3 n K σ) : typeOf4 n T = some σ := by
  rw [typeOf4_typeOfW_compat (by rw [headOrd_of_mem_omMenuW3 hT]; exact zero_ne_one)]
  exact WildMenuW3.mem_omMenuW3_type hT

/-! ## 4. The canonical mixed menu: σ-side data -/

/-- The ascending list of distinct `e`-values of σ. -/
noncomputable def eVals (σ : FactorizationType) : List ℕ :=
  (σ.data.map Prod.fst).toFinset.sort (· ≤ ·)

/-- The residual-degree budget of the `e`-group: `F_e = Σ {f : (e, f) ∈ σ.data}`. -/
def Fof (σ : FactorizationType) (e : ℕ) : ℕ :=
  ((σ.data.filter (fun pr => pr.1 = e)).map Prod.snd).sum

/-- **The mixed-e predicate** (Wave 4a): σ nonempty, every pair with `e ≥ 2` and `f ≥ 1`,
degree `n`, and AT LEAST TWO distinct `e`-values. (One distinct `e` is Wave 1/3's constant-e
family — keeping the families apart is what keeps the counting fibers disjoint; the ≥ 2 sides
are also what the polygon-contradiction disjointness leg pins.) -/
def mixedOK (n : ℕ) (σ : FactorizationType) : Prop :=
  σ.data ≠ 0 ∧ (∀ pr ∈ σ.data, 2 ≤ pr.1 ∧ 1 ≤ pr.2) ∧ σ.degree = n
    ∧ 2 ≤ (σ.data.map Prod.fst).toFinset.card

theorem mem_eVals {σ : FactorizationType} {e : ℕ} :
    e ∈ eVals σ ↔ ∃ pr ∈ σ.data, pr.1 = e := by
  rw [eVals, Finset.mem_sort, Multiset.mem_toFinset, Multiset.mem_map]

theorem eVals_pairwise (σ : FactorizationType) : (eVals σ).Pairwise (· < ·) :=
  List.sortedLT_iff_pairwise.mp (Finset.sortedLT_sort _)

theorem eVals_ne_nil {n : ℕ} {σ : FactorizationType} (h : mixedOK n σ) : eVals σ ≠ [] := by
  obtain ⟨hne, -, -, -⟩ := h
  obtain ⟨pr, hpr⟩ := Multiset.exists_mem_of_ne_zero hne
  intro h0
  have hmem : pr.1 ∈ eVals σ := mem_eVals.mpr ⟨pr, hpr, rfl⟩
  rw [h0] at hmem
  simp at hmem

theorem two_le_eVals_length {n : ℕ} {σ : FactorizationType} (h : mixedOK n σ) :
    2 ≤ (eVals σ).length := by
  obtain ⟨-, -, -, hcard⟩ := h
  rw [eVals, Finset.length_sort]
  exact hcard

theorem eVals_two_le {n : ℕ} {σ : FactorizationType} (h : mixedOK n σ) :
    ∀ e ∈ eVals σ, 2 ≤ e := by
  intro e he
  obtain ⟨pr, hpr, rfl⟩ := mem_eVals.mp he
  exact (h.2.1 pr hpr).1

theorem Fof_pos {n : ℕ} {σ : FactorizationType} (h : mixedOK n σ) {e : ℕ}
    (he : e ∈ eVals σ) : 1 ≤ Fof σ e := by
  obtain ⟨pr, hpr, rfl⟩ := mem_eVals.mp he
  have hmem : pr ∈ σ.data.filter (fun pr' => pr'.1 = pr.1) :=
    Multiset.mem_filter.mpr ⟨hpr, rfl⟩
  have hle : pr.2 ≤ ((σ.data.filter (fun pr' => pr'.1 = pr.1)).map Prod.snd).sum :=
    Multiset.single_le_sum (fun x _ => Nat.zero_le x) _ (Multiset.mem_map_of_mem _ hmem)
  have hf := (h.2.1 pr hpr).2
  unfold Fof
  omega

theorem mixedOK_n_pos {n : ℕ} {σ : FactorizationType} (h : mixedOK n σ) : 0 < n := by
  obtain ⟨hne, hall, hdeg, -⟩ := h
  obtain ⟨pr, hpr⟩ := Multiset.exists_mem_of_ne_zero hne
  have h1 := (hall pr hpr).1
  have h2 := (hall pr hpr).2
  have hle : pr.1 * pr.2 ≤ σ.degree :=
    Multiset.single_le_sum (fun x _ => Nat.zero_le x) _ (Multiset.mem_map_of_mem _ hpr)
  have hprod : 2 * 1 ≤ pr.1 * pr.2 := Nat.mul_le_mul h1 h2
  omega

/-- Mixed types are NOT constant-e (≥ 2 distinct `e`'s vs a single one). -/
theorem mixedOK_not_constERam {n : ℕ} {σ : FactorizationType} (h : mixedOK n σ) :
    ¬ WildMenu.constERam n σ := by
  rintro ⟨e, -, -, hall, -⟩
  obtain ⟨-, -, -, hcard⟩ := h
  have hsub : (σ.data.map Prod.fst).toFinset ⊆ {e} := by
    intro x hx
    rw [Multiset.mem_toFinset, Multiset.mem_map] at hx
    obtain ⟨pr, hpr, rfl⟩ := hx
    rw [Finset.mem_singleton]
    exact (hall pr hpr).1
  have := Finset.card_le_card hsub
  rw [Finset.card_singleton] at this
  omega

/-- Mixed σ have an EMPTY order-0 separable menu (they carry a pair with `e ≥ 2`). -/
theorem sepShapesOf_empty_of_mixedOK {n : ℕ} {σ : FactorizationType} (h : mixedOK n σ) :
    Order0.sepShapesOf n σ = ∅ := by
  rw [Order0.sepShapesOf, Finset.image_eq_empty, Finset.filter_eq_empty_iff]
  intro lam _ heq
  obtain ⟨hne, hall, -, -⟩ := h
  obtain ⟨pr, hpr⟩ := Multiset.exists_mem_of_ne_zero hne
  have h2 := (hall pr hpr).1
  have h1 : pr.1 = 1 := by
    have hpr' : pr ∈ lam.parts.map (fun d => ((1 : ℕ), d)) := by
      rw [← show (Order0.unramType n lam).data = lam.parts.map (fun d => ((1 : ℕ), d)) from rfl,
        ← heq]
      exact hpr
    rw [Multiset.mem_map] at hpr'
    obtain ⟨d, -, rfl⟩ := hpr'
    rfl
  omega

/-! ### The e-group partition identities -/

/-- **The master partition identity**: the group filters over the distinct `e`-values
reassemble the multiset. -/
theorem sum_filter_fst (s : Multiset (ℕ × ℕ)) :
    ∑ e ∈ (s.map Prod.fst).toFinset, s.filter (fun pr => pr.1 = e) = s := by
  refine Multiset.ext.mpr fun pr => ?_
  rw [Multiset.count_sum']
  have hcnt : ∀ e ∈ (s.map Prod.fst).toFinset,
      (s.filter (fun pr' => pr'.1 = e)).count pr = if pr.1 = e then s.count pr else 0 :=
    fun e _ => Multiset.count_filter
  rw [Finset.sum_congr rfl hcnt, Finset.sum_ite_eq]
  by_cases hmem : pr ∈ s
  · rw [if_pos (Multiset.mem_toFinset.mpr (Multiset.mem_map_of_mem _ hmem))]
  · have h0 : s.count pr = 0 := Multiset.count_eq_zero_of_notMem hmem
    rw [h0]
    simp

/-- Push a `Multiset.map`+`sum` through a `Finset.sum` of multisets. -/
theorem multiset_map_sum_sum {ι β : Type*} [DecidableEq ι] (s : Finset ι)
    (m : ι → Multiset (ℕ × ℕ)) (g : ℕ × ℕ → β) [AddCommMonoid β] :
    ((∑ i ∈ s, m i).map g).sum = ∑ i ∈ s, ((m i).map g).sum := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
      rw [Finset.sum_insert hi, Finset.sum_insert hi, Multiset.map_add, Multiset.sum_add, ih]

/-- Transfer a sorted-list map-sum to the `Finset.sum`. -/
theorem sort_map_sum {β : Type*} [AddCommMonoid β] (s : Finset ℕ) (f : ℕ → β) :
    ((s.sort (· ≤ ·)).map f).sum = ∑ e ∈ s, f e := by
  calc ((s.sort (· ≤ ·)).map f).sum
      = ((((s.sort (· ≤ ·)).map f : List β) : Multiset β)).sum := (Multiset.sum_coe _).symm
    _ = (((s.sort (· ≤ ·) : List ℕ) : Multiset ℕ).map f).sum := by rw [Multiset.map_coe]
    _ = ((s.val).map f).sum := by rw [Finset.sort_eq]
    _ = ∑ e ∈ s, f e := rfl

/-- `Σ_{e ∈ eVals} F_e = fSum σ` (the canonical total height `H_total`). -/
theorem sum_Fof (σ : FactorizationType) :
    ((eVals σ).map (Fof σ)).sum = WildMenu.fSum σ := by
  rw [eVals, sort_map_sum]
  unfold Fof WildMenu.fSum
  rw [← multiset_map_sum_sum, sum_filter_fst]

/-- `Σ_{e ∈ eVals} e·F_e = n` (the canonical total width). -/
theorem sum_eFof {n : ℕ} {σ : FactorizationType} (h : mixedOK n σ) :
    ((eVals σ).map (fun e => e * Fof σ e)).sum = n := by
  obtain ⟨-, -, hdeg, -⟩ := h
  rw [eVals, sort_map_sum]
  have hstep : ∀ e ∈ (σ.data.map Prod.fst).toFinset,
      e * Fof σ e = (((σ.data.filter (fun pr => pr.1 = e))).map
        (fun pr => pr.1 * pr.2)).sum := by
    intro e _
    unfold Fof
    rw [← Multiset.sum_map_mul_left]
    congr 1
    refine Multiset.map_congr rfl fun pr hpr => ?_
    have := (Multiset.mem_filter.mp hpr).2
    show e * pr.2 = pr.1 * pr.2
    rw [this]
  rw [Finset.sum_congr rfl hstep, ← multiset_map_sum_sum, sum_filter_fst]
  exact hdeg

/-! ### The canonical per-side shape -/

/-- The canonical all-μ=1 residual shape of the `e`-group: sorted `(f, 1)` parts. -/
noncomputable def shapeOf (σ : FactorizationType) (e : ℕ) : List (ℕ × ℕ) :=
  (((σ.data.filter (fun pr => pr.1 = e)).map Prod.snd).sort (· ≤ ·)).map (fun f => (f, 1))

theorem shapeOf_mu (σ : FactorizationType) (e : ℕ) : ∀ q ∈ shapeOf σ e, q.2 = 1 := by
  intro q hq
  rw [shapeOf, List.mem_map] at hq
  obtain ⟨f, -, rfl⟩ := hq
  rfl

theorem shapeOf_fst_sum (σ : FactorizationType) (e : ℕ) :
    ((shapeOf σ e).map Prod.fst).sum = Fof σ e := by
  rw [shapeOf, List.map_map]
  rw [show (Prod.fst ∘ fun f : ℕ => ((f, 1) : ℕ × ℕ)) = id from rfl, List.map_id]
  rw [show (((σ.data.filter (fun pr => pr.1 = e)).map Prod.snd).sort (· ≤ ·)).sum
      = ((((σ.data.filter (fun pr => pr.1 = e)).map Prod.snd).sort (· ≤ ·) : List ℕ)
          : Multiset ℕ).sum from (Multiset.sum_coe _).symm]
  rw [Multiset.sort_eq]
  rfl

theorem shapeOf_pos {n : ℕ} {σ : FactorizationType} (h : mixedOK n σ) (e : ℕ) :
    ∀ q ∈ shapeOf σ e, 1 ≤ q.1 := by
  intro q hq
  rw [shapeOf, List.mem_map] at hq
  obtain ⟨f, hf, rfl⟩ := hq
  rw [Multiset.mem_sort, Multiset.mem_map] at hf
  obtain ⟨pr, hpr, rfl⟩ := hf
  exact (h.2.1 pr (Multiset.mem_filter.mp hpr).1).2

theorem shapeOf_ne {σ : FactorizationType} {e : ℕ} (he : e ∈ eVals σ) : shapeOf σ e ≠ [] := by
  obtain ⟨pr, hpr, rfl⟩ := mem_eVals.mp he
  intro hnil
  rw [shapeOf, List.map_eq_nil_iff] at hnil
  have hzero : (σ.data.filter (fun pr' => pr'.1 = pr.1)).map Prod.snd = 0 := by
    have := congrArg (fun l : List ℕ => (l : Multiset ℕ)) hnil
    simpa [Multiset.sort_eq] using this
  rw [Multiset.map_eq_zero] at hzero
  have : pr ∈ σ.data.filter (fun pr' => pr'.1 = pr.1) := Multiset.mem_filter.mpr ⟨hpr, rfl⟩
  rw [hzero] at this
  simp at this

theorem shapeOf_pairwise (σ : FactorizationType) (e : ℕ) :
    (shapeOf σ e).Pairwise shapeLE := by
  rw [shapeOf]
  refine List.Pairwise.map _ ?_ (Multiset.pairwise_sort _ (· ≤ ·))
  intro a b hab
  rcases Nat.lt_or_ge a b with hlt | hge
  · exact Or.inl hlt
  · exact Or.inr ⟨show a = b by omega, le_refl 1⟩

/-- The canonical group shape is a genuine residual shape of degree `F_e`. -/
theorem shapeOf_mem_shapesOfDegree {n : ℕ} {σ : FactorizationType} (h : mixedOK n σ)
    (e : ℕ) : shapeOf σ e ∈ shapesOfDegree (Fof σ e) := by
  rw [mem_shapesOfDegree_iff]
  refine ⟨shapeOf_pairwise σ e, ?_, ?_⟩
  · intro q hq
    exact ⟨shapeOf_pos h e q hq, le_of_eq (shapeOf_mu σ e q hq).symm⟩
  · rw [List.map_congr_left (fun q hq => by
      rw [shapeOf_mu σ e q hq, Nat.mul_one] : ∀ q ∈ shapeOf σ e, q.1 * q.2 = Prod.fst q)]
    exact shapeOf_fst_sum σ e

/-! ### The canonical path (ERRATUM APPLIED: groups in ASCENDING `e` = ascending slope `−1/e`,
steepest side first — the F4-admissible order) -/

/-- The vertex tail of the canonical path: one vertex per `e`-group, accumulated left to right
(run `e·F_e`, drop `F_e` per group). -/
noncomputable def vertsFrom (σ : FactorizationType) : List ℕ → ℕ → ℕ → List (ℕ × ℕ)
  | [], _, _ => []
  | e :: es, x, y =>
      (x + e * Fof σ e, y - Fof σ e) :: vertsFrom σ es (x + e * Fof σ e) (y - Fof σ e)

/-- **The canonical mixed menu path**: left endpoint `(0, H_total)` with
`H_total = Σ_e F_e = fSum σ`, then one side per `e`-group in ascending `e`. -/
noncomputable def mixedPath (σ : FactorizationType) : List (ℕ × ℕ) :=
  ((0 : ℕ), WildMenu.fSum σ) :: vertsFrom σ (eVals σ) 0 (WildMenu.fSum σ)

/-- **The canonical per-side shape list**: the group shapes in the same ascending-`e` order. -/
noncomputable def mixedSh (σ : FactorizationType) : List (List (ℕ × ℕ)) :=
  (eVals σ).map (shapeOf σ)

theorem vertsFrom_length (σ : FactorizationType) :
    ∀ (es : List ℕ) (x y : ℕ), (vertsFrom σ es x y).length = es.length := by
  intro es
  induction es with
  | nil => intro x y; rfl
  | cons e es ih => intro x y; simp only [vertsFrom, List.length_cons, ih]

/-- **The F4 chain invariant for the canonical tail** (the erratum-corrected order): with the
previous edge of slope `−1/eprev` (run `eprev·D`, drop `D`) and every remaining group `e`
strictly larger than `eprev`, the accumulated tail is a valid `ChainOK` continuation — the
slopes `−1/e` strictly INCREASE precisely because the `e`'s do. -/
theorem chainOK_vertsFrom {n : ℕ} (σ : FactorizationType) :
    ∀ (es : List ℕ) (x y eprev D : ℕ) (p0 : ℕ × ℕ),
      1 ≤ D → p0.1 + eprev * D = x → p0.2 = y + D →
      (∀ e ∈ es, eprev < e) → (∀ e ∈ es, 1 ≤ Fof σ e) →
      es.Pairwise (· < ·) →
      x + ((es.map (fun e => e * Fof σ e)).sum) = n →
      y = ((es.map (Fof σ)).sum) →
      ChainOK n p0 (x, y) (vertsFrom σ es x y) := by
  intro es
  induction es with
  | nil =>
      intro x y eprev D p0 hD hx hy hlt hF hpw hsx hsy
      simp only [List.map_nil, List.sum_nil] at hsx hsy
      exact ChainOK.nil (by omega) (by omega)
  | cons e es ih =>
      intro x y eprev D p0 hD hx hy hlt hF hpw hsx hsy
      simp only [List.map_cons, List.sum_cons] at hsx hsy
      have hFe : 1 ≤ Fof σ e := hF e List.mem_cons_self
      have hee : eprev < e := hlt e List.mem_cons_self
      have he1 : 1 ≤ e := by omega
      have heF : 1 ≤ e * Fof σ e := Nat.mul_le_mul he1 hFe
      have hyF : Fof σ e ≤ y := by omega
      show ChainOK n p0 (x, y)
        ((x + e * Fof σ e, y - Fof σ e)
          :: vertsFrom σ es (x + e * Fof σ e) (y - Fof σ e))
      refine ChainOK.cons (by omega) (by omega) ?_ ?_
      · -- SlopeLt p0 (x,y) (x,y) (x + e·F, y − F): slope −D/(eprev·D) < −F/(e·F) ⟺ eprev < e
        show ((((x, y) : ℕ × ℕ).2 : ℤ) - p0.2)
              * ((((x + e * Fof σ e, y - Fof σ e) : ℕ × ℕ).1 : ℤ) - ((x, y) : ℕ × ℕ).1)
            < ((((x + e * Fof σ e, y - Fof σ e) : ℕ × ℕ).2 : ℤ) - ((x, y) : ℕ × ℕ).2)
              * ((((x, y) : ℕ × ℕ).1 : ℤ) - p0.1)
        have hc1 : (p0.2 : ℤ) = (y : ℤ) + (D : ℤ) := by exact_mod_cast congrArg Nat.cast hy
        have hc2 : ((x + e * Fof σ e : ℕ) : ℤ) = (x : ℤ) + (e : ℤ) * (Fof σ e : ℤ) := by
          push_cast; ring
        have hc3 : ((y - Fof σ e : ℕ) : ℤ) = (y : ℤ) - (Fof σ e : ℤ) := by
          omega
        have hc4 : (p0.1 : ℤ) = (x : ℤ) - (eprev : ℤ) * (D : ℤ) := by
          have : (p0.1 : ℤ) + (eprev : ℤ) * (D : ℤ) = (x : ℤ) := by exact_mod_cast hx
          omega
        rw [hc1, hc2, hc3, hc4]
        have hkey : (eprev : ℤ) * D * Fof σ e < (e : ℤ) * D * Fof σ e := by
          have hnat : eprev * D * Fof σ e < e * D * Fof σ e := by
            have hpos : 0 < D * Fof σ e := Nat.mul_pos (by omega) (by omega)
            calc eprev * D * Fof σ e = eprev * (D * Fof σ e) := by ring
              _ < e * (D * Fof σ e) := Nat.mul_lt_mul_of_lt_of_le hee (le_refl _) hpos
              _ = e * D * Fof σ e := by ring
          exact_mod_cast hnat
        nlinarith [hkey]
      · exact ih (x + e * Fof σ e) (y - Fof σ e) e (Fof σ e) (x, y) hFe rfl (by omega)
          (fun e' he' => (List.pairwise_cons.mp hpw).1 e' he')
          (fun e' he' => hF e' (List.mem_cons_of_mem _ he'))
          (List.pairwise_cons.mp hpw).2 (by omega) (by omega)

/-- **The canonical path is a menu path** at every level `N ≥ H_total + 1` (F4 verified for the
ascending-`e` order; vertex arithmetic closes at `(n, 0)` by the width identity `sum_eFof`). -/
theorem menuPath_mixedPath_of_le {n N : ℕ} {σ : FactorizationType} (h : mixedOK n σ)
    (hN : WildMenu.fSum σ + 1 ≤ N) : MenuPath n N (mixedPath σ) := by
  obtain ⟨e₀, es, hes⟩ := List.exists_cons_of_ne_nil (eVals_ne_nil h)
  have hsF : WildMenu.fSum σ = Fof σ e₀ + (es.map (Fof σ)).sum := by
    rw [← sum_Fof σ, hes]
    simp
  have hsE : e₀ * Fof σ e₀ + (es.map (fun e => e * Fof σ e)).sum = n := by
    have hh := sum_eFof h
    rw [hes] at hh
    simpa using hh
  have hF₀ : 1 ≤ Fof σ e₀ := Fof_pos h (by rw [hes]; exact List.mem_cons_self)
  have he₀ : 2 ≤ e₀ := eVals_two_le h e₀ (by rw [hes]; exact List.mem_cons_self)
  have hpw : (e₀ :: es).Pairwise (· < ·) := by
    have := eVals_pairwise σ
    rwa [hes] at this
  have heF : 1 ≤ e₀ * Fof σ e₀ := Nat.mul_pos (by omega) hF₀
  refine ⟨WildMenu.fSum σ, (0 + e₀ * Fof σ e₀, WildMenu.fSum σ - Fof σ e₀),
    vertsFrom σ es (0 + e₀ * Fof σ e₀) (WildMenu.fSum σ - Fof σ e₀), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [mixedPath, hes, vertsFrom]
  · omega
  · omega
  · show 0 < 0 + e₀ * Fof σ e₀
    omega
  · show WildMenu.fSum σ - Fof σ e₀ < WildMenu.fSum σ
    omega
  · exact chainOK_vertsFrom σ es (0 + e₀ * Fof σ e₀) (WildMenu.fSum σ - Fof σ e₀) e₀
      (Fof σ e₀) ((0 : ℕ), WildMenu.fSum σ) hF₀ rfl (by omega)
      (fun e' he' => (List.pairwise_cons.mp hpw).1 e' he')
      (fun e' he' => Fof_pos h (by rw [hes]; exact List.mem_cons_of_mem _ he'))
      (List.pairwise_cons.mp hpw).2 (by omega) (by omega)

/-- The canonical path at its own base level `N₀ = H_total + 1`. -/
theorem menuPath_mixedPath {n : ℕ} {σ : FactorizationType} (h : mixedOK n σ) :
    MenuPath n (WildMenu.fSum σ + 1) (mixedPath σ) :=
  menuPath_mixedPath_of_le h (le_refl _)

/-- **The per-side admissibility chain**: along the accumulated tail, side `j` has run
`e_j·F_j`, drop `F_j`, hence `sideDeg = gcd(F, e·F) = F` — the group shape is admissible. -/
theorem shapesFor_vertsFrom {n : ℕ} {σ : FactorizationType} (h : mixedOK n σ) :
    ∀ (es : List ℕ) (x y : ℕ),
      (∀ e ∈ es, e ∈ eVals σ) →
      y = ((es.map (Fof σ)).sum) →
      List.Forall₂ (fun l pr => l ∈ shapesOfDegree (sideDeg pr))
        (es.map (shapeOf σ)) (sidePairs ((x, y) :: vertsFrom σ es x y)) := by
  intro es
  induction es with
  | nil => intro x y _ _; exact List.Forall₂.nil
  | cons e es ih =>
      intro x y hmem hsy
      simp only [List.map_cons, List.sum_cons] at hsy
      have hFe : 1 ≤ Fof σ e := Fof_pos h (hmem e List.mem_cons_self)
      show List.Forall₂ _ (shapeOf σ e :: es.map (shapeOf σ))
        (sidePairs (((x, y) : ℕ × ℕ)
          :: (x + e * Fof σ e, y - Fof σ e)
          :: vertsFrom σ es (x + e * Fof σ e) (y - Fof σ e)))
      rw [sidePairs_cons₂]
      refine List.Forall₂.cons ?_
        (ih (x + e * Fof σ e) (y - Fof σ e)
          (fun e' he' => hmem e' (List.mem_cons_of_mem _ he')) (by omega))
      have hdeg : sideDeg (((x, y), (x + e * Fof σ e, y - Fof σ e)) : (ℕ × ℕ) × (ℕ × ℕ))
          = Fof σ e := by
        show Nat.gcd (y - (y - Fof σ e)) (x + e * Fof σ e - x) = Fof σ e
        rw [show y - (y - Fof σ e) = Fof σ e from by omega,
          show x + e * Fof σ e - x = e * Fof σ e from by omega]
        exact Nat.gcd_eq_left (dvd_mul_left (Fof σ e) e)
      rw [hdeg]
      exact shapeOf_mem_shapesOfDegree h e

/-- **The canonical shape assignment is valid** for the canonical path. -/
theorem shapesFor_mixedPath {n : ℕ} {σ : FactorizationType} (h : mixedOK n σ) :
    ShapesFor (mixedPath σ) (mixedSh σ) := by
  unfold ShapesFor mixedSh mixedPath
  exact shapesFor_vertsFrom h (eVals σ) 0 (WildMenu.fSum σ) (fun e he => he)
    (sum_Fof σ).symm

theorem allMuOne_mixedSh (σ : FactorizationType) : AllMuOne (mixedSh σ) := by
  intro shape hs q hq
  rw [mixedSh, List.mem_map] at hs
  obtain ⟨e, -, rfl⟩ := hs
  exact shapeOf_mu σ e q hq

theorem allNonempty_mixedSh (σ : FactorizationType) : AllNonempty (mixedSh σ) := by
  intro shape hs
  rw [mixedSh, List.mem_map] at hs
  obtain ⟨e, he, rfl⟩ := hs
  exact shapeOf_ne he

theorem sidePairs_mixedPath_length (σ : FactorizationType) :
    (sidePairs (mixedPath σ)).length = (eVals σ).length := by
  show ((mixedPath σ).zip (mixedPath σ).tail).length = _
  rw [List.length_zip]
  simp only [mixedPath, List.length_cons, List.tail_cons, vertsFrom_length]
  omega

theorem mixedSh_length_eq (σ : FactorizationType) :
    (mixedSh σ).length = (sidePairs (mixedPath σ)).length := by
  rw [sidePairs_mixedPath_length, mixedSh, List.length_map]

/-! ### σ-recovery on the canonical family -/

/-- Blocks of low tag are invisible to the σ-reader's deeper filters. -/
theorem typeListAux_append_low :
    ∀ (prs : List ((ℕ × ℕ) × (ℕ × ℕ))) (block cells : List ShapeCell) (j₀ : ℕ),
      (∀ c ∈ block, c.δ ≤ j₀) →
      typeListAux j₀ prs (block ++ cells) = typeListAux j₀ prs cells := by
  intro prs
  induction prs with
  | nil => intro block cells j₀ _; rfl
  | cons pr prs ih =>
      intro block cells j₀ h
      simp only [typeListAux, List.filter_append]
      have hnil : block.filter (fun c => c.δ == j₀ + 1) = [] := by
        rw [List.filter_eq_nil_iff]
        intro c hc
        have := h c hc
        simp only [beq_iff_eq]
        omega
      rw [hnil, List.nil_append, ih block cells (j₀ + 1) (fun c hc => by
        have := h c hc; omega)]

/-- The geometric `e`-read is exact on a canonical side: `run / sideDeg = e·F / F = e`. -/
theorem sideE_canonical {x y e F : ℕ} (hF : 1 ≤ F) (hyF : F ≤ y) :
    sideE (((x, y), (x + e * F, y - F)) : (ℕ × ℕ) × (ℕ × ℕ)) = e := by
  unfold sideE sideDeg
  show (x + e * F - x) / Nat.gcd (y - (y - F)) (x + e * F - x) = e
  rw [show y - (y - F) = F from by omega, show x + e * F - x = e * F from by omega,
    Nat.gcd_eq_left (dvd_mul_left F e), Nat.mul_div_cancel _ (by omega : 0 < F)]

/-- **The σ-reader on the canonical data** returns, group by group in ascending `e`, the
sorted `(e, f)` pairs of the group. -/
theorem typeListAux_canonical {n : ℕ} {σ : FactorizationType} (h : mixedOK n σ) :
    ∀ (es : List ℕ) (x y j₀ : ℕ),
      (∀ e ∈ es, e ∈ eVals σ) →
      y = ((es.map (Fof σ)).sum) →
      typeListAux j₀ (sidePairs ((x, y) :: vertsFrom σ es x y))
          (cellsAux j₀ (sidePairs ((x, y) :: vertsFrom σ es x y)) (es.map (shapeOf σ)))
        = es.flatMap (fun e =>
            ((((σ.data.filter (fun pr => pr.1 = e)).map Prod.snd).sort (· ≤ ·)).map
              (fun f => (e, f)))) := by
  intro es
  induction es with
  | nil => intro x y j₀ _ _; rfl
  | cons e es ih =>
      intro x y j₀ hmem hsy
      simp only [List.map_cons, List.sum_cons] at hsy
      have hFe : 1 ≤ Fof σ e := Fof_pos h (hmem e List.mem_cons_self)
      have hyF : Fof σ e ≤ y := by omega
      -- name the head side and the tail path
      set x' := x + e * Fof σ e with hx'
      set y' := y - Fof σ e with hy'
      have hpath : ((x, y) : ℕ × ℕ) :: vertsFrom σ (e :: es) x y
          = (x, y) :: (x', y') :: vertsFrom σ es x' y' := rfl
      rw [hpath, sidePairs_cons₂]
      simp only [List.map_cons, typeListAux, cellsAux, List.filter_append, List.flatMap_cons]
      -- the head filter keeps exactly the head block, the deeper cells are invisible
      have h1 := filter_block_self j₀ (((x, y), (x', y')) : (ℕ × ℕ) × (ℕ × ℕ)) (shapeOf σ e)
      have h2 : (cellsAux (j₀ + 1) (sidePairs ((x', y') :: vertsFrom σ es x' y'))
          (es.map (shapeOf σ))).filter (fun c => c.δ == j₀ + 1) = [] :=
        filter_cellsAux_lower _ _ (j₀ + 1) j₀ (by omega)
      rw [h1, h2, List.append_nil]
      congr 1
      · -- the head block reads back the sorted (e, f) pairs of the e-group
        rw [List.map_map]
        rw [show ((fun c : ShapeCell => (sideE (((x, y), (x', y')) : (ℕ × ℕ) × (ℕ × ℕ)), c.dS))
            ∘ (fun q : ℕ × ℕ =>
              (⟨q.1, j₀ + 1, M7.toSideFace (mkSide (((x, y), (x', y')) : (ℕ × ℕ) × (ℕ × ℕ))), []⟩
                : ShapeCell)))
            = (fun q : ℕ × ℕ => (sideE (((x, y), (x', y')) : (ℕ × ℕ) × (ℕ × ℕ)), q.1)) from
          rfl]
        rw [shapeOf, List.map_map]
        refine List.map_congr_left fun f _ => ?_
        show (sideE (((x, y), (x', y')) : (ℕ × ℕ) × (ℕ × ℕ)), f) = (e, f)
        rw [hx', hy', sideE_canonical hFe hyF]
      · -- the tail: strip the (invisible) head block, apply the IH at j₀ + 1
        rw [typeListAux_append_low _ _ _ (j₀ + 1) (fun c hc => by
          rw [List.mem_map] at hc
          obtain ⟨q, -, rfl⟩ := hc
          exact le_refl _)]
        exact ih x' y' (j₀ + 1) (fun e' he' => hmem e' (List.mem_cons_of_mem _ he')) (by omega)

/-- Coerce a `flatMap` to the multiset sum of its blocks. -/
theorem coe_flatMap_eq_sum {α β : Type*} (l : List α) (g : α → List β) :
    ((l.flatMap g : List β) : Multiset β) = ((l.map (fun a => ((g a : List β) : Multiset β))).sum) := by
  induction l with
  | nil => rfl
  | cons a l ih =>
      simp only [List.flatMap_cons, List.map_cons, List.sum_cons, ← ih]
      rfl

/-- The sorted `(e, ·)`-tagged group list is, as a multiset, exactly the `e`-group of σ. -/
theorem coe_group_map (σ : FactorizationType) (e : ℕ) :
    (((((σ.data.filter (fun pr => pr.1 = e)).map Prod.snd).sort (· ≤ ·)).map
        (fun f => (e, f)) : List (ℕ × ℕ)) : Multiset (ℕ × ℕ))
      = σ.data.filter (fun pr => pr.1 = e) := by
  rw [← Multiset.map_coe, Multiset.sort_eq]
  rw [Multiset.map_map]
  conv_rhs => rw [← Multiset.map_id (σ.data.filter (fun pr => pr.1 = e))]
  refine Multiset.map_congr rfl fun pr hpr => ?_
  have hfst := (Multiset.mem_filter.mp hpr).2
  simp only [Function.comp_apply, id_eq]
  exact Prod.ext hfst.symm rfl

/-- **σ-recovery on the canonical literal** (blueprint §2-W4a item 2): the Wave-4 decoder
reads the canonical mixed literal back to its σ. -/
theorem typeOf4_multiSideLit {n : ℕ} {σ : FactorizationType} (h : mixedOK n σ) :
    typeOf4 n (multiSideLit n (mixedPath σ) (mixedSh σ)) = some σ := by
  rw [typeOf4, if_pos (headOrd_multiSideLit n (mixedPath σ) (mixedSh σ))]
  congr 1
  rw [decodePath_multiSideLit]
  have hcells : (multiSideLit n (mixedPath σ) (mixedSh σ)).cells
      = cellsAux 0 (sidePairs (mixedPath σ)) (mixedSh σ) := rfl
  rw [hcells]
  have hpath : mixedPath σ = ((0 : ℕ), WildMenu.fSum σ)
      :: vertsFrom σ (eVals σ) 0 (WildMenu.fSum σ) := rfl
  rw [hpath, show mixedSh σ = (eVals σ).map (shapeOf σ) from rfl,
    typeListAux_canonical h (eVals σ) 0 (WildMenu.fSum σ) 0 (fun e he => he)
      (sum_Fof σ).symm]
  -- assemble the multiset: ⋃ groups = σ.data
  have hassemble : ((((eVals σ).flatMap (fun e =>
      ((((σ.data.filter (fun pr => pr.1 = e)).map Prod.snd).sort (· ≤ ·)).map
        (fun f => (e, f))))) : List (ℕ × ℕ)) : Multiset (ℕ × ℕ)) = σ.data := by
    rw [coe_flatMap_eq_sum]
    rw [List.map_congr_left (fun e _ => coe_group_map σ e)]
    rw [eVals, sort_map_sum]
    exact sum_filter_fst σ.data
  exact congrArg FactorizationType.mk hassemble

/-! ### `mixedShape`, `omMenu4`, and the keying bank -/

/-- **The canonical mixed stratum shape** (blueprint §2-W4a item 3): the multi-slope literal on
the canonical minimal path (ascending-`e`, height-1-per-side) for mixed σ; `none` otherwise. -/
noncomputable def mixedShape (n : ℕ) (σ : FactorizationType) : Option ClusterShape :=
  if mixedOK n σ then some (multiSideLit n (mixedPath σ) (mixedSh σ)) else none

theorem mixedShape_of_mixedOK {n : ℕ} {σ : FactorizationType} (h : mixedOK n σ) :
    mixedShape n σ = some (multiSideLit n (mixedPath σ) (mixedSh σ)) := by
  rw [mixedShape, if_pos h]

theorem mixedShape_of_not_mixedOK {n : ℕ} {σ : FactorizationType} (h : ¬ mixedOK n σ) :
    mixedShape n σ = none := by
  rw [mixedShape, if_neg h]

/-- **The Wave-4 σ-keyed menu**: the Wave-3 window menu extended by the canonical mixed
stratum (empty extra branch unless σ is mixed-all-e≥2). -/
noncomputable def omMenu4 (n K : ℕ) (σ : FactorizationType) : Finset ClusterShape :=
  WildMenuW3.omMenuW3 n K σ ∪ (mixedShape n σ).toFinset

/-- **The recovery gate**: on every non-mixed σ the Wave-4 menu IS the Wave-3 menu. -/
theorem omMenu4_eq_of_not_mixed {n K : ℕ} {σ : FactorizationType} (h : ¬ mixedOK n σ) :
    omMenu4 n K σ = WildMenuW3.omMenuW3 n K σ := by
  rw [omMenu4, mixedShape_of_not_mixedOK h, Option.toFinset_none, Finset.union_empty]

/-- For mixed σ the Wave-4 menu is EXACTLY the canonical mixed singleton (mixed σ are neither
unramified nor constant-e, so both Wave-3 legs are empty). -/
theorem omMenu4_of_mixed {n K : ℕ} {σ : FactorizationType} (h : mixedOK n σ) :
    omMenu4 n K σ = {multiSideLit n (mixedPath σ) (mixedSh σ)} := by
  rw [omMenu4, WildMenuW3.omMenuW3, sepShapesOf_empty_of_mixedOK h,
    WildMenuW3.ramShapes3_of_not_constERam (mixedOK_not_constERam h),
    mixedShape_of_mixedOK h, Option.toFinset_some, Finset.empty_union, Finset.empty_union]

/-- Case analysis for `omMenu4` membership. -/
theorem mem_omMenu4_cases {n K : ℕ} {σ : FactorizationType} {T : ClusterShape}
    (hT : T ∈ omMenu4 n K σ) :
    T ∈ WildMenuW3.omMenuW3 n K σ
      ∨ (mixedOK n σ ∧ T = multiSideLit n (mixedPath σ) (mixedSh σ)) := by
  rw [omMenu4, Finset.mem_union] at hT
  rcases hT with hT | hT
  · exact Or.inl hT
  · rw [Option.mem_toFinset, Option.mem_def] at hT
    have hOK : mixedOK n σ := by
      by_contra hc
      rw [mixedShape_of_not_mixedOK hc] at hT
      simp at hT
    rw [mixedShape_of_mixedOK hOK] at hT
    exact Or.inr ⟨hOK, (Option.some.inj hT).symm⟩

/-- **The cross-σ disjointness lever**: every Wave-4 menu shape names its type. -/
theorem mem_omMenu4_type {n K : ℕ} {σ : FactorizationType} {T : ClusterShape}
    (hT : T ∈ omMenu4 n K σ) : typeOf4 n T = some σ := by
  rcases mem_omMenu4_cases hT with h | ⟨hOK, rfl⟩
  · exact typeOf4_of_mem_omMenuW3 h
  · exact typeOf4_multiSideLit hOK

/-- Distinct types have disjoint Wave-4 menus — at ANY two window bounds. -/
theorem eq_of_mem_omMenu4 {n K K' : ℕ} {σ σ' : FactorizationType} {T : ClusterShape}
    (h : T ∈ omMenu4 n K σ) (h' : T ∈ omMenu4 n K' σ') : σ = σ' := by
  have h1 := mem_omMenu4_type h
  have h2 := mem_omMenu4_type h'
  rw [h1] at h2
  exact Option.some.inj h2

/-! ## 5. The unified stratum count and coefficient -/

/-- **The Wave-4 stratum count** (blueprint §2-W4a item 4): on multi-slope literals, the
GENUINE order-1 stratum count `stratumCount1` over `classify1` at the decoded menu cell (kept
definitional through the decode — §3 risk item); on every other shape, the schematic
`M8.stratumCount` over `M9.rawCount` unchanged. -/
noncomputable def stratumCount4 (n : ℕ) (T : ClusterShape) (N : ℕ) : ℚ :=
  if headOrd T = 1 then
    ((StratumOrder1.stratumCount1 M9.realP n N (mkCell n (decodePath T) (decodeShapes T)) : ℕ) : ℚ)
  else M8.stratumCount (M9.rawCount n) T N

theorem stratumCount4_of_mem_omMenuW3 {n K : ℕ} {σ : FactorizationType} {T : ClusterShape}
    (hT : T ∈ WildMenuW3.omMenuW3 n K σ) (N : ℕ) :
    stratumCount4 n T N = M8.stratumCount (M9.rawCount n) T N := by
  rw [stratumCount4, if_neg (by rw [headOrd_of_mem_omMenuW3 hT]; exact zero_ne_one)]

/-- **The Wave-4 coefficient** (blueprint §2-W4a item 5): on multi-slope literals, the PRODUCT
over sides of the re-scoped single-side engine values `omCount (sideSubShape pr shape)`; on
every other shape, `omCount` unchanged. -/
noncomputable def C4 (T : ClusterShape) (q' : ℕ) : ℚ :=
  if headOrd T = 1 then
    (List.zipWith (fun pr shape => omCount (sideSubShape pr shape) q')
      (sidePairs (decodePath T)) (decodeShapes T)).prod
  else omCount T q'

theorem C4_of_headOrd_ne {T : ClusterShape} (h : headOrd T ≠ 1) (q' : ℕ) :
    C4 T q' = omCount T q' := by
  rw [C4, if_neg h]

/-- `IsRationalFn` is closed under `zipWith`-products (the list-product closure the product
coefficient needs). -/
theorem isRationalFn_zipWith_prod {α β : Type*} (l : List α) (l' : List β)
    (g : α → β → ℕ → ℚ) (h : ∀ a b, IsRationalFn (g a b)) :
    IsRationalFn (fun q => (List.zipWith (fun a b => g a b q) l l').prod) := by
  induction l generalizing l' with
  | nil => simpa using isRationalFn_const 1
  | cons a l ih =>
      cases l' with
      | nil => simpa using isRationalFn_const 1
      | cons b l' =>
          simp only [List.zipWith_cons_cons, List.prod_cons]
          exact isRationalFn_mul (h a b) (ih l')

/-- **`C4` is a uniform rational function of `q`** on every shape (product closure on the
multi-slope leg, the banked `omCount_isRational` on the old legs). -/
theorem C4_isRational (T : ClusterShape) : IsRationalFn (fun q' => C4 T q') := by
  by_cases h : headOrd T = 1
  · simp only [C4, if_pos h]
    exact isRationalFn_zipWith_prod _ _ _ (fun pr shape => omCount_isRational _)
  · simp only [C4, if_neg h]
    exact omCount_isRational T

/-- **The tendsto bridge on the mixed leg** (blueprint §2-W4a item 5): at `p = M9.realP`, the
normalized Wave-4 stratum count of the canonical mixed literal converges (as the level
`N → ∞`) to its Wave-4 product coefficient — `hnode_multiSideProduct` fired with the canonical
admissibility bank. -/
theorem stratum_tendsto_C4_mixed {n : ℕ} {σ : FactorizationType} (h : mixedOK n σ) :
    Filter.Tendsto
      (fun N => stratumCount4 n (multiSideLit n (mixedPath σ) (mixedSh σ)) N
        / (M9.realP : ℚ) ^ (n * N))
      Filter.atTop
      (nhds (C4 (multiSideLit n (mixedPath σ) (mixedSh σ)) M9.realP)) := by
  have hdecP := decodePath_multiSideLit n (mixedPath σ) (mixedSh σ)
  have hdecS := decodeShapes_multiSideLit (n := n) (mixedSh_length_eq σ) (allMuOne_mixedSh σ)
  have hsc : ∀ N, stratumCount4 n (multiSideLit n (mixedPath σ) (mixedSh σ)) N
      = ((StratumOrder1.stratumCount1 M9.realP n N (mkCell n (mixedPath σ) (mixedSh σ)) : ℕ) : ℚ) := by
    intro N
    rw [stratumCount4, if_pos (headOrd_multiSideLit n (mixedPath σ) (mixedSh σ)), hdecP, hdecS]
  have hC : C4 (multiSideLit n (mixedPath σ) (mixedSh σ)) M9.realP
      = (List.zipWith (fun pr shape => omCount (sideSubShape pr shape) M9.realP)
          (sidePairs (mixedPath σ)) (mixedSh σ)).prod := by
    rw [C4, if_pos (headOrd_multiSideLit n (mixedPath σ) (mixedSh σ)), hdecP, hdecS]
  rw [hC]
  have hbase := PathShapeMultiSideTree.hnode_multiSideProduct n (WildMenu.fSum σ + 1)
    (Nat.succ_pos _) (mixedPath σ) (menuPath_mixedPath h) (mixedSh σ) (shapesFor_mixedPath h)
    (allMuOne_mixedSh σ) (allNonempty_mixedSh σ) M9.realP
  refine Filter.Tendsto.congr (fun N => ?_) hbase
  rw [hsc N]

/-! ## 6. Disjointness and the box bound (the keystone bank)

Both fiber notions live on the SAME box `QuotientBox.monicBox M9.realP N n` (blueprint §2-W4a
item 4 NOTE): the mixed literals count `classify1`-fibers of their decoded `NodeConfig` cells,
the old shapes count `B.classify`-fibers of the `ClusterShape` itself. The disjointness
statements are therefore between SUBSETS of the box. -/

/-- The Wave-4 counting fiber of a menu entry, as a subset of the box. -/
def Fiber4 (n N : ℕ) (T : ClusterShape) (f : QuotientBox.monicBox M9.realP N n) : Prop :=
  if headOrd T = 1 then
    classify1 M9.realP f = some (mkCell n (decodePath T) (decodeShapes T))
  else M9.realClassify n N f = T

/-- `stratumCount4` IS the fiber card (both legs are `Nat.card`s of box subsets). -/
theorem stratumCount4_eq_card (n N : ℕ) (T : ClusterShape) :
    stratumCount4 n T N
      = ((Nat.card {f : QuotientBox.monicBox M9.realP N n // Fiber4 n N T f} : ℕ) : ℚ) := by
  by_cases h : headOrd T = 1
  · rw [stratumCount4, if_pos h]
    congr 1
    refine Nat.card_congr (Equiv.subtypeEquivRight fun f => ?_)
    simp only [Fiber4, if_pos h]
  · rw [stratumCount4, if_neg h]
    show ((M9.rawCount n T N : ℕ) : ℚ) = _
    congr 1
    refine Nat.card_congr (Equiv.subtypeEquivRight fun f => ?_)
    simp only [Fiber4, if_neg h]

theorem stratumCount4_nonneg (n : ℕ) (T : ClusterShape) (N : ℕ) :
    0 ≤ stratumCount4 n T N := by
  rw [stratumCount4_eq_card]
  exact Nat.cast_nonneg _

/-- Any `InCell` membership forces a READABLE, POSITIVE constant-coefficient valuation
(`1 ≤ v(a₀) ≤ N − 1`) — the vertex exactness at the left endpoint `(0, H)` of the menu path. -/
theorem inCell_v0 {p : ℕ} [Fact p.Prime] {N n : ℕ} {f : QuotientBox.monicBox p N n}
    {c : NodeConfig} (h : InCell p f c) : 1 ≤ vOf p f 0 ∧ vOf p f 0 ≤ N - 1 := by
  obtain ⟨P, sh, hP, -, -, hm⟩ := h
  obtain ⟨H, p1, T, rfl, hH1, hH2, -, -, -⟩ := hP
  have h0 := hm.1 ((0 : ℕ), H) List.mem_cons_self
  simp only at h0
  omega

/-- **Disjointness leg (i)** — mixed (indeed ANY) `InCell` fiber vs the order-0 separable
`B.classify` fiber: the sepShape fiber forces a UNIT `a₀` (`v(a₀) = 0`), the `InCell` hull
forces `v(a₀) ≥ 1`. -/
theorem inCell_sep_disjoint {n N : ℕ} (hn : 0 < n) (hN : 0 < N)
    {f : QuotientBox.monicBox M9.realP N n} {c : NodeConfig} {lam : Nat.Partition n}
    (h1 : InCell M9.realP f c)
    (h2 : B.classify M9.realP n N f = Order0.sepShape n lam) : False := by
  obtain ⟨hunit, -, -⟩ := Order0.classify_eq_sepShape_only_if M9.realP n N hN hn lam f h2
  have hv := (inCell_v0 h1).1
  have hv0 : vOf M9.realP f 0 = 0 := hunit
  omega

/-- The `Tselfloop` classify fiber pins the left Newton vertex as a support dot:
`v(a₀) = H < N` (the H-generic support-dot argument, mirrored off
`WildMenuW3.stratumCount_ramShapeAt_smallN`). -/
theorem classify_Tselfloop_v0 {n N H : ℕ} (hn : 0 < n) (hN : 0 < N)
    {f : QuotientBox.monicBox M9.realP N n} {shape : List (ℕ × ℕ)} (hne : shape ≠ [])
    (hcl : B.classify M9.realP n N f = ClassifierBridgeFiber.Tselfloop n
      (((0, H), (n, 0)) : (ℕ × ℕ) × (ℕ × ℕ)) shape) :
    vOf M9.realP f 0 = H ∧ vOf M9.realP f 0 < N := by
  have hrs := ClassifierBridgeFiber2.rootSide_eq_of_classify hn hN f shape hcl hne
  have hverts := ClassifierBridgeFiber.npVertices_of_rootSide M9.realP hn hN f hrs
  have hmem0 : (((0 : ℕ), H) : ℕ × ℕ)
      ∈ NewtonPolygon.npVertices (B.boxValSupport M9.realP N f)
          (B.boxValSupport_nonempty M9.realP N hN f) := by
    rw [hverts]
    exact List.mem_cons_self
  have hS := ClassifierBridgeFiber.mem_S_of_mem_npVertices M9.realP f
    (B.boxValSupport_nonempty M9.realP N hN f) hmem0
  obtain ⟨hv, hne0⟩ := ClassifierBridgeFiber.boxValSupport_eq_dot M9.realP f hS
  have hlt : PadicLift.zmodValuation M9.realP N ((f.1).coeff 0) < N :=
    PadicLift.zmodValuation_lt M9.realP hN hne0
  have hv' : H = PadicLift.zmodValuation M9.realP N ((f.1).coeff 0) := hv
  constructor
  · show PadicLift.zmodValuation M9.realP N ((f.1).coeff 0) = H
    omega
  · show PadicLift.zmodValuation M9.realP N ((f.1).coeff 0) < N
    omega

/-- The faces of a menu cell are one per (side, shape) pair. -/
theorem faces_length_mkCell (s : ℕ) (P : List (ℕ × ℕ)) (sh : List (List (ℕ × ℕ))) :
    (mkCell s P sh).faces.length = min (sidePairs P).length sh.length := by
  simp [mkCell, List.length_zipWith]

/-- **Disjointness leg (ii)** — the mixed `InCell` fiber vs a full-width `Tselfloop`
`B.classify` fiber. Two pinned polygons on the same `f` are impossible: for `N` above the
leg's threshold the leg fiber IS a single-side `InCell` (`classify_eq_selfloop_iff`) and
`inCell_unique` forces the ≥2-side mixed cell to EQUAL the 1-side leg cell (faces-length
contradiction); below the threshold the leg fiber pins `v(a₀) = H_leg ≥ N`, unreadable inside
any `InCell` (which forces `v(a₀) ≤ N − 1`). -/
theorem inCell_mixed_selfloop_disjoint {n N : ℕ} {σ σ' : FactorizationType} {k : ℕ}
    (hσ : mixedOK n σ) (hc' : WildMenu.constERam n σ') (hk1 : 1 ≤ k)
    (hk : Nat.gcd k (n / WildMenu.fSum σ') = 1)
    {f : QuotientBox.monicBox M9.realP N n}
    (h1 : InCell M9.realP f (mkCell n (mixedPath σ) (mixedSh σ)))
    (h2 : B.classify M9.realP n N f = WildMenuW3.ramShapeAt n σ' k) : False := by
  have hn : 0 < n := mixedOK_n_pos hσ
  have hN : 0 < N := by
    rcases Nat.eq_zero_or_pos N with rfl | hpos
    · obtain ⟨ha, hb⟩ := inCell_v0 h1
      omega
    · exact hpos
  have h2' : B.classify M9.realP n N f = ClassifierBridgeFiber.Tselfloop n
      (((0, WildMenu.fSum σ' * k), (n, 0)) : (ℕ × ℕ) × (ℕ × ℕ)) (WildMenu.wShape σ') := h2
  rcases Nat.lt_or_ge N (WildMenu.fSum σ' * k + 1) with hsmall | hbig
  · -- below the leg threshold: v(a₀) = F·k ≥ N vs readability
    obtain ⟨hv0, hlt⟩ := classify_Tselfloop_v0 hn hN (WildMenu.wShape_ne hc') h2'
    obtain ⟨ha, hb⟩ := inCell_v0 h1
    omega
  · -- above the threshold: the leg fiber is the single-side InCell; polygons collide
    have hPleg : MenuPath n N (WildMenuW3.wPathAt n σ' k) :=
      WildMenuW3.menuPath_wPathAt_of_le hc' hk1 hbig
    have hleg : InCell M9.realP f
        (mkCell n (WildMenuW3.wPathAt n σ' k) [WildMenu.wShape σ']) := by
      rw [← ClassifierBridgeFiber2.classify_eq_selfloop_iff n N hN hn
        (WildMenuW3.wPathAt n σ' k) hPleg
        (((0, WildMenu.fSum σ' * k), (n, 0)) : (ℕ × ℕ) × (ℕ × ℕ))
        (WildMenuW3.sidePairs_wPathAt n σ' k) (WildMenu.wShape σ')
        (WildMenuW3.shapesFor_wPathAt hc' hk) (WildMenu.wShape_mu σ')
        (WildMenu.wShape_ne hc') f]
      exact h2'
    have hcell := inCell_unique M9.realP h1 hleg
    have hlen := congrArg (fun c : NodeConfig => c.faces.length) hcell
    simp only [faces_length_mkCell] at hlen
    have hms : (mixedSh σ).length = (eVals σ).length := by rw [mixedSh, List.length_map]
    have hleg1 : (sidePairs (WildMenuW3.wPathAt n σ' k)).length = 1 := rfl
    rw [sidePairs_mixedPath_length, hms, hleg1, Nat.min_self] at hlen
    simp only [List.length_cons, List.length_nil, Nat.min_self] at hlen
    have h2le := two_le_eVals_length hσ
    omega

/-- **Disjointness leg (iii)** — canonical mixed cells of distinct σ are distinct (the pinned
polygon or the pinned residual differs): cell equality is injective back to σ through
`mkCell_injective` (at a common level) + `typeOf4` recovery. -/
theorem mixedCell_injective {n : ℕ} {σ σ' : FactorizationType}
    (hσ : mixedOK n σ) (hσ' : mixedOK n σ')
    (heq : mkCell n (mixedPath σ) (mixedSh σ) = mkCell n (mixedPath σ') (mixedSh σ')) :
    σ = σ' := by
  set N₀ := max (WildMenu.fSum σ) (WildMenu.fSum σ') + 1 with hN₀
  have hP : MenuPath n N₀ (mixedPath σ) :=
    menuPath_mixedPath_of_le hσ (Nat.succ_le_succ (Nat.le_max_left _ _))
  have hP' : MenuPath n N₀ (mixedPath σ') :=
    menuPath_mixedPath_of_le hσ' (Nat.succ_le_succ (Nat.le_max_right _ _))
  obtain ⟨hPP, hss⟩ := mkCell_injective hP hP' (shapesFor_mixedPath hσ)
    (shapesFor_mixedPath hσ') heq
  have h1 := typeOf4_multiSideLit hσ
  rw [hPP, hss] at h1
  have h2 := typeOf4_multiSideLit hσ'
  rw [h1] at h2
  exact Option.some.inj h2

/-! ### The finite mixed type menu -/

theorem multiset_card_le_sum (m : Multiset ℕ) (h : ∀ x ∈ m, 1 ≤ x) :
    Multiset.card m ≤ m.sum := by
  induction m using Multiset.induction_on with
  | empty => simp
  | @cons a t ih =>
      rw [Multiset.card_cons, Multiset.sum_cons]
      have h1 := h a (Multiset.mem_cons_self a t)
      have h2 := ih (fun x hxm => h x (Multiset.mem_cons_of_mem hxm))
      omega

theorem mixedOK_card_le {n : ℕ} {σ : FactorizationType} (h : mixedOK n σ) :
    Multiset.card σ.data ≤ n := by
  obtain ⟨-, hall, hdeg, -⟩ := h
  have hpos : ∀ x ∈ σ.data.map (fun pr : ℕ × ℕ => pr.1 * pr.2), 1 ≤ x := by
    intro x hx
    rw [Multiset.mem_map] at hx
    obtain ⟨pr, hpr, rfl⟩ := hx
    have h1 := (hall pr hpr).1
    have h2 := (hall pr hpr).2
    exact Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
  have hsum := multiset_card_le_sum _ hpos
  rw [Multiset.card_map] at hsum
  have hdeg' : (σ.data.map (fun pr : ℕ × ℕ => pr.1 * pr.2)).sum = n := hdeg
  omega

theorem mixedOK_bounds {n : ℕ} {σ : FactorizationType} (h : mixedOK n σ) :
    ∀ pr ∈ σ.data, 1 ≤ pr.1 ∧ pr.1 ≤ n ∧ 1 ≤ pr.2 ∧ pr.2 ≤ n := by
  intro pr hpr
  obtain ⟨-, hall, hdeg, -⟩ := h
  have h1 := (hall pr hpr).1
  have h2 := (hall pr hpr).2
  have hle : pr.1 * pr.2 ≤ n := by
    rw [← hdeg]
    exact Multiset.single_le_sum (fun x _ => Nat.zero_le x) _
      (Multiset.mem_map_of_mem _ hpr)
  have hb1 : pr.1 ≤ pr.1 * pr.2 := Nat.le_mul_of_pos_right _ (by omega)
  have hb2 : pr.2 ≤ pr.1 * pr.2 := Nat.le_mul_of_pos_left _ (by omega)
  omega

/-- **The finite mixed type menu** (blueprint §2-W4a item 4): all mixed-e degree-`n` types,
carved out of the sub-multisets of the master multiset `n • ([1,n] × [1,n])`. -/
noncomputable def mixedTypes (n : ℕ) : Finset FactorizationType :=
  (((n • ((Finset.Icc 1 n ×ˢ Finset.Icc 1 n).val)).powerset.toFinset).filter
    (fun m => mixedOK n ⟨m⟩)).image (fun m => (⟨m⟩ : FactorizationType))

/-- Membership in `mixedTypes` is EXACTLY the `mixedOK` predicate. -/
theorem mem_mixedTypes {n : ℕ} {σ : FactorizationType} :
    σ ∈ mixedTypes n ↔ mixedOK n σ := by
  constructor
  · intro h
    simp only [mixedTypes, Finset.mem_image, Finset.mem_filter, Multiset.mem_toFinset] at h
    obtain ⟨m, ⟨-, hOK⟩, heq⟩ := h
    rw [← heq]
    exact hOK
  · intro h
    simp only [mixedTypes, Finset.mem_image, Finset.mem_filter, Multiset.mem_toFinset]
    refine ⟨σ.data, ⟨?_, h⟩, rfl⟩
    rw [Multiset.mem_powerset, Multiset.le_iff_count]
    intro a
    by_cases hmem : a ∈ σ.data
    · have hcard := mixedOK_card_le h
      have hcount : σ.data.count a ≤ n :=
        le_trans (Multiset.count_le_card a _) hcard
      obtain ⟨hb1, hb2, hb3, hb4⟩ := mixedOK_bounds h a hmem
      have hamem : a ∈ (Finset.Icc 1 n ×ˢ Finset.Icc 1 n).val := by
        rw [Finset.mem_val, Finset.mem_product, Finset.mem_Icc, Finset.mem_Icc]
        exact ⟨⟨hb1, hb2⟩, hb3, hb4⟩
      have h1 : ((Finset.Icc 1 n ×ˢ Finset.Icc 1 n).val).count a = 1 :=
        Multiset.count_eq_one_of_mem (Finset.Icc 1 n ×ˢ Finset.Icc 1 n).nodup hamem
      rw [Multiset.count_nsmul, h1]
      omega
    · rw [Multiset.count_eq_zero_of_notMem hmem]
      exact Nat.zero_le _

/-- **The Wave-4 type menu**: the Wave-1/3 type menu extended by the mixed types. -/
noncomputable def typeMenu4 (n : ℕ) : Finset FactorizationType :=
  WildMenuPrep.typeMenuW n ∪ mixedTypes n

/-! ### The box bound -/

/-- Pairwise-disjoint subsets of a finite type have summable cards (the two-classifier
generalization of `WildMenuPrep.sum_card_fibers_le_finset` — the subsets need not be the
fibers of a single function). -/
theorem sum_card_disjoint_le {α : Type*} [Finite α] {ι : Type*} (s : Finset ι)
    (F : ι → α → Prop)
    (hdisj : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → ∀ a, F i a → F j a → False) :
    (∑ i ∈ s, Nat.card {a : α // F i a}) ≤ Nat.card α := by
  classical
  cases nonempty_fintype α
  calc ∑ i ∈ s, Nat.card {a : α // F i a}
      = ∑ i ∈ s, (Finset.univ.filter (fun a : α => F i a)).card :=
        Finset.sum_congr rfl fun i _ => by
          rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    _ = (s.biUnion (fun i => Finset.univ.filter (fun a : α => F i a))).card := by
        refine (Finset.card_biUnion ?_).symm
        intro i hi j hj hij
        refine Finset.disjoint_left.mpr fun a ha ha' => ?_
        exact hdisj i hi j hj hij a (Finset.mem_filter.mp ha).2 (Finset.mem_filter.mp ha').2
    _ ≤ Fintype.card α := Finset.card_le_univ _
    _ = Nat.card α := (Nat.card_eq_fintype_card).symm

/-- Splitting of the Wave-3 menu members into the two order-0-headed families. -/
theorem mem_omMenuW3_cases {n K : ℕ} {σ : FactorizationType} {T : ClusterShape}
    (hT : T ∈ WildMenuW3.omMenuW3 n K σ) :
    (∃ lam : Nat.Partition n, T = Order0.sepShape n lam)
      ∨ (WildMenu.constERam n σ ∧ ∃ k, 1 ≤ k ∧ Nat.gcd k (n / WildMenu.fSum σ) = 1
          ∧ T = WildMenuW3.ramShapeAt n σ k) := by
  rw [WildMenuW3.omMenuW3, Finset.mem_union] at hT
  rcases hT with h | h
  · simp only [Order0.sepShapesOf, Finset.mem_image, Finset.mem_filter, Finset.mem_univ,
      true_and] at h
    obtain ⟨lam, -, rfl⟩ := h
    exact Or.inl ⟨lam, rfl⟩
  · rw [WildMenuW3.mem_ramShapes3] at h
    obtain ⟨hc, k, hk, rfl⟩ := h
    obtain ⟨⟨hk1, -⟩, hke⟩ := WildMenuW3.mem_admissibleK.mp hk
    exact Or.inr ⟨hc, k, hk1, hke, rfl⟩

/-- The mixed classify1-fiber never meets an old `B.classify` fiber (legs (i) + (ii)
assembled). -/
theorem fiber4_mixed_old_disjoint {n K N : ℕ} (hn : 0 < n) (hN : 0 < N)
    {σ σ' : FactorizationType} {T : ClusterShape} (hσ : mixedOK n σ)
    (hT : T ∈ WildMenuW3.omMenuW3 n K σ')
    {f : QuotientBox.monicBox M9.realP N n}
    (hcl1 : classify1 M9.realP f = some (mkCell n (mixedPath σ) (mixedSh σ)))
    (hcl2 : M9.realClassify n N f = T) : False := by
  have hIn : InCell M9.realP f (mkCell n (mixedPath σ) (mixedSh σ)) :=
    (classify1_eq_some_iff M9.realP).mp hcl1
  rcases mem_omMenuW3_cases hT with ⟨lam, rfl⟩ | ⟨hc', k, hk1, hke, rfl⟩
  · exact inCell_sep_disjoint hn hN hIn hcl2
  · exact inCell_mixed_selfloop_disjoint hσ hc' hk1 hke hIn hcl2

/-- **The keystone pairwise disjointness** of the Wave-4 counting fibers across the whole
menu family (blueprint §2-W4a item 4 (i)–(iii) assembled). -/
theorem fiber4_disjoint {n K N : ℕ} (hn : 0 < n) (hN : 0 < N)
    {σ σ' : FactorizationType} {T T' : ClusterShape}
    (hσT : T ∈ omMenu4 n K σ) (hσT' : T' ∈ omMenu4 n K σ') (hTT : T ≠ T')
    (f : QuotientBox.monicBox M9.realP N n)
    (h1 : Fiber4 n N T f) (h2 : Fiber4 n N T' f) : False := by
  rcases mem_omMenu4_cases hσT with hold | ⟨hOK, rfl⟩
  · rcases mem_omMenu4_cases hσT' with hold' | ⟨hOK', rfl⟩
    · -- both old: two values of the same classifier
      rw [Fiber4, if_neg (by rw [headOrd_of_mem_omMenuW3 hold]; exact zero_ne_one)] at h1
      rw [Fiber4, if_neg (by rw [headOrd_of_mem_omMenuW3 hold']; exact zero_ne_one)] at h2
      exact hTT (h1.symm.trans h2)
    · -- T old, T' the mixed literal
      rw [Fiber4, if_neg (by rw [headOrd_of_mem_omMenuW3 hold]; exact zero_ne_one)] at h1
      rw [Fiber4, if_pos (headOrd_multiSideLit n (mixedPath σ') (mixedSh σ')),
        decodePath_multiSideLit,
        decodeShapes_multiSideLit (mixedSh_length_eq σ') (allMuOne_mixedSh σ')] at h2
      exact fiber4_mixed_old_disjoint hn hN hOK' hold h2 h1
  · rcases mem_omMenu4_cases hσT' with hold' | ⟨hOK', rfl⟩
    · -- T the mixed literal, T' old (mirror)
      rw [Fiber4, if_pos (headOrd_multiSideLit n (mixedPath σ) (mixedSh σ)),
        decodePath_multiSideLit,
        decodeShapes_multiSideLit (mixedSh_length_eq σ) (allMuOne_mixedSh σ)] at h1
      rw [Fiber4, if_neg (by rw [headOrd_of_mem_omMenuW3 hold']; exact zero_ne_one)] at h2
      exact fiber4_mixed_old_disjoint hn hN hOK hold' h1 h2
    · -- both mixed: one classifier value, cells injective back to σ
      rw [Fiber4, if_pos (headOrd_multiSideLit n (mixedPath σ) (mixedSh σ)),
        decodePath_multiSideLit,
        decodeShapes_multiSideLit (mixedSh_length_eq σ) (allMuOne_mixedSh σ)] at h1
      rw [Fiber4, if_pos (headOrd_multiSideLit n (mixedPath σ') (mixedSh σ')),
        decodePath_multiSideLit,
        decodeShapes_multiSideLit (mixedSh_length_eq σ') (allMuOne_mixedSh σ')] at h2
      have hcc : mkCell n (mixedPath σ) (mixedSh σ) = mkCell n (mixedPath σ') (mixedSh σ') :=
        Option.some.inj (h1.symm.trans h2)
      have hσσ : σ = σ' := mixedCell_injective hOK hOK' hcc
      subst hσσ
      exact hTT rfl

/-- The union re-indexing over the Wave-4 type menu (distinct σ have disjoint menus). -/
theorem sum_omMenu4_eq_biUnion (n K : ℕ) {M : Type*} [AddCommMonoid M]
    (g : ClusterShape → M) :
    ∑ σ ∈ typeMenu4 n, ∑ T ∈ omMenu4 n K σ, g T
      = ∑ T ∈ (typeMenu4 n).biUnion (fun σ => omMenu4 n K σ), g T := by
  refine (Finset.sum_biUnion ?_).symm
  intro σ _hσ σ' _hσ' hne
  exact Finset.disjoint_left.mpr fun T hT hT' => hne (eq_of_mem_omMenu4 hT hT')

/-- **The Wave-4 box bound** (blueprint §2-W4a item 4, the `undecidedCount ≥ 0` feed): at every
level `N ≥ 1` the total Wave-4 decided count over the enlarged type menu is at most the box
count `realP^(nN)` — the fibers are pairwise-disjoint box subsets (`fiber4_disjoint`). -/
theorem sum_stratumCount4_le_box (n K N : ℕ) (hn : 0 < n) (hN : 0 < N) :
    (∑ σ ∈ typeMenu4 n, ∑ T ∈ omMenu4 n K σ, stratumCount4 n T N)
      ≤ (M9.realP : ℚ) ^ (n * N) := by
  rw [sum_omMenu4_eq_biUnion]
  set S := (typeMenu4 n).biUnion (fun σ => omMenu4 n K σ) with hS
  haveI hfin : Finite (QuotientBox.monicBox M9.realP N n) := by
    have hpos : 0 < Nat.card (QuotientBox.monicBox M9.realP N n) := by
      rw [QuotientBox.card_monicBox M9.realP N n hN]
      exact pow_pos (pow_pos (by norm_num [M9.realP]) N) n
    exact (Nat.card_pos_iff.mp hpos).2
  have hdisj : ∀ T ∈ S, ∀ T' ∈ S, T ≠ T' →
      ∀ f : QuotientBox.monicBox M9.realP N n, Fiber4 n N T f → Fiber4 n N T' f → False := by
    intro T hT T' hT' hne f h1 h2
    rw [hS, Finset.mem_biUnion] at hT hT'
    obtain ⟨σ, -, hT⟩ := hT
    obtain ⟨σ', -, hT'⟩ := hT'
    exact fiber4_disjoint hn hN hT hT' hne f h1 h2
  have key : (∑ T ∈ S, Nat.card {f : QuotientBox.monicBox M9.realP N n // Fiber4 n N T f})
      ≤ M9.realP ^ (n * N) := by
    have hle := sum_card_disjoint_le S (Fiber4 n N) hdisj
    rw [QuotientBox.card_monicBox M9.realP N n hN] at hle
    calc (∑ T ∈ S, Nat.card {f : QuotientBox.monicBox M9.realP N n // Fiber4 n N T f})
        ≤ (M9.realP ^ N) ^ n := hle
      _ = M9.realP ^ (n * N) := by rw [← pow_mul, Nat.mul_comm]
  calc (∑ T ∈ S, stratumCount4 n T N)
      = ((∑ T ∈ S, Nat.card {f : QuotientBox.monicBox M9.realP N n // Fiber4 n N T f} : ℕ) : ℚ) := by
        rw [Nat.cast_sum]
        exact Finset.sum_congr rfl fun T _ => stratumCount4_eq_card n N T
    _ ≤ ((M9.realP ^ (n * N) : ℕ) : ℚ) := by exact_mod_cast key
    _ = (M9.realP : ℚ) ^ (n * N) := by push_cast; ring

/-! ### Small-N vanishing, level constancy, monotonicity (the counting-model feeds) -/

theorem ceilAt_head_zero (H : ℕ) (rest : List (ℕ × ℕ)) :
    ceilAt (((0 : ℕ), H) :: rest) 0 = H := by
  cases rest with
  | nil => rfl
  | cons q1 T => simp [ceilAt]

/-- **Small-N vanishing of the mixed leg**: below the threshold `N₀ = H_total + 1` the mixed
fiber is EMPTY — any `InCell` witness pins the column-0 hull height `H_total` (via the shared
polygon), but a level-`N` menu path only admits heights `≤ N − 1`. -/
theorem stratumCount4_mixed_smallN {n N : ℕ} {σ : FactorizationType} (hσ : mixedOK n σ)
    (hN : N ≤ WildMenu.fSum σ) :
    stratumCount4 n (multiSideLit n (mixedPath σ) (mixedSh σ)) N = 0 := by
  have hn : 0 < n := mixedOK_n_pos hσ
  rw [stratumCount4, if_pos (headOrd_multiSideLit n (mixedPath σ) (mixedSh σ)),
    decodePath_multiSideLit,
    decodeShapes_multiSideLit (mixedSh_length_eq σ) (allMuOne_mixedSh σ)]
  haveI : IsEmpty {f : QuotientBox.monicBox M9.realP N n //
      classify1 M9.realP f = some (mkCell n (mixedPath σ) (mixedSh σ))} := by
    constructor
    rintro ⟨f, hcl⟩
    have hIn := (classify1_eq_some_iff M9.realP).mp hcl
    obtain ⟨P', sh', hP', -, hceq, -⟩ := hIn
    obtain ⟨H', p1, T', hPeq, hH1, hH2, -, -, -⟩ := hP'
    have hpoly : mkPoly n (mixedPath σ) = mkPoly n P' :=
      congrArg OMCountV2.NodeConfig.polygon hceq
    have hh : polyHeight (mkPoly n (mixedPath σ)) 0 = polyHeight (mkPoly n P') 0 := by
      rw [hpoly]
    rw [polyHeight_mkPoly hn, polyHeight_mkPoly hn, hPeq, ceilAt_head_zero,
      show mixedPath σ = ((0 : ℕ), WildMenu.fSum σ)
        :: vertsFrom σ (eVals σ) 0 (WildMenu.fSum σ) from rfl, ceilAt_head_zero] at hh
    omega
  show ((Nat.card {f : QuotientBox.monicBox M9.realP N n //
      classify1 M9.realP f = some (mkCell n (mixedPath σ) (mixedSh σ))} : ℕ) : ℚ) = 0
  rw [Nat.card_of_isEmpty]
  norm_num

/-- The mixed-leg closed form at every level above the threshold (via
`stratumCount1_eq_closed`). -/
theorem stratumCount4_mixed_eq_closed {n N : ℕ} {σ : FactorizationType} (hσ : mixedOK n σ)
    (hN : WildMenu.fSum σ + 1 ≤ N) :
    stratumCount4 n (multiSideLit n (mixedPath σ) (mixedSh σ)) N
      = (CellCard.prodSC M9.realP (mixedSh σ) : ℚ)
          * (M9.realP : ℚ) ^ CellCard.freeExp n N (mixedPath σ) := by
  have hNpos : 0 < N := by omega
  rw [stratumCount4, if_pos (headOrd_multiSideLit n (mixedPath σ) (mixedSh σ)),
    decodePath_multiSideLit,
    decodeShapes_multiSideLit (mixedSh_length_eq σ) (allMuOne_mixedSh σ)]
  rw [StratumOrder1.stratumCount1_eq_closed M9.realP hNpos (menuPath_mixedPath_of_le hσ hN)
    (shapesFor_mixedPath hσ)]
  push_cast
  ring

/-- **Level constancy of the normalized mixed leg** above its threshold `N₀ = H_total + 1`
(the `freeExp` affinity cancels the box growth — mirror of the W3a staircase legs). -/
theorem normStratumCount4_mixed_levelConst {n N : ℕ} {σ : FactorizationType}
    (hσ : mixedOK n σ) (hN : WildMenu.fSum σ + 1 ≤ N) :
    stratumCount4 n (multiSideLit n (mixedPath σ) (mixedSh σ)) N / (M9.realP : ℚ) ^ (n * N)
      = stratumCount4 n (multiSideLit n (mixedPath σ) (mixedSh σ)) (WildMenu.fSum σ + 1)
          / (M9.realP : ℚ) ^ (n * (WildMenu.fSum σ + 1)) := by
  have hP₀ : MenuPath n (WildMenu.fSum σ + 1) (mixedPath σ) := menuPath_mixedPath hσ
  rw [stratumCount4_mixed_eq_closed hσ hN, stratumCount4_mixed_eq_closed hσ (le_refl _),
    DecidedOrder1.freeExp_eq_add_mul hP₀ hN]
  have hp0 : (M9.realP : ℚ) ≠ 0 := by norm_num [M9.realP]
  have hsplit : n * (WildMenu.fSum σ + 1) + n * (N - (WildMenu.fSum σ + 1)) = n * N := by
    rw [← Nat.mul_add]
    congr 1
    omega
  rw [pow_add, show (M9.realP : ℚ) ^ (n * N)
      = (M9.realP : ℚ) ^ (n * (WildMenu.fSum σ + 1))
          * (M9.realP : ℚ) ^ (n * (N - (WildMenu.fSum σ + 1))) from by
    rw [← pow_add, hsplit]]
  have hB : (M9.realP : ℚ) ^ (n * (N - (WildMenu.fSum σ + 1))) ≠ 0 := pow_ne_zero _ hp0
  field_simp

/-- **FULL monotonicity of the normalized Wave-4 menu sum** (the `decided_mono` discharge,
mirror of W3a): for mixed σ the menu is the single mixed staircase (`0, …, 0, c, c, …`); for
every other σ the menu and the counts are Wave 3's, whose monotonicity is banked. -/
theorem normSum_omMenu4_mono (n K : ℕ) (hn : 0 < n) (σ : FactorizationType) :
    Monotone (fun N => (∑ T ∈ omMenu4 n K σ, stratumCount4 n T N)
      / (M9.realP : ℚ) ^ (n * N)) := by
  by_cases hσ : mixedOK n σ
  · intro N₁ N₂ h₁₂
    simp only [omMenu4_of_mixed hσ, Finset.sum_singleton]
    rcases Nat.lt_or_ge (WildMenu.fSum σ) N₂ with hK | hK
    · rcases Nat.lt_or_ge (WildMenu.fSum σ) N₁ with hgt | hle
      · rw [normStratumCount4_mixed_levelConst (N := N₁) hσ (by omega),
          normStratumCount4_mixed_levelConst (N := N₂) hσ (by omega)]
      · rw [stratumCount4_mixed_smallN hσ hle, zero_div]
        exact div_nonneg (stratumCount4_nonneg n _ N₂)
          (le_of_lt (RealInstanceV2.realP_pow_pos _))
    · rw [stratumCount4_mixed_smallN hσ (h₁₂.trans hK),
        stratumCount4_mixed_smallN hσ hK, zero_div, zero_div]
  · have hsum : ∀ N, (∑ T ∈ omMenu4 n K σ, stratumCount4 n T N)
        = ∑ T ∈ WildMenuW3.omMenuW3 n K σ, M8.stratumCount (M9.rawCount n) T N := by
      intro N
      rw [omMenu4_eq_of_not_mixed hσ]
      exact Finset.sum_congr rfl fun T hT => stratumCount4_of_mem_omMenuW3 hT N
    intro N₁ N₂ h₁₂
    simp only [hsum]
    exact WildMenuW3.normSum_omMenuW3_mono n K hn σ h₁₂

/-! ## 7. AxCheck — every declaration of this wave is core-only -/

section AxCheck
#print axioms headOrd
#print axioms cellsAux
#print axioms multiSideLit
#print axioms headOrd_multiSideLit
#print axioms decodePath
#print axioms decodePath_multiSideLit
#print axioms decodeShapes
#print axioms decode_aux
#print axioms decodeShapes_multiSideLit
#print axioms multiSideLit_injective
#print axioms multiSideLit_ne_sepShape
#print axioms multiSideLit_ne_Tselfloop
#print axioms headOrd_of_mem_omMenuW3
#print axioms sideE
#print axioms typeListAux
#print axioms typeOf4
#print axioms typeOf4_typeOfW_compat
#print axioms typeOf4_of_mem_omMenuW3
#print axioms eVals
#print axioms Fof
#print axioms mixedOK
#print axioms mem_eVals
#print axioms eVals_pairwise
#print axioms eVals_ne_nil
#print axioms two_le_eVals_length
#print axioms eVals_two_le
#print axioms Fof_pos
#print axioms mixedOK_n_pos
#print axioms mixedOK_not_constERam
#print axioms sepShapesOf_empty_of_mixedOK
#print axioms sum_filter_fst
#print axioms sum_Fof
#print axioms sum_eFof
#print axioms shapeOf
#print axioms shapeOf_mem_shapesOfDegree
#print axioms vertsFrom
#print axioms mixedPath
#print axioms mixedSh
#print axioms chainOK_vertsFrom
#print axioms menuPath_mixedPath_of_le
#print axioms menuPath_mixedPath
#print axioms shapesFor_vertsFrom
#print axioms shapesFor_mixedPath
#print axioms allMuOne_mixedSh
#print axioms allNonempty_mixedSh
#print axioms sidePairs_mixedPath_length
#print axioms mixedSh_length_eq
#print axioms typeListAux_append_low
#print axioms sideE_canonical
#print axioms typeListAux_canonical
#print axioms coe_flatMap_eq_sum
#print axioms coe_group_map
#print axioms typeOf4_multiSideLit
#print axioms mixedShape
#print axioms mixedShape_of_mixedOK
#print axioms mixedShape_of_not_mixedOK
#print axioms omMenu4
#print axioms omMenu4_eq_of_not_mixed
#print axioms omMenu4_of_mixed
#print axioms mem_omMenu4_cases
#print axioms mem_omMenu4_type
#print axioms eq_of_mem_omMenu4
#print axioms stratumCount4
#print axioms stratumCount4_of_mem_omMenuW3
#print axioms C4
#print axioms C4_of_headOrd_ne
#print axioms isRationalFn_zipWith_prod
#print axioms C4_isRational
#print axioms stratum_tendsto_C4_mixed
#print axioms Fiber4
#print axioms stratumCount4_eq_card
#print axioms stratumCount4_nonneg
#print axioms inCell_v0
#print axioms inCell_sep_disjoint
#print axioms classify_Tselfloop_v0
#print axioms faces_length_mkCell
#print axioms inCell_mixed_selfloop_disjoint
#print axioms mixedCell_injective
#print axioms multiset_card_le_sum
#print axioms mixedOK_card_le
#print axioms mixedOK_bounds
#print axioms mixedTypes
#print axioms mem_mixedTypes
#print axioms typeMenu4
#print axioms sum_card_disjoint_le
#print axioms mem_omMenuW3_cases
#print axioms fiber4_mixed_old_disjoint
#print axioms fiber4_disjoint
#print axioms sum_omMenu4_eq_biUnion
#print axioms sum_stratumCount4_le_box
#print axioms ceilAt_head_zero
#print axioms stratumCount4_mixed_smallN
#print axioms stratumCount4_mixed_eq_closed
#print axioms normStratumCount4_mixed_levelConst
#print axioms normSum_omMenu4_mono
end AxCheck

end LeanUrat.OM.MultiSlopeMenu
