/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.OM.WildMenu
import LeanUrat.OM.WildMenuPrep

/-!
# WildMenuW3 — the H-window wild shape menu (Wave 3a,
`notes/WILD_WAVE3_BLUEPRINT_2026-07-21.md` §2 item 1)

**Scope (blueprint §1).** For a constant-e ramified type σ (`F := fSum σ`, `e = n/F`) the
admissible self-loop heights are exactly `H = F·k` with `gcd(k, e) = 1`
(`gcd(F·k, F·e) = F·gcd(k, e) = F = sideDeg`, so `ShapesFor` holds with the SAME residual shape
`wShape σ`). Wave 1 is the window `K = 1` (only `k = 1`); this module K-parameterizes the whole
Wave-1 menu bank. Window-K certifies the K-truncated decided density of each constant-e type —
a strictly larger leading sum than Wave 1, still NOT the full type density (the geometric tail
is the recursive self-loop wall); mixed-e and order ≥ 2 unchanged. No exhaustiveness claim.

Contents:
* `admissibleK e K` — the admissible multiplier window `{1 ≤ k ≤ K : gcd(k, e) = 1}`;
  `gcd_admissible` — the keystone arithmetic `gcd(F·k, n) = F`.
* `wPathAt n σ k` / `ramShapeAt n σ k` — the height-`F·k` self-loop menu path
  `[(0, F·k), (n, 0)]` and its `Tselfloop` literal (payload `wShape σ`, k-independent);
  the per-k admissibility bank (`MenuPath` at every `N ≥ F·k + 1`, `ShapesFor`, side degree)
  and the packaged `ramShapeAtWitness : SelfLoopWitness n (ramShapeAt n σ k)`.
* `ramShapes3 n K σ` / `omMenuW3 n K σ` — the windowed menus; **compatibility gate
  `omMenuW3_one : omMenuW3 n 1 σ = WildMenu.omMenuW n σ`** (Wave 1 is the K = 1 window).
* Distinctness/keying bank: `ramShapeAt_injective_k` (the discriminating projection is the head
  payload cell's polygon, whose column-0 ceiling reads back the height `F·k`;
  `ramShapeAt_height_eq`), `typeOfW_ramShapeAt` (the decoder is payload-face-blind: every k-leg
  keys to σ), `mem_omMenuW3_type`, `eq_of_mem_omMenuW3` (cross-σ disjointness, ANY two windows),
  `ramShapes3_disjoint_sepShapesOf`, `treeSize_of_mem_omMenuW3`.
* Prep bank (windowed): `sum_stratumCount_le_box_W3` (box bound over the unchanged type menu
  `WildMenuPrep.typeMenuW n` with the enlarged per-σ menus — disjoint classifier fibers, cross-σ
  via `eq_of_mem_omMenuW3`, within-σ via `ramShapeAt_injective_k`);
  `stratumCount_ramShapeAt_smallN` (per-leg vanishing for `N ≤ F·k`, support-dot valuation
  route); `normRamCountAt_levelConst` / `normRamCountAt_eventually_const` (per-leg constancy
  above the leg's own threshold `N₀ = F·k + 1`); `normRamCountAt_mono` (each leg is a
  0-then-constant staircase) and `normSum_omMenuW3_mono` (a finite sum of monotone staircases
  is monotone — the `decided_mono` discharge for the windowed counting model);
  `omCount_ramShapeAt_nonneg` (the `density_nonneg` feed, at every natural `q'`).

Leaf module: no existing file is modified. No axiom, no sorry.
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false

namespace LeanUrat.OM.WildMenuW3

open scoped Classical
open LeanUrat LeanUrat.OM Finset
open LeanUrat.OM.CellMenu

/-! ## 1. The admissible multiplier window and the keystone gcd -/

/-- **The admissible multiplier window**: `1 ≤ k ≤ K` with `gcd(k, e) = 1` (blueprint §1: for
constant-e σ these are exactly the multipliers whose height `H = F·k` carries type σ). -/
def admissibleK (e K : ℕ) : Finset ℕ :=
  (Finset.Icc 1 K).filter (fun k => Nat.gcd k e = 1)

theorem mem_admissibleK {e K k : ℕ} :
    k ∈ admissibleK e K ↔ (1 ≤ k ∧ k ≤ K) ∧ Nat.gcd k e = 1 := by
  rw [admissibleK, Finset.mem_filter, Finset.mem_Icc]

/-- Window `K = 1` is exactly `{1}` (Wave 1): `gcd(1, e) = 1` always. -/
theorem admissibleK_one (e : ℕ) : admissibleK e 1 = {1} := by
  ext k
  rw [mem_admissibleK, Finset.mem_singleton]
  constructor
  · rintro ⟨⟨h1, h2⟩, -⟩
    omega
  · rintro rfl
    exact ⟨⟨le_refl 1, le_refl 1⟩, Nat.gcd_one_left e⟩

/-- **The keystone arithmetic (blueprint §1)**: for constant-e σ and `gcd(k, e) = 1`
(`e = n / fSum σ`), the height `H = fSum σ · k` has `gcd(H, n) = fSum σ` — the side degree of
the k-leg is the SAME `F = fSum σ` as Wave 1's, so the SAME residual shape `wShape σ` is
admissible. Route: `n = F·e`, `gcd(F·k, F·e) = F·gcd(k, e) = F`. -/
theorem gcd_admissible {n : ℕ} {σ : FactorizationType} {k : ℕ}
    (h : WildMenu.constERam n σ) (hk : Nat.gcd k (n / WildMenu.fSum σ) = 1) :
    Nat.gcd (WildMenu.fSum σ * k) n = WildMenu.fSum σ := by
  obtain ⟨e, he2, hne, hall, hprod⟩ := h
  have hfpos : 0 < WildMenu.fSum σ :=
    WildMenu.constERam_fSum_pos ⟨e, he2, hne, hall, hprod⟩
  rw [WildMenu.constERam_e_eq he2 hprod hfpos] at hk
  rw [← hprod, Nat.mul_comm e (WildMenu.fSum σ), Nat.gcd_mul_left, hk, Nat.mul_one]

/-! ## 2. The k-leg path, shape literal, and admissibility bank -/

/-- **The height-`F·k` self-loop menu path**: `[(0, fSum σ · k), (n, 0)]` (Wave 1 is `k = 1`). -/
def wPathAt (n : ℕ) (σ : FactorizationType) (k : ℕ) : List (ℕ × ℕ) :=
  [(0, WildMenu.fSum σ * k), (n, 0)]

/-- **The k-th wild stratum shape of σ**: the `Tselfloop` literal on the height-`F·k` self-loop
side with the SAME canonical all-μ=1 residual shape `wShape σ` as Wave 1 (blueprint §1: all
window legs share the head tree `[(0, n, F)]` and differ only in the face payload side). -/
noncomputable def ramShapeAt (n : ℕ) (σ : FactorizationType) (k : ℕ) : ClusterShape :=
  ClassifierBridgeFiber.Tselfloop n
    (((0, WildMenu.fSum σ * k), (n, 0)) : (ℕ × ℕ) × (ℕ × ℕ)) (WildMenu.wShape σ)

theorem ramShapeAt_def (n : ℕ) (σ : FactorizationType) (k : ℕ) :
    ramShapeAt n σ k = ClassifierBridgeFiber.Tselfloop n
      (((0, WildMenu.fSum σ * k), (n, 0)) : (ℕ × ℕ) × (ℕ × ℕ)) (WildMenu.wShape σ) := rfl

/-- At `k = 1` the leg is EXACTLY Wave 1's canonical stratum literal (`fSum σ · 1 = fSum σ`). -/
theorem ramShapeAt_one (n : ℕ) (σ : FactorizationType) :
    ramShapeAt n σ 1 = ClassifierBridgeFiber.Tselfloop n
      (((0, WildMenu.fSum σ), (n, 0)) : (ℕ × ℕ) × (ℕ × ℕ)) (WildMenu.wShape σ) := by
  rw [ramShapeAt_def, Nat.mul_one]

/-- The single side of the k-leg path. -/
theorem sidePairs_wPathAt (n : ℕ) (σ : FactorizationType) (k : ℕ) :
    sidePairs (wPathAt n σ k)
      = [(((0, WildMenu.fSum σ * k), (n, 0)) : (ℕ × ℕ) × (ℕ × ℕ))] := rfl

/-- The side degree of the k-leg side is `gcd (F·k) n = fSum σ` (the keystone gcd). -/
theorem sideDeg_wPathAt {n : ℕ} {σ : FactorizationType} {k : ℕ}
    (h : WildMenu.constERam n σ) (hk : Nat.gcd k (n / WildMenu.fSum σ) = 1) :
    sideDeg (((0, WildMenu.fSum σ * k), (n, 0)) : (ℕ × ℕ) × (ℕ × ℕ)) = WildMenu.fSum σ := by
  change Nat.gcd (WildMenu.fSum σ * k - 0) (n - 0) = WildMenu.fSum σ
  rw [Nat.sub_zero, Nat.sub_zero]
  exact gcd_admissible h hk

/-- The k-leg path is a valid menu path at every level `N ≥ F·k + 1` (only `1 ≤ k` needed). -/
theorem menuPath_wPathAt_of_le {n N : ℕ} {σ : FactorizationType} {k : ℕ}
    (h : WildMenu.constERam n σ) (hk1 : 1 ≤ k) (hN : WildMenu.fSum σ * k + 1 ≤ N) :
    MenuPath n N (wPathAt n σ k) := by
  have hn : 0 < n := WildMenu.constERam_n_pos h
  have hf : 0 < WildMenu.fSum σ * k := Nat.mul_pos (WildMenu.constERam_fSum_pos h) hk1
  exact ⟨WildMenu.fSum σ * k, ((n : ℕ), (0 : ℕ)), [], rfl, hf, by omega, hn, hf,
    ChainOK.nil rfl rfl⟩

/-- The k-leg path at its own base level `N₀ = F·k + 1`. -/
theorem menuPath_wPathAt {n : ℕ} {σ : FactorizationType} {k : ℕ}
    (h : WildMenu.constERam n σ) (hk1 : 1 ≤ k) :
    MenuPath n (WildMenu.fSum σ * k + 1) (wPathAt n σ k) :=
  menuPath_wPathAt_of_le h hk1 (le_refl _)

/-- The SAME canonical shape assignment `[wShape σ]` is valid for EVERY admissible k-leg
(blueprint §1: the side degree is still `F`, so `wShape_mem_shapesOfDegree` applies verbatim). -/
theorem shapesFor_wPathAt {n : ℕ} {σ : FactorizationType} {k : ℕ}
    (h : WildMenu.constERam n σ) (hk : Nat.gcd k (n / WildMenu.fSum σ) = 1) :
    ShapesFor (wPathAt n σ k) [WildMenu.wShape σ] := by
  unfold ShapesFor
  rw [sidePairs_wPathAt]
  refine List.Forall₂.cons ?_ List.Forall₂.nil
  rw [sideDeg_wPathAt h hk]
  exact WildMenu.wShape_mem_shapesOfDegree h

/-- **The k-leg witness bundle** (blueprint §2 item 1): `H = F·k`, `N₀ = F·k + 1`,
`P = wPathAt n σ k`, `shape = wShape σ` — exactly the hypotheses of the banked counting legs,
for constant-e σ and any admissible multiplier (`1 ≤ k`, `gcd(k, e) = 1`; the window bound
`k ≤ K` is not needed by the legs). -/
noncomputable def ramShapeAtWitness {n : ℕ} {σ : FactorizationType} {k : ℕ}
    (h : WildMenu.constERam n σ) (hk1 : 1 ≤ k)
    (hk : Nat.gcd k (n / WildMenu.fSum σ) = 1) :
    WildMenu.SelfLoopWitness n (ramShapeAt n σ k) where
  H := WildMenu.fSum σ * k
  N₀ := WildMenu.fSum σ * k + 1
  P := wPathAt n σ k
  shape := WildMenu.wShape σ
  hN₀ := Nat.succ_pos _
  hHN₀ := rfl
  hn := WildMenu.constERam_n_pos h
  hP := menuPath_wPathAt h hk1
  hsingle := sidePairs_wPathAt n σ k
  hsh := shapesFor_wPathAt h hk
  hpos := WildMenu.wShape_pos h
  hμ := WildMenu.wShape_mu σ
  hne := WildMenu.wShape_ne h
  hT := rfl

/-! ## 3. The windowed menus and the compatibility gate -/

/-- **The windowed wild stratum menu**: one `Tselfloop` literal per admissible multiplier
`k ∈ admissibleK (n / fSum σ) K`; empty unless σ is constant-e ramified. -/
noncomputable def ramShapes3 (n K : ℕ) (σ : FactorizationType) : Finset ClusterShape :=
  if WildMenu.constERam n σ then
    (admissibleK (n / WildMenu.fSum σ) K).image (ramShapeAt n σ)
  else ∅

theorem ramShapes3_of_constERam {n K : ℕ} {σ : FactorizationType}
    (h : WildMenu.constERam n σ) :
    ramShapes3 n K σ = (admissibleK (n / WildMenu.fSum σ) K).image (ramShapeAt n σ) := by
  rw [ramShapes3, if_pos h]

theorem ramShapes3_of_not_constERam {n K : ℕ} {σ : FactorizationType}
    (h : ¬ WildMenu.constERam n σ) : ramShapes3 n K σ = ∅ := by
  rw [ramShapes3, if_neg h]

theorem mem_ramShapes3 {n K : ℕ} {σ : FactorizationType} {T : ClusterShape} :
    T ∈ ramShapes3 n K σ ↔ WildMenu.constERam n σ ∧
      ∃ k ∈ admissibleK (n / WildMenu.fSum σ) K, ramShapeAt n σ k = T := by
  constructor
  · intro h
    by_cases hc : WildMenu.constERam n σ
    · rw [ramShapes3_of_constERam hc, Finset.mem_image] at h
      exact ⟨hc, h⟩
    · rw [ramShapes3_of_not_constERam hc] at h
      simp at h
  · rintro ⟨hc, k, hk, rfl⟩
    rw [ramShapes3_of_constERam hc]
    exact Finset.mem_image_of_mem _ hk

/-- **The Wave-3 σ-keyed menu**: the order-0 separable menu extended by the windowed wild
strata. -/
noncomputable def omMenuW3 (n K : ℕ) (σ : FactorizationType) : Finset ClusterShape :=
  Order0.sepShapesOf n σ ∪ ramShapes3 n K σ

/-- For non-constant-e σ the windowed menu is the order-0 menu (every window). -/
theorem omMenuW3_unram {n K : ℕ} {σ : FactorizationType} (h : ¬ WildMenu.constERam n σ) :
    omMenuW3 n K σ = Order0.sepShapesOf n σ := by
  rw [omMenuW3, ramShapes3_of_not_constERam h, Finset.union_empty]

/-- For constant-e ramified σ the windowed menu is EXACTLY the admissible-k image (the order-0
separable menu is empty, as in Wave 1). -/
theorem omMenuW3_ram_of_constE {n K : ℕ} {σ : FactorizationType}
    (h : WildMenu.constERam n σ) :
    omMenuW3 n K σ = (admissibleK (n / WildMenu.fSum σ) K).image (ramShapeAt n σ) := by
  rw [omMenuW3, WildMenu.sepShapesOf_empty_of_constERam h, ramShapes3_of_constERam h,
    Finset.empty_union]

/-- **The compatibility gate (blueprint §2 item 1)**: the `K = 1` window IS Wave 1's menu. -/
theorem omMenuW3_one (n : ℕ) (σ : FactorizationType) :
    omMenuW3 n 1 σ = WildMenu.omMenuW n σ := by
  by_cases hc : WildMenu.constERam n σ
  · rw [omMenuW3_ram_of_constE hc, admissibleK_one, Finset.image_singleton, ramShapeAt_one,
      WildMenu.omMenuW_ram_of_constE hc]
  · rw [omMenuW3_unram hc, WildMenu.omMenuW_unram hc]

/-! ## 4. Distinctness and keying -/

/-- The head tree of every k-leg is `[(0, n, fSum σ)]` — k-independent AND payload-side
independent (the `Tselfloop` tree reads only the shape's residual-degree sum). -/
theorem tree_Tselfloop_wShape (n : ℕ) (σ : FactorizationType) (pr : (ℕ × ℕ) × (ℕ × ℕ)) :
    (ClassifierBridgeFiber.Tselfloop n pr (WildMenu.wShape σ)).tree
      = [((0 : ℕ), n, WildMenu.fSum σ)] := by
  change [((0 : ℕ), n, ((WildMenu.wShape σ).map Prod.fst).sum)] = _
  rw [WildMenu.wShape_fst_sum]

theorem tree_ramShapeAt (n : ℕ) (σ : FactorizationType) (k : ℕ) :
    (ramShapeAt n σ k).tree = [((0 : ℕ), n, WildMenu.fSum σ)] :=
  tree_Tselfloop_wShape n σ _

/-- **The discriminating projection**: equal k-legs have equal heights `F·k` — the head payload
cell's polygon is the side face of `((0, F·k), (n, 0))`, whose column-0 ceiling (`v₀`) reads
the height back (`toSideFace_v0_eq`). -/
theorem ramShapeAt_height_eq {n : ℕ} {σ : FactorizationType} (h : WildMenu.constERam n σ)
    {k k' : ℕ} (heq : ramShapeAt n σ k = ramShapeAt n σ k') :
    WildMenu.fSum σ * k = WildMenu.fSum σ * k' := by
  have hn : 0 < n := WildMenu.constERam_n_pos h
  obtain ⟨q, qs, hq⟩ := List.exists_cons_of_ne_nil (WildMenu.wShape_ne h)
  have hcells : (ramShapeAt n σ k).cells = (ramShapeAt n σ k').cells :=
    congrArg ClusterShape.cells heq
  rw [show (ramShapeAt n σ k).cells = (WildMenu.wShape σ).map (fun q => (⟨q.1, 1,
        M7.toSideFace (mkSide (((0, WildMenu.fSum σ * k), (n, 0)) : (ℕ × ℕ) × (ℕ × ℕ))), []⟩
          : ShapeCell)) from rfl,
      show (ramShapeAt n σ k').cells = (WildMenu.wShape σ).map (fun q => (⟨q.1, 1,
        M7.toSideFace (mkSide (((0, WildMenu.fSum σ * k'), (n, 0)) : (ℕ × ℕ) × (ℕ × ℕ))), []⟩
          : ShapeCell)) from rfl,
      hq, List.map_cons, List.map_cons] at hcells
  have hhead := List.head_eq_of_cons_eq hcells
  have hpoly : M7.toSideFace (mkSide (((0, WildMenu.fSum σ * k), (n, 0)) : (ℕ × ℕ) × (ℕ × ℕ)))
      = M7.toSideFace (mkSide (((0, WildMenu.fSum σ * k'), (n, 0)) : (ℕ × ℕ) × (ℕ × ℕ))) :=
    congrArg ShapeCell.polygon hhead
  have hw : 0 < (mkSide (((0, WildMenu.fSum σ * k), (n, 0)) : (ℕ × ℕ) × (ℕ × ℕ))).length := by
    change 0 < n - 0
    omega
  exact ClassifierBridgeFiber2.toSideFace_v0_eq hpoly hw

/-- **`ramShapeAt` is injective in k** (for constant-e σ): cancel `F > 0` in the height. -/
theorem ramShapeAt_injective_k {n : ℕ} {σ : FactorizationType} (h : WildMenu.constERam n σ)
    {k k' : ℕ} (heq : ramShapeAt n σ k = ramShapeAt n σ k') : k = k' :=
  Nat.eq_of_mul_eq_mul_left (WildMenu.constERam_fSum_pos h) (ramShapeAt_height_eq h heq)

/-- **The decoder is payload-face-blind**: `typeOfW` recovers σ on EVERY `Tselfloop` literal
carrying the canonical shape `wShape σ`, whatever the side `pr` (the head tree and the `dS`
payload do not see `pr`). Mirrors `WildMenu.typeOfW_ramShape` with `pr` generic. -/
theorem typeOfW_Tselfloop_wShape {n : ℕ} {σ : FactorizationType} (h : WildMenu.constERam n σ)
    (pr : (ℕ × ℕ) × (ℕ × ℕ)) :
    WildMenu.typeOfW n (ClassifierBridgeFiber.Tselfloop n pr (WildMenu.wShape σ)) = some σ := by
  obtain ⟨e, he2, hne, hall, hprod⟩ := h
  have hc' : WildMenu.constERam n σ := ⟨e, he2, hne, hall, hprod⟩
  have hfpos := WildMenu.constERam_fSum_pos hc'
  have hflt := WildMenu.constERam_fSum_lt hc'
  set T := ClassifierBridgeFiber.Tselfloop n pr (WildMenu.wShape σ) with hTdef
  have htree : T.tree = [((0 : ℕ), n, WildMenu.fSum σ)] := tree_Tselfloop_wShape n σ pr
  have hdr : WildMenu.headDr T = WildMenu.fSum σ := by rw [WildMenu.headDr, htree]; rfl
  -- the unramified branch does not fire (`fSum σ < n`)
  have hne1 : ¬ (T.tree = [((0 : ℕ), n, n)]) := by
    rw [htree]
    intro heq
    have hhead := List.head_eq_of_cons_eq heq
    have hval : WildMenu.fSum σ = n := by
      have := congrArg (fun t : ℕ × ℕ × ℕ => t.2.2) hhead
      simpa using this
    omega
  -- the payload `dS`-multiset is the `f`-parts multiset (pr-independent)
  have hcells : ((WildMenu.dSListOf T : List ℕ) : Multiset ℕ) = σ.data.map Prod.snd := by
    rw [hTdef]
    unfold WildMenu.dSListOf
    rw [show (ClassifierBridgeFiber.Tselfloop n pr (WildMenu.wShape σ)).cells
        = (WildMenu.wShape σ).map (fun q => (⟨q.1, 1,
            M7.toSideFace (mkSide pr), []⟩ : ShapeCell)) from rfl]
    rw [List.map_map]
    rw [show ((fun c : ShapeCell => c.dS) ∘ fun q : ℕ × ℕ => (⟨q.1, 1,
        M7.toSideFace (mkSide pr), []⟩ : ShapeCell)) = Prod.fst from rfl]
    rw [WildMenu.wShape, List.map_map]
    rw [show (Prod.fst ∘ fun f : ℕ => ((f, 1) : ℕ × ℕ)) = id from rfl]
    rw [List.map_id]
    exact Multiset.sort_eq _ _
  rw [WildMenu.typeOfW, if_neg hne1, if_pos ⟨by rw [htree, hdr], by omega, by omega⟩]
  rw [hdr, hcells, WildMenu.constERam_e_eq he2 hprod hfpos,
    WildMenu.data_eq_map_snd (fun pr' hpr' => (hall pr' hpr').1)]

/-- Every k-leg keys to σ through `typeOfW` (mirror of `WildMenu.typeOfW_ramShape`). -/
theorem typeOfW_ramShapeAt {n : ℕ} {σ : FactorizationType} (h : WildMenu.constERam n σ)
    (k : ℕ) : WildMenu.typeOfW n (ramShapeAt n σ k) = some σ :=
  typeOfW_Tselfloop_wShape h _

/-- **Cross-family disjointness**: a k-leg is never an order-0 separable menu shape — the head
trees differ (`dr = fSum σ < n` vs `dr = n`). -/
theorem ramShapeAt_not_mem_sepShapesOf {n : ℕ} {σ σ' : FactorizationType}
    (h : WildMenu.constERam n σ) (k : ℕ) : ramShapeAt n σ k ∉ Order0.sepShapesOf n σ' := by
  intro hmem
  simp only [Order0.sepShapesOf, Finset.mem_image, Finset.mem_filter, Finset.mem_univ,
    true_and] at hmem
  obtain ⟨lam, -, hT⟩ := hmem
  have h1 := tree_ramShapeAt n σ k
  rw [← hT, WildMenu.tree_sepShape n lam] at h1
  have hval : n = WildMenu.fSum σ := by
    have hhead := List.head_eq_of_cons_eq h1
    have := congrArg (fun t : ℕ × ℕ × ℕ => t.2.2) hhead
    simpa using this
  have := WildMenu.constERam_fSum_lt h
  omega

theorem ramShapes3_disjoint_sepShapesOf (n K : ℕ) (σ σ' : FactorizationType) :
    Disjoint (ramShapes3 n K σ) (Order0.sepShapesOf n σ') := by
  rw [Finset.disjoint_left]
  intro T hT hT'
  rw [mem_ramShapes3] at hT
  obtain ⟨hc, k, -, rfl⟩ := hT
  exact ramShapeAt_not_mem_sepShapesOf hc k hT'

/-- **The cross-σ disjointness lever**: every windowed menu shape names its type. -/
theorem mem_omMenuW3_type {n K : ℕ} {σ : FactorizationType} {T : ClusterShape}
    (hT : T ∈ omMenuW3 n K σ) : WildMenu.typeOfW n T = some σ := by
  rw [omMenuW3, Finset.mem_union] at hT
  rcases hT with h | h
  · simp only [Order0.sepShapesOf, Finset.mem_image, Finset.mem_filter, Finset.mem_univ,
      true_and] at h
    obtain ⟨lam, hσ, rfl⟩ := h
    rw [WildMenu.typeOfW_sepShape n lam, hσ]
  · rw [mem_ramShapes3] at h
    obtain ⟨hc, k, -, rfl⟩ := h
    exact typeOfW_ramShapeAt hc k

/-- Distinct types have disjoint windowed menus — at ANY two window bounds. -/
theorem eq_of_mem_omMenuW3 {n K K' : ℕ} {σ σ' : FactorizationType} {T : ClusterShape}
    (h : T ∈ omMenuW3 n K σ) (h' : T ∈ omMenuW3 n K' σ') : σ = σ' := by
  have h1 := mem_omMenuW3_type h
  have h2 := mem_omMenuW3_type h'
  rw [h1] at h2
  exact Option.some.inj h2

/-- Every windowed menu shape has tree size `n`. -/
theorem treeSize_of_mem_omMenuW3 {n K : ℕ} {σ : FactorizationType} {T : ClusterShape}
    (hT : T ∈ omMenuW3 n K σ) : M6.treeSize T = n := by
  rw [omMenuW3, Finset.mem_union] at hT
  rcases hT with h | h
  · simp only [Order0.sepShapesOf, Finset.mem_image, Finset.mem_filter, Finset.mem_univ,
      true_and] at h
    obtain ⟨lam, -, rfl⟩ := h
    rfl
  · rw [mem_ramShapes3] at h
    obtain ⟨hc, k, -, rfl⟩ := h
    unfold M6.treeSize
    rw [tree_ramShapeAt]

/-- The windowed-menu reindexing over the admissible multipliers (feed for W3b sums). -/
theorem sum_ramShapes3_eq {n K : ℕ} {σ : FactorizationType} (h : WildMenu.constERam n σ)
    {M : Type*} [AddCommMonoid M] (g : ClusterShape → M) :
    ∑ T ∈ ramShapes3 n K σ, g T
      = ∑ k ∈ admissibleK (n / WildMenu.fSum σ) K, g (ramShapeAt n σ k) := by
  rw [ramShapes3_of_constERam h]
  exact Finset.sum_image (fun k _ k' _ heq => ramShapeAt_injective_k h heq)

/-! ## 5. The box bound over the windowed union family -/

/-- **The union re-indexing** (windowed): the double sum over the UNCHANGED type menu and its
enlarged σ-keyed menus is the single sum over the biUnion — distinct σ have disjoint windowed
menus (`eq_of_mem_omMenuW3`). -/
theorem sum_omMenuW3_eq_biUnion (n K : ℕ) {M : Type*} [AddCommMonoid M]
    (f : ClusterShape → M) :
    ∑ σ ∈ WildMenuPrep.typeMenuW n, ∑ T ∈ omMenuW3 n K σ, f T
      = ∑ T ∈ (WildMenuPrep.typeMenuW n).biUnion (fun σ => omMenuW3 n K σ), f T := by
  refine (Finset.sum_biUnion ?_).symm
  intro σ _hσ σ' _hσ' hne
  exact Finset.disjoint_left.mpr fun T hT hT' => hne (eq_of_mem_omMenuW3 hT hT')

/-- **The box bound over the windowed union family** (the `undecidedCount ≥ 0` feed): at every
level `N ≥ 1` the total decided count over the whole type menu, with EVERY per-σ window-K menu,
is at most the box count `realP^(nN)` — the fibers of `realClassify` over the (distinct) menu
shapes are disjoint. Mirrors `WildMenuPrep.sum_stratumCount_le_box_W` verbatim. -/
theorem sum_stratumCount_le_box_W3 (n K N : ℕ) (hN : 0 < N) :
    (∑ σ ∈ WildMenuPrep.typeMenuW n, ∑ T ∈ omMenuW3 n K σ,
        M8.stratumCount (M9.rawCount n) T N)
      ≤ (M9.realP : ℚ) ^ (n * N) := by
  rw [sum_omMenuW3_eq_biUnion]
  set S := (WildMenuPrep.typeMenuW n).biUnion (fun σ => omMenuW3 n K σ) with hS
  haveI hfin : Finite (QuotientBox.monicBox M9.realP N n) := by
    have hpos : 0 < Nat.card (QuotientBox.monicBox M9.realP N n) := by
      rw [QuotientBox.card_monicBox M9.realP N n hN]
      exact pow_pos (pow_pos (by norm_num [M9.realP]) N) n
    exact (Nat.card_pos_iff.mp hpos).2
  have key : (∑ T ∈ S, M9.rawCount n T N) ≤ M9.realP ^ (n * N) := by
    have hle := WildMenuPrep.sum_card_fibers_le_finset S (M9.realClassify n N)
    rw [QuotientBox.card_monicBox M9.realP N n hN] at hle
    calc ∑ T ∈ S, M9.rawCount n T N
        = ∑ T ∈ S, Nat.card {f : QuotientBox.monicBox M9.realP N n //
            M9.realClassify n N f = T} := rfl
      _ ≤ (M9.realP ^ N) ^ n := hle
      _ = M9.realP ^ (n * N) := by rw [← pow_mul, Nat.mul_comm]
  calc (∑ T ∈ S, M8.stratumCount (M9.rawCount n) T N)
      = ((∑ T ∈ S, M9.rawCount n T N : ℕ) : ℚ) := by
        rw [Nat.cast_sum]
        rfl
    _ ≤ ((M9.realP ^ (n * N) : ℕ) : ℚ) := by exact_mod_cast key
    _ = (M9.realP : ℚ) ^ (n * N) := by push_cast; ring

/-! ## 6. The per-leg level behavior (small-N vanishing, closed form, constancy) -/

/-- **Per-leg small-N vanishing**: at every level `N ≤ F·k` the k-leg stratum count is `0`.
Level `0`: empty box. Levels `1 ≤ N ≤ F·k`: the classifier fiber is EMPTY — `classify =
Tselfloop` forces the Newton vertex `(0, F·k)` to be a support dot, whose native valuation is
`< N ≤ F·k`. Mirrors `WildMenuPrep.stratumCount_ramShape_smallN` (the support-dot route is
H-generic; only the vertex height changes). -/
theorem stratumCount_ramShapeAt_smallN {n : ℕ} {σ : FactorizationType}
    (h : WildMenu.constERam n σ) {k N : ℕ} (hN : N ≤ WildMenu.fSum σ * k) :
    M8.stratumCount (M9.rawCount n) (ramShapeAt n σ k) N = 0 := by
  have hn : 0 < n := WildMenu.constERam_n_pos h
  rcases Nat.eq_zero_or_pos N with rfl | hNpos
  · exact RealInstanceV2.stratumCount_level0 n hn _
  · haveI : IsEmpty {f : QuotientBox.monicBox M9.realP N n //
        M9.realClassify n N f = ramShapeAt n σ k} := by
      constructor
      rintro ⟨f, hcl⟩
      have hcl' : B.classify M9.realP n N f = ClassifierBridgeFiber.Tselfloop n
          (((0, WildMenu.fSum σ * k), (n, 0)) : (ℕ × ℕ) × (ℕ × ℕ)) (WildMenu.wShape σ) := hcl
      have hrs := ClassifierBridgeFiber2.rootSide_eq_of_classify hn hNpos f
        (WildMenu.wShape σ) hcl' (WildMenu.wShape_ne h)
      have hverts := ClassifierBridgeFiber.npVertices_of_rootSide M9.realP hn hNpos f hrs
      have hmem0 : (((0 : ℕ), WildMenu.fSum σ * k) : ℕ × ℕ)
          ∈ NewtonPolygon.npVertices (B.boxValSupport M9.realP N f)
              (B.boxValSupport_nonempty M9.realP N hNpos f) := by
        rw [hverts]
        exact List.mem_cons_self ..
      have hS := ClassifierBridgeFiber.mem_S_of_mem_npVertices M9.realP f
        (B.boxValSupport_nonempty M9.realP N hNpos f) hmem0
      obtain ⟨hv, hne0⟩ := ClassifierBridgeFiber.boxValSupport_eq_dot M9.realP f hS
      have hlt : PadicLift.zmodValuation M9.realP N ((f.1).coeff 0) < N :=
        PadicLift.zmodValuation_lt M9.realP hNpos hne0
      have hv' : WildMenu.fSum σ * k
          = PadicLift.zmodValuation M9.realP N ((f.1).coeff 0) := hv
      omega
    change ((M9.rawCount n (ramShapeAt n σ k) N : ℕ) : ℚ) = 0
    rw [show M9.rawCount n (ramShapeAt n σ k) N
        = Nat.card {f : QuotientBox.monicBox M9.realP N n //
            M9.realClassify n N f = ramShapeAt n σ k} from rfl, Nat.card_of_isEmpty]
    norm_num

/-- **The k-leg stratum count closed form** at every level `N ≥ F·k + 1`: the banked count
identity `stratumCount_selfloop_R` (H-generic) composed with the order-1 closed form. Mirrors
`WildMenuPrep.stratumCount_ramShape_eq_closed`. -/
theorem stratumCount_ramShapeAt_eq_closed {n : ℕ} {σ : FactorizationType} {k : ℕ}
    (h : WildMenu.constERam n σ) (hk1 : 1 ≤ k)
    (hk : Nat.gcd k (n / WildMenu.fSum σ) = 1) {N : ℕ}
    (hN : WildMenu.fSum σ * k + 1 ≤ N) :
    M8.stratumCount (M9.rawCount n) (ramShapeAt n σ k) N
      = (CellCard.prodSC M9.realP [WildMenu.wShape σ] : ℚ)
          * (M9.realP : ℚ) ^ CellCard.freeExp n N (wPathAt n σ k) := by
  have hn : 0 < n := WildMenu.constERam_n_pos h
  have hNpos : 0 < N := by omega
  have hPN : MenuPath n N (wPathAt n σ k) := menuPath_wPathAt_of_le h hk1 hN
  rw [ramShapeAt_def]
  rw [ClassifierBridgeFiber2.stratumCount_selfloop_R n N hNpos hn (wPathAt n σ k) hPN
    (((0, WildMenu.fSum σ * k), (n, 0)) : (ℕ × ℕ) × (ℕ × ℕ)) (sidePairs_wPathAt n σ k)
    (WildMenu.wShape σ) (shapesFor_wPathAt h hk) (WildMenu.wShape_mu σ)
    (WildMenu.wShape_ne h)]
  rw [StratumOrder1.stratumCount1_eq_closed M9.realP hNpos hPN (shapesFor_wPathAt h hk)]
  push_cast
  ring

/-- **Per-leg level constancy above the leg's OWN threshold** `N₀ = F·k + 1` (each leg joins
its staircase at its own height): the normalized k-leg count is constant for `N ≥ F·k + 1`.
Mirrors `WildMenuPrep.normRamCount_levelConst` (the count identity is H-generic). -/
theorem normRamCountAt_levelConst {n : ℕ} {σ : FactorizationType} {k : ℕ}
    (h : WildMenu.constERam n σ) (hk1 : 1 ≤ k)
    (hk : Nat.gcd k (n / WildMenu.fSum σ) = 1) {N : ℕ}
    (hN : WildMenu.fSum σ * k + 1 ≤ N) :
    M8.stratumCount (M9.rawCount n) (ramShapeAt n σ k) N / (M9.realP : ℚ) ^ (n * N)
      = M8.stratumCount (M9.rawCount n) (ramShapeAt n σ k) (WildMenu.fSum σ * k + 1)
          / (M9.realP : ℚ) ^ (n * (WildMenu.fSum σ * k + 1)) := by
  have hP₀ : MenuPath n (WildMenu.fSum σ * k + 1) (wPathAt n σ k) := menuPath_wPathAt h hk1
  rw [stratumCount_ramShapeAt_eq_closed h hk1 hk hN,
    stratumCount_ramShapeAt_eq_closed h hk1 hk (le_refl _),
    DecidedOrder1.freeExp_eq_add_mul hP₀ hN]
  have hp0 : (M9.realP : ℚ) ≠ 0 := by norm_num [M9.realP]
  have hsplit : n * (WildMenu.fSum σ * k + 1) + n * (N - (WildMenu.fSum σ * k + 1))
      = n * N := by
    rw [← Nat.mul_add]
    congr 1
    omega
  rw [pow_add, show (M9.realP : ℚ) ^ (n * N)
      = (M9.realP : ℚ) ^ (n * (WildMenu.fSum σ * k + 1))
          * (M9.realP : ℚ) ^ (n * (N - (WildMenu.fSum σ * k + 1))) from by
    rw [← pow_add, hsplit]]
  have hB : (M9.realP : ℚ) ^ (n * (N - (WildMenu.fSum σ * k + 1))) ≠ 0 := pow_ne_zero _ hp0
  field_simp

/-- The `∃ N₀` packaging of the per-leg eventual constancy. -/
theorem normRamCountAt_eventually_const {n : ℕ} {σ : FactorizationType} {k : ℕ}
    (h : WildMenu.constERam n σ) (hk1 : 1 ≤ k)
    (hk : Nat.gcd k (n / WildMenu.fSum σ) = 1) :
    ∃ N₀, 0 < N₀ ∧ ∀ N, N₀ ≤ N →
      M8.stratumCount (M9.rawCount n) (ramShapeAt n σ k) N / (M9.realP : ℚ) ^ (n * N)
        = M8.stratumCount (M9.rawCount n) (ramShapeAt n σ k) N₀
            / (M9.realP : ℚ) ^ (n * N₀) :=
  ⟨WildMenu.fSum σ * k + 1, Nat.succ_pos _,
    fun _N hN => normRamCountAt_levelConst h hk1 hk hN⟩

/-! ## 7. Monotonicity of the windowed normalized sum -/

/-- **Each k-leg is a monotone staircase**: `0, …, 0` through level `F·k`, then constant
`c_k ≥ 0` from level `F·k + 1`. -/
theorem normRamCountAt_mono {n : ℕ} {σ : FactorizationType} {k : ℕ}
    (h : WildMenu.constERam n σ) (hk1 : 1 ≤ k)
    (hk : Nat.gcd k (n / WildMenu.fSum σ) = 1) :
    Monotone (fun N => M8.stratumCount (M9.rawCount n) (ramShapeAt n σ k) N
      / (M9.realP : ℚ) ^ (n * N)) := by
  intro N₁ N₂ h₁₂
  dsimp only
  rcases Nat.lt_or_ge (WildMenu.fSum σ * k) N₂ with hK | hK
  · rcases Nat.lt_or_ge (WildMenu.fSum σ * k) N₁ with hNgt | hNle
    · rw [normRamCountAt_levelConst h hk1 hk (by omega : WildMenu.fSum σ * k + 1 ≤ N₁),
        normRamCountAt_levelConst h hk1 hk (by omega : WildMenu.fSum σ * k + 1 ≤ N₂)]
    · rw [stratumCount_ramShapeAt_smallN h hNle, zero_div]
      exact div_nonneg (M8.stratumCount_nonneg _ _ _)
        (le_of_lt (RealInstanceV2.realP_pow_pos _))
  · rw [stratumCount_ramShapeAt_smallN h (h₁₂.trans hK),
      stratumCount_ramShapeAt_smallN h hK, zero_div, zero_div]

/-- **FULL monotonicity of the normalized windowed menu sum** (the `decided_mono` discharge for
the window-K counting model). For constant-e σ the menu sum is a FINITE SUM of monotone
staircases — the legs join at their own thresholds `N = F·k + 1`, and a finite sum of monotone
functions is monotone. For every other σ the menu is Wave 1's, whose monotonicity is banked
(`WildMenuPrep.normSum_omMenuW_mono`). -/
theorem normSum_omMenuW3_mono (n K : ℕ) (hn : 0 < n) (σ : FactorizationType) :
    Monotone (fun N => (∑ T ∈ omMenuW3 n K σ, M8.stratumCount (M9.rawCount n) T N)
      / (M9.realP : ℚ) ^ (n * N)) := by
  by_cases hc : WildMenu.constERam n σ
  · -- the windowed wild menu: a finite sum of 0-then-constant staircases
    have hsum : ∀ N, (∑ T ∈ omMenuW3 n K σ, M8.stratumCount (M9.rawCount n) T N)
        = ∑ k ∈ admissibleK (n / WildMenu.fSum σ) K,
            M8.stratumCount (M9.rawCount n) (ramShapeAt n σ k) N := by
      intro N
      rw [omMenuW3_ram_of_constE hc]
      exact Finset.sum_image (fun k _ k' _ heq => ramShapeAt_injective_k hc heq)
    intro N₁ N₂ h₁₂
    calc (∑ T ∈ omMenuW3 n K σ, M8.stratumCount (M9.rawCount n) T N₁)
            / (M9.realP : ℚ) ^ (n * N₁)
        = ∑ k ∈ admissibleK (n / WildMenu.fSum σ) K,
            M8.stratumCount (M9.rawCount n) (ramShapeAt n σ k) N₁
              / (M9.realP : ℚ) ^ (n * N₁) := by
          rw [hsum N₁, Finset.sum_div]
      _ ≤ ∑ k ∈ admissibleK (n / WildMenu.fSum σ) K,
            M8.stratumCount (M9.rawCount n) (ramShapeAt n σ k) N₂
              / (M9.realP : ℚ) ^ (n * N₂) := by
          refine Finset.sum_le_sum fun k hk => ?_
          obtain ⟨⟨hk1, -⟩, hke⟩ := mem_admissibleK.mp hk
          exact normRamCountAt_mono hc hk1 hke h₁₂
      _ = (∑ T ∈ omMenuW3 n K σ, M8.stratumCount (M9.rawCount n) T N₂)
            / (M9.realP : ℚ) ^ (n * N₂) := by
          rw [hsum N₂, Finset.sum_div]
  · -- every other σ: the menu is Wave 1's, monotonicity is banked
    have hmenu : omMenuW3 n K σ = WildMenu.omMenuW n σ := by
      rw [omMenuW3_unram hc, WildMenu.omMenuW_unram hc]
    simp only [hmenu]
    exact WildMenuPrep.normSum_omMenuW_mono n hn σ

/-! ## 8. Nonnegativity of the per-leg engine value (the `density_nonneg` feed) -/

/-- The engine value of every k-leg is nonnegative at EVERY natural `q'` — the banked
`WildMenuPrep.omCount_Tselfloop_nonneg` is already H-generic. -/
theorem omCount_ramShapeAt_nonneg {n : ℕ} {σ : FactorizationType}
    (h : WildMenu.constERam n σ) (k : ℕ) (q' : ℕ) :
    0 ≤ OMCountV2.omCount (ramShapeAt n σ k) q' :=
  WildMenuPrep.omCount_Tselfloop_nonneg n (WildMenu.fSum σ * k) (WildMenu.wShape σ)
    (WildMenu.wShape_pos h) (WildMenu.wShape_ne h) q'

/-! ## 9. AxCheck — every declaration of this wave is core-only -/

section AxCheck
#print axioms admissibleK
#print axioms mem_admissibleK
#print axioms admissibleK_one
#print axioms gcd_admissible
#print axioms wPathAt
#print axioms ramShapeAt
#print axioms ramShapeAt_def
#print axioms ramShapeAt_one
#print axioms sidePairs_wPathAt
#print axioms sideDeg_wPathAt
#print axioms menuPath_wPathAt_of_le
#print axioms menuPath_wPathAt
#print axioms shapesFor_wPathAt
#print axioms ramShapeAtWitness
#print axioms ramShapes3
#print axioms ramShapes3_of_constERam
#print axioms ramShapes3_of_not_constERam
#print axioms mem_ramShapes3
#print axioms omMenuW3
#print axioms omMenuW3_unram
#print axioms omMenuW3_ram_of_constE
#print axioms omMenuW3_one
#print axioms tree_Tselfloop_wShape
#print axioms tree_ramShapeAt
#print axioms ramShapeAt_height_eq
#print axioms ramShapeAt_injective_k
#print axioms typeOfW_Tselfloop_wShape
#print axioms typeOfW_ramShapeAt
#print axioms ramShapeAt_not_mem_sepShapesOf
#print axioms ramShapes3_disjoint_sepShapesOf
#print axioms mem_omMenuW3_type
#print axioms eq_of_mem_omMenuW3
#print axioms treeSize_of_mem_omMenuW3
#print axioms sum_ramShapes3_eq
#print axioms sum_omMenuW3_eq_biUnion
#print axioms sum_stratumCount_le_box_W3
#print axioms stratumCount_ramShapeAt_smallN
#print axioms stratumCount_ramShapeAt_eq_closed
#print axioms normRamCountAt_levelConst
#print axioms normRamCountAt_eventually_const
#print axioms normRamCountAt_mono
#print axioms normSum_omMenuW3_mono
#print axioms omCount_ramShapeAt_nonneg
end AxCheck

end LeanUrat.OM.WildMenuW3
