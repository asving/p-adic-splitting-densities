/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.OM.WildMenu
import LeanUrat.OM.RealInstanceV2
import LeanUrat.OM.ClassifierBridgeFiber2
import LeanUrat.OM.DecidedOrder1

/-!
# WildMenuPrep — the Prep-bank generalization to the union (wild) menu (Wave 1a,
`notes/WILD_WAVE1_BLUEPRINT_2026-07-21.md` §2 item 2)

Generalizes `RealInstanceV2Prep` from the order-0 separable menu to the union family
`omMenuW n σ = sepShapesOf n σ ∪ (ramShape n σ).toFinset` over the enlarged type menu
`typeMenuW n = unramTypeMenu n ∪ constERamTypes n`. Contents:

* `constERamTypes n` — the FINITE set of constant-e ramified degree-`n` types (`e ∣ n`, `e ≥ 2`,
  `f`-parts a partition of `n/e`); `mem_constERamTypes` (the defining iff), `typeMenuW` with
  degree + disjointness facts.
* **The box bound** `sum_stratumCount_le_box_W`: at every level `N ≥ 1` the total decided count
  over the union type menu is at most the box count `realP^(nN)` — pairwise-disjoint classifier
  fibers over the union (cross-σ disjointness via `WildMenu.mem_omMenuW_type`; the fiber-count
  argument is `sum_card_fibers_le_finset`, the Finset-indexed form of
  `RealInstanceV2Prep.sum_card_fibers_le`).
* **The ramified-leg level behavior** (the `decided_mono`/`decided_tendsto` feed):
  - `stratumCount_ramShape_smallN` — the stratum count VANISHES at every level `N ≤ fSum σ`
    (level 0: empty box; `1 ≤ N ≤ fSum σ`: the classifier fiber is EMPTY, because
    `classify = Tselfloop` forces the Newton vertex `(0, H)` to be a support dot, whose native
    valuation is `< N` — but `H = fSum σ ≥ N`);
  - `normRamCount_levelConst` — for `N ≥ N₀ := fSum σ + 1` the normalized count is CONSTANT
    (`= its N₀ value`): the banked count identity `stratumCount_selfloop_R` + the closed form
    `stratumCount1_eq_closed` + the `freeExp` affinity `freeExp_eq_add_mul`; `N₀` depends on σ
    through the height `H = fSum σ` (pinned, per blueprint §3);
  - `normRamCount_eventually_const` — the `∃ N₀, ∀ N ≥ N₀, …` packaging;
  - `normSum_omMenuW_mono` — FULL monotonicity of the normalized union menu sum (the
    `decided_mono` discharge): the sequence is `0, …, 0, c, c, …` on the wild leg
    (vanishing below `N₀`, constancy from `N₀`) and `0, c', c', …` on the order-0 leg.
* **Nonnegativity of the wild engine value at EVERY natural `q'`** (`density_nonneg` feed):
  `omCount_Tselfloop_nonneg` / `omCount_ramShape_nonneg`, mirroring
  `RealInstanceV2.omCount_sepShape_nonneg`: at `q' = 0` the volume factor kills the value; at
  `q' ≥ 1` the face choice polynomial is a product of falling factorials of naturals
  (`ffPoly_availPoly_eval_nonneg`) and the volume factor is an inverse of a nonnegative.

Leaf module: no existing file is modified. No axiom, no sorry.
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false

namespace LeanUrat.OM.WildMenuPrep

open scoped Classical
open LeanUrat LeanUrat.OM Finset
open LeanUrat.OM.CellMenu
open LeanUrat.OM.OMCountV2 (omCount configOf configsOf mCell volExp choicePoly)

/-! ## 1. The finite constant-e ramified type menu -/

/-- **The constant-e ramified degree-`n` type menu** (finite by construction): for each divisor
`e ≥ 2` of `n` and each partition of `n/e` (the `f`-parts), the type `{(e, f) : f ∈ parts}`. -/
noncomputable def constERamTypes (n : ℕ) : Finset FactorizationType :=
  (n.divisors.filter (fun e => 2 ≤ e)).biUnion
    (fun e => (Finset.univ : Finset (Nat.Partition (n / e))).image
      (fun lam => ⟨lam.parts.map (fun f => (e, f))⟩))

/-- Membership in `constERamTypes` is EXACTLY the `constERam` predicate. -/
theorem mem_constERamTypes {n : ℕ} {σ : FactorizationType} :
    σ ∈ constERamTypes n ↔ WildMenu.constERam n σ := by
  constructor
  · intro h
    simp only [constERamTypes, Finset.mem_biUnion, Finset.mem_filter, Nat.mem_divisors,
      Finset.mem_image, Finset.mem_univ, true_and] at h
    obtain ⟨e, ⟨⟨hdvd, hn0⟩, he2⟩, lam, rfl⟩ := h
    have he0 : 0 < e := by omega
    have hle : e ≤ n := Nat.le_of_dvd (Nat.pos_of_ne_zero hn0) hdvd
    have hdivpos : 0 < n / e := Nat.div_pos hle he0
    refine ⟨e, he2, ?_, ?_, ?_⟩
    · -- data ≠ 0
      intro hdata
      have hparts : lam.parts = 0 := by
        simpa [Multiset.map_eq_zero] using hdata
      have hsum := lam.parts_sum
      rw [hparts, Multiset.sum_zero] at hsum
      omega
    · intro pr hpr
      rw [show (⟨lam.parts.map (fun f => (e, f))⟩ : FactorizationType).data
          = lam.parts.map (fun f => (e, f)) from rfl, Multiset.mem_map] at hpr
      obtain ⟨f, hf, rfl⟩ := hpr
      exact ⟨rfl, lam.parts_pos hf⟩
    · change e * ((lam.parts.map (fun f => (e, f))).map Prod.snd).sum = n
      rw [Multiset.map_map]
      simp only [Function.comp_def]
      rw [Multiset.map_id', lam.parts_sum]
      exact Nat.mul_div_cancel' hdvd
  · rintro ⟨e, he2, hne, hall, hprod⟩
    have hfpos : 0 < WildMenu.fSum σ :=
      WildMenu.constERam_fSum_pos ⟨e, he2, hne, hall, hprod⟩
    have he0 : 0 < e := by omega
    have hn0 : n ≠ 0 := by
      have h21 : 2 * 1 ≤ e * WildMenu.fSum σ := Nat.mul_le_mul he2 hfpos
      omega
    simp only [constERamTypes, Finset.mem_biUnion, Finset.mem_filter, Nat.mem_divisors,
      Finset.mem_image, Finset.mem_univ, true_and]
    refine ⟨e, ⟨⟨⟨WildMenu.fSum σ, hprod.symm⟩, hn0⟩, he2⟩,
      ⟨σ.data.map Prod.snd, ?_, ?_⟩, ?_⟩
    · intro f hf
      rw [Multiset.mem_map] at hf
      obtain ⟨pr, hpr, rfl⟩ := hf
      exact (hall pr hpr).2
    · show (σ.data.map Prod.snd).sum = n / e
      have : WildMenu.fSum σ = n / e := by
        rw [← hprod, Nat.mul_div_cancel_left _ he0]
      exact this
    · change (⟨(σ.data.map Prod.snd).map (fun f => (e, f))⟩ : FactorizationType) = σ
      rw [WildMenu.data_eq_map_snd (fun pr hpr => (hall pr hpr).1)]

/-- **The Wave-1 type menu**: the unramified types plus the constant-e ramified types. -/
noncomputable def typeMenuW (n : ℕ) : Finset FactorizationType :=
  RealInstanceV2Prep.unramTypeMenu n ∪ constERamTypes n

/-- Every menu type has degree `n`. -/
theorem typeMenuW_degree (n : ℕ) : ∀ σ ∈ typeMenuW n, σ.degree = n := by
  intro σ hσ
  rw [typeMenuW, Finset.mem_union] at hσ
  rcases hσ with h | h
  · simp only [RealInstanceV2Prep.unramTypeMenu, Finset.mem_image, Finset.mem_univ,
      true_and] at h
    obtain ⟨lam, rfl⟩ := h
    exact RealInstanceV2.unramType_degree n lam
  · exact WildMenu.constERam_degree (mem_constERamTypes.mp h)

/-- An unramified-menu type is never constant-e ramified (its pairs all have `e = 1`). -/
theorem unramTypeMenu_not_constERam {n : ℕ} {σ : FactorizationType}
    (hσ : σ ∈ RealInstanceV2Prep.unramTypeMenu n) : ¬ WildMenu.constERam n σ := by
  intro hc
  obtain ⟨e, he2, hne, hall, -⟩ := hc
  simp only [RealInstanceV2Prep.unramTypeMenu, Finset.mem_image, Finset.mem_univ,
    true_and] at hσ
  obtain ⟨lam, rfl⟩ := hσ
  obtain ⟨pr, hpr⟩ := Multiset.exists_mem_of_ne_zero hne
  have h1 : pr.1 = 1 := by
    have hpr' : pr ∈ lam.parts.map (fun d => ((1 : ℕ), d)) := hpr
    rw [Multiset.mem_map] at hpr'
    obtain ⟨d, -, rfl⟩ := hpr'
    rfl
  have he := (hall pr hpr).1
  omega

/-- The two halves of the type menu are disjoint. -/
theorem disjoint_unram_constERamTypes (n : ℕ) :
    Disjoint (RealInstanceV2Prep.unramTypeMenu n) (constERamTypes n) :=
  Finset.disjoint_left.mpr fun _σ hσ hσ' =>
    unramTypeMenu_not_constERam hσ (mem_constERamTypes.mp hσ')

/-! ## 2. The box bound over the union family -/

/-- Fibers of a function over the distinct elements of a `Finset` of values are disjoint, so
their counts sum to at most the domain cardinality (the Finset-indexed form of
`RealInstanceV2Prep.sum_card_fibers_le` — no injectivity needed, the values ARE distinct). -/
theorem sum_card_fibers_le_finset {α β : Type*} [Finite α] (s : Finset β) (g : α → β) :
    ∑ b ∈ s, Nat.card {a : α // g a = b} ≤ Nat.card α := by
  classical
  cases nonempty_fintype α
  calc ∑ b ∈ s, Nat.card {a : α // g a = b}
      = ∑ b ∈ s, (Finset.univ.filter (fun a : α => g a = b)).card :=
        Finset.sum_congr rfl fun b _ => by
          rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    _ = (s.biUnion (fun b => Finset.univ.filter (fun a : α => g a = b))).card := by
        refine (Finset.card_biUnion ?_).symm
        intro b _ b' _ hbb'
        refine Finset.disjoint_left.mpr fun a ha ha' => hbb' ?_
        rw [← (Finset.mem_filter.mp ha).2, ← (Finset.mem_filter.mp ha').2]
    _ ≤ Fintype.card α := Finset.card_le_univ _
    _ = Nat.card α := (Nat.card_eq_fintype_card).symm

/-- **The union re-indexing**: the double sum over the type menu and its σ-keyed menus is the
single sum over the biUnion of the menus — distinct σ have disjoint menus
(`WildMenu.eq_of_mem_omMenuW`). -/
theorem sum_omMenuW_eq_biUnion (n : ℕ) {M : Type*} [AddCommMonoid M] (f : ClusterShape → M) :
    ∑ σ ∈ typeMenuW n, ∑ T ∈ WildMenu.omMenuW n σ, f T
      = ∑ T ∈ (typeMenuW n).biUnion (fun σ => WildMenu.omMenuW n σ), f T := by
  refine (Finset.sum_biUnion ?_).symm
  intro σ _hσ σ' _hσ' hne
  exact Finset.disjoint_left.mpr fun T hT hT' =>
    hne (WildMenu.eq_of_mem_omMenuW hT hT')

/-- **The box bound over the union family** (the `undecidedCount ≥ 0` feed): at every level
`N ≥ 1` the total decided count over the whole Wave-1 type menu is at most the box count
`realP^(nN)`. -/
theorem sum_stratumCount_le_box_W (n N : ℕ) (hN : 0 < N) :
    (∑ σ ∈ typeMenuW n, ∑ T ∈ WildMenu.omMenuW n σ, M8.stratumCount (M9.rawCount n) T N)
      ≤ (M9.realP : ℚ) ^ (n * N) := by
  rw [sum_omMenuW_eq_biUnion]
  set S := (typeMenuW n).biUnion (fun σ => WildMenu.omMenuW n σ) with hS
  haveI hfin : Finite (QuotientBox.monicBox M9.realP N n) := by
    have hpos : 0 < Nat.card (QuotientBox.monicBox M9.realP N n) := by
      rw [QuotientBox.card_monicBox M9.realP N n hN]
      exact pow_pos (pow_pos (by norm_num [M9.realP]) N) n
    exact (Nat.card_pos_iff.mp hpos).2
  have key : (∑ T ∈ S, M9.rawCount n T N) ≤ M9.realP ^ (n * N) := by
    have hle := sum_card_fibers_le_finset S (M9.realClassify n N)
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

/-! ## 3. The ramified-leg level behavior -/

/-- The canonical menu path is a valid `MenuPath` at every level `N ≥ fSum σ + 1`. -/
theorem menuPath_wPath_of_le {n N : ℕ} {σ : FactorizationType}
    (h : WildMenu.constERam n σ) (hN : WildMenu.fSum σ + 1 ≤ N) :
    MenuPath n N (WildMenu.wPath n σ) := by
  have hn : 0 < n := WildMenu.constERam_n_pos h
  have hf : 0 < WildMenu.fSum σ := WildMenu.constERam_fSum_pos h
  exact ⟨WildMenu.fSum σ, ((n : ℕ), (0 : ℕ)), [], rfl, hf, by omega, hn, hf,
    ChainOK.nil rfl rfl⟩

/-- **The wild stratum count closed form** at every level `N ≥ fSum σ + 1`: the banked count
identity `stratumCount_selfloop_R` composed with the order-1 closed form
`stratumCount1_eq_closed`. -/
theorem stratumCount_ramShape_eq_closed {n : ℕ} {σ : FactorizationType} {T : ClusterShape}
    (hT : WildMenu.ramShape n σ = some T) {N : ℕ} (hN : WildMenu.fSum σ + 1 ≤ N) :
    M8.stratumCount (M9.rawCount n) T N
      = (CellCard.prodSC M9.realP [WildMenu.wShape σ] : ℚ)
          * (M9.realP : ℚ) ^ CellCard.freeExp n N (WildMenu.wPath n σ) := by
  have hc := WildMenu.constERam_of_ramShape hT
  have hn : 0 < n := WildMenu.constERam_n_pos hc
  have hNpos : 0 < N := by omega
  have hPN : MenuPath n N (WildMenu.wPath n σ) := menuPath_wPath_of_le hc hN
  rw [WildMenu.ramShape_some_eq hT]
  rw [ClassifierBridgeFiber2.stratumCount_selfloop_R n N hNpos hn (WildMenu.wPath n σ) hPN
    (((0, WildMenu.fSum σ), (n, 0)) : (ℕ × ℕ) × (ℕ × ℕ)) (WildMenu.sidePairs_wPath n σ)
    (WildMenu.wShape σ) (WildMenu.shapesFor_wPath hc) (WildMenu.wShape_mu σ)
    (WildMenu.wShape_ne hc)]
  rw [StratumOrder1.stratumCount1_eq_closed M9.realP hNpos hPN
    (WildMenu.shapesFor_wPath hc)]
  push_cast
  ring

/-- **Level-≥N₀ constancy of the normalized wild stratum count** (the `decided_mono` /
`decided_tendsto` feed; `N₀ = fSum σ + 1 = H + 1` — the threshold DEPENDS on σ through the
self-loop height `H = fSum σ`, unlike the order-0 legs' uniform `N₀ = 1`). -/
theorem normRamCount_levelConst {n : ℕ} {σ : FactorizationType} {T : ClusterShape}
    (hT : WildMenu.ramShape n σ = some T) {N : ℕ} (hN : WildMenu.fSum σ + 1 ≤ N) :
    M8.stratumCount (M9.rawCount n) T N / (M9.realP : ℚ) ^ (n * N)
      = M8.stratumCount (M9.rawCount n) T (WildMenu.fSum σ + 1)
          / (M9.realP : ℚ) ^ (n * (WildMenu.fSum σ + 1)) := by
  have hc := WildMenu.constERam_of_ramShape hT
  have hP₀ : MenuPath n (WildMenu.fSum σ + 1) (WildMenu.wPath n σ) :=
    WildMenu.menuPath_wPath hc
  rw [stratumCount_ramShape_eq_closed hT hN,
    stratumCount_ramShape_eq_closed hT (le_refl _),
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

/-- The `∃ N₀` packaging of the eventual constancy (blueprint §2 item 2 statement shape). -/
theorem normRamCount_eventually_const {n : ℕ} {σ : FactorizationType} {T : ClusterShape}
    (hT : WildMenu.ramShape n σ = some T) :
    ∃ N₀, 0 < N₀ ∧ ∀ N, N₀ ≤ N →
      M8.stratumCount (M9.rawCount n) T N / (M9.realP : ℚ) ^ (n * N)
        = M8.stratumCount (M9.rawCount n) T N₀ / (M9.realP : ℚ) ^ (n * N₀) :=
  ⟨WildMenu.fSum σ + 1, Nat.succ_pos _, fun _N hN => normRamCount_levelConst hT hN⟩

/-- **Small-N vanishing of the wild stratum count** (the `decided_mono` edge): at every level
`N ≤ fSum σ` the count is `0`. Level `0`: the box over `ZMod 1` is empty. Levels
`1 ≤ N ≤ fSum σ`: the classifier fiber is EMPTY — `classify = Tselfloop` forces
`rootSide = some (mkSide ((0,H),(n,0)))` (`rootSide_eq_of_classify`), hence the Newton vertex
`(0, H)` is a support dot (`npVertices_of_rootSide` + `mem_S_of_mem_npVertices` +
`boxValSupport_eq_dot`), whose native valuation is `< N` (`zmodValuation_lt`) — but its height
is `H = fSum σ ≥ N`. -/
theorem stratumCount_ramShape_smallN {n : ℕ} {σ : FactorizationType} {T : ClusterShape}
    (hT : WildMenu.ramShape n σ = some T) {N : ℕ} (hN : N ≤ WildMenu.fSum σ) :
    M8.stratumCount (M9.rawCount n) T N = 0 := by
  have hc := WildMenu.constERam_of_ramShape hT
  have hn : 0 < n := WildMenu.constERam_n_pos hc
  rcases Nat.eq_zero_or_pos N with rfl | hNpos
  · exact RealInstanceV2.stratumCount_level0 n hn T
  · haveI : IsEmpty {f : QuotientBox.monicBox M9.realP N n // M9.realClassify n N f = T} := by
      constructor
      rintro ⟨f, hcl⟩
      have hcl' : B.classify M9.realP n N f = ClassifierBridgeFiber.Tselfloop n
          (((0, WildMenu.fSum σ), (n, 0)) : (ℕ × ℕ) × (ℕ × ℕ)) (WildMenu.wShape σ) := by
        rw [← WildMenu.ramShape_some_eq hT]
        exact hcl
      have hrs := ClassifierBridgeFiber2.rootSide_eq_of_classify hn hNpos f
        (WildMenu.wShape σ) hcl' (WildMenu.wShape_ne hc)
      have hverts := ClassifierBridgeFiber.npVertices_of_rootSide M9.realP hn hNpos f hrs
      have hmem0 : (((0 : ℕ), WildMenu.fSum σ) : ℕ × ℕ)
          ∈ NewtonPolygon.npVertices (B.boxValSupport M9.realP N f)
              (B.boxValSupport_nonempty M9.realP N hNpos f) := by
        rw [hverts]
        exact List.mem_cons_self ..
      have hS := ClassifierBridgeFiber.mem_S_of_mem_npVertices M9.realP f
        (B.boxValSupport_nonempty M9.realP N hNpos f) hmem0
      obtain ⟨hv, hne0⟩ := ClassifierBridgeFiber.boxValSupport_eq_dot M9.realP f hS
      -- hv : fSum σ = vOf realP f 0 = zmodValuation realP N (f.coeff 0), with coeff 0 ≠ 0
      have hlt : PadicLift.zmodValuation M9.realP N ((f.1).coeff 0) < N :=
        PadicLift.zmodValuation_lt M9.realP hNpos hne0
      have hv' : WildMenu.fSum σ = PadicLift.zmodValuation M9.realP N ((f.1).coeff 0) := hv
      omega
    change ((M9.rawCount n T N : ℕ) : ℚ) = 0
    rw [show M9.rawCount n T N = Nat.card {f : QuotientBox.monicBox M9.realP N n //
        M9.realClassify n N f = T} from rfl, Nat.card_of_isEmpty]
    norm_num

/-- **FULL monotonicity of the normalized union menu sum** (the `decided_mono` discharge for
the Wave-1 counting model). On the wild leg the normalized sequence is `0, …, 0, c, c, …`
(vanishing through level `fSum σ`, constant `c ≥ 0` from level `fSum σ + 1`); on the order-0
leg it is `0, c', c', …`. In both cases monotone — no small-N obstruction survives. -/
theorem normSum_omMenuW_mono (n : ℕ) (hn : 0 < n) (σ : FactorizationType) :
    Monotone (fun N => (∑ T ∈ WildMenu.omMenuW n σ, M8.stratumCount (M9.rawCount n) T N)
      / (M9.realP : ℚ) ^ (n * N)) := by
  intro N K hNK
  by_cases hc : WildMenu.constERam n σ
  · -- the wild singleton menu: 0, …, 0, c, c, …
    have hT := WildMenu.ramShape_of_constERam hc
    simp only [WildMenu.omMenuW_ram_of_constE hc, Finset.sum_singleton]
    rcases Nat.lt_or_ge (WildMenu.fSum σ) K with hK | hK
    · rcases Nat.lt_or_ge (WildMenu.fSum σ) N with hNgt | hNle
      · rw [normRamCount_levelConst hT (by omega : WildMenu.fSum σ + 1 ≤ N),
          normRamCount_levelConst hT (by omega : WildMenu.fSum σ + 1 ≤ K)]
      · rw [stratumCount_ramShape_smallN hT hNle, zero_div]
        exact div_nonneg (M8.stratumCount_nonneg _ _ _)
          (le_of_lt (RealInstanceV2.realP_pow_pos _))
    · rw [stratumCount_ramShape_smallN hT (hNK.trans hK),
        stratumCount_ramShape_smallN hT hK, zero_div, zero_div]
  · -- the order-0 menu: 0, c', c', …
    simp only [WildMenu.omMenuW_unram hc]
    rcases Nat.eq_zero_or_pos N with rfl | hNpos
    · rcases Nat.eq_zero_or_pos K with rfl | hKpos
      · exact le_refl _
      · calc (∑ T ∈ Order0.sepShapesOf n σ, M8.stratumCount (M9.rawCount n) T 0)
              / (M9.realP : ℚ) ^ (n * 0)
            ≤ (∑ T ∈ Order0.sepShapesOf n σ, M8.stratumCount (M9.rawCount n) T 1)
              / (M9.realP : ℚ) ^ (n * 1) :=
              RealInstanceV2Prep.normSum_sepShapesOf_zero_le n hn σ
          _ = (∑ T ∈ Order0.sepShapesOf n σ, M8.stratumCount (M9.rawCount n) T K)
              / (M9.realP : ℚ) ^ (n * K) :=
              (RealInstanceV2Prep.normSum_sepShapesOf_levelConst n hn σ K hKpos).symm
    · have hKpos : 0 < K := lt_of_lt_of_le hNpos hNK
      exact le_of_eq
        ((RealInstanceV2Prep.normSum_sepShapesOf_levelConst n hn σ N hNpos).trans
          (RealInstanceV2Prep.normSum_sepShapesOf_levelConst n hn σ K hKpos).symm)

/-! ## 4. Nonnegativity of the wild engine value at every natural `q'` -/

/-- The `configOf` reader emits no children on a `Tselfloop` shape (every payload cell is
childless). -/
private theorem children_configOf_Tselfloop_nil (n : ℕ) (pr : (ℕ × ℕ) × (ℕ × ℕ))
    (shape : List (ℕ × ℕ)) :
    (configOf (ClassifierBridgeFiber.Tselfloop n pr shape)).children = [] := by
  change (M7.cellsOfShapeWF (ClassifierBridgeFiber.Tselfloop n pr shape)).flatMap _ = []
  rw [ClassifierBridgeFiber.cellsOfShapeWF_Tselfloop]
  apply List.flatMap_eq_nil_iff.mpr
  intro c hc
  rw [List.mem_map] at hc
  obtain ⟨q, -, rfl⟩ := hc
  rfl

/-- The single face's `dF` on a `Tselfloop` shape is the residual degree sum `Σ dᵢ`. -/
private theorem faces_dF_configOf_Tselfloop (n : ℕ) (pr : (ℕ × ℕ) × (ℕ × ℕ))
    (shape : List (ℕ × ℕ)) :
    (((configOf (ClassifierBridgeFiber.Tselfloop n pr shape)).faces).map
        OMCountV2.FaceAssign.dF).sum = (shape.map Prod.fst).sum := by
  change ((M7.cellsOfShapeWF (ClassifierBridgeFiber.Tselfloop n pr shape)).map
      OMCountV2.cellResDeg).sum + 0 = (shape.map Prod.fst).sum
  rw [ClassifierBridgeFiber.cellsOfShapeWF_Tselfloop, List.map_map, Nat.add_zero]
  rfl

/-- The `mCell` of the `configOf` reader on a `Tselfloop` shape is the all-μ=1 face choice
polynomial evaluated at `q'^δ`. -/
private theorem mCell_configOf_Tselfloop (n : ℕ) (pr : (ℕ × ℕ) × (ℕ × ℕ))
    (shape : List (ℕ × ℕ)) (q' : ℕ) :
    mCell (configOf (ClassifierBridgeFiber.Tselfloop n pr shape)) q'
      = (choicePoly true ((shape.map Prod.fst).map (fun d => (d, 1)))).eval
          ((q' : ℚ) ^ Order0.nodeDelta
            (M7.cellsOfShapeWF (ClassifierBridgeFiber.Tselfloop n pr shape))) := by
  change ([(choicePoly true ((M7.cellsOfShapeWF
      (ClassifierBridgeFiber.Tselfloop n pr shape)).map
        (fun c => (c.dS, OMCountV2.cellMult c)))).eval
      ((q' : ℚ) ^ Order0.nodeDelta (M7.cellsOfShapeWF
        (ClassifierBridgeFiber.Tselfloop n pr shape)))]).prod = _
  rw [List.prod_singleton]
  congr 1
  rw [ClassifierBridgeFiber.cellsOfShapeWF_Tselfloop, List.map_map, List.map_map]
  rfl

/-- **The `Tselfloop` engine value is nonnegative at EVERY natural `q'`** (mirror of
`RealInstanceV2.omCount_sepShape_nonneg`): the value is
`(choice polynomial).eval(q'^δ) · (q'^volExp)⁻¹` — at `q' = 0` the volume factor vanishes
(`volExp ≥ Σ dᵢ ≥ 1`); at `q' ≥ 1` the choice polynomial is a product of falling factorials of
naturals. -/
theorem omCount_Tselfloop_nonneg (n H : ℕ) (shape : List (ℕ × ℕ))
    (hpos : ∀ q ∈ shape, 1 ≤ q.1) (hne : shape ≠ []) (q' : ℕ) :
    0 ≤ omCount (ClassifierBridgeFiber.Tselfloop n
      (((0, H), (n, 0)) : (ℕ × ℕ) × (ℕ × ℕ)) shape) q' := by
  -- the residual-degree sum is ≥ 1
  have hsum_pos : 1 ≤ (shape.map Prod.fst).sum := by
    cases shape with
    | nil => exact absurd rfl hne
    | cons q t =>
        have hq := hpos q (List.mem_cons_self ..)
        simp only [List.map_cons, List.sum_cons]
        omega
  -- the volume exponent is ≥ Σ dᵢ ≥ 1
  have hvol_pos : volExp (configOf (ClassifierBridgeFiber.Tselfloop n
      (((0, H), (n, 0)) : (ℕ × ℕ) × (ℕ × ℕ)) shape)) ≠ 0 := by
    have hdF := faces_dF_configOf_Tselfloop n (((0, H), (n, 0)) : (ℕ × ℕ) × (ℕ × ℕ)) shape
    rw [OMCountV2.volExp]
    omega
  -- reduce `omCount` to the single-configuration term (children collapse to `[]`)
  rw [OMCountV2.omCount]
  unfold OMCountV2.configsOf
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero,
    children_configOf_Tselfloop_nil, List.prod_nil, mul_one]
  rcases Nat.eq_zero_or_pos q' with rfl | hq'
  · -- `q' = 0`: the volume factor vanishes
    rw [show ((0 : ℕ) : ℚ) ^ volExp (configOf (ClassifierBridgeFiber.Tselfloop n
        (((0, H), (n, 0)) : (ℕ × ℕ) × (ℕ × ℕ)) shape)) = 0 from by
      rw [Nat.cast_zero]
      exact zero_pow hvol_pos]
    rw [inv_zero, mul_zero]
  · -- `q' ≥ 1`: choice polynomial ≥ 0, volume factor ≥ 0
    refine mul_nonneg ?_ (inv_nonneg.mpr (by positivity))
    rw [mCell_configOf_Tselfloop]
    have hcast : ((q' : ℚ)) ^ Order0.nodeDelta (M7.cellsOfShapeWF
        (ClassifierBridgeFiber.Tselfloop n
          (((0, H), (n, 0)) : (ℕ × ℕ) × (ℕ × ℕ)) shape))
        = (((q' ^ Order0.nodeDelta (M7.cellsOfShapeWF (ClassifierBridgeFiber.Tselfloop n
            (((0, H), (n, 0)) : (ℕ × ℕ) × (ℕ × ℕ)) shape)) : ℕ)) : ℚ) := by
      push_cast
      ring
    rw [hcast, OMCountV2.choicePoly_map_one, Polynomial.eval_prod]
    refine Finset.prod_nonneg fun d hd => ?_
    rw [Polynomial.eval_mul, Polynomial.eval_C]
    refine mul_nonneg (by positivity) ?_
    have hd1 : 1 ≤ d := by
      rw [List.mem_toFinset, List.mem_map] at hd
      obtain ⟨q, hq, rfl⟩ := hd
      exact hpos q hq
    exact RealInstanceV2.ffPoly_availPoly_eval_nonneg d ((shape.map Prod.fst).count d)
      _ hd1 (Nat.one_le_pow _ _ hq')

/-- Nonnegativity of the engine value on every `ramShape` output, at every natural `q'`
(the `density_nonneg` feed for the Wave-1 real foundation). -/
theorem omCount_ramShape_nonneg {n : ℕ} {σ : FactorizationType} {T : ClusterShape}
    (hT : WildMenu.ramShape n σ = some T) (q' : ℕ) :
    0 ≤ omCount T q' := by
  have hc := WildMenu.constERam_of_ramShape hT
  rw [WildMenu.ramShape_some_eq hT]
  exact omCount_Tselfloop_nonneg n (WildMenu.fSum σ) (WildMenu.wShape σ)
    (WildMenu.wShape_pos hc) (WildMenu.wShape_ne hc) q'

end LeanUrat.OM.WildMenuPrep
