/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.OM.ChainMenuU

/-!
# UniformModelN2 — Wave W6q-b: the general-`p` full counting model and cluster covering (`n = 2`)

**Provenance.** `notes/WILD_WAVE6Q_BLUEPRINT_2026-07-22.md` §1.1 (the five-family stratum
table), §2-W6q-b; ground truth `notes/MATH_FULLTYPE_DECOMPOSITION_2026-07-22.md` (ACCEPTED).
This module is the general-`p` analogue of `OM/SeriesAssembly.lean` §§C–G+I (the W6 `p = 2`
model), built PURELY ADDITIVELY on `OM/ChainMenuU.lean` (W6q-a) and the banked
`ChainMenu`/`RecenterBox` engine. `SeriesAssembly` is NOT imported (cone kept light); its
`p = 2` recovery tie lives in `OM/UniformModelN2Recovery.lean`.

## The model (blueprint §1.1 table ↔ this module's counts)

At level `N` on the coefficient box `pairBoxP p N` (monic quadratics `x² + a₁x + a₀` mod
`p^N` via `coeffEquiv`), the DECIDED count of type σ is `decidedCountP p σ N` =
`ord0Count + chainCountP`, whose fibers realize the blueprint's five families:

* **order-0 split / inert cells** (`Ord0SplitCell`/`Ord0InertCell`, from W6q-a): residual
  shape two-distinct-roots / root-free — `ord0Count`;
* at EVERY residue point `c ∈ F_p` (`Finset.range p`, translate `transMapP c` =
  `RecenterBox.affineEquiv`), all depth-`k ≥ 0` descend chains (`ms` prefix = the table's
  descend rows) ending in
  - the **ram H** rows (`ChainLeaf.ram`, keyed `{(2,1)}`),
  - the **inert m** rows (`ChainLeaf.inert`, keyed `{(1,2)}`),
  - the **two-sided split k** rows (`ChainLeaf.split`, keyed `{(1,1),(1,1)}`)
  — together `chainCountMain` (σ-keyed via `chainLeaves`), and
  - the **splitU m** rows (`ChainPairU`, keyed `{(1,1),(1,1)}`, NEW at `q > 2`) —
  `chainCountUTot`, keyed to `splitType2` inside `chainCountP`.

`undecidedCountP` is the box residual; `decided_add_undecided` is the definitional per-level
count identity.

## The coverings (the wave's hardest items)

* `cluster_coveringP` — the general-`p` transcription of W6's `cluster_covering`: every
  cluster pair either realizes a terminating chain stratum within budget — the FOUR leaf
  kinds, with the height-`2m` residual read classified by the banked `ChainMenuU`
  trichotomy `cover_of_fst_ne_zero` (root-free → inert; two-distinct-nonzero → splitU;
  unit square → descend) instead of W6's `F₂` digit dichotomy — or lies in a `StallPairP`
  stall stratum (`v(b₀) ≥ B − 1` containment). Strong induction on the budget. THE PARITY
  DISCIPLINE (blueprint §1.1 sanity note): no `p` odd/even case split anywhere — the
  square-residual classification is `StratumPair`'s digit form via the banked pools.
* `box_coveringP` — the order-0 layer: every box pair is order-0 decided or lies in the
  cluster at the ONE residue point named by its square residual (`cover_all` +
  `transMapP_cluster_iff`); `cross_cluster_conflictP` — distinct residue points have
  DISJOINT clusters (residual-center uniqueness of a square, `square_map_injective`).

## Disjointness (no double-counting)

All counted fibers are pairwise disjoint: `transFiber_pairwise_disjoint` (distinct
`(c, family, parameters)` chain fibers conflict — same-`c` via the digit-ledger bank
extended with the splitU cases `leafPairU_*_disjoint`/`chainPairU_disjoint`/
`chainPair_chainPairU_disjoint`; cross-`c` via `cross_cluster_conflictP`), and the order-0
cells conflict with each other and with every cluster (`ord0Split_not_cluster` etc. via the
banked pool disjointness). Consequence: `sum_decidedP_le_box` and `undecidedP_nonneg`.

## Honest scope

Counting-side only: the fibers are digit-condition fibers; σ-keying faithfulness is W6q-d's
business. No `sorry`, no axiom; core-only footprint (`AxCheck`).
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1600000

namespace LeanUrat.OM.UniformModelN2

open scoped Classical
open LeanUrat LeanUrat.OM Finset
open LeanUrat.OM.QuotientBox LeanUrat.OM.CellCard
open LeanUrat.OM.RestartEquiv
open LeanUrat.OM.RecenterBox
open LeanUrat.OM.ChainMenu
open LeanUrat.OM.ChainMenuU

variable (p : ℕ) [hp : Fact p.Prime]

/-! ## 1. The box and the residue-point translates (general-`p` W6 §E) -/

/-- The coefficient-pair box at level `N` (via `coeffEquiv`, = the monic quadratic box). -/
abbrev pairBoxP (N : ℕ) : Type := ZMod (p ^ N) × ZMod (p ^ N)

/-- The residue-point translate on the coefficient pair: `f(x) ↦ f(x + ĉ)` reads
`(a₀, a₁) ↦ (a₀ + ĉa₁ + ĉ², a₁ + 2ĉ)` — exactly `RecenterBox.affineEquiv` at levels `(N, N)`
(the W6 `transMap` at general `p`). -/
noncomputable def transMapP (c N : ℕ) : pairBoxP p N ≃ pairBoxP p N :=
  affineEquiv p N N le_rfl c

theorem transMapP_zero (N : ℕ) (a : pairBoxP p N) : transMapP p 0 N a = a := by
  unfold transMapP affineEquiv
  refine Prod.ext ?_ ?_
  · dsimp only [Equiv.coe_fn_mk]
    push_cast
    ring
  · dsimp only [Equiv.coe_fn_mk]
    push_cast
    ring

/-- Counts compose through an equivalence (the W6 3-line count-composition pattern). -/
theorem card_comp_equiv {α β : Type*} (e : α ≃ β) (Q : β → Prop) :
    Nat.card {a : α // Q (e a)} = Nat.card {b : β // Q b} :=
  Nat.card_congr (e.subtypeEquiv (fun _ => Iff.rfl))

/-! ## 2. The mod-`p` residual read of a translate, and the cluster ⟺ square-residual tie -/

/-- The height-0 digit IS the mod-`p` residue `resp`. -/
theorem digit_zero_eq_resp {N : ℕ} (x : ZMod (p ^ N)) : digit p N 0 x = resp p N x := by
  show ((x.val / p ^ 0 : ℕ) : ZMod p) = ((x.val : ℕ) : ZMod p)
  rw [pow_zero, Nat.div_one]

/-- The residual read of the translated constant coefficient:
`resp((transMapP c a).1) = ā₀ + c̄ā₁ + c̄²`. -/
theorem resp_transMapP_fst {N : ℕ} (hN : 0 < N) (c : ℕ) (a : pairBoxP p N) :
    resp p N (transMapP p c N a).1
      = resp p N a.1 + (c : ZMod p) * resp p N a.2 + (c : ZMod p) ^ 2 := by
  show resp p N (a.1
      + (c : ZMod (p ^ N)) * (ZMod.castHom (pow_dvd_pow p (le_refl N)) (ZMod (p ^ N)) a.2)
      + (c : ZMod (p ^ N)) ^ 2) = _
  rw [resp_add p N hN, resp_add p N hN, resp_mul p N hN, resp_pow p N hN,
    resp_natCast p N hN, resp_castHom p hN le_rfl]

/-- The residual read of the translated linear coefficient:
`resp((transMapP c a).2) = ā₁ + 2c̄`. -/
theorem resp_transMapP_snd {N : ℕ} (hN : 0 < N) (c : ℕ) (a : pairBoxP p N) :
    resp p N (transMapP p c N a).2 = resp p N a.2 + 2 * (c : ZMod p) := by
  show resp p N (a.2 + 2 * (c : ZMod (p ^ N))) = _
  have hprod : (2 : ZMod (p ^ N)) * ((c : ℕ) : ZMod (p ^ N))
      = ((2 * c : ℕ) : ZMod (p ^ N)) := by push_cast; ring
  rw [resp_add p N hN, hprod, resp_natCast p N hN]
  push_cast
  ring

/-- **The cluster ⟺ square-residual tie**: the `c`-translate of `a` lies in the cluster locus
iff the residual pair of `a` is EXACTLY the square shape `(c̄², −2c̄)` — the residual-center
read that drives both coverings and the cross-translate conflict. Uniform in `p`. -/
theorem transMapP_cluster_iff {N : ℕ} (hN : 0 < N) (c : ℕ) (a : pairBoxP p N) :
    ClusterPair p N N (transMapP p c N a)
      ↔ (resp p N a.1 = (c : ZMod p) ^ 2 ∧ resp p N a.2 = -(2 * (c : ZMod p))) := by
  constructor
  · rintro ⟨h1, h2⟩
    rw [← resp_eq_zero_iff_dvd_val] at h1 h2
    rw [resp_transMapP_fst p hN c a] at h1
    rw [resp_transMapP_snd p hN c a] at h2
    have hb : resp p N a.2 = -(2 * (c : ZMod p)) := by linear_combination h2
    exact ⟨by linear_combination h1 - (c : ZMod p) * hb, hb⟩
  · rintro ⟨h1, h2⟩
    refine ⟨?_, ?_⟩
    · rw [← resp_eq_zero_iff_dvd_val, resp_transMapP_fst p hN c a, h1, h2]
      ring
    · rw [← resp_eq_zero_iff_dvd_val, resp_transMapP_snd p hN c a, h2]
      ring

/-- **The cross-translate cluster conflict** (general-`p` `cross_cluster_conflict`): distinct
residue points `c ≠ c' < p` have DISJOINT cluster fibers — a square residual has a UNIQUE
center (`square_map_injective`). -/
theorem cross_cluster_conflictP {N : ℕ} (hN : 0 < N) {c c' : ℕ} (hc : c < p) (hc' : c' < p)
    (hne : c ≠ c') {a : pairBoxP p N}
    (h : ClusterPair p N N (transMapP p c N a))
    (h' : ClusterPair p N N (transMapP p c' N a)) : False := by
  haveI : NeZero p := ⟨hp.out.ne_zero⟩
  obtain ⟨h1, h2⟩ := (transMapP_cluster_iff p hN c a).mp h
  obtain ⟨h1', h2'⟩ := (transMapP_cluster_iff p hN c' a).mp h'
  have hpair : ((c : ZMod p) ^ 2, -(2 * (c : ZMod p)))
      = ((c' : ZMod p) ^ 2, -(2 * (c' : ZMod p))) := by
    rw [← h1, ← h2, ← h1', ← h2']
  have hcc : ((c : ZMod p)) = ((c' : ZMod p)) := square_map_injective p hpair
  refine hne ?_
  calc c = ((c : ZMod p)).val := (ZMod.val_cast_of_lt hc).symm
    _ = ((c' : ZMod p)).val := by rw [hcc]
    _ = c' := ZMod.val_cast_of_lt hc'

/-- **The square-residual locus** at level `N`: the height-0 residual pair is a square
`(c̄², −2c̄)` for SOME center — the order-0 cluster locus, i.e. the complement of the two
order-0 decided cells (`cover_all` + pool disjointness). -/
def SqResLocus (N : ℕ) (a : pairBoxP p N) : Prop :=
  (digit p N 0 a.1, digit p N 0 a.2) ∈ squareAllPairs p

/-- Any translate's cluster fiber lies in the square-residual locus. -/
theorem sqResLocus_of_cluster {N : ℕ} (hN : 0 < N) {c : ℕ} {a : pairBoxP p N}
    (h : ClusterPair p N N (transMapP p c N a)) : SqResLocus p N a := by
  obtain ⟨h1, h2⟩ := (transMapP_cluster_iff p hN c a).mp h
  refine (mem_squareAllPairs p).mpr ⟨(c : ZMod p), ?_, ?_⟩
  · show digit p N 0 a.1 = (c : ZMod p) ^ 2
    rw [digit_zero_eq_resp]
    exact h1
  · show digit p N 0 a.2 = -(2 * (c : ZMod p))
    rw [digit_zero_eq_resp]
    exact h2

/-- The square-residual locus count: `p · p^{2(N−1)}` (pool `p` × free tails). -/
theorem card_sqResLocus (N : ℕ) (hN : 0 < N) :
    Nat.card {a : pairBoxP p N // SqResLocus p N a}
      = p * (p ^ (N - 1) * p ^ (N - 1)) := by
  have e : {a : pairBoxP p N // SqResLocus p N a}
      ≃ {a : pairBoxP p N //
          p ^ 0 ∣ a.1.val ∧ p ^ 0 ∣ a.2.val
            ∧ (digit p N 0 a.1, digit p N 0 a.2) ∈ squareAllPairs p} :=
    Equiv.subtypeEquivRight (fun a =>
      ⟨fun h => ⟨by rw [pow_zero]; exact one_dvd _, by rw [pow_zero]; exact one_dvd _, h⟩,
       fun h => h.2.2⟩)
  rw [Nat.card_congr e]
  have h := card_pair_digitSet p (show 0 < N by omega) (show 0 < N by omega) (squareAllPairs p)
  simp only [Nat.sub_zero] at h
  rw [h, card_squareAllPairs p]

/-! ## 3. The stall strata and the translated fibers (general-`p` W6 §C/§E) -/

/-- **The stall stratum** (general-`p` W6 `StallPair`, same recursion): a certified descend
chain prefix, then `v(b₀) ≥ B − 1` in the bottom frame (`B = L₀ − 2Σm` the remaining budget)
— the note's (3f) stall containment. -/
def StallPairP : List ℕ → (L₀ L₁ : ℕ) → ZMod (p ^ L₀) × ZMod (p ^ L₁) → Prop
  | [], L₀, _, a => ClusterPair p L₀ _ a ∧ p ^ (L₀ - 1) ∣ a.1.val
  | m :: ms, L₀, L₁, a =>
      ∃ c : (ZMod p)ˣ, StratumPair p L₀ L₁ m c a ∧
        StallPairP ms (L₀ - 2 * m) (L₁ - m) (descendPair p m ((c : ZMod p)).val a)

/-- Stall strata subsume the cluster condition. -/
theorem clusterPair_of_stallPairP (ms : List ℕ) (hms : ∀ m ∈ ms, 1 ≤ m) {L₀ L₁ : ℕ}
    {a : ZMod (p ^ L₀) × ZMod (p ^ L₁)} (h : StallPairP p ms L₀ L₁ a) :
    ClusterPair p L₀ L₁ a := by
  cases ms with
  | nil => exact h.1
  | cons m ms =>
      obtain ⟨c, hstep, -⟩ := h
      exact clusterPair_of_stratumPair p L₀ L₁ m (hms m List.mem_cons_self) c a hstep

/-- The translated main-chain fiber (the W6 `TransChain` at general `p`). -/
def TransChainP (c : ℕ) (ms : List ℕ) (leaf : ChainLeaf) (N : ℕ) (a : pairBoxP p N) : Prop :=
  ChainPair p ms leaf N N (transMapP p c N a)

/-- The translated splitU-chain fiber (the NEW family, W6q-a's `ChainPairU`). -/
def TransChainU (c : ℕ) (ms : List ℕ) (m : ℕ) (N : ℕ) (a : pairBoxP p N) : Prop :=
  ChainPairU p ms m N N (transMapP p c N a)

/-- The translated stall fiber. -/
def TransStallP (c : ℕ) (ms : List ℕ) (N : ℕ) (a : pairBoxP p N) : Prop :=
  StallPairP p ms N N (transMapP p c N a)

noncomputable def transChainCountP (c : ℕ) (ms : List ℕ) (leaf : ChainLeaf) (N : ℕ) : ℕ :=
  Nat.card {a : pairBoxP p N // TransChainP p c ms leaf N a}

noncomputable def transChainCountU (c : ℕ) (ms : List ℕ) (m : ℕ) (N : ℕ) : ℕ :=
  Nat.card {a : pairBoxP p N // TransChainU p c ms m N a}

noncomputable def transStallCountP (c : ℕ) (ms : List ℕ) (N : ℕ) : ℕ :=
  Nat.card {a : pairBoxP p N // TransStallP p c ms N a}

/-- **The translate count tie** (main chains): translation is count-exact — every translated
chain fiber has the un-translated pair-frame count (mirrors W6 `transChainCount_eq_pair`). -/
theorem transChainCountP_eq_pair (c : ℕ) (ms : List ℕ) (leaf : ChainLeaf) (N : ℕ) :
    transChainCountP p c ms leaf N
      = Nat.card {a : pairBoxP p N // ChainPair p ms leaf N N a} :=
  card_comp_equiv (transMapP p c N) _

/-- The translate count tie, splitU chains. -/
theorem transChainCountU_eq_pair (c : ℕ) (ms : List ℕ) (m : ℕ) (N : ℕ) :
    transChainCountU p c ms m N
      = Nat.card {a : pairBoxP p N // ChainPairU p ms m N N a} :=
  card_comp_equiv (transMapP p c N) _

/-- The translate count tie, stalls. -/
theorem transStallCountP_eq_pair (c : ℕ) (ms : List ℕ) (N : ℕ) :
    transStallCountP p c ms N
      = Nat.card {a : pairBoxP p N // StallPairP p ms N N a} :=
  card_comp_equiv (transMapP p c N) _

/-! ## 4. The model counts (general-`p` W6 §G, four families) -/

/-- The three degree-2 types are pairwise distinct. -/
theorem ram_ne_inert : ramType2 ≠ inertType2 := by
  intro h
  have := congrArg (fun σ => σ.data) h
  exact absurd this (by decide)

theorem ram_ne_split : ramType2 ≠ splitType2 := by
  intro h
  have := congrArg (fun σ => σ.data) h
  exact absurd this (by decide)

theorem inert_ne_split : inertType2 ≠ splitType2 := by
  intro h
  have := congrArg (fun σ => σ.data) h
  exact absurd this (by decide)

/-- The order-0 contribution, keyed by type (blueprint §1.1 order-0 cells; ram gets none). -/
noncomputable def ord0Count (σ : FactorizationType) (N : ℕ) : ℚ :=
  if σ = splitType2 then (Nat.card {a : pairBoxP p N // Ord0SplitCell p N a} : ℚ)
  else if σ = inertType2 then (Nat.card {a : pairBoxP p N // Ord0InertCell p N a} : ℚ)
  else 0

/-- The σ-keyed main-chain contribution: ALL `p` residue points × the level-`N` rectangle of
descend prefixes (`msMenu N N`) × σ's leaf menu (`chainLeaves N σ`: ram H / inert m /
two-sided split k — three of the blueprint §1.1 table's five families; below-threshold
strata have empty fibers, so the rectangle over-indexes harmlessly). -/
noncomputable def chainCountMain (σ : FactorizationType) (N : ℕ) : ℚ :=
  ∑ c ∈ Finset.range p, ∑ x ∈ msMenu N N ×ˢ chainLeaves N σ,
    ((transChainCountP p c x.1 x.2 N : ℕ) : ℚ)

/-- The splitU-family contribution: ALL `p` residue points × descend prefixes × splitU
heights `m ∈ [1, N]` (the blueprint's NEW `q > 2` family; honestly empty at `p = 2`). -/
noncomputable def chainCountUTot (N : ℕ) : ℚ :=
  ∑ c ∈ Finset.range p, ∑ x ∈ msMenu N N ×ˢ Finset.Icc 1 N,
    ((transChainCountU p c x.1 x.2 N : ℕ) : ℚ)

/-- **The per-type chain contribution** = the four chain families of blueprint §1.1, keyed:
`chainCountMain` carries ram/inert/two-sided-split through `chainLeaves N σ`; the splitU
family (leaf `{(1,1),(1,1)}`) is keyed to `splitType2`. The DECIDED count below is thus
exactly the sum of all four families over all `p` residue points, plus order-0. -/
noncomputable def chainCountP (σ : FactorizationType) (N : ℕ) : ℚ :=
  chainCountMain p σ N + if σ = splitType2 then chainCountUTot p N else 0

/-- **The full-model per-type decided count** (general-`p` `decidedCount6`). -/
noncomputable def decidedCountP (σ : FactorizationType) (N : ℕ) : ℚ :=
  ord0Count p σ N + chainCountP p σ N

/-- The degree-2 type menu. -/
noncomputable def typeMenuP : Finset FactorizationType := {ramType2, inertType2, splitType2}

/-- **The full-model undecided count** (the box residual). -/
noncomputable def undecidedCountP (N : ℕ) : ℚ :=
  (p : ℚ) ^ (2 * N) - ∑ σ ∈ typeMenuP, decidedCountP p σ N

theorem sum_typeMenuP (f : FactorizationType → ℚ) :
    ∑ σ ∈ typeMenuP, f σ = f ramType2 + f inertType2 + f splitType2 := by
  unfold typeMenuP
  rw [Finset.sum_insert (by
    simp only [Finset.mem_insert, Finset.mem_singleton]
    rintro (h | h)
    · exact ram_ne_inert h
    · exact ram_ne_split h)]
  rw [Finset.sum_insert (by
    simp only [Finset.mem_singleton]
    exact inert_ne_split)]
  rw [Finset.sum_singleton]
  ring

theorem ord0Count_nonneg (σ : FactorizationType) (N : ℕ) : 0 ≤ ord0Count p σ N := by
  unfold ord0Count
  split
  · exact Nat.cast_nonneg _
  · split
    · exact Nat.cast_nonneg _
    · exact le_refl 0

theorem chainCountMain_nonneg (σ : FactorizationType) (N : ℕ) : 0 ≤ chainCountMain p σ N :=
  Finset.sum_nonneg fun _c _ => Finset.sum_nonneg fun _x _ => Nat.cast_nonneg _

theorem chainCountUTot_nonneg (N : ℕ) : 0 ≤ chainCountUTot p N :=
  Finset.sum_nonneg fun _c _ => Finset.sum_nonneg fun _x _ => Nat.cast_nonneg _

theorem chainCountP_nonneg (σ : FactorizationType) (N : ℕ) : 0 ≤ chainCountP p σ N := by
  unfold chainCountP
  have h1 := chainCountMain_nonneg p σ N
  split
  · have h2 := chainCountUTot_nonneg p N
    linarith
  · linarith

theorem decidedCountP_nonneg (σ : FactorizationType) (N : ℕ) : 0 ≤ decidedCountP p σ N :=
  add_nonneg (ord0Count_nonneg p σ N) (chainCountP_nonneg p σ N)

/-- **The per-level count identity** (definitional): decided + undecided = box. -/
theorem decided_add_undecided (N : ℕ) :
    ∑ σ ∈ typeMenuP, decidedCountP p σ N + undecidedCountP p N = (p : ℚ) ^ (2 * N) := by
  unfold undecidedCountP
  ring

/-! ### Level-0 vanishing -/

theorem digit_zero_level_zero (x : ZMod (p ^ 0)) : digit p 0 0 x = 0 := by
  haveI : NeZero (p ^ 0) := QuotientBox.instNeZeroPow p 0
  have hval : x.val = 0 := by
    have h := ZMod.val_lt x
    have h1 : p ^ 0 = 1 := pow_zero p
    omega
  show ((x.val / p ^ 0 : ℕ) : ZMod p) = 0
  rw [hval, Nat.zero_div, Nat.cast_zero]

theorem ord0Split_zero_empty (a : pairBoxP p 0) : ¬ Ord0SplitCell p 0 a := by
  intro h
  refine splitResPairs_not_squareAll p h 0 ⟨?_, ?_⟩
  · show digit p 0 0 a.1 = (0 : ZMod p) ^ 2
    rw [digit_zero_level_zero p a.1]
    ring
  · show digit p 0 0 a.2 = -(2 * (0 : ZMod p))
    rw [digit_zero_level_zero p a.2]
    ring

theorem ord0Inert_zero_empty (a : pairBoxP p 0) : ¬ Ord0InertCell p 0 a := fun h =>
  noRootPairs_fst_ne_zero p h (digit_zero_level_zero p a.1)

theorem chainLeaves_zero (σ : FactorizationType) : chainLeaves 0 σ = ∅ := by
  have hIcc : Finset.Icc 1 0 = (∅ : Finset ℕ) := Finset.Icc_eq_empty (by omega)
  unfold chainLeaves
  split_ifs <;> simp [hIcc]

/-- Everything vanishes at level `0` (trivial box: thresholds unreachable). -/
theorem decidedCountP_zero (σ : FactorizationType) : decidedCountP p σ 0 = 0 := by
  unfold decidedCountP
  have hord : ord0Count p σ 0 = 0 := by
    unfold ord0Count
    have h1 : Nat.card {a : pairBoxP p 0 // Ord0SplitCell p 0 a} = 0 := by
      haveI : IsEmpty {a : pairBoxP p 0 // Ord0SplitCell p 0 a} :=
        ⟨fun x => ord0Split_zero_empty p x.1 x.2⟩
      exact Nat.card_of_isEmpty
    have h2 : Nat.card {a : pairBoxP p 0 // Ord0InertCell p 0 a} = 0 := by
      haveI : IsEmpty {a : pairBoxP p 0 // Ord0InertCell p 0 a} :=
        ⟨fun x => ord0Inert_zero_empty p x.1 x.2⟩
      exact Nat.card_of_isEmpty
    rw [h1, h2]
    split_ifs <;> simp
  have hmain : chainCountMain p σ 0 = 0 := by
    unfold chainCountMain
    rw [chainLeaves_zero, Finset.product_empty]
    simp
  have hU : chainCountUTot p 0 = 0 := by
    unfold chainCountUTot
    rw [Finset.Icc_eq_empty (by omega), Finset.product_empty]
    simp
  unfold chainCountP
  rw [hord, hmain, hU]
  split_ifs <;> ring

/-! ## 5. THE CLUSTER COVERING (general-`p` W6 §D; blueprint §2-W6q-b)

The decision tree at a cluster frame: if the last budget digit of `b₀` is unreadable →
stall. Else read `v₀ = v(b₀)`. Odd `v₀` with deep `b₁` → ram leaf; shallow `b₁` (either
parity of `v₀`) → two-sided split leaf; even `v₀ = 2m` with deep `b₁` → classify the
height-`2m` residual pair by the banked `cover_of_fst_ne_zero` trichotomy: root-free →
inert leaf / two-distinct-nonzero-roots → splitU leaf / unit square `(c̃², −2c̃)` → descend
one step (`StratumPair` holds LITERALLY, no parity case) and recurse on the child budget. -/

/-- **The cluster covering**: a cluster pair realizes a main-chain stratum within budget, a
splitU-chain stratum within budget, or a stall stratum with certified steps. Strong
induction on the budget; the W6 proof shape with the residual classification swapped to the
general-`p` trichotomy. -/
theorem cluster_coveringP :
    ∀ L₀ L₁ : ℕ, L₀ ≤ L₁ →
    ∀ a : ZMod (p ^ L₀) × ZMod (p ^ L₁),
      ClusterPair p L₀ L₁ a →
      (∃ ms leaf, (∀ m ∈ ms, 1 ≤ m) ∧ leafOK leaf ∧
        2 * ms.sum + leafNeed leaf ≤ L₀ ∧ ChainPair p ms leaf L₀ L₁ a)
      ∨ (∃ ms m, (∀ x ∈ ms, 1 ≤ x) ∧ 1 ≤ m ∧
          2 * ms.sum + leafNeedU m ≤ L₀ ∧ ChainPairU p ms m L₀ L₁ a)
      ∨ (∃ ms, (∀ m ∈ ms, 1 ≤ m) ∧ (ms ≠ [] → 2 * ms.sum + 2 ≤ L₀) ∧
          StallPairP p ms L₀ L₁ a) := by
  intro L₀
  induction L₀ using Nat.strong_induction_on with
  | _ L₀ ih =>
  intro L₁ h01 a hCl
  by_cases hstall : p ^ (L₀ - 1) ∣ a.1.val
  · exact Or.inr (Or.inr ⟨[], fun m hm => absurd hm List.not_mem_nil,
      fun h => absurd rfl h, hCl, hstall⟩)
  · have hL₀2 : 2 ≤ L₀ := by
      by_contra hc
      exact hstall (by
        rw [show L₀ - 1 = 0 by omega, pow_zero]
        exact one_dvd _)
    set v₀ := PadicLift.zmodValuation p L₀ a.1 with hv₀def
    have hv₀le : v₀ ≤ L₀ - 2 := by
      by_contra hc
      exact hstall ((pow_dvd_val_iff p (by omega : L₀ - 1 ≤ L₀) a.1).mpr (by omega))
    have hdvd₀ : p ^ v₀ ∣ a.1.val :=
      (pow_dvd_val_iff p (by omega : v₀ ≤ L₀) a.1).mpr le_rfl
    have hdig₀ : digit p L₀ v₀ a.1 ≠ 0 :=
      (valuation_eq_iff_digit_ne p (by omega : v₀ < L₀) hdvd₀).mp hv₀def.symm
    have hv₀1 : 1 ≤ v₀ := by
      have h1 := (pow_dvd_val_iff p (by omega : 1 ≤ L₀) a.1).mp (by
        rw [pow_one]
        exact hCl.1)
      omega
    rcases Nat.even_or_odd v₀ with heven | hodd
    · -- even height `v₀ = 2m`: one-sided integer-slope read
      obtain ⟨m, hm⟩ := heven
      have hm2 : v₀ = 2 * m := by omega
      have hm1 : 1 ≤ m := by omega
      by_cases hb : p ^ m ∣ a.2.val
      · -- deep `b₁`: classify the height-`2m` residual pair (THE trichotomy)
        have hdig₀' : digit p L₀ (2 * m) a.1 ≠ 0 := by
          rw [← hm2]
          exact hdig₀
        have hdvd₀' : p ^ (2 * m) ∣ a.1.val := by
          rw [← hm2]
          exact hdvd₀
        rcases cover_of_fst_ne_zero p
            (s := (digit p L₀ (2 * m) a.1, digit p L₁ m a.2)) hdig₀' with hnr | hru | hsq
        · -- INERT leaf at height `2m` (residual root-free)
          refine Or.inl ⟨[], ChainLeaf.inert m, fun x hx => absurd hx List.not_mem_nil,
            hm1, ?_, ?_⟩
          · show 2 * List.sum [] + leafNeed (ChainLeaf.inert m) ≤ L₀
            simp only [List.sum_nil, leafNeed]
            omega
          · exact ⟨hdvd₀', hb, hnr⟩
        · -- SPLITU leaf at height `2m` (residual two distinct nonzero roots — NEW family)
          refine Or.inr (Or.inl ⟨[], m, fun x hx => absurd hx List.not_mem_nil,
            hm1, ?_, ?_⟩)
          · show 2 * List.sum [] + leafNeedU m ≤ L₀
            simp only [List.sum_nil, leafNeedU]
            omega
          · exact ⟨hdvd₀', hb, hru⟩
        · -- DESCEND at slope `m` (residual a UNIT square `(c̃², −2c̃)`; no parity case)
          obtain ⟨c, h1, h2⟩ := (mem_squareUnitPairs p).mp hsq
          have hstr : StratumPair p L₀ L₁ m c a := ⟨⟨hdvd₀', h1⟩, hb, h2⟩
          have h₀ : 2 * m + 1 ≤ L₀ := by omega
          have hchildCl : ClusterPair p (L₀ - 2 * m) (L₁ - m)
              (descendPair p m (((c : ZMod p)).val) a) := by
            rw [descendPair_eq_stratumPairEquiv p L₀ L₁ m c h₀ h01 ⟨a, hstr⟩]
            exact ((stratumPairEquiv p L₀ L₁ m c h₀ h01) ⟨a, hstr⟩).2
          rcases ih (L₀ - 2 * m) (by omega) (L₁ - m) (by omega) _ hchildCl with
            ⟨ms', leaf, hms', hOK, hth, hcp⟩ | ⟨ms', m', hms', hm', hth, hcp⟩ |
            ⟨ms', hms', hbud, hsp⟩
          · refine Or.inl ⟨m :: ms', leaf, ?_, hOK, ?_, ⟨c, hstr, hcp⟩⟩
            · intro x hx
              rcases List.mem_cons.mp hx with rfl | hx'
              · omega
              · exact hms' x hx'
            · rw [List.sum_cons]
              omega
          · refine Or.inr (Or.inl ⟨m :: ms', m', ?_, hm', ?_, ⟨c, hstr, hcp⟩⟩)
            · intro x hx
              rcases List.mem_cons.mp hx with rfl | hx'
              · omega
              · exact hms' x hx'
            · rw [List.sum_cons]
              omega
          · refine Or.inr (Or.inr ⟨m :: ms', ?_, ?_, ⟨c, hstr, hsp⟩⟩)
            · intro x hx
              rcases List.mem_cons.mp hx with rfl | hx'
              · omega
              · exact hms' x hx'
            · intro _
              rw [List.sum_cons]
              by_cases hnil : ms' = []
              · subst hnil
                simp only [List.sum_nil]
                omega
              · have := hbud hnil
                omega
      · -- `v(b₁) < m`: two-sided polygon, SPLIT leaf at `k = v(b₁)`
        set v₁ := PadicLift.zmodValuation p L₁ a.2 with hv₁def
        have hv₁lt : v₁ < m := by
          by_contra hc
          exact hb ((pow_dvd_val_iff p (by omega : m ≤ L₁) a.2).mpr (by omega))
        have hdvd₁ : p ^ v₁ ∣ a.2.val :=
          (pow_dvd_val_iff p (by omega : v₁ ≤ L₁) a.2).mpr le_rfl
        have hdig₁ : digit p L₁ v₁ a.2 ≠ 0 :=
          (valuation_eq_iff_digit_ne p (by omega : v₁ < L₁) hdvd₁).mp hv₁def.symm
        have hv₁1 : 1 ≤ v₁ := by
          have h1 := (pow_dvd_val_iff p (by omega : 1 ≤ L₁) a.2).mp (by
            rw [pow_one]
            exact hCl.2)
          omega
        refine Or.inl ⟨[], ChainLeaf.split v₁, fun x hx => absurd hx List.not_mem_nil,
          hv₁1, ?_, ?_⟩
        · show 2 * List.sum [] + leafNeed (ChainLeaf.split v₁) ≤ L₀
          simp only [List.sum_nil, leafNeed]
          omega
        · show LeafPair p (ChainLeaf.split v₁) L₀ L₁ a
          exact ⟨by omega,
            dvd_trans (pow_dvd_pow p (by omega : 2 * v₁ + 1 ≤ v₀)) hdvd₀,
            hdvd₁, hdig₁⟩
    · -- odd height `v₀ = 2t + 1`
      obtain ⟨t, ht⟩ := hodd
      by_cases hb : p ^ ((v₀ + 1) / 2) ∣ a.2.val
      · -- RAM leaf at `H = v₀`
        refine Or.inl ⟨[], ChainLeaf.ram v₀, fun x hx => absurd hx List.not_mem_nil,
          ⟨⟨t, by omega⟩, hv₀1⟩, ?_, ⟨⟨hdvd₀, hdig₀⟩, hb⟩⟩
        show 2 * List.sum [] + leafNeed (ChainLeaf.ram v₀) ≤ L₀
        simp only [List.sum_nil, leafNeed]
        omega
      · -- `2·v(b₁) < v₀ + 1`: two-sided, SPLIT leaf at `k = v(b₁)`
        set v₁ := PadicLift.zmodValuation p L₁ a.2 with hv₁def
        have hv₁lt : v₁ < (v₀ + 1) / 2 := by
          by_contra hc
          exact hb ((pow_dvd_val_iff p (by omega : (v₀ + 1) / 2 ≤ L₁) a.2).mpr
            (by omega))
        have hdvd₁ : p ^ v₁ ∣ a.2.val :=
          (pow_dvd_val_iff p (by omega : v₁ ≤ L₁) a.2).mpr le_rfl
        have hdig₁ : digit p L₁ v₁ a.2 ≠ 0 :=
          (valuation_eq_iff_digit_ne p (by omega : v₁ < L₁) hdvd₁).mp hv₁def.symm
        have hv₁1 : 1 ≤ v₁ := by
          have h1 := (pow_dvd_val_iff p (by omega : 1 ≤ L₁) a.2).mp (by
            rw [pow_one]
            exact hCl.2)
          omega
        refine Or.inl ⟨[], ChainLeaf.split v₁, fun x hx => absurd hx List.not_mem_nil,
          hv₁1, ?_, ?_⟩
        · show 2 * List.sum [] + leafNeed (ChainLeaf.split v₁) ≤ L₀
          simp only [List.sum_nil, leafNeed]
          omega
        · show LeafPair p (ChainLeaf.split v₁) L₀ L₁ a
          exact ⟨by omega,
            dvd_trans (pow_dvd_pow p (by omega : 2 * v₁ + 1 ≤ v₀)) hdvd₀,
            hdvd₁, hdig₁⟩

/-- **The box covering** (the order-0 layer): every box pair is order-0 decided (split/inert
residual shape) or lies in the cluster at the ONE residue point `c̄ ∈ F_p` named by its
square residual — the `q`-point residue enumeration (`cover_all` classifies the height-0
read; the square's center picks the translate). -/
theorem box_coveringP (N : ℕ) (hN : 0 < N) (a : pairBoxP p N) :
    Ord0SplitCell p N a ∨ Ord0InertCell p N a
      ∨ ∃ c ∈ Finset.range p, ClusterPair p N N (transMapP p c N a) := by
  haveI : NeZero p := ⟨hp.out.ne_zero⟩
  rcases cover_all p (digit p N 0 a.1, digit p N 0 a.2) with h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · obtain ⟨cbar, h1, h2⟩ := (mem_squareAllPairs p).mp h
    have hcv : ((cbar.val : ℕ) : ZMod p) = cbar := ZMod.natCast_rightInverse cbar
    refine Or.inr (Or.inr ⟨cbar.val, Finset.mem_range.mpr (ZMod.val_lt cbar), ?_⟩)
    refine (transMapP_cluster_iff p hN cbar.val a).mpr ⟨?_, ?_⟩
    · rw [hcv, ← digit_zero_eq_resp]
      exact h1
    · rw [hcv, ← digit_zero_eq_resp]
      exact h2

/-! ## 6. The disjointness bank: the splitU cases (blueprint's "new cases")

Same-frame conflicts, extending `ChainMenu` §6: splitU vs splitU (distinct heights pin
distinct exact `v(b₀)`); splitU vs inert (SAME height: pool disjointness, banked); splitU vs
ram/two-sided (height/exactness mismatches); splitU vs a descend step (same slope: the
banked square-exclusion `rootedPairs_not_squareUnit`). -/

/-- SplitU leaves at distinct heights conflict. -/
theorem leafPairU_leafPairU_disjoint {m m' : ℕ} (hne : m ≠ m') {L₀ L₁ : ℕ}
    {a : ZMod (p ^ L₀) × ZMod (p ^ L₁)}
    (h : LeafPairU p m L₀ L₁ a) (h' : LeafPairU p m' L₀ L₁ a) : False := by
  have hud : digit p L₀ (2 * m) a.1 ≠ 0 := leafPairU_digit_ne_zero p h
  have hud' : digit p L₀ (2 * m') a.1 ≠ 0 := leafPairU_digit_ne_zero p h'
  rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
  · exact digit_conflict p (show 2 * m < 2 * m' by omega) hud h'.1
  · exact digit_conflict p (show 2 * m' < 2 * m by omega) hud' h.1

/-- **A splitU leaf conflicts with EVERY main-family leaf** — vs ram/two-sided by
height/exactness pins, vs inert at the same height by the banked pool disjointness. -/
theorem leafPairU_leafPair_disjoint {m : ℕ} {leaf' : ChainLeaf} (hOK' : leafOK leaf')
    {L₀ L₁ : ℕ} {a : ZMod (p ^ L₀) × ZMod (p ^ L₁)}
    (h : LeafPairU p m L₀ L₁ a) (h' : LeafPair p leaf' L₀ L₁ a) : False := by
  obtain ⟨hua, hub, hum⟩ := h
  have hud : digit p L₀ (2 * m) a.1 ≠ 0 := rootedPairs_fst_ne_zero p hum
  cases leaf' with
  | ram H =>
      obtain ⟨hodd', -⟩ := hOK'
      obtain ⟨⟨hra', hrd'⟩, hrb'⟩ := h'
      obtain ⟨t, rfl⟩ := hodd'
      rcases Nat.lt_or_ge (2 * t + 1) (2 * m) with hlt | hge
      · exact digit_conflict p hlt hrd' hua
      · exact digit_conflict p (by omega) hud hra'
  | inert m' =>
      obtain ⟨hia', hib', him'⟩ := h'
      have hid' : digit p L₀ (2 * m') a.1 ≠ 0 := noRootPairs_fst_ne_zero p him'
      rcases Nat.lt_trichotomy m m' with hlt | heq | hgt
      · exact digit_conflict p (show 2 * m < 2 * m' by omega) hud hia'
      · subst heq
        exact Finset.disjoint_left.mp (rootedPairs_disjoint_noRootPairs p) hum him'
      · exact digit_conflict p (show 2 * m' < 2 * m by omega) hid' hua
  | split k' =>
      obtain ⟨-, hsa', hsb', hsd'⟩ := h'
      rcases Nat.lt_or_ge k' m with hlt | hge
      · exact digit_conflict p hlt hsd' hub
      · exact digit_conflict p (by omega) hud hsa'

/-- **A splitU leaf conflicts with a descend step** — distinct slopes pin distinct exact
valuations; the SAME slope pins the square residual `(c̃², −2c̃)`, banked-excluded from the
splitU pool. -/
theorem leafPairU_step_disjoint {m : ℕ} {L₀ L₁ mstep : ℕ}
    {c : (ZMod p)ˣ} {a : ZMod (p ^ L₀) × ZMod (p ^ L₁)}
    (h : LeafPairU p m L₀ L₁ a) (h' : StratumPair p L₀ L₁ mstep c a) : False := by
  obtain ⟨hua, hub, hum⟩ := h
  obtain ⟨⟨hca, hcd⟩, hcb, hce⟩ := h'
  have hcne : digit p L₀ (2 * mstep) a.1 ≠ 0 := by
    rw [hcd]
    exact unit_sq_ne_zero p c
  have hud : digit p L₀ (2 * m) a.1 ≠ 0 := rootedPairs_fst_ne_zero p hum
  rcases Nat.lt_trichotomy m mstep with hlt | heq | hgt
  · exact digit_conflict p (show 2 * m < 2 * mstep by omega) hud hca
  · subst heq
    exact rootedPairs_not_squareUnit p hum c ⟨hcd, hce⟩
  · exact digit_conflict p (show 2 * mstep < 2 * m by omega) hcne hua

/-- **The master splitU-chain disjointness**: distinct `(ms, m)` indices have disjoint
splitU-chain fibers (mirrors `chainPair_disjoint`'s recursion). -/
theorem chainPairU_disjoint :
    ∀ (ms : List ℕ) (m : ℕ), (∀ x ∈ ms, 1 ≤ x) → 1 ≤ m →
    ∀ (ms' : List ℕ) (m' : ℕ), (∀ x ∈ ms', 1 ≤ x) → 1 ≤ m' →
    ¬(ms = ms' ∧ m = m') →
    ∀ (L₀ L₁ : ℕ) (a : ZMod (p ^ L₀) × ZMod (p ^ L₁)),
      ChainPairU p ms m L₀ L₁ a → ChainPairU p ms' m' L₀ L₁ a → False := by
  intro ms
  induction ms with
  | nil =>
      intro m _ hm ms' m' hms' hm' hne L₀ L₁ a h h'
      cases ms' with
      | nil =>
          exact leafPairU_leafPairU_disjoint p (fun hc => hne ⟨rfl, hc⟩) h h'
      | cons mstep' tl' =>
          obtain ⟨c', hstep', -⟩ := h'
          exact leafPairU_step_disjoint p h hstep'
  | cons mstep tl ih =>
      intro m hms hm ms' m' hms' hm' hne L₀ L₁ a h h'
      obtain ⟨c, hstep, hrest⟩ := h
      cases ms' with
      | nil =>
          exact leafPairU_step_disjoint p h' hstep
      | cons mstep' tl' =>
          obtain ⟨c', hstep', hrest'⟩ := h'
          by_cases hmc : mstep = mstep' ∧ c = c'
          · obtain ⟨rfl, rfl⟩ := hmc
            refine ih m (fun x hx => hms x (List.mem_cons_of_mem mstep hx)) hm tl' m'
              (fun x hx => hms' x (List.mem_cons_of_mem mstep hx)) hm'
              (fun ⟨htl, hlf⟩ => hne ⟨by rw [htl], hlf⟩)
              (L₀ - 2 * mstep) (L₁ - mstep) _ hrest hrest'
          · exact step_step_disjoint p hmc hstep hstep'

/-- **The cross-family master disjointness**: EVERY main-chain fiber is disjoint from EVERY
splitU-chain fiber at the same frame (no index condition — the families never overlap). -/
theorem chainPair_chainPairU_disjoint :
    ∀ (ms : List ℕ) (leaf : ChainLeaf), (∀ x ∈ ms, 1 ≤ x) → leafOK leaf →
    ∀ (ms' : List ℕ) (m' : ℕ), (∀ x ∈ ms', 1 ≤ x) → 1 ≤ m' →
    ∀ (L₀ L₁ : ℕ) (a : ZMod (p ^ L₀) × ZMod (p ^ L₁)),
      ChainPair p ms leaf L₀ L₁ a → ChainPairU p ms' m' L₀ L₁ a → False := by
  intro ms
  induction ms with
  | nil =>
      intro leaf _ hOK ms' m' hms' hm' L₀ L₁ a h h'
      cases ms' with
      | nil =>
          exact leafPairU_leafPair_disjoint p hOK h' h
      | cons mstep' tl' =>
          obtain ⟨c', hstep', -⟩ := h'
          exact leaf_step_disjoint p hOK (hms' mstep' List.mem_cons_self) h hstep'
  | cons mstep tl ih =>
      intro leaf hms hOK ms' m' hms' hm' L₀ L₁ a h h'
      obtain ⟨c, hstep, hrest⟩ := h
      cases ms' with
      | nil =>
          exact leafPairU_step_disjoint p h' hstep
      | cons mstep' tl' =>
          obtain ⟨c', hstep', hrest'⟩ := h'
          by_cases hmc : mstep = mstep' ∧ c = c'
          · obtain ⟨rfl, rfl⟩ := hmc
            exact ih leaf (fun x hx => hms x (List.mem_cons_of_mem mstep hx)) hOK tl' m'
              (fun x hx => hms' x (List.mem_cons_of_mem mstep hx)) hm'
              (L₀ - 2 * mstep) (L₁ - mstep) _ hrest hrest'
          · exact step_step_disjoint p hmc hstep hstep'

/-! ### Order-0 cells vs everything (the banked pool conflicts, box level) -/

/-- The two order-0 cells are disjoint (split pool vs inert pool). -/
theorem ord0Split_ord0Inert_disjoint {N : ℕ} {a : pairBoxP p N}
    (h : Ord0SplitCell p N a) (h' : Ord0InertCell p N a) : False :=
  Finset.disjoint_left.mp (splitResPairs_disjoint_noRootPairs p) h h'

/-- An order-0 split cell is in no translate's cluster (split shape vs square residual). -/
theorem ord0Split_not_cluster {N : ℕ} (hN : 0 < N) {c : ℕ} {a : pairBoxP p N}
    (h : Ord0SplitCell p N a) (h' : ClusterPair p N N (transMapP p c N a)) : False :=
  Finset.disjoint_left.mp (splitResPairs_disjoint_squareAllPairs p) h
    (sqResLocus_of_cluster p hN h')

/-- An order-0 inert cell is in no translate's cluster (root-free vs square residual). -/
theorem ord0Inert_not_cluster {N : ℕ} (hN : 0 < N) {c : ℕ} {a : pairBoxP p N}
    (h : Ord0InertCell p N a) (h' : ClusterPair p N N (transMapP p c N a)) : False :=
  Finset.disjoint_left.mp (noRootPairs_disjoint_squareAllPairs p) h
    (sqResLocus_of_cluster p hN h')

/-! ## 7. The combined chain index and THE MASTER PAIRWISE DISJOINTNESS (W6 §I at general `p`) -/

/-- The combined leaf menu across the three types (main families). -/
noncomputable def allLeavesP (K : ℕ) : Finset ChainLeaf :=
  chainLeaves K ramType2 ∪ chainLeaves K inertType2 ∪ chainLeaves K splitType2

theorem chainLeaves_shape_ram {K : ℕ} {leaf : ChainLeaf}
    (h : leaf ∈ chainLeaves K ramType2) : ∃ H, leaf = ChainLeaf.ram H := by
  rw [chainLeaves, if_pos rfl, Finset.mem_image] at h
  obtain ⟨j, -, rfl⟩ := h
  exact ⟨2 * j - 1, rfl⟩

theorem chainLeaves_shape_inert {K : ℕ} {leaf : ChainLeaf}
    (h : leaf ∈ chainLeaves K inertType2) : ∃ m, leaf = ChainLeaf.inert m := by
  rw [chainLeaves, if_neg (Ne.symm ram_ne_inert), if_pos rfl, Finset.mem_image] at h
  obtain ⟨m, -, rfl⟩ := h
  exact ⟨m, rfl⟩

theorem chainLeaves_shape_split {K : ℕ} {leaf : ChainLeaf}
    (h : leaf ∈ chainLeaves K splitType2) : ∃ k, leaf = ChainLeaf.split k := by
  rw [chainLeaves, if_neg (Ne.symm ram_ne_split), if_neg (Ne.symm inert_ne_split),
    if_pos rfl, Finset.mem_image] at h
  obtain ⟨k, -, rfl⟩ := h
  exact ⟨k, rfl⟩

theorem disj_ram_inert (K : ℕ) :
    Disjoint (chainLeaves K ramType2) (chainLeaves K inertType2) :=
  Finset.disjoint_left.mpr fun leaf h1 h2 => by
    obtain ⟨H, rfl⟩ := chainLeaves_shape_ram h1
    obtain ⟨m, hm⟩ := chainLeaves_shape_inert h2
    exact ChainLeaf.noConfusion hm

theorem disj_ramInert_split (K : ℕ) :
    Disjoint (chainLeaves K ramType2 ∪ chainLeaves K inertType2)
      (chainLeaves K splitType2) :=
  Finset.disjoint_left.mpr fun leaf h1 h2 => by
    obtain ⟨k, hk⟩ := chainLeaves_shape_split h2
    rcases Finset.mem_union.mp h1 with h | h
    · obtain ⟨H, rfl⟩ := chainLeaves_shape_ram h
      exact ChainLeaf.noConfusion hk
    · obtain ⟨m, rfl⟩ := chainLeaves_shape_inert h
      exact ChainLeaf.noConfusion hk

theorem leafOK_of_mem_allLeavesP {K : ℕ} {leaf : ChainLeaf} (h : leaf ∈ allLeavesP K) :
    leafOK leaf := by
  rcases Finset.mem_union.mp h with h' | h3
  · rcases Finset.mem_union.mp h' with h1 | h2
    · exact (of_mem_chainLeaves h1).1
    · exact (of_mem_chainLeaves h2).1
  · exact (of_mem_chainLeaves h3).1

/-- The combined chain fiber, indexed by a leaf tag: `.inl leaf` = a main family (ram /
inert / two-sided split), `.inr m` = the splitU family (the blueprint §1.6 design: a SUM
index instead of extending `ChainLeaf`). -/
def TransFiber (c : ℕ) (ms : List ℕ) : ChainLeaf ⊕ ℕ → (N : ℕ) → pairBoxP p N → Prop
  | .inl leaf, N, a => TransChainP p c ms leaf N a
  | .inr m, N, a => TransChainU p c ms m N a

noncomputable def transFiberCount (c : ℕ) (ms : List ℕ) (t : ChainLeaf ⊕ ℕ) (N : ℕ) : ℕ :=
  Nat.card {a : pairBoxP p N // TransFiber p c ms t N a}

theorem transFiberCount_inl (c : ℕ) (ms : List ℕ) (leaf : ChainLeaf) (N : ℕ) :
    transFiberCount p c ms (Sum.inl leaf) N = transChainCountP p c ms leaf N := rfl

theorem transFiberCount_inr (c : ℕ) (ms : List ℕ) (m : ℕ) (N : ℕ) :
    transFiberCount p c ms (Sum.inr m) N = transChainCountU p c ms m N := rfl

/-- Every valid chain fiber lies in the square-residual locus (its translate clusters). -/
theorem sqResLocus_of_transFiber {N : ℕ} (hN : 0 < N) {c : ℕ} {ms : List ℕ}
    {t : ChainLeaf ⊕ ℕ} (hms : ∀ m ∈ ms, 1 ≤ m)
    (ht : t ∈ (allLeavesP N).disjSum (Finset.Icc 1 N))
    {a : pairBoxP p N} (h : TransFiber p c ms t N a) : SqResLocus p N a := by
  cases t with
  | inl leaf =>
      exact sqResLocus_of_cluster p hN (clusterPair_of_chainPair p ms leaf hms
        (leafOK_of_mem_allLeavesP (Finset.inl_mem_disjSum.mp ht)) h)
  | inr m =>
      exact sqResLocus_of_cluster p hN (clusterPair_of_chainPairU p ms hms
        (Finset.mem_Icc.mp (Finset.inr_mem_disjSum.mp ht)).1 h)

/-- **THE MASTER PAIRWISE DISJOINTNESS** of all counted chain fibers: distinct
`(c, ms, family-tag)` indices conflict — same residue point via the digit-ledger bank
(incl. the new splitU cases), distinct residue points via the square-center uniqueness
(`cross_cluster_conflictP`). The model's decided count double-counts nothing. -/
theorem transFiber_pairwise_disjoint {N : ℕ} (hN : 0 < N)
    {i j : ℕ × List ℕ × (ChainLeaf ⊕ ℕ)}
    (hi : i ∈ (Finset.range p) ×ˢ (msMenu N N ×ˢ (allLeavesP N).disjSum (Finset.Icc 1 N)))
    (hj : j ∈ (Finset.range p) ×ˢ (msMenu N N ×ˢ (allLeavesP N).disjSum (Finset.Icc 1 N)))
    (hij : i ≠ j) (a : pairBoxP p N)
    (h1 : TransFiber p i.1 i.2.1 i.2.2 N a) (h2 : TransFiber p j.1 j.2.1 j.2.2 N a) :
    False := by
  obtain ⟨ci, msi, ti⟩ := i
  obtain ⟨cj, msj, tj⟩ := j
  rw [Finset.mem_product] at hi hj
  obtain ⟨hci, hxi⟩ := hi
  obtain ⟨hcj, hxj⟩ := hj
  rw [Finset.mem_product] at hxi hxj
  have hmsi : ∀ m ∈ msi, 1 ≤ m := fun m hm => (((mem_msMenu N N msi).mp hxi.1).2 m hm).1
  have hmsj : ∀ m ∈ msj, 1 ≤ m := fun m hm => (((mem_msMenu N N msj).mp hxj.1).2 m hm).1
  by_cases hcc : ci = cj
  · subst hcc
    cases ti with
    | inl leafi =>
        cases tj with
        | inl leafj =>
            have hOKi := leafOK_of_mem_allLeavesP (Finset.inl_mem_disjSum.mp hxi.2)
            have hOKj := leafOK_of_mem_allLeavesP (Finset.inl_mem_disjSum.mp hxj.2)
            have hne : ¬(msi = msj ∧ leafi = leafj) := by
              rintro ⟨rfl, rfl⟩
              exact hij rfl
            exact chainPair_disjoint p msi leafi hmsi hOKi msj leafj hmsj hOKj hne
              N N _ h1 h2
        | inr mj =>
            have hOKi := leafOK_of_mem_allLeavesP (Finset.inl_mem_disjSum.mp hxi.2)
            have hmj : 1 ≤ mj := (Finset.mem_Icc.mp (Finset.inr_mem_disjSum.mp hxj.2)).1
            exact chainPair_chainPairU_disjoint p msi leafi hmsi hOKi msj mj hmsj hmj
              N N _ h1 h2
    | inr mi =>
        have hmi : 1 ≤ mi := (Finset.mem_Icc.mp (Finset.inr_mem_disjSum.mp hxi.2)).1
        cases tj with
        | inl leafj =>
            have hOKj := leafOK_of_mem_allLeavesP (Finset.inl_mem_disjSum.mp hxj.2)
            exact chainPair_chainPairU_disjoint p msj leafj hmsj hOKj msi mi hmsi hmi
              N N _ h2 h1
        | inr mj =>
            have hmj : 1 ≤ mj := (Finset.mem_Icc.mp (Finset.inr_mem_disjSum.mp hxj.2)).1
            have hne : ¬(msi = msj ∧ mi = mj) := by
              rintro ⟨rfl, rfl⟩
              exact hij rfl
            exact chainPairU_disjoint p msi mi hmsi hmi msj mj hmsj hmj hne N N _ h1 h2
  · have hcip : ci < p := Finset.mem_range.mp hci
    have hcjp : cj < p := Finset.mem_range.mp hcj
    have hcli : ClusterPair p N N (transMapP p ci N a) := by
      cases ti with
      | inl leafi =>
          exact clusterPair_of_chainPair p msi leafi hmsi
            (leafOK_of_mem_allLeavesP (Finset.inl_mem_disjSum.mp hxi.2)) h1
      | inr mi =>
          exact clusterPair_of_chainPairU p msi hmsi
            (Finset.mem_Icc.mp (Finset.inr_mem_disjSum.mp hxi.2)).1 h1
    have hclj : ClusterPair p N N (transMapP p cj N a) := by
      cases tj with
      | inl leafj =>
          exact clusterPair_of_chainPair p msj leafj hmsj
            (leafOK_of_mem_allLeavesP (Finset.inl_mem_disjSum.mp hxj.2)) h2
      | inr mj =>
          exact clusterPair_of_chainPairU p msj hmsj
            (Finset.mem_Icc.mp (Finset.inr_mem_disjSum.mp hxj.2)).1 h2
    exact cross_cluster_conflictP p hN hcip hcjp hcc hcli hclj

/-! ## 8. The box bound (`undecidedCountP ≥ 0` — the disjointness made consumable) -/

/-- The σ-sum of chain counts re-indexes over the combined `(leaf ⊕ splitU)` menu. -/
theorem chainTotalP_eq (N : ℕ) :
    ∑ σ ∈ typeMenuP, chainCountP p σ N
      = ∑ c ∈ Finset.range p,
          ∑ x ∈ msMenu N N ×ˢ (allLeavesP N).disjSum (Finset.Icc 1 N),
            ((transFiberCount p c x.1 x.2 N : ℕ) : ℚ) := by
  have hmain : ∑ σ ∈ typeMenuP, chainCountMain p σ N
      = ∑ c ∈ Finset.range p, ∑ x ∈ msMenu N N ×ˢ allLeavesP N,
          ((transChainCountP p c x.1 x.2 N : ℕ) : ℚ) := by
    rw [sum_typeMenuP]
    unfold chainCountMain
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [Finset.sum_product, Finset.sum_product, Finset.sum_product, Finset.sum_product]
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun ms _ => ?_
    unfold allLeavesP
    rw [Finset.sum_union (disj_ramInert_split N), Finset.sum_union (disj_ram_inert N)]
  have hif : ∑ σ ∈ typeMenuP, (if σ = splitType2 then chainCountUTot p N else 0)
      = chainCountUTot p N := by
    rw [sum_typeMenuP, if_neg ram_ne_split, if_neg inert_ne_split, if_pos rfl]
    ring
  calc ∑ σ ∈ typeMenuP, chainCountP p σ N
      = ∑ σ ∈ typeMenuP, chainCountMain p σ N
          + ∑ σ ∈ typeMenuP, (if σ = splitType2 then chainCountUTot p N else 0) := by
        unfold chainCountP
        rw [Finset.sum_add_distrib]
    _ = ∑ c ∈ Finset.range p, ∑ x ∈ msMenu N N ×ˢ allLeavesP N,
          ((transChainCountP p c x.1 x.2 N : ℕ) : ℚ)
        + ∑ c ∈ Finset.range p, ∑ x ∈ msMenu N N ×ˢ Finset.Icc 1 N,
            ((transChainCountU p c x.1 x.2 N : ℕ) : ℚ) := by
        rw [hmain, hif]
        rfl
    _ = ∑ c ∈ Finset.range p,
          (∑ x ∈ msMenu N N ×ˢ allLeavesP N, ((transChainCountP p c x.1 x.2 N : ℕ) : ℚ)
            + ∑ x ∈ msMenu N N ×ˢ Finset.Icc 1 N,
                ((transChainCountU p c x.1 x.2 N : ℕ) : ℚ)) := by
        rw [← Finset.sum_add_distrib]
    _ = ∑ c ∈ Finset.range p,
          ∑ x ∈ msMenu N N ×ˢ (allLeavesP N).disjSum (Finset.Icc 1 N),
            ((transFiberCount p c x.1 x.2 N : ℕ) : ℚ) := by
        refine Finset.sum_congr rfl fun c _ => ?_
        rw [Finset.sum_product, Finset.sum_product, Finset.sum_product,
          ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun ms _ => ?_
        rw [Finset.sum_disjSum]
        simp only [transFiberCount_inl, transFiberCount_inr]

/-- The chain total is bounded by the square-residual locus (all fibers disjoint inside it). -/
theorem chainTotalP_le_sq (N : ℕ) (hN : 0 < N) :
    ∑ σ ∈ typeMenuP, chainCountP p σ N
      ≤ ((Nat.card {a : pairBoxP p N // SqResLocus p N a} : ℕ) : ℚ) := by
  rw [chainTotalP_eq]
  have hkey : (∑ i ∈ ((Finset.range p) ×ˢ
        (msMenu N N ×ˢ (allLeavesP N).disjSum (Finset.Icc 1 N))),
      transFiberCount p i.1 i.2.1 i.2.2 N)
      ≤ Nat.card {a : pairBoxP p N // SqResLocus p N a} := by
    have hsub := MultiSlopeMenu.sum_card_disjoint_le
      (α := {a : pairBoxP p N // SqResLocus p N a})
      (s := (Finset.range p) ×ˢ (msMenu N N ×ˢ (allLeavesP N).disjSum (Finset.Icc 1 N)))
      (F := fun i e => TransFiber p i.1 i.2.1 i.2.2 N e.1)
      (fun i hi j hj hij e he1 he2 =>
        transFiber_pairwise_disjoint p hN hi hj hij e.1 he1 he2)
    refine le_trans (le_of_eq ?_) hsub
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [Finset.mem_product] at hi
    obtain ⟨hci, hxi⟩ := hi
    rw [Finset.mem_product] at hxi
    have hms : ∀ m ∈ i.2.1, 1 ≤ m :=
      fun m hm => (((mem_msMenu N N i.2.1).mp hxi.1).2 m hm).1
    unfold transFiberCount
    exact (Nat.card_congr ((Equiv.subtypeSubtypeEquivSubtypeInter
        (fun a : pairBoxP p N => SqResLocus p N a)
        (fun a => TransFiber p i.1 i.2.1 i.2.2 N a)).trans
      (Equiv.subtypeEquivRight (fun a =>
        ⟨fun h => h.2, fun h => ⟨sqResLocus_of_transFiber p hN hms hxi.2 h, h⟩⟩)))).symm
  have hcast : ∑ c ∈ Finset.range p,
      ∑ x ∈ msMenu N N ×ˢ (allLeavesP N).disjSum (Finset.Icc 1 N),
        ((transFiberCount p c x.1 x.2 N : ℕ) : ℚ)
      = ((∑ i ∈ ((Finset.range p) ×ˢ
            (msMenu N N ×ˢ (allLeavesP N).disjSum (Finset.Icc 1 N))),
          transFiberCount p i.1 i.2.1 i.2.2 N : ℕ) : ℚ) := by
    rw [Nat.cast_sum, Finset.sum_product]
  rw [hcast]
  exact_mod_cast hkey

/-- **The box bound**: the decided total never exceeds the box — the order-0 cells and the
square-residual locus tile the box (`card_ord0_partition`), and the chain fibers are
pairwise-disjoint subsets of the latter. -/
theorem sum_decidedP_le_box (N : ℕ) :
    ∑ σ ∈ typeMenuP, decidedCountP p σ N ≤ (p : ℚ) ^ (2 * N) := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · rw [Finset.sum_eq_zero fun σ _ => decidedCountP_zero p σ]
    positivity
  · have hsum : ∑ σ ∈ typeMenuP, decidedCountP p σ N
        = ∑ σ ∈ typeMenuP, ord0Count p σ N + ∑ σ ∈ typeMenuP, chainCountP p σ N := by
      unfold decidedCountP
      rw [Finset.sum_add_distrib]
    have hord : ∑ σ ∈ typeMenuP, ord0Count p σ N
        = ((Nat.card {a : pairBoxP p N // Ord0SplitCell p N a}
            + Nat.card {a : pairBoxP p N // Ord0InertCell p N a} : ℕ) : ℚ) := by
      rw [sum_typeMenuP]
      unfold ord0Count
      rw [if_neg ram_ne_split, if_neg ram_ne_inert, if_neg inert_ne_split,
        if_pos rfl, if_pos rfl]
      push_cast
      ring
    have hchain := chainTotalP_le_sq p N hN
    have hpart : Nat.card {a : pairBoxP p N // Ord0SplitCell p N a}
        + Nat.card {a : pairBoxP p N // Ord0InertCell p N a}
        + Nat.card {a : pairBoxP p N // SqResLocus p N a} = p ^ (2 * N) := by
      rw [card_ord0Split p N hN, card_ord0Inert p N hN, card_sqResLocus p N hN]
      have hpools : (splitResPairs p).card + (noRootPairs p).card + p = p * p := by
        have h := card_ord0_partition p
        rw [card_squareAllPairs p] at h
        exact h
      have hpow : p ^ (2 * N) = p * p * (p ^ (N - 1) * p ^ (N - 1)) := by
        rw [show 2 * N = 1 + (1 + ((N - 1) + (N - 1))) from by omega, pow_add, pow_add,
          pow_add, pow_one]
        ring
      calc (splitResPairs p).card * (p ^ (N - 1) * p ^ (N - 1))
            + (noRootPairs p).card * (p ^ (N - 1) * p ^ (N - 1))
            + p * (p ^ (N - 1) * p ^ (N - 1))
          = ((splitResPairs p).card + (noRootPairs p).card + p)
              * (p ^ (N - 1) * p ^ (N - 1)) := by ring
        _ = p * p * (p ^ (N - 1) * p ^ (N - 1)) := by rw [hpools]
        _ = p ^ (2 * N) := hpow.symm
    have hcast : ((Nat.card {a : pairBoxP p N // Ord0SplitCell p N a}
        + Nat.card {a : pairBoxP p N // Ord0InertCell p N a} : ℕ) : ℚ)
        + ((Nat.card {a : pairBoxP p N // SqResLocus p N a} : ℕ) : ℚ)
        = (p : ℚ) ^ (2 * N) := by
      rw [← Nat.cast_add, hpart]
      push_cast
      ring
    rw [hsum, hord]
    linarith
theorem undecidedP_nonneg (N : ℕ) : 0 ≤ undecidedCountP p N := by
  unfold undecidedCountP
  linarith [sum_decidedP_le_box p N]

/-! ## 9. `p = 2` splitU vanishing (the honest-empty family at the wild prime) -/

/-- At `p = 2` every splitU chain fiber is EMPTY (the pool `rootedPairs 2 = ∅`). -/
theorem chainPairU_two_empty (ms : List ℕ) (m : ℕ) :
    ∀ (L₀ L₁ : ℕ) (a : ZMod (2 ^ L₀) × ZMod (2 ^ L₁)), ¬ ChainPairU 2 ms m L₀ L₁ a := by
  induction ms with
  | nil =>
      rintro L₀ L₁ a ⟨-, -, hmem⟩
      rw [rootedPairs_two_empty] at hmem
      exact absurd hmem (Finset.notMem_empty _)
  | cons mstep ms ih =>
      rintro L₀ L₁ a ⟨c, -, hrest⟩
      exact ih _ _ _ hrest

/-- At `p = 2` every translated splitU count vanishes — the `q = 2` recovery's key zero. -/
theorem transChainCountU_two (c : ℕ) (ms : List ℕ) (m : ℕ) (N : ℕ) :
    transChainCountU 2 c ms m N = 0 := by
  haveI : IsEmpty {a : pairBoxP 2 N // TransChainU 2 c ms m N a} :=
    ⟨fun x => chainPairU_two_empty ms m N N _ x.2⟩
  exact Nat.card_of_isEmpty

/-- The whole splitU total vanishes at `p = 2`. -/
theorem chainCountUTot_two (N : ℕ) : chainCountUTot 2 N = 0 := by
  unfold chainCountUTot
  refine Finset.sum_eq_zero fun c _ => Finset.sum_eq_zero fun x _ => ?_
  rw [transChainCountU_two]
  rfl

/-! ## 10. Census gates (blueprint §4 mitigation: anchors at `p = 3`) -/

section GateCensus

/-- `p = 3, N = 2` order-0 split gate: `ord0Count = q(q−1)/2 · q² = 3·9 = 27`. -/
theorem gate_ord0Split_three : ord0Count 3 splitType2 2 = 27 := by
  unfold ord0Count
  rw [if_pos rfl, card_ord0Split_closed 3 2 (by norm_num)]
  norm_num

/-- `p = 3, N = 2` order-0 inert gate: `27` (the split/inert order-0 symmetry). -/
theorem gate_ord0Inert_three : ord0Count 3 inertType2 2 = 27 := by
  unfold ord0Count
  rw [if_neg inert_ne_split, if_pos rfl, card_ord0Inert_closed 3 2 (by norm_num)]
  norm_num

/-- The smallest nonempty splitU frame at `p = 3` (`ms = []`, `m = 1`, `N = 3`): count
`= pool × tails = 1 · 3 = 3` (blueprint §0's splitU pool check, fiber level). -/
theorem gate_transChainCountU_three : transChainCountU 3 1 [] 1 3 = 3 := by
  rw [transChainCountU_eq_pair]
  rw [card_chainPairU 3 [] 1 (fun x hx => absurd hx List.not_mem_nil) le_rfl 3 3
    (by simp [leafNeedU]) le_rfl]
  simp only [List.length_nil, List.sum_nil, pow_zero, one_mul, Nat.mul_zero, Nat.sub_zero]
  simp only [leafCountU]
  rw [card_rootedPairs_three]
  norm_num

end GateCensus

/-! ## 11. AxCheck — every declaration of this wave is core-only -/

section AxCheck
#print axioms transMapP
#print axioms transMapP_zero
#print axioms card_comp_equiv
#print axioms digit_zero_eq_resp
#print axioms resp_transMapP_fst
#print axioms resp_transMapP_snd
#print axioms transMapP_cluster_iff
#print axioms cross_cluster_conflictP
#print axioms SqResLocus
#print axioms sqResLocus_of_cluster
#print axioms card_sqResLocus
#print axioms StallPairP
#print axioms clusterPair_of_stallPairP
#print axioms TransChainP
#print axioms TransChainU
#print axioms TransStallP
#print axioms transChainCountP
#print axioms transChainCountU
#print axioms transStallCountP
#print axioms transChainCountP_eq_pair
#print axioms transChainCountU_eq_pair
#print axioms transStallCountP_eq_pair
#print axioms ram_ne_inert
#print axioms ram_ne_split
#print axioms inert_ne_split
#print axioms ord0Count
#print axioms chainCountMain
#print axioms chainCountUTot
#print axioms chainCountP
#print axioms decidedCountP
#print axioms typeMenuP
#print axioms undecidedCountP
#print axioms sum_typeMenuP
#print axioms ord0Count_nonneg
#print axioms chainCountMain_nonneg
#print axioms chainCountUTot_nonneg
#print axioms chainCountP_nonneg
#print axioms decidedCountP_nonneg
#print axioms decided_add_undecided
#print axioms digit_zero_level_zero
#print axioms ord0Split_zero_empty
#print axioms ord0Inert_zero_empty
#print axioms chainLeaves_zero
#print axioms decidedCountP_zero
#print axioms cluster_coveringP
#print axioms box_coveringP
#print axioms leafPairU_leafPairU_disjoint
#print axioms leafPairU_leafPair_disjoint
#print axioms leafPairU_step_disjoint
#print axioms chainPairU_disjoint
#print axioms chainPair_chainPairU_disjoint
#print axioms ord0Split_ord0Inert_disjoint
#print axioms ord0Split_not_cluster
#print axioms ord0Inert_not_cluster
#print axioms allLeavesP
#print axioms chainLeaves_shape_ram
#print axioms chainLeaves_shape_inert
#print axioms chainLeaves_shape_split
#print axioms disj_ram_inert
#print axioms disj_ramInert_split
#print axioms leafOK_of_mem_allLeavesP
#print axioms TransFiber
#print axioms transFiberCount
#print axioms transFiberCount_inl
#print axioms transFiberCount_inr
#print axioms sqResLocus_of_transFiber
#print axioms transFiber_pairwise_disjoint
#print axioms chainTotalP_eq
#print axioms chainTotalP_le_sq
#print axioms sum_decidedP_le_box
#print axioms undecidedP_nonneg
#print axioms chainPairU_two_empty
#print axioms transChainCountU_two
#print axioms chainCountUTot_two
#print axioms gate_ord0Split_three
#print axioms gate_ord0Inert_three
#print axioms gate_transChainCountU_three
end AxCheck

end LeanUrat.OM.UniformModelN2
