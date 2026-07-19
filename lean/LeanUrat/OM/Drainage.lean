/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.L5fix
import LeanUrat.OM.CellCard
import LeanUrat.OM.HNode1

/-!
# Drainage — Phase-B wave W5: the ORDER-1 drainage bounds (the undecided-mass census)

**Provenance.** `notes/PHASEB_CLASSIFIER_BLUEPRINT.md` §6 (drainage / h_env-v2), assembled from
banked APIs only: `CellCard` (W4a/b: `card_clusterBox`, `card_cluster_dead`, `cell_card_raw`,
`shapeCount_linear_pow`), `CellMenu` (W2: `classify1`, the F1 sharp law
`classify1_isSome`/`classify1_eq_none_of_tail`), `HNode1` (W4e: `selfLoop_cost_tie`),
`RestartEquiv` (W4d1: `gate_A` cross-check).  This module edits NOTHING existing.

**W0-ERRATUM (F1) honoured**: the order-1 TAIL is LEFT-ENDPOINT unreadability `a₀ ≡ 0 mod p^N`
— NOT a discriminant condition.  `IsTail` is defined through the genuine classifier
(`classify1 = none`) and *proved* equal to the dead-`a₀` set (`isTail_iff_dead`).

**The census** (numeric gate `/workspace-vast/asving/tmp/phaseb_w5/`, `undecided_census.py`,
verified exactly at `(p,s,N) ∈ {2,3}×{2,3,4}×{3,4,5}` windows, 8 parameter points):

* `card_tail = p^((s−1)(N−1))`, index form `card_tail · p^(N−1) = card_clusterBox`;
* `card_selfLoopFiber = (p−1) · p^(s(N−1) − s(s+1)/2)`, index form
  `card_selfLoopFiber · p^(w(s)+1) = (p−1) · card_clusterBox`, `w = L5fix.selfLoopExponent`;
* `card_undecided₁ = card_tail + card_selfLoopFiber` (disjoint: an `Option` cannot be `none`
  and `some c` at once; semantically, self-loop fibers are readable — `inCell_isReadable`);
* EXACT density: `undecidedDensity = p^{−(N−1)} + (p−1)·p^{−(w(s)+1)}`.

**Honesty notes (numerically calibrated, see the W5 gate artifacts).**
1. The task-sheet index bound `undecided₁ · p^(min(N−1)(w+1)) ≤ cluster` is FALSE — at
   `(2,2,3)`: `6·2² = 24 > 16` (`probe_naive_min_bound_fails`).  The true forms proved here:
   the EXACT two-term index identity `card_undecided1_index` and the corrected inequality
   `undecided₁ · p^(min(N−1)(w)) ≤ 2·cluster` (`card_undecided1_min_bound`).
2. The task-sheet density bound `≤ p^{−(N−1)} + p^{−(w+1)}` is TIGHT (an equality) at `p = 2`
   (`gate_density_tight_s2N3`: `3/8 = 1/4 + 1/8`) but FALSE for `p ≥ 3` — at `(3,2,3)` the
   density is `5/27 > 4/27` (`probe_p3_mass`): the `(p−1)` residual-root multiplicity is real.
   The true general-`p` bound is `≤ p^{−(N−1)} + p^{−w(s)}` (`undecidedDensity_le`).
3. `Undecided1` tracks the tail plus THE order-1 self-loop cell (slope `−1`, shape `(1,s)`).
   In the window **`s` prime and `s < N ≤ 2s`** this is verified (numerically, F5-restricted
   menu) to be the COMPLETE set of no-progress boxes: the self-loop cell is the unique
   childless-but-undecided menu cell there.  Beyond the window further stuck cells join:
   at `(s,N) = (2,5)` the `h = 2` recentering cell `(0,4)→(2,0)`, shape `(1,2)`
   (`probe_deeper_selfLoop_cell`), and at `(s,N) = (4,5)` the residue-degree-2 cell
   `(0,4)→(4,0)`, shape `(2,2)`.  Their mass (`p^{−h(w+1)}`-sized, resp. `D ≥ 2`-descent) is
   W6 scope: the tower iteration, where after `k` self-loop orders the stuck mass costs
   `p^{−k(w+1)}`.
4. THE VANISHING, stated honestly: the TAIL mass tends to `0` as `N → ∞`
   (`tendsto_tailDensity_zero`), while the one-step self-loop mass is `N`-INDEPENDENT — the
   full density tends to the nonzero constant `(p−1)·p^{−(w(s)+1)}`
   (`tendsto_undecidedDensity`), which is `s`-uniformly `≤ p^{−2} ≤ 1/4` for `s ≥ 2`
   (`selfLoopMass_le`).  Genuine full vanishing NEEDS the order-tower iteration
   (self-loop → next order → its own drainage), i.e. the geometric `Σ_k p^{−k(w+1)}`
   resummation that `L5fix.selfLoopPivot`/`countPivot` compensates — W6 scope.  We do NOT
   overclaim it from the one-step bound.

Discipline: no `sorry`/`axiom`/`native_decide`; core-only footprints (checked with
`#print axioms`, prints removed after checking); no existing module touched.
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

namespace LeanUrat.OM.Drainage

open Filter Polynomial
open LeanUrat LeanUrat.OM
open LeanUrat.OM.CellMenu
open LeanUrat.OM.CellCard
open LeanUrat.OM.OMCountV2 (NodeConfig)

noncomputable section

variable (p : ℕ) [hp : Fact p.Prime]

/-! ## 0. Generic helper: disjoint-union split of a subtype count -/

/-- Disjoint split of a subtype count (the `∨`-companion of
`CellCard.card_subtype_and_compl`). -/
theorem card_subtype_or_disjoint {α : Type*} [Finite α] (P Q : α → Prop)
    (h : ∀ x, ¬ (P x ∧ Q x)) :
    Nat.card {x // P x ∨ Q x} = Nat.card {x // P x} + Nat.card {x // Q x} := by
  have hsplit := card_subtype_and_compl (fun x => P x ∨ Q x) P
  have h1 : Nat.card {x // (P x ∨ Q x) ∧ P x} = Nat.card {x // P x} :=
    Nat.card_congr (Equiv.subtypeEquivRight fun x =>
      ⟨fun hx => hx.2, fun hx => ⟨Or.inl hx, hx⟩⟩)
  have h2 : Nat.card {x // (P x ∨ Q x) ∧ ¬ P x} = Nat.card {x // Q x} :=
    Nat.card_congr (Equiv.subtypeEquivRight fun x =>
      ⟨fun hx => hx.1.resolve_left hx.2, fun hx => ⟨Or.inr hx, fun hP => h x ⟨hP, hx⟩⟩⟩)
  omega

/-! ## 1. Deliverable 1: the TAIL and its census -/

/-- **The order-1 TAIL**: cluster boxes on which the genuine order-1 classifier is silent.
By the F1 sharp law (W0-erratum: LEFT-ENDPOINT readability, not disc) these are exactly the
boxes with `a₀ ≡ 0 mod p^N` — `isTail_iff_dead`. -/
def IsTail {N s : ℕ} (f : QuotientBox.monicBox p N s) : Prop :=
  IsCluster p f ∧ classify1 p f = none

/-- The F1 sharp law, packaged: on the cluster box, `classify1 = none ⟺ v_p(a₀) ≥ N`
(⟺ `a₀ = 0` in `ZMod (p^N)`). -/
theorem isTail_iff_dead {N s : ℕ} (hN : 0 < N) (hs : 0 < s)
    (f : QuotientBox.monicBox p N s) :
    IsTail p f ↔ IsCluster p f ∧ ¬ vOf p f 0 < N := by
  constructor
  · rintro ⟨hcl, hnone⟩
    refine ⟨hcl, fun hread => ?_⟩
    have h1 := classify1_isSome p hN hs f hcl hread
    rw [hnone] at h1
    simp at h1
  · rintro ⟨hcl, hdead⟩
    refine ⟨hcl, ?_⟩
    have hcoeff : (f.1).coeff 0 = 0 := by
      by_contra hne
      exact hdead (PadicLift.zmodValuation_lt p hN hne)
    exact classify1_eq_none_of_tail p hN hcoeff

/-- **Deliverable 1, `card_tail`**: exactly `p^((s−1)(N−1))` tail boxes — the classifier-side
statement of W4a's `card_cluster_dead`. -/
theorem card_tail {N s : ℕ} (hN : 0 < N) (hs : 0 < s) :
    Nat.card {f : QuotientBox.monicBox p N s // IsTail p f} = p ^ ((s - 1) * (N - 1)) := by
  rw [Nat.card_congr (Equiv.subtypeEquivRight (isTail_iff_dead p hN hs))]
  exact card_cluster_dead p hN hs

/-- **Deliverable 1, division-free index form**: the tail sits inside the cluster box at index
exactly `p^(N−1)` — the tail mass fraction is `p^{−(N−1)}`. -/
theorem card_tail_index {N s : ℕ} (hN : 0 < N) (hs : 0 < s) :
    Nat.card {f : QuotientBox.monicBox p N s // IsTail p f} * p ^ (N - 1)
      = Nat.card {f : QuotientBox.monicBox p N s // IsCluster p f} := by
  rw [card_tail p hN hs, card_clusterBox p hN, ← pow_add]
  congr 1
  obtain ⟨s', rfl⟩ : ∃ s', s = s' + 1 := ⟨s - 1, by omega⟩
  rw [Nat.add_sub_cancel, Nat.succ_mul]

/-! ## 2. The self-loop cell and its fiber census -/

/-- The self-loop path: the single side `(0, s) → (s, 0)` of slope `−1`. -/
def selfLoopPath (s : ℕ) : List (ℕ × ℕ) := [(0, s), (s, 0)]

/-- **THE order-1 self-loop cell** of the size-`s` x-power cluster: slope `−1` (so `e = 1`,
no ramification gain), residual `(y − c̃)^s` shape (so `D = 1`, no residue gain) — the unique
menu cell whose A2 child budget `μ·D = s` equals the parent budget: NO PROGRESS.  It is
childless (`selfLoopCell_children`) but undecided.  This is `RestartEquiv.restartCell 1 s`
with the `s·1` arithmetic normalized away. -/
def selfLoopCell (s : ℕ) : NodeConfig := mkCell s (selfLoopPath s) [[(1, s)]]

theorem selfLoopPath_menuPath {N s : ℕ} (hs : 0 < s) (hsN : s < N) :
    MenuPath s N (selfLoopPath s) :=
  ⟨s, (s, 0), [], rfl, hs, by omega, hs, hs, ChainOK.nil rfl rfl⟩

theorem sideDeg_selfLoop (s : ℕ) : sideDeg ((0, s), (s, 0)) = s := by
  show Nat.gcd (s - 0) (s - 0) = s
  rw [Nat.sub_zero, Nat.gcd_self]

theorem selfLoopShapes {s : ℕ} (hs : 0 < s) : ShapesFor (selfLoopPath s) [[(1, s)]] := by
  show List.Forall₂ _ [[(1, s)]] (sidePairs (selfLoopPath s))
  rw [show sidePairs (selfLoopPath s) = [((0, s), (s, 0))] from rfl]
  refine List.Forall₂.cons ?_ List.Forall₂.nil
  rw [sideDeg_selfLoop, mem_shapesOfDegree_iff]
  refine ⟨List.pairwise_singleton _ _, ?_, ?_⟩
  · intro q hq
    rw [List.mem_singleton] at hq
    subst hq
    exact ⟨le_refl 1, hs⟩
  · simp

/-- Menu-structure verification (blueprint §6 falsifiability: the statement mentions genuine
cells): the self-loop cell IS a menu cell whenever `0 < s < N`. -/
theorem selfLoopCell_mem_cellMenu {N s : ℕ} (hs : 0 < s) (hsN : s < N) :
    selfLoopCell s ∈ cellMenu s N :=
  mem_cellMenu_iff.mpr ⟨selfLoopPath s, [[(1, s)]], selfLoopPath_menuPath hs hsN,
    selfLoopShapes hs, rfl⟩

/-- The self-loop cell is CHILDLESS: its unique repeated factor has `μ·D = s·1`, which is
not `< s`, so A2 emits no child — the no-progress marker the recursion's depth cap records. -/
theorem selfLoopCell_children (s : ℕ) : (selfLoopCell s).children = [] := by
  show cellChildren s [[(1, s)]] = []
  unfold cellChildren
  simp

/-- The self-loop column ceilings: `⌈h_i⌉ = s − i`. -/
theorem ceilAt_selfLoop {s : ℕ} (hs : 0 < s) {i : ℕ} (hi : i ≤ s) :
    ceilAt (selfLoopPath s) i = s - i := by
  show (if i ≤ 0 then s
      else if i ≤ s then s - (s - 0) * (i - 0) / (s - 0)
      else ceilAt [(s, 0)] i) = s - i
  by_cases h0 : i = 0
  · subst h0
    rw [if_pos (le_refl 0)]
    omega
  · rw [if_neg (by omega), if_pos hi]
    congr 1
    simp only [Nat.sub_zero]
    exact Nat.mul_div_cancel_left i hs

theorem chainFree_selfLoop (s : ℕ) : chainFree (selfLoopPath s) = 0 := by
  show (((sidePairs (selfLoopPath s)).map fun pr => pr.2.1 - pr.1.1 - sideDeg pr)).sum = 0
  rw [show sidePairs (selfLoopPath s) = [((0, s), (s, 0))] from rfl]
  simp [sideDeg_selfLoop]

/-- Gauss sum of the self-loop ceilings: `(Σ_{i<s} (s − i)) · 2 = s(s+1)`. -/
theorem sum_ceil_selfLoop (s : ℕ) :
    (∑ i ∈ Finset.range s, (s - i)) * 2 = s * (s + 1) := by
  induction s with
  | zero => simp
  | succ n ih =>
      have hstep : ∀ i ∈ Finset.range n, n + 1 - i = (n - i) + 1 := by
        intro i hi
        rw [Finset.mem_range] at hi
        omega
      rw [Finset.sum_range_succ, Finset.sum_congr rfl hstep, Finset.sum_add_distrib,
        Finset.sum_const, Finset.card_range, smul_eq_mul, mul_one]
      have h2 : (n + 1) * (n + 1 + 1) = n * (n + 1) + 2 * (n + 1) := by ring
      omega

/-- The free-digit exponent of the self-loop cell: `s(N−1) − s(s+1)/2` — the per-column
floors `N−1−(s−i)` summed; the single full-width side has no off-pattern residue digits. -/
theorem freeExp_selfLoop {N s : ℕ} (hs : 0 < s) (hsN : s < N) :
    freeExp s N (selfLoopPath s) = s * (N - 1) - s * (s + 1) / 2 := by
  unfold freeExp
  rw [chainFree_selfLoop, Nat.add_zero]
  have hceil : ∀ i ∈ Finset.range s, N - 1 - ceilAt (selfLoopPath s) i = N - 1 - (s - i) := by
    intro i hi
    rw [Finset.mem_range] at hi
    rw [ceilAt_selfLoop hs (le_of_lt hi)]
  rw [Finset.sum_congr rfl hceil]
  have hsplit : (∑ i ∈ Finset.range s, (N - 1 - (s - i)))
      + (∑ i ∈ Finset.range s, (s - i)) = s * (N - 1) := by
    rw [← Finset.sum_add_distrib]
    have hterm : ∀ i ∈ Finset.range s, (N - 1 - (s - i)) + (s - i) = N - 1 := by
      intro i hi
      rw [Finset.mem_range] at hi
      omega
    rw [Finset.sum_congr rfl hterm, Finset.sum_const, Finset.card_range, smul_eq_mul]
  have hg := sum_ceil_selfLoop s
  omega

/-- **Deliverable 2a, the self-loop fiber card**: `(p−1) · p^(s(N−1) − s(s+1)/2)` — W4b's
`cell_card_raw` at the self-loop cell; the `(p−1)` is the residual-root (unit `c̃`) count
`shapeCount [(1,s)]`. -/
theorem card_selfLoopFiber {N s : ℕ} (hs : 0 < s) (hsN : s < N) :
    Nat.card {f : QuotientBox.monicBox p N s // InCell p f (selfLoopCell s)}
      = (p - 1) * p ^ (s * (N - 1) - s * (s + 1) / 2) := by
  have hN : 0 < N := lt_of_le_of_lt (Nat.zero_le s) hsN
  rw [show selfLoopCell s = mkCell s (selfLoopPath s) [[(1, s)]] from rfl,
    cell_card_raw p hN (selfLoopPath_menuPath hs hsN) (selfLoopShapes hs),
    freeExp_selfLoop hs hsN]
  congr 1
  show (([[(1, s)]]).map (shapeCount p)).prod = p - 1
  rw [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
  exact shapeCount_linear_pow p (by omega)

/-- The fiber card in `w`-form: exponent `s(N−1) − (w(s)+1)`, `w = L5fix.selfLoopExponent`
(`w(s) = s(s+1)/2 − 1`, the `countPivot` exponent). -/
theorem card_selfLoopFiber_w {N s : ℕ} (hs : 0 < s) (hsN : s < N) :
    Nat.card {f : QuotientBox.monicBox p N s // InCell p f (selfLoopCell s)}
      = (p - 1) * p ^ (s * (N - 1) - (L5fix.selfLoopExponent s + 1)) := by
  rw [card_selfLoopFiber p hs hsN]
  congr 2
  unfold L5fix.selfLoopExponent
  have h2 : s * (s + 1) / 2 * 2 = s * (s + 1) :=
    Nat.div_mul_cancel (even_iff_two_dvd.mp (Nat.even_mul_succ_self s))
  have h1 : 1 * 2 ≤ s * (s + 1) := Nat.mul_le_mul hs (by omega)
  omega

/-- **Deliverable 2b, division-free index form**: the self-loop fiber sits inside the cluster
box at index exactly `p^(w(s)+1)` per unit root — HNode1's `selfLoop_cost_tie` in census form,
now for the MENU fiber (all `p−1` roots together):
`card_selfLoopFiber · p^(w(s)+1) = (p−1) · card_clusterBox`. -/
theorem card_selfLoopFiber_index {N s : ℕ} (hs : 0 < s) (hsN : s < N) :
    Nat.card {f : QuotientBox.monicBox p N s // InCell p f (selfLoopCell s)}
        * p ^ (L5fix.selfLoopExponent s + 1)
      = (p - 1) * Nat.card {f : QuotientBox.monicBox p N s // IsCluster p f} := by
  have hN : 0 < N := lt_of_le_of_lt (Nat.zero_le s) hsN
  rw [card_selfLoopFiber p hs hsN, card_clusterBox p hN, mul_assoc, ← pow_add,
    HNode1.selfLoop_cost_tie N s hs hsN]

/-- Cross-check against W4d's root-refined restart fiber (`RestartEquiv.gate_A`): at `p = 2`
the unit root is unique, so the menu fiber is `(2−1)·`(the `InCellAt` fiber) — both `2`. -/
theorem crosscheck_gate_A :
    Nat.card {f : QuotientBox.monicBox 2 3 2 // InCell 2 f (selfLoopCell 2)}
      = (2 - 1) * Nat.card {f : QuotientBox.monicBox 2 3 (2 * 1) //
          RestartEquiv.InCellAt 2 3 1 2 1 f} := by
  rw [RestartEquiv.gate_A, card_selfLoopFiber 2 (by norm_num) (by norm_num)]
  norm_num

/-! ## 3. Deliverable 2: `Undecided1` and its exact census -/

/-- **The order-1 UNDECIDED set** (blueprint §6, one-step form): cluster boxes on which the
order-1 read makes NO progress — the classifier is silent (tail) or emits THE self-loop cell
(child budget = parent budget).  Defined through the genuine `classify1` (§6 falsifiability:
a shell classifier that decides everything at order 0 does NOT satisfy the census below).
Completeness window: for `s` prime and `s < N ≤ 2s` this is (numerically verified) the FULL
no-progress set; beyond it, deeper-`h` recentering cells and `D ≥ 2` residue-extension cells
join — W6 scope (see the module docstring, honesty note 3, and
`probe_deeper_selfLoop_cell`). -/
def Undecided1 {N s : ℕ} (f : QuotientBox.monicBox p N s) : Prop :=
  IsCluster p f ∧
    (classify1 p f = none ∨ classify1 p f = some (selfLoopCell s))

/-- **The disjoint split**: `undecided₁ = tail ⊔ self-loop fiber`.  Disjointness is free from
the classifier encoding (`none ≠ some`); semantically, self-loop fibers are READABLE
(`inCell_isReadable`), tails are not. -/
theorem card_undecided1_split {N s : ℕ} (hN : 0 < N) :
    Nat.card {f : QuotientBox.monicBox p N s // Undecided1 p f}
      = Nat.card {f : QuotientBox.monicBox p N s // IsTail p f}
        + Nat.card {f : QuotientBox.monicBox p N s // InCell p f (selfLoopCell s)} := by
  have hiff : ∀ f : QuotientBox.monicBox p N s,
      Undecided1 p f ↔ (IsTail p f ∨ InCell p f (selfLoopCell s)) := by
    intro f
    constructor
    · rintro ⟨hcl, hnone | hsome⟩
      · exact Or.inl ⟨hcl, hnone⟩
      · exact Or.inr ((classify1_eq_some_iff p).mp hsome)
    · rintro (⟨hcl, hnone⟩ | hin)
      · exact ⟨hcl, Or.inl hnone⟩
      · exact ⟨(inCell_isReadable p hN hin).1, Or.inr ((classify1_eq_some_iff p).mpr hin)⟩
  rw [Nat.card_congr (Equiv.subtypeEquivRight hiff)]
  refine card_subtype_or_disjoint _ _ ?_
  rintro f ⟨⟨_, hnone⟩, hin⟩
  have hsome := (classify1_eq_some_iff p).mpr hin
  rw [hnone] at hsome
  exact Option.some_ne_none _ hsome.symm

/-- **Deliverable 2, the EXACT two-term census** (the `≤` form of the task sheet holds with
equality): `card_undecided₁ = p^((s−1)(N−1)) + (p−1)·p^(s(N−1) − s(s+1)/2)`.
Gates: `(2,2,3)`: `6 = 4 + 2` of `16`; `(2,2,4)`: `16 = 8 + 8` of `64`;
`(2,3,4)`: `72 = 64 + 8` of `512`; `(3,2,3)`: `15 = 9 + 6` of `81`. -/
theorem card_undecided1 {N s : ℕ} (hs : 0 < s) (hsN : s < N) :
    Nat.card {f : QuotientBox.monicBox p N s // Undecided1 p f}
      = p ^ ((s - 1) * (N - 1)) + (p - 1) * p ^ (s * (N - 1) - s * (s + 1) / 2) := by
  have hN : 0 < N := lt_of_le_of_lt (Nat.zero_le s) hsN
  rw [card_undecided1_split p hN, card_tail p hN hs, card_selfLoopFiber p hs hsN]

/-- **Deliverable 2, the sharp division-free INDEX identity** (the true replacement of the
task-sheet `min`-bound, which is FALSE — `probe_naive_min_bound_fails`):

    `card_undecided₁ · p^(N−1) · p^(w(s)+1) = (p^(w(s)+1) + (p−1)·p^(N−1)) · card_clusterBox`. -/
theorem card_undecided1_index {N s : ℕ} (hs : 0 < s) (hsN : s < N) :
    Nat.card {f : QuotientBox.monicBox p N s // Undecided1 p f}
        * (p ^ (N - 1) * p ^ (L5fix.selfLoopExponent s + 1))
      = (p ^ (L5fix.selfLoopExponent s + 1) + (p - 1) * p ^ (N - 1))
        * Nat.card {f : QuotientBox.monicBox p N s // IsCluster p f} := by
  have hN : 0 < N := lt_of_le_of_lt (Nat.zero_le s) hsN
  have h1 := card_tail_index p hN hs
  have h2 := card_selfLoopFiber_index p hs hsN
  rw [card_undecided1_split p hN]
  set T := Nat.card {f : QuotientBox.monicBox p N s // IsTail p f} with hT
  set S := Nat.card {f : QuotientBox.monicBox p N s // InCell p f (selfLoopCell s)} with hS
  set C := Nat.card {f : QuotientBox.monicBox p N s // IsCluster p f} with hC
  calc (T + S) * (p ^ (N - 1) * p ^ (L5fix.selfLoopExponent s + 1))
      = (T * p ^ (N - 1)) * p ^ (L5fix.selfLoopExponent s + 1)
        + (S * p ^ (L5fix.selfLoopExponent s + 1)) * p ^ (N - 1) := by ring
    _ = C * p ^ (L5fix.selfLoopExponent s + 1) + ((p - 1) * C) * p ^ (N - 1) := by
        rw [h1, h2]
    _ = (p ^ (L5fix.selfLoopExponent s + 1) + (p - 1) * p ^ (N - 1)) * C := by ring

/-- The corrected `min`-form index BOUND (the task-sheet exponent `w+1` is too strong; `w`
with the doubled right side is the clean true form):
`card_undecided₁ · p^(min(N−1)(w(s))) ≤ 2 · card_clusterBox`. -/
theorem card_undecided1_min_bound {N s : ℕ} (hs : 0 < s) (hsN : s < N) :
    Nat.card {f : QuotientBox.monicBox p N s // Undecided1 p f}
        * p ^ (min (N - 1) (L5fix.selfLoopExponent s))
      ≤ 2 * Nat.card {f : QuotientBox.monicBox p N s // IsCluster p f} := by
  have hN : 0 < N := lt_of_le_of_lt (Nat.zero_le s) hsN
  have hp1 : 1 ≤ p := hp.out.one_lt.le
  have hppos : 0 < p := hp.out.pos
  have h1 := card_tail_index p hN hs
  have h2 := card_selfLoopFiber_index p hs hsN
  rw [card_undecided1_split p hN, add_mul]
  set T := Nat.card {f : QuotientBox.monicBox p N s // IsTail p f} with hTdef
  set S := Nat.card {f : QuotientBox.monicBox p N s // InCell p f (selfLoopCell s)} with hSdef
  set C := Nat.card {f : QuotientBox.monicBox p N s // IsCluster p f} with hCdef
  set m := min (N - 1) (L5fix.selfLoopExponent s) with hm
  have hT : T * p ^ m ≤ C :=
    le_trans (Nat.mul_le_mul_left T (Nat.pow_le_pow_right hp1 (min_le_left _ _))) (le_of_eq h1)
  have hS : S * p ^ m * p ≤ C * p := by
    calc S * p ^ m * p = S * p ^ (m + 1) := by rw [pow_succ, mul_assoc]
      _ ≤ S * p ^ (L5fix.selfLoopExponent s + 1) :=
          Nat.mul_le_mul_left S (Nat.pow_le_pow_right hp1 (by omega))
      _ = (p - 1) * C := h2
      _ ≤ p * C := Nat.mul_le_mul_right C (by omega)
      _ = C * p := Nat.mul_comm _ _
  have hS' : S * p ^ m ≤ C := Nat.le_of_mul_le_mul_right hS hppos
  omega

/-! ## 4. Census gates (the W0/W5 numbers, proved) -/

/-- Gate `(p,s,N) = (2,2,3)`: tail `4`. -/
theorem gate_tail_s2N3 : Nat.card {f : QuotientBox.monicBox 2 3 2 // IsTail 2 f} = 4 := by
  rw [card_tail 2 (by norm_num) (by norm_num)]
  norm_num

/-- Gate `(2,2,3)`: self-loop fiber `2` (W0's cell S2C2). -/
theorem gate_selfLoop_s2N3 :
    Nat.card {f : QuotientBox.monicBox 2 3 2 // InCell 2 f (selfLoopCell 2)} = 2 := by
  rw [card_selfLoopFiber 2 (by norm_num) (by norm_num)]
  norm_num

/-- **Gate `(2,2,3)`: undecided `6 = 4 + 2` of the `16` cluster boxes** (W0 census). -/
theorem gate_undecided_s2N3 :
    Nat.card {f : QuotientBox.monicBox 2 3 2 // Undecided1 2 f} = 6 := by
  rw [card_undecided1 2 (by norm_num) (by norm_num)]
  norm_num

/-- Gate `(2,2,4)`: undecided `16 = 8 + 8` of `64` (tail `8`, self-loop fiber `8` — the
latter also = `card_restart_fiber` at `(2,4,1,2)`: `2^(2·3 − 3) = 8`). -/
theorem gate_undecided_s2N4 :
    Nat.card {f : QuotientBox.monicBox 2 4 2 // Undecided1 2 f} = 16 := by
  rw [card_undecided1 2 (by norm_num) (by norm_num)]
  norm_num

/-- Gate `(2,3,4)`: undecided `72 = 64 + 8` of `512`. -/
theorem gate_undecided_s3N4 :
    Nat.card {f : QuotientBox.monicBox 2 4 3 // Undecided1 2 f} = 72 := by
  rw [card_undecided1 2 (by norm_num) (by norm_num)]
  norm_num

/-- Gate `(3,2,3)`: undecided `15 = 9 + 6` of `81` — note the `(p−1) = 2` root multiplicity
in the self-loop term. -/
theorem gate_undecided_p3 :
    Nat.card {f : QuotientBox.monicBox 3 3 2 // Undecided1 3 f} = 15 := by
  rw [card_undecided1 3 (by norm_num) (by norm_num)]
  norm_num

/-- **FALSIFIABILITY PROBE 1**: the task-sheet index bound
`undecided₁ · p^(min(N−1)(w+1)) ≤ cluster` is FALSE at the gate: `6 · 2^min(2,3) = 24 > 16`. -/
theorem probe_naive_min_bound_fails :
    ¬ (Nat.card {f : QuotientBox.monicBox 2 3 2 // Undecided1 2 f}
          * 2 ^ (min (3 - 1) (L5fix.selfLoopExponent 2 + 1))
        ≤ Nat.card {f : QuotientBox.monicBox 2 3 2 // IsCluster 2 f}) := by
  rw [gate_undecided_s2N3, sanity_cluster_s2]
  norm_num [L5fix.selfLoopExponent]

/-- **FALSIFIABILITY PROBE 3** (the completeness WINDOW of `Undecided1` is real): at
`(s, N) = (2, 5)` — beyond `N ≤ 2s` — the F5 menu contains a SECOND childless-but-undecided
cell, the `h = 2` recentering cell `(0,4) → (2,0)` with shape `(1,2)`.  Its fiber mass is the
`k = 2` term `p^{−2(w+1)}` of the W6 tower; `Undecided1` deliberately tracks only the `h = 1`
cell. -/
theorem probe_deeper_selfLoop_cell :
    mkCell 2 [(0, 4), (2, 0)] [[(1, 2)]] ∈ cellMenu 2 5
      ∧ (mkCell 2 [(0, 4), (2, 0)] [[(1, 2)]]).children = []
      ∧ mkCell 2 [(0, 4), (2, 0)] [[(1, 2)]] ≠ selfLoopCell 2 := by
  refine ⟨?_, rfl, ?_⟩
  · refine mem_cellMenu_iff.mpr ⟨[(0, 4), (2, 0)], [[(1, 2)]], ?_, ?_, rfl⟩
    · exact ⟨4, (2, 0), [], rfl, by norm_num, by norm_num, by norm_num, by norm_num,
        ChainOK.nil rfl rfl⟩
    · show List.Forall₂ _ [[(1, 2)]] [((0, 4), (2, 0))]
      exact List.Forall₂.cons (by decide) List.Forall₂.nil
  · intro h
    have h4 : polyHeight (mkCell 2 [(0, 4), (2, 0)] [[(1, 2)]]).polygon 0
        = polyHeight (selfLoopCell 2).polygon 0 := by rw [h]
    exact absurd h4 (by decide)

/-! ## 5. Deliverable 3: the density statements over ℚ and the honest vanishing -/

/-- The tail mass fraction of the level-`N` cluster box. -/
def tailDensity (s N : ℕ) : ℚ :=
  (Nat.card {f : QuotientBox.monicBox p N s // IsTail p f} : ℚ)
    / (Nat.card {f : QuotientBox.monicBox p N s // IsCluster p f} : ℚ)

/-- The order-1 undecided mass fraction of the level-`N` cluster box. -/
def undecidedDensity (s N : ℕ) : ℚ :=
  (Nat.card {f : QuotientBox.monicBox p N s // Undecided1 p f} : ℚ)
    / (Nat.card {f : QuotientBox.monicBox p N s // IsCluster p f} : ℚ)

theorem tailDensity_eq {N s : ℕ} (hN : 0 < N) (hs : 0 < s) :
    tailDensity p s N = ((p : ℚ) ^ (N - 1))⁻¹ := by
  have hp0 : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hp.out.ne_zero
  have e1 : s * (N - 1) = (s - 1) * (N - 1) + (N - 1) := by
    obtain ⟨s', rfl⟩ : ∃ s', s = s' + 1 := ⟨s - 1, by omega⟩
    rw [Nat.add_sub_cancel, Nat.succ_mul]
  unfold tailDensity
  rw [card_tail p hN hs, card_clusterBox p hN]
  push_cast
  have hden : (p : ℚ) ^ (s * (N - 1))
      = (p : ℚ) ^ ((s - 1) * (N - 1)) * (p : ℚ) ^ (N - 1) := by
    rw [← pow_add, ← e1]
  rw [hden, ← div_div, div_self (pow_ne_zero _ hp0), one_div]

/-- **Deliverable 3, the EXACT one-step drainage identity over ℚ**:

    `undecidedDensity = p^{−(N−1)} + (p−1)·p^{−(w(s)+1)}`.

The first term (the TAIL mass) dies as `N → ∞`; the second (the self-loop mass at ONE order)
is `N`-INDEPENDENT — see `tendsto_undecidedDensity` and honesty note 4 of the module
docstring.  At `p = 2` this is exactly the task-sheet form `p^{−(N−1)} + p^{−(w+1)}`
(`gate_density_tight_s2N3`); for `p ≥ 3` the `(p−1)` factor is REAL (`probe_p3_mass`). -/
theorem undecidedDensity_eq {N s : ℕ} (hs : 0 < s) (hsN : s < N) :
    undecidedDensity p s N
      = ((p : ℚ) ^ (N - 1))⁻¹
        + ((p : ℚ) - 1) * ((p : ℚ) ^ (L5fix.selfLoopExponent s + 1))⁻¹ := by
  have hN : 0 < N := lt_of_le_of_lt (Nat.zero_le s) hsN
  have hp0 : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hp.out.ne_zero
  have hp1 : 1 ≤ p := hp.out.one_lt.le
  have e1 : s * (N - 1) = (s - 1) * (N - 1) + (N - 1) := by
    obtain ⟨s', rfl⟩ : ∃ s', s = s' + 1 := ⟨s - 1, by omega⟩
    rw [Nat.add_sub_cancel, Nat.succ_mul]
  have e2 : s * (N - 1)
      = (s * (N - 1) - s * (s + 1) / 2) + (L5fix.selfLoopExponent s + 1) :=
    (HNode1.selfLoop_cost_tie N s hs hsN).symm
  unfold undecidedDensity
  rw [card_undecided1 p hs hsN, card_clusterBox p hN]
  push_cast [Nat.cast_sub hp1]
  rw [add_div]
  congr 1
  · have hden : (p : ℚ) ^ (s * (N - 1))
        = (p : ℚ) ^ ((s - 1) * (N - 1)) * (p : ℚ) ^ (N - 1) := by
      rw [← pow_add, ← e1]
    rw [hden, ← div_div, div_self (pow_ne_zero _ hp0), one_div]
  · have hden : (p : ℚ) ^ (s * (N - 1))
        = (p : ℚ) ^ (s * (N - 1) - s * (s + 1) / 2)
          * (p : ℚ) ^ (L5fix.selfLoopExponent s + 1) := by
      rw [← pow_add, ← e2]
    rw [hden, ← div_div, mul_div_assoc, div_self (pow_ne_zero _ hp0), mul_one,
      div_eq_mul_inv]

/-- **TIGHTNESS at the gate `(2,2,3)`** (the falsifiability probe of the task sheet): the
density is EXACTLY `2^{−2} + 2^{−3} = 3/8` — the prompt-form bound is attained. -/
theorem gate_density_tight_s2N3 :
    undecidedDensity 2 2 3 = ((2 : ℚ) ^ 2)⁻¹ + ((2 : ℚ) ^ 3)⁻¹
      ∧ undecidedDensity 2 2 3 = 3 / 8 := by
  constructor <;>
    rw [undecidedDensity_eq 2 (by norm_num) (by norm_num)] <;>
    norm_num [L5fix.selfLoopExponent]

/-- **FALSIFIABILITY PROBE 2**: at `p = 3` the task-sheet constant `p^{−(w+1)}` FAILS —
the density at `(3,2,3)` is `1/9 + 2/27 = 5/27 > 4/27 = 3^{−2} + 3^{−3}`.  The `(p−1)`
residual-root multiplicity in `undecidedDensity_eq` is genuine. -/
theorem probe_p3_mass :
    ¬ (undecidedDensity 3 2 3 ≤ ((3 : ℚ) ^ 2)⁻¹ + ((3 : ℚ) ^ 3)⁻¹) := by
  rw [undecidedDensity_eq 3 (by norm_num) (by norm_num)]
  norm_num [L5fix.selfLoopExponent]

/-- The true general-`p` one-step BOUND (task-sheet shape, corrected exponent):
`undecidedDensity ≤ p^{−(N−1)} + p^{−w(s)}` (from `p − 1 ≤ p`). -/
theorem undecidedDensity_le {N s : ℕ} (hs : 0 < s) (hsN : s < N) :
    undecidedDensity p s N
      ≤ ((p : ℚ) ^ (N - 1))⁻¹ + ((p : ℚ) ^ L5fix.selfLoopExponent s)⁻¹ := by
  have hpQ : (0 : ℚ) < (p : ℚ) := by exact_mod_cast hp.out.pos
  rw [undecidedDensity_eq p hs hsN]
  refine add_le_add le_rfl ?_
  rw [← div_eq_mul_inv, inv_eq_one_div,
    div_le_div_iff₀ (pow_pos hpQ _) (pow_pos hpQ _)]
  calc ((p : ℚ) - 1) * (p : ℚ) ^ L5fix.selfLoopExponent s
      ≤ (p : ℚ) * (p : ℚ) ^ L5fix.selfLoopExponent s :=
        mul_le_mul_of_nonneg_right (by linarith) (le_of_lt (pow_pos hpQ _))
    _ = 1 * (p : ℚ) ^ (L5fix.selfLoopExponent s + 1) := by
        rw [one_mul, pow_succ]
        ring

/-- `w(s) ≥ 2` for `s ≥ 2` (so `w(s)+1 ≥ 3`): the `s`-uniform floor of the self-loop cost. -/
theorem selfLoopExponent_ge {s : ℕ} (hs2 : 2 ≤ s) : 2 ≤ L5fix.selfLoopExponent s := by
  unfold L5fix.selfLoopExponent
  have h3 : 2 * 3 ≤ s * (s + 1) := Nat.mul_le_mul hs2 (by omega)
  have h2 : s * (s + 1) / 2 * 2 = s * (s + 1) :=
    Nat.div_mul_cancel (even_iff_two_dvd.mp (Nat.even_mul_succ_self s))
  omega

/-- The one-step self-loop mass is `s`-UNIFORMLY small: `(p−1)·p^{−(w(s)+1)} ≤ p^{−2} ≤ 1/4`
for all `s ≥ 2`.  (`N`-independent though: one order of reading cannot drain it — W6.) -/
theorem selfLoopMass_le {s : ℕ} (hs2 : 2 ≤ s) :
    ((p : ℚ) - 1) * ((p : ℚ) ^ (L5fix.selfLoopExponent s + 1))⁻¹ ≤ ((p : ℚ) ^ 2)⁻¹ := by
  have hpQ : (0 : ℚ) < (p : ℚ) := by exact_mod_cast hp.out.pos
  have hw : 3 ≤ L5fix.selfLoopExponent s + 1 := by
    have := selfLoopExponent_ge hs2
    omega
  have hpow : ((p : ℚ)) ^ 3 ≤ (p : ℚ) ^ (L5fix.selfLoopExponent s + 1) := by
    have hnat : p ^ 3 ≤ p ^ (L5fix.selfLoopExponent s + 1) :=
      Nat.pow_le_pow_right hp.out.one_lt.le hw
    exact_mod_cast hnat
  rw [← div_eq_mul_inv, inv_eq_one_div,
    div_le_div_iff₀ (pow_pos hpQ _) (pow_pos hpQ _)]
  calc ((p : ℚ) - 1) * (p : ℚ) ^ 2 ≤ (p : ℚ) * (p : ℚ) ^ 2 :=
        mul_le_mul_of_nonneg_right (by linarith) (le_of_lt (pow_pos hpQ _))
    _ = (p : ℚ) ^ 3 := by ring
    _ ≤ (p : ℚ) ^ (L5fix.selfLoopExponent s + 1) := hpow
    _ = 1 * (p : ℚ) ^ (L5fix.selfLoopExponent s + 1) := (one_mul _).symm

/-- `p^{−(N−1)} → 0` over `N` — the engine of the tail vanishing. -/
theorem tendsto_inv_pow_pred :
    Tendsto (fun N : ℕ => ((p : ℚ) ^ (N - 1))⁻¹) atTop (nhds 0) := by
  have hp1 : (1 : ℚ) < (p : ℚ) := by exact_mod_cast hp.out.one_lt
  have h0 : Tendsto (fun n : ℕ => ((p : ℚ)⁻¹) ^ n) atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity) (inv_lt_one_of_one_lt₀ hp1)
  have h1 := h0.comp (tendsto_sub_atTop_nat 1)
  refine h1.congr fun N => ?_
  simp [Function.comp, inv_pow]

/-- **Deliverable 3a — THE TAIL VANISHES**: `tailDensity → 0` as `N → ∞` (for every fixed
budget `s ≥ 1`).  This is the part of the order-1 undecided mass that level-refinement alone
kills. -/
theorem tendsto_tailDensity_zero (s : ℕ) (hs : 0 < s) :
    Tendsto (fun N => tailDensity p s N) atTop (nhds 0) := by
  refine (tendsto_inv_pow_pred p).congr' ?_
  filter_upwards [eventually_ge_atTop 1] with N hN
  rw [tailDensity_eq p (by omega) hs]

/-- **Deliverable 3b — the HONEST one-step limit**: the full order-1 undecided density tends
to the NONZERO, `N`-independent self-loop mass `(p−1)·p^{−(w(s)+1)}`:

    `undecidedDensity p s N  ⟶  (p−1)·p^{−(w(s)+1)}`   as `N → ∞`.

The one-step census does NOT vanish: one order of reading drains the tail but leaves the
self-loop coset untouched (its index in the cluster box is level-independent —
`card_selfLoopFiber_index`).  Genuine vanishing requires the ORDER-TOWER iteration
(self-loop → recenter → next order → its own drainage): after `k` orders the surviving
self-loop mass costs `p^{−k(w(s)+1)}` (numerically visible already at one order as the
deeper-`h` cells, `probe_deeper_selfLoop_cell`), summing to the `countPivot` geometric
factor `1/(1 − q^{−w})` of the omCount recursion.  That iteration is W6 scope; we state
here exactly what one order proves. -/
theorem tendsto_undecidedDensity (s : ℕ) (hs : 0 < s) :
    Tendsto (fun N => undecidedDensity p s N) atTop
      (nhds (((p : ℚ) - 1) * ((p : ℚ) ^ (L5fix.selfLoopExponent s + 1))⁻¹)) := by
  have h1 : Tendsto (fun N : ℕ => ((p : ℚ) ^ (N - 1))⁻¹
      + ((p : ℚ) - 1) * ((p : ℚ) ^ (L5fix.selfLoopExponent s + 1))⁻¹) atTop
      (nhds (0 + ((p : ℚ) - 1) * ((p : ℚ) ^ (L5fix.selfLoopExponent s + 1))⁻¹)) :=
    (tendsto_inv_pow_pred p).add tendsto_const_nhds
  rw [zero_add] at h1
  refine h1.congr' ?_
  filter_upwards [eventually_ge_atTop (s + 1)] with N hN
  rw [undecidedDensity_eq p hs (by omega)]

end

end LeanUrat.OM.Drainage
