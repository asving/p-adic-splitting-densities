/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.OM.CellMenu
import LeanUrat.OM.CellCard
import LeanUrat.OM.LevelNCount

/-!
# StratumOrder1 — the genuine order-1 stratum count and its CellCard bridge (S2 sub-piece (i))

**Provenance.** `notes/ASSEMBLY_BLUEPRINT.md` §S2 sub-structure `(i)`: the genuine order-1
stratum-count bridge — the prerequisite of the S2 `h_node` discharge.  Where `M8.stratumCount`
threads the *schematic* per-level `rawCount` (a free classifier symbol), the *genuine* order-1 count
must go through the concrete order-1 menu classifier `CellMenu.classify1`.  This module establishes
that genuine count, bridges it to the CellCard `InCell` fibers, and states its partition — the shape
the `h_node` limit consumes.  It touches NEITHER `rawCount`/`RealInstance` NOR the schematic
classifier (the S3a wiring is a separate later step); it is a purely ADDITIVE new module composing
EXISTING proven lemmas.

**The four deliverables.**
* `stratumCount1 s N c` — `Nat.card {f ∈ monicBox p N s | classify1 p f = some c}`, the genuine
  order-1 stratum count over `CellMenu.classify1` (mirrors `M8.shapeFiberCount` but over the genuine
  classifier).
* `stratumCount1_eq_cellCard` — **THE BRIDGE**: `stratumCount1 s N c = #{f | InCell p f c}`, an
  immediate subtype congruence on `classify1_eq_some_iff`; and `stratumCount1_eq_closed`:
  `= prodSC p sh · p ^ freeExp s N P` for `c = mkCell s P sh` (compose with `CellCard.cell_card_raw`).
* `stratumCount1_tail_zero` — the tail (`classify1 = none`, unreadable `a₀`) count is the dead-`a₀`
  card `p^((s−1)(N−1))` (`CellCard.card_cluster_dead`), the drainage input at order 1.
* `stratumCount1_partition` — `∑_{c ∈ cellMenu s N} stratumCount1 s N c + tailCount1 s N = p^(s(N−1))`,
  the genuine order-1 stratum PARTITION (analogue of the order-0 `decidedRaw` sum): decided mass
  (`CellCard.cell_partition` = `#readable`) plus undecided tail = the whole cluster box
  (`CellCard.card_clusterBox`).

**W0 gates** (`p = 2, N = 3`, `SUMMARY.md` census): the per-cell genuine order-1 counts
S2C1 ↦ 8 (slope −1/2), S2C2 ↦ 2 (self-loop), S2C3 ↦ 2, split ↦ 0, tail ↦ 4; and the partition sum
= 16 (`s=2`), 64 (`s=3`), 256 (`s=4`) cluster-box cards.
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

namespace LeanUrat.OM.StratumOrder1

open LeanUrat LeanUrat.OM
open LeanUrat.OM.CellMenu
open LeanUrat.OM.OMCountV2 (NodeConfig)

open scoped Classical

section Count

variable (p : ℕ) [hp : Fact p.Prime]

/-! ## 1. The genuine order-1 stratum count -/

/-- **The genuine order-1 stratum count** over `CellMenu.classify1`.  `stratumCount1 s N c` is the
number of monic degree-`s` cosets mod `p^N` whose genuine order-1 menu classifier `classify1`
returns `some c`.  This mirrors `M8.shapeFiberCount` but over the GENUINE order-1 classifier
`classify1` (not the schematic `rawCount`). -/
noncomputable def stratumCount1 (s N : ℕ) (c : NodeConfig) : ℕ :=
  Nat.card {f : QuotientBox.monicBox p N s // classify1 p f = some c}

/-! ## 2. The bridge to the CellCard `InCell` fibers -/

/-- **THE BRIDGE (S2 sub-piece (i)).** The genuine order-1 stratum count equals the CellCard
`InCell`-fiber count of the same cell.  Immediate from `classify1_eq_some_iff`
(`classify1 p f = some c ↔ InCell p f c`): the two subtypes coincide, so their `Nat.card`s do. -/
theorem stratumCount1_eq_cellCard (s N : ℕ) (c : NodeConfig) :
    stratumCount1 p s N c = Nat.card {f : QuotientBox.monicBox p N s // InCell p f c} := by
  unfold stratumCount1
  exact Nat.card_congr (Equiv.subtypeEquivRight fun f => classify1_eq_some_iff p)

/-- **The closed form** for the genuine order-1 stratum count of a full menu cell
`c = mkCell s P sh`: composing the bridge with `CellCard.cell_card_raw`, it equals
`prodSC p sh · p ^ freeExp s N P` — the per-side residual-shape count times the free-digit
exponent. -/
theorem stratumCount1_eq_closed {s N : ℕ} (hN : 0 < N) {P : List (ℕ × ℕ)}
    (hP : MenuPath s N P) {sh : List (List (ℕ × ℕ))} (hsh : ShapesFor P sh) :
    stratumCount1 p s N (mkCell s P sh)
      = CellCard.prodSC p sh * p ^ CellCard.freeExp s N P := by
  rw [stratumCount1_eq_cellCard, CellCard.cell_card_raw p hN hP hsh]

/-! ## 3. The tail (undecided, unreadable `a₀`) -/

/-- **The order-1 tail count**: the number of cluster cosets whose classifier is undecided
(`classify1 = none`) — the drainage input at order 1. -/
noncomputable def tailCount1 (s N : ℕ) : ℕ :=
  Nat.card {f : QuotientBox.monicBox p N s // CellCard.IsCluster p f ∧ classify1 p f = none}

/-- Within the cluster box, `classify1 = none` is EXACTLY the dead-`a₀` (unreadable) tail:
`classify1 f = none ↔ ¬ (vOf p f 0 < N)`. -/
theorem cluster_classify1_none_iff {s N : ℕ} (hN : 0 < N) (hs : 0 < s)
    {f : QuotientBox.monicBox p N s} (hcl : CellCard.IsCluster p f) :
    classify1 p f = none ↔ ¬ vOf p f 0 < N := by
  constructor
  · intro hnone hread
    -- readable ⟹ classify1 is some, contradicting none
    have := classify1_isSome p hN hs f hcl hread
    rw [hnone] at this
    exact absurd this (by simp)
  · intro hnread
    -- unreadable ⟹ vOf f 0 = N ⟹ coeff 0 = 0 ⟹ tail
    have hle := CellCard.vOf_le p hN f 0
    have hval : vOf p f 0 = N := by omega
    have hcoeff : (f.1).coeff 0 = 0 := by
      by_contra hne
      have hlt := PadicLift.zmodValuation_lt p hN hne
      rw [CellCard.vOf_eq] at hval
      omega
    exact classify1_eq_none_of_tail p hN hcoeff

/-- **`stratumCount1_tail_zero`** (the drainage input at order 1): the order-1 tail count equals the
dead-`a₀` cluster card `p^((s−1)(N−1))` (`CellCard.card_cluster_dead`). -/
theorem stratumCount1_tail_zero {s N : ℕ} (hN : 0 < N) (hs : 0 < s) :
    tailCount1 p s N = p ^ ((s - 1) * (N - 1)) := by
  unfold tailCount1
  rw [← CellCard.card_cluster_dead p hN hs]
  refine Nat.card_congr (Equiv.subtypeEquivRight fun f => ?_)
  constructor
  · rintro ⟨hcl, hnone⟩
    exact ⟨hcl, (cluster_classify1_none_iff p hN hs hcl).mp hnone⟩
  · rintro ⟨hcl, hdead⟩
    exact ⟨hcl, (cluster_classify1_none_iff p hN hs hcl).mpr hdead⟩

/-! ## 4. The order-1 stratum PARTITION -/

/-- **THE ORDER-1 STRATUM PARTITION** (the genuine analogue of the order-0 `decidedRaw` sum): the
menu-list sum of the genuine order-1 stratum counts, plus the tail count, equals the full cluster
box card `p^(s(N−1))`.  This is the shape the `h_node` limit consumes: the decided mass
(`∑_{c ∈ cellMenu} stratumCount1`) is `#readable` (`CellCard.cell_partition`), and the tail is the
undecided dead-`a₀` mass, together partitioning the whole cluster box (`CellCard.card_clusterBox`). -/
theorem stratumCount1_partition {s N : ℕ} (hN : 0 < N) (hs : 0 < s) :
    ((cellMenu s N).map (fun c => stratumCount1 p s N c)).sum + tailCount1 p s N
      = p ^ (s * (N - 1)) := by
  -- The decided part = #readable via the bridge + CellCard.cell_partition.
  have hdecided : ((cellMenu s N).map (fun c => stratumCount1 p s N c)).sum
      = Nat.card {f : QuotientBox.monicBox p N s // CellCard.IsReadable p f} := by
    rw [CellCard.cell_partition p hN hs]
    congr 1
    exact List.map_congr_left fun c _ => stratumCount1_eq_cellCard p s N c
  rw [hdecided, stratumCount1_tail_zero p hN hs, ← CellCard.card_cluster_dead p hN hs,
    ← CellCard.card_clusterBox p (s := s) (N := N) hN]
  -- readable = cluster ∧ (v_p a₀ < N); dead = cluster ∧ ¬(...); they partition the cluster box.
  have hsplit := CellCard.card_subtype_and_compl (α := QuotientBox.monicBox p N s)
    (CellCard.IsCluster p) (fun f => vOf p f 0 < N)
  have he : Nat.card {f : QuotientBox.monicBox p N s // CellCard.IsReadable p f}
      = Nat.card {f : QuotientBox.monicBox p N s // CellCard.IsCluster p f ∧ vOf p f 0 < N} := rfl
  omega

end Count

/-! ## 5. Numeric gates: the W0 per-cell census over the GENUINE classifier -/

section Gates

/-- **W0 GATE S2C1** (slope −1/2, shape `{(1,1)}`): genuine order-1 stratum count `8`. -/
theorem gate_stratum_S2C1 :
    stratumCount1 2 2 3 (mkCell 2 [(0, 1), (2, 0)] [[(1, 1)]]) = 8 := by
  rw [stratumCount1_eq_cellCard]
  exact CellCard.gate_card_S2C1

/-- **W0 GATE S2C2** (the SELF-LOOP cell, slope −1, shape `{(1,2)}`): genuine order-1 count `2`. -/
theorem gate_stratum_S2C2 :
    stratumCount1 2 2 3 (mkCell 2 [(0, 2), (2, 0)] [[(1, 2)]]) = 2 := by
  rw [stratumCount1_eq_cellCard]
  exact CellCard.gate_card_S2C2

/-- **W0 GATE S2C3** (slope −1, inert-quadratic shape `{(2,1)}`): genuine order-1 count `2`. -/
theorem gate_stratum_S2C3 :
    stratumCount1 2 2 3 (mkCell 2 [(0, 2), (2, 0)] [[(2, 1)]]) = 2 := by
  rw [stratumCount1_eq_cellCard]
  exact CellCard.gate_card_S2C3

/-- **W0 GATE, split cell** (readable-but-unhit at `p = 2`): genuine order-1 count `0`. -/
theorem gate_stratum_S2split :
    stratumCount1 2 2 3 (mkCell 2 [(0, 2), (2, 0)] [[(1, 1), (1, 1)]]) = 0 := by
  rw [stratumCount1_eq_cellCard]
  exact CellCard.gate_card_S2split

/-- **W0 GATE, order-1 tail** (`s = 2`): the dead-`a₀` count is `4 = 2^((2−1)(3−1))`. -/
theorem gate_tail_s2 : tailCount1 2 2 3 = 4 := by
  rw [stratumCount1_tail_zero 2 (by norm_num) (by norm_num)]; norm_num

/-- **W0 GATE, the order-1 partition** at `s = 2`: `8 + 2 + 2 + 0` decided (= 12 readable) plus
`4` tail equals the `16`-element cluster box. -/
theorem gate_partition_s2 :
    ((cellMenu 2 3).map (fun c => stratumCount1 2 2 3 c)).sum + tailCount1 2 2 3 = 16 := by
  rw [stratumCount1_partition 2 (by norm_num) (by norm_num)]; norm_num

theorem gate_partition_s3 :
    ((cellMenu 3 3).map (fun c => stratumCount1 2 3 3 c)).sum + tailCount1 2 3 3 = 64 := by
  rw [stratumCount1_partition 2 (by norm_num) (by norm_num)]; norm_num

theorem gate_partition_s4 :
    ((cellMenu 4 3).map (fun c => stratumCount1 2 4 3 c)).sum + tailCount1 2 4 3 = 256 := by
  rw [stratumCount1_partition 2 (by norm_num) (by norm_num)]; norm_num

/-- The decided menu sum reproduces W0's `s = 2` per-cell census `8 + 0 + 2 + 2` = 12. -/
theorem gate_decided_sum_s2 :
    ((cellMenu 2 3).map (fun c => stratumCount1 2 2 3 c)).sum = 8 + (0 + (2 + (2 + 0))) := by
  have hcong : (cellMenu 2 3).map (fun c => stratumCount1 2 2 3 c)
      = (cellMenu 2 3).map (fun c => Nat.card {f : QuotientBox.monicBox 2 3 2 // InCell 2 f c}) :=
    List.map_congr_left fun c _ => stratumCount1_eq_cellCard 2 2 3 c
  rw [hcong]
  exact CellCard.consistency_cells_s2

end Gates

end LeanUrat.OM.StratumOrder1
