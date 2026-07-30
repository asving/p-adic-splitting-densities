/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import LeanUrat.MovesT.Defs

/-! # SYN-C2 — `ReadLocality`: THE one level-locality kernel row

CONSOLIDATION UNIT **SYN-C2** (synthesis pass 1, C2/N2;
`lean/notes/SYNTHESIS_PASS1_2026-07-30.md` §C2, RATIFIED at
`lean/notes/BRIDGE_ADJUDICATIONS_2026-07-30.md` "SYNTHESIS PASS 1
ADJUDICATIONS": "ONE ReadLocality kernel row (chart_pin + cross-level child
locality); TransferRow (BridgeD5_transferRow) and StableInputs (TV_B2) become
derived lemmas — consolidation unit SYN-C2 assigned; theoremU's honesty
surface names the kernel once").

THE ONE OPEN KERNEL: the same open mathematics — "the tree model's reads at
working level N′ depend only on the first n·N box digits once the tree's
threshold is ≤ N" (the note's Thm 2.1 / D4R.4 / TB-CAP face, owner
**HC-2/D4R0K**, MOVES 7566–7570) — was being typed as THREE premise surfaces:
`MovesT.treeN_stable`'s fenced sorry (E11_treeN.lean), TV-B2's `StableInputs`,
and IB-D5's `TransferRow`.  This module types it ONCE; the other two are now
DERIVED (this file + TV_B2.lean + BridgeD5_transferRow.lean carry the
derivations), and the fence record on `treeN_stable` names this row.

TRANSCRIPTION RESOLUTIONS (recorded per the E-phase rules):
1. **χat is GUARDED** (`χat : ∀ N' (h' : N₀ ≤ N'), Fin n → Fin (n * N')`) —
   the ratified chi-at guard-repair shape (E-phase adjudication 2026-07-30,
   commit 89b2f7f: "chi-at guard repair RATIFIED"; TV-B1's compiled law: the
   unguarded carrier is uninhabited at n ≥ 1 via N' = 0, and the BRIDGE tower
   instantiation is impossible unguarded).  COORDINATION RECORD: at SYN-C2
   execution time the Defs carriers (`TreeNStable`/`TreeNStableStmt`/
   `KBTotTower`, MovesT/Defs.lean:1624/1637/1771) are still UNGUARDED on disk
   — consumers over those carriers adapt by forgetting the guard
   (`fun N' _ => χat N'`, see `stableInputs_of_readLocality` in TV_B2.lean);
   the adapters collapse when the gates fleet lands the Defs guard sweep.
2. **`child_local`'s cutoff level N is DECOUPLED from the two working levels
   (M, M')**.  The C2 spec displays the cross-level law at x : Box p (n·N)
   with x' at N' ≥ N extending it ("two applications of (ii) at N′ = N′"
   deriving `StableInputs` by truncating to level N).  That truncation needs
   N₀ ≤ N, but `StableInputs.child_cyl`/`TreeNStable` quantify over ALL
   N ≥ Tr.thr n INCLUDING N < N₀ (the below-tower-base corner) — the verbatim
   spec shape would leave that corner underivable.  Decoupling (N = the
   cutoff, needs only Tr.thr n ≤ N; M, M' = the tower levels, each ≥ N and
   ≥ N₀, NO order between them) makes the fixed-level face ONE application
   (M = M' = N'), the cross-level face the M < M' instance, and both
   directions of realization transfer available (no M ≤ M' bias).  The
   spec's display is literally the (M = N ≤ M') instance.  Same open
   content, same owner; strictly the faithful quantifier closure of the
   note's "reads only digits < n·N" claim.
3. Field (iii) of the C2 spec (an NsHalts face "if TV-B2's typing pass finds
   it non-derived") is ABSENT: TV-B2's executed typing pass verified
   `NsHalts` is mem/child-composed (Defs.lean:223–225), so its transfer is
   derived — no field (TV-B2's own recorded finding, inherited).
4. The row is stated at the ABSTRACT MovesT tower in the STANDARD layout
   ("coordinate c at level ⌊c/n⌋ + 1"; the level-<N block = the first n·N
   coordinates — `TreeNStable`'s pinned convention, Defs.lean:1613–1631).
   The (†3) bridge layout (slot i·N + k, coefficient-blocked;
   `MovesU.digitIdx`) is a DIFFERENT labeling of the same digits; the raw
   bridge pair (bridgeTm, bridgeChart) provably VIOLATES `chart_pin`
   (bridgeChart b = b·N' ≥ n at n ≥ 2 ≤ N'), so the bridge instantiates this
   row THROUGH the block-interleave dressing below
   (`reindexModel`/`blockInterleave`; the concrete pins + compiled coherence
   gates live bridge-side in `MovesU/BridgeD5_transferRow.lean`).

DISCHARGE (open; owner HC-2/D4R0K): the note's proof inputs — per site the
joint cell's literal system at its B(iii) level, per branch D4R.4's exact
level-N realization, per leaf TB-CAP's level-N_V cylinders.  N3 UPSIDE PROBE
(adjudicated into the gate class): for the CANONICAL policy the row may be
PROVABLE from the SP8 CanTreeModel / designer-round CONSTRUCTION (its child
predicate is built from level-N digit reads) — one construction proof would
discharge `treeN_stable` + `StableInputs` + `TransferRow` simultaneously.

Consumed by: TV_B2 (`stableInputs_of_readLocality`), TV_B7 (the hoisted
`treeN_stable` rows), MovesU/BridgeD5_transferRow
(`transferRow_of_readLocality` at the dressed bridge tower).  NEVER proved in
this corpus (short of the N3 probe firing). -/

set_option linter.style.longLine false
set_option linter.unusedVariables false

namespace LeanUrat.MovesT

open Polynomial LeanUrat.Moves LeanUrat.MovesC LeanUrat.MovesD

variable {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
variable {n : ℕ} {pol : CanonPolicy p F}

/-- **SYN-C2 `ReadLocality` — THE level-locality kernel row** (owner
HC-2/D4R0K, MOVES 7566–7570; the note's Thm 2.1 / D4R.4 / TB-CAP face).  Over
a pinned tower of models/charts (guarded χat — header resolution 1) and a
tree `Tr`:

* `chart_pin` — the chart lands in the LEVEL-1 block (`(χat N' h' b : ℕ) < n`),
  so `redPoly`/`henPayload`/the factor roster read only level-0 digit slots at
  every tower level (TV-B2's (S-chart), guarded);
* `child_local` — the CROSS-LEVEL child locality: once the tree's threshold is
  ≤ N, the child relation at ANY tower level ≥ N is one function of the first
  n·N box digits, uniformly across levels — for tower levels M, M' ≥ N (no
  order) and boxes agreeing on the first n·N coordinates, child at M ↔ child
  at M', at EVERY site (o, ν) (TV-B2's quantifier option α).  The fixed-level
  cylinder face is the M = M' instance; the cross-level transport face is the
  M < M' instance (header resolution 2).

Derived surfaces (SYN-C2): `StableInputs` (TV_B2.lean,
`stableInputs_of_readLocality` — PROVED), `TransferRow`
(BridgeD5_transferRow.lean, `transferRow_of_readLocality` at the dressed
bridge tower).  Carried as a NAMED warranted hypothesis; NEVER proved in this
corpus. -/
structure ReadLocality {N₀ : ℕ}
    (Tat : ∀ N', N₀ ≤ N' → TreeModel p F n N' (n * N') pol)
    (χat : ∀ N' (h' : N₀ ≤ N'), Fin n → Fin (n * N'))
    (Tr : VTree p F) : Prop where
  chart_pin : ∀ (N' : ℕ) (h' : N₀ ≤ N') (b : Fin n), ((χat N' h' b : ℕ)) < n
  child_local : ∀ (N : ℕ), Tr.thr n ≤ N →
    ∀ (M : ℕ) (hM : N₀ ≤ M) (M' : ℕ) (hM' : N₀ ≤ M')
      (hNM : N ≤ M) (hNM' : N ≤ M')
      (o : Option (History p F)) (ν : Node p F)
      (x : Box p (n * M)) (x' : Box p (n * M')),
      (∀ c : Fin (n * N),
        x (Fin.castLE (Nat.mul_le_mul_left n hNM) c)
          = x' (Fin.castLE (Nat.mul_le_mul_left n hNM') c)) →
      ((Tat M hM).child o ν x ↔ (Tat M' hM').child o ν x')

/-! ## The layout dressing (generic half; header resolution 4)

The bridge tower's (†3) coefficient-blocked labeling (slot i·N + k) reaches
this row's standard level-blocked labeling (slot k·n + i) through a box-slot
relabeling.  `reindexModel` pulls a `TreeModel` back along any slot bijection;
`blockInterleave` is the concrete (†3)→standard pairing.  Both are DEFINED
(not hypothesized); the bridge pins + compiled coherence gates live in
`MovesU/BridgeD5_transferRow.lean`. -/

/-- Pull a `TreeModel` back along a box-slot bijection `e`: the reindexed
model reads relabeled boxes — `(reindexModel T e).child o ν x =
T.child o ν (fun s => x (e s))` (definitional; gate lemmas below).  All five
laws transport pointwise (each is a ∀-law with the same box on both sides). -/
def reindexModel {N m : ℕ} (T : TreeModel p F n N m pol) (e : Fin m ≃ Fin m) :
    TreeModel p F n N m pol where
  mem o x := T.mem o fun s => x (e s)
  child o ν x := T.child o ν fun s => x (e s)
  root_mem x := T.root_mem _
  mem_single ν h1 x := T.mem_single ν h1 _
  mem_snoc H ν hν x := T.mem_snoc H ν hν _
  mem_realizable H x h := T.mem_realizable H _ h

/-- Gate (definitional): the reindexed model's `child` IS the original's at
the relabeled box. -/
theorem reindexModel_child {N m : ℕ} (T : TreeModel p F n N m pol)
    (e : Fin m ≃ Fin m) (o : Option (History p F)) (ν : Node p F)
    (x : Box p m) :
    (reindexModel T e).child o ν x ↔ T.child o ν (fun s => x (e s)) :=
  Iff.rfl

/-- Gate (definitional): the reindexed model's `mem` IS the original's at the
relabeled box. -/
theorem reindexModel_mem {N m : ℕ} (T : TreeModel p F n N m pol)
    (e : Fin m ≃ Fin m) (o : Option (History p F)) (x : Box p m) :
    (reindexModel T e).mem o x ↔ T.mem o (fun s => x (e s)) :=
  Iff.rfl

/-- The (†3)↔standard slot pairing at one working level: bridge slot
i·N + k (digit k of coefficient i, coefficient-blocked; `MovesU.digitIdx`)
↦ standard slot k·n + i (coordinate at level k, level-blocked —
`TreeNStable`'s "coordinate c at level ⌊c/n⌋ + 1" convention).  Forward
formula `(s % N)·n + s/N`, inverse `(c % n)·N + c/n`. -/
def blockInterleave (n N : ℕ) : Fin (n * N) ≃ Fin (n * N) where
  toFun s := ⟨((s : ℕ) % N) * n + (s : ℕ) / N, by
    rcases Nat.eq_zero_or_pos N with h0 | hN
    · exact absurd s.isLt (by simp [h0])
    · have h2 : (s : ℕ) / N < n := (Nat.div_lt_iff_lt_mul hN).mpr s.isLt
      calc ((s : ℕ) % N) * n + (s : ℕ) / N
          < ((s : ℕ) % N) * n + n := by omega
        _ = ((s : ℕ) % N + 1) * n := by ring
        _ ≤ N * n := Nat.mul_le_mul_right n (Nat.mod_lt _ hN)
        _ = n * N := Nat.mul_comm N n⟩
  invFun c := ⟨((c : ℕ) % n) * N + (c : ℕ) / n, by
    rcases Nat.eq_zero_or_pos n with h0 | hn
    · exact absurd c.isLt (by simp [h0])
    · have h2 : (c : ℕ) / n < N :=
        (Nat.div_lt_iff_lt_mul hn).mpr (Nat.mul_comm n N ▸ c.isLt)
      calc ((c : ℕ) % n) * N + (c : ℕ) / n
          < ((c : ℕ) % n) * N + N := by omega
        _ = ((c : ℕ) % n + 1) * N := by ring
        _ ≤ n * N := Nat.mul_le_mul_right N (Nat.mod_lt _ hn)⟩
  left_inv s := by
    rcases Nat.eq_zero_or_pos N with h0 | hN
    · exact absurd s.isLt (by simp [h0])
    · have hn : 0 < n := by
        rcases Nat.eq_zero_or_pos n with h0' | hn'
        · exact absurd s.isLt (by simp [h0'])
        · exact hn'
      have h2 : (s : ℕ) / N < n := (Nat.div_lt_iff_lt_mul hN).mpr s.isLt
      apply Fin.ext
      change ((((s : ℕ) % N) * n + (s : ℕ) / N) % n) * N
          + (((s : ℕ) % N) * n + (s : ℕ) / N) / n = (s : ℕ)
      rw [Nat.add_comm (((s : ℕ) % N) * n) ((s : ℕ) / N),
        Nat.add_mul_mod_self_right, Nat.add_mul_div_right _ _ hn,
        Nat.mod_eq_of_lt h2, Nat.div_eq_of_lt h2, Nat.zero_add]
      exact Nat.div_add_mod' (s : ℕ) N
  right_inv c := by
    rcases Nat.eq_zero_or_pos n with h0 | hn
    · exact absurd c.isLt (by simp [h0])
    · have hN : 0 < N := by
        rcases Nat.eq_zero_or_pos N with h0' | hN'
        · exact absurd c.isLt (by simp [h0'])
        · exact hN'
      have h2 : (c : ℕ) / n < N :=
        (Nat.div_lt_iff_lt_mul hn).mpr (Nat.mul_comm n N ▸ c.isLt)
      apply Fin.ext
      change ((((c : ℕ) % n) * N + (c : ℕ) / n) % N) * n
          + (((c : ℕ) % n) * N + (c : ℕ) / n) / N = (c : ℕ)
      rw [Nat.add_comm (((c : ℕ) % n) * N) ((c : ℕ) / n),
        Nat.add_mul_mod_self_right, Nat.add_mul_div_right _ _ hN,
        Nat.mod_eq_of_lt h2, Nat.div_eq_of_lt h2, Nat.zero_add]
      exact Nat.div_add_mod' (c : ℕ) n

/-- Gate (rfl): the forward formula of the pairing. -/
theorem blockInterleave_val (n N : ℕ) (s : Fin (n * N)) :
    (blockInterleave n N s : ℕ) = ((s : ℕ) % N) * n + (s : ℕ) / N :=
  rfl

/-- Gate: the pairing's SEMANTIC pin — bridge slot i·N + k goes to standard
slot k·n + i (the (†3) digit (i, k) lands at level-k block position i). -/
theorem blockInterleave_apply (n N : ℕ) (i : Fin n) (k : Fin N)
    (h : (i : ℕ) * N + (k : ℕ) < n * N) :
    (blockInterleave n N ⟨(i : ℕ) * N + (k : ℕ), h⟩ : ℕ)
      = (k : ℕ) * n + (i : ℕ) := by
  rw [blockInterleave_val]
  have hk : ((i : ℕ) * N + (k : ℕ)) % N = (k : ℕ) := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt k.isLt]
  have hi : ((i : ℕ) * N + (k : ℕ)) / N = (i : ℕ) := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by omega : 0 < N),
      Nat.div_eq_of_lt k.isLt, Nat.zero_add]
  rw [hk, hi]

end LeanUrat.MovesT
