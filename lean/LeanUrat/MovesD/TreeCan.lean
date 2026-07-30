/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.MovesD.Defs
import LeanUrat.MovesD.PolPin
import LeanUrat.HC2.Defs

/-!
# MovesD/TreeCan — the GENERAL (n, N) canonical tree model (designer-round E-phase skeleton)

Bridge campaign BP1, DESIGN ADDENDUM D-TM (`lean/notes/BRIDGE_BP1_INSTANCE_2026-07-30.md`,
appended 2026-07-30). Resolves blueprint risk R7 / the IB-D1 E-phase finding
(`MovesU/BridgeD1_treeModelWire.lean`): "no (n, N)-generic real (pol, Tm) exists in-corpus —
the only concrete `MovesD.TreeModel`s are n = 2 toys over `polTriv`". MovesD owns
`TreeModel`; this module is the designer round's deliverable, factored in three so that
each open residue is NAMED (never a monolithic sorry):

* **(†12) `canDec`** — the canonical digit decode `Box p (n·N) → ℤ_p[X]`: slot i·N + k
  carries the k-th base-p digit of coefficient i (the COEFFICIENT-MAJOR `digitIdx` layout,
  MovesU DefsLedger.lean:289 / blueprint (†3); the level-0 slot chart `canChart` is
  MovesU's `chartWitness` shape i ↦ i·N, and `canDec_red` ties the mod-p reduction to
  MovesT's `redPoly` at that chart — IB-D2's chart-semantics question is answered BY
  CONSTRUCTION here; the residual level-major `levelIdx` tension is IB-D28, Q10).
* **(†13) `memCan`** — T_can(f)'s membership semantics at general (n, N): a nonempty chain
  H sits in the canonical tree at box point x iff it is a `ReadsOf`-run of the decoded
  lift (the f-explicit Wall-A run predicate, HC2/Defs — carries `HistoryCoherent` as a
  conjunct), transition-admissible (`Realizable`), and canonically presented
  (`pol.IsCanonPres` — L1's lifts + the canonical residue roots). `InBox` is NOT baked in:
  IB-D25a probes its derivation from the run's root development (Q9 adjudicates the
  fallback). The empty chain (`none`) is the full box — L2's root law.
* **(†14) `canTreeModel`** — the `TreeModel` instance over ANY policy and decode.
  `root_mem` is definitional; `mem_single` is History proof-irrelevance; `mem_snoc` is the
  ONE load-bearing law `memCan_snoc_mono` (IB-D23: every memCan clause is a ∀-restriction
  or witness-reuse under truncation); `mem_realizable` is projection. The W4-1 seam
  REVERSES at this model: `child` is DEFINED as run-extension, so the all-and-only
  face is definitional (`canTreeModel_child_some_iff`, the `WallAReconciled` genre) while
  the covering duties (`W41ChildCover`/`ChildCover`) become genuine ReadsOf-totality
  claims — owner HC-2/D4R.0-K, exactly the ledger's assignment.
* **(†15) `canPolicy` + `canPolicy_pin`** — the POL-PIN policy (the note's ONE (S6b)
  OFFSET-P-LIFT rule, note 4646–4651): HONEST DATA SORRIES, owner HC-1 (`PolPin.lean`:
  "The HC-1 wave instantiates `Realizes` with the (S6b′) formula and discharges all five
  laws"). The model is policy-PARAMETRIC, so only canonicity-demanding consumers block
  on these two; the wire `bridgeTm := canTreeModelN p n N (canPolicy p)` is IB-D27
  (a MovesU edit, outside this new-modules-only round).

PROVER STATUS (BP1-P8, 2026-07-30): IB-D22/D23/D24/D25/D30 are PROVED — the E-phase
sorries are discharged. IB-D23's design-time check held exactly as sketched (every
`memCan` clause restricted or reused verbatim; no prefix-stability failure — R10 dead);
the IB-D25a PROBE **derived** `InBox` from the run's root development (degree-1 root key
per `HistoryCoherent`, top pattern digit `hpatTop` occupies development slot s0+wSide,
occupied slots of a degree-1 development are ≤ natDegree = n) — Q9's roster stands, NO
`InBox` conjunct needed. SORRY CENSUS (2): `canPolicy`/`canPolicy_pin` (IB-D26, owner
HC-1 — NOT dischargeable this campaign without the (S6b′) lower-stage realizer export;
R12 guard: no unit unfolds them, canonicity-demanding consumers bind `OffsetPPin pol`).
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesD

open Polynomial LeanUrat.Moves LeanUrat.MovesC

/-! ## (†12) IB-D22 — the canonical decode (coefficient-major digitIdx layout) -/

/-- The level-0 slot chart of the coefficient-major layout: coefficient `i`'s 0-th
base-p digit sits at slot `i·N` (MovesU `chartWitness`'s shape, blueprint (†3)). -/
def canChart (n N : ℕ) (hN : 0 < N) : Fin n → Fin (n * N) :=
  fun i => ⟨i.1 * N, by
    have h1 : i.1 + 1 ≤ n := i.isLt
    calc i.1 * N < i.1 * N + N := Nat.lt_add_of_pos_right hN
      _ = (i.1 + 1) * N := by ring
      _ ≤ n * N := Nat.mul_le_mul h1 (le_refl N)⟩

/-- Coefficient `i`'s canonical ℤ_p lift off the digit box: `Σ_{k<N} digit(i,k)·p^k`,
digits read at slots `i·N + k` (junk 0 beyond the box — dead for `i < n`). -/
noncomputable def canCoeff (p : ℕ) [Fact p.Prime] {m : ℕ} (N : ℕ)
    (x : Box p m) (i : ℕ) : ℤ_[p] :=
  ∑ k ∈ Finset.range N,
    (if h : i * N + k < m then (((x ⟨i * N + k, h⟩).val : ℕ) : ℤ_[p]) else 0) * (p : ℤ_[p]) ^ k

/-- **The canonical decode** (†12): the monic degree-n ℤ_p lift of a level-N digit box
member — `X^n + Σ_{i<n} canCoeff(i)·X^i`. The intended instance of `ReadsOf`'s `f` and
of the Wall-A `dec` binder (`MovesT.WallAReconciled`); the same layout as MovesU's
`digitIdx`/`boxeq_digits` ((†3b)) and the blueprint's `lift_exists` display (†11d). -/
noncomputable def canDec (p : ℕ) [Fact p.Prime] (n N : ℕ)
    (x : Box p (n * N)) : Polynomial ℤ_[p] :=
  Polynomial.X ^ n + ∑ i ∈ Finset.range n, Polynomial.C (canCoeff p N x i) * Polynomial.X ^ i

/-- The tail sum of `canDec` has degree `< n` (each term `C c · X^i` has degree `≤ i < n`;
at n = 0 the sum is 0 of degree ⊥ < 0). Shared engine of the two IB-D22 degree laws. -/
private theorem canDec_sum_degree_lt (p : ℕ) [Fact p.Prime] (n N : ℕ) (x : Box p (n * N)) :
    (∑ i ∈ Finset.range n, Polynomial.C (canCoeff p N x i) * Polynomial.X ^ i).degree
      < (n : WithBot ℕ) := by
  refine lt_of_le_of_lt (Polynomial.degree_sum_le _ _) ?_
  refine (Finset.sup_lt_iff (WithBot.bot_lt_coe n)).mpr fun i hi => ?_
  refine lt_of_le_of_lt (Polynomial.degree_C_mul_X_pow_le _ _) ?_
  exact WithBot.coe_lt_coe.mpr (Finset.mem_range.mp hi)

/-- IB-D22 law 1: the decode is monic (leading slot is the bare X^n; the sum has
degree < n — unconditional, n = 0 gives the monic constant 1). -/
theorem canDec_monic (p : ℕ) [Fact p.Prime] (n N : ℕ) (x : Box p (n * N)) :
    (canDec p n N x).Monic := by
  exact Polynomial.monic_X_pow_add (canDec_sum_degree_lt p n N x)

/-- IB-D22 law 2: the decode has the box's degree. -/
theorem canDec_natDegree (p : ℕ) [Fact p.Prime] (n N : ℕ) (x : Box p (n * N)) :
    (canDec p n N x).natDegree = n := by
  have hd : (canDec p n N x).degree = (n : WithBot ℕ) := by
    unfold canDec
    rw [Polynomial.degree_add_eq_left_of_degree_lt
      (by rw [Polynomial.degree_X_pow]; exact canDec_sum_degree_lt p n N x),
      Polynomial.degree_X_pow]
  exact Polynomial.natDegree_eq_of_degree_eq_some hd

/-- IB-D22 law 3 — **the chart tie** (answers IB-D2 by construction): at 0 < N the
mod-p reduction of the decode is the level-0 read at the slot chart — literally
`MovesT.redPoly (canChart n N hN) x` unfolded (stated import-free here; the one-line
`redPoly` re-key lands with the IB-D27 wire). Sketch: `Polynomial.map` through C/X;
`PadicInt.toZMod` kills every `p^k`-term with k ≥ 1 and returns digit 0's value on the
k = 0 term (`ZMod.natCast_val` roundtrip). -/
theorem canDec_red (p : ℕ) [Fact p.Prime] (n N : ℕ) (hN : 0 < N) (x : Box p (n * N)) :
    (canDec p n N x).map (PadicInt.toZMod) =
      Polynomial.X ^ n
        + ∑ b : Fin n, Polynomial.C (x (canChart n N hN b)) * Polynomial.X ^ (b : ℕ) := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  unfold canDec
  rw [Polynomial.map_add, Polynomial.map_pow, Polynomial.map_X]
  congr 1
  calc (∑ i ∈ Finset.range n,
          Polynomial.C (canCoeff p N x i) * Polynomial.X ^ i).map PadicInt.toZMod
      = ∑ i ∈ Finset.range n,
          (Polynomial.C (canCoeff p N x i) * Polynomial.X ^ i).map PadicInt.toZMod := by
        simp [Polynomial.map_sum]
    _ = ∑ b : Fin n,
          (Polynomial.C (canCoeff p N x (b : ℕ)) * Polynomial.X ^ (b : ℕ)).map PadicInt.toZMod :=
        Finset.sum_range _
    _ = ∑ b : Fin n, Polynomial.C (x (canChart n N hN b)) * Polynomial.X ^ (b : ℕ) := by
        refine Finset.sum_congr rfl fun b _ => ?_
        rw [Polynomial.map_mul, Polynomial.map_C, Polynomial.map_pow, Polynomial.map_X]
        congr 2
        -- the digit read: toZMod kills every p^k-term with k ≥ 1 and returns digit 0
        unfold canCoeff
        rw [map_sum, Finset.sum_eq_single 0
          (fun k _ hk => by
            rw [map_mul, map_pow, map_natCast, ZMod.natCast_self, zero_pow hk, mul_zero])
          (fun h => absurd (Finset.mem_range.mpr hN) h)]
        have hb : (b : ℕ) * N + 0 < n * N := by
          have h1 : (b : ℕ) + 1 ≤ n := b.isLt
          have h2 : ((b : ℕ) + 1) * N ≤ n * N := Nat.mul_le_mul_right N h1
          have h3 : (b : ℕ) * N + N ≤ n * N := by rw [← Nat.succ_mul]; exact h2
          omega
        rw [dif_pos hb, pow_zero, mul_one, map_natCast]
        have hidx : (⟨(b : ℕ) * N + 0, hb⟩ : Fin (n * N)) = canChart n N hN b := by
          apply Fin.ext; simp [canChart]
        rw [hidx, ZMod.natCast_val, ZMod.cast_id]

/-! ## (†13) IB-D23 — T_can(f)'s membership semantics + the load-bearing prefix law -/

section
variable {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F] {m : ℕ}

/-- **T_can membership, general (n, N)** (†13): the chain H is realized at box point x
iff H is a `ReadsOf`-run of the decoded lift (Wall A's f-explicit run predicate —
`HistoryCoherent` is its third conjunct), transition-admissible, and canonically
presented under `pol`. Clause roster flagged for ratification (Q9): `InBox` is a
DERIVATION PROBE (IB-D25a), not a conjunct; the note's T_can(f) chains should be in-box
because the run reads a degree-n lift. -/
def memCan (n : ℕ) (pol : CanonPolicy p F) (dec : Box p m → Polynomial ℤ_[p])
    (H : History p F) (x : Box p m) : Prop :=
  LeanUrat.MovesJ.ReadsOf p F n (dec x) H ∧ Realizable H ∧ pol.IsCanonPres H

/-- The one-node history at a root-species node (MovesD-local mirror of
`MovesT.oneNode` — MovesD cannot import MovesT). -/
def rootHist (ν : Node p F) (h : ν.species = ReadSpecies.root) : History p F :=
  ⟨[ν], by simp, by
    intro j hj
    have hj1 : j < 1 := by simpa using hj
    have hj0 : j = 0 := by omega
    subst hj0
    simpa using h⟩

/-! ### IB-D23 snoc-restriction engine (private): every `memCan` clause is a
∀-restriction or a verbatim witness-reuse under truncation. The three list-level
facts (`snoc` length / getElem / strFrame) are stated once and consumed by the four
clause-restriction lemmas below. -/

private theorem snoc_length (H : History p F) (ν : Node p F)
    (hν : ν.species ≠ ReadSpecies.root) :
    (H.snoc ν hν).nodes.length = H.nodes.length + 1 := by
  change (H.nodes ++ [ν]).length = H.nodes.length + 1
  simp

/-- Snoc-nodes restriction: below the truncation point the snoc reads the original nodes. -/
private theorem snoc_getElem (H : History p F) (ν : Node p F)
    (hν : ν.species ≠ ReadSpecies.root) {i : ℕ} (hi : i < H.nodes.length)
    {hi' : i < (H.snoc ν hν).nodes.length} :
    (H.snoc ν hν).nodes[i]'hi' = H.nodes[i]'hi := by
  change (H.nodes ++ [ν])[i]'hi' = H.nodes[i]'hi
  exact List.getElem_append_left hi

/-- `strFrame` take-stability: the accumulated stretch below the truncation point is
computed from the original nodes (`take i` never sees the appended node). -/
private theorem snoc_strFrame (H : History p F) (ν : Node p F)
    (hν : ν.species ≠ ReadSpecies.root) {i : ℕ} (hi : i ≤ H.nodes.length) :
    (H.snoc ν hν).strFrame i = H.strFrame i := by
  change (((H.nodes ++ [ν]).take i).map Node.e).prod = ((H.nodes.take i).map Node.e).prod
  rw [List.take_append, Nat.sub_eq_zero_of_le hi, List.take_zero, List.append_nil]

/-- `HistoryCoherent` restricts along the snoc-peel: clauses 1–3 are per-node
(`strFrame` take-stable), clause 4 is per-adjacent-pair — all indices stay below the
truncation point. -/
private theorem historyCoherent_of_snoc {H : History p F} {ν : Node p F}
    {hν : ν.species ≠ ReadSpecies.root}
    (hc : HistoryCoherent (H.snoc ν hν)) : HistoryCoherent H := by
  obtain ⟨h1, h2, h3, h4⟩ := hc
  refine ⟨fun hj => ?_, fun i hi => ?_, fun i hi => ?_, fun i hi => ?_⟩
  · have hj' : 0 < (H.snoc ν hν).nodes.length := by rw [snoc_length]; omega
    have := h1 hj'
    rwa [snoc_getElem H ν hν hj] at this
  · have hi' : i < (H.snoc ν hν).nodes.length := by rw [snoc_length]; omega
    have := h2 i hi'
    rwa [snoc_getElem H ν hν hi, snoc_strFrame H ν hν hi.le] at this
  · have hi' : i < (H.snoc ν hν).nodes.length := by rw [snoc_length]; omega
    have := h3 i hi'
    rwa [snoc_getElem H ν hν hi, snoc_strFrame H ν hν hi.le] at this
  · have hi' : i + 1 < (H.snoc ν hν).nodes.length := by rw [snoc_length]; omega
    have := h4 i hi'
    rwa [snoc_getElem H ν hν (show i < H.nodes.length by omega),
      snoc_getElem H ν hν hi] at this

/-- `Realizable` restricts (per-adjacent-pair ∀). -/
private theorem realizable_of_snoc {H : History p F} {ν : Node p F}
    {hν : ν.species ≠ ReadSpecies.root}
    (hr : Realizable (H.snoc ν hν)) : Realizable H := by
  intro i hi
  have hi' : i + 1 < (H.snoc ν hν).nodes.length := by rw [snoc_length]; omega
  have := hr i hi'
  rwa [snoc_getElem H ν hν (show i < H.nodes.length by omega),
    snoc_getElem H ν hν hi] at this

/-- `IsCanonPres` restricts (both conjuncts are per-node ∀s). -/
private theorem isCanonPres_of_snoc {pol : CanonPolicy p F} {H : History p F}
    {ν : Node p F} {hν : ν.species ≠ ReadSpecies.root}
    (hp : pol.IsCanonPres (H.snoc ν hν)) : pol.IsCanonPres H := by
  obtain ⟨hlift, hroot⟩ := hp
  constructor
  · intro r hr
    have hr' : r < (H.snoc ν hν).nodes.length := by rw [snoc_length]; omega
    have := hlift r hr'
    rwa [snoc_getElem H ν hν hr] at this
  · intro r hr
    have hr' : r < (H.snoc ν hν).nodes.length := by rw [snoc_length]; omega
    have := hroot r hr'
    rwa [snoc_getElem H ν hν hr] at this

/-- `ReadsOf` restricts: Monic/natDegree are H-free; `HistoryCoherent` restricts; the
per-read development witnesses (B, Nd, Φnext) are REUSED VERBATIM — truncation only
vacates the `∀ hi1 : i+1 < length` Φnext guard at the new last read. -/
private theorem readsOf_of_snoc {n : ℕ} {f : Polynomial ℤ_[p]} {H : History p F}
    {ν : Node p F} {hν : ν.species ≠ ReadSpecies.root}
    (hro : LeanUrat.MovesJ.ReadsOf p F n f (H.snoc ν hν)) :
    LeanUrat.MovesJ.ReadsOf p F n f H := by
  obtain ⟨hmon, hdeg, hcoh, hrun⟩ := hro
  refine ⟨hmon, hdeg, historyCoherent_of_snoc hcoh, ?_⟩
  intro i hi
  have hi' : i < (H.snoc ν hν).nodes.length := by rw [snoc_length]; omega
  obtain ⟨B, Nd, Φnext, hdev, hkey, hside⟩ := hrun i hi'
  refine ⟨B, Nd, Φnext, ?_, ?_, ?_⟩
  · rwa [snoc_getElem H ν hν hi] at hdev
  · intro hi1
    have hi1' : i + 1 < (H.snoc ν hν).nodes.length := by rw [snoc_length]; omega
    have := hkey hi1'
    rwa [snoc_getElem H ν hν hi1] at this
  · rwa [snoc_getElem H ν hν hi] at hside

/-- **IB-D23 — the load-bearing prefix law** feeding `mem_snoc`: membership descends
along the snoc-peel. Every `memCan` clause is a ∀-restriction or a witness-reuse under
truncation: `Realizable`/`IsCanonPres` quantify per node/adjacent pair
(`List.getElem_append_left` transports); `ReadsOf`'s Monic/natDegree conjuncts are
H-free; `HistoryCoherent` restricts (with `History.strFrame` take-stability); the
per-read development witnesses (B, Nd, Φnext) are REUSED VERBATIM — the truncation only
shrinks the `Φnext`-constraint set (its `∀ hi1 : i+1 < length` guard goes vacuous at the
new last read). COUNTERMODEL GATE: none needed (restriction + reuse); if a clause turns
out non-prefix-stable the unit returns BLOCKED and the adjudicated fallback is an
explicit prefix-closure scoping of `memCan` (a fence event — Q9). -/
theorem memCan_snoc_mono {n : ℕ} {pol : CanonPolicy p F}
    {dec : Box p m → Polynomial ℤ_[p]} (H : History p F) (ν : Node p F)
    (hν : ν.species ≠ ReadSpecies.root) (x : Box p m) :
    memCan n pol dec (H.snoc ν hν) x → memCan n pol dec H x := by
  rintro ⟨hro, hreal, hpres⟩
  exact ⟨readsOf_of_snoc hro, realizable_of_snoc hreal, isCanonPres_of_snoc hpres⟩

end

/-! ## (†14) IB-D24 — the general TreeModel instance -/

section
variable {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]

/-- **THE GENERAL (n, N) CANONICAL TREE MODEL** (†14) — the designer-round deliverable
(R7's re-plan): `mem` is `memCan` on nonempty chains and the full box at the root (L2's
law); `child` is DEFINED as run-extension — a root child is a realized one-node run at a
root-species node, a state child is a realized snoc at a non-root node. Structural laws:
`root_mem` definitional; `mem_single` History proof-irrelevance (IB-D24a); `mem_snoc` =
projection + `memCan_snoc_mono` (IB-D24b); `mem_realizable` = projection off `memCan`'s
conjuncts, with `HistoryCoherent` supplied by `ReadsOf`'s third conjunct (IB-D24c).
Parametric in (pol, dec) BY DESIGN: the MovesT corpus quantifies over every policy; the
canonical instance pins `dec := canDec` (`canTreeModelN`) and `pol := canPolicy` (IB-D26,
HC-1-owned) at the IB-D27 wire. -/
noncomputable def canTreeModel (p : ℕ) [Fact p.Prime] (F : Type*) [Field F] [Finite F]
    (n N m : ℕ) (pol : CanonPolicy p F) (dec : Box p m → Polynomial ℤ_[p]) :
    TreeModel p F n N m pol where
  mem := fun o x =>
    match o with
    | none => True
    | some H => memCan n pol dec H x
  child := fun o ν x =>
    match o with
    | none => ∃ h : ν.species = ReadSpecies.root, memCan n pol dec (rootHist ν h) x
    | some H => ∃ hν : ν.species ≠ ReadSpecies.root, memCan n pol dec (H.snoc ν hν) x
  root_mem := fun _ => trivial
  mem_single := by
    -- IB-D24a: `⟨[ν], h1.1, h1.2⟩ = rootHist ν (h1.2-at-0)` by proof irrelevance.
    intro ν h1 x
    have hroot : ν.species = ReadSpecies.root := by
      simpa using (h1.2 0 (by simp)).mpr rfl
    constructor
    · intro hm
      exact ⟨hroot, hm⟩
    · rintro ⟨h, hm⟩
      exact hm
  mem_snoc := by
    -- IB-D24b: backward = proof-irrelevant projection; forward = `memCan_snoc_mono`.
    intro H ν hν x
    constructor
    · intro hm
      exact ⟨memCan_snoc_mono H ν hν x hm, hν, hm⟩
    · rintro ⟨-, hν', hm⟩
      exact hm
  mem_realizable := by
    -- IB-D24c: `⟨hm.1.2.2.1, hm.2.1, hm.2.2⟩` — HistoryCoherent off ReadsOf.
    rintro H x ⟨hro, hreal, hpres⟩
    exact ⟨hro.2.2.1, hreal, hpres⟩

/-- The canonical model at the working level m = n·N with the canonical decode — the
shape `bridgeTm` wires to (IB-D27: `bridgeTm p n N := canTreeModelN p n N (canPolicy p)`). -/
noncomputable def canTreeModelN (p : ℕ) [Fact p.Prime] (n N : ℕ)
    (pol : CanonPolicy p (ZMod p)) : TreeModel p (ZMod p) n N (n * N) pol :=
  canTreeModel p (ZMod p) n N (n * N) pol (canDec p n N)

variable {n N m : ℕ} {pol : CanonPolicy p F} {dec : Box p m → Polynomial ℤ_[p]}

/-- Display (defeq): nonempty-chain membership IS the run predicate. -/
theorem canTreeModel_mem_some_iff (H : History p F) (x : Box p m) :
    (canTreeModel p F n N m pol dec).mem (some H) x ↔
      LeanUrat.MovesJ.ReadsOf p F n (dec x) H ∧ Realizable H ∧ pol.IsCanonPres H :=
  Iff.rfl

/-- IB-D30 — **the Wall-A face, definitional at the canonical model**: a state child is
exactly a realized run-extension of the decoded lift (`MovesT.WallAReconciled`'s genre,
with `Realizable ∧ IsCanonPres` riding along; proof-irrelevance collapses the ∃). -/
theorem canTreeModel_child_some_iff (H : History p F) (ν : Node p F)
    (hν : ν.species ≠ ReadSpecies.root) (x : Box p m) :
    (canTreeModel p F n N m pol dec).child (some H) ν x ↔
      memCan n pol dec (H.snoc ν hν) x := by
  constructor
  · rintro ⟨hν', hm⟩
    exact hm
  · intro hm
    exact ⟨hν, hm⟩

/-- IB-D25b — root-child display: a root child is a realized one-node run at a
root-species node. -/
theorem canTreeModel_child_root_iff (ν : Node p F)
    (h : ν.species = ReadSpecies.root) (x : Box p m) :
    (canTreeModel p F n N m pol dec).child none ν x ↔
      memCan n pol dec (rootHist ν h) x := by
  constructor
  · rintro ⟨h', hm⟩
    exact hm
  · intro hm
    exact ⟨h, hm⟩

/-- IB-D25b — non-root nodes are never root children (matches `MovesT.ChildRoot`'s
`none` leg). -/
theorem canTreeModel_child_none_not_root (ν : Node p F)
    (hν : ν.species ≠ ReadSpecies.root) (x : Box p m) :
    ¬ (canTreeModel p F n N m pol dec).child none ν x := by
  rintro ⟨h, -⟩
  exact hν h

/-- Private degree engine for the IB-D25a probe: in a degree-1 key every nonzero
development slot sits at index ≤ the developed polynomial's natDegree (all slot
coefficients are constants, so the nonzero terms have pairwise-distinct degrees =
their indices; the maximal one carries the degree). -/
private theorem slot_le_natDegree_of_isDevelopment {Φ f : Polynomial ℤ_[p]}
    {B : ℕ → Polynomial ℤ_[p]} {Nd : ℕ} (hΦ : Φ.natDegree = 1)
    (hdev : IsDevelopment Φ f B Nd) {j : ℕ} (hB : B j ≠ 0) : j ≤ f.natDegree := by
  classical
  obtain ⟨hdegB, hzero, hsum⟩ := hdev
  have hΦne : Φ ≠ 0 := fun h => by simp [h] at hΦ
  have hΦdeg : Φ.degree = ((1 : ℕ) : WithBot ℕ) := by
    rw [Polynomial.degree_eq_natDegree hΦne, hΦ]
  set S : Finset ℕ := (Finset.range Nd).filter (fun i => B i ≠ 0) with hSdef
  have hjS : j ∈ S := by
    refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr ?_, hB⟩
    by_contra hge
    exact hB (hzero j (le_of_not_gt hge))
  have hSne : S.Nonempty := ⟨j, hjS⟩
  set J := S.max' hSne with hJdef
  have hJS : J ∈ S := S.max'_mem hSne
  -- each carried term has degree exactly its slot index
  have hterm : ∀ i ∈ S, (B i * Φ ^ i).degree = (i : WithBot ℕ) := by
    intro i hi
    have hBi : B i ≠ 0 := (Finset.mem_filter.mp hi).2
    have hBn0 : (B i).natDegree = 0 := by
      have := (Polynomial.natDegree_lt_iff_degree_lt hBi).mpr (hΦdeg ▸ hdegB i)
      omega
    have htne : B i * Φ ^ i ≠ 0 := mul_ne_zero hBi (pow_ne_zero _ hΦne)
    have hnat : (B i * Φ ^ i).natDegree = i := by
      rw [Polynomial.natDegree_mul hBi (pow_ne_zero _ hΦne), hBn0,
        Polynomial.natDegree_pow, hΦ, zero_add, mul_one]
    rw [Polynomial.degree_eq_natDegree htne, hnat]
  -- f is the S-restricted sum, whose degree is the maximal slot index
  have hfS : f = ∑ i ∈ S, B i * Φ ^ i := by
    rw [hsum, hSdef]
    exact (Finset.sum_filter_of_ne fun i _ hne => left_ne_zero_of_mul hne).symm
  have hrest : (∑ i ∈ S.erase J, B i * Φ ^ i).degree < (B J * Φ ^ J).degree := by
    rw [hterm J hJS]
    refine lt_of_le_of_lt (Polynomial.degree_sum_le _ _) ?_
    refine (Finset.sup_lt_iff (WithBot.bot_lt_coe J)).mpr fun i hi => ?_
    rw [hterm i (Finset.mem_of_mem_erase hi)]
    exact WithBot.coe_lt_coe.mpr (lt_of_le_of_ne (S.le_max' i (Finset.mem_of_mem_erase hi))
      (Finset.ne_of_mem_erase hi))
  have hdegf : f.degree = (J : WithBot ℕ) := by
    rw [hfS, ← Finset.add_sum_erase S _ hJS,
      Polynomial.degree_add_eq_left_of_degree_lt hrest, hterm J hJS]
  have hnatf : f.natDegree = J := Polynomial.natDegree_eq_of_degree_eq_some hdegf
  rw [hnatf]
  exact S.le_max' j hjS

/-- IB-D25a — **PROBE** (countermodel-first; Q9's evidence): realized chains are
in-box — `MovesT.InBoxOfMem`'s statement at the canonical model, attempted from the
run's root development on the degree-n decoded lift (`SideReads` root clause). A
BLOCKED outcome re-adjudicates `memCan`'s roster (add the `InBox` conjunct) rather
than weakening this statement. -/
theorem canTreeModel_inBox (H : History p F) (x : Box p m) :
    (canTreeModel p F n N m pol dec).mem (some H) x → InBox n H := by
  rintro ⟨⟨hmon, hdeg, hcoh, hrun⟩, -, -⟩
  intro hj
  obtain ⟨B, Nd, Φnext, hdev, hkey, hside⟩ := hrun 0 hj
  -- the root key is degree-1 (HistoryCoherent's root-frame clause)
  have hΦ1 : ((H.nodes[0]'hj).σ.Φ).natDegree = 1 := hcoh.1 hj
  -- the top pattern digit is nonzero, so the development slot s0 + wSide is occupied
  have htop := hside.2.1 ((H.nodes[0]'hj).wSide / (H.nodes[0]'hj).e) (le_refl _)
    (H.nodes[0]'hj).hpatTop
  have hslot : (H.nodes[0]'hj).s0
        + (H.nodes[0]'hj).e * ((H.nodes[0]'hj).wSide / (H.nodes[0]'hj).e)
      = (H.nodes[0]'hj).s0 + (H.nodes[0]'hj).wSide := by
    rw [Nat.mul_div_cancel' (H.nodes[0]'hj).hEdvd]
  have hBne : B ((H.nodes[0]'hj).s0 + (H.nodes[0]'hj).wSide) ≠ 0 := by
    rw [← hslot]; exact htop.1
  -- an occupied slot of a degree-1 development is bounded by the lift's degree n
  have := slot_le_natDegree_of_isDevelopment hΦ1 hdev hBne
  rwa [hdeg] at this

end

/-! ## (†15) IB-D26 — the POL-PIN policy (HONEST DATA SORRIES, owner HC-1) -/

/-- **THE CANONICAL POLICY** (†15, IB-D26): the note's ONE lift rule — the (S6b)
OFFSET-P-LIFT realizer at every recentering (note 4646–4651; POL-PIN, W4-5). OWNER
HC-1/§B2-DEF: the (S6b′) formula needs the lower-stage realizer vocabulary that MovesC/
MovesD do not export (`PolPin.lean`'s named residue). NOT dischargeable this campaign;
the sorry is the designer round's honest boundary, and `canPolicy_pin` below is its
LAW-CARRYING obligation — a filled `canPolicy` without the pin is NOT acceptance. -/
noncomputable def canPolicy (p : ℕ) [Fact p.Prime] : CanonPolicy p (ZMod p) :=
  sorry

/-- The policy is PINNED (†15): `canPolicy` carries the W4-5 `OffsetPPin` — L1 totality,
genuineness, the forced-class support law, determinism, and the D.10 digit-value law.
Owner HC-1 (discharged together with `canPolicy`; the pin excludes every under-typed
instantiation — see `OffsetPPin.not_realizes_bare_ne_zero` and the bypass kills). -/
noncomputable def canPolicy_pin (p : ℕ) [Fact p.Prime] : OffsetPPin (canPolicy p) :=
  sorry

end LeanUrat.MovesD
