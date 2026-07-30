/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.MovesU.SlotsG9_m4bConst
import LeanUrat.MovesU.SlotsG10_jcInvHist
import LeanUrat.MovesT.S2_sibFalse

/-!
# IB-G11c — non-vacuity audit, SEAM FAMILY (bridge campaign BP1, cluster c12;
E-phase skeleton — PARTIAL, see the blocked record below)

Blueprint: `lean/notes/BRIDGE_BP1_INSTANCE_2026-07-30.md` §3.8 (non-vacuity
audit paragraph) + §4 group G (IB-G11c; split of G11 post-Codex finding 11).
Deps per blueprint: IB-G7 (Slot_m1m5Echo), IB-G8 (Slot_x1aDict), IB-G9
(Slot_m4bConst), IB-G10 (Slot_jcInvHist).

THE WAVE-2 DOCTRINE (the audit's charge): every formulated slot Prop must be
FALSE for a degenerate instance the note would reject — a compiled falsifier
per slot, killing the True-instantiation escape recorded at U10's wave-4
boundary paragraph.  The E-phase skeleton states each falsifier as an
∃-degenerate-instance negation with a `sorry` body; the prover owes the
explicit degenerate construction.

PARTIAL AT WRITE TIME (2026-07-30, cluster c12): the seam family is
(m1m5Echo, x1aDict, m4bConst, jcInvHist), but `Slot_m1m5Echo` (IB-G7) and
`Slot_x1aDict` (IB-G8) are owned by a sibling cluster and are NOT on disk —
their falsifiers cannot elaborate and are BLOCKED, recorded in the cluster
report.  When G7/G8 land, the two missing falsifiers go in a NEW file
(new-files-only discipline; this file is not edited).

PROVER SKETCHES (from the slot formulations' failure modes):
* `slot_m4bConst_falsifiable`: a degenerate `CtsMeasured` whose `entInst`
  census READS A HEIGHT COORDINATE of the written shape (e.g. census :=
  hentCode of the written ε) — two `Order0Perimeter`-certified points of one
  listed component with different height slots then give different
  `instCensus` values at a landing cell, refuting the constancy conjunct.
  Care: the degenerate instance must still satisfy `CtsMeasured`'s own laws
  (`ent_card` etc.) — the toy witness `V1_witnessC.Ctoy`-style n = 1 carrier
  is the recommended chassis.
* `slot_jcInvHist_falsifiable`: a degenerate `CellData` whose joint read
  `cellOf (.st H)` depends on the LENGTH of the history H (legal: `cellOf` is
  free per-entrance data, `cell_local` only constrains the box argument) —
  two realized histories with `NodeRetainedKeyEq` last nodes but different
  chain lengths then price the same joint cell differently, refuting the
  cross-multiplied law equality.  The G1-toy diagonal read
  (`branchCellOf es ν := cellOf es`) is the recommended chassis.
-/

set_option linter.style.longLine false
set_option linter.style.header false

namespace LeanUrat.MovesU

/-!
BLOCKED RECORD — falsifier 1/4 (m4bConst) (2026-07-30, cluster BP1-P10-slots;
honest sorry per the bounded-repair rule).  The sketched height-reading census
toy is NOT reachable without new upstream machinery: any census or realizability
asymmetry between two certified height points requires a NONEMPTY
`entInst`/`entEvt` at a pool (both conjuncts route through `ent_card`, which
forces `entEvt ≠ ∅ ↔ census ≠ 0` at pools), and `CtsMeasured.ent_cut` then
demands, at the nonempty census, a compiled `CutRealization` — an
`EntranceCut` + encode bijection over a genuine `MovesD.Presented` (per-class
`JetSetup`s + `PresentNorm`) at the written shape.  The corpus has NO
non-vacuous `CutRealization`/`Presented` instance (grep 2026-07-30); the only
landed `CtsMeasured` toy (`V1_witnessC.mcV`) uses the ∅-census device precisely
to keep `ent_cut` vacuous, and the ∅-census device provably CANNOT falsify
(zero censuses are constant and unrealizable on both sides).  Discharging this
falsifier therefore needs an HC-2-scale helper (a minimal `Presented` with one
realized prefix class) — surfaced for adjudication, not improvised here. -/
theorem slot_m4bConst_falsifiable :
    ∃ (n : ℕ) (Cv : MovesV.CtsFamily n) (Sv : MovesV.StepSys n)
      (V : MovesV.CtsMeasured n Cv Sv), ¬ Slot_m4bConst n V :=
  sorry

/-! ### Falsifier 2/4 (jcInvHist) — PROVED.  The chassis is the 0-sorry
`MovesT.S2_sibFalse` toy: `sibModel` realizes the two one-node histories
`t1 = ⟨[toyHead]⟩` and `t2 = ⟨[sibNode2]⟩` on the `x 0 = 0` slice, where
`sibNode2 = { toyHead with center := 0 }` differs from `toyHead` ONLY in the
`center` field — a datum the retained key ERASES, so
`NodeRetainedKeyEq t1.lastNode t2.lastNode` holds by `rfl`s while the histories
are distinct.  The degenerate `CellData` below reads the ENTRANCE HISTORY in
its joint read (`cellOf (.st H) := if H = t1 then 2 else 3` — legal: `cellOf`
is free per-entrance data, `cell_local` constrains only the box argument), so
the two key-equal entrances price the joint cell `2` differently:
`|Ψ⁻¹(2) ∩ Σ| · |Σ'| = 2·2 = 4 ≠ 0 = |Ψ'⁻¹(2) ∩ Σ'| · |Σ|`. -/

section JcFalsifier

open scoped Classical

/-- the history-reading joint cell assignment (`Fin 4` alphabet: 0 = the
child-carrying root/reduction cell, 1 = the off-slice reduction cell,
2 = the `t1` entrance, 3 = every other state entrance). -/
noncomputable def jcFalsCellOf :
    MovesT.EntSt 2 (ZMod 2) 2 → MovesD.Box 2 2 → Fin 4
  | .amb, _ => 0
  | .red _ _, x => if x 0 = 0 then 0 else 1
  | .st H, _ => if H = MovesT.t1 then 2 else 3

/-- branch sets: only the child-carrying cell `0` carries the two root children. -/
noncomputable def jcFalsBranch : Fin 4 → Finset (MovesC.Node 2 (ZMod 2)) :=
  fun c => if c = 0 then {MovesT.toyHead, MovesT.sibNode2} else ∅

/-- the degenerate history-reading `CellData` over `MovesT.sibModel` (the
falsifier's device; every law checked against the sib toy's child relation). -/
noncomputable def jcFalsCA :
    MovesT.CellData 2 (ZMod 2) 2 1 2 MovesT.polTriv MovesT.sibModel where
  Cell := Fin 4
  hCellFin := inferInstance
  cellOf := jcFalsCellOf
  cellLevel := fun _ => 1
  levelOf := fun _ => 0
  cell_local := by
    intro es x x' h
    have hx : x = x' := funext fun c => h c (by norm_num)
    rw [hx]
  branchSetOf := jcFalsBranch
  child_cell := by
    intro H ν x hmem
    show MovesT.sibChild (some H) ν x ↔ _
    constructor
    · intro h
      exact (h : False).elim
    · intro hν
      exfalso
      by_cases hH : H = MovesT.t1
      · rw [show jcFalsCellOf (.st H) x = 2 from by
          simp only [jcFalsCellOf, if_pos hH]] at hν
        rw [show jcFalsBranch 2 = ∅ from by
          simp only [jcFalsBranch]; exact if_neg (by decide)] at hν
        exact absurd hν (Finset.notMem_empty ν)
      · rw [show jcFalsCellOf (.st H) x = 3 from by
          simp only [jcFalsCellOf, if_neg hH]] at hν
        rw [show jcFalsBranch 3 = ∅ from by
          simp only [jcFalsBranch]; exact if_neg (by decide)] at hν
        exact absurd hν (Finset.notMem_empty ν)
  child_root_sub := by
    intro ν x hchild
    have h : (ν = MovesT.toyHead ∨ ν = MovesT.sibNode2) ∧ x 0 = 0 := hchild
    show ν ∈ jcFalsBranch (jcFalsCellOf .amb x)
    rw [show jcFalsCellOf .amb x = 0 from rfl,
      show jcFalsBranch 0 = {MovesT.toyHead, MovesT.sibNode2} from by
        simp [jcFalsBranch]]
    simp only [Finset.mem_insert, Finset.mem_singleton]
    exact h.1
  child_cell_red := by
    intro χ g ψ ν x hx hν
    show (ν = MovesT.toyHead ∨ ν = MovesT.sibNode2) ∧ x 0 = 0
    by_cases h0 : x 0 = 0
    · refine ⟨?_, h0⟩
      rw [show jcFalsCellOf (.red g ψ) x = 0 from by
        simp only [jcFalsCellOf, if_pos h0]] at hν
      rw [show jcFalsBranch 0 = {MovesT.toyHead, MovesT.sibNode2} from by
        simp [jcFalsBranch]] at hν
      simpa only [Finset.mem_insert, Finset.mem_singleton] using hν
    · exfalso
      rw [show jcFalsCellOf (.red g ψ) x = 1 from by
        simp only [jcFalsCellOf, if_neg h0]] at hν
      rw [show jcFalsBranch 1 = ∅ from by
        simp only [jcFalsBranch]; exact if_neg (by decide)] at hν
      exact absurd hν (Finset.notMem_empty ν)
  child_red_uniform := by
    intro g ψ x y hcell ν
    have hxy : (x 0 = 0) ↔ (y 0 = 0) := by
      by_cases hx0 : x 0 = 0 <;> by_cases hy0 : y 0 = 0
      · exact iff_of_true hx0 hy0
      · exfalso
        rw [show jcFalsCellOf (.red g ψ) x = 0 from by
              simp only [jcFalsCellOf, if_pos hx0],
            show jcFalsCellOf (.red g ψ) y = 1 from by
              simp only [jcFalsCellOf, if_neg hy0]] at hcell
        exact absurd hcell (by decide)
      · exfalso
        rw [show jcFalsCellOf (.red g ψ) x = 1 from by
              simp only [jcFalsCellOf, if_neg hx0],
            show jcFalsCellOf (.red g ψ) y = 0 from by
              simp only [jcFalsCellOf, if_pos hy0]] at hcell
        exact absurd hcell (by decide)
      · exact iff_of_false hx0 hy0
    show (ν = MovesT.toyHead ∨ ν = MovesT.sibNode2) ∧ x 0 = 0
      ↔ (ν = MovesT.toyHead ∨ ν = MovesT.sibNode2) ∧ y 0 = 0
    rw [hxy]
  branchCellOf := fun es _ x => jcFalsCellOf es x
  branch_cell_joint := by
    intro es ν x y h
    exact h

/-- the box point `0` — the shared witness of both entrance events. -/
noncomputable def jcFalsPt : MovesD.Box 2 2 := fun _ => 0

lemma jcFals_mem_t1 :
    jcFalsPt ∈ MovesT.entEvent MovesT.sibModel MovesT.toyχ2
      (MovesT.EntSt.st MovesT.t1) :=
  show MovesT.sibMem (some MovesT.t1) jcFalsPt from ⟨Or.inl rfl, rfl⟩

lemma jcFals_mem_t2 :
    jcFalsPt ∈ MovesT.entEvent MovesT.sibModel MovesT.toyχ2
      (MovesT.EntSt.st MovesT.t2) :=
  show MovesT.sibMem (some MovesT.t2) jcFalsPt from ⟨Or.inr rfl, rfl⟩

/-- the retained key ignores `center`: the two last nodes are key-equal. -/
lemma jcFals_keyEq :
    NodeRetainedKeyEq MovesT.t1.lastNode MovesT.t2.lastNode := by
  have h1 : MovesT.t1.lastNode = MovesT.toyHead := by
    show (MovesT.t1.nodes).getLast _ = MovesT.toyHead
    rw [List.getLast_eq_iff_getLast?_eq_some]
    rfl
  have h2 : MovesT.t2.lastNode = MovesT.sibNode2 := by
    show (MovesT.t2.nodes).getLast _ = MovesT.sibNode2
    rw [List.getLast_eq_iff_getLast?_eq_some]
    rfl
  rw [h1, h2]
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- IB-G11c falsifier 2/4 (jcInvHist): `Slot_jcInvHist` is FALSE at some
    degree n — witnessed by a degenerate history-reading `CellData` inside the
    ∀-quantified instance (wave-2 doctrine).  Prover: build the chain-length
    joint read toy (file-header sketch). -/
theorem slot_jcInvHist_falsifiable :
    ∃ n : ℕ, ¬ Slot_jcInvHist n := by
  refine ⟨2, fun hslot => ?_⟩
  have heq := hslot 2 1 2 MovesT.polTriv MovesT.sibModel jcFalsCA MovesT.toyχ2
    MovesT.t1 MovesT.t2 ⟨jcFalsPt, jcFals_mem_t1⟩ ⟨jcFalsPt, jcFals_mem_t2⟩
    jcFals_keyEq (2 : Fin 4)
  -- the (.st t2) fiber of cell 2 is EMPTY (its joint read is the constant 3):
  haveI hem : IsEmpty ↥(MovesT.cellEventE MovesT.sibModel jcFalsCA MovesT.toyχ2
      (MovesT.EntSt.st MovesT.t2) (2 : Fin 4)) := by
    refine ⟨fun z => ?_⟩
    have hc : jcFalsCellOf (.st MovesT.t2) z.1 = 2 := z.2.2
    rw [show jcFalsCellOf (.st MovesT.t2) z.1 = 3 from by
      simp only [jcFalsCellOf]
      exact if_neg (fun h => MovesT.t1_ne_t2 h.symm)] at hc
    exact absurd hc (by decide)
  -- the (.st t1) fiber of cell 2 and both entrance events are NONEMPTY:
  haveI hne1 : Nonempty ↥(MovesT.cellEventE MovesT.sibModel jcFalsCA MovesT.toyχ2
      (MovesT.EntSt.st MovesT.t1) (2 : Fin 4)) := by
    refine ⟨⟨jcFalsPt, jcFals_mem_t1, ?_⟩⟩
    show jcFalsCellOf (.st MovesT.t1) jcFalsPt = 2
    rw [show jcFalsCellOf (.st MovesT.t1) jcFalsPt
        = if MovesT.t1 = MovesT.t1 then 2 else 3 from rfl, if_pos rfl]
  haveI hne2 : Nonempty ↥(MovesT.entEvent MovesT.sibModel MovesT.toyχ2
      (MovesT.EntSt.st MovesT.t2)) := ⟨⟨jcFalsPt, jcFals_mem_t2⟩⟩
  -- cross-multiplied law: positive = 0 — contradiction:
  rw [Nat.card_of_isEmpty (α := ↥(MovesT.cellEventE MovesT.sibModel jcFalsCA
    MovesT.toyχ2 (MovesT.EntSt.st MovesT.t2) (2 : Fin 4))), zero_mul] at heq
  have hpos := Nat.mul_pos
    (Nat.card_pos (α := ↥(MovesT.cellEventE MovesT.sibModel jcFalsCA MovesT.toyχ2
      (MovesT.EntSt.st MovesT.t1) (2 : Fin 4))))
    (Nat.card_pos (α := ↥(MovesT.entEvent MovesT.sibModel MovesT.toyχ2
      (MovesT.EntSt.st MovesT.t2))))
  omega

end JcFalsifier

/- BLOCKED (recorded; not elaborable at write time):
   falsifier 3/4 (m1m5Echo) — needs `Slot_m1m5Echo` (IB-G7, sibling cluster);
   falsifier 4/4 (x1aDict)  — needs `Slot_x1aDict`  (IB-G8, sibling cluster).
   Disposition: NEW follow-up file once G7/G8 land (this file stays unedited). -/

end LeanUrat.MovesU
