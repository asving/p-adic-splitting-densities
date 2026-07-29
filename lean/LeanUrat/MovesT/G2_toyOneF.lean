/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.MovesT.Defs
import LeanUrat.MovesT.G1_toyGate

/-! # T-G2 `toy_oneF_gate` — T-n3 Layer C's ONE-F face (MOVES 7745–7752): the
∃!-partition shape + a below-halt excess instance > 0 (the gap EXHIBITED, not just
typed). REV 9 (Fable-8 GAP-2): `toyBelowHaltExcess`'s roster matched TO THE GLOSS —
BOTH one-node extensions OF tA2a; expected gate value 2. -/

set_option linter.style.longLine false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesT

open Polynomial LeanUrat.Moves LeanUrat.MovesC LeanUrat.MovesD

open Classical in
noncomputable def toyTrees : Finset (VTree 2 (ZMod 2)) := {toyTreeA}

def toyFiber (Tr : VTree 2 (ZMod 2)) (x : Box 2 9) : Prop :=
  Tr.fiberAt toyModel toyχ x

def ToyDecided (x : Box 2 9) : Prop := Decided toyModel toyχ x

/-- T-G2's below-halt surrogate (REV 9 roster): the SYNTACTIC continuations
tA3 = tA2a.snoc tAνa and its tAνb twin extend BELOW tA2a's τ-irr halt, so both fail
`PreHalt`; the excess counts such marks on the enumerated roster. -/
noncomputable def toyBelowHaltExcess (x : Box 2 9) : ℕ :=
  Nat.card {H : History 2 (ZMod 2) //
    (H = tA2a.snoc toyLeafA toyLeafA_nonroot ∨
     H = tA2a.snoc toyLeafB toyLeafB_nonroot) ∧
    toyMemA (some tA1) x ∧ ¬ PreHalt H}

theorem toy_oneF : ∀ x, ToyDecided x →
    ∃! t, t ∈ toyTrees ∧ toyFiber t x := by
  sorry

/-- the dictionary gap EXHIBITED (expected witness value 2 — the REV-9 recomputed
gate). -/
theorem toy_belowHalt_pos : ∃ x, 0 < toyBelowHaltExcess x := by
  sorry

end LeanUrat.MovesT
