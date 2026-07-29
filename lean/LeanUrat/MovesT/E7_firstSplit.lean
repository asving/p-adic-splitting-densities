/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.MovesT.Defs

/-! # T-E7 `fiber_first_split` [hard] — FIRST SPLIT (MOVES 7503–7515): (A) the SIB
product at the cell event through `hdecomp`; (B) the charge-composed display with
`hcharge` CONSUMED. The frame prices its OWN `scope` (REV 5, Codex-4 #3);
`belowEnt`/`SubtreeFiber`/`SplitSiteData` are Defs carriers (REV 6, Codex-5 gap #9).
`hcharge` is discharged by T-E3 at one-side sites and rides as `JCmultiAt` (hjcm) at
multi-side sites. -/

set_option linter.style.longLine false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesT

open Polynomial LeanUrat.Moves LeanUrat.MovesC LeanUrat.MovesD

variable {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
variable {n N m : ℕ} {pol : CanonPolicy p F}

theorem fiber_first_split (Tr : VTree p F) (T : TreeModel p F n N m pol)
    (CA : CellData p F n N m pol T) (χ : Fin n → Fin m)
    (hsib : SibCount T CA χ) (d : SplitSiteData Tr T CA χ)
    (hcharge : Nat.card ↥(cellEventE T CA χ d.es d.c) * p ^ d.jointExp
      = Nat.card ↥(entEvent T χ d.es)) :
    (Nat.card ↥(d.scope ∩ entEvent T χ d.es)
        * (Nat.card ↥(cellEventE T CA χ d.es d.c)) ^ ((CA.branchSetOf d.c).card - 1)
      = ∏ ν ∈ CA.branchSetOf d.c,
          Nat.card ↥(cellEventE T CA χ d.es d.c ∩ d.S ν)) ∧
    (Nat.card ↥(d.scope ∩ entEvent T χ d.es) * p ^ d.jointExp
        * (Nat.card ↥(cellEventE T CA χ d.es d.c)) ^ (CA.branchSetOf d.c).card
      = Nat.card ↥(entEvent T χ d.es)
        * ∏ ν ∈ CA.branchSetOf d.c,
            Nat.card ↥(cellEventE T CA χ d.es d.c ∩ d.S ν)) := by
  -- (A): apply (SIB) at (es, c, S); then identify the scope∩ent count via `hdecomp`.
  have hA := hsib d.es d.c d.S d.hbr d.hS
  rw [d.hdecomp]
  refine ⟨hA, ?_⟩
  -- (B): multiply (A) by card(cell)·p^jointExp and consume `hcharge`.
  set X := Nat.card ↥(cellEventE T CA χ d.es d.c ∩ ⋂ ν ∈ CA.branchSetOf d.c, d.S ν)
  set C := Nat.card ↥(cellEventE T CA χ d.es d.c)
  set P := ∏ ν ∈ CA.branchSetOf d.c, Nat.card ↥(cellEventE T CA χ d.es d.c ∩ d.S ν)
  set Sg := Nat.card ↥(entEvent T χ d.es)
  have hb : (CA.branchSetOf d.c).card = ((CA.branchSetOf d.c).card - 1) + 1 := by
    have := d.hbr; omega
  rw [hb, pow_succ]
  have hrw : X * p ^ d.jointExp * (C ^ ((CA.branchSetOf d.c).card - 1) * C)
      = (X * C ^ ((CA.branchSetOf d.c).card - 1)) * (C * p ^ d.jointExp) := by ring
  rw [hrw, hA, hcharge]
  exact mul_comm P Sg

end LeanUrat.MovesT
