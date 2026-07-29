/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.MovesT.Defs

/-! # T-E9 `tree_fiber_disjoint` — "one f, ONE tree … a genuine PARTITION of the
decided set" (MOVES 7025–7029). TRUE under the repaired `fiberAt` (REV 2, Codex 14).
The conclusion IS `VTree.ext Tr Tr'` definitionally — the quotient bridge T-F1/T-E13
consume. The CHOICE-FREENESS payoff, unconditional. -/

set_option linter.style.longLine false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesT

open Polynomial LeanUrat.Moves LeanUrat.MovesC LeanUrat.MovesD

variable {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
variable {n N m : ℕ} {pol : CanonPolicy p F}

theorem tree_fiber_disjoint (Tr Tr' : VTree p F) (T : TreeModel p F n N m pol)
    (χ : Fin n → Fin m) (x : Box p m)
    (h : Tr.fiberAt T χ x) (h' : Tr'.fiberAt T χ x) :
    Tr.chains = Tr'.chains ∧ Tr.henV = Tr'.henV ∧
    ∀ H ∈ Tr.chains, Tr.leafV H = Tr'.leafV H ∧ (Tr.nsLeaf H ↔ Tr'.nsLeaf H) := by
  obtain ⟨hi, hii, hiii, hiv, hv, hvi⟩ := h
  obtain ⟨hi', hii', hiii', hiv', hv', hvi'⟩ := h'
  -- clause (i): chains equal (both equal the pruned-realized-prefix set)
  have hchains : Tr.chains = Tr'.chains := by
    ext H; rw [hi H, hi' H]
  -- clause (iii): hen payloads equal (both equal `henPayload χ x`)
  have hhen : Tr.henV = Tr'.henV := by rw [hiii, hiii']
  refine ⟨hchains, hhen, ?_⟩
  intro H hH
  have hH' : H ∈ Tr'.chains := hchains ▸ hH
  by_cases hmax : IsMaximalIn Tr.chains H
  · -- H is a leaf: clause (ii) pins the verdict VALUE on the leg decided by `IrrHalts H`
    have hmax' : IsMaximalIn Tr'.chains H := hchains ▸ hmax
    have L := hii H hH hmax
    have L' := hii' H hH' hmax'
    by_cases hirr : IrrHalts H
    · -- irr leg on both trees (ns leg would require ¬IrrHalts H)
      rcases L with ⟨_, hns, hlv⟩ | ⟨_, hnirr, _, _⟩
      · rcases L' with ⟨_, hns', hlv'⟩ | ⟨_, hnirr', _, _⟩
        · exact ⟨hlv.trans hlv'.symm, iff_of_false hns hns'⟩
        · exact absurd hirr hnirr'
      · exact absurd hirr hnirr
    · -- ns leg on both trees (irr leg would require IrrHalts H)
      rcases L with ⟨hirrL, _, _⟩ | ⟨_, _, hnsleaf, hlv⟩
      · exact absurd hirrL hirr
      · rcases L' with ⟨hirrL', _, _⟩ | ⟨_, _, hnsleaf', hlv'⟩
        · exact absurd hirrL' hirr
        · exact ⟨hlv.trans hlv'.symm, iff_of_true hnsleaf hnsleaf'⟩
  · -- H is not a leaf: `hleaf`/`hns_leaf` force leafV = none and ¬nsLeaf on both
    have hmax' : ¬ IsMaximalIn Tr'.chains H := fun hc => hmax (hchains ▸ hc)
    have hlv : Tr.leafV H = none :=
      Option.not_isSome_iff_eq_none.mp (by rw [Tr.hleaf H]; exact fun hc => hmax hc.2)
    have hlv' : Tr'.leafV H = none :=
      Option.not_isSome_iff_eq_none.mp (by rw [Tr'.hleaf H]; exact fun hc => hmax' hc.2)
    have hns : ¬ Tr.nsLeaf H := fun hc => hmax (Tr.hns_leaf H hc).2
    have hns' : ¬ Tr'.nsLeaf H := fun hc => hmax' (Tr'.hns_leaf H hc).2
    exact ⟨hlv.trans hlv'.symm, iff_of_false hns hns'⟩

end LeanUrat.MovesT
