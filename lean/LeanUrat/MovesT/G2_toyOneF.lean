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
  intro x _hdec
  refine ⟨toyTreeA, ⟨⟨show toyTreeA ∈ ({toyTreeA} : Finset (VTree 2 (ZMod 2))) from
    Finset.mem_singleton_self _, ?_⟩, ?_⟩⟩
  · -- BLOCKED (statement appears FALSE): goal is `toyFiber toyTreeA x`, i.e.
    -- `toyTreeA.fiberAt toyModel toyχ x`, which (by G1's `fiberA_iff`) forces the
    -- all-zero digit stratum x0=…=x5=0. But `ToyDecided x = ∃ Tr, Tr.fiberAt` is
    -- satisfiable OFF that stratum: for any x with `redPoly toyχ x` irreducible
    -- (e.g. x0=x1=1 ⇒ X²+X+1), the empty-chains tree with `henV := henPayload toyχ x`
    -- (a single `henVerdict 2`) satisfies every fiberAt clause (chains=∅ ⇒ (i)/(ii)/(iv)/(vi)
    -- hold; (iii) by construction; (v) typemult product-sum = 1·2 = 2 = n). Then
    -- ToyDecided x holds yet NO member of `toyTrees = {toyTreeA}` fibers x. See notes.
    sorry
  · rintro y ⟨hy, -⟩
    exact Finset.mem_singleton.mp (show y ∈ ({toyTreeA} : Finset (VTree 2 (ZMod 2)))
      from hy)

/-- the dictionary gap EXHIBITED (expected witness value 2 — the REV-9 recomputed
gate). -/
theorem toy_belowHalt_pos : ∃ x, 0 < toyBelowHaltExcess x := by
  classical
  refine ⟨fun _ => 0, ?_⟩
  have hmem : toyMemA (some tA1) (fun _ : Fin 9 => (0 : ZMod 2)) :=
    ⟨Or.inl rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  have hirr : IrrHalts tA2a := ⟨tA2a.nonempty, rfl⟩
  have hnph : ∀ (ν : Node 2 (ZMod 2)) (hν : ν.species ≠ ReadSpecies.root),
      ¬ PreHalt (tA2a.snoc ν hν) := by
    intro ν hν hph
    have hpre : tA2a.IsPrefixOf (tA2a.snoc ν hν) := ⟨[ν], rfl⟩
    have hne : tA2a ≠ tA2a.snoc ν hν := by
      intro heq
      have h := congrArg (fun K : History 2 (ZMod 2) => K.nodes.length) heq
      simp only [History.snoc, List.length_append, List.length_cons,
        List.length_nil] at h
      omega
    exact hph tA2a hpre hne tA2a.nonempty hirr
  unfold toyBelowHaltExcess
  rw [Nat.card_pos_iff]
  refine ⟨⟨⟨tA2a.snoc toyLeafA toyLeafA_nonroot, Or.inl rfl, hmem,
      hnph toyLeafA toyLeafA_nonroot⟩⟩, ?_⟩
  have hfin : ({H : History 2 (ZMod 2) |
      (H = tA2a.snoc toyLeafA toyLeafA_nonroot ∨
        H = tA2a.snoc toyLeafB toyLeafB_nonroot) ∧
      toyMemA (some tA1) (fun _ => 0) ∧ ¬ PreHalt H}).Finite := by
    apply Set.Finite.subset ((Set.finite_singleton
      (tA2a.snoc toyLeafB toyLeafB_nonroot)).insert
      (tA2a.snoc toyLeafA toyLeafA_nonroot))
    rintro H ⟨h, -⟩
    rcases h with h | h
    · exact Or.inl h
    · exact Or.inr h
  exact hfin.to_subtype

end LeanUrat.MovesT
