/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.MovesT.Defs

/-! # T-D2 `eligible_nonvacuity` — W4-1(b)'s non-vacuity roster (MovesD §2.5 W4-1(b))
+ the REV-7/8 W4-1-LAYER falsification (`constFalse_childCover_false`,
`constFalse_no_cellAssign` — the INSTALLED rejection, §0 record 23; both PROVED,
E-phase prove-now set, fence-free). The five-round W4-1 adjudication history rides in
the blueprint. `RejectsRootOnlyChildless` (DO-2) is the displayed decl below. -/

set_option linter.style.longLine false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesT

open Polynomial LeanUrat.Moves LeanUrat.MovesC LeanUrat.MovesD

variable {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
variable {n N m : ℕ} {pol : CanonPolicy p F}

/-- T-D2's predicate (DO-2, formerly a bracket note): on every window-opening input,
the root-only childless tree FAILS `fiberAt` — for the given model/chart. -/
def RejectsRootOnlyChildless (T : TreeModel p F n N m pol)
    (CA : CellData p F n N m pol T) (χ : Fin n → Fin m) : Prop :=
  ∀ x : Box p m,
    (∃ ψ, ψ ∈ UniqueFactorizationMonoid.normalizedFactors (redPoly χ x) ∧
      2 ≤ Multiset.count ψ (UniqueFactorizationMonoid.normalizedFactors (redPoly χ x))) →
    ∀ Tr : VTree p F, Tr.chains = ∅ → ¬ Tr.fiberAt T χ x

/-- the GENERAL in-corpus rejection (REV 3, Codex-2 #16): through fiberAt's degree
clause (v)/(vi), for EVERY model and EVERY CellData. -/
theorem rootOnly_childless_rejected (T : TreeModel p F n N m pol)
    (χ : Fin n → Fin m) (hχ : Function.Injective χ) (x : Box p m)
    (hrep : ∃ ψ, ψ ∈ UniqueFactorizationMonoid.normalizedFactors (redPoly χ x) ∧
      2 ≤ Multiset.count ψ (UniqueFactorizationMonoid.normalizedFactors (redPoly χ x)))
    (Tr : VTree p F) (hchains : Tr.chains = ∅) : ¬ Tr.fiberAt T χ x := by
  intro hfib
  obtain ⟨-, -, -, -, -, hvi⟩ := hfib
  -- chains = ∅ ⇒ the head chains are empty ⇒ clause (vi)'s LHS is the empty multiset
  have hchainsFin : Tr.hfin.toFinset = ∅ := by
    rw [Set.Finite.toFinset_eq_empty]; exact hchains
  have hheads : Tr.heads = ∅ := by
    simp only [VTree.heads, hchainsFin, Finset.filter_empty]
  rw [hheads, Finset.empty_val, Multiset.map_zero] at hvi
  -- so clause (vi)'s RHS multiset (over the repeated factors) is empty
  have hRHS := hvi.symm
  rw [Multiset.map_eq_zero, Finset.val_eq_zero] at hRHS
  -- but hrep exhibits a repeated factor ψ, contradicting the empty filtered finset
  obtain ⟨ψ, hmem, hcount⟩ := hrep
  have hψ : ψ ∈ ((UniqueFactorizationMonoid.normalizedFactors (redPoly χ x)).toFinset.filter
      (fun ψ => 2 ≤ Multiset.count ψ
        (UniqueFactorizationMonoid.normalizedFactors (redPoly χ x)))) := by
    rw [Finset.mem_filter, Multiset.mem_toFinset]
    exact ⟨hmem, hcount⟩
  rw [hRHS] at hψ
  simp only [Finset.notMem_empty] at hψ

theorem no_childless_vacuity (T : TreeModel p F n N m pol)
    (CA : CellData p F n N m pol T)
    (h : ∃ (H : History p F) (ν : Node p F) (x : Box p m),
      T.mem (some H) x ∧ T.child (some H) ν x) :
    ∃ (H : History p F) (ν : Node p F) (x : Box p m),
      eligibleT T CA (some H) ν x := by
  obtain ⟨H, ν, x, hmem, hchild⟩ := h
  exact ⟨H, ν, x, (CA.child_cell H ν x hmem).mp hchild⟩

theorem cellOf_nonconstant (T : TreeModel p F n N m pol)
    (CA : CellData p F n N m pol T)
    (h : ∃ (H : History p F) (ν : Node p F) (x x' : Box p m),
      T.mem (some H) x ∧ T.mem (some H) x' ∧
      T.child (some H) ν x ∧ ¬ T.child (some H) ν x') :
    ∃ (es : EntSt p F n) (x x' : Box p m), CA.cellOf es x ≠ CA.cellOf es x' := by
  obtain ⟨H, ν, x, x', hx, hx', hc, hnc⟩ := h
  refine ⟨.st H, x, x', fun heq => hnc ?_⟩
  have h1 := (CA.child_cell H ν x hx).mp hc
  rw [heq] at h1
  exact (CA.child_cell H ν x' hx').mpr h1

/-- the toy leg (Gates layer; DO-2 plumbing) — witnesses live at T-G1. -/
theorem eligible_nonvacuity_toy :
    ∃ (T : TreeModel 2 (ZMod 2) 2 3 9 polTriv)
      (CA : CellData 2 (ZMod 2) 2 3 9 polTriv T)
      (o : Option (History 2 (ZMod 2))) (ν : Node 2 (ZMod 2)) (x : Box 2 9),
      eligibleT T CA o ν x ∧ RejectsRootOnlyChildless T CA toyχ := by
  sorry

/-- NEW at REV 7 (ruling 1): the W4-1-LAYER falsification, in-corpus, fence-free.
PROVED. -/
theorem constFalse_childCover_false
    (T : TreeModel p F n N m pol) (CA : CellData p F n N m pol T)
    (χ : Fin n → Fin m) (trackOf : Node p F → Polynomial (ZMod p))
    (hnochild : ∀ ν x, ¬ T.child none ν x)
    (hwin : ∃ (g : Fin n → ZMod p) (x : Box p m), x ∈ rootCell χ g ∧
      ∃ ψ, ψ ∈ UniqueFactorizationMonoid.normalizedFactors (redPoly χ x) ∧
        2 ≤ Multiset.count ψ
          (UniqueFactorizationMonoid.normalizedFactors (redPoly χ x))) :
    ¬ ChildCover T CA χ trackOf := by
  intro hcov
  obtain ⟨g, x, hx, ψ, hmem, hcount⟩ := hwin
  obtain ⟨ν, _, hchild, _⟩ := hcov g x hx ψ hmem hcount
  exact hnochild ν x hchild

/-- NEW at REV 8 (Codex-7 #1): the INSTALLED form — the forbidden model admits NO
instance of the W4-1 interface AT ALL. PROVED. -/
theorem constFalse_no_cellAssign
    (T : TreeModel p F n N m pol)
    (χ : Fin n → Fin m) (trackOf : Node p F → Polynomial (ZMod p))
    (hnochild : ∀ ν x, ¬ T.child none ν x)
    (hwin : ∃ (g : Fin n → ZMod p) (x : Box p m), x ∈ rootCell χ g ∧
      ∃ ψ, ψ ∈ UniqueFactorizationMonoid.normalizedFactors (redPoly χ x) ∧
        2 ≤ Multiset.count ψ
          (UniqueFactorizationMonoid.normalizedFactors (redPoly χ x))) :
    IsEmpty (CellAssign p F n N m pol T χ trackOf) :=
  ⟨fun CA =>
    constFalse_childCover_false T CA.toCellData χ trackOf hnochild hwin
      CA.child_cover⟩

end LeanUrat.MovesT
