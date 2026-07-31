/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.MovesU.BridgeVerdictDeg
import LeanUrat.MovesU.BridgeB15a_r2Neg
import LeanUrat.MovesS.N2Shape

/-!
# IB-B19 — the VerdictDeg/DegConsDelta GATE (queue item 9 threading evidence)

The non-vacuity pair for IB-B18's additive sibling laws, compiled:

* CONTENTFULNESS (falsifiers): the IB-B15a countermodel table `R2Neg.cmT`
  VIOLATES both laws — `vdeg_size` at the recorded degree cheat (the t₂ exit's
  (1,2) verdict on a size-1, δ = 1 member: 2 ≠ 1·1) and `size_sum_delta` at
  the reader's second recorded cheat (the block-2 split outcome: 1·1 + 1·2 =
  3 > e = 2, invisible to the as-built `DegCons.size_sum` since 1 + 1 ≤ 2).
  So the new laws EXCLUDE exactly the cheats the countermodel record named.
* SATISFIABILITY (real-instance witnesses): the carried n = 2 table `n2T`
  (MovesS/N2Shape.lean — the instance the whole §S n = 2 wiring rides)
  SATISFIES both laws, so they are consistent with the real corpus and
  available as named hypothesis rows at the instance.

IMPORT NOTE: importing `BridgeB15a_r2Neg` here is legal as of the item-9
commit — the sorried universal its coexistence rule guarded against was
deleted in that same commit (see the dated note at the end of that file).
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesU

open MovesS

/-! ## Falsifiers at the countermodel table -/

/-- FALSIFIER 1 (the recorded degree cheat): `cmT` violates `vdeg_size` — the
    block-1 t₂ exit halts a size-1, δ = 1 member with the degree-2 verdict
    (1,2). -/
theorem cmT_not_verdictDeg : ¬ VerdictDeg R2Neg.cmT := by
  intro h
  have hμ : (⟨1, 1, Sum.inl ⟨((1 : ℕ+), (2 : ℕ+)), by decide⟩⟩ :
      Member R2Neg.cmT.VType R2Neg.cmT.State)
      ∈ (R2Neg.cmT.odata 1 R2Neg.τ1 ((2 : Fin 3))).mem := List.mem_singleton.mpr rfl
  have h2 := h.vdeg_size 1 (by decide) R2Neg.τ1 ((2 : Fin 3)) _ hμ
    ⟨((1 : ℕ+), (2 : ℕ+)), by decide⟩ rfl
  exact absurd h2 (by decide)

/-- FALSIFIER 2 (the reader's second cheat, item 9(iii)): `cmT` violates
    `size_sum_delta` — the block-2 split outcome's δ-weighted size sum is
    1·1 + 1·2 = 3 > e = 2 (the as-built `DegCons.size_sum` sees only
    1 + 1 ≤ 2). -/
theorem cmT_not_degConsDelta : ¬ DegConsDelta R2Neg.cmT := by
  intro h
  have h2 := h.size_sum_delta 2 (by decide) R2Neg.τ2 ((0 : Fin 3))
  exact absurd h2 (by decide)

/-! ## Witnesses at the real n = 2 instance -/

/-- The n2T roster reduction, block 2 (the e = 2 outcomes are the three
    concrete rosters; defeq to the private construction data). -/
private lemma n2_mem2 (τ : n2T.State 2) (o : Fin 3) :
    (n2T.odata 2 τ o).mem =
      (if o = 0 then [⟨2, 1, Sum.inr ()⟩]
       else if o = 1 then
        [⟨1, 1, Sum.inl ⟨((1 : ℕ+), (1 : ℕ+)), by decide⟩⟩,
         ⟨1, 1, Sum.inl ⟨((1 : ℕ+), (1 : ℕ+)), by decide⟩⟩]
       else [⟨2, 1, Sum.inl ⟨((1 : ℕ+), (2 : ℕ+)), by decide⟩⟩]) := by
  fin_cases o <;> rfl

/-- The n2T roster reduction, block 1 (o-independent). -/
private lemma n2_mem1 (τ : n2T.State 1) (o : Fin 3) :
    (n2T.odata 1 τ o).mem =
      [⟨1, 1, Sum.inl ⟨((1 : ℕ+), (1 : ℕ+)), by decide⟩⟩] := rfl

/-- SATISFIABILITY 1: the real n = 2 table carries the verdict-degree law —
    every halted member's verdict degree equals its δ-weighted size. -/
theorem n2T_verdictDeg : VerdictDeg n2T := by
  constructor
  intro e he τ o μ hμ v hv
  obtain ⟨h1, h2⟩ := Finset.mem_Icc.mp he
  interval_cases e
  · rw [n2_mem1 τ o] at hμ
    simp only [List.mem_singleton] at hμ
    subst hμ
    obtain rfl : (⟨((1 : ℕ+), (1 : ℕ+)), by decide⟩ : n2T.VType) = v :=
      Sum.inl.inj hv
    decide
  · rw [n2_mem2 τ o] at hμ
    split_ifs at hμ with h0 h1'
    · simp only [List.mem_singleton] at hμ
      subst hμ
      exact absurd hv (by simp)
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hμ
      rcases hμ with rfl | rfl <;>
        · obtain rfl : (⟨((1 : ℕ+), (1 : ℕ+)), by decide⟩ : n2T.VType) = v :=
            Sum.inl.inj hv
          decide
    · simp only [List.mem_singleton] at hμ
      subst hμ
      obtain rfl : (⟨((1 : ℕ+), (2 : ℕ+)), by decide⟩ : n2T.VType) = v :=
        Sum.inl.inj hv
      decide

/-- SATISFIABILITY 2: the real n = 2 table carries the δ-weighted size-sum
    law (all δ = 1 there, so the sums are the plain `size_sum` sums). -/
theorem n2T_degConsDelta : DegConsDelta n2T := by
  constructor
  intro e he τ o
  obtain ⟨h1, h2⟩ := Finset.mem_Icc.mp he
  interval_cases e
  · rw [n2_mem1 τ o]; decide
  · rw [n2_mem2 τ o]; split_ifs <;> decide

end LeanUrat.MovesU
