/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.MovesT.Defs

/-! # T-V8 `shapeOfH_matches` — the L3 dictionary bridge under the KEYING-CONSTANT-FREE
fragment `HistLawful` (§2.2's displayed 12-clause ShapeWF roster + 13-conjunct Matches
roster). FENCE NOTE (REV 4/5): `HistLawful` pins NO keying CONSTANT; no unit of this
corpus premises `HistoryCoherent`. InBox is subsumed by the root-box clause.
REGRESSION GATES: `toy_v8_wchain`/`toy_v8_monic` (T-G1). `acc_pos` is the REV-2
guard-death statement, PROVED here. -/

set_option linter.style.longLine false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesT

open Polynomial LeanUrat.Moves LeanUrat.MovesC LeanUrat.MovesD

variable {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]

theorem shapeOfH_matches (H : History p F) (n : ℕ) (hlaw : HistLawful p n H) :
    (shapeOfH H n).MatchesHist H ∧ ShapeWF n (shapeOfH H n) := by
  sorry

/-- the (τ-irr) junk guards are DEAD under per-node lawfulness (REV 2, Codex 4). -/
theorem acc_pos (H : History p F) (hlaw : NodeDataLawful p H) :
    max (accE H) 1 = accE H ∧ max (accF H) 1 = accF H := by
  have hE : 1 ≤ accE H := by
    have : 0 < (H.nodes.map fun ν => ν.e).prod := by
      apply List.prod_pos
      intro a ha
      obtain ⟨ν, hν, rfl⟩ := List.mem_map.mp ha
      exact lt_of_lt_of_le Nat.zero_lt_one (hlaw ν hν).1
    exact this
  have hF : 1 ≤ accF H := by
    have : 0 < (H.nodes.map fun ν => ν.g).prod := by
      apply List.prod_pos
      intro a ha
      obtain ⟨ν, hν, rfl⟩ := List.mem_map.mp ha
      exact lt_of_lt_of_le Nat.zero_lt_one (hlaw ν hν).2.1
    exact this
  exact ⟨Nat.max_eq_left hE, Nat.max_eq_left hF⟩

/-- REV 4 (Fable-3 GAP-2): the `readOf` w-guard is DEAD on the lawful domain — w₀ = 1
+ w-mult + g ≥ 1 give card K_i ≥ p, so the factorization exponent is ≥ 1. -/
theorem readOf_guards_dead (H : History p F) (n : ℕ) (hlaw : HistLawful p n H)
    (i : ℕ) (hi : i < H.nodes.length) :
    max ((Nat.card ↥(H.nodes[i]'hi).σ.K).factorization p) 1
      = (Nat.card ↥(H.nodes[i]'hi).σ.K).factorization p := by
  sorry

end LeanUrat.MovesT
