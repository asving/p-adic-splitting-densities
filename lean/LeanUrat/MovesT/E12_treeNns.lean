/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.MovesT.Defs
import LeanUrat.MovesT.C7_nsNull

/-! # T-E12 `treeN_ns` — for (ns)-leaf trees TREE-N is REPLACED by the NORMALIZED
capped bound (MOVES 7574–7576): domination + T-C7's vanishing ratio; the raw count
need NOT tend to 0 (§0 refutation record). -/

set_option linter.style.longLine false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesT

open Polynomial LeanUrat.Moves LeanUrat.MovesC LeanUrat.MovesD

variable {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
variable {n : ℕ} {pol : CanonPolicy p F}

theorem treeN_ns (Tr : VTree p F) (H : History p F)
    (hns : H ∈ Tr.chains ∧ Tr.nsLeaf H) (N₀ : ℕ)
    (Tat : ∀ N', N₀ ≤ N' → TreeModel p F n N' (n * N') pol)
    (χat : ∀ N', Fin n → Fin (n * N'))
    (Jat : ∀ N' (h : N₀ ≤ N'), JetSetup H n N' (n * N'))
    (Lat : ∀ N' (h : N₀ ≤ N'), NsLumpFamily (Tat N' h) (Jat N' h))
    (htw : JetTower Jat)
    (hzc : ∀ N' h, ZCPack (Jat N' h))
    (hM₀ : ∀ N' h, M₀ (Jat N' h) ≤ Mlev (Jat N' h) N')
    (hMgrow : Filter.Tendsto
      (fun N' : {k // N₀ ≤ k} => Mlev (Jat N'.1 N'.2) N'.1 - M₀ (Jat N'.1 N'.2))
      Filter.atTop Filter.atTop)
    (hne : ∀ N' (h : N₀ ≤ N'), (stateTruncAt Jat N').Nonempty)
    (hdom : ∀ N' (h : N₀ ≤ N'),
      {x : Box p (n * N') | Tr.fiberAt (Tat N' h) (χat N') x}
      ⊆ nsTruncAt Jat Lat N') :
    Filter.Tendsto
      (fun N' : {k // N₀ ≤ k} => (Nat.card ↥{x : Box p (n * N'.1) |
          Tr.fiberAt (Tat N'.1 N'.2) (χat N'.1) x} : ℝ) / (p : ℝ) ^ (n * N'.1))
      Filter.atTop (nhds 0) := by
  -- T-C7 (`ns_null`): the truncated ns-lump ratio |nsTruncAt| / |stateTruncAt| → 0.
  have hnull := ns_null (H := H) N₀ Tat Jat Lat htw hzc hM₀ hMgrow hne
  -- Squeeze: 0 ≤ |fiber| / p^{nN} ≤ |nsTruncAt| / |stateTruncAt|.
  refine squeeze_zero (fun N' => by positivity) (fun N' => ?_) hnull
  haveI : NeZero p := ⟨(Fact.out (p := p.Prime)).pos.ne'⟩
  -- (i) DOMINATION (hdom = T-C8's inclusion): the fiber is inside the truncated lump.
  have hfb : Nat.card ↥{x : Box p (n * N'.1) | Tr.fiberAt (Tat N'.1 N'.2) (χat N'.1) x}
      ≤ Nat.card ↥(nsTruncAt Jat Lat N'.1) :=
    Set.ncard_le_ncard (hdom N'.1 N'.2) (Set.toFinite (nsTruncAt Jat Lat N'.1))
  -- (ii) STATE COUNT ≤ p^{nN}: states live in the full box `Fin (n*N') → ZMod p`.
  have hboxcard : Nat.card (Box p (n * N'.1)) = p ^ (n * N'.1) := by
    rw [Nat.card_eq_fintype_card, Fintype.card_fun, ZMod.card, Fintype.card_fin]
  have hDle : Nat.card ↥(stateTruncAt Jat N'.1) ≤ p ^ (n * N'.1) := by
    rw [← hboxcard]
    exact Nat.card_le_card_of_injective _ Subtype.val_injective
  -- (iii) DENOMINATOR POSITIVE: realized states are nonempty (`hne`).
  have hDpos : 0 < Nat.card ↥(stateTruncAt Jat N'.1) := by
    haveI : Nonempty ↥(stateTruncAt Jat N'.1) := (hne N'.1 N'.2).to_subtype
    exact Nat.card_pos
  -- Real casts.
  have hp0 : (0 : ℝ) < (p : ℝ) := by
    have := (Fact.out : p.Prime).pos; exact_mod_cast this
  have hpPpos : (0 : ℝ) < (p : ℝ) ^ (n * N'.1) := pow_pos hp0 _
  have hDposR : (0 : ℝ) < (Nat.card ↥(stateTruncAt Jat N'.1) : ℝ) := by exact_mod_cast hDpos
  have hfbR : (Nat.card ↥{x : Box p (n * N'.1) | Tr.fiberAt (Tat N'.1 N'.2) (χat N'.1) x} : ℝ)
      ≤ (Nat.card ↥(nsTruncAt Jat Lat N'.1) : ℝ) := by exact_mod_cast hfb
  have hDleR : (Nat.card ↥(stateTruncAt Jat N'.1) : ℝ) ≤ (p : ℝ) ^ (n * N'.1) := by
    exact_mod_cast hDle
  -- Assemble: |fiber|/p^{nN} ≤ |nsTruncAt|/|stateTruncAt|.
  rw [div_le_div_iff₀ hpPpos hDposR]
  exact mul_le_mul hfbR hDleR (le_of_lt hDposR) (Nat.cast_nonneg _)

end LeanUrat.MovesT
