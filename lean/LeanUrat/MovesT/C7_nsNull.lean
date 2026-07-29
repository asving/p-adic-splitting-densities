/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.MovesT.Defs
import LeanUrat.MovesT.C4_nsLadder
import LeanUrat.MovesT.C6_nsPrice

/-! # T-C7 `ns_null` — THE FINITE-LEVEL FACE of (ns-null) (MOVES 7210–7231). SCOPE
RIDER (binding on every consumer, quoted in T-D12's S-2 row): this corpus states ONLY
the truncated-ratio limit; continuity-from-above and the profinite class NEVER enter.
`Mlev`/`JetTower`/`stateTruncAt`/`nsTruncAt` are Defs §2.5a/§2.10 carriers (the
stateTruncAt/nsTruncAt junk-total `dite` is an E-DEV, MANIFEST). -/

set_option linter.style.longLine false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesT

open Polynomial LeanUrat.Moves LeanUrat.MovesC LeanUrat.MovesD

variable {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
variable {n : ℕ} {pol : CanonPolicy p F}

theorem ns_null {H : History p F} (N₀ : ℕ)
    (Tat : ∀ N', N₀ ≤ N' → TreeModel p F n N' (n * N') pol)
    (Jat : ∀ N' (h : N₀ ≤ N'), JetSetup H n N' (n * N'))
    (Lat : ∀ N' (h : N₀ ≤ N'), NsLumpFamily (Tat N' h) (Jat N' h))
    (htw : JetTower Jat)
    (hzc : ∀ N' h, ZCPack (Jat N' h))
    (hM₀ : ∀ N' h, M₀ (Jat N' h) ≤ Mlev (Jat N' h) N')
    (hMgrow : Filter.Tendsto
      (fun N' : {k // N₀ ≤ k} => Mlev (Jat N'.1 N'.2) N'.1 - M₀ (Jat N'.1 N'.2))
      Filter.atTop Filter.atTop)
    (hne : ∀ N' (h : N₀ ≤ N'), (stateTruncAt Jat N').Nonempty) :
    Filter.Tendsto
      (fun N' : {k // N₀ ≤ k} => (Nat.card ↥(nsTruncAt Jat Lat N'.1) : ℝ)
        / (Nat.card ↥(stateTruncAt Jat N'.1)))
      Filter.atTop (nhds 0) := by
  -- Per level (T-C5 at M = Mlev): the admissible cap-M lump locus, its lump shape,
  -- and the pin-count lower bound `Mlev − M₀ ≤ pinCount Z`.
  -- T-C5 (`nsZ_free`) instantiated at `M = Mlev`, per level.  LOCALIZED as a `have`
  -- rather than imported: the sibling unit `C5_nsFree` is a separate in-flight prover
  -- target (currently red); wire `nsZ_free (Jat N'.1 N'.2) (hzc N'.1 N'.2) …` here once
  -- it is green.  This `sorry` IS exactly T-C5's conclusion at `M = Mlev`.
  have nsZ_free' : ∀ N' : {k // N₀ ≤ k},
      ∃ Z : Locus p (n * N'.1),
        AdmissibleZ ((Jat N'.1 N'.2).Sigma H.nodes.length) Z ∧
          IsLumpLocus (Jat N'.1 N'.2) (Mlev (Jat N'.1 N'.2) N'.1) Z ∧
          Mlev (Jat N'.1 N'.2) N'.1 - M₀ (Jat N'.1 N'.2) ≤ pinCount Z := by
    intro N'
    sorry
  choose Z hZadm hZlump hZcnt using nsZ_free'
  -- The pin-count ladder tends to 0 (T-C4 with `lower := Mlev − M₀`, whose divergence
  -- is exactly `hMgrow`).
  have hlad : Filter.Tendsto
      (fun N' : {k // N₀ ≤ k} => (p : ℝ) ^ (-(pinCount (Z N') : ℤ)))
      Filter.atTop (nhds 0) :=
    ns_ladder (fun N' => pinCount (Z N'))
      (fun N' => Mlev (Jat N'.1 N'.2) N'.1 - M₀ (Jat N'.1 N'.2))
      (fun N' => hZcnt N') hMgrow
  refine squeeze_zero (fun N' => by positivity) (fun N' => ?_) hlad
  -- Fix the level; the ratio is bounded above by `p^(−pinCount Z)`.
  have hstate : stateTruncAt Jat N'.1
      = (Jat N'.1 N'.2).SHZ (topLocus p (n * N'.1)) := by
    simp only [stateTruncAt, dif_pos N'.2]
  have hns : nsTruncAt Jat Lat N'.1
      = stateTruncAt Jat N'.1 ∩ (Lat N'.1 N'.2).L (Mlev (Jat N'.1 N'.2) N'.1) := by
    simp only [nsTruncAt, dif_pos N'.2]
  -- THE FINITE→LOCUS BRIDGE (C5/C6-level content): the truncated lump event is the
  -- transported admissible locus `S(H, Z_M)`.  [Not among the cited C3–C6 conclusions;
  -- it is the Theta-transport of the digit-zero condition onto the terminal Z-system.]
  have hsub : nsTruncAt Jat Lat N'.1 ⊆ (Jat N'.1 N'.2).SHZ (Z N') := by
    sorry
  -- T-C6 prices the locus exactly: |S(H, Z)| · p^{pinCount Z} = |state|.
  have hprice : Nat.card ↥((Jat N'.1 N'.2).SHZ (Z N')) * p ^ pinCount (Z N')
      = Nat.card ↥(stateTruncAt Jat N'.1) := by
    rw [hstate]
    exact ns_price (Jat N'.1 N'.2) (Mlev (Jat N'.1 N'.2) N'.1) (hM₀ N'.1 N'.2)
      (Z N') (hZadm N') (hZlump N')
  -- Cardinal monotonicity along the bridge inclusion.
  have hbcard : Nat.card ↥(nsTruncAt Jat Lat N'.1)
      ≤ Nat.card ↥((Jat N'.1 N'.2).SHZ (Z N')) := by
    exact Set.ncard_le_ncard hsub (Set.toFinite ((Jat N'.1 N'.2).SHZ (Z N')))
  -- Denominator positive (realized states have members — `hne`).
  have hDpos : 0 < Nat.card ↥(stateTruncAt Jat N'.1) := by
    haveI : Nonempty ↥(stateTruncAt Jat N'.1) := (hne N'.1 N'.2).to_subtype
    exact Nat.card_pos
  set b := Nat.card ↥(nsTruncAt Jat Lat N'.1) with hb
  set a := Nat.card ↥((Jat N'.1 N'.2).SHZ (Z N')) with ha
  set D := Nat.card ↥(stateTruncAt Jat N'.1) with hD'
  set P := pinCount (Z N') with hP
  -- Recast the price as a real identity `D = a · p^P`.
  have hDR : (D : ℝ) = (a : ℝ) * (p : ℝ) ^ P := by
    rw [← hprice]; push_cast; ring
  have hDpos' : (0 : ℝ) < D := by exact_mod_cast hDpos
  have hp0 : (0 : ℝ) < (p : ℝ) := by
    have := (Fact.out : p.Prime).pos; exact_mod_cast this
  have hpPpos : (0 : ℝ) < (p : ℝ) ^ P := pow_pos hp0 P
  have hpPne : ((p : ℝ) ^ P) ≠ 0 := ne_of_gt hpPpos
  have ha0 : 0 < a := by
    rcases Nat.eq_zero_or_pos a with h | h
    · rw [h, zero_mul] at hprice; omega
    · exact h
  have haR : (0 : ℝ) < a := by exact_mod_cast ha0
  -- Assemble: b/D ≤ a/D = 1/p^P = p^{−P}.
  show (b : ℝ) / D ≤ (p : ℝ) ^ (-(P : ℤ))
  rw [zpow_neg, zpow_natCast, hDR, div_le_iff₀ (mul_pos haR hpPpos)]
  have hsimp : ((p : ℝ) ^ P)⁻¹ * ((a : ℝ) * (p : ℝ) ^ P) = (a : ℝ) := by
    rw [mul_comm ((p : ℝ) ^ P)⁻¹, mul_assoc, mul_inv_cancel₀ hpPne, mul_one]
  rw [hsimp]
  exact_mod_cast hbcard

end LeanUrat.MovesT
