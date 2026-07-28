/-
ScratchT10 — REFUTATION SCHEMA for T10_floorStaircase conjunct 2 (escalation artifact).

Machine-checked: on ANY realizable tower, ANY factor-interior block b, ANY coordinate
c of block b carrying a nonzero sub-top slot, the pointwise history floor is STRICTLY
below the block staircase: `floorC c < floorB b`. Hence the T10 statement
`∀ c, blk c = b → floorC c = floorB b` is provable only if every tower admitting a
TowerRealizable has all slotBounds = 1 (no degree jumps) — false for any genuine
increment (S1's g = 2 gate spec). NOT part of the blueprint; delete freely.
-/
import Mathlib
import LeanUrat.HC1.DefsCar
import LeanUrat.MovesC.C2_DOM_floorForm

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

namespace LeanUrat.HC1

open Polynomial LeanUrat.Moves

variable {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]

private lemma strAux_pos (T : Tower p F) : ∀ n, 0 < T.strAux n := by
  intro n
  induction n with
  | zero => simp [Tower.strAux]
  | succ k ih =>
    unfold Tower.strAux
    split
    · exact Nat.mul_pos ih (T.stg _).he
    · simpa using Nat.mul_pos ih Nat.one_pos

private lemma frameWidth_pos (T : Tower p F) (k : ℕ) : 0 < T.frameWidth k := by
  cases k with
  | zero => simp [Tower.frameWidth]
  | succ m =>
    show 0 < if h : m < T.K + 1 then (T.stg ⟨m, h⟩).Φ.natDegree else 1
    by_cases h : m < T.K + 1
    · rw [dif_pos h]; exact (T.stg _).hdeg
    · rw [dif_neg h]; exact Nat.one_pos

private lemma kappa_pos (T : Tower p F) (k : Fin (T.K + 1)) : 0 < T.kappa k := by
  unfold Tower.kappa
  apply div_pos
  · exact_mod_cast (T.stg k).hh
  · exact mul_pos (by exact_mod_cast (T.stg k).he) (by exact_mod_cast strAux_pos T k.val)

/-- slope_K > 0 is FORCED on every realizable tower (slope_law + hh/he/hdeg). -/
private lemma slopeK_pos (T : Tower p F) (rl : TowerRealizable T) :
    0 < (rl.line T.K).slope := by
  have hlaw := rl.slope_law (Fin.last T.K)
  rw [Fin.val_last] at hlaw
  have hk : 0 < T.kappa (Fin.last T.K) := kappa_pos T _
  have hfw : (0 : ℚ) < (T.frameWidth T.K : ℚ) := by exact_mod_cast frameWidth_pos T T.K
  rw [← hlaw] at hk
  rcases mul_pos_iff.mp hk with ⟨h, _⟩ | ⟨_, h⟩
  · exact h
  · exact absurd hfw (not_lt.mpr h.le)

/-- the mixed-radix decomposition: baseIdx = sub-top OFFSET + blockEdge(blk c). -/
private lemma baseIdx_decomp (T : Tower p F) (c : T.Coord) :
    T.baseIdx c = (∑ r : Fin T.K, c.slot r.castSucc * (T.stg r.castSucc).Φ.natDegree)
      + T.blockEdge (T.blk c) := by
  unfold Tower.baseIdx Tower.blockEdge Tower.blk Tower.topStage
  rw [Fin.sum_univ_castSucc]

/-- the OFFSET stays strictly inside one top block (telescoped slot_lt bounds). -/
private lemma offset_lt (T : Tower p F) (c : T.Coord) :
    (∑ r : Fin T.K, c.slot r.castSucc * (T.stg r.castSucc).Φ.natDegree)
      < (T.topStage).Φ.natDegree := by
  set d : ℕ → ℕ := fun i => if h : i < T.K + 1 then (T.stg ⟨i, h⟩).Φ.natDegree else 0 with hd
  set s : ℕ → ℕ := fun i => if h : i < T.K then
    c.slot (Fin.castSucc ⟨i, h⟩) * (T.stg (Fin.castSucc ⟨i, h⟩)).Φ.natDegree else 0 with hs
  have hstep : ∀ i, i < T.K → s i + d i ≤ d (i + 1) := by
    intro i hi
    have hi1 : i < T.K + 1 := Nat.lt_succ_of_lt hi
    have hi2 : i + 1 < T.K + 1 := Nat.succ_lt_succ hi
    have hcs : (Fin.castSucc (⟨i, hi⟩ : Fin T.K)) = (⟨i, hi1⟩ : Fin (T.K + 1)) := rfl
    have hsc : ((⟨i, hi⟩ : Fin T.K)).succ = (⟨i + 1, hi2⟩ : Fin (T.K + 1)) := rfl
    have hslt := c.slot_lt ⟨i, hi⟩
    unfold Tower.slotBound at hslt
    rw [hcs, hsc] at hslt
    simp only [hs, hd, dif_pos hi, dif_pos hi1, dif_pos hi2, hcs]
    calc c.slot ⟨i, hi1⟩ * (T.stg ⟨i, hi1⟩).Φ.natDegree + (T.stg ⟨i, hi1⟩).Φ.natDegree
        = (c.slot ⟨i, hi1⟩ + 1) * (T.stg ⟨i, hi1⟩).Φ.natDegree := by ring
      _ ≤ ((T.stg ⟨i + 1, hi2⟩).Φ.natDegree / (T.stg ⟨i, hi1⟩).Φ.natDegree)
            * (T.stg ⟨i, hi1⟩).Φ.natDegree :=
          Nat.mul_le_mul_right _ (Nat.succ_le_of_lt hslt)
      _ ≤ (T.stg ⟨i + 1, hi2⟩).Φ.natDegree := Nat.div_mul_le_self _ _
  have hind : ∀ n, n ≤ T.K → (∑ i ∈ Finset.range n, s i) + d 0 ≤ d n := by
    intro n
    induction n with
    | zero => simp
    | succ m ih =>
      intro hm
      have hmK : m < T.K := Nat.lt_of_succ_le hm
      rw [Finset.sum_range_succ]
      calc (∑ i ∈ Finset.range m, s i) + s m + d 0
          = ((∑ i ∈ Finset.range m, s i) + d 0) + s m := by ring
        _ ≤ d m + s m := Nat.add_le_add_right (ih hmK.le) _
        _ = s m + d m := Nat.add_comm _ _
        _ ≤ d (m + 1) := hstep m hmK
  have hsum : (∑ r : Fin T.K, c.slot r.castSucc * (T.stg r.castSucc).Φ.natDegree)
      = ∑ i ∈ Finset.range T.K, s i := by
    rw [← Fin.sum_univ_eq_sum_range]
    exact Finset.sum_congr rfl fun r _ => by
      simp only [hs]
      rw [dif_pos r.isLt]
  have hd0 : 1 ≤ d 0 := by simp only [hd, dif_pos (Nat.succ_pos T.K)]; exact (T.stg _).hdeg
  have hdK : d T.K = (T.topStage).Φ.natDegree := by
    simp only [hd, dif_pos (Nat.lt_succ_self T.K)]; rfl
  have := hind T.K le_rfl
  omega

/-- **THE REFUTATION SCHEMA**: any block coordinate with a nonzero sub-top slot sits
STRICTLY below the block staircase — T10's conjunct 2 fails at every such c. -/
theorem T10_conjunct2_refuted (T : Tower p F) (rl : TowerRealizable T)
    (b : ℕ) (hb : rl.interiorB b) (c : T.Coord) (hc : T.blk c = b)
    (r0 : Fin T.K) (hr0 : 0 < c.slot r0.castSucc) :
    rl.floorC c < rl.floorB b := by
  set OFF := ∑ r : Fin T.K, c.slot r.castSucc * (T.stg r.castSucc).Φ.natDegree with hOFF
  have hdec : T.baseIdx c = OFF + T.blockEdge b := by rw [baseIdx_decomp, hc]
  have hOFFpos : 0 < OFF := by
    have h1 : c.slot r0.castSucc * (T.stg r0.castSucc).Φ.natDegree
        ≤ ∑ r : Fin T.K, c.slot r.castSucc * (T.stg r.castSucc).Φ.natDegree :=
      Finset.single_le_sum
        (f := fun r : Fin T.K => c.slot r.castSucc * (T.stg r.castSucc).Φ.natDegree)
        (fun i _ => Nat.zero_le _) (Finset.mem_univ r0)
    rw [← hOFF] at h1
    exact lt_of_lt_of_le (Nat.mul_pos hr0 (T.stg _).hdeg) h1
  have hOFFlt : OFF < (T.topStage).Φ.natDegree := offset_lt T c
  -- interiority of the coordinate's base index
  have hin : T.baseIdx c ≤ rl.interiorEnd T.K := by
    have hEdge : T.blockEdge (b + 1) = T.blockEdge b + (T.topStage).Φ.natDegree := by
      unfold Tower.blockEdge; ring
    have hlt : T.baseIdx c < T.blockEdge (b + 1) := by
      rw [hdec, hEdge, Nat.add_comm (T.blockEdge b)]
      exact Nat.add_lt_add_right hOFFlt _
    exact le_trans hlt.le hb
  -- DOM floor form at the fine index
  have dom : MovesC.DomData rl.line T.K (rl.interiorEnd T.K) :=
    ⟨fun m hm => rl.steeper (Fin.last T.K) m hm,
     fun m hm => rl.vertex_entry (Fin.last T.K) m hm⟩
  have hfloor : rl.floorC c = (rl.line T.K).at (T.baseIdx c) :=
    MovesC.C2_DOM_floorForm dom _ hin
  -- strict descent by slope_K · OFF > 0
  have hsl : 0 < (rl.line T.K).slope := slopeK_pos T rl
  rw [hfloor]
  show (rl.line T.K).at (T.baseIdx c) < (rl.line T.K).at (T.blockEdge b)
  simp only [MovesC.Line.at]
  have hcast : ((T.baseIdx c : ℚ)) = (OFF : ℚ) + (T.blockEdge b : ℚ) := by
    exact_mod_cast congrArg (Nat.cast : ℕ → ℚ) hdec
  rw [hcast]
  have hOFFq : (0 : ℚ) < (OFF : ℚ) := by exact_mod_cast hOFFpos
  nlinarith [mul_pos hsl hOFFq]

/-- conjunct 1 of T10 is definitional (recorded). -/
example (T : Tower p F) (rl : TowerRealizable T) (b : ℕ) :
    rl.floorB b = (rl.line T.K).at (T.blockEdge b) := rfl

end LeanUrat.HC1

#print axioms LeanUrat.HC1.T10_conjunct2_refuted
