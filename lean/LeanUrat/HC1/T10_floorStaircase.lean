/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.HC1.DefsCar
import LeanUrat.MovesC.C2_DOM_floorForm
import LeanUrat.Moves.L3_liftMonic

/-!
# HC1.T10_floorStaircase — on factor-interior blocks the coordinate STEP floor is the
block staircase

moves_ref: MOVES 3743–3745 (LST(ii)) + 3650–3651 (DOM: "the floor is the current
staircase: F_i(b) = old_i(slot(b))"). deps: T3, C4 (DOM_real), MovesC
`C2_DOM_floorForm` (proved). The first conjunct (`floorB b = (lines K).at
(blockEdge b)`) is DEFINITIONAL (rfl-level; the F3-3 repair by construction).
difficulty: medium. hyp: `TowerRealizable` (the realizability chain (SAE)/(NA)/(HV)
of the tower's moves — §5's open kernel, carried as `rl`).

**F-1 RESTATEMENT (sign-off event 2026-07-28, blueprint §9.1):** conjunct 2 was
MACHINE-REFUTED on the raw-line pointwise floor `floorC`
(`ScratchT10.T10_conjunct2_refuted`, retained: on any realizable tower, any
factor-interior block, any coordinate with a nonzero sub-top slot,
`floorC c < floorB b` STRICTLY — slope-K > 0 is forced by `slope_law` + κ
positivity, and `Line.at` descends across the block). The note's floor is old_i
evaluated at the SLOT of b — a STEP function constant on each current block
(MovesC's own `Node.lineStep`/`History.floorH` convention). Conjunct 2 is RESTATED
on the F-1 step floor `floorS` (DefsCar); `floorC` stays for the DOM-side
consumers; conjunct 1 and the hypotheses are unchanged. PROOF ROUTE (blueprint
§9.1, checked on the refutation kernel's own lemmas): the m = K summand of the sup'
is exactly `floorB b` (frame-K quantization of `baseIdx c = OFF + blockEdge b` with
`OFF < deg Φ_top` returns `blockEdge b`); for m < K the frame-m edge is ≥ the
frame-K edge (nested radices `frameWidth (m+1) ∣ frameWidth (K+1)`), `Line.at`
decreasing gives `lineStep m ≤ (rl.line m).at (blockEdge b)`, and DOM
(`C2_DOM_floorForm.dom_le` at `blockEdge b ≤ interiorEnd`) caps it by `floorB b`.
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

namespace LeanUrat.HC1

open Polynomial LeanUrat.Moves

variable {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]

/-! ### Reproduced numeric kernel (from `ScratchT10`, minus the refutation). -/

private lemma t10_strAux_pos (T : Tower p F) : ∀ n, 0 < T.strAux n := by
  intro n
  induction n with
  | zero => simp [Tower.strAux]
  | succ k ih =>
    unfold Tower.strAux
    split
    · exact Nat.mul_pos ih (T.stg _).he
    · simpa using Nat.mul_pos ih Nat.one_pos

private lemma t10_frameWidth_pos (T : Tower p F) (k : ℕ) : 0 < T.frameWidth k := by
  cases k with
  | zero => simp [Tower.frameWidth]
  | succ m =>
    show 0 < if h : m < T.K + 1 then (T.stg ⟨m, h⟩).Φ.natDegree else 1
    by_cases h : m < T.K + 1
    · rw [dif_pos h]; exact (T.stg _).hdeg
    · rw [dif_neg h]; exact Nat.one_pos

private lemma t10_kappa_pos (T : Tower p F) (k : Fin (T.K + 1)) : 0 < T.kappa k := by
  unfold Tower.kappa
  apply div_pos
  · exact_mod_cast (T.stg k).hh
  · exact mul_pos (by exact_mod_cast (T.stg k).he) (by exact_mod_cast t10_strAux_pos T k.val)

/-- every recorded read-line has strictly positive slope (slope_law + κ/frameWidth
positivity) — `Line.at` descends everywhere, at every read. -/
private lemma t10_slope_pos (T : Tower p F) (rl : TowerRealizable T) (m : ℕ)
    (hm : m < T.K + 1) : 0 < (rl.line m).slope := by
  have hlaw := rl.slope_law ⟨m, hm⟩
  have hk : 0 < T.kappa ⟨m, hm⟩ := t10_kappa_pos T _
  have hfw : (0 : ℚ) < (T.frameWidth m : ℚ) := by exact_mod_cast t10_frameWidth_pos T m
  rw [← hlaw] at hk
  rcases mul_pos_iff.mp hk with ⟨h, _⟩ | ⟨_, h⟩
  · exact h
  · exact absurd hfw (not_lt.mpr h.le)

private lemma t10_baseIdx_decomp (T : Tower p F) (c : T.Coord) :
    T.baseIdx c = (∑ r : Fin T.K, c.slot r.castSucc * (T.stg r.castSucc).Φ.natDegree)
      + T.blockEdge (T.blk c) := by
  unfold Tower.baseIdx Tower.blockEdge Tower.blk Tower.topStage
  rw [Fin.sum_univ_castSucc]

private lemma t10_offset_lt (T : Tower p F) (c : T.Coord) :
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

/-! ### The nested-radix divisibility chain (reproduced from T4's private lemmas). -/

/-- Degree divisibility per move: `deg Φ_m ∣ deg Φ_{m+1}` (increment: `deg Φ̂ = e·g·deg Φ`
via `L3_liftMonic`; recentering: degree unchanged since `deg t < deg Φ`). -/
private lemma t10_deg_dvd_step (T : Tower p F) (m : ℕ) (hm : m < T.K) :
    (T.stg ⟨m, Nat.lt_succ_of_lt hm⟩).Φ.natDegree ∣ (T.stg ⟨m + 1, Nat.succ_lt_succ hm⟩).Φ.natDegree := by
  set k : Fin T.K := ⟨m, hm⟩ with hk
  show (T.stg k.castSucc).Φ.natDegree ∣ (T.stg k.succ).Φ.natDegree
  cases T.move k with
  | inc ψ g Φhat e' h' zbar hyp core _ =>
    have hkey := core.base.child_key
    have hdeg := (L3_liftMonic (T.stg k.castSucc) ψ g hyp.hg Φhat hyp.hlift).2
    rw [hkey, hdeg]
    exact ⟨(T.stg k.castSucc).e * g, by ring⟩
  | recenter cc tt core _ =>
    obtain ⟨_, _, _, htt, _, _, _, hΦ', _, _, _, _, _, _⟩ := core.base
    rw [hΦ']
    have hne1 : (T.stg k.castSucc).Φ - tt ≠ 0 := by rw [← hΦ']; exact (T.stg k.succ).hmonic.ne_zero
    have hne2 : (T.stg k.castSucc).Φ ≠ 0 := (T.stg k.castSucc).hmonic.ne_zero
    have hdegeq : ((T.stg k.castSucc).Φ - tt).degree = (T.stg k.castSucc).Φ.degree :=
      Polynomial.degree_sub_eq_left_of_degree_lt htt
    have hnd : ((T.stg k.castSucc).Φ - tt).natDegree = (T.stg k.castSucc).Φ.natDegree := by
      rw [Polynomial.degree_eq_natDegree hne1, Polynomial.degree_eq_natDegree hne2] at hdegeq
      exact_mod_cast hdegeq
    rw [hnd]

/-- Transitive divisibility: `deg Φ_a ∣ deg Φ_b` for `a ≤ b ≤ K`. -/
private lemma t10_deg_dvd_le (T : Tower p F) (a : ℕ) :
    ∀ (b : ℕ) (hab : a ≤ b) (hbK : b < T.K + 1),
      (T.stg ⟨a, by omega⟩).Φ.natDegree ∣ (T.stg ⟨b, hbK⟩).Φ.natDegree := by
  intro b hab
  induction b, hab using Nat.le_induction with
  | base => intro _; exact dvd_refl _
  | succ n hn ih =>
    intro hbK
    have hnK : n < T.K + 1 := by omega
    have hnlt : n < T.K := by omega
    exact (ih hnK).trans (t10_deg_dvd_step T n hnlt)

/-- If `w ∣ X` and `X ≤ N`, then `X` is at most the frame-`w` edge below `N`. -/
private lemma t10_edge_ge {w X N : ℕ} (hwX : w ∣ X) (hXN : X ≤ N) : X ≤ (N / w) * w := by
  conv_lhs => rw [← Nat.div_mul_cancel hwX]
  gcongr

/-! ### The unit. -/

/-- Unit T10: the staircase equation (rfl-level) + THE CONTENT (F-1 restated): on
factor-interior blocks the history STEP floor at every block coordinate equals the
block staircase value. -/
theorem T10_floorStaircase {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
    (T : Tower p F) (rl : TowerRealizable T) (b : ℕ) (hb : rl.interiorB b) :
    rl.floorB b = (rl.line T.K).at (T.blockEdge b) ∧
    (∀ c : T.Coord, T.blk c = b → rl.floorS c = rl.floorB b) := by
  refine ⟨rfl, ?_⟩
  intro c hc
  -- abbreviations
  have hdtoppos : 0 < (T.topStage).Φ.natDegree := (T.topStage).hdeg
  have hblock : T.blockEdge b = b * (T.topStage).Φ.natDegree := rfl
  -- the mixed-radix decomposition of the coordinate's base index
  have hdec : T.baseIdx c
      = (∑ r : Fin T.K, c.slot r.castSucc * (T.stg r.castSucc).Φ.natDegree) + T.blockEdge b := by
    rw [t10_baseIdx_decomp, hc]
  have hOFFlt : (∑ r : Fin T.K, c.slot r.castSucc * (T.stg r.castSucc).Φ.natDegree)
      < (T.topStage).Φ.natDegree := t10_offset_lt T c
  have hbaseform : T.baseIdx c
      = (∑ r : Fin T.K, c.slot r.castSucc * (T.stg r.castSucc).Φ.natDegree)
        + b * (T.topStage).Φ.natDegree := by rw [hdec, hblock]
  -- frame-K width is the top degree
  have hfwK : T.frameWidth (T.K + 1) = (T.topStage).Φ.natDegree := by
    show (if h : T.K < T.K + 1 then (T.stg ⟨T.K, h⟩).Φ.natDegree else 1) = (T.topStage).Φ.natDegree
    rw [dif_pos (Nat.lt_succ_self T.K)]
    rfl
  -- frame-K quantization returns the block edge
  have hdiv : T.baseIdx c / (T.topStage).Φ.natDegree = b := by
    rw [hbaseform, Nat.add_mul_div_right _ b hdtoppos, Nat.div_eq_of_lt hOFFlt, Nat.zero_add]
  have hedgeK : (T.baseIdx c / T.frameWidth (T.K + 1)) * T.frameWidth (T.K + 1) = T.blockEdge b := by
    rw [hfwK, hdiv, hblock]
  have hstepK : rl.lineStep T.K (T.baseIdx c) = rl.floorB b := by
    unfold TowerRealizable.lineStep TowerRealizable.floorB
    rw [hedgeK]
  -- the block edge sits inside the factor interior
  have hble : T.blockEdge b ≤ T.baseIdx c := by
    rw [hbaseform, hblock]; exact Nat.le_add_left _ _
  have hbint : T.blockEdge b ≤ rl.interiorEnd T.K := by
    have hlt : T.blockEdge b < T.blockEdge (b + 1) := by
      unfold Tower.blockEdge; nlinarith [hdtoppos]
    exact le_trans hlt.le hb
  -- DOM data of the top read on the factor interior
  have hdom : MovesC.DomData rl.line T.K (rl.interiorEnd T.K) :=
    ⟨fun m hm => rl.steeper (Fin.last T.K) m hm,
     fun m hm => rl.vertex_entry (Fin.last T.K) m hm⟩
  -- the per-summand upper bound: every step term is capped by the block staircase
  have hmbound : ∀ m ∈ Finset.range (T.K + 1), rl.lineStep m (T.baseIdx c) ≤ rl.floorB b := by
    intro m hmem
    have hm : m < T.K + 1 := Finset.mem_range.mp hmem
    have hmK : m ≤ T.K := Nat.lt_succ_iff.mp hm
    -- frame-m width = deg Φ_m
    have hfwm : T.frameWidth (m + 1) = (T.stg ⟨m, hm⟩).Φ.natDegree := by
      show (if h : m < T.K + 1 then (T.stg ⟨m, h⟩).Φ.natDegree else 1) = (T.stg ⟨m, hm⟩).Φ.natDegree
      rw [dif_pos hm]
    -- frame-m width divides the top degree (nested radices)
    have hwdvd : (T.stg ⟨m, hm⟩).Φ.natDegree ∣ (T.topStage).Φ.natDegree :=
      t10_deg_dvd_le T m T.K hmK (Nat.lt_succ_self _)
    -- the frame-m edge dominates the block edge
    have hedge : T.blockEdge b ≤ (T.baseIdx c / T.frameWidth (m + 1)) * T.frameWidth (m + 1) := by
      rw [hfwm]
      refine t10_edge_ge ?_ hble
      rw [hblock]; exact hwdvd.mul_left b
    -- line-m descends: value at the edge ≤ value at the block edge
    have hslopem : 0 < (rl.line m).slope := t10_slope_pos T rl m hm
    have hdescent : (rl.line m).at ((T.baseIdx c / T.frameWidth (m + 1)) * T.frameWidth (m + 1))
        ≤ (rl.line m).at (T.blockEdge b) := by
      simp only [MovesC.Line.at]
      have hq : ((T.blockEdge b : ℕ) : ℚ)
          ≤ (((T.baseIdx c / T.frameWidth (m + 1)) * T.frameWidth (m + 1) : ℕ) : ℚ) := by
        exact_mod_cast hedge
      linarith [mul_le_mul_of_nonneg_left hq (le_of_lt hslopem)]
    -- DOM caps line-m at the block edge by the top read = floorB
    have hcap : (rl.line m).at (T.blockEdge b) ≤ rl.floorB b := by
      have hfloorForm := MovesC.C2_DOM_floorForm hdom (T.blockEdge b) hbint
      have hle : (rl.line m).at (T.blockEdge b) ≤ MovesC.floorOf rl.line T.K (T.blockEdge b) := by
        unfold MovesC.floorOf
        exact Finset.le_sup' (fun m' => (rl.line m').at (T.blockEdge b)) hmem
      rw [hfloorForm] at hle
      exact hle
    calc rl.lineStep m (T.baseIdx c)
        = (rl.line m).at ((T.baseIdx c / T.frameWidth (m + 1)) * T.frameWidth (m + 1)) := rfl
      _ ≤ (rl.line m).at (T.blockEdge b) := hdescent
      _ ≤ rl.floorB b := hcap
  -- assemble the sup' as an antisymmetric sandwich
  apply le_antisymm
  · unfold TowerRealizable.floorS
    apply Finset.sup'_le
    exact hmbound
  · rw [← hstepK]
    unfold TowerRealizable.floorS
    exact Finset.le_sup' (fun m => rl.lineStep m (T.baseIdx c)) (Finset.self_mem_range_succ T.K)

end LeanUrat.HC1

#print axioms LeanUrat.HC1.T10_floorStaircase
