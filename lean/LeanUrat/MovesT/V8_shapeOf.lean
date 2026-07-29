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
  obtain ⟨hnode, hrootdeg, hw0card, hslope, hgam, hae, hchain, hrootbox, hmoniclead⟩ := hlaw
  -- length of the shape's read list = number of nodes
  have hlenR : (shapeOfH H n).reads.length = H.nodes.length := by
    simp [shapeOfH]
  -- the read at index r is exactly `readOf` of the node at r (proof-term-generic)
  have hget : ∀ (r : ℕ) (hr : r < H.nodes.length) (hr' : r < (shapeOfH H n).reads.length),
      (shapeOfH H n).reads[r]'hr' = readOf (H.nodes[r]'hr) r n := by
    intro r hr hr'
    show ((List.range H.nodes.length).map
        (fun k => (H.nodes[k]?).elim default (fun ν => readOf ν k n)))[r]'hr' = _
    rw [List.getElem_map, List.getElem_range, List.getElem?_eq_getElem hr]
    rfl
  -- the residue-degree guard is dead: p ∣ card K, so its p-factorization is ≥ 1
  have hguard : ∀ (r : ℕ) (hr : r < H.nodes.length),
      (1 : ℕ) ≤ (Nat.card ↥(H.nodes[r]'hr).σ.K).factorization p := by
    intro r hr
    have hc := (hnode (H.nodes[r]'hr) (List.getElem_mem hr)).2.2.2
    have h2 : 1 < Nat.card ↥(H.nodes[r]'hr).σ.K := Finite.one_lt_card
    rw [hc] at h2
    rcases Nat.eq_zero_or_pos ((Nat.card ↥(H.nodes[r]'hr).σ.K).factorization p) with h0 | hpos
    · rw [h0, pow_zero] at h2; exact absurd h2 (lt_irrefl 1)
    · exact hpos
  -- the Dwidth guard is dead: root Φ-degree 1 + the width chain give Dwidth ≥ 1
  have hDwpos : ∀ (r : ℕ) (hr : r < H.nodes.length), 1 ≤ (H.nodes[r]'hr).Dwidth := by
    intro r
    induction r with
    | zero =>
      intro hr
      rw [(H.nodes[0]'hr).hDwidth, hrootdeg hr]
    | succ k ih =>
      intro hr
      have hk : k < H.nodes.length := by omega
      obtain ⟨_, hdw, _, _⟩ := hchain k hr
      rw [hdw]
      simp only [Node.childWidth]
      exact Nat.mul_pos (Nat.mul_pos (hnode (H.nodes[k]'hk) (List.getElem_mem hk)).1
        (hnode (H.nodes[k]'hk) (List.getElem_mem hk)).2.1) (ih hk)
  -- STR (frame stretch) is shape data: e-products over prefixes agree
  have hmape : ∀ i, (H.nodes.take i).map Node.e
      = ((shapeOfH H n).reads.take i).map ShapeRead.e := by
    intro i
    apply List.ext_getElem
    · simp [hlenR]
    · intro j hj1 _
      have hjn : j < H.nodes.length := by
        simp only [List.length_map, List.length_take] at hj1; omega
      simp only [List.getElem_map, List.getElem_take]
      rw [hget j hjn]
      rfl
  have hstr : ∀ i, H.strFrame i = (shapeOfH H n).strS i := by
    intro i
    show ((H.nodes.take i).map Node.e).prod
      = (((shapeOfH H n).reads.take i).map ShapeRead.e).prod
    rw [hmape i]
  constructor
  · -- MatchesHist
    refine ⟨hlenR.symm, ?_⟩
    intro r hr
    rw [hget r hr (hlenR.symm ▸ hr)]
    refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_, rfl, rfl, ?_, ?_⟩
    · -- Dwidth guard dead
      exact (max_eq_left (hDwpos r hr)).symm
    · -- pool card = p ^ w
      simp only [readOf]
      rw [max_eq_left (hguard r hr)]
      exact (hnode (H.nodes[r]'hr) (List.getElem_mem hr)).2.2.2
    · -- the monic-lead tie
      intro hmt
      simp only [readOf, decide_eq_true_eq] at hmt
      obtain ⟨hr00, hn, _⟩ := hmt
      simp only [readOf, ShapeRead.len]
      subst hr00
      exact hmoniclead hr hn
  · -- ShapeWF
    refine
      { species_iff := ?_
        root_box := ?_
        window := ?_
        gmu := ?_
        edvd := ?_
        dchain0 := ?_
        dchain := ?_
        monic := ?_
        w0 := ?_
        wchain := ?_
        gamTie := ?_
        anchorTie := ?_ }
    · -- species_iff
      intro r hr
      have hr0 : r < H.nodes.length := by rw [hlenR] at hr; exact hr
      rw [hget r hr0 hr]
      exact H.root_iff r hr0
    · -- root_box
      intro h0
      have h0' : 0 < H.nodes.length := by rw [hlenR] at h0; exact h0
      rw [hget 0 h0' h0]
      exact hrootbox h0'
    · -- window
      intro r hr
      have hr1 : r + 1 < H.nodes.length := by rw [hlenR] at hr; exact hr
      have hr0 : r < H.nodes.length := by omega
      rw [hget (r + 1) hr1 hr, hget r hr0 (by omega)]
      obtain ⟨hwin, _, _, _⟩ := hchain r hr1
      exact hwin
    · -- gmu
      intro r hr
      have hr0 : r < H.nodes.length := by rw [hlenR] at hr; exact hr
      rw [hget r hr0 hr]
      simp only [readOf, ShapeRead.len]
      obtain ⟨_, _, hgmu⟩ := hae r hr0
      exact hgmu
    · -- edvd
      intro r hr
      have hr0 : r < H.nodes.length := by rw [hlenR] at hr; exact hr
      rw [hget r hr0 hr]
      obtain ⟨_, hedvd, _⟩ := hae r hr0
      exact hedvd
    · -- dchain0
      intro h0
      have h0' : 0 < H.nodes.length := by rw [hlenR] at h0; exact h0
      rw [hget 0 h0' h0]
      simp only [readOf]
      rw [(H.nodes[0]'h0').hDwidth, hrootdeg h0']
      exact max_self 1
    · -- dchain
      intro r hr
      have hr1 : r + 1 < H.nodes.length := by rw [hlenR] at hr; exact hr
      have hr0 : r < H.nodes.length := by omega
      rw [hget (r + 1) hr1 hr, hget r hr0 (by omega)]
      simp only [readOf, ShapeRead.childWidthS]
      rw [max_eq_left (hDwpos (r + 1) hr1), max_eq_left (hDwpos r hr0)]
      obtain ⟨_, hdw, _, _⟩ := hchain r hr1
      rw [hdw]
      simp only [Node.childWidth]
    · -- monic (MonicTie)
      intro r hr
      have hr0 : r < H.nodes.length := by rw [hlenR] at hr; exact hr
      rw [hget r hr0 hr]
      simp only [readOf, decide_eq_true_eq]
      constructor
      · rintro ⟨hr00, hn, _⟩; exact ⟨hr00, hn⟩
      · rintro ⟨hr00, hn⟩
        exact ⟨hr00, hn, (H.root_iff r hr0).mpr hr00⟩
    · -- w0
      intro h0
      have h0' : 0 < H.nodes.length := by rw [hlenR] at h0; exact h0
      rw [hget 0 h0' h0]
      simp only [readOf]
      rw [max_eq_left (hguard 0 h0'), hw0card h0']
      exact Nat.Prime.factorization_self Fact.out
    · -- wchain
      intro r hr
      have hr1 : r + 1 < H.nodes.length := by rw [hlenR] at hr; exact hr
      have hr0 : r < H.nodes.length := by omega
      rw [hget (r + 1) hr1 hr, hget r hr0 (by omega)]
      simp only [readOf]
      rw [max_eq_left (hguard (r + 1) hr1), max_eq_left (hguard r hr0)]
      obtain ⟨_, _, _, hcard⟩ := hchain r hr1
      rw [hcard, Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul]
      exact Nat.mul_comm _ _
    · -- gamTie
      intro r hr
      have hr0 : r < H.nodes.length := by rw [hlenR] at hr; exact hr
      rw [hget r hr0 hr]
      simp only [readOf]
      rw [← hstr r]
      exact hgam r hr0
    · -- anchorTie
      intro r hr
      have hr0 : r < H.nodes.length := by rw [hlenR] at hr; exact hr
      rw [hget r hr0 hr]
      simp only [readOf]
      obtain ⟨hanch, _, _⟩ := hae r hr0
      exact hanch

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
  apply max_eq_left
  have hc := (hlaw.1 (H.nodes[i]'hi) (List.getElem_mem hi)).2.2.2
  have h2 : 1 < Nat.card ↥(H.nodes[i]'hi).σ.K := Finite.one_lt_card
  rw [hc] at h2
  rcases Nat.eq_zero_or_pos ((Nat.card ↥(H.nodes[i]'hi).σ.K).factorization p) with h0 | hpos
  · rw [h0, pow_zero] at h2; exact absurd h2 (lt_irrefl 1)
  · exact hpos

end LeanUrat.MovesT
