/-
Unit G1.gateBlock  (MovesD campaign, E-phase)  [ADDENDUM unit — not among the 48
blueprint ids; built per the E-phase charge: "the ∅ bridge (F3) and the gate block are
units too". Content = the blueprint's MANDATORY GATE CHECK (§0.6) + adversary block
(§3.1), restricted to what is STATABLE on shape data at E-phase.]
moves_ref: §0.6 (P̂* data, REV-6 subtype addendum: P̂* ∈ Shape 3; W = 7, M = 1,
Nshape = 5, A = 11, NPband = 5) + §3.1 (P̂₀ ∈ Shape 4, A(P̂₀) = 14 — Fable#6's unclaimed
cross-check; adversaries A-i/A-ii/A-vi — the BUILDABLE ones; A-iii/A-iv are unbuildable
records, excluded by `ShapeRead`'s own Prop fields, and need no statement).
NOTE: the classifier-side gate numbers (C_P̂*(2) = 3, C_P̂*(3) = 48, mult ≡ 1) are
class-count semantics over PrefSet — owned by the P-phase/menu wave, not statable as
closed shape arithmetic here.
deps: Defs.  difficulty: easy (decide/norm_num arithmetic at P-phase).
hypothesis_fields: none.
-/
import Mathlib
import LeanUrat.MovesD.Defs

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesD
open LeanUrat.Moves LeanUrat.MovesC

/-- P̂* read 0 (§D4-R.6): root, (e,h,g,μ,a) = (1,1,2,1,0), span [0,3], u*₀ = 0, γ₀ = 3,
w₀ = 1, monicTop = true (slot 3 = the monic lead). -/
def readStar0 : ShapeRead where
  species := ReadSpecies.root
  e := 1; h := 1; g := 2; μ := 1; a := 0
  s0 := 0; wSide := 3; Dwidth := 1
  ustar := 0; gam := 3; w := 1; monicTop := true
  he := by decide
  hg := by decide
  hμ := by decide
  hw := by decide
  hDw := by decide
  hh := by decide
  hcop := by decide
  hspecInc := by decide
  hspecRec := by decide
  hmonicRoot := by decide

/-- P̂* read 1 (§D4-R.6): recentering, (1,3,1,1,0), span [0,1], u*₁ = 1, γ₁ = 4, w₁ = 2,
monicTop = false. -/
def readStar1 : ShapeRead where
  species := ReadSpecies.recentering
  e := 1; h := 3; g := 1; μ := 1; a := 0
  s0 := 0; wSide := 1; Dwidth := 2
  ustar := 1; gam := 4; w := 2; monicTop := false
  he := by decide
  hg := by decide
  hμ := by decide
  hw := by decide
  hDw := by decide
  hh := by decide
  hcop := by decide
  hspecInc := by decide
  hspecRec := by decide
  hmonicRoot := by decide

/-- The sealed gate shape P̂* (§D4-R.6, n = 3). -/
def PhatStar : ShapePrefix := ⟨[readStar0, readStar1]⟩

/-- P̂₀ (§3.1, n = 4): root-only (1,1,1,2,0), full span, u* = 0, γ = 4, w = 1. -/
def read0Phat0 : ShapeRead where
  species := ReadSpecies.root
  e := 1; h := 1; g := 1; μ := 2; a := 0
  s0 := 0; wSide := 4; Dwidth := 1
  ustar := 0; gam := 4; w := 1; monicTop := true
  he := by decide
  hg := by decide
  hμ := by decide
  hw := by decide
  hDw := by decide
  hh := by decide
  hcop := by decide
  hspecInc := by decide
  hspecRec := by decide
  hmonicRoot := by decide

/-- The second positive gate shape P̂₀ (n = 4). -/
def Phat0 : ShapePrefix := ⟨[read0Phat0]⟩

/-- Adversary A-i (§3.1): root wSide = 10 against n = 3 (must fail `root_box`). -/
def advI : ShapeRead where
  species := ReadSpecies.root
  e := 1; h := 1; g := 1; μ := 1; a := 0
  s0 := 0; wSide := 10; Dwidth := 1
  ustar := 0; gam := 10; w := 1; monicTop := false
  he := by decide
  hg := by decide
  hμ := by decide
  hw := by decide
  hDw := by decide
  hh := by decide
  hcop := by decide
  hspecInc := by decide
  hspecRec := by decide
  hmonicRoot := by decide

/-- Adversary A-ii (§3.1): monicTop faker — s0 + wSide = 2 ≠ 3 (must fail `MonicTie`). -/
def advII : ShapeRead where
  species := ReadSpecies.root
  e := 1; h := 1; g := 1; μ := 1; a := 0
  s0 := 0; wSide := 2; Dwidth := 1
  ustar := 0; gam := 2; w := 1; monicTop := true
  he := by decide
  hg := by decide
  hμ := by decide
  hw := by decide
  hDw := by decide
  hh := by decide
  hcop := by decide
  hspecInc := by decide
  hspecRec := by decide
  hmonicRoot := by decide

/-- Adversary A-vi (§3.1, REV 8): root-only record with w = 2 (must fail `ShapeWF.w0`). -/
def advVI : ShapeRead where
  species := ReadSpecies.root
  e := 1; h := 1; g := 1; μ := 1; a := 0
  s0 := 0; wSide := 4; Dwidth := 1
  ustar := 0; gam := 4; w := 2; monicTop := true
  he := by decide
  hg := by decide
  hμ := by decide
  hw := by decide
  hDw := by decide
  hh := by decide
  hcop := by decide
  hspecInc := by decide
  hspecRec := by decide
  hmonicRoot := by decide

/-! ### The gate statements (P-phase: decide/norm_num against the definitions) -/

/-- GATE (positive): P̂* carries the certificate — P̂* ∈ Shape 3, clause by clause. -/
theorem PhatStar_wf : ShapeWF 3 PhatStar := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · decide
  · decide +revert
  · intro r hr
    have hr0 : r = 0 := by have hlen : PhatStar.reads.length = 2 := rfl; omega
    subst hr0
    decide +revert
  · decide
  · decide
  · decide +revert
  · intro r hr
    have hr0 : r = 0 := by have hlen : PhatStar.reads.length = 2 := rfl; omega
    subst hr0
    decide +revert
  · unfold ShapePrefix.MonicTie; decide
  · decide +revert
  · intro r hr
    have hr0 : r = 0 := by have hlen : PhatStar.reads.length = 2 := rfl; omega
    subst hr0
    decide +revert
  · intro r hr
    rw [show PhatStar.reads.length = 2 from rfl] at hr
    interval_cases r <;> norm_num [PhatStar, readStar0, readStar1, ShapePrefix.strS]
  · intro r hr
    rw [show PhatStar.reads.length = 2 from rfl] at hr
    interval_cases r <;> norm_num [PhatStar, readStar0, readStar1, bezT]

/-- GATE (positive): P̂₀ carries the certificate — P̂₀ ∈ Shape 4. -/
theorem Phat0_wf : ShapeWF 4 Phat0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · decide
  · decide +revert
  · intro r hr; exfalso; have hlen : Phat0.reads.length = 1 := rfl; omega
  · decide
  · decide
  · decide +revert
  · intro r hr; exfalso; have hlen : Phat0.reads.length = 1 := rfl; omega
  · unfold ShapePrefix.MonicTie; decide
  · decide +revert
  · intro r hr; exfalso; have hlen : Phat0.reads.length = 1 := rfl; omega
  · intro r hr
    rw [show Phat0.reads.length = 1 from rfl] at hr
    interval_cases r <;> norm_num [Phat0, read0Phat0, ShapePrefix.strS]
  · intro r hr
    rw [show Phat0.reads.length = 1 from rfl] at hr
    interval_cases r <;> norm_num [Phat0, read0Phat0, bezT]

/-- GATE: W(P̂*) = 1·3 + 2·2 = 7. -/
theorem PhatStar_W : PhatStar.W = 7 := by
  decide

/-- GATE: M(P̂*) = 1·1 = 1. -/
theorem PhatStar_Mfac : PhatStar.Mfac = 1 := by
  decide

/-- GATE: Nshape(P̂*) = 1 + max(⌈3⌉, ⌈4⌉) = 5. -/
theorem PhatStar_Nshape : PhatStar.Nshape = 5 := by
  norm_num [ShapePrefix.Nshape, ShapePrefix.lineS, ShapePrefix.strS, PhatStar, readStar0,
    readStar1, List.range_succ, List.range_zero]
  decide

/-- The `bandS` predicate for P̂*'s ROOT read, decidably characterized on the level grid
`[0,5) × [0,3)`: the fresh band is exactly `ℓ + i ≤ 3` (the root line `3 − i`). -/
private theorem PhatStar_bandS0_iff :
    ∀ c ∈ (Finset.range 5 ×ˢ Finset.range 3), PhatStar.bandS 3 0 c ↔ c.1 + c.2 ≤ 3 := by
  intro c hc
  simp only [Finset.mem_product, Finset.mem_range] at hc
  obtain ⟨ℓ, i⟩ := c
  obtain ⟨hℓ, hi⟩ := hc
  simp only at hℓ hi
  interval_cases i <;> interval_cases ℓ <;>
    simp only [PhatStar, ShapePrefix.bandS, ShapePrefix.prevRimS, ShapePrefix.floorS,
      ShapePrefix.htS, ShapePrefix.lineS, ShapePrefix.kappaS, ShapePrefix.innerslotS,
      ShapePrefix.strS, ShapeRead.childWidthS, readStar0, readStar1, Line.at, ShapeRead.staircaseS,
      List.range_zero, List.range_succ, List.foldr_nil, List.foldr_cons, List.map_nil,
      List.map_cons, Finset.range_zero, Finset.range_one, Finset.sum_empty, Finset.sum_range_one,
      List.getElem?_cons_zero, List.getElem?_cons_succ, Option.elim_some, List.take, List.prod_nil,
      List.prod_cons, WithBot.coe_lt_coe, WithBot.coe_le_coe, WithBot.bot_lt_coe] <;>
    norm_num

/-- The `bandS` predicate for P̂*'s recentering read, decidably characterized: the only
fresh-band coordinates are `(ℓ,i) = (4,0)` and `(3,1)`. -/
private theorem PhatStar_bandS1_iff :
    ∀ c ∈ (Finset.range 5 ×ˢ Finset.range 3), PhatStar.bandS 3 1 c ↔
      (c.2 = 0 ∧ c.1 = 4) ∨ (c.2 = 1 ∧ c.1 = 3) := by
  intro c hc
  simp only [Finset.mem_product, Finset.mem_range] at hc
  obtain ⟨ℓ, i⟩ := c
  obtain ⟨hℓ, hi⟩ := hc
  simp only at hℓ hi
  interval_cases i <;> interval_cases ℓ <;>
    simp only [PhatStar, ShapePrefix.bandS, ShapePrefix.prevRimS, ShapePrefix.floorS,
      ShapePrefix.htS, ShapePrefix.lineS, ShapePrefix.kappaS, ShapePrefix.innerslotS,
      ShapePrefix.strS, ShapeRead.childWidthS, readStar0, readStar1, Line.at, ShapeRead.staircaseS,
      List.range_zero, List.range_succ, List.foldr_nil, List.foldr_cons, List.map_nil,
      List.map_cons, Finset.range_zero, Finset.range_one, Finset.sum_empty, Finset.sum_range_one,
      List.getElem?_cons_zero, List.getElem?_cons_succ, Option.elim_some, List.take, List.prod_nil,
      List.prod_cons, WithBot.coe_lt_coe, WithBot.coe_le_coe, WithBot.bot_lt_coe] <;>
    norm_num <;> norm_cast

/-- GATE: A(P̂*) = 9 + 2 = 11 (at n = 3, N = Nshape = 5). -/
theorem PhatStar_A' : PhatStar.A' 3 = 11 := by
  classical
  have key0 : (Finset.range 5 ×ˢ Finset.range 3).filter (fun c => PhatStar.bandS 3 0 c)
            = (Finset.range 5 ×ˢ Finset.range 3).filter (fun c => c.1 + c.2 ≤ 3) :=
    Finset.filter_congr PhatStar_bandS0_iff
  have key1 : (Finset.range 5 ×ˢ Finset.range 3).filter (fun c => PhatStar.bandS 3 1 c)
            = (Finset.range 5 ×ˢ Finset.range 3).filter
                (fun c => (c.2 = 0 ∧ c.1 = 4) ∨ (c.2 = 1 ∧ c.1 = 3)) :=
    Finset.filter_congr PhatStar_bandS1_iff
  unfold ShapePrefix.A'
  rw [PhatStar_Nshape]
  unfold ShapePrefix.A
  rw [show PhatStar.reads.length = 2 from rfl]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.zero_add]
  rw [key0, key1]
  decide

/-- GATE: NPband(P̂*) = 1 + 4 = 5 (the inhabited-branch NP value — the note's own
"N(P̂*) = 1 + (largest pinned base level = 4, at c₀) = 5"). -/
theorem PhatStar_NPband : PhatStar.NPband 3 = 5 := by
  classical
  have hpred : ∀ c ∈ (Finset.range 5 ×ˢ Finset.range 3),
      (∃ r < PhatStar.reads.length, PhatStar.bandS 3 r c) ↔
        (c.1 + c.2 ≤ 3) ∨ ((c.2 = 0 ∧ c.1 = 4) ∨ (c.2 = 1 ∧ c.1 = 3)) := by
    intro c hc
    constructor
    · rintro ⟨r, hr, hb⟩
      rw [show PhatStar.reads.length = 2 from rfl] at hr
      interval_cases r
      · exact Or.inl ((PhatStar_bandS0_iff c hc).mp hb)
      · exact Or.inr ((PhatStar_bandS1_iff c hc).mp hb)
    · rintro (h | h)
      · exact ⟨0, by decide, (PhatStar_bandS0_iff c hc).mpr h⟩
      · exact ⟨1, by decide, (PhatStar_bandS1_iff c hc).mpr h⟩
  have keyNP : (Finset.range 5 ×ˢ Finset.range 3).filter
        (fun c => ∃ r < PhatStar.reads.length, PhatStar.bandS 3 r c)
      = (Finset.range 5 ×ˢ Finset.range 3).filter
        (fun c => (c.1 + c.2 ≤ 3) ∨ ((c.2 = 0 ∧ c.1 = 4) ∨ (c.2 = 1 ∧ c.1 = 3))) :=
    Finset.filter_congr hpred
  unfold ShapePrefix.NPband
  rw [PhatStar_Nshape, keyNP]
  decide

/-- Nshape(P̂₀) = 1 + ⌈4⌉ = 5. -/
private theorem Phat0_Nshape : Phat0.Nshape = 5 := by
  norm_num [ShapePrefix.Nshape, ShapePrefix.lineS, ShapePrefix.strS, Phat0, read0Phat0,
    List.range_succ, List.range_zero]
  decide

/-- The `bandS` predicate for P̂₀'s single root read (n = 4): the band is `ℓ + i ≤ 4`. -/
private theorem Phat0_bandS0_iff :
    ∀ c ∈ (Finset.range 5 ×ˢ Finset.range 4), Phat0.bandS 4 0 c ↔ c.1 + c.2 ≤ 4 := by
  intro c hc
  simp only [Finset.mem_product, Finset.mem_range] at hc
  obtain ⟨ℓ, i⟩ := c
  obtain ⟨hℓ, hi⟩ := hc
  simp only at hℓ hi
  interval_cases i <;> interval_cases ℓ <;>
    simp only [Phat0, ShapePrefix.bandS, ShapePrefix.prevRimS, ShapePrefix.floorS,
      ShapePrefix.htS, ShapePrefix.lineS, ShapePrefix.kappaS, ShapePrefix.innerslotS,
      ShapePrefix.strS, ShapeRead.childWidthS, read0Phat0, Line.at, ShapeRead.staircaseS,
      List.range_zero, List.range_succ, List.foldr_nil, List.foldr_cons, List.map_nil,
      List.map_cons, Finset.range_zero, Finset.range_one, Finset.sum_empty, Finset.sum_range_one,
      List.getElem?_cons_zero, List.getElem?_cons_succ, Option.elim_some, List.take, List.prod_nil,
      List.prod_cons, WithBot.coe_lt_coe, WithBot.coe_le_coe, WithBot.bot_lt_coe] <;>
    norm_num

/-- GATE: A(P̂₀) = 14 (Fable#6's unclaimed cross-check against the note). -/
theorem Phat0_A' : Phat0.A' 4 = 14 := by
  classical
  have key0 : (Finset.range 5 ×ˢ Finset.range 4).filter (fun c => Phat0.bandS 4 0 c)
            = (Finset.range 5 ×ˢ Finset.range 4).filter (fun c => c.1 + c.2 ≤ 4) :=
    Finset.filter_congr Phat0_bandS0_iff
  unfold ShapePrefix.A'
  rw [Phat0_Nshape]
  unfold ShapePrefix.A
  rw [show Phat0.reads.length = 1 from rfl]
  simp only [Finset.sum_range_one]
  rw [key0]
  decide

/-- ADVERSARY A-i: fails `root_box` at n = 3. -/
theorem advI_not_wf : ¬ ShapeWF 3 ⟨[advI]⟩ := by
  intro h
  have h1 := h.root_box (by decide)
  revert h1; decide

/-- ADVERSARY A-ii: fails `MonicTie` at n = 3. -/
theorem advII_not_wf : ¬ ShapeWF 3 ⟨[advII]⟩ := by
  intro h
  have h1 := h.monic 0 (by decide)
  revert h1; decide

/-- ADVERSARY A-vi: fails `w0` at n = 4. -/
theorem advVI_not_wf : ¬ ShapeWF 4 ⟨[advVI]⟩ := by
  intro h
  have h1 := h.w0 (by decide)
  revert h1; decide

end LeanUrat.MovesD
