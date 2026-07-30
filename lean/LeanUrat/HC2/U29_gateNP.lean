/-
Unit U29.gate_NP  (HC-2 campaign, E-phase — blueprint §5 Layer E)
moves_ref: the MovesD gate instance: for the worked shape P̂* (MovesD §3.3's gate row /
G1_gates `PhatStar`), the CONSTRUCTED system's largest equation level + 1 = 5 = Shape.NP
(the note's own derivation "NP(P̂*) = 1 + 4 = 5") — U14's arithmetic at one census-pinned
instance.  deps: U14, MovesD.G1_gates (`PhatStar`, `PhatStar_NPband` PROVED).
difficulty: easy-medium.  hypothesis_fields: none.
RESTATED-POST-DEFS-REPAIR (2026-07-27): statement stands on the REPAIRED ZCSeedLaws.downsets_literal (chart-coverage guard added; box-truncation refuted by scratch_U9_presentSeed_false — blueprint §2.2 DC-1). Now sorry-free and Lean-core as-built (the fleet round completed; stale sorry-note corrected 2026-07-30).
-/
import Mathlib
import LeanUrat.HC2.Defs
import LeanUrat.MovesD.G1_gates
import LeanUrat.MovesD.D8_bandShape

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesJ
open Polynomial LeanUrat.Moves LeanUrat.MovesC LeanUrat.MovesD

/-- The gate shape as a certified `Shape 3` (`PhatStar` + its well-formedness certificate). -/
def Pstar : Shape 3 := ⟨PhatStar, PhatStar_wf⟩

/-! ### Shape-side line values of P̂* (finite `norm_num`/`decide` computations). -/

/-- P̂*'s root line evaluates to 3 at 0 (its intercept). -/
private lemma lineS0_at0 : (PhatStar.lineS 0).at 0 = 3 := by
  norm_num [ShapePrefix.lineS, ShapePrefix.strS, PhatStar, readStar0, readStar1, Line.at, List.take]

/-- P̂*'s recentering line evaluates to 4 at 0 (its intercept — the note's "largest pinned
base level = 4"). -/
private lemma lineS1_at0 : (PhatStar.lineS 1).at 0 = 4 := by
  norm_num [ShapePrefix.lineS, ShapePrefix.strS, PhatStar, readStar0, readStar1, Line.at, List.take]

/-- The K1-chain height of the band point `(4,0)` at read 1 is 4. -/
private lemma htS1_40 : PhatStar.htS 1 (4, 0) = 4 := by
  norm_num [ShapePrefix.htS, ShapePrefix.innerslotS, ShapePrefix.kappaS, PhatStar, readStar0,
    readStar1, ShapeRead.childWidthS, Finset.sum_range_one]

/-- The shape floor at read 1 is the root line's value `3` on the whole `prevRim` block
`b < 2` (the root staircase's single block). -/
private lemma floorS1_lt2 (b : ℕ) (hb : b < 2) :
    PhatStar.floorS 1 b = (((PhatStar.lineS 0).at 0 : ℚ) : WithBot ℚ) := by
  have hb0 : b / 2 = 0 := Nat.div_eq_of_lt hb
  simp only [ShapePrefix.floorS, PhatStar, List.range_one, List.map_cons, List.map_nil,
    List.foldr_cons, List.foldr_nil, List.getElem?_cons_zero, Option.elim_some,
    ShapeRead.staircaseS, ShapeRead.childWidthS, readStar0]
  norm_num [hb0]
  omega

/-- **The shape roster fact (no straddle for P̂*)**: any coordinate at read 1 whose base index
sits in the rim block (`< 2`) and whose K1-height equals the recentering line's value at 0
is in P̂*'s fresh band.  This is exactly what breaks the general `mkFresh_cover` (U4), but
holds here because P̂*'s slot-0 level set (`{(4,0),(3,1)}`) lies wholly in the band. -/
private lemma shape_roster (c' : Coord) (hb : c'.2 < 2)
    (hht : PhatStar.htS 1 c' = (PhatStar.lineS 1).at 0) : PhatStar.bandS 3 1 c' := by
  refine ⟨?_, ?_, ?_⟩
  · -- base index below the rim threshold `prevRimS 3 1 = 2`
    show c'.2 < PhatStar.prevRimS 3 1
    have hpr : PhatStar.prevRimS 3 1 = 2 := by rfl
    omega
  · -- strictly above the floor: floor = 3 < 4 = height
    rw [hht, floorS1_lt2 c'.2 hb, WithBot.coe_lt_coe, lineS0_at0, lineS1_at0]
    norm_num
  · -- at or below the fine-slot valuation (equality here)
    change PhatStar.htS 1 c' ≤ (PhatStar.lineS 1).at ((c'.2 / readStar1.Dwidth) * readStar1.Dwidth)
    rw [hht]
    have hz : (c'.2 / readStar1.Dwidth) * readStar1.Dwidth = 0 := by
      have hb0 : c'.2 / 2 = 0 := Nat.div_eq_of_lt hb
      simp [readStar1, hb0]
    rw [hz]

/-! ### The band transfer for P̂* (verbatim `D8.band_shape`, specialized to `boxChart 3 5`). -/

/-- The fresh band of a P̂*-matched coherent history is the shape band, coordinate for
coordinate (the three `inFreshBand` conjuncts transferred through D6d/D6e/D7b/D7c). -/
private lemma band_transfer {F : Type*} [Field F] [Finite F] {H : History 2 F}
    (hm : PhatStar.MatchesHist H) (hcoh : HistoryCoherent H)
    (r : ℕ) (hr : r < H.nodes.length) (c : Fin 15) :
    inFreshBand H 3 (boxChart 3 5) r (H.nodes[r]'hr) c ↔ PhatStar.bandS 3 r (boxChart 3 5 c) := by
  have hr' : r < (Pstar : ShapePrefix).reads.length := by
    obtain ⟨hlen, _⟩ := hm; rw [hlen] at hr; exact hr
  change inFreshBand H 3 (boxChart 3 5) r (H.nodes[r]'hr) c
      ↔ (Pstar : ShapePrefix).bandS 3 r (boxChart 3 5 c)
  unfold inFreshBand ShapePrefix.bandS
  rw [htH_shape (P := Pstar) hm r (boxChart 3 5 c),
    floorH_shape (P := Pstar) hcoh hm r (boxChart 3 5 c).2,
    prevRim_shape (P := Pstar) hm r,
    slotVal_shape (P := Pstar) hcoh hm r hr hr' (boxChart 3 5 c).2,
    List.getElem?_eq_getElem hr']
  simp only [Option.elim_some]

/-- Extract `support = S` from a `C1_TYP_toClause`-shaped existential (cf. U3). -/
private lemma choose_support_eq {p m : ℕ} {S : Finset (Fin m)} {P : LevelClause p m → Prop}
    (h : ∃ cl : LevelClause p m, cl.support = S ∧ P cl) : h.choose.support = S :=
  h.choose_spec.1

/-! ### The unit theorems. -/

/-- The census-pinned NPband value (re-export of MovesD's PROVED gate: NP(P̂*) = 5). -/
theorem gate_NP_value : PhatStar.NPband 3 = 5 := PhatStar_NPband

/-- GATE: at N = 5 = NPband(P̂*), every constructed fresh support coordinate of a matched
coherent history fits below level 5 (U14's bound at the instance).  As stated with the box
height pinned at `N = 5`, this is immediate: every chart coordinate lands with level `< N`. -/
theorem gate_NP_fits {F : Type*} [Field F] [Finite F] {H : History 2 F}
    (hm : PhatStar.MatchesHist H) (hcoh : HistoryCoherent H) (hreal : Realizable H)
    (hbox : InBox 3 H) {keys : ℕ → Polynomial ℤ_[2]}
    (S : PresentSeed 2 F H 3 5 keys) (vOf : VOf 2 (3 * 5)) :
    ∀ (i : ℕ) (hi : i < H.nodes.length), ∀ cl ∈ (mkFresh H 3 5 S vOf i hi).clauses,
      ∀ c ∈ cl.support, (boxChart 3 5 c).1 + 1 ≤ 5 := by
  intro i hi cl hcl c hc
  have h := (boxChart_lt 3 5 c).1
  omega

/-- GATE (attainment): the bound is EXACT — some constructed equation coordinate sits at
level 4 (the note's "largest pinned base level = 4, at c₀"; shape-side, the band point
(4,0) of `PhatStar_bandS1_iff`).  Witness: the value clause at recentering slot 0, whose
support (the slot-0 level set `{(4,0),(3,1)}`) is rostered because it lies wholly in the
band — the straddle that defeats the general cover (U4) does not occur for P̂*. -/
theorem gate_NP_attained {F : Type*} [Field F] [Finite F] {H : History 2 F}
    (hm : PhatStar.MatchesHist H) (hcoh : HistoryCoherent H) (hreal : Realizable H)
    (hbox : InBox 3 H) {keys : ℕ → Polynomial ℤ_[2]}
    (S : PresentSeed 2 F H 3 5 keys) (vOf : VOf 2 (3 * 5)) :
    ∃ (i : ℕ) (hi : i < H.nodes.length),
      ∃ cl ∈ (mkFresh H 3 5 S vOf i hi).clauses,
        ∃ c ∈ cl.support, (boxChart 3 5 c).1 = 4 := by
  classical
  -- The matched history has exactly the two reads of P̂*.
  have hi : (1 : ℕ) < H.nodes.length := by
    obtain ⟨hlen, -⟩ := hm; rw [hlen]; decide
  set ν := H.nodes[1]'hi with hνdef
  -- Node-1 window data from the shape match.
  have hDw : ν.Dwidth = 2 := by
    obtain ⟨hlen, hmatch⟩ := hm
    obtain ⟨-, -, -, -, -, -, -, -, hDw', -, -, -, -⟩ := hmatch 1 hi
    exact hDw'
  have hs0 : ν.s0 = 0 := by
    obtain ⟨hlen, hmatch⟩ := hm
    obtain ⟨-, -, -, -, -, -, hs0', -, -, -, -, -, -⟩ := hmatch 1 hi
    exact hs0'
  -- Read 1's line at fine slot 0 is the recentering intercept (= 4).
  have hr' : (1 : ℕ) < (Pstar : ShapePrefix).reads.length := by decide
  have hsv0 : ν.slotVal 0 = (PhatStar.lineS 1).at 0 := by
    have hsl := slotVal_shape (P := Pstar) hcoh hm 1 hi hr' 0
    have hfs0 : ν.fineSlot 0 = 0 := by simp [Node.fineSlot]
    rw [hfs0] at hsl
    have hz : (0 / ((Pstar : ShapePrefix).reads[1]'hr').Dwidth)
        * ((Pstar : ShapePrefix).reads[1]'hr').Dwidth = 0 := by simp
    rw [hz] at hsl
    exact hsl
  -- The witness coordinate 14 ↦ (4,0), level 4.
  set c₀ : Fin (3 * 5) := ⟨14, by norm_num⟩ with hc₀def
  have hbc : boxChart 3 5 c₀ = (4, 0) := by decide
  -- `c₀` lies in slot 0's level set.
  have hc₀level : c₀ ∈ levelSet H 3 5 1 ν 0 := by
    simp only [levelSet, Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨?_, ?_⟩
    · rw [hbc]; simp [Node.fineSlot]
    · rw [hbc, hsv0]
      have hht : PhatStar.htS 1 (4, 0) = H.htH 1 (4, 0) :=
        (htH_shape (P := Pstar) hm 1 (4, 0)).symm
      rw [← hht, htS1_40, lineS1_at0]
  -- Slot 0 is a span slot.
  have hspan0 : ν.spanSlot 0 := ⟨le_of_eq hs0, Nat.zero_le _⟩
  -- Slot 0 is rostered (the whole level set is in-band — no straddle).
  have hj0 : (0 : ℕ) ∈ valueSlots H 3 5 1 ν := by
    simp only [valueSlots, Finset.mem_filter, Finset.mem_range]
    refine ⟨by have := hspan0.2; omega, hspan0, ⟨c₀, hc₀level⟩, ?_⟩
    -- ROSTER: every slot-0 level-set member is in-band.
    intro c hc
    simp only [levelSet, Finset.mem_filter, Finset.mem_univ, true_and] at hc
    obtain ⟨hfs, hht⟩ := hc
    rw [band_transfer hm hcoh 1 hi c]
    apply shape_roster
    · -- base index < 2 from `fineSlot = 0` and `Dwidth = 2`
      simp only [Node.fineSlot, hDw] at hfs
      omega
    · -- height = recentering intercept
      have hshp : PhatStar.htS 1 (boxChart 3 5 c) = H.htH 1 (boxChart 3 5 c) :=
        (htH_shape (P := Pstar) hm 1 (boxChart 3 5 c)).symm
      rw [hshp, hht, hsv0]
  -- The value clause at slot 0, its membership, and its support.
  set vcl := valueClause H 3 5 S vOf 1 hi 0 (valueSlots_spanSlot hj0) with hvcl
  refine ⟨1, hi, vcl, ?_, c₀, ?_, ?_⟩
  · -- vcl is in the value part of the clause list
    change vcl ∈ mkFreshClauses H 3 5 S vOf 1 hi
    unfold mkFreshClauses
    rw [List.mem_append]
    right
    rw [List.mem_map]
    exact ⟨⟨0, hj0⟩, by rw [Finset.mem_toList]; exact Finset.mem_attach _ _, rfl⟩
  · -- c₀ ∈ vcl.support = levelSet
    have hsupp : vcl.support = levelSet H 3 5 1 ν 0 := by
      rw [hvcl]; unfold valueClause; exact choose_support_eq _
    rw [hsupp]; exact hc₀level
  · -- (boxChart 3 5 c₀).1 = 4
    rw [hbc]

end LeanUrat.MovesJ
