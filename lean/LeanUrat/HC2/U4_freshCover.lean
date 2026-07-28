/-
Unit U4.mkFresh_cover  (HC-2 campaign, E-phase — blueprint §5 Layer A)
moves_ref: MovesC `fresh_cover` docstring ("every band coordinate lies in SOME clause's
support — EXACTLY one, by disj").
deps: D6, U2.  difficulty: easy-medium.  hypothesis_fields: none.
sketch: dichotomy on `IsValueCoord c`: value → c is in its slot's level set = that value
clause's support; non-value → its strip clause exists by D6's strip roster.

*** OBSTRUCTION (P-phase, 2026-07-27; dual-confirmed by Codex gpt-5.6-sol, fresh context) ***
U4 IS NOT PROVABLE AS STATED — `hypothesis_fields: none` is insufficient; the value case is
FALSE on a legal countermodel.  The strip case and ALL list/clause plumbing DO close (proved
below); the entire theorem reduces to the single leftover goal at the `sorry`:
    the value slot `j := ν.fineSlot (boxChart n N c).2` lies in `valueSlots H n N i ν`,
whose defining filter (`Defs.lean` `valueSlots`, lines ~328-332) carries the ROSTER clause
    `∀ c' ∈ levelSet H n N i ν j, inFreshBand H n (boxChart n N) i ν c'`
— the ENTIRE height-level set of slot `j` must be in-band.  U4 hands us this for ONE member
(`c`) only.  `levelSet j` (`Defs.lean` ~310-313) collects EVERY box coordinate at fine slot
`j` and height `ν.slotVal j`, with NO band filter; `inFreshBand` (MovesC `Defs.lean` ~750-754)
imposes the per-BASE-INDEX conditions `(boxChart c').2 < H.prevRim n i` and
`H.floorH i (boxChart c').2 < ν.slotVal j`.  `H.floorH` reads ONLY the `Node.line`/`staircase`
data of the EARLIER nodes (r < i); `ν.slotVal`/`H.htH` read node-i's line and the level/kappa
data.  In U4 (no `HistoryCoherent`, no `Realizable`) the Node structure constraints are all
PER-NODE and never cross-link node-i's line to the earlier nodes' lines, so `floorH` is
adversarially FREE relative to `slotVal`/`htH`, and it varies across the base indices of a
single fine slot (staircase blocks have width `childWidth_r`, unrelated to node-i's `Dwidth`).
Hence `levelSet j` can STRADDLE the floor-crossing: an in-band `c` and an out-of-band sibling
`c'` at the same fine slot and same height `slotVal j`.  Then `j ∉ valueSlots`, its value
clause is absent, and `c` (a value coord, so excluded from every strip) is UNCOVERED.
Countermodel skeleton (Codex, with `h ≥ 1` repair): `n=N=2`, `i=1`, nodes `[ρ, ν]`, `ρ`
supplies a `line` with `floorH 1 0 = 0` but `floorH 1 1 = 2`; `ν` has `Dwidth=2` so bases 0,1
share fine slot 0 with `slotVal 0 = 1`; coords `(1,0)` and `(1,1)` are both in `levelSet 0`
at height 1, yet only `(1,0)` is in-band.  (Root case `i=0` is clean: `floorH 0 = ⊥`,
`prevRim n 0 = n`, so every level-set member is in-band — the straddle needs `i ≥ 1`.)
ROOT CAUSE: the blueprint's U3/U4 sketch treats `levelSet` as ALREADY band-restricted ("value
slots past the (γ) crossing have empty level sets IN THE BAND"), but the E-phase Defs made
`levelSet` the FULL level set with a separate roster in `valueSlots`; the two co-satisfy U3
(band) + U5 (IsValueSupport = full level set) but make U4 (cover) unsatisfiable on straddling
slots.  FIX (statement/Defs-fence — needs human SIGN-OFF, NOT applied here): either (i) add
`HistoryCoherent`+`Realizable` to U4 AND supply the genuine geometric no-straddle lemma (the
SAE strict span-entry keeps node-i's line strictly above the floor across span slots — this is
hard-core content), or (ii) redesign `levelSet`/`IsValueSupport`/`valueSlots` to be band-aware
(intersect the level set with the band), which then also touches U3/U5/U6.

*** N-6 SIGN-OFF EXECUTED (2026-07-28 — §9 F-7's ruling: OPTION (i), the RECOMMENDED
route; option (ii) rejected as non-minimal — it re-opens proved U3/U5/U6 + Defs). ***
`mkFresh_cover` GAINS `hcoh : HistoryCoherent H` + `hreal : Realizable H`; the roster
goal is discharged by the NEW named geometric lemma `levelSet_no_straddle` (below,
sorried — the (SAE)/C.1.5 line-dominance content, the U10 wave's family; QUEUED for the
fleet). U4's own theorem body is now complete modulo that named lemma; the countermodel
above is closed by hypothesis (its adversarial `floorH` needs an incoherent H).
Consumer update: U13 threads `hcoh hreal` (it holds both).
-/
import Mathlib
import LeanUrat.HC2.Defs

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesJ
open Polynomial LeanUrat.Moves LeanUrat.MovesC LeanUrat.MovesD

/-- THE GEOMETRIC NO-STRADDLE LEMMA (N-6 option (i), 2026-07-28): under coherence +
realizability, a span slot's exact-valuation level set cannot STRADDLE the floor — if
one member is in-band, every member is. Content: the (SAE) strict span-entry / C.1.5
line-dominance keeps node-i's line strictly above the accumulated floor across the whole
window, so the per-base floor variation of the earlier staircases cannot cross a level
set sitting AT `slotVal j` (the U10 wave's family; the root case i = 0 is clean —
`floorH 0 = ⊥`). QUEUED-FLEET; the U4 countermodel's adversarial `floorH` is
coherence-infeasible. -/
theorem levelSet_no_straddle {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
    (H : History p F) (n N : ℕ)
    (hcoh : HistoryCoherent H) (hreal : Realizable H)
    (i : ℕ) (hi : i < H.nodes.length) (j : ℕ) (c c' : Fin (n * N))
    (hc : c ∈ levelSet H n N i (H.nodes[i]'hi) j)
    (hband : inFreshBand H n (boxChart n N) i (H.nodes[i]'hi) c)
    (hc' : c' ∈ levelSet H n N i (H.nodes[i]'hi) j) :
    inFreshBand H n (boxChart n N) i (H.nodes[i]'hi) c' := by
  sorry

/-- Every band coordinate is covered by some constructed clause's support (verbatim
`JetSetup.fresh_cover`'s field type at `mkFresh`; N-6 RESTATEMENT: under
coherence + realizability — the sign-off's option (i)). -/
theorem mkFresh_cover {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
    (H : History p F) (n N : ℕ) {keys : ℕ → Polynomial ℤ_[p]}
    (S : PresentSeed p F H n N keys) (vOf : VOf p (n * N))
    (hcoh : HistoryCoherent H) (hreal : Realizable H)
    (i : ℕ) (hi : i < H.nodes.length) :
    ∀ c : Fin (n * N), inFreshBand H n (boxChart n N) i (H.nodes[i]'hi) c →
      ∃ cl ∈ (mkFresh H n N S vOf i hi).clauses, c ∈ cl.support := by
  classical
  set ν := H.nodes[i]'hi with hν
  intro c hband
  by_cases hv : IsValueCoord H (boxChart n N) i ν c
  · -- VALUE case: c sits in its slot's level set = a value clause's support
    set j := ν.fineSlot ((boxChart n N c).2) with hj
    have hspan : ν.spanSlot j := hv.1
    have hht : H.htH i (boxChart n N c) = ν.slotVal j := hv.2
    -- c belongs to slot j's level set
    have hc_level : c ∈ levelSet H n N i ν j := by
      unfold levelSet
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ c, rfl, hht⟩
    -- slot j is rostered as a value slot
    have hj_val : j ∈ valueSlots H n N i ν := by
      unfold valueSlots
      rw [Finset.mem_filter, Finset.mem_range]
      refine ⟨?_, hspan, ⟨c, hc_level⟩, ?_⟩
      · have := hspan.2; omega
      · -- ROSTER: the WHOLE level set of slot `j` is in-band — the N-6 no-straddle
        -- lemma fired at the in-band member `c` (the former dual-confirmed obstruction,
        -- closed by the option-(i) hypothesis addition; see the header record).
        intro c' hc'
        exact levelSet_no_straddle H n N hcoh hreal i hi j c c' hc_level hband hc'
    -- the value clause at slot j
    set vcl := valueClause H n N S vOf i hi j (valueSlots_spanSlot hj_val) with hvcl
    have hcard : Nat.card (Fin (levelSet H n N i ν j).card → ZMod p)
        = p ^ (levelSet H n N i ν j).card := by
      haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
      simp [Nat.card_eq_fintype_card, ZMod.card]
    have hsupp : vcl.support = levelSet H n N i ν j := by
      rw [hvcl]
      unfold valueClause
      exact (C1_TYP_toClause _ _ (levelSet H n N i ν j).card hcard).choose_spec.1
    refine ⟨vcl, ?_, ?_⟩
    · -- vcl is in the value part of the clause list
      show vcl ∈ mkFreshClauses H n N S vOf i hi
      unfold mkFreshClauses
      rw [List.mem_append]
      right
      rw [List.mem_map]
      exact ⟨⟨j, hj_val⟩, by rw [Finset.mem_toList]; exact Finset.mem_attach _ _, rfl⟩
    · rw [hsupp]; exact hc_level
  · -- STRIP case: c is a non-value band coordinate, covered by its strip clause
    have hc_strip : c ∈ stripSet H n N i ν := by
      unfold stripSet
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ c, hband, hv⟩
    set cl := (C1_stripClause (p := p) c).choose with hcl
    have hspec := (C1_stripClause (p := p) c).choose_spec
    refine ⟨cl, ?_, ?_⟩
    · show cl ∈ mkFreshClauses H n N S vOf i hi
      unfold mkFreshClauses
      rw [List.mem_append]
      left
      rw [List.mem_map]
      exact ⟨c, by rw [Finset.mem_toList]; exact hc_strip, rfl⟩
    · rw [hspec.1]; exact Finset.mem_singleton_self c

end LeanUrat.MovesJ
