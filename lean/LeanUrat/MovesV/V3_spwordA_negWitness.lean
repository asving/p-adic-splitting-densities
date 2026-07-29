/-
Unit V3-3a-NEG — the COMPILED NEGATION WITNESS for `spWord_exists` as stated
(MovesV wave-4 prover fleet, 2026-07-29; the `U1_negWitness` durability pattern).

WHAT IS REFUTED. V3-3a states
  `spWord_exists (n) (P) (hWF : MovesD.ShapeWF n P) : ∃ ws, SpWordFits n P ws`.
This is FALSE at the build target n = 3 — THE WIDTH-1 CONTINUATION HOLE:
`SpFitsRead` pins EVERY letter's selection `s.sel = some (R.g, R.μ)` (a ShapeRead
carries g, μ ≥ 1 by type), while `SpWordFits` demands catalogue membership and a
`SuccStep` chain; the stage law forces the SECOND letter's window `W = μ₀`, and
`Coherent`'s (G6) terminal rule (`sel = none ↔ W = 1`) then FORBIDS a selection
on any letter whose inherited window is 1.  `ShapeWF` nowhere excludes a read
FOLLOWING a μ = 1 read (its `window` clause allows `s0' + wSide' ≤ μ = 1`), so the
two-read WF prefix [root(e=1, s0=0, wSide=1, g=1, μ=1); recentering(same)] is a
shape with NO fitting species word.  (At n = 1 even the SINGLE-read WF prefix
already fails: RootStage forces W = n = 1, and (G6) + Budget's W ≤ n kill every
selection-bearing letter.)  The missing law is a width-≥-2 continuation clause —
either in `ShapeWF` (a read after a μ = 1 read is not a shape) or in
`SpFitsRead`'s selection clause; both are statement-level repairs (sign-off).

* `SpWordNeg.P3` — the two-read WF prefix at n = 3.
* `SpWordNeg.hWF3` — its machine-checked `ShapeWF 3` certificate.
* `SpWordNeg.spWordFits_impossible` — NO ws fits it.
* `SpWordNeg.spWord_exists_false` — the ∀-sentence of V3-3a is FALSE.

deps: MovesV Defs (`SpWordFits`), MovesD Defs (`ShapeWF`), MovesSp Defs
(`SuccStep`/`StageLaws`/`Coherent`).  axioms: Lean core only.
-/
import LeanUrat.MovesV.Defs

set_option linter.style.longLine false
set_option linter.style.header false

namespace LeanUrat.MovesV
namespace SpWordNeg

/-- the root read: e = 1, h = 1, g = 1, μ = 1, s0 = 0, wSide = 1 (so μ = 1 is a
LEGAL selection: g·μ = 1 ≤ len = 1), w = 1, Dwidth = 1; γ-tie at u* = 0, h = 1. -/
def R0 : MovesD.ShapeRead :=
  { species := .root, e := 1, h := 1, g := 1, μ := 1, a := 0, s0 := 0,
    wSide := 1, Dwidth := 1, ustar := 0, gam := 1, w := 1, monicTop := false,
    he := le_refl 1, hg := le_refl 1, hμ := le_refl 1, hw := le_refl 1,
    hDw := le_refl 1, hh := le_refl 1, hcop := rfl,
    hspecInc := fun h => (nomatch h),
    hspecRec := fun h => (nomatch h),
    hmonicRoot := fun h => (nomatch h) }

/-- the follow-up read inside the width-1 window (recentering: e = g = 1). -/
def R1 : MovesD.ShapeRead :=
  { species := .recentering, e := 1, h := 1, g := 1, μ := 1, a := 0, s0 := 0,
    wSide := 1, Dwidth := 1, ustar := 0, gam := 1, w := 1, monicTop := false,
    he := le_refl 1, hg := le_refl 1, hμ := le_refl 1, hw := le_refl 1,
    hDw := le_refl 1, hh := le_refl 1, hcop := rfl,
    hspecInc := fun h => (nomatch h),
    hspecRec := fun _ => ⟨rfl, rfl⟩,
    hmonicRoot := fun h => (nomatch h) }

/-- THE WITNESS PREFIX: root then a read in its width-1 window. -/
def P3 : MovesD.ShapePrefix := ⟨[R0, R1]⟩

/-- the length of the witness prefix, by rfl (the r+1-bounded clauses' omega seed). -/
theorem P3_len : P3.reads.length = 2 := rfl

/-- the machine-checked WF certificate at n = 3 (kernel evaluation over the
two-read literal; the r+1-bounded clauses split to r = 0 first). -/
theorem hWF3 : MovesD.ShapeWF 3 P3 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · decide  -- species_iff
  · decide  -- root_box
  · -- window
    intro r hr
    have hr0 : r = 0 := by have := P3_len; omega
    subst hr0
    simp only [P3, List.getElem_cons_zero, List.getElem_cons_succ]
    decide
  · decide  -- gmu
  · decide  -- edvd
  · decide  -- dchain0
  · -- dchain
    intro r hr
    have hr0 : r = 0 := by have := P3_len; omega
    subst hr0
    simp only [P3, List.getElem_cons_zero, List.getElem_cons_succ]
    decide
  · -- monic
    unfold MovesD.ShapePrefix.MonicTie
    decide
  · decide  -- w0
  · -- wchain
    intro r hr
    have hr0 : r = 0 := by have := P3_len; omega
    subst hr0
    simp only [P3, List.getElem_cons_zero, List.getElem_cons_succ]
    decide
  · -- gamTie
    intro r hr
    have hr2 : r < 2 := by have := P3_len; omega
    interval_cases r <;>
      norm_num [P3, R0, R1, MovesD.ShapePrefix.strS]
  · -- anchorTie (bezT 1 h = 0 via x % 1 = 0 — no xgcd evaluation needed)
    intro r hr
    have hr2 : r < 2 := by have := P3_len; omega
    interval_cases r <;>
      · simp only [P3, List.getElem_cons_zero, List.getElem_cons_succ]
        norm_num [R0, R1, MovesD.bezT, Int.emod_one]

/-- NO species word fits `P3`: the second letter inherits window W = μ₀ = 1
(`StageLaws` through the chain), so (G6) forces `sel = none`, while
`SpFitsRead` pins `sel = some (1, 1)`. -/
theorem spWordFits_impossible : ¬ ∃ ws, SpWordFits 3 P3 ws := by
  rintro ⟨ws, hlen, hfit, _hmem, hchain⟩
  have hlen2 : ws.length = 2 := by simpa [P3] using hlen
  obtain ⟨a, b, rfl⟩ := List.length_eq_two.mp hlen2
  -- the two per-index fit clauses
  have hfit0 := hfit 0 (by norm_num) (by simp [P3])
  have hfit1 := hfit 1 (by norm_num) (by simp [P3])
  have hsel0 : a.sel = some (1, 1) := by
    have h := hfit0.2.2.2.2.1
    simpa [P3, R0] using h
  have hsel1 : b.sel = some (1, 1) := by
    have h := hfit1.2.2.2.2.1
    simpa [P3, R1] using h
  -- the chain step: SuccStep a b
  have hsucc : MovesSp.SuccStep 3 a b := List.rel_of_isChain_cons_cons hchain
  -- StageLaws forces b.W = μ₀ = 1
  have hstage := hsucc.1
  unfold MovesSp.StageLaws at hstage
  rw [hsel0] at hstage
  have hW : b.W = 1 := hstage.2.2.1
  -- Coherent b's (G6) terminal rule then forces b.sel = none
  have hcoh : MovesSp.Coherent b := hsucc.2.1
  have hnone : b.sel = none := hcoh.2.2.2.2.2.mpr hW
  rw [hsel1] at hnone
  simp at hnone

/-- THE REFUTATION: V3-3a's ∀-sentence is FALSE (at the build target n = 3). -/
theorem spWord_exists_false :
    ¬ ∀ (n : ℕ) (P : MovesD.ShapePrefix), MovesD.ShapeWF n P →
        ∃ ws, SpWordFits n P ws := by
  intro h
  exact spWordFits_impossible (h 3 P3 hWF3)

end SpWordNeg
end LeanUrat.MovesV
