/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapE.E05
import Uniformity.ChapE.E08

/-!
# Uniformity.ChapE.E68 — the five-frame threshold regression (Q3's table as `decide`s)

**Chapter E, NODE E.68** [gate] [fresh] (`blueprint/CHAP-E_sigma_ladder.md` §10, the executable
gates; the node carries amendment A-E.1's defect **E-D7**, transcribed in full below). ENV-E1.
The file signs four gate-local ladders as `def`s (the frames that ARE legal rungs) and executes
everything else as `example`s over E.02/E.05/E.08.

## The table

`EFF.HE7.23`'s TEETH table, verbatim: the bound recursion evaluated at the five Q3 frames
`(e₁, f₁, h, ℓ, d_r, u)`, against the spec's recorded thresholds

| frame | `(e₁, f₁, h, ℓ, d_r, u)` | `bound₁ = (e₁f₁ − 1)h` | `bound₂ = (ℓd_r − 1)u + ℓ·bound₁` |
| ----- | ------------------------ | ---------------------- | --------------------------------- |
| 1 | `(2,1,1,2,1,5)`  | `1` | `(2−1)·5 + 2·1 = 7`  |
| 2 | `(2,1,1,2,2,5)`  | `1` | `(4−1)·5 + 2·1 = 17` |
| 3 | `(2,2,1,2,2,7)`  | `3` | `(4−1)·7 + 2·3 = 27` |
| 4 | `(3,1,2,2,3,13)` | `4` | `(6−1)·13 + 2·4 = 73` |
| 5 | `(1,2,1,3,2,11)` | `1` | `(6−1)·11 + 3·1 = 58` |

**All five recomputations match the spec's table exactly** (`7, 17, 27, 73, 58`). Each is fired
twice: on `RungDatum.nextBound` (E.02's one-step recursion) and — for the four frames that build
a genuine ladder — through `LadderData.boundAt` (E.05's iterated form), which is the shape a
consumer reads.

## ⚠ FRAME 3 IS NOT A LEGAL RUNG AT ITS CORPUS THRESHOLD — the row is SPLIT IN TWO

*[repaired: A-E.1/E-D7]*. Frame 3 `(2,2,1,2,2,7)` has `D′h = e₁f₁h = 4`, so its level-2 rung
would carry `T₂ = 4` — and E.01's node condition `hnode : ℓ * T < u` then reads `2·4 = 8 < 7`,
which is FALSE (machine-checked below). In corpus letters `λ = u/ℓ = 3.5 ≤ D′h = 4` violates
DEFINITION HE7-1's `λ > D′h` as E.01 transcribes it, so **no `RungDatum` exists at that frame's
own threshold**. The THRESHOLD VALUE is unaffected — `nextBound` never reads `T` — so the row is
checked TWICE: once at a legal `T` (`T = 3`, where `2·3 = 6 < 7` holds) and once
formula-directly, both giving `27`. ⚠ The `T = 3` rung is a legal `RungDatum` but does NOT chain
to frame 3's base either (`base.nextT = 4 ≠ 3`), which is why frame 3 gets no `LadderData` here
and no `boundAt` line: the two legal spellings are the ones executed.

*Reading (the gate's, adopted):* the Q3 sharpness frames are ENUMERATION frames outside
DEFINITION HE7-1's scope (`EFF.HE7.23`'s TEETH table is about reachable-height thresholds), OR
`hnode` is stronger than the chapter's own gate data — the chapter does not need to decide which,
because no node consumes frame 3 as a rung. **Binding consequence for consumers:** anything that
builds a `RungDatum` from a Q3 frame must check `ℓ * T < u` first; a `sorry`-free `RungDatum.mk`
at frame 3's corpus threshold is impossible, not merely awkward.

The other four frames build as genuine `RungDatum`s at `T₂ = D′h` (`2, 2, 6, 2` respectively),
and their bases chain to them (`base.nextT = D′h` in each case) — so frames 1, 2, 4, 5 are landed
as `LadderData` and read through `boundAt`.

## The E.08 leg, boundary-exact

`(‡₂) ⟹ (†₂)` (E.08's `lift_threshold_step`) fired at the frame-2 rung `(ℓ, g, u, T) = (2,2,5,2)`
with `b = 1`, `k = 17`, `s₀ = 1`, `m₀ = 6`: the hypothesis `(4−1)·5 + 2·1 = 17 ≤ 17` and the
conclusion `(2−1)·5 + 1 = 6 ≤ 6` are BOTH exact, so the implication is scored at its boundary,
where an off-by-one in either threshold would show.

## Frame bookkeeping (corpus letters → the landed arguments)

`RungDatum.mk ℓ g u T` (E.01). A frame `(e₁, f₁, h, ℓ, d_r, u)` contributes the base rung
`(e₁, f₁, h, 0)` — whose `nextBound 0 = (e₁f₁ − 1)h` is `bound₁` — and the level-2 rung
`(ℓ, d_r, u, D′h)`, whose `nextBound bound₁` is `bound₂`. `RungDatum.mk`'s four proof arguments
are `hℓ, hg, hcop, hnode`; the coprimality one is discharged with `decide`, the other three with
`norm_num`. No `native_decide` anywhere (repo policy).

**DEPENDS.** E.02 (`slotCount`/`nextT`/`nextBound`), E.05 (`LadderData`, `boundAt`), E.08
(`lift_threshold_step`) — all imported.

**SOURCE.** `EFF.HE7.23` TEETH (the five-frame table, verbatim values); `EFF.HE7.22` (sharpness —
this gate checks the sufficiency values only; the non-necessity half is the source's enumeration
evidence, §13).

**TEETH.** Q3/HE7-LIFT2 (ten frames, exhaustive) → the five threshold values become Lean
`decide`s. Retained regression: `verification/chapE_gate_thresholds.py`.

**ENVIRONMENT.** ENV-E1.

## Status

Sorry-free, axiom-free (Lean core only): the four gate-local ladders print Lean core, and every
`example` closes by `decide` or by an application of a landed lemma.
-/

namespace Uniformity.Density.Ladder

/-! ## The five frames, one step at a time (`RungDatum.nextBound`, E.02) -/

/-- frame 1 `(2,1,1,2,1,5)`: `bound₂ = (2·1−1)·5 + 2·1 = 7`. -/
example : (RungDatum.mk 2 1 5 2 (by norm_num) (by norm_num) (by decide)
    (by norm_num)).nextBound 1 = 7 := by decide

/-- frame 2 `(2,1,1,2,2,5)`: `bound₂ = (2·2−1)·5 + 2·1 = 17`. -/
example : (RungDatum.mk 2 2 5 2 (by norm_num) (by norm_num) (by decide)
    (by norm_num)).nextBound 1 = 17 := by decide

/-- frame 3 `(2,2,1,2,2,7)`, **[repaired: A-E.1/E-D7] leg (a)**: the node condition FAILS at the
corpus threshold `T₂ = D′h = 4` — `ℓ·T = 2·4 = 8 < 7` is false — so `RungDatum.mk 2 2 7 4` does
not exist and the row cannot be checked at its own threshold. -/
example : ¬ (2 * 4 < 7) := by decide

/-- frame 3, **leg (b)**: the same value `27` at a LEGAL `T = 3` (`2·3 = 6 < 7`). The recursion
never reads `T`, so the threshold value is untouched by the defect. -/
example : (RungDatum.mk 2 2 7 3 (by norm_num) (by norm_num) (by decide)
    (by norm_num)).nextBound 3 = 27 := by decide

/-- frame 3, **leg (c)**: the same value `27` formula-directly,
`(ℓd_r − 1)u + ℓ·bound₁ = (2·2−1)·7 + 2·((2·2−1)·1)`. -/
example : (2 * 2 - 1) * 7 + 2 * ((2 * 2 - 1) * 1) = 27 := by decide

/-- frame 3, **leg (d)**: the `T = 3` rung of leg (b) does not chain to frame 3's base either —
`base.nextT = D′h = 4 ≠ 3` — so no `LadderData` for this frame exists, at any spelling. -/
example : (RungDatum.mk 2 2 1 0 (by norm_num) (by norm_num) (by decide)
    (by norm_num)).nextT = 4 ∧ (4 : ℕ) ≠ 3 := by decide

/-- frame 4 `(3,1,2,2,3,13)`: `bound₂ = (2·3−1)·13 + 2·4 = 73`. -/
example : (RungDatum.mk 2 3 13 6 (by norm_num) (by norm_num) (by decide)
    (by norm_num)).nextBound 4 = 73 := by decide

/-- frame 5 `(1,2,1,3,2,11)`: `bound₂ = (3·2−1)·11 + 3·1 = 58`. (This frame's `hnode`, `3·2 < 11`,
is discharged by `decide` rather than the stub's `norm_num`: at the 4.31.0 pin `norm_num` reduces
`3 * 2 < 11` to `6 < 11` and then stalls, while the same tactic closes the other four frames'
`hnode`s. A tactic-choice deviation only — no value and no statement moves.) -/
example : (RungDatum.mk 3 2 11 2 (by norm_num) (by norm_num) (by decide)
    (by decide)).nextBound 1 = 58 := by decide

/-! ## The four base rungs' `bound₁ = (e₁f₁ − 1)h` -/

/-- frames 1 and 2, base `(e₁, f₁, h) = (2,1,1)`: `bound₁ = 1`. -/
example : (RungDatum.mk 2 1 1 0 (by norm_num) (by norm_num) (by decide)
    (by norm_num)).nextBound 0 = 1 := by decide

/-- frame 3, base `(2,2,1)`: `bound₁ = 3`. -/
example : (RungDatum.mk 2 2 1 0 (by norm_num) (by norm_num) (by decide)
    (by norm_num)).nextBound 0 = 3 := by decide

/-- frame 4, base `(3,1,2)`: `bound₁ = 4`. -/
example : (RungDatum.mk 3 1 2 0 (by norm_num) (by norm_num) (by decide)
    (by norm_num)).nextBound 0 = 4 := by decide

/-- frame 5, base `(1,2,1)`: `bound₁ = 1`. -/
example : (RungDatum.mk 1 2 1 0 (by norm_num) (by norm_num) (by decide)
    (by norm_num)).nextBound 0 = 1 := by decide

/-! ## The same table through `LadderData.boundAt` (E.05), for the four LEGAL frames

Each ladder is a genuine `LadderData`: the level-2 rung sits at `T₂ = D′h` and chains to the base
(`rungFollows`, i.e. `T₂ = base.nextT`), and `hnode` holds at every rung. Frame 3 is absent by
E-D7 (see leg (d) above). -/

/-- gate-local data (E.68): frame 1 `(2,1,1,2,1,5)` as a ladder — base `(2,1,1,0)`, rung
`(2,1,5,2)` with `T₂ = D′h = 2 = base.nextT`. -/
def gate68Frame1 : LadderData where
  base := RungDatum.mk 2 1 1 0 (by norm_num) (by norm_num) (by decide) (by norm_num)
  rungs := [RungDatum.mk 2 1 5 2 (by norm_num) (by norm_num) (by decide) (by norm_num)]
  hbase := rfl
  hchain := List.IsChain.cons_cons rfl (List.IsChain.singleton _)

/-- gate-local data (E.68): frame 2 `(2,1,1,2,2,5)` as a ladder. -/
def gate68Frame2 : LadderData where
  base := RungDatum.mk 2 1 1 0 (by norm_num) (by norm_num) (by decide) (by norm_num)
  rungs := [RungDatum.mk 2 2 5 2 (by norm_num) (by norm_num) (by decide) (by norm_num)]
  hbase := rfl
  hchain := List.IsChain.cons_cons rfl (List.IsChain.singleton _)

/-- gate-local data (E.68): frame 4 `(3,1,2,2,3,13)` as a ladder — base `(3,1,2,0)`, rung
`(2,3,13,6)` with `T₂ = D′h = 6`. -/
def gate68Frame4 : LadderData where
  base := RungDatum.mk 3 1 2 0 (by norm_num) (by norm_num) (by decide) (by norm_num)
  rungs := [RungDatum.mk 2 3 13 6 (by norm_num) (by norm_num) (by decide) (by norm_num)]
  hbase := rfl
  hchain := List.IsChain.cons_cons rfl (List.IsChain.singleton _)

/-- gate-local data (E.68): frame 5 `(1,2,1,3,2,11)` as a ladder — base `(1,2,1,0)`, rung
`(3,2,11,2)` with `T₂ = D′h = 2`. -/
def gate68Frame5 : LadderData where
  base := RungDatum.mk 1 2 1 0 (by norm_num) (by norm_num) (by decide) (by norm_num)
  -- `hnode` by `decide` here; see the frame-5 note above.
  rungs := [RungDatum.mk 3 2 11 2 (by norm_num) (by norm_num) (by decide) (by decide)]
  hbase := rfl
  hchain := List.IsChain.cons_cons rfl (List.IsChain.singleton _)

/-- frame 1 through the iterated recursion: `boundAt 0 = 1`, `boundAt 1 = 7`. -/
example : gate68Frame1.boundAt 0 = 1 ∧ gate68Frame1.boundAt 1 = 7 := by decide

/-- frame 2: `boundAt 0 = 1`, `boundAt 1 = 17`. -/
example : gate68Frame2.boundAt 0 = 1 ∧ gate68Frame2.boundAt 1 = 17 := by decide

/-- frame 4: `boundAt 0 = 4`, `boundAt 1 = 73`. -/
example : gate68Frame4.boundAt 0 = 4 ∧ gate68Frame4.boundAt 1 = 73 := by decide

/-- frame 5: `boundAt 0 = 1`, `boundAt 1 = 58`. -/
example : gate68Frame5.boundAt 0 = 1 ∧ gate68Frame5.boundAt 1 = 58 := by decide

/-- the four legal frames' level-2 thresholds are their `D′h`, read off the ladders: `2, 2, 6,
2` — the datum frame 3 cannot supply. -/
example : gate68Frame1.base.nextT = 2 ∧ gate68Frame2.base.nextT = 2
    ∧ gate68Frame4.base.nextT = 6 ∧ gate68Frame5.base.nextT = 2 := by decide

/-! ## The E.08 leg — `(‡₂) ⟹ (†₂)` fired boundary-exact at the frame-2 rung -/

/-- the Bézout bookkeeping at `k = 17`: `ℓ·m₀ + s₀·u = 2·6 + 1·5 = 17`. -/
example : (2 : ℕ) * 6 + 1 * 5 = 17 := by decide

/-- the hypothesis `(‡₂)` is EXACT at `k = 17`: `(L−1)u + ℓb = (2·2−1)·5 + 2·1 = 17`. -/
example : ((2 * 2 : ℕ) - 1) * 5 + 2 * 1 = 17 := by decide

/-- the conclusion `(†₂)` is EXACT at `m₀ = 6`: `(g−1)u + b = (2−1)·5 + 1 = 6`. -/
example : ((2 : ℕ) - 1) * 5 + 1 = 6 := by decide

/-- **E.08 fired**: at the frame-2 rung `(ℓ, g, u, T) = (2,2,5,2)` with `b = 1`, `k = 17`,
`s₀ = 1`, `m₀ = 6`, the lift-threshold implication delivers `(g−1)u + b ≤ m₀` — boundary-exact on
both sides, so an off-by-one in either threshold would fail here. -/
example : (2 - 1) * 5 + 1 ≤ 6 :=
  lift_threshold_step (RungDatum.mk 2 2 5 2 (by norm_num) (by norm_num) (by decide)
    (by norm_num)) (b := 1) (k := 17) (m₀ := 6) (s₀ := 1)
    (by decide) (by decide) (by decide)

end Uniformity.Density.Ladder

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Ladder.gate68Frame1
#print axioms Uniformity.Density.Ladder.gate68Frame2
#print axioms Uniformity.Density.Ladder.gate68Frame4
#print axioms Uniformity.Density.Ladder.gate68Frame5

end AxCheck
