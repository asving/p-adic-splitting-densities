/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapE.E01
import Uniformity.ChapE.E02
import Uniformity.ChapE.E05
import Uniformity.ChapE.E07
import Uniformity.ChapE.E49
import Uniformity.ChapE.E50
import Uniformity.ChapE.E60

/-!
# Uniformity.ChapE.E65 — the `q = 2` gate: the `n = 8` frame end-to-end, EXECUTED

**Chapter E, NODE E.65** [gate] [fresh] (`blueprint/CHAP-E_sigma_ladder.md` §10, the executable
gates; GC-11's two-prime rule pairs this `q = 2` battery with E.66's `q = 3` battery — neither
may be scored alone). ENV-E1.

The node signs three gate-local `def`s (the frame's two rungs and the ladder they form) and then
runs the frame end-to-end as `example`s over the landed defs and lemmas of E.01/E.02/E.05/E.07/
E.49/E.50/E.60. It proves no new mathematics: its job is to catch a mis-transcribed recursion,
an off-by-one threshold, or a dictionary row that drifted from `EFF.HE7.58`.

## The frame (`EFF.HE7.57`)

`(e₁, f₁, h) = (2, 1, 1)` at level 1 and `(ℓ, d_r) = (2, 1)` at level 2, with the level-2 slope
numerator `u = 5`. In E.01's letters a rung is `RungDatum.mk ℓ g u T`, so

* the **base rung** is `(ℓ, g, u, T) = (2, 1, 1, 0)` — the level-1 datum `(e₁, f₁, h, 0)`;
* the **level-2 rung** is `(2, 1, 5, 2)`, sitting at the threshold `T₂ = D′h = 2` the base
  produces (`rungFollows`, i.e. `T₂ = base.nextT`).

Everything the STATEMENT asks for is then a read of the landed recursions:

| check | value | source |
|---|---|---|
| `D′ = e₁f₁` | `slotCount = 2` | E.02 |
| `T₂ = D′h` | `base.nextT = 2` | E.02 |
| `bound₁ = (D′−1)h` | `base.nextBound 0 = 1` | E.02 |
| `T₃ = L·u = 2·1·5` | `rung.nextT = 10` | E.02 |
| `bound₂ = (L−1)u + ℓ·bound₁ = 1·5 + 2·1` | `rung.nextBound 1 = 7` | E.02 |
| `D′ = 2`, `D″ = D′·ℓd_r = 4` | `degAt 1 0 = 2`, `degAt 1 1 = 4` | E.05 |
| the same thresholds through the ladder | `boundAt 0 = 1`, `boundAt 1 = 7` | E.05 |
| the μ₂ = 2 dictionary rows, degree 8 | `mu2Sigma` + `mu2Sigma_degree` | E.49 |
| three letters, no fourth | `mu2Sigma_alphabet` | E.50 |
| `μ₀ = 4 ⟹ J ≤ 1` | `ladder_finite_bounds` clause 2 | E.60 |
| `2μ₂ ≤ 4 ⟹ μ₂ ≤ 2` | `jump_halving` (E.07(ii)) | E.07 |

Recomputed fresh at drafting, against the blueprint's own expected values: `2^(J+1) ≤ 4 ⟹
J ≤ 1` ✓; `2·μ₂ ≤ 4 ⟹ μ₂ ≤ 2` ✓; `(2·1−1)·5 + 2·1 = 7` ✓. No mismatch.

## How the checks are written

* **the lemmas are FIRED, not merely the defs evaluated.** The `J ≤ 1` and `μ₂ ≤ 2` bounds come
  out of `ladder_finite_bounds` and `jump_halving` applied at the frame — and the `J ≤ 1` leg is
  fired in its CONTRADICTION form (a second jump at `μ₀ = 4` is impossible for *every* mass
  sequence), which is the shape a consumer actually needs. The dictionary degrees come out of
  `mu2Sigma_degree`, the three-letter claim out of `mu2Sigma_alphabet`. Scoring only the `def`
  bodies would leave a mis-stated lemma hypothesis invisible.
* **the GC-11 gate-spelling rider (A-E.1/E-D10) is in play here** and is respected: comparisons
  BETWEEN `FactorizationType` values are closed by `rfl` (definitional), never by `decide` —
  `FactorizationType`'s `DecidableEq` is `Classical.decEq` and does not reduce. Only `ℕ`-valued
  reads (`degree`, `slotCount`, `nextT`, `nextBound`, `degAt`, `boundAt`) are `decide`d.
* **no `native_decide` anywhere** (repo policy).

## Overlap with E.68, declared

E.68's `gate68Frame1` is the same `(2,1,1,0) / (2,1,5,2)` ladder, and re-checks
`boundAt 0 = 1 ∧ boundAt 1 = 7`. The duplication is deliberate: E.65 is signed with its own
frame data in the committed stub, imports E.49/E.50/E.60 that E.68 does not, and must stay
readable as the standalone `q = 2` half of GC-11. Neither node imports the other.

**DEPENDS.** E.01, E.02, E.05, E.07, E.49, E.50, E.60 — all imported, all used.

**SOURCE.** `EFF.HE7.57` (the `n = 8` frame); `EFF.HE7.23` TEETH (the Q3 threshold table's first
two frames); `EFF.HE7.58` (the μ₂ = 2 dictionary).

**TEETH.** re-fires Q1/Q3's spot values as Lean-side `decide`s. Retained regression per GC-8:
`leanfinal/verification/chapE_gate_q2.py` (the blueprint pins it as `verification/…`; it lands
next to the corpus it mirrors, beside `drainage_check.py` and `equalchar_probe.py`). It
re-implements the E.02/E.05 recursions from the blueprint text — NOT by reading the Lean defs —
and re-checks every numeric expectation in the table above, so a drifted Lean recursion and a
drifted transcription cannot agree by accident. `python3 leanfinal/verification/chapE_gate_q2.py`
→ 27/27 checks pass (run at landing). The sibling gates E.66–E.68 do NOT yet have their pinned
mirrors (`chapE_gate_q3_seam.py`, `chapE_gate_ef.py`, `chapE_gate_thresholds.py`); those remain
owed.

**ENVIRONMENT.** ENV-E1.

## Status

Sorry-free; the three gate-local `def`s carry Lean-core axiom footprints only (printed below),
and every `example` closes by `rfl`, `decide`, `norm_num`, `omega`, or an application of a
landed Lean-core lemma.
-/

set_option linter.style.longLine false

namespace Uniformity.Density.Ladder

/-! ## The frame's data (`EFF.HE7.57`) -/

/-- gate-local data (E.65): the base rung `(e₁, f₁, h, 0) = (2, 1, 1, 0)` of the `n = 8` frame. -/
def gateBase65 : RungDatum :=
  RungDatum.mk 2 1 1 0 (by norm_num) (by norm_num) (by decide) (by norm_num)

/-- gate-local data (E.65): the level-2 rung `(ℓ, d_r, u, T₂) = (2, 1, 5, 2)`, at the threshold
`T₂ = D′h = 2`. -/
def gateRung65 : RungDatum :=
  RungDatum.mk 2 1 5 2 (by norm_num) (by norm_num) (by decide) (by norm_num)

/-- gate-local data (E.65): the `n = 8` ladder — base plus the one level-2 rung, chained by
`rungFollows` (`T₂ = base.nextT`).  [repaired: A-E.1/E-D2] the chain field is built through the
`List.IsChain` constructors; the deprecated `List.Chain.cons`/`.nil` of the stub are retyped. -/
def gateLadder65 : LadderData where
  base := gateBase65
  rungs := [gateRung65]
  hbase := rfl
  hchain := List.IsChain.cons_cons rfl (List.IsChain.singleton _)

/-! ## Leg 1 — the rung recursions (E.02) -/

/-- `D′ = e₁f₁ = 2`, the base rung's slot count. -/
example : gateBase65.slotCount = 2 := by decide

/-- `T₂ = D′h = 2`, the threshold the base produces. -/
example : gateBase65.nextT = 2 := by decide

/-- `bound₁ = (D′ − 1)h = 1` (the recursion seeded at `bound₀ = 0`). -/
example : gateBase65.nextBound 0 = 1 := by decide

/-- the level-2 rung sits at exactly that threshold — the chain condition, read as a value. -/
example : gateRung65.T = gateBase65.nextT := by decide

/-- `T₃ = L·u = (2·1)·5 = 10`. -/
example : gateRung65.nextT = 10 := by decide

/-- `bound₂ = (L − 1)u + ℓ·bound₁ = 1·5 + 2·1 = 7` — the blueprint's `(2·1−1)·5 + 2·1 = 7`. -/
example : gateRung65.nextBound 1 = 7 := by decide

/-- the threshold recursion is boundary-sensitive: seeding it at the WRONG previous bound
(`bound₁ = 0` instead of `1`) gives `5 ≠ 7`, so an off-by-one upstream cannot pass this gate. -/
example : gateRung65.nextBound 0 = 5 ∧ gateRung65.nextBound 0 ≠ gateRung65.nextBound 1 := by
  decide

/-! ## Leg 2 — the same frame through the ladder (E.05) -/

/-- `degAt`: the key degree at level 1 is `D′ = D₀·L₀ = 1·2 = 2`. -/
example : gateLadder65.degAt 1 0 = 2 := by decide

/-- `degAt`: at level 2 it is `D″ = D′·ℓd_r = 2·2 = 4` — so the frame's `n = D″·μ₂ = 4·2 = 8`. -/
example : gateLadder65.degAt 1 1 = 4 := by decide

/-- `boundAt`: the iterated (LIFT) recursion reproduces `bound₁ = 1` … -/
example : gateLadder65.boundAt 0 = 1 := by decide

/-- … and `bound₂ = 7`, matching the per-rung read of leg 1. -/
example : gateLadder65.boundAt 1 = 7 := by decide

/-- past the ladder's top rung `degAt` stalls (the `getD 1` branch) rather than inventing a
level: `D‴ = D″`. This pins the out-of-range convention the frame relies on. -/
example : gateLadder65.degAt 1 2 = 4 := by decide

/-! ## Leg 3 — the μ₂ = 2 dictionary at the frame (E.49, E.50)

The four decided polygon/peel rows and the `none` pointer row, read off `mu2Sigma` by `rfl`
(defect E-D10: `FactorizationType` equality does not `decide`). -/

example : mu2Sigma .oneSideHalf = some ⟨{(8, 1)}⟩ := rfl

example : mu2Sigma .oneSideInert = some ⟨{(4, 2)}⟩ := rfl

example : mu2Sigma .oneSideSplit = some ⟨{(4, 1), (4, 1)}⟩ := rfl

example : mu2Sigma .twoSides = some ⟨{(4, 1), (4, 1)}⟩ := rfl

/-- row 5 is a POINTER (re-read at the refined key, E.52), not a value. -/
example : mu2Sigma .refineRow = none := rfl

example : mu2Sigma .peelRow = some ⟨{(4, 1), (4, 1)}⟩ := rfl

/-- the three letters have degree `8` — `#eval`-style reads of `FactorizationType.degree`
(`8·1 = 8`, `4·2 = 8`, `4·1 + 4·1 = 8`). -/
example : (⟨{(8, 1)}⟩ : Uniformity.FactorizationType).degree = 8 := by decide

example : (⟨{(4, 2)}⟩ : Uniformity.FactorizationType).degree = 8 := by decide

example : (⟨{(4, 1), (4, 1)}⟩ : Uniformity.FactorizationType).degree = 8 := by decide

/-- the same three degrees PREDICTED by E.49's conservation lemma rather than computed: each
value is produced by naming its row, and `mu2Sigma_degree` returns the degree. -/
example : (⟨{(8, 1)}⟩ : Uniformity.FactorizationType).degree = 8 :=
  mu2Sigma_degree .oneSideHalf _ rfl

example : (⟨{(4, 2)}⟩ : Uniformity.FactorizationType).degree = 8 :=
  mu2Sigma_degree .oneSideInert _ rfl

example : (⟨{(4, 1), (4, 1)}⟩ : Uniformity.FactorizationType).degree = 8 :=
  mu2Sigma_degree .twoSides _ rfl

/-- E.50 fired at the frame: the four decided rows emit only the three listed letters — there is
no fourth value at `μ₂ = 2` (`EFF.HE7.61`). -/
example : ∀ r v, mu2Sigma r = some v →
    v = ⟨{(8, 1)}⟩ ∨ v = ⟨{(4, 2)}⟩ ∨ v = ⟨{(4, 1), (4, 1)}⟩ :=
  mu2Sigma_alphabet

/-! ## Leg 4 — the jump bounds at `μ₀ = 4` (E.60, E.07)

The frame's initial mass is `μ₀ = n / D′ = 8 / 2 = 4`. -/

/-- the numeric shadow of E.60's clause 1 at `μ₀ = 4`, on the bounded range: `2^(J+1) ≤ 4`
forces `J ≤ 1`. -/
example : ∀ J ≤ 8, 2 ^ (J + 1) ≤ 4 → J ≤ 1 := by decide

/-- the numeric shadow of the halving at `μ₀ = 4`: `2μ₂ ≤ 4` forces `μ₂ ≤ 2`. -/
example : ∀ m ≤ 8, 2 * m ≤ 4 → m ≤ 2 := by decide

/-- **E.60 clause 2 fired, in its contradiction form.** For EVERY mass sequence with the
A-E.1/E-D11 hypotheses at `J = 2`, initial mass `μ 0 = 4` is impossible: the `n = 8` frame
admits at most one level jump. (This is the shape the σ-ladder consumer needs — "no second jump
at `n = 8`" — not merely `1 ≤ 1` at one chosen sequence.) -/
example (μ : ℕ → ℕ) (h4 : ∀ i < 2, 4 ≤ μ i) (hh : ∀ i < 2, 2 * μ (i + 1) ≤ μ i)
    (h0 : μ 0 = 4) : False := by
  have hJ : (2 : ℕ) ≤ 1 := (ladder_finite_bounds μ 2 h4 hh).2.1 h0
  omega

/-- **E.60 clause 2 fired positively** at the frame's own mass sequence `μ = 4 → 2`: one jump,
and the bound says at most one. -/
example : (1 : ℕ) ≤ 1 :=
  (ladder_finite_bounds (fun i => if i = 0 then 4 else 2) 1 (by decide) (by decide)).2.1
    (by decide)

/-- **E.07(ii) fired** at the frame: the level-2 multiplier is `ℓd_r = 2`, so a level-2 mass
`μ₂` with `μ₂·2 ≤ 4` satisfies `2μ₂ ≤ 4`, i.e. `μ₂ ≤ 2` — the frame's `μ₂ = 2` is the extreme
value, attained. -/
example {μ₂ : ℕ} (h : μ₂ * 2 ≤ 4) : μ₂ ≤ 2 := by
  have := jump_halving (μ := 4) (μ₂ := μ₂) (p := 2) (by norm_num) h
  omega

/-- and the frame attains it: `μ₂ = 2`, `2·2 ≤ 4`. -/
example : (2 : ℕ) * 2 ≤ 4 := by decide

/-- the end-to-end degree read of the frame: `n = D″ · μ₂ = 4 · 2 = 8`, which is the degree every
decided dictionary row reports. -/
example : gateLadder65.degAt 1 1 * 2 = 8 := by decide

end Uniformity.Density.Ladder

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Ladder.gateBase65
#print axioms Uniformity.Density.Ladder.gateRung65
#print axioms Uniformity.Density.Ladder.gateLadder65

end AxCheck
