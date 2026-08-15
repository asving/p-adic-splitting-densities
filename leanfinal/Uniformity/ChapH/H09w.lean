/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapH.H06
import Uniformity.ChapH.H09
import Uniformity.ChapH.H12
import Uniformity.ChapH.H21
import Uniformity.ChapH.H72
import Uniformity.ChapH.H74

/-!
# Uniformity.ChapH.H09w — the `StageInterface` NON-VACUITY WITNESSES (genre E and genre F)

**A witness file for NODE H.09, not a blueprint node.** It declares no new mathematics: it exhibits
inhabitants of `StageInterface` (H.09) so that H.72 (`rate_lossPriced`) and every other
`StageInterface`-consuming theorem is a statement about a NON-EMPTY type. Nothing downstream may
cite this file for content; it may be cited only for inhabitation.

## Why it exists

* **RETIREMENT FINDING R3** (`leanspec/Leanspec/ChapH.lean`, header census, 2026-08-15): *"the
  landed corpus contains **no** inhabitant of `StageInterface` (`grep -rn ': StageInterface'
  leanfinal/` finds only binders and docstrings), so `leanfinal`'s H.72 is a theorem about a
  possibly-empty type. The repo's only witness is `stageIfaceE` here, and `leanspec` is never
  imported by `leanfinal`."* This file moves that witness across the boundary (the code moves, with
  its proof terms — `leanfinal` must not import `leanspec`) and adds the genre-F one.
* **§3's design note** (`blueprint/CHAP-H_general_induction.md`, THE GENRE SCHEMA AND THE STAGE
  INTERFACE): *"Two instances are exhibited (H.38's genre E and H.42's genre F) with
  `stageLoss = 0`, which is exactly the exemption `EFF.GENIND.199` grants."* — struck at A-H.1/F2 as
  FALSE as committed (H.38/H.42 sign only `lawE`/`lawV1E2` plus exponent lemmas). This file is what
  makes the *repaired* note true: the genre-E instance is landed here (booked as H.38-adjacent
  content) and so is the genre-F one.
* **§16 TODO item 14** (`[TODO, added: A-H.1/F2] The genre-F StageInterface instance is OWED`):
  *"The genre-F one (over a datum with `f₁ = 2`, e.g. `genreD2bwitness`'s schema — the cell where
  the MASS normalization of `hbracket` is visible, per H.09's normalization note) is a new small
  node or the §3 claim stays withdrawn … Until it lands, every `f₁ ≥ 2` consumer of
  `StageInterface` is a theorem about an unexhibited instance family."* Item 14 is DISCHARGED by
  `stageIfaceF` below, at exactly the datum the item names.

## What is witnessed, precisely

Both witnesses take `stageLoss = 0`, the `EFF.GENIND.199` entry exemption §3's note names, and both
sit at the minimal side length `S = G.sideLen = 4 = 2 · G.keyDeg` (so H.33's `2a ≤ S` holds at
equality — the floor-adjacent cell, inhabited).

* `stageIfaceE : StageInterface (genreE2 0) 2 0 4` — genre E, `(Q; e₁, f₁, μ; h) = (2; 2, 1, 2; 1)`,
  stage residue cardinality `|K| = Q^{f₁} = 2`. **Ported verbatim, with its proof terms**, from the
  stage-0e stub gate `leanspec/Leanspec/ChapH.lean` (gate section, where it was built to
  machine-refute H.72's committed display, A-H.1/D4).
* `stageIfaceF (N H : ℕ) (l : StageLeaf) : StageInterface genreD2bwitness N H 4` — genre F,
  `(Q; e₁, f₁, μ; h) = (2; 1, 2, 2; 1)` (`genreD2bwitness`, H.12), the quartic `(1,2,2)` schema with
  `|K| = Q^{f₁} = 4`. This is the `f₁ ≥ 2` cell TODO item 14 asks for, and it is landed as a FAMILY
  over the ambient window `N`, the entry height `H` and the decided leaf `l` — so no `f₁ ≥ 2`
  consumer is left with an unexhibited instance family. Its minimal cell is `stageIfaceF 2 0 .ram :
  StageInterface genreD2bwitness 2 0 4`, the exact analogue of the genre-E point.

`stageWindow` is `G.e₁ * (N − 1 − H)` in both (the smallest value `hwin` admits at zero loss:
`2 * (2 − 1 − 0) = 2` for E, `1 * (N − 1 − H)` for F), `entryCodim = slack = 0`, `drainFrac = 0`,
and `stageSigma` is a `stageSigma` row of the H.73 leaf dictionary.

**The brackets are the MASS normalization, and at genre F that is visible.** `bracket κ = 2^{2κ−1}`
for E and `3 · 4^{2κ−1} = (|K|−1)|K|^{(c(2)+1)κ−1}` for F. At `κ = μ = 2` the genre-F value is
`192`, which is exactly H.21's certified `alphaBracket 4 1 2` — the mass form — and `192 = 16 · 12`
is H.21's `ghost × letters` reconciliation, not the letter-sum `12`. The gate section below checks
both, and checks that the letter-sum candidate `κ ↦ (|K|−1)|K|^{κ−1}` FAILS `hbracket` at this
datum: exactly the "loudly, at elaboration time" failure H.21's ⚠ note promises a genre-F instance
would expose.

**Two honest asymmetries between the witnesses.** (1) `stageIfaceE.hsigma` is the gate's `decide`
(verbatim port); `stageIfaceF.hsigma` routes through H.74's general `stageSigma_degree`, so it needs
no decidability of `FactorizationType` (finding F1: `DecidableEq FactorizationType` is
noncomputable) and it holds for every leaf `l`. (2) Nothing here discharges any *teeth* obligation:
`(CS-1Q)`/`(CS-3)` still have NONE anywhere in the corpus (H.09's signed vacuity disclosure), and
`HYP.36` is still CARRY. Inhabitation is not verification — these witnesses show the hypothesis
family is non-empty, **not** that any particular arithmetic stage satisfies it.

DEPENDS: H.06 (`genreE2`), H.09 (`StageInterface`), H.12 (`genreD2bwitness`), H.13 (`clusterC`),
H.21 (`alphaBracket_audit`, `massNorm_eq_ghost_mul_letters` — gate cross-checks only), H.72
(`rate_lossPriced` — fired at both witnesses in the gate), H.73 (`StageLeaf`, `stageSigma`), H.74
(`stageSigma_degree`).

## Status

Sorry-free, axiom-free (Lean core only). Non-vacuity assertions and the axiom gate are at the
bottom of the file.
-/

set_option linter.style.longLine false

namespace Uniformity.Density.Induction

/-! ## 1. The genre-E witness (ported verbatim from the stage-0e stub gate) -/

/-- **The genre-E `StageInterface` witness.** Genre E at `t = 0` (`(Q,e₁,f₁,μ,h) = (2,2,1,2,1)`),
window `N = 2`, entry height `H = 0`, side length `S = 4`, `stageLoss = 0` (the `EFF.GENIND.199`
entry exemption). All eleven fields proved.

PROVENANCE: ported verbatim, proof terms included, from `stageIfaceE` in
`leanspec/Leanspec/ChapH.lean` (the stage-0e gate section, where it machine-refuted H.72's committed
display; A-H.1/D4). `leanfinal` may not import `leanspec`, so the code moves. -/
def stageIfaceE : StageInterface (genreE2 0) 2 0 4 where
  stageWindow := 2
  stageLoss := 0
  entryCodim := 0
  slack := 0
  bracket := fun κ => 2 ^ (2 * κ - 1)
  drainFrac := fun _ => 0
  stageSigma := stageSigma (genreE2 0) .ram
  hS := by decide
  hwin := by decide
  hprice := by decide
  hbracket := by
    intro κ hκ
    have hc : (clusterC (genreE2 0).μ + 1) * κ = 2 * κ - 1 + 1 := by
      simp [clusterC, genreE2]
      omega
    have hsc : (genreE2 0).stageCard = 2 := by decide
    rw [hc, hsc, pow_succ]
    ring
  hdrain_nonneg := by intro M; norm_num
  hdrain_le_one := by intro M; norm_num
  hsigma := by intro _; decide

/-! ## 2. The genre-F witness (§16 TODO item 14) -/

/-- **The genre-F `StageInterface` witness family.** Over `genreD2bwitness` (H.12), the quartic
`(1,2,2)` schema `(Q; e₁, f₁, μ; h) = (2; 1, 2, 2; 1)` — genre F, `|K| = Q^{f₁} = 4` — at the
minimal side length `S = 4 = G.sideLen = 2 · G.keyDeg`, every ambient window `N`, every entry height
`H`, and every decided leaf `l`. `stageLoss = 0` (the `EFF.GENIND.199` exemption §3's design note
names), `stageWindow = e₁(N − 1 − H) = N − 1 − H`, `entryCodim = slack = 0`, `drainFrac = 0`.

`bracket κ = 3 · 4^{2κ−1}` is the MASS normalization `(|K|−1)|K|^{(c(μ)+1)κ−1}` at `|K| = 4`,
`c(2) = 1`; at `κ = μ = 2` its value is H.21's certified `alphaBracket 4 1 2 = 192`. This is the
datum where a letter-sum discharge of `(CS-2)` would be off by the ghost `|K|^{c(μ)μ} = 16`
(H.09's ⚠ NORMALIZATION note, H.21's ⚠ WHY THE RECONCILIATION IS A NODE) — checked both ways in the
gate below.

Discharges §16 TODO item 14; the minimal cell `stageIfaceF 2 0 .ram` is the genre-E point's
analogue. -/
def stageIfaceF (N H : ℕ) (l : StageLeaf) : StageInterface genreD2bwitness N H 4 where
  stageWindow := N - 1 - H
  stageLoss := 0
  entryCodim := 0
  slack := 0
  bracket := fun κ => 3 * 4 ^ (2 * κ - 1)
  drainFrac := fun _ => 0
  stageSigma := stageSigma genreD2bwitness l
  hS := by decide
  hwin := by simp [genreD2bwitness]
  hprice := by simp
  hbracket := by
    intro κ hκ
    have hc : (clusterC genreD2bwitness.μ + 1) * κ = 2 * κ - 1 + 1 := by
      have hcc : clusterC genreD2bwitness.μ = 1 := by decide
      rw [hcc]
      omega
    have hsc : genreD2bwitness.stageCard = 4 := by decide
    rw [hc, hsc, pow_succ]
    ring
  hdrain_nonneg := by intro M; norm_num
  hdrain_le_one := by intro M; norm_num
  hsigma := fun _ => stageSigma_degree genreD2bwitness l

end Uniformity.Density.Induction

/-! ## 3. NON-VACUITY — the assertions finding R3 asks for

Each `example` is an inhabitation claim, and nothing more. -/

section NonVacuity

open Uniformity.Density.Induction

-- Genre E: `StageInterface` is inhabited at all (R3's headline gap).
example : Nonempty (StageInterface (genreE2 0) 2 0 4) := ⟨stageIfaceE⟩

-- Genre F at the minimal cell, i.e. an `f₁ ≥ 2` datum (§16 TODO item 14's headline gap).
example : Nonempty (StageInterface genreD2bwitness 2 0 4) := ⟨stageIfaceF 2 0 .ram⟩

-- The whole genre-F FAMILY, over every ambient window and entry height: item 14's *"every `f₁ ≥ 2`
-- consumer of `StageInterface` is a theorem about an unexhibited instance family"* is discharged.
example : ∀ N H : ℕ, Nonempty (StageInterface genreD2bwitness N H 4) :=
  fun N H => ⟨stageIfaceF N H .ram⟩

-- Genre F at its own visibility window (`N ≥ 4k + 1 = 5` at `h = k = 1`), one witness per decided
-- leaf of the H.73 dictionary — the σ field is not what constrains inhabitation.
example : Nonempty (StageInterface genreD2bwitness 5 0 4) := ⟨stageIfaceF 5 0 .ram⟩
example : Nonempty (StageInterface genreD2bwitness 5 0 4) := ⟨stageIfaceF 5 0 .twoSided⟩
example : Nonempty (StageInterface genreD2bwitness 5 0 4) := ⟨stageIfaceF 5 0 .inert⟩

end NonVacuity

/-! ## 4. GATE — H.72 fired at both witnesses, and the mass normalization checked at genre F -/

section WitnessGate

open Uniformity.Density.Induction

/-! ### H.72 `rate_lossPriced` at the two witnesses.
Its hypothesis type is no longer possibly-empty: here is the theorem applied. The repaired
(A-H.1/D4 CANDIDATE A) display is TIGHT — both sides are `4` — at each witness, as the blueprint's
H.38-adjacent note claims for genre E and as item 14 asks to be confirmed for genre F. -/

example : 2 * ((genreE2 0).f₁ * stageIfaceE.stageWindow) + (4 + 1) * 0
      + 2 * stageIfaceE.entryCodim + 2 * stageIfaceE.slack
    ≥ 2 * (genreE2 0).keyDeg * (2 - 1 - 0) + 2 * (genreE2 0).keyDeg * 0 + 0 :=
  rate_lossPriced stageIfaceE

example : 2 * (genreD2bwitness.f₁ * (stageIfaceF 2 0 .ram).stageWindow) + (4 + 1) * 0
      + 2 * (stageIfaceF 2 0 .ram).entryCodim + 2 * (stageIfaceF 2 0 .ram).slack
    ≥ 2 * genreD2bwitness.keyDeg * (2 - 1 - 0) + 2 * genreD2bwitness.keyDeg * 0 + 0 :=
  rate_lossPriced (stageIfaceF 2 0 .ram)

-- Tightness at genre E: `4 ≥ 4`.
example : 2 * ((genreE2 0).f₁ * stageIfaceE.stageWindow) + (4 + 1) * 0
      + 2 * stageIfaceE.entryCodim + 2 * stageIfaceE.slack
    = 2 * (genreE2 0).keyDeg * (2 - 1 - 0) + 2 * (genreE2 0).keyDeg * 0 + 0 := by decide

-- Tightness at genre F: `4 ≥ 4` again, with the `f₁`/`e₁` roles exchanged.
example : 2 * (genreD2bwitness.f₁ * (stageIfaceF 2 0 .ram).stageWindow) + (4 + 1) * 0
      + 2 * (stageIfaceF 2 0 .ram).entryCodim + 2 * (stageIfaceF 2 0 .ram).slack
    = 2 * genreD2bwitness.keyDeg * (2 - 1 - 0) + 2 * genreD2bwitness.keyDeg * 0 + 0 := by decide

/-! ### The mass normalization, at the genre-F witness.
H.09's ⚠ note: `hbracket` is the MASS form, the two normalizations differ by the ghost
`|K|^{c(μ)κ}`, *"invisible at genre E and visible at genre F"*, and a genre-F instance is where a
wrong normalization surfaces. It surfaces here. -/

-- The witness's bracket at `κ = μ = 2` IS H.21's certified mass number `alphaBracket 4 1 2 = 192`.
example : (stageIfaceF 2 0 .ram).bracket 2 = alphaBracket 4 1 2 := by
  rw [alphaBracket_audit.1]
  decide

-- ... which is H.21 clause (iv)'s `ghost × letters`: `16 · 12 = 192`, ghost `= |K|^{μ} = 4²`.
example : (stageIfaceF 2 0 .ram).bracket 2 = 4 ^ 2 * ((4 - 1) * 4 ^ 1) := by
  rw [massNorm_eq_ghost_mul_letters, alphaBracket_audit.1]
  decide

-- ... and the letter-sum candidate `κ ↦ (|K|−1)|K|^{κ−1}` does NOT satisfy `hbracket` at this
-- datum: at `κ = 1` it gives `12`, the mass form gives `48`. A letter-normalized genre-F instance
-- fails to elaborate, which is exactly the guard H.21's ⚠ note promises.
example : ¬ (∀ κ, 1 ≤ κ →
    ((genreD2bwitness.stageCard - 1) * genreD2bwitness.stageCard ^ (κ - 1))
        * genreD2bwitness.stageCard
      = (genreD2bwitness.stageCard - 1)
        * genreD2bwitness.stageCard ^ ((clusterC genreD2bwitness.μ + 1) * κ)) := by
  intro h
  have h1 := h 1 (le_refl 1)
  revert h1
  decide

-- The genre-E bracket at `κ = 2`, for contrast: `2^3 = 8`, and there `|K| = Q = 2`, where H.21's
-- numeric gate records the two normalizations as numerically EQUAL (the ghost is invisible).
example : stageIfaceE.bracket 2 = 8 := by decide

end WitnessGate

/-! ## 5. Axiom footprint — both witnesses must be Lean-core only -/

section AxCheck

#print axioms Uniformity.Density.Induction.stageIfaceE
#print axioms Uniformity.Density.Induction.stageIfaceF

end AxCheck
