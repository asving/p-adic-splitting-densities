# Verdict NP-1 — the S2 level-one stage table (S2_SOURCE_PLAN §6 row NP-1)

**VERDICT: COMPLETE.** `leanfinal/Uniformity/ChapC/C130np1.lean` compiles clean
(`lake env lean`, zero errors/warnings); all 28 declarations print Lean-core axioms only
`[propext, Classical.choice, Quot.sound]`; no `sorry`, no new axiom, no `unsafe`, no
statement touched; no other unit's file touched (C130nv consumed read-only, olean built).

## What landed (mirror of CC-6's level-2 table, one level down)

- **VALUE**: NV-1's landed `C130nv.s2Hgt₁` **REUSED, not redefined** (the row's
  instruction); its landed bank (`_zero/_ne_top_slot/_add_ge/_add_eq` + `s2Hgt₁_mul`) is
  consumed verbatim by the carrier — reuse pinned by `s2Slot₁_hgt` (`rfl`).
- **q=2 collapse at level 1**: `s2Fld₁_card : Nat.card (fld 1) = 2` — definitionally
  C.80's `card_K₁` (C.97's constant residue tower), so the collapse DOES apply (the row's
  "check C35b's card facts" charge: the operative card fact is C80's, and it transports).
- **DIGIT** `s2Dig₁` (0 at 0, else 1) with `dig_zero`, slot-shaped `dig_ne_zero`,
  **forced-digit uniqueness** `s2Dig₁_forced` (any lawful table = this one on slot range),
  and the value/digit compatibility law `s2Dig₁_add` (char-2, no residual case).
- **FULL/LIFT**: `S2Full₁` (realizability on slot range, live and source-bound —
  `s2Full₁_ne_trivial`), teeth at 0/1/2 (witnesses `1, x, 2`), negative refuters
  (`not_s2Full₁_of_neg`), lift `s2Lift₁` (realizability IS the lift at |K₁|=2), **plus the
  level-one bonus CC-6 could not have: the COMPLETE characterization
  `s2Full₁_iff : S2Full₁ k ↔ 0 ≤ k`** (witness `2^m·x^j` via NV-1's product law).
- **Carrier + interface tie**: `s2Slot₁ : Ladder.SlotCarrier O (fld 1)` with numeral pins
  `D = 2 = ê₁·f̂₁ = 2·1` (`s2DepthTwo_Dcum_one` consumed as named), and the five CC-5
  `stageCarrier` ties at `i = 1` — `D`/`eC`/`fC` unconditional `rfl`s, `hgt`/`dig`/`Full`
  conditional in the CC-6 style (no `NodePointSource` instance exists; U13 refuted the
  present signature).

## Honesty scope

No `NodePointSource` inhabited; no slot ties/threshold/window/reads (NP-0/2/3/4/5/6-8);
no level-two fact restated; the digit table's tie to an actual residual read is NP-3's
(after RP-2), by design.
