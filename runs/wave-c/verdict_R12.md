# Verdict: UNIT R12 — rows R1 (stage-three slot tables) + R2 (stage-four slot tables)

**Status: LANDED, both rows, first attempt, zero repairs, zero `sorry`.**

Source: `docs/in-progress/DEEP_WITNESS_CAMPAIGN_2026-08-28.md` §6.4 rows R1 and R2.

New file: `leanfinal/Uniformity/ChapC/C136r1.lean`
(namespace `Uniformity.Density.Tower.C136r1`).

## Naming-ambiguity finding (flagged, resolved, documented in the file header)

The row text ties "level 3"/R1 to μ₄ data (D3-01/D3-05) and "level-4"/R2 to μ₅ data
(D4-01/D4-03). Read as literal `DeepTower` stage indices this is off by one from
the tower's own numbering (μ₄ lives at tower stage `i = 4`; μ₅ is not a tower stage
at all, per `DeepTower.hproper`'s exclusion of `e'f'=1` refinements). Cross-checked
against the campaign's own §6.2/§6.3 headers ("Depth-three / μ₄ operator stack",
"Depth-four / μ₅ refinement stack"), the row numerals are Okutsu–Montes REFINEMENT
DEPTH, not tower stage: μ₄ = OM-depth 3, μ₅ = OM-depth 4. Rather than gamble on one
reading, the file supplies the superset: BOTH the untouched tower-stage-3 branch
(μ₃, pre-existing `s2Hgt₃`) and the new tower-stage-4 branch (μ₄, this row's cited
input) for R1, and the μ₅-refinement bank for R2. No numeral is invented either way.

## The actual gap closed (the "source tables" blocker)

Grepping the whole μ₃/μ₄/μ₅ stacks (`C132nv1`, `C136d0`–`C136e1`) found HEIGHT
tables and `AddValuation` packagings landed at every level (`s2Hgt₃/s2Hgt₄/s2Hgt₅`),
but no digit table, `Full` predicate, or `lift` law at any of the three — the
`hgt/dig/Full/lift` bank the row asks for is only 1/4 landed going in. Since the S2
terminal residue field is the SAME two-element field at every level
(`C80.card_K₁`, transported exactly as `C130s6.s2Fld₂_card` does at level 2), the
digit/Full/lift bank is FORCED by the same argument NP-1/CC-6 already ran at levels
1/2 — not a faithfulness gap. Part 0 re-derives that argument generically
(parametrized by a bare `Nat.card F = 2` fact); Parts 1/2/4 instantiate it at
levels 3, 4, and the μ₅ refinement.

## What landed

* **Part 0** — `s2r1_eq_one_of_ne_zero`, `s2r1_one_add_one`: generic card-2-field
  copies of `C130s6`'s/`C130np1`'s private per-level units arguments.
* **Part 1 (R1, tower-stage-3/μ₃)** — `s2Fld₃_card`, `s2Dig₃` (+ zero/of_ne_zero/
  ne_zero/add laws), `S2Full₃`, `s2Lift₃`.
* **Part 2 (R1, tower-stage-4/μ₄, D3-01/D3-05 consumed)** — `s2Fld₄_card`,
  `s2Dig₄` (+ laws), `S2Full₄`, `s2Lift₄`.
* **Part 3 (R1 exit)** — the extended FOUR-branch total tables `s2NPHgtFour`,
  `s2NPDigFour`, `s2NPFullFour` (mirroring `C130sg.s2NPFull`'s two-branch recipe,
  now four), pin theorems at every level, and `s2LiftFour` — the `lift` law at
  every live level in one `interval_cases` dispatch, the exact shape a future
  depth-four `SplitNodePointSource`'s `lift` field needs.
* **Part 4 (R2, μ₅ refinement, D4-01/D4-03 consumed)** — `s2Dig₅` (+ laws),
  `S2Full₅`, `s2Lift₅`, bounded by degree `16` (= `Dcum 4`, not a fresh numeral:
  T5's `e'=f'=1` refinement is growth-free).
* **Part 5 (R2 exit)** — ★★ `s2SlotFourMu5 : Ladder.SlotCarrier O ((s2DepthFour
  h2 hq).fld 4)`, built to the exact field shape `C130k2.SplitNodePointSource
  .stageCarrier` produces at `i = 4` (`D/eC/fC` from the tower's own `Dcum 4`/
  `ehat 4`/`fhat 4` — valid reuse since `e'=f'=1` leaves both cumulative
  invariants unchanged), with `hgt/dig/Full/hlift` from the Part 4 bank.
  `s2SlotFourMu5_hgt_eq : (s2SlotFourMu5 h2 hq).hgt = s2Hgt₅ h2 hq` (`rfl`) is
  the row's requested point-height tie.

## Named open (not invented)

The row asks the carrier be tied to μ₅'s `FGMNSourceData.nextValue`. No
`FGMNSourceData` record exists yet for the μ₅ refinement (that is D4-17, not
cited as landed for this row). `s2SlotFourMu5_hgt_eq` is the tightest honest tie
available now (constructional, `rfl`); the further identification
`(future D4-17 record).nextValue = s2Hgt₅` is D4-17's job, recorded as an open
in the file's docstring, not filled with an invented record here.

## Verification

```
cd leanfinal && timeout 580 ~/.elan/bin/lake env lean Uniformity/ChapC/C136r1.lean
```

Exit code 0 at every increment (6 incremental checks: skeleton, Part 1, Part 2,
Part 3, Part 4, Part 5+AxCheck). Final AxCheck footer output is 44 `#print axioms`
lines; zero errors, zero warnings, zero `sorry`. Every declaration's footprint is
`[propext, Classical.choice, Quot.sound]` (Lean-core only).

## Scope discipline

GCW-6 fence respected: everything in the file is DATA (digit/Full/lift laws,
total tables, one `Ladder.SlotCarrier`) — no `SplitNodePointSource`,
`ChainRealization`, or `RealizedInput` is touched (that remains R3/R7/R9). No
landed file was edited; `C136e1.lean` (another unit's territory) untouched; no
git operations performed.
