# Unit CC06 verdict — chain-carrier node CC-6 (S2 stage regression)

## Verdict

**LANDED — all four stage-field groups (VALUE / DIGIT / FULL / LIFT), every law in its
exact `NodePointSource` field shape at `i = 2`, plus the concrete `SlotCarrier`.**
One new file `leanfinal/Uniformity/ChapC/C130s6.lean` (namespace
`Uniformity.Density.Tower.C130s6`, collision-safe against in-flight CC units).
No `sorry`, no new axiom, no `unsafe`, no other file touched. 53 `#print axioms`
lines, every one Lean-core (49 × the full triple, 3 axiom-free, 1 `propext`-only).

Per stage field:

| field group | status | content |
|---|---|---|
| VALUE `hgt 2` | **LANDED** | `s2Hgt₂` := C.11's `dv2Hgt` at the LANDED S2 level datum (C.44 `levelDatum` of C.80's `s2Tower`) = `dvSupp (s2Frame) · 5 2`, coerced `ℕ∞ → WithTop ℤ`; both identifications are `rfl` pins. Laws `hgt_zero`, `hgt_ne_top` (proved for ALL nonzero `A`, stronger than the slot-fenced field), `hgt_add_ge`, `hgt_add_eq` — all proved. |
| DIGIT `dig 2` | **LANDED** | `s2Dig₂` (0 at 0, else 1) — FORCED by the q=2 collapse: `s2Fld₂_card : Nat.card (fld 2) = 2` (C.80's `card_K₁`, definitional along C.97's constant residue tower); `s2Dig₂_forced` proves ANY lawful table agrees on slot range (the C130A "free tables" cure). `dig_zero`, `dig_ne_zero`, `dig_add` (char-2 makes the nonzero-sum hypothesis force a zero side, height ⊤ ≠ k) — all proved. |
| FULL `Full 2` | **LANDED** | `S2Full₂ k` := realized by a nonzero slot-range polynomial (maximal honest instance; `EFF.T2.10` criteria stay consumer-side per E.10's own doctrine). LIVE, not `True`: `S2Full₂ 0/2/5` inhabited (witnesses `1`, `x`, `Φ′`), `¬S2Full₂ k` for all `k < 0`, `S2Full₂ ≠ fun _ => True`. |
| LIFT | **LANDED** | `s2Lift₂` — a THEOREM at this occurrence: with two-element `K₂` the only nonzero digit is 1, so `(LIFT)` = realizability = exactly what `S2Full₂` certifies. |

The concrete carrier: **`s2Slot₂ : Ladder.SlotCarrier O ((s2DepthTwo h2 hq).fld 2)`** —
`D = Dcum 2 (= 4)`, `(eC, fC) = (ê₂, f̂₂) (= 4, 1)` with C130st's proved `(DEG-EF)` split,
all law fields from the above; numeral pins `s2Slot₂_D/eC/fC` and `rfl` table pins.

**The "via CC-5 `stageCarrier`" clause, honestly conditional:** no `NodePointSource` is
inhabitable yet (points/threshold/reads are CC-9/7/10/11). Landed instead:
`stageCarrier_D_eq_s2` / `stageCarrier_eC_fC_eq_s2` (UNCONDITIONAL `rfl`: the produced
`D/eC/fC` at the S2 level 2 are `s2Slot₂`'s for ANY future instance), and
`stageCarrier_hgt/dig/Full_eq_s2` (conditional: any instance carrying these stage tables
at `i = 2` produces exactly `s2Slot₂`'s tables through `stageCarrier` — the proofs are the
hypotheses themselves, via CC-5's `rfl` pins). No BLOCKED item remains inside CC-6's
scope; the point theorem the design's exit condition anticipated (`slot_value`/
`slot_digit` exactness of `dv2Hgt` at legal points, C.11's documented C.25/C.26-style
obligation) belongs to the POINT fields and is CC-9's, as recorded in the file docstring.

## New reusable supply (Part 2 — generic, any frame/side)

`dvSupp` valuation-law bank, mirrored from B32b one level up (`dvSupp` is the NESTED
cleared support, so B32b did not apply verbatim): `dvSupp_zero_eq_top`,
`dvSupp_eq_inf_range`, `dvSupp_ne_top_of_ne_zero` (via B.05 `sum_dev_eq`),
`min_dvSupp_le_dvSupp_add`, `dvSupp_neg`, `dvSupp_add_eq_of_lt`, and
**`dvSupp_add_eq` (ultrametric equality off ties — new at any level above `suppVal`;
derived from the inequality + neg-invariance by the standard `A = (A+B) + (−B)`
argument, no attainment analysis)**. Also `toZ : ℕ∞ → WithTop ℤ` with a small public
API (E.55's private `nv`, made reusable for CC-17).

## Regression teeth

`s2Hgt₂ 1 = 0`, `s2Hgt₂ x = 2` (cleared `v₂(x) = 1/2`), `s2Hgt₂ Φ′ = 5 = u₂` (the table
sees the tower height), and `s2Hgt₂ f₅ = 10 = E₂` read off C.80's landed `dvsupp_f₅`.

## Consumption note (brief vs. actual)

Design §6 named C.46/C.47/C.127 as the stage pieces. Actual consumption: the tables ride
C.02/C.06/C.11 (`stageHeight`/`dvSupp`/`dv2Hgt`) + C.35b/C.80 landed S2 computations
(`sh_C/sh_X/sh_zero`, `card_K₁`, `dvsupp_f₅`) + C118a helpers + the B-chapter dev bank.
C.46/C.47 are the KEY-side computations (already consumed by CC-2) and will feed CC-9's
point ties; C.127's law E-W lives at the trinomial frame (`e₂ = 1`), which the S2 tower
(`e₂ = 2`) does not instantiate. Recorded in the file docstring.

## Declarations (53, all `#print axioms` Lean-core)

Part 1: `toZ`, `toZ_top`, `toZ_coe`, `toZ_eq_top_iff`, `toZ_le_toZ_iff`, `toZ_min`,
`toZ_inj`, `toZ_eq_intCast_iff`.
Part 2: `dvSupp_zero_eq_top`, `dvSupp_eq_inf_range`, `dvSupp_ne_top_of_ne_zero`,
`min_dvSupp_le_dvSupp_add`, `dvSupp_neg`, `dvSupp_add_eq_of_lt`, `dvSupp_add_eq`.
Part 3: `s2Hgt₂` (+`_eq_dvSupp`, `_eq_dv2Hgt`, `_zero`, `_ne_top`, `_ne_top_slot`,
`_add_ge`, `_add_eq`, `_one`, `_X`, `_key`, `_f₅`), `s2Fld₂_card`, `s2Dig₂` (+`_zero`,
`_of_ne_zero`, `_ne_zero`, `_forced`, `_add`), `S2Full₂`, `s2Lift₂`, `s2Full₂_zero/two/
five`, `not_s2Full₂_of_neg`, `s2Full₂_ne_trivial`, `s2Slot₂` (+`_D`, `_eC`, `_fC`,
`_hgt`, `_dig`, `_Full`), `stageCarrier_D_eq_s2`, `stageCarrier_eC_fC_eq_s2`,
`stageCarrier_hgt_eq_s2`, `stageCarrier_dig_eq_s2`, `stageCarrier_Full_eq_s2`.
Private helpers (file-local, per the established private-copy pattern):
`fld₂_eq_one_of_ne_zero`, `fld₂_one_add_one` (C.80's `eq_one_of_card_two` re-derivations),
`sh_one`, `one_mod_key`, `one_div_key`.

## Verification

Run from `leanfinal/`:

```text
lake env lean Uniformity/ChapC/C130s6.lean   # exit 0 (2026-08-24); 53 footprint lines, all Lean-core
lake build Uniformity.ChapC.C130s6           # Build completed successfully (8685 jobs)
```

## Notes for the orchestrator

* Everything is inside the `C130s6` namespace — no shared-namespace names added, so no
  collision risk with in-flight CC03/CC04/CC07/CC13/C131w (C130pt.lean appeared during
  this unit's run and was not touched or read).
* CC-17 assembly consumes: the four table definitions + the nine law lemmas (exact field
  shapes at `i = 2`), `s2Slot₂`, and the ties. CC-9's exactness obligation is stated in
  the docstring so the point unit can target it: `hgt 2` = `toZ ∘ dv2Hgt(levelDatum
  s2Tower)`; `slot_value` at level 2 must equate the legal-point valuation of the
  evaluation with THIS table on slot range (`deg < 4`).
* The generic Part-2 bank (`dvSupp_add_eq` especially) is frame-generic supply usable by
  any future level-2 table (e.g. a `linTower` instance once its `DeepTower` bridge lands).
