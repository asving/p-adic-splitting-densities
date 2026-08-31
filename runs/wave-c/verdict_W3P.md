# UNIT W3P verdict — W-a/W-b/W-c LAND (all three are plumbing, as promised) and the S2 rung-3 `RungLift` + `towerPacks` FIRE at the keystone (2026-08-31)

**Status: COMPLETE — ★ the deepTwist bank's tower side is inhabited to rung 3+ at the
keystone genre, Lean-core.**
`leanfinal/Uniformity/ChapI/I10RungLift3W.lean` (NEW, ~370 lines, namespace
`Uniformity.Density.Tower.I10rl3w`) — 0 errors, 0 warnings, **0 `sorry`**; all **15**
printed footprints exactly `[propext, Classical.choice, Quot.sound]`.  Verified
per-file (`timeout 580 ~/.elan/bin/lake env lean Uniformity/ChapI/I10RungLift3W.lean`,
exit 0), per-target (`lake build Uniformity.ChapI.I10RungLift3W` — Build completed
successfully, 8858 jobs), and aggregator (`Uniformity/ChapI.lean` + the one sanctioned
import line, exit 0).  Cite ledger: **empty** — every input is landed repo content.

## STATUS FIRST — the three lemmas, exactly as RL3 §6 demanded

| lemma | statement landed | mechanism (all landed content) |
|---|---|---|
| **W-a** `s2_exact_ne` | `deg g < deg g8` + `dv2Supp … g 21 2 = m` ⇒ `eval 1 (s2Mu3GradedRes m g) ≠ 0` — the S2 pack's eval-1 `exact_ne`, consumed verbatim by `s2Rung2Pack` | C136d2's ALREADY-LANDED eval-1 collapse **at the deg-8 fence** (`eval_one_s2Mu3GradedRes_eq_coeff_zero` — built for the μ₄ level's inner reads, which are exactly the dev-g8 coefficients) + C132rp8's fence-free `s2Mu3GradedRes_ne_zero_of_exact` + `S2Mu3ExactGrade_iff_dv2Supp`.  STRICTLY LESS new proof than RL3 forecast: no fresh C132rp1 gate re-derivation was needed — two verbatim private twins of C136d2's constant-collapse pair suffice |
| **W-b** `s2_nextSupp_g16` | `nextSupp s2Carrier s2Key g16 = 170` | two halves: (generic) `nextSupp_eq_inf_range` — the ℕ-indexed `nextSupp` infimum truncates to the development range, past-degree slots price `⊤`; (S2) `s2_nextSupp_eq_dv3Supp` for **every** `f` — term-for-term, since `dv3Pin = dv2Supp ∘ dev g8` by definition and `2•x = 2·x`; then the landed `g16_exactGrade` through `S2Mu4ExactGrade_iff_dv3Supp` (the s2Hgt₄/toZ bridge is inside that landed iff) |
| **W-c** `s2_eval_one_nextRead_g16` | `eval 1 (nextRead s2Carrier s2Key 170 g16) = 0` | payload `s2_nextRead_g16 : nextRead … 170 g16 = X² + 1` — the landed μ₄ residual `s2Mu4GradedRes_g16 = X + 1` with slots dilated by the ramification stretch `ℓ = 2` (raw abscissae `{0, 2}`; odd and past-fence slots die on the `(85,2)` guard); dictionary through a verbatim twin of WCC's private `s2Mu4Coeff_eq_wcoeff`; eval-1 is reindex-invariant and the landed char-2 tooth `C130rp2.tooth_char_two` (`1 + 1 = 0` in `fld 2`) kills it |

**Honesty ruling: all three ARE pure plumbing against landed content — no real gap
surfaced anywhere.** No statement weakened; `RungLift`/`RungPack`/`PackAt`/`LiftAt`
and WCC's `s2Carrier`/`s2Key` consumed byte-verbatim (anti-drift pin `s2Key_key`).

## ★★ THE FIRE

* `s2Rung2Pack : RungPack O (fld 2) 85 2` — WCC's carrier/key completed by W-a; the
  keystone rung-2 pack (`s2Rung2PackAt` bundled).
* `s2RungLift3 : RungLift (s2Rung2Pack) (fld 2) 171 1 := RungLift.ofRootF1 …` — RL3's
  f′ = 1 closed form fired with: `g16` monic deg 16 (= the fence `2·8` EXACTLY),
  W-b's grade 170, root `1 ≠ 0` of W-c, `gcd 85 2 = 1`, and the tower's own μ₅ slopes.
* **The μ₅ slopes are `(u₅, ℓ₅) = (171, 1)`** (not a `(2·170+1, 2)` guess): C136e0's
  landed table, strict floor `1·170 = 170 < 171` — anti-drift tie landed as
  `s2Rung3_slope_is_mu5_tooth : s2Hgt₅ ((s2Rung3PackAt).pack.P.key) = 171`
  (= the landed tooth `C136e0.s2Hgt₅_g16`); the fired slopes ARE the μ₅ table's.
* `s2LiftAt3 := liftAtOfRootF1 …` (RL3's §5 wrapper) and
  `s2Rung3PackAt := s2LiftAt3.next` — ★ **the rung-3 pack at the keystone**: ring
  `fld 2` AGAIN (f′ = 1: no ring growth, exactly RL3's finding), key `g16`, grade
  `170`, slopes `(171, 1)` — all four pinned by `rfl`
  (`s2Rung3PackAt_u/ell/key/kgrade`).
* `s2_towerPacks_rung3` — **`towerPacks` fires**: any step supplier extending the S2
  lift reaches the rung-3 pack at index 1.
* Banks: `s2_rungLift3_nonempty`, `s2_rung3_pack_nonempty` — the tower side of the
  deepTwist bank inhabited at rung 3; `s2_rung3_wcoeff_mul` — ★★ the level-4→5
  weighted convolution law fires through the landed rung-3 pack.
* The **"3+"**: `s2Rung4Carrier := nextCarrier (s2Rung3Pack)` — the rung-4 CARRIER
  exists UNCONDITIONALLY (RUNG §6); the tower continues past rung 3 with no new data.

## What remains of the bank after the fire (the honest rung-4 remainder)

Exactly the rung-4 KEY LIFT, three data (the W-a/b/c analogues one level up):

1. **the μ₅ coefficient layer** (`SlotOnGrade`/`Coeff`/`GradedRes` at `(171, 1)`) —
   C136e0's DECLARED D4-13..16 gap; this is the W-c analogue's supply.  Note the W-b
   analogue's support half is CHEAPER than at rung 3: `dv4Supp` is already landed
   (C136e0), and the rung-3 carrier's `nextSupp` has the same two-step identification.
2. **the level-5 key with its exact μ₅ grade** (the tower-norm computation; at
   `(u,ℓ) = (171,1)` the f′ = 1 fence reads `deg key₅ ≤ 1·16`).
3. **the μ₆ slopes** with `ℓ₆·kg₅ < u₆` (the hfloor genre).

The generic core needs NOTHING new: `ofRootF1` fires again at `gcd 171 1 = 1` if the
μ₅ residual is linear with a nonzero root; `ofPrime` covers f′ ≥ 2.

## New statements flagged for the standing review

`s2_exact_ne`, `s2Key_key`, `s2Rung2Pack`, `s2_nextSupp_eq_dv3Supp`, `s2_nextSupp_g16`,
`s2_nextRead_g16`, `s2_eval_one_nextRead_g16`, `s2Rung2PackAt`, `s2RungLift3`,
`s2LiftAt3`, `s2Rung3PackAt` (+ 4 rfl-pins), `s2Rung3_slope_is_mu5_tooth`,
`s2_towerPacks_rung3`, `s2_rungLift3_nonempty`, `s2Rung3Pack`, `s2_rung3_pack_nonempty`,
`s2_rung3_wcoeff_mul`, `s2Rung4Carrier` — all supplier-side below the signed surface.
Local twins flagged for the standing dedup: the `wcoeff` guard pair (6th corpus
repetition), C136d2's constant-collapse pair, WCC's `s2Mu4Coeff_eq_wcoeff`.

## Verification + repair log

* Per-increment `timeout 580 ~/.elan/bin/lake env lean Uniformity/ChapI/I10RungLift3W.lean`;
  FINAL: exit 0, 0 errors, 0 warnings, `grep -c sorry` = 0; AxChk **15/15** Lean-core;
  `lake build Uniformity.ChapI.I10RungLift3W` — Build completed successfully (8858
  jobs); aggregator `Uniformity/ChapI.lean` exit 0 after the one import line.
* Repairs (4 rounds, all mechanical, zero mathematical rework): (1) missing opens
  (`C80` for `s2Tower`, `C132rp10b` for `g8`) + RL3's typed-`have` form for
  `WithTop.mul_top` (instance-path mismatch on direct rw); (2) `s2Key` name CLASH with
  `C97.s2Key` — qualified `I10wcc.s2Key` throughout; (3) `_ _`-elided `C P` at the
  guard-twin call sites left `u` a metavariable at `omega`-time — pinned explicitly;
  (4) `Polynomial.coeff_one` missing from two `simp` closes + `hgcd` needed a `show`
  through the bundled `PackAt` projections.
* Footprint: `leanfinal/Uniformity/ChapI/I10RungLift3W.lean` CREATED;
  `leanfinal/Uniformity/ChapI.lean` one import line; this verdict.  No landed file
  edited; IFCG61 untouched; no git operations.
