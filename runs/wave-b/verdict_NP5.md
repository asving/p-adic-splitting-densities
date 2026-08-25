# Unit NP5 verdict — S2-source plan node NP-5 (the window)

## Verdict: LANDED (level 2, complete), level 1 honestly split (finiteness landed, strict
half BLOCKED — confirms, does not create, NP-4's gap)

New file `leanfinal/Uniformity/ChapC/C130np5.lean` (imports `C130np0`, `C130np4`, `C53b`).
Sorry-free, no new axiom, no `unsafe`; all 22 `#print axioms` lines are Lean core
(`propext, Classical.choice, Quot.sound`) only. No `NodePointSource` instance is constructed,
named, or claimed anywhere in the file.

## The 5-vs-10 resolution (computed, not chosen)

Computed `d(Φ₂(ρ)) = pointHgt 2 x (keyAt 2)` from scratch, via C.47's three already-landed
composed-key clauses (`composedKey_top_digit`, `composedKey_offLattice_digit`,
`composedKey_slot_height`) plus `dev_eq_zero_of_lt` beyond the degree: the `Φ′`-development of
`Φ₂ = composedKey (s2Tower h2 hq)` has height `5` at slot `0`, `⊤` at slot `1` (off the
`e₂ = 2`-lattice), `0` at slot `2` (top digit), `⊤` beyond `natDegree = 4`. Folding into
`dvSupp`'s `(u,ℓ) = (5,2)` inf gives `min(2·5+0, 2·0+10) = 10` exactly
(`s2Hgt₂_composedKey_s2Tower`), independently cross-checked against C.42's separately-landed
`TowerDatum.E₂ = 10` (`s2NPPointHgt_keyAt_two_eq_E₂`) — two routes, same numeral. **Resolution:
`seam = 5` WORKS (`seam_lt_pointHgt_two`: `5 < 10`); `ℓ·seam = 10` FAILS (teeth,
`not_ellSeam_lt_pointHgt_two`: it equals `d(Φ₂(ρ))`, not strictly below it).** Expected Montes
shape: a key sits exactly on the boundary of its own disk, so its self-height under its own
valuation equals the cleared companion of the admitting threshold, not the threshold itself.

## What is proved

* `s2_window_at_two` — the level-2 `window` field in its exact shape, `thresholdZ 2 := seam`
  (NP-4's own numeral, tied through `seam_s2Tower_intCast`; no numeral invented here).
* `s2_window_finiteness_at_one` — the level-1 `window` field's finiteness half, exact shape
  (re-exposed from NP-0's `s2NP_window_ne_top`).
* `level_one_threshold_lt_five` — the honest necessary constraint at level 1: any future
  source-backed `thresholdZ 1` must satisfy `T < 5` (since `d(Φ₁(ρ)) = u₂ = 5`, NP-0's
  `key_value`). Teeth `not_seam_lt_pointHgt_one` / `not_ellSeam_lt_pointHgt_one` confirm
  NEITHER of NP-4's two avatars (`5`, `10`) can serve at level 1 either — independently
  reconfirming, not inventing around, NP-4's "no source occurrence" finding for level 1.

## Level 1: honest gap, not a new blocker

NP-4 searched `spec/EFF-T2*.md`, `spec/EFF-GENTOW5*.md`, `spec/EFF-GENHN*.md` and found no
source occurrence naming a level-1 threshold (level 1 is the base `KeyFrame`, no prior
`LevelDatum` to derive one from). This node checked whether NP-4's own two computed numerals
could fill the gap regardless of labelling convention — they cannot (`5 ≮ 5`, `10 ≮ 5`) — and
otherwise did not attempt to invent a numeral, per the plan's explicit rule. The strict half of
level 1's window stays BLOCKED, pending a genuine source occurrence for `T₁`, exactly as NP-4
left it.

## Verification

`lake build Uniformity.ChapC.C130np0 Uniformity.ChapC.C130np4 Uniformity.ChapC.C53b` then
`lake env lean Uniformity/ChapC/C130np5.lean` from `leanfinal/` — exit 0, zero errors, zero
warnings, zero `sorry`. `lake build Uniformity.ChapC.C130np5` — success (8757 jobs). `git
status`: only `C130np5.lean` added by this unit; `C130np7.lean`/`C130rp2.lean` are other
in-flight units' files, untouched. No commit (per brief).
