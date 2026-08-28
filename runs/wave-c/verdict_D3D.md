# Verdict — UNIT D3D (μ₄ stack CLOSER: D3-15..D3-19)

**Date:** 2026-08-28 · **File:** `leanfinal/Uniformity/ChapC/C136d3.lean` (new, 1935 lines)
**Build:** `lake env lean Uniformity/ChapC/C136d3.lean` exit 0, zero errors, zero `sorry`.
**Axioms:** all 69 AxCheck lines report exactly `{propext, Classical.choice, Quot.sound}` —
Lean-core, no cite, no new axiom.  No landed/leanspec file touched.

## ★★★ The campaign's μ₄ milestone (D3-19)

```
theorem Uniformity.Density.Tower.C136d3.s2Mu4_calculus_nonempty :
    Nonempty (FGMNCalculus (s2DepthThree h2 hq) 2 1 85)
```

UNCONDITIONAL, fired through `C130pk.fgmn_model_calculus_nonempty` at the D3-18 records.
This is the depth-three (μ₄) twin of the depth-two star
`C132kp6b.s2Mu3_calculus_nonempty`, and the entry requirement of the D4 (μ₅) stack.

## Per-row status

| row | status | key declarations (namespace `…Tower.C136d3`) |
|---|---|---|
| D3-15 | **LANDED** | `S2Mu4InitialEquiv/Dvd/Minimal/Irreducible/KeyPoly` (anchored to `s2Hgt₄`), equivalence + grade-transport + dvd law bank, `S2Mu4Dvd_iff_mu4NormRes_dvd` (honest monic `deg ≤ 16` nonunit-residual scope; low-degree lemmas at fence `16 = 2·deg g₈`) |
| D3-16 | **LANDED** | `s2Mu4_key_criterion` (literal field shape at recipe degree `2·1·deg(keyAt 3) = 16`), `s2Mu4_key_irreducible`, ★ `s2Mu4KeyPoly_g16` (D3-14's `g16 = g₈² − 2⁸Φ₂`, residual `X+1`) |
| D3-17 | **LANDED, converse included** | ★ `s2Mu4KeyPoly_g8` (carried key via odd-carry + slot-zero gate; residual-1 = landed `s2Mu4NormRes_key`, restated as `s2Mu4NormRes_g8`); bank: ★ `s2Mu4Minimal_natDegree_eight_dvd`, ★ `s2Mu4Minimal_exactGrade` (`μ₄ = 85·(deg/8)`), ★ `s2Mu4KeyPoly_slotZero`, `s2Mu4KeyPoly_normRes_natDegree` (`= deg/16`), `s2Mu4KeyPoly_natDegree_pin`; ★★ `s2Mu4_residual_to_initial` (the flagged converse, C132kp6b's mechanism 1-1), `s2Mu4_initial_iff_residual` |
| D3-18 | **LANDED, UNCONDITIONAL** | `s2SourceDataThree : FGMNSourceData (s2DepthThree) (s2DepthThreeKeyChain) 2 1 85` + 7 rfl read pins; ★★ `s2SourceLawsThree` — all THIRTEEN laws with NO carried hypotheses (unlike depth-2's `s2SourceLawsTwo_of`: μ₄ `hex` was already landed at D3-14, the converse landed here at D3-17); recipe field discharged by `s2Mu4_recipe_grade_eighty_five_vacuous` (odd grade 85 impossible below degree 8 — the RP-9 parity defect, one level up, recorded not hidden); letter `s2LetterThree` = forced constant 1, depth-3 typed |
| D3-19 | **LANDED** | ★★★ `s2Mu4_calculus_nonempty` (above); `s2DepthFourKeyAt` with `keyAt 4 = g16` (`s2DepthFourKeyAt_four`), ★★ `s2DepthFourKeyChain : KeyChain (s2DepthFour h2 hq)` (`Φ′/Φ₂/g₈/g16`, degrees `2/4/8/16 = Dcum`); T5's deferred half COMPLETED: `s2Mu5_chainNormBelow_four_one_seventy_one_chain` — the chain-level `hkey : I.keyAt = (s2DepthFourKeyChain).keyAt` restatement of `chainNormBelow 4 171 = s2Mu5Lambda = 2·x·Φ′·Φ₂·g₈` |

## The one genuinely new ledger (D3-17's divisibility pin)

The kp6b refuter `g₈^(m+1) /ₘ g` needs SEVEN inner cleared μ₃ bounds for monic digits of
degree `1..7` (vs three at μ₃): `c′₁..c′₇ = 4, 10, 14, 21, 25, 31, 35`
(`c′_{4a+b} = 2·c_b + 21a` over the kp6b μ₂ bounds `c₁,c₂,c₃ = 2,5,7`, with `c′₄ = 21`
from the trivial top digit).  Worst residue pair is `r = 4`: `2·(21+21) = 84 < 85` —
tight against the T3 floor, exactly as `r = 2` was tight (`20 < 21`) one level down.
These live as privates `dv2Supp_le_of_monic_deg1'..deg7'` +
`dev_g8_top_monic`/`dv3Pin_top_of_monic_mul_eight`/`slot_top_of_monic_mul_eight`.

## Deviations from the models (all recorded in docstrings)

* `s2SourceLawsThree` is unconditional (the fd0 model carried `hex`/`hconv`); the
  `set_option maxHeartbeats 1600000 in` precedent is kept on the record.
* kp6b's file-local copies of kp4's privates are unnecessary here — one file, shared
  privates (`mu4_initialEquiv_iff_gradedRes`, `mu4Coeff_ne_zero_of_slot`,
  `mu4Dvd_g8_of_not_slotZero` serve both the carried-key proof and the bank).
* The slot-1 digit-bound engine `dv2Supp_le_of_monic_deg4b'` drops the unused degree
  fences (they live in the top-digit bound argument itself).
* Two compile repairs total across ten increments: (i) implicit-`b` in the deg4b'
  helper (made the numeral explicit), (ii) `(i := k)` pins on `s2DepthFourKeyAt_of_le`
  in the T5 restatement (`by omega` elaborated before the index metavariable was
  pinned).  Everything else landed first-pass against the μ₃ models.

## Downstream unlocked

D4-00 (`keyAt4` support shell) and the whole μ₅ stack (`s2DepthFourKeyChain` + grade
`171` rows); C0/C1/R5's depth-three calculus consumers (`s2Mu4_calculus_nonempty` is the
literal `Nonempty` they project); T5 row closed on the C136t side (both recorded halves).
