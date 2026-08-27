# Verdict MSG2 — node M3-SG2: the μ₃ consumer wiring (`gentow5w_two` at `(2,1,21)`)

**Date:** 2026-08-27
**Unit:** MSG2 (Fable) — μ₃ campaign finale, blueprint row M3-SG second half + §7 wiring row
(`docs/in-progress/MU3_CAMPAIGN_2026-08-26.md`).
**Landed file:** `leanfinal/Uniformity/ChapC/C132sg2.lean` (first-attempt green,
`lake env lean` exit 0; sorry-free; no new axiom; no existing file touched).

## Disposition

| deliverable | status |
|---|---|
| Package the μ₃ calculus | **LANDED** — `s2Mu3Calculus` (§7's endpoint def verbatim at the landed names: `fgmnCalculusOf` + `s2SourceDataTwo` + `s2SourceLawsTwo_of` fired by KP6b's `s2Mu3_hconv` and RP10b's `s2Mu3_hex`); `s2_mu3_calculus_discharge` = exit gate 3's literal type through `fgmn_model_calculus_nonempty`; six anti-drift `rfl` pins (keyAt/ExactGrade/PrevGrade/Rres/KP/nuEquiv). |
| Scoped/local instance | **LANDED per §7's own prescription** — deliberately a `def` (C130pk's no-silent-instance rule); the local `letI` exposure is enacted inside `s2Mu3_gentow2_A_supply`. |
| Amended `gentow5w_two` at `(2,1,21)` | **CONDITIONAL LANDING, 7 of 8 legs discharged** — `gentow5w_two_at_mu3_of_norm` (general instance w/ canonical-chain pin) and `s2Mu3_gentow5w_two_of_norm` (the packaged instance; conclusion = the SIGNED `GENTOW5W (s2DepthTwo h2 hq) 2 1 21 (s2Mu3Calculus h2 hq)`). Discharged: `he'`, `hf'`, `hcop` (decide), `hfloor` (machine `20 < 21` via `s2Bridge_Econst`+`s2Tower_data`), `hprev` (A-C.17 fence VACUOUS at `f' = 1`), `hnormdeg`+`hnormz` (M3-FD1's supplies at `hkey := rfl`). Carried: `hnorm` only. |
| `hnorm` | **BLOCKED-BECAUSE, REFUTED** — `s2Mu3_gentow5w_two_hnorm_refuted`: the carried hypothesis is FALSE at the μ₃ instance (M3-FD1's certificate through the `rfl` grade pin: `chainNormBelow 2 21 = 16Φ′` has degree `2 < 4`, hence EVEN μ₃ grade by C132rp9, but the requested grade `21` is odd). Campaign exit gate 4 cannot close as written; the A-C.17/A-C.18 `hnorm` family needs a grade re-target in the next A-C amendment round. Nothing weakened, nothing invented. |
| `gentow2_A_supply` exposure | **HONEST PARTIAL** — `s2Mu3_gentow2_A_supply`: packaging discharges the instance (`letI`), `hkey` (`rfl`: `keyAt 2 = composedKey (s2Tower)`), `hκ` (`2·1·5 = 10 < 21`), `he'`/`hf'`/`hcop`, `hh`, `hπ := h2`. NOT landed anywhere (checked; the campaign's OPEN-A-SUPPLY row): `ρ : fld 2 ≃+* AdjoinRoot ψ₂` (OPEN-EVAL-ISO/OPEN-DICT-3-MU3), the digit string `c` (`c 0 ≠ 0`), `hliftdeg` (`deg (k2DigitLift T (c 0) 21) < D₂ = 4`), `hadm` (recipe-residual admissibility). These remain explicit binders. |

## AxChk footer (`lake env lean Uniformity/ChapC/C132sg2.lean`, exit 0)

Every declaration is Lean-core — `[propext, Classical.choice, Quot.sound]`:

```text
s2Mu3Calculus · s2_mu3_calculus_discharge · s2Mu3Calculus_keyAt ·
s2Mu3Calculus_ExactGrade · s2Mu3Calculus_PrevGrade · s2Mu3Calculus_Rres ·
s2Mu3Calculus_KP · s2Mu3Calculus_nuEquiv · gentow5w_two_at_mu3_of_norm ·
s2Mu3_gentow5w_two_of_norm · s2Mu3_gentow5w_two_hnorm_refuted ·
s2Mu3_gentow2_A_supply
```

**Cite note:** NO footprint here carries the declared cite `fgmn_dv_exact_mul` — the μ₃
construction chain (C132nv/rp/kp/fd) and the GENTOW consumer chain (C99r/C107gt5/C107ac14)
are both Lean-core; that cite lives on the separate dv-engine chain (C.52/C.54), untouched.

## Builds run

- `lake build Uniformity.ChapC.C132kp6b` — green (8807 jobs; the freshly landed star).
- `lake build Uniformity.ChapC.C132fd1 Uniformity.ChapC.C107ac14` — green (8800 jobs).
- `lake env lean Uniformity/ChapC/C132sg2.lean` — exit 0, the 12 footprints above, no
  warnings.

No commit made (per charge); leanspec/roll-ups untouched.
