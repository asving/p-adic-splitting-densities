# Verdict — unit MRP0: μ₃ campaign node M3-RP0 (grades)

Date: 2026-08-27 · Plan: `docs/in-progress/MU3_CAMPAIGN_2026-08-26.md` §6, row M3-RP0
"grades" (deps: μ₂ `S2ExactGrade` bank `C130rp0.lean:115-248`, M3-NV4/NV5→NV6). File
created (the ONLY file touched): `leanfinal/Uniformity/ChapC/C132rp0.lean` (14 public
declarations; not added to `Uniformity/ChapC.lean` or any roll-up).

## M3-RP0 (grades) — LANDED, pure REUSE-WITH-NUMERALS, no BLOCKED-BECAUSE

Mechanical port of the μ₂ `S2ExactGrade`/`S2AboveGrade` bank to the μ₃ value table
`s2Hgt₃` (C132nv1) and its now-genuinely-unconditional product law `s2Hgt₃_mul_all` /
`AddValuation` packaging `s2AddVal₃` (C132nv6, landed same day). Landed:
`S2Mu3ExactGrade`/`S2Mu3AboveGrade` (free-standing `Prop`s, `nextValue := s2Hgt₃ h2 hq`,
no `FGMNSourceData` instance built); the exact-/above-membership normal forms against the
raw `dv2Supp` table (`S2Mu3ExactGrade_iff_dv2Supp`/`S2Mu3AboveGrade_iff_dv2Supp`); grade
existence (`S2Mu3ExactGrade_exists`, via `dv2Supp_ne_top_of_ne_zero` + `s2Φ₂_monic`/
`s2Φ₂_natDegree`) and uniqueness (`S2Mu3ExactGrade_unique`); ★ the grade arithmetic
`S2Mu3ExactGrade_mul` — UNCONDITIONAL, no side-set/pin fence at all, since the input
`s2Hgt₃_mul_all` is already the fully unconditional `∀ x y` law (a strictly easier port
than μ₂, whose `S2ExactGrade_mul` was also unconditional but off a same-shape
`s2Hgt₂_mul`) — plus `S2Mu3ExactGrade_not_above`; the zero/⊤ edge cases
(`S2Mu3ExactGrade_not_zero`/`_zero_false`, `S2Mu3AboveGrade_zero`) off `s2Hgt₃_zero`; the
`AddValuation` tie (`S2Mu3ExactGrade_eq_addVal`/`S2Mu3AboveGrade_eq_addVal` against
`s2AddVal₃`); one numeral tooth `tooth_Φ₂ : S2Mu3ExactGrade 21 Φ₂`, re-reading nv1's
`s2Hgt₃_Φ₂`. Every law in the μ₂ bank ported directly — no law was dropped or blocked.

The generic value-group arithmetic `toZ_lt_toZ_iff`/`S2Grade_natCast_add` (C130rp0) was
REUSED verbatim via `import`/`open`, not re-derived: neither statement mentions μ₂ or any
S2 numeral, so a byte-copy would have been pure duplication.

## One recorded trap (same one hit at μ₂'s RP-0, per `verdict_RP0.md`)

Docstring text "exact-/above-membership" contains the literal substring `-/`, which
closes the enclosing Lean block comment early and cascades into unrelated parse errors
(`s2Tower` "unknown identifier", etc. downstream). Reworded to "exact- and
above-membership" — the exact same fix `verdict_RP0.md` already recorded for the μ₂
transcription. Separately needed one open missing from the mechanical copy:
`open Uniformity.Density.Tower.C80` (for `s2Tower`), not required by C130rp0's own file
since C130rp0 reads `s2Frame`/`s2Hgt₂` rather than `s2Tower`/`dv2Supp` directly.

## What was deliberately NOT claimed

No `gradedResidual`/`Rgr`/`normalizedResidual`/`Rres` scalar or polynomial content
(RP-1-analogue onward); no `FGMNSourceData`/`FGMNSourceLaws`/`ChainRealization` instance
(FD-0-analogue territory, out of scope here).

## Verification

`cd leanfinal && lake env lean Uniformity/ChapC/C132rp0.lean` — CLEAN (0 errors, 0
warnings beyond the pre-existing title-line `longLine` info also present on sibling files
C132nv4/C132nv6, 0 sorry). `lake build Uniformity.ChapC.C132rp0` — success (8783 jobs,
after first building the not-yet-compiled `C132nv6` dependency, also green, 6.3s). 14
`#print axioms` rows, ALL `[propext, Classical.choice, Quot.sound]` (Lean-core only); no
new axiom, no `unsafe`. No roll-up/leanspec/existing file touched. No git commit (per
brief).
