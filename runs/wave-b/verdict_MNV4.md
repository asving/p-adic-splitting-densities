# Verdict — unit MNV4, node M3-NV4 (μ₃ campaign, `s2Hgt₃` product law) — LANDED

Date: 2026-08-27. File created (the ONLY repo file touched, besides this verdict):
`leanfinal/Uniformity/ChapC/C132nv4.lean` (node tag `[M3-NV4, 2026-08-27]`; 7 public
theorems, 197 lines). Not added to any roll-up/leanspec file. No git commit.

## The charge

Assemble `s2Hgt₃ (g·h) = s2Hgt₃ g + s2Hgt₃ h` (`docs/in-progress/MU3_CAMPAIGN_2026-08-26.md`
§6, row M3-NV4), including the zero cases and the endpoint-minimizer corollaries, at the S2
instance `L = (s2Tower h2 hq).levelDatum h2`, `Φ₂ = s2DepthTwoKeyAt h2 hq 2`, OUTER pair
`(u₂,ℓ₂) = (21,2)`. The hard mathematics was already machine-pinned in
`leanfinal/scratch/MADJ_probe.lean` (green): C132nv3b's two landed `Dv2ResSurv` clauses
(both closing at `(21,2)`, unlike the BLOCKED `(5,2)` inner read) assemble into the survival
package, which fires C132nv2's "NV-4 consumption shape" endpoint theorem through to exactly
the carrier conclusion. This node's job was to transcribe the probe into a production file
plus supply the row's remaining items (zero cases, minimizer corollaries) that the probe did
not cover.

## Verdict: LANDED

**Precision honored** (per `runs/wave-b/verdict_MADJ.md`): the outer pair is `(21,2)`
everywhere in the new file; nothing is stated at `(5,2)` (that numeral lives one layer down,
inside `dv2Hgt L`, and is never conflated with the outer `(u₂,ℓ₂)` here).

**What lands** (`C132nv4.lean`):

* `s2_dv2ResSurv_at_21` — the survival package `Dv2ResSurv L Φ₂ 21 2`, UNCONDITIONAL,
  transcribed verbatim from the probe's `s2_dv2ResSurv_at_21` (built from C132nv3b's
  `dv2Hgt_dev_composedKey_mod_eq` + `s2_dv2ResSurv_slot1_at_21`).
* `s2_dv2Supp_mul_at_21` — the endpoint product law for the raw `dv2Supp` table (probe's
  `nv4_endpoint_fires_at_21`, renamed for the production naming convention), firing
  C132nv2's `dv2Supp_mul_eq_add_of_endpoint_le` through the survival package.
* `s2Hgt₃_mul` — **the row's advertised statement**: `s2Hgt₃ (g·z) = s2Hgt₃ g + s2Hgt₃ z`
  (probe's `nv4_value_fires_at_21`, renamed to match the `s2Hgt₂_mul`/`s2Hgt₁_mul` naming
  precedent), read off `s2_dv2Supp_mul_at_21` through `toZ_add`.
* `s2Hgt₃_zero_mul` / `s2Hgt₃_mul_zero` — **the zero cases** (NOT in the probe; new for this
  node). Proved DIRECTLY from `s2Hgt₃_zero` + `WithTop`'s `⊤`-absorbing addition
  (`top_add`/`add_top`), not via `s2Hgt₃_mul`: a zero factor has an empty `dv2SideSet`
  (`dv2Pin` of `0` is always `⊤`, so `Dv2OnSide` never holds), so the conditional product
  law above literally does not reach the zero corner — this is a genuinely separate
  obligation, matching the `C130nv.s2Hgt₁_zero_mul` precedent's role one level down (though
  there it followed for free from an UNCONDITIONAL product law; here it cannot, honestly,
  since NV4's law keeps the side-set hypotheses).
* `s2_dv2OnSide_mul_endpoint_at_21` / `s2_dv2SideMin_mul_le_at_21` — **the endpoint-minimizer
  corollaries** (NOT in the probe; new for this node), mirroring the old S2 level-two
  assembly shape (`C130nv3.lean:557-582`, `s2_dvOnSide_mul_endpoint`/`s2_dvSideMin_mul_le`):
  C132nv2's generic `dv2OnSide_mul_endpoint`/`dv2SideMin_mul_le` fired at `Φ₂`, `(21,2)`,
  through the same survival package and the same monic/degree/positivity numerals used
  throughout this file.

## What was NOT claimed (honesty scope)

No UNCONDITIONAL (all-`g,z`) product law for `s2Hgt₃`. Per the orchestrator's brief,
`s2_dv2Supp_mul_at_21`/`s2Hgt₃_mul`/the two minimizer corollaries keep the probe's
hypotheses EXACTLY as stated (`hng`, `hnz` — side-set nonemptiness — and `hHg`, `hHz` —
finite pins at the chosen minimizer); no `dv2SideSet_nonempty`-style unconditional existence
fact is derived here — deriving one was explicitly out of scope for this node. Nothing at
`(5,2)` is stated anywhere in the file. No new axiom; no statement invented beyond the row's
sketch and the probe's machine pin.

**Flagged for human review** (parent CLAUDE.md trust boundary — new statements):
`s2_dv2ResSurv_at_21`, `s2_dv2Supp_mul_at_21`, `s2Hgt₃_mul`, `s2Hgt₃_zero_mul`,
`s2Hgt₃_mul_zero`, `s2_dv2OnSide_mul_endpoint_at_21`, `s2_dv2SideMin_mul_le_at_21`.

## Verification

`cd leanfinal && lake env lean Uniformity/ChapC/C132nv4.lean` — CLEAN (exit 0, no errors, no
warnings; `grep -c sorry` on the file returns `0`). `#print axioms` on all 7 public
declarations:

```
'Uniformity.Density.Tower.C132nv4.s2_dv2ResSurv_at_21' depends on axioms: [propext, Classical.choice, Quot.sound]
'Uniformity.Density.Tower.C132nv4.s2_dv2Supp_mul_at_21' depends on axioms: [propext, Classical.choice, Quot.sound]
'Uniformity.Density.Tower.C132nv4.s2Hgt₃_mul' depends on axioms: [propext, Classical.choice, Quot.sound]
'Uniformity.Density.Tower.C132nv4.s2Hgt₃_zero_mul' depends on axioms: [propext, Classical.choice, Quot.sound]
'Uniformity.Density.Tower.C132nv4.s2Hgt₃_mul_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'Uniformity.Density.Tower.C132nv4.s2_dv2OnSide_mul_endpoint_at_21' depends on axioms: [propext, Classical.choice, Quot.sound]
'Uniformity.Density.Tower.C132nv4.s2_dv2SideMin_mul_le_at_21' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Lean-core only, uniformly. No axiom regression possible (no capstone touches this file yet).
`git status` shows only the new `C132nv4.lean` plus this verdict file. No roll-up/leanspec
file touched. No git commit.
