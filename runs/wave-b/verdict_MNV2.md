# Verdict — unit MNV2, node M3-NV2 (`docs/in-progress/MU3_CAMPAIGN_2026-08-26.md` §6)

**File delivered:** `leanfinal/Uniformity/ChapC/C132nv2.lean` (new; only file written by this
unit besides this verdict). Builds clean: `cd leanfinal && lake env lean
Uniformity/ChapC/C132nv2.lean` exits 0 — zero errors, zero `sorry`, zero new `axiom`. (One
benign lint fix applied mid-build: `push_neg` → `push Not`, per house style.)

## What landed

Ported the parameter-free endpoint/minimizer bank (C.07 + `C130nv2`'s Part 1) and the
convolution-pricing bank (`C130nv2.lean:475-784`'s term estimates + endpoint assembly, in the
spirit of the "generic once one supplies survival" pattern at `C130nv3.lean:153-210`) from
`dvSupp`/`F.key` to `dv2Supp`/`Ψ` (C.11's level-2 recursion), leaving ONE explicit hypothesis,
`Dv2ResSurv`.

* **Part 0** — two free shims (`dv2Hgt_zero`, `min_dv2Hgt_le_dv2Hgt_add`, `dv2Hgt_add_eq`):
  `dv2Hgt`'s zero and ultrametric-add/equality-off-ties laws, read straight off `dv2Hgt L A :=
  dvSupp F A L.u L.ℓ` and the already-landed level-1 bank (C130s6) — no proof beyond unfolding.
* **Part 1** — `Dv2OnSide`/`dv2SideSet`/`dv2SideMin` (mirror of C.07) and their basic reads
  (`dv2OnSide_dv2SideMin`, `dv2SideMin_le_of_dv2OnSide`, `dv2OnSide_endpoint_unique`,
  `dv2Supp_eq_of_dv2OnSide`, `dv2Supp_le_term`, `le_dv2Weight`, `lt_dv2Weight`) — pure
  combinatorics, the only height fact consumed is C132nv0's `dv2Pin_top_of_gt`.
* **Part 2** — `Dv2ResSurv L Ψ u₂ ℓ₂` (the one hypothesis, defined as a `Prop`, never an
  axiom): for `Ψ`-digit-bounded `A, B` (degree `< Ψ.natDegree` — every `dev Ψ` output
  UNCONDITIONALLY, B03's `degree_dev_lt`) of known `dv2Hgt` heights, the product's `Ψ`-reduced
  value (slot `0`) is EXACTLY `Ha + Hb`, and the carry (slot `1`) value is bounded STRICTLY
  above the line. `natDegree_dev2_mul_lt`, `le_line_dev2_term`, `lt_line_dev2_term` (the
  convolution pricing bank), and `dv2Supp_add_le_dv2Supp_mul` (the universal `≥` product law)
  are assembled from it, mirroring `C130nv2.lean`'s Parts 4/5 term-for-term.
* **Part 3** — the endpoint/minimizer assembly (mirror of `C130nv2.lean:641-784`):
  `dv2SideMin_le_natDegree`, the private `dv2_endpoint_dev_le` (derives the endpoint's own
  survival directly from `Dv2ResSurv`'s first clause — no separate `hup` hypothesis needed,
  unlike the level-1 original, since `Dv2ResSurv` already supplies it), and the four public
  consumer theorems `dv2Supp_mul_of_endpoint_le`, `dv2OnSide_mul_endpoint`,
  `dv2SideMin_mul_le`, `dv2Supp_mul_eq_add_of_endpoint_le` — each closing on `Dv2ResSurv`
  alone.

## Why one hypothesis, and why this shape (flagged for owner review)

`dv2Hgt L A := dvSupp F A L.u L.ℓ` (C.11) is a level-1 SUPPORT (an `inf`), not a valuation:
unlike `F.stageHeight` (multiplicative from `X`'s primality — `stageHeight_mul`,
`C130nv2.lean:203`), `dvSupp` is only "≥"-multiplicative unconditionally and exactly
multiplicative conditional on its own endpoint survival — precisely the NV0–NV4 story one
level down. The level-1 "one-step MacLane expansion" (`stageHeight_le_modByMonic` et al.,
`C130nv2.lean:296-468`) is proved from `X`'s degree bookkeeping and has no level-2 analogue for
`dv2Hgt`+`Ψ`. `Dv2ResSurv` packages exactly the two facts the pricing bank needs about a digit
PRODUCT's own `Ψ`-development (its only two possible slots, since a digit product has degree
`< 2·deg Ψ`) — this is the campaign's own diagnosis (§5: "survival must be proved from the
landed μ₂ normalized residual product, not copied from the parity proof"), assigned to the
separate node M3-NV3. Everything else in this file is UNCONDITIONAL and parameter-free (no S2
numeral, no concrete `u₂`/`ℓ₂`, no `Ψ = Φ₂` anywhere).

**This is a judgment call about the hypothesis's exact statement shape** (not dictated
verbatim by the blueprint row, which names the fact informally). The full derivation is
recorded in the file's own docstring. Flagged for a fresh-eyes pass to confirm `Dv2ResSurv`'s
shape is what M3-NV3 can actually discharge for `Ψ = Φ₂`, degree-`<4` coefficients, from
`s2NormRes_mul`.

## Scope discipline

Plumbing-adjustment port only, per the row's binding spec — no new axiom, no statement
weakened to become provable, no roll-up/leanspec file touched, `C132nv3.lean` (sibling) not
touched. Imports only `C130nv2` (for `weight_read`/`succ_le_of_weight_succ_le`, pure `ℕ∞`
arithmetic, no frame dependence) plus the two required chain-head files `C132nv0`/`C132nv1`.
No commit taken.

## `#print axioms` (AxCheck footer, `lake env lean` run 2026-08-27)

All 26 declarations in `Uniformity.Density.Tower.C132nv2` — `dv2Hgt_zero`,
`min_dv2Hgt_le_dv2Hgt_add`, `dv2Hgt_add_eq`, `Dv2OnSide`, `dv2SideSet`, `dv2SideMin`,
`dv2OnSide_of_mem_dv2SideSet`, `mem_dv2SideSet_of_dv2OnSide`, `dv2OnSide_dv2SideMin`,
`dv2SideMin_le_of_dv2OnSide`, `not_dv2OnSide_of_lt_dv2SideMin`, `dv2OnSide_endpoint_unique`,
`exists_dv2SideMin_height`, `dv2Supp_eq_of_dv2OnSide`, `dv2Supp_le_term`, `le_dv2Weight`,
`lt_dv2Weight`, `Dv2ResSurv`, `natDegree_dev2_mul_lt`, `le_line_dev2_term`,
`lt_line_dev2_term`, `dv2Supp_add_le_dv2Supp_mul`, `dv2SideMin_le_natDegree`,
`dv2Supp_mul_of_endpoint_le`, `dv2OnSide_mul_endpoint`, `dv2SideMin_mul_le`,
`dv2Supp_mul_eq_add_of_endpoint_le` — print:

```
propext, Classical.choice, Quot.sound
```

Lean-core only, uniformly. No axiom regression possible (no capstone touches this file yet).
