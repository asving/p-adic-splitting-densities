# Verdict — node M3-RP3: the μ₃ graded ADD law (zero law was already discharged)

Date: 2026-08-27 · Unit MRP3 (Sonnet transcription tier) ·
`docs/in-progress/MU3_CAMPAIGN_2026-08-26.md` §6, row M3-RP3 · REUSE-WITH-NUMERALS
(mechanical port, no invention needed) · Deliverable: `leanfinal/Uniformity/ChapC/C132rp3.lean`
(276 lines, node tag `[M3-RP3, 2026-08-27]`).

## Finding first: `graded_zero_of_above` was ALREADY landed, at M3-RP2

The row's sketch names two obligations. Checking C132rp2 (landed by the sibling MRP2 unit,
verdict `verdict_MRP2.md`) before writing any new code showed the FIRST — the polynomial-level
zero-above law — was already discharged there as `s2Mu3GradedRes_zero_of_above`, because
M3-RP1's own division of labor put the coefficient-level `s2Mu3Coeff_eq_zero_of_above` among
RP-2's landed inputs. Re-proving it here would be a byte-identical duplicate. This node instead
adds an explicit **shape pin** confirming `s2Mu3GradedRes_zero_of_above` has EXACTLY the
`FGMNSourceLaws.graded_zero_of_above` field type (`C130fg.lean:198-199`) at the μ₃ occurrence,
and spends its budget on the genuinely open obligation: the μ₃ analogue of published
Corollary 4.12(1) (graded additivity).

## What landed

A mechanical port of the μ₂ ADD-law engine (`C130rp2.lean:168-183` the slot-floor bridge,
`:440-510` the `graded_add` assembly) one recursion layer up, against `s2Mu3Coeff`
(C132rp1) and `s2Mu3GradedRes` (C132rp2):

* `le_dv2Pin_of_le_dv2Supp` (+ private `dv2Supp_le_term`) — the level-2 slot floor from a
  cleared-support floor, mirroring `C130rp2.le_dvHgt_of_le_dvSupp` one level up against
  `dv2Pin`/`dv2Supp` (C.11) instead of `dvHgt`/`dvSupp` (C.06/C.07). Kept generic in `(u₂,
  ℓ₂)` — as `C130nv2.weight_read` is — rather than hardcoding `(21, 2)`, to avoid a
  `Nat.cast`-vs-`OfNat`-numeral mismatch inside the proof (caught by the compiler on the
  first attempt: instantiating the numerals before the `weight_read` rewrite makes the
  pattern fail to unify; instantiating only at the call site, as the μ₂ original does,
  fixes it).
* `s2Mu3Coeff_eq_eval_of_le` — the coefficient floor bridge, mirroring
  `C130rp2.s2GradedCoeff_eq_twistRead_of_le`: ON the gate, `s2Mu3Coeff` reads the landed μ₂
  operator `s2GradedRes` at the true inner grade `m` (`s2Mu3Coeff_eq_eval`); STRICTLY ABOVE
  it, the gate is false AND the SAME landed μ₂ read vanishes there
  (`s2GradedRes_zero_of_above`, C130rp1) — both cases display the identical formula. This is
  the one genuinely new step: at μ₂ the off-gate vanishing came from a frame-level
  `twistRead_eq_zero_of_lt` fact; here there is no frame read at this recursive layer, so the
  off-gate case reads through the μ₂ operator's OWN zero-above law instead.
* `s2Mu3Coeff_add` — the coefficientwise ADD law (strong form, mirror of
  `C130rp2.s2GradedCoeff_add`): on a common `dv2Supp`-floor, cancellation slots (both
  summands on-line, the sum strictly above) are absorbed via `dev` additivity (B32a) plus
  the μ₂ operator's OWN landed add law `s2GradedRes_add_of_le` (C130rp2) at the shared inner
  grade — never re-split by hand.
* `s2Mu3GradedRes_add_of_le` / `s2Mu3GradedRes_add` — the polynomial lift (mirror of
  `C130rp2.s2GradedRes_add_of_le` / `.s2GradedRes_add`): the strong `dv2Supp`-floor form, and
  the `FGMNSourceLaws.graded_add` field-shape form (published Cor 4.12(1)) at the μ₃
  occurrence, by `Polynomial.ext` against the master coefficient law `s2Mu3GradedRes_coeff`.
* two `example` shape pins: one confirming `s2Mu3GradedRes_add`'s field-shape fit, one
  re-confirming `s2Mu3GradedRes_zero_of_above`'s (the honesty note above, made checkable).

Five named theorems (plus the private helper and the two unnamed shape-pin examples), all
`#print axioms`-checked.

## BLOCKED-BECAUSE ledger

None. Every step in the μ₂ ADD-law bank ported; the only non-literal step (reading the
off-gate vanishing through `s2GradedRes_zero_of_above` instead of a frame-level `twistRead`
fact) is forced by the recursive structure of `s2Mu3Coeff`, not a new mathematical idea —
it is the SAME landed μ₂ zero-above law C132rp2 already consumed one level up.

## Build verification

`C132rp2`'s `.olean` did not yet exist in the build cache; built it via the scoped target
`lake build Uniformity.ChapC.C132rp2` (8785/8785 jobs, Lean-core-only footprint on all seven
declarations). Then, from `leanfinal/`:

```
lake env lean Uniformity/ChapC/C132rp3.lean
```

Exit 0. Zero errors, zero warnings, zero `sorry`. Also confirmed via the scoped project
target `lake build Uniformity.ChapC.C132rp3` (8786/8786 jobs, succeeded). Every declaration
prints exactly `[propext, Classical.choice, Quot.sound]` (Lean core only, no new axiom):

```
'Uniformity.Density.Tower.C132rp3.le_dv2Pin_of_le_dv2Supp' depends on axioms: [propext, Classical.choice, Quot.sound]
'Uniformity.Density.Tower.C132rp3.s2Mu3Coeff_eq_eval_of_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'Uniformity.Density.Tower.C132rp3.s2Mu3Coeff_add' depends on axioms: [propext, Classical.choice, Quot.sound]
'Uniformity.Density.Tower.C132rp3.s2Mu3GradedRes_add_of_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'Uniformity.Density.Tower.C132rp3.s2Mu3GradedRes_add' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Scope discipline

No roll-up, leanspec, or other existing file touched. `C132rp4.lean` untouched (sibling
node). `grep -n "C132rp3"` across the tree finds only the new file itself — nothing else
imports it yet, as expected for a leaf just landed. No commit made.
