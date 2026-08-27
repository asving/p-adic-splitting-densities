# VERDICT — unit MRP8 (node M3-RP8: μ₃ normalized residual)

**Status: LANDED — Lean check green, zero `sorry`, zero new axiom.**

Node M3-RP8 of `docs/in-progress/MU3_CAMPAIGN_2026-08-26.md` §6 landed in
`leanfinal/Uniformity/ChapC/C132rp8.lean` with tag **[M3-RP8, 2026-08-27]**.

## Landed content

- `s2Mu3GradeOf`, with exact-grade extraction and witness-independence.
- `s2Mu3NormRes`, its exact-grade form, coefficient shift, zero law, and reconstruction law.
- `s2Mu3GradedRes_ne_zero_of_exact`: the arbitrary-degree nonvanishing bridge needed by the
  strip and trailing-order arguments.  It uses an attained μ₃ slot; its development digit has
  degree `< 4`, where the landed μ₂ scalar law applies.
- `s2Mu3NormRes_coeff_zero_ne_zero` and `s2Mu3NormRes_ne_zero`.
- `s2Mu3GradedRes_natTrailingDegree_mul`, including the odd-by-odd carry.
- `s2Mu3NormRes_mul_of_exact` and the universal, zero-inclusive `s2Mu3NormRes_mul`.
- Exact, graded, and normalized key-power values:
  `S2Mu3ExactGrade_key_pow`, `s2Mu3GradedRes_key_pow`, and `s2Mu3NormRes_key_pow`, with the
  base/key pins `s2Mu3GradedRes_one`, `s2Mu3GradedRes_key`, `s2Mu3NormRes_one`, and
  `s2Mu3NormRes_key`.

No requested law failed to port. **BLOCKED-BECAUSE: none.**

## Verification

From `leanfinal/`, missing landed dependency oleans were generated with the permitted scoped
command:

```text
lake build Uniformity.ChapC.C132rp6 Uniformity.ChapC.C132rp7
```

Then the requested direct check succeeded:

```text
lake env lean Uniformity/ChapC/C132rp8.lean
```

Exit 0.  The new Lean source contains no `sorry`, `unsafe`, or `axiom` declaration.  No
roll-up, leanspec, or existing source file was edited; no git commit was made.

## AxChk footer (verbatim from the green run)

```text
'Uniformity.Density.Tower.C132rp8.s2Mu3GradeOf' depends on axioms: [propext, Classical.choice, Quot.sound]
'Uniformity.Density.Tower.C132rp8.S2Mu3ExactGrade_s2Mu3GradeOf' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Uniformity.Density.Tower.C132rp8.s2Mu3NormRes' depends on axioms: [propext, Classical.choice, Quot.sound]
'Uniformity.Density.Tower.C132rp8.s2Mu3GradedRes_ne_zero_of_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Uniformity.Density.Tower.C132rp8.s2Mu3NormRes_coeff_zero_ne_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Uniformity.Density.Tower.C132rp8.s2Mu3GradedRes_natTrailingDegree_mul' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Uniformity.Density.Tower.C132rp8.s2Mu3NormRes_mul' depends on axioms: [propext, Classical.choice, Quot.sound]
'Uniformity.Density.Tower.C132rp8.s2Mu3GradedRes_key_pow' depends on axioms: [propext, Classical.choice, Quot.sound]
'Uniformity.Density.Tower.C132rp8.s2Mu3NormRes_key' depends on axioms: [propext, Classical.choice, Quot.sound]
'Uniformity.Density.Tower.C132rp8.s2Mu3NormRes_key_pow' depends on axioms: [propext, Classical.choice, Quot.sound]
```
