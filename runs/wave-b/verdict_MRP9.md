# Verdict — unit MRP9: node M3-RP9 BLOCKED-BECAUSE

Date: 2026-08-27  
Authority: `docs/in-progress/MU3_CAMPAIGN_2026-08-26.md` §6, row M3-RP9  
Tier: REUSE-WITH-NUMERALS; BLOCKED-BECAUSE over invention

## Outcome

`leanfinal/Uniformity/ChapC/C132rp9.lean` landed with node tag `[M3-RP9, 2026-08-27]`.
The literal `(e',f',u') = (2,1,21)` `normalized_recipe` display elaborates and is proved,
but its hypotheses are vacuous.  The row's requested non-vacuity tooth is formally refuted.

The obstruction is the landed μ₃ grade gate itself.  If `g.natDegree < 4`, its
`Φ₂`-development has only slot `0`.  An on-line exact-grade equation is then

```text
2*m + 21*0 = beta,
```

so `beta` is even.  Consequently no degree-`<4` polynomial has exact μ₃ grade `21`.

## Landed certificates

- `s2Mu3_recipe_grade_twenty_one_vacuous`: the general incompatibility
  `g.natDegree < 4 -> not S2Mu3ExactGrade 21 g`.
- `s2Mu3_normalized_recipe`: the exact finite-sum field display at
  `(e',f',u')=(2,1,21)`, discharged only by the incompatible `khat 0` premises.
- `s2Mu3_chainNormBelow_tooth_degree`: `natDegree (16*Phi') < 4`.
- `s2Mu3_chainNormBelow_two_twenty_one`: for any calculus carrying the landed key chain,
  A-C.18 computes `chainNormBelow 2 21 = 16*Phi'`.
- `s2Mu3_chainNormBelow_tooth_not_exact` and `s2Mu3_chainNormBelow_not_exact`: the proposed
  non-vacuity tooth is not exact μ₃ grade `21`, both as the explicit polynomial and through
  the actual `FGMNCalculus.chainNormBelow` definition.

This is not repaired by M3-RP3/RP6/RP8: those laws agree with the same gate.  No alternative
grade, degree fence, exponent, or recipe statement was invented.  The campaign row must be
re-adjudicated before a non-vacuous `normalized_recipe` field can land.

## Verification

The first direct check found only the missing landed `C132rp8.olean`.  The permitted scoped
command `lake build Uniformity.ChapC.C132rp8` completed successfully.  Then, from
`leanfinal/`:

```text
lake env lean Uniformity/ChapC/C132rp9.lean
```

returned exit 0.  The new Lean source contains zero `sorry`, zero new `axiom`, and no
`unsafe`.  No roll-up, leanspec file, or existing source file was edited; no git commit was
made.

## AxChk footer

The green direct run printed:

```text
'Uniformity.Density.Tower.C132rp9.s2Mu3_recipe_grade_twenty_one_vacuous' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Uniformity.Density.Tower.C132rp9.s2Mu3_normalized_recipe' depends on axioms: [propext, Classical.choice, Quot.sound]
'Uniformity.Density.Tower.C132rp9.s2Mu3_chainNormBelow_tooth_degree' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Uniformity.Density.Tower.C132rp9.s2Mu3_chainNormBelow_two_twenty_one' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Uniformity.Density.Tower.C132rp9.s2Mu3_chainNormBelow_tooth_not_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Uniformity.Density.Tower.C132rp9.s2Mu3_chainNormBelow_not_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

No footprint contains `sorryAx`.
