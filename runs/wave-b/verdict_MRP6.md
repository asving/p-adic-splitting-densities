# VERDICT — unit MRP6 (node M3-RP6: μ₃ graded product assembly)

**Status: LANDED — sorry-free, no new axiom, Lean check green.**

Node M3-RP6 of `docs/in-progress/MU3_CAMPAIGN_2026-08-26.md` §6 landed in
`leanfinal/Uniformity/ChapC/C132rp6.lean` with tag **[M3-RP6, 2026-08-27]**.  The file is the
mechanical μ₃ port of the cited μ₂ polynomial-ext and `S2PrevGrade` assembly patterns.

## Landed declarations

- `s2Mu3GradedRes_mul_coeff`, `s2Mu3GradedRes_mul_coeff_zero_of_odd`, and
  `s2Mu3GradedRes_mul_coeff_of_prevGrade`: polynomial-coefficient companions assembled from
  RP5's coefficient convolution bank.
- `s2Mu3GradedRes_mul_of_exact`: the arbitrary-grade identity with twist
  `X ^ ((β % 2) * (β' % 2))`.
- `s2Mu3GradedRes_mul_of_prevGrade`: its plain even-second-grade specialization.
- `S2Mu3PrevGrade := 2 ∣ β` and `S2Mu3PrevGrade_iff_mod`.
- `s2Mu3_graded_mul`: the exact-grade conjunct bundled with the plain identity, matching the
  restored A-C.13 `FGMNSourceLaws.graded_mul` binder shape.
- `s2Mu3_graded_mul_twisted`: the same exact-grade conjunct bundled with the arbitrary-grade
  twisted identity.
- `s2Mu3_graded_mul_fills`: field-shape pin for an
  `FGMNSourceData (s2DepthTwo h2 hq) K 2 1 21`, including the current restored
  `PrevGrade` field.

No law failed to port; **BLOCKED-BECAUSE: none**.  The A-C.17 consumer fence
`2 ≤ f' → PrevGrade u'` does not alter the source-law field assembled here: the current
`FGMNSourceLaws.graded_mul` correctly retains its unconditional `PrevGrade β'` premise.

## Verification

From `leanfinal/`:

```text
lake build Uniformity.ChapC.C132rp5
```

was used only to generate the missing landed RP5 `.olean` (scoped build, exit 0), followed by:

```text
lake env lean Uniformity/ChapC/C132rp6.lean
```

Exit 0.  Zero `sorry`, zero `unsafe`, zero `axiom` declarations in the new Lean file.

## AxChk footer (all declarations, verbatim from the green run)

```text
'Uniformity.Density.Tower.C132rp6.s2Mu3GradedRes_mul_coeff' depends on axioms: [propext, Classical.choice, Quot.sound]
'Uniformity.Density.Tower.C132rp6.s2Mu3GradedRes_mul_coeff_zero_of_odd' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Uniformity.Density.Tower.C132rp6.s2Mu3GradedRes_mul_coeff_of_prevGrade' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Uniformity.Density.Tower.C132rp6.s2Mu3GradedRes_mul_of_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Uniformity.Density.Tower.C132rp6.s2Mu3GradedRes_mul_of_prevGrade' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Uniformity.Density.Tower.C132rp6.S2Mu3PrevGrade' does not depend on any axioms
'Uniformity.Density.Tower.C132rp6.S2Mu3PrevGrade_iff_mod' depends on axioms: [propext, Classical.choice, Quot.sound]
'Uniformity.Density.Tower.C132rp6.s2Mu3_graded_mul' depends on axioms: [propext, Classical.choice, Quot.sound]
'Uniformity.Density.Tower.C132rp6.s2Mu3_graded_mul_twisted' depends on axioms: [propext, Classical.choice, Quot.sound]
'Uniformity.Density.Tower.C132rp6.s2Mu3_graded_mul_fills' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Repository footprint: the requested new Lean file and this verdict only; no roll-up,
leanspec, or pre-existing source file was edited, and no git commit was made.
