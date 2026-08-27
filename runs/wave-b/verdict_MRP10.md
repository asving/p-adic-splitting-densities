# Verdict — unit MRP10, μ₃ campaign node M3-RP10

**Deliverable:** `leanfinal/Uniformity/ChapC/C132rp10.lean` (new file; node tag
`[M3-RP10, 2026-08-27]`).  No roll-up, leanspec, existing Lean source, or `C132kp0.lean`
was edited.  No git commit was made.

## Result: BLOCKED-BECAUSE, with the reusable pieces landed

The two-element-field collapse succeeds: `s2Mu3_unique_admissible_linear` proves that every
monic degree-one residual with nonzero constant coefficient is `X + 1`, and
`s2Mu3_X_add_one_irreducible` supplies the corresponding irreducibility tooth.

The intended recipe polynomial `Φ₂² - 2⁴ Φ'` is constructed in theorem statements and its
bookkeeping succeeds: `s2Mu3_gEight_monic` proves it monic and
`s2Mu3_gEight_natDegree` proves its degree is exactly `8 = 2·1·deg(Φ₂)`.

The requested μ₃ residual proof cannot be obtained from the named M3-RP9 input.  Its literal
recipe theorem requires a correction `khat` satisfying both
`S2Mu3ExactGrade 21 khat` and `khat.natDegree < 4`; M3-RP9 proves that conjunction
impossible.  `s2Mu3_recipe_correction_input_impossible` records the general contradiction,
and `s2Mu3_gEight_recipe_input_impossible` fires it on the intended correction `2⁴ Φ'`.
Per the row's `REUSE-WITH-NUMERALS` constraint, this unit does not invent a corrected recipe
signature or a new direct μ₃ residual computation.

## Verification

The first direct check found only the missing just-landed `C132rp9.olean`.  The permitted
scoped command `lake build Uniformity.ChapC.C132rp9` succeeded.  Then, from `leanfinal/`:

```text
lake env lean Uniformity/ChapC/C132rp10.lean
```

returned exit 0.  The file contains zero `sorry`, zero new `axiom`, and no `unsafe`.

## AxChk footer

```text
'Uniformity.Density.Tower.C132rp10.s2Mu3_unique_admissible_linear' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Uniformity.Density.Tower.C132rp10.s2Mu3_X_add_one_irreducible' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Uniformity.Density.Tower.C132rp10.s2Mu3_gEight_monic' depends on axioms: [propext, Classical.choice, Quot.sound]
'Uniformity.Density.Tower.C132rp10.s2Mu3_gEight_natDegree' depends on axioms: [propext, Classical.choice, Quot.sound]
'Uniformity.Density.Tower.C132rp10.s2Mu3_recipe_correction_input_impossible' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Uniformity.Density.Tower.C132rp10.s2Mu3_gEight_recipe_input_impossible' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

No footprint contains `sorryAx`.
