# MKP3 verdict — M3-KP3 LANDED

Node: **M3-KP3 key criterion** (`REUSE-WITH-NUMERALS`), 2026-08-27.

Landed [C132kp3.lean](../../leanfinal/Uniformity/ChapC/C132kp3.lean):

- `s2Mu3_key_criterion` assembles the literal
  `2 * 1 * deg(keyAt 2) = 8` field from monicity, irreducible normalized residual,
  residual degree one, and nonzero residual constant coefficient.
- `s2Mu3_key_criterion_fills` adapts that result to
  `FGMNSourceData (s2DepthTwo h2 hq) K 2 1 21`, using the key-chain degree pin.

M3-RP10's `s2Mu3_recipe_correction_input_impossible` remains the exact
**BLOCKED-BECAUSE** boundary: this conditional field does not assert a new degree-eight
recipe witness or residual-existence theorem.

## Verification

From `leanfinal/`, after the permitted scoped build of the two missing landed dependency
artifacts:

```text
lake build Uniformity.ChapC.C132kp2 Uniformity.ChapC.C132rp10
lake env lean Uniformity/ChapC/C132kp3.lean
```

Exit 0. The new file contains zero `sorry` and declares no axioms.

## AxChk footer

```text
'Uniformity.Density.Tower.C132kp3.s2Mu3_key_criterion' depends on axioms: [propext, Classical.choice, Quot.sound]
'Uniformity.Density.Tower.C132kp3.s2Mu3_key_criterion_fills' depends on axioms: [propext, Classical.choice, Quot.sound]
```
