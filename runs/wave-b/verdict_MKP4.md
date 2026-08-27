# MKP4 verdict — M3-KP4 LANDED

Node: **M3-KP4 carried key** (`REUSE-WITH-NUMERALS`), 2026-08-27.

## Outcome

Landed `leanfinal/Uniformity/ChapC/C132kp4.lean`, with zero `sorry` and zero new axiom.

- `s2Mu3KeyPoly_Φ₂` proves
  `S2Mu3KeyPoly h2 hq (s2DepthTwoKeyAt h2 hq 2)`.
- `s2Mu3NormRes_Φ₂` proves the carried μ₃ residual is `1`.
- `tooth_Φ₂_mu3_vs_mu2` keeps both reads in one theorem: the μ₃ read is `1`, while the
  landed μ₂ read of the same `keyAt 2 = composedKey` polynomial is `X + 1`.

The unit μ₃ residual prevents use of the nonunit-residual divisibility criterion.  The proof
therefore reuses the landed μ₂ carried-key architecture with numerals `(4,21,2)`: slot-zero
divisibility, the odd-carry obstruction, short-polynomial minimality, and multiplicativity of
the slot-zero scalar.  The μ₂ certification in `C132nv3.s2Φ₂_keyPoly` is not duplicated.

**BLOCKED-BECAUSE: none.**

## Verification

From `leanfinal/`:

```text
lake env lean Uniformity/ChapC/C132kp4.lean
exit 0
```

No bare `lake build` was run.  No roll-up, leanspec, existing Lean source, sibling-owned file,
or git history was changed.

## AxChk footer

Verbatim from the green direct check:

```text
'Uniformity.Density.Tower.C132kp4.s2Mu3KeyPoly_Φ₂' depends on axioms: [propext, Classical.choice, Quot.sound]
'Uniformity.Density.Tower.C132kp4.s2Mu3NormRes_Φ₂' depends on axioms: [propext, Classical.choice, Quot.sound]
'Uniformity.Density.Tower.C132kp4.tooth_Φ₂_mu3_vs_mu2' depends on axioms: [propext, Classical.choice, Quot.sound]
```
