# MKP5 verdict — M3-KP5 LANDED

Node: **M3-KP5 key irreducibility** (`REUSE-WITH-NUMERALS`), 2026-08-27.

## Outcome

Landed `leanfinal/Uniformity/ChapC/C132kp5.lean`, with zero `sorry` and zero new axiom.

- `s2Mu3_key_irreducible`: every `S2Mu3KeyPoly` is irreducible in `Polynomial O`.
- `s2Mu3_key_irreducible_of_fraction_map`: the existing monic Gauss transport from `C130lb`
  specializes directly to μ₃ keys; no new fraction-field citation or transport is introduced.
- `s2Mu3_Φ₂_irreducible`: specializes the universal law to the carried
  `Φ₂ = s2DepthTwoKeyAt h2 hq 2`, using M3-KP4's landed key witness.

The universal proof is the landed μ₂ factorization argument at the new predicates: monicity
turns degree-zero factors into units, μ₃-primality selects a factor, and μ₃-minimality rules
out that factor by its strictly smaller degree.

**BLOCKED-BECAUSE: none.** Reuse with the μ₃ numerals was sufficient.

## Verification

From `leanfinal/`:

```text
lake build Uniformity.ChapC.C132kp2 Uniformity.ChapC.C132kp4
Build completed successfully.

lake env lean Uniformity/ChapC/C132kp5.lean
exit 0
```

The scoped build materialized missing dependency `.olean`s; no bare `lake build` was run.
No roll-up, leanspec, existing Lean source, sibling-owned `C132kp3.lean`, or git history was
changed.

## AxChk footer

Verbatim from the green direct check:

```text
'Uniformity.Density.Tower.C132kp5.s2Mu3_key_irreducible' depends on axioms: [propext, Classical.choice, Quot.sound]
'Uniformity.Density.Tower.C132kp5.s2Mu3_key_irreducible_of_fraction_map' depends on axioms: [propext,
 Classical.choice, Quot.sound]
'Uniformity.Density.Tower.C132kp5.s2Mu3_Φ₂_irreducible' depends on axioms: [propext, Classical.choice, Quot.sound]
```
