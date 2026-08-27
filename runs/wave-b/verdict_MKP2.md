# MKP2 verdict — M3-KP2 LANDED

Node: **M3-KP2 primality/minimality** (`REUSE-WITH-NUMERALS`), 2026-08-27.

## Outcome

Landed `leanfinal/Uniformity/ChapC/C132kp2.lean`, with zero `sorry` and zero new axiom.

- `s2Mu3Irreducible_of_irreducible_normRes`: a monic degree-`≤ 8` polynomial with
  irreducible normalized μ₃ residual is μ₃-irreducible.
- `s2Mu3Minimal_of_not_isUnit_normRes`: a positive-degree degree-`≤ 8` polynomial with
  nonunit normalized μ₃ residual is μ₃-minimal.
- `s2Mu3Minimal_of_irreducible_normRes`: the degree-eight recipe specialization, using
  irreducibility to supply the nonunit condition.

Primality pushes μ₃-divisibility of a product to normalized residual divisibility, invokes
irreducible-implies-prime in the residual polynomial UFD, then pulls the chosen factor back
through M3-KP1.  Minimality pushes a hypothetical smaller-degree divisor forward; M3-KP1
shows its residual is a unit, contradicting the nonunit residual of the proposed divisor.

**BLOCKED-BECAUSE: none.** The planned numeral-level reuse was sufficient; no new engine was
introduced.

## Verification

From `leanfinal/`:

```text
lake build Uniformity.ChapC.C132kp1
Build completed successfully (8793 jobs).

lake env lean Uniformity/ChapC/C132kp2.lean
exit 0
```

The scoped build only materialized the missing M3-KP1 `.olean`; no bare `lake build` was run.
No roll-up, leanspec, existing Lean source, sibling-owned `C132kp4.lean`, or git history was
changed.

## AxChk footer

Verbatim from the green direct check:

```text
'Uniformity.Density.Tower.C132kp2.s2Mu3Irreducible_of_irreducible_normRes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Uniformity.Density.Tower.C132kp2.s2Mu3Minimal_of_not_isUnit_normRes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Uniformity.Density.Tower.C132kp2.s2Mu3Minimal_of_irreducible_normRes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```
