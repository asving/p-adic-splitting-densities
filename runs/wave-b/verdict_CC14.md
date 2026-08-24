# CC-14 verdict — FGMN scalar laws A

**LANDED** (all laws in scope; no SUPPLY, no BLOCKED).

## Deliverable

One new file: `leanfinal/Uniformity/ChapC/C130la.lean` (imports only landed `C130fg`).
No other file touched; CC-13's `C130fg.lean` unchanged (no field added); roll-ups and
leanspec untouched; nothing committed.

## Per-law status (namespace `Uniformity.Density.Tower`)

| published clause (design §10 row CC-14) | declaration | status |
|---|---|---|
| — (U9 Q2 projection, design §7 row `Rgr`) | `FGMNSourceData.Rgr` (def: `(gradedResidual β g).coeff 0`) + `Rgr_eq_coeff_zero` (`rfl` anti-drift pin) | LANDED |
| Lemma 3.14 scalar | `FGMNSourceLaws.Rgr_zero_of_above` | LANDED |
| Cor 4.12(1) scalar | `FGMNSourceLaws.Rgr_add` | LANDED |
| Cor 4.12(2) scalar + exact-grade product | `FGMNSourceLaws.Rgr_mul` (conjunction, A-C.11 field shape); components `exactGrade_mul`, `Rgr_mul_eq` | LANDED |
| Cor 4.12(3) | `FGMNSourceLaws.Rres_mul` (direct transport) + scalar corollary `Rres_coeff_zero_mul` | LANDED |
| Thm 4.1/Cor 4.9(1) scalar scope | `FGMNSourceLaws.Rgr_ne_zero` — carries the U9 degree fence `g.natDegree < (K.keyAt r).natDegree` verbatim | LANDED |
| bonus iterate (Lean-core corollary, no new source content) | `FGMNSourceLaws.Rgr_pow` (`0 < n`-fenced; grade `n·β`, scalar `(Rgr β g)^n`) | LANDED |

Every theorem is CONDITIONAL on `hL : FGMNSourceLaws W K e' f' u' S` exactly as the A-C.11
class fields are conditional on an instance — the published clauses stay source hypotheses
(design §9); what is proved is scalar-coordinate ⟸ polynomial-valued. Statement shapes match
the enacted A-C.11 fields (`leanspec/Leanspec/ChapC.lean` `FGMNCalculus`) byte-for-byte
under the §7 substitutions `Rgr ↦ coeff 0 ∘ gradedResidual`, `Rres ↦ normalizedResidual`,
`keyAt ↦ K.keyAt`, so CC-16 can consume them by name.

## Coefficient-zero regressions (row exit condition): PASS

`Regressions` section, three kinds of `example`-teeth, all green:
(i) SHAPE-FIT — each scalar law re-stated with the raw `(…).coeff 0` read in place of `Rgr`
and closed by the theorem term itself (definitional identity, zero rewriting room),
including the demanded "scalar of a product = product of scalars under exact grades" and an
`n = 2` power read; (ii) the three generic mathlib reads carrying the projection
(`Polynomial.coeff_zero`/`coeff_add`/`mul_coeff_zero`, names rg-verified against pinned
mathlib); (iii) a concrete numeric tooth over `ℤ` (`coeff 0` of `(X+2)(3X+4)` = `8`).

## Verification

```
cd leanfinal
lake env lean Uniformity/ChapC/C130la.lean       # exit 0
lake build Uniformity.ChapC.C130la               # completed, 8631 jobs
```

`#print axioms` (in-file, all 11 new declarations): `[propext, Classical.choice,
Quot.sound]` — Lean core only. No `sorry`, no new axiom, no `unsafe`, no `True` body, no
instance of any carrier.
