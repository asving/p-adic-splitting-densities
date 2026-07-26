## Semantic-faithfulness verdict

The four fence changes are mathematically faithful. None makes its theorem vacuous or evades the intended MOVES argument.

### Fence changes

| Unit | Classification | Verdict |
|---|---|---|
| `L2.iaugStep` + `hψ : Irreducible ψ` | FLAGGED-OK | D.8/B1.3 uses an irreducible residual key throughout. The reducible branch is outside the referent, not an omitted case. Keep the existing monicity and `ψ ≠ X` conditions or derivation. |
| `L5.landTwoSided` + anchor exactness | FLAGGED-OK | Faithful completion. In D.8, `a` is the exact `z`-order and `R(f)=z^a R_anch`; hence `X ∤ R_anch` is intrinsic stratum data. Via `IsDevelopment`, the proposed `¬ X ∣ Σ j, Cdig j * ψ^j` expresses exactly that condition. |
| `L4.TRANSv` + `hcore : StageCore σ` | FLAGGED-OK | D.7(v)’s field-surjectivity argument consumes the current stage axioms, including the previous I-augmentation inequality and scalar realizers. `StageCore σ` is therefore a legitimate input, provided it is the parent/current certificate—not the certificate being constructed—and does not contain `TRANSv` itself. |
| `L6.measureExact` + `hzsolN`/`hzsolM` | FLAGGED-OK | These are the missing zero-code exclusions. For the abstract event interface they must be hypotheses unless derivable from `IsSolution`. They mirror the existing zero-stratum exclusions and do not trivialize the nonzero transfer. |

For `landTwoSided`, placing exactness directly in the theorem is acceptable and has the smallest blast radius. It leaves `LandingCylinderL` broader than the mathematical landing cylinder, but the theorem’s locus is correct.

### Other repair statements

- `L1.baseWeight`: FLAGGED-OK. The unchanged multiplicativity statement is precisely B1.1/B1.2 and must be discharged through the graded-domain construction.
- `L5.landVertexDigit`: FLAGGED-OK. The unchanged vertex congruence is D.8’s order-\(\mu\) reduction; the cited K1 residual-sum mechanism is the correct proof route.
- The repaired `L6.measureExact` statement remains semantically sound, but is not proof-ready because its separate landing theorem is still only a mismatched placeholder.

### The 13-unit A/B1 campaign

All 13 units are FLAGGED-OK as a coverage decomposition of §§A and B1:

- `grRing`, `grDomain`, `weightMul`, `weightUlt`, `weightNonneg`, `weightKey`
- `anchorCongMod`, `normalForm`, `oreResidual`, `K1dev`
- `rsLemma`, `rsLanding`, `incLanding`

They cover the essential missing mathematics rather than recreating the earlier `grRes` façade.

The following scope guards are mandatory in their actual fences:

- `normalForm` and additive-anchor claims must assume `f ≠ 0`.
- `oreResidual`’s anchor-additivity clause must assume both factors are nonzero, or define the zero case separately.
- `K1dev` must concern the standard lift attached to monic irreducible `ψ ≠ X`, not an arbitrary polynomial called `Φ`.
- `rsLemma`/`rsLanding` must be explicitly integer-slope (`e = 1`).
- `incLanding` must retain the standard-lift, irreducibility, `ψ ≠ X`, multiplicity, and `e · deg ψ > 1` conditions.

If any full JSON fence omits one of these guards, that particular unit becomes IMPRECISE and should be withheld.

## Cylinder anomaly

The anomaly is real, and the proposed “future reconciliation unit” is currently IMPRECISE rather than fully scoped.

A blanket equivalence between `DefsCore.LandingCylinder` and `DefsL.LandingCylinderL` would be wrong: they encode different objects, and `LandingCylinderL` by itself omits anchor exactness. The repair must choose one of these narrow forms:

1. Re-point `measureExact` to the `DefsL` theorem and explicitly translate its stratum/event parameters; or
2. Prove a measureExact-specific bridge under an explicit encoding relation and the anchor-exactness hypothesis.

No unrestricted `LandingCylinder ↔ LandingCylinderL` theorem should be filed.

## Cleanup and deprecation

The two stale-comment removals and five deprecation headers are FLAGGED-OK.

No live content is lost because the old files remain for provenance and each has a named clean successor. Preserve the counterexamples in `L5_landTransport_R3` and `L6_moveReduceCommute_R3`. Re-point `L4.TRANSv` before treating `L4_TRANSviii_b_R3` as non-importable. The header spelling should be `DEPRECATED`, not `DEPROCATED`.

## Counts

Statement-level audit:

- FAITHLESS: **5** — the standing audit-#5 boundary units.
- IMPRECISE: **1** — the presently underspecified cylinder-reconciliation proposal.
- FLAGGED-OK: **19** — 6 repair units plus 13 MovesGr units.

Administrative items:

- FLAGGED-OK: **7** — 2 comment cleanups and 5 deprecation headers.

## Units unsafe to prove

Do not fan out:

- `L1.baseStage_exists`
- `L1.base_nonvacuity_gate`
- `L4.TRANSvi`
- `L4.TRANSstage`
- `L5.recTRANSRS`
- `L6.measureExact`, until the cylinder-type bridge/re-pointing is supplied
- Any blanket `LandingCylinder`/`LandingCylinderL` equivalence
- The five deprecated predecessor files as proof targets

The four amended fences themselves are approved.

**Verdict: FAN-OUT MAY PROCEED — minus the units listed above.**
