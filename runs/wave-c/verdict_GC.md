# UNIT GC — VERDICT: HONEST PARTIAL; `finiteGenreCoverAt_all` BLOCKED

| required property | status |
|---|---|
| **EXHAUSTIVE** | **BLOCKED** — conditional exhaustion is landed as `exists_realizesSkeletonAt_of_degreeExhausted`; `degreeExhausted_iff_below_eq_one` proves the new hypothesis is exactly IFCG8's `hbelow1`. The missing coefficient-side theorem is isolated as `RecentredClusterDegreeExhaustionStatement`. |
| **DISJOINT** | **BLOCKED; CURRENT REALIZATION SURFACE FORMALLY INSUFFICIENT** — `realizes_repeatedLinear_iff_simpleQuadratic` proves that IFCG5's `RealizesFaceAt` cannot distinguish the distinct mass-two patterns `{(1,2)}` and `{(2,1)}`. IFCG7 reads slope/denominator/length/total residual degree, not the residual `FactorizationType`. |
| **DECREASING** | **LANDED** — `decreasingGenreBankAt_all` proves every child of every non-loop skeleton in the finite bank has mass `< m`; `sameMass_child_is_loop` pins the loop as the sole same-mass edge. |
| **TYPE-SOUND** | **PARTIAL / PRODUCER BLOCKED** — IFCG6's engine bank remains sound once supplied its residual factorization. IFCG9 defines the exact repaired carrier `StrongRealizesFaceAt` and exports `strongRealizesFaceAt_schemaData`, but IFCG8 returns only weak `RealizesSkeletonAt` and discards the UFD factorization used internally in its proof. |

Date: 2026-08-29. File: `leanfinal/Uniformity/ChapI/IFCG9.lean` (sorry-free; per-file command
exit 0). No landed or leanspec file was edited. `finiteGenreCoverAt_all` is deliberately not
declared: doing so from the current bank would hide both GC1 and GC2.

## What landed

### GC0 finite carrier (not the classifier)

* `genreSkeletonFinset m := Finset.univ` on IFCG5's finite type `ClusterSkeleton m` exposes
  one finite schema bank before any polynomial is supplied.
* `gc0_finiteBank_all` proves that bank contains exactly every `ValidSkeleton m` list.

This is GC0's finite carrier only. It is not a coefficient-vector classifier: no current
declaration maps a raw recentred coefficient box canonically into the bank.

### GC1 normalization dictionary and conditional exhaustion

* `DissectionDegreeExhausted F f` says every C.33 dissection's above-floor factors account for
  all of `f.natDegree`.
* `natDegree_eq_below_add_factors` proves

  ```text
  deg f = deg D.below + Σ p ∈ D.slopes, deg (D.factor p).
  ```

* `degreeExhausted_iff_below_eq_one` proves, with no new axiom,

  ```text
  DissectionDegreeExhausted F f ↔ ∀ D : DvDissection F f, D.below = 1.
  ```

* `exists_realizesSkeletonAt_of_degreeExhausted` feeds that result to IFCG8 and produces a
  realized member of the finite bank. Its only non-core axiom is the allowlisted
  `Uniformity.Density.Tower.exists_dvDissection`.

The exact missing coefficient-side statement is the defined proposition
`RecentredClusterDegreeExhaustionStatement`:

```lean
∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
  (π : O) (_hπ : Irreducible π) (F : KeyFrame O π) (f : Polynomial O),
  f.Monic → ¬ F.key ∣ f → StrictlyRecentredAboveFloor F f →
    DissectionDegreeExhausted F f
```

Here `StrictlyRecentredAboveFloor` is coefficient-side: every development coefficient left of
the monic endpoint lies strictly above the continued frame-floor line. It mentions neither
`DvDissection.below` nor a dissection. The corpus has no theorem turning that condition (or the
raw `ClusterState`/coefficient-box normalization) into whole-degree above-floor exhaustion.
This is not an arithmetic omission: it needs an entire/principal Newton-polygon comparison or
equivalent full-span theorem that C.33 does not export.

### GC2 formal falsifier and repair surface

`RealizesFaceAt F g u (b, σ)` unfolds to purity at `(u,b)` plus
`dvSideLen = b * σ.degree`; it never inspects `σ.data`. IFCG9 proves the general blindness
lemma `realizesFaceAt_iff_of_den_resDeg_eq`, then instantiates it at mass two:

```text
repeatedLinearFace  = (1, {(1,2)})
simpleQuadraticFace = (1, {(2,1)})
```

Both are valid, both have residual degree two, they are unequal, and every block realizing one
realizes the other. Thus the blueprint's “IFCG7 read-off uniqueness” premise is insufficient as
currently typed. `face_split_unique` does not repair this: it proves uniqueness of a
labelled/complement split after a residual label has been supplied; it does not reconstruct the
whole pattern stored in the face.

The required repaired carrier is now explicit:

* `ResidualPatternWitnessAt` retains the pairwise-distinct monic irreducible residual factors,
  their `(degree,multiplicity)` labels, the equality to `face.2.data`, and the exact `dvResPoly`
  product.
* `StrongRealizesFaceAt` is weak geometric realization plus that witness.
* `strongRealizesFaceAt_schemaData` exports IFCG6 `schema_split`'s exact input shape.

To close GC2/type soundness, a successor must strengthen IFCG8's per-slope and whole-skeleton
bridges to produce `StrongRealizesFaceAt`, and prove UFD/read-off uniqueness of the stored
patterns. A theorem merely choosing one weak realization would make cells disjoint by choice,
but would not prove canonical coefficient-cylinder classification and is not accepted here.

### GC3 decrease

`decreasingGenreBankAt_all` is unconditional and ranges over the full finite skeleton bank.
`sameMass_child_is_loop` is the sharp entry-indexed loop tooth. These consume IFCG5/IFCG6 and
add no axiom.

## Numeric gate

**NOT MET as a genre-cover theorem.** IFCG0's executable first-layer residue-pattern regression
prints `5` at degree three and `11` at degree four, matching the named tables. But those are
residue-pattern/output rows, not IFCG5 NP skeletons: the landed skeleton regression prints `15`
at mass three and `56` at mass four. Conflating the two would be a type error in the campaign's
mathematics. Since the exhaustive/disjoint strong classifier is absent, there is no accepted
Lean theorem saying its `m ≤ 4` instances recover the cubic/quartic tables. The blueprint's
examples-first gate therefore remains red, exactly as required (the quartic computation is not
promoted to proof).

## Verification and AxCheck

Command run after each increment and finally:

```text
cd leanfinal && timeout 580 ~/.elan/bin/lake env lean Uniformity/ChapI/IFCG9.lean
```

Final result: exit 0, no warnings. The footer prints Lean core only (`propext`,
`Classical.choice`, `Quot.sound`) for every new declaration except
`exists_realizesSkeletonAt_of_degreeExhausted`, which additionally prints exactly
`Uniformity.Density.Tower.exists_dvDissection`. No other literature axiom appears.
