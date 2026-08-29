# UNIT GCF — VERDICT: BOTH REPAIR LEGS LANDED; cover now conditional on ONLY the exhaustion kernel

Date: 2026-08-29. File: `leanfinal/Uniformity/ChapI/IFCG10.lean` (706 lines, sorry-free,
per-file command exit 0, no warnings). No landed or leanspec file was edited.

| charge leg | status |
|---|---|
| (a) **STRONG BRIDGE** | **LANDED** — `exists_strongRealizesSkeletonAt_of_dissection`: IFCG8's proof re-plumbed to KEEP the `exists_ers_of_monic` factorization; every produced face carries its `ResidualPatternWitnessAt`. Footprint: Lean core + `Uniformity.Density.Tower.exists_dvDissection`, exactly as IFCG8's weak bridge. |
| (c) **DISJOINTNESS on the strong carrier** | **LANDED, UNCONDITIONAL, Lean-core** — `strongRealizes_skeleton_unique`: same blocks ⇒ same mass, same skeleton LIST (residual patterns included), same numerators. The GC countermodel `{(1,2)}`/`{(2,1)}` is DISTINGUISHED: `strong_repeatedLinear_simpleQuadratic_discriminated`. |
| (3) assembled shape | **STATED AND PROVED conditional on ONLY the kernel** — `finiteGenreCoverAt_strong_of_kernel : RecentredClusterDegreeExhaustionStatement → StrongCoverExhaustive ∧ StrongCoverDisjoint ∧ ∀ m, DecreasingGenreBankAt m`. DISJOINT and DECREASING enter unconditionally; only EXHAUSTIVE consumes the kernel. |

## Leg (a): the strong bridge (§3 of the file)

* `exists_strongFace_of_dissection_slope` — IFCG8 §3's per-slope proof byte-adapted, with
  the internal `set R := dvResPoly …` + `exists_ers_of_monic R` data RETURNED: the witness
  `⟨hne_own, M₀, hpinM, ers, hval, hdist, rfl-pattern, R-equation⟩` is literally IFCG9's
  `ResidualPatternWitnessAt` shape, so the re-plumb was exactly as predicted — no step
  resisted, no new mathematics on this leg. **Lean-core** (consumes an already-given
  dissection; the cite enters only at the whole-skeleton bridge below).
* `StrongRealizesSkeletonAt F H₀ hpin S num blocks` — the whole-skeleton strong carrier
  (`SlopesOrdered` + per-index `StrongRealizesFaceAt`); `strongRealizesSkeletonAt_realizes`
  projects to the weak carrier.
* `exists_strongRealizesSkeletonAt_of_dissection` — IFCG8 §4 byte-adapted over the strong
  per-slope theorem; conclusion includes bank membership (`S ∈ genreSkeletonFinset m`).
* `exists_strongRealizesSkeletonAt_of_degreeExhausted` — the IFCG9-§3 interface: hypothesis
  `DissectionDegreeExhausted`, not the raw `hbelow1`.

## Leg (c): disjointness (§1–§2 of the file), all Lean-core

The two new pieces of mathematics, then the assembly:

1. **UFD pattern read-off** (`residualPattern_eq_of_prod_eq`, over any field with
   classical decidability supplied at the use site): two pairwise-distinct
   monic-irreducible power factorizations with EQUAL products carry the same
   `(degree, multiplicity)` label multiset. Mechanism: `normalizedFactors` of the common
   product equals the multiplicity expansion (`normalizedFactors_mul/pow/irreducible` +
   `Monic.normalize_eq_self`), and the label multiset is the canonical function
   `r ↦ (deg r, count r)` over the expansion's support (`labels_eq_canon`, an induction
   using the pairwise-distinctness for the count bookkeeping).
2. **Pin invariance** (`dvResPoly_pin_congr`): C.25's residual polynomial is independent
   of the supplied nonemptiness/pin certificates — `ℕ∞`-cast injectivity pins the level
   `M`, proof irrelevance does the rest (the proof ends in `rfl`). This is what lets two
   independent `ResidualPatternWitnessAt`s be compared at all.
3. `strongRealizesFaceAt_unique` — one block strong-realizes at most one `(u, face)`:
   IFCG7's `realizesFaceAt_param_unique` pins `(u, b)`; pin invariance aligns the two
   witnesses' `dvResPoly`s; (1) pins the pattern; `FactorizationType.ext` closes.
4. `strongRealizes_skeleton_unique` — the target: same blocks ⇒ `m = m'` ∧ `S.1 = S'.1` ∧
   equal numerators (via `mass_eq_of_realizes_same_blocks`, per-face uniqueness,
   `List.ext_get`). `strongRealizes_skeleton_unique_same_mass` gives `S = S'` at the
   subtype at equal mass.
5. **Countermodel gate MET**: `strong_repeatedLinear_simpleQuadratic_discriminated` — no
   block strong-realizes both `repeatedLinearFace = (1, {(1,2)})` and
   `simpleQuadraticFace = (1, {(2,1)})`, at ANY numerators — precisely the discrimination
   IFCG9's `realizes_repeatedLinear_iff_simpleQuadratic` proves the weak carrier lacks.

**Honest scoping (recorded).** Disjointness is stated at the same surface as IFCG7's
parameter uniqueness: SAME block family (the `hlen` cast is needed even to state
"same blocks"). It does not additionally claim that a monic `f` determines its block
decomposition — that is the separate C133mh11-adjacent whole-`f` factorization-uniqueness
question, deliberately not claimed here; the bridge produces the blocks WITH `f = ∏ blocks`,
and cells are keyed by the produced realization data.

## The assembled cover (§4 of the file)

`StrongCoverExhaustive` and `StrongCoverDisjoint` are `Prop`-level definitions quantifying
over `O : Type` (matching the kernel's quantification). Landed:

* `strongCoverDisjoint_all : StrongCoverDisjoint` — unconditional, Lean-core.
* `strongCoverExhaustive_of_kernel : RecentredClusterDegreeExhaustionStatement → StrongCoverExhaustive`.
* `finiteGenreCoverAt_strong_of_kernel` — EXHAUSTIVE ∧ DISJOINT ∧ DECREASING from the
  single carried hypothesis. **The campaign's last GC piece is exactly the kernel**
  (`RecentredClusterDegreeExhaustionStatement`, IFCG9's coefficient-side polygonal
  exhaustion — the entire/principal-polygon comparison C.33 does not export).

## Plumbing dedup record

`isKey_X₂` / `localFieldStageField₂` / `exists_pin₂` / `list_prod_monic₂` /
`list_prod_natDegree_sum₂` / `list_mul_sum₂` re-derive C133mh14/IFCG6/IFCG8's private
plumbing (byte-identical mechanism; private there, hence unreachable; none of those files
edited; credited in the module docstring and per declaration). The disjointness section
carries NO `IsAdicComplete` (matching IFCG9's carrier section — uniqueness is pure
read-off); only the bridge section does.

## Verification and AxCheck

Command run after each increment and finally:

```text
cd leanfinal && timeout 580 ~/.elan/bin/lake env lean Uniformity/ChapI/IFCG10.lean
```

Final result: **exit 0, no errors, no warnings, no sorry**. The footer prints, for every
declaration:

* Lean core only (`propext`, `Classical.choice`, `Quot.sound`):
  `residualPattern_eq_of_prod_eq`, `dvResPoly_pin_congr`, `strongRealizesSkeletonAt_realizes`,
  `strongRealizesFaceAt_unique`, `strongRealizes_skeleton_unique`,
  `strongRealizes_skeleton_unique_same_mass`,
  `strong_repeatedLinear_simpleQuadratic_discriminated`,
  `exists_strongFace_of_dissection_slope`, `strongCoverDisjoint_all`.
* Lean core + exactly `Uniformity.Density.Tower.exists_dvDissection`:
  `exists_strongRealizesSkeletonAt_of_dissection`,
  `exists_strongRealizesSkeletonAt_of_degreeExhausted`,
  `strongCoverExhaustive_of_kernel`, `finiteGenreCoverAt_strong_of_kernel`.

No other axiom appears anywhere.

## What remains for GC (updated stop line)

The ONLY open input to `finiteGenreCoverAt_strong_of_kernel` is
`RecentredClusterDegreeExhaustionStatement` (GC1's coefficient-side polygonal exhaustion).
GC2/type-soundness is CLOSED by this unit. The `m ≤ 4` numeric gate of the GC blueprint
remains keyed to the strong classifier's instances and still awaits the kernel.
