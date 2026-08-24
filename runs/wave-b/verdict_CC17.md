# Unit CC-17 verdict — the S2 acceptance gate

## Verdict

**HONEST PARTIAL / BLOCKED on source mathematics.**  The full S2 `ChainRealization` is not
unconditionally inhabited.  The repository side is completely inhabited by the named
`s2RepositoryRealization`; the input polynomial occurrence is also concrete
(`s2InputPolynomial = keyAt 2 + 1`, `n = 4`, `μ = 1`) under the campaign's standard
`[IsAdicComplete (maximalIdeal O) O]` environment.  What remains is exactly the source-side
`NodePointSource`, `FGMNSourceData`, `FGMNSourceLaws`, and OPEN-DICT-2/4 package bundled as
`S2SourceFrontier`.

No field was weakened, no arbitrary threshold or residual table was installed, and no
`sorry`, new axiom, or `unsafe` declaration was used.  The conditional maps prove exactness
of the diagnosis:

- `S2SourceFrontier.toChainRealization` constructs the literal full
  `ChainRealization (s2DepthTwo h2 hq) ((s2DepthTwo h2 hq).fld 2) L 2 1 5`;
- `S2SourceFrontier.calculusNonempty` then constructs
  `Nonempty (FGMNCalculus (s2DepthTwo h2 hq) 2 1 5)`;
- `S2SourceFrontier.s2RealizedInput` constructs the literal `RealizedInput` over the concrete
  `keyAt 2 + 1` arising occurrence.

These are conditional constructors, not claims that `S2SourceFrontier` is inhabited.

## Landed declarations

New file: `leanfinal/Uniformity/ChapC/C130s17.lean`, namespace
`Uniformity.Density.Tower.C130s17`.

| declaration | status | content |
|---|---|---|
| `S2DepthTwo` | FILLED | short name for CC-2's literal `s2Witness.trunc 2` tower |
| `s2TerminalReceiver` | FILLED | CC-3 receiver; every off-range map is `RingHom.id` because C.97's `fld` is constant |
| `S2RepositoryRealization` | FILLED sub-record type | receiver, keys, normalizer, and complete level-2 carrier |
| `s2RepositoryRealization` | FILLED inhabitant | named maximal unconditional S2 repository realization |
| four `s2RepositoryRealization_*` pins | FILLED | components are literally CC-3/2/4/6 witnesses |
| `S2SourceFrontier` | BLOCKER BUNDLE | exact remaining node/FGMN/OPEN-DICT objects; level-2 table ties are mandatory |
| `S2SourceFrontier.toChainRealization` | FILLED conditional constructor | packages exactly the full `ChainRealization` |
| `S2SourceFrontier.calculusNonempty` | FILLED conditional constructor | literal CC-16 calculus at `(2,1,5)` |
| `point`, `point_mem` | FILLED from frontier | CC-9 `legalPoint`, chosen from carried `point_exists` |
| `thresholdZ`, `thresholdNat` | FILLED projections | inherited threshold; no numeral/formula |
| `canonicalRead`, `arenaRead`, `towerRead`, `peelUnit` | FILLED projections | named reads, with canonical/arena separation preserved |
| `stageTwo_view` | FILLED | derived carrier and `s2Slot₂` agree on `D,eC,fC,hgt,dig,Full` |
| `S2InputData`, `toArisingCore` | FILLED exact interface/map | exposes and packages an arbitrary honest input occurrence |
| `s2InputPolynomial` and three laws | FILLED | `keyAt 2 + 1` is monic, has degree 4, and is key-free after fraction-field mapping |
| `s2InputData`, `s2ArisingCore` | FILLED under `[IsAdicComplete]` | concrete `n=4`, `μ=1` input occurrence |
| `realizedInput`, `s2RealizedInput` | FILLED conditional constructors | literal `RealizedInput`; receiver/key/degree equalities are `rfl`, point is `legalPoint` |

## `ChainRealization` field table

| field | status | witness / exact blocker |
|---|---|---|
| `receiver` | **FILLED** | `s2TerminalReceiver h2 hq` |
| `keys` (OPEN-DICT-1) | **FILLED** | `s2DepthTwoKeyChain h2 hq`; live keys are frame key and `composedKey (s2Tower h2 hq)` |
| `normalizer` | **FILLED** | `(s2DepthTwo h2 hq).laurentNormalizer`, the repaired literal normalizer |
| `node` | **BLOCKED** | missing a full `NodePointSource`; exact constituent ledger below |
| `fgmn` | **BLOCKED** | missing the realized next MacLane valuation/residual model `FGMNSourceData` at `(2,1,5)` |
| `fgmnLaws` | **BLOCKED** | missing proofs that that source model satisfies the thirteen `FGMNSourceLaws` fields |
| `grade_compat` (OPEN-DICT-2) | **BLOCKED** | missing equality of the cleared next MacLane valuation with the terminal legal-point evaluation read |
| `letter_compat` (OPEN-DICT-4) | **BLOCKED** | missing equality between transported FGMN letters and ambient node letters |

OPEN-DICT-3's repository half is **FILLED** by the terminal receiver and the fixed
`Polynomial ((s2DepthTwo h2 hq).fld 2)` codomain.  Its mathematical/source half remains
inside the blocked `fgmn`/`fgmnLaws` objects; no free scalar residual was substituted.

## `NodePointSource` field-by-field table

CC-9/10/11 land derived layers over `NodePointSource`; their verdicts explicitly state that
they do not inhabit it.  CC-6 closes the entire level-2 table only, while this structure is
tower-indexed and also demands level 1 plus point ties.

| field | status | witness / exact blocker |
|---|---|---|
| `Point` | **BLOCKED** | actual S2 legal P-locus point type |
| `Pt` | **BLOCKED** | stagewise P-locus predicate |
| `point_exists` | **BLOCKED** | nonemptiness theorem for the legal P-locus at levels 1 and 2 |
| `coeffHom` | **BLOCKED** | ambient coefficient homomorphism for actual evaluation |
| `coord` | **BLOCKED** | ambient coordinate of each legal point |
| `valueOn` | **BLOCKED** | ambient stage valuation read |
| `value_zero` | **BLOCKED** | zero law for that read |
| `value_mul` | **BLOCKED** | multiplicativity of that read |
| `value_add_ge` | **BLOCKED** | ultrametric inequality for that read |
| `value_add_eq` | **BLOCKED** | off-tie ultrametric equality for that read |
| `hgt` | **PARTIAL** | level 2 is `s2Hgt₂`; a full total family, especially the live level-1 table, is missing |
| `dig` | **PARTIAL** | level 2 is `s2Dig₂`; a full total family, especially level 1, is missing |
| `pointHgt` | **BLOCKED** | pointwise polynomial evaluation height |
| `pointDig` | **BLOCKED** | pointwise digit read |
| `pointHgt_eval` | **BLOCKED** | equality with `valueOn i (eval₂ coeffHom (coord x) A)` |
| `slot_value` | **BLOCKED** | legal-point exactness tying evaluations to `hgt` at both live levels |
| `slot_digit` | **BLOCKED** | legal-point exactness tying point digits to `dig` at both live levels |
| `hgt_zero` | **PARTIAL** | proved at level 2 by `s2Hgt₂_zero`; level 1 missing |
| `dig_zero` | **PARTIAL** | proved at level 2 by `s2Dig₂_zero`; level 1 missing |
| `hgt_ne_top` | **PARTIAL** | proved at level 2 by `s2Hgt₂_ne_top_slot`; level 1 missing |
| `dig_ne_zero` | **PARTIAL** | proved at level 2 by `s2Dig₂_ne_zero`; level 1 missing |
| `hgt_add_ge` | **PARTIAL** | proved at level 2 by `s2Hgt₂_add_ge`; level 1 missing |
| `hgt_add_eq` | **PARTIAL** | proved at level 2 by `s2Hgt₂_add_eq`; level 1 missing |
| `dig_add` | **PARTIAL** | proved at level 2 by `s2Dig₂_add`; level 1 missing |
| `Full` | **PARTIAL** | level 2 is the nontrivial `S2Full₂`; level-1 predicate missing |
| `lift` | **PARTIAL** | proved at level 2 by `s2Lift₂`; level 1 missing |
| `thresholdZ` | **BLOCKED** | inherited integer threshold, not derivable from the tower |
| `thresholdNat` | **BLOCKED** | natural repository avatar of that inherited threshold |
| `threshold_nonneg` | **BLOCKED** | exact integer/natural dictionary at both live levels |
| `window` | **BLOCKED** | EFF.T2.11 `T < d(Φ(ρ)) < ∞` at every legal point |
| `ambientLetter` | **BLOCKED** | actual ambient node letters |
| `key_value` | **BLOCKED** | exact legal-point key value at the unique gauge-live level 1 |
| `psi_root` | **BLOCKED** | transported `ψ₁` root law for the ambient letter |
| `canonicalRead` | **BLOCKED** | source L-valued kernel read; CC-10 only exports a carried read |
| `arenaRead` | **BLOCKED** | separate source terminal-field kernel read; CC-11 only exports a carried read |
| `towerRead` | **BLOCKED** | source terminal-field lattice read |
| `peelUnit` | **BLOCKED** | source peel-unit family |

`S2SourceFrontier.hgt_two`, `.dig_two`, and `.full_two` force any future full node instance
to use CC-6's concrete tables.  `stageTwo_view` checks the resulting CC-5 carrier against
`s2Slot₂` on all data fields.

## FGMN source field-by-field table

### `FGMNSourceData`

| field | status | exact missing source object |
|---|---|---|
| `nextValue` | **BLOCKED** | realized cleared next augmented MacLane valuation `μ₃` |
| `gradedResidual` | **BLOCKED** | polynomial-valued operators `R_(3,β)` over the transported terminal residue field |
| `normalizedResidual` | **BLOCKED** | normalized residual operator `R₃` |
| `keyPolynomial` | **BLOCKED** | predicate `KP(μ₃)` |
| `initialEquiv` | **BLOCKED** | initial-form equivalence for `μ₃` |
| `letter` | **BLOCKED** | transported FGMN letters `z_i` |

### `FGMNSourceLaws`

| field | status | exact missing proof |
|---|---|---|
| `graded_zero_of_above` | **BLOCKED** | Lemma 3.14 on the actual graded residual |
| `graded_add` | **BLOCKED** | Corollary 4.12(1) on the actual source operators |
| `graded_mul` | **BLOCKED** | Corollary 4.12(2), including exact-grade product |
| `graded_scalar_nonzero` | **BLOCKED** | Theorem 4.1 + Corollary 4.9(1), with the degree fence |
| `normalized_mul` | **BLOCKED** | Corollary 4.12(3) on the actual normalized residual |
| `normalized_recipe` | **BLOCKED** | Definition 1.6/3.13, equation (11), Corollary 4.12 recipe dictionary |
| `normalized_exists` | **BLOCKED** | Theorem 5.7 construction for the actual source model |
| `key_criterion` | **BLOCKED** | Lemma 5.2(2)/Corollary 4.9/Theorem 5.7 criterion |
| `key_irreducible` | **BLOCKED** | Lemma 1.8/Corollary 1.10 source claim; the Gauss transport itself is already proved in CC-15 |
| `carried_key_is_key` | **BLOCKED** | Proposition 1.7(4) for the carried `keyAt 2` |
| `carried_key_residual` | **BLOCKED** | equation (11) for the carried key |
| `initial_iff_residual` | **BLOCKED** | Proposition 5.6(2) iff (3) on actual key polynomials |
| `letter_ne_zero` | **BLOCKED** | §3.3 nonvanishing for the actual transported letters |

CC-14/15 prove scalar projections and class-facing transports **from an
`FGMNSourceLaws` hypothesis**.  They do not provide an inhabitant, so using them cannot close
this table without circularly assuming the missing source package.

## `RealizedInput` field table

For `S2SourceFrontier.s2RealizedInput`, under `[IsAdicComplete]`:

| field | status | witness |
|---|---|---|
| `receiver_eq` | **FILLED** | `rfl` |
| `stageKey_eq` | **FILLED** | `rfl`; the core uses repository `keyAt 2` |
| `stageDeg_eq` | **FILLED** | `rfl`; the core uses `Dcum 2 = 4` |
| `point` | **FILLED conditionally** | `S.node.legalPoint 2`, chosen from `point_exists` |
| `point_mem` | **FILLED conditionally** | `S.node.legalPoint_mem 2` |

The concrete arising occurrence itself is filled: `F₀ = keyAt 2 + 1`, monic, degree 4,
`μ = 1`, and key-free because `(keyAt 2 + 1, keyAt 2)` is coprime after mapping.  Thus the
only obstruction to the named `s2RealizedInput` is the same `S2SourceFrontier` blocking the
full chain; no additional input-polynomial theorem remains.

## Axioms and cites

Every one of the 30 authored declarations has an in-file `#print axioms`.  Every footprint is
exactly Lean core:

```text
[propext, Classical.choice, Quot.sound]
```

**Explicit cite list consumed by CC-17: NONE.**

- `fgmn_dv_exact_mul`: **not used**.
- No declared literature cite appears in any CC-17 axiom footprint.
- The published FGMN clauses named above occur only as documentation for fields of the
  uninhabited source frontier; they are not consumed by a CC-17 proof.

## Verification

From `leanfinal/`:

```text
lake env lean Uniformity/ChapC/C130s17.lean
lake build Uniformity.ChapC.C130s17
```

Both exit 0.  The module build completed successfully (8699 jobs).  No roll-up, leanspec, or
other unit file was touched.

---
## ORCHESTRATOR ADDENDUM (2026-08-24, for unit U13)

A killed Fable U13 predecessor's last finding, unverified but flagged load-bearing: the
`(e′, f′, u′) = (2, 1, 5)` parameter choice in this verdict's S2 instance may conflict with
the witness's STAGE-3 data `(2, 1, 21)` — under U9's Q1 decision (the class is the calculus
of the NEXT augmented valuation), the parameters at `r = 2` should be the next-augmentation
data, and whether that is `(2,1,5)` or `(2,1,21)` at the S2 chain must be traced (D62w's
`u = (1, 5, 21)`; C131ac consumed `(2,1,5)`-shaped loci). U13 must adjudicate this before
planning the inhabitation — a wrong parameter here would make the frontier bundle
inhabitable-but-useless (fed to consumers at the wrong slot).

---
## ORCHESTRATOR ADDENDUM 2 (2026-08-24, post-U13) — VACUITY FINDING

U13's machine-checked refutation (`scratch/U13_probe.lean`, `IsEmpty` proofs, Lean-core):
`S2SourceFrontier` is UNINHABITABLE as typed — `[Algebra Kt L]` forces char L = 2 at S2,
so the coefficient hom kills `C 2` while `slot_value`/`hgt_ne_top` demand finite height.
This verdict's conditional constructors are correct implications with an EMPTY premise at
S2 (vacuous conditionals). The cure (U13's plan §2): split the valued evaluation field `E`
(char 0) from the residue/letter field `L`; the re-typed bundle + the corrected 30–45-node
campaign are in `docs/in-progress/S2_SOURCE_PLAN_2026-08-24.md`. The same caveat applies
to C130s18's S2 socket applications (general-`ChainRealization` forms unaffected).
