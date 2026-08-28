# Verdict A0G — uniform general-`n` `a0`

**Date:** 2026-08-28  
**Route adjudication:** **BLOCKED as a theorem today; select the PURE-ENGINE architecture;
reject the presently available cite-backed route as a closure.**

## The uniform theorem

The capstone-strength endpoint is

```lean
theorem decidedSliceAt_all : ∀ n : ℕ, DecidedSliceAt n := by
  intro n
  exact decidedSliceAt_of_clusterRecursion n
```

It includes `n=0`; that base cannot be discarded behind the positive-degree guard in
`UniformityStatementDecided`.

## Why the route is blocked

The post-A0C dv-graded Hensel engine is genuinely degree-generic.  In particular,
`C133mh9.theoremA`, `C133mh3.dvResPoly_mul_gen`,
`C133mh11.dv_oneSlope_split_unique`, `C133mh13.theoremC_placement`,
`C133mh15.blockFrontier_of_context`, and the `C134*`/`C136*` level machinery split a supplied
Newton/MacLane block with exact factors, degrees, purity and residual data.  The generic type
algebra `typeOf_of_residual_coprime`, `typeOf_shift`, and `typeOf_scaleRoots` supplies the
corresponding algebraic legs.

What is not landed is the one theorem the engine cannot manufacture:

```lean
theorem finiteGenreCoverAt_all : ∀ m : ℕ, FiniteGenreCoverAt m
```

Here `FiniteGenreCoverAt m` means a finite list of parametric NP/OM schemas which is disjoint
and exhaustive on the coefficient box, whose non-loop recursive children all have mass `<m`,
whose unbounded depth parameters sum to exact rational functions of `q`, and whose output types
are certified by the engine.  A finite output `FactorizationType` menu
(`IFC6.exists_uniform_coveringMenu`) is not such a coefficient-space cover.

The cubic mass/fixed-point/drainage architecture is only partly generic:

* `decidedSeq_tendsto` is already generic, and the fixed-point algebra generalizes;
* the size-`m` conditional rescale factor is `q^(-m(m-1)/2)`, while the full-box common-centre
  loop is `q^(1-m(m+1)/2)`; at `m=3` this is IFC7's `q^-5` step;
* IFC7's `density_ge_of_step`, its four concrete families, `totalMass_three`, and
  `drainageAt_three` are degree-three declarations;
* `H98.drainage_of_package` is conditional on `∀ n, InductionPackage n`, so an all-degree
  lower-bound-plus-mass squeeze would inherit the open drainage campaign.

The chosen uniform route therefore proves exact disjoint recurrences for `decidedDensity`
directly and uses `decidedSeq_tendsto`; it does not route through `genuineDensity` or assume
uniform drainage.

## Pure engine versus citation

FGMN, *Residual ideals of MacLane valuations*, Theorem 6.6, supports the local
slope/residual-label dissection already isolated in `C33Cite.lean`.  It does not state finite
uniform coefficient genres or rational measures.  The rank-one termination theorem in
Alberich-Carramiñana–Guàrdia–Nart–Poteaux–Roé–Weimann, *Polynomial factorization over
henselian fields*, is in a factorization section assuming a monic square-free input and
`char(k)=0` or `char(k)>deg(g)`; it cannot cover the wild primes quantified by
`DecidedSliceAt n`.  Pointwise termination would in any event not imply a finite rational cell
grammar.

A future hybrid cite is acceptable only for an exact all-characteristic local
factorization/termination clause, with its hypotheses bound explicitly.  Lean must still prove
the finite schema list, disjoint exhaustion, measures, geometric summation, and type
faithfulness.  A cite or axiom asserting rational density directly is not faithful.

## Blueprint and critical path

The full blueprint is `docs/in-progress/A0_GENERAL_2026-08-28.md`.  It contains 16 nodes,
estimated at 8,000–14,000 lines:

```text
residue patterns/census ─┐
generic coefficient boxes → NP schemas → Hensel binding → child decrease
                                                   ↓
                                  A0G-GC finite genre cover  [STOP LINE]
                                                   ↓
                      rational weights + rescale fixed point
                                                   ↓
                   strong cluster induction → affine assembly
                                                   ↓
                  DecidedSliceAt n → ∀ n, DecidedSliceAt n
```

**Single highest-risk node:** `A0G-GC`.  Work downstream of that node may be prototyped, but it
must not be presented as a proof of the general theorem until the classifier is exhaustive and
disjoint in arbitrary degree.

## Quartic reality check

`verification/a0g_quartic_cert.py` implements the degree-four table using the eleven residue
divisor patterns `(δ,m)` and their exact finite-field counts.  A `--fast` run completed
**32 checks with 0 failures**:

* the eleven rational densities sum to one and have expected root count `q/(q+1)`;
* q=2 and q=3 anchors match exactly and all tested masses are positive;
* exhaustive residue factorization at `p=2,3,5,7` matches the eleven symbolic genre counts,
  which sum to `q^4`;
* an independent eleven-row cluster convolution agrees termwise with both the displayed table
  and `om_density_engine.alpha_full(4)`;
* PARI/GP quartic factorization samples at `p=2,3,5,7`, including the wild prime, pass every
  four-sigma gate with no stray shapes.

This certifies the quartic table as a degree-four computational target.  It is not evidence of
genre completeness at `n≥5` without `finiteGenreCoverAt_all`.

No landed `.lean` or leanspec file was edited.  No git operation was performed.
