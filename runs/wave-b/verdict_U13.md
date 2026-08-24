# U13 verdict — S2SourceFrontier inhabitation

Date: 2026-08-24  
Verdict: **REFUTED AS TYPED; concrete construction can only be reconsidered after an ambient split**

## Result

`S2SourceFrontier h2 hq L` has no inhabitant under its stated assumptions.  The obstruction is
already in `NodePointSource`, before any FGMN field or compatibility field is used.

At S2 the terminal field `Kt = (s2DepthTwo h2 hq).fld 2` has cardinality two.  Since the
frontier assumes `[Algebra Kt L]`, `(2 : L) = 0`; consequently every
`coeffHom : O →+* L` sends `2` to zero.  Apply the node laws at the live level `i = 2` to
`A = Polynomial.C (2 : O)`:

* `h2 : Irreducible (2 : O)` gives `A ≠ 0`;
* `A.natDegree = 0 < Dcum 2 = 4`;
* `point_exists` supplies a point in the required slot;
* `pointHgt_eval` and `value_zero` give `pointHgt 2 x A = ⊤`;
* `slot_value` and `hgt_ne_top` give `pointHgt 2 x A ≠ ⊤`.

This contradiction is formalized by `no_s2_node_source` and `no_s2_source_frontier` in
`leanfinal/scratch/U13_probe.lean`.  The probe exits zero with no `sorry` or axiom declaration;
the printed dependency footprint is `[propext, Classical.choice, Quot.sound]` for all four
named probe theorems.

## Design consequence

The conditional funnel in C130s17/C130s18 remains valid, but its S2 premise is empty.  Finite
development computation, general MacLane theory, or extra FGMN citations cannot inhabit the
current type.

The conservative interface repair is to split the ambients:

* a valued field `E` receives `coeffHom : O →+* E`, point coordinates, and `valueOn`;
* the characteristic-two field `L`, still an algebra over the terminal residue field, receives
  residue letters and canonical reads.

No `E → L` map and no identification of CC node points with FGMN roots is justified.  This
preserves the U12 false-dictionary fence.

## Feasibility after repair

A concrete depth-two route is plausible, but not computationally finite.  Use the landed
`dev`/`dvSupp`/`twistRead` machinery to define the two polynomial values and residual operators,
prove their universal laws, and extend the values to a common rational-function field using
mathlib's localization valuation API.  Mathlib supplies Gauss-norm multiplication, valuation
localization, and extension relations, but no augmented/MacLane valuation, `AdjoinRoot`
valuation constructor, Newton-polygon package, or FGMN residual-operator API.

The first genuine inductive blocker is `NodePointSource.value_mul`: the universal product law
for the level-two weighted-development value.  The further large cores are
`FGMNSourceLaws.graded_mul`, `normalized_mul`, `key_criterion`, and
`initial_iff_residual`.  Depth two fixes recursion depth but does not bound the degree or number
of development coefficients of arbitrary input polynomials.  Existing C.66/C.66b multiplication
results are too narrowly fenced to discharge the universal normalized-product field.

The corrected all-Lean source is estimated at 30--45 focused 30--60 minute nodes, about
20--35 engineer-hours after the signature repair, with significant risk in development
convolution and initial-form/key-polynomial theory.  The exact per-field analysis, dependencies,
and node schedule are in `docs/in-progress/S2_SOURCE_PLAN_2026-08-24.md`.

## Files delivered

* `docs/in-progress/S2_SOURCE_PLAN_2026-08-24.md`
* `leanfinal/scratch/U13_probe.lean`
* `runs/wave-b/verdict_U13.md`

No file under `leanspec/` or `leanfinal/Uniformity/`, and no roll-up, was edited.  No commit was
created.
