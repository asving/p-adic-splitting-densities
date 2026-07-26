The REV 2 dispositions are mixed. The canonical-policy rebuild and the cone/arithmetic split are genuine repairs. The VALUE fallback, STATE closure, STALL argument, and associated gates are not yet structurally adequate. The resolved probe is useful negative evidence, but it does not satisfy the STATE-probe specified by REV 2 and does not establish RS.0.

## Critical obstructions

1. **CRITICAL OBSTRUCTION — VAL.1’s worked stratification is already incorrect.**

The plan gives as its model example:

> “the counterexample's target space stratifies as \(\{t \notin \mathbf F_q\cdot\alpha\}\) with \(c_V=1\) versus \(\{t\in\mathbf F_q^\times\cdot\alpha\}\) with \(c_V=0\)”

For \(V(A,B)=A\alpha+B\) with \(A,B\in\mathbf F_q^\times\), this is false. If \(t\in\mathbf F_q^\times\), then \(t\notin\mathbf F_q\alpha\), but realizing \(t\) requires \(A=0\), so \(c_V(t)=0\), not \(1\). The correct partition must at least separate:

- both \(\alpha\)- and constant coordinates nonzero: count \(1\);
- pure \(\alpha\)-line: count \(0\);
- pure constant line: count \(0\).

This is repairable locally, but it exposes the larger issue: scalar target strata do not automatically encode the joint correlations needed when one node supplies several linked children, collision conditions, or several transported values. VAL.2 only proposes a distribution of the singular quantity

> “vtx(parent)”

and a scalar pairing over cells. It needs a joint fiber calculus for every tuple of hinge values and sibling-collision data. The stated VAL.1/VAL.2 mechanism does not presently cover the classifier’s full linked-count problem.

2. **CRITICAL OBSTRUCTION — VAL.3 is not a defined fallback for the block recursion.**

The fallback says:

> “the TYPE-AGGREGATED sums \(\sum_{S\ contributing\ to\ \sigma} C_S(p)p^{-A(S)}\) are values of fixed elements of \(\mathbf Q(q)\)”

and:

> “A PROVED cancellation keeps RESUM alive at aggregate granularity”

But RS.0–RS.3 require rational coefficients before the final \(\sigma\)-aggregate: individual same-size transition blocks, source-state rows, mixed legs, and shallow terms. Cancellation visible only after summing all shapes contributing to a final \(\sigma\) does not produce a local matrix \(M_e(q)\), nor does it support induction in \(e\).

R8 acknowledges that RS.1 would have to be re-derived, but no replacement unknowns, transition law, closure theorem, DAG node, or solvability argument is supplied. Thus VAL.3 is a research possibility, not a fallback inside the stated architecture.

The R1 wall experiment is also logically impossible as written:

> “differs from every \(\mathbf Q(q)\) interpolation of the tame/prime-power values”

Any finite table of values at \(q=2,3,4,5,7,8,9,11,13\) has a polynomial, hence rational, interpolation. Finite exact data can refute a sealed formula or a bounded-degree ansatz; it cannot refute membership in \(\mathbf Q(q)\) without an independently proved structural family, recurrence, degree bound, or infinitely many values.

3. **CRITICAL OBSTRUCTION — the seven-note DAG is cyclic and omits a required edge.**

The declared execution order is:

> “[1] → { [1v] ∥ [2] ∥ [5] } → [2r] → [3] → [4]”

But MENU M2 defines state using:

> “the STRATUM … under [1v]'s VAL.1 stratification”

and M4b explicitly consumes:

> “[1v] VAL.2 + M2(ii)”

Conversely, Theorem VAL quantifies over:

> “each shape \(S\in\mathcal S_n\)”

whose finite, complete list is the output of MENU. So [1v] and [2] are not parallel independent notes as drawn; their current statements are mutually dependent. A simultaneous VALUE–MENU construction or a preliminary raw-species note is needed.

There is a second missing edge: X.2 says its envelope constants are

> “traced to X.1b + M4a tails”

so EXHAUST consumes MENU, although [5] is scheduled in parallel with [2]. The actual dependencies include at least \([2]\to[5]\).

4. **CRITICAL OBSTRUCTION — M2’s state is not shown to contain the data needed by M4b or RS.0.**

M2 defines state as:

> “(residual polynomial's shape, anchor \(a\), tower phase, the STRATUM of … vtx)”

This retains the residual polynomial’s shape, not its actual factor configuration, joint hinge data, sibling-collision context, or any proven invariant of the evaluation map. Yet M4b concludes:

> “the number of realizable value assignments is \(C_{S,\tau}(q)\) — a function of the shape and state type ONLY, not of the cone position”

and RS.0 concludes that every transition coefficient depends only on \(\tau\).

Neither conclusion follows from “the move maps state type to state type.” Closure of labels is different from lumpability of transition counts. The proof must establish that any two concrete states in one type have identical full outgoing laws, including linked joint distributions and all arithmetic admissibility conditions.

There is also an internal inconsistency: R2 describes retained state as

> “(vtx stratum, anchor, phase, position)”

while M2’s displayed definition omits position, and RS.0 says loop position adds nothing. The plan has not decided whether position is part of the type or a theoremically eliminable variable.

5. **CRITICAL OBSTRUCTION — the reported R2 probe does not satisfy REV 2’s own STATE-probe specification.**

REV 2 requires:

> “two same-shape, same-size states in DIFFERENT VAL.1 vtx-strata”

but then states the pass condition as:

> “same type \(\Longrightarrow\) same law”

Since the vtx stratum is part of the type in M2, states in different vtx strata are ordinarily different types. The gate specification is internally inconsistent unless “type” is meant to exclude the stratum for this comparison.

The actual probe establishes exact one-step equality for the enumerated same-type conditioned states at \(p=2,3\), plus one specified cross-height comparison. That is legitimate evidence for those rows. But its recorded limitations are decisive:

- one-step law only;
- no vtx-stratum variation below \(n=6\);
- only the tested positions/heights;
- no test of multi-step Markov/lumpability;
- no test that cone position or accumulated linkage data remain irrelevant.

Thus “NO-WALL” is valid only as a probe-level statement meaning “no counterexample in this census.” It does not support RS.0 in the sense claimed by the plan, and because the required different-stratum configuration was not exercised, the planned STATE gate should still be recorded as incomplete rather than resolved.

6. **CRITICAL OBSTRUCTION — X.1b’s stated premise does not imply its claimed affine discriminant bound.**

X.1b proposes:

> “\((\#\text{zero-gain nodes})\le s(n)\cdot(\text{local height budget})\)”

and immediately claims:

> “HONEST consequence: \(v_p(\operatorname{disc}f)\ge c_1(n)d_{\rm total}(H)-c_2(n)\)”

That implication is missing. A local height budget can itself be arbitrarily large. To deduce an affine lower bound in total node count, the plan needs an explicit inequality controlling the sum of all such height budgets by genuine index gain, discriminant valuation, or another globally coercive quantity. Merely saying that the ladder is “capped by the … different budget” does not display the required comparison.

Without that bridge, arbitrarily long zero-gain runs proportional to an arbitrarily large height budget remain compatible with bounded \(d_{\rm gen}\). The depth envelope used by RS.1 and the finiteness claim used by SQ.1 therefore do not follow. This does not genuinely dispose of pass-1 C7 yet.

7. **CRITICAL OBSTRUCTION — the matrix normalization needed by RS.3 is undefined.**

The recursion is written as

> \[
> \beta_{e,\cdot}
> =q^{-e(e-1)/2}M_e(q)\beta_{e,\cdot}+\mathrm{SHALLOW}_{e,\cdot},
> \]

while \(M_e\) is described as having entries equal to

> “[1v]-counted one-move coefficients”

RS.3 then treats \(M_e(p)\) as a substochastic transition matrix. The plan does not specify whether fresh-volume costs, cone sums, multiplicities, and the displayed exterior factor have already been included in \(M_e\). A matrix obtained by resumming several heights or shapes need not have row sum at most one merely because the underlying disjoint one-step cylinders do.

The LEAK argument is valid only after a precise probabilistic normalization proves:

\[
K_e(p):=p^{-e(e-1)/2}M_e(p)\ge0,\qquad
\sum_{\tau'}K_e(p)_{\tau,\tau'}\le1,
\]

with strict eventual leakage from every closed communicating class. Direct one-step leakage from every state, which REV 2 demands, may be unnecessarily strong and may be false for forced recentering states. Until \(K_e\), rather than ambiguously \(M_e\), is tied to disjoint conditional masses, the Neumann argument is not licensed.

## Concerns

1. **CONCERN — the canonical-policy Hist rebuild is a genuine repair, but D4R.0 remains the entire burden.**

The changes

> “a deterministic TOTAL map \(f\mapsto H_{\rm can}(f)\)”  
> “a literal SET of histories, NO quotient”

correctly remove the invalid lift-orbit aggregation. Likewise,

> “strata are FIBERS of a map”

is the right way to prove disjointness.

This disposition is genuine architecturally. It still requires proof that the canonical choice is defined at every eligible recentering, that all terminal outcomes are included, and that two putatively common prefixes really induce identical common frames before the next read.

2. **CONCERN — D4R.1 uses ambiguous terminal-system notation.**

The repeated phrase

> “Theorem C(b) with \(Z=\varnothing\)”

is dangerous. If \(Z\) is a terminal locus, \(\varnothing\) normally has zero volume; the unconstrained terminal system should be a full/tautological locus. The note must fix this notation before its mass equations can be checked literally.

3. **CONCERN — the M4a cone repair is genuine, but M4b is substantially stronger than the repair table admits.**

REV 2 correctly retreats to:

> “NECESSARY cone + congruence-lattice geometry only”

and routes arithmetic realizability elsewhere. That genuinely fixes pass-1 C3 at the MENU-statement level.

However, independence from cone position is a new arithmetic assertion. Heights and strides can alter exponents, anchor maps, available digits, or which collision equations occur. It cannot be obtained solely from VAL.2 plus the existence of a type map; it needs a translation or normal-form theorem comparing evaluation families at different lattice points.

4. **CONCERN — REL recognizes the right missing theorem, but REL.2 is not a consequence of REL.1.**

The new note genuinely acknowledges the pass-1 scope debt. Still, proving Theorem C over \(O_\delta\) does not show that a conditioned subcluster over \(\mathbf Z_p\) is Haar-distributed as a monic polynomial over \(O_\delta\). REL.2 must establish the coordinate identification, normalization/Jacobian, independence from sibling conditions, and compatibility with the canonical lift policy.

The single \(p=2,\delta=2,n=4\) gate is a useful falsifier, but both sides appear to use MOVES strata. An independent description of the conditioned \(\mathbf Z_2\)-slice is needed to avoid a shared normalization error.

5. **CONCERN — X.1a’s assertion that all increments are genuine is not justified by naming GMN.**

The plan says \(d_{\rm gen}\) includes:

> “all increments”

Every such species must be checked to contribute at least one unit of index. Producing an on-side lattice point is insufficient unless it is a point counted by the precise GMN index formula rather than an endpoint or otherwise zero-contributing point. This is exactly the sort of convention error that caused the pass-1 EXHAUST failure.

6. **CONCERN — SQ.1 cites too little for finite truncation.**

A STALL bound proportional to height does not alone show that threshold-\(\le N\) histories have bounded node count. SQ.1 must combine:

- a threshold-\(\le N\) bound on every relevant height;
- the corrected global STALL inequality;
- a bound on genuine events.

At present it cites X.1b alone.

7. **CONCERN — several “exact” gates are exact but not independently discriminating at the claimed layer.**

Examples:

- RESUM-n3 uses PARI for the final factorization type, but assigning a polynomial to a “depth-row” still uses the history extractor under test.
- REL-n4 compares two MOVES-based computations unless the conditioned \(\mathbf Z_2\) slice is generated independently.
- EXHAUST-n3 and MENU-n3 cover only \(n=3\), where the plan itself records weak exercise of deeper species.
- Passing finitely many exact gates never proves a universal identity; it only falsifies sealed formulas. The proof passes must remain primary.

The revised protocol mostly acknowledges this, but the risk register sometimes overstates what a gate can decide.

8. **CONCERN — the STATE probe’s cross-height result is narrower than “loop position carries no further information.”**

The reported equality of the S1 marginal and S2 word over 16 cells is good exact evidence for that comparison. It does not cover arbitrary loop number, arbitrary height congruence class, changes of anchor, or histories in which earlier linked choices create correlations invisible to the tested marginal. RS.0 needs either a symbolic conjugacy/Markov proof or a finite-state bisimulation argument, not extrapolation from this check.

## Pass-1 disposition assessment

- C1, false torus lemma: **genuine retirement; replacement not yet adequate**.
- C2, lift quotient: **genuinely repaired** by canonical fibers.
- C3, cones versus arithmetic realizability: **genuinely repaired at the statement level**; M4b adds an unresolved burden.
- C4, missing coefficient bridge: **honestly exposed, not repaired until VAL succeeds**.
- C5, triangular closure: **redesigned rather than proved; current state definition and probe are inadequate**.
- C6, relative measure: **genuine architectural repair**, subject to the substantial REL.2 conditioning theorem.
- C7, zero-index recenterings: **not genuinely repaired**, because the displayed STALL premise does not imply the asserted affine discriminant bound.
- C8, nondiscriminating gates: **partially repaired** by exact censuses and independent factorization types, but R1’s finite-data wall rule is impossible and the R2 gate was not exercised in its prescribed stratum-varying regime.

The seven pass-1 concerns are mostly addressed honestly: the degree bound, removal of quotient finiteness, common-frame partition obligation, matrix rather than scalar inversion, explicit coercivity target, and named SQ.1 finiteness dependency are real improvements. They remain proof obligations, and the matrix, coercivity, and finiteness items still contain the gaps identified above.

**Counts: 7 CRITICAL OBSTRUCTIONS, 8 CONCERNS.**

**Verdict: UNSOUND.**
