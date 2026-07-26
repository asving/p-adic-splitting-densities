Verdict: **UNSOUND**, though NOTE [1] D4-R is sufficiently isolated to begin drafting. The main campaign should not be treated as architecture-complete until the state definition, cone summation, leakage, and aggregate census logic are repaired.

## Pass-2 dispositions

1. **C1 — VAL.1 / joint calculus: GENUINE BUT INCOMPLETE.**

The correction

> “THREE cells — FG … c_V = 1 … FL … c_V = 0 … FS … c_V = 0”

is correct. Upgrading scalar VAL.2 to

> “VAL.2J … the JOINT distribution … constant on products of ANCHOR-TWISTED VAL.1 cells (or an explicit common refinement)”

also recognizes the right problem. But “or an explicit common refinement” postpones the decisive issue: the refinement must be finite, \(p\)-independent, polynomial-counted, and included in the state type. As written, M2 records only the multiset of individual factor cells, not joint relational strata.

2. **C2 — the (†) census epistemics: GENUINE FOR INDIVIDUAL COUNTS, NOT FOR THE CLAIMED AGGREGATES.**

For a fixed integer-valued count \(C_S(q)\), the argument is valid. If \(R=A/B\in\mathbf Q(q)\), with \(A,B\in\mathbf Z[q]\) coprime, is integral at every prime power, then \(B(q)\mid A(q)\). A Bézout/resultant argument bounds \(\gcd(A(q),B(q))\) uniformly, so a nonconstant \(B\) is impossible along an unbounded set of prime powers. Hence \(R\) is a polynomial. The bound \(0\le C_S(q)\le q^{W(S)}\) then forces degree at most \(W(S)\).

Consequently, after \(W(S)+1\) distinct exact values determine the interpolant, one further exact mismatch really does conclusively refute universal \(R\in\mathbf Q(q)\). This part is sound.

The extension

> “The same rule governs σ-aggregates (clear the \(p^{-A}\) denominators to restore integrality; degree bound \(\max_S W(S)\) + the A-shift)”

is not established. A final or depth-resummed \(\sigma\)-aggregate has geometric denominators such as \(1-q^{-a}\), and there need not be one finite “A-shift” making it an integer-valued count. The rule works for a specified finite sum with a displayed common monomial normalization; it does not automatically apply to the completed density. Thus the claimed “wild-p mismatch … is the WALL, demonstrated conclusively” is currently too strong.

3. **C3 — DAG cycle: GENUINE.**

The split

> “[2a] SPECIES … feeds [1v]”  
> “[2b] STATE-GEOM … consumes [1v]”

does remove the syntactic cycle, and the missing edges into EXHAUST are now shown. No graph cycle remains.

There is, however, a semantic ambiguity between finite raw species and shapes with unbounded loop parameters; see Critical Obstruction 4 below.

4. **C4 — M2 label closure versus lumpability: GENUINE REFORMULATION, INSUFFICIENT STATE.**

The plan now correctly asks for

> “any two CONCRETE states of one type have IDENTICAL full outgoing one-step laws”

rather than mere closure of labels. That is the correct theorem.

But the proposed state

> “the multiset over residual factors of (degree, multiplicity, ANCHOR-TWISTED VAL.1 cell …)”

does not record joint relations among factor values. Two configurations can have the same multiset of individual cells while differing in ratios, traces, norms, collision relations, or shared-parent correlations that affect the next joint law. VAL.2J itself anticipates a “common refinement,” but M2 does not put that refinement into \(\tau\). The state definition therefore does not presently support the theorem it is supposed to prove.

5. **C5 — STATE probe disposition: MOSTLY GENUINE, BLOCKING SCOPE TOO NARROW.**

REV 3 accurately says:

> “probe-level NO-WALL”  
> “it does not establish RS.0”  
> “the vtx-VARYING regime is untested”

and reopens the gate. That is proper weighting.

But STATE-probe-2 is declared blocking only for acceptance of [3]. It directly tests M2(ii), which is a theorem of [2b]. A failure would invalidate the proposed state space before RESUM begins. It must therefore block acceptance of [2b] as well as [3].

6. **C6 — WEIGHT-CHARGE: GENUINE DEMOTION AND VALID ALGEBRAIC REDUCTION.**

The plan correctly demotes X.1b to an open kernel and states:

\[
d_{\rm total}
 \le \frac{v_p(\operatorname{disc} f)}2+s(n)v_p(\operatorname{disc} f),
\]

so the displayed consequence is valid if WEIGHT-CHARGE is proved. The major consumers are visibly tagged conditional.

This repair does not, however, supply RS.3’s uniform \(B(n)\)-step leakage; see Critical Obstruction 3.

7. **C7 — normalized kernel: PARTLY GENUINE.**

Defining \(K_e\) as conditional masses of disjoint measurable continuation events is the right normalization. If those events are indeed an exact, nonoverlapping subfamily of the source cylinder, their row sums are at most one.

But “substochastic by construction” is conditional on three still-unproved facts: exact cone-domain enumeration, D4R.0 disjointness after height grouping, and lumpability making the quotient by \(\tau\) well-defined. It is not yet an unconditional consequence merely of writing the ratio.

## Critical obstructions

1. **CRITICAL OBSTRUCTION — necessary cones are used as exact summation domains.**

MENU explicitly says:

> “NO claim that the lattice points exhaust realizability”

and M4a supplies only necessary conditions. Yet RS.1 says:

> “per shape, Fubini the cone-lattice sum”  
> “per-direction sums are geometric series over congruence sublattices”

That step requires an exact description of the realizable parameter domain, or a theorem that every omitted/nonrealizable point contributes zero and that this zero pattern is itself translation-invariant. M4b-T only discusses value-count translation; it does not prove geometric realizability of all lattice points. Summing a containing cone overcounts histories.

Required repair: state an exact semilinear parameter theorem, or partition the cone into finitely many exact admissibility classes with polynomial per-class counts.

2. **CRITICAL OBSTRUCTION — M2 omits the joint refinement demanded by VAL.2J.**

Individual twisted-cell labels do not determine the full joint outgoing law. Either \(\tau\) must contain the finite joint relational stratum, or VAL.2J must prove that all relevant joint relations are conditionally determined by the current individual-cell multiset. The present M2/VAL.2J interface does neither.

3. **CRITICAL OBSTRUCTION — WEIGHT-CHARGE cannot yield uniform \(B(n)\)-step leakage.**

RS.3 claims:

> “there exist \(B=B(n)\) … bounded via the menu diameter + X.1b’s STALL budget”

But WEIGHT-CHARGE only gives

\[
\#\text{zero-gain nodes}\le s(n)\,v_p(\operatorname{disc} f).
\]

The discriminant valuation is unbounded across a source cylinder. Thus this permits arbitrarily long finite zero-gain runs and gives no \(B\) depending only on \(n\). Termination of individual paths also does not imply a uniform spectral gap.

RS.3 needs a separate probabilistic escape lemma—perhaps a uniform positive exit probability in a bounded number of steps—or a weighted-norm/renewal argument that tolerates unbounded run lengths.

4. **CRITICAL OBSTRUCTION — VALUE alternates between finite species and unrolled shapes without a fixed degree bound.**

The raw catalogue forgets

> “all self-loop repetition counts (depths)”

while Theorem VAL assigns a single \(C_S\) and \(W(S)\) to each raw shape. An unrolled history with \(k\) loop reads normally has \(k\) sets of fresh value choices, so its pool dimension grows with \(k\). Conversely, RESUM needs local one-move coefficients, not one count for an arbitrary completed loop family.

The plan must distinguish:

- finite local transition species, each with its own fixed \(W\);
- unrolled finite histories, whose \(W\) depends on the loop parameters; and
- resummed loop families, which need not be integer-valued polynomials.

Without that separation, (†), M4b, and RS.2 refer to different objects under the same \(C_S\) notation.

5. **CRITICAL OBSTRUCTION — the aggregate version of (†) is not justified.**

A surplus mismatch conclusively refutes a fixed degree-bounded integer count. It does not conclusively refute an arbitrary rational density unless a finite common normalization and its degree bound are first proved. R1’s aggregate wall protocol must be restricted to an explicitly normalized finite census quantity or supplied with a separate rational numerator/denominator bound.

6. **CRITICAL OBSTRUCTION — SQ.1 invokes a tail estimate as a pointwise box bound.**

SQ.1 says:

> “\(v_p(\operatorname{disc} f)\) is bounded on the decided level-\(N\) box (Lemma 3.3’s tail at box level)”

Lemma 3.3 is a measure bound; it does not imply a pointwise discriminant bound on a finite-level box. Residue boxes can contain discriminant-zero polynomials and lifts with arbitrarily high discriminant valuation.

A separate lemma may be true: a history whose decision threshold is at most \(N\) has its relevant discriminant/index budget bounded in terms of \(N\). But that must be proved from decision stability, not from the tail inequality.

7. **CRITICAL OBSTRUCTION — STATE-probe-2 must gate [2b], not merely [3].**

Because the probe tests the defining M2 lumpability claim, accepting STATE-GEOM before it passes would violate the plan’s own sealed-gate protocol. This is a governance defect with mathematical consequences: every downstream type-indexed count presupposes [2b].

## Concerns

1. **CONCERN — D4R.0 conflates a history with a history prefix.**

The statement

> “\(S(H,\top)=\{f:H_{\rm can}(f)=H\}\)”

is appropriate for a complete history. For an incomplete prefix it should be “\(H_{\rm can}(f)\) has prefix \(H\).” The distinction affects terminal exhaustiveness and what Theorem C with \(Z=\top\) is being applied to.

2. **CONCERN — M4b-T’s “cell-preserving” assertion needs a precise equivariance statement.**

Changing the lattice point changes the exponent in the anchor monomial. The natural result may be a bijection between two differently twisted stratifications, not preservation of one fixed cell label. If types are relabeled under translation, RS.0 and the matrix indexing must incorporate that permutation.

3. **CONCERN — “the only position-dependent factor” is asserted before the normal-form audit.**

The claim that all other residual coefficients, factor collisions, and lift choices are position-independent is exactly what M4b-T must prove. It should be presented as the target conclusion, not as already established motivation.

4. **CONCERN — the R2 summary misnames the probed regime.**

The record calls it

> “the value-varying n = 4 configuration”

after explaining that vtx was rigid and only an untyped retained value varied. Elsewhere the distinction is handled correctly, but this wording invites later overcitation.

5. **CONCERN — conditional tagging is not consistently repeated at checksum/capstone statements.**

RS.4 says the series equals one “by [5],” and SQ.4 states Theorem U without an inline conditional qualifier. The global text acknowledges X.1b is open, but acceptance records should explicitly prevent RS.4, [3], [4], and the capstone from being marked unconditional before WEIGHT-CHARGE closes.

6. **CONCERN — an unbounded legal zero-gain chain is not automatically “a hole in the termination story.”**

Unbounded finite chain lengths across inputs are compatible with almost-everywhere termination. Even an infinite chain on a measure-zero degenerate input may be compatible with a density theorem. It would defeat the proposed envelope or uniform leak argument, but the exact termination consequence depends on L5fix’s quantifiers.

## Probe weighting

The evidence is mostly weighted correctly. REV 3 repeatedly states that both probes are exploration-class, “never acceptance evidence,” and that the state probe exercised only selected rows. The fixed-frame failures are appropriately used as design warnings, not as proof of the twisted theory.

The two remaining overstatements are:

- calling the n=4 state probe “vtx/value-varying” when vtx was rigid; and
- using the aggregate census language as a “conclusive wall” without first establishing a valid finite normalization and degree bound.

## Draft readiness

NOTE [1] D4-R is ready to be drafted first, because its canonical-policy partition argument and pool inequality do not depend on the unresolved RESUM architecture. Its draft must cleanly distinguish complete histories from prefixes and prove all three named D4R.0 obligations.

The campaign as a whole is not ready to be regarded as a sound assembly architecture. Before [1v]/[2b] are accepted, it needs:

- an exact realizability domain for cone summation;
- a joint-refined state definition;
- a clean separation of local species, unrolled histories, and resummed families;
- a separate uniform escape/spectral-radius argument;
- and a corrected aggregate census protocol.

**Counts:** 7 CRITICAL OBSTRUCTIONS, 6 CONCERNS.

**Final verdict: UNSOUND.**
