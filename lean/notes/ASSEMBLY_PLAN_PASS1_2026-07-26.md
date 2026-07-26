The architecture is unsound as written. The main obstruction is concrete: D4R.3’s torus lemma is false in the stated generality. Several later claims then rely on precisely the uniformity it was supposed to establish.

## Critical obstructions

### 1. D4R.3’s torus lemma is false for extension-valued vertices

> “The number of side-pattern values with a GIVEN residual shape and GIVEN lead value vtx ∈ F_{i+1}ˣ is independent of the vtx value”

and

> “scale the pattern by the torus action z ↦ u·z, u ∈ Fˣ, which permutes shapes' realizations shape-preservingly”

**CRITICAL OBSTRUCTION.** The indicated torus is only \(F^\times\). When
\(F_{i+1}=F[z]/(\psi)\) has degree \(g>1\), it cannot act transitively on
\(F_{i+1}^{\times}\): its orbit size is at most \(q-1\), versus
\(q^g-1\) possible nonzero vertex values. Substitution \(z\mapsto uz\) also transports
\(\psi\), rather than giving an action on the fibers for a fixed \(\psi\).

There is a direct candidate counterexample shape. Let \(\psi\) be irreducible quadratic
over \(F_q\), put \(\alpha=z\bmod\psi\), and consider, for \(\mu\ge2\) and \(a>0\),

\[
R_{\rm anch}(z)=z^a\psi(z)^\mu(Az+B),\qquad A,B\in F_q^\times .
\]

The residual degree–multiplicity shape is fixed. Up to the fixed nonzero monomial
factor appearing in the definition of `vtx`, the vertex value is

\[
A\alpha+B\in F_{q^2}^{\times}.
\]

Because \(1,\alpha\) are an \(F_q\)-basis, a target \(A\alpha+B\) determines
\((A,B)\) uniquely. The target \(\alpha+1\) has one admissible realization
\(A=B=1\), whereas the target \(\alpha\) would require \(B=0\), prohibited by the
nonzero endpoint convention. Thus the fiber counts are respectively one and zero.
Multiplication by the fixed \(\alpha^{a-\mu\widehat m}\) merely permutes the targets and
does not restore uniformity.

Possibly the classifier reaches only a restricted subset of vertex values, but that
would be an additional theorem. D4R.3, as universally stated, is false.

### 2. Quotienting lifts does not justify the exact aggregation formula

> “The value fiber: Hist(P̂) := { realizable lift-carrying histories H with shape P̂ }, taken up to lift-transport”

and

> “M3 makes this quotient honest”

**CRITICAL OBSTRUCTION.** The accepted lift-translation remark gives an equal-mass
bijection between a stratum and a correspondingly transported stratum. It does not say
that the two strata are the same subset of the original coefficient box, nor that one
may discard all but one representative while computing the mass of their union.

Consequently, “equal mass on transport classes” is insufficient for

\[
\mu(\widehat P)=C_{\widehat P}(p)p^{-A(\widehat P)}.
\]

A deterministic canonical-lift classifier might avoid multiplicity, but D4-R instead
defines `Hist(P̂)` modulo transport. Theorem C expressly warns that with downstream
data literally fixed, no correspondence is claimed.

### 3. MENU’s “product of cones” statement ignores arithmetic realizability

> “the realizable histories of shape S are exactly the lattice points of an explicit product of cones”

and

> “per-cone sums are products of geometric series”

**CRITICAL OBSTRUCTION.** Polygon heights do produce linear inequalities, but the full
realizability predicate also contains:

- lattice/congruence conditions from slopes and anchors;
- factor-degree and irreducibility conditions;
- nonzero endpoint conditions;
- the extension-field equation `(HV)`;
- possible collisions between cofactor and residual factors.

These are not encoded by a product of ordinary \(\mathbb N\)-cones. The counterexample
above already shows that, for fixed numerical parameters, realizability can depend on
the actual extension-field target. Thus a shape’s numerical parameters are not
“exactly” the lattice points of a \(p\)-independent product cone in the asserted sense.
This is load-bearing for the claimed product-geometric resummation.

### 4. RS.2 does not follow from Theorem C or Claim 4.3

> “Every coefficient of (R_e) is one fixed element of ℚ(q)”

and

> “value counts are universal polynomials in the pool sizes Q = q^w”

**CRITICAL OBSTRUCTION.** Theorem C proves the mass of each fixed value-bearing history.
It says nothing about the number of histories satisfying finite-field factorization and
`(HV)` constraints.

Claim 4.3 about unrestricted per-shape counts in a pool does not imply that a fiber of
a constrained evaluation map has constant cardinality. Such fibers can depend on trace,
norm, subfield membership, coefficient-support conditions, or the actual irreducible
polynomial \(\psi\). In general, point counts of finite-field definable families need
not be a single polynomial in \(q\).

D4R.3 was the only proposed bridge from Theorem C to this coefficient-uniformity claim.
Since that bridge is false, \(p\)-independence of the system’s coefficients is not
derivable from the accepted perimeter.

### 5. The advertised scalar triangular system is not shown to be closed

> “FULLMONIC(e) is LINEAR in the unknown β_e … with knowns β_m(q^δ), m < e — triangular in e”

and

> “a self-loop step multiplies the cluster law by a FIXED ℚ(q)-factor independent of the loop's own depth position”

**CRITICAL OBSTRUCTION.** Bottom-up induction in cluster size is well-founded only after
proving that every same-size transition is the single, state-independent FULLMONIC
self-loop. The plan does not establish that.

The accepted history data retain anchors, residual factors, transported vertex values,
tower phases, and recentering state. Those data can change while the cluster size stays
\(e\). In particular, the candidate above shows that the number of legal successors
can depend on the transported vertex state even when all retained numerical “shape”
parameters agree. The resulting recursion may require same-\(e\) state-indexed
unknowns, potentially infinitely many if loop position retains information.

Thus the triangularity is currently an assertion of R2’s negation, not a consequence
of MENU or Theorem C.

### 6. Base change preserves formal rationality but breaks the proposed domination proof

> “the mixed legs β_m(q^δ) need the induction hypothesis at BASE-CHANGED arguments”

**CRITICAL OBSTRUCTION.** Algebraically, if \(\beta_m(q)\in\mathbb Q(q)\), then
\(\beta_m(q^\delta)\in\mathbb Q(q)\); the substitution itself does not threaten
rationality.

The obstruction is probabilistic. SQ.2 needs componentwise positivity and domination
at \(q=p^\delta\). The accepted Theorem C is stated for monic polynomials over
\(\mathbb Z_p\), while \(\beta_m(p^\delta)\) naturally represents a cluster law over an
unramified degree-\(\delta\) coefficient ring. Internal residue alphabets of size
\(p^\delta\) do not by themselves supply an ambient covering theorem or finite-level
domination theorem for that ring.

Hence the induction “first in \(m\), then evaluate at \(p^\delta\)” is formally
well-founded, but its required measure-theoretic induction hypothesis lies outside the
certified inputs.

### 7. EXHAUST states a node-count inequality its own kernel admits may be false

> “Every non-root node of a realizable MOVES history is a GMN descend/refinement event contributing ind_r ≥ 1”

but later:

> “the one place a MOVES-node species could fail to be a GMN event is the recentering with unchanged polygon data (improvement steps of zero index gain)”

**CRITICAL OBSTRUCTION.** These statements are incompatible. If a recorded recentering
can have zero index gain, counting every MOVES node as a unit event does not yield

\[
\text{depth }d\Longrightarrow v_p(\operatorname{disc}f)\ge2d.
\]

Even a uniform bound on the number of intervening zero-gain recenterings would only
produce a shifted or rescaled relationship, not X.1 as stated. Since X.1 feeds the
absolute-convergence argument, the undecided envelope, and all later squeezing, this is
not a local proof gap.

### 8. The five gates cannot discriminate the registered R1/R2/R3 failures

> “All gates are at n = 3”

**CRITICAL OBSTRUCTION.**

- **R1:** D4-n3 explicitly uses `μ = 1`, while R1 names the dangerous cases
  `μ ≥ 2 or a > 0`. For a cubic, a degree-two key cannot carry multiplicity two, so
  this gate structurally cannot exercise the advertised obstruction.
- **R1 again:** RESUM-n3 is a statistical frequency comparison. A small exact
  non-polynomial correction may lie inside the sampling bands or aggregate away across
  shapes. The engine comparison is not independent evidence if the engine uses the
  same value-count formulas.
- **R2:** A same-size state dependence first occurring at \(n\ge4\), order three, or
  after a phase absent from cubic histories is invisible to RESUM-n3.
- **R3:** A million random samples cannot certify absence of a rare shape. The
  requirement that every nonempty predicted row be observed “given the sample size”
  is not deterministic and fails for rows of mass below the sampling scale.
- **R3 again:** A species omitted both by the theoretical classifier and the extraction
  code will not appear as a “stray shape.”
- **SQUEEZE:** exact enumeration at \(p=3,N=8\) ranges over \(3^{24}\) coefficient
  boxes. “Stratified-exact” is unspecified and risks using the same stratum formulas
  whose domination is being tested.

The gates are useful counterexample searches, but they do not have the stated
discriminating power.

## Concerns

### 1. Unbounded residual degrees are probably not the MENU obstruction

> “w ≤ n!-bounded (residue degrees multiply along the tower, Σ e·f ≤ n at each stage)”

**CONCERN.** There is no evident unbounded-\(g\) counterexample if the standard degree
identity is available: a genuine increment multiplies the key degree by
\(e_{\rm read}g\), while a degree-preserving recentering has \(e_{\rm read}=g=1\).
Thus cumulative residual degrees are bounded by the fixed degree budget.

However, the plan alternates between \(g\), \(w\), cumulative residue degree, and
factor residue degree without displaying the invariant that relates them. The
conclusion is plausible, but “\(n!\)-bounded” is not yet a proof at arbitrary tower
order.

### 2. L5fix finiteness is not automatically finiteness of the proposed MOVES quotient

> “the quotiented skeleton has ≤ n − 1 proper-refinement internal nodes”

**CONCERN.** A change of key representative, anchor, residual polynomial, or tower
phase need not strictly refine the final \((e,f)\)-partition or increase
\(\sum e_if_i\). The plan invokes the different bound for “phases,” but it does not
give a map from every degree-preserving MOVES state change to one of L5fix’s bounded
phase invariants. The finite cluster-tree menu does not by itself establish finiteness
of this finer history-state quotient.

### 3. D4R.1’s disjointness is not supplied by Theorem C

> “different values ⟹ disjoint digit cylinders”

**CONCERN.** This is believable for a deterministic reader with a fixed lift policy,
but histories are compared after coordinate transports and lift quotienting. Theorem C
computes individual cylinder masses; it does not state that all value-bearing histories
in the proposed quotient are mutually disjoint in the original coefficient box.

### 4. D4R.4 has not justified a uniform threshold over its fiber

> “finite because Hist(P̂) is finite (fixed shape bounds all heights)”

**CONCERN.** A D4 shape-prefix retains heights, so the height part is bounded. But
histories literally carry \(p\)-adic lifts, and their finiteness is obtained only after
the disputed lift quotient. The accepted theorem provides \(N(H,Z)\) history by
history, not a uniform threshold over an inadequately defined transport quotient.

### 5. RS.3’s pivot argument is too weak for a coupled positive system

> “the pivot is 1 − w(e) ≠ 0”

and

> “each pivot is 1 − (positive mass < 1)”

**CONCERN.** If FULLMONIC acts on several types or retained states, the same-size block
is a nonnegative matrix, not a scalar. Positivity of individual transition masses or
diagonal entries does not establish invertibility, convergence of the Neumann series,
or componentwise domination. Those require control of the whole same-size operator.

### 6. X.2 is not implied merely by saying M4 has positive affine exponents

> “the depth-d envelope + the per-shape height tails beyond threshold N”

**CONCERN.** The connection between a history’s numerical heights and its finite
decision threshold \(N(H,Z)\) is not displayed. Mixed height cones can have directions
along which the nominal exponent grows while the required precision grows at a
different rate. An explicit exponential `env(N)` requires a uniform coercivity
statement, not just positivity of each written exponent.

### 7. SQ.1/SQ.2 silently require exclusion of zero-cost infinite refinement

> “the finite-N decided set is covered by strata of finite partial-sum families”

**CONCERN.** This finiteness follows only if a history with threshold at most \(N\)
cannot contain arbitrarily many moves contributing no new digit condition. The
zero-index recentering issue in EXHAUST is evidence that such steps need separate
control. Without it, the passage from the finite-level decided set to a finite
truncation of the history series is not established.

The base-change substitutions do not themselves harm rationality, and unbounded deep
residual degrees do not appear to be the actual MENU failure. The decisive problems
are value-fiber nonuniformity, unproved closure of the same-size recursion, the missing
relative base-change measure statement, and the false node-count premise in EXHAUST.

**Count: 8 critical obstructions, 7 concerns.**

**Verdict: UNSOUND.**
