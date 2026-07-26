## Structural pass 4

REV 4 makes several genuine repairs, especially the aggregate-census protocol, conditionality bookkeeping, and governance around STATE-probe-2. But the central JREF→STATE→RESUM interface still does not type-check, and the LOC/HIST/FAM separation is contradicted downstream by M4b. The current architecture is therefore not yet sound.

### Pass-3 dispositions

| Pass-3 finding | REV 4 disposition | Judgment |
|---|---|---|
| C1: necessary cones used as exact domains | Introduces “**M4a-X (EXACT-DOMAIN — NEW OPEN KERNEL)**” and makes RS.1 cite it | **PARTIAL / genuine relocation.** The overcount is no longer hidden, but Route A still needs a finite-generation/fundamental-domain proof; translation invariance alone does not imply the claimed finite semilinear decomposition. |
| C2: M2 lacks the joint refinement | Defines JREF and sets “**τ = (the JREF CELL …; anchor a; tower phase)**” | **NOT YET GENUINE.** JREF is not defined as a single source-state partition common to all possible outgoing species, and the local theorem does not provide the cell-to-cell polynomial transition tables needed downstream. |
| C3: WEIGHT-CHARGE cannot imply uniform leakage | “**The route is STRUCK on record**”; adds ESCAPE with E1/E2 | **GENUINE separation**, but ESCAPE remains open and E2 does not presently prove the stated finite-state \(B\)-step estimate. |
| C4: LOC/HIST/FAM conflation | Adds §1s and `unroll`/`resum` | **NOT GENUINE downstream.** The three labels are stated, but “history” still denotes incompatible objects, and M4b contradicts the CHAIN formulation for variable loop length. |
| C5: aggregate interpolation invalid | Restricts (†) to LOC/HIST and adds “**(†-AGG)**” | **GENUINE, with two dependencies to expose.** The canonical decided-count example requires a \(p\)-independent finite syntactic family and, for prime-power censuses, REL.1/REL.2. |
| C6: false pointwise discriminant bound in SQ.1 | Strikes it and adds SQ.0 | **GENUINE citation repair, incomplete lemma repair.** SQ.0(c) is not established as stated, and SQ.0(d) needs an exact-history argument rather than its present shorthand. |
| C7: STATE-probe-2 did not gate [2b] | “**must PASS before [2b] OR [3] is accepted**” | **GENUINE.** |
| K1: prefix/complete conflation | Displays two cases in D4R.0 | **PARTIAL.** The claimed union over completions still omits nonterminating maximal runs. |
| K2: M4b-T cell preservation imprecise | Adds \(\pi_v\)-equivariance/orbit alternative | **GENUINE.** |
| K3: anchor factor was premised | Makes it a “**TARGET CONCLUSION — proved, never premised**” | **GENUINE.** |
| K4: R2 misnamed probe regime | Renames it “UNTYPED-VALUE-varying, vtx-RIGID” | **GENUINE.** |
| K5: missing conditional tags | Adds inline tags and acceptance-record rule | **GENUINE.** |
| K6: unbounded stalls do not automatically contradict termination | Corrects X.1b/R4 language | **GENUINE.** |

## Critical obstructions

### 1. JREF is not a single state partition

REV 4 defines:

> “Per local species \(m\) … JREF(m) := the common refinement…”

but M2 later uses:

> “the JREF CELL of the FULL residual-factor tuple”

as though there were one partition attached to the current state.

A concrete current state can admit several outgoing move species. Species-relative partitions \(\operatorname{JREF}(m)\) do not automatically define one common source-state type. Consequently “same \(\tau\)” is not presently meaningful simultaneously for all possible outgoing moves.

The repair must define, for every bounded current-state skeleton \(s\),

\[
\operatorname{JREF}^{\mathrm{src}}(s)
=
\bigwedge_{m\in\operatorname{Out}(s)}
\operatorname{JREF}_{m}^{\mathrm{source}},
\]

including every source observable used by every admissible outgoing species. It must then define explicit target-cell maps for each transition \(m:s\to s'\). Finiteness follows only after using finiteness of the outgoing-species menu.

There is a second definitional problem: phrases such as “norm/trace strata to subfields” and “relational strata” do not specify the cells. A finite syntactic list of relations is not itself a partition with polynomial cardinalities. The actual predicates, target cells, and exceptional-characteristic conventions must be displayed.

### 2. Theorem VAL LOCAL is too weak for CHAIN, M2, and \(K_e\)

The stated LOCAL conclusion supplies only one total polynomial:

> “for each local move species \(m\) … ONE polynomial \(C_m\)”

J2 supplies cell sizes, while J3 supplies constancy of an outgoing law. Those facts do not supply the polynomial cell-to-cell transition numerators needed to iterate a chain.

The actual local theorem must give, for every source cell \(\alpha\), move species \(m\), full outcome label \(o\), and target cell \(\beta\),

\[
T_{m,o}^{\alpha,\beta}(q)
=
\#\{\text{fresh assignments producing }(m,o,\beta)\mid\alpha\},
\]

or an equivalent unnormalized joint-count table, and prove:

- every entry is in \(\mathbb Q[q]\);
- its degree bound is displayed;
- the rows partition the source assignment set;
- the table is independent of the representative inside \(\alpha\);
- source and target cells use the global JREF definition above.

Without these tables, “iterated pairing” is not a defined operation, M2(ii) is not proved by VAL.2J, and RS.2 cannot construct \(K_e\).

J2’s assertion that cells themselves have polynomial size is also insufficient: a fiber-constant value may still depend non-polynomially on \(q\). Both cell sizes and transition numerators need polynomiality.

### 3. LOC/HIST/FAM still do not compose

Section 1s says a HIST object is:

> “A shape PLUS a full \(\mathbb N\)-parameter tuple”

whose count \(C_H\) has degree growing with its loop parameters.

But the certified Theorem C uses a “lift-carrying history” with actual node values. D4-R’s `Hist(P̂)` also counts value-specific histories. Thus \(H\) is still used for at least two different mathematical objects:

1. a realized lift-carrying history;
2. a value-forgotten parameterized history template whose realizations are counted by \(C_H\).

These must receive different symbols.

More seriously, M4b claims:

> “At every lattice point … the number … is \(C_{S,\tau}(q)\) — a function of shape and state type ONLY, not of the cone position.”

Loop repetition count is one of the forgotten \(\mathbb N\)-parameters. A point with \(k\) loop reads has \(k\) fresh pools and generally a count given by a \(k\)-fold transition product. Section 1s correctly says its degree grows with \(k\). Therefore it cannot simultaneously equal one position-independent \(C_{S,\tau}\).

The repair must choose one of the following coherent formulations:

- Treat self-loop chains as paths in a finite weighted automaton. A length-\(k\) template has count given by a product of local transition matrices; only height coordinates that do not change path length may use M4b-T constancy.
- Refine “shape” to include the entire finite type path. Then there are infinitely many unrolled shapes, organized as a regular language and resummed by the matrix fixpoint—not as one finite shape with a position-independent count.

Until this is repaired, `unroll` followed by `resum` does not produce the RS.1 series claimed in the plan.

### 4. D4R.0 still mishandles nonterminating runs

REV 4 says:

> “for a PREFIX \(P\), \(S(P,\top)=\{f:P\preceq H_{\rm can}(f)\}\) (a prefix-fiber — the union of the fibers of all completions).”

But \(H_{\rm can}\) was defined only:

> “on terminating \(f\).”

A finite prefix cylinder can contain inputs whose canonical run is infinite. It is therefore not, exactly, the union of fibers of finite complete histories. Measure-zero nontermination does not repair an exact finite-cylinder partition statement.

The draft must extend the canonical classifier to a maximal finite-or-infinite run for every input. Prefix cylinders are then fibers of the finite-prefix map. Only a terminating complete history is a fiber of the finite-complete-history map.

This is a localized repair and does not destroy D4-R’s drafting independence, but the current quote is not a genuine resolution of pass-3 K1.

### 5. SQ.0(c) is not established as stated

SQ.0 asserts:

> “#zero-gain nodes \(\le n!\,w^*(N)\)”

because each recentering strictly raises “the current key’s weight” in \((1/n!)\mathbb Z\).

That argument bounds a single monotone ladder. A history can contain several keys, branches, or ladder restarts. One must bound the number of independent weight tracks and sum their budgets. The current constant omits that multiplicity.

An acceptable statement would have the form

\[
d_{\rm zero}(H)
\le L(n)\,D(n)\,w^*(N),
\]

where:

- \(L(n)\) bounds all zero-gain ladders/tracks in a degree-\(n\) history;
- \(D(n)\) is a common denominator for all possible key weights;
- every zero-gain move stays on one identified track and increases it by at least \(1/D(n)\);
- each track’s weight lies in a displayed interval bounded using threshold \(\le N\).

SQ.0(d) also needs sharpening. For an individual realized lift-carrying history, Theorem C gives the nonzero integer count \(p^{nN-A(H)}\), which indeed forces \(A(H)\le nN\). That argument must be stated. For a value-forgotten template with count \(C_H(p)\), the same conclusion does not follow directly from \(C_H(p)p^{nN-A(H)}\in\mathbb Z\).

## Concerns

### 1. J2 may encounter genuine congruence dependence

Monomial power maps naturally produce factors such as \(\gcd(a,q^g-1)\), which are not universal polynomials in \(q\). The anchor twist eliminated one observed characteristic split, but it does not prove that all norm, trace, ratio, and collision strata avoid this phenomenon.

J2 is honestly marked open, so this is not an additional logical contradiction. Its derivation must explicitly audit every exponent map; “triangular/monomial shape” alone is not enough.

### 2. M4a-X Route A needs an affine-semigroup argument

Even if translations preserve counts along allowed lattice directions, it does not immediately follow that every congruence class in a cone is one translation orbit or that there are finitely many boundary orbits. Route A needs a Gordan-lemma/fundamental-module statement for the exact cone semigroup, together with compatibility of the translation bijections under composition.

Route B remains a legitimate alternative.

### 3. ESCAPE Route E2 does not currently imply ESCAPE

E2 proposes:

> “a weighted norm \(V(\tau,\text{ key weight})\)”

while \(K_e\) is indexed only by the finite type \(\tau\), with height and loop position deliberately eliminated.

A drift estimate on an infinite augmented state space does not by itself yield

\[
\sup_x \Pr_x(\text{still in block after }B)\le1-p^{-c}.
\]

Indeed, ordinary Foster–Lyapunov drift often gives eventual escape without any uniform finite-\(B\) bound over unbounded weights.

E2 must either:

- prove a uniform minorization/renewal event within bounded time; or
- change RS.3 to use the weaker conclusion actually supplied by the drift theorem.

There is also a potentially simpler route worth stating: if X.3 gives almost-sure exit from the same-size block and M2 gives an exact finite substochastic kernel, then \(K_e(p)^k\mathbf1\to0\), hence \(\rho(K_e(p))<1\) for each fixed \(p\). A uniform \(B(n),c(n)\) is stronger than RS.3 appears to need.

### 4. E1’s probability multiplication must be displayed

Graph reachability alone is insufficient. If a path of length at most \(B\) has each required transition mass at least \(p^{-c_0}\), its path mass is at least \(p^{-Bc_0}\). The stated \(c\) must absorb the full path length and all fresh-pool dimensions. The witness lemma must concern the required transition at each intermediate type, not merely the existence of some exit-producing assignment somewhere.

### 5. The (†-AGG) canonical example has hidden dependencies

The corrected protocol is sound in principle. For `decided_σ(N)` one must still prove:

- a single finite, \(p\)-independent syntactic list of templates bounded by SQ.0;
- zero-extension for templates unrealizable at particular \(p\);
- polynomiality of every normalized summand through the corrected cell-transition version of VAL;
- the degree-\(\le nN\) bound;
- when censusing prime powers \(q\), the relative \(W(\mathbb F_q)\) version supplied by REL, rather than silently treating such counts as ordinary \(\mathbb Z_p\) boxes.

Thus (†-AGG) is genuinely repaired, but its canonical instance is conditional on more than SQ.0 alone.

### 6. X.2 remains adequately routed, but only conditionally

Striking WEIGHT-CHARGE→\(B(n)\) does not deprive X.2 of its intended support. The plan now uses WEIGHT-CHARGE only to turn large total depth into large discriminant valuation, while tall histories are controlled by M4a tails. That separation is correct.

However, “PROGRESS” must provide an actual quantitative dichotomy and constants:

\[
\operatorname{threshold}(H)>N
\Longrightarrow
d_{\rm total}(H)\ge d^*(N)
\quad\text{or}\quad
\max h(H)\ge h^*(N),
\]

with both \(d^*(N)\) and \(h^*(N)\) linear enough in \(N\) to obtain the claimed exponential envelope. Until WEIGHT-CHARGE and that coercivity calculation close, X.2—and therefore SQ.3/SQ.4—remains conditional. REV 4 records this honestly.

### 7. Some gate language still overstates what finite tests establish

MENU-n3’s two-sided parameter test can refute the sealed exact-domain description in the tested box, but it cannot establish M4a-X for unbounded parameters or higher degree. Similarly, STATE-probe-2 can refute lumpability but cannot establish it. Section 7 generally says this correctly; phrases such as “deciding probe” should not migrate into acceptance records as proof language.

## D4-R drafting question

REV 4 does preserve D4-R’s independence from the unresolved VALUE/STATE/RESUM architecture. Its pool inequality, exact finite-prefix mass law, and common-frame partition argument can still be drafted first.

The drafting decision is therefore **GO, with one mandatory correction**: the draft must not repeat the assertion that a prefix cylinder is exactly the union of finite terminating completions. It must use maximal finite-or-infinite canonical runs.

An acceptable D4-R draft needs the following lemma list.

1. **Canonical-choice totality.**  
   The S6b offset-\(P\) lift is defined at every eligible recentering, including all boundary cases.

2. **Maximal canonical run.**  
   Every input has a unique maximal canonical run, finite terminal or infinite. This is a deterministic object even before almost-everywhere termination is invoked.

3. **Three-level object distinction.**  
   Introduce separate notation for:

   - a shape prefix \(\widehat P\), with values forgotten;
   - a realized lift-carrying prefix \(\eta\), with node values and canonical lifts;
   - a complete finite terminal history \(H\).

4. **Common-frame coherence.**  
   If two inputs realize the same realized prefix \(\eta\), their next read is performed in the identical frame \(\Psi_\eta\). Prove this inductively from equality of prior node data and deterministic canonical lifts.

5. **Next-outcome totality and exclusivity.**  
   In the common frame, every input produces exactly one of:

   - one displayed next-node datum;
   - one displayed terminal verdict.

   The polygon/side/outcome case list must be exhaustive, including zero, endpoint, and no-side cases.

6. **Realized-prefix cylinder identification.**  
   Prove

   \[
   S(\eta,\top)
   =
   \{f:\eta\preceq H_{\rm can}^{\max}(f)\}.
   \]

   These cylinders are disjoint for distinct realized prefixes of the same shape.

7. **Complete-history fiber identification.**  
   For finite terminal \(H\),

   \[
   S(H,\top)=\{f:H_{\rm can}^{\max}(f)=H\}.
   \]

   This is separate from the prefix statement.

8. **Finite value-prefix lemma.**  
   For fixed \(\widehat P\), the set

   \[
   \operatorname{Pref}(\widehat P)
   =
   \{\eta:\operatorname{shape}(\eta)=\widehat P\}
   \]

   is finite. This—not the possibly infinite set of terminal completions—is the set whose cardinality is \(C_{\widehat P}(p)\).

9. **Shape-constant fresh-volume lemma.**  
   For every \(\eta\in\operatorname{Pref}(\widehat P)\),

   \[
   \prod_i\operatorname{vol}(E_{\rm fresh}(\nu_i))
   =p^{-A(\widehat P)}.
   \]

10. **Exact prefix mass law.**  
    Using Theorem C with \(Z=\top\) on each realized prefix cylinder,

    \[
    \mu(\widehat P)
    =
    \sum_{\eta\in\operatorname{Pref}(\widehat P)}
      \mu(S(\eta,\top))
    =
    C_{\widehat P}(p)p^{-A(\widehat P)}.
    \]

    No sum over terminal completions is needed.

11. **Pool encoding and bound.**  
    Give an explicit injection from realized value prefixes into the product of the retained digit pools and conclude

    \[
    C_{\widehat P}(p)\le p^{W(\widehat P)}.
    \]

    Explain exactly why (NA)/(HV) only remove assignments.

12. **Uniform finite-level realization.**  
    Define

    \[
    N(\widehat P)=
    \max_{\eta\in\operatorname{Pref}(\widehat P)}N(\eta,\top),
    \]

    prove it is finite, and establish the exact count at every \(N\ge N(\widehat P)\).

With these lemmas, all three advertised D4R.0 burdens—totality, terminal exhaustiveness, and common frame—are genuinely discharged, and D4R.1/D4R.2/D4R.4 follow without depending on JREF or RESUM.

## Final assessment

- **CRITICAL OBSTRUCTIONS: 5**
- **CONCERNS: 7**
- **Verdict: UNSOUND**
- **D4-R drafting: GO WITH THE MANDATORY PREFIX/MAXIMAL-RUN REPAIR**

The decisive architecture repair is to replace the current species-relative JREF plus position-independent \(C_{S,\tau}\) picture with a globally compatible, cell-to-cell polynomial transition system. Once that is done, LOC→HIST→FAM can be expressed as finite-path matrix products followed by positive rational resummation.
