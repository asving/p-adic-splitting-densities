## Pass-5 structural review

REV 5 makes the requested conceptual change: the species-relative scalar-count picture has been replaced by a global cell-indexed transition system, and the LOC/realized/template/FAM distinction is now coherent at the level of notation. Nevertheless, the CTS is not yet a sound measured transition system. Its combinatorial tables, conditional probabilities, initial-state masses, empty-cell behavior, and height resummation do not currently fit together.

### A. Disposition of every pass-4 finding

| Pass-4 finding | REV 5 disposition | Classification |
|---|---|---|
| Critical 1: JREF was not a single state partition | “**JREF^src(s) := ⋀_{m ∈ Out(s)} JREF_m^source**” and “**CTS.5 GLOBAL COMPATIBILITY**” | **PARTIAL.** The global-meet construction is the right architectural object. But `Out(s)` is called the menu of “admissible” species rather than the full \(p\)-independent syntactic menu, and the constituent partitions remain schematic pending CTS.0. Empty cells and exceptional-prime behavior are not defined. |
| Critical 2: VAL lacked cell-to-cell numerators | “**T_{m,o}^{α,β}(q) := #{fresh assignments producing (m,o,β) \mid one representative source state in α}**” with CTS.1–CTS.5 | **PARTIAL.** The necessary table object now exists, with row partition and representative independence as explicit burdens. But its normalization and composition are still defective: the path product omits initial-cell multiplicity, while RS.PRE incorrectly divides the per-representative count by “source-cell mass.” |
| Critical 3: LOC/HIST/FAM did not compose | “**FOUR distinct objects**” and “**a k-loop template is a k-step path with k fresh pools and a k-fold product**” | **GENUINE at the object/notation level.** Realized histories and value-forgotten templates are now separate, \(C_{S,\tau}\) is retired, and loop length is represented by path length. The remaining failure is in the measured CTS composition, not in this separation itself. |
| Critical 4: prefix cylinders omitted infinite maximal runs | “**H_can^max(f) — finite terminal or infinite**” and prefix cylinders are “**NOT the union of fibers of finite completions**” | **GENUINE.** This is the requested correction, and the twelve-lemma D4-R roster is carried over accurately. |
| Critical 5: SQ.0(c)/(d) invalid | “**MULTI-TRACK zero-gain bound**” and “**argued at the REALIZED level**” | **PARTIAL.** Clause (d) is genuinely repaired, subject to identifying the decision threshold with a level at which Theorem C applies. Clause (c) is now stated in the right form, but the existence of a bounded number \(L(n)\) of tracks remains a substantial open lemma; “ladder restarts each open a track” makes the proposed \(L(n)\le n^2\) especially nonautomatic. |
| Concern 1: possible \(\gcd(a,q^g-1)\) dependence | “**EXPONENT-MAP AUDIT written into CTS.2**” | **GENUINE relocation, not closure.** The precise danger is now an explicit CTS burden and no longer waved away by “monomial shape.” |
| Concern 2: Route A needs affine-semigroup machinery | “**Gordan/fundamental-module statement + composition compatibility**” | **GENUINE relocation, not closure.** The missing theorem is now correctly named, and Route B remains available. |
| Concern 3: E2 does not imply uniform ESCAPE | “**primary route E0 per-fixed-p**” and ESCAPE-UNIF “**consumed by nothing**” | **GENUINE.** REV 5 adopts the weaker spectral condition actually needed. The E0 proof remains conditional on an exact finite kernel. |
| Concern 4: E1 path probabilities were not multiplied | “**path mass ≥ p^{-Bc₀}, so c=B·c₀**” | **GENUINE.** The optional route now states the correct multiplication burden. |
| Concern 5: hidden dependencies in (†-AGG) | “**FIVE exposed inputs**” | **GENUINE.** The dependencies on finite syntax, zero-extension, CTS polynomiality, degree, and REL are all explicit. |
| Concern 6: X.2 lacked a quantitative dichotomy | “**threshold(H)>N ⇒ d_total(H)≥d*(N) OR max h(H)≥h*(N)**” with linear lower bounds | **GENUINE relocation, not proof.** This is now a properly stated open coercivity theorem with its conditional consumers identified. |
| Concern 7: probes were described as deciding proofs | “**‘deciding probe’/‘decisive test’ banned from acceptance records**” | **GENUINE.** The live protocol consistently treats probes as refuters/support only. Historical record text still contains the older wording, but it is clearly historical rather than acceptance language. |

## B. CTS audit

### 1. Finiteness and \(p\)-independence

The meet is syntactically finite only under two conditions:

1. `Out(s)` is the full finite \(p\)-independent syntactic menu, including species that are empty at particular characteristics.
2. Every \(JREF_m^{\mathrm{source}}\) is itself a uniformly labelled finite partition, with explicit exceptional-characteristic and empty-cell conventions.

REV 5 asserts the second as CTS.0/CTS.1 but does not yet define it. More seriously, `Out(s)` is presently described as the menu of “admissible” outgoing species. If admissibility is evaluated over the current residue field, the meet itself can vary with \(p\). The intended zero-extension convention must be built into the CTS definition, not only into (†-AGG).

“Same \(\alpha\)” is not automatically sufficient merely because all named observables were placed in the meet. It is sufficient exactly if CTS.4 is proved for the entire joint row. REV 5 correctly labels that as the lumpability theorem. Thus this is an honest open theorem, not a consequence of the definition.

There is also a type error in CTS.2:

> “every table entry AND every cell size … degree bound \(\le W_{\rm loc}(m)\)”

A source-cell size belongs to \(s,\alpha\), not to a particular outgoing \(m\), and its dimension can exceed the fresh-pool dimension of some outgoing move. Cell sizes need their own state-space degree bound. The displayed \(W_{\rm loc}(m)\) bound is meaningful for transition numerators, not uniformly for source-cell sizes.

### 2. Are CTS.0–CTS.5 complete?

No. They cover the finite combinatorial automaton, but not the measured Markov system that RESUM uses. At least four additional burdens are missing.

- **Initial/source mass.** A path starting with a source cell needs an initial-cell count or mass. The product of extension counts alone does not count all realizations of the source cell.

- **Fresh-pool normalization.** The denominator of a conditional transition is the total fresh-assignment mass or cardinality available from a concrete source representative. It is not the mass of the source cell.

- **Empty-cell semantics.** At a prime where a formally labelled cell is empty, there is no representative and no conditional row. A fixed symbolic matrix needs an explicit convention that avoids division by zero and does not introduce arbitrary rows affecting its determinant or spectral radius.

- **Height-domain Markov compatibility.** M4a-X proves exact domains at fixed whole templates, while \(K_e^k\) assumes those height choices compose stepwise. One must prove that the admissible future height domain and its geometric mass depend only on the retained CTS state—or augment the state by the necessary boundary/gap data. Global cone inequalities can otherwise couple successive steps and prevent factorization into powers of a one-step kernel.

Measurability is also not stated at the CTS layer. D4R.0 gives cylinder measurability for realized prefixes, but RS.PRE needs a theorem identifying every table/height summand with a measurable disjoint subevent of the source cylinder.

### 3. Does the path product equal realized-history mass/count?

Not as stated.

REV 5 defines

\[
C_\gamma(q)=\prod_i T_{m_i,o_i}^{\beta_{i-1},\beta_i}(q)
\]

for a template whose data include “a source cell.” Each \(T\) counts fresh extensions from one fixed representative. Therefore the product counts extensions from one fixed initial representative, provided CTS.4 holds and every assignment determines a unique next concrete state.

It does not count all linked assignments including the initial source values unless one of the following is supplied:

- an initial multiplicity \(|\beta_0|(q)\);
- an initial distribution/vector from the preceding root transition; or
- a definition making the first table entry create the entire initial state.

None is presently specified.

After an initial distribution is supplied, representative independence is strong enough to prevent ordinary conditioning drift: even a nonuniform distribution within the target cell yields the same next-row law if every representative has the identical row. But that conclusion requires per-representative weighted transition equality, not merely an unnormalized cardinality statement divorced from fresh-volume normalization.

### 4. RS.PRE normalization

The displayed formula is dimensionally wrong:

> “\(T_{m,o}^{\alpha,\beta}(q)\cdot G_{m,o}(q) /(\text{source-cell mass})\)”

Here \(T\) is already defined per one source representative, and \(G\) is described as the per-assignment fresh-volume/height mass. Thus \(T\,G\) is already a conditional continuation mass from that representative. Dividing by source-cell mass again inflates the conditional probability.

If instead the numerator were an aggregate mass over the whole source cell, it would require a factor of source-cell mass before division, which would cancel under representative independence. The current definition mixes these two conventions.

Consequently substochasticity does not presently follow from RS.PRE, and the claimed identification

\[
K_e(p)^k\mathbf 1
=
\Pr(\text{still in the block after }k)
\]

has not been typed correctly.

### 5. Positive rational resummation and the spectral condition

Finiteness plus substochasticity alone does **not** imply \(\rho(K_e(p))<1\). A stochastic closed class has spectral radius one.

REV 5 recognizes this and introduces exactly the missing condition:

> “**ESCAPE (OPEN KERNEL)** … \(K_e(p)^k\mathbf1\to0\) … hence \(\rho(K_e(p))<1\).”

That implication is sound for a finite nonnegative matrix. If the exact-kernel identification is repaired, X.3 can plausibly imply E0 by conditioning on a positive source cylinder.

Thus the spectral issue is no longer hidden, but it is still open. The unqualified FAM prose describing \((I-K_e)^{-1}\) as the completed resummation should be read as conditional on E0. Substochasticity and finiteness alone are insufficient.

Empty source cells again interfere: X.3 says nothing about a conditional row for a zero-mass cell, yet such a formal row can affect the determinant of the full symbolic matrix.

## C. Retirements

The three retirements are mostly respected.

- **M4b position independence:** No downstream passage still explicitly uses a loop-length-independent \(C_{S,\tau}\). RS.0’s height/position bisimulation is a law-invariance claim, not a count-constancy claim. The remaining problem is the unproved factorization of exact height domains into a one-step kernel.

- **\(C_{S,\tau}\):** It appears only in historical or explicit retirement language. Live counting uses table entries, \(C_\gamma\), and FAM objects.

- **ESCAPE-UNIF:** RS.3 and SQ.2 explicitly consume E0 only. E1/E2 are optional and no downstream argument silently requires uniform \(B(n),c(n)\).

One over-retained dependency is harmless but misleading: RS.4 is tagged as inheriting X.1b through X.2, although the identity “total terminating mass \(=1\)” appears to need X.3 rather than the quantitative envelope. This is over-conditioning, not an unsound inference.

## D. DAG, gates, and conditionality

The declared note-level DAG remains acyclic. In particular:

- SPECIES precedes VALUE;
- VALUE precedes STATE-GEOM;
- STATE-GEOM and EXHAUST precede RESUM;
- RESUM and EXHAUST precede SQUEEZE.

The apparent backward use of SQ.0 in (†-AGG) is labelled as a conditional example rather than an input required to accept VALUE, so it does not by itself create a note cycle.

The roster names a gate or probe for every kernel the plan itself recognizes. But the CTS audit exposes unnamed obligations:

- source/initial mass normalization;
- empty-cell rows at exceptional primes;
- compositionality of the exact height domains;
- measurable identification of table rows with source-cylinder subevents.

COMPOSE-probe can detect some two-step count failures, and RESUM-n3 can detect aggregate normalization errors, but neither gate is explicitly sealed against these four statements. Therefore the assertion that every open load-bearing kernel has a named probe/gate is not yet true.

The capstone carries the advertised conditional tags for ESCAPE, X.1b, and the three stated RS.PRE inputs. However, those tags do not mention the missing normalization, active-cell, and height-Markov conditions, because those conditions have not yet been named. No completed proof is being accepted unconditionally, but the conditionality ledger is incomplete.

## E. Fresh sweep

The most serious additional issue is the treatment of cells that are uniformly labelled but empty at some wild primes. This cuts across all three central claims:

- `T | one representative` is undefined;
- division by source-cell mass can have a zero denominator;
- E0 on positive cylinders does not control arbitrary formal rows;
- the determinant of a matrix containing such rows need not reflect the realized process.

Deleting empty rows separately for each \(p\) would recover a genuine finite Markov chain at that \(p\), but would make the symbolic block index set \(p\)-dependent unless a compatible fixed-matrix convention is proved. REV 5 currently has neither convention.

The second fresh issue is that M4a-X’s whole-template semilinearity and RS.PRE’s one-step matrix formalism are different kinds of structure. Exact rational summability of every fixed path does not imply that the sum over all paths is generated by a fixed one-step matrix. That needs the height-domain Markov compatibility theorem noted above.

## Final assessment

### Critical obstructions

1. **RS.PRE has an incorrect source normalization.** Per-representative transition counts multiplied by per-assignment masses must not then be divided by source-cell mass.

2. **VAL CHAIN omits the initial-cell factor/distribution.** \(\prod T_i\) counts extensions from a fixed initial representative, not all realizations of a template whose source cell varies.

3. **The fixed \(p\)-independent CTS has no empty-cell semantics.** At exceptional primes, representatives and conditional rows may not exist, denominators may vanish, and formal unused rows may corrupt the symbolic determinant and spectral analysis.

4. **Height resummation is not proved to be Markov-compatible with depth matrix powers.** M4a-X exact domains are whole-template objects; \(K_e^k\) requires their successive choices to factor through the retained state.

### Concerns

1. `Out(s)` must be the \(p\)-independent syntactic menu, not the field-dependent menu of actually admissible moves.

2. CTS.2 gives the wrong common degree bound for source-cell sizes; they need a state-space bound independent of \(m\).

3. CTS.0 still names categories of predicates rather than displaying the actual finite uniform partition; the global meet is therefore schematic.

4. Measurable cylinder realization and weighted—not merely cardinality—row equality need explicit CTS burdens.

5. SQ.0’s bounded track count \(L(n)\) is still highly nontrivial; repeated ladder restarts cannot simply be counted by degree without a separate structural lemma.

6. Finiteness plus substochasticity does not give rational matrix resummation; REV 5 correctly adds E0, but all fixpoint assertions remain conditional on it and on a correctly normalized active-state kernel.

- **CRITICAL OBSTRUCTIONS: 4**
- **CONCERNS: 6**
- **Verdict: UNSOUND**

The single highest-leverage repair is to replace CTS.0–CTS.5 with a **measured CTS theorem** that simultaneously defines the fixed syntactic state set, active/empty-cell conventions at every prime, the initial distribution, correctly normalized per-representative transition probabilities, and stepwise compatibility of exact height domains. Its composition theorem must directly identify initial-vector × kernel-path products with realized cylinder masses. Only then can E0 legitimately turn the finite kernel into a rational Neumann solve.

**Draft readiness:** no NOTE beyond **[1] D4-R** is presently cleared for drafting. D4-R remains ready with the mandatory maximal-run formulation. [2a] is next in the declared dependency order, but the plan itself makes it consume accepted [1], while all CTS-dependent notes remain blocked by the measured-transition defects above.
