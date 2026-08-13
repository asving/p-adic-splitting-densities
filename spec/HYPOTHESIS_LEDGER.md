# PHASE-0b — HYPOTHESIS-CLOSURE LEDGER

Scope: surviving conditions on the current path from `leanfinal`’s `UniformityStatement` through W12/GENIND, the T-unit chain, the low-degree checks, and the cited external mathematics. This is an enumeration and proposed classification only; it resolves none of the listed obligations.

## Ledger

### Capstone and low-degree interface

HYP.01  `typeOf` faithfulness  
WHERE: `leanfinal/notes/GENUINE_DENSITY_2026-08-13.md`, STATUS/trust-boundary discussion.  
STATEMENT: For separable polynomials, the gcd-defined `typeOf` agrees with the classical ramification-degree/residue-degree splitting type used in the mathematical theorem.  
CONSUMED BY: `genuineDensity`, `UniformityStatement`, and every transfer from a classical splitting-type count to the Lean event.  
CLASS: lean-open-statement  
PROPOSED DISPOSITION: NODE — the note supplies the intended classical argument and Lean already proves `typeOf_degree`; the remaining node is formal faithfulness review and packaging.

HYP.02  `eq_of_add_mul_eq`  
WHERE: `leanfinal/notes/HENSEL_FACT_2026-08-13.md`, §6.  
STATEMENT: Solutions of the landed coprime-factor lifting equation are unique in the relevant congruence class.  
CONSUMED BY: uniqueness/injectivity refinements of the two-block Hensel factorization interface.  
CLASS: lean-open-statement  
PROPOSED DISPOSITION: NODE — the note gives an equal-rank finite-free-module/Orzech route; no new mathematical conjecture is indicated.

HYP.03  n-fold/multi-block Hensel factorization  
WHERE: `leanfinal/notes/HENSEL_FACT_2026-08-13.md`, §6.  
STATEMENT: A finite family of pairwise coprime residue factors lifts to a factorization into the corresponding number of monic factors.  
CONSUMED BY: general-degree factorization and the n≥4 splitting-type assembly.  
CLASS: lean-open-statement  
PROPOSED DISPOSITION: NODE — induction from the landed two-block theorem using `IsCoprime.prod_right` is recorded in the corpus.

HYP.04  strong Hensel inequality  
WHERE: `leancheck/notes/N3_CHECK_2026-08-13.md`, §§9–12.  
STATEMENT: For monic \(F\) over a complete DVR, if \(v(F(x_0))>2v(F'(x_0))=2w\) with \(w\ge1\), then there is \(r\) such that \(F(r)=0\) and \(v(r-x_0)>w\).  
CONSUMED BY: the repeated-root branch of the cubic recursion and `CertRam3`.  
CLASS: lean-open-statement  
PROPOSED DISPOSITION: MATH — medium formalization: put \(b=F'(x_0)\), form \(G(Y)=b^{-2}F(x_0+bY)\), prove its constant term is in the maximal ideal, its linear coefficient is one, and its higher Taylor coefficients \(a_jb^{j-2}\) are integral; ordinary Hensel at zero yields \(y\in\mathfrak m\), and \(r=x_0+by\). The paper proof is clear, but no corpus proof presently exists.

HYP.05  `typeOf` shift invariance  
WHERE: `leancheck/notes/N3_CHECK_2026-08-13.md`, §§9–12.  
STATEMENT: Translation \(X\mapsto X+c\) by an integral constant does not change `typeOf`.  
CONSUMED BY: recentering in the cubic repeated-root analysis.  
CLASS: lean-open-statement  
PROPOSED DISPOSITION: MATH — small formal lemma, but the corpus contains no proof at the `typeOf` level.

HYP.06  `typeOf` scale invariance  
WHERE: `leancheck/notes/N3_CHECK_2026-08-13.md`, §§9–12.  
STATEMENT: After the prescribed extraction \(X=\pi^mY\), the normalized polynomial has the splitting-type relation asserted by the recursion.  
CONSUMED BY: the cubic depth-reduction step and recurrence.  
CLASS: lean-open-statement  
PROPOSED DISPOSITION: MATH — medium formal work involving normalized coefficients, roots, and the gcd-based type definition; no corpus proof exists.

HYP.07  nonintegral-slope `CertRam3`  
WHERE: `leancheck/notes/N3_CHECK_2026-08-13.md`, §§9–12.  
STATEMENT: The nonintegral Newton-slope branch has the certified cubic ramification type claimed by the informal classification.  
CONSUMED BY: cubic menu exhaustiveness and exact cubic densities.  
CLASS: lean-open-statement  
PROPOSED DISPOSITION: MATH — medium; the note identifies the norm/valuation route but does not prove it.

HYP.08  cubic tail recurrence  
WHERE: `leancheck/notes/N3_CHECK_2026-08-13.md`, §9.4.  
STATEMENT: The unresolved cubic mass satisfies  
\[
u(N)\le q^{-N/2}+q^{-5}u(N-3).
\]  
CONSUMED BY: quantitative drainage of the cubic triple-root branch.  
CLASS: named-obligation  
PROPOSED DISPOSITION: MATH — medium; the recurrence is stated but not derived in the corpus.

HYP.09  cubic triple-root drainage  
WHERE: `leancheck/notes/N3_CHECK_2026-08-13.md`, STATUS and §§9–12.  
STATEMENT: The infinite triple-root recursion has measure-zero complement after all finite classified cubic strata are removed.  
CONSUMED BY: `hExhaust3`, the cubic probability partition, and exact cubic density assembly.  
CLASS: conditional-theorem-leg  
PROPOSED DISPOSITION: MATH — medium-to-large; it depends on HYP.04–HYP.08, and no complete corpus proof exists.

HYP.10  exactly five cubic splitting types  
WHERE: `leancheck/notes/N3_CHECK_2026-08-13.md`, §§9–12.  
STATEMENT: Every separable monic cubic over the target local field has exactly one of the five listed \((e,f)\)-multisets.  
CONSUMED BY: the finite cubic menu and the sum-to-one theorem.  
CLASS: lean-open-statement  
PROPOSED DISPOSITION: MATH — small-to-medium formal classification; the assertion is open in the current Lean note.

HYP.11  exact cubic densities  
WHERE: `leancheck/notes/N3_CHECK_2026-08-13.md`, STATUS; W12’s accepted `HMENU3`/`HEX3` inputs.  
STATEMENT: Each of the five cubic splitting types has the stated rational function in \(q\) as its density.  
CONSUMED BY: the degree-three leaf of `UniformityStatement`.  
CLASS: lean-open-statement  
PROPOSED DISPOSITION: NODE — the accepted informal `HMENU3`/`HEX3` laws already supply the finite formulas; the remaining task is transcription and verification.

HYP.12  ordering convention for \((e,f)\) pairs  
WHERE: `leancheck/notes/N3_CHECK_2026-08-13.md`, trust item; `leanfinal/notes/GENUINE_DENSITY_2026-08-13.md`.  
STATEMENT: The implemented ordering and multiset normalization of \((e,f)\)-pairs matches the ordering used by the classical splitting-type statements.  
CONSUMED BY: equality between exact low-degree events and `typeOf`.  
CLASS: audit-work-item  
PROPOSED DISPOSITION: NODE — finite definitional audit against the implemented normalization.

### Citation and theorem-scope residue

HYP.13  all-\(O\) citation swap  
WHERE: `docs/CITE_SCOPE_RESOLUTION_2026-08-13.md`, verdict table.  
STATEMENT: Approximately thirteen imported facts must cite their all-complete-DVR sources rather than narrower \(p\)-adic surrogates.  
CONSUMED BY: the external-reference layer supporting the general capstone.  
CLASS: cite-scope-residue  
PROPOSED DISPOSITION: NODE — the replacement sources are identified in AGNPRW, GN15, FGMN, and Kuhlmann.

HYP.14  `NS-6` residual-separability descent criterion  
WHERE: `docs/CITE_SCOPE_RESOLUTION_2026-08-13.md`, NS-6.  
STATEMENT: The descent trigger is equivalent to separability of the relevant residual polynomials.  
CONSUMED BY: the descent/drainage interface used by the higher-degree induction.  
CLASS: cite-scope-residue  
PROPOSED DISPOSITION: NODE — combine the two directions from GN15 Theorem 2.3 and AGNPRW Theorem 2.10 into the recorded short internal corollary.

HYP.15  `NS-7` termination  
WHERE: `docs/CITE_SCOPE_RESOLUTION_2026-08-13.md`, NS-7.  
STATEMENT: The MacLane/Okutsu construction used by the project terminates over every complete DVR in the capstone’s scope.  
CONSUMED BY: finite-depth certificates, GENIND termination, and the existence of a finite menu/drain description.  
CLASS: cite-scope-residue  
PROPOSED DISPOSITION: CARRY — OPEN-CALL: the available theorem has the correct all-\(O\) statement but cites a \(\mathbf Q_p\)-scope index step; this can instead become a 2–4 page internal NODE using length/index machinery, so 0d must choose.

HYP.16  `NS-15` finite-depth bound  
WHERE: `docs/CITE_SCOPE_RESOLUTION_2026-08-13.md`, NS-15.  
STATEMENT: Replace the unsupported mixed-characteristic formula \(B(n,p)\) by the finite bound “depth at most \(\tfrac12v(\operatorname{disc}f)\)” where used.  
CONSUMED BY: `L5fix(b)` and finite certificate statements; the capstone does not require the explicit \(B(n,p)\).  
CLASS: cite-scope-residue  
PROPOSED DISPOSITION: NODE — a statement edit using NS-7/F2 removes the unsupported formula without adding a capstone hypothesis.

HYP.17  publisher-number verification  
WHERE: `docs/CITE_SCOPE_RESOLUTION_2026-08-13.md`, verdict table.  
STATEMENT: The author/arXiv theorem surrogates for AGNPRW, GN15, and Kuhlmann must be checked against final publisher numbering.  
CONSUMED BY: final bibliography and theorem attribution.  
CLASS: audit-work-item  
PROPOSED DISPOSITION: NODE — bibliographic verification only.

HYP.18  `AX-DEFECT` correction  
WHERE: `docs/CITE_SCOPE_RESOLUTION_2026-08-13.md`, verdict table.  
STATEMENT: Defectlessness must be justified from discreteness of the value group, not from the currently written reason.  
CONSUMED BY: external field-theory assumptions used by the induction.  
CLASS: cite-scope-residue  
PROPOSED DISPOSITION: NODE — Kuhlmann Theorem 3.3 supplies the correct all-characteristic statement.

### W12 and general induction

HYP.19  `[W12-H]`  
WHERE: `lean/notes/openmath/W12_PROOF_2026-08-12.md`, hypothesis box.  
STATEMENT: The W12 reduction is conditional on its five supplier clauses `[H-a]`–`[H-e]`.  
CONSUMED BY: W12.D and the passage from finite menus plus drainage to the capstone.  
CLASS: hypothesis-box  
PROPOSED DISPOSITION: CARRY — this aggregate remains honest until every child clause is converted into a node; do not add it separately if the children are expanded in the final signature.

HYP.20  `[H-a]` / JC composite-stage warrant  
WHERE: `lean/notes/openmath/W12_PROOF_2026-08-12.md`, `[W12-H]`.  
STATEMENT: The composite-stage JC construction has the warrant required by the W12 decomposition.  
CONSUMED BY: W12’s composite-stage partition.  
CLASS: hypothesis-box  
PROPOSED DISPOSITION: NODE — the accepted `GRTJC` supplier is identified as its discharge.

HYP.21  `[H-b]` / JB membership  
WHERE: `lean/notes/openmath/W12_PROOF_2026-08-12.md`, `[W12-H]`; `docs/TIGHTNESS_CENSUS_2026-08-11.md`, `JB-NOLEG`.  
STATEMENT: The JB strata have the claimed membership characterization uniformly over the unbounded parameter grid.  
CONSUMED BY: the W12 finite partition and exclusion of non-legs.  
CLASS: hypothesis-box  
PROPOSED DISPOSITION: CARRY — OPEN-CALL: the census records an unclosed membership residue; it may collapse to a finite structural NODE after the weld-face audit.

HYP.22  `[H-c]` / J-D1 value-side package  
WHERE: `lean/notes/openmath/W12_PROOF_2026-08-12.md`, `[W12-H]`.  
STATEMENT: The J-D1 value computation, including its weld boxes and \(\Sigma\)-law, is valid on every claimed face.  
CONSUMED BY: W12’s exact measure assignments and general-stage power sums.  
CLASS: hypothesis-box  
PROPOSED DISPOSITION: CARRY — OPEN-CALL: the package is explicitly conditional on unresolved weld subboxes, and the corpus has not established that every such face is capstone-live.

HYP.23  `[H-d]` universal finite-field residual censuses  
WHERE: `lean/notes/openmath/W12_PROOF_2026-08-12.md`, `[W12-H]`.  
STATEMENT: The required finite-field residual counts hold uniformly over the residue-field towers appearing in the induction.  
CONSUMED BY: W12 menu weights and GENIND stage counts.  
CLASS: hypothesis-box  
PROPOSED DISPOSITION: NODE — the corpus treats these as finite-field census nodes with explicit supplier computations rather than new hypotheses on \(O\).

HYP.24  `[H-e]` higher-order GMN leaf/\(\sigma\) decision  
WHERE: `lean/notes/openmath/W12_PROOF_2026-08-12.md`, `[W12-H]`; GENIND `CS-3`.  
STATEMENT: At every order at least two, the GMN leaf data determine whether the requested splitting type \(\sigma\) occurs.  
CONSUMED BY: terminal leaves in W12 and GENIND.  
CLASS: hypothesis-box  
PROPOSED DISPOSITION: NODE — the cite-scope resolution assigns this to the external general leaf theorem after the all-\(O\) citation swap.

HYP.25  `A0` lift well-posedness  
WHERE: `lean/notes/openmath/W12_PROOF_2026-08-12.md`, W12.D.  
STATEMENT: Every classified residue/certificate datum lifts to a well-defined polynomial event with the claimed splitting-type label.  
CONSUMED BY: W12.D and the capstone measure identity.  
CLASS: conditional-theorem-leg  
PROPOSED DISPOSITION: CARRY — this is one of W12.D’s explicit public assumptions unless its lower supplier nodes are assembled before freeze.

HYP.26  `A1` exact finite core menu  
WHERE: `lean/notes/openmath/W12_PROOF_2026-08-12.md`, W12.D.  
STATEMENT: For fixed \(n,\sigma\), there is a finite, disjoint, \(q\)-independent menu of core cases carrying exact \(\sigma\)-labels and weights.  
CONSUMED BY: the numerator/denominator construction in W12.D and `UniformityStatement`.  
CLASS: conditional-theorem-leg  
PROPOSED DISPOSITION: CARRY — the general-degree supplier remains the GENIND conditional package.

HYP.27  `A2` complement drainage  
WHERE: `lean/notes/openmath/W12_PROOF_2026-08-12.md`, W12.D.  
STATEMENT: The complement of the finite classified core menu has measure tending to zero.  
CONSUMED BY: exhaustion of the genuine-density event and the capstone equality.  
CLASS: conditional-theorem-leg  
PROPOSED DISPOSITION: CARRY — its n≥4 instance is the surviving `DRAIN-N4`/`CS-1Q` obligation.

HYP.28  `hMenu3` / `W12-BOX-2`  
WHERE: `lean/notes/openmath/W12_PROOF_2026-08-12.md`, W12 boxes.  
STATEMENT: The cubic cases form the stated finite disjoint menu.  
CONSUMED BY: W12’s degree-three specialization.  
CLASS: hypothesis-box  
PROPOSED DISPOSITION: NODE — accepted `HMENU3` discharges it.

HYP.29  `hExhaust3` / `W12-BOX-3`  
WHERE: `lean/notes/openmath/W12_PROOF_2026-08-12.md`, W12 boxes.  
STATEMENT: The cubic menu exhausts the separable cubic event up to a null set.  
CONSUMED BY: W12’s degree-three specialization.  
CLASS: hypothesis-box  
PROPOSED DISPOSITION: NODE — accepted `HEX3` is the designated supplier, subject to closing the Lean cubic leaves HYP.04–HYP.10.

HYP.30  `W12-BOX-4` / `DRAIN-N4`  
WHERE: `lean/notes/openmath/W12_PROOF_2026-08-12.md`; `docs/TIGHTNESS_CENSUS_2026-08-11.md`, I1.  
STATEMENT: For every \(n\ge4\), the unclassified complement of the general finite menu has measure zero.  
CONSUMED BY: `A2`, W12.D, and the n≥4 capstone.  
CLASS: hypothesis-box  
PROPOSED DISPOSITION: CARRY — the later GENIND correction identifies a genuine surviving per-genre drainage obligation.

HYP.31  `[GENIND-H]`  
WHERE: GENIND hypothesis ledger.  
STATEMENT: The general induction theorem assumes `CS-1`, `CS-2`, `CS-3`, and `CS-EXACT`.  
CONSUMED BY: the general-degree menu and drainage theorem.  
CLASS: hypothesis-box  
PROPOSED DISPOSITION: CARRY — aggregate only; omit it if its component assumptions are displayed individually.

HYP.32  `CS-1` composite-stage transport  
WHERE: GENIND per-genre ledger.  
STATEMENT: Composite and mixed children are transported through each ragged stage with the asserted fibration and product structure.  
CONSUMED BY: GENIND’s stage recursion and `A1`.  
CLASS: named-obligation  
PROPOSED DISPOSITION: CARRY — the corrected general embedded/mixed transport is not proved uniformly in the corpus.

HYP.33  `CS-2` stage bracket  
WHERE: GENIND per-genre ledger.  
STATEMENT: Each stage has the claimed mass-normalized bracket compatible with the recursive count.  
CONSUMED BY: GENIND’s measure recursion and exact weights.  
CLASS: named-obligation  
PROPOSED DISPOSITION: CARRY — no corpus-wide proof closes it for every general genre.

HYP.34  `CS-3`  
WHERE: GENIND per-genre ledger.  
STATEMENT: The terminal higher-order leaf determines the requested splitting-type label.  
CONSUMED BY: GENIND terminal cases.  
CLASS: named-obligation  
PROPOSED DISPOSITION: NODE — identical to `[H-e]`, with the resolved general leaf citation as supplier.

HYP.35  `CS-EXACT`  
WHERE: GENIND per-genre ledger.  
STATEMENT: Every stage contributes an exact finite \(q\)-power-sum menu and an explicitly bounded drain.  
CONSUMED BY: rationality and exact numerator/denominator extraction.  
CLASS: named-obligation  
PROPOSED DISPOSITION: CARRY — general exactness remains part of the induction’s stated supplier package.

HYP.36  `(CS-1Q)` per-genre digit-loss bound  
WHERE: GENIND dated correction/per-genre ledger row.  
STATEMENT: For every realized genre, the loss of \(K\) digits is bounded by entry codimension or support slack strongly enough to force the residual mass to zero.  
CONSUMED BY: `DRAIN-N4`, `A2`, and the n≥4 capstone.  
CLASS: named-obligation  
PROPOSED DISPOSITION: CARRY — standalone CS4-E/F cases are available, but the general embedded/mixed statement is explicitly unproved.

HYP.37  `GENIND-BOX-2` per-route ledger compression  
WHERE: GENIND box ledger.  
STATEMENT: The displayed schema faithfully expands to every route used by the induction.  
CONSUMED BY: auditability of GENIND’s finite case partition.  
CLASS: audit-work-item  
PROPOSED DISPOSITION: NODE — the corpus classifies this as presentation/schema debt, not a missing mathematical lemma.

HYP.38  `FGMN-MAIN` Lean declaration/faithfulness  
WHERE: `docs/TIGHTNESS_CENSUS_2026-08-11.md`, I3.  
STATEMENT: The cited FGMN theorem must be declared with a Lean statement faithful to the verified mathematical source and connected to its consumers.  
CONSUMED BY: general higher-order leaf and factorization nodes.  
CLASS: audit-work-item  
PROPOSED DISPOSITION: NODE — the citation has already been scope-verified; declaration and wiring remain.

HYP.39  `JD0-BAR` sub-bar  
WHERE: `docs/TIGHTNESS_CENSUS_2026-08-11.md`, I5.  
STATEMENT: The JD0 bar required by the capstone route needs a proof-grade rather than machine-only coverage.  
CONSUMED BY: the JD0 value-side decomposition inside `[H-c]`.  
CLASS: grade-cap  
PROPOSED DISPOSITION: NODE — the 68,523-case zero-failure computation exists; the remaining obligation is a clean proof artifact.

HYP.40  `WI-LEMMA` proof-grade gate  
WHERE: `docs/TIGHTNESS_CENSUS_2026-08-11.md`, I2; `GENTOW5_WI` certification.  
STATEMENT: The cumulative-window lemma is mathematically certified, but the second proof-evidence report remains pending.  
CONSUMED BY: `GENTOW5-W(i)` for \(i\ge3\), T3, and T5.  
CLASS: grade-cap  
PROPOSED DISPOSITION: NODE — PE1 is clean and the proof is present; PE2 is an audit/report node, not a new hypothesis.

### T2 carrier obligations and grade

HYP.41  `(LB1)`  
WHERE: T2 ACCEPTANCE RECORD, standing conditionality.  
STATEMENT: Whenever level-one state processing constructs side/label blocks, the stipulated block construction has the required properties.  
CONSUMED BY: T2 clause 4 and any capstone chain using the level-one block constructor.  
CLASS: named-obligation  
PROPOSED DISPOSITION: CARRY — the acceptance record explicitly leaves the level-one instance open; clauses 1–2 do not need it.

HYP.42  `(MP1)`  
WHERE: T2 ACCEPTANCE RECORD, standing conditionality.  
STATEMENT: The level-one clause-5 peel at the recentered key is valid, including irreducibility of the recentered \(\Phi''\).  
CONSUMED BY: T2 clause 5 and the corresponding recentered level-one branch.  
CLASS: named-obligation  
PROPOSED DISPOSITION: CARRY — irreducibility at the recentered key remains absent; original-key and level-two cases are discharged.

HYP.43  `(SEC-RANK)`  
WHERE: T2 ACCEPTANCE RECORD, standing conditionality.  
STATEMENT: The section/carrier used by the T2 construction has the required rank.  
CONSUMED BY: the T2 carrier theorem.  
CLASS: named-obligation  
PROPOSED DISPOSITION: NODE — all recorded instances are supplied by `HE3-A-PROOF`, `HE7-REF-TERM`, `HETOW-A(ii)`, or `GENTOW-4-A(iii)`.

HYP.44  `(RISE)`  
WHERE: T2 ACCEPTANCE RECORD, standing conditionality.  
STATEMENT: The carrier parameter rises strictly in each recursive transport step.  
CONSUMED BY: T2 termination and the derived height bound `HT`.  
CLASS: named-obligation  
PROPOSED DISPOSITION: NODE — the note gives level-one and deeper instance discharges through HE3/HE6 and `HE7-PERT-TRANSPORT`/`HE7-REF-TERM`.

HYP.45  `(GRADE)` cap  
WHERE: T2 ACCEPTANCE RECORD.  
STATEMENT: The usable grade is the minimum of master, carrier, frame, and local grades; HE3 currently caps level-one S3.1/S3.2 and chains through S1.8C at 0/2 or 1/2-clean evidence.  
CONSUMED BY: proof-status claims for T2’s level-one branch.  
CLASS: grade-cap  
PROPOSED DISPOSITION: NODE — this is a proof-evidence completion node; it must not be represented as a mathematical assumption on the capstone field.

### T1/T3/T5 supplier conditions

HYP.46  canonical-letter reduction scope  
WHERE: T1 ACCEPTANCE RECORD, standing conditionality.  
STATEMENT: The closed exponent-vector description is proved only for level-two canonical letters; arbitrary depth uses the terminating reduction procedure.  
CONSUMED BY: T1 canonical-form consumers.  
CLASS: conditional-theorem-leg  
PROPOSED DISPOSITION: NODE — the general statement should expose the terminating reduction instead of silently claiming the level-two closed form.

HYP.47  `C3-ladder-multiplicativity`  
WHERE: T1 effective hypothesis list.  
STATEMENT: Residual reads multiply along the C3 ladder as used in the B-law.  
CONSUMED BY: T1 B-law and higher-depth residual comparison.  
CLASS: named-obligation  
PROPOSED DISPOSITION: NODE — designated sitewise residual supplier; LOW-CONFIDENCE pending exact theorem-name audit.

HYP.48  `C3-slot-grade`  
WHERE: T1 effective hypothesis list.  
STATEMENT: Each C3 slot has the grade assigned by the residual-read computation.  
CONSUMED BY: T1 B-law and slot comparison.  
CLASS: named-obligation  
PROPOSED DISPOSITION: NODE — supplied by the accepted C3 site facts.

HYP.49  `C3-graded-scalar-covariance`  
WHERE: T1 effective hypothesis list.  
STATEMENT: Residual reads transform covariantly under the graded scalar action.  
CONSUMED BY: T1 B-law and canonical comparison.  
CLASS: named-obligation  
PROPOSED DISPOSITION: NODE — supplied by the accepted C3 package.

HYP.50  `C3-zero-read`  
WHERE: T1 effective hypothesis list.  
STATEMENT: A zero residual read is characterized as required at the relevant C3 slots.  
CONSUMED BY: T1 support and noncancellation arguments.  
CLASS: named-obligation  
PROPOSED DISPOSITION: NODE — supplied by the accepted C3 package.

HYP.51  `C3-ladder-nonvanishing`  
WHERE: T1 effective hypothesis list.  
STATEMENT: The residual quantity propagated along the C3 ladder remains nonzero on the stated branch.  
CONSUMED BY: T1 B-law and cancellation exclusion.  
CLASS: named-obligation  
PROPOSED DISPOSITION: NODE — supplied by the accepted C3 package.

HYP.52  `C3-read-codomain`  
WHERE: T1 effective hypothesis list.  
STATEMENT: Every C3 residual read lands in the asserted graded/residue codomain.  
CONSUMED BY: typing and equality statements in the T1 B-law.  
CLASS: named-obligation  
PROPOSED DISPOSITION: NODE — supplied by the accepted C3 package.

HYP.53  `(H-JA-CONJ_i)`  
WHERE: T1 effective hypothesis list.  
STATEMENT: At arbitrary depth, the preceding-letter contribution has the claimed monomial description.  
CONSUMED BY: T1’s higher-depth JA calculation.  
CLASS: hypothesis-box  
PROPOSED DISPOSITION: NODE — the acceptance record names the accepted JA supplier.

HYP.54  `(H-JA-RES-CONJ)`  
WHERE: T1 effective hypothesis list.  
STATEMENT: The whole residual polynomial and its support compare as claimed after the JA transformation.  
CONSUMED BY: T1 residual-support comparison.  
CLASS: hypothesis-box  
PROPOSED DISPOSITION: NODE — the accepted JA supplier is recorded as its discharge.

HYP.55  `(H-GENHN-CLEAR)`  
WHERE: T1 effective hypothesis list.  
STATEMENT: The outer side is clear of the competing terms excluded by the GENHN analysis.  
CONSUMED BY: T1’s outer-side residual computation.  
CLASS: hypothesis-box  
PROPOSED DISPOSITION: NODE — the accepted GENHN supplier is named in the record.

HYP.56  `(H-HETOW-LOCAL)`  
WHERE: T1 effective hypothesis list.  
STATEMENT: The HETOW local bridge and carry package holds at the required transition.  
CONSUMED BY: T1 higher-level transport.  
CLASS: hypothesis-box  
PROPOSED DISPOSITION: NODE — the accepted HETOW supplier is named in the record.

HYP.57  `(H-VARTHETA-RES_i)`  
WHERE: T1 and T5 standing conditionality, especially depths \(i\ge3\).  
STATEMENT: The standard MacLane specialization gives the required residual behavior of the varying \(\Theta_i\) at depth \(i\).  
CONSUMED BY: T1’s higher-depth B-law, T5 for \(i\ge3\), and the general tower path.  
CLASS: hypothesis-box  
PROPOSED DISPOSITION: CARRY — OPEN-CALL: the records explicitly decline to decide whether S11.2’s monomial-quotient theorem discharges it.

HYP.58  integral \(K_1\) lift range  
WHERE: T1 standing conditionality.  
STATEMENT: The integral \(K_1\) lift is asserted only when \(M>D'h\).  
CONSUMED BY: the particular T1 lift branch.  
CLASS: conditional-theorem-leg  
PROPOSED DISPOSITION: NODE — retain the inequality in the relevant theorem leg; no broader capstone hypothesis is required.

HYP.59  `WELD-M-PKG` boundary  
WHERE: T1 standing conditionality.  
STATEMENT: The package supplies its five stated fields but does not assert cross-face coherence, map uniqueness, or gauge uniqueness.  
CONSUMED BY: weld consumers in T1 and `[H-c]`.  
CLASS: conditional-theorem-leg  
PROPOSED DISPOSITION: NODE — preserve the narrower interface and prohibit downstream use of the three absent properties.

HYP.60  raw-print/canonical equality criterion  
WHERE: T1 standing conditionality.  
STATEMENT: Equality of the raw print and canonical expression is equivalent to \(z^\nu=1\), not to \(\nu=0\).  
CONSUMED BY: T1 equality and cancellation tests.  
CLASS: conditional-theorem-leg  
PROPOSED DISPOSITION: NODE — correct the consumer statement to the accepted criterion.

HYP.61  \(d v_i\) codomain  
WHERE: T1 standing conditionality.  
STATEMENT: \(d v_i\) is not generally integral; only the nonzero arguments used by consumers are integral, while its natural codomain is \(\frac{e(\mu_i)}{e(\mu_r)}\mathbf Z\).  
CONSUMED BY: T1 valuation arithmetic.  
CLASS: conditional-theorem-leg  
PROPOSED DISPOSITION: NODE — narrow the typing and integrality statements to the consumed cases.

HYP.62  `T3-JOINT-OPEN` / `F4-JOINT`  
WHERE: T3 ACCEPTANCE RECORD and T1 standing conditionality.  
STATEMENT: No realized \(p\)-adic B″ frame in the machine suite simultaneously exhibits \(\Theta\ne1\) and \(w\ne1\).  
CONSUMED BY: regression coverage only; T3 explicitly records no proof dependence.  
CLASS: audit-work-item  
PROPOSED DISPOSITION: NODE — record signed non-applicability to the proof path; it is a joint-coverage target, not a capstone assumption.

HYP.63  `[GENTOW5-W(i)]`, \(i\ge3\)  
WHERE: T5 ACCEPTANCE RECORD; `GENTOW5_WI`; `runs/qgen/Q4_output.log`.  
STATEMENT: The cumulative-window bound \(W_{\le i}\) required at every depth \(i\ge3\) holds.  
CONSUMED BY: T3/T5 higher-depth legs.  
CLASS: conditional-theorem-leg  
PROPOSED DISPOSITION: NODE — the later `GENTOW5_WI` certification proves it; the older Q4 “open” report is stale, although HYP.40’s grade report remains.

HYP.64  `WFRAME OPEN-1`  
WHERE: T5 ACCEPTANCE RECORD.  
STATEMENT: A structural closed formula or criterion for \(w_i\), including the case \(w_i=1\), is not proved.  
CONSUMED BY: no current capstone leg; T5 states only its narrower certified conclusions.  
CLASS: audit-work-item  
PROPOSED DISPOSITION: NODE — signed non-applicability to the present capstone, with the stronger formula kept out of theorem statements.

HYP.65  `WFRAME OPEN-2`  
WHERE: T5 ACCEPTANCE RECORD.  
STATEMENT: The outer tie \(u_1=w_1\) is not proved.  
CONSUMED BY: no current capstone leg.  
CLASS: audit-work-item  
PROPOSED DISPOSITION: NODE — signed non-applicability; do not let a downstream statement assume the tie.

HYP.66  `WFRAME OPEN-3`  
WHERE: T5 ACCEPTANCE RECORD.  
STATEMENT: Exact equality among the alternative avatar bookkeeping presentations is not proved.  
CONSUMED BY: no current capstone leg.  
CLASS: audit-work-item  
PROPOSED DISPOSITION: NODE — signed non-applicability; consumers must use only the certified avatar interface.

### T4 boxes and tightness suspects

HYP.67  `GENTOW6-BOX-1`  
WHERE: T4 ACCEPTANCE RECORD.  
STATEMENT: The lower-coordinate and compound \(f_1\ge2,\mu_2\ge3\) certificate classification is incomplete.  
CONSUMED BY: potentially the general weld/value branch under `[H-c]`.  
CLASS: hypothesis-box  
PROPOSED DISPOSITION: MATH — OPEN-CALL, LOW-CONFIDENCE: medium-to-large if the face audit shows it is capstone-live; otherwise it becomes a NODE recording non-applicability.

HYP.68  `GENTOW6-BOX-2`  
WHERE: T4 ACCEPTANCE RECORD.  
STATEMENT: The partial-side product-measure count has not been proved on its full claimed domain.  
CONSUMED BY: potentially the general value-side measure package `[H-c]`.  
CLASS: hypothesis-box  
PROPOSED DISPOSITION: MATH — OPEN-CALL, LOW-CONFIDENCE: medium if live; the pending weld-face audit may remove it from the capstone cone.

HYP.69  `GENTOW6-BOX-3`  
WHERE: T4 ACCEPTANCE RECORD.  
STATEMENT: The entry-driven/non-top-overflow cases have not been exhaustively classified.  
CONSUMED BY: potentially W12’s value-side partition.  
CLASS: hypothesis-box  
PROPOSED DISPOSITION: MATH — OPEN-CALL, LOW-CONFIDENCE: medium-to-large if live; otherwise close by a non-applicability node.

HYP.70  `GENTOW6-BOX-4`  
WHERE: T4 ACCEPTANCE RECORD.  
STATEMENT: The sealed case is proved only for \(f_1=1,\mu_2=2\); the \(f_1\ge2\) widening remains open.  
CONSUMED BY: potentially the compound general tower branch.  
CLASS: hypothesis-box  
PROPOSED DISPOSITION: MATH — OPEN-CALL, LOW-CONFIDENCE: medium-to-large if the widened branch reaches the capstone.

HYP.71  `GENTOW3-BOX-1`  
WHERE: T4 ACCEPTANCE RECORD.  
STATEMENT: Genre-general noncancellation and the required refinement of \(\omega_j\)-vanishing are not proved.  
CONSUMED BY: potentially `[H-c]` and the general weld computation.  
CLASS: hypothesis-box  
PROPOSED DISPOSITION: MATH — OPEN-CALL, LOW-CONFIDENCE: medium if live; the face audit must first establish reachability.

HYP.72  `disc ≠ 0` \(\sigma\)-read fence  
WHERE: T4 standing conditionality.  
STATEMENT: Splitting-type reads are valid only on the separable locus \(\operatorname{disc}\ne0\).  
CONSUMED BY: T4’s \(\sigma\)-read legs and W12’s lift labeling.  
CLASS: conditional-theorem-leg  
PROPOSED DISPOSITION: NODE — keep the fence locally; W12 `A0`/drainage already handles the excluded locus.

HYP.73  `WELD-FACE-AUDIT`  
WHERE: `docs/TIGHTNESS_CENSUS_2026-08-11.md`, S4.  
STATEMENT: Every unresolved weld face must be checked for actual reachability from the capstone path.  
CONSUMED BY: disposition of HYP.67–HYP.71 and HYP.74–HYP.80.  
CLASS: audit-work-item  
PROPOSED DISPOSITION: NODE — a finite reachability audit determines which residues are real obligations; it proves none of their mathematics.

HYP.74  `JD0-BOX-2` unit-character warrant  
WHERE: `docs/TIGHTNESS_CENSUS_2026-08-11.md`, S5.  
STATEMENT: The unit-character assertion used by JD0 is currently a synthesis reading rather than a proved theorem.  
CONSUMED BY: JD0’s contribution to `[H-c]`.  
CLASS: hypothesis-box  
PROPOSED DISPOSITION: CARRY — OPEN-CALL: carry if the JD0 face is live; otherwise replace with a signed non-applicability NODE after HYP.73.

HYP.75  `JB-NOLEG`  
WHERE: `docs/TIGHTNESS_CENSUS_2026-08-11.md`, S6.  
STATEMENT: The claimed JB non-leg membership property must hold uniformly over its unbounded quantifier.  
CONSUMED BY: `[H-b]` and W12’s partition.  
CLASS: named-obligation  
PROPOSED DISPOSITION: CARRY — OPEN-CALL: it is the census-level form of the unresolved `[H-b]` membership condition.

HYP.76  `W2-VALUE` / `W2-OPEN1`, `W2-OPEN2`, `W2-BOX1`  
WHERE: `docs/TIGHTNESS_CENSUS_2026-08-11.md`, S7.  
STATEMENT: The W2 value formula and its two side conditions hold on every claimed face.  
CONSUMED BY: the value-side package `[H-c]`.  
CLASS: hypothesis-box  
PROPOSED DISPOSITION: CARRY — OPEN-CALL: no general corpus proof is identified, while face reachability remains unaudited.

HYP.77  `DMULT-S`  
WHERE: `docs/TIGHTNESS_CENSUS_2026-08-11.md`, S8.  
STATEMENT: The exact \(\omega=1\) tier in the multiplicity computation satisfies the claimed formula, beyond the currently measured cases.  
CONSUMED BY: the weld/value package `[H-c]`.  
CLASS: named-obligation  
PROPOSED DISPOSITION: CARRY — OPEN-CALL: the present evidence is measurement rather than proof, conditional on the tier being capstone-live.

HYP.78  `S8.1-MEMBER`  
WHERE: `docs/TIGHTNESS_CENSUS_2026-08-11.md`, S1.  
STATEMENT: The above-floor divergence cases have the claimed complete membership classification.  
CONSUMED BY: potentially the general drainage/value decomposition.  
CLASS: named-obligation  
PROPOSED DISPOSITION: MATH — OPEN-CALL, LOW-CONFIDENCE: medium if HYP.73 finds a live route; otherwise NODE by non-applicability.

HYP.79  `P-BINOM`  
WHERE: `docs/TIGHTNESS_CENSUS_2026-08-11.md`, S2.  
STATEMENT: When \(p\mid\binom m2\), floor attainment and the associated lower-coordinate cases are classified correctly.  
CONSUMED BY: potentially the compound tower/value branch.  
CLASS: named-obligation  
PROPOSED DISPOSITION: MATH — OPEN-CALL, LOW-CONFIDENCE: medium if live; otherwise a signed non-applicability NODE.

HYP.80  `COMPOUND-6.5′`  
WHERE: `docs/TIGHTNESS_CENSUS_2026-08-11.md`, S3.  
STATEMENT: The compound case \(f_1\ge2,\mu_2\ge3\) satisfies the required classification and measure formula.  
CONSUMED BY: potentially the general compound genre under `[H-c]`.  
CLASS: named-obligation  
PROPOSED DISPOSITION: MATH — OPEN-CALL, LOW-CONFIDENCE: large if live; it overlaps T4’s widened compound boxes.

## Deduplication

- `A0`, `A1`, and `A2` are W12.D’s public reduction interface. `[W12-H]` and `[GENIND-H]` are lower supplier packages, not additional independent field hypotheses once that interface is carried.
- Drainage is one fact presented at several levels:
  \[
  A2 \longleftarrow \texttt{W12-BOX-4/DRAIN-N4}
  \longleftarrow \texttt{GENIND-(CS-1Q)}
  \]
  for \(n\ge4\). The former Lean name `hExhaust` belongs to the same interface. Its cubic instance is `hExhaust3`/`HEX3`; the quadratic instance is closed separately.
- Menu exactness similarly appears as `A1`, general `CS-1`/`CS-2`/`CS-EXACT`, and cubic `hMenu3`/`HMENU3`.
- `[H-e]`, `CS-3`, and the higher-order GMN \(\sigma\)-decision are the same terminal-leaf obligation.
- `[H-b]` and `JB-NOLEG` are two formulations of the JB membership residue.
- `[H-c]` is the aggregate value-side package. `JD0-BOX-2`, `W2-VALUE`, `DMULT-S`, and relevant T4/GENTOW boxes are components or potential components, not additional independent assumptions if `[H-c]` is carried wholesale.
- `GENTOW5-W(i)`, the older qgen Q4 conditional, and the cumulative-window premise used by T3/T5 refer to the same bound. `GENTOW5_WI` supplies the mathematical lemma; only its evidence-grade node remains.
- `W12-BOX-2`/`hMenu3` and `W12-BOX-3`/`hExhaust3` are discharged by the accepted `HMENU3` and `HEX3` packages respectively, although the corresponding Lean cubic leaves remain to be assembled.
- The strong Hensel inequality HYP.04 is not the landed coprime-factor Hensel theorem. The latter does not apply to the repeated-factor split \(X\cdot X^2\).
- `typeOf` shift/scale invariance is stronger than existing certificate-level shift lemmas such as `RamAt_shift`; those lemmas do not close HYP.05–HYP.06.
- `T3-JOINT-OPEN` and `F4-JOINT` are the same joint machine-coverage gap.
- `WFRAME OPEN-1` includes the older “can \(w=1\)?” tightness question; it is not a current capstone premise.
- `GENTOW6-BOX-1` and `COMPOUND-6.5′` overlap on \(f_1\ge2,\mu_2\ge3\). `P-BINOM` and `S8.1-MEMBER` are lower-coordinate subcases adjacent to that same compound classification, but are not proved identical.
- The historical `RealInstance` placeholder, old global `hExhaust`, and Haar/Denef bridge plans are superseded by the current `genuineDensity` formulation and were not revived as live rows.
- `(MP1′)` is retired by the T2 record and is not a surviving obligation.

## Coverage statement

The sweep read:

- all five T-unit acceptance records and their terminal standing-conditionality sections;
- `docs/TIGHTNESS_CENSUS_2026-08-11.md`;
- `docs/STATEMENT_LEDGER_2026-08-10.md`;
- `docs/CITE_SCOPE_RESOLUTION_2026-08-13.md`;
- `docs/PROJECT_STATE.md`, entries #32–#44;
- `leanfinal/notes/GENUINE_DENSITY_2026-08-13.md`;
- `leanfinal/notes/HENSEL_FACT_2026-08-13.md`, including §6;
- `leancheck/notes/N2_EXACT_2026-08-13.md`;
- `leancheck/notes/N3_CHECK_2026-08-13.md`, including §§9–12;
- `docs/MATH_COMPLETION_TREE_2026-08-01.md`;
- the W12 proof note’s hypothesis/menu/exhaustiveness boxes;
- GENIND’s per-genre `CS-1Q` correction;
- `GENTOW5_WI`;
- the qgen Q4 audit summary in `runs/qgen/Q4_output.log`.

The mechanical sweep used `rg --files`, targeted reads of STATUS/ACCEPTANCE/tail sections, and repository-wide searches for `OPEN`, `BOX`, `hypothesis`, `obligation`, `conditional`, `GRADE`, `LB1`, `MP1`, `SEC-RANK`, `RISE`, `CS-1Q`, `H-VARTHETA`, `Hensel`, `shift`, `scale`, `hExhaust`, and `drain`. The statement ledger warns that its extraction omits some bold-display and bullet-form hypotheses; the direct note searches were used specifically to compensate for that blind spot.

Items deliberately excluded as no longer surviving on the capstone path include the old quadratic STATUS opens closed by `N2_EXACT`, exact quadratic sharpness/rate questions not consumed by the capstone, the dropped Haar bridge, `htameFE`, retired `(MP1′)`, and historical completion-tree branches superseded by accepted W12/GENIND/T-unit records. Machine-coverage-only and stronger-than-needed questions were retained only where an explicit acceptance record still required a disposition.

## Capstone-conditionality preview

A dagger marks a CARRY-vs-NODE open call. Aggregate names are shown once; parent boxes such as `[W12-H]`, `[GENIND-H]`, and `[H-c]` must not be duplicated as additional conjuncts if their components are expanded.

If every proposed CARRY row is carried, the honest conditional capstone has the following shape:

\[
\boxed{
\begin{aligned}
&\forall\, n>0,\ \forall\,\sigma\ \text{with }\deg(\sigma)=n,\\[-2mm]
&\Bigg[
  \underbrace{\mathrm{NS7}(O)^{\dagger}}_{\text{termination}}
  \ \land\ 
  \underbrace{\mathrm{LB1}\land\mathrm{MP1}}_{\text{open T2 level-one legs}}\\
&\qquad\land\
  \underbrace{\forall i\ge3,\ \mathrm{H\!-\!VARTHETA\!-\!RES}_i^{\dagger}}
             _{\text{higher-depth residual specialization}}\\
&\qquad\land\
  \underbrace{\mathrm{A0}_{n,\sigma}\land
              \mathrm{A1}_{n,\sigma}\land
              \mathrm{A2}_{n,\sigma}}
             _{\text{W12 lift, exact finite menu, and drainage}}\\
&\qquad\land\
  \underbrace{\mathrm{JBMembership}_{n,\sigma}^{\dagger}}
             _{\text{[H-b] = JB-NOLEG}}\\
&\qquad\land\
  \underbrace{\mathrm{JD1ValuePackage}_{n,\sigma}^{\dagger}
    \left[
      \mathrm{JD0Box2}^{\dagger},
      \mathrm{W2Value}^{\dagger},
      \mathrm{DMULTS}^{\dagger}
    \right]}
             _{\text{expanded surviving [H-c] residue}}\\
&\qquad\land\
  \underbrace{
    \forall G\in\mathrm{Genres}(n,\sigma),\
      \mathrm{CS1}_G\land
      \mathrm{CS2}_G\land
      \mathrm{CSExact}_G\land
      \mathrm{CS1Q}_G}
             _{\text{general-stage transport, brackets, exactness, drainage}}
 \Bigg]\\
&\qquad\Longrightarrow\
 \exists\,\mathrm{num}_{n,\sigma},\mathrm{den}_{n,\sigma}\in\mathbf Z[q],\
 \forall O\ \text{a complete DVR with finite residue field of size }q,\\
&\hspace{47mm}
 \operatorname{genuineDensity}_{O}(\sigma)
 =
 \frac{\mathrm{num}_{n,\sigma}(q)}
      {\mathrm{den}_{n,\sigma}(q)} .
\end{aligned}
}
\]

The display uses `A0`–`A2` as the public W12 interface while exposing the still-carried lower suppliers that currently prevent those clauses from becoming unconditional. At phase 0d, the frozen theorem should choose either the public interface or its fully expanded supplier list, not redundantly assume both. The fifteen MATH rows are blockers to unconditional assembly, not appropriate hypotheses on \(O\); they therefore do not appear in this display.

HYPLEDGER: 80 rows / 20 carry-proposed / 15 math / 16 open calls
