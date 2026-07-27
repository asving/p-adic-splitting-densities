## A. Disposition of the pass-8 findings

| Pass-8 finding | REV 9 disposition | Classification |
|---|---|---|
| C1. The FAM solve counts marked branches, not trees | “**NOTE [3t] built … TREE-EXP/TREE-N/ONE-F GIVEN (SIB)**”; “**b_e^split’s multilinear formula displayed**” | **PARTIAL.** The first-split tree recursion itself is now a genuine assembly mechanism. But the displayed algebra still has an unresolved entrance boundary: \(b_e^{\mathrm{split}}\) handles branching after entry into a CTS state, while \(\iota_e\) remains a linear aggregate of marked entrances. The plan must show that every shallow/root split is already represented by a parent \(b^{\mathrm{split}}\), rather than by separately summed child entrances. The simultaneous claims that \(\beta_{e,\tau}\) is conditional on one entered state, that “SHALLOW carries \(\iota_e\),” and that \(\iota_e^T\beta_e\) restores a per-\(f\) meaning are not yet type-consistent. |
| C2. COMP falsely identifies a branch-weighted sum with an ordinary event mass | “**MARKED-BRANCH TYPING made binding**”; “**the false sentence STRUCK**”; “**\(\widehat\mu:=\sum_\eta\mu\)**” | **GENUINE.** COMP, ENT-AGG, entrances, and FAM paths are now consistently marked objects. Equal strata may contribute repeatedly without any disjointness assertion. No ordinary probability measure is claimed at this layer. |
| C3. Capstone ledger incomplete | “**CAPSTONE LEDGER made canonical and complete … CL-1…CL-12**” | **PARTIAL.** The omissions named in pass 8—REL, X.2, X.3, RS.0, tree assembly, SQ.2 feedback, and the SAE perimeter—are restored. But the ledger still omits other explicitly open load-bearing conclusions: CTS-M(i) fixed syntax/target compatibility, [2a] M1/M5 menu completeness, X.1a’s index dictionary, and the M4b/M4b-T translation/count interface except insofar as parts are implicitly folded into XHD/RS.0. Under the plan’s own “all still-open load-bearing conditions” standard, “complete” remains false. |
| K1. Entrance height suppressed | “**\(h_{\rm ent}\) an EXPLICIT argument**”; COMP-h fixes it, COMP-\(\Sigma\) sums only continuation heights, ENT-AGG sums it | **GENUINE.** The height is now threaded and summed exactly once. |
| K2. CTS-M(iv)-REP cannot supply sibling independence | “**(SIB) named, stated, statused OPEN with the SIB-gate**”; REL.2(c) re-homed | **GENUINE.** The single-branch and joint-sibling burdens are now correctly separated. |
| K3. (†-AGG) vii merely named a normalization | “**displayed tree-shape identity**”; marked\((N)\) separated from decided\(_\sigma(N)\) | **GENUINE**, conditional on TREE-EXP/TREE-N and the missing count-polynomial interface. ONE-F supplies coefficient one through the choice-free tree partition. |
| K4. Multiplicity-gate status inconsistent and irrelevant to tree assembly | “**D4-m2 PASSED 33/33**”; “**tree-assembly refuter is the NEW SIB-gate**” | **GENUINE.** Status and scope are now explicit. |
| K5. Linear \(b_e\) hides simultaneous children | “**MULTILINEAR EXIT FORMULA displayed**”; multiset convolution and strict-smaller-block induction supplied | **PARTIAL.** The local branching exit is correctly nonlinear in smaller child blocks, but the plan has not yet shown that the same construction covers branching in the shallow entrance layer. The \(\beta/\iota\) typing around this boundary remains inconsistent. |

## B. Full-depth test of the [3t] recursion

Take a tree with a root shared segment ending at a two-child branching cell. Let:

- \(a_0\) be the product of the fresh-volume factors along the shared root segment, including the root branching-cell outcome exactly once;
- the left child have an unbranched segment of mass \(a_1\), ending at another two-child branching;
- \(x,y\) be the conditional masses of the two descendant subtrees there;
- \(z\) be the conditional mass of the right root-child subtree.

The first-split recursion gives

\[
P(T)
 =a_0\,P(T_L\mid c_0)\,P(T_R\mid c_0)
 =a_0\,(a_1xy)\,z.
\]

The direct, inclusion-exclusion-free decomposition is

\[
T
 =
P_0\cap
\bigl[(A_{\rm seg}\cap T_{L_1}\cap T_{L_2})\cap T_R\bigr].
\]

Conditioning first at \(c_0\), root SIB gives

\[
P(T\mid c_0)
 =
P(A_{\rm seg}\cap T_{L_1}\cap T_{L_2}\mid c_0)
 P(T_R\mid c_0).
\]

C.1.5 charges the left unbranched segment by \(a_1\); conditioning at its descendant branching cell and applying SIB again gives \(xy\). Hence the direct decomposition is also

\[
a_0a_1xyz.
\]

Thus the recursion reconstructs the once-per-tree node product, with neither a duplicated shared prefix nor an inclusion-exclusion correction.

### Is SIB strong enough at descendant branchings?

Yes, as written. It quantifies over:

> “Let \(\eta\) be a realized prefix … for each \(j\), let \(S_j\) be … a prescribed finite subtree \(T_j\).”

That is not merely a one-step statement. It applies at every realized branching prefix and lets a root sibling event already be an arbitrarily deep subtree event. Recursive application at descendant prefixes therefore supplies the tree-indexed product law needed by the induction.

If “prescribed finite subtree” were weakened to “next outcome,” it would be insufficient. The SIB-gate tests only that weaker, one-step face, so the theorem is stated strongly enough but the gate does not exercise its full quantified depth. REV 9 records this limitation honestly.

A remaining interface should be made explicit in the eventual proof: to replace

\[
\mu(S_j\mid \Sigma_c)
\]

by the state-indexed value \(\beta_{e_j,\tau_j(c)}\), the continuation law must depend only on the child CTS state, not on unused parent/sibling cell data. This should follow from REL.2 plus the single-branch Markov/REP package, but it is not part of the displayed SIB equation itself.

### Well-foundedness

The local argument is genuine:

\[
m\ge2,\qquad e_j\ge1,\qquad \sum_j e_j\le e
\quad\Longrightarrow\quad e_j<e\ \text{for every }j.
\]

Therefore \(b_e^{\mathrm{split}}\) uses only already-solved smaller blocks, while the equal-\(e\) direction remains the single-child linear kernel \(K_e\). Multiset convolution is finite because a fixed degree has only finitely many factorization-type multisets.

The draft must prove that every branching outcome satisfies the displayed positive-size conservation law. Calling it “the same degree identity” is not a substitute for checking it against every CTS branching outcome, but the proposed order itself is sound.

## C. Verdict pin

The alphabet

\[
V=\{\text{finite multisets of }(E,F)\}
\]

is sufficient for the theorem’s target. The target \(\sigma\) is exactly such a multiset, and multiset union over leaves retains multiplicities while forgetting irrelevant branch order.

The three certificate clauses are plausibly cell-data-only:

- \(\tau\)-irr uses accumulated \(e_r,g_r\), the cluster degree, and the Montes irreducibility certificate.
- \(\tau\)-ns uses the no-side status and the certified exact factor \(\widehat\Phi^\mu\).
- \(\tau\)-hen uses root residual multiplicity one and residue degree \(g\).

None inherently requires inspecting the ambient polynomial beyond the retained cell/node data. But coverage, mutual exclusion, and VP-SOUND remain genuine proof duties. In particular, “compatibility is automatic” is valid only after the cell-data nature and exactly-one-verdict theorem have actually been established. Treating these as honest kernels with oracle refuters is architecturally acceptable.

## D. DAG, refuters, and ledger

The nine mathematical notes form an acyclic order:

\[
[1]\to[2a]\to[1v]\text{-COND}\to[2b]\to[1v]\text{-FULL}
\to\{[2r],[5]\}\to[3t]\to[3]\to[4].
\]

The position of [3t] is coherent: it needs [1] for the canonical tree, [2r] for base-changed sibling factors, and precedes both consumers.

There is one edge-list inconsistency. The diagram visually has \([5]\to[3t]\), and CL-4 says TGT consumes X.3, but the prose “REV 9 additions” lists only §C, [1], and [2r] as incoming edges to [3t]. If TGT literally identifies the complete-tree series with the full density, then it is conditional on X.3 and \([5]\to[3t]\) must be present. Otherwise [3t] must state only the finite-tree mass identity, leaving the density equality to [4].

The open-kernel/refuter roster is substantially coherent. In particular, SIB has its own exact gate and no longer hides behind REP. The main remaining governance defect is the supposedly complete CL ledger:

- CTS-M(i) is required for a fixed finite matrix and globally compatible indices.
- M1/M5 are required for the finite, exhaustive species/menu catalogue.
- X.1a is an open load-bearing input to the discriminant/depth route.
- M4b/M4b-T is used in RS.1’s height translation and count closure beyond the portions explicitly packaged into XHD.
- The local degree-conservation check required by \(b_e^{\mathrm{split}}\) is not identified in CL-11 or elsewhere.

Thus CL-1…CL-12 is improved but not yet a complete acceptance ledger.

## E. Fresh sweep

The most serious remaining issue is the entrance boundary of the recursion.

REV 9 correctly defines \(\beta_{e,\tau}\) as:

> “the probability, given ONE branch entering state \(\tau\), that its full subtree completes…”

That conditional object satisfies

\[
\beta_e=K_e\beta_e+b_e.
\]

It should contain no entrance vector. An entrance law is paired only after this conditional solve:

\[
\iota_e^T\beta_e.
\]

But elsewhere the plan continues to say that “SHALLOW carries \(\iota_e\)” inside \((R_e)\), while \(\iota_e\) is the aggregate marked mass of all shallow entrances. If a shallow cell spawns two siblings and both are inserted separately into \(\iota\), then

\[
\iota_{e_1}^T\beta_{e_1}+\iota_{e_2}^T\beta_{e_2}
\]

is still a marked sum, not the required sibling product. TREE-EXP cannot change that algebra after the fact. The plan must establish that such a split is represented at its parent by one \(T\!\cdot G\) factor times the multilinear child convolution, and that only a genuinely single root entrance is paired linearly at the outermost boundary. No such root/shallow analogue of \(b_e^{\mathrm{split}}\) is displayed.

Two lesser issues remain:

- The branch set is written \(\{b_1,\ldots,b_m\}\), but the final draft must give a canonical sibling indexing or an explicitly unordered convolution convention. Otherwise equal-shape siblings can introduce hidden automorphism factors in \(C_{\widehat T}\).
- The risk-register preamble still says “D4R.2’s pool bound (3i)” survives, although the live plan explicitly withdraws literal coefficient-one (3i) in favor of the \(M(\widehat P)\)-carrying bound. That stale statement should not enter an acceptance record.

## CRITICAL OBSTRUCTIONS

1. **The solve/tree-series interface remains incomplete at shallow entrances.**  
   The local first-split recursion and \(b_e^{\mathrm{split}}\) are sound, but the plan does not prove that every root or shallow split is routed through that multilinear construction before the linear marked entrance aggregation. The current \(\beta/\iota/\mathrm{SHALLOW}\) descriptions are mutually inconsistent, so RS.1’s claimed solve \(=\) tree-series identity is not yet established.

2. **The canonical capstone ledger is still incomplete under its own standard.**  
   CTS-M(i), M1/M5, X.1a, and the remaining M4b/M4b-T interface are open and load-bearing but absent as explicit CL items. Consequently the acceptance-record protocol can still mark the capstone conditional on less than everything it consumes.

## CONCERNS

1. The prose edge list omits \([5]\to[3t]\), although TGT consumes X.3 and the diagram/acceptance order imply that edge.

2. SIB is theorem-level strong enough for arbitrary-depth recursion, but its gate exercises only one-step sibling laws.

3. The substitution of the child-state value \(\beta_{e_j,\tau_j}\) for \(\mu(S_j\mid\Sigma_c)\) needs an explicit parent-context-independence interface from REL.2/REP.

4. Canonical sibling indexing or automorphism handling must be specified for equal-shape siblings and the tree-count \(C_{\widehat T}\).

5. The strict-smaller-block argument depends on a per-outcome degree-conservation theorem that is asserted but not yet tied to the CTS outcome roster.

6. The risk register retains a stale statement that literal (3i) survives, contrary to the live \(M(\widehat P)\)-carrying replacement.

- **CRITICAL OBSTRUCTIONS: 2**
- **CONCERNS: 6**
- **Verdict: UNSOUND**

The verdict is not caused by SIB, VP, XHD, HMC, ESCAPE, WEIGHT-CHARGE, TRACK-COUNT, or other honestly open kernels. The first-split mechanism itself is sound given the stated all-depth SIB kernel. The unsoundness comes from the still-missing shallow-entry realization of that recursion and the still-incomplete canonical conditionality ledger.

**Drafting clearance:** [1] D4-R remains cleared in its branch-tree form, conditional on the stated SAE perimeter; [2a] SPECIES remains cleared as branch-aware and count-free; [1v]-COND is now cleared for drafting only in its strictly marked-\(\widehat\mu\), XHD-conditional form; [3t] TREE is cleared for drafting as a theorem package conditional on SIB/VP, but not for acceptance. [3] RESUM and [4] SQUEEZE are not cleared as complete notes.
