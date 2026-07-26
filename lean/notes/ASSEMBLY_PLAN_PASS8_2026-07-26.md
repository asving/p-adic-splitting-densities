## Pass-8 structural review

REV 8 repairs the formal entrance indexing and expands the capstone ledger in the places identified by pass 7. The branch-cell choice itself is coherent for constructing a single-branch transition system.

It does not, however, provide the missing map from that single-branch system to factorization-type probabilities. The linear FAM solve retains branch multiplicity rather than eliminating it. Worse, COMP’s asserted disjointness at fixed shape contradicts the motivating F1 example. Consequently RS.1 does not currently establish that the rational solve computes each polynomial \(f\) exactly once.

### A. Disposition of every pass-7 finding

| Pass-7 finding | REV 8 disposition | Classification |
|---|---|---|
| C1. Entrance granularity mismatch | “**REFINEMENT CHOSEN over aggregation**”; primitives \(\iota_{e,\varepsilon,\beta_0}\), \(I^{ent}_{\varepsilon,\beta_0}\); “**COMP-h/COMP-\(\Sigma\) stated PER \((\varepsilon,\gamma,h)\)**”; aggregate only through ENT-AGG | **PARTIAL.** The indices on the displayed mass and count factors now match. But the event used by COMP is still described as an ordinary union of \(f\)-events and asserted disjoint at fixed shape. F1 explicitly supplies same-shape branches with coincident strata. Thus the new primitives are naturally marked-branch masses, not ordinary event masses, and the advertised COMP identity has not been repaired at the measure-theoretic level. Entrance-height indexing is also suppressed in the formulas. |
| C2. SQ.4 ledger omits POLY and TRACK-COUNT | “**PLUS … CTS-M(iv)-POLY … and TRACK-COUNT with its D(n)/positive-genuine-increment companion duties**” | **PARTIAL.** The two specifically named omissions are restored. But the ledger is still advertised as complete while omitting other open load-bearing conclusions, notably REL.1–REL.3, X.2 PROGRESS itself, X.3 where used, RS.0’s position/height elimination, RS.1’s tree/branch mult-accounting theorem, and SQ.2’s no-equal-\(e\)-feedback check. |
| K1. \(\iota_e\in\mathbb Q(q)^{\mathcal C_n}\) not concluded | “**INIT-RAT … hence \(\iota_e\in\mathbb Q(q)^{\mathcal C_n}\), a CONCLUSION … CITED by RS.2**” | **GENUINE**, conditional on the corrected marked-branch/entrance semantics and XHD. |
| K2. \(W_{\rm ent}\) not constructed | “**\(W_{\rm ent}(\varepsilon):=\sum_{r\in reads(\varepsilon)}w_r d_r\)**” | **GENUINE.** Bounds and normalizations are now per entrance shape; no common raw entrance count is claimed. |
| K3. HMC probe mixes fixed and resummed heights | “**TWO-LAYER … COMP-h … \(g\) only; … \(G\) appears only after the \(h_2\)-sum**” | **GENUINE.** The probe now respects the fixed-height/resummed distinction. |
| K4. [2b] proof order and STATE-probe-2 attribution | “**FIRST prove the XHD package … THEN instantiate … ONLY THEN … consume CTS-M(iv)-REP**”; seal “**from CTS-M(iv)’s conditional \((T\!\cdot\!G)\)-rows alone**” | **GENUINE.** The governance cycle is removed at the stated proof order. |
| Fresh sweep: row/column inconsistency | “**\(\iota_e\) is the entrance COLUMN vector acting once … via \(\iota_e^T\); ‘row’ retired**” | **GENUINE.** |

## B. Branch-cell decision and multiplicity trace

The branch-cell choice is internally sensible through the local layers:

1. \(T_{\rm can}(f)\) may contain several continuing branches.
2. Each eligible continuation becomes a separate branch entrance.
3. \(I^{ent}_{\varepsilon,\beta_0}\) counts realized marked entrances.
4. \(\iota_{e,\varepsilon,\beta_0}\) uses D4R.1-SUM, hence also counts mass once per marked branch.
5. Each CTS path walks one branch, and \(T\), \(g\), \(G\), and \(K_e\) introduce no further branching multiplicity.
6. The linear expression
   \[
   \iota_e^T(I-K_e)^{-1}b_e
   \]
   therefore preserves the multiplicity already present in \(\iota_e\).

Thus multiplicity enters exactly once as a **branch multiplicity**. The problem is that the target density requires each \(f\), equivalently each complete tree fiber, exactly once. No displayed operation converts the former into the latter.

### Same-template branches

Suppose one \(f\) has two branches realizing the same \((\varepsilon,\gamma,h)\). D4R.1-SUM counts its mass twice. The CTS/FAM solve also counts the two marked walks twice.

COMP attempts to avoid this by asserting:

> “within one shape prefix distinct \(\eta\) occupy distinct cells, so no multiplicity enters HERE”

That is incompatible with the F1 example underlying REV 8: two same-shape branches may lie over literally equal strata. The union
\[
\bigcup_\eta S(\eta,\top)
\]
then has ordinary mass counted once, while the D4R.1-SUM and \(I^{ent}\) count it twice. COMP-h cannot identify both quantities.

The identity could be formulated on a marked-branch space, but REV 8 does not define such a measure space, and a marked-branch measure would generally have total mass greater than one. It would not itself be a density.

### Different-template branches

If one digit cell spawns branches realizing different templates, the same defect appears across the \((\varepsilon,\gamma)\)-sum. Adding the branch-walk masses computes an expected number of successful/terminal branches, not the probability of the complete factorization tree.

For a factorization type \(\sigma\), sibling outcomes must be assembled jointly. Schematically, after a shared prefix one expects something of the form

\[
\text{shared-prefix mass}\times
\prod_j \text{conditional child-tree mass}_j,
\]

with the shared prefix charged once and with the child types combined into the multiset \(\sigma\). It is not

\[
\sum_j \text{mass of branch }j.
\]

The plan mentions “mixed legs composed multiplicatively” and REL.2(c) sibling independence, but supplies no tree-transition or hyperedge formula showing:

- which shared ancestral factor is charged once;
- how simultaneous branches are combined;
- how equal branches and automorphisms are handled;
- how the children’s types combine into \(\sigma\);
- why the resulting expression is represented by the stated linear exit vector \(b_e\);
- how the branch-indexed linear solve becomes the mass of a complete tree fiber.

REL.2(c), even if proved, would justify a product of conditional sibling laws. It cannot turn a sum of individual branch masses into a joint-tree probability.

### Normalization of (†-AGG) input vii

Input vii is not presently a well-defined normalization. It offers:

> “mult \(\equiv1\) proved on the family, or the tree-assembly regrouping of RS.1”

The first alternative is clear but does not cover the \(m\ge2\) regime. The second merely names the missing theorem. There is no displayed weight \(w(f,\eta)\) satisfying, for every decided \(f\),

\[
\sum_{\eta\text{ used for }f} w(f,\eta)=1,
\]

nor a joint-tree regrouping identity replacing such weights.

Multiplicity weights currently equal numbers of branches, not reciprocal or Möbius-type normalization weights. Therefore the \((\varepsilon,\gamma)\)-sum in (†-AGG) is branch-weighted and cannot be identified with `decided_σ(N)`, which counts each polynomial once.

The queued/externally reported \(33/33\) multiplicity census can verify D4R.1-SUM versus D4R.1-EV. It does not establish the missing tree-to-density normalization.

### Does anything still consume a per-\(f\) partition?

Yes:

- RS.1 uses the fibers \(\{f:T_{\rm can}(f)=T\}\).
- SQ.1 uses those fibers for the finite-level box partition.
- The definition of `decided_σ(N)` counts those \(f\)-fibers once.

Those are legitimate partitions because \(T_{\rm can}\) is choice-free. The unresolved interface is precisely between this per-\(f\) tree partition and the branch-weighted CTS/FAM sum.

## C. Entrance refinement and ENT-AGG

At the purely indexed level, COMP-h and COMP-\(\Sigma\) now pair the same entrance shape \(\varepsilon\), landing cell \(\beta_0\), template \(\gamma\), and continuation factors. This repairs pass 7’s original cell-aggregate/per-shape mismatch.

ENT-AGG is licit only under a narrower reading:

- the entrance quantities are marked-branch masses;
- every continuation law depends only on the landed CTS state;
- CTS-M(iv)-REP supplies representative independence;
- HMC supplies the required multi-step height factorization;
- no sibling or tree-level condition changes the branch continuation law.

Under those assumptions, it is algebraically valid to factor a common continuation row out of a sum of marked entrances. It does **not** show that the aggregate is an ordinary initial probability distribution for \(f\)-events.

There are two remaining entrance-level defects.

First, \(\varepsilon\) is said to retain shallow heights as parameters, and the primitives are defined “at each height point,” but the notation normally writes only
\(\iota_{e,\varepsilon,\beta_0}\). ENT-AGG later sums over \(h\in H(\varepsilon)\), while COMP-h only displays the continuation height \(h\in H(\gamma)\). The unsummed primitive should still carry an entrance-height argument. As written, it is unclear whether COMP-h uses a fixed entrance height or an already resummed entrance mass.

Second, COMP’s “cylinder” is not a disjoint union whenever one \(f\) carries multiple same-shape branches. Consequently:

- the count shadow \(I^{ent}_{\varepsilon,\beta_0}\prod T\) is a marked-history count;
- the right side of COMP-h is a branch-weighted sum;
- the left side, if interpreted as the ordinary mass of a union of \(f\)-events, is not equal to it.

So COMP-h/COMP-\(\Sigma\) are syntactically like-with-like in \(\varepsilon\), but not yet semantically like-with-like in their underlying measure object.

## D. DAG, roster, and ledger

The acceptance-event DAG remains acyclic. The [1v]-COND → [2b] → [1v]-FULL order and the explicit internal [2b] proof order are structurally sound.

The new branch architecture does not introduce a graph-theoretic cycle. It introduces a missing theorem at RS.1: the branch automaton’s output has not been shown equal to the complete-tree fiber sum.

The refuter roster also has two gaps:

- The multiplicity gate tests D4R.1-SUM/-EV, not RS.1’s conversion of simultaneous branch families into a once-per-\(f\) type mass.
- RESUM-n3 is not a satisfactory refuter for the general branch assembly if its exercised cubic families have multiplicity one or lack simultaneous same-shape branches. The plan itself records that the old D4-n3 instance does not exercise this regime.

There is also a status inconsistency: the surrounding REV 8 account says the multiplicity regime was census-confirmed \(33/33\), while the plan repeatedly calls the multiplicity gate “QUEUED.” One status should govern the acceptance record. Either way, this gate does not close RS.1.

Finally, SQ.4 and §7 still do not contain a genuinely complete capstone ledger. In addition to the newly added POLY and TRACK-COUNT entries, the target consumes at least:

- REL.1–REL.3 for mixed/base-changed legs and domination;
- X.2 PROGRESS, not merely X.1b used inside its proof;
- X.3 for termination/total-mass claims and E0’s route;
- RS.0’s position/height elimination;
- RS.1’s tree/branch aggregation and multiplicity conversion;
- SQ.2’s no-equal-\(e\)-feedback theorem;
- the choice-free/total tree interface, including the stated SAE repair dependency.

Some may eventually be accepted note theorems rather than “open kernels,” but the acceptance-record rule is explicitly framed as listing all still-open load-bearing conditions. Under that standard, the claimed capstone ledger remains incomplete.

## CRITICAL OBSTRUCTIONS

1. **The single-branch FAM solve counts marked branches, not complete factorization trees.**  
   Multiplicity enters once through \(I^{ent}\) and \(\iota\), is preserved by the linear CTS solve, and is never normalized or converted into once-per-\(f\) tree mass. Simultaneous branches require a displayed joint tree/hyperedge assembly with shared-prefix mass charged once and child types combined multiplicatively. RS.1 currently only names that missing conversion.

2. **COMP’s measure identity contradicts the branch-tree premise.**  
   REV 8 asserts that distinct realized histories at a fixed shape are disjoint, while F1’s same-shape multiplicity example says their strata may coincide. Hence the ordinary union mass in COMP-h is not the D4R.1-SUM branch-weighted mass represented by \(I^{ent}\) and \(\iota\). ENT-AGG therefore yields, at best, a marked-branch aggregate rather than an initial probability distribution.

3. **The capstone conditionality ledger remains semantically incomplete.**  
   POLY and TRACK-COUNT were added, but REL, X.2, X.3 where consumed, RS.0, RS.1 mult-accounting, SQ.2’s equal-\(e\) closure check, and the tree/SAE perimeter are still absent from the purported complete acceptance ledger.

## CONCERNS

1. The entrance-height coordinate is not consistently indexed: primitives are defined at each \(h_{\rm ent}\), but COMP suppresses it and ENT-AGG later sums it.

2. CTS-M(iv)-REP proves single-branch representative independence; it does not by itself prove independence from sibling-tree context. That burden must be carried by a precise joint sibling theorem, not by the word “entrance-independent.”

3. (†-AGG) input vii is a duty label, not a normalization. No weights or regrouping identity show that each decided \(f\) contributes total coefficient one.

4. The multiplicity-gate status is inconsistent (“33/33 confirmed” versus “QUEUED”), and its specified content does not refute the RS.1 tree-assembly defect.

5. The linear exit-vector notation \(b_e\) obscures how a branching cell simultaneously contributes several child factor types. Without a displayed multilinear/tree formula, it is unclear that the target \(\sigma\) is even an observable of one branch state.

- **CRITICAL OBSTRUCTIONS: 3**
- **CONCERNS: 5**
- **Verdict: UNSOUND**

The verdict is not caused by XHD, HMC, WEIGHT-CHARGE, TRACK-COUNT, E0, or the other honestly open kernels. It is caused by the absent branch-to-tree probability assembly and the resulting invalid COMP/(†-AGG) identifications, together with the still-incomplete capstone ledger.

**Draft readiness:** **[2a] SPECIES remains cleared for drafting in its branch-aware, count-free form.** The branch-tree form of **[1] D4-R remains cleared for drafting/verification** under its stated SAE condition. **[1v]-COND is not cleared as a complete note**, because its COMP theorem currently conflates ordinary event mass with marked-branch mass. No later complete note is cleared.
