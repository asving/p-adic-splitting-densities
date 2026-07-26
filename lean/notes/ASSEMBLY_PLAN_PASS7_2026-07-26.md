## Pass-7 structural review

REV 7 genuinely repairs the height-domain cycle and the fixed-height/resummed-height typing defect. The acceptance-event DAG can now be read acyclically, and the four pass-6 concerns are substantially resolved.

A new interface defect remains at INIT/ENT-COUNT/COMP: the plan alternates between an entrance vector aggregated over every shallow entrance to \(\beta_0\) and an entrance count refined by “\(\gamma\)’s entrance shape.” Those are not matching initial objects. This affects both the mass identity and the finite-count shadow. The advertised nine-input ledger also still omits load-bearing coefficient and SQUEEZE conditions.

### A. Disposition of every pass-6 finding

| Pass-6 finding | REV 7 disposition | Classification |
|---|---|---|
| C1. Hidden \([1v]\leftrightarrow[2b]\) cycle | “**XHD named and displayed as CTS-M’s hypotheses; ACCEPTANCE SPLIT — [1v]-COND … → [2b] … → [1v]-FULL**” | **GENUINE.** XHD can be stated using the already-defined CTS cells, finite templates, height coordinates, and C.1.5 weights. Defining \(G\) by the length-one XHD-d domain is legitimate in a conditional theorem: it defines the consequence of an assumed exact domain; it does not assert that the domain is exact without [2b]. There is no remaining edge on which the *content* of conditional CTS-M requires [2b] merely to be stated. Within [2b], the proof order must be XHD first, then instantiate conditional REP, then prove M2. The text mostly says this explicitly. |
| C2. Heights double-typed at COMP/RS.1 | “**templates CARRY height points**”; “**\(g\) … fixed-height**”; “**\(G:=\sum g\) is FAM-only**”; “**COMP-h → COMP-\(\Sigma\)**” | **GENUINE.** At fixed \((\gamma,h)\), COMP-h uses \(g(h_i)\). The single sum over \(H(\gamma)\) then uses HMC to replace \(\sum_h\prod g_i(h_i)\) by \(\prod G_i\). Only after that does the depth automaton use \(K_e\). RS.1 no longer performs a second height sum. HMC is consumed exactly at the whole-domain-to-product step. |
| C3. Bare \(|\beta_0|\) is not an entrance count | “**ENTRANCE COUNT \(I^{ent}_\gamma\)**”; “**D4R.1’s \(C_{\widehat P}\) refined by the landing cell**”; “**degree \(\le W_{\rm ent}(\gamma)\)**” | **PARTIAL.** The correct kind of object and the correct polynomiality burden have been identified. The stated bound is by the shallow-entrance pool dimension \(W_{\rm ent}(\gamma)\), and the plan requires that dimension to be displayed. But \(I^{ent}_\gamma\) is not aligned with \(\iota_{e,\beta_0}\): the former is restricted to “\(\gamma\)’s entrance shape,” while the latter is the mass of the entire event that the root/branch cascade enters \(\beta_0\). See Critical Obstruction 1. |
| C4. Conditionality ledger omits PART/MEAS/COMP typing | “**The NINE-input ledger: XHD · D4R.0 · PART · REP · MEAS · HMC · ACT · INIT+ENT-COUNT · COMP-typing**” | **PARTIAL.** These nine items appear consistently at RS.PRE, SQ.4, §7, and R9. The three pass-6 omissions are genuinely restored. But the ledger advertised at SQ.4 and the acceptance protocol is still not complete for Theorem U: CTS-M(iv)-POLY and TRACK-COUNT are load-bearing and absent from SQ.4’s inline list. |
| K1. \(G_{m,o}\) under-indexed | “**\(g^{\alpha,\beta}_{m,o}/G^{\alpha,\beta}_{m,o}\)**” | **GENUINE.** Source and target cell dependence is now represented everywhere relevant. |
| K2. \(k\le8\) cannot refute E0 | “**SYMBOLIC CLOSED-CLASS REFUTER**”; finite-depth decay “**CONSISTENCY-CLASS ONLY**” | **GENUINE.** In a finite substochastic chain, a closed active class with stochastic rows gives \(\rho=1\) and directly refutes E0. The finite-depth observations are correctly demoted. |
| K3. TRACK/STALL probes overstate scope | “**refutes SEALED CANDIDATE constants … only**”; existential statements “**decided by derivation alone**” | **GENUINE.** Their logical scope is now honest at the probe definitions, §7, and the risk register. |
| K4. NO-JUNK-POLE too strong | “**ACTIVE-VALUE … burden is AGREEMENT, not junk invertibility**”; junk singularities checked removable | **GENUINE.** This is the appropriate active-subsystem convention. It preserves the fixed symbolic rational function while avoiding an unnecessary demand that \(I-D_p\) be invertible. |

## B. Height trace and CTS-M strength

For a correctly aligned entrance class, the new height trace is well typed:

1. A parametric CTS path \(\gamma\) has an exact domain \(H(\gamma)\).
2. An instantiated event \((\gamma,h)\) receives
   \[
   \iota_{\beta_0}\prod_i T_i g_i(h_i).
   \]
3. XHD-d/XHD-s justify summing exactly over \(H(\gamma)\).
4. HMC alone supplies
   \[
   H(\gamma)=\prod_iH(\gamma_i^1),
   \qquad
   \sum_{h\in H(\gamma)}\prod_i g_i(h_i)=\prod_iG_i.
   \]
5. COMP-\(\Sigma\) therefore produces \(\iota_{\beta_0}\prod_i(T_iG_i)\).
6. The depth regular language is then summed by \((I-K_e)^{-1}\), with no remaining height coordinate.

Thus the COMP-h/COMP-\(\Sigma\) split is strong enough for the height and depth part of RS.1, conditional on XHD and HMC.

CTS-M is not yet strong enough for RESUM exactly as written, because its initial factor is not consistently indexed. It is also missing an explicit conclusion that each component of \(\iota_e\) is a fixed rational function of \(q\), or a finite displayed sum of common-exponent entrance-count polynomials. RS.2 presently assumes this.

For SQUEEZE, CTS-M supplies the needed positive path law and active kernel only after that entrance defect is resolved. SQUEEZE additionally depends on REL, X.2/WEIGHT-CHARGE, TRACK-COUNT, and the no-equal-\(e\)-feedback argument; those are not conclusions of CTS-M and must remain separate conditions.

## C. Acceptance-event DAG

The relevant acceptance events are:

- \(C\): certified §C/decomposition perimeter
- \(D\): [1] D4-R
- \(S\): [2a] SPECIES
- \(V_c\): [1v]-COND, CTS-M conditional on XHD and other explicitly open clauses
- \(X\): [2b] STATE-GEOM, proving XHD and M2
- \(V_f\): [1v]-FULL, recording XHD discharge
- \(L\): [2r] REL
- \(E\): [5] EXHAUST
- \(R\): [3] RESUM
- \(Q\): [4] SQUEEZE

The material edges are

\[
C\to D,\quad D\to S,\quad S\to V_c,\quad
V_c\to X,\quad X\to V_f,
\]

\[
X\to L,\quad S\to E,\quad X\to E,
\]

\[
V_f,L,E,X\to R,\qquad R,L,E\to Q.
\]

There is no directed path from \(X\) or \(V_f\) back to \(V_c\). In particular:

- XHD-w/d/s can be stated before being proved.
- Length-one \(G\) is a conditional construction from XHD, not a disguised proof of XHD.
- \([2b]\) may use the theorem \(XHD\Rightarrow REP\) only after establishing XHD inside its own proof.

The last point should be made an explicit internal proof-order sentence because M4b still says “CTS-M(iv)-REP + M2(ii) close the count.” If that sentence were used in proving XHD itself, the cycle would return; on the current intended reading it is used afterward.

A smaller governance blemish remains: STATE-probe-2 says its sealed rows come from “RS.PRE/M2,” although [3]/RS.PRE follows [2b]. The rows are already definable from CTS-M(iv), so this need not be a mathematical cycle, but the seal should not formally depend on an unaccepted later note.

## D. Kernel/refuter roster

The roster is now mostly honest:

- D4R.0 — D4-n3.
- CTS tables, ACT, MEAS, REP, and selected ENT-COUNT instances — VALUE-Fq/VALUE-p, JOINT, and COMPOSE.
- HMC — an exact two-step mismatch can refute the universal factorization claim.
- XHD/M4a-X — MENU-n3 can refute a sealed exact-domain formula inside its tested box.
- M2/RS.0 — STATE-probe-2 and RESUM-n3.
- REL — REL-n4.
- X.1a/X.2 — EXHAUST-n3.
- WEIGHT-CHARGE and TRACK-COUNT — probes now refute only sealed constants; derivations decide the existential statements.
- E0 — the symbolic closed-class layer is a genuine refuter.
- ACTIVE-VALUE — a surviving wild-prime component pole or disagreement with the active solve is a genuine counterexample.

One probe specification remains ambiguous. HMC-probe varies a fixed first-step height \(h_1\) but says it compares with products of resummed \(T\cdot G\) factors. A fixed-\(h_1\) event naturally carries \(Tg(h_1)\), not \(TG\). Unless the probe explicitly says which coordinates are held fixed and which are summed, it risks recreating the height-typing error at the verification layer.

## Fresh sweep

The principal new defect is the entrance granularity mismatch.

A CTS template was defined as a source cell plus within-block transition steps. It therefore has no separately defined “entrance shape.” Yet CTS-M(iii) defines

> “\(I^{ent}_\gamma\) … with \(\gamma\)’s entrance shape”

while COMP-h uses

> “\(\iota_{e,\beta_0}\)”

where \(\iota_{e,\beta_0}\) aggregates the entire root/branch-cascade entrance event.

There are only two possible readings, and neither matches all displays:

- If \(\gamma\) is only the within-block CTS path, “\(\gamma\)’s entrance shape” is undefined, and \(I^{ent}_\gamma\) should aggregate all shallow entries into \(\beta_0\).
- If \(\gamma\) includes a particular shallow entrance shape, then \(I^{ent}_\gamma\) is meaningful, but COMP-h cannot use the total \(\iota_{e,\beta_0}\); it needs the mass of that same entrance class.

This also affects the claimed bound and normalization in (†-AGG). Different shallow entrance shapes can have different ledger exponents \(A\). Their raw realized-prefix counts cannot necessarily be combined into one \(I^{ent}\) and then multiplied by a single \(q^{nN-A(\gamma)}\) unless a common normalization is displayed.

A second issue is coefficient closure. ENT-COUNT says each refined count is polynomial, but CTS-M(iii) does not state that the mass vector \(\iota_e(q)\) is in \(\mathbb Q(q)^{\mathcal C_n}\), nor that it is assembled from a finite, explicitly normalized family. RS.2 lists initial vectors as fixed coefficients without citing such a conclusion.

Finally, the orientation is conceptually repaired but notationally inconsistent: the plan calls \(\iota_e\) a “ROW entrance vector” and then writes \(\iota_e^T(I-K_e)^{-1}b_e\). One convention should be selected in the draft.

## CRITICAL OBSTRUCTIONS

1. **INIT, ENT-COUNT, and COMP use incompatible entrance granularity.**  
   \(I^{ent}_\gamma\) is entrance-shape-refined, while \(\iota_{e,\beta_0}\) is cell-aggregated. Consequently COMP-h does not presently pair the same entrance event on its mass and count sides. The defect propagates to RS.1 and (†-AGG), especially when different entrance shapes have different ledger exponents.

2. **The conditionality ledger remains semantically incomplete for Theorem U.**  
   The nine items are textually consistent and repair the three pass-6 omissions, but CTS-M(iv)-POLY is required for \(R_\sigma\in\mathbb Q(q)\), and TRACK-COUNT is required for SQ.0/SQ.1 and hence the finite-level squeeze. SQ.4’s inline conditional statement omits both, even though §7 separately recognizes TRACK-COUNT.

## CONCERNS

1. CTS-M(iii) does not explicitly conclude that the aggregated initial vector \(\iota_e\) has fixed \(\mathbb Q(q)\)-entries; RS.2 assumes it.

2. \(W_{\rm ent}(\gamma)\) is named as the shallow pool dimension, but its construction and compatibility with potentially different entrance exponents are not yet displayed.

3. HMC-probe’s comparison of a varied fixed height with \(T\cdot G\) products is under-specified and may mix fixed-height and resummed objects.

4. The internal [2b] proof order and STATE-probe-2’s reference to later RS.PRE should be made explicit to prevent governance-level cycle drift. The mathematical acceptance DAG itself is currently acyclic.

- **CRITICAL OBSTRUCTIONS: 2**
- **CONCERNS: 4**
- **Verdict: UNSOUND**

The verdict is not caused by XHD, HMC, E0, TRACK-COUNT, or WEIGHT-CHARGE remaining open. Those have honest conditional tags and substantially honest refuters. It is caused by the still-mismatched entrance objects at the CTS-M/COMP boundary and the incomplete capstone dependency ledger.

**Draft readiness beyond accepted [1] D4-R:** **[2a] SPECIES is cleared for drafting.** The XHD-free CTS partition/table work may be prepared afterward, but **[1v]-COND as a complete note is not cleared** until its INIT/ENT-COUNT/COMP entrance indexing is made coherent. No later complete note is cleared under the declared acceptance order.
