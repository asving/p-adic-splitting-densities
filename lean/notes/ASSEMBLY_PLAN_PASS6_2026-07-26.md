## Pass-6 structural review

REV 6 substantially improves the measured-process architecture. The source-mass normalization is now algebraically correct, ACT uses the correct block orientation, and HMC is honestly exposed as an open kernel. However, CTS-M creates a hidden DAG cycle, conflates height-retaining templates with height-resummed transitions, and does not justify the claimed initial count shadow. Those defects reach COMP, RS.1, and the acceptance ledger.

### A. Disposition of the four pass-5 criticals

| Pass-5 finding | REV 6 disposition | Classification |
|---|---|---|
| C1. Incorrect source normalization | “**K_e := Σ T·G with NO division**”; “**substochasticity = the per-representative partition identity Σ T·G + terminal = 1**” | **GENUINE.** Fix a representative \(x\in\alpha\). If the disjoint continuation events are indexed by \((m,o,\beta)\), with \(T_{m,o}^{\alpha,\beta}\) fresh value assignments and common per-assignment height/fresh mass \(G_{m,o}\), their conditional mass is \(T_{m,o}^{\alpha,\beta}G_{m,o}\). Summing gives \(K_e\). No source-cell factor appears: conditioning has already divided by the source-cylinder mass. Aggregating first over all \(x\in\alpha\) would multiply numerator and denominator by the same source mass and cancel. Thus there is no residual division and, given iv-PART/iv-MEAS, no double-counting. A remaining notation issue about \(G\) is listed below, but it does not revive the rejected division. |
| C2. Missing initial factor/distribution | “**Ĉ_γ := (initial-cell size)·C_γ**”; “**the INITIAL VECTOR ι_e displayed … from D4R.1 masses**” | **PARTIAL.** The measured repair is correct: if \(\nu_\beta\) is the possibly nonuniform entrance measure on cell \(\beta\), weighted representative independence makes the future path probability constant on \(\beta\), so \(\int_\beta P_\gamma(x)\,d\nu_\beta=\iota_\beta\prod(TG)\). But the count shadow does not follow. In general the full count is \(I_{e,\beta_0}(q)\prod T\), where \(I_{e,\beta_0}\) counts entrance-cascade realizations landing in that cell. Nothing in INIT proves \(I_{e,\beta_0}=|\beta_0|\). That equality is valid only when the template begins with one unrestricted copy of every concrete state in the cell. It need not hold for the stated “root/branch cascade enters the size-\(e\) block” event. |
| C3. Empty-cell semantics | “**NO-ENTRY**”; “**K_e(q₀) is … \(\begin{bmatrix}A&0\\ C&D\end{bmatrix}\)**”; “**NO-JUNK-POLE**” | **GENUINE.** With rows as sources and columns as targets, active-to-inactive vanishing is exactly the upper-right zero block. A row distribution supported on active states remains in \(A\); likewise the active part of the value equation is \(\beta_A=A\beta_A+\text{shallow}_A\), independent of \(C,D\). Formal inactive rows are not used as conditional laws. The construction therefore gives a genuine finite substochastic Markov kernel on the active states at each \(p\), conditional on STEP/PART/MEAS. |
| C4. Height resummation not Markov-compatible | “**CTS-M(v) HMC named as an OPEN KERNEL**”; “**Until HMC closes, \(K_e(p)^k\) is NOT a theorem about the process**”; HMC-probe compares exact two-step masses with one-step products | **PARTIAL.** The scope and conditionality are now honest, and the proposed exact two-step mismatch would genuinely refute the universal HMC statement. But the live template/COMP/RS.1 definitions still mix height-retaining and height-resummed objects, so downstream composition is not yet well typed. This is not merely that HMC remains open; the two sides of HMC are used inconsistently. |

### B. Disposition of the six pass-5 concerns

| Pass-5 concern | REV 6 disposition | Classification |
|---|---|---|
| K1. `Out(s)` might be field-dependent | “**Out(s) redefined SYNTACTIC … NO residue-field evaluation**” | **GENUINE.** This is the required fixed menu. Prime-specific impossibility is routed through zero entries and inactive cells rather than removal of labels. |
| K2. Wrong degree bound for cell sizes | “**table entries ≤ \(W_{\rm loc}(m)\), cell sizes ≤ \(W_{\rm state}(s)\)**” | **GENUINE.** The types and degree bounds are now correctly separated. |
| K3. The meet was schematic | “**the finite uniform partition is COMPUTED and LISTED**” | **GENUINE relocation, not closure.** The architecture now requires the actual boolean predicates, labels, and exceptional-characteristic conventions. The theorem remains to be drafted and proved, as expected. |
| K4. Measurability and weighted row equality missing | “**CTS-M(iv)-MEAS**” and “**CTS-M(iv)-REP (WEIGHTED … row representative independence)**” | **GENUINE.** These are precisely the missing measured statements. Weighted REP is strong enough even for a nonuniform entrance distribution within a cell. |
| K5. Bounded track count nonautomatic | “**TRACK-COUNT named OPEN structural lemma**”; “**candidate \(L(n)\le n^2\) is NOT accepted**” | **GENUINE relocation, not proof.** The danger is correctly isolated. The probe can refute a sealed candidate \(L(n)\), though it cannot establish the existential theorem. |
| K6. Substochasticity does not imply inversion | “**\(\rho\le1\) only**”; solve is “**GIVEN clauses (i)–(v) AND ESCAPE(E0)**” | **PARTIAL.** E0 conditionality is now correct. But the advertised six-input ledger omits other measured CTS-M clauses actually needed for the kernel interpretation—especially iv-PART and iv-MEAS—and the height-object mismatch means COMP is not yet a valid bridge to that kernel. |

## Normalization audit

The repaired one-step law has the right form. For a fixed active representative \(x\), let

\[
\mathcal E_x=\bigsqcup_{m,o,\beta,a,h}\mathcal E_{m,o,\beta,a,h}(x)
\]

be the disjoint fresh continuation partition, where \(a\) is a fresh value assignment and \(h\) a height choice. If, for fixed \((m,o,\beta)\),

\[
\#\{a\}=T_{m,o}^{\alpha,\beta}(q),\qquad
\sum_h \operatorname{mass}(a,h\mid x)=G_{m,o}(q),
\]

with the second expression independent of \(a\), then

\[
\Pr_x(m,o,\beta)
 =\sum_{a,h}\operatorname{mass}(a,h\mid x)
 =T_{m,o}^{\alpha,\beta}(q)G_{m,o}(q).
\]

Thus

\[
K_e(x;\beta)=\sum_{m,o}T_{m,o}^{\alpha,\beta}G_{m,o}.
\]

There is no division by \(|\alpha|\) or by its mass. Summing over the partition, terminal outcomes included, gives one. This is exactly the correct per-representative conditional law.

The caveat is that the plan must prove the Cartesian/common-weight statement used above. iv-PART asserts the resulting identity, but HMC as written only excludes dependence on earlier heights; it does not explicitly exclude dependence of the height domain or weight on the current fresh assignment or target cell. Moreover HMC says \(G\) may depend on the retained source state, while the notation is merely \(G_{m,o}\). Unless \(m,o\) already encode the source cell and every relevant target distinction, the honest notation is closer to \(G_{m,o}^{\alpha,\beta}\).

## Initial-vector audit

For masses, INIT plus weighted REP is sufficient. If \(\nu_{\beta_0}\) is the entrance measure in the first cell, then

\[
\mu(\gamma)
 =\int_{\beta_0}\Pr_x(\gamma)\,d\nu_{\beta_0}(x)
 =\iota_{e,\beta_0}\prod_i(T_iG_i).
\]

No uniform distribution within the first cell is required.

Counts are different. The corresponding formula is

\[
\#\gamma
 = I_{e,\beta_0}(q)\prod_iT_i(q),
\]

where \(I_{e,\beta_0}\) is the number of shallow entrance realizations, with any earlier multiplicities retained. The plan replaces \(I_{e,\beta_0}\) by \(|\beta_0|\) without a theorem identifying the entrance cascade with exactly one unrestricted copy of the concrete state cell.

This matters most for precisely the case named in the charge: templates whose first cell varies after a root/branch cascade. The vector \(\iota_e\) repairs their mass, but \(|\beta_0|\) does not automatically repair their finite-level count. Consequently the revised formula for `decided_σ(N)` in (†-AGG) is not yet justified.

## ACT audit

The block form is correct:

\[
K_e(q_0)=
\begin{bmatrix}
A&0\\
C&D
\end{bmatrix}
\]

with active states first. The zero upper-right block says an active representative cannot land in an empty target. Starting from \((\iota_A,0)\), every path remains in \(A\). Nothing requires a representative of an inactive source cell.

NO-JUNK-POLE is sufficient but stronger than what the realized process intrinsically needs. Active solutions are independent of \(D\). If \(D\) is singular at a wild prime, one could still have a well-defined active value after cancellation or after defining the rational solution through the active subsystem. REV 6 deliberately chooses the stronger full-matrix convention and makes \(\det(I-D_p)\ne0\) a proof duty. That is coherent, although it may create an avoidable failure mode.

## HMC and downstream use

HMC is honestly described as open, and its probe is a genuine falsifier: an exact two-step mass depending on \(h_1\) beyond the retained state, or differing from the product of sealed one-step factors, refutes HMC as universally stated.

Downstream tags are mostly honest:

- RS.PRE names HMC.
- RS.1 says height sums compose “ONLY through CTS-M(v) HMC.”
- SQ.4 and the capstone carry HMC.
- R9 adjudicates E0 against HMC before declaring a spectral wall.

The remaining defect is object-level. Section 1s defines a template \(\gamma\) with “**heights retained as \(\mathbb N\)-parameters**.” But CTS-M(iv)/(vi) uses \(G_{m,o}\), defined as the already-summed “**M4a-X-exact height sum**.” RS.1 then says:

> “group … by TEMPLATE \(\gamma\) and height point: … realized MASS is \(\iota_{\beta_0}\prod(T\cdot G)\)”

and afterwards:

> “Fubini the height sum over the EXACT semilinear domain.”

That sums height twice. At a fixed height point the factor must be a monomial or local weight \(g_{m,o}(h)\), not the resummed \(G_{m,o}\). Alternatively, if \(G\) has already summed the height coordinate, then \(\gamma\) must be a height-forgotten path cylinder, and RS.1 must not subsequently sum over height points.

Therefore COMP is not yet strong enough in its present typing for RESUM. A valid theorem needs two distinct composition identities:

\[
\mu(\gamma,\mathbf h)
 =\iota_{\beta_0}\prod_i T_i\,g_i(h_i),
\]

followed, under HMC, by

\[
\sum_{\mathbf h\in H(\gamma)}
 \mu(\gamma,\mathbf h)
 =\iota_{\beta_0}\prod_i T_i\,G_i.
\]

REV 6 currently states only the second while continuing to use \(\gamma\) as an object of the first kind.

## DAG and conditionality audit

The displayed note-level DAG is no longer the actual dependency DAG.

CTS-M(iv) defines \(G\) using “**the M4a-X-exact height sum**,” and CTS-M(v) is a theorem about M4a-X’s exact whole-template domains. But:

- CTS-M is housed in [1v] VALUE.
- [1v] is supposed to be accepted before [2b].
- M4a-X lives in [2b].
- [2b] consumes CTS-M(iv)-REP from [1v].

Hence there is a hidden cycle:

\[
[1v]\ \text{CTS-M/REP}\longrightarrow [2b]\ \text{M4a-X}
\longrightarrow [1v]\ \text{STEP/HMC/COMP}.
\]

Calling HMC open does not remove this dependency. Even iv-PART’s weighted row identity uses the exact \(G\), so [1v] cannot prove its displayed CTS-M theorem before [2b] supplies M4a-X. The DAG is therefore not acyclic as presently partitioned among notes.

The six-input ledger is textually repeated consistently at RS.PRE, SQ.4, §7, and R9:

1. M4a-X
2. D4R.0
3. CTS-M(iv)-REP
4. HMC
5. ACT
6. INIT

But it is semantically incomplete. Exact-kernel identification also needs:

- CTS-M(iv)-PART for total/substochastic rows;
- CTS-M(iv)-MEAS for identification with disjoint cylinder subevents;
- CTS-M(iv)-POLY for the fixed rational coefficient claim;
- the correctly typed fixed-height/resummed-height composition law.

These may eventually be discharged by accepting [1v], but the ledger selectively lists ACT and INIT—also clauses of [1v]—while omitting PART and MEAS. Under §7’s rule, that is not a coherent account of which still-open CTS-M duties the acceptance depends upon.

The open-kernel/refuter invariant also fails in one place. ESCAPE-probe observes only \(k=1,\dots,8\). A row appearing stable over eight steps does not refute \(A^k\mathbf1\to0\); arbitrarily delayed escape is compatible with E0. A genuine finite refuter would be, for example, an exact closed active communicating class with row sum one, detected from the symbolic active graph. The current probe can refute sealed finite-depth predictions but not E0 itself.

TRACK-probe and STALL-probe likewise refute particular proposed constants, not the existential TRACK-COUNT or WEIGHT-CHARGE statements. That is acceptable as exploration, but the roster should not claim that each is a refuter of the full open theorem.

## Fresh sweep

Two further points deserve attention.

First, “cylinder of \(\gamma\)” remains ambiguous. A value-forgotten path denotes a union of realized-history cylinders, not a single realized cylinder. COMP needs that union to be explicitly measurable and disjoint, with its treatment of height parameters stated. iv-MEAS supplies the one-step ingredients but does not by itself repair the present fixed-height/resummed-height ambiguity.

Second, the displayed recursion

\[
\beta_e=K_e\beta_e+\mathrm{SHALLOW}_e
\]

does not show exactly where \(\iota_e\) acts. An entry distribution normally produces an expression of the form

\[
\iota_e^{\,T}(I-K_e)^{-1}b_e
\]

for an exit/reward vector \(b_e\). Saying that “SHALLOW carries \(\iota_e\)” may encode this, but RS.PRE/COMP should state the orientation and multiplication explicitly. Otherwise the correct initial-vector theorem can still be lost when transferred into the block equations.

## Final assessment

### CRITICAL OBSTRUCTIONS

1. **CTS-M introduces a hidden [1v] ↔ [2b] cycle.** STEP/HMC/COMP require M4a-X, while M4a-X’s note consumes CTS-M/REP.

2. **COMP and RS.1 double-type the height variables.** Templates retain height points, but \(G\) is already the exact height sum; RS.1 then sums those height points again. The current COMP theorem is not strong or well typed enough for RESUM.

3. **The initial count shadow is unjustified.** INIT genuinely supplies the entrance mass \(\iota_{e,\beta}\), but the corresponding entrance count is not generally the bare cell size \(|\beta|\). This leaves VAL CHAIN’s full-count claim and (†-AGG)’s `decided_σ(N)` expansion unsupported for block-entry templates.

4. **The conditionality ledger omits load-bearing measured clauses.** iv-PART and iv-MEAS are required for the active Markov interpretation and E0 reduction but are absent from the advertised six-input ledger; the fixed-height/resummed-height composition duty is absent as well.

### CONCERNS

1. \(G_{m,o}\) is under-indexed relative to HMC’s own statement that the height mass may depend on the retained source state, and possibly on target-cell data.

2. ESCAPE-probe’s finite \(k\le8\) observation cannot refute the asymptotic E0 statement. A symbolic closed-class test would be a genuine refuter.

3. TRACK-probe and STALL-probe refute sealed candidate constants, not the existential open kernels themselves; the roster overstates their logical scope.

4. NO-JUNK-POLE is coherent but stronger than necessary because the active solution is independent of the junk block. It may reject an otherwise valid active-chain rational specialization.

- **CRITICAL OBSTRUCTIONS: 4**
- **CONCERNS: 4**
- **Verdict: UNSOUND**

Open kernels themselves are not the reason for this verdict. The verdict is UNSOUND because the current architecture has a hidden cycle and mismatched measured objects at the COMP/RESUM interface.

**Draft readiness:** no additional note beyond **[1] D4-R** is cleared for drafting under the declared acceptance order. In particular, [1v] cannot be drafted as the single self-contained CTS-M theorem claimed here until its circular dependence on [2b]’s M4a-X is reorganized.
