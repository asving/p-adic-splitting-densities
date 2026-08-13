# EFF-T3 — CANONICAL EFFECTIVE SPECIFICATION

## 1. Header

**Source note:** `lean/notes/openmath/T3_COCYCLE_TELESCOPE_2026-08-12.md`

**HEAD blob hash:** `34cc4d40dceda561b56e1deb8f7167c7e5500c8f`

**Compilation context:** `docs/BLUEPRINT_PHASE_DESIGN_2026-08-13.md`, Revision 2, Stage 0a.

### Governing effective-text record

The acceptance record contains no sentence literally defining “the effective text.” Its governing chronology says:

> “Arc: composed 2026-08-10 (RCT sol-arm) → revised vs the certified seam (comp1 T3R) → pass 1 post-r1... T3P1 0C+1G (the FRAME-C comparison-port arithmetic) → r1 applied → T3P2 CLEAN (fresh route) → T3P3 CLEAN (absorption-derivation route). Two consecutive clean fresh-context hostile passes: **LEMMA COCYCLE-TELESCOPE is ACCEPTED at 2/2**”

The post-acceptance record then gives the operative scope definition:

> “The unit's scope of record is therefore TWO absorptions + one documented non-instance; GENTOW-6.4 retains its own certified proof (the blueprint's third target was honestly narrowed at revision).”

This second quotation governs the accepted consumer-facing scope because it is later, explicitly post-acceptance, and uses the dispositive phrase “scope of record.”

### Resolution rules applied

1. The 2026-08-12 base text at lines 1–1217 supersedes the composed `T3_COCYCLE_TELESCOPE_2026-08-10.md`.
2. r1 R1-G1 replaces base §8.2 in full. Base lines 940–1000 are historical; r1 lines 1229–1337 are effective.
3. No other base statement is textually replaced by r1.
4. The acceptance record makes the base-plus-r1 mathematical text accepted at 2/2.
5. The acceptance paragraph’s list “three absorptions (GENTOW2-B″, HETOW-4, GENTOW-6.4)” is superseded for consumer scope by the later consumption-check record: GENTOW2-B″ and HETOW-4 pass; GENTOW-6.4 is not absorbed.
6. The post-acceptance narrowing changes the supply/absorption record. It does not expressly delete §5 or declare the displayed GENTOW5 mathematics false. Consequently §5 remains inventoried, but it is not listed as an accepted T3 supply to an absorbed consumer.
7. GENTOW6_BOXES E11 riders remain regression records and do not become carrier hypotheses.
8. The pre-acceptance status at base line 6 and the base “three absorptions” summaries are historical wherever they conflict with the final records.

---

## 2. Statement inventory

### EFF.T3.01  [convention]

**CANONICAL STATEMENT:**

> “Fix a tower level \(i\). Write
> \[
> N(k):=\widehat n_i(k),
> \qquad
> N(0)=1.
> \]”

The abstract vocabulary “height,” “normalized exact-height section,” `res`, and its ambient residue field is imported from:

XREF: `lean/notes/openmath/T1_GAUGE_COCYCLE_2026-08-12.md:NORMALIZED-NORMALIZER-SECTION-SETUP`

Ordinary field, product, sum, inverse, polynomial, degree, factor, root, and separability notation has its usual algebraic meaning in the ambient fields named by the imported or specialized source units.

**CONDITIONALITY:** “Fix a tower level \(i\).”

**RESOLUTION TRACE:** base §1, lines 43–51; no r-round touched it.

**TEETH:**

- §8.1(1) — guards \(N(0)=1\).
- §8.1(3) — rejects an independent or conflicting T1 normalizer-frame definition.

---

### EFF.T3.02  [definition]

**CANONICAL STATEMENT:**

> “For all defined heights,
> \[
> \tau_N(a,b):=\frac{N(a)N(b)}{N(a+b)}
> \]
> has height zero and satisfies
> \[
> \tau_N(0,a)=\tau_N(a,0)=1,
> \qquad
> \tau_N(a,b)\tau_N(a+b,c)
> =
> \tau_N(b,c)\tau_N(a,b+c).
> \tag{T1-C2}
> \]”

> “At level \(1\), its residue is governed by T1’s wrap formula. T3 does not repeat that computation.”

XREF: `lean/notes/openmath/T1_GAUGE_COCYCLE_2026-08-12.md:T1-C2`

XREF: `lean/notes/openmath/T1_GAUGE_COCYCLE_2026-08-12.md:T1-WRAP-FORMULA`

**CONDITIONALITY:** “For all defined heights.”

**RESOLUTION TRACE:** base §1.1, lines 55–76; no r-round touched it.

**TEETH:**

- §8.1(3) — rejects a competing proof or redefinition of the wrap or cocycle law.

---

### EFF.T3.03  [definition]

**CANONICAL STATEMENT:**

> “Fix a ladder step \(q=u_{i+1}\). For \(s\ge0\), T1 defines
> \[
> \vartheta_N(s;q)
> :=
> \operatorname{res}\!\left(
> \frac{N(q)^s}{N(sq)}
> \right)
> \]
> and proves
> \[
> \vartheta_N(0;q)=\vartheta_N(1;q)=1,
> \qquad
> \vartheta_N(s+1;q)
> =
> \vartheta_N(s;q)\,
> \operatorname{res}\bigl(\tau_N(sq,q)\bigr).
> \tag{T1-TEL}
> \]”

XREF: `lean/notes/openmath/T1_GAUGE_COCYCLE_2026-08-12.md:T1-TEL`

**CONDITIONALITY:** “Fix a ladder step \(q=u_{i+1}\). For \(s\ge0\).”

**RESOLUTION TRACE:** base §1.2, lines 80–102; no r-round touched it.

**TEETH:**

- §8.1(1) — guards the endpoints \(\vartheta_N(0;q)=\vartheta_N(1;q)=1\).
- §8.1(2) — guards the recurrence and inverse orientation.
- §8.1(3) — rejects a competing telescope recursion.

---

### EFF.T3.04  [definition]

**CANONICAL STATEMENT:**

> “The B-law orientation is the inverse
> \[
> \Theta_N(s;q)
> :=
> \vartheta_N(s;q)^{-1}
> =
> \operatorname{res}\!\left(
> \frac{N(sq)}{N(q)^s}
> \right).
> \tag{T1-THETA}
> \]”

> “For the slot \(t<f_{i+1}\), put
> \[
> s=f_{i+1}-t,
> \qquad
> \Theta_i(t):=\Theta_N(s;u_{i+1}).
> \]”

XREF: `lean/notes/openmath/T1_GAUGE_COCYCLE_2026-08-12.md:T1-THETA`

**CONDITIONALITY:** “For the slot \(t<f_{i+1}\).”

**RESOLUTION TRACE:** base §1.2, lines 104–125; no r-round touched it.

**TEETH:**

- §8.1(2) — guards \(\Theta_N=\vartheta_N^{-1}\).
- §8.4(4), inverse-orientation mutant — rejects replacement of \(\Theta_N\) by \(\vartheta_N\).

---

### EFF.T3.05  [convention]

**CANONICAL STATEMENT:**

> “If a height-\(sq\) coefficient has coherent digit \(\Gamma\) against \(N(sq)\) and multiplicative coefficient \(c^{\rm mult}\) against \(N(q)^s\), T1 supplies
> \[
> \Gamma
> =
> c^{\rm mult}\vartheta_N(s;q),
> \qquad
> c^{\rm mult}
> =
> \Gamma\Theta_N(s;q).
> \tag{T1-DICT}
> \]”

> “T1 also records the formal B-law once the relevant sitewise residual-read obligation has been discharged. T3 does **not** cite that conditional conclusion as a premise for \([{\rm GENTOW5\!-\!W}(i)]\). Instead, the boundary-read port below discharges the obligation from the source’s primitive read package.”

XREF: `lean/notes/openmath/T1_GAUGE_COCYCLE_2026-08-12.md:T1-DICT`

**CONDITIONALITY:** “If a height-\(sq\) coefficient has coherent digit \(\Gamma\) against \(N(sq)\) and multiplicative coefficient \(c^{\rm mult}\) against \(N(q)^s\).”

**RESOLUTION TRACE:** base §1.3, lines 129–146; no r-round touched it.

**TEETH:**

- §8.1(3) — rejects a conflicting corrected-key dictionary.
- §8.1(4) — guards against importing T1’s conditional B-law.
- §8.4(3), endpoint-as-input mutant — requires independent read paths.

---

### EFF.T3.06  [hypothesis]

**CANONICAL STATEMENT:**

> “Fix \(s\ge1\), put \(q=u_{i+1}\), and let
> \[
> G:=N(q)^s.
> \]
> Assume the source supplies a \(\Phi_i\)-adic expansion
> \[
> G=\sum_{j\ge0}Q_j\Phi_i^j
> \]
> and a canonical residual read at the slot grade \(\beta_s\). Let \(\operatorname{ct}\) denote constant-coefficient extraction in its residual variable.”

The source-specific meanings of \(\Phi_i,\beta_s,Q_j,R_{\beta_s}\), and `digit` are supplied by the specialization’s source XREF.

**CONDITIONALITY:** “Fix \(s\ge1\)” and “Assume the source supplies a \(\Phi_i\)-adic expansion … and a canonical residual read at the slot grade \(\beta_s\).”

**RESOLUTION TRACE:** base §2.1, lines 154–167; no r-round touched it.

**TEETH:**

- §8.1(4) — the setup may not conceal the conditional B-law.
- §8.4(3), endpoint-as-input mutant — the endpoint identity may not be installed as setup data.

---

### EFF.T3.07  [hypothesis]

**CANONICAL STATEMENT:**

> “**Peel.** The ladder read of \(G=N(q)^s\) satisfies
> \[
> \operatorname{ct}R_{\beta_s}(G)=w_i^s,
> \qquad
> w_i
> =
> R_{i+1,\bar\kappa_i}\bigl(N(q)\bigr)
> \in K_i^\times.
> \tag{BR1}
> \]”

**CONDITIONALITY:** BR1 verbatim above.

**RESOLUTION TRACE:** base §2.1(1), lines 170–180; no r-round touched it.

**TEETH:**

- effective §8.2 boundary frame — guards the independent \(w^s\) path.
- §8.4(2), theta-free mutant — requires the nontrivial \(\Theta\) factor to survive comparison with the digit path.
- §8.4(3), endpoint-as-input mutant — forces inconsistency when the endpoint is falsified.

---

### EFF.T3.08  [hypothesis]

**CANONICAL STATEMENT:**

> “**Expansion.**
> \[
> R_{\beta_s}(G)
> =
> \sum_{j\ge0}R_{\beta_s}(Q_j\Phi_i^j).
> \tag{BR2}
> \]”

**CONDITIONALITY:** BR2 verbatim above.

**RESOLUTION TRACE:** base §2.1(2), lines 182–189; no r-round touched it.

**TEETH:**

- §8.4(3), endpoint-as-input mutant — guards the independent expansion route.

---

### EFF.T3.09  [hypothesis]

**CANONICAL STATEMENT:**

> “**Positive-degree elimination.** For every \(j\ge1\),
> \[
> \operatorname{ct}R_{\beta_s}(Q_j\Phi_i^j)=0.
> \tag{BR3}
> \]”

**CONDITIONALITY:** “For every \(j\ge1\).”

**RESOLUTION TRACE:** base §2.1(3), lines 191–196; no r-round touched it.

**TEETH:**

- §8.4(3), endpoint-as-input mutant — guards the reduction to the independently read constant coefficient.

---

### EFF.T3.10  [hypothesis]

**CANONICAL STATEMENT:**

> “**Exact constant digit.** The coefficient \(Q_0\) has exact grade \(\beta_s\), and the per-grade read factor \(U_i(\beta_s)\) satisfies
> \[
> \operatorname{ct}R_{\beta_s}(Q_0)
> =
> U_i(\beta_s)\operatorname{digit}_i(Q_0).
> \tag{BR4}
> \]”

**CONDITIONALITY:** “The coefficient \(Q_0\) has exact grade \(\beta_s\).”

**RESOLUTION TRACE:** base §2.1(4), lines 198–205; no r-round touched it.

**TEETH:**

- effective §8.2 boundary frame — \(U(s)\) must be independently supplied.
- §8.4(3), endpoint-as-input mutant — guards the pre-cancellation equality.

---

### EFF.T3.11  [hypothesis]

**CANONICAL STATEMENT:**

> “**Evaluation digit.** Evaluation at the \(\Phi_i\)-root gives
> \[
> \operatorname{digit}_i(Q_0)
> =
> \operatorname{res}\!\left(
> \frac{N(q)^s}{N(sq)}
> \right)
> =
> \vartheta_N(s;q).
> \tag{BR5}
> \]”

> “These are source-local residual-read hypotheses. Neither the B-law nor a one-\(w_i\) power law is included among them.”

**CONDITIONALITY:** BR5 and the quoted exclusion above.

**RESOLUTION TRACE:** base §2.1(5), lines 207–220; no r-round touched it.

**TEETH:**

- §8.1(4) — rejects the conditional B-law as an input.
- §8.4(2), theta-free mutant — guards the \(\vartheta/\Theta\) factor.
- §8.4(3), endpoint-as-input mutant — guards independence of the digit route.
- §8.4(4), inverse-orientation mutant — guards the orientation.

---

### EFF.T3.12  [definition]

**CANONICAL STATEMENT:**

> “Let \(N\) and \(\widehat N\) be two normalized exact-height sections on the same set of heights. Their T1 cocycles are
> \[
> \tau_N(a,b)=\frac{N(a)N(b)}{N(a+b)},
> \qquad
> \tau_{\widehat N}(a,b)
> =
> \frac{\widehat N(a)\widehat N(b)}{\widehat N(a+b)}.
> \]
> Define their pointwise residual ratio by
> \[
> \chi(k)
> :=
> \operatorname{res}\!\left(
> \frac{\widehat N(k)}{N(k)}
> \right)
> \in K^\times.
> \]”

> “The symbol \(\chi\) is used here to avoid collision with T1’s cocycle symbol \(\tau_N(a,b)\). In the HETOW-4 specialization, \(\chi\) is renamed to the source’s \(\tau\).”

**CONDITIONALITY:** “Let \(N\) and \(\widehat N\) be two normalized exact-height sections on the same set of heights.”

**RESOLUTION TRACE:** base §2.2, lines 224–248; no r-round touched it.

**TEETH:**

- effective §8.2 comparison frame — supplies a visibly non-character \(\chi\).
- §8.4(1), character mutant — rejects imposing \(\chi(a+b)=\chi(a)\chi(b)\).

---

### EFF.T3.13  [definition]

**CANONICAL STATEMENT:**

> “Fix
> \[
> H_t=H_0-tq,
> \qquad
> 0\le t\le D,
> \]
> and let \(A_t\) have height \(H_t\). Define
> \[
> \rho_t
> =
> \operatorname{res}\!\left(
> \frac{A_tN(q)^t}{N(H_0)}
> \right),
> \qquad
> \widehat\rho_t
> =
> \operatorname{res}\!\left(
> \frac{A_t\widehat N(q)^t}{\widehat N(H_0)}
> \right).
> \]
> Set
> \[
> R(Z)=\sum_{t=0}^{D}\rho_tZ^t,
> \qquad
> \widehat R(Z)=\sum_{t=0}^{D}\widehat\rho_tZ^t,
> \qquad
> \delta=\chi(q).
> \]
> All displayed residual quotients have height zero.”

**CONDITIONALITY:** “\(0\le t\le D\)” and “let \(A_t\) have height \(H_t\).”

**RESOLUTION TRACE:** base §2.2, lines 250–284; no r-round touched it.

**TEETH:**

- effective §8.2 comparison frame — fixes \(q_{\rm CMP}=2,H_0=6,D=3\) and verifies the assembled coefficients.
- §8.3(2), HETOW-4 regression — guards the X/Z/S assembled-coefficient specialization.

---

### EFF.T3.14  [lemma]

**CANONICAL STATEMENT:**

> “**Boundary-read telescope.** Under (BR1)–(BR5),
> \[
> U_i(\beta_s)
> =
> \Theta_N(s;q)\,w_i^s.
> \tag{T3-BR}
> \]”

> “The endpoint equation was not supplied: its two sides arose independently from the peeled read of \(N(q)^s\) and the coherent digit of the surviving constant coefficient.”

**CONDITIONALITY:** “Under (BR1)–(BR5).”

**RESOLUTION TRACE:** base §2.3(1), lines 290–301; proof fence at lines 403–404; no r-round touched it.

**TEETH:**

- effective §8.2 boundary frame — verifies \(w^s=U(s)\vartheta_s\) and \(U(s)=\Theta_sw^s\) without defining \(U\) from the endpoint.
- §8.3(1), GENTOW2-B″ regression — guards the local specialization.
- §8.3(3), GENTOW5-W regression — guards both slots of the level-3 specialization.
- §8.4(2), theta-free mutant.
- §8.4(3), endpoint-as-input mutant.
- §8.4(4), inverse-orientation mutant.

---

### EFF.T3.15  [lemma]

**CANONICAL STATEMENT:**

> “**Descending bracket telescope.** For \(H_t=H_0-tq\),
> \[
> \prod_{r=0}^{t-1}
> \tau_N(H_{r+1},q)
> =
> \frac{N(H_t)N(q)^t}{N(H_0)}.
> \tag{T3-BKT}
> \]”

**CONDITIONALITY:** “For \(H_t=H_0-tq\),” with the normalized cocycle of EFF.T3.02.

**RESOLUTION TRACE:** base §2.3(2), lines 303–313; no r-round touched it.

**TEETH:**

- §8.3(2), HETOW-4 regression — guards the coefficient telescope.
- §8.1(3) — ensures this remains an iteration of the imported cocycle rather than a competing cocycle proof.

---

### EFF.T3.16  [lemma]

**CANONICAL STATEMENT:**

> “**Section-ratio coboundary.**
> \[
> \frac{\chi(a)\chi(b)}{\chi(a+b)}
> =
> \operatorname{res}\!\left(
> \tau_{\widehat N}(a,b)\tau_N(a,b)^{-1}
> \right).
> \tag{T3-COB}
> \]”

> “In particular, no character law for \(\chi\) is assumed. It is a character exactly when the two imported cocycles have equal residue.”

**CONDITIONALITY:** The two normalized exact-height sections and their imported cocycles from EFF.T3.12; no character hypothesis.

**RESOLUTION TRACE:** base §2.3(3), lines 315–328; no r-round touched it.

**TEETH:**

- effective §8.2 comparison frame — verifies \(\chi(1)^2\ne\chi(2)\).
- §8.3(2), HETOW-4 non-character regression.
- §8.4(1), character mutant.

---

### EFF.T3.17  [lemma]

**CANONICAL STATEMENT:**

> “**Assembled comparison.**
> \[
> \rho_t
> =
> \widehat\rho_t\,
> \chi(H_0)\delta^{-t},
> \qquad
> R(Z)
> =
> \chi(H_0)\widehat R(Z/\delta).
> \tag{T3-CMP}
> \]”

**CONDITIONALITY:** The definitions and height-zero residual quotients of EFF.T3.12–13.

**RESOLUTION TRACE:** base §2.3(4), lines 330–344; no r-round touched it.

**TEETH:**

- effective §8.2 comparison frame — verifies
  \(\rho_t=3\widehat\rho_t2^{-t}\) and
  \(R(Z)=3\widehat R(Z/2)\).
- §8.3(2), HETOW-4 regression — guards the X/Z/S comparison and rescaling.
- §8.4(1), character mutant — keeps the comparison independent of a false character law.

---

### EFF.T3.18  [lemma]

**CANONICAL STATEMENT:**

> “**Polynomial routing.** Multiplication by the nonzero scalar \(\chi(H_0)\) and substitution \(Z\mapsto Z/\delta\) preserve separability and the multiset of irreducible-factor degrees and multiplicities. If \(\widehat r(Z)\) is monic of degree \(m\), its corresponding monic factor is
> \[
> r(Z)
> =
> \delta^m\widehat r(Z/\delta),
> \qquad
> \widehat s\longmapsto\delta\widehat s
> \tag{T3-ROUTE}
> \]
> on roots. Rationality over any field containing \(K\) is preserved.”

**CONDITIONALITY:** “Multiplication by the nonzero scalar \(\chi(H_0)\)” and \(\delta\in K^\times\); “If \(\widehat r(Z)\) is monic of degree \(m\).”

**RESOLUTION TRACE:** base §2.3(5), lines 346–359; no r-round touched it.

**TEETH:**

- §8.3(2), HETOW-4 regression — guards polynomial rescaling and factor/root direction.
- Effective §8.2 comparison frame — keeps \(Z\mapsto Z/2\) live.
- Honesty-ledger item 10 — limits the conclusion to factor patterns, not literal coefficients.

---

### EFF.T3.19  [instance-record]

**CANONICAL STATEMENT:** [ASSEMBLED — verbatim components from base lines 460–525]

> “Fix \(t<f_3\) and put
> \[
> s=f_3-t,\qquad q=u_3,\qquad
> N(q)=\widehat n_2(u_3),\qquad
> N(sq)=\widehat n_2(su_3).
> \]”

> “The source’s B-law-oriented unit is
> \[
> \vartheta_{\rm G2}(t)
> :=
> \operatorname{res}\!\left(
> \frac{\widehat n_2(su_3)}
> {\widehat n_2(u_3)^s}
> \right)
> =
> \Theta_N(s;u_3).
> \]”

> “Set
> \[
> w=R_{3,\bar k}\bigl(\widehat n_2(u_3)\bigr),
> \qquad
> U_2(\beta_t)=u(\beta_t).
> \]”

> “Therefore (T3-BR) gives the closed absorbed display
> \[
> \begin{gathered}
> s=f_3-t,\\
> u(\beta_t)
> =
> \vartheta_{\rm G2}(t)\,
> w^{\,f_3-t},\\
> y^{f_3}
> -
> \sum_{t<f_3}
> \vartheta_{\rm G2}(t)
> w^{\,f_3-t}c_ty^t
> =
> w^{f_3}P(y/w),\\
> P(y)
> =
> y^{f_3}
> -
> \sum_{t<f_3}
> \vartheta_{\rm G2}(t)c_ty^t.
> \end{gathered}
> \tag{ABS-G2}
> \]”

> “This absorbs GENTOW2-B\(''\) and its factor-pattern invariance. No value of \(w\) is required.”

XREF: `lean/notes/openmath/GENTOW2_PROOF_2026-08-09.md:S5.1-LEMMA-GENTOW2-B′`

XREF: `lean/notes/openmath/GENTOW2_PROOF_2026-08-09.md:S5.2-LEMMA-GENTOW2-B″`

**CONDITIONALITY:**

> “The source inputs are its slot geometry, exact ladder heights, residual peel and additivity, positive-degree elimination, exact constant-digit law, root evaluation, and value-zero gamma-letter calculation. Neither the displayed B-law nor a one-\(w\) family is an input.”

The ledger classification is:

> “Unconditional at the landed \(i=2\) rung.”

**RESOLUTION TRACE:** base §3; no r-round touched the mathematics; post-acceptance consumption record confirms “GENTOW2-B″ PASS.”

**TEETH:**

- §8.3(1), GENTOW2-B″ regression — LP/LD quotient, inverse orientation, and both residual polynomials.
- §8.4(2), theta-free mutant.
- §8.4(3), endpoint-as-input mutant.
- §8.4(4), inverse-orientation mutant.

---

### EFF.T3.20  [instance-record]

**CANONICAL STATEMENT:** [ASSEMBLED — verbatim components from base lines 531–616]

> “Set
> \[
> N(k)=n_2(k),\qquad
> \widehat N(k)=\widehat n_2(k),\qquad
> \tau_{\rm H}(k)
> =
> \operatorname{res}\!\left(
> \frac{\widehat n_2(k)}{n_2(k)}
> \right).
> \]
> Thus \(\tau_{\rm H}\) is T3’s \(\chi\), not T1’s two-variable cocycle. Put
> \[
> q=u_3,\qquad
> \delta=\tau_{\rm H}(u_3),\qquad
> H_t=H_0-tu_3.
> \]”

> “The HETOW assembled coefficients instantiate (T3-CMP), giving the closed absorption
> \[
> \begin{gathered}
> \rho_t
> =
> \widehat\rho_t\,
> \tau_{\rm H}(H_0)\delta^{-t},\\
> R_{\lambda_2}(Z)
> =
> \tau_{\rm H}(H_0)\,
> \widehat R_{\lambda_2}(Z/\delta),\\
> \widehat r_2(Z)
> \longmapsto
> r_2(Z)
> =
> \delta^{\deg\widehat r_2}
> \widehat r_2(Z/\delta),\\
> \widehat s_2
> \longmapsto
> \delta\widehat s_2.
> \end{gathered}
> \tag{ABS-HE4}
> \]”

> “The section-ratio coboundary is
> \[
> \frac{\tau_{\rm H}(k)\tau_{\rm H}(k')}
> {\tau_{\rm H}(k+k')}
> =
> \operatorname{res}\!\left(
> \tau_{\widehat n_2}(k,k')
> \tau_{n_2}(k,k')^{-1}
> \right).
> \tag{HE4-COB}
> \]”

> “No character law for \(\tau_{\rm H}\) is asserted.”

XREF: `lean/notes/openmath/HETOW_RECON_2026-08-09.md:LEMMA-HETOW-4(a)`

XREF: `lean/notes/openmath/HETOW_RECON_2026-08-09.md:LEMMA-HETOW-4(b)`

XREF: `lean/notes/openmath/HETOW_RECON_2026-08-09.md:LEMMA-HETOW-4(c)`

**CONDITIONALITY:**

> “Comparison/routing block unconditional on its stated source hypotheses.”

The exact boundary is:

- Clause (a), \(\tau_{\rm H}(k)=\eta^{-Q(m(k))}\): source-specific ladder arithmetic, not supplied by T3.
- Clause (b), coboundary-comparison shape: supplied by T3-COB; the explicit two-floor exponent additionally uses HETOW floor arithmetic.
- Clause (c): fully supplied by T3-BKT and T3-CMP.
- Clause (d), separability/factor/root routing: fully supplied by T3-ROUTE.
- Common polynomial lift and later iterate independence remain on HETOW-4’s lift and finite-chain inputs.

**RESOLUTION TRACE:** base §4; no r-round touched it; post-acceptance consumption record confirms “HETOW-4 PASS.”

**TEETH:**

- §8.3(2), HETOW-4 regression — X/Z/S comparison, non-character, rescaling, and routing.
- §8.4(1), character mutant.
- Effective §8.2 comparison frame — guards the inverse power, scalar, and root direction.

---

### EFF.T3.21  [lemma]

**CANONICAL STATEMENT:** [ASSEMBLED — verbatim components from base lines 622–672]

> “Fix \(i\ge3\), \(t<f_{i+1}\), and put
> \[
> s=f_{i+1}-t,\qquad
> q=u_{i+1},\qquad
> N(q)=\widehat n_i(u_{i+1}),\qquad
> N(sq)=\widehat n_i(su_{i+1}).
> \]”

> “Define
> \[
> \theta_i(t)
> =
> \operatorname{res}\!\left(
> \frac{\widehat n_i(su_{i+1})}
> {\widehat n_i(u_{i+1})^s}
> \right)
> =
> \Theta_N(s;u_{i+1}),
> \]
> and
> \[
> w_i
> =
> R_{i+1,\bar k_i}
> \bigl(\widehat n_i(u_{i+1})\bigr).
> \]”

> “Hence:
> \[
> [{\rm GENTOW5\!-\!W}(i)]
> \qquad
> u_i(\beta_t)
> =
> \theta_i(t)\,
> w_i^{\,f_{i+1}-t},
> \qquad
> i\ge3,\quad t<f_{i+1}.
> \tag{ABS-G5W}
> \]”

> “At \(i=2\), this is the landed GENTOW2-B\(''\) instance in §3. The \(i=1\) residual remains GENTOW5 S11.3’s fixed \(z_1\)-letter-power statement; T3 does not identify that unit with a displayed \(w_1\).”

XREF: `lean/notes/openmath/GENTOW5_WI_2026-08-10.md:S1–S2-[GENTOW5-W(i)]`

**CONDITIONALITY:**

> “The certified level-\(i\) expansion, peel, positive-degree elimination, exact-grade law, and root-evaluation package instantiate (BR1)–(BR5).”

The post-acceptance record does not list this unit among T3’s two consumer-facing absorptions. Its mathematical text survives, but its supply status is unresolved as recorded in OPEN-CALL 3.

**RESOLUTION TRACE:** base §5 and §7; no r-round touched it; acceptance paragraph omits it from its named “three”; post-acceptance scope lists only two passing absorptions and does not name it.

**TEETH:**

- §8.3(3), GENTOW5-W regression — level-3 LW3 boundary instance and both slots.
- §8.1(4) — rejects circular use of T1’s conditional B-law.
- §8.4(2), theta-free mutant.
- §8.4(3), endpoint-as-input mutant.
- §8.4(4), inverse-orientation mutant.

---

### EFF.T3.22  [definition]

**CANONICAL STATEMENT:**

> “For \(n\ge3\), write
> \[
> \mathcal W_{\le n}
> :=
> \bigwedge_{3\le q\le n}
> [{\rm GENTOW5\!-\!W}(q)].
> \]”

**CONDITIONALITY:** “For \(n\ge3\).”

**RESOLUTION TRACE:** base §5.1, lines 676–683; no r-round touched it.

**TEETH:**

- §8.3(4), GENTOW5 conditionality lint.
- §8.4(5), GENTOW5 conditionality mutant.

---

### EFF.T3.23  [hypothesis]

**CANONICAL STATEMENT:** [ASSEMBLED — verbatim components from base lines 685–724]

> “The complete consumer chain remains explicitly conditional:
> \[
> \mathcal W_{\le n}
> \Longrightarrow
> (a)@n
> \Longrightarrow
> {\rm Corollary\ 6.4}
> \Longrightarrow
> (b)@n
> \Longrightarrow
> {\rm S11.1.1/S11.1.3}
> \Longrightarrow
> (c)@n
> \Longrightarrow
> (e)@n
> \Longrightarrow
> \text{the next automatic floor}.
> \tag{G5-COND}
> \]”

> “Locally, the new residual input at rung \(n\) is \([{\rm GENTOW5\!-\!W}(n)]\); the earlier members of \(\mathcal W_{\le n}\) are ambient induction hypotheses.”

> “In particular, at \(n\ge3\), all of the following ride \(\mathcal W_{\le n}\):
>
> - the pinned-key residual \(\psi_{n+1}^{(w_n)}\);
> - key-polynomial membership, primality/irreducibility, admissibility, and non-equivalence;
> - every lower-level one-sidedness assertion in clause (b);
> - exact intermediate values and repo-side residue classes;
> - \(P_{n+1}\)-membership;
> - S11.1.1 and S11.1.3;
> - clause (c), including sufficiency, ascent, fibration, pins, and field floor;
> - clause (e) and the automatic derivation of the next floor.”

> “‘\(w\)-blind’ means invariant after the single-\(w_i\) geometric law has been proved. It does not construct that law from an arbitrary fixed per-grade family.”

XREF: `lean/notes/openmath/GENTOW5_PROOF_2026-08-09.md:S12.1-[R-i2]`

**CONDITIONALITY:** \(\mathcal W_{\le n}\), verbatim as displayed and propagated above.

**RESOLUTION TRACE:** base §5.1; no T3 r-round touched it; it folds GENTOW5 S12.1 R-i2.

**TEETH:**

- §8.3(4), conditionality lint — rejects every unqualified \(n\ge3\) use of clauses (a), (b), (c), or (e), or the automatic-floor consequence.
- §8.4(5), conditionality mutant — erasing \(\mathcal W_{\le n}\) must fail.

---

### EFF.T3.24  [convention]

**CANONICAL STATEMENT:** [ASSEMBLED — verbatim components from base lines 728–764]

> “Under \(\mathcal W_{\le n}\), the clause-(b) residual display is
> \[
> R_{j-1}(\Phi_{n+1})
> =
> \left(
> \psi_j^{(\omega_{j-1})}
> \right)^{
> l_{j+1}\cdots l_{n+1}
> },
> \qquad
> 2\le j\le n+1.
> \tag{G5-TWIST}
> \]”

> “where
> \[
> \omega_1
> =
> \text{the fixed S11.3 \(z_1\)-letter-power unit},
> \qquad
> \omega_2=w_2,
> \qquad
> \omega_r=w_r\quad(r\ge3).
> \]”

> “Thus:
>
> - \(\psi_2\) carries \(\omega_1\);
> - \(\psi_3\) carries \(w_2\);
> - \(\psi_j\) carries \(w_{j-1}\) for \(j\ge4\);
> - the top term \(\psi_{n+1}\) carries \(w_n\), which is available under \(\mathcal W_{\le n}\).”

> “The outer \(\psi_1\) leg remains separately governed by its accepted source statement. No display in T3 uses the superseded index \(\psi_j^{(\omega_j)}\).”

XREF: `lean/notes/openmath/GENTOW5_PROOF_2026-08-09.md:S11.3-FIXED-z₁-LETTER-POWER`

XREF: `lean/notes/openmath/GENTOW5_PROOF_2026-08-09.md:S12.1-POST-D3i-TWIST-INDEX-CORRIGENDUM`

XREF: `lean/notes/openmath/GENTOW5_PROOF_2026-08-09.md:S11.5-OUTER-ψ₁-LEG`

**CONDITIONALITY:** “Under \(\mathcal W_{\le n}\)” and “\(2\le j\le n+1\).”

**RESOLUTION TRACE:** base §5.2; no T3 r-round touched it; folds the post-D3i GENTOW5 corrigendum.

**TEETH:**

- §8.3(5), GENTOW5 index lint — requires \(j-1\) and \(w_n\) at the top.
- §8.4(6), twist-index mutant — restoring \(\omega_j\) must expose unavailable \(w_{n+1}\).

---

### EFF.T3.25  [hypothesis]

**CANONICAL STATEMENT:** [ASSEMBLED — verbatim components from base lines 768–808]

> “For every nonzero recipe coefficient, with
> \[
> s=f_{i+1}-t\ge1,
> \qquad
> m_t=su_{i+1},
> \]
> GENTOW5 S12.2 supplies
> \[
> \operatorname{bound}_i<E_i,
> \qquad
> m_t
> \ge u_{i+1}
> >
> e_{i+1}E_i
> \ge E_i
> >
> \operatorname{bound}_i.
> \tag{G5-LIFT-RANGE}
> \]”

> “Therefore
> \[
> \widehat k_t
> =
> \operatorname{lift}_i
> \bigl(
> c_t\vartheta_{i,s};su_{i+1}
> \bigr)
> \]
> uses the preceding-rung \(K_i\)-digit lift above \(\operatorname{bound}_i\), not a nonexistent requirement above \(\operatorname{bound}_{i+1}\). Recipe lifts and refine lifts retain their respective corrected rungs.”

> “This range repair does not itself discharge \([{\rm GENTOW5\!-\!W}(i)]\) and does not weaken (G5-COND).”

XREF: `lean/notes/openmath/GENTOW5_PROOF_2026-08-09.md:S12.2-[R-i4]`

**CONDITIONALITY:** “For every nonzero recipe coefficient,” with \(s=f_{i+1}-t\ge1\) and \(m_t=su_{i+1}\).

**RESOLUTION TRACE:** base §5.3; no T3 r-round touched it; folds GENTOW5 S12.2 R-i4.

**TEETH:**

- §8.3(6), GENTOW5 lift lint — recipe and refine lifts must use their respective rungs.
- §8.4(7), lift-rung mutant — a recipe demand above \(\operatorname{bound}_{i+1}\) must fail on the depth-4 witness.

---

### EFF.T3.26  [instance-record]

**CANONICAL STATEMENT:** [ASSEMBLED — verbatim components from base lines 816–859]

> \[
> {\rm GENTOW\!-\!6.4}
> \quad\text{is not an instance of LEMMA COCYCLE-TELESCOPE.}
> \tag{G6-NONINSTANCE}
> \]

> “Its operative projection and cap have the additive form
> \[
> \begin{gathered}
> \text{block value at height }m
> =
> \bigl(
> \text{\(f\)-value at height }m+c_g
> \bigr)-c_g,\\
> \text{the block read is lift-stable below }
> e_1e_2N-c_g.
> \end{gathered}
> \tag{G6-PROJECTION}
> \]”

> “The proof uses:
>
> - triangularity of repeated monic division in the \(x\)-degree filtration;
> - congruence of digit coordinates;
> - nonnegativity of the offset \(w(a,b)\);
> - ultrametric minima below the window cap;
> - the separately established projection equation.”

> “It does not use a multiplicative normalizer section, a degree-zero residue quotient, a normalizer cocycle, a ladder peel, or a cocycle bracket.”

> “Taking (G6-PROJECTION) as carrier data would insert the endpoint relation needed by the source and violate the withdrawal tooth.”

XREF: `lean/notes/openmath/GENTOW6_PROOF_2026-08-09.md:S6.2-LEMMA-GENTOW-6.4`

**CONDITIONALITY:** Its own additive triangular-cap source proof; it is not a T3 instance and contributes no absorption.

**RESOLUTION TRACE:** base §6.1; acceptance paragraph incorrectly lists GENTOW-6.4 among “three absorptions”; post-acceptance record expressly confirms “GENTOW-6.4 confirmed NOT ABSORBED.”

**TEETH:**

- §8.3(7), GENTOW-6.4 regression — must be labelled `NON_INSTANCE_REGRESSION` and must not increment the absorption count.
- §8.4(3), endpoint-as-input mutant — the same withdrawal principle guards against installing G6-PROJECTION as carrier data.

---

### EFF.T3.27  [instance-record]

**CANONICAL STATEMENT:** [ASSEMBLED — verbatim components from base lines 863–900]

> “The GENTOW6_BOXES E11 riders are regression facts, not new T3 carrier fields.”

> “In GENTOW-6.5 Step IV, \(\pi^{2a_{t^*}}\) is a valuation carrier, not a unit:
> \[
> v\!\left(
> \binom m2\,
> \widehat c_{t^*}^{\,2}
> \pi^{2a_{t^*}}
> \cdot{\rm wrap}
> \right)
> =
> v\!\left(\binom m2\right)+2a_{t^*}.
> \tag{G6-E11-1}
> \]
> After removing the prescribed power, the graded digit is nonzero exactly when \(p\nmid\binom m2\).”

> “Exact-\(\Theta_j\) attainment is decided by the \(\chi\)-criterion at maximal-\(s^*\) slots and by the displayed cascade digits at lower-\(s\) slots. T3 carries no broader chi-only shorthand.”

> “The certified record has three kill-count fields totaling five kills:
> \[
> T\text{-OBSTR}=1,\qquad
> T\text{-NODELTA}=2,\qquad
> T\text{-BELOW}=2.
> \]”

> “S12’s final byte-frozen list contains six runner/output pairs; the GENTOW6_PROOF prefix and PE3 pair are recorded separately.”

> “None of these corrections introduces a multiplicative cocycle into GENTOW-6.4 or changes its non-instance status.”

XREF: `lean/notes/openmath/GENTOW6_BOXES_2026-08-10.md:E11-F-1`

XREF: `lean/notes/openmath/GENTOW6_BOXES_2026-08-10.md:E11-F-2`

XREF: `lean/notes/openmath/GENTOW6_BOXES_2026-08-10.md:E11-F-3`

XREF: `lean/notes/openmath/GENTOW6_BOXES_2026-08-10.md:E11-F-4`

**CONDITIONALITY:** “regression facts, not new T3 carrier fields.”

**RESOLUTION TRACE:** base §6.2; no T3 r-round touched it; folds the certified GENTOW6_BOXES E11 riders.

**TEETH:**

- §8.3(8), GENTOW6 E11 records — scores all four rider corrections.
- §8.4(8), GENTOW6 unit mutant — declaring \(\pi^{2a_{t^*}}\) a unit must fail.

---

### EFF.T3.28  [instance-record]

**CANONICAL STATEMENT:** [ASSEMBLED — verbatim final-record components from lines 1360–1368]

> “GENTOW2-B″ PASS, HETOW-4 PASS; GENTOW-6.4 confirmed NOT ABSORBED — in exact agreement with this note's own (G6-NONINSTANCE) display.”

> “The unit's scope of record is therefore TWO absorptions + one documented non-instance; GENTOW-6.4 retains its own certified proof.”

> “The absorbed notes' dated ‘absorbed by S-2 as instance’ appends may now land for the two passing absorptions.”

Thus the accepted supply set is exactly:

1. GENTOW2-B″ through ABS-G2.
2. HETOW-4 through ABS-HE4 and HE4-COB.

GENTOW-6.4 is the documented non-instance and is not supplied. GENTOW5-W(i) is not included in this final supply set because it is absent from the dispositive post-acceptance record.

**CONDITIONALITY:** NONE for the scope record itself. Each supplied conclusion retains the hypotheses and fences in EFF.T3.19–20.

**RESOLUTION TRACE:** base §0 and §7 say three absorptions; acceptance lines 1351–1353 give a contradictory three-item list; post-acceptance lines 1360–1368 expressly narrow the scope of record to two absorptions plus one non-instance and therefore govern.

**TEETH:**

- §8.3(7) — GENTOW-6.4 must not increment the absorption count.
- Acceptance consumption checks — GENTOW2-B″ PASS; HETOW-4 PASS; GENTOW-6.4 NOT ABSORBED.

---

### EFF.T3.29  [instance-record]

**CANONICAL STATEMENT:** [ASSEMBLED — effective r1 replacement §8.2, lines 1229–1337]

> “The boundary-read and comparison ports use the same section arithmetic but distinct, explicitly declared ladder steps. No common value of \(q\) is asserted between the two port instances.”

Boundary port:

> \[
> p=5,\qquad
> N(k)=x^{\,k\bmod2}5^{(k-(k\bmod2))/2},
> \qquad
> q_{\rm BR}=1.
> \]

> \[
> \operatorname{res}(x/T)=3,
> \qquad
> \operatorname{res}(x^2/5)=2.
> \]

> \[
> U(0),U(1),U(2),U(3),U(4)=1,3,2,1,4,
> \]
> while
> \[
> \vartheta_0,\vartheta_1,\vartheta_2,\vartheta_3,\vartheta_4
> =1,1,2,2,4.
> \]

> “The runner must verify
> \[
> w^s=U(s)\vartheta_s,
> \qquad
> U(s)=\Theta_sw^s
> \]
> without defining \(U(s)\) from the endpoint formula.”

Comparison port:

> \[
> \widehat N(k)=x^k,\qquad
> q_{\rm CMP}=2,\qquad
> H_0=6,\qquad
> D=3,\qquad
> H_t=6-2t.
> \]

> \[
> \chi(k)
> =
> \operatorname{res}\!\left(
> \frac{\widehat N(k)}{N(k)}
> \right)
> =
> 2^{\lfloor k/2\rfloor}\pmod5.
> \]

> \[
> \chi(1)\chi(1)=1\ne2=\chi(2).
> \]

> \[
> \delta=\chi(q_{\rm CMP})=\chi(2)=2,
> \qquad
> \chi(H_0)=\chi(6)=2^3=3
> \quad\text{in }\mathbf F_5^\times.
> \]

> \[
> \rho_t
> =
> 3\widehat\rho_t\,2^{-t},
> \qquad
> R(Z)
> =
> 3\widehat R(Z/2)
> \quad\text{in }\mathbf F_5[Z].
> \]

> “The runner must verify both identities from the assembled coefficient definitions. FRAME-C consists of two direct graded-carrier port instances sharing the displayed section arithmetic; it is not a realized p-adic tower.”

**CONDITIONALITY:** The reference \(T\) is formal; the two ports use \(q_{\rm BR}=1\) and \(q_{\rm CMP}=2\), respectively; the frame is not a realized p-adic tower.

**RESOLUTION TRACE:** base §8.2, lines 940–1000, replaced in full; r1 R1-G1 supplies the canonical §8.2 at lines 1229–1337.

**TEETH:**

- Effective §8.2 is itself the direct common-carrier battery.
- §8.4(1), character mutant.
- §8.4(2), theta-free mutant.
- §8.4(3), endpoint-as-input mutant.
- §8.4(4), inverse-orientation mutant.

---

### EFF.T3.30  [hypothesis]

**CANONICAL STATEMENT:**

> \[
> \text{a realized p-adic B\(''\) frame with }
> \Theta_N(s;q)\ne1
> \quad\text{and}\quad
> w_i\ne1
> \text{ simultaneously}.
> \tag{T3-JOINT-OPEN}
> \]

> “The abstract FRAME-C has both axes live, but its reference \(T\) is formal. This machine-coverage gap is not a proof gap.”

**CONDITIONALITY:** This is an open machine-coverage obligation, not a hypothesis of T3-BR and not a proof gap.

**RESOLUTION TRACE:** base §8.5, lines 1065–1081; r1 corrects FRAME-C but does not close this realized p-adic coverage item.

**TEETH:** NONE. The note explicitly records this as unexercised machine coverage.

---

### EFF.T3.31  [convention]

**CANONICAL STATEMENT:** [ASSEMBLED — verbatim fences from base §9]

> “T3 imports T1’s cocycle laws; it does not claim a second proof of them.”

> “T3’s boundary port discharges a sitewise residual-read obligation. It does not assert multiplicativity for arbitrary homogeneous initial forms.”

> “\(\vartheta_N\) is the building/dictionary orientation and \(\Theta_N=\vartheta_N^{-1}\) is the B-law orientation.”

> “HETOW’s pointwise section ratio need not be a character.”

> “HETOW-4’s explicit floor exponent and common-lift/iteration conclusions remain source-specific.”

> “Polynomial gauge substitution preserves factor patterns, not literal coefficients.”

> “Conversion of a residual factor pattern to a p-adic splitting type still uses the surrounding tower correctness theorem.”

> “GENTOW-6.4 remains additive, filtration-triangular, and unabsorbed.”

> “T3 proves no universal closed formula for \(w_i\).”

> “T3 does not identify an avatar unit with an intrinsic residual-read unit.”

> “T3 proves no cross-face WELD coherence or gauge uniqueness.”

**CONDITIONALITY:** These are scope fences on every preceding unit; NONE is an additional theorem hypothesis unless its corresponding statement already names it.

**RESOLUTION TRACE:** base §9, items 1–3, 8–16; no r-round touched them; the final record confirms the GENTOW-6.4 fence.

**TEETH:**

- §8.1(3) — guards the T1 non-reproof and WELD fences.
- §8.1(4) — guards the sitewise-only B-law perimeter.
- §8.3(2) — guards HETOW non-character and routing.
- §8.3(7) — guards the GENTOW-6.4 non-instance.
- §8.4(1), character mutant.
- §8.4(2), theta-free mutant.
- §8.4(4), inverse-orientation mutant.

---

## 3. Consumption table

### 3.1 Consolidated imports/XREFs

| # | XREF | Material consumed by T3 |
|---:|---|---|
| 1 | `T1_GAUGE_COCYCLE_2026-08-12.md:NORMALIZED-NORMALIZER-SECTION-SETUP` | Exact-height normalized section, height-zero residual vocabulary, ambient residue fields |
| 2 | `T1_GAUGE_COCYCLE_2026-08-12.md:T1-C2` | Normalized cocycle definition, endpoints, and cocycle law |
| 3 | `T1_GAUGE_COCYCLE_2026-08-12.md:T1-WRAP-FORMULA` | Level-1 residue governance only; not re-proved |
| 4 | `T1_GAUGE_COCYCLE_2026-08-12.md:T1-TEL` | \(\vartheta_N\), endpoints, and recurrence |
| 5 | `T1_GAUGE_COCYCLE_2026-08-12.md:T1-THETA` | Inverse B-law orientation |
| 6 | `T1_GAUGE_COCYCLE_2026-08-12.md:T1-DICT` | Coherent/multiplicative digit dictionary |
| 7 | `GENTOW2_PROOF_2026-08-09.md:S5.1-LEMMA-GENTOW2-B′` | \(i=2\) slot geometry, residual read, expansion/elimination, exact digit, and root evaluation |
| 8 | `GENTOW2_PROOF_2026-08-09.md:S5.2-LEMMA-GENTOW2-B″` | \(i=2\) one-\(w\) specialization and B″ target |
| 9 | `HETOW_RECON_2026-08-09.md:LEMMA-HETOW-4(a)` | Pointwise section-ratio formula and source floor arithmetic |
| 10 | `HETOW_RECON_2026-08-09.md:LEMMA-HETOW-4(b)` | Source wrap/floor specialization of the abstract coboundary |
| 11 | `HETOW_RECON_2026-08-09.md:LEMMA-HETOW-4(c)` | HETOW assembled-coefficient recipe |
| 12 | `GENTOW5_WI_2026-08-10.md:S1–S2-[GENTOW5-W(i)]` | Certified level-\(i\) boundary-read package and displayed target |
| 13 | `GENTOW5_PROOF_2026-08-09.md:S12.1-[R-i2]` | Cumulative \(\mathcal W_{\le n}\) consumer conditionality |
| 14 | `GENTOW5_PROOF_2026-08-09.md:S11.3-FIXED-z₁-LETTER-POWER` | The \(i=1\) unit \(\omega_1\) |
| 15 | `GENTOW5_PROOF_2026-08-09.md:S12.2-[R-i4]` | Correct recipe/refine lift rungs and range |
| 16 | `GENTOW5_PROOF_2026-08-09.md:S12.1-POST-D3i-TWIST-INDEX-CORRIGENDUM` | Correct \(j-1\) residual-twist index |
| 17 | `GENTOW5_PROOF_2026-08-09.md:S11.5-OUTER-ψ₁-LEG` | Separately governed outer \(\psi_1\) leg |
| 18 | `GENTOW6_PROOF_2026-08-09.md:S6.2-LEMMA-GENTOW-6.4` | Independent additive triangular-cap theorem used only as a non-instance regression |
| 19 | `GENTOW6_BOXES_2026-08-10.md:E11-F-1` | Valuation-carrier correction |
| 20 | `GENTOW6_BOXES_2026-08-10.md:E11-F-2` | Maximal-\(s^*\)/lower-\(s\) attainment split |
| 21 | `GENTOW6_BOXES_2026-08-10.md:E11-F-3` | Three fields/five kills record |
| 22 | `GENTOW6_BOXES_2026-08-10.md:E11-F-4` | Six-pair artifact count |

T1’s conditional B-law is deliberately excluded from the import list as a premise for GENTOW5-W(i). HETOW’s common lift and finite-chain conclusions are also excluded: they remain source-local.

### 3.2 Accepted supplies to consumers

| Consumer/source unit | Effective T3 supply | Surviving fence | Final status |
|---|---|---|---|
| GENTOW2-B″ | EFF.T3.14 specialized as EFF.T3.19, ABS-G2, including polynomial rescaling and factor-pattern invariance | Source-local BR1–BR5 package; no endpoint identity as input | **ABSORBED — PASS** |
| HETOW-4(b) | EFF.T3.16 specialized as HE4-COB | Explicit two-floor exponent remains HETOW arithmetic | **ABSORBED SHAPE — PASS** |
| HETOW-4(c) | EFF.T3.15 and EFF.T3.17 specialized as ABS-HE4 | HETOW assembled-coefficient recipe | **ABSORBED — PASS** |
| HETOW-4(d), routing portion | EFF.T3.18 specialized in ABS-HE4 | Common polynomial lift and later iterate independence remain HETOW-local | **ABSORBED ROUTING — PASS** |
| GENTOW-6.4 | No T3 theorem supplied | Independent additive triangular-cap proof | **NOT ABSORBED; documented non-instance** |
| GENTOW5-W(i) | EFF.T3.21 remains in the mathematical inventory | Its downstream chain retains \(\mathcal W_{\le n}\) | **NOT IN FINAL TWO-ABSORPTION SCOPE; see OPEN-CALL 3** |

### Acceptance paragraph versus later narrowing record

The acceptance paragraph’s wording cannot govern the supply list literally: it calls GENTOW-6.4 both an absorption and, through the accepted body, a non-instance. The later record was written after the consumption checks, explicitly says “scope of record,” identifies the two passing absorptions, and confirms GENTOW-6.4 “NOT ABSORBED.” It therefore governs the consumer-facing supply list.

The later record does not say that §5 is deleted or false. This compilation consequently retains EFF.T3.21–25 as mathematical content but does not promote GENTOW5-W(i) into the final accepted absorption list.

---

## 4. Fidelity rules obeyed

1. The source rule followed was:

   > “The T-unit acceptance records' own effective-text rules govern.”

2. No displayed mathematical statement was paraphrased where it could be reproduced verbatim.
3. Blocks marked `[ASSEMBLED]` concatenate verbatim components that are separated by setup, qualification, or rider text. Each such block lists the source line span.
4. No `[ASSEMBLED]` block changes a quantifier, index, inequality, direction of implication, inverse, field, rung, or source status.
5. r1’s §8.2 is reproduced as the effective battery frame. The superseded base §8.2 arithmetic is not treated as canonical.
6. The post-acceptance supply narrowing is folded only into supply status. It is not used to invent a textual deletion of §5.
7. E11 material is retained only in its stated role:

   > “regression facts, not new T3 carrier fields.”

8. Proof prose was not promoted into a new theorem unless the note itself states the corresponding mathematical conclusion or fence.
9. No unnamed source theorem was assigned a fabricated designation. Where T3 itself lacks an exact designation, that defect is recorded below.

---

## 5. Self-audit

### OPEN-CALL 1 — missing literal effective-text definition

Unlike some other T-units, T3’s acceptance record contains no sentence of the form “the accepted text is base plus r1” or “the effective text is…”. This compilation inferred base-plus-r1 from the acceptance chronology and the explicit R1-G1 replacement. The requested header field therefore cannot be populated by a literal effective-text-definition sentence; the closest governing quotations were supplied.

### OPEN-CALL 2 — internally impossible acceptance list

The acceptance paragraph says:

> “three absorptions (GENTOW2-B″, HETOW-4, GENTOW-6.4) and one displayed non-instance.”

This simultaneously classifies GENTOW-6.4 as absorbed and accepts a body that says it is not an instance. The later consumption record resolves GENTOW-6.4’s status, but the acceptance paragraph remains internally malformed.

### OPEN-CALL 3 — GENTOW5 omission from the final scope

The base text repeatedly identifies ABS-G5W as the third genuine absorption, but neither the acceptance paragraph’s list nor the post-acceptance three-leg consumption check names it. The later record says the scope is “TWO absorptions + one documented non-instance.” This compilation excludes GENTOW5-W(i) from the supply list but retains §5 as accepted mathematical content because no record declares §5 superseded, withdrawn, or false. The cross-reader must decide whether the final record was intended to delete §5 from effective mathematics or only from the consumption protocol.

### OPEN-CALL 4 — “blueprint’s third target” referent

The post-acceptance record says:

> “the blueprint's third target was honestly narrowed at revision.”

The note’s base ordering has GENTOW5-W(i) as absorption 3 and GENTOW-6.4 as the displayed non-instance, while the consumption protocol’s third leg is GENTOW-6.4. The phrase “third target” therefore has two possible enumeration schemes.

### OPEN-CALL 5 — base absorption ledger after narrowing

Base §7 says the absorption count is three and names GENTOW5-W(i); the post-acceptance record says the scope is two. The final record does not explicitly say “replace §7.” This compilation treats §7’s supply count as superseded but keeps its hypothesis and dependency information.

### OPEN-CALL 6 — exact T1 setup designation

T3 imports the normalized section setup from “T1” but gives only display designations for T1-C2, T1-TEL, T1-THETA, and T1-DICT. `NORMALIZED-NORMALIZER-SECTION-SETUP` is a descriptive cross-spec designation, not a tag printed by T3. Phase 0a cross-note reconciliation should replace it with T1’s eventual EFF identifier.

### OPEN-CALL 7 — T1 wrap unit designation

T3 says “T1’s wrap formula” without giving its display tag. `T1-WRAP-FORMULA` is therefore a descriptive unit designation pending the T1 effective spec.

### OPEN-CALL 8 — GENTOW5 primitive supplier perimeter

T3 says the “certified level-\(i\) expansion, peel, positive-degree elimination, exact-grade law, and root-evaluation package” instantiates BR1–BR5, but it does not give separate source tags for all five facts. This compilation points to GENTOW5_WI S1–S2 as the smallest named source span and does not invent five finer units.

### OPEN-CALL 9 — outer \(\psi_1\) source designation

T3 says the outer \(\psi_1\) leg is governed by “its accepted source statement” without naming that statement. The mapping to GENTOW5 S11.5 follows the note’s own change record, but should be confirmed against EFF-GENTOW5.

### OPEN-CALL 10 — inventory type for non-instances and regression frames

The prescribed inventory types have no `non-instance`, `regression`, or `open-obligation` category. GENTOW-6.4, E11, and FRAME-C were classified as `instance-record`; T3-JOINT-OPEN was classified as `hypothesis`. This is a pilot-format defect, not a mathematical resolution.

### OPEN-CALL 11 — teeth granularity

Several battery rows jointly guard BR1–BR5 and T3-BR rather than one declaration each. The same row is therefore attached to multiple units. The prescribed format does not specify whether duplicated source teeth should become duplicated formalization obligations or one shared regression node.

### OPEN-CALL 12 — unnamed surrounding tower correctness theorem

Honesty-ledger item 11 requires a “surrounding tower correctness theorem” to convert residual factor patterns to p-adic splitting types, but T3 names neither its note nor unit. It cannot yet be emitted as a valid XREF without invention and must be resolved during cross-spec interface compilation.

EFF-T3 COMPILED: 31 statements / 22 xrefs / 12 open calls
