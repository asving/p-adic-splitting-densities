# T2 — THE σ-LADDER MASTER: one original-\(O\) carrier, one general HE7.A, and five literal instances

**Unit:** T2 / σ-ladder master composition.  
**Date:** 2026-08-12.  
**Status:** composition draft, attempt grade **0/2**. This note states one master theorem and records five literal source instances: **HE3.A**, **HE6**, **HE7 + HE6R1**, **HETOW**, and **GENTOW4**. It is a composition claim, not an acceptance upgrade of any supplier.

## S0. VERDICT, REDLINE, AND SOURCE-PIN CONVENTION

**S-6 GO.** The mandatory structural redline is:

> The master carrier is a DVR-backed ladder carrier over the **original complete DVR \(O\)**. A quotient or stage order may be carried as optional instance data, but the master never requires it to be a complete DVR.

The current key is required to be **monic**, not irreducible. This is load-bearing: the central HE7 key \(\Psi=\Psi_{\lambda,r}\) is explicitly never assumed irreducible. Requiring either a complete-DVR stage quotient or `keyIrreducible` would exclude that instance and import precisely the stage-ring obstruction that the original-\(O\) slot proof avoids.

### S0.1 Immutable HEAD span pins

The five source texts supplied for this composition are append-heavy. Line numbers are therefore not immutable: a dated append moves them without changing the cited text. This note uses **marker-delimited span pins**. A pin

```text
path :: «exact unique start marker» ..< «exact unique end marker»
```

means the span beginning at the exact start marker and ending immediately before the exact end marker. A consumer fails closed if either marker is absent, non-unique, or ordered incorrectly.

The five instance pins are:

1. **HE3.A**

   ```text
   lean/notes/openmath/HE3_PROOF_2026-08-08.md
   :: «> **THEOREM HE3.A (THE STAGE-σ RECURSION — the mechanism).**»
   ..< «> **COROLLARY HE3.B»
   ```

   with proof span

   ```text
   :: «### S6.3 PROOF OF THEOREM HE3.A»
   ..< «### S6.4 PROOF OF COROLLARY HE3.B»
   ```

   and auxiliary carrier spans beginning at:

   ```text
   > **DEFINITION 1 (the stage resolvent and its label set).**
   > **LEMMA HE3-1L [r1, F1 — THE LETTER LIFT AT LEVEL 1
   > **LEMMA HE3-6 [r1] (Galois equivariance of labels).**
   ```

   The dated R8 repairs consumed here begin at:

   ```text
   ### Dated correction (2026-08-12, post-R8) — R8-2
   ### Dated correction (2026-08-12, post-R8) — R8-3
   ### Dated correction (2026-08-12, post-R8) — R8-4
   ### Dated correction (2026-08-12, post-R8) — R8-5
   ```

2. **HE6**

   ```text
   lean/notes/openmath/HE6_PROOF_2026-08-08.md
   :: «> **DEFINITION HE6-1 (THE ENLARGED TEST FAMILY).**»
   ..< «> ~~**COROLLARY HE6.B**»
   ```

   with proof span

   ```text
   :: «## S3. THE DISK, THE FORCING, AND THE ξ-SIDE»
   ..< «## S7. THE ONE SURVIVING BOX»
   ```

   The slot seam is pinned by:

   ```text
   :: «**Dated correction (2026-08-12, post-acceptance challenge F-1 —
         normalized slot coefficients in LEMMA HE6-0″).**»
   .. «No theorem statement is weakened.»
   ```

   This is the source of \(\gamma_k(A)\) and the
   \(\gamma_k(A)\eta^{-q(k)}\) conversion below.

3. **HE7 + HE6R1**

   ```text
   lean/notes/openmath/HE7_PROOF_2026-08-08.md
   :: «> **THEOREM HE7.A (THE LEVEL-2 READ DECIDES — HE6.A one level up).**»
   ..< «> **THEOREM HE7.C»
   ```

   with the slot/lift and transfer span

   ```text
   :: «> **(SLOT₂) [PROVED, §S3].**»
   ..< «## S7. TERMINATION»
   ```

   together with:

   ```text
   lean/notes/openmath/HE6R1_RECON_2026-08-08.md
   :: «> **LEMMA HE6R1-1 (the widened jump condition descends, with HE7.C's
         > bounds).**»
   ..< «### S3.4 LEMMA HE6R1-2»
   ```

   ```text
   :: «> **LEMMA HE6R1-2 [r1′] (block projection).**»
   ..< «### S3.4b LEMMA HE6R1-3»
   ```

   ```text
   :: «> **LEMMA HE6R1-3 (the level-2 peel).**»
   ..< «### S3.5 RECONCILIATION VERDICT»
   ```

   The mixed-residual rider is the HE7 span beginning:

   ```text
   > **ANNEX-LEMMA HE7-13′ (mixed residual nodes: the block split, and the
   ```

   and ending after its `**The wiring` paragraph and three bullets. The corrected all-level cocycle is pinned from:

   ```text
   > **ANNEX-DEF HE7-2′
   ```

   through:

   ```text
   > **ANNEX-COROLLARY R1-d
   ```

4. **HETOW**

   ```text
   lean/notes/openmath/HETOW_RECON_2026-08-09.md
   :: «> **LEMMA HETOW-1 (label translation)»
   ..< «## S3. THE RECONCILIATION THEOREM»
   ```

   and:

   ```text
   :: «> **THEOREM HETOW.A ([GENHN-HE(μ₂)] at tower stages = THEOREM HE7.A at
         > the composed carrier — literal instance).**»
   ..< «**MINIMAL LIVE DEGREE (derived).**»
   ```

   The normalizer bridge is the inclusive dated span beginning:

   ```text
   > **LEMMA HETOW-4 (the normalizer bridge).**
   ```

   and ending with its proof. Raw per-height residues are not identified; the **assembled** residuals are related by one global unit and one variable rescaling.

5. **GENTOW4**

   ```text
   lean/notes/openmath/GENTOW4_PROOF_2026-08-09.md
   :: «> **LEMMA GENTOW-4.1.** In the S0 setting (partial side):»
   ..< «## S3. THEOREM GENTOW-4.A»
   ```

   ```text
   :: «> **THEOREM GENTOW-4.A (partial inner sides: block split +
         > projection + per-block full-side instances).**»
   ..< «## S4. LEMMA GENTOW-4.2»
   ```

   ```text
   :: «> **LEMMA GENTOW-4.2 (tie, PURE-POWER sides).**»
   ..< «## S5. PE2-P VERIFIED EXACTLY»
   ```

   The record also consumes the acceptance-fold paragraph beginning:

   ```text
   [acceptance fold (post-PE3) 2026-08-10, m-i — THE CITATION COMPLETED
   ```

   because it distinguishes vertex equality from side-interior equality and supplies the residual-scalar reason for the latter.

No unpasted file content is used to manufacture a theorem hypothesis.

## S1. THE ORIGINAL-\(O\) σ-LADDER CARRIER

### S1.1 Ground data

A **σ-ladder carrier** \(\mathcal C\) consists of

\[
\mathcal C=
(O,K_0,\overline K_0,v,\pi,k_0,\overline k;
 K,D,\Phi,d,T,\operatorname{Pt},\iota,n,h,\operatorname{dig},
 \operatorname{Full},L,\tau).
\]

It satisfies:

1. \(O\) is a complete DVR with fraction field \(K_0\), uniformizer \(\pi\), finite residue field \(k_0=\mathbf F_Q\), and a fixed algebraic closure \(\overline K_0\). The valuation \(v(\pi)=1\) has its unique extension to \(\overline K_0\). The residue target is a fixed \(\overline k\).

2. \(K/k_0\) is a finite field. It is the current residue-label field, constructed from the irreducible residual labels already traversed. Extending \(K\) by a residual factor extends only this label field; it does not replace \(O\).

3. \(\Phi\in O[x]\) is monic of degree \(D>0\).

   \[
   \boxed{\text{There is no hypothesis that \(\Phi\) is irreducible.}}
   \tag{NO-IRR}
   \]

4. \(d\) is the current integer-normalized value, \(T\in\mathbf Z\) is the inherited disk threshold, and \(\operatorname{Pt}\subseteq\overline K_0\) is the current point class. Every \(\xi\in\operatorname{Pt}\) carries a field embedding

   \[
   \iota_\xi:K\hookrightarrow\overline k.
   \]

5. The exact-height normalizer system is

   \[
   n:\mathbf Z\longrightarrow K_0(x)^\times,
   \qquad n(0)=1,
   \qquad d(n(k)(\xi))=k
   \]

   for every \(k\) and every \(\xi\in\operatorname{Pt}\). Normalizers may be Laurent polynomials. Integrality is required of constructed lift and test polynomials, not of the normalizers used to read residues.

The complete DVR in this definition is always the original coefficient ring \(O\). An instance may expose an order \(O[\theta]\), its integral closure, or a stage quotient, but none is a master carrier hypothesis.

### S1.2 Slot grammar

For every nonzero \(A\in O[x]\) with \(\deg A<D\), the carrier provides

\[
h(A)\in\mathbf Z,
\qquad
\operatorname{dig}(A)\in K^\times,
\]

and, for every \(\xi\in\operatorname{Pt}\),

\[
d(A(\xi))=h(A),
\qquad
\operatorname{res}\!\left(
 \frac{A(\xi)}{n(h(A))(\xi)}
\right)=\iota_\xi(\operatorname{dig}(A)).
\tag{SLOT}
\]

Set \(h(0)=+\infty\) and \(\operatorname{dig}(0)=0\) when total notation is convenient. At arbitrary \(\xi\notin\operatorname{Pt}\), the carrier supplies only the ultrametric lower bound obtained from the preceding-key development; it makes no exactness claim outside `Pt`.

At level one the coherent digit is not a sum of bare coefficient residues. For \(A=\sum_{j<D'}a_jx^j\), \(k=dv(A)\), and the unique \(0\le i<e_1\) satisfying \(ih\equiv k\pmod {e_1}\), it is

\[
\boxed{
\gamma_k(A)=
\sum_{\substack{t\ge0\\i+e_1t<D'}}
\operatorname{res}\!\left(
a_{i+e_1t}\pi^{-(k-(i+e_1t)h)/e_1}
\right)\eta^t.}
\tag{GAMMA}
\]

Pins strictly above height \(k\) contribute zero. Thus the HE6 carrier has

\[
\operatorname{dig}(A)=\gamma_k(A).
\]

If an HE6 consumer reads against \(\varpi^k\) rather than the coherent canonical \(n(k)\), its literal source formula is

\[
\boxed{
\operatorname{res}\!\left(\frac{A(\xi)}{\varpi(\xi)^k}\right)
=\iota_\xi(\gamma_k(A))\,\eta_\xi^{-q(k)}.}
\tag{HE6-SEAM}
\]

The factor \(\eta^{-q(k)}\) is a frame conversion, not part of the coherent digit. Omitting the coefficient normalizers inside \(\gamma_k\), or using the opposite sign on \(q(k)\), is forbidden by the HE6 HEAD correction.

### S1.3 Occupied heights and lifts

The carrier has a predicate \(\operatorname{Full}(k)\). Only at a full height does it provide an integral lift

\[
L_k:K\longrightarrow O[x]_{<D}
\]

with

\[
L_k(0)=0,
\qquad
c\ne0\Longrightarrow
h(L_k(c))=k,
\quad
\operatorname{dig}(L_k(c))=c.
\tag{LIFT}
\]

A theorem block \(B\) declares finite sets

\[
H_{\mathrm{occ}}(B),\qquad H_{\mathrm{lift}}(B).
\]

The first contains every coefficient height read by the proof. The second contains every height at which the proof constructs a digit. Its visible domain obligation is

\[
\boxed{
H_{\mathrm{lift}}(B)\subseteq
\{k:\operatorname{Full}(k)\}.}
\tag{OCC}
\]

There is no assertion that every integral height is full.

For the HE6 level-one carrier,

\[
\operatorname{Full}(k)
\Longleftrightarrow
k\ge(i(k)+e_1(f_1-1))h,
\]

and \(k\ge(D'-1)h\) is a uniform sufficient condition.

For the HE7 level-two carrier, writing

\[
n_2(k)=\varpi^{m(k)}{\Phi'}^{s(k)},
\qquad
\ell m(k)+s(k)u=k,
\qquad
0\le s(k)<\ell,
\]

a sufficient per-height condition is

\[
m(k)\ge(d_r-1)u+(D'-1)h,
\tag{FULL2}
\]

and the uniform sufficient bound is

\[
k\ge(\ell d_r-1)u+\ell(D'-1)h.
\tag{FULL2-U}
\]

Higher carriers retain `Full` as a proved predicate. They do not replace it with “all integral heights.”

### S1.4 Cocycles and coherent frames

Define

\[
\tau(a,b)=\frac{n(a)n(b)}{n(a+b)}.
\]

At every carrier point this is a value-zero unit whose residue is the transport of a fixed element of \(K^\times\). It satisfies

\[
\tau(0,a)=\tau(a,0)=1,
\qquad
\tau(a,b)\tau(a+b,c)=\tau(b,c)\tau(a,b+c).
\tag{COC}
\]

For a next-step numerator \(u\), set

\[
\vartheta_s=
\operatorname{res}\!\left(\frac{n(u)^s}{n(su)}\right),
\qquad
\Theta_s=\vartheta_s^{-1}.
\]

The master theorem is stated in the **coherent normalizer frame**: every pin is divided by the normalizer of its total height and every cocycle bracket is included in residual assembly. A multiplicative or print-frame consumer supplies

\[
\Gamma_s=c_s^{\mathrm{mult}}\vartheta_s,
\qquad
R_{\mathrm{can}}(Y)=w^mR_{\mathrm{mult}}(Y/w).
\tag{FRAME}
\]

Only factor degrees, multiplicities, separability, and transported root classes are invariant. Literal coefficient strings are not claimed equal.

At HE7 level two,

\[
\frac{n_2(k)n_2(k')}{n_2(k+k')}
=
\left(\frac{{\Phi'}^\ell}{\varpi^u}\right)^c,
\qquad
c=\frac{s(k)+s(k')-s(k+k')}{\ell},
\]

so its residue is the genuine

\[
\boxed{\beta^c}
\tag{BETA}
\]

twist. It is not set to \(1\).

At deeper levels the corrected HE7-2′ normalizer recursion makes \(\tau\) a monomial in all preceding letters. The slot formula multiplies by those fixed units, and the lift formula inserts their inverses.

### S1.5 Blocks, windows, caps, and origin

A **σ-block** \(B\) over \(\mathcal C\) consists of a monic polynomial \(F\in O[x]\), an integer \(\mu\ge1\), and its \(\Phi\)-development

\[
F=\Phi^\mu+\sum_{j<\mu}A_j\Phi^j,
\qquad
\deg A_j<D,
\qquad
\deg F=\mu D.
\tag{DEV}
\]

It carries these visible certificates:

1. `Separable`:

   \[
   \operatorname{disc}(F)\ne0.
   \]

2. `Roots`: the roots of \(F\) are exactly the designated Galois-stable block class and all lie in `Pt`.

3. `Proper`:

   \[
   \boxed{\Phi\nmid F.}
   \tag{PROPER}
   \]

   If \(\Phi\mid F\), the separate generic peel is run first.

4. `Window`:

   \[
   T<d(\Phi(\rho))<\infty
   \tag{WINDOW}
   \]

   for every root \(\rho\) of \(F\).

5. `WindowSafe`: in the declared index window, the lower hull and coherent residuals of any proxy, truncated, or tower-print polynomial equal those of \(F\).

6. `CapSafe`: every omitted or outside-window term lies strictly above every consumed face, and neither collection nor key carry can create a term below a consumed face.

For actual HE3, HE6, and HE7 block factors with their full developments, `WindowSafe` and `CapSafe` are tautological or immediate. They are substantive obligations for HETOW and GENTOW4.

If a raw harness begins at attained abscissa

\[
s_{\mathrm{act}}=s_{\min}+\nu e,
\]

the frame record supplies units \(a,b\in K^\times\) such that

\[
\boxed{
R_{\mathrm{raw}}(Y)=Y^\nu aR_{\mathrm{norm}}(bY).}
\tag{ORIGIN}
\]

The master factors \(R_{\mathrm{norm}}\) and records \(\nu\) separately. Raw and minimal-grid factors agree only after the corresponding \(z^\nu\) bridge; the origin is never silently reset to zero.

### S1.6 Base-change-free tests

For every side of slope \(u'/e'\) and every monic irreducible factor \(r'\) of its coherent normalized residual, the carrier supplies a monic test polynomial

\[
\Psi_{u'/e',r'}\in O[x]
\]

of degree

\[
De'\deg r'.
\]

The certificate package contains:

- the disk/label equivalence for every root of the test polynomial;
- local ramification and residue-degree forcing;
- nonemptiness of the target label class;
- disjointness and exhaustion of the side class;
- Galois equivariance of the fixed residual label;
- the multiplication laws for \(e\) and \(f\).

Every lift and test polynomial remains in \(O[x]\). Passing from \(K\) to \(K[Z]/(r')\) changes the residue-label carrier only. It is not a base change of \(O\).

### S1.7 Refinement and well-foundedness

For a repeated irreducible residual factor \(r'\) of multiplicity at least two, the branch is determined by \(e'\deg r'\):

- if \(e'\deg r'=1\), then \(e'=1\) and \(r'=Z-s\) for \(s\in K\). The refinement height belongs to \(H_{\mathrm{lift}}\), `(OCC)` supplies \(L_k(s)\), and the key is replaced by \(\Phi-L_k(s)\);

- if \(e'\deg r'\ge2\), the carrier constructs the child ladder carrier, and its block mass satisfies

  \[
  \mu_{\mathrm{child}}
  \le\frac{\mu}{e'\deg r'}
  \le\frac\mu2.
  \tag{MASS}
  \]

At a mixed residual the operation is performed **per label block**, not by sequentially recentering the whole polynomial. The selected repeated class moves above the refined slope; companion classes remain in their own translated blocks, as in HE7-13′.

The state family carries a well-founded lexicographic measure:

- a child jump strictly decreases mass;
- a split or peel strictly decreases degree;
- an \(\alpha\)-refine fixes degree but decreases a finite secondary discriminant/slope budget.

Equivalently, an infinite pure refine tail would converge to a repeated perfect power, contradicting separability. Termination is therefore an explicit field of the carrier/block package, not prose.

## S2. THE SINGLE GENERAL THEOREM

> **THEOREM HE7.A (σ-LADDER MASTER).** Let \(\mathcal C\) be a σ-ladder carrier over the original complete DVR \(O\), and let \(B\) be a σ-block satisfying `(NO-IRR)`, `(SLOT)`, `(OCC)`, `(COC)`, `(PROPER)`, `(WINDOW)`, `WindowSafe`, `CapSafe`, `(ORIGIN)` where applicable, the base-change-free test-family package, and the well-founded step package.
>
> Let
>
> \[
> F=\Phi^\mu+\sum_{j<\mu}A_j\Phi^j
> \]
>
> be the proper development, let \(P\) be the lower hull of \((j,h(A_j))\), and define each side residual in the coherent normalizer frame. Then:
>
> 1. every side of \(P\) has slope strictly greater than \(T\), and
>
>    \[
>    \sum_\lambda L_\lambda=\mu;
>    \]
>
> 2. if \(\lambda=u'/e'\) is a side in lowest terms whose normalized residual is separable, then for every monic irreducible \(r'\mid R_\lambda\), the label class has
>
>    \[
>    |S_{\lambda,r'}|=De'\deg r',
>    \]
>
>    is one Galois orbit, and therefore is the root set of one monic irreducible factor of \(F\). Relative to the carrier’s inherited invariants \((e_{\mathcal C},f_{\mathcal C})\), that factor has
>
>    \[
>    e=e_{\mathcal C}e',
>    \qquad
>    f=f_{\mathcal C}\deg r';
>    \]
>
> 3. if \(r'\) is repeated, the read splits on \(e'\deg r'\), not on \(e'\) alone. When the product is \(1\), the certified lift performs the \(\alpha\)-refine and the read continues at the refined key. When the product is at least \(2\), the certified child carrier continues the read with `(MASS)`;
>
> 4. at a mixed side, first split into the Galois-stable label blocks and apply clauses 2–3 to each block. No whole-polynomial sequential refine is asserted;
>
> 5. the recursive read terminates and its terminal irreducible factors, with the displayed \(e\)- and \(f\)-multiplication laws, exhaust the roots of \(F\).

**Proof.** The proof is HE7’s original-\(O\) slot argument abstracted only over the interfaces in S1.

For a point in `Pt`, `(SLOT)` makes every coefficient value exact and identifies every attaining residue in one fixed copy of \(K\). `(COC)` makes residual assembly coherent. The test-family ξ-side places all test roots in the intended disk and label; the ρ-side gives generic equality off the intended class and strict excess on it. Resultant symmetry transfers that strictness to nonemptiness.

Generic test factors of degree larger than every consumed residual give, at each rational height \(\kappa>T\),

\[
\sum_\lambda n_\lambda\min(\lambda,\kappa)
=
D\,h_F(\kappa)
=
D\sum_\lambda L_\lambda\min(\lambda,\kappa).
\]

Triangular inversion at rational samples gives no side at or below \(T\) and \(n_\lambda=DL_\lambda\).

For a separable residual, its distinct irreducible factors partition the side. Nonemptiness, Galois equivariance, and local forcing give the lower bound \(De'\deg r'\) on each class. The side total is the sum of those same bounds, so equality holds termwise and each class is one orbit. This proves clauses 1–2.

For a repeated factor, a residue usable for recentering lies in the current field exactly when \(e'\deg r'=1\). `(OCC)` makes the required lift legal. The refined-key package follows from `WindowSafe`, `CapSafe`, and the above-line perturbation certificate. In the other branch, the child carrier is the same slot construction one level up and `(MASS)` follows from side length.

HE7-13′ supplies the per-block form at mixed residuals. The well-founded measure of S1.7 rules out an infinite history. No step asks that \(\Phi\) be irreducible, that \(O[x]/(\Phi)\) be a DVR, or that \(O\) be base-changed. ∎

### S2.1 Separate peel

Properness is not hidden in HE7.A.

> **LEMMA T2.PEEL.** If \(\Phi\mid F\), the carrier’s gcd/orbit certificate gives one simple factor \(\Phi\) whenever the key-divides stratum fires, with the carrier’s current \((e,f)\). Remove it and apply HE7.A to the proper remainder. The peel decreases \(\mu\) by one and fires at most once for a separable block.

For HE7 this is HE6R1-3 together with the later gcd dichotomy at reducible keys. Irreducibility on the peel stratum is a **conclusion** of the orbit-degree sandwich, never a master hypothesis.

## S3. FIVE LITERAL INSTANCE RECORDS

Each record is a field-by-field instantiation of S1. A source may prove a stronger local fact—HE3 and HE6 have irreducible current keys—but the instance map forgets that strength. No record may add a premise absent from HE7.A.

### S3.1 INSTANCE HE3.A — base-stage resolvent read

**Source pin:** S0.1(1).

- Ground: the original complete DVR \(O\), fraction field \(K_0\), and residue field \(\mathbf F_Q\).
- Current label field: \(K=\mathbf F_{Q^{f_1}}\).
- Key: \(\Phi=\Phi'\), \(D=D'=e_1f_1\). The source has an irreducible key; the instance exports only monicity and degree.
- Value and threshold: \(d=dv=e_1v\), \(T=D'h\).
- Points: the `(T1)/(T2)` points, with \(\iota_\xi(\eta_\theta)=\eta_\xi\).
- Normalizers: coherent canonical height monomials \(n(k)\). The order \(O[\theta]\) is not asserted to be a complete DVR and is not the master carrier.
- Slot digit: the normalized coefficient sum \(\gamma_k(A)\). Exactness at arbitrary `(T1)/(T2)` points is routed through HE6-0″ as cited by HE3 HEAD.
- `Full`: the HE3-1L domain. Every height used by its test-key family lies above \(D'h>(D'-1)h\), hence `(OCC)`.
- Block: the proper separable stage factor after the \(\Phi'\)-peel. The actual full development makes `WindowSafe` and `CapSafe` immediate.
- Tests and forcing: HE3-1/1′, HE3-3/4, and HE3-6 on the HE3-decided range. The base-change-free fractional-height obligations are supplied by the HE6 carrier below; no HE3 base-change argument is imported.
- Output dictionary:

  \[
  (e,f)=(e_1e_s,f_1f_s).
  \]

This is a literal base-stage instance. It creates no complete-DVR quotient hypothesis.

### S3.2 INSTANCE HE6 — enlarged fractional-height test family

**Source pin:** S0.1(2).

- Ground, field, key, value, threshold, points, and embeddings are as in HE3.A.
- The coherent slot digit is exactly `(GAMMA)`. When reading HE6’s printed \(\varpi^k\)-formula, the instance applies `(HE6-SEAM)`:

  \[
  \operatorname{dig}(A)=\gamma_k(A),
  \qquad
  \operatorname{res}(A/\varpi^k)
  =\iota(\gamma_k(A))\eta^{-q(k)}.
  \]

  The bare sum \(\sum\operatorname{res}(a_j)\eta^t\) is not an admissible replacement.

- `Full` is the corrected HE6-1L predicate. Every coefficient lift \(B_t\) used in \(\Psi_{\kappa,r}\) lies above the uniform threshold; `(OCC)` is explicit and discharged.
- The base-change-free tests are

  \[
  \Psi_{\kappa,r}
  ={\Phi'}^{\ell d}+\sum_{t<d}B_t{\Phi'}^{\ell t}\in O[x],
  \]

  monic of degree \(D'\ell d\), never assumed irreducible.

- HE6-1 is the ξ-side; HE6-2/2′ are the evaluation displays; HE6-3 and HE6-4 are the slope-count and nonemptiness certificates; HE6-5 is equivariance.
- The block is proper after the \(\Phi'\)-peel. The full development supplies the window and cap fields.
- HE7.A(2) specializes to HE6.A:

  \[
  |S_{\lambda,r}|=D'\ell\deg r,
  \qquad
  (e,f)=(e_1\ell,f_1\deg r).
  \]

The HE6 record is the first literal witness that a fractional-height test requires neither a ramified base change nor a complete-DVR quotient.

### S3.3 INSTANCE HE7 + HE6R1 — level two

**Source pin:** S0.1(3).

Given a level-one label \((\lambda,r)\), with \(\lambda=u/\ell>D'h\) and \(d_r=\deg r\):

- \(K_{\mathcal C}=K_2=K[Z]/(r)=K(\beta)\);
- \(\Phi=\Psi_{\lambda,r}\), monic of degree

  \[
  D=D''=D'\ell d_r,
  \]

  with **no irreducibility premise**;

- \(d=dv_2=\ell\,dv\), \(T=T_2=\ell d_ru\);
- `Pt` is the level-two point class and \(\iota_\xi=\iota_\xi^{(2)}\);
- \(n=n_2\), with \(n_2(k)=\varpi^{m(k)}{\Phi'}^{s(k)}\);
- `(SLOT)` is `(SLOT₂)`;
- `(LIFT)` is `(LIFT₂)` on `(FULL2)`, with `(FULL2-U)` as the uniform sufficient domain;
- `(COC)` is the real \(\beta^c\) twist `(BETA)`;
- the test family is HE7-3 with its inverse-twisted coefficient prescription;
- the block is the Galois-stable factor \(f_S\);
- HE6R1-2 projects the \(>T_2\) hull, lengths, and residual factors from \(f\);
- HE6R1-3 and the later gcd dichotomy supply the peel;
- HE7-12 supplies `WindowSafe` and `CapSafe` after above-line key perturbations;
- HE7-13 and HE7-8 supply refine progress and termination;
- HE7-13′ supplies the mandatory per-class reading at mixed residuals;
- the widened branch predicate is

  \[
  \ell_2\deg r_2=1
  \quad\text{versus}\quad
  \ell_2\deg r_2\ge2.
  \]

HE7.A becomes the original level-two statement:

\[
|S_{\lambda_2,r_2}|=D''\ell_2\deg r_2,
\qquad
e=e_1\ell\ell_2,
\qquad
f=f_1d_r\deg r_2.
\]

**First-gate result.** Every field above is constructible without proving `Irreducible Ψ`. The only irreducibility used is that of residual labels \(r\) and \(r_2\), which makes their residue extensions fields and their power bases independent.

Therefore this instance generates no `keyIrreducible` obligation. If formal elaboration generates one, the carrier is wrong.

### S3.4 INSTANCE HETOW — full inner tower sides

**Source pin:** S0.1(4).

For a full tower side with data \((e_2,f_2,u_2,\psi_2)\):

- the current field is \(K_2\cong\mathbf F_{Q^{f_1f_2}}\);
- the key is the **wrap-corrected** composed key \(\Phi_2\), monic of degree

  \[
  D_2=D'e_2f_2;
  \]

- HETOW-2 identifies \(\Phi_2\) with a genuine HE6-family key, literally in the reduced `(LIFT)` form, or with an allowed above-line perturbation;
- \(d=dv_2=e_1e_2v\), \(T=T_2=e_2f_2u_2\);
- `Pt` is the tower-node locus;
- HETOW-1 transports its letter to

  \[
  \beta=\eta^{-Q(u_2)}\eta_2
  \]

  and defines \(\widetilde r\) as its minimal polynomial;
- the coherent normalizer is HE7’s \(n_2\);
- the tower-print normalizer \(\widehat n_2\) is connected by HETOW-4.

Per-height residues are related by

\[
\tau(k)=\eta^{-Q(m(k))},
\]

but are not declared equal. On an assembled side,

\[
R_{\lambda_2}(Z)
=
\tau(H_0)\,\widehat R_{\lambda_2}(Z/\delta),
\qquad
\delta=\tau(u_3)\in K^\times.
\]

This is the `(FRAME)` bridge. It preserves separability, factor degrees, multiplicities, the product branch, and the refined polynomial.

The full-side identity gives \(f_S=f\). If \(\Phi_2\mid f\), the HE6R1-3 peel runs first.

`WindowSafe` and `CapSafe` are HETOW-2’s corrected-key and carry audit. The tower print’s attained-origin shift is recorded through `(ORIGIN)`; its \(z^\nu\) factor is removed before factor comparison.

The output dictionary is

\[
e=e_1e_2\ell_2,
\qquad
f=f_1f_2\deg r_2,
\]

exactly HETOW.A. The instance does not claim that raw tower-print coefficients equal coherent coefficients.

### S3.5 INSTANCE GENTOW4 — partial inner sides, per block

**Source pin:** S0.1(5).

For a partial tower side, the carrier fields are those of HETOW, with these block-specific fields:

- the wrap-corrected \(\Phi_2\), \(K_2\), \(dv_2\), \(T_2\), point class, and normalizer bridge are supplied by GENTOW-4.1 through the corrected HETOW interfaces;
- the level-one label classes form a bouquet

  \[
  f=\prod_{(\kappa,r)}f_{\kappa,r};
  \]

- for the selected class,

  \[
  F=f_S=f_{\kappa,r};
  \]

  no whole-polynomial monic-of-length-\(\mu_2\) hypothesis is fabricated;

- HE6R1-2 gives a constant

  \[
  c_g=dv_2(g(\xi)),
  \qquad
  g=f/f_S,
  \]

  and identifies the \(>T_2\) hull of \(f\) with the hull of \(f_S\) translated by \(c_g\);

- consequently,

  \[
  \mu_2^*
  =
  \sum_{\lambda_2>T_2}L_{\lambda_2}(f),
  \qquad
  \deg f_S=D_2\mu_2^*;
  \]

- per-side residuals agree only up to the fixed nonzero scalar and coherent cocycle unit supplied by pin-height normalization;
- `WindowSafe` is the projection identity on the selected initial hull;
- `CapSafe` is the partial-side cap and collection certificate: sibling terms cannot create a face below the selected \(>T_2\) segment;
- the origin and canonical-frame fields carry the \(c_g\)-shift, \(w\)-rescaling, and any \(Y^\nu\) raw origin separately;
- parity and residual decisions are made after subtracting \(c_g\), not from raw \(f\)-pins;
- mixed sides are read per block as required by HE7-13′;
- the unproved equality between level-one residual multiplicity and projected block length is not assumed: \(\mu_2^*\) is computed from the projected hull.

HE7.A yields GENTOW-4.A’s per-block dictionary

\[
e=e_1e_2\ell_2,
\qquad
f=f_1f_2\deg r_2,
\]

and \(\sigma(f)\) is the disjoint union over the bouquet plus peels.

The count-side mixed-multiplicity tie and partial-side budget laws remain outside this σ-decision instance.

## S4. LEAN SIGNATURE SKETCH

```lean
universe uO uK uκ uΩ

open Polynomial

/-- The DVR is always the original coefficient ring. -/
class CompleteDVRData
    (O : Type uO) (K₀ : Type uK) (k₀ : Type uκ) where
  valuation   : K₀ → WithTop ℤ
  uniformizer : O
  residue     : O →+* k₀
  complete    : Prop
  isComplete  : complete

structure SigmaLadderCarrier
    (O : Type uO) (K₀ : Type uK)
    (k₀ Kres : Type uκ) (Ω : Type uΩ)
    [CommRing O] [Field K₀] [Field k₀] [Field Kres] where
  dvr             : CompleteDVRData O K₀ k₀

  key             : Polynomial O
  keyMonic        : key.Monic
  keyDegree       : ℕ
  keyDegree_pos   : 0 < keyDegree
  key_degree_eq   : key.natDegree = keyDegree
  -- Deliberately no `Irreducible key`.

  threshold       : ℤ
  point           : Ω → Prop
  residueEmbed    : ∀ ξ, point ξ → Kres →+* Ω

  normalizer      : ℤ → RationalFunction K₀
  normalizer_zero : normalizer 0 = 1
  normalizerValue : ∀ k, Prop

  slotValue       : Polynomial O → ℤ
  slotDigit       : Polynomial O → Kres
  slotExact       :
    ∀ A ξ, A ≠ 0 → A.natDegree < keyDegree → point ξ → Prop
  slotResidue     :
    ∀ A ξ, A ≠ 0 → A.natDegree < keyDegree → point ξ → Prop
  slotLowerBound  : ∀ A ξ, Prop

  fullHeight      : ℤ → Prop
  lift            : ∀ k, fullHeight k → Kres → Polynomial O
  lift_degree     :
    ∀ k hk c, (lift k hk c).natDegree < keyDegree
  lift_value      :
    ∀ k hk c, c ≠ 0 → slotValue (lift k hk c) = k
  lift_digit      :
    ∀ k hk c, slotDigit (lift k hk c) = c
  lift_zero       :
    ∀ k hk, lift k hk 0 = 0

  cocycle         : ℤ → ℤ → Kresˣ
  cocycle_normal  :
    ∀ a, cocycle 0 a = 1 ∧ cocycle a 0 = 1
  cocycle_law     :
    ∀ a b c,
      cocycle a b * cocycle (a + b) c =
      cocycle b c * cocycle a (b + c)

structure SigmaBlock
    {O K₀ k₀ Kres Ω}
    [CommRing O] [Field K₀] [Field k₀] [Field Kres]
    (C : SigmaLadderCarrier O K₀ k₀ Kres Ω) where
  poly             : Polynomial O
  monic            : poly.Monic
  separable        : Discriminant poly ≠ 0

  multiplicity     : ℕ
  multiplicity_pos : 0 < multiplicity
  degree_eq        :
    poly.natDegree = multiplicity * C.keyDegree

  coeff            : Fin multiplicity → Polynomial O
  development      : Prop
  coeff_degree     :
    ∀ j, (coeff j).natDegree < C.keyDegree

  proper           : ¬ C.key ∣ poly
  rootsArePoints   : Prop
  aboveThreshold   : Prop

  occupiedHeights  : Finset ℤ
  liftHeights      : Finset ℤ
  occupied_spec    : Prop
  lift_domain      :
    ∀ k, k ∈ liftHeights → C.fullHeight k

  windowSafe       : Prop
  capSafe          : Prop
  window_ok        : windowSafe
  cap_ok           : capSafe

  frameBridge      : Prop
  frameBridge_ok   : frameBridge
  originShift      : ℕ
  originBridge     : Prop

  testFamily       : BaseChangeFreeTestFamily C poly
  stepData         : SigmaStepData C poly
  step_wf          : WellFounded stepData.next

structure HE7AResult
    {O K₀ k₀ Kres Ω}
    [CommRing O] [Field K₀] [Field k₀] [Field Kres]
    (C : SigmaLadderCarrier O K₀ k₀ Kres Ω)
    (B : SigmaBlock C) : Prop where
  slopes_gt_threshold       : Prop
  side_lengths_sum          : Prop
  separable_factor_classes  : Prop
  repeated_linear_refines   : Prop
  repeated_non_linear_jumps : Prop
  mixed_residuals_per_block : Prop
  recursion_terminates      : Prop

theorem HE7_A_master
    {O K₀ k₀ Kres Ω}
    [CommRing O] [Field K₀] [Field k₀] [Field Kres]
    (C : SigmaLadderCarrier O K₀ k₀ Kres Ω)
    (B : SigmaBlock C) :
    HE7AResult C B := by
  sorry

theorem sigma_peel
    (hdiv : C.key ∣ B.poly) :
    PeelResult C B := by
  sorry
```

The signature deliberately makes `proper`, `lift_domain`, `windowSafe`, `capSafe`, `frameBridge`, `originBridge`, the test family, the mixed-block rule, and well-foundedness visible. None may be hidden in a proposition named only “valid tower block.”

## S5. HONESTY LEDGER

### S5.1 Scope and grade

This note proves a **composition theorem**: the common original-\(O\) interface is sufficient for one HE7.A proof, and each of the five pinned sources maps to it. It does not re-prove the suppliers’ local calculations, rerun their batteries, or upgrade a documentary grade.

The consumption grade of an instance is

\[
\operatorname{grade}(I)=
\min(g_{\mathrm{master}},g_{\mathrm{carrier}},g_{\mathrm{frame}},
g_{\mathrm{local}}).
\tag{GRADE}
\]

This new master is at attempt grade \(0/2\); therefore every composed instance is currently \(0/2\), even when its suppliers are accepted.

Source-status reading at supplied HEAD:

- HE6 is accepted \(2/2\), with its 2026-08-12 normalized-slot corrections consumed.
- HE7 is accepted \(2/2\) with its annex stack and dated corrections; this note consumes corrected HE7-2′ and HE7-13′.
- HE6R1 is accepted \(2/2\), with its jump bound re-displayed by stage-rooted versus ambient-rooted histories. Its separate `GENHN-ERR-1` count-side proof unit is not used by HE7.A.
- HETOW is accepted \(2/2\); HETOW-4 is essential here.
- GENTOW4 is accepted \(2/2\); its mixed multiplicity tie and count budgets remain boxed and are not imported.
- HE3 is consumed at the grade stated by its supplied HEAD. In any event, `(GRADE)` prices this T2 note at \(0/2\).

### S5.2 Explicit exclusions

The master does **not** claim:

- a complete-DVR structure on \(O[x]/(\Phi)\);
- irreducibility of the current key;
- all-height lift surjectivity;
- equality of literal residual coefficient arrays across frames;
- the multiplicity-weighted product formula at mixed blocks;
- partial-side budget or density laws;
- machine coverage outside the axes named by suppliers;
- acceptance of this composition before its own hostile arc.

## S6. TEN CHANGES FROM THE BLUEPRINT

Exactly ten changes are made relative to the pre-probe blueprint.

1. **Original-\(O\) carrier.** The complete DVR is the original coefficient ring, never a quotient stage ring.

2. **Monic key only.** `keyMonic` and degree replace every implicit `keyIrreducible` field.

3. **Pointwise transport is explicit.** `Pt` and \(\iota_\xi:K\hookrightarrow\overline k\) are carrier fields.

4. **Slot data is normalized.** The digit is \(\gamma_k(A)\), not a bare coefficient-residue sum, and the \(\eta^{-q(k)}\) HE6 seam is explicit.

5. **Lift domains are finite obligations.** `Full`, \(H_{\mathrm{occ}}\), \(H_{\mathrm{lift}}\), and `(OCC)` replace a universal all-height lift axiom.

6. **Cocycles are structural.** The coherent frame carries \(\tau\), HE7’s genuine \(\beta^c\), and deeper letter monomials; inverse twists are part of test construction.

7. **Perimeter certificates are fields.** `Proper`, `WindowSafe`, `CapSafe`, and the separate peel replace the phrase “arising as a label.”

8. **Frame and origin are separated.** The \(w\)-rescaling, multiplicative/coherent conversion, \(c_g\)-translation, and \(Y^\nu/z^\nu\) origin bridge are independent records.

9. **Tests stay over \(O\), and repeated branches use the product.** The family is base-change-free, refinement splits on \(e'\deg r'\), and mixed residuals are handled per block.

10. **Termination and grades are data.** A well-founded step relation and `(GRADE)` replace prose termination and grade inheritance by implication.

## S7. FIVE-HAZARD CLOSURE

| Hazard | Verdict | Closing data |
|---|---|---|
| Hypothesis migration | **Closed for composition** | `Proper`, `Window`, `(OCC)`, tests, frame/origin bridges, and well-foundedness are visible. |
| Instance-strength collapse | **Closed** | The key is monic only; lifts exist only on `Full`; repeated branches split on \(e'\deg r'\). |
| Hidden perimeter enlargement | **Closed** | `WindowSafe` and `CapSafe` are instance obligations. Multiplicativity is required only on consumed coherent ladder monomials. |
| Convention seam | **Closed** | `(GAMMA)`, `(HE6-SEAM)`, `(BETA)`, `(FRAME)`, `(ORIGIN)`, HETOW-4, and \(c_g\)-translation normalize every comparison. |
| Grade laundering | **Closed for composition, open for acceptance** | `(GRADE)` takes the meet of master, carrier, frame, and local grades. |

No hazard blocks composition. Acceptance remains a separate arc.

## S8. ARC PLAN AND FILE-LEVEL GATES

The T2 arc consists of two fresh hostile passes on the post-composition text. A repair at gap-or-worse resets the clean count.

The first pass runs these gates in order:

1. **First gate — HE7 obligation shape.** Elaborate the HE7 + HE6R1 instance against `SigmaLadderCarrier`. Generated goals must contain `keyMonic`, slot, lift-domain, cocycle, block, frame, test, and well-foundedness obligations, and must contain **no** `keyIrreducible` obligation. Any such obligation is an immediate structural failure.

2. **HE6 seam gate.** Check that the carrier digit is \(\gamma_k(A)\) with normalized coefficients and that the \(\varpi^k\)-read is exactly

   \[
   \iota(\gamma_k(A))\eta^{-q(k)}.
   \]

3. **HE7 cocycle gate.** Force a live carry and verify that assembled residuals include \(\beta^c\). Dropping it must change the designated bad-twist witness.

4. **HETOW frame gate.** Compare \(n_2\) and \(\widehat n_2\) only after bracket assembly. Verify the global-unit/variable-rescale formula, a non-geometric raw per-height string, and a nonzero origin shift \(\nu\).

5. **GENTOW4 perimeter gate.** On a partial side, verify the projected \(>T_2\) hull, \(c_g\)-translated pins, per-block residual factors, cap safety, and refusal of the full-side reader. Do not consult the boxed mixed multiplicity tie.

Pass 2 attacks a disjoint surface:

- reducible keys and peels;
- sub-threshold lift refusal;
- mixed residual bouquets with two repeated classes;
- a deep cocycle;
- proxy/window caps;
- a nonzero raw-origin shift.

Acceptance requires both passes clean under the repository’s bar.

## S9. FINAL COMPOSITION VERDICT

**S-6 GO.** HE7.A has one carrier over the original complete DVR \(O\), one proof, and five literal pinned instances.

The master makes:

- no complete-DVR quotient assumption;
- no current-key irreducibility assumption;
- no all-height lift assumption;
- no raw-frame coefficient-invariance claim.

HE6 enters through \(\gamma_k(A)\eta^{-q(k)}\). HE7 enters with the real \(\beta^c\) twist. HETOW and GENTOW4 enter through explicit coherent-frame, origin, window, cap, and block-projection records.

The first formal gate is decisive:

\[
\boxed{\text{The HE7 instance must generate no `keyIrreducible` obligation.}}
\]

If it does, the carrier abstraction is rejected before any proof or acceptance claim is considered.


---

## r1 (2026-08-12): arc repairs (T2P1 1C + 5G)

*(gpt-5.6-sol high, runs/comp5/T2R1_output.log; transcribed unaltered; counter resets.)*

The minimal honest r1 cannot preserve the current “GO / five literal instances / first gate passed” language. The following six repairs close the reported defects without assuming key irreducibility or changing the coefficient DVR.

### R1-1 — C1: replace the invalid peel dichotomy

Replace S1.5(3), S2.1, and every “after the \(\Phi\)-peel” reference with:

> **Key-boundary condition.** For a block to enter HE7.A, require
>
> \[
> \boxed{
> \gcd_{K_0[x]}(F_{K_0},\Phi_{K_0})=1.}
> \tag{KEY-FREE}
> \]
>
> The weaker condition \(\Phi\nmid F\) is not sufficient when \(\Phi\) is reducible.
>
> A non-key-free input must first carry a **key-boundary certificate**. Writing
>
> \[
> G=\operatorname{monicGCD}_{K_0[x]}(F_{K_0},\Phi_{K_0}),
> \]
>
> that certificate supplies:
>
> 1. monic polynomials \(P_i\in O[x]\) whose images in \(K_0[x]\) are the distinct irreducible factors of \(G\) occurring in \(F\);
> 2. the corresponding Galois-orbit, irreducibility, and local \((e,f)\) certificates for every \(P_i\);
> 3. zero or more residual blocks \(B_j\), each satisfying `(KEY-FREE)` and every other hypothesis of HE7.A;
> 4. the product identity
>
>    \[
>    F=\prod_i P_i\prod_j B_j.\operatorname{poly},
>    \]
>
>    together with disjointness and exhaustion of the associated root classes; and
> 5. strict degree descent for every nonterminal residual block.
>
> Since \(F\) is separable, the \(P_i\) occur simply. No assertion is made that \(G\) equals \(\Phi\), that \(\Phi\) is one irreducible factor, that the peel decreases \(\mu\) by one, or that it fires at most once.
>
> **LEMMA T2.KEY-BOUNDARY.** Apply HE7.A separately to the certified `(KEY-FREE)` blocks and adjoin the certified factors \(P_i\). The resulting factors exhaust \(F\).
>
> This lemma requires no `Irreducible Φ` hypothesis. Irreducibility is required only for each emitted orbit factor \(P_i\), as part of the key-boundary certificate.

In `SigmaBlock`, replace

```lean
proper : ¬ C.key ∣ poly
```

by the mapped-polynomial coprimality certificate

```lean
keyCoprime : IsCoprime (poly.map C.ground.inclusion)
                         (C.key.map C.ground.inclusion)
```

Delete `sigma_peel`; replace `PeelResult` by the explicit key-boundary result described above.

### R1-2 — G1: make the first gate honest and inspectable

Replace “First-gate result” and S8(1) with:

> **First-gate status (r1): NOT YET RUN.** The prose schema contains no `keyIrreducible` field, but that is not an elaboration result. A first-gate pass exists only after the following declarations and an HE7 constructor term have elaborated:
>
> - the original-ground DVR record;
> - `SigmaLadderCarrier`;
> - `SigmaBlock`, including `(KEY-FREE)`;
> - the side-accounting certificate;
> - the complete test-family certificate;
> - mixed-block step data;
> - the well-founded recursion data; and
> - the key-boundary result.
>
> The constructor-generated obligation manifest must contain exactly the following groups:
>
> 1. original-\(O\) ground, fraction-field, valuation, residue, and completeness obligations;
> 2. `keyMonic`, positive degree, and degree equality;
> 3. inherited \(e_{\mathcal C}\) and \(f_{\mathcal C}\);
> 4. point, embedding, normalizer, slot, lift-domain, and cocycle obligations;
> 5. development, `(KEY-FREE)`, roots, window, cap, frame, and origin obligations;
> 6. finite occupied- and lift-height sets with `(OCC)`;
> 7. side accounting and complete test certificates;
> 8. mixed-block transition and `step_wf`; and
> 9. the key-boundary certificate when the input is not key-free.
>
> It may require `Irreducible r` for residual labels and `Irreducible P_i` for emitted boundary factors. It must not require `Irreducible C.key`.
>
> Until an elaborated constructor and its generated goals are recorded, this note claims only that the proposed interface does not visibly request `keyIrreducible`; it does not claim that the first gate has passed.

The previously opaque declarations must expose, at minimum, these fields:

```text
BaseChangeFreeTestFamily:
  test polynomial; integrality; monicity; degree;
  root disk/label equivalence; local e- and f-forcing;
  nonemptiness; disjointness; side exhaustion;
  Galois equivariance.

SigmaStepData:
  state type; next relation; linear-refine transition;
  child-jump transition; mixed-block transition;
  degree/mass/secondary-budget decrease certificates.

KeyBoundaryResult:
  common-factor list; irreducibility and orbit certificates;
  residual block list; product/root-partition certificate;
  local invariants; strict degree descent.
```

None of these declarations may contain `Irreducible C.key`.

### R1-3 — G2: replace every informal span with paired anchors

Insert marker-only lines immediately before and after each cited source unit, and replace all informal pins by:

```text
:: «<!-- T2PIN:<NAME>:BEGIN -->»
..< «<!-- T2PIN:<NAME>:END -->»
```

Use these unique names:

```text
HE3-DEF1
HE3-HE3-1L
HE3-HE3-6
HE3-R8-2
HE3-R8-3
HE3-R8-4
HE3-R8-5
HE6-SLOT-SEAM
HE7-MIXED-13P
HE7-COCYCLE-2P-THROUGH-R1D
HETOW-NORMALIZER-4
GENTOW-ACCEPTANCE-FOLD
```

Replace the HE6 inclusive `..` by `..<`. Delete the phrases “ending after its wiring paragraph and three bullets,” “ending with its proof,” and every begin-only pin.

Add:

> A source pin is valid only when both named markers occur exactly once and the begin marker precedes the end marker. Marker insertion changes no mathematical source text. Until every pair exists, the corresponding instance fails closed.

### R1-4 — G3: remove undeclared generic tests from the proof

Add to `SigmaBlock`:

> **Side-accounting certificate.** The block supplies a certificate, in the coherent frame, that:
>
> \[
> \lambda>T,\qquad
> \sum_\lambda L_\lambda=\mu,\qquad
> |S_\lambda|=D L_\lambda
> \]
>
> for every consumed side \(\lambda\). The certificate records its finite side set and the root partition inducing the final equality.

Replace the first three substantive paragraphs of the proof of HE7.A with:

> `(SLOT)` and `(COC)` identify the coherent coefficient pins and residual polynomials. The side-accounting certificate gives clause 1 and the total cardinality \(DL_\lambda\) of each side class.
>
> For a separable side residual, the test-family certificate supplies nonemptiness, disjointness, exhaustion, Galois equivariance, and local forcing for each irreducible residual factor. Local forcing gives the lower bound \(De'\deg r'\). Since the classes exhaust the side and their lower bounds sum to the certified side total, equality holds termwise; each class is one Galois orbit.
>
> No generic test factor, \(\rho\)-side equality/strictness theorem, or resultant-symmetry theorem is invoked by the master proof. If an instance derives its side-accounting or nonemptiness certificate using those tools, they belong to that instance’s certificate proof, not to the master interface.

Add to the honesty ledger:

> HE7.A is an interface-composition theorem. Side accounting, nonemptiness, and exhaustion are explicit inputs, not outputs newly proved by the abstract master.

### R1-5 — G4: complete the record shape and retract premature instance claims

Add to `SigmaLadderCarrier`:

```lean
inheritedE       : ℕ
inheritedF       : ℕ
inheritedE_pos   : 0 < inheritedE
inheritedF_pos   : 0 < inheritedF
```

Add to `SigmaBlock`:

```lean
sideAccounting    : SideAccountingCertificate C poly
originBridge_ok   : originBridge
mixedBlockRule    : MixedBlockCertificate C poly
keyBoundary       : Option (KeyBoundaryCertificate C poly)
```

Replace the opening of S3 with:

> ## S3. FIVE CANDIDATE INSTANCE OBLIGATION RECORDS
>
> The following subsections are source-routing ledgers, not yet Lean instances. A literal instance exists only when the repository contains named elaborated terms
>
> ```text
> <name>.carrier
> <name>.block
> <name>.sideAccounting
> <name>.testFamily
> <name>.stepData
> <name>.step_wf
> <name>.keyBoundary
> ```
>
> and a constructor check records their generated obligations.
>
> Each record must instantiate, without prose inheritance: the original ground token; \(e_{\mathcal C},f_{\mathcal C}\); finite occupied and lift-height sets; `(OCC)`; normalizer and cocycle laws; slot and lift laws; side accounting; complete tests; `(KEY-FREE)` or a key-boundary certificate; window, cap, frame, and origin bridges; the mixed-block rule; and `step_wf`.
>
> HETOW and GENTOW4 may transport these fields only through a typed transport certificate preserving each named field. “As in HE7,” “through HETOW,” and similar prose do not instantiate a field.

Rename the five subsection headings from `INSTANCE` to `CANDIDATE INSTANCE`. Replace every “literal instance” and “First-gate result” claim accordingly.

For HE6, a one-shot record may use the empty transition relation and its immediate well-foundedness proof. HETOW and GENTOW4 must use, respectively, a typed pullback and a typed restriction of the HE7 transition relation; well-foundedness then follows by inverse image or restriction, not by prose.

### R1-6 — G5: anchor every carrier to a genuine original DVR object

Replace `CompleteDVRData` by an ambient ground record containing, at minimum:

> An **original-DVR ground** \(\mathscr O\) contains:
>
> - the coefficient ring \(O\);
> - its fraction field \(K_0\);
> - an injective inclusion \(O\hookrightarrow K_0\);
> - an `IsFractionRing O K₀` witness;
> - an `IsDiscreteValuationRing O` witness;
> - the normalized valuation on \(K_0\) and its uniformizer compatibility;
> - identification of the residue field with \(k_0\); and
> - completeness of \(K_0\) for the topology induced by that valuation.
>
> `SigmaLadderCarrier` is parameterized by a fixed \(\mathscr O\); it does not contain a replaceable DVR field. Every child carrier, test family, block, lift, and polynomial remains parameterized by the same \(\mathscr O\). A stage order or quotient may occur only in optional auxiliary data and cannot occupy the ground slot.

The signature header becomes schematically:

```lean
structure OriginalDVRGround (O K₀ k₀ : Type*) := ...

structure SigmaLadderCarrier
    (G : OriginalDVRGround O K₀ k₀)
    (Kres Ω : Type*) where
  -- no independent `dvr` field
  ...
```

Add:

> Equality of the ground parameter is part of every carrier-transport and child-carrier constructor. Consequently a purported stage ring cannot replace \(O\) during recursion. This is the formal content of the original-\(O\) redline.

Finally replace S9 by:

> **R1 COMPOSITION VERDICT: HOLD.** The repaired conditional master uses one fixed original-\(O\) ground and no current-key irreducibility assumption. The reducible-key boundary is now an explicit gcd/orbit decomposition rather than a false divisibility dichotomy.
>
> The five source routes remain candidate obligation records until their paired source anchors, explicit constructors, field witnesses, and generated obligation manifests are present. No acceptance, literal-instance, or passed-first-gate claim is made by this r1 text.
