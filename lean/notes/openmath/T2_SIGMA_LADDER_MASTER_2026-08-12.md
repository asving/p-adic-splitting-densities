# T2 v2 — THE σ-LADDER MASTER: one original-\(O\) theorem and five span-pinned mathematical instances

**Unit:** T2 / σ-ladder master re-composition.  
**Date:** 2026-08-12.  
**Status:** mathematical composition draft, attempt grade \(0/2\).

This note states and proves one mathematical master theorem, HE7.A, over the original complete DVR \(O\). It records five source instances:

\[
\mathrm{HE3.A},\qquad
\mathrm{HE6},\qquad
\mathrm{HE7+HE6R1},\qquad
\mathrm{HETOW},\qquad
\mathrm{GENTOW4}.
\]

It contains no Lean signature, record declaration, or interface sketch. Formal encodings belong to the S-5 probe output and to stage 2 of the arc.

## S0. VERDICT, REDLINE, AND SOURCE PINS

### S0.1 Structural redline

**S-6 GO for mathematical composition.** The master carrier is defined over the original complete DVR \(O\). A stage order, integral closure, or quotient may appear as auxiliary instance data, but it never replaces \(O\) as coefficient ring or ground DVR.

The current key \(\Phi\in O[x]\) is required to be monic, with

\[
D=\deg\Phi>0.
\]

There is deliberately no hypothesis that \(\Phi\) is irreducible:

\[
\boxed{\Phi\text{ is monic; irreducibility is not assumed.}}
\tag{NO-IRR}
\]

This is essential for the level-two instance, whose key is the HE6 test polynomial

\[
\Psi_{\lambda,r}\in O[x].
\]

That polynomial is monic but is not assumed irreducible. Neither a complete-DVR structure on \(O[x]/(\Phi)\) nor irreducibility of \(\Phi\) may enter the master proof.

### S0.2 Marker-delimited span convention

Every cited source unit is bounded by a pair of marker-only lines

\[
\texttt{<!-- T2V2PIN:NAME:BEGIN -->},
\qquad
\texttt{<!-- T2V2PIN:NAME:END -->}.
\]

The corresponding pin is the half-open span beginning at the first marker and ending immediately before the second.

A pin is valid only if both markers occur exactly once in the named file and the begin marker precedes the end marker. Missing, repeated, or reversed markers cause the corresponding source route to fail closed. Marker insertion changes no mathematical source text.

The complete pin inventory is:

\[
\begin{array}{c|l}
\text{source}&\text{paired pin names}\\ \hline
\text{HE3}&
\begin{array}{l}
\texttt{HE3-A-STMT},\ \texttt{HE3-A-PROOF},\ \texttt{HE3-DEF1},\\
\texttt{HE3-HE3-1L},\ \texttt{HE3-HE3-6},\\
\texttt{HE3-R8-2},\ \texttt{HE3-R8-3},\
\texttt{HE3-R8-4},\ \texttt{HE3-R8-5}
\end{array}\\[2mm]
\text{HE6}&
\texttt{HE6-FAMILY},\ \texttt{HE6-PROOF},\ \texttt{HE6-SLOT-SEAM}\\[1mm]
\text{HE7}&
\begin{array}{l}
\texttt{HE7-A-STMT},\ \texttt{HE7-SLOT-TRANSFER},\\
\texttt{HE7-MIXED-13P},\
\texttt{HE7-COCYCLE-2P-THROUGH-R1D}
\end{array}\\[2mm]
\text{HE6R1}&
\texttt{HE6R1-1},\ \texttt{HE6R1-2},\ \texttt{HE6R1-3}\\[1mm]
\text{HETOW}&
\texttt{HETOW-LABELS},\ \texttt{HETOW-A},\
\texttt{HETOW-NORMALIZER-4}\\[1mm]
\text{GENTOW4}&
\begin{array}{l}
\texttt{GENTOW-4-1},\ \texttt{GENTOW-4-A},\\
\texttt{GENTOW-4-2},\ \texttt{GENTOW-ACCEPTANCE-FOLD}
\end{array}
\end{array}
\tag{PINS}
\]

These pins lie in:

\[
\begin{aligned}
&\texttt{lean/notes/openmath/HE3\_PROOF\_2026-08-08.md},\\
&\texttt{lean/notes/openmath/HE6\_PROOF\_2026-08-08.md},\\
&\texttt{lean/notes/openmath/HE7\_PROOF\_2026-08-08.md},\\
&\texttt{lean/notes/openmath/HE6R1\_RECON\_2026-08-08.md},\\
&\texttt{lean/notes/openmath/HETOW\_RECON\_2026-08-09.md},\\
&\texttt{lean/notes/openmath/GENTOW4\_PROOF\_2026-08-09.md}.
\end{aligned}
\]

No unpinned source material is used to manufacture a theorem hypothesis.

## S1. THE ORIGINAL-\(O\) σ-LADDER

### S1.1 Ground data and inherited invariants

Fix a complete DVR \(O\) with fraction field \(K_0\), uniformizer \(\pi\), finite residue field

\[
k_0=\mathbf F_Q,
\]

and normalized valuation \(v(\pi)=1\). Fix an algebraic closure \(\overline K_0\), the unique extension of \(v\) to \(\overline K_0\), an algebraic closure \(\overline k\) of \(k_0\), and the associated reduction maps on value-zero elements.

Every carrier occurring in the recursion uses this same \(O\), \(K_0\), valuation, and residue field. Child construction may enlarge a residue-label field, but it does not change the ground DVR.

A σ-ladder carrier has a finite extension

\[
k_0\hookrightarrow K,\qquad [K:k_0]<\infty,
\tag{FINITE-RES}
\]

and a monic key

\[
\Phi\in O[x],\qquad D=\deg\Phi>0.
\]

It also carries positive inherited ramification and residue invariants

\[
e_{\mathcal C}>0,\qquad f_{\mathcal C}>0,
\]

satisfying the compatibility relation

\[
\boxed{D=e_{\mathcal C}f_{\mathcal C}.}
\tag{DEG-EF}
\]

This equality is an explicit mathematical hypothesis. It is not inferred from monicity.

The carrier has an integer-normalized value \(d\), an inherited threshold \(T\in\mathbf Z\), and a class of points

\[
\operatorname{Pt}\subseteq\overline K_0.
\]

Every \(\xi\in\operatorname{Pt}\) has a \(k_0\)-embedding

\[
\iota_\xi:K\hookrightarrow\overline k,
\qquad
\iota_\xi|_{k_0}=\operatorname{id}_{k_0}.
\tag{RES-COMP}
\]

Valuations and polynomial evaluations take place in \(\overline K_0\); residual digits and embeddings take place in \(\overline k\). These two ambient fields are never identified.

### S1.2 Exact slots

For every nonzero \(A\in O[x]\) with \(\deg A<D\), the carrier assigns

\[
h(A)\in\mathbf Z,
\qquad
\operatorname{dig}(A)\in K^\times,
\]

such that, for every \(\xi\in\operatorname{Pt}\),

\[
d(A(\xi))=h(A)
\tag{SLOT-V}
\]

and

\[
\operatorname{res}\!\left(
\frac{A(\xi)}{n(h(A))(\xi)}
\right)
=
\iota_\xi(\operatorname{dig}(A)).
\tag{SLOT-R}
\]

Here \(n(h(A))(\xi)\) has the same value as \(A(\xi)\), so the quotient is a value-zero element and its residue is defined.

When total notation is useful, set

\[
h(0)=+\infty,\qquad \operatorname{dig}(0)=0.
\]

Outside \(\operatorname{Pt}\), only the lower bounds supplied by the preceding-key development are asserted. No exact slot formula is claimed at arbitrary points of \(\overline K_0\).

At level one, for

\[
A=\sum_{j<D'}a_jx^j,\qquad k=dv(A),
\]

let \(0\le i<e_1\) be the unique residue class satisfying

\[
ih\equiv k\pmod{e_1}.
\]

The coherent digit is

\[
\boxed{
\gamma_k(A)=
\sum_{\substack{t\ge0\\i+e_1t<D'}}
\operatorname{res}\!\left(
a_{i+e_1t}
\pi^{-(k-(i+e_1t)h)/e_1}
\right)\eta^t.}
\tag{GAMMA}
\]

Terms strictly above height \(k\) contribute zero. Thus the HE6 carrier has

\[
\operatorname{dig}(A)=\gamma_k(A).
\]

When the HE6 print frame divides by \(\varpi^k\) rather than by the coherent normalizer \(n(k)\), the correct conversion is

\[
\boxed{
\operatorname{res}\!\left(
\frac{A(\xi)}{\varpi(\xi)^k}
\right)
=
\iota_\xi(\gamma_k(A))\,\eta_\xi^{-q(k)}.}
\tag{HE6-SEAM}
\]

The coefficient normalizers inside \(\gamma_k(A)\) and the negative sign on \(q(k)\) are mandatory.

### S1.3 Normalizers and the actual cocycle

The carrier has exact-height normalizers

\[
n:\mathbf Z\longrightarrow K_0(x)^\times,
\qquad
n(0)=1,
\]

such that

\[
d(n(k)(\xi))=k
\]

for every \(k\) used by the construction and every \(\xi\in\operatorname{Pt}\).

Normalizers may be Laurent polynomials or rational functions. Integrality is required of the constructed lifts and test polynomials, not of the auxiliary functions used to read residues.

The cocycle is not independent data. It is defined from the normalizers by

\[
\boxed{
\tau_\xi(a,b)
=
\operatorname{res}\!\left(
\frac{n(a)(\xi)n(b)(\xi)}
     {n(a+b)(\xi)}
\right).}
\tag{COC-DEF}
\]

The carrier hypotheses say that this residue is the image under \(\iota_\xi\) of an element

\[
\tau(a,b)\in K^\times
\]

independent of \(\xi\). Hence

\[
\tau(0,a)=\tau(a,0)=1
\]

and

\[
\tau(a,b)\tau(a+b,c)
=
\tau(b,c)\tau(a,b+c).
\tag{COC}
\]

Every residual product in the coherent frame includes these cocycle factors.

For a next-step numerator \(u\), put

\[
\vartheta_s=
\operatorname{res}\!\left(\frac{n(u)^s}{n(su)}\right),
\qquad
\Theta_s=\vartheta_s^{-1}.
\]

At HE7 level two,

\[
n_2(k)=\varpi^{m(k)}{\Phi'}^{s(k)},
\qquad
\ell m(k)+s(k)u=k,
\qquad
0\le s(k)<\ell,
\]

and

\[
\frac{n_2(k)n_2(k')}{n_2(k+k')}
=
\left(\frac{{\Phi'}^\ell}{\varpi^u}\right)^c,
\qquad
c=\frac{s(k)+s(k')-s(k+k')}{\ell}.
\]

Its residue is therefore the genuine twist

\[
\boxed{\tau(k,k')=\beta^c.}
\tag{BETA}
\]

It is not replaced by \(1\). At deeper levels the same construction gives a monomial in all preceding residual letters.

### S1.4 Full heights and legal lifts

The carrier specifies which integer heights are full. At a full height \(k\), every digit \(c\in K\) has an integral lift

\[
L_k(c)\in O[x],\qquad \deg L_k(c)<D,
\]

such that

\[
L_k(0)=0
\]

and, for \(c\ne0\),

\[
h(L_k(c))=k,
\qquad
\operatorname{dig}(L_k(c))=c.
\tag{LIFT}
\]

For each theorem block \(B\), let

\[
H_{\mathrm{occ}}(B),\qquad H_{\mathrm{lift}}(B)
\]

be finite sets containing, respectively, all coefficient heights read by the proof and all heights at which a new digit is constructed. The visible domain obligation is

\[
\boxed{
H_{\mathrm{lift}}(B)
\subseteq
\{k:k\text{ is full}\}.}
\tag{OCC}
\]

There is no all-height lift hypothesis.

For HE6,

\[
k\text{ is full}
\Longleftrightarrow
k\ge(i(k)+e_1(f_1-1))h,
\]

and \(k\ge(D'-1)h\) is uniformly sufficient.

For HE7 level two, a sufficient condition is

\[
m(k)\ge(d_r-1)u+(D'-1)h,
\tag{FULL2}
\]

with uniform sufficient bound

\[
k\ge(\ell d_r-1)u+\ell(D'-1)h.
\tag{FULL2-U}
\]

### S1.5 Key-free blocks, hulls, and residuals

A σ-block consists of a monic separable polynomial \(F\in O[x]\), an integer \(\mu\ge1\), and a \(\Phi\)-development

\[
F=\Phi^\mu+\sum_{j<\mu}A_j\Phi^j,
\qquad
\deg A_j<D,
\qquad
\deg F=\mu D.
\tag{DEV}
\]

Its roots form a designated Galois-stable class contained in \(\operatorname{Pt}\).

Because \(\Phi\) may be reducible, the correct boundary condition is not merely \(\Phi\nmid F\). A block entering HE7.A must satisfy

\[
\boxed{
\gcd_{K_0[x]}(F,\Phi)=1.}
\tag{KEY-FREE}
\]

In particular, \(A_0\ne0\), so the lower hull of the points

\[
(j,h(A_j)),\qquad 0\le j\le\mu,
\]

runs from abscissa \(0\) to abscissa \(\mu\). Denote this lower hull by \(P\). Its side lengths therefore satisfy

\[
\sum_{\lambda\in\operatorname{Sides}(P)}L_\lambda=\mu.
\tag{HULL-LENGTH}
\]

Every root \(\rho\) of \(F\) satisfies the finite window condition

\[
T<d(\Phi(\rho))<\infty.
\tag{WINDOW}
\]

Any proxy, truncated, or tower-print development used by an instance must agree with the full development on every lower-hull side under consideration. In addition, omitted terms, collected terms, and key carries must lie strictly above those sides. These are the mathematical `WindowSafe` and `CapSafe` assertions; they are not inferred merely from the phrase “arising from a label.”

Let \(\lambda=u'/e'\) be a side slope in lowest terms. After removal of any raw-origin factor, its coherent normalized residual polynomial satisfies

\[
R_\lambda(Y)
=
\prod_{r'}r'(Y)^{m_{\lambda,r'}},
\tag{RES-FACT}
\]

where the product is over distinct monic irreducible polynomials in \(K[Y]\). Its degree and the side length are related by

\[
\boxed{
\deg R_\lambda=\frac{L_\lambda}{e'},
\qquad
e'\sum_{r'}m_{\lambda,r'}\deg r'=L_\lambda.}
\tag{RES-DEG}
\]

This displayed identity is part of the Newton-side calculation. It is the degree bridge used in the orbit count.

### S1.6 Frame and origin changes

The master uses the coherent normalizer frame: every pin is divided by the normalizer of its total height, and every cocycle bracket is included in residual assembly.

If a source uses a multiplicative or print normalizer, the comparison has the form

\[
\Gamma_s=c_s^{\mathrm{mult}}\vartheta_s,
\qquad
R_{\mathrm{can}}(Y)=w^mR_{\mathrm{mult}}(Y/w)
\tag{FRAME}
\]

for a fixed \(w\in K^\times\).

If the source’s first attained grid point is

\[
s_{\mathrm{act}}=s_{\min}+\nu e,
\]

then

\[
\boxed{
R_{\mathrm{raw}}(Y)=Y^\nu aR_{\mathrm{norm}}(bY)}
\tag{ORIGIN}
\]

for fixed \(a,b\in K^\times\). The factor \(Y^\nu\) is recorded and removed before the normalized residual is factored.

Frame changes preserve factor degrees, multiplicities, separability, and transported root classes. Literal coefficient strings are not asserted to be invariant.

### S1.7 Test polynomials and quantitative side accounting

For every side \(\lambda=u'/e'\) and every monic irreducible factor \(r'\) of \(R_\lambda\), the carrier supplies a monic polynomial

\[
\Psi_{\lambda,r'}\in O[x],
\qquad
\deg\Psi_{\lambda,r'}=De'\deg r'.
\tag{TEST}
\]

The test polynomial is not assumed irreducible.

Its proved properties are:

1. its roots lie in the intended disk and carry the label defined by \(r'\);

2. for roots of \(F\), its generic evaluation value is attained away from that label class and rises strictly on that class;

3. resultant symmetry makes the target class nonempty;

4. the classes associated with the distinct \(r'\) are disjoint and exhaust the roots belonging to the side;

5. the label construction is Galois equivariant;

6. every point in the \(r'\)-class has local invariants divisible by

   \[
   e_{\mathcal C}e',
   \qquad
   f_{\mathcal C}\deg r';
   \]

7. all tests and coefficient lifts remain in \(O[x]\).

Passing from \(K\) to \(K[Y]/(r')\) enlarges only the finite residue-label field. It does not base-change \(O\).

The test argument also supplies the quantitative Newton accounting identity. If

\[
w_\rho=d(\Phi(\rho))
\]

for the roots \(\rho\) of \(F\), counted with multiplicity, then, for every rational \(\kappa>T\) outside the finite set of critical values,

\[
\boxed{
\sum_{\rho:F(\rho)=0}\min(w_\rho,\kappa)
=
D\sum_{\lambda\in\operatorname{Sides}(P)}
L_\lambda\min(\lambda,\kappa).}
\tag{ACCOUNT}
\]

This is the only side-accounting identity used by the master proof. An instance may prove it using generic tests, the \(\xi\)- and \(\rho\)-side evaluations, and resultant symmetry, but those arguments remain inside that instance’s pinned proof.

### S1.8 Repeated factors and root-preserving continuation

Suppose \(r'\) occurs in \(R_\lambda\) with multiplicity at least two.

If

\[
e'\deg r'=1,
\]

then \(e'=1\) and \(r'=Y-s\) for some \(s\in K\). The required refinement height lies in \(H_{\mathrm{lift}}\), so `(OCC)` supplies a legal lift. The new key is

\[
\Phi_{\mathrm{new}}=\Phi-L_k(s).
\]

This recentering keeps the same original ground \(O\), the same root block, and the same inherited \((e_{\mathcal C},f_{\mathcal C})\). The above-line perturbation, window, and cap calculations provide a new valid development.

If

\[
e'\deg r'\ge2,
\]

the test polynomial becomes the monic key of a child carrier over the same \(O\). Its inherited invariants are

\[
e_{\mathrm{child}}=e_{\mathcal C}e',
\qquad
f_{\mathrm{child}}=f_{\mathcal C}\deg r',
\]

and hence, by `(DEG-EF)`,

\[
\deg\Psi_{\lambda,r'}
=
e_{\mathrm{child}}f_{\mathrm{child}}
=
De'\deg r'.
\]

The \(r'\)-label class is partitioned into finitely many Galois-stable child blocks. Their monic polynomials multiply to the polynomial of that class, their root sets are pairwise disjoint and exhaustive, and every nonterminal child satisfies

\[
\mu_{\mathrm{child}}
\le
\frac{\mu}{e'\deg r'}
\le\frac{\mu}{2}.
\tag{MASS}
\]

At a mixed residual, this operation is performed separately on each label block. Refining one repeated class does not sequentially recenter the whole polynomial or absorb companion classes.

Finally, every transition preserves the represented root set or partitions it into explicitly disjoint child root sets; transports the polynomial product identity; and composes the inherited ramification and residue invariants by the displayed multiplication laws.

The states carry a well-founded rank. A child jump strictly decreases mass, a split or boundary decomposition strictly decreases degree, and a linear recentering decreases a finite secondary discriminant/slope rank. Every nonterminal repeated class has one of the transitions just described. Consequently there is no infinite branch.

These root-partition and invariant-transport assertions are essential: well-foundedness alone would prove termination but not exhaustion.

### S1.9 Key-boundary preprocessing

A polynomial not satisfying `(KEY-FREE)` does not enter HE7.A.

For a monic separable input \(F\), write

\[
G=\operatorname{monicGCD}_{K_0[x]}(F,\Phi).
\]

A key-boundary decomposition consists of monic polynomials \(P_i\in O[x]\) and key-free residual blocks \(B_j\) such that:

\[
F=\prod_iP_i\prod_jB_j;
\tag{BOUNDARY-PROD}
\]

the \(P_i\) are the distinct irreducible factors of \(G\) occurring in \(F\); their root sets and the residual-block root sets are pairwise disjoint and exhaustive; each \(P_i\) has its proved orbit and local-\((e,f)\) description; and every nonterminal \(B_j\) has strictly smaller degree than \(F\).

Separability makes each \(P_i\) simple. Nothing asserts that \(G=\Phi\), that \(\Phi\) is irreducible, that one factor \(\Phi\) is peeled, or that a peel lowers \(\mu\) by exactly one.

## S2. THE MASTER THEOREM

> **THEOREM HE7.A (σ-LADDER MASTER).**  
> Let \(\mathcal C\) be a σ-ladder carrier over the fixed original complete DVR \(O\), satisfying `(NO-IRR)`, `(DEG-EF)`, `(FINITE-RES)`, `(RES-COMP)`, the exact slot and lift formulas, the normalizer-defined cocycle law, and the base-change-free test assertions of S1.
>
> Let \(F\) be a key-free σ-block with development
>
> \[
> F=\Phi^\mu+\sum_{j<\mu}A_j\Phi^j,
> \]
>
> and suppose its window, cap, frame, origin, residual-degree, accounting, and root-preserving continuation assertions hold.
>
> Then:
>
> 1. every side \(\lambda\) of the complete lower hull \(P\) satisfies
>
>    \[
>    \lambda>T,
>    \qquad
>    \sum_{\lambda\in\operatorname{Sides}(P)}L_\lambda=\mu;
>    \]
>
> 2. if \(\lambda=u'/e'\) is in lowest terms and \(R_\lambda\) is separable, then every monic irreducible factor \(r'\mid R_\lambda\) determines a Galois-stable root class
>
>    \[
>    S_{\lambda,r'}
>    \]
>
>    with
>
>    \[
>    |S_{\lambda,r'}|
>    =De'\deg r'.
>    \]
>
>    This class is one Galois orbit and therefore is the root set of one monic irreducible factor of \(F\). Its invariants are
>
>    \[
>    e=e_{\mathcal C}e',
>    \qquad
>    f=f_{\mathcal C}\deg r';
>    \]
>
> 3. if \(r'\) is repeated, the continuation is decided by the product \(e'\deg r'\). Product \(1\) gives the certified linear recentering; product at least \(2\) gives the certified child carrier and the mass bound `(MASS)`;
>
> 4. mixed residuals are first split into their Galois-stable label blocks, and clauses 2–3 are applied independently to those blocks;
>
> 5. the recursive read terminates. Its terminal monic irreducible factors have pairwise disjoint root sets, their product is \(F\), and their ramification and residue degrees are obtained by multiplying the successive displayed \(e\)- and \(f\)-increments.

**Proof.**

Because \(F\) is key-free, \(A_0\ne0\), and the lower hull spans the full interval from \(0\) to \(\mu\). Thus `(HULL-LENGTH)` gives

\[
\sum_{\lambda\in\operatorname{Sides}(P)}L_\lambda=\mu.
\]

All \(\mu D\) roots of \(F\) lie in the window, so every number

\[
w_\rho=d(\Phi(\rho))
\]

is finite and strictly greater than \(T\).

Apply `(ACCOUNT)` for \(\kappa>T\). On a sufficiently small interval immediately above \(T\), the left side has slope \(\mu D\), since every \(w_\rho\) exceeds \(\kappa\). The right side has slope

\[
D\sum_{\lambda>\kappa}L_\lambda.
\]

It follows that the sides of slope greater than \(T\) already have total length \(\mu\). Since all side lengths are positive and their total length is \(\mu\), there can be no side of slope at most \(T\). This proves clause 1.

Group the roots according to the value \(w_\rho\), and let \(n_\lambda\) denote the number for which \(w_\rho=\lambda\). The two sides of `(ACCOUNT)` are finite sums of the functions \(\min(a,\kappa)\). Their slope jumps at \(\kappa=\lambda\) are respectively \(n_\lambda\) and \(DL_\lambda\). Equality on the complement of the finite critical set, followed by continuity, therefore gives

\[
n_\lambda=DL_\lambda
\tag{SIDE-COUNT}
\]

for every side \(\lambda\).

Now suppose \(R_\lambda\) is separable. Then

\[
R_\lambda=\prod_{r'\mid R_\lambda}r'
\]

with distinct irreducible factors, and `(RES-DEG)` gives

\[
e'\sum_{r'\mid R_\lambda}\deg r'=L_\lambda.
\tag{DEG-SUM}
\]

The test assertions give nonempty, disjoint, exhaustive, Galois-stable classes \(S_{\lambda,r'}\). Local forcing and `(DEG-EF)` show that every orbit in such a class has size at least

\[
(e_{\mathcal C}e')
(f_{\mathcal C}\deg r')
=
De'\deg r'.
\]

Hence

\[
|S_{\lambda,r'}|\ge De'\deg r'.
\]

Summing these inequalities and using `(DEG-SUM)` gives

\[
\sum_{r'}|S_{\lambda,r'}|
\ge
De'\sum_{r'}\deg r'
=
DL_\lambda.
\]

The classes exhaust the side, whose cardinality is exactly \(DL_\lambda\) by `(SIDE-COUNT)`. Equality must therefore hold term by term:

\[
|S_{\lambda,r'}|=De'\deg r'.
\]

A nonempty Galois-stable class with no room for two locally forced orbits is one orbit. Its orbit polynomial is monic, irreducible over \(K_0\), divides \(F\), and has the asserted \(e\)- and \(f\)-values. This proves clause 2.

For a repeated \(r'\), if \(e'\deg r'=1\), then \(e'=1\) and \(r'=Y-s\). The required height is in \(H_{\mathrm{lift}}\); `(OCC)` supplies \(L_k(s)\); and the linear recentering of S1.8 gives the next block while preserving its root set and inherited invariants.

If \(e'\deg r'\ge2\), the child construction partitions the \(r'\)-class into child blocks over the same original DVR and satisfies `(MASS)`. The child invariants are precisely

\[
e_{\mathcal C}e',
\qquad
f_{\mathcal C}\deg r'.
\]

At a mixed residual, disjointness of the label classes permits these operations to be performed independently. The root-partition identities show that no class is lost or counted twice.

Finally apply well-founded induction to the rank of a state. A terminal separable class yields the irreducible factor proved in clause 2. A nonterminal linear refinement preserves the represented roots and has smaller secondary rank. A child jump or split replaces the state by finitely many smaller states whose root sets are disjoint and exhaustive and whose polynomials multiply to the parent polynomial. The induction hypothesis therefore gives exhaustive irreducible factorizations of all children; multiplying them gives the corresponding factorization of the parent. The invariant-transport formulas compose along each branch.

Thus every branch terminates, the terminal factors exhaust \(F\), and the successive \(e\)- and \(f\)-multipliers give their final local invariants. No step assumes that \(\Phi\) is irreducible, that \(O[x]/(\Phi)\) is a DVR, or that the coefficient DVR has changed. ∎

### S2.1 Boundary theorem

> **THEOREM T2.KEY-BOUNDARY.**  
> Let \(F\) be a monic separable input with a key-boundary decomposition `(BOUNDARY-PROD)`. Adjoin the certified irreducible boundary factors \(P_i\), and apply HE7.A separately to each key-free residual block \(B_j\). The resulting irreducible factors have disjoint root sets and exhaust the roots of \(F\).

**Proof.** The boundary decomposition already gives the polynomial product and the disjoint exhaustive partition into boundary and residual root classes. Each \(P_i\) is terminal by its orbit certificate. HE7.A factors every residual block without changing or losing its root class. Multiplying the resulting identities proves the assertion. ∎

This replaces the invalid reducible-key “\(\Phi\)-peel” dichotomy.

## S3. FIVE SPAN-PINNED MATHEMATICAL INSTANCE RECORDS

The following are mathematical substitutions into HE7.A. Local source strength may be forgotten, but no instance may add a premise absent from the master or silently omit one of its hypotheses.

### S3.1 HE3.A — base-stage resolvent read

**Source pins:** `HE3-A-STMT`, `HE3-A-PROOF`, `HE3-DEF1`, `HE3-HE3-1L`, `HE3-HE3-6`, and `HE3-R8-2` through `HE3-R8-5`.

The instance substitution is

\[
\boxed{
\begin{aligned}
K&=\mathbf F_{Q^{f_1}},\\
\Phi&=\Phi',\\
D&=D'=e_1f_1,\\
(e_{\mathcal C},f_{\mathcal C})&=(e_1,f_1),\\
d&=dv=e_1v,\\
T&=D'h,\\
\operatorname{dig}(A)&=\gamma_{dv(A)}(A).
\end{aligned}}
\tag{HE3-INSTANCE}
\]

The points are the HE3 `(T1)/(T2)` points, with

\[
\iota_\xi(\eta_\theta)=\eta_\xi.
\]

The original coefficient DVR is \(O\). The order \(O[\theta]\) is auxiliary and is not asserted to be a complete DVR.

The source proves more than the master requests by having an irreducible local key. The instance forgets that strength and exports only monicity, degree, and `(DEG-EF)`.

The HE3-1L span supplies the required full-height domain. Every height used by the test family lies above \(D'h>(D'-1)h\), so `(OCC)` holds. The full development supplies the hull, window, and cap assertions. HE3-6 supplies label equivariance.

A key-free HE3 block enters HE7.A directly. A raw block meeting a proper factor of \(\Phi'\) may enter only through the separate key-boundary theorem; no assertion that one copy of \(\Phi'\) can be peeled is used.

The resulting dictionary is

\[
(e,f)=(e_1e_s,f_1f_s).
\]

### S3.2 HE6 — enlarged fractional-height tests

**Source pins:** `HE6-FAMILY`, `HE6-PROOF`, and `HE6-SLOT-SEAM`.

The ground data, label field, key, and inherited invariants are those of HE3:

\[
\boxed{
\begin{aligned}
K&=\mathbf F_{Q^{f_1}},\\
\Phi&=\Phi',\\
D&=D'=e_1f_1,\\
(e_{\mathcal C},f_{\mathcal C})&=(e_1,f_1),\\
d&=dv,\\
T&=D'h.
\end{aligned}}
\tag{HE6-INSTANCE}
\]

Its coherent slot digit is exactly `(GAMMA)`. The print-frame read is exactly

\[
\operatorname{res}(A/\varpi^k)
=
\iota(\gamma_k(A))\eta^{-q(k)}.
\]

The bare sum of coefficient residues is not an admissible substitute.

The test family is

\[
\Psi_{\kappa,r}
=
{\Phi'}^{\ell d}
+\sum_{t<d}B_t{\Phi'}^{\ell t}
\in O[x],
\]

with

\[
\deg\Psi_{\kappa,r}=D'\ell d.
\]

It is monic and is not assumed irreducible. HE6’s ξ-side, evaluation formulas, slope count, resultant argument, and equivariance supply the test assertions and `(ACCOUNT)`.

The corrected HE6 full-height condition makes all coefficient lifts \(B_t\) legal. The instance therefore requires neither a ramified base change nor a stage complete DVR.

For a separable residual factor \(r\),

\[
|S_{\lambda,r}|=D'\ell\deg r,
\qquad
(e,f)=(e_1\ell,f_1\deg r).
\]

On a block whose residuals are all separable, this is a terminal instance of the full theorem. When repeated factors occur, HE6 supplies the test step and the continuation is the level-two construction recorded in the next instance; an empty continuation is not inferred merely from the fact that HE6 is a one-round theorem.

### S3.3 HE7 + HE6R1 — level two

**Source pins:** `HE7-A-STMT`, `HE7-SLOT-TRANSFER`, `HE7-MIXED-13P`, `HE7-COCYCLE-2P-THROUGH-R1D`, `HE6R1-1`, `HE6R1-2`, and `HE6R1-3`.

Given a level-one label \((\lambda,r)\), write

\[
\lambda=\frac{u}{\ell}>D'h,
\qquad
d_r=\deg r,
\qquad
K_2=K[Y]/(r)=K(\beta).
\]

The instance is

\[
\boxed{
\begin{aligned}
K_{\mathcal C}&=K_2,\\
\Phi&=\Psi_{\lambda,r},\\
D&=D''=D'\ell d_r,\\
(e_{\mathcal C},f_{\mathcal C})
&=(e_1\ell,f_1d_r),\\
d&=dv_2=\ell\,dv,\\
T&=T_2=\ell d_ru.
\end{aligned}}
\tag{HE7-INSTANCE}
\]

Thus

\[
D''
=
(e_1\ell)(f_1d_r)
=
e_{\mathcal C}f_{\mathcal C}.
\]

The key \(\Psi_{\lambda,r}\) is monic. Its irreducibility is not a premise.

The level-two point class and embeddings are the source’s

\[
\operatorname{Pt}_2,\qquad
\iota_\xi^{(2)}:K_2\hookrightarrow\overline k.
\]

The normalizers are

\[
n_2(k)=\varpi^{m(k)}{\Phi'}^{s(k)},
\]

the slot is `(SLOT₂)`, and the legal lift domain is `(FULL2)`, with `(FULL2-U)` as a uniform sufficient bound.

The cocycle is the actual residue of the normalizer quotient and equals the nontrivial \(\beta^c\) twist. The HE7 test coefficients contain the corresponding inverse twists.

HE6R1-2 transports the \(>T_2\) hull, lengths, and residual factors to the selected block. HE7’s above-line perturbation argument supplies the window and cap assertions. HE7-13′ supplies the per-label treatment of mixed residuals. The refinement package supplies root-preserving linear steps, child partitions, invariant transport, and the well-founded rank.

The repeated-factor branch is

\[
\ell_2\deg r_2=1
\quad\text{versus}\quad
\ell_2\deg r_2\ge2.
\]

The conclusion is

\[
|S_{\lambda_2,r_2}|
=
D''\ell_2\deg r_2,
\]

with

\[
e=e_1\ell\ell_2,
\qquad
f=f_1d_r\deg r_2.
\]

The only irreducibility assumptions are those on residual labels such as \(r\) and \(r_2\). No irreducibility of the current key is used.

### S3.4 HETOW — full inner tower sides

**Source pins:** `HETOW-LABELS`, `HETOW-A`, and `HETOW-NORMALIZER-4`.

For full tower-side data \((e_2,f_2,u_2,\psi_2)\), the instance is

\[
\boxed{
\begin{aligned}
K_{\mathcal C}&=K_2
 \cong\mathbf F_{Q^{f_1f_2}},\\
\Phi&=\Phi_2,\\
D&=D_2=D'e_2f_2,\\
(e_{\mathcal C},f_{\mathcal C})
&=(e_1e_2,f_1f_2),\\
d&=dv_2=e_1e_2v,\\
T&=T_2=e_2f_2u_2.
\end{aligned}}
\tag{HETOW-INSTANCE}
\]

Since \(D'=e_1f_1\),

\[
D_2=(e_1e_2)(f_1f_2).
\]

The key \(\Phi_2\) is the wrap-corrected composed key. HETOW-2 identifies it with a genuine HE6-family key in the legal lifted form, or with an allowed above-line perturbation.

The transported letter is

\[
\beta=\eta^{-Q(u_2)}\eta_2,
\]

and \(\widetilde r\) is its minimal polynomial.

The coherent normalizer is HE7’s \(n_2\). The tower-print normalizer \(\widehat n_2\) is compared through HETOW-4. Per-height residues satisfy

\[
\tau(k)=\eta^{-Q(m(k))}
\]

but are not declared equal. After complete bracket assembly,

\[
R_{\lambda_2}(Z)
=
\tau(H_0)\,
\widehat R_{\lambda_2}(Z/\delta),
\qquad
\delta=\tau(u_3)\in K^\times.
\]

This is the frame bridge. It preserves separability, residual factor degrees, multiplicities, product branches, and refined root classes.

The full-side identity gives \(f_S=f\). Any key-boundary contribution is handled by T2.KEY-BOUNDARY, not by a purported single \(\Phi_2\)-peel.

The corrected-key and carry audit gives the window and cap assertions. Any attained-origin shift is retained through `(ORIGIN)` and removed before factor comparison.

The output is

\[
e=e_1e_2\ell_2,
\qquad
f=f_1f_2\deg r_2.
\]

No equality of raw tower-print and coherent coefficient arrays is claimed.

### S3.5 GENTOW4 — partial inner sides, per block

**Source pins:** `GENTOW-4-1`, `GENTOW-4-A`, `GENTOW-4-2`, and `GENTOW-ACCEPTANCE-FOLD`.

The ground carrier is the HETOW carrier:

\[
\boxed{
\begin{aligned}
K_{\mathcal C}&=K_2,\\
\Phi&=\Phi_2,\\
D&=D_2=D'e_2f_2,\\
(e_{\mathcal C},f_{\mathcal C})
&=(e_1e_2,f_1f_2),\\
d&=dv_2,\\
T&=T_2.
\end{aligned}}
\tag{GENTOW4-INSTANCE}
\]

The level-one decomposition is a bouquet

\[
f=\prod_{(\kappa,r)}f_{\kappa,r}.
\]

For a selected class,

\[
F=f_S=f_{\kappa,r}.
\]

No whole-polynomial monicity or length hypothesis is transferred to \(f_S\) without proof.

Writing

\[
g=f/f_S,
\]

HE6R1-2 gives a constant

\[
c_g=dv_2(g(\xi))
\]

and identifies the \(>T_2\) hull of \(f\) with the hull of \(f_S\) translated vertically by \(c_g\). Hence the correct block mass is

\[
\mu_2^*
=
\sum_{\lambda_2>T_2}L_{\lambda_2}(f),
\qquad
\deg f_S=D_2\mu_2^*.
\]

Residual polynomials agree only up to the fixed nonzero scalar and cocycle unit supplied by pin-height normalization. Parity and residual decisions are made after subtracting \(c_g\).

The projection identity supplies the window assertion. The partial-side cap and collection calculation supplies cap safety: sibling terms cannot create a lower face beneath the selected \(>T_2\) segment. The frame data separately records the \(c_g\)-translation, variable rescaling, and any nonzero raw-origin factor \(Y^\nu\).

Mixed sides are read per label block. The unproved equality between level-one residual multiplicity and projected block length is not assumed; \(\mu_2^*\) is read from the projected hull itself.

The conclusion on each selected block is

\[
e=e_1e_2\ell_2,
\qquad
f=f_1f_2\deg r_2.
\]

The factorization of \(f\) is the disjoint union of the bouquet-block factorizations together with any separately certified key-boundary factors.

The count-side mixed-multiplicity tie, partial-side budgets, and density laws are not conclusions of this σ-decision instance.

## S4. HONESTY LEDGER

### S4.1 Scope and grade

This note proves a mathematical composition theorem: the displayed original-\(O\) hypotheses suffice for one HE7.A argument, and the five pinned source displays give the intended substitutions.

It does not rerun supplier batteries, certify marker installation, construct a Lean term, or upgrade a documentary grade.

The consumption grade is

\[
\operatorname{grade}(I)
=
\min(
g_{\mathrm{master}},
g_{\mathrm{carrier}},
g_{\mathrm{frame}},
g_{\mathrm{local}}
).
\tag{GRADE}
\]

This v2 master begins at attempt grade \(0/2\). Consequently every composed instance remains \(0/2\) until this note completes its own hostile arc, regardless of the supplier’s grade.

At the supplied source HEAD:

- HE6 is accepted \(2/2\), including its corrected normalized-slot formula.
- HE7 is accepted \(2/2\), including the corrected all-level cocycle and mixed-residual rider.
- HE6R1 is accepted \(2/2\). Its separate count-side unit is not used here.
- HETOW is accepted \(2/2\); the HETOW-4 normalizer bridge is essential.
- GENTOW4 is accepted \(2/2\); its boxed count budgets are not imported.
- HE3 is consumed at the grade stated by its supplied HEAD.

The theorem assumes the explicit quantitative consequences `(ACCOUNT)`, `(RES-DEG)`, nonemptiness, exhaustion, and root-preserving continuation. These are source obligations, not conclusions obtained merely by naming a carrier.

### S4.2 Explicit exclusions

The master does not claim:

- a complete-DVR structure on \(O[x]/(\Phi)\);
- irreducibility of the current key;
- that \(\Phi\nmid F\) is sufficient for key-freeness;
- that a common key boundary is one copy of \(\Phi\);
- all-height lift surjectivity;
- a residue map without its valuation domain;
- equality of raw and coherent residual coefficient arrays;
- termination without root preservation and root partition;
- the mixed-multiplicity product formula;
- partial-side budget or density laws;
- an elaborated formal instance;
- acceptance before two clean hostile passes.

## S5. RE-COMPOSITION LEDGER

The P1–P3 defects are closed mathematically as follows.

1. The invalid reducible-key peel is replaced by `(KEY-FREE)` and the separate gcd/orbit boundary theorem.

2. The note makes no claim that a formal first gate has run. Formal declarations and obligation manifests belong to stage 2.

3. Every cited source unit has a named paired begin/end pin.

4. The master consumes only the explicitly displayed test consequences, including `(ACCOUNT)` and `(RES-DEG)`.

5. All five substitutions display \(D\), \(e_{\mathcal C}\), and \(f_{\mathcal C}\), with \(D=e_{\mathcal C}f_{\mathcal C}\).

6. The complete lower hull is used; there is no unspecified subset of “consumed sides.”

7. Key-boundary preprocessing is outside the key-free block theorem.

8. An empty transition is allowed only for a genuinely terminal block with no repeated residual factor.

9. Valued points live in \(\overline K_0\), while residual labels live in \(\overline k\).

10. The finite extension \(K/k_0\) and compatibility of every \(\iota_\xi\) are explicit.

11. The cocycle is defined as the residue of the normalizer quotient, so the HE7 \(\beta^c\) twist cannot be replaced by a trivial cocycle.

12. Recursive transitions preserve or partition root classes, transport polynomial products, and compose invariants; well-foundedness then proves both termination and exhaustion.

## S6. FIVE-HAZARD CLOSURE

| Hazard | Verdict | Mathematical closure |
|---|---|---|
| Hypothesis migration | **Closed for composition** | Key-freeness, finite windows, lift domains, accounting, residual degree, frame/origin changes, cap safety, and recursive root preservation are displayed hypotheses. |
| Instance-strength collapse | **Closed** | The key is monic only; \(D=e_{\mathcal C}f_{\mathcal C}\); lifts exist only at full heights; repeated branches split on \(e'\deg r'\). |
| Hidden perimeter enlargement | **Closed** | Every instance must prove its full-hull or projected-hull identity and its cap assertion. Mixed residuals are processed per block. |
| Convention seam | **Closed** | `(GAMMA)`, `(HE6-SEAM)`, `(COC-DEF)`, `(BETA)`, `(FRAME)`, `(ORIGIN)`, the HETOW bridge, and the \(c_g\)-translation govern all comparisons. |
| Grade laundering | **Closed for composition; open for acceptance** | `(GRADE)` takes the minimum of the master, carrier, frame, and local grades. |

No mathematical hazard blocks composition. Acceptance remains a separate arc.

## S7. ARC PLAN AND FILE-LEVEL GATES

The v2 arc consists of two hostile passes over this post-composition text. A gap-or-worse repair resets the clean count.

### Pass 1

1. **Pure-mathematics theorem gate.** Check every implication in HE7.A, especially `(ACCOUNT)` to `(SIDE-COUNT)`, `(RES-DEG)` to the termwise orbit equality, and root-preserving well-founded induction to exhaustion.

2. **Reducible-key boundary gate.** Test a monic reducible \(\Phi\) for which \(\gcd(F,\Phi)\) is a proper nontrivial factor. HE7.A must refuse the raw input, while T2.KEY-BOUNDARY must handle it without asserting that \(\Phi\) itself is irreducible.

3. **HE6 seam gate.** Verify normalized coefficients in \(\gamma_k(A)\) and the exact factor \(\eta^{-q(k)}\).

4. **HE7 cocycle gate.** Force a carry and verify the live factor \(\beta^c\) in the assembled residual.

5. **HETOW frame gate.** Compare coherent and print residuals only after bracket assembly and after recording any nonzero origin shift.

6. **GENTOW4 perimeter gate.** Check the projected \(>T_2\) hull, \(c_g\)-translation, cap safety, and per-block residual reading without using the boxed mixed-multiplicity tie.

7. **Pin gate.** Check every marker pair in `(PINS)` for existence, uniqueness, ordering, and containment of the cited source unit.

### Pass 2

The second pass attacks a disjoint surface:

- a reducible key with several boundary factors;
- a sub-threshold lift request, which must be refused;
- a mixed residual with two repeated label classes;
- a deep cocycle involving more than one preceding letter;
- a proxy development with a dangerous collected term;
- a nonzero raw-origin shift;
- a transition that is well-founded but fails to preserve roots, which must be rejected;
- a residual factorization with a missing `(RES-DEG)` bridge, which must be rejected.

### Stage 2 formal gate

Only after the mathematical passes are clean does the S-5 formal probe encode the theorem. That later encoding must preserve:

- the fixed original-\(O\) ground;
- separate valued and residue closures;
- finite compatible \(K/k_0\);
- `(DEG-EF)`;
- the normalizer-defined cocycle;
- legal lift domains;
- complete lower-hull coverage;
- residual degree accounting;
- key-boundary preprocessing outside key-free blocks;
- root-preserving recursive transitions.

Its HE7 construction may require irreducibility of residual labels and emitted boundary factors. It must generate no obligation asserting irreducibility of the current key.

This v2 note does not claim that the formal gate has already passed.

## S8. FINAL COMPOSITION VERDICT

**S-6 GO for the pure-mathematics master.**

HE7.A is now stated and proved over one fixed original complete DVR \(O\). The current key is monic of degree

\[
D=e_{\mathcal C}f_{\mathcal C},
\]

but need not be irreducible.

The proof uses:

- exact normalized slots;
- legal finite lift domains;
- the actual normalizer cocycle;
- complete lower-hull accounting;
- the residual degree identity;
- base-change-free tests;
- explicit frame and origin bridges;
- key-free blocks;
- root-preserving, invariant-preserving, well-founded continuation.

A reducible key boundary is handled by a separate gcd/orbit decomposition, never by a false one-factor peel.

The five source substitutions are recorded by paired span pins. HE6 enters through

\[
\gamma_k(A)\eta^{-q(k)};
\]

HE7 enters with the genuine \(\beta^c\) twist; and HETOW and GENTOW4 enter through explicit frame, origin, window, cap, and block-projection formulas.

No complete-DVR quotient, current-key irreducibility, all-height lift, raw-frame coefficient invariance, or unsupported recursive exhaustion is claimed.

\[
\boxed{
\text{Any later HE7 formalization that requires irreducibility of the current key is not a formalization of this theorem.}}
\]


---

## r1 (v2) (2026-08-12): arc repairs

*(gpt-5.6-sol high, runs/comp11/T2R1v2_output.log; transcribed unaltered; counter resets.)*

## r1 repair 1 — install the mixed-residual block theorem

Insert after S1.7:

> ### S1.7A Label-block decomposition
>
> Let \(\lambda=u'/e'\) be a side of a \(\sigma\)-block \(F\), and write
>
> \[
> R_\lambda(Y)=\prod_{r'}r'(Y)^{m_{\lambda,r'}}.
> \]
>
> For every factor \(r'\), the carrier supplies a monic separable polynomial
>
> \[
> F_{\lambda,r'}\in O[x]
> \]
>
> whose roots are exactly the roots in the \(r'\)-label class. Put
>
> \[
> \mu_{\lambda,r'}
> =
> e'm_{\lambda,r'}\deg r'.
> \]
>
> The polynomial \(F_{\lambda,r'}\) has degree
>
> \[
> \deg F_{\lambda,r'}
> =
> D\mu_{\lambda,r'}
> =
> De'm_{\lambda,r'}\deg r',
> \tag{LABEL-DEG}
> \]
>
> and a full \(\Phi\)-development
>
> \[
> F_{\lambda,r'}
> =
> \Phi^{\mu_{\lambda,r'}}
> +
> \sum_{j<\mu_{\lambda,r'}}A^{(\lambda,r')}_j\Phi^j.
> \tag{LABEL-DEV}
> \]
>
> This development is key-free, has a single lower-hull side of slope \(\lambda\) and length \(\mu_{\lambda,r'}\), and, after the prescribed frame and origin normalization, has residual polynomial
>
> \[
> R_{\lambda,r'}(Y)
> =
> c_{\lambda,r'}\,r'(Y)^{m_{\lambda,r'}},
> \qquad
> c_{\lambda,r'}\in K^\times.
> \tag{LABEL-PURE}
> \]
>
> Each \(F_{\lambda,r'}\) inherits the window, cap, occupied-height, legal-lift, test, accounting, and root-preserving continuation assertions required by HE7.A. In particular,
>
> \[
> \sum_{\rho:F_{\lambda,r'}(\rho)=0}
> \min(d(\Phi(\rho)),\kappa)
> =
> D\mu_{\lambda,r'}\min(\lambda,\kappa)
> \tag{LABEL-ACCOUNT}
> \]
>
> for every allowed \(\kappa\).
>
> For a fixed side, the block polynomials multiply to the polynomial of the roots belonging to that side, and the products over all sides multiply to the parent:
>
> \[
> F_\lambda
> =
> \prod_{r'}F_{\lambda,r'},
> \qquad
> F
> =
> \prod_\lambda F_\lambda.
> \tag{LABEL-PROD}
> \]
>
> Their root sets are pairwise disjoint and exhaustive, and these product identities are preserved by every later transition. If \(R_\lambda\) contains at least two distinct irreducible factors, every \(F_{\lambda,r'}\) has degree strictly smaller than the polynomial represented by the unsplit side state.
>
> This is the mixed-residual block theorem. Galois stability of label classes or disjointness alone is not used as a substitute for `(LABEL-DEG)`–`(LABEL-PROD)`.

Replace the mixed-residual paragraph in S1.8 with:

> At a mixed residual, first apply the label-block decomposition of S1.7A. Each multiplicity-one block has residual \(c\,r'\) and is therefore terminal by clause 2 of HE7.A. Each block with multiplicity at least two is continued independently by the product-\(1\)/product-\(\ge2\) alternatives above. Refining one block never recenters, absorbs, or changes a companion block.

Replace clause 4 of HE7.A with:

> 4. if a residual contains more than one distinct irreducible factor, the label-block theorem first replaces the side state by the monic blocks \(F_{\lambda,r'}\). These blocks have pure residuals \(c_{\lambda,r'}r'^{m_{\lambda,r'}}\), pairwise disjoint exhaustive root sets, and product equal to the side polynomial. A block with \(m_{\lambda,r'}=1\) is terminal by clause 2; a block with \(m_{\lambda,r'}\ge2\) is continued by clause 3;

Replace the two sentences beginning “At a mixed residual” in the proof with:

> If a residual is mixed, invoke `(LABEL-PROD)` before performing any refinement. The resulting \(F_{\lambda,r'}\) are valid smaller HE7.A states with single-side residual \(c_{\lambda,r'}r'^{m_{\lambda,r'}}\). When \(m_{\lambda,r'}=1\), the original separable-side argument applied to this block gives one orbit of size
>
> \[
> De'\deg r'.
> \]
>
> When \(m_{\lambda,r'}\ge2\), clause 3 applies to that block alone. The disjoint root partition and polynomial product in `(LABEL-PROD)` ensure that no simple companion class is omitted and that refinement of a repeated class cannot absorb another label class.

In the well-founded-induction paragraph, insert before the linear-refinement case:

> A mixed-label split replaces its state by the strictly smaller label blocks of S1.7A. The induction hypothesis applies to every such block, and `(LABEL-PROD)` reassembles their exhaustive factorizations.

This supplies the missing terminal case for a simple factor beside a repeated factor and the missing transition/product theorem for every mixed residual.

## r1 repair 2 — make HE3 explicitly consume HE6

Replace the source-pin paragraph at the start of S3.1 with:

> **Source pins:** `HE3-A-STMT`, `HE3-A-PROOF`, `HE3-DEF1`, `HE3-HE3-1L`, `HE3-HE3-6`, `HE3-R8-2` through `HE3-R8-5`, together with `HE6-FAMILY`, `HE6-PROOF`, and `HE6-SLOT-SEAM`.
>
> The HE3 pins supply the base carrier, exact slots, legal full-height lifts, full development, hull/window/cap data, and label equivariance. They are not credited with the master’s universal test package or with `(ACCOUNT)`.
>
> For every side denominator \(e'\) and every monic irreducible residual factor \(r'\), the HE6 pins supply the monic test polynomial
>
> \[
> \Psi_{\lambda,r'}\in O[x],
> \qquad
> \deg\Psi_{\lambda,r'}=D'e'\deg r',
> \]
>
> together with its intended-disk and label properties, generic and raised evaluation values, resultant nonemptiness, disjointness and exhaustion, Galois equivariance, local divisibility, integrality, and the quantitative identity `(ACCOUNT)`. Thus this record is a composite HE3+HE6 discharge of the master hypotheses; it is not an HE3-only discharge.

Delete:

> Every height used by the test family lies above \(D'h>(D'-1)h\), so `(OCC)` holds.

Replace it with:

> The HE3-1L full-height result, together with the coefficient-height bounds in `HE6-FAMILY` and `HE6-PROOF`, proves `(OCC)` for every coefficient lift used by the HE6 test family.

Replace:

> A key-free HE3 block enters HE7.A directly.

with:

> A key-free HE3 block enters HE7.A only through this composite HE3+HE6 route. No claim is made that the HE3 pins alone cover the fractional-slope, residual-degree-\(\ge2\) test branch.

This preserves the HE3 carrier while explicitly sourcing the universal tests and `(ACCOUNT)` from HE6.

## r1 repair 3 — install and audit all advertised source markers

Do not weaken the fail-closed convention. Insert the following exact marker-only lines immediately before and after the complete source unit named by each pin.

For `HE3_PROOF_2026-08-08.md`:

```html
<!-- T2V2PIN:HE3-A-STMT:BEGIN -->
<!-- T2V2PIN:HE3-A-STMT:END -->
<!-- T2V2PIN:HE3-A-PROOF:BEGIN -->
<!-- T2V2PIN:HE3-A-PROOF:END -->
<!-- T2V2PIN:HE3-DEF1:BEGIN -->
<!-- T2V2PIN:HE3-DEF1:END -->
<!-- T2V2PIN:HE3-HE3-1L:BEGIN -->
<!-- T2V2PIN:HE3-HE3-1L:END -->
<!-- T2V2PIN:HE3-HE3-6:BEGIN -->
<!-- T2V2PIN:HE3-HE3-6:END -->
<!-- T2V2PIN:HE3-R8-2:BEGIN -->
<!-- T2V2PIN:HE3-R8-2:END -->
<!-- T2V2PIN:HE3-R8-3:BEGIN -->
<!-- T2V2PIN:HE3-R8-3:END -->
<!-- T2V2PIN:HE3-R8-4:BEGIN -->
<!-- T2V2PIN:HE3-R8-4:END -->
<!-- T2V2PIN:HE3-R8-5:BEGIN -->
<!-- T2V2PIN:HE3-R8-5:END -->
```

For `HE6_PROOF_2026-08-08.md`:

```html
<!-- T2V2PIN:HE6-FAMILY:BEGIN -->
<!-- T2V2PIN:HE6-FAMILY:END -->
<!-- T2V2PIN:HE6-PROOF:BEGIN -->
<!-- T2V2PIN:HE6-PROOF:END -->
<!-- T2V2PIN:HE6-SLOT-SEAM:BEGIN -->
<!-- T2V2PIN:HE6-SLOT-SEAM:END -->
```

For `HE7_PROOF_2026-08-08.md`:

```html
<!-- T2V2PIN:HE7-A-STMT:BEGIN -->
<!-- T2V2PIN:HE7-A-STMT:END -->
<!-- T2V2PIN:HE7-SLOT-TRANSFER:BEGIN -->
<!-- T2V2PIN:HE7-SLOT-TRANSFER:END -->
<!-- T2V2PIN:HE7-MIXED-13P:BEGIN -->
<!-- T2V2PIN:HE7-MIXED-13P:END -->
<!-- T2V2PIN:HE7-COCYCLE-2P-THROUGH-R1D:BEGIN -->
<!-- T2V2PIN:HE7-COCYCLE-2P-THROUGH-R1D:END -->
```

The `HE7-MIXED-13P` span must contain the complete source theorem supplying `(LABEL-DEG)`–`(LABEL-PROD)`, not merely the sentence directing per-label processing.

For `HE6R1_RECON_2026-08-08.md`:

```html
<!-- T2V2PIN:HE6R1-1:BEGIN -->
<!-- T2V2PIN:HE6R1-1:END -->
<!-- T2V2PIN:HE6R1-2:BEGIN -->
<!-- T2V2PIN:HE6R1-2:END -->
<!-- T2V2PIN:HE6R1-3:BEGIN -->
<!-- T2V2PIN:HE6R1-3:END -->
```

For `HETOW_RECON_2026-08-09.md`:

```html
<!-- T2V2PIN:HETOW-LABELS:BEGIN -->
<!-- T2V2PIN:HETOW-LABELS:END -->
<!-- T2V2PIN:HETOW-A:BEGIN -->
<!-- T2V2PIN:HETOW-A:END -->
<!-- T2V2PIN:HETOW-NORMALIZER-4:BEGIN -->
<!-- T2V2PIN:HETOW-NORMALIZER-4:END -->
```

For `GENTOW4_PROOF_2026-08-09.md`:

```html
<!-- T2V2PIN:GENTOW-4-1:BEGIN -->
<!-- T2V2PIN:GENTOW-4-1:END -->
<!-- T2V2PIN:GENTOW-4-A:BEGIN -->
<!-- T2V2PIN:GENTOW-4-A:END -->
<!-- T2V2PIN:GENTOW-4-2:BEGIN -->
<!-- T2V2PIN:GENTOW-4-2:END -->
<!-- T2V2PIN:GENTOW-ACCEPTANCE-FOLD:BEGIN -->
<!-- T2V2PIN:GENTOW-ACCEPTANCE-FOLD:END -->
```

Add at the end of S0.2:

> “Source pins” below means installed and audited spans, not proposed future anchors. The r1 source bundle is valid only when all 26 begin/end pairs occur in the six named source files, each marker occurs exactly once, each begin precedes its matching end, and each resulting span contains the complete cited source unit. The expected audit total is 52 marker-only lines: 26 begin markers and 26 end markers. The T2 text alone cannot discharge this source-edit obligation.


---

## r2 (2026-08-12): the model-diverse pass findings repaired

*(gpt-5.6-sol high, runs/comp12/T2R2v2_output.log, from the Fable-arm pass of record (0C+4G+4m); transcribed unaltered; counter resets.)*

## r2 repair 1 — replace synthetic pins by immutable existing-text spans

Delete S0.2 and replace it with:

> ### S0.2 Existing-text span convention
>
> No source file is edited to install a pin.
>
> For a unique complete source unit \(U\), write
>
> \[
> \langle\operatorname{first}(U),\operatorname{last}(U)\rangle
> \]
>
> for the closed span beginning with the complete first nonblank source line of \(U\) and ending with its complete last nonblank source line. Both delimiter lines must already occur in the accepted source.
>
> The unit boundaries are the Markdown structural boundaries already present in the source: a theorem, lemma, definition, numbered clause, proof, annex, or redline unit ends immediately before the next unit of equal or higher structural rank. For a subclause pin, the unit ends immediately before the next sibling subclause.
>
> A pin is valid only if:
>
> 1. its named source unit occurs exactly once in the named file;
> 2. its first and last delimiter lines each occur exactly once;
> 3. the first delimiter precedes the last delimiter;
> 4. the resulting span contains the complete named unit.
>
> Failure of any condition makes that route fail closed. A line number, synthetic comment, prospective anchor, or text inserted after source acceptance is not a pin.
>
> The 26 pins are the following existing-text pairs:
>
> \[
> \begin{array}{c|l|l}
> \text{file}&\text{pin}&\text{unique complete source unit }U\\ \hline
> \text{HE3}&\texttt{HE3-A-STMT}&\text{the statement display of THEOREM HE3.A}\\
> &\texttt{HE3-A-PROOF}&\text{the proof unit belonging to THEOREM HE3.A}\\
> &\texttt{HE3-DEF1}&\text{DEFINITION 1}\\
> &\texttt{HE3-HE3-1L}&\text{LEMMA HE3-1L}\\
> &\texttt{HE3-HE3-6}&\text{LEMMA HE3-6}\\
> &\texttt{HE3-R8-2}&\text{the complete R8.2 redline unit}\\
> &\texttt{HE3-R8-3}&\text{the complete R8.3 redline unit}\\
> &\texttt{HE3-R8-4}&\text{the complete R8.4 redline unit}\\
> &\texttt{HE3-R8-5}&\text{the complete R8.5 redline unit}\\ \hline
> \text{HE6}&\texttt{HE6-FAMILY}&\text{the complete HE6 test-family display}\\
> &\texttt{HE6-PROOF}&\text{the complete proof unit of THEOREM HE6.A}\\
> &\texttt{HE6-SLOT-SEAM}&\text{the corrected normalized-slot/seam display}\\ \hline
> \text{HE7}&\texttt{HE7-A-STMT}&\text{the statement display of THEOREM HE7.A}\\
> &\texttt{HE7-SLOT-TRANSFER}&\text{the complete level-two slot-transfer display}\\
> &\texttt{HE7-MIXED-13P}&\text{ANNEX-LEMMA HE7-13'}\\
> &\texttt{HE7-COCYCLE-2P-THROUGH-R1D}&
> \text{the complete accepted cocycle chain from ANNEX 2-P through R1-D}\\ \hline
> \text{HE6R1}&\texttt{HE6R1-1}&\text{LEMMA HE6R1-1}\\
> &\texttt{HE6R1-2}&\text{LEMMA HE6R1-2}\\
> &\texttt{HE6R1-3}&\text{LEMMA HE6R1-3}\\ \hline
> \text{HETOW}&\texttt{HETOW-LABELS}&\text{the complete HETOW label dictionary}\\
> &\texttt{HETOW-A}&\text{the statement and proof unit of THEOREM HETOW.A}\\
> &\texttt{HETOW-NORMALIZER-4}&\text{the complete HETOW-4 normalizer comparison}\\ \hline
> \text{GENTOW4}&\texttt{GENTOW-4-1}&\text{the complete GENTOW-4.1 unit}\\
> &\texttt{GENTOW-4-A}&\text{THEOREM GENTOW-4.A, including clause (i)}\\
> &\texttt{GENTOW-4-2}&\text{the complete GENTOW-4.2 unit}\\
> &\texttt{GENTOW-ACCEPTANCE-FOLD}&
> \text{the complete GENTOW4 acceptance-fold unit}
> \end{array}
> \tag{PINS}
> \]
>
> Thus, for example,
>
> \[
> \texttt{HE7-MIXED-13P}
> =
> \langle
> \operatorname{first}(\text{ANNEX-LEMMA HE7-13'}),
> \operatorname{last}(\text{ANNEX-LEMMA HE7-13'})
> \rangle,
> \]
>
> and
>
> \[
> \texttt{GENTOW-4-A}
> =
> \langle
> \operatorname{first}(\text{THEOREM GENTOW-4.A}),
> \operatorname{last}(\text{THEOREM GENTOW-4.A})
> \rangle;
> \]
>
> the latter span therefore contains the bouquet carrier in GENTOW-4.A(i).
>
> These pins lie in the six files listed below `(PINS)`. “Source pins” means these audited existing-text spans. The expected source edit count is zero.

Delete r1 repair 3 in its entirety. Replace S7’s pin gate by:

> 7. **Pin gate.** Resolve every pin in `(PINS)` to its existing first/last delimiter pair. Check uniqueness, ordering, structural completeness, and containment of the cited display. Also check that the six accepted source files contain no `T2V2PIN` line. The expected pin count is 26 and the expected synthetic-marker count is zero.

---

## r2 repair 2 — replace the false parent-multiplicity tie by block-owned residual data

Delete r1’s S1.7A and replace it with:

> ### S1.7A Side and label blocks
>
> Let \(F\) be a state to which the carrier’s block theorem applies. Its roots first decompose by their actual \(\Phi\)-value:
>
> \[
> F=\prod_\lambda F_\lambda,
> \tag{SIDE-PROD}
> \]
>
> where \(F_\lambda\in O[x]\) is monic and separable, its roots are exactly the roots satisfying
>
> \[
> d(\Phi(\rho))=\lambda,
> \]
>
> and the root sets of the \(F_\lambda\) are pairwise disjoint and exhaustive.
>
> Each \(F_\lambda\) has a full, key-free \(\Phi\)-development whose lower hull is its single side of slope \(\lambda=u'/e'\). If its normalized residual is mixed, its roots decompose further into their actual label classes:
>
> \[
> F_\lambda=\prod_{r'}F_{\lambda,r'}.
> \tag{LABEL-PROD}
> \]
>
> Here \(F_{\lambda,r'}\in O[x]\) is monic and separable and its roots are exactly the roots in the \(r'\)-label class. Its root set is Galois-stable; the label-block root sets are pairwise disjoint and exhaustive.
>
> Put
>
> \[
> \nu_{\lambda,r'}
> =
> \frac{\deg F_{\lambda,r'}}{D}.
> \]
>
> The block theorem asserts that this is a positive integer and supplies a full development
>
> \[
> F_{\lambda,r'}
> =
> \Phi^{\nu_{\lambda,r'}}
> +
> \sum_{j<\nu_{\lambda,r'}}
> A^{(\lambda,r')}_j\Phi^j.
> \tag{LABEL-DEV}
> \]
>
> Its lower hull is its own single side of slope \(\lambda\) and length
>
> \[
> L(F_{\lambda,r'})=\nu_{\lambda,r'}.
> \tag{LABEL-LENGTH}
> \]
>
> After the prescribed frame and origin normalization, its own residual polynomial is
>
> \[
> R(F_{\lambda,r'};Y)
> =
> c_{\lambda,r'}\,r'(Y)^{k_{\lambda,r'}},
> \qquad
> c_{\lambda,r'}\in K^\times,
> \tag{LABEL-PURE}
> \]
>
> where
>
> \[
> \boxed{
> k_{\lambda,r'}
> =
> \frac{\nu_{\lambda,r'}}{e'\deg r'}
> =
> \frac{\deg F_{\lambda,r'}}
>        {De'\deg r'}
> \in\mathbf Z_{\ge1}.}
> \tag{LABEL-OWN}
> \]
>
> This is the HE7-13′ block calculation. No equality between
>
> \[
> k_{\lambda,r'}
> \quad\text{and}\quad
> m_{\lambda,r'}
> \]
>
> from the parent residual factorization is assumed. In particular, neither
>
> \[
> \nu_{\lambda,r'}=e'm_{\lambda,r'}\deg r'
> \]
>
> nor the former `(LABEL-DEG)` is a carrier hypothesis or a conclusion of this master.
>
> Each block inherits the window, cap, occupied-height, legal-lift, test, accounting, and root-preserving continuation assertions needed for its own read. Its accounting identity is
>
> \[
> \sum_{\rho:F_{\lambda,r'}(\rho)=0}
> \min(d(\Phi(\rho)),\kappa)
> =
> D\nu_{\lambda,r'}\min(\lambda,\kappa).
> \tag{LABEL-ACCOUNT}
> \]
>
> A multi-side split or mixed-label split preserves the polynomial product and the disjoint exhaustive root partition. If it is nontrivial, every emitted block has degree strictly smaller than the unsplit state.
>
> The parent multiplicities in `(RES-FACT)` may be recorded as parent residual data, but terminality and continuation of \(F_{\lambda,r'}\) are decided only from the exponent \(k_{\lambda,r'}\) in the block’s own normalized residual `(LABEL-PURE)`.

Replace S1.8’s mixed-residual paragraph by:

> At a multi-side state, first apply `(SIDE-PROD)`. At a mixed side, next apply `(LABEL-PROD)`. Every emitted label block is read from its own development and residual data. A block with
>
> \[
> k_{\lambda,r'}=1
> \]
>
> has separable residual \(c_{\lambda,r'}r'\) and is terminal by clause 2. A block with
>
> \[
> k_{\lambda,r'}\ge2
> \]
>
> is continued independently by the product-\(1\)/product-\(\ge2\) alternatives. No decision is made from the multiplicity of \(r'\) in the parent residual.

Replace clause 4 of HE7.A by:

> 4. a state with more than one side is first replaced by its side blocks \(F_\lambda\) using `(SIDE-PROD)`. A mixed side is then replaced by the monic blocks \(F_{\lambda,r'}\) using `(LABEL-PROD)`. Each label block has its own pure residual
>
>    \[
>    c_{\lambda,r'}r'^{\,k_{\lambda,r'}},
>    \qquad
>    k_{\lambda,r'}
>    =
>    \frac{\deg F_{\lambda,r'}}
>         {De'\deg r'}.
>    \]
>
>    The block is terminal when \(k_{\lambda,r'}=1\), and is continued by clause 3 when \(k_{\lambda,r'}\ge2\). No equality with the parent residual multiplicity is used;

In the proof, replace the r1 mixed-residual passage with:

> If the hull has several sides, invoke `(SIDE-PROD)` before applying any single-side continuation. If a resulting side residual is mixed, invoke `(LABEL-PROD)`. The emitted label block \(F_{\lambda,r'}\) is read using its own exponent \(k_{\lambda,r'}\) from `(LABEL-OWN)`.
>
> If \(k_{\lambda,r'}=1\), its normalized residual is \(c_{\lambda,r'}r'\), so the separable-side argument gives one orbit of size
>
> \[
> De'\deg r'.
> \]
>
> If \(k_{\lambda,r'}\ge2\), clause 3 applies to that block alone. The product identities and disjoint root partitions ensure that no side or companion label is lost, duplicated, recentered, or absorbed.

---

## r2 repair 3 — add the mid-chain key-divides peel

Insert in S1.8 immediately before the paragraph beginning “The states carry a well-founded rank”:

> ### Mid-chain boundary produced by recentering
>
> Key-freeness is required before applying `(WINDOW)`, `(ACCOUNT)`, or a Newton-side read. It need not persist automatically after replacing a key by a recentered key.
>
> Let a recursive state have current monic key \(\widetilde\Phi\) of degree \(D\) and monic separable represented polynomial
>
> \[
> G
> =
> \widetilde\Phi^\nu
> +
> \sum_{j<\nu}C_j\widetilde\Phi^j.
> \]
>
> Before invoking the window, test whether
>
> \[
> \widetilde\Phi\mid G.
> \]
>
> In that case put
>
> \[
> G'=\frac{G}{\widetilde\Phi}.
> \tag{MID-PEEL}
> \]
>
> Then \(G'\in O[x]\) is monic,
>
> \[
> \deg G'=D(\nu-1),
> \qquad
> \mu(G')=\nu-1,
> \tag{MID-MASS}
> \]
>
> and separability of \(G\) gives
>
> \[
> \gcd_{K_0[x]}(G',\widetilde\Phi)=1.
> \]
>
> Thus \(G'\) is the next key-free state. Its represented roots are the roots of \(G\) not lying on the peeled current-key boundary. The roots on that boundary are emitted through the state’s certified key-boundary/orbit decomposition; the monic key itself is not declared irreducible merely because it is a key.
>
> This is the HE6R1-3/HE7-8 `[r3]` mid-chain peel. The value
>
> \[
> d(\widetilde\Phi(\rho))=+\infty
> \]
>
> is never fed into `(WINDOW)`: the boundary branch is taken first.
>
> If a proper nontrivial gcd with \(\widetilde\Phi\), rather than the whole key, occurs, use the general key-boundary decomposition of S1.9 before any window assertion.

Replace the well-founded-rank paragraph of S1.8 by:

> The states carry a well-founded lexicographic rank. The permitted nonterminal transitions are:
>
> 1. a nontrivial side split, which strictly decreases represented degree;
> 2. a nontrivial label split, which strictly decreases represented degree;
> 3. a mid-chain key-boundary peel `(MID-PEEL)`, which changes
>
>    \[
>    \nu\longmapsto\nu-1;
>    \]
>
> 4. a product-\(\ge2\) child jump, which strictly decreases mass, or a product-\(1\) linear recentering, which strictly decreases the finite secondary discriminant/slope rank.
>
> Every transition preserves the represented roots or partitions them into explicitly disjoint exhaustive child root sets, and transports the corresponding polynomial product. Consequently there is no infinite branch.

Insert a new clause before the termination clause of HE7.A, renumbering the old clause 5 as clause 6:

> 5. if a recentered current key divides its represented block, the algorithm performs `(MID-PEEL)` before asserting `(WINDOW)`. The quotient is key-free and has mass smaller by one; the peeled boundary roots are discharged by their certified boundary/orbit decomposition;

Replace the induction’s final paragraph by:

> Finally apply well-founded induction to the rank of a state. A terminal separable class yields the irreducible factor proved in clause 2.
>
> A multi-side split invokes `(SIDE-PROD)`; a mixed-label split invokes `(LABEL-PROD)`. In either case every emitted block has smaller represented degree, and the product identity reassembles the exhaustive child factorizations.
>
> In the mid-chain key-divides case, `(MID-PEEL)` emits the certified boundary factors and replaces \(G\) by the key-free quotient \(G'\), whose mass is \(\nu-1\). The induction hypothesis applies to \(G'\). This case is taken before `(WINDOW)`, so no infinite key value enters the Newton-side argument.
>
> A product-\(1\) linear refinement preserves its represented roots and decreases the secondary rank. A product-\(\ge2\) child jump replaces its state by finitely many smaller-mass states. The induction hypothesis applies in each case. All product identities and root partitions are disjoint and exhaustive, so their terminal factors multiply to the parent polynomial.

---

## r2 repair 4 — fence the unsupported level-one label-block carrier

Insert after S1.7A:

> ### S1.7B Named level-one block obligation
>
> The generic carrier hypothesis in S1.7A is not inferred from label equivariance, class cardinalities, or the existence of HE6 test polynomials.
>
> For the HE3+HE6 level-one records, denote the missing assertion by
>
> \[
> \boxed{\operatorname{LB}_1(\mathrm{HE3{+}HE6}).}
> \tag{LB1}
> \]
>
> It is the assertion that every mixed nonseparable level-one side has the monic side and label blocks of S1.7A, with their own full developments, pure residuals, product identities, disjoint exhaustive root partitions, and inherited continuation data.
>
> None of `HE3-A-STMT`, `HE3-A-PROOF`, `HE3-DEF1`, `HE3-HE3-1L`, `HE3-HE3-6`, `HE3-R8-2`–`HE3-R8-5`, `HE6-FAMILY`, `HE6-PROOF`, or `HE6-SLOT-SEAM` is claimed to prove `(LB1)`. HE6.A step 1 supplies the separable read, and the repeated-linear class-size calculation does not manufacture a monic label block.
>
> Consequently the HE3.A and HE6 instance records are unconditional for separable sides and for already-pure repeated sides. Their application to a mixed nonseparable level-one side is conditional on the separately supplied obligation `(LB1)`.
>
> At level two, `HE7-MIXED-13P` supplies the corresponding carrier through ANNEX-LEMMA HE7-13′. For the partial-tower instance, `GENTOW-4-A` is deliberately the span of the complete theorem, including GENTOW-4.A(i), which supplies the bouquet blocks. Neither source is used to prove `(LB1)` retroactively at level one.

Append to S3.1 and S3.2:

> **Level-one fence.** This record does not discharge `(LB1)`. Therefore no mixed nonseparable level-one state is advertised as an unconditional instance of clause 4. Such a state may enter only after `(LB1)` has been supplied as an additional named instance obligation.

Replace the relevant S3.3 sentence by:

> ANNEX-LEMMA HE7-13′ supplies the level-two side and per-label blocks with their own residual exponents `(LABEL-OWN)`. It does not supply, and this record does not use, an equality between those exponents and multiplicities in a parent residual polynomial. HE6R1-3 together with HE7-8 `[r3]` supplies the mid-chain peel `(MID-PEEL)`.

Replace the GENTOW4 bouquet sentence by:

> GENTOW-4.A(i), contained in the existing-text span `GENTOW-4-A`, supplies the monic bouquet blocks
>
> \[
> f=\prod_{(\kappa,r)}f_{\kappa,r}.
> \]
>
> This is the block carrier used by the partial-tower instance; it is not inferred from GENTOW-4.2.

---

## r2 repair 5 — strengthen KEY-BOUNDARY’s declared hypotheses

In S1.9, after “A key-boundary decomposition consists of”, insert:

> Every residual block \(B_j\) is a σ-block for the same carrier and satisfies the complete HE7.A input suite applicable to that block: its full development, point condition, key-freeness, window and cap safety, frame and origin data, occupied-height and lift conditions, residual-degree identity, accounting identity, test assertions, and root-preserving continuation assertions. Where a side or label split is invoked, the applicable S1.7A block theorem is also part of the residual block’s data.

Replace the first sentence of T2.KEY-BOUNDARY by:

> Let \(F\) be a monic separable input with a key-boundary decomposition `(BOUNDARY-PROD)`, and suppose every residual block \(B_j\) satisfies the full HE7.A hypothesis suite declared in S1.9.

---

## r2 repair 6 — invoke the fundamental identity in the orbit count

Replace the paragraph beginning “The test assertions give nonempty” by:

> The test assertions give nonempty, disjoint, exhaustive, Galois-stable classes \(S_{\lambda,r'}\). Choose a root \(\rho\) in one Galois orbit \(\Omega\subseteq S_{\lambda,r'}\). Since \(K_0\) is complete discretely valued and the orbit extension is finite separable, the fundamental identity gives
>
> \[
> |\Omega|
> =
> [K_0(\rho):K_0]
> =
> e(\rho/K_0)f(\rho/K_0).
> \tag{FUND}
> \]
>
> Local forcing says
>
> \[
> e_{\mathcal C}e'\mid e(\rho/K_0),
> \qquad
> f_{\mathcal C}\deg r'\mid f(\rho/K_0).
> \]
>
> Hence, using `(DEG-EF)`,
>
> \[
> |\Omega|
> \ge
> (e_{\mathcal C}e')
> (f_{\mathcal C}\deg r')
> =
> De'\deg r'.
> \]
>
> Thus every orbit contained in \(S_{\lambda,r'}\) has at least \(De'\deg r'\) elements, and in particular
>
> \[
> |S_{\lambda,r'}|\ge De'\deg r'.
> \]

After obtaining equality for the class, replace the one-orbit conclusion by:

> Since every orbit in the nonempty class has at least \(De'\deg r'\) elements and the entire class has exactly that cardinality, the class contains exactly one orbit. Moreover `(FUND)` and the two divisibilities have product equal to \(De'\deg r'\); therefore both divisibilities are equalities:
>
> \[
> e(\rho/K_0)=e_{\mathcal C}e',
> \qquad
> f(\rho/K_0)=f_{\mathcal C}\deg r'.
> \]

---

## r2 repair 7 — bind the level-one vocabulary and repair \(\vartheta_s\)

Insert immediately before the level-one formula in S1.2:

> The following paragraph is level-one instance notation, not unbound master vocabulary. Fix positive integers
>
> \[
> e_1,\ f_1,\ D',\ h,
> \qquad
> D'=e_1f_1,
> \qquad
> \gcd(h,e_1)=1,
> \]
>
> and a monic polynomial \(\Phi'\in O[x]\) of degree \(D'\). The symbol \(\pi\) is the ground uniformizer fixed in S1.1. Define the level-one integer-normalized coefficient height by
>
> \[
> dv\!\left(\sum_j a_jx^j\right)
> =
> \min_j\{e_1v(a_j)+jh\}.
> \]
>
> Fix the HE6 print normalizer
>
> \[
> \varpi\in K_0(x)^\times,
> \qquad
> dv(\varpi(\xi))=1,
> \]
>
> the residual letter
>
> \[
> \eta\in K^\times,
> \qquad
> \eta_\xi=\iota_\xi(\eta),
> \]
>
> and the integer-valued comparison function \(q(k)\) characterized on the occupied heights by
>
> \[
> \operatorname{res}\!\left(
> \frac{n(k)(\xi)}{\varpi(\xi)^k}
> \right)
> =
> \eta_\xi^{-q(k)}.
> \tag{Q-DEF}
> \]
>
> These objects are supplied by the HE3+HE6 instance and are used only in `(GAMMA)` and `(HE6-SEAM)`.

Replace the first two sentences of S1.3’s next-step-normalizer paragraph by:

> For a next-step numerator \(u\), let \(\vartheta_s\in K^\times\) be the source-supplied element independent of \(\xi\) characterized by
>
> \[
> \boxed{
> \iota_\xi(\vartheta_s)
> =
> \operatorname{res}\!\left(
> \frac{n(u)(\xi)^s}{n(su)(\xi)}
> \right)}
> \tag{THETA-EVAL}
> \]
>
> for every relevant \(\xi\in\operatorname{Pt}\), and put
>
> \[
> \Theta_s=\vartheta_s^{-1}.
> \]

Add \(\gcd(h,e_1)=1\) to the boxed HE3 and HE6 instance data.

---

## r2 repair 8 — make the multi-side induction branch explicit

In addition to `(SIDE-PROD)` above, insert before the mixed-label part of the proof:

> A recursive state is not silently treated as single-sided. If its complete lower hull has at least two sides, `(SIDE-PROD)` is invoked first. Every side block has strictly smaller represented degree, so the induction hypothesis applies separately to all of them. Their root sets are disjoint and exhaustive and their polynomials multiply to the state polynomial. Only after this side split is a residual factorization read and, when necessary, a label split performed.

Add to S5:

> 13. Multi-side states invoke `(SIDE-PROD)` as an explicit degree-decreasing induction case.
>
> 14. Label-block terminality uses the block-owned exponent `(LABEL-OWN)`, never the parent residual multiplicity.
>
> 15. A recentered key-divides state invokes `(MID-PEEL)` before `(WINDOW)`; its mass decreases by one.
>
> 16. Mixed nonseparable level-one reads remain conditional on the named obligation `(LB1)`.

In S4.1, replace “the five pinned source displays give the intended substitutions” by:

> the pinned source displays give the intended substitutions subject to the explicitly named level-one obligation `(LB1)`; HE3.A and HE6 are not represented as unconditional mixed-nonseparable label-block instances.


---

## r3 (2026-08-12): pin re-derivation + (MID-PEEL) suite + (LB1) widening

*(Fable-arm; counter resets.)*

## r3 repair 1 — F1+F2 (GAPs): the four defective pins re-derived as verbatim existing-text delimiter pairs

The r2 `(PINS)` table named four units that do not occur in their sources under those descriptions. Each is re-derived below from its actual consumption site in this master. Both delimiter lines of every pin are quoted byte-exactly from the accepted source and were verified by exact-full-line search on 2026-08-12: each occurs exactly once in its file, and each begin precedes its end. One pin resolves into two, so the inventory grows from 26 to 27.

**(a) `HE7-SLOT-TRANSFER`.** Consumption: the S3.3 sentence "the slot is `(SLOT₂)`, and the legal lift domain is `(FULL2)`, with `(FULL2-U)` as a uniform sufficient bound." The consumed source units are the **(SLOT₂) and (LIFT₂) statement displays**, which live in HE7 §S1 (the level-2 frame section, not §S2) and are introduced there as one bundle by the source sentence "The two lemmas HE6 §S7.2 named as its exact residue, stated here in full." The (LIFT₂) display's (†₂)/(‡₂) are exactly this master's `(FULL2)`/`(FULL2-U)`. The pin is NOT ANNEX-THEOREM R1-b: the composed instance is level-two, where ANNEX-COROLLARY R1-d certifies "levels 1 and 2 are byte-unchanged"; the level-\(i\) restatement enters only through the cocycle-chain pin (b). Delimiters:

- first: `> **(SLOT₂) [PROVED, §S3].** Let C ∈ O[x] with deg C < D″ and let`
- last: `> HE7-T-LIFT2SHARP verifies the exact reachable set by enumeration.`

The span contains both complete displays; the capture of (LIFT₂) beyond the pin's short name is over-capture licensed by condition 4 (see repair 2), and it is itself consumed.

**(b) `HE7-COCYCLE-2P-THROUGH-R1D`.** No source unit named "ANNEX 2-P" exists; the r2 description corrupted the name of **ANNEX-DEF HE7-2′**. The chain's actual endpoint units, named verbatim: **ANNEX-DEF HE7-2′** (the corrected level recursion) and **ANNEX-COROLLARY R1-d** (THEOREM HE7.D and COROLLARY HE7.B(ii), re-proved). Delimiters:

- first: `> **ANNEX-DEF HE7-2′ (the corrected level recursion; replaces DEFINITION`
- last: `> box, per the honesty invariant.`

The span contains, in source order, ANNEX-DEF HE7-2′, ANNEX-LEMMA R1-a, ANNEX-THEOREM R1-b, ANNEX-THEOREM R1-c, the R1.2 twist-blindness audit, and ANNEX-COROLLARY R1-d — the complete corrected cocycle chain this master consumes at `(COC-DEF)`/`(BETA)` and in S3.3 ("the cocycle ... equals the nontrivial \(\beta^c\) twist").

**(c) `HETOW-LABELS`.** The master consumes two distinct HETOW units, so this pin resolves into two (inventory 26 → 27).

`HETOW-LABELS` := **the §S1 instantiation-map unit** — the tower setting plus the row-by-row dictionary table. It supplies the boxed `(HETOW-INSTANCE)` data: \(K_2\cong\mathbf F_{Q^{f_1f_2}}\), the wrap-corrected key \(\Phi_2\), \(D_2=D'e_2f_2\), \((e_{\mathcal C},f_{\mathcal C})=(e_1e_2,f_1f_2)\), \(dv_2=e_1e_2v\), \(T_2=e_2f_2u_2\). Delimiters:

- first: `## S1. THE INSTANTIATION MAP (every hypothesis of DEFINITION HE7-1 + THEOREM HE7.A at the composed data)`
- last: `sealed table was sound only on the battery's η = 1 gauge.`

Note at the pin: the span contains the superseded J-D0 normalizer row. This master does not consume that row — its normalizer comparison enters only through `HETOW-NORMALIZER-4` (the HETOW-4 bridge), exactly as S3.4 states.

`HETOW-LABELS-1` := **LEMMA HETOW-1 (label translation)**, statement and proof. It supplies the transported letter \(\beta=\eta^{-Q(u_2)}\eta_2\) and its minimal polynomial \(\widetilde r\), as consumed by S3.4. Delimiters:

- first: `> **LEMMA HETOW-1 (label translation) [r1 2026-08-09 (passPE1 F-1)`
- last: `σ = {(4,1)} ≠ {(2,2)}. ∎`

Amend the S3.4 source-pin line to: **Source pins:** `HETOW-LABELS`, `HETOW-LABELS-1`, `HETOW-A`, and `HETOW-NORMALIZER-4`.

**(d) `GENTOW-ACCEPTANCE-FOLD`.** The source carries two bracketed fold units ("[acceptance fold (post-PE3) 2026-08-10, m-i — THE CITATION COMPLETED ...]" at the 4.C proof line, and "[acceptance fold (post-PE3) 2026-08-10, m-ii — INSTRUMENT-STRENGTH DISCLOSURE ...]" at the S9 head). This master consumes neither bracket's content; its only consumption is the S4.1 grade line "GENTOW4 is accepted \(2/2\)". The unit carrying that grade is the dated record **"### Dated acceptance record (2026-08-10, post-PE3)"** ("GENTOW4 IS ACCEPTED 2/2 ... two consecutive clean hostile passes"), which also names both fold brackets at their sites. The pin is therefore that record. Delimiters:

- first: `### Dated acceptance record (2026-08-10, post-PE3)`
- last: `dated brackets only from here.`

(The record ends immediately before the next `###` unit, the TOWERRAT2-C annex.)

Replace the four corresponding rows of the r2 `(PINS)` table by the five entries above; replace "The 26 pins are the following existing-text pairs" by "The 27 pins are the following existing-text pairs"; and in the S7 pin gate replace "The expected pin count is 26" by "The expected pin count is 27".

---

## r3 repair 2 — F3 (minor): unit types "display" and "record", and the nesting rank rule

In S0.2's unit-boundary sentence, extend the type list: "a theorem, lemma, definition, numbered clause, proof, annex, or redline unit" becomes "a theorem, lemma, definition, numbered clause, proof, annex, redline, **named statement display, or dated record** unit". Append to S0.2:

> When units nest, the pin resolves to the OUTERMOST unit bearing the pin's named designation: an inner unit does not truncate a span whose named unit contains it. A span may properly contain other complete units (over-capture) provided condition 4 holds for the named unit. A section-separating horizontal-rule line is a boundary marker, not unit content: a unit's last delimiter is the last nonblank content line before such a boundary.

---

## r3 repair 3 — F4 (minor): the HE6R1-1 competing re-display, noted at the pin

Add at pin `HE6R1-1`:

> The source HEAD carries the "Dated statement re-display (2026-08-12, R7 finding 1 — LEMMA HE6R1-1's global bound)", which re-displays the lemma's global jump bound as three clauses (\(J\le\log_2\mu-1\) in any history; \(J\le\log_2 n-2\) for stage-rooted ladders, \(D'\ge2\); \(J\le\log_2 n-1\) ambient-rooted, sharp). **The 2026-08-12 statement re-display governs.** The clauses this master consumes — the widened jump condition \(\ell_i\deg r_i\ge2\) and the descent \(\mu_{i+1}\le\mu_i/2\) feeding `(MASS)` — are byte-unchanged by the re-display; this master never cites the global \(\log_2 n-2\) form.

---

## r3 repair 4 — F5 (GAP): the (MID-PEEL) carrier suite

r2 repair 5 declared the full input suite for the boundary blocks of S1.9, but the mid-chain peel's quotient received no such declaration: `(MID-PEEL)` produced \(G'\) with only key-freeness and mass proved. Insert into S1.8's "Mid-chain boundary produced by recentering", immediately after the paragraph ending "the monic key itself is not declared irreducible merely because it is a key":

> **(MID-PEEL) input suite.** The peel supplier certifies for the quotient \(G'\) the same carrier data that S1.9 demands of a boundary block:
>
> 1. key-freeness: \(\gcd_{K_0[x]}(G',\widetilde\Phi)=1\);
> 2. `(WINDOW)` for \(G'\): every root \(\rho\) of \(G'\) satisfies \(T<d(\widetilde\Phi(\rho))<\infty\);
> 3. \(G'\)'s own full development and its accounting identity `(ACCOUNT)`;
> 4. the test assertions of S1.7 for \(G'\)'s sides and labels, with the occupied-height, lift, frame, origin, and residual-degree data;
> 5. the peeled key's certified orbit/(e,f) decomposition: the emitted boundary factor's irreducibility, simplicity, and local invariants.
>
> None of this is inferred from the peel identity `(MID-PEEL)` alone. At level two the instance discharge is **LEMMA HE6R1-3**: \(\Psi\mid f_S\) forces \(\gcd(f_S,\Psi)=\Psi\) with \(\Psi\) irreducible over \(O\) of degree \(D''\), a simple factor with \(e(\Psi)=e_1\ell\) and \(f(\Psi)=f_1d_r\), and \(f_S'=f_S/\Psi\) key-free with every root still a level-2 point and "THEOREM HE7.A applies to \(f_S'\) with \(\mu_2-1\) in place of \(\mu_2\)" — the source's own assertion that the complete input suite holds for the quotient. That lemma is cited as the instance discharge of this suite.

---

## r3 repair 5 — F6 (minor): the ν = 1 degenerate guard

Insert into the same subsection, immediately after the display `(MID-MASS)`:

> **Degenerate guard.** If \(\nu=1\), then \(G'=1\): the peel emits the certified boundary factors and no successor state exists — the state is decided. This is LEMMA HE7-8's `[r3]` clause "μ₂ = 1 is decided, so at most μ₂ − 1 peels ever fire" in master notation. `(MID-MASS)` and the continuation to a key-free successor apply only at \(\nu\ge2\).

---

## r3 repair 6 — F7 (GAP): (LB1) widened to every clause-4-demanding level-one state

r2 repair 4 fenced only "mixed nonseparable" level-one sides, but repair 8's split-first discipline makes clause 4 demand side-block developments at EVERY multi-side state — including states whose side residuals are each individually separable or already pure. No level-one pin supplies those side-block developments. Replace S1.7B's sentence "It is the assertion that every mixed nonseparable level-one side has the monic side and label blocks of S1.7A, with their own full developments, pure residuals, product identities, disjoint exhaustive root partitions, and inherited continuation data." by:

> It is the assertion that every level-one state whose clause-4 processing demands blocks — every state with at least two sides, and every side whose residual is mixed — has the monic side and label blocks of S1.7A, with their own full developments, single-side hulls, pure residuals, product identities, disjoint exhaustive root partitions, and inherited continuation data.
>
> The fence is not limited to nonseparable mixtures. A two-side level-one state whose sides carry, respectively, a separable residual and an already-pure repeated residual has each side individually within the level-one records' strength, yet its `(SIDE-PROD)` side-block developments are supplied by no level-one pin. That state is `(LB1)`-conditional.

Replace S1.7B's sentences "Consequently the HE3.A and HE6 instance records are unconditional for separable sides and for already-pure repeated sides. Their application to a mixed nonseparable level-one side is conditional on the separately supplied obligation `(LB1)`." by:

> Consequently the HE3.A and HE6 instance records are unconditional only for single-side level-one states whose residual is separable or already pure repeated. Every level-one state requiring a side split or a label split — multi-side states included — is conditional on the separately supplied obligation `(LB1)`.

In the S3.1/S3.2 "Level-one fence" appends, replace "Therefore no mixed nonseparable level-one state is advertised as an unconditional instance of clause 4." by "Therefore no level-one state requiring a side split or a label split is advertised as an unconditional instance of clause 4." In S5 item 16, replace "Mixed nonseparable level-one reads remain conditional on the named obligation `(LB1)`." by "Level-one reads demanding side or label blocks remain conditional on the named obligation `(LB1)`."

---

## r3 repair 7 — F8 (minor): the clause-1/2 direct read and the split-first algorithm reconciled

Insert immediately after r2 repair 8's inserted paragraph ("A recursive state is not silently treated as single-sided. ..."):

> Clauses 1 and 2 remain direct statements about the unsplit hull of \(F\): their proofs run on \(F\) itself through `(ACCOUNT)`, `(SIDE-COUNT)`, `(RES-DEG)`, and the test assertions, with no appeal to `(SIDE-PROD)`. The recursive algorithm nevertheless follows the split-first discipline above. The two routes agree: by `(SIDE-PROD)` the roots of \(F_\lambda\) are exactly the side-\(\lambda\) roots of \(F\), and labels attach to roots pointwise (S1.7, clause 1), so the label classes read on the block \(F_\lambda\) are the same root sets as the classes read directly at side \(\lambda\) of \(F\); clause 2 applied to either returns the same Galois orbits with the same \((e,f)\). The algorithm text follows repair 8; the direct read is retained as the stated form of clauses 1–2.

---

## r3 repair 8 — F9 (minor): clause 3's "repeated"/"multiplicity" bound to the block's own residual

Add, as a reading directive attached to clause 3 of HE7.A and to S1.8's opening sentence:

> In clause 3 and in S1.8's "Suppose \(r'\) occurs in \(R_\lambda\) with multiplicity at least two", the hypothesis is read at the state's OWN normalized residual: the state is a single-side block, and "repeated" means that the exponent of \(r'\) in its own residual — \(k_{\lambda,r'}\) of `(LABEL-PURE)`/`(LABEL-OWN)` for an emitted label block, the exponent in its own `(RES-FACT)` for an unsplit pure side — is at least \(2\). A multiplicity recorded in a parent residual factorization triggers nothing: parent data decides neither terminality nor continuation. This binds clause 3's wording to r2 repair 2's discipline.

---

## r3 repair 9 — F10 (minor): the six file-path bindings restored

The r2 S0.2 replacement closes with "These pins lie in the six files listed below `(PINS)`" but deleted the list itself with the old S0.2. Insert, immediately after the `(PINS)` table of S0.2:

> These pins lie in:
>
> \[
> \begin{aligned}
> &\texttt{lean/notes/openmath/HE3\_PROOF\_2026-08-08.md},\\
> &\texttt{lean/notes/openmath/HE6\_PROOF\_2026-08-08.md},\\
> &\texttt{lean/notes/openmath/HE7\_PROOF\_2026-08-08.md},\\
> &\texttt{lean/notes/openmath/HE6R1\_RECON\_2026-08-08.md},\\
> &\texttt{lean/notes/openmath/HETOW\_RECON\_2026-08-09.md},\\
> &\texttt{lean/notes/openmath/GENTOW4\_PROOF\_2026-08-09.md}.
> \end{aligned}
> \]


---

## r4 (2026-08-13): pin adjudication + the clause-5 trigger + the displayed rank + the level-one peel fence

*(Opus/Claude repair arm, against the r3 hostile pass of record `runs/comp13/T2P3_output.log` — 0 CRITICAL + 4 GAP + 8 minor; counter resets.)*

**Verification protocol for this round.** Every delimiter line quoted below was checked on 2026-08-13 by exact-full-line search in the named accepted source file, and both the command and its count are recorded at the pin. No source file is edited by this round; the expected source edit count remains zero.

---

## r4 repair 1 — A-3 (GAP): `HE6-SLOT-SEAM` adjudicated to LEMMA HE6-0″ and re-derived as a byte-exact delimiter pair

The r2 description "the corrected normalized-slot/seam display" resolves against three distinct corrected slot/seam units of `HE6_PROOF_2026-08-08.md`, so condition 1 of S0.2 ("its named source unit occurs exactly once in the named file") could not be discharged. The pin is adjudicated by its consumption, not by its wording.

**What this master consumes at this pin.** S1.2 consumes two clauses about a *given* \(A\): the exact height law `(SLOT-V)`, \(d(A(\xi))=h(A)\) with \(h\) the level-one \(dv\)-minimum, and the print-frame conversion `(HE6-SEAM)`,

\[
\operatorname{res}\!\left(\frac{A(\xi)}{\varpi(\xi)^k}\right)
=
\iota_\xi(\gamma_k(A))\,\eta_\xi^{-q(k)} .
\]

S3.2 restates exactly these two ("Its coherent slot digit is exactly `(GAMMA)`. The print-frame read is exactly \(\operatorname{res}(A/\varpi^k)=\iota(\gamma_k(A))\eta^{-q(k)}\)").

**Adjudication.** Only **LEMMA HE6-0″ (THE SLOT LEMMA at (T1)/(T2) POINTS)** carries both consumed clauses in one unit: the exact height law at an arbitrary \(A\) and an arbitrary (T1)/(T2) point, and the \(\varpi\)-read residue \(\iota_\xi(\gamma)\eta_\xi^{-q}\) with the `[r2]` sign correction that this master's minus sign reproduces. Its own head calls it "the form this note actually consumes". The two competing candidates are declined for stated reasons, so that no later reader re-opens the choice:

- HE6's §S1 **CONVENTION (ϖ-normalizers: twist-free)** fixes \(\varpi\) and constructs \(R_\lambda\). It is a Newton-side residual assembly — this master's `(RES-FACT)` input — and states no per-\(A\) slot law and no \(\eta^{-q}\) conversion. This master pins its \(R_\lambda\) construction at HE3 instead, through `HE3-DEF1` (repair 5). This unit is separately pinned by repair 4, for its peel clause only.
- **LEMMA HE6-1L** with its **RIDER** is the reachability/lift lemma: it describes the *set* of residues realised at a height, i.e. this master's `(LIFT)`/`(OCC)` data, and its RIDER records the \(\varpi\)-vs-\(n(k)\) ratio as one fixed element of \(K\). It does not evaluate a given \(A\). This master's full-height criterion (S1.4, "\(k\ge(i(k)+e_1(f_1-1))h\)", "\(k\ge(D'-1)h\) is uniformly sufficient") is already pinned at its level-one counterpart `HE3-HE3-1L`, whose statement carries that threshold verbatim.

**The pin.** Replace the r2 `(PINS)` row

> `&\texttt{HE6-SLOT-SEAM}&\text{the corrected normalized-slot/seam display}\\`

by

> `&\texttt{HE6-SLOT-SEAM}&\text{LEMMA HE6-0″ (THE SLOT LEMMA at (T1)/(T2) POINTS), statement and proof}\\`

with delimiters:

- first: `> **LEMMA HE6-0″ [r1, R5/F6] (THE SLOT LEMMA at (T1)/(T2) POINTS — the form`
- last: `> restatement.**`

**Verification remark.** In `lean/notes/openmath/HE6_PROOF_2026-08-08.md`, on 2026-08-13:
`grep -cFx '> **LEMMA HE6-0″ [r1, R5/F6] (THE SLOT LEMMA at (T1)/(T2) POINTS — the form' HE6_PROOF_2026-08-08.md` → **1**;
`grep -cFx '> restatement.**' HE6_PROOF_2026-08-08.md` → **1**;
the first delimiter precedes the last, and the span contains the complete lemma — statement, the `[r2]` sign correction and its witness, the proof, and the Codex-PE1-finding-6 restatement note — ending immediately before the next sibling unit, LEMMA HE6-0 (the disk criterion). Conditions 1–4 of S0.2 hold.

---

## r4 repair 2 — B-1 (GAP): clause 5's trigger extended to the child-jump key-divides route

Clause 5 as installed by r2 repair 3 fires only when "a **recentered** current key divides its represented block". The level-two discharge that r3 repair 4 cites for the `(MID-PEEL)` input suite — **LEMMA HE6R1-3**, hypothesis \(\Psi\mid f_S\) — is not a recentering: \(\Psi=\Psi_{\lambda,r}\) is the test polynomial promoted to child key by S1.8's product-\(\ge2\) branch. The theorem statement therefore did not cover the case its own cited discharge is about, while the section body ("Let a recursive state have current monic key \(\widetilde\Phi\) … test whether \(\widetilde\Phi\mid G\)") and the induction paragraph ("In the mid-chain key-divides case, `(MID-PEEL)` emits …") already do.

This repair widens the trigger to what the body proves. It adds a trigger case; it adds no conclusion, and the mechanism it invokes is the one already stated in S1.8 and already carried in the induction.

**First, prove that these are the only two triggers.** Insert into S1.8's "Mid-chain boundary produced by recentering", immediately after the paragraph beginning "Key-freeness is required before applying `(WINDOW)`":

> Exactly two transitions can destroy key-freeness, so exactly two need the test. A nontrivial side or label split cannot: \(F_\lambda\mid F\) by `(SIDE-PROD)` and \(F_{\lambda,r'}\mid F_\lambda\) by `(LABEL-PROD)`, so any common divisor of an emitted block and \(\Phi\) is a common divisor of \(F\) and \(\Phi\), and `(KEY-FREE)` gives \(\gcd_{K_0[x]}(F,\Phi)=1\). `(MID-PEEL)` itself cannot: its output satisfies \(\gcd_{K_0[x]}(G',\widetilde\Phi)=1\), so the peel never fires twice in succession at one key. What remains are the two transitions that replace the key: the product-\(1\) linear recentering \(\Phi\mapsto\Phi-L_k(s)\), which keeps the block and changes the key, and the product-\(\ge2\) child jump \(\Phi\mapsto\Psi_{\lambda,r'}\), which changes both. Both are tested.

Insert also, immediately after the display \(\gcd_{K_0[x]}(G',\widetilde\Phi)=1\) in the same subsection, the derivation the effective text asserted in one word:

> (If an irreducible \(p\in K_0[x]\) divided both \(G'\) and \(\widetilde\Phi\), then \(p^2\mid\widetilde\Phi G'=G\), contradicting separability of \(G\). This is the full gcd condition, not merely \(\widetilde\Phi\nmid G'\), so `(KEY-FREE)` holds for \(G'\) even at a reducible key.)

**Then replace clause 5 of HE7.A** (installed by r2 repair 3) by:

> 5. if the current key divides its represented block, the algorithm performs `(MID-PEEL)` before asserting `(WINDOW)`. The test is applied after each of the two transitions that can destroy key-freeness — the product-\(1\) linear recentering and the product-\(\ge2\) child jump — and is not needed after any other, key-freeness being preserved by side and label splits and by `(MID-PEEL)` itself. The quotient is key-free, its mass is smaller by one, and its represented degree is smaller by \(D\); the peeled boundary roots are discharged by their certified boundary/orbit decomposition, which is item 5 of the `(MID-PEEL)` input suite and is a hypothesis of this clause, not a consequence of the peel identity;

**And replace S5 ledger item 15** ("A recentered key-divides state invokes `(MID-PEEL)` before `(WINDOW)`; its mass decreases by one.") by:

> 15. A key-divides state — arising from a linear recentering or from a child jump — invokes `(MID-PEEL)` before `(WINDOW)`; its mass decreases by one and its represented degree by \(D\). Side and label splits and `(MID-PEEL)` itself preserve key-freeness and need no test.

**Instance consequence.** The child-jump branch of the trigger is precisely LEMMA HE6R1-3's hypothesis, so r3 repair 4's cited discharge now discharges a case the theorem states. The recentering branch is discharged at level two by the `[r3]` interleaving clause of LEMMA HE7-8 (pinned by repair 3 below) and is **fenced at level one** by repair 4.

---

## r4 repair 3 — B-2 (GAP): the well-founded rank displayed as a tuple, with every transition checked against every component

r2 repair 3 asserts "The states carry a well-founded lexicographic rank" and then lists four transitions decreasing three different quantities, with no tuple, no order, and no check that a transition never increases an earlier component. As the text stood, nothing excluded a recentering/child-jump cycle in which each step decreases its own quantity while an earlier one grows back, and nothing explained why a peel may reset the secondary rank.

**Insert, in S1.8, immediately before the paragraph beginning "The states carry a well-founded lexicographic rank"**, the missing carrier datum:

> The secondary rank is carrier data, not master data. The carrier supplies
>
> \[
> \boxed{
> \sigma_{\mathcal C}:\{\text{states}\}\longrightarrow W_{\mathcal C},
> \qquad
> W_{\mathcal C}\ \text{well-founded},
> \qquad
> \sigma_{\mathcal C}(S')<\sigma_{\mathcal C}(S)}
> \tag{SEC-RANK}
> \]
>
> at every product-\(1\) linear recentering \(S\to S'\). Nothing is required of \(\sigma_{\mathcal C}\) at any other transition: it may rise, or be reset, freely. `(SEC-RANK)` is part of the root-preserving continuation assertions hypothesised by HE7.A; this master does not derive it, and any instance that cannot supply it does not instantiate HE7.A.

**Replace the well-founded-rank paragraph of S1.8** (the r2 repair 3 version) by:

> The states carry the lexicographic rank
>
> \[
> \boxed{
> \operatorname{rank}(S)
> =
> \bigl(\deg F_S,\ \mu_S,\ \sigma_{\mathcal C}(S)\bigr)
> \in
> \mathbf Z_{\ge1}\times\mathbf Z_{\ge1}\times W_{\mathcal C},}
> \tag{RANK}
> \]
>
> ordered lexicographically with the represented degree \(\deg F_S\) most significant, the mass \(\mu_S=\deg F_S/D_S\) next, and the carrier's secondary rank \(\sigma_{\mathcal C}(S)\) of `(SEC-RANK)` last. Here \(D_S=\deg\Phi_S>0\) is the degree of the state's own key, so the three components are read at the state's own carrier and \(\deg F_S=\mu_SD_S\) by `(DEV)`. A lexicographic product of well-founded orders is well-founded, so `(RANK)` is well-founded.
>
> The permitted nonterminal transitions, each checked against **every** component:
>
> 1. **Nontrivial side split** (`(SIDE-PROD)`, at least two sides). Degree: strictly down, since "if it is nontrivial, every emitted block has degree strictly smaller than the unsplit state" (S1.7A). Mass and secondary rank: unconstrained, and irrelevant, the first component having strictly decreased.
> 2. **Nontrivial label split** (`(LABEL-PROD)`, at least two distinct labels). Degree: strictly down, by the same S1.7A sentence. Mass and secondary rank: unconstrained.
> 3. **Mid-chain key-boundary peel** `(MID-PEEL)`, at \(\nu\ge2\). Degree: strictly down, since \(\deg G'=D(\nu-1)\) by `(MID-MASS)` while \(\deg G=D\nu\), and \(D=\deg\widetilde\Phi>0\) by S0.1. Mass: \(\mu(G')=\nu-1<\nu\) by `(MID-MASS)`, so this component also falls, though the first already suffices. Secondary rank: unconstrained — a peel may reset the refine chain's slope floor, and that is harmless precisely because the first component strictly decreased. The case \(\nu=1\) is excluded by the degenerate guard: the state is decided and has no successor.
> 4. **Product-\(\ge2\) child jump.** Degree: NON-INCREASING. The child key is \(\Psi_{\lambda,r'}\) with \(D_{\mathrm{child}}=\deg\Psi_{\lambda,r'}=De'\deg r'\) by `(TEST)`, and every nonterminal child satisfies \(\mu_{\mathrm{child}}\le\mu/(e'\deg r')\) by `(MASS)`; hence
>
>    \[
>    \deg F_{\mathrm{child}}
>    =
>    D_{\mathrm{child}}\mu_{\mathrm{child}}
>    \le
>    (De'\deg r')\frac{\mu}{e'\deg r'}
>    =
>    D\mu
>    =
>    \deg F .
>    \]
>
>    Mass: strictly down, \(\mu_{\mathrm{child}}\le\mu/2<\mu\) by `(MASS)` (and \(\mu\ge2\), since \(\mu_{\mathrm{child}}\ge1\)). Secondary rank: unconstrained. So the pair \((\deg,\mu)\) falls lexicographically whether or not the degree is preserved. `(MASS)` is asserted for nonterminal children only; a child to which no further transition applies emits its factor by clause 2 and needs no rank comparison.
> 5. **Product-\(1\) linear recentering.** Degree: EQUAL. The recentering "keeps … the same root block" (S1.8), so \(F\) is unchanged, and \(\Phi_{\mathrm{new}}=\Phi-L_k(s)\) is monic of the same degree \(D\) because \(\deg L_k(s)<D\) by S1.4. Mass: EQUAL, \(\mu_{\mathrm{new}}=\deg F/D=\mu\). Secondary rank: strictly down, by `(SEC-RANK)`. This is the only transition whose strict decrease sits in the third component, and it is exactly the transition at which `(SEC-RANK)` is asserted.
> 6. **Key-boundary decomposition of S1.9**, entered from `(MID-PEEL)`'s proper-nontrivial-gcd branch. Degree: strictly down on every residual block, since "every nonterminal \(B_j\) has strictly smaller degree than \(F\)" (S1.9). Mass and secondary rank: unconstrained.
>
> Every permitted nonterminal transition therefore strictly decreases `(RANK)`, and no transition increases a component earlier than the one it decreases. Every transition also preserves the represented roots or partitions them into explicitly disjoint exhaustive child root sets, and transports the corresponding polynomial product. Consequently there is no infinite branch, and the terminal factors exhaust the parent.

**Honest status of the three components.** Components one and two are derived above from the effective text; the four supporting facts the note previously lacked — the split's strict decrease, the peel's degree drop, the child jump's degree non-increase via `(TEST)` composed with `(MASS)`, and the recentering's degree/mass preservation via \(\deg L_k(s)<D\) — are now displayed with their sources. Component three is **not** derived: `(SEC-RANK)` is a named carrier hypothesis. Its instance status:

- **Level one** (S3.1/S3.2): supplied inside the existing pin `HE3-A-PROOF`, whose §S6.3 stage-α passage reads "Termination: each refine strictly increases the floor λ and dv-heights are bounded by the leaf's window (GENHN-3(a)), so the chain is finite" — an \(\mathbf N\)-valued instance of `(SEC-RANK)` (window bound minus current floor). Verification remark: `grep -cFx 'Termination: each refine strictly increases the floor λ and dv-heights' HE3_PROOF_2026-08-08.md` → **1**, and that line lies strictly inside the `HE3-A-PROOF` span, whose delimiters `grep -cFx '### S6.3 PROOF OF THEOREM HE3.A' HE3_PROOF_2026-08-08.md` → **1** and `grep -cFx "leaf's history, so THEOREM HE3.A is proved. ∎" HE3_PROOF_2026-08-08.md` → **1** both resolve uniquely.
- **Level two and deeper** (S3.3, and S3.4/S3.5 which read at the composed key with the same refinement package): supplied by **LEMMA HE7-8 ((REF-TERM))**, which was cited by r3 repair 5 but pinned by nothing. It is pinned here as a new existing-text span `HE7-REF-TERM` (repair 13). HE7-8 discharges `(SEC-RANK)` in its well-foundedness form rather than by an \(\mathbf N\)-valued rank: it refutes infinite α-refine chains directly, and its `[r3]` clause handles peels interleaving a chain. Accordingly `(SEC-RANK)` is stated above with \(W_{\mathcal C}\) merely well-founded, not \(\mathbf N\); an instance may discharge it either way.

No instance is claimed to discharge `(SEC-RANK)` by an argument this master reproduces.

---

## r4 repair 4 — D-1 (GAP): the level-one `(MID-PEEL)` suite — original-key branch supplied from a new pin, recentered-key branch fenced as `(MP1)`

r3 repair 4's `(MID-PEEL)` input suite names a level-two discharge (LEMMA HE6R1-3) and nothing at level one, although clause 5 fires at every level and repair 2 above has just widened its trigger. The corpus supports a **split**, not a single verdict, and this repair records the split rather than manufacturing a uniform discharge.

**(a) Item 1 is not an obligation.** Key-freeness of \(G'\) is proved in-master from separability of \(G\); the two-line derivation is inserted by repair 2. Item 1 is struck from the list of certified supplier inputs and restated as a master lemma. Replace, in r3 repair 4's suite, the item

> 1. key-freeness: \(\gcd_{K_0[x]}(G',\widetilde\Phi)=1\);

by

> 1. key-freeness: \(\gcd_{K_0[x]}(G',\widetilde\Phi)=1\) — **not** a supplier obligation; it is proved above from separability of \(G\) and holds at a reducible key;

**(b) Original level-one key: supplied, and pinned.** When the dividing key is the *original* level-one key \(\Phi'\), items 2–5 are discharged by HE6's standing peel convention, which asserts irreducibility of the peeled factor, its known σ-block, and the applicability of every statement of HE6 to the quotient. That convention was consumed by no existing pin, so it is added as a pin (repair 13). Append to r3 repair 4's suite:

> At level one the discharge splits by which key divides. If the dividing key is the **original** key \(\Phi'\), the suite is discharged by `HE6-PEEL-CONVENTION`: "if A₀ = 0 then Φ′ | f, and disc f ≠ 0 forces f = Φ′·f̃ with Φ′ ∤ f̃; the peeled factor Φ′ is irreducible of degree D′ and contributes the KNOWN σ-block (e₁, f₁), while f̃ is again monic with all roots (T1)/(T2) points, disc f̃ ≠ 0 and μ̃ = μ − 1, so every statement below is applied to f̃." The final clause supplies items 2–4 (all roots of the quotient remain (T1)/(T2) points, so the HE6 window, development, accounting and test package applies to it verbatim) and the middle clause supplies item 5 (irreducibility, simplicity, and the local invariants \((e_1,f_1)\)). If the dividing key is the level-one **child** key \(\Psi_{\lambda,r'}\), the state is a level-two state and the discharge is LEMMA HE6R1-3, as above.

**(c) Recentered level-one key: fenced.** The remaining case has no general carrier in the corpus. HE3 does record it — "each of the three sides. CASE A₀′ = 0: then Φ″ | f exactly (disc f ≠ 0 gives Φ″ ∤ f/Φ″), the top class contains Φ″'s D′ roots, and the development of g := f/Φ″ at Φ″ is P(F″) shifted left by one abscissa" — but that passage sits inside HE3's bracketed `[r1-N1]` three-consecutive-slope supplement, is not a general lemma, is not inside any pin, and supplies **no** orbit/\((e,f)\) decomposition for \(\Phi''\)'s \(D'\) roots, which is item 5. A recentered \(\Phi''=\Phi'-L_k(s)\) is asserted irreducible nowhere, and this master forbids assuming it ("the monic key itself is not declared irreducible merely because it is a key"). Insert into S1.8's "Mid-chain boundary produced by recentering", immediately after the `(MID-PEEL)` input suite paragraph installed by r3 repair 4 and amended by (a) and (b) above:

> ### S1.8A Named level-one mid-chain peel obligation
>
> Let a level-one state have as current key a **recentered** key \(\Phi''=\Phi'-L_k(s)\) dividing its represented block. Items 2–5 of the `(MID-PEEL)` input suite are not supplied for that state by any level-one pin. Denote the missing assertion by
>
> \[
> \boxed{\operatorname{MP}_1(\mathrm{HE3{+}HE6}).}
> \tag{MP1}
> \]
>
> It is the assertion that, at every level-one state whose current key is a recentered key dividing its represented block, the quotient \(G'\) satisfies `(WINDOW)`, carries its own full development with `(ACCOUNT)` and the S1.7 test assertions together with the occupied-height, lift, frame, origin and residual-degree data, and that the peeled recentered key admits a certified orbit/\((e,f)\) decomposition — items 2, 3, 4 and 5 of the suite.
>
> None of `HE3-A-STMT`, `HE3-A-PROOF`, `HE3-DEF1`, `HE3-HE3-1L`, `HE3-HE3-6`, `HE3-R8-2`–`HE3-R8-5`, `HE6-FAMILY`, `HE6-PROOF`, `HE6-SLOT-SEAM`, or `HE6-PEEL-CONVENTION` is claimed to prove `(MP1)`. `HE6-PEEL-CONVENTION` discharges the suite for the ORIGINAL key \(\Phi'\) only, and its argument runs on irreducibility of \(\Phi'\), which a recentered key does not inherit. `HE6R1-3` discharges the suite at level two, where the dividing key is \(\Psi\) and irreducibility is a conclusion of the lemma, not a hypothesis of the master; it is not used to prove `(MP1)` retroactively at level one.
>
> The stratum is machine-real, not hypothetical: HE3's battery legs P2-N1 and the PE2 `FR-D` runs both exercise the CASE A₀′ = 0 branch at a recentered level-one key. What is missing is a general lemma, not a witness.
>
> Consequently a level-one state that triggers clause 5 at a recentered key is conditional on the separately supplied obligation `(MP1)`, exactly as a level-one state that triggers clause 4 is conditional on `(LB1)`.

**Append to the S3.1 and S3.2 "Level-one fence"** (as installed by r2 repair 4 and rewritten by r3 repair 6):

> This record likewise does not discharge `(MP1)`. Therefore no level-one state whose recentered key divides its represented block is advertised as an unconditional instance of clause 5. Such a state may enter only after `(MP1)` has been supplied as an additional named instance obligation. The original-key peel is not fenced: it is discharged by `HE6-PEEL-CONVENTION`.

**Add to S5:**

> 17. Level-one clause-5 reads at a **recentered** key remain conditional on the named obligation `(MP1)`. The original-key level-one peel is discharged by `HE6-PEEL-CONVENTION`; the level-two peel by `HE6R1-3`.

**Add to S4.2's exclusion list**, immediately before its final item "acceptance before two clean hostile passes":

> - an unconditional level-one mid-chain peel at a recentered key;

**Amend the S4.1 sentence** installed by r2 repair 8, replacing "subject to the explicitly named level-one obligation `(LB1)`" by "subject to the explicitly named level-one obligations `(LB1)` and `(MP1)`".

---

## r4 repair 5 — A-1 (minor in the verdict, GAP in §A.3 of the report): `HE3-DEF1` re-derived so that the coherent-\(R_\lambda\) construction is inside the span

The r2 row reads "DEFINITION 1", whose plain reading is the blockquote alone. That blockquote names \(R_\lambda\) without displaying a construction. The master consumes the construction and its type-invariance in three places: S1.5's "After removal of any raw-origin factor, its COHERENT normalized residual polynomial satisfies `(RES-FACT)`"; S1.6's `(FRAME)`; and S1.6's "Frame changes preserve factor degrees, multiplicities, separability, and transported root classes." The last is the geometric-system theorem of HE3's `[r2]` CONSTRUCTION PIN, which is a separate bolded unit immediately following DEFINITION 1 and outside the blockquote. The note never adjudicated the boundary; it is adjudicated here in favour of the span that carries the consumed mathematics.

Replace the r2 `(PINS)` row

> `&\texttt{HE3-DEF1}&\text{DEFINITION 1}\\`

by

> `&\texttt{HE3-DEF1}&\text{DEFINITION 1 together with its attached [r2] CONSTRUCTION PIN}\\`

with delimiters:

- first: `> **DEFINITION 1 (the stage resolvent and its label set).**`
- last: `not see it.]**`

This is a two-unit contiguous span, declared in the same form as `HE7-COCYCLE-2P-THROUGH-R1D` (r3 repair 1(b)): the pin is the run of consecutive complete units from the first delimiter to the last, and both endpoint units are complete. The source's own HEAD calls the pair "PINNED at DEFINITION 1 [r2] with the coboundary Remark", so the two-unit reading is the source's.

**Verification remark.** In `lean/notes/openmath/HE3_PROOF_2026-08-08.md`, on 2026-08-13:
`grep -cFx '> **DEFINITION 1 (the stage resolvent and its label set).**' HE3_PROOF_2026-08-08.md` → **1**;
`grep -cFx 'not see it.]**' HE3_PROOF_2026-08-08.md` → **1**;
first precedes last, and the span contains DEFINITION 1 in full, the coherent display \(R_\lambda(Z):=\sum_k\operatorname{res}(A_{j_0+\ell k}(\theta)n(u)(\theta)^k/n(\kappa_0)(\theta))Z^k\), the geometric-system type-invariance theorem this master's S1.6 consumes, and the exclusion of the naive per-slot read. It ends immediately before the next sibling unit, DEFINITION 2.

*(The report classifies this finding GAP in §A.3 and minor in its verdict. It is repaired here at GAP strength — a byte-exact adjudicated delimiter pair — so the discrepancy is moot.)*

---

## r4 repair 6 — A-2 (minor): the four R8 rows named by their actual source designation

`grep -ic redline HE3_PROOF_2026-08-08.md` → **0**: the word never occurs in the source, and the source writes `R8-2`…`R8-5` with a hyphen, not `R8.2`…`R8.5`. Replace the four r2 `(PINS)` rows "the complete R8.\(N\) redline unit" (\(N=2,3,4,5\)) by

> `&\texttt{HE3-R8-}N&\text{the complete dated-correction unit }\texttt{\#\#\# Dated correction (2026-08-12, post-R8) — R8-}N\\`

each with first delimiter the byte-exact heading line and last delimiter fixed by S0.2's boundary rule (the unit ends immediately before the next `###` unit of equal rank), except `HE3-R8-5`, whose successor is not a `###` heading and whose last delimiter is quoted:

- `HE3-R8-2` first: `### Dated correction (2026-08-12, post-R8) — R8-2: the unramified branch is repaired by split-component summation`
- `HE3-R8-3` first: `### Dated correction (2026-08-12, post-R8) — R8-3: the D′ = 1 case is direct`
- `HE3-R8-4` first: `### Dated correction (2026-08-12, post-R8) — R8-4: piecewise definition of ramified label classes`
- `HE3-R8-5` first: `### Dated correction (2026-08-12, post-R8) — R8-5: HE3-0 provenance correction`
- `HE3-R8-5` last: `been updated to cite it.`

**Verification remark.** In `lean/notes/openmath/HE3_PROOF_2026-08-08.md`, on 2026-08-13, `grep -cFx` returned **1** for each of the five lines above; each `R8-N` heading precedes the next, and `R8-1` (which this master does not consume) is a distinct heading, so no row is ambiguous. Extend S0.2's unit-type list, already carrying "named statement display, or dated record", to make "dated correction" an explicit synonym of "dated record".

---

## r4 repair 7 — A-4 (minor): r3 repair 1's delimiter claim scoped to the pins it re-derived

As written, "Both delimiter lines of **every** pin are quoted byte-exactly from the accepted source and were verified by exact-full-line search on 2026-08-12" is false for 22 of the then-27 pins and would let a reader believe the S7 pin gate is already discharged. Replace that sentence by:

> Both delimiter lines of every pin **re-derived in this repair** are quoted byte-exactly from the accepted source and were verified by exact-full-line search on 2026-08-12: each occurs exactly once in its file, and each begin precedes its end. The remaining pins of `(PINS)` are description-only: their first and last delimiter lines are not quoted in this note, and the S7 pin gate must re-derive them from the description before checking conditions 1–4. Quoting a delimiter pair discharges conditions 2 and 3 in advance; it does not discharge conditions 1 and 4, which remain the gate's work.

After r4, the pins carrying quoted delimiter pairs are `HE7-SLOT-TRANSFER`, `HE7-COCYCLE-2P-THROUGH-R1D`, `HETOW-LABELS`, `HETOW-LABELS-1`, `GENTOW-ACCEPTANCE-FOLD` (r3 repair 1) and `HE6-SLOT-SEAM`, `HE3-DEF1`, `HE3-R8-2`–`HE3-R8-5`, `HE6-PEEL-CONVENTION`, `HE7-REF-TERM` (r4) — 13 of 29. The other 16 remain description-only.

---

## r4 repair 8 — A-5 (minor): the no-unpinned-material clause restored to S0.2

Base S0.2 closed with "No unpinned source material is used to manufacture a theorem hypothesis." r2 repair 1 deleted S0.2 wholesale and its replacement carries no such clause; r3 repair 9 diagnosed the same deletion but restored only the six file paths. The clause is what makes the pin apparatus load-bearing at all. Append to S0.2, immediately after the file list restored by r3 repair 9:

> No unpinned source material is used to manufacture a theorem hypothesis, to discharge a named obligation, or to certify an instance substitution. A source display that this master consumes but no pin covers is a defect of the pin table, to be cured by adding a pin or by fencing the consumption as a named obligation — never by citing the display anyway. Two consumptions were cured this way at r4: HE6's standing peel convention became `HE6-PEEL-CONVENTION`, and LEMMA HE7-8 became `HE7-REF-TERM`.

---

## r4 repair 9 — A-6 (minor): `(GAMMA)`'s coefficient normalizers disclosed, and reconciled from inside a pinned span

The master's `(GAMMA)` writes the coefficient normalizer \(\pi^{-(k-(i+e_1t)h)/e_1}\) explicitly and then warns that "The coefficient normalizers inside \(\gamma_k(A)\) and the negative sign on \(q(k)\) are mandatory" and that "The bare sum of coefficient residues is not an admissible substitute" — while the pinned displays write the bare sum \(\gamma=\sum_t\operatorname{res}(a_{i_0+e_1t})\eta_\theta^{t}\) (LEMMA HE6-0″, inside `HE6-SLOT-SEAM`; likewise HE7-L1's proof). Read literally at a slot with \(v(a)>0\) the bare residue is \(0\), so the master's warning reads as an unattributed correction of its own suppliers. It is not one, and the reconciliation is available inside an existing pin. Insert after the sentence "The coefficient normalizers inside \(\gamma_k(A)\) and the negative sign on \(q(k)\) are mandatory":

> **Normalization disclosure.** The pinned displays state this residue in abbreviated form, as the bare sum \(\sum_t\operatorname{res}(a_{i_0+e_1t})\eta_\theta^{t}\). The two agree, and the agreement is the sources' own monomial arithmetic rather than a master-side amendment. Inside the pin `HE3-HE3-1L`, LEMMA HE3-1L's proof fixes the valuation of an attaining slot — "with v(c_i) = (κ − (i₀+e₁t)h)/e₁ — a nonnegative integer exactly when t ∈ T(κ)" — and then performs the division — "c_i θ^{i₀+e₁t} / n(κ)(θ) = c_i·(θ^{e₁}π^{−h})^{t}·(unit-free exact monomial arithmetic: the π-exponents cancel to −th), whose residue is res(c_i)·η_θ^{t}" — so the quantity whose residue is taken is \(c_i\pi^{-(\kappa-(i_0+e_1t)h)/e_1}\), the height-normalized coefficient, which is exactly `(GAMMA)`'s summand. The abbreviation "\(\operatorname{res}(c_i)\)" in the sources' summary lines therefore denotes the residue of the height-normalized coefficient; the sources' own clause that these residues "rang[e] freely over F_Q" for the attainable slots forces that reading, since a literal bare residue would be \(0\) at every slot with \(v(c_i)>0\). This master writes the normalizer out because at \(e_1\ge2\) and \(k>(i_0+e_1t)h\) the two readings visibly differ, and because the `(FRAME)` discipline requires every read to name its normalizer. No pinned display is asserted to be wrong; one abbreviation is expanded.

**Verification remark.** In `lean/notes/openmath/HE3_PROOF_2026-08-08.md`, on 2026-08-13, `grep -cFx` returned **1** for each of the three quoted source lines
`> invertible mod e₁), with v(c_i) = (κ − (i₀+e₁t)h)/e₁ — a nonnegative`,
`> c_i θ^{i₀+e₁t} / n(κ)(θ) = c_i·(θ^{e₁}π^{−h})^{t}·(unit-free exact`,
`> monomial arithmetic: the π-exponents cancel to −th), whose residue is`,
and all three lie strictly inside the `HE3-HE3-1L` span.

---

## r4 repair 10 — D-2 (minor): S1.7B's conditionality sentence scoped to clause 4

r3 repair 6's sentence declares every multi-side level-one state `(LB1)`-conditional, while r3 repair 7, installed three repairs later, states that clauses 1 and 2 "run on \(F\) itself … with no appeal to `(SIDE-PROD)`". A multi-side level-one state all of whose side residuals are separable is decided outright by clauses 1–2 and consumes nothing from `(LB1)`. The S3.1/S3.2 appends already scope to clause 4; S1.7B, the definitional home, does not, and is the sentence a reader will quote. Replace S1.7B's

> Consequently the HE3.A and HE6 instance records are unconditional only for single-side level-one states whose residual is separable or already pure repeated. Every level-one state requiring a side split or a label split — multi-side states included — is conditional on the separately supplied obligation `(LB1)`.

by

> Consequently a level-one state is `(LB1)`-conditional exactly when its processing actually constructs a block: when clause 4 emits side blocks or label blocks. Every level-one state requiring a side split or a label split — multi-side states included — is `(LB1)`-conditional in that sense. Clauses 1 and 2 are not: their proofs run on the unsplit hull of \(F\) itself, so the HE3.A and HE6 instance records' clause-1 and clause-2 conclusions are unconditional at every level-one state, multi-side states included. What is conditional is the clause-4 route, and only where it is taken.

---

## r4 repair 11 — E-1 (minor): the pointwise-label claim re-cited to S1.7 clause 2

r3 repair 7 justifies "the label classes read on the block \(F_\lambda\) are the same root sets as the classes read directly at side \(\lambda\) of \(F\)" by "labels attach to roots pointwise (S1.7, clause 1)". S1.7 clause 1 is about the roots of the test polynomial \(\Psi_{\lambda,r'}\), not about the roots of \(F\). The claim is true; the citation is not the one that supports it. Replace, in r3 repair 7's inserted paragraph, the phrase

> and labels attach to roots pointwise (S1.7, clause 1)

by

> and labels attach to roots of \(F\) pointwise (S1.7, clause 2): the \(r'\)-class is \(\{\rho:\ d(\Psi_{\lambda,r'}(\rho))\text{ exceeds the generic value}\}\), a condition on \(\rho\) and \((\lambda,r')\) alone, since the carrier supplies \(\Psi_{\lambda,r'}\) from \((\lambda,r')\) and not from the state polynomial

with the rest of the sentence unchanged. The direct partition and the block partition are then restrictions of one pointwise partition to the same root set, and each being exhaustive their index sets coincide.

---

## r4 repair 12 — F-1 (minor): the superseded 4.A(ii) parenthetical noted at pin `GENTOW-4-A`

r3 repair 3 established the practice of noting a competing or superseded display at the pin, and applied it at `HE6R1-1` and `HETOW-LABELS`. The same configuration exists at `GENTOW-4-A` and was left unnoted. Add at pin `GENTOW-4-A`:

> The span is THEOREM GENTOW-4.A in GENTOW4 §S3. Its clause (ii) carries the parenthetical "top coefficient NOT monic — the partial-side signature", which a later dated correction outside this span declares superseded: `### [TOWERRAT2-C annex, 2026-08-10] Dated correction: the 4.A(ii)` / `### "top coefficient NOT monic" parenthetical SUPERSEDED`. **The 2026-08-10 TOWERRAT2-C correction governs.** This master consumes from clause (ii) only \(\mu_2^*=\sum_{\lambda_2>T_2}L_{\lambda_2}\) and \(\deg f_S=D_2\mu_2^*\), never the top-coefficient parenthetical; S3.5 states the complementary restraint, "No whole-polynomial monicity or length hypothesis is transferred to \(f_S\) without proof". The pin is unchanged; the note is a reading directive.

**Verification remark.** In `lean/notes/openmath/GENTOW4_PROOF_2026-08-09.md`, on 2026-08-13, `grep -cFx` returned **1** for each of the two annex heading lines quoted above.

---

## r4 repair 13 — pin inventory 27 → 29: the two consumptions cured by pinning

Two source units this master consumes were covered by no pin. Both are added as existing-text spans; neither requires a source edit.

**(a) `HE6-PEEL-CONVENTION`** — consumed by repair 4(b) as the level-one original-key discharge of the `(MID-PEEL)` input suite, and by S1.5's key-freeness discipline at the HE3+HE6 instance. New `(PINS)` row, in the HE6 block:

> `&\texttt{HE6-PEEL-CONVENTION}&\text{the HE6 §S1 CONVENTION [r1] on }f\text{ (separability, }\Phi'\nmid f\text{, and the original-key peel)}\\`

- first: `> **CONVENTION [r1] (the two standing hypotheses on f — R2/F2 and R6/F7).**`
- last: `> the peel is cleaner and is what is adopted.)`

Verification remark: in `lean/notes/openmath/HE6_PROOF_2026-08-08.md`, on 2026-08-13, `grep -cFx` returned **1** for each of the two delimiter lines; first precedes last; the span contains the complete convention — the two standing hypotheses, the peel clause with \(\Phi'\) irreducible and its σ-block \((e_1,f_1)\), the PE1-finding-2 counterexample \(f=\Phi'(\Phi'+\pi^2)\) motivating it, and the declined ∞-label alternative — ending immediately before the next unit.

**(b) `HE7-REF-TERM`** — consumed by repair 3 as the level-two-and-deeper discharge of `(SEC-RANK)`, by r3 repair 5's degenerate guard (which cites HE7-8's `[r3]` clause), and by r2 repair 4's S3.3 replacement ("HE6R1-3 together with HE7-8 `[r3]`"). New `(PINS)` row, in the HE7 block:

> `&\texttt{HE7-REF-TERM}&\text{LEMMA HE7-8 ((REF-TERM)), statement and proof}\\`

- first: `> **LEMMA HE7-8 ((REF-TERM) — α-refine chains are FINITE, characteristic-free).**`
- last: `μ₂ ≥ 2 this makes disc f_S = 0. ∎`

Verification remark: in `lean/notes/openmath/HE7_PROOF_2026-08-08.md`, on 2026-08-13, `grep -cFx` returned **1** for each of the two delimiter lines; first precedes last; the span contains the lemma statement, the `[r2]` hypothesis-set box, the `[r3]` peel-interleaving box (the clause r3 repair 5 quotes), and the complete proof.

**Bookkeeping.** In the effective S0.2 (r2 repair 1 as amended by r3 repair 1) replace "The 27 pins are the following existing-text pairs" by "The 29 pins are the following existing-text pairs". In the effective S7 pin gate (r2 repair 1 as amended by r3 repair 1) replace "The expected pin count is 27" by "The expected pin count is 29"; the expected synthetic-marker count stays zero. Amend three source-pin lines:

- S3.1 (the r1 repair 2 replacement paragraph): after "`HE6-FAMILY`, `HE6-PROOF`, and `HE6-SLOT-SEAM`" read "`HE6-FAMILY`, `HE6-PROOF`, `HE6-SLOT-SEAM`, and `HE6-PEEL-CONVENTION`".
- S3.2: **Source pins:** `HE6-FAMILY`, `HE6-PROOF`, `HE6-SLOT-SEAM`, and `HE6-PEEL-CONVENTION`.
- S3.3: **Source pins:** `HE7-A-STMT`, `HE7-SLOT-TRANSFER`, `HE7-MIXED-13P`, `HE7-COCYCLE-2P-THROUGH-R1D`, `HE7-REF-TERM`, `HE6R1-1`, `HE6R1-2`, and `HE6R1-3`.

Add to the S7 pin gate, as a standing check that would have caught both omissions:

> Also enumerate every source display the master text quotes, names, or leans on for a hypothesis or an obligation discharge, and confirm each lies inside some span of `(PINS)`. A consumption outside every span fails the gate.

---

## r4 counter

r4 folds repairs for all four GAPs (A-3, B-1, B-2, D-1) and all eight minors (A-1, A-2, A-4, A-5, A-6, D-2, E-1, F-1) of the r3 hostile pass of record, plus the pin-inventory consequences. Two of these are theorem-statement changes: clause 5's trigger is widened to the case its own cited discharge is about (repair 2), and the rank paragraph now displays the tuple it previously only named (repair 3). Neither adds a conclusion; both add a hypothesis or a case whose mechanism the body already proves, and repair 3 makes an implicit carrier assumption explicit as `(SEC-RANK)`. Two named obligations are now open at level one: `(LB1)` for clause-4 block construction and `(MP1)` for the clause-5 peel at a recentered key.

Gap-or-worse repairs reset the clean count (S7: "A gap-or-worse repair resets the clean count"). **The clean-pass counter is RESET to 0 of 2.** The acceptance gate still owes **TWO consecutive clean hostile passes** over the r4 effective text before this note may leave attempt grade \(0/2\); the status line therefore stays "mathematical composition draft, attempt grade \(0/2\)", and by `(GRADE)` every composed instance stays \(0/2\) regardless of supplier grade.

---

## r5 (2026-08-13): the perturbation transport pinned — `(SEC-RANK)` re-routed at the composed key, the level-two recentered peel derived, the consumption sweep closed

*(Opus/Claude repair arm, against the r4 hostile pass of record `runs/comp13/T2P4_output.log` — 0 CRITICAL + 2 GAP + 5 minor; counter resets.)*

**Verification protocol for this round.** Every source delimiter line quoted below was checked on 2026-08-13 by exact-full-line search (`grep -cFx`) in the named accepted source file, and both the command and its count are recorded at the pin. No source file is edited by this round; the expected source edit count remains zero. Landmarks internal to this master are quoted from the **r4 effective text**, and their uniqueness is recorded in the form `sed -n '1,2608p' T2_SIGMA_LADDER_MASTER_2026-08-12.md | grep -cF '<string>'` → **1**; the line bound 2608 is the last line of the r4 round and excludes this round's own re-quotations, which would otherwise inflate every count.

**The root cause both GAPs share.** Both r4 theorem-statement changes — the widened clause-5 trigger (r4 repair 2) and the carrier hypothesis `(SEC-RANK)` (r4 repair 3) — are consumed at keys that are not literally DEFINITION HE6-1 test polynomials: at the composed key \(\Phi_2\) (S3.4/S3.5), and at a **recentered** level-two key \(\Psi-W\) (every level-two α-refine, at every level-two record). The corpus object that carries the level-two package across such a key is **LEMMA HE7-12 (SLOT-DOMINATION)**, asserted at the composed key by **LEMMA HETOW-2** and at the partial-tower key by **LEMMA GENTOW-4.1(c)**. r4 named none of the first two and pinned only the third. This round pins the transport, re-routes `(SEC-RANK)` to clauses stated at the composed key, derives the level-two recentered peel from the transport, and fences the one configuration the transport does not reach.

---

## r5 repair 1 — G-1 (GAP): `(SEC-RANK)` for S3.4/S3.5 re-routed to the clauses stated AT the composed key, and the transport pinned

**The finding repaired.**

> `(SEC-RANK)`'s discharge for the HETOW and GENTOW4 records is routed through a lemma stated at a DIFFERENT key, by a transfer that no pin covers and the note never names; and the pin it does name is in neither record's pin line.

with the diagnosis that HE7-8's hypothesis reads "Let 𝔇 be a level datum with key Ψ", that "S3.4/S3.5 read at the composed key Phi_2", that "LEMMA HETOW-2 is therefore inside NO span of `(PINS)`; LEMMA HE7-12 is likewise inside no span", and with the observation that the FACT "is available at pins that ARE listed — HETOW-A(ii) … and GENTOW-4-A(iii) … The conclusion survives; the stated route does not."

**The diagnosis is accepted in full, and the route is replaced rather than patched.** The chosen mechanism is (ii) — re-routing to the already-pinned clauses — because those clauses state the needed conclusion **at \(\Phi_2\) itself**, so the master performs no transport at all; the transport is internal to the pinned theorems' own proofs. The transport lemma is *additionally* pinned (below), because S3.4's own text names LEMMA HETOW-2 and because repair 2 consumes LEMMA HE7-12 at the master level.

**Why the re-route type-checks at the key the records read.** `(SEC-RANK)` asks, of a state, for a well-founded \(W_{\mathcal C}\) and a \(\sigma_{\mathcal C}\) strictly decreasing at every **product-\(1\) linear recentering**. By S1.8 that transition is the branch \(e'\deg r'=1\), i.e. "\(e'=1\) and \(r'=Y-s\) for some \(s\in K\)" — integer slope, linear residual factor. At a level-two state of S3.4/S3.5 that is exactly the configuration the two pinned clauses quantify over, "a repeated K₂-rational linear factor at integer λ₂", and each asserts of it, **at the composed key**, that the α-refine chain it generates is FINITE:

- `HETOW-A` clause (ii), `HETOW_RECON_2026-08-09.md`:307–309 —
  > `> linear factor at integer λ₂ is a finite α-refine chain (LEMMA`
  THEOREM HETOW.A's own preamble binds every clause to the composed key: `> η ≠ 1 wrap frames; every clause below reads at the corrected key):`.
- `GENTOW-4-A` clause (iii), `GENTOW4_PROOF_2026-08-09.md`:289–292 —
  > `> finite alpha-refine chain (HE7-12/13, HE7-8; the chain re-reads`
  under the same clause's own key declaration `> f_S at the datum (kappa2, rtilde) with key Phi2: every side of`.

Finiteness of every chain of the recentering relation **is** well-foundedness of that relation, and a well-founded relation carries an ordinal rank function; that rank is a legitimate \(\sigma_{\mathcal C}\) into a well-founded \(W_{\mathcal C}\), which is precisely the latitude r4 repair 3 wrote into `(SEC-RANK)` ("\(W_{\mathcal C}\) merely well-founded, not \(\mathbf N\)"). No step of this reads HE7-8 at a key other than the one its host theorem declares.

**Verification remark.** On 2026-08-13, `grep -cFx` returned **1** for each of the four quoted source lines above, in `lean/notes/openmath/HETOW_RECON_2026-08-09.md` (lines 1 and 2) and `lean/notes/openmath/GENTOW4_PROOF_2026-08-09.md` (lines 3 and 4). All four lie strictly inside the existing spans `HETOW-A` and `GENTOW-4-A` respectively.

**The transport, pinned. (a) New pin `HETOW-KEY-BRIDGE`** — LEMMA HETOW-2, statement and proof; the unit S3.4's text names ("HETOW-2 identifies it with a genuine HE6-family key in the legal lifted form, or with an allowed above-line perturbation") and the unit that licenses HE6R1-3's peel at \(\Phi_2\). Delimiters:

- first: `> **LEMMA HETOW-2 (the composed key is a key-family member up to an`
- last: `covers w = 0). ∎`

Verification remark: in `lean/notes/openmath/HETOW_RECON_2026-08-09.md`, on 2026-08-13, `grep -cFx` returned **1** for each of the two lines; the first (line 198) precedes the last (line 262); the span contains the complete lemma — the \(\Psi\)-membership statement, the conclusion `> and **either w = 0 (in particular under the (LIFT)-slot coefficient` … `dv₂(w) > T₂`, and the complete `[F-4]`/`[F-2]` proof with its carry accounting — ending immediately before the next sibling unit, LEMMA HETOW-3. Conditions 1–4 of S0.2 hold.

**(b) New pin `HE7-PERT-TRANSPORT`** — LEMMA HE7-12 together with LEMMA HE7-13, statements and proofs: a two-unit contiguous span, declared in the same form as `HE3-DEF1` (r4 repair 5) and `HE7-COCYCLE-2P-THROUGH-R1D` (r3 repair 1(b)). Delimiters:

- first: `> **LEMMA HE7-12 [r2] (SLOT-DOMINATION — the §S5 package survives every`
- last: `by one block (§S5.5), leaving the same conclusion for f_S′. ∎`

Verification remark: in `lean/notes/openmath/HE7_PROOF_2026-08-08.md`, on 2026-08-13, `grep -cFx` returned **1** for each of the two lines; the first (line 812) precedes the last (line 951); the span contains LEMMA HE7-12 in full — hypothesis `> degree D″. Then, **with the level-2 point set of DEFINITION HE7-1` unchanged, clauses (a)–(d) and the eleven-item audit proof — and LEMMA HE7-13 in full, ending immediately before the next unit (the `[r2]` machine-confirmation record). Both endpoint units are complete. Conditions 1–4 of S0.2 hold.

**Supersession.** Replace, in r4 repair 3's "Honest status of the three components", the entire second bullet

> - **Level two and deeper** (S3.3, and S3.4/S3.5 which read at the composed key with the same refinement package): supplied by **LEMMA HE7-8 ((REF-TERM))**, which was cited by r3 repair 5 but pinned by nothing. It is pinned here as a new existing-text span `HE7-REF-TERM` (repair 13). HE7-8 discharges `(SEC-RANK)` in its well-foundedness form rather than by an \(\mathbf N\)-valued rank: it refutes infinite α-refine chains directly, and its `[r3]` clause handles peels interleaving a chain. Accordingly `(SEC-RANK)` is stated above with \(W_{\mathcal C}\) merely well-founded, not \(\mathbf N\); an instance may discharge it either way.

by the two bullets

> - **Level two at a DEFINITION HE6-1 key** (S3.3): supplied by **LEMMA HE7-8 ((REF-TERM))**, pinned as `HE7-REF-TERM` (r4 repair 13). HE7-8 is stated at the base key \(\Psi\) of the chain and quantifies over the whole chain \(\Psi^{(0)}=\Psi\), \(\Psi^{(j+1)}=\Psi^{(j)}-w_j\), which is S3.3's actual configuration: the record's key is \(\Psi_{\lambda,r}\), a DEFINITION HE6-1 member, so the lemma applies with no transfer. It discharges `(SEC-RANK)` in its well-foundedness form rather than by an \(\mathbf N\)-valued rank: it refutes infinite α-refine chains directly. Accordingly `(SEC-RANK)` is stated above with \(W_{\mathcal C}\) merely well-founded, not \(\mathbf N\); an instance may discharge it either way.
> - **Level two at the composed key** (S3.4/S3.5): **not** supplied by instantiating HE7-8, whose hypothesis names the chain's base key and whose base key here would have to be \(\Phi_2=\Psi_{\kappa_2,\widetilde r}-w\). It is supplied instead by the clause of each record's own already-listed pin that states the conclusion at \(\Phi_2\): `HETOW-A` clause (ii), "a repeated K₂-rational linear factor at integer λ₂ is a finite α-refine chain (LEMMA HE7-12/13, HE7-8)", under THEOREM HETOW.A's preamble "every clause below reads at the corrected key"; and `GENTOW-4-A` clause (iii), "a repeated K2-rational linear factor at integer lambda2 is a finite alpha-refine chain (HE7-12/13, HE7-8; the chain re-reads f itself through (ii) at each refined key, available by LEMMA HE7-12 with W + w)", stated of "f_S at the datum (kappa2, rtilde) with key Phi2". Both clauses cite LEMMA HE7-8 and LEMMA HE7-12 by name, so `HE7-REF-TERM` and `HE7-PERT-TRANSPORT` (repair 1 of r5) are listed at both records as the named supporting units; the transfer from \(\Psi_{\kappa_2,\widetilde r}\) to \(\Phi_2\) is performed inside those theorems' proofs, by `HETOW-KEY-BRIDGE` and by `GENTOW-4-1` clause (c), and is not performed by this master.

**Verification remark (landmark).** `sed -n '1,2608p' T2_SIGMA_LADDER_MASTER_2026-08-12.md | grep -cF -- '- **Level two and deeper** (S3.3, and S3.4/S3.5 which read at the composed key'` → **1**.

The pin-line consequences of this repair are folded into repair 6 below, which sets all five Source-pin lines in final form.

---

## r5 repair 2 — G-2 (GAP): the level-two recentered-key peel DERIVED from `HE7-PERT-TRANSPORT`, and the one configuration it does not reach fenced as `(MP1′)`

**The finding repaired.**

> The recentered-key branch that r4 repair 2 newly added to clause 5 has no stated level-two discharge of the `(MID-PEEL)` input suite. The clause named as its discharge states none of items 2–5, and the lemma it routes to is stated at the unrecentered key.

with the demonstration that HE7-8's `[r3]` clause asserts only "(a) that it happens and (b) that mass drops by one — precisely the two facts the master proves IN-master", and that HE6R1-3's hypothesis is the unrecentered \(\Psi\), its proof consuming "Every root ξ of g₀ is a root of Ψ = Ψ_{λ,r}, hence a level-2 point with level-1 label (λ, r) (LEMMA HE6-1)".

**The `[r3]`-clause route is withdrawn, not defended.** Replace r4 repair 2's closing paragraph

> **Instance consequence.** The child-jump branch of the trigger is precisely LEMMA HE6R1-3's hypothesis, so r3 repair 4's cited discharge now discharges a case the theorem states. The recentering branch is discharged at level two by the `[r3]` interleaving clause of LEMMA HE7-8 (pinned by repair 3 below) and is **fenced at level one** by repair 4.

by

> **Instance consequence.** The child-jump branch of the trigger is precisely LEMMA HE6R1-3's hypothesis, so r3 repair 4's cited discharge now discharges a case the theorem states. The recentering branch is **fenced at level one** by repair 4 as `(MP1)`, and is discharged at level two by S1.8B below — by LEMMA HE7-12(c)'s transport of LEMMA HE6R1-3 to the recentered key, **not** by the `[r3]` interleaving clause of LEMMA HE7-8, which asserts only that a mid-chain peel occurs and drops \(\mu_2\) by one and supplies no item of the input suite. That clause keeps exactly the role r3 repair 5 gave it: the \(\nu=1\) degenerate guard and the pigeonhole bounding how many peels may interleave one chain.

**Verification remark (landmark).** `sed -n '1,2608p' … | grep -cF -- '**Instance consequence.** The child-jump branch of the trigger is precisely'` → **1**.

**The derivation.** Insert into S1.8's "Mid-chain boundary produced by recentering", immediately after the final paragraph of S1.8A (installed by r4 repair 4(c)), "Consequently a level-one state that triggers clause 5 at a recentered key is conditional on the separately supplied obligation `(MP1)`, exactly as a level-one state that triggers clause 4 is conditional on `(LB1)`.":

> ### S1.8B The level-two mid-chain peel at a recentered key, derived
>
> Let a level-two state have as current key a recentered key \(\Psi^{(j)}=\Psi-W\) dividing its represented block, \(\Psi=\Psi_{\lambda,r}\) being the DEFINITION HE6-1 key at which the α-refine chain began. Items 2–5 of the `(MID-PEEL)` input suite are supplied for that state, and the derivation has two steps, each read at the key the state actually carries.
>
> **Step 1 — the recentered key is an above-the-line perturbation, by the master's own data.** Each refine increment is \(L_{k}(s)\) at the exact height \(k=\lambda_2\) of the side being refined (S1.8's recentering, `(OCC)` supplying the legal lift at that height), and every side slope of a state satisfies \(\lambda_2>T\) by clause 1 of HE7.A. At a level-two state \(T=T_2\), so each increment \(w\) has \(\deg w<D''\) and \(dv_2(w)=\lambda_2>T_2\) — literally the hypothesis of **LEMMA HE7-12** ("level-2 slot value ν := dv₂(w) … > T₂"), and along a chain **LEMMA HE7-12(d)** folds \(W=w_1+\dots+w_j\) into ONE application ("so every iterate Ψ − W of a refine chain is covered by ONE instance of (a)–(c)"). The source states the same height independently, inside the same pin: `> (it exists: λ₂ > T₂ satisfies (‡₂) by §S4.3) and Ψ̃^{(1)} := Ψ̃ − w.` The two legs — this master's clause 1 plus S1.8's lift height, and LEMMA HE7-13's own display — agree, so the hypothesis is not carried by a single textual reading.
>
> **Step 2 — the transport delivers HE6R1-3 verbatim at that key.** `HE7-PERT-TRANSPORT` clause (c) lists what survives: "the §S1 CONVENTION with LEMMA HE6R1-3's peel, and LEMMA HE6R1-2's read — holds VERBATIM with Ψ^{(w)} in place of Ψ (same λ, r, dv₂, n₂, K₂, T₂, ι^{(2)}; labels and residues now read on Ψ^{(w)}), by the SAME proofs". Item (11) of its proof discharges the one hypothesis of HE6R1-3 that mentions the key at all: "the peel at Ψ^{(w)}: LEMMA HE6R1-3's proof needs 'every root of the key is a level-2 point' — a root ξ of Ψ^{(w)} has dv₂(Ψ^{(w)}(ξ)) = ∞ > T₂, so ξ is a level-2 point by (b)'s disk criterion; Galois stability, integral closedness of O and disc ≠ 0 are key-free; and deg Ψ^{(w)} = D″ with e ≥ e₁ℓ, f ≥ f₁d_r forces (e, f) = (e₁ℓ, f₁d_r) by the same sandwich."
>
> Hence LEMMA HE6R1-3 holds at \(\Psi^{(j)}\) with its full conclusion, which is what r3 repair 4 already identified as the suite's level-two supplier: irreducibility of the peeled key over \(O\) of degree \(D''\), its simplicity, and \(e=e_1\ell\), \(f=f_1d_r\) — item 5; and the quotient's key-freeness with "every root still a level-2 point" and "THEOREM HE7.A applies to \(f_S'\) with \(\mu_2-1\) in place of \(\mu_2\)" — items 2, 3 and 4. The level-two recentered-key branch of clause 5 is therefore **discharged, not fenced**; the level-one branch remains fenced as `(MP1)`, because LEMMA HE7-12 is a level-TWO statement and this master asserts no level-one analogue of it.
>
> ### The one configuration the transport does not reach: `(MP1′)`
>
> Repair 4(b)'s sentence
>
> > If the dividing key is the level-one **child** key \(\Psi_{\lambda,r'}\), the state is a level-two state and the discharge is LEMMA HE6R1-3, as above.
>
> is exact when the level-one key beneath that child key is the **original** \(\Phi'\). When the level-one key beneath is itself a recentered \(\Phi''=\Phi'-L_k(s)\), the child key is a DEFINITION HE6-1 construction over a level-one frame whose key no pinned unit certifies as such a frame. LEMMA HE7-12 does not close this: its clauses (a)/(b) run on the level-2 point set **over a fixed level-1 frame** ("with the level-2 point set of DEFINITION HE7-1 unchanged (it is defined by level-1 data, not by the key)"), and its hypothesis "Let (λ, r) be a level-2 datum with key Ψ (DEFINITION HE7-1)" takes that level-one frame as given. Denote the missing assertion by
>
> \[
> \boxed{\operatorname{MP}_1'(\mathrm{HE3{+}HE6}).}
> \tag{MP1′}
> \]
>
> It is the assertion that a recentered level-one key \(\Phi''=\Phi'-L_k(s)\) carries a level-one frame in the sense S1.2–S1.7 demand — the same \((T1)/(T2)\) point set, the same \(dv\), \(\varpi\), \(K\) and \(T=D'h\), with DEFINITION HE6-1's test family constructible over it — so that a state built over \(\Phi''\) instantiates HE7.A at all, at level one or above. `(MP1′)` is a companion of `(MP1)` with the same status: named, not proved, and supplied by no pin of `(PINS)`. It is separate from `(MP1)`: `(MP1)` is about *peeling* a recentered level-one key, `(MP1′)` about *reading over* one. A state is `(MP1′)`-conditional exactly when a level-one recentering lies anywhere in its history.
>
> The two are independent of the level-two derivation above, which reads over an unrecentered level-one frame and recenters only the level-two key.

**Propagation to the sites the `(MP1)` fence touches.** Four textual amendments, each on a landmark unique in the r4 effective text (counts recorded at the end of this repair):

1. In the S3.1/S3.2 "Level-one fence" append installed by r4 repair 4, replace "This record likewise does not discharge `(MP1)`." by "This record likewise discharges neither `(MP1)` nor `(MP1′)`."
2. Replace S5 item 17, "17. Level-one clause-5 reads at a **recentered** key remain conditional on the named obligation `(MP1)`. The original-key level-one peel is discharged by `HE6-PEEL-CONVENTION`; the level-two peel by `HE6R1-3`.", by "17. Level-one clause-5 reads at a **recentered** key remain conditional on the named obligation `(MP1)`, and any read whose history contains a level-one recentering remains conditional on `(MP1′)`. The original-key level-one peel is discharged by `HE6-PEEL-CONVENTION`; the level-two peel at a DEFINITION HE6-1 key by `HE6R1-3`, and at a recentered level-two key by `HE7-PERT-TRANSPORT` clause (c) carrying `HE6R1-3` to that key (S1.8B)."
3. Add to S4.2's exclusion list, immediately after "- an unconditional level-one mid-chain peel at a recentered key;", the item "- an unconditional read at any level over a recentered level-one key;".
4. In S4.1, replace "subject to the explicitly named level-one obligations `(LB1)` and `(MP1)`" by "subject to the explicitly named level-one obligations `(LB1)`, `(MP1)` and `(MP1′)`".

The other consumers of the level-one fence identified by the r4 pass — clause 5 itself, the S1.8 induction paragraph, and `(RANK)` item 3 — consume the suite as a clause hypothesis rather than as a discharged fact, so they inherit whichever of `(MP1)`, `(MP1′)` the state carries without further amendment; that is the property r4 repair 2 installed when it made the suite "a hypothesis of this clause, not a consequence of the peel identity".

**Verification remarks.** In `lean/notes/openmath/HE7_PROOF_2026-08-08.md`, on 2026-08-13, `grep -cFx` returned **1** for each of the five quoted source lines used in Steps 1–2:

> `> degree D″. Then, **with the level-2 point set of DEFINITION HE7-1`
> `> (it exists: λ₂ > T₂ satisfies (‡₂) by §S4.3) and Ψ̃^{(1)} := Ψ̃ − w.`
> `> §S1 CONVENTION with LEMMA HE6R1-3's peel, and LEMMA HE6R1-2's read —`
> `> holds VERBATIM with Ψ^{(w)} in place of Ψ (same λ, r, dv₂, n₂, K₂, T₂,`
> `the peel at Ψ^{(w)}: LEMMA HE6R1-3's proof needs "every root of the key`

All five lie strictly inside the `HE7-PERT-TRANSPORT` span (lines 812–951). Each of the six master-internal landmarks this repair supersedes or anchors on — the S1.8A closing sentence quoted as the insertion point, the "Instance consequence" paragraph, the S3.1/S3.2 fence sentence, S5 item 17, the S4.2 exclusion item, the S4.1 obligation phrase, and repair 4(b)'s child-key sentence — is quoted byte-exactly at its amendment above and returned **1** under `sed -n '1,2608p' T2_SIGMA_LADDER_MASTER_2026-08-12.md | grep -cF -- '<the quoted string>'` on 2026-08-13.

---

## r5 repair 3 — m-1 (minor): the quoted-delimiter-pair inventory corrected in both directions

**The finding repaired.**

> r4's own inventory of quoted delimiter pairs is wrong in both directions, so its two totals are wrong. … My recount: quoted pairs = HE7-SLOT-TRANSFER, HE7-COCYCLE-2P-THROUGH-R1D, HETOW-LABELS, HETOW-LABELS-1, GENTOW-ACCEPTANCE-FOLD, HE6-SLOT-SEAM, HE3-DEF1, HE3-R8-5, HE6-PEEL-CONVENTION, HE7-REF-TERM, HE3-A-PROOF = 11 of 29; 18 remain without a quoted pair.

The recount is correct, and the two directional errors are named here so that neither recurs. **Over-count:** `HE3-R8-2`, `HE3-R8-3` and `HE3-R8-4` were listed as carrying quoted pairs, but r4 repair 6 quotes only their **first** delimiter and fixes each **last** delimiter by S0.2's boundary rule ("the unit ends immediately before the next `###` unit of equal rank"), explicitly excepting only `HE3-R8-5`. A single quoted delimiter discharges condition 2 for that line alone; it discharges neither condition 3 nor condition 2 for the unquoted endpoint. **Under-count:** `HE3-A-PROOF` was omitted although r4 repair 3's own verification remark quotes and grep-verifies both of its delimiters, `### S6.3 PROOF OF THEOREM HE3.A` and `leaf's history, so THEOREM HE3.A is proved. ∎`.

Replace r4 repair 7's sentence

> After r4, the pins carrying quoted delimiter pairs are `HE7-SLOT-TRANSFER`, `HE7-COCYCLE-2P-THROUGH-R1D`, `HETOW-LABELS`, `HETOW-LABELS-1`, `GENTOW-ACCEPTANCE-FOLD` (r3 repair 1) and `HE6-SLOT-SEAM`, `HE3-DEF1`, `HE3-R8-2`–`HE3-R8-5`, `HE6-PEEL-CONVENTION`, `HE7-REF-TERM` (r4) — 13 of 29. The other 16 remain description-only.

by

> After r5, the pins carrying quoted delimiter **pairs** are `HE7-SLOT-TRANSFER`, `HE7-COCYCLE-2P-THROUGH-R1D`, `HETOW-LABELS`, `HETOW-LABELS-1`, `GENTOW-ACCEPTANCE-FOLD` (r3 repair 1); `HE6-SLOT-SEAM`, `HE3-DEF1`, `HE3-A-PROOF`, `HE3-R8-5`, `HE6-PEEL-CONVENTION`, `HE7-REF-TERM` (r4); and `HETOW-KEY-BRIDGE`, `HE7-PERT-TRANSPORT`, `HE6-LIFT-1L` (r5) — **14 of 32**. Three further pins, `HE3-R8-2`, `HE3-R8-3` and `HE3-R8-4`, carry a quoted **first** delimiter only, their last delimiter being fixed by S0.2's boundary rule; for these, condition 2 is discharged in advance for the first delimiter alone and condition 3 remains the gate's work. The other 15 pins are description-only at both ends. Totals: 14 pairs + 3 first-only + 15 description-only = 32.

**Verification remark (landmark).** `sed -n '1,2608p' … | grep -cF -- '13 of 29. The other 16 remain description-only.'` → **1**.

---

## r5 repair 4 — m-2 (minor): the uncovered-consumption list completed — LEMMA HETOW-2 pinned, and \(q(k)\) pinned at a new `HE6-LIFT-1L`

**The finding repaired.**

> r4's claim that exactly two consumptions lay outside every pin is false; at least two more remain, one of them named in the master's own instance text. … Uncovered consumption (a): LEMMA HETOW-2 … Uncovered consumption (b): the definition of q(k). … The RIDER and the defining display "η_θ^{q(k)} := res(ϖ(θ)^k/n(k)(θ))" live at HE6_PROOF:139 and :170-175, inside LEMMA HE6-1L's blockquote (122-199) — a unit r4 repair 1 explicitly DECLINES to pin — and inside no other span.

**(a) LEMMA HETOW-2** is cured by the new pin `HETOW-KEY-BRIDGE` declared in repair 1 above.

**(b) \(q(k)\).** The master posits \(q(k)\) as instance data by `(Q-DEF)` and consumes it at `(HE6-SEAM)` and in S3.2's print-frame read, and the finding is right that the only source unit defining it is LEMMA HE6-1L. The honest cure is to pin that unit; the alternative — leaving the definition of a symbol that appears in a displayed theorem hypothesis outside every span — is exactly what S0.2's restored no-unpinned-material clause forbids.

**r4 repair 1's declination is preserved, and is not what is being reversed.** That repair declined LEMMA HE6-1L as the adjudication target of `HE6-SLOT-SEAM`, on the ground that HE6-1L "describes the *set* of residues realised at a height … It does not evaluate a given \(A\)". That ground is correct and stands: HE6-1L supplies no per-\(A\) slot law, and `HE6-SLOT-SEAM` remains LEMMA HE6-0″. Declining a unit as the supplier of one consumption is not a declaration that the master consumes nothing from it. What it does supply, and what is pinned here, is the definition of \(q(k)\) and the \(\varpi\)-vs-\(n(k)\) normalizer ratio.

**New pin `HE6-LIFT-1L`** — LEMMA HE6-1L ((LIFT), corrected) with its `[r2]` correction record, its RIDER, and the two non-propagation boxes. Delimiters:

- first: `> **LEMMA HE6-1L [r1; display corrected [r2], PE2 F-1] ((LIFT), corrected =`
- last: `> q(0) = q(1) = 0; (3,1,2): T(1) = ∅), per PE2 F-1.`

Verification remark: in `lean/notes/openmath/HE6_PROOF_2026-08-08.md`, on 2026-08-13, `grep -cFx` returned **1** for each of the two lines; the first (line 130) precedes the last (line 199); the span contains the corrected reachable-set display, the defining line `> where η_θ^{q(k)} := res(ϖ(θ)^k/n(k)(θ)) is the RIDER's fixed normalizer` (`grep -cFx` → **1**, line 139), the RIDER, the `[r2]` correction record and both non-propagation boxes, ending immediately before the next sibling unit, DEFINITION HE6-1. Conditions 1–4 of S0.2 hold.

**Reconciliation of `(Q-DEF)` with the pinned display, so the seam is not re-opened.** Add at the new pin:

> The source defines the ratio in the inverse direction from this master: `η_θ^{q(k)} := res(ϖ(θ)^k/n(k)(θ))`, with the RIDER's evaluation "ϖ(θ)^k/n(k)(θ) = (θ^{e₁}π^{−h})^{q} = η_θ^{q}". This master's `(Q-DEF)` writes \(\operatorname{res}(n(k)(\xi)/\varpi(\xi)^k)=\eta_\xi^{-q(k)}\), the reciprocal of the same nonzero element of \(K\), so the two agree on \(q(k)\) with no sign convention left free; the minus sign of `(HE6-SEAM)` is the same one LEMMA HE6-0″ `[r2]` corrected. The pin is declined as the supplier of a per-\(A\) slot law (r4 repair 1); it is consumed only for \(q(k)\), for the `(LIFT)`/`(OCC)` reachable set, and for the RIDER's universality of the twist.

**The S0.2 clause and r4's count corrected.** Replace, in the clause r4 repair 8 appended to S0.2, the sentence

> Two consumptions were cured this way at r4: HE6's standing peel convention became `HE6-PEEL-CONVENTION`, and LEMMA HE7-8 became `HE7-REF-TERM`.

by

> Four consumptions have been cured this way. At r4: HE6's standing peel convention became `HE6-PEEL-CONVENTION`, and LEMMA HE7-8 became `HE7-REF-TERM`. At r5, after the r4 pass found the r4 sweep incomplete: LEMMA HETOW-2, named in S3.4, became `HETOW-KEY-BRIDGE`; LEMMA HE6-1L, the sole source of \(q(k)\)'s definition for `(Q-DEF)`, became `HE6-LIFT-1L`; and LEMMA HE7-12, consumed by S1.8B, entered with LEMMA HE7-13 as `HE7-PERT-TRANSPORT`.

and replace r4 repair 13's opening sentence

> Two source units this master consumes were covered by no pin. Both are added as existing-text spans; neither requires a source edit.

by

> Two source units this master consumes were covered by no pin at the time of r4. Both are added as existing-text spans; neither requires a source edit. The r4 hostile pass showed this sweep incomplete: three further consumptions were found and cured at r5 (repairs 1 and 4 of that round), so the count of cured consumptions reads two of five.

**The sweep, re-run and recorded.** So that the S7 gate can check rather than repeat it, here is the enumeration behind the claim, with its residues:
LEMMA HETOW-3 — consumed by S3.4's "The full-side identity gives \(f_S=f\)", covered inside `HETOW-A` clause (i), which states "f_S = f with μ₂ = μ₁/(e₂f₂) (HETOW-3)"; LEMMA GENTOW-4.1 — pinned as `GENTOW-4-1`, its clause (c) carrying the partial-tower transport; LEMMA HE7-13 — now inside `HE7-PERT-TRANSPORT`; DEFINITION HE6-1 — inside `HE6-FAMILY`; GENHN-3(a) — named only inside the sentence r4 repair 3 quotes from within `HE3-A-PROOF`, hence internal to a pinned span; HE3's bracketed `[r1-N1]` three-consecutive-slope supplement — named by r4 repair 4(c) only in order to **decline** it, and a declination is not a consumption. This enumeration is recorded, not asserted complete; the gate re-runs it.

**Verification remark (landmarks).** Both superseded sentences quoted above — the S0.2 "Two consumptions were cured this way at r4 …" sentence and r4 repair 13's "Two source units this master consumes were covered by no pin. …" opening — returned **1** under `sed -n '1,2608p' T2_SIGMA_LADDER_MASTER_2026-08-12.md | grep -cF -- '<the quoted string>'` on 2026-08-13.

---

## r5 repair 5 — m-3 (minor): transition 6 folded into the two-trigger completeness proof

**The finding repaired.**

> The proof that only two transitions need the key-freeness test enumerates three of the four other transitions; the S1.9 key-boundary decomposition — transition 6 of the very rank table installed in the same round — is not addressed. … Its emitted blocks are key-free by S1.9's definition … so the claim is TRUE — but the displayed completeness proof does not cover it, and "any other" is therefore asserted over a case the argument omits.

The claim is preserved and the argument is completed. Append to r4 repair 2's inserted paragraph, inside the same blockquote, immediately after its final sentence "Both are tested.":

> The sixth transition of `(RANK)`, the key-boundary decomposition of S1.9, cannot destroy key-freeness either, and for a definitional rather than a derived reason: S1.9 requires a key-boundary decomposition to consist of "monic polynomials \(P_i\in O[x]\) and key-free residual blocks \(B_j\)", so every block it hands to a successor state satisfies `(KEY-FREE)` at the same key by the decomposition's own defining clause, while the \(P_i\) are emitted factors and not states. The six transitions of `(RANK)` are therefore exhaustively accounted: 1, 2, 3 and 6 preserve key-freeness and need no test; 4 and 5 replace the key and are tested.

Replace, in clause 5 of HE7.A as installed by r4 repair 2, the phrase

> and is not needed after any other, key-freeness being preserved by side and label splits and by `(MID-PEEL)` itself

by

> and is not needed after any other, key-freeness being preserved by side and label splits, by `(MID-PEEL)` itself, and by the S1.9 key-boundary decomposition, whose residual blocks are key-free by definition

and replace, in S5 ledger item 15 as installed by the same repair, the sentence

> Side and label splits and `(MID-PEEL)` itself preserve key-freeness and need no test.

by

> Side and label splits, `(MID-PEEL)` itself, and the S1.9 key-boundary decomposition preserve key-freeness and need no test.

**Verification remark (landmarks).** The anchor sentence "Both are tested." and the two superseded strings quoted above (clause 5's "and is not needed after any other …" phrase, and S5 item 15's "Side and label splits …" sentence) each returned **1** under `sed -n '1,2608p' T2_SIGMA_LADDER_MASTER_2026-08-12.md | grep -cF -- '<the quoted string>'` on 2026-08-13.

---

## r5 repair 6 — m-4 (minor): the five Source-pin lines set in final form

**The finding repaired.**

> The per-record Source-pin lines were not maintained against the hypothesis the same round added. r4 repair 13 rewrote three of them and left three holes … it means no record's declared pin set currently instantiates the master's full hypothesis suite after r4.

Rather than amend three lines and leave the reader to compose four rounds of edits, all five lines are set here in final form. Each supersedes every earlier setting of that line; the superseded settings, quoted byte-exactly from the r4 effective text, are

> - S3.1 (the r1 repair 2 replacement paragraph): after "`HE6-FAMILY`, `HE6-PROOF`, and `HE6-SLOT-SEAM`" read "`HE6-FAMILY`, `HE6-PROOF`, `HE6-SLOT-SEAM`, and `HE6-PEEL-CONVENTION`".

> - S3.2: **Source pins:** `HE6-FAMILY`, `HE6-PROOF`, `HE6-SLOT-SEAM`, and `HE6-PEEL-CONVENTION`.

> - S3.3: **Source pins:** `HE7-A-STMT`, `HE7-SLOT-TRANSFER`, `HE7-MIXED-13P`, `HE7-COCYCLE-2P-THROUGH-R1D`, `HE7-REF-TERM`, `HE6R1-1`, `HE6R1-2`, and `HE6R1-3`.

> Amend the S3.4 source-pin line to: **Source pins:** `HETOW-LABELS`, `HETOW-LABELS-1`, `HETOW-A`, and `HETOW-NORMALIZER-4`.

> **Source pins:** `GENTOW-4-1`, `GENTOW-4-A`, `GENTOW-4-2`, and `GENTOW-ACCEPTANCE-FOLD`.

(the first four being r4 repair 13's three bullets and r3 repair 1's S3.4 amendment, the last being S3.5's base line). Each addition below is justified by the consumption it covers.

> - **S3.1** (in the r1 repair 2 replacement paragraph) — **Source pins:** `HE3-A-STMT`, `HE3-A-PROOF`, `HE3-DEF1`, `HE3-HE3-1L`, `HE3-HE3-6`, `HE3-R8-2` through `HE3-R8-5`, `HE6-FAMILY`, `HE6-PROOF`, `HE6-SLOT-SEAM`, `HE6-PEEL-CONVENTION`, and `HE6-LIFT-1L`.
> - **S3.2** — **Source pins:** `HE6-FAMILY`, `HE6-PROOF`, `HE6-SLOT-SEAM`, `HE6-PEEL-CONVENTION`, `HE6-LIFT-1L`, and `HE3-A-PROOF`.
> - **S3.3** — **Source pins:** `HE7-A-STMT`, `HE7-SLOT-TRANSFER`, `HE7-MIXED-13P`, `HE7-COCYCLE-2P-THROUGH-R1D`, `HE7-REF-TERM`, `HE7-PERT-TRANSPORT`, `HE6R1-1`, `HE6R1-2`, and `HE6R1-3`.
> - **S3.4** — **Source pins:** `HETOW-LABELS`, `HETOW-LABELS-1`, `HETOW-KEY-BRIDGE`, `HETOW-A`, `HETOW-NORMALIZER-4`, `HE7-REF-TERM`, `HE7-PERT-TRANSPORT`, `HE7-MIXED-13P`, and `HE6R1-3`.
> - **S3.5** — **Source pins:** `GENTOW-4-1`, `GENTOW-4-A`, `GENTOW-4-2`, `GENTOW-ACCEPTANCE-FOLD`, `HE7-REF-TERM`, `HE7-PERT-TRANSPORT`, `HE7-MIXED-13P`, `HE6R1-2`, and `HE6R1-3`.

Justifications, one per addition. **S3.1/S3.2 `HE6-LIFT-1L`:** \(q(k)\) of `(Q-DEF)`, consumed by S1.2's `(HE6-SEAM)` and restated by S3.2's print-frame read, is defined only there (repair 4). **S3.2 `HE3-A-PROOF`:** r4 repair 3 routes S3.2's `(SEC-RANK)` to the stage-α termination clause inside that span. **S3.3 `HE7-PERT-TRANSPORT`:** S1.8B's level-two recentered-key discharge runs through LEMMA HE7-12(c) at every level-two record, S3.3 included. **S3.4 `HETOW-KEY-BRIDGE`:** S3.4's text names LEMMA HETOW-2 by name. **S3.4/S3.5 `HE7-REF-TERM`:** `HETOW-A`(ii) and `GENTOW-4-A`(iii) both name LEMMA HE7-8 in the clause the records consume. **S3.4/S3.5 `HE7-PERT-TRANSPORT`:** the same two clauses name LEMMA HE7-12, and S1.8B applies at these records too. **S3.4/S3.5 `HE7-MIXED-13P`:** clause 4 demands side and label blocks whenever \(P_2\) has at least two sides, and ANNEX-LEMMA HE7-13′ is their supplier. **S3.4/S3.5 `HE6R1-3`:** the clause-5 peel at \(\Phi_2\), available there by `HETOW-KEY-BRIDGE` and `GENTOW-4-1`(c) respectively; S3.4's standing restraint "Any key-boundary contribution is handled by T2.KEY-BOUNDARY, not by a purported single \(\Phi_2\)-peel" is untouched and continues to govern the **proper-gcd** case, which routes to S1.9 — `HE6R1-3` is listed for the exact-division case \(\Phi_2\mid f\) that clause 5 now states. **S3.5 `HE6R1-2`:** S3.5's text consumes it by name ("HE6R1-2 gives a constant \(c_g=dv_2(g(\xi))\)").

**Verification remark (landmarks).** Each of the five superseded settings quoted above returned **1** under `sed -n '1,2608p' T2_SIGMA_LADDER_MASTER_2026-08-12.md | grep -cF -- '<the quoted string>'` on 2026-08-13. The S3.5 line is quoted as it stands in the base text; the S3.4 line as r3 repair 1 set it; S3.2 and S3.3 as r4 repair 13 set them; S3.1's HE6 tail as r4 repair 13's bullet set it.

---

## r5 repair 7 — m-5 (minor): the `(MID-MASS)` / degenerate-guard seam repaired

**The finding repaired.**

> Assembly seam: the r3 degenerate-guard insert splits a sentence of r2 repair 3, and r4 inserted twice into the same broken sentence without repairing it. … The effective text therefore reads "… **Degenerate guard.** … apply only at \(\nu\ge2\). / and separability of \(G\) gives …", leaving an orphaned clause beginning "and".

The insertion points installed by r3 repair 5 and r4 repair 2 are correct and are left where they are; what is repaired is the connective they orphaned. In r2 repair 3's inserted subsection "Mid-chain boundary produced by recentering", replace the line

> and separability of \(G\) gives

by

> Separability of \(G\) also gives

The gcd display that follows is unchanged, and its scope is unchanged: it holds at every \(\nu\ge1\) (at \(\nu=1\) trivially, \(G'=1\)), so the repair restores a sentence without narrowing a statement.

**Verification remark (landmark).** `sed -n '1,2608p' … | grep -cF -- '> and separability of \(G\) gives'` → **1**.

---

## r5 repair 8 — pin inventory 29 → 32: bookkeeping

Three pins are added by repairs 1 and 4. New `(PINS)` rows, each in its file's block:

> `&\texttt{HE6-LIFT-1L}&\text{LEMMA HE6-1L ((LIFT), corrected) with its [r2] record, RIDER and non-propagation boxes}\\`

> `&\texttt{HE7-PERT-TRANSPORT}&\text{LEMMA HE7-12 (SLOT-DOMINATION) and LEMMA HE7-13, statements and proofs}\\`

> `&\texttt{HETOW-KEY-BRIDGE}&\text{LEMMA HETOW-2 (composed key = key-family member up to an above-line perturbation), statement and proof}\\`

In the effective S0.2 (r2 repair 1 as amended by r3 repair 1 and r4 repair 13) replace "The 29 pins are the following existing-text pairs" by "The 32 pins are the following existing-text pairs". In the effective S7 pin gate replace "The expected pin count is 29" by "The expected pin count is 32"; the expected synthetic-marker count stays zero, and the expected source edit count stays zero. Pin arithmetic for the gate: 26 (r2) → 27 (r3 repair 1 splits `HETOW-LABELS`) → 29 (r4 repair 13 adds two) → **32** (r5 adds three).

The standing S7 consumption check added by r4 repair 13 ("Also enumerate every source display the master text quotes, names, or leans on … A consumption outside every span fails the gate") is unchanged; repair 4 above records the sweep it now returns.

**Verification remarks (landmarks).** `sed -n '1,2608p' … | grep -cF` → **1** for each of `The 29 pins are the following existing-text pairs` and `The expected pin count is 29`.

---

## r5 counter

r5 folds repairs for both GAPs (G-1, G-2) and all five minors (m-1 … m-5) of the r4 hostile pass of record, plus the pin-inventory consequences. Its substantive content is one object: the perturbation transport LEMMA HE7-12, previously consumed at two theorem-statement changes and named nowhere, is now pinned as `HE7-PERT-TRANSPORT` and cited at the two places that need it. `(SEC-RANK)` at the composed key is re-routed to `HETOW-A`(ii) and `GENTOW-4-A`(iii), which state the conclusion at \(\Phi_2\), so the master performs no key transfer of its own; the level-two mid-chain peel at a recentered key is derived in the new S1.8B from LEMMA HE7-12(c) and item (11) of its proof, replacing r4's insufficient appeal to LEMMA HE7-8's `[r3]` clause. One theorem-adjacent addition is a new named obligation, not a new conclusion: `(MP1′)`, the assertion that a recentered level-one key carries a level-one frame at all, which the corpus does not supply and which every state with a level-one recentering in its history now carries. Three named obligations are therefore open: `(LB1)` for clause-4 block construction at level one, `(MP1)` for the clause-5 peel at a recentered level-one key, and `(MP1′)` for reading over a recentered level-one key at any level.

Gap-or-worse repairs reset the clean count (S7: "A gap-or-worse repair resets the clean count"). **The clean-pass counter is RESET to 0 of 2.** The acceptance gate still owes **TWO consecutive clean hostile passes** over the r5 effective text before this note may leave attempt grade \(0/2\); the status line therefore stays "mathematical composition draft, attempt grade \(0/2\)", and by `(GRADE)` every composed instance stays \(0/2\) regardless of supplier grade.

---

## r6 (2026-08-13): the refinement height bound to the side slope, and `(MP1′)` adjudicated and DISCHARGED

*(Opus/Claude repair arm, against the r5 hostile pass of record `runs/comp13/T2P5_output.log` — 0 CRITICAL + 2 GAP + 4 minor; counter resets.)*

**Verification protocol for this round.** Every source line quoted below was checked on 2026-08-13 by exact-full-line search (`grep -cFx`) in the named accepted source file, with the count and the source line number recorded at the point of use. No source file is edited by this round; the expected source edit count remains zero. Landmarks internal to this master are quoted from the **r5 effective text**, and their uniqueness is recorded in the form `sed -n '1,2912p' T2_SIGMA_LADDER_MASTER_2026-08-12.md | grep -cF -- '<string>'` → **1**; the line bound 2912 is the last line of the r5 round and excludes this round's own re-quotations, which would otherwise inflate every count.

**What the two GAPs share.** Both are about something the note named instead of settling. G-1: S1.8B's hypothesis needs "refinement height = side slope", and the index \(k\) of \(L_k(s)\) is unbound at every site of the effective text, so the height was asserted rather than derived, and the offered corroboration cited a line that does not carry it. G-2: `(MP1′)`'s load-bearing negative — that no pinned unit certifies a recentered level-one key as carrying a level-one frame — was asserted without adjudicating the obvious pinned candidate. Repair 1 binds the height from the master's own `(SIDE-COUNT)`, `(SLOT-V)` and `(LIFT)`, as `(REF-HT)`. Repair 2 performs the adjudication; the candidate wins, the fence is **discharged**, and one of the three open obligations is retired.

---

## r6 repair 1 — G-1P5 (GAP): the refinement height BOUND to the side slope as `(REF-HT)`, and the source leg re-cited to the line that carries it

**The finding repaired.**

> S1.8B Step 1 establishes HE7-12's hypothesis dv₂(w) = λ₂ only through an identification the master never makes, and the "two independent legs" that are offered as corroboration do not corroborate it: leg 1 cites a height S1.8 does not bind, and leg 2 quotes a source line that does not carry the height.

with the diagnosis that "`k` is UNBOUND at both sites: neither says k = λ, and no other site of the effective text binds it", that "(LIFT) gives h(L_k(c)) = k, so leg 1 yields dv₂(w) = k, and clause 1 yields λ₂ > T₂; without k = λ₂ these do not compose into HE7-12's hypothesis ν > T₂", and that "the line that carries the height is the UNQUOTED preceding line, HE7_PROOF:924".

**The diagnosis is accepted in full, and the cure is the one the report names — bind the height, do not fence it.** The binding is derivable at the master's own generality from three data already displayed in S1: `(SIDE-COUNT)`, `(SLOT-V)`, and `(LIFT)`. It is installed as `(REF-HT)` at the transition that needs it, and the source leg is re-cited to the line that states the height.

**(a) The binding, in S1.8.** Replace the product-\(1\) sentence

> then \(e'=1\) and \(r'=Y-s\) for some \(s\in K\). The required refinement height lies in \(H_{\mathrm{lift}}\), so `(OCC)` supplies a legal lift. The new key is

by

> then \(e'=1\) and \(r'=Y-s\) for some \(s\in K\), and the slope \(\lambda=u'/e'=u'\) is an INTEGER. The refinement height is that slope:
>
> \[
> \boxed{k=\lambda .}
> \tag{REF-HT}
> \]
>
> `(REF-HT)` is forced, not chosen, and the forcing uses master data only. Every root \(\rho\) of the class being refined satisfies \(d(\Phi(\rho))=\lambda\): by S1.7 clause 4 "the classes associated with the distinct \(r'\) are disjoint and exhaust the roots belonging to the side", and the roots belonging to side \(\lambda\) are exactly the \(DL_\lambda\) roots with \(w_\rho=\lambda\), by `(SIDE-COUNT)` as derived in the proof of clause 1. The increment satisfies \(\deg L_k(s)<D\) (S1.4) and the block's roots lie in \(\operatorname{Pt}\) (S1.5, "Its roots form a designated Galois-stable class contained in \(\operatorname{Pt}\)"), so `(SLOT-V)` applies to the increment at those roots and `(LIFT)` gives
>
> \[
> d\bigl(L_k(s)(\rho)\bigr)=h\bigl(L_k(s)\bigr)=k .
> \]
>
> If \(k\ne\lambda\), the two values \(d(\Phi(\rho))=\lambda\) and \(d(L_k(s)(\rho))=k\) differ, so the ultrametric inequality is an equality and
>
> \[
> d\bigl(\Phi_{\mathrm{new}}(\rho)\bigr)
> =
> d\bigl(\Phi(\rho)-L_k(s)(\rho)\bigr)
> =
> \min(\lambda,k)\le\lambda
> \]
>
> at every root of the class: at \(k>\lambda\) the value does not move at all, at \(k<\lambda\) it falls, and at \(k\le T\) it leaves the window. Only \(k=\lambda\) can raise it, and raising it on the class is what the recentering is for — it is what the next sentence's "new valid development" asserts, and it is what makes `(SEC-RANK)` strictly decrease at this transition. So \(k=\lambda\) is the only admissible height, and the index of \(L_k\) is hereby bound to the side datum. **This binds the height; it does not derive the rise.** That \(d(\Phi_{\mathrm{new}}(\rho))>\lambda\) actually holds at \(k=\lambda\) with the digit \(s\) of the repeated residual factor remains a root-preserving continuation assertion of the carrier, hypothesised by HE7.A and unchanged by this repair.
>
> Two consequences are recorded because later sections read them. First, `(OCC)` is now read at a determined height: the visible domain obligation for this transition is \(\lambda\in H_{\mathrm{lift}}(B)\), a legible integer-height demand precisely because \(e'=1\). Second, at \(e'\ge2\) the slope \(u'/e'\) is not an integer and no \(L_k\) sits at it; that is why the recentering branch is the product-\(1\) branch and the product-\(\ge2\) branch builds a child key instead. `(OCC)` therefore supplies a legal lift at height \(\lambda\), and the new key is

**(b) The same binding in the S2 proof of clause 3.** Replace

> For a repeated \(r'\), if \(e'\deg r'=1\), then \(e'=1\) and \(r'=Y-s\). The required height is in \(H_{\mathrm{lift}}\); `(OCC)` supplies \(L_k(s)\); and the linear recentering of S1.8 gives the next block while preserving its root set and inherited invariants.

by

> For a repeated \(r'\), if \(e'\deg r'=1\), then \(e'=1\), \(r'=Y-s\) and \(\lambda\) is an integer. The required height is the side's own slope, \(k=\lambda\) by `(REF-HT)`; that height is in \(H_{\mathrm{lift}}\); `(OCC)` supplies \(L_\lambda(s)\); and the linear recentering of S1.8 gives the next block while preserving its root set and inherited invariants.

**(c) S1.8B Step 1, rebuilt on the binding.** In the S1.8B paragraph installed by r5 repair 2, replace the opening derivation

> Each refine increment is \(L_{k}(s)\) at the exact height \(k=\lambda_2\) of the side being refined (S1.8's recentering, `(OCC)` supplying the legal lift at that height), and every side slope of a state satisfies \(\lambda_2>T\) by clause 1 of HE7.A.

by

> Each refine increment is \(L_\lambda(s)\) at the side's own slope, by `(REF-HT)`: the lift index is bound to the side datum, so `(LIFT)` returns \(h(L_\lambda(s))=\lambda\) with no further identification, and `(OCC)` is read at \(\lambda\in H_{\mathrm{lift}}\). At level two the slot function is \(dv_2\) and the refined side's slope is \(\lambda_2\), so the increment \(w\) has \(dv_2(w)=\lambda_2\) — the conjunct the r5 text asserted without deriving — and every side slope of a state satisfies \(\lambda_2>T\) by clause 1 of HE7.A.

and replace the corroboration sentences

> The source states the same height independently, inside the same pin: `> (it exists: λ₂ > T₂ satisfies (‡₂) by §S4.3) and Ψ̃^{(1)} := Ψ̃ − w.` The two legs — this master's clause 1 plus S1.8's lift height, and LEMMA HE7-13's own display — agree, so the hypothesis is not carried by a single textual reading.

by

> The source displays the same configuration, inside the same pin, at the line that carries the height —
>
> > `> s₂ ≠ 0). Let w be a (LIFT₂) polynomial at height λ₂ with residue s₂`
>
> (`HE7_PROOF_2026-08-08.md`:924) — continued by the existence parenthetical
>
> > `> (it exists: λ₂ > T₂ satisfies (‡₂) by §S4.3) and Ψ̃^{(1)} := Ψ̃ − w.`
>
> (:925), which supplies not the height but the fact that a lift AT that height exists — the source's own `(OCC)`. The r5 text quoted only the second line and called the two readings independent legs. That claim is **withdrawn**: both lines belong to LEMMA HE7-13's hypothesis-side description of the α-refine configuration, not to a derivation of it, and \(\lambda_2>T_2\) inside them is HE7-13's own hypothesis. They are recorded here as a **corroboration** of `(REF-HT)` — confirmation that the configuration this master derives is the configuration LEMMA HE7-12/13 are written about — and the height itself is carried by `(REF-HT)`, a master-side derivation, and by nothing textual.

**Verification remark (source).** In `lean/notes/openmath/HE7_PROOF_2026-08-08.md`, on 2026-08-13, `grep -cFx` returned **1** for `> s₂ ≠ 0). Let w be a (LIFT₂) polynomial at height λ₂ with residue s₂` (line 924) and **1** for `> (it exists: λ₂ > T₂ satisfies (‡₂) by §S4.3) and Ψ̃^{(1)} := Ψ̃ − w.` (line 925); both lie strictly inside the `HE7-PERT-TRANSPORT` span (812–951), and 924 precedes 925 inside LEMMA HE7-13's statement.

**Verification remark (landmarks).** Under `sed -n '1,2912p' T2_SIGMA_LADDER_MASTER_2026-08-12.md | grep -cF -- '<the quoted string>'` on 2026-08-13, each of the four superseded master strings returned **1**: the S1.8 product-\(1\) sentence (line 575), the S2 clause-3 sentence (775), and S1.8B Step 1's opening derivation and corroboration sentences (both on line 2698). The three master-internal citations the new text leans on are also unique: S1.7 clause 4 (530), the `(SIDE-COUNT)` grouping sentence "Group the roots according to the value \(w_\rho\), and let \(n_\lambda\) denote the number for which \(w_\rho=\lambda\)." (720), and S1.5's "Its roots form a designated Galois-stable class contained in \(\operatorname{Pt}\)." (423).

---

## r6 repair 2 — G-2P5 (GAP): `(MP1′)` adjudicated against `HE3-A-PROOF`'s stage-α passage — DISCHARGED, and the obligation retired

**The finding repaired.**

> `(MP1′)`'s load-bearing negative — that no pinned unit certifies a recentered level-one key as carrying a level-one frame — is asserted without adjudicating `HE3-A-PROOF`'s stage-α passage, which states the opposite fifteen lines above the passage r4 repair 3 already mines from the same pin.

with the two aggravating specifics that "`(MP1′)` carries no list and no reason" where r4's `(MP1)` carries a per-pin declination list, and that "The master's own level-one data are largely key-free by construction … so at least part of what `(MP1′)` names is either master-side or already pinned. The note argues neither way."

**The adjudication is performed here, and the pinned candidate wins.** The negative is withdrawn and the obligation is discharged, not narrowed to a declination list. The discharge rests on four pinned units, all four of which are already on both level-one records' Source-pin lines as r5 repair 6 set them: `HE3-A-PROOF`, `HE6-SLOT-SEAM`, `HE6-FAMILY`, `HE6-PROOF`.

**Span supersession.** Replace the entire r5 subsection running from its heading

> ### The one configuration the transport does not reach: `(MP1′)`

through its final sentence

> The two are independent of the level-two derivation above, which reads over an unrecentered level-one frame and recenters only the level-two key.

by:

> ### S1.8C The level-one frame over a recentered key, adjudicated and supplied
>
> Repair 4(b)'s sentence
>
> > If the dividing key is the level-one **child** key \(\Psi_{\lambda,r'}\), the state is a level-two state and the discharge is LEMMA HE6R1-3, as above.
>
> is exact when the level-one key beneath that child key is the **original** \(\Phi'\). When the level-one key beneath is itself a recentered \(\Phi''=\Phi'-L_\lambda(s)\), a prior question arises, and this subsection settles it: does a state read over \(\Phi''\) have a level-one frame at all?
>
> **What has to be supplied.** For a state whose level-one key is \(\Phi''\), S1.2–S1.7 demand (i) the same \((T1)/(T2)\) point set \(\operatorname{Pt}\); (ii) the same \(dv\); (iii) the same \(\varpi\); (iv) the same \(K\); (v) the same \(T=D'h\); (vi) DEFINITION HE6-1's test family over \(\Phi''\); and (vii) a \(\Phi''\)-development with its lower hull and its label read — so that a state built over \(\Phi''\) instantiates HE7.A at all, at level one or above.
>
> **The supplying text.** `HE3-A-PROOF` is the §S6.3 proof unit of THEOREM HE3.A. Strictly inside it stands the stage-α step, HE3's own inductive treatment of exactly this transition:
>
> > *Stage-α step.* If the read refines at (λ, s) (a residual root of
> > multiplicity m ≥ 2 — so the leaf is not decided at this node), then by
> > LEMMA HE3-2(b) the recentered key Φ″ has a polygon whose portion above
> > λ has length exactly m, the corresponding block of D′m roots is
> > S_{λ, Z−s} … and this block's
> > own labels are read at Φ″ …
> > Apply the inductive hypothesis to the sub-block: it is the
> > label-class of a multiplicity-m system over the SAME stage ring, with
> > the same (e₁, f₁), so its pieces compose into the dictionary as claimed.
>
> The configuration is this master's, exactly. "Refines at (λ, s)" with "a residual root of multiplicity m ≥ 2" is clause 3's repeated \(r'=Y-s\) with \(s\in K\); LEMMA HE3-2(b)'s recentered key exists only at an integer slope, which by `(REF-HT)` and \(e'=1\) is the product-\(1\) branch and no other; and the sub-block the passage carries to \(\Phi''\) is the root block this master's recentering "keeps".
>
> **Component by component.**
>
> **(i)–(v) The stage does not move, and the level-one frame is stage data.** The passage places the refined system "over the SAME stage ring, with the same (e₁, f₁)". Each of (i)–(v) is a function of that datum and of nothing else. `HE6-SLOT-SEAM` — the pinned unit this master consumes for `(SLOT-V)` and `(HE6-SEAM)` — states its slot law at
>
> > `> ξ be ANY point of K̄₀ satisfying (T1) and (T2). Then`
> > `> dv(A(ξ)) = min_i(e₁v(a_i) + ih) EXACTLY, and the residue of the attaining`
> > `> class, read after division by ϖ(ξ)^{dv(A)}, is ι_ξ(γ)·η_ξ^{−q} **[r2 sign`
>
> — a law about an \(A\) with \(\deg A<D'\) and about a point \(\xi\), whose parameters are \(e_1\), \(h\), \(\varpi\), \(\eta\), \(\iota\) and \(\psi\), and in which no key occurs. The same pinned unit says so twice in its own words. Its proof records
>
> > `> irreducible ψ of degree f₁); it never uses Φ′(ξ) = 0. ∎* **Codex PE1`
>
> and its correction record states that the restatement exists precisely so that the law may be applied off the key:
>
> > `> finding 6 is the observation that GENHN-2 as PASTED is stated at roots θ of`
> > `> Φ′ only, while this note applies it at roots of f and at roots of the`
> > `> (generally reducible) test polynomials — an overconsumption cured by this`
>
> Hence (i) the point set — (T1)/(T2) are conditions on \(\xi\) alone — (ii) \(dv\), (iii) \(\varpi\), (iv) \(K\), fixed by the \(\psi\) of degree \(f_1\) named in the same span, and (v) \(T=D'h\) with \(D'=e_1f_1\), are determined by the stage ring and \((e_1,f_1)\), which the passage holds fixed. They are not "carried by" \(\Phi''\): nothing about them moves when the key does. That is why no pin was ever going to state them in the form `(MP1′)` demanded, and why the absence of such a pin was not evidence of a gap.
>
> **(vi) DEFINITION HE6-1's family over \(\Phi''\).** `HE6-FAMILY` is that definition, and its recipe splits cleanly. The test data are chosen key-free —
>
> > `> irreducible with r(0) ≠ 0. Choose, by (LIFT), B_t ∈ O[x] with`
> > `> deg B_t < D′, dv(B_t) = (d−t)u and res(B_t(θ)/ϖ(θ)^{(d−t)u}) = c_t (and`
>
> three conditions naming \(D'\), \(dv\), \(\varpi\), \(\theta\) and the coefficients of \(r\), and no key. The assembly is then a formula in whatever monic degree-\(D'\) key is current —
>
> > `>     Ψ_{κ,r} := Φ′^{ℓd} + Σ_{t<d} B_t·Φ′^{ℓt}  ∈ O[x],`
> > `> monic of degree D″ := D′ℓd (each B_tΦ′^{ℓt} has degree < D′ℓd). For ℓ = 1`
>
> and \(\Phi''\) is monic of degree \(D'\), since \(\deg L_\lambda(s)<D'\) by S1.4. Substituting \(\Phi''\) for \(\Phi'\) therefore reproduces the construction verbatim, with the same \(D''=D'\ell d\) and the same degree bookkeeping. The same pinned display goes further and identifies \(\Phi''\) as a member of the family:
>
> > `> this is HE3's recentered-key family enlarged in DEGREE; for ℓ ≥ 2 it is a`
>
> At \((\ell,d)=(1,1)\) the member \(\Psi_{\lambda,Z-s}=\Phi'+B_0\) IS the recentered key, \(B_0\) being the \(\varpi\)-frame form of \(-L_\lambda(s)\) under `(HE6-SEAM)`. A recentered level-one key is not a foreign object to HE6; it is one of HE6's own test polynomials.
>
> **(vii) The \(\Phi''\)-development, the label read, and the instantiation.** The passage supplies all three directly. "the recentered key Φ″ has a polygon whose portion above λ has length exactly m" is the \(\Phi''\)-development with its lower hull. "this block's own labels are read at Φ″" is the label read performed at the new key. And the closing sentence does the decisive thing: it APPLIES THEOREM HE3.A to the sub-block at \(\Phi''\). That is not an enumeration of frame data; it is the assertion that every hypothesis of HE3.A holds for the refined system at \(\Phi''\). Since the S3.1 record is exactly the claim that HE3.A's data instantiate this master's S1.2–S1.7, the passage transports that record to \(\Phi''\).
>
> **The HE6 record's leg.** S3.1 is HE3; S3.2 is HE6, whose family is enlarged beyond HE3's, so the transport has to be licensed for HE6's classes too. It is, inside `HE6-PROOF`, in the closing paragraph of the pinned proof unit of THEOREM HE6.A:
>
> > `**This is HE3's LEMMA HE3-4 in full generality**, so HE3's THEOREM HE3.A`
> > `assembly (§S6.3 there: base read + stage-α + stage-CS + embedded genres) may`
> > `be run with HE3-4 replaced by THEOREM HE6.A — with the one caveat of §S7 for`
> > `histories containing an ℓ ≥ 2 side with a repeated residual factor.`
>
> The "§S6.3 there" of that paragraph is HE3's §S6.3, i.e. the `HE3-A-PROOF` span quoted above — not HE6's own §S6.3, which is the sibling unit immediately after this span. The paragraph names **stage-α** and licenses running it with HE6's classes. Its caveat names a configuration this master routes elsewhere: an \(\ell\ge2\) side with a repeated residual factor is \(e'\deg r'\ge2\), the product-\(\ge2\) child jump of clause 3, of which S3.2's own text already says "When repeated factors occur, HE6 supplies the test step and the continuation is the level-two construction recorded in the next instance". Nothing behind that caveat is consumed here.
>
> **Honest status of the discharge.** Derived master-side: the configuration match (through `(REF-HT)`), the key-freeness of (i)–(vi) read off the pinned displays, and the composition of the passage with the S3.1/S3.2 substitutions. Consumed, not reproved: HE3's own inductive step, at HE3's own rigour, which S4.1 already grades ("HE3 is consumed at the grade stated by its supplied HEAD") and which `(GRADE)` already minimises over. The adjudication does not claim the passage is beyond challenge. It claims something narrower and sufficient: the passage is the step without which THEOREM HE3.A is not proved at all, so a master that pins `HE3-A-PROOF` and consumes THEOREM HE3.A cannot simultaneously declare the frame that step reads over to be supplied by no pin.
>
> **What the discharge does NOT give.** It does not touch `(MP1)`. Peeling a recentered level-one key still needs item 5 of the `(MID-PEEL)` input suite — the peeled key's certified orbit/\((e,f)\) decomposition — which requires \(\Phi''\) irreducible, asserted nowhere and the stated reason r4 declined `HE6-PEEL-CONVENTION` for that case. It does not touch `(LB1)`. And it is **relative**: it transports the S3.1/S3.2 records to \(\Phi''\) carrying whatever conditionality they carry at \(\Phi'\), so a state over \(\Phi''\) is `(LB1)`-conditional and `(MP1)`-conditional on exactly the same triggers as a state over \(\Phi'\). What is removed is the extra frame-level obligation, not the level-one fences.
>
> **Two reading directives that come with the discharge.**
>
> 1. **Only the refined sub-block travels to \(\Phi''\).** The passage's own `[r1, F5]` bracket is explicit — "the above-λ blocks' labels are NOT readable at Φ″ — they are read at Φ′ (or at their own recenterings), where the induction reads them". Master-side this is automatic, since S1.8's recentering "keeps … the same root block"; it is recorded so that no instance reads a sibling side or label class at the recentered key.
> 2. **The discharge is invoked at the product-\(1\) branch and nowhere else.** The passage's configuration is a repeated \(K\)-rational residual root at an integer slope; by `(REF-HT)` that is clause 3's product-\(1\) branch, the only transition of `(RANK)` that recenters a key.
>
> **The name `(MP1′)` is retired.** r5 named the assertion (i)–(vii) as an obligation on the ground that "no pinned unit certifies" it. That ground is withdrawn: `HE3-A-PROOF`, `HE6-SLOT-SEAM`, `HE6-FAMILY` and `HE6-PROOF` certify it between them, and all four are already on both level-one records' Source-pin lines. The name is kept here only so that r5's text resolves — `(MP1′)` denotes (i)–(vii) — and it now denotes a consequence of the pins, not an obligation. No instance record carries it and no ledger item fences it.
>
> This subsection and S1.8B are independent: S1.8B recenters the level-two key over an unrecentered level-one frame, while S1.8C is about the level-one key itself being recentered. A state may be in both configurations at once, and then it carries S1.8B's level-two discharge over S1.8C's level-one frame.

**Propagation, replacing r5 repair 2's four amendments.** Each landmark is unique in the r5 effective text (counts at the end of this repair).

1. In the S3.1/S3.2 "Level-one fence" append, replace "This record likewise discharges neither `(MP1)` nor `(MP1′)`." by "This record likewise does not discharge `(MP1)`. It does supply the level-one frame over a recentered key: the obligation `(MP1′)` named at r5 is discharged in S1.8C from this record's own pins, so no read is fenced merely for having a level-one recentering in its history."
2. Replace S5 item 17, "17. Level-one clause-5 reads at a **recentered** key remain conditional on the named obligation `(MP1)`, and any read whose history contains a level-one recentering remains conditional on `(MP1′)`. The original-key level-one peel is discharged by `HE6-PEEL-CONVENTION`; the level-two peel at a DEFINITION HE6-1 key by `HE6R1-3`, and at a recentered level-two key by `HE7-PERT-TRANSPORT` clause (c) carrying `HE6R1-3` to that key (S1.8B).", by "17. Level-one clause-5 reads at a **recentered** key remain conditional on the named obligation `(MP1)`. Reading OVER a recentered level-one key is not an obligation: the frame is supplied in S1.8C from `HE3-A-PROOF`, `HE6-SLOT-SEAM`, `HE6-FAMILY` and `HE6-PROOF`, and the `(MP1′)` named at r5 is retired. The original-key level-one peel is discharged by `HE6-PEEL-CONVENTION`; the level-two peel at a DEFINITION HE6-1 key by `HE6R1-3`, and at a recentered level-two key by `HE7-PERT-TRANSPORT` clause (c) carrying `HE6R1-3` to that key (S1.8B)."
3. In S4.2's exclusion list, replace the item "- an unconditional read at any level over a recentered level-one key;" by "- a read over a recentered level-one key that is free of this master's other level-one conditions: the frame is supplied (S1.8C), but `(LB1)` and `(MP1)` apply at a recentered key on exactly the triggers on which they apply at the original key;".
4. In S4.1, replace "subject to the explicitly named level-one obligations `(LB1)`, `(MP1)` and `(MP1′)`" by "subject to the explicitly named level-one obligations `(LB1)` and `(MP1)`".

**`HE6-PROOF`'s delimiters, quoted rather than left to the gate.** The discharge leans on the closing paragraph of that span, so the span's boundary is fixed here instead of being the gate's work. The row description "the complete proof unit of THEOREM HE6.A" resolves to the `###` unit `### S6.2 PROOF OF THEOREM HE6.A`, which by S0.2's boundary rule ends immediately before the next `###` unit of equal rank, `### S6.3 Multiplicity ≥ 2 on an ℓ = 1 side (the stage-α node) is unaffected`. This is the practice r4 repair 6 set for `###`-headed units. Delimiters:

- first: `### S6.2 PROOF OF THEOREM HE6.A`
- last: `histories containing an ℓ ≥ 2 side with a repeated residual factor.`

Verification remark: in `lean/notes/openmath/HE6_PROOF_2026-08-08.md`, on 2026-08-13, `grep -cFx` returned **1** for each of the two lines; the first (line 639) precedes the last (line 666); the span contains the four numbered steps of the proof, its ∎, and the closing transfer paragraph, ending immediately before the next sibling unit §S6.3. Conditions 1–4 of S0.2 hold. Accordingly, in r5 repair 3's replacement text, replace "and `HETOW-KEY-BRIDGE`, `HE7-PERT-TRANSPORT`, `HE6-LIFT-1L` (r5) — **14 of 32**." by "`HETOW-KEY-BRIDGE`, `HE7-PERT-TRANSPORT`, `HE6-LIFT-1L` (r5); and `HE6-PROOF` (r6) — **15 of 32**." and replace "The other 15 pins are description-only at both ends. Totals: 14 pairs + 3 first-only + 15 description-only = 32." by "The other 14 pins are description-only at both ends. Totals: 15 pairs + 3 first-only + 14 description-only = 32." The pin count itself is unchanged at 32; no pin is added or removed by this round.

**Verification remark (source).** On 2026-08-13, `grep -cFx` returned **1** for each of the following, in the file and at the line shown.

In `lean/notes/openmath/HE3_PROOF_2026-08-08.md`, all strictly inside the `HE3-A-PROOF` span, whose delimiters `### S6.3 PROOF OF THEOREM HE3.A` (1092) and `leaf's history, so THEOREM HE3.A is proved. ∎` (1205) each returned **1**:

> `*Stage-α step.* If the read refines at (λ, s) (a residual root of` — 1149
> `multiplicity m ≥ 2 — so the leaf is not decided at this node), then by` — 1150
> `LEMMA HE3-2(b) the recentered key Φ″ has a polygon whose portion above` — 1151
> `λ has length exactly m, the corresponding block of D′m roots is` — 1152
> `own labels are read at Φ″ — **[r1, F5: specifically, at the part of` — 1155
> `above-λ blocks' labels are NOT readable at Φ″ — they are read at Φ′` — 1162
> `Apply the inductive hypothesis to the sub-block: it is the` — 1164
> `label-class of a multiplicity-m system over the SAME stage ring, with` — 1165
> `the same (e₁, f₁), so its pieces compose into the dictionary as claimed.` — 1166

In `lean/notes/openmath/HE6_PROOF_2026-08-08.md`: lines 217, 218, 219, 234, 235, 236 and 237 all lie strictly inside the `HE6-SLOT-SEAM` span, whose delimiters `> **LEMMA HE6-0″ [r1, R5/F6] (THE SLOT LEMMA at (T1)/(T2) POINTS — the form` (215) and `> restatement.**` (238) each returned **1**; lines 203, 204, 207, 209 and 210 all lie strictly inside the `HE6-FAMILY` unit, whose first line `> **DEFINITION HE6-1 (THE ENLARGED TEST FAMILY).** Let κ = u/ℓ ∈ ℚ in lowest` (201) returned **1**; and lines 663, 664, 665 and 666 lie inside the `HE6-PROOF` span 639–666 declared above.

**Verification remark (landmarks).** Under `sed -n '1,2912p' T2_SIGMA_LADDER_MASTER_2026-08-12.md | grep -cF -- '<the quoted string>'` on 2026-08-13, each returned **1**: the superseded subsection's heading (2704) and its final sentence (2719), which bound the replaced span; the S3.1/S3.2 fence sentence (2723); S5 item 17 as r5 set it (2724); the S4.2 exclusion item (2725); the S4.1 obligation phrase (2726); r5 repair 3's two inventory strings (both 2756); and the S3.2 sentence cited for the HE6 caveat, "On a block whose residuals are all separable, this is a terminal instance of the full theorem." (901).

---

## r6 repair 3 — m-1P5 (minor): S1.7B's unconditionality assertion scoped to carry both surviving level-one fences

**The finding repaired.**

> The one effective-text sentence that asserts unconditionality at every level-one state now contradicts `(MP1′)`, and r5's propagation list does not touch it. … the sentence's closing "What is conditional is the clause-4 route, and only where it is taken" is false after r4 already (clause 5 at a recentered key is `(MP1)`-conditional) and doubly so after r5.

Repair 2 removes the `(MP1′)` half of the contradiction; the `(MP1)` half is older than r5 and survives it, so the sentence is scoped here rather than merely narrowed. Replace, in S1.7B as rewritten by r4 repair 10,

> Clauses 1 and 2 are not: their proofs run on the unsplit hull of \(F\) itself, so the HE3.A and HE6 instance records' clause-1 and clause-2 conclusions are unconditional at every level-one state, multi-side states included. What is conditional is the clause-4 route, and only where it is taken.

by

> Clauses 1 and 2 are not: their proofs run on the unsplit hull of \(F\) itself, so the HE3.A and HE6 instance records' clause-1 and clause-2 conclusions carry no `(LB1)` conditionality at any level-one state, multi-side states included. "Unconditional" is said here of `(LB1)` alone and of clauses 1–2 alone. Two level-one routes remain conditional, each where it is taken: the clause-4 route on `(LB1)`, and the clause-5 peel at a recentered key on `(MP1)` (S1.8A). No level-one route is asserted unconditional simpliciter. Reading over a recentered level-one key is not among the conditions — that frame is supplied in S1.8C — so no clause of these records is fenced for that reason.

**Verification remark (landmark).** The superseded S1.7B sentence-pair quoted above returned **1** under `sed -n '1,2912p' T2_SIGMA_LADDER_MASTER_2026-08-12.md | grep -cF -- '<the quoted string>'` on 2026-08-13 (line 2542). It is quoted here rather than inlined into the command because it contains an apostrophe.

---

## r6 repair 4 — m-2P5 (minor): the count word in r5 repair 2's verification remark

**The finding repaired.**

> r5 repair 2's verification remark announces "the six master-internal landmarks this repair supersedes or anchors on" and then lists SEVEN … All seven verify (above); the count word does not. This is the same inventory defect r5 repair 3 was written to cure one repair later.

Replace, in r5 repair 2's closing verification remark, the phrase

> Each of the six master-internal landmarks this repair supersedes or anchors on

by

> Each of the seven master-internal landmarks this repair supersedes or anchors on

The list itself is unchanged; the r5 pass re-ran all seven and all seven returned **1**.

**Verification remark (landmark).** `sed -n '1,2912p' … | grep -cF -- 'Each of the six master-internal landmarks this repair supersedes or anchors on'` → **1** (line 2738).

---

## r6 repair 5 — m-3P5 (minor): the effective-text orphan repaired, and the third `###` unit numbered

**The finding repaired.**

> Effective-text orphan: the last two paragraphs of r2 repair 3's "Mid-chain boundary produced by recentering" now render under the (MP1′) heading, and the (MP1′) subsection is given the same `###` rank as S1.8B, so by S0.2's own boundary rule the S1.8B unit ends before it. … The second of these is load-bearing for `(RANK)` transition 6 … and now reads as part of a fenced level-one obligation subsection.

Two moves; no mathematics changes.

**(a) The two paragraphs are relocated ahead of the three `###` units.** In S1.8's "Mid-chain boundary produced by recentering", move the two closing paragraphs

> This is the HE6R1-3/HE7-8 `[r3]` mid-chain peel. The value
>
> \[
> d(\widetilde\Phi(\rho))=+\infty
> \]
>
> is never fed into `(WINDOW)`: the boundary branch is taken first.

and

> If a proper nontrivial gcd with \(\widetilde\Phi\), rather than the whole key, occurs, use the general key-boundary decomposition of S1.9 before any window assertion.

so that they sit immediately after the paragraph ending "the monic key itself is not declared irreducible merely because it is a key" and immediately BEFORE the `(MID-PEEL)` input suite paragraph installed by r3 repair 4. This supersedes r3 repair 4's "immediately after" as to ordering only — the suite paragraph now follows these two paragraphs, which follow that anchor — and nothing else about r3 repair 4's insertion changes. The effective order in the subsection is then: r2's prose body, contiguous and in r2's own order; the `(MID-PEEL)` input suite paragraph; and the three `###` units S1.8A, S1.8B, S1.8C. In particular the proper-gcd routing that `(RANK)` transition 6 depends on ("entered from `(MID-PEEL)`'s proper-nontrivial-gcd branch") again reads in the subsection body rather than after a numbered subsection.

**(b) The third `###` unit is numbered.** Repair 2 above renames the unnumbered heading "### The one configuration the transport does not reach: `(MP1′)`" to "### S1.8C The level-one frame over a recentered key, adjudicated and supplied". The three units S1.8A, S1.8B and S1.8C are then deliberate siblings of equal rank: each is a complete numbered unit, each ends immediately before the next by S0.2's boundary rule, each is citable by number, and none continues into the next — which is what the finding asked for, the defect having been that the third unit was both unnumbered and a continuation of the second.

**Verification remark (landmarks).** `sed -n '1,2912p' … | grep -cF` returned **1** for `> This is the HE6R1-3/HE7-8 `[r3]` mid-chain peel. The value` (line 1874) and **1** for `> If a proper nontrivial gcd with \(\widetilde\Phi\), rather than the whole key, occurs, use the general key-boundary decomposition of S1.9 before any window assertion.` (line 1882). The insertion anchor "the monic key itself is not declared irreducible merely because it is a key" is the anchor r3 repair 4 already used and verified.

---

## r6 repair 6 — m-4P5 (minor): the composition into S1.8B's scope at the composed key, displayed

**The finding repaired.**

> r5 repair 6's pin-line justification asserts that S1.8B applies at the composed-key records, but S1.8B's own scope sentence excludes them and the composition is nowhere displayed. … Both bridge units ARE pinned … and the same paragraph names them one sentence later … so the ingredients are present and the claim is true. What is missing is the one-clause composition, at exactly the seam this round exists to close.

The composition is displayed, in S1.8B itself, and the justification sentence is re-pointed at it.

**(a) A scope clause in S1.8B.** Append to S1.8B, immediately after the sentence ending "because LEMMA HE7-12 is a level-TWO statement and this master asserts no level-one analogue of it.":

> **Scope: entry at a composed key.** S1.8B is stated for a chain based at a DEFINITION HE6-1 key \(\Psi=\Psi_{\lambda,r}\). At S3.4/S3.5 the chain is based at the composed key \(\Phi_2\), which is not such a key, and entry costs one composition — performed by the records' own already-listed pins, not by this master. `HETOW-KEY-BRIDGE` gives \(\Phi_2=\Psi_{\kappa_2,\widetilde r}-w\) with \(\deg w<D''\) and "either w = 0 … or dv₂(w) > T₂", and `GENTOW-4-1` clause (c) gives the same at the partial tower. If \(w=0\), the base key IS a DEFINITION HE6-1 key and S1.8B applies literally. If \(w\ne0\), then \(w\) already satisfies LEMMA HE7-12's hypothesis at \(\Psi_{\kappa_2,\widetilde r}\), and Step 1 gives the same for each refine increment \(w_1,\dots,w_j\) by `(REF-HT)`; LEMMA HE7-12(d) folds the whole sum, so
>
> \[
> \Phi_2-W
> =
> \Psi_{\kappa_2,\widetilde r}-\bigl(w+w_1+\dots+w_j\bigr)
> \]
>
> is covered by ONE instance of clauses (a)–(c) at \(\Psi_{\kappa_2,\widetilde r}\). That is the composition `GENTOW-4-A`(iii) already displays as "available by LEMMA HE7-12 with W + w". Step 2 then runs unchanged, at \(\Psi_{\kappa_2,\widetilde r}\) and not at \(\Phi_2\).

**(b) The justification sentence re-pointed.** In r5 repair 6, replace

> **S3.4/S3.5 `HE7-PERT-TRANSPORT`:** the same two clauses name LEMMA HE7-12, and S1.8B applies at these records too.

by

> **S3.4/S3.5 `HE7-PERT-TRANSPORT`:** the same two clauses name LEMMA HE7-12, and S1.8B applies at these records after the single composition its scope clause displays — \(W\leftarrow w+W\), with \(w\) the wrap perturbation supplied by `HETOW-KEY-BRIDGE` resp. `GENTOW-4-1`(c) and the fold by LEMMA HE7-12(d) — so that the chain is read at \(\Psi_{\kappa_2,\widetilde r}\), a DEFINITION HE6-1 key, and not at \(\Phi_2\).

**Verification remark (landmarks).** `sed -n '1,2912p' … | grep -cF` returned **1** for the S1.8B anchor sentence ending "…this master asserts no level-one analogue of it." (line 2702) and **1** for r5 repair 6's justification sentence (line 2864).

---

## r6 repair 7 — the four recorded nits, three cured and one adjudicated

The r5 pass recorded four non-counted nits. They are dealt with here so that a later pass does not have to re-raise them.

**(a) Cured — the item (11) characterisation.** In S1.8B Step 2, replace the phrase

> the one hypothesis of HE6R1-3 that mentions the key at all

by

> every hypothesis of HE6R1-3 that mentions the key

The nit is right that item (11) covers the disk-criterion leg, \(\deg\Psi^{(w)}=D''\) and the \((e,f)\) sandwich, which are three key-mentioning hypotheses and not one; the full quote that follows was already correct.

**(b) Cured — the dangling comma at `(MID-MASS)`.** In r2 repair 3's inserted subsection, replace the line

> Then \(G'\in O[x]\) is monic,

by

> Then \(G'\in O[x]\) is monic, with

so that the sentence r5 repair 7 rebuilt reads "Then \(G'\in O[x]\) is monic, with [the `(MID-MASS)` display]." — the sentence now closing on its own display. The r3 repair 5 degenerate guard, inserted immediately after that display, and then "Separability of \(G\) also gives [the gcd display]" follow unchanged; the comma is the only edit.

**(c) Cured — `HE6R1-3`'s row description.** S1.8B consumes not only LEMMA HE6R1-3's conclusion but its PROOF, through item (11) of LEMMA HE7-12's proof, which is checked against the six facts that proof consumes. Replace the r2 `(PINS)` row

> `&\texttt{HE6R1-3}&\text{LEMMA HE6R1-3}\\`

by

> `&\texttt{HE6R1-3}&\text{LEMMA HE6R1-3, statement and proof}\\`

bringing it into the form the r4/r5-era rows use. The unit is unchanged; the r5 pass confirmed that "LEMMA HE6R1-3 occurs as a unit exactly once" in `HE6R1_RECON_2026-08-08.md` (statement 469–477, proof 479–486), so condition 1 is unaffected.

**(d) Adjudicated, no change — the asymmetric record-level note.** The nit observes that S3.1/S3.2 carried a record-level `(MP1′)` note while S3.3–S3.5 did not. Repair 2 retires `(MP1′)`, so the asymmetry is moot: no record carries a frame note, and the S4.1/S4.2/S5.17 amendments of repair 2 are global.

**Verification remark (landmarks).** `sed -n '1,2912p' … | grep -cF` returned **1** for each of `the one hypothesis of HE6R1-3 that mentions the key at all` (line 2700), `> Then \(G'\in O[x]\) is monic,` (line 1857) and `> &\texttt{HE6R1-3}&\text{LEMMA HE6R1-3}\\` (line 1624).

---

## r6 counter

r6 folds repairs for both GAPs (G-1P5, G-2P5) and all four minors (m-1P5 … m-4P5) of the r5 hostile pass of record, plus the four recorded nits. Its substantive content is two objects. First, `(REF-HT)`: the refinement height of the product-\(1\) recentering is bound to the side's own slope, derived from `(SIDE-COUNT)`, `(SLOT-V)` and `(LIFT)` rather than named, so that S1.8B's use of LEMMA HE7-12 no longer rests on an identification the master never made; the r5 claim that two independent textual legs carried it is withdrawn, and the source display is re-cited to `HE7_PROOF_2026-08-08.md`:924, the line that states the height, and demoted from a leg to a corroboration. Second, the `(MP1′)` adjudication: the r5 negative is withdrawn, and the assertion that a recentered level-one key reads over a level-one frame is DISCHARGED in the new S1.8C from four pins already on both level-one records' lines — `HE3-A-PROOF`'s stage-α step for the \(\Phi''\)-polygon, the \(\Phi''\)-label read and the inductive application of THEOREM HE3.A to the sub-block "over the SAME stage ring, with the same (e₁, f₁)"; `HE6-SLOT-SEAM` for the key-freeness of the level-one slot package ("it never uses Φ′(ξ) = 0"); `HE6-FAMILY` for the family's key-free recipe and for the identification of \(\Phi''\) as its own \((\ell,d)=(1,1)\) member; and `HE6-PROOF` for the licence to run HE3's stage-α with HE6's classes. The discharge is relative and is stated as such: it transports the level-one records to \(\Phi''\) with their existing conditionality, and removes only the frame-level obligation.

No theorem-statement change is made by this round. `(REF-HT)` binds a parameter that clause 3 and S1.8 already quantified over without naming a value; it adds no case and no conclusion. One pin gains a quoted delimiter pair (`HE6-PROOF`), and the pin count stays 32.

**Two named obligations are open**, both at level one: `(LB1)` for clause-4 block construction, and `(MP1)` for the clause-5 peel at a recentered key. r5's counter recorded three; that sentence is r5's own record of r5 and is left standing as such. The third, `(MP1′)`, is retired by repair 2 above.

Gap-or-worse repairs reset the clean count (S7: "A gap-or-worse repair resets the clean count"). **The clean-pass counter is RESET to 0 of 2.** The acceptance gate still owes **TWO consecutive clean hostile passes** over the r6 effective text before this note may leave attempt grade \(0/2\); the status line therefore stays "mathematical composition draft, attempt grade \(0/2\)", and by `(GRADE)` every composed instance stays \(0/2\) regardless of supplier grade.

---

## r7 (2026-08-13): the refinement rise displayed as a stipulated clause of `(REF-HT)` and discharged per instance

*(Opus/Claude repair arm, against the r6 hostile pass of record `runs/comp13/T2P6_output.log` — 0 CRITICAL + 1 GAP + 5 minor; counter resets.)*

**Verification protocol for this round.** Every source line quoted below was checked on 2026-08-13 by exact-full-line search (`grep -cFx`) in the named accepted source file, with the count and the source line number recorded at the point of use. No source file is edited by this round; the expected source edit count remains zero, and no pin is added or removed, so the expected pin count remains 32. Landmarks internal to this master are quoted from the **r6 effective text**, and their uniqueness is recorded in the form `sed -n '1,3293p' T2_SIGMA_LADDER_MASTER_2026-08-12.md | grep -cF -- '<string>'` → **1**; the line bound 3293 is the last line of the r6 round and excludes this round's own re-quotations, which would otherwise inflate every count.

**What the GAP is, and what it is not.** The pass certified every positive leg of `(REF-HT)` — \(d(\Phi(\rho))=\lambda\) at every root of the class being refined, \(d(L_k(s)(\rho))=k\) uniformly in \(\rho\), \(e'=1\Rightarrow\lambda\in\mathbf Z\), the ultrametric case reading, and the exclusion of \(k\le T\) by `(WINDOW)` — together with the whole of the `(MP1′)` adjudication and retirement and the completeness of the two-legs withdrawal. What it refuted is one premise. The NECESSITY direction of `(REF-HT)` ran through "the recentering must raise the value on the class", and this master hypothesises no such thing: the only rise in its text is S1.7 clause 2's, which is about the test polynomial \(\Psi_{\lambda,r'}\); the sentence below the recentering display asserts that a development is valid, which holds at any monic degree-\(D\) key; and `(SEC-RANK)` is itself an underived carrier hypothesis, asserted at every product-\(1\) recentering irrespective of \(k\), so it neither entails the rise nor discriminates \(k=\lambda\) from \(k\ne\lambda\). Repair 1 prices the premise instead of deriving it: the rise becomes a displayed clause (RISE) of `(REF-HT)`, stipulated in the register r4 repair 3 gave `(SEC-RANK)`, with the height binding (HT) derived FROM it by the ultrametric display the pass certified, and with (RISE)'s own discharge recorded per instance from pinned lines. Nothing downstream changes in content: S1.8B Step 1 and r6 repair 6's scope clause consume the binding, and the binding stands.

---

## r7 repair 1 — G-1P6 (GAP): `(REF-HT)` restated in two clauses — (RISE) stipulated and discharged per instance, (HT) derived from it, three unsupported supports withdrawn

**The finding repaired.**

> `(REF-HT)`'s necessity rests on a rise that the effective text nowhere hypothesises. "hypothesised by HE7.A" names no displayed assertion (the only rise in the master, S1.7 clause 2 line 526, is about the test polynomial); the cited "next sentence" (line 581) asserts a valid development, not a rise; `(SEC-RANK)` is a hypothesis and cannot supply it. The BINDING survives as the note's own stipulation ("hereby bound"), so S1.8B Step 1 and r6 rep6's scope clause are unaffected — but "forced, not chosen" / "the only admissible height" and the r6 counter's "No theorem-statement change is made by this round" do not.

**All three sub-findings are accepted.** The rise is hypothesised by no displayed assertion of this master; line 581 does not carry it; `(SEC-RANK)` cannot supply it, and the appeal to it ran the wrong way. The cure is to stop deriving what is being assumed, and to say at the display what is assumed.

**(a) The lead-in and the display.** In the `(REF-HT)` paragraph installed by r6 repair 1(a), replace the lead-in phrase

> The refinement height is that slope:

by

> The recentering at this branch is a REFINE step, and this master stipulates of a refine step both that it raise the key's value on the class it refines and that its increment sit at the side's own slope — the second a consequence of the first, derived below:

and replace the boxed display line

> \boxed{k=\lambda .}

by

> \boxed{
> \begin{aligned}
> \text{(RISE)}\quad & d\bigl(\Phi_{\mathrm{new}}(\rho)\bigr)>\lambda\quad\text{at every root }\rho\text{ of the class being refined},\\[1mm]
> \text{(HT)}\quad & k=\lambda .
> \end{aligned}}

**(b) The opening claim.** Replace the sentence

> `(REF-HT)` is forced, not chosen, and the forcing uses master data only.

by

> The two clauses of `(REF-HT)` are not independent stipulations: (HT) is forced by (RISE), and that forcing uses master data only. (RISE) itself is stipulated, and its status is recorded at the end of this passage.

**(c) The necessity sentences, and the honest status of (RISE).** Replace

> at every root of the class: at \(k>\lambda\) the value does not move at all, at \(k<\lambda\) it falls, and at \(k\le T\) it leaves the window. Only \(k=\lambda\) can raise it, and raising it on the class is what the recentering is for — it is what the next sentence's "new valid development" asserts, and it is what makes `(SEC-RANK)` strictly decrease at this transition. So \(k=\lambda\) is the only admissible height, and the index of \(L_k\) is hereby bound to the side datum. **This binds the height; it does not derive the rise.** That \(d(\Phi_{\mathrm{new}}(\rho))>\lambda\) actually holds at \(k=\lambda\) with the digit \(s\) of the repeated residual factor remains a root-preserving continuation assertion of the carrier, hypothesised by HE7.A and unchanged by this repair.

by

> at every root of the class: at \(k>\lambda\) the value does not move at all, at \(k<\lambda\) it falls, and at \(k\le T\) it leaves the window. Only \(k=\lambda\) escapes the display, so **(RISE) forces (HT)**: a recentering that raises the key's value on the class it refines has its increment at the side's own slope and at no other height, and the index of \(L_k\) is thereby bound to the side datum. The implication is this master's own. The premise is not: (RISE) is a carrier assertion on the footing r4 repair 3 gave `(SEC-RANK)` — it is part of the root-preserving continuation assertions hypothesised by HE7.A, this master does not derive it, and any instance that cannot supply it does not instantiate HE7.A. Three earlier supports for the rise are **withdrawn**, and are used nowhere: the "new valid development" of the sentence below the recentering display, which asserts that a development exists and is valid and not that any value rises; `(SEC-RANK)`, which is asserted at every product-\(1\) recentering irrespective of \(k\) and which r4 repair 3's own fence declares underived here; and the attribution of the rise to an assertion "hypothesised by HE7.A", which named no displayed assertion — (RISE) above is now the displayed assertion that carries it.
>
> **Honest status of (RISE).** Not derived by this master. Its instance status, recorded in the form r4 repair 3 used for `(SEC-RANK)`:
>
> - **Level one** (S3.1/S3.2): supplied inside the existing pin `HE3-A-PROOF`, whose §S6.3 stage-α step is the passage S1.8C quotes and whose configuration contains this master's product-\(1\) branch. It places the refined sub-block strictly above the refined-at slope at the recentered key — `LEMMA HE3-2(b) the recentered key Φ″ has a polygon whose portion above` (1151), `λ has length exactly m, the corresponding block of D′m roots is` (1152), read at `P(F″) STRICTLY ABOVE λ, which by the corrected LEMMA HE3-2(b) is the` (1156) — and it records the rise as the step's termination datum, `Termination: each refine strictly increases the floor λ and dv-heights` (1167), which is the line r4 repair 3 already mines from this span for level-one `(SEC-RANK)`. That sub-block is this master's refined class, as S1.8C says in the same breath: `the sub-block the passage carries to \(\Phi''\) is the root block this master's recentering "keeps".` A recentering at \(k\ne\lambda\) is excluded there by the display above rather than by fiat: it leaves every root of the class at \(d=\min(\lambda,k)\le\lambda\), so the class contributes nothing strictly above \(\lambda\), the sub-block does not travel, and the floor does not increase.
>
> - **Level two and deeper** (S3.3, and S3.4/S3.5): supplied inside the existing pin `HE7-PERT-TRANSPORT`, whose LEMMA HE7-13 — `> **LEMMA HE7-13 [r2] (the strict slope increase along the refine chain —` (918), `> DERIVED, not assumed).** Let Ψ̃ = Ψ − W with W = 0 or as in LEMMA` (919) — states the level-two α-refine step with its increment at the node's own slope, `> s₂ ≠ 0). Let w be a (LIFT₂) polynomial at height λ₂ with residue s₂` (924), and derives the rise as that lemma's conclusion: `> Then EVERY root ρ of f_S has` (926), `>     dv₂(Ψ̃^{(1)}(ρ)) > λ₂    (possibly = ∞) ,                     (S5.8.2)` (928). LEMMA HE7-8, inside the pin `HE7-REF-TERM`, describes the same chain with the same convention, `> Ψ^{(j+1)} = Ψ^{(j)} − w_j with dv₂(w_j) = λ₂^{(j)} and` (1090). What these lines supply is the level-two carrier's own refine step, hypothesis-side — which is what an instance record needs and all it needs. They are NOT a derivation that a step must be this one; r6 repair 1(c) withdrew that claim about this same pin, and it is not revived here.
>
> The height binding that S1.8B Step 1 consumes at level two therefore rests on (RISE) as a carrier assertion discharged by these pins, together with this master's (RISE) \(\Rightarrow\) (HT) implication, and on no derivation of necessity. (RISE) is a carrier hypothesis, not a ledger obligation: it fences no instance read, and the open named obligations remain `(LB1)` and `(MP1)`.

**What this costs the r6 counter.** r6's counter says "No theorem-statement change is made by this round … it adds no case and no conclusion". That sentence is r6's own record of r6 and is left standing as such, but it is superseded in substance here: in the r7 form, `(REF-HT)` adds the hypothesis clause (RISE) to the root-preserving continuation suite and narrows clause 3's product-\(1\) transition to the refine step at the side's own slope, with `(OCC)`'s demand sharpened to \(\lambda\in H_{\mathrm{lift}}(B)\) as r6 already flagged. A hypothesis is added; no case and no conclusion is added. That is a theorem-statement change of the kind S7 counts, and the r7 counter books it as one.

**Non-circularity.** The level-one discharge above uses S1.8C's configuration match, which after repair 4 below invokes no clause of `(REF-HT)`; `(REF-HT)` enters S1.8C only at reading directive 2, downstream of the match. The level-two discharge uses LEMMA HE7-13, which derives its rise from its own hypotheses at \(\widetilde\Psi\) and consumes nothing of this master.

**Verification remark (source).** On 2026-08-13, `grep -cFx` returned **1** for each source line quoted above, in the file and at the line shown. In `lean/notes/openmath/HE3_PROOF_2026-08-08.md`, lines 1151, 1152, 1156 and 1167, all strictly inside the `HE3-A-PROOF` span whose delimiters `### S6.3 PROOF OF THEOREM HE3.A` (1092) and `leaf's history, so THEOREM HE3.A is proved. ∎` (1205) each returned **1**. In `lean/notes/openmath/HE7_PROOF_2026-08-08.md`, lines 918, 919, 924, 926 and 928, all strictly inside the `HE7-PERT-TRANSPORT` span (812–951) whose delimiters r5 repair 1 declared and r6 repair 1 re-verified; and line 1090, strictly inside the `HE7-REF-TERM` span, whose delimiters `> **LEMMA HE7-8 ((REF-TERM) — α-refine chains are FINITE, characteristic-free).**` (1087) and `μ₂ ≥ 2 this makes disc f_S = 0. ∎` (1128) each returned **1**. Every consumption of this repair lies inside a span of `(PINS)`, as the standing S7 consumption check demands.

**Verification remark (landmarks).** Under `sed -n '1,3293p' T2_SIGMA_LADDER_MASTER_2026-08-12.md | grep -cF -- '<the quoted string>'` on 2026-08-13, each of the four superseded strings returned **1**: the lead-in phrase (line 2942), the boxed display line (2945), the opening claim (2949), and the case-reading line (2965). The S1.8C clause quoted inside the replacement, for the sub-block identification, likewise returned **1** (line 3049); it is left standing by repair 4 below.

---

## r7 repair 2 — m-1P6 (minor): `HE6-FAMILY` booked as a first-only pin, and the inventory taxonomy corrected

**The finding repaired.**

> The r6 inventory update moves `HE6-PROOF` from description-only to quoted-pair but does not move `HE6-FAMILY`, whose FIRST delimiter this same round quotes and grep-verifies. … By r5 repair 3's own taxonomy … `HE6-FAMILY` is now a fourth first-only pin … and should read 15 + 4 + 13.

Accepted; the recount is right, and the arithmetic is right in both forms. Two amendments to the one effective inventory sentence, at the two places its parts now live.

**(a)** In r5 repair 3's replacement text, replace

> Three further pins, `HE3-R8-2`, `HE3-R8-3` and `HE3-R8-4`, carry a quoted **first** delimiter only, their last delimiter being fixed by S0.2's boundary rule; for these, condition 2 is discharged in advance for the first delimiter alone and condition 3 remains the gate's work.

by

> Four further pins, `HE3-R8-2`, `HE3-R8-3`, `HE3-R8-4` and `HE6-FAMILY`, carry a quoted **first** delimiter only, their last delimiter being fixed by S0.2's boundary rule; for these, condition 2 is discharged in advance for the first delimiter alone and condition 3 remains the gate's work. `HE6-FAMILY`'s first delimiter is the one r6 repair 2 quotes and grep-verifies, `> **DEFINITION HE6-1 (THE ENLARGED TEST FAMILY).** Let κ = u/ℓ ∈ ℚ in lowest` (`HE6_PROOF_2026-08-08.md`:201).

**(b)** In r6 repair 2's replacement text for the same sentence, replace

> The other 14 pins are description-only at both ends. Totals: 15 pairs + 3 first-only + 14 description-only = 32.

by

> The other 13 pins are description-only at both ends. Totals: 15 pairs + 4 first-only + 13 description-only = 32.

The pin count itself is unchanged at 32, and 15 + 4 + 13 = 32.

**Verification remarks.** In `lean/notes/openmath/HE6_PROOF_2026-08-08.md`, on 2026-08-13, `grep -cFx` returned **1** for `> **DEFINITION HE6-1 (THE ENLARGED TEST FAMILY).** Let κ = u/ℓ ∈ ℚ in lowest` (line 201). Under `sed -n '1,3293p' … | grep -cF` on 2026-08-13, the r5 taxonomy sentence returned **1** (line 2756) and the r6 totals sentence returned **1** (line 3123).

---

## r7 repair 3 — m-2P6 (minor): the stale `(MP1′)` disjunct in r5 repair 2's closing paragraph

**The finding repaired.**

> A live sentence still treats `(MP1′)` as a condition a state may carry. r5 repair 2's closing paragraph (line 2728) is not in r6's propagation list, which is scoped as "replacing r5 repair 2's four amendments" … After the retirement no state carries `(MP1′)`, so the disjunct is empty and the sentence is stale.

Accepted. r6's blanket resolution clause covers the name's meaning, not the implication that a state may carry it. Replace, in that paragraph,

> so they inherit whichever of `(MP1)`, `(MP1′)` the state carries without further amendment

by

> so they inherit whatever level-one conditionality the state carries — after r6 repair 2 that is `(MP1)`, `(MP1′)` having been retired and carried by no state — without further amendment

**Verification remark (landmark).** `sed -n '1,3293p' … | grep -cF` returned **1** for the superseded phrase (line 2728).

---

## r7 repair 4 — m-3P6 (minor): the lean on LEMMA HE3-2(b) corrected and re-based on the quoted lines

**The finding repaired.**

> S1.8C names and leans on `LEMMA HE3-2(b)`, which lies inside no span of `(PINS)`, and mis-describes it. … (a) Location: LEMMA HE3-2 is HE3 §S5 … §S5 is inside none of them. … (b) Accuracy: HE3-2's hypotheses are "Keep κ > D′h, s ∈ K^×, w := −C …, Φ″ = Φ′ + w" — no integer-slope requirement; clause (b) has an explicit branch "if κ is not a slope of P(F), P(F″) is P(F) truncated at height κ" … So the recentered key exists at every κ > D′h.

Accepted on both counts. The sentence is rebuilt so that it asserts only the containment the discharge needs and consumes only lines already quoted from inside `HE3-A-PROOF`. Replace, in S1.8C's configuration paragraph,

> The configuration is this master's, exactly. "Refines at (λ, s)" with "a residual root of multiplicity m ≥ 2" is clause 3's repeated \(r'=Y-s\) with \(s\in K\); LEMMA HE3-2(b)'s recentered key exists only at an integer slope, which by `(REF-HT)` and \(e'=1\) is the product-\(1\) branch and no other

by

> The passage's configuration contains this master's, exactly at the branch that recenters. "Refines at (λ, s)" with "a residual root of multiplicity m ≥ 2" is clause 3's repeated \(r'=Y-s\) with \(s\in K\); the slope at which the read refines is an integer here because \(e'=1\) forces \(\lambda=u'/e'=u'\), which is S1.8's product-\(1\) branch and is settled there independently of `(REF-HT)`; and nothing further is asserted of LEMMA HE3-2, whose own unit is HE3 §S5 and lies inside no span of `(PINS)`, so that only the lines quoted above are consumed

The sentence's remaining clause — `the sub-block the passage carries to \(\Phi''\) is the root block this master's recentering "keeps".` — is unchanged. Two consequences are recorded. First, the "only at an integer slope" claim is **withdrawn**: it is false of LEMMA HE3-2, which requires only \(\kappa>D'h\) and \(s\in K^\times\) and carries its own branch for a \(\kappa\) that is not a slope. Second, the configuration match no longer invokes `(REF-HT)`, which is what makes repair 1's level-one discharge non-circular; `(REF-HT)` still governs reading directive 2, downstream of the match.

**Verification remark (landmark).** The superseded string returned **1** under `sed -n '1,3293p' … | grep -cF` on 2026-08-13 (line 3049), as did the remaining clause quoted above (same line). Both are quoted here rather than inlined into the command because they contain apostrophes.

---

## r7 repair 5 — m-4P6 (minor): S1.8C's four pins added to the three level-two Source-pin lines

**The finding repaired.**

> S1.8C's discharge is consumed by S3.3/S3.4/S3.5, whose Source-pin lines were not amended for it. … The four pins the discharge rests on — `HE3-A-PROOF`, `HE6-SLOT-SEAM`, `HE6-FAMILY`, `HE6-PROOF` — are on S3.1's and S3.2's lines only … Under r5 repair 6's own per-record discipline … the three level-two lines are now incomplete.

Accepted. The consumption is S1.8C's own closing sentence, "A state may be in both configurations at once, and then it carries S1.8B's level-two discharge over S1.8C's level-one frame.", so under r5 repair 6's per-record discipline the four pins belong on the level-two lines too; where a level-two chain sits over the ORIGINAL level-one key \(\Phi'\) they are simply unconsumed. Replace the three lines as r5 repair 6 set them —

> - **S3.3** — **Source pins:** `HE7-A-STMT`, `HE7-SLOT-TRANSFER`, `HE7-MIXED-13P`, `HE7-COCYCLE-2P-THROUGH-R1D`, `HE7-REF-TERM`, `HE7-PERT-TRANSPORT`, `HE6R1-1`, `HE6R1-2`, and `HE6R1-3`.

by

> - **S3.3** — **Source pins:** `HE7-A-STMT`, `HE7-SLOT-TRANSFER`, `HE7-MIXED-13P`, `HE7-COCYCLE-2P-THROUGH-R1D`, `HE7-REF-TERM`, `HE7-PERT-TRANSPORT`, `HE6R1-1`, `HE6R1-2`, `HE6R1-3`, and — for a chain whose level-one key is itself recentered, by S1.8C — `HE3-A-PROOF`, `HE6-SLOT-SEAM`, `HE6-FAMILY` and `HE6-PROOF`.

> - **S3.4** — **Source pins:** `HETOW-LABELS`, `HETOW-LABELS-1`, `HETOW-KEY-BRIDGE`, `HETOW-A`, `HETOW-NORMALIZER-4`, `HE7-REF-TERM`, `HE7-PERT-TRANSPORT`, `HE7-MIXED-13P`, and `HE6R1-3`.

by

> - **S3.4** — **Source pins:** `HETOW-LABELS`, `HETOW-LABELS-1`, `HETOW-KEY-BRIDGE`, `HETOW-A`, `HETOW-NORMALIZER-4`, `HE7-REF-TERM`, `HE7-PERT-TRANSPORT`, `HE7-MIXED-13P`, `HE6R1-3`, and — for a chain whose level-one key is itself recentered, by S1.8C — `HE3-A-PROOF`, `HE6-SLOT-SEAM`, `HE6-FAMILY` and `HE6-PROOF`.

> - **S3.5** — **Source pins:** `GENTOW-4-1`, `GENTOW-4-A`, `GENTOW-4-2`, `GENTOW-ACCEPTANCE-FOLD`, `HE7-REF-TERM`, `HE7-PERT-TRANSPORT`, `HE7-MIXED-13P`, `HE6R1-2`, and `HE6R1-3`.

by

> - **S3.5** — **Source pins:** `GENTOW-4-1`, `GENTOW-4-A`, `GENTOW-4-2`, `GENTOW-ACCEPTANCE-FOLD`, `HE7-REF-TERM`, `HE7-PERT-TRANSPORT`, `HE7-MIXED-13P`, `HE6R1-2`, `HE6R1-3`, and — for a chain whose level-one key is itself recentered, by S1.8C — `HE3-A-PROOF`, `HE6-SLOT-SEAM`, `HE6-FAMILY` and `HE6-PROOF`.

Justification, one for all three: S1.8C supplies the level-one frame over a recentered level-one key, and its closing sentence puts a level-two state over that frame. Before r6 the configuration was covered globally, by `(MP1′)` propagated to S4.1/S4.2/S5.17; the retirement removed the global cover without adding the per-record one. r6 repair 6 performed exactly this cure for the sibling seam (S1.8B at S3.4/S3.5); this completes it for S1.8C. No pin is added to `(PINS)` and the count stays 32.

**Verification remark (landmarks).** Each of the three superseded source-pin lines returned **1** under `sed -n '1,3293p' … | grep -cF` on 2026-08-13: S3.3 (line 2860), S3.4 (2861), S3.5 (2862). S1.8C's closing sentence quoted above returned **1** (line 3109).

---

## r7 repair 6 — m-5P6 (minor): (vii)'s engine sentence and the (i)–(vii) framing aligned with r1 repair 2's credit

**The finding repaired.**

> "the S3.1 record is exactly the claim that HE3.A's data instantiate this master's S1.2–S1.7" contradicts r1 rep2's installed "it is not an HE3-only discharge"; and the (i)–(vii) list is presented as what S1.2–S1.7 demand while omitting S1.3, S1.4, S1.6, and S1.7's proved test package.

Accepted on both halves. The list is a frame inventory, not an enumeration of what S1.2–S1.7 demand; and the record transported is the composite, not the HE3 leg alone.

**(a) The framing.** In S1.8C's "What has to be supplied" paragraph, replace

> For a state whose level-one key is \(\Phi''\), S1.2–S1.7 demand (i) the same \((T1)/(T2)\) point set \(\operatorname{Pt}\); (ii) the same \(dv\); (iii) the same \(\varpi\); (iv) the same \(K\); (v) the same \(T=D'h\); (vi) DEFINITION HE6-1's test family over \(\Phi''\); and (vii) a \(\Phi''\)-development with its lower hull and its label read — so that a state built over \(\Phi''\) instantiates HE7.A at all, at level one or above.

by

> For a state whose level-one key is \(\Phi''\), the level-one FRAME that S1.2–S1.7 are read over consists of (i) the same \((T1)/(T2)\) point set \(\operatorname{Pt}\); (ii) the same \(dv\); (iii) the same \(\varpi\); (iv) the same \(K\); (v) the same \(T=D'h\); (vi) DEFINITION HE6-1's test family over \(\Phi''\); and (vii) a \(\Phi''\)-development with its lower hull and its label read. That is the frame, and not an enumeration of everything S1.2–S1.7 demand: S1.3's normalizers and cocycle law, S1.4's full-height lift data, S1.5's `(WINDOW)` and `(RES-DEG)`, S1.6's `(FRAME)` and `(ORIGIN)`, and S1.7's seven proved test properties with `(ACCOUNT)` are demands on the RECORDS, and they reach \(\Phi''\) only as (vii) transports the records themselves.

**(b) The engine sentence.** Replace

> Since the S3.1 record is exactly the claim that HE3.A's data instantiate this master's S1.2–S1.7, the passage transports that record to \(\Phi''\).

by

> What (vii) transports is the S3.1/S3.2 records, with the credit r1 repair 2 assigned them. The HE3 pins there supply "the base carrier, exact slots, legal full-height lifts, full development, hull/window/cap data, and label equivariance", and the same paragraph adds: "They are not credited with the master’s universal test package or with `(ACCOUNT)`." So what this passage carries to \(\Phi''\) is the HE3 leg — every hypothesis of THEOREM HE3.A, at the new key — while the universal test package and `(ACCOUNT)`, which are those records' HE6 leg, reach \(\Phi''\) through (vi) and through the HE6 paragraph below. The record transported is the composite HE3+HE6 discharge r1 repair 2 installed, and no more of it is claimed at \(\Phi''\) than is claimed at \(\Phi'\).

**Verification remark (landmarks).** Under `sed -n '1,3293p' … | grep -cF` on 2026-08-13: the "What has to be supplied" sentence returned **1** (line 3035), the engine sentence returned **1** (line 3087), and r1 repair 2's credit sentence quoted inside the replacement returned **1** (line 1444).

---

## r7 counter

r7 folds repairs for the single GAP (G-1P6) and all five minors (m-1P6 … m-5P6) of the r6 hostile pass of record. Its substantive content is one object: `(REF-HT)` is now two clauses — (RISE), that a product-\(1\) recentering raises the key's value on the class it refines, and (HT), that its increment sits at the side's own slope. (HT) is DERIVED from (RISE) by the ultrametric display the pass certified. (RISE) is STIPULATED, as a carrier assertion on r4 repair 3's `(SEC-RANK)` footing, with its discharge recorded per instance: at level one inside `HE3-A-PROOF` (the sub-block read strictly above \(\lambda\) at the recentered key, plus the stage-α termination clause "Termination: each refine strictly increases the floor λ"), and at level two and deeper inside `HE7-PERT-TRANSPORT` (LEMMA HE7-13's α-refine step, whose increment is at the node's slope and whose rise is that lemma's derived conclusion), with LEMMA HE7-8's chain convention inside `HE7-REF-TERM` recording the same. Three supports for the rise are withdrawn: the "new valid development" sentence, `(SEC-RANK)`, and the undisplayed attribution "hypothesised by HE7.A". The binding S1.8B Step 1 and r6 repair 6's scope clause consume is unchanged.

**This round makes a theorem-statement change**, and one only: (RISE) joins the root-preserving continuation assertions hypothesised by HE7.A, and clause 3's product-\(1\) transition is thereby narrowed to the refine step at the side's own slope, with `(OCC)` read at \(\lambda\in H_{\mathrm{lift}}(B)\). A hypothesis is added; no case and no conclusion is added. r6's counter recorded "No theorem-statement change is made by this round"; that sentence is r6's own record of r6, left standing as such and superseded in substance by this paragraph.

The five minors are bookkeeping and citation hygiene: `HE6-FAMILY` becomes the fourth first-only pin, so the inventory reads **15 pairs + 4 first-only + 13 description-only = 32**; the stale `(MP1′)` disjunct in r5 repair 2's closing paragraph is removed; the lean on LEMMA HE3-2(b) is corrected — the "only at an integer slope" claim withdrawn as false of that lemma, and the configuration match re-based on lines already quoted from inside `HE3-A-PROOF`, which is also what makes repair 1's level-one discharge non-circular; S1.8C's four pins are added to the S3.3/S3.4/S3.5 Source-pin lines; and S1.8C's (i)–(vii) framing and its engine sentence are aligned with r1 repair 2's composite HE3+HE6 credit.

**Two named obligations remain open**, both at level one: `(LB1)` for clause-4 block construction, and `(MP1)` for the clause-5 peel at a recentered key. (RISE) is a carrier hypothesis, not a ledger obligation: it fences no instance read, and both instance families discharge it from pins already on their lines. No pin is added or removed and no source file is edited, so the expected pin count stays 32, the expected synthetic-marker count stays zero, and the expected source edit count stays zero.

**Landmark census for this round.** Sixteen master-internal landmark strings, on fifteen lines, each returning **1** under `sed -n '1,3293p' … | grep -cF` on 2026-08-13: lines 1444, 2728, 2756, 2860, 2861, 2862, 2942, 2945, 2949, 2965, 3035, 3049 (two strings — the superseded configuration clause and the sub-block clause left standing), 3087, 3109 and 3123. Eleven source lines, each returning **1** under `grep -cFx`: `HE3_PROOF_2026-08-08.md` 1151, 1152, 1156, 1167; `HE6_PROOF_2026-08-08.md` 201; `HE7_PROOF_2026-08-08.md` 918, 919, 924, 926, 928, 1090. Six span delimiters re-verified at **1**: HE3 1092 and 1205; HE7 812 and 951; HE7 1087 and 1128.

Gap-or-worse repairs reset the clean count (S7: "A gap-or-worse repair resets the clean count"). **The clean-pass counter is RESET to 0 of 2.** The acceptance gate still owes **TWO consecutive clean hostile passes** over the r7 effective text before this note may leave attempt grade \(0/2\); the status line therefore stays "mathematical composition draft, attempt grade \(0/2\)", and by `(GRADE)` every composed instance stays \(0/2\) regardless of supplier grade.

---

## r8 (2026-08-13): the level-one (RISE) discharge made joint at one step, and S1.8C's `(REF-HT)` entry points brought into agreement

*(Opus/Claude repair arm, against the r7 hostile pass of record `runs/comp13/T2P7_output.log` — 0 CRITICAL + 1 GAP + 2 minor, plus 2 recorded nits; counter resets.)*

**Verification protocol for this round.** Every source line quoted below was checked on 2026-08-13 by exact-full-line search (`grep -cFx`) in the named accepted source file, with the count and the source line number recorded at the point of use. No source file is edited by this round; the expected source edit count remains zero, and no pin is added or removed, so the expected pin count remains 32. No Source-pin line is amended either: the three pins this round cites — `HE3-A-PROOF`, `HE6-FAMILY`, `HE6-PROOF` — already stand on both level-one records' lines (S3.1, line 2858; S3.2, line 2859) and, since r7 repair 5, on the three level-two lines as well. Landmarks internal to this master are quoted from the **r7 effective text**, and their uniqueness is recorded in the form `sed -n '1,3509p' T2_SIGMA_LADDER_MASTER_2026-08-12.md | grep -cF -- '<string>'` → **1**; the line bound 3509 is the last line of the r7 round and excludes this round's own re-quotations, which would otherwise inflate every count.

**What the GAP is, and what it is not.** The pass certified the whole of r7's architecture except its order of assembly at one instance. It certified that (RISE) \(\Rightarrow\) (HT) is the exact contrapositive of the min-rule display and is sound one way; that HE3's stage-α lines 1151/1152/1156 give (RISE) at level one and LEMMA HE7-13's 926/928 derive it at level two; that all four r7 withdrawals are orphan-free; that the statement change is hypothesis-only with all five instances pin-covered; and the whole of the strict assembly. What it refuted is the level-one discharge's assembly order. The master's product-\(1\) new key is \(\Phi_{\mathrm{new}}=\Phi-L_k(s)\) at an index \(k\) the display leaves free (S1.8, line 578, unamended by any round), while the passage's conclusion is about HE3's \(\Phi''\); r7's discharge read the second as the first without ever exhibiting the step that both are about, so the only visible route from the passage to the master's (RISE) ran through (HT) — the clause r7 derives from (RISE). Repair 1 rebuilds the discharge in the only order that is not a circle: the instance's step is exhibited FIRST, as a recentering of this master's form at an index its own construction fixes and this master does not choose; (RISE) is then the passage's conclusion about that step, read with no height in the reading; and (HT) at that step follows, on two independent grounds neither of which is the theorem's (HT) clause. Nothing downstream changes in content: the two clauses, their honest status, and everything S1.8B Step 1 and r6 repair 6's scope clause consume are as r7 left them.

---

## r8 repair 1 — G-1P7 (GAP): the level-one discharge exhibits its step first and supplies both clauses of `(REF-HT)` at it, and S1.8C's entry-point claim is corrected

**The finding repaired.**

> the level-one (RISE) discharge supplies no non-circular route from the master's unbound lift height k to the passage's refine slope λ, and r7's own non-circularity paragraph is false of the effective text at four installed sites. … For the passage's conclusion (the D′m-root sub-block sits strictly above λ in P(F″)) to BE the master's (RISE) for Φ_new, one needs k = λ. That is exactly (HT), which r7 derives from (RISE). … "(REF-HT) enters S1.8C only at reading directive 2" is false at four installed sites of S1.8C, three of which are upstream of the match … and, decisively, the honest-status sentence of the same subsection — installed text, NOT superseded by r7 — which credits the configuration match itself to (REF-HT).

**Accepted on both halves.** The substantive half is accepted as stated: r7's bullet asserts the passage's conclusion IS this master's (RISE) without ever exhibiting the object both statements are about, and with the height identification left to (HT). The textual half is accepted as stated: the entry-point claim is false at 3033, 3081, 3085 and 3098, and 3098 is an orphaned dependent of r7 repair 4's withdrawal. One correction to the report, recorded because the repair turns on it: the report's one-sentence cure ("HE3's stage-α recenters at its own λ by construction") is **not** available as a quoted formula. The pinned span states the node's refine datum and names the key formed there; the increment's height is displayed only by LEMMA HE3-2, whose unit is HE3 §S5 and which r7 repair 4 fenced out of every consumption. What IS available inside the pins is stronger in one respect and weaker in another, and the repair installs both legs with their status marked.

**(a) The level-one discharge, restated so that the step comes first.** In the honest-status list installed by r7 repair 1(c), replace

> **Level one** (S3.1/S3.2): supplied inside the existing pin `HE3-A-PROOF`, whose §S6.3 stage-α step is the passage S1.8C quotes and whose configuration contains this master's product-\(1\) branch.

by

> **Level one** (S3.1/S3.2): supplied at the instance's own refine step, inside the existing pins `HE3-A-PROOF` and — for S3.2's enlarged classes — `HE6-FAMILY` and `HE6-PROOF`. Both clauses are properties of that one step, and the step is exhibited before either clause is read. `HE3-A-PROOF`'s §S6.3 stage-α step is the passage S1.8C quotes, and its configuration contains this master's product-\(1\) branch. That step is a recentering of this master's own form at an index its construction fixes and this master does not choose: at \(\ell=1\) DEFINITION HE6-1's family IS the family of these recenterings — `> monic of degree D″ := D′ℓd (each B_tΦ′^{ℓt} has degree < D′ℓd). For ℓ = 1` (`HE6_PROOF_2026-08-08.md`:209), `> this is HE3's recentered-key family enlarged in DEGREE; for ℓ ≥ 2 it is a` (210) — and that family's recipe puts the increment of the member indexed by \((\kappa,r)\) at the index's own height: `> **DEFINITION HE6-1 (THE ENLARGED TEST FAMILY).** Let κ = u/ℓ ∈ ℚ in lowest` (201), `> terms with κ > D′h, and let r = Z^{d} + Σ_{t<d}c_tZ^t ∈ K[Z] be monic` (202), `> deg B_t < D′, dv(B_t) = (d−t)u and res(B_t(θ)/ϖ(θ)^{(d−t)u}) = c_t (and` (204). At \((\ell,d)=(1,1)\) and \(r=Z-s\) that reads \(\Psi_{\kappa,Z-s}=\Phi'+B_0\) with \(u=\ell\kappa=\kappa\), \(\deg B_0<D'\), \(d(B_0)=\kappa\) and residue \(c_0=-s\): this master's \(\Phi-L_\kappa(s)\), at the family's own index \(\kappa\), with the recipe's standing \(\kappa>D'h=T\) placing it inside `(WINDOW)` before any clause of `(REF-HT)` is read. **No height is asserted of \(\kappa\) here, and none is needed to read the clause that follows.** (RISE) at that step is the passage's own conclusion, stated of \(\Phi''\) with no height in the reading.

**(b) The alternative-height sentence, restated as the two height legs it has to be.** In the same bullet, replace

> A recentering at \(k\ne\lambda\) is excluded there by the display above rather than by fiat: it leaves every root of the class at \(d=\min(\lambda,k)\le\lambda\), so the class contributes nothing strictly above \(\lambda\), the sub-block does not travel, and the floor does not increase.

by

> **(HT) at that same step**, on two grounds, neither of them the theorem's own (HT) clause. FIRST, reading no index at all. The display above is a statement about every \(k\) alike, and its inputs hold of this step: \(\deg B_0<D'=D\) and the class's roots lie in \(\operatorname{Pt}\) (S1.5), so `(SLOT-V)` and `(LIFT)` give \(d(B_0(\rho))=\kappa\) at them, while \(d(\Phi(\rho))=\lambda\) on the class by `(SIDE-COUNT)` as S1.8 derives it. At any index \(\kappa\ne\lambda\) the display leaves every root of the class at \(d=\min(\lambda,\kappa)\le\lambda\), so the class contributes nothing strictly above \(\lambda\), the sub-block does not travel, and the floor does not increase — which is not what the passage states of \(\Phi''\). Hence \(\kappa=\lambda\), and the step is \(\Phi-L_\lambda(s)\). This is this master's (RISE) \(\Rightarrow\) (HT) implication run AT the instance, on an instance-supplied premise whose reading used no height; it is not the theorem's (HT) clause imported to license that reading, and the direction of use is the safe one — the master's generality in \(k\) is INSTANTIATED here, not transferred. SECOND, and independently of the display: the passage forms its key at its own refine datum — `*Stage-α step.* If the read refines at (λ, s) (a residual root of` (`HE3_PROOF_2026-08-08.md`:1149) and then `LEMMA HE3-2(b) the recentered key Φ″ has a polygon whose portion above` (1151) — so the member of DEFINITION HE6-1's family that the read uses at that node is the one indexed by \((\lambda,Z-s)\), whose increment sits at \(d=\lambda\) by the recipe above. This second ground is a **reading of the passage's index, not a quoted formula**: the pinned span states the node's datum and names the key formed there, and does not display the increment's height, that display belonging to LEMMA HE3-2, which r7 repair 4 fenced out of every consumption and which nothing here revives. It is recorded as corroboration; the first ground carries the leg. Both clauses are therefore properties of one and the same instance step, and neither is obtained from the other through the theorem's hypothesis suite: (RISE) is the passage's conclusion about \(\Phi''\), read with no height, and (HT) is a property of that step established at the instance.

**(c) S1.8C's honest-status sentence, the orphaned dependent.** In S1.8C, replace

> Derived master-side: the configuration match (through `(REF-HT)`), the key-freeness of (i)–(vi) read off the pinned displays, and the composition of the passage with the S3.1/S3.2 substitutions.

by

> Derived master-side: the configuration match — which invokes no clause of `(REF-HT)`, resting instead on S1.8's own case split \(e'\deg r'=1\) and on \(e'=1\Rightarrow\lambda=u'/e'=u'\in\mathbf Z\) in lowest terms, as r7 repair 4 rebuilt it — the key-freeness of (i)–(vi) read off the pinned displays, and the composition of the passage with the S3.1/S3.2 substitutions.

**(d) The non-circularity paragraph, made true of the effective text.** Replace r7 repair 1's

> **Non-circularity.** The level-one discharge above uses S1.8C's configuration match, which after repair 4 below invokes no clause of `(REF-HT)`; `(REF-HT)` enters S1.8C only at reading directive 2, downstream of the match.

by

> **Non-circularity, stated of the effective text.** The level-one discharge above establishes both clauses at the instance's own step and neither from the other: (RISE) is the passage's conclusion about \(\Phi''\), whose reading uses no height, and (HT) at that step follows at the instance from that conclusion through this master's own display, corroborated by the passage's index. S1.8C's configuration match invokes no clause of `(REF-HT)`, as r7 repair 4 rebuilt it and as the honest-status sentence now records. The claim that "`(REF-HT)` enters S1.8C only at reading directive 2" is **withdrawn** as false: three sites of S1.8C carry the \(\lambda\)-index upstream of the match — the subsection's setup sentence (r6 effective text line 3033), the degree bookkeeping at (vi) (3081), and the family-member identification (3085). What is true, and is all the discharge needs, is that no claim made at those three sites depends on the index being \(\lambda\): 3081's is \(\deg L_k(s)<D'\), which S1.4 gives at every \(k\); 3085's is that a recentered level-one key is the \((\ell,d)=(1,1)\) member of DEFINITION HE6-1's family at the index it carries, which is that family's recipe at every index; and 3033's is the setup, naming the configuration under discharge. The \(\lambda\) written at those sites is the name of the step's own height, fixed at the instance by the discharge above and by no clause of `(REF-HT)`. Reading directive 2 no longer cites `(REF-HT)` either (repair 4(b) below), so after this round no clause of `(REF-HT)` is a premise anywhere in S1.8C.

**Verification remark (source).** On 2026-08-13, `grep -cFx` returned **1** for each source line quoted in this repair, in the file and at the line shown. In `lean/notes/openmath/HE6_PROOF_2026-08-08.md`, lines 202, 204, 209 and 210, all strictly inside the `HE6-FAMILY` unit whose quoted first delimiter is line 201 (itself returning **1**) and whose last line is fixed by S0.2's boundary rule at 213, immediately before the next `>`-unit LEMMA HE6-0″ (215). In `lean/notes/openmath/HE3_PROOF_2026-08-08.md`, lines 1149 and 1151, both strictly inside the `HE3-A-PROOF` span whose delimiters `### S6.3 PROOF OF THEOREM HE3.A` (1092) and `leaf's history, so THEOREM HE3.A is proved. ∎` (1205) each returned **1**; line 1149 is already inside r6 repair 2's verified list for this span, and 1151 is already quoted by r7 repair 1. Every consumption of this repair lies inside a span of `(PINS)`, as the standing S7 consumption check demands, and nothing of LEMMA HE3-2's own statement is consumed.

**Verification remark (landmarks).** Under `sed -n '1,3509p' T2_SIGMA_LADDER_MASTER_2026-08-12.md | grep -cF -- '<the quoted string>'` on 2026-08-13, each of the four superseded strings returned **1**: the level-one discharge's opening sentence (line 3353), the alternative-height sentence (3353, the same line's later sentence), S1.8C's honest-status clause (3098) and r7's non-circularity sentence (3361).

---

## r8 repair 2 — m-1P7 (minor): the three surviving "derived from three S1 data" sentences booked, with the elided clause inside the sentence r7 already booked

**The finding repaired.**

> r6's counter and r6 repair 1's lead prose still describe the height binding as derived from three S1 data alone; r7 booked only the adjacent sentence of the same counter paragraph. … Booking one clause of a paragraph and leaving its three siblings — one of them inside the booked sentence — is inconsistent supersession bookkeeping.

Accepted. Four live sentences, all r6 round prose, make the same now-incomplete claim; r7 booked one of them. They are booked here together and on one uniform footing — each is r6's own record of r6, is left standing as such, and is superseded in substance by the (RISE)+(HT) architecture:

> Repair 1 binds the height from the master's own `(SIDE-COUNT)`, `(SLOT-V)` and `(LIFT)`, as `(REF-HT)`.

(line 2922, r6's lead-in);

> The binding is derivable at the master's own generality from three data already displayed in S1: `(SIDE-COUNT)`, `(SLOT-V)`, and `(LIFT)`.

(2934, r6 repair 1);

> the refinement height of the product-\(1\) recentering is bound to the side's own slope, derived from `(SIDE-COUNT)`, `(SLOT-V)` and `(LIFT)` rather than named

(3287, r6's counter); and, inside the very sentence r7 elides with "…" at 3359,

> `(REF-HT)` binds a parameter that clause 3 and S1.8 already quantified over without naming a value

(3289, the same counter).

**What the correction is, once for all four.** The three S1 data derive the min-rule DISPLAY — \(d(\Phi(\rho))=\lambda\) on the class by `(SIDE-COUNT)`, \(d(L_k(s)(\rho))=k\) by `(SLOT-V)` + `(LIFT)`, hence \(d(\Phi_{\mathrm{new}}(\rho))=\min(\lambda,k)\le\lambda\) at \(k\ne\lambda\) — and that display is an IMPLICATION, converting (RISE) into (HT). It binds nothing on its own, because it is silent on whether any value rises: the three data are as true at \(k\ne\lambda\), where the class does not rise, as at \(k=\lambda\). The binding needs a fourth datum, the stipulated (RISE), which r7 displays and discharges per instance. The last of the four sentences is superseded on a second count as well: in the r7 form `(REF-HT)` does not only bind a parameter already quantified over — it adds the hypothesis clause (RISE) to the root-preserving continuation suite, which is exactly why r7's counter books a theorem-statement change and r6's counter, correctly for r6, did not.

**Verification remark (landmarks).** Under `sed -n '1,3509p' … | grep -cF` on 2026-08-13, each of the four sentences returned **1**, at lines 2922, 2934, 3287 and 3289 respectively.

---

## r8 repair 3 — m-2P7 (minor): the HE6 leg invoked inside the level-one discharge, with its caveat addressed

**The finding repaired.**

> the level-one (RISE) discharge is scoped to "(S3.1/S3.2)" but cites only `HE3-A-PROOF`; the HE6 leg that licenses running HE3's stage-α with HE6's classes is not invoked. … The licence exists and `HE6-PROOF` is already on S3.2's Source-pin line (2859), so this is a citation completeness defect, not a missing pin; but by the note's own r6 standard the S3.2 half of the (RISE) discharge is uncited, and the licence carries a caveat the discharge does not address.

Accepted. Repair 1(a) above puts `HE6-FAMILY` and `HE6-PROOF` on the discharge's own citation line; the licence itself and its caveat are installed here, in the same bullet. Replace

> That sub-block is this master's refined class, as S1.8C says in the same breath:

by

> **The S3.2 half of the scope.** S3.1 is HE3 and S3.2 is HE6, whose family is enlarged beyond HE3's, so the stage-α reading above has to be licensed for HE6's classes before the discharge may be scoped to both. It is, in the closing paragraph of the pinned proof unit of THEOREM HE6.A: `**This is HE3's LEMMA HE3-4 in full generality**, so HE3's THEOREM HE3.A` (`HE6_PROOF_2026-08-08.md`:663), `assembly (§S6.3 there: base read + stage-α + stage-CS + embedded genres) may` (664), `be run with HE3-4 replaced by THEOREM HE6.A — with the one caveat of §S7 for` (665), `histories containing an ℓ ≥ 2 side with a repeated residual factor.` (666) — the same quoted pair S1.8C already leans on, naming **stage-α** explicitly. The caveat is not consumed by this discharge: an \(\ell\ge2\) side with a repeated residual factor is \(e'\deg r'\ge2\), the product-\(\ge2\) child jump of clause 3, whereas the step under discharge is the product-\(1\) refine step, \(e'\deg r'=1\); S1.8C records the same routing for the frame discharge, and S3.2's own text sends that configuration to the level-two construction. That sub-block is this master's refined class, as S1.8C says in the same breath:

**Verification remark (source).** On 2026-08-13, `grep -cFx` returned **1** for each of `HE6_PROOF_2026-08-08.md` lines 663, 664, 665 and 666, all inside the `HE6-PROOF` span 639–666 whose delimiters `### S6.2 PROOF OF THEOREM HE6.A` (639) and `histories containing an ℓ ≥ 2 side with a repeated residual factor.` (666) r6 repair 2 declared and each of which returned **1** again here.

**Verification remark (landmark).** The superseded sentence returned **1** under `sed -n '1,3509p' … | grep -cF` on 2026-08-13 (line 3353); it is quoted rather than inlined into the command because it contains an apostrophe.

---

## r8 repair 4 — the two recorded nits

**(a) n-1: the r7 lead-in lists (HT) among the stipulations.** The report:

> The r7 lead-in installed at 3321 … lists (HT) among the stipulations before the trailing clause demotes it. … Self-correcting within the sentence, but the two readings are not the same theorem.

Accepted; the sentence is the one place a reader meets `(REF-HT)` for the first time, so it must not misdescribe which clause is stipulated. In r7 repair 1(a)'s replacement text, replace

> The recentering at this branch is a REFINE step, and this master stipulates of a refine step both that it raise the key's value on the class it refines and that its increment sit at the side's own slope — the second a consequence of the first, derived below:

by

> The recentering at this branch is a REFINE step, and this master stipulates of a refine step ONE thing: that it raise the key's value on the class it refines. That its increment then sits at the side's own slope is not a second stipulation but a consequence of the first, derived below. Both are displayed, because both are consumed downstream:

**(b) n-2: reading directive 2 cites `(REF-HT)` for a proposition neither clause contains.** The report:

> Reading directive 2 (3105) cites `(REF-HT)` for a proposition neither of its two clauses contains … The support is the lowest-terms convention (λ = u'/e' integer ⟺ e' = 1) plus the "Two consequences" sentence at 2967, not (RISE) or (HT).

Accepted, and cured rather than retained: with repair 1(d) above the directive is the last `(REF-HT)` citation left in S1.8C, and it is a mis-citation. In S1.8C's reading directive 2, replace

> The passage's configuration is a repeated \(K\)-rational residual root at an integer slope; by `(REF-HT)` that is clause 3's product-\(1\) branch, the only transition of `(RANK)` that recenters a key.

by

> The passage's configuration is a repeated \(K\)-rational residual root at an integer slope; that is clause 3's product-\(1\) branch by S1.8's own case split, since a \(K\)-rational residual root has \(\deg r'=1\) and an integer \(\lambda=u'/e'\) in lowest terms forces \(e'=1\), so \(e'\deg r'=1\) — the only transition of `(RANK)` that recenters a key. Neither clause of `(REF-HT)` is used here: (RISE) and (HT) are about the step this branch performs, not about which branch is taken.

**Consequential booking.** r7 repair 4's closing clause

> `(REF-HT)` still governs reading directive 2, downstream of the match.

is superseded on that clause alone: after (b) above, `(REF-HT)` governs neither the match nor the directive, and the rest of r7 repair 4's paragraph — the withdrawal of the "only at an integer slope" claim and the re-based configuration sentence — stands unchanged.

**Verification remark (landmarks).** Under `sed -n '1,3509p' … | grep -cF` on 2026-08-13, each of the three superseded strings returned **1**: the r7 lead-in (line 3321), reading directive 2's proposition (3105) and r7 repair 4's closing clause (3431).

---

## r8 counter

r8 folds repairs for the single GAP (G-1P7), both minors (m-1P7, m-2P7) and both recorded nits of the r7 hostile pass of record. Its substantive content is one object, and it is an assembly order rather than a new claim: the level-one discharge of (RISE) now exhibits the instance's refine step BEFORE reading either clause off it. The step is a recentering of this master's form at an index its own construction fixes — DEFINITION HE6-1's family at \(\ell=1\) IS the family of HE3's recenterings, and its recipe puts the \((\ell,d)=(1,1)\) member's increment at the member's own index, above \(D'h=T\) — so (RISE) is the passage's conclusion about that step, read with no height, and (HT) at that step follows at the instance from (RISE) through this master's own display, corroborated by the passage's own refine index. Neither clause is obtained from the other through the theorem's hypothesis suite, and the master's generality in \(k\) is instantiated at the instance rather than transferred to it. Two textual consequences: S1.8C's honest-status sentence no longer credits the configuration match to `(REF-HT)`, and the false claim that `(REF-HT)` "enters S1.8C only at reading directive 2" is withdrawn and replaced by a true one — three upstream sites carry the \(\lambda\)-index, every claim made at them holds at every index, and after repair 4(b) no clause of `(REF-HT)` is a premise anywhere in S1.8C.

**No theorem-statement change is made by this round**, in the exact sense S7 counts: no display is amended, no hypothesis is added to or removed from HE7.A's suite, no case is added or dropped, and no conclusion is touched. (RISE) and (HT) read exactly as r7 set them; (RISE) remains STIPULATED, on r4 repair 3's `(SEC-RANK)` footing, and (HT) remains DERIVED from it by the min-rule display. r7's own statement change — (RISE) joining the root-preserving continuation assertions — stands as r7 booked it. What this round changes is the discharge of (RISE) at level one, one citation in a reading directive, and four items of supersession bookkeeping.

The minors and nits: the level-one discharge is now cited for both halves of its "(S3.1/S3.2)" scope, `HE6-PROOF`'s closing paragraph supplying the licence to run HE3's stage-α with HE6's classes and its \(\ell\ge2\)-with-repeated-residual caveat being routed to the product-\(\ge2\) branch that this step is not; the four r6 sentences describing the binding as derived from `(SIDE-COUNT)`, `(SLOT-V)` and `(LIFT)` alone are booked together, with the correction stated once — those three data derive the implication, not the binding, which needs (RISE) as a fourth datum; the `(REF-HT)` lead-in no longer lists (HT) among the stipulations; and reading directive 2 is re-cited to S1.8's own case split and the lowest-terms integrality that actually support it.

**Two named obligations remain open**, both at level one: `(LB1)` for clause-4 block construction, and `(MP1)` for the clause-5 peel at a recentered key. (RISE) is a carrier hypothesis, not a ledger obligation: it fences no instance read, and both instance families discharge it from pins already on their lines. No pin is added or removed, no Source-pin line is amended, and no source file is edited, so the expected pin count stays 32, the expected synthetic-marker count stays zero, and the expected source edit count stays zero.

**Landmark census for this round.** Twelve master-internal landmark strings, on eleven lines, each returning **1** under `sed -n '1,3509p' T2_SIGMA_LADDER_MASTER_2026-08-12.md | grep -cF -- '<string>'` on 2026-08-13: lines 2922, 2934, 3098, 3105, 3287, 3289, 3321, 3353 (three strings — the discharge's opening sentence, the sub-block sentence, and the alternative-height sentence), 3361 and 3431. Nine source lines, each returning **1** under `grep -cFx`: `HE3_PROOF_2026-08-08.md` 1149 and 1151; `HE6_PROOF_2026-08-08.md` 201, 202, 204, 209, 210, and 663–666 counted as four. Four span delimiters re-verified at **1**: HE3 1092 and 1205; HE6 639 and 666; plus `HE6-FAMILY`'s quoted first delimiter, HE6 201, whose unit ends at 213 by S0.2's boundary rule.

Gap-or-worse repairs reset the clean count (S7: "A gap-or-worse repair resets the clean count"). **The clean-pass counter is RESET to 0 of 2.** The acceptance gate still owes **TWO consecutive clean hostile passes** over the r8 effective text before this note may leave attempt grade \(0/2\); the status line therefore stays "mathematical composition draft, attempt grade \(0/2\)", and by `(GRADE)` every composed instance stays \(0/2\) regardless of supplier grade.

---

## r9 (2026-08-13): the level-one identification re-derived in the coherent frame — the print twist displayed, the HE6 family reindexed, and the step's digit forced by (RISE)

*(Opus/Claude repair arm, against the r8 hostile pass of record `runs/comp13/T2SOL_output.log` — this note's FIRST model-diverse pass (gpt-5.6-sol high) on the current architecture, returning 0 CRITICAL + 1 GAP + 1 minor; counter resets.)*

**Verification protocol for this round.** Every source line quoted below was checked on 2026-08-13 by exact-full-line search (`grep -cFx`) in the named accepted source file, with the count and the source line number recorded at the point of use. No source file is edited by this round; the expected source edit count remains zero, and no pin is added or removed, so the expected pin count remains 32. No Source-pin line is amended: the three pins this round consumes — `HE3-A-PROOF`, `HE6-FAMILY`, and `HE6-SLOT-SEAM` (the pin r4 repair 1 adjudicated as the supplier of `(SLOT-V)` and `(HE6-SEAM)`) — already stand on both level-one records' lines (S3.1, line 2858; S3.2, line 2859) and, since r7 repair 5, on the three level-two lines as well. Landmarks internal to this master are quoted from the **r8 effective text**, and their uniqueness is recorded in the form `sed -n '1,3667p' T2_SIGMA_LADDER_MASTER_2026-08-12.md | grep -cF -- '<string>'` → **1**; the bound 3667 is the last line of the r8 round and excludes this round's own re-quotations, which would otherwise inflate every count.

**What the GAP is, and what it is not.** The pass certified the master core end to end and said so clause by clause: "`(ACCOUNT)` correctly yields clause 1 and `(SIDE-COUNT)`"; "`(RES-DEG)` plus the defect-free fundamental identity gives the termwise orbit count and exact \((e,f)\)"; "`(SIDE-PROD)`, `(LABEL-PROD)`, `(MID-PEEL)`, terminal reads, child jumps, and linear refinements form a complete recursive analysis under the stated block/continuation hypotheses"; "The clause-5 trigger analysis covers both key-changing transitions, while transition 6 returns key-free residual blocks by definition"; "`(RANK)=(\deg F,\mu,\sigma_{\mathcal C})` decreases correctly in every transition, with `(SEC-RANK)` honestly explicit"; "`(LB1)` and `(MP1)` remain fenced; I found no fence leakage"; and "S1.8B's level-two transport and composed-key \(W+w\) routing are coherent. The HE6-PROOF \(\ell\ge2\) caveat is correctly routed to the product-\(\ge2\) child branch." No sentence of that list is touched by this round. What the pass refuted is one identification inside the level-one INSTANCE discharge, and the refutation is exact: r8 read DEFINITION HE6-1's family index as if it were this master's digit, when the family indexes its members by a \(\varpi\)-PRINT residue and this master indexes its recenterings by the COHERENT digit — the two differing by exactly the twist `(Q-DEF)` exists to name. In the report's own words, "the abstract theorem remains true because `(RISE)` is an explicit carrier hypothesis; the instance discharge is the gap." Repair 1 displays the seam at the point of use; shows that the relabelling it forces is a BIJECTION, so the family still covers every recentering of this master, member for member; and then rebuilds the discharge so that it never reads the print label at all — the step's height AND its digit are both forced by the passage's own rise, read against the coherent label display that `HE3-A-PROOF` carries in its own text. What r8 asserted at the print index is thereby derived, in the frame in which it is true.

---

## r9 repair 1 — G-1SOL (GAP): the print/coherent seam displayed at the family identification, the family reindexed by the twist, and the level-one step identified in the coherent frame

**The finding repaired.**

> But the effective seam is \(\operatorname{res}(B_0/\varpi^{\kappa})=\iota(\gamma_\kappa(B_0))\eta^{-q(\kappa)}\). Thus the source choice \(\operatorname{res}(B_0/\varpi^\kappa)=-s\) implies \(\gamma_\kappa(B_0)=-s\,\eta^{q(\kappa)}\), not \(-s\), unless \(\eta^{q(\kappa)}=1\). No such hypothesis exists; indeed the note pins \(q\) precisely because the twist can be nontrivial. Equivalently, the print factor \(Z-s\) transports to a coherent linear factor with a rescaled root. Therefore the quoted HE6-family member is not shown to be the master's exact recentering \(\Phi-L_\kappa(s)\). This breaks r8's joint same-step identification used to discharge level-one `(RISE)` — especially S3.2 — and also affects S1.8C's claimed family-member identification.

**Accepted without reservation, and the scope is one site wider than the report names.** The conflation is r8's, it sits at the print/coherent seam, and the arithmetic is the report's: the family's defining residue is a \(\varpi\)-read and this master's digit is an \(n(\kappa)\)-read, so a family label \(-s\) is a coherent digit \(-s\eta^{q(\kappa)}\). THREE sentences of the effective text carry the conflated identification: r8 repair 1(a)'s step sentence, r8 repair 1(b)'s SECOND (corroboration) ground — which names the member "indexed by \((\lambda,Z-s)\)" — and S1.8C's family-member sentence. All three are replaced below. The report's own suggestion, that the identification might survive reindexed, is settled here in that direction and then made unnecessary: the relabelling is a bijection, so nothing is lost by it; and the rebuilt discharge does not consult the label at all.

**(a) The step sentence, with the seam displayed and the family reindexed.** In r8 repair 1(a)'s replacement text for the "Level one" bullet, replace

> At \((\ell,d)=(1,1)\) and \(r=Z-s\) that reads \(\Psi_{\kappa,Z-s}=\Phi'+B_0\) with \(u=\ell\kappa=\kappa\), \(\deg B_0<D'\), \(d(B_0)=\kappa\) and residue \(c_0=-s\): this master's \(\Phi-L_\kappa(s)\), at the family's own index \(\kappa\), with the recipe's standing \(\kappa>D'h=T\) placing it inside `(WINDOW)` before any clause of `(REF-HT)` is read. **No height is asserted of \(\kappa\) here, and none is needed to read the clause that follows.** (RISE) at that step is the passage's own conclusion, stated of \(\Phi''\) with no height in the reading.

by

> At \((\ell,d)=(1,1)\) and \(r=Z-\sigma\) that reads \(\Psi_{\kappa,Z-\sigma}=\Phi'+B_0\) with \(u=\ell\kappa=\kappa\), \(\deg B_0<D'\), \(d(B_0)=\kappa\) and residue \(c_0=-\sigma\) — a residue in the RECIPE'S OWN frame, which is the print frame: line 204, quoted above, fixes \(B_0\) by \(\operatorname{res}(B_0(\theta)/\varpi(\theta)^{\kappa})\), the \(\varpi\)-read, and not by the coherent \(n(\kappa)\)-read of `(SLOT-R)`. This master's `(HE6-SEAM)` is the conversion between the two, \(\operatorname{res}(A(\xi)/\varpi(\xi)^{k})=\iota_\xi(\gamma_k(A))\eta_\xi^{-q(k)}\), and at \(\xi=\theta\) — a \((T1)/(T2)\) point, being the point at which the recipe states its own condition and at which `(GAMMA)` is written — the embedding \(\iota_\theta\) is the identity inclusion of \(K=\mathbf F_Q(\eta)\): it is a \(k_0\)-embedding by `(RES-COMP)`, \(k_0=\mathbf F_Q\) by S1.1, and \(\eta_\theta\mapsto\eta_\theta\) by S3.1's \(\iota_\xi(\eta_\theta)=\eta_\xi\) read at \(\xi=\theta\), so it is the identity on \(K=k_0(\eta)\). Hence \(-\sigma=\gamma_\kappa(B_0)\eta^{-q(\kappa)}\), so \(\operatorname{dig}(B_0)=\gamma_\kappa(B_0)=-\sigma\eta^{q(\kappa)}\), and the family member's master form is
>
> \[
> \boxed{
> \Psi_{\kappa,Z-\sigma}
> =
> \Phi'-L_\kappa\bigl(\sigma\eta^{q(\kappa)}\bigr),
> \qquad\text{equivalently}\qquad
> \Phi'-L_\kappa(s)
> =
> \Psi_{\kappa,\,Z-s\eta^{-q(\kappa)}} .}
> \tag{IDX-TWIST}
> \]
>
> The print label and the coherent digit are the same element of \(K\) only when \(\eta^{q(\kappa)}=1\), and no hypothesis of this master or of its sources supplies that: `(Q-DEF)` posits \(q\) precisely because the twist can be nontrivial, and the minus sign of `(HE6-SEAM)` is declared mandatory at S1.2. **Nothing is lost by the mismatch, because the relabelling is a bijection.** \(\eta\in K^\times\) and \(q(\kappa)\in\mathbf Z\), so \(\eta^{q(\kappa)}\) is ONE fixed element of \(K^\times\), depending on \(\kappa\) alone and on neither the polynomial read nor the label — that is the universality of the RIDER's twist, the clause `HE6-LIFT-1L` is pinned for. Multiplication by it is a bijection of \(K\) fixing \(0\), and of \(K^\times\) onto itself. The family's labels at \((\ell,d)=(1,1)\) run over exactly \(K^\times\), because the recipe quantifies over EVERY monic irreducible \(r\in K[Z]\) with \(r(0)\ne0\) — `> irreducible with r(0) ≠ 0. Choose, by (LIFT), B_t ∈ O[x] with` (`HE6_PROOF_2026-08-08.md`:203), with line 202 quoted above — and \(r=Z-\sigma\) is such an \(r\) exactly for \(\sigma\in K^\times\); this master's digits at a full height run over all of \(K\) (S1.4, "every digit \(c\in K\) has an integral lift"), with \(L_\kappa(0)=0\) the empty recentering, which is no transition. So at each index \(\kappa\) the family IS the set of this master's nonempty recenterings at height \(\kappa\), member for member, under (IDX-TWIST) — enlarged in degree at \(d\ge2\) and in height at \(\ell\ge2\), which is what lines 209–210 say. What r8 asserted member-by-member at equal index NAMES is true after the relabelling and false before it.
>
> That is the sense, and the only sense, in which the step is a recentering of this master's own form at an index its construction fixes and this master does not choose: whichever member of the family the read forms, it is \(\Phi'-\Lambda\) with \(\Lambda:=-B_0\) integral, \(\deg\Lambda<D'=D\), \(h(\Lambda)=\kappa\) and \(\operatorname{dig}(\Lambda)\in K^\times\), and the recipe's standing \(\kappa>D'h=T\) places it inside `(WINDOW)` before any clause of `(REF-HT)` is read. **No height and no digit is asserted of that member here, and neither is needed to read the clause that follows.** (RISE) at that step is the passage's own conclusion, stated of \(\Phi''\) with no height and no index in the reading.

**(b) The height ground, extended to the digit — the reading that makes the print label unnecessary.** In r8 repair 1(b)'s replacement text, replace

> At any index \(\kappa\ne\lambda\) the display leaves every root of the class at \(d=\min(\lambda,\kappa)\le\lambda\), so the class contributes nothing strictly above \(\lambda\), the sub-block does not travel, and the floor does not increase — which is not what the passage states of \(\Phi''\). Hence \(\kappa=\lambda\), and the step is \(\Phi-L_\lambda(s)\). This is this master's (RISE) \(\Rightarrow\) (HT) implication run AT the instance, on an instance-supplied premise whose reading used no height; it is not the theorem's (HT) clause imported to license that reading, and the direction of use is the safe one — the master's generality in \(k\) is INSTANTIATED here, not transferred.

by

> At any index \(\kappa\ne\lambda\) the display leaves every root of the class at \(d=\min(\lambda,\kappa)\le\lambda\), so the class contributes nothing strictly above \(\lambda\), the sub-block does not travel, and the floor does not increase — which is not what the passage states of \(\Phi''\). Hence \(\kappa=\lambda\). At \(\kappa=\lambda\) the display is silent, the two values being equal; there the same reading continues one notch finer, at the residues, and fixes the step's DIGIT as well — without consulting the family's print label. The class being refined is the class of the label \((\lambda,Z-s)\), and `HE3-A-PROOF` states the level-one label read in the COHERENT frame, dividing by the same \(n(\lambda)\) that `(SLOT-R)` divides by: `note's frame, where the label of ρ is (λ, r) with r ∈ K[Z] read via the` (`HE3_PROOF_2026-08-08.md`:1114), `F_Q-embedding ι_ρ : K → k̄, η_θ ↦ η_ρ, and β_ρ := res(y_ρ/n(λ)(ρ)) at` (1115); the argument \(y_\rho\) is the key's own value, as the equivariance display inside the same span shows at \(g=\operatorname{id}\), `    β_{gρ} = res(Φ′(gρ)^{ℓ}/n(u)(gρ)) = ḡ(β_ρ)   (ℓ = 1: n(λ) read).` (1131, quoted with its four leading spaces), giving \(\beta_\rho=\operatorname{res}(\Phi(\rho)/n(\lambda)(\rho))\) at \(\ell=1\) with \(\Phi=\Phi'\) by `(HE3-INSTANCE)`; and the label condition itself is \(\iota_\rho(r)(\beta_\rho)=0\), `ι_{gρ}(r)(β_{gρ}) = ḡ(ι_ρ(r)(β_ρ)) = ḡ(0) = 0, and gρ carries the same` (1135) — that line's middle term \(\bar g(\iota_\rho(r)(\beta_\rho))=\bar g(0)\) is exactly the assertion \(\iota_\rho(r)(\beta_\rho)=0\) at a root carrying the label \((\lambda,r)\), which is how LEMMA HE3-6's statement inside this span uses the word "label". At \(r=Z-s\) that condition reads \(\beta_\rho=\iota_\rho(s)\), i.e.
>
> \[
> \operatorname{res}\!\left(\frac{\Phi(\rho)}{n(\lambda)(\rho)}\right)
> =
> \iota_\rho(s)
> \qquad\text{at every root }\rho\text{ of the class.}
> \]
>
> `(SLOT-R)` reads the increment in that same frame, \(\operatorname{res}(\Lambda(\rho)/n(\lambda)(\rho))=\iota_\rho(\operatorname{dig}(\Lambda))\), legitimately: \(\deg\Lambda<D\) and \(\rho\in\operatorname{Pt}\) (S1.5). Since \(d(n(\lambda)(\rho))=\lambda\) (S1.3), the quotient \((\Phi-\Lambda)(\rho)/n(\lambda)(\rho)\) has value \(d((\Phi-\Lambda)(\rho))-\lambda\ge0\) and its residue vanishes exactly when that value is positive, so subtracting the two reads gives
>
> \[
> \boxed{
> d\bigl((\Phi-\Lambda)(\rho)\bigr)>\lambda
> \iff
> \iota_\rho\bigl(s-\operatorname{dig}(\Lambda)\bigr)=0
> \iff
> \operatorname{dig}(\Lambda)=s ,}
> \]
>
> \(\iota_\rho\) being an injection of fields. The passage's rise therefore forces both readings at once: \(h(\Lambda)=\lambda\) and \(\operatorname{dig}(\Lambda)=s\), with \(s\) this master's own coherent residual root of `(RES-FACT)` — the digit at which S1.8 forms \(\Phi-L_\lambda(s)\) — while the family's print label at that same member is \(s\eta^{-q(\lambda)}\) by (IDX-TWIST) and plays no part in the derivation. Two riders complete it. FIRST, the derived digit is automatically in \(K^\times\): a zero increment cannot raise \(d(\Phi(\rho))=\lambda\), and S1.2 gives \(\operatorname{dig}(A)\in K^\times\) at every nonzero slot. SECOND, the lift freedom is immaterial. \(\Lambda\) is the increment the instance's construction actually formed; \(L_\lambda(s)\) is the carrier's designated lift at the same height and digit (S1.4). Their difference \(E=\Lambda-L_\lambda(s)\) has \(\deg E<D\) and, read at the fixed height \(\lambda\), digit \(s-s=0\) — `(GAMMA)`'s formula is additive in the coefficient array at a fixed height, and "Terms strictly above height \(k\) contribute zero", as the sentence below `(GAMMA)` records — so \(E\) cannot have \(h(E)=\lambda\), since S1.2 gives a nonzero slot a digit in \(K^\times\); hence \(E=0\) or \(h(E)>\lambda\), and then \(d(E(\rho))>\lambda\) by `(SLOT-V)`. From \((\Phi-L_\lambda(s))(\rho)=(\Phi-\Lambda)(\rho)+E(\rho)\), both clauses hold at this master's own displayed step and not merely at a companion of it. This is this master's (RISE) \(\Rightarrow\) (HT) implication run AT the instance, together with its residue-level refinement, on an instance-supplied premise whose reading used no height and no index; it is not the theorem's (HT) clause imported to license that reading, and the direction of use is the safe one — the master's generality in \(k\), and in the digit, is INSTANTIATED here, not transferred.

**(c) The corroboration ground, restated in the frame it holds in.** In the same replacement text, replace

> so the member of DEFINITION HE6-1's family that the read uses at that node is the one indexed by \((\lambda,Z-s)\), whose increment sits at \(d=\lambda\) by the recipe above.

by

> so the member of DEFINITION HE6-1's family that the read uses at that node is the one whose COHERENT digit is the node's own \(s\) — its print label being \(s\eta^{-q(\lambda)}\) and not \(s\), by (IDX-TWIST) — and its increment sits at \(d=\lambda\) by the recipe above.

**(d) S1.8C's family-member identification.** In S1.8C, replace

> At \((\ell,d)=(1,1)\) the member \(\Psi_{\lambda,Z-s}=\Phi'+B_0\) IS the recentered key, \(B_0\) being the \(\varpi\)-frame form of \(-L_\lambda(s)\) under `(HE6-SEAM)`.

by

> At \((\ell,d)=(1,1)\) the recentered key IS a member of the family, and the member it is, is \(\Psi_{\lambda,\,Z-s\eta^{-q(\lambda)}}=\Phi'+B_0\) with \(B_0=-L_\lambda(s)\): the family indexes its members by the PRINT residue of \(B_0\) (`HE6_PROOF_2026-08-08.md`:204, a \(\varpi\)-read), this master indexes its recenterings by the COHERENT digit of the increment (`(SLOT-R)`), and the two differ by the fixed unit \(\eta^{q(\lambda)}\in K^\times\) of `(HE6-SEAM)`, as (IDX-TWIST) in r9 repair 1 displays. The relabelling is a bijection of \(K^\times\), so the family covers every recentering of this master at that height, member for member; what it does not do is match them at equal index names.

**(e) The frame authority, and what is NOT cited.** The transport law consumed above is this master's own `(HE6-SEAM)`, whose supplier pin is `HE6-SLOT-SEAM` (LEMMA HE6-0″, adjudicated at r4 repair 1 for exactly the two clauses `(SLOT-V)` and the \(\varpi\)-read conversion, with the `[r2]` sign correction this master reproduces). No new pin and no new source is needed for it. The gauge-cocycle note T1 (`T1_GAUGE_COCYCLE_2026-08-12.md`, ACCEPTED 2/2 on 2026-08-13) books the same SHAPE of error at its own seam — its honesty ledger records that "raw print/canonical equality is iff \(z^\nu=1\), not iff \(\nu=0\)" — and that sentence is recorded here as methodological precedent ONLY: T1 is not among this master's six source files, no pin covers it, and nothing above consumes it. S0.2's no-unpinned-material clause is therefore respected in the strict sense it states.

**Non-circularity, restated for the rebuilt discharge.** The order of assembly is unchanged and the added leg does not disturb it. The step is exhibited first, as a family member in master form, with NO height and NO digit asserted of it — (a). (RISE) is then the passage's conclusion about that step, read with no height and no index — unchanged from r8. Both the height and the digit are then derived FROM that conclusion, through this master's own `(SLOT-V)`/`(SLOT-R)`/`(GAMMA)`/S1.3 displays and the coherent label read that `HE3-A-PROOF` carries — (b). Neither derivation is a clause of `(REF-HT)`, and no clause of `(REF-HT)` is a premise anywhere in S1.8C, as r8 repair 1(d) records and (d) above leaves standing. The description of site 3085 in that same paragraph — a recentered level-one key is the \((\ell,d)=(1,1)\) member of the family "at the index it carries" — remains true after (d), and is left standing rather than booked, because the index a member carries is exactly what (IDX-TWIST) computes.

**Verification remark (source).** On 2026-08-13, `grep -cFx` returned **1** for each source line quoted in this repair, in the file and at the line shown. In `lean/notes/openmath/HE3_PROOF_2026-08-08.md`, lines 1114, 1115, 1131 and 1135, all strictly inside the `HE3-A-PROOF` span whose delimiters `### S6.3 PROOF OF THEOREM HE3.A` (1092) and `leaf's history, so THEOREM HE3.A is proved. ∎` (1205) each returned **1** again here; lines 1114–1116 are the `[r1, F3]` bracket that fixes this note's label read, and 1131/1135 lie in the proof of LEMMA HE3-6, quoted inside that span. In `lean/notes/openmath/HE6_PROOF_2026-08-08.md`, line 203, strictly inside the `HE6-FAMILY` unit whose quoted first delimiter is line 201 and whose last line is 213 by S0.2's boundary rule. Lines 202, 204, 209 and 210, cited by number above, are quoted verbatim in the surviving part of the same bullet and were verified at r8. Every consumption of this repair lies inside a span of `(PINS)`, as the standing S7 consumption check demands; HE3's own definition \(y_\rho:=\Phi'(\rho)\) at HE3 §S2/§S4 is consistent with the reading of 1115 taken here but sits outside the span and is not consumed.

**Verification remark (landmarks).** Under `sed -n '1,3667p' T2_SIGMA_LADDER_MASTER_2026-08-12.md | grep -cF -- '<the quoted string>'` on 2026-08-13, each of the four superseded strings returned **1**: r8's step sentence (line 3537), r8's height-ground passage (3545), r8's corroboration clause (3545, the same line's later sentence) and S1.8C's family-member sentence (3085). All four are quoted rather than inlined into the command because they contain apostrophes.

---

## r9 repair 2 — m-1SOL (minor): r8's census arithmetic, in both of its counts

**The finding repaired.**

> r8 says "Nine source lines…" but lists two HE3 lines, five HE6-family lines, and HE6 lines 663–666 as four lines: \(2+5+4=11\), not nine. It also says "Twelve master-internal landmark strings, on eleven lines…" but the listed line numbers contain ten distinct lines; line 3353 carries three strings.

Accepted; both counts are wrong and both are re-counted here. The source list is HE3 1149 and 1151 (two), HE6 201, 202, 204, 209 and 210 (five), and HE6 663, 664, 665 and 666 (four): eleven. The landmark list is 2922, 2934, 3098, 3105, 3287, 3289, 3321, 3353, 3361 and 3431: ten distinct lines carrying twelve strings, three of them on 3353. In r8's landmark-census paragraph, replace

> Twelve master-internal landmark strings, on eleven lines

by

> Twelve master-internal landmark strings, on ten lines

and replace

> Nine source lines

by

> Eleven source lines

Neither count is load-bearing for any claim: both are bookkeeping over lists that are themselves correct and unchanged. **Verification remark (landmarks).** Under `sed -n '1,3667p' … | grep -cF` on 2026-08-13, each of the two superseded strings returned **1** (both on line 3665).

---

## r9 counter

r9 folds repairs for the single GAP (G-1SOL) and the single minor (m-1SOL) of this note's first model-diverse hostile pass, `runs/comp13/T2SOL_output.log` (gpt-5.6-sol high). The finding is credited to that pass in full: it caught a print/coherent frame conflation that five same-arm passes did not.

Its substantive content is one object. The HE6 family indexes its members by a \(\varpi\)-PRINT residue and this master indexes its recenterings by the COHERENT digit; the two differ by the fixed unit \(\eta^{q(\kappa)}\in K^\times\) that `(HE6-SEAM)` carries, so the member \(\Psi_{\kappa,Z-\sigma}\) is \(\Phi'-L_\kappa(\sigma\eta^{q(\kappa)})\) and not \(\Phi'-L_\kappa(\sigma)\) — (IDX-TWIST). Two consequences are installed. First, the relabelling loses nothing: multiplication by a fixed unit is a bijection of \(K^\times\), the family's labels at \((\ell,d)=(1,1)\) run over all of \(K^\times\) by the recipe's own quantifier over monic irreducible \(r\) with \(r(0)\ne0\), and this master's digits run over all of \(K\), so at each height the family IS the set of this master's nonempty recenterings, member for member, and only the index NAMES differ. Second, and this is what makes the discharge independent of the seam: the level-one discharge no longer identifies the member by its label at all. It exhibits the step as a master-form recentering with no height and no digit asserted; reads (RISE) off the passage; and then derives BOTH the height \(h(\Lambda)=\lambda\) and the digit \(\operatorname{dig}(\Lambda)=s\) from that rise — the height by the min-rule display r8 already ran, the digit by the same reading one notch finer, at the residues, using the coherent label read `HE3-A-PROOF` carries in its own text (\(\beta_\rho=\operatorname{res}(\Phi(\rho)/n(\lambda)(\rho))\), \(\iota_\rho(r)(\beta_\rho)=0\)) against `(SLOT-R)` on the increment. The lift freedom between the instance's increment and the carrier's designated \(L_\lambda(s)\) is closed: their difference has zero digit at height \(\lambda\), hence height \(>\lambda\), and the rise transfers.

**No theorem-statement change is made by this round.** No display of the statement suite S1.2–S1.8 is amended, no hypothesis is added to or removed from HE7.A's suite, no case is added or dropped, and no conclusion is touched. (RISE) and (HT) read exactly as r7 set them and r8 left them; (RISE) remains STIPULATED on r4 repair 3's `(SEC-RANK)` footing, and (HT) remains DERIVED from it. The one new display, (IDX-TWIST), is a derived identity of the level-one instance, not a clause of the theorem. Two sentences of the r8 counter survive verbatim and are not booked: "DEFINITION HE6-1's family at \(\ell=1\) IS the family of HE3's recenterings" is a statement about the family as a SET, which (IDX-TWIST) confirms, and "its recipe puts the \((\ell,d)=(1,1)\) member's increment at the member's own index" is a statement about HEIGHTS, which the twist does not touch. What was false was only the matching of index names, and that lived in the three sentences replaced by repair 1.

**Two named obligations remain open**, both at level one and both unchanged: `(LB1)` for clause-4 block construction, and `(MP1)` for the clause-5 peel at a recentered key. (RISE) is a carrier hypothesis, not a ledger obligation. No pin is added or removed, no Source-pin line is amended, and no source file is edited, so the expected pin count stays 32, the expected synthetic-marker count stays zero, and the expected source edit count stays zero.

**Landmark census for this round.** Six master-internal landmark strings, on four lines, each returning **1** under `sed -n '1,3667p' T2_SIGMA_LADDER_MASTER_2026-08-12.md | grep -cF -- '<string>'` on 2026-08-13: lines 3085, 3537, 3545 (two strings — the height ground and the corroboration clause) and 3665 (two strings — the two census counts). Five source lines, each returning **1** under `grep -cFx`: `HE3_PROOF_2026-08-08.md` 1114, 1115, 1131 and 1135; `HE6_PROOF_2026-08-08.md` 203. Two span delimiters re-verified at **1**: HE3 1092 and 1205.

Gap-or-worse repairs reset the clean count (S7: "A gap-or-worse repair resets the clean count"). **The clean-pass counter is RESET to 0 of 2.** The acceptance gate still owes **TWO consecutive clean hostile passes** over the r9 effective text before this note may leave attempt grade \(0/2\); the status line therefore stays "mathematical composition draft, attempt grade \(0/2\)", and by `(GRADE)` every composed instance stays \(0/2\) regardless of supplier grade.
