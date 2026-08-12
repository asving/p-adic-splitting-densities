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
