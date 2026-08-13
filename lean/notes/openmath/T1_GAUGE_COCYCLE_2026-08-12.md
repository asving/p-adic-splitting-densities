# T1 — LEMMA GAUGE-COCYCLE

## The wrap/\(\vartheta\) recursion, exact lifts, and normalization bridges, stated once

**RCT unit:** S-1-T1-gauge-cocycle, revision pass S-1, 2026-08-12  
**Status:** revised candidate of record, under hostile arc — repair rounds appended below; THE HIGHEST-NUMBERED r-SECTION GOVERNS; the clean-pass counter and owed passes are recorded in that section.  
**Supersedes:** the composed 2026-08-10 T1 draft and its inline repair riders

This revision folds the certified 2026-08-12 gauge-seam corrections into the statement rather than leaving them as riders. In particular:

- exact integral \(K_1\)-lifts are asserted on the proved live domain \(M>D'h\), and the composed-key coefficient contains the positive \(\eta^{W(t)}\) wrap correction;
- the canonical minimal-grid twist is separated from the actual print twist by the attained-origin factor \(z^\nu\);
- the weld is used only at the proved scope of the five-field package WELD-M-PKG; no cross-face coherence or uniqueness is asserted; and
- the HE6 slot coefficient is the normalized coefficient sum \(\gamma_k(A)\), not the generally vacuous sum of bare coefficient residues.

The lemma is one source of the tower gauge formulas. It organizes those fields of WELD-M-PKG that consume the formulas around the same cocycle, but it does not upgrade the package to a single coherent map.

## 1. Statement

### LEMMA GAUGE-COCYCLE

#### 1.1 Carrier and domain

Fix a discretely valued base field with uniformizer \(\pi\), residue field \(\mathbf F_Q\), and a MacLane/Okutsu tower with level-\(i\) residue field \(K_i\). At level \(1\), fix

\[
e_1,f_1,h\ge1,\qquad \gcd(e_1,h)=1,\qquad D'=e_1f_1,
\]

with

\[
dv_1(x)=h,\qquad dv_1(\pi)=e_1,
\qquad
\eta=\operatorname{res}\!\left(\frac{x^{e_1}}{\pi^h}\right),
\qquad
K_1=\mathbf F_Q(\eta),
\]

and chosen basis \(1,\eta,\ldots,\eta^{f_1-1}\).

For every integer height \(k\), let

\[
\widehat n_1(k)=x^{i(k)}\pi^{a(k)},\qquad
0\le i(k)<e_1,\qquad i(k)h+a(k)e_1=k.
\]

This is a Laurent normalizer at an arbitrary integer height. A full integral \(K_1\)-digit slot is asserted below only on the proved live domain \(k>D'h\). No full \(K_1\)-slot is asserted at \(k\le D'h\).

At a general level \(i\), fix exact-height normalizers \(\widehat n_i(m)\) in the prescribed bounded-exponent tower normal form, stage data

\[
e_{i+1},\qquad f_{i+1},\qquad u_{i+1},
\]

and

\[
\psi_{i+1}(y)
=
y^{f_{i+1}}-\sum_{t<f_{i+1}}c_ty^t
\in K_i[y],
\qquad c_0\ne0.
\]

Whenever an exact-height lift is invoked, assume it lies in its stated integral domain and satisfies

\[
dv_i(\operatorname{lift}_i(d;m))=m,
\qquad
\operatorname{res}\!\left(
\frac{\operatorname{lift}_i(d;m)}{\widehat n_i(m)}
\right)=d.
\]

Zero is lifted as zero. At level \(1\), conclusion (C6) supplies this lift uniformly when \(m>D'h\).

Define the repo and canonical letters

\[
\eta_{i+1}
=
\operatorname{res}\!\left(
\frac{\Phi_i^{e_{i+1}}}{\widehat n_i(u_{i+1})}
\right),
\qquad
z_{i+1}
=
\operatorname{res}\!\left(
\frac{\Phi_i^{e_{i+1}}}{\pi_{i+1}^{u_{i+1}}}
\right).
\]

At level \(1\), write

\[
\pi_2=x^{\ell_1}\pi^{\ell'_1},
\qquad
\ell_1h+\ell'_1e_1=1,
\qquad
0\le\ell_1<e_1.
\]

For a homogeneous slot of height \(su_{i+1}\), distinguish:

1. its coherent digit \(\Gamma\), read against \(\widehat n_i(su_{i+1})\);
2. its multiplicative coefficient, read against \(\widehat n_i(u_{i+1})^s\); and
3. its canonical residual read \(R_{i+1,\beta}\).

Assume at the consumed sites that the canonical residual read is multiplicative on the relevant ladder monomials and agrees with residue on value-zero factors. This is a site obligation, not an assertion about every homogeneous initial form.

Put

\[
\bar\kappa_i=\frac{u_{i+1}}{e(\mu_i)},
\qquad
w_i
=
R_{i+1,\bar\kappa_i}
\bigl(\widehat n_i(u_{i+1})\bigr)
\in K_i^\times.
\]

The carrier contains no letter recursion, cocycle identity, corrected-key formula, read dictionary, print-origin bridge, or weld coherence theorem.

#### (C1) Letter recursion

At every defined level,

\[
\boxed{
z_{i+1}=\eta_{i+1}\rho_i,
\qquad
\rho_i=
\operatorname{res}\!\left(
\frac{\widehat n_i(u_{i+1})}
{\pi_{i+1}^{u_{i+1}}}
\right).
}
\tag{C1-general}
\]

The quotient has value zero. Successive reduction by the tower relations expresses \(\rho_i\) as a monomial in preceding canonical letters. This is a terminating reduction algorithm; no closed exponent formula is asserted at arbitrary depth.

At level \(2\),

\[
\boxed{
z_2=\eta_2z_1^{-\lfloor\ell_1u_2/e_1\rfloor}.
}
\tag{C1-level-2}
\]

#### (C2) The normalized wrap cocycle and its telescope

Define

\[
\operatorname{wrap}(a,b)
=
\left\lfloor
\frac{i(a)+i(b)}{e_1}
\right\rfloor
\in\{0,1\}.
\]

Then

\[
\boxed{
\widehat n_1(a)\widehat n_1(b)
=
\widehat n_1(a+b)
\left(\frac{x^{e_1}}{\pi^h}\right)^{\operatorname{wrap}(a,b)}.
}
\tag{C2-wrap}
\]

For

\[
\tau_i(a,b)
=
\frac{\widehat n_i(a)\widehat n_i(b)}
{\widehat n_i(a+b)},
\]

associativity gives the normalized two-cocycle law

\[
\tau_i(0,a)=\tau_i(a,0)=1,
\qquad
\boxed{
\tau_i(a,b)\tau_i(a+b,c)
=
\tau_i(b,c)\tau_i(a,b+c).
}
\tag{C2-cocycle}
\]

Define the building-orientation telescope unit

\[
\boxed{
\vartheta_{i,s}
=
\operatorname{res}\!\left(
\frac{\widehat n_i(u_{i+1})^s}
{\widehat n_i(su_{i+1})}
\right)
\in K_i^\times.
}
\tag{C2-vartheta}
\]

Then

\[
\boxed{
\vartheta_{i,0}=\vartheta_{i,1}=1,
\qquad
\vartheta_{i,s+1}
=
\vartheta_{i,s}\,
\operatorname{res}
\bigl(\tau_i(su_{i+1},u_{i+1})\bigr).
}
\tag{C2-recursion}
\]

At level \(1\),

\[
\widehat n_1(u_2)^s
=
\widehat n_1(su_2)
\left(\frac{x^{e_1}}{\pi^h}\right)^{
\lfloor s\,i(u_2)/e_1\rfloor},
\]

and hence

\[
\boxed{
\vartheta_{1,s}
=
\eta^{\lfloor s\,i(u_2)/e_1\rfloor}.
}
\tag{C2-level-1}
\]

For \(s=f_2-t\), put

\[
W(t)
=
\left\lfloor
\frac{(f_2-t)i(u_2)}{e_1}
\right\rfloor.
\]

Thus

\[
\vartheta_{1,f_2-t}=\eta^{W(t)}.
\]

The exponent has the displayed positive sign.

#### (C3) Corrected key and read dictionary

For \(s=f_{i+1}-t\), let \(\Gamma_t\) denote the coherent digit against \(\widehat n_i(su_{i+1})\), and let \(c_t^{\mathrm{mult}}\) denote the coefficient against \(\widehat n_i(u_{i+1})^s\). Then

\[
\boxed{
\Gamma_t
=
c_t^{\mathrm{mult}}\vartheta_{i,s},
\qquad
c_t^{\mathrm{mult}}
=
\Gamma_t\vartheta_{i,s}^{-1}.
}
\tag{C3-dictionary}
\]

The corrected composed key is

\[
\boxed{
\Phi_{i+1}
=
\Phi_i^{e_{i+1}f_{i+1}}
-
\sum_{t<f_{i+1}}
\widehat k_t\Phi_i^{e_{i+1}t},
}
\tag{C3-key}
\]

where

\[
\boxed{
\widehat k_t
=
\operatorname{lift}_i\!\left(
c_t\vartheta_{i,f_{i+1}-t};
(f_{i+1}-t)u_{i+1}
\right).
}
\tag{C3-corrected-lift}
\]

At level \(1\), whenever

\[
M_t=(f_2-t)u_2>D'h,
\]

this is the explicit integral coefficient

\[
\boxed{
\widehat k_t
=
L_{M_t}\bigl(c_t\eta^{W(t)}\bigr).
}
\tag{C3-level-1-key}
\]

Its multiplicative coefficient is exactly \(c_t\).

The naive and corrected recipes agree in slot \(t\) exactly when

\[
c_t
\bigl(
\vartheta_{i,f_{i+1}-t}-1
\bigr)=0.
\]

They therefore agree if every relevant telescope unit is \(1\), including the cases \(\eta=1\) at level \(1\) and \(f_{i+1}=1\). This says nothing about whether arbitrary \(K_1\)-digits are \(x\)-free.

For the B-law orientation define

\[
\boxed{
\Theta_i(t)
=
\vartheta_{i,f_{i+1}-t}^{-1}
=
\operatorname{res}\!\left(
\frac{
\widehat n_i((f_{i+1}-t)u_{i+1})
}{
\widehat n_i(u_{i+1})^{f_{i+1}-t}
}
\right).
}
\tag{C3-Theta}
\]

Let \(\beta_t\) be the slot grade and set

\[
u(\beta_t)
=
R_{i+1,\beta_t}
\bigl(
\widehat n_i((f_{i+1}-t)u_{i+1})
\bigr).
\]

At every site where the stated ladder-multiplicativity obligation is discharged,

\[
\boxed{
u(\beta_t)
=
\Theta_i(t)w_i^{f_{i+1}-t}.
}
\tag{C3-B-law}
\]

Consequently a slot with coherent digit \(\Gamma_t\) has canonical read

\[
\boxed{
R_{i+1,\beta_t}(\text{slot }t)
=
w_i^{f_{i+1}-t}\Theta_i(t)\Gamma_t.
}
\tag{C3-canonical-read}
\]

At the corrected key,

\[
\Gamma_t
=
c_t\vartheta_{i,f_{i+1}-t},
\]

so the \(\vartheta/\Theta\) factors cancel. The three reads are therefore

\[
\boxed{
\begin{aligned}
\text{multiplicative residual}
&=\psi_{i+1}(y),\\
\text{coherent digits}
&=
\bigl(
c_t\vartheta_{i,f_{i+1}-t}
\bigr)_{t<f_{i+1}},\\
\text{canonical residual}
&=
\psi_{i+1}^{(w_i)}(y)
:=
w_i^{f_{i+1}}\psi_{i+1}(y/w_i).
\end{aligned}
}
\tag{C3-three-reads}
\]

The map

\[
P(y)\longmapsto w_i^{\deg P}P(y/w_i)
\]

preserves irreducible-factor degrees and multiplicities. Residual factor patterns, and verdict data depending only on those patterns, are gauge-invariant. Conversion of a residual factor pattern to a p-adic splitting type still uses the surrounding tower correctness theorem.

#### (C4) Attained-origin normalization bridge

This clause records the correction that is independent of the \(\vartheta\)-telescope but belongs to the same gauge seam. At a print level write

\[
s_{\min}(\beta)=\ell\beta\bmod e,
\qquad
t_{\min}(\beta)
=
\frac{\ell\beta-s_{\min}(\beta)}e,
\qquad
\varepsilon(\beta)=z^{-t_{\min}(\beta)}.
\]

If the actual attained initial abscissa is

\[
s_{\mathrm{act}}
=
s_{\min}(\beta)+\nu e,
\qquad
\nu\in\mathbf Z_{\ge0},
\]

then the print Definition-\(t(i)\) exponent in print orientation is

\[
t_{\mathrm{Def}}
=
\frac{s_{\mathrm{act}}-\ell\beta}{e}
=
\nu-t_{\min}(\beta).
\]

Therefore

\[
\boxed{
z^{t_{\mathrm{Def}}}
=
z^\nu\varepsilon(\beta),
\qquad
\varepsilon(\beta)
=
z^{t_{\mathrm{Def}}-\nu}.
}
\tag{C4-origin}
\]

Raw equality

\[
z^{t_{\mathrm{Def}}}=\varepsilon(\beta)
\]

holds exactly when \(z^\nu=1\); it holds in particular when \(\nu=0\). It is false in general to identify the canonical minimal-grid factor with the raw print factor without displaying \(z^\nu\).

If \(H(y)\) is the harness residual and \(P(y)\) the normalized print residual, the corresponding support statement is

\[
H(y)=y^\nu Q(y),
\qquad
P(y)=aQ(by),
\qquad
a,b\in K^\times.
\]

Thus, for nonzero residuals,

\[
\boxed{
\operatorname{Supp}_y(H)
=
\nu+\operatorname{Supp}_y(P),
\qquad
\deg H=\deg P+\nu.
}
\tag{C4-support}
\]

Attained abscissas and normalized support widths agree. Ordinary exponent supports and ordinary degrees agree only after translating the harness origin by \(\nu\).

#### (C5) HE6 normalized slot coefficient and canonical-normalizer read

Let

\[
A(x)=\sum_{j<D'}a_jx^j,
\qquad
k=dv(A),
\qquad
i=i(k),
\qquad
n(k)=x^i\pi^{(k-ih)/e_1}.
\]

Define

\[
\boxed{
\gamma_k(A)
=
\sum_{\substack{t\ge0\\i+e_1t<D'}}
\operatorname{res}\!\left(
a_{i+e_1t}
\pi^{-(k-(i+e_1t)h)/e_1}
\right)\eta^t.
}
\tag{C5-gamma}
\]

A coefficient whose pin lies strictly above height \(k\) contributes zero.

For every tower point \(\xi\) carrying the specified residue embedding \(\iota_\xi\),

\[
\boxed{
\operatorname{res}\!\left(
\frac{A(\xi)}{n(k)(\xi)}
\right)
=
\iota_\xi\bigl(\gamma_k(A)\bigr).
}
\tag{C5-normalizer-read}
\]

Let \(i_0\in[0,e_1)\) satisfy

\[
i_0h\equiv1\pmod {e_1},
\]

and define

\[
q(k)=\frac{i_0k-i(k)}{e_1}.
\]

For the canonical level-one normalizer

\[
\varpi
=
x^{i_0}\pi^{(1-i_0h)/e_1},
\]

one has

\[
\operatorname{res}\!\left(
\frac{n(k)(\xi)}
{\varpi(\xi)^k}
\right)
=
\eta_\xi^{-q(k)}.
\]

Hence

\[
\boxed{
\operatorname{res}\!\left(
\frac{A(\xi)}
{\varpi(\xi)^k}
\right)
=
\iota_\xi\bigl(\gamma_k(A)\bigr)
\eta_\xi^{-q(k)}.
}
\tag{C5-varpi-read}
\]

The coefficient normalizers in (C5-gamma) are essential. Replacing each normalized coefficient residue by \(\operatorname{res}(a_j)\) is generally false and may make all tying contributions vanish.

The same integer function records the carry:

\[
\boxed{
q(a+b)
=
q(a)+q(b)+\operatorname{wrap}(a,b).
}
\tag{C5-carry}
\]

#### (C6) Exact integral \(K_1\)-lift and the \(x\)-free criterion

Let \(M>D'h\), put

\[
i=i(M),
\qquad
a=\frac{M-ih}{e_1},
\]

and write uniquely

\[
\lambda
=
\sum_{r=0}^{f_1-1}\lambda_r\eta^r,
\qquad
\lambda_r\in\mathbf F_Q.
\]

Define

\[
\boxed{
L_M(\lambda)
=
\sum_{r=0}^{f_1-1}
\widetilde{\lambda_r}
x^{i+e_1r}\pi^{a-rh}.
}
\tag{C6-lift}
\]

Then

\[
L_M(\lambda)\in\widehat O[x],
\qquad
\deg L_M(\lambda)<D',
\qquad
dv(L_M(\lambda))=M
\]

for \(\lambda\ne0\). Every nonzero summand has exact height \(M\), and

\[
\boxed{
\operatorname{res}\!\left(
\frac{L_M(\lambda)(\theta)}
{n(M)(\theta)}
\right)
=
\lambda.
}
\tag{C6-residue}
\]

For \(\lambda\ne0\),

\[
\boxed{
L_M(\lambda)\text{ is an }x\text{-free monomial}
\iff
i(M)=0
\text{ and }
\lambda\in\mathbf F_Q.
}
\tag{C6-x-free}
\]

The hypothesis \(M>D'h\) is the simple sufficient domain used by all live consumers here. This theorem makes no universal full-slot assertion at lower heights.

In the composed-key application, put

\[
r=f_2-t,
\qquad
M=ru_2>D'h.
\]

Then

\[
L_{ru_2}\bigl(c_t\eta^{W(t)}\bigr)
\]

has coherent digit \(c_t\eta^{W(t)}\) and multiplicative coefficient \(c_t\).

If the tower additionally has

\[
u_2>e_2D'h,
\]

every monomial in this lift, after multiplication by a monomial of \(\Phi'^{e_2t}\), clears the outer side by at least

\[
\boxed{
\frac{r(u_2-e_2D'h)}{e_1}>0.
}
\tag{C6-clearance}
\]

Collection and \(\Phi'\)-carry can cancel terms or move them upward, but cannot create a term below that side.

#### (C7) WELD-M-PKG interface and scope fence

Let

\[
\mathbf T_T
=
(\mathbf T_{M0},\mathbf T_{M1},\mathbf T_{M2},
 \mathbf T_{M3},\mathbf T_{M4})
\]

denote the anchored five-field package of WELD-M-PKG. T1 relates to its fields only as follows:

| Package field | T1 datum available to that field |
|---|---|
| \(M0\), division chains | Common tower and canonical division-chain anchor; no new identity is proved here. |
| \(M1\), shear and \(w_m=v_{m+1}\) | The carrier unit \(w_i\) and letter recursion (C1); the shear, equality, and membership fences remain supplier facts. |
| \(M2\), per-slot character transport | The dictionary and canonical read in (C3), together with the origin correction (C4). |
| \(M3\), multiplication transport | The cocycle/telescope (C2) and canonical twist in (C3), only on the scored stratum. |
| \(M4\), lift covariance | The exact-height formulas (C5)–(C6), only at W2-C3’s accepted fence. |

Accordingly,

\[
\boxed{
\begin{gathered}
\text{T1 organizes five named fields around one tower cocycle;}\\
\text{it proves no cross-face coherence theorem.}
\end{gathered}
}
\tag{C7-scope}
\]

It also proves no uniqueness of the gauge. Gauges with a fixed coboundary may differ by a character. WELD-M-PKG is an existence package assembled field by field, and T1 neither identifies its heterogeneous fields as restrictions of one map nor supplies compatibility beyond the anchors explicitly displayed in the package theorem.

## 2. Proof

### 2.1 Letter recursion

Divide the defining fractions for \(z_{i+1}\) and \(\eta_{i+1}\):

\[
z_{i+1}
=
\eta_{i+1}
\operatorname{res}\!\left(
\frac{\widehat n_i(u_{i+1})}
{\pi_{i+1}^{u_{i+1}}}
\right).
\]

Both normalizers have height \(u_{i+1}\), so the quotient has value zero. Successively remove the highest key by the corresponding value-zero tower relation. Coprimality forces the highest exponent into the required ramification-index class; iteration terminates at a value-zero \(x,\pi\)-monomial, hence a power of \(x^{e_1}/\pi^h\). This proves (C1-general) and the asserted reduction algorithm.

At level \(2\), with \(u=u_2\),

\[
\frac{\widehat n_1(u)}{\pi_2^u}
=
x^{i(u)-\ell_1u}
\pi^{a(u)-\ell'_1u}.
\]

The congruences

\[
i(u)h\equiv u\equiv\ell_1uh\pmod {e_1}
\]

give

\[
i(u)
=
\ell_1u
-
e_1
\left\lfloor
\frac{\ell_1u}{e_1}
\right\rfloor.
\]

The value-zero equation supplies the corresponding \(\pi\)-exponent, so the quotient is

\[
\left(\frac{x^{e_1}}{\pi^h}\right)^{
-\lfloor\ell_1u/e_1\rfloor}.
\]

Taking residues proves (C1-level-2).

### 2.2 Cocycle and telescope

The reduced representative of \(i(a)+i(b)\) is \(i(a+b)\). Hence

\[
i(a)+i(b)
=
i(a+b)+e_1\operatorname{wrap}(a,b).
\]

Height additivity gives

\[
a(a)+a(b)
=
a(a+b)-h\operatorname{wrap}(a,b),
\]

which proves (C2-wrap). Comparing the two parenthesizations of

\[
\widehat n_i(a)\widehat n_i(b)\widehat n_i(c)
\]

proves (C2-cocycle).

For \(u=u_{i+1}\),

\[
\frac{\widehat n_i(u)^{s+1}}
{\widehat n_i((s+1)u)}
=
\frac{\widehat n_i(u)^s}
{\widehat n_i(su)}
\frac{\widehat n_i(su)\widehat n_i(u)}
{\widehat n_i((s+1)u)}.
\]

Taking residues proves the recursion.

At level \(1\), reducing the \(x\)-exponent \(s\,i(u_2)\) modulo \(e_1\) gives exactly

\[
\left\lfloor\frac{s\,i(u_2)}{e_1}\right\rfloor
\]

copies of \(x^{e_1}/\pi^h\), proving (C2-level-1) and the positive \(\eta^{W(t)}\) sign.

### 2.3 Corrected key and the three reads

If a height-\(su\) element has coherent digit \(\Gamma\), division first by \(\widehat n_i(su)\) and then by \(\widehat n_i(u)^s\) gives

\[
c^{\mathrm{mult}}
=
\Gamma
\operatorname{res}\!\left(
\frac{\widehat n_i(su)}
{\widehat n_i(u)^s}
\right)
=
\Gamma\vartheta_{i,s}^{-1}.
\]

This proves the dictionary. Choosing

\[
\Gamma_t=c_t\vartheta_{i,f-t}
\]

therefore makes the multiplicative coefficient exactly \(c_t\), proving the corrected-key and degeneracy claims.

Put

\[
N=\widehat n_i(u),
\qquad
M_s=\widehat n_i(su).
\]

At a consumed site, ladder multiplicativity and the value-zero rule give

\[
w_i^s
=
R(N^s)
=
R(M_s)\operatorname{res}(N^s/M_s)
=
R(M_s)\vartheta_{i,s}.
\]

Thus

\[
R(M_s)
=
w_i^s\vartheta_{i,s}^{-1},
\]

which is the B-law. Multiplying by a coherent digit proves (C3-canonical-read).

At the corrected key, the inverse telescope factors cancel slotwise, and summing gives

\[
y^f-\sum_{t<f}c_tw_i^{f-t}y^t
=
w_i^f\psi(y/w_i).
\]

Scaling the variable by a unit transports factorizations bijectively and preserves degrees, multiplicities, and irreducibility.

### 2.4 Attained-origin bridge

Substitution of

\[
s_{\mathrm{act}}=s_{\min}+\nu e
\]

gives

\[
t_{\mathrm{Def}}
=
\frac{s_{\min}+\nu e-\ell\beta}{e}
=
\nu-t_{\min}.
\]

Exponentiating by \(z\) proves (C4-origin).

The support and degree formulas follow because multiplication by \(y^\nu\) translates ordinary exponents, whereas multiplication by a unit and substitution by a unit preserve them.

### 2.5 Normalized slot coefficient and carry

For \(j=i+e_1t\), direct division gives

\[
\frac{a_j\xi^j}{n(k)(\xi)}
=
\left(
a_j\pi^{-(k-jh)/e_1}
\right)
\left(
\xi^{e_1}\pi^{-h}
\right)^t.
\]

Indices outside the class \(i\bmod e_1\) have strictly larger value and vanish after reduction; pins above \(k\) also reduce to zero. Summing the surviving residues proves (C5-normalizer-read).

Composing with

\[
\operatorname{res}
\left(
\frac{n(k)}
{\varpi^k}
\right)
=
\eta^{-q(k)}
\]

proves (C5-varpi-read).

Finally,

\[
\begin{aligned}
e_1\bigl(q(a+b)-q(a)-q(b)\bigr)
&=
i(a)+i(b)-i(a+b)\\
&=
e_1\operatorname{wrap}(a,b),
\end{aligned}
\]

which proves (C5-carry).

### 2.6 Exact integral lift

For \(0\le r<f_1\),

\[
i+e_1r\le D'-1,
\]

and

\[
a-rh
=
\frac{M-(i+e_1r)h}{e_1}
\ge0
\]

because \(M>D'h\). Thus every displayed term is integral and has degree less than \(D'\).

Its height is

\[
e_1(a-rh)+(i+e_1r)h=M.
\]

After division by \(n(M)\), its residue is \(\lambda_r\eta^r\). Basis independence prevents cancellation and proves (C6-residue).

The \(x\)-exponents \(i+e_1r\) are distinct and nonnegative. A nonzero lift is one \(x\)-free monomial exactly when only \(r=0\) occurs and \(i=0\), equivalently when

\[
i(M)=0
\quad\text{and}\quad
\lambda\in\mathbf F_Q.
\]

The corrected-key and clearance applications are then the substitutions stated in (C6).

### 2.7 Package boundary

WELD-M-PKG is proved by choosing five witnesses and applying a product/record constructor. Conclusions (C1)–(C6) give common tower formulas that individual fields may cite, exactly as listed in (C7).

Nothing in those proofs supplies:

- a map with all five heterogeneous source and target types;
- a compatibility square between distinct fields; or
- uniqueness of the gauge.

Hence only the organization claim in (C7-scope) follows.

## 3. Absorption map

“Verbatim” means that, after replacing local names by the displayed T1 names, the certified local mathematical display is an immediate specialization with no added hypothesis or conclusion.

“Adapted” means that T1 deliberately changes notation, carries a certified domain or fence, or separates a normalization that the old annex conflated.

| Annex | Local site | T1 conclusion | Mode and specialization |
|---|---|---|---|
| A1 GENHN | GENHN-LIFT | C6 | **Verbatim** on \(M>D'h\): same component formula, integrality, degree, exact height, and residue. |
| A1 GENHN | Corrected T(b)\('\) coefficient | C2, C3, C6 | **Verbatim** with \(M=(f_2-t)u_2\): \(L_M(c_t\eta^{W(t)})\); the clearance bound is retained. |
| A2 HETOW | Wrap/carry preamble | C2, C5 | **Verbatim**: the wrap identity and \(q(a+b)=q(a)+q(b)+\operatorname{wrap}(a,b)\). |
| A2 HETOW | Telescope and corrected key | C2, C3 | **Verbatim** after \(s=f_2-t\); T1 makes the positive \(\eta^{W(t)}\) sign explicit. |
| A3 GENTOW1 | Corrected coefficient pin | C3 | **Adapted only in notation**: the local coherent digit \(\gamma_t\) is T1’s \(\Gamma_t\), avoiding collision with HE6’s \(\gamma_k(A)\). |
| A3 GENTOW1 | Value-blind budgets/floors | C3 | **Adapted/fenced**: corrected and naive lifts have equal exact height where the integral lift exists; budgets and floors themselves are not reproved. |
| A4 GENTOW3 | Gauge-annex corrected key | C3, C6 | **Verbatim** on the live lift domain. |
| A4 GENTOW3 | \(x\)-free rescope | C6 | **Verbatim**: \(x\)-free iff \(i(M)=0\) and the digit lies in \(\mathbf F_Q\); T1 withdraws any full-slot claim below \(D'h\). |
| A5 GENTOW4 | S0 naive key | C3, C6 | **Adapted** by the explicit domain and corrected coherent digit. |
| A5 GENTOW4 | 4.1(c)/S3 bridge | C3, C4 | **Adapted**: the \(\vartheta\)-cancellation is verbatim, but any raw-print identification must also carry \(z^\nu\). |
| A5 GENTOW4 | BOX-3 no-\(\eta\) axis | C2, C3 | **Verbatim**: a \(\vartheta=1\) battery cannot test naive versus corrected. |
| A5 GENTOW4 | S4 residue-one relation | C2, C6 | **Verbatim**: \(\eta=1\) is not \(f_1=1\), and does not make arbitrary digits \(x\)-free. |
| A6 GENTOW6 | Corrected coefficient/full support | C3, C6 | **Adapted**: full support is proved on \(M>D'h\), with normalized coefficients when a slot is read coefficientwise. |
| A6 GENTOW6 | 6.3 scalar read | C5, C6 | **Materially adapted**: use \(\gamma_k(A)\) with coefficient normalizers; the bare-residue formula is not absorbed. Overflow uses the actual top exponent. |
| A7 GENTOW2 | S5.1 letter formula | C1 | **Verbatim** at level \(2\). |
| A7 GENTOW2 | S5.2 B-law | C3 | **Verbatim** after the explicit inverse orientation \(\Theta=\vartheta^{-1}\), at sites where ladder multiplicativity is discharged. |
| A7 GENTOW2 | Factor-pattern invariance | C3 | **Verbatim**: \(\psi^{(w)}=w^f\psi(y/w)\). |

Supporting context, not counted as a separate A1–A7 annex:

- GENTOW5’s definitions of \(w\) and \(\psi^{(w)}\) are absorbed verbatim; its dictionary is absorbed with the \(\Gamma/\gamma_k\) notation separation.
- GRTJA’s JA-EPS-CORR is absorbed verbatim in (C4), including the exact root-of-unity criterion \(z^\nu=1\).
- WELD-M-PKG is not absorbed as a stronger theorem: (C7) is only an interface map and scope fence.
- HE6-0\(''\) is absorbed with adapted names but with its corrected normalized coefficient formula verbatim.

The B-law rows consume only ladder-monomial multiplicativity and the value-zero digit read at their stated sites. At \(i=2\), these are supplied by GENTOW2-B\(''\). For \(i\ge3\), they must cite the accepted status, if any, of the level-general GENTOW5-W(i) supplier. T1 does not promote that sitewise result to an unproved theorem about all homogeneous initial forms.

## 4. Verification record and revision battery

### 4.1 Inherited sealed evidence

The 2026-08-10 sealed battery remains historical evidence, not a certification of this revised text. Its computed surface had 83 computed-versus-registered rows plus two literal bookkeeping rows.

All substantive rows were green except the preregistered F4-JOINT display slip. The correct value is

\[
\psi(y)=y^2+y+\omega,
\qquad
w=\omega
\quad\Longrightarrow\quad
\boxed{
\psi^{(w)}(y)=y^2+\omega y+1.
}
\]

The old instrument’s orientation tooth scored only one B-unit and did not score the promised full three-slot canonical vector. Neither defect is carried forward as a passed check.

The inherited exact frames remain:

| Frame | Essential axes |
|---|---|
| X | \(p=3\), \(e_1=2,f_1=1,h=1,\eta=2,u_2=3\); corrected versus naive p-adic split. |
| FR-G | The GENTOW4 partial-side witness and separator regression. |
| F4-JOINT | \(K_1=\mathbf F_4\), \(e_1=2,f_1=2,h=1,\eta=w=\omega\), live wrap, quadratic and \(\mu=3\) legs. |
| LP/LD | Recorded GENTOW2 letter and inverse-cocycle geography. |

The inherited exact predictions are unchanged except for the corrected F4-JOINT value above. At the F4-JOINT quadratic,

\[
R_{\mathrm{corr}}=y^2+y+\omega,
\qquad
R_{\mathrm{naive}}=y^2+y+1,
\qquad
\psi^{(w)}=y^2+\omega y+1.
\]

At its \(\mu=3\) leg,

\[
(\vartheta_0,\vartheta_1,\vartheta_2,\vartheta_3)
=
(1,1,\omega,\omega),
\]

\[
(\Gamma_2,\Gamma_1,\Gamma_0)
=
(1,\omega,\omega),
\]

\[
\bigl(
u(\beta_2),u(\beta_1),u(\beta_0)
\bigr)
=
(\omega,\omega,\omega^2),
\]

and the full canonical coefficient vector is

\[
(\omega,\omega^2,1),
\]

giving \((y+\omega)^3\).

### 4.2 Required revision checks

The new hostile battery must add the following scored rows before this revision can receive a clean grade.

1. **GENHN-LIFT boundary.** Check integrality, degree, height, and residue for several \(M>D'h\), including \(f_1\ge2\). Also instantiate a low-height counterexample such as

   \[
   (e_1,f_1,h,M)=(1,2,1,0)
   \]

   to ensure the code does not infer a full \(K_1\)-slot from integrality of \(n(M)\) alone.

2. **Positive-wrap sign.** Re-run the corrected/naive and wrong-sign teeth. Exact coefficient equality, not merely factor pattern, must be scored.

3. **JA origin.** For \(\nu=0\), verify raw and canonical factors agree. For \(\nu>0\) and \(z^\nu\ne1\), verify the raw equality fails by exactly \(z^\nu\). Add a root-of-unity case with \(\nu>0\) and \(z^\nu=1\), so the battery rejects the overstatement “iff \(\nu=0\).” Score the support and degree translation by \(\nu\).

4. **HE6 coefficient normalization.** Use a tying coefficient of positive valuation for which

   \[
   \operatorname{res}(a_j)=0
   \]

   but

   \[
   \operatorname{res}\!\left(
   a_j\pi^{-(k-jh)/e_1}
   \right)\ne0.
   \]

   Score (C5-normalizer-read), (C5-varpi-read), and the \(-q(k)\) sign.

5. **Full orientation tooth.** With \(\Theta\) intentionally replaced by \(\vartheta\), score all three entries of the canonical \(\mu=3\) vector, not only the \(s=2\) B-unit.

6. **Weld scope lint.** Fail the document check if T1 contains “one transport map,” “unique gauge,” or an unqualified cross-face compatibility claim. Confirm every \(M3\) use retains the scored-stratum fence and every \(M4\) use the accepted W2-C3 fence.

The four original planted teeth remain mandatory:

- gauge-naive;
- wrong-sign;
- misindexed telescope; and
- inverse-orientation confusion.

Every tooth must fire.

## 5. Honesty ledger

1. A closed canonical-letter exponent vector is proved only at level \(2\). General depth has a terminating reduction algorithm.
2. The B-law is conditional on the stated sitewise residual-read facts. T1 does not assume or prove multiplicativity on all homogeneous initial forms.
3. \(\vartheta_{i,s}\) is the building/dictionary orientation, while

   \[
   \Theta_i(t)=\vartheta_{i,f-t}^{-1}
   \]

   is the B-law orientation.
4. The canonical residual is

   \[
   \psi^{(w)}=w^f\psi(y/w).
   \]

   This preserves factor patterns, not literal coefficients.
5. The canonical minimal-grid factor \(\varepsilon\) and the raw print factor differ by \(z^\nu\). Raw equality is equivalent to \(z^\nu=1\), not to \(\nu=0\) unless an additional order hypothesis makes those equivalent.
6. The full integral level-one lift is proved here on \(M>D'h\). No universal full \(K_1\)-slot is claimed at lower heights.
7. The HE6 digit is \(\gamma_k(A)\) with coefficient normalizers. It is different from the coherent corrected-key digit \(\Gamma_t\).
8. \(\eta=1\) removes the level-one wrap correction but does not imply \(f_1=1\) or make arbitrary digits \(x\)-free.
9. Gauge-invariant residual factor patterns become splitting types only through the surrounding tower correctness theorem.
10. T1 does not prove note-specific budgets, floors, fullness counts, separator inequalities, clearance outside (C6-clearance), or the remaining extraction and attainment claims of GENTOW6 6.3\('\).
11. WELD-M-PKG is five heterogeneously typed fields assembled into one named record. T1 proves neither a single cross-face map nor compatibility beyond the package’s displayed anchors.
12. Gauge uniqueness is not asserted. Fixed-coboundary gauges form a torsor under the available character group.
13. F4-JOINT remains a finite graded-carrier model, not an explicit p-adic realization. Its formal sigma values are not PARI measurements.
14. The explicit joint p-adic realization remains open and is not required for the algebraic lemma.

## 6. CHANGES from the 2026-08-10 composition

| Revision | Driver | Annex effect |
|---|---|---|
| Replaced the conditional old C4 lift by (C6) on the uniform live domain \(M>D'h\), including integrality, residue, degree, and clearance. | GENHN-LIFT and the later occupied-height tightening | A1 GENHN becomes verbatim; A4 GENTOW3 and A6 GENTOW6 are absorbed with the live-domain fence. |
| Made \(L_{(f_2-t)u_2}(c_t\eta^{W(t)})\) the level-one corrected coefficient, with positive wrap exponent. | GENHN-LIFT application and HETOW wrap correction | A1 and A2 are verbatim; A3, A5, and A6 specialize with notation adaptation. |
| Renamed coherent digits from \(\gamma_t\) to \(\Gamma_t\). | HE6’s corrected, reserved \(\gamma_k(A)\) | A3, A5, A6, and the GENTOW5 dictionary rows are notational adaptations; no formula changes. |
| Added the normalized coefficient formula (C5-gamma) and the \(\eta^{-q(k)}\) canonical-normalizer factor. | HE6 F-1 | A6’s scalar-reading site is materially adapted; the old bare-residue formula is rejected rather than absorbed. |
| Added (C4-origin) and the \(\nu\)-translated support/degree law. | JA-EPS-CORR and JA-MIN-CORR | A5 bridge consumption is adapted: tower \(\vartheta\)-cancellation survives, but raw print equality carries \(z^\nu\). |
| Stated raw print/canonical equality as iff \(z^\nu=1\), with \(\nu=0\) only a sufficient special case. | JA-EPS-CORR | Prevents a new false “iff \(\nu=0\)” strengthening. |
| Added the five-row package interface and boxed no-cross-face-coherence fence. | WELD-M-PKG | No local annex is strengthened. T1 organizes M0–M4 citations but does not absorb or reprove the package as one map. |
| Withdrew any gauge-uniqueness implication and recorded character-torsor ambiguity. | WELDMASTER C6 F-1/F-2 | Scope correction across all annex consumers; formulas C1–C6 are unchanged. |
| Narrowed the residual-read carrier assumption to the ladder monomials consumed at B-law sites. | Earlier T1 G-2 plus WELD package-scoping discipline | A5/A7/GENTOW5 B-law rows remain supplier-dependent rather than globally assumed. |
| Corrected F4-JOINT \(\psi^{(w)}\) to \(y^2+\omega y+1\) in the draft body. | Sealed P-J2 diagnosis | A7 factor-pattern absorption remains verbatim; the exact-value defect is removed. |
| Required the orientation tooth to score the full three-slot vector. | Sealed instrument disclosure F-5 | Verification-only change; no annex statement changes. |
| Reclassified the sealed 2026-08-10 run as inherited evidence rather than certification of the revised statement. | Revision integrity | All seven annex consumptions must be rechecked against this text. |

## 7. Hostile arc plan

The first hostile pass should attack, in this order:

1. **Normalization composition at a live \(\nu>0\), live-wrap, \(w\ne1\) slot.** Verify that \(\vartheta\), \(w\), and \(z^\nu\) occur in distinct places and that no cancellation silently drops the attained-origin factor.

2. **HE6-to-C3 digit typing.** Attempt to substitute a bare coefficient residue for \(\gamma_k(A)\), and attempt to identify \(\gamma_k(A)\) with \(\Gamma_t\) without the exact-height normalizer. A successful substitution would expose a type or normalization error.

3. **Lift-domain boundary.** Probe \(M=D'h\) and lower heights, especially \(f_1>1\), for any sentence that still promises a full integral \(K_1\)-slot or silently uses one.

4. **Weld scope.** Search every proof and absorption row for an inferred compatibility between M0–M4, a single-map interpretation, or gauge uniqueness. None is available from record assembly.

5. **B-law supplier perimeter.** Check each A5/A7/GENTOW5 consumer against the actual accepted grade and level range of GENTOW2-B\(''\)/GENTOW5-W(i), including any unresolved \(i=1\) tie.

6. **Root-of-unity exception.** Use \(\nu>0\) with \(z^\nu=1\) to refute any accidental replacement of the exact JA criterion by “only at \(\nu=0\).”

7. **Sign and inverse conventions.** Re-run the positive-\(W\), wrong-sign, misindexed-telescope, and full-vector \(\Theta=\vartheta^{-1}\) teeth.

8. **Consumption sweep.** For each of A1–A7, verify that the local theorem uses no stronger lift domain, raw-print equality, scalar gauge, or weld coherence than the corresponding T1 row supplies.

A clean first pass must either discharge all eight attacks or return a finding with an exact statement span and a live consumer. Only after repair should the second independent hostile pass run.

The acceptance gate remains two clean hostile passes plus the revised machine battery. The historical 2026-08-10 run does not count as either clean pass.


---

## r1 (2026-08-12): the three T1A gaps repaired

*(Derived by the T1R1 run (gpt-5.6-sol high, runs/cert5/T1R1_output.log) from the T1A pass-1 findings; transcribed unaltered; pass 2 of the arc follows.)*

## T1 r1 corrections — 2026-08-12

### R1-1 — Define the base canonical letter

In §1.1, immediately after

\[
\eta=\operatorname{res}\!\left(\frac{x^{e_1}}{\pi^h}\right),
\qquad
K_1=\mathbf F_Q(\eta),
\]

insert:

> Set the base canonical residue letter
> \[
> \boxed{z_1:=\eta.}
> \tag{C1-base-letter}
> \]
> Thus the level-two recursion below uses a defined letter; this is a notation convention, not an additional relation among higher-level letters.

In §2.1, replace the final sentence

> Taking residues proves (C1-level-2).

with:

> Taking residues and using the base convention \(z_1=\eta\) proves (C1-level-2).

This makes

\[
z_2=\eta_2z_1^{-\lfloor\ell_1u_2/e_1\rfloor}
\]

identical to the computed residue

\[
\eta_2\eta^{-\lfloor\ell_1u_2/e_1\rfloor}.
\]

### R1-2 — Normalize every height-zero normalizer

In §1.1, replace

> At a general level \(i\), fix exact-height normalizers \(\widehat n_i(m)\) in the prescribed bounded-exponent tower normal form, stage data

with:

> At a general level \(i\), fix exact-height normalizers \(\widehat n_i(m)\) in the prescribed bounded-exponent tower normal form, with the height-zero normalization
> \[
> \boxed{\widehat n_i(0)=1.}
> \tag{C2-zero-normalizer}
> \]
> Fix also stage data

In §2.2, replace

> Comparing the two parenthesizations of
> \[
> \widehat n_i(a)\widehat n_i(b)\widehat n_i(c)
> \]
> proves (C2-cocycle).

with:

> Comparing the two parenthesizations of
> \[
> \widehat n_i(a)\widehat n_i(b)\widehat n_i(c)
> \]
> proves the cocycle identity. The convention \(\widehat n_i(0)=1\) gives
> \[
> \tau_i(0,a)=\tau_i(a,0)=1
> \]
> and also
> \[
> \vartheta_{i,0}
> =
> \operatorname{res}\!\left(\widehat n_i(0)^{-1}\right)
> =1.
> \]
> Exact-height equality gives \(\vartheta_{i,1}=1\). This proves the normalized assertions in (C2-cocycle) and (C2-recursion).

### R1-3 — Respect the carrier implication \(\eta=1\Rightarrow f_1=1\)

In the absorption map, replace the A5 row

> | A5 GENTOW4 | S4 residue-one relation | C2, C6 | **Verbatim**: \(\eta=1\) is not \(f_1=1\), and does not make arbitrary digits \(x\)-free. |

with:

> | A5 GENTOW4 | S4 residue-one relation | C2, C6 | **Adapted to the carrier**: because \(K_1=\mathbf F_Q(\eta)\) with basis \(1,\eta,\ldots,\eta^{f_1-1}\), the specialization \(\eta=1\) forces \(K_1=\mathbf F_Q\) and hence \(f_1=1\). It removes the level-one wrap correction, but it does not by itself make an arbitrary lift \(x\)-free: (C6-x-free) still additionally requires \(i(M)=0\). |

Replace honesty-ledger item 8 with:

> 8. Under the stated carrier, \(\eta=1\) forces \(K_1=\mathbf F_Q\) and \(f_1=1\); these are not independent specialization axes. The condition \(\eta=1\) removes the level-one wrap correction, but it does not by itself make arbitrary digits \(x\)-free, because (C6-x-free) still requires \(i(M)=0\).

Add this row to §6:

> | Defined \(z_1=\eta\), normalized \(\widehat n_i(0)=1\), and corrected the A5 residue-one specialization to record \(\eta=1\Rightarrow f_1=1\) under the carrier. | T1A hostile pass, findings G1–G3, 2026-08-12 r1 | Repairs the level-two letter formula and normalized cocycle endpoints; A5 is adapted rather than falsely marked verbatim. |


---

## r2 (2026-08-12): the T1P findings + the A2–A7 consumption re-scope

*(Derived by the T1R2 run (gpt-5.6-sol high, runs/comp1/T1R2_output.log) from the T1P pass findings (1C+3G+1m) and the strict consumption-check results (A1 pass; A2–A7 re-scoped to pinned gauge subclaims per the blueprint's non-row-annex provision); transcribed unaltered; the arc counter resets — two consecutive clean passes owed from here.)*

# T1 r2 corrections — 2026-08-12

These edits are statement-narrowing repairs. Supplier-dependent facts are named explicitly and are not counted as proved by T1.

## R2-1 — Remove the unsupported arbitrary-depth letter reduction

In §1.1, after the general-level normalizer paragraph, insert:

> No normalization of the residue-unit part of \(\widehat n_i(m)\) is imposed at arbitrary depth. Consequently, exact height and bounded-exponent normal form alone do not imply that a value-zero quotient of tower normalizers is a monomial in the preceding canonical letters.
>
> If such a description is consumed at level \(i\ge2\), it must cite the following named supplier hypothesis:
>
> \[
> \boxed{
> \begin{minipage}{0.88\linewidth}
> \(\mathrm{(H\!-\!JA\!-\!CONJ)}_i\): the accepted JA conjugation formula supplies a specified Laurent monomial
> \[
> J_i(Z_1,\ldots,Z_i)
> \]
> such that
> \[
> \operatorname{res}\!\left(
> \frac{\widehat n_i(u_{i+1})}
> {\pi_{i+1}^{u_{i+1}}}
> \right)
> =
> J_i(z_1,\ldots,z_i).
> \]
> \end{minipage}
> }
> \tag{H-JA-CONJ}
> \]
>
> This is a site hypothesis imported from the JA supplier, not a consequence of the T1 carrier. The explicit level-two calculation below does not require it.

In (C1), replace

> The quotient has value zero. Successive reduction by the tower relations expresses \(\rho_i\) as a monomial in preceding canonical letters. This is a terminating reduction algorithm; no closed exponent formula is asserted at arbitrary depth.

with:

> The quotient has value zero. No arbitrary-depth canonical-letter monomial assertion follows from the T1 carrier. At a site carrying \(\mathrm{(H\!-\!JA\!-\!CONJ)}_i\), one may additionally conclude
> \[
> \boxed{\rho_i=J_i(z_1,\ldots,z_i).}
> \tag{C1-JA-specialization}
> \]
> The level-two formula below is unconditional and is proved directly from the displayed level-one normalizers.

In §2.1, replace the arbitrary-depth reduction paragraph beginning

> Both normalizers have height \(u_{i+1}\), so the quotient has value zero. Successively remove the highest key …

with:

> Both normalizers have height \(u_{i+1}\), so the quotient has value zero. This proves the unconditional content of (C1-general). The carrier supplies no control of the remaining residue-unit part. Formula (C1-JA-specialization), when used, is exactly the imported hypothesis \(\mathrm{(H\!-\!JA\!-\!CONJ)}_i\), not an additional conclusion of this proof.
>
> The following level-two computation is independent of that supplier hypothesis.

This defeats the unit-twist counter-configuration without enlarging T1.

## R2-2 — Make the harness/print polynomial comparison a named supplier fact

In (C4), replace the paragraph beginning

> If \(H(y)\) is the harness residual and \(P(y)\) the normalized print residual, the corresponding support statement is …

with:

> The attained-origin calculation above concerns one normalization exponent. It does not by itself compare all coefficients of a harness residual and a normalized print residual.
>
> A support comparison may be invoked only under the following named supplier hypothesis:
>
> \[
> \boxed{
> \begin{minipage}{0.88\linewidth}
> \(\mathrm{(H\!-\!JA\!-\!RES\!-\!CONJ)}\): for specified nonzero
> \(H,P,Q\in K[y]\), the accepted harness/print conjugation formula supplies
> \[
> H(y)=y^\nu Q(y),
> \qquad
> P(y)=aQ(by),
> \qquad
> a,b\in K^\times.
> \]
> \end{minipage}
> }
> \tag{H-JA-RES-CONJ}
> \]
>
> Under \(\mathrm{(H\!-\!JA\!-\!RES\!-\!CONJ)}\), multiplication by \(y^\nu\) translates exponent support, while multiplication by a unit and substitution by a unit preserve it. Hence
> \[
> \boxed{
> \operatorname{Supp}_y(H)
> =
> \nu+\operatorname{Supp}_y(P),
> \qquad
> \deg H=\deg P+\nu.
> }
> \tag{C4-support}
> \]
>
> Thus attained abscissas and normalized support widths agree at sites carrying the supplier comparison. Neither the polynomial identities nor their support consequences follow from (C4-origin) alone.

Replace the final paragraph of §2.4 with:

> This proves (C4-origin). The proof of (C4-origin) stops here.
>
> If \(\mathrm{(H\!-\!JA\!-\!RES\!-\!CONJ)}\) is cited, its two polynomial identities immediately give (C4-support). T1 does not derive those identities from the attained-origin exponent calculation.

## R2-3 — Type the evaluation point and its residue embedding

Immediately before (C6), insert:

> Fix a level-one tower point \(\theta\) together with the specified residue embedding
> \[
> \iota_\theta:K_1\hookrightarrow\kappa(\theta)
> \]
> satisfying
> \[
> \boxed{
> \operatorname{res}\!\left(
> \frac{\theta^{e_1}}{\pi^h}
> \right)
> =
> \iota_\theta(\eta).
> }
> \tag{C6-theta}
> \]
> Whenever \(K_1\) is identified with its image under \(\iota_\theta\), the symbol \(\iota_\theta(\lambda)\) may be written simply as \(\lambda\).

Replace (C6-residue) by:

\[
\boxed{
\operatorname{res}\!\left(
\frac{L_M(\lambda)(\theta)}
{n(M)(\theta)}
\right)
=
\iota_\theta(\lambda).
}
\tag{C6-residue}
\]

In §2.6, replace

> After division by \(n(M)\), its residue is \(\lambda_r\eta^r\). Basis independence prevents cancellation and proves (C6-residue).

with:

> After evaluation at \(\theta\) and division by \(n(M)(\theta)\), the \(r\)-th summand has residue
> \[
> \iota_\theta(\lambda_r)\,
> \operatorname{res}\!\left(
> \frac{\theta^{e_1}}{\pi^h}
> \right)^r
> =
> \iota_\theta(\lambda_r\eta^r).
> \]
> Summing and using the chosen \(K_1\)-basis gives
> \[
> \operatorname{res}\!\left(
> \frac{L_M(\lambda)(\theta)}
> {n(M)(\theta)}
> \right)
> =
> \iota_\theta(\lambda).
> \]
> Under the declared identification of \(K_1\) with its image, this is the accepted GENHN display with right-hand side \(\lambda\).

## R2-4 — Turn clearance into an explicit GENHN supplier interface

Replace (C6-clearance) and its following collection sentence with:

> The exact-lift theorem above contains no definition of \(\Phi'\), its monomial valuations, or the outer polygon side. Consequently it proves no clearance estimate by itself.
>
> At the composed GENHN application, clearance may be used only after citing:
>
> \[
> \boxed{
> \begin{minipage}{0.88\linewidth}
> \(\mathrm{(H\!-\!GENHN\!-\!CLEAR)}\): \(\Phi'\), the outer side, and the collection/\(\Phi'\)-carry operation are those of the accepted \(T(b)'(i)\) site. For
> \[
> r=f_2-t,\qquad M=ru_2,\qquad u_2>e_2D'h,
> \]
> that supplier proves that every product of a monomial of
> \[
> L_{ru_2}\!\bigl(c_t\eta^{W(t)}\bigr)
> \]
> with a monomial of \(\Phi'^{e_2t}\) clears the outer side by at least
> \[
> \frac{r(u_2-e_2D'h)}{e_1}>0,
> \]
> and that collection and \(\Phi'\)-carry can only cancel terms or move them upward.
> \end{minipage}
> }
> \tag{H-GENHN-CLEAR}
> \]
>
> Thus T1 supplies the exact-height coefficient used at that site; the outer-side estimate remains the named GENHN supplier fact.

Replace the last sentence of §2.6 with:

> Substitution of \(M=ru_2\) proves the corrected coefficient, its coherent digit, and its multiplicative coefficient. Any subsequent outer-side clearance assertion is an invocation of \(\mathrm{(H\!-\!GENHN\!-\!CLEAR)}\); it is not derived in T1.

The second A1 absorption row must consequently end:

> T1 absorbs the corrected coefficient and its exact-lift properties. The clearance sentence is retained only by the explicit citation \(\mathrm{(H\!-\!GENHN\!-\!CLEAR)}\), not as a T1 consequence.

## R2-5 — Type the modular-origin data

Replace the opening of (C4) by:

> Fix
> \[
> e\in\mathbf Z_{>0},
> \qquad
> \ell,\beta\in\mathbf Z,
> \qquad
> z\in K^\times.
> \]
> Let \(s_{\min}(\beta)\) be the unique representative in
> \(\{0,\ldots,e-1\}\) of the integer residue class
> \(\ell\beta\bmod e\), and put
> \[
> s_{\min}(\beta)
> =
> \operatorname{rem}_e(\ell\beta),
> \qquad
> t_{\min}(\beta)
> =
> \frac{\ell\beta-s_{\min}(\beta)}e
> \in\mathbf Z,
> \qquad
> \varepsilon(\beta)=z^{-t_{\min}(\beta)}.
> \]

The remaining attained-origin calculation is unchanged.

## Pin-enabling C5 corollary

After the definition of \(\varpi\), insert the directly derived identity

\[
\boxed{
\frac{n(k)}{\varpi^k}
=
\left(\frac{x^{e_1}}{\pi^h}\right)^{-q(k)}.
}
\tag{C5-monomial-ratio}
\]

In §2.5, derive it before taking residues:

\[
i(k)-i_0k=-e_1q(k),
\qquad
\frac{k-i(k)h}{e_1}
-
\frac{k-i_0kh}{e_1}
=
hq(k).
\]

This adds no hypothesis and makes the HETOW ratio pin a literal specialization.

# Replacement §3 — Exact-span absorption map

Replace the introductory paragraphs of §3 with:

> Under the revised blueprint’s non-row-annex provision, an A-row absorbs only the closed sub-display quoted in that row. A theorem or lemma identifier is a span locator; it does not mean that T1 implies the entire containing statement.
>
> Each row must have the form
> \[
> \text{specified T1 clause}
> \Longrightarrow
> \text{quoted pinned subclaim}.
> \]
> If the containing result needs geometry, routing, membership, extraction, or a site theorem not supplied by T1, the row is labeled “supplies the gauge input to,” and the residual obligation is named explicitly.

## A2 — HETOW

**SPAN PIN.** Accepted file `HETOW`, LEMMA HETOW-4, `md5=2500c2f458b6647e9bedeee8c84009a0`, parts (a)–(b):

\[
\boxed{
\frac{\widehat n_2(k)}{n_2(k)}
=
\frac{\widehat n(m(k))}{\varpi^{m(k)}}
=
\left(\frac{x^{e_1}}{\pi^h}\right)^{-Q(m(k))}
}
\]

and

\[
\boxed{
\operatorname{res}\!\left(
\frac{\widehat n_2(k)(\xi)}{n_2(k)(\xi)}
\right)
=
\eta_\xi^{-Q(m(k))}
=
\iota_\xi\!\left(\eta^{-Q(m(k))}\right).
}
\]

With \(w_2=\lfloor(s(k)+s(k'))/e_2\rfloor\), the pinned carry display is

\[
\boxed{
\frac{\tau(k)\tau(k')}{\tau(k+k')}
=
\eta^{
\operatorname{wrap}_1(m(k),m(k'))
+
w_2\left(
Q(u_2)+
\operatorname{wrap}_1(m(k)+m(k'),u_2)
\right)
}.
}
\]

**Consumption check.**

\[
\boxed{
\text{T1 (C5-monomial-ratio) + (C5-carry)}
\Longrightarrow
\text{the three pinned HETOW displays}.
}
\]

**Scope.** T1 does not absorb HETOW-4(c)–(d). The side-assembly brackets, telescoping coefficient identity, side-letter equality, routing transport, and common refinement polynomial remain HETOW/HE7 supplier conclusions.

## A3 — GENTOW1

**SPAN PIN.** Accepted file `GENTOW1`, the gauge-correction display attached to the level-one coefficient pin preceding LEMMA GENTOW-1 (`md5=4b4d9f21dae75e08d515ff8a7263b559`):

\[
\boxed{
M_t=(f_2-t)u_2>D'h,
\qquad
\gamma_t=c_t\eta^{W(t)},
\qquad
\widehat k_t=L_{M_t}(\gamma_t),
}
\]

with the closed read statement

\[
\boxed{
dv_1(\widehat k_t)=M_t,
\qquad
c_t^{\mathrm{mult}}
=
\gamma_t\eta^{-W(t)}
=
c_t.
}
\]

Here the accepted local \(\gamma_t\) is T1’s coherent digit \(\Gamma_t\), not HE6’s \(\gamma_k(A)\).

**Consumption check.**

\[
\boxed{
\text{T1 (C2-level-1) + (C3-dictionary) + (C6)}
\Longrightarrow
\text{the pinned corrected-coefficient display}.
}
\]

**Classification.** T1 **supplies the gauge input to** LEMMA GENTOW-1.

**Residual obligation.** The characterization of \(\mathcal T\), budget floors, triangular-unimodular fibration, digit counts, sharp node bounds, class separation, and the field-root inequality in GENTOW-1(a)–(d) remain GENTOW1/GENHN-2′/HE6 supplier results. Equal exact height only says that an already-established value-blind budget is unchanged by the gauge correction.

## A4 — GENTOW3

**SPAN PIN.** Accepted file `GENTOW3`, gauge-annex corrected-key and \(x\)-free-rescope displays associated with THEOREM GENTOW-3 (`md5=a6d97dfefeb2be042cada0d9ca46c31e`):

\[
\boxed{
M_t=(f_2-t)u_2>D'h,
\qquad
\widehat k_t
=
L_{M_t}\!\bigl(c_t\eta^{W(t)}\bigr),
}
\]

and, for a nonzero digit \(\lambda\),

\[
\boxed{
L_M(\lambda)\text{ is an \(x\)-free monomial}
\iff
i(M)=0
\text{ and }
\lambda\in\mathbf F_Q.
}
\]

**Consumption check.**

\[
\boxed{
\text{T1 (C3-level-1-key) + (C6-x-free)}
\Longrightarrow
\text{the two pinned GENTOW3 gauge displays}.
}
\]

**Classification.** T1 **supplies the corrected-key and \(x\)-free inputs to** THEOREM GENTOW-3.

**Residual obligation.** The definitions and comparison of \(ShC_j\) and \(C_j\), the \(\Theta_j\) floor, faithful-band equality, zero-discrepancy theorem, self-overflow certificate, attainment, and deep-perturbation conclusions remain GENTOW3 results.

## A5 — GENTOW4

**SPAN PIN.** Accepted file `GENTOW4`, S3 corrected-key bridge attached to LEMMA GENTOW-4.1 (`md5=d7d1bf2b130424408025b37187067507`):

\[
\boxed{
\Phi_2
=
\Phi'^{\,e_2f_2}
-
\sum_{t<f_2}
L_{(f_2-t)u_2}
\!\bigl(c_t\eta^{W(t)}\bigr)
\Phi'^{\,e_2t},
}
\]

on the displayed live domain \((f_2-t)u_2>D'h\).

The separately pinned attained-origin equation is

\[
\boxed{
z^{t_{\mathrm{Def}}}
=
z^\nu\varepsilon(\beta).
}
\]

Any support comparison additionally cites \(\mathrm{(H\!-\!JA\!-\!RES\!-\!CONJ)}\).

**Consumption checks.**

\[
\boxed{
\text{T1 (C2-level-1) + (C3-level-1-key) + (C6)}
\Longrightarrow
\text{the pinned corrected-key display},
}
\]

\[
\boxed{
\text{T1 (C4-origin)}
\Longrightarrow
z^{t_{\mathrm{Def}}}=z^\nu\varepsilon(\beta).
}
\]

**Classification.** T1 **supplies the gauge input to** GENTOW-4.1(c)/S3.

**Residual obligation.** The all-sides slope bound, nonzero residual constants, level-2 point-set identification, \(\Psi\)-membership, the HE7 routing/refinement package, both frame peels, and their splitting contributions remain GENTOW4/HETOW/HE7 supplier conclusions. In particular, T1 does not imply

\[
\Phi_2=\Psi_{\kappa_2,\widetilde r}-w,
\qquad
w=0\ \text{or}\ dv_2(w)>T_2.
\]

## A6 — GENTOW6

**SPAN PIN.** Accepted file `GENTOW6`, normalized scalar-read display used by THEOREM GENTOW-6.3 (`md5=05fc38817b8c75297267bb57089e898f`):

\[
\boxed{
\gamma_k(A)
=
\sum_{\substack{t\ge0\\i(k)+e_1t<D'}}
\operatorname{res}\!\left(
a_{i(k)+e_1t}
\pi^{-(k-(i(k)+e_1t)h)/e_1}
\right)\eta^t,
}
\]

\[
\boxed{
\operatorname{res}\!\left(
\frac{A(\xi)}{n(k)(\xi)}
\right)
=
\iota_\xi\bigl(\gamma_k(A)\bigr),
\qquad
\operatorname{res}\!\left(
\frac{A(\xi)}{\varpi(\xi)^k}
\right)
=
\iota_\xi\bigl(\gamma_k(A)\bigr)\eta_\xi^{-q(k)}.
}
\]

The associated lift pin is

\[
\boxed{
L_M(\lambda)
=
\sum_{r=0}^{f_1-1}
\widetilde{\lambda_r}
x^{i(M)+e_1r}\pi^{a-rh},
\qquad
M>D'h,
}
\]

with its full displayed support and exact height.

**Consumption check.**

\[
\boxed{
\text{T1 (C5-gamma) + (C5-normalizer-read)
+ (C5-varpi-read) + (C6-lift)}
\Longrightarrow
\text{the pinned GENTOW6 scalar-read and lift displays}.
}
\]

**Classification.** T1 **supplies the normalized scalar-read and exact-lift inputs to** THEOREM GENTOW-6.3.

**Residual obligation.** The \(f_1=1\) scope, shadow/composed grids, single-\(\Phi'\)-extraction census, unique top branch, noncancellation certificate, no-overflow equality, regime-3 witness, and attainment statements remain GENTOW6 results. No part of GENTOW-6.3(a)–(d) is absorbed merely from C5–C6.

## A7 — GENTOW2

**SPAN PIN 1.** Accepted file `GENTOW2`, S5.1 level-two letter display:

\[
\boxed{
z_2
=
\eta_2z_1^{-\lfloor\ell_1u_2/e_1\rfloor}.
}
\]

**Consumption check.**

\[
\boxed{
\text{T1 (C1-base-letter) + (C1-level-2)}
\Longrightarrow
\text{the pinned S5.1 letter display}.
}
\]

**SPAN PIN 2.** LEMMA GENTOW2-B, `md5=8a00bf44d21f87e878c0be6226b13b61`, terminal rescaling display:

\[
\boxed{
\psi_3^{(w)}(y)
=
w^{f_3}\psi_3(y/w).
}
\]

The pinned consequences are: monicity after the displayed renormalization, preservation of degree and irreducibility, preservation of a nonzero constant term, and preservation of irreducible-factor degrees and multiplicities.

**Consumption check.**

\[
\boxed{
\text{T1 (C3-three-reads) and its unit-substitution argument}
\Longrightarrow
\text{the pinned rescaling and factor-pattern subclaim}.
}
\]

**B-law classification.** T1 only **supplies the gauge algebra to** the preceding B-law display. The residual obligation is the accepted GENTOW2-B″ per-grade-unit theorem discharging ladder multiplicativity and the value-zero read:

\[
u(\beta_t)
=
\Theta(t)w^{f_3-t}.
\]

T1 may then perform the slotwise cancellation

\[
\Gamma_t=c_t\vartheta_{f_3-t},
\qquad
\Theta(t)=\vartheta_{f_3-t}^{-1},
\]

but it does not prove the supplier identity itself. Thus the B-law is no longer labeled “absorbed verbatim.”

# Consequential scope edits

Replace honesty-ledger items 1, 5, and 10 by:

> 1. At arbitrary depth, T1 proves only the value-zero ratio in (C1-general). A preceding-letter monomial description requires the named supplier hypothesis \(\mathrm{(H\!-\!JA\!-\!CONJ)}_i\). The level-two formula is proved directly and is unconditional.

> 5. The canonical minimal-grid factor and raw print factor differ by \(z^\nu\). The exponent identity (C4-origin) does not imply a comparison of whole residual polynomials. The support and degree formulas require \(\mathrm{(H\!-\!JA\!-\!RES\!-\!CONJ)}\).

> 10. T1 does not prove note-specific budgets, floors, fullness counts, separator inequalities, polygon geometry, or extraction and attainment claims. In particular, outer-side clearance is available only through the named supplier input \(\mathrm{(H\!-\!GENHN\!-\!CLEAR)}\).

In (C7), amend the affected package rows to read:

| Package field | T1 datum available to that field |
|---|---|
| \(M1\) | The unconditional value-zero ratio and level-two letter formula in (C1); arbitrary-depth letter monomiality only under \(\mathrm{(H\!-\!JA\!-\!CONJ)}_i\). |
| \(M2\) | The dictionary and canonical read in (C3), plus (C4-origin); support transport only under \(\mathrm{(H\!-\!JA\!-\!RES\!-\!CONJ)}\). |
| \(M4\) | The exact-height formulas (C5)–(C6), at W2-C3’s accepted fence; polygon clearance only under \(\mathrm{(H\!-\!GENHN\!-\!CLEAR)}\). |

Add to §6:

> | Removed the unsupported arbitrary-depth unit reduction; made harness/print polynomial conjugation and GENHN clearance explicit supplier inputs; typed the modular-origin data; fixed the \(C6\) evaluation embedding; and re-scoped A2–A7 to closed gauge spans with named residual obligations. | T1P and T1CC2, 2026-08-12 r2 | Repairs 1 CRITICAL, 3 GAP, and 1 MINOR finding; prevents theorem-wide absorption from gauge-input rows. |


---

## r3 (2026-08-12): arc repairs

*(Derived by gpt-5.6-sol high, runs/comp2/T1R3_output.log; transcribed unaltered; counter resets.)*

# T1 r3 corrections — 2026-08-12

These edits repair the three gaps and one minor found by T1P2.

## R3-1 — Type the general canonical letter

In §1.1, immediately after the general-level stage data

\[
e_{i+1},\qquad f_{i+1},\qquad u_{i+1},
\]

insert:

> Fix also the stage element \(\pi_{i+1}\) with
> \[
> \boxed{dv_i(\pi_{i+1})=1.}
> \tag{C1-stage-uniformizer}
> \]
> Hence
> \[
> dv_i\!\left(\pi_{i+1}^{u_{i+1}}\right)=u_{i+1}.
> \]
> At level \(1\), this condition follows from
> \[
> \pi_2=x^{\ell_1}\pi^{\ell'_1},
> \qquad
> \ell_1h+\ell'_1e_1=1.
> \]

In §2.1, replace

> Both normalizers have height \(u_{i+1}\), so the quotient has value zero.

with:

> By exact height,
> \[
> dv_i\!\left(\widehat n_i(u_{i+1})\right)=u_{i+1},
> \]
> while (C1-stage-uniformizer) gives
> \[
> dv_i\!\left(\pi_{i+1}^{u_{i+1}}\right)=u_{i+1}.
> \]
> Hence their quotient has value zero.

## R3-2 — Type the C5 residue embedding

In (C5), replace

> Let
> \[
> A(x)=\sum_{j<D'}a_jx^j,
> \qquad
> k=dv(A),
> \qquad
> i=i(k),
> \qquad
> n(k)=x^i\pi^{(k-ih)/e_1}.
> \]

with:

> Let
> \[
> 0\ne A(x)=\sum_{j<D'}a_jx^j,
> \qquad
> k=dv(A),
> \qquad
> i=i(k),
> \qquad
> n(k)=x^i\pi^{(k-ih)/e_1}.
> \]

Replace

> For every tower point \(\xi\) carrying the specified residue embedding \(\iota_\xi\),

with:

> For every level-one tower point \(\xi\), fix the specified residue embedding
> \[
> \iota_\xi:K_1\hookrightarrow\kappa(\xi)
> \]
> satisfying
> \[
> \boxed{
> \operatorname{res}\!\left(
> \frac{\xi^{e_1}}{\pi^h}
> \right)
> =
> \iota_\xi(\eta).
> }
> \tag{C5-xi}
> \]
> Write
> \[
> \eta_\xi
> :=
> \operatorname{res}\!\left(
> \frac{\xi^{e_1}}{\pi^h}
> \right)
> =
> \iota_\xi(\eta).
> \]
> Then

In §2.5, after

\[
\frac{a_j\xi^j}{n(k)(\xi)}
=
\left(
a_j\pi^{-(k-jh)/e_1}
\right)
\left(
\xi^{e_1}\pi^{-h}
\right)^t,
\]

insert:

> By (C5-xi), the residue of the second factor is
> \[
> \eta_\xi^t=\iota_\xi(\eta^t).
> \]

## R3-3 — Remove the unsupported character-torsor classification

In (C7), replace

> It also proves no uniqueness of the gauge. Gauges with a fixed coboundary may differ by a character.

with:

> It also proves no uniqueness of the gauge and makes no classification of the fiber of gauges having a fixed coboundary. Any torsor or character description requires separately stated coefficient actions, admissibility conditions, and a supplier theorem.

Replace honesty-ledger item 12 with:

> 12. Gauge uniqueness is not asserted. T1 defines no gauge space, coefficient action, or character group and therefore asserts no character-torsor classification of fixed-coboundary gauges.

In §6, replace the row beginning

> | Withdrew any gauge-uniqueness implication and recorded character-torsor ambiguity.

with:

> | Withdrew any gauge-uniqueness implication and made no classification of fixed-coboundary gauge fibers. | WELDMASTER C6 F-1/F-2 and T1P2 finding G3 | Scope correction across all annex consumers; formulas C1–C6 are unchanged. |

## R3-4 — Record this repair pass

Add to §6:

> | Required \(dv_i(\pi_{i+1})=1\) at general depth; required \(A\ne0\) and a compatible C5 residue embedding; and removed the untyped character-torsor assertion. | T1P2, 2026-08-12 r3 | Repairs 3 GAP and 1 MINOR findings without strengthening the mathematical conclusions. |


---

## r4 (2026-08-12): arc repairs

*(gpt-5.6-sol high, runs/comp4/T1R4_output.log; transcribed unaltered; counter resets.)*

# T1 r4 corrections — 2026-08-12

These edits repair the two gaps and one instrumentation minor found by T1P3.

## R4-1 — Type the general-stage key height

In §1.1, immediately after (C1-stage-uniformizer), insert:

> Fix also the stage key \(\Phi_i\) with the stage-height identity
> \[
> \boxed{
> dv_i\!\left(\Phi_i^{e_{i+1}}\right)
> =
> u_{i+1}.
> }
> \tag{C1-stage-key-height}
> \]
> Consequently, for every \(s\in\mathbf Z_{\ge0}\),
> \[
> dv_i\!\left(\Phi_i^{e_{i+1}s}\right)
> =
> su_{i+1}.
> \]
> This identity is part of the typed stage data. It is used both in the definitions of the residue letters and in the equal-height composed-key calculation.

Immediately after the definitions of \(\eta_{i+1}\) and \(z_{i+1}\), insert:

> By exact height, (C1-stage-uniformizer), and
> (C1-stage-key-height),
> \[
> \begin{aligned}
> dv_i\!\left(\Phi_i^{e_{i+1}}\right)
> &=
> dv_i\!\left(\widehat n_i(u_{i+1})\right)\\
> &=
> dv_i\!\left(\pi_{i+1}^{u_{i+1}}\right)
> =
> u_{i+1}.
> \end{aligned}
> \]
> Hence both displayed quotients defining
> \(\eta_{i+1}\) and \(z_{i+1}\) have value zero, so both residue letters are typed.

In §2.1, replace the opening argument through the sentence preceding the level-two computation with:

> By (C1-stage-key-height),
> \[
> dv_i\!\left(\Phi_i^{e_{i+1}}\right)
> =
> u_{i+1}.
> \]
> Exact height and (C1-stage-uniformizer) give
> \[
> dv_i\!\left(\widehat n_i(u_{i+1})\right)
> =
> dv_i\!\left(\pi_{i+1}^{u_{i+1}}\right)
> =
> u_{i+1}.
> \]
> Thus both defining fractions for
> \(\eta_{i+1}\) and \(z_{i+1}\), as well as
> \[
> \frac{\widehat n_i(u_{i+1})}
> {\pi_{i+1}^{u_{i+1}}},
> \]
> have value zero. Multiplicativity of residue on these value-zero factors gives
> \[
> z_{i+1}
> =
> \eta_{i+1}
> \operatorname{res}\!\left(
> \frac{\widehat n_i(u_{i+1})}
> {\pi_{i+1}^{u_{i+1}}}
> \right),
> \]
> proving the unconditional content of (C1-general).
>
> The carrier supplies no control of the remaining residue-unit part. Formula (C1-JA-specialization), when used, is exactly the imported hypothesis
> \(\mathrm{(H\!-\!JA\!-\!CONJ)}_i\), not an additional conclusion of this proof.
>
> The following level-two computation is independent of that supplier hypothesis.

Immediately after (C3-corrected-lift), insert:

> Put \(s=f_{i+1}-t\). If \(c_t\ne0\), then
> \(\vartheta_{i,s}\in K_i^\times\) implies
> \(c_t\vartheta_{i,s}\ne0\), and the exact-height lift contract gives
> \[
> dv_i(\widehat k_t)=su_{i+1}.
> \]
> By (C1-stage-key-height),
> \[
> dv_i\!\left(\Phi_i^{e_{i+1}t}\right)
> =
> tu_{i+1}.
> \]
> Therefore every nonzero lower term has height
> \[
> \boxed{
> dv_i\!\left(
> \widehat k_t\Phi_i^{e_{i+1}t}
> \right)
> =
> (s+t)u_{i+1}
> =
> f_{i+1}u_{i+1}.
> }
> \tag{C3-common-height}
> \]
> The leading term has the same height:
> \[
> dv_i\!\left(
> \Phi_i^{e_{i+1}f_{i+1}}
> \right)
> =
> f_{i+1}u_{i+1}.
> \]
> If \(c_t=0\), then \(\widehat k_t=0\) by the zero-lift convention and the corresponding lower term is absent; no finite exact height is assigned to that zero term.

In §2.3, replace

> Choosing
> \[
> \Gamma_t=c_t\vartheta_{i,f-t}
> \]
> therefore makes the multiplicative coefficient exactly \(c_t\), proving the corrected-key and degeneracy claims.

with:

> Choosing
> \[
> \Gamma_t=c_t\vartheta_{i,f-t}
> \]
> makes the multiplicative coefficient exactly \(c_t\). If
> \(c_t\ne0\), the lift has exact height \((f-t)u\), and
> (C1-stage-key-height) makes its product with
> \(\Phi_i^{e_{i+1}t}\) a term of height \(fu\). If
> \(c_t=0\), the lift and the corresponding key term are zero, and their coherent and multiplicative reads are both zero. Thus all nonzero terms participating in the residual-key calculation have the common height asserted in (C3-common-height).

## R4-2 — Separate the nonzero exact-height lift contract from the zero lift

In §1.1, replace the general lift contract

> Whenever an exact-height lift is invoked, assume it lies in its stated integral domain and satisfies
> \[
> dv_i(\operatorname{lift}_i(d;m))=m,
> \qquad
> \operatorname{res}\!\left(
> \frac{\operatorname{lift}_i(d;m)}{\widehat n_i(m)}
> \right)=d.
> \]
>
> Zero is lifted as zero.

with:

> Whenever a lift is invoked, assume that \(m\) lies in its stated integral domain and that
> \[
> \boxed{
> \operatorname{res}\!\left(
> \frac{\operatorname{lift}_i(d;m)}
> {\widehat n_i(m)}
> \right)
> =
> d
> \qquad(d\in K_i).
> }
> \tag{C3-lift-residue}
> \]
> Exact height is asserted only for a nonzero digit:
> \[
> \boxed{
> dv_i\!\left(\operatorname{lift}_i(d;m)\right)
> =
> m
> \qquad(d\in K_i^\times).
> }
> \tag{C3-lift-height}
> \]
> The zero convention is
> \[
> \boxed{
> \operatorname{lift}_i(0;m)=0,
> \qquad
> dv_i(0)=+\infty.
> }
> \tag{C3-zero-lift}
> \]
> Thus the residue identity remains valid at \(d=0\), but no finite exact-height assertion is made for the zero lift. At level \(1\), conclusion (C6) supplies this contract uniformly when \(m>D'h\).

This replacement, together with the zero branch in (C3-common-height), permits vanishing \(c_t\) without assigning finite valuation to zero.

## R4-3 — Make the weld-scope lint exclude its own specification

Replace required revision check 6 with:

> 6. **Weld scope lint.** Build the lint target from assertion-bearing T1 prose after excluding this numbered check, quoted rejected formulations, and matches lying within the scope of an explicit negation. On that target, fail on either literal-pattern regex
>    \[
>    \texttt{\textbackslash bone\textbackslash s+transport\textbackslash s+map\textbackslash b}
>    \qquad\text{or}\qquad
>    \texttt{\textbackslash bunique\textbackslash s+gauge\textbackslash b}.
>    \]
>    Also fail on an affirmative assertion that distinct \(M0\)–\(M4\) fields satisfy a compatibility relation without a named displayed package anchor. Occurrences inside this lint specification, quotations of rejected language, and explicit scope-fence negations are nonmatches. Confirm independently that every \(M3\) use retains the scored-stratum fence and every \(M4\) use retains the accepted W2-C3 fence.

This preserves the intended scope check while preventing its pattern specification from triggering the document lint.

## Consequential record edits

Append to the honesty ledger:

> 15. The general residue letters and the common-height composed-key calculation use the explicit stage identity
> \[
> dv_i\!\left(\Phi_i^{e_{i+1}}\right)=u_{i+1}.
> \]
> Exact lift height is asserted only for nonzero digits. A zero digit is lifted to zero, has residue zero after normalization, and contributes no finite-height key term.

Add to §6:

> | Added the general stage-key height identity; separated the nonzero exact-height lift contract from the zero-lift convention; and made the weld lint exclude its own specification, quotations, and negated scope fences. | T1P3, 2026-08-12 r4 | Repairs 2 GAP and 1 MINOR findings and types the letter residues, composed-key heights, and vanishing-coefficient branch. |


---

## r5 (2026-08-12): arc repairs

*(gpt-5.6-sol high, runs/comp5/T1R5_output.log; transcribed unaltered; counter resets.)*

# T1 r5 corrections — 2026-08-12

These edits repair the two proof/scope gaps and one editorial minor found by T1P5.

## R5-1 — State the graded scalar-covariance convention used by C3

In §1.1, replace:

> Assume at the consumed sites that the canonical residual read is multiplicative on the relevant ladder monomials and agrees with residue on value-zero factors. This is a site obligation, not an assertion about every homogeneous initial form.

with:

> At each consumed B-law site, assume the following graded read convention on the displayed ladder elements. If
> \[
> N=\widehat n_i(u_{i+1}),
> \qquad
> M_s=\widehat n_i(su_{i+1}),
> \qquad
> \bar\kappa_i=\frac{u_{i+1}}{e(\mu_i)},
> \]
> then
> \[
> \boxed{
> R_{i+1,s\bar\kappa_i}(N^s)
> =
> R_{i+1,\bar\kappa_i}(N)^s
> }
> \tag{C3-ladder-multiplicativity}
> \]
> for every ladder exponent \(s\) used at that site.
>
> Assume also graded scalar covariance: if \(X\) is one of the consumed homogeneous ladder elements of grade \(\beta\), and \(g\) is a value-zero factor for which \(Xg\) is defined in the same homogeneous slot, then
> \[
> \boxed{
> R_{i+1,\beta}(Xg)
> =
> R_{i+1,\beta}(X)\operatorname{res}(g).
> }
> \tag{C3-graded-scalar-covariance}
> \]
> In grade zero the read agrees with residue on the consumed value-zero factors. These are site obligations, or may be discharged by a named per-grade residual-read supplier; they are not assertions about every homogeneous initial form.

In (C3), replace:

> Let \(\beta_t\) be the slot grade and set
> \[
> u(\beta_t)
> =
> R_{i+1,\beta_t}
> \bigl(
> \widehat n_i((f_{i+1}-t)u_{i+1})
> \bigr).
> \]

with:

> Put
> \[
> s=f_{i+1}-t
> \]
> and define the slot grade by
> \[
> \boxed{
> \beta_t
> :=
> s\bar\kappa_i
> =
> (f_{i+1}-t)\bar\kappa_i.
> }
> \tag{C3-slot-grade}
> \]
> Set
> \[
> u(\beta_t)
> =
> R_{i+1,\beta_t}
> \bigl(
> \widehat n_i(su_{i+1})
> \bigr).
> \]

Replace:

> At every site where the stated ladder-multiplicativity obligation is discharged,

with:

> At every site where (C3-ladder-multiplicativity) and
> (C3-graded-scalar-covariance) are discharged,

In §2.3, replace the B-law argument beginning

> At a consumed site, ladder multiplicativity and the value-zero rule give

and ending

> Multiplying by a coherent digit proves (C3-canonical-read).

with:

> At a consumed site, put
> \[
> N=\widehat n_i(u),
> \qquad
> M_s=\widehat n_i(su),
> \qquad
> \beta_t=s\bar\kappa_i.
> \]
> By (C3-ladder-multiplicativity),
> \[
> R_{i+1,\beta_t}(N^s)
> =
> R_{i+1,\bar\kappa_i}(N)^s
> =
> w_i^s.
> \]
> Since
> \[
> N^s
> =
> M_s\left(\frac{N^s}{M_s}\right)
> \]
> and \(N^s/M_s\) has value zero, graded scalar covariance gives
> \[
> \begin{aligned}
> w_i^s
> &=
> R_{i+1,\beta_t}(N^s)\\
> &=
> R_{i+1,\beta_t}(M_s)
> \operatorname{res}\!\left(\frac{N^s}{M_s}\right)\\
> &=
> R_{i+1,\beta_t}(M_s)\vartheta_{i,s}.
> \end{aligned}
> \]
> Hence
> \[
> R_{i+1,\beta_t}(M_s)
> =
> w_i^s\vartheta_{i,s}^{-1}
> =
> w_i^s\Theta_i(t),
> \]
> which proves (C3-B-law).
>
> A slot with coherent digit \(\Gamma_t\) is represented, at the consumed read site, as
> \[
> M_sg_t,
> \qquad
> dv_i(g_t)=0,
> \qquad
> \operatorname{res}(g_t)=\Gamma_t.
> \]
> A second application of (C3-graded-scalar-covariance) gives
> \[
> \begin{aligned}
> R_{i+1,\beta_t}(M_sg_t)
> &=
> R_{i+1,\beta_t}(M_s)\Gamma_t\\
> &=
> w_i^s\Theta_i(t)\Gamma_t,
> \end{aligned}
> \]
> proving (C3-canonical-read).

In the supporting-context paragraph following the absorption map, replace:

> The B-law rows consume only ladder-monomial multiplicativity and the value-zero digit read at their stated sites.

with:

> The B-law rows consume (C3-ladder-multiplicativity), the grade identity
> \(\beta_t=(f_{i+1}-t)\bar\kappa_i\), and
> (C3-graded-scalar-covariance) for the displayed value-zero factors at their stated sites.

Replace honesty-ledger item 2 with:

> 2. The B-law is conditional on the sitewise graded read facts (C3-ladder-multiplicativity), (C3-slot-grade), and (C3-graded-scalar-covariance). Agreement with residue on isolated value-zero factors is not used as a substitute for scalar covariance, and T1 asserts no multiplicativity theorem for all homogeneous initial forms.

In the A7 B-law residual obligation, replace:

> the accepted GENTOW2-B″ per-grade-unit theorem discharging ladder multiplicativity and the value-zero read

with:

> the accepted GENTOW2-B″ per-grade-unit theorem discharging the slot-grade identity, ladder multiplicativity, and graded scalar covariance for the consumed value-zero factors

## R5-2 — Restore the missing HETOW supplier structure in A2

Immediately before the A2 consumption check, insert:

> **Local supplier interface.** The following data are not defined or proved by C5 and remain part of the accepted HETOW site:
> \[
> \boxed{
> \begin{minipage}{0.88\linewidth}
> \(\mathrm{(H\!-\!HETOW\!-\!LOCAL)}\): the accepted HETOW construction supplies
> \[
> \widehat n_2(k),\quad n_2(k),\quad m(k),\quad Q,\quad
> \tau(k),\quad s(k),\quad w_2,
> \]
> identifies its level-one normalizer and carry function with the C5 objects on the relevant heights,
> \[
> \widehat n(m)=n(m),
> \qquad
> Q(m)=q(m),
> \]
> and proves the local bridge and second-level carry relations
> \[
> \frac{\widehat n_2(k)}{n_2(k)}
> =
> \frac{\widehat n(m(k))}{\varpi^{m(k)}},
> \]
> \[
> w_2
> =
> \left\lfloor
> \frac{s(k)+s(k')}{e_2}
> \right\rfloor,
> \qquad
> m(k+k')
> =
> m(k)+m(k')+w_2u_2.
> \]
> It also identifies the local scalar \(\tau(k)\) with the residue of the displayed normalizer ratio:
> \[
> \tau(k)
> =
> \eta^{-Q(m(k))}.
> \]
> These identities are HETOW structure, not consequences of T1.
> \end{minipage}
> }
> \tag{H-HETOW-LOCAL}
> \]

Replace the A2 consumption check

> \[
> \boxed{
> \text{T1 (C5-monomial-ratio) + (C5-carry)}
> \Longrightarrow
> \text{the three pinned HETOW displays}.
> }
> \]

with:

> \[
> \boxed{
> \mathrm{(H\!-\!HETOW\!-\!LOCAL)}
> +
> \text{T1 (C5-monomial-ratio) + (C5-carry)}
> \Longrightarrow
> \text{the three pinned HETOW displays}.
> }
> \]
>
> Indeed, the supplier bridge followed by (C5-monomial-ratio) gives
> \[
> \frac{\widehat n_2(k)}{n_2(k)}
> =
> \frac{\widehat n(m(k))}{\varpi^{m(k)}}
> =
> \left(\frac{x^{e_1}}{\pi^h}\right)^{-Q(m(k))},
> \]
> and taking residues gives the second pinned display. For the third, write
> \[
> m=m(k),
> \qquad
> m'=m(k').
> \]
> The supplier relation
> \[
> m(k+k')=m+m'+w_2u_2
> \]
> and two applications of (C5-carry) give
> \[
> \begin{aligned}
> Q(m(k+k'))-Q(m)-Q(m')
> &=
> \operatorname{wrap}_1(m,m')\\
> &\quad+
> w_2\left(
> Q(u_2)+
> \operatorname{wrap}_1(m+m',u_2)
> \right).
> \end{aligned}
> \]
> Substitution of
> \(\tau(k)=\eta^{-Q(m(k))}\) proves the pinned \(\tau\)-ratio.
>
> Thus T1 supplies only the level-one monomial-ratio and \(q\)-carry algebra. The bridge from level \(2\), the function \(m\), the second-level carry \(w_2\), and the identification of \(\tau\) remain explicitly imported HETOW facts.

## R5-3 — Reattach the level-one basis sentence

In the integrated application of R1-1, replace the detached text

> and chosen basis \(1,\eta,\ldots,\eta^{f_1-1}\).

with:

> Fix also the chosen \(\mathbf F_Q\)-basis
> \[
> 1,\eta,\ldots,\eta^{f_1-1}
> \]
> of \(K_1\).

Equivalently, the base-letter paragraph may be placed after the original complete sentence ending with the basis datum. No mathematical content changes.

## Consequential record edit

Add to §6:

> | Stated the graded scalar-covariance and slot-grade conventions used by the C3 ladder reads; imported the missing level-two bridge and carry structure through \(\mathrm{(H\!-\!HETOW\!-\!LOCAL)}\); and reattached the level-one basis sentence. | T1P5, 2026-08-12 r5 | Repairs 2 GAP and 1 MINOR findings without promoting either the sitewise residual-read law or the local HETOW construction to an unconditional T1 theorem. |


---

## r6 (2026-08-12): arc repairs

*(gpt-5.6-sol high, runs/comp8/T1R6_output.log; transcribed unaltered; counter resets.)*

# T1 r6 corrections — 2026-08-12

These edits repair the two absorption-scope gaps found by T1P7.

## R6-1 — Propagate the zero-lift branch into the A3 and A6 pins

In the replacement §3 absorption map, under **A3 — GENTOW1**, replace the closed read statement

\[
\boxed{
dv_1(\widehat k_t)=M_t,
\qquad
c_t^{\mathrm{mult}}
=
\gamma_t\eta^{-W(t)}
=
c_t.
}
\]

with:

> The valuation statement is conditional on the coefficient being nonzero:
> \[
> \boxed{
> \begin{aligned}
> c_t\ne0
> &\Longrightarrow
> dv_1(\widehat k_t)=M_t,\\
> c_t=0
> &\Longrightarrow
> \gamma_t=0,\quad
> \widehat k_t=L_{M_t}(0)=0,\quad
> dv_1(\widehat k_t)=+\infty.
> \end{aligned}
> }
> \]
> In both branches, the multiplicative coefficient identity remains
> \[
> \boxed{
> c_t^{\mathrm{mult}}
> =
> \gamma_t\eta^{-W(t)}
> =
> c_t.
> }
> \]

Replace the A3 consumption check

\[
\boxed{
\text{T1 (C2-level-1) + (C3-dictionary) + (C6)}
\Longrightarrow
\text{the pinned corrected-coefficient display}.
}
\]

with:

\[
\boxed{
\text{T1 (C2-level-1) + (C3-dictionary)
+ (C3-zero-lift) + (C6)}
\Longrightarrow
\text{the re-scoped pinned corrected-coefficient display}.
}
\]

Immediately after that display, insert:

> Exact height is consumed only on the nonzero-coefficient branch. A vanishing coefficient produces an absent key term and is governed by
> \[
> \operatorname{lift}_1(0;M_t)=0,
> \qquad
> dv_1(0)=+\infty.
> \]

Under **A6 — GENTOW6**, replace:

> with its full displayed support and exact height.

with:

> Its actual \(x\)-support is
> \[
> \boxed{
> \operatorname{Supp}_x L_M(\lambda)
> =
> \left\{
> i(M)+e_1r:
> 0\le r<f_1,\ \lambda_r\ne0
> \right\}.
> }
> \]
> Every present summand has exact height \(M\). If
> \(\lambda\ne0\), then
> \[
> dv_1\!\left(L_M(\lambda)\right)=M.
> \]
> If \(\lambda=0\), then
> \[
> L_M(0)=0,\qquad
> \operatorname{Supp}_xL_M(0)=\varnothing,\qquad
> dv_1(L_M(0))=+\infty.
> \]

Replace the A6 consumption check by:

\[
\boxed{
\begin{gathered}
\text{T1 (C5-gamma) + (C5-normalizer-read)
+ (C5-varpi-read) + (C6-lift)}\\
\Longrightarrow
\text{the pinned GENTOW6 scalar-read and lift formulas,}\\
\text{with exact lift height only for }\lambda\ne0
\text{ and the displayed zero-lift branch for }\lambda=0.
\end{gathered}
}
\]

## R6-2 — Import and use the binary second-level carry

In the A2 local supplier interface
\(\mathrm{(H\!-\!HETOW\!-\!LOCAL)}\), replace

\[
w_2
=
\left\lfloor
\frac{s(k)+s(k')}{e_2}
\right\rfloor,
\qquad
m(k+k')
=
m(k)+m(k')+w_2u_2.
\]

with:

\[
\boxed{
0\le s(a)<e_2
\quad
\text{for every relevant height }a,
}
\]

and

\[
\boxed{
w_2
=
\left\lfloor
\frac{s(k)+s(k')}{e_2}
\right\rfloor
\in\{0,1\},
\qquad
m(k+k')
=
m(k)+m(k')+w_2u_2.
}
\]

Immediately after these displays, insert:

> The range condition on \(s\), and hence the binary-carry conclusion
> \(w_2\in\{0,1\}\), are HETOW supplier facts. They are not consequences of T1 or of (C5-carry).

In the A2 consumption proof, replace the paragraph beginning

> The supplier relation
> \[
> m(k+k')=m+m'+w_2u_2
> \]
> and two applications of (C5-carry) give

through its displayed equality with:

> The supplier relation gives
> \[
> m(k+k')=m+m'+w_2u_2,
> \qquad
> w_2\in\{0,1\}.
> \]
> First, (C5-carry) gives
> \[
> Q(m+m')-Q(m)-Q(m')
> =
> \operatorname{wrap}_1(m,m').
> \]
> If \(w_2=0\), this is already
> \[
> Q(m(k+k'))-Q(m)-Q(m').
> \]
> If \(w_2=1\), a second application of (C5-carry) gives
> \[
> Q(m+m'+u_2)-Q(m+m')
> =
> Q(u_2)+
> \operatorname{wrap}_1(m+m',u_2).
> \]
> Combining the two binary cases yields
> \[
> \boxed{
> \begin{aligned}
> Q(m(k+k'))-Q(m)-Q(m')
> &=
> \operatorname{wrap}_1(m,m')\\
> &\quad+
> w_2\left(
> Q(u_2)+
> \operatorname{wrap}_1(m+m',u_2)
> \right).
> \end{aligned}
> }
> \]
> Substitution of
> \(\tau(k)=\eta^{-Q(m(k))}\) proves the pinned
> \(\tau\)-ratio.
>
> The displayed formula uses the binary-carry supplier fact essentially. No analogous linear-in-\(w_2\) formula is asserted for \(w_2>1\).

Replace the closing A2 scope sentence

> Thus T1 supplies only the level-one monomial-ratio and \(q\)-carry algebra. The bridge from level \(2\), the function \(m\), the second-level carry \(w_2\), and the identification of \(\tau\) remain explicitly imported HETOW facts.

with:

> Thus T1 supplies only the level-one monomial-ratio and \(q\)-carry algebra. The bridge from level \(2\), the function \(m\), the canonical range
> \(0\le s(a)<e_2\), the resulting binary second-level carry
> \(w_2\in\{0,1\}\), and the identification of \(\tau\) remain explicitly imported HETOW facts.

## Consequential record edits

Append to the honesty ledger:

> 16. Exact lift height is asserted only for a nonzero digit. In particular, a corrected-key coefficient with \(c_t=0\) is the zero lift, has valuation \(+\infty\), and contributes an empty support rather than a finite-height key term.
>
> 17. The pinned A2 HETOW carry formula uses the supplier range
> \[
> 0\le s(a)<e_2,
> \]
> which makes
> \[
> w_2=\left\lfloor
> \frac{s(k)+s(k')}{e_2}
> \right\rfloor
> \]
> binary. T1 does not assert the displayed linear-in-\(w_2\) formula for a nonbinary carry.

Add to §6:

> | Propagated the zero-lift branch into the A3 and A6 absorption pins, and imported the canonical \(s\)-range and binary second-level carry required by the A2 derivation. | T1P7, 2026-08-12 r6 | Repairs 2 GAP findings: no finite exact height is assigned to a zero coefficient, and the HETOW carry proof now states and uses \(w_2\in\{0,1\}\). |


---

## r7 (2026-08-12): arc repairs

*(gpt-5.6-sol high, runs/comp9/T1R7_output.log; transcribed unaltered; counter resets.)*

# T1 r7 corrections — 2026-08-12

These edits repair the zero-coefficient read gap and bind the coefficient representatives defining \(L_M\).

## R7-1 — Add the zero-coefficient branch to the C3 canonical read

In §1.1, immediately after (C3-graded-scalar-covariance), insert:

> At every consumed grade, the read is also defined on the zero homogeneous component and satisfies
> \[
> \boxed{
> R_{i+1,\beta}(0)=0.
> }
> \tag{C3-zero-read}
> \]
> A coherent digit \(\Gamma=0\) means that the homogeneous component at the displayed grade is zero; an underlying representative may instead have strictly larger value. Such a component is not represented by multiplication by a value-zero factor of residue zero.

In (C3), replace the paragraph

> Consequently a slot with coherent digit \(\Gamma_t\) has canonical read
> \[
> \boxed{
> R_{i+1,\beta_t}(\text{slot }t)
> =
> w_i^{f_{i+1}-t}\Theta_i(t)\Gamma_t.
> }
> \tag{C3-canonical-read}
> \]

with:

> Consequently the homogeneous component at grade
> \(\beta_t\) of a slot with coherent digit \(\Gamma_t\) has canonical read
> \[
> \boxed{
> R_{i+1,\beta_t}(\text{slot }t)
> =
> w_i^{f_{i+1}-t}\Theta_i(t)\Gamma_t.
> }
> \tag{C3-canonical-read}
> \]
> If \(\Gamma_t\ne0\), this follows from graded scalar covariance using a value-zero factor of residue \(\Gamma_t\). If \(\Gamma_t=0\), the homogeneous slot component is zero and the formula follows from (C3-zero-read).

In §2.3, replace the paragraph beginning

> A slot with coherent digit \(\Gamma_t\) is represented, at the consumed read site, as

and the following paragraph beginning

> At the corrected key, the inverse telescope factors cancel slotwise

with:

> Let \(X_t\) denote the homogeneous component of slot \(t\) at grade
> \(\beta_t\). If \(\Gamma_t\ne0\), then
> \[
> X_t=M_sg_t,
> \qquad
> dv_i(g_t)=0,
> \qquad
> \operatorname{res}(g_t)=\Gamma_t.
> \]
> Graded scalar covariance therefore gives
> \[
> \begin{aligned}
> R_{i+1,\beta_t}(X_t)
> &=
> R_{i+1,\beta_t}(M_s)\Gamma_t\\
> &=
> w_i^s\Theta_i(t)\Gamma_t.
> \end{aligned}
> \]
> If \(\Gamma_t=0\), then \(X_t=0\) at grade \(\beta_t\), and
> (C3-zero-read) gives
> \[
> R_{i+1,\beta_t}(X_t)
> =
> 0
> =
> w_i^s\Theta_i(t)\Gamma_t.
> \]
> This proves (C3-canonical-read) in both branches.
>
> At the corrected key,
> \[
> \Gamma_t=c_t\vartheta_{i,s},
> \qquad
> \Theta_i(t)=\vartheta_{i,s}^{-1}.
> \]
> If \(c_t\ne0\), graded scalar covariance and cancellation of the inverse telescope factors give
> \[
> R_{i+1,\beta_t}(X_t)
> =
> c_tw_i^s.
> \]
> If \(c_t=0\), then \(\Gamma_t=0\), the zero-lift convention makes the corresponding key term absent, and (C3-zero-read) gives the same identity with both sides zero. Thus the cancellation holds slotwise for every \(t\), and summing gives
> \[
> y^f-\sum_{t<f}c_tw_i^{f-t}y^t
> =
> w_i^f\psi(y/w_i).
> \]

Replace honesty-ledger item 2 with:

> 2. The B-law is conditional on the sitewise graded read facts (C3-ladder-multiplicativity), (C3-slot-grade), and (C3-graded-scalar-covariance). For a zero coherent digit, the displayed homogeneous component is zero and its read is governed separately by (C3-zero-read); no value-zero factor with residue zero is asserted. T1 proves no multiplicativity theorem for all homogeneous initial forms.

In the supporting-context paragraph following the absorption map, replace the sentence beginning

> The B-law rows consume (C3-ladder-multiplicativity) …

with:

> The B-law rows consume (C3-ladder-multiplicativity), the grade identity
> \(\beta_t=(f_{i+1}-t)\bar\kappa_i\), and
> (C3-graded-scalar-covariance) for nonzero coherent digits at their stated sites. Zero coherent digits use the separate zero-component rule (C3-zero-read).

## R7-2 — Fix a residue section for the definition of \(L_M\)

At the beginning of (C6), before

> Let \(M>D'h\), put …

insert:

> Fix once and for all a set-theoretic section of the coefficient residue map
> \[
> \boxed{
> \sigma:\mathbf F_Q\longrightarrow\widehat O,
> \qquad
> \operatorname{res}(\sigma(a))=a,
> \qquad
> \sigma(0)=0.
> }
> \tag{C6-residue-section}
> \]
> Write
> \[
> \widetilde a:=\sigma(a).
> \]
> Thus
> \[
> a\ne0
> \Longrightarrow
> dv(\widetilde a)=0.
> \]
> No additive or multiplicative compatibility of \(\sigma\) is assumed. Every occurrence of \(L_M\) below uses this fixed section.

Immediately after (C6-lift), insert:

> The polynomial \(L_M(\lambda)\) may depend on the fixed section
> \(\sigma\). Its displayed support, integrality, exact-height, residue, and \(x\)-free conclusions do not depend on that choice.

In §2.6, replace the opening proof through the proof of (C6-residue) with:

> For \(0\le r<f_1\),
> \[
> i+e_1r\le D'-1,
> \]
> and
> \[
> a-rh
> =
> \frac{M-(i+e_1r)h}{e_1}
> \ge0
> \]
> because \(M>D'h\). Hence every summand lies in
> \(\widehat O[x]\), and every occurring \(x\)-exponent is less than
> \(D'\).
>
> If \(\lambda_r\ne0\), then (C6-residue-section) gives
> \[
> dv(\widetilde{\lambda_r})=0.
> \]
> The corresponding nonzero summand therefore has height
> \[
> e_1(a-rh)+(i+e_1r)h=M.
> \]
> If \(\lambda_r=0\), that summand is absent because
> \(\widetilde{\lambda_r}=\sigma(0)=0\).
>
> After evaluation at \(\theta\) and division by \(n(M)(\theta)\), the \(r\)-th nonzero summand has residue
> \[
> \iota_\theta(\lambda_r)\,
> \operatorname{res}\!\left(
> \frac{\theta^{e_1}}{\pi^h}
> \right)^r
> =
> \iota_\theta(\lambda_r\eta^r).
> \]
> Summing gives
> \[
> \operatorname{res}\!\left(
> \frac{L_M(\lambda)(\theta)}
> {n(M)(\theta)}
> \right)
> =
> \iota_\theta(\lambda).
> \]
> If \(\lambda\ne0\), injectivity of \(\iota_\theta\) prevents cancellation at height \(M\), so
> \[
> dv(L_M(\lambda))=M.
> \]
> This proves (C6-residue) and the asserted exact-height statement.

Under **A6 — GENTOW6**, immediately after the displayed lift formula, insert:

> Here every representative
> \(\widetilde{\lambda_r}\) is taken using the fixed section
> (C6-residue-section); the pinned lift is therefore a literally defined function of \(M\) and \(\lambda\).

## Consequential record edit

Add to §6:

> | Added the zero-homogeneous-component branch to the C3 canonical read and fixed a residue section for all coefficient representatives in \(L_M\). | T1P8, 2026-08-12 r7 | Repairs 1 GAP and 1 MINOR finding: zero coherent digits now satisfy the canonical-read and three-reads formulas without a nonexistent value-zero representative, and \(L_M\) is a literally defined section-dependent function. |


---

## r8 (2026-08-12): arc repairs

*(gpt-5.6-sol high, runs/comp11/T1R8_output.log; transcribed unaltered; counter resets.)*

# T1 r8 corrections — 2026-08-12

These edits repair the general corrected-key coefficient-space gap and the unsupported nonvanishing of the canonical ladder unit.

## R8-1 — Import the bounded coefficient space into the corrected-key lift contract

In §1.1, replace the opening of the stage-key paragraph introduced by R4-1,

> Fix also the stage key \(\Phi_i\) with the stage-height identity

with:

> Fix also a monic stage key \(\Phi_i\), put
> \[
> d_i:=\deg\Phi_i>0,
> \]
> and assume the stage-height identity

Immediately after (C3-zero-lift), insert:

> Every lift used as a coefficient in (C3-key) is additionally required to lie in the standard bounded coefficient space
> \[
> \mathcal C_i
> :=
> \left\{
> A:\deg A<\deg\Phi_i
> \right\},
> \]
> with the convention \(\deg0=-\infty\). Thus the corrected-key lift contract includes
> \[
> \boxed{
> \deg\!\left(
> \operatorname{lift}_i(d;m)
> \right)
> <
> \deg\Phi_i
> \qquad(d\in K_i).
> }
> \tag{C3-lift-coefficient-space}
> \]
> This coefficient-space condition is an independent part of the lift contract imported from the corrected-coefficient supplier. It does not follow from exact height or normalized residue. In particular, a higher-degree, strictly higher-value perturbation of a valid representative is not an admissible corrected-key lift.
>
> At a level-one consumer with
> \(\deg\Phi_1=D'\), the degree conclusion in (C6) discharges
> (C3-lift-coefficient-space) on the live domain \(m>D'h\).

Immediately after (C3-corrected-lift), insert:

> In addition to the residue, zero, and nonzero-height clauses, this coefficient is chosen under (C3-lift-coefficient-space):
> \[
> \boxed{
> \deg\widehat k_t<\deg\Phi_i.
> }
> \tag{C3-corrected-coefficient-bound}
> \]

In §2.3, immediately after the proof of (C3-common-height), insert:

> It remains to check the polynomial shape. Put
> \[
> d_i=\deg\Phi_i.
> \]
> For every nonzero lower coefficient and every \(t<f_{i+1}\),
> \[
> \begin{aligned}
> \deg\!\left(
> \widehat k_t\Phi_i^{e_{i+1}t}
> \right)
> &<
> d_i+e_{i+1}t\,d_i\\
> &=
> \bigl(e_{i+1}t+1\bigr)d_i\\
> &\le
> e_{i+1}f_{i+1}d_i\\
> &=
> \deg\!\left(
> \Phi_i^{e_{i+1}f_{i+1}}
> \right).
> \end{aligned}
> \]
> The inequality is strict even in the boundary case
> \(e_{i+1}=1\) and \(t=f_{i+1}-1\), because
> \(\deg\widehat k_t<d_i\). A zero coefficient contributes no term. Since \(\Phi_i\) is monic, (C3-key) is therefore monic of degree
> \[
> e_{i+1}f_{i+1}\deg\Phi_i
> \]
> and has coefficients reduced modulo \(\Phi_i\) in the asserted
> \(\Phi_i\)-adic shape.
>
> This proves only the monicity and bounded-coefficient shape of the displayed composed polynomial. Any further assertion that it is a key polynomial uses the surrounding tower supplier theorem.

Under **A7 — GENTOW2**, insert before **B-law classification**:

> **COEFFICIENT-SPACE PIN.** The accepted GENTOW2 corrected-coefficient construction selects each coefficient in the bounded space
> \[
> \boxed{
> \deg\widehat k_t<\deg\Phi_i.
> }
> \]
> T1 imports precisely this condition as
> (C3-lift-coefficient-space) and
> (C3-corrected-coefficient-bound). Exact height and normalized residue supply no substitute for this bound. No general lift-existence theorem beyond the stated integral domains is imported from GENTOW2.

## R8-2 — Make ladder nonvanishing an explicit certified-site obligation

In §1.1, immediately after (C3-zero-read), insert:

> At every consumed site where \(w_i\) and the unit-rescaling conclusion in (C3) are used, assume the base ladder read is nonzero:
> \[
> \boxed{
> R_{i+1,\bar\kappa_i}
> \bigl(
> \widehat n_i(u_{i+1})
> \bigr)
> \ne0.
> }
> \tag{C3-ladder-nonvanishing}
> \]
> This is an independent site obligation. It does not follow from ladder multiplicativity, graded scalar covariance, agreement with residue in grade zero, or (C3-zero-read). Those obligations alone permit a read that vanishes on every positive-grade homogeneous component.
>
> At \(i=2\), the accepted GENTOW2-B\('\)/B\(''\) supplier discharges (C3-ladder-nonvanishing) at its local site. At \(i\ge3\), every consumer must cite a level-general residual-read supplier that includes this nonvanishing conclusion; T1 does not infer it from the other read axioms.

Replace the definition of \(w_i\) by:

> Put
> \[
> \bar\kappa_i=\frac{u_{i+1}}{e(\mu_i)},
> \qquad
> N_i:=\widehat n_i(u_{i+1}),
> \]
> and define
> \[
> w_i
> =
> R_{i+1,\bar\kappa_i}(N_i).
> \]
> At every consumed site carrying
> (C3-ladder-nonvanishing),
> \[
> \boxed{w_i\in K_i^\times.}
> \tag{C3-ladder-unit}
> \]

In (C3), immediately before (C3-three-reads), insert:

> Assume for the remainder of the three-read and factor-pattern conclusions that the consumed site discharges
> (C3-ladder-multiplicativity),
> (C3-graded-scalar-covariance),
> (C3-zero-read), and
> (C3-ladder-nonvanishing). In particular,
> \(w_i\in K_i^\times\).

In §2.3, immediately before the B-law calculation, insert:

> By (C3-ladder-nonvanishing),
> \[
> w_i
> =
> R_{i+1,\bar\kappa_i}(N)
> \ne0.
> \]
> Hence \(w_i\in K_i^\times\).

Replace the final factor-pattern paragraph of §2.3 with:

> By (C3-ladder-nonvanishing), \(w_i\) is a unit. Therefore
> \[
> y\longmapsto y/w_i
> \]
> is an automorphism of \(K_i[y]\), and multiplication by
> \(w_i^{\deg P}\) is multiplication by a nonzero scalar. Consequently
> \[
> P(y)\longmapsto
> w_i^{\deg P}P(y/w_i)
> \]
> transports factorizations bijectively and preserves degrees, multiplicities, irreducibility, and a nonzero constant term. This proves the factor-pattern conclusion. Without
> (C3-ladder-nonvanishing), neither division by \(w_i\) nor the unit-substitution argument is asserted.

In the A7 **B-law classification**, replace the residual-obligation sentence with:

> The residual obligation is the accepted GENTOW2-B\('\)/B\(''\) per-grade-unit theorem discharging the slot-grade identity, ladder multiplicativity, graded scalar covariance for the consumed value-zero factors, and
> \[
> R_{i+1,\bar\kappa_i}
> \bigl(
> \widehat n_i(u_{i+1})
> \bigr)\ne0.
> \]
> Only after this nonvanishing clause is supplied may T1 regard \(w_i\) as an element of \(K_i^\times\), form
> \[
> \psi_{i+1}^{(w_i)}(y)
> =
> w_i^{f_{i+1}}\psi_{i+1}(y/w_i),
> \]
> and invoke unit-substitution invariance.

Replace the supporting-context paragraph following the absorption map with:

> The B-law rows consume (C3-ladder-multiplicativity), the grade identity
> \(\beta_t=(f_{i+1}-t)\bar\kappa_i\), and
> (C3-graded-scalar-covariance) for nonzero coherent digits at their stated sites. Zero coherent digits use the separate zero-component rule (C3-zero-read). The three-read rescaling and factor-pattern conclusion additionally consume
> (C3-ladder-nonvanishing). At \(i=2\), these obligations are supplied at the accepted GENTOW2-B\('\)/B\(''\) site. For \(i\ge3\), they must be included explicitly in the cited level-general residual-read supplier.

## Consequential scope and verification edits

Replace honesty-ledger item 2 with:

> 2. The B-law is conditional on the sitewise graded read facts
> (C3-ladder-multiplicativity), (C3-slot-grade), and
> (C3-graded-scalar-covariance). For a zero coherent digit, the displayed homogeneous component is zero and its read is governed separately by (C3-zero-read). The assertion
> \(w_i\in K_i^\times\), and hence the unit-rescaling and factor-pattern argument, additionally require the independent site obligation
> (C3-ladder-nonvanishing). T1 proves none of these facts for all homogeneous initial forms.

Append to the honesty ledger:

> 18. Exact height and normalized residue do not determine an admissible corrected-key representative. Every coefficient used in (C3-key) must also satisfy
> \[
> \deg\widehat k_t<\deg\Phi_i.
> \]
> Higher-degree, higher-value perturbations are excluded by the coefficient-space contract.
>
> 19. The displayed residual-read axioms do not imply that the base ladder read is nonzero. The status
> \(w_i\in K_i^\times\) is asserted only at sites carrying
> (C3-ladder-nonvanishing), supplied locally by GENTOW2-B\('\)/B\(''\) or by an explicitly cited level-general analogue.

Append to §4.2:

> 7. **General coefficient-space bound.** For every corrected-key coefficient, score
>    \[
>    \deg\widehat k_t<\deg\Phi_i.
>    \]
>    Add a mock representative obtained from a valid lift by adding a sufficiently high-degree, strictly higher-value term. Confirm that it still passes the height and residue checks but is rejected by
>    (C3-lift-coefficient-space). Score that the accepted coefficients make every lower key term have degree strictly below the leading term.
>
> 8. **Ladder nonvanishing.** Instantiate a mock residual read that is zero on every positive-grade homogeneous component while satisfying ladder multiplicativity, graded scalar covariance, the grade-zero residue rule, and
>    \(R_{i+1,\beta}(0)=0\). Confirm that it is rejected precisely by
>    (C3-ladder-nonvanishing), and that no expression containing
>    \(y/w_i\) or unit-substitution factor transport is accepted without that clause.

In the \(M2\) row of (C7), add:

> Corrected-key coefficients additionally use
> (C3-lift-coefficient-space), and canonical factor-pattern transport uses
> (C3-ladder-nonvanishing).

Add to §6:

> | Imported the GENTOW2 bounded coefficient space into the general corrected-key lift contract and made base-ladder nonvanishing an explicit certified-site obligation. | T1P9, 2026-08-12 r8 | Repairs 2 GAP findings: higher-degree higher-value perturbations are excluded, so the composed polynomial retains its monic bounded \(\Phi_i\)-adic shape; and \(w_i\in K_i^\times\), division by \(w_i\), and factor-pattern transport are asserted only where nonvanishing is supplied. |


---

## r9 (2026-08-12): provenance + fencing repairs

*(Fable-arm; findings = the model-diverse pass of record; counter resets.)*

# T1 r9 corrections — 2026-08-12

These edits repair the findings of the model-diverse hostile pass of record (0 CRITICAL / 2 GAP / 4 MINOR; all arithmetic and repairs verified): two provenance/fencing gaps (G-1, G-2) and four minors (m-1 through m-4). Every supplier fact cited below was re-verified against the accepted files this round; the greps, ledger lookups, and md5 recomputations are named inline.

## R9-1 (G-1) — Re-attribute the A6 scalar-read pin to HE6 F-1

**Finding G-1.** The r2 A6 row's SPAN PIN attributes the boxed \(\gamma_k(A)\)-definition and \(n(k)\)/\(\varpi\)-read displays to `GENTOW6`, locator `md5=05fc38817b8c75297267bb57089e898f`. Verified this round: that md5 is the ledger's [THEOREM GENTOW-6.3] entry (`runs/comp1/_absorbed_statements.txt`: `GENTOW6_PROOF_2026-08-09.md` @ commit `3d7fc37b`, lines 378–434; recomputed under the R9-5 normalization — it reproduces `05fc38817b8c75297267bb57089e898f` exactly), and the accepted `GENTOW6` contains no \(\gamma_k\) and no \(\varpi\) anywhere (grep: zero occurrences). The pinned scalar-read displays live ONLY in `HE6_PROOF_2026-08-08.md`'s dated correction F-1 (2026-08-12), grep-verified there at the three displays quoted closed below. The r2 md5 pinned a consumer, not the source.

Under **A6 — GENTOW6**, replace the SPAN PIN header sentence

> **SPAN PIN.** Accepted file `GENTOW6`, normalized scalar-read display used by THEOREM GENTOW-6.3 (`md5=05fc38817b8c75297267bb57089e898f`):

with:

> **SPAN PIN (scalar read; provenance HE6 F-1).** Accepted file `HE6_PROOF_2026-08-08.md`, dated correction “F-1 — normalized slot coefficients in LEMMA HE6-0″” (2026-08-12; commit `a5d8eb01`, lines 1061–1113, normalized-span `md5=2c80192d30f82191476b4113e2314dad`). With \(k:=dv(A)\), \(i=i(k)\) the unique integer \(0\le i<e_1\) satisfying \(ih\equiv k\pmod{e_1}\), and \(n(k):=x^i\pi^{(k-ih)/e_1}\), F-1’s displays, quoted closed, are
> \[
> \gamma_k(A):=
> \sum_{\substack{t\ge0\\i+e_1t<D'}}
> \operatorname{res}\!\left(
> a_{i+e_1t}\pi^{-(k-(i+e_1t)h)/e_1}
> \right)\eta_\theta^t\in K,
> \]
> \[
> \operatorname{res}\!\left(\frac{A(\xi)}{n(k)(\xi)}\right)
> =\iota_\xi(\gamma_k(A)).
> \]
> \[
> \operatorname{res}\!\left(\frac{A(\xi)}{\varpi(\xi)^k}\right)
> =\iota_\xi(\gamma_k(A))\,\eta_\xi^{-q(k)}.
> \]
> The two boxed displays below are exactly these F-1 displays transcribed into T1 notation (\(i(k)\) written for F-1’s \(i\), \(\eta\) for \(\eta_\theta\), the two reads joined into one box). Their provenance is HE6 F-1 and only HE6 F-1: the accepted `GENTOW6` contains no \(\gamma_k(A)\) and no \(\varpi\)-read display anywhere. The locator `md5=05fc38817b8c75297267bb57089e898f` pins THEOREM GENTOW-6.3 — the CONSUMER of the scalar read, retained at the lift pin below — not the source of these displays. In T1 notation the pinned scalar read is:

The two boxed \(\gamma_k(A)\) displays that follow stay byte-unchanged.

In the same row, replace the sentence

> The associated lift pin is

with:

> The associated lift pin — this half IS `GENTOW6`’s own display (S6.1’s exact-height (LIFT) shape; consumer THEOREM GENTOW-6.3, `md5=05fc38817b8c75297267bb57089e898f`), kept as pinned — is

In the A6 consumption check as replaced by R6-1, replace the line

> \text{the pinned GENTOW6 scalar-read and lift formulas,}\\

with:

> \text{the pinned scalar-read (HE6 F-1) and lift (GENTOW6 S6.1) formulas,}\\

No formula changes anywhere in this repair; only provenance.

## R9-2 (G-2) — Fence (C2-vartheta)’s \(K_i^\times\) membership at depth \(i\ge3\)

**Finding G-2.** (C2-vartheta)’s box asserts \(\vartheta_{i,s}\in K_i^\times\) at every level \(i\). The quotient \(\widehat n_i(u_{i+1})^s/\widehat n_i(su_{i+1})\) has value zero — that much is exact-height arithmetic — but at depth \(i\ge3\) nothing in §2.2 proves that its residue lies in the FIELD \(K_i\): it is a value-zero quotient of tower normalizers, exactly the class of object R2-1 conceded needs a supplier when it fenced \(\rho_i\). Proved suppliers exist at \(i\in\{1,2\}\) only. The repair fences the box the way \(\rho_i\) was fenced.

In §1.1 (C2), immediately after (C2-vartheta), insert:

> The membership \(\vartheta_{i,s}\in K_i^\times\) displayed in (C2-vartheta) is proved only at \(i\in\{1,2\}\): at \(i=1\) by direct evaluation ((C2-level-1): \(\vartheta_{1,s}=\eta^{\lfloor s\,i(u_2)/e_1\rfloor}\), a power of \(\eta\in K_1^\times\)); at \(i=2\) by the accepted LEMMA GENTOW2-B\(''\) \(\gamma\)-calculus (S5.2), which writes the value-zero \(\widehat n_2\)-quotient as a letter monomial and specializes it into \(K_2^\times\). At \(i\ge3\), T1 does not prove that the residue lies in \(K_i\). Every consumer at depth \(i\ge3\) must carry the named supplier hypothesis
> \[
> \mathrm{(H\!-\!VARTHETA\!-\!RES)}_i:
> \quad
> \operatorname{res}\!\left(
> \frac{\widehat n_i(u_{i+1})^s}
> {\widehat n_i(su_{i+1})}
> \right)\in K_i
> \qquad(s\ge0)
> \]
> — the residue of the value-zero tower-normalizer quotient lies in the level-\(i\) residue field: standard MacLane residual specialization, unproved here. Under \(\mathrm{(H\!-\!VARTHETA\!-\!RES)}_i\), value zero makes the residue nonzero, whence \(\vartheta_{i,s}\in K_i^\times\). Without it, at \(i\ge3\) the box asserts a membership T1 does not prove.

In §2.2, immediately after “Taking residues proves the recursion.”, insert:

> At \(i\ge3\), taking residues proves the recursion among the residues; that each \(\vartheta_{i,s}\) lies in \(K_i\) is \(\mathrm{(H\!-\!VARTHETA\!-\!RES)}_i\), not a computation of this proof. At \(i\in\{1,2\}\) the memberships are supplied as displayed in (C2).

In (C3), immediately after the R8-1 insertion following (C3-corrected-lift) (the boxed (C3-corrected-coefficient-bound)), insert:

> At \(i\ge3\), the digit \(c_t\vartheta_{i,f_{i+1}-t}\) fed to \(\operatorname{lift}_i\) is an element of \(K_i\) — so (C3-corrected-lift) type-checks and the corrected composed key (C3-key) is formed — only at a site carrying \(\mathrm{(H\!-\!VARTHETA\!-\!RES)}_i\). At \(i\in\{1,2\}\) the membership is supplied as displayed in (C2). No corrected composed key is asserted at depth \(i\ge3\) without that hypothesis.

In the R4-1 paragraph inserted immediately after (C3-corrected-lift), replace the opening

> Put \(s=f_{i+1}-t\). If \(c_t\ne0\), then
> \(\vartheta_{i,s}\in K_i^\times\) implies
> \(c_t\vartheta_{i,s}\ne0\), and the exact-height lift contract gives

with:

> Put \(s=f_{i+1}-t\). At \(i\in\{1,2\}\), and at \(i\ge3\) at a site carrying \(\mathrm{(H\!-\!VARTHETA\!-\!RES)}_i\), one has \(\vartheta_{i,s}\in K_i^\times\); hence if \(c_t\ne0\), then \(c_t\vartheta_{i,s}\ne0\), and the exact-height lift contract gives

## R9-3 (m-1) — Fix the A3 “accepted local \(\gamma_t\)” misattribution

**Finding m-1.** A3’s closing sentence calls \(\gamma_t\) “the accepted local” symbol, implying `GENTOW1` uses it. Verified this round: `GENTOW1` contains no \(\gamma_t\) anywhere (grep: zero occurrences); its corrected-lift pin is \(\widehat c_t:=\operatorname{lift}(c_t\cdot\eta^{W(t)})\) (the S0 pin, dated gauge annex S7.1), and it displays no single closed span carrying A3’s read statement.

Under **A3 — GENTOW1**, replace

> with the closed read statement

with:

> with the read statement — ASSEMBLED, not quoted closed, per the quoted-closed rule of this map’s introduction: its content is assembled from `GENTOW1`’s S0 corrected-lift pin together with the dated gauge annex S7.1, and `GENTOW1` displays no single closed span carrying it —

and replace

> Here the accepted local \(\gamma_t\) is T1’s coherent digit \(\Gamma_t\), not HE6’s \(\gamma_k(A)\).

with:

> The symbol \(\gamma_t\) in the first boxed display is T1’s local abbreviation for its own coherent digit \(\Gamma_t=c_t\eta^{W(t)}\) — read \(\Gamma_t\) for \(\gamma_t\) there. The accepted `GENTOW1` displays no \(\gamma_t\) anywhere; its pin names \(\widehat c_t:=\operatorname{lift}(c_t\cdot\eta^{W(t)})\) (S0 pin, S7.1). As before, \(\Gamma_t\) is distinct from HE6’s \(\gamma_k(A)\).

## R9-4 (m-2) — Scope the A7 SPAN PIN 2 consequence list to the pinned span

**Finding m-2.** The A7 SPAN PIN 2 consequence list includes “preservation of irreducible-factor degrees and multiplicities,” which the pinned LEMMA GENTOW2-B span (`md5=8a00bf44d21f87e878c0be6226b13b61`) does not assert: the span’s preservation parenthetical covers monicity after the displayed renormalization, irreducibility, degree, and the nonzero constant, for its monic irreducible target.

Under **A7 — GENTOW2**, replace

> The pinned consequences are: monicity after the displayed renormalization, preservation of degree and irreducibility, preservation of a nonzero constant term, and preservation of irreducible-factor degrees and multiplicities.

with:

> The pinned consequences — exactly what the pinned span asserts, for its monic irreducible target \(\psi_3\) (the span’s parenthetical: the substitution \(y\mapsto wy\) “preserves monicity after the renormalization displayed, irreducibility, degree, and the nonzero constant”) — are: monicity after the displayed renormalization, and preservation of degree, of irreducibility, and of the nonzero constant term. Preservation of irreducible-factor degrees and multiplicities for a general polynomial is NOT asserted by the pinned span; it is T1’s factor-pattern conclusion (§2.3), asserted only at sites where the accepted GENTOW2-B\('\)/B\(''\) supplier discharges (C3-ladder-nonvanishing) (the R8-2 fence).

## R9-5 (m-3) — Document the md5 pin normalization convention

**Finding m-3.** The map’s `md5=…` locators nowhere state what text they hash, so the pins were not mechanically checkable from the note alone.

In the replacement §3 absorption map, immediately after the introductory blockquote (the paragraph ending “the residual obligation is named explicitly.”), insert:

> **Pin normalization convention (md5).** Every `md5=…` in this map pins a NORMALIZED ONE-LINE STATEMENT SPAN at a declared commit: take the ledger’s line range from the accepted file at the commit declared in the ledger’s section header; strip leading blockquote markers; join the lines into one line; collapse repeated whitespace; trim; md5 the resulting one-line text. The ledger of record is `runs/comp1/_absorbed_statements.txt` (S-0 @ `788bba26`; per-note commits in its section headers, e.g. `GENTOW6_PROOF_2026-08-09.md` @ `3d7fc37b`), reproduced in the T1CC2 brief (`runs/comp1/T1CC2_brief.txt`). Re-verified this round: lines 378–434 of `GENTOW6_PROOF_2026-08-09.md` @ `3d7fc37b` normalize to `md5=05fc38817b8c75297267bb57089e898f`, the ledger’s [THEOREM GENTOW-6.3] entry.

## R9-6 (m-4) — Refresh the stale front-matter status line

**Finding m-4.** The front matter still reads “hostile arc not yet run on this revision”; eight repair rounds (and this ninth) sit below it.

Replace the front-matter line

> **Status:** revised candidate of record; hostile arc not yet run on this revision

with (preserving the trailing two-space markdown line break):

> **Status:** revised candidate of record, under hostile arc — rounds r1–r9 appended below (r1–r8 sol-derived repair rounds; r9 the Fable-arm repairs of the model-diverse pass of record). Clean-pass counter at reset (every repair round resets it); the §7 acceptance gate still owes two consecutive clean hostile passes plus the revised machine battery.

## Consequential record edits

Append to the honesty ledger:

> 20. The A6 scalar-read displays — the \(\gamma_k(A)\) definition and the \(n(k)\)/\(\varpi\)-reads — are HE6 F-1’s displays, transcribed; the accepted `GENTOW6` contains no \(\gamma_k(A)\) and no \(\varpi\)-read display. The locator `md5=05fc38817b8c75297267bb57089e898f` pins THEOREM GENTOW-6.3, the consumer. Every SPAN PIN md5 is a normalized one-line span at a declared commit, per the §3 convention paragraph.
>
> 21. \(\vartheta_{i,s}\in K_i^\times\) is proved at \(i\in\{1,2\}\) only. At \(i\ge3\), that membership — and with it the typing of (C3-corrected-lift), the formation of (C3-key), and the nonzero-digit common-height argument — is asserted only at sites carrying \(\mathrm{(H\!-\!VARTHETA\!-\!RES)}_i\).

Add to §6:

> | Re-attributed the A6 scalar-read pin to HE6 F-1 (`GENTOW6` has no \(\gamma_k\)/\(\varpi\) display); fenced (C2-vartheta)’s \(K_i^\times\) membership behind \(\mathrm{(H\!-\!VARTHETA\!-\!RES)}_i\) at depth \(i\ge3\) and threaded the fence through (C3-corrected-lift)/(C3-key)/the R4-1 nonvanishing step; fixed the A3 \(\gamma_t\) naming; scoped the A7 PIN 2 consequence list to the pinned span; documented the md5 pin normalization convention; refreshed the front-matter status line. | model-diverse pass of record, 2026-08-12 r9 (Fable arm) | Repairs 2 GAP and 4 MINOR findings: absorption provenance now names the actual supplier note, and depth-\(\ge3\) residue membership is an explicit named supplier hypothesis rather than an unproved boxed claim. |

---

## r10 (2026-08-12): C7 fence completion

*(Fable-arm; the single T1P10 finding; counter resets.)*

# T1 r10 correction — 2026-08-12

This edit repairs the single finding of T1P10 (0 CRITICAL / 1 GAP / 0 MINOR).

## R10-1 (G-1) — Propagate \(\mathrm{(H\!-\!VARTHETA\!-\!RES)}_i\) into (C7)’s \(M2\) and \(M3\) rows

**Finding G-1.** (C7) introduces its interface table with “T1 relates to its fields only as follows,” yet its effective \(M2\) row (the r2 replacement as extended by the r8 addition) and its \(M3\) row (unamended since the original table) omit \(\mathrm{(H\!-\!VARTHETA\!-\!RES)}_i\), which both fields consume at depth \(i\ge3\): \(M2\) uses \(\vartheta_{i,s}\), the inverses \(\Theta_i(t)\), and the corrected digits \(c_t\vartheta_{i,f_{i+1}-t}\) as \(K_i\)-scalars, and \(M3\) uses the \(K_i^\times\)-valued telescope — while r9 requires that every consumer at depth \(i\ge3\) carry the named supplier hypothesis. The scored-stratum and residual-read obligations already listed in those rows do not themselves establish that the normalizer-quotient residue lies in \(K_i\), so without the fence the table is not the complete standalone WELD-M-PKG interface it claims to be.

In (C7), supersede the \(M2\) row (as amended by r2 and r8) and the \(M3\) row (as in the original table) with the following rows; each is its predecessor verbatim with \(\mathrm{(H\!-\!VARTHETA\!-\!RES)}_i\) \((i\ge3)\) appended to its fence list, and nothing else changed:

| Package field | T1 datum available to that field |
|---|---|
| \(M2\) | The dictionary and canonical read in (C3), plus (C4-origin); support transport only under \(\mathrm{(H\!-\!JA\!-\!RES\!-\!CONJ)}\). Corrected-key coefficients additionally use (C3-lift-coefficient-space), and canonical factor-pattern transport uses (C3-ladder-nonvanishing). At depth \(i\ge3\), the scalars \(\vartheta_{i,s}\), their inverses \(\Theta_i(t)\), and the corrected digits \(c_t\vartheta_{i,f_{i+1}-t}\) are \(K_i\)-scalars only under \(\mathrm{(H\!-\!VARTHETA\!-\!RES)}_i\) \((i\ge3)\). |
| \(M3\) | The cocycle/telescope (C2) and canonical twist in (C3), only on the scored stratum. At depth \(i\ge3\), the \(K_i^\times\)-valued telescope is available only under \(\mathrm{(H\!-\!VARTHETA\!-\!RES)}_i\) \((i\ge3)\). |

The \(M0\), \(M1\), and \(M4\) rows are unchanged: those fields consume no \(\vartheta_{i,s}\) datum, so \(\mathrm{(H\!-\!VARTHETA\!-\!RES)}_i\) does not enter their fence lists.

Add to §6:

> | Propagated \(\mathrm{(H\!-\!VARTHETA\!-\!RES)}_i\) (depth \(i\ge3\)) into (C7)’s \(M2\) and \(M3\) interface rows, completing the r9 fence at the WELD-M-PKG interface. | T1P10, 2026-08-12 r10 (Fable arm) | Repairs 1 GAP finding: the “only as follows” table now carries the depth-\(\ge3\) residue-membership hypothesis on both fields that consume it; formulas C1–C6 and all other rows unchanged. |


---

## r11 (2026-08-12): the read codomain + complete M2 fence + permanent status line

*(Fable-arm; counter resets.)*

# T1 r11 corrections — 2026-08-12

These edits repair the findings of the latest Fable hostile pass (0 CRITICAL / 2 GAP / 3 MINOR): the undeclared codomain of the canonical residual read (F-1), the incomplete (C7) \(M2\) fence list (F-2), the twice-stale front-matter status line (m-1), the \(w_2\) symbol collision (m-2), and the undefined grade data plus unsubscripted \(dv\) (m-3). Counter state after this round: the clean-pass counter is RESET (every repair round resets it); the §7 acceptance gate still owes TWO consecutive clean hostile passes; the machine battery, green at its r-early state, is inherited evidence only, pending re-run against the current effective text.

## R11-1 (F-1) — Declare the read codomain: (C3-read-codomain)

**Finding F-1 (GAP).** The canonical residual read \(R_{i+1,\beta}\) has no declared codomain anywhere in the carrier, and r8 infers \(w_i\in K_i^\times\) from nonvanishing alone. The inference is defeated by the initial-form read \(R_{i+1,\beta}(g):=\operatorname{in}(g)\), valued in the graded ring \(\operatorname{gr}(\mu_i)\): it satisfies every displayed read axiom — ladder multiplicativity (initial forms multiply on the single-pin ladder monomials), graded scalar covariance and the grade-zero rule (through the grade-0 identification), \(\operatorname{in}\) of the zero component is \(0\), and (C3-ladder-nonvanishing) (\(\operatorname{in}(N)\ne0\) for \(N\ne0\)) — yet its outputs are grade-\(\beta\) homogeneous elements, not \(K_i\)-scalars. Under that read, “\(w_i\in K_i^\times\)”, the automorphism \(y\mapsto y/w_i\) of \(K_i[y]\), the rescaled key \(\psi_{i+1}^{(w_i)}\), and factor-pattern transport are not even typeable. In particular this mock read PASSES §4.2 check 8 (its base ladder read is nonzero); the battery had no codomain tooth.

In §1.1, immediately after the R8-2 insertion (C3-ladder-nonvanishing), insert:

> At every consumed site, assume additionally that the canonical residual read is scalar-valued on the consumed slices: for every consumed grade \(\beta\), the read carries the consumed grade-\(\beta\) homogeneous elements into the level-\(i\) residue field,
> \[
> \boxed{
> R_{i+1,\beta}\bigl(\text{consumed grade-}\beta\text{ slice}\bigr)
> \subseteq
> K_i.
> }
> \tag{C3-read-codomain}
> \]
> This is an independent site obligation. It does not follow from ladder multiplicativity, graded scalar covariance, the grade-zero residue rule, (C3-zero-read), or (C3-ladder-nonvanishing): the initial-form read \(g\mapsto\operatorname{in}(g)\in\operatorname{gr}(\mu_i)\) satisfies all of them and outputs grade-\(\beta\) homogeneous elements, not \(K_i\)-scalars.
>
> At \(i=2\), the accepted GENTOW2 supplier discharges (C3-read-codomain) at its local site: the S5.1 (R-FGMN) display types the read into the field — \(R_{3,\beta}(g)\in F_3=K_2\) (FGMN Def 3.16 at \(i=3\), single \(j=0\) term: \(R_{3,\beta}(g)=\varepsilon_2(\beta)\cdot R_{2,\beta}(g)(z_2)\)) — and LEMMA GENTOW2-B\('\) types its per-grade unit \(u(\beta):=R_{3,\beta}(\widehat n_2(\widehat\beta))\in K_2^\times=F_3^{*}\), with B\(''\) (S5.2) computing the values; both re-verified against the accepted `GENTOW2_PROOF_2026-08-09.md` this round. At \(i\ge3\), (C3-read-codomain) rides the same named level-general residual-read supplier package as (C3-ladder-nonvanishing); T1 does not infer it from the other read axioms.

Replace the R8-2 unit clause

> At every consumed site carrying
> (C3-ladder-nonvanishing),
> \[
> \boxed{w_i\in K_i^\times.}
> \tag{C3-ladder-unit}
> \]

with:

> At every consumed site carrying
> (C3-read-codomain) and (C3-ladder-nonvanishing),
> \[
> \boxed{w_i\in K_i^\times.}
> \tag{C3-ladder-unit}
> \]
> The two clauses split the inference: (C3-read-codomain) places \(w_i\in K_i\); (C3-ladder-nonvanishing) makes it nonzero. Neither alone yields a unit.

In the R8-2 insertion before (C3-three-reads), replace the discharge list “(C3-ladder-multiplicativity), (C3-graded-scalar-covariance), (C3-zero-read), and (C3-ladder-nonvanishing)” with “(C3-ladder-multiplicativity), (C3-graded-scalar-covariance), (C3-zero-read), (C3-ladder-nonvanishing), and (C3-read-codomain)”.

In §2.3, replace the R8-2 insertion before the B-law calculation with:

> By (C3-read-codomain),
> \[
> w_i
> =
> R_{i+1,\bar\kappa_i}(N)\in K_i;
> \]
> by (C3-ladder-nonvanishing), \(w_i\ne0\). Hence \(w_i\in K_i^\times\).

In the R8-2 replacement of the final factor-pattern paragraph of §2.3, replace its first sentence

> By (C3-ladder-nonvanishing), \(w_i\) is a unit.

with

> By (C3-read-codomain) and (C3-ladder-nonvanishing), \(w_i\) is a unit of \(K_i\).

and replace its closing sentence with:

> Without (C3-read-codomain), \(y/w_i\) is not defined in \(K_i[y]\); without (C3-ladder-nonvanishing), division by \(w_i\) fails. Neither the automorphism nor the unit-substitution argument is asserted without both.

In the A7 **B-law classification** (as replaced by R8-2), replace

> discharging the slot-grade identity, ladder multiplicativity, graded scalar covariance for the consumed value-zero factors, and

with:

> discharging the slot-grade identity, ladder multiplicativity, graded scalar covariance for the consumed value-zero factors, the field codomain of the read ((R-FGMN): \(R_{3,\beta}(g)\in F_3=K_2\)), and

and replace

> Only after this nonvanishing clause is supplied may T1 regard

with:

> Only after the codomain and nonvanishing clauses are both supplied may T1 regard

In the R8-2 supporting-context paragraph, replace

> The three-read rescaling and factor-pattern conclusion additionally consume
> (C3-ladder-nonvanishing).

with:

> The three-read rescaling and factor-pattern conclusion additionally consume
> (C3-read-codomain) and (C3-ladder-nonvanishing).

Append to §4.2:

> 9. **Read codomain.** Instantiate the initial-form mock read \(g\mapsto\operatorname{in}(g)\in\operatorname{gr}(\mu_i)\). Confirm that it passes check 8 (its base ladder read is nonzero) and every other displayed read axiom, and is rejected precisely by (C3-read-codomain): its output at grade \(\bar\kappa_i\) is a positive-grade homogeneous element, not a grade-0/\(K_i\)-scalar. Score that every accepted read output is a \(K_i\)-scalar before any expression containing \(y/w_i\), \(\psi_{i+1}^{(w_i)}\), or \(w_i^{\deg P}\) is accepted.

## R11-2 (F-2) — Complete the (C7) \(M2\) fence list

**Finding F-2 (GAP).** The effective \(M2\) row (the r10 supersession) names only one member of the graded-read bundle — (C3-ladder-nonvanishing) — while \(M2\)’s consumed canonical read and factor-pattern transport rest on all five ((C3-ladder-multiplicativity), (C3-slot-grade), (C3-graded-scalar-covariance), (C3-zero-read), (C3-ladder-nonvanishing)) and now (C3-read-codomain). Under r10’s own standard — the “only as follows” table must be the complete standalone WELD-M-PKG interface — the row must name them all.

In (C7), supersede the \(M2\) row (as superseded by r10) with the following row; it is the r10 row with the complete graded-read fence named, and nothing else changed:

| Package field | T1 datum available to that field |
|---|---|
| \(M2\) | The dictionary and canonical read in (C3), plus (C4-origin); support transport only under \(\mathrm{(H\!-\!JA\!-\!RES\!-\!CONJ)}\). The graded-read bundle consumed by the canonical read and its factor-pattern transport is, in full: (C3-ladder-multiplicativity), (C3-slot-grade), (C3-graded-scalar-covariance), (C3-zero-read), (C3-ladder-nonvanishing), and (C3-read-codomain). Corrected-key coefficients additionally use (C3-lift-coefficient-space). At depth \(i\ge3\), the scalars \(\vartheta_{i,s}\), their inverses \(\Theta_i(t)\), and the corrected digits \(c_t\vartheta_{i,f_{i+1}-t}\) are \(K_i\)-scalars only under \(\mathrm{(H\!-\!VARTHETA\!-\!RES)}_i\) \((i\ge3)\). |

The \(M3\) row is confirmed defensible as it stands (its r10 form): its consumed datum — the (C2) cocycle/telescope and the (C3) canonical twist, on the scored stratum — carries the fences that row already names (the scored-stratum fence and \(\mathrm{(H\!-\!VARTHETA\!-\!RES)}_i\) at depth \(i\ge3\)) and does not consume the graded-read bundle. \(M0\), \(M1\), \(M4\) unchanged.

## R11-3 (m-1) — Make the front-matter status line self-maintaining

**Finding m-1 (MINOR).** The front-matter status line went stale AGAIN: the R9-6 replacement (“rounds r1–r9 appended below”) predates r10. Any dated form re-stales at every subsequent round.

Repaired PERMANENTLY, and applied to the front matter IN PLACE this round (the one sanctioned in-place edit of r11; every other repair appends). The line now reads, datelessly:

> **Status:** revised candidate of record, under hostile arc — repair rounds appended below; THE HIGHEST-NUMBERED r-SECTION GOVERNS; the clean-pass counter and owed passes are recorded in that section.

R9-6’s directive form is superseded. No future round can stale this line: every round-dependent fact (counter state, owed passes, battery state) lives in the governing r-section — for this round, in the r11 header paragraph above.

## R11-4 (m-2) — Resolve the \(w_2\) symbol collision: the HETOW carry becomes \(c_2^{\mathrm{HET}}\)

**Finding m-2 (MINOR).** The carrier’s ladder unit \(w_i\) (§1.1; at \(i=2\), \(w_2=R_{3,\bar\kappa_2}(\widehat n_2(u_3))\in K_2^\times\)) collides with the A2/ledger-17 HETOW binary carry \(w_2=\lfloor(s(k)+s(k'))/e_2\rfloor\in\{0,1\}\) — two unrelated objects under one symbol.

Rename, following the note’s own \(\gamma_t/\Gamma_t\) precedent (R9-3): T1’s symbol for the HETOW second-level carry is henceforth \(c_2^{\mathrm{HET}}\).

In A2, replace the framing sentence

> With \(w_2=\lfloor(s(k)+s(k'))/e_2\rfloor\), the pinned carry display is

with:

> With \(c_2^{\mathrm{HET}}=\lfloor(s(k)+s(k'))/e_2\rfloor\) — T1’s symbol for HETOW’s second-level carry; the pinned display below writes \(w_2\) for it, and the pinned span stays byte-unchanged: read \(c_2^{\mathrm{HET}}\) for \(w_2\) there — the pinned carry display is

In every NON-PINNED occurrence in the A2 row and its r6 amendments — the \(\mathrm{(H\!-\!HETOW\!-\!LOCAL)}\) boxed displays as replaced by R6-2, the A2 consumption proof as replaced by R6-2 (including its boxed combined wrap formula, which is T1’s own derivation, not a pin), the range-condition insertion, and the closing scope sentence as replaced by R6-2 — read \(c_2^{\mathrm{HET}}\) for \(w_2\). Pinned spans (md5-pinned or quoted closed from the accepted `HETOW`) stay byte-unchanged under the read-as note above.

Supersede honesty-ledger item 17 with:

> 17. The pinned A2 HETOW carry formula uses the supplier range
> \[
> 0\le s(a)<e_2,
> \]
> which makes T1’s carry
> \[
> c_2^{\mathrm{HET}}=\left\lfloor
> \frac{s(k)+s(k')}{e_2}
> \right\rfloor
> \]
> binary. T1 does not assert the displayed linear-in-\(c_2^{\mathrm{HET}}\) formula for a nonbinary carry. SYMBOL NOTE: the accepted `HETOW` and the pinned displays write \(w_2\) for this carry; T1 writes \(c_2^{\mathrm{HET}}\) to avoid collision with the carrier’s ladder unit \(w_i\) (whose \(i=2\) instance \(w_2\in K_2^\times\) is unrelated). Precedent: the R9-3 \(\gamma_t/\Gamma_t\) note.

## R11-5 (m-3) — Define the grade data; unsubscripted \(dv\) reads \(dv_1\)

**Finding m-3 (MINOR).** \(\mu_i\), \(e(\mu_i)\), and the group in which the grades \(\beta\), \(\bar\kappa_i\), \(\beta_t\) live are used but never defined; and (C5)/(C6) write unsubscripted \(dv\).

In §1.1, immediately before the paragraph “For a homogeneous slot of height \(su_{i+1}\), distinguish:”, insert:

> **Grade data (definitions).** Throughout, \(\mu_i\) is the level-\(i\) valuation of the MacLane/Okutsu tower, and \(e(\mu_i)\) is its ramification index over the base valuation — cumulative, so \(e(\mu_1)=e_1\) and \(e(\mu_{i+1})=e_{i+1}\,e(\mu_i)\); the per-stage index over \(\mu_{i-1}\) is \(e_i\), not \(e(\mu_i)\). Heights at level \(i\) — the arguments \(m\) of \(\widehat n_i(m)\) and the values of \(dv_i\) — are integers in the normalization \(dv_i=e(\mu_i)\cdot v\), \(v\) the base-normalized valuation. Grades at level \(i\) — the subscripts \(\beta\) of \(R_{i+1,\beta}\), the ladder grade \(\bar\kappa_i=u_{i+1}/e(\mu_i)\), and the slot grades \(\beta_t=(f_{i+1}-t)\bar\kappa_i\) — lie in the grade group
> \[
> \Gamma_i=\frac{1}{e(\mu_i)}\mathbb Z,
> \]
> with height-to-grade conversion \(\widehat\beta=e(\mu_i)\beta\).

The finding’s sketch read “\(e(\mu_i)\) its ramification index over \(\mu_{i-1}\)”; the definition adopted above is the corpus form instead — cumulative over the base — re-verified this round in the accepted `GENTOW2_PROOF_2026-08-09.md`: \(u_2/e(\mu_2)=u_2/(e_1e_2)\) (so \(e(\mu_2)=e_1e_2\)); \(e_3=e(\mu_3)/e(\mu_2)\); the ladder rows \(dv_1=e(\mu_1)\cdot v\), \(dv_2=e(\mu_2)\cdot v\); \(\Gamma_2=\tfrac12\mathbb Z\) at \(e(\mu_2)=2\). It is this form that the note’s own displays use.

Unsubscripted \(dv\): in the (C5) display, replace

> k=dv(A),

with

> k=dv_1(A),

and in the (C6) display, replace

> dv(L_M(\lambda))=M

with

> dv_1(L_M(\lambda))=M

Reading rule for the r-round texts that quote these spans (R3-2’s two \(k=dv(A)\) displays, R7-2’s \(dv(\widetilde a)=0\), R9-1’s \(k:=dv(A)\)): every unsubscripted \(dv\) is \(dv_1\), the level-1 grid valuation (\(dv_1(x)=h\), \(dv_1(\pi)=e_1\)); quoted-closed and pinned spans stay byte-unchanged under this rule. The level-2 valuation is always written \(dv_2\).

## Consequential record edits

Append to the honesty ledger:

> 22. The canonical residual read is scalar-valued only by the site obligation (C3-read-codomain); no displayed read axiom forces it — the initial-form read into \(\operatorname{gr}(\mu_i)\) is the standing counterexample (§4.2 check 9). \(w_i\in K_i^\times\) requires BOTH (C3-read-codomain) and (C3-ladder-nonvanishing). At \(i=2\) both are supplied by the accepted GENTOW2 package (S5.1 (R-FGMN) and LEMMA GENTOW2-B\('\)/B\(''\)); at \(i\ge3\) both ride the same named level-general residual-read supplier package, unproved here.

Add to §6:

> | Declared the read codomain ((C3-read-codomain)) and threaded it through the \(w_i\) unit inference, the \(y/w_i\) automorphism, \(\psi_{i+1}^{(w_i)}\), the A7 B-law row, and a new §4.2 codomain tooth; completed the (C7) \(M2\) fence list with the full graded-read bundle; made the front-matter status line self-maintaining (in-place edit of record); renamed the HETOW carry to \(c_2^{\mathrm{HET}}\); defined the grade data \(\mu_i\), \(e(\mu_i)\), \(\Gamma_i=\frac{1}{e(\mu_i)}\mathbb Z\) and fixed unsubscripted \(dv\) to \(dv_1\). | Fable hostile pass, 2026-08-12 r11 (Fable arm) | Repairs 2 GAP and 3 MINOR findings: scalar output of the residual read is now an explicit named obligation with a verified \(i=2\) supplier citation rather than an inference from nonvanishing, and the WELD-M-PKG \(M2\) interface names its complete read fence. |

---

## r12 (2026-08-12): the terminal-valuation binding + 4 typing minors

*(Fable-arm; counter resets.)*

# T1 r12 corrections — 2026-08-12

These edits repair the findings of the latest Fable hostile pass (0 CRITICAL / 1 GAP / 4 MINOR; all mathematics recomputed clean; r11's codomain threading, \(e(\mu)\) form, and check-9 tooth verified): the unbound normalization valuation \(v\) in the r11 grade data (F-1), the \(\Gamma\) symbol collision (m-1), the one-clause \(w_i\in K_i^\times\) gate still standing in honesty-ledger items 2 and 19 (m-2), the R6-2 span whose strict assembly duplicates a sentence (m-3), and the unbound field \(K\) in (C4)/\(\mathrm{(H\!-\!JA\!-\!RES\!-\!CONJ)}\) (m-4). Counter state after this round: the clean-pass counter is RESET (every repair round resets it); the §7 acceptance gate still owes TWO consecutive clean hostile passes; the machine battery, green at its r-early state, is inherited evidence only, pending re-run against the current effective text.

## R12-1 (F-1) — Bind \(v\): the base-normalized terminal tower valuation

**Finding F-1 (GAP).** R11-5's grade data declares heights "integers in the normalization \(dv_i=e(\mu_i)\cdot v\), \(v\) the base-normalized valuation" — but \(v\) is unbound: no clause says which valuation of the tower it is. The natural misreading \(v=\mu_i\) (the level-\(i\) valuation, defined in the same paragraph's opening sentence) FALSIFIES (C1-stage-key-height): on the accepted GENTOW2 witness tower it yields \(dv_2(\Phi_2^{e_3})=20\ne21=u_3\) (displayed below). Only the terminal reading is compatible with the typed stage data.

In the R11-5 §1.1 insertion (the **Grade data (definitions)** paragraph), replace the clause

> are integers in the normalization \(dv_i=e(\mu_i)\cdot v\), \(v\) the base-normalized valuation.

with:

> are integers in the normalization \(dv_i=e(\mu_i)\cdot v\), where \(v\) is the base-normalized TERMINAL valuation of the tower — GENTOW2's \(\nu\), the last valuation of the MacLane chain; equivalently \(\mu_{i+1}\) on the consumed elements — and NOT the level-\(i\) valuation \(\mu_i\). On level-\(i\)-free elements (degree \(<\deg\Phi_i\), \(\Phi_i\)-free) the readings agree, \(\mu_i=v\) there (GENTOW2's standing Prop 1.9 cite); on the consumed powers of the stage key they differ, and only the terminal reading satisfies (C1-stage-key-height).

Immediately after the **Grade data (definitions)** paragraph (as amended above and by R12-2), insert:

> **Terminal-binding verification (the accepted `GENTOW2_PROOF_2026-08-09.md` witness tower, S2 dictionary, genre \((2,1,4)\to(2,1,2)\)).** There \(e(\mu_2)=4\), \(e_3=2\), \(\nu(\Phi_2)=w_3+\lambda_3=\tfrac{21}{8}\), \(\kappa_3=e(\mu_2)\,\nu(\Phi_2)=\tfrac{21}{2}\), and \(u_3=e_3\kappa_3=21\). Under the terminal binding \(v=\nu\ (=\mu_3)\),
> \[
> dv_2\!\left(\Phi_2^{e_3}\right)
> =
> e(\mu_2)\cdot e_3\cdot\nu(\Phi_2)
> =
> 4\cdot2\cdot\tfrac{21}{8}
> =
> 21
> =
> u_3,
> \]
> which is exactly (C1-stage-key-height) at \(i=2\). Under the reading \(v=\mu_2\), the key value drops to \(\mu_2(\Phi_2)=w_3=\nu(\Phi_2)-\lambda_3=\tfrac{5}{2}\) — recomputed this round on the S2 witness: on the \(\Phi'\)-expansion \(\Phi_2=\Phi'^2-4x\), \(\mu_2(\Phi'^2)=2\cdot\tfrac{5}{4}=\tfrac{5}{2}=\mu_1(-4x)\), so \(\mu_2(\Phi_2)=\tfrac{5}{2}\); consistency: \(\lambda_3=\tfrac{21}{8}-\tfrac{5}{2}=\tfrac{1}{8}>0\) with \(e_3=\operatorname{denom}(e(\mu_2)\lambda_3)=\operatorname{denom}(\tfrac{1}{2})=2\), matching the S2 row — so
> \[
> dv_2\!\left(\Phi_2^{e_3}\right)\Big|_{v=\mu_2}
> =
> 4\cdot2\cdot\tfrac{5}{2}
> =
> 20
> <
> 21
> =
> u_3,
> \]
> FALSIFYING (C1-stage-key-height). The unbound clause admitted this reading; the terminal binding excludes it.

## R12-2 (m-1) — Rename the grade group: \(\Lambda_i\), not \(\Gamma_i\)

**Finding m-1 (MINOR).** R11-5's grade group \(\Gamma_i=\frac{1}{e(\mu_i)}\mathbb Z\) collides with the carrier's coherent digits \(\Gamma_t\) ((C3); R1's \(\gamma_t\to\Gamma_t\) rename) and with the F4-JOINT digit tuple \((\Gamma_2,\Gamma_1,\Gamma_0)\): under the \(\Gamma_i\) spelling, \(\Gamma_2\) names both the F4-JOINT digit and the level-2 grade group.

In the R11-5 **Grade data (definitions)** insertion, replace

> lie in the grade group
> \[
> \Gamma_i=\frac{1}{e(\mu_i)}\mathbb Z,
> \]
> with height-to-grade conversion \(\widehat\beta=e(\mu_i)\beta\).

with:

> lie in the grade group
> \[
> \Lambda_i=\frac{1}{e(\mu_i)}\mathbb Z,
> \]
> with height-to-grade conversion \(\widehat\beta=e(\mu_i)\beta\). SYMBOL NOTE: the grade group is written \(\Lambda_i\), NOT \(\Gamma_i\), to avoid collision with the coherent digits \(\Gamma_t\) of (C3) and the F4-JOINT digit tuple \((\Gamma_2,\Gamma_1,\Gamma_0)\). The accepted `GENTOW2` writes \(\Gamma_i\) for this group (\(\beta\in\Gamma_2\) throughout; \(\Gamma_2=\tfrac12\mathbb Z\) at its N1 worked frame, where \(e(\mu_2)=2\)): read GENTOW2's \(\Gamma_i\) as T1's \(\Lambda_i\). Precedent: the R9-3 \(\gamma_t/\Gamma_t\) note and the R11-4 \(c_2^{\mathrm{HET}}\) note.

and in R11-5's verification sentence ("The finding's sketch read …"), replace

> \(\Gamma_2=\tfrac12\mathbb Z\) at \(e(\mu_2)=2\)

with

> \(\Lambda_2=\tfrac12\mathbb Z\) at \(e(\mu_2)=2\) (GENTOW2 writes \(\Gamma_2\))

The r11 §6 row's "\(\Gamma_i=\frac{1}{e(\mu_i)}\mathbb Z\)" is a historical record of what r11 wrote and stays byte-unchanged; the effective symbol is \(\Lambda_i\).

## R12-3 (m-2) — The two-clause gate in honesty-ledger items 2 and 19

**Finding m-2 (MINOR).** Items 2 and 19 (their effective r8 forms) still name (C3-ladder-nonvanishing) as the sole gate for \(w_i\in K_i^\times\); after R11-1 the gate is two-clause — (C3-read-codomain) places \(w_i\in K_i\), (C3-ladder-nonvanishing) makes it nonzero (ledger item 22, §4.2 check 9).

Supersede honesty-ledger item 2 with:

> 2. The B-law is conditional on the sitewise graded read facts (C3-ladder-multiplicativity), (C3-slot-grade), and (C3-graded-scalar-covariance). For a zero coherent digit, the displayed homogeneous component is zero and its read is governed separately by (C3-zero-read). The assertion \(w_i\in K_i^\times\), and hence the unit-rescaling and factor-pattern argument, additionally require BOTH independent site obligations (C3-read-codomain) (placing \(w_i\in K_i\)) and (C3-ladder-nonvanishing) (making it nonzero); neither alone yields a unit. T1 proves none of these facts for all homogeneous initial forms.

Supersede honesty-ledger item 19 with:

> 19. The displayed residual-read axioms do not imply that the base ladder read is a nonzero \(K_i\)-scalar. The status \(w_i\in K_i^\times\) is asserted only at sites carrying BOTH (C3-read-codomain) and (C3-ladder-nonvanishing) — at \(i=2\) supplied by the accepted GENTOW2 package (S5.1 (R-FGMN) for the codomain, LEMMA GENTOW2-B\('\)/B\(''\) for nonvanishing), at \(i\ge3\) by an explicitly cited level-general analogue carrying both clauses.

## R12-4 (m-3) — Re-declare the R6-2 span through the substitution sentence

**Finding m-3 (MINOR).** R6-2's directive replaces the A2 consumption paragraph "The supplier relation … and two applications of (C5-carry) give" THROUGH ITS DISPLAYED EQUALITY; but the original (R5-2) text continues past that equality with the sentence "Substitution of \(\tau(k)=\eta^{-Q(m(k))}\) proves the pinned \(\tau\)-ratio.", and R6-2's replacement text supplies the same sentence again before its binary-carry scope note. Strict assembly therefore renders the sentence twice.

Re-declare the span (the replacement text is unchanged): the span replaced by R6-2 runs from the paragraph opening "The supplier relation" through the original trailing sentence "Substitution of \(\tau(k)=\eta^{-Q(m(k))}\) proves the pinned \(\tau\)-ratio." INCLUSIVE — not merely through the displayed equality. Under the re-declared span the strict assembly carries the sentence exactly once, i.e. the effective A2 text every round since r6 has read.

## R12-5 (m-4) — Bind \(K\) in (C4)/\(\mathrm{(H\!-\!JA\!-\!RES\!-\!CONJ)}\)

**Finding m-4 (MINOR).** The R2-2 replacement in (C4) quantifies over "\(H,P,Q\in K[y]\)" and "\(a,b\in K^\times\)" with \(K\) unbound — no clause in the effective (C4) names the field.

In the R2-2 insertion in (C4), immediately after the \(\mathrm{(H\!-\!JA\!-\!RES\!-\!CONJ)}\) boxed display and before the paragraph "Under \(\mathrm{(H\!-\!JA\!-\!RES\!-\!CONJ)}\), multiplication by \(y^\nu\) translates exponent support…", insert:

> Typing: \(K\) is the ambient residue field of the level under comparison — at a level-\(i\) JA harness/print site, \(K=K_i\), the field carrying that site's residuals \(H,P,Q\in K_i[y]\) and units \(a,b\in K_i^\times\). The A5 consumption instantiates \(K=K_2\).

## Consequential record edits

Add to §6:

> | Bound the grade-data normalization \(v\) to the base-normalized terminal tower valuation, with the GENTOW2 witness displayed (\(dv_2(\Phi_2^{e_3})=4\cdot2\cdot\tfrac{21}{8}=21=u_3\); the \(v=\mu_2\) reading gives \(20<21\) and falsifies (C1-stage-key-height)); renamed the grade group to \(\Lambda_i\) (GENTOW2's \(\Gamma_i\); translation noted); superseded honesty-ledger items 2 and 19 with the two-clause \(w_i\in K_i^\times\) gate ((C3-read-codomain) + (C3-ladder-nonvanishing)); re-declared the R6-2 replacement span through the original substitution sentence; bound \(K\) in (C4)/\(\mathrm{(H\!-\!JA\!-\!RES\!-\!CONJ)}\) to the ambient residue field of the level under comparison (A5: \(K=K_2\)). | Fable hostile pass, 2026-08-12 r12 (Fable arm) | Repairs 1 GAP and 4 MINOR findings: the height normalization now names its valuation — the terminal reading verified and the \(\mu_i\) reading falsified on the GENTOW2 witness — and the remaining loose symbols (\(\Gamma\), \(K\)) and the one-clause ledger gate are bound to their typed referents. |

---

## r13 (2026-08-13): the base §3 table retired + five span re-declarations + the value-group re-scope

*(Opus/Claude arm; counter resets.)*

# T1 r13 corrections — 2026-08-13

These edits repair the findings of the latest hostile pass (0 CRITICAL / 3 GAP / 5 MINOR; report `runs/comp13/T1P11_output.log`): the base §3 absorption-map TABLE, which no round ever retired (A-1); R2-2's undeclared span end, which double-renders the (C4-support) box unfenced (A-2); R2-4's span start, which orphans the clearance lead-in (A-3); three further span-boundary defects of exactly the family R12-4 opened (A-4, A-5, A-6); honesty-ledger item 4's surviving one-clause \(w_i\) gate (B-1); and the grade-data clause "the values of \(dv_i\) … are integers", falsified by r12's own witness under r12's own binding (C-1).

CHARACTER OF THE ROUND: every repair below is a span declaration, a relocation, a scope narrowing, or a typing correction. No formula changes, no new absorption, no strengthening — all eight findings are strict-assembly, ledger-coherence, or typing defects. The pass independently re-derived and CONFIRMED the r10–r12 mathematics — R12-1's terminal binding and both legs of its GENTOW2 witness (\(4\cdot2\cdot\tfrac{21}{8}=21=u_3\); the \(v=\mu_2\) leg re-derived from \(\Phi_2=\Phi'^2-4x\) giving \(20<21\)), all nine classes of grade-data consumer, the completeness of the r10 \(\mathrm{(H\!-\!VARTHETA\!-\!RES)}_i\) propagation, 7/7 md5 pins recomputed from git under the R9-5 normalization, and the A2/A6/A7 byte-level spot checks including the \(\Theta=\vartheta^{-1}\) orientation — so nothing in (C1)–(C7), in the SPAN PINs, or in the consumption checks is touched here.

Counter state after this round: the clean-pass counter is RESET (every repair round resets it); the §7 acceptance gate still owes TWO consecutive clean hostile passes; the machine battery, green at its r-early state, is inherited evidence only, pending re-run against the current effective text.

**Landmark-uniqueness convention (r13).** Every span landmark declared below was grep-verified this round, and its count is recorded at the point of declaration. Counts are taken over the note AS IT STOOD BEFORE THIS r13 SECTION — lines 1–3951, i.e. through the last line of r12 — because the directives below necessarily quote each landmark a second time. The counts are therefore reproducible verbatim with

```
sed -n '1,3951p' T1_GAUGE_COCYCLE_2026-08-12.md | grep -Fc '<landmark>'
```

All thirty-three recorded counts were re-run under exactly that command after this section was appended, and all reproduce. A recorded count of 2 means the second occurrence is an earlier r-round directive's own quotation of the landmark; in that case the declaration binds the base occurrence, and this is stated at the declaration.

## R13-1 (A-1) — Retire the base §3 absorption-map table; relocate the A1 rows into an A1 block

**Finding A-1 (GAP).** "r2's 'Replacement §3' never retires the base §3 TABLE. The stale A2-A7 rows survive alongside the r2 prose blocks and still label the absorptions 'Verbatim' — including the B-law row that four later rounds fenced." The pass exhibits a direct self-contradiction inside §3 — the surviving base row

> | A7 GENTOW2 | S5.2 B-law | C3 | **Verbatim** after the explicit inverse orientation \(\Theta=\vartheta^{-1}\), at sites where ladder multiplicativity is discharged. |

against the effective A7 block's own closing sentence, "Thus the B-law is no longer labeled 'absorbed verbatim.'" — and the two surviving A2 rows, which claim VERBATIM absorption of exactly the displays whose effective consumption check imports \(\mathrm{(H\!-\!HETOW\!-\!LOCAL)}\). The table is proved live by two independent later directives: R2-4 amends "the second A1 absorption row", and R5-1e / R7-1d / R8-2 edit the supporting-context paragraph that follows the table.

### (a) Span re-declaration

Re-declare the span (the r2 replacement text is unchanged). The span replaced by the r2 directive under `# Replacement §3 — Exact-span absorption map`,

> Replace the introductory paragraphs of §3 with:

runs from the §3 opening paragraph

> “Verbatim” means that, after replacing local names by the displayed T1 names, the certified local mathematical display is an immediate specialization with no added hypothesis or conclusion.

THROUGH THE FINAL ROW OF THE ABSORPTION-MAP TABLE,

> | A7 GENTOW2 | Factor-pattern invariance | C3 | **Verbatim**: \(\psi^{(w)}=w^f\psi(y/w)\). |

INCLUSIVE — i.e. through both introductory paragraphs, the table header line, the table separator line, and all seventeen table rows. The span STOPS THERE. Everything after the last row is OUTSIDE it and survives unchanged, in particular the bullet list opened by

> Supporting context, not counted as a separate A1–A7 annex:

and the supporting-context paragraph that follows the list — the paragraph edited by R5-1e, R7-1d and R8-2, whose effective (R8-2) form is preserved verbatim.

Landmark uniqueness (counts per the r13 convention above): the §3 opening paragraph landmark `“Verbatim” means that, after replacing local names by the displayed T1 names` — **1**; the final-row landmark `| A7 GENTOW2 | Factor-pattern invariance | C3 | **Verbatim**: \(\psi^{(w)}=w^f\psi(y/w)\). |` — **1**; the stop landmark `Supporting context, not counted as a separate A1–A7 annex:` — **1**; the table header line `| Annex | Local site | T1 conclusion | Mode and specialization |` — **1**.

### (b) The two A1 rows are relocated, not retired

A1 is the one annex that was NOT re-scoped at r2: the r2 header records the strict consumption-check result as "A1 pass; A2–A7 re-scoped to pinned gauge subclaims per the blueprint's non-row-annex provision", so r2 wrote prose blocks for A2–A7 only and left A1 in row form. R2-4 amends the second of those rows. The retirement therefore relocates them rather than deleting them.

In the replacement §3 absorption map, immediately after the **Pin normalization convention (md5).** paragraph inserted by R9-5, and immediately before the heading

> ## A2 — HETOW

insert:

> ## A1 — GENHN
>
> **RETAINED ROW FORM.** A1 is the one annex whose strict consumption check passed unchanged at r2 and was therefore not re-scoped to a pinned-span block. Its two rows are retained here byte-unchanged from the retired base table; no A1 absorption status is enlarged, narrowed, or re-derived by the relocation. The row-form requirement of this map's introduction — "Each row must have the form [specified T1 clause \(\Longrightarrow\) quoted pinned subclaim]" — governs the re-scoped A2–A7 blocks, whose **SPAN PIN** plus boxed **Consumption check** supply exactly that form; it is not a fresh obligation discharged by the two retained A1 rows, and T1 asserts no A1 consumption beyond what those two rows state.
>
> | Annex | Local site | T1 conclusion | Mode and specialization |
> |---|---|---|---|
> | A1 GENHN | GENHN-LIFT | C6 | **Verbatim** on \(M>D'h\): same component formula, integrality, degree, exact height, and residue. |
> | A1 GENHN | Corrected T(b)\('\) coefficient | C2, C3, C6 | **Verbatim** with \(M=(f_2-t)u_2\): \(L_M(c_t\eta^{W(t)})\); the clearance bound is retained. |
>
> R2-4's amendment is unaffected by the relocation and applies here: "the second A1 absorption row" is the second row of THIS block, and by R2-4 it must consequently end "T1 absorbs the corrected coefficient and its exact-lift properties. The clearance sentence is retained only by the explicit citation \(\mathrm{(H\!-\!GENHN\!-\!CLEAR)}\), not as a T1 consequence."

Landmark uniqueness: `## A2 — HETOW` — **1**; `**Pin normalization convention (md5).**` — **1**; `| A1 GENHN | GENHN-LIFT | C6 |` — **1**; `| A1 GENHN | Corrected T(b)\('\) coefficient | C2, C3, C6 |` — **1**.

### (c) Disposition of every retired row

Each retired row asserted an ABSORPTION STATUS; retiring it therefore withdraws a claim and cannot strengthen the note. Where the row's content is carried by an effective A-block, this is a relocation of status into the block that already re-scoped it; where it is not, the claim is WITHDRAWN and that is said. No proof, clause, or consumption check outside §3 derives anything from a table row. The only two directives in r1–r12 that target the table are R2-4 (handled in (b) above) and R1-3 (handled in the table below); the only other places where A-rows are referred to outside §3 — §6's annex-effect column and §7's eighth attack — are addressed in (d) and (e).

| Retired base row | Where its content now lives |
|---|---|
| A2 HETOW · Wrap/carry preamble | A2 block: the three pinned HETOW displays, the \(\mathrm{(H\!-\!HETOW\!-\!LOCAL)}\) supplier interface (R5-2, R6-2), the boxed consumption check, and the closing scope sentence. The "Verbatim" label is withdrawn: the block's own scope sentence names the bridge, \(m\), the canonical range \(0\le s(a)<e_2\), the binary carry \(c_2^{\mathrm{HET}}\in\{0,1\}\) (R11-4) and the identification of \(\tau\) as imported HETOW facts. |
| A2 HETOW · Telescope and corrected key | A2 block, same displays and consumption check; the positive \(\eta^{W(t)}\) sign is (C2)/(C3) carrier text and is unaffected. |
| A3 GENTOW1 · Corrected coefficient pin | A3 block: the SPAN PIN displays, the R6-1 zero-coefficient branch, the R9-3 \(\gamma_t/\Gamma_t\) naming note, and the boxed consumption check. |
| A3 GENTOW1 · Value-blind budgets/floors | A3 block, **Residual obligation**: "Equal exact height only says that an already-established value-blind budget is unchanged by the gauge correction," with the budget floors themselves left to the GENTOW1/GENHN-2\('\)/HE6 suppliers. |
| A4 GENTOW3 · Gauge-annex corrected key | A4 block: the pinned corrected-key display on the live domain, with its consumption check. |
| A4 GENTOW3 · \(x\)-free rescope | A4 block: the pinned \(x\)-free display \(\iff i(M)=0\) and \(\lambda\in\mathbf F_Q\), with its consumption check; the withdrawal of full-slot claims below \(D'h\) is carrier text (§1.1) and ledger item 6. |
| A5 GENTOW4 · S0 naive key | A5 block: the pinned S3 corrected-key bridge on the displayed live domain \((f_2-t)u_2>D'h\); the corrected-versus-naive digit distinction is (C3) carrier text. |
| A5 GENTOW4 · 4.1(c)/S3 bridge | A5 block: the same pin plus the separately pinned attained-origin equation \(z^{t_{\mathrm{Def}}}=z^\nu\varepsilon(\beta)\) and the sentence "Any support comparison additionally cites \(\mathrm{(H\!-\!JA\!-\!RES\!-\!CONJ)}\)." |
| A5 GENTOW4 · BOX-3 no-\(\eta\) axis | WITHDRAWN as an absorption claim (narrowing). No A5-block equivalent is supplied and none is claimed; the live instrument requirement in its neighbourhood is §4.2 check 5 (full orientation tooth, all three entries of the canonical \(\mu=3\) vector) together with the standing gauge-naive and inverse-orientation teeth. T1 now absorbs nothing from GENTOW4's BOX-3 statement. |
| A5 GENTOW4 · S4 residue-one relation (as replaced by R1-3) | Honesty-ledger item 8 (r1 form), which carries the content in full: "Under the stated carrier, \(\eta=1\) forces \(K_1=\mathbf F_Q\) and \(f_1=1\); these are not independent specialization axes. The condition \(\eta=1\) removes the level-one wrap correction, but it does not by itself make arbitrary digits \(x\)-free, because (C6-x-free) still requires \(i(M)=0\)." R1-3's row-replacement directive is hereby HISTORICAL: its target row no longer exists in the effective text. R1-3's other repair (ledger item 8) is untouched and remains the live carrier of the correction. |
| A6 GENTOW6 · Corrected coefficient/full support | A6 block: R6-1's actual-support display \(\operatorname{Supp}_xL_M(\lambda)\), the exact-height statement for \(\lambda\ne0\), and the zero branch. |
| A6 GENTOW6 · 6.3 scalar read | A6 block: the **SPAN PIN (scalar read; provenance HE6 F-1)** as re-attributed by R9-1, the \(\gamma_k(A)\) displays, the retained GENTOW6 S6.1 lift pin, and ledger item 20. |
| A7 GENTOW2 · S5.1 letter formula | A7 block: **SPAN PIN 1** (the level-two letter display) with its consumption check. |
| A7 GENTOW2 · S5.2 B-law | A7 block: the **B-law classification** in its effective R5-1 / R8-2 / R11-1 form, together with the retained supplier display re-anchored by R13-6 below. This row's "Verbatim" label is precisely what the block retires. |
| A7 GENTOW2 · Factor-pattern invariance | A7 block: **SPAN PIN 2** with R9-4's scoped consequence list (irreducible-factor degrees and multiplicities are NOT in the pinned span), and honesty-ledger item 4 in its R13-7 form. |

### (d) Status authority

After this retirement the effective text contains exactly ONE authoritative A-row status list: §3's A1 block (two rows) together with the A2–A7 pinned-span blocks. §6's "Annex effect" column is a historical change log of the 2026-08-10 \(\to\) revision delta, not an absorption-status list — the R12-2 precedent for §6 ("The r11 §6 row's … is a historical record of what r11 wrote and stays byte-unchanged") applies to every §6 row. Where a §6 annex-effect phrase (for example "A1 and A2 are verbatim") disagrees with a §3 A-block, THE §3 BLOCK GOVERNS, and the §6 rows stay byte-unchanged as record.

### (e) Reading rule for §7 attack 8

In §7's eighth attack, "the corresponding T1 row" reads as the corresponding §3 A-row (A1) or A-block (A2–A7). No attack is added or removed.

## R13-2 (A-2) — Declare R2-2's span end; (C4-support) renders exactly once

**Finding A-2 (GAP).** "R2-2's span has no declared end; strict assembly double-renders the (C4-support) box and leaves the UNFENCED summary sentence standing, contradicting effective honesty-ledger item 5." The pass records `\tag{C4-support}` at file lines 513 and 1476, "only one inside a declared span", and notes that the second rendering "carries NO supplier fence … and it defeats the entire purpose of R2-2". Same defect family as R12-4, worse consequence.

Re-declare the span (the R2-2 replacement text is unchanged). The paragraph replaced by R2-2's directive

> In (C4), replace the paragraph beginning
>
> > If \(H(y)\) is the harness residual and \(P(y)\) the normalized print residual, the corresponding support statement is …

runs from that lead-in sentence THROUGH the closing sentence pair

> Attained abscissas and normalized support widths agree. Ordinary exponent supports and ordinary degrees agree only after translating the harness origin by \(\nu\).

INCLUSIVE — that is, the span is all four base blocks of the (C4) tail: the lead-in sentence; the display \(H(y)=y^\nu Q(y),\ P(y)=aQ(by),\ a,b\in K^\times\); the connective "Thus, for nonzero residuals,"; the boxed (C4-support) display; and the closing sentence pair. The span must reach the end because R2-2's replacement re-supplies every one of these items inside the \(\mathrm{(H\!-\!JA\!-\!RES\!-\!CONJ)}\) fence: the two polynomial identities appear in the hypothesis box, the (C4-support) box is re-displayed under "Hence", and the closing sentence returns in its fenced form "Thus attained abscissas and normalized support widths agree at sites carrying the supplier comparison. Neither the polynomial identities nor their support consequences follow from (C4-origin) alone."

Under the re-declared span the strict assembly renders `\tag{C4-support}` EXACTLY ONCE, inside the fence, and no unfenced "Attained abscissas …" sentence survives — the effective (C4) that honesty-ledger item 5 (r2 form) prices, and the one R12-5's typing insertion assumes.

Landmark uniqueness: the end landmark `Ordinary exponent supports and ordinary degrees agree only after translating the harness origin by` — **1**; the interior connective `Thus, for nonzero residuals,` — **1**; the start landmark `If \(H(y)\) is the harness residual and \(P(y)\) the normalized print residual, the corresponding support statement is` — **2**, the second being R2-2's own quotation of it, so the declaration binds the base occurrence; `\tag{C4-support}` — **2**, of which exactly one (R2-2's replacement) is live after this declaration, the other now lying inside the retired span.

## R13-3 (A-3) — Declare R2-4's span start at the clearance lead-in

**Finding A-3 (GAP).** "R2-4's span starts at the (C6-clearance) BOX, orphaning its lead-in sentence — which asserts the clearance unfenced, contradicting the replacement text placed immediately after it and ledger item 10." Assembled, the effective (C6) read "… clears the outer side by at least" immediately followed by "The exact-lift theorem above contains no definition of \(\Phi'\) … Consequently it proves no clearance estimate by itself" — a sentence truncated at "by at least", its object deleted, followed by a flat denial of the assertion it just made.

Re-declare the span (the R2-4 replacement text is unchanged). The text replaced by

> Replace (C6-clearance) and its following collection sentence with:

BEGINS at the conditional lead-in

> If the tower additionally has

and runs through the collection sentence

> Collection and \(\Phi'\)-carry can cancel terms or move them upward, but cannot create a term below that side.

INCLUSIVE — that is, the span is: the lead-in sentence, the display \(u_2>e_2D'h\), the boxed (C6-clearance) display, and the collection sentence.

Nothing is lost by the extension, and this is exactly why the extension is forced: R2-4's replacement re-supplies all three assertions INSIDE the \(\mathrm{(H\!-\!GENHN\!-\!CLEAR)}\) box — the hypothesis \(u_2>e_2D'h\), the bound \(\frac{r(u_2-e_2D'h)}{e_1}>0\), and "collection and \(\Phi'\)-carry can only cancel terms or move them upward" — so leaving the lead-in outside the span leaves the same assertion standing a second time, unfenced, in the one place ledger item 10 (r2 form) forbids it: "outer-side clearance is available only through the named supplier input \(\mathrm{(H\!-\!GENHN\!-\!CLEAR)}\)."

Landmark uniqueness: the start landmark `If the tower additionally has` — **1**; the end landmark `Collection and \(\Phi'\)-carry can cancel terms or move them upward, but cannot create a term below that side.` — **1**; the interior phrase `clears the outer side by at least` — **2**, of which exactly one (inside R2-4's supplier box) is live after this declaration, the other now lying inside the retired span.

## R13-4 (A-4) — Re-declare the R4-2 span through the trailing level-1 sentence

**Finding A-4 (minor).** "R4-2 mis-quotes the base paragraph boundary; strict assembly renders 'At level 1, conclusion (C6) supplies this … when \(m>D'h\)' TWICE. Exact R12-4 sibling." The base paragraph is one paragraph of two sentences; R4-2's from-text quotes it as ending at the first, and R4-2's replacement text re-supplies the second in the wording "supplies this contract uniformly".

Re-declare the span (the R4-2 replacement text is unchanged): the text replaced by R4-2 in §1.1 runs from

> Whenever an exact-height lift is invoked, assume it lies in its stated integral domain and satisfies

through the COMPLETE base paragraph

> Zero is lifted as zero. At level \(1\), conclusion (C6) supplies this lift uniformly when \(m>D'h\).

INCLUSIVE OF ITS SECOND SENTENCE — not merely through "Zero is lifted as zero." Under the re-declared span the strict assembly carries that sentence exactly once, in R4-2's wording ("supplies this contract uniformly when \(m>D'h\)"), i.e. the effective §1.1 text every round since r4 has read. Same defect and same mechanism as R12-4; this is the sibling that round did not hunt.

Landmark uniqueness: the end landmark `conclusion (C6) supplies this lift uniformly when` — **1** (the base occurrence, now inside the span); the R4-2 replacement's own form `conclusion (C6) supplies this contract uniformly when` — **1**; the start landmark `Whenever an exact-height lift is invoked` — **2**, the second being R4-2's own quotation of it, so the declaration binds the base occurrence.

## R13-5 (A-5) — Reattach the general-stage-data \(\psi_{i+1}\) display (the unrepaired R5-3 sibling)

**Finding A-5 (minor).** "R3-1's insertion point splits the general-stage-data sentence, orphaning 'and \[\psi_{i+1}(y)=…\]'. Exact R5-3 sibling, unrepaired." Base §1.1's general-level sentence spans two displays; R3-1 inserts between them, and R4-1 and R8-1 then stack two further paragraphs at the same point, so the connective "and" and the \(\psi_{i+1}\) display are stranded after three inserted blockquotes. R5-3 repaired precisely this defect for R1-1's basis datum; the R3-1 instance was never repaired.

Repair by the R5-3 mechanism. In the integrated application of R3-1 — and of the R4-1 and R8-1 insertions stacked at the same anchor — replace the detached text

> and
> \[
> \psi_{i+1}(y)
> =
> y^{f_{i+1}}-\sum_{t<f_{i+1}}c_ty^t
> \in K_i[y],
> \qquad c_0\ne0.
> \]

with:

> Fix also, as part of the same stage data,
> \[
> \psi_{i+1}(y)
> =
> y^{f_{i+1}}-\sum_{t<f_{i+1}}c_ty^t
> \in K_i[y],
> \qquad c_0\ne0.
> \]

Equivalently, the R3-1 / R4-1 / R8-1 insertions may be placed after the original complete sentence ending with the \(\psi_{i+1}\) display. The display is byte-unchanged; only the dangling connective "and" is replaced by a self-standing lead-in. No mathematical content changes — in particular no property of \(\psi_{i+1}\) beyond what the display itself shows is asserted by the lead-in.

Landmark uniqueness: the display landmark `y^{f_{i+1}}-\sum_{t<f_{i+1}}c_ty^t` — **1**; `\psi_{i+1}(y)` — **2**, the second being an unrelated §2.2-side derivation line `&=\psi_{i+1}(y),\\`, so the declaration binds the §1.1 display, uniquely identified by the first landmark.

## R13-6 (A-6) — Declare R8-2's A7 span narrow; re-anchor the retained supplier display

**Finding A-6 (minor).** "R8-2's A7 'residual-obligation sentence' replacement leaves the pinned B-law display \(u(\beta_t)=\Theta(t)w^{f_3-t}\) with no lead-in (or, on the wide reading, deletes it and strands the phrase 'the supplier identity itself')."

Declare the NARROW reading, and supply the retained display's governing text. The text replaced by R8-2's directive

> In the A7 **B-law classification**, replace the residual-obligation sentence with:

is THE SENTENCE ONLY — in its effective form, i.e. the r2 sentence as amended by R5-1,

> The residual obligation is the accepted GENTOW2-B″ per-grade-unit theorem discharging the slot-grade identity, ladder multiplicativity, and graded scalar covariance for the consumed value-zero factors:

through its terminal colon, EXCLUSIVE of the display that follows it. The per-grade-unit display

\[
u(\beta_t)
=
\Theta(t)w^{f_3-t}.
\]

is RETAINED, byte-unchanged, in place.

To give the retained display the governing text its replaced lead-in used to supply, insert immediately before it — that is, immediately after R8-2's replacement text as amended by R11-1, which ends "and invoke unit-substitution invariance." — the single connective sentence:

> That supplier theorem's per-grade-unit conclusion — the supplier identity referred to below — is

The effective A7 **B-law classification** therefore reads, in order: R8-2's residual-obligation text as amended by R11-1 (codomain plus nonvanishing clauses); this connective lead-in; the retained display \(u(\beta_t)=\Theta(t)w^{f_3-t}\); then the r2 slotwise-cancellation paragraph, unchanged, ending "but it does not prove the supplier identity itself. Thus the B-law is no longer labeled 'absorbed verbatim.'"

The lead-in adds no claim and no content: it names the display as the accepted supplier's conclusion, which is exactly what the surrounding sentences already say — R8-2's text calls that theorem's discharge the residual obligation, and the closing clause explicitly denies that T1 proves the identity. It also fixes the referent that the wide reading would have stranded: "the supplier identity itself" is the displayed \(u(\beta_t)=\Theta(t)w^{f_3-t}\).

Landmark uniqueness: the replaced-sentence opener `The residual obligation is the accepted GENTOW2-B″ per-grade-unit theorem discharging` — **1**; R5-1's amending phrase `the accepted GENTOW2-B″ per-grade-unit theorem discharging the slot-grade identity, ladder multiplicativity, and graded scalar covariance for the consumed value-zero factors` — **1**; the retained display `\Theta(t)w^{f_3-t}` — **1**; the insertion anchor `and invoke unit-substitution invariance.` — **1**; the block opener `T1 only **supplies the gauge algebra to** the preceding B-law display.` — **1**; the closing referent `but it does not prove the supplier identity itself` — **1**.

## R13-7 (B-1) — The two-clause gate in honesty-ledger item 4

**Finding B-1 (minor).** "Ledger item 4 still asserts the factor-pattern conclusion unconditionally, after r8/r11 made it two-clause-conditional and r12 repaired precisely this defect in items 2 and 19." Item 4 is the ledger's own statement of the gated conclusion; the effective §2.3 (R8-2 as amended by R11-1) says "Without (C3-read-codomain), \(y/w_i\) is not defined in \(K_i[y]\); without (C3-ladder-nonvanishing), division by \(w_i\) fails. Neither the automorphism nor the unit-substitution argument is asserted without both."

Supersede honesty-ledger item 4 with (its first two sentences byte-unchanged; the gate appended, textually parallel to the R12-3 forms of items 2 and 19):

> 4. The canonical residual is
> \[
> \psi^{(w)}=w^f\psi(y/w).
> \]
> This preserves factor patterns, not literal coefficients. Both the displayed identity and its factor-pattern conclusion are asserted only at sites carrying BOTH independent site obligations (C3-read-codomain) (placing \(w_i\in K_i\), so that \(y\mapsto y/w_i\) is defined on \(K_i[y]\)) and (C3-ladder-nonvanishing) (making \(w_i\ne0\), so that division by \(w_i\) is available); neither alone yields a unit, and without both neither the automorphism nor the unit-substitution argument is asserted (§2.3, R8-2 as amended by R11-1). Preservation of irreducible-factor degrees and multiplicities is T1's own factor-pattern conclusion at such a site, NOT part of the pinned GENTOW2-B span (R9-4).

Effective ledger after this round: items 1–22, with item 4 in this r13 form; no renumbering, no new item, no collision. The three ledger statements of the \(w_i\in K_i^\times\) gate — items 2 and 19 (r12 forms) and item 22 (r11) — now agree with item 4 and with the carrier.

Landmark uniqueness: the item opener `4. The canonical residual is` — **1**; the superseded item's closing sentence `This preserves factor patterns, not literal coefficients.` — **1**.

## R13-8 (C-1) — Re-scope the grade-data integrality clause to the value group

**Finding C-1 (minor).** "The r11/r12 grade-data clause 'the values of \(dv_i\) … are integers' is FALSIFIED by r12's own witness: \(dv_2(\Phi_2)=21/2\)." Under exactly r12's terminal binding, on exactly R12-1's witness, \(dv_2(\Phi_2)=e(\mu_2)\cdot\nu(\Phi_2)=4\cdot\tfrac{21}{8}=\tfrac{21}{2}\notin\mathbb Z\). Before r12 the clause was unfalsifiable because \(v\) was unbound; binding \(v\) terminally is what makes it checkable, and checkable it fails. The pass classifies it minor: "I grepped the effective text for a bare \(dv_i(\Phi_i)\) and found none — every occurrence is \(dv_i(\Phi_i^{e_{i+1}})\) or \(dv_i(\Phi_i^{e_{i+1}t})\), both integral". That grep was re-run independently this round with the same result: every \(dv\) applied to a stage key in the effective text carries the exponent \(e_{i+1}\), \(e_{i+1}s\), \(e_{i+1}t\) or (in the witness) \(e_3\) — there is no bare \(dv_i(\Phi_i)\) consumer, so no consumer of the old clause fails, and NO open obligation is created by the re-scope.

**(i) Scope the clause to the consumed sites.** In the R11-5 §1.1 **Grade data (definitions)** insertion, replace

> Heights at level \(i\) — the arguments \(m\) of \(\widehat n_i(m)\) and the values of \(dv_i\) —

with:

> Heights at level \(i\) — the arguments \(m\) of \(\widehat n_i(m)\), and the values of \(dv_i\) at every site consumed in this note —

The clause that follows (R12-1's terminal binding, "are integers in the normalization \(dv_i=e(\mu_i)\cdot v\), where \(v\) is the base-normalized TERMINAL valuation of the tower … only the terminal reading satisfies (C1-stage-key-height).") is unchanged and is now true as scoped.

**(ii) Declare the actual codomain.** Insert at the END of the same **Grade data (definitions)** paragraph — i.e. immediately after the R12-2 symbol note that now closes it ("… Precedent: the R9-3 \(\gamma_t/\Gamma_t\) note and the R11-4 \(c_2^{\mathrm{HET}}\) note."), and BEFORE the paragraph beginning "**Terminal-binding verification (the accepted `GENTOW2_PROOF_2026-08-09.md` witness tower …" that R12-1 inserts after this paragraph (the order of the two insertions is declared here explicitly, on the R9-2 precedent for pinning one insertion relative to another). Placing it at the end rather than beside the height clause keeps the grade group \(\Lambda_i\) defined before it is used:

> The restriction to consumed sites is necessary, not decorative: \(dv_i\) is NOT integer-valued in general. Write \(r\) for the terminal level, so that \(v=\mu_r=\nu\) and \(e(\mu_r)\) is its ramification index over the base valuation; then \(v\) takes values in \(\Lambda_r=\frac{1}{e(\mu_r)}\mathbb Z\), and therefore
> \[
> \boxed{
> dv_i=e(\mu_i)\cdot v
> \ \text{ takes values in }\
> e(\mu_i)\Lambda_r
> =
> \frac{e(\mu_i)}{e(\mu_r)}\mathbb Z
> \supseteq\mathbb Z,
> }
> \]
> with equality exactly when \(e(\mu_r)=e(\mu_i)\), i.e. when the tower carries no further ramification above level \(i\). In particular (C1-stage-key-height) gives \(dv_i(\Phi_i)=u_{i+1}/e_{i+1}\), which is non-integral exactly when \(e_{i+1}\nmid u_{i+1}\). On the witness of the terminal-binding verification below,
> \[
> dv_2(\Phi_2)
> =
> e(\mu_2)\,\nu(\Phi_2)
> =
> 4\cdot\tfrac{21}{8}
> =
> \tfrac{21}{2}
> =
> \kappa_3
> \notin\mathbb Z,
> \qquad
> \text{while}
> \qquad
> dv_2\!\left(\Phi_2^{e_3}\right)=21=u_3\in\mathbb Z .
> \]
>
> Every \(dv_i\)-value consumed in the effective text is nevertheless an integer, in one of four classes. (i) Typed stage and lift heights: \(dv_i(\pi_{i+1})=1\) and \(dv_i(\pi_{i+1}^{u_{i+1}})=u_{i+1}\) (C1-stage-uniformizer); \(dv_i(\widehat n_i(m))=m\) by exact height; \(dv_i(\operatorname{lift}_i(d;m))=m\) (C3-lift-height); \(dv_i(\widehat k_t)=su_{i+1}\). (ii) Stage-key powers, which are consumed ONLY as \(\Phi_i^{e_{i+1}t}\): \(dv_i(\Phi_i^{e_{i+1}t})=tu_{i+1}\) by (C1-stage-key-height). No clause of this note takes \(dv_i\) of a bare \(\Phi_i^{k}\) with \(e_{i+1}\nmid k\). (iii) Value-zero factors, \(dv_i(g)=0\), and the zero convention \(dv_i(0)=+\infty\) (C3-zero-lift). (iv) The level-one grid, where \(dv_1(x)=h\) and \(dv_1(\pi)=e_1\) are integers and (C5)/(C6) apply \(dv_1\) only to nonzero elements of degree \(<D'=\deg\Phi_1\) (R3-2's \(A\ne0\); R8-1's \(\deg\Phi_1=D'\)), which are level-1-free, so \(\mu_1=v\) there by the clause above. The re-scoped clause therefore costs no consumer, and the grade clause above is unaffected: grades are attached to the integer heights, so \(\bar\kappa_i=u_{i+1}/e(\mu_i)\) and \(\beta_t=(f_{i+1}-t)\bar\kappa_i\) lie in \(\Lambda_i\) as stated.

No honesty-ledger item is added: the clause gates no (C1)–(C7) conclusion (the ledger's standing rule is to price what gates a C-clause), and by the enumeration above every consumed value remains integral. R12-1's displayed witness arithmetic is unchanged — \(\nu(\Phi_2)=\tfrac{21}{8}\), \(\kappa_3=\tfrac{21}{2}\), \(u_3=21\), \(dv_2(\Phi_2^{e_3})=4\cdot2\cdot\tfrac{21}{8}=21=u_3\), and the falsified \(v=\mu_2\) leg at \(20<21\) — and the value \(\tfrac{21}{2}\) displayed above is R12-1's own \(\kappa_3=e(\mu_2)\nu(\Phi_2)\), re-labelled, not a new computation.

Landmark uniqueness: the replaced height-clause opening `the values of \(dv_i\)` — **1** (it occurs only in R11-5's insertion; R12-1's amendment begins after it); the interior of R12-1's retained clause `and NOT the level-\(i\) valuation \(\mu_i\)` — **1**; the end-of-clause anchor `only the terminal reading satisfies (C1-stage-key-height)` — **1**; the end-of-paragraph insertion anchor `Precedent: the R9-3 \(\gamma_t/\Gamma_t\) note and the R11-4 \(c_2^{\mathrm{HET}}\) note.` — **1**; the following-sentence guard `Grades at level \(i\)` — **1**.

**(iii) Battery tooth.** Append to §4.2:

> 10. **Grade-data value group.** Instantiate a witness tower with \(e_{i+1}\nmid u_{i+1}\) — the accepted GENTOW2 S2 tower at \(i=2\) (\(u_3=21\), \(e_3=2\), \(e(\mu_2)=4\), \(e(\mu_3)=8\)) is one — and confirm that \(dv_i(\Phi_i)=u_{i+1}/e_{i+1}\notin\mathbb Z\) while \(dv_i(\Phi_i^{e_{i+1}})=u_{i+1}\in\mathbb Z\). Then score every \(dv\)-site of the effective text against the four consumed classes named in the grade-data paragraph, and fail on any site that consumes a \(dv_i\)-value outside \(\mathbb Z\) or that applies \(dv_i\) to \(\Phi_i^{k}\) with \(e_{i+1}\nmid k\).

Check 10 has never been run; it joins checks 7 and 8 (r8) and check 9 (r11) as scored rows the revised battery owes. §4.2 now carries ten checks, no collisions (base 1–6 with 6 in its R4-3 form, r8's 7–8, r11's 9, r13's 10).

## Consequential record edits

Add to §6:

> | Retired the base §3 absorption-map TABLE by declaring the r2 "Replacement §3" span through its final row, relocating the two A1 rows byte-unchanged into a new **A1 — GENHN** block (R2-4's amendment re-anchored there) and recording the disposition of all fifteen retired rows, so that exactly one authoritative A-row status list survives (§3's A1 rows + the A2–A7 pinned-span blocks; §6's annex-effect column is historical record only); re-declared the R2-2 span through the closing (C4) sentence pair, so the (C4-support) box renders exactly once, inside the \(\mathrm{(H\!-\!JA\!-\!RES\!-\!CONJ)}\) fence; re-declared the R2-4 span back to "If the tower additionally has", so no unfenced outer-side clearance survives; re-declared the R4-2 span through the trailing level-one sentence and reattached the general-stage-data \(\psi_{i+1}\) display (R5-3 mechanism); declared the R8-2 A7 span narrow and re-anchored the retained supplier display \(u(\beta_t)=\Theta(t)w^{f_3-t}\); superseded honesty-ledger item 4 with the two-clause \(w_i\in K_i^\times\) gate; and re-scoped the grade-data integrality clause to the consumed sites, declaring the true codomain \(dv_i\in e(\mu_i)\Lambda_r=\frac{e(\mu_i)}{e(\mu_r)}\mathbb Z\supseteq\mathbb Z\) with the \(dv_2(\Phi_2)=\tfrac{21}{2}\) instance and a new §4.2 check 10. | Opus/Claude hostile pass, `runs/comp13/T1P11_output.log`, 2026-08-13 r13 (Claude arm) | Repairs 3 GAP and 5 MINOR findings, all strict-assembly or ledger-coherence: the effective text no longer asserts any absorption or clearance that the same section denies, every declared span now reaches its actual end, and the height normalization states the value group it actually has. No formula, pin, consumption check, or supplier fence is changed. |

## Counter state and what remains owed

The clean-pass counter is RESET by this round, as by every repair round. The §7 acceptance gate still owes TWO CONSECUTIVE CLEAN HOSTILE PASSES on the effective text as of r13, plus the revised machine battery; the 2026-08-10 sealed run remains inherited evidence only, green at its r-early state and pending re-run, and §4.2's checks 7, 8, 9 and 10 have never been scored.

Standing note for the next pass: r12 opened the strict-assembly surface with R12-4 and repaired one instance; the pass of record found three more of the same family (A-2, A-3, A-4) plus two adjacent orphan defects (A-5, A-6), all now declared. Every "replace"/"insert" directive in r1–r12 was read for a declared end by that pass (its S1 method statement), and every defect it returned is declared above; the four span ambiguities the same pass recorded as NOTED, NOT COUNTED (R2-5's opening-of-(C4) replacement, R7-1c's grammatically bound display, the mutual order of R4-1 and R8-1, and R7-2's §2.6 opening) are left as they stand, both branches being benign, and are named here so a later round does not mistake silence for an unexamined surface.


---

## Post-pass riders (2026-08-13, after the r13 clean-w-minors pass)

**Dated riders (2026-08-13, post-pass-1 — the five minors of the Opus/Claude-arm hostile pass on r13, folded per the campaign's minors-only precedent: T4's post-pass \(\mathfrak M\)-gloss-direction rider and T5's two post-pass-1 locator riders, each folded as riders on a 0C + 0G pass and each subsequently confirmed to 2/2. No grade event, NO r-section, NO counter reset.)** Every rider below is referential, enumerative or scoping: it repairs r13's own directive prose, or a battery instruction, or restores a definition the r13 retirement dropped at a site that still uses it. No formula, no display, no span boundary in effect, no pin, no fence, no hypothesis, no honesty-ledger item and no consumption check is changed, and no absorption status moves. The pass's own verdict slot reads NOT CLEAN on its template's strict reading (any finding of any grade); the campaign precedent above governs the fold, and the counter statement at the end of this block is the operative one.

**Landmark convention (riders).** Counts are taken over the note AS IT STOOD BEFORE THIS RIDER BLOCK — lines 1–4261, i.e. through the last line of r13 — because each rider necessarily quotes its landmark a second time. Each count is a whole-line fixed-string match, reproducible verbatim with

```
sed -n '1,4261p' T1_GAUGE_COCYCLE_2026-08-12.md | grep -cFx '<landmark line>'
```

### Rider 1 (m-1) — reading rule for "The B-law rows" in the preserved supporting-context paragraph

Finding: "R13-1 retires the B-law ROW but preserves verbatim a §3 paragraph whose grammatical subject is that row; no reading rule is supplied."

Cure, referential only, on the R13-1(e) precedent for §7 attack 8's "the corresponding T1 row": in the supporting-context paragraph that R13-1(a) preserves verbatim — the R8-2 replacement as amended by R11-1, opening "The B-law rows consume (C3-ladder-multiplicativity), the grade identity \(\beta_t=(f_{i+1}-t)\bar\kappa_i\), and (C3-graded-scalar-covariance) …" — the subject phrase "The B-law rows" reads as the effective A7 **B-law classification** block, which after the retirement is the note's sole B-law site. The paragraph is byte-unchanged and the obligations it names are unchanged; only its referent is stated.

Landmark: the R8-2 directive line that introduces the paragraph, `Replace the supporting-context paragraph following the absorption map with:` — **1**.

### Rider 2 (m-2) — restore the "Verbatim" definition at the A1 block that still carries the label

Finding: "the relocated A1 rows keep the bolded status label **Verbatim** while the same span retires the only definition of 'Verbatim' in the note."

Cure: in the relocated **A1 — GENHN** block (R13-1(b)), at the end of the **RETAINED ROW FORM** preamble paragraph — i.e. immediately before that block's table header line — add as the preamble's closing sentence:

> The label **Verbatim** in these two rows carries the definition retired with the base table, restored here unchanged for the rows that use it: “Verbatim” means that, after replacing local names by the displayed T1 names, the certified local mathematical display is an immediate specialization with no added hypothesis or conclusion.

This restores a definition rather than supplying a new one, at the one site that still uses the label: it re-pins the two A1 rows to exactly the strength they carried before the retirement and cannot enlarge them. The companion "Adapted" definition is NOT restored, because no surviving row or block carries the bolded **Adapted** mode label — the only such label outside the retired base table is R1-3's replacement A5 row, which lies inside the retired span and is declared HISTORICAL by R13-1(c).

Landmarks: the block heading `> ## A1 — GENHN` — **1**; the block's table header line `> | Annex | Local site | T1 conclusion | Mode and specialization |` — **1**; the restored sentence's base source line `“Verbatim” means that, after replacing local names by the displayed T1 names, the certified local mathematical display is an immediate specialization with no added hypothesis or conclusion.` — **1**.

### Rider 3 (m-3) — R13-3's span enumeration names all five blocks

Finding: "R13-3's explicit span enumeration omits precisely the sentence whose orphaning was finding A-3; read as authoritative it reinstates the defect."

Cure: R13-3's enumeration sentence reads, with the omitted block named:

> INCLUSIVE — that is, the span is, in order, five blocks: the conditional lead-in sentence; the display \(u_2>e_2D'h\); the monomial-clearance sentence "every monomial in this lift, after multiplication by a monomial of \(\Phi'^{e_2t}\), clears the outer side by at least"; the boxed (C6-clearance) display; and the collection sentence.

The span's declared boundaries are unchanged — R13-3's start and end landmarks are untouched, and its landmark paragraph already declared the correct branch (of the two occurrences of `clears the outer side by at least`, the second "now lying inside the retired span"). This rider only makes the enumeration agree with the boundaries R13-3 already declared.

Landmark: the enumeration sentence `INCLUSIVE — that is, the span is: the lead-in sentence, the display \(u_2>e_2D'h\), the boxed (C6-clearance) display, and the collection sentence.` — **1**.

### Rider 4 (m-4) — two block-count slips

(a) In R13-2's span enumeration, the phrase "all four base blocks of the (C4) tail" reads "all five base blocks of the (C4) tail". The five-item list that follows it is complete, unchanged and governs (lead-in sentence; the \(H(y)=y^\nu Q(y),\ P(y)=aQ(by)\) display; the connective "Thus, for nonzero residuals,"; the boxed (C4-support) display; the closing sentence pair), as do R13-2's landmarks; only the numeral was wrong.

(b) R13-6's "reads, in order" list is prefixed with the block's unchanged r2 opening sentence, which R13-6 itself declares as a landmark (count **1**) and does not replace, so that the list reads: the r2 opener "T1 only **supplies the gauge algebra to** the preceding B-law display."; then R8-2's residual-obligation text as amended by R11-1 (codomain plus nonvanishing clauses); this connective lead-in; the retained display \(u(\beta_t)=\Theta(t)w^{f_3-t}\); then the r2 slotwise-cancellation paragraph, unchanged, ending as R13-6 quotes it. Nothing is inserted, replaced or re-anchored by this rider.

Landmarks: (a) the section heading `## R13-2 (A-2) — Declare R2-2's span end; (C4-support) renders exactly once` — **1**; (b) the amended sentence `The effective A7 **B-law classification** therefore reads, in order: R8-2's residual-obligation text as amended by R11-1 (codomain plus nonvanishing clauses); this connective lead-in; the retained display \(u(\beta_t)=\Theta(t)w^{f_3-t}\); then the r2 slotwise-cancellation paragraph, unchanged, ending "but it does not prove the supplier identity itself. Thus the B-law is no longer labeled 'absorbed verbatim.'"` — **1**.

### Rider 5 (m-5) — §4.2 check 10 excludes its own specification (the R4-3 mechanism)

Finding: "the new §4.2 check 10 self-matches: as written it must fail the very paragraph that introduces it. Exact recurrence of the defect R4-3 repaired for check 6."

Cure, in R4-3's own idiom ("Occurrences inside this lint specification, quotations of rejected language, and explicit scope-fence negations are nonmatches"): append to check 10, immediately after its closing "… or that applies \(dv_i\) to \(\Phi_i^{k}\) with \(e_{i+1}\nmid k\).", the self-exclusion and scoring scope:

> Scored sites exclude this numbered check's own instruction text and the value-group declaration's own witness displays and prose in the **Grade data (definitions)** paragraph — the boxed codomain display, the \(dv_i(\Phi_i)=u_{i+1}/e_{i+1}\) sentence, and the \(dv_2(\Phi_2)=\tfrac{21}{2}\) witness display — which exhibit a non-integral \(dv_i(\Phi_i)\) deliberately, as the specification of what this check confirms; occurrences inside that specification are nonmatches. A site is scored only where the note CONSUMES the value: a display standing inside an explicit non-implication ("In particular, T1 does not imply …") is not a consumed site. A consumed value that is integral by additivity of the listed classes — the composed-key product \(dv_i(\widehat k_t\Phi_i^{e_{i+1}t})=(s+t)u_{i+1}\), class (i) plus class (ii) — scores as passing under those classes.

This changes no class, no value and no claim of the R13-8 declaration; it fixes the scorer's target so that the tooth does not fail the note on the tooth's own text, and so that its "score every \(dv\)-site … against the four consumed classes" instruction matches the scope of the integrality claim (consumed values), which the pass of record independently re-derived and confirmed.

Landmark: the directive line that appends the check, `**(iii) Battery tooth.** Append to §4.2:` — **1**.

### Counter state (NOT reset by this block)

These riders repair the five MINOR findings of a hostile pass that returned **0 CRITICAL + 0 GAP + 5 minor**. A minors-only pass is a clean pass whose minors fold as post-pass riders (T4, T5), and folding riders is not a repair round: **the clean-pass counter is NOT reset and STANDS AT 1 OF 2.** Pass of record: the Opus/Claude-arm hostile pass on r13, `runs/comp13/T1P12_output.log`. Still owed at the §7 acceptance gate: the sol confirmation pass — the second of the two consecutive clean passes, on the model-diverse arm, against the effective text as of r13 plus these riders — and the §4.2 battery re-run of checks 1–10 (checks 7, 8, 9 and 10 have never been scored, and the 2026-08-10 sealed run remains inherited evidence only).
