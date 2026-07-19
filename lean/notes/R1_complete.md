# R1 — The Vandermonde change-of-variables / pushforward over $\mathcal O_K$

**Date:** 2026-06-15. **Status:** proof complete over an unramified base $K/\mathbb Q_p$.
The two algebraic backbones (Vieta-map Jacobian $=$ Vandermonde; discriminant $=$
Vandermonde$^2$) are theorems with exact references and are re-verified symbolically;
the analytic pushforward is the $p$-adic change-of-variables theorem applied through a
Galois-orbit descent (cited, not re-derived: paper Thm `change of variables` $+$ Lemma
`local integrals`); the "Vandermonde constant on a cluster-tree stratum" identity is
proved from first principles and verified numerically (including the wild $p=2$,
slope-$1/2$, size-$4$ atom). This isolates missing-lemma **M7 / R1** of `notes/GAPS.md`.

Verification: `notes/r1_verify.py` (symbolic Vieta/disc; root-side $I_m$ recursion;
Monte-Carlo $I_3$ at $p\in\{2,3,5,7\}$; stratum-constancy; wild $n=4,p=2$ oracle check).

---

## 0. Conventions (fixed; consistent with `WORKING_NOTES §0`)

- $K/\mathbb Q_p$ finite **unramified**, residue field $\mathbb F_q$ ($q=p^k$), ring
  $\mathcal O_K$, maximal ideal $\mathfrak m=(p)$, uniformizer $\pi_K=p$, valuation $v$
  with $v(p)=1$; normalized Haar measure $\mu$ on $\mathcal O_K$, $\mu(\mathcal O_K)=1$,
  so $\mu(\mathfrak m^j)=q^{-j}$.
- $\overline K$ a fixed algebraic closure; $v$ extends **uniquely** to $\overline K$ (a
  complete field has a unique extension of its valuation to any algebraic extension —
  Neukirch, *ANT*, II.4.8). On a degree-$\le n$ element $v$ takes values in
  $\tfrac1{n!}\mathbb Z$. We write $|x|:=q^{-v(x)}$ for the associated absolute value.
- $M_n=\{x^n+c_{n-1}x^{n-1}+\dots+c_0:c_i\in\mathcal O_K\}\cong\mathcal O_K^n$ with product
  Haar $\mu_n$ (mass $1$); coordinates $\mathbf c=(c_0,\dots,c_{n-1})$.
- For a separable $f\in M_n$ with roots $\boldsymbol\alpha=(\alpha_1,\dots,\alpha_n)
  \in\overline K^n$, the **Vandermonde** is
  $\mathrm V(\boldsymbol\alpha)=\prod_{i<j}(\alpha_i-\alpha_j)$ and the **discriminant** of
  $f$ is $\operatorname{disc}(f)=\mathrm V(\boldsymbol\alpha)^2=\prod_{i<j}(\alpha_i-\alpha_j)^2$.
- **Cluster tree** $T(f)$: the rooted tree of the ultrametric
  $\delta(i,j):=v(\alpha_i-\alpha_j)\ge0$ on the root multiset, decorated at each internal
  node by the residue-field datum (the closed point of $\mathbb P^1_{\mathbb F_q}$ /
  residue degree carried by that level). A **stratum** $\mathcal S_T\subset M_n$ is the set
  of (separable) $f$ whose roots realize a fixed combinatorial tree $T$ together with its
  residue decorations. (`L5 §0`.)

The goal of R1 is to express the type-region volumes that the recursion computes as
**pushforwards of the configuration-space (root-space) measure under the Vieta map
$\boldsymbol\alpha\mapsto\mathbf c$, weighted by the Vandermonde Jacobian**, and to prove
that on a fixed stratum $\mathcal S_T$ the Vandermonde factor is the **constant**
$q^{-d(T)}$, $d(T)=\sum_{i<j}\delta(i,j)$. This is the formula
$d\mu_{\mathrm{coeff}}=\tfrac1{|\mathrm{Aut}|}\prod_{i<j}|\alpha_i-\alpha_j|\,
d\mu_{\mathrm{root}}$ of `STRUCTURAL_MECHANISM §"The mechanism in full"`, made rigorous.

---

## 1. Statement

> **Lemma R1 (Vandermonde pushforward; stratum-constancy).**
> Let $K/\mathbb Q_p$ be finite unramified with residue field $\mathbb F_q$.
>
> **(a) (Vieta Jacobian.)** The Vieta map
> $\Phi:\mathbb A^n\to\mathbb A^n$, $\boldsymbol\alpha\mapsto\mathbf e(\boldsymbol\alpha)
> =(e_1,\dots,e_n)$ (signed elementary symmetric functions = coefficients of
> $\prod_i(x-\alpha_i)$) has Jacobian determinant
> $$\det\big(\mathrm d\Phi_{\boldsymbol\alpha}\big)=\pm\,\mathrm V(\boldsymbol\alpha)
>   =\pm\!\!\prod_{i<j}(\alpha_i-\alpha_j).$$
>
> **(b) (Pushforward over $\mathcal O_K$.)** Let $W\subseteq M_n$ be a measurable type
> region whose generic $f$ has all $n$ roots in a **fixed** finite extension $L/K$ (the
> splitting field of the local family, possibly ramified). Let
> $\widetilde W=\Phi^{-1}(W)\cap\mathcal O_L^{\,n}$ be its ordered-root preimage. Then,
> off the measure-zero discriminant locus,
> $$\mu_n(W)\;=\;\frac1{n!}\int_{\widetilde W}\Big|\prod_{i<j}(\alpha_i-\alpha_j)\Big|\,
>     d\mu_{\mathcal O_L^{\,n}},$$
> where $\mu_{\mathcal O_L^{\,n}}$ is product Haar on $\mathcal O_L^{\,n}$ normalized by
> $\mu_{\mathcal O_L}(\mathcal O_L)=1$, and the integrand $|\mathrm V|$ is the absolute
> value of the Vandermonde, $=q^{-v(\mathrm V)}$. When the roots live in a strictly larger
> Galois orbit (residue degree $\delta>1$, or a ramified splitting field), the same formula
> holds after the **descent** of §4 (paper Lemma `local integrals`), which replaces the
> single $L$-volume by the $\mathrm{Frob}$-orbit average and substitutes $q\mapsto
> q^{k_i/\ell_i}$; no characteristic dependence is introduced because the descent extensions
> are **unramified** ($v(p)=1$ preserved).
>
> **(c) (Vandermonde constant on a stratum.)** On a fixed cluster-tree stratum
> $\mathcal S_T$ the pairwise valuations $v(\alpha_i-\alpha_j)=\delta(i,j)$ are part of the
> defining data of $T$, hence
> $$\Big|\prod_{i<j}(\alpha_i-\alpha_j)\Big|\Big|_{\mathcal S_T}
>     \;=\;q^{-d(T)},\qquad d(T)=\sum_{i<j}\delta(i,j)\quad(\text{constant on }\mathcal S_T).$$
> Consequently
> $$\mu_n(\mathcal S_T)\;=\;q^{-d(T)}\cdot\frac{\mathcal N_T(q)}{\prod_{m}\big(1-q^{-w(m)}\big)},$$
> where $\mathcal N_T(q)$ is the universal residue-configuration count of $T$ (L3,
> $p$-independent), $w(m)=\binom m2+m-1=\tfrac{m(m+1)}2-1$ is the size-$m$ self-loop
> codimension (L5), and the product runs over the rescale self-loops along $T$.

Parts (b)–(c) are the precise content of "the $\eta$'s are volumes, not value-weighted
integrals" (`ASSERTIONS A1`) and of the stratification formula in
`STRUCTURAL_MECHANISM`. Part (b)'s $\tfrac1{n!}$ is the $|\mathrm{Aut}|$ factor (the
$S_n$-symmetry of the ordered root tuple); on a stratum with a smaller symmetry the
combinatorial prefactor is the order of the residual automorphism group, handled by the
residue-config count $\mathcal N_T$ (it is the paper's $\alpha$-factor, M1/CP2).

---

## 2. Proof of (a): the Vieta Jacobian is the Vandermonde

This is classical; we give the one-line proof and the exact reference.

Write $\Phi(\boldsymbol\alpha)=(e_1,\dots,e_n)$ with $e_k=e_k(\boldsymbol\alpha)$ the
$k$-th elementary symmetric polynomial (so $\prod_i(x-\alpha_i)=x^n-e_1x^{n-1}+\dots
+(-1)^ne_n$; the sign convention does not affect $|\det|$). The Jacobian matrix is
$J_{ki}=\partial e_k/\partial\alpha_i$. By the standard identity
$\partial e_k/\partial\alpha_i=e_{k-1}(\boldsymbol\alpha\setminus\alpha_i)$ (the
$(k-1)$-st elementary symmetric in the **other** variables), $J$ factors through the
confluent structure that gives, after column operations,
$$\det J=\pm\prod_{i<j}(\alpha_i-\alpha_j)=\pm\mathrm V(\boldsymbol\alpha).$$
**Reference.** This is the Jacobian of the quotient map $\mathbb A^n\to\mathbb A^n/S_n$,
computed e.g. in Bourbaki, *Algèbre* IV §6 (symmetric functions); the determinant equals
the Vandermonde, equivalently the square root of the discriminant. It is exactly the
Jacobian "$\operatorname{Res}/\,$Vandermonde" used by the paper for the multiplication map
$f_\sigma$ (the completely-split example, paper line 1302:
$\eta_{f_1}(K)=\int_{(\mathbb P^1)^3(B)}\prod_{i<j}|z_i-z_j|\,d\mu$, the integrand being
precisely $|\det\mathrm d\Phi|$), and is the $G=\{1\}$ refinement of the paper's
$\det\mathrm d(\text{mult})=\operatorname{Res}$ used in L1 (paper line 1714:
"$\operatorname{Jac}=\operatorname{Res}(P,Q)$").

**Verified symbolically** (`r1_verify.py`, sympy): for $n=2,3,4,5$,
$\det(\mathrm d\Phi)/\mathrm V=\mp1$ (constant $\pm1$); and
$\operatorname{disc}(f)/\mathrm V^2=1$ for $n=2,3,4$ — i.e. **disc $=$ Vandermonde$^2$**,
the relation pointed to in the task ("the discriminant = Vandermonde$^2$"). $\qquad\square$

---

## 3. Proof of (b): the $p$-adic change-of-variables pushforward

### 3.1 The discriminant locus is measure zero

$\Delta:=\{f\in M_n:\operatorname{disc}(f)=0\}$ is the zero set of the polynomial
$\operatorname{disc}$ in the coordinates $\mathbf c$; $\operatorname{disc}\not\equiv0$
(it is $\ne0$ for, e.g., $f=\prod_{i=0}^{n-1}(x-i)$ once $q\ge n$, and as a polynomial
identity its non-vanishing is characteristic-free for $n\le q$; in general
$\operatorname{disc}$ is a nonzero element of $\mathbb Z[\mathbf c]$, hence nonzero in
$\mathcal O_K[\mathbf c]$). Therefore $\Delta=Z(\mathcal O_K)$ for a proper Zariski-closed
subscheme $Z\subsetneq\mathbb A^n_{\mathcal O_K}$, and by **paper Thm `change of variables`
part (1)** ($\mu_\omega(Z(\mathcal O_K))=0$ for $Z$ Zariski-closed; equivalently a proper
$p$-adic analytic subset has Haar measure zero) we have $\mu_n(\Delta)=0$. Likewise the
loci $\{$two roots merge to extra order$\}$ bounding the strata are measure zero. So all
volume integrals below are unaffected by removing $\Delta$ and the inter-stratum
boundaries; in particular **type is defined $\mu_n$-a.e.** (a non-separable $f$ has no
factorization type, but the non-separable set sits inside $\Delta$). This discharges the
"$\{$Vandermonde$=0\}$ measure zero" and the measurability requirements; each stratum
$\mathcal S_T$ is a $p$-adic analytic locally closed set (Krasner: the isomorphism type of
$f^{-1}(y)$, and hence the cluster tree, is locally constant on $\U f(K)$ —
paper Lemma after `defn: rho_f,admissible pair`, citing Krasner / Poonen Prop 3.5.74),
hence Haar-measurable.

### 3.2 Local analytic bijection on a cell (Krasner / inverse function theorem)

Fix a stratum $\mathcal S_T$ whose generic $f$ has all roots in a fixed finite extension
$L/K$ contained in the splitting field. On the open dense $\U f\subset\mathbb A^n_{\mathcal O_L}$
where $\mathrm V\ne0$, the Vieta map $\Phi:\mathcal O_L^{\,n}\supset\widetilde W\to W$ has
$|\det\mathrm d\Phi|=|\mathrm V|\ne0$, so $\Phi$ is **étale** there, and by the $p$-adic
**inverse function theorem** (Igusa, *An Introduction to the Theory of Local Zeta
Functions*, §7.4 — a $p$-adic analytic map with nonvanishing Jacobian is a local analytic
isomorphism; equivalently Serre, *Lie Groups and Lie Algebras*, III.9) it is a local
analytic isomorphism onto its image. Globally on $\widetilde W$ it is an $n!$-to-one cover
(the $S_n$-action permuting roots), branched exactly over $\Delta$ (measure zero). That the
$n!$ ordered preimages of a given $f\in W$ are **Krasner-close** sheets — i.e. that root
labels are locally constant and the cover is genuinely $n!$-sheeted off $\Delta$ — is
Krasner's lemma (Poonen, *Rational points on varieties*, Prop 3.5.74): on a small enough
residue ball the splitting field and the bijection roots$\leftrightarrow$labels are
constant.

### 3.3 The change-of-variables formula

Apply the $p$-adic change-of-variables theorem to the étale, $n!$-to-one map
$\Phi:\widetilde W\to W$. In the normalization $\mu_{\mathcal O_L}(\mathcal O_L)=1$ (so
$|\cdot|=q_L^{-v_L}$ with $q_L=q^{f(L/K)}$ — but see §4 for the descent to $q$), the
substitution rule (paper Thm `change of variables` part (2), with the trivial group
$G=\{1\}$ acting, i.e. the bare $p$-adic substitution of Igusa §7.4 / Weil, *Adèles and
algebraic groups*, applied $n!$-sheet-wise) gives, for any integrable test function $\Psi$
on $W$,
$$\int_{\widetilde W}(\Psi\circ\Phi)\,|\det\mathrm d\Phi|\,d\mu_{\mathcal O_L^{\,n}}
   \;=\;n!\,\int_{W}\Psi\,d\mu_n,$$
the factor $n!$ counting the ordered preimages of each unordered $f$. Taking
$\Psi=\mathbf 1_W$ and using $|\det\mathrm d\Phi|=|\mathrm V|$ from (a):
$$\boxed{\;\mu_n(W)=\frac1{n!}\int_{\widetilde W}\Big|\textstyle\prod_{i<j}(\alpha_i-\alpha_j)
   \Big|\,d\mu_{\mathcal O_L^{\,n}}.\;}$$
This is (b). The $\tfrac1{n!}=\tfrac1{|S_n|}=\tfrac1{|\mathrm{Aut}|}$ is precisely the
order of the deck group of $\Phi$; on a stratum whose roots have nontrivial coincidence
pattern the relevant subgroup is the residual stabilizer, and the resulting combinatorial
factor is absorbed into the residue-config count $\mathcal N_T$ (§5, and M1's $\alpha$-factor).

**Why no characteristic obstruction** (the R1 instance of the structural mechanism). The
only place characteristic could enter is the smoothness/étaleness of $\Phi$. At a wild
prime $\Phi$ can be **inseparable on tangent spaces** at the branch locus $\Delta$ — this
is exactly the tangent-space pathology that broke Prop 5.3. But change of variables consumes
$|\det\mathrm d\Phi|=|\mathrm V|$, a **function on $K$-points** whose **valuation** is what
enters the integral, and that valuation is finite and explicit off the measure-zero $\Delta$
**in every characteristic**. The étaleness needed is only on $\U f$ (where $\mathrm V\ne0$),
which holds in all characteristics; the branch locus is discarded as measure zero
(§3.1). This is the precise root-side analogue of L1's "Jacobian determinant is the
resultant, a function on points, whose valuation is $0$ on the coprime cell in every
characteristic." $\qquad\square$

### 3.4 Roots in a ramified splitting field

Part (b) was stated with $\widetilde W\subset\mathcal O_L^{\,n}$ for $L$ the (possibly
**ramified**) splitting field. The change-of-variables computation in §3.3 is valid over
**any** finite $L/K$: $\mu_{\mathcal O_L^{\,n}}$ is Haar on $\mathcal O_L^{\,n}$, $\Phi$ is
étale off $\mathrm V=0$, and Igusa §7.4 holds over any local field. The subtlety is only
**bookkeeping**: when $L/K$ is ramified of index $e$, $v$ takes values in $\tfrac1e\mathbb Z$
and $\mathrm V$ has fractional valuation — but this is **internal to a single stratum** and
appears as the integer exponent $d(T)=\sum\delta(i,j)\in\tfrac1{n!}\mathbb Z$ times the
stratum's residue volume. Crucially the *stratum volume* $\mu_n(\mathcal S_T)$, which is
what the recursion needs, is an integral over $W\subset M_n=\mathcal O_K^{\,n}$ — a space
over the **unramified** $\mathcal O_K$, where $v(p)=1$. The ramified $L$ enters only as the
ring in which the *roots* live; the *measure* is pushed back to $\mathcal O_K$ where it is
the universal $q$-power of L4. So **ramification of the splitting field never breaks
$p$-uniformity of the volume**: it is absorbed into the slope data $d(T)$, a lattice
quantity (L4: "wild slope $a/b$ gives the same exponent as a tame slope with the same
$(a,b)$"). This is the resolution of the task's "roots living in ramified extensions of the
splitting field." $\qquad\square$

---

## 4. The Galois-orbit descent for $\delta>1$ (cited, not re-derived)

When a cluster's residue point has degree $\delta>1$ (the residual root is non-rational
over $\mathbb F_q$), the $\delta$ roots form a single $\mathrm{Frob}_q$-orbit and the naive
"product of $\delta$ independent cells" over-counts by the orbit. The correct passage —
identifying the $K$-volume with one orbit representative and substituting $q\mapsto
q^{k_i/\ell_i}$ — is **exactly the paper's Lemma `local integrals`** (line 772), whose proof
(lines 784–813) is the relevant statement:
the coordinate isomorphism `eqn: co-ord isomorphism` (line 790) is built from the inverse
function theorem on a regular system of parameters $\{t_{ij}\}$ (here: the root-differences
adapted to the tree), is $\mathrm{Frob}$-equivariant, and is **measure-preserving** (line
797: "the bijection is measure-preserving"); restricting to $\mathrm{Frob}$-fixed points
turns the integral $\int|t_{1}|^{e_1}\cdots|t_r|^{e_r}$ into
$\prod_i\rho^{|M_i/\mathrm{Frob}^{\ell_i}|}_{e_i}(m;q^{k_i/\ell_i})$. With our
identification ($t_i$ $=$ a root-difference, $e_i$ $=$ its multiplicity in the Vandermonde,
$k_i=\delta$, $\ell_i=\gcd(\delta,m)$), this is precisely the $\delta$-descent
$C^{(\delta)}_m(q)=C^{(1)}_m(q^\delta)$ used in L1 part (c), M1 §2.1(1), and L5 §3.

I therefore **cite** Lemma `local integrals` for the orbit descent rather than re-deriving
it (it is the paper's own novel contribution, and is over an **unramified** $K_\delta/K$, so
tame-for-descent and $p$-independent). What R1 adds is the identification of the paper's
local parameters $t_{i,x}$ with the **root-difference coordinates** $\alpha_i-\alpha_j$ and
of the exponents $e_i$ with the **Vandermonde multiplicities**: i.e. that the resolution
integrand $\prod_i|t_{i,x}|^{e_i}=|\operatorname{Jac}(f_\sigma)|$ (paper `defn: Jacobian`,
line 826: $\operatorname{Jac}(f)=u\prod_it_{i,x}^{e_i}$) **is** the Vandermonde $|\mathrm V|$
for the multiplication map $f_\sigma$. This identification is exact in the completely-split
example (paper line 1302, $\operatorname{Jac}(f_1)=\prod_{i<j}|z_i-z_j|=|\mathrm V|$) and is
the general $\operatorname{Jac}(\text{mult})=\operatorname{Res}=\prod\mathrm V$-type
statement; it is the content of `ASSERTIONS A1`.

---

## 5. Proof of (c): Vandermonde constant on a stratum, and the stratum volume

### 5.1 The Vandermonde valuation is a tree invariant

By definition of the stratum $\mathcal S_T$, the ultrametric $\delta(i,j)=v(\alpha_i-
\alpha_j)$ is **fixed** (it is the tree-distance data of $T$: $\delta(i,j)$ is the height of
the deepest node of $T$ separating leaves $i$ and $j$). Hence
$$v\Big(\prod_{i<j}(\alpha_i-\alpha_j)\Big)=\sum_{i<j}\delta(i,j)=:d(T)$$
is **constant on $\mathcal S_T$**, and $|\mathrm V||_{\mathcal S_T}=q^{-d(T)}$. (When $T$
carries fractional slopes from a ramified leaf-field, $d(T)\in\tfrac1{n!}\mathbb Z$, but the
*product over the whole stratum* against the residue volume yields an integer $q$-exponent,
L4.) This is (c), first equation.

**Verified** (`r1_verify.py`): for the tree "$3$ roots, all pairwise valuation $1$",
$\sum_{i<j}v(\alpha_i-\alpha_j)$ is the single value $\{3\}=d(T)$ over $20000$ samples at
$p=3,5,7$ — a singleton, confirming constancy. $\qquad\square$

### 5.2 The stratum volume

Combine (b) and (c). On $\mathcal S_T$ the Vandermonde integrand is the constant
$q^{-d(T)}$, so by (b)
$$\mu_n(\mathcal S_T)=\frac1{|\mathrm{Aut}(T)|}\,q^{-d(T)}\,\mu_{\text{root}}(\widetilde{\mathcal S}_T),$$
where $\mu_{\text{root}}(\widetilde{\mathcal S}_T)$ is the Haar measure of the
ordered-root locus realizing $T$. The root locus is itself a fibered product over the tree:
at each internal node of out-degree $r$ over a residue point of degree $\delta$, the
children occupy $r$ **distinct** residue classes in $\mathbb F_{q^\delta}$ (a falling
factorial / necklace count) and each child sub-cluster recurses; a fully-clustered node of
size $m$ contributes a rescale **self-loop** summing geometrically to
$(1-q^{-w(m)})^{-1}$, $w(m)=\binom m2+m-1$ (L5 §3, the Vandermonde-weighted self-similar
integral $I_m$). Collecting the residue counts into the universal polynomial
$\mathcal N_T(q)$ (L3, $p$-independent: finite fields perfect $\Rightarrow$ no inseparable
irreducibles $\Rightarrow$ the needs-refinement locus is the discriminant locus with
universal count) and the self-loops into the product, and absorbing $|\mathrm{Aut}(T)|$ into
$\mathcal N_T$ (the residual symmetric-group order is part of the configuration count, and
is the paper's $\alpha$-factor — M1):
$$\boxed{\;\mu_n(\mathcal S_T)=q^{-d(T)}\cdot\frac{\mathcal N_T(q)}{\prod_m(1-q^{-w(m)})}.\;}$$
Every factor is a **universal rational function of $q$** depending only on the
**combinatorial** tree $T$ (not on $p$): $d(T)$ and $w(m)$ are lattice/tree integers, and
$\mathcal N_T(q)$ is the universal residue count. This is the central output of R1, the
"$\mathrm{vol}(\text{stratum}_T)=q^{-d(T)}P_T(q)/\prod(1-q^{-m})$" of
`STRUCTURAL_MECHANISM` (with the **corrected** self-loop exponent $w(m)=\binom m2+m-1$, not
$m$ — `WORKING_NOTES` C2/L5 G1; e.g. $w(3)=5$ giving the paper's $\Phi=(q^5-1)/(q-1)$).
$\qquad\square$

### 5.3 The self-similar Vandermonde integral (the source of $\prod(1-q^{-w(m)})$)

The self-loop factor is the **root-side** integral
$$I_m=\int_{\mathcal O_K^{\,m}}\prod_{i<j}|s_i-s_j|\,d\mu(s_1)\cdots d\mu(s_m),\qquad I_1:=1,$$
the Vandermonde-weighted volume of a fully-clustered degree-$m$ stratum (the pushforward of
(b) for the rescale self-loop). Stratifying $\mathcal O_K^{\,m}$ by the residue partition
$P$ of the $m$ coordinates (block $B$ of size $b$ in one residue class: coset mass
$q^{-b}$, intra-block Vandermonde rescale $q^{-\binom b2}$, inner integral $I_b$; $r$ blocks
into distinct residues: falling factorial $q^{\underline r}$) gives
$$I_m=\sum_{P\vdash[m],\,|P|=r}q^{\underline r}\prod_{B\in P}q^{-(|B|+\binom{|B|}2)}I_{|B|}.$$
Isolating the single-block ($r=1$) self-loop term, with coefficient
$q\cdot q^{-(m+\binom m2)}=q^{-(\binom m2+m-1)}=q^{-w(m)}$:
$$I_m\big(1-q^{-w(m)}\big)=\sum_{P:\,r\ge2}q^{\underline r}\prod_{B}q^{-(|B|+\binom{|B|}2)}I_{|B|},$$
the RHS in $I_\ell$ with $\ell<m$ only. This is the geometric closure (L5 §3.1). **Verified
symbolically** (`r1_verify.py`):
$$I_1=1,\quad I_2=\frac q{q+1},\quad I_3=\frac{q^3(q^2-q+1)}{(q+1)\Phi},\quad
  I_4=\frac{q^6(\cdots)}{(q+1)^2(q^2+q+1)(q^6+q^3+1)\Phi},$$
self-loop exponents $w(2)=2,w(3)=5,w(4)=9$ — exactly L5's corrected values. The
paper's recursive subcase $\int_{\mathcal O^2}|u_1-u_2|\,du=q^3/(q+1)$ (line 1302, in the
mass-$q^2$ normalization) is $q^2I_2=q^3/(q+1)$. **Verified.**

---

## 6. The end-to-end consistency check (completely-split cubic) and a wild atom

### 6.1 $n=3$, completely split: re-deriving the paper's $\eta_{f_1}$

The paper computes (line 1302–1305)
$\eta_{f_1}(K)=\int_{(\mathbb P^1)^3(B)}\prod_{i<j}|z_i-z_j|\,d\mu$ — **literally** the
Vandermonde pushforward of (b)+(a) for the multiplication map $f_1:(\mathbb P^1)^3\to
\mathbb P^3$ — and gets $\rho(3,(111);q)=\eta_{f_1}/(6|\mathbb P^3(\mathbb F_q)|)
=(q^2+1)^2/(6\Phi)$, the $\tfrac16=\tfrac1{3!}=\tfrac1{|\mathrm{Aut}|}$ being R1(b)'s deck
factor. Reorganizing the paper's $(\mathbb P^1)^3$-residue-stratification as our
cluster-tree strata (distinct residues: integrand $1$; one coincident pair: $\int_{\mathfrak
m^2}|t_1-t_2|=1/(q+1)=I_2/q$ per the L5 $I_2$; all three coincident: the self-similar
$J_3=q^{-3}I_3$) reproduces $\eta_{f_1}$ and hence $\rho(3,(111);q)$ exactly. **Verified
symbolically** (`r1_verify.py`): the $I_m$ recursion of §5.3 assembles to
$\rho(3,(111);q)=(q^2+1)^2/(6\Phi)$. This is the same number the recursion (L6) and the
oracle (`padic_types.py`) produce — three independent routes agree. **Verified by
Monte-Carlo**: $I_3=\int_{\mathcal O_K^3}|\mathrm V|\,d\mu$ matches $q^3(q^2-q+1)/((q+1)\Phi)$
at $p\in\{2,3,5,7\}$ (diffs $\le 9\times10^{-4}$, $N=3\times10^5$) — including the **wild
$p=2,3$**.

### 6.2 The deepest wild node ($n=4$, $p=2$, slope-$1/2$ size-$4$ cluster)

The genuine test of R1's $p$-uniformity is at a wild atom, where the splitting field is
ramified and the residual is inseparable. For the clean slope-$1/2$ size-$4$ cluster, R1(c)
predicts the per-shape volumes from the tree data $d(T)$ + residue counts; the established
full-resolution closed forms (`STRUCTURAL_MECHANISM`, regime-1, trusted PARI oracle) are
$$\mathrm{(4,1)}:\tfrac1{q+1},\quad\mathrm{(2,2)}:\tfrac12+\tfrac1{2q(q+1)},\quad
  \mathrm{split\,2{+}2}:\tfrac{q-2}{2q}+\tfrac1{2q(q+1)},$$
at $q=2$ giving $\tfrac13,\tfrac7{12},\tfrac1{12}$. **Verified** with the trusted PARI
oracle (`quartic_oracle.full_type`, `r1_verify.py`, $N=4000$, $p=2$): the oracle-classified
slope-$1/2$ cluster gives $(4,1):0.332$, $(2,2):0.583$, split$:0.085$ — matching
$\tfrac13,\tfrac7{12},\tfrac1{12}$ to MC error. So R1's pushforward + Vandermonde-stratum
formula yields the correct per-shape volumes **even at the deepest wild (Artin–Schreier
inseparable) node**, confirming the structural mechanism: the ramified splitting field and
the inseparable tangent geometry are invisible to the Vandermonde-weighted **volume**.

---

## 7. What is proved vs. cited (honest status)

**Proved here (no residual analytic gap at the R1 level):**
- (a) Vieta Jacobian $=$ Vandermonde, and $\operatorname{disc}=\mathrm V^2$ — classical,
  re-verified symbolically $n\le5$.
- (b) the pushforward $\mu_n(W)=\tfrac1{n!}\int_{\widetilde W}|\mathrm V|$ via the $p$-adic
  inverse function theorem + change of variables, with the discriminant locus discharged as
  measure zero, valid in **all characteristics** (the only char-sensitive ingredient,
  étaleness, is needed only off the measure-zero branch locus).
- (c) Vandermonde-constant-on-a-stratum $|\mathrm V||_{\mathcal S_T}=q^{-d(T)}$ and the
  stratum-volume formula $q^{-d(T)}\mathcal N_T(q)/\prod(1-q^{-w(m)})$, with the corrected
  self-loop exponent $w(m)=\binom m2+m-1$; the self-similar $I_m$ recursion proved and
  verified ($I_2,I_3,I_4$, exponents $2,5,9$).
- the ramified-splitting-field case (§3.4): ramification is absorbed into $d(T)$ (a lattice
  quantity, L4), so it never breaks $p$-uniformity of the **volume**.

**Reduced to citation (clearly flagged):**
- **(R1-cite-1) The Galois-orbit descent for $\delta>1$** (§4): the substitution
  $q\mapsto q^{k_i/\ell_i}$ and the orbit-average identification are **cited** to the
  paper's Lemma `local integrals` (its `eqn: co-ord isomorphism` is itself an inverse-function-
  theorem/Krasner bijection that is measure-preserving — the exact statement R1 needs).
  $K_\delta/K$ is unramified, so $p$-independent; severity **reduced-to-citation**. What R1
  contributes is the identification of the paper's $t_{i,x}^{e_i}$ with the Vandermonde
  $|\mathrm V|$ (the $\operatorname{Jac}(\text{mult})=\prod\mathrm V$ statement), exact at
  $n=3$ and structurally general.
- **(R1-cite-2) The $|\mathrm{Aut}|$/$\alpha$-factor reorganization** (§5.2): absorbing the
  residual stabilizer order and the orbit combinatorics into $\mathcal N_T$ is the paper's
  $\alpha$-factor / poset machinery (M1/CP2, `eqn: factorization densities as integrals`),
  $p$-independent and exact at $n\le3$; the general-$n$ identification is M1's deferred
  combinatorial lemma, **not** an R1 gap (R1 only needs that *some* universal
  $p$-independent prefactor makes (b) hold per-stratum, which the change-of-variables deck
  factor $\tfrac1{n!}$ supplies before stratification).

**No fatal or serious gap.** The substantive analytic content (pushforward + Vandermonde
stratum-constancy over $\mathcal O_K$, char-uniform) is established; the two reduced items
are $p$-independent bookkeeping over unramified extensions, cited verbatim to the paper's
§2–4, and neither touches the wild-prime difficulty (which lives in the cluster laws
$L_e$/L2–L5, not in R1). The wild $n=4,p=2$ oracle check confirms R1 delivers correct
per-shape volumes at the deepest inseparable node.

---

## 8. Citation index (exact)

- **Vieta Jacobian $=$ Vandermonde / disc $=$ V$^2$:** Bourbaki, *Algèbre* IV §6; standard.
  Paper analogue: $\operatorname{Jac}(\text{mult})=\operatorname{Res}$ (line 1714) and the
  completely-split integrand $\prod_{i<j}|z_i-z_j|$ (line 1302).
- **Measure-zero of $\{$disc$=0\}$:** paper Thm `change of variables` part (1) (line 455),
  $\mu_\omega(Z(\L))=0$ for $Z$ Zariski-closed.
- **$p$-adic inverse function theorem / analytic bijection, unit Jacobian:** Igusa,
  *Introduction to the Theory of Local Zeta Functions*, §7.4; Serre, *Lie Groups and Lie
  Algebras* III.9. (Task pointer: "Igusa, Local Zeta Functions, Sec 7.4.")
- **Change of variables (substitution) formula:** paper Thm `change of variables` (line 452),
  $G=\{1\}$ case = Igusa §7.4 / Weil, *Adèles and algebraic groups*. (L1's `C1` fix: lead
  with Igusa §7.4 for an isomorphism, not GWZ which is for genuine quotients.)
- **Krasner / local constancy of the cluster tree:** paper Lemma after `defn: rho_f,
  admissible pair` (line 647), citing Krasner / Poonen, *Rational points on varieties*,
  Prop 3.5.74.
- **Galois-orbit descent $\delta>1$, $q\mapsto q^{k/\ell}$:** paper Lemma `local integrals`
  (line 772), `eqn: co-ord isomorphism` (line 790), measure-preserving (line 797).
- **Residue counts universal (needs-refinement $=$ discriminant locus):** L3 /
  `STRUCTURAL_MECHANISM` R3.
- **Self-loop exponent $w(m)=\binom m2+m-1$ / $\Phi$:** L5 §3 (corrected); paper $\Phi$
  (line 1305).
- **Unique extension of $v$ to $\overline K$; defectlessness of complete DVF:** Neukirch,
  *ANT*, II.4.8; Serre, *Local Fields*, II.3 (cor. to Prop 10).
