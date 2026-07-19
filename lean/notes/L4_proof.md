# L4 — Newton-polygon cell volume is a characteristic-independent $q$-power

**Status:** proved, with all numeric checks passing (exact enumeration + MC).
**Date:** 2026-06-14. Author: L4 worker.

Throughout, $K/\mathbb Q_p$ is finite **unramified** with residue field $\mathbb F_q$
($q=p^k$), ring of integers $O=O_K$, uniformizer $p$, and normalized valuation
$v$ with $v(p)=1$, $v(O^\times)=0$. Haar measure $\mu$ on $O$ is normalized by
$\mu(O)=1$; equivalently $\mu(\{x: v(x)\ge m\}) = \mu(p^m O)=q^{-m}$ for $m\ge 0$.
For a finite unramified extension $K_\delta/K$ of degree $\delta$ (residue field
$\mathbb F_{q^\delta}$, same uniformizer $p$, $v(p)=1$) the same statements hold with
$q$ replaced by $q^\delta$.

We write $M_e(O_{K_\delta})=\{g(x)=x^e+c_{e-1}x^{e-1}+\dots+c_0 : c_i\in O_{K_\delta}\}
\cong O_{K_\delta}^e$ with the product Haar measure of total mass $1$ (so $\mu(M_e)=1$).
We set $c_e:=1$ (fixed, not integrated).

---

## 0. The single building block: valuation-box measures

These two facts are the *only* analytic input; both depend on $q$ alone (the residue
field size), never on $p$, $k$, or the slope arithmetic.

**Lemma 0 (box and shell measures).** For $c$ Haar-distributed on $O_{K_\delta}$ and any
integer $m\ge 0$,
$$
\mu(\{v(c)\ge m\}) = (q^\delta)^{-m},
\qquad
\mu(\{v(c)= m\}) = \bigl(1-(q^\delta)^{-1}\bigr)\,(q^\delta)^{-m}.
$$

*Proof.* $\{v(c)\ge m\}=p^mO_{K_\delta}$ is a coset-union of $[\,O_{K_\delta}:p^mO_{K_\delta}\,]^{-1}$
of the total; since $O_{K_\delta}/p^mO_{K_\delta}$ has $(q^\delta)^m$ elements (residue field
$\mathbb F_{q^\delta}$ and $v(p)=1$, so $p^m$ generates a subgroup of index $(q^\delta)^m$),
its measure is $(q^\delta)^{-m}$. Then $\{v(c)=m\}=p^mO_{K_\delta}\setminus p^{m+1}O_{K_\delta}$
has measure $(q^\delta)^{-m}-(q^\delta)^{-(m+1)}=(1-(q^\delta)^{-1})(q^\delta)^{-m}$. $\square$

**The crucial $p$-independence.** The number $(q^\delta)^m=[\,O_{K_\delta}:p^mO_{K_\delta}\,]$
uses only that $K_\delta/K$ is unramified ($v(p)=1$, so the $\mathfrak m$-adic filtration steps
by one residue field at a time). It is a function of $q^\delta$ alone. *No splitting field,
no separability, no tangent-space data enters.* This is the volume-side incarnation of the
structural mechanism (STRUCTURAL_MECHANISM.md, building block 1): valuation conditions are
visible only through $q$.

(Verified numerically: over the unramified degree-$2$ ring with residue field $\mathbb F_4$,
the single-coordinate measures are exactly $1-1/q,\ (1-1/q)q^{-1},\ q^{-1},\ q^{-2}$ for
$q=4$ — i.e. functions of $q$, not of $p,k$ separately. See `l4_q4.py`.)

---

## 1. Newton polygon and the cell

For $g=x^e+\sum_{i<e}c_ix^i\in M_e(O_{K_\delta})$ with $c_e=1$, plot the points
$$
T(g)=\{(i,\,v(c_i)) : 0\le i\le e,\ c_i\ne 0\}\subset \mathbb R^2 ,
$$
where $(e,0)$ is always present ($c_e=1$). The **Newton polygon** $NP(g)$ is the lower
convex hull of $T(g)$ on $[0,e]$ (we use the "valuation of roots = slope magnitude"
convention: a segment from $(i,v_i)$ to $(j,v_j)$, $i<j$, has slope $(v_i-v_j)/(j-i)\ge0$
equal to the common valuation of the $j-i$ roots it accounts for; this is the standard
Newton polygon of $g$, e.g. Neukirch, *ANT*, II.6.3).

Fix a target lattice polygon $P$: a piecewise-linear convex graph on $[0,e]$ with vertices
$(i_0=0,\,h_{i_0}),(i_1,h_{i_1}),\dots,(i_s=e,\,0)$, each $h_{i_t}\in\mathbb Z_{\ge0}$, integer
abscissae $0=i_0<i_1<\dots<i_s=e$, and $h_e=0$. Let $h_i:=$ the height of $P$ above abscissa
$i$ ($0\le i\le e$); $h_i\in\mathbb Q_{\ge0}$, integral exactly at the vertices. (The vertex
slopes are strictly increasing — convexity.) Write
$$
\mathrm{Vert}(P)=\{i_0,\dots,i_s\}\subseteq\{0,1,\dots,e\}.
$$
Define the **cell**
$$
\mathcal C(P)\ :=\ \{\,g\in M_e(O_{K_\delta}) : NP(g)=P\,\}.
$$

---

## 2. Exact description of the cell as a product of valuation conditions

**Lemma 1 (cell = box).** $NP(g)=P$ if and only if
$$
\begin{cases}
v(c_i)=h_i &\text{for every vertex } i\in\mathrm{Vert}(P),\ i<e,\\[2pt]
v(c_i)\ge h_i &\text{for every non-vertex } i\in\{0,\dots,e-1\}\setminus\mathrm{Vert}(P).
\end{cases}
\tag{$\ast$}
$$
(The abscissa $i=e$ carries the fixed datum $c_e=1$, $v(c_e)=0=h_e$, which is a vertex and
is automatically satisfied; it is not integrated.)

*Proof.* The Newton polygon $NP(g)$ is by definition the lower convex hull of $T(g)$, hence
$NP(g)=P$ iff (a) every plotted point lies **on or above** $P$, i.e. $v(c_i)\ge h_i$ for all
$i$ with $c_i\ne0$ (and vacuously when $c_i=0$, i.e. $v=+\infty\ge h_i$); **and** (b) every
**vertex** of $P$ is **attained** by a plotted point, i.e. $v(c_{i_t})=h_{i_t}$ at each vertex
$i_t$.

For (b): if at some vertex $i_t<e$ we had $v(c_{i_t})>h_{i_t}$ (including $c_{i_t}=0$), the
point $(i_t,h_{i_t})$ would not be in $T(g)$ and, $i_t$ being a strict vertex (a corner where
the slope strictly increases), the lower hull of the remaining points would either bridge over
$(i_t,h_{i_t})$ with a single segment of intermediate slope or rise above it — in both cases
the hull would differ from $P$. Conversely $v(c_{i_t})<h_{i_t}$ is excluded by (a). The vertex
$i_s=e$ is fixed ($c_e=1$, $v=0=h_e$), automatically attained.

For the non-vertices: convexity of $P$ means a non-vertex $i$ lies in the relative interior of
an edge or strictly inside; (a) requires only $(i,v(c_i))$ to lie on or above $P$, i.e.
$v(c_i)\ge h_i$, and **no** equality is forced (a value $v(c_i)>h_i$, including $c_i=0$, keeps
the same hull $P$ as long as the vertices are attained). This is exactly ($\ast$). The
equivalence (a)$\wedge$(b) $\Leftrightarrow$ $NP(g)=P$ is the defining property of the lower
convex hull. $\square$

**Remark (integrality at non-vertices).** Since $v(c_i)\in\mathbb Z_{\ge0}$ while $h_i$ may be
fractional, the condition $v(c_i)\ge h_i$ at a non-vertex is *equivalent* to
$v(c_i)\ge \lceil h_i\rceil$. At a vertex $h_i\in\mathbb Z$ so $\lceil h_i\rceil=h_i$. This is
the only place where the *rounding* of fractional (possibly wild) slopes enters — and it is
purely combinatorial.

---

## 3. The cell volume

Conditions ($\ast$) are **independent across the coordinates** $c_0,\dots,c_{e-1}$ (a product
condition on $O_{K_\delta}^e$), so by Lemma 0 the volume factorizes.

**Theorem L4 (cell volume).** With $Q:=q^\delta$,
$$
\boxed{\;\mu\bigl(\mathcal C(P)\bigr)
= \Bigl(1-Q^{-1}\Bigr)^{\,V(P)}\; Q^{-N(P)}\;}
$$
where
$$
V(P)=\#\bigl(\mathrm{Vert}(P)\cap\{0,1,\dots,e-1\}\bigr),
\qquad
N(P)=\sum_{i=0}^{e-1}\bigl\lceil h_i\bigr\rceil .
$$
Equivalently $\mu(\mathcal C(P))=Q^{-\delta'\!\cdot}\dots$; writing it as a single power we set
$$
A(P)\ :=\ N(P)\ \in\ \mathbb Z_{\ge0},
\qquad
\mu(\mathcal C(P)) = (1-Q^{-1})^{V(P)}\,Q^{-A(P)} .
$$
Both $V(P)$ and $A(P)=N(P)$ are determined by the **lattice geometry of $P$ alone**: $V(P)$
counts vertices in columns $0..e-1$, and $N(P)$ sums the **ceilings of the polygon heights**
over those columns. **Neither depends on $p$, on $k$, or on the slope denominators.**

*Proof.* By Lemma 1, $\mathcal C(P)=\prod_{i=0}^{e-1}E_i$ where
$E_i=\{v(c_i)=h_i\}$ for $i\in\mathrm{Vert}(P)$, $i<e$, and $E_i=\{v(c_i)\ge\lceil h_i\rceil\}$
otherwise. The product Haar measure factorizes, and Lemma 0 gives
$\mu(E_i)=(1-Q^{-1})Q^{-h_i}$ at a vertex and $\mu(E_i)=Q^{-\lceil h_i\rceil}$ at a
non-vertex. Multiplying:
$$
\mu(\mathcal C(P))
= \prod_{\substack{i\in\mathrm{Vert}(P)\\ i<e}}(1-Q^{-1})Q^{-h_i}
\ \prod_{\substack{i\notin\mathrm{Vert}(P)\\ i<e}}Q^{-\lceil h_i\rceil}
= (1-Q^{-1})^{V(P)}\,Q^{-\sum_{i<e}\lceil h_i\rceil},
$$
using $\lceil h_i\rceil = h_i$ at vertices. $\square$

**Corollary (characteristic-independence / wild = tame).** Fix the combinatorial polygon $P$.
For *every* prime $p$ and *every* unramified $K_\delta$ with residue size $Q$, the cell volume
is the same rational function $(1-Q^{-1})^{V(P)}Q^{-A(P)}$ of $Q$. In particular a **wild** slope
$a/b$ ($p\mid b$) contributes exactly the same $V,A$ as a **tame** slope with the same
reduced $(a,b)$: the slope enters $A(P)$ only through the heights $\lceil h_i\rceil$ along the
segment, which are integers read off the lattice line and are blind to $p\mid b$.

*Proof.* $V(P),A(P)$ are defined from the lattice graph $P$ with no reference to $p$. The only
prime-dependent fact one might fear — the index $[\,O_{K_\delta}:p^mO_{K_\delta}\,]$ — equals
$Q^m$ for all $p$ because $K_\delta/\mathbb Q_p$ is unramified ($v(p)=1$). $\square$

---

## 4. Explicit $A(P)$ from lattice geometry (Pick-type form)

It is useful to record $N(P)=\sum_{i=0}^{e-1}\lceil h_i\rceil$ in closed lattice form. Split a
single edge $\varepsilon$ of $P$ from vertex $(i,h_i)$ to vertex $(j,h_j)$ ($i<j$,
$h_i>h_j$, slope $s=(h_i-h_j)/(j-i)=a/b$ in lowest terms, $b\mid(j-i)$). Its columns
$i\le \ell<j$ contribute $\sum_{\ell=i}^{j-1}\lceil h_\ell\rceil$ with
$h_\ell = h_i - s(\ell-i)$. Writing $\ell-i=m$ ($0\le m<j-i$),
$$
A(\varepsilon) = \sum_{m=0}^{(j-i)-1}\Bigl\lceil h_i - \tfrac{a}{b}m\Bigr\rceil .
$$
Because $a/b$ is in lowest terms, as $m$ runs over a length-$b$ block the fractional parts
$\{am/b\}$ run over $\{0,1/b,\dots,(b-1)/b\}$ in some order, so each length-$b$ block of
columns contributes the same correction independent of $p$; summing over the
$(j-i)/b$ blocks gives a closed form. Concretely, using
$\lceil x\rceil = x + (\lceil x\rceil - x)$ and $\sum_{r=0}^{b-1}\lceil -ar/b\rceil
= -\tfrac{a(b-1)}{2}+\tfrac{b-1}{2}=\tfrac{(b-1)(1-a)}{2}$ (a Gauss-sum identity, $\gcd(a,b)=1$),
one gets a polynomial-in-the-edge-data expression for $A(\varepsilon)$. Then
$A(P)=\sum_{\text{edges }\varepsilon}A(\varepsilon)$, **manifestly $p$-independent**.

(The reader needs only the operational form $N(P)=\sum_{i<e}\lceil h_i\rceil$; the Pick-type
rewrite is a convenience and is not used downstream.)

---

## 5. Worked instances and numeric verification

All numbers below are produced by `/tmp/l4_*.py` (exact `sympy`/`Fraction` arithmetic for
closed forms; Monte-Carlo where noted). Exact enumeration over $O/p^kO$ matched the closed
form on **every** trusted polygon (heights $<k$) for $(e,p,k)\in\{(2,2,5),(2,3,4),(2,5,3),
(3,2,5),(3,3,4),(4,2,4)\}$ — see `l4_exact.py` (88 trusted polygons, 0 mismatches).

### 5.1 Eisenstein (single slope $1/e$, length $e$)
Polygon $P$: vertices $(0,1),(e,0)$, single slope $1/e$. Heights $h_i=1-i/e$, so
$\lceil h_0\rceil=1$ (vertex) and $\lceil h_i\rceil=1$ for $1\le i\le e-1$ (since
$0<1-i/e\le 1-1/e<1$ rounds up to $1$). Thus $V(P)=1$ (only the vertex $i=0$ lies in
$\{0,\dots,e-1\}$; the vertex $e$ is excluded), and $N(P)=\underbrace{1}_{i=0}+(e-1)\cdot 1=e$.
Therefore
$$
\mu(\mathcal C_{\mathrm{Eis}}) = (1-Q^{-1})\,Q^{-e}=\frac{Q-1}{Q^{\,e+1}} .
$$
This is exactly the paper's Eisenstein volume $(q-1)/q^{e+1}$ (with $Q=q$ when $\delta=1$),
**at every prime including $p\mid e$ (totally wild)**.

*Checks.* Closed form $=(q-1)/q^{e+1}$ exactly for $q\in\{2,3,5,7\}$, $e\in\{2,3,4,5\}$
(`l4_special.py`). MC (2,000,000 draws) for $p\in\{2,3,5\}$, $e\in\{2,3,4,5\}$ agrees to MC
noise (`l4_check.py`); e.g. $p=2,e=2$: $0.12498$ vs $0.125$; $p=3,e=3$: $0.02463$ vs
$0.024691$. (The $p=5,e=5$ MC ratio $0.94$ is pure sampling noise: predicted prob
$\approx2.6\times10^{-4}$, so $\approx520$ hits.)

### 5.2 The $n=4$ wild atom: single slope $1/2$, length $4$
Polygon $P$: vertices $(0,2),(4,0)$, slope $1/2$, all four roots at valuation $1/2$. Heights:
$h_0=2$ (vertex), $h_1=1.5$, $h_2=1$, $h_3=0.5$; ceilings $2,2,1,1$. **Note $i=2$ is a
non-vertex even though $h_2=1$ is an integer** — it lies in the relative interior of the single
edge, so we use $v(c_2)\ge1$ (not equality). $V(P)=1$ ($i=0$), $N(P)=2+2+1+1=6$, hence
$$
\mu(\mathcal C_{1/2,4}) = (1-Q^{-1})\,Q^{-6}=\frac{Q-1}{Q^{7}} .
$$
*Checks.* Closed form $=(q-1)/q^7$ exactly for $q\in\{2,3,5,7\}$ (`l4_special.py`); direct MC
(up to $4\times10^7$ draws): $p=2$ $0.0078410$ vs $0.0078125$; $p=7$ (high-N) $7.20\times10^{-6}$
vs $7.29\times10^{-6}$ (`l4_general.py`, `l4_q4.py`).

### 5.3 Consistency with ASSERTIONS A11 (the $1/q$ non-split measure)
A11 concerns a *conditional* measure **inside** the slope-$1/2$ length-$4$ stratum of §5.2.
Conditioned on a clean slope-$1/2$ cluster, the level-$1$ residual polynomial is
$R(y)=y^2+\bar b y+\bar a\in\mathbb F_q[y]$ with $\bar a=-(c_0/p^2)\bmod p\in\mathbb F_q^\times$,
$\bar b=-(c_2/p)\bmod p\in\mathbb F_q$; the cell structure ($v(c_0)=2$ with $c_0/p^2$ a unit,
$v(c_2)\ge1$) makes $\bar a$ **uniform on $\mathbb F_q^\times$** and $\bar b$ **uniform on
$\mathbb F_q$**, by Lemma 0 applied to the leading unit digits. The "non-split" (residual has a
repeated root) locus has conditional measure
$$
\text{odd } p:\ \{\bar b^2=4\bar a\}; \qquad p=2:\ \{\bar b=0\}.
$$
*Odd $p$:* $\Pr=\frac{1}{(q-1)q}\sum_{\bar a\in\mathbb F_q^\times}\#\{\bar b:\bar b^2=4\bar a\}
=\frac{1}{(q-1)q}\cdot(q-1)=\frac1q$ (as $4\bar a$ ranges over $\mathbb F_q^\times$, the pairs
$(\bar b,4\bar a)$ with $\bar b\ne0$, $4\bar a=\bar b^2$ number $q-1$).
*$p=2$:* $\Pr(\bar b=0)=1/q$ (uniform $\bar b$). **Same $1/q$ in both characteristics**, even
though the loci are geometrically different (punctured parabola vs. inseparable punctured line).
This is consistent with the volume-only mechanism: it is a *residue-configuration* count
(building block 2/3), and §5.2's cell volume is its ambient stratum. Verified exactly
(combinatorial count, all $q$) and by brute force over $\mathbb F_p$, $p\in\{3,5,7,11,13\}$
(`l4_special.py`): non-split fraction $=1/p$ exactly. (This $1/q$ is a *residue count*, not a
Newton-cell volume; it is recorded here only to confirm L4 is consistent with the A11 datum it
sits above. The A11 statement itself is the domain of L3, not L4.)

### 5.4 Wild $=$ tame across primes (direct illustration)
For the fixed polygon "slope $1/2$, length $2$" (Eisenstein degree $2$), the cell volume is
$(q-1)/q^3$ for $q\in\{2,3,5,7,9,11\}$ — identical formula whether the slope is **wild**
($q=2$, $p=2\mid2$) or **tame** ($q=3,5,\dots$). Likewise "slope $1/3$, length $3$" gives
$(q-1)/q^4$ at $q=2,3,5,7$, wild at $q=3$, tame elsewhere (`l4_wild.py`).

---

## 6. Statement actually proved, and its role

**L4 (as used by the skeleton).** Let $P$ be a fixed lattice Newton polygon on $[0,e]$. For
every prime $p$ and every finite unramified extension $K_\delta/\mathbb Q_p$ with residue size
$Q=q^\delta$, the Haar volume of the cell $\{g\in M_e(O_{K_\delta}):NP(g)=P\}$ is
$$
\mu(\mathcal C(P)) = (1-Q^{-1})^{V(P)}\,Q^{-A(P)},
\qquad A(P)=\sum_{i=0}^{e-1}\lceil h_i\rceil,\quad
V(P)=\#(\mathrm{Vert}(P)\cap\{0,\dots,e-1\}),
$$
a fixed element of $\mathbb Z[Q^{-1}]$ depending only on the lattice geometry of $P$ — in
particular independent of $p$, of the residue degree split $q=p^k$ (only $Q$ enters), and of
whether any slope is wild. This is **building block 1** of the structural mechanism, made
rigorous over an arbitrary unramified base.

In the cluster recursion (L2/L5) this is exactly the factor "explicit $q$-power $\times$
geometric-series denominators": a single cluster of size $e$ with prescribed Newton polygon
contributes $\mu(\mathcal C(P))$, and the $(1-Q^{-1})$ vertex factors are the finite analogues
of the $\prod_m(1-q^{-m})^{-1}$ that appear after summing the rescale self-loops (L5). L4 says
this factor is $q$-rational and $p$-uniform; the *which-polygons-occur* bookkeeping and the
residue-shape multiplicities are L2/L3, not L4.

---

## 7. Honest gaps / scope limits

1. **(minor, scope) Edge convention at the right endpoint.** The statement integrates only
   $c_0,\dots,c_{e-1}$ (monic, $c_e=1$). If one instead works with non-monic $g$ of degree
   $\le e$ inside $\mathbb P^e$ (the paper's projective normalization), the leading column is a
   genuine variable and $V,A$ shift by the obvious leading-coefficient factor. The cluster
   recursion uses the **monic** local model (a cluster is centred and rescaled to be monic), so
   the monic statement is the one needed; the projective bookkeeping is handled in L1/L6, not
   here. No mathematical gap, but the normalization must be quoted consistently downstream.

2. **(minor) "$NP(g)=P$" vs. "$g$ has factorization type $\dots$".** L4 computes the volume of
   the *Newton-polygon* cell only. Translating a polygon into a factorization type requires the
   residual polynomials at each slope (separable $\Rightarrow$ factors split off; inseparable
   $\Rightarrow$ refine), which is **precisely** where wildness lives and is the content of
   L2/L3 (residual-polynomial separability over the finite residue field). L4 deliberately stops
   at the polygon. The Corollary's "wild $=$ tame" is *only* about the cell volume, not about
   the downstream type — that is the correct division of labor (STRUCTURAL_MECHANISM.md §"why
   each ingredient is universal").

3. **(minor) Heights must be $\ge0$ / $g\in O[x]$.** We assumed $g\in M_e(O)$ (coefficients
   integral), so $h_i\ge0$ and the polygon lies in the first quadrant. This is the only regime
   the recursion feeds to L4 (a cluster's translated/rescaled coefficients are integral by L1/L5,
   A5). For $g$ with negative slopes (roots of negative valuation) one rescales first; not needed
   here.

4. **(not a gap, but flagged) The independence across coordinates** in Lemma 1 uses that
   ($\ast$) is a *product* of one-variable conditions. This is immediate because each condition
   constrains a single $c_i$; there is no joint constraint. (The cell is a product of annuli/balls,
   literally a "box".) Verified by the exact enumeration matching in §5 / `l4_exact.py`.

No fatal or serious gaps were found: the core statement is an elementary but rigorous Haar-measure
computation, and every closed form was cross-checked by exact enumeration over $O/p^kO$ and by
Monte Carlo.
