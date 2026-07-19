# L3 — Residue-field factorization-shape counts are universal polynomials in $Q$

**Status:** proved (parts (a) and (b)), with the L2-interface connection stated precisely and
its one genuine assumption flagged. All closed forms re-verified numerically and symbolically
(see "Numerical checks" at the end).

Throughout, $Q = q^{\delta}$ is a fixed prime power; $\mathbb{F}_Q$ is the finite field with $Q$
elements, of characteristic $p$ (so $Q = p^{f}$ for some $f \ge 1$). "Monic of degree $m$" always
means a monic polynomial in $\mathbb{F}_Q[y]$ of degree $m \ge 0$. We write $\mu$ for the number-
theoretic Möbius function. The phrase **universal polynomial in $Q$** means: a single element
$P(t) \in \mathbb{Q}[t]$ (independent of $p$, $f$, $Q$) such that the quantity in question equals
$P(Q)$ for **every** prime power $Q$.

---

## 0. Where L3 sits, and exactly what it must deliver

In the cluster/Newton-polygon recursion (L1–L2), each node of the cluster tree carries an
**OM/MacLane residual polynomial** $R \in \kappa[y]$, where $\kappa = \mathbb{F}_{q^{\delta}}$ is
the residue field at that node ($\delta$ the residue degree accumulated along the path to the
node; $\delta \le n$). Refining the node — deciding how the cluster splits at the next level —
is governed by the factorization of $R$ over $\kappa$:

* each **separable irreducible factor** of $R$ of degree $d$ lifts (Hensel/Krasner) to a
  sub-cluster with residue degree multiplied by $d$, with no further refinement needed at this
  level;
* each **repeated factor** of $R$ (equivalently, $R$ non-squarefree) forces descent to the next
  OM level (the "needs-refinement" / wild-sensitive locus).

L2 reduces a single cluster's Haar volume to a **finite sum over the factorization shapes of $R$
over $\kappa$**, weighted by (i) characteristic-independent $q$-power slope/cell volumes (L4) and
(ii) recursively, the volumes attached to the lifted sub-clusters. The **combinatorial weight**
that multiplies each shape is the **number of monic $R$ of that shape over $\kappa$**.

Hence L3 must prove exactly:

> **(b)** For every factorization shape $\lambda$ (a finite multiset of pairs (degree, multiplicity)
> of irreducible factors with total degree $m$), the count
> $$ S_\lambda(Q) := \#\{\, R \in \mathbb{F}_Q[y]\ \text{monic},\ \deg R = m,\ R\ \text{has shape}\ \lambda \,\} $$
> is a universal polynomial in $Q$, with rational coefficients, **independent of the
> characteristic $p$**.

and the special case that controls the wild/refinement locus:

> **(a)** Every irreducible polynomial over $\mathbb{F}_Q$ is separable; consequently
> "non-separable $=$ non-squarefree", and the number of **non-squarefree** (= needs-refinement)
> monic polynomials of degree $m$ is the universal $Q^{m-1}$ for all $m \ge 1$ and all $Q$ — i.e.
> $\#\{\text{squarefree monic deg } m\} = Q^m - Q^{m-1}$ for $m \ge 2$ (and $=Q$ for $m=1$).

Because $\kappa = \mathbb{F}_{q^{\delta}}$ is itself a finite field with $q^{\delta}$ elements,
applying (a),(b) with $Q = q^{\delta}$ shows every residual-polynomial count appearing in L2 is a
universal polynomial in $q^{\delta}$, hence (composing $t \mapsto t^{\delta}$) a universal Laurent-
free polynomial in $q$ with $\mathbb{Q}$-coefficients independent of $p$. This is the connection
asserted in §3 below.

---

## 1. Part (a): perfectness, separability, and the universal non-squarefree count

### 1.1 Finite fields are perfect; every irreducible is separable

**Lemma 1 (perfectness).** $\mathbb{F}_Q$ is a perfect field: the Frobenius endomorphism
$\Phi: x \mapsto x^{p}$ is surjective (indeed bijective) on $\mathbb{F}_Q$.

*Proof.* $\Phi$ is a ring homomorphism (the "freshman's dream": $(x+y)^p = x^p + y^p$ in
characteristic $p$, since $\binom{p}{i} \equiv 0 \pmod p$ for $0 < i < p$; and $(xy)^p = x^p y^p$).
Its kernel is $\{x : x^p = 0\} = \{0\}$ since $\mathbb{F}_Q$ is a domain, so $\Phi$ is injective.
An injective self-map of a **finite** set is bijective. ∎

(Equivalently: $\Phi$ generates $\mathrm{Gal}(\mathbb{F}_Q/\mathbb{F}_p)$, a finite cyclic group,
so $\Phi$ is invertible.)

**Lemma 2 (every irreducible is separable).** If $g \in \mathbb{F}_Q[y]$ is irreducible, then $g$
is separable, i.e. $g$ has no repeated root in any extension; equivalently $\gcd(g, g') = 1$ and
$g' \ne 0$.

*Proof.* Standard (Lang, *Algebra*, Ch. V, or any text): a perfect field has no inseparable
irreducible polynomials. We give the argument. Suppose $g$ is irreducible but inseparable. An
irreducible polynomial is inseparable iff $g' = 0$ (if $g' \ne 0$, then $\deg g' < \deg g$ and
$\gcd(g,g')$ is a proper factor of the irreducible $g$, hence a unit, so $g$ is separable). Now
$g' = 0$ in characteristic $p$ forces every exponent appearing in $g$ to be divisible by $p$, so
$g(y) = h(y^{p})$ for some $h \in \mathbb{F}_Q[y]$, say $h(y) = \sum_i a_i y^{i}$. By Lemma 1 each
$a_i$ has a $p$-th root $b_i = a_i^{1/p} \in \mathbb{F}_Q$. Then, using the freshman's dream in
$\mathbb{F}_Q[y]$,
$$ \Big(\sum_i b_i y^{i}\Big)^{\! p} = \sum_i b_i^{p} y^{ip} = \sum_i a_i y^{ip} = h(y^p) = g(y), $$
so $g = (\,\sum_i b_i y^i\,)^p$ is a proper $p$-th power, contradicting irreducibility (its degree
$\ge 1$ and the base has degree $\ge 1$). Hence no inseparable irreducible exists; every
irreducible is separable. ∎

**Corollary 3 (separable $\iff$ squarefree over $\mathbb{F}_Q$).** For monic
$R \in \mathbb{F}_Q[y]$:
$$ R \text{ squarefree (no repeated irreducible factor)} \iff R \text{ separable (no repeated root in } \overline{\mathbb{F}_Q}). $$

*Proof.* Factor $R = \prod_i g_i^{e_i}$ into distinct monic irreducibles. By Lemma 2 each $g_i$ is
separable, so its roots in $\overline{\mathbb{F}_Q}$ are simple and the root-sets of distinct
$g_i, g_j$ are disjoint (distinct irreducibles are coprime, hence share no root). Therefore the
multiplicity of any root $\alpha$ of $R$ equals the unique $e_i$ with $g_i(\alpha)=0$. Thus $R$ has
a repeated root $\iff$ some $e_i \ge 2$ $\iff$ $R$ is non-squarefree. ∎

This is the precise sense in which **the discriminant locus, the non-squarefree locus, and the
"needs-refinement" (non-separable residual) locus coincide over every finite field, with no
inseparable-irreducible exceptions in any characteristic.** Wildness (Artin–Schreier
inseparability) can only appear for the *infinite* perfect-closure phenomena of the $p$-adic
tree (slopes, lifting) — never inside a residue-field count.

### 1.2 The universal non-squarefree / squarefree counts

**Theorem A (squarefree count).** For all prime powers $Q$ and all $m \ge 2$,
$$ \#\{\text{squarefree monic of degree } m \text{ over } \mathbb{F}_Q\} = Q^{m} - Q^{m-1}, $$
hence $\#\{\text{non-squarefree monic of degree } m\} = Q^{m-1}$. (For $m = 1$ all $Q$ monic
linears are squarefree; for $m = 0$ the empty product is squarefree.)

We give three independent proofs; any one suffices, and they reinforce that the count is a
universal polynomial in $Q$.

**Proof 1 (direct bijection, cleanest).** Every monic $R$ of degree $m \ge 1$ factors uniquely as
$R = A\,B^{2}$ with $A$ **squarefree** and $B$ monic (collect each irreducible $g$ appearing to
power $e$: put $\lfloor e/2 \rfloor$ copies into $B$ and the parity $e \bmod 2$ copy into $A$; this
is the unique such decomposition with $A$ squarefree). Let $s_k = \#\{\text{squarefree monic deg }k\}$
and $N_k = Q^{k}$ the number of all monic of degree $k$. Counting by $\deg B = j$, $\deg A = m-2j$:
$$ Q^{m} \;=\; \sum_{0 \le j \le m/2} s_{m-2j}\, Q^{j}. \tag{$\ast$} $$
This is the coefficient form of the generating-function identity
$\sum_k N_k u^k = \big(\sum_k s_k u^k\big)\cdot\big(\sum_j Q^{j} u^{2j}\big)$, i.e.
$$ \frac{1}{1 - Q u} \;=\; \mathcal S(u)\cdot \frac{1}{1 - Q u^{2}}, \qquad
\mathcal S(u) := \sum_{k \ge 0} s_k u^{k}. $$
Hence
$$ \mathcal S(u) = \frac{1 - Q u^{2}}{1 - Q u} = (1 - Q u^2)\sum_{k\ge 0} Q^k u^k
= 1 + Q u + \sum_{m \ge 2}(Q^{m} - Q^{m-1}) u^{m}. $$
Reading off coefficients: $s_0 = 1$, $s_1 = Q$, and $s_m = Q^m - Q^{m-1}$ for $m \ge 2$. ∎

(Solving $(\ast)$ recursively also works: $s_0=1$, $s_1=Q$, and for $m\ge 2$,
$s_m = Q^m - \sum_{j\ge1} s_{m-2j}Q^j = Q^m - Q\cdot Q^{m-2} = Q^m - Q^{m-1}$ by induction, where
the inner sum telescopes because $\sum_{j\ge1}s_{m-2j}Q^j = Q\sum_{j\ge0}s_{(m-2)-2j}Q^j = Q\cdot Q^{m-2}$
using $(\ast)$ at degree $m-2$.)

**Proof 2 (Euler product / cycle index).** Let $N_d = N_d(Q)$ be the number of monic irreducibles
of degree $d$ over $\mathbb{F}_Q$ (Theorem B below). Unique factorization gives the zeta function of
$\mathbb{A}^1_{\mathbb{F}_Q}$,
$$ \sum_{m\ge0} (\#\text{monic deg } m)\,u^m = \sum_{m\ge0} Q^m u^m = \frac{1}{1-Qu}
= \prod_{d\ge1}(1-u^d)^{-N_d}, \tag{Z} $$
and, since squarefree means each irreducible appears to power $\le 1$, replacing the geometric
factor $(1-u^d)^{-1} = \sum_{e\ge0}u^{de}$ by $(1+u^d)$:
$$ \mathcal S(u) = \prod_{d\ge1}(1+u^d)^{N_d}
= \prod_{d\ge1}\frac{(1-u^{2d})^{N_d}}{(1-u^{d})^{N_d}}
= \frac{\prod_d (1-u^{2d})^{N_d}}{\prod_d (1-u^{d})^{N_d}}
\overset{(Z)}{=} \frac{1-Qu^{2}}{1-Qu}, $$
where the numerator uses (Z) with $u \mapsto u^2$: $\prod_d(1-u^{2d})^{N_d} = (1/(1-Qu^2))^{-1}
= 1 - Q u^2$. Reading coefficients reproduces Theorem A. ∎

**Proof 3 (separability and the derivative map).** By Corollary 3, non-squarefree $=$ non-separable.
A monic $R$ of degree $m$ is non-separable iff $\gcd(R,R') \ne 1$. Pellet/Stickelberger-type
counting then gives $Q^{m-1}$ directly; but Proofs 1–2 are self-contained and we do not need this.
(Stated for completeness; not relied upon.)

**Universality.** $Q^m - Q^{m-1}$ is manifestly a single polynomial in the variable $Q$ with
integer coefficients, evaluated at the field size; **the characteristic $p$ never entered**: Proof 1
used only unique factorization and the count $Q^k$ of all monic polynomials (true over any field
of size $Q$); Proof 2 additionally used $N_d(Q)$, itself universal (Theorem B). This is assertion
**A11 / R3** of the project, now proved rather than asserted.

---

## 2. Part (b): all shape counts are universal polynomials in $Q$

### 2.1 The number of monic irreducibles is a universal polynomial

**Theorem B (Gauss necklace count).** The number of monic irreducible polynomials of degree
$d \ge 1$ over $\mathbb{F}_Q$ is
$$ N_d(Q) = \frac{1}{d}\sum_{e \mid d} \mu(e)\, Q^{\,d/e} . $$
In particular $N_d(t) := \frac1d\sum_{e\mid d}\mu(e)t^{d/e} \in \mathbb{Q}[t]$ is a single
polynomial (of degree $d$, leading coefficient $1/d$), independent of $p$, with $N_d(Q)$ giving the
count for every prime power $Q$.

*Proof.* Standard (Lidl–Niederreiter, *Finite Fields*, Thm 3.25). Every element of $\mathbb{F}_{Q^d}$
is a root of a unique monic irreducible over $\mathbb{F}_Q$ whose degree divides $d$, and
conversely each monic irreducible of degree $e \mid d$ contributes $e$ roots lying in
$\mathbb{F}_{Q^d}$. Counting $|\mathbb{F}_{Q^d}| = Q^d$ gives $\sum_{e\mid d} e\, N_e(Q) = Q^d$.
Möbius inversion over the divisor lattice yields $d\, N_d(Q) = \sum_{e\mid d}\mu(e)Q^{d/e}$.
Since $d\mid \big(\sum_{e\mid d}\mu(e)t^{d/e}\big)$ as polynomials (necklace integrality:
the right side is divisible by $d$ at every integer, and a fortiori the rational polynomial
$N_d(t)$ takes integer values at all prime powers; for the count itself it is an integer), $N_d$ is
well defined as a count. The integrality of the *coefficients* is not needed: $N_d(t)\in\mathbb{Q}[t]$
suffices for universality. ∎

That $N_d(Q)$ depends on $Q$ only — never on $p$ — is the elementary but central point: the lattice
of subfields of $\mathbb{F}_{Q^d}$ and their sizes are governed purely by the exponent
arithmetic $e \mid d$, with sizes $Q^{d/e}$, and Frobenius $x\mapsto x^Q$ (not $x\mapsto x^p$) is the
relevant generator. Characteristic is invisible.

### 2.2 Shape counts via multiset selection

Fix a shape $\lambda$. Group it by irreducible-factor degree: let $\lambda$ specify that, for each
$d \ge 1$, the polynomial has exactly $r_d \ge 0$ irreducible factors of degree $d$ **counted with
multiplicity** (so $\sum_d d\, r_d = m$, and all but finitely many $r_d$ are $0$). Note a shape only
records degrees-with-multiplicity, not which specific irreducibles occur (this matches L2: lifting
depends on factor degrees and multiplicities, and the symmetric/Frobenius bookkeeping over the
choice of irreducibles is exactly the count we now compute).

**Theorem C (shape count).** For any shape $\lambda = (r_d)_{d\ge1}$ with $\sum_d d r_d = m$,
$$ \boxed{\,S_\lambda(Q) \;=\; \prod_{d \ge 1} \binom{N_d(Q) + r_d - 1}{r_d}\, } $$
where $\binom{X}{r} = X(X-1)\cdots(X-r+1)/r!$ is the polynomial (in $X$) binomial coefficient. Each
factor is a polynomial in $N_d(Q)$, hence (by Theorem B) a polynomial in $Q$ with $\mathbb{Q}$-
coefficients; the finite product $S_\lambda(t) = \prod_d \binom{N_d(t)+r_d-1}{r_d} \in \mathbb{Q}[t]$
is therefore a **universal polynomial in $Q$, independent of $p$.**

*Proof.* By unique factorization in $\mathbb{F}_Q[y]$ (a PID, hence UFD), a monic $R$ of shape
$\lambda$ is determined by, and determines, an independent choice for each degree $d$ of a
**multiset of size $r_d$** drawn from the set $\mathcal I_d$ of monic irreducibles of degree $d$
(multiset because a given irreducible may be repeated to a higher power; e.g. $g^2$ uses the
multiset $\{g,g\}$). The choices over distinct $d$ are independent and their product reconstructs
$R$ uniquely (distinct irreducibles are coprime). The number of multisets of size $r$ from a set of
size $N = N_d(Q)$ is the multiset coefficient
$\left(\!\!\binom{N}{r}\!\!\right) = \binom{N + r - 1}{r}$. Taking the product over $d$ gives the
displayed formula. As a function of $Q$, each $\binom{N_d(Q)+r_d-1}{r_d}$ is a fixed polynomial of
$N_d(Q)$ (degree $r_d$ in $N_d$), and $N_d(Q) = N_d(t)|_{t=Q}$ with $N_d \in \mathbb{Q}[t]$; composing
polynomials keeps us in $\mathbb{Q}[t]$. Hence $S_\lambda(t)\in\mathbb{Q}[t]$ and
$S_\lambda(Q)$ is the count for every $Q$. ∎

**Remark (squarefree special case, distinct vs. multiset).** If $\lambda$ is squarefree
(all multiplicities $1$, i.e. the factors are $r_d$ **distinct** irreducibles of each degree $d$),
then the relevant count is **distinct** selection $\binom{N_d(Q)}{r_d}$, not the multiset
coefficient. Summing $\prod_d \binom{N_d(Q)}{r_d}$ over all squarefree shapes of degree $m$
reproduces $Q^m - Q^{m-1}$ (Theorem A), and summing the multiset coefficients over **all** shapes
of degree $m$ reproduces $Q^m$ (the zeta identity (Z)). Both identities were checked symbolically
in $Q$ to degree $m = 12$ (below). The distinction (distinct vs. multiset) is the one place a naive
assembly can go wrong; it is handled correctly by the boxed formula because a shape encodes
multiplicities, so a degree-$d$ block with $r_d$ factors that may coincide is exactly a multiset.

### 2.3 Total-mass and squarefree-mass identities (consistency, and re-derivation of (a))

Summing Theorem C over all shapes of degree $m$ must give all monic polynomials, $Q^m$; summing the
distinct-selection variant over squarefree shapes must give $Q^m - Q^{m-1}$. Both follow from the
Euler-product identities (Z) and $\mathcal S(u) = \prod_d(1+u^d)^{N_d}$ of §1, since expanding the
products by the multiset/subset binomial theorem term-by-term is exactly the shape decomposition.
Thus Part (b) **contains** Part (a) as the squarefree-mass corollary; we proved (a) separately for
the cleaner structural statement (perfectness ⇒ separability ⇒ discriminant locus).

---

## 3. Connection to L2: the residual-polynomial counts are universal

**Proposition D (L3 ⇒ universality of residual counts in the recursion).** Let a cluster node in
the L1–L2 recursion have residue field $\kappa = \mathbb{F}_{q^{\delta}}$ ($\delta \le n$,
$\delta$ depending only on the combinatorial tree to the node) and residual polynomial family of
degree $m$ (a monic family in $\kappa[y]$, equidistributed by Haar — A2/A4). Then:

1. The **needs-refinement locus** at the node = $\{R \in \kappa[y] \text{ monic deg } m :
   R \text{ non-separable}\}$ = $\{R \text{ non-squarefree}\}$ (Corollary 3), with count
   $(q^{\delta})^{m-1} = q^{\delta(m-1)}$ (Theorem A), **independent of $p$**.
2. For each separable-splitting shape $\lambda$ of $R$ over $\kappa$, the number of $R$ of that
   shape is $S_\lambda(q^{\delta})$ (Theorem C), a universal polynomial in $q^{\delta}$, hence
   a universal element of $\mathbb{Q}[q]$ after substituting $t = q^{\delta}$ — **independent of $p$.**

Consequently every **combinatorial weight** entering the L2 single-cluster volume formula is a
universal polynomial in $q$ (independent of $p$). Combined with L4 (each slope/cell volume is a
characteristic-independent $q$-power, using only $v(p)=1$ on the unramified base) and the recursive
structure (L5/L6), the per-cluster volume is a universal rational function of $q$.

*Proof.* Immediate from Theorems A, B, C and Corollary 3 with $Q = q^{\delta}$, once we note that
$\kappa$ is a finite field of size $q^{\delta}$ and that, by A2/A4 (Haar equidistribution of the
translated/rescaled cluster coefficients on the relevant congruence cell), the residual coefficients
$\bar R$ are **uniformly distributed over all monic $R$ of degree $m$ in $\kappa[y]$** — possibly
restricted to a sub-locus cut out by lower OM data, but that restriction is itself a union of the
shape strata counted above. The count of $R$ in any prescribed shape stratum is $S_\lambda(q^\delta)$,
a universal polynomial; dividing by the total $q^{\delta m}$ (also universal) gives a universal
conditional probability. ∎

**Why characteristic never enters — the structural summary.**
* Perfectness of $\mathbb{F}_Q$ (Lemma 1) is characteristic-uniform: it holds for **every** $p$.
* Therefore the only way a residual polynomial can fail to split into separable pieces is by a
  **repeated factor** (Corollary 3) — never by an inseparable irreducible. The repeated-factor
  (discriminant) locus has the **universal** count $Q^{m-1}$ (Theorem A), the same polynomial in
  $Q$ at $p=2,3$ as at large $p$.
* Frobenius $x \mapsto x^{Q}$ acts as a bijection on $\mathbb{F}_{Q^d}$-points (Lemma 1), so the
  number of irreducibles $N_d(Q)$ and all derived shape counts depend on $Q$ **as a point-count**,
  invisibly to the inseparable degenerations that occur on tangent spaces. This is the precise
  finite-field shadow of "Frobenius is bijective on points but inseparable on tangent spaces"
  (STRUCTURAL_MECHANISM, building block 3): the wild $p$-adic degeneration (Artin–Schreier) lives
  in the **slopes/lifting** of the tree, while every **residue-field count** sees only the universal
  discriminant-stratum polynomials.

---

## 4. Statement proved

> **L3 (Residue-field factorization-shape counts are universal polynomials in $Q$).**
> Let $\mathbb{F}_Q$ be any finite field ($Q = p^f$).
> **(a)** Every irreducible polynomial over $\mathbb{F}_Q$ is separable; non-separable
> $\iff$ non-squarefree; and $\#\{\text{non-squarefree monic of degree } m\} = Q^{m-1}$ for all
> $m \ge 1$, equivalently $\#\{\text{squarefree monic of degree } m\} = Q^m - Q^{m-1}$ for $m\ge2$.
> **(b)** For every factorization shape $\lambda$ of total degree $m$, the count of monic degree-$m$
> polynomials of shape $\lambda$ equals $S_\lambda(Q) = \prod_{d}\binom{N_d(Q)+r_d-1}{r_d}$ with
> $N_d(Q) = \frac1d\sum_{e\mid d}\mu(e)Q^{d/e}$; this is a single polynomial $S_\lambda(t)\in
> \mathbb{Q}[t]$, independent of the characteristic, with $S_\lambda(Q)$ the count for every $Q$.
> Applied with $Q = q^{\delta}$ at each OM node, all residual-polynomial counts in L2 are universal
> polynomials in $q$, independent of $p$ (Proposition D). ∎

---

## 5. Numerical checks (all passed)

Run with `python3` + `sympy`. Two scripts (since deleted from `tmp_L3/`); results recorded here.

**(a) Exhaustive over prime $Q\in\{2,3,5\}$, $m=1..5$:** for every $(Q,m)$,
`#squarefree = q^m - q^{m-1}` (for $m\ge2$; $=Q$ at $m=1$) **exactly**, and the count of
**irreducible-and-inseparable** monics (`deg(gcd(R,R'))≥1` with $R$ irreducible) is identically
$0$ — confirming the "no inseparable irreducible" gap is empty in every tested characteristic
(including $p=2,3 \le n$).

**(b) Exhaustive shape counts vs. formula:** over prime $Q\in\{2,3,5\}$, $m=1..5$, the full
factorization of every monic was computed (sympy `Poly(...,modulus=Q).factor_list`), shapes
tallied, and compared against the boxed multiset formula $\prod_d\binom{N_d+r_d-1}{r_d}$.
**All shapes match**, and $\sum_\lambda S_\lambda(Q) = Q^m$ in every case.

**Prime-power cross-check $Q\in\{4,8,9\}$, $m=1..5$:** the partition-of-the-space identity
$\sum_{\lambda \vdash m} S_\lambda(Q) = Q^m$ holds exactly (consistency of the universal polynomial
at non-prime $Q$, i.e. at fields where $p \ne Q$).

**Squarefree-via-formula $Q\in\{2,3,4,5,7,8,9\}$, $m=2..6$:** summing the **distinct**-selection
variant $\prod_d\binom{N_d}{r_d}$ over squarefree shapes gives $Q^m - Q^{m-1}$ exactly for all
listed $Q$ (prime and prime-power), confirming the distinct-vs-multiset distinction of §2.2.

**Symbolic generating-function identities (proof of the closed forms as polynomial identities in
the symbol $Q$, hence char-free):** using truncated power-series arithmetic with $N_d(t)$
symbolic,
* $\prod_{d\ge1}(1-u^d)^{-N_d(t)} = 1/(1-tu)$ — coefficient of $u^m$ equals $t^m$ for $m=0..12$;
* $\prod_{d\ge1}(1+u^d)^{N_d(t)} = (1 - t u^2)/(1 - tu)$ — coefficient of $u^m$ equals
  $t^m - t^{m-1}$ ($m\ge2$), $t$ ($m=1$), $1$ ($m=0$), for $m=0..12$.
Both verified to $u^{12}$ with `sympy.simplify(diff)==0`. This upgrades Theorem A from a per-$Q$
identity to an **identity of polynomials in $Q$**, the form L3 needs.

---

## 6. Honest gaps / scope notes

* **No gap in (a) or (b) themselves.** Lemmas 1–2, Corollary 3, Theorems A–C are standard finite-
  field algebra with complete proofs above; the numerics are corroboration, not load-bearing.
* **Interface assumption flagged (Proposition D), severity minor, owned by L2/L4 not L3.** L3 proves
  the *counts* are universal. Proposition D additionally uses (i) that the L2 reduction's
  combinatorial weights *are* exactly these shape counts over $\kappa=\mathbb F_{q^\delta}$, and
  (ii) A2/A4 Haar-equidistribution of residual coefficients so that "count of shape stratum /
  $q^{\delta m}$" is the correct conditional probability. Both are L1/L2/L4 statements assumed here
  per the proof skeleton; (i) in particular requires that the residual family at a node ranges over
  *all* monic degree-$m$ polynomials in $\kappa[y]$ (or a union of full shape strata), which is the
  content of the OM/MacLane residual-polynomial formalism. If a node's residual family were instead
  constrained to a sub-variety that is **not** a union of shape strata, L3's counts would not
  directly apply; standard OM theory (the residual polynomial is a genuine free monic polynomial in
  the residual variable) rules this out, but the rigorous statement lives in L2, not here.
* **$\delta \le n$ and finiteness of the residue degrees** is an L5 (depth/termination) input;
  L3 only needs that $\kappa$ is *some* finite field, which holds at every node.
* The functional equation $R_\sigma(1/t)=R_\sigma(t)$ is **not** an L3 statement; L3 provides the
  universal-polynomial counts that feed it (L7).
