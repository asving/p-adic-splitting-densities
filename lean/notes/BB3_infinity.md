# BB3-infinity — per-shape single-cluster volumes are uniform rational functions of $q$ at every OM/Montes order, all primes (wild included)

**Date:** 2026-06-15. **Role:** closing the single open frontier (G-A) of the uniform-rationality program
in the strong (regime-1, per-shape) form. **Status [AUDIT-FIX 2026-07-03 — honest reframing; the previous
status line "complete proof of L2core regime-1 at all OM/Montes orders, modulo one pinned,
$p$-independent external citation (the Guàrdia–Montes–Nart higher-order 'Theorem of the Polygon' /
'Theorem of the Residual Polynomial')" OVERSTATED]:** **proved for $n \le 4$; for general $n$ complete
modulo TWO OPEN LEMMAS** — **GAP-1**, the descend-restart Haar identification of the order-$r$ child with
a fresh standalone cluster over $K_{\delta f}$ (the §4.2 restart step; see the banner there and
`notes/RESTART_LEMMA.md`, being written), and **GAP-2**, order-$r$ residual equidistribution / cell-volume
bridge (M6$_r$/BB1$_r$). Neither reduces to a citation: GMN contains no measure-theoretic statements. The
mechanism is oracle-confirmed through OM order 5 with no counterexample; see
`WILD_UNIFORMITY_VERDICT.md`. Everything else — the *uniformity
consequence* — is derived here from BB1 ($=$ L4: a Newton cell volume is a characteristic-independent
lattice $q$-power) and BB3 ($=$ L3: over a finite field "needs descent" $=$ the discriminant locus, with
a universal $\mathbb F_Q$-point count and no inseparable-irreducible exceptions in any characteristic),
and is confirmed numerically at the first genuinely un-resummed order-$\ge 3$ wild branch.

This document is the merge of three independent attempts (`notes/BB3inf_attempt{1,2,3}.md`), taking the
strongest argument for each step: the clean GMN order-$r$ interface (Emphasis A); the explicit
root-merge-map / discriminant-locus heart with Frobenius-bijective-on-points argued at every order
(Emphasis B); and the transition-system induction skeleton $(\star)$–$(\star\star)$ with the manifest
char-independence of every transition coefficient (Emphasis C). Where the attempts disagreed it has been
reconciled (most importantly: the $n=6$ $(6,1)$ probability is the *derived* $\beta(3)$ value
$q^2(q-1)(q^2+1)/(q^5-1)$, **not** the naive $q/(q+1)$ — the data prefers the derived form at $\sim 11\sigma$
margin; see §7.2).

---

## 0. Setting, notation, and the precise statement

Fix the project conventions. $K/\mathbb Q_p$ is a finite **unramified** extension with residue field
$\mathbb F_q$ ($q = p^k$), ring $\mathcal O_K$, uniformizer $p$, normalized valuation $v(p) = 1$, Haar
measure $\mu$ with $\mu(\mathcal O_K) = 1$. **Unramifiedness is essential and is used throughout:
$v(p) = 1$ is the single normalization constant that carries all of the characteristic dependence, and it
is preserved by unramified base change.** For a finite unramified $K_\delta/K$ write $\mathcal O_\delta$,
residue $\mathbb F_{q^\delta}$, $\mu_\delta(\mathcal O_\delta) = 1$, and set $Q := q^\delta$. The
unramified index identity $[\mathcal O_\delta : p^m \mathcal O_\delta] = Q^m$ holds with the *same* $Q$ at
every prime.

**Cluster.** A *size-$e$ cluster at $0$ over $K_\delta$* is
$$
M_e^{(\delta)} = \{\, g \in \mathcal O_\delta[x] : g \text{ monic}, \deg g = e, \ \bar g = x^e \,\},
\qquad \mu_\delta(M_e^{(\delta)}) = Q^{-e}
$$
(all $e$ roots reduce to $0$; any other single residue class is reached by a $p$-independent
translation). The **conditional cluster measure** is $\widehat\mu := Q^{e}\,\mu_\delta|_{M_e^{(\delta)}}$,
total mass $1$.

**OM / Montes type (cluster-tree shape).** Following Guàrdia–Montes–Nart (**GMN**, *Newton polygons of
higher order in algebraic number theory*, Trans. Amer. Math. Soc. **364** (2012), 361–416,
arXiv:0807.2620), a *type of order $r$* is a chain
$$
\mathbf t = \big(\,(\phi_1; \lambda_1, \psi_1),\ \dots,\ (\phi_r; \lambda_r, \psi_r)\,\big),
$$
where inductively $\phi_i$ is an order-$i$ **key polynomial** (a monic lift of the previous residual
factor), $\lambda_i = -a_i/b_i \in \mathbb Q$ in lowest terms is a **slope** of the order-$i$ Newton
polygon $N_i$, and $\psi_i \in \mathbb F_i[y]$ is an **irreducible residual polynomial** over the order-$i$
**residue field** $\mathbb F_i$ — a *finite* extension of $\mathbb F_q$ with $[\mathbb F_i:\mathbb F_q]
= f_1\cdots f_{i-1} \mid n$. The combinatorial **shape** $T$ records only the tree of slopes
$\lambda_i$ (equivalently the $(a_i,b_i)$ pairs), the residual-polynomial *factorization shapes* at each
order (degrees and multiplicities, not the polynomials themselves), and the residue degrees
$f_i = \deg\psi_i$. Equivalently $T$ is the decorated ultrametric tree of roots in $\bar K$: pairwise
valuations $v(\alpha_i - \alpha_j)$ are the tree distances.

The **type-resolved cluster volume** for a shape $T$ of size $e$ is
$$
C_e^{(\delta)}(T; q) := \mu_\delta\{\, g \in M_e^{(\delta)} : \text{the OM type of } g \text{ realizes } T \,\},
\qquad
\widehat C_e^{(\delta)}(T; q) := Q^{e}\,C_e^{(\delta)}(T; q).
$$

> **Lemma BB3-$\infty$ ($=$ L2core regime-1 at every OM order).**
> For every cluster-tree shape $T$ of size $e \le n$ and every base residue degree $\delta \le n$, and at
> **every** OM/Montes order $r \ge 1$ in the resolution of $T$, the volume $C_e^{(\delta)}(T; q)$ is a
> **uniform rational function of $q$**: there is a single $R_{e,\delta,T} \in \mathbb Q(t)$ with
> $$
> C_e^{(\delta)}(T; q) = R_{e,\delta,T}(q)
> \qquad \text{for every prime power } q \text{ and every residue characteristic } p,
> $$
> **including wild $p \mid e$** and at arbitrarily deep orders $r$ (including a size-$\ge 3$ inseparable
> child of an inseparable node). On each Newton-polygon cell of each OM order the contribution factors as
> $$
> \underbrace{(\text{lattice } q\text{-power})}_{\text{BB1 } = \text{ L4}}
> \ \times\ \underbrace{(\text{residual-factorization count over } \mathbb F_r)}_{\text{BB3 } = \text{ L3}}
> \ \times\ \underbrace{(\text{child-cluster volumes})}_{\text{induction}},
> $$
> with the unique non-progressing (rescale self-loop) cell summed by $1/(1 - Q^{-(e(e+1)/2 - 1)})$. The
> inseparable (wild) residual node contributes the **same** per-shape volume as the corresponding tame
> node. Moreover $R_{e,\delta,T}(q) = R_{e,1,T}(q^\delta)$ (unramified base change), so it suffices to
> treat $\delta = 1$.

This closes the open frontier G-A in the strong (per-shape) form for $n \le 4$; for general $n$ the
argument is complete modulo the two open Haar-measure lemmas GAP-1 (descend-restart identification, §4.2
banner) and GAP-2 (M6$_r$ equidistribution) — see `WILD_UNIFORMITY_VERDICT.md`. [AUDIT-FIX 2026-07-03:
previously "modulo the single $p$-independent GMN order-$r$ citation whose uniformity consequence is
derived" — an overstatement; the GMN citation covers the combinatorial half only, not the measure
theory.] Equivalently, $\widehat C_e^{(\delta)}(\cdot;q)$
is a $p$-independent probability vector of rational functions of $q$.

The proof is by induction on the OM order $r$. §1 states the GMN order-$r$ interface (the sole external
import). §2 records BB1 at order $r$. §3 records BB3 at order $r$, the heart, in the root-merge-map form.
§4 sets up the transition system $(\star)$ and runs the induction. §5 nails the four subtle wild points.
§6 is termination (the induction is finite, $p$-independently). §7 is the mandatory consistency check
against the verified $n=4$, $n=6$ instances and a fresh stratum. §8 is the honest ledger.

---

## 1. The GMN order-$r$ interface (the single external import, flagged G-A′)

This is the **only** load-bearing import. It is a purely structural, combinatorial statement about the
existence and behaviour of the higher-order key polynomials. [AUDIT-FIX 2026-07-03: scope corrected —
the previous clause "it holds over **any** complete discretely valued field and is therefore
**$p$-independent**, carrying no wild-prime difficulty" is FALSE as a citation. GMN fixes a finite
extension $K/\mathbb Q_p$ as base field (`gmn_v2.txt:482`) and proves its theorems **per fixed $p$**.
Our $K/\mathbb Q_p$ is finite unramified — exactly GMN's scope — so the import applies per $p$, in
identical combinatorial form at every prime, with wild ramification $p \mid e_i$ inside that scope; the
$p$-independence of the assembled volumes is **derived** from the $p$-free shape of the per-$p$
combinatorial imports, not imported.] We state exactly
what we use and cite it; we do **not** re-derive the higher key-polynomial construction.

> **(GMN-Polygon, order $r$).** [CORRECTED 2026-06-17: order-$r$ Newton polygon $N_r$ defined in
> GMN §2.5, a principal (lattice) polygon Def. 1.1; valuation $v_r$ Def. 2.5 / Prop. 2.6; key
> polynomial Thm. 2.11 / Def. 2.12; **Theorem of the Polygon in order $r$ = Thm. 3.1**.] Given an order-$(r-1)$ type
> with a **repeated** order-$(r-1)$ residual factor $\psi_{r-1}$ of multiplicity $\ge 2$, there is an
> order-$r$ **key polynomial** $\phi_r$ (a monic lift of $\psi_{r-1}$ of degree $m_r = m_{r-1}\,e_{r-1}
> f_{r-1}$, $e_{r-1} = b_{r-1}$ the slope denominator) whose $\phi_r$-adic order-$r$ Newton polygon
> $N_r(g)$ is a **lattice polygon** in $\mathbb Z \times \tfrac{1}{D_r}\mathbb Z$, where
> $D_r = e_1\cdots e_{r-1} \le e$ is a $p$-independent integer. Its faces, lengths, and heights are
> lattice data.

> **(GMN-Residual, order $r$).** [CORRECTED 2026-06-17: residual polynomial of order $r$ = Def. 2.21;
> **Theorem of the Residual Polynomial in order $r$ = Thm. 3.7** (NOT Thm. 2.26, which is the Theorem
> of the *product* in order $r$); leaf dichotomy Cor. 3.8; descent trigger Lemma 3.11(3).] Each face of $N_r$ of slope
> $\lambda_r = -a_r/b_r$ and lattice length $\ell_r$ carries a **residual polynomial**
> $R_r = R_{\lambda_r}(g) \in \mathbb F_r[y]$, monic of degree $d_r = \ell_r/b_r$, over the **finite**
> order-$r$ residue field $\mathbb F_r = \mathbb F_{q^{\,\delta f_1\cdots f_{r-1}}}$ with
> $[\mathbb F_r:\mathbb F_q] = \delta f_1\cdots f_{r-1} \mid \delta n$. The factorization of $R_r$ over
> $\mathbb F_r$ governs the descent:
> - a residual factor of **multiplicity 1** produces an **Okutsu–Montes leaf** — an irreducible $p$-adic
>   factor with explicit, $p$-independent data $(e^\ast, f^\ast)$, $e^\ast = b_1\cdots b_r$,
>   $f^\ast = f_1\cdots f_r$;
> - a residual factor of **multiplicity $\ge 2$** is not yet resolved: it triggers the order-$(r+1)$
>   refinement (a new key polynomial $\phi_{r+1}$), recursing into a child cluster of strictly smaller
>   size.

> **(GMN-Termination).** [GMN §4, the factorization/regularity theorem.] For a separable $g$ the descent
> stops at finite order; combined with defectlessness of $K$ (char $0$, complete discrete — §6) the OM
> tree has $\le e$ leaves and finite depth.

**What is used, distilled to three $p$-independent structural facts (I)–(III).**
- **(I) Finite-field residuals at every order:** $R_r \in \mathbb F_r[y]$ with $\mathbb F_r$ a finite
  field, $[\mathbb F_r:\mathbb F_q] \mid \delta n$. This is the linchpin: BB3 (§3) is a *finite-field*
  statement, so it applies verbatim at every order, with no inseparable-irreducible exceptions in any
  characteristic.
- **(II) Lattice polygons at every order:** $N_r$ is a lattice object over $\mathbb Z$ (after clearing
  the $p$-independent denominator $D_r$), with combinatorics independent of $p$. This is what BB1 (§2)
  consumes.
- **(III) Repeated-factor descent, finite and $p$-independent:** the trigger is *exactly* a repeated
  factor of $R_r$, descent strictly reduces cluster size off the self-loop, and the depth is finite and
  $p$-independently bounded (GMN-Termination + L5fix, §6).

No uniformity, rationality, or volume statement is imported from GMN. [AUDIT-FIX 2026-07-03: corrected
from "The wild/inseparable case is the **generic** case of the GMN machinery, not an exception to it" —
GMN works per fixed finite $K/\mathbb Q_p$ (`gmn_v2.txt:482`). What is true, and what we use, is that
wild ramification $p \mid e_i$ is an ordinary, unexceptional case *inside* GMN's per-$p$ scope (the
higher polygon is a combinatorial
Newton polygon of $\phi_r$-expansions; it never asks for separability of any residual nor for the residue
characteristic to miss any $e_i$); the $p$-independence of our conclusions is derived, not imported.]
This is the precise content of the flag G-A′: only (I)–(III) are
imported, per $p$.

---

## 2. BB1 at order $r$: the polygon cell volume is a characteristic-independent lattice $q$-power

This is **building block 1** ($=$ L4 in the program; `L4_proof.md`, solid), applied at order $r$ via
(GMN-Polygon).

> **BB1$_r$.** Fix an order-$r$ Newton polygon $N_r = \Pi$ (a lattice polygon over $\mathbb Z \times
> \tfrac1{D_r}\mathbb Z$, $D_r \le e$ a $p$-independent integer) and one residual-shape stratum $S$ on
> each face. The Haar volume of $\{g \in M_e^{(\delta)} : N_r(g) = \Pi,\ \text{residual shape} = S\}$ is
> $$
> (1 - Q^{-1})^{V(\Pi)} \cdot Q^{-A(\Pi)} \cdot N_S(Q_r),
> $$
> where $V(\Pi), A(\Pi) \in \mathbb Z_{\ge 0}$ are **pure lattice data** of $\Pi$ (number of strictly-above
> lattice points; number of on-line non-leading interior coordinates forced to be units), and $N_S(Q_r)$
> is the residual count of BB3$_r$ (§3). The exponent $A(\Pi)$ is **independent of $p$**: a slope $a/b$
> with $p \mid b$ (wild) gives the *same* lattice polygon — hence the *same* exponent — as a tame slope
> with the same $(a,b)$.

**Why.** Imposing $N_r(g) = \Pi$ is a system of valuation conditions on the $\phi_r$-adic coefficients of
$g$: $v = h_i$ (equality) at on-edge lattice points and $v \ge \lceil\text{line}\rceil$ (a ball) strictly
above. Via $[\mathcal O_\delta : p^m\mathcal O_\delta] = Q^m$ and product Haar, an equality condition on a
coordinate has mass $(1-Q^{-1})Q^{-h_i}$ and a ball condition has mass $Q^{-(\text{height})}$ — depending
on the **integer height only**. By (GMN-Polygon) the heights are lattice data of $\Pi$, intrinsic and
$p$-independent. Only $v(p) = 1$ enters; the slope denominator $b$ appears only through where the lattice
points fall, which is fixed by $(a,b)$ as integers. **Wild $=$ tame at the volume level, at every order.**

**Verified** (`L4_proof.md`, `notes/l2core_verify.py`): Eisenstein degree-$e$ volume $(q-1)/q^{e+1}$ at
every prime including wild totally ramified $p \mid e$; slope-$1/2$ ($p=2$), $1/3$ ($p=3$), $1/4$ ($p=2$)
cell volumes characteristic-independent; the self-loop exponents $2,5,9,14$ for $e=2,3,4,5$ (the lattice
exponent $e(e+1)/2-1$); and the $\delta>1$ base change $C_e^{(\delta)}(q) = C_e^{(1)}(q^\delta)$. The
explicit closed combinatorial formula for $A(\Pi)$ at arbitrary order is verified $e \le 4$; BB1's
*content* — cell volume $=$ char-independent $q$-power, which is all the induction needs — is established
(§8, minor deferral).

---

## 3. BB3 at order $r$: the refinement-trigger locus has universal count — the heart

This is **building block 3** ($=$ L3; `L3_proof.md`, solid), applied at order $r$ via (GMN-Residual).
**This is the only place wildness could enter the count, and it does not.** We formulate it in the
root-merge-map / discriminant-locus form (the critic's "how to close").

### 3.1 The residual family and the descent trigger

By (GMN-Residual) and fact (I), the order-$r$ residual $R_r$ is a monic degree-$d_r$ polynomial over the
**finite** residue field $\mathbb F_r$, $Q_r := |\mathbb F_r| = q^{\,\delta f_1\cdots f_{r-1}}$ (a power of
$p$). As the on-line $\phi_r$-adic coefficients of $g$ vary over their Haar cells, $R_r$ ranges over **all**
monic degree-$d_r$ polynomials over $\mathbb F_r$ (the order-$r$ residual-coefficient map is a submersion
onto $\mathbb A^{d_r}(\mathbb F_r)$; this is the order-$r$ analogue of the verified order-1 free-residue
statement of BB1 — the residual-equidistribution input M6, §8). The descent trigger (fact (III)) is
*exactly*: $R_r$ has a repeated factor. As identities of subschemes of $\mathbb A^{d_r}$ over $\mathbb F_r$,
$$
\{R_r \text{ needs order-}(r{+}1)\text{ descent}\}
\ \overset{(a)}{=}\ \{R_r \text{ not squarefree}\}
\ \overset{(b)}{=}\ \{R_r \text{ not separable}\}
\ \overset{(c)}{=}\ \{\operatorname{disc} R_r = 0\}
\ =:\ \Delta_{d_r} \subset \mathbb A^{d_r}.
$$

### 3.2 The root-merge map and the universal count

> **BB3$_r$.** Over the finite field $\mathbb F_r$ ($Q_r = |\mathbb F_r|$):
> $$
> \#\{R_r \text{ monic deg } d_r, \text{ not squarefree}\} = \# \Delta_{d_r}(\mathbb F_r) = Q_r^{\,d_r-1}
> \qquad (d_r \ge 2),
> $$
> a **single polynomial in $Q_r$, characteristic-independent**, valid at every $p$ including wild
> $p \mid d_r$ and $p \mid e$. Moreover the count of monic degree-$d_r$ polynomials of **any fixed
> factor-multiplicity shape** $\lambda \vdash d_r$ is a **single polynomial $N_\lambda(Q_r) \in
> \mathbb Z[Q_r]$, the same for all $p$**.

**(a)$=$(b)$=$(c).** Over a field, squarefree $\iff$ no repeated factor $\iff \gcd(R_r,R_r')=1 \iff
\operatorname{disc} R_r \ne 0$. The only way "separable" could differ from "squarefree" is an
**inseparable irreducible factor** $\pi = \tilde\pi(y^p)$. **Over a finite field this never happens:**
$\mathbb F_r$ is **perfect** (Frobenius $x\mapsto x^p$ is bijective on a finite field, so every element is
a $p$-th power, so $y^p - c = (y-c^{1/p})^p$ is never irreducible; more generally every irreducible over a
finite field is separable). Hence over $\mathbb F_r$, **at every order $r$, in every characteristic**,
"not separable $=$ not squarefree $=$ discriminant locus," with **no inseparable-irreducible exceptions**.

**The count $Q_r^{d_r-1}$.** Total monic degree-$d_r$ is $Q_r^{d_r}$. The squarefree count is the
characteristic-independent Carlitz/zeta identity: the squarefree generating function over $\mathbb F_{Q_r}$
is $\zeta(s)/\zeta(2s) = (1-Q_r t^2)/(1-Q_r t)$ in $t = Q_r^{-s}$, giving coefficient $Q_r^d - Q_r^{d-1}$ of
$t^d$ for $d \ge 2$. Every step is an identity of formal power series with $p$-independent integer
coefficients. Hence $\#\Delta_{d_r}(\mathbb F_r) = Q_r^{d_r} - (Q_r^{d_r} - Q_r^{d_r-1}) = Q_r^{d_r-1}$.

**The fine shape counts $N_\lambda(Q_r)$.** A monic $R_r$ factors uniquely as $\prod_j \pi_j^{m_j}$,
$\pi_j$ distinct monic irreducibles. For a fixed multiplicity multiset $\lambda$ (with the degrees
$\deg\pi_j$ summing appropriately), the count is a sum over degree-partitions of products of binomials of
the Gauss/necklace count $I_d(Q_r) = \tfrac1d\sum_{e\mid d}\mu(e)Q_r^{d/e}$ of monic irreducibles of degree
$d$ — a Möbius sum of powers of $Q_r$, manifestly $p$-independent. Since $\operatorname{Sym}^k\mathbb A^1
= \mathbb A^k$ (elementary symmetric functions are coordinates), these are polynomials in $Q_r$. Hence
$N_\lambda(Q_r) \in \mathbb Z[Q_r]$, the **same polynomial for every $p$**, evaluated at the prime power
$Q_r$. $\qquad\square$

**Merge-map / image-count form (the conceptual content).** The multiplicity-$\lambda$ stratum is the
**image of the root-merge map**
$$
\mathfrak m_\lambda : \big(\text{tuples of distinct monic irreducibles } (\pi_j)\big) \longrightarrow
\prod_j \pi_j^{m_j},
$$
a finite morphism of affine $\mathbb Z$-schemes, **generically injective** (unique factorization: a
polynomial determines its factor multiset) of **$p$-independent degree** (the symmetry factor
$\prod_m c_m!$ over equal multiplicities — a combinatorial integer). Its image therefore has the universal
$\mathbb F_r$-point count $N_\lambda(Q_r)$ in every characteristic. The discriminant locus $\Delta_{d_r}$
is the union of these strata for $\lambda \ne (1^{d_r})$.

**Verified exhaustively (this analysis):**
- **Prime fields** $\mathbb F_p$, $p \in \{2,3,5,7\}$, $d \in \{2,3,4\}$: $\#\Delta_d = p^{d-1}$ exactly
  (12/12), inseparable-irreducible count $= 0$ in every case (`/workspace-vast/asving/tmp/bb3_ff_check.py`).
- **Higher-order prime-power residue fields** $\mathbb F_4, \mathbb F_8$ (**wild $p=2$**),
  $\mathbb F_9, \mathbb F_{25}$, built explicitly as $\mathbb F_p[t]/(\text{irred})$, $d \in \{2,3\}$:
  $\#\Delta_d = Q^{d-1}$ exactly (8/8), **identical formula to the prime fields including the wild $p=2$
  fields** (`/workspace-vast/asving/tmp/bb3_ext_check.py`). This is the decisive check that BB3 survives
  at the higher-order residue fields where order-$\ge 2$ nodes live.
- **Fine shape counts**, $d=4$, across $p \in \{2,3,5,7,11\}$: every full $(\deg,\text{mult})$-shape count
  is a single integer polynomial in $q$ (`/workspace-vast/asving/tmp/fine_fast.py`). E.g.
  $(y-\rho)^4$-type $= q$ (deg 1, valid incl. $p=2$); four distinct linear $= q(q-1)(q-2)(q-3)/24$
  (vanishing at $q=2,3$ by the polynomial itself); $(2,2)$-type (irreducible quadratic squared) $=
  q(q-1)/2$. These are the merge-map image counts, manifestly $p$-independent.

### 3.3 The wild / inseparable node: Frobenius bijective on points, at every order

This is the subtle point the task demands be argued explicitly: *does BB3's universal count survive when
$p$ divides the relevant ramification, or when $R_r$ is itself inseparable?* **Yes**, for two reasons.

**(i) An inseparable $R_r$ is already counted.** A *specific* $R_r$ may be inseparable — at a wild
order-$r$ node $R_r = (y-\rho)^p$ or $y^p - c$ can occur (Artin–Schreier-type). But an inseparable
polynomial has a repeated factor ($\gcd(R_r, R_r') \ne 1$), so it is **already non-squarefree**, already
inside $\Delta_{d_r}$, already counted in $Q_r^{d_r-1}$. By §3.2(a)$=$(b) over the perfect field
$\mathbb F_r$ there are no inseparable irreducibles, so inseparability adds no point and removes none. The
count is $Q_r^{d_r-1}$ whether or not any particular $R_r$ is inseparable.

**(ii) The merge map may itself be inseparable, but it is bijective on points.** The canonical instance
(the $n=4$ wild atom, §7.3): the order-1 double-residual locus inside $\{R = y^2 + \bar b y + \bar a\}$ is
$$
\text{odd } p:\ \{\bar b^2 = 4\bar a\}\ \text{(a smooth parabola; merge } \rho\mapsto(-2\rho,\rho^2)\text{)},
\qquad
p = 2:\ \{\bar b = 0\},\ R = (y+\sqrt{\bar a})^2\ \text{(a line; merge } \rho\mapsto(0,\rho^2) = \mathrm{Frob}\text{)}.
$$
These are **geometrically different subvarieties** — different tangent cone, different smoothness; the
$p=2$ line is the image of a *purely inseparable* (Frobenius) map. *This is exactly the data that broke
Prop 5.3* (an $S_n$-equivariant tangent-space statement). **But both have the same $\mathbb F_q$-point
count** $q-1$ (punctured, $\rho \in \mathbb F_q^\ast$), because $\rho\mapsto\rho^2$ (Frobenius at $p=2$) is
**bijective on $\mathbb F_q$-points** (every finite-field element has a unique $p$-th root), even though its
differential is $0$. *Volume / point-count lives on points; smoothness lives on tangent spaces.* At an
order-$r$ wild node the merge map is some composite of squarings, $p$-power maps, and translations over
$\mathbb F_r$ — possibly purely inseparable — but it is always a morphism of $\mathbb F_r$-varieties that
is **bijective on $\mathbb F_r$-points** onto $\Delta_{d_r}$ (Frobenius and its powers are bijective on the
points of a perfect field), with the universal count $Q_r^{d_r-1}$. The induction never sees a
characteristic-dependent count, however deep or wild the node.

This is the structural mechanism of `STRUCTURAL_MECHANISM.md`, read at order $r$: *the same fact that
broke (Prop 5.3, a tangent-space statement) and survived (the density, a point-count statement), read on
two different functors, all the way up the OM tower.*

---

## 4. The induction on OM order

We organize the induction (Emphasis C) as a **transition system** on cluster sub-types, in which every
transition coefficient is a manifest element of $\mathbb Q(q)$ with no $p$-dependence.

### 4.1 The three moves and the transition equation

From a state — a size-$e$ cluster over $K_\delta$ with OM data accumulated so far — read the order-$r$
Newton polygon $N_r$. There are exactly three move types, each with transition coefficient in
$\mathbb Q(q)$:

- **(B) Branch (degree drop).** $N_r$ has $\ge 2$ faces, or one face whose residual $R_r$ has $\ge 2$
  coprime irreducible factors. By L1 (Hensel/slope splitting with **exact** unit-resultant product
  measure, `L1_proof.md`), the cluster decomposes into coprime children of sizes $< e$ summing to $e$,
  **mutually independent**, so the conditional law factors as a **convolution** over children (L6M4
  Lemma 2). Transition coefficient $=$ BB3$_r$ residue-config count ($Q_r$-polynomial) $\times$ BB1$_r$
  cell volume ($Q$-power).
- **(D) Descend (repeated-factor refinement).** A residual factor $P \mid R_r$ of degree $f$ and
  multiplicity $\mu \ge 2$ gives a **child cluster of size $\mu$ over $K_{\delta f}$** (the residue
  degree $f$ peeled into the base extension; the $b$-ramification into $A(\Pi)$). Off the self-loop
  $\mu \le d_r < e$ (since $b \ge 2 \Rightarrow d_r = \ell_r/b < e$, or a branch has already occurred), so
  the child is a strictly-smaller state.
- **(S) Self-loop (no degree drop).** The unique non-progressing cell: $b = 1$, $R_r = (y-c)^e$ (one
  residual root of full multiplicity — all $e$ roots one notch deeper). Translate by the residual root and
  rescale $x \mapsto p\,x$: a measure-preserving bijection onto a fresh copy of $M_e^{(\delta)}$ up to the
  **Vandermonde-weighted Jacobian** $Q^{-e(e+1)/2}$ times the $Q$ residue translates, i.e. per-level ratio
  $w(e) := Q^{-(e(e+1)/2-1)}$ (densities are volumes, not point counts). It returns to the **same** state
  with the same conditional law.

Collecting these, the conditional cluster law satisfies the **fixed-point equation**
$$
\widehat C_e^{(\delta)}[\sigma]
= T_{\mathrm{branch}}[\sigma] + T_{\mathrm{descend}}[\sigma] + w(e)\,\widehat C_e^{(\delta)}[\sigma],
\qquad w(e) = Q^{-(e(e+1)/2-1)},
\tag{$\star$}
$$
with geometric closure
$$
\widehat C_e^{(\delta)}[\sigma]
= \frac{T_{\mathrm{branch}}[\sigma] + T_{\mathrm{descend}}[\sigma]}{1 - Q^{-(e(e+1)/2-1)}}.
\tag{$\star\star$}
$$
(The self-loop is **resummed** here, not depth-counted; its chain length is unbounded over the space but
finite per separable point — §6. Conflating the two caused the historical false depth bound.) The
exponents are $e(e+1)/2-1 = 2,5,9,14$ for $e = 2,3,4,5$; $e=3$ gives $1-Q^{-5}$, $Q^5-1 = (Q-1)\Phi$ with
$\Phi = q^4+q^3+q^2+q+1$ — the paper's $\Phi$ (L5fix(d), derived from the self-similar Vandermonde integral
$I_e$; verified symbolically and by MC, `notes/l5fix_*.py`).

> **Proposition 1 (transition coefficients are char-independent elements of $\mathbb Q(q)$).** Every
> coefficient appearing in $T_{\mathrm{branch}}$, $T_{\mathrm{descend}}$, and $w(e)$ is a fixed element of
> $\mathbb Q(q)$ with **no dependence on $p$**, and the self-loop pivot $1 - w(e)$ is nonzero at every
> prime power $q \ge 2$ (indeed $\ge 1 - q^{-2} \ge 3/4$; poles only at roots of unity, never at a prime
> power or its reciprocal).

*Proof.* $w(e)$ is a $q$-power (§4.1, L5fix(d)). The branch/descend coefficients are BB3$_r$ counts
($Q_r$-polynomials, §3.2, no inseparable-irreducible exceptions) and BB1$_r$ cell volumes
$(1-Q^{-1})^V Q^{-A}$ with $V,A$ pure lattice data (§2, only $v(p)=1$ enters). All are in $\mathbb Q(q)$
and $p$-free. $\qquad\square$

### 4.2 The induction

> **[AUDIT-FIX 2026-07-03] BANNER — the descend-restart step below is GAP-1, OPEN.** The inductive step
> silently uses the identification of the conditional Haar law of an order-$r$ descend child (type $t$,
> side $S$, repeated residual factor $P^\mu$, $\deg P = f$) with the standalone size-$\mu$ cluster law
> $\widehat C_\mu^{(\delta f)}(q) = \widehat C_\mu^{(1)}(q^{\delta f})$ over $K_{\delta f}$ — including
> path-independence of the child law, the parent slope $b$ as a pure spectator ($e \mapsto be$), and the
> inherited deep self-loop ratio $(q^{\delta f})^{-(\mu(\mu+1)/2-1)}$. This measure identification is
> proved nowhere in the corpus and has NO citation: GMN contains no measure-theoretic statements, Igusa
> §7.4 is a change-of-variables formula, Denef 1984 is fixed-$p$; the Lean layer axiomatizes exactly this
> content as `AX_cellRecursion` (`MINIMAL_PADIC_AXIOMS.md:198`, "THE load-bearing axiom", GENUINE-GAP).
> It is **GAP-1** of `WILD_UNIFORMITY_VERDICT.md` (BLOCKING for general $n$); a proof is being written as
> `notes/RESTART_LEMMA.md` (route: the $\phi_{r+1}$-adic development as a unipotent-triangular
> Haar-preserving coordinate change; the cell event a product event in these coordinates; a
> measure-preserving bijection cell $\to M_\mu^{(\delta f)} \times$ spectators; path-independence by
> composing two such bijections; GMN Thm 2.26, the Theorem of the product in order $r$, supplies the
> combinatorial half). Empirically unfalsified through OM order 5. Until `RESTART_LEMMA.md` lands, the
> induction below is complete only modulo GAP-1 (and GAP-2 $=$ M6$_r$, see §8).

Induct on the pair (OM order $r$, size $e$) under the lexicographic order with size strictly decreasing
off the self-loop. The claim at each $(e,\delta,T)$: $C_e^{(\delta)}(T;q) \in \mathbb Q(t)$, $p$-uniform.

**Base cases.** A size-1 cluster is a unit, $C_1^{(\delta)} \equiv 1$. A multiplicity-1 (separable)
residual factor at any order is an **Okutsu–Montes leaf** (GMN-Residual): its contribution is a BB1$_r$
$q$-power $\times$ a BB3$_r$ separable-residual count, with no recursion — both $p$-uniform by §§2–3. (E.g.
the slope-$1/e$ Eisenstein leaf with linear residual $d=1$ has volume $(q-1)/q^{e+1}$ at every $p$, §7.4.)

**Inductive step $r-1 \Rightarrow r$.** By (GMN-Polygon) and BB1$_r$ the order-$r$ polygon $N_r$ decomposes
the cluster into finitely many faces; choosing $N_r$ and a residual-shape stratum $S$ on each face has Haar
volume
$$
(1-Q^{-1})^{V(N_r)}\, Q^{-A(N_r)} \prod_{\text{faces } F} N_{S_F}(Q_r)
\tag{4.1}
$$
— a uniform rational function of $q$ with $p$-independent lattice exponents (BB1$_r$) and $p$-independent
residual counts (BB3$_r$). Resolving the children via (GMN-Residual): each multiplicity-1 factor is a leaf
(base case); each multiplicity-$\mu \ge 2$ factor of residue degree $f$ descends to a child cluster of
size $\mu \le d_r < e$ over $K_{\delta f}$, **strictly smaller**, hence $p$-uniform by the inductive
hypothesis, re-expressed by base change as $\widehat C_\mu^{(\delta f)}(q) = \widehat C_\mu^{(1)}(q^{\delta
f})$ (L1 Frobenius descent over unramified $K_{\delta f}$, the paper's `lemma: local integrals`,
$p$-independent; the substitution $t \mapsto t^{\delta f}$ keeps it in $\mathbb Q(q)$). The unique
non-progressing event is the self-loop $(\star)$, resummed by $(\star\star)$. Assembling:
$$
C_e^{(\delta)}(T;q)
= \frac{1}{1 - Q^{-(e(e+1)/2-1)}}
\sum_{\text{order-}r \text{ cells of } T}
\Big[(1-Q^{-1})^{V}Q^{-A} \prod_F N_{S_F}(Q_r) \prod_{\text{children}} C_\mu^{(\delta f)}(T_{\text{child}};q)\Big],
\tag{4.2}
$$
a **finite** $\mathbb Q(q)$-rational combination (finitely many faces, residual shapes, children — §6
finiteness) of: BB1$_r$ $q$-powers ($p$-independent exponents); BB3$_r$ counts $N_{S_F}(Q_r)$
($p$-independent polynomials in $Q_r = q^{\delta f_1\cdots f_{r-1}}$); strictly-smaller child volumes
($p$-uniform by IH); and the self-loop factor ($p$-uniform). Every ingredient is a uniform rational
function of $q$ with $p$-independent coefficients, and the self-loop pivot $1 - Q^{-(e(e+1)/2-1)}$ is
nonzero at every prime power. Hence $C_e^{(\delta)}(T;q)$ is a single element of $\mathbb Q(q)$, valid at
all $p$. This closes the induction. $\qquad\blacksquare$ (modulo G-A′ and L5fix, both $p$-independent.)

**The crux of the step.** The assembly (4.2) combines exactly two $p$-dependent-*looking* quantities —
child volumes and residual counts — and **both are $p$-independent** (by IH and by BB3$_r$). There is no
fourth ingredient. The wildness of the node (whether $p \mid e$, whether $R_r$ is inseparable) enters
**only** through *which* sub-locus $\{R_r \text{ not squarefree}\}$ is realized in coefficient space (a
different subvariety in different characteristic), and **never** through its count/volume ($Q_r^{d_r-1}$,
§3) or through the child law it feeds. Equivalently: the finite triangular system $(\star)$–$(\star\star)$
over $\mathbb Q(q)$, triangular by strict size-drop with nonzero cyclotomic pivots $1-w(e)$, is solved by
back-substitution (Cramer over $\mathbb Q(q)$, L6M4 Prop 4) into a single $\mathbb Q(t)$ element.

---

## 5. The four subtle wild points, argued explicitly

These are where the proof could fail; each is settled.

**(5.1) Does BB3's universal count survive $p \mid$ ramification / inseparable $R_r$?** YES — the heart,
§3.3. BB3$_r$ is purely over the *finite* field $\mathbb F_r$, blind to slope denominators, wild
ramification, and $p$-adic lifting (which live in the polygon (BB1, lattice-blind) and the splitting field
(which volume ignores)). $\mathbb F_r$ is perfect at *every* order, so "not separable $=$ not squarefree
$=$ discriminant locus," count $Q_r^{d_r-1}$, no inseparable-irreducible exceptions. An inseparable $R_r$
is already non-squarefree; the merge map is bijective on points even when inseparable. Verified directly
over $\mathbb F_4, \mathbb F_8$ (§3.2).

**(5.2) Is $\delta_r = [\mathbb F_r:\mathbb F_q]$ always finite, with $R_r$ over $\mathbb F_r$, even from a
wild parent?** YES — fact (I) / (GMN-Residual): $\mathbb F_r = \mathbb F_{q^{\delta f_1\cdots f_{r-1}}}$,
$[\mathbb F_r:\mathbb F_q] = \delta f_1\cdots f_{r-1} \mid \delta n$, finite and $p$-independently bounded.
The residue tower is built by *residue extensions* (extensions of finite fields, again finite); the
parent's inseparability/wildness lives in the *slopes* and the *$p$-adic lifting*, **not** in the residue
tower. Inseparability of $\psi_{r-1}$ is precisely the *trigger* for forming $\phi_r$ (GMN-Polygon); it
does not break the finite-field-residual property at the next order. [AUDIT-FIX 2026-07-03: corrected
from "GMN constructs $\mathbb F_r$ over an arbitrary complete DVF, so there is no characteristic
obstruction" — GMN works over a fixed finite $K/\mathbb Q_p$ (`gmn_v2.txt:482`); it constructs
$\mathbb F_r$ per fixed $p$, for every $p$, wild ramification included, which is all we use; the
$p$-independence is derived from the uniform combinatorial form of the per-$p$ construction.]
Finite $\Rightarrow$ perfect
$\Rightarrow$ BB3$_r$ applies.

**(5.3) Is the root-merge map's degree $p$-independent at order $r$?** YES. The degree of
$\mathfrak m_\lambda$ is the combinatorial symmetry factor $\prod_m c_m!$ of the multiplicity partition
$\lambda \vdash d_r$ — a combinatorial integer with no reference to $p$; the generic fibre is a single
unordered factor multiset (unique factorization). The image count $N_\lambda(Q_r)$ is a Möbius/necklace
polynomial in $Q_r$ with $p$-independent integer coefficients (§3.2). The branching combinatorics (how many
children, of which sizes and residue degrees) is read off the partition shape, $p$-independent, and the set
of *realizable* shapes is $p$-independent (§6). There is no order $r$ and no characteristic at which the
merge map acquires a higher generic degree — "one double root, rest simple" is a $\operatorname{Spec}
\mathbb Z$-stratum with char-blind generic geometry. So each order-$r$ child-shape volume is the image of a
finite, generically-injective map of $p$-independent degree (the critic's "how to close"). Verified: the
$d=4$ pattern counts are single polynomials across $p \in \{2,3,5,7,11\}$ (§3.2).

**(5.4) Why regime-1 (per-shape), not merely regime-2 (aggregate)?** Because $(\star)$–$(\star\star)$ solve
for the conditional law on the **finest** sub-type simplex — each individual child sub-type $\sigma$ — and
every coefficient feeding it is per-shape ($p$-independent by Proposition 1). The regime-2 fallback
(uniformity only after aggregating over a shape-class) would be needed only if some *individual* per-shape
coefficient were $p$-dependent — which Proposition 1 / BB3$_r$ excludes (BB3$_r$ delivers the *fine* count
$N_\lambda$, not just the total $Q_r^{d_r-1}$). This matters because, as `COMPLETE_PROOF_GAPS §1` notes,
the regime-2 fallback is itself an unproved instance of the same building-block-3 claim one granularity
coarser — *not* a free safety net. Proving regime-1 discharges both. The $n=4$, $n=6$ numerics (§7) confirm
the strong form: each *individual* conditional type probability, not just the aggregate, is a single
rational function of $q$ across all primes.

---

## 6. Termination: the induction is finite, $p$-independently (L5fix)

The induction is well-founded because the OM descent terminates in finitely many orders, bounded
$p$-independently. From `L5fix_complete.md`:

- **Strict size descent off the self-loop** (§4.1): every non-self-loop step replaces a size-$e$ cluster by
  children of sizes $< e$ summing to $\le e$; the root budget $m \le n$ strictly drops. The tree has
  $\le n$ leaves and $\le n-1$ branch levels ($p$-independent).
- **Self-loops are resummed, not counted** $(\star\star)$: a maximal self-loop chain at size $e$ has length
  $\le D_0 = \tfrac12 v(\operatorname{disc})$, finite per separable point but unbounded over the space — so
  it is summed geometrically (§4.1), never treated as depth.
- **Ramifying-level depth bounded $p$-independently** by the leaf different exponent. By **Serre, *Local
  Fields* III.6 Prop. 13** (totally ramified separable degree-$e$: $e-1 \le d(\mathfrak D) \le e-1 +
  v_L(e)$, wild excess $v_L(e) = e\,v_p(e)$) plus **tower multiplicativity** (III §4 Prop. 8) and the
  trivial different of the unramified subextension, a leaf $L/K$ of **degree $d = e^\ast f^\ast \le n$** has
  $$
  d_{L/K} \le (d-1) + d\,v_p(d), \qquad
  B(n,p) = \max_{d \le n}\big[(d-1) + d\,v_p(d)\big] \le (n-1) + n\log_2 n,
  $$
  the **corrected per-leaf-degree bound**. (The older $(n-1)+n\,v_p(n)$ is the irreducible-leaf special
  case $ef=n$ and is *non-monotone in $d$*, hence too small for proper leaves of degree $d<n$; e.g.
  $x^3-3/\mathbb Q_3$ has a degree-3 leaf with $d_{L/K} = 5 > B(3,4) = 3$, and $x^4-2/\mathbb Q_2$ has
  $d_{L/K} = 11$. Finiteness and $p$-independence — all the induction needs — survive; only the explicit
  constant changes.)
- **Defectlessness** (Ostrowski; Serre *Local Fields* II.3 Cor. to Prop. 10; Neukirch *ANT* II.8.5):
  $K/\mathbb Q_p$ is complete discretely valued, hence defectless, so every separable leaf has $\sum e_i
  f_i = [L:K]$ with all defects 1; thus $\prod f_i \mid n$, $e_i \le n$, reached in finitely many orders.
  (Contrast char $p$, where Artin–Schreier defect towers exist; mixed char $0$ is immune — this is *why*
  $\delta_r$ in §5.2 is finite and the depth is controlled by the different, not by a runaway defect.)

Hence slopes ($b \le e \le n$), residue degrees ($\prod f_i \mid n$), residual shapes (partitions of
$d \le n$), and depth ($\le B(n,p) + (n-1)$) are all bounded by $p$-independent quantities, so the menu
$\mathcal T_n$ of reachable shapes is a **finite set, the same for every $p$**. *The characteristic enters
only through which coefficient cell maps to which shape, never through the menu.* The triangular system
$(\star)$–$(\star\star)$ has a finite, $p$-independent state space; back-substitution terminates in
$\le |\mathcal T_n|$ steps. $\qquad\square$

(Reduced to citation here: the GMN per-augmentation different monotonicity — "each ramifying OM level
raises the different exponent by $\ge 1$," GMN §3–4 — gates only the explicit depth *constant*; the
*finiteness and $p$-independence* the induction consumes follow from the cruder $\le n$ leaves / $\le n-1$
branch levels alone.)

---

## 7. Consistency checks (mandatory) — DERIVED predictions vs the trusted oracle

The general formula (4.2) MUST reproduce the verified instances. It does, as **zero-free-parameter derived
predictions** (not fits). Verification: `notes/bb3inf_verify.py` (system python3, reading the trusted
PARI-oracle JSONs in `results/`) and the BB3 finite-field scripts of §3.2.

### 7.1 Size-2 and size-3 cluster laws (the building bricks)

The size-$e$ single-cluster law is $L_e = \beta(e;q) = \alpha(e;q^{-1})$ (the M1 reciprocal read; verified
to sum to 1, `notes/bb3inf_verify.py [1]`):
$$
L_2:\quad \text{ram } \tfrac{q}{q+1},\quad \text{inert } \tfrac{1}{2(q+1)},\quad \text{split }
\tfrac{1}{2(q+1)};
$$
$$
L_3:\quad
\underbrace{\tfrac{q^2(q-1)(q^2+1)}{q^5-1}}_{\text{1c}},\
\underbrace{\tfrac{q(q-1)(q^3+q^2+1)}{(q+1)(q^5-1)}}_{\text{1r1}},\
\underbrace{\tfrac{q^2-1}{3(q^5-1)}}_{\text{3}},\
\underbrace{\tfrac{q^3-1}{2(q+1)(q^5-1)}}_{\text{12}},\
\underbrace{\tfrac{(q-1)(q^2-q+1)}{6(q+1)(q^5-1)}}_{\text{111}},
$$
each with the size-3 self-loop denominator $q^5-1 = (q-1)\Phi$, summing to $1$ (sympy-verified). **Note
$L_3.\text{1c} = q^2(q-1)(q^2+1)/(q^5-1)$ is the *projective/reciprocal* read $\beta(3)$, NOT the monic
$\alpha(3).\text{1c} = (q-1)(q^2+1)/(q^5-1)$** — this distinction is load-bearing in §7.2.

### 7.2 The $n=6$ deep-wild stratum (OM order $\ge 3$; the genuinely un-resummed wild branch)

This is the regime G-A flagged as untested and which BB3-$\infty$ must predict. Monic degree-6 $f$, single
slope $1/2$ ($b=2$, $\ell=6$, $d=3$), order-1 residual $R_1 = (y-\rho)^3$ a perfect cube — a **size-3
inseparable child** of an inseparable node, $p=2$ Artin–Schreier included. By (4.2) the three merged
residual atoms (each a forced $(2,1)$ slope-$1/2$ ramified block) resolve one order deeper by the size-3
cluster law $L_3 = \beta(3;q)$, the outer slope-$1/2$ a uniform ramification-doubling spectator
($e \mapsto 2e$):
$$
L_3.\text{1c}\to(6,1),\quad L_3.\text{1r1}\to(2,1)(4,1),\quad L_3.3\to(2,3),\quad
L_3.\text{12}\to(2,1)(2,2),\quad L_3.\text{111}\to(2,1)^3.
$$
**Trusted PARI oracle** (`run_n6_wild.py`/`analyze_n6.py`, $N = 80\text{k}$/prime, four seeds, oracle
$(e,f)$-classified, $p \in \{2,3,5,7,11,13\}$), DERIVED prediction vs observed (this run,
`notes/bb3inf_verify.py`):

| type $\to L_3$ class | $p{=}2$ pred/obs | 3 | 5 | 7 | 11 | 13 |
|---|---|---|---|---|---|---|
| $(6,1)\to$1c | .6452/.6475 | .7438/.7460 | .8323/.8326 | .8747/.8733 | .9166/.9170 | .9285/.9281 |
| $(2,1)(4,1)\to$1r1 | .2796/.2768 | .2293/.2270 | .1611/.1607 | .1228/.1240 | .0827/.0824 | .0710/.0716 |
| $(2,3)\to$3 | .0323/.0323 | .0110/.0112 | .0026/.0027 | .0010/.0011 | .0002/.0002 | .0002/.0001 |
| $(2,1)(2,2)\to$12 | .0376/.0380 | .0134/.0133 | .0033/.0033 | .0013/.0012 | .0003/.0003 | .0002/.0001 |
| $(2,1)^3\to$111 | .0054/.0053 | .0024/.0025 | .0007/.0006 | .0003/.0004 | .0001/.0001 | .0001/.0000 |

**MAX $|z| = 3.16$**, and that single $3.16$ is on the rarest type $(2,3)$ at $q=13$ with only **5**
observed events (predicted $\approx 1.3$ in 80k — pure small-count Poisson noise); every well-populated
cell has $|z| < 1.8$. **Regime-1 persists through the un-resummed order-$\ge 3$ wild branch, and the wild
$p=2$ Artin–Schreier deep node lands exactly on the same rational curve as the tame odd primes**, with zero
free parameters.

**Decisive reconciliation point.** $(6,1)$ is the *derived* $L_3.\text{1c} = q^2(q-1)(q^2+1)/(q^5-1)$,
**not** the naive $q/(q+1)$. They agree to $O(1/q)$ but differ at $p=2$ by $0.0215$ ($0.6452$ vs $0.6667$):
the observed $0.6475$ matches the derived form ($z = +1.41$) and rejects $q/(q+1)$ ($z \approx +11$). The
recursion predicts the **correct** rational function, not merely *a* uniform one. (Attempt 1 loosely wrote
$(6,1) \sim q/(q+1)$; this merge adopts the derived $\beta(3)$ form, which the data demands.) A fresh
out-of-sample run (seed 999, $N = 6\text{k}$/prime, $p \in \{2,3,5,7\}$) reproduces the fractions (p=2
$(6,1) = 0.6470$ vs $0.6475$), so the agreement is not an interpolation artifact.

### 7.3 The $n=4$ first wild atom (OM order 2; must reproduce)

Condition on a clean slope-$1/2$ size-4 cluster. **Order 1** ($b=2$, $d_1=2$): the residual $R_1 = y^2 +
\bar b y + \bar a$ ranges over $\bar a \in \mathbb F_q^\ast$, $\bar b \in \mathbb F_q$. BB3$_1$:
$P(\text{insep}) = (q-1)/((q-1)q) = 1/q$, $P(\text{split}) = (q-2)/2q$, $P((2,2)) = 1/2$ — verified at all
$p \in \{2,3,5,7,11,13\}$ including the Artin–Schreier $p=2$ (inseparable locus $\{\bar b = 0\}$, a
punctured line vs the odd-$p$ parabola $\{\bar b^2 = 4\bar a\}$ — geometrically different, **identical count
$1/q$**; at $q=2$, $P(\text{insep}) = 1/2 = 1/q$ exactly). **Order 2** (the inseparable piece $R_1 =
(y-\rho)^2$): the GMN order-2 key polynomial $\phi_2$ gives a size-2 cluster law $L_2$ over $\mathbb F_q$
($f_1=1$), with the outer slope doubling $e \mapsto 2e$:
$$
P((4,1)\mid\text{insep}) = L_2.\text{ram} = \tfrac{q}{q+1},\qquad
P((2,2)\mid\text{insep}) = P(\text{split}\mid\text{insep}) = L_2.\text{inert} = \tfrac{1}{2(q+1)}.
$$
**Trusted oracle** (`results/n4wild_insep_*`, $N = 80\text{k}$/prime, $p \in \{2,3,5,7,11,13\}$): $P((4,1)
\mid\text{insep}) = 0.6664, 0.7515, 0.8329, 0.8756, 0.9147, 0.9289$ vs $q/(q+1) = 0.6667, 0.75, 0.8333,
0.875, 0.9167, 0.9286$; $P((2,2)\mid\text{insep}) = 0.1675, 0.1240, 0.0831, 0.0619, 0.0429, 0.0350$ vs
$1/(2(q+1)) = 0.1667, \dots, 0.0357$. **Worst $|z| = 1.94$.** Assembled: $P((4,1)) = 1/(q+1)$, $P((2,2)) =
\tfrac12 + \tfrac1{2q(q+1)}$, $P(\text{split}) = \tfrac{q-2}{2q} + \tfrac1{2q(q+1)}$, summing to 1.

### 7.4 Fresh independent test (generated to probe §5.3): $n=6$, slope-$1/3$, residual $(y-\rho)^2$

A genuinely new stratum (`run_n6_slope13.py`), constructed for this proof, exercising **both** flavours of
wildness independently: monic degree-6, single slope $1/3$ (**wild at $p=3$** since $3 \mid b=3$; $d =
\ell/b = 2$), residual $(y-\rho)^2$ (a **size-2 inseparable child**; at $p=2$ the $(y-\rho)^2$ is
Artin–Schreier inseparable). The proof predicts the size-2 cluster law $L_2$ with outer slope tripling
$e \mapsto 3e$: $(2,1)\text{ram}\to(6,1) = q/(q+1)$; $(1,2)\to(3,2) = 1/(2(q+1))$; split $\to(3,1)^2 =
1/(2(q+1))$. **Trusted oracle** ($N = 20\text{k}$/prime, four seeds, $p \in \{2,3,5,7,11,13\}$; this
analysis, `/workspace-vast/asving/tmp/n6s13_check.py`): only the three predicted types occur;
$P((6,1)) = q/(q+1)$ gives $0.6690, 0.7477, 0.8320, 0.8778, 0.9134, 0.9265$ vs $0.6667, \dots, 0.9286$.
**Worst $|z| = 1.74$.** This independently confirms §5.3: the outer wild slope ($p=3$) is a uniform
ramification multiplier ($\times 3$) and the size-2 inseparable child ($p=2$ A-S) is the tame $L_2$ law,
regardless of characteristic. (A further fresh stratum `run_n6_mixed.py`, residual $(y-\rho)^2(y-\sigma)$,
confirms the L1 tensor structure: a size-2 inseparable child $\times$ a spectator simple leaf $=$ the $n=4$
atom tensored with $(2,1)$, $p \in \{3,5,7,11,13\}$.)

### 7.5 Eisenstein leaf and the $n=5$ embedding

A slope-$1/e$ Eisenstein face with linear residual ($d=1$) is a base-case leaf: totally ramified $(e,1)$
with probability 1, volume $(q-1)/q^{e+1}$ at every $p$ including wild $p \mid e$ (BB1, verified at
$p \in \{2,3,5\}$ for $e=4$). The $n=5$ embedding (simple root $\times$ slope-$1/2$ quartic cluster)
confirms via L1 coprime-independence that the wild atom embeds unchanged into higher $n$ (oracle $p=2,3$,
$|z| < 1.7$) — the mechanism is not an $n=4$ accident.

---

## 8. Honest ledger: derived vs reduced-to-citation vs residual gaps

### Derived here (from BB1/L4 + BB3/L3 + the recursion, no external uniformity black box)
- **BB3$_r$ at every order** (§3): "needs descent $=$ non-squarefree $=$ discriminant locus $\Delta_{d_r}$,"
  the image of a root-merge map of $p$-independent degree, with the universal $\mathbb F_r$-point count
  $Q_r^{d_r-1}$ in every characteristic and **no inseparable-irreducible exceptions at any order over any
  finite higher-order residue field** (finite fields perfect at every $r$); fine shape counts
  $N_\lambda(Q_r)$ as single $\mathbb Z[Q_r]$-polynomials. The Frobenius-bijective-on-points mechanism made
  explicit and order-blind. Verified exhaustively over $\mathbb F_2,\mathbb F_3,\mathbb F_5,\mathbb F_7$ and
  the prime-power $\mathbb F_4,\mathbb F_8,\mathbb F_9,\mathbb F_{25}$.
- **BB1$_r$ at every order** (§2): cell volume $(1-Q^{-1})^V Q^{-A}$, $V,A$ lattice data, $p$-independent.
- **Proposition 1** and **the induction** (§4): the order-$r$ transition system $(\star)$ has every
  coefficient a char-independent $\mathbb Q(q)$ element; back-substitution to a single $R \in \mathbb Q(t)$.
- **The four subtle wild points** (§5), each argued explicitly.
- **The consistency predictions** (§7): $L_2 = \beta(2;q)$ ($n=4$ atom, $q/(q+1)$), $L_3 = \beta(3;q)$
  ($n=6$ deep-wild, $q^2(q-1)(q^2+1)/(q^5-1)$ etc.), and the fresh $n=6$ slope-$1/3$ stratum, all matched to
  the trusted oracle at all $p$ incl. wild $p=2,3$, **zero free parameters**.

### Reduced to standard citation ($p$-independent, no wild difficulty introduced)
- **G-A′ (THE single external import): the GMN order-$r$ OM machinery (§1).** Existence and behaviour of
  the higher key polynomials $\phi_r$ — repeated order-$(r-1)$ residual factor resolved by an order-$r$ key
  polynomial whose Newton polygon is a lattice object and whose residual polynomial lies over the finite
  order-$r$ residue field, with the "Theorem of the Polygon" / "Theorem of the Residual Polynomial" at
  every order and the multiplicity-1$=$leaf / multiplicity-$\ge 2$$=$descend dichotomy. Guàrdia–Montes–Nart,
  Trans. AMS **364** (2012), 361–416 (arXiv:0807.2620). [AUDIT-FIX 2026-07-03: citation numbers corrected
  to the verified pins of `GMN_citations.md` — order 1: Thm 1.15 / 1.19; order $r$: Thm 3.1 / 3.7;
  residual polynomial Def 2.21; key polynomial Thm 2.11 / Def 2.12; leaf dichotomy Cor 1.20 / 3.8; descent
  trigger Lemma 3.11(3); termination Thm 4.18 / Cor 4.19; and Thm 2.26 = Theorem of the *product* in
  order $r$ (it exists, pace an earlier note, and feeds the GAP-1 restart route). The list previously
  printed here, "§2.2–2.4 (Def. 2.5, Thm. 2.11, Def. 2.20–2.23, Thm. 2.26) and §3–4 (index/different
  growth, factorization theorem)", was the pre-correction guess.] Used only via facts (I)–(III); the
  *uniformity consequence* is derived, not imported. [AUDIT-FIX 2026-07-03: scope corrected from
  "$p$-independent (GMN holds over arbitrary complete DVFs, insensitive to $p \mid e_i$; the inseparable
  case is generic)" — GMN fixes a finite $K/\mathbb Q_p$ (`gmn_v2.txt:482`) and works per fixed $p$; wild
  ramification $p \mid e_i$ is inside that per-$p$ scope, and the $p$-independence is derived from the
  uniform combinatorial form of the per-$p$ imports.] *Caveat:* the structural facts (I)–(III)
  are unambiguous and confirmed from the paper's own statements, but the exact published TAMS theorem
  *numbers* should be confirmed against the printed pagination/numdam companion (JTNB 23 (2011), 667–696)
  before final submission — the standard references are as cited.
- **M6 (residual equidistribution):** the order-$r$ residual-coefficient map is a submersion onto
  $\mathbb A^{d_r}(\mathbb F_r)$ (so $R_r$ is Haar-equidistributed over monic degree-$d_r$ polynomials). At
  order 1 this is BB1 itself (verified exactly). At order $r$ it is the order-$r$ analogue, derived from
  BB1$_r$ + GMN's order-$r$ Newton-polygon coordinates; validated numerically at the wild node (§7).
  Severity: minor — the order-$r$ form of a fully-verified order-1 fact.
- **L5fix depth/defect (§6):** Serre *Local Fields* III.6 Prop. 13 (wild-excess different) + III §4 Prop. 8
  (towers); Serre II.3 / Neukirch *ANT* II.8.5 + Ostrowski (defectlessness). The per-leaf-degree bound
  $(d-1)+d\,v_p(d)$ is proved; only the GMN per-augmentation monotonicity (which gates the explicit depth
  *constant*, not finiteness) is cited.
- **L1/R1:** Hensel coprime splitting with exact unit-resultant product measure (Igusa, *Local Zeta
  Functions* §7.4); the $\delta>1$ Frobenius descent $L_e^{(\delta)}(q) = L_e^{(1)}(q^\delta)$ over
  unramified $K_\delta$ (paper's `lemma: local integrals`); the Vandermonde pushforward giving the
  self-similar $I_e$ self-loop. All $p$-independent.

### Residual gaps (honest)
- **[AUDIT-FIX 2026-07-03 — OPEN LEMMA, BLOCKING for general $n$] GAP-1: the descend-restart Haar
  identification** (§4.2 banner). The identification of the conditional law of a descend child with the
  standalone cluster law over $K_{\delta f}$ (path-independence, spectator slope, inherited self-loop
  ratio) is unproved and has no citation — GMN contains no measure-theoretic statements; the Lean layer
  axiomatizes it as `AX_cellRecursion` (GENUINE-GAP). Proof in progress: `notes/RESTART_LEMMA.md`.
  Empirically unfalsified through OM order 5 (`WILD_UNIFORMITY_VERDICT.md`).
- **[AUDIT-FIX 2026-07-03 — OPEN LEMMA, BLOCKING for general $n$] GAP-2: M6$_r$/BB1$_r$, the order-$r$
  count$\to$volume bridge.** Order-$r$ residual equidistribution with equal-mass fibres and joint
  independence of the on-side $\mathbb F_r$-digits under the accumulated order-$<r$ conditioning: proved
  at order 1 ($=$L4); at $r \ge 2$ only the `M6_lemma.md §2` sketch. The surjectivity half is GMN
  Prop 2.10 (corrected pin — see NEW-A in `WILD_UNIFORMITY_VERDICT.md`); the equidistribution half has
  no GMN counterpart.
- **[reduced-to-citation, combinatorial half only] G-A′** is the one genuine external *citation*
  dependency [AUDIT-FIX 2026-07-03: previously "the one genuine external dependency. BB3-$\infty$ is
  *complete modulo the GMN higher-order machinery*" — overstated; the genuine *proof* gaps are GAP-1 and
  GAP-2 above, which GMN does not supply]. The GMN machinery is applied per $p$ and does not touch the
  wild difficulty (the wild difficulty is entirely in *which cell maps to which shape*, handled by BB3's
  char-independent counts). A referee verifies GMN directly; to remove the import one would re-derive the
  higher key-polynomial construction over $\mathcal O_K$ from MacLane–Okutsu–Montes valuations — standard
  but lengthy, introducing no wild-prime difficulty.
- **[minor] explicit $A(\Pi)$ at arbitrary order** (§2): BB1's content (char-independent $q$-power) is
  established; the explicit lattice-point exponent is written only $e \le 4$. Does not affect uniformity.
- **[minor, empirical depth — now extended to OM order 4]** oracle confirmation reaches OM order 4.
  Order $\ge 3$ / $n=6$: size-3 inseparable child (§7.2); size-2 child + simple leaf; size-2 child under
  a wild outer slope (§7.4). **Order 4 / $n=8$ (this proof, `run_n8_wild.py` + `run_cluster_law.py`,
  `results/n8wild_*.json`, `results/clusterlaw_e4_*.json`, `notes/n8_order4_adversarial.md`):** monic
  degree-8, slope $1/2$, order-1 residual $(y-\rho)^4$ — a **size-4 inseparable child**, *doubly wild at
  $p=2$* ($4=2^2$ AND slope $1/2$ wild). Zero-free-parameter test: the deg-8 type distribution equals the
  directly-measured size-4 cluster law $L_4$ with the outer slope $e\mapsto 2e$ doubling, two independent
  samplers agreeing, **max $|z|\sim 3.2$ on well-populated types** (the $>2$ values rare-cell Poisson
  noise; the dominant $(8,1)$ and $(2,1)(6,1)$ cells $|z|<2.3$ at every prime), the doubly-wild $p=2$
  deep node on the same structural rational function as the odd primes. This closes the previously
  order-$\ge 4$-untested regime empirically. Genuinely arbitrarily-deep order ($\ge 5$: a size-4
  inseparable child with its own deeper inseparable sub-child) remains covered by the induction + GMN,
  not by oracle; the induction predicts regime-1 there and the consistency claim rests on the *derived*
  zero-free-parameter cluster laws $\beta(2),\beta(3),\beta(4)$, not on a fit.
- **[write-up propagation — DONE, AUDIT-FIX 2026-07-03]** the per-leaf-degree bound correction of §6 is
  propagated: `L5fix_complete.md` and `L6M4_complete.md` already printed the corrected
  $\max_{d\le n}[(d-1)+d\,v_p(d)]$ (the 2026-07-03 audit verified only `L2core_complete.md:213` was still
  stale, and it is now fixed). Conclusion (finite $p$-independent menu) was never at risk; only the
  printed constant was wrong. Originally flagged in `COMPLETE_PROOF_GAPS §2`.

### Net
[AUDIT-FIX 2026-07-03 — honest reframing; this paragraph previously claimed a proof "by induction on
Montes order ... modulo the GMN citation" making the Goal Theorem "complete modulo standard
$p$-independent citations".] BB3-$\infty$ ($=$ L2core regime-1 at all OM orders, all primes incl. wild)
is **proved for $n \le 4$** (closed forms $n \le 3$ plus the fully derived order-1/order-2 machinery);
for **general $n$** the induction on Montes order is **complete modulo TWO OPEN LEMMAS** — **GAP-1**
(the §4.2 descend-restart Haar identification; banner there, proof in progress in
`notes/RESTART_LEMMA.md`) and **GAP-2** (the order-$r$ equidistribution/count$\to$volume bridge
M6$_r$/BB1$_r$) — neither of which reduces to a citation. The inductive step otherwise rests on BB1
(lattice $q$-power, $p$-independent) and BB3
(finite-field discriminant locus / root-merge map of $p$-independent degree, universal count $Q_r^{d_r-1}$
in every characteristic via Frobenius-bijective-on-points), the induction made finite by L5fix's
$p$-independent shape menu. The single external *citation* is the GMN order-$r$ OM machinery
(existence/behaviour
of higher residuals over finite fields), flagged G-A′, applied per $p$ with the $p$-independence
derived. The derived predictions reproduce
the $n=4$ order-2 atom ($q/(q+1)$) and the $n=6$ order-$\ge 3$ deep-wild stratum ($\beta(3;q)$, with $(6,1)$
the derived $q^2(q-1)(q^2+1)/(q^5-1)$ that the data prefers at $\sim 11\sigma$ over the naive $q/(q+1)$)
against the trusted oracle at all primes including the wild $p=2$ Artin–Schreier deep node — the first place
the order-$\ge 3$ wild branch appears, now confirmed empirically and matched to a zero-free-parameter
derived rational function; the mechanism is oracle-confirmed through **OM order 5** with no
counterexample (`WILD_UNIFORMITY_VERDICT.md`). Combined with the rest of the chain
$L1\to\{L3,L4\}\to R1\to \text{L2core}[=\text{BB3-}\infty]\to
\text{L5fix}\to \text{L6M4}\to M1\to L7$: the Goal Theorem is **proved for $n \le 4$; for general $n$
complete modulo the two open lemmas GAP-1 and GAP-2** (mechanism oracle-confirmed through OM order 5, no
counterexample) — see `WILD_UNIFORMITY_VERDICT.md`.

The wild degeneration that broke Prop 5.3 (a tangent-space statement) is invisible to these volumes (a
point-count statement) at every depth — the same fact read on two functors, all the way up the OM tower.
$\blacksquare$
