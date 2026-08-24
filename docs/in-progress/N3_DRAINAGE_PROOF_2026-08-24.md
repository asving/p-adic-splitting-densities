# The cubic drainage block: HYP.04--HYP.09

**Date:** 2026-08-24  
**Status:** complete proof.  Every item HYP.04--HYP.09 used below is marked **PROVED**.  No
mathematical gap remains in the drainage argument.

## 1. Result, including the correction to HYP.08

Let (O) be a complete discrete valuation ring, (pi) a uniformizer, (mathfrak m=(pi)),
(k=O/\mathfrak m), and (q=\#k).  Thus (q\ge 2).  This includes (O=\mathbb Z_p) for every
prime (p), and the proof never divides by (2) or (3).  In particular it includes the wild
residue characteristics (2) and (3).

For (N\ge0), put

\[
 A_N=(O/\mathfrak m^N)^3,
 \qquad \#A_N=q^{3N}.
\]

A class (c\in A_N) is *decided* if there is a factorization type \(\sigma\) such that every
integral lift (a=(a_0,a_1,a_2)) of (c) gives the same type \(\sigma\) for

\[
 F_a(X)=X^3+a_2X^2+a_1X+a_0.
\]

Let (U_N\subseteq A_N) be the set of classes which are not decided, and define

\[
 C_N=\#U_N,\qquad u_N=\frac{C_N}{q^{3N}}.
\]

The exact recurrence proved here is

\[
 \boxed{\quad u_N\le q^{-N}+q^{-5}u_{N-3}\quad(N\ge3).\quad}                 \tag{1}
\]

Equivalently, before normalization,

\[
 \boxed{\quad C_{M+3}\le q^{2(M+3)}+q^4C_M\quad(M\ge0).\quad}              \tag{2}
\]

This is **stronger than the ledger display**

\[
 u_N\le q^{-N/2}+q^{-5}u_{N-3}.
\]

For even (N=2r), the displayed ledger term is literally (q^{-r}), and (1) implies it because
(q^{-2r}\le q^{-r}).  For arbitrary integral (N), the corpus should avoid the ambiguous
integer notation (q^{-N/2}); (1) is the precise level-by-level statement.  The constants in
(1) are derived below: (q^{-N}) comes from the simple-root/peel branch, and (q^{-5}) from the
mixed-precision triple-root extraction.  The earlier uniform-precision extraction gives only
(q^{-2}), not (q^{-5}).

Iterating (1), with (r=\lfloor N/3\rfloor), gives

\[
 u_N\le q^{-N}\sum_{j=0}^{r-1}q^{-2j}+q^{-5r}u_{N-3r}
 \le \frac{q^{-N}}{1-q^{-2}}+q^{-5\lfloor N/3\rfloor}.                    \tag{3}
\]

Since (0\le u_j\le1), the right side tends to zero.  Hence (u_N\to0).  Section 9 converts
this counting statement into the required Haar-null and `UndecidedVanishes` statements.

## 2. Counting normalization and Haar measure

Give (O) its normalized additive Haar probability measure and (O^3) the product measure
(\mu).  Every coset of \(\mathfrak m^N\) in (O) has measure (q^{-N}): the (q^N) cosets
partition (O), translations preserve measure, and their measures are equal.  Consequently
every coefficient cylinder above a point of (A_N) has measure (q^{-3N}).  Therefore, for
every (S\subseteq A_N),

\[
 \mu(\operatorname{pr}_N^{-1}(S))=\frac{\#S}{q^{3N}}.                    \tag{4}
\]

This is exactly the normalization in `Coeff O 3 N`, `card_coeff`, and `undecidedSeq`: no
additional factor of (q), no choice of a root centre, and no per-centre normalization occurs.

The same discussion works for any complete DVR with finite residue field.  In the requested
(O=\mathbb Z_p) case, (q=p).

## 3. Four input lemmas: HYP.04--HYP.07

### 3.1 HYP.04: strong Hensel -- **PROVED**

We use the normalized valuation (v(\pi)=1), with (v(0)=\infty).

**Lemma 3.1 (strong Hensel).**  Let (F\in O[X]), (x_0\in O), and suppose

\[
 v(F'(x_0))=w<\infty,\qquad v(F(x_0))=k>2w.
\]

Then (F) has a root (r\in O) satisfying

\[
 v(r-x_0)\ge k-w>w.
\]

No monicity or residue-characteristic hypothesis is needed.

**Proof.**  We give the Newton proof because the exact surplus is used in case L below.  More
generally, suppose at a point (x) that

\[
 F'(x)=\pi^w u,\quad u\in O^\times,\qquad F(x)=\pi^{2w+j}a,\quad j\ge1.
\]

Set

\[
 h=-\pi^{w+j}au^{-1},\qquad y=x+h.
\]

Then (F'(x)h=-F(x)).  Taylor expansion in (O[X]) gives elements (G,H\in O) such that

\[
 F(y)=F(x)+F'(x)h+h^2G=h^2G,
\]

and

\[
 F'(y)=F'(x)+hH
       =\pi^w\bigl(u+\pi^j(-au^{-1}H)\bigr).
\]

The expression in parentheses is a unit, since it is a unit plus an element of \(\mathfrak m\).
Thus (v(F'(y))=w), (v(y-x)\ge w+j), and (v(F(y))\ge2w+2j).  One Newton step therefore
doubles the positive surplus (j) while leaving (w) fixed.

Start with (j_0=k-2w\ge1) and iterate.  At the (n)-th step the surplus is at least
(2^nj_0), and

\[
 v(x_{n+1}-x_n)\ge w+2^nj_0\longrightarrow\infty.
\]

Hence ((x_n)) is Cauchy and converges, by completeness, to some (r\in O).  Polynomial
evaluation is continuous, while (v(F(x_n))\to\infty), so (F(r)=0).  Every displacement after
the first lies in \(\mathfrak m^{k-w}\), as does the first displacement; hence
(v(r-x_0)\ge k-w>w).  This proves the claim. \(\square\)

This proves the ledger statement and slightly strengthens it: the landed theorem also gives
uniqueness among roots satisfying (v(r-x_0)>w), but uniqueness is not needed for drainage.
If \(F(x_0)=0\), the ledger statement is immediate with \(r=x_0\); the iteration above covers
the nonzero-value case, where \(k=v(F(x_0))\) is finite.

### 3.2 HYP.05: integral translation invariance -- **PROVED**

For (c\in O), the map

\[
 T_c:O[X]\longrightarrow O[X],\qquad P(X)\longmapsto P(X+c)
\]

is an (O)-algebra automorphism with inverse (T_{-c}).  It preserves monicity, degree, products,
and irreducibility, so it bijects the monic irreducible factors of (F) with those of
(F(X+c)).  If \(\alpha\) is a root of a factor of (F), then \(\alpha-c\) is a root of the
corresponding translated factor and

\[
 K(\alpha)=K(\alpha-c),\qquad K=\operatorname{Frac}(O).
\]

Thus the ramification index and residue degree of every corresponding factor agree.  The
multiset of ((e,f))-pairs, hence `typeOf`, is unchanged.  This also matches the corpus's
norm-gcd definition directly: the root algebras of corresponding factors are \(O\)-algebra
isomorphic under \(\alpha\leftrightarrow\alpha-c\), so their algebra norms and therefore their
sets of norm valuations have exactly the same gcd.  Translation is also an invertible polynomial
map on coefficient vectors and preserves congruence modulo every \(\mathfrak m^N\).

### 3.3 HYP.06: scale invariance and the lost digits -- **PROVED**

Suppose (F,G\in O[X]), (G) is monic of degree (n), and

\[
 F(\pi^mY)=\pi^{mn}G(Y).                                                   \tag{5}
\]

The roots correspond by \(\alpha=\pi^m\beta\).  Since \(\pi^m\in K^\times\),
(K(\alpha)=K(\beta)); corresponding irreducible factors therefore have the same (e) and
(f).  Here is the extra argument needed to verify this against the corpus's order-based
norm-gcd definition rather than merely the classical field invariant.  For a corresponding
degree-\(d\) irreducible factor, set

\[
 A=O[\alpha]\subseteq B=O[\beta],\qquad \alpha=\pi^m\beta.
\]

The inclusion preserves the field norm, so the set of nonzero norm valuations from \(A\) is a
subset of the one from \(B\).  Conversely,

\[
 \pi^{m(d-1)}B\subseteq A:
\]

indeed, for \(0\le i<d\),
\(\pi^{m(d-1)}\beta^i=\pi^{m(d-1-i)}\alpha^i\in A\).  If \(D_A\) is the gcd of the nonzero norm
valuations from \(A\), then \(D_A\) divides both

\[
 v_K\!\left(N_{L/K}(\pi^{m(d-1)}y)\right)
   =m d(d-1)+v_K(N_{L/K}(y))
\]

and \(m d(d-1)\), the norm valuation of the scalar \(\pi^{m(d-1)}\in A\).  Hence \(D_A\) divides
every norm valuation from \(B\).  Together with the first inclusion this gives \(D_A=D_B\).
Thus the corpus's residue-degree value, and then \(e=d/f\), is unchanged on every factor.
Consequently `typeOf F = typeOf G`.

For the cubic extraction used later,

\[
 B(X)=X^3+B_2X^2+B_1X+B_0,\qquad
 (B_0,B_1,B_2)=(\pi^3d_0,\pi^2d_1,\pi d_2),                              \tag{6}
\]

and (B(\pi Y)=\pi^3F_d(Y)).  If (B'\equiv B\pmod{\pi^{M+3}}) and (d') is its extraction,
cancellation in the domain (O) gives

\[
 d'_0\equiv d_0\pmod{\pi^M},\quad
 d'_1\equiv d_1\pmod{\pi^{M+1}},\quad
 d'_2\equiv d_2\pmod{\pi^{M+2}}.                                       \tag{7}
\]

Thus the extracted class is certainly determined modulo \(\pi^M\).  Formula (7), rather than
scale invariance alone, is the level bookkeeping needed by HYP.08.

### 3.4 HYP.07: the nonintegral-slope totally ramified leaves -- **PROVED**

After recentering a triple residual root, the two nonintegral single-side leaves needed by the
recursion are the following.

**Case E.**  If

\[
 v(B_0)=1,\qquad v(B_1),v(B_2)\ge1,
\]

then (B) is Eisenstein.  It is irreducible of degree (3), has residue degree (1), and has
type \(\{(3,1)\}\).

**Case R.**  If

\[
 v(B_0)=2,\qquad v(B_1)\ge2,qquad v(B_2)\ge1,                            \tag{8}
\]

then (B) also has type \(\{(3,1)\}\).

To prove case R, first suppose (B(r)=0) for (r\in O).  Reducing the equality

\[
 r^3=-(B_2r^2+B_1r+B_0)
\]

modulo \(\pi\) shows \(\pi\mid r^3\), hence \(\pi\mid r\).  Every term other than (B_0) in
(B(r)=0) is then divisible by \(\pi^3\), forcing \(\pi^3\mid B_0\), contrary to (8).  Thus
(B) has no root in (O).  A reducible monic cubic over (K) has a root in (K); that root is
integral over (O), hence lies in the integrally closed DVR (O).  Therefore (B) is
irreducible.

Let \(\theta\) be a root and (L=K(\theta)).  The norm of \(\theta\) is \(-B_0\), so
(v_K(N_{L/K}\theta)=2).  The norm of the scalar \(\pi\) is \(\pi^3\), of valuation (3).
For a finite extension with residue degree (f), every norm valuation is divisible by (f).
Hence (f\mid2) and (f\mid3), so (f=1).  Since (ef=[L:K]=3), (e=3), proving the stated
type.  This argument is characteristic-free.

These are precisely the nonintegral-slope leaves used below.  A former prose claim that
"constant valuation not divisible by (3) implies total ramification" without a condition on
(B_1) was false: (v(B_0)=2, v(B_1)=1) is the two-side case L below and has type
\(\{(1,1),(2,1)\}\), not \(\{(3,1)\}\).

To see that E and R cover the full *single-side* nonintegral-slope assertion of HYP.07, let the
constant-term valuation be \(t=3m+r\), with \(r\in\{1,2\}\).  A single Newton side from
\((0,t)\) to \((3,0)\) says

\[
 v(B_1)\ge\lceil2t/3\rceil,\qquad v(B_2)\ge\lceil t/3\rceil.
\]

After extracting \(X=\pi^mY\), the new coefficient valuations are at least

\[
 \bigl(r,\ \lceil2r/3\rceil,\ \lceil r/3\rceil\bigr).
\]

For \(r=1\) this is case E; for \(r=2\) it is case R.  Scale invariance then transports the
type back to the original cubic.  Thus HYP.07 is proved in its full single-side scope, while the
excluded \(v(B_1)=1\) example is correctly treated as a multi-side polygon.

## 4. Characteristic-free cubic trichotomy

**Lemma 4.1.**  A monic cubic over any field (k) satisfies exactly one of:

1. it has a simple root in (k);
2. it has no root in (k);
3. it equals \((X-\gamma)^3\) for a unique \(\gamma\in k\).

**Proof.**  Suppose the cubic has a root \(\rho\) but no simple root.  Factor it as

\[
 (X-\rho)^2(X-s).
\]

If (s\ne\rho), then (s) is a root and the derivative there is \((s-\rho)^2\ne0\), a
contradiction.  Thus (s=\rho) and the polynomial is \((X-\rho)^3\).  Conversely a perfect cube
has no simple root.  Uniqueness follows from uniqueness of the monic linear factor, or directly
from equality of the two cubics.  This proof is valid in characteristics (2) and (3). \(\square\)

For a lift over (O), a simple residual root lifts by ordinary Hensel to a root (r\in O) at
which (F'(r)) is a unit.  A rootless residual cubic is irreducible and its entire level-one
coefficient class is decided of unramified type \(\{(1,3)\}\).  Therefore every undecided cubic
class of positive level lies either in the *peel branch* (it has a unit-derivative root) or in the
*triple branch* (its residue is a perfect cube).

## 5. The peel branch and the term (q^{-N})

We use one already-proved quadratic fact, which is the exact (n=2) drainage law and is the
input patterned by `drainage_two`:

**Quadratic lemma.**  The number of undecided monic-quadratic coefficient classes modulo
\(\mathfrak m^N\) is exactly (q^N).

For completeness, the count has no tame-characteristic assumption.  A quadratic class is
undecided exactly when some centre \(\gamma\) satisfies

\[
 \pi^N\mid G(\gamma),\qquad
 \pi^{\lceil N/2\rceil}\mid G'(\gamma).                                  \tag{9}
\]

Such a centre is unique modulo \(\pi^{\lceil N/2\rceil}\): if \(\gamma'=\gamma+\delta\) is
another and (v(\delta)<\lceil N/2\rceil), then

\[
 G(\gamma')-G(\gamma)=\delta(G'(\gamma)+\delta)
\]

has valuation (2v(\delta)<N), contradicting (9).  For each of the
(q^{\lceil N/2\rceil}) centres, there are (q^{N-\lceil N/2\rceil}) possible linear
coefficients satisfying the derivative congruence, and the constant coefficient is then unique
modulo \(\pi^N\).  Hence the count is (q^N).  The equivalence with undecidedness is the landed
quadratic certificate dichotomy: failure of (9) gives one of the split/ramified/inert
certificates, while (9) permits two lifts of different type.  This is
`undecidedSet_eq_tangSet` plus `card_tangSet`, assembled as `undecidedCount_two_eq`.

Now fix (N\ge1).  Suppose an undecided cubic class (c\in U_N) has a lift (a) and a root
(r\in O) with (F_a'(r)\in O^\times).  Define the quadratic cofactor

\[
 g_{a,r}(X)=X^2+(a_2+r)X+(a_1+a_2r+r^2).                                \tag{10}
\]

The identity

\[
 F_a(X)=(X-r)g_{a,r}(X)                                                   \tag{11}
\]

follows by expansion and (F_a(r)=0).

The class of (g_{a,r}) modulo \(\pi^N\) is quadratic-undecided.  Indeed, suppose it were
decided of type \(\tau\).  For any other lift (a'\equiv a\pmod{\pi^N}), one has
(F_{a'}(r)\in\pi^NO), and (F_{a'}'(r)) is still a unit.  Ordinary Hensel gives a root
(r'=r+\delta) with initially \(\delta\in\mathfrak m\).  Expanding exactly,

\[
 0=F_{a'}(r+\delta)
  =F_{a'}(r)+\delta\bigl(F_{a'}'(r)+(3r+a'_2)\delta+\delta^2\bigr).
\]

The bracket is a unit: its first term is a unit and the other terms lie in \(\mathfrak m\).
Consequently \(\pi^N\mid\delta\).  Formula (10) now shows

\[
 g_{a',r'}\equiv g_{a,r}\pmod{\pi^N}.
\]

The assumed quadratic decidedness and (11) would force every lift (a') to have type
\(\{(1,1)\}\sqcup\tau\), contrary to (c\in U_N).

Choose one pair ((a,r)) for every undecided class in the peel branch and record

\[
 c\longmapsto\bigl(r\bmod\pi^N,\ g_{a,r}\bmod\pi^N\bigr).                \tag{12}
\]

This map is injective.  Indeed, if the two records agree, the reconstruction identities

\[
 a_2=g_1-r,\qquad a_1=g_0-g_1r,\qquad a_0=-rg_0                         \tag{13}
\]

show that the original cubic coefficient vectors agree modulo \(\pi^N\).  The second component
of (12) ranges through the quadratic undecided set.  Thus

\[
 \#(U_N\cap\text{peel branch})
 \le q^N\cdot q^N=q^{2N}.                                                \tag{14}
\]

After division by (q^{3N}), this is the term (q^{-N}) in (1).  The older tangency-pinning
bound (q^{-N/2}) is valid but not sharp enough for (14).

## 6. The triple-root step

Let (c\in U_{M+3}) lie in the triple branch.  Its residual polynomial is
\((X-\bar\gamma)^3\) for a unique \(\bar\gamma\in k\).  Fix once and for all a section
(s:k\to O) and put \(\gamma=s(\bar\gamma)\).  Recenter:

\[
 F_a(X+\gamma)=X^3+B_2X^2+B_1X+B_0,                                    \tag{15}
\]

where

\[
 B_0=F_a(\gamma),\quad B_1=F_a'(\gamma),\quad B_2=a_2+3\gamma.
\]

All three (B_i) lie in \(\mathfrak m\).  The following four cases are exhaustive and disjoint:

\[
\begin{array}{c|c|c}
\text{case}&\text{condition}&\text{type/conclusion}\\ \hline
E&\pi^2\nmid B_0&\{(3,1)\}\\
L&\pi^2\mid B_0,\ \pi^2\nmid B_1&\{(1,1),(2,1)\}\\
R&\pi^2\mid B_0,\ \pi^2\mid B_1,\ \pi^3\nmid B_0&\{(3,1)\}\\
S&\pi^3\mid B_0,\ \pi^2\mid B_1&\text{extract and recurse.}
\end{array}                                                               \tag{16}
\]

Cases E and R were proved in Section 3.4.  It remains to justify L.

Write (B_1=\pi u) with (u\in O^\times), (B_0=\pi^2C), and (B_2=\pi D).  Choose
(t=-Cu^{-1}) and (x_0=\pi t).  Direct expansion gives

\[
 F(x_0)=\pi^3(t^3+Dt^2),
\]

while

\[
 F'(x_0)=\pi\bigl(u+\pi(3t^2+2Dt)\bigr),
\]

whose parenthesis is a unit.  Lemma 3.1 with (k=3,w=1) gives a root (r) such that
\(r\equiv x_0\pmod{\pi^2}\), in particular \(\pi\mid r\).  Its cofactor has coefficients

\[
 g_1=B_2+r\in\mathfrak m,qquad
 g_0=B_1+B_2r+r^2\equiv B_1\pmod{\pi^2}.
\]

Thus (v(g_0)=1), so (g) is an Eisenstein quadratic.  Peeling (r) gives type
\(\{(1,1),(2,1)\}\).  This proves case L, including at (p=2,3).

The conditions in E, L, and R depend only on the coefficients modulo \(\pi^3\).  Translation
preserves type and congruence.  Hence, if any of E, L, R held for (15), every lift of the original
level-(M+3) class would have the displayed type.  That would decide (c), a contradiction.
Therefore S is forced.  There is (d=(d_0,d_1,d_2)\in O^3) with

\[
 B_0=\pi^3d_0,\qquad B_1=\pi^2d_1,\qquad B_2=\pi d_2.                    \tag{17}
\]

Moreover the level-(M) class of (d) is undecided.  For if that class were decided, take any
(a'\equiv a\pmod{\pi^{M+3}}), recenter at the same \(\gamma\), and extract (d').  Equations
(7) show (d'\equiv d\pmod{\pi^M}).  Scale invariance applied to

\[
 F_{B'}(\pi Y)=\pi^3F_{d'}(Y)
\]

and shift invariance would then give one fixed type for every (a'), contradicting the
undecidedness of (c).  This proves the triple-root step, including all level bookkeeping.

## 7. The sharp triple-root count and the constant (q^{-5})

Define the mixed-precision box

\[
 \mathcal B_M=(O/\mathfrak m^M)\times(O/\mathfrak m^{M+1})
                    \times(O/\mathfrak m^{M+2}).                         \tag{18}
\]

It has cardinality (q^{3M+3}).  Let

\[
 \tau_M:\mathcal B_M\longrightarrow A_M
\]

reduce all three coordinates modulo \(\mathfrak m^M\).  This is a surjective homomorphism of
finite additive groups.  All its fibres therefore have the same cardinality, namely

\[
 \frac{q^{3M+3}}{q^{3M}}=q^3.                                           \tag{19}
\]

Consequently

\[
 \#\tau_M^{-1}(U_M)=q^3C_M.                                             \tag{20}
\]

For each undecided triple-root class at level (M+3), perform Section 6 using the fixed lift
(s(\bar\gamma)) of its unique residual centre and record

\[
 c\longmapsto
 \left(\bar\gamma,
 d_0\bmod\mathfrak m^M,
 d_1\bmod\mathfrak m^{M+1},
 d_2\bmod\mathfrak m^{M+2}\right).                                     \tag{21}
\]

The record belongs to (k\times\tau_M^{-1}(U_M)).  It is injective.  Indeed, equal records
give the same \(\gamma=s(\bar\gamma)\) and precisely the three congruences in (7).  Multiplying
them by \(\pi^3,\pi^2,\pi\), respectively, shows that the three recentered coefficients agree
modulo \(\pi^{M+3}\).  Applying the inverse translation (X\mapsto X-\gamma) shows that the
original coefficient vectors agree modulo \(\pi^{M+3}\), so the two classes are equal.

By (20) and \(\#k=q\),

\[
 \#(U_{M+3}\cap\text{triple branch})
 \le q\cdot q^3C_M=q^4C_M.                                              \tag{22}
\]

The normalized ambient box grows from (q^{3M}) to (q^{3(M+3)}=q^{3M+9}).  Therefore the
normalized multiplier in (22) is

\[
 \frac{q^4q^{3M}}{q^{3M+9}}=q^{-5}.                                    \tag{23}
\]

This derives the ledger's (q^{-5}); it is not asserted.  If all (d_i) are instead recorded
uniformly modulo \(\pi^{M+2}\), the record has three unnecessary digits and gives (q^7C_M),
hence only (q^{-2}).  The mixed precisions are essential for the sharp constant.

## 8. HYP.08: assembly of the recurrence -- **PROVED**

By Lemma 4.1, an undecided level-N class, (N\ge1), lies in the peel or triple branch; the
rootless residual branch is already decided.  A union bound, (14), and (22), with (N=M+3), give

\[
 C_{M+3}\le q^{2(M+3)}+q^4C_M.
\]

Dividing by (q^{3(M+3)}) gives

\[
 u_{M+3}
 \le q^{2(M+3)-3(M+3)}
      +q^{4+3M-3(M+3)}u_M
 =q^{-(M+3)}+q^{-5}u_M.
\]

This is (1).  Thus HYP.08 is **PROVED in a strengthened form**.  The exact correction is

\[
 \boxed{q^{-N/2}\ \text{may be replaced by}\ q^{-N}.}
\]

No assertion about the conservative `hex3U` reader is used or proved here.  The recurrence is
about the actual `undecidedSet` in the coefficient boxes.

## 9. HYP.09: Haar-null complement and drainage -- **PROVED**

Let

\[
 E_N=\operatorname{pr}_N^{-1}(U_N)\subseteq O^3.
\]

Each (E_N) is a finite union of clopen coefficient cylinders and is measurable.  If a class is
decided at level (N), every refinement is decided with the same type.  Hence

\[
 E_{N+1}\subseteq E_N.                                                    \tag{24}
\]

By (4), \(\mu(E_N)=u_N\), and by (3), \(\mu(E_N)\to0\).  Continuity from above for the finite
measure \(\mu\) gives

\[
 \mu\left(\bigcap_{N\ge0}E_N\right)=\lim_{N\to\infty}\mu(E_N)=0.         \tag{25}
\]

The intersection in (25) is exactly the locus which remains undecided at every finite
coefficient precision.  In particular its triple-root recursive sublocus is null.  This is the
measure-theoretic null-complement statement of HYP.09.

For the corpus's named statement, fix a type \(\sigma\).  At level (N), a class which is
\(\sigma\)-possible but not \(\sigma\)-decided must lie in (U_N): if it were decided of some
type \(\tau\), its \(\sigma\)-type lift would force \(\tau=\sigma\).  Therefore

\[
 0\le \operatorname{possibleSeq}_\sigma(N)
       -\operatorname{decidedSeq}_\sigma(N)\le u_N\longrightarrow0.
\]

Thus `UndecidedVanishes O 3 σ` holds for every \(\sigma\).  This implication does not require
the assertion that there are exactly five cubic types (HYP.10); HYP.10 is needed for the
five-type total-mass converse/assembly, not for drainage.

## 10. Ledger disposition and correspondence with landed Lean

| row | disposition | mathematical supplier |
|---|---|---|
| HYP.04 | **PROVED** | Lemma 3.1; landed as `Uniformity.Hensel.strongHensel` and `strongHensel_addVal` |
| HYP.05 | **PROVED** | Section 3.2; landed as `Uniformity.Density.typeOf_shift` |
| HYP.06 | **PROVED** | Section 3.3, including (7); landed as `typeOf_scale`, with the level step in `undecided_of_extract` |
| HYP.07 | **PROVED** | Section 3.4, cases E and R; landed as `typeOf_ram3_of_val_one` and `typeOf_ram3_of_val_two` |
| HYP.08 | **PROVED, STRONGER CONSTANT** | Sections 5--8; natural-number form `undecidedCount_three_recursion` in `ChapH/H97r4.lean` |
| HYP.09 | **PROVED** | Section 9; landed as `undecidedSeq_three_tendsto_zero`, `drainage_three`, and `drainageAt_three` in `ChapH/H97b.lean` |

The proof also uses the already-closed quadratic theorem
`undecidedCount_two_eq : undecidedCount O 2 N = q^N` from `ChapG/G36.lean`.  Degree one is the
degenerate model: every monic linear polynomial has type \(\{(1,1)\}\), so its ambiguity gap is
identically zero (`drainage_one`).

The current ledger prose predates the `H97r1`--`H97r4` and `H97b` landings.  Mathematically,
HYP.08 and HYP.09 are no longer open.  The exact recurrence that should be quoted in future
consumers is (1), not the weaker and notationally ambiguous displayed recurrence in the ledger.

## 11. Scope and remaining open mathematics

There is no open step in the cubic drainage block HYP.04--HYP.09.  This proof does **not** prove
the four still-missing exact cubic density formulas: those require the resultant-weighted deep
menu.  It also does not identify the actual undecided count with the conservative arithmetic
function `hex3U`; drainage is proved directly on `undecidedSet`, so no such identification is
needed.
