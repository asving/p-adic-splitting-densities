# L7 — Functional equation $q\mapsto 1/q$ transfers from tame primes by interpolation

**Date:** 2026-06-14.
**Status:** Proven, modulo two clearly-isolated external inputs (the tame rationality of
Del Corso–Dvornicich / Yin, and the L6 single-rational-function statement, which is assumed
as a hypothesis here). Numeric checks confirm the mechanism on $n\le 3$.

Throughout, $K/\mathbb{Q}_p$ is finite unramified with residue field $\mathbb{F}_q$ ($q=p^k$),
and $\rho(n,\sigma;q)$ is the factorization-type density in the **projective ($\mathbb{P}^n$)
normalization** of the paper — i.e.
$$
\rho(n,\sigma;q) \;=\; \mu_{\mathrm{Haar}}\bigl(\{h\in K[z]\text{ of degree }n : K[z]/h(z)\text{ \'etale of type }\sigma\}\bigr)
$$
with the projective normalization of Lemma `bhargava densities to our densities`
(`main_gemini_revision.tex`, l.1034–1049). **This normalization is load-bearing**: the
monic-density variants do *not* satisfy the $q\mapsto 1/q$ symmetry (verified below).

---

## 0. Precise statement

> **Lemma L7.** Fix $n\ge 1$ and a factorization type $\sigma$ of degree $n$ with
> $\sum_i e_i f_i = n$. Assume:
> - **(H-tame)** For every local field $K$ whose residue characteristic $p$ is coprime to all
>   exponents $e_i$ occurring in $\sigma$ (in particular for every $p>n$), there is a rational
>   function $R_\sigma\in\mathbb{Q}(t)$ with $\rho(n,\sigma;q)=R_\sigma(q)$ for the residue size
>   $q$, and $R_\sigma(t^{-1})=R_\sigma(t)$ (this is the paper's Theorem
>   `symmetry follows from rationality for factorization densities`, l.1073–1085, resting on the
>   palindromic-weight machinery of Theorems `symmetry for pullback` / `twist symmetry under
>   pullback` together with the tame rationality of Del Corso–Dvornicich `del_corso_dvornicich_2000`
>   and Yin `john`).
> - **(H-L6)** There is a *single* rational function $S_\sigma\in\mathbb{Q}(t)$ with
>   $\rho(n,\sigma;q)=S_\sigma(q)$ for **every** prime power $q$ (all $p$, wild included). This is
>   the conclusion of L6.
>
> Then $S_\sigma=R_\sigma$ as elements of $\mathbb{Q}(t)$, and consequently
> $$
> S_\sigma(t^{-1})=S_\sigma(t).
> $$
> In particular $\rho(n,\sigma;q)$ satisfies the functional equation $q\mapsto 1/q$ at **every**
> prime $p$, including the wild primes $p\le n$.

Two remarks on the hypotheses, both honestly flagged:

1. **(H-tame) is the paper's, not an extra assumption.** The task statement phrases the tame
   hypothesis as "$p\nmid n!$", i.e. $p>n$. The paper's tame theorem actually holds on the
   *larger* set $\mathcal L_\sigma=\{K:\ \mathrm{char}\,\mathbb{F}_K \nmid \prod_i e_i\}$. Since
   each $e_i\le n$, every $p>n$ lies in $\mathcal L_\sigma$, so the task's $p>n$ set is a subset
   of $\mathcal L_\sigma$; using either set, the tame set of residue characteristics is cofinite
   in the primes, hence the tame set of *residue sizes* is infinite (see §3). I will work with
   the task's set $\{q=p^k : p>n\}$, which suffices and is cleanest.

2. **(H-L6) is consumed, not re-proven.** L7 is purely the *transfer* step: it takes the two
   rational functions handed to it (one valid on a cofinite-in-primes set with the symmetry,
   one valid everywhere) and identifies them. The truth of (H-L6) is L6's responsibility; the
   truth of the symmetry on the tame locus is the paper's. L7 contributes the (elementary but
   genuinely necessary) fact that these two facts combine to give the symmetry at wild primes.

---

## 1. The algebraic core: a rational function is determined by an infinite set of values

> **Proposition 1 (Identity theorem for $\mathbb{Q}(t)$).** Let $F\in\mathbb{Q}(t)$ and let
> $T\subset\mathbb{Q}$ be an infinite set such that $F$ is defined (no pole) at every $a\in T$.
> If $F(a)=0$ for all $a\in T$, then $F=0$ in $\mathbb{Q}(t)$.

*Proof.* Write $F=N/D$ with $N,D\in\mathbb{Q}[t]$ coprime, $D\ne 0$. At each $a\in T$, $D(a)\ne 0$
(no pole), so $F(a)=0$ forces $N(a)=0$. Thus $N$ has infinitely many roots in $\mathbb{Q}$. A
nonzero polynomial over a field (here $\mathbb{Q}$, an integral domain) of degree $d$ has at most
$d$ roots (factor theorem + the fact that $\mathbb{Q}[t]$ is a domain, so a degree-$d$ polynomial
factors into at most $d$ linear factors over any extension). Hence $N=0$, i.e. $F=0$. $\qquad\blacksquare$

> **Corollary 1 (two rational functions agreeing on an infinite set).** If $F,G\in\mathbb{Q}(t)$
> and $F(a)=G(a)$ for all $a$ in an infinite set $T\subset\mathbb{Q}$ at which both are defined,
> then $F=G$.

*Proof.* Apply Proposition 1 to $F-G\in\mathbb{Q}(t)$, which is defined on $T$ (difference of
functions defined there) and vanishes on the infinite set $T$. Hence $F-G=0$. $\qquad\blacksquare$

This is exactly assertion **A9** in `ASSERTIONS.md` ("a rational function is determined by values
at tame prime powers"), made precise. Note we only ever need the **zero-set bound** ($\#$ zeros
$\le \deg N$); we never need to *reconstruct* $R_\sigma$ from finitely many values, and in
particular we do **not** need any a priori degree bound. (The numeric experiment in §5 shows why
naive finite interpolation *with a guessed denominator* fails — but that is a strawman; the
identity theorem sidesteps it entirely.)

---

## 2. The tame side genuinely delivers the symmetric rational function $R_\sigma$

This section records *why* (H-tame) holds, i.e. that the resolution route does produce a single
$R_\sigma\in\mathbb{Q}(t)$ with $R_\sigma(t^{-1})=R_\sigma(t)$, valid at the tame residue sizes.
I cite the paper's chain precisely; nothing new is proved here, but the citations matter because
L7's conclusion is only as strong as this input.

**(2a) Rationality on the tame locus.** For $K$ with residue characteristic coprime to the $e_i$
(e.g. $p>n$), every \'etale algebra of type $\sigma$ is *tamely* ramified, and the recurrence of
Del Corso–Dvornicich `del_corso_dvornicich_2000` (and independently Yin `john`) shows
$q\mapsto\rho(n,\sigma;q)$ is a rational function of $q$, uniformly over such primes. This is the
$\mathcal L_\sigma$ rationality invoked at l.1080.

**(2b) The functional equation on the tame locus (palindromic-weight machinery).** Fix a single
prime $p>n$ and let $q$ range over the powers $p,p^2,p^3,\dots$ (i.e. over the residue sizes
$q^m$ of the unramified extensions of $\mathbb{Q}_p$, $m\ge 1$). Over this arithmetic progression:

  - For $p>n=\dim Y$ (so $p\nmid |S_n|$, since $|S_n|=n!$ and $p>n\Rightarrow p\nmid n!$), the
    group $H=H_\sigma\subset S_n$ has order prime to $p$; $H$ is therefore linearly reductive in
    residue characteristic $p$, and a characteristic-$0$ $G$-equivariant resolution of
    $(\mathbb{P}^1)^n/H_\sigma\to\mathbb{P}^n$ spreads out to an SNCD resolution over
    $\widehat{\mathcal O}_{\mathbb{Q},p}$ (Theorem `main theorem for almost all primes`, l.970–979,
    with Remark `char 0 resolutions`). Thus Hypothesis `res of sing` is satisfied at every $p>n$.
  - Theorem `symmetry for pullback` (l.815) and its twisted form `twist symmetry under pullback`
    (l.877) then express the relevant integral $\eta_{f_{\sigma'}}(K)$ as a $\mathbb{Q}$-linear
    combination of products
    $$
    \prod_i \eta_{e_i}^{|\Lambda_i|}(m;q^{k_i/\ell_i})\,\bigl(|{}^{g}D_{\mathcal L}(\mathbb{F}_{q^m})| + |{}^{g^{-1}}D_{\mathcal L}(\mathbb{F}_{q^m})|\bigr),
    $$
    each summand a **palindromic form of weight $\dim Y=n$** in the variable $m$
    (Lemmas `point counts have right weight`, `twisted point counts have the right weight`,
    and Definition `rho, eta`; the palindromicity is Poincaré duality on the smooth proper
    strata $D_{\mathcal L}$, i.e. the Weil conjectures).
  - By Equation `factorization densities as integrals` (l.1132) and Lemma
    `relation of bhargava conjecture to our theorem` (l.1061), $\rho(n,\sigma;q^m)$ is the ratio
    of such a palindromic form of weight $n$ by $|\mathbb{P}^n(\mathbb{F}_{q^m})|$, itself
    palindromic of weight $n$; a ratio of weight-$n$ palindromic forms is a palindromic form of
    weight $0$, i.e. satisfies $\Phi(-m)=\Phi(m)$ (Theorem
    `symmetry follows from rationality for factorization densities`, l.1073–1085).

  The weight-$0$ palindromic property $\Phi(-m)=\Phi(m)$ is *exactly* the statement
  $\rho(n,\sigma;q^{-m})=\rho(n,\sigma;q^{m})$ along this progression, i.e.
  $R_\sigma(q^{-m})=R_\sigma(q^m)$ for all $m\ge 1$.

**(2c) Upgrading "$R_\sigma(q^{-m})=R_\sigma(q^m)$ along one progression" to "$R_\sigma(t^{-1})=R_\sigma(t)$
in $\mathbb{Q}(t)$".** Define $G(t):=R_\sigma(t^{-1})-R_\sigma(t)\in\mathbb{Q}(t)$ (well-defined:
$R_\sigma(t^{-1})$ is the image of $R_\sigma$ under the $\mathbb{Q}$-algebra automorphism
$t\mapsto t^{-1}$ of $\mathbb{Q}(t)$). By (2b), $G(p^m)=0$ for all $m\ge 1$; the set
$\{p^m:m\ge1\}$ is infinite and avoids the finitely many poles of $G$ (discard the finitely many
$m$ with $p^m$ a pole). By Proposition 1, $G=0$, i.e. $R_\sigma(t^{-1})=R_\sigma(t)$ identically.
This is the precise sense in which "the tame resolution proof delivers the functional equation":
it gives the symmetry on one geometric progression of $q$-values, and Proposition 1 promotes it
to an identity in $\mathbb{Q}(t)$.

> **Important normalization caveat (verified, §5).** The symmetry holds for the **projective**
> density $\rho(n,\sigma;q)$, *not* for the monic-polynomial density. For $n=3$ the monic
> densities $t_{111},\dots,t_{1c}$ violate $R(1/q)=R(q)$ (nonzero differences in §5), whereas the
> five projective densities satisfy it exactly ($R(1/q)-R(q)=0$). L7 — and the whole paper —
> concerns the projective normalization (Lemma `bhargava densities to our densities`,
> $\mu_{\mathrm{Haar}}(\pi^{-1}S)=\mu_{\mathbb{P}^n}(S)/|\mathbb{P}^n(\mathbb{F}_q)|$). Any
> statement of L7 that omitted "projective" would be false.

---

## 3. The tame set of residue sizes is infinite

Let $T_\sigma=\{q=p^k:\ p>n,\ k\ge 1\}$ be the set of residue sizes of finite unramified
extensions of $\mathbb{Q}_p$ for tame $p$. Since there are infinitely many primes $p>n$
(Euclid), and for each such $p$ already $p\in T_\sigma$, the set $T_\sigma\subset\mathbb{Q}$ is
infinite. (We do not even need prime powers $k\ge2$; the primes $p>n$ alone are infinite. The
prime powers are nonetheless legitimate elements of $T_\sigma$ because the unramified base
hypothesis lets us realize residue size $p^k$ via $K=\mathbb{Q}_{p^k}$, all with $v(p)=1$.)

Moreover $T_\sigma$ is contained in the paper's tame locus $\mathcal L_\sigma$ (residue char
coprime to $\prod_i e_i$), since $p>n\ge e_i$ forces $p\nmid e_i$. So (H-tame) supplies, for
every $q\in T_\sigma$, the equality $\rho(n,\sigma;q)=R_\sigma(q)$ with the symmetric
$R_\sigma\in\mathbb{Q}(t)$ from §2.

---

## 4. Proof of L7

Both $S_\sigma$ (from (H-L6)) and $R_\sigma$ (from (H-tame), §2) are elements of $\mathbb{Q}(t)$.

**Step 1 — agreement on $T_\sigma$.** For every $q\in T_\sigma$ we have, by (H-L6) and (H-tame)
respectively,
$$
S_\sigma(q)=\rho(n,\sigma;q)=R_\sigma(q).
$$
(Both right-hand evaluations are the *same real number* $\rho(n,\sigma;q)$ — the honest density of
the same measurable set in the same coefficient space — so there is no ambiguity in equating them.
This is the only place where the two routes must be checked to compute the *same* quantity, and
they do: both are $\mu_{\mathrm{Haar}}$ of the type-$\sigma$ locus in projective coefficient space.)

**Step 2 — finitely many bad points.** $S_\sigma$ and $R_\sigma$ each have finitely many poles in
$\mathbb{Q}$. Remove from $T_\sigma$ the finitely many $q$ that are poles of $S_\sigma$ or
$R_\sigma$; call the result $T'_\sigma$. Then $T'_\sigma$ is still infinite (infinite minus
finite) and both functions are defined on $T'_\sigma$, with $S_\sigma=R_\sigma$ there by Step 1.

**Step 3 — identity in $\mathbb{Q}(t)$.** By Corollary 1 applied to $F=S_\sigma$, $G=R_\sigma$,
$T=T'_\sigma$, we conclude $S_\sigma=R_\sigma$ as elements of $\mathbb{Q}(t)$.

**Step 4 — the functional equation propagates.** Applying the automorphism $t\mapsto t^{-1}$ to the
identity $S_\sigma=R_\sigma$ gives $S_\sigma(t^{-1})=R_\sigma(t^{-1})$. By §2c,
$R_\sigma(t^{-1})=R_\sigma(t)$. Hence
$$
S_\sigma(t^{-1})=R_\sigma(t^{-1})=R_\sigma(t)=S_\sigma(t)\quad\text{in }\mathbb{Q}(t).
$$
Since $S_\sigma$ represents $\rho(n,\sigma;q)$ at *every* prime power $q$ (H-L6), the functional
equation
$$
\rho(n,\sigma;q^{-1})=\rho(n,\sigma;q)
$$
holds at every prime, including all wild $p\le n$. $\qquad\blacksquare$

---

## 5. Numeric sanity checks (sympy)

All computed via `padic_types.py` closed forms and sympy; see commands run on 2026-06-14.

**(C1) Functional equation holds for the projective densities, fails for monic.**
For $n=3$, $R(1/q)-R(q)$ computed symbolically:

| type | monic density | projective density |
|------|---------------|--------------------|
| 111  | $(1-q^3)(q-1)(q^2-q+1)/[6(q+1)(q^5-1)]\ne 0$ | $0$ |
| 12   | nonzero | $0$ |
| 3    | nonzero | $0$ |
| 1r1  | $q^2(q-1)^2/[(q+1)(q^5-1)]\ne 0$ | $0$ |
| 1c   | $(q-1)(q^2-1)(q^2+1)/(q^5-1)\ne 0$ | $0$ |

Sum of the five projective densities $=1$ identically. **Conclusion:** the $q\mapsto1/q$ symmetry
is a property of the *projective* normalization only — this is the normalization in L7, and the
distinction is essential (matches the paper, l.1034–1049, and `STRUCTURAL_MECHANISM.md` §A1's
"volumes are special" caution).

**(C2) Agreement on tame samples + identity-theorem bound.** The verified all-prime closed form
$S_{111}(q)=(q^4+2q^2+1)/(6q^4+6q^3+6q^2+6q+6)$ agrees with the oracle at
$q\in\{5,7,11,13,17,19,23,25,49,121\}$ (a mix of tame primes and tame prime powers). Numerator and
denominator of $S_{111}$ both have degree $4$; a nonzero $S-R=N/D$ has at most $\deg N<\infty$
zeros, while $T'_\sigma$ is infinite — confirming the mechanism of §4.

**(C3) Why naive finite interpolation is the wrong tool (strawman check).** Attempting to
*reconstruct* $R$ from $6$ tame samples while guessing the denominator
$6(q+1)(q^5-1)(q^3+q^2+q+1)$ produced a degree-$5$ numerator that does **not** equal $S$ — because
the guessed denominator was wrong and $6$ points underdetermine the (true) function. This is
exactly why L7 uses the *identity theorem* (Corollary 1, which needs no degree/denominator guess)
rather than Lagrange/rational interpolation. The identity theorem only ever uses "infinitely many
zeros ⟹ zero," which is robust.

---

## 6. Gaps and honest assessment

L7 *as a transfer lemma* is rigorous and elementary given its two hypotheses. The residual risk
is entirely in the inputs, which are not L7's to discharge:

- **(G1, minor for L7 / fatal for the program if false) (H-L6) is assumed.** L7 cannot be more
  true than L6. If L6's single-rational-function claim fails (e.g. if the densities were only
  rational along arithmetic progressions in $q$, as the *splitting* densities $\rho_{f,\tau}$ are —
  see l.1087), then there is no $S_\sigma$ to identify with $R_\sigma$ and L7 is vacuous. L6 is a
  separate lemma in the skeleton; here we only flag the dependency.
- **(G2, minor) (H-tame) cites external rationality.** The tame rationality (2a) rests on
  Del Corso–Dvornicich / Yin. These are published and standard for *tamely ramified* splitting
  densities; I have not re-derived them. The functional equation part (2b–2c) is internal to the
  paper and is sound modulo the paper's resolution at tame primes (which holds because $p\nmid|S_n|$
  for $p>n$, the non-wild case the referee did *not* dispute).
- **(G3, minor) "same quantity" check.** Step 1 equates two evaluations of $\rho(n,\sigma;q)$. One
  must know both routes compute the identical density (same measurable set, same normalization).
  They do — both are $\mu_{\mathbb{P}^n}$-volume of the type-$\sigma$ locus — but this relies on
  Lemma `relation of bhargava conjecture to our theorem` identifying the resolution-side
  $\eta_{f_\sigma}$ combination with $\rho(n,\sigma;\cdot)$. That identification is in the paper
  and is not in dispute.
- **(G4, minor) prime-power tame values.** I include $q=p^k$ with $k\ge2$ in $T_\sigma$. These are
  legitimate (unramified base, $v(p)=1$), but even discarding them the primes $p>n$ alone give an
  infinite $T_\sigma$, so the argument does not depend on prime powers.
- **No fatal gap in L7 itself.** The identity theorem (Prop 1) is unconditional; the only
  non-elementary content is bookkeeping (finitely many poles, automorphism $t\mapsto t^{-1}$ of
  $\mathbb{Q}(t)$), all routine.

**Bottom line.** Given L6 (single rational function at all $q$) and the paper's tame symmetry
theorem (which is not affected by the Prop 5.3 failure, since that failure is confined to wild
$p\le n$), L7 rigorously transfers the functional equation to wild primes. The transfer step is
the easy and certain part; all genuine difficulty has been correctly relocated into L6 and the
tame resolution, exactly as the skeleton intends.
