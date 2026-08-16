# CITE-SCOPE resolution — published general-`O` sources for every ℚ_p-scoped citation

**Date:** 2026-08-13. **Unit:** literature search closing the H6/`CITE-SCOPE` findings of the
8-slice generality audit (`runs/qgen/Q1..Q8_output.log`). **Author:** literature agent.

**Charge.** The Lean capstone quantifies over all complete DVRs `O` with finite residue field
`F_q` — equal characteristic `F_q[[t]]` included. The audit found the corpus's own arguments
characteristic-blind but flagged ~15 `CITE-SCOPE` rows that all trace to one root: the
Ore/GMN/FGMN citations are consumed at general `O` while the pinned source
(Guàrdia–Montes–Nart, *Newton polygons of higher order in algebraic number theory*, TAMS 364
(2012) 361–416 = arXiv:0807.2620) fixes a finite extension `K/ℚ_p`. For each distinct consumed
statement: does a **published** general statement exist?

## 0. Verdict in one paragraph

**Yes, for essentially everything.** Two refereed papers by (supersets of) the same authors carry
the whole OM/Ore package at a scope that strictly contains ours:

- **[AGNPRW]** M. Alberich-Carramiñana, J. Guàrdia, E. Nart, A. Poteaux, J. Roé, M. Weimann,
  *Polynomial factorization over henselian fields*, **Found. Comput. Math. (2024)**, DOI
  10.1007/s10208-024-09646-x = **arXiv:2207.02139**. Standing setting: an **arbitrary valued
  field** — no discreteness, no completeness, no residue-field hypothesis.
- **[GN15]** J. Guàrdia, E. Nart, *Genetics of polynomials over local fields*, **Contemp. Math.
  637 (2015) 207–241** (AGCT proceedings), DOI 10.1090/conm/637/12767. Standing setting: **an
  arbitrary discrete valued field `(K,v)`**.

together with **[FGMN]** (already local to the repo; scope "a field equipped with a discrete
valuation", not ℚ_p), **[GNP12]** (J. Symb. Comput.; "local field" = complete discretely valued
with **perfect** residue field), **[BNS13]** and **[Nart14]** ("local field" = **locally compact**
complete discretely valued ⇒ finite residue field = exactly our `O`), and **[Kuhlmann]** for
defectlessness. The single most economical fix is a **bibliography swap**, not a re-proof.

**Method / honesty.** Every scope quote below was read out of a document fetched in this session
(arXiv PDF → `pdftotext -layout`, or a repo-local copy under `docs/references/`). Nothing is
quoted from memory. Where a printed (publisher) version could not be opened, the arXiv/author
copy is cited explicitly as the surrogate and the fact is flagged. Rows I could not verify are
marked **UNVERIFIED** with what would be needed.

---

## 1. Source register — standing settings, quoted verbatim

| Tag | Full reference | What I actually read | Standing setting, VERBATIM |
|---|---|---|---|
| **[GMN12]** | Guàrdia–Montes–Nart, *Newton polygons of higher order in algebraic number theory*, Trans. Amer. Math. Soc. **364** (2012) 361–416 (arXiv:0807.2620) | repo-local LaTeX source `docs/references/HigherNewton.tex`, line 401 | "We fix a finite extension $K$ of $\Q_p$ as a base field, and we denote $v:=v_K$, $\oo:=\oo_K$, $\m:=\m_K$, $\ff{}:=\ff{K}$, $q:=\|\ff{}\|$. We fix also a prime element $\pi\in\oo$." — **ℚ_p-only. Confirmed.** |
| **[AGNPRW]** | Alberich-Carramiñana, Guàrdia, Nart, Poteaux, Roé, Weimann, *Polynomial factorization over henselian fields*, Found. Comput. Math. (2024), DOI 10.1007/s10208-024-09646-x | arXiv:2207.02139v1 PDF, §1 line 102 (publisher PDF paywalled — arXiv is the surrogate) | "**Let $(K,v)$ be a valued field, with valuation ring $O$ and residue class field $k$.** Let $\Gamma=v(K^*)$ be the value group and denote by $\Gamma_{\mathbb Q}=\Gamma\otimes\mathbb Q$ the divisible hull of $\Gamma$." Abstract: "Given a valued field $(K,v)$ and an irreducible polynomial $g\in K[x]$, we survey the ideas of Ore, Maclane, Okutsu, Montes, Vaquié and Herrera-Olalla-Mahboub-Spivakovsky, leading (under certain conditions) to an algorithm to find the factorization of $g$ over a henselization of $(K,v)$." |
| **[GN15]** | Guàrdia–Nart, *Genetics of polynomials over local fields*, Contemp. Math. **637** (2015) 207–241 | author PDF at `upcommons.upc.edu` (open), Introduction + §1 line 148 | "In this paper, we deal with **an arbitrary discrete valued field $(K,v)$** with valuation ring $O$. Let $K_v$ be the completion of $K$ at $v$ … Given a monic square-free polynomial $f\in O[x]$, we are interested in the computation of the prime factors of $f$ in $O_v[x]$." And §1: "Let $K$ be a field equipped with a discrete valuation $v:K^*\to\mathbb Z$, normalized so that $v(K^*)=\mathbb Z$." |
| **[FGMN]** | Fernández–Guàrdia–Montes–Nart, *Residual ideals of MacLane valuations*, J. Algebra **427** (2015) 30–75 (arXiv:1305.0775) | repo-local `docs/references/fgmn_residual_ideals_1305.0775v3_layout.txt`, line 137 | "**Let $K$ be a field equipped with a discrete valuation $v:K^*\longrightarrow\mathbb Z$, normalized so that $v(K^*)=\mathbb Z$.** Let $O$ be the valuation ring of $K$, $m$ the maximal ideal, $\pi\in m$ a generator of $m$ and $F=O/m$ the residue class field." Plus (line 141) "Let $K_v$ be the completion of $K$ …". No completeness, no residue-field hypothesis. |
| **[GNP12]** | Guàrdia–Nart–Pauli, *Single-factor lifting and factorization of polynomials over local fields*, J. Symb. Comput. **47** (2012) 1318–1346 (arXiv:1104.3181) | arXiv PDF, "Notation" para. + §2 opening | "Notation. Throughout the paper we fix a local field $K$, that is, **a complete field with respect to a discrete valuation $v$**. We let $O$ be its ring of integers, $m$ the maximal ideal of $O$, $\pi\in m$ a generator of $m$, $F=O/m$ the residue class field of $K$, **which is suposed to be perfect** …" — and the crucial widening sentence: "Although most of the results about Montes algorithm are formulated for separable polynomials over the ring of integers of a $p$-adic field, **they can be easily generalized to separable monic polynomials with integral coefficients over local fields with perfect residue field. In this paper we work in the general setting.**" |
| **[BNS13]** | Bauch–Nart–Stainsby, *Complexity of OM factorizations of polynomials over local fields*, LMS J. Comput. Math. **16** (2013) 139–171 (arXiv:1204.4671) | arXiv PDF, §1 | "Let $k$ be a **local field, i.e. a locally compact and complete field with respect to a discrete valuation $v$**. Let $O$ be the valuation ring of $k$, $m$ the maximal ideal, $\pi\in m$ a generator of $m$ and $F=O/m$ the residue field, **which is a finite field**." |
| **[Nart14]** | Nart, *Local computation of differents and discriminants*, Math. Comp. **83** (2014) no. 287, 1513–1534 (arXiv:1205.1340) | arXiv PDF, §1 | "Let $k$ be a **local field, i.e. a locally compact and complete field with respect to a discrete valuation $v$.**" |
| **[GMN11-IB]** | Guàrdia–Montes–Nart, *Higher Newton polygons and integral bases* — journal version **RESOLVED [A-3, 2026-08-16]: J. Number Theory 147 (2015) 549–589**, DOI 10.1016/j.jnt.2014.07.027 (Crossref; cited in that form by arXiv:1409.4345's bibliography); ~~arXiv:0902.3428v3, 22 Jul 2012; journal version UNVERIFIED~~ (the "arXiv-only" reading came from [FGMN]/[GN15], both written before it appeared) | arXiv PDF, abstract + §1 | Abstract: "Let $A$ be a Dedekind domain whose field of fractions $K$ is **a global field**." §1: "Let $k$ be a local field, i.e. a locally compact and complete field with respect to a discrete valuation $v$ … $F=O/m$ the residue field, which is a finite field." |
| **[PW26]** | Poteaux–Weimann, *Local polynomial factorisation: improving the Montes algorithm*, **arXiv:2607.02153v1, 2 Jul 2026 (PREPRINT — not refereed)** | arXiv HTML, §2 | "**Let $\mathbb L$ be a complete discrete valuation field**, $v:\mathbb L\to\mathbb Z\cup\{+\infty\}$ any normalised and surjective valuation on $\mathbb L$ and $\pi$ an uniformiser. … **The two fields we have in mind in this paper are $\mathbb L=\mathbb Q_p$ … and $\mathbb L=\mathbb K((t))$ the field of Laurent series over any field $\mathbb K$.**" |
| **[ML36]** | MacLane, *A construction for absolute values in polynomial rings*, Trans. Amer. Math. Soc. **40** (1936) 363–395 | D. Ford re-typeset PDF (`users.encs.concordia.ca/~ford/UNCG/smvals.pdf`), §1 Introduction | "The succession of values $V_1,V_2,\dots$ is defined in Part I for polynomials with **coefficients in any field $K$**. … Here, as in §§8 and 16, we assume that every value of the field $K$ is 'discrete'; that is, that the real numbers used as values form an isolated point set, as in the case of $p$-adic values." (Numbering caveat: re-typeset, not a scan; TAMS pagination unchecked.) |
| **[Kuhl]** | F.-V. Kuhlmann, *The defect*, in **Valuation theory in interaction**, EMS Ser. Congr. Rep. (2014) 277–318 | author PDF hosted at KGRC Vienna (`DEFECT.pdf`) | **Theorem 3.3** verbatim: "Let $(K,v)$ be a **discretely valued field**, that is, with value group $vK\simeq\mathbb Z$. **Then every finite separable extension is defectless.** If in addition $\operatorname{char}K=0$, then $(K,v)$ is a defectless field." (Publication venue **UNVERIFIED** at symbol level — I read the author's PDF, not the EMS volume.) |
| **[MdON-a]** | Moraes de Oliveira–Nart, *Computation of residual polynomial operators of inductive valuations* (arXiv:1901.04937) | arXiv PDF, abstract | "Let $(K,v)$ be a valued field, and $\mu$ an inductive valuation on $K[x]$ extending $v$. … This leads to an OM algorithm to compute the factorization of separable defectless polynomials over henselian fields." |
| **[ACGNR21]** | Alberich-Carramiñana, Guàrdia, Roé, Nart, *Okutsu frames of irreducible polynomials over henselian fields* (arXiv:2111.02811) | arXiv abstract page | "For a **henselian valued field $(K,v)$** we establish a complete parallelism between the arithmetic properties of irreducible polynomials $F\in K[x]$, encoded by their Okutsu frames, and the valuation-theoretic properties of their induced valuations $v_F$ on $K[x]$, encoded by their MacLane-Vaquié chains." |
| **[Nart20]** | Nart, *Key polynomials over valued fields*, Publ. Mat. **64** (2020) 195–232 (arXiv:1803.08406) | arXiv PDF, Introduction | "In this paper, we fix **an arbitrary valuation $\mu$ on $K[x]$**, and we determine the structure of its graded algebra $\mathcal G_\mu$, and describe its set of key polynomials $\mathrm{KP}(\mu)$ …" |

**Why "locally compact complete discretely valued" is exactly our `O`.** A complete discretely
valued field is locally compact iff its residue field is finite. So [BNS13]/[Nart14]/[GMN11-IB]
§1 quantify over **precisely** the capstone's `O` (both characteristics), and the [GMN11-IB]
abstract's "global field" hypothesis likewise covers `F_q((t))` (every `F_q((u))` is the
completion of the global function field `F_q(u)` at `(u)`).

---

## 2. The needed-statements table

Column key. **Consumed as** = the corpus's own label + the audit row that flagged it.
**Verdict**: `COVERS-ALL-O` (published statement holds over every complete DVR with finite
residue field) · `COVERS-HENSELIAN-DISCRETE` (published at henselian/discrete scope, which
contains ours — complete DVR ⇒ henselian, discrete rank one) · `PARTIAL` · `NOT-FOUND`.

### NS-1 — Ore order 1: theorem of the polygon

- **Consumed as:** GMN Thm 1.15; `W12_PROOF_2026-08-08.md` S2 ("Ore's theorem … factors any
  `O`-lift `F`"), audit rows **Q1 W12-2**, **Q2** (HMENU3/HEX3/GENIND/GENH4, "Ore/GMN published
  theorem"), **Q3 GENHN** ("Ore order-1"), **Q1 HUMAN-8**.
- **Source:** [AGNPRW] **Theorem 4.4** (arXiv:2207.02139, §4.3). Verbatim: *"Let $\mu$ be an inner
  node of $\mathcal T$ and $\phi\in\mathrm{KP}(\mu)$. Denote $N=N^+_{\mu,\phi}(g)$ and let
  $Q\in\mathrm{Irr}(K^h)$ be the irreducible factor of $\phi$ determined by $\mu$. Then, (i) All
  $G\in\mathcal F_{\mu,\phi}(g)$ have degree a multiple of $\deg(Q)$. (ii) For all
  $\lambda\in\Gamma_{\mathbb Q}$, we have $\sum_{G\in\mathcal F_{\mu,\phi}(g)(\lambda)}\deg(G)
  =\ell(S_\lambda(N))\deg(Q)$. In particular, if $\ell(S_\lambda(N))=1$, then $\mathcal
  F_{\mu,\phi}(g)(\lambda)$ contains a unique irreducible factor of $g$, and this factor has degree
  $\deg(Q)$."* Their own remark: *"If $v$ has rank one, then $\phi=Q$ and this theorem follows
  easily from Montes' original arguments in the discrete rank-one case. The proof in the general
  case is much more involved."*
- **Alt source (nearer our formulation):** [GN15] **Theorem 2.3** — see NS-2, which states the
  polygon and residual dissections jointly.
- **Verdict:** **COVERS-ALL-O.** Setting is an arbitrary valued field; our `(K,v)` is a special
  case (complete ⇒ henselian ⇒ `K = K^h`, `φ = Q`).

### NS-2 — Ore order 1: theorem of the residual polynomial + leaf dichotomy with explicit `(e,f)`

- **Consumed as:** GMN Thm 1.19 + Cor 1.20 ("multiplicity-1 residual factor is an irreducible
  `p`-adic leaf with explicit `(e,f)`"); `docs/GMN_citations.md` §1, fact (III) at order 1; audit
  rows **Q1 W12-2**, **Q2 all four**, **Q6 W2-C1/C2**.
- **Source:** [GN15] **Theorem 2.3**, verbatim: *"Let $\mu$ be an inductive valuation equipped with
  a MacLane chain of length $r$ as in (1.1). Let $\phi\in\mathrm{KP}(\mu)$ such that
  $\phi\not\sim_\mu\phi_r$. Then, every monic polynomial $g\in O_v[x]$ factorizes into a product of
  monic polynomials in $O_v[x]$: $g=g_0\,\phi^{\mathrm{ord}_\phi(g)}\prod_{(\lambda,\psi)}
  g_{\lambda,\psi}$, where $-\lambda$ runs on the slopes of $N^-_{r+1}(g):=N^-_{v_r,\phi}(g)$ and
  $\psi$ runs on the prime factors of $R_{r+1,\lambda}(g):=R_{v_r,\phi,\lambda}(g)$ in
  $\mathbb F_{r+1}[y]$, where $\mathbb F_{r+1}:=\mathbb F_r[y]/(R_r(\phi))$. Moreover, $\deg
  g_0=\deg g-\ell(N^-_{r+1}(g))\deg\phi$, $\deg g_{\lambda,\psi}=e_\lambda\,
  \mathrm{ord}_\psi(R_{r+1,\lambda}(g))\deg\psi\deg\phi$, where $e_\lambda$ is the least positive
  denominator of $\lambda$. **Further, if $\mathrm{ord}_\psi(R_{r+1,\lambda}(g))=1$, then
  $g_{\lambda,\psi}$ is irreducible in $O_v[x]$.**"* — proved in place (5 lines, from their Thm 2.2
  = FGMN Thm 6.3).
- **Explicit `(e,f)`:** [GN15] eq. **(2.1)**: *"$e(F)=e(\mu_F)=e_0\cdots e_r,\quad
  f(F)=f_0\cdots f_r,\quad \delta_0(F)=w_{r+1}$."*
- **Alt:** [AGNPRW] §4.4 + **Proposition 4.5**: *"If in the factorization (8) we have $n_i=1$, then
  the pair $(\mu_\lambda,\varphi_i)$ singles out an irreducible factor of $g$ in $K^h[x]$."*
- **Verdict:** **COVERS-ALL-O.** [GN15] Thm 2.3 is stated for *any* monic `g ∈ O_v[x]` (no
  separability needed) over an arbitrary discrete valued field; it is simultaneously the order-1
  and the order-`r` statement, since `µ` ranges over all inductive valuations including `µ_0`.

### NS-3 — Higher-order OM: theorems of the polygon and of the residual polynomial in order `r`, leaf dichotomy

- **Consumed as:** GMN Thm 3.1, Thm 3.7, Cor 3.3, Cor 3.8; `BB3_infinity.md` §4, `L2core` §2,
  `W12_PROOF` (H-e), `GRTJB`/`GRTJC`, `JA-PIN`. Audit rows **Q1 W12-3**, **Q6 JA/W2/WELDMASTER**,
  **Q7 JB-VTX**.
- **Source:** identical to NS-1/NS-2 — [GN15] Thm 2.3 (any `r`, any MacLane chain length) and
  [AGNPRW] Thm 4.4 + §4.4 + Prop 4.5. Also [PW26] **Theorem 1** restates GMN Thm 3.1 and Thm 3.7
  *verbatim as items 1 and 2* over "a complete discrete valuation field … the two fields we have in
  mind are `ℚ_p` and `K((t))`", including *"3. (Irreducibility criterion) If $a_j=1$, then
  $F_{t,i,j}$ is irreducible."*
- **Verdict:** **COVERS-ALL-O** via [GN15]/[AGNPRW] (both refereed). [PW26] is a corroborating
  preprint only — its items 1–2 are *cited* to [GMN12] Thms 3.1/3.7 rather than reproved, so it is
  a widening-by-assertion, not an independent proof.

### NS-4 — Fact (I): the residue tower `F = F_0 ⊆ … ⊆ F_r` is a tower of **finite** fields with `[F_r:F] = f_0⋯f_{r-1}`

- **Consumed as:** `docs/GMN_citations.md` §0 fact (I) — the linchpin that lets L3/BB3's
  finite-field counts apply verbatim at every order; GMN §2.1 tower + Def 2.21.
- **Source:** [GN15] **Theorem 1.10**: *"The mapping $\mathbb F_r[y]\to\Delta$ determined by
  $y\mapsto y_r$ is an isomorphism of $\mathbb F_r$-algebras."* with the chain
  `F_{i+1} := F_i[y]/(ψ_i)` from §1.4, and eq. (2.1) `f(F) = f_0⋯f_r`. Equivalently [FGMN]
  **Theorem 4.8** (`docs/references/…_layout.txt` line 1136): *"The mapping $R_{r,0}:\Delta
  \longrightarrow \mathbb F_r[y]$ is an isomorphism of $\mathbb F_r$-algebras …"*.
  In [AGNPRW] language: **Theorem 2.7**, *"$\xi=\pi^e u^{-1}\in\Delta_\mu$ is transcendental over
  $k$ and satisfies $\Delta_\mu=\kappa[\xi]$"*, with `κ(µ)` = the relative algebraic closure of `k`
  in `k_µ`.
- **Finiteness** is then immediate and characteristic-free: each `F_{i+1}/F_i` is a finite
  (`deg ψ_i`) extension of the finite `F = F_q`. No source needs to say "finite" — it follows from
  `F` finite, which is our hypothesis, not theirs.
- **Verdict:** **COVERS-ALL-O.**

### NS-5 — Fact (II): the order-`r` Newton polygon is a lattice (principal) polygon

- **Consumed as:** GMN Def 1.1/Def 2.3; `BB3_infinity.md` §2 / L4 (cell volume a `q`-power).
- **Source:** [AGNPRW] §4.1–4.3 define `N^+_{µ,φ}(g)` as the principal part of the lower convex
  hull of `{(n, µ(a_n)) | 0 ≤ n ≤ ℓ}` over `Q × Γ_Q` (see the `NP(µ,φ,ℓ)` subroutine, verbatim:
  *"compute the first $\ell+1$ coefficients $a_0,\dots,a_\ell$ of the $\phi$-expansion of $g$;
  return lower convex hull of the set $\{(n,\mu(a_n))\mid 0\le n\le\ell\}$"*). [GN15] §1.3 does the
  same with `Γ(µ) = e(µ)^{-1}ℤ`, i.e. the polygon lives on the lattice
  `ℤ × (1/(e_1⋯e_{r-1}))ℤ` exactly as GMN Def 1.1.
- **Verdict:** **COVERS-ALL-O** — but note this is a *definition*, not a theorem: it transports by
  restatement, so the re-citation is cosmetic. Flagged as the cheapest row in the whole table.

### NS-6 — Descent trigger: the tower stops at order `r` iff every order-`r` residual is separable

- **Consumed as:** GMN **Lemma 3.11(3)**; `docs/GMN_citations.md` fact (III); the locus L3/BB3
  counts as `Q_r^{d_r-1}`. Audit rows **Q1 GMN-5**, **Q6**.
- **Source:** [GN15] **Theorem 2.3** supplies the ⇐ direction directly (mult-1 factor ⇒ irreducible
  leaf, so no further descent), and [GN15] §5's Montes-algorithm flow (step 12(b): "IF `ω_i = 1`
  THEN add the leaf") is the algorithmic form. [AGNPRW] **Proposition 4.5** is the same. The ⇒
  direction (a repeated residual factor genuinely forces a further level) is
  [AGNPRW] **Theorem 2.10** (`deg(Q) = m·e·deg R(Q)`, so a residual factor of multiplicity ≥ 2
  cannot be resolved at this level) plus the `liftµ,φ` operator.
- **Verdict:** **COVERS-ALL-O**, but as a *composite* — no single published lemma states the
  equivalence in Lemma 3.11's three-clause form at general scope. **PARTIAL** if the corpus wants a
  one-line cite of the biconditional. Re-proof cost: ~½ page assembling [GN15] Thm 2.3 + [AGNPRW]
  Thm 2.10 (see §3).

### NS-7 — Termination: the OM descent stops at finite order

- **Consumed as:** GMN **Thm 4.18 (theorem of the index) + Cor 4.19**; `L5fix` §6, `HUMAN_PROOF` §9
  L5fix(a)/(b), `docs/GMN_citations.md` fact (III) finiteness half. Audit rows **Q1 HUMAN-6**,
  **Q6**.
- **Source:** [AGNPRW] **Theorem 5.2**, verbatim: *"**If $v$ is discrete of rank-one, then the
  OM-algorithm terminates.**"* with the proof sketch: *"The proof of this theorem is based on the
  finiteness of the local index $\mathrm{ind}(g):=v((O_g:O_v[\theta]))\in\Gamma$, where $O_g$ is
  the integral closure of $O_v$ in the finite extension $L/K$. … The theorem follows from the fact
  that in all intermediate steps of the algorithm, including the refinement steps, there is a
  positive integer contributing to the total value of $\mathrm{ind}(g)$ [10, Thm. 4.8]."*
- **Corroborating published widening:** [GN15] §5, immediately after the Montes pseudocode,
  verbatim: *"The arguments of [5] show that the algorithm terminates and has the right output.
  **In that paper it was assumed that $K$ was a number field, but the arguments are valid for an
  arbitrary discrete valued field $(K,v)$.**"* ([5] = Guàrdia–Montes–Nart, *Higher Newton polygons
  in the computation of discriminants and prime ideal decomposition in number fields*, J. Théor.
  Nombres Bordeaux **23** (2011) 667–696.)
- **Verdict:** **COVERS-ALL-O** at the level of the *statement* (published, refereed, exactly our
  hypothesis class), with an honest caveat: the load-bearing index step is discharged inside
  [AGNPRW] by citation to [GMN12, Thm 4.8] and to Montes' thesis, both of which are stated at
  number-field / ℚ_p scope. Two independent author teams assert the widening in print. If the
  corpus wants a *proof* rather than an assertion at general scope, this is the **one row that is
  only PARTIAL**; see §3 for the internal fallback.

### NS-8 — Existence of the key polynomial / representative of a type with prescribed residual

- **Consumed as:** GMN **Thm 2.11 + Def 2.12**; `SIGMALAW_PROOF_2026-08-08.md` print anchor
  `Thm-`\`phir\` (= `\label{phir}`, `HigherNewton.tex` line 1257); `BB3_infinity.md` §4,
  `L2core` §2. Audit rows **Q6 SIGMALAW-2**, **Q6 W2**.
- **Source:** [AGNPRW] **Theorem 2.10** + the lift operator, verbatim: *"For a residually
  transcendental $\mu$, take $\phi\in\mathrm{KP}(\mu)$ of minimal degree $m$. A monic $Q\in K[x]$
  is a key polynomial for $\mu$ if and only if either $\deg(Q)=m$ and $Q\sim_\mu\phi$, or
  $\deg(Q)=me\deg(R(Q))$ and $R(Q)$ is irreducible in $\kappa[y]$."* followed by *"It is easy to
  design a lifting routine [23, Cor. 5.6] $\mathrm{lift}_{\mu,\phi}:\mathrm{Irr}(\kappa)
  \setminus\{y\}\longrightarrow \mathrm{KP}(\mu)$, $\psi\mapsto Q$, to construct
  $Q\in\mathrm{KP}(\mu)$ with a prefixed $R(Q)=\psi$."* ([23] = Nart, *Key polynomials over valued
  fields*, Publ. Mat. 64 (2020) 195–232.)
- **Alt (constructive, our normalization):** [GN15] **Theorem 3.5** — *"We may efficiently
  construct representatives of types."* — with Proposition 3.4 giving the construction and the
  explicit `deg φ = m_r e_r f_r`; and [FGMN] **Theorem 5.8** (`KP(µ)/∼ ↔ Max Δ`).
- **Verdict:** **COVERS-ALL-O.**

### NS-9 — Theorem of the product in order `r`

- **Consumed as:** GMN **Thm 2.26** (`N_r^-(fg)=N_r^-(f)+N_r^-(g)`, `R(fg)=R(f)R(g)`);
  `GRTJC_PROOF_2026-08-08.md` prints "For non-zero $g,h\in K[x]$, we have
  $S_\lambda(gh)=S_\lambda(g)+S_\lambda(h)$"; also `J-D0`, `W2`, and the `ord_t(gh)=ord_t(g)+ord_t(h)`
  multiplicativity everywhere. Audit rows **Q7 GRTJC**, **Q6 JD0-3**.
- **Source (two independent, both general):**
  - [FGMN] **Theorem 2.8** (layout line 546) and **Corollary 2.7** (line 525, verbatim):
    *"For non-zero $g,h\in K[x]$, we have $S_\lambda(gh)=S_\lambda(g)+S_\lambda(h)$."* — the exact
    sentence GRTJC prints, at FGMN's "field equipped with a discrete valuation" scope.
  - [AGNPRW] **Theorem 4.6**: *"For all $\phi\in\mathrm{KP}(\mu)$ and nonzero $g,h\in K[x]$, we
    have $N^+_{\mu,\phi}(gh)=N^+_{\mu,\phi}(g)+N^+_{\mu,\phi}(h)$."* with *"This result is proved in
    [22, Thm. 4.8] for $\mu$ an inductive valuation. However, the proof is valid in the general
    case."*; and **Corollary 2.9**: *"For all $g,h\in K[x]$ we have $R(gh)=R(g)R(h)$."*
- **Verdict:** **COVERS-ALL-O.** The GRTJC row is a *verbatim* re-cite: same sentence, wider scope.

### NS-10 — Graded-algebra / residual-ideal facts consumed by GRTJC

- **Consumed as:** GRTJC prints "Let $g\in K[x]$ be a non-zero polynomial … $\mathcal
  P_\alpha(\mu)/\mathcal P_\alpha^+(\mu)$ is a free $\Delta$-module of rank one." Audit row
  **Q7 GRTJC H6** — the audit's "only potentially mixed-characteristic-sensitive citation gap".
- **Source:** [FGMN] §4, layout line 1030, verbatim: *"In particular, $P_\alpha(\mu)/P_\alpha^+(\mu)
  =\varphi_r(\alpha)\Delta$ is a free $\Delta$-module of rank one."* — inside [FGMN]'s §1 standing
  setting ("Let $K$ be a field equipped with a discrete valuation $v$"). Companion:
  [FGMN] **Theorem 4.2** (line 1028), **Theorem 4.8** (line 1136).
- **Verdict:** **COVERS-ALL-O.** *The audit's flag was a pasting artefact, not a real gap:* the
  quotation omitted [FGMN]'s standing hypotheses, which are already the general ones. **No edit to
  the mathematics is needed — only re-paste the §1 setting sentence next to the quote.**

### NS-11 — GMN engine lemmas printed by GRTJB/JA (`shape`, `propertiesv`, `t(i)`, `rescoeff`)

- **Consumed as:** `GRTJB_PROOF_2026-08-08.md` "Classifier side = the GMN print
  `docs/references/HigherNewton.tex` … Lemma `shape` items 1–2 … Proposition `propertiesv` item 3";
  `SIGMALAW` "Def-`t(i)` + Def-`rescoeff`". Audit row **Q7 JB H6** (load-bearing in JB-VTX(a),(c),(d1)).
  Identified locally: `\label{shape}` = `HigherNewton.tex` line 1401 = GMN **Lemma 2.17**;
  `\label{propertiesv}` = line 1028 = GMN **Proposition 2.7**; `\label{phir}` = line 1257 =
  GMN **Theorem 2.11** (⇒ NS-8).
- **Source for `shape`:** [GN15] **Lemma 1.5** (*"For every non-zero polynomial $g\in K[x]$, we have
  $\ell(N^-_{\mu,\phi}(g))=\mathrm{ord}_{\mu,\phi}(g)$, where $\mathrm{ord}_{\mu,\phi}(g)$ denotes
  the largest integer $s$ such that $\phi^s\mid_\mu g$"*) **+ Corollary 1.14** (*"Let $\phi$ be a key
  polynomial for $\mu$ such that $\phi_r\nmid_\mu\phi$ and denote $\psi=R_r(\phi)$. Then,
  $\mathrm{ord}_\psi(R_r(g))=\mathrm{ord}_{\mu,\phi}(g)$ for any non-zero $g\in K[x]$."*) — jointly
  `shape` items 1–2 (`length of N^-_r(f) = ω_r(f)` with `ω_{i+1}(P) := ord_{ψ_i}(R_i(P))`).
  Equivalently [FGMN] **Lemma 2.2** + **Prop 5.14 / Cor 5.15**, and [AGNPRW] **Lemma 4.2**.
- **Source for `propertiesv` item 3** (the `v_r`-from-`φ`-development formula, GD23 flag **T-1**):
  [GN15] §1.2 defines the augmented valuation by exactly that formula — *"$\mu'(g)=
  \mathrm{Min}_{0\le s}\{\mu(a_s\phi^s)+s\nu\}$, where $\sum a_s\phi^s$ is the canonical
  $\phi$-expansion of $g$. We denote $\mu'=[\mu;\phi,\nu]$."* — i.e. at general scope the statement
  is the **definition** of `v_r`, which is strictly stronger than citing it as a proposition.
- **Source for `rescoeff` / `t(i)`:** [AGNPRW] §2.2 definition (3) of the residual coefficient
  `ζ_j = (ā_ℓ)^{-1}u^{j-d}ā_{ℓ_j} ∈ ∆*_µ = κ*` and `R(g)=ζ_0+ζ_1y+⋯+y^d ∈ κ[y]`; [GN15]
  **Theorem 1.9**.
- **Verdict:** **COVERS-ALL-O** for `shape` and `rescoeff`/`t(i)`; **COVERS-ALL-O (definitional)**
  for `propertiesv` item 3. Caveat: the general-scope sources use MacLane/graded-algebra
  normalizations (`µ` valued in `Γ_Q`, `R` monic-normalized) rather than GMN's integer-rescaled
  `v_r = e_{r-1}H_{r-1}∘S_{r-1}`; the re-cite therefore carries a **normalization-shear obligation**
  — exactly the one `GENTOW2_PROOF_2026-08-09.md` already discharges for the FGMN side
  ("NORMALIZATION SHEAR (the repo polygon = FGMN polygon, one affine map)"). Reuse that.

### NS-12 — FGMN inventory consumed by GENTOW2/GENTOW5 ([Q1]–[Q10])

- **Consumed as:** `GENTOW2_PROOF_2026-08-09.md` §S3 pins [Q1] Lemma 1.11, [Q2] Cor 1.13,
  [Q4] Prop 1.12/Thm 3.11, [Q6] Lemma 5.3, [Q8] Cor 4.7(1)+eq (14), [Q9] **Theorem 6.3**,
  [Q10] **Corollary 6.4**; plus Cor 5.4, Cor 5.6, Thm 5.8, Def 3.16. Audit rows **Q4 A2**
  ("FGMN's ambient scope is not quoted") and **Q4 B6**.
- **Source:** [FGMN] itself. §1 line 137 (quoted in §1 above) is the standing setting: *arbitrary*
  field with a discrete valuation. §6 opens (line 1433): *"In this section, we apply inductive
  valuations $\mu$ on $K(x)$ to polynomials in $K_v[x]$…"*, and **Definition 6.1**: *"Let
  $\mathcal P=\mathcal P(O_v)\subset O_v[x]$ be the set of all monic irreducible polynomials in
  $O_v[x]$. We say that an element in $\mathcal P$ is a prime polynomial with respect to $v$."*
  — **no separability restriction on `P`**, and the proof of **Lemma 6.2** explicitly says
  *"where $Z(F)$ is the multiset of roots of $F$ in $\overline{K}_v$, **with due count of
  multiplicities if $F$ is inseparable**."*
- **Verdict:** **COVERS-ALL-O**, and it resolves both sub-questions the audit could not settle from
  the pasted record: (a) arbitrary discretely valued fields — yes, including `F_q((t))`; (b)
  inseparable prime polynomials such as `x^p − t` — **yes, `P` contains them and FGMN handles them
  explicitly**. *The GENTOW2 flag is discharged by pasting FGMN §1 + Def 6.1 + Lemma 6.2's
  inseparability clause into the faithfulness record.* No mathematics changes.

### NS-13 — Single-factor lifting (Guàrdia–Nart–Pauli)

- **Consumed as:** **not consumed.** `rg` over `docs/` and `lean/notes/` finds SFL only in
  exploratory route notes (`M01-track-count_fable.md`, `M02-count-tie_fable.md`,
  `M05-exhaust_fable.md`, `M12-cl2-route_fable.md`), never in a live theorem chain. No audit row
  names it.
- **Source (if ever needed):** [GNP12], scope quoted in §1 — complete discretely valued field with
  **perfect** residue field. Finite residue fields are perfect, so it covers our `O`.
- **Verdict:** **COVERS-ALL-O (background, non-load-bearing).**

### NS-14 — Defectlessness: `Σ e_i f_i = [L:K]`, all defects 1

- **Consumed as:** `HUMAN_PROOF.md` §9 L5fix(c) — *"`K` is **defectless**: every finite separable
  `L/K` has `Σ e_i f_i = [L:K]`, all defects 1"* with the parenthetical *"complete discrete
  valuation ⇒ defectless (Ostrowski; Serre LF II.3; Neukirch ANT II.8.5)"*; `docs/AXIOM_FAITHFULNESS.md`
  entry **AX-DEFECT**. Audit row **Q1 HUMAN-7** (`CITE-SCOPE / overbroad as presented`).
- **Source:** [Kuhl] **Theorem 3.3**, verbatim: *"Let $(K,v)$ be a discretely valued field, that is,
  with value group $vK\simeq\mathbb Z$. **Then every finite separable extension is defectless.** If
  in addition $\operatorname{char}K=0$, then $(K,v)$ is a defectless field."* Supporting apparatus
  in the same document: the **Lemma of Ostrowski** (eq. 2.1) *"$[L':L]=p^\nu\cdot(vL':vL)\cdot
  [L'v:Lv]$ with $\nu\ge0$"*, and **Theorem 2.3** *"A valued field $(L,v)$ is a defectless field if
  and only if its henselization is."*
- **Verdict:** **COVERS-ALL-O** — and it **corrects the repo**. `AX-DEFECT`'s faithfulness note
  currently reads *"Equal-char-`p` Artin–Schreier defect towers correctly excluded by the mixed-char-0
  hypothesis"*, which mis-locates the obstruction: the defect obstruction is **non-discreteness**,
  not equal characteristic. For a discretely valued field, **every finite separable extension is
  defectless in every characteristic**, so `F_q((t))` is fine. (Only *inseparable* extensions need
  `char K = 0`; the corpus fences its uses to `disc ≠ 0`, i.e. separable, so nothing is lost.)
  Completeness then supplies `g = 1` and `ef = [L:K]` — standard, and not the flagged part.
  **Action: rewrite the AX-DEFECT hypothesis line and the HUMAN_PROOF §9 parenthetical to cite
  [Kuhl] Thm 3.3 with the separability fence made explicit.** Serre/Neukirch numbering remains
  **UNVERIFIED** (books not machine-read this session); with [Kuhl] pinned they are no longer
  load-bearing and can be demoted to "see also".

### NS-15 — Different bound for the depth envelope `B(n,p)`

- **Consumed as:** `HUMAN_PROOF.md` §9 L5fix(b), *"Serre LF III.6 Prop 13 (totally ramified
  separable degree-`e`: `e-1 ≤ d ≤ e-1+v_L(e)`, wild excess `v_L(e)=e·v_p(e)`)"*, giving
  `B(n,p) := max_{d≤n}[(d-1)+d·v_p(d)]`. Audit row **Q1 HUMAN-6**, classified
  **MIXED-CHAR-ONLY, substantive** (not merely CITE-SCOPE).
- **Verdict:** **NOT-FOUND as a re-citation fix, and it is not a citation problem.** In equal
  characteristic `v_p(d)` is not the right wildness measure (Serre's different bound is stated for a
  complete DVR with perfect residue field in both characteristics, so the *bound* transports; what
  fails is the corpus's use of `v_p(d)` — a mixed-characteristic quantity — as the depth envelope).
  The audit is right that a separate equal-characteristic termination/finite-menu argument is owed.
  **However** NS-7 ([AGNPRW] Thm 5.2) already gives termination at general discrete rank-one scope
  *without* a different bound, so the `B(n,p)` route is only needed if the corpus wants an *explicit*
  depth constant. See §3 for the two options.

---
## 3. Fallback column — internal re-proof estimates for the non-clean rows

Only three rows are not a pure bibliography swap. For each: size estimate, and which
corpus/`leanfinal` machinery a re-proof would reuse.

### F-1 (NS-6) — Lemma 3.11's biconditional at general scope · **~½ page, LOW risk**

*Missing:* a single published lemma saying "`t_{r+1}(f)=∅` ⟺ every order-`r` residual is
separable". *Have:* both directions separately at general scope.
*Re-proof:* (⇐) is [GN15] Thm 2.3's last clause (`ord_ψ = 1 ⟹ g_{λ,ψ}` irreducible), applied to
every `(λ,ψ)`. (⇒) is [AGNPRW] Thm 2.10's degree law `deg Q = m·e·deg R(Q)`: a residual factor `ψ`
with `ord_ψ(R) = a ≥ 2` gives `deg g_{λ,ψ} = e_λ·a·deg ψ·deg φ > e_λ·deg ψ·deg φ = deg(lift of ψ)`,
so the type is not `f`-complete and a level must be added.
*Reuses:* nothing new — this is exactly the "leaf vs descend" dichotomy already formalized on the
`OM/` side; the Lean-side consumer is `OM/Classifier` + `MontesV2`'s `descend`/`leaf` split.

### F-2 (NS-7) — termination proved (not asserted) at general scope · **~2–4 pages, MEDIUM risk**

*Missing:* [AGNPRW] Thm 5.2's statement is at exactly our scope, but its proof discharges the key
step by citing [GMN12, Thm 4.8] and Montes' thesis, both ℚ_p/global-field. So a reader who refuses
widening-by-assertion has a gap.
*Re-proof sketch:* define `ind(f) := length_O(O_L / O[θ])` for separable monic `f` over a complete
DVR with finite residue field — finite because `O_L` is a finite `O`-module (complete DVR,
`[L:K] < ∞`). Show each augmentation/refinement step of the OM flow consumes ≥ 1 from the index.
The lattice-point count `ind_i(f) = f_0⋯f_{i-1}·(#{integer points under `N_i(f)`})` is pure
`ℤ²`-combinatorics and is already characteristic-free in the corpus (`L4`/`BB1_exponent.md`); the
only genuinely arithmetic input is `ind(f) = Σ_i ind_i(f)` with equality iff `ind_{r+1}(f)=0`.
*Reuses:* `L4` lattice-volume machinery, `L5fix` §6's well-founded-descent skeleton (root budget +
discriminant budget), and `docs/references/HigherNewton.tex` §4 as the proof template (its §4
argument uses only `v(disc)`, `φ`-developments and lattice counts — I found no `v(p)`, Teichmüller,
Witt, or `char 0` step there, but **I did not line-by-line audit GMN §4 in this unit**, so that is a
claim about what a re-proof would have to check, not a verified claim).
*Cheaper alternative:* cite [AGNPRW] Thm 5.2 as-is and record the assertion-chain honestly in
`AXIOM_FAITHFULNESS.md` (this is what the corpus already does for other cited results).

### F-3 (NS-15) — equal-characteristic depth envelope · **~1–2 pages, MEDIUM risk; or delete the need**

*Missing:* `B(n,p) = max_{d≤n}[(d-1)+d·v_p(d)]` is a mixed-characteristic expression.
*Option A (delete the need):* the qualitative statement L6M4 actually consumes is "finite,
`p`-independent shape menu `T_n`". [AGNPRW] Thm 5.2 gives finiteness at general scope with no
explicit constant; `L5fix(b)`'s only other use of `B(n,p)` is the *explicit* depth constant, which
`docs/PROJECT_STATE.md` already records as gating nothing downstream. Cost: a statement edit
weakening `L5fix(b)` to "finite depth, bound `≤ (1/2)v(disc f)`" — which follows from F-2's index
argument and is uniform in characteristic.
*Option B (keep an explicit constant):* replace `v_p(d)` by the correct general wildness measure.
Serre's different bound `e−1 ≤ d_{L/K} ≤ e−1+v_L(e)` holds for any complete DVR with perfect residue
field in both characteristics; in equal characteristic `p`, `v_L(e) = e·v_p(e)` is still the right
formula because `e` is an *integer* and `v_L(e)` means the valuation of the integer `e` viewed in
`O_L` — which is `∞` when `p | e` and `char K = p`. **That is the actual breakage:** in equal
characteristic the naive different bound is vacuous, so Option B needs the Artin–Schreier–style
ramification-break bound instead, not a re-citation. Recommend **Option A**.
*Reuses:* `L5fix` §6, `L6M4`'s finite-menu interface, and the index bound from F-2.

---

## 4. Audit-row → resolution map (for the orchestrator)

| Audit row | Flagged text (abbrev.) | Needed statement | Resolution |
|---|---|---|---|
| Q1 W12-2 | "Ore's theorem … factors any `O`-lift `F`" | NS-1, NS-2 | re-cite [GN15] Thm 2.3 |
| Q1 W12-3 | "(H-e) … order-≥2 GMN LEAF/σ-DECISION theorem" | NS-3 | re-cite [GN15] Thm 2.3 / [AGNPRW] Thm 4.4 + Prop 4.5 |
| Q1 HUMAN-7 | "complete discrete valuation ⇒ defectless" | NS-14 | re-cite [Kuhl] Thm 3.3 + **fix AX-DEFECT's stated reason** |
| Q1 HUMAN-8, GMN-1/2/3 | "GMN works over an arbitrary complete DVF" (false) | NS-1..NS-9 | swap the base citation; keep [GMN12] as the ℚ_p-specialized reference |
| Q1 HUMAN-6 | `B(n,p)` depth envelope | NS-15 | **not a citation fix** — §3 F-3, Option A |
| Q2 (HMENU3/HEX3/GENIND/GENH4) | "Ore/GMN published theorem — no precise publication" | NS-1, NS-2 | re-cite [GN15] Thm 2.3 (all four notes, one edit each) |
| Q3 GENHN | bare "Ore order-1" supplier line | NS-1, NS-2 | re-cite, or downgrade to background if W-12.A supplies it |
| Q4 A2 / B6 (GENTOW2, GENTOW5) | "FGMN's ambient scope is not quoted" | NS-12 | **paste [FGMN] §1 + Def 6.1 + Lemma 6.2** into the faithfulness record; no math change |
| Q6 JA-PIN | `O ∈ {ℤ_p, F_p[[t]]}`, "print is mixed-characteristic" | NS-3, NS-8, NS-11 | widen the domain quantifier to all complete DVRs, citing [GN15]/[AGNPRW]; JA-BOX-4's equal-characteristic deferral **can be retired** |
| Q6 W2-C1/C2, WELDMASTER, JD0 | inherited from JA/W2/GMN | NS-3, NS-9 | inherited resolution — no independent work once JA-PIN is widened |
| Q6 SIGMALAW-2 | print evaluator + `Thm-`\`phir\` | NS-8, NS-11 | re-cite [AGNPRW] Thm 2.10 + `lift`, or [GN15] Thm 3.5 |
| Q7 JB-VTX | `shape` items 1–2, `propertiesv` item 3 | NS-11 | re-cite [GN15] Lem 1.5 + Cor 1.14 + §1.2 definition; carry the normalization shear |
| Q7 GRTJC | "free `Δ`-module of rank one", "`S_λ(gh)=S_λ(g)+S_λ(h)`" | NS-9, NS-10 | **pasting artefact** — the quoted sentences are [FGMN]'s, already general; re-paste with §1 |

## 5. Summary — cheapest complete resolution path, ranked

**Stage 1 (≈ one editing pass; resolves ~13 of the ~15 rows).** Add one bibliography block naming
[AGNPRW], [GN15], [FGMN], [BNS13]/[Nart14] with their standing-setting sentences quoted verbatim,
and retarget every `Ore/GMN` cite to it. Concretely, three substitutions cover almost everything:

1. **Order-1 and order-`r` polygon + residual + leaf dichotomy** (GMN Thms 1.15/1.19/3.1/3.7,
   Cors 1.20/3.3/3.8) → **[GN15] Theorem 2.3** (one theorem, all orders, any monic `g`, arbitrary
   discrete valued field, proof in place) with **[GN15] eq. (2.1)** for the `(e,f)` readout, and
   **[AGNPRW] Thm 4.4 + Prop 4.5** as the second, independent leg.
2. **Product theorem, graded algebra, residual operators, key-polynomial existence** (GMN Thms 2.26,
   2.11, Prop 2.7, Lem 2.17, Defs 2.5/2.21) → **[FGMN]** (already repo-local; scope is already
   general — this is a *quotation* fix, not a *source* fix) plus **[AGNPRW] Thms 2.7–2.10** and
   **[GN15] Thms 1.9–1.13, 3.5**.
3. **Defectlessness** → **[Kuhl] Thm 3.3**, with the separability fence made explicit and the
   AX-DEFECT reasoning corrected (the obstruction is non-discreteness, not equal characteristic).

**Stage 2 (≈ ½ page of new prose).** Write F-1 (NS-6, the descent-trigger biconditional) as a
two-line corollary of [GN15] Thm 2.3 + [AGNPRW] Thm 2.10, since no single published lemma states it.

**Stage 3 (choose one).** For termination (NS-7): either cite **[AGNPRW] Theorem 5.2** — published,
refereed, *exactly* our hypothesis class ("if `v` is discrete of rank-one, then the OM-algorithm
terminates") — and record in `AXIOM_FAITHFULNESS.md` that its key step is itself discharged by
citation to ℚ_p-scope sources; or spend F-2's 2–4 pages proving the index-descent internally on the
existing `L4` lattice machinery. **Recommended: cite, and record honestly.** Two independent author
teams ([AGNPRW] Thm 5.2; [GN15] §5's "the arguments are valid for an arbitrary discrete valued
field") assert the widening in print, and the corpus's own generality audit found no
characteristic-sensitive step in the argument.

**Stage 4 (statement edit, not a citation).** `L5fix(b)`'s explicit depth constant `B(n,p)` is
genuinely mixed-characteristic. Weaken to "finite depth, `≤ (1/2)v(disc f)`" (§3 F-3 Option A);
this is the only place where the equal-characteristic extension costs a *theorem*, not a *cite*.

**Net.** The `CITE-SCOPE` cluster is **not** a mathematical obstruction to the all-`O` capstone. It
is one bibliography swap (Stage 1), one half-page corollary (Stage 2), one honesty entry (Stage 3),
and one statement weakening in a place that gates nothing downstream (Stage 4).

---

## 6. What I could NOT verify

> **ITEMS 1 AND 2 RESOLVED — AUDIT A-3, 2026-08-16** (`docs/CITE_NUMBERING_AUDIT_2026-08-16.md`),
> and item 1 resolved **against** this doc: the AGNPRW numbers below are arXiv-v1 numbers that the
> published paper does not use. **Every AGNPRW number in this document must be remapped**:
> 2.7 → **2.14** · Cor 2.9 → **Cor 2.17** · 2.10 → **2.18** · 4.4 → **4.10** · 4.6 → **4.15** ·
> 4.7 → **4.16** · 4.8 → **4.17** · **5.2 → 5.6** · Prop 4.5 → **Prop 4.14** (and v1's Thm 5.1 is
> what now occupies **5.2**, so NS-7's cite currently mis-points at a real but different theorem).
> Correct reference: **Found. Comput. Math. 25 (2025), no. 2, 631–681**. NS-7's quoted proof sketch
> ends `[14, Thm. 4.8]` in print, not `[10, Thm. 4.8]`; and GMN12 has no *Theorem* 4.8 (it is a
> Lemma; the theorem of the index is **GMN Thm 4.18**), so that last link is imprecise in the source
> itself — say so rather than repeating it. **The [FGMN] numbering in this document (NS-9, NS-10,
> NS-12) drifted too** — see the audit's §4 map; in particular NS-12's scope pins move off numbered
> items (v3 "Def 6.1" → unnumbered published §6 opening prose; v3 "Lemma 6.2" → published **Lemma
> 6.1**, inseparability clause verbatim intact). Item 6 (ML36) and items 3–5, 7–8 remain open.

1. ~~**Publisher-side pagination/numbering** for [AGNPRW] (FoCM 2024)~~ — **RESOLVED (A-3): drift
   found, see the box above.** `link.springer.com` redirects
   to an auth endpoint. All theorem numbers (2.7, 2.9, 2.10, 4.4, 4.6, 4.7, 4.8, 5.2, Prop 4.5) are
   from **arXiv:2207.02139v1** — and arXiv has **only** v1, never updated. The two open surrogates
   named below turn out to be the **accepted version** (both compiled 2023-12-11), not copies of v1,
   and they carry the published renumbering:
   `iri.upc.edu/files/scidoc/2965-Polynomial-factorization-over-Henselian-fields.pdf` and
   `weimann.users.lmno.cnrs.fr/HenselianFactorization.pdf`.
2. ~~**[GN15] printed pagination.**~~ — **RESOLVED (A-3): VERIFIED, no drift.** Volume/pages
   (Contemp. Math. **637**, **207–241**) and DOI 10.1090/conm/637/12767 are now confirmed from the
   publisher (AMS's own CONM 637 table of contents) plus Crossref and zbMATH (Zbl 1396.11143); and
   the theorem numbers, previously known only from the `upcommons.upc.edu` author PDF (1.5, 1.9,
   1.10, 1.13, 1.14, 2.1, 2.2, 2.3, 3.5, eq. 2.1), are confirmed by a second, **post-referee**
   witness this doc did not know about: **arXiv:1309.4340v2** (2014-06-10, comments *"revised
   according to suggestions by a referee"*). Cite that arXiv version alongside the chapter.
3. **[Kuhl] venue.** The verbatim Theorem 3.3 is from the author's PDF (`DEFECT.pdf`, KGRC Vienna).
   Its publication as *The defect*, in **Valuation theory in interaction**, EMS Ser. Congr. Rep.
   (2014) 277–318, is **UNVERIFIED** — I did not fetch the EMS volume.
4. **Serre, *Local Fields* II.3 / III.6 Prop 13 and Neukirch *ANT* II.8.5.** Not machine-read;
   numbering remains at the "medium confidence" grade `AXIOM_FAITHFULNESS.md` already records.
   With [Kuhl] Thm 3.3 pinned, the Serre/Neukirch numbers are no longer load-bearing for NS-14.
5. **[GMN12] §4 (theorem of the index) characteristic-audit.** I did **not** read GMN §4 line by
   line. §3 F-2's claim that its argument is characteristic-free is a *plan*, not a verified fact.
6. **[ML36] TAMS pagination.** Read from D. Ford's re-typeset PDF; the §-numbering (Thm 4.2,
   Thm 12.1, …) is the standard one every citing paper uses, but original page numbers are not
   checkable from that copy. (Same caveat the repo's `LITUNIT_2026-08-01.md` already records.)
7. **[PW26]** (arXiv:2607.02153, 2 Jul 2026) is a **preprint**, cited only as corroboration; and its
   restatement of the two Ore theorems is a *citation* to [GMN12], not an independent proof.
8. I did not check whether [BNS13]/[Nart14]/[GMN11-IB] contain the *statements* we need (I verified
   only their standing settings and their restatements of the OM apparatus). They are listed as
   scope witnesses for "the OM machinery is routinely deployed over locally compact complete DVFs",
   not as primary sources for any NS row.
