# H2C design — statement currency for the slope-`h` deep-primary recentering

## 0. Verdict

There is a clean Lean-ready ring and lattice package, but it is **not** obtained by
putting a DVR instance on

\[
  O[X]/(X^{e}-z\pi^h).
\]

That order is generally not normal.  The correct DVR is an Eisenstein
normalization obtained from a positive Bézout identity

\[
  ah-be=1.
\]

Its uniformizer is \(\gamma=x^a/\pi^b\), and it has the explicit presentation

\[
  O'=O[\gamma]\simeq O[Y]/(Y^e-z^a\pi).
\]

This presentation makes the complete-DVR cascade almost entirely an instance of
IFCG39's landed \(h=1\) cascade.  The genuinely new elementary theorem is the
coordinate permutation/lattice induced by multiplication by \(h\) modulo \(e\).

There is, however, a second and essential distinction.  The ring embedding of the
old order into \(O'\) is not an isomorphism of its finite principal quotients.  A
count-preserving `cellTransport` exists only after a Bézout coordinate
normalization.  The assertion that the resulting normalized polynomial has the
correct factorization type is the actual OM theorem.  It should be a named
correspondence statement (and probably a cite), not hidden in the commutative
algebra of the normalization.

Thus the recommended package has two layers:

1. a Lean-core **normalization/coordinate/finite-transport layer**;
2. an explicit **slope Bézout factor-correspondence law**, from which the usual
   `DecidedAt` transport follows by the already-landed multiset bookkeeping.

The direct claim

\[
  \operatorname{AdjoinRoot}(X^e-z\pi^h)
  \simeq \text{a complete DVR}
\]

must not appear: it is false for \(h>1\).

## 1. Ambient data and conventions

Use the same base hypotheses as IFCG39/43:

- \(O\) is a commutative domain and a discrete valuation ring;
- \(O\) is complete for its maximal-ideal topology;
- its residue field is finite;
- \(\pi\in O\) is irreducible;
- \(2\le e\), \(2\le h<e\), and \(\gcd(h,e)=1\);
- \(z\in O^\times\).  In the actual API it is preferable to bind a unit
  \(u:O^\times\) and write \(z=(u:O)\), rather than repeatedly choose an inverse
  from a nonzero-residue hypothesis.

The campaign uses \(e'\); this note writes \(e\) to reduce clutter.  The
\(e=1\) integer-slope case should be a separate trivial branch, not forced through
the package below.

Choose natural numbers \(a,b\) satisfying

\[
  0<a<e,\qquad ah=be+1.
  \tag{B}
\]

Existence and uniqueness of \(a\) in \(\{1,\ldots,e-1\}\) follow from coprimality;
then \(b=(ah-1)/e\).  This positive orientation is preferable to a statement with
\(\pm1\), because it gives an integral Eisenstein generator without a second sign
branch.

Define

\[
\begin{aligned}
  \kappa_{h,z}(X)&=X^e-z\pi^h,\\
  \varepsilon_{a,z}(Y)&=Y^e-z^a\pi,\\
  A&=\operatorname{AdjoinRoot}(\kappa_{h,z}),\\
  O'&=\operatorname{AdjoinRoot}(\varepsilon_{a,z}),\\
  \gamma&=\operatorname{root}(\varepsilon_{a,z}),\\
  \xi&=z^{-b}\gamma^h\in O'.
\end{aligned}
\]

For compatibility with IFCG39, observe that
\(\varepsilon_{a,z}=\operatorname{eisKey}(\pi,-z^a,e)\).

## 2. Ring-presentation statement family

### 2.1 Bézout arithmetic

The first small structure should package \((a,b)\) and (B).  The following facts
should be separate simp-facing lemmas:

\[
  \gamma^e=z^a\pi,qquad
  \xi^e=z\pi^h,qquad
  \xi^a=\pi^b\gamma.
  \tag{R}
\]

All three are direct exponent arithmetic from (B).  They are the anti-drift pins
for signs, powers of the centre, and the orientation of Bézout.

### 2.2 The order embedding and normalization

There should be a ring homomorphism

\[
  \iota_{h,z}:A\longrightarrow O'
\]

characterized by \(\iota_{h,z}(x)=\xi\), where \(x\) is the root of
\(\kappa_{h,z}\).  Its well-definedness is exactly \(\xi^e=z\pi^h\).

The principal structural theorem should state all of the following, preferably as
separate projections/lemmas rather than one large conjunction.

- `bezout_orderEmbedding_injective`: \(\iota_{h,z}\) is injective.
- `bezout_fractionField_eq`: after passing to fraction fields it is an
  equivalence; concretely \(\gamma=\xi^a/\pi^b\).
- `bezout_isIntegralClosure`: \(O'\), with the above embedding of \(A\), is
  the integral closure of \(A\) in their common fraction field.
- `bezout_recentring_stack`: \(O'\) is a domain, local ring, complete DVR,
  and has finite residue field; its maximal ideal is \((\gamma)\), its residue
  cardinality is that of \(O\), and

  \[
    (\mathfrak m_O^N)O'=\mathfrak m_{O'}^{eN}.
  \]

- `bezout_root_irreducible`: \(\gamma\) is irreducible in \(O'\).
- `bezout_values`: with the base valuation normalized by
  \(v_O(\pi)=1\), the extended field valuation satisfies
  \(v(\gamma)=1/e\), \(v(\xi)=h/e\), and has value group
  \((1/e)\mathbf Z\).

Proof sketch.  The polynomial \(Y^e-z^a\pi\) is exactly an IFCG39 Eisenstein key,
so the complete-DVR, maximal-ideal, residue-cardinality, and ramification claims
are landed results after changing the unit parameter.  For injectivity, use the
coordinate calculation in §3: the residues \(hi\bmod e\), for \(0\le i<e\), are a
permutation, so a degree-\(<e\) relation among the powers of \(\xi\) becomes a
relation among the power basis \(1,\gamma,\ldots,\gamma^{e-1}\).  Equality of
fraction fields follows from (R).  Since \(A\) is finite integral over \(O\), an
element integral over \(A\) is integral over \(O\); since the DVR \(O'\) is
integrally closed, this proves the normalization statement.  No general theorem
about finiteness of normalization is needed.

The corresponding assertions with \(A\) in place of \(O'\)—local DVR, principal
maximal ideal, or complete DVR—must be explicitly absent.

## 3. Coordinate lattice

For \(0\le i<e\), put

\[
  q_i=\lfloor hi/e\rfloor,qquad r_i=hi\bmod e,qquad
  \delta_i=z^{a q_i-bi}\in O^\times.
\]

Then

\[
  \xi^i=\delta_i\pi^{q_i}\gamma^{r_i},
  \tag{C1}
\]

and \(i\mapsto r_i\) is a permutation of \(\{0,ldots,e-1\}\).

For naturals \(w,s\), write

\[
  \operatorname{cceil}_e(w,s)=
  \frac{w+e-1-s}{e}
\]

with natural-number subtraction.  This is
\(\max(0,\lceil(w-s)/e\rceil)\).

### 3.1 Raw-order lattice

The exact analogue of `eis_root_pow_dvd_mk_iff` is:

> **`bezout_root_pow_dvd_orderMk_iff`.**  If
> \(P=\sum_{i<e}p_iX^i\) has degree \(<e\), then
> \[
>   \gamma^w\mid \iota_{h,z}(\operatorname{mk}_{\kappa}P)
>   \quad\Longleftrightarrow\quad
>   \forall i<e,\ 
>   \pi^{\operatorname{cceil}_e(w,hi)}\mid p_i.
>   \tag{L-raw}
> \]

Proof sketch.  Substitute (C1).  Distinct \(i\)'s occupy distinct
\(\gamma\)-power coordinates because the \(r_i\)'s are a permutation.  In the
\(i\)-coordinate, divisibility by \(\gamma^w\) is exactly
\(e(v_\pi(p_i)+q_i)+r_i\ge w\), equivalently
\(ev_\pi(p_i)+hi\ge w\), which is (L-raw).  Units \(\delta_i\) do not affect
divisibility.

This theorem is instance-light in the same sense as IFCG39's lattice theorem: it
needs the DVR structure on \(O\), the Eisenstein root relation, and the unit
hypothesis, but not completeness or finiteness of the residue field.

### 3.2 Normalized coordinate equivalence

Define the **Bézout coordinate normalization** on degree-\(<e\) representatives by

\[
  \Theta_{h,z}\!\left(\sum_{i<e}p_iX^i\right)
    =\sum_{i<e}p_i\delta_i\gamma^{r_i}.
  \tag{C2}
\]

This is an \(O\)-linear equivalence from the rank-\(e\) coordinate module of the
order to \(O'\).  It is deliberately **not** claimed to be a ring homomorphism.
Its lattice theorem is

\[
  \gamma^w\mid\Theta_{h,z}(P)
  \quad\Longleftrightarrow\quad
  \forall i<e,\ 
  \pi^{\operatorname{cceil}_e(w,r_i)}\mid p_i.
  \tag{L-norm}
\]

The crucial level-exact specialization is

\[
  \gamma^{eN}\mid\Theta_{h,z}(P)
  \quad\Longleftrightarrow\quad
  \forall i<e,\ \pi^N\mid p_i.
  \tag{L-level}
\]

Thus \(\Theta_{h,z}\), rather than the ring embedding \(\iota_{h,z}\), is what
can support a bijection of the ordinary finite coefficient boxes.

### 3.3 The mandatory negative lemma

The API should record the obstruction, at least in documentation and preferably by
a concrete theorem/example at \((h,e)=(2,3)\): the map induced by
\(\iota_{h,z}\)

\[
  A/\pi^N A\longrightarrow O'/\gamma^{eN}O'

\]

is generally not injective.  For example, when \(x=\gamma^2\), the class of
\(\pi^{N-1}x^2\) can be nonzero modulo \(\pi^N A\) while its image is zero modulo
\(\gamma^{3N}\).  This prevents an accidental reintroduction of the false
`h=1` proof.

## 4. The normalized development and finite cell transport

Let \(f\) be monic of degree \(ek\), and write its \(\kappa_{h,z}\)-adic
development as

\[
  f=\sum_{t=0}^{k} A_t\kappa_{h,z}^{,t},
  \qquad \deg A_t<e,qquad A_k=1.

\]

Define

\[
  \operatorname{bezDevT}_{h,z,k}(f)
    =\sum_{t=0}^{k}\Theta_{h,z}(A_t)T^t\in O'[T].
  \tag{D}
\]

The inverse operation applies \(\Theta_{h,z}^{-1}\) coefficientwise and then uses
the generic `reassT` formula with key \(\kappa_{h,z}\).  Call it
`bezReassT`.

The elementary development family should contain:

- `bezDevT_coeff`;
- `bezDevT_monic` and its degree statement;
- `bezDevT_bezReassT` and `bezReassT_bezDevT`;
- `bezReassT_monic` and its degree statement;
- outbound and inbound level exactness using (L-level).

These yield the exact finite equivalence

\[
  \operatorname{bezCellTransport}_{h,z}:
  \operatorname{Coeff}(O,ek,N)
  \simeq
  \operatorname{Coeff}(O',k,eN).
  \tag{T}
\]

It must have the same three interface theorems as IFCG43:

- `bezCellTransport_apply` computes (T) on any lift by `bezDevT`;
- `bezCellTransport_symm_apply` computes its inverse by
  `bezReassT`;
- `bezCellTransport_card_image` preserves the cardinality of every set.

Also retain the unchanged normalization identity

\[
  \#\operatorname{Coeff}(O',k,eN)=q^{keN}=q^{(ek)N}.

\]

Proof sketch.  Euclidean development and reassembly are the generic IFCG39 §4
arguments.  Replace each use of the quotient `AdjoinRoot.mk` by
\(\Theta_{h,z}\), use its linear inverse for reassembly, and use (L-level) for the
two congruence lemmas.  No factorization theorem is used here.

## 5. The deep box and residual transfer

For a target coefficient

\[
  B_t=\Theta_{h,z}\!\left(\sum_{i<e}p_{t,i}X^i\right),

\]

define the slope-`h` deep condition at slot \(t<k\) by

\[
  \pi^{\lambda_{t,i}}\mid p_{t,i}\quad(i<e),
  \qquad
  \lambda_{t,i}=
  \operatorname{cceil}_e\bigl(eh(k-t)+1,hi\bigr).
  \tag{A}
\]

Equivalently, after restoring the omitted carry factors \(\pi^{q_i}\), the raw
order coefficient is divisible by \(\gamma^{eh(k-t)+1}\).  Let
`bezoutAlphaBox` be the subset of
\(`Coeff`(O',k,eN)\) satisfying (A) at every \(t<k\).  The usual depth
hypothesis should ensure \(\lambda_{t,i}\le N\), so membership is independent of
the chosen representatives.

The desired transfer statement is:

> **`resPoly_eq_pow_iff_bezoutBox`.**  Under the full-span side pins at
> slope \(h/e\), with centre \(\bar z\),
> \[
>   \operatorname{resPoly}(f)=(X-\bar z)^k
>   \quad\Longleftrightarrow\quad
>   \operatorname{bezCellTransport}_{h,z}([f])
>     \in\operatorname{bezoutAlphaBox}(h,e,k,N,z).
>   \tag{RB}
> \]

This is a **new proof obligation**, not verbatim IFCG43.  Its proof should replay
the C110 binomial shift with \(\pi^{h(s-t)}\) in place of
\(\pi^{s-t}\).  All terms in the relevant sum then have common height
\(h(k-t)\); the same binomial-vanishing identity removes the lower combinations.
The final conversion between raw root divisibility and normalized coordinates is
(L-raw).  IFCG44's landed `xres_eq_pow_iff_digits_h` supplies the residual side
of (RB).  What remains to be checked in Lean is the generalized exponent arithmetic
and the compatibility of the chosen unit factors \(\delta_i\); this is not a
literature gap.

The exact box count should also be stated:

\[
  \#\operatorname{bezoutAlphaBox}
   =q^{ekN-\sum_{t<k}\sum_{i<e}\lambda_{t,i}}.
  \tag{Count}
\]

The exponent identity

\[
  \sum_{t<k}\sum_{i<e}\lambda_{t,i}
  =
  \sum_{j<ek}\left\lceil\frac{h(ek-j)}e\right\rceil+k

\]

should be a separate arithmetic lemma.  It identifies (Count) exactly with
IFCG64's `card_slopeBox`; it is a useful hostile test of all `+1` and carry
conventions.

## 6. The OM/decision statement: exact form

### 6.1 The correspondence surface

The pointwise statement should parallel IFCG48's `FactorCorrespondenceAt`, not
be bundled into the ring construction.  At depth \(k\), define
`SlopeBezoutFactorCorrespondenceAt(h,k)` to assert, uniformly in all ambient
data above, that a monic \(g\in O[X]\) of degree \(ek\) satisfying

- the slope lattice
  \(\pi^{\lceil h(ek-j)/e\rceil}\mid g_j\) for \(j<ek\), and
- the Bézout deep-box condition (A) on its normalized development,

has a multiset relation

\[
  \operatorname{monicFactors}(g)
  \mathrel{\operatorname{Rel}}
  \operatorname{monicFactors}(\operatorname{bezDevT}_{h,z,k}(g))

\]

in which matched factors \((g_0,G_0)\) satisfy

\[
  \operatorname{inertiaDegOf}(g_0)=\operatorname{inertiaDegOf}(G_0),
  \qquad
  \deg g_0=e\deg G_0.
  \tag{FC}
\]

The already-landed `typeOf_eq_scaleType_of_rel` reduction then gives

\[
  \operatorname{typeOf}(g)
  =\operatorname{scaleType}(e,
       \operatorname{typeOf}(\operatorname{bezDevT}_{h,z,k}(g))).
  \tag{TS}
\]

No new `(e,f)` bookkeeping is required.

### 6.2 Decision transport

Assuming (FC), the exact cell theorem is the literal analogue of IFCG47:

> **`bezCellTransport_decidedAt_iff`.**  If a base class has minimal face
> \((h,e)\), satisfies the full-span pins, and its transported class lies in
> `bezoutAlphaBox`, then for every \(\sigma'\),
> \[
> \begin{aligned}
> &\operatorname{DecidedAt}
>   (O',k,\sigma',eN,
>      \operatorname{bezCellTransport}_{h,z}(c))\\
> &\hspace{35mm}\Longleftrightarrow
> \operatorname{DecidedAt}
>   (O,ek,\operatorname{scaleType}(e,\sigma'),N,c).
> \end{aligned}
> \tag{DT}
> \]

The proof from (TS), the two computation lemmas for transport, and injectivity of
`scaleType` is verbatim IFCG47/48.  In particular, the target of (DT) is the
ordinary `DecidedAt` over the complete DVR \(O'\); no new weakened decision
predicate should be introduced.

### 6.3 Why the normalization in (D) is part of the cite surface

The raw ring embedding sends

\[
  \sum p_i x^i\longmapsto
  \sum p_i\delta_i\pi^{q_i}\gamma^{r_i},

\]

whereas `bezDevT` uses the same expression with the carry factors
\(\pi^{q_i}\) removed.  Removing those factors is an \(O\)-linear coordinate
normalization, not a ring map.  Consequently, (FC) does not follow formally from
factorization after scalar extension.  A cite or proof must identify this exact
normalized transform with the source's MacLane/OM residual transform.  This is the
one place where a seemingly harmless definition can make the theorem false.

## 7. Reuse audit: IFCG39 §§3–5

| Landed \(h=1\) item | Status for \(h\ge2\) | Required change or argument |
|---|---|---|
| `eisKey`, `eisKey_monic`, `eisKey_natDegree` | Verbatim on the normalized key | Instantiate at \(-z^a\); the polynomial is \(Y^e-z^a\pi\). |
| `eisKey_eq_xKey` | New normalization identity | The old equality concerns the slope-\(1/e\) key.  Separately identify \(\kappa_{h,z}\) with the linear-residual `xKey` at slope \(h/e\). |
| `eisKey_irreducible` | Verbatim for \(\varepsilon_{a,z}\) | This proves irreducibility of the normalized Eisenstein key.  Irreducibility of \(\kappa_{h,z}\) needs the coordinate injection/Newton polygon argument; do not transfer a DVR instance to its quotient. |
| `eis_root_pow` | Verbatim plus new Bézout identities | Gives \(\gamma^e=z^a\pi\); derive all identities (R) arithmetically. |
| reduction-at-root map, kernel, maximality | Verbatim for \(O'\) | Replace the unit by \(-z^a\).  The analogous assertion for the root \(x\) in \(A\) is false as a DVR statement. |
| `eis_mk_X_pow` and the power-basis uniqueness kit | Verbatim for \(\gamma\) | Used after permuting exponents by \(i\mapsto hi\bmod e\). |
| `eis_root_pow_dvd_mk_iff` | Verbatim only for normalized power-basis coordinates | (L-raw) and (L-norm) are new corollaries requiring the modular permutation and carry calculation. |
| `eis_isDomain`, `eis_isLocalRing`, `eis_maximalIdeal_eq`, `eis_isDVR` | Verbatim for \(O'\) | Never instantiate them on \(A\). |
| `eis_map_pow_maximalIdeal`, `eis_isAdicComplete`, residue-field equivalence, `eis_residueCard` | Verbatim for \(O'\) | These supply the legal induction ring and preserve the base \(q\). |
| generic `devT`/`reassT` definitions and coefficient formulas | Algebraically verbatim for the monic key \(\kappa_{h,z}\) | Their coefficients initially live in the order \(A\).  The target-DVR transform must postcompose each coefficient with \(\Theta_{h,z}\). |
| `devT_monic`, `devT_reassT`, `reassT_devT`, `reassT_monic` | Proof skeleton verbatim | Insert \(\Theta\) and \(\Theta^{-1}\) coefficientwise; monicity is preserved because \(\Theta(1)=1\). |
| `devT_sub_root_pow_dvd` (outbound level exactness) | New short proof | Use generic development congruence plus (L-level), giving \(\gamma^{eN}\) on normalized coefficients. |
| `reassT_sub_pi_pow_dvd` (inbound level exactness) | New short proof | Use \(\Theta^{-1}\) and the reverse direction of (L-level). |
| The same two level lemmas with the **raw order embedding** in place of \(\Theta\) | False in both-direction/equivalence form | Outbound divisibility survives, but inbound exactness fails because of the conductor/carry factors. |
| IFCG43 `devVec`/`reassVec` and round trips | Proof skeleton verbatim | Replace them by their Bézout-normalized versions. |
| IFCG43 `cellTransport`, apply/symm/card-image, `card_coeff_eis` | Verbatim after the two new level lemmas | The target remains `Coeff O' k (e*N)` and the residue-cardinality proof is unchanged. |
| IFCG43 binomial shift and vanishing package | Combinatorics verbatim; valuation arithmetic new | Replace each shift power \(\pi^{s-t}\) by \(\pi^{h(s-t)}\); finish with (L-raw)/(A). |
| IFCG43 `resPoly_eq_pow_iff_box` | New theorem (RB) | Consume IFCG44's `xres_eq_pow_iff_digits_h` and the generalized binomial/lattice bridge. |
| IFCG47/48 multiset-to-`typeOf` and decision-transport reductions | Verbatim once (FC) is supplied | Only the correspondence theorem is new mathematics. |

## 8. Faithfulness and citation boundary

The complete-DVR and coordinate claims should be proved, not cited.  They reduce to
the landed Eisenstein cascade plus elementary Bézout and basis arithmetic.

The residual/box equivalence (RB) should also be proved in Lean.  Its mechanism is
already present in IFCG43 and IFCG44; citing it would obscure sign and carry errors
that the coordinate theorem is meant to expose.

The clean citation surface is exactly
`SlopeBezoutFactorCorrespondenceAt`.  A future extension of
`FGMNCitePackage` could add a fourth leg of that type, but only after the
following dictionary is print-checked against the source:

- the source's chosen normalizer for height \(hi/e\) must give precisely the
  \(q_i,r_i,\delta_i\) formula (C2), including the unit \(z^{a q_i-bi}\);
- its transformed polynomial must be the monic polynomial (D), not the raw scalar
  extension through \(\iota_{h,z}\);
- the theorem must match irreducible factors with multiplicity, not merely give
  residual degrees or a first-order residual dissection;
- its ramification and inertia conclusions must imply exactly (FC).

FGMN Theorem 6.4 is plausibly the right mathematical source genre, but CP2's
current legs do **not** certify this dictionary.  Leg E is the \(h=1\) case, where
all \(q_i=0\) and the distinction between raw and normalized coordinates
disappears.  Leg R decides squarefree residual blocks and does not supply the
deep-primary iteration.  Therefore citing the existing package for (FC) would be
unfaithful.

If source verification does not expose the exact normalized transform, leave (FC)
as an explicit hypothesis rather than weakening (DT) or replacing ordinary
`DecidedAt` by a custom predicate.

## 9. Recommended landing order

1. Bézout data and identities (R).
2. The normalized Eisenstein stack for \(O'\), the order embedding, and the
   normalization theorem.
3. The permutation/carry lemmas and (L-raw), (L-norm), (L-level).
4. `bezDevT`/`bezReassT` and the finite equivalence (T).
5. `bezoutAlphaBox`, (RB), (Count), and the exponent identity against
   `card_slopeBox`.
6. Stage `SlopeBezoutFactorCorrespondenceAt` without asserting it; derive
   (TS) and (DT) conditionally in Lean.
7. Only after a source-level dictionary audit, decide whether to sign the
   correspondence as a new FGMN package leg.

This order keeps every structural theorem Lean-core, makes the non-DVR obstruction
visible in the API, and isolates the sole literature-grade claim needed by the
slope-\(h\) decision transport.
