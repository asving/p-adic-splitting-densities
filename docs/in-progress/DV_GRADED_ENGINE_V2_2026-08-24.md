# THE DV-GRADED ENGINE, v2 — floor calculus, conversion, and the exact half

**Date:** 2026-08-24.  **Deliverable:** mathematics and Lean blueprint only.  **Nothing in this
document is signed or landed.**  This document supersedes
`DV_GRADED_ENGINE_2026-08-20.md`.

## 0. Verdict and status discipline

The adversarial review was right to split the work into three layers.

1. The **floor engine** is a two-index coefficient-weight calculus plus monic division and a
   branch census.  It proves lower bounds only.
2. The **conversion module** identifies that weight with the landed `dvHgt`/`dvSupp`/`dv2Hgt`
   definitions.  It is load-bearing for C.72 and for C.52's `DvAbove` goal.
3. The **exact half** proves purity and normalized residual identities.  These do not follow
   from lower bounds.

The exact-half literature question has a positive answer.  In the published version of
Fernández--Guàrdia--Montes--Nart, *Residual ideals of MacLane valuations*, J. Algebra 427
(2015), 30--75, DOI [10.1016/j.jalgebra.2014.12.022](https://doi.org/10.1016/j.jalgebra.2014.12.022),
Theorem 2.8 gives principal-Newton-polygon additivity and Corollary 4.12(3) gives the exact
normalized identity `R_r(gh)=R_r(g)R_r(h)`.  The accessible post-referee author version prints
both statements with the published numbering
([author PDF](https://upcommons.upc.edu/bitstream/handle/2117/28203/ResidualIdealsArxiv.pdf)).
The recommendation is therefore **CITE**, at gate (b), subject to owner secondary review of the
normalization dictionary in §4.4.  Until that review and signature, every exact-half conclusion
below is **OPEN**.

The words **PROVED**, **PROOF BLUEPRINT**, and **OPEN** have literal force below:

* **PROVED** means a complete paper proof is given here or a landed theorem with a matching
  statement is named.
* **PROOF BLUEPRINT** means all intermediate statements and proof moves are named, but no Lean
  declaration is claimed.
* **OPEN** means neither of the preceding statuses applies.  Unproved transitions are marked
  rather than hidden behind an adjective.

### 0.1 Notation

Fix `F : KeyFrame O π`, a pin `hpin : F.Pin H₀`, and
`T : TowerDatum F H₀ hpin`.  Put

\[
D'=e_1f_1,\qquad q=e_2f_2,\qquad D_2=D'q,\qquad
E_2=qu_2,\qquad \delta=u_2-e_2D'h.
\]

Here `δ` is honest natural subtraction: `T.hfloor` gives `e₂D'h < u₂`, hence landed
`T.one_le_margin` gives `1 ≤ δ`.  We write `ℕ∞` for Lean's `ENat`/`ℕ∞`; `⊤` is the value of a
zero coefficient.  Multiplication of an `ℕ∞` value by a natural number is written as scalar
multiplication when matching Lean.

Let `R := Polynomial (Polynomial O)`, with the outer variable denoted `Y` and the inner one
denoted `x`.  For `P : R`, `P.coeff b : Polynomial O`, and
`(P.coeff b).coeff a : O`.

## 1. Disposition of all thirteen review findings

| finding | disposition in v2 |
|---|---|
| **#1 CRITICAL** | §2.1 defines a well-typed weight with outer index `b` and inner index `a`. |
| **#2** | §2.2 proves the product inequality through both convolution sums, using `addVal_add` and `addVal_mul`; it is not called support arithmetic alone. |
| **#3** | §2.3 states and proves the `F.hpure`-to-all-coefficients bridge. |
| **#4** | §2.4 distinguishes public pins from private helpers and gives the required export list. |
| **#5** | §2.5 states and proves separate quotient-side and remainder-side bounds before iterating them. |
| **#6 CRITICAL** | §2.6 replaces rewriting by structural recursion on quotient depth and finite reconstruction ranges.  Termination is structural, not measured by an arithmetic expression. |
| **#7** | §2.7 records `j' ≤ j ≤ μ₂`, `1 ≤ k`, and all no-truncation lemmas explicitly. |
| **#8 CRITICAL** | §3.8 derives the actual C.72 `dv2Hgt` statement; no `WT` statement is identified with it before conversion. |
| **#9** | §3 gives the complete named flattening chain down to `dev`, `npHgt`, `suppVal`, `stageHeight`, `dvHgt`, `dvSupp`, and `dv2Hgt`. |
| **#10** | §3.7 is the separate all-coefficient/`DvAbove` bridge used by C.52. |
| **#11 CRITICAL** | §4 supplies the second, exact engine and a gate-(b) cite candidate; floor results are never used to infer purity or residual equality. |
| **#12** | §3.9 adds height exactness and residue stability below the discrepancy floor, with C.72's finite-height/drain guard retained. |
| **#13** | §6 states the exact finite scope of `verification/dv_ledger_cert.py`; it is evidence, not a proof of the universal statements. |

## 2. The repaired floor engine

### 2.1 The two-index weight

For `c : O` and `a b : ℕ`, define

\[
w_T(c,a,b)=(e_1e_2)\,\operatorname{addVal}(c)+a(e_2h)+bu_2\in\mathbb N_\infty.
\]

For `P : Polynomial (Polynomial O)`, define

\[
\operatorname{WT}_T(P)=
 \inf_{b\in P.\mathrm{support}}
 \inf_{a\in(P.\mathrm{coeff}\ b).\mathrm{support}}
 w_T((P.\mathrm{coeff}\ b).\mathrm{coeff}\ a,a,b).
\tag{WT}
\]

Both infima are finite `Finset.inf`s in `ℕ∞`; an empty infimum is `⊤`.  Thus `WT 0 = ⊤`.
This is well typed because the outer coefficient is first indexed by `b`, producing a
`Polynomial O`, and only the second index `a` produces an element of `O` for `addVal`.

Lean-facing definition sketch:

```lean
noncomputable def wtCoeff (T : TowerDatum F H₀ hpin) (c : O) (a b : ℕ) : ℕ∞ :=
  (F.e₁ * T.e₂) • addVal O c + ((a * (T.e₂ * F.h) + b * T.u₂ : ℕ) : ℕ∞)

noncomputable def WT (T : TowerDatum F H₀ hpin)
    (P : Polynomial (Polynomial O)) : ℕ∞ :=
  P.support.inf fun b =>
    (P.coeff b).support.inf fun a => wtCoeff T ((P.coeff b).coeff a) a b
```

The exact parenthesization of the natural term is to be frozen by a `ring` lemma before this
definition is consumed.

### 2.2 Addition and multiplication

**Lemma F1 (`WT_add`).** `min (WT P) (WT Q) ≤ WT (P+Q)`.

**Proof.** Fix `b,a`.  The scalar coefficient of `x^aY^b` in `P+Q` is the sum of the two
scalar coefficients.  `addVal_add` gives
`min (addVal p) (addVal q) ≤ addVal (p+q)`.  Natural offsets are the same on both terms, so
adding the offset preserves the inequality.  Taking the inner and outer finite infima proves
the claim.  If a coefficient cancels, its valuation increases, which is in the asserted
direction.  Zero coefficients contribute `⊤`.  **Status: PROVED.**

**Lemma F2 (`wtCoeff_mul`).**
`w_T(c d,a+a',b+b') = w_T(c,a,b)+w_T(d,a',b')`.

**Proof.** `addVal_mul` gives `addVal(cd)=addVal(c)+addVal(d)`.  Distribute the positive natural
scalar and use the two natural identities for the `a`- and `b`-offsets.  **Status: PROVED.**

**Lemma F3 (`WT_mul`).** `WT P + WT Q ≤ WT (P*Q)`.

**Proof.** This is a two-convolution proof.

1. The outer coefficient is
   `(P*Q).coeff b = Σ_{b₁+b₂=b} P.coeff b₁ * Q.coeff b₂`.
2. Its inner coefficient at `a` is the finite sum over both constraints
   `b₁+b₂=b`, `a₁+a₂=a` of
   `(P.coeff b₁).coeff a₁ * (Q.coeff b₂).coeff a₂`.
3. Repeated `addVal_add` bounds the valuation of that finite sum below by the infimum of the
   summands' valuations.  `addVal_mul` and F2 identify every summand's total weight with the sum
   of its two input weights.
4. Each input weight is at least the corresponding `WT`; therefore every convolution summand
   has weight at least `WT P + WT Q`.
5. Take the inner and outer infima.  Missing convolution pairs and cancellation only replace a
   candidate by `⊤` or a larger valuation.

This proof needs helper lemmas for `Polynomial.coeff_mul`, finite sums, and the two support
projections; it does not assert exact additivity.  **Status: PROVED mathematically; Lean proof
blueprint complete.**

### 2.3 The `hpure` bridge and the x-carry

**Lemma F4 (`key_coeff_side_floor`).** For every `a : ℕ`,

\[
D'h\le e_1\operatorname{addVal}((F.key)_a)+ah.
\tag{KCF}
\]

**Proof.** `F.hpure : IsPure X F.key h e₁`.  Apply landed `suppVal_of_pure` with
`φ=X`, `f=F.key`, `n=D'`; `F.hmonic`, `F.hdeg`, and `natDegree X=1` give

\[
\operatorname{suppVal}(X,F.key,h,e_1)=hD'.
\]

Landed `suppVal_le_weight` at the arbitrary abscissa `a` gives

\[
hD'\le e_1\operatorname{npHgt}(X,F.key,a)+ha.
\]

Landed `npHgt_X` rewrites the height as `addVal ((F.key).coeff a)`.  This proves (KCF),
including indices above the degree, where the coefficient is zero and the right side is `⊤`.
**Status: PROVED from named landed lemmas.**

**Corollary F5 (`key_coeff_side_floor_cleared`).** For every `a`,

\[
D'e_2h\le e_1e_2\operatorname{addVal}((F.key)_a)+ae_2h.
\]

**Proof.** Apply the monotone map `e₂ • ·` to F4 and distribute it over addition.  **Status:
PROVED.**

Put `tail := X^D' - F.key`.  Since `F.key` is monic of degree `D'`, the degree-`D'`
coefficient cancels; below `D'`, `tail.coeff a = -(F.key.coeff a)`; above `D'`, it is zero.
Using `addVal_neg` and F5 gives

\[
\operatorname{WT}(tail\,x^{a_0}Y^b)\ge
D'e_2h+a_0e_2h+bu_2.
\]

The other branch in `X^D'=Y+tail` has weight
`u₂+a₀e₂h+bu₂`, hence gains exactly
`u₂-D'e₂h=δ`.  This proves the x-carry prices without assuming that every tail coefficient lies
on the side; coefficients strictly above it are allowed.  **Status: PROVED.**

### 2.4 The composed-key price and the private-export fence

Let `B_b := dev F.key (composedKey T) b`.  C.47 publicly supplies:

* `composedKey_top_digit`: `B_q=1`;
* `composedKey_offLattice_digit`: off the `e₂`-lattice below `q`, `B_b=0`;
* `composedKey_zero_slot`: a zero label coefficient gives `B_(e₂t)=0`;
* `composedKey_slot_height`: for a nonzero label coefficient,
  `F.stageHeight B_(e₂t)=((f₂-t)u₂ : ℕ∞)`.

Unfolding `stageHeight` as a coefficient infimum implies that every nonzero scalar monomial
`c x^a` in `B_(e₂t)` satisfies

\[
e_1\operatorname{addVal}(c)+ah\ge(f_2-t)u_2.
\]

After multiplying by `e₂` and adding the outer cost `(e₂t)u₂`, every such monomial has weight
at least

\[
e_2(f_2-t)u_2+e_2tu_2=e_2f_2u_2=E_2.
\]

The leading monomial `Y^q` has weight exactly `qu₂=E₂`.  Consequently the reduced two-variable
image

\[
K_T(Y):=\sum_b B_bY^b
\]

has `WT K_T = E₂`.  A zero slot has weight `⊤`; a nonzero slot has minimum exactly `E₂`, but
**not every scalar monomial is claimed to have weight exactly `E₂`**.  The floor engine uses
only the lower bound.  **Status: PROVED from the four public C.47 clauses plus the conversion
lemma `stageHeight_eq_coeff_inf` in §3.2.**

The following helpers are currently private and must not be named by a new file.  Minimal export
plan:

| current private helper | file | public replacement required | consumer |
|---|---|---|---|
| `natDegree_stageLiftO_lt` | C.46 (also re-derived through `natDegree_cLift_lt` in C.47) | `KeyFrame.natDegree_stageLiftO_lt` | structural reconstruction of C.43's displayed digits; avoid duplicate copies |
| `slotRes_stageLiftO` | C.46 | `KeyFrame.slotRes_stageLiftO` with the fullness hypothesis | normalization-faithfulness proof for the exact cite |
| `slotRes_neg_stageLiftO` | C.46 | derive publicly from the preceding export plus a public additivity/negation lemma for `slotRes`; do not export a second specialized theorem unless Lean forces it | C.46 cleanup only |
| `stageHeight_stageLiftO` | C.47 | `KeyFrame.stageHeight_stageLiftO` | general lift pricing; C.47's public `composedKey_slot_height` suffices for the floor engine itself |
| `dev_composedKey`, `dev_composedKey_slot` | C.47 | no export required for this engine: the four public C.47 clauses above are sufficient | none |

Until these exports land, any node that needs the general lift rather than the public
`composedKey_*` wrapper is **BLOCKED BY VISIBILITY**, not licensed to copy a private name.

### 2.5 Monic division: both sides of the ledger

The key input is the following homogeneous-monic hypothesis on `K : R`:

* `K.Monic`, `K.natDegree=q` in `Y`;
* its leading term is `Y^q` of weight `E₂=qu₂`;
* every monomial in its tail has weight at least `E₂`.

`K_T` satisfies these conditions by §2.4 and C.47.

**Lemma F6 (`WT_divByMonic_ge_sub`).** Let `w : ℕ` and `P : R`.  If
`(w : ℕ∞) ≤ WT P`, then

\[
(w-E_2:\mathbb N)\le \operatorname{WT}(P /ₘ K).
\tag{Q}
\]

**Lemma F7 (`WT_modByMonic_ge`).** Under the same hypotheses,

\[
(w:\mathbb N)\le \operatorname{WT}(P \%ₘ K).
\tag{R}
\]

**Proof of F6--F7.** Use the actual monic-division algorithm, by induction on the outer degree of
the current dividend.

1. If its degree is `<q`, the quotient is zero and the remainder is the dividend.  Thus (Q) is
   `≤ ⊤` and (R) is the hypothesis.
2. Otherwise let `cY^m` be the current leading outer term.  The quotient step adds
   `cY^(m-q)` to the quotient.  Removing `q` powers of `Y` lowers its weight by exactly
   `qu₂=E₂`; hence the new quotient term has weight at least `w-E₂`.
3. Subtract `cY^(m-q)K` from the current dividend.  The leading term cancels.  Every tail term
   inserted by this subtraction has weight at least the weight of `cY^m`, because the tail of
   `K` has weight at least `E₂`.  F1 shows that the new dividend still has floor `w`.
4. Monicity makes its outer degree strictly smaller.  Apply the induction hypothesis.  F1
   combines the new quotient term with the recursive quotient; the recursive remainder already
   has floor `w`.

This is the missing quotient argument from v1.  It does not follow from linearity; linearity is
only useful after these inequalities are proved.  **Status: PROVED mathematically; Lean proof
blueprint complete.**

**Lemma F8 (`division_ledger`).** Define iterated quotients structurally by
`quot 0 P=P`, `quot (j+1) P=quot j (P /ₘ K)`, and let
`digit j P=(quot j P) %ₘ K`.  If `j≤μ` and `(μE₂ : ℕ∞)≤WT P`, then

\[
((\mu-j)E_2:\mathbb N)\le WT(quot\ j\ P),\qquad
((\mu-j)E_2:\mathbb N)\le WT(digit\ j\ P).
\]

**Proof.** Induct structurally on `j`, apply F6 to each quotient and F7 at the end, and use
`(μ-j)E₂-E₂=(μ-(j+1))E₂`, justified from `j<μ` in the successor case.  **Status: PROVED.**

### 2.6 Normal form by structural recursion, not rewriting

There is no reduction relation and no global rewrite measure in v2.

For a monic `φ`, define its quotient tower by structural recursion on `n`:

```text
qpow φ A 0       := A
qpow φ A (n + 1) := (qpow φ A n) /ₘ φ
digit φ A n      := (qpow φ A n) %ₘ φ.
```

Then define the finite reconstruction

\[
\operatorname{xNF}_F(A)=
 \sum_{b<A.\mathrm{natDegree}+1} C(\operatorname{digit}(F.key,A,b))Y^b.
\]

This is `biRead` before quotienting the coefficients by `F.key`.  B.05/B.06's reconstruction
and uniqueness prove evaluation at `Y=F.key` returns `A`, every digit has degree `<D'`, and all
extra digits are zero.  No recursive call is made on a polynomial selected by a rewrite:
`qpow` recurses on the syntactic natural `n`; the `Finset.range` fold recurses on a finite data
structure.  Lean therefore accepts termination structurally even before one proves that monic
division lowers degree.

At the outer key, use C.71's already landed structural recursion `devQ`:

```text
devQ K P 0       := P %ₘ K
devQ K P (j + 1) := devQ K (P /ₘ K) j.
```

The two-key normal form at coordinate `j` is obtained by applying `xNF_F` coefficientwise to
`devQ K_T (xNF_F f) j`.  Its existence is by definition; reconstruction and uniqueness follow
from monic division at `F.key` and then at `K_T`.  Termination is structural on `j` and the two
finite reconstruction ranges.  **Status: PROVED as a termination design; the semantic equality
with the C.71 shadow/honest discrepancy remains the named node F13 in §3.8.**

For the branch census, enrich the structural recursion's output with a natural tag `paid`:
tail contributions preserve the tag, a `Y` branch increments it, and outer recarry transports
the tag to the next `K_T` coordinate.  This is a recursion returning a finite tagged sum, not a
nondeterministic rewrite tree.  Erasing tags gives the preceding normal form by induction on the
same recursion.  The pricing invariant is proved simultaneously: a contribution with
`paid=k` has gained at least `kδ`.  This simultaneous induction is the formal content of the
census.  **Status: PROOF BLUEPRINT.**

### 2.7 Recarry arithmetic and the floor statement before conversion

The recarry lemma must be stated with the order hypotheses visible.

**Lemma F9 (`recarry_price`).** If `j' ≤ j`, `j ≤ μ₂`, and `1 ≤ k`, then

\[
(\mu_2-j')E_2+k\delta-(j-j')E_2
=(\mu_2-j)E_2+k\delta
\ge(\mu_2-j)E_2+\delta.
\]

In Lean the first displayed subtraction is not used as an unguarded `Nat` expression.  First
prove

```text
(μ₂ - j') = (μ₂ - j) + (j - j')
```

from `j'≤j≤μ₂`, distribute `E₂`, and cancel the explicit addend `(j-j')E₂`.  Then use
`δ≤kδ`, from `1≤k`.  **Status: PROVED.**

**Lemma F10 (`recarry_moves_up`).** In the unique `K_T`-development, absorbing one `K_T`
factor changes the coordinate from `j` to `j+1`; iterated absorption changes `j'` to
`j'+r`, never to a smaller index.

**Proof.** This is the quotient-tower definition: coordinate `j+1` is computed from the quotient
used to compute coordinate `j`.  Uniqueness of monic division forbids a second development with
the same evaluation and a downward term.  Induct on `r`.  **Status: PROVED mathematically;
requires a public `devQ` reconstruction/uniqueness lemma in Lean.**

**Floor census F11.** Under the `towerLocus` entry ledger and `j<μ₂`, the structurally computed
normal form of the shadow/honest discrepancy at coordinate `j` has every scalar monomial at
weight at least

\[
\Theta_j=(\mu_2-j)E_2+\delta=T.theta\ \mu_2\ j.
\]

**Proof blueprint.** F8 supplies the starting floor `(μ₂-j')E₂`.  A discrepancy contribution
has `paid=k≥1` by construction, so §2.3 adds `kδ`.  F10 gives `j'≤j`; F9 pays for each absorbed
outer-key factor and leaves at least one `δ`.  Forward feeding is another application of F6--F8
to a contribution already carrying the invariant.  Simultaneous structural induction over the
tagged quotient tower proves all three cases.  **Status: PROOF BLUEPRINT.**

F11 is still a statement about an actual reduced two-variable normal form.  It is **not** yet
C.72 and it is **not** yet `DvAbove`.

## 3. The conversion module (v1's L6, now load-bearing)

### 3.1 Finite-infimum utilities

The following lemmas are separate nodes because they control `⊤` and empty ranges.

**Cnv1 (`enat_nsmul_finset_inf`).** For `0<n`,
`n • (s.inf f) = s.inf (fun i => n • f i)`.

**Proof sketch.** Multiplication by a positive natural is an order embedding of `ℕ∞`, sends
`⊤` to `⊤`, and preserves binary minima.  Induct on the finite set; the empty case is
`n•⊤=⊤`.  **Status: PROOF BLUEPRINT.**

**Cnv2 (`enat_add_finset_inf`).**
`c + s.inf f = s.inf (fun i => c+f i)` and its right-addition version.

**Proof sketch.** If `c=⊤`, both sides are `⊤`.  If `c` is finite, addition by `c` is an order
embedding and preserves binary minima.  Induct on `s`.  **Status: PROOF BLUEPRINT.**

**Cnv3 (`finset_inf_product`).** A nested finite infimum equals the infimum over the sigma
product of the two index sets.

**Proof sketch.** Induct on the outer finite set, using associativity and commutativity of
`min`; the empty outer or inner set contributes `⊤`.  **Status: PROOF BLUEPRINT.**

**Cnv4 (`inf_range_eq_inf_support`).** If a range contains a polynomial's support, then the
infimum of `w (coeff i) i` over the range equals the infimum over support, provided
`w 0 i=⊤`.

**Proof sketch.** Split the range into support and its complement.  On the complement the
coefficient is zero, so every added value is `⊤`, the identity for finite infimum.  **Status:
PROOF BLUEPRINT.**

### 3.2 Flatten `stageHeight`

**Cnv5 (`gaussVal_C_eq_addVal`).** `gaussVal (C c)=addVal O c`.

**Proof sketch.** Unfold `gaussVal`.  If `c=0`, both sides are `⊤`; otherwise the constant
polynomial's range has the single relevant coefficient.  This is also a one-line consequence of
landed `npHgt_X` and `dev_X`.  **Status: PROVED.**

**Cnv6 (`stageHeight_eq_coeff_inf`).**

\[
F.stageHeight(A)=
 \inf_{a<A.natDegree+1}
 \bigl(e_1\operatorname{addVal}(A_a)+ha\bigr).
\]

**Proof sketch.** Start with landed `F.stageHeight_eq_inf`, replace `gaussVal (C (A.coeff a))`
using Cnv5, and normalize the `Nat.cast_mul` seam.  Zero `A` is included: its sole range term has
valuation `⊤`.  **Status: PROVED from a landed theorem plus Cnv5.**

### 3.3 Flatten `dvHgt` and `dvSupp`

**Cnv7 (`dvHgt_eq_coeff_inf`).**

\[
dvHgt(F,A,b)=
 \inf_{a<(dev\ F.key\ A\ b).natDegree+1}
 \bigl(e_1\operatorname{addVal}((dev\ F.key\ A\ b)_a)+ha\bigr).
\]

**Proof sketch.** Unfold `dvHgt`; it is `stageHeight (dev F.key A b)`.  Apply Cnv6.  **Status:
PROVED.**

**Cnv8 (`dvSupp_eq_nested_inf`).** For `0<e₂`,

\[
dvSupp(F,A,u_2,e_2)=
 \inf_b\inf_a
 \bigl(e_1e_2\operatorname{addVal}((dev\ F.key\ A\ b)_a)
       +ae_2h+bu_2\bigr),
\tag{FLAT}
\]

where `b` runs through `range (A.natDegree+1)` and `a` through the corresponding digit range.

**Proof sketch.** Unfold `dvSupp`, substitute Cnv7, distribute `e₂ •` across the inner infimum
with Cnv1, distribute it across addition, move the outer constant `bu₂` through the infimum with
Cnv2, and normalize natural casts.  Cnv3 flattens the nested infimum if a single index type is
preferred.  Every move is an equality, not merely a lower bound.  **Status: PROOF BLUEPRINT.**

### 3.4 Development recovery at the reduced normal form

**Cnv9 (`dev_reconstruct_reduced`).** Suppose

\[
A=\sum_{b<B} A_b(F.key)^b,\qquad \deg A_b<D'.
\]

Then `dev F.key A b=A_b` for `b<B`, and it is zero for `b≥B` once the reconstruction range is
past the degree.

**Proof sketch.** B.05 reconstructs the displayed development; B.06 uniqueness compares it with
the canonical `dev`.  Degree `<D'`, `F.hmonic`, and `F.hdeg` discharge the reduced-coefficient
hypotheses.  The vanishing tail follows from landed `dev_eq_zero_of_lt`.  **Status: PROVED from
named landed lemmas.**

**Cnv10 (`phiNF_coeff`).** In the structural `xNF_F A`, the outer coefficient at `b` is exactly
`dev F.key A b`, already reduced modulo `F.key`.

**Proof sketch.** Use the coefficient of a finite sum of `C digit * Y^b`; `Finset.sum_eq_single`
handles the in-range case and `dev_eq_zero_of_lt` the out-of-range case.  **Status: PROOF
BLUEPRINT.**

### 3.5 The weight-to-height identification

**Cnv11 (`dv2Hgt_eq_WT_phiNF`).** For `L=T.levelDatum hπ` and every `A : Polynomial O`,

\[
dv2Hgt(L,A)=WT_T(xNF_F(A)).
\tag{CONV}
\]

**Proof.** Unfold `dv2Hgt` to `dvSupp F A L.u L.ℓ`, then unfold `L.u=u₂` and `L.ℓ=e₂`.
Cnv8 gives (FLAT).  Cnv10 identifies the two scalar coefficients.  Apply Cnv4 first to each
inner range and then to the outer range: coefficients absent from support contribute `⊤`.
The resulting nested support infimum is exactly (WT).  **Status: PROVED modulo the four explicit
finite-infimum utility lemmas Cnv1--Cnv4.**

This equality handles cancellation honestly: it is applied to the **actual coefficient** of the
actual reduced normal form.  It never replaces the weight of a sum by the minimum of its
summands.  It also handles the zero polynomial: both sides are `⊤`.

### 3.6 Heights do not need a separate “class-separation” assertion

For the floor direction, the claim “heights separate classes” is unnecessary and is deleted.
The single exact identity (CONV) says that `dv2Hgt` is the minimum of the scalar weights of the
canonical reduced development.  Class separation enters only in residual exactness and CRT
realizability, not in converting a lower bound on every scalar coefficient into a height floor.

### 3.7 The all-coefficient/`DvAbove` bridge

**Cnv12 (`dvAbove_iff_coeff_floor`).** For `w : ℕ∞`,

```text
DvAbove F A u₂ e₂ w
```

is equivalent to saying, for every `b,a`,

\[
w\le e_1e_2\operatorname{addVal}((dev\ F.key\ A\ b)_a)+ae_2h+bu_2.
\]

**Proof sketch.** Unfold `DvAbove`, `dvHgt`, and `stageHeight`.  For the forward direction,
`stageHeight` is below every coefficient term, so the displayed coefficient bound follows only
if the `DvAbove` bound is combined with equality at the relevant infimum; thus the literal
equivalence is too strong in that direction and is **rejected**.  The direction actually needed
is:

**Cnv12' (`dvAbove_of_forall_coeff_floor`).** If the displayed inequality holds for all `a,b`,
then `DvAbove F A u₂ e₂ w`.

For each fixed `b`, take the inner infimum using `Finset.le_inf`; this yields the `DvAbove`
inequality at `b`.  Out-of-range coefficients are zero and contribute `⊤`.  **Status: PROVED.**

This correction prevents v2 from silently asserting a false converse.  C.52's box monomial uses
only Cnv12'.

### 3.8 From the census to C.72's actual floor

**Cnv13 (`shadow_discrepancy_phiNF`).** The reduced normal form produced by the tagged structural
census for coordinate `j`, after evaluation back at `Y=F.key`, is

```text
shadowDev T f j - dev (composedKey T) f j.
```

**Proof blueprint.** Expand `shadowDev`, `biRead`, and `devQ`; commute the canonical
`AdjoinRoot.modByMonicHom` representative with each finite sum; apply monic-division
reconstruction at `K_T` and `F.key`; and use uniqueness at both levels.  The honest tower is the
same quotient recursion before coefficient reduction.  Induction on `j` shows their difference
is exactly the tagged discrepancy with tags erased.  **Status: OPEN until formalized; no landed
lemma presently identifies these objects.**

**Cnv14 (`shadow_floor`).** Assuming `hf : f∈towerLocus T μ₂` and `hj:j<μ₂`,

```lean
(T.theta μ₂ j : ℕ∞) ≤
  dv2Hgt (T.levelDatum hπ)
    (shadowDev T f j - dev (composedKey T) f j)
```

**Proof blueprint.** F11 gives the scalar weight floor on the discrepancy normal form.  Cnv13
identifies that normal form with the displayed polynomial.  Cnv11 converts its `WT` to
`dv2Hgt`.  This is exactly C.72's `ShadowFloorStatement`; no type mismatch remains.  **Status:
OPEN precisely on F11 and Cnv13.**

### 3.9 The faithful band is an additional exactness theorem

**Cnv15 (`dv2Hgt_add_eq_left_of_lt`).** If
`dv2Hgt L A < dv2Hgt L B`, then `dv2Hgt L (A+B)=dv2Hgt L A`.

**Proof blueprint.** Flatten all three heights with Cnv11.  At every scalar coordinate the
valuation is ultrametric.  At a coordinate attaining the finite minimum for `A`, the strict
global inequality forces the corresponding coefficient of `B` to have larger valuation; the
strict valuation law gives equality for the sum at that coordinate.  The lower bound at every
coordinate gives the reverse inequality.  If `A=0`, the hypothesis is impossible.  **Status:
PROOF BLUEPRINT.**

**Cnv16 (`dv2Res_add_deep`).** If `dv2Hgt L A=(m:ℕ∞)` and
`m<dv2Hgt L B`, then `dv2Res L (A+B)=dv2Res L A`.

**Proof blueprint.** Cnv11 turns the strict bound on `B` into strict divisibility at every
scalar coefficient consulted by the side at height `m`.  The strict inequality ensures that the
side set and its minimum are unchanged.  For each consulted slot, `twistRead` is unchanged
because the added coefficient lies above the digit height; apply the coefficient formula in
`dvResPoly` and then the definition of `dv2Res`.  This is the uncapped, difference-height form of
the stability argument used in C.118b; it must be proved directly rather than citing C.118b's
coefficientwise-congruence hypothesis.  **Status: PROOF BLUEPRINT.**

Apply these with honest digit `A`, discrepancy `B=shadow-honest`, and Cnv14.  If the signed C.72
guard supplies `dv2Hgt A=(m:ℕ∞)` and `m<T.theta μ₂ j`, then Cnv15 gives equality of heights and
Cnv16 equality of `dv2Res`.  The drain stratum `dv2Hgt A=⊤` remains outside the statement, exactly
as C.72 requires.  Thus `shadow_faithful_band` consumes Cnv14--Cnv16; it is not a restatement of
the floor alone.  **Status: OPEN on those nodes.**

## 4. ★ The exact half

### 4.1 What the published theorem says

The positive citation determination is exact:

* **Published Theorem 2.8:** for a valuation `μ`, a key polynomial `φ`, and nonzero
  `g,h∈K[x]`, the principal Newton polygon satisfies
  `N^-_{μ,φ}(gh)=N^-_{μ,φ}(g)+N^-_{μ,φ}(h)`.
* **Published Corollary 4.12(3):** for the normalized residual polynomial operator associated to
  a fixed MacLane chain, `R_r(gh)=R_r(g)R_r(h)` for all `g,h∈K[x]`.
* **Published Definition 3.15:** `R_r(g)` is obtained from the unshifted residual polynomial by
  dividing out the power of `y` determined by the left endpoint.  This normalization is why the
  product formula is equality, not equality up to a scalar or monomial.
* **Published Definition 5.4:** “one-sided of slope `-ν`” means the relevant polygon equals its
  `ν`-component, begins at abscissa zero, and has positive length.

Theorem 2.8 implies closure of nonzero one-sided polygons of the same positive slope under
products: the Minkowski sum of their two segments is a segment of the same slope, with endpoint
coordinates added.  Induction gives powers.  Corollary 4.12(3) gives exact residual
multiplicativity, and induction gives `R_r(g^n)=R_r(g)^n`.  **Status: PROVED by the cited
published statements.**

The older arXiv v3 has different §4 numbering: the exact product formula is Corollary 4.7(3)
there.  A gate entry must use **published Corollary 4.12(3)**.  C.66's current header is to be
audited separately: its references to Corollaries 4.9(3)/4.12(3) mix the degree/nonzero-constant
clause with multiplicativity.

### 4.2 Draft Lean-facing gate-(b) signature

The following is a draft, not an axiom authorized by this document.  It deliberately keeps the
same positive-slope, full-degree fences as the already landed `fgmn_residual_mul`.

```lean
axiom fgmn_dv_exact_mul :
  ∀ {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {π : O}
    (F : KeyFrame O π) (hπ : Irreducible π) (H₀ : ℕ) (hpin : F.Pin H₀)
    {g g' : Polynomial O} (hg : g.Monic) (hg' : g'.Monic)
    {u ℓ : ℕ} (hℓ : 0 < ℓ) (hcop : Nat.Coprime u ℓ)
    (hfloor : ℓ * ((F.e₁ * F.f₁) * F.h) < u)
    (hdg : F.e₁ * F.f₁ ∣ g.natDegree)
    (hdg' : F.e₁ * F.f₁ ∣ g'.natDegree)
    (hpos : 0 < g.natDegree) (hpos' : 0 < g'.natDegree)
    (hpg : IsDvPure F g u ℓ) (hpg' : IsDvPure F g' u ℓ),
    IsDvPure F (g * g') u ℓ ∧
      ∀ (hne : (dvSideSet F g u ℓ).Nonempty)
        (hne' : (dvSideSet F g' u ℓ).Nonempty)
        (hne'' : (dvSideSet F (g * g') u ℓ).Nonempty)
        (M₀ M₀' M₀'' : ℕ)
        (hp : dvHgt F g (dvSideMin F g u ℓ hne) = (M₀ : ℕ∞))
        (hp' : dvHgt F g' (dvSideMin F g' u ℓ hne') = (M₀' : ℕ∞))
        (hp'' : dvHgt F (g * g') (dvSideMin F (g * g') u ℓ hne'') =
          (M₀'' : ℕ∞)),
        dvResPoly F H₀ hpin (g * g') u ℓ hne'' M₀'' hp'' =
          dvResPoly F H₀ hpin g u ℓ hne M₀ hp *
            dvResPoly F H₀ hpin g' u ℓ hne' M₀' hp'
```

The first conjunct imports Theorem 2.8 after the one-sidedness dictionary; the second imports
Corollary 4.12(3) after the residual-operator dictionary.  It strengthens C.66's “up to a
nonzero scalar” conclusion.  The gate must either replace C.66 or coexist under a name that
makes the stronger normalization commitment explicit; silently changing C.66's signed type is
not authorized here.

### 4.3 Local lemmas surrounding the cite

These are proof nodes, not literature axioms.

**E1 (`isTestKey_isDvPure`).** If `IsTestKey L Ψ`, then
`IsDvPure F Ψ L.u L.ℓ`.

**Proof blueprint.** Use the top digit, off-lattice vanishing, exact nonzero slot heights, and
the monic degree clause in `IsTestKey`.  Compute `dvSupp` at slope `(L.u,L.ℓ)`: all displayed
lattice slots have the same cleared value and off-lattice slots are `⊤`; the endpoints `0` and
`natDegree Ψ/D' = L.ℓ*deg L.r` lie on the side.  The constant label coefficient is nonzero in a
`LevelDatum`, so the left endpoint is finite.  **Status: PROOF BLUEPRINT.**

**E2 (`dvResPoly_testKey`).** For every legal side witness and pin of a test key,

```text
dvResPoly F H₀ hpin Ψ L.u L.ℓ ... = L.r.
```

**Proof blueprint.** E1 identifies `dvSideMin=0` and the side degree.  Unfold `dvResPoly`.
`IsTestKey`'s zero/nonzero cases identify each coefficient through `twistRead`; top monicity gives
the leading coefficient.  Finite-sum extensionality proves polynomial equality.  **Status:
PROOF BLUEPRINT.**

**E3 (`isDvPure_pow`, `dvResPoly_pow_exact`).** If `0<n`, `IsDvPure F g u ℓ`, and the degree
fences hold, then `IsDvPure F (g^n) u ℓ` and every normalized residual read equals
`(dvResPoly ... g)^n`.

**Proof blueprint.** Induct on positive `n`, using `fgmn_dv_exact_mul`; use monicity, degree
addition, positivity, and divisibility at the successor step.  Side witnesses exist from purity,
and finite pins come from `DvOnSide`.  Witness-independence follows because `dvSideMin` is a
definition and equality to a finite natural pin is unique.  **Status: OPEN on the gate cite.**

For `g=composedKey T`, C.47 gives `IsTestKey`; E1--E3 give
`IsDvPure F (composedKey T ^ μ₂) T.u₂ T.e₂` and exact residual
`towerLabel T ^ μ₂`.  With C.47 monicity/degree and `dev_pow_self`, this proves
`composedKey_pow_mem_towerLocus`.  **Status: OPEN on E1, E2, and the gate cite.**

### 4.4 Faithfulness argument and the owner-review gate

The cite is faithful only if all five identifications below are accepted together.

1. **Ambient valuation.** Use the same frame-to-MacLane valuation identification already trusted
   by C.66.  This document does not widen its ambient scope.
2. **Principal/positive side.** Published Theorem 2.8 concerns `N^-`.  The hypothesis
   `ℓ(D'h)<u` is exactly the positive augmented-slope fence used by C.66; boundary slope zero is
   excluded.
3. **Purity.** With `D'∣deg g` and positive degree, `IsDvPure` says the left endpoint and the
   actual terminal `F.key`-development index lie on the same side.  This is the corpus form of a
   full one-sided principal polygon.  Degree divisibility is essential because `IsDvPure` uses
   natural division.
4. **Left-end normalization.** Published Definition 3.15 divides the unshifted residual by the
   `y`-power determined by the left endpoint.  Corpus `dvResPoly` starts its sum at
   `dvSideMin` and assigns that term exponent zero.  These are the same shift.
5. **Coefficient normalization.** The source's coefficient is the residue after division by the
   MacLane normalizer at height `M₀-tu`.  Corpus C.22 defines exactly that read as `twistRead`,
   including the negative `twistExp` exponent; C.25 inserts it at
   `dvSideMin+ℓt`.  Thus coefficient-by-coefficient the corpus polynomial is the published
   normalized `R_r`, not merely a scalar associate.

Items 4--5 are the load-bearing basis for an **exact** gate.  They must receive owner
secondary review against the published Definition 3.15 and the corpus's C.22/C.25 sign
convention.  A review failure downgrades the cite to C.66's existing scalar statement and leaves
Step 1 OPEN; it may not be patched by choosing a scalar after the fact.

**Recommendation: CITE.** Reasons: the published results state both universal mechanisms at the
needed precision; powers are formal induction; and proving the graded-algebra product theorem
inside Lean would reproduce a substantial part of the cited theory.  The local E1/E2 dictionary
still must be proved, so the citation does not outsource corpus-specific normalization checks.

Contingency if the owner rejects item 5: prove, in order, `(i)` `dvSupp` product equality on
pure full sides, `(ii)` convolution uniqueness at the two endpoint-minimizing lattice classes,
`(iii)` multiplicativity of `slotRes`, `(iv)` the `twistExp_add` cocycle cancellation, `(v)`
coefficient convolution for `dvResPoly`, and `(vi)` polynomial extensionality.  These are
blueprint nodes, not claims that the route is short.

## 5. Revised node plan (each target 30--60 minutes)

The prime marks distinguish this plan from v1's invalid C.131 list.  Estimates are coding
increments, not promises of mathematical closure.

| node | deliverable | consumes |
|---|---|---|
| C.131a′ | `wtCoeff`, two-index `WT`, zero/support lemmas | C.06 arithmetic vocabulary |
| C.131b′ | `WT_add`, finite-sum valuation helpers | `addVal_add` |
| C.131c′ | two convolution lemmas and `WT_mul` | C.131a′--b′, `addVal_mul` |
| C.131d′ | `key_coeff_side_floor` and cleared form | `F.hpure`, B.35b, `npHgt_X` |
| C.131e′ | x-carry tail and exact `+δ` branch | C.131d′, C.71 margin |
| C.131f′ | public lift-pin exports/cleanup | C.46/C.47 private helpers |
| C.131g′ | composed-key monomial floor and `WT K_T=E₂` | public C.47 clauses, C.131f′ only if generality is needed |
| C.131h′ | one-step quotient bound F6 | C.131b′, C.131g′ |
| C.131i′ | one-step remainder bound F7 | C.131b′, C.131g′--h′ |
| C.131j′ | iterated quotient/digit ledger F8 | C.131h′--i′ |
| C.131k′ | structural `xNF`, reconstruction, uniqueness | B.05/B.06 |
| C.131l′ | structural outer normal form using `devQ` | C.71, C.131k′ |
| C.131m′ | tagged paid-branch recursion and erasure theorem | C.131e′, C.131l′ |
| C.131n′ | upward-recarry and guarded Nat arithmetic | C.131j′--m′ |
| C.131o′ | census floor F11 | C.131j′, C.131m′--n′ |
| C.131p′ | `ℕ∞` finite-infimum utilities Cnv1--Cnv4 | mathlib order lemmas |
| C.131q′ | `stageHeight_eq_coeff_inf` | C.02, B.15 |
| C.131r′ | flatten `dvHgt`/`dvSupp` | C.06, C.131p′--q′ |
| C.131s′ | reduced-development recovery/range-to-support | B.05/B.06, C.131p′ |
| C.131t′ | `dv2Hgt_eq_WT_phiNF` | C.11, C.131r′--s′ |
| C.131u′ | `dvAbove_of_forall_coeff_floor` | C.52 definition, C.131r′ |
| C.131v′ | shadow-discrepancy semantic identification | C.71, C.131k′--l′ |
| C.131w′ | C.72 `shadow_floor` | C.131o′, C.131t′, C.131v′ |
| C.131x′ | strict height exactness below a deeper summand | C.131t′ |
| C.131y′ | `dv2Res` stability and C.72 faithful band | C.22/C.25/C.38a, C.131w′--x′ |
| C.131z′ | gate-(b) `fgmn_dv_exact_mul` package, owner review | published FGMN Thm 2.8, Cor 4.12(3) |
| C.131aa′ | `IsTestKey → IsDvPure` | C.13 |
| C.131ab′ | exact residual of a test key | C.13, C.25/C.26 |
| C.131ac′ | exact powers; `composedKey_pow_mem_towerLocus` | C.47, C.131z′--ab′ |
| C.131ad′ | box monomial coefficient floor and `dvAbove_boxMonomial` | C.131c′--j′, C.131u′ |
| C.131ae′ | budget floors imply locus | C.118 capped tools, C.131ac′--ad′ |
| C.131af′ | locus implies budget floors | census and conversion; no pointwise use of C.53b's measure transport |
| C.131ag′ | `towerLocus_iff_budget` assembly | C.52 landed arithmetic, C.131ae′--af′ |
| C.131ah′ | C.54 node floor | C.131t′, C.131ag′ |
| C.131ai′ | C.54 sharp CRT realization | C.131ah′, H.51/H.52 |
| C.131aj′ | C.54 field floor | C.46 corrected residues, C.23; separate exact term census |

Splits C.131ae′/af′ may expand after their first proof state.  C.131aj′ is not advertised as a
floor-engine corollary: its residue cancellation is value-live and uses C.46.

### 5.1 Consumer matrix

* **C.72** consumes C.131w′ for `shadow_floor` and C.131x′--y′ for
  `shadow_faithful_band`.  It also consumes landed `T.theta`/`one_le_margin`.  It does not
  consume the exact-half cite.
* **C.52** consumes C.131ad′ for `dvAbove_boxMonomial`; C.131z′--ac′ for the exact purity and
  normalized residual power of `composedKey^μ₂`; and C.131ae′--ag′ for the two directions of
  `towerLocus_iff_budget`.  Lower bounds alone do not discharge Step 1.
* **C.53** consumes only the resulting `TowerBudgetIff`/`towerLocus_iff_budget` from C.52.
  Landed C.53b already replaces the false box-preserving triangular claim by a measure-preserving
  digit-vector transport and proves `towerLocus_fibration_of_leg1`.  No new “triangular box
  bijection” node is planned.
* **C.54(c)** consumes C.52's budget theorem plus C.131t′/ah′; **C.54(c)-sharp** additionally
  consumes C.131ai′; **C.54(d)** consumes C.131aj′ and therefore C.46's corrected residues.
  C.54 is currently a blueprint node, not a landed `C54.lean` file.

## 6. Honest scope of the numerical certificate

`verification/dv_ledger_cert.py` tests one fixed `s2` slice over the 2-adic integers:

```text
Φ' = x²-2, (e₁,f₁,h)=(2,1,1), (e₂,f₂,u₂)=(2,1,5),
Φ₂=(Φ')²-4x, E₂=10, δ=1.
```

It exhausts only its finite box range (`v<3`, `a<2D'`, `b<2e₂f₂`, `j<3`) and performs 4000
bounded random polynomial probes through degree 12, plus 400 equality probes.  Its recorded run
was 4143 tests, zero failures, with 372/400 equality hits.  This is useful evidence that the
specialized floor direction and both carries are correctly priced.  It does **not** certify:

* arbitrary DVRs, frames, tower data, degrees, or indices;
* the two-convolution proof of `WT_mul`;
* structural normal-form identification with `shadowDev`;
* the conversion to `DvAbove`/`dv2Hgt`;
* purity, residual multiplicativity, or any exact-half statement.

The script's docstring phrase “exactly C.52's statement” must therefore be read as “the
specialization of C.52's numeric inequality to this fixed instance,” not as universal
certification.

## 7. Final dependency verdict

The repaired floor engine is mathematically coherent: the weight is well typed, multiplication
uses both valuation convolutions, the x-carry premise follows from `hpure`, division has an
explicit quotient bound, and normalization terminates structurally.  Its remaining open proof
frontier is the tagged census plus the semantic identification with C.71's two division towers.

The conversion module is a major theorem chain, not an annex.  It has a complete finite-infimum
blueprint and isolates the two genuinely new faithful-band exactness lemmas.

The exact half has a published source at citable precision.  The recommended gate-(b) cite is
published Theorem 2.8 plus Corollary 4.12(3), with the corpus-normalization correspondence in
§4.4 receiving owner secondary review.  Before that gate is signed and E1/E2 are proved,
`composedKey_pow_mem_towerLocus`, C.52's capstone, C.53's remaining leg, and the corresponding
C.54 consumers remain **OPEN**.
