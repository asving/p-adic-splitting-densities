# WELD-ZERO pass 2 — HYP.148 discharged; HYP.139 retired from the capstone cone

**Date:** 2026-08-18  
**Unit:** WELD-ZERO, second model-diverse clean pass  
**Rows:** HYP.148 (`GENHN-BOX-2`) and HYP.139 (`W-1` transport)  
**Scope:** the `GENHN-BOX-2` side only. The `JD0-BOX-2` side and blueprint
amendment A-W.2 are outside this pass and are untouched.

## Verdict

**PASS 2 IS CLEAN.** The WELD-ZERO route gives a complete, general discharge of
HYP.148 at the strength stated in the hypothesis ledger. Consequently HYP.139
is completely retired **from the capstone cone**, because the only in-cone use
of its FGMN transport was underneath the W-9 face that HYP.148 carried.

The second conclusion is a removal-of-consumption argument, not a proof of the
global transport theorem. The march-level dictionary `TR-3′-GEN` remains open
at general order inside GRTJC. Thus the exact honest outcome is:

| row | pass-2 outcome | what is, and is not, proved |
|---|---|---|
| HYP.148 | **DISCHARGED** | GENHN-4 layer 1 is proved without COROLLARY W-9, uniformly in all stage data and all `μ`; no `GenhnBox2` hypothesis remains necessary on the capstone path. |
| HYP.139 | **RETIRED FROM THE CAPSTONE CONE** | No FGMN object occurs in the replacement proof, so the W-1 transport is no longer consumed. `TR-3′-GEN` itself is **not proved** and remains an off-cone GRTJC gap. |

This is the second consecutive clean pass over the effective WELD-ZERO text
(r0 + r1 repairs + the six-minor post-pass rider). It supplies the mathematical
premise for the already-authorized owner/ledger amendment described in chapter
F §8 and chapter I O-3. This note does not execute that amendment, edit a ledger,
remove a field, or change any Lean declaration.

## 1. Exact obligations and accepted inputs

The ledger statement of HYP.148 is narrowly scoped: at `μ ≥ 3`, **layer 1** of
LEMMA GENHN-4 imports COROLLARY W-9's twisted group algebra as its carry
bookkeeping. The GENHN source confirms twice that the consumption is in layer 1
(`GENHN_PROOF_2026-08-08.md`, S6.1 lines 873–884 and its grade note lines
908–909), and `GENHN-BOX-2` gives its retirement criterion: an elementary
general-`μ` carry display replacing that imported frame.

The proof below uses only the following already-landed or accepted inputs.

1. GENHN's `[e2]` field correction: if `θ` is a root of the stage key `Φ′`, then
   `L = Frac(Ô)(θ)` is the stage leaf field, its ramification and residue degrees
   are `e₁` and `f₁`, and its residue field is canonically `K`.
2. LEMMA GENHN-2: evaluation at `θ` has one `K`-line per occupied integral
   `dv`-height, and the slot minimum equals the valuation.
3. LEMMA GENHN-LIFT: for every consumed height `M > D′h` and every
   `λ ∈ K`, there is a degree-`< D′` integral lift of exact `dv`-height `M`
   whose normalized residue is `λ`.
4. LEMMA GENHN-3(c),(d): after the leading graded calculation, reduction to the
   canonical `Φ′_new`-development contributes only strictly deeper, in-window
   terms. This is GENHN-4's layer 2.

No W-9 clause, FGMN theorem, W-1 transport, J-D0 perimeter, or chapter-F carrier
theorem is an input to the proof. The chapter-F results landed by OM-9 remain
valid, but they are not needed to make the bypass work.

All quantifiers below are general. Let the base be any complete discretely
valued field in GENHN's stage setting; let `(e₁,f₁,h,μ)` be arbitrary admissible
stage data; put `D′ = e₁f₁`; and let `κ > D′h` be any consumed integral event
slope. The proof does not split by residue characteristic, by `e₁`, by `f₁`, or
by `μ`. In particular, the displayed proof holds for every `μ ≥ 1`; HYP.148
uses only its `μ ≥ 3` specialization.

The inequality `κ > D′h` is not an added hypothesis. At a consumed event the
left endpoint of the one-sided polygon gives `dv(A₀(θ)) = μκ`, while GENHN's
stage-initial node floor gives `dv(A₀(θ)) ≥ μD′h+1`. Hence
`μκ ≥ μD′h+1 > μD′h`, and therefore `κ>D′h`. This is precisely the occupied
domain on which GENHN-LIFT applies.

## 2. Elementary graded frame, with no weld input

Normalize the valuation on `L` by `dv = e₁v`, so `dv(L×) = ℤ`, and write

```text
gr_m(L) = {a : dv(a) ≥ m} / {a : dv(a) > m}.
```

For `a ≠ 0`, write `[a]` for its homogeneous initial class. The valuation laws
give

```text
[a][b] = [ab] ≠ 0,       [a]⁻¹ = [a⁻¹].
```

Hence `gr(L)` is a commutative graded field in the standard sense: every
nonzero homogeneous element is invertible. Its degree-zero part is the residue
field `k_L ≅ K`. If `u_m ∈ L` has `dv(u_m)=m`, then every degree-`m` class is
uniquely `ι(λ)[u_m]`, `λ ∈ K`; thus every homogeneous component is one
dimensional over `K`.

GENHN calls its positive-degree frame `gr(O_L)`. There is no mismatch here:
`gr(O_L)` is the nonnegative-degree subring of the full valuation grading just
used, and every degree occurring below is `(μ-k)κ ≥ 0`. We use the full grading
only to state homogeneous invertibility cleanly. No inference depends on a
positive-degree element being invertible *inside* `gr(O_L)`.

This proves directly the only structural facts for which GENHN layer 1 invoked
W-9(i) and W-9(iii): associative multiplication and one `K`-line per height.

## 3. The carry law is normalizer arithmetic

For every integer height `m`, let

```text
n(m) = x^{i(m)} π^{a(m)},
0 ≤ i(m) < e₁,
i(m)h + e₁a(m) = m.
```

The integer `i(m)` is unique because `gcd(h,e₁)=1`. For arbitrary integers
`a,b`, reduction of `i(a)+i(b)` to `[0,e₁)` gives

```text
i(a)+i(b) = i(a+b) + e₁ wrap(a,b),
wrap(a,b) = floor((i(a)+i(b))/e₁) ∈ {0,1}.
```

Comparing the height equations gives

```text
a(a)+a(b) = a(a+b) - h wrap(a,b),
n(a)n(b) = n(a+b)(x^{e₁}/π^h)^{wrap(a,b)}.        (3.1)
```

Associating `n(a)n(b)n(c)` in the two ways proves both the integer carry
identity and the corresponding unit-valued cocycle identity. This is a monomial
identity, not an invocation of W-9. It replaces W-9(ii), and supplies a concrete
representative for the cocycle mentioned in W-9(i).

Let

```text
N = [n(κ)(θ)] ∈ gr_κ(L),
η = res(θ^{e₁}/π^h) ∈ K×.
```

Iterating (3.1) gives, for every `t ≥ 0`,

```text
n(κ)(θ)^t = n(tκ)(θ)(θ^{e₁}/π^h)^{Wκ(t)},
Wκ(t) = floor(t i(κ)/e₁),
ϑ_t = η^{Wκ(t)},
[n(tκ)(θ)] = N^t ι(ϑ_t)⁻¹.                       (3.2)
```

This is the level-1 normalizer dictionary. It is derived here for arbitrary
`e₁,h,κ,t`; T1's accepted `(C2-wrap)/(C3-dictionary)` and GENTOW5-A1 are
corroborating suppliers, not logical premises.

## 4. The convention pin is resolved

For the old `Φ′`-development

```text
f = Σ_{j=0}^μ A_j Φ′^j,     A_μ = 1,
dv(A_j(θ)) ≥ (μ-j)κ,
```

define the multiplicative coefficient `c_j ∈ K` by

```text
[A_j(θ)] = ι(c_j)N^{μ-j}
```

when equality holds in the valuation bound, and set `c_j=0` when the inequality
is strict. Define

```text
R_N(T) = Σ_j c_j T^j.
```

If `Γ_j` is instead the coherent digit read against `n((μ-j)κ)`, equation
(3.2) gives

```text
Γ_j = c_j ϑ_{μ-j},       c_j = Γ_j ϑ_{μ-j}⁻¹.     (4.1)
```

The pass-1 note correctly treated the meaning of GENHN's unqualified word
“residual” as a load-bearing question. On the accepted corpus at HEAD, it is
resolved in favor of `R_N`, for three independent reasons.

1. GENTOW5 S1.2 defines `R_N`, calls it “the corpus's operative convention”,
   and explicitly names GENHN-4's layer-1 assembly as a consumer of that
   convention. Its convention consequence says that event statements are in
   the multiplicative convention and that the coherent vector need not itself
   be a perfect-power vector when the wrap is live.
2. GENHN's own event says that the key lift is “convention-keyed as always”,
   and its layer-1 proof says that the same wrap powers enter the residual
   assembly and the carry products. That is precisely (4.1) followed by
   multiplication in powers of `N`.
3. All three pinned corpus readers implement (4.1): QSCOUT22's `e₁=2` reader,
   GENHN's `e₁=3` reader, and GENHN's `μ=3` GN-REFINE3 reader. In the last, the
   raw exponent is

   ```text
   g_t = Wκ(μ) - Wκ(μ-t),
   ```

   and monic normalization cancels the common `η^{Wκ(μ)}`, leaving exactly
   `c_t = Γ_t ϑ_{μ-t}^{-1}`.

This is a resolution of the frozen statement's convention, not a new
mathematical assumption. It also agrees with the sealed live-wrap row: the
multiplicative read kills every pin, while the coherent read changes residual
type. Reading the hypothesis as the coherent polynomial would contradict both
the implemented convention and GENHN-4's claimed conclusion.

Thus the stage-event hypothesis used below is exactly

```text
R_N(T) = (T-s)^μ,       s ∈ K×.                    (4.2)
```

There is no residual “WZ-PIN” sub-lemma left open in this pass.

## 5. General substitution theorem

Choose the exact-height lift supplied by GENHN-LIFT so that

```text
w ∈ Ô[x],   deg w < D′,   dv(w(θ))=κ,
res(w(θ)/n(κ)(θ)) = -s.
```

Put `Φ′_new = Φ′+w`, so `[-w(θ)] = ι(s)N`. For each `0 ≤ k ≤ μ`, define

```text
B_k = Σ_{j=k}^μ binom(j,k)(-w)^{j-k}A_j.           (5.1)
```

This definition is unambiguous and gives the polynomial identity

```text
f = Σ_k B_k Φ′_new^k
```

before any reduction of a `B_k` modulo `Φ′_new`.

Every term of `B_k(θ)` has valuation at least

```text
(j-k)κ + (μ-j)κ = (μ-k)κ.
```

Taking the degree-`(μ-k)κ` initial class, terms whose `A_j` lies strictly above
the side contribute zero, while the remaining terms give

```text
[B_k(θ)]_{(μ-k)κ}
  = Σ_{j=k}^μ red(binom(j,k)) ι(s)^{j-k} N^{j-k}
      · ι(c_j)N^{μ-j}
  = N^{μ-k} ι(Σ_{j=k}^μ red(binom(j,k))s^{j-k}c_j)
  = N^{μ-k} ι([T^k] R_N(T+s)).                    (5.2)
```

Here `red` is the image of the integer binomial coefficient in the residue
field. Therefore (5.2) is valid in mixed and equal characteristic, including
when the residue characteristic divides a binomial coefficient.

By (4.2),

```text
R_N(T+s) = (T+s-s)^μ = T^μ.
```

Consequently, for every `k<μ`, equation (5.2) is zero, which by the definition
of the associated graded quotient is equivalent to

```text
dv(B_k(θ)) > (μ-k)κ.                               (5.3)
```

At `k=μ` the class is `1`. Thus all `μ` node-height pins die and the new leading
residual is `T^μ`. This is exactly GENHN-4 layer 1.

Nothing in this calculation assumes the existence of a W-9 carry table. It uses
only field multiplication, the normalizer identity (3.1), the exact-height
lift, and the polynomial Taylor identity. This proves the required statement
for all admissible `e₁,f₁,h,κ,μ` and both characteristics.

## 6. Why the canonical-reduction seam is not a gap in HYP.148

The `B_k` of (5.1) need not have degree `<D′`; passing from them to the canonical
`Φ′_new`-development is a separate operation. This does not leave a hidden gap
in the present discharge:

1. HYP.148 and `GENHN-BOX-2` explicitly identify only **layer 1** as the W-9
   consumer.
2. Equation (5.3) proves precisely the leading graded conclusion of that layer.
3. GENHN-4 layer 2 already handles the reduction overflow and other correction
   terms using GENHN-3(c),(d), proving they land strictly deeper and in-window.
   Layer 2 cites no W-9 clause and is not re-proved or strengthened here.
4. GENHN-4 layer 3 is the existing triangularity/cardinality argument and also
   cites no W-9 clause.

Accordingly the replacement proof composes as

```text
Sections 2–5 above (new weld-free layer 1)
  + GENHN-4's existing layers 2 and 3
  = GENHN-4 with no W-9 consumption.
```

The pass-1 `WZ-BOX-1` was an honesty scope marker, not an open sub-lemma owed by
the WELD-ZERO route. A proof of layers 2 and 3 from scratch would be useful
redundancy but is not part of HYP.148's statement or retirement condition.

## 7. Clause-by-clause discharge of HYP.148

The ledger's imported W-9 content is exhausted as follows.

| W-9 content | weld-free replacement |
|---|---|
| unit-valued 2-cocycle and associativity | `gr(L)` is an associative commutative graded ring; the concrete normalizer cocycle is equation (3.1), derived from exponents |
| integer `{0,1}` carry cocycle | `wrap(a,b)=floor((i(a)+i(b))/e₁)` and its cocycle identity follow from the two associations of `n(a)n(b)n(c)` |
| twisted group algebra / one `K`-line per height | every `gr_m(L)` is one dimensional over `K`, and GENHN-2 identifies the coefficient slot with that line |
| W-9(iv), monodromy/gauge period | not consumed by GENHN-4 layer 1 |

The actual pin-killing conclusion is then equation (5.3), rather than a
repackaging of the clause table. Hence no unspecified content hidden in the
phrase “organizing frame” is being assumed.

The proof is non-circular. Equations (3.1)–(3.2) are derived from the normalizer
monomials; GENHN-2 and GENHN-LIFT are internal elementary results whose proofs
do not use W-9; and the proof never names an FGMN residual operator. J-D0 is not
consumed: the additive substitution is proved directly, and no pointwise
type-preservation claim is made for the coherent/multiplicative dictionary.

Therefore HYP.148 is discharged at its full ledger quantification. OM-9's
carrier residual—“the site's carry table is a `CarryCocycle` instance, plus
HYP.139”—is bypassed rather than instantiated: the capstone proof no longer
needs a `GenhnBox2` witness at that site.

## 8. Exact disposition of HYP.139

HYP.139 asserts the still-open transport from the harness `(w,𝑅)` to the FGMN
objects, with the compatible general-order dictionary `TR-3′-GEN`. Nothing in
Sections 2–7 proves that transport. In particular, OM-9's
`w1Transport_iff_zero_iff` proves only the weak carrier signature and cannot
prove the march-level compatibility.

The capstone, however, no longer consumes that theorem:

1. The hypothesis ledger and the weld-face audit identify the sole in-cone
   chain as

   ```text
   W-1 transport
     → W-9
     → GENHN-4 layer 1 at μ≥3
     → GENHN count laws
     → GENIND.B / W-12.D.
   ```

2. Sections 2–7 replace the middle two arrows by a direct proof in the stage
   leaf field. The replacement contains only `L`, `O_L`, `gr(L)`, `K`, the
   normalizers, and the polynomial coefficients. It contains no FGMN object and
   no residual-operator transport.
3. The weld-face audit records the other apparent W/J routes as not taken or
   out of the capstone cone. No second in-cone consumer of W-1 remains.

Thus HYP.139 is **completely retired as a capstone condition** when HYP.148 is
struck. This is the exact sense in which the HYP.149/WELD-ZERO route “retires
both HYP.148 and HYP.139”.

The exact remaining mathematical gap, outside the capstone cone, is unchanged:

> Construct, at arbitrary general order, the line-wise units identifying the
> harness residual operators with the FGMN residual operators and prove their
> compatibility with the full march-level dictionary (`TR-3′-GEN`), beyond the
> strata where that dictionary is already closed.

This note neither solves nor conceals that problem. A future theorem inside
GRTJC may still need it; the capstone route does not.

## 9. Pass-2 checks and acceptance boundary

As a corroborating check, not as a proof premise, the pinned
`verification/openmath/weldzero_checks.py` was rerun at current HEAD:
**9,877 checks, 0 violations**. It includes both residue characteristics,
`e₁=2,3`, `μ=2,3,4`, live and dead wraps, actual polynomial re-division, a
non-perfect-power negative control, and 9,295 independent normalizer-wrap
checks. The effective pass-1 source note is unchanged by this pass.

No open mathematical sub-lemma remains for the HYP.148 discharge. The only
remaining actions are governance/implementation actions outside this charge:

1. book the accepted two-pass WELD-ZERO arc in the hypothesis ledger;
2. close HYP.149;
3. mark HYP.148 discharged and HYP.139 retired from the cone, while preserving
   HYP.139's off-cone `TR-3′-GEN` residue;
4. execute the owner-gated chapter-F/chapter-I field-removal amendment already
   authorized at F §8 / I O-3.

Until that owner fold is executed, the existing files continue to display
HYP.148 as CARRY and HYP.139 as MATH. This pass supplies the argument that
licenses the fold; it does not silently perform it.

## Fence record

The A-W.2 fence is untouched. No Lean file, blueprint, ledger, campaign file,
or original WELD-ZERO note was edited. This pass adds only this argument note.
