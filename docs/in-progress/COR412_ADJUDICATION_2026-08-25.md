# Corollary 4.12 adjudication: grade anchoring and the carry twist

Date: 2026-08-25

Unit: U14

Status: decided by print-reading; proposal only, no Lean source changed

## 1. Decision

The source operator `R_{r,α}` is **grade-anchored**. It is defined on the fixed grade line
`L_α`, whose first legal abscissa is `s_r(α)`. It is not independently shifted to the left
endpoint of each input polynomial.

The apparent conflict with published Corollary 4.12(2) comes from a hypothesis omitted in
`C130fg.lean`: the printed plain product law assumes that the second grade belongs to the
**preceding value group**, `β ∈ Γ_{r-1}`. Definition 3.12 then gives `s_r(β) = 0`, so there is
no carry. In the S2 integer clearing, this is the even-grade condition.

Consequently:

1. RP-1's `s2GradedRes` should **not** be re-anchored. Its `β % 2 + 2t` slots are the faithful
   S2 instance of the printed fixed line `L_α`.
2. The S2 law
   `R_{β+β'}(gh) = X^((β % 2) * (β' % 2)) R_β(g) R_β'(h)` is the correct extension of the
   proof to two arbitrary S2 grades, but it is **not a transcription of Corollary 4.12(2)**.
   The corollary states only its no-carry specialization.
3. `FGMNSourceLaws.graded_mul` must regain the preceding-grade premise (or the equivalent
   cleared divisibility premise). It must not be replaced by an S2-specific parity formula in
   the general FGMN carrier.
4. `normalized_mul` is unchanged. The separately defined operator `R_r` removes the initial
   `y`-power, and this removal absorbs exactly the carry.
5. The unrestricted scalar law currently consumed through A-C.11 does **not** follow by taking
   coefficient zero of the twisted graded law. In an odd-by-odd product its left side is the
   constant coefficient of `X P Q`, hence zero, while the product of the two constant
   coefficients need not be zero. RP23's tooth is precisely `0 ≠ 1` after this projection.

This is a third outcome, rather than either side of the proposed dichotomy: retain the printed
grade-anchored operator, restore the printed scope restriction, and keep the normalized
operator as the unrestricted multiplicative one.

## 2. Sources and numbering

Print-read files:

- `docs/references/FGMN_residual_ideals_2015_authorpdf.pdf`, SHA-256
  `33b849ce6784f4bad8368d83b5b725b4545eebdd79918e3ee5dfafd1791daeda`;
- `docs/references/fgmn_residual_ideals_1305.0775v3.pdf`, SHA-256
  `651b0cef64e6aea11526965d3ef7879d69ce7c0a31af497978c3e6192f615f35`.

The repository map in `FGMNCALCULUS_FIELDLIST_2026-08-24.md` §2 is correct for the loci at
issue. In the author/published numbering the graded and normalized product laws are
Corollary 4.12(2) and (3), with the fixed-line operator in Definitions 3.12--3.13 and the
normalized operator in Definition 3.15. In arXiv v3 the same product result is Corollary 4.7,
the line data and graded operator are in Definitions 3.15--3.16, and normalization is
Definition 3.18. ArXiv-v3 Corollary 4.12 is a later prescribed-residual construction, not the
product law.

## 3. Verbatim print-read: the anchoring convention

The author PDF, p. 16, Definition 3.12 says:

> “For `0 ≤ i ≤ r` and `α ∈ Γ_i`, let `s_i(α), u_i(α)` be the unique integers satisfying
> `u_i(α)e_i + s_i(α)h_i = e(μ_i)α` and `0 ≤ s_i(α) < e_i`.”

Definition 3.13 then begins (p. 16):

> “For `α ∈ Γ(μ)` and `g = Σ_{0≤s} a_s φ_r^s` the `φ_r`-expansion of
> `g ∈ P_α(μ)`, we define:”

and its formula uses

> “`s_j := s_r(α) + je_i` and `α_j := α − s_j μ(φ_r) ∈ Γ_{r−1}`.”

The explanatory paragraph is dispositive (p. 16):

> “Let `L_α` be the line of slope `−ν_r` cutting the vertical axis at the point `(0, α)`.
> The monomials of `R_{r,α}(g)` are in 1-1 correspondence with the points of `C ∩ L_α`.”

Thus the origin of the polynomial coordinate is the grade-dependent first lattice point
`s_r(α)` on `L_α`. It is not the polynomial's own Newton-side left endpoint `s(g)`.
For an exact input, `α = μ(g)`, so `L_α` is of course the supporting line of that polynomial;
this coincidence of lines does not move the `y^0` origin from `s_r(α)` to `s(g)`.

The source introduces that second shift only for the different operator `R_r`. Definition
3.15, p. 17, says verbatim:

> “For a nonzero `g ∈ K[x]`, let `α = μ(g)`. We define”

and, for `r > 0`,

> “`R_r(g) := R_{r,α}(g)/y^{j_0}`, ... where `j_0 = ⌊s(g)/e_r⌋`. We take `R_r(0) = 0`
> for all `r`.”

Therefore “read on the polynomial's own minimal point” describes the **normalization from
`R_{r,α}` to `R_r`**, not the definition of `R_{r,α}`.

## 4. Verbatim print-read: why Corollary 4.12(2) has no carry

Published Corollary 4.12, p. 20, states:

> “(2) If `β ∈ Γ_{r−1}`, then `R_{r,α+β}(gh) = R_{r,α}(g)R_{r,β}(h)` for all
> `g ∈ P_α(μ), h ∈ P_β(μ)`.”

The restriction is used explicitly in the proof:

> “The second equality proves (2) because `s_r(β) = 0`, and this leads to
> `s_r(α + β) = s_r(α)`, `u_r(α + β) = u_r(α) + u_r(β)`.”

ArXiv v3 Corollary 4.7(2), pp. 21--22, has the same restriction and proof, with `i` in place
of `r`: “If `β ∈ Γ_{i−1}` ...”; “because `s(β) = 0` ...”. This is not numbering drift in the
hypothesis.

The current comment in `C130fg.lean` that the premise is “automatic after clearing” is
incompatible with RP-1's actual grade domain. RP-1 admits all cleared S2 values, including
grade `5`, and Definition 3.12 reads `s_2(5) = 1`. If the interface instead restricted every
grade argument to the preceding group, then it would not be instantiated by RP-1's total
full-grade operator. One cannot simultaneously use the full S2 grade domain and declare the
preceding-group premise automatic.

## 5. The arbitrary-grade extension and the S2 parity tooth

The twist follows directly from the same printed data. Put

```text
s = s_r(α),  t = s_r(β),  c = floor((s+t)/e_r) ∈ {0,1}.
```

Definition 3.12 gives

```text
s_r(α+β) = s+t-c e_r,
u_r(α+β) = u_r(α)+u_r(β)+c h_r.
```

With the paper's `ϕ_r(α) = x_r^{s_r(α)} p_r^{u_r(α)}` and
`y_r = x_r^{e_r}p_r^{-h_r}`, this yields

```text
ϕ_r(α) ϕ_r(β) = ϕ_r(α+β) y_r^c.
```

Substitution in the second displayed equality in the proof of Corollary 4.12 gives the
arbitrary-grade extension

```text
R_{r,α+β}(gh) = y^c R_{r,α}(g) R_{r,β}(h).
```

When `β ∈ Γ_{r−1}`, `t = 0`, hence `c = 0`; this is exactly the printed corollary. At S2,
`e_2 = 2` and `s_2(k) = k % 2`, so

```text
c = ((β % 2) + (β' % 2)) / 2 = (β % 2) * (β' % 2).
```

RP23's two teeth then have the correct interpretation:

- mixed/no carry: the exponent is zero and the printed-looking product is plain;
- odd-by-odd: the exponent is one, so `R_10(Φ'^2) = X`, whereas
  `R_5(Φ')R_5(Φ') = 1`.

The S2 twist is therefore mathematically faithful to the source definitions and proof as a
**new generalization**, while the claim that it is Corollary 4.12(2) verbatim would be false.

## 6. Scalar projection: the current unrestricted A-C.11 law does not survive

`C130la.lean` defines

```lean
S.Rgr β g := (S.gradedResidual β g).coeff 0
```

For the arbitrary-grade law with carry `c`:

```text
coeff_0 (X^c P Q) =
  coeff_0(P) coeff_0(Q),  if c = 0;
  0,                      if c > 0.
```

Thus coefficient zero gives the current plain scalar `Rgr_mul` only under the no-carry
scope, in particular under the printed `PrevGrade β'` premise. It does not give an
unrestricted scalar law. The RP23 odd-by-odd tooth makes this non-vacuous:

```text
coeff_0 R_10(Φ'^2) = coeff_0 X = 0,
coeff_0 R_5(Φ') * coeff_0 R_5(Φ') = 1 * 1 = 1.
```

This matters immediately to `C99r.lean`: `gentow2_Bpp` iterates A-C.11's `Rgr_mul` with
second grade `u'`. Its own hypotheses include `Nat.Coprime u' e'`; at the S2 values
`(e',u') = (2,5)`, that grade is specifically outside the preceding group. Hence the printed
Corollary 4.12(2) cannot justify that iteration, and the twisted full-grade law cannot justify
its coefficient-zero step.

There are only two faithful consumer routes:

1. Keep `Rgr = coeff 0` of `R_{r,β}` and restrict A-C.11's scalar `Rgr_mul` by
   `PrevGrade β'` (at S2, `2 ∣ β'`). Consumers such as `gentow2_Bpp` must then provide that
   premise or cease using this law.
2. If consumers genuinely require unrestricted scalar multiplication, change their scalar to
   the attained-origin/normalized scalar `(R_r(g)).coeff 0`. Its multiplication is a
   coefficient-zero consequence of Corollary 4.12(3), not of (2). This must be a deliberate
   A-C.11 semantic amendment; it must not be described as coefficient zero of the unnormalized
   `R_{r,β}`. The recipe bridge must then be rechecked at every use.

Re-anchoring `s2GradedRes` itself is not a faithful third route: it would silently replace
`R_{r,α}` by `R_r` and duplicate the already separate `normalizedResidual` carrier.

## 7. Why normalization absorbs the twist

Published Definition 3.15 gives

```text
R_{r,α}(g) = y^{j_g} R_r(g),  j_g = floor(s(g)/e_r).
```

The left endpoints add under multiplication, and the floor identity is

```text
j_{gh} = j_g + j_h + c,
```

where `c` is the same carry as above. Dividing the arbitrary-grade identity by
`y^{j_{gh}}` cancels `y^c` and gives `R_r(gh) = R_r(g)R_r(h)`.

This agrees with the printed statement and proof. Corollary 4.12(3), p. 20, says verbatim:

> “`R_r(gh) = R_r(g)R_r(h)` for all `g,h ∈ K[x]`.”

Its proof concludes:

> “The third equality proves (3) by Corollary 2.7.”

Therefore `FGMNSourceLaws.normalized_mul` is correctly typed today and needs no twist, grade
premise, or signature change.

## 8. Diff proposal (do not apply in this unit)

### 8.1 Recommended source-faithful carrier change

Restore the scope carrier already recommended by
`FGMNCALCULUS_FIELDLIST_2026-08-24.md` §3--§4. The realization must identify it with membership
in the preceding value group. Under the full-current-group integer clearing used by RP-1, this
is `e' ∣ β`; at S2 it is evenness.

```diff
--- a/leanfinal/Uniformity/ChapC/C130fg.lean
+++ b/leanfinal/Uniformity/ChapC/C130fg.lean
@@ structure FGMNSourceData ... where
   nextValue : Polynomial O → WithTop ℤ
   gradedResidual : ℕ → Polynomial O → Polynomial (W.fld r)
   normalizedResidual : Polynomial O → Polynomial (W.fld r)
+  /-- Cleared grades coming from the preceding value group Γ_r
+  (published Corollary 4.12(2)'s β ∈ Γ_r after the repo index shift). -/
+  PrevGrade : ℕ → Prop
   ...

@@ structure FGMNSourceLaws ... where
-  /-- FGMN published Corollary 4.12(2), polynomial-valued, with the exact-grade product
-  conclusion. U9 Q3 makes the source's β ∈ Γ_r premise automatic after clearing, so no
-  PrevGrade binder appears. -/
+  /-- FGMN published Corollary 4.12(2), including its β ∈ Γ_r premise. -/
   graded_mul : ∀ β β' (g h : Polynomial O),
     S.ExactGrade β g → S.ExactGrade β' h →
+    S.PrevGrade β' →
       S.ExactGrade (β + β') (g * h) ∧
       S.gradedResidual (β + β') (g * h) =
         S.gradedResidual β g * S.gradedResidual β' h

   /-- FGMN published Corollary 4.12(3); unchanged. -/
   normalized_mul : ∀ g h : Polynomial O,
     S.normalizedResidual (g * h) =
       S.normalizedResidual g * S.normalizedResidual h
```

If the orchestrator prefers not to add an abstract predicate, the exact arithmetic variant in
the established cleared coordinate is:

```lean
graded_mul : ∀ β β' (g h : Polynomial O),
  S.ExactGrade β g → S.ExactGrade β' h → e' ∣ β' →
    S.ExactGrade (β + β') (g * h) ∧
    S.gradedResidual (β + β') (g * h) =
      S.gradedResidual β g * S.gradedResidual β' h
```

The predicate form is recommended until OPEN-DICT-2 formally proves that divisibility is the
correct general cleared-group test.

### 8.2 Keep the S2 arbitrary-grade law separate

RP-4/RP-6 may and should prove the stronger S2 theorem on `s2GradedRes`:

```lean
s2GradedRes_mul : ∀ β β' (g h : Polynomial O),
  S2ExactGrade β g → S2ExactGrade β' h →
    s2GradedRes (β + β') (g * h) =
      Polynomial.X ^ ((β % 2) * (β' % 2)) *
        s2GradedRes β g * s2GradedRes β' h
```

It should be documented as the arbitrary-grade carry extension, not installed verbatim as the
general `FGMNSourceLaws.graded_mul` field.

### 8.3 Mandatory downstream follow-up

If A-C.11 keeps `Rgr := coeff 0` of `gradedResidual`, propagate `PrevGrade β'` to
`C130la.lean`'s `Rgr_mul` and `C130pk.lean`'s class field. Remove or restrict `Rgr_pow`; its
present unrestricted proof repeatedly uses the omitted premise. `C99r.gentow2_Bpp` cannot
discharge that premise at the S2 `u' = 5` step and must be redesigned.

If the campaign instead chooses the consumer-preserving normalized scalar, make that a
separate signed amendment:

```lean
RgrNorm (g : Polynomial O) := (S.normalizedResidual g).coeff 0
```

and derive its unrestricted multiplication from `normalized_mul` plus
`Polynomial.mul_coeff_zero`. Do not alter `s2GradedRes`, and do not cite this normalized scalar
law as Corollary 4.12(2).

## 9. Final adjudication line

**SOURCE CONVENTION: grade-anchored. SOURCE PRODUCT LAW: plain only with the printed
preceding-group premise. S2 FULL-GRADE EXTENSION: parity/carry twisted. NORMALIZED LAW: plain
and unrestricted. COEFFICIENT-ZERO SCALAR: multiplicative only in the no-carry scope; the
current unrestricted A-C.11 field is not supplied by Corollary 4.12(2).**
