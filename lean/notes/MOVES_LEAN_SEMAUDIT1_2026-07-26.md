## Audit result

Stop the line. The shared `Stage` package does not encode the accepted stage axioms. In particular, it erases the current residue subfield, the coefficient localization, the exponent-vector data for `T`, the parent scale, and the required relation between the S6b threshold and the parent key weight. Several later statements then either restate assumed `Stage` fields, add the missing mathematics as hypotheses, or collapse residue growth to the linear case.

Counts for the 59 theorem statements:

- **39 FAITHLESS**
- **2 IMPRECISE**
- **3 FLAGGED-OK**
- 15 faithful as scoped

Separately, the definitions file contains **10 FAITHLESS structural defects** and **1 IMPRECISE formulation**.

## Definitions audit

### DEF-1 — S3 is absent: FAITHLESS

Lean jumps directly from K1 to S5:

```lean
hK1 : K1At w Φ (w Φ)
resUnits : Subgroup Fˣ
hS5 : ...
```

Accepted mathematics requires:

> “(S3) Slot decomposition: for each γ, the development induces a group isomorphism  
> `gr_γ(A) ≅ ⊕_j gr^C_{γ−j·h}`; equivalently `Y` is transcendental over the coefficient classes.”

No slot decomposition, degreewise independence, or transcendence property appears in `Stage`. K1 alone does not package S3 in the residual-only model.

### DEF-2 — S4 and the current residue field are absent: FAITHLESS

Lean has only one ambient field:

```lean
structure Stage ... (F : Type u) [Field F] [Fintype F]
resUnits : Subgroup Fˣ
```

Accepted mathematics requires:

> “`(L^coeff)₀ = F`, `L₀ = F[z^{±1}]`, and the degree-0 exponent group … is infinite cyclic.”

At an increment it further requires:

> “The degree-0 coefficient field is `F' := F[z]/(ψ)`.”

A multiplicative subgroup `resUnits : Subgroup Fˣ` is not a subfield and does not determine addition, scalar action, field extension, or the coefficient-localization degree-zero field.

The fixed-ambient design consequently fails: it needs a tracker such as a current `Subfield F` and an extension `K(zbar)`. Instead, statements use:

```lean
Algebra.adjoin F {(zbar : F)}
```

This is adjoin over `F` inside `F`, hence is simply all of `F`. It records no residue growth.

Worse, the signatures often combine:

```lean
ψ : Polynomial F
hψ : Irreducible ψ
zbar : Fˣ
hzbar : ψ.eval (zbar : F) = 0
```

An irreducible polynomial over the ambient field having a root in that same field is linear. Thus every such “degree-`g` residue extension” collapses to `g = 1`.

### DEF-3 — `U`, representatives, `V`, and the exponent vector for `T` are absent: FAITHLESS

Lean contains no fields for any of them. It merely comments:

```lean
/-- the residual map `R(f) = [f]·T^{−w(f)}` -/
R : Polynomial ℤ_[p] → LaurentPolynomial F
```

Accepted mathematics requires:

> “`T` is carried as an INTEGER EXPONENT VECTOR over the representative list  
> `(p, φ = Φ₁, Φ₂, …)`.”

It also requires the outgoing key to join `U`, the current key to be localized separately, and a transported vector `V'`. None of those are expressible in `Stage`.

Consequently `R` is not defined as `[f]·T^{-w(f)}`. It is an arbitrary function satisfying a limited collection of equations.

### DEF-4 — the S5 exponent uses the wrong scale: FAITHLESS

Lean:

```lean
R B = LaurentPolynomial.C (c : F) *
      LaurentPolynomial.T (- t * w B)
```

Accepted mathematics:

> “`k(B) = −t·w_prev(B)`,”

with current coefficient weight

> “`w(B) = e·w_prev(B)`.”

Lean therefore uses `−t·e·w_prev(B)` where the mathematics uses `−t·w_prev(B)`. This is not cosmetic: it changes digit positions, stride formulas, standard-lift exponents, and S6 indices.

The base-stage spot check exposes it immediately. Accepted:

> `dig(B) = ū·z^{−t·v(B)}`

while Lean gives `z^{-t·e·v(B)}`.

### DEF-5 — the `e = 1` pinning correction is missing: FAITHLESS

Accepted P2 requires:

> “at `e = 1` stages `T`’s vector has zero exponent on the current key,”

hence `t = 0` and coefficient digits have position zero.

Lean only assumes:

```lean
hbez : (e : ℤ) * s + (h : ℤ) * t = 1
```

When `e = 1`, this does not force `t = 0`; there are infinitely many Bézout pairs. This invalidates the claimed position-zero conclusions in recentering and `L5_realConclusion`.

### DEF-6 — S6a’s constant orbit group is not constant: FAITHLESS

Lean:

```lean
O : Subgroup Fˣ
hO_le : O ≤ resUnits
```

Accepted mathematics:

> “the CONSTANT orbit group `O := F_Qˣ` (the BASE field’s units).”

Every `Stage` chooses an unrelated subgroup. There is no base field object, embedding of `F_Q`, or cross-stage equality preserving `O`.

The projected `weightSet` also loses the accepted pair-valued index set

> `𝒜 := {(w(B), k(B)) : B ∈ C∖0}`.

That projection would only be harmless if the forced position formula were correct; DEF-4 shows it is not.

### DEF-7 — S6b is not “all current-field scalars”: FAITHLESS

Lean:

```lean
hS6b : ... a ∈ resUnits → ∃ B, ...
```

Accepted mathematics:

> “ANY prescribed digit scalar in the current field’s unit group.”

Nothing requires `resUnits = ⊤`, nor does `resUnits` represent the units of a current subfield. Some theorems add `σ.resUnits = ⊤` as a separate assumption, which smuggles in missing stage strength instead of proving the accepted S6b package.

### DEF-8 — the S6b threshold is arbitrary: FAITHLESS

Lean:

```lean
thr : ℤ
```

with no law relating it to other data.

Accepted mathematics:

> “STRICTLY ABOVE the current key’s parent weight `w_prev(Φ)`.”

No parent valuation or parent key weight is stored, so the rev-D4/D5/D8 threshold correction cannot be stated. Conditions such as

```lean
σ.thr < W
```

do not express the accepted clean threshold.

### DEF-9 — `IsStandardLift` is much weaker than the displayed lift: FAITHLESS

Lean:

```lean
Φhat.Monic ∧
Φhat.natDegree = σ.e * g * σ.Φ.natDegree ∧
σ.R Φhat = T(...) * Polynomial.toLaurent ψ
```

Accepted mathematics defines:

> `Φ̂ := Φ^{eg} + Σ_{k<g, ψ_k≠0} t_k·Φ^{ek}`

with each `t_k` an S6b realizer of a specified weight and scalar, zero slots absent, equal slot weights, and literal leading coefficient one.

The Lean predicate admits any monic polynomial of the correct degree and residual. It does not say it has the displayed slots or that

> `w(Φ̂) = ehg`.

Thus later recovery of the weight or K1 from `IsStandardLift` is not semantically justified.

### DEF-10 — `IsRecentering` assumes an unrelated completed stage: FAITHLESS

Lean:

```lean
def IsRecentering (σ σ' : Stage p F) ... :=
  ...
  σ'.Φ = σ.Φ - tt ∧
  (∀ f, σ'.w f = σ.w f)
```

Accepted TRANS-RS constructs and checks, item by item:

> same coefficient representatives, same coefficient field, unchanged `T`,  
> `L'₀ = F[z'^{±1}]`, unchanged coefficient digits, and the same S6 data.

Lean assumes `σ'` is already an arbitrary full `Stage`. It does not relate `σ'.R`, `σ'.O`, `σ'.resUnits`, `σ'.weightSet`, `σ'.thr`, or its Bézout pinning to `σ`. This makes several recentering theorems circular or unprovable.

### DEF-11 — value-group formulation: IMPRECISE

Lean:

```lean
hvalgrp : ∃ f g, f ≠ 0 ∧ g ≠ 0 ∧ w f - w g = 1
```

Accepted mathematics says:

> “the subgroup of `ℤ` generated by all differences `w(f)−w(g)` is `ℤ`.”

Under multiplicativity the Lean condition is plausibly equivalent or slightly stronger, but it should be stated as the generated-subgroup condition at the trust boundary.

## Degeneracy and vacuity findings

The package is not vacuous through an empty stage, empty weight set, trivial field, or zero residual:

- A `Field` is nontrivial.
- `hRne` excludes `R f = 0` for nonzero `f`.
- `hvalgrp` supplies nonzero witnesses.
- Since `1 ∈ C`, `hWS` forces at least one weight into `weightSet`.
- Every subgroup contains `1`, so S6a has at least a scalar witness.

The actual danger is not emptiness but **pathological non-mathematical stages** satisfying the weakened axioms.

There are also three direct vacuity collapses:

1. `L2_iaugRoot` assumes both `σ.w σ.Φ = 0` and the stage field `σ.w σ.Φ = σ.h`, while `1 ≤ σ.h`.
2. `Algebra.adjoin F {zbar}` is the whole ambient field.
3. `OrdPsiEq Polynomial.X` is always false in a Laurent ring because `X` maps to the invertible monomial `T 1`.

## The 59 statements

| ID | Verdict | Lean versus accepted mathematics |
|---|---|---|
| `L0.GRa` | OK | Correct closure of Laurent monomial units. |
| `L0.GRb` | OK | Correct independence of two distinct Laurent exponents. |
| `L0.GRc` | OK | Correct evaluation formula. |
| `L0.GRd` | OK | Correct nonvanishing of an evaluated Laurent monomial unit. |
| `L0.GRe` | OK | Correct power consequence of residual multiplicativity. |
| `L0.GRf` | OK | Correct distinct-ψ-order lemma in `F[z^{±1}]`. |
| `L0.GRg` | IMPRECISE | Lean permits `g = 0`; D.3 assumes `g ≥ 1`. The hypotheses become impossible for nonzero `x`, so this is harmless but should be typed. |
| `L0.FactA_exists` | OK | Correct existence of monic development. |
| `L0.FactB_unique` | IMPRECISE | Omits the accepted positive-degree key condition. It is harmless as a stronger general uniqueness statement, but mismatches the declared Fact A/B scope. |
| `L1.gaussVal` | OK | Correct base Gauss multiplicativity claim. |
| `L1.baseWeight` | FAITHLESS | Lean: arbitrary `φ e h`. Math: multiplicativity uses monic key, irreducible reduction, positive coprime read index. These hypotheses are absent. |
| `L1.baseResidual` | FAITHLESS | Lean: arbitrary `φ e h emb`. Math: `gr A ≅ F_Q[π,y]` and multiplicativity require the accepted base-key hypotheses. |
| `L1.baseStage_exists` | FAITHLESS | Lean assumes `p^deg φ ∣ card F`. Math needs an embedding of `F_{p^d}` into the ambient field, which requires `d ∣ [F:F_p]`, not merely `d ≤ [F:F_p]`. Example: degree 2 need not embed in `F_{p^3}`. |
| `L1.base_nonvacuity_gate` | FAITHLESS | It witnesses only the weakened `Stage`; it does not gate S3, S4, the T-vector, correct S5 positions, or the threshold. |
| `L2.anchorCong` | FAITHLESS | Lean must conclude `e ∣ j'−j`, but `Stage` never asserts coefficient weights lie in `eℤ`. Math explicitly uses `w(B)=e·w_prev(B)`. |
| `L2.keyResidualPow` | OK | Correct scoped consequence of the pinned residual axiom. |
| `L2.strideRule` | OK | Correct multiplicative consequence `R(BΦ^j)=R(B)z^{sj}`. |
| `L2.widthBound` | FAITHLESS | Math uses S3, coefficient-scale divisibility, and correct S5 positions. All are absent or wrong in `Stage`. |
| `L2.psiNotDvd` | FAITHLESS | Depends on the unencoded width theorem; weakened stages can have wide residuals. |
| `L2.P6i` | FAITHLESS | Lean states kernel-zero plus conditional binary addition. Math requires per-piece additive, **`F_Q`-linear**, injective maps with the stated slot-image description. |
| `L2.P6ii` | FAITHLESS | Lean merely says an arbitrary equivalence preserves cardinality. Math says a `k`-equation unitriangular digit system has the nominal product mass. No equations, ordering, alphabets, or `k` appear. |
| `L2.iaugRoot` | FAITHLESS | Lean assumes `σ.w σ.Φ=0`; `Stage.hwΦ` and `hh` force it to be positive. The theorem is vacuous. |
| `L2.iaugStep` | FLAGGED-OK | Lean proves only the landing chord inequality. No manifest theorem derives the full convexity/every-next-side conclusion from it; consumers take `IAug` separately. Acceptable as a scoped chord lemma, not as the full D.4 invariant. |
| `L2.iaugRecenter` | FAITHLESS | Lean transports an already-assumed `IAug` using equal weights. Math derives the new invariant from RS landing and convexity in the primed frame. |
| `L3.liftExists` | FAITHLESS | Adds `resUnits=⊤`, explicit threshold, and weight-membership assumptions; returns only the weak `IsStandardLift`, not the displayed lift. The missing stage strength is smuggled in as hypotheses. |
| `L3.liftWeight` | FAITHLESS | Math derives `w(Φ̂)=ehg` from equal-weight displayed slots. Lean’s `IsStandardLift` does not assert those slots or the weight. |
| `L3.liftResidual` | OK | Faithful projection of the residual identity, though it does not validate the construction. |
| `L3.K1` | FAITHLESS | The conclusion is correct for the accepted lift, but Lean’s weak lift predicate and weak `Stage` do not provide the width/ψ-order argument. |
| `L3.digPrime_nonzero` | FAITHLESS | Correct only after D.3’s width theorem. It also uses the ambient-root typing that forces irreducible `ψ` to be linear. |
| `L3.DIV` | FAITHLESS | The mathematical conclusion is right, but the hypotheses lack a faithful width/K1/extension setup; the ambient-root typing again collapses to `g=1`. |
| `L4.TRANSi` | FAITHLESS | Lean assumes only a slot-minimum weight and IAug. Math’s proof also critically uses DIV for products of coefficients and the standard lift. |
| `L4.TRANSii` | OK | Correct coefficient-slot scaling consequence as scoped. |
| `L4.TRANSiii` | FAITHLESS | Lean omits irreducibility, `ψ≠z`, degree matching, and a residue root/field. Math proves domainhood using nonzero `dig'` products in `F'`. |
| `L4.TRANSiv` | OK | Correct scoped outgoing-key nonvanishing claim, subject to its explicit root hypotheses. |
| `L4.TRANSv` | FAITHLESS | Lean: `a ∈ Algebra.adjoin F {zbar}`. Math: `a ∈ K(zbar)` for the **current proper subfield** `K`. Lean’s condition is automatic and does not express the new coefficient field. |
| `L4.TRANSvi` | FAITHLESS | Lean only restates `σ'.hRΦ`. Math requires fixed-`Y'` lines, transported `V'`, `z'=V'^{-h'}Y'^{e'}`, exponent group, and `L'₀=F'[z'^{±1}]`. |
| `L4.TRANSvii` | FAITHLESS | Lean only restates `σ'.hS5`. Math constructs the transported exponent-vector `T'` and then proves S5'. |
| `L4.TRANSviii_a` | FAITHLESS | Lean records only the projected weight union. Math’s S6a' also includes forced positions and constant-`F_Qˣ` single-slot realizers. |
| `L4.TRANSviii_b` | FAITHLESS | Uses the old `weightSet`, arbitrary `thr`, and vacuous self-adjoin condition. It does not state the clean parent-key threshold or the current-subfield extension. |
| `L4.TRANSstage` | FAITHLESS | Produces another `Stage p F` without a root, current subfield, residue extension, transported `O`, threshold, or T-vector. For degree `g>1`, it entirely omits `F→F'`. |
| `L5.landBox` | FAITHLESS | The displayed inequality matches D.8, but it is quantified over weakened stages/lifts for which K1 and the width argument are absent. |
| `L5.landVertex` | FAITHLESS | Same issue: correct target formula, insufficient and semantically broader hypotheses. |
| `L5.landVertexDigit` | FAITHLESS | The normalization exponent is correct, but the theorem relies on the unencoded width/K1 and degenerate ambient-root setup. |
| `L5.landTransport` | FLAGGED-OK | This is determinacy only: equality of all slot residuals implies equality of total residuals. No manifest theorem consumes a triangular `Equiv`; the actual ledger connection is absent. Acceptable only as the blueprint’s declared weak lemma, not as D.8 TRANSPORT. |
| `L5.landTwoSided` | FAITHLESS | Lean RHS contains only BOX and weight-minimal VERTEX. Math’s landing cylinder also contains the pinned vertex unit and higher-slot triangular transport of the stratum’s pattern. |
| `L5.realRecursion` | OK | Correct scoped weight-set recursion, given `weightSet` exactness. |
| `L5.realCofin` | FAITHLESS | Lean assumes `e ∣ W`; then `j=0` and its own `hWS` already solve the claim. Math uses `j=0,…,e−1` to fill **all residue classes**, not only existing multiples of `e`. |
| `L5.realDomination` | FAITHLESS | Lean makes `fr` a lower bound for every coefficient weight. Math’s `f_r` is the onset of a cofinite tail, not the global minimum. Since `w(1)=0`, Lean’s hypothesis forces `fr≤0` and trivializes the conclusion. |
| `L5.realConclusion` | FAITHLESS | Lean directly assumes threshold clearance and weight membership at every `W≥fr`. Math derives realizability from D.9’s cofinite recursion, domination, IAug, and S6b. It also assumes position `T 0` without `e=1 ⇒ t=0`. |
| `L5.recSpecies` | FAITHLESS | The `e'=1` direction needs REAL/S6b and IAug to realize a coefficient of the required weight. None is assumed. It also omits positivity of the read index. |
| `L5.recVV` | FAITHLESS | Both conclusions are already contained in `IsRecentering` or the assumed target `Stage`. Math constructs K1 and proves `v=v'`; Lean is circular. |
| `L5.recLiftIndep` | FAITHLESS | `IsRecentering` imposes no relation between `σ1.R` and `σ2.R`. It also quantifies arbitrary `f,zbar`, exceeding the accepted “graded data at read heights” scope. |
| `L5.recSubst` | FAITHLESS | `IsRecentering` contains no cross-stage residual or common-localization identity, so the evaluation equality is unsupported. It is also weaker than the Laurent substitution identity. |
| `L5.recRSland` | FAITHLESS | RHS uses `OrdPsiEq Polynomial.X`. In `LaurentPolynomial`, `toLaurent X = T 1` is a unit, so every power divides every element and `OrdPsiEq X x μ` is always false. |
| `L5.recTRANSRS` | FAITHLESS | Constructs only an arbitrary weakened `Stage` satisfying `IsRecentering`; it does not preserve the representatives, T-vector, coefficient field, S5, S6, or residual substitution. |
| `L6.moveReduceCommute` | OK | Correct compatibility of development with coefficient reduction. |
| `L6.moveAffineBij` | FAITHLESS | Lean states only injectivity: equal developments imply `f=g`. Math requires an affine unitriangular bijection, including existence, digit triangularity, and reduction compatibility. |
| `L6.ledgerCount` | FLAGGED-OK | Correct for the declared single uniform `p^{-k}` model, assuming the equivalence. No manifest consumer needs varying field alphabets. It is not the full D.11 product-of-alphabet-factors theorem. |
| `L6.measureExact` | FAITHLESS | It assumes the cardinal formula for an arbitrary family of predicates and proves an arithmetic identity. It mentions no move, landing cylinder, unitriangular equations, or stratum-to-cylinder bijection, so it does not state D.11 measure exactness. |

## Quantifier audit

The signatures generally quantify stages and polynomials explicitly; they do not hide “every stage” behind typeclass inference. That part is sound.

The quantifier failure is architectural:

- D.4 says IAug holds **at every read along every history**. Lean has isolated conditional lemmas but no history/read quantifier or induction theorem.
- D.7 constructs the next stage from every accepted side. `L4_TRANSstage` existentially returns a weakened stage without residue growth.
- D.11 concerns every actual move and its actual stratum/cylinder. `L6_ledgerCount` and `L6_measureExact` quantify arbitrary predicates/equivalences instead, with no theorem connecting them to a move.

Prop-valued fields are not intrinsically a problem. The defect is that important axioms are missing and several “proofs” assume a completed target `Stage` and merely project its Prop fields.

## Units unsafe to prove as stated

```text
L1.baseWeight
L1.baseResidual
L1.baseStage_exists
L1.base_nonvacuity_gate

L2.anchorCong
L2.widthBound
L2.psiNotDvd
L2.P6i
L2.P6ii
L2.iaugRoot
L2.iaugRecenter

L3.liftExists
L3.liftWeight
L3.K1
L3.digPrime_nonzero
L3.DIV

L4.TRANSi
L4.TRANSiii
L4.TRANSv
L4.TRANSvi
L4.TRANSvii
L4.TRANSviii_a
L4.TRANSviii_b
L4.TRANSstage

L5.landBox
L5.landVertex
L5.landVertexDigit
L5.landTwoSided
L5.realCofin
L5.realDomination
L5.realConclusion
L5.recSpecies
L5.recVV
L5.recLiftIndep
L5.recSubst
L5.recRSland
L5.recTRANSRS

L6.moveAffineBij
L6.measureExact
```

The decisive issue is that this formalization does not merely abstract away graded-ring implementation details: it erases mathematical state that the induction uses. An arbitrary Laurent-valued residual map, arbitrary scalar subgroup, arbitrary threshold, and unchanged ambient field cannot represent the accepted tower. The self-adjoin typing forces all rooted irreducible descents to be linear, while `OrdPsiEq X` makes recentering landing vacuous. Proving the listed statements would therefore certify consequences of a different and substantially weaker specification, not §B2-DEF rev D-10.
