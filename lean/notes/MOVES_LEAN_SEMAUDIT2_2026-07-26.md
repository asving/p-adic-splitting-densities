## Audit result

**STOP THE LINE.**

Round 2 materially improves the residue-field typing, scale bookkeeping, standard-lift predicate, and polynomial ψ-order. It does not yet encode the accepted induction faithfully. Five structural defects remain, and several transition/landing/REAL statements are either substantially weaker than their cited mathematics or false under their stated hypotheses.

Counts for the 61 statements:

- **29 FAITHLESS**
- **2 IMPRECISE**
- **4 FLAGGED-OK**
- 26 faithful as scoped

Separately, **5 round-1 structural defects remain materially unresolved**: DEF-1, DEF-2 (S4 half), DEF-3, DEF-8 (transition/history half), and DEF-10.

## Structural defect re-audit

| Defect | Round-2 Lean | Judgment |
|---|---|---|
| DEF-1 — S3 absent | `theorem L2_slotDecomp ... : σ.R (∑ ...) = ∑ ...` | **Not genuinely repaired.** This is a residual additivity statement under already-assumed equal-weight hypotheses. It is not the degreewise group isomorphism `gr_γ(A) ≅ ⊕j gr^C_{γ-jh}`, and it does not express slot injectivity or transcendence of `Y`. |
| DEF-2 — S4/current field absent | `K : Subfield F`; `R : ... → LaurentPolynomial ↥K`; `nextField := Subfield.closure (↑σ.K ∪ {zbar})` | **Partially repaired.** The current field and residue growth are now correctly typed. But no coefficient localization, fixed-`Y` line theorem, exponent group, or proof that the declared `K` is `(L^coeff)₀` is encoded. Thus the residue-field-collapse defect is repaired, but the S4 defect remains. |
| DEF-3 — representatives/T-vector absent | `reps : List ...`; `Tvec : List (... × ℤ)`; `hTvec : Tvec.map Prod.fst = reps` | **Not genuinely repaired.** `reps` may be empty, need not contain `p`, and `Tvec` has no product identity relating it to `R`, `T`, `V`, or transport. It is decorative data. |
| DEF-4 — wrong S5 scale | `hStretch ... w B = e * wPrev B`; `T (-t * wPrev B)` | **Repaired.** This is the accepted parent/current scale relation and correct S5 exponent. |
| DEF-5 — missing `e=1` pin | `he1t : e = 1 → t = 0` | **Repaired.** |
| DEF-6 — nonconstant orbit group | `FQ : Subfield F`; `hFQ_le : FQ ≤ K`; `hS6a ... ((c : ↥K) : F) ∈ FQ` | **Repaired locally.** `TRANSstage` also requires `σ'.FQ = σ.FQ`. |
| DEF-7 — incomplete scalar range | `hS6b ... (a : (↥K)ˣ) ...` | **Repaired.** It quantifies all current-field units. |
| DEF-8 — arbitrary threshold | `wPrev Φ < ν` in `hS6b` | **Partially repaired.** The threshold inside a stage is now literal. But `wPrev` is not required to be a parent valuation, and `TRANSstage` does not explicitly establish `σ'.wPrev Φhat = σ.w Φhat`. Consequently the threshold can again become arbitrary during transition. |
| DEF-9 — weak standard lift | `Φhat = Φ^(e*g) + ∑ ... tt k * Φ^(e*k)` with weights and residuals specified | **Repaired.** The displayed lift, absent zero slots, parent weights, and forced residual positions are present. |
| DEF-10 — unrelated recentered stage | `IsRecentering σ σ' ...` relates `w`, `wPrev`, `K`, `FQ`, `weightSet`, and coefficient evaluations | **Not genuinely repaired.** It still starts with an already-complete `σ' : Stage`; does not relate `reps` or `Tvec`; does not state a common-localization residual identity; and only relates `digPrime` on old coefficients. Later statements apply it to arbitrary `f`, exceeding this relation. |
| DEF-11 — value group | `AddSubgroup.closure {...} = ⊤` | **Repaired exactly.** |

### Fresh structural findings

A `Stage` can still represent no genuine OM read:

- `reps := []` and `Tvec := []` satisfy their structural clauses.
- `wPrev` is unconstrained outside the coefficient space and is not asserted to be a valuation.
- `K` is declared to be the coefficient residue field without any localization theorem connecting it to `R`.
- There is no history invariant saying that the current `wPrev`, key, representatives, and residue field came from the preceding stage.
- `R` remains an abstract Laurent-valued operation rather than a residual derived from the claimed exponent vector.

This is not empty-type vacuity; it is **pathological-stage vacuity**: the axioms can describe an abstract residual calculus lacking the tower data the accepted proof transports.

## Round-1 faithless-unit repair audit

| Round-1 unit | New Lean excerpt | Round-2 judgment |
|---|---|---|
| `L1.baseWeight` | `baseWeight φ e h (f * g) = ...` with no hypotheses on `φ,e,h` | **Not repaired.** Monicity, irreducible reduction, positivity, and coprimality remain absent. |
| `L1.baseResidual` | `baseResidual K0 φ e h (f * g) = ...` | **Not repaired.** The base-key and compatible residue-field hypotheses remain absent. |
| `L1.baseStage_exists` | `hirred ...` and `hcardK0 : Nat.card ↥K0 = p ^ φ.natDegree` | **Partially improved but still faithless.** The subfield-cardinality defect is repaired, but the conclusion only produces the weakened `Stage`, not accepted S3/S4/T-vector pinning. |
| `L1.base_nonvacuity_gate` | `∃ σ : Stage 2 (GaloisField 2 2), ...` | **Not repaired.** It gates only the weakened structure. |
| `L2.anchorCong` | Stage now supplies `hStretch` | **Repaired.** Coefficient weights are multiples of `e`, so the accepted congruence argument is available. |
| `L2.widthBound` | `B.natDegree < σ.e * g * σ.Φ.natDegree` | **Repaired.** Correct stretch, S5 exponent, K1, and stride data now suffice. |
| `L2.psiNotDvd` | `hψ : Irreducible ψ`, `hψz : ψ ≠ X` | **Not repaired.** Without `ψ.Monic` or “not associated to `X`”, `ψ = cX`, `c ≠ 1`, satisfies these hypotheses while `toLaurent ψ` is a unit. |
| `L2.P6i` | kernel equivalence plus conditional `R(f+g)=...` | **Not repaired.** Still omits per-piece `F_Q`-linearity and the slot-image description. |
| `L2.P6ii` | `Nat.card {c // cyl (Θ c)} = Nat.card {a // cyl a}` | **Not repaired.** This is cardinality invariance under an arbitrary equivalence, not a `k`-equation unitriangular digit count. |
| `L2.iaugRoot` | `(h' : ℤ) > e' * 0` | **Repaired as G3-scoped arithmetic.** No longer vacuous. |
| `L2.iaugRecenter` | assumes `hbox`, `hvtx`, concludes the chord inequality | **Repaired as a chord lemma.** It no longer transports an already-assumed `IAug`. |
| `L3.liftExists` | returns `IsStandardLift σ ψ g Φhat`; no `resUnits = ⊤` | **Repaired.** `hthr` is the explicit range check and `hS6b` supplies the current-field scalars. |
| `L3.liftWeight` | derives `σ.w Φhat = e*h*g` from the displayed lift | **Repaired.** |
| `L3.K1` | `ψ : Polynomial ↥σ.K`, monic, irreducible, `ψ ≠ X` | **Repaired.** Width and prime-order reasoning now occur over the current field. |
| `L3.digPrime_nonzero` | root lies in ambient `F`, while `ψ` is over `↥σ.K` | **Repaired conditionally.** The former same-field linear collapse is gone. |
| `L3.DIV` | same current-field/root setup and displayed lift | **Repaired.** |
| `L4.TRANSi` | only `IsSlotMinWeight` and `IAug` | **Not repaired.** DIV/standard-lift coefficient multiplication is still absent. Slot-minimum data alone do not make `w'` submultiplicative. |
| `L4.TRANSiii` | `hlift` but no irreducibility/root hypotheses | **Not repaired.** A reducible `ψ` can make coefficient products vanish in the would-be residue quotient. |
| `L4.TRANSv` | `a ∈ σ.nextField zbar → ∃ B ≠ 0, ... digPrime B = a` | **Not repaired; internally impossible at `a=0`.** Zero belongs to `nextField`, while `L3.digPrime_nonzero` says every nonzero coefficient has nonzero digit. |
| `L4.TRANSvi` | conclusion is exactly `σ'.hRΦ` | **Not repaired.** Fixed-`Y'` lines, `V'`, exponent group, and `L'₀` are absent. |
| `L4.TRANSvii` | conclusion is exactly `σ'.hS5` | **Not repaired.** It extracts an assumed field instead of constructing transported `T'`. |
| `L4.TRANSviii_a` | only an equivalence of achievable weights | **Not repaired.** Forced positions and constant-`F_Qˣ` realizers are missing. |
| `L4.TRANSviii_b` | `hthr : σ.wPrev σ.Φ < ν`, but the conclusion omits `w B = ν` | **Not repaired.** It neither realizes the prescribed weight nor uses the correct next-stage threshold `σ.w Φhat`; it also incorrectly demands a nonzero realizer for `a=0`. |
| `L4.TRANSstage` | `σ'.K = σ.nextField zbar` | **Residue growth repaired, full TRANS not repaired.** It returns the weakened stage and omits the critical law `σ'.wPrev Φhat = σ.w Φhat`, genuine T-vector transport, and S4 construction. |
| `L5.landBox` | anchored `OrdPsiPoly` and displayed lift | **Repaired.** |
| `L5.landVertex` | anchored `OrdPsiPoly` and displayed lift | **Repaired.** |
| `L5.landVertexDigit` | factor `zbar^(μ*t*h*g)` | **Repaired.** This is `z̄^{-μm̂}` for `m̂=-thg`. |
| `L5.landTwoSided` | RHS contains only BOX and weight-minimal VERTEX | **Not repaired as D.8 two-sidedness.** The pinned vertex digit and transported higher pattern are absent. |
| `L5.realCofin` | assumes `∀ν, fr ≤ ν → ν ∈ weightSet`, then concludes it for `W` | **Not repaired.** It is a tautological specialization, not the residue-class-filling recursion. |
| `L5.realDomination` | `hbase : wPrev Φ ≤ fr`; `hnext : ∀ν≥fr, ν∈weightSet` | **Not repaired and generally false.** These hypotheses do not imply `h > e*fr`. |
| `L5.realConclusion` | uses `hS6b` plus `he1t` | **Repaired as a direct stage consequence.** |
| `L5.recSpecies` | only `IsSlotMinWeight`; no `IAug`, REAL, or S6b range clearance | **Not repaired.** The `e'=1 → existence` direction lacks the required weight realization. |
| `L5.recVV` | projects weight equality and `σ'.hK1` | **Not repaired.** Still circular because `σ'` is already a full `Stage`. |
| `L5.recLiftIndep` | concludes equality for arbitrary `f` | **Not repaired.** `IsRecentering` relates digits only for `B ∈ C_Φ`; the theorem applies that relation to every polynomial. |
| `L5.recSubst` | arbitrary `f`, evaluation equality | **Not repaired.** No common-localization or cross-stage residual substitution law is present in `IsRecentering`. |
| `L5.recRSland` | polynomial order is fixed, but `a'=μ` is inferred from unrelated anchors | **Not repaired.** The Laurent-unit vacuity is gone, but the needed substitution relation is absent. |
| `L5.recTRANSRS` | `∃ σ' : Stage ..., IsRecentering ...` | **Not repaired.** It must construct a new residual frame, T-vector, representatives, and S4 data, none of which the interface relates. |
| `L6.moveAffineBij` | still concludes only `f = g` from equal developments | **G8-scoped only.** It is injectivity, not itself the affine-unitriangular bijection. |
| `L6.measureExact` | assumes an arbitrary family’s cardinal formula | **Not repaired.** No actual move, stratum/cylinder equivalence, or digit-equation theorem supplies `hcard`. |

## Fresh audit of all 61 statements

| ID | Verdict | Reason |
|---|---|---|
| `L0.GRa` | OK | Correct monomial-unit closure. |
| `L0.GRb` | OK | Correct independence of distinct Laurent exponents. |
| `L0.GRc` | OK | Correct evaluation formula. |
| `L0.GRd` | OK | Correct nonvanishing under a field homomorphism and unit evaluation point. |
| `L0.GRe` | OK | Correct consequence of residual multiplicativity, including `n=0`. |
| `L0.GRf` | OK | Correct distinct-prime-order lemma under its nondivisibility hypotheses. |
| `L0.GRg` | **IMPRECISE** | Still permits `g=0`; then the support-window hypothesis is impossible for nonzero `x`. |
| `L0.FactA_exists` | OK | Correct monic-development existence. |
| `L0.FactB_unique` | **IMPRECISE** | Omits positive key degree; harmless because constant monic keys admit only the trivial development situation. |
| `L1.gaussVal` | OK | Correct base Gauss multiplicativity. |
| `L1.baseWeight` | **FAITHLESS** | Missing base-key/read-index hypotheses. |
| `L1.baseResidual` | **FAITHLESS** | Missing compatible base-field and irreducible-key hypotheses. |
| `L1.baseStage_exists` | **FAITHLESS** | Produces a structurally weakened stage. |
| `L1.base_nonvacuity_gate` | **FAITHLESS** | Does not gate S3/S4/T-vector semantics. |
| `L2.anchorCong` | OK | Correct scale and coprimality argument. |
| `L2.keyResidualPow` | OK | Correct. |
| `L2.strideRule` | OK | Correct. |
| `L2.slotDecomp` | **FAITHLESS** | Residual additivity is not S3 slot decomposition/transcendence. |
| `L2.widthBound` | OK | Correct with the repaired parent scale. |
| `L2.psiNotDvd` | **FAITHLESS** | `ψ ≠ X` does not exclude nonunit scalar multiples of `X`. |
| `L2.P6i` | **FAITHLESS** | Missing `F_Q`-linearity and image description. |
| `L2.P6ii` | **FAITHLESS** | No digit equations, ordering, alphabets, or nominal factor. |
| `L2.iaugRoot` | **FLAGGED-OK** | G3 arithmetic root case only. |
| `L2.iaugStep` | **FLAGGED-OK** | G4 chord inequality only; no full hull invariant. |
| `L2.iaugRecenter` | OK | Correct chord consequence of BOX and VERTEX in the primed frame. |
| `L3.liftExists` | OK | Correct displayed-lift construction, conditional on its range check. |
| `L3.liftMonic` | OK | Correct. |
| `L3.liftWeight` | OK | Correct. |
| `L3.liftResidual` | OK | Correct. |
| `L3.K1` | OK | Correct current-field ψ-order formulation. |
| `L3.digPrime_nonzero` | OK | Correct conditional ambient-root formulation. |
| `L3.DIV` | OK | Correct. |
| `L4.TRANSi` | **FAITHLESS** | Lacks DIV/standard-lift hypotheses. |
| `L4.TRANSii` | OK | Correct coefficient scaling. |
| `L4.TRANSiii` | **FAITHLESS** | Lacks irreducibility/root data needed for domainhood. |
| `L4.TRANSiv` | OK | Correct outgoing-key nonvanishing. |
| `L4.TRANSv` | **FAITHLESS** | Incorrectly requires a nonzero coefficient realizer for `a=0`. |
| `L4.TRANSvi` | **FAITHLESS** | Merely projects `hRΦ`; does not state D.7(vi). |
| `L4.TRANSvii` | **FAITHLESS** | Merely projects `hS5`; does not construct T′. |
| `L4.TRANSviii_a` | **FAITHLESS** | Omits positions and constant-orbit realizers. |
| `L4.TRANSviii_b` | **FAITHLESS** | Omits prescribed weight, uses the wrong transition threshold, mishandles zero. |
| `L4.TRANSstage` | **FAITHLESS** | Full tower transition is not encoded despite correct subfield growth. |
| `L5.landBox` | OK | Correct. |
| `L5.landVertex` | OK | Correct. |
| `L5.landVertexDigit` | OK | Correct normalization factor. |
| `L5.landTransport` | **FAITHLESS** | Equal normalized slot residuals do not determine which slots minimize; slot weights are missing. |
| `L5.landTwoSided` | **FAITHLESS** | Not the full landing cylinder or pinned-pattern correspondence. |
| `L5.realRecursion` | **FAITHLESS** | `Φhat` has no degree relation to `e*g*deg Φ`; the stated equivalence is unsupported. |
| `L5.realCofin` | **FAITHLESS** | Tautologically restates its tail assumption. |
| `L5.realDomination` | **FAITHLESS** | Hypotheses do not imply the conclusion. |
| `L5.realConclusion` | OK | Correct direct S6b/P2 consequence. |
| `L5.recSpecies` | **FAITHLESS** | Reverse direction lacks IAug and REAL/S6b clearance. |
| `L5.recVV` | **FAITHLESS** | Circular extraction from an already-complete target stage. |
| `L5.recLiftIndep` | **FAITHLESS** | Exceeds the coefficient/read-height relation in `IsRecentering`. |
| `L5.recSubst` | **FAITHLESS** | No cross-stage residual substitution law. |
| `L5.recRSland` | **FAITHLESS** | Anchors are not connected by substitution. |
| `L5.recTRANSRS` | **FAITHLESS** | Does not construct the missing residual/localization/vector data. |
| `L6.moveReduceCommute` | **FAITHLESS** | Missing monicity: reduction can lower `deg Φhat`, destroying coefficient-space inequalities. |
| `L6.moveAffineBij` | **FLAGGED-OK** | G8 injective component only; Fact A supplies existence separately. |
| `L6.ledgerCount` | **FLAGGED-OK** | G9 uniform `p^{-k}` model only. |
| `L6.measureExact` | **FAITHLESS** | Arithmetic from an assumed cardinal law, with no theorem connecting the law to an actual move. |

## Declared-gap decisions

- **G1 — unacceptable.** `Tvec` is unconstrained and may be empty. `TRANSstage` claims a full stage while consuming no exponent-vector identity or transport law.
- **G2 — acceptable as scoped.** `nextField zbar` is genuinely `K⟮z̄⟯`; for irreducible `ψ` with a root in `F`, evaluation identifies it with the intended quotient field. Every consuming unit explicitly assumes `zbar : Fˣ` and the root equation. What remains unproved is global availability of such roots for an entire run.
- **G3 — acceptable as scoped.** No unit derives more than the arithmetic root inequality from it.
- **G4 — acceptable as scoped.** `iaugStep` is only the chord lemma, and `TRANSstage` separately assumes `IAug`; it does not silently derive the full hull conclusion.
- **G5 — unacceptable.** `TRANSvi/vii` are projections from an assumed `Stage`, while the Stage structure itself omits S4 and the T-vector product law. `TRANSstage` therefore consumes more semantic package than these units construct.
- **G6 — unacceptable.** `landTransport` is not merely weaker than the carry equivalence; it lacks slot-weight equality and is false for normalized residuals that agree while their weights differ.
- **G7 — unacceptable.** `recLiftIndep` quantifies arbitrary `f`, whereas `IsRecentering` relates evaluations only on old coefficient-space elements. It exceeds the declared read-height scope.
- **G8 — acceptable as a component.** Together with development existence and reduction compatibility it can support the set-level bijection story, although no single theorem states affine unitriangularity.
- **G9 — uniform alphabet collapse acceptable; endpoint use unacceptable.** `ledgerCount` is a sound scoped counting lemma. `measureExact` still assumes the needed cardinal law for arbitrary predicates and never connects it to an actual move.

## Subfield, scale, threshold, and vacuity conclusions

`nextField` is genuinely the note’s `F'` under its explicit root hypothesis. Membership does not collapse to the ambient field unless `K=F`; in that case higher-degree irreducible polynomials simply have no root and the affected transition theorems become inapplicable. Thus ambient-`F` size is a **conditional scope restriction**, not a hidden proof of root existence.

The old/current stretch is correct inside a stage, but transition scale bookkeeping fails at the most important threshold: `L4_TRANSviii_b` checks

```lean
σ.wPrev σ.Φ < ν
```

where the next stage’s S6b threshold should be the parent value

```text
σ.w Φhat = e·h·g.
```

It also fails to assert that the produced coefficient has weight `ν`. `TRANSstage` does not repair this by stating `σ'.wPrev Φhat = σ.w Φhat`.

## Units unsafe to prove as stated

```text
L1.baseWeight
L1.baseResidual
L1.baseStage_exists
L1.base_nonvacuity_gate

L2.slotDecomp
L2.psiNotDvd
L2.P6i
L2.P6ii

L4.TRANSi
L4.TRANSiii
L4.TRANSv
L4.TRANSvi
L4.TRANSvii
L4.TRANSviii_a
L4.TRANSviii_b
L4.TRANSstage

L5.landTransport
L5.landTwoSided
L5.realRecursion
L5.realCofin
L5.realDomination
L5.recSpecies
L5.recVV
L5.recLiftIndep
L5.recSubst
L5.recRSland
L5.recTRANSRS

L6.moveReduceCommute
L6.measureExact
```

The decisive verdict is **STOP THE LINE**. Round 2 fixes the most conspicuous field-extension collapse and several local scale errors, but the induction boundary is still weaker than §B2-DEF: S3 and S4 are not encoded, the T-vector is unconnected decorative data, transition S6b uses the wrong threshold and omits the requested weight, recentering remains circular at the residual-frame level, and the ledger has no theorem connecting actual landing cylinders to its assumed cardinal formula. Proving the unsafe units would therefore certify a residual interface that can be satisfied without representing the accepted OM tower.
