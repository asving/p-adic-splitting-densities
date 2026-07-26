## Round-3 delta audit

**STOP THE LINE.**

Round 3 repairs several local statements, notably the threshold formula, `ψ` monicity, zero handling in `TRANSv`, unitriangular counting, slot-weight determinacy, REAL domination, and reduction monicity. It does not repair the tower interface. The decisive defects are:

- `StageWF.reps_pinned` is not the residual consequence of a transported `T`-vector and is generally false for outgoing keys.
- `CoeffFieldLaw` does not characterize the coefficient localization or its exponent group.
- `TransitionData` contains no `Tvec`/`V'` transport and does not ensure child S3/S4.
- The recentering law is restricted to old coefficients, whereas D.10’s read-height identity applies to every polynomial’s graded residual.
- `recRSland` consumes an arbitrary-`f` cross-frame identity that `IsRecenteringT` does not provide.
- `measureExact` still assumes the move equivalence and cylinder identification instead of deriving them for an actual move.

### Counts for the 29 restated units

- **17 FAITHLESS**
- **1 IMPRECISE**
- **11 FLAGGED-OK**

`FLAGGED-OK` means faithful only at the explicitly stated local scope; it does not certify a full stage transition.

---

## Audit-#2 structural demands

| Demand | Round-3 Lean | Judgment |
|---|---|---|
| DEF-1: genuine S3 | `SlotDecomp` adds the implication `∑ ... = 0 → ∀ j, j < N → B j = 0` | **Definition repaired locally; integration NOT repaired.** This is a reasonable degreewise independence law. But `L2_slotDecomp (σ : Stage ...) : SlotDecomp σ` is unconditional, while neither `Stage` nor `StageWF` contains this law. `TRANSstage` also does not produce `SlotDecomp σ'`. |
| DEF-2: coefficient localization/S4 | `CoeffFieldLaw` asserts realizers, equal-position scalar multiples, and an `AddSubgroup.closure ... = ⊤` | **NOT genuinely repaired.** There is still no coefficient localization object or identification `(L^coeff)₀ ≅ K`. The “fixed line” clause is automatic in the already-flattened `LaurentPolynomial K` codomain. The exponent set is not restricted to coefficient monomials and does not say the exponent group is cyclic modulo `Kˣ`. |
| DEF-3: genuine representatives and `T` vector | `reps_nonempty`, `p_is_rep`, and `reps_pinned` | **NOT genuinely repaired.** Nothing mentions `σ.Tvec`, its exponents, its product, or factorwise transport. Moreover `reps_pinned` is the wrong mathematical consequence: `σ.R ũ = T (-t*wPrev ũ)` forces scalar exactly `1`, while accepted S5/D.7(iv) permits `c·z^k`. |
| DEF-8: transition/history threshold | `child_wPrev : ∀ f, σ'.wPrev f = σ.w f`; `threshold : σ'.wPrev Φhat = σ.w Φhat` | **Threshold genuinely repaired.** The formula and scale are correct. The wider transition/history package remains incomplete because `Tvec`, `V'`, S3, and S4 are not transported. |
| DEF-10: recentering frame/substitution | `RecenterSubstLaw ... B ≠ 0 → inC σ.Φ B → ...` | **NOT genuinely repaired.** This is an evaluation identity only on old coefficients, not a common-localization identity for every residual element. It is too weak for `recRSland`. |
| Current-field residue growth | `child_field : σ'.K = σ.nextField zbar`; `field_grow : σ.K ≤ σ'.K` | **Genuinely repaired as a conditional field-growth law.** Availability of a suitable ambient root remains scoped. |
| Representative history | `child_reps : σ'.reps = σ.reps ++ [σ.Φ]` | **Partially repaired.** List growth is correct, but no exponent-vector entry or transported product accompanies the new representative. |
| S6b threshold and prescribed weight | `hthr : σ.w Φhat < ν`; conclusion includes `a ≠ 0 → ... σ.w B = ν` | **Genuinely repaired locally.** Zero is handled without demanding a nonzero realizer. |
| P6ii digit count | `DigitSystem.solve` depends only on `j < i`; count is `|α|^(n-numPinned)` | **Genuinely repaired at the abstract uniform-alphabet level.** |
| P6i image description | fourth conjunct: `∀ B, ... → IsMonomialUnit (σ.R B)` | **NOT repaired.** “Every coefficient residual is monomial” is not the additive span of the slot images on each graded piece. |
| D.11 move/count connection | hypotheses `hmove`, `hcyl`, and `E` | **NOT repaired as the endpoint.** The actual move equivalence and identification of its landing cylinder are still assumed. |

---

## Fresh-eyes audit of `DefsT.lean`

### 1. `StageWF` still admits pathological non-OM data

Yes.

The only connection to representatives is:

```lean
reps_nonempty : σ.reps ≠ []
p_is_rep : Polynomial.C (p : ℤ_[p]) ∈ σ.reps
reps_pinned : ∀ ũ ∈ σ.reps,
  σ.R ũ = LaurentPolynomial.T (-σ.t * σ.wPrev ũ)
```

This leaves `σ.Tvec` entirely untouched. Its exponents can remain decorative and unrelated to `R`, `T`, `V`, or transition transport.

`wPrev` is now valuation-like, but it is not related globally to the current valuation except in `TransitionData`. Thus an isolated `StageWF` need not be a stage arising in a tower.

`K_gen` is also not a localization theorem:

```lean
σ.K = Subfield.closure
  {x | ∃ B c k, ... ∧ σ.R B = C c * T k ∧ x = c}
```

It defines `K` through scalars already returned by the abstract operation `R`; it does not prove that degree-zero localized coefficient fractions are precisely `K`.

More seriously, `reps_pinned` is too strong for genuine transitions. Accepted D.7(iv) only yields

```text
R(ũ) = c · z^k
```

for a representative. For the outgoing key, for example, `dig'(Φ) = z̄^s` generally has a nontrivial scalar. The new law instead requires scalar `1`. Hence genuine OM stages can fail `StageWF`.

### 2. `TransitionData` still admits pathological children

Yes. It constrains the child’s key, field, parent valuation, side weight, and representative list, but not:

- `SlotDecomp σ'`;
- `CoeffFieldLaw σ'`;
- `σ'.Tvec`;
- the transported `V'`;
- factorwise transport of exponent vectors;
- a relation between the child residual map and the transported vector.

An arbitrary already-constructed `Stage σ'` can satisfy the displayed transition fields while retaining unrelated residual data.

### 3. Threshold law

The threshold itself is correct:

```lean
child_wPrev : ∀ f, σ'.wPrev f = σ.w f
threshold   : σ'.wPrev Φhat = σ.w Φhat
```

and `L4_TRANSviii_b` correctly checks:

```lean
hthr : σ.w Φhat < ν
```

with the prescribed nonzero weight:

```lean
a ≠ 0 → B ≠ 0 ∧ σ.w B = ν
```

This audit-#2 demand is genuinely repaired.

### 4. Recentering substitution scope

The scope is not D.10’s scope.

Accepted D.10 says the common-localization residual equality holds **for every `f`**, while lift independence is limited to the graded/read-height information of that `f`. “Read-height” does not mean “old coefficient space.”

Round 3 instead states:

```lean
B ≠ 0 → inC σ.Φ B →
  σ'.digPrime zbar' B = σ.digPrime zbar B
```

For an `e = 1` coefficient, this is essentially the trivial constant-digit part. It omits the nontrivial substitution on key developments and the anchor factor `(z' + c̃)^a`.

It is also weaker than a polynomial/common-localization identity because it only compares evaluations at unit points. Over a finite field, equality on the available evaluation points need not identify Laurent polynomials.

### 5. `DigitSystem`

`DigitSystem` is faithful to the isolated unitriangular counting lemma:

```lean
solve : (i : Fin n) → ((j : Fin n) → j < i → α) → α
```

Each pinned coordinate is uniquely determined by earlier coordinates, so the nominal count is correct.

It does not encode the bridge from OM developments to these coordinates, reduction compatibility, varying residue-field alphabets, or the actual landing cylinder. Those omissions are acceptable for `L2.P6ii`, but not for `L6.measureExact` as a claimed D.11 endpoint.

---

## Classification of the 29 restated units

| Unit | Classification | Audit |
|---|---|---|
| `L1.baseWeight` | **FLAGGED-OK** | The missing monicity, positive degree, positive read index, coprimality, and irreducible reduction hypotheses are now present. |
| `L1.baseResidual` | **FAITHLESS** | Still omits `1 ≤ e`, `1 ≤ h`, and `gcd e h = 1`; cardinality of `K0` also does not state compatibility with the residue quotient used by the base residual. |
| `L1.baseStage_exists` | **FAITHLESS** | Concludes the defective `StageWF`; in particular its scalar-1 `reps_pinned` law is not accepted S5/T-vector semantics. |
| `L1.base_nonvacuity_gate` | **FAITHLESS** | Gates the same defective layered package, not the accepted base-stage localization/vector data. |
| `L2.slotDecomp` | **FAITHLESS** | Claims `SlotDecomp σ` for every old `Stage`; the hypothesis contains neither `SlotDecomp` nor a construction provenance from which it follows. |
| `L2.psiNotDvd` | **FLAGGED-OK** | `ψ.Monic` now excludes the `cX` counterexample. |
| `L2.P6i` | **FAITHLESS** | Conditional scalar multiplication plus `IsMonomialUnit` is not the per-piece `F_Q`-linear image-as-slot-span theorem. |
| `L2.P6ii` | **FLAGGED-OK** | Correct abstract unitriangular count. |
| `L4.TRANSi` | **FLAGGED-OK** | Standard-lift, irreducibility/root, slot-minimum, and augmentation hypotheses now expose the DIV argument. |
| `L4.TRANSiii` | **FLAGGED-OK** | The missing irreducibility/root and monicity data are present. |
| `L4.TRANSv` | **FLAGGED-OK** | Correctly permits `B = 0` only when `a = 0`; faithful to the local large-weight surjectivity conclusion. |
| `L4.TRANSvi` | **FAITHLESS** | `TransitionData` contains no S4 construction. The theorem attempts to infer `CoeffFieldLaw σ'` from an arbitrary already-complete target stage. |
| `L4.TRANSvii` | **FAITHLESS** | Still verifies the child’s already-assumed `hS5`; it constructs neither `T'` nor transported `V'`/`Tvec`. |
| `L4.TRANSviii_a` | **FAITHLESS** | The realizer conclusion has only `∃ k`; it omits the forced child position `−t'·(γ+jh)` and does not mention the child scale `e'`. |
| `L4.TRANSviii_b` | **FLAGGED-OK** | Correct clean threshold, next-field scalar, zero handling, and prescribed nonzero weight. |
| `L4.TRANSstage` | **FAITHLESS** | Assumes only `StageWF σ`, not parent `SlotDecomp`/`CoeffFieldLaw`, and produces neither for the child. No vector transport is encoded. |
| `L5.landTransport` | **FLAGGED-OK** | Honest determinacy lemma now that both residuals and slot weights are compared. It is not the carry equivalence. |
| `L5.landTwoSided` | **FAITHLESS** | Adds the vertex digit but still contains no higher transported pattern or landing-cylinder parameter. It is not D.8 two-sidedness. |
| `L5.realRecursion` | **FLAGGED-OK** | The standard lift now supplies the required degree relation and the weight union is stated at the correct scale. |
| `L5.realCofin` | **IMPRECISE** | Gives the stronger threshold `W₀ + e·h`; accepted D.9(b) needs `W₀ + (e−1)·h`. It proves eventual cofiniteness but not the sharp bound consumed by the stated domination recursion. |
| `L5.realDomination` | **FLAGGED-OK** | The inductive inequality follows from lift weight, the previous domination hypothesis, and `IAug`. |
| `L5.recSpecies` | **FAITHLESS** | No `g ≥ 1`/irreducibility assumptions are explicit, and the existence direction still lacks a stated REAL/S6b realization hypothesis for the required coefficient weight. |
| `L5.recVV` | **FAITHLESS** | Unchanged circular shape: it starts from an already-complete `σ' : Stage` and `IsRecentering`, then projects equality/K1. |
| `L5.recLiftIndep` | **FAITHLESS** | Restriction to `inC σ.Φ f` avoids the round-2 overquantification but is narrower than D.10’s “every `f`, at read heights” statement. |
| `L5.recSubst` | **FAITHLESS** | Only an old-coefficient evaluation identity; it is not the common-localization substitution for a general residual. |
| `L5.recRSland` | **FAITHLESS** | Applies anchors to arbitrary `f`, but `IsRecenteringT` relates the frames only on old coefficients. No premise connects `σ.R f` to `σ'.R f`. |
| `L5.recTRANSRS` | **FAITHLESS** | Does not assume a well-formed parent and produces neither child S3 nor S4. The residual/localization/vector construction remains absent. |
| `L6.moveReduceCommute` | **FLAGGED-OK** | Monicity now prevents the key degree from dropping on reduction. |
| `L6.measureExact` | **FAITHLESS** | `hmove` and `hcyl` assume exactly the move/cylinder bridge D.11 must obtain from developments and landing. This remains an abstract counting schema. |

---

## Declared R3.3 gaps

- **G1′ — unacceptable.** `StageWF.reps_pinned` neither states nor follows from the exponent-vector product, and it incorrectly forces all representative scalars to `1`. `TRANSstage`, `TRANSvii`, and `recTRANSRS` claim more than this interface constructs.

- **G5′ — unacceptable.** `TransitionData` contains no S4 or `T'` construction. Therefore `TRANSvi` and `TRANSvii` remain projections from an already-complete child rather than post-construction verification of recorded construction data.

- **G6′ — acceptable only for `L5.landTransport`.** Determinacy from equal slot residuals and weights is a valid scoped lemma. It does not repair `L5.landTwoSided`, whose claimed higher-pattern cylinder is absent.

- **G7′ — unacceptable.** The accepted scope is “graded/read-height data on every `f`,” not “only `f ∈ C_Φ`.” `recRSland` directly exceeds the supplied law by using arbitrary `f` and anchored residuals.

- **G9′ — unacceptable for the endpoint.** `L2.P6ii` is sound, but `L6.measureExact` assumes arbitrary `hmove` and `hcyl`; no restated unit instantiates them from an actual OM move.

- **S4 partial — unacceptable.** The new clauses live entirely inside `LaurentPolynomial K`, making the fixed-line clause largely tautological, and they never construct or identify the coefficient localization.

## Units unsafe to prove

```text
L1.baseResidual
L1.baseStage_exists
L1.base_nonvacuity_gate

L2.slotDecomp
L2.P6i

L4.TRANSvi
L4.TRANSvii
L4.TRANSviii_a
L4.TRANSstage

L5.landTwoSided
L5.recSpecies
L5.recVV
L5.recLiftIndep
L5.recSubst
L5.recRSland
L5.recTRANSRS

L6.measureExact
```

`L5.realCofin` may be proved as written, but it must not be used as the sharp D.9(b) bound without restatement.

## Final verdict

**STOP THE LINE.**

Fan-out may continue only on the 11 `FLAGGED-OK` local units, with `L5.realCofin` separately relabeled as a weaker cofiniteness lemma. The 17 listed units must not be proved as certifications of §B2-DEF.
