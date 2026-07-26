# Round-4 semantic-faithfulness audit

## Final gate: **STOP THE LINE**

Round 4 genuinely repairs the recentering substitution scope, the three machine-refuted statements, the species/v=v′ formulations, and several local interfaces. It does **not** repair the central T-vector/localization semantics, and the new carry cylinder is not equivalent to D.8’s Laurent triangular transport.

### Counts for the 20 statements

- **8 FAITHLESS**
- **0 IMPRECISE**
- **12 FLAGGED-OK**

`FLAGGED-OK` means sound only at the stated local or conditional scope, not certification of the full §B2-DEF construction.

---

## 1. Round-3 unsafe units: repaired or not

| Round-3 unsafe unit | Verdict | Audit |
|---|---|---|
| `L1.baseResidual` | **GENUINELY REPAIRED** | Now includes `he`, `hh`, `hcop`, and the specified residue isomorphism `emb : AdjoinRoot ... ≃+* ↥K0`. |
| `L1.baseStage_exists` | **NOT REPAIRED** | It concludes `StageCore`, but `StageCore.tvec` and `StageCore.coeff` remain residual shadows rather than the accepted T/localization data. |
| `L1.base_nonvacuity_gate` | **NOT REPAIRED** | Gates the same semantically incomplete `StageCore`. |
| `L2.slotDecomp` | **GENUINELY REPAIRED LOCALLY** | The missing tie laws are now explicit hypotheses: `hstrict`, `hjump`, and `hneg`. With the existing `Stage` K1/slot infrastructure, this is an honest local derivation target. |
| `L2.P6i` | **NOT REPAIRED** | The purported `F_Q` action does not say multiplication preserves the weight-`γ` piece. Its hypothesis permits `û` of arbitrary weight; the conclusion lacks `σ.w (û * f) = γ`. Thus it does not state an `F_Q`-linear endomorphism of `gr_γ`. |
| `L4.TRANSvi` | **NOT REPAIRED** | `TransitionCore.child_Tvec` and `child_dig` do not entail either global `CoeffFieldLawCore σ'` or `TvecLaw σ'`. |
| `L4.TRANSvii` | **GENUINELY REPAIRED LOCALLY** | It now exposes the parent digit, frame unit, forced position, and history equality. It is essentially verification of `TransitionCore.child_dig`, not a construction of the full child package. |
| `L4.TRANSviii_a` | **NOT REPAIRED** | The fixed `m` before `∀ c` and instantiated position are correct targets, but neither `TransitionCore` nor `StageCore` records the coherence needed to derive that one fixed orbit class for all scalars. |
| `L4.TRANSstage` | **NOT REPAIRED** | It returns a core whose T-vector and coefficient-localization fields are semantically insufficient. It therefore still does not certify the accepted full transition. |
| `L5.landTwoSided` | **NOT REPAIRED** | The executable recursion is polynomial-only, while D.8 transports anchored Laurent slot terms. The cylinder also omits the terminal carry condition. |
| `L5.recSpecies` | **GENUINELY REPAIRED** | It now has positive degree, monicity, irreducibility, and an explicit realization hypothesis `hreal`. |
| `L5.recVV` | **GENUINELY REPAIRED** | No pre-existing child stage is assumed. Both weight equality and K1 are parent-frame conclusions. |
| `L5.recLiftIndep` | **GENUINELY REPAIRED LOCALLY** | Quantifies over every `f` in the transcendental common target. It assumes the two substitution laws, which is appropriate for this comparison lemma. |
| `L5.recSubst` | **GENUINELY REPAIRED AT THE RESIDUAL-DISPLAY SCOPE** | Its conclusion is the correct every-`f` Laurent substitution identity in `RatFunc F`. This does not construct the actual graded common localization, but the displayed identity itself is faithful. |
| `L5.recRSland` | **GENUINELY REPAIRED LOCALLY** | It explicitly consumes `RecenterSubstCore` and displays the `(ζ+c̃)^a` anchor factor. |
| `L5.recTRANSRS` | **NOT REPAIRED AS A FULL-STAGE CERTIFICATION** | It constructs the incomplete `StageCore`; unchanged `Tvec` is insufficient to certify equality of the actual normalizing units. |
| `L6.measureExact` | **NOT FULLY REPAIRED AS D.11; FLAGGED-OK AS A CONDITIONAL COUNTING SCHEMA** | `hmove` is gone, but `hcylN`/`hcylM` still assume a `DigitSystem` presentation of the actual landing cylinder. That is the principal jet-coordinate bridge D.11 is meant to obtain from D.3(e)(ii). |

---

## 2. Fresh-eyes audit of `DefsCore`

### 2.1 `RatFunc` embedding

The map is injective as a Laurent-polynomial representation.

The relevant definition is:

```lean
LaurentPolynomial.eval₂
  ((algebraMap F (RatFunc F)).comp σ.K.subtype)
  (ratX F)
  (σ.R f)
```

Because:

- `σ.K.subtype` is injective;
- a field’s algebra map into `RatFunc F` is injective;
- `RatFunc.X` is transcendental;
- negative Laurent powers are evaluated at the unit `ratX F`;

a nonzero Laurent polynomial cannot vanish under this map. This genuinely repairs round 3’s finite-field-point-evaluation defect.

It is **not**, however, a construction of D.10’s actual

```text
gr_v(A)[⟨U ∪ {Y_Φ̂,Y_Φ′}⟩⁻¹].
```

There is no homomorphism from that graded localization into `RatFunc F`, nor a proof that the two abstract `Stage.R` maps arise from the same initial-form map. Therefore:

- faithful for comparing complete Laurent residual displays: **yes**;
- faithful construction of the accepted common localization: **no**.

That limitation is acceptable for `recLiftIndep`, `recSubst`, and `recRSland`, but not as a replacement for the missing tower provenance.

### 2.2 `TvecLaw`: only a shadow

The definition is:

```lean
def TvecLaw (σ : Stage p F) : Prop :=
  σ.w σ.tvecNum = σ.w σ.tvecDen + 1 ∧
  σ.R σ.tvecNum = σ.R σ.tvecDen
```

In an already genuine graded model with

```text
R(f) = [f]·T⁻ʷ⁽ᶠ⁾,
```

this equation is a valid consequence of

```text
[tvecNum]/[tvecDen] = T.
```

But the converse used in the blueprint presupposes exactly the structure that `DefsCore` does not build:

- actual initial forms `[f]`;
- their localization;
- the element `T`;
- the identity defining `R` from that `T`.

Inside an abstract `Stage`, equality of two residual values at two literal polynomials cannot identify an absent localized element. It constrains two evaluations only.

There is a second independent defect: nothing states that entries of `σ.Tvec` are precisely supported on `σ.reps`. `StageCore` has:

```lean
reps_nonempty
p_is_rep
tvec : TvecLaw σ
```

but no condition resembling:

```text
∀ (u,a) ∈ σ.Tvec, u ∈ σ.reps
```

or equality of the vector’s support with the representative history.

**Verdict:** `TvecLaw` does not pin the product law. It is a necessary residual shadow.

### 2.3 `CoeffFieldLawCore`

This is stronger than round 3’s tautological fixed-line clauses, but it still does not characterize the accepted localization.

The inclusion clause

```lean
σ.R f = LaurentPolynomial.C d * σ.R g
```

for equal-weight coefficient products is meaningful. But the exponent clause

```lean
AddSubgroup.closure {n : ℤ | ... n = k - k'} = ⊤
```

only proves that the observed integer positions generate `ℤ`. Rank one has already been imposed by mapping everything into the one-variable codomain `LaurentPolynomial K`.

It does not establish:

- that every degree-zero coefficient-localization fraction is represented;
- that every equal-weight unit monomial has a monomial residual;
- that no additional exponent direction was erased by `R`;
- a localization object or its universal property.

Thus a non-OM model can satisfy this law by arranging its flattened residual outputs appropriately.

### 2.4 Can a pathological non-OM `StageCore` satisfy the package?

**Yes.**

The simplest remaining freedom is an unrelated T-vector:

- choose `σ.Tvec` entries not belonging to `σ.reps`;
- arrange the two aggregate polynomials to have a weight gap of one;
- arrange `R(tvecNum) = R(tvecDen)`.

That satisfies `StageCore.tvec` without any transported representative product being the actual normalizing unit.

Likewise, `CoeffFieldLawCore` sees only flattened residual positions, not the source localization. Therefore `StageCore` is a useful collection of necessary residual laws, but it is not a provenance certificate for genuine OM stages.

### 2.5 `carryDigit` and D.8

The elementary recurrence is algebraically correct for polynomial coefficients:

```lean
digit := (cj + carry) %ₘ ψ
carry := (cj + carry) /ₘ ψ
```

This computes the canonical digits of

```text
Σ c_j ψ^j
```

provided every `c_j` is a polynomial and the final overflow is handled.

D.8’s actual terms are

```text
z^(j·m̂-a) R(B_j),
```

which are generally Laurent polynomials. Anchoring makes the total residual polynomial; it does not imply that each summand is individually polynomial. Negative Laurent powers can cancel between different ψ-level contributions.

`LandingCylinder` demands:

```lean
Polynomial.toLaurent (canch j)
  = T (...) * σ.R (B j)
```

so it silently restricts every anchored slot term to be polynomial. That restriction is not in D.8.

There is also no condition that the last carry vanishes:

```text
(carryRec ψ canch (N-1)).2 = 0.
```

Consequently the first `N` digits may agree while an unrecorded `ψ^N` overflow remains. This breaks the reverse implication to the finite `IsDevelopment ψ Ranch Cdig N`.

**Verdict:** the recurrence captures one polynomial shadow of the downward carry calculation, not D.8’s full triangular bijection.

### 2.6 `prevIaug`

The placement is correct:

```lean
prevIaug : (σ.e : ℤ) * σ.wPrev σ.Φ < (σ.h : ℤ)
```

This is precisely the parent-scale form of

```text
h/e > wPrev(Φ),
```

needed when the S6b recursion descends one stage before the new augmented weight exists.

It belongs in the parent stage core consumed by `TRANSviii_b`. Base construction and transition/recentering transport still require proofs, but the interface location and inequality are faithful.

---

## 3. The three machine-checked corrections

### `L4.TRANSviii_b`

**GENUINELY REPAIRED.**

The corrected statement consumes:

```lean
hcore : StageCore σ
```

and hence:

```lean
hcore.prevIaug :
  (σ.e : ℤ) * σ.wPrev σ.Φ < (σ.h : ℤ)
```

The clean threshold remains correct:

```lean
hthr : σ.w Φhat < ν
```

and zero handling is honest:

```lean
a ≠ 0 → B ≠ 0 ∧ σ.w B = ν.
```

### `L5.landTransport`

**GENUINELY REPAIRED AS A DETERMINACY LEMMA.**

It now has the machine-pinned missing data:

```lean
hlift : IsStandardLift σ ψ g Φhat
hK1 : K1At σ.w Φhat (σ.w Φhat)
hcore : StageCore σ
```

Together with equality of both slot residuals and slot weights, these eliminate the previous total-minimal-block cancellation counterexample.

This remains determinacy only; it does not prove D.8 transport two-sidedness.

### `L6.moveReduceCommute`

**GENUINELY REPAIRED.**

The added assumptions are exactly the needed ones:

```lean
hmon : Φhat.Monic
hM : 1 ≤ M
```

`M ≥ 1` prevents the coefficient ring from collapsing to `ZMod 1`, and monicity prevents the key degree from dropping after reduction.

---

## 4. Declared round-3 gaps

| Gap | Round-4 verdict |
|---|---|
| **G1′ — T vector** | **NOT repaired.** `child_Tvec` is a useful list equation, but `TvecLaw` remains only a two-evaluation shadow and vector support is not tied to `reps`. |
| **G5′ — child S4/T′** | **NOT repaired.** `TransitionCore` does not contain enough coherent information to imply `CoeffFieldLawCore σ'` or `TvecLaw σ'`; `TRANSvi` overclaims. |
| **G6′ — transport** | **Correction repaired for `landTransport`; not repaired for `landTwoSided`.** Polynomial carry data are not the full anchored Laurent transport. |
| **G7′ — recentering scope** | **Repaired.** `RecenterSubstCore` quantifies over every polynomial and uses a transcendental target. |
| **G9′ — endpoint** | **Partially repaired.** The arbitrary `hmove` hypothesis is gone. The actual jet-coordinate/cylinder presentation remains assumed by `hcylN` and `hcylM`; acceptable only for a conditional counting theorem. |
| **S4 partial** | **NOT repaired.** The new clauses are less tautological, but still characterize only the flattened residual image, not the actual coefficient localization. |

---

## 5. Classification of the 20 statements

| Unit | Classification |
|---|---|
| `L1.baseResidual` | **FLAGGED-OK** |
| `L1.baseStage_exists` | **FAITHLESS** |
| `L1.base_nonvacuity_gate` | **FAITHLESS** |
| `L2.slotDecomp` | **FLAGGED-OK** |
| `L2.P6i` | **FAITHLESS** |
| `L4.TRANSvi` | **FAITHLESS** |
| `L4.TRANSvii` | **FLAGGED-OK** |
| `L4.TRANSviii_a` | **FAITHLESS** |
| `L4.TRANSstage` | **FAITHLESS** |
| `L5.landTwoSided` | **FAITHLESS** |
| `L5.recSpecies` | **FLAGGED-OK** |
| `L5.recVV` | **FLAGGED-OK** |
| `L5.recLiftIndep` | **FLAGGED-OK** |
| `L5.recSubst` | **FLAGGED-OK** |
| `L5.recRSland` | **FLAGGED-OK** |
| `L5.recTRANSRS` | **FAITHLESS** |
| `L6.measureExact` | **FLAGGED-OK** — conditional only |
| `L4.TRANSviii_b` | **FLAGGED-OK** |
| `L5.landTransport` | **FLAGGED-OK** |
| `L6.moveReduceCommute` | **FLAGGED-OK** |

---

## 6. R4.5 impossible-list scope

The acceptable omissions are consumer-dependent:

- Not constructing the full graded ring/localization is **FLAGGED-OK** for the three recentering statements whose conclusions are only Laurent identities in an injective `RatFunc` representation.
- Assuming a named unitriangular `DigitSystem` presentation of the actual cylinder is **FLAGGED-OK** for `L6.measureExact` as a conditional counting schema.
- The same omissions are **not acceptable** for `StageCore`, `TRANSstage`, `TRANSvi`, or `recTRANSRS`, because those units claim to certify the full S4/T′ stage package.
- Replacing Laurent carry transport with ordinary polynomial division is not an “impossible object” omission; it changes the mathematical locus and is **FAITHLESS**.

---

## Units unsafe to prove as certifications of §B2-DEF

```text
L1.baseStage_exists
L1.base_nonvacuity_gate

L2.P6i

L4.TRANSvi
L4.TRANSviii_a
L4.TRANSstage

L5.landTwoSided
L5.recTRANSRS
```

`L6.measureExact` may be proved only with an explicit label such as “conditional on the supplied jet-coordinate presentations”; it must not be advertised as deriving the complete D.11 endpoint.

## Explicit verdict

**STOP THE LINE.**

Fan-out may proceed on the 12 `FLAGGED-OK` units at their stated scopes. It must not proceed on the eight listed unsafe units until:

1. the T-vector is tied to genuine representatives and to an actual localized normalizing unit, or an interface genuinely equivalent to that construction;
2. S4 identifies the coefficient localization rather than only its flattened residual image;
3. D.8 transport operates on Laurent slot terms and records terminal carry/no-overflow; and
4. the P6i scalar action explicitly preserves the fixed graded piece.
