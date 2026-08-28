# Verdict A8D — replace the GN payload leg by the direct key route

**Date:** 2026-08-28
**Adjudication:** **choose (β)**.  Retire `GNCitePayload` from the live `RecenterStep`
premise and make the same realization export the recentered polynomial as a key for its
concrete deep valuation, with the key-irreducibility law proved directly.  Route (α) is not
blocked in principle, but it retains completion, selected-factor, descent, slope, and
multiplicity work which the E.40 consumer does not use.

No owner's-paper citation is used in this adjudication.

## 1. What the consumer actually needs

`MP1CarrierLive` preserves E.40's exact conclusion:

```lean
Nonempty (Ladder.MidPeelEmission B B')
```

Its fields split without any GN factor theorem:

| `MidPeelEmission` field | exact supplier |
|---|---|
| `quot`, `hkey`, `hpeel`, `hmass`, `hthr`, `iface` | `MP1StepCore B B'` |
| `hirr : Irreducible (B'.Φ.map (algebraMap O (FractionRing O)))` | direct key proof for `B'.Φ`, followed by the landed monic Gauss equivalence |
| `hef : B'.Φ.natDegree = C.eC * C.fC` | `B'.hΦdeg.trans C.hef`; no key theorem and no cite |

Thus the only mathematical payload beyond the peel core is ordinary irreducibility of the
peeled key.  A valuation-key proof is sufficient, because the standard factorization
argument turns

```text
Monic ∧ MuMinimal ∧ MuPrime
```

into `Irreducible` in `O[x]`: apply μ-primality to the self μ-divisibility of
`g = a*b`, and use μ-minimality to exclude either positive-degree factor.  Monicity makes a
degree-zero factor a unit.  The final fraction-field statement is exactly
`Polynomial.Monic.irreducible_iff_irreducible_map_fraction_map`.

This last bridge was shape-checked as
`A8DProbe.irreducible_of_isMuKey`; it needs no residual-calculus hypothesis beyond the
three `IsMuKey` conjuncts.

## 2. Why β wins end to end

Route (α) would first have to replace the false identification
`selected g_{λ,ψ} = B'.Φ` by two different polynomials, build the completed selected
factor and its descent, and then prove that this separate factor makes `B'.Φ` a key.  Even
after all of that, E.40 discards the selected factor, slope, and residual multiplicity and
retains only `hirr`.

Route (β) starts at the exact datum already produced by the deep operator stacks: the
degree-16 `leaf` has its normalized residual `X+1`, and D4-13--D4-15 already promise the
deep key predicate, criterion, and irreducibility theorem.  It therefore removes the
structural G9 contradiction and four GN-only research nodes without weakening the E.40
conclusion.

There is **no genuine obstruction** to β.  There is, however, an important scope finding:
`C134p1d.isMuKey_of_isTestKey` cannot be instantiated definitionally at absolute μ₄ or μ₅.
Its signature is generic over a `KeyFrame` and one `LevelDatum`, but its valuation and
residual are concretely

```text
dvSupp F · L.u L.ℓ
dvResPoly F H₀ hpin · L.u L.ℓ.
```

The planned μ₄ and μ₅ operators are recursive `g8`/`keyAt4` developments, not instances of
those exact terms.  What generalizes is the proof architecture; the operator-facing lemmas
need μ₄/μ₅ twins.  Those twins coincide with work already assigned to the D3/D4 key tails
and the L2E product engine.  β is therefore **unblocked but not already landed** at the deep
occurrence.

## 3. Leg-by-leg generalization table

Legend: **LANDED** means an exact current declaration applies; **TWIN NEEDED** means the
argument is valid but the absolute-depth operator has a different Lean type; **BLOCKED**
would mean a missing mathematical mechanism rather than an unported theorem.  No row is
blocked.

| leg | one-`LevelDatum` theorem (`C134p1d`) | μ₄ at `(e',f',u')=(2,1,85)` | μ₅ refinement at `(1,1,171)` |
|---|---|---|---|
| monic | **LANDED.** `IsTestKey` clause 1, used as `hΨ.1`. | **TWIN NEEDED, routine.** D3-14 supplies monicity of `g16`; D3-15/16 must expose it in the μ₄ key predicate/criterion. | **TWIN NEEDED, routine.** D4-12 supplies `leaf.Monic`; D4-14 consumes it. |
| μ-minimality: positivity | **LANDED.** `natDegree_pos_of_isTestKey`; degree is `L.keyDeg₂`. | **TWIN NEEDED, numeric.** Recipe degree is 16 from `2*1*8`; D3-14 pins it. | **TWIN NEEDED, numeric.** Recipe degree is 16 from `1*1*16`; D4-12 pins it. |
| μ-minimality: below-key residual cannot be divisible | **LANDED.** `not_residual_dvd_of_natDegree_lt`, using B.04 plus C.26's exact residual degree and nonzero constant coefficient. | **TWIN NEEDED, already in the D3 tail.** The literal C.26 theorem does not type at μ₄.  D3-08/12 plus L2E-03/09 must prove the two-slot low-degree residual is a nonzero constant/unit; D3-15 then obtains the contradiction. | **TWIN NEEDED, simpler.** A remainder below degree 16 has only slot 0 in the `keyAt4`-development; D4-08/09 supply nonzero scalar/normalized read and D4-13 packages the contradiction. |
| μ-divisibility → residual divisibility | **LANDED.** `residual_dvd_of_muDvd`, via `C134p1.not_muDvd_of_residual_notdvd`. | **TWIN NEEDED.** D3-15's planned normalized-residual divisibility equivalence is the stronger required output. | **TWIN NEEDED.** D4-13's planned equivalence is the required output. |
| μ-primality head | **LANDED.** `residual_dvd_or_of_muDvd_mul`; product residual comes from frame-generic Theorem M clause 3, `C133mh3.dvResPoly_mul_gen`. | **TWIN NEEDED; same L2E root.** The landed theorem's types do not mention μ₄.  L2E-09 gives coefficientwise level-2 multiplication, D3-12 gives μ₄ normalized multiplication, and primality of the irreducible residual then splits divisibility. | **TWIN NEEDED; recursive instance.** D4-07/09 give untwisted μ₅ normalized multiplication from the μ₄ product law; the same prime-divisor step applies. |
| residual lift | **LANDED.** `muDvd_of_residual_dvd`; quotient/remainder plus the generic line-read tie transfer. | **TWIN NEEDED, not blocked.** The polynomial quotient/remainder split is level-free.  At this concrete degree the stronger landed `C132kp1.S2Mu3Dvd_iff_mu3NormRes_dvd` two-slot pattern is the closer template; D3-15 owns the μ₄ twin, fed by D3-08/12 and L2E. | **TWIN NEEDED, not blocked.** D4-13 owns the one-slot μ₅ twin.  With `ℓ=1` and remainder degree `<16`, the tie contradiction is simpler than P1D's general `lineRes` branch. |
| assemble `IsMuKey` | **LANDED.** `muPrime_of_isTestKey` and `isMuKey_of_isTestKey`. | **TWIN NEEDED.** D3-15/16; no literature premise. | **TWIN NEEDED.** D4-13/14; no literature premise. |
| valuation key → `Irreducible O[x]` | The exact `C134dv2g.IsMuKey` bridge is **SHAPE-VALIDATED** in `A8D_probe.lean`; the identical argument is landed for the concrete lower predicates as `C130fd0.s2_key_irreducible` and `C132kp5.s2Mu3_key_irreducible`. | **TWIN NEEDED, algebra-only.** Put the generic bridge in the A-I.8 support file or instantiate it in D3-16. | **TWIN NEEDED, algebra-only.** Reuse the same bridge in D4-15. |
| `Irreducible O[x]` → E.40 `hirr` | **LANDED.** Monic Gauss equivalence. | **LANDED once the μ₄ key theorem exists.** | **LANDED once the μ₅ leaf theorem exists.** |

Theorem M is therefore frame-generic exactly where P1D uses it, but not magically
absolute-depth generic.  L2E-09 is its μ₄ operator twin; D4-07/09 are the μ₅ recursive
instance.  Likewise C.26 and the P1D remainder mechanism are architecturally generic but
need operator-facing twins.  Those are the same D3-15/D4-13 key-tail obligations already
present in §6, not a new analytic campaign.

## 4. A-I.8 amendment draft — exact Lean diff shape

This is a **draft only**; no landed Lean or leanspec edit was made.

1. Retire `GNCitePayload` from the live dependency surface.  It may remain byte-frozen as a
   historical declaration for one compatibility pass, but no production theorem may use it.
2. Add a direct, same-chain payload:

```lean
structure DirectKeyPayload ... (A : ChainRealization ...) (phi : Polynomial O) where
  e' f' u' : ℕ
  source : FGMNSourceData core.T A.keys e' f' u'
  keyPolynomial : source.keyPolynomial phi
  key_irreducible : ∀ g, source.keyPolynomial g → g.Monic → Irreducible g
```

The enactment review must record that, at the deep instance, `key_irreducible` is filled by
D3/D4's direct `IsMuKey → Irreducible` theorem.  The payload deliberately does not demand
the other twelve `FGMNSourceLaws` fields, and it is not an authorization to install a
literature axiom.

3. In `RecenterStep`, replace exactly

```diff
- (∃ (kRes : Type) (_fRes : Field kRes),
-   Nonempty (GNCitePayload (Kt := Kt) (L := L) A B.F B'.Φ kRes)) ∧
- Nonempty (MP1StepCore B B')
+ Nonempty (DirectKeyPayload (Kt := Kt) (L := L) A B'.Φ) ∧
+ ∃ step : MP1StepCore B B',
+   step.quot.F = B'.F ∧
+   B'.T = B.T ∧
+   step.quot.T = B.T ∧
+   B.F = B'.Φ * B'.F
```

The existing `Lambda ≠ 0`, degree, recenter equality, divisor, slot/block/gauge views, and
single existential owner remain unchanged.  `step.hkey`, `step.hmass`, and `step.iface`
remain the quotient key/mass/interface fields.  The four added equalities are DWR's
anti-splicing bindings; some are derivable from `step.hpeel`/`step.hthr`, but carrying them
keeps the producer contract explicit.

4. `MP1CarrierLive` changes only the type of its final producer premise from
`RecenterStep` to the amended direct `RecenterStep`; its quantifier prefix and E.40
conclusion are byte-preserved.
5. Add the compiler theorem `midPeelEmission_of_recenterStepDirect`.  It projects items
2--4 from `MP1StepCore`, applies the direct payload's `key_irreducible` law, applies
monic Gauss for `hirr`, and fills `hef` by `B'.hΦdeg.trans C.hef`.

The exact proposed declarations and compiler elaborate in
`leanfinal/scratch/A8D_probe.lean`, with no `sorry` and only
`[propext, Classical.choice, Quot.sound]` in every printed footprint.

## 5. Consumer/supplier obligation table

| boundary | consumer demand | supplier obligation after A-I.8 | status |
|---|---|---|---|
| E.40 item 2--4 | quotient block, peel, mass, threshold, interface | construct `MP1StepCore`; bind `quot.F=B'.F`, both thresholds to `B.T`, and `B.F=B'.Φ*B'.F` | existing C5r work; G7 still mandatory |
| E.40 `hirr` | fraction-field irreducibility of `B'.Φ` | same `A.keys` source predicate contains `B'.Φ`; the payload's universal `key_irreducible` law is filled by the direct deep key proof; apply Gauss | μ₅: D4-12--D4-15; no GN node |
| E.40 `hef` | degree read-off | `B'.hΦdeg.trans C.hef` | landed/definitional |
| recenter provenance | same socket and same realization | retain `core/A/X/eK/eG`, all three view equalities, `Λ`, and the DWR quotient bindings under one existential | A-I.8 statement enactment |
| μ₄ prerequisite | construct the carried degree-16 `keyAt4` and μ₄ calculus | L2E; D3-12; D3-14--D3-19, with D3-15's residual iff and D3-16's direct irreducibility | twin-needed, not blocked |
| μ₅ occurrence | prove `leaf` is the direct key at `(1,1,171)` | D4-09; D4-12--D4-17, especially D4-13 residual iff, D4-14 key criterion, D4-15 irreducibility | twin-needed, not blocked |
| one occurrence | one direct `RecenterStep` and one `MidPeelEmission` | C4d/C5d at the exact `X`, `Λ`, `B'` | nonvacuity only |
| universal MP1 carrier | every direct step implies an emission | generic `midPeelEmission_of_recenterStepDirect`; `mp1CarrierLiveDirect_of_steps` then inhabits the carrier for every socket | **shape-closed in the probe**; no occurrence-to-universal argument |
| full ladder supply | `package`, `lb1`, `mp1`, and universal `vartheta` | the direct compiler supplies `mp1`; independent HE7A/LB1 and the deep-level/vartheta exporter remain | open outside the MP1 leg |

## 6. Blueprint node delta

Delete the GN-only nodes/edges:

* G0 principal polygon/slope residual;
* G1 completed selected factor/descent;
* G8 input slope-residual order-one (the input residual multiplicity is irrelevant to
  direct keyhood of `B'.Φ`);
* G9 GN valuation/index alignment;
* all edges from those nodes to C4r/C5r.

Replace, without increasing the node count:

* G2 by **A8D-S0 direct recenter surface + compiler**;
* G5 by **direct μ₅ refinement admissibility** (MacLane/operator validity only; no GN
  theorem applicability);
* C4r by **C4d direct key binding**;
* C5r by **C5d direct recenter/MP1 occurrence tooth**.

Strengthen existing rows rather than clone them:

* D3-15 must include the μ₄ forward/backward normalized-residual divisibility theorem and
  the below-key nondivisibility/unit lemma; D3-16 must fill keyhood and direct
  irreducibility.
* D4-13 must include the corresponding μ₅ statements; D4-14/D4-15 fill leaf keyhood and
  direct irreducibility.
* D3-18 and D4-17 independently fill `FGMNSourceLaws.key_irreducible` from those same
  direct theorems; MP1's narrower payload does not demand their other law fields.

Re-scope G10: delete its `MP1EmissionPerWitnessExporter` half, which the generic direct
compiler supersedes; retain its deep-level/vartheta universal-export half for the other
`LadderSupplyLive₂` field.  Keep G7, L2E, R8r, and all remaining provenance/supply
fences.  With the previous
83-node accounting convention, deleting four GN-only nodes and replacing the other rows
in place gives a **conditional 79-node campaign**.  This count does not downgrade the
deep key twins to transcription; D3-15/16 and D4-13--15 are load-bearing proof nodes.

The revised MP1 spine is

```text
L2E → D3-12 → D3-15/16 → D3-18/19
                         ↓
        D4-09 → D4-12 → D4-13/14/15 → D4-17
                                             ↓
A8D-S0 → generic MP1 compiler → MP1CarrierLive
G7 + R8r/R9 + D4-17 ─────────────────→ C4d → C5d  (nonvacuity)
deep-level/vartheta producers ───────────────→ G10      (other field)
```

There is no remaining GN stop-line.  The exit is now entirely internal: the μ₄ and μ₅
key-tail twins must elaborate, the direct key law must be filled without an axiom, the
quotient block must pass G7 for an honest occurrence, and the independent universal
vartheta/package/LB1 obligations must still be met before claiming the full ladder record.

## 7. Verification

```text
cd leanfinal
timeout 580 ~/.elan/bin/lake env lean scratch/A8D_probe.lean
```

Exit 0.  Six probe declarations print only Lean core
`[propext, Classical.choice, Quot.sound]`; there is no `sorry`.  No landed `.lean` or
leanspec file was edited, no git commit was made, and no owner's-paper citation was used.
