## Audit result

STOP THE LINE.

The manifest does not faithfully formalize accepted §C. The principal failures are structural, not proof gaps:

- `History` does not encode coherent realizable lift-carrying histories.
- `FreshData` reintroduces pin addresses and models value clauses as coordinate assignments, contradicting rev-9 Route B.
- `JetSetup` has a root/off-by-one mismatch and is unrelated to the nodes of `H`.
- `C5.massRec`, `C5.numPinnedCodim`, and `C6.thmC_b` admit concrete countermodels.
- The two final theorem statements do not state Theorem C(a) or (b).

### (a) Definitions audit

#### Node, History, coherence, and realizability: FAITHLESS

`Node` stores many appropriately named fields, but does not enforce their §C meanings:

- `Ranch` is not required to equal the anchored residual constructed from `pat`, stride positions, and `a`.
- `ψ` need not be monic, divide `Ranch`, or have degree `g`.
- `e`, `h`, `g`, `μ`, `Dwidth`, `line`, and the stage data are mutually unrelated.
- Increment nodes need not satisfy `e*g > 1`; recenterings need not satisfy `e=g=1`.
- Every node carries a `lift`, but `HistoryCoherent`’s recentering witness `tt` is existential and is not required to equal the child node’s recorded `lift`.
- The increment transition uses fields from the child `Stage`, not the node’s recorded `e`, `h`, `g`, or read data.
- A later node may have species `root`; the coherence predicate then imposes no transition condition.
- Neither `HistoryCoherent` nor `Realizable` is required by `JetSetup` or any C5/C6 theorem.

The formal `(HV)` clause is vacuous:

```lean
∃ lead, previous.vtxPoly = lead
```

It is always witnessed by `lead := previous.vtxPoly`. It never mentions the next node’s pattern lead. Moreover, `vtxPoly` omits the scalar factors in the accepted transported vertex value and is valued in the parent field.

The formal `(NA)` also has a typing problem: `Line.at` is documented as evaluation at a base index, but it is evaluated at `μ`, a slot index, without the `Dwidth` conversion.

Thus `Realizable` accepts histories that violate both the classifier geometry and the accepted `(HV)` condition.

#### Locus and mass: locally faithful, globally incomplete

```lean
Locus p m := DigitSystem m (ZMod p)
Locus.mass := Nat.card solution subtype
```

is a reasonable rendering of the BLOCK CONVENTION after expansion to base digits. `Nat.card` is also the correct finite-box measure.

However:

- `m` is never tied to `n*N`.
- There is no `N(H,Z)` or hypothesis `N ≥ N(H,Z)`.
- `C0.coordSort` proves only the existence of an arbitrary cardinal equivalence; it does not say that it implements `CoordPrec`.
- The flattening therefore lacks a formal link between `Fin m`, base levels, coefficient indices, and the global order.

#### `ZCData`: materially weaker than `(ZC)`

`ZCData.pin_dichotomy` says only that a pinned coordinate is either in one `Fin` suffix or has constant-zero solve function. It does not encode:

- that every coordinate in the literal floor downset is pinned;
- the floor `F_i` or height map at all;
- exactness of the downset;
- DIG equations solving for whole rim level sets;
- the node-dependent rim base-index region.

More seriously, a base-index rim condition is not a suffix of the global `CoordPrec` order: levels are ordered before coefficient indices. One `rimStart : Fin m` cannot generally represent “base index at least `μ_i D_{i+1}` at every level.”

`rimStart := 0` labels every coordinate as rim, making `pin_dichotomy` vacuous. This is exactly how statements such as `C1.rimLeads` can satisfy the weakened interface without proving rim persistence.

Also, `rimStart : Fin m` makes `ZCData` and `JetSetup` uninhabited when `m = 0`.

#### `FreshData`: contradicts accepted Route B

This is the largest definition-level mismatch:

```lean
coords : Finset (Fin m)
sat x := ∀ c ∈ coords, x c = pinTo c
```

The accepted rev-9 formulation explicitly avoids assigning addresses to fresh value digits. A fresh value clause is an additive function of an entire weight level set, counted through `TYP`; it is not generally an equation `x_c = v` at one base coordinate.

`FreshData` therefore formalizes the discarded address-based model. Its `Finset` only proves that its chosen addresses are distinct; it does not prove that the geometric clause inventory produces independent level-set constraints.

#### Pin arithmetic for C(b)

Algebraically, if

- `m = nN`,
- `K = Σ m*(ν_i) + |pins Z|`,
- `Dfin` is the actual final joint-history locus, and
- `K ≤ m`,

then

```text
mass(Dfin) · p^K = p^m
```

is the division-free equivalent of

```text
mass(Dfin) = p^{nN} · ∏ p^{-m*(ν_i)} · p^{-|pins Z|}.
```

So the arithmetic form itself is sound.

`C6_thmC_b` is not equivalent to the note, however, because `Dfin` is an unconstrained existential. It is not required to present `S(H,Z)`, `T(H,Z)`, or even `Σ_k ∩ locus(Z)`. The statement also lacks the `m=nN`, realizability, coherence, and sufficiently-large-`N` conditions.

### (b) Classification of all 31 statements

“FLAGGED-OK” means the local statement is a legitimate combinatorial/interface lemma; it does not repair the defective global definitions.

| Unit | Classification | Main reason |
|---|---|---|
| C0.coordPrec_trichotomy | FLAGGED-OK | Correct strict-order comparison |
| C0.coordPrec_trans | FLAGGED-OK | Correct transitivity |
| C0.coordSort | IMPRECISE | Cardinal equivalence only; no sorting/order property |
| C0.digitSystemMass | FLAGGED-OK | Correct digit-system count law |
| C0.pinWelldef | IMPRECISE | Gives pin count only, not per-coordinate free/determined status |
| C0.unitriBij | FLAGGED-OK | Correct over `ZMod p` |
| C0.moveMass | FLAGGED-OK | Correct bijective pullback count |
| C0.pinTransport | IMPRECISE | Same count, not the same pin coordinates/status |
| C1.zcMass | FLAGGED-OK | Correct consequence of `zc_c` |
| C1.zcInit | FAITHLESS | Assumes the root count it purports to establish |
| C1.valClauseDownset | FAITHLESS | Builds a synthetic downset for arbitrary `htc`; no K1 valuation bridge |
| C1.rimLeads | FAITHLESS | Can make every coordinate “rim”; does not preserve accepted `(ZC-b)` |
| C2.DOM | FLAGGED-OK | Valid affine consequence of its hypotheses |
| C2.DOM_floorForm | FLAGGED-OK | Valid affine supremum consequence |
| C2.LST_selection | FAITHLESS | `selection` is merely a stored conclusion and does not mention `Σ_i` or freeness |
| C2.LST_typing | FAITHLESS | Returns only `ht=ℓ+off`; no K1-chain-weight identification |
| C2.TYP_fiberCount | FLAGGED-OK | Correct generic equal-fiber theorem |
| C3.crossing | FLAGGED-OK | Correct endpoint/affine interpolation |
| C3.crossing_reverse | FLAGGED-OK | Correct right-side affine comparison |
| C3.EInh_implied | FAITHLESS | Restates `hdownset`; proves pinned booleans, not clause implication on a locus |
| C3.freshFree | FAITHLESS | Allows the rim alternative and assumes the decisive implication |
| C4.stripCount | FLAGGED-OK | Correct for literal free-coordinate zero pins |
| C4.valueCount | FLAGGED-OK | Correct generic quotient count |
| C4.conditionalMass | FAITHLESS | Counts direct coordinate pins, not Route-B level-set value clauses |
| C4.zcPersist | FAITHLESS | Only proves a numeric field equality, not persistence of `(ZC-a/b)` |
| C5.massRec | FAITHLESS | False: missing root initialization and off by one |
| C5.numPinnedCodim | FAITHLESS | False through the same root/index defect |
| C6.transportedAdmissible | FLAGGED-OK | Correct digit-system intersection principle |
| C6.psiBij | IMPRECISE | Only a two-map composition lemma; no history composition/root indexing |
| C6.thmC_b | FAITHLESS | False in general and disconnected from the target locus |
| C6.thmC_a | FAITHLESS | Generic bijection cardinality tautology; no `S`, `T`, or history move composition |

Counts:

- FLAGGED-OK: 14
- IMPRECISE: 4
- FAITHLESS: 13

### (c) Interface-deferral audit

#### `LstData`

Non-vacuous, but not honestly sufficient for LST.

- `ht_scale` does not assert that `off` is the κ-weight combination.
- `floor_const` is asserted for every base index, stronger than the accepted interior-only result.
- `selection` follows trivially from `floor_const` and `old < γ'`; the hypotheses involving `ht` do no work.
- There is no `Sigma`, so it cannot state that a level set is free on the current cylinder.

The consuming LST units do not consume more formally than supplied—they simply project fields—but the interface fails to defer the actual semantic bridge.

#### `htc`

This is not a genuine interface predicate at all: it is an arbitrary function `Fin m → ℚ`.

`C1.valClauseDownset` proves that any chosen set `{c | htc c < β}` can be encoded as zero pins. It does not assert that `htc` is realized by K1 weights or that a real valuation clause has this solution set. The claimed graded-ring deferral is therefore absent from the statement.

#### `TypObject`

Non-vacuous when the alphabet is an additive quotient/image of the source. The equal-fiber consumers use exactly what it provides.

Its scope is nevertheless incomplete: nothing ties a `TypObject` to

- a particular node;
- a particular slot and height;
- the entire corresponding level set;
- the real piece map `R_δ`;
- the emitted pattern value.

Most importantly, `C4.conditionalMass` does not consume `TypObject` at all; it bypasses TYP by replacing value clauses with coordinate pins.

#### `JetSetup`

Non-vacuous for `m>0` through artificial histories—for example, constant/full loci, identity moves, and empty fresh sets. That is itself evidence that it is not tied to the classifier history.

It omits:

- `HistoryCoherent H`;
- `Realizable H`;
- any dependence of `Sigma`, `fresh`, or `Theta` on `H.nodes`;
- bounds by `H.nodes.length`;
- the root construction;
- identification of `Theta` with the recorded transitions/lifts;
- LST/TYP evidence for fresh value clauses.

There is also an indexing contradiction:

- prose says `Sigma 0` is the state after the root;
- `fresh 0` is the root fresh data;
- `recursion 0` applies `fresh 0` again to obtain `Sigma 1`.

One unit consumes more than the interface supplies: `C5.massRec` assumes the missing root equality. Consequently `C5.numPinnedCodim` and `C6.thmC_b` also overconsume it transitively.

### (d) Vacuity probes

#### Degenerate histories

Accepted by the formal definitions:

- later `root` nodes;
- zero `e`, `g`, `μ`, or widths;
- side endpoint `s0+wSide > parent.μ`;
- unrelated node and stage transition data;
- unrelated recorded recentering lift;
- incoherent histories, since coherence is never a theorem hypothesis;
- non-realizable histories, since realizability is never a theorem hypothesis.

Formal `(HV)` is always true when its adjacency premise holds.

#### Empty loci

A standalone unitriangular `DigitSystem` is a graph over its free coordinates and is therefore nonempty. Thus `Locus` cannot directly represent an empty joint stratum. Intersections can be empty, but `FreshData` and `AdmissibleZ` are designed to avoid conflicts.

The accepted exclusion of unrealizable empty strata is therefore not being tested; invalid histories instead pass through the vacuous formal `Realizable`.

#### `k = 0`

This gives an explicit failure of the mass recursion.

Take `m=1`, let `Sigma 0` be the full locus, and let `fresh 0` pin its single free coordinate. A `JetSetup` can continue with `Sigma 1` equal to that pinned locus. Then:

```text
(Sigma 0).numPinned = 0
Σ_{i∈range(1)} mstar(fresh i) = 1
```

so `C5.massRec` at `k=0` is false.

For `C6.thmC_b`, additionally choose `Z` to pin that same coordinate. It is admissible relative to the full `Sigma 0`, but `totalPins = 2 > m = 1`. For prime `p`, no one-coordinate digit-system mass can satisfy

```text
Dfin.mass · p² = p.
```

Thus `C6.thmC_b` is formally false, not merely semantically weak.

## Units unsafe to prove

Do not fan out proofs for these statement fences:

- `C1.zcInit`
- `C1.valClauseDownset`
- `C1.rimLeads`
- `C2.LST_selection`
- `C2.LST_typing`
- `C3.EInh_implied`
- `C3.freshFree`
- `C4.conditionalMass`
- `C4.zcPersist`
- `C5.massRec`
- `C5.numPinnedCodim`
- `C6.thmC_b`
- `C6.thmC_a`

Of these, at least `C5.massRec`, `C5.numPinnedCodim`, and `C6.thmC_b` are outright false under the current definitions.

Final verdict: **STOP THE LINE.**
