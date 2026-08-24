# THE TOWER-INSTANTIATION FREEZE, v2 (A-C.9 / A-I.2)

**Design document, 2026-08-24. Nothing in this document is signed.** This supersedes
`TOWER_INSTANTIATION_FREEZE_DRAFT_2026-08-20.md` §§3–4. The v1 review banner is binding:
surviving findings #19–#32 are incorporated below, and the lost part of the review has been
re-derived from the landed sources. No binder of I.10a, I.10b, or `CapstoneHypotheses` is changed.

## 0. Verdict

The freeze can define an honest **arising-configuration guard** and an L-valued canonical
node-point read without swallowing `(H-VARTHETA-RES)`. It cannot, however, make the frozen
chapter-I consumer literally faithful to the source's per-level statement.

There are two signed-shape defects which this document does not conceal:

1. **SINGLE-Kt defect.** D.62 says that its `K` is the current `K_i`; OM-8 proves membership in
   `K_i`; but E.24, E.63, and the frozen I.10 fields use one `Kt` for the entire `∀ i` family.
   The only coherent single receiving field for a finite tower is the terminal residue field
   `K_r`. Thus v2 resolves the Lean binder as `Kt ≃ K_r`, but this changes each live conclusion
   from “lies in `K_i`” to the weaker “lies in `K_r`”. It is dischargeable from OM-8 by the
   tower embeddings `K_i ↪ K_r`, but it is not the literal HYP.57 statement. **OPEN (owner):**
   accept this weaker common-receiver recast, or re-sign E.61/E.24/E.63 to carry `K : ℕ → Type`
   with `[∀ i, Field (K i)]`. The latter would require changing a frozen consumer and is outside
   this unit.
2. **Unbounded-index defect (re-derived).** `DeepTower … r` has meaningful data only on
   `1 ≤ i ≤ r`; an HVR use at level `i` also needs `u_{i+1}`, hence is live only for `i < r`.
   E.63 nevertheless defines `DeepTwistConjunct` with `∀ i, 3 ≤ i → …`, without an upper bound.
   Live-range-only socket pinning therefore cannot control the consequent's off-range values.
   Total equalities would merely pin C.83's forbidden junk. **OPEN (owner):** the consumer must
   eventually be range-bounded (`3 ≤ i ∧ i < r`, or by a ladder-top index), or it must consume an
   explicitly infinite legal tower. E.63's `deepTwist_vacuous_shallow` is only an index theorem;
   it does not repair the definition.

The first defect is the required #20 finding. The second is a lost-review constraint recovered
directly from C.83's junk-total discipline and E.63's body. Neither is repaired by pretending
that `T.fld r = L`: that choice would make `Kt = L`, and then D.62 is tautological by taking
`u := ρ(…)`; it is forbidden by the non-swallowing fence.

### Review-finding disposition

| finding | v2 disposition |
|---|---|
| #19 | one existing `[Algebra Kt L]`; terminal chain maps and every transport carry explicit commutative squares (§§2, 5) |
| #20 | `Kt` resolves to terminal `K_r`; the mismatch with literal per-level `K_i` is a signed-shape finding, not hidden (§0) |
| #21/#22 | canonical letters are L-valued; `arenaRes` is separate; neither arena agreement nor τ-letter Kt descent is a socket field (§4) |
| #23–#26 | `μ`, `hμ`, both degree equations/divisibility, the sourced threshold, and exact E.11 key-freeness are bound in `ArisingInput` (§3) |
| #27 | arising means D-TIF-4's legal GENTOW5-1 class, with tower and input in one record; no algorithm claim (§2) |
| #28 | the concrete lattice is explicitly `ULift`ed to `uG` (§5) |
| #29 | the tower is explicitly `DeepTower.{0,uKt}`; cross-universe transports are obligations (§5) |
| #30 | only live projections are pinned; off-range functions, proof fields, and total `Full` are not (§6) |
| #31/#32 | the gate targets both full sockets at fixed `s2Witness`, `i=2`, `μ=1`, `F₀=Φ₂+1`, and lists every missing bridge (§9) |

## 1. Source facts which fix the design

* C.83's `DeepTower` is only `(e,f,u,ψ)` plus the range-scoped arithmetic and abstract
  residue-field iterate witnesses. Its own faithfulness note says it does **not** tie `ψ` to an
  actual polynomial factorisation or node locus. Consequently `DeepTower` is necessary but not
  sufficient for “legal DEF GENTOW5-1 instantiation”.
* D.07's `GaugeArena G K N` contains a `K`-valued homomorphism on all of `ker v`. D-H3 says this
  structure, used as a theorem hypothesis, is stronger than the sitewise source clauses.
  D.62's `hvarthetaRes_of_arena_agree` needs a separate agreement equation between that arena
  homomorphism and the given L-valued `ρ`.
* D62w's `hvarthetaRes_of_tau_letters` needs, in addition to kernel membership, a **Kt-valuedness
  witness for every τ-value**. `deep2_tau_descent`, `deep3_tau_descent`, `dvd_stage`, and
  `triangular_descent` supply the exponent factorisation, not the Kt-valuedness of the letter
  residues.
* OM-8 §3.1 and PROJECT_STATE append #73 adjudicate: YES for every legal DEF GENTOW5-1
  instantiation with the canonical node-point read, simultaneously for all live `i ≥ 3` and
  `s ≥ 0`; NO for arbitrary ambient `ρ`. Its proof has three separate legs: (L1) lattice
  factorisation, (L2) residue multiplicativity at node points, and (L3) the letters' descent to
  `K_i`.
* E.61 deliberately chooses one ambient field `L` for the whole ladder. This is compatible with
  the source after embedding all node-point residue fields into one ambient field. It does not
  license identifying `L` with the common receiving field `Kt`.

## 2. Decisions

### D-TIF-1 — height normalization (retained)

The E-side carrier remains `WithTop ℤ`. A C-side finite height is embedded in `WithTop ℤ`; no
re-gauging or subtraction is built into the socket. Negative recentered heights belong to the
E-side ladder. The general-depth ultrametric and digit-addition laws remain proof obligations of
the stage carrier; they are not consequences of an `ℕ∞` coercion.

### D-TIF-2 — a synchronized abstract lattice (revised)

A single `G` and a single `N : NormSection G` must serve a family of genuinely different
level normalizers. Therefore the v1 group `Multiplicative (Fin (r+2) →₀ ℤ)` is insufficient.
The canonical group is a synchronized finite product

```text
GaugeLattice X := ∏ j : LiveLevel X, LevelExponentLattice X j,
N.n(k)          := (n̂_j(k))_j,
v j             := height_j ∘ projection_j.
```

For a live `j`, `v j (N.n k) = k`. The `j`th ambient read ignores the other factors and applies
the level-`j` node-point read to the `j`th factor. This packages, rather than identifies, the
level normalizers. The level lattice is the Laurent exponent lattice on
`(π,x,Φ₁,…,Φ_{j-1})`; its value-zero distinguished generators are exactly
`W₀ = x^e₁/π^h` and `Λ_a = Φ_a^e(a+1)/n̂_a(u(a+1))`. Sources: EFF.T1.01–.03,
EFF.T1.09, EFF.GENTOW2.42, and EFF.GENTOW5 S2.1/S2.3 step (3), as recorded in OM-8
§§1.2 and 3.1. No residue table for the raw letters is invented.

The off-by-one is fixed, not inferred: for `j ≥ 2`, the nonnegative part of `n̂_j(k)` is
`T.towerNorm (j-1) k`, because C.83 explicitly says `towerNorm 1 = n̂₂`; `n̂₁` is the frame
normalizer. Extend to negative `k` by the inverse Laurent word and set `n̂_j(0)=1`. C.130f must
prove the exact-height equation after this extension; `NormSection` itself contains only
`n_zero` and supplies no such theorem.

The product is abstract on purpose. It contains no ambient-unit relations, so the socket cannot
obtain a Kt-valuedness theorem from a quotient relation hidden in `G`.

### D-TIF-3 — one terminal receiver and one genuinely ambient field (revised)

For a legal depth-`r` instance, the frozen single binder is interpreted as

```text
Kt ≃+* X.T.fld r,
[Algebra Kt L] = the one ambient embedding used everywhere in the socket.
```

For each live `j ≤ r`, define `levelHom j : X.T.fld j →+* Kt` by composing C.83's step
equivalences with the canonical `AdjoinRoot.of` maps and the terminal equivalence. The required
square at a step is

```text
levelHom j
  = levelHom (j+1) ∘ (step j).symm.toRingHom ∘ AdjoinRoot.of (ψ j).
```

All maps into `L` are exactly `algebraMap Kt L ∘ levelHom j`. There is no second `Algebra Kt L`
instance, no transported competing algebra map, and no equality `L ≃ T.fld r`. This resolves
#19. The step-composition and algebra square are named proof obligations, not instance-search
guesses.

As stated in §0, terminal `Kt` is the only coherent interpretation of the frozen family, but it
is a faithful **common-receiver recast**, not the literal per-level `K_i` content.

### D-TIF-4 — “arising” means the adjudicated legal class, not algorithm output (new)

`Arising` means: **a legal DEF GENTOW5-1 instantiation, with the canonical node-point residue
read, and an input block built at one of its live stages.** It does not mean “returned by the
global classification algorithm”. The classifier linkage is neither landed nor needed.

This is the review's recommended repair to #27. It also prevents an unrelated `DeepTower` from
witnessing the guard: the same legal-instantiation record owns the tower, stage key, input
polynomial, development, node locus, node-point values, lattice, and exported configuration.

Strength bookkeeping must be stated with the comparison fixed:

* relative to the pre-A-I.1 **all-configurations** reading, guarding by the legal class weakens
  the `ladder`/`deepTwist` fields and therefore strengthens the capstone theorem;
* relative to an **algorithm-produced subset** of the legal class, requiring supply at every
  legal instantiation is a stronger hypothesis and hence a weaker conditional theorem.

Thus “strengthens the theorem” is correct only for the first comparison. Claiming it relative to
the algorithm-produced alternative would reverse implication. The advantage of D-TIF-4 is that
the larger legal class is exactly what OM-8 adjudicated and needs no unlanded classifier.

### D-TIF-5 — two residue reads, with no agreement in the socket

The W-leg needs a Kt-valued arena read; the HVR leg receives the canonical L-valued node-point
read. They are distinct exported objects:

```text
arenaRes     j : ker (v j) →* Ktˣ
canonicalRes j : ker (v j) →* Lˣ.
```

The socket pins `A j |>.res` to `arenaRes j` and `ρ j` to `canonicalRes j`, on the live range,
but contains **no** equation between them. Their agreement is OM-8's L2+L3 content after the
single-Kt recast. This separation is load-bearing.

## 3. The arising carrier

The chapter-C object is conceptually the following. Names are provisional; every field marked
OPEN needs its own source transcription before landing.

```lean
structure LegalGentowInstantiation
    (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (Kt : Type uKt) [Field Kt] (L : Type uL) [Field L] [Algebra Kt L]
    (n : ℕ) where
  π       : O
  hπ      : Irreducible π
  complete : IsAdicComplete (IsLocalRing.maximalIdeal O) O
  finite   : Finite (IsLocalRing.ResidueField O)
  F       : KeyFrame O π
  H₀      : ℕ
  hpin    : F.Pin H₀
  r i     : ℕ
  hi      : 1 ≤ i ∧ i ≤ r
  T       : DeepTower.{0,uKt} F H₀ hpin r
  topEquiv : T.fld r ≃+* Kt
  levelHom : ∀ j, 1 ≤ j → j ≤ r → T.fld j →+* Kt
  levelHom_step : ...                         -- the square in D-TIF-3

  F₀      : Polynomial O
  F₀_monic : F₀.Monic
  μ       : ℕ
  hμ      : 1 ≤ μ
  degree_input : F₀.natDegree = n
  degree_block : n = μ * stageDeg T i
  keyfree : IsCoprime
      (F₀.map (algebraMap O (FractionRing O)))
      ((stageKey T i).map (algebraMap O (FractionRing O)))
  threshold : ℕ
  threshold_spec : CanonicalThresholdAt T i F₀ threshold -- OPEN transcription

  node : NodePointDatum T Kt L                    -- OPEN: legal P-locus realization
  node_legal : LegalGENTOW5NodeRead T node         -- OPEN: EFF clause-by-clause
```

`ArisingInput n` is this structure together with the derived stage carrier, input block,
synchronized lattice, and the export views below. It is not an existential `DeepTower` plus an
unrelated `F₀`: `F₀`, `μ`, `i`, `stageKey`, the development, and `n` all belong to one record.

The live predicates are explicit:

```text
StageLive X j := 1 ≤ j ∧ j ≤ X.r
GaugeLive X j := 1 ≤ j ∧ j < X.r       -- q_j reads u_(j+1)
DeepLive  X j := 3 ≤ j ∧ j < X.r.
```

No theorem may read C.83 data outside these ranges.

### Input-block binding (#23–#26)

The derived `BlockData` is not allowed to infer or choose the missing inputs:

* `B.μ = X.μ`, and `B.hμ` is transported from `X.hμ`;
* `B.F = X.F₀`, `B.Φ = stageKey X.T X.i`;
* `B.A j = dev B.Φ B.F j` for `j < X.μ`; above-range values use E.11's stated zero convention;
* `B.hdev` is B.02/B.05/B.06 development reconstruction, not a new identity;
* `B.hkeyfree` is exactly `X.keyfree` in E.11's `FractionRing` spelling;
* `B.hA0` is proved from that same key-free datum and the development, or is carried as a named
  derived obligation if the generic lemma is absent;
* `B.T = X.threshold`, and `X.threshold_spec` identifies the source threshold. No numeral or
  formula is guessed. **OPEN:** transcribe `CanonicalThresholdAt` from EFF.T2.11 and the
  applicable GENTOW5/GENHN clause before C.130e is signed.

The equality `F₀.natDegree = μ * stageDeg` is explicit even though it follows by combining two
displayed degree equations; this closes the review's divisibility gap and gives the exact input
to `BlockData`.

## 4. The canonical L-valued residue read

For each `GaugeLive X j`, the legal node datum supplies units directly in `L`:

```text
η_j : Lˣ
β_j,a : Lˣ  (a < j).
```

The notation is schematic, not a residue table. Each clause is fixed only by these sources:

| clause | source and content admitted into the definition |
|---|---|
| wrap generator `W₀` | EFF.T1.01's level-one node residue; D62w `hvarthetaRes_levelOne` is the level-one regression |
| depth-2 generators | EFF.GENTOW2.42's `⟨γ₁,γ₂⟩` calculus; D62w `deep2_tau_descent` is the exponent regression |
| generator `Λ_a` at general depth | DEF GENTOW5-1 S2.1 and S2.3 step (3): its residue is the canonical node-point class `β_a`; OM-8 §3.1 L2 |
| nonzero/unit condition in `L` | the P-locus realized-residual clause and `ψ_(a+1)(0) ≠ 0`; this admits only an `Lˣ` value |
| multiplicative extension | residue multiplicativity at node points, OM-8 §3.1 L2; D62w's τ reductions are regressions |

Nothing more specific is written until those EFF clauses are transcribed in C.130g. In
particular, v1's guesses “`π ↦ 1`”, “`x ↦ η_j`”, and a raw-`Φ` table are deleted.

OM-8 L3 is deliberately absent from this table and from `LegalGENTOW5NodeRead`: L3 is the
theorem that these ambient letter values descend to the level field. Storing L3, a Kt preimage,
or an equation obtained from L3 in the legality record would recreate findings #21/#22.

`canonicalRes j` is the unique homomorphism on the level kernel whose distinguished-generator
values are the L-units above, extended to the synchronized product by sending the other level
factors to `1`. Existence uses the legal node-point residue hom; uniqueness uses the triangular
basis theorem. D62w currently proves general existence of a factorisation but not the complete
chain-indexed uniqueness/instantiation, so both bridges are **OPEN**.

Most importantly, the carrier has no field of either form

```text
∃ u : Ktˣ, β = algebraMap Kt L u
canonicalRes j x = algebraMap Kt L (arenaRes j x)
```

for a deep letter or a general kernel element. Deep letters are genuinely constructed as
L-values. Descent to `Kt` is a theorem obligation, not constructor data.

### Why the socket cannot swallow HVR

There are only two landed short routes named by the I.10 fence.

1. To apply `hvarthetaRes_of_arena_agree (A j) (ρ j)`, Lean must synthesize
   `∀ x, ρ j x = algebraMap Kt L ((A j).res x)`. Unpacking the socket yields
   `(A j).res = arenaRes j` and `ρ j = canonicalRes j`, but D-TIF-5 deliberately supplies no
   `canonicalRes/arenaRes` agreement. The goal reduces to the omitted OM-8 L2+L3 bridge and
   cannot close by rewriting.
2. To apply `hvarthetaRes_of_tau_letters`, Lean obtains the τ kernel-membership from exact
   heights and obtains an L-valued factorisation
   `canonicalRes(τ) = η^a ∏ β_k^b_k`. The theorem still requires
   `∃ u : Ktˣ, canonicalRes(τ) = algebraMap Kt L u`. No socket field gives Kt preimages of the
   deep `β_k`, so multiplicativity cannot manufacture `u`.

This is a type-level obstruction, not merely a proof-term style rule: after all socket fields are
projected, both helper applications retain exactly the missing descent/agreement goal. OM-8 may
subsequently solve it; the socket cannot solve it **by unpacking**. The gate must check that the
socket constructor and its non-vacuity witness mention neither helper and contain no field whose
codomain is `HVarthetaRes`, `VarthetaRes`, or a Kt-preimage proposition.

## 5. Universe and transport plan (#28–#29, #19)

The frozen I binders put `O` and the E-side digit field `K` in `Type 0`, while `G`, `Kt`, and `L`
live in `Type uG`, `Type uKt`, and `Type uL`. C.83 actually elaborates as

```text
DeepTower.{uO,uFld} ... : Type (max uO (uFld+1)),
DeepTower.fld : ℕ → Type uFld.
```

Accordingly:

* instantiate the tower explicitly as `DeepTower.{0,uKt}`; its `fld j` then has exactly the
  universe of `Kt`, and no impossible down-lift is requested;
* define the concrete synchronized lattice in `Type 0` and export
  `GaugeLattice.{uG} X := ULift.{uG} (GaugeLattice0 X)`, transporting all group homomorphisms
  through `Equiv.ulift`; do not silently hope Lean raises it;
* keep the stage digit field transport universe-polymorphic: a `RingEquiv` may relate frozen
  `K : Type` to `T.fld i : Type uKt`; `SlotCarrier.transport` and `BlockData.transport` must be
  proved for cross-universe equivalences;
* the only `Kt → L` map used is the existing `algebraMap Kt L`; every ring-equivalence transport
  must carry a commutative-square lemma with that map;
* `uW` remains explicit only in `LadderSupply`, exactly as E.24 requires. The socket must not
  select `W := ℕ` or try to infer `uW` from `(C,B)`.

## 6. Live projection pinning (#30)

The socket does not equate total records or total families. It uses named views:

* `SlotViewEq`: pins `D,eC,fC,hgt,dig` and their intended stage source. It does not equate the
  proof fields. `Full` is pinned only at heights actually consulted by the exported block/rungs;
  no equality of predicates on all `ℤ` is asserted.
* `BlockViewEq`: pins `Φ,F,μ,A` on `j < μ`, key-freeness, `A₀`, and the explicitly sourced
  threshold. It does not equate the zero-padding function above `μ` as data.
* `GaugeViewEq j`: only under `GaugeLive X j`, pins `N`'s `j`th projection, `v j`, `ρ j`, and
  `q j = X.T.u (j+1)` (with the source's indexing proof).
* `ArenaViewEq j`: only under `GaugeLive X j`, pins `(A j).v`, `(A j).res` to the separate
  `arenaRes`, and pins `R j,w j`; it does not assert agreement with `ρ j`.

Off-range `v,ρ,q,A,R,w` remain unconstrained. This is mathematically honest and is exactly why
the unbounded-index defect in §0 must remain visible.

## 7. Revised C.130 node list

All IDs are provisional and all declarations are design-only.

1. **C.130a `DeepTower.levelHom`** — the live chain embeddings into the terminal field, their
   step squares, injectivity, and compatibility with `algebraMap Kt L`. Depends on C.83.
2. **C.130b `stageKey`, `stageDeg`** — a live stage-key chain and degree/monicity laws. At depth
   two it must agree with C.43's `composedKey`; at general depth it is an iterated EFF.HETOW.13 /
   EFF.GENTOW5.21 transcription. **OPEN** beyond the landed depth-two bridge.
3. **C.130c `stageHgt`, `stageDig`, `stageCarrier`** — E.10's carrier at a live stage, including
   ultrametricity, shared-height digit additivity, nonvanishing, and the live `Full`/lift law.
   Sources: EFF.T2.04/.05/.09, EFF.HE7.96(c), and the C.46/C.127 landed depth-two battery.
   **OPEN** at general depth.
4. **C.130d `CanonicalThresholdAt`** — the source threshold predicate, transcribed without a
   guessed formula. Source: EFF.T2.11 plus the applicable GENTOW5/GENHN inherited-threshold
   clause. **OPEN.**
5. **C.130e `inputBlock`** — the fully bound `μ,hμ,n=μD`, development, exact E.11 key-free
   spelling, `A₀`, and C.130d threshold. This node contains no algorithm provenance.
6. **C.130f `LevelExponentLattice`, `GaugeLattice`, `normSection`, `levelHeight`** — the
   synchronized-product construction of D-TIF-2. Its regressions are D62w's depth-two/depth-three
   sections and C.83's `towerNorm` values.
7. **C.130g `NodePointDatum`, `LegalGENTOW5NodeRead`** — the actual legal P-locus/node-point
   realization omitted by `DeepTower`. Transcribe EFF.GENTOW5 S2.1/S2.3 and the P-locus clauses
   clause by clause, but exclude OM-8 L3 (the descent theorem). **OPEN; no invented table.**
8. **C.130h `canonicalRes`** — the L-valued hom fixed on `W₀,Λ_a` by C.130g, with the
   chain-indexed triangular-basis and multiplicativity bridges. It has no Kt-descent field.
   **OPEN** for the general chain bridge; regress against D62w and OM-8.
9. **C.130i `arenaRes`, `gaugeArena`, `towerRead`, `peelUnit`** — the separate Kt-valued W-leg
   data. No theorem equates `arenaRes` and `canonicalRes`. Sources: D.07/D.08, D.44, EFF.T3.21.
   **OPEN** at deep levels.
10. **C.130j `LegalGentowInstantiation`, `ArisingInput`, and the four view equalities** — the
    D-TIF-4 carrier and live-only export layer.
11. **C.130k transport library** — cross-universe `SlotCarrier`/`BlockData`/group/arena transport,
    including algebra-map squares and preservation of all E.10/E.11 laws.
12. **C.130gate** — full socket inhabitation at §9's named witness, the non-swallowing dependency
    audit, live-range lint, and the I.10b→I.10a refinement check.

This replaces v1's seven-node list. In particular, a legal node locus, an algebra-compatible
field chain, a separate arena read, and a real gate are no longer hidden inside `canonicalRes`.

## 8. Proposed I.10 socket bodies (frozen binders unchanged)

The following is shape-accurate pseudocode; exact names await C.130. It intentionally contains
no tower algorithm predicate.

```lean
def CanonicalLadderConfig {O : Type} [CommRing O] {K : Type} [Field K]
    (C : Ladder.SlotCarrier O K) (B : Ladder.BlockData C)
    (G : Type uG) [CommGroup G] (Kt : Type uKt) [Field Kt]
    (L : Type uL) [Field L] [Algebra Kt L]
    (N : Gauge.NormSection G) (v : ℕ → (G →* Multiplicative ℤ))
    (ρ : ∀ j, MonoidHom.ker (v j) →* Lˣ) (q : ℕ → ℤ) (n : ℕ) : Prop :=
  ∃ X : Tower.ArisingInput O Kt L n,
    SlotViewEq C X ∧ BlockViewEq B X ∧
    Nonempty (G ≃* Tower.GaugeLattice.{uG} X) ∧
    GaugeFamilyViewEq N v ρ q X
```

`GaugeFamilyViewEq` is a bounded family of projection equations, not equality of total
functions. The equivalence is packaged with all transported equations in C.130k; `Nonempty` is
shown only to stress that no choice of inverse is mathematical content.

```lean
def CanonicalDeepTwistConfig ...
    (A : ℕ → Gauge.GaugeArena G Kt N)
    (R : ℕ → G → Kt) (w : ℕ → Ktˣ) (n : ℕ) : Prop :=
  CanonicalLadderConfig C B G Kt L N v ρ q n ∧
  ∃ X : Tower.ArisingInput O Kt L n,
    CanonicalExportWitness X C B G N v ρ q ∧ ArenaFamilyViewEq A R w X
```

The second conjunct contains one witness exporting **both** the ladder data and arena data; it is
not merely `∃ X, ArenaFamilyViewEq ...`. Thus it cannot use an arena from a tower unrelated to the
input. The first conjunct is retained because I.10b's refinement shape is frozen; the joint
witness in the second conjunct independently certifies the same external `(C,B,G,N,v,ρ,q)`.
An implementation should define one private `CanonicalExportWitness` and reuse it in both
public bodies. `CanonicalDeepTwistConfig → CanonicalLadderConfig` remains `And.left`.

Because of §0's unbounded-index defect, these bodies honestly guard only live projections. They
make the sockets typable, but **do not by themselves make the frozen `deepTwist` field
dischargeable**. Signing them before the range issue is adjudicated would be misleading.

## 9. Real non-vacuity witness plan (#31–#32)

The gate target is a full inhabitant of both sockets, not merely a `DeepTower` value.

Use the following fixed data:

```text
O  := ℤ_[2]                         π := 2
h2 := C35b.h2_padic                 hq := C35b.rc2
F  := s2Frame h2 hq                H₀ := 1
hpin := s2Frame_pin h2 hq
T  := s2Witness h2 hq 1 hpin       r := 3
i  := 2                            μ := 1
T₂ := C80.s2Tower h2 hq
Φ₂ := composedKey T₂
F₀ := Φ₂ + 1                       n := 4
Kt := T.fld 3
L  := FractionRing (Polynomial Kt)
```

After C.130 lands, name the one arising record and every exported socket argument rather than
leaving an existential hole:

```text
X₂   := s2ArisingInput h2 hq                    -- the record above, at (r,i,μ,n)=(3,2,1,4)
K₂   := T.fld 2
C₂   := stageCarrier X₂
B₂   := inputBlock X₂
G₂   := GaugeLattice.{uG} X₂                    -- genuinely tests the ULift export
N₂   := normSection X₂
v₂   := gaugeHeightFamily X₂
ρ₂   := canonicalResFamily X₂                   -- L-valued read
q₂   := useHeightFamily X₂
A₂   := gaugeArenaFamily X₂                     -- separate Kt-valued read
R₂   := towerReadFamily X₂
w₂   := peelUnitFamily X₂
```

The gate's two goals are the literal full applications
`CanonicalLadderConfig C₂ B₂ G₂ Kt L N₂ v₂ ρ₂ q₂ 4` and
`CanonicalDeepTwistConfig C₂ B₂ G₂ Kt L N₂ v₂ ρ₂ q₂ A₂ R₂ w₂ 4`. Thus neither a bare
`DeepTower`, nor `Nonempty` of a partial carrier, counts as G-1.

The choice `i=2` is deliberate: C.80 lands the matching `TowerDatum`, and C.43 proves
`Φ₂.Monic` and `natDegree Φ₂ = 4`. The former v1 phrase “a concrete quartic from §13” named no
term and was not a witness. `F₀ = Φ₂+1` is now fixed. It is monic of degree four, has
`Φ₂`-development `1 + Φ₂`, and is coprime to `Φ₂` because its remainder is `1`.

The gate must discharge every item below; until then G-1 is **OPEN**:

1. the standard DVR, completeness, finiteness, irreducibility, and `residueCard=2` instances for
   `ℤ_[2]`;
2. `s2Frame_pin`, `s2Witness`, and all needed field instances without using an axiom;
3. a proved bridge that C.80's `s2Tower` is the depth-two datum exported by `s2Witness` (all
   `(e₂,f₂,u₂,ψ₂)`, field, step, and composed-key transports); this bridge is not landed;
4. construction of C.130b's `stageKey T 2` and the equation to `composedKey T₂`;
5. `Φ₂.Monic`, `Φ₂.natDegree=4`, `F₀.Monic`, `F₀.natDegree=4`, `μ=1`, `hμ`, and
   `n=μ·stageDeg`;
6. the exact E.11 development equations: `A 0=1`, no lower coefficient beyond it, reconstruction,
   and all degree bounds;
7. `IsCoprime (F₀.map ...) (Φ₂.map ...)` over `FractionRing ℤ_[2]`, plus the derived `A₀≠0`;
8. a named threshold `T₀ := canonicalThreshold T 2 F₀`, its source specification, and
   `B.T=T₀`—no guessed numeral;
9. every field of `stageCarrier T 2`: `D,hD,eC,fC,hef,heC,hfC,hgt,dig`, both zero laws,
   `hgt_ne_top`, `dig_ne_zero`, both ultrametric laws, shared-height digit additivity, the
   live `Full` predicate, and `hlift` at precisely those full heights;
10. the field-chain maps, their step squares, the terminal equivalence, and the unique
    `[Algebra Kt L]` compatibility square;
11. the synchronized lattice, its `CommGroup`, the normalizer, every live exact-height equation,
    and the `ULift` transports for the selected `uG`;
12. the legal node datum at the witness, each source legality clause, and the L-valued
    `canonicalRes`; no Kt-preimage proof is permitted in the socket constructor;
13. the separate `arenaRes`, every live `GaugeArena`, `R`, and `w`, including all required
    transports; no `canonicalRes=algebraMap∘arenaRes` field;
14. `SlotViewEq`, `BlockViewEq`, `GaugeFamilyViewEq`, and `ArenaFamilyViewEq` at exactly their
    live ranges, with no equality of off-range functions, `Full` predicates, or proof fields;
15. the actual terms
    `CanonicalLadderConfig ... 4` and `CanonicalDeepTwistConfig ... 4`, followed by
    `#print axioms` and a dependency audit excluding `hvarthetaRes_of_arena_agree`,
    `hvarthetaRes_of_tau_letters`, `HVarthetaRes`, and any owner hypothesis.

C.53c's `linTower` and C.80's `s2Tower` alone cannot serve this gate: both are `TowerDatum`, not
`DeepTower`. C.97's `s2Witness` supplies the required deep object; C.80 supplies its named
depth-two composed-key companion. This closes findings #31/#32 honestly.

The witness has no live deep index (`DeepLive j` means `3 ≤ j < 3`), so it proves socket
inhabitation but does not test OM-8's deep descent. A later depth-four landed witness must be added
as a positive deep regression. No such `DeepTower` witness is currently in the cited inventory.

## 10. I.05/I.06/I.07 quantification bodies

These nodes quantify over the same `ArisingInput n`, but they must not quantify over structures
which already contain the conclusion as a field.

### I.05 `WindowPinningAt`

Quantifying over `I : StageInterface ...` and returning `I.hwin` would be tautological. Introduce
a raw, conclusion-free `StageOccurrence X` whose fields include the linked genre, `N,H,S`,
`stageWindow`, and `stageLoss`, but not `hwin`. Then:

```lean
def WindowPinningAt (n : ℕ) : Prop :=
  ∀ (X : ArisingInput n) (s : StageOccurrence X),
    s.Live →
    s.genre.e₁ * (s.N - 1 - s.H) ≤ s.stageWindow + s.stageLoss
```

This is exactly H.09's `StageInterface.hwin` formula, asserted rather than unpacked. H.89w
supplies the general-`e₁` arithmetic/census components but explicitly says `hwin` remains HYP.36
CARRY, so the body remains an open hypothesis as intended.

### I.06 `GenhnHEAt`

Define `StageDecision s` on the raw occurrence, not on a “decided leaf” carrier:

```lean
def StageDecision (s : StageOccurrence X) : Prop :=
  (s.genre.μ = 3 ∧ ∃ l : StageLeaf3,
      s.stageType = stageType3 l ∧ s.σ = stageSigma3 s.genre l) ∨
  (4 ≤ s.genre.μ ∧ HE3Box6Decision s)

def GenhnHEAt (n : ℕ) : Prop :=
  ∀ (X : ArisingInput n) (s : StageOccurrence X),
    s.Live → 3 ≤ s.genre.μ → StageDecision s
```

The `μ=3` arm binds H73w's landed five-type dictionary and transport. The `μ≥4` arm is
**OPEN** and `HE3Box6Decision` must be transcribed from EFF.HE3.16/.17 and HYP.143; no formula is
invented here. The disjunction is exhaustive under `3≤μ`.

### I.07 `GenhnTow1At`

Define a conjunction at one legal tower occurrence, then quantify it:

```lean
def Tow1CensusAt (X : ArisingInput n) : Prop :=
  GENTOW1At X ∧ GENTOW2At X ∧ GENTOW3At X ∧ GENTOW4At X ∧
  GENTOW5CoreAt X ∧ Depth3FloorAt X ∧ KeyCertificateAt X

def GenhnTow1At (n : ℕ) : Prop :=
  ∀ X : ArisingInput n, 2 ≤ X.r → Tow1CensusAt X
```

The seven conjuncts must instantiate, in order, C.93's census names
`towerLocus_iff_budget`, `refine_invariants`, `shadow_floor`, `partial_floor_and_datum`,
`window_band1`, `towerLocus_depth3_floor`, and `gentow5_key_certificate`. At HEAD these names
exist only in the leanspec census (and one open text artifact); they are not declarations in
`leanfinal`. Therefore `Tow1CensusAt` is **OPEN and presently untypeable**. C.93's landed
`tower_first_live` supplies only the threshold implication and must not be substituted for the
seven-item census.

## 11. Acceptance gate and owner items

Before any signature is adopted:

* all C.130 OPEN transcriptions must cite the effective EFF clause next to each field;
* the full §9 witness must elaborate, not merely the underlying `DeepTower`;
* helper-argument reduction must demonstrate the two missing descent/agreement goals in §4;
* a lint must reject reads of `T.e/f/u/ψ/fld` outside their live ranges;
* transport must use the one `[Algebra Kt L]` and prove every commutative square;
* I.10b refinement must be `And.left`, with a shared export witness;
* the unbounded-index defect and single-Kt faithfulness delta require explicit owner rulings;
* I.05 must not be defined by projecting `StageInterface.hwin`;
* I.07 may not land until all seven C.93 census declarations exist in `leanfinal`.

Owner decisions: D-TIF-1 through D-TIF-5; adoption of the I.10 socket bodies; acceptance or
re-signing of the single-Kt recast; repair of the unbounded `DeepTwistConjunct`; the precise
`CanonicalThresholdAt` source clause; and whether a first non-vacuity gate with no live deep
index is sufficient pending a landed depth-four witness.

## 12. What this document does not claim

It does not sign any declaration; does not discharge `LadderSupply`, `DeepTwistConjunct`,
`HVarthetaRes`, `[GENTOW5-W(i)]`, HYP.36, HYP.81, or HYP.82; does not assert an algorithm-to-tower
classifier; does not invent a residue table or threshold formula; does not identify `L` with
`Kt`; and does not turn a landed `DeepTower` value into a full socket witness by assertion.
