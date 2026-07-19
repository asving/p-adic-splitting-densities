# VACUITY_SIGMA_BLUEPRINT — de-vacuifying the Montes capstone (V1 + O1 + the classifier-degeneracy chain)

**DESIGN DECISIONS SIGNED OFF (Asvin, 2026-07-02):**
* **A2 childSize units:** `childSize := μ·deg ψ` (degree units; GLUE-2 tiling closes; re-check
  `hcs`/`hNodeSize` consumers; self-loop cutoff = `childSize = cs` absorbed into `countPivot`).
* **A6 multiplicities:** EXPLICIT `realF.multiplicity := m_T(q)` (L3Gauss necklace counts +
  multinomial corrections; matches the paper's `ρ = Σ m_T·C_T`).
* **A7 Phase-A capstone:** NEW `montes_order0` restricted to the separable-stratum densities
  (h_node / h_decided_mono discharged as THEOREMS via `cylinder_count_stable`);
  `montes_unconditional` stays as the Phase-B target.
* **Priority:** Phase A next (before the HNODE chain, which partially depends on A3/A4 anyway).

**Status: 2026-07-02.** Written after the soundness-repair round that (i) deleted the false global
`tame_functionalEquation` axiom (U1) and replaced it with the `TameFunctionalEquation` hypothesis +
the concrete named cite `realDensity_tame_functionalEquation`; (ii) deleted the dead false axioms
`AX_columnMeasure`/`cellVolume_eq_bb1Value` (U3); (iii) converted `gmn_node_ef_law` to the
hypothesis-predicate `GMNNodeEfLaw` (U4); (iv) flagged `L2_reconstruct` (U5) and deleted the
sorry-over-false `M8.nodeMeasure_boxSum` skeleton (U2); (v) **deleted `discZeroValTail_density`
(A11) — REFUTED, see §1.4 — and `decidedDensity_mono_realP` (A12, unauditable), restoring `h_env`
and `h_decided_mono` as capstone hypotheses.**

After that round the trusted base is believed sound (no false axiom), and the capstone
`montes_unconditional` is honestly conditional on THREE hypotheses (`h_node`, `h_decided_mono`,
`h_env`) **all of which are currently FALSE (or unaudited) for the real instance**, because the
order-0 instance is degenerate. This blueprint is the repair design.

---

## 1. The defect chain, precisely (four interlocking bugs)

The audit's V1 ("density ≡ 0") and O1 ("σ-independent") are symptoms of a single interlocking chain
in `Classifier.lean` / `OMType.lean` / `RealInstance.lean`. Each link verified by direct read
2026-07-02.

### 1.1 `hDrLtCs` is semantically wrong at the ROOT node ⟹ the degree guard

`M5.OMType.hDrLtCs : 0 < dr → dr < cs` is carried as a structure INVARIANT. It is the GMN
cluster-size law for **descent children** (Lemma 3.11(3)) — but the ROOT of a genuine order-0 tree
violates it: for `f` with unit constant coefficient (the generic case), the Newton polygon is the
single flat side and the residual is `f̄` itself, so `dr = n = cs`.

To satisfy the invariant, `Classifier.rootResidual` (Classifier.lean:155-161) GUARDS the residual:
`if R.natDegree < n then R else 0`. Consequence: **the generic polynomial's root residual is zeroed.**

### 1.2 The guard ⟹ empty cells ⟹ one lump shape

With `Rr = 0`, `M4.factorize_any 0` is forced to the empty factorization (`degree_budget` +
irreducibility force `factors = ∅`), so `M5.cells (fRootCtx …) = []`, so `classifyAux` emits the
shape `⟨[(0, n, 0)], []⟩` for EVERY `f` whose first side has residual degree `0` or `≥ n`. In
particular the classifier does NOT distinguish separable from non-separable reductions: the strata
are NOT the OM strata. (The count side is nonzero — the lump shape's fiber is most of the box — but
semantically wrong.)

### 1.3 `decode` ⟹ coefficient ≡ 0 (V1) and `h_node` false-for-instance

`M9.decode T := leafOMTypeOfSize (M6.treeSize T)` with `Rr := 0` ⟹ `M5.cells (decode T) = []` ⟹
`clusterCount … T q = (empty sum)/pivot = 0` ⟹ `coeff ≡ 0` on the whole menu ⟹ the certified
density is the constant 0. Meanwhile the genuine normalized fiber counts converge to something
positive, so the capstone hypothesis `h_node` (LHS → RHS with RHS = 0) is **FALSE for the real
instance**: `montes_unconditional` is vacuously true.

### 1.4 The classifier does not DRAIN ⟹ `h_env` (old A11) is FALSE — the refutation

Menu shapes are `[(0, s, 0)]`; the classifier's root always has `cs := n`, so only `[(0, n, 0)]` is
reachable. Any `f` whose first side has residual degree strictly between `0` and `n` classifies
OFF-menu at every level `N` — e.g. at `n = 2`, `p = 2`: `f = x² + a₁x + a₀` with `v(a₀) = 1`,
`v(a₁) = 0` (measure `≥ 1/8`, independent of `N`). So the undecided density does NOT decay like
`2^{-N}`; at `N = 4`, `1/8 > 2^{-4}` refutes the old axiom `discZeroValTail_density`. (This
resolves MONTES_AUDIT open item 7 NEGATIVELY; the axiom is deleted, the obligation restored as the
hypothesis `h_env`.) The same degeneracy makes `h_decided_mono`'s truth unauditable (read-boundary
flips are not controlled), hence its restoration as a hypothesis too.

### 1.5 σ-independence (O1) and the missing multiplicities

`shapesOf σ₀ σ = if σ = σ₀ then shapeMenu n else ∅` with `σ₀ := σ` re-pinned per query: every
degree-`n` type gets the SAME menu, so the certified function is σ-independent. Moreover
`realF.multiplicity := 1` — the genuine decomposition `ρ(n,σ;q) = Σ_T m_T(q)·C_T(q)` has
**necklace-count polynomial multiplicities** `m_T` (the L3 content; `L3Gauss.gauss_necklace_count`
is PROVED and currently unused on this path). Both must enter for the density to be the genuine
per-type `ρ`.

### 1.6 Latent payload mismatch (will bite in Phase A)

`M5.shapeOf` writes the faithful cell payload (`encodeCells`) into `ClusterShape.cells`, but
`classifyAux` constructs shapes MANUALLY with `cells := []` (Classifier.lean:263-268). Today they
agree (everything is `[]`); the moment cells become genuine, classifier-shapes ≠ shapeOf-shapes and
the menu/fiber bookkeeping silently breaks. Phase A must unify them.

Also: `classifyAux` recurses into children with the f-FREE `childCtxOfSize` (`Rr := 0`), so the
classification below the root never looks at `f` — depth-≥1 classification is f-blind. That is the
genuine GMN order-≥1 machinery (key polynomials, lifted coefficient reads) — Phase B.

---

## 2. Phase A — the genuine ORDER-0 prototype (bounded; the next work package)

**Goal.** Make the capstone certify a TRUE, non-vacuous statement: *the density of each
separable-reduction factorization stratum (the order-0-decided locus), per type σ, is the genuine
count-native tree-sum — a uniform rational function of q, palindromic* — with `h_node`,
`h_decided_mono`, `h_env` TRUE-for-the-instance statements (dischargeable or honestly citable), and
the σ-content genuine. Everything below is order-0 only: no key polynomials, no higher-order OM.

### A1. Fix the `OMType` size law (root-compatible)

Replace the field `hDrLtCs : 0 < dr → dr < cs` by `hDrLeCs : dr ≤ cs`.
Strict descent is NOT lost: it is re-derived per-child in `M5.cells` from the budget arithmetic
(see A2). Ripple sites (grep `hDrLtCs`): `OMType.lean` (`cells`' `hChildSizeLt` chain),
`Classifier.lean` (`fRootCtx`, `M9rootCtx`, `childCtxOfSize`, `rootResidual_natDegree_lt` — the
GUARD and its lemma become deletable), `RealInstance.leafOMTypeOfSize`. Audit: `hDrLeCs` holds at
the genuine root (`dr = cs`), at leaves (`0 ≤ cs`), and at GMN descent nodes (`dr < cs` a fortiori).

### A2. Un-guard the root residual + self-loop-aware cells

* `rootResidual := residualPoly (boxCoeffData p N S f) S` UNGUARDED (need the elementary lemma
  `natDegree (residualPoly …) ≤ side length ≤ n` to discharge `hDrLeCs` — provable from the
  `residualPoly` definition + M3 side bounds; NOT the old guard).
* `M5.cells` child emission: for a factor `ψ^μ` with `μ ≥ 2`, emit a descent child **only when
  `childSize < cs`**; when the repeated factor consumes the whole cluster (`childSize = cs`, the
  totally-clustered case, e.g. `f̄ = ψ^μ` with `μ·deg ψ = dr = cs`), the refinement is the
  **self-loop** — do NOT emit a child; it is resummed by `countPivot (treeSize T)`. This matches
  the already-designed self-loop split (GLUE-1 filters cells by
  `∀ ch ∈ children, treeSize ch ≠ treeSize S`) and keeps `cells_descend` (strict `<`) intact for
  the WF recursion.
* DESIGN DECISION for Asvin (the childSize units, §5.4(1) of OMSTEP_BLUEPRINT): `childSize := μ`
  (current) vs `childSize := μ·deg ψ` vs `(μ−1)·δ·deg ψ`. The count recursion's budget accounting
  (GLUE-2 tiling `∑_c (δ·dS + ∑_ch childSize) = cs`) only closes with childSize in DEGREE units:
  recommend `childSize := μ·deg ψ` — re-check `hcs`/`hNodeSize` consumers.

### A3. Payload-carrying classifier

`classifyAux` must emit the faithful per-node cell payload, exactly as `M5.shapeOf` does:
`⟨(order, cs, dr) :: …, encodeCells-of-the-node⟩` (or better: refactor so `classifyAux` BUILDS an
`OMType` tree and the shape is literally `M5.shapeOf` of it — then classifier-shapes and
encoder-shapes coincide by construction and §1.6 dissolves). Audit: `cellsOfShape_shapeOf` (the
2b faithfulness rfl) must remain `rfl`.

### A4. Coefficient side reads the payload, not `decode`

`realD.cells := M7.cellsOfShape` (the faithful lossless reader) instead of
`M7.cells decode = cellsOfType ∘ decode`. Then `coeff T` is computed from T's OWN recorded cells:
non-empty for genuine shapes, and the V1 zero disappears. `cells_descend` for `cellsOfShape`:
children recorded in the payload are serialized with their sizes in the root slot and carry
strictly-smaller sizes by construction (A2) — a small structural lemma
(`cellsOfShape_descend : ∀ T c ch, … treeSize ch < treeSize T` for classifier-produced `T`;
NOTE it is FALSE for arbitrary enriched `ClusterShape` — the payload is free data — so either
(i) restrict the MontesData instance to the reachable menu, or (ii) add the descent bound as a
`ShapeCell` proof field. (ii) is cleaner; it mirrors `OMCell.Child.hChildSizeLt`.)
`decode` survives only where an `OMType` is genuinely needed (`shapeMenu` realness); its
`leafOMTypeOfSize` can then also carry the genuine separable residual data.

### A5. The genuine order-0 menu, σ-keyed (kills O1)

The order-0 decided shapes are indexed by the residual factor-degree data: for each factor-degree
multiset `λ = (d₁ ≤ … ≤ d_k)` with `Σ dᵢ = n` (a partition of `n`), the leaf shape `T_λ` with one
`ShapeCell` per distinct degree (dS := dᵢ, δ := 1, polygon := the flat order-0 face, children []).
Define `shapeMenu n := image over partitions λ ⊢ n`; `shapesOf σ := {T_λ : λ matches σ's
unramified residue-degree pattern}` — genuinely σ-DEPENDENT. (Order-0 σ's are the unramified types
`(eᵢ=1, fᵢ=dᵢ)`; ramified types have empty order-0 menu and their density is carried by the
undecided/deeper-order tail — out of Phase A scope, stated honestly.)

### A6. Multiplicities: wire the PROVED L3 necklace counts

`realF.multiplicity T_λ` := the residue-configuration count polynomial (number of ways to pick
distinct monic irreducibles with pattern λ — products of necklace counts `M_d(q)` with multinomial
corrections; `L3Gauss.gauss_necklace_count` + `L3.card_monicDegree` are PROVED, currently
decorative). ALTERNATIVELY fold `m_T` into `C_T` (make the per-shape coefficient the
pattern-density directly); then `multiplicity ≡ 1` stays honest. DESIGN DECISION for Asvin:
multiplicity-explicit (matches the paper's `ρ = Σ m_T C_T` and the DensityFoundation field) vs
folded (fewer moving parts). Recommend multiplicity-explicit — it is the L3 content the interface
was built for.

### A7. Truth restoration for the three hypotheses (order-0 forms)

* `h_node` (per-shape limit): for T_λ the normalized fiber count converges to
  `m_λ(q)·(volume factor)` — at order 0 the level-1 count already equals the limit times
  `q^{n(N-1)}·q^n`-scaling (fibers are exactly constant for N ≥ 1: an order-0-decided coset's
  lifts are all decided to the same shape — this is `CountingModel.cylinder_count_stable`, PROVED).
  So Phase-A `h_node` should be PROVABLE OUTRIGHT (finite level-1 count + constant-fiber
  stability), not cited: the genuinely hard across-level content only enters at order ≥ 1.
* `h_decided_mono`: with exact level-1 stability, decided fractions are CONSTANT for N ≥ 1 —
  monotone. Provable.
* `h_env`: undecided (= non-separable-reduction locus for the genuine order-0 classifier)
  has density ≈ 1/q, NOT → 0. **So Phase-A `h_env` as stated (≤ q^{-N}) remains FALSE** —
  the capstone's `CountingModel` semantics (decided limit = density) needs the undecided mass to
  vanish, which REQUIRES deeper-order refinement (Phase B). Two honest Phase-A options:
  (i) RESTRICT the capstone claim to the separable-stratum densities (change `densityVal`
  semantics to the order-0-decided limit and DROP the `undecidedVanishes`-dependent clauses);
  (ii) keep the full claim conditional on `h_env` (true only post-Phase-B). Recommend (i) as the
  Phase-A theorem (a TRUE unconditional-modulo-tame statement) with (ii) kept as the target form.
  ⚠ NOTE: option (i) touches `CountingModel`/`Decomposition` (the decided-limit vs density
  identification `density_isLimit`), so scope it carefully — it may be cleaner to state a NEW
  Phase-A capstone (`montes_order0`) alongside, leaving `montes_unconditional` as the Phase-B
  target.

### A8. Numeric acceptance tests (mandatory gate, cf. the cells:=[] audit gate)

Machine checks, not inspection:
1. **Non-vacuity probe (V1 reversal):** `∑_{T ∈ shapesOf σ} m_T(q)·coeff T q ≠ 0` for a concrete
   σ, `q = 2` — as a Lean `example` (decide/norm_num on the finite data) or via `#eval`-style
   rational evaluation.
2. **Cross-check vs closed forms:** for `n = 2, 3` compare the Lean tree-sum values at
   `q = 2, 3, 5` against `padic_types.py`'s separable-stratum densities (e.g. `n = 2`:
   split `(q²−q)/2 / q²`, inert `(q²−q)/2 / q²`, and `Σ_λ = 1 − 1/q`). Any mismatch = design bug.
3. **Fiber-count probe:** brute-force `#{f ∈ monicBox(2, 1, 2) : classify 1 f = T_λ}` in Python
   against the Lean stratumCount semantics for one or two λ.
4. **Re-run the `cells := []` falsifiability test** on every statement whose free params were
   pinned (A4's `cellsOfShape_descend`, the restated M8 axioms if touched).

**Phase-A effort estimate:** ~2-4 focused weeks with agents on bounded sub-lemmas; the design
decisions (A2 childSize units, A6 multiplicity placement, A7 option (i) vs (ii)) need Asvin's
sign-off FIRST (blueprint-first discipline).

---

## 2.5 ADDENDUM (2026-07-02, mid-implementation): findings from the A1–A4 build + the A6 aggregation mismatch

**A1–A4 implemented** (this session, build verification in flight):
* A1: `hDrLtCs` → `hDrLeCs : dr ≤ cs` (OMType field); all five literals re-discharged.
* A2: `rootResidual` guard weakened `< n` → `≤ n` (never fires for genuine residuals; the generic
  full-degree residual is now KEPT — the V1 zeroing is gone); `M5.cells` children now
  `childSize := μ·deg ψ` with the descent witness = the `if μ·deg ψ < cs` guard itself, and the
  full-budget repeated factor (`μ·deg ψ = cs`) EXCLUDED as the self-loop (absorbed into `countPivot`).
* A3: `classifyAux` emits the faithful payload `M5.encodeCells T` (was `[]`); child payloads inside
  `ShapeCell.children` stay schematic (Phase-B obligation).
* A5-prep (canonicalization): `M5.cells` sorts the factor list by degree (`List.mergeSort`) —
  `Finset.toList` order is representative-dependent, and without the sort same-λ fibers fragment into
  payload-order variants. Degree-sort fully canonicalizes separable payloads (equal-degree separable
  cells erase equal); non-separable same-degree ties are a Phase-B canonicalization obligation.
* A4: new guarded faithful reader `M7.cellsOfShapeWF` (filter: all payload children strictly
  descend) with `cellsOfShapeWF_descend` (∀-shapes, discharges `MontesData.cells_descend` with NO
  decode) and `cellsOfShapeWF_shapeOf` (identity on genuine shapes). `RealInstance` re-pointed from
  `M7.cells decode` to `M7.cellsOfShapeWF` throughout.

**The order-0 stratum picture that emerges (for A5/A7):** the generic stratum is `v(a₀) = 0` (flat
single side `(0,0)–(n,0)`, shared face). Separable patterns λ ⊢ n give tree `[(0,n,n)]` + payload
`[⟨dᵢ, 1, flatFace n, []⟩]` sorted — the menu is indexed by `Nat.Partition n` as DIRECT `ClusterShape`
literals (no polynomial witnesses needed: `M6.finiteTermination` consumes only the `treeSize ≤ n`
bound, provable from the root slot). Full-budget prime-power reductions (`f̄ = ψ^μ`, `μ·deg ψ = n`)
emit `Σ dS < n` payloads — off the separable menu, genuinely order-0-undecidable (the h_env
non-drain mass), exactly the montes_order0 exclusion.

**⚠ A6 DESIGN-CRITICAL FINDING (the Σ-vs-∏ aggregation mismatch).** For the multi-factor separable
root shape `T_λ`, the genuine per-shape density is
`lim stratumCount T_λ N / q^{nN} = m_λ(q) · q^{-n}`
(`m_λ(q) = ∏_d C(M_d(q), mult_d λ)` = the distinct-irreducible choice count, `M_d` = necklace counts;
`q^{-n}` = the volume of ONE level-1 coset; check: `Σ_λ m_λ(q) = q^n − q^{n−1}` = the separable
count). But `MontesData.C = clusterCount` aggregates per node as `(Σ_cells countCellCoeff · ∏_children) / pivot`
— a SUM over cells. For `k ≥ 2` cells the sum form provably cannot equal `m_λ(q)·q^{-n}` (e.g.
λ=(1,1), n=2: `2·bb1/pivot` vs `(q choose 2 …)·q^{-2}`-shaped). The single-cluster strata that all the
oracle/BCFG validation exercised have `k = 1`, where sum and product coincide — the multi-cell root
was never exercised because the density was identically 0 (V1). **Consequence: `h_node` as currently
shaped (limit = `clusterCount` value) would be FALSE for the repaired multi-factor shapes too.** The
per-node aggregation for a node whose cells partition the residual must be the CHOICE-COUNT ×
box-volume form, not the cell sum.

**Repair options (need Asvin + a reconciliation pass against `HUMAN_PROOF.md` eq-(4.2) before Lean):**
* (i) **Multiplicity-weighted MontesData**: keep `clusterCount` for per-cluster volumes; change the
  `Decomposition`/`MontesAxiom` layer so the per-shape coefficient is `m_T(q)·C_T(q)` with `m_T` a
  polynomial read off the shape's payload (`m_λ` from the dS-multiset). `h_node` then targets
  `m_T(realP)·C_T(realP)`; `coeff_isRational` = polynomial × rational (closure lemmas exist). This
  matches the signed-off "explicit m_T" decision and the paper's `ρ = Σ m_T·C_T`.
* (ii) **Corrected per-node recursion**: change `clusterCount`'s node form to a per-node
  `choiceCount(cells) × ∏_cells(per-cell volume) × ∏_children` product. More faithful to eq-(4.2) as
  one recursion, but revises the machine-checked `C_rec`/`clusterCount_boxSum` suite.
Recommend (i): smaller blast radius, keeps the banked `clusterCount` lemmas intact, puts the proved
`L3Gauss` necklace counts exactly where the interface expects them.
**Numeric gate before implementing either**: a Python harness computing, for `n = 2, 3`, `q = 2, 3, 5`,
the exact level-1 fiber counts per λ vs `m_λ(q)·q^{-n}·q^{n·N}` at `N = 1, 2` (and the `q^n`-fold
constant-fiber growth), cross-checked against `padic_types.py` closed forms.
**GATE RUN + PASSED (2026-07-02, exact brute force):** for all `q ∈ {2,3,5}`, `n ∈ {2,3}`, every
separable pattern λ: `#{monic f̄ : pattern λ} = m_λ(q) = ∏_d C(M_d(q), mult_d λ)` EXACTLY, and
`Σ_λ m_λ(q) = q^n − q^{n−1}` on the nose (λ = (1,1,1) at q=2 correctly impossible, `C(2,3) = 0`).
⚠ **AUDIT CORRECTION (SIGMA-2, 2026-07-02 adversarial audit):** this gate validates the
UNCONDITIONED pattern count `m_λ` (`M₁(q) = q`). The FORMAL per-shape stratum (the classifier fiber
of `sepShape λ` = the flat-face, unit-`a₀` substratum) has the PUNCTURED count
`m̃_λ` (`avail₁ = q − 1`, factor `X` excluded), and `m̃_λ = m_λ` iff λ has NO part of size 1. The
correct boxed identity for `M8.stratumCount` is `lim = m̃_λ(q)·q^{−n}`; gating the assembly against
the unconditioned `m_λ` MIS-GATES it (exact counterexamples at every λ with a 1-part). The §2.7
transcription gate (which uses `avail₁ = q−1`) is the correct gate. The excluded unramified mass
(separable reductions with residue root 0) is `(m_λ − m̃_λ)·q^{−n}` per λ — recovering it needs the
multi-side menu (Phase-A′ extension or Phase B).

## 2.6 ADDENDUM 2 (2026-07-02, engine reconciliation — the CORRECTED per-node semantics, numerically exact)

A read-only reconciliation agent extracted the per-node recursion from the ground-truth
`om_density_engine.py` (byte-identical copies in release-pasd/verification and uniform-rationality;
reproduces BCFG exactly through n=6) and validated the corrected form by exact brute force on: all 14
order-0 separable (q,n,λ) strata (q∈{2,3,5}, n∈{2,3}), the non-generic n=2 slope-−1/2 stratum
(p∈{2,3,5}, N∈{2,3}), and a NON-FLAT n=4 slope-−1/2 face with per-residual-shape resolution (p∈{2,3},
including a correctly-EMPTY stratum). Zero failures on the corrected form; the current-Lean column
fails everywhere except dS=1 leaf cells. Artifacts: /workspace-vast/asving/tmp/order0_reconcile/.

**THE CORRECTED `nodeMeasure_boxSum` TARGET** (in payload data; cell c = polygon Π_c + residual-shape
assignment {(D_i, μ_i)} per face F with extension degree δ_F; children paired to μ≥2 factors):

```
lim_N stratumCount T N / q^{nN}
  = ( Σ_{c ∈ cells T}  m_cell(c,q) · q^{−B(c)} · ∏_{ch ∈ c.children} C(ch, q^{δ_ch·D_ch}) ) / countPivot*(T,q)

m_cell(c,q) = ∏_F N_{S_F}(q^{δ_F}),  N_S(Q) = ∏_D ff(avail_D(Q), k_D)/∏ cnt!   (falling factorials),
              avail_1 = Q−1 on a genuine face (Q at the unconditioned order-0 root),
              avail_D = necklace M_D(Q) = (1/D)·Σ_{e|D} μ(e)·Q^{D/e}  (D ≥ 2)
B(c) = newtonExponent(Π_c) + Σ_F d_F      (pure lattice exponent; NO (1−q⁻¹)^V factor)
countPivot* = countPivot (treeSize T) at CLUSTER nodes (descent-conditioned, s ≥ 2); = 1 at the ROOT.
```
m_T × C_T split (signed-off explicit-m_T): m_T = ∏_nodes m_cell (order-0 separable: exactly m_λ);
C_T = ∏_nodes q^{−B}/pivots (order-0: exactly q^{−n}).

**The six pinned defects (D1–D6) in the current formalization** (full quotes in the reconciliation
report; none previously caught because the payload was always empty):
* D1: `(q^δ)^{dS−1}` is the AGGREGATE non-squarefree count, not the per-cell fine count `N_{S_F}`;
  and `M5.cells` sets `dS := ψ.natDegree` (factor degree), for which `q^{d−1}` counts nothing
  (necklace `M_d` is right; they coincide only at d = 1 — why all past single-cell validation passed).
* D2: `countCellCoeff` DOUBLE-COUNTS the residual: `bb1Value`'s exponent A already integrates over
  on-face residual values. Consistent pairings: count × per-configuration volume `q^{−B}` (B = A + Σd_F),
  OR `bb1Value` × shape PROBABILITY `N_S/(Q^d − Q^{d−1})`.
* D3: Σ-vs-∏ (already §2.5) — one cell per (polygon × full residual-shape assignment), product across
  faces, single choice count; NOT a sum over factors.
* D4: `clusterCount` divides EVERY node by `countPivot`; the pivot belongs only to cluster-law
  fixpoint nodes (β_e), NOT the order-0 root (the engine's top node is pivot-free). The pivot VALUE
  matches `L5fix.selfLoopExponent` exactly — only its placement is wrong.
* D5: eq-(4.1)/(4.2) as literally written in BB3_infinity.md is SCHEMATIC (overcounts by
  `∏_F(Q^{d_F} − Q^{d_F−1})`); the engine implements the normalized form. The notes' conclusions
  (rationality, p-independence) are unaffected; the formula is not usable verbatim as a measure
  identity — the Lean file formalized the schematic literally.
* D6: M6_lemma.md's fibre normalization `Q^{−d_r}` is inconsistent with its own unit-endpoint
  convention; the reliable primitive is the absolute per-configuration volume `q^{−B}` (punctured
  pair: avail₁ = Q−1 with norm (Q−1)Q^{d−1}).
* Also: children must be evaluated at the base-changed `q^{δ·D}`, not the parent's `q` (latent at
  order 0).

**Implementation consequence for option (i):** the MontesData surgery is now fully specified — the
`nodeMeasure_boxSum` field target becomes the boxed formula above (equivalently: keep `bb1Value` and
use the shape-probability pairing); `CountCell` needs the residual-shape data (the dS-multiset with
multiplicities per face) rather than one-factor-per-cell; `countPivot` moves to cluster nodes only.
This revises `MontesAxiom.CountCell`/`countCellCoeff`/`clusterCount` and their banked lemma suite —
the next work package, to be numerically re-gated per stratum after restatement.

## 2.7 ADDENDUM 3 (2026-07-02): the Wave-1 implementation architecture for §2.6 — ADDITIVE, not surgical

**Decision (autonomy granted; rationale = blast-radius + honest increments):** the corrected
semantics (§2.6) lands as PURE ADDITIONS in a NEW leaf module `LeanUrat/OM/Order0.lean`, leaving the
existing (documented-wrong-for-multi-cell) `clusterCount`/`MontesData.nodeMeasure_boxSum` path
untouched until Phase B retires it. No structure fields change; nothing existing rebuilds; the old
capstone stays honest-conditional (its `h_node` documented false-for-instance). Contents:

1. **Necklace/choice machinery**: `necklacePoly d = C(1/d)·Σ_{e ∈ d.divisors} C(μ(e))·X^{d/e}`
   (`ArithmeticFunction.moebius`), `ffPoly P k = ∏_{i<k}(P − C i)`, `availPoly d = X − 1` (d = 1,
   face-punctured) `| necklacePoly d` (d ≥ 2), `nodeChoicePolyQ cells = (∏_d ffPoly(avail_d, k_d)·C(1/k_d!)).comp (X^δ)`
   with `k_d` = the dS-multiset counts of the payload and δ from the head cell.
2. **Volume**: `nodeVolumeExp cells = newtonExponent(headPolygon) + Σ_c dS` (0 on `[]`);
   `rootCount T q = (nodeChoicePolyQ …).eval q · (q^nodeVolumeExp)⁻¹ · ∏_cells ∏_children clusterCount …`
   — NO pivot at the root (D4); children still on the old cluster recursion (dead for Phase-A
   childless shapes; base-change `q^{δ·D}` = Phase-B).
3. **Rationality**: eval-of-polynomial (num := P, den := 1) × inverse-q-power (num := 1, den := X^B)
   × list-product closure (add `isRationalFn_listProd` if absent) — all from RatFn.
4. **The menu** (A5): `Nat.Partition n` → direct `ClusterShape` literals
   `⟨[(0, n, n)], (sorted parts).map (fun d => ⟨d, 1, flatFace n, []⟩)⟩` where
   `flatFace n := M7.toSideFace (the (0,0)–(n,0) Side literal)` — MUST be checked equal to the
   classifier's emitted `rootFace` on the generic stratum (a defeq/lemma gate; if `npSides`' Side
   representation differs, adjust the literal, not the classifier).
5. **`montes_order0`** (A7): for unramified σ with pattern λ, conclusion = uniform RATIONALITY of
   `q' ↦ Σ_{T ∈ menu_σ} rootCount T q'` (= `m_λ(q')·q'^{-n}`) + the value tie at `realP`, taking as
   explicit hypothesis `h_node0` the per-menu-shape limit (level-1 decidedness + constant `q^n`-fold
   fibers make it PROVABLE later via `cylinder_count_stable` — the Phase-A truth-restoration target).
   NO palindromy clause: the separable-stratum monic density is genuinely non-palindromic; palindromy
   belongs to the full projective density (Phase B).
6. **The one genuine new math obligation**: `density_nonneg`-grade facts need necklace
   INTEGRALITY + NONNEGATIVITY at every natural `q` (the Witt/aperiodic-word count over an arbitrary
   `q`-letter alphabet — Gauss congruence `d ∣ Σ_{e|d} μ(e)q^{d/e}` + `≥ 0`), NOT just prime powers
   (`L3Gauss` covers finite fields only). Self-contained, mathlib-searchable (Möbius inversion on
   periodic words); a good bounded agent task. Until it lands, `montes_order0` should avoid needing
   pointwise nonnegativity (state rationality + value tie only, no `DensityFoundation` packaging).

Numeric gates for Wave 1 (mandatory): re-run the §2.6 tables against the LEAN `rootCount` values
(via `#eval`-style rational evaluation or a transcription check) for all 14 order-0 strata + the
non-flat n=4 face; the menu/classifier face-equality gate (item 4); the `cells := []` falsifiability
test on any new ∀-shape statement.
**TRANSCRIPTION GATE RUN + PASSED (2026-07-02): 15/15** — the Lean `rootCount` formula (avail₁ = q−1,
B = n on the flat face) = brute-force `v(a₀) ≠ 0` separable stratum densities exactly, including the
correctly-empty λ = (1,1) at q = 2 (`ff(q−1, 2) = 0` reproduces the x-exclusion for free).

**§2.7.1 The `h_node0` discharge plan (the last Phase-A math; three bounded packages):**
* **(α) mod-p cylinder stability on the generic stratum**: for `v(a₀) = 0` cosets, `classify N f`
  depends only on `f mod p` (unit valuations read exactly at every level; flat side; residual =
  reduction). Hence the level-`N` fiber of `sepShape λ` = (level-1 fiber) · `p^{n(N−1)}`, so the
  normalized count is CONSTANT in `N ≥ 1` and the limit is trivial (`tendsto_const_nhds`). This is
  an f-keyed reduction-stability instance FAR easier than the general wall (everything reads mod p);
  Lean-engineering through `boxValSupport`/`npSides`/`rootResidual`.
* **(β) the level-1 count identity**: `#{f̄ : v(a₀)≠0, separable, pattern λ} = ∏_d ff(avail_d(p), k_d)/k_d!`
  — finite-field combinatorics: `L3Gauss.gauss_necklace_count` (the degree-d irreducible count) +
  the choose-k-distinct counting (`Finset.card_powersetCard`-style) + the x-exclusion at d = 1.
  Classical, bounded; this is where the PROVED L3Gauss content finally becomes load-bearing.
* **(γ) the face-equality gate**: on the generic stratum the classifier emits EXACTLY the
  `sepShape λ` literal — `npSides` of the flat support = `[flatSide n]` (the banked hull machinery:
  vertices of all-height-0 dots = `[(0,0),(n,0)]` after `dropCollinear`), `rootResidual` = `f̄` with
  `natDegree = n` (un-guarded now), payload sort = `mergeSort` by degree ascending = the menu's
  `parts.sort (· ≤ ·)`.
After (α)+(β)+(γ), `h_node0` becomes a THEOREM at `realP` and `montes_order0` fires unconditionally
(modulo Lean core only — no tame cite needed since it makes no palindromy claim): the first
genuinely NON-VACUOUS machine-checked density statement in the development.

## 3. Phase B — the genuine draining classifier (the long pole, unchanged)

The f-DEPENDENT depth-≥1 classification: lift `boxCoeffData` through the key polynomial of the
selected side, build the order-(r+1) context from the order-r one (GMN §2-3), so that
non-separable cosets refine as N grows and the undecided mass genuinely decays (`h_env` becomes
true; `discZeroValTail_density`'s intended content). Components (all previously scoped):
* the order-r residual/Newton machinery on lifted coefficients (M3/M4 exist; the LIFTING is new);
* `certLevel_stabilizes` (f-keyed reduction stability) — the across-level cylinder identity;
  its remaining sorry chain: `npVertices_stable_of_hull_preserved` (HULL_BLUEPRINT; in progress)
  → `boxValSupport_reduce_stable_R` → `oneDigitCylinder_fkeyed` (built) + the honest f-keyed GMN
  cite `omReadValuation_lt_of_certLevel_fkeyed` (properly constrained, sound);
* the `h_node` discharge chain per HNODE_GENUINE_FIX_BLUEPRINT.md (IsGenuineOM-constrained
  restatements of `L2_reconstruct` / `selfLoop_childFiber` / `boxVolumeScale_collapse`, then
  `nodeTrunc_tendsto_OM` via the banked `firstOrder_recurrence_limit_rat`).
Phase B is the multi-month, human-supervised effort; agent sweeps historically fake-close here
(twice) — keep the per-axiom falsifiability audits mandatory.

---

## 4. Post-fix trusted-base ledger (expected, to be re-verified by `#print axioms` after the build)

**Axioms remaining in the whole tree** (excluding Lean core):
* `realDensity_tame_functionalEquation` (RealInstance) — concrete, pinned, the paper §5 cite.
  Currently trivially true (density ≡ 0); becomes the genuine cite after Phase A. ON the capstone.
* `PadicMeasure`: `clusterMeasure`, `AX_cellRecursion`, `omCells`, `descend_size_lt` — the OLD
  measure route (only `goal_theorem` uses them; sound-as-refactored per audit).
* `Classifier.omReadValuation_lt_of_certLevel_fkeyed` — f-keyed GMN Cor 4.19 cite, properly
  `v_p(disc) < N`-constrained (audit: SOUND). Off capstone.
* `CountingModel.selfLoop_childFiber_fkeyed` (A6), `LevelNCount.L2_reconstruct` (A7),
  `selfLoop_childFiber_corrected` (A9), `boxVolumeScale_collapse` (A10) — ⚠ ALL FALSE-AS-STATED
  (free cells), ALL FLAGGED, ALL OFF every capstone footprint. To be replaced by the
  `IsGenuineOM`-constrained versions (HNODE blueprint) — do NOT consume as-is.
**Deleted this round:** `tame_functionalEquation` (U1), `AX_columnMeasure` (U3),
`gmn_node_ef_law` (U4, → `GMNNodeEfLaw` hypothesis), `discZeroValTail_density` (A11, REFUTED),
`decidedDensity_mono_realP` (A12, unauditable), the sorry-over-false `M8.nodeMeasure_boxSum` (U2).

**Capstone statuses (expected footprints):**
* `Goal.goal_theorem_montes`, `goal_theorem_via_montes`: `[propext, Classical.choice, Quot.sound]`
  — Lean core ONLY (tame is now the `htameFE` hypothesis).
* `OM.M9.montes_unconditional`: core + `realDensity_tame_functionalEquation`; hypotheses
  `h_node`, `h_decided_mono`, `h_env` (all false-for-instance until Phase A/B — the theorem is
  sound but currently certifies nothing about the degenerate instance).
* `Goal.goal_theorem` (old measure route): core + the 4 PadicMeasure axioms.
* `Witness.montes_full_instance`: core only (tame hypothesis PROVED via `trivF_tame`).

**Sorries remaining (all disclosed, off-capstone):** `Classifier.certLevel_stabilizes` cluster
(`npVertices_stable_of_hull_preserved` being the live one), `LevelNCount.nodeTrunc_tendsto`
(flagged false-as-stated, do-not-wire), `L3.lean:159,182` (superseded stubs), plus prose-sorries.

---

## 5. Order of work (recommended)

1. **[this session]** Soundness round above + hull lemma attempt + this blueprint. ✔
2. **Asvin sign-off** on A2/A6/A7 design decisions (childSize units; multiplicity placement;
   Phase-A capstone form (i) new `montes_order0` vs (ii) conditional retention).
3. **Phase A** (A1→A8 in order; A1-A4 mechanical-ish, agent-assisted with the falsifiability
   gate; A5-A6 the genuine order-0 math; A7-A8 the payoff + tests).
4. **HNODE chain** (IsGenuineOM restatements) — can proceed in parallel with Phase A after A3/A4
   (it needs the genuine cells to be non-empty for `cellsOfShape_ne_nil`).
5. **Phase B** (draining classifier / certLevel) — the long pole, human-supervised.
