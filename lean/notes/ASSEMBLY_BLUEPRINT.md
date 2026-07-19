# ASSEMBLY_BLUEPRINT — wiring the verified engine into the unconditional all-orders density

2026-07-07. The remaining formal work: assemble the machine-checked pieces (omCount recursion +
its rationality; the restart lemma at all orders; CellCard cell counts; Drainage; the order-0
capstone) into an UNCONDITIONAL `∀ n σ, ρ(n,σ;q) = R_σ(q)` at all primes incl. wild. Written
math-and-blueprint-first (Asvin's rule; PHASEB §5 fake-close warning applies hardest to h_node).

## Precise current state (verified 2026-07-07)
- `omCount T q` (OMCountV2:300) — the corrected per-node recursion — is DEFINED for all shapes and
  `omCount_isRational` (:497) is PROVEN (rationality of the recursion value, all shapes).
- `omDensityV2 n σ q := Σ_{T ∈ omMenu n σ} omCount T q` (:318), `omDensityV2_isRational` (:523) PROVEN.
- BUT `omMenu n σ := sepShapesOf n σ` (:311, DEFINITIONALLY order-0) — the genuine all-orders menu
  (cluster-bearing shapes with `typeOf T = σ`) is NOT yet built. So omDensityV2 = the order-0
  density today.
- `h_node0` (the value tie) is discharged only for separable/leaf shapes (Order0Capstone
  montes_order0 takes `h_node0`; Order0Alpha h_node0_proved supplies it). The cluster-bearing
  value tie `h_node` is OPEN.
- The restart lemma (RestartEquivGenH, r_level_census_equiv), CellCard, Drainage are proven but
  STANDALONE — no capstone imports them yet.

## The target
`montes_allorders_unconditional : ∀ n (hn:0<n) σ, ∃ R ∈ ℚ(t), (∀ q>1, ρ(n,σ;q)=R(q)) ∧ (value tie)`,
where ρ is the genuine density (∑ over the FULL menu of the genuine stratum counts). Extends
montes_order0_unconditional from the separable slice to all strata.

## Honest three-stage decomposition (each gate/blueprint-first; S1 tractable, S2 the crux, S3 the long pole)

### S1 — the ASSEMBLY SKELETON (conditional capstone), tractable NOW, core-only
Generalize montes_order0's PROOF STRUCTURE from `(sepShapesOf, rootCount)` to an arbitrary menu +
`omCount`, taking the two open pieces as explicit hypotheses:
```
theorem montes_allorders_of_hnode (n : ℕ) (σ : FactorizationType) (M : Finset ClusterShape)
    (h_node : ∀ T ∈ M, Tendsto (fun N => M8.stratumCount (M9.rawCount n) T N / realP^(n*N))
                          atTop (nhds (omCount T realP))) :
    ∃ num den, den ≠ 0 ∧ (∀ q'>1, den.eval q' ≠ 0 ∧ (∑ T ∈ M, omCount T q') = num/den) ∧
      Tendsto (fun N => (∑ T ∈ M, M8.stratumCount (M9.rawCount n) T N)/realP^(n*N)) atTop
        (nhds (num/den))
```
Proof = montes_order0's verbatim structure with `rootCount_isRational_of_leaf` → `omCount_isRational`
(PROVEN, no leaf hypothesis needed) + `isRationalFn_finsetSum` + `tendsto_finsetSum` on h_node.
This is the SKELETON: it turns "the complete theorem" into exactly "(a) exhibit the genuine
all-orders menu M, (b) discharge h_node on M". Core-only, delegable now. GATE: it must specialize
to montes_order0 at M = sepShapesOf (via omCount_sepShape_eq_rootCount) — prove that corollary.

### S2 — the h_node DISCHARGE at ORDER 1 (the crux) — STATEMENT CORRECTED 2026-07-07 by the gate

⚠ **S2 GATE FINDING (the naive statement is FALSE for cluster shapes; box vs M_e measure).** The
gate (/workspace-vast/asving/tmp/phaseb_s2gate/, p=2&3, two independent classifiers agreeing
g-by-g) found: for a cluster-bearing T, the per-box-classify count `stratumCount(T_box,N)/q^{nN}`
does NOT converge to `omCount(T)`. The self-loop tower ratio at the BOX level is the bare
Vandermonde Jacobian `q^{−s(s+1)/2}` (= q^{−3} at s=2), whereas `omCount`'s
`countPivot(s)=1−q^{−(s(s+1)/2−1)}` (the `−1`) assumes ratio `q^{−(s(s+1)/2−1)}` (= q^{−2}).
Reconciliation, exact: `box-limit = omCount · (1−q^{−(s(s+1)/2−1)})/(1−q^{−s(s+1)/2})`
(p=2: (2/3)(6/7)=4/7 ✓; p=3: (3/4)(12/13)=9/13 ✓). ROOT CAUSE: `omCount` computes the DENSITY in
the `M_e` cluster measure, which identifies the `q` residue-translate cosets of a self-loop level
(a ×q freedom quotiented out); `stratumCount` is a box `Nat.card` that counts those `q` cosets as
DISTINCT box strata. R0's 69/69 missed it because R0 only brute-checked the depth-1 term (same in
both measures) + `β` vs engine separately — never the box self-loop tower sum (= exactly S2).
This corrects NO landed result: order-0 (no self-loop clusters) and every single finite-depth cell
are unaffected (gate: PASS, N-independent); the restart-lemma equivalences and card lemmas are
unaffected (they are per-cell/per-level, not the tower sum). It corrects the S2 STATEMENT only.

**CORRECTED node-limit statement (option 2 — target stays `omCount` = the validated DENSITY).**
`omCount` IS the correct density (R0-validated); the fix is the box↔engine-shape correspondence.
The h_node target is the AGGREGATE over the residue-translate cosets that the engine's shape T
represents:
```
  ( Σ_{T_box : engineShapeOf T_box = T}  M8.stratumCount T_box N ) / realP^(nN)  →  omCount T realP
```
i.e. h_node must sum the box-classify strata that map to one engine-shape T (the residue translates
the M_e measure quotients). Equivalently, the CellCard per-level decomposition must expose the `q`
residue-translate cosets of each self-loop level as `q` DISTINCT box strata, so the per-level factor
becomes `q · q^{−s(s+1)/2} = q^{−(s(s+1)/2−1)}` = exactly `countPivot`'s exponent. The restart
lemma already supplies the `q` new residues (the residue field grows by the descent) — they must be
counted as separate cosets, not identified. (Option 1 — redefine `countPivot` to drop the `−1` —
is REJECTED: it would make `omCount` the single-coset box count, NOT the density, breaking the
whole point.)

The factorization then (per corrected statement):
1. **Level-N node decomposition** (CellCard): `Σ_{T_box↦T} stratumCount(T_box,N) = Σ_{cells c}
   (cell census m_cell·q^{-B}) × (residue-translate multiplicity q per self-loop level) × Π_children
   (aggregated child stratum count)` + undecided. CellCard.cell_partition + cell_card_raw give the
   per-cell count; the ×q residue-translate multiplicity is the correction; the CHILD aggregated
   counts come from the RESTART LEMMA (children are fresh cluster problems at the advanced residue).
2. **Drainage** (Drainage.tendsto_tailDensity_zero): undecided mass → 0.
3. **The limit = omChildCount's value**: with the ×q multiplicity, the self-loop geometric series
   resums with ratio `q^{−(s(s+1)/2−1)}` = `countPivot`'s, so the limit = omChildCount T realP.
   Induction on tree depth, base = h_node0 (leaf). The gate CONFIRMS this corrected factorization
   (per-level box decomposition 0-mismatch; the ×q residue translates are the exposed cosets).
✅ RE-GATE DONE 2026-07-07 (/workspace-vast/asving/tmp/phaseb_s2regate/): the AGGREGATED count
(sum over T_box↦T) → omCount CONFIRMED, gap→0 at rate q^{−2} (p=2: −1/12,−1/48,−1/192,−1/768;
p=3 analogous), n=2 AND n=3; the ×q-per-self-loop-level multiplicity converts q^{−s(s+1)/2} →
q^{−(s(s+1)/2−1)} = countPivot's exponent EXACTLY (s=2: 1−q⁻²; s=3: 1−q⁻⁵). Corrected §S2
statement is numerically CONFIRMED and Lean-ready. NO re-derivation needed.

S2 LEAN SUB-STRUCTURE (the discharge, coordinator-scoped — fake-close zone, do sub-piece by
sub-piece with a footprint gate each): (i) BRIDGE `M8.stratumCount T N` ↔ the CellCard/classifier
cell-partition count at order 1 (the h_node0 discharge did this at order 0 — generalize; likely
the first real sub-gap, check whether the genuine order-1 classifier's stratum count is even wired
to CellCard's InCell fibers); (ii) the per-node DECOMPOSITION with the ×q residue-translate
multiplicity exposed (CellCard.cell_partition + the q new residues from the restart descent as
separate cosets); (iii) the child-as-fresh-cluster identification (RestartEquivGenH /
r_level_census) tying the child stratum counts to omChildCount's recursion; (iv) Drainage (undecided
→ 0); (v) the geometric self-loop resummation (Drainage + SelfLoopTower) giving countPivot; (vi) the
limit + tree induction (base h_node0). Sub-piece (i) is the prerequisite and the first to scope.
GATE: numeric — the order-1 cluster h_node limit against the brute-force stratum counts (reuse
phaseb_w0 / restart_gates classifier) at p=2, N growing, for the slope −1/2 / self-loop cells;
confirm the limit = omCount before the Lean. This is COORDINATOR-BLUEPRINTED work (fake-close
zone); deliver the limit-wiring lemma with the restart lemma + CellCard + Drainage as the named
inputs, STOP-and-report if the child-as-fresh-problem identification resists.

### S3 — the GENUINE all-orders menu + h_node at all orders (the long pole)
(a) `omMenu` extended to the genuine Phase-B menu: all shapes T with `typeOf T = σ` (typeOf reads
the (e,f) data off the payload; the genuine order-r classifier emits these). Needs the genuine
order-r classifier STEP (the v_r reader, the tower development — DevelopTower/TowerBase give the
ring side; the CLASSIFIER walk that produces the shapes is the remaining construction). (b) h_node
at all orders by induction on order, the step = S2's order-1 argument over the tower child ring
(r_level_census_equiv gives the tower restart). Then `montes_allorders_unconditional` =
`montes_allorders_of_hnode` at M = the genuine menu with h_node discharged. This is the F-C
capstone; it consumes S1 (skeleton) + S2 (order-1 discharge) generalized via the tower.

## ✅ S3 PROGRESS (2026-07-08, build #37) — single-side childless family COMPLETE
Module `OM/PathShape.lean` (all core-only, adversarially verified, audit #37 SOUND):
- `oneSideShape s pr shape := ⟨[(1,s,1)], shape.map (q ↦ ⟨q.1,1,mkPoly s [pr.1,pr.2],[]⟩)⟩` — the
  (s, Newton-path, residual)→ClusterShape CONSTRUCTOR, ONE CELL PER FACTOR (generalizes decidedTc).
- `configsOf_oneSideShape` — the engine↔classifier BRIDGE: configOf(oneSideShape) = [mkCell s [pr.1,pr.2]
  [shape]] field-for-field, single-side all-μ=1. (Multi-side DIVERGES: configOf aggregates a node's sides
  into ONE face, mkCell keeps one face per side, choicePoly not multiplicative across face vars — deferred.)
- `omCount_oneSideShape_closed` — omCount = shapeCount·p^{-(newtonExponent(mkPoly)+sideDeg)}, engine value
  in closed form tied to the count keystone. S2C1 → 1/8.
- `mkCell_volExp_add_freeExp` — the box identity volExp(mkCell s P sh)+freeExp s N P = s·N (span=s via
  chainOK_run_sum telescoping).
- `hnode_oneSideShape` — THE FIRST GENUINE CLUSTER-SHAPE h_node: stratumCount1(mkCell s P [shape])/p^{sN}
  → omCount(oneSideShape s pr shape), single-side childless. Real order-1 stratum density (classify1
  fiber) of a SLOPED shape ties to the engine, natural p^{sN} box, genuine limit.

## ✅ S3 PARALLEL ROUND (2026-07-08, build #38) — bridge 3/4 + childful landed
BRIDGE (`OM/ClassifierBridge.lean`, core-only): the order-1 single-side childless h_node is CONNECTED to
the REAL density modulo ONE named lemma. KEY: `omCount` is configsOf-AGNOSTIC to the tree-head order slot
(reads only cellsOfShapeWF cells + nodeSizeOf), so B.classify's order-0-head output
`Tselfloop = ⟨[(0,n,dr)],cells⟩` and `oneSideShape`'s order-1-head literal have the SAME omCount —
`omCount_selfloop_eq_oneSideShape` is UNCONDITIONAL. `stratumCount_selfloop` + `hnode_selfloop_over_Bclassify`
give the h_node in EXACTLY `montes_allorders_of_hnode`'s shape (limit of
`M8.stratumCount (M9.rawCount n) (Tselfloop) N / realP^{nN}` → `omCount(Tselfloop) realP`), CONDITIONAL on
the fiber-iff `hfiber`.

★ THE SINGLE REMAINING BRIDGE OBLIGATION (sharpened): `classify_eq_selfloop_iff` —
`B.classify realP n N f = Tselfloop n pr shape ↔ InCell realP f (mkCell n P [shape])`, single-side all-μ=1.
Forward half needs a NEWTON-POLYGON UNIQUENESS lemma not yet in repo:
`NewtonPolygon.npSides (boxValSupport realP N f) = [mkSide pr]` from `InCell`'s vertex-exactness
(`vOf p f q.1 = q.2` on P) + `SideAbove`; then residual `= residualOf p f pr`, all-μ=1 (squarefree) ⟹
`classifyAux_of_childless` collapses `B.classify` to `Tselfloop`. Route = the order-1 analogue of the
PROVEN `Order0Alpha.classify_eq_sepShape_iff`. Plus a notational polygon respell (Tselfloop.cells polygon
`mkPoly`→`toSideFace(mkSide pr)`, omCount-invisible). Discharging it ⟹ UNCONDITIONAL order-1 single-side
density theorem via the S1 skeleton (n = s; general degree needs block-product/drainage).

CHILDFUL (`OM/PathShapeChildful.lean`, core-only): `oneSideShapeChildful` (genuine μ≥2 descent children),
`omChildCount_childShape = 1/countPivot` (empty-payload collapse; RESTART not needed), closed form, and
`hnode_oneSideShapeChildful` (stratum limit → the RAW finite value `shapeCount·p^{-V}`, NO pivot).
★ FINDING: at a childful cell `limit ≠ omCount` — proved `omCount_eq_limit_mul_pivot`
(`omCount = limit·∏ pivot`, pivot arg `p^D` base-changed), NOT a false `limit = omCount`. So the FULL
child-bearing h_node must carry the pivot in the normalization (analogue of the p^run finding).

DEFERRED: multi-side (configOf aggregates a node's sides into one face; needs the children-per-side tree
redesign). On the critical path to `montes_allorders_unconditional` after the fiber-iff lemma.

## ✅ KEYSTONE CLOSED (build #34, 2026-07-07) — cell census UNCONDITIONAL at all orders
`ShapeCountTie.shapeCount_tie_general` (UNCONDITIONAL, core-only) + `cell_card_mCell_uncond` (the
per-cell census `Nat.card{InCell} = mCell·p^freeExp` with `hties` DISCHARGED). Proof: multiplicativity-
over-degrees crux (`card_shapeSet_prod`, UFM bijection) + single-degree multinomial count
(`single_degree_count`, via `DomMulAct.stabilizer_card'` for ∏c_μ! and `Fintype.card_embedding_eq` for
descFactorial). Only hyp = positivity, auto from ShapesFor. This section's decomposition below is the
record of how it was built. IMPACT: every order's density count no longer needs banked per-shape ties.

## KEYSTONE (record) — the GENERAL shapeCount = choicePoly tie (discharges `cell_card_mCell`'s `hties`)
2026-07-07. `CellCard.cell_card_mCell` (:2083) — the per-cell census `Nat.card{InCell} = mCell·p^freeExp`
that feeds EVERY order's density — is unconditional EXCEPT for the hypothesis
`hties : ∀ l ∈ sh, (shapeCount p l : ℚ) = (choicePoly true l).eval p`. Per-shape ties are banked
(`shapeCount_tie_one_one/_one_two/_two_one/_split_two`); the GENERAL tie is the named-open keystone.

✅ GATE (2026-07-07, /workspace-vast/asving/tmp/mcell_shapecount_gate.py): brute enumeration over
F_p[X] (monic, prime to X) vs the engine polynomial `∏_d ff(N_d,k_d)/symFactor` evaluated at p.
35 cases, p=2,3,5, incl. μ>1 ([(1,2)],[(2,2)],[(1,2),(1,1)]) AND multi-degree
([(1,1),(2,1)],[(1,1),(1,1),(2,1)]) — ALL MATCH. So the count identity is GENERAL (not just
single-side all-μ=1); the DecidedOmCountTie "all-μ=1 only" caveat was about the SEPARATE
`volExp = −net` exponent bookkeeping, NOT the count. This de-risks the general decided tie AND every
cell census.

DECOMPOSITION (the math blueprint for the Lean proof — general `shapeCount p l = choicePoly.eval p`):
1. **Multiplicativity over degrees** (the crux): M prime-to-X of shape l factors uniquely as
   M = ∏_d M_d (coprime, M_d = product of the degree-d irreducible factors). shape l splits l = ⊔_d l_d
   ⟹ `shapeCount(l) = ∏_d shapeCount_d(l_d)` — a `Nat.card` product over distinct degrees via
   coprime-CRT / UniqueFactorizationMonoid. HARDEST structural lemma.
2. **Single-degree count**: shapeCount_d({μ_1..μ_k}) = choose k DISTINCT degree-d irreducibles from the
   pool N_d assigned to μ-slots (equal-μ slots unordered) = `ff(N_d,k)/∏_μ(count μ)!` = the choicePoly
   degree-d factor. Counting injections up to symmetry.
3. **N_d = necklace** (HAVE): N_d = #monic irred deg d over F_p = `necklacePoly d`.eval p, via
   `Order0.necklaceQ_eq_card`/`L3Gauss.gauss_necklace_count`. d=1 PUNCTURE: prime-to-X excludes X
   itself, so available deg-1 pool = p−1 = availPoly(1)=X−1 (matches). 
Base-case ties (one_one/one_two/two_one/split_two) are the sanity anchors. This tie, once closed,
makes cell_card_mCell UNCONDITIONAL for all shapes — a keystone for S2/S3 h_node at every order.
SEPARATE remaining half of the general DECIDED tie: `volExp(configOf T_c) = s(N₀−1) − freeExp`
(N-independent via DecidedOrder1.freeExp_eq_add_mul); proven single-side μ=1 (volExp_decidedConfig=1);
multi-side needs the general decided ClusterShape constructor (generalize decidedTc).

## Delegation order & honesty
S1 now (skeleton, core-only, quick). S2 next, coordinator-blueprinted with a numeric gate FIRST
(the fake-close zone). S3 is the long pole (genuine classifier walk + all-orders induction) — a
sequence of waves, not one. Until S3 lands, the UNCONDITIONAL theorem is order-0 only; S1 makes the
conditional all-orders theorem explicit and S2 makes the first deeper case genuine. NO stage claims
the complete theorem until S3's menu + h_node are both unconditional. The restart lemma being done
means S2/S3 are assembly of verified pieces, not new analytic discovery — but the classifier walk
(S3a) is genuine remaining construction, not wiring.
