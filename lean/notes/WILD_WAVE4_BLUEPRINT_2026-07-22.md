# WILD_WAVE4_BLUEPRINT — mixed-e types via multi-slope strata with product coefficients

**Date: 2026-07-22. Under the iterate-to-completion directive. Grounded in: the multi-slope asset
survey (2026-07-22) + `MATH_FULLTYPE_DECOMPOSITION_2026-07-22.md` (pass-1 verified: Case D re-run
exactly; W4 untouched by the findings).**

## §0. Goal and scope

Extend the certified σ-keyed menu to MIXED-e types: multi-slope Newton polygons, all-μ=1 per-side
residuals, order ≤ 1. First increment: **all side-e's ≥ 2 and pairwise distinct** (one side per
distinct e, canonical minimal height k=1 per side; slopes −1/e strictly increasing as e decreases).
DEFERRED (named): e=1-mixed types (need the flat slope-0 side supported in the path machinery —
check `MenuPath`/residual reading on flat sides before attempting); same-e multi-side (two sides,
same denominator, different heights — a later window); per-side K-windows.

## §1. The established ground (do not re-derive)
- `hnode_multiSideProduct` (PathShapeMultiSideTree:252): PROVED stratum limit = ∏_side
  `omCount (sideSubShape pr shape) p` at PLAIN p (per-side width re-scoping, no base change).
- `prod_omCount_eq_blockCardinality` (:292): the product = `prodSC p sh · p^{-(newtonExponent +
  Σ sideDeg)}` — the multiplicity × volume split for `DensityFoundation.decomposition` (which
  constrains ONLY the sum identity).
- `stratumCount1_eq_closed` (StratumOrder1:82): general multi-side closed count; fibers are
  `classify1`/`InCell` fibers (`stratumCount1_eq_cellCard`), NOT `B.classify` (which reads only the
  first side — recorded no-go; the abstract-C design does NOT need the product to be an omCount
  summand, so the `omDensityV2`-folding no-go is respected, and `obligation_hensel_surjective`'s
  semantic content routes to the W4c axiom extension = GMN Thm 1.15/1.19, paper-stated).
- `MontesDataV2` demands only `C_isRational` + `stratum_tendsto_C` — product-form C admissible with
  zero spine edits.

## §2. Design

### W4a — `OM/MultiSlopeMenu.lean` + prep
1. **The literal family** (the tree-index encoding, designed to extend to W5): for a path `P`
   (vertex list) and per-side shapes `sh`, mint
   `multiSideLit P sh : ClusterShape` with `tree := (1, n, (sidePairs P).length) :: P.map (fun v =>
   (0, v.1, v.2))` (the TREE carries the full path — pure numeric data, injectively) and
   `cells := for side j, for each part (f,1) of sh_j: ShapeCell ⟨dS := f, δ := j+1, face :=
   toSideFace (mkSide pr_j), children := []⟩` (δ = side tag ⟹ cells group by side without face
   injectivity questions). Decode `(P, sh)` from tree+cells; prove `multiSideLit_injective`.
   Distinguishability from ALL existing families: head order-slot 1 vs order-0 heads (sepShape
   `[(0,n,n)]`, Tselfloop `[(0,n,F)]`) — a one-lemma discriminator.
2. **σ-keying**: `typeOf4 (T)` — on multiSideLit heads: per side j read e_j := run_j/sideDeg_j
   (from the tree's P), f-parts := {dS of cells with δ = j+1}; σ := ⋃_j {(e_j, f)}. On old heads:
   defer to `typeOfW`. Prove recovery on the canonical family + cross-family/cross-σ disjointness.
3. **The canonical menu**: for σ with distinct e's ≥ 2 (each (e, f-parts-of-that-e) group):
   `mixedShape σ := multiSideLit (canonical path) (per-side wShape-style parts)` — sides ordered by
   increasing slope (decreasing e), side for group e: run = e·(Σf), drop = Σf (k=1 minimal).
   Admissibility: `MenuPath` (H_total = Σ drops; threshold N₀ = H_total + 1), `ShapesFor` (per-side
   partition of sideDeg = Σf via the gcd argument per side), `AllMuOne`, `AllNonempty`.
   `omMenu4 n K σ := omMenuW3 n K σ ∪ (mixedShape σ).toFinset` (empty extra branch unless σ is
   mixed-all-e≥2).
4. **The unified stratum count**: `stratumCount4 T N` := for multiSideLit T, `stratumCount1 p n N
   (mkCell n P sh)` (decoded); else `M8.stratumCount (M9.rawCount n) T N`. Cross-family fiber
   DISJOINTNESS (the box-bound keystone; all provable — the InCell conditions pin the polygon
   exactly): (i) vs order-0 (unit a₀ vs H ≥ 1); (ii) vs full-width Tselfloop (a ≥2-side polygon's
   InCell excludes the single-full-side InCell — vertex exactness); (iii) within multi-slope
   (different P ⟹ different pinned polygon; same P different sh ⟹ different pinned residual).
   NOTE: the two fiber notions live on the same box (`monicBox p N n`); the disjointness statements
   are between SUBSETS of the box, mixing `B.classify`-fibers and `InCell`-sets — state them at the
   set level. Small-N vanishing (MenuPath needs H_total ≤ N−1); level constancy (freeExp — banked,
   general P); windowed box bound + full monotonicity (staircase sum, mirroring W3a).
5. **The coefficient**: `C4 T` := for multiSideLit: `∏_side omCount (sideSubShape …)`; else
   `omCount T`. `C_isRational` via a product closure (`isRationalFn_listProd` — check RatFn, else
   ~10 lines); `stratum_tendsto_C` via `hnode_multiSideProduct` (+ the stratumCount1 bridge).

### W4b — `OM/RealInstanceW4.lean` + gates
`realMW4 n K hn` (decidedCount over omMenu4 with stratumCount4; typeMenu grows by the mixed types
— finite: partitions of n into distinct-e≥2 groups), `realDW4` (C := C4), `realFW4` (decomposition:
per-family split — omCount_eq_mul_all for old shapes, blockCardinality for multi-slope; multiplicity
polynomial := prodSC-as-polynomial), capstones `montes_unconditional_w4 (n K)` verbatim-modulo-menu
+ recovery gate (`omMenu4 = omMenuW3` on non-mixed σ). Gates: n=5, σ = {(2,1),(3,1)} (sides slope
−1/3 then −1/2), value computed both by the Lean product and the external brute force (p=2, N=4:
2^20 boxes); a σ-separation pair; census; C4 := 0 mutation.

### W4c — axiom extension #3 + guardian ceremony
Re-scope `om_leaf_faithful`'s menu to `omMenu4` (adds the mixed literals; the (e,f)-multiset
conclusion σ now mixed — content: GMN Thm 1.15 (slope dissection into coprime factors, one per
side) + per-side Thm 1.19/Cor 1.20; cite both; the derivation-back theorem for the W3 form).
Axiom-free anchors: at the n=5 gate stratum prove (a) the polygon forces a factorization-shape
constraint refutable under a wrong-σ mutation — minimum: the fiber members have NO root in ℚ_p with
valuation of denominator ∉ {2,3} (or an irreducibility/degree constraint strong enough for a probe);
design the strongest cheap anchor available (the two-root style valuation arguments generalize:
root valuations are 1/3 (×3) and 1/2 (×2) — any degree-1 factor forces an integral root valuation
1/3·? — a probe deriving False from a mutated all-unramified σ should be cheap via "f has no
ℚ_p-root": root valuation would be 1/2 or 1/3 ∉ ℤ). Fresh guardian audit gates the push.

## §3. Risks
- ShapeCell field availability for the tree/δ encoding (check the actual structure fields first;
  if δ can't serve as a tag, use face-order or a dS-offset encoding — report).
- The stratumCount1 (NodeConfig) ↔ ClusterShape-keyed model bridge: keep it definitional in
  stratumCount4 via the decode.
- `classify1` totality/box-partition interplay: the model's undecidedCount is the box remainder;
  disjointness (§2-4) is what keeps it nonnegative — no classify1-vs-B.classify global coherence
  is needed (both fiber families are just subsets of the box).
- Flat sides (e=1 mixing) deliberately out of scope; do not let the enumerator emit them.
