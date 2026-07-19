# Full formalization audit — findings (2026-07-12, 26-agent adversarial workflow + independent re-verification)

**VERDICT: `provesWhatItClaims = False`.** The formalization does NOT currently prove the headline
("p-adic factorization density = the OM engine's uniform rational function for ALL primes incl. wild
p≤n"). It proves a CONDITIONAL/PLACEHOLDER version. The trusted base is clean and much of the
machinery is genuine, but the real-instance capstone is VACUOUS. All findings below survived
adversarial verification and I re-confirmed the load-bearing ones by hand.

## What is SOLID (verified, EXIT=0)
- **Trusted base is exactly the 7 declared axioms**, nothing snuck in (grep + #print axioms). Other
  `axiom` grep hits are docstring tombstones of deleted axioms.
- **Past inconsistency genuinely repaired**: the free-pivot `AX_cellRecursion`, free-F
  `tame_functionalEquation`, free `AX_columnMeasure`, and the `x^n+p^N`-refuted classifier axiom are
  all deleted; current forms are pinned to fixed objects and pass the free-parameter falsifiability
  test. `clusterMeasureModel`/`_rec` is a genuine relative-consistency witness (core + descend_size_lt
  + omCells, independent of clusterMeasure/AX_cellRecursion).
- **Rationality is DERIVED, not assumed**: `OMInduction.clusterVol_isRational` is a real, sorry-free,
  Lean-core-only well-founded induction. The non-decorative heart.
- **Genuine non-vacuous, core-only pieces**: `Order0Alpha.montes_order0_unconditional` (over
  `sepShapesOf`, non-empty cells, real fiber count), `ClassifierBridgeFiber2.montes_order1_selfloop_density`
  (real gates 1/4, 1/9, 1/3, 2/3), the count keystone `ShapeCountTie.*`, the general-μ fixpoint
  `SelfLoopFixpointGeneralMu.*`. These are real.

## The CRITICAL gaps (why the headline is not proved)
1. **Real-instance capstone `montes_unconditional` is VACUOUS.** `decode := leafOMTypeOfSize (treeSize T)`
   has `Rr := 0` ⟹ `M5.cells = []` ⟹ `clusterCount = (empty sum)/pivot = 0`. Certified density is
   IDENTICALLY 0, σ-independent (machine-proved `tame_lhs_zero`, EXIT=0). Misnamed "unconditional": it
   binds h_node/h_decided_mono/h_env, which its own docstring admits are "each currently FALSE for the
   degenerate order-0 instance." It certifies only "constant-0 is palindromic-rational." (RealInstance.lean)
2. **`realP := 2` — a FIXED CONSTANT.** Every top-level theorem's real-count clause is evaluated ONLY
   at p=2, NOT "for all primes." "All primes incl. wild p≤n" is not stated for the real polynomial count.
3. **σ is DECOUPLED.** `montes_allorders_of_hnode` and `ConditionalDensity.density_eq_engine_conditional`
   bind `σ : FactorizationType` but NEVER use it — the menu `M` is arbitrary, not σ-determined.
4. **`realDensity_tame_functionalEquation` is TRUE-but-VACUOUS** (about the constant-0 tree-sum); its
   §5 Del Corso–Dvornicich cite over-claims for the current prototype.
5. **Menu mismatch**: two disjoint shape families coexist. `sepShape`/`Tselfloop` carry genuine
   non-zero payload (order-0/order-1 gates) but are NEVER wired into the real capstone, which uses the
   EMPTY-cell `M5.shapeOf(leafOMTypeOfSize s)` (Rr=0 → count 0).
6. **Measure wall un-crossed**: no theorem identifies any `F.density` / counting density with the
   genuine p-adic Haar density ρ — surfaced honestly as hypothesis `hbridge` (mathlib has no p-adic
   Haar measure on any DVR). `realF.density` is literally the zero tree-sum.
7. **Witness capstones** (`montes_full_instance`, etc.) are non-vacuity witnesses over a TRIVIAL
   degree-0 model (q=2, n=0, density ≡ 1), not statements about the real density.

## Minor / hygiene
- **Dead axioms on the goal path**: `descend` (no consumer, in no footprint) and
  `omReadValuation_lt_of_certLevel_fkeyed` (only consumed by `oneDigitCylinder_fkeyed`, which itself
  carries a contained `sorryAx` reaching no capstone). Advertise trusted base as 5, not 7, or label
  these as forward-declarations.
- `oneDigitCylinder_fkeyed` carries `sorryAx` (contained; no capstone reached).
- `Decomposition.wiring_assessment : True := trivial` — a literally-vacuous placeholder "theorem."
- Rename `montes_unconditional` → `montes_order0_prototype`; treat the tame axiom as placeholder, not
  an imported §5 theorem, in any external claim.

## De-vacuification path (the real work, per notes/VACUITY_SIGMA_BLUEPRINT.md)
(1) repair `decode`/leaf cells so `M5.cells ≠ []` (wire sepShape/Tselfloop genuine payload into the
real menu); (2) generalize `realP` from 2 to all primes; (3) make the menu σ-determined; (4) then the
self-loop h_node (the Denef/×q measure content, per SELFLOOP_GENERALK_WALL.md); (5) cross the measure
wall (needs p-adic Haar in mathlib, or keep as recorded hypothesis).

## Correction to this session's narrative (candor)
My earlier reports over-claimed: "tame is done / unconditional" and the "#49 conditional milestone"
and "we're basically done modulo Denef" were too strong. The genuine order-0/order-1 pieces ARE
proven core-only, but the REAL-INSTANCE capstone tying them to actual polynomial densities (all
primes, type σ, non-vacuous) is a degenerate placeholder. The self-loop threads were locally honest
about their sub-problem; the global "we're close" was my over-extrapolation. The audit is the corrective.

## CLARIFICATION (2026-07-12, root-cause probe): the vacuity is MENU WIRING, not the root residual
The blueprint §1.1-1.2 (rootResidual zeroes the generic residual) describes a PRE-5f1addb state.
At 5f1addb the fix is ALREADY LANDED: `M5.OMType.hDrLtCs` → `hDrLeCs : dr ≤ cs` (OMType.lean:129,
strictness moved to descent children `OMCell.Child.hChildSizeLt`); `Classifier.rootResidual` guard
weakened `< n` → `≤ n` (Classifier.lean:180) so it NEVER fires on a genuine residual. Machine-checked
core-only: `Order0.rootResidual_eq_reduction` (root residual = mod-p reduction, monic degree n) and a
scratch check that `M5.cells (fRootCtx f) ≠ []` on the generic stratum. So the ACTUAL classify path is
NON-vacuous; `Order0.montes_order0_unconditional` over `sepShapesOf` is the genuine non-vacuous capstone
(1/4 gate proven, and `montes_order0_certified_value_pos` certifies strictly positive).
THE remaining vacuity: the ALL-ORDERS `M9.montes_unconditional` (RealInstance.lean:982) uses
`shapeMenu n = (leafTypesUpTo n).map M5.shapeOf` built from `leafOMTypeOfSize s` (hardcoded `Rr:=0` →
empty cells → density ≡ 0), which BYPASSES `classify`/`fRootCtx`. Precise next fix = swap that menu for
the σ-keyed `sepShapesOf`/`sepShape` family + generalize `realP` from 2 + σ-determined menu (a larger
RealInstance/CountingModel surgery). NOT the root residual, NOT decode-of-classify.

## TAME DRAINAGE INVESTIGATION (2026-07-13, workflow wacclrs54) — decisive
Question: is TameMenuExhaustive (off-menu fraction →0 at p>n) provable for the current classifier?
ANSWER: NO — and the split is the result.
- MATH DRAINS (confirmed): the density engine is EXHAUSTIVE — Σ over all degree-n types = EXACTLY 1
  (symbolic + exact-rational at every tame prime tested, om_density_engine.py). And the FULL OM
  recursion drains tamely at FINITE depth: recentered self-loop survivors [81,6,3,0], [729,54,27,0],
  tame [15625,0] → 0 (rate ~1/p per level). So tame drainage is TRUE mathematically (matches the
  no-wild-self-loop arithmetic at p>n: p|e, e≤n ⟹ p≤n, impossible).
- CURRENT LEAN CLASSIFIER DOES NOT DRAIN (definitional, not a subtle gap): classifyAux is f-BLIND
  below the root — it recurses via childCtxOfSize (Classifier.lean:263-267) built with Rr:=0, so every
  child instantly bottoms out as a childless stub (M5.cells of Rr=0 = []); classifyAux_indep
  (Classifier.lean:582-590, by rfl) certifies the output depends only on (n,budget,size), NOT on f.
  TameMenuExhaustive is over rawCount = classifyAux fibers (ClassifierBridge.lean:150), so it is
  definitionally non-draining (off-menu plateau 0.89-0.96, self-loop fraction level-INDEPENDENT:
  p=3,n=2→0.0082 at N=3,4; p=5,n=2→0.00128). Proving it would contradict banked classifyAux_indep +
  tendsto_undecidedDensity. It is a WRONG TARGET for the current classifier, correctly flagged as the
  one open hypothesis.
- FIX (dedicated project, deep surgery): de-stub childCtxOfSize so classifyAux re-derives child
  residuals from f below the root (the R2/Phase-B obligation, Classifier.lean:1290-1292). This BREAKS
  classifyAux_indep and the CERTLEVEL Layer D-E cylinder — both must be re-proven with genuine
  (N,f)-dependence. Needed new lemmas: tame_depth_bound (bounded descent at p>n), menu_completeness
  (de-stubbed output shapes ⊆ tameMenu), selfloop_recenter_contraction (drains ~1/p per level).
  REUSE: M5.OMCell.Child.hChildSizeLt (strict descent), tendsto_tailDensity_zero. ALT: W6 order-tower
  Σ_k p^{−k(w+1)} resummation (larger scope).
- MATH-COMPARISON UPSHOT: the paper's §9/L5fix tame termination (finite depth B(n,p)) is CORRECT and
  the drainage is real; the formalization's gap is that the CLASSIFIER is a stub that truncates the
  descent structurally instead of genuinely descending. The detail to spell out outside Lean is minor
  here (the math is right); the work is Lean-side (de-stub).
