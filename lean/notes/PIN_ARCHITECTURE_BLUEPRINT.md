# PIN_ARCHITECTURE_BLUEPRINT — Phase-B pinned interface over the ENGINE-VALIDATED objects

**Status: 2026-07-03, BLUEPRINT ONLY (lane 4; no Lean written).** Synthesis of the pin-field /
enforcement-audit ideas of `MONTES_ARCHITECTURE_REDESIGN.md` §3/§7 (a stopped session's design —
the *architecture* was right, its *execution* was wrong twice over) with the CURRENT tree state
(`VACUITY_SIGMA_BLUEPRINT.md` §2.5–2.7, `HNODE0_BLUEPRINT.md` §5, the live `Order0*` modules,
`lean_urat/quarantine/README.md`). Every cited signature verified against the live tree
2026-07-03 (file:line index in §6). Assumes the in-flight main build (`D_asving_final3`) confirms
`montes_order0_unconditional` core-only per `AxChk_baseline.lean:22`.

**The design constraint to internalize (the A11/omDensity lesson): CONCRETENESS ≠ TRUTH.**
The stopped session correctly removed all free binders — and still produced (i) a density object
built on the REFUTED `clusterCount` per-node aggregation (`clusterCount(sepShape (2)) = 4/3` at
`q = 2` vs the true stratum density `1/4`, and `4/3` for the provably-EMPTY `p = 2` split stratum),
and (ii) an ARITHMETICALLY FALSE concrete axiom (`omDensity_tame_functionalEquation`: from its own
definitions `omDensity(n=2) = q(q+2)/(q+1)`, and `R(1/q) ≠ R(q)` — at `q = 2`, `8/3 ≠ 5/6`; the
axiom asserted `IsPalindromic`, making the base inconsistent). Pinning kills F1
(falsification-by-instantiation); ONLY a numeric gate on the concrete object kills F2′ (a concrete
axiom that is simply false). Both gates are mandatory below; neither substitutes for the other.

**The engine-validated concrete object is `Order0.rootCount`** (`LeanUrat/OM/Order0.lean:121`) and
its Phase-B extension `omCount` (§1.2) — NOT `clusterCount` (`LeanUrat/MontesAxiom.lean:311`),
whose per-node semantics are refuted for multi-cell nodes (§2.6 D1–D6). Every pin below points at
the rootCount family.

---

## §0 — Current tree state (what the pins attach to)

Live, sorry-free, expected core-only (the Phase-A bank):

* `Order0.rootCount` (`OM/Order0.lean:121`) — the CORRECTED root-node coefficient:
  `nodeChoicePolyQ(cells T).eval q · (q^nodeVolumeExp(cells T))⁻¹ · ∏_cells ∏_children clusterCount …`
  — choice count (`OM/Order0.lean:102 nodeChoicePolyQ`, `:91 nodeChoicePoly`, `:74 availPoly`,
  `:67 necklacePoly`, `:79 ffPoly`) × per-configuration volume `q^{−B}` (`:110 nodeVolumeExp`,
  `B = newtonExponent(polygon) + Σ dS`), NO pivot at the root (D4). Children still on the OLD
  cluster recursion — dead for childless Phase-A shapes, the Phase-B obligation (§1.2).
* `Order0.sepShape` / `sepShapesOf` / `unramType` (`OM/Order0Capstone.lean:74/:84/:79`) — the
  σ-KEYED order-0 separable menu (direct `ClusterShape` literals over `Nat.Partition n`).
* `montes_order0` (`OM/Order0Capstone.lean:146`, conditional) and
  **`montes_order0_unconditional` (`OM/Order0Alpha.lean:450`)** — `h_node0` DISCHARGED
  (`h_node0_proved`, `OM/Order0Alpha.lean:413`) via the fiber characterization
  `classify_eq_sepShape_iff` (`OM/Order0Alpha.lean:64`; forward `OM/Order0Fiber.lean:148`, backward
  `OM/Order0Classify.lean:224`), the reduction-fiber count (`card_red_fiber`
  `OM/Order0Alpha.lean:164`, `card_classify_fiber :216`, `stratumCount_sepShape :254`), and the
  eval identity (`rootCount_sepShape_eval` `OM/Order0Alpha.lean:385`). This capstone takes NO
  structure parameter at all — it is the model for Phase B (§1.4, option P0).
* Counting substrate: `M8.stratumCount` (`OM/LevelNCount.lean:55`), `M8.shapeFiberCount`
  (same file, directly below), `M9.rawCount` (`OM/RealInstance.lean:143`), `M9.realP = 2`
  (`OM/RealInstance.lean:128`), `B.classify` (`OM/Classifier.lean:487`, D7-fixed `boxCoeffData`),
  `M7.cellsOfShapeWF` (`OM/CellPartition.lean:150`) with `cellsOfShapeWF_descend` (`:157`),
  `M6.treeSize` (`OM/Termination.lean:51`).
* Count identities: `Order0Count.sepStratum/avail/card_sepStratum`
  (`OM/Order0Count.lean:183/:113/:377`), `necklaceQ_eq_card` (`OM/Order0Count.lean:58`);
  necklace integrality/nonnegativity at ALL naturals: `Necklace.necklaceSum` (`OM/Necklace.lean:49`),
  `necklaceSum_nonneg` (`:69`), `dvd_necklaceSum` (`:221`), `necklaceQ`/`necklaceQ_eq_natCast`
  (`:256/:266`).

Legacy path (to be retired, §3): `clusterCount`/`countCellCoeff`/`countPivot`
(`MontesAxiom.lean:311/:119/:126`), `MontesData` (`MontesAxiom.lean:386`, with `boxMeasure :415`,
`boxHaarEquidist :432`, `nodeMeasure_boxSum :446`, `MontesData.C :517`, `nodeMultiplicativity :542`),
`CountingModel` (`CountingModel.lean:95`), `DensityFoundation` (`Interface.lean:231`), `OMBridge`
(`Interface.lean:285`), the M9 real instance (`realM/realD/realF` `OM/RealInstance.lean:514/:681/:773`,
`decode :105`, `shapeMenu :161`, `shapesOf :192`), the capstone `montes_unconditional`
(`OM/RealInstance.lean:942`), and the ONE non-core axiom on its footprint,
`realDensity_tame_functionalEquation` (`OM/RealInstance.lean:485`).

Quarantined (`lean_urat/quarantine/omDensity_tail_2026-07-03.lean.txt`, README in that dir): the
stopped session's `omDensity`/`omFoundation`/`omDensity_tame_functionalEquation`/`montes_via_omDensity`
tail. Never built; the false axiom never entered an olean. ⚠ `LeanUrat/AxProbe.lean` still
`#print axioms` the quarantined names (`AxProbe.lean:8–14`) — STALE, will not compile if built;
rewrite or delete it in Phase-B step R1 (§3). `AxChk_baseline.lean` is the current harness.

---

## §1 — (a) The concrete layer and the pin fields

### 1.1 Layered design (three layers, strict downward dependency)

* **Layer C (concrete definitions)** — `omCount`, `omMultiplicity`, `omVolume`, `omMenu`,
  `omDensityV2` (§1.2–1.3). Plain `def`s; no structure, no axiom. Everything is stated about these.
* **Layer S (statements)** — capstones and cites take NO structure binders; they mention Layer-C
  names literally (the `montes_order0_unconditional` model: its statement contains
  `rootCount M7.cellsOfShapeWF M6.treeSize M7.cellsOfShapeWF_descend` and
  `M8.stratumCount (M9.rawCount n)` verbatim, `OM/Order0Alpha.lean:450–461`).
* **Layer E (engines)** — `CountingModel`/`MontesData`-style structures survive ONLY as proof
  engines (the squeeze/decomposition machinery `Decomposition.countingDensity_eq_sum_coeff`
  (`Decomposition.lean:104`), `countingDensity_isRational` (`:185`) is genuinely generic and worth
  reusing). Rule: a structure may be *hypothesized* in a theorem (sound — theorems over free
  structures are conditional, not asserted) but NEVER quantified in an `axiom`; and every
  *exhibited instance* must be the pinned one.

### 1.2 The corrected §2.6 per-node semantics as Layer C (the Phase-B recursion)

The engine-validated per-node form (`VACUITY_SIGMA_BLUEPRINT.md` §2.6 boxed formula; exact against
`om_density_engine.py` on all 14 order-0 strata + the non-generic slope-−1/2 stratum + the
non-flat `n = 4` face):

```
lim_N stratumCount T N / q^{nN}
  = ( Σ_{c ∈ configs T}  m_cell(c,q) · q^{−B(c)} · ∏_{ch ∈ c.children} omChildCount ch.shape (q^{ch.δ · ch.D}) )
    / countPivot*(T, q)

m_cell(c,q) = ∏_{F ∈ c.faces} N_{S_F}(q^{δ_F})      (falling-factorial choice counts; avail_1 = Q−1
                                                     on a genuine face; avail_D = necklace M_D(Q), D ≥ 2)
B(c)        = newtonExponent(c.polygon) + Σ_F d_F   (pure lattice exponent; NO (1−q⁻¹)^V factor)
countPivot* = countPivot (treeSize T) at descent-conditioned CLUSTER nodes (s ≥ 2); = 1 at the ROOT.
```

⚠ **R0 ERRATA (2026-07-04, gate 69/69 PASS with these corrections — they are BINDING on R1/W2;
full tables /workspace-vast/asving/tmp/phaseb_r0/results.txt, semantics in harness.py docstring):**
* **E1 — B at CLUSTER nodes:** `B = newtonExponent + Σ_F d_F − s` (s = the node's cluster size).
  The boxed `B` above is the ROOT-node form only; without the `−s` the parent's per-digit charge
  is double-counted against the child block.
* **E2 — the rescale face is UNPUNCTURED:** the all-descend (rescale) face of a cluster node has
  `avail₁ = Q`, not Q−1 (a third case beyond the boxed dichotomy; with Q−1 the split count is
  `(q−1)(q−2) = 0` at q = 2, refuted by the gate's Case 2).
* **E3 — cluster config census:** cluster-node configs = strict polygons with rightmost slope
  `< 1`, PLUS one-step rescale configs (`B = s(s+1)/2`); slope-≥1 polygons appear ONLY inside the
  self-loop resummed by `countPivot(s) = 1 − q^{−(s(s+1)/2−1)}` (enumerating them as configs
  double-counts: 16/21 ≠ 2/3 at q = 2).
* Pinned conventions: `d_F` = the FULL face residual degree (μ ≥ 2 factors included); the pivot
  argument is the node's OWN subtree size, evaluated at the node's base-changed Q.
* Discriminating check: pivot at ROOT (the old D4-refuted placement) mismatches everywhere
  (e.g. 4/9 vs 1/3; 128/2555 vs 1/20); cluster-only placement matches all 69 cases.

Lean shape (two functions, mirroring the engine's root/cluster split — this is how D4 "pivot at
cluster nodes only" is carried without a node flag):

```lean
-- the V2 per-node configuration datum (D3: ONE entry per (polygon × full residual-shape
-- assignment); the current one-CountCell-per-factor payload is the order-0 single-face special
-- case and stays untouched):
structure FaceAssign where
  δ : ℕ                          -- residue-extension degree of this face
  shape : List (ℕ × ℕ)           -- the (D, μ) residual-shape multiset on this face
  dF : ℕ                         -- the face's residual digit count d_F (§2.6: B = newtonExponent + Σ_F d_F;
                                 -- order-0 flat face: d_F = Σ dS = n — TRANSCRIBE from the engine at R0,
                                 -- do not re-derive by hand; D6 warns the M6_lemma normalization is inconsistent)
structure ChildData where
  shape : ClusterShape           -- the descent child (paired to a μ ≥ 2 factor)
  δ : ℕ                          -- parent face δ_F
  D : ℕ                          -- degree of the paired factor  (base change q ↦ q^{δ·D}, §2.6 last bullet)
structure NodeConfig where
  polygon : L4.LatticePolygon
  faces : List FaceAssign
  children : List ChildData

noncomputable def configsOf : ClusterShape → List NodeConfig := …   -- V2 payload reader (additive;
                                                                    -- CountCell (MontesAxiom.lean:100) untouched)

noncomputable def omChildCount (T : ClusterShape) (q : ℕ) : ℚ :=    -- CLUSTER node: pivot applies
  (((configsOf T).map (fun c => mCell c q * ((q:ℚ) ^ volExp c)⁻¹
      * (c.children.map (fun ch => omChildCount ch.shape (q ^ (ch.δ * ch.D)))).prod)).sum)
    / countPivot (M6.treeSize T) q
termination_by …                                                    -- descent via the V2 cells_descend

noncomputable def omCount (T : ClusterShape) (q : ℕ) : ℚ :=         -- ROOT node: NO pivot (D4)
  ((configsOf T).map (fun c => mCell c q * ((q:ℚ) ^ volExp c)⁻¹
      * (c.children.map (fun ch => omChildCount ch.shape (q ^ (ch.δ * ch.D)))).prod)).sum
```

with `mCell c q = ∏_{F ∈ c.faces} (choicePoly F.shape).eval ((q:ℚ) ^ F.δ)` (choicePoly = the
`ffPoly (availPoly D) k_D / k_D!` product, exactly `nodeChoicePoly` `OM/Order0.lean:91` generalized
per-face) and `volExp c = L4.newtonExponent c.polygon + Σ_F d_F` (generalizing `nodeVolumeExp`
`OM/Order0.lean:110`).

Design notes (each a §2.6 defect, now structural):
* **D1** — per-face fine counts `N_{S_F}` via necklace pools, never `(q^δ)^{dS−1}`. `countCellCoeff`
  (`MontesAxiom.lean:119`) does not appear anywhere in Layer C.
* **D2** — volume is the pure `q^{−B}`; `bb1Value` (`L4.lean:79`) does not appear (its `(1−q⁻¹)^V`
  factor belongs to the integrated form, not the counted form).
* **D3** — SUM over configurations, PRODUCT over faces within one configuration. The current
  order-0 payload (one `CountCell` per factor) encodes ONE configuration; the compatibility lemma
  is `omCount_sepShape_eq_rootCount : omCount (sepShape n lam) q = rootCount M7.cellsOfShapeWF
  M6.treeSize M7.cellsOfShapeWF_descend (sepShape n lam) q` — REQUIRED, so every Phase-A theorem
  (in particular `h_node0_proved`) transfers by rewriting, not re-proving.
* **D4** — pivot only in `omChildCount`. The pivot VALUE is unchanged
  (`countPivot` `MontesAxiom.lean:126`, `L5fix.selfLoopExponent` `L5fix.lean:38`).
* **Base change** — children at `q^{δ·D}`. Rationality engine addition:
  `isRationalFn_compQpow (k : ℕ) : IsRationalFn f → IsRationalFn (fun q => f (q ^ k))`
  (num/den ↦ `num.comp (X^k)`/`den.comp (X^k)`; the RatFn closure family
  `isRationalFn_polyEval`/`isRationalFn_invQpow` `OM/Order0.lean:132/:136` is the pattern).
  ⚠ SUBTLETY: `f : ℕ → ℚ` composed with `q ↦ q^k` is fine, but `omChildCount ch` is consumed at
  the CHILD's residue cardinality — the "uniform rational in q" claim must be in the ROOT `q`;
  state rationality of `fun q => omCount T q` directly by the recursion (each recursive call is a
  rational function of `q` via comp), NOT by composing after the fact.
* **The menu** — `omMenu n σ : Finset ClusterShape`, the genuine σ-keyed decided-shape menu:
  order-0 slice = `sepShapesOf n σ` (`OM/Order0Capstone.lean:84`); Phase-B extension adds the
  deeper-order shapes with `typeOf T = σ` where `typeOf` reads the `(e, f)` data off the payload
  (the sound per-node law is the `GMNNodeEfLaw` predicate shape, `OM/LevelNCount.lean:997` —
  consumed as a structural property of classifier-emitted shapes, NEVER re-axiomatized over a free
  `D : M5.OMType`, which is the refuted `gmn_node_ef_law` U4 lesson).
* **The density** — `omDensityV2 n σ q := ∑ T ∈ omMenu n σ, omCount T q`. σ enters through the
  menu — the quarantined tail's `_σ` discard (O1 reintroduction) is structurally impossible here
  only if the σ-separation gate (§2, gate 6) is run; keep it mandatory.

### 1.3 The m_T × C_T split (signed-off explicit-multiplicity form)

For the `DensityFoundation.multiplicity` pin (Interface.lean:244 expects `Polynomial ℚ`):

```lean
noncomputable def omMultiplicity (T : ClusterShape) : Polynomial ℚ :=
  -- ∏ over the tree's nodes of the per-node choice polynomial, each comp'd with X^{δ·D-chain}:
  …   -- order-0 value: nodeChoicePolyQ (M7.cellsOfShapeWF T)  (= m_λ up to the avail₁ puncture)
noncomputable def omVolume (T : ClusterShape) (q : ℕ) : ℚ :=
  …   -- ∏ over nodes of q^{−B} / cluster pivots  (order-0 value: (q^n)⁻¹, by nodeVolumeExp_sepShape
      --  OM/Order0Alpha.lean:297 + no pivot at the root)
theorem omCount_eq_mul :
  ∀ T ∈ omMenu n σ, ∀ q, 1 < q → omCount T q = (omMultiplicity T).eval (q:ℚ) * omVolume T q
```

⚠ The split is exact only on shapes where each node carries ONE configuration (menu shapes; the
sum-over-configs and product-over-nodes do not commute in general). Stating `omCount_eq_mul` on
`omMenu` membership (not ∀ shapes) is the honest scope. If this proves awkward in Lean, the
fallback is the folded form (`multiplicity := 1`, coefficient = `omCount`) — but the signed-off A6
decision prefers explicit `m_T`; revisit only with Asvin.

### 1.4 The pins (exact field statements)

**P0 (preferred, the Phase-A precedent): no structure at all.** The Phase-B capstone is stated like
`montes_order0_unconditional` — Layer-C names verbatim, zero structure binders. Use P1–P3 only
where a Layer-E engine is genuinely reused.

**P1 — `MontesDataV2` (replaces `MontesData`, `MontesAxiom.lean:386`).** The V2 drops
`boxMeasure`/`boxHaarEquidist`/`nodeMeasure_boxSum` (their per-box target `countCellCoeff` is the
D1/D2-refuted value — a pinned instance could never satisfy them truthfully) and pins every
content field:

```lean
structure MontesDataV2 (n : ℕ) where
  shapesOf : FactorizationType → Finset ClusterShape
  shapesOf_pin : ∀ σ, shapesOf σ = omMenu n σ
  treeSize : ClusterShape → ℕ
  treeSize_pin : treeSize = M6.treeSize
  cells : ClusterShape → List NodeConfig
  cells_pin : cells = configsOf
  stratumCount : ClusterShape → ℕ → ℚ
  stratumCount_pin : stratumCount = M8.stratumCount (M9.rawCount n)
  -- the ONE analytic clause, stated about the CONCRETE corrected object (h_node-v2 target;
  -- discharge = the Phase-B analogue of h_node0_proved, per HNODE_GENUINE_FIX / HNODE0 §5 α):
  node_limit : ∀ σ, ∀ T ∈ omMenu n σ,
    Filter.Tendsto (fun N => M8.stratumCount (M9.rawCount n) T N / (M9.realP : ℚ) ^ (n * N))
      Filter.atTop (nhds (omCount T M9.realP))
```

With the pins, `cells := []` / `stratumCount := 0` / a junk menu are *not instances* (the pin
equation fails) — the redesign-§3 property. `partition`/`finiteTermination` analogues become
THEOREMS about the pinned fields (partition = `M8.shapeFiberCount` disjoint-fiber counting;
termination = the menu literal's `treeSize ≤ n`, as in `sepShape`'s root slot), not fields.

**P2 — `PinnedCountingModel` (wraps `CountingModel`, `CountingModel.lean:95`).** Keep the generic
`CountingModel` engine untouched (its squeeze machinery is proved and axiom-free); pin at the
instance boundary:

```lean
structure PinnedCountingModel (n : ℕ) extends CountingModel M9.realP n where
  decidedCount_pin : ∀ σ N,
    decidedCount σ N = ∑ T ∈ omMenu n σ, M8.stratumCount (M9.rawCount n) T N
  undecidedCount_pin : ∀ N,
    undecidedCount N = (M9.realP : ℚ) ^ (n * N) − ∑ σ ∈ typeMenu, decidedCount σ N
  typeMenu_pin : typeMenu = degreeTypeMenu n        -- the genuine degree-n type menu (new def;
                                                    -- NOT the {σ₀} re-pinning of realM — the O1 bug)
```

The three `realM` hypotheses map as: `decided_tendsto` ⟸ `node_limit` (finite sum of per-shape
limits); `decided_mono` ⟸ Phase-B cylinder monotonicity (order-0 slice: constant for `N ≥ 1`,
already the `stratumCount_sepShape` content); `box_partition` ⟸ `undecidedCount_pin` by
`add_sub_cancel` — same seam as `realM` (`OM/RealInstance.lean:514`), now over the genuine
multi-σ `typeMenu` instead of `{σ₀}`.

**P3 — `PinnedFoundation` (wraps `DensityFoundation`, `Interface.lean:231`).** Needed only for the
L7 palindromy-transfer plumbing (`TameFunctionalEquation` `Interface.lean:392` is `F`-indexed;
`goal_theorem_montes` `Goal.lean:160` consumes it):

```lean
structure PinnedFoundation (n : ℕ) extends DensityFoundation where
  density_pin : ∀ σ (q' : ℕ), 1 < q' → density n σ q' = omDensityV2 n σ q'
  shapes_pin : ∀ σ, shapes n σ = omMenu n σ
  clusterVolume_pin : ∀ T (q' : ℕ), 1 < q' → clusterVolume T q' = omVolume T q'
  multiplicity_pin : ∀ σ, ∀ T ∈ omMenu n σ, multiplicity T = omMultiplicity T
```

(`decomposition` `Interface.lean:251` then holds by `omCount_eq_mul`; `density_nonneg` by
necklace nonnegativity — `necklaceSum_nonneg` `OM/Necklace.lean:69` + `ffPoly` eval ≥ 0 on the
integer pools, the `Necklace` module's raison d'être.) Alternatively skip P3 entirely and state
the tame cite + transfer directly about `omDensityV2` (P0) — preferred; P3 exists only if reusing
`goal_theorem_montes` verbatim is cheaper than restating its 30-line proof.

**Witness discipline:** `Witness.DensityFoundation_nonempty` (`Witness.lean:116`) and the bundle
(`trivF` `:284`, `trivF_tame` `:330`, `montes_full_instance`) keep their role as *engine*
non-vacuity checks, but the PINNED structures' non-emptiness witnesses must be the genuine
instances (constructible only because the pins are satisfiable — that construction IS the
non-vacuity proof, redesign-§3's "enforced at instance-construction time").

---

## §2 — (b) The enforcement audit checklist (adapted to this tree)

Run after every Phase-B wave; all seven gates. Gates 1–2 are the redesign's; 3 is the NEW
A11/omDensity gate; 4–7 are tree-specific.

1. **grep-no-free-axioms.** `grep -rnE "^ *axiom " LeanUrat/ --include="*.lean"` — current
   inventory (2026-07-03): `PadicMeasure.{omCells:268, descend:272, descend_size_lt:278,
   clusterMeasure:405, AX_cellRecursion:438}`, `BB3inf.{descend:90, descend_size_lt:95,
   AX_GMN_IV_terminates:101}`, `Classifier.omReadValuation_lt_of_certLevel_fkeyed:634`,
   `LevelNCount.{L2_reconstruct:252, selfLoop_childFiber_corrected:1136,
   boxVolumeScale_collapse:1257}`, `OM/CountingModel.selfLoop_childFiber_fkeyed:520`,
   `RealInstance.realDensity_tame_functionalEquation:485`. For each: no binder of type
   `DensityFoundation`/`CountingModel`/`MontesData`/free `cells`/`classify`/`treeSize`/free
   `M5.OMType`. Every retirement step (§3) must strictly shrink this list.
2. **False-witness attempts (F1).** For every surviving axiom, attempt an `example : False` in the
   `AxFalse.lean` style. A SUCCESSFUL probe = the axiom is inconsistent → delete immediately.
   ⚠ NOTE the current tree already contains a COMPILING `example : False` from `L2_reconstruct`
   (`AxFalse.lean`, via `cells := fun _ => []`, `Fin 0` selector) — i.e. any environment importing
   `LevelNCount` is inconsistent-in-principle. This makes the §3 step R2 deletion a PRIORITY, not
   housekeeping. Failed probes get recorded (statement + why it fails) in the axiom's docstring.
3. **ARITHMETIC truth gate on every concrete axiom (F2′ — the new lesson).** BEFORE a concrete
   axiom lands in any `.lean` file: (i) transcribe its statement into an exact-arithmetic Python
   harness (sympy/Fraction — the §2.6/§2.7 gate pattern; artifacts under
   `/workspace-vast/asving/tmp/` + a note in this repo); (ii) evaluate BOTH sides at small cases —
   minimum `n ∈ {1, 2, 3}`, `q ∈ {2, 3, 5}`, and for functional-equation claims the symbolic
   `R(1/q) = R(q)` check; (iii) where feasible, brute-force the ground truth over `ZMod (p^N)`,
   `N ≤ 3` (the D7-gate pattern, `HNODE0_BLUEPRINT.md` §0); (iv) record the gate artifact path in
   the axiom's docstring. The quarantined axiom fails this gate in seconds (`8/3 ≠ 5/6` at
   `n = 2, q = 2`). NO exceptions for "obviously true" cites — the stopped session thought so too.
4. **Footprint harness.** `AxChk_baseline.lean` is the source of truth; `#print axioms` targets:
   `montes_order0_unconditional` MUST stay `[propext, Classical.choice, Quot.sound]`
   (`AxChk_baseline.lean:22`); each Phase-B capstone gets a ★-line with its EXPECTED footprint
   written next to it before the build runs. Repair or delete the stale `AxProbe.lean`
   (references quarantined names, `AxProbe.lean:8–14`) — a harness that cannot compile audits
   nothing.
5. **Non-degeneracy + honest-emptiness (F2).** Per new density object: a PROVED positivity witness
   at one small case (e.g. `omCount (sepShape 1 ⟨{1}⟩) 2 = 1/2 > 0` — evaluable by `norm_num`
   after `rootCount_sepShape_eval`-style unfolding), AND a proved correctly-EMPTY case
   (`rootCount (sepShape 2 (1,1)) 2 = 0` via `ff(q−1, 2) = 0` at `q = 2` — the SIGMA-1 scope
   honesty). Blanket "≠ 0 everywhere" is WRONG for punctured strata; gate per-stratum against the
   engine table, not against a slogan.
6. **σ-separation (O1).** Exhibit (as a Lean `example` or the numeric harness) two degree-`n`
   types with DIFFERENT certified values — order-0 witness at `n = 2, q = 3`: split
   `ff(2,2)/2!·q^{−2} = 1/9` vs inert `M_2(3)·q^{−2} = 1/3`. Any σ-discarding regression
   (the quarantined `_σ`) fails this gate mechanically.
7. **Falsifiability of new ∀-shape statements.** Every new statement quantifying over all
   `ClusterShape`/payloads gets the `cells := []`-style adversarial instantiation attempt
   (the `cellsOfShapeWF_descend`-vs-raw-payload lesson: ∀-shape claims true only on the reachable
   menu must carry the guard or the menu restriction).

---

## §3 — (c) The retirement plan (what replaces what, in what order, with gates)

Each step lands separately, with gates named; a step that cannot pass its gate does not land
(precise TODO + revert, no partial merge).

* **R0 — numeric re-gate of the Phase-B recursion (no Lean).** Extend the §2.6 reconciliation
  harness to cluster nodes: pivot placement, child base change `q^{δD}`, at least one genuine
  order-1 stratum (the slope-−1/2 family) and one two-level tree, exact vs `om_density_engine.py`.
  Gate: zero mismatches. *Replaces nothing yet; unblocks §1.2.*
* **R1 — Layer C lands (pure addition).** `NodeConfig`/`configsOf`/`omChildCount`/`omCount`/
  `omMenu`/`omDensityV2` + `omCount_sepShape_eq_rootCount` + `isRationalFn_compQpow` + the m×C
  split (§1.3). Fix/delete `AxProbe.lean` in the same wave. Gates: audit-§2 items 3 (transcription
  tables re-run against Lean values), 4 (Phase-A footprints unchanged), 5, 6, 7. *Nothing retired
  yet; `clusterCount` gets a deprecation docstring pointing at §2.6 D1–D6.*
* **R2 — delete the four FALSE free-cells axioms** — `L2_reconstruct`
  (`OM/LevelNCount.lean:252`), `selfLoop_childFiber_corrected` (`:1136`),
  `boxVolumeScale_collapse` (`:1257`), `selfLoop_childFiber_fkeyed`
  (`OM/CountingModel.lean:520`) — together with their `AxFalse.lean` probes (which then no longer
  compile — correct). They are consumed by nothing on any capstone footprint
  (`VACUITY_SIGMA_BLUEPRINT.md` §4) and one of them yields a compiled `False`. Their INTENDED
  content returns, if and when needed, only as `IsGenuineOM`-constrained restatements
  (HNODE_GENUINE_FIX design) each passing audit gates 2, 3, 7 first. Gate: grep inventory (§2.1)
  shrinks by four; full build green; AxChk unchanged.
* **R3 — `MontesDataV2`/`PinnedCountingModel` land; the Decomposition engine re-instantiated.**
  Re-point the generic squeeze/decomposition machinery (`Decomposition.lean:104/:185`; the
  `OMInduction.clusterVol_isRational` generic engine — the quarantined tail's
  `clusterCount_isRational` block, README-flagged salvageable, is the instantiation TEMPLATE, now
  run at `omCount`'s corrected recursion instead) onto the pinned V2 objects. `node_limit`'s
  order-0 slice discharges from `h_node0_proved` + `omCount_sepShape_eq_rootCount`; the deeper
  slice stays an explicit hypothesis until the Phase-B classifier work (h_env chain) matures.
  Gates: 1, 4, 7.
* **R4 — retire the M9 capstone.** Delete `montes_unconditional` (`OM/RealInstance.lean:942`),
  `realM`/`realD`/`realF` (`:514/:681/:773`), `decode`/`leafTypesUpTo`/`shapeMenu`/`shapesOf`
  (`:105/:156/:161/:192`) — the degenerate (`≡ 0`, σ-independent, three-false-hypotheses) path —
  AND, in the SAME commit, the axiom `realDensity_tame_functionalEquation`
  (`OM/RealInstance.lean:485`): it is currently trivially-true-about-a-degenerate-object; its
  statement is about the WRONG object (the `clusterCount` sum over the leaf menu) and must not
  survive into an era where anyone might cite it. Replacement: the Phase-B capstone chain
  (order-0: `montes_order0_unconditional`, already live; full: `montes_projective`, §4). Gate:
  grep inventory −1 axiom; `AxChk` rewritten (M9 lines removed, replacements ★'d); full build.
  ⚠ scope: `Goal.goal_theorem_montes`/`goal_theorem_via_montes` (`Goal.lean:160/:222`) are
  hypothesis-clean core-only GENERIC lemmas — keep (they cost nothing and P3 may consume them).
* **R5 — retire the measure route (redesign-§5 "better: retire").** `Goal.goal_theorem`
  (`Goal.lean:87`) + the `PadicMeasure` axiom cone (`clusterMeasure:405`, `AX_cellRecursion:438`,
  `omCells:268`, `descend:272`, `descend_size_lt:278`) + `BB3inf`'s parallel stubs (`:90/:95/:101`)
  + `OMBridge` (`Interface.lean:285`) move to `quarantine/` (documented, per the README pattern) —
  they are already off every count-native footprint. Gate: grep inventory shrinks to
  {`omReadValuation_lt_of_certLevel_fkeyed` (sound, constrained, Phase-B classifier input) +
  whatever concrete cite §4 has landed}; full build green.
* **R6 — retire `clusterCount` itself.** Only after `omChildCount` owns every consumer
  (`rootCount`'s children product is the last in-tree use — swap to `omChildCount` inside
  `rootCount` behind the `omCount_sepShape_eq_rootCount` equality, or retire `rootCount` into a
  lemma about `omCount`). `clusterCount`/`countCellCoeff`/`countPivot`-at-root semantics and the
  banked `C_rec`/`clusterCount_boxSum` suite (`MontesAxiom.lean:325/:360`) go to quarantine with
  the D1–D6 documentation. Gate: `grep -rn "clusterCount" LeanUrat --include="*.lean"` hits only
  quarantine + historical docstrings; AxChk full pass.

Standing rule for ALL steps: **never delete quarantine/** (it is the audit record), and the
`#print axioms` harness runs in the same build as the change (a retirement whose gate runs "later"
is a fake retirement).

---

## §4 — (d) Palindromy: stated ONLY at the full projective density

**The order-0/monic stratum is provably non-palindromic — palindromy must never be stated about
it.** Two exhibits, keep both in the eventual docstring:

* *The cautionary counterexample (the quarantined axiom):* the stopped session's
  `omDensity(n=2) = q(q+2)/(q+1)` (its own definitions: two menu shapes, `clusterCount` values
  `q²/(q+1)` and `2q/(q+1)`), and `R(1/q) = (1+2q)/(q(1+q)) ≠ R(q)` — at `q = 2`: `5/6 ≠ 8/3`.
  Asserting `IsPalindromic` (`Interface.lean:361`) for it was an INCONSISTENT axiom over a fully
  concrete object. (Doubly wrong: the value itself is the refuted aggregation — the correct
  `n = 2` order-0 separable density is `(q−1)²/q²`, per the gated `Σ_λ m̃_λ(q)·q^{−n}`.)
* *Even the CORRECT monic object is non-palindromic:* `(q−1)²/q²` has
  `R(1/q) = (1−q)² ≠ (q−1)²/q²`; the full monic separable density `1 − 1/q` has `R(1/q) = 1 − q`.
  Non-palindromy is not an artifact of the wrong recursion — the monic stratum genuinely lacks the
  functional equation (the projective symmetrization is what restores it). This is why
  `montes_order0` carries the explicit "NO palindromy clause" (`OM/Order0Capstone.lean:45–46`).

**Where palindromy eventually lives.** After Phase B (draining classifier ⟹ h_env-v2 true; full
menu; ramified types on-menu), define the CONCRETE projective density
`omProjDensity n σ q` (the monic `omDensityV2` assembled with the leading-coefficient/infinity
strata per the paper's `α/ρ` normalization — the projectivization is itself a Layer-C definition
with its own R0-style engine gate). THEN one concrete cite, the single genuinely-external input
(redesign-§6's "honest measure-wall boundary"):

```lean
axiom omProjDensity_tame_functionalEquation (n : ℕ) (σ : FactorizationType) (hσ : σ.degree = n) :
    ∃ (num den : Polynomial ℚ), den ≠ 0 ∧
      (∀ q' : ℕ, q'.Prime → n < q' →
        omProjDensity n σ q' = num.eval (q' : ℚ) / den.eval (q' : ℚ)) ∧
      IsPalindromic num den
```

Landing preconditions (all MANDATORY, audit-§2 order): gate 3 numeric run — `n ∈ {2, 3}`,
`q ∈ {2, 3, 5}` values against `padic_types.py` closed forms AND the symbolic `R(1/q) = R(q)`
check on the assembled rational function; gate 5 non-degeneracy + the honest-empty strata; gate 6
σ-separation; gate 2 False-witness attempt. The capstone `montes_projective` then =
PROVED rationality of `omProjDensity` (Layer-C engine) + PROVED value tie (V2 `node_limit` +
discharged h_env-v2) + palindromy transferred from the cite via the L7 identity-theorem plumbing
(`goal_theorem_montes` pattern, `Goal.lean:160`; `L7.tame_to_all_primes`/`isPalindromic_of_agree`).

Enforcement corollary: `grep -rn "IsPalindromic" LeanUrat --include="*.lean"` — the ONLY
axiom-level occurrence permitted in the end state is `omProjDensity_tame_functionalEquation`
(during transition, also the R4-doomed `realDensity_tame_functionalEquation`). Any palindromy
clause mentioning a monic/stratum/order-0 object is an automatic audit failure.

---

## §5 — Order of work

1. R0 (numeric re-gate; python only) → 2. R1 (Layer C + `AxProbe` repair) → 3. R2 (delete the
four false axioms — PRIORITY, see §2 gate 2) → 4. R3 (pinned structures + engine re-instantiation)
→ 5. Phase-B classifier work proper (h_env-v2 / draining; the long pole, human-supervised — agent
sweeps have fake-closed here twice) → 6. R4, R5 as their gates allow → 7. projectivization + §4
cite + `montes_projective` → 8. R6. The enforcement audit (§2, all seven gates) runs at every
numbered step.

## §6 — Verified signature index (live tree, 2026-07-03)

| name | file:line |
|---|---|
| `rootCount` | `LeanUrat/OM/Order0.lean:121` |
| `necklacePoly` / `availPoly` / `ffPoly` | `OM/Order0.lean:67/:74/:79` |
| `nodeChoicePoly` / `nodeChoicePolyQ` / `nodeDelta` / `nodeVolumeExp` | `OM/Order0.lean:91/:102/:98/:110` |
| `rootCount_isRational_of_leaf` | `OM/Order0.lean:148` |
| `flatSide` / `flatFace` / `sepShape` / `unramType` / `sepShapesOf` | `OM/Order0Capstone.lean:65/:68/:74/:79/:84` |
| `cellsOfShapeWF_sepShape` / `sepShape_leaf` / `isRationalFn_finsetSum` | `OM/Order0Capstone.lean:92/:108/:119` |
| `montes_order0` | `OM/Order0Capstone.lean:146` |
| `classify_eq_sepShape_iff` / `card_red_fiber` / `card_classify_fiber` | `OM/Order0Alpha.lean:64/:164/:216` |
| `stratumCount_sepShape` / `nodeVolumeExp_sepShape` / `nodeChoicePolyQ_sepShape_eval` | `OM/Order0Alpha.lean:254/:297/:360` |
| `rootCount_sepShape_eval` / `h_node0_proved` / `montes_order0_unconditional` | `OM/Order0Alpha.lean:385/:413/:450` |
| `classify_eq_sepShape` (γ5) / `classify_eq_sepShape_only_if` (γ6) | `OM/Order0Classify.lean:224` / `OM/Order0Fiber.lean:148` |
| `sepStratum` / `avail` / `card_sepStratum` / `necklaceQ_eq_card` | `OM/Order0Count.lean:183/:113/:377/:58` |
| `necklaceSum` / `necklaceSum_nonneg` / `dvd_necklaceSum` / `necklaceQ` / `necklaceQ_eq_natCast` | `OM/Necklace.lean:49/:69/:221/:256/:266` |
| `M8.stratumCount` / `L2_reconstruct` (ax) / `selfLoop_childFiber_corrected` (ax) / `boxVolumeScale_collapse` (ax) / `GMNNodeEfLaw` | `OM/LevelNCount.lean:55/:252/:1136/:1257/:997` |
| `cylinder_count_stable` / `selfLoop_childFiber_fkeyed` (ax) | `OM/CountingModel.lean:322/:520` |
| `M7.cellsOfShape` / `cellsOfShapeWF` / `cellsOfShapeWF_descend` / `cellsOfShapeWF_shapeOf` | `OM/CellPartition.lean:127/:150/:157/:175` |
| `M6.treeSize` | `OM/Termination.lean:51` |
| `classifyAux` / `B.classify` / `omReadValuation_lt_of_certLevel_fkeyed` (ax) | `OM/Classifier.lean:283/:487/:634` |
| `decode` / `realP` / `realClassify` / `rawCount` / `leafTypesUpTo` / `shapeMenu` / `shapesOf` | `OM/RealInstance.lean:105/:128/:138/:143/:156/:161/:192` |
| `realDensity_tame_functionalEquation` (ax) / `realM` / `realD` / `realF` / `montes_unconditional` | `OM/RealInstance.lean:485/:514/:681/:773/:942` |
| `CountCell` / `countCellCoeff` / `countPivot` / `clusterCount` / `clusterCount_rec` / `clusterCount_boxSum` | `MontesAxiom.lean:100/:119/:126/:311/:325/:360` |
| `MontesData` (fields `boxMeasure`/`boxHaarEquidist`/`nodeMeasure_boxSum`) / `MontesData.C` / `nodeMultiplicativity` / `undecidedVanishes` | `MontesAxiom.lean:386 (:415/:432/:446)/:517/:542/:618` |
| `CountingModel` | `CountingModel.lean:95` |
| `DensityFoundation` / `OMBridge` / `IsPalindromic` / `TameFunctionalEquation` | `Interface.lean:231/:285/:361/:392` |
| `MontesData.coeff` / `countingDensity_eq_sum_coeff` / `countingDensity_isRational` | `Decomposition.lean:70/:104/:185` |
| `goal_theorem` / `goal_theorem_montes` / `goal_theorem_via_montes` | `Goal.lean:87/:160/:222` |
| `DensityFoundation_nonempty` / `trivF` / `trivF_tame` | `Witness.lean:116/:284/:330` |
| `PadicMeasure` axioms | `PadicMeasure.lean:268/:272/:278/:405/:438` |
| `BB3inf` axioms | `BB3inf.lean:90/:95/:101` |
| `L4.newtonExponent` / `newtonVertexCount` / `bb1Value` | `L4.lean:70/:74/:79` |
| `L5fix.selfLoopExponent` | `L5fix.lean:38` |
| `npSides_of_flat` / `rootSide_eq_flat` / `rootResidual_eq_reduction` | `OM/Order0Hull.lean:243` / `OM/Order0Root.lean:99/:177` |
| audit harnesses | `LeanUrat/AxChk_baseline.lean` (★ line 22), `AxFalse.lean` (compiling `False` probe!), `AxProbe.lean` (STALE) |
| quarantine record | `lean_urat/quarantine/README.md`, `quarantine/omDensity_tail_2026-07-03.lean.txt` |
