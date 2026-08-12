# INVENTORY MAP — LeanUrat corpus vs. the five-node target

*(Composed by a read-only Explore agent under the 2026-08-12 parallel
regime; transcribed by the orchestrator. Part 3 of the Lean scoping
document.)*

## 0. HEADLINE FINDING (read first)

**The five-node proof has zero Lean footprint today.** The annex tags `W12`, `GENIND`, `HMENU3`, `HEX3`, `GENH4`, `GENHN`, `HE3/HE6/HE7`, `HETOW`, `GENTOW1–6`, `LIFTCORNER`, `GRTW2`, `GRTJA/B/C`, `WELDMASTER`, `SIGMALAW`, `W11` appear in **no `.lean` file anywhere** under `lean/` — only in `docs/*.md` and `lean/notes/openmath/*.md`.

Consequence for the 18-step plan: steps 8–12 are **greenfield authoring against informal notes**, not module moves. The existing corpus supplies *ingredients* (finite-field counts, Newton polygons, Witt base change, triangular solves, termination measures), never node statements. Only the KEEP island (step 1) and the Core/Counting splits (steps 3–4) are genuine migrations.

---

## 1. PER-NODE SOURCE MAP

Verified by reading declarations, not by echoing the verdict tables. `(N)` = file count.

### Node: Reduction (`Stage2/Reduction/MenuBound.lean`, `W12.lean`) — Units 2/3/4

| Source | What it actually supplies |
|---|---|
| `MovesSp/SP2_finThm.lean`, `SP2_finWords`, `SP2_speciesEnum`, `SP2_encodeCard`, `SP2_encodeInj` | **The menu-bound math**: `𝒮_n^raw` is FINITE and p-INDEPENDENT, via integer encoding + injectivity. This is the closest existing thing to W-12.A. |
| `OM/CellMenu.lean` (7 AxChk rows), `OM/CellPartition.lean`, `OM/MultiSlopeMenu.lean` (108 decls), `OM/ChainMenu.lean` | order-1 menu classifier (`cell_unique`, `cell_exists`, `classify1_eq_some_iff`), `Class`/`OfShapeWF_descend` partition |
| `OM/Drainage.lean` | `card_tail`, `card_undecided1`, `undecidedDensity_eq`, `tendsto_tailDensity_zero` — the drainage half of the reduction |
| `Kernels/E0Route.lean` | `blockMass`, `BlockDrain`, `blockMass_antitone`, `escape_of_drain` — a **matrix-shaped** drainage abstraction. Log says retire this as a measure seam; the four lemmas are reusable and measure-free. |
| `CountingModel.lean` | `decidedMeasure_sum_add_undecided`, `box_partition`, `UndecidedVanishes`, `countingDensity_is_squeezed_limit` |

### Node: Induction (`Species.lean`, `TwoSpecies.lean`) — Units 5/6 (GENIND.A/B)

| Source | What it actually supplies |
|---|---|
| **`MovesSp/` (71)** — the primary owner | `Defs.lean` = species datum + coherence + closure + interfaces; `DefsN3.lean` = sealed exhaustive n=3 catalogue; `SP0_*` = memCoherent / reflBudget (B1–B5) / reflCoherent (G1–G6) / reflSucc (SUCC menu) / succTerminal; `SP1_*` = shift-invariance, `shDvd`, `shE1`, `shStage`, `shEquiv`; `SP3_*` = entrance words, loop-collapse (`collapseWalk`, `collapseSublist`), `compMember`; **`SP4_rankStrict` / `rankStepInc` / `rankStepRec` / `rankRadix`** = the termination measure ρ(s) = (D, tagord, n−W, …) strictly decreasing — the induction's well-founded engine; `SP4_dagWalk`/`dagWords`/`selfloopChar`/`fullForcing`/`fullUnique`; `SP6_*` = the n=3 instantiation (`card53` = |𝒮₃^raw| = 53) |
| `HC2/` (28 files mention species) | second species campaign layer; RETIRE verdict, extract only if a `MovesSp` gap appears |
| `MovesU/` (22 species files) | bridge-layer species restatements; RETIRE |

### Node: StageLaws (`FiniteGenres.lean`, `OrderOne.lean`) — Units 7/8/9 (GENHN)

| Source | What it actually supplies |
|---|---|
| **`MovesS/` (98)** — the "final-shape stage law" owner | U-1 `dispatch_spec` (the (m,c) route iff-triple); U-2 `ktri`, U-3 `kcol_agree`, U-4/5/6 `scs_flank`/`scs_stage`/`scs`; U-7 `bdy_edge`/`bdy_node_shadow`/`bdy_mass_split`; U-8/9/10 `ksub_regroup`/`ksub`/`ksub_eval`/`ksub_pool`; U-19/20 `evalAt`/`eval_det`; U-28 `rs4_rational_step`; U-27 `ratfunc_eval_infinite` (the shared infinitude engine); `CountLaws.lean`; `Interfaces.lean` (RS1Meas/RS1Bundle/RS4Chain hypothesis interfaces). N2* (~40 files) = the n=2 worked instance, not general law. |
| `L3.lean` + `L3Squarefree.lean` + `L3Gauss.lean` | finite-field factorization API: separable↔squarefree, monic/irreducible-degree counts, `necklace_count`, `e_mul_card_eq_pow`, squarefree-monic recursion `S_recursion` |
| `OM/NewtonPolygon.lean` (60 decls) | `Slope`, `Line`, `IsValidLine`, `Height`, `Sides`, `Vertices`, `OnHull`, `Collinear*` — full hull geometry |
| `OM/ResidualPolynomial.lean` (19) | `Poly`, `Poly_mul`, `Poly_monic_normalized`, `separable_iff_squarefree`, `Descent_iff_exists_repeated`, `ResidualFactorization` |
| `OM/Order0*.lean` (Order0, Order0Alpha, Order0Capstone, Order0Classify, Order0Count, Order0Fact, Order0Fiber, Order0Hull, Order0RealDensity, Order0Root) | the closed order-zero stage law + `rootCount_isRational_of_leaf` |
| `OM/StratumOrder1.lean` (16), `OM/DecidedOrder1.lean` (7) | `Count1_eq_cellCard`, `Count1_eq_closed`, `Count1_partition`, `Count1_decided_density`, `Order1_omCount_tie` |
| `OM/HNode1.lean` | `h_node1_single`, `h_node1_selfLoop`, `h_node1_census`, `h_node1_general` |
| `OM/FDescentCensus.lean` | `Field_card_eq_q_pow_f`, `Census_child_eq_base_at_q_pow_f`, `Block_orbit_count` |
| `MovesGr/` (22) | `Defs.lean` = genuine graded ring `gr_w(A)`; `L0_*`/`L1_*` = `initialForm_mul`, `initialForm_add_lt`, `pmul_assoc`, `deg_add`; `L2_degZero_subring_v2`, `L3_residual_mul`, `L3_rank1_residual`, `L4_grRes_eq_genuine`. Retire `HeldUnits_*` (certificates). |
| `L4.lean` | `LatticePolygon`, `Exponent`, `VertexCount`, `Volume_eq`, `Volume_pIndependent` |
| `GMNIndex.lean` | ⚠ carries **`axiom AX_GMN_index_finsum`** (line 61) + `Accounting_of_face` |
| `Kernels/KA6b1.lean`, `KA6b2.lean` | `ka6b1_card_squarefree_monic(_pos)`, `ka6b1_degree_one_separable`, `ka6b2_exists_monic_irreducible`, `ka6b2_exists_monic_squarefree_not_X_dvd`, `WindowModel` — clean generic `[Field F] [Fintype F]` counts, the best "keep pure finite-field lemmas" candidates |
| `OM/SchwartzZippel.lean` | `card_roots_zmod_ppow_le`, `field_zero_count_le`, `tail_fiber_card` |

### Node: Ladder (`Base.lean`, `FractionalKeys.lean`, `StrictDescent.lean`, `Exhaustiveness.lean`) — Units 10–13

| Source | What it actually supplies |
|---|---|
| `OM/Termination.lean` | `treeSize`, `child_size_lt`, `treeSize_le_degree`, `cells_descend`, **`finiteTermination`** — the existing well-founded ladder skeleton |
| `OM/LevelDrop.lean` (+ `LevelDropResidue`, `ChildResidualLevelDrop`) | `levelDropCoeff`, `levelDropHom(_root)`, `gbar_levelDrop`, `resUnitResidue_levelDrop`, `childResidualExt_reduce_stable_of_cuts` — the level-descent transport |
| `OM/HullStability.lean` | `dropCollinear_*`, `collinear₃_trans`, `pairLine_right_form`, `sorted_head_min` — hull stability under descent (the geometry the fractional-height keys need) |
| `OM/GradedMargin.lean` | `sideFloor_le_sideDepth_of_admissible`, `sideDepth_add_sideDepth_ge_of_admissible` |
| `OM/DescendBijection.lean` | `descendMap`/`descendInv` + inverse pair, `fourMap_descendMap`, `pairMul`/`pairSq` |
| `MovesS/BlockSolve*.lean` (`BlockSolve`, `BlockSolveSpec`, `BlockSolveTot`), `SolveCramer`, `SolveExistsUnique`, `SolveIff`, `NeumannPartial`, `PowEntryNonneg/Tendsto`, `PowFixedVector`, `E0DetNeZero`, `E0InvNonneg`, `MulVecAbsBound` | triangular bottom-up solve + Neumann telescope + escape/drain: the algebraic form of exhaustiveness/descent termination |
| `MovesSp/SP4_rankStrict` | shared with Induction; the μ′<μ measure candidate |
| `L5fix.lean` (52 lines, RETIRE) | `Bound`, `LoopExponent`, `Loop_geometric` — the old termination mechanism the HE ladder replaces |
| `OM/SelfLoop*` (11 files, RETIRE) | the refuted per-depth decomposition + the surviving fixpoint `b = depth0 + slExposedRatio·b`. Read `AxChk_baseline.lean:295-401` before reusing — several theorems are documented as sound-but-not-density. |

### Node: Towers (`Budgets.lean`, `Windows.lean`, `TwistedTransport.lean`, `Cap.lean`) — Units 14–16

| Source | What it actually supplies |
|---|---|
| **`MovesRBase/` (9)** — exactly `Towers/BaseChange` | `Defs.lean`: `Kbar := AlgebraicClosure (ZMod p)`, `Wbar := WittVector p Kbar`, `Fsub m`, `O m`, `qq m := p^m`, `relExt m δ' := O (m*δ')`, `cyl`, `SpeciesSyntax`, `AlphabetData`, `EQ2law`. Laws: `Fsub_le`/`O_le` (d ∣ m monotonicity), **`O_chain`**, `relExt_relExt` (composition), `O_le_relExt`, **`qq_mul : qq (m*δ') = (qq m)^δ'`**, **`Fsub_card : Nat.card (Fsub m) = p^m`**, `EQ2law_card`, `map_comp`. Composition + cardinality laws, verbatim as the plan describes. |
| `Kernels/D4R0K/Tower.lean` | **`StageData`, `thr s := e*h*g`, `IAug prev cur := cur.e * prev.thr < cur.h`, `TowerData`, `ExtCarrier`, `Carrier`, `ψpoly` monic/degree lemmas, `j0`/`j0_lt`** — a ready-made **budget ledger** (`IAug` = the composed-budget inequality). Strongest `Towers/Budgets.lean` seed in the corpus. |
| `OM/TowerBase.lean` (38), `OM/UnramifiedBase.lean` (46) | `Gen`, `Gen_eq_root`, `MapG` inj/surj, `EquivG`, `Gen_pow_e`, `assembleG`, `PhiG` semilinear laws; unramified base local-ring/residue-field facts (`LocalRing`, `Maximal_span_p`, `residueField`) |
| `OM/DevelopTower.lean` (21) | `EquivTower`, `InCellTower`, `TowerLevel`, `Level_ballCount`, `level_census_equiv`, `tower_reduce_*`, `order2_tower_matches_child` |
| `OM/Development.lean`, `DevelopmentExt.lean` | `developEquiv`, `develop_unique`, `develop_map` (commutes with `Polynomial.map`), `developEquiv_card_consistency` |
| `OM/RphiRing.lean`, `RphiRingGenH.lean`, `RphiGenHCount.lean` | `card_Rphi`, `digitEquiv`, `card_residueField`, `isLocalRing`, `maximalIdeal_eq_span_theta_p`, `card_filtIdeal` — the level-N avatar of O_L with gapped ⟨e,h⟩ semigroup |
| `OM/RestartEquiv.lean`, `RestartEquivGenH.lean`, `TowerRestartAbstract/GenH.lean` | **`restartEquiv`** (the project's central lemma), `card_restart_fiber`, `card_freshPattern` |
| `OM/GradedCertificates.lean` (48), `OM/GradedHensel.lean` | `*_law_graded`, `*_ker_card`, `node_census`, `graded_ker_bound`, `pair_card_graded`, `caseB_law_graded` — the window/margin certificates |
| `OM/ProductTheorem.lean` (**41 AxChk rows**, the largest single block) | composed budgets in disguise: `imageSet_subset_inCellMulti_*`, `card_inCellMulti_fixedpin_*`, `node_identity_fixedpin_multiside`, `on_side_conv_of_cofactor`, `zmodValuation_mul/sum_unique_min` |
| `MovesS/PowSubst*.lean` | `powSubst` = base change q ↦ q^δ on ℚ(q), with `powSubst_mul` (nested composition) and `powSubstOK` transport — the rational-function side of base change |
| `OM/OrderTwoContext(R).lean`, `OM/RecenterBox.lean`, `OM/LiftKeyExt.lean`, `OM/ChildResidualExt.lean` | window recentering + the corrected-key/lift material |
| `Scaffold/HDischarge/H1/TowerStep.lean`, `TruncatedRun.lean`, `GlueRun.lean`, `Window.lean`, `Transfer.lean` | window ledger scaffolding (8 of these are in the measure closure — see §4) |

### Gauge package (`Gauge/Defs.lean`, `Cocycle.lean`, `Transport.lean`) — D4

Gauge/cocycle vocabulary (`cocycle`, `wrapComp`, `η^W`, θ-recursion, `liftKey`) lives in only **3 dirs**: `OM/` (9 files, incl. `LiftKeyExt`, `GradedCertificates`), `HC1/` (7 files), `Scaffold/` (4 files). This is the smallest and cleanest extraction in the plan.

### Counting.Algebra ← `MovesC/` (37)

Confirmed a compact, coherent, **measure-free** library: `Defs.lean` carries `Coord`/`CoordPrec` (the global order ≺), `Locus := DigitSystem m (ZMod p)`, `Locus.mass`, `boxMass p m := p^m`, `IsUnitriangular`, `Line`/`HtMap`/`floorOf`, `DomData`, `LevelClause`, `FreshData`, `TypObject`, **`Node`** (with `childWidth`, `mhat`, `vtxPoly`, `staircase`, `lineStep`, `fineSlot`, `spanSlot`, `IsNodeLift`, `LandingKey`), `History`, `JetSetup`. Laws: `C0_unitriBij`, `C0_moveMass`, `C1_clausesCount` (`card {sat} · p^mstar = p^m`), `C4_stepMass`, `C5_massRec`, **`C6_thmC_a/b`** (`#S(H,Z)·p^{Σm*+|pins Z|} = p^{nN}`), `C6_psiBij`, `C3_crossing`, `C2_DOM`. Zero sorries.

### Core/* split ← `Interface.lean` (411 lines) — D5, step 3

Exact split lines available:

- `Core/Factorization.lean` ← `FactorizationShape` (:50), `totalDegree` (:59), `FactorizationType` (:152), `FactorizationType.degree` (:157)
- `Core/ClusterShape.lean` ← `ClusterShape` (:180), `ShapeCell` (:192), `OMType` (:88), `NeedsDescent` (:117), `ResidualEquidistribution` (:129)
- `Core/RationalLaw.lean` ← `IsPalindromic` (:371), `TameFunctionalEquation` (:405); pairs with `RatFn.lean` (126 lines: `IsRationalFn` + closure lemmas)
- `Legacy/MeasureFoundation.lean` ← `DensityFoundation` (:231), `OMBridge` (:287), `clusterVolume_rational` (:343), and the sole `import LeanUrat.PadicMeasure` (:2)

---

## 2. THE STAGE2 SPINE AS IT EXISTS

`lean/LeanUrat/Stage2/` contains **exactly one file**: `UniformityTarget.lean` (137 lines, rev. 2 of 2026-08-12). Imported by **nothing** (verified: no `import` mentions `Stage2` anywhere). Its full import closure is **11 modules**: `MontesV2, Interface, CountingModel, RatFn, L7, PadicMeasure, OMInduction, L3, L3Squarefree, L4, L5fix`.

Declarations (3 total):

1. **`structure RealCountingFamily (n : ℕ)`** — the rev-2 canonical prime-indexed family. Fields: `modelAt : ∀ p, Nat.Prime p → CountingModel p n`; `menu : FactorizationType → Finset ClusterShape` (one shared menu); `coefficient : ClusterShape → ℕ → ℚ` (one shared C); `dataAt : ∀ p hp, MontesDataV2 p n (modelAt p hp)`; `shapes_coherent : ∀ p hp σ, (dataAt p hp).shapesOf σ = menu σ`; `coefficient_coherent : ∀ p hp T, (dataAt p hp).C T = coefficient T`; **`faithfulAt : True`** ← the named placeholder (Unit 1 / realness gates).
2. `theorem uniformity_target` — sorry #1.
3. `theorem uniformity_target_exhaustive` — sorry #2.

(The two sorries' enclosing statements are quoted verbatim in
LEAN_SCOPING_core_2026-08-12.md §1; the D9 defect is still live —
the exhaustive variant's drainage hypothesis is consumed nowhere.
Dangling doc reference at line 20: `MontesV2.countingDensity_eq_sum_C`
should be `MontesDataV2.countingDensity_eq_sum_coeff`.)

---

## 3. THE TRUSTED CAPSTONE CHAIN

### `OM/RealInstanceV2.lean` (17 decls; closure = 86 modules, 70 OM + 16 root)

Supporting instance triple: `realM2 : CountingModel M9.realP n` (:137), `realD2 : MontesDataV2 …` (:234), `realF2 : DensityFoundation` (:358). `montes_unconditional` fires `MontesV2.goal_theorem_montes (realM2 n hn) (realD2 n hn) σ realF2 hσ (fun _ _ => rfl) htameFE` — the `hbridge` argument discharges by `rfl`, which is why the V2 island is thin. `montes_unconditional_exhaustive` (:439) adds the drainage hypothesis and — unlike the Stage2 exhaustive target — **genuinely consumes it** (via `hlim.add hExhaust`) to conclude bracket-uniqueness. It is the model D9/step 15 should copy.

### `MontesV2.lean` (265 lines)

`MontesDataV2` (docstring itself flags interface weakness: degenerate empty-menu/`C ≡ 0` instances admitted by design; semantics pinned at the INSTANCE). Palindromy is the only leg of `goal_theorem_montes` needing `DensityFoundation`/`L7` (via `L7.tame_to_all_primes` + `L7.isPalindromic_of_agree`). **This confirms D8 is mechanically achievable**: drop the `IsPalindromic` conjunct and `F`/`hbridge`/`htameFE` become dead, leaving rationality + value tie — both `MontesDataV2`-internal and `L7`-free.

### What `AxChk_baseline.lean` pins (1450 lines, 91 imports)

**746 `#print axioms` rows**, no wildcards. Namespace distribution: `OM` 694, `PadicMeasure` 10, `SerreLocalFields` 5, `Witness` 4, `NestedCollapse` 4, `L7` 4, `RatFn` 3, `CountingModel` 3, `MontesV2` 2, others 1–2. Heaviest OM blocks: `OmLeafFaithful` 45, `ProductTheorem` 41, `RealInstanceW3` 23, `RealInstanceW`/`QpTypeMixed` 21, `RealInstanceW4`/`QpTypeH3` 18, `FullFaithfulGates` 17, `QpTypeSplitU` 16, `ChainMenu` 13, `RealInstanceV2` 12, `RealInstanceV2Gates` 10. Acceptance bar: Lean core only — `[propext, Classical.choice, Quot.sound]`; more is stop-the-line. The V2 capstone rows are re-asserted 8 more times as regression anchors after each W3/W4/W5/W6 wave. Ledger state at inventory: 166→178 rows GREEN.

---

## 4. COUNTS

### Files and real sorries per top-level dir

Real sorries = comment-stripped. Raw grep counts are inflated by prose.

| Dir | .lean | real `sorry` | raw grep |
|---|---|---|---|
| `OM/` | 134 | **0** | 204 |
| `MovesV/` | 128 | 10 | 37 |
| `Scaffold/` | 113 | 8 | 100 |
| `HC1/` | 103 | 5 | 60 |
| `MovesS/` | 98 | **0** | 13 |
| `MovesU/` | 95 | 7 | 47 |
| `MovesT/` | 74 | 4 | 59 |
| `MovesSp/` | 71 | **0** | 5 |
| `HC2/` | 66 | 2 | 57 |
| `Moves/` | 64 | **0** | 18 |
| `MovesD/` | 61 | **0** | 11 |
| `MovesX/` | 58 | **0** | 7 |
| `MovesC/` | 37 | **0** | 3 |
| `B2D/` | 27 | **0** | 16 |
| ROOT | 24 | **0** | 32 |
| `Kernels/` | 24 | **0** | 11 |
| `MovesGr/` | 22 | **0** | 2 |
| `MovesRBase/` | 9 | **0** | 1 |
| `Stage2/` | 1 | **2** | 4 |
| **TOTAL** | **1209** | **38** | 683 |

All 38 real sorries by file: Scaffold/DictIII/CU1 (4), MovesU/SlotsG2_relFamily (4), HC1/V9_K1nonrec (4), Stage2/UniformityTarget (2), MovesV/TV_G3 (2), MovesT/G1_toyGate (2), Scaffold/{ValueSide/Transfer, MeasureFloor/SumOne, DictIII/Locality, DictIII/Devid} (1 each), MovesV/{V7_scsData, V7_rbC, V7_livC, TV_F6, TV_F5, TV_F4, TV_F3, TV_F2} (1 each), MovesU/{SlotsG3_rel3, SlotsG11c_seamAudit, BridgeD19_omAgree} (1 each), MovesT/{TV_B7, E11_treeN} (1 each), HC2/{U26_fiberWelldef, U17a_liftSwap} (1 each), HC1/CL04_addrDichotomy (1).

**The node-source dirs (`MovesS`, `MovesSp`, `MovesC`, `MovesGr`, `MovesRBase`, `Kernels`, `OM`) are entirely sorry-free — 495 files, 0 sorries.** Every real sorry outside Stage2 lives in a RETIRE-verdict dir.

### PadicMeasure route (the measure isolation target)

**Direct importers of `LeanUrat.PadicMeasure`: exactly one — `Interface.lean` (line 2).** `PadicMeasure.lean` declares **5 axioms**: `omCells`, `descend`, `descend_size_lt`, `clusterMeasure`, `AX_cellRecursion`.

Transitive importer closures: `OMInduction` 147, **`PadicMeasure` 146** (incl. Stage2 1), `Interface` 145, `CountingModel` 132, `Goal` 95, `MontesV2` 42, `SerreLocalFields` 3.

**`Stage2/UniformityTarget.lean` is in the PadicMeasure closure today** (`Stage2 → MontesV2 → Interface → PadicMeasure`). This is the single edge D2/D5 must cut; splitting `Interface.lean`'s `DensityFoundation`/`OMBridge`/`clusterVolume_rational` into `Legacy/MeasureFoundation.lean` cuts it, because Stage2 rev-2 no longer references `DensityFoundation` at all.

**Dirs entirely outside the measure closure (1063 of 1209 modules):** `B2D`, `HC1`, `Moves`, `MovesC`, `MovesD`, `MovesGr`, `MovesRBase`, `MovesS`, `MovesSp`, `MovesT`, `MovesV`, `MovesX` — all 100% clean.

**Non-OM contaminated files (21) — the complete quarantine-or-rewire list:** `Stage2/UniformityTarget.lean` · `HC2/DefsPrime.lean` · `Kernels/WeightChargeRed.lean` · `MovesU/{BridgeD19_omAgree, BridgeD19_omAgreeNeg, BridgeDict, BridgeMk, BridgeSolve}.lean` · `Scaffold/{AnchorN2, AxChk, CorpusBridge}.lean` · `Scaffold/HDischarge/H1/{GlueRun, JuncForge, RecSLWire, SiteExhProbe, TruncatedRun}.lean` · `Scaffold/MeasureFloor/{Base, NsNull, Semantic, SumOne, Types}.lean`

**The 21 measure-free `OM/` modules** (safe to migrate into the five nodes): `Development`, `DevelopmentExt`, `HenselCount`, `HullStability`, `LevelDrop`, `LiftKeyExt`, `LimitRecurrence`, `LinearFiber`, `Necklace`, `NewtonPolygon`, `Order0Hull`, `PadicLift`, `PadicValuation`, `QuotientBox`, `ResidualPolynomial`, `RphiGenHCount`, `RphiRing`, `RphiRingGenH`, `SparseResultant`, `TowerBase`, `UnramifiedBase`.

Direct mathlib `MeasureTheory`/`Haar` users — only 9 files: `Scaffold/MeasureFloor/{Haar,Decided,Semantic,SumOne,Base,NsNull}.lean`, `Scaffold/O12/Semantic.lean`, `OM/{QuotientBox,LimitSpine,LevelNCount}.lean`.

### Axiom census (trust boundaries)

Real `axiom` declarations, 5 sites: `PadicMeasure.lean` (5), `GMNIndex.AX_GMN_index_finsum`, `SerreLocalFields.AX_integralClosure_dvr`, `OM/Classifier.omReadValuation_lt_of_certLevel_fkeyed`, `OM/OmLeafFaithful.om_leaf_faithful` — plus ~13 deliberately-false `*_MUTATED_*` countermodel axioms in RETIRE-verdict `OM/QpType*`/`FullFaithfulGates`/`OmLeafFaithful` files.

Closure check: `RealInstanceV2`'s 86-module closure includes `PadicMeasure` and `OM/Classifier` (reachable-by-import, not consumed — footprint core-only per AxChk) and **excludes** `OmLeafFaithful`, `GMNIndex`, `SerreLocalFields`, `FullFaithfulGates`, `QpType*`. Stage2's 11-module closure includes `PadicMeasure` only. **`OmLeafFaithful.om_leaf_faithful` is a genuine axiom carrying 45 AxChk rows on a chain the V2 capstone does not touch** — worth its own step-2 quarantine-manifest entry.
