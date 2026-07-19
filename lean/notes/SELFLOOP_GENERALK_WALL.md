# The self-loop h_node general-k census wall — precise characterization (2026-07-11)

**Status of this session's work.** Build #48 green (49 green builds): general-μ self-loop
fixpoint formalized (`SelfLoopFixpointGeneralMu`), μ=3 self-loop density SETTLED = **20/31**
(three-way MC-backed: engine anchor `padic_types.monic_cubic_pred '1c'` + PARI oracle +
fresh 800k MC z=−0.01; naive scalar 16/31 rejected at z=+241), cross-fed size-3
`omChildCount shape3Half 2 = 32/93` through the genuine WF recursion. All core-only.

**The wall (recurring, now precisely characterized).** The self-loop h_node at self-loop
depth k≥2 needs the ACTUAL finite-N `stratumCount1` census, decomposed by self-loop depth,
to converge (×q-exposed) to the engine value `depth0·countPivot⁻¹`. The abstract geometric
tower `floorTowerMass k = depth0·slBoxRatio^k` has the CORRECT limit (PROVEN abstract, Part D
of `SelfLoopDensityConnect`; = 2/3 at the halfCluster child, MC-confirmed). The gap is
connecting that abstract tower to any ACTUAL iterated box census at general depth.

**Numerical finding (2026-07-11, `/workspace-vast/asving/tmp/verdict_census/`,
`FLOORCHAIN.py` / `FASTGATE.py` / `GATE_FIXPOINT.py`, exact, uniform in N):**
NO natural iterated box census matches the geometric `slBoxRatio^k` per depth:

- **Verdict chain** (`classify1(recenterIter i g)=selfLoopCell`, i<k): NON-geometric. At
  (2,N,2): per-level ratios v[k+1]/v[k] = 9/64, ~2/9, ~1/2, ~... irregular; the ×q^k-exposed
  aggregate DIVERGES (62, 126, ...), does NOT reach `countPivot⁻¹=4/3`. Its bare fixpoint
  recursion is `v(N)=shallow+slBox·v(N−2)` → 1/7, not the density. **This is why
  `VerdictTranslationInvariant` / uniform coset density (SelfLoopCensusFiltration STEP 3,
  SelfLoopCensusK "UNIFORM COSET DENSITY") is FALSE** — re-confirmed: coset_k·scale ≠ cluster_k
  ∀k≥1. The verdict census is the WRONG object (matches the retired Part E).
- **Floor chain** (`selfLoopFloor(recenterIter i g)`, p^(μ−j)|coeff_j, i<k): SATURATES.
  f_0=1, f_k=1/2 constant ∀k≥1 (ratios 1/2,1,1,1,...). Recenter PRESERVES the floor
  (`recenter_mem_clusterBox`), so "stay in the floor set" is automatic after level 1 — NOT
  geometric with slBox. Same for the cluster-chain (recenter is a clusterBox endomorphism).

**Consequence.** The geometric `slBoxRatio^k` is a count over the DEVELOPING p-adic tower ring
(`DevelopTower.card_r_level_census`, PROVEN all r = ∏∏ ballCount over `towerLevel…r`), NOT a
chain-in-a-fixed-box condition. The precise missing lemma is the identification of the actual
depth-k stratum census with the developing-tower ball-count product — i.e. relating the
fixed-box `recenterIter` census (ZMod p^N) to the developing-tower ring census at general
depth, on the actual `stratumCount1`. This is the "child-as-fresh-cluster" identification
iterated k-fold, NOT via any fixed-box chain predicate. Normalization note: `stratumCount1`
seed ratio = slBox (1/8 at (2,·,2)) is relative to the FULL box; `floorTowerMass depth0`=(q−1)/q
=1/2 is the child-normalized seed — the two differ by the clusterBox index p^μ.

**Routes exhausted (≈4 rounds, all meet here):** verdict/STEP3 (false), floor/STEP2
(per-level proven but saturates on chains), fixpoint reframe (correct algebra + general-μ, but
NOTE confirms per-depth k≥2 still open). Endpoints agree everywhere (density MC-confirmed); the
bridge at general depth is the genuine open lemma.

**Scope of the wall — it is the SOLE genuine obstacle (Thread 2, verified 2026-07-11).**
The tame case (every prime p > n) has NO self-loop at all: a self-loop needs wild ramification
(p | e for some ramification index e ≤ n), impossible when p > n (then p ∤ d for every part
d ≤ n, so v_p(d)=0 and descent terminates at separable all-μ=1 leaves). Every tame per-shape
h_node is PROVEN UNCONDITIONALLY and core-only: unramified `Order0.montes_order0_unconditional`;
tame ramified single-side `ClassifierBridgeFiber2.montes_order1_selfloop_density`; multi-slope
`PathShapeMultiSideTree.hnode_multiSideProduct`; assembled through `montes_allorders_of_hnode`.
The only remaining tame work is the σ↦shapes menu enumeration (S3a) — the SAME shared long-pole
as the general case, NOT wild-specific. Verified scratch certifications:
`/workspace-vast/asving/tmp/assemble_hyp/TameAssembly.lean` (all core-only, exit 0).
⟹ **The wild self-loop general-depth census is the ONLY genuine open obstacle in the whole
formalization** (everything else is proven unconditionally or is the shared S3a menu assembly).

**Assembly-under-hypothesis (Thread 2, verified).** Under the honest hypothesis
`FloorCensusPerDepth` (the FLOOR-tower per-depth identity `depthKMass N k = q^k·floorTowerMass k`
— NOT the false uniform-coset-density), the chain closes to the density:
`floorAgg_of_hyp → hnode_selfloop_box_order1 (PROVEN) → fixpoint (PROVEN) → density`, general μ.
Scratch `/workspace-vast/asving/tmp/assemble_hyp/SelfLoopHypAssembly.lean` (core-only, exit 0).
Caveat: `depthKMass` there is a FREE function; tying it to the actual `stratumCount1` depth-k
slice (and whether that slice really is `q^k·floorTowerMass k`) is EXACTLY Thread 1's open lemma.

**Thread 1 result (2026-07-11, tower-ring route CLOSED as unable — sharpens the target).**
The recommended tower-ring bridge is refuted: at `e=1` (the self-loop regime) the developing
tower ring IS the base ring (`SelfLoopTower.ringIso : Rphi p N 1 1 c ≃+* ZMod (p^N)`), so
`DevelopTower.card_r_level_census` is CONSTANT in tower level `r` (returns the depth-0 fiber at
every level) — no per-level geometry. (Tower geometry appears only at `e>1`, but the self-loop is
`e=1`.) Numerically validated mirror at `/workspace-vast/asving/tmp/tower_bridge/` (level-0 matches
Lean `census_base` exactly). **FOUR natural actual objects now refuted:** verdict chain
(N-dependent, diverges), floor chain (saturates), tower-ring `card_r_level_census` (constant in
r — NEW), decide-shallow-at-depth-k `Dsh_k` (N-dependent, not geometric per depth — NEW;
`Dsh_0/ncl=(p−1)·slBox` exact/uniform = Part A seed, but `Dsh_1/ncl` overshoots `slBox·seed`).
⟹ **There is NO per-depth finite-N geometric count identity.** The correct target is the
AGGREGATE/LIMIT: `lim_N Σ_k q^k·(Dsh_k(N)/ncl)/(Dsh_0/ncl) = countPivot⁻¹` (finite-N partials
converge monotonically: (2,2) 1.0→1.25→1.281→4/3; (3,2) 1.0→1.111→9/8), fed by a Drainage-style
tail bound — NOT a per-depth box equality. Do NOT assume `Dsh_k/ncl → depth0·slBox^k` pointwise
(it overshoots). Key structural lever: at `e=1` the self-loop-again is a self-map of the SAME base
box (endomorphism), so the density is a genuine fixpoint `b=seed+r·b` on the AGGREGATE, r from the
×q residue-translate exposure — the total-census route (Thread 3), not per-depth.

**Thread 3 result (2026-07-11, depth-bypass NO-GO, exact counterexample banked).**
The total (all-depths) verdict census satisfies EXACTLY `A(N) = slBox + slBox·A(N−2)` → fixpoint
`slBox/(1−slBox) = 1/7` — a clean N-recursion, but with the BARE ratio, so the WRONG fixpoint
(density is 2/3, needs the EXPOSED ratio slExposedRatio=q·slBox). The ×q exposure CANNOT be folded
into a total recursion: the ×q-exposed total `Σ_k q^k·cluster_k/ncl` DIVERGES (1.53, 2.41, 8.16,
24.2, 65.7 at (2,N,2)), because the actual per-depth census decays with per-step ratio →1, not
slBox, so `q^k·(depth-k)` grows. The ×q exposure is intrinsically PER-DEPTH; a total census has
already summed over k and carries only the bare ratio. So the two endpoints (bare recursion→1/7,
exposed per-depth→2/3) sit on opposite sides of the ×q exposure and no total-census object bridges
them. Banked core-only: `/workspace-vast/asving/tmp/bypass_depth/BypassDepthNoGo.lean`
(`bare_recursion`, `bare_fixpoint_eq`=1/7, `bare_fixpoint_ne_engineDensity`,
`exposed_fixpoint_eq_engineDensity`=2/3, `ratios_differ_by_q`).

## CONVERGENT CONCLUSION (all three threads, 2026-07-11)

**The self-loop h_node general-k census does not reduce to ANY clean count identity.** Five routes
refuted, each with an exact counterexample (three banked as core-only Lean no-go's):
1. Verdict chain per-depth — non-geometric, exposed sum diverges.
2. Floor chain per-depth — saturates (recenter preserves floor).
3. Tower-ring `card_r_level_census` — constant in r (e=1 ⟹ tower ring ≅ base ring).
4. Decide-shallow-at-depth-k `Dsh_k` — N-dependent, overshoots slBox·seed.
5. Total-census N-recursion (bypass) — clean but bare ratio → 1/7 ≠ density; exposed total diverges.

**Deep reason:** the ×q residue-translate exposure is intrinsically per-depth (weight q^k at depth
k) AND the actual per-depth finite-N census is not geometric. The abstract `floorTowerMass` tower
(PROVEN → density) is a formal idealization matching NO concrete finite-N box census. The genuine
missing content is RESIDUE-THEORETIC (recenter maps valuation patterns uniformly, but the self-loop
verdict depends on unit residues, not valuations) — the deep analytic OM density content, NOT a
combinatorial count identity. This is why every count-identity route (5 of them) fails.

**Status of the whole formalization:** COMPLETE except this one wild self-loop h_node. Tame (all
p>n) done; count keystone done; general-μ fixpoint + μ=3=20/31 done; assembly closes under the
honest explicit hypothesis (Thread 2). The self-loop h_node needs either (a) the residue-theoretic
OM density argument (hard, separate sub-project), or (b) taken as an explicit MC/PARI-true
hypothesis and discharged later. Recommendation: (b) complete the full CONDITIONAL theorem now
(density = engine: unconditional tame + wild modulo the single explicit self-loop hypothesis), and
scope (a) as the named remaining analytic input.

## DEFINITIVE RESOLUTION (Thread B, residue-theoretic, 2026-07-11 — the ×q is measure-theoretic)

The residue-theoretic investigation settled WHY every count route fails, exactly:

- **FACT A (recenter cascade, EXACT p=2, core-only Lean):** recenter sends the self-loop-again set
  at level k bijectively onto the newly-DECIDED set at level k+1: `Shallow_{k+1}(N)=Deep_k(N)`,
  all k, N (verified N=5,7,9). p-dependent — fails at p≥3.
- **FACT B (conditional no-go, EXACT, THE sharpest wall statement, core-only Lean):** conditioned on
  a self-loop verdict, `P(deep|verdict)(N) → slBox` (the BARE ratio q^{−s(s+1)/2}), NOT the ×q-exposed
  `r = q·slBox`. Verified p=2 (`1/9, 9/73, 73/585 → 1/8`, not 1/4) and p=3 (`1/28 → 1/27`, not 1/9).

**Conclusion — the ×q residue-translate exposure is INVISIBLE to every finite-N box count** (proven
six ways now). It is intrinsically the difference between *counting* the q translate-cosets of each
self-loop level (finite-N census → `slBox`) and *integrating* over them (p-adic Haar cluster measure
→ `r = q·slBox`). The factor q per level appears ONLY in the N→∞ Haar limit — it is a
MEASURE/equidistribution fact, NOT a count identity. The **count-native route is a proven dead end
for the ×q**; no combinatorial finite-N identity can produce it.

**The measure frame does not independently crack it — it IS it.** `PadicMeasure.lean`: the self-loop
resummation `1/(1−q^{−w})` is literally the `omPivot` divisor inside the declared axiom
`AX_cellRecursion` (Igusa/Denef local-zeta cell recursion); `clusterMeasure_isRational_of_AX`
derives density+rationality MODULO that axiom. So the ×q self-loop pivot is exactly the content of
`AX_cellRecursion`. Banked 6th no-go (sharpest): `/workspace-vast/asving/tmp/residue_core/ResidueCascadeNoGo.lean`
(13 thms, core-only; `no_go_consolidated`, `Pdeep_limit_ne_r`, `gap_is_slBox`, cascade_5/7/9).

## THE TWO-ROUTE STRUCTURE (honest complete picture)

- **Count-native route (axiom-free, core-only):** proven unconditional for ALL tame primes; wild
  reduced to the single aggregate self-loop hypothesis `SelfLoopHNode` (build #49
  `ConditionalDensity.density_eq_engine_conditional`). CANNOT reach the ×q (proven).
- **Measure-native route:** full density = rational MODULO `AX_cellRecursion` (= Denef's Igusa-zeta
  rationality, a declared standard axiom), which INCLUDES the ×q self-loop pivot — the Witness
  capstone (`montes_full_instance`, footprint includes `PadicMeasure.clusterMeasure`/`AX_cellRecursion`).

The two are COMPLEMENTARY: count-native is axiom-free but stops at the ×q; measure-native reaches
everything but rests on `AX_cellRecursion`. Full unconditionality of the wild self-loop = proving
`AX_cellRecursion` (Denef's theorem) — a known-hard, legitimately-citable result. The formalization
is thus "complete modulo Denef" (measure route) OR "unconditional for tame + one explicit honest
hypothesis for wild" (count route, #49).

**Recommended next directions (for the user to choose):**
1. Pursue the fixed-box ↔ developing-tower-ring identification at general depth (wire
   `card_r_level_census` to actual `stratumCount1` via the recenter/develop tower — the
   `two_level_census`/`census_step_equiv` bijection is banked at k=1; the k-fold needs the
   tower-ring reindexing, NOT uniform coset density).
2. Accept the self-loop h_node depth-k≥2 census as a stated HYPOTHESIS (it is MC/PARI-true) and
   proceed to the full assembly / tame cases, discharging it later — matches the user's earlier
   "assume as theory and keep running with the lean we can discharge later."
3. Reconsider whether the h_node even NEEDS the per-depth decomposition, or whether a direct
   total-census-to-limit argument (bypassing depth) exists.
