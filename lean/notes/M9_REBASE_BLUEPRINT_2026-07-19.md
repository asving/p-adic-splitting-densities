# M9_REBASE_BLUEPRINT — rebasing `montes_unconditional` onto the corrected engine

**Date: 2026-07-19. Status: SIGNED OFF (Asvin, 2026-07-19) — D1 = (i) additive-then-swap;
D3 = (a) include the full-density clause behind `hExhaust`; D4 = retire the axiom (tame FE as
hypothesis; v2 capstone footprint Lean-core only). D2/D5 as specified.
W1–W3 COMPLETE (2026-07-19): `MontesV2.lean` + `OM/RealInstanceV2Prep.lean` + `OM/RealInstanceV2.lean`
+ `OM/RealInstanceV2Gates.lean` all green, capstones + 10 gates core-only, census zero-regression
(585 entries), Python gate 21/21 exact, fresh-context semantic audit 9/10 PASS with the one
justification gap (tame-prime htameFE non-triviality) closed by `gate_v2_htameFE_nontrivial`.
W4 (the swap + axiom retirement) AWAITING SIGN-OFF.**

Successor to `VACUITY_SIGMA_BLUEPRINT.md` (whose Phase A is **complete** in the repo:
`montes_order0_unconditional`, `h_node0_proved`, `montes_order0_density_general_prime` + positivity
gates, `Necklace.necklaceQ_nonneg`/`_eq_natCast`, the S1 skeleton `montes_allorders_of_hnode`, the
order-1 self-loop leg, and the conditional assembly `density_eq_engine_conditional`). This blueprint
executes PROJECT_STATE.md standing obligation 1: make the all-orders capstone certify a TRUE,
non-vacuous, σ-dependent statement. Prepared after a three-agent wiring survey (2026-07-19);
file:line references verified against the current tree.

---

## §0. Goal and honest scope

**Goal.** Replace the vacuous `M9.montes_unconditional` (`OM/RealInstance.lean:982`) with a capstone
whose conclusion is about the CORRECTED engine density
`g_σ(q') := ∑_{T ∈ omMenu n σ} omCount T q'` (σ-keyed menu, corrected per-node semantics), which
fires a `Goal`-layer theorem over a real `DensityFoundation` instance, and whose hypotheses are
TRUE-shaped (each either discharged, or an honest open input that numerics confirm and Phase B
targets).

**The rebased capstone WILL certify** (for degree-n σ):
1. uniform rationality of `g_σ` (one num/den, all q' > 1) — UNCONDITIONAL (`omCount_isRational`);
2. the real normalized decided counts at `realP` converge to `g_σ(realP)` — order-0 leg
   UNCONDITIONAL (`h_node0_proved`), wild self-loop legs behind `SelfLoopHNode` (vacuous for the
   current order-0 menu);
3. genuine σ-DEPENDENCE (O1 killed): distinct σ get distinct menus and provably distinct values (§5 G2);
4. non-vacuity (V1 killed): certified value > 0 at concrete σ (banked gates);
5. palindromy of `g_σ` — CONDITIONAL on `htameFE` (hypothesis, not axiom — see D4).

**It will NOT claim** (stated loudly in its docstring):
- that `g_σ` is the FULL density ρ(n,σ;q) — the decided limit equals the full density only given
  exhaustiveness/drainage (`TameMenuExhaustive`-style; classifier does not drain at any finite
  order, `Drainage.lean`) — Phase B;
- unconditional palindromy — the monic decided stratum is genuinely non-palindromic; the faithful
  Del Corso–Dvornicich cite needs exhaustiveness + the M1 projective bridge (see D4);
- any order-≥1 wild content beyond the self-loop hypothesis.

---

## §1. Wiring facts the design rests on (surveyed 2026-07-19)

**Old capstone anatomy (all must-change):**
- `montes_unconditional` (`RealInstance.lean:982–1010`): `h_node` hypothesis TYPE is the old
  box-sum → `clusterCount` limit (`:983–990`); conclusion sums `realD.coeff = clusterCount ≡ 0`;
  fires `Goal.goal_theorem_montes` with `hbridge = rfl` and the axiom
  `realDensity_tame_functionalEquation` (`:1010`).
- `shapesOf σ₀ σ = if σ = σ₀ then shapeMenu n else ∅` (`RealInstance.lean:192–193`) — σ-independent
  (query passed as σ₀); `realF.multiplicity ≡ 1` (`:796`).
- `realM/realD/realF` (`:514/:681/:773`) all carry the old `h_node` type in their signatures.
- The axiom `realDensity_tame_functionalEquation` (`:485–491`): RHS is the `clusterCount` sum —
  currently "true" ONLY because that sum ≡ 0. See D4.
- `MontesData` (`MontesAxiom.lean:386`) is pinned to the refuted semantics by `boxHaarEquidist`
  (`:432`, `boxMeasure = countCellCoeff`) and `nodeMeasure_boxSum` (`:446`, box-sum/`countPivot`
  target); `D.coeff := clusterCount` via `MontesData.C` (`:517`) + `Decomposition.lean:70`.
- `Goal.goal_theorem_montes` (`Goal.lean:160`) / `goal_theorem_via_montes` (`:222`) consume ONLY
  `D.coeff`, `D.countingDensity_isRational`, `D.countingDensity_eq_sum_coeff`, `hbridge`, `htameFE`
  — the Goal layer is agnostic to HOW rationality/value-tie are produced. Core-only footprints.
- `decode` (`RealInstance.lean:105`) is VESTIGIAL — not consumed by the realM/realD/realF path
  (cells come from `M7.cellsOfShapeWF` payload reads). PROJECT_STATE's "repair the decode" is,
  post-A3/A4, really "repair the coefficient semantics + σ-keying"; no decode work is needed.

**Corrected assets (reused, not re-proved):**
- `omCount` + `omCount_isRational` (every shape) — `OMCountV2.lean:300/:497`; pivot at cluster
  nodes only; `omCount_sepShape_eq_rootCount` (`:366`) transfers all Phase-A theorems.
- `omMenu n σ` (`OMCountV2.lean:311`) `= sepShapesOf n σ` at R1 (definitional); Phase-B TODO
  (`:65–69, :307–310`): extend with classifier-emitted deeper shapes, `typeOf`-keyed.
- S1 skeleton `montes_allorders_of_hnode` (`MontesAllOrders.lean:67`) — arbitrary menu + per-shape
  `h_node` ⟹ rationality + value tie.
- `density_eq_engine_conditional` / `SelfLoopHNode` / `hNodeLimit` (`ConditionalDensity.lean:113/
  :85/:68`) — the conditional assembly with tame legs discharged (`hNodeLimit_unramified` etc.).
- m×C split for the `DensityFoundation.decomposition` field: `omCount_eq_mul`, `omMultiplicity`,
  `omVolume` (`OMCountV2.lean:552/:536/:544`).
- Positivity/integrality: `rootCount_sepShape_nonneg`, `gate_rootCount_inert2` (=1/4),
  `montes_order0_certified_value_pos` (`Order0Alpha.lean:519/:504/:545`); `Necklace.lean`.
- `CountingModel` fields (`CountingModel.lean:95`): on the current menu all fields are genuinely
  dischargeable — `decided_mono` via level-≥1 CONSTANCY of normalized separable counts
  (`stratumCount_sepShape`), `decided_tendsto`/`densityVal` via the per-shape limits,
  `box_partition`/`undecidedCount ≥ 0` via menu disjointness (distinct σ ⟹ disjoint `sepShapesOf`
  images; distinct shapes ⟹ disjoint classifier fibers), `upper_tail` via decided-stays-decided on
  the separable stratum (mod-p stability, banked). NO false-shaped field survives.

**Blast-radius verdicts (from the consumer survey):**
- MUST change (type-level committed to old semantics): `montes_unconditional`, `realM/realD/realF`,
  `MontesData.{boxMeasure, boxHaarEquidist, nodeMeasure_boxSum, C}` + `Decomposition.{coeff,
  coeff_isRational, countingDensity_isRational, countingDensity_eq_sum_coeff}` — or be BYPASSED by
  V2 siblings (D1).
- SAFE to leave: `countCellCoeff`/`countPivot`/`clusterCount` definitions (`countPivot` is LIVE on
  the corrected path via `omChildCount`; `clusterCount` transitively referenced by `rootCount`'s
  dead children product); the whole M8 layer (`stratumCount`, `shapeFiberCount` — shared);
  banked reductions (`LimitGlue`, `LimitSpine`, `nodeTrunc_tendsto`, SelfLoop suites);
  `Witness.trivD`. The four §4-flagged false axioms are ALREADY deleted (tombstones only).

---

## §2. The rebased capstone (target shape; exact Lean pinned in W1)

New module `OM/RealInstanceV2.lean` (additive; see D1):

```
-- the σ-keyed corrected real counting model (fields discharged per §1)
realM2 (n) ... : CountingModel realP n          -- decidedCount σ N := ∑_{T ∈ omMenu n σ} M8.stratumCount (rawCount n) T N
-- the abstract-coefficient Montes data (D2): C := omCount, C_isRational := omCount_isRational,
-- stratum_tendsto_C := per-shape hNodeLimit legs
realD2 (n) ... : MontesDataV2 realP n realM2
-- the corrected real density foundation: the FIRST non-trivial real instance
realF2 (n) : DensityFoundation
  -- density n σ q' := ∑_{T ∈ omMenu n σ} omCount T q'   (0 at other degrees, as now)
  -- shapes := omMenu, multiplicity := omMultiplicity, clusterVolume := omVolume
  -- decomposition := omCount_eq_mul; density_nonneg := menu nonneg (order-0: rootCount_sepShape_nonneg)

theorem montes_unconditional_v2 (n) (σ) (hσ : σ.degree = n)
    (hSelfLoop : ConditionalDensity.SelfLoopHNode n isSelfLoopPred)   -- wild input; VACUOUS on the R1 menu
    (hExhaust : MenuExhaustive n σ)                                    -- ONLY for clause (V2) below
    (htameFE : TameFunctionalEquation (realF2 n) n σ) :               -- hypothesis, NOT axiom (D4)
    ∃ num den, den ≠ 0 ∧
      (R)  ∀ q' > 1, den(q') ≠ 0 ∧ ∑_{T ∈ omMenu n σ} omCount T q' = num(q')/den(q')   -- unconditional
      (V)  (realM2 n).countingDensity σ = num(realP)/den(realP)                          -- decided-density tie
      (V2) [given hExhaust] the FULL type-σ density tie                                   -- optional clause, see D3
      (P)  IsPalindromic num den                                                          -- via htameFE
```

plus the discharged corollary (the deliverable headline): on the current R1 menu `hSelfLoop` is
vacuous (no self-loop shapes in `sepShapesOf`), so `montes_unconditional_v2` specializes to a
core-only theorem conditional ONLY on (`hExhaust` if clause V2 retained) + `htameFE` — with clauses
(R), (V) fully unconditional and non-vacuous (value 1/4 > 0 at n=2 inert).

The Goal wiring: `montes_unconditional_v2` fires `goal_theorem_montes_v2` (Goal-layer sibling typed
over `MontesDataV2`, proof verbatim modulo field names), giving the ∀F conditionals their first
non-trivial real instance `realF2`.

**W2 packaging refinement (2026-07-19, post-W1):** hypothesis-minimal split into TWO theorems —
(a) `montes_unconditional_v2` takes ONLY `htameFE` (on the R1 menu the counting legs are discharged
outright by `hNodeLimit_unramified`, so `hSelfLoop` would be an unused hypothesis; it re-enters via
the INSTANCE when the Phase-B menu grows); (b) `montes_unconditional_v2_exhaustive` adds `hExhaust`
(undecided normalized mass → 0) and the clause-(V2) content as BRACKET UNIQUENESS: any `d` consistent
with every level-N bracket `[decidedMeasure σ N, decidedMeasure σ N + undecidedMeasure N]` equals
`countingDensity σ` — the only definable full-density tie short of the semantic wall (no formal
"true type of f over ℚ_p" exists to compare against).

---

## §3. Design decisions REQUIRING SIGN-OFF (D1–D5)

**D1 — Additive-then-swap vs surgical in-place.**
(i) *Additive-then-swap (RECOMMENDED)*: land `MontesDataV2` (abstract coefficient: fields
`C : ClusterShape → ℕ → ℚ`, `C_isRational`, `stratum_tendsto_C` REPLACING `boxMeasure`/
`boxHaarEquidist`/`nodeMeasure_boxSum`), `DecompositionV2` lemmas, `goal_theorem_montes_v2`,
`RealInstanceV2` — all leaf modules, old chain frozen and green throughout. THEN, in a separate
signed-off wave (W4), swap names: old capstone + `realM/realD/realF` + the old-`MontesData`
`Decomposition`/`Goal` bridge → `quarantine/` with tombstones; V2 assumes the `montes_unconditional`
name. End state: ONE chain, corrected semantics, no duplicated spine.
(ii) *Surgical*: re-type `MontesData` in place. Smaller end-state diff, but the tree is broken
mid-flight across MontesAxiom/Decomposition/Goal/RealInstance/Witness — against the
honest-increments discipline that §2.7 of the vacuity blueprint established.

**D2 — MontesDataV2 = abstract-coefficient form.** The V2 structure carries the per-shape
coefficient abstractly (`C`, `C_isRational`, `stratum_tendsto_C`) instead of hard-coding a per-node
recursion shape. Rationale: the Goal layer only ever consumes the three derived facts; the refuted
box-sum shape (`D1–D6` defects) came from freezing engine internals into the interface. The
corrected instance sets `C := omCount`; the old `clusterCount` instance remains expressible (for the
Witness) — instantiation, not statement, carries the semantics. ⚠ Statement-fence note: this WEAKENS
what the abstract structure demands (deliberately — the demand moves to the real instance's
discharge); flagged for audit precisely because interface-weakening is how vacuity crept in before.
Mitigation: the non-vacuity + σ-separation gates (§5) are stated against the REAL instance, not the
interface.

**D3 — Hypothesis set** of the rebased capstone:
- `hSelfLoop : SelfLoopHNode n isSelfLoop` — the wild aggregate input (MC/PARI-true; the five
  refuted per-depth routes are documented in `SELFLOOP_GENERALK_WALL.md`). Vacuous on the R1 menu;
  stated now so the capstone statement is STABLE as `omMenu` grows in Phase B.
- `hExhaust` — replaces BOTH old `h_env` (false-shaped `q^{-N}` envelope — DROPPED) and the
  decided-vs-full-density identification. Scope decision: (a) keep clause (V2) with `hExhaust`
  [RECOMMENDED: the capstone then contains the full-theorem SHAPE honestly], or (b) drop clause
  (V2) and `hExhaust` entirely, claiming only the decided density (a smaller, fully-honest v2;
  full-density tie deferred to Phase B).
- `htameFE` — see D4. Old `h_decided_mono` is DROPPED as a hypothesis (provable: level-≥1 constancy
  on the current menu; becomes a per-extension obligation as the menu grows).

**D4 — The tame axiom CANNOT be mechanically retargeted (trusted-base decision).**
`realDensity_tame_functionalEquation` restated over the corrected sum would assert palindromy of a
PARTIAL monic decided density — FALSE in general (the current version is unfalsifiable only because
its sum ≡ 0; an axiom that is true-because-vacuous fails the non-vacuity leg of the faithfulness
discipline). The faithful Del Corso–Dvornicich statement needs the density to be the FULL projective
one: exhaustiveness at tame primes + the M1 monic→projective bridge.
*RECOMMENDED*: RETIRE the axiom in W4 (with the old capstone); v2 takes `htameFE` as an explicit
hypothesis — the capstone's `#print axioms` footprint becomes **Lean-core ONLY** (a net trusted-base
REDUCTION). The DCD cite returns in the Phase-B exhaustiveness/M1 wave, where it can be declared
faithfully. Alternative: re-declare now in guarded form (FE conditional on tame exhaustiveness) —
rejected by default: conditionals-on-open-hypotheses make poor axioms and the guard belongs in the
theorem, not the trusted base.

**D5 — σ-keying and its gates.** Menu := `omMenu n σ` (already σ-keyed by `unramType` matching;
`= sepShapesOf n σ` today). The Phase-B extension contract (documented in the capstone docstring):
menu growth must preserve (i) `typeOf T = σ` keying, (ii) per-shape `hNodeLimit` discharge or
`isSelfLoop` classification, (iii) cross-σ disjointness (feeds `box_partition`). O1-reversal gate:
prove as a Lean `example` that at n=2, q=3 the split type (λ=(1,1): value 1/9) and the inert type
(λ=(2): value 3/9) get DIFFERENT certified values, and a ramified σ gets 0 ≠ 1/4 at q=2 — the
certified function is genuinely σ-dependent.

---

## §4. Wave plan (each wave = green build + committed; leaf-first)

- **W0 (done)**: this blueprint. → Asvin sign-off on D1–D5.
- **W1 — the V2 spine (additive, no RealInstance changes):** `MontesAxiomV2.lean` (or a section in a
  new leaf module): `MontesDataV2` structure per D2; `DecompositionV2`: `countingDensity_eq_sum_coeff`,
  `countingDensity_isRational` (proofs: finite-sum of `C_isRational` + `stratum_tendsto_C` +
  `partition` + limit uniqueness — mirrors existing Decomposition with the abstraction doing the
  work); `Goal.goal_theorem_montes_v2` + `goal_theorem_via_montes_v2` (verbatim-modulo-names).
  Gate: old AxChk unchanged; new theorems core-only.
- **W2 — the real V2 instance:** `OM/RealInstanceV2.lean`: `realM2` (CountingModel fields per §1 —
  the genuinely new Lean work: menu disjointness, level-≥1 constancy ⟹ `decided_mono`,
  `upper_tail`), `realD2`, `realF2` (`density_nonneg` from menu nonnegativity), and
  `montes_unconditional_v2` + its discharged-legs corollary firing the Goal V2.
- **W3 — gates (mandatory, machine-checked):** (G1) non-vacuity: certified value = 1/4 > 0 at n=2
  inert, `realP = 2` (reuse `gate_rootCount_inert2`); (G2) σ-separation per D5; (G3) axiom census:
  `lake env lean LeanUrat/AxChk_baseline.lean` — v2 capstone core-only, ZERO regression on existing
  entries; (G4) falsifiability: re-run the `cells := []` mutation test against every new ∀-shape
  statement; (G5) transcription: `verification/` cross-check of `∑ omCount` per (n=2,3; q=2,3,5; σ)
  against `padic_types.py` separable-stratum closed forms (re-run of the 15/15 gate, now σ-sliced).
- **W4 — the swap (SEPARATE sign-off; statement-fence event):** rename v2 → `montes_unconditional`;
  old capstone + old-`MontesData` bridge + `realM/realD/realF` → `quarantine/` with tombstones;
  RETIRE `realDensity_tame_functionalEquation` (D4); update `AXIOM_FAITHFULNESS.md` (axiom removed),
  `SEMANTIC_AUDIT_LOG.md` (this rebase as an audit event), `PROJECT_STATE.md`, `AxChk_baseline.lean`.
- **Semantic-guardian audit** after W2 and after W4 (fresh-context verifier per the standing
  discipline; checklist: no smuggled palindromy/exhaustiveness, menu-disjointness not assumed,
  σ-keying not `if σ = σ₀`-shaped, V2 interface not satisfiable by the zero density AND the gates
  actually pinned to the real instance).

## §5. Risks / open items
- `realP = 2` stays hardwired in v2 (the general-prime order-0 twin already exists; general-prime
  v2 is a later additive step).
- `upper_tail` for `realM2` needs decided-stays-decided across levels for menu fibers — banked for
  the separable stratum; verify the N=0 edge in W2.
- `omCount` reads ONE config per node (`configsOf`) — fine for the R1 menu; multi-config nodes are a
  flagged Phase-B restatement (`OMCountV2.lean:65–69`).
- Clause (V2)/`hExhaust` interplay with `CountingModel.densityVal` semantics: `countingDensity` IS
  the decided limit by definition — the honest full-density claim needs a separate definition or the
  Phase-B drained classifier; W1 must keep these two densities typographically distinct.
