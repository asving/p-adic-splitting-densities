# SEMANTIC AUDIT LOG — lean_urat trusted base

**Baseline run: 2026-07-16.** Repo `/workspace-vast/asving/forum-sigma/lean_urat`, git HEAD
`82c5844` ("Add build #67: A (STRUCTURAL half)"). Auditor: SEMANTIC-AUDIT GUARDIAN (read-only).

Sole job: verify semantic faithfulness of every declared `axiom` + every load-bearing definition.
For each item: TRIPLE-CHECK = (1) STATEMENT-MAP both directions vs its cited GMN/Montes/Denef/DCD
claim, hunting over-generalization / quantifier over-reach; (2) MUTATION (would a wrong tweak still
typecheck; are the guards load-bearing); (3) NON-VACUITY (hypotheses satisfiable for the instance;
not a compiled `False`-witness, not a `rfl`/`0`-stub).

Verdict legend: **CLEAN** (faithful) · **SUSPECT** (scope worry or vacuous-until-upgraded) ·
**FALSE** (mis-ported / refutable as stated).

---

## ⚠ FLAGS — read first

Nothing FALSE was found in the trusted base at this HEAD. Two SUSPECT items, both already
self-documented in the source; no over-generalized `∀` past the paper scope was found.

- **SUSPECT — `classify_singleValued` (Classifier.lean:1690).** VACUOUS `rfl` PLACEHOLDER. Its body
  proves `xs.map g = xs.map g` (a reflexivity tautology, `X = X`), which carries **zero** of the
  cited GMN OM-tree uniqueness content. It is NOT `False` and does NOT poison the base (a tautology is
  sound), but the docstring advertises "the `classify` function COINCIDES with the mathematical OM
  tree (faithfulness)" — the statement delivers none of that. Known/expected state; remains SUSPECT
  until upgraded to a genuine single-valuedness statement. Load-bearing risk is bounded: it is cited
  as justifying `M8.shapeFiber_partition` disjointness, so any downstream fiber-disjointness that
  *names* this lemma is trusting a tautology. **Precise defect:** statement should assert canonicity /
  order-independence of the emitted cell list (e.g. permutation-invariance of `omStep` outputs, or
  functionhood of `classify`), NOT `l = l`.

- **SUSPECT (residual, benign) — `realDensity_tame_functionalEquation` (RealInstance.lean:485)**
  NON-VACUITY caveat, not scope error. The tame-prime binding `∀ q', q'.Prime → n < q' → …` is
  **correctly** guarded (see CLEAN verdict below); it does NOT read as all-primes. The residual worry
  is that, per its own docstring, for the CURRENT order-0 prototype the count-native tree-sum is
  degenerate (V1 leaf-cell vacuity), under which the axiom is satisfied trivially (the constant-`0`
  function is palindromic-rational). So the axiom is presently near-vacuous on the concrete instance —
  true, but not yet asserting the genuine §5 Del Corso–Dvornicich/Yin content. This is disclosed
  honestly in the docstring; recorded here so the baseline is explicit. Not FALSE, not over-general.

All other audited items: **CLEAN.**

---

# AXIOMS

### omReadValuation_lt_of_certLevel_fkeyed (Classifier.lean:1114) — CLEAN
*(2026-07-16 baseline)* — the ROOT CITE. Cites GMN Cor 4.19 / Thm 4.18 (`ind(f) ≤ v_p(disc f)`),
f-keyed + read-set restricted. STATEMENT: for a box `g : monicBox p (N+1) n`, under the bulk guard
`hbulk : zmodValuation p (N+1) g.discr < N`, it yields `GuardSuppR ∧ GuardSideR` — the RESTRICTED
guards quantified only over the hull-vertex abscissae (`hullDots`) and the side columns up to
`residualDeg S`. Both-directions: the Lean statement says NEITHER MORE (it is confined to the
read-set — `GuardSuppR`/`GuardSideR` over-quantify NOT over all `i ∈ support`/all `Side`×all `t`,
contrast the retired `GuardSupp`/`GuardSide`) NOR LESS (it does assert `< N` on every read dot) than
`ind ≤ v_p(disc)` specialized to what the OM reader touches. MUTATION: the `hbulk` guard is
load-bearing — drop it and `g = xⁿ + pᴺ` (disc valuation ≈ N, in the TAIL) refutes it, exactly the
counterexample that killed the earlier uniform `omReadValuation_lt_of_certLevel`. The threshold is the
box-native `zmodValuation p (N+1) g.discr` (mathlib `Polynomial.discr`, `ZMod (p^(N+1))`), NOT the
retired PadicInt `certLevel` — correct. NON-VACUITY: `hbulk` is satisfiable (any `g` with small disc
valuation, e.g. separable-mod-p boxes, is in the bulk); the conclusion is a genuine finite conjunction
of strict inequalities, not `True`. This is an accepted declared import; its STATEMENT is faithful and
the scope fix vs the false predecessor is intact.

### PadicMeasure.omCells (PadicMeasure.lean:268) — CLEAN
*(2026-07-16 baseline)* — AX-GMN-III cell partition, `(T : OMShape) → List (OMCell T)`. Cites GMN
§2.5 + Def 2.21 (one order-`r` cell per Newton face × residual stratum). STATEMENT-MAP: postulates
only the EXISTENCE of a finite cell list; asserts NO uniformity, NO rationality, NO volume — correct
for a structural interface axiom. The strong content is pushed into the DATA: `OMCell` carries
`hStratumDvd : stratum ∣ T.residual` and each `OMCell.Child` carries `hmult : 2 ≤ mult`,
`hdvd : factor^mult ∣ T.residual`, `hsize : node.size = mult` as fields (OMType.lean:186-234), so any
inhabitant is TYPE-LEVEL pinned to the real residual factorization (the D2/D3 anti-caricature fix);
`descend_children_of_factors` / `cell_stratum_of_residual` are then PROVED by projection, not axioms.
MUTATION: because the child witnesses are structure fields, one cannot smuggle a free non-factor child
past the type checker. NON-VACUITY: the empty list `[]` is a legal inhabitant, so the axiom is
trivially consistent (and `descend_size_lt` over it is vacuously true — sound). Faithful.

### PadicMeasure.descend (PadicMeasure.lean:272) — CLEAN
*(2026-07-16 baseline)* — AX-GMN-III descent list, `OMShape → List OMShape`. Cites GMN Cor 1.20/3.8 +
Lemma 3.11(3). STATEMENT: bare existence of a descent list; the docstring notes it is "kept for the
interface; not consumed by the recursion." No quantifier, no numeric claim. NON-VACUITY: any list
(incl. `[]`) inhabits it. Inert on the rationality path. Faithful and harmless.

### PadicMeasure.descend_size_lt (PadicMeasure.lean:278) — CLEAN
*(2026-07-16 baseline)* — AX-GMN-III strict size descent: `∀ T, ∀ c ∈ omCells T, ∀ ch ∈ c.children,
ch.node.size < T.size`. Cites GMN (mult-`≥2` factor of a degree-`d_r < e` residual ⇒ child size
`< e`). STATEMENT-MAP both directions: says exactly the well-foundedness input the OM induction needs
(strict `<`, not `≤` — correct, `<` is load-bearing for `InvImage.wf`). It is quantified over `omCells
T`'s children only (the honest scope), NOT over an arbitrary child forest. MUTATION: weaken `<` to `≤`
and the recursion's termination is lost — the guard is load-bearing. NON-VACUITY: satisfiable jointly
with `omCells := fun _ => []` (vacuous) and, more importantly, consistent with the concrete
`clusterMeasureModel` well-founded model. Faithful.

### PadicMeasure.clusterMeasure (PadicMeasure.lean:405) — CLEAN
*(2026-07-16 baseline)* — opaque `OMShape → ℕ → ℚ`. STATEMENT: asserts only that the symbol denotes a
FIXED `ℚ`-valued function; it is NOT a rationality/uniformity/value claim (the earlier free-`clusterMeasure`
+ free-`pivot` form that derived `False` is gone — cf. the AX_cellRecursion note). Its sole
mathematical content is supplied by AX_cellRecursion. NON-VACUITY: satisfiability is DEMONSTRATED by
`clusterMeasureModel` + `clusterMeasureModel_rec` (a concrete well-founded model on `OMShape.size`
satisfying the same recursion), so the pair is consistent, not a `False`-witness. Faithful.

### PadicMeasure.AX_cellRecursion (PadicMeasure.lean:438) — CLEAN
*(2026-07-16 baseline)* — THE Denef/Igusa measure wall. Cites Igusa *Local Zeta Functions* §7.4 /
Prop 7.4.1 + Denef Invent. Math. 77 (1984). STATEMENT: `clusterMeasure T q = (Σ_{c∈omCells T}
residualCountFn T c.residualDeg q · bb1Value c.polygon q · ∏_{ch} clusterMeasure ch.node q) /
omPivot T q`. Confirmed per the prompt's spec: it asserts ONLY the scalar MEASURE-FACTORIZATION
identity (a finite sum of `Nat.card`/Haar quantities over the cells, self-loop resummed by the fixed
`omPivot`), NOT ρ's rationality — the docstring is explicit ("STRUCTURAL measure-factorization
identity, NOT a rationality claim"), and rationality emerges only downstream via
`OMInduction.clusterVol_isRational`. Both-directions: neither side has a free function binder — it is
stated about the FIXED `clusterMeasure` and the FIXED concrete `omPivot`, so the historic
`False`-derivation (two different pivots forcing `1 = 1/2`) is structurally impossible. MUTATION: the
`/ omPivot T q` divisor and the `∏ children` (multi-child, recursive) shape are the faithful eq-(4.2)
form; dropping the pivot or flattening the product would change the identity. NON-VACUITY: the concrete
`clusterMeasureModel` satisfies the very same recursion (`clusterMeasureModel_rec`), and the certified
value is machine-checked STRICTLY POSITIVE on the inert-`n=2` instance
(`montes_order0_certified_value_pos`, `gate_rootCount_inert2`), so it is not the trivial `0 = 0/1`.
This is a legitimately recorded analytic-boundary axiom whose STATEMENT is faithful.

### OM.M9.realDensity_tame_functionalEquation (RealInstance.lean:485) — CLEAN (with residual NON-VACUITY caveat, see FLAGS)
*(2026-07-16 baseline)* — the H-tame CITE. Cites paper §5 / Del Corso–Dvornicich (2000) / Yin. STATEMENT:
`∃ num den : ℚ[X], den ≠ 0 ∧ (∀ q', q'.Prime → n < q' → Σ_{T∈shapesOf n σ σ} clusterCount
(M7.cellsOfShapeWF) M6.treeSize (…) T q' = num.eval q'/den.eval q') ∧ IsPalindromic num den`.
**The scope guard is the crux, and it is CORRECT:** the equality is quantified `q'.Prime ∧ n < q'`, i.e.
TAME primes `q > n` ONLY — it does NOT read as all primes. If it were stated at free `q`/all primes it
would be FALSE (bulk-ratio failure), and it is NOT. Both-directions: no free `F`/`cells`/`classify`/
`treeSize` binder (the retired global `tame_functionalEquation (F : DensityFoundation)` was FALSE-AS-
STATED via a `density := fun _ _ q => q` witness; this replacement pins every object to the real one),
so no legal instantiation decouples the two sides — passes the free-parameter falsifiability test.
`IsPalindromic` uses the faithful degree-robust encoding (Interface.lean:361, the ∀-x pointwise
`R(1/x) = R(x)` form), NOT the degree-blind coefficient-reverse encoding that was rejected in audit B1.
NON-VACUITY caveat (see FLAGS): on the current degenerate order-0 instance the tree-sum can collapse so
the existential is met by the constant-0 palindromic-rational — disclosed in the docstring; genuine §5
content lands once leaf cells are de-vacuified. Faithful as a scoped cite; not over-generalized.

---

# LOAD-BEARING DEFINITIONS

### classify (Classifier.lean:640) — CLEAN
*(2026-07-16 baseline)* — `fun N f => classifyAux p N n n f (rootCtx p N f) (clusterSize_rootCtx …)`.
Runs the budget recursion from the dispatch root `rootCtx`. For `0 < N` the root is the f-DEPENDENT
`fRootCtx` (genuine `Rr := rootResidual`, `Nr := rootFace` from `boxCoeffData`), so `classify` reflects
`f`'s Newton polygon + residual factorization; at `N=0` it falls back to the f-free `M9rootCtx` shell
(the trivial mod-1 box, never used downstream). Budget invariant `clusterSize (rootCtx …) = n` holds on
both branches. No over-reach; a genuine function of `f`. CLEAN.

### classifyAux (Classifier.lean:436) — CLEAN
*(2026-07-16 baseline)* — `Nat.strongRecOn` on the cluster-size budget; at each node emits the root
tuple `(order, clusterSize, dr)` and recurses over `omStep`'s cells' children with strictly-smaller
budget (`ch.hChildSizeLt`), serializing via `M5.encodeCells`. Payload-carrying (Phase-A A3): tree and
payload erase the SAME `M5.cells T` term. HONEST SCOPE (in docstring, verified): descent children
recurse through the f-BLIND `childCtxOfSize` (`Rr := 0`, always childless), so `classifyAux`/`classify`
are f-reading only at the ROOT; the genuine multi-level reader is `classifyGenuine` (built alongside,
swap deferred). This is disclosed, not hidden — the definition is faithful to what it claims (a truncated
OM recursion), with the stub-child limitation documented. CLEAN.

### classifyGenuine (Classifier.lean:742) / classifyGenuineAux (Classifier.lean:720) — CLEAN
*(2026-07-16 baseline)* — the genuine MULTI-LEVEL f-reading classifier. Peels the root via `fRootCtx`
then descends into `classifyGenuineAux`, which recurses at EVERY level through `fChildCtx`
(`Rr := childResidual`, a genuine function of `f`'s φ-adic development; `Fr := ZMod p` definitionally,
so `ch.P : (fChildCtx …).Fr[X]` is a real `(ZMod p)[X]` with no type transport). Strict descent by
`ch.hChildSizeLt` via `clusterSize_fChildCtx`. SCOPE (in docstring, verified): faithful only at ORDER
≤ 1 (single-slope tame tower, `Fr = ZMod p`); order ≥ 2 needs the residue-field-EXTENSION reader
(`childResidualExt`/`OrderTwoContext`, does not exist yet). NON-VACUITY: genuinely distinguished from
the stub — `classifyGenuineAux_head_dr_pos` (line 890) proves the ROOT TUPLE carries a nonzero `dr`
when `childResidual` has positive degree, and `cells_fChildCtx_ne_nil` (line 671) proves the child
produces genuine (non-empty) cells, contrasting the always-`[]` stub `childCtxOfSize`. Honest scope,
non-vacuous. CLEAN.

### classifyFirstDescent (Classifier.lean:654) — CLEAN
*(2026-07-16 baseline)* — the first-descent increment: root via `fRootCtx`, then ONE genuine descent
level through `fChildCtx` (develop `f` against the lifted key), then recurses via the (stubbed)
`classifyAux`. Reads `f` at the root + one level. Peeled explicitly (not baked into `classifyAux`)
because `OMType.Fr` is opaque and `ch.P` is only liftable when `T.Fr = ZMod p`, which holds
definitionally at the root — documented honestly. Faithful additive increment. CLEAN.

### classify_singleValued (Classifier.lean:1690) — SUSPECT
*(2026-07-16 baseline)* — **VACUOUS `rfl` PLACEHOLDER, confirmed.** Body: `(omStep … T).map (fun c =>
c.polygon) = (omStep … T).map (fun c => c.polygon)` proved by `rfl` — literally `l = l`. Cites GMN Thm
3.1/3.7/Cor 3.8/Lemma 3.11(3) and the docstring claims it establishes that `classify` COINCIDES with
the mathematical OM tree (uniqueness/canonicity). NON-VACUITY: FAILS — a reflexivity tautology carries
none of the cited content. Not `False` (tautologies are sound, base stays consistent), but it is a stub
masquerading as the faithfulness import. Precise defect: the statement must express canonicity /
order-independence of the cell list (or functionhood of `classify`), not `X = X`. SUSPECT until
upgraded, exactly as the known-state note anticipated.

### childResidual (Classifier.lean:295) — CLEAN
*(2026-07-16 baseline)* — `∑ t : Fin μ, C (zmodUnitResidue p N ((develop (liftKey p N ψ) μ f.1 t).coeff
0)) · X^t : (ZMod p)[X]`. The order-1 residual read off the φ-adic development of `f` against the lifted
key. STATEMENT-MAP: this IS GMN Def 2.21's residual polynomial at the develop-digit residue datum (GMN
Def 2.20) — certified by `ResidualBridge.childResidual_eq_residualPoly` (`childResidual = M4.residualPoly
(childDigitData …) S` under the honest index-reconciliation `residualDeg S + 1 = μ`). `develop` is a
GENUINE implementation (iterated `%ₘ`/`/ₘ` by the monic key, Development.lean:59), NOT a stub. Reduction-
stability (`childResidual_reduce_stable`) is PROVED core-only below an honest per-digit cutoff. SCOPE:
order-1 / `Fr = ZMod p` only, disclosed. NON-VACUITY: `cells_fChildCtx_ne_nil` witnesses positive-degree
residuals occur. Genuinely f-dependent, faithful. CLEAN.

### fChildCtx (Classifier.lean:368) — CLEAN
*(2026-07-16 baseline)* — the f-dependent child OMType: `order := r`, `Fr := ZMod p`, `cs := s`,
`Rr := if (childResidual …).natDegree ≤ s then childResidual … else 0`, `dr := Rr.natDegree`. The `≤ s`
guard discharges `hDrLeCs` and (per `rootResidual`'s analogous note) never fires for genuine residuals
within budget. STATEMENT-MAP: a genuine function of `f` (via `childResidual`), NOT the `Rr := 0` stub;
`clusterSize = s` by `rfl` threads the budget invariant. MUTATION: the guard is a budget-safety clamp,
not a faithfulness lever. NON-VACUITY: `cells_fChildCtx_ne_nil` (positive-degree residual ⇒ non-empty
cells) shows it is not the always-childless stub. Faithful. CLEAN.

### boxCoeffData (Classifier.lean:120) — CLEAN
*(2026-07-16 baseline)* — the ROOT residual datum `ℕ → ZMod p`: for column `t`, IF the coefficient's
box-native valuation lies exactly ON the side (`zmodValuation = v₀ + t·h`) then its `zmodUnitResidue`,
ELSE `0`. STATEMENT-MAP: this is GMN Def 2.20's `c_t` (unit part of the side coefficient, 0 off-side).
The on-side GUARD is LOAD-BEARING and was a genuine bug fix (D7, 2026-07-02): the previous
guard-free form took the unit residue unconditionally, misclassifying up to 44% of the generic stratum
(machine-checked counterexample `p=2, f=x²+2x+1`). MUTATION: drop the on-side `if` and the residual is
wrong (an above-side coefficient contributes its unit part instead of the correct 0). NON-VACUITY: the
guard is satisfiable on genuine side columns. Faithful, guard essential. CLEAN.

### rootResidual (Classifier.lean:175) — CLEAN
*(2026-07-16 baseline)* — the order-0 root residual `(ZMod p)[X]`: for the selected first finite-slope
side `S = rootSide`, `residualPoly (boxCoeffData p N S f) S` guarded to `natDegree ≤ n` (else 0). The
`≤ n` guard (weakened from `< n` in Phase-A A2) discharges `hDrLeCs : dr ≤ cs = n` and NEVER FIRES for
genuine residuals (`natDegree ≤ residualDeg S ≤ n`); the old strict `< n` guard ZEROED the generic
full-degree residual (the V1 vacuity chain) — this is the de-vacuifying fix, not a weakening of a live
claim. `rootResidual_natDegree_le` (proved, no axiom) discharges the size law. Faithful. CLEAN.

### M4.residualPoly (ResidualPolynomial.lean:74) / residualCoeff (:69) — CLEAN
*(2026-07-16 baseline)* — `residualPoly coeffData S = ∑_{t ∈ range (residualDeg S + 1)} C (residualCoeff
coeffData S t) · X^t`, with `residualCoeff coeffData S t = coeffData t` (pass-through). Cites GMN Def
2.20/2.21. STATEMENT-MAP: exactly the residual polynomial `R_S(f)(Y) = ∑_{t=0}^{d} c_t Y^t`. `residualDeg
S = S.length / S.e` matches `d = ℓ(S)/e_S`. Note (already documented, BUG-M4 fix): the endpoint lemmas
(`natDegree = residualDeg`, `≠ 0`) correctly REQUIRE `coeffData 0 ≠ 0 ∧ coeffData d ≠ 0` hypotheses —
because `coeffData` is a free opaque datum, without the vertex-unit guard `natDegree = residualDeg S`
would be UNPROVABLE / FALSE; threading them is the faithful fix (endpoints are Newton-polygon vertices ⇒
unit coeffs). `residualPoly_mul` (GMN Thm 2.26) correctly guards on the Cauchy convolution + per-factor
vanishing hypotheses. No over-reach. CLEAN.

### childResidualExt (ChildResidualExt.lean:213) — CLEAN
*(2026-07-16 baseline)* — the `resField[X]`-valued extension mirror of `childResidual`: `∑ t : Fin μ,
C (resUnitResidue ((developExt Φ μ h t).coeff 0)) · X^t`, over `resField = F_{p^{deg g}}`. STATEMENT-MAP:
degree bound `< μ` is proved (`childResidualExt_degree`), `= 0` at `μ=0`. HONEST SCOPE (docstring,
verified): `Φ` and `h` are ARBITRARY here — this file does NOT tie `Φ = liftKeyExt Ψ` nor `h` to a
base-changed `f`, and does NOT certify the output IS `f`'s order-`r` residual (OPEN TARGET B.2). So it is
well-formed machinery, NOT yet a faithfulness claim about `f`. Correctly scoped; makes no false coincidence
assertion. CLEAN (as scaffolding — carries no unearned faithfulness).

### LiftKeyExt.liftKeyExt (LiftKeyExt.lean:87) — CLEAN
*(2026-07-16 baseline)* — Lemma A key lift `resField[X] → O″[X]`: `X^{deg Ψ} + ∑_{i<deg Ψ} C (resSection
(Ψ.coeff i)) · X^i`, `resSection` a set-section (surjInv, right-inverse only — NOT a ring hom, NOT
Teichmüller-multiplicative, as documented). Monic (`liftKeyExt_monic`), degree-preserving
(`liftKeyExt_natDegree`), reduces correctly. STATEMENT-MAP: faithful extension analogue of
`Classifier.liftKey` over the surjInv section; the docstring is explicit that only the right-inverse
property is used (no unearned multiplicativity claim). CLEAN.

### DevelopmentExt.developExt (DevelopmentExt.lean:79) — CLEAN
*(2026-07-16 baseline)* — `= Development.develop Φ k h` over `O″ = Oring p N g` (definitional rename).
Digit degree bounds + reassembly transported from `Development`; residue-naturality
(`developExt_resHom_natural`) is a bare `Development.develop_map` instance. STATEMENT-MAP: purely a
named wrapper carrying intent; adds no content beyond the generic `develop`. The docstring is explicit it
is "scaffolding" and does NOT certify the reduced digits are `f`'s residual (OPEN TARGET B.2). CLEAN.

### ResidualBridge (childDigitData ResidualBridge.lean:110, Thms 1-3) — CLEAN
*(2026-07-16 baseline)* — reconciles the two readers: `childResidual = M4.residualPoly (childDigitData …)
S` for `residualDeg S + 1 = μ` (Thm 2), with the side-free core `childResidual = ∑_{t ∈ range μ} C
(childDigitData t) · X^t` (Thm 1, UNCONDITIONAL). STATEMENT-MAP: the single side hypothesis `residualDeg
S + 1 = μ` is the honest GMN degree identity `ℓ(S)/e_S + 1 = μ` and is NECESSARY (without it the sums
range over different index sets) — correctly threaded, not hidden. SCOPE (docstring, verified): order ≤ 1
only; the develop-digit-constant-term = side-coefficient geometry is flagged OPEN, not silently sorried.
Core-only. CLEAN.

### OrderTwoContext.fChildCtxExt (OrderTwoContext.lean:109) — CLEAN
*(2026-07-16 baseline)* — INTERFACE STUB, explicitly. Builds an `M5.OMType` with `Fr :=
UnramifiedBase.resField` (a genuine degree-`deg g` field extension of `ZMod p`), but `Rr := 0`,
`dr := 0` — content-free, reads NOTHING from `f`, EXACTLY like the old `childCtxOfSize` stub. STATEMENT-MAP:
the docstring is emphatic and accurate — it is NOT an order-2 reader; its ONE genuine content is
`card_Fr_fChildCtxExt : Nat.card Fr = p^{deg g}` (the extension field has the right cardinality), and
`δ := g.natDegree = finrank (ZMod p) Fr` is faithful to the finrank (an inflated `δ` would break
`hResidueDeg`). NON-VACUITY: constructible (all OMType obligations discharge). It makes NO faithfulness
claim it cannot back — the stub status is loud and correct. CLEAN.

---

## Methodology notes / residual risks for future runs

- The trusted base at this HEAD comprises **7 declared axioms** (1 root CITE + 5 PadicMeasure structural/
  measure + 1 tame CITE) and the audited **17 load-bearing defs**. The `#print axioms` census in
  `AxChk_baseline.lean` is the enforced trusted-base tripwire; every capstone there should footprint to
  `[propext, Classical.choice, Quot.sound]` plus (only where expected) the named CITE axioms.
- `develop` (Development.lean:59) is a genuine iterated-Euclidean-division implementation — the
  faithfulness of every child/root residual rests on it, and it is NOT a stub.
- The recurring failure mode (over-general `∀`) is ABSENT at this HEAD: the two historically-false axioms
  (uniform `omReadValuation_lt_of_certLevel`; global `tame_functionalEquation (F : …)`) are both retired
  and replaced by correctly-scoped f-keyed / pinned forms. `AX_columnMeasure` (the free-`cellVol`
  `0 = 1` defect) is likewise deleted, its content moved to the hypothesis-form `L4.cellVolume_eq`.
- Watch item for the next baseline: `classify_singleValued` upgrade (retire the `rfl`), and whether
  leaf-cell de-vacuification promotes `realDensity_tame_functionalEquation` from near-vacuous to the
  genuine §5 cite.

---

## REFRESH — 2026-07-16 (no change since HEAD `82c5844`, prior verdicts hold)

Light refresh run (SEMANTIC-AUDIT GUARDIAN, read-only). **HEAD unchanged** at `82c5844`
("Add build #67: A (STRUCTURAL half)") — identical to the baseline above. `git status -s`: the only
dirty path is untracked `notes/` (this log itself); **no tracked `.lean` file is modified**
(`git diff --name-only HEAD -- '*.lean'` empty). Therefore NO new or changed axioms / load-bearing
defs exist to re-audit. **0 new/changed items audited.**

Confirmations performed this refresh:

- **Axiom census re-run** (`grep -rn '^axiom ' LeanUrat/`): the trusted base is still exactly the
  **7 declared axioms** of the baseline — `omCells`, `descend`, `descend_size_lt`, `clusterMeasure`,
  `AX_cellRecursion` (PadicMeasure.lean 268/272/278/405/438), `omReadValuation_lt_of_certLevel_fkeyed`
  (Classifier.lean:1114), `realDensity_tame_functionalEquation` (RealInstance.lean:485). All other
  `^axiom ` grep hits (Goal.lean:149; PadicMeasure 135/251; FineCellResultant:43; LimitRecurrence:17;
  LevelNCount:1001 + `.lean.bak`:1013; SelfLoopCensusReduction:71; SparseResultant:59; and the
  `Classifier.lean.w3a.bak` copy) are mid-sentence prose uses of the word "axiom" inside comments or
  stale `.bak` backups, NOT live declarations. No axiom added or removed.

- **Standing SUSPECTs re-confirmed at their recorded source lines (no drift):**
  - `classify_singleValued` (Classifier.lean:1690) — STILL the vacuous `rfl` placeholder; body is
    literally `(omStep …).map (fun c => c.polygon) = (omStep …).map (fun c => c.polygon)` closed by
    `rfl` (line 1694). It is a `theorem` (correctly NOT in the axiom census), sound as a tautology but
    carrying none of the advertised GMN OM-tree canonicity. **SUSPECT stands, unchanged.**
  - `realDensity_tame_functionalEquation` (RealInstance.lean:485) — STILL the correctly-scoped tame-only
    form `∀ q', q'.Prime → n < q' → …` (NOT all-primes; the over-generalization failure mode is absent),
    with the benign order-0 near-vacuity disclosed in its own docstring (lines 483-484). **CLEAN with
    residual NON-VACUITY caveat stands, unchanged.**

- The recurring over-general-`∀` failure mode remains ABSENT (root CITE stays f-keyed + read-set
  restricted; tame CITE stays `q > n`-guarded). No new/changed load-bearing def, so
  `classify`/`classifyGenuine`/`childResidual`/`childResidualExt`/`boxCoeffData`/`rootResidual`/
  `M4.residualPoly`/`fChildCtx`/`OrderTwoContext`/`ResidualBridge` verdicts all carry over verbatim.

**Refresh verdict: no new or changed axioms; all prior verdicts (2 SUSPECT/caveat, remainder CLEAN)
hold. No new FLAGS.**

---

## REFRESH — 2026-07-16 (HEAD `ce2fbd4`, Stream-B wave-3 builds #66-#68 audited)

Full audit of the NEW-since-baseline Stream-B wave-3 files. HEAD moved `82c5844 → ce2fbd4`
("Add build #68: Stream B wave 3 — extension bridge B.2 + genuine ext context"). Auditor:
SEMANTIC-AUDIT GUARDIAN (read-only). **Axiom census unchanged** — `grep -rn '^axiom ' LeanUrat/`
still yields exactly the **7 declared axioms** of the baseline (omCells/descend/descend_size_lt/
clusterMeasure/AX_cellRecursion at PadicMeasure 268/272/278/405/438; omReadValuation_lt_of_certLevel_fkeyed
at Classifier.lean:1114; realDensity_tame_functionalEquation at RealInstance.lean:485). All other
`^axiom ` grep hits are mid-sentence prose or stale `.bak`/`.w3a.bak` copies, NOT live declarations.
No axiom added or removed. All baseline verdicts carry over verbatim.

### ⚠ FLAGS (wave-3) — read first

**Nothing FALSE, nothing over-generalized, nothing mis-ported.** One NON-VACUITY caveat (benign,
disclosed) recorded on the new extension subsystem, and the two standing baseline SUSPECTs unchanged.
The recurring failure modes the mandate warns about are ABSENT here:

- **NO over-claim of genuineness.** `childResidualExt_eq_residualPoly` (B.2) does NOT claim more than
  the #67 FORM certification — see CLEAN verdict below. It exhibits `childResidualExt` as
  `M4.residualPoly` at *its own* datum `childDigitDataExt`, NOT against an independent side-coefficient
  reader. The "genuine Def 2.20 residual" reading rests SQUARELY on the Asvin-confirmed 2026-07-16
  semantic fact (full-k_S-element = c_t), which every docstring attributes explicitly and honestly.
- **NO deg-ψ≥2 faithfulness on the ℤ/p reader.** No new lemma treats `childResidual` (ℤ/p) as
  faithful for deg ψ ≥ 2; the deg ψ ≥ 2 regime is correctly routed to `childResidualExt`. The
  confirmed rule is satisfied.
- **`fChildCtxExtR.Rr` is GENUINELY non-trivial (NOT the old `Rr:=0` stub collapse).** The guard is a
  budget clamp, not a zero-collapse — see below.

### Wave-3 NON-VACUITY caveat (benign, disclosed — recorded for the next baseline)

- **`ChildResidualExt.childResidualExt` / `OrderTwoContextR.fChildCtxExtR` — no positive-degree
  witness on a genuine `f`.** Unlike the ℤ/p `Classifier.fChildCtx` (which has
  `cells_fChildCtx_ne_nil` witnessing that a positive-degree residual actually OCCURS), the extension
  subsystem carries NO witness that `childResidualExt` is ever nonzero for a genuine base-changed `f`,
  because `Φ`/`h` are ARBITRARY (never tied to `liftKeyExt … Ψ` / a base-changed `f` — that is the
  wave-4 wiring, honestly deferred). So the faithfulness TIE, while non-vacuous as a `∑ C(·) X^t`-FORM
  identity (it holds for the reader against its own datum for ANY `Φ`,`h`), is not yet WITNESSED to
  carry positive-degree content on a real `f`. This is the exact same category as the baseline's
  `childResidualExt` "CLEAN as scaffolding — carries no unearned faithfulness" verdict, correctly
  inherited. Disclosed loudly in every wave-3 docstring (`Φ`,`h` arbitrary; wave-4 wires them). Not
  FALSE, not over-general, not vacuous-as-stated. Recorded so the boundary is explicit.

---

### childDigitDataExt (ResidualBridgeExt.lean:120) + _of_lt/_vanish_ge — CLEAN
*(2026-07-16, wave-3)* — `ℕ → resField` datum: `fun t => if t < μ then resUnitResidue ((developExt
Φ μ h ⟨t,·⟩).coeff 0) else 0`. The EXTENSION analogue of `ResidualBridge.childDigitData` (#67).
STATEMENT-MAP: this is a repackaging of the `childResidualExt` reader's own digit residues as an
`M4`-shaped coefficient datum — it is the reader's OWN data, NOT an independently-specified
side-coefficient datum. Per the confirmed semantic fact (full-`k_S`-element develop-digit reading IS
GMN Def 2.20's `c_t` for deg ψ ≥ 2), this is the genuine residual datum over `resField`. The `< μ`
guard + `vanish_ge` (`= 0` for `μ ≤ t`) are the honest support bound; `_of_lt` is a `dif_pos` unfold.
No over-reach. The `develop` under it is the genuine iterated-`%ₘ`/`/ₘ` implementation
(Development.lean:59), NOT a stub. CLEAN.

### childResidualExt_eq_range_sum (ResidualBridgeExt.lean:160) — Theorem 1, side-free core — CLEAN
*(2026-07-16, wave-3)* — `childResidualExt … = ∑ t ∈ range μ, C (childDigitDataExt t) · X^t`,
UNCONDITIONAL. STATEMENT-MAP: a pure `Fin μ → Finset.range μ` re-indexing of the reader against its
own datum (`Finset.sum_range` + termwise `childDigitDataExt_of_lt`). Verbatim the #67
`childResidual_eq_range_sum` argument over `resField` (a `CommRing`, so no field structure needed —
correctly stated as needing no `hgirr`). Says neither more nor less than "the reader IS its own
range-sum". NON-VACUITY: it is a genuine algebraic identity, not `True`/`rfl`-on-`X=X` (the RHS is a
different syntactic term reconciled by the sum lemma). CLEAN.

### childResidualExt_eq_residualPoly (ResidualBridgeExt.lean:200) — Theorem 2, THE EXTENSION BRIDGE (B.2) — CLEAN
*(2026-07-16, wave-3)* — **the gating result; the item the mandate flagged for the deepest scrutiny.**
Under `Fact (Irreducible ḡ)` + `Finite resField`, for a side `S` with `residualDeg S + 1 = μ`:
`childResidualExt … = M4.residualPoly (childDigitDataExt …) S` over `k_S = resField`. STATEMENT-MAP
BOTH DIRECTIONS: this is the FORM certification, EXACTLY the honest scope of #67's
`childResidual_eq_residualPoly`. It exhibits `childResidualExt` as `residualPoly` instantiated at
**its OWN** develop-digit datum `childDigitDataExt` — proof is `childResidualExt_eq_range_sum` +
`M4.residualPoly` unfold + `rw [hdeg]` (range μ = range (residualDeg S+1)) + `residualCoeff`
pass-through. It does **NOT** claim `childDigitDataExt` equals a `boxCoeffData`-style independent
side-coefficient datum — precisely the develop-digit ↔ side-coefficient identity that
`ChildResidualExt.lean`'s own Goal-3 note (lines 311-355) correctly identifies as ABSENT even at
order 0/1 and `M4.residualCoeff`'s docstring calls "opaque in the skeleton". So it neither
OVER-claims (the "genuine Def 2.20 residual for deg ψ ≥ 2" reading rests entirely and ONLY on the
Asvin-confirmed 2026-07-16 semantic fact — full-`k_S`-element = `c_t` — which the docstring attributes
explicitly, not on any smuggled Lean identity) nor UNDER-claims (the FORM identity is genuine, not a
tautology). INDEX HYPOTHESIS present + honest + load-bearing: `residualDeg S + 1 = μ` is the μ-analogue
`ℓ(S)/e_S + 1 = μ`, threaded (the `rw [hdeg]` at line 209 is exactly where the two ranges are
reconciled), NECESSARY — drop it and the sums range over different index sets. MUTATION: replace the
datum with an independent reader and the proof (which relies on the reader = its own datum) fails.
NON-VACUITY: the identity is a genuine range-reconciliation, not `rfl`-on-`X=X`; benign
positive-degree-witness caveat recorded under FLAGS (Φ,h arbitrary — same as baseline's scaffolding
verdict). This is the faithful extension analogue of the committed #67 bridge; it carries no unearned
genuineness beyond the confirm. CLEAN.

### childResidualExt_coeff (ResidualBridgeExt.lean:223) — Theorem 3 — CLEAN
*(2026-07-16, wave-3)* — `(childResidualExt …).coeff j = if j < μ then childDigitDataExt j else 0`,
UNCONDITIONAL. The `M4.residualPoly_coeff` analogue phrased directly on the reader; coefficient-wise
readout via `finsetSum_coeff` + `Finset.sum_ite_eq`. Faithful, no field structure needed. CLEAN.

### childResidualExt_natDegree_le (ResidualBridgeExt.lean:243) — CLEAN
*(2026-07-16, wave-3)* — under the index reconciliation, `natDegree ≤ residualDeg S`, inherited from
`M4.residualPoly_natDegree_le` through Theorem 2. A consistency corollary cross-checking against
`childResidualExt_natDegree_lt` (`< μ`), exactly as #67's `childResidual_natDegree_le`. CLEAN.

### OrderTwoContextR.fChildCtxExtR (OrderTwoContextR.lean:84) — CLEAN (with benign non-vacuity caveat, see FLAGS)
*(2026-07-16, wave-3)* — **THE de-stubbed extension context; the mandate's "is the genuine Rr actually
non-trivial or does a guard collapse it like the old Rr:=0 stub?" check.** `M5.OMType` with
`F0 := ZMod p`, `Fr := resField` (genuine card-`p^{deg g}` extension), `δ := g.natDegree`,
`Rr := if (childResidualExt …).natDegree ≤ s then childResidualExt … else 0`, `dr := Rr.natDegree`.
VERDICT ON THE COLLAPSE QUESTION: **the `Rr` is GENUINELY non-trivial — NOT the `Rr:=0` stub.** The
on-branch is the real `childResidualExt` (a `∑ C(resUnitResidue(develop-digit)) X^t` over the genuine
iterated-division `develop`, NOT a stub); the `≤ s` guard is a BUDGET-SAFETY CLAMP identical to
`Classifier.fChildCtx`'s, NOT a faithfulness lever and NOT a collapse-to-zero (it fires only when the
residual overruns the cluster-size budget, which never happens for genuine within-budget residuals).
This is a strict upgrade over the sibling `OrderTwoContext.fChildCtxExt` stub (`Rr := 0`, reads
nothing). MUTATION: the three OMType obligations discharge honestly — `hResidueDeg` from
`finrank_resField` (δ = finrank; an inflated δ would break it), `hResidualDeg` by `rfl`
(`dr := Rr.natDegree`), `hDrLeCs` from the `≤ s` guard (both branches). NON-VACUITY: constructible (all
obligations discharge); benign caveat (no positive-degree witness on a genuine `f` because Φ,h
arbitrary) recorded under FLAGS — inherited from `childResidualExt`'s scaffolding status, disclosed,
NOT a hidden vacuity. CLEAN.

### OrderTwoContextR.Rr_fChildCtxExtR_eq_residualPoly (OrderTwoContextR.lean:123) — CLEAN
*(2026-07-16, wave-3)* — the faithfulness TIE: when `natDegree ≤ s` (guard on-branch) and
`residualDeg S + 1 = μ`, `(fChildCtxExtR …).Rr = M4.residualPoly (childDigitDataExt …) S`, via the
B.2 bridge. STATEMENT-MAP: says exactly "the context's residual, on the guard's on-branch, is the
extension residualPoly FORM" — inherits precisely the FORM-certification scope of Theorem 2 (no more).
MUTATION: the proof's `show …if…then childResidualExt else 0…` + `rw [if_pos hle]` (lines 136-139)
PINS `Rr` to the genuine reader; revert to `Rr := 0` and the `if_pos` rewrite fails — so the tie is
load-bearing against the stub. NON-VACUITY: `clusterSize_fChildCtxExtR = s` by `rfl` (budget invariant
holds); the tie is the honest FORM identity, benign witness caveat as above. CLEAN.

### clusterSize_fChildCtxExtR (OrderTwoContextR.lean:111) — CLEAN
*(2026-07-16, wave-3)* — `clusterSize (fChildCtxExtR …) = s` by `rfl` (`cs := s`). Budget invariant,
matching `clusterSize_fChildCtx`/`clusterSize_fChildCtxExt`. CLEAN.

### Re-touch: ResidualBridge.lean (#67, order-1) — CLEAN (unchanged verdict, re-confirmed)
*(2026-07-16, wave-3)* — the ℤ/p `childResidual_eq_residualPoly` and siblings. Re-read in full: it is
the HONEST FORM certification at order ≤ 1 (`Fr = ZMod p`), scoped emphatically (docstring lines 62-82:
"ORDER ≤ 1 ONLY"; deg ψ ≥ 2 routed to `childResidualExt`). Exhibits `childResidual` as `residualPoly`
at its own `childDigitData` datum; explicitly flags the develop-digit ↔ side-coefficient geometry as
an OPEN sub-target (lines 79-82), NOT silently sorried. Index hypothesis `residualDeg S + 1 = μ`
present + necessary. The deg-ψ≥2 rule is honored. CLEAN.

### Re-touch: ChildResidualExt.lean (#66, canonicity/transport) — CLEAN (re-confirmed, upgraded content noted)
*(2026-07-16, wave-3)* — since the baseline verdict (CLEAN as scaffolding) this file GAINED wave-2
content, all CLEAN: `resUnitResidue_eq_of_witness` (canonicity for `x ≠ 0`, honest `x = 0` boundary
NOT claimed — genuinely non-canonical there, correctly excluded via the polygon guard);
`childResidualExt_transport` (the CERTLEVEL transport core, correctly abstracting the per-digit
`resUnitResidue`-compatibility as the hypothesis `hcompat` — no unearned reduce-stability claimed, the
concrete level-reduction hom honestly flagged as not-yet-built). Most important: the **Goal-3 OPEN
TARGET B.2 obstruction note** (lines 311-355) is a MODEL of honest scoping — it states precisely why a
naive faithfulness claim would be "either vacuous (pick coeffData := digit reader, rfl-true,
content-free) or unprovable (against an independently-specified coeffData, which does not exist)", and
that NO develop-digit ↔ side-coefficient bridge exists even at order 0/1. The wave-3 bridge
(ResidualBridgeExt Thm 2) lands EXACTLY the tractable FORM half this note describes, not the intractable
independent-datum half. `childResidualExt` itself remains the well-formed `resField[X]` function with
degree bound; genuine-reader status still honestly OPEN (wave-4 wiring). CLEAN.

### Re-touch: OrderTwoContext.fChildCtxExt (OrderTwoContext.lean:109, the STUB) — CLEAN (unchanged)
*(2026-07-16, wave-3)* — the `Rr := 0` INTERFACE STUB. Verdict carries over verbatim from baseline:
loud+accurate stub status, one genuine content `card_Fr_fChildCtxExt` (card `p^{deg g}`), δ faithful
to finrank. It is NOT edited by wave-3 (two-stream rule); `fChildCtxExtR` is the new-file upgrade
beside it. CLEAN.

---

**Wave-3 refresh verdict: 8 new load-bearing decls audited across 2 new files (ResidualBridgeExt,
OrderTwoContextR) + 2 re-touched (#66 ChildResidualExt gained wave-2 content, #67 ResidualBridge
unchanged). Axiom census UNCHANGED (7 axioms). ALL new/changed items CLEAN. Zero FALSE, zero
over-generalized, zero mis-ported, zero vacuous-as-stated. One benign NON-VACUITY caveat (no
positive-degree witness on a genuine `f` for the extension reader — Φ,h arbitrary, wave-4 wiring
deferred, disclosed everywhere) recorded, inherited from baseline scaffolding status. The B.2 bridge
is the honest FORM certification, its "genuine deg-ψ≥2 residual" reading resting explicitly on the
Asvin-confirmed 2026-07-16 semantic fact, exactly like #67 at order ≤ 1. The two standing baseline
SUSPECTs (classify_singleValued vacuous-rfl; realDensity_tame_functionalEquation benign order-0
non-vacuity) unchanged.**

---

## REFRESH — 2026-07-17 (HEAD `f55252b`, Stream-B wave-4 build #69 audited)

Deep audit of the NEW-since-#68 file `LeanUrat/OM/ClassifyGenuineExt.lean` (build #69, "Stream B
wave 4 — classifyGenuineExtAux, order-≥2 extension recursion, additive"). HEAD moved
`ce2fbd4 → f55252b`. Auditor: SEMANTIC-AUDIT GUARDIAN (read-only; Read/Grep only, no builds).

**Axiom census UNCHANGED.** `grep -rn '^axiom ' LeanUrat/` still yields exactly the **7 declared
axioms** of the baseline (`omCells`/`descend`/`descend_size_lt`/`clusterMeasure`/`AX_cellRecursion`
at PadicMeasure 268/272/278/405/438; `omReadValuation_lt_of_certLevel_fkeyed` at Classifier.lean:1114;
`realDensity_tame_functionalEquation` at RealInstance.lean:485). All other `^axiom ` hits are
mid-sentence prose or stale `.bak`/`.w3a.bak` copies, NOT live declarations. No axiom added/removed.
The single new/changed tracked `.lean` since #68 is `ClassifyGenuineExt.lean`
(`git diff --name-only ce2fbd4 f55252b -- '*.lean'` = that file alone; working tree clean of dirty
tracked `.lean`). No `sorry`/`native_decide`/`admit` in the file; `#print axioms` footprint block
present on all three built decls (lines 238-240).

### ⚠ FLAGS (wave-4) — read first

**NOTHING FALSE, nothing over-generalized, nothing mis-ported, nothing vacuous-as-stated.** The exact
mislabel the mandate warned about (the retired #57/#58 `…_tree_ne_leaf` / "descends past a leaf"
over-claim) DID NOT repeat — see the `_head_dr_pos` verdict. The confirmed deg-ψ≥2 rule (genuine
Def-2.20 residual = full `k_S`-element; ℤ/p `childResidual` NOT faithful for deg ψ ≥ 2) is HONORED:
this recursion routes the deg-≥2 regime through the EXTENSION reader `childResidualExt` over
`resField = F_{p^{deg g}}`, never the ℤ/p reader. One benign NON-VACUITY caveat (no positive-degree
witness on a genuine `f`, Φ/h arbitrary) carries over from the wave-3 scaffolding status — recorded,
disclosed in-source, NOT a defect.

### classifyGenuineExtAux (ClassifyGenuineExt.lean:125) — CLEAN
*(2026-07-17, wave-4)* — **the order-≥2 extension descent recursion; the mandate's deepest-scrutiny
target on the changing-field question.** `Nat.strongRecOn` on the cluster budget, motive
`fun _ : ℕ => (r : ℕ) → (Ψ : (resField p N g hN)[X]) → (μ : ℕ) → ClusterShape`. At each node: lift
`Ψ` to `Φ := liftKeyExt p N g hgm hN Ψ`, form `T := OrderTwoContextR.fChildCtxExtR p N g r b …Φ μ h`,
emit root tuple `(T.order, clusterSize T, T.dr) = (r, b, T.dr)`, and `flatMap` over `(cells T)`'s
children recursing on `ch.childSize < b` (via `clusterSize_fChildCtxExtR ▸ ch.hChildSizeLt`) with the
child's own `ch.P : T.Fr[X] = (resField p N g hN)[X]` at order `T.order + 1`.

(1) STATEMENT-MAP both directions. This is the FAITHFUL extension analogue of
`Classifier.classifyGenuineAux` (line 720): identical strongRecOn shape, identical emit-then-descend
body, with `fChildCtx`(ℤ/p)→`fChildCtxExtR`(ext), `ψ:(ZMod p)[X]`→`Ψ:(resField …)[X]`,
`clusterSize_fChildCtx`→`clusterSize_fChildCtxExtR`. **The residue field TRAVELS AS DATA, not in the
motive** — verified: `resField p N g hN` appears in the motive only as a closure CONSTANT
(`p N g hgm hN hgirr h` are outer `def` parameters captured in the closure), never bound or
transported across the recursion, so there is no `eqRec`-on-motive; every recursive call reads the
SAME fixed field type and `ch.P` threads with NO `▸`. This is genuinely non-trivial: the per-node
context is the REAL `fChildCtxExtR` whose `Rr := childResidualExt …` (guarded to budget) is the
`∑ C(resUnitResidue(develop-digit)) X^t` extension reader over the genuine iterated-division
`develop` — NOT a collapsed `Rr:=0` guard, NOT the stub `fChildCtxExt`. **Uses the EXTENSION reader,
correct for deg-≥2:** the recursion argument type is `(resField …)[X]` and the residual read is
`childResidualExt` (returns `(resField p N g hN)[X]`, `resField = AdjoinRoot (gbar …) = F_{p^{deg g}}`)
— the ℤ/p `childResidual` is nowhere on this path. **Boundary honestly disclosed:** a SINGLE fixed `g`
(one extension level) is threaded — `ch.P` is fed back over the SAME `resField p N g hN`, NOT a
per-child FURTHER extension `resField p N g' hN`; the genuine per-level-larger-field Montes crux is
loudly flagged OPEN (wave-5) in the docstring (lines 74-80, 119-124). So it claims the ext-tree SHAPE
with a genuine per-node reader over a fixed extension level, NEITHER MORE (no full faithful order-≥2
reader; no reduce-stability; no CITE) NOR LESS. (2) MUTATION: the `clusterSize_fChildCtxExtR ▸`
rewrite is load-bearing for `hlt : ch.childSize < b` (strict descent / well-foundedness); the guarded
`Rr` in `fChildCtxExtR` is what makes `T.dr` genuine. (3) NON-VACUITY: `strongRecOn` terminates via
genuine `hChildSizeLt`; the emitted tree is a genuine cons of the root tuple with the real descent,
not `[]`/`True`. Benign caveat: Φ,h arbitrary (no positive-degree witness on a genuine `f` — inherited
from `childResidualExt` scaffolding, wave-5 wiring). CLEAN.

### classifyGenuineExtAux_unfold (ClassifyGenuineExt.lean:147) — CLEAN
*(2026-07-17, wave-4)* — one-step unfold via `Nat.strongRecOn_eq` + triple `congrFun` (over `r`, `Ψ`,
`μ`). Verbatim mirror of `classifyGenuineAux_unfold` (line 754). STATEMENT-MAP: the RHS is exactly the
recursion body with the recursive `ih` replaced by `classifyGenuineExtAux …` at the child budget —
faithful βδ-unfold, the `let Φ`/`let T` bindings reproduced identically. NON-VACUITY: a genuine
equational rewrite, not `rfl`-on-`X=X`; the `▸ hlt` proof-term inside the body is erased on the
recursive-form RHS exactly as in the ℤ/p original. CLEAN.

### classifyGenuineExtAux_head (ClassifyGenuineExt.lean:183) — CLEAN
*(2026-07-17, wave-4)* — head-tuple / tree-SHAPE lemma: `(…).tree.head? = some (r, budget,
(fChildCtxExtR …).dr)`. Proof: `rw [classifyGenuineExtAux_unfold]; rfl`. STATEMENT-MAP both
directions: after unfold the tree is a `cons`, `head?` reads the root tuple; `T.order = r`
(`order := r`, OrderTwoContextR.lean:91) and `clusterSize T = budget` (`cs := s = budget`,
`clusterSize_fChildCtxExtR` by `rfl`) hold DEFINITIONALLY, so the `rfl` is honest — it reads back the
`(order, clusterSize, dr)` triple the context specifies, NEITHER MORE (no claim about the tail/descent)
NOR LESS. NON-VACUITY: `head?` of a genuine cons is `some (root tuple)`, not `none`; the third slot is
the genuine `(fChildCtxExtR …).dr`, not a hardcoded constant. CLEAN.

### classifyGenuineExtAux_head_dr_pos (ClassifyGenuineExt.lean:208) — CLEAN
*(2026-07-17, wave-4)* — **the NON-VACUITY item; the exact place the #57/#58 mislabel could recur.**
Statement: under `h0 : 0 < (childResidualExt … (liftKeyExt … Ψ) μ h).natDegree` and
`hle : (childResidualExt …).natDegree ≤ budget`, the emitted tree `≠ [(r, budget, 0)]`.

**VERDICT ON THE MISLABEL: the over-claim DID NOT repeat.** This is an HONEST dr-slot non-vacuity,
NOT an over-claim of "descends past a leaf" / `tree.length ≥ 2`. (1) STATEMENT-MAP both directions:
the claim is a SINGLETON-LEAF inequality `tree ≠ [(r, budget, 0)]`, discharged PURELY through the
head/dr-slot — proof reads `head?` (via `classifyGenuineExtAux_head`), assumes the leaf, and derives
`0 = (fChildCtxExtR …).dr`, then unfolds `dr = (if …≤budget then childResidualExt else 0).natDegree`
with `if_pos hle` to `(childResidualExt …).natDegree`, contradicting `h0` by `omega`. It says the
emitted tree DIFFERS FROM THE DEGENERATE `(r,budget,0)` LEAF IN THE dr-SLOT ALONE — exactly the
honestly-restated ℤ/p `classifyGenuineAux_head_dr_pos` (line 890, whose own docstring records it "was
misleadingly named/doc'd `…_tree_ne_leaf` / 'descends past a leaf'"). It does NOT claim tree.length ≥ 2,
does NOT claim the descent flatMap is non-empty — the docstring (lines 205-207) EXPLICITLY disclaims
this ("does NOT assert the descent flatMap is non-empty … a length-≥2 witness needs an extra
repeated-factor hypothesis and is future work"), matching the ℤ/p disclaimer verbatim. Note the RHS
uses literal `(r, budget, 0)` (vs the ℤ/p `((fChildCtx …).order, budget, 0)`) — same value since
`order := r` definitionally; equally honest. **Genuine, not a collapse:** the dr-slot that makes the
inequality bite is the EXTENSION residual degree `(childResidualExt …).natDegree` over
`resField = F_{p^{deg g}}` — the genuine deg-≥2 reader, NOT ℤ/p `childResidual`, so the confirmed rule
is honored; and it is contrasted precisely against the `Rr:=0` stub `OrderTwoContext.fChildCtxExt`
(whose `dr = 0`). (2) MUTATION: `hle` is load-bearing (drop it and the `if_pos` step fails, `dr` could
be the `else 0` branch); `h0` is load-bearing (without positive degree the trees could coincide);
weakening `≤` to `<` in the guard would not match `fChildCtxExtR`'s `≤ s` clamp — the guards are
faithful. (3) NON-VACUITY: `h0 ∧ hle` are JOINTLY satisfiable (a within-budget positive-degree
extension residual), so the hypotheses are not a compiled `False`; the conclusion is a genuine
`≠`, not `True`. Benign caveat (same as `childResidualExt`/`fChildCtxExtR` scaffolding): Φ,h arbitrary
⇒ the hypotheses are not yet WITNESSED on a genuine base-changed `f` (wave-5), disclosed in-source.
CLEAN.

**Wave-4 refresh verdict: 4 new decls audited in 1 new file (`ClassifyGenuineExt.lean`):
`classifyGenuineExtAux` (def) + `_unfold` + `_head` + `_head_dr_pos`. Axiom census UNCHANGED (7).
ALL new items CLEAN. Zero FALSE, zero over-generalized, zero mis-ported, zero vacuous-as-stated. The
recursion is the FAITHFUL extension analogue of `classifyGenuineAux` with the residue field threaded
as CLOSURE DATA (no eqRec-on-motive), using the EXTENSION reader `childResidualExt` over
`resField = F_{p^{deg g}}` for the deg-≥2 regime — the confirmed Def-2.20 rule is honored. The
changing-field crux (per-level larger `k_S`) is honestly OPEN (single fixed `g`, wave-5). Critically:
`classifyGenuineExtAux_head_dr_pos` is an HONEST dr-slot / `tree ≠ [(r,budget,0)]` non-vacuity, NOT a
repeat of the retired #57/#58 "descends past a leaf"/length-≥2 over-claim (explicitly disclaimed in
its docstring, matching the ℤ/p original). One benign NON-VACUITY caveat inherited (Φ,h arbitrary — no
positive-degree witness on a genuine `f`, wave-5 wiring deferred, disclosed everywhere). The two
standing baseline SUSPECTs (classify_singleValued vacuous-rfl; realDensity_tame_functionalEquation
benign order-0 non-vacuity) re-confirmed at their source lines, unchanged.**

---

## REFRESH — 2026-07-17 (HEAD `7c3cb10`, Stream-B wave-5 builds #70-#72 audited)

Deep audit of the THREE new-since-#69 additive-leaf files that build "wave 5" of the order-≥2 OM
reader over the unramified extension base — the level-drop subsystem. HEAD moved `f55252b → 7c3cb10`.
Auditor: SEMANTIC-FAITHFULNESS GUARDIAN (read-only; Read/Grep only, no builds, no git).
Files (per the mandate, the only tracked `.lean` changed since #69):
`LeanUrat/OM/LevelDrop.lean` (#70), `LeanUrat/OM/LevelDropResidue.lean` (#71),
`LeanUrat/OM/ChildResidualLevelDrop.lean` (#72).

**Axiom census UNCHANGED — trusted base identical to #69.** Independent re-confirmation:
`grep -rn '^axiom' ` over the three new files = **0 hits** (exit 1). The trusted base is therefore
still exactly the **7 declared axioms** of the baseline (`omCells`/`descend`/`descend_size_lt`/
`clusterMeasure`/`AX_cellRecursion` at PadicMeasure 268/272/278/405/438;
`omReadValuation_lt_of_certLevel_fkeyed` at Classifier.lean:1114;
`realDensity_tame_functionalEquation` at RealInstance.lean:485). **PRIOR-LOGGED-CLEAN AXIOMS AND
DEFS NOT RE-VERIFIED** (per mandate): the 7 axioms above and the previously-audited load-bearing defs
(classify/classifyGenuine/childResidual/childResidualExt/boxCoeffData/rootResidual/M4.residualPoly/
fChildCtx/OrderTwoContext(R)/ResidualBridge(Ext)/classifyGenuineExtAux family) all carry over verbatim
— no grep showed any of them changed. `sorry`/`admit`/`native_decide` grep over the three files = only
docstring-prose mentions of the "no sorry" discipline, ZERO live tactic uses. `#print axioms` footprint
block present on all decls (LevelDrop 170-177; LevelDropResidue 193; ChildResidualLevelDrop 75).

### ⚠ FLAGS (wave-5) — read first

**NOTHING FALSE, nothing over-generalized, nothing mis-ported, nothing vacuous-as-stated. Empty flag
list.** The exact recurring failure mode the mandate warns about — an over-general `∀` past the
construction's scope (the false uniform `omReadValuation`; the universal descent CITE refuted by
`g=X²+X+pᴺ`) — is ABSENT: these three files declare NO CITE at all (they are the CITE-FREE glue), and
the one universally-quantified hypothesis (`hcuts : ∀ t : Fin μ, …`) ranges over EXACTLY the μ
develop-digits of the given Φ,h (the reader's own read-set), NOT over all keys. The
sibling-repo scope note (`uniform-rationality/notes/ORDER2_CITE_INTERPRETATION_2026-07-17.md`) was
cross-checked and independently corroborates every semantic finding below (arising-key scope;
source-level `< N` cutoff non-vacuity; `p^M=0`-vacuity avoided by the two-level split).

### levelDropCoeff (LevelDrop.lean:55) — CLEAN
*(2026-07-17, wave-5)* — `ZMod (p^(N+1)) →+* ZMod (p^N)`. STATEMENT-MAP: it is EXACTLY the mandated
canonical `ZMod.castHom (pow_dvd_pow p (Nat.le_succ N)) (ZMod (p^N))` — the modulus-reduction ring
hom, same idiom as `UnramifiedBase.redHom`/`Classifier.coeffReduce`. Neither more nor less. CLEAN.

### levelDropHom (LevelDrop.lean:76) + eval₂_g'_root_g / levelDropHom_mk / levelDropHom_root — CLEAN
*(2026-07-17, wave-5)* — the induced level-drop hom `AdjoinRoot g' →+* AdjoinRoot g`. Built as
`AdjoinRoot.lift ((AdjoinRoot.of g).comp (levelDropCoeff)) (root g) (eval₂_g'_root_g …)`, i.e.
base-reduce-along-`levelDropCoeff` + root↦root. **Compatibility hypothesis present + correct:**
`hgg : g'.map (levelDropCoeff p N) = g` is threaded everywhere; without it the `AdjoinRoot.lift`
well-definedness (`eval₂_g'_root_g`, proved via `eval₂_map` + `hgg` + `eval₂_root`) fails — so `hgg`
is genuinely load-bearing, not decorative. `levelDropHom_mk` (`mk g' q ↦ mk g (q.map levelDropCoeff)`)
and `levelDropHom_root` (`root g' ↦ root g`) confirm it genuinely reduces coefficients mod `p^N` and
sends root↦root — the mandated faithfulness checks pass. NON-VACUITY: `hgg` is satisfiable (any monic
`g'` with `g := g'.map levelDropCoeff`). Faithful mirror of `UnramifiedBase.resHom`. CLEAN.

### gbar_levelDrop (LevelDrop.lean:101) — CLEAN
*(2026-07-17, wave-5)* — `ḡ' = ḡ` (both `= g' mod p`). STATEMENT-MAP: proved by
`ZMod.castHom_comp` — the level-`N+1→N` reduction then mod-`p` equals the direct mod-`p` reduction
(`redHom (N+1) = (redHom N) ∘ levelDropCoeff`), under `hgg`. This is the genuine composition-of-casts
identity, the correct compatibility for the residue-field hom to be natural. CLEAN.

### levelDropResHom (LevelDrop.lean:124) + eval₂_gbar'_root_gbar / levelDropResHom_mk — CLEAN
*(2026-07-17, wave-5)* — `resField (N+1) →+* resField N`. Built as the natural `AdjoinRoot.lift` given
`ḡ' = ḡ` (step 4): base `id : ZMod p → ZMod p`, root↦root. `levelDropResHom_mk` (`mk ḡ' r ↦ mk ḡ r`)
confirms the base map is identity on `ZMod p`. Faithful "the natural map given ḡ'=ḡ", exactly as
intended. CLEAN.

### resHom_natural_levelDrop (LevelDrop.lean:143) — CLEAN
*(2026-07-17, wave-5)* — the naturality square `resHom_N ∘ levelDropHom = levelDropResHom ∘ resHom_{N+1}`.
STATEMENT-MAP both directions: a genuine `RingHom.ext` commuting square — reduced on `mk g' q`
generators via `levelDropHom_mk`/`resHom_mk`/`levelDropResHom_mk`, then the two coefficient maps are
reconciled by `Polynomial.map_map` + `ZMod.castHom_comp` (`(redHom N) ∘ (levelDropCoeff) = redHom (N+1)`).
**NOT trivially true:** the `congr 1` + `castHom_comp` step is exactly where the square's content lives
(the two paths `q.map(levelDropCoeff).map(redHom_N)` vs `q.map(redHom_{N+1})` genuinely coincide by the
cast-composition, not by `rfl`). NON-VACUITY: the two composites are DIFFERENT syntactic terms
reconciled by a real algebraic identity. CLEAN.

### resUnitResidue_levelDrop (LevelDropResidue.lean:64) — CLEAN — **the mandate's KEY-CHECK item**
*(2026-07-17, wave-5)* — `resUnitResidue_N(θ x) = φ(resUnitResidue_{N+1} x)` GIVEN
`hcut : pval_Oring p (N+1) g' x < N`. All three mandated key checks PASS:

**(i) The cutoff is at the SOURCE level `N+1` and is genuinely NON-VACUOUS.** `hcut` reads
`pval_Oring p (N+1) g' x < N` — the valuation at the SOURCE ring `Oring(p,N+1,g')`. Verified against
`UnramifiedBase.pval_Oring` (`findGreatest (…) N`, i.e. capped at the modulus) and
`ChildResidualExt.pval_eq_N_iff` (`pval_M x = M ↔ x = 0`): at level `M = N+1`, a NONZERO `x` has
`pval ∈ {0,…,N}`, so `pval = N` IS ATTAINED by nonzero elements (e.g. `p^N`, nonzero since `p^{N+1}=0`
but `p^N≠0` at level `N+1`). Hence `hcut : pval < N` is STRICTLY STRONGER than `x ≠ 0` (which would
only give `pval ≤ N`), and it excludes exactly the boundary `pval = N` nonzero digits — precisely the
ones `θ` sends to `0`. NOT vacuous, NOT automatic. This is the corrected two-level insight (the naive
"`pval < M` is automatic over `ZMod(p^M)[X]/(g)`" trap is AVOIDED by reading the cutoff at the source
level while the drop targets level `N`), independently confirmed in the sibling scope note.

**(ii) The extra hypotheses are honest standing data, NOT a vacuity/smuggling device.** `hgirr :
Irreducible (gbar p (N+1) g' h1)` is needed so `resField` is a genuine `Field` (⇒ `φ = levelDropResHom`
is injective as a nonzero field hom — used at line 130-133 `RingHom.injective φ`; irreducibility at
level `N` is DERIVED, not assumed, via `gbar_levelDrop`, line 84-85). The `IsLocalRing` instances +
`hm' : 0 < g'.natDegree` are what `mem_span_p_of_mul_p_pow_eq_zero` / `p_pow_ne_zero_of_lt` /
`resUnitResidue_eq_of_witness` genuinely require (they establish `p^v ≠ 0` for `v < N` at level `N`, and
canonicity of the reader). The target statement is meaningless without them (no field ⇒ no residue
reader). They do NOT narrow the scope vacuously — they are satisfiable for the real instance (any
unramified base with irreducible reduced key).

**(iii) MUTATION — `hcut` is load-bearing; `< N` cannot weaken to `≤ N` nor be dropped.** `hcut` feeds
TWO places: (a) `hx : x ≠ 0` (via `pval < N` and `pval_zero = N`), and — decisively — (b) line 165,
passed as the `hv : v < N` argument to `mem_span_p_of_mul_p_pow_eq_zero` in the crux step
`pval_N(θ x) = v`. That lemma needs `v < N` so that `p^v ≠ 0` at the TARGET level `N`
(`p_pow_ne_zero_of_lt`). Flip `< N → ≤ N`: since `pval ≤ N` is the always-true junk bound
(`pval_le`), the hypothesis becomes vacuous AND the `p_pow_ne_zero_of_lt hj` call (needs `v < N`) fails
— the crux `pval(θx)=v` collapses (at `v=N`, `p^N=0` at level `N`, so `θx=θu·p^N=0` and the residue is
uncontrolled). Drop `hcut` entirely: `x ≠ 0` alone gives only `v ≤ N` at the source, insufficient. So
the guard is faithful and essential. NON-VACUITY: `hcut ∧ (all standing data)` jointly satisfiable —
not a compiled `False`; conclusion is a genuine residue-field equation. **This is the faithful
extension analogue of the order-≤1 `PadicLift.zmodUnitResidue_reduce_stable`.** CLEAN.

### childResidualExt_reduce_stable_of_cuts (ChildResidualLevelDrop.lean:50) — CLEAN — **the mandate's KEY-CHECK item**
*(2026-07-17, wave-5)* — order-≥2 reduce-stability GIVEN the per-digit cutoffs. All three mandated key
checks PASS:

**(i) Conclusion is the GENUINE reduce-stability, not a weakened identity.**
`childResidualExt_N (Φ.map θ) μ (h.map θ) = (childResidualExt_{N+1} Φ μ h).map φ` — verbatim the
level-drop-stability of the extension child residual (`θ = levelDropHom`, `φ = levelDropResHom`). This
is a direct instance of the wave-2 `ChildResidualExt.childResidualExt_transport` (whose statement was
re-read and confirmed: it transports `childResidualExt` along ANY base ring hom `θ` + residue hom `φ`
given the per-digit `hcompat`). NEITHER MORE NOR LESS.

**(ii) `hcuts` quantifies over EXACTLY the right read-set.** `hcuts : ∀ t : Fin μ, pval_{N+1}
((developExt p (N+1) g' Φ μ h t).coeff 0) < N`. Cross-checked against `childResidualExt`'s own
definition (ChildResidualExt.lean:213-217): the reader reads `resUnitResidue ((developExt … Φ μ h t)
.coeff 0)` for `t : Fin μ` — the SAME `μ` develop-digits of THIS Φ against THIS h. So `hcuts` quantifies
over neither MORE (not `∀`-over-all-keys — that universal form is the one REFUTED by `g=X²+X+pᴺ` in the
sibling note; it is emphatically NOT what appears here) nor LESS (all `μ` digits are covered; the
transport discharges `hcompat t` termwise at line 67 via `resUnitResidue_levelDrop … _ (hcuts t)`,
feeding digit `t`'s cutoff to digit `t`). Correct read-set.

**(iii) It is a THEOREM, and `hcuts` is the HONEST stand-in for the future CITE.** Confirmed a
`theorem` (grep: zero axioms in the file), so `hcuts` is a HYPOTHESIS — it cannot be a false axiom; the
file reduces order-≥2 reduce-stability to precisely this single scalar input with no other assumption.
`hcuts` is the ARISING-KEY-restricted, source-level `< N` per-digit form — matching the sibling scope
note's determination that the CITE is arising-key-restricted (option (b)), NOT the universal ∀-over-all-
keys form (option (a), refuted). The file is CITE-FREE glue; the CITE proper (piece 2b,
`childResidualExt_reduce_stable_fkeyed`) is honestly deferred to wave-5-final, to be declared against
real objects (Φ = liftKeyExt ψ, μ≥2, hbulk : v_p(disc f) < N) — NOT declared here. NON-VACUITY: the
same benign scaffolding caveat as all wave-1..4 ext decls (Φ,h arbitrary ⇒ `hcuts` not yet WITNESSED on
a genuine base-changed `f`), disclosed in the docstring; the identity itself is a genuine transport, not
`rfl`-on-`X=X`. CLEAN.

**Wave-5 refresh verdict: 8 new load-bearing decls audited across 3 new files (LevelDrop:
levelDropCoeff/levelDropHom(+mk/root)/gbar_levelDrop/levelDropResHom(+mk)/resHom_natural_levelDrop;
LevelDropResidue: resUnitResidue_levelDrop; ChildResidualLevelDrop:
childResidualExt_reduce_stable_of_cuts). Axiom census UNCHANGED (7 axioms; ZERO new axioms in the three
files, independently re-confirmed by grep). ALL new items CLEAN. Zero FALSE, zero over-generalized,
zero mis-ported, zero vacuous-as-stated — EMPTY FLAG LIST. The two mandate KEY-CHECK items both pass in
full: (#71) the `hcut : pval < N` cutoff is at the SOURCE level `N+1`, genuinely non-vacuous (excludes
the boundary `pval=N` nonzero digit that `pval_eq_N_iff` shows a nonzero level-`N+1` element can
attain), and load-bearing (mutation `< N → ≤ N` or dropping it breaks the crux `pval(θx)=v` via
`p_pow_ne_zero_of_lt`); (#72) `childResidualExt_reduce_stable_of_cuts` is the GENUINE reduce-stability
(direct `childResidualExt_transport` instance), `hcuts` quantifies over EXACTLY the μ develop-digits of
THIS Φ,h (not all keys — the universal form refuted by `g=X²+X+pᴺ` is absent), and it is a THEOREM
(`hcuts` a hypothesis, not a false axiom; the honest arising-key stand-in for the deferred CITE).
Cross-checked against `uniform-rationality/notes/ORDER2_CITE_INTERPRETATION_2026-07-17.md` — every
finding corroborated. The two standing baseline SUSPECTs (classify_singleValued vacuous-rfl;
realDensity_tame_functionalEquation benign order-0 non-vacuity) unchanged; prior CLEAN axioms/defs not
re-verified (base unchanged), verdicts carry over.**

---

## 2026-07-19/21 — M9-rebase V2 chain audit + the W4a axiom retirement

**Fresh-context guardian audit of the V2 chain (2026-07-19)** — `MontesV2.lean`,
`OM/RealInstanceV2Prep.lean`, `OM/RealInstanceV2.lean` (design: `notes/M9_REBASE_BLUEPRINT_2026-07-19.md`).
Ten-item checklist, verdict: **zero CRITICAL ERROR, 9/10 immediate PASS, one JUSTIFICATION GAP closed
same day.** Highlights: palindromy enters ONLY via the `htameFE` hypothesis (L7 transfer requires it,
never manufactures it); σ-keying is genuine (`omMenu → sepShapesOf → unramType` filter; no `if σ = σ₀`
anywhere; cross-σ disjointness PROVED via `eq_of_mem_sepShapesOf`); every `realM2` CountingModel field
discharge is semantically faithful (decidedCount traced to genuine `Nat.card` classifier fibers over the
M1 box; undecided = honest remainder with the disjoint-fiber box bound carrying the content;
`decided_tendsto` limit = the engine value via the PROVED `h_node0` legs); capstone conclusion fully
pinned to concrete objects (no free fields — the D2 deliberately-weak `MontesDataV2` interface cannot
leak into it); bracket-uniqueness clause non-circular. THE GAP (item 2): `htameFE` non-triviality was
certified only at the wild prime 2; closed by `gate_v2_htameFE_nontrivial` (density = 1/3 > 0 at the
TAME prime 3, n = 2 inert), excluding the vacuous `num = 0` discharge. Gates at close: value 1/4
through the real instance (V1 reversed), split 1/9 ≠ inert 1/3 at q'=3 (O1 reversed), ramified menu
honestly empty, `C := 0` mutation refuses to compile, census 14 entries all core-only with byte-identical
zero regression, Python brute force 21/21 exact (p ∈ {2,3,5}, n ∈ {2,3}, incl. correctly-empty strata).

**W4a (2026-07-21): `realDensity_tame_functionalEquation` RETIRED — the standing baseline SUSPECT is
RESOLVED by removal.** The 2026-07-16 baseline flagged this axiom SUSPECT (benign): true-but-near-vacuous
on the degenerate instance (constant-0 density satisfies it trivially). The rebase established the axiom
CANNOT be mechanically retargeted to the corrected σ-keyed density (that sum is a PARTIAL monic decided
density — palindromy is false in general; the faithful Del Corso–Dvornicich statement needs
exhaustiveness + the M1 projective bridge). Per signed-off D4 the axiom was deleted with the old chain
(quarantine/RealInstance_oldCapstone_2026-07-21.lean.txt); the tame FE is now the explicit capstone
hypothesis `htameFE`, machine-certified non-trivial for the real instance. Trusted base: ONE FEWER
axiom; the canonical capstone `OM.RealInstanceV2.montes_unconditional` prints
`[propext, Classical.choice, Quot.sound]`. The DCD cite returns at Phase B where it can be declared
faithfully. (Standing SUSPECT #1, `classify_singleValued` vacuous-rfl, is unchanged by this wave.)

---

## 2026-07-21 — Wild Wave 1 audit (fresh context): PASS 8/8, no flags

Modules: `OM/WildMenu.lean`, `OM/WildMenuPrep.lean`, `OM/RealInstanceW.lean`,
`OM/RealInstanceWGates.lean` (design `notes/WILD_WAVE1_BLUEPRINT_2026-07-21.md`). All 8 checklist
items PASS: σ-keying structural (head-tree invariant `dr = fSum σ < n` vs `dr = n`; no `if σ = σ₀`;
`n/(n/e) = e` genuinely discharged via `constERam_fSum_dvd`); docstrings honestly scope every wild
value as the MINIMAL-H stratum leading term (never the H-tower sum or the full type density);
`upper_tail` non-circular (per-σ increment ≤ total increment ≤ undecided, `Tot ≤ 1` from the
independent disjoint-fiber box bound); `omCount_eq_mul_all` a sound membership-free generalization
(`configsOf` is definitionally a singleton for every shape; the dropped hypotheses were
introduced-and-discarded in the original); wild counting legs route through the banked
`hnode_selfloop_over_Bclassify_R` via a faithfully-constructed `SelfLoopWitness`; gate values 1/8,
0, 1/256 rest on genuine pool combinatorics (`shapeCount_split_two = 0` is the C(1,2)=0 pattern,
machine-checked emptiness); census 18 W1 entries all core-only, V2 capstones unchanged; capstone
statements verbatim-modulo-menu. Python brute-force cross-check exact on all anchors.

**Standing follow-up (= Wild Wave 2):** the σ-keying is definitional; the semantic faithfulness
claim ("fiber members' true ℚ_p factorization type is σ") awaits the `om_tree_unique` Montes-paper
axiom + faithfulness theorem, per the standing directive (wild uniformity conditional on the Montes
paper).

---

## 2026-07-21 — Wild Wave 2: `om_leaf_faithful` DECLARED (the Montes-paper types↔factors import)

New axiom `OM/OmLeafFaithful.om_leaf_faithful` per the standing directive (wild uniformity
conditional on the Montes paper) and `notes/WILD_WAVE2_BLUEPRINT_2026-07-21.md`. Content: for monic
`f : ℤ_[p][X]` that the level-N classifier sends to a shape `T ∈ omMenuW n σ`, there EXISTS a
`QpFactorization` (monic ℚ_p-irreducible factors, each with a `LocalFactorData` bundle carrying its
genuine mathlib `ramificationIdx`/`inertiaDeg`) whose induced (e,f)-multiset is σ. Cite: GMN Thm
1.15/1.19 + Cor 1.20 (+ Def 3.10/eq.(37)) jointly with the Serre-standard local-field structure the
paper presupposes (DVR-ness of the integers of finite L/ℚ_p — unprovable at the mathlib pin; this
existence is exactly what the axiom carries). Menu-fiber-scoped (arising-shape house form);
existence-only; no uniformity/rationality/measure/density term; drainage and equidistribution
remain deliberate NON-imports.

Safety evidence at declaration (all machine-checked, on record in the module):
- **Non-vacuity of the bundle type**: degree-1 witness (`L = ℚ_p`, `𝒪 = ℤ_p`) with (e,f) = (1,1)
  PROVED (`QpType.trivialFactorData`).
- **Axiom-free coherence layer**: the wild gate fiber (classify = Tselfloop, n=2) is PROVED
  ℚ_p-irreducible with NO axiom (fiber ⟹ Eisenstein ⟹ irreducible; `wildGateFiber_eisenstein`).
- **Mutation probe**: the split-type mutated variant + the concrete fiber witness
  (`X² + 2X + 2` at N=3, via the banked `gate_S2C1`) derives `False` (scratch compiled, recorded,
  deleted) — the (e,f) content of the conclusion is load-bearing, not decorative.
- **Footprint containment**: census re-prints confirm both density capstones
  (`montes_unconditional`, `montes_unconditional_w`) remain `[propext, Classical.choice,
  Quot.sound]`; the axiom enters exactly the faithfulness cones (`menuFiber_hasType`,
  `gateFiber_hasType`, `gate_axiom_coherent` = core + `om_leaf_faithful`).
- Pre-declaration truth-scope check (module header): the minimal `0 < N` guard is sound — a
  nonempty menu fiber forces `fSum σ < N` (support-dot valuations < N), the range where the banked
  fiber characterizations exhibit the genuine stratum; below threshold the instance is vacuous.

Guardian audit: PENDING (this entry records the declaration; the fresh-context audit verdict is
appended separately and gates the push).

**Guardian audit verdict (2026-07-21, fresh context): ACCEPT-WITH-FLAGS — push cleared.**
Triple test: STATEMENT-MAP PASS both directions (bundle demands exactly the GMN+Serre package;
both menu branches' (e,f)-multisets faithful — order-0 via Hensel/Thm 1.15, wild via Cor 1.20 with
the right-vertex forcing deg φ = 1; no smuggled uniformity/rationality/measure/uniqueness; the
`0 < N`-only guard PROVABLY sound — `stratumCount_ramShape_smallN` closes the small-N wild hole,
`classify_eq_sepShape_iff` covers order-0 at every level). MUTATION PASS (probe genuine; refutation
cone free of the real axiom; `hT` confirmed load-bearing — dropping it makes the axiom blatantly
false, as intended). NON-VACUITY PASS (gate fiber inhabited by the concrete `X²+2X+2`; order-0 leg
inhabited; conclusion type inhabited; core-only capstone containment STRUCTURAL — no module imports
OmLeafFaithful except the census).
FLAGS on record: (1) fine-(e,f) swap ({(1,2)} vs {(2,1)}) not yet machine-refutable — value is
math-forced by the proved Eisenstein condition but catching the mutation needs an axiom-free
`eOf = deg` for Eisenstein bundles (the named follow-up); (2) mutation coverage is n=2-gate-local;
general constant-e σ and the order-0 branch are cite-trusted; (3) `LocalFactorData` omits
`eOf·fOf = finrank` — existence-only conclusion ⟹ no soundness exposure.

**FLAG 1 CLOSED (2026-07-21, same day): `OM/QpTypeEisenstein.lean`.** Axiom-free
`ef_of_eisenstein`: for monic Eisenstein `g` and ANY `LocalFactorData p g`, `eOf = g.natDegree ∧
fOf = 1` — full equality on both coordinates (route: root descends to the integral closure, the
Eisenstein unit identity `y^(m+1) = p·unit` pins `map(pℤ_p) = m_O^(k·n)` exactly via
`ramificationIdx_spec`, and `Ideal.ramificationIdx_mul_inertiaDeg_of_isLocalRing` collapses k = 1).
Gate corollary `gate_ef_forced : efOf = (2,1)` for every bundle on a gate-fiber member, stated
WITHOUT the axiom. The fine-(e,f)-swap mutation ({(1,2)} at the gate — which passed the old
count-only probe) now machine-derives `False`; refutation cone free of the real axiom; scratch
recorded and deleted. 12 new declarations + census, all core-only, zero regression. The wild
branch's (e,f) payload at the gate is now MACHINE-GUARDED, not cite-trusted. FLAGS 2–3 unchanged
(probe coverage gate-local; bundle e·f-coherence rests on the pinned integral closure).
