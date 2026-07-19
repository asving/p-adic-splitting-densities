# MONTES / OM UNIFORMITY — SEMANTIC + SOUNDNESS AUDIT

Target: Lean 4 / mathlib v4.31.0 formalization at `/workspace-vast/asving/forum-sigma/lean_urat`.
Capstones: `LeanUrat.OM.M9.montes_unconditional` (RealInstance.lean) and
`LeanUrat.Goal.goal_theorem` / `goal_theorem_montes` / `goal_theorem_via_montes` (Goal.lean).

Method: read-only inspection ("false-as-stated" test = does the axiom become false under some legal
instantiation of a free binder). All four parallel auditors (false-axioms, vacuity, sorry-footprint,
meaning) independently converged on the same top finding. Findings deduped and severity-ordered below.
Line numbers reconfirmed by direct read of Interface.lean, OMType.lean, PadicMeasure.lean, L4.lean.

The tree has already had TWO false-axiom fake-closes this session. This audit finds a THIRD of the same
class — on the one axiom the Map inventory had cleared — plus two more (off-footprint) instances.

---

## (1) UNSOUND

### U1 — `tame_functionalEquation` is FALSE-AS-STATED, and it is on ALL FIVE capstone footprints. [HIGHEST SEVERITY]

- **File:line:** `LeanUrat/Interface.lean:367-373`.
- **Statement:**
  ```lean
  axiom tame_functionalEquation (F : DensityFoundation) :
      ∀ (n : ℕ) (σ : FactorizationType), σ.degree = n →
        ∃ (num den : Polynomial ℚ), den ≠ 0 ∧
          (∀ q : ℕ, q.Prime → n < q → F.density n σ q = num.eval (q:ℚ) / den.eval (q:ℚ)) ∧
          IsPalindromic num den
  ```
- **Exact issue:** the axiom is quantified over a **free** `F : DensityFoundation` and asserts that
  `F.density n σ` agrees with a rational function of `q` at infinitely many (tame) primes AND is
  palindromic. But the structure `DensityFoundation` (Interface.lean:226-249) has exactly six fields —
  `density, clusterVolume, shapes, multiplicity, decomposition, density_nonneg` — and NONE constrains
  `density` to be rational, bounded, or palindromic. The only structural field, `decomposition`
  (line 246-247), reads `density = ∑_T (multiplicity T).eval q · clusterVolume T q` where
  `clusterVolume : ClusterShape → ℕ → ℚ` is a *free arbitrary* function (its rationality lives in the
  SEPARATE `OMBridge` / `clusterVolume_rational`, which is NOT a field of `DensityFoundation` and NOT a
  hypothesis of this axiom). So `density` is a completely free `ℚ`-valued function of `q` subject only to
  matching its own arbitrary decomposition — i.e. no constraint at all. This is exactly the same
  free-parameter/conclusion-shaped defect as the already-flagged A6/A7/A9/A10, one level up (free `F`
  instead of free `cells`). The Map inventory graded this "Free-param risk: No (over abstract `F`)" —
  that grade is WRONG: "over abstract `F`" IS the defect.
- **Concrete witness (falsifying instantiation), field-by-field checked:**
  Build `Fbad : DensityFoundation` with (mirroring the freely-constructed `Witness.witnessFoundation`,
  Witness.lean:84-92):
  - `density := fun _ _ q => (Nat.factorial q : ℚ)` (equivalently `(q:ℚ)`; factorial is starker)
  - `shapes := fun _ _ => {T₀}` (ClusterShape is inhabited), `multiplicity := fun _ => 1`,
    `clusterVolume := fun _ q => (Nat.factorial q : ℚ)`
  - `decomposition`: RHS `= ∑_{T ∈ {T₀}} (1).eval q · q! = q!` = LHS by `Finset.sum_singleton`. HOLDS.
  - `density_nonneg`: `0 ≤ q!`. HOLDS.
  Apply `tame_functionalEquation Fbad 0 ⟨∅⟩ rfl` (degree-0 type; then `n < q` is `0 < q`, all primes).
  It asserts `∃ num den, den ≠ 0 ∧ (∀ q prime, q! = num(q)/den(q)) ∧ IsPalindromic num den`. A nonzero
  rational function grows polynomially (`|num(q)/den(q)| ≲ C·q^{deg num − deg den}`), while `q!` is
  super-polynomial, so the equality fails at all large primes and the existential is UNSATISFIABLE.
  (If `den` has a root at some prime `q`, Lean's `x/0 = 0` convention makes the RHS `0 ≠ q!`, still
  false — no escape hatch.) Hence `False` is derivable from `tame_functionalEquation` ALONE.
  - A gentler witness (`density := q`) also works: the ℚ(t) identity theorem forces `num = X·den`, then
    `IsPalindromic` (Interface.lean:356-358) at any non-root `x ∉ {-1,0,1}` demands `x⁻¹ = x`, contradiction.
- **Reaches capstones:** YES — all five. Entry point `Goal.lean:177`
  (`obtain ⟨num,den,…⟩ := tame_functionalEquation F n σ hσ`), which `goal_theorem_montes`,
  `goal_theorem_via_montes`, `goal_theorem`, and (via `goal_theorem_montes`) `montes_unconditional` all
  route through for the palindromy half. `#print axioms` of every capstone lists `tame_functionalEquation`.
- **Severity:** UNSOUND. Because the axiom set under every capstone is inconsistent, the palindromy half of
  every capstone rests on `False`. (The capstones only ever *fire* the axiom at "good" `F` — e.g.
  `montes_unconditional` pins `F := realF` whose density is the genuine rational tree-sum, and the Goal
  theorems gate `F.density` rational via `hbridge` — so the *conclusions* are not the thing being
  contradicted; but the trusted base is inconsistent, so the proofs are not valid proofs.)
- **Precise fix (pick one):**
  1. State the axiom about the CONCRETE count-native density family (as A11/A12 are pinned to `realP`),
     not over a free `DensityFoundation`; OR
  2. Add a hypothesis to the axiom that `F.density n σ` is eventually a rational function of `q`
     (i.e. supply the `num/den` as input and let the axiom assert only the palindromy of THAT rep); OR
  3. Add the missing `density_le_one` / `total_mass` fields the docstring already advertises (see C1) —
     `density_le_one` alone kills the `q!` and `q` witnesses, though a bounded-but-non-rational `density`
     (e.g. `1/2 + sin`-like ℚ-valued oscillation) could still falsify palindromy, so (1) or (2) is safer.
- **Build-check for Verify:** construct `Fbad` in a scratch module and confirm
  `example : False := by have := tame_functionalEquation Fbad 0 ⟨∅⟩ rfl; …` type-checks.

### U2 — `nodeMeasure_boxSum` is a SORRY over a FALSE-AS-STATED statement (landmine). [off all footprints]

- **File:line:** `LeanUrat/OM/LevelNCount.lean:533-544` (sorry at 544).
- **Exact issue:** LHS is `lim_N stratumCount (shapeFiberCount p n classify) T N / q^(n·N)`, which depends only
  on `p, n, classify, T, q` (verified `shapeFiberCount` = `Nat.card {f // classify N f = T}`, LevelNCount:64-67,
  no `cells`). RHS sums over `(cells T).map (…)` divided by `countPivot (treeSize T) q`. The two sides are
  decoupled: LHS does not mention `cells`/`treeSize`, RHS does.
- **Concrete witness:** `cells := fun _ => []` and a LEAF shape `T` (`treeSize T < 2`, so
  `countPivot (treeSize T) q = 1`, MontesAxiom.lean:126-127). Then RHS `= (empty sum)/1 = 0`, while LHS is
  the genuine shape-fiber density, generically NONZERO (positive for the classifier's most-common leaf shape).
  Statement FALSE.
- **Severity:** UNSOUND-if-wired. It is a `sorry`, not an `axiom`, so it only injects unsoundness via `sorryAx`
  if referenced as a term. Confirmed OFF every capstone footprint: no `sorryAx` in any capstone's `#print axioms`;
  and the `MontesData.nodeMeasure_boxSum` FIELD is discharged in `montes_unconditional` by the honest hypothesis
  `h_node` (RealInstance.lean:641, `nodeMeasure_boxSum := h_node`), a harmless name collision with this theorem.
- **Precise fix:** couple the signature — make the LHS density depend on `cells` (e.g. state it about
  `nodeNum`/`stratumCount` built FROM `cells`), or discharge it only through the pinned real instance. Until
  then, keep it strictly out of every term. Ideally delete the theorem and rely solely on the `h_node` hypothesis.

### U3 — `AX_columnMeasure` is FALSE-AS-STATED (free `cellVol`, derives 0 = 1). [DEAD; no footprint]

- **File:line:** `LeanUrat/PadicMeasure.lean:337-339`; live consumer `cellVolume_eq_bb1Value` at 621-624.
- **Statement:** `axiom AX_columnMeasure (cellVol : L4.LatticePolygon → ℕ → ℚ) (pg) (Q) : cellVol pg Q = ∏ i : Fin pg.width, L4.columnMeasure pg Q i`.
- **Exact issue:** `cellVol` is a FREE function asserted equal to a fixed product. This is the classic
  conclusion-as-free-parameter axiom (the sibling `L4.cellVolume_eq` correctly takes the SAME equation as a
  HYPOTHESIS `hfactor`). At a width-0 polygon the product over `Fin 0` is the empty product `= 1`, so with
  `cellVol := fun _ _ => 0` the axiom asserts `0 = 1`.
- **Concrete witness:** `cellVol := fun _ _ => 0`, `pg` a width-0 `L4.LatticePolygon`, any `Q`. Verified
  `bb1Value pg Q = (1-Q⁻¹)^{newtonVertexCount} · Q^{-newtonExponent}` with both exponents 0 at width 0, so
  `bb1Value = 1` (L4.lean:79-80). Then `cellVolume_eq_bb1Value (fun _ _ => 0) pg 2 (le_refl _)` (PadicMeasure:621)
  proves `0 = bb1Value pg 2 = 1`, i.e. `False`.
- **Severity:** UNSOUND-in-base, but DEAD: `cellVolume_eq_bb1Value` has NO consumers, and `AX_columnMeasure` has
  no other consumer, so it is off every capstone footprint. Still a `False`-generator sitting in the trusted base.
- **Precise fix:** delete `AX_columnMeasure` + `cellVolume_eq_bb1Value` (both dead), or convert `AX_columnMeasure`
  to the `hfactor`-hypothesis form exactly like `L4.cellVolume_eq`.

### U4 — `gmn_node_ef_law` is FALSE-AS-STATED (free `D : OMType`, fields not tied). [off footprint]

- **File:line:** `LeanUrat/OM/LevelNCount.lean:971`. `axiom gmn_node_ef_law (D : M5.OMType) : D.δ * D.dr = M5.clusterSize D`.
- **Exact issue:** verified `OMType` (OMType.lean:87-124) carries `δ`, `dr`, `cs` as INDEPENDENT `ℕ` fields;
  `clusterSize D := D.cs` (OMType.lean:130). The only proof-fields are `hResidueDeg` (`δ = finrank F0 Fr`),
  `hResidualDeg` (`dr = Rr.natDegree`), and `hDrLtCs` (`0 < dr → dr < cs`). NONE forces `δ·dr = cs`. So the
  axiom asserts a relation among three independent fields that a legal `OMType` can violate.
- **Concrete witness:** `D` with `F0 = Fr = ZMod 2` (so `finrank = 1`), `δ := 1` (matches `hResidueDeg`),
  `Rr := Polynomial.X` (so `dr := 1` matches `hResidualDeg`), `cs := 5`, `hDrLtCs : 0 < 1 → 1 < 5` ✓. Then
  `δ · dr = 1 ≠ 5 = clusterSize D`. Statement FALSE.
- **Severity:** UNSOUND-in-base; off all capstone footprints (feeds only GLUE-2 `hSideTile_separable` /
  `perNode_tiling_separable`, LevelNCount:994, none in the montes route). Landmine. The Map inventory graded it
  "No free-param risk" — WRONG.
- **Precise fix:** add `hEfLaw : δ * dr = cs` as a proof FIELD of `OMType` (exactly as `hDrLtCs` is carried),
  or gate the axiom on the actual per-node e·f budget rather than the bare product of independent fields.

### U5 — `L2_reconstruct` is FALSE-AS-STATED and UNDER-FLAGGED. [off footprint]

- **File:line:** `LeanUrat/OM/LevelNCount.lean:241`. Free `classify`/`cells`/`cellPred`.
- **Exact issue:** LHS `Nat.card {f // classify N f = T}` is independent of `cells`; the conclusion is
  `Nonempty (Σ' sel : {f // classify N f = T} → Fin (cells T).length, …)`. Set `cells := fun _ => []` ⇒ codomain
  `Fin 0` is empty; on a NON-EMPTY fiber (e.g. `classify := fun _ _ => T`) no selector `nonempty → Fin 0` exists,
  so the `Σ'` type is empty and `Nonempty` is FALSE.
- **Severity:** UNSOUND-in-base; off all footprints (feeds only `stratumCount_factor_card` / `stratumCount_factor`,
  neither in the montes route). The key note: this axiom carries ONLY "honest NAMED axiom" docstring language, NOT
  the ⚠-FALSE-AS-STATED flag that its siblings A6/A9/A10 carry, despite being cleanly false. It is the
  least-flagged of the free-param axioms.
- **Precise fix:** add the ⚠-FALSE-AS-STATED flag; and couple the statement (state the selector's codomain from
  the actual fiber cardinality, not a free `cells`-derived length), or restrict `cells` to the real OM cells.

---

## (2) VACUITY

### V1 — Per-shape coefficients may be identically zero (density sum degenerate). [needs Verify build-check]

- **File:line:** `RealInstance.lean:105` (`decode T := leafOMTypeOfSize (M6.treeSize T)`), 73-85
  (`leafOMTypeOfSize` sets `Rr := 0`), `OMType.lean:202-242` (`cells` factorizes `Rr`),
  `ResidualPolynomial.lean:329-339` (`factorize_any 0` admits `factors := ∅`).
- **Exact issue:** `coeff T q' = clusterCount (M7.cells decode) … T q'`, and `M7.cells decode T` factorizes
  `Rr = 0` via `Classical.choice (M4.factorize_any T.Rr)`. If the chosen factorization of the zero residual is
  the empty list, `clusterCount [] … = 0` for every `T`, so the ENTIRE density sum of `montes_unconditional` is
  identically 0 — then the rationality/palindromy claim is about the constant-zero function (trivially rational;
  `IsPalindromic 0 den` trivially holds), i.e. arithmetically vacuous. Cannot be resolved by inspection because
  `M5.cells` uses opaque `Classical.choice` over the many inhabitants of `ResidualFactorization 0`.
- **Severity:** VACUITY (possible). Non-emptiness of the MENU is proved (V-clean below); this is a separate risk
  that the SUMMANDS are all zero.
- **Precise fix / build-check:** evaluate `M9.rawCount` / `coeff` on `shapeMenu 1` and check whether the density
  sum is a non-trivial function of `q` (not identically 0 or 1). If it can be zero, pin `decode`/the factorization
  so leaf shapes get their genuine (non-empty) cell list.

### V-clean (confirmed non-vacuous, no defect)

- **Menu is genuinely non-empty:** `shapeMenu n` (RealInstance:161) is the `M5.shapeOf`-image of `leafTypesUpTo n`;
  `shapeMenu_nonempty` (RealInstance:183) is PROVED (contains `shapeOf (leafOMTypeOfSize 0)`). `realClassify`
  (RealInstance:138) = `B.classify realP n` is the genuine OM classifier, not the old `⟨[],[]⟩` stub. The
  de-vacuification the Map reported HELD — the density sum is NOT an empty sum.
- **`n` (degree) is fully general:** `variable (q n : ℕ)` (RealInstance:58), so `montes_unconditional` is stated
  for arbitrary degree `n`, not degree-0-only. `realP := 2` is only the residue characteristic — legitimate.
- **`countingDensity_eq_sum_coeff`** (Decomposition:104-116) genuinely proves `ρ = ∑_T C_T` via `density_isLimit` +
  `stratum_tendsto_coeff` — a theorem, not a definitional tautology.
- **Goal capstones non-vacuous:** `montes_full_instance` (Witness.lean:318-324) fires `goal_theorem_montes` on a
  genuine coupled sorry-free bundle with `∑ coeff = 1` (over a trivial degree-0, `q=2` model — the honest measure
  wall, Goal.lean:24-39, not a new defect). `witnessFoundation.density := fun _ _ _ => 0` (Witness.lean:85) is a
  density≡0 stub used ONLY for `DensityFoundation_nonempty`, not for the coupled capstones.

---

## (3) OVERCLAIM

### O1 — `montes_unconditional`'s density is σ-INDEPENDENT: the type `σ` carries no content.

- **File:line:** `RealInstance.lean:852-871` (capstone) + `192-193` (`shapesOf σ₀ σ = if σ = σ₀ then shapeMenu n else ∅`).
- **Exact issue:** the capstone binds a query `σ` and passes it AS `σ₀` to `realM/realD/realF` (line 863,
  `realD n σ hσ`). So `(realD).shapesOf σ = if σ = σ then shapeMenu n else ∅ = shapeMenu n`. But `shapeMenu n` is
  the leaf menu of cluster sizes `0..n` — the SAME set for every `σ`. So the claimed "density of type σ",
  `∑_{T ∈ shapeMenu n} coeff T q'`, is IDENTICAL for every degree-`n` type σ; the model does not distinguish
  factorization types. The theorem is meaningful for every σ (each σ becomes its own σ₀, so it is NOT vacuous),
  but it is the SAME σ-independent function, NOT the genuine per-type density ρ(n,σ;q). The Map's "universality
  only at σ₀" understates this — σ₀ is re-pinned to whatever σ is queried.
- **Severity:** OVERCLAIM. The rationality+palindromy of `q' ↦ ∑_{T∈shapeMenu n} coeff T q'` is genuine; its
  attachment to "type σ" is vacuous of σ-content.
- **Precise fix:** either make `shapesOf` genuinely σ-dependent (partition the menu by type), or state the theorem
  about the σ-independent aggregate function and drop the per-type framing to avoid overclaiming.

---

## (4) COSMETIC

### C1 — `DensityFoundation` docstring advertises non-existent `density_le_one` / `total_mass` fields.

- **File:line:** `Interface.lean:219-223` (docstring) vs 226-249 (structure). The docstring claims fields
  `density_le_one` (densities in [0,1]) and `total_mass` (∑_σ density = 1). Neither exists (only `density`,
  `clusterVolume`, `shapes`, `multiplicity`, `decomposition`, `density_nonneg`). Documentation bug, but
  LOAD-BEARING to U1: had `density_le_one` existed, the `q!`/`q` falsifying witnesses would be excluded.
- **Fix:** either add the two fields (helps U1 — see U1 fix 3) or correct the docstring.

### C2 — Stale/self-contradictory docstring block on the orphaned `real_h_node` path.

- **File:line:** `RealInstance.lean:823-828` and 836-841 (stale) vs 763-768 + 843-851 (accurate corrective notes).
- **Issue:** `real_h_node` (RealInstance:790) discharges `h_node` via `nodeTrunc_tendsto` (LevelNCount:1262), which
  is itself FALSE-AS-STATED (same `cells := fun _ => []` argument; "compiles green" only because its proof invokes
  the false axioms `selfLoop_childFiber_corrected` + `boxVolumeScale_collapse`, and the tree even contains a
  machine-checked disproof of its limit value, `nodeTrunc_limit_denominator_mismatch`, LevelNCount:1296-1302).
  `real_h_node` is ORPHANED — never referenced as a term (confirmed by grep; the current `montes_unconditional`
  takes `h_node` as a HYPOTHESIS, RealInstance:853-860). The intervening docstring (836-841) still claims the
  "unconditional / no remaining hypotheses" close — self-contradictory and stale.
- **Severity:** COSMETIC documentation hazard on an otherwise-sound (conditional) capstone. But it is a live
  RE-WIRING landmine: re-connecting `real_h_node` into `montes_unconditional` would reintroduce two false axioms
  plus a disproven limit.
- **Fix:** delete the orphaned `real_h_node` and the false-as-stated `nodeTrunc_tendsto` (and its feeders
  A9/A10), or clearly mark them UNSOUND/DEAD; correct the 836-841 block.

### C3 — Zero-content restatement theorems (honest, harmless).

- `cellDegreeSum_eq_dr_of_separable` (LevelNCount:980-982) is `(hsep:P):P := hsep` — a tautology, but it is a
  THEOREM gated on the hypothesis (honest), not an axiom, and is off the capstone. `Decomposition.wiring_assessment
  : True := trivial` (Decomposition.lean:230) is an intentional docstring-only `True`. Both harmless.

---

## CONFIRMATIONS (matching the Map; verified by inspection)

- **The revert HELD.** `montes_unconditional` (RealInstance:852-871) takes `h_node` as a HYPOTHESIS and passes it
  to `realM/realD/realF`; it does NOT call the orphaned `real_h_node`. So the four already-flagged false-as-stated
  axioms A6 `selfLoop_childFiber_fkeyed` (CountingModel:520), A7 `L2_reconstruct` (LevelNCount:241),
  A9 `selfLoop_childFiber_corrected` (LevelNCount:1107), A10 `boxVolumeScale_collapse` (LevelNCount:1228) are ALL
  ABSENT from both montes capstone footprints (`#print axioms`, per Map). Confirmed off-footprint here by tracing
  consumers: A6→dead/superseded; A7→`stratumCount_factor*`; A9→`stratumCount_selfLoop_rec`; A10→`nodeTrunc_tendsto`;
  A9+A10→`nodeTrunc_tendsto`→orphaned `real_h_node`.
- **`h_node` is a genuine independent limit fact, NOT a conclusion-in-disguise.** It asserts per-shape convergence
  of `stratumCount T N / realP^{nN}` to the concrete finite tree-sum value = `D.C T realP` (via `C_rec`,
  MontesAxiom:522-527), a single rational NUMBER. It discharges the `nodeMeasure_boxSum` field and feeds ONLY the
  value clause via `countingDensity_eq_sum_coeff`. It says NOTHING about `num/den`, rationality, or palindromy.
  The rationality clause is proved independently by `countingDensity_isRational` (Decomposition:185-201) from the
  recursion structure, never touching `h_node`.
- **The `q := realP` pin is legitimate.** In `montes_unconditional` (RealInstance:861-868) the `∀ q'`
  uniform-rationality clause keeps its own bound variable `q'` over all `q' > 1` (line 862) and `IsPalindromic num
  den` (line 868) is unconstrained; only the VALUE clause (866-867) is `1 < realP → countingDensity = num(realP)/
  den(realP)`. The pin specializes the value clause alone. Does not weaken the uniform statement.
- **A11 `discZeroValTail_density` / A12 `decidedDensity_mono_realP`** (RealInstance:423/439) are the two live
  axioms unique to `montes_unconditional`. Both are CONCRETE (over `shapeMenu n` / `rawCount n`, pinned `realP=2`),
  with only `n`/`N` as bound vars — NO free `cells`/`classify`/`treeSize`. They PASS the false-as-stated inspection
  test. A12's docstring correctly notes it is FALSE at free `q>2`, hence stated only at `realP` — legitimate. Their
  TRUTH (Hensel disc-tail decay / cylinder monotonicity at the matched prime) is a deferred number-theory CITE that
  inspection cannot certify — flag for build/NT sanity check, but the STATEMENT SHAPE is sound.
- **A5 `omReadValuation_lt_of_certLevel_fkeyed`** (Classifier:602) is properly CONSTRAINED by
  `hbulk : zmodValuation(disc g) < N` (excludes the `xⁿ+p^N` counterexample its docstring cites). SOUND. Off
  capstone (feeds `certLevel_stabilizes`).
- **A18 `AX_cellRecursion`** (PadicMeasure:429) is SOUND-as-refactored: stated over the FIXED objects
  `clusterMeasure`/`omPivot` (no double-`pivot` binder), consistency witnessed by `clusterMeasureModel`. The prior
  double-binder unsoundness is genuinely fixed. (Measure route only — not the montes capstones.)
- **`hbridge` is honest and satisfiable.** In `goal_theorem_montes`/`_via_montes` (Goal.lean:155-156/211-212),
  `hbridge : ∀ q'>1, F.density n σ q' = ∑_T D.coeff T q'` identifies `F.density` with a concrete tree-sum; it
  asserts no rationality/palindromy, so it is not the conclusion. Discharged by `rfl` in `montes_unconditional`
  (RealInstance:871) because `realF.density` IS the tree-sum. `IsPalindromic` (Interface:356-358) is the FAITHFUL
  semantic `R(1/x)=R(x)` (the degree-blind reverse encoding was fixed) — genuine, not a weakened shadow.
- **Measure-route VACUITY watch (not the montes capstones):** A13 `omCells` (PadicMeasure:265) and A18 permit
  `omCells T := []`, collapsing `clusterMeasure` to 0 (trivially rational) — a weakness of the OLD route
  (`goal_theorem`/`clusterVolume_rational`/`density_rational`), which additionally carries the 4 PadicMeasure
  axioms as expected. The montes route drops them.
- **No conclusion-in-disguise on the RATIONALITY side.** `MontesData.C`/`C_rec`/`coeff_isRational`/
  `countingDensity_isRational` (Decomposition/MontesAxiom:517-561) are genuine recursion + the generic engine
  `OMInduction.clusterVol_isRational`; `IsRationalFn` (RatFn:32) is a real `∃ num den`. No rationality axiom.

---

## BOTTOM LINE

Both capstones are **NOT SOUND as they currently stand** — but the defect is a single shared axiom, not the
capstone-specific machinery, and the capstone-specific machinery is otherwise clean.

- **`LeanUrat.OM.M9.montes_unconditional` (conditional on `h_node`):** footprint is clean of the four previously
  flagged free-param axioms, of `sorryAx`, and of `real_h_node`/`nodeTrunc_tendsto` (the revert held); its
  count-native rationality half is genuinely proved and `h_node` is an honest hypothesis (not a
  conclusion-in-disguise). BUT its footprint contains `tame_functionalEquation`, which is FALSE-AS-STATED
  (U1), so its palindromy half rests on an inconsistent base. Honest status: *conditional-on-`h_node`,
  count-native-rationality sound, palindromy UNSOUND via `tame_functionalEquation`; also σ-content-vacuous (O1)
  and possibly summand-vacuous (V1).*

- **`LeanUrat.Goal.goal_theorem_via_montes`:** footprint `{propext, Classical.choice, Quot.sound,
  tame_functionalEquation}`; the `hbridge`-conditioned rationality half is genuinely proved and non-vacuous over
  the coupled witness, but the palindromy half rests on the FALSE `tame_functionalEquation` (U1). Honest status:
  *rationality sound and honestly conditional on the count-native bridge; palindromy UNSOUND via
  `tame_functionalEquation`.*

The single fix that restores soundness of BOTH capstones is U1: constrain / re-state `tame_functionalEquation`
so it is not an unconditional axiom over a free `DensityFoundation`. U2–U5 are additional false-as-stated items
in the trusted base but all OFF both capstone footprints (landmines, not active).

---

## VERIFY-PHASE BUILD-CHECK LIST (construct a `False`-witness for each suspected false axiom)

1. **U1 — `tame_functionalEquation` (Interface.lean:367): TOP PRIORITY.** Build `Fbad : DensityFoundation` with
   `density := fun _ _ q => (Nat.factorial q : ℚ)`, `shapes := fun _ _ => {T₀}`, `multiplicity := fun _ => 1`,
   `clusterVolume := fun _ q => (Nat.factorial q : ℚ)` (discharge `decomposition` by `Finset.sum_singleton`,
   `density_nonneg` by `q! ≥ 0`). Confirm `example : False := by have := tame_functionalEquation Fbad 0 ⟨∅⟩ rfl; …`
   type-checks (super-polynomial growth vs rational function).
2. **U3 — `AX_columnMeasure` (PadicMeasure.lean:337):** confirm `cellVolume_eq_bb1Value (fun _ _ => 0) pg 2
   (le_refl _)` reduces to `0 = 1` for a width-0 `L4.LatticePolygon pg` (`bb1Value = 1` at width 0).
3. **U4 — `gmn_node_ef_law` (LevelNCount.lean:971):** build an `OMType` with `F0=Fr=ZMod 2, δ:=1, Rr:=X (⇒dr=1),
   cs:=5, hDrLtCs := fun _ => by omega`; confirm `gmn_node_ef_law D` gives `1 = 5`, hence `False`.
4. **U5 — `L2_reconstruct` (LevelNCount.lean:241):** confirm at `cells := fun _ => []`, `classify := fun _ _ => T`
   the `Nonempty (Σ' sel …)` conclusion is refutable (nonempty fiber → `Fin 0` selector impossible).
5. **U2 — `nodeMeasure_boxSum` (LevelNCount.lean:544):** confirm it is a `sorry` over a false statement (`cells :=
   fun _ => []`, leaf `T`, RHS `= 0` vs nonzero LHS limit); and confirm `#print axioms montes_unconditional` shows
   NO `sorryAx`.
6. **Footprint re-confirm (all capstones):** re-run `#print axioms LeanUrat.OM.M9.montes_unconditional
   LeanUrat.Goal.goal_theorem_montes LeanUrat.Goal.goal_theorem_via_montes` — expect
   `montes_unconditional = {propext, Classical.choice, Quot.sound, tame_functionalEquation,
   decidedDensity_mono_realP, discZeroValTail_density}` (NO `sorryAx`, NO A6/A7/A9/A10) and the two Goal theorems
   `= {propext, Classical.choice, Quot.sound, tame_functionalEquation}`.
7. **A11/A12 number-theory sanity (not a shape defect):** sanity-check `discZeroValTail_density` and
   `decidedDensity_mono_realP` are true at `realP = 2` (Hensel disc-tail decay + cylinder monotonicity).
8. **V1 — summand non-vacuity:** evaluate `M9.rawCount` / `coeff` on `shapeMenu 1` and confirm the density sum is a
   non-trivial function of `q` (not identically 0 or 1).
