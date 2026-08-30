# UNIT RDC — VERDICT: THE RESULTANT-DEPTH CENSUS INSTRUMENTED AND THE DEFECT LAW RE-BASED — the lift-free depth instrument lands, the exact graded count identities land at every finite level, the depth-`v` GAP ENGINE (finite-precision factorization uniqueness at the shifted level `N−v`) is machine-checked Lean-core with the `v = 0` unit-corner injectivity as its instance, the decidedness-transfer criterion fires modulo the named Hensel leg, and `SplitConvolutionDefectLaw m σ` at EVERY mass reduces to two named census laws — while the `m ≥ 4` outright firing honestly does NOT close (the census rationality = the q-power fiber law is the exact named remainder, as SDL's fence predicted) (2026-08-30)

**Deliverable:** `leanfinal/Uniformity/ChapI/IFCG41.lean` (889 lines, ZERO sorries, zero
warnings, zero errors; 17 AxCheck footer lines — THIRTEEN pure Lean core
`{propext, Classical.choice, Quot.sound}` (the ENTIRE §3 engine, the §1 depth
instrument, the §2 graded identities and the multiplicity bound), and exactly FOUR carry
Lean core PLUS the owner-signed B.42 cite
`Uniformity.Density.Leaf.exists_slope_factorization` (inherited ONLY through SDL's
`one_le_multCount_of_vis`/`convCount_eq_card_vis_add_defect`):
`convCount_eq_card_vis_add_totals`, `convCount_graded_census`,
`splitConvolutionDefectLaw_of_censusLaws`, `splitSectorLaw_of_censusLaws`.  **The C.33
cites and `AX_cellRecursion` do NOT occur** — the measure route was never consumed; the
elementary route carried everything landed.  Verification: per-increment
`timeout 580 lake env lean Uniformity/ChapI/IFCG41.lean` (final run: only the 17
footprint infos), targeted `lake build Uniformity.ChapI.IFCG41` GREEN (8954 jobs).
Sanctioned one-line aggregator import appended to `Uniformity/ChapI.lean` after
IFCG40's; NOTE: `lake env lean Uniformity/ChapI.lean` is currently blocked by
**IFCG39 (another unit's in-flight module — instance-synthesis errors at its lines
1306–1309, pre-existing and untouched by this unit)**; my import line is validated by
the targeted build of the full IFCG41 chain.  No git ops.

## THE HEADLINE (what is new)

1. **★★ THE DEPTH-`v` GAP ENGINE** (`factor_perturbation_gap`, Lean-core, fully uniform
   in `q, N, v`, degrees): if `g·p + h·q = C(π^v)` (a depth-`v` Bezout witness),
   `g'h' ≡ gh mod π^N` (coefficientwise), and the monic same-degree factors agree mod
   `π^{v+1}`, then they agree mod `π^{N−v}` — **the factors are determined mod `π^{N−v}`
   exactly**, the charge's candidate mechanism, machine-checked.  Proof mechanism: the
   ultrametric bootstrap `s ↦ min(2s, N) − v` — the Bezout witness turns the linearized
   congruence into `C(π^v)·a − g·(pa − qb) = q·(D − ab)` (and its mirror), the
   quadratic error `ab` sits at doubled level, and the MONIC KILL
   (`C_pow_dvd_of_dvd_sub_monic_mul`, SDL's cancellation genre run at an arbitrary
   modulus `π^r`: a nonzero cofactor would give `ḡ·φ̄` a surviving leading coefficient at
   degree `≥ deg g` where `π^v·a` has none) discharges each round; ℕ-induction climbs
   `v+1 → N−v` in `≤ N` steps.  **This is the corrected replacement for the injectivity
   SDL refuted**: not level-exactness (false at depth `v > 0`) but exactness at the
   `v`-shifted level.
2. **★ THE DECIDEDNESS-TRANSFER CRITERION at depth `v`**
   (`decidedAt_mulClass_of_liftsFactor`, Lean-core): given (i) the depth-`v` Bezout
   witness, (ii) the Hensel existence leg `LiftsFactor` (every monic lift of the product
   class factors through the pair mod `π^{v+1}` — THE named open leg), and (iii) the
   factors decided at the SHIFTED level `N − v`, the product class is
   `⟨σ₁.data + σ₂.data⟩`-DECIDED at full level `N`.  The gap engine pins every lift's
   factors mod `π^{N−v}`; the shifted decidedness reads their types; `typeOf_mul` sums
   them.  SDL's sector-converse gate leg `hdec` now has its exact discharge criterion.
3. **★ the `v = 0` firing** (`mulClass_inj_of_coprime`, Lean-core): coprime lift pairs
   pinned residually (agreeing mod `π`) are determined LEVEL-EXACTLY by their product
   class — the unit-corner genre (IFCG16 §6/XHS §3) recovered as the depth-`0` instance
   of the engine, `N − 0 = N`.
4. **THE DEPTH INSTRUMENT is lift-free** (`classRes`, `mixDepth`): mathlib's
   `Polynomial.resultant` of the CLASS polynomials over the truncation ring `Res O N` —
   no lift consulted, so well-definedness is by construction; `classRes_proj`
   (mathlib's `resultant_map_map` + H102's `map_monicPoly_proj`) computes it as the
   truncation of any lift resultant, and `mk_pow_dvd_mk_iff` reads `π^v ∣` on classes
   as `π^v ∣` on lifts for `v ≤ N`.  `mixDepth` = greatest `v ≤ N` with
   `π^v ∣ classRes` (`Nat.findGreatest`; API: `mixDepth_le`, `mixDepth_dvd`,
   `le_mixDepth`).  The Bezout witness is SUPPLIED from the resultant by
   `exists_bezout_of_not_dvd_resultant` (DVR factorization `res = u·π^w` + mathlib's
   Sylvester-adjugate `exists_mul_add_mul_eq_C_resultant`): `¬ π^{v+1} ∣ res ⟹
   ∃ p q, g·p + h·q = C(π^v)`.

## ★ THE EXACT GRADED COUNT IDENTITIES (charge 1: landed, every finite level)

* ★ `pairFiber_eq_sum_pairDepthFiber` + ★ `multCount_eq_sum_pairDepthFiber` — THE
  RESULTANT-DEPTH CENSUS: every SDL `multCount` fiber partitions exactly by `mixDepth`
  (`pairFiber p c = Σ_{v ≤ M+m} pairDepthFiber p c v`), so the collision sum IS a
  census over resultant-depth strata.  Lean-core.
* ★ `collisionTotal_graded` / `strayTotal_graded` — the cell-side grading in the exact
  shape SDL's decomposition dictates: `Σ_vis (multCount−1) = Σ_k (k−1)·#{c ∈ vis :
  multCount c = k}` and `Σ_stray multCount = Σ_k k·#strayStrata_k`, ranges pinned by
  `multCount_le_convCount`.  Lean-core.  **The charged `Σ_v (strata)·(q^v − 1)` shape
  is exactly these identities composed with the OPEN fiber law `multCount = q^{depth}`
  — deliberately NOT asserted; the fiber law is the named remainder.**
* ★★ `convCount_graded_census` — the fully graded exact census:
  `convCount = #vis + [Σ_k (k−1)·#visStrata_k + Σ_k k·#strayStrata_k]` (B.42 via SDL).
* Instance-hygiene design: `collisionTotal`/`strayTotal` are summed over
  `(Set.toFinite ·).toFinset` — `Set.Finite` is a Prop, so the totals are
  Fintype-instance-free and every consumer identity is `rw`-stable (SDL's repair-log-5
  lesson enacted at the definition layer).

## ★★ THE REDUCTION (charge 4: the honest disposition of `m ≥ 4`)

`SplitConvolutionDefectLaw m σ` did NOT fire outright at `m ≥ 4` — exactly as SDL's
fence predicted, its content IS the census rationality.  What landed instead is the
COMPLETE reduction, at EVERY mass and type:

* `CollisionLaw m σ` / `StrayLaw m σ` — the two named census laws (the normalized
  collision excess resp. stray mass is a `ZcURLim` uniform rational limit).
* ★★ `splitConvolutionDefectLaw_of_censusLaws` : CollisionLaw → StrayLaw →
  `SplitConvolutionDefectLaw m σ` (all `0 < m`, all σ; B.42 via SDL's decomposition).
* ★ `splitSectorLaw_of_censusLaws` : under the `< m` decided value laws the two census
  laws close `SplitSectorLaw m σ` OUTRIGHT — the `m ≥ 4` ramified split leg is now
  OFFICIALLY: discharge `CollisionLaw` and `StrayLaw`.

## THE HONEST FENCE (the named remainder after this file)

1. **The `q`-power fiber law** — `pairDepthFiber` at depth `v` has size `q^v` per
   Hensel-liftable factorization (Sylvester kernel count mod `π^N` = Smith normal form
   over the DVR; Igusa genre) — and hence the RATIONALITY of
   `CollisionLaw`/`StrayLaw`.  The instruments are all landed (`mixDepth`, the graded
   identities, the gap engine for fiber separation, `mk_pow_dvd_mk_iff` for reading
   depth on digit boxes); the census itself is the one remaining engine.  The declared
   `AX_cellRecursion` cite family remains AVAILABLE for it (measure route) but was NOT
   consumed here.
2. **The Hensel existence leg** (`LiftsFactor` — polygon-block factor lifting at depth
   `v`; completeness enters HERE and only here).  Its exact complement (uniqueness) is
   this file's engine; SDL's `hdec` gate leg discharges through
   `decidedAt_mulClass_of_liftsFactor` once `LiftsFactor` lands.
3. Optional instrument not landed (out of core charge, cheap later): the per-argument
   cancellation bound `pairFiber p c ≤ decidedCount` (fiber injects via first
   projection by SDL's `mulClass_cancel_left`).

## File map (`leanfinal/Uniformity/ChapI/IFCG41.lean`, 889 lines)

§0 supply (`natCard_set_eq_card_filter` copy, `natCard_eq_sum_range_fiber`,
`C_pow_dvd_mono`) · §1 `classRes` (135), `classRes_proj` (146), `mk_pow_dvd_mk_iff`
(157), `mixDepth` (188), `mixDepth_le`/`mixDepth_dvd`/`le_mixDepth` · §2
`pairDepthFiber` (231), ★ `pairFiber_eq_sum_pairDepthFiber` (247), ★
`multCount_eq_sum_pairDepthFiber` (262), `visStrata`/`strayStrata`(+Counts),
`collisionTotal` (300), `strayTotal` (307), `multCount_le_convCount` (313), ★
`collisionTotal_graded` (325), ★ `strayTotal_graded` (367), ★
`convCount_eq_card_vis_add_totals` (407), ★★ `convCount_graded_census` (438) · §3
`exists_bezout_of_not_dvd_resultant` (459), `C_pow_dvd_of_dvd_sub_monic_mul` (494), ★★
`factor_perturbation_gap` (561), `C_dvd_monicPoly_sub`/`C_pow_dvd_mul_sub_of_mulClass_eq`,
★ `mulClass_fiber_gap` (703), ★ `mulClass_inj_of_coprime` (737), `LiftsFactor` (775), ★
`decidedAt_mulClass_of_liftsFactor` (790) · §4 `CollisionLaw`/`StrayLaw` (843/850), ★★
`splitConvolutionDefectLaw_of_censusLaws` (857), ★ `splitSectorLaw_of_censusLaws`
(881) · AxCheck footer (17 lines).  Imports: `Uniformity.ChapI.IFCG40` only.

## Design decisions (recorded)

* **Rationality route choice (charge 2)**: the elementary/digit route was taken as far
  as it provably reaches TODAY — the depth strata and graded identities are landed
  Lean-core, and `mk_pow_dvd_mk_iff` is exactly the digit-instrument hook (depth-v
  membership is a `π^v ∣ polynomial-in-digits` condition).  The rationality itself
  requires the fiber law (open); asserting it via `AX_cellRecursion` without the
  transfer bridge would have been a vacuity-shaped shortcut — declined.
* **The Bezout witness as interface** (`∃ p q, g·p + h·q = C(π^v)`) instead of a
  resultant-valuation hypothesis: monotone in `v` (weakening is multiplication by π),
  supplied from the resultant by `exists_bezout_of_not_dvd_resultant`, and the engine
  never needs the resultant itself — the criterion stays consumable at polygon faces
  where only ideal-theoretic coprimality data is available.
* `mixDepth` via `Nat.findGreatest` under the section-local
  `attribute [local instance] Classical.propDecidable` (IFCG24's idiom — `open
  Classical in` does NOT activate the scoped instance in this pin).
* **Explicit-application discipline against defeq blowups**: the depth-census `exact`
  had to pin `(α := …)` and the full set argument — underscore elaboration sent the
  unifier through `mixDepth → classRes → resultant → det` (deterministic heartbeat
  timeout); with all arguments explicit the match is syntactic and instant.

## Repair log (4 error rounds, all mechanical; every theorem landed as designed)

1. `open Classical in` fails to provide `DecidablePred` for `Nat.findGreatest` in this
   pin — section-local `attribute [local instance] Classical.propDecidable` (IFCG24's
   idiom); `Nat.findGreatest_spec` additionally needs `(P := …)` pinned (higher-order
   unification stuck otherwise).
2. Pin renames: `Ideal.Quotient.nontrivial_iff` (not `.nontrivial`),
   `Irreducible.not_isUnit` (not `.not_unit`), `Nat.lt_or_ge` (no bare `le_or_lt`),
   `← add_div` (no `div_add_div_same`); one over-eager `simpa` replaced by staged
   `simp only` + `rw` (simp pushed `map` through `C(π^w)` into a `C(ψπ)^w` shape).
3. The depth-census defeq timeout (see design decisions) — also required stating
   `pairDepthFiber`'s depth clause as a PREIMAGE (`(fun q => mixDepth π q.1 q.2) ⁻¹'
   {v}`) rather than a setOf, so the fiber helper matches syntactically.
4. `lean_multi_attempt` probes on a multi-line `exact` inherit the stale continuation
   line — two rounds of phantom "function expected" errors until diagnosed; the real
   signal was attempt-3's clean whnf timeout.
