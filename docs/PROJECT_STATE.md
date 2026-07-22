# Project state — Lean formalization of uniform rationality of *p*-adic factorization densities

*Snapshot: 2026-07-19. This document lays out (1) the bigger picture, (2) what is proved and on what
it rests, (3) the Lean blueprint and its correspondence to the math-language proof, and (4) what is in
progress. It is meant to be sufficient, together with the code, for a reader to reconstruct the full
state of the project.*

---

## 1. The result and the bigger picture

**Theorem (informal).** Factorization "types" σ classify how a monic polynomial splits (e.g. "two
distinct linear factors and one irreducible quadratic"). Draw a monic degree-*n* polynomial over ℤ_*p*
uniformly at random. The probability `ρ(n, σ; p)` that it has factorization type σ over ℚ_*p* is, as a
function of `q = p`, one **fixed rational function** `R_σ ∈ ℚ(t)` — **independent of the prime**, valid
even at the *wild* primes `p ≤ n` where naive Hensel/tame arguments break — and in the projective
weight-normalized normalization `R_σ` is **palindromic**.

**Why it is hard.** At *tame* primes (`p > n`) the count is governed by residue-field combinatorics and
is visibly a polynomial in `q`. At *wild* primes (`p ≤ n`) ramification is genuinely *p*-adic: the
factorization is controlled by the Okutsu–Montes (OM) higher-order Newton-polygon algorithm, whose
combinatorics a priori depend on *p*. The content of the theorem is that, after the right normalization,
the wild contribution assembles into the *same* rational function — the p-dependence cancels.

**The bigger picture.** This is the local input to a *p*-adic Chebotarev-type program (the companion
project *"A Chebotarev Density Theorem over p-adic Fields"*, Asvin G., Wei, Yin). The paper being
formalized is `docs/references/uniform-rationality-paper.pdf` (Claude & Asvin G.).

---

## 2. What is proved, and on what it rests

**Read this section carefully — `sorry`-free is not the same as non-vacuous, and the distinction is
the whole point.** A standing semantic audit (2026-07-19) established the following honest picture.

### Genuinely machine-checked, non-vacuous

- **A `p`-uniform rationality engine.** The count-native OM cluster-volume recursion + the `RatFn`
  closure produce, over all primes *including wild*, a uniform rational function of `q` (genuinely
  `q`-varying; wild contribution = lattice-volume factor × finite-field residual count). The soundness
  fixes are real: `IsPalindromic` is the faithful `R(1/x)=R(x)`; `TameFunctionalEquation` is a
  definition (an earlier *false* global axiom was caught and removed).
- **A real order-0 density theorem** — `Order0RealDensity.montes_order0_density_general_prime`: an
  actual `Nat.card` fiber count over `monicBox p N n`, uniform-rational over all primes, machine-checked
  with a positivity/non-vacuity gate. **But** it covers the **order-0 separable/unramified stratum
  only**, is **monic** (not projective), carries **no palindromy**, and feeds no `Goal` capstone.
- The Okutsu–Montes classifier subsystem is formalized (higher-order Newton polygons, residual
  polynomials, the OM tree/type, φ-adic development) — the ~95-module `LeanUrat/OM/`.
- **The rebased V2 capstone chain (2026-07-19, M9-rebase waves W1–W3;
  `notes/M9_REBASE_BLUEPRINT_2026-07-19.md`; canonical names since W4, 2026-07-21).**
  `OM/RealInstanceV2.montes_unconditional` — THE capstone: for
  every degree-`n` type σ, the σ-KEYED corrected engine density `∑_{T ∈ omMenu n σ} omCount T q'`
  is uniform-rational (unconditional), the real decided counting density at `realP` equals its
  value (unconditional — the counting legs are the PROVED `h_node0` limits), and it is palindromic
  GIVEN the explicit hypothesis `htameFE` (no axiom: footprint is Lean-core ONLY). Fires
  `MontesV2.goal_theorem_montes` through the first non-trivial real `DensityFoundation` instance
  (`realF2`). **Non-vacuous and σ-dependent, machine-checked**: value 1/4 at n=2 inert
  (`gate_v2_countingDensity_inert2`, through the real instance), split 1/9 ≠ inert 1/3 at the tame
  prime q'=3 (σ-separation, O1 reversed), ramified menu honestly empty, `htameFE` certified a
  non-trivial constraint at a tame prime (`gate_v2_htameFE_nontrivial`), zero-coefficient mutation
  refuses to compile (V1 reversed at the instance). The `_exhaustive` companion adds the
  bracket-uniqueness full-density clause behind the honest `hExhaust` (undecided mass → 0 — open,
  Phase B drainage). Scope honesty: the certified density is the order-0-decided stratum density;
  wild self-loop legs re-enter as hypotheses only when the Phase-B menu grows. Gates: 10 Lean gate
  theorems (`OM/RealInstanceV2Gates.lean`), 21/21 exact Python brute-force cross-check, 2026-07-19
  fresh-context semantic audit clean (no critical error, single gap closed same day).

- **The first machine-checked WILD densities (Wild Wave 1, 2026-07-21;
  `notes/WILD_WAVE1_BLUEPRINT_2026-07-21.md`).** `OM/RealInstanceW.montes_unconditional_w`
  (+`_exhaustive`): the capstone statement over the extended σ-keyed menu `omMenuW` — order-0
  separable shapes ∪ the canonical minimal-H wild stratum for constant-e ramified types (the
  PROVED terminating "Tselfloop" family; slope −1/e, side (0, n/e)–(n, 0), separable residual).
  Footprints Lean-core only. Machine-checked wild values through the real instance: the totally
  ramified quadratic type {(2,1)} — genuinely wild at p=2 (p ∣ e) — certifies density
  **1/8 = (p−1)/p³** (its V2 menu value was 0); n=4 wild σ-separation 0 vs 1/256 with the p=2
  empty stratum machine-checked as a pool-size effect, not a bug. Exhaustive Python cross-check
  exact on all anchors ((p−1)/p³, (p−1)/p⁴, the n=4 pair). Scope honesty (in every docstring):
  the certified ramified value is the MINIMAL-H stratum density — the leading term of the type's
  density, NOT the H-tower sum (that resummation is the recursive self-loop wall); mixed-e types
  (multi-slope) and order ≥ 2 not covered; no exhaustiveness claim.

### `sorry`-free but NOT (yet) a non-vacuous proof of the FULL theorem — the honest remaining gaps

**The W4 swap (2026-07-21) retired the old vacuous chain**: the old `M9.montes_unconditional` +
`realM/realD/realF`, the old `MontesData` bridge (`Decomposition.lean`, old `Goal.goal_theorem_montes`
/`goal_theorem_via_montes`), and the axiom `realDensity_tame_functionalEquation` now live only in
`lean/quarantine/{RealInstance_oldCapstone,MontesData_oldSpine}_2026-07-21.lean.txt`. The canonical
spine is `MontesV2.lean` (abstract-coefficient `MontesDataV2` + `goal_theorem_montes`/
`goal_theorem_via_montes`, ∀-conditionals, core-only) instantiated by `OM/RealInstanceV2.lean`;
`Goal.goal_theorem` (the measure route, 4 PadicMeasure axioms) remains as the independent second route.

What still separates the (non-vacuous, σ-keyed, order-0) capstone from the FULL theorem:

- **`htameFE` is a hypothesis, not yet discharged on the real instance.** Palindromy of the certified
  density is conditional on the tame functional equation for `realF2`. It is machine-certified
  NON-trivial (`gate_v2_htameFE_nontrivial`: the density is 1/3 > 0 at the tame prime 3), but its
  honest discharge needs Phase B: tame-menu exhaustiveness + the M1 projective bridge, at which point
  the Del Corso–Dvornicich cite can be declared faithfully (the retired axiom's intended content).
- **Decided vs full density.** The certified value is the order-0-decided stratum density; the tie to
  the full type-σ density is the bracket-uniqueness clause of `montes_unconditional_exhaustive`,
  conditional on `hExhaust` (undecided normalized mass → 0) — open until the classifier drains
  (Phase B; `Drainage.lean` shows the current classifier does not drain at any finite order).
- **Order ≥ 1 wild content.** The current `omMenu` is the order-0 separable slice; deeper decided
  shapes and the wild self-loop `h_node` legs (the `SelfLoopHNode` aggregate) re-enter as menu growth
  in Phase B. The `F.density` of the abstract conditionals remains un-pinned to the paper's Haar
  density (mathlib has no `p`-adic Haar measure) — the standing interpretive wall, carried honestly
  as `hbridge` (discharged by `rfl` for the count-native real instance).

**Bottom line for §2:** the machine-checked content is now the rationality machinery PLUS a
non-vacuous, σ-dependent, core-only order-0 capstone through the full interface; the FULL palindromic
all-orders per-type theorem still awaits Phase B (drainage, wild legs, faithful tame cite, projective
normalization). `LeanUrat/AxChk_baseline.lean` (`lake build LeanUrat.AxChk_baseline`) prints the
machine-checked per-theorem `#print axioms` — the ground truth for footprints, not this prose.

### The trusted base (the declared `axiom`s)

Each is an explicit `axiom` that faithfully ports one published result. Full audit:
`docs/AXIOM_FAITHFULNESS.md`; standing re-audit log: `notes/SEMANTIC_AUDIT_LOG.md`.

| axiom | file | ports |
|---|---|---|
| `AX_cellRecursion` | `PadicMeasure.lean` | Denef–Igusa *p*-adic Igusa-zeta **cell recursion** (the measure "wall") |
| `clusterMeasure`, `omCells`, `descend`, `descend_size_lt` | `PadicMeasure.lean` | the measure-route OM-tree interface (dropped by the count-native capstone) |
| `omReadValuation_lt_of_certLevel_fkeyed` | `OM/Classifier.lean` | GMN (Guàrdia–Montes–Nart, arXiv:0807.2620) **theorem of the index**, `ind(f) ≤ v_p(disc f)`, read-set-restricted, arising-key form |
| `om_leaf_faithful` | `OM/OmLeafFaithful.lean` | GMN Thm 1.15 + 1.19 + Cor 1.20 (order-1 leaf dichotomy, explicit (e,f); the order-≤1 instances of Thm 3.1/3.7/Cor 3.8) + Def 3.10/eq.(37), **jointly with** the standard local-field structure theory the paper presupposes (integer rings of finite extensions of ℚ_p are DVRs; Serre, *Local Fields* I–II — mathlib cannot prove this at the pin, so the `LocalFactorData` existence is carried here). **Menu-fiber-scoped** (arising-shape form; RE-SCOPED W4c 2026-07-22, guardian audit #4 ACCEPT-WITH-FLAGS): only for `f : ℤ_[p][X]` in a genuine fiber of a shape of the mixed-e menu `MultiSlopeMenu.omMenu4 n K σ` (∀K), via the PER-FAMILY fiber predicate `fiberOf4` — `B.classify = T` on the order-0/constant-e families, `classify1 = some (mkCell (decode T))` on the multi-slope mixed-e literals (the dispatch that prevents a vacuous mixed branch: B.classify reads only the first side). Content: GMN Thm 1.15 slope dissection + per-side Thm 1.19/Cor 1.20, the mixed (e,f)-multiset recovered by `typeOf4`. Prior scopes derived back (`om_leaf_faithful_w3`/`_w1`); consumers byte-unchanged. Anchors/probes: full-strength no-root theorem at the n=5 mixed gate; all-unramified AND wrong-e mutations machine-refuted. Existence-only; no uniformity/rationality/measure/density term. Consumed ONLY by the faithfulness theorems (`menuFiber_hasType` etc.) — the density capstones remain Lean-core-only (census re-prints). Mutation probe on record: the split-type mutation derives machine-checked `False` against the axiom-free Eisenstein irreducibility of the wild gate fiber. |

**RETIRED (W4, 2026-07-21):** `realDensity_tame_functionalEquation` (Del Corso–Dvornicich tame
functional equation) — deleted with the old capstone chain. It could not be faithfully retargeted to
the corrected σ-keyed density (a partial monic decided density is non-palindromic in general; the old
version was satisfied only vacuously by the constant-0 instance). The tame FE is now the capstone's
explicit `htameFE` hypothesis, machine-certified non-trivial; the DCD cite returns at Phase B where
exhaustiveness + the M1 projective bridge make it faithfully statable. Net: the count-native capstone
footprint is Lean-core ONLY, and the trusted base is one axiom smaller.

Faithfulness discipline (why these are trusted, not just asserted): every axiom is checked by a
standing read-only "semantic guardian" agent under a triple test — (1) *statement-map both directions*
(says neither more nor less than the cited claim; in particular no smuggled uniformity/rationality/
p-independence — those are **derived**, never imported); (2) *mutation* (a wrong tweak must break the
build); (3) *non-vacuity* (hypotheses satisfiable, not a compiled `False`). Two false axioms were caught
this way and removed (a false *uniform* `omReadValuation`, refuted by `g = xⁿ + pᴺ`; and a *universal*
descent citation, refuted by `g = X² + X + pᴺ`), which is why the surviving citations are narrowly
scoped (read-set-restricted, arising-key-only).

### The one banked `sorry`

`Classifier.npVertices_stable_of_hull_preserved` — a Newton-polygon hull-invariance helper. It is the
**sole** `sorry` in the repository and is **off the capstone path**: it is consumed only by
`boxValSupport_reduce_stable_R` (an off-capstone reduce-stability lemma), never by any capstone. Retained
as an honest banked contract rather than deleted.

---

## 3. The Lean blueprint, and how it builds on the math-language proof

The math-language proof is `docs/HUMAN_PROOF.md` (13 sections). The Lean mirrors it layer for layer.

| math proof (`HUMAN_PROOF.md`) | Lean module(s) | content |
|---|---|---|
| §1, §13 Goal Theorem + assembly | `MontesV2.lean` (count-native spine), `Goal.lean` (measure route), `OM/RealInstanceV2.lean` (the real capstone) | the capstones + `countingDensity_eq_sum_coeff` (old `Decomposition.lean` quarantined at W4) |
| §3 L1 Hensel splitting is measure-exact | `Interface.lean`, `Witness.lean` | the density foundation / measure interface |
| §4 L3 residue-field shape counts are universal polynomials | `L3.lean`, `L3Gauss.lean`, `L3Squarefree.lean` | necklace/Gauss counts over 𝔽_q |
| §5 L4 = BB1 Newton-polygon cell volume | `L4.lean` | `cellVolume_eq` — a characteristic-independent `q`-power (proved, not axiomatized) |
| §6 M6 order-`r` residual equidistribution | `OM/` subsystem | count → volume at each OM order |
| §7 R1 Vandermonde change-of-variables | `R1.lean` | pushforward over `O_K` |
| §8 L2core / BB3-∞ cluster volume is rational (all OM orders) | `OM/` (count-native); `PadicMeasure.lean` (measure) | the wild engine; the old measure-route `BB3inf` is retired to `quarantine/` |
| §9 L5fix termination + finite p-independent menu | `L5fix.lean`, `OM/…` | geometric closure, finite shape menu |
| §10 L6M4 finite linear system over ℚ(q) | `L6M4.lean` | p-independent coefficients |
| §11 M1 monic → projective bridge | `M1.lean` | normalization |
| §12 L7 functional equation by interpolation from tame primes | `L7.lean` | palindromy |

Two routes to the capstone are formalized (see `notes/SEMANTIC_AUDIT_LOG.md` / the paper for why both):

- **Measure route** (`PadicMeasure` + `clusterVolume_rational`): full density = rational modulo the
  Denef cell-recursion axiom `AX_cellRecursion`. Complete but rests on the measure wall.
- **Count-native route** (`MontesV2` spine + `OM/` + `MontesAllOrders` + `ConditionalDensity` +
  `OM/RealInstanceV2`): the wild content is moved into explicit hypotheses so the spine theorems are
  Lean-core-clean, and — since the M9 rebase (W1–W4, 2026-07-21) — the spine has a **non-vacuous,
  σ-keyed real instance** (`realF2`, order-0 decided stratum; §2). The residual vacuity is honestly
  scoped to Phase B: the order-≥1 menu legs, drainage/exhaustiveness, and the `htameFE` discharge
  remain open hypotheses, not instances.

### The OM subsystem (`LeanUrat/OM/`, the bulk of the work)

This is the novel formalization: a Lean model of the Okutsu–Montes higher-order Newton-polygon
classifier — the object that computes the *p*-adic factorization at wild primes. Key pieces:
`OMType.lean` (the OM tree/type), `Classifier.lean` (the `classify`/`classifyGenuine` reader),
`Development.lean` (φ-adic development), `NewtonPolygon.lean`, `ResidualPolynomial.lean`,
`UnramifiedBase.lean` (the residue-field-extension base ring `O'' = AdjoinRoot g`),
`MontesAllOrders.lean` (assembly), `ConditionalDensity.lean` (the conditional top-level density).

---

## 4. In progress — the order-≥2 wild tower

The classifier's faithfulness to the genuine Montes tree is currently established at **order ≤ 1**
(tame + first-order wild). Extending it to **order ≥ 2** (deep wild ramification, where the OM algorithm
descends through a *tower* of residue-field extensions) is the active work. Design docs are in
`docs/in-progress/`.

**Resolved (2026-07-17):** the semantic scope of the order-≥2 index citation — it is **arising-key-
restricted**, not universal (forced by GMN's theorem of the index `ind = Σ_r ind_r ≤ v_p(disc)` plus
worked examples; a universal reading is refuted by `g = X²+X+pᴺ`). Write-up:
`docs/in-progress/ORDER2_CITE_INTERPRETATION_2026-07-17.md`.

**Landed (builds #70–#72, additive leaf modules, all core-only):**
- `OM/LevelDrop.lean` — the level-drop ring hom `θ : Oring(N+1,g') → Oring(N,g)` between consecutive
  truncation levels, + residue hom + the naturality square.
- `OM/LevelDropResidue.lean` — `resUnitResidue_levelDrop`: the residue reader commutes with `θ` below
  the read cutoff (CITE-free).
- `OM/ChildResidualLevelDrop.lean` — `childResidualExt_reduce_stable_of_cuts`: reduces the whole
  order-≥2 reduce-stability to exactly one input, the per-digit read cutoffs (which *is* the order-≥2
  citation).

**Remaining (the growing tower):** the architecture is decided — a **fixed ambient residue field**
`F = 𝔽_{p^{n!}}` giving a field-*constant* recursion (avoids the varying-type recursion-motive
obstacle), with the subfield-embedding faithfulness as the one new-math obligation, and the order-≥2
citation declared against the real `θ`. Then a `classifyFull` dispatcher (order ≤ 1 → existing reader,
order ≥ 2 → tower reader) makes the "classify = Montes tree" coincidence honest at all orders. Design:
`docs/in-progress/TOWER_ARCHITECTURE_BLUEPRINT_2026-07-18.md`.

---

## 5. What "done" means, and the road there

Three distinct gaps separate the current Lean from a machine-checked proof of the full theorem; they
should not be conflated (this is the mistake an earlier draft of this document made):

1. **Non-vacuity / the density instance — CLOSED at order 0 (M9 rebase W1–W4, 2026-07-21).** The
   V2 rebase (§2, `notes/M9_REBASE_BLUEPRINT_2026-07-19.md`) delivered the non-vacuous, σ-keyed,
   Goal-firing capstone `montes_unconditional` (Lean-core-only footprint), V1/O1 both reversed by
   machine-checked gates; the W4 swap executed (old chain quarantined, tame axiom RETIRED).
   Remaining density content beyond order 0 is Phase B: menu growth (deeper decided shapes), the
   recursive wild self-loop `h_node` legs, exhaustiveness/drainage (`hExhaust`), and the faithful
   tame-FE discharge (needs exhaustiveness + the M1 projective bridge).
   **Standing directive (Asvin, 2026-07-21): formalize WILD-case uniformity conditional on the
   Montes paper** (paper-stated results importable as axioms under the faithfulness discipline).
   Waves 1–2 LANDED (2026-07-21): Wave 1 (`notes/WILD_WAVE1_BLUEPRINT_2026-07-21.md`, audited
   PASS 8/8) — the first machine-checked wild densities, no new axiom; Wave 2
   (`notes/WILD_WAVE2_BLUEPRINT_2026-07-21.md`, guardian ACCEPT-WITH-FLAGS, flag 1 closed
   same-day) — genuine (e,f) vocabulary (`OM/QpType.lean`: mathlib ramificationIdx/inertiaDeg via
   the `LocalFactorData` bundle), the menu-scoped Montes-paper axiom `om_leaf_faithful`
   (`OM/OmLeafFaithful.lean`; see the trusted-base table), the faithfulness theorems
   (`menuFiber_hasType`: fiber members genuinely factor with type σ — core + the one axiom), and
   the axiom-free Eisenstein guard (`OM/QpTypeEisenstein.lean`: e = deg, f = 1 proved; the
   fine-(e,f) mutation machine-refuted). Density capstones remain Lean-core-only throughout.
   Wave 3 LANDED (2026-07-21, `notes/WILD_WAVE3_BLUEPRINT_2026-07-21.md`; guardian re-audit
   ACCEPT-WITH-FLAGS): the K-windowed menu `omMenuW3` + capstone `montes_unconditional_w3 (n K)`
   — window K=3 certifies 9/64 for the ramified quadratic at p=2 with machine-checked STRICT
   growth over Wave 1's 1/8, approaching (never claiming) the tower value 1/7; the axiom
   re-scoped to the windowed menu with new axiom-free H=3 anchors (non-Eisenstein (e,f)=(2,1)
   via ϖ-order parity) and both mutation probes re-fired.
   **Directive extended (Asvin, 2026-07-22): keep iterating toward the COMPLETE formalization
   modulo the Montes paper, or until multiple iterations stop moving the needle. Method: math
   first → detailed Lean blueprint → implementation; on difficulty, refine the math.** Declared
   endpoint boundary: palindromy remains conditional on `htameFE` (Del Corso–Dvornicich + the M1
   projective bridge — NOT Montes-paper content); "complete modulo Montes" = clauses (R)/(V) with
   full type coverage and full per-type mass, faithfulness modulo the (possibly extended)
   Montes-cited axioms. Roadmap: Wave 4 mixed-e types via the abstract product coefficient
   (banked `hnode_multiSideProduct`); Wave 5 the μ≥2 descent strata (recentering = the
   paper-stated OM descent; math-first note required); Wave 6 the K→∞ full-tower assembly
   (infinite menus, per-level finite support, series rationality via L5fix closure).
   Non-imports with machine-checked reasons: finite-level drainage (FALSE
   of the truncated classifier — `Drainage.lean`), residual equidistribution (no GMN counterpart
   — `notes/M6_lemma.md`).
2. **Order ≥ 2 (deep wild).** Classifier faithfulness is at order ≤ 1; the higher-order OM tower is
   in progress (§4).
3. **The trusted citation base.** Fully unconditional would require *proving* the cited axioms in Lean.
   The Denef–Igusa cell recursion (`AX_cellRecursion`) is known-hard and is the honest citation
   boundary; the GMN and Del Corso–Dvornicich inputs are literature results ported faithfully.

- **What is genuinely done now:** a `p`-uniform rationality *engine* (all primes, wild included) and a
  real *order-0* density theorem, plus the formalized OM classifier (§2). Palindromy is proved as a
  *transfer* mechanism but only ever fed an *assumed* tame functional equation — it is not yet
  established for a constructed real density.
- **Honest one-line status:** the *mathematics* is complete modulo the published Montes/GMN algorithm
  and is extensively cross-checked; the *Lean* is a sound, `sorry`-free engine + order-0 real result, but
  **not yet a non-vacuous machine-checked proof** of the full palindromic all-orders per-type theorem.

Canonical math notes (blueprints, audits, negative results) live in the companion `uniform-rationality`
project; the copies in `docs/` here are snapshots sufficient to reconstruct this Lean state.
