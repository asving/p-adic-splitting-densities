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
   Montes-cited axioms.
   **Directive superseding the endpoint boundary (Asvin, 2026-07-22, post-W6c): PALINDROMY IS
   OUT OF SCOPE ENTIRELY — do not touch `htameFE`/L7/M1/DCD at all. The end goal of the
   formalization is EXACTLY the uniformity statement: for each type σ, ONE fixed rational
   function computes the density at ALL primes, wild included. Move directly toward
   formalizing the (accepted-note) argument proving this.**
   **W6q LANDED (2026-07-22, same day; blueprint `notes/WILD_WAVE6Q_BLUEPRINT_2026-07-22.md`
   Codex-verified CLEAN in 2 passes; guardian audit #7 ACCEPT-WITH-FLAGS): THE ALL-PRIMES
   UNIFORMITY CAPSTONE — `OM/UniformCapstone.montes_uniform_n2`, footprint Lean-core-ONLY.**
   FIXED polynomials (num, den) per degree-2 type — numR = 1, denR = X+1, numI = numS = X,
   denI = denS = 2X+2, defined once with NO prime in them — and for EVERY prime p (wild
   p = 2 included): (R) fixed-num/den uniform rationality, (V) `(M7 p).countingDensity σ =
   num(p)/den(p)` with den(p) ≠ 0, (B) bracket uniqueness fired OUTRIGHT via the general-p
   exhaustion `hExhaustP` (envelope (⌊N/2⌋+1)·p^{−(N−1)}, pure counting, NO new axiom).
   The general-p model `M7 p : CountingModel p 2` (`OM/UniformModelN2.lean`: residual-shape
   order-0 cells; ALL p residue points; FOUR chain families incl. the NEW even-height
   split-residual splitU leaf — pool (q−1)(q−2)/2, machine-checked empty at q = 2 —
   `OM/ChainMenuU.lean`); the four-way `cluster_coveringP` with NO parity case-split;
   the folded-weight envelope + the exact (q−1)-cancellation ledger + two-sided squeeze
   (`OM/UniformCapstone.lean`, 2107 lines). Gates: p = 2 recovers the W6 values 1/3 (plus
   the model-level tie `(M7 2).countingDensity = realMW6.countingDensity` for every σ);
   p = 3 certifies 1/4, 3/8, 3/8 (census-anchored); checksum = 1 at every p. Faithfulness:
   splitU masters axiom-free at general p (`OM/QpTypeSplitU.lean`, root-generic Hensel);
   axiom RE-SCOPE #6 (`OM/ChainMenu7.lean` splitU literals at fresh order-slot 3 —
   collision-safe vs the chain decoder — + `fiberOf7`; scope #5 derived back; split-keyed
   cones machine-checked CORE-ONLY per the redundancy requirement). External validation:
   `verification/census_n2_uniform.py` — per-family digit census EXACT at every (family,
   height, translate) for p = 2 and p = 3. Spine note: the capstone fires
   `MontesDataV2.countingDensity_eq_sum_coeff` (the decomposition theorem inside
   `goal_theorem_montes`) — the full spine theorem bundles palindromy/htameFE, excluded by
   this directive; the monic uniform densities are not palindromic, so no honest htameFE
   exists to supply. Guardian flags (all benign, recorded in the audit log): bibliographic
   pagination confirmation to carry; census stop-the-line is review-enforced (CI suggestion
   noted). Remaining beyond n = 2: the note's class-3/D1–D5 perimeter (n ≥ 3), order ≥ 2.
   **General-n START (2026-07-23, W8a landed):** Case E gate PASSED (count 3/64 exact in
   original coordinates; 36/36 type certificates (2,2)); D1-marginal PROVED (paper +
   Codex; `WILD_WAVE8_BLUEPRINT_2026-07-23.md` §1) and MACHINE-CHECKED
   (`OM/DevBijection.lean`: the unitriangular development bijection, the division
   identity, compatibility with `Development.develop` proved, the Case-E stratum count
   transported to original coordinates, kernel-decide gates at p = 2 and p = 3 — all
   core-only). OPEN: JOINT-D1 (depth-≥1 class-3 histories; non-import #12 — prove or
   carry conditionally); W8b (the (2,2) leaf master + axiom re-scope #7) is the named
   next lever.
   **Directive (Asvin, 2026-07-23): go for the GENERAL-n case and the complete theorem.**
   **Directive (Asvin, 2026-07-26): keep iterating on the MATH with Codex until either a
   COMPLETE math proof of wild uniformity exists or the current approach is shown
   conclusively to not work. Campaign ledger: `lean/notes/MOVES_2026-07-24.md`.
   MILESTONE (2026-07-26): **§B2-DEF — the MOVES tower induction — ACCEPTED** after 13
   adversarial passes (two consecutive CLEAN; all five pass-8 structural demands
   discharged; Case-K sealed gates: v1 failed-and-adjudicated, v2 all-pass). The
   general-n move ledger now rests on accepted §A + §B1 + §B2-DEF + JOINT-D1 + nine
   sealed gates. Next campaign units: §C (composition along read histories), the D4
   restatement, the assembly notes (menu finiteness, depth resummation, general-n
   squeeze), exhaustion tie-in.**
   MILESTONE (2026-07-26, the parallel campaign): **§C at rev 7** (kernel derived twice
   over — the C10B window derivation and the Case-L sealed gate, ALL 21 verdicts, the
   β-strip 760σ discriminant; sole remaining proof obligation = C.1.5, in derivation) and
   **the MOVES LEAN CORPUS: 50/61 units proved-clean** (core axioms only, 294
   declarations audited, 0 fence breaks; 5 semantic-audit rounds drove unsafe 39→5;
   3 statements machine-refuted and corrected; 5 units boundary-deferred to the specced
   graded-ring campaign — `lean/notes/MOVES_LEAN_FINAL_CENSUS_2026-07-26.md` +
   `MOVES_LEAN_BLUEPRINT_2026-07-26.md` R5.3). Evidence perimeter: E…L (ten sealed
   gates).**
   MILESTONE (2026-07-26, later): **§C ACCEPTED** (passes 12+13 consecutive CLEAN;
   13-pass arc; the pass-13 instance trace reproduced the sealed Case-L masses through
   the live apparatus). Certified: §A + §B1 + §B2-DEF + §C + JOINT-D1 + eleven gates.
   MILESTONE (2026-07-26, latest): **§D4-R ACCEPTED — the first assembly note** (the
   per-shape-prefix mass law; passes 5+6 consecutive CLEAN after a 1-crit + 3
   zero-critical spiral). Conditionality: accepted §C + §B2-DEF + the OPEN kernel
   D4R.0-K (offset-P totality; outcome exhaustiveness — derivation unit launched).
   **Gate D4-n3 PASSED** (sealed pre-census, FC1–FC9 documented, the note's pin = the
   seal by two-way convergence; all predictions exact at 4 configs; partition 0
   double-counts/0 orphans over 404,128,692 boxes). Twelve gates now. Assembly plan
   at rev 7 under structural passes (pass 7: 2 criticals, both interface-grade;
   [2a] SPECIES cleared for drafting). DUAL BAR results (2026-07-26, latest):
   **§B2-DEF DUAL-ACCEPTED** (Codex CLEAN + Fable CLEAN on identical D¹¹d text — the
   first section through the full standard). **§C PUNCTURED by its Fable pass**: 1
   CRITICAL — the realizability class (NA)+(HV) is incomplete, needs the independent
   span-entry condition (SAE); certified by an empty-stratum instance predicted 62500
   members; counting engine itself validated on a fresh species mix; + 4 gaps; repair
   queued. **§D4-R PUNCTURED by its Fable pass**: 1 CRITICAL — factor/side selection
   is not a function of f (two same-shape factors ⟹ equal strata for distinct
   prefixes; the D4-n3 gate structurally blind to it); sum-form mass law survives;
   branch-multiset repair (rev 6) in flight; plan rev 8 inherits. The dual bar is
   catching decorrelated criticals exactly as designed — three Fable passes, two
   fresh criticals that 6–13 Codex passes each missed, one clean confirmation.
   UPDATE (2026-07-27): **§C DUAL-ACCEPTED** (revs 12–14 added (SAE) +
   TRANSITION-ADMISSIBLE + the fence; Codex 16+17 clean + Fable confirm clean —
   F-EMPTY excluded live, new empty-stratum hunt found none). **§D4-R rebuilt on the
   branch-tree architecture** (T_can(f); SUM + EVENT laws with multiplicity; gate
   D4-m2 33/33 census-pinned the mult ≥ 2 regime at the refutation shape) and
   re-accepted at the Codex bar (passes 8+9); its Fable pass: 0 criticals, 2 one-line
   display gaps — dual acceptance imminent. D4R.0-K kernel derivation under its own
   spiral (Theorem A adoptable; grammar rebuild converging). ASSEMBLY PLAN at rev 10:
   [3t] TREE note (first-split recursion, certified sound given the new open kernel
   (SIB), whose SIB-gate census is running), verdict pin VP; FOUR notes cleared for
   drafting ([1] accepted, [2a] drafting, [1v]-COND, [3t]). LEAN: MovesC frozen layer
   23/23 PROVED-CLEAN (opus fleet, zero escalations, independently recompiled).
   UPDATE (2026-07-27, later): **§D4-R DUAL-ACCEPTED at rev 9** (Codex pass 11 +
   Fable confirm on identical text; the u* spiral-crossing repaired with the
   γ-blindness analysis and an explicit witness pair). **The D4R.0-K kernel
   derivation is DUAL-VERIFIED** (Codex SOUND + Fable CLEAN; grammar counterexample
   attempts all died at named clauses) — kernel parts (a)+(b) DISCHARGED; §D4-R's
   conditionality reduces to dual-accepted §C + §B2-DEF + the (c) verdict-pin
   residual (uniform detection cap, owned by the plan's [3t]/VP). **THREE artifacts
   through the full dual standard: §B2-DEF, §C, §D4-R.** §M-SPECIES (note [2a])
   drafted (catalogue bound (n+2)^{n²+3n+12} as corrected at §M rev 3; n=3 catalogue = 53 by hand; gate M-n3
   census running); its P̂ gloss carries a queued gap (the u* witness). Plan at rev
   10 (RS.1-DEEP/SH/MARKED routing; CL-1..16; tree-indexed (SIB) + depth-2 gate
   layer). Gates: 13 sealed + D4-m2 + SIB/M-n3 running.
   UPDATE (2026-07-27, latest): **THE ASSEMBLY PLAN IS SOUND** — pass 13: 0 critical
   obstructions after 13 revisions/passes (conditional on the honestly-listed open
   kernels: (SIB-STEP), XHD/HMC, (ns-null) verification, EXHAUST/ESCAPE/TRACK-COUNT,
   RS.1; rev 14 = three one-liner concerns). GATES: SIB-gate 32/32 (the product law
   census-exact; mechanism corrected to JOINT UNIMODULARITY — coordinate disjointness
   refuted); T-n3 21/21 (the first-split recursion exact both ways at depths 1+2;
   ONE-F dictionary exact); M-n3 content PASS (53-letter catalogue complete, 0 strays)
   with the realizability clause FAIL-as-sealed adjudicated (Case-K class; threshold
   repair at §M rev 2; v2 re-seal running). FOUR assembly notes in flight: §D4-R
   dual-accepted; §M-SPECIES rev 2 (pass 1 running); §T-ASSEMBLY rev 3 (passes: 8c →
   1c; the (ns-null) PROOF survived); §V-TABLES rev 2 pass 2: **NOT ACCEPTED
   (3 critical / 3 gaps)** — semilinear-overlap summation, ordinary-source
   disjointness in (iv)-MEAS, and VAL(b)'s XHD-free count-product status remain;
   V-n3 arithmetic checked, census not yet run.
   LEAN: MovesC fully ACCEPTED at audit round 6 (six-round spiral) — 23 frozen proved
   + the 13-unit fleet running. The campaign's remaining structural risk is
   concentrated in the named kernels, each with a live refuter.
   UPDATE (2026-07-27, latest): **§T-ASSEMBLY DUAL-ACCEPTED** (Codex pass 8 + Fable
   confirm on identical rev-7 text; the (ns-null) proof verified four times incl. two
   Fable break-attempt derivations; gates SIB 32/32 + T-n3 21/21) — the FOURTH
   artifact through the full dual standard (§B2-DEF, §C, §D4-R, §T-ASSEMBLY).
   **Gate V-n3 PASSED 178/178** (the [1v] tables + COMP-h dyadic mass, exact).
   §V-TABLES: math clean at passes 4+5 (0 criticals), record sweep in flight.
   §M-SPECIES at rev 4 (the census-vs-geometric coordinate shift being displayed as
   an isomorphism; SP-DAG's entrance-finiteness proof GENUINE). LEAN: **MovesC
   36/36 proved-clean** (the 13-unit fleet closed with zero failures, incl.
   thmC_a/b); the MovesGr bridge round produced machine-checked REFUTATION
   certificates for three design statements (vacuous/unprovable-as-stated) + one
   proved fragment; ONE item awaits Asvin's sign-off: the proposed `add_def` field
   on GradedRingStr (blueprint §8.1/§8.3 — the L1 statement is false without it;
   adding it breaks existing instances, so it is fenced). 18 sealed gates.
   UPDATE (2026-07-27, later still): **§V-TABLES DUAL-ACCEPTED** (Codex 6+7 + Fable,
   all clean on rev 7; the (U-A) proof survived six break vectors; tables exact at
   off-census q = 16/25) — the FIFTH artifact through the full dual standard.
   **§M-SPECIES ACCEPTED at the Codex bar** (passes 4+5 clean on rev 5; the
   two-coordinate-systems repair + the (τ-hen) n=1 adjudication; its Fable half
   queued behind the M-n3 v2 threshold re-seal, in flight). [2r] REL (assembly note
   5, the §T acceptance-event dependency) drafting. DUAL LEDGER: five artifacts
   dual-accepted; §M-SPECIES Codex-accepted; the plan SOUND. The math write-up's
   accepted perimeter now spans the moves ledger (§A/§B1/§B2-DEF), the composition
   theorem (§C), and four of the plan's assembly notes ([1], [2a] at Codex, [1v]-COND,
   [3t]) with every open kernel named, fenced, and refuter-equipped.
   UPDATE (2026-07-27, end of day): **§M-SPECIES DUAL-ACCEPTED** (Codex pass 7 +
   Fable on identical rev-8 text; the Fable side REBUILT the 53-letter catalogue from
   the definition alone, menu 7/7; gate M-n3-V2 PASSED N = 1..7 exhaustive with all
   45 fresh thresholds sharp both sides — the 19th sealed gate). **§R-LEDGER
   ACCEPTED at the Codex bar** (passes 3+4 on rev 3; the obligations ledger with the
   literal derives-nothing banner; its Fable half running). SIX artifacts through
   the full dual standard: §B2-DEF, §C, §D4-R, §T-ASSEMBLY, §V-TABLES, §M-SPECIES.
   NEXT FRONTS: [2b] XHD (the big prove-side note: the exact height-domain package
   that discharges [1v]-FULL), the plan's rev-15 sync batch (CL-8's (e) leg + count;
   the JOINT-D1 cross-cluster rewording at four lines), the [2a]/[3t] acceptance-event
   formalities, and the remaining kernels ((SIB-STEP), HMC, ESCAPE, WEIGHT-CHARGE,
   TRACK-COUNT, X-items) each with a named refuter.
   UPDATE (2026-07-27, final): **§R-LEDGER DUAL-ACCEPTED** (Codex 5+6 + Fable on
   rev 5; the Fable spiral caught and fixed the (EQ-2) refutation-stability defect
   with a per-position-class pin) — the SEVENTH artifact through the full dual
   standard: §B2-DEF, §C, §D4-R, §T-ASSEMBLY, §V-TABLES, §M-SPECIES, §R-LEDGER.
   **§H-DOMAINS ([2b]) drafted and in spiral** (pass 1: 9c/2g — the derivation-heavy
   note held to proof standards; H-LIST's slack/cone injectivity, the honest
   consumer-match rewrite, and a real seal for gate H-n3 are the rev-2 work; rev 2
   in flight). **PLAN REV 15 LANDED** (the sync batch: the §0 note-vs-event
   acceptance ledger with exact blockers — [1v]-FULL = [2b]'s four H.6 fences;
   [3t]-COND = the conditionality record only; CL-8 five REL.2 obligations; the
   four JOINT-D1 lines reworded to Montes-L1 authority; (ns-null) CLOSED; 19
   sealed gates; drafting ruling: [5] + [3]-COND cleared NOW, [4] not cleared). The write-up now has SEVEN dual-accepted artifacts + one note in
   spiral + two plan notes ([3] RESUM, [4] SQUEEZE + [5] EXHAUST) not yet drafted —
   those await [2b]'s package and the remaining kernels per the plan's DAG.
   UPDATE (2026-07-27, night — PLAN REV 16 LANDED, after the milestone entry
   below): the plan synchronized to the dual-standard milestone (§0 ledger →
   TEN note-accepted artifacts with event rows for [5]/[3]-COND/[2b];
   [1v]-FULL's blockers corrected to [2b]'s SIX H.6 fences; gate count TWENTY
   with H-n3 151/151). **THE [4] RE-RULING: [4] SQUEEZE CLEARED for
   CONDITIONAL drafting ([4]-COND)** — REV 15's blocker (undrafted [3]
   interface) is void with §S-RESUM dual-accepted frozen text; the [4]-COND
   spec addendum is at plan §1 (SQ.4 = Theorem U in the FULL HONEST FORM,
   capstone ledger now CL-1…CL-19 — CL-18 (J-RAT)/CL-19 (JC-INV) added per
   §S's plan-sync flags); THE UNRUN-CENSUS ROSTER consolidated at plan §7
   (12 rows, owners + blockers; rows 1–4 — STATE-probe-2, X-n3, STALL-,
   ESCAPE-probe — runnable now). Next drafting unit: [4]-COND.
   UPDATE (2026-07-28, the capstone census): **GATE RESUM-n3 PASSED** — the five
   R_σ hand-derived through the full solve MATCH the repo's independent records +
   the Kac-Rice moment, wild values included; 65/65 decided integers exact at both
   primes; PARI 0 mismatches; det(I−K_e) exact at pools q₀ = 2, 3, 4 (the per-pool
   E0/(REG-p) evidence); the checksum exact at every level. The assembled pipeline
   demonstrably computes the correct densities at n = 3. Event-ledger consequence:
   with STATE-probe-2 and RESUM-n3 both passed, the [3] acceptance event's sole
   remaining blocker is [1v]-FULL (the six §H fences). 22 sealed censuses.
   UPDATE (2026-07-28, the campaign completion): **THE WRITE-UP'S DUAL STANDARD
   IS COMPLETE** — every artifact incl. **§U-SQUEEZE/THEOREM U DUAL-ACCEPTED**
   (the theorem in the full honest form: one fixed R_σ ∈ ℚ(q) per type at every
   (REG-p)-satisfying prime incl. wild, Σ R_σ = 1, conditional on the complete
   displayed ledger; the (REG-p) separateness spiral closed with both verifiers
   concurring; the Fable side's numeric instances exact at p = 2, 3, 5 — its own
   wrong R(2) falsified live by the bracket discipline). STATE-probe-2 PASSED
   (the vtx-varying regime; the [2b]/[3] probe blocker discharged). 21 sealed
   censuses. The distance to the UNCONDITIONAL theorem is exactly §U.SQ.6's
   displayed list: the named open kernels + the event discharges, each fenced
   with a refuter. The goal's dual-verification condition is met for the entire
   drafted write-up.
   UPDATE (2026-07-27, night — THE DUAL-STANDARD MILESTONE): **TEN artifacts
   through the full dual bar — the ENTIRE math write-up drafted to date passes
   BOTH Codex and a fresh Fable instance clean on identical text**: §B2-DEF, §C,
   and all seven assembly notes incl. **§S-RESUM DUAL-ACCEPTED** (the final one:
   the Fable confirm's rebuilt 9,494-outcome census — routing exhaustive/exclusive,
   the (K-SUB) partition exact, (SCS) 0 violations). Twenty sealed gates, all
   passing. The dual bar caught six decorrelated criticals across the campaign.
   Remaining to the full Theorem U write-up: the [4] SQUEEZE note (the plan's
   re-ruling next, with [3] note-accepted), the unrun census layers (X-n3,
   RESUM-n3, STALL/ESCAPE), and the named open kernels — each fenced with a
   refuter. Earlier same-day entry follows:
   UPDATE (2026-07-27, night): NINE artifacts through the full dual standard —
   **§X-EXHAUST DUAL-ACCEPTED** (the [5] note: the explicit index table with two
   Fable censuses totaling 6,181 polynomials at 0 violations; WEIGHT-CHARGE and
   the X2 kernels honestly open) and **§H-DOMAINS DUAL-ACCEPTED** (the [2b] note:
   the H-LIST construction survived SIX break campaigns, the last a 409/409
   attack suite; gate H-n3 151/151 with the factorpadic oracle; the [1v]-FULL
   blockers = its six fences, displayed). **§S-RESUM ([3]-COND) in its final
   round** (Codex-accepted; the Fable pass 0-critical; a wording resolution on
   the single-child size clause + the dual shot remain). GATES: 20 sealed, all
   passing. Remaining after §S: the [4] SQUEEZE note (Theorem U's closer, gated
   on [3]'s solve), the unrun census layers (X-n3, RESUM-n3, STALL/ESCAPE
   probes), and the named open kernels — each fenced with a refuter.
   REMAINING to the complete wild-uniformity proof: the D4 restatement, the assembly
   notes (menu finiteness, depth resummation, general-n squeeze), exhaustion tie-in.**
   Honest gap statement: the note's general-n architecture is conditional on JOINT-D1
   (+ D3/D5 at n ≥ 3; D2 = Lean vocabulary). Campaign method (per directive): attack the
   open lemmas MATH-FIRST with Codex as helper; when stuck, compute explicit small cases
   at the sticking point and diagnose; maintain semantic-guardian audits at every axiom
   change; keep going to the full theorem. Campaign artifacts live under the W8+ blueprint
   series; empirical gates in verification/ (Case E landed; Case F = the depth-1 joint-D1
   uniformity probe is next).
   PROGRESS (2026-07-22): **Wave 4 COMPLETE** (mixed-e types certified — σ = {(2,1),(3,1)} at
   n=5 certifies 1/512 through the real instance; axiom re-scope #3 with the per-family
   `fiberOf4` dispatch, guardian audit #4 ACCEPT). **The math ground truth is ACCEPTED**:
   `notes/MATH_FULLTYPE_DECOMPOSITION_2026-07-22.md` — six adversarial passes across two verifier
   models (defects 8→5→6→2→3→1); proved perimeter: the whole-window recenter–rescale staircase
   bijection (Lemma 2.3, general s/m/depth), the n=2 undecided envelope (pure counting), the class
   partition; the wall SIDESTEPPED (exhaustion via pointwise depth⟹disc + the elementary
   discriminant tail — no per-depth identities); class-3 (deg φ ≥ 2) apparatus = the explicit
   conditional W7 perimeter (joint-D1/D2/D3/D4/D5). **Active: Waves 5–6**
   (`notes/WILD_WAVE56_BLUEPRINT_2026-07-22.md`): the n=2 descent-tower capstones (W5a staircase
   bijection LANDED — `OM/RecenterBox.lean`) → the series assembly with the FIRST `hExhaust`
   discharge (n=2 envelope is pure counting, no new axiom) → `montes_unconditional_n2_full`: the
   first COMPLETE per-type density, machine-checked modulo the Montes faithfulness axiom
   (+ htameFE for palindromy).
   **W5b LANDED (2026-07-22, no new axiom, no sorry):** the n=2 depth-windowed DESCENT-CHAIN menu
   + real instance (`OM/ChainMenu.lean`, `OM/RealInstanceW5.lean`, `OM/RealInstanceW5Gates.lean`).
   Menu `omMenu5 n D K σ = omMenu4 ∪ chainLit`-literals (head order-slot 2; exact decode;
   n=2-only emission); counts = genuine `ChainCell` digit-fiber `Nat.card`s (W5a
   `stratumPairEquiv` iterated via `descendPair`; closed form `(p−1)^depth · leafCount`,
   thresholds exact); leaves = ram-rungs / inert (root-free pool `q(q−1)/2` counted via
   Sym2/Vieta) / two-sided split (note-§7 readability gate); coefficient
   `C5 = (q−1)^k·pool·q^{−(3Σm+eLeaf)}`; capstone `montes_unconditional_w5 (n D K)` verbatim-
   modulo, recovery `montes_w5_recovers` at D=0. Gates reproduce the §7 Case-A ledger ABSOLUTE
   values at p=2 (cluster-conditional × 2⁻²): Case C (1)→ram1 = 1/64 (count gate: 4 of 256 at
   N=4), (1,1)→ram1 = 1/512, (1)→ram3 = 1/512, (1)→inert1 = (1)→split1 = 1/256; depth-window
   growth 1/8 (D=0) < 9/64 (D=1) through the real `countingDensity`; C:=0 mutation refused by
   the compiler; external brute-force census re-verified all five masses at p=2 (N=8) and the
   closed form at p=3. HONEST SCOPE: counting-side only — chain-fiber TYPE faithfulness
   (translation invariance [COUNT] + Cor 1.20 in the recentered frame, boundary #5 pin) is
   **W5c** (next); the (D,K) window is a partial tower sum (W6 resums); odd-p even-height
   split-residual leaf deferred to W6 (pool empty at realP=2).
   **W5c LANDED (2026-07-22, guardian audit #5 PENDING before push): axiom re-scope #4 +
   the PROVED translation lemma + the full depth-1 chain-gate anchor.** The BLOCKING
   declaration gate was completed FIRST: boundary #5 (lift invariance) pinned verbatim as
   `notes/GMN_citations.md` §(P4) — (P4a) GMN §1.2's arbitrary-monic-lift scope (line 389 of
   the 2026-07-22 pdftotext extraction), (P4b) §1.5's explicit "types are not intrinsical
   objects… the data λ, ψ(y) depend on this choice" WITH the per-choice factorization +
   Cor 1.20, (P4c) the order-r analogues (Def 2.12 sequel, Def 3.10 remark), (P4d) the paper
   states NO translation-form invariance — that content is PROVED, not imported. New leaf
   `OM/QpTypeChain.lean` (core-only, no sorry): `qpType_translate_rescale` — a
   `QpFactorization` of `g` transports to `f` with the SAME `qpType` along
   `f(a·y+c) = a^{deg g}·g(y)`, ANY `a ≠ 0`, ANY degree (factor transport `affLift`; affine
   `AlgEquiv` irreducibility transfer; bundle transport `compData` with `L`, `O` literally
   unchanged); the box→genuine decode (`dvd_of_box_dvd`, `box_shift_cast`); and the FULL
   axiom-free anchor: `ChainCell [1] (ram 1)` fiber at `N ≥ 4` ⟹ recentered `g` genuinely
   Eisenstein ⟹ `f` IRREDUCIBLE over ℚ_p AND every `LocalFactorData` bundle forced to
   `efOf = (2,1)` (`chainGate_irreducible`, `chainGate_ef_forced`) — the target anchor at full
   strength. `om_leaf_faithful` re-scoped to `(D K) omMenu5 n D K σ` + `fiberOf5` (chain heads
   → the PROVED `ChainCell` counting fiber at the exact decode; else `fiberOf4`); W4c form
   DERIVED back (`om_leaf_faithful_w4`), W3c/W2 chains unchanged; witness
   `chainGatePoly = X²+4` (`p=2, N=4`; recentered read = the W1 gate witness `y²+2y+2`);
   probes: split-type AND fine-(e,f)-swap mutations at the chain gate both derive `False`
   against the axiom-free anchors (evidence block `OM/QpTypeChain.lean` Block 7b; real axiom
   in neither cone); positive coherence `chainGate_axiom_coherent`. Census: all capstones
   re-printed core-only (`AxChk_baseline` W5c section); faithfulness theorems = core +
   `om_leaf_faithful` exactly; full `lake build` green 2026-07-22.
   Non-imports with machine-checked reasons: finite-level drainage (FALSE
   of the truncated classifier — `Drainage.lean`), residual equidistribution (no GMN counterpart
   — `notes/M6_lemma.md`), translation-form GMN invariance (NOT stated in the paper — (P4d);
   PROVED instead as `QpTypeChain.qpType_translate_rescale`).
   **W6 LANDED (2026-07-22, leaf `OM/SeriesAssembly.lean`, 2333 lines, no new axiom, no sorry,
   ALL capstones Lean-core-only): the n=2 SERIES ASSEMBLY — the FIRST unconditional `hExhaust`
   discharge and the first FULL per-type density capstone.** The full counting model `realMW6 :
   CountingModel realP 2`: decided counts = order-0 separable cells + BOTH residue points
   (translate `f(x)↦f(x+c)` = `affineEquiv` at `(N,N)` — measure-exact) × ALL depth-`k ≥ 0`
   chains × all leaf kinds (including the depth-0 even-height inert/split cluster leaves NO
   earlier menu carried — structural finding: `omMenu5` covers one residue point and lacks
   those legs, so the W5 window family's `D→∞` limit is NOT the full density; the full model
   per blueprint §3 bypasses the Finset-menu spine, then re-enters `MontesDataV2` via
   one-marker-shape bookkeeping `realDW6` to reuse `goal_theorem_montes` verbatim).
   Key theorems (all pure counting, core-only): `cluster_covering` (the note-3.4′(a) decision
   tree: every cluster pair terminates in a menu leaf within budget or stalls at
   `v(a₀) ≥ B−1`, strong induction on the budget); `card_stallPair_le`
   (`≤ (p−1)^k·p^{L₁−Σm}`, `card_step` transport); **`undecided_envelope`:
   `undecided(N)/p^{2N} ≤ (⌊N/2⌋+1)·p^{−(N−1)}` for ALL `N ≥ 1`** (the note proved `N ≥ 4`;
   same constant) via the ≤-relaxed critical chain sum `msW_half_le` (`Σ_{ms}(1/2)^{Σm} ≤ D+1`);
   **`hExhaust_n2`** (envelope → 0); the value ties by two-sided squeeze — (U)
   `decided ≤ (1/3)·box` per type (the geometric fixpoint `msW_eighth_le : Σ(1/8)^{Σm} ≤ 7/6`
   closing EXACTLY at the full values) and `≥ (1/3 − envelope)·box` (box partition + (U) for
   the other two) — so `fullDecided_tendsto : → 1/3` per type. **Capstone
   `montes_unconditional_n2_full (σ) (hσ : σ.degree = 2) (htameFE)`**: (R) rationality of the
   closed forms `fullValueFn` (ram `1/(q+1)`, inert `q/(2(q+1))`, split `(q³−q+2)/(2q²(q+1))`
   — the p=2-complete tree; ledger match β_ram = q/(q+1)), (V) `realMW6.countingDensity σ =
   num(2)/den(2) = 1/3` per type, (P) palindromy conditional on `htameFE` (about `realFW6`),
   (B) **bracket-uniqueness UNCONDITIONAL — `hExhaust` supplied by `hExhaust_n2`, the first
   full-density clause fired outright**. Gates: `gate_w6_{ram,inert,split}_full = 1/3`,
   `gate_w6_checksum` (sum = 1), window comparisons (`1/8, 9/64 < 1/3`), `w5_window_mono`
   (W5 family monotone in D), `decided6_mono` (level-window monotone), C:=0 mutation refused
   (evidence block), `AxChk_baseline` re-run UNCHANGED. HONEST SCOPE: counting-side digit
   fibers — σ-keying of the translate fibers and the depth-0 inert/split cluster leaves is
   DEFINITIONAL here, outside W5c's declared axiom scope #4 (a W6c-style faithfulness scope
   extension is required before calling the full model's keying Montes-faithful —
   **CLOSED by W6c, next paragraph**); the
   `q`-uniform family omits the even-height split-residual family (pool `(q−1)(q−2)/2`, empty
   at the real prime q=2), so at general q the split form is NOT the true split density
   (difference `(q−2)/(2q²(q+1))`); palindromy remains exactly the content of `htameFE`
   (whether `htameFE` holds at `realFW6` is NOT established — the capstone is conditional on
   it, per the standing endpoint boundary). Python cross-check dispatch values are in the
   module docstring (per-type limits 1/3; envelope at N=9 ≤ 5/256; per-stratum anchors).
   **W6c LANDED (2026-07-22, guardian audit #6 ACCEPT-WITH-FLAGS, all flags adjudicated
   benign; leaves `OM/QpTypeLeafMasters.lean`, `OM/QpTypeChainAll.lean`, `OM/ChainMenu6.lean`,
   `OM/FullFaithful.lean`, `OM/FullFaithfulGates.lean`; blueprint
   `notes/WILD_WAVE6C_BLUEPRINT_2026-07-22.md`, math §1 Codex-verified over 3 adversarial
   passes 4 gaps → 1 gap → CLEAN): the scope-#5 faithfulness extension — W6's named honest
   gap CLOSED.** `FullFaithful.fullFiber_hasType`: every genuine monic quadratic in ANY
   counted fiber of `realMW6`'s decided count (order-0 sep cells; `TransChain c ms leaf` at
   both residue points, all depths, all leaf kinds) has a genuine ℚ₂-factorization of the
   keyed type — footprint core + `om_leaf_faithful` EXACTLY; the split-keyed legs are
   axiom-FREE (`fullFiber_split_hasType_axfree`). Machinery all PROVED core-only: the three
   leaf masters at ALL parameters (ram: every odd H — two-root ultrametric irreducibility +
   every-bundle (2,1) forcing, the H=3 parity argument generalized; inert: every m ≥ 0
   including the order-0 sep cell, (1,2) forced, the sep-inert classify glue proved via the
   banked `Order0.classify_eq_sepShape_iff`; split: every k ≥ 0 including b₀ = 0, full
   Hensel certificate), the general-m tail-generic step decode (erratum recorded: the
   staircase invariant L₀ ≤ L₁ is required), the chain unwind composing each chain into ONE
   affine relation, and the c=1 translate reduction DERIVED via the proved transport — per
   the (P4d) discipline no translation content enters the axiom. Axiom re-scope #5 = pure
   menu widening (`omMenu6` admits the depth-0 `chainLit []` literals; fiber dispatch and
   conclusion byte-identical; per-literal GMN statement map incl. the b₀ = 0 split case in
   the docstring; scope #4 derived back as `om_leaf_faithful_w5`). Gates: four externally
   cross-checked witnesses (depth-0 inert x²+2x+4 — a literal on NO earlier menu — depth-0
   split x²+2x+8, c=1 translate x²−2x+5, general-m chain x²+16 at m=2), both wrong-keying
   mutation probes derive False against the axiom-free forcing (real axiom outside both
   refuter cones), positive coherence gate through the new depth-0 menu leg, and the
   capstone companion `montes_n2_full_faithful` (capstone conclusion verbatim ∧ the
   faithfulness clause; capstone itself untouched). Census byte-identical on all 600 prior
   entries; every capstone still Lean-core-only. Honest limits UNCHANGED by W6c: the q>2
   even-height split-residual family (empty at q=2) and palindromy = `htameFE`.
2. **Order ≥ 2 (deep wild).** Classifier faithfulness is at order ≤ 1; the higher-order OM tower is
   in progress (§4).
3. **The trusted citation base.** Fully unconditional would require *proving* the cited axioms in Lean.
   The Denef–Igusa cell recursion (`AX_cellRecursion`) is known-hard and is the honest citation
   boundary; the GMN and Del Corso–Dvornicich inputs are literature results ported faithfully.

- **What is genuinely done now:** a `p`-uniform rationality *engine* (all primes, wild included) and a
  real *order-0* density theorem, plus the formalized OM classifier (§2). Palindromy is proved as a
  *transfer* mechanism but only ever fed an *assumed* tame functional equation — it is not yet
  established for a constructed real density. NEW (W6, 2026-07-22): at `n = 2, p = 2` the FULL
  decided tower is machine-counted with a PROVED exhaustion envelope (`hExhaust` discharged, no
  axiom) and per-type full densities `1/3, 1/3, 1/3` tied to closed rational forms — the first
  complete per-type density value — and since W6c (same day) the σ-keying is Montes-faithful in
  EVERY counted fiber (`FullFaithful.fullFiber_hasType`, core + `om_leaf_faithful`; split legs
  axiom-free); palindromy still conditional on `htameFE`.
- **Honest one-line status (updated 2026-07-22, post-W6q):** at n = 2 the DIRECTIVE TARGET is
  machine-checked, Lean-core-only, at every prime: `montes_uniform_n2` — one fixed rational
  function per type computes the full counting density at ALL primes including the wild one,
  exhaustion discharged, faithfulness modulo the one Montes axiom (split-keyed legs
  axiom-free). Palindromy is out of scope by directive. Beyond n = 2, the general-n statement
  awaits the note's class-3/D1–D5 perimeter and the order ≥ 2 tower — the *mathematics* is
  complete modulo the published Montes/GMN algorithm at n = 2 unconditionally and conditional
  on D1–D5 beyond; the *Lean* general-n content remains the p-uniform engine + the order-0
  real theorem.

Canonical math notes (blueprints, audits, negative results) live in the companion `uniform-rationality`
project; the copies in `docs/` here are snapshots sufficient to reconstruct this Lean state.

## UPDATE (2026-07-28, THE LEAN FORMALIZATION CAMPAIGN — Theorem U machine-checked)

The wave-1/2/3 campaign (master plan: lean/notes/LEAN_FORMALIZATION_CAMPAIGN_2026-07-28.md)
converted the dual-accepted assembly notes into audited Lean blueprints and began proving.
Milestone: **`LeanUrat.MovesU.theoremU` and `.identification` are PROVED** (13/13 fleet,
zero sorries in LeanUrat/MovesU, footprint = Lean core only, verified post-rebuild).
CONDITIONALITY (named per the honesty invariant): this is the dual-accepted CONDITIONAL
Theorem U — quantified over typed interface structures (ClassifierSpec, SolveData,
RegData/RegP, FiberSeries) and the CapstoneLedger (CL-1..19 as hypothesis fields incl.
VP-SOUND); the identification clause (ii) is VP-SOUND-conditional. The interfaces are
degenerate-instantiable at the declared D9 boundary — the REAL instantiation is the
remaining campaign: MovesX (dual-accepted, fleet running), MovesS/MovesSp/MovesD (audit
spirals converging), MovesT/MovesV (wave 4), HC-1 (B2 tower induction), HC-2 (the
JetSetup/classifier bridge). Do NOT describe this as an unconditional density theorem;
it is the note's Theorem U, checked. Also: MovesR parked (its §C-pointer layer awaits
HC-1's carriers; Witt base layer split to MovesRBase, fleet running); ONE note erratum
found and dual-confirmed (the §M-SPECIES [R4/R5 rows] bracket omits R6 — record at the
end of MOVES_2026-07-24.md).

## UPDATE (2026-07-28b, the proved corpora)

Fleet results, all statement-fenced and footprint-verified post-rebuild (Lean core
only): **MovesU 13/13 (THE conditional Theorem U + identification)** ·
**MovesRBase 7/7 (the Witt base layer)** · **MovesSp 67/67** (the §M-SPECIES
catalogue: |catalogue| = 53, SnRaw3_eq closure, menu3_exact_global, loops,
exclusions, rosters — all kernel-`decide`d, native_decide banned throughout) ·
**MovesX 38/40** (§X-EXHAUST incl. the ballCover kernel-timeout repair; the two
envelope units were KERNEL-REFUTED as first stated, adjudicated as blueprint
over-strength against the note's own (N−1−c_cap) display, restated with ∃N₀ and
D9-rebound constants, now in prover hands). MovesS (95-unit core) and MovesD
(rev 8) are in their acceptance passes. Conditionality discipline unchanged: all
of this is the statement/derivation layer over typed interfaces + the CL ledger;
instantiation = the remaining campaign (waves 4–5, HC-1/HC-2).

## UPDATE (2026-07-28c): MovesX COMPLETE 40/40

XE.2/XE.3 proved in their refutation-hardened forms (∃N₀ + D9-rebound constants;
Lean-core footprints). Four campaign corpora now FULLY PROVED: MovesU 13 (Theorem U),
MovesRBase 7, MovesSp 67, MovesX 40 — 127 units, plus MovesC's 36 pre-campaign.
MovesS (95) + MovesD (48) cores in E-phase; HC-1/HC-2 blueprints being written;
the 9-unit Moves tail under Fable provers.

## UPDATE (2026-07-28d): PHASE-3 ROUND 1 — the hard cores mapped

HC-1 (the §B2-DEF tower induction): ~40/50 PROVED including the carry algebra,
the base stages, LST/TYP/DOM AS THEOREMS over the real carriers (C1–C5), the
child laws S2–S8 (partial), the anchored-substitution/landing spine S14–S16,
and ALL FIVE sealed decide-gates (Case-J, Case-K with the corrected d₀ = d₁²
pairing, DIV, carry, span). Seven mapped obstructions with machine-checked
kernels (T10's conjunct-2 refutation, C6's card-K bridge, S7's CoeffLocLaw(c),
S8's twist symmetry, S9's assembly core, S13's SOURCE-MISMATCH vs D.9(d) —
math adjudication queued, S17 mirroring the known measureExact holes); three
units interrupted mid-attempt (D7/S10/S11, elaborating, honest sorries).
HC-2 (the JetSetup bridge): the reads layer + both fireable order-0 gates
PROVED (U19/U23/U24/U28/U31 + the mkFresh chain); the PresentSeed Defs
inconsistency FOUND BY REFUTATION and REPAIRED with the note's own (ZC-c)
guard (closure artifact green); the seed chain awaits its re-fleet; nine
sharpened interface obstructions on record. NO AXIOMS ANYWHERE in either core
(all three GMN proposals resolved as hypotheses pre-declaration).
QUEUED NEXT WAVE: the S13 adjudication; the HC-2 seed-chain re-fleet;
D7/S10/S11 re-attempts; the post-Aug-02 Codex ratification batch; wave 4
(MovesT/MovesV — unlocks all 22 seam-contract entries); MovesR unparking via
HC-1's R-layer.

## UPDATE (2026-07-28e): THE HARD CORES AT THREE KERNELS

Under Asvin's definition-change authority (Codex-confirmed batches; acceptance =
proofs run through), the campaign closed the hard cores to THREE remaining
mathematical items, each with a machine-checked obstruction record:
(1) THE CARRY BRIDGE at non-recentering reads — one identity appearing as both
HC2.K1_readVertexPin_nonrec and HC1.V9.R3b; the V-prime kernel (§10, Codex 0-crit)
proved everything around it (V1-V4, V6-V8 incl. the one-step OM residual
homomorphism, S9a/S9b guarded+proved per the note's e·g>1 display, the coset hS6a
restatement acceptance-passed across a 15-file ripple);
(2) U21's HV gap (a certified-structural interface item);
(3) S9c's core assembly.
Everything else in HC1+HC2 is PROVED with Lean-core footprints. Adjudication
tally for the whole campaign: EVERY kernel refutation traced to blueprint or
elaboration over-strength; the note survived all of them (latest: U18's
EtaGalEq keying traced to a blueprint-rev origin — the note counts the
witnesses as distinct etas; S9a/S9b's corner = the note's own e·g>1 guard;
hS6a = the note's coset display). U18 proved under the faithful transport form.
The wave-4 (MovesT/MovesV) and seam re-keying program is unchanged and fully
recorded. 550+ commits, all local.

## UPDATE (2026-07-28f): S9c CLOSED → S9 (the D.7 TRANS capstone) PROVED

Kernel (3) of update 2026-07-28e — S9c's core assembly — is CLOSED, and with it
the parent S9_transStage: every legal INCREMENT read (`e·g > 1`) of a cored
stage produces a cored child with the full round-5 transition record. Both
gained the adjudicated note guard `hEG : 1 < σ.e * g` (MOVES 3755–3757; the
S9a/S9b restate-after-refutation precedent applied verbatim — their unguarded
conclusions CONTAIN the refuted S9a shape; in-file machine-checked corner
kernels `S9c_ungated_corner_refuted` / `S9_ungated_corner_refuted`). Suppliers:
the S9a/S9b guarded literal + the S9w lawful carrier (w_jump/R_neg from
`ChildResLaws`), S11a's seven non-twist legs, S9d's pin bridges — plus two NEW
generic in-file lemmas in S9c's file: `tvecLaw_of_tvecUnitLaw` (the round-4
TvecLaw shadow follows from K1's pin-derived TvecUnitLaw by bare Stage laws)
and `coeffCore_of_stage` (ALL of CoeffFieldLawCore from bare fields +
wPrev_mul; clause 3's exponent group hits −1 = −(e·s+h·t) on an hS6b realizer
pair — supersedes the §9.5 "L4_TRANSvii_R4 + S6" plan). Footprints Lean-core
(zero axioms, zero sorry); full `lake build` green (8579 jobs);
AxChk_baseline: no regression, zero sorryAx. Remaining HC-1 sorries: C6
(card-K bridge leg), R6 (carrier instance), V9/R3b (the carry bridge — kernel
(1), in flight). MANIFEST units 34/39 updated.

## UPDATE (2026-07-28g): R3b ADJUDICATED — the carry bridge does NOT close from
## the fenced pool; the missing display is D.8-(TRANSPORT)'s upward FORCED WINDOW

Kernel (1) of update 2026-07-28e (the carry bridge = HC1.V9.R3b =
HC2.K1_readVertexPin_nonrec) ran its dedicated escalation round. Outcome: NOT
closed — with the obstruction now EXACT and partly machine-checked. (a) The
REDUCTION is proved, Lean-core, in `HC1/V9_K1nonrec.lean`
(`V9_wvEqStretch_of_bottomSlot`, `V9_bottomSlot_of_wvEqStretch`,
`V9_steepSide_frameDescent`): R3b ⟺ the BOTTOM-WINDOW LAW — the vertex
coefficient B_μ's own σ.Φ-development attains its σ.w slot-min at inner slot 0.
(b) A sympy-verified COUNTERMODEL (f = (X+8)(Φ̂²+8X³), (1,1)-Gauss frame at X,
read pair (1,2), Φ̂ = X²+4X+16: side gam = 10 on slots {1,3,5}, pattern ψ²,
μ = 2, B₂ = X+16 with σ.w = 1 < 2 = target) shows R3b is NOT derivable from
SideReads(i)+(ii)+(vi) + hOrd/hAnchor + the PROVED V-frame engine (V1–V4) +
hStretch/child_slotmin — clause (vi) HOLDS on the witness (digit equations
carry no weight content); the sole violated ReadsOf clause is SideReads(iii)'s
`σ.R f` rendering, the U31-fenced seam V9 is charged not to consume (at every
steep read, (iii) is conspiracy-or-vacuous — seed lemma
`V9_steepSide_frameDescent`). (c) THE FINDING: the display R3b needs is §B2-DEF
D.8-(TRANSPORT), UPWARD leg, the FORCED-WINDOW clause (MOVES 2521–2528), re-run
at the regraded frame — blueprint §10.1 fenced (TRANSPORT) out of V4 as "not
needed by any of the three discharges"; that fencing is WRONG for V9. The
dedicated follow-on unit = transcribe D.8-(TRANSPORT) at the ReadFrame; R3b
then closes via the proved reduction (boundary caveat t★ = 1 ∧ h★ − e★σ.h = 1
recorded in the REV-3 block). R3c (the root e·g = 1 corner) unchanged. Full
records: `HC1/V9_K1nonrec.lean` REV-3 block (at the sorry) and
`HC2/K1_vertexPin.lean` obstruction item 5. Both files compile; footprints
verified (new theorems Lean-core; sorries unchanged: exactly the two kernels).

## UPDATE (2026-07-28h): V10 (TRANSPORT) transcription — the recorded read-transition
## is INCONSISTENT at steep reads (machine-checked); K1 kernel wired; R3c corner remains

The REV-3 follow-on unit landed: `lean/LeanUrat/HC1/V10_transportWindow.lean`
(zero sorry, Lean-core; the §B2-DEF D.8-(TRANSPORT) UPWARD FORCED-WINDOW display,
MOVES 2520–2528, quoted verbatim).  Its machine-checked content is NOT transport
mathematics but an INCONSISTENCY FINDING about the recorded semantics:

* `V10_forcedKeyWeight` + `V10_readTransition_incompatible` (both Lean-core,
  zero axioms beyond core): HistoryCoherent's round-3 keying of `TransitionCoreL`
  at the READ pair `(ν.e, ν.h)` on the READ lift contradicts the child stage's own
  laws whenever `ν.e·ν.g ≥ 2` — first `ν.h = ν.e²·ν.g·σ.h` is FORCED
  (`Φ^{e★g} = Φ̂ − τ` weighed by hwmul+hStretch vs child_slotmin; the read lift is
  read-equal-weight, not frame-equal-weight), then `σ′.R Φ̂ = T 1` (hRΦ + the
  recorded `σ′.s` tie) clashes with `C(c^g)·T 0` (hRlt/hRmul/hS5′).  CONSEQUENCE:
  `ReadsOf` records NO steep increment with a successor — the K1 kernel
  (U20a/U20b/U22-E2's supplier) is VACUOUS at its intended hard perimeter.  This is
  a flagged FAITHFULNESS BUG in HistoryCoherent (named sign-off item: re-key the
  child at the regraded side value `Φ̂ ↦ e★·(e★h★g)`; add a 2-node ReadsOf gate —
  U31's single-node gate never probed this).  S9's frame-pair transitions are
  UNAFFECTED (the same computation is consistent there).
* `V9_K1nonrec` is now proved at every leg except the R3c corner
  `i = 0 ∧ ν.e·ν.g = 1` — the ONE remaining sorry of the K1 cone.  Corner records
  are consistent; the honest g = 1 landing needs StageCore-grade tie laws (w_jump,
  unrecorded by ReadsOf) or SideReads(iii) (the U31-fenced seam — faithful at
  single-side reads per the fence's own text).  Full record: V9's REV-4 block.
* `HC2.K1_readVertexPin_nonrec := HC1.V9_K1nonrec` WIRED (statement-verbatim, the
  recorded delegation; import direction reversed).  Downstream footprints after a
  full green `lake build` (8579 jobs): V10's three theorems Lean-core;
  K1_readVertexPin{,_nonrec}/K1_NA_transport_*/K1_SAE_vertexEq_endpoint/U20a/U20b/
  U22E2/readsOf_NA/readsOf_SAE = sorryAx via the corner (readsOf_SAE also via
  U22E1's own sorry) — downstream Lean-core-clean: 0/10, unchanged in kind; the
  obstruction perimeter shrank from {R3a, R3b, R3c} to {R3c corner}.
* R3b DISPOSITION: closed by emptiness of its perimeter (the reduction lemmas
  `V9_wvEqStretch_of_bottomSlot`/`V9_bottomSlot_of_wvEqStretch` remain the
  interface for the eventual honest transport after the keying repair).  The r3b
  countermodel cannot extend to `ReadsOf` (satisfies the forced key-weight
  equation, dies at the position clash); SideReads(iii) consumed NOWHERE
  (⚠ fence respected).  Numeric mirror: `verification/v10_transition_check.py`.

⚠ HONESTY: never describe the K1 kernel/U20a/U20b/U22-E2 as machine-checked
transport results — at present their `e·g ≥ 2` content is vacuous-by-inconsistency
and their corner content is open.  The V10 unit's own docstring carries the same
disclosure.  Records updated: HC1/HC2 MANIFESTs, HC1 blueprint §10.8,
`notes/SEMANTIC_AUDIT_LOG.md`.

## UPDATE (2026-07-28i): R3c CORNER CLOSED — V9_K1nonrec is sorry-free, Lean-core;
## the K1 kernel cone (K1 total, U20a/b/c, readsOf_NA, U22-E2) is Lean-core clean

The one remaining sorry of the K1 cone — V9's R3c corner `i = 0 ∧ e·g = 1` — is
PROVED (`lean/LeanUrat/HC1/V9_K1nonrec.lean`, REV-5 note + the `V9CornerHelpers`
toolkit).  The REV-4 adjudication ("needs StageCore tie laws (w_jump) or the
fenced SideReads(iii)") is SUPERSEDED: neither is consumed.  Three
corner-specific mechanisms close it from the records alone:

1. **K1 is the cross-slot jump law at the corner.**  Both keys have degree 1, so
   every sum in sight is a development with CONSTANT coefficients at distinct
   slots; `TransitionCoreL.child_slotmin` pins the weight of every sub-sum
   (`v9c_subsum`), so the hRadd/hRlt chains (`v9c_Rsum`) run with no `w_jump`.
2. **The binomial transport at the degree-1 keys** (`v9c_slotmin`): `Φ = Φ̂ − t₀`
   re-expands any σ.Φ-development as a σ'.Φ-development with constant
   coefficients (the coefficient space is multiplication-closed exactly at
   degree 1), transporting the READ functional's slot-min to the parent key —
   the S10/D.10 recentering mechanism WITHOUT `StageCoreL`.  With SideReads
   (i)+(ii) this forces `σ'.w f = gam` and the two residual computations
   `σ'.R f = Σ_{m∈M} C(β_m)·T(m) = Σ_k C(b_k)·(T1 − C ĉ₀)^{s0+k}` — the (★)
   polynomial identity, via `toLaurent` injectivity.
3. **The frame-unit twists cancel.**  `child_dig_frame`'s unknown `z̄^{mfun w}`
   factors are eliminated by cross-multiplying its two instances at the SHARED
   weight `σ.w(B₀ s0) = σ.w(B₀(s0+k)·t₀^k)` (mfun is quantified before the
   elements — the round-5 per-index coherence is exactly what fires), and the
   (S5) positions collapse by the σ.e-cleared `hStretch` identity
   `wPrev(B₀(s0+k)) + k·wPrev(t₀) = wPrev(B₀ s0)`.  The μ-coefficient of (★)
   becomes `unit · Σ_k pat k·z̄^k·C(s0+k,μ)` — the μ-th Taylor coefficient of
   `X^{s0}·Ranch` at the recorded root `−c₀` — NONZERO by `ν.hOrd`
   (`v9c_taylor_ne`: Hasse-derivative nonvanishing at an order-exactly-μ zero;
   mathlib `Polynomial.taylor`/`coeff_X_add_C_pow`).  Hence `μ ∈ M`: both
   conjuncts of the kernel's conclusion at once — clause (vi)/`vtx` is not
   even needed.

Discipline: statement verbatim (fence intact); SideReads(iii) consumed NOWHERE;
ZERO new axioms; `#print axioms LeanUrat.HC1.V9_K1nonrec` =
`[propext, Classical.choice, Quot.sound]`.

Downstream cone (fresh oleans via explicit `lake build` targets — NOTE lake's
up-to-date check silently skipped the changed file twice on this NFS; the
stale-olean discipline caught it):
* Lean-core CLEAN (previously 0/10 via the corner's sorryAx):
  `K1_readVertexPin_nonrec`, `K1_readVertexPin` (TOTAL), `K1_NA_transport_root`,
  `K1_NA_transport_increment`, `K1_SAE_vertexEq_endpoint`, `NA_transport_root`
  (U20a), `NA_transport_increment` (U20b), `NA_transport_recentering` (U20c),
  `readsOf_NA` (U20), `SAE_vertexEq_endpoint` (U22-E2) — **10/10**.
* Still sorryAx, NOT via this kernel: `SAE_spanStrict_endpoint` (U22-E1's own
  sorry), `readsOf_SAE` (via U22-E1), `readsOf_realizable` (via U21/U22's own
  sorries).
* Trusted-base census (`AxChk_baseline`) re-run: no footprint regression; the
  M9 capstone `montes_unconditional` unchanged Lean-core.

⚠ HONESTY (unchanged in kind from 2026-07-28h): the `e·g ≥ 2` legs of the K1
kernel remain vacuous-by-inconsistency (the V10 finding — the HistoryCoherent
child-keying repair + 2-node gate is still the open sign-off item).  What is NEW
is that the corner leg is now honest transport mathematics: at `e·g = 1` the
records are consistent and the vertex pin is DERIVED, so `readsOf_NA`/U20a-c and
the K1 kernel are non-vacuously proved exactly on the recentering-shaped
(root, e·g = 1) perimeter, machine-checked end to end.

## UPDATE (2026-07-28j): THE HARD-CORE PROGRAM COMPLETE TO THE QUEUE

The carry bridge (R3b/R3c) CLOSED — V9_K1nonrec sorry-free Lean-core; the K1
vertex pin TOTAL; downstream 14/14 clean (K1 family, U20a/b/c, U22 chain incl.
both endpoints, readsOf_NA/SAE). S9 (the full TRANS child) PROVED. Every
remaining sorry in HC1+HC2 is one of ASVIN'S THREE QUEUE ITEMS:
(Q1) the HistoryCoherent child re-key at the regraded value + 2-node ReadsOf
gate (the V10 inconsistency finding — repairs steep-read vacuity; frozen
MovesC interface); (Q2) U21's RunVertexPin (the D.7(v)-warranted
child_dig_frame pin; frozen interface); (Q3) C6's restatement over the
alignment class (machine-certified mistyping; ScratchC6.lean the certificate)
— or wave-4-owned (R6's carrier instance, the seam contracts). The V10
inconsistency finding and the C6 mistyping certificate are the campaign's
standing interface findings of record. Wave 4 (MovesT/MovesV) is the next
program phase; MovesR unparks behind HC-1's now-real carriers.

## UPDATE (2026-07-29a): RATIFICATION PASSES ON THE PROVED CORPORA + WAVE-4 ROUND 6

The Codex budget window rolled over early (15% used), so the deferred
fresh-context RATIFICATION passes over the AS-BUILT MovesS/MovesD statements
ran ahead of schedule. Outcome: 10 criticals + 1 gap across both — on
statements, not proofs. Orchestrator adjudication by direct note reads:
**two overruled** (the γ-tie STR factor is the documented stage-vs-absolute
scale convention, C.1.0(c); the PrefIdx "image quotient" is the deliberate
η-granularity design with PresentNorm as the typed dictionary), **eight
accepted** — nearly all instances of the campaign's own doctrine (ledger pins
as comments instead of typed fields; one literal vacuous `Prop` tag; the
∅-shape event unwired; a silently strengthened pool burden). The three prior
MovesS adjudications survived independent re-judgment (one sharpened). All
repairs are APPLIED and green (7 new files, zero sorry, Lean-core; the N2
sealed gate stays proved; statement fence git-diff-verified): notably
`RS4Chain.wsh17_pin` is now a projection-def = the typed `W17ii` production
core, W4-4/W4-5 are typed Lean objects (`NPIDPin`, `OffsetPPin`), and the
classifier-side sealed-gate numbers are typed obligations
(`G2_gatesClassifier`). Interface deltas: `lean/notes/W4_SYNC_DELTAS_2026-07-29.md`.
Wave 4: REV 6 of both blueprints landed (MovesT's joint-unsatisfiability fix
verified by full 2⁹ enumeration; MovesV's SelRankTie replaced by a
definitional SelMatches; HMC stays open, its record line honestly scoped).
IN FLIGHT: the consolidated Codex confirm on the repair diff + full-dual
round-6 audits. Ledger: `lean/notes/LEAN_FORMALIZATION_CAMPAIGN_2026-07-28.md`.

## UPDATE (2026-07-29b): WAVE-4 BLUEPRINT PHASE COMPLETE; E-PHASE LAUNCHED

The MovesT (§T-ASSEMBLY, 55 units) and MovesV (§V-TABLES, 100 units) blueprints
closed at REV 9 after nine dual-audit rounds (Codex + fresh Fable each round,
every mathematical-content finding converged or resolved by orchestrator note
reads). The campaign's deepest design question — whether the interface must
exhibit a ¬HMC ∧ HMCAug separation witness — closed by focused fresh-context
adjudication, verdict (A): the obligation is withdrawn; three coupling
mechanisms are structurally barred (zc by extension-preservation; history-rich
carriers by the note's own XHD-u representative uniformity; census-level by the
assign_cover/tgam_last forcing chain), the interface is faithful and unchanged,
and the recorded limitation — under the exactness + uniformity package the
purported coupling may have no model — is CONSISTENT with the note, which
states the HMC-AUG repair conditionally and never exhibits a coupling (R2's
wall channel is its escape). HMC remains OPEN and unprovable (repeated
closure sweeps). Along the way the ratification arc on the PROVED MovesS/
MovesD corpora fully closed (three Codex confirm rounds; every thread
repaired-and-confirmed, overruled-with-machine-checked-seals, or terminated at
a NAMED vocabulary boundary with an owner — see W4_SYNC_DELTAS, 11 entries).
E-phase writers for both corpora are IN FLIGHT (the compiler as closure
arbiter; the census-level ¬HMC toy becomes decide-checked Lean; dual
ratification then runs on as-built statements). Ledger:
lean/notes/LEAN_FORMALIZATION_CAMPAIGN_2026-07-28.md.

## UPDATE (2026-07-30a): WAVE-4 PROVING CAMPAIGN — THE CONVERGED STATE

Three fleet rounds + three adjudicated-repair rounds after E-phase: ~140 of the
155 wave-4 units are PROVED (Lean-core; zero new axioms; the trusted-base
census clean throughout). Machine-checked highlights: the ¬HMC census toy
(V4_hmc — the campaign's central open kernel now has a kernel-checked openness
witness); both V1 full-bundle satisfiability witnesses; the complete T-C
ladder (cap/ns pricing/nullity); the composition chain (comp_h/comp_hsum)
fully Lean-core; rootTable_census proved for EVERY finite field (stronger
than the nine sealed points); D11's fiber disjointness. Fifteen
statement-level defects were caught by the fence at proof time — every one
refuted with a compiled countermodel or machine-verified analysis, adjudicated
with note/blueprint reads, repaired, and re-proved.
THE IRREDUCIBLE REMAINDER (all named, owned, analyzed at their sorry sites):
- E8 treeExp — BLOCKED at a machine-checked seam (Codex-verified): the premise
  row forces sibling one-side split sites to share cells/exponents,
  double-charging Σ siteExp and REFUTING the REV-6 F1 joint-satisfiability
  record at the LEAF sites (the rev-6 enumeration checked only the head).
  Three adjudication candidates on record (E8 header + MANIFEST ADJ-SPINE-4 +
  lean/notes/E8_BLOCK_CHARGE_2026-07-29.md). E10 perShape_law/E11 treeN gate
  on it. NEXT SESSION'S FIRST ITEM: the TREE-EXP note read + adjudication.
- E5 hnostray (head-roster completeness — the (c2) m_i=1 τ-hen leg, owner
  HC-2/D4R0K); D11 fibOf_partition (the rep-normalization law, owner
  HC-2/PresentNorm); G1's four (ASVIN Q1 — the V10/HistoryCoherent sign-off
  cluster, now also carrying the F4 card-4 stage); np_id_pin's jet-existence
  (Wall B, fenced); the banked W17ii (V7-8); spWord's EntShapeV width-law
  sign-off item; the disclosed boundaries (F1 witness, hRes-Q1).
AFTER THE E8 ADJUDICATION: the as-built dual ratification (Codex + Fable over
both corpora), then the 22+ seam re-keys (MovesS's 7 gated units, MovesD's
seam rows), MovesR unparking. Ledger:
lean/notes/LEAN_FORMALIZATION_CAMPAIGN_2026-07-28.md (the full round-by-round
record); the sorry sites themselves carry the exact missing-lemma statements.

## UPDATE (2026-08-01): MOVEST T RE-RATIFICATION REPAIRS — THE SITE-ENTRANCE KEYING

The second T ratification (Codex, REJECT-M) found the exact-cell re-key still
structurally unable to represent distinct co-realized sibling reads (one read
map Ψ shared across siblings forced equal cells/state events at a shared fiber
witness), plus a c/cSplit two-keying in `SibCountAt` deviating from the note's
single Σ_c. ADJUDICATED FIX EXECUTED (task #62): `CellData` gains the
MEMBER-KEYED SITE READ `branchCellOf es ν` + the joint-factoring law
`branch_cell_joint`; `siteCellEvent`/`SitePresents`/`JCmultiAt`/`SibCountAt`/
`state_cell` re-keyed at the site's own branch node (`H.lastNode`) — the branch
taken is part of the child site's entrance datum (the note's member-index
recursion, MOVES 7503–7515). `SibCountAt` is now ONE-CELL (conditioning =
roster cell), tied to the scaffold by the new `TreeScaffold.hframe_cell`. The
old sibling forcing is machine-checked DEAD: E8's `f1_two_leaf_discharge`
displays the F1 two-leaf configuration satisfiable (distinct pins, co-realized,
joint-factoring), with `shared_read_forces` quarantining the retired forcing to
its shared-map hypothesis. `RS1GivenPackage.tree_n` now carries the TREE-N
stability leg (`TreeNStableStmt`; T-E11b's honest sorry, fence-rule record: no
KBTotTower instance exists in-corpus, negation unconstructible). Full
enumerated corpus sweep green (9,429 jobs; census integers verbatim; MovesT
sorry census unchanged at 6 disclosed declarations; zero new axioms). Record:
MovesT/MANIFEST.json RERATIFY-T-1.

## UPDATE (2026-08-01): THE UNIFORMITY COMPLETION CAMPAIGN — DONE CRITERION MET

The /goal directive ("complete the formalization of the uniformity theorem") is
achieved in the campaign's own defined terms — the maximal honest completion
available without new mathematics. THE FINAL STATE, all verified this date:

**THE CAPSTONE.** `LeanUrat.MovesU.theoremU` — the uniformity squeeze: at every
prime p satisfying the typed regularity gate (REG-p) = (r1) ∧ (r2), the splitting
density ρ_σ(p) equals the evaluated rational function R_σ(p), exported with the
two-sided (U-n) bracket, the solve identification R = S.R = MovesS.Rsh, and the
ℤ_p bridge clause with (e,f) = (ramIdx, resDeg) — `#print axioms` = exactly
[propext, Classical.choice, Quot.sound]. Its hypothesis surface is FULLY HONEST:
typed rows over the ratified corpora where owner vocabulary exists; thirteen
explicit named parameters (the wave-4 boundary, recorded verbatim in the
docstring) where it does not.

**THE RATIFICATIONS.** All three wave-4 corpora cleared multi-round adversarial
Codex ratification with full verdict histories: MovesU (round 4, 0 material),
MovesT (round 4, clean), MovesV (round 5, 0M/1N). MovesX ratified round 1;
MovesSp core ratified + instantiated (SP8); MovesS 95/95 sorry-free; MovesD
complete. The corpus-wide sorry census: TEN, every one a named/owned fenced
item — E5's (U)+(R) D4R0K pair, the TreeNStable row, G1's four (task #44, the
V10/HistoryCoherent sign-off cluster — two recorded BLOCKED-FALSE at their
pinned tables), the three Phase-B seam-instantiation duties, the banked W17ii.

**THE KERNEL SEALS.** Every open mathematical kernel's predictions are
computationally sealed at the tested ranges: E0 (140/0 — no closed class,
κ < 1, decay exact), L1/D4R.0-K(a) (40,378/40,378 boundary cases),
STATE/TRACK (15/15), X-n3 (30/32 + the X1B reading adjudicated: the note's
own (CD)-pinned reading SEALED, the over-broad reading refuted as the note
itself predicts). The ¬HMC census toy is kernel-checked (the central kernel's
openness is a machine fact). R_σ re-derived bottom-up = the sealed forms.

**THE OPEN SURFACE (what a full unconditional theorem still needs).** The
mathematics: E0 (per-pool, all pools), HMC, WEIGHT-CHARGE/X.1b, X.3 general-n,
the (ALIGN) discharges, VP-SOUND's cites, the Phase-B/HC-2 bridges, htameFE
(palindromy, out of scope by directive), hExhaust general-n. The formalization:
the thirteen wave-D parameter rows, the W4-5 slot-selection discharge, task #44
(ASVIN's sign-off), the two trusted axioms (GMN, Denef–Igusa) eventually proved.

**THE PROCESS LEDGER.** ~20 statement defects caught at proof time with compiled
countermodels; one soundness event (a sorried universal coexisting with its
compiled negation) caught by ratification and excised; two false axioms caught
historically; three standing methodology rules earned: (1) enumerated
out-of-root-graph sweeps, (2) lake build never lake env lean, (3) no sorried
universal without a countermodel-construction attempt. The full round-by-round
record: lean/notes/LEAN_FORMALIZATION_CAMPAIGN_2026-07-28.md. ~750 local
commits, unpushed pending sign-off.
