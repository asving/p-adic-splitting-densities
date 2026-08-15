# CHAPTER C — THE TOWER GRAMMAR (levels ≥ 2, the twist layer, block lengths, the count laws)

**Chapter of:** the Phase-1 formalization blueprint (`docs/BLUEPRINT_PHASE_DESIGN_2026-08-13.md`
REVISION 2; node contract §2 as tightened by the fleet-protocol repairs), under
`blueprint/CONVENTIONS_2026-08-15.md` (GC-1…GC-14, PA-3(i), PA-5, BRIEF C) in full.
**Chapter cut:** `spec/DAG_README.md` "THE CHAPTER CUT", chapter **C = TOWER GRAMMAR**
(notes `GENTOW1, GENTOW3, GENTOW4, GENTOW5, GENTOW6, HETOW`; 363 DAG nodes), **plus the czar's
three additions**: `GENTOW2` (93 nodes, PA-3(i)), `HE6R1` (48, per BRIEF C — the level-2
reconciliation CHAP-B's H-3 deferred here), and the `W12-HT` slice (`EFF.W12.83`–`.87`, PA-5).
Planning figure **≈ 505 DAG nodes** (BRIEF C, [F2-corrected]).
**Sources transcribed:** `spec/EFF-HE6R1.md` (48 units), `spec/EFF-HETOW.md` (58),
`spec/EFF-GENTOW1.md` (67), `spec/EFF-GENTOW3.md` (62), `spec/EFF-GENTOW4.md` (57),
`spec/EFF-GENTOW5.md` (84, MERGED — contiguous IDs per GC-12), `spec/EFF-GENTOW6.md` (35),
`spec/EFF-GENTOW2.md` (93), `spec/EFF-W12.md` `.83`–`.87` (contiguous IDs; shard-local DAG rows
per GC-12/H-9's mitigation), plus the `e₁ ≥ 2` frame units of `spec/EFF-HE6.md` that CHAP-B's
H-1 explicitly deferred here (`EFF.HE6.08 .11 .13 .14`; the class-size complex `.18 .29 .30 .31
.32` is NOT transcribed — DECISION C-D1). `EFF-HE7.md` is **chapter E** (czar BRIEF E);
tower-geometric HE7 objects are consumed as `EFF.HE7.<nn> [supplied-by: chapter E]` placeholders
(GC-13).
**Supplier chapters consumed:** **A** (the landed kernel), **B** by committed node ID
(B.01–B.82: polygon, residual, `(e,f)`, certificates), **H §8 ONLY** (H.51–H.58, per H-14/GC-5;
H.54's `normIdx` is WITHDRAWN and is not consumed), **D** by GC-14 anchor (the ϑ table), **E**
by GC-13 placeholder.
**Target repo:** `leanfinal/` (general `O`; the standing complete-DVR bundle, fixed ONCE per GC-7).
**Authored:** 2026-08-15, Fable-max arm (append #56 fork plan). **CODEX CROSS-READ OWED** (§16).

---

## 0. How to read this chapter

### 0.1 The five standing environments

Every node names its environment as `ENV-C1` … `ENV-C5` plus deltas (GC-6.3: chapter-prefixed,
full variable blocks quoted; GC-6.4: minimal binding, declared per NODE, never per section).

**ENV-C1 — the polynomial arena over the fixed bundle** (= CHAP-B's ENV-A′, verbatim: ENV-A with
`π` promoted to an explicit hypothesis):

```lean
import Uniformity
namespace Uniformity.Density.Tower
open IsLocalRing Polynomial
variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {π : O}
-- nodes taking π carry (hπ : Irreducible π) explicitly
```

**ENV-C2 — ENV-C1 plus completeness** (every node that lifts through Hensel):

```lean
variable [IsAdicComplete (maximalIdeal O) O]
```

**ENV-C3 — ENV-C2 plus finiteness of the residue field** (every node that counts or names
`Res`/`Coeff`/`proj`/`residueCard`/`DecidedAt`-family objects, or factors a residual polynomial):

```lean
variable [Finite (ResidueField O)]
```

**ENV-C4 — the residue-tower arena** (pure finite-field algebra, no `O`; the level residue field
`K` and its extension `K₂` — the abstract two-field arena of GC-7's abstract/concrete split,
= CHAP-H's ENV-H4 with `K₂` for `K`):

```lean
import Uniformity
namespace Uniformity.Density.Tower
open Polynomial
variable {K K₂ : Type*} [Field K] [Field K₂] [Algebra K K₂]
-- [Finite K] [Finite K₂] added only where a node counts
```

**ENV-C5 — the arithmetic arena** (no `O`, no polynomials: statements about `ℕ`, `ℤ`, `ℝ` only —
the jump bounds, the budget/window arithmetic, the wrap exponents):

```lean
import Uniformity
namespace Uniformity.Density.Tower
open Finset
```

**GC-7 IS THE LAW OF THIS CHAPTER.** The bundle `O` is fixed once; a tower level is DATA over
`O` (§3's `LevelDatum`), never a re-quantified DVR; residue enlargement is the iterated CHAP-B
`resField` pattern (`resField φ = AdjoinRoot (φ.map (residue O))`), never an
`IntermediateField` of a closure. Any base change (`HE3-BOX-6`'s `O ↝ O[Π]/(Π^ℓ − π)`) is an
explicit constructed `O₂` with its own instances and a FAITHFULNESS flag; none is currently
needed by any node below (H-3).

### 0.2 File layout and naming

* One Lean file per node: `leanfinal/Uniformity/ChapC/C<nn>.lean`, module
  `Uniformity.ChapC.C<nn>` (the LANDED convention per GC-6.1; micro-nodes suffix a letter).
* Chapter roll-up `leanfinal/Uniformity/ChapC.lean` imports node modules in topological order;
  `Uniformity.lean` gains one line. `ChapC.lean` imports `Uniformity.ChapB` and the H §8 slice
  (`Uniformity.ChapH.H51` … `H58` — never the ChapH roll-up, which would re-create the backward
  arc H-14 removed).
* **Namespaces:** new *definitions* live in `Uniformity.Density.Tower` (GC-6.2); new *theorems
  about landed or CHAP-B objects* live in the namespace that owns the object.
  `Uniformity.Density.Leaf` (B's) and `Uniformity.Density.Induction` (H's) are READ, never
  extended.
* One PUBLIC declaration per node; reusable helpers trigger RE-PLAN (GC-6.5).
* Leanspec stubs wrap in `namespace LeanspecC`, file `leanspec/Leanspec/ChapC.lean` (GC-6.6),
  gate order per GC-6.6(a)–(d).

### 0.3 Names that already exist and must not be redefined

**From `Uniformity.Density` (chapter A, the landed kernel)** — the CHAP-B §0.3 list governs
verbatim; the ones this chapter's nodes actually consume by name: `FactorizationType`,
`FactorizationType.degree`, `FactorizationType.ext`, `FactorizationType.degree_mk_add`, `typeOf`,
`typeOf_degree`, `typeOf_mul`, `monicFactors`, `efPair`, `ramIndexOf`, `inertiaDegOf`,
`efPair_pos_of_mem`, `efPair_mul_le_natDegree`, `inertiaDegOf_dvd`, `ramIndexOf_mul_inertiaDegOf`,
`natDegree_dvd_addVal_norm`, `norm_adjoinRoot_root`, `typeOf_shift`, `typeOf_scaleRoots`,
`Res`, `Coeff`, `proj`, `residueCard`, `DecidedAt`, `decidedAt_of_congr`, `CoveringMenu`,
`UniformityStatement`, `DrainageAt`. **From `Uniformity.Hensel`:** `exists_monic_factorization`,
`monic_factorization_unique`, `isCoprime_of_map_eq`, `strongHensel`, `coeffIdeal`.
**From CHAP-B (committed node IDs, to land as `Uniformity.Density.Leaf.*`):** `dev` (B.02),
`npHgt` (B.07), `suppVal` (B.14), `OnSide`/`sideSet` (B.16), `sideMin`/`sideMax`/`sideLen`/
`sideDeg` (B.20), `resField` (B.21), `finrank_resField` (B.23), `resPoly` (B.28–B.30),
`suppVal_mul` (B.32), the dissections (B.41/B.42/B.48), the `(e,f)` reads (B.49–B.58), NS-6
(B.63/B.64), `NeedsDescent` (B.73, read under the GC-1/PA-1 REPAIRED `sideMin` pin),
the certificate layer (B.75–B.82). **From CHAP-H, H.51–H.58 ONLY** (GC-5): `class_sep` (H.51),
`slot_min_unique` (H.52), `eta_independent` (H.53), `stageLift'` (H.54 — `normIdx` WITHDRAWN,
never consumed), `stageLift_height` (H.55), `stageLift_summand_eq` (H.56), `wrap_div_mod`/
`wrap_height` (H.57), `divMod_bij`/`card_composedBasis` (H.58).
**From the Quarry (GC-3):** `Ideal.ramificationIdx_mul_inertiaDeg_eq_finrank_of_isLocalRing`
(`leanfinal/Uniformity/Quarry/RamificationInertiaLocal.lean`), primed generation, rank form;
reconcilers `Ideal.ramificationIdx_eq_ramificationIdx'`, `Ideal.inertiaDeg_eq_inertiaDeg'` by
exactly those names. The polynomial-level `efPair` engine and the ideal-theoretic primed pair
are NEVER silently identified (GC-3: that identification is `HYP.01` + `HYP.12`, [CORE-SET]).

### 0.4 The chapter's mathematical spine, in one page

CHAP-B is the corpus at **level 1 with `e₁ = 1`**: one key `φ` (order-0, `ϖ = π`, twist trivial),
one polygon, one residual read, the `(ℓ, m·d)` leaf. This chapter is everything the corpus does
when the read does NOT stop there, and its content is four layers:

| layer | corpus content | Lean character | sections |
|---|---|---|---|
| **the level frame** | the level-2 dictionary `D″ = D′ℓd_r`, `T₂ = ℓd_rλ`, `dv₂`, `K₂ = K(β)`, `μ₂ = deg f_S / D″` (`EFF.HE6R1.18`); level data over the FIXED `O`; the level-1 reconciliation with B's API | definitional + `ring`/`omega` arithmetic | §3 |
| **the gauge layer** | the `e₁ ≥ 2` normalizer `ϖ = x^{i₀}π^{a₀}`, the letter `η`, the wrap `W(t)`, the corrected `chat_t := lift(c_t·η^{W(t)})`, the cocycle `c₁(a,b) = (s(a)+s(b)−s(a+b))/ℓ`, twist triviality at `ℓ = 1` | algebra over `O[x]` + ENV-C4 residue algebra; consumes H.51–H.58 | §4, §6 |
| **the descent grammar** | the widened box (four cases), the jump trigger `ℓ_i·deg r_i ≥ 2`, the THREE-CLAUSE jump bound (`EFF.HE6R1.47`), the level-2 peel `Ψ ∣ f_S` with `(e,f) = (e₁ℓ, f₁d_r)`, the block projection/translation `h_{F₂,f} = h_{F₂,f_S} + c_g` | the B §0.4 divisibility-plus-degree route one level up; support-function statements per GC-2 | §5, §7 |
| **the count layer** | block lengths `\|S_{λ,r}\| = D″μ₂` in read form; the mixed-side tie `μ₂*(r) = m_r` ([cite:FGMN]); budgets/windows/shadow reads (GENTOW1/3/4/5/6); `LEMMA W12-HT` | counting over `Coeff O n N`; ENV-C3/C5 | §§8–12 |

**The one design fact the whole chapter turns on** (DECISION C-D1 below): the corpus's class-size
theorem (`THEOREM HE6.A`, `\|S_{λ,r}\| = D′ℓ·deg r`) counts **roots in a fixed algebraic closure**;
`leanfinal` has no closure and never will (GC-7). Every consumer of a class size below consumes it
as a **factor degree** — the degree of a canonical block factor exhibited by Hensel dissection —
and the corpus's own level-2 development already proves that recast for us: `LEMMA HE6R1-3`'s
sandwich `e ≥ e₁ℓ, f ≥ f₁d_r, ef = D″ ⟹ equality` is the B §0.4 divisibility-plus-degree
argument one level up, and `LEMMA HE6R1-2(b)`'s translation identity makes `\|S_{λ,r}\| = D″·μ₂`
**computable from `f`** without exhibiting `f_S`. No node of this chapter mentions a root that is
not a root of a named `O[x]`-factor.

### DECISION C-D1 — THE CLASS-SIZE / BLOCK-LENGTH ROUTE (decided first; BRIEF C trap (i))

**The question.** `THEOREM HE6.A` (`EFF.HE6.18`: `|S_{λ,r}| = D′ℓ·deg r`, multiplicity-1 case)
is the one thing CHAP-B refused (its H-2), and downstream consumers (the tower's block-length
prediction, E's ladder anchors `EFF.HE6.30/.32`, D's T1 battery check 10) were told to get it
from chapter C. Its corpus proof rests on the resultant account `(RES)`, the enlarged test family
`Ψ_{κ,r}` at fractional heights, Galois equivariance, and the valuation on a fixed `K̄₀`
(`EFF.HE6.06`) — none available, none quarriable (CHAP-B H-6's survey). The brief's two options:
re-derive closure-free, or carry as a schema/hypothesis field.

**RULING: a three-tier route — closure-free theorems where the corpus's own level-2 development
supplies them, one explicit hypothesis where the level-2 residue lower bound bites (the `B-BOX-1`
analogue, named `C-BOX-1`), and one gate-(b) literature cite for the multiplicity tie. THEOREM
HE6.A's own resultant/Galois-orbit route is NOT transcribed; no closure, ever.**

* **Tier 1 (proved, closure-free): the simple-block law as a factor statement.** The class size
  is REPRESENTED by the degree of the canonical `(λ, r)`-block factor `f_{λ,r}` cut out by the
  two dissections at the level-2 polygon (Hensel + the product law, B §6's route one level up).
  At a multiplicity-1 residual factor the statement is `deg f_{λ,r} = D″ = D′·ℓ·deg r` and
  `typeOf f_{λ,r} = ⟨{(e₁ℓ, f₁·deg r)}⟩`, proved by the divisibility-plus-degree sandwich
  (`EFF.HE6R1.16`'s arithmetic: `e' ≥ e₁ℓ` from the polygon/value-group leg, `f' ≥ f₁d_r` from
  the residue leg, `Σ e'f' = D″ = (e₁ℓ)(f₁d_r)` forces the singleton). The ramified divisibility
  leg (`e₁ℓ ∣ e'`) is closure-free at every parameter (the level-2 analogue of B.57, through the
  Quarry rank form). The residue leg (`f₁d_r ∣ f'`) is closure-free where B.53's mechanism
  reaches (`f₁d_r = 1`, and the `d = 1` tower of B's D-3 row) and is otherwise **conditional on
  `C-BOX-1`**, stated as an explicit hypothesis on exactly the nodes that need it — the same
  honesty shape as B.55/B.58, one level up. `C-BOX-1` is B-BOX-1's level-2 analogue, and a node
  needing it at `d_r ≥ 2` inherits B-BOX-1's repair route (B.56/B.62), not a new axiom.
* **Tier 2 (proved, closure-free): the proper-block count in read form.** `LEMMA HE6R1-2`
  (`EFF.HE6R1.13`, TERMINAL scalar form per PE3 F-1 at `.39`): under `Ψ ∤ f_S`, the level-2
  support function translates — `h_{F₂,f}(κ₂) = h_{F₂,f_S}(κ₂) + c_g` for `κ₂ > T₂` — so
  `μ₂ = Σ_{λ₂ > T₂} L_{λ₂}(f)` and `|S_{λ,r}| = D″·μ₂` are computable from `f` without
  exhibiting `f_S`. Transcribed as support-function/argmin statements per GC-2; the `c_g`-fold
  is exactly GC-2's ℕ∞-carrier mechanism. This is the READ form (`EFF.HE6R1.21`'s careful
  qualification: HE7-BOX-4 is superseded "in read form" — this chapter claims no more).
* **Tier 3 (gate-(b) cite): the mixed-side multiplicity tie.** `μ₂*(r) = m_r` at mixed sides is
  `LEMMA GENTOW-6.1`, whose corpus grade is PROVED-VIA-CITE (FGMN residual multiplicativity,
  GENTOW2's faithful-cite pattern — the corpus's ONE load-bearing literature cite). It enters as
  a **[cite:FGMN]** node under Part V's owner ruling: exact Lean statement of the cited theorem,
  axiom-faithfulness pattern, signed per cite. It is never re-derived through a closure here.

**FALSIFIER protocol.** If a §7 node provably cannot state its block factor without a root-level
object, the fallback is a `StageInterface`-keyed hypothesis field (GC-5 RE-PLAN — entry-pattern
data C-side, keyed to `GenreDatum`), recorded as a DECISION amendment here; never a closure
import, never a silent weakening.

---

## 1. HONESTY BLOCK (read before consuming any node)

**C-H1 — this chapter is the `e₁ ≥ 2` / level ≥ 2 complement of CHAP-B, and the seam is one
reconciliation lemma.** CHAP-B is HE6's frame at `e₁ = 1, h = 0, D′ = m` (its H-1): `dv = addVal`,
`ϖ = π`, twist trivial. This chapter installs the general frame — `dv := e₁·v`, the normalizer
`ϖ = x^{i₀}π^{a₀} ∈ K₀[x]` (`EFF.HE6.11`; `a₀` may be negative, which is why GC-2's ruling folds
the offset into the cleared pair rather than carrying signed heights), the letter `η`, the twist,
and the level-`r` iterates. The seam is C.05 (the level-1 reconciliation: this chapter's level-1
instance IS B's `npHgt`/`suppVal`, definitionally). A fleet agent needing `e₁ = 1` order-1 facts
consumes B nodes by name, never re-proves them here.

**C-H2 — the class-size theorem is transcribed at DECISION C-D1's three tiers and at no more.**
`THEOREM HE6.A`'s own proof complex (`EFF.HE6.18 .29 .30 .31 .32`: resultants, `Ψ_{κ,r}` at
fractional heights, Galois equivariance over `K̄₀`) has **no node** — matching CHAP-B H-2, which
this chapter's §7 discharges rather than re-litigates. What consumers get: Tier-1 factor-degree
law (conditional on `C-BOX-1` exactly where stated), Tier-2 read-form count `|S_{λ,r}| = D″μ₂`,
Tier-3 [cite:FGMN] multiplicity tie. A fleet agent needing the root-count form itself (as opposed
to the factor-degree form) has left the formalizable corpus and returns
`BLOCKED: C-D1 (closure-free recast only)`.

**C-H3 — `HE3-BOX-6` (ledger `HYP.143`) is disclosed, scoped `n ≥ 8`, and NO node here performs
its base change.** "The ramified base change `O ↝ O[Π]/(Π^ℓ − π)` is stated too cheaply — `Φ′`
need not remain irreducible over `O₂`" (`EFF.HE3.44`). The §5/§7 route needs no test key at a
fractional height and no base change (the same immunity-by-construction as CHAP-B H-5, one level
up: the divisibility-plus-degree sandwich touches only `O[x]`-factors). GC-7's explicit-`O₂`
rider stands armed but unused; the immunity claim is §16 cross-read item 1.

**C-H4 — `[GENHN-TOW-1]` (ledger `HYP.82`; "seven items under six numerals" [F8]) is load-bearing
at `n ≥ 8` ONLY, and this chapter transcribes exactly the items that have proofs.** The
item-by-item disposition, against the GENTOW notes' own charges:

| item | content | status | here |
|---|---|---|---|
| (1) | composed entry budgets (GENHN-1 at `Φ₂`) | PROVED — `LEMMA GENTOW-1` (4 clauses, R2a clip TERMINAL) + `COR GENTOW-1.1` | §6 |
| (2) | inner refine transfer (GENHN-4 one level up) | PROVED — `LEMMA GENTOW-2` (4 clauses, R2b `DOM_N`/`COD_N` TERMINAL) | §6 |
| (3) | stage-shadow vs composed read | PROVED — `THEOREM GENTOW-3` (4 clauses at the S8.1/S8.4 TERMINAL forms) + `COR GENTOW-3.C` | §8 |
| (4) | partial inner sides (`e₂f₂μ₂ < μ₁`) | PROVED — `GENTOW-4.1`, `THEOREM GENTOW-4.A` (TOWERRAT2-C monic-signature TERMINAL), `GENTOW-4.2`, `COR GENTOW-4.C` | §8 |
| (5) | composed window ledger (GENHN-3 at `dv₂`) | PROVED — `LEMMA GENTOW-5` (5 clauses, R2c THREE-BANDS TERMINAL) | §6 |
| (6)(α) | iterated depth-≥ 3 key composition | THIRD STAGE ONLY (first live `n = 16`) — `THEOREM GENTOW5-A` at its acceptance scope; depth ≥ 4 NOT claimed, boxed at exact scope | §9 |
| (6)(β) | depth-3 node-floor rider | DISCHARGED INTO item (1) (`EFF-GENTOW1` scope split A); the `κ₃ > e₂f₂u₂` floor is an explicit HYPOTHESIS routed to `COR GENTOW-1.1` (GENTOW5's FP-4 fence 2) | §6/§9 |

Nothing here upgrades any item beyond its note's own acceptance scope; the `n ≥ 8`-only and
depth-3-`n ≥ 16` fences are stated on the §9 nodes themselves.

**C-H5 — `LEMMA GENHN-T(b)` is REFUTED and only `T(b)′`'s surviving content is used.** (CHAP-H
H-10.) The composed-key lift is licensed ONLY by `LEMMA GENHN-LIFT` = H.54–H.57, consumed by
name, never re-proved; H.54's `normIdx` is WITHDRAWN and no DEPENDS field below names it. The
gauge-naive `chat_t` is DEAD corpus-wide (CHAIN-GAUGE: HETOW PE1 F-1 → GENHN erratum `59c1966` →
the `[GT*-r1]` pins); every node below states the CORRECTED display
`chat_t := lift(c_t·η^{W(t)})`, `W(t) = ⌊(f₂−t)·i(u₂)/e₁⌋`, and a node written against the naive
form is a blueprint defect to be returned, not repaired in flight.

**C-H6 — ϑ-orientation: chapter D owns the four-way table (GC-14); this chapter CITES and never
restates.** The trap has teeth here twice: `LEMMA GENTOW5-A1`'s `ϑ_t` is the table's RECIPROCAL
row ([F6]: `theta_t = res(n̂₂(λ)^t / n̂₂(tλ))`, so `ϑ(t) = ϑ_{f₃−t}^{−1}` at `λ = u₃`), and
GENTOW2 itself DECLINES to adjudicate the correspondence (its NON-IMPORT N-7) — so neither
source note alone is authority; the D-table anchor is. Every ϑ-touching node below (§9, §10)
carries `DEPENDS: [ϑ-TABLE — supplied-by: chapter D, GC-14 anchor]` and states its own content
in normalizer-ratio form (residues of explicit `n̂₂` monomial ratios), never in bare-ϑ form. The
B-law direction (`u(β) = R_{3,β}(n̂₂(β̂))`, `FGMN = u·repo`, NOT the inverse) is a separate
orientation and is never conflated with the Θ/ϑ inversion.

**C-H7 — `LEMMA W12-HT` is transcribed at exactly its corpus strength, and its conditionality is
carried in the statements.** `EFF.W12.87` OPEN-CALL 6: composed by a model from a conjectured
law, hand-verified, machine-corroborated only on grid `n ∈ {3,4}, q ∈ {2,3}, N ≤ 6`, **no
hostile-arc pass**. Consequences here: (i) §11's HT nodes are stated per-member at explicit `N`
(GC-9.3 — no uniform-`N` law; the `R8-1` refutation `f = (Φ′−C)³ + 5^M` stands); (ii) σ is read
through `monicFactors`/`typeOf` at every-lift strength (GC-9.1, CHAP-B H-11's route), with the
corpus's `disc ≠ 0` divergence flagged per node; (iii) an HT node at `d ≥ 2` **inherits
`B-BOX-1`** through B.55/B.58 (CHAP-B H-10) and says so in its CONDITIONALITY; (iv) GC-11 gates
apply with extra force — §13's gates fire HT instances at `q = 2` AND `q = 3` with an
`e > 1 ∧ f > 1` witness.

**C-H8 — the tower notes' post-acceptance corrections reach INTO displayed lemma statements, and
this chapter transcribes TERMINAL forms only.** Unusually for the corpus, four of this chapter's
sources carry accepted-then-corrected lemma displays: GENTOW1's R2a (the budget clip
`Σ max(0, N − floor)`), R2b (`DOM_N`/`COD_N` onto), R2c (GENTOW-5(a)'s iff → THREE BANDS);
GENTOW3's CHAIN-GEOG/CHAIN-PERSIST/CHAIN-NONFUNC (S8.4 TERMINAL: "not a function of the honest
read's σ"); GENTOW4's TOWERRAT2-C (the monic parenthetical FALSE; true signature `n > μ₂·D₂`)
and m-A/m-i/m-ii; HE6R1's `.47` three-clause re-display of the jump bound and `.39`'s pin-height
cocycle exponent; GENTOW6's PE2-F-2 codomain (`n mod D₂ ≠ D₂ − 1`, sharper than `D₂ ∤ n`).
**Every node below transcribes the TERMINAL layer and its SOURCE field names the chain**, so the
cross-read can verify no superseded display leaked in. A fleet agent finding a node text that
matches a frozen (non-terminal) display returns it as a blueprint defect.

**C-H9 — NS-7 (ladder termination) is a cite-hypothesis, not a theorem of this chapter.** The
resolution doc's own verdict: NS-7 is "the one row that is only PARTIAL". What IS proved here is
the jump-count arithmetic — the three-clause bound (a) `J ≤ log₂μ − 1` / (b) `J ≤ log₂n − 2`
stage-rooted / (c) `J ≤ log₂n − 1` ambient-rooted, sharp (`EFF.HE6R1.47`, §5) — which bounds the
LEVEL depth. Full descent termination (GMN Thm 4.18/Cor 4.19 scope) enters as the **[AGNPRW]
Thm 5.2 cite-hypothesis** (`HYP.15`'s answered branch), a [cite:AGNPRW] gate-(b) node in §9,
consumed by name downstream and never silently strengthened.

**C-H10 — GENTOW2's FGMN cite is THE load-bearing literature cite, and it enters through gate
(b) alone.** `docs/TIGHTNESS_CENSUS_2026-08-11.md` row I-3. §10 states the cited FGMN residual-
multiplicativity theorem as an exact Lean statement under the axiom-faithfulness pattern
([cite:FGMN]; Asvin signs per Part V gate (b)); `LEMMA GENTOW2-B″`/`B′` and Tier 3 of C-D1
consume it. The `w`-disclosure stands: `w` is NOT computed anywhere in the corpus
(`EFF.GENTOW2.82`'s dated brackets); no node below claims a closed form for it. The `ψ₂`
overload is resolved per TOWERRAT-R3-4: every §10 statement writes `ψ₂^FGMN` or `ψ₂^repo`
explicitly.

**C-H11 — what is in the cut but NOT in this file.** (i) `EFF-HE7` (137 headings) is chapter E's
(czar BRIEF E); its objects appear below only as `EFF.HE7.<nn> [supplied-by: chapter E]`
placeholders (`LEMMA HE7-6`'s block factor, `LEMMA HE7-8`'s α-refine finiteness, `ANNEX-LEMMA
R1-a`(iii)/(iv)'s cocycle transport). (ii) `LEMMA HETOW-4` was ABSORBED into T3 as
`(ABS-HE4)`/`(HE4-COB)` (`EFF.HETOW.53/.57`); its content is chapter D's to state, dual-cite
licensed — this chapter cites the D placeholder, and only clause (a) (source-local) is
transcribed here if a node needs it. (iii) The ϑ table is D's (C-H6). (iv) `THEOREM W-12.D` is
H.98 + landed `UniformityStatement.ofDecided`, not re-transcribed (PA-5). (v) Run-records,
instrument records, acceptance boxes and grade arcs of all nine sources: TEETH dispositions
(§16), not nodes.

**C-H12 — the coincidence-regime trap is live in this chapter's numerics, twice.** (i) Every
battery row of the GENHN/HE6R1 complex has `f₁ = 1`, where `D′h = e₁h = S` — the exact
degeneracy that hid GENHN-1's wrong node floor (`EFF.HE6R1.04`). Every §3–§6 node therefore
states floors in the `D′h` form; a node written with `e₁·h` where `keyDeg·h` is meant is a
blueprint defect even though every machine row agrees (CHAP-H H.02's fidelity rule, adopted).
(ii) The G.23 lesson (GC-11): §13's gates run `q = 2` AND `q = 3`, and the `e₁ ≥ 2` witness is
genuinely wild. (iii) A third instance for free: `LEMMA HE6R1-1`'s `n`-bound was FALSE at
ambient roots because every consumption site was stage-rooted (`EFF.HE6R1.43`) — scope pins are
stated on the §5 nodes, not inferred from batteries.

**C-H13 — boxes that are NON-NODES here, by name.** `HE6-BOX-1` (the widened box) is CLOSED as a
two-note composition (branch (iv) at HE7/E, branch (ii) at HE6R1/§5 here) and is a declared
NON-NODE (CHAP-B B.64's note, adopted): an agent needing "the box" returns `BLOCKED: HE6-BOX-1`
and consumes §5's theorems instead. `HEX3-BOX-1` (`HYP.137`) is a NON-NODE everywhere (G H-2,
H H-4 precedents). `GENTOW4-BOX-1/-2/-4` (`HYP.144`) enter only at their TERMINAL states:
BOX-1 CLOSED by `LEMMA GENTOW-6.1` (§7 Tier 3), BOX-4 DISCHARGED by GENTOW6's SUB-BOX battery
row, BOX-2 carried at exact wording where §8 needs it. `GENTOW6-BOX-1` is CLOSED AT `f₁ = 1` by
`THEOREM GENTOW-6.5` with the "iff" WITHDRAWN (the converse is FALSE with a witness — §8
transcribes the surviving direction only). `GENTOW3-BOX-1`'s three measured certificate
configurations are a TEETH row, not a node.

**C-H14 — GC-2's carrier ruling is executed, not just cited.** §3 arranges the level-`r` height
function `ℕ∞`-valued by construction: the level dictionary keeps `dv₂` ℤ-valued on keys and the
`c_g`-translation (`EFF.HE6R1.13`(b)) folds the normalizer offset into the cleared pair, so the
declared carrier is B's `npHgt`/`suppVal` applied to the level-`r` development — no new polygon
type (GC-2), no `ℚ`, no hull. If a §5/§7 node hits a provably-negative height, the recorded
fallback (`WithTop ℤ` + simp-bridge) triggers a DECISION block here plus the GC-2 flag; as
composed, no node needs it.

**C-H15 — codex cross-read status: OWED.** Opus/Fable-authored like every artifact of this week;
the flagged items are §16. Numeric gates execute at the leanspec stub stage (GC-6.6(c)) BEFORE
any fleet agent fires on §§7–12.

---

## 2. NODE INDEX

| § | nodes | content | env |
|---|---|---|---|
| 3 | C.01–C.14 | the level frame: `LevelDatum` over fixed `O`, the level-2 dictionary, iterated `resField`, the level-1 reconciliation with B | C1/C4 |
| 4 | C.15–C.28 | the gauge layer: `dv = e₁v`, `ϖ`, `η`, `W(t)`, corrected `chat_t`, `s(·)`, the cocycle `c₁`, twist-triviality at `ℓ = 1` | C1/C4/C5 |
| 5 | C.29–C.40 | the descent grammar: widened box (four cases), jump trigger, the THREE-CLAUSE jump bound, the level-2 peel, the block projection/translation | C2/C5 |
| 6 | C.41–C.58 | composed keys and the tower bridges: `Φ₂` (wrap-corrected), HETOW-1/2/3, GENTOW-1 + 1.1 (budgets, clipped), GENTOW-2 (refine transfer), GENTOW-5 (window ledger, three bands), the K₂-digit lift | C1/C2/C5 |
| 7 | C.59–C.70 | class size / block length (DECISION C-D1): the block factor, Tier-1 factor-degree law + `C-BOX-1`, Tier-2 read-form count, Tier-3 [cite:FGMN] tie | C2/C3 |
| 8 | C.71–C.82 | the shadow-read layer and the caps: GENTOW-3 (terminal forms) + 3.C, GENTOW-4.1/4.A/4.2/4.C, GENTOW-6.2/6.2C/6.3/6.3′/6.4/6.5 | C2/C5 |
| 9 | C.83–C.96 | the third stage and the thresholds: GENTOW5-A/D at acceptance scope, the (β)-floor hypothesis, depth arithmetic (`n ≥ 8`, depth-3 `n ≥ 16`), [cite:AGNPRW] termination, the `HYP.82` census made formal | C2/C5 |
| 10 | C.97–C.106 | the GENTOW2 supply layer: [cite:FGMN], B″/B′ (terminal supply to D and F), the S2 tower witness, `ψ₂` discipline, the u/B-law direction | C2/C4 |
| 11 | C.107–C.116 | the HT count layer (`EFF.W12.83`–`.87`): (HT-rec), (HT-branch), (HT-global) at every-lift strength, level-`N` cells, `B-BOX-1` inheritance disclosed | C3 |
| 12 | C.117–C.122 | level-`N` tower certificates: the level-2 polygon/residual pin decides `typeOf`, per-member at explicit `N` (B.75–B.82 one level up) | C3 |
| 13 | C.123–C.126 | gates: `q = 2` and `q = 3` firing instances (genuinely wild `e₁ ≥ 2`, `e > 1 ∧ f > 1`), the HT spot values, the axiom census | C3 |
| 14 | — | DAG additions (GC-12: shard-local rows, contiguous IDs in `evidence`) | — |
| 15 | — | leanspec stub list (`LeanspecC`, GC-6.6) | — |
| 16 | — | TEETH disposition summary; flagged for the codex cross-read | — |

**Planned kind census** (index, not contract, on kinds — CHAP-B A-§9.2 precedent): ≈ 30 `def`,
≈ 62 `lemma`, ≈ 22 `theorem`, 2 `cite`, 4 `gate` — **126 nodes planned**. Deltas against this
index are recorded per section in dated `A-§` blocks at the file tail, never by editing this
table.

**TERMINAL SUPPLY NODES (what other chapters consume from here, by ID):**

* **C.03** — the level-2 dictionary (`D″ = D′ℓd_r`, `T₂ = ℓd_rλ`, `μ₂`) as a `LevelDatum`
  structure → chapter E's ladder (`EFF.HE6.09/.15/.17/.56` pin anchors resolve here per BRIEF E
  [F1]), chapter D's telescope.
* **C.15/C.18/C.21/C.24** — the normalizer/twist layer (`ϖ`, `η`, `W(t)`/`chat_t`, the cocycle
  `c₁`) → CHAP-B H-1's out-of-scope consumers, chapter E's `.13`/`.14` pin anchors [F1].
* **C.61 (Tier 1), C.64 (Tier 2), C.66 (Tier 3)** — the class-size/block-length laws → CHAP-B
  H-2's downstream consumers, E's `.30`/`.32` anchors [F1], D's T1 battery check 10, F's weld
  faces.
* **C.99 (B″), C.100 (B′)** — GENTOW2's lemmas → chapters D and F (their briefs route here via
  GC-13).
* **C.83/C.84** — the third-stage frame → E's deep rungs, D's w-frame.
* **C.107–C.110** — the HT count laws → chapter H's entry-law audits' supplier of record
  (CHAP-B H-10 routing), chapter I's count-side conditionality.

**GC-13 PLACEHOLDERS ISSUED BY THIS CHAPTER** (unauthored chapters; the orchestrator resolves at
freeze): `EFF.HE7.<nn> [supplied-by: chapter E]` for `LEMMA HE7-6`, `LEMMA HE7-8`,
`ANNEX-LEMMA R1-a(iii)/(iv)`, `(SLOT₂)`/`(LIFT₂)`; `ϑ-TABLE [supplied-by: chapter D, GC-14]`;
`(ABS-HE4)/(HE4-COB) [supplied-by: chapter D]` for HETOW-4's absorbed clauses.

**Graph shape:** computed and recorded in §14 (`spec/DAG_BLUEPRINT_C.tsv`) as sections complete;
the §3–§5 spine is serial (frame → gauge → grammar), §§6–11 fan out wide.

---

## 3. §3 — THE LEVEL FRAME AND THE LEVEL DICTIONARY

<!-- §3 nodes: C.01–C.14 -->

---

## 4. §4 — THE GAUGE LAYER: NORMALIZERS, THE LETTER, THE WRAP, THE COCYCLE

<!-- §4 nodes: C.15–C.28 -->

---

## 5. §5 — THE DESCENT GRAMMAR: THE WIDENED BOX, THE JUMP, THE PEEL, THE PROJECTION

<!-- §5 nodes: C.29–C.40 -->

---

## 6. §6 — COMPOSED KEYS AND THE TOWER BRIDGES

<!-- §6 nodes: C.41–C.58 -->

---

## 7. §7 — CLASS SIZE AND BLOCK LENGTH (DECISION C-D1 EXECUTED)

<!-- §7 nodes: C.59–C.70 -->

---

## 8. §8 — THE SHADOW-READ LAYER AND THE CAPS

<!-- §8 nodes: C.71–C.82 -->

---

## 9. §9 — THE THIRD STAGE, THE THRESHOLDS, AND TERMINATION

<!-- §9 nodes: C.83–C.96 -->

---

## 10. §10 — THE GENTOW2 SUPPLY LAYER

<!-- §10 nodes: C.97–C.106 -->

---

## 11. §11 — THE HT COUNT LAYER

<!-- §11 nodes: C.107–C.116 -->

---

## 12. §12 — LEVEL-`N` TOWER CERTIFICATES

<!-- §12 nodes: C.117–C.122 -->

---

## 13. §13 — GATES

<!-- §13 nodes: C.123–C.126 -->

---

## 14. §14 — DAG ADDITIONS

<!-- populated per completed section -->

---

## 15. §15 — LEANSPEC STUB LIST

<!-- populated at chapter close -->

---

## 16. §16 — TEETH DISPOSITIONS; FLAGGED FOR THE CODEX CROSS-READ

<!-- populated at chapter close; running flag list kept here meanwhile -->

**Cross-read flags (running list):**
1. C-H3's immunity claim (no base change, no fractional-height test key anywhere in §5/§7).
2. DECISION C-D1's Tier-1 recast (root count → factor degree) — attack the faithfulness of the
   recast against `EFF.HE6.18`'s statement and `EFF.HE6R1.16`'s sandwich.
3. The TERMINAL-form discipline of C-H8 — verify no superseded display leaked into any node.

---

<!-- RESUME: skeleton committed. Next: compose §3 (C.01–C.14) from EFF.HE6R1.18/.06, EFF.HE6.08/.11, B.01–B.30 interfaces. Then §4 from EFF.HE6.11/.13, GENTOW1 chat_t/W(t) pins, H.51–H.58. Sections in order §3→§13; commit per 2–3 nodes; A-§ delta blocks at tail. -->

<!-- CHAP-C APPEND POINT — do not remove; sections are appended here in order -->
