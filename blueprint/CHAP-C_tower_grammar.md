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

> **Design note (the tower's one recursion).** GC-2 demands the polygon be D-1's three objects
> at every level, with no new polygon type. §3 delivers that by exhibiting the tower as ONE
> recursion on B's API: **a level's height function is the previous level's cleared support
> value.** Concretely: the stage height `dv` of a coefficient `A` (degree `< D′`) is
> `suppVal X A h e₁` — B's own cleared support of the `X`-development at the frame's side
> (C.02); the level-1 polygon of `f` is the pair `(dvHgt, dvSupp)` built from `dev Φ′ f` in that
> normalization (C.06); and the level-2 height of a Ψ-development coefficient `A`
> (degree `< D″`) is `dvSupp F A u ℓ` — the level-1 support value at the level's side (C.11).
> Every carrier is `ℕ∞`/`Finset ℕ`/`Prop` (GC-2's ℕ∞-by-construction leg, executed: heights
> are infima of `ℕ`-linear forms at every level, so no negative height can arise and the
> `WithTop ℤ` fallback is never needed — C-H14). Sides/argmin data mirror B.16/B.20 shape for
> shape (C.07), and the level-1 reconciliation (C.05) is definitional, as GC-2 mandates.

### NODE C.01 [def] [fresh]

**STATEMENT.** *The stage key frame.* A **key frame** over the fixed bundle `O` consists of
natural numbers `e₁, f₁, h` and a polynomial `Φ′ ∈ O[X]` ("the key") subject to: `0 < e₁`,
`0 < f₁`, `Nat.Coprime h e₁` (the slope `h/e₁` in lowest terms); `Φ′` monic of degree
`D′ = e₁·f₁`, irreducible over `O`; `Φ′` is `(h, e₁)`-pure with respect to the order-0 key `X`
(the closure-free form of "the roots of `Φ′` have valuation `h/e₁`"); and the residual
polynomial of `Φ′` at that side — read under the GC-1 `sideMin` pin — is **irreducible** of
degree `f₁` (the frame's `ψ`). This is `EFF.HE6.08`'s frame
`(O, Φ′, ψ, K = F_Q(η_θ), dv = e₁v)` with every closure-dependent clause recast on B's API.

**SIGNATURE.**
```lean
namespace Uniformity.Density.Tower

open Uniformity.Density.Leaf in
/-- The stage key frame `(e₁, f₁, h; Φ′)` of `EFF.HE6.08`: `Φ′` monic irreducible of degree
`D′ = e₁f₁`, one-sided of slope `h/e₁` over the order-0 key `X`, with irreducible residual
read `ψ` of degree `f₁`.  The valuation normalization is `dv := e₁·v` (C.02). -/
structure KeyFrame (O : Type*) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (π : O) where
  e₁ : ℕ
  f₁ : ℕ
  /-- The slope numerator.  `h = 0` (forcing `e₁ = 1`) is the DEGENERATE frame, admitted so
  that C.05's level-1 reconciliation is definitional; the corpus frame has `1 ≤ h`. -/
  h : ℕ
  key : Polynomial O
  he₁ : 0 < e₁
  hf₁ : 0 < f₁
  hcop : Nat.Coprime h e₁
  hmonic : key.Monic
  hdeg : key.natDegree = e₁ * f₁
  hirr : Irreducible key
  hpure : IsPure Polynomial.X key h e₁
  hne : (sideSet Polynomial.X key h e₁).Nonempty
  /-- The residual read of the key is irreducible of degree `f₁` (frame hypothesis
  `ψ ∈ F_Q[T]` irreducible, `EFF.HE6.08`) — pinned at `sideMin` per GC-1. -/
  hresirr : ∀ (H₀ : ℕ), npHgt Polynomial.X key (sideMin Polynomial.X key h e₁ hne) = (H₀ : ℕ∞) →
    Irreducible (resPoly π Polynomial.X key h e₁ hne H₀) ∧
    (resPoly π Polynomial.X key h e₁ hne H₀).natDegree = f₁
```

**⚠ FAITHFULNESS (mandatory, trust-boundary definition).** Three recasts against
`EFF.HE6.08`'s verbatim frame, each flagged for the cross-read (§16): (i) *"roots of
`v = h/e₁`"* becomes the purity clause `hpure` + `hne` — the two are equivalent through the
polygon dictionary (a one-sided `X`-polygon of slope `h/e₁` IS the root-valuation statement,
closure-free; B's D-1 criterion C2); (ii) *"`ψ` irreducible with root
`η_θ = res(θ^{e₁}π^{−h})`"* becomes `hresirr` — the residual read at the side, B.28's object;
the `η_θ`-embedding `ι_ξ` of `EFF.HE6.08` is NOT carried (labels are transported by algebra
maps of `AdjoinRoot` quotients, §4); (iii) the degenerate `h = 0` instance is admitted
(corpus: `h ≥ 1`) solely so C.05 can be definitional — every node needing positivity states
`0 < F.h` explicitly (GC-6.4). Note `IsKey key` does NOT hold at `h ≥ 1` (the reduction is
`x^{D′}`, not irreducible) — the frame is genuinely disjoint from B's key class except at the
degenerate instance, which is the H-1 seam made precise.

**DEPENDS.** B.01 (`IsKey`, for the contrast only) · B.16 (`sideSet`) · B.20 (`sideMin`) ·
B.28 (`resPoly`) · B.34 (`IsPure`) — all by committed node ID (GC-13(b)).

**PROOF.** definitional.

**SIZE.** 30 lines.

**SOURCE.** `EFF.HE6.08` (the frame convention, verbatim); `EFF.HE6.10` (the development
frame it feeds); CHAP-B H-1 (the deferral of exactly this object to chapter C).

**TEETH.** signed non-applicable (a definition; the frame audits fire at C.10 and §13).

**ENVIRONMENT.** ENV-C1.

---

### NODE C.02 [def] [fresh]

**STATEMENT.** *The stage height `dv` is a REUSE of B's cleared support.* For a frame `F` and
any `A ∈ O[X]`, the **stage height** is `stageHeight F A := suppVal X A F.h F.e₁ ∈ ℕ∞` —
literally B.14's cleared support value of the `X`-development of `A` at the side `(h, e₁)`.
Companion unfold: `stageHeight F A = inf_{i ≤ deg A} (F.e₁ • addVal(A.coeff i) + F.h * i)`,
which is `EFF.HE6.10`'s `dv(A) := min_i (e₁·v(a_i) + i·h)` verbatim, `ℕ∞`-valued.

**SIGNATURE.**
```lean
namespace Uniformity.Density.Tower

open Uniformity.Density.Leaf in
/-- `dv(A) = min_i (e₁·v(a_i) + i·h)` (`EFF.HE6.10`), realised as B's `suppVal` at the
order-0 key `X` — GC-2's reuse, literal. -/
noncomputable def KeyFrame.stageHeight (F : KeyFrame O π) (A : Polynomial O) : ℕ∞ :=
  suppVal Polynomial.X A F.h F.e₁

theorem KeyFrame.stageHeight_eq_inf (F : KeyFrame O π) (A : Polynomial O) :
    F.stageHeight A
      = (Finset.range (A.natDegree + 1)).inf
          (fun i => F.e₁ • gaussVal (Polynomial.C (A.coeff i)) + (F.h * i : ℕ∞))
```

**DEPENDS.** C.01 · B.14 (`suppVal`) · B.15 (`dev_X`, `npHgt_X` — the `X`-development is the
coefficient list).

**PROOF.**
1. `stageHeight_eq_inf`: unfold `suppVal`; rewrite each `npHgt X A i` by B.15's
   `dev_X : dev X A i = C (A.coeff i)`.
2. definitional otherwise.

**SIZE.** 10 lines.

**SOURCE.** `EFF.HE6.10` (the `dv` display); GC-2 (the reuse mandate); `EFF.HE6R1.18` (the
audit `dv(ϖ(ξ)) = 1` consuming exactly this normalization).

**TEETH.** signed non-applicable.

**ENVIRONMENT.** ENV-C1 (`hπ` needed only by consumers that read residues).

---

### NODE C.03 [def] [fresh]

**STATEMENT.** *The stage residual polynomial and the stage residue field.* For a frame `F`
with a correct pin `H₀` (`npHgt X Φ′ (sideMin …) = H₀`): the **frame residual**
`frameRes F H₀ hpin := resPoly π X F.key F.h F.e₁ F.hne H₀ ∈ (resField X)[Y]` (B.28's object;
irreducible of degree `f₁` by `F.hresirr`), and the **stage residue field**
`stageField F H₀ hpin := AdjoinRoot (frameRes F H₀ hpin)` — the CHAP-B `resField` pattern
iterated once (GC-7's mandated carrier: `K = F_Q(η_θ)` as an explicit quotient, never an
`IntermediateField`). The **stage residue cardinality** is `stageCard F := residueCard O ^ F.f₁`.

**SIGNATURE.**
```lean
namespace Uniformity.Density.Tower

open Uniformity.Density.Leaf in
/-- The frame residual `ψ` — B.28's `resPoly` at the frame's side, under the GC-1 pin. -/
noncomputable def KeyFrame.frameRes (F : KeyFrame O π) (H₀ : ℕ)
    (hpin : npHgt Polynomial.X F.key (sideMin Polynomial.X F.key F.h F.e₁ F.hne) = (H₀ : ℕ∞)) :
    Polynomial (resField (Polynomial.X : Polynomial O)) :=
  resPoly π Polynomial.X F.key F.h F.e₁ F.hne H₀

/-- The stage residue field `K = F_Q(η_θ) ≅ F_{Q^{f₁}}`, as an iterated `AdjoinRoot` (GC-7). -/
abbrev KeyFrame.stageField (F : KeyFrame O π) (H₀ : ℕ) (hpin : _) : Type _ :=
  AdjoinRoot (F.frameRes H₀ hpin)

/-- `|K| = Q^{f₁}` as a number (the lemma-level identity is C.04). -/
def KeyFrame.stageCard (F : KeyFrame O π) [Finite (ResidueField O)] : ℕ :=
  residueCard O ^ F.f₁
```

**DEPENDS.** C.01 · B.21/B.25 (`resField`, `resMk`) · B.28 (`resPoly`).

**PROOF.** definitional.

**SIZE.** 16 lines.

**SOURCE.** `EFF.HE6.08` (“`K := F_Q(η_θ) ≅ F_{Q^{f₁}}`”); GC-7 (the `resField`-iterate
mandate, verbatim: *"iterated at level `r` over the previous level's residual key"*).

**TEETH.** signed non-applicable.

**ENVIRONMENT.** ENV-C1; the `stageCard` clause adds `[Finite (ResidueField O)]` (ENV-C3
binding on that declaration only).

---

### NODE C.04 [lemma] [fresh]

**STATEMENT.** *The stage residue field is a finite field of the predicted size.* With `F`,
`H₀`, `hpin` as in C.03 and `[Finite (ResidueField O)]`: `stageField F H₀ hpin` is a field
(`Fact (Irreducible ψ)` from `F.hresirr`); it is finite;
`Module.finrank (resField X) (stageField …) = F.f₁`; and
`Nat.card (stageField …) = residueCard O ^ F.f₁ = stageCard F`. (B.22–B.24's statement
shapes, one level up — GC-7's card/finrank bookkeeping clause.)

**SIGNATURE.**
```lean
namespace Uniformity.Density.Tower

theorem KeyFrame.card_stageField (F : KeyFrame O π) [Finite (ResidueField O)]
    (hπ : Irreducible π) (H₀ : ℕ)
    (hpin : npHgt Polynomial.X F.key (sideMin Polynomial.X F.key F.h F.e₁ F.hne) = (H₀ : ℕ∞)) :
    Nat.card (F.stageField H₀ hpin) = residueCard O ^ F.f₁
```

with the `Field`/`Finite`/`finrank` clauses as instance/companion statements in the same file
(private helpers below the public declaration; the public name is `card_stageField`).

**DEPENDS.** C.01 · C.03 · B.22 (field instance pattern) · B.23 (`finrank_resField`,
`card_resField` — the level-1 template) · landed `residueCard`.

**PROOF.**
1. `F.hresirr H₀ hpin` gives `Irreducible ψ`; `AdjoinRoot` of an irreducible over a field is a
   field (mathlib `AdjoinRoot.instField` route, as in B.22).
2. `finrank = natDegree ψ = f₁` (B.23's route: `AdjoinRoot.powerBasis`).
3. `Nat.card = (Nat.card (resField X))^{f₁}` by the rank-`f₁` free-module count;
   `Nat.card (resField X) = residueCard O` since `X` is a key of degree 1 (B.23's
   `card_resField` at `IsKey X`).

**SIZE.** 22 lines.

**SOURCE.** `EFF.HE6.08` (`K ≅ F_{Q^{f₁}}`); GC-7 (statement-shape mandate).

**TEETH.** `HE6R1` frame audit `K₂ = F_{p²}` (`EFF.HE6R1.18`, arithmetic-audit row
“`[K₂:K] = d_r = 2` and `K = F_p` (since `f₁ = 1`), so `K₂ = F_{p²}` ✓”) → **Lean theorem**
(this node at the C.12 iterate); the numeric leg re-fires at §13.

**ENVIRONMENT.** ENV-C3 (counts a residue object; `hπ` explicit).

---

### NODE C.05 [lemma] [fresh]

**STATEMENT.** *The level-1 reconciliation (GC-2's mandated lemma).* Let `F` be a DEGENERATE
frame: `F.h = 0` (hence `F.e₁ = 1` by coprimality). Then for every `A, f ∈ O[X]` and `j, u, ℓ`:

* `F.stageHeight A = gaussVal A`;
* `dvHgt F f j = npHgt F.key f j` (C.06's heights ARE B's heights);
* `dvSupp F f u ℓ = suppVal F.key f u ℓ` (C.06's support IS B's support);
* `dvSideSet F f u ℓ = sideSet F.key f u ℓ`.

So chapter C's level-1 instance is CHAP-B's committed API, as GC-2 requires — definitionally
up to B.08's inf-identity for `gaussVal`.

**SIGNATURE.**
```lean
namespace Uniformity.Density.Tower

theorem KeyFrame.stageHeight_degenerate (F : KeyFrame O π) (hh : F.h = 0)
    (A : Polynomial O) : F.stageHeight A = gaussVal A

theorem dvHgt_degenerate (F : KeyFrame O π) (hh : F.h = 0) (f : Polynomial O) (j : ℕ) :
    dvHgt F f j = npHgt F.key f j

theorem dvSupp_degenerate (F : KeyFrame O π) (hh : F.h = 0) (f : Polynomial O) (u ℓ : ℕ) :
    dvSupp F f u ℓ = suppVal F.key f u ℓ
```

**DEPENDS.** C.01 · C.02 · C.06 · B.08 (`gaussVal` inf/range identities) · B.11 · B.14.

**PROOF.**
1. `h = 0` and `Nat.Coprime 0 e₁` force `e₁ = 1` (`Nat.coprime_zero_left`).
2. `stageHeight F A = suppVal X A 0 1 = inf_i (1 • v(A.coeff i) + 0) = gaussVal A` — C.02's
   unfold plus B.08's `gaussVal`-as-inf (`gaussVal_range`).
3. The `dvHgt`/`dvSupp`/`dvSideSet` clauses then unfold to B's definitions termwise.

**SIZE.** 18 lines.

**SOURCE.** GC-2 (the ruling's verbatim demand: *"must state a reconciliation lemma
identifying its level-1 instance with B's `npHgt`/`suppVal` definitionally"*); CHAP-B H-1
(the seam: `e₁ = 1, h = 0, dv = addVal, ϖ = π`, twist trivial).

**TEETH.** signed non-applicable (an interface identity).

**ENVIRONMENT.** ENV-C1.

---

### NODE C.06 [def] [fresh]

**STATEMENT.** *The level polygon: heights and cleared support in the `dv`-normalization.*
For a frame `F` and `f ∈ O[X]`: the **level heights** `dvHgt F f j := stageHeight F (dev F.key f j)`
(the `dv`-pins of the `Φ′`-development — `EFF.HE6.10`'s `{(j, dv(A_j))}`), and the **level
cleared support** `dvSupp F f u ℓ := inf_{j ≤ deg f/D′} (ℓ • dvHgt F f j + u * j)` — D-1's
three-object representation at the `dv`-level, same shapes as B.11/B.14, no new type.

**SIGNATURE.**
```lean
namespace Uniformity.Density.Tower

open Uniformity.Density.Leaf in
/-- `dv(A_j)` — the level heights of the `Φ′`-development (`EFF.HE6.10`). -/
noncomputable def dvHgt (F : KeyFrame O π) (f : Polynomial O) (j : ℕ) : ℕ∞ :=
  F.stageHeight (dev F.key f j)

/-- The cleared level support `inf_j (ℓ·dv(A_j) + u·j)` — B.14's shape at the `dv`-level.
The range bound mirrors B.14's (`natDegree f + 1` is safe and convention-free). -/
noncomputable def dvSupp (F : KeyFrame O π) (f : Polynomial O) (u ℓ : ℕ) : ℕ∞ :=
  (Finset.range (f.natDegree + 1)).inf (fun j => ℓ • dvHgt F f j + (u * j : ℕ∞))
```

**DEPENDS.** C.01 · C.02 · B.02 (`dev`) · B.11 · B.14 (shape templates).

**PROOF.** definitional.

**SIZE.** 12 lines.

**SOURCE.** `EFF.HE6.10` (verbatim: `F(Y) := Y^μ + Σ_j A_j(θ)Y^j; P(F) := lower hull of
{(j, dv(A_j))}` — the hull replaced by the cleared support per D-1/GC-2); `EFF.HE3.31`'s
`(★)` one level up.

**TEETH.** signed non-applicable.

**ENVIRONMENT.** ENV-C1.

---

### NODE C.07 [def] [fresh]

**STATEMENT.** *Level sides as argmin data.* Mirroring B.16/B.20 shape for shape:
`DvOnSide F f u ℓ j := (dvSupp F f u ℓ = ℓ • dvHgt F f j + u * j) ∧ dvHgt F f j ≠ ⊤`;
`dvSideSet F f u ℓ : Finset ℕ` (the argmin filter over `range (natDegree + 1)`); and, given
nonemptiness `h`, `dvSideMin/dvSideMax` (the `Finset.min'/max'`), `dvSideLen := max − min`,
`dvSideDeg := dvSideLen / ℓ`.

**SIGNATURE.**
```lean
namespace Uniformity.Density.Tower

def DvOnSide (F : KeyFrame O π) (f : Polynomial O) (u ℓ j : ℕ) : Prop :=
  dvSupp F f u ℓ = ℓ • dvHgt F f j + (u * j : ℕ∞) ∧ dvHgt F f j ≠ ⊤

noncomputable def dvSideSet (F : KeyFrame O π) (f : Polynomial O) (u ℓ : ℕ) : Finset ℕ :=
  (Finset.range (f.natDegree + 1)).filter (fun j => DvOnSide F f u ℓ j)

noncomputable def dvSideMin (F : KeyFrame O π) (f : Polynomial O) (u ℓ : ℕ)
    (h : (dvSideSet F f u ℓ).Nonempty) : ℕ := (dvSideSet F f u ℓ).min' h
-- dvSideMax, dvSideLen, dvSideDeg analogous (one file, one public cluster per B.20 precedent)
```

**DEPENDS.** C.06 · B.16/B.20 (templates).

**PROOF.** definitional (decidability of the filter as in B.16).

**SIZE.** 20 lines.

**SOURCE.** `EFF.HE6.10` (“sides have dv-slope λ = u/ℓ in lowest terms and length
`L_λ = ℓd_λ`”); GC-2 (argmin representation).

**TEETH.** signed non-applicable.

**ENVIRONMENT.** ENV-C1.

---

### NODE C.08 [lemma] [fresh]

**STATEMENT.** *Argmin spacing and the length law at the `dv`-level.* For `0 < ℓ`,
`Nat.Coprime u ℓ`, `F` a frame, `f` monic with `0 < f.natDegree`: any two on-side abscissae
are congruent mod `ℓ` (B.17's argument transposed), hence `ℓ ∣ dvSideLen` and
`dvSideLen = ℓ * dvSideDeg` exactly — `EFF.HE6.10`'s `L_λ = ℓ·d_λ`.

**SIGNATURE.**
```lean
namespace Uniformity.Density.Tower

theorem dvOnSide_modEq (F : KeyFrame O π) (hℓ : 0 < ℓ) (hcop : Nat.Coprime u ℓ)
    {f : Polynomial O} {j j' : ℕ} (hj : DvOnSide F f u ℓ j) (hj' : DvOnSide F f u ℓ j') :
    j ≡ j' [MOD ℓ]

theorem dvSideLen_eq (F : KeyFrame O π) (hℓ : 0 < ℓ) (hcop : Nat.Coprime u ℓ)
    {f : Polynomial O} (h : (dvSideSet F f u ℓ).Nonempty) :
    dvSideLen F f u ℓ h = ℓ * dvSideDeg F f u ℓ h
```

**DEPENDS.** C.06 · C.07 · B.17 (the proof pattern: two attained values of an
`ℕ`-linear form differ by a multiple of `ℓ` once heights are finite; re-run, not consumed —
B.17's constant is `suppVal`-specific).

**PROOF.**
1. From two attained equalities, `ℓ•(H j − H j') = u•(j' − j)` in `ℕ∞`-cleared form (work in
   `ℕ` after finiteness from the `≠ ⊤` clauses).
2. `Nat.Coprime u ℓ` gives `ℓ ∣ (j' − j)` — exactly B.17 step 3.
3. Length law: min and max are on-side, apply step 2; division is exact.

**SIZE.** 22 lines.

**SOURCE.** `EFF.HE6.10`; B.17/B.20 (the level-1 twin whose proof is replayed).

**TEETH.** signed non-applicable (guarded numerically by the §13 frame audit).

**ENVIRONMENT.** ENV-C1.

---

### NODE C.09 [def] [fresh]

**STATEMENT.** *The level datum and the level-2 dictionary numerals.* A **level datum** over a
frame `F` consists of a side `(u, ℓ)` and a residual factor `r` subject to: `0 < ℓ`,
`Nat.Coprime u ℓ`, `u > ℓ * (F.e₁ * F.f₁) * F.h` (the cleared form of `κ = u/ℓ > D′h` —
`EFF.HE6.14`'s standing hypothesis), `r` monic irreducible over the stage field with
`r.coeff 0 ≠ 0` and `d_r := r.natDegree ≥ 1`. Derived numerals (`EFF.HE6R1.18`'s dictionary):
the **level-2 key degree** `D″ := D′ * ℓ * d_r`, and the **seam** `T₂ := d_r * u` (the cleared
integer form of `T₂ = ℓ·d_r·λ` at `λ = u/ℓ`).

**SIGNATURE.**
```lean
namespace Uniformity.Density.Tower

/-- A level-2 label `(λ = u/ℓ, r)` over the frame `F`, with the dictionary numerals
`D″ = D′ℓd_r` and `T₂ = ℓd_rλ` (cleared: `T₂ = d_r·u`).  `EFF.HE6R1.18`. -/
structure LevelDatum (F : KeyFrame O π) (H₀ : ℕ)
    (hpin : npHgt Polynomial.X F.key (sideMin Polynomial.X F.key F.h F.e₁ F.hne) = (H₀ : ℕ∞))
    where
  u : ℕ
  ℓ : ℕ
  r : Polynomial (F.stageField H₀ hpin)
  hℓ : 0 < ℓ
  hcop : Nat.Coprime u ℓ
  /-- `κ > D′h`, cleared of the denominator `ℓ`. -/
  hκ : ℓ * (F.e₁ * F.f₁) * F.h < u
  hrmonic : r.Monic
  hrirr : Irreducible r
  hr0 : r.coeff 0 ≠ 0
  hrdeg : 0 < r.natDegree

/-- `D″ = D′·ℓ·deg r`. -/
def LevelDatum.keyDeg₂ {F : KeyFrame O π} {H₀ hpin} (L : LevelDatum F H₀ hpin) : ℕ :=
  (F.e₁ * F.f₁) * L.ℓ * L.r.natDegree

/-- `T₂ = ℓ·d_r·λ`, cleared to the integer `d_r·u`. -/
def LevelDatum.seam {F : KeyFrame O π} {H₀ hpin} (L : LevelDatum F H₀ hpin) : ℕ :=
  L.r.natDegree * L.u
```

**⚠ FAITHFULNESS.** `r` lives over the CONCRETE stage field (C.03's `AdjoinRoot` iterate),
per GC-7's abstract/concrete split: level data must transport back to `typeOf` definitionally,
so the concrete iterate is mandatory here; ENV-C4 abstract statements are instantiated AT this
carrier. `hκ` is the cleared `κ > D′h`; `hcop`'s load-bearing status is machine-certified in
the corpus (tooth `HE6-T-BADKEY`: a `κ = 6/2` key has two p-adic factors — `EFF.HE6.14`'s
CONDITIONALITY), so it is a structure field, not a per-lemma hypothesis.

**DEPENDS.** C.01 · C.03.

**PROOF.** definitional.

**SIZE.** 26 lines.

**SOURCE.** `EFF.HE6.14` (DEFINITION HE6-1's data: `κ = u/ℓ` lowest terms, `κ > D′h`, `r`
monic irreducible, `r(0) ≠ 0`); `EFF.HE6R1.18` (the dictionary: `D″ = D′ℓd_r = 2·1·2 = 4`,
`T₂ = ℓd_rλ = 2λ`, `K₂ = K(β)`, `μ₂ = deg f_S/D″`).

**TEETH.** `EFF.HE6R1.18`'s frame audit (“Every frame parameter is forced and every one
checks”) → **Lean theorem** at C.10 + **executable regression** at §13 (the
`(e₁,f₁,h) = (2,1,1), Φ′ = x²−π, D″ = 4, T₂ = 2λ, μ₂ = 2` instance re-fired at `q = 3` AND
the `q = 2` analogue).

**ENVIRONMENT.** ENV-C1.

---

### NODE C.10 [lemma] [fresh]

**STATEMENT.** *Dictionary arithmetic.* For any level datum `L` over `F`: (i)
`L.keyDeg₂ = (F.e₁ * L.ℓ) * (F.f₁ * L.r.natDegree)` — the `D″ = (e₁ℓ)(f₁d_r)` regrouping that
drives the peel's sandwich (`EFF.HE6R1.16`'s audit); (ii) `L.seam = L.ℓ * L.r.natDegree * L.u / L.ℓ`
in cleared form: `L.ℓ * L.seam = L.keyDeg₂ * L.u / (F.e₁ * F.f₁)` is avoided — the honest
integer identity is `L.ℓ * L.seam = (L.ℓ * L.r.natDegree) * L.u`; (iii) at `L.ℓ = 1` the
dictionary degenerates benignly (`EFF.HE6R1.06`): `keyDeg₂ = D′·d_r`, `seam = d_r·u`, and the
level-2 normalization scale collapses (`dv₂ = dv`-scale, the C.11 recursion at `ℓ = 1`);
(iv) `4 ≤ L.keyDeg₂` whenever `2 ≤ F.e₁ * F.f₁` and `2 ≤ L.ℓ * L.r.natDegree` (the jump-frame
floor `L_λ ≥ 4` feeding §5).

**SIGNATURE.**
```lean
namespace Uniformity.Density.Tower

theorem LevelDatum.keyDeg₂_regroup {F : KeyFrame O π} {H₀ hpin} (L : LevelDatum F H₀ hpin) :
    L.keyDeg₂ = (F.e₁ * L.ℓ) * (F.f₁ * L.r.natDegree)

theorem LevelDatum.seam_mul {F : KeyFrame O π} {H₀ hpin} (L : LevelDatum F H₀ hpin) :
    L.ℓ * L.seam = (L.ℓ * L.r.natDegree) * L.u

theorem LevelDatum.four_le_keyDeg₂ {F : KeyFrame O π} {H₀ hpin} (L : LevelDatum F H₀ hpin)
    (hD : 2 ≤ F.e₁ * F.f₁) (hjump : 2 ≤ L.ℓ * L.r.natDegree) : 4 ≤ L.keyDeg₂
```

**DEPENDS.** C.09.

**PROOF.** 1. `ring`. 2. `ring`. 3. `Nat.mul_le_mul` as in H.03's pattern; `omega`/`nlinarith`
fallback.

**SIZE.** 12 lines.

**SOURCE.** `EFF.HE6R1.16` (audit: `D″ = D′ℓd_r = (e₁f₁)ℓd_r = (e₁ℓ)(f₁d_r)` ✓);
`EFF.HE6R1.18` (audit rows); `EFF.HE6R1.06` (the `ℓ = 1` degeneration table);
`EFF.HE6R1.08`/(F1's non-propagation arithmetic `m ≥ 2 ∧ ℓ₂d_{r₂} ≥ 2 ⟹ ≥ 4`).

**TEETH.** `EFF.HE6R1.18` audit row → **Lean theorem** (this node); the frame instance values
re-fire at §13 per GC-11.

**ENVIRONMENT.** ENV-C5 (arithmetic only; stated over the structure for keying).

---

### NODE C.11 [def] [fresh]

**STATEMENT.** *The level-2 heights — the tower recursion.* For a level datum `L` over `F` and
a level-2 key `Ψ` (any monic polynomial of degree `D″`; C.13 supplies the canonical ones):
the **level-2 slot height** of a coefficient `A ∈ O[X]` is
`dv2Hgt L A := dvSupp F A L.u L.ℓ` — *the level-1 cleared support of `A` at the level's side*;
the **level-2 pins** of `f` are `dv2Pin L Ψ f j := dv2Hgt L (dev Ψ f j)`; and the **level-2
cleared support** is `dv2Supp L Ψ f u₂ ℓ₂ := inf_j (ℓ₂ • dv2Pin L Ψ f j + u₂ * j)`. All
`ℕ∞`-valued by construction (C-H14 discharged: each level's heights are infima of `ℕ`-linear
forms in the coefficients' `addVal`s — the normalizer offset never appears as a subtraction
because the cleared pair `(u, ℓ)` carries it, which is exactly the mechanism GC-2's ruling
names via `EFF.HE6R1.13`(b)).

**SIGNATURE.**
```lean
namespace Uniformity.Density.Tower

/-- The level-2 slot height of a coefficient: the level-1 support value at the side.
This equality of shapes IS the tower recursion (design note above). -/
noncomputable def dv2Hgt {F : KeyFrame O π} {H₀ hpin} (L : LevelDatum F H₀ hpin)
    (A : Polynomial O) : ℕ∞ :=
  dvSupp F A L.u L.ℓ

noncomputable def dv2Pin {F : KeyFrame O π} {H₀ hpin} (L : LevelDatum F H₀ hpin)
    (Ψ f : Polynomial O) (j : ℕ) : ℕ∞ :=
  dv2Hgt L (dev Ψ f j)

noncomputable def dv2Supp {F : KeyFrame O π} {H₀ hpin} (L : LevelDatum F H₀ hpin)
    (Ψ f : Polynomial O) (u₂ ℓ₂ : ℕ) : ℕ∞ :=
  (Finset.range (f.natDegree + 1)).inf (fun j => ℓ₂ • dv2Pin L Ψ f j + (u₂ * j : ℕ∞))
```

**⚠ FAITHFULNESS.** The corpus's `dv₂` is defined at level-2 POINTS (`dv₂(A(ξ))`,
`EFF.HE6R1.18`); this definition is the cleared-support recast, and the statement tying the
two — `dv2Hgt` computes the exact value at every root of every factor carrying the label —
is §4's slot-exactness layer (C.25/C.26), NOT this definition. Consumers must depend on those
lemmas, never on an assumed exactness of this `def`. The seam identity
`dv2Hgt L (Ψ-const-coeff) = T₂`-family facts are C.14/§5 content.

**DEPENDS.** C.06 · C.09 · B.02 (`dev`).

**PROOF.** definitional.

**SIZE.** 16 lines.

**SOURCE.** `EFF.HE6R1.18` (the level-2 frame: `T₂ = 2λ`, “the level-2 layer over
`K₂ = F_{p²}` is fresh”); `EFF.HE6R1.13`(b) (the translation identity this shape makes
stateable); GC-2 (three objects at every level).

**TEETH.** signed non-applicable at the definition; exactness teeth live on C.25/C.26.

**ENVIRONMENT.** ENV-C1.

---

### NODE C.12 [def] [fresh]

**STATEMENT.** *The level-2 residue field.* `level2Field L := AdjoinRoot L.r` — the
`resField` pattern iterated a second time over the stage field (GC-7: `K₂ = K(β)` as an
explicit quotient; `EFF.HE6R1.18`'s `K₂ = F_{p²}`). Companion (public name
`card_level2Field`): under `[Finite (ResidueField O)]` and the frame pin, `level2Field L` is a
finite field with `Module.finrank (stageField …) (level2Field L) = L.r.natDegree` and
`Nat.card (level2Field L) = stageCard F ^ L.r.natDegree = residueCard O ^ (F.f₁ * L.r.natDegree)`.

**SIGNATURE.**
```lean
namespace Uniformity.Density.Tower

/-- `K₂ = K(β)`, the second `AdjoinRoot` iterate (GC-7). -/
abbrev level2Field {F : KeyFrame O π} {H₀ hpin} (L : LevelDatum F H₀ hpin) : Type _ :=
  AdjoinRoot L.r

theorem card_level2Field {F : KeyFrame O π} {H₀ hpin} (L : LevelDatum F H₀ hpin)
    [Finite (ResidueField O)] (hπ : Irreducible π) :
    Nat.card (level2Field L) = residueCard O ^ (F.f₁ * L.r.natDegree)
```

**DEPENDS.** C.03 · C.04 · C.09.

**PROOF.**
1. Field/finite instances from `L.hrirr` as in C.04 steps 1–2.
2. `Nat.card (level2Field L) = (Nat.card (stageField …))^{d_r}` (rank-`d_r` count) and C.04's
   `Nat.card (stageField …) = residueCard O ^ f₁`; `pow_mul` closes.

**SIZE.** 18 lines.

**SOURCE.** `EFF.HE6R1.18` (audit: “`K₂ = K(β)` with `[K₂:K] = d_r = 2` and `K = F_p`
(since `f₁ = 1`), so `K₂ = F_{p²}` ✓”); GC-7.

**TEETH.** the same `EFF.HE6R1.18` audit row as C.04 → **Lean theorem**; §13 regression.

**ENVIRONMENT.** ENV-C3.

**⚠ DEPTH-3 NOTE (GC-7's medium-confidence leg).** This is the depth-2 iterate. §9's
third-stage nodes need the depth-3 iterate `AdjoinRoot r₃` over `level2Field`; no new
mechanism, but nobody has elaborated a depth-3 `AdjoinRoot` tower in `leanfinal` — if the
instance chain fails to elaborate at stub stage, GC-7's recorded fallback (a level structure
carrying abstract `[Field K_r]` with a specified `Algebra` chain) triggers a DECISION block
here. Flagged to §16.

---

### NODE C.13 [def] [fresh]

**STATEMENT.** *What it is to be a level-2 test key.* `IsTestKey L Ψ : Prop` holds iff `Ψ` is
monic with `Ψ.natDegree = L.keyDeg₂`, and the `Φ′`-development of `Ψ` transcribes DEFINITION
HE6-1's construction output: writing `d := L.r.natDegree`, (i) `dev F.key Ψ (L.ℓ * d) = 1`
(top), (ii) `dev F.key Ψ b = 0` for `b < L.ℓ * d` **not** a multiple of `L.ℓ`, (iii) for
`t < d` with `L.r.coeff t ≠ 0`: `F.stageHeight (dev F.key Ψ (L.ℓ * t)) = ((d − t) * L.u : ℕ∞)`
and the slot-residue read of that coefficient equals `L.r.coeff t` (read through C.03's
carriers at the `n(k)`-normalizer; the ϖ-read coset factor `η^{−q(k)}` is absorbed because
every height here sits in the fullness regime — `EFF.HE6.13`'s NON-PROPAGATION route (1));
(iv) `dev F.key Ψ (L.ℓ * t) = 0` when `L.r.coeff t = 0`.

**SIGNATURE.**
```lean
namespace Uniformity.Density.Tower

/-- `Ψ_{κ,r}`-hood: the slot-pinned shape of `EFF.HE6.14`'s enlarged test family, as a
predicate (the construction is non-canonical; C.14 supplies existence). -/
def IsTestKey {F : KeyFrame O π} {H₀ hpin} (L : LevelDatum F H₀ hpin)
    (Ψ : Polynomial O) : Prop :=
  Ψ.Monic ∧ Ψ.natDegree = L.keyDeg₂ ∧
  dev F.key Ψ (L.ℓ * L.r.natDegree) = 1 ∧
  (∀ b < L.ℓ * L.r.natDegree, ¬ L.ℓ ∣ b → dev F.key Ψ b = 0) ∧
  (∀ t < L.r.natDegree,
    (L.r.coeff t = 0 → dev F.key Ψ (L.ℓ * t) = 0) ∧
    (L.r.coeff t ≠ 0 →
      F.stageHeight (dev F.key Ψ (L.ℓ * t)) = (((L.r.natDegree − t) * L.u : ℕ) : ℕ∞) ∧
      slotRes F H₀ hpin ((L.r.natDegree − t) * L.u) (dev F.key Ψ (L.ℓ * t)) = L.r.coeff t))
```

where `slotRes` is §4's normalized slot-residue read (C.21) — the A3 F-1 TERMINAL form
`γ_k(A) = Σ_t res(a_{i₀+e₁t}·π^{−(k−(i₀+e₁t)h)/e₁})·η^t` packaged over C.03's carriers.

**⚠ ORDERING NOTE.** `slotRes` (C.21) is a §4 object consumed here; the DAG order is
C.21 → C.13. The index places C.13 in §3 because it is frame data; the fleet fires it after
§4's C.21 lands.

**DEPENDS.** C.01 · C.02 · C.09 · C.21 (§4's normalized slot residue) · B.02.

**PROOF.** definitional.

**SIZE.** 24 lines.

**SOURCE.** `EFF.HE6.14` (DEFINITION HE6-1 verbatim: `Ψ_{κ,r} := Φ′^{ℓd} + Σ_{t<d} B_t·Φ′^{ℓt}`,
`B_t` with `dv(B_t) = (d−t)u` and residue `c_t`, `B_t := 0` if `c_t = 0`); `EFF.HE6.13` (the
corrected LIFT display whose fullness clause licenses the residue clause); A3 F-1 via
`spec/EFF-HE6.md` `.58` (the normalized-γ TERMINAL — C-H8 discipline).

**TEETH.** `EFF.HE6.14`'s audit (`deg(B_tΦ′^{ℓt}) < D″`; lift heights `> (D′−1)h`) →
**Lean theorem** at C.14 steps 2–3.

**ENVIRONMENT.** ENV-C1 (`hπ` explicit via `slotRes`).

---

### NODE C.14 [lemma] [fresh]

**STATEMENT.** *Test keys exist (the enlarged family, closure-free).* For every level datum
`L` over `F` with `2 ≤ F.e₁ * F.f₁`, and `[Finite (ResidueField O)]`, there exists `Ψ` with
`IsTestKey L Ψ`. The construction is `EFF.HE6.14`'s: lift each nonzero `c_t := L.r.coeff t`
to `B_t ∈ O[X]` with `deg B_t < D′`, `stageHeight = (d−t)u` and slot residue `c_t` — the
exact-height stage lift of `LEMMA GENHN-LIFT`, consumed as **H.54's `stageLift'` + H.55
(height) + H.56 (residue)**, legal because every height `(d−t)u > (D′−1)h` sits in the
fullness regime (`EFF.HE6.13`'s uniform sufficient condition) — then set
`Ψ := Φ′^{ℓd} + Σ_t B_t Φ′^{ℓt}`. The degenerate `D′ = 1` frame takes the elementary lift
`B_t := π^{(d−t)u} · (unit lift of c_t)` (same file, same public name, internal case split).

**SIGNATURE.**
```lean
namespace Uniformity.Density.Tower

theorem exists_testKey {F : KeyFrame O π} {H₀ hpin} (L : LevelDatum F H₀ hpin)
    [Finite (ResidueField O)] (hπ : Irreducible π) :
    ∃ Ψ : Polynomial O, IsTestKey L Ψ
```

**DEPENDS.** C.09 · C.10 · C.13 · **H.54 (`stageLift'`) · H.55 · H.56 · H.57** (the H §8
entry point, GC-5; `normIdx` NOT consumed) · B.02–B.06 (development uniqueness for reading
the `dev`-clauses off the explicit sum) · landed `two_le_residueCard`.

**PROOF.**
1. Fullness arithmetic: `(d − t)·u ≥ u > ℓ·D′·h ≥ D′·h > (D′−1)·h` for `t < d` (`L.hκ`,
   `omega`) — `EFF.HE6.13`'s NON-PROPAGATION route (1), re-derived.
2. At `2 ≤ D′`: build the `GenreDatum` `G := ⟨residueCard O, F.e₁, F.f₁, 2, F.h, …⟩`
   (μ-field dummy `2` — H.54's lift reads only `(Q, e₁, f₁, h, M)`; ⚠ if the stub stage
   finds `stageLift'` reading `G.μ`, RE-PLAN to H per GC-5, do not fork the lift) and take
   `B_t := stageLift' G π ((d−t)·L.u) …` per nonzero `c_t`; H.55 gives `deg < D′` and the
   exact height, H.56 gives the residue.
3. At `D′ = 1`: `B_t := π^{(d−t)u} · c̃_t` with `c̃_t` any unit lift; height and residue are
   B.08-level facts.
4. Read clauses (i)–(iv) of `IsTestKey` off the explicit sum by development uniqueness
   (B.05/B.06): each `B_tΦ′^{ℓt}` has degree `< D′(1+ℓt) ≤ D″` (`EFF.HE6.14`'s audit,
   step: `1 + ℓt ≤ ℓd ⟺ 1 ≤ ℓ(d−t)`), so the displayed sum IS the development.

**SIZE.** 38 lines. **Split candidate:** step 2's `GenreDatum` plumbing may become C.14a if
the elaboration is heavy.

**SOURCE.** `EFF.HE6.14` (construction + audit, verbatim); `EFF.HE6.13` (LEMMA HE6-1L's
fullness clause + the `[r1]` NON-PROPAGATION inventory); CHAP-H H.54–H.57 (the lift layer,
consumed per H-14).

**TEETH.** `EFF.HE6.14` audit → **Lean theorem** (steps 1, 4); `HE6-T-BADKEY`
(`gcd(u,ℓ) = 1` load-bearing) → carried at C.09's structure field, **executable regression**
retained at §13.

**ENVIRONMENT.** ENV-C3 (`hπ` explicit; finiteness for the residue count in H.56's
instantiation).

---

---

## 4. §4 — THE GAUGE LAYER: NORMALIZERS, THE LETTER, THE COCYCLE

> **Design note (how the closure-dependent gauge is recast).** The corpus's gauge layer reads
> residues *at points*: `res(A(ξ)/ϖ(ξ)^k)` for `(T1)/(T2)` points `ξ ∈ K̄₀`, transported by
> per-point embeddings `ι_ξ` (`EFF.HE6.08/.11/.15`). None of that types in `leanfinal`. The
> recast, following A3 F-1's own TERMINAL display (`EFF.HE6.58` — whose derivation is
> point-free algebra): the **normalized slot residue** `γ_k(A) ∈ K` is defined directly from
> the coefficients by `digAt`-reads (C.21), the ϖ-read is the `η^{−q(k)}`-twist of it (C.22),
> and every downstream law is stated about these `O`-level objects. The corpus's
> "at every (T1)/(T2) point ξ, transported by `ι_ξ`" becomes: consumers read values through
> `addVal ∘ norm` over `AdjoinRoot g` (C.27's exactness), never at points. The corpus's ϖ
> itself (`x^{i₀}π^{a₀}`, possibly `a₀ < 0`, `EFF.HE6.11`) is never constructed — only its
> exponent arithmetic (`i₀`, `q(k)`) survives, which is exactly what `EFF.HE6.11` says is
> "all that is ever used".

### NODE C.15 [def] [fresh]

**STATEMENT.** *The normalizer exponents.* For a frame `F` and `k : ℕ`: the **slot index**
`slotIdx F k` = the unique `0 ≤ i < e₁` with `i·h ≡ k (mod e₁)` (exists and is unique by
`Nat.Coprime h e₁` — H.51's bijection); and the **twist exponent**
`twistExp F k := (slotIdx F 1 * k − slotIdx F k) / e₁` — `EFF.HE6.13`-RIDER's `q(k)`, defined
by `i₀·k = i(k) + q(k)·e₁` with `i₀ = slotIdx F 1` (ϖ's `x`-exponent, since
`i₀h + e₁a₀ = 1` forces `i₀h ≡ 1`).

**SIGNATURE.**
```lean
namespace Uniformity.Density.Tower

/-- `i(k)`: the unique `0 ≤ i < e₁` with `ih ≡ k (mod e₁)` (`EFF.HE6.58`'s `i(k)`;
`EFF.HE6.13`'s `i₀(k)`). Total: at the degenerate `e₁ = 1` it is `0`. -/
noncomputable def KeyFrame.slotIdx (F : KeyFrame O π) (k : ℕ) : ℕ :=
  Nat.find (F.slotIdx_exists k)   -- packaged via the H.51 bijection; see C.16

/-- `q(k)`: the ϖ-vs-`n(k)` twist exponent, `i₀·k = i(k) + q(k)·e₁` (`EFF.HE6.13` RIDER). -/
noncomputable def KeyFrame.twistExp (F : KeyFrame O π) (k : ℕ) : ℕ :=
  (F.slotIdx 1 * k - F.slotIdx k) / F.e₁
```

**DEPENDS.** C.01 · H.51 (`class_sep_bij` — the mod-`e₁` bijection `i ↦ ih`).

**PROOF.** definitional (the existence witness is C.16's business; the `Nat.find` packaging
may become `(h⁻¹·k) % e₁` via `Nat.ModEq` inverse arithmetic at the formalizer's choice —
the SPEC is the defining congruence + range, C.16, not the implementation).

**SIZE.** 14 lines.

**SOURCE.** `EFF.HE6.11` (ϖ's exponents: `i₀h + e₁a₀ = 1`, `0 ≤ i₀ < e₁`); `EFF.HE6.13`
(RIDER: `i₀k = i + qe₁`, `a₀k − a = −qh`); `EFF.HE6.58` (`i(k)` as re-displayed).

**TEETH.** `EFF.HE6.11`'s witness audit (`(e₁,h) = (2,3) ⟹ i₀ = 1, a₀ = −1`) →
**executable regression** at §13 (`slotIdx` table at the gate frames); the `a₀ < 0`
phenomenon is DESIGNED OUT (no `a₀` is ever computed — C-H14).

**ENVIRONMENT.** ENV-C5 (pure arithmetic on the frame's numerals).

---

### NODE C.16 [lemma] [fresh]

**STATEMENT.** *Slot-index laws.* For every `k`: (i) `slotIdx F k < F.e₁` and
`slotIdx F k * F.h ≡ k [MOD F.e₁]`; (ii) uniqueness: any `i < e₁` with `ih ≡ k (mod e₁)`
equals `slotIdx F k`; (iii) the twist identity
`F.slotIdx 1 * k = F.slotIdx k + F.e₁ * F.twistExp F k`; (iv) `slotIdx` is `e₁`-periodic in
`k` and `slotIdx F k = k % e₁`-compatible at `h ≡ 1`; (v) at `F.e₁ = 1`: `slotIdx = 0`,
`twistExp = 0` (the degenerate/CHAP-B seam — no twist, C-H1).

**SIGNATURE.**
```lean
namespace Uniformity.Density.Tower

theorem KeyFrame.slotIdx_spec (F : KeyFrame O π) (k : ℕ) :
    F.slotIdx k < F.e₁ ∧ F.slotIdx k * F.h ≡ k [MOD F.e₁]

theorem KeyFrame.slotIdx_unique (F : KeyFrame O π) {k i : ℕ} (hi : i < F.e₁)
    (hcong : i * F.h ≡ k [MOD F.e₁]) : i = F.slotIdx k

theorem KeyFrame.twistExp_spec (F : KeyFrame O π) (k : ℕ) :
    F.slotIdx 1 * k = F.slotIdx k + F.e₁ * F.twistExp F k
```

**DEPENDS.** C.15 · H.51 (`class_sep`, `class_sep_bij`).

**PROOF.**
1. (i)/(ii): H.51's bijection `i ↦ ih mod e₁` on `range e₁` (coprimality), inverted at `k`.
2. (iii): `i₀k ≡ k·h·h⁻¹`-arithmetic — `(i₀k)·h ≡ k (mod e₁)` from `i₀h ≡ 1`, so
   `i₀k mod e₁ = slotIdx k` by (ii); the division is exact and nonneg (both sides congruent,
   `slotIdx k < e₁ ≤ i₀k + e₁`; the `i₀k < e₁` corner gives `q = 0` with `i₀k = slotIdx k`).
3. (v): at `e₁ = 1` everything is `mod 1`.

**SIZE.** 24 lines.

**SOURCE.** `EFF.HE6.13` (RIDER); `EFF.HE6.15` (the (T1) role: *"`i ↦ ih mod e₁` is a
bijection of `ℤ/e₁` because `gcd(h,e₁) = 1`"* — verbatim the proof mechanism).

**TEETH.** the `.13` audit's `q(3) = 1` at `(2,2,3)` → **executable regression** (§13 gate
value).

**ENVIRONMENT.** ENV-C5.

---

### NODE C.17 [def] [fresh]

**STATEMENT.** *The slot window `T(k)`.* `slotWindow F k := {t ∈ range F.f₁ :
(slotIdx F k + F.e₁ * t) * F.h ≤ k}` — `EFF.HE6.13`'s
`T(k) = {t < f₁ : k ≥ (i₀ + e₁t)·h}`, the set of slots available at height `k`.

**SIGNATURE.**
```lean
namespace Uniformity.Density.Tower

/-- `T(k) := {t < f₁ : k ≥ (i₀(k) + e₁t)h}` (`EFF.HE6.13`). -/
noncomputable def KeyFrame.slotWindow (F : KeyFrame O π) (k : ℕ) : Finset ℕ :=
  (Finset.range F.f₁).filter (fun t => (F.slotIdx k + F.e₁ * t) * F.h ≤ k)
```

**DEPENDS.** C.15.

**PROOF.** definitional.

**SIZE.** 6 lines.

**SOURCE.** `EFF.HE6.13` (the `T(k)` display, verbatim).

**TEETH.** the `.12` audit (`(3,1,2)`: `T(1) = ∅`; `(1,2,1)`: `T(0) = {0}` proper) →
**executable regression** at §13.

**ENVIRONMENT.** ENV-C5.

---

### NODE C.18 [lemma] [fresh]

**STATEMENT.** *Window thresholds (`EFF.HE6.13`'s audited clauses).* (i) **Fullness:**
`slotWindow F k = range F.f₁ ↔ (slotIdx F k + F.e₁*(F.f₁ − 1)) * F.h ≤ k`. (ii) **Uniform
sufficiency:** `(F.e₁*F.f₁ − 1) * F.h ≤ k → slotWindow F k = range F.f₁` (from
`i₀ + e₁(f₁−1) ≤ e₁f₁ − 1` since `i₀ ≤ e₁ − 1`). (iii) **Downward closure:** `t ∈ slotWindow`
and `t' ≤ t` imply `t' ∈ slotWindow`. (iv) at `F.h = 0`: every window is full.

**SIGNATURE.**
```lean
namespace Uniformity.Density.Tower

theorem KeyFrame.slotWindow_full_iff (F : KeyFrame O π) (hf : 0 < F.f₁) (k : ℕ) :
    F.slotWindow k = Finset.range F.f₁
      ↔ (F.slotIdx k + F.e₁ * (F.f₁ - 1)) * F.h ≤ k

theorem KeyFrame.slotWindow_full_of_le (F : KeyFrame O π) (k : ℕ)
    (hk : (F.e₁ * F.f₁ - 1) * F.h ≤ k) : F.slotWindow k = Finset.range F.f₁
```

**DEPENDS.** C.15 · C.16 · C.17.

**PROOF.**
1. (iii) first: the filter's bound is monotone in `t` (`Nat.mul_le_mul`); (i) follows —
   fullness iff the top slot `t = f₁ − 1` is in.
2. (ii): `i₀ + e₁(f₁−1) ≤ (e₁−1) + e₁f₁ − e₁ = e₁f₁ − 1` — `EFF.HE6.13`'s audit clause (i),
   re-derived; `omega` after C.16(i)'s bound.

**SIZE.** 16 lines.

**SOURCE.** `EFF.HE6.13` (the fullness clause `k ≥ (i₀(k) + e₁(f₁−1))h`, the uniform
`k ≥ (D′−1)h`, both audited there).

**TEETH.** `EFF.HE6.13`'s audit (i) → **Lean theorem** (clause (ii) here).

**ENVIRONMENT.** ENV-C5.

---

### NODE C.19 [def] [fresh]

**STATEMENT.** *The stage letter.* `stageLetter F H₀ hpin := AdjoinRoot.root (frameRes F H₀ hpin)
∈ stageField F H₀ hpin` — the recast of `EFF.HE6.08`'s `η_θ = res(θ^{e₁}π^{−h})`: the
canonical residual root, generating `K` over `resField X` with power basis
`{1, η, …, η^{f₁−1}}` (companion lemma, the (T2)-role carrier). `η` is a unit: `ψ(0) ≠ 0`
because the frame residual has nonzero constant term (B.30 at the frame's side).

**SIGNATURE.**
```lean
namespace Uniformity.Density.Tower

noncomputable def KeyFrame.stageLetter (F : KeyFrame O π) (H₀ : ℕ) (hpin : _) :
    F.stageField H₀ hpin :=
  AdjoinRoot.root (F.frameRes H₀ hpin)

theorem KeyFrame.stageLetter_ne_zero (F : KeyFrame O π) (hπ : Irreducible π)
    (H₀ : ℕ) (hpin : _) : F.stageLetter H₀ hpin ≠ 0
```

with the power-basis statement (`AdjoinRoot.powerBasis` at `Irreducible ψ`) as a companion
in the same file.

**DEPENDS.** C.03 · C.04 · B.30 (`resPoly` has nonzero constant term — gives `ψ(0) ≠ 0`,
hence root ≠ 0).

**PROOF.** 1. definitional. 2. `η = 0 → ψ(0) = 0`, contradicting B.30's constant-term
clause applied to the frame's side.

**SIZE.** 14 lines.

**SOURCE.** `EFF.HE6.08` (`η_θ`, `K = F_Q(η_θ)`); `EFF.HE6.15` (the (T2) role:
`{1, η, …, η^{f₁−1}}` `F_Q`-independent — here the `AdjoinRoot` power basis).

**TEETH.** signed non-applicable.

**ENVIRONMENT.** ENV-C1 (`hπ` explicit).

---

### NODE C.20 [lemma] [fresh]

**STATEMENT.** *Class separation of slot heights, `O[x]`-level.* For `A ∈ O[X]` with
`deg A < D′` and `i < D′`: the slot value `F.e₁ • addVal (A.coeff i) + i * F.h ≡ i * F.h
(mod F.e₁)`; consequently (i) a slot value equals `k` only if `i ≡ slotIdx F k (mod e₁)`;
(ii) if `stageHeight F A = (k : ℕ∞)` then the minimum is attained, and attained ONLY in the
class `slotIdx F k`; (iii) **the emptiness clause**: if `slotWindow F k = ∅` then NO `A` with
`deg A < D′` has `stageHeight F A = k` (`EFF.HE6.13`'s twist-free clause — "if `T(k) = ∅`
the height `k` is not attained at all"). Cross-class ties cannot occur (H.52's mechanism at
the `O[x]` carrier).

**SIGNATURE.**
```lean
namespace Uniformity.Density.Tower

theorem KeyFrame.stageHeight_class (F : KeyFrame O π) {A : Polynomial O} {i k : ℕ}
    (hi : i ≤ A.natDegree) (hval : F.e₁ • addVal O (A.coeff i) + (i * F.h : ℕ∞) = (k : ℕ∞)) :
    i * F.h ≡ k [MOD F.e₁]

theorem KeyFrame.stageHeight_unattained (F : KeyFrame O π) {A : Polynomial O} {k : ℕ}
    (hA : A.natDegree < F.e₁ * F.f₁) (hwin : F.slotWindow k = ∅) :
    F.stageHeight A ≠ (k : ℕ∞)
```

**DEPENDS.** C.02 · C.15 · C.16 · C.17 · H.52 (`slot_height_injective` — the arithmetic
no-tie engine, instantiated).

**PROOF.**
1. (i): `e₁•v + ih ≡ ih (mod e₁)`, then C.16's uniqueness.
2. (ii): the inf over a finite range is attained where finite; every attaining slot passes
   (i).
3. (iii): an attaining slot `i = slotIdx k + e₁t` needs `v(a_i) = (k − ih)/e₁ ≥ 0`, i.e.
   `ih ≤ k`, i.e. `t ∈ slotWindow F k` — empty window, no slot, contradiction with (ii).
   (`t < f₁` from `i < D′`.)

**SIZE.** 26 lines.

**SOURCE.** `EFF.HE6.15` (the (T1) role, verbatim mechanism); `EFF.HE6.13` (the
`T(k) = ∅` clause).

**TEETH.** `HE6R1`'s P3 NOT-onto rows (`k < λ` fails — `EFF.HE6R1.27`) → **executable
regression** retained (§13 re-fires one row at `q = 2` and `q = 3`).

**ENVIRONMENT.** ENV-C1.

---

### NODE C.21 [def] [fresh]

**STATEMENT.** *The normalized slot residue `γ_k(A)` — A3 F-1's TERMINAL display, verbatim in
`digAt`-form.* For `A ∈ O[X]` and `k : ℕ`, with `i := slotIdx F k`:

```
slotRes F H₀ hpin k A := Σ_{t ∈ slotWindow F k}
    (algebraMap … (digAt π ((k − (i + e₁t)·h)/e₁) (A.coeff (i + e₁t)))) · η^t  ∈ stageField F,
```

where `digAt π m x` is B.24's digit read (`res(x·π^{−m})` for `π^m ∣ x`, junk `0` otherwise —
which implements `EFF.HE6.58`'s "a coefficient whose pin lies strictly above height `k`
contributes zero" *and* its normalizer `π^{−(k−jh)/e₁}` in one landed object), and the sum
ranges over the slot window (slots outside it would need negative digit indices and are
exactly the pins forced above height `k`).

**SIGNATURE.**
```lean
namespace Uniformity.Density.Tower

open Uniformity.Density.Leaf in
/-- A3 F-1's normalized slot residue
`γ_k(A) = Σ_t res(a_{i+e₁t}·π^{−(k−(i+e₁t)h)/e₁})·η^t` (`EFF.HE6.58`, TERMINAL layer of the
`HE6-SLOT-SEAM` chain — the frozen bare-`γ` display is DEAD, C-H8). -/
noncomputable def KeyFrame.slotRes (F : KeyFrame O π) (H₀ : ℕ) (hpin : _) (k : ℕ)
    (A : Polynomial O) : F.stageField H₀ hpin :=
  (F.slotWindow k).sum fun t =>
    algebraMap _ _ (digAt π ((k - (F.slotIdx k + F.e₁ * t) * F.h) / F.e₁)
        (A.coeff (F.slotIdx k + F.e₁ * t)))
      * (F.stageLetter H₀ hpin) ^ t
```

(the `algebraMap` route `ResidueField O → resField X → stageField` is the composite of the
landed quotient maps; one private helper may name it.)

**⚠ FAITHFULNESS (trust-boundary definition — the chapter's most consequential recast).**
Three clauses. (i) This is the **n(k)-read** (`res(A(θ)/n(k)(θ))`), per `EFF.HE6.58`'s
derivation `res(A(ξ)/n(k)(ξ)) = ι_ξ(γ_k(A))` — the ϖ-read is C.22. (ii) The TERMINAL-form
discipline (C-H8): the frozen `HE6-SLOT-SEAM` display's bare `γ = Σ res(a_{i₀+e₁t})η^t` is
**vacuous** (its tying coefficients have positive valuation — `EFF.HE6.58`'s compiler
confirmation), and this definition is the corrected `γ_k`. Any node or stub matching the
bare form is a defect. (iii) The per-point embedding `ι_ξ` is eliminated: `γ_k(A)` is
K-valued data; transport to factors happens through `addVal ∘ norm` statements (C.27), never
through embeddings into a closure. Flagged to §16 for the cross-read against `EFF.HE6.58`'s
six displays.

**DEPENDS.** C.02 · C.15 · C.17 · C.19 · B.24 (`digAt`, `digAt_eq`, `digAt_eq_zero_iff`).

**PROOF.** definitional.

**SIZE.** 22 lines.

**SOURCE.** `EFF.HE6.58` (A3 F-1, the six-display correction, verbatim); `EFF.HE6.15`
(LEMMA HE6-0″, whose consumed residue this is); `EFF.HE6.11` (`R_λ`'s coefficient reads,
which C.25 builds from this).

**TEETH.** the divisibility sanity `(k − jh)/e₁ ∈ ℕ` on the window (exact division by
C.16's congruence) → **Lean theorem** (a private lemma in this file, named in the stub);
`EFF.HE6.58`'s exponent-identity audit → re-derived at C.27's proof step 2.

**ENVIRONMENT.** ENV-C1 (`hπ` explicit through `digAt`).

---

### NODE C.22 [def] [fresh]

**STATEMENT.** *The ϖ-read (twisted read).* `twistRead F H₀ hpin k A :=
(stageLetter F H₀ hpin)⁻¹ ^ (twistExp F k) * slotRes F H₀ hpin k A` — the corpus's
`res(A(ξ)/ϖ(ξ)^k) = ι_ξ(γ_k(A))·η_ξ^{−q(k)}` (`EFF.HE6.58`'s corrected conclusion; the
`[r2]`-corrected sign, TERMINAL: **minus** `q`).

**SIGNATURE.**
```lean
namespace Uniformity.Density.Tower

/-- The ϖ-read residue `γ_k(A)·η^{−q(k)}` (`EFF.HE6.15` [r2]-corrected sign; `EFF.HE6.58`
TERMINAL).  All corpus residual polynomials (`R_λ`, C.25) read through THIS. -/
noncomputable def KeyFrame.twistRead (F : KeyFrame O π) (H₀ : ℕ) (hpin : _) (k : ℕ)
    (A : Polynomial O) : F.stageField H₀ hpin :=
  (F.stageLetter H₀ hpin)⁻¹ ^ (F.twistExp k) * F.slotRes H₀ hpin k A
```

**⚠ FAITHFULNESS.** The corpus DERIVES this from ϖ (`res(n(k)/ϖ^k) = η^{−q}`); here it is a
DEFINITION, because ϖ itself (`∈ K₀[x]`, possibly negative `π`-exponent) is never
constructed. The definitional content matches the corpus's `[r2]`-corrected identity by the
RIDER's computation, and its ONE machine-checkable consequence is the `(2,2,3)` witness:
`k = 3, A = x` gives `γ = 1`, `q(3) = 1`, `twistRead = η^{−1} = 2η` in `F₉` over `ℤ₃` — the
`[r1]` `+q` reading predicts `η` and is refuted. That witness is a MANDATORY §13 gate
(GC-11; it is also a `q = 3` instance, so the two-prime rule is served by adding the
`(2,2,1)`-frame `q = 2` row where `q(k) = 0` — the coincidence regime C-H12 names — plus a
`q(k) ≠ 0` row at `q = 2`: the gate node picks `(e₁,f₁,h) = (2,2,3)` over `ℤ₂` … `i₀ = 1,
a₀ = −1` and `q(3) = 1` identically, since `q(k)` is `π`-independent arithmetic).

**DEPENDS.** C.15 · C.19 · C.21.

**PROOF.** definitional.

**SIZE.** 10 lines.

**SOURCE.** `EFF.HE6.15` (the `[r2]` sign correction + witness, verbatim); `EFF.HE6.58`
(the TERMINAL composed display); `EFF.HE6.13` (RIDER: the fixed `η^q` ratio).

**TEETH.** the `(2,2,3)` PE2-leg-B witness (`CXRES` realizes `2η`) → **executable
regression** (§13 gate C.124); the sign is additionally guarded by C.24's span law (a wrong
sign breaks the coset-form image characterization at every proper window).

**ENVIRONMENT.** ENV-C1.

---

### NODE C.23 [lemma] [fresh]

**STATEMENT.** *The slot lemma, value-and-residue half (LEMMA HE6-0″ recast).* Let `A ∈ O[X]`,
`deg A < D′`, and suppose `stageHeight F A = (k : ℕ∞)`. Then `slotRes F H₀ hpin k A ≠ 0`.
Moreover the window coefficients of `slotRes` are exactly the attaining-slot digits: the
`t`-th coefficient is nonzero iff slot `slotIdx k + e₁t` attains the minimum.

**SIGNATURE.**
```lean
namespace Uniformity.Density.Tower

theorem KeyFrame.slotRes_ne_zero (F : KeyFrame O π) (hπ : Irreducible π) (H₀ : ℕ)
    (hpin : _) {A : Polynomial O} {k : ℕ} (hA : A.natDegree < F.e₁ * F.f₁)
    (hht : F.stageHeight A = (k : ℕ∞)) :
    F.slotRes H₀ hpin k A ≠ 0
```

**DEPENDS.** C.02 · C.19 (power basis) · C.20 · C.21 · B.24 (`digAt_eq_zero_iff`) · H.53
(`eta_independent` — instantiated at `(resField X, stageField F)` through C.19's basis).

**PROOF.**
1. The minimum `k` is attained at some slot in class `slotIdx k` (C.20(ii)); at an attaining
   slot the digit read is nonzero (`digAt_eq_zero_iff`: `π^{m+1} ∤ a` exactly at exact
   valuation).
2. `slotRes` is a `K`-combination of `{η^t}_{t<f₁}` with the attaining coefficient nonzero;
   the power basis (C.19) — H.53's independence packaged — forces the sum ≠ 0.

**SIZE.** 20 lines.

**SOURCE.** `EFF.HE6.15` (LEMMA HE6-0″: exactness + nonvanishing, with the two hypothesis
roles verbatim); `EFF.HE6.58` (the corrected γ this instantiates).

**TEETH.** `HE6R1-T-BASIS` (`EFF.HE6R1.29`: at `γ₀ = −γ₁ ≠ 0` NO cancellation — "the machine
form of `{1, β}` is a K-basis") → **Lean theorem** (this node's step 2, at the C.12 iterate
level for β) + **executable regression** retained.

**ENVIRONMENT.** ENV-C3 (`hπ`; finiteness enters only through consumers — bind minimally:
ENV-C1 + `hπ` suffices; recorded as ENV-C1′).

---

### NODE C.24 [theorem] [fresh]

**STATEMENT.** *The corrected LIFT law (LEMMA HE6-1L, both directions, closure-free).* Fix
`k` and write `T := slotWindow F k`, `η := stageLetter`. Then the image of
`{A : deg A < D′ ∧ stageHeight F A = k}` under `slotRes F H₀ hpin k` is exactly
`{Σ_{t ∈ T} c_t η^t : c_t ∈ image of (resField X), not all 0}` — the braced span of
`EFF.HE6.13` (n(k)-read; the ϖ-read image is the `η^{−q(k)}`-coset, which for the fullness
clause is invisible: `η^{−q}·K^× = K^×`). Consequences, as separate clauses: (i) the image
is all of `K^×` iff `T = range f₁` iff `k ≥ (slotIdx k + e₁(f₁−1))h` (C.18); (ii) if
`T = ∅` the height is unattained (C.20(iii) restated on the image).

**SIGNATURE.**
```lean
namespace Uniformity.Density.Tower

theorem KeyFrame.slotRes_image (F : KeyFrame O π) (hπ : Irreducible π)
    [Finite (ResidueField O)] (H₀ : ℕ) (hpin : _) (k : ℕ) :
    (Set.image (F.slotRes H₀ hpin k)
        {A : Polynomial O | A.natDegree < F.e₁ * F.f₁ ∧ F.stageHeight A = (k : ℕ∞)})
      = {x | ∃ c : ℕ → ResidueField O, (∃ t ∈ F.slotWindow k, c t ≠ 0) ∧
          x = (F.slotWindow k).sum fun t => algebraMap _ _ (c t) * F.stageLetter H₀ hpin ^ t}
```

with clauses (i)/(ii) as companion corollaries in the same file (public name
`slotRes_image`; the fullness corollary `slotRes_surj_iff` is the one §6/§9 consume).

**DEPENDS.** C.15–C.21 · C.23 · **H.54 (`stageLift'`) · H.55 · H.56** (the constructive
direction — the same consumption pattern as C.14, `GenreDatum` plumbing included, μ-dummy
caveat carried) · B.24.

**PROOF.**
1. `⊆`: C.21's definition lands in the span; C.23 gives "not all 0".
2. `⊇`: given `(c_t)`, H.54's lift at height `k` with window data `c` produces `A` with the
   pinned height (H.55) and residue (H.56); at `D′ = 1` the elementary lift (C.14 step 3's
   mechanism).
3. (i): C.18's iff + the span being `K^×` exactly at a full window (power-basis counting,
   C.19); (ii): C.20(iii).

**SIZE.** 38 lines. **Split-mandated:** C.24 → 2 (image law / corollaries).

**SOURCE.** `EFF.HE6.13` (LEMMA HE6-1L, the corrected display verbatim, TERMINAL layer:
coset + span + fullness iff + emptiness; the `[r2]` record's witness); `EFF.HE6.12` (the
STRUCK `(LIFT)` — the sealed display is DEAD and this node is its corrected replacement; both
counter-instances re-audited there).

**TEETH.** `EFF.HE6.12`'s two counter-instances (`(1,2,1), k = 0`: only `F_Q ⊊ K` reached;
`(3,1,2), k = 1`: `T(1) = ∅`, unattained) → **Lean theorem** (they are instances of this
statement's `⊆` direction and (ii)); `EFF.HE6.13`'s `(2,2,3)` witness → §13 gate.

**ENVIRONMENT.** ENV-C3.

---

### NODE C.25 [def] [fresh]

**STATEMENT.** *The level residual polynomial `R_λ` (`EFF.HE6.11`'s display, ϖ-read,
GC-1-pinned).* For a frame `F` and `f ∈ O[X]` with side data `(u, ℓ)`, nonemptiness `hne₂`,
and a correct level pin `M₀` (`dvHgt F f (dvSideMin …) = (M₀ : ℕ∞)` — the `sideMin` pin,
GC-1): writing `j₁ := dvSideMin`, `d := dvSideDeg`,

```
dvResPoly F f u ℓ … : Polynomial (stageField F H₀ hpin) :=
  Σ_{t ≤ d} C (twistRead F H₀ hpin (M₀ − t·u) (dev F.key f (j₁ + t·ℓ))) · Z^t,
```

the `t`-th coefficient being the ϖ-read of the `(j₁ + tℓ)`-th development coefficient at its
on-side height `M₀ − tu` (junk `0` when the pin sits strictly above the side — `digAt`'s
junk-0 discipline makes the formula total, B.28's pattern).

**SIGNATURE.**
```lean
namespace Uniformity.Density.Tower

/-- `R_λ(Z) := Σ_t res(A_{j₁+tℓ}(θ)/ϖ(θ)^{m₁−tu})·Z^t ∈ K[Z]` (`EFF.HE6.11`), through the
C.22 ϖ-read at the GC-1 `sideMin` pin. -/
noncomputable def dvResPoly (F : KeyFrame O π) (H₀ : ℕ) (hpin : _)
    (f : Polynomial O) (u ℓ : ℕ) (hne₂ : (dvSideSet F f u ℓ).Nonempty) (M₀ : ℕ)
    (hpin₂ : dvHgt F f (dvSideMin F f u ℓ hne₂) = (M₀ : ℕ∞)) :
    Polynomial (F.stageField H₀ hpin) :=
  ((Finset.range (dvSideDeg F f u ℓ hne₂ + 1)).sum fun t =>
    Polynomial.C (F.twistRead H₀ hpin (M₀ - t * u) (dev F.key f (dvSideMin F f u ℓ hne₂ + t * ℓ)))
      * Polynomial.X ^ t)
```

**⚠ FAITHFULNESS.** `EFF.HE6.11`'s variable `Z` "is the class of `y^ℓ/ϖ^u`" — a
closure-side gloss carried as documentation only; the polynomial's IDENTITY as data is the
coefficient list above, and the semantic tie to factors is C.27 + §5's laws (never assumed
from the gloss). The height argument `M₀ − t·u`: on-side pins satisfy
`ℓ·(pin) + u·(abscissa) = const`, so the `t`-th pin height is `M₀ − tu` when ℓ ∣ … — the
same bookkeeping as B.28, with GC-1's warrant that this is the pin under which correctness
(C.26) is provable.

**DEPENDS.** C.06 · C.07 · C.22 · B.02 · B.28 (the level-1 template).

**PROOF.** definitional.

**SIZE.** 20 lines.

**SOURCE.** `EFF.HE6.11` (the `R_λ` display, verbatim — with the `[r1]` bracket's warning
that ϖ ∉ O[x], which is why the read is C.22's and not a literal quotient); `EFF.HE6.10`
(sides/lengths).

**TEETH.** signed non-applicable at the definition (C.26 carries the correctness teeth).

**ENVIRONMENT.** ENV-C1.

---

### NODE C.26 [lemma] [fresh]

**STATEMENT.** *`R_λ` has degree `d` and nonzero constant term (B.30 one level up).* With
C.25's data, `0 < ℓ`, `Nat.Coprime u ℓ`, `dvSupp F f u ℓ ≠ ⊤`: (i) the `t`-th coefficient is
`0` iff `¬ DvOnSide F f u ℓ (j₁ + ℓt)`; (ii) coefficients `0` and `d` are nonzero;
(iii) `natDegree = d` and `coeff 0 ≠ 0`.

**SIGNATURE.**
```lean
namespace Uniformity.Density.Tower

theorem dvResPoly_coeff_eq_zero_iff (F : KeyFrame O π) (hπ : Irreducible π) (H₀ : ℕ)
    (hpin : _) {f : Polynomial O} {u ℓ : ℕ} (hℓ : 0 < ℓ) (hcop : Nat.Coprime u ℓ)
    (hne₂ : (dvSideSet F f u ℓ).Nonempty) {M₀ : ℕ}
    (hpin₂ : dvHgt F f (dvSideMin F f u ℓ hne₂) = (M₀ : ℕ∞)) {t : ℕ}
    (ht : t ≤ dvSideDeg F f u ℓ hne₂) :
    (dvResPoly F H₀ hpin f u ℓ hne₂ M₀ hpin₂).coeff t = 0
      ↔ ¬ DvOnSide F f u ℓ (dvSideMin F f u ℓ hne₂ + ℓ * t)

theorem natDegree_dvResPoly (…same…) :
    (dvResPoly F H₀ hpin f u ℓ hne₂ M₀ hpin₂).natDegree = dvSideDeg F f u ℓ hne₂ ∧
    (dvResPoly F H₀ hpin f u ℓ hne₂ M₀ hpin₂).coeff 0 ≠ 0
```

**DEPENDS.** C.07 · C.08 · C.20 · C.22 · C.23 · C.25 · B.30 (the proof template).

**PROOF.**
1. On-side pin at `j₁ + ℓt` has height exactly `M₀ − tu` (C.08's spacing + the side's line
   equation); C.23 gives the nonzero read. Off-side pin sits strictly above; every window
   digit reads `0` (`digAt_eq_zero_iff` — strictly-above means every slot's digit index
   undershoots its valuation), so the coefficient is `0`; the twist factor is a unit and
   preserves (non)vanishing.
2. (ii): endpoints are on-side by definition of min'/max'; (iii) follows.

**SIZE.** 30 lines.

**SOURCE.** `EFF.HE6.11` (“So `R_λ` has degree `d` and `R_λ(0) ≠ 0`”); B.30 (the level-1
twin whose proof route is replayed at the `dv`-carrier).

**TEETH.** `W12-SHAPE`-family at level 1 is B.30's; the level-2 shape is guarded by the §13
frame audit (`R_λ = r²`, `r` quadratic, at the `EFF.HE6R1.18` frame → the `q = 2`/`q = 3`
gate instances).

**ENVIRONMENT.** ENV-C1′ (`hπ` explicit).

---

### NODE C.27 [theorem] [fresh]

**STATEMENT.** *(SLOT₂)-exactness in norm form — the value law consumers actually read.* Let
`L` be a level datum over `F`, `g ∈ O[X]` monic with `0 < deg g` carrying the label `L`
(§5's `HasLabel`, C.29 — forward reference resolved there; the two nodes land together), and
`C ∈ O[X]` with `deg C < L.keyDeg₂`. Then

```
(F.e₁ * L.ℓ) • addVal O (Algebra.norm O (AdjoinRoot.mk g C…)) = g.natDegree • dv2Hgt L C
```

— the cleared, closure-free form of "`dv₂(C(ξ)) = dv2Hgt L C` exactly at every root":
summed over the factor's roots via the norm, with `EFF.HE6R1.26`'s battery form
`v(Res(f,C)) = D″·dv₂(C)` as the `deg g = D″`, `e₁ℓ = 2` instance
(`8·dv₂/2 = 4·dv₂` ✓ its audit).

**SIGNATURE.**
```lean
namespace Uniformity.Density.Tower

theorem slot2_exact {F : KeyFrame O π} {H₀ hpin} (L : LevelDatum F H₀ hpin)
    (hπ : Irreducible π) [Finite (ResidueField O)]
    {g : Polynomial O} (hg : HasLabel L g) {C : Polynomial O}
    (hC : C.natDegree < L.keyDeg₂) (hC0 : dv2Hgt L C ≠ ⊤) :
    ∃ v : ℕ, dv2Hgt L C = (v : ℕ∞) ∧
      (F.e₁ * L.ℓ) * (addVal O (Algebra.norm O (AdjoinRoot.mk g C))).get! = g.natDegree * v
```

(the `addVal … .get!` packaging follows the landed `normValues` idiom; the stub stage fixes
the exact `ℕ∞`-plumbing against `leanfinal`'s `addVal` API.)

**PROOF (route, the section's hard node).**
1. Reduce to prime-power label blocks: `HasLabel` gives `g`'s level-1 purity and residual
   `r`-power; the two-dissection layer one level up (§5's C.33/C.34) splits any counterexample.
2. The `≥` direction: every root contribution is bounded below by the slot minimum — via the
   development of `C` and B.31's monic-division monotonicity transposed (C.11's recursion:
   `dv2Hgt` is an inf of slot values, each a `suppVal`-shape bounded by the norm additivity
   `gaussVal_mul`-pattern at the `dv`-carrier).
3. The `≤` direction (no cancellation): the attaining slot's residue is nonzero — C.23 at
   level 1 for the inner read, then the level-2 attaining term's residue nonzero by C.12's
   power basis (H.53's mechanism at `(stageField, level2Field)`); a strict drop in the norm
   valuation would force the level-2 residue sum to vanish, contradiction.
4. Assemble through `norm = ± resultant = product over the dissected factors` using landed
   `norm_adjoinRoot_root`-family and `typeOf_mul`-side multiplicativity (B.32-pattern at the
   `dv`-carrier).

**SIZE.** 55 lines as one node — **split-mandated: C.27 → 3** (≥ half; no-cancellation half;
assembly). This is the chapter's schedule-risk node alongside C.61; it sits at depth 3 of
the intra-chapter DAG and should be claimed early.

**DEPENDS.** C.09 · C.11 · C.12 · C.20 · C.23 · C.29 (`HasLabel`, §5) · C.33/C.34 (§5
dissections — for step 1) · H.53 · B.31/B.32 (templates) · landed `norm_adjoinRoot_root`,
`addVal` API.

**SOURCE.** `EFF.HE6R1.26` (P2: `v(Res(f,C)) = 4·dv₂(C)`, 1,512 checks, 0 violations, with
the methodological note that at `ℓ = 1` exactness comes ENTIRELY from `K₂`-independence —
which is why H.53 carries step 3 there); `EFF.HE6R1.29` (T-BASIS: the no-cancellation tooth);
`EFF.HE6.15` (the level-1 exactness mechanism being iterated).

**TEETH.** `HE6R1-SLOT2` (1,512 exactness identities) → **Lean theorem** (this node) +
**executable regression** retained; `HE6R1-T-BASIS` → step 3 (as at C.23).

**ENVIRONMENT.** ENV-C3.

---

### NODE C.28 [def+lemma] [fresh]

**STATEMENT.** *The level-2 normalizer cocycle.* Over a level datum `L` (side `(u, ℓ)`):
the **shift** `s L m := the unique 0 ≤ β < ℓ with β·u ≡ m (mod ℓ)` (the `Φ′`-exponent of the
canonical height-`m` level-2 monomial `ϖ^{(m−βu)/ℓ}Φ′^{β}`), and the **cocycle**
`c₁ L a b := (s L a + s L b − s L (a+b)) / ℓ`. Lemmas: (i) `s L a + s L b ≡ s L (a+b)
(mod ℓ)` and `ℓ * c₁ L a b = s L a + s L b − s L (a+b)` exactly, with `c₁ L a b ∈ {0, 1}`;
(ii) **twist-triviality at `ℓ = 1`**: `s ≡ 0` and `c₁ ≡ 0` — `EFF.HE6R1.06`'s
"`s(·) ≡ 0` at `ℓ = 1`" and the mechanism of tooth `HE6R1-T-TWIST0` ("the level-2 normalizer
cocycle degenerates at `ℓ = 1`, `n₂(k) = ϖ^k`"), as a theorem.

**SIGNATURE.**
```lean
namespace Uniformity.Density.Tower

noncomputable def LevelDatum.shift {F : KeyFrame O π} {H₀ hpin} (L : LevelDatum F H₀ hpin)
    (m : ℕ) : ℕ := …  -- the unique β < ℓ with β·u ≡ m (mod ℓ); C.15's pattern at (u, ℓ)

noncomputable def LevelDatum.cocycle {F : KeyFrame O π} {H₀ hpin} (L : LevelDatum F H₀ hpin)
    (a b : ℕ) : ℕ := (L.shift a + L.shift b - L.shift (a + b)) / L.ℓ

theorem LevelDatum.cocycle_mem {F : KeyFrame O π} {H₀ hpin} (L : LevelDatum F H₀ hpin)
    (a b : ℕ) : L.ℓ * L.cocycle a b = L.shift a + L.shift b - L.shift (a + b)
      ∧ L.cocycle a b ≤ 1

theorem LevelDatum.cocycle_eq_zero_of_ell_one {F : KeyFrame O π} {H₀ hpin}
    (L : LevelDatum F H₀ hpin) (hℓ : L.ℓ = 1) (a b : ℕ) :
    L.shift a = 0 ∧ L.cocycle a b = 0
```

**⚠ FAITHFULNESS + PLACEHOLDER.** The corpus's `s(·)`/`c₁` live in HE7's level-2 frame
(`ANNEX-LEMMA R1-a`(iii)/(iv) — chapter E's). This node defines the arithmetic normal form
(the display `c₁(a,b) = (s(a)+s(b)−s(a+b))/ℓ` is quoted verbatim at `EFF.HE6R1.35`) and
proves its arithmetic; the RESIDUE-transport law (the cocycle unit's residue is `β^{c₁}`,
R1-a(iii)) is §5's scalar node C.39, which carries the placeholder
`EFF.HE7.<nn> — ANNEX-LEMMA R1-a(iii)/(iv) [supplied-by: chapter E]` (GC-13). The orchestrator
reconciles E's transcription with this arithmetic normal form at freeze; a mismatch is a
stop-the-line finding, not a silent adjustment.

**DEPENDS.** C.09 · C.15/C.16 (the pattern; `s` is `slotIdx` at the pair `(u, ℓ)` with the
roles of `h, e₁` played by `u, ℓ`).

**PROOF.** (i): the two shifts' sum is a representative of `a + b`'s class; subtracting the
reduced representative leaves a multiple of `ℓ` in `{0, ℓ}` since both `s`-values are `< ℓ`
— `omega` after C.16's spec. (ii): everything is mod 1.

**SIZE.** 26 lines.

**SOURCE.** `EFF.HE6R1.35` (PE2 F-2: the cocycle display, verbatim); `EFF.HE6R1.39` (PE3
F-1: the pin-height argument — consumed at C.39, recorded here so the TERMINAL form is not
lost); `EFF.HE6R1.06` (`s(·) ≡ 0` at `ℓ = 1`); `EFF.HE6R1.29` (T-TWIST0, the 1,276-exponent
tooth).

**TEETH.** `HE6R1-T-TWIST0` (1,276 level-2 twist exponents all zero at `ℓ = 1`) →
**Lean theorem** (clause (ii)) + **executable regression** retained; the contrastive half
(HE7-T-BADTWIST: dropping the twist at `ℓ ≥ 2` mispredicts σ on 21 reads) stays with
chapter E's battery inheritance (GC-8).

**ENVIRONMENT.** ENV-C5.

---

---

## 5. §5 — THE DESCENT GRAMMAR: THE WIDENED BOX, THE JUMP, THE PEEL, THE PROJECTION

> **Design note (what is proved vs what is carried).** This section transcribes the descent
> grammar at its TERMINAL forms (C-H8): the per-factor trichotomy behind COROLLARY HE6.B
> `[r1]` (C.30), the jump floors and the one-step multiplicity drop (C.31), the THREE-CLAUSE
> jump bound of the owner-directive re-display `EFF.HE6R1.47` (C.32 — the frozen
> `J ≤ log₂n − 2` unconditional display is DEAD), the two dissections one level up
> (C.33/C.34 — the section's heavy nodes), and LEMMA HE6R1-2/-3 (C.36–C.40). The standing
> hypotheses `disc f ≠ 0` and `Φ′ ∤ f` (`HE6-PEEL-CONVENTION`, `EFF.HE6.09` — T2's
> 32-consumption pin) enter as `Squarefree f` plus `¬ F.key ∣ f`; the `disc`-to-`Squarefree`
> recast is a GC-9-class divergence, flagged per node. **`HE6-BOX-1` is a NON-NODE**
> (C-H13): its widened closure is exactly C.30 + §7 + chapter E's branch — an agent
> "needing the box" consumes those.

### NODE C.29 [def] [fresh]

**STATEMENT.** *Level purity and the label predicate.* `IsDvPure F g u ℓ : Prop` — `g`'s
level polygon is one-sided of slope `u/ℓ`: both extreme abscissae `0` and
`g.natDegree / D′` lie in `dvSideSet F g u ℓ` (B.34's shape at the `dv`-carrier). And
`HasLabel L g : Prop` — `g` is monic, `0 < deg g`, `IsDvPure F g L.u L.ℓ`, and `g`'s level
residual is an `r`-power: `∃ m, 0 < m ∧ dvResPoly F H₀ hpin g L.u L.ℓ … = L.r ^ m` (the
closure-free form of "every root of `g` is a level-2 point with level-1 label `(λ, r)`").

**SIGNATURE.**
```lean
namespace Uniformity.Density.Tower

def IsDvPure (F : KeyFrame O π) (g : Polynomial O) (u ℓ : ℕ) : Prop :=
  0 ∈ dvSideSet F g u ℓ ∧ g.natDegree / (F.e₁ * F.f₁) ∈ dvSideSet F g u ℓ

def HasLabel {F : KeyFrame O π} {H₀ hpin} (L : LevelDatum F H₀ hpin)
    (g : Polynomial O) : Prop :=
  g.Monic ∧ 0 < g.natDegree ∧ IsDvPure F g L.u L.ℓ ∧
  ∃ (hne₂ : (dvSideSet F g L.u L.ℓ).Nonempty) (M₀ : ℕ)
    (hpin₂ : dvHgt F g (dvSideMin F g L.u L.ℓ hne₂) = (M₀ : ℕ∞)) (m : ℕ),
    0 < m ∧ dvResPoly F H₀ hpin g L.u L.ℓ hne₂ M₀ hpin₂ = L.r ^ m
```

**⚠ FAITHFULNESS.** The corpus's `S_{λ,r}` is a set of roots in `K̄₀`; `HasLabel` is the
factor-level surrogate (DECISION C-D1's recast). The tie "every root of a `HasLabel` factor
is a `(λ, r)`-point" is not stated (no points exist); what downstream consumes is exactly
this predicate plus C.27/C.37's value laws.

**DEPENDS.** C.06 · C.07 · C.09 · C.25 · B.34 (shape template).

**PROOF.** definitional. **SIZE.** 20 lines.

**SOURCE.** `EFF.HE6.10` (sides/labels); `EFF.HE6R1.13` (“let `(λ, r)` be a level-1 label of
`f`, `S = S_{λ,r}`, `f_S` the block factor”); DECISION C-D1.

**TEETH.** signed non-applicable. **ENVIRONMENT.** ENV-C1.

---

### NODE C.30 [lemma] [fresh]

**STATEMENT.** *The descent trichotomy (COROLLARY HE6.B `[r1]`'s case split, re-derived from
the proof's own display).* For a side `(u, ℓ)` (`0 < ℓ`, coprime) and a monic irreducible
factor `r` of the side residual with multiplicity `m_r ≥ 1` and `d_r := deg r ≥ 1`, exactly
one of:
(a) `m_r = 1` — the separable-at-`r` case (decided by the §7 layer);
(b) `m_r ≥ 2 ∧ ℓ = 1 ∧ d_r = 1` — repeated `K`-rational linear at an integer slope (the
α-refine case: descent stays at the current level — chapter B's order-1 recentering at the
degenerate frame, `EFF.HE6.19`'s "HE3 stage-α" branch);
(c) `m_r ≥ 2 ∧ 2 ≤ ℓ * d_r` — the **level jump** (LEMMA HE6R1-1's widened condition:
"a node requires a level jump exactly when its side carries a repeated irreducible residual
factor with `ℓ_i·deg r_i ≥ 2`").
The three cases are pairwise disjoint and exhaustive, decidably in `(m_r, ℓ, d_r)`.

**SIGNATURE.**
```lean
namespace Uniformity.Density.Tower

theorem descent_trichotomy (mr ℓ dr : ℕ) (hm : 1 ≤ mr) (hℓ : 0 < ℓ) (hd : 1 ≤ dr) :
    (mr = 1 ∧ ¬(mr ≥ 2 ∧ ℓ = 1 ∧ dr = 1) ∧ ¬(mr ≥ 2 ∧ 2 ≤ ℓ * dr)) ∨
    (mr ≥ 2 ∧ ℓ = 1 ∧ dr = 1 ∧ ¬(2 ≤ ℓ * dr) ∧ mr ≠ 1) ∨
    (mr ≥ 2 ∧ 2 ≤ ℓ * dr ∧ ¬(ℓ = 1 ∧ dr = 1) ∧ mr ≠ 1)
```

(the formalizer may package the three cells as an `inductive` case tag — GC-4 allows
inductive DOMAIN types; the σ carrier is unaffected.)

**DEPENDS.** none (arithmetic).

**PROOF.** `ℓ = 1 ∧ dr = 1 ↔ ℓ*dr = 1 ↔ ¬(2 ≤ ℓ*dr)` given positivity; `omega`.

**SIZE.** 12 lines.

**SOURCE.** `EFF.HE6R1.10` (the proof's own three-way split, verbatim: “HE6.A decides a
separable residual at every ℓ; HE3's stage-α decides a repeated K-rational linear factor at
an integer slope; the complement is exactly a repeated irreducible `r` with `ℓ·deg r ≥ 2`”);
`EFF.HE6.19` (COROLLARY HE6.B `[r1]`, the honest scope + "the excluded set is now EXACTLY
the complement of the union of the two surviving node hypotheses"); `EFF.HE6R1.05` (the §S2
four-case enumeration — the four cells `(ℓ ≥ 2?) × (d ≥ 2?)` of case (c)∪(b) refine this
trichotomy; per GC-10's re-derive rule the PROOF-consumed split is the one transcribed).

**TEETH.** `HE6-T-CASEB` + `HE6R1-T-CRACK` (both branches of (c) machine-certified genuinely
undecided by outer data — three distinct PARI σ on identical outer data) → **executable
regressions** retained; they guard the NECESSITY of the case split, which no Lean theorem
states (a Lean theorem cannot say "no outer-data-only argument decides this").

**ENVIRONMENT.** ENV-C5.

---

### NODE C.31 [lemma] [fresh]

**STATEMENT.** *Jump floors and the one-step multiplicity drop.* (i) In case (c) the side
length obeys `L_λ ≥ m_r·ℓ·d_r ≥ 4` (floor: `m_r ≥ 2`, `ℓd_r ≥ 2`). (ii) `L_λ ≤ μ` (side
lengths bound the polygon's abscissa range), so `μ ≥ 4`. (iii) At a composite frame
(`2 ≤ D′`): `n = D′μ ≥ 8` — the first-bite bound, and depth-3 first bites at `n ≥ 16`
(iterating: a second jump needs `μ₂ ≥ 4`, so `μ ≥ 8`, `n ≥ 16`). (iv) **The drop:** at a
jump on `(u, ℓ)` with residual `R` of degree `d_R` and block `f_S`,
`μ₂ = deg f_S / D″ ≤ deg R / d_r ≤ μ / (ℓ·d_r) ≤ μ/2` — `EFF.HE6R1.10`'s audited chain
(`n_λ = D′L_λ`, `(SEP)`-free, enters as `deg f_S ≤ D′·L_λ` from C.33's dissection).

**SIGNATURE.**
```lean
namespace Uniformity.Density.Tower

theorem jump_floor (mr ℓ dr L μ : ℕ) (hm : 2 ≤ mr) (hjump : 2 ≤ ℓ * dr)
    (hL : mr * (ℓ * dr) ≤ L) (hLμ : L ≤ μ) : 4 ≤ L ∧ 4 ≤ μ

theorem first_bite (D μ n : ℕ) (hD : 2 ≤ D) (hμ : 4 ≤ μ) (hn : n = D * μ) : 8 ≤ n

theorem jump_drop (D ℓ dr μ μ₂ dfS : ℕ) (hD : 0 < D) (hℓ : 0 < ℓ) (hd : 0 < dr)
    (hμ₂ : μ₂ * (D * ℓ * dr) = dfS) (hfS : dfS ≤ D * (ℓ * (μ / ℓ)))  -- deg f_S ≤ D′L_λ, L_λ ≤ μ
    (hL : ℓ * dr * 2 ≤ 2 * μ) : 2 * μ₂ ≤ μ
```

(the exact hypothesis plumbing of `jump_drop` is fixed at stub stage against C.33/C.35's
outputs; the SPEC is the chain `μ₂ ≤ deg R_λ/d_r ≤ μ/(ℓd_r)` with every step ℕ-cleared.)

**DEPENDS.** C.30 · C.33/C.35 (suppliers of `deg f_S ≤ D′L_λ` and `L_λ ≤ μ` — forward
within-section refs, fired after them).

**PROOF.** 1. (i)/(ii)/(iii): `Nat.mul_le_mul` + `omega` (H.03's pattern; the depth-3 clause
iterates (iv) once). 2. (iv): divide the audited chain
`μ₂·D″ = deg f_S ≤ D′L_λ = D′ℓd_R` and `d_R·… ≤ μ`-clearing; `omega`/`Nat.div` lemmas.

**SIZE.** 22 lines.

**SOURCE.** `EFF.HE6R1.09`/.10 (the displays + the compile-time audit “`L_λ = ℓ·deg R_λ ≥
ℓ·m·d_r = m(ℓd_r) ≥ 4` ✓ … `μ₂ = deg f_S/D″ ≤ … ≤ μ/(ℓd_r)` ✓ every step exact”);
`EFF.HE6.19`'s first-bite audit (`n = D′μ ≥ 2·4 = 8`); `EFF.HE6.20` items 1–2.

**TEETH.** `EFF.HE6.20`'s bite-frame numbers (`n = 8, μ = 4, D′ = 2, ℓ = 2, d = 2`, polygon
`(0,2u)–(4,0)`) → **Lean theorem** instances + §13 regression.

**ENVIRONMENT.** ENV-C5.

---

### NODE C.32 [theorem] [fresh]

**STATEMENT.** *The jump-count bound — the THREE-CLAUSE re-display, `ℕ`-cleared (TERMINAL;
the frozen unconditional `J ≤ log₂n − 2` is withdrawn at ambient roots and DEAD).* Let
`a : Fin J → ℕ` be the multiplicities at the successive jumps of a history (`a 0 ≤ μ`,
`4 ≤ a j` for every jump, `2 * a (j+1) ≤ a j`). Then:
(a) **any history:** `2 ^ (J + 1) ≤ 2 * μ` — the cleared form of `J ≤ log₂ μ − 1`
(read: `4·2^{J−1} ≤ μ`);
(b) **composite-stage-rooted** (`2 ≤ D′`, `n = D′·μ`): `2 ^ (J + 2) ≤ n` — the cleared
`J ≤ log₂ n − 2`, THE bound every consumption site cites (stage-rooted, unchanged by the
re-display);
(c) **ambient-rooted** (`D′ = 1`, `n = μ`): `2 ^ (J + 1) ≤ n` — the cleared
`J ≤ log₂ n − 1`, **and this is sharp**: `J = 1, n = 4` satisfies every hypothesis with
equality (the R7/A4 quartic witness `m = 2, ℓ = 1, d_r = 2`, side length `4 = μ = n`), while
clause (b)'s bound would read `8 ≤ 4`, false — the frozen display's refutation, landed as
arithmetic.

**SIGNATURE.**
```lean
namespace Uniformity.Density.Tower

theorem jump_count_bound {J μ : ℕ} (a : Fin (J + 1) → ℕ) (ha0 : a 0 ≤ μ)
    (hfloor : ∀ j, 4 ≤ a j) (hdrop : ∀ j : Fin J, 2 * a j.succ ≤ a j.castSucc) :
    2 ^ (J + 2) ≤ 2 * μ
-- (a) with J+1 jumps ⇒ 2^{(J+1)+1} ≤ 2μ; the (b)/(c) corollaries and the sharpness
-- example land as companions `jump_count_stage`, `jump_count_ambient`,
-- `jump_count_ambient_sharp` in the same file.
```

**DEPENDS.** C.31 (whose (iv) instantiates `hdrop` for real histories).

**PROOF.**
1. Downward induction: `a J ≥ 4` and each step doubles — `4 * 2^J ≤ a 0·…` via
   `Nat.pow_le` induction; `≤ μ` closes (a).
2. (b): `μ ≤ n / D′ ≤ n / 2` cleared: `2μ ≤ n`, chain with (a).
3. (c): substitute `n = μ`. Sharpness: `decide`-grade instance `J = 1, a = ![4, …]`-check
   plus the counter-evaluation `2^3 = 8 > 4` against (b)'s conclusion — the A4
   counterexample's arithmetic, exactly (`EFF.HE6R1.43`'s audit: “`J ≤ log₂4 − 2 = 0` is
   contradicted by `J = 1`”).

**SIZE.** 30 lines.

**SOURCE.** `EFF.HE6R1.47` (the owner-directive re-display, all three clauses verbatim,
with its consumer sweep: “THEOREM HE7.C's bounds are stage-rooted (clause (b)) and
unchanged”); `EFF.HE6R1.43` (the obstruction record + exact counterexample); `EFF.HE6R1.09`
(the superseded display — carried as DEAD, per C-H8); `EFF.HE6R1.11` (the structural
punchline: both widened-box branches supply the descent factor `ℓd_r ≥ 2`, unaffected by
the re-display).

**TEETH.** the A4 counterexample → **Lean theorem** (the sharpness companion); the `n = 8`
one-jump/`n = 16` two-jump consumption values (`EFF.HE6R1.17`(i)) → **Lean theorem**
instances of (b).

**ENVIRONMENT.** ENV-C5.

---

### NODE C.33 [theorem] [fresh]

**STATEMENT.** *The slope dissection at the level polygon (B.41/B.42 one level up).* Over
the complete bundle (`[IsAdicComplete …]`), let `f` be monic with `F.key ∤ f`,
`Squarefree f` NOT required here, and let the level polygon of `f` have side slopes
`λ₁ = u₁/ℓ₁ > … > λ_s` above the frame's floor (`u_i > ℓ_i·D′·F.h`). Then `f` factors as
`f = f₀ · ∏_i f_i` with each `f_i` monic, `IsDvPure F f_i u_i ℓ_i`, the `Φ′`-degree of `f_i`
equal to the side's length `L_{λ_i}` (so `deg f_i = D′·L_{λ_i}` — the `(SEP)`-free
`n_λ = D′L_λ` of LEMMA HE6-3(b), consumed by C.31), and `f₀` the below-floor remainder
(the part whose development sits at or below the frame floor — order-1 territory, chapter
B's); the factorization is unique among monic dissections.

**SIGNATURE** (shape; the stub fixes the side-indexing plumbing).
```lean
namespace Uniformity.Density.Tower

theorem exists_dv_slope_dissection (F : KeyFrame O π) (hπ : Irreducible π)
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    {f : Polynomial O} (hf : f.Monic) (hkey : ¬ F.key ∣ f) … :
    ∃ …, f = … ∧ (∀ i, IsDvPure F (f_i) (u_i) (ℓ_i)) ∧
      (∀ i, (f_i).natDegree = (F.e₁ * F.f₁) * ℓ_i * dvSideDeg F f (u_i) (ℓ_i) _) ∧ …
```

**⚠ HEAVY NODE — split-mandated: C.33 → 3** (graded solve at the `dv`-filtration; the limit
through completeness; uniqueness). The proof is B.41/B.42's route re-run at the
`dv`-graded structure — the graded pieces are `(stageHeight ≥ k)`-filtered `O[x]_{<D′}`
modules instead of `π`-adic ones; the Hensel engine (`exists_solve_*`,
`isCoprime_of_map_eq`, `exists_adicLimit_of_degree_lt`) is consumed as landed.

**DEPENDS.** C.01 · C.06 · C.07 · C.08 · C.20 · C.23 · C.26 · C.29 · B.41/B.42 (route
templates — NOT consumable directly: they require `IsKey φ`, false for `F.key` at `h ≥ 1`) ·
landed Hensel engine.

**PROOF (route).**
1. Two-piece split at the top slope: the `dv`-graded coprimality of the slope-`λ₁` part
   against the rest (C.26's residual nonvanishing at the seam gives the unit leading datum);
   B.42's induction shape.
2. Newton/Hensel iteration in the `dv`-filtration; degree bookkeeping through C.08's length
   law gives `deg f_i = D′L_{λ_i}`.
3. Uniqueness via `monic_factorization_unique` + purity separation (distinct slopes ⟹
   coprime reductions in the graded ring — C.20's class separation).

**SIZE.** 3 × ~45 lines.

**SOURCE.** `EFF.HE6.10` (the polygon this dissects); `EFF.HE6R1.10` (the consumed
`n_λ = D′L_λ` — LEMMA HE6-3(b), “(SEP)-free”, entering as this node's degree clause);
`docs/GMN_citations.md` Thm 1.15 scope note (the level-1 twin's warrant, B §6's D-2).

**TEETH.** the §13 frame audit (the `EFF.HE6R1.18` battery frame's single side `λ ∈ {3,5}`,
`deg f_S = 8`) → **executable regression**; `HE6-T-BADKEY` guards `hcop` (via C.09).

**ENVIRONMENT.** ENV-C2 (`hπ` explicit; NO residue-field finiteness — GC-6.4).

---

### NODE C.34 [theorem] [fresh]

**STATEMENT.** *The residual dissection at the level polygon (B.48 one level up).* With
C.33's context and a pure factor `g` (`IsDvPure F g u ℓ`, side residual
`R := dvResPoly F … g u ℓ …`): for every factorization `R = ∏_k ρ_k^{m_k}` into pairwise
coprime prime powers over the stage field, `g` factors as `g = ∏_k g_k` with `g_k` monic,
`IsDvPure F g_k u ℓ`, and `dvResPoly` of `g_k` equal to `ρ_k^{m_k}` (up to the C.39-class
unit scalar — the `K^×`-scale consumers are invariant under); unique among monic
refinements. In particular for `L` a level datum with `L.r ∣ R`: the **`(λ, r)`-block
factorization** `g = f_S · g'` with `HasLabel L f_S` (multiplicity `m_r`) and
`¬ L.r ∣ dvResPoly … g' …`.

**SIGNATURE** (shape).
```lean
namespace Uniformity.Density.Tower

theorem exists_dv_residual_dissection (F : KeyFrame O π) (hπ : Irreducible π)
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O] {H₀ hpin}
    {g : Polynomial O} (hg : g.Monic) {u ℓ : ℕ} (hpure : IsDvPure F g u ℓ) … :
    ∃ fS g', g = fS * g' ∧ HasLabel (L) fS ∧ … ∧ ¬ L.r ∣ dvResPoly F H₀ hpin g' u ℓ … …
```

**⚠ HEAVY NODE — split-mandated: C.34 → 2** (the coprime-residual Hensel split; the
block-factor packaging). Route: B.48's graded-coprime lift (`GradedCoprime`,
`exists_graded_solve`-pattern) at the `dv`-carrier, with C.26 supplying degree/constant-term
control and the multiplicativity of `dvResPoly` on pure products (the B.35-analogue enters
as a private helper here or a RE-PLAN node if reusable — ⚠ the orchestrator should expect
that RE-PLAN: `dvResPoly_mul_of_pure`, the level-2 twin of B.35, is needed by C.37 too).

**DEPENDS.** C.25 · C.26 · C.29 · C.33 · B.44–B.48 (route templates) · landed Hensel engine.

**PROOF (route).** B.48's steps at the `dv`-graded ring: lift the coprime residual
factorization through the graded Hensel solve; purity of the factors from the two-line
squeeze (B.57's step-1 pattern at the `dv`-carrier); uniqueness from
`monic_factorization_unique` + residual coprimality.

**SIZE.** 2 × ~45 lines.

**SOURCE.** `EFF.HE6R1.13` (the block factor `f_S` — cited there to `LEMMA HE7-6
[supplied-by: chapter E]`; per GC-13 this node is chapter C's own supply of the
tower-geometric content, and the orchestrator reconciles E's HE7-6 transcription with this
node at freeze — one of the two becomes the citing party, never both proving);
`EFF.HE6.20` item 1 (single-label sides need no dissection — the `R = r^m` case is
`fS = g`).

**TEETH.** `EFF.HE6R1.25`'s census (the block = everything at `R_λ = r²`, `μ₂ = 2`) →
§13 regression.

**ENVIRONMENT.** ENV-C2.

---

### NODE C.35 [def] [fresh]

**STATEMENT.** *The block factor and `μ₂`.* Via C.34's uniqueness: `blockFactor L f`
(defined under C.33/C.34's hypotheses by choice from the unique dissection) — the monic
`f_S` with `HasLabel L f_S` in the `(λ, r)`-block factorization of `f`'s slope-`λ` part —
and `mult₂ L f := (blockFactor L f).natDegree / L.keyDeg₂` (the corpus's
`μ₂ := deg f_S / D″`, `EFF.HE6R1.12`). Companion: `(blockFactor L f).natDegree =
L.keyDeg₂ * mult₂ L f` exactly (the division is exact — C.34's degree bookkeeping).

**SIGNATURE.**
```lean
namespace Uniformity.Density.Tower

noncomputable def blockFactor {F : KeyFrame O π} {H₀ hpin} (L : LevelDatum F H₀ hpin)
    (f : Polynomial O) (h : …C.33/C.34 context…) : Polynomial O := …

noncomputable def mult₂ {F : KeyFrame O π} {H₀ hpin} (L : LevelDatum F H₀ hpin)
    (f : Polynomial O) (h : …) : ℕ := (blockFactor L f h).natDegree / L.keyDeg₂
```

**DEPENDS.** C.09 · C.33 · C.34.

**PROOF.** definitional (choice from C.34's unique existence). **SIZE.** 14 lines.

**SOURCE.** `EFF.HE6R1.12` (“THEOREM HE7.A is stated about the block factor `f_S` and puts
`μ₂ := deg f_S/D″`”); `EFF.HE6R1.18` (`μ₂ = 8/4 = 2` audit).

**TEETH.** the `μ₂ = 2` frame value → §13 regression. **ENVIRONMENT.** ENV-C2.

---

### NODE C.36 [lemma] [fresh]

**STATEMENT.** *Block projection, clause (a) (LEMMA HE6R1-2(a), `[r1′]`-hypothesis form).*
Let `f` be monic, `Squarefree f`, `¬ F.key ∣ f` (the PEEL-CONVENTION pair), `L` a level
datum with block `f_S := blockFactor L f` and complement `g := f / f_S`, and let `Ψ` be a
test key (`IsTestKey L Ψ`) with **`¬ Ψ ∣ f_S`**. Then: (i) the `[r1′]` equivalence
`Ψ ∣ f_S ↔ Ψ ∣ f` (so the hypothesis may be checked on `f`); (ii) `L.r` does not divide
`g`'s side residual (`¬ L.r ∣ dvResPoly F … g L.u L.ℓ …` — C.34's complement clause,
restated); (iii) consequently the **complement constant**
`c_g := (the ℕ-value of) L.ℓ • dvSupp F g L.u L.ℓ`… is finite and well-defined — the
closure-free `c_g` ("for every level-2 point `ξ`, `dv₂(g(ξ)) = ℓ·h_{F_g}(λ)`, a constant
depending on `(g, λ)` only").

**SIGNATURE.**
```lean
namespace Uniformity.Density.Tower

theorem block_complement_notdvd {F : KeyFrame O π} {H₀ hpin} (L : LevelDatum F H₀ hpin)
    (hπ : Irreducible π) [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    {f : Polynomial O} (hf : f.Monic) (hsq : Squarefree f) (hkey : ¬ F.key ∣ f) (hctx : …) :
    (∀ Ψ, IsTestKey L Ψ → (Ψ ∣ blockFactor L f hctx ↔ Ψ ∣ f)) ∧
    ¬ L.r ∣ dvResPoly F H₀ hpin (f /ₘ blockFactor L f hctx) L.u L.ℓ … …
```

with `complementConst` (the `c_g` value) as a companion `def` in the same file (RE-PLAN if
another section needs it by name — expected: C.37, C.39, §7).

**DEPENDS.** C.13 · C.29 · C.34 · C.35 · B.31 (division monotonicity).

**PROOF.**
1. (i) `⟸` needs: a `Ψ`-divisor of `f` divides `f_S`. Closure-free route: `Ψ` is monic with
   `HasLabel`-grade slot data (C.13); any common divisor bookkeeping runs through C.34's
   uniqueness — `gcd(Ψ, f)`'s residual is an `r`-power (Ψ's is), so the gcd sits inside the
   `(λ,r)`-block by the dissection's uniqueness; squarefreeness transfers divisibility.
   (The corpus's root-set argument `EFF.HE6R1.13`'s bracket is replaced by this
   factor-level argument — FAITHFULNESS-flagged, §16.)
2. (ii) is C.34's clause.
3. (iii): finiteness of `dvSupp F g L.u L.ℓ` from `g ≠ 0`; the constancy claim is
   definitional in the recast (the constant IS the support value; the corpus's "for every
   point" content is carried by C.27's exactness at label factors).

**SIZE.** 34 lines.

**SOURCE.** `EFF.HE6R1.13` (LEMMA HE6R1-2 with the `[r1′]` insertion + its equivalence
argument, verbatim; clause (a)); `EFF.HE6.09` (the standing-hypothesis pair).

**TEETH.** the 12-member `Ψ ∣ f_S` stratum (`EFF.HE6R1.14`: BADTOTAL diagnosis) →
**executable regression** retained (the §13 gate re-fires one degenerate member and checks
the (i)-equivalence detects it).

**ENVIRONMENT.** ENV-C2.

---

### NODE C.37 [theorem] [fresh]

**STATEMENT.** *Block projection, clause (b): THE TRANSLATION IDENTITY (the GC-2 mechanism
node).* With C.36's context (in particular `¬ Ψ ∣ f_S`), for every level-2 side `(u₂, ℓ₂)`
above the seam (`u₂ > ℓ₂ * L.seam`):

```
dv2Supp L Ψ f u₂ ℓ₂ = dv2Supp L Ψ f_S u₂ ℓ₂ + ℓ₂ • (c_g : ℕ∞)
```

— `EFF.HE6R1.13`(b)'s `h_{F₂,f}(κ₂) = h_{F₂,f_S}(κ₂) + c_g`, cleared by `ℓ₂`. Consequently
the above-seam level-2 polygon of `f` is that of `f_S` translated by `c_g`: same argmin
sets shifted, same slopes, same lengths — so `mult₂` and the §7 count are computable from
`f` without exhibiting `f_S` (the consequence itself is packaged at C.64).

**SIGNATURE.**
```lean
namespace Uniformity.Density.Tower

theorem dv2Supp_translation {F : KeyFrame O π} {H₀ hpin} (L : LevelDatum F H₀ hpin)
    (hπ : Irreducible π) [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    {f Ψ : Polynomial O} (hΨ : IsTestKey L Ψ) (hctx : …C.36's context…)
    {u₂ ℓ₂ : ℕ} (hℓ₂ : 0 < ℓ₂) (hseam : ℓ₂ * L.seam < u₂) :
    dv2Supp L Ψ f u₂ ℓ₂
      = dv2Supp L Ψ (blockFactor L f …) u₂ ℓ₂ + ℓ₂ • (complementConst L f … : ℕ∞)
```

**DEPENDS.** C.11 · C.13 · C.27 (`slot2_exact` — the value transport) · C.35 · C.36 · the
`dvResPoly_mul_of_pure` RE-PLAN helper (C.34's ⚠) · B.32 (additivity template).

**PROOF (route).**
1. `f = f_S·g` gives the Ψ-development of `f` as the product's; the level-2 pin of the
   product at index `j` decomposes through the development-of-product bookkeeping
   (B.32/B.33's shape at the `dv2`-carrier).
2. Above the seam, `g`'s contribution to every pin is EXACTLY `c_g` (no interaction): the
   attaining slot of `g` sits at the side value (C.36(ii)–(iii): `r ∤ R^{(g)}` kills
   cancellation at the seam residue — C.23's mechanism at the `(stageField, level2Field)`
   pair), so each pin translates by `c_g`.
3. Infima translate; argmin sets are preserved under constant shifts.

**SIZE.** 44 lines. **Split candidate** (step 2's no-interaction lemma may become C.37a —
the orchestrator books it if the stub run finds the file over the contract bound).

**SOURCE.** `EFF.HE6R1.13`(b) (verbatim, including “same breakpoints, same slopes λ₂, same
lengths `L_{λ₂}`”); GC-2 (this identity is the czar's named ℕ∞-mechanism: *"the translation
identity `EFF.HE6R1.13`(b) with `c_g` is the mechanism"*).

**TEETH.** `HE6R1`'s P2/P4 legs (252 flat identities; the 1,512 exactness identities feed
step 2 via C.27) → **executable regression** retained; §13 re-fires the frame instance.

**ENVIRONMENT.** ENV-C2.

---

### NODE C.38 [lemma] [fresh]

**STATEMENT.** *Block projection, clause (c): same radical at every above-seam side.* With
C.37's context, at every level-2 side `(u₂, ℓ₂)` above the seam: the level-2 residuals of
`f` and `f_S` (the `dv2`-analogue of C.25, built from `twistRead`-reads of the
Ψ-development at the side — `dv2ResPoly`, a companion `def` in this file, RE-PLAN if §7/§9
need it by name: they do — book it) have the same degree `L_{λ₂}/ℓ₂` and the same monic
irreducible factors (same radical); in particular one is separable iff the other is.

**SIGNATURE.**
```lean
namespace Uniformity.Density.Tower

theorem dv2ResPoly_radical_eq {F : KeyFrame O π} {H₀ hpin} (L : LevelDatum F H₀ hpin)
    (hπ : Irreducible π) [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    (hctx : …C.37's context…) {u₂ ℓ₂ : ℕ} (hseam : ℓ₂ * L.seam < u₂) … :
    (dv2ResPoly L Ψ f u₂ ℓ₂ …).radical = (dv2ResPoly L Ψ (blockFactor L f …) u₂ ℓ₂ …).radical
    ∧ (dv2ResPoly L Ψ f u₂ ℓ₂ …).natDegree = (dv2ResPoly L Ψ (blockFactor L f …) u₂ ℓ₂ …).natDegree
```

**DEPENDS.** C.25 (template) · C.37 · C.39 (the scalar — the radical equality is scalar-
invariance + C.37's translation; fired together).

**PROOF.** C.37 shifts every read height by `c_g`; the residual coefficients of `f` at the
shifted heights are the `f_S`-coefficients times the C.39 scalar (a fixed `K₂^×` unit per
side); a unit scalar preserves degree, radical, separability.

**SIZE.** 20 lines.

**SOURCE.** `EFF.HE6R1.13`(c) (verbatim through the truncation: “same degree `L_{λ₂}/ℓ₂` and
the same monic irreducible factors (same radical); in particular one is separable iff the
other is”).

**TEETH.** as C.37's. **ENVIRONMENT.** ENV-C2.

---

### NODE C.39 [lemma] [fresh]

**STATEMENT.** *The per-side scalar, TERMINAL pin-height form (PE3 F-1).* With C.37's
context, at every above-seam side `(u₂, ℓ₂)`:

```
dv2ResPoly L Ψ f … = γ_g · β^{c₁(m₁^{f_S}, c_g)} · dv2ResPoly L Ψ f_S …
```

where `γ_g` is `g`'s level-2 residue read (a fixed element of `K₂^×`), `β` = C.12's
level-2 letter (`AdjoinRoot.root L.r`), `m₁^{f_S}` is the PIN height at the side's starting
index (an integer — NOT the side's line value, which off the first side need not be one:
PE3 F-1's ill-formedness witness `39/2 ∉ ℤ`), and `c₁` is C.28's cocycle. At `L.ℓ = 1` the
exponent vanishes (C.28(ii)) and the scalar is `γ_g` alone — the battery-exercised branch.

**SIGNATURE.**
```lean
namespace Uniformity.Density.Tower

theorem dv2ResPoly_scalar {F : KeyFrame O π} {H₀ hpin} (L : LevelDatum F H₀ hpin) … :
    dv2ResPoly L Ψ f u₂ ℓ₂ …
      = Polynomial.C (γg … * (AdjoinRoot.root L.r) ^ (L.cocycle (pinHeight …) (complementConst …)))
          * dv2ResPoly L Ψ (blockFactor L f …) u₂ ℓ₂ …
```

(`γg` and `pinHeight` are companion `def`s in this file; `pinHeight` is the level-2
`dv2Pin` at the side's `dvSideMin`-analogue index — the GC-1 pin discipline at level 2.)

**DEPENDS.** C.12 · C.22 · C.28 · C.36 · C.37 · **GC-13 placeholder:
`EFF.HE7.<nn> — ANNEX-LEMMA R1-a(iii)/(iv) [supplied-by: chapter E]`** (the cocycle-unit
residue law `res(τ₂) = β^{c₁}`; C.28's arithmetic is chapter C's, the residue-transport
step is stated here with the placeholder as its corpus anchor — the orchestrator reconciles
at freeze; if E's transcription of R1-a lands first, this node's step 2 cites it by node ID).

**PROOF (route).**
1. Multiply the developments; normalize each side by the pin-height monomial (PE3 F-1's own
   mechanism: “normalize each side by `n₂(m₁)·Ψ(ξ)^{j₁}` … the `Ψ(ξ)^{j₁}` factor is COMMON
   to `f` and `f_S` and CANCELS in the ratio”).
2. The normalizer composition picks up exactly `β^{c₁(m₁^{f_S}, c_g)}` (C.28's arithmetic +
   the placeholder residue law); the remaining ratio is `γ_g` by C.36(iii)'s constancy.
3. `ℓ = 1` clause: C.28(ii).

**SIZE.** 36 lines.

**SOURCE.** `EFF.HE6R1.39` (PE3 F-1, TERMINAL layer of chain C-5, verbatim display
`R^f_{λ₂} = γ_g·β^{c₁(m₁^{f_S}, c_g)}·R^{f_S}_{λ₂}`, with the ill-formedness audit);
`EFF.HE6R1.35` (PE2 F-2 — layer 2, DEAD as a display, kept as the derivation's source);
`EFF.HE6R1.13`(c)'s `[r1′]` `γ_g` (layer 1, exact at `ℓ = 1`).

**TEETH.** “PE3's blast-radius check found no consumer of the exponent at HEAD”
(`EFF.HE6R1.39`) → the scalar's UNIT-hood (not its exponent) is what C.38/§7 consume —
**signed non-applicability** for the exponent value; the `ℓ = 1` clause rides
`HE6R1-T-TWIST0`'s regression (C.28).

**ENVIRONMENT.** ENV-C2.

---

### NODE C.40 [theorem] [fresh]

**STATEMENT.** *The level-2 peel (LEMMA HE6R1-3, closure-free).* With the standing pair
(`Squarefree f`, `¬ F.key ∣ f`) and C.35's block `f_S`, suppose instead `Ψ ∣ f_S` for a test
key `Ψ` (`IsTestKey L Ψ`). Then: (i) `Ψ` is the ONLY such divisor and appears to the first
power: `f_S = Ψ * f_S'` with `¬ Ψ ∣ f_S'` (squarefreeness); (ii) `typeOf Ψ =
⟨{(F.e₁ * L.ℓ, F.f₁ * L.r.natDegree)}⟩` — `e(Ψ) = e₁ℓ, f(Ψ) = f₁d_r` — hence `Ψ` is
irreducible over `O`; **conditional exactly as §7's Tier-1 is** (the residue leg at
`f₁·d_r ≥ 2` carries `C-BOX-1` — this node consumes C.61 and inherits its conditionality,
no more); (iii) `mult₂` drops by exactly one:
`(f_S'.natDegree) = L.keyDeg₂ * (mult₂ L f … − 1)`, and the peel applies at most once
(squarefreeness kills a second `Ψ`-factor).

**SIGNATURE.**
```lean
namespace Uniformity.Density.Tower

theorem level2_peel {F : KeyFrame O π} {H₀ hpin} (L : LevelDatum F H₀ hpin)
    (hπ : Irreducible π) [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    [Finite (ResidueField O)]
    {f Ψ : Polynomial O} (hΨ : IsTestKey L Ψ) (hctx : …) (hdvd : Ψ ∣ blockFactor L f hctx)
    (hbox : CBox1Side L Ψ) :   -- §7's C-BOX-1 hypothesis carrier, C.60; vacuous at f₁·d_r = 1
    typeOf Ψ = ⟨{(F.e₁ * L.ℓ, F.f₁ * L.r.natDegree)}, …⟩ ∧
    Irreducible Ψ ∧
    ∃ fS', blockFactor L f hctx = Ψ * fS' ∧ ¬ Ψ ∣ fS' ∧
      fS'.natDegree = L.keyDeg₂ * (mult₂ L f hctx - 1)
```

**⚠ FAITHFULNESS (the C-D1 recast at its sharpest).** The corpus proof (`EFF.HE6R1.16`) is
a Galois-orbit squeeze (“`g₀ ∈ O[x]` is Galois-stable, so it contains ξ's whole orbit”).
The Lean route replaces it: `Ψ` has degree `D″ = (e₁ℓ)(f₁d_r)` (C.13) and label-grade slot
data, so §7's divisibility legs give `e₁ℓ ∣ e'` and (under `hbox`) `f₁d_r ∣ f'` for every
`(e', f') ∈ (typeOf Ψ).data`; landed `typeOf_degree` + `efPair_pos_of_mem` force the
singleton — **the same sandwich as the corpus's step, `ef = D″` forcing equality, with the
orbit replaced by the factor** (`EFF.HE6R1.16`'s audit itself notes this is “the same
sandwich as HE6's THEOREM HE6.A step 4, one level up”). Flagged §16 with C-D1.

**DEPENDS.** C.10 (`keyDeg₂_regroup`) · C.13 · C.35 · C.36(i) · **C.60/C.61 (§7's
divisibility legs + Tier-1 — forward dependency; §7 fires before this node)** · landed
`typeOf_degree`, `efPair_pos_of_mem`, `FactorizationType.ext`.

**PROOF.**
1. (ii): C.61 applied to `Ψ` itself (a degree-`D″` label carrier: C.13's slot data make
   `HasLabel L Ψ` with `m = 1` — a private lemma here); irreducibility from the singleton
   `typeOf` + degree (`typeOf` of a monic with singleton data of full degree ⟹ one monic
   factor — landed `monicFactors` uniqueness).
2. (i)/(iii): `Squarefree f` descends to `f_S`; degree arithmetic through C.35's exact
   division and C.10.

**SIZE.** 34 lines.

**SOURCE.** `EFF.HE6R1.15` (LEMMA HE6R1-3, verbatim: `g₀ = Ψ`, `Ψ` irreducible of degree
`D″`, `e(Ψ) = e₁ℓ, f(Ψ) = f₁d_r`, `μ₂` drops by 1, at most once); `EFF.HE6R1.16` (the proof
+ audit + the 12/12, 5/5-PARI machine confirmation); `EFF.HE6R1.14` (FINDING HE6R1-F2 — the
missing hypothesis this peel repairs).

**TEETH.** the supplementary leg (`he6r1_supp.py` item (A): 12/12 decided, 5/5 PARI,
`σ = {(2,2),(2,2)}` member by member) → **executable regression** retained + the σ value
`{(e₁ℓ, f₁d_r)} = {(2,2)}` fires as a §13 gate instance (`q = 3` from the battery; the
`q = 2` twin at the `(1,2)`-genre frame per `EFF.HE6.20`(3), which is live at `q = 2`).

**ENVIRONMENT.** ENV-C3.

---

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

<!-- RESUME: §3–§5 COMPLETE (C.01–C.40). Forward refs recorded in-node: C.13→C.21; C.27→C.29/C.33/C.34; C.31→C.33/C.35; C.40→C.60/C.61 (§7 fires before C.40). RE-PLAN bookings so far: dvResPoly_mul_of_pure (B.35 twin, from C.34/C.37), dv2ResPoly def (from C.38), complementConst/γg/pinHeight defs (C.36/C.39). AMENDMENT owed to committed C-H3 wording: §5 DOES construct test keys (C.13/C.14, O[x]-algebra) — record in A-§5 block at chapter close: the immunity claim is "no fractional-height ELEMENT below degree D″, no base change", not "no test key". Next: §6 (C.41–C.58) from EFF-HETOW (composed key Φ₂ wrap-corrected .13, HETOW-1/2/3 bridges, W(t), C-A/C-B riders) + EFF-GENTOW1 (GENTOW-1 clip R2a .65, GENTOW-2 DOM/COD R2b .66, GENTOW-5 three bands R2c .67, K₂-digit lift M_{r,t} .62/.53, COR GENTOW-1.1). Read those EFF units first. Then §7 (DECISION section, C.59–C.70). Commit per 2–3 nodes. -->


<!-- CHAP-C APPEND POINT — do not remove; sections are appended here in order -->
