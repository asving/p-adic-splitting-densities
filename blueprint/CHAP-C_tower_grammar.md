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
abbrev KeyFrame.stageField (F : KeyFrame O π) (H₀ : ℕ) (hpin : F.Pin H₀) : Type _ :=
  AdjoinRoot (F.frameRes H₀ hpin)

/-- `|K| = Q^{f₁}` as a number (the lemma-level identity is C.04). -/
noncomputable def KeyFrame.stageCard (F : KeyFrame O π) [Finite (ResidueField O)] : ℕ :=
  residueCard O ^ F.f₁  -- [A-C.1/D18: `noncomputable` — `residueCard` is]
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

-- [A-C.1/D5: the "analogous" cluster DECLARED — B.20 lands no `sideLen`, so `dvSideLen`
-- is the stub-side determination `max − min` (the only reading making C.08(b) the B.20(d)
-- analogue); adopted as the signed text]
noncomputable def dvSideMax (F : KeyFrame O π) (f : Polynomial O) (u ℓ : ℕ)
    (h : (dvSideSet F f u ℓ).Nonempty) : ℕ := (dvSideSet F f u ℓ).max' h

noncomputable def dvSideDeg (F : KeyFrame O π) (f : Polynomial O) (u ℓ : ℕ)
    (h : (dvSideSet F f u ℓ).Nonempty) : ℕ :=
  (dvSideMax F f u ℓ h - dvSideMin F f u ℓ h) / ℓ

noncomputable def dvSideLen (F : KeyFrame O π) (f : Polynomial O) (u ℓ : ℕ)
    (h : (dvSideSet F f u ℓ).Nonempty) : ℕ :=
  dvSideMax F f u ℓ h - dvSideMin F f u ℓ h
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

theorem dvOnSide_modEq (F : KeyFrame O π) {u ℓ : ℕ} (hℓ : 0 < ℓ) (hcop : Nat.Coprime u ℓ)
    {f : Polynomial O} {j j' : ℕ} (hj : DvOnSide F f u ℓ j) (hj' : DvOnSide F f u ℓ j') :
    j ≡ j' [MOD ℓ]   -- [A-C.1/D3: `{u ℓ : ℕ}` bound — they were unbound]

theorem dvSideLen_eq (F : KeyFrame O π) {u ℓ : ℕ} (hℓ : 0 < ℓ) (hcop : Nat.Coprime u ℓ)
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
noncomputable def LevelDatum.keyDeg₂ {F : KeyFrame O π} {H₀ hpin} (L : LevelDatum F H₀ hpin) : ℕ :=
  (F.e₁ * F.f₁) * L.ℓ * L.r.natDegree

/-- `T₂ = ℓ·d_r·λ`, cleared to the integer `d_r·u`. -/
noncomputable def LevelDatum.seam {F : KeyFrame O π} {H₀ hpin} (L : LevelDatum F H₀ hpin) : ℕ :=
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
    [Finite (ResidueField O)] (hπ : Irreducible π) (hh : 1 ≤ F.h) :
    ∃ Ψ : Polynomial O, IsTestKey L Ψ
```

**⚠ D20 RE-SIGN [signed: A-C.1, 2026-08-16].** The originally-signed form carried no frame
hypothesis, and the stub gate found the case `F.h = 0 ∧ 2 ≤ F.e₁·F.f₁` (live: `hcop` forces
`e₁ = 1` at `h = 0`, `f₁` unconstrained) covered by NEITHER proof branch — step 2's
`GenreDatum` needs `1 ≤ h` (D19), step 3 covers only `D′ = 1`. Re-signed with
`(hh : 1 ≤ F.h)`, the corpus's own frame hypothesis (`EFF.HE6.08`; C.01's docstring: "the
corpus frame has `1 ≤ h`"), under which the two branches are EXHAUSTIVE (`2 ≤ D′` via the
C.14a adapter; `D′ = 1`, which forces `e₁ = f₁ = 1`, via the elementary lift). The excluded
`h = 0` corner is the degenerate frame admitted for C.05's reconciliation alone; no test-key
consumer fires on it. The STATEMENT's original "with `2 ≤ F.e₁ * F.f₁`" clause was the
misplaced trace of the proof's INTERNAL split (restoring it would kill the proof's own step 3
and leave `h = 0 ∧ D′ ≥ 2` inside the statement and uncovered) — it is superseded by the
`1 ≤ F.h` reading above. Step 2's `GenreDatum` plumbing is now NODE C.14a (below), the §15
RE-PLAN booking ("the `stageLiftO` GenreDatum packaging — merge into ONE helper") executed.

---

### NODE C.14a [def] [fresh] [signed: A-C.1] — **the H §8 carrier bridge (D19/D20 resolution)**

**STATEMENT.** *The adapter from the frame to H.01's landed carrier, with the corpus
preconditions explicit.* (i) `KeyFrame.genreDatum F hh hkey : GenreDatum` — the landed H.01
datum at `(Q, e₁, f₁, μ, h) := (residueCard O, F.e₁, F.f₁, 2, F.h)`, requiring EXACTLY the two
hypotheses the corpus has and `KeyFrame` (deliberately) lacks: `hh : 1 ≤ F.h` (`EFF.HE6.08`'s
frame) and `hkey : 2 ≤ F.e₁ * F.f₁` (`GENHN.CLASS`(i)'s composite-stage clause); `hQ` is landed
`two_le_residueCard`, and the `μ`-slot is the dummy `2` (H.54's lift never reads `μ` —
machine-verified at the stub gate, `ChapH/H54.lean:76`). **H's landed side is untouched.**
(ii) `KeyFrame.stageLiftIA F i a lift` — the lift with H.54's own summand shape over the
frame's numerals, TOTAL (no hypotheses: definitions are total; the preconditions sit on the
consuming theorems). (iii) `stageLiftIA_eq_stageLift'` — the `rfl`-grade reconciliation on the
corpus perimeter: **the ONE door through which chapter C consumes H §8** (GC-5/H-14 honored);
H.55/H.56 transport through it. (iv) `KeyFrame.stageCoord` (the `F_Q`-digit read of a
stage-field element in the letter basis, canonical-representative-based) and
`KeyFrame.stageLiftO F H₀ hpin M c` — the element-at-height-`M` form C.43's display consumes,
with the `(i, a)`-solve by C.15's `slotIdx` (H.54's signed lesson executed: `i`, `a` explicit,
the height equation carried by the consuming lemmas, never `Exists.choose`).

**SIGNATURE.** [signed: A-C.1 — elaborated in `leanspec/Leanspec/ChapC.lean`]
```lean
namespace Uniformity.Density.Tower

noncomputable def KeyFrame.genreDatum (F : KeyFrame O π) [Finite (ResidueField O)]
    (hh : 1 ≤ F.h) (hkey : 2 ≤ F.e₁ * F.f₁) : Uniformity.Density.Induction.GenreDatum where
  Q := residueCard O
  e₁ := F.e₁
  f₁ := F.f₁
  μ := 2
  h := F.h
  hQ := two_le_residueCard O
  he₁ := F.he₁
  hh := hh
  hkey := hkey
  hmul := le_rfl
  hcop := F.hcop

noncomputable def KeyFrame.stageLiftIA (F : KeyFrame O π) (i a : ℕ) (lift : ℕ → O) :
    Polynomial O :=
  ∑ s ∈ Finset.range F.f₁,
    Polynomial.C (lift s * π ^ (a - s * F.h)) * Polynomial.X ^ (i + F.e₁ * s)

theorem stageLiftIA_eq_stageLift' (F : KeyFrame O π) [Finite (ResidueField O)]
    (hh : 1 ≤ F.h) (hkey : 2 ≤ F.e₁ * F.f₁) (i a : ℕ) (lift : ℕ → O) :
    F.stageLiftIA (π := π) i a lift
      = Uniformity.Density.Induction.stageLift' (F.genreDatum hh hkey) π i a lift := rfl

noncomputable def KeyFrame.stageCoord (F : KeyFrame O π) (H₀ : ℕ) (hpin : F.Pin H₀)
    (c : F.stageField H₀ hpin) (s : ℕ) : ResidueField O :=
  (resFieldXEquiv O).symm (((AdjoinRoot.mk_surjective c).choose).coeff s)

noncomputable def KeyFrame.stageLiftO (F : KeyFrame O π) (H₀ : ℕ) (hpin : F.Pin H₀)
    (M : ℕ) (c : F.stageField H₀ hpin) : Polynomial O :=
  F.stageLiftIA (π := π) (F.slotIdx M) ((M - F.slotIdx M * F.h) / F.e₁)
    (fun s => resLift (F.stageCoord H₀ hpin c s))
```
(`KeyFrame.Pin` is the named pin proposition — the stub gate's D4 recommendation, hereby
ADOPTED as a blueprint declaration of this node; `resLift` is the choice-section of the
residue map, a private helper of this file.)

**DEPENDS.** C.01 · C.15 · H.01 · H.54 (both by committed ID; the consuming height/residue
clauses enter H.55/H.56 only through the reconciliation) · landed `two_le_residueCard`,
`resFieldXEquiv` (B.59's auxiliary).

**PROOF.** definitional (`rfl` for the reconciliation). **SIZE.** 40 lines.

**SOURCE.** `EFF.HE6.08` (the `1 ≤ h` frame hypothesis); `EFF.GENHN.07` clause (i) (the
`2 ≤ e₁f₁` clause, via H.01); H.54's ⚠ SIGNATURE NOTE (the `(i, a)`-explicit lesson);
stub-gate defects D19/D20 (the adjudication record).

**TEETH.** signed non-applicable (an adapter; its consumers' teeth fire at C.14/C.43/§13).

**ENVIRONMENT.** ENV-C1 + `[Finite (ResidueField O)]` (for `Q`).

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
`EFF.HE6.13`'s `i₀(k)`). Total: at the degenerate `e₁ = 1` it is `0`.
[A-C.1/D6: the `Nat.find (F.slotIdx_exists k)` body was UNDECLARABLE (`slotIdx_exists`
exists in no node, and `Nat.find` needs the predicate); the gate's total, COMPUTABLE,
junk-`0`-defaulting body is adopted — it agrees with the intended value exactly when it
exists, which `F.hcop` guarantees (C.16's spec pins it).] -/
def KeyFrame.slotIdx (F : KeyFrame O π) (k : ℕ) : ℕ :=
  ((List.range F.e₁).find? (fun i => (i * F.h) % F.e₁ == k % F.e₁)).getD 0

/-- `q(k)`: the ϖ-vs-`n(k)` twist exponent, `i₀·k = i(k) + q(k)·e₁` (`EFF.HE6.13` RIDER). -/
def KeyFrame.twistExp (F : KeyFrame O π) (k : ℕ) : ℕ :=
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

**ENVIRONMENT.** ENV-C1 *[A-C.1 re-tag per D7: stated over `KeyFrame`, which binds the DVR telescope; the pure-arithmetic content is carried by the numeric-gate mirrors (`slotIdxN` etc.)]*.

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

**ENVIRONMENT.** ENV-C1 *[A-C.1 re-tag per D7: stated over `KeyFrame` — see C.15's rider]*.

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

**ENVIRONMENT.** ENV-C1 *[A-C.1 re-tag per D7: stated over `KeyFrame` — see C.15's rider]*.

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

noncomputable def KeyFrame.stageLetter (F : KeyFrame O π) (H₀ : ℕ) (hpin : F.Pin H₀) :
    F.stageField H₀ hpin :=
  AdjoinRoot.root (F.frameRes H₀ hpin)

theorem KeyFrame.stageLetter_ne_zero (F : KeyFrame O π) (hπ : Irreducible π)
    (H₀ : ℕ) (hpin : F.Pin H₀) : F.stageLetter H₀ hpin ≠ 0
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
noncomputable def KeyFrame.slotRes (F : KeyFrame O π) (H₀ : ℕ) (hpin : F.Pin H₀) (k : ℕ)
    (A : Polynomial O) : F.stageField H₀ hpin :=
  (F.slotWindow k).sum fun t =>
    algebraMap (resField (Polynomial.X : Polynomial O)) (F.stageField H₀ hpin)
        (algebraMap (ResidueField O) (resField (Polynomial.X : Polynomial O))
          (digAt π ((k - (F.slotIdx k + F.e₁ * t) * F.h) / F.e₁)
            (A.coeff (F.slotIdx k + F.e₁ * t))))
      * (F.stageLetter H₀ hpin) ^ t
```

[A-C.1/D8: the composite of the two landed quotient maps WRITTEN OUT — mathlib composes no
`Algebra` chains, so `algebraMap _ _` did not elaborate; the two-step form is the signed
text.]

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
noncomputable def KeyFrame.twistRead (F : KeyFrame O π) (H₀ : ℕ) (hpin : F.Pin H₀) (k : ℕ)
    (A : Polynomial O) : F.stageField H₀ hpin :=
  letI : Field (resField (Polynomial.X : Polynomial O)) := instFieldResField isKey_X
  letI : Fact (Irreducible (F.frameRes H₀ hpin)) := ⟨(F.hresirr H₀ hpin).1⟩
  (F.stageLetter H₀ hpin)⁻¹ ^ (F.twistExp k) * F.slotRes H₀ hpin k A
```

[A-C.1/D9: the two `letI`s are the signed text — `stageField` has no `Inv` without them
(the `⁻¹` needs `AdjoinRoot`'s field structure, keyed on `Fact (Irreducible …)` +
`Field (resField X)`, the latter through the new helper `isKey_X` — hereby a blueprint
declaration of this node); this makes `hpin` genuinely USED, as the gate observed.]

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
    (hpin : F.Pin H₀) {A : Polynomial O} {k : ℕ} (hA : A.natDegree < F.e₁ * F.f₁)
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
    [Finite (ResidueField O)] (H₀ : ℕ) (hpin : F.Pin H₀) (k : ℕ) :
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
noncomputable def dvResPoly (F : KeyFrame O π) (H₀ : ℕ) (hpin : F.Pin H₀)
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
    (hpin : F.Pin H₀) {f : Polynomial O} {u ℓ : ℕ} (hℓ : 0 < ℓ) (hcop : Nat.Coprime u ℓ)
    (hne₂ : (dvSideSet F f u ℓ).Nonempty) {M₀ : ℕ}
    (hpin₂ : dvHgt F f (dvSideMin F f u ℓ hne₂) = (M₀ : ℕ∞)) {t : ℕ}
    (ht : t ≤ dvSideDeg F f u ℓ hne₂) :
    (dvResPoly F H₀ hpin f u ℓ hne₂ M₀ hpin₂).coeff t = 0
      ↔ ¬ DvOnSide F f u ℓ (dvSideMin F f u ℓ hne₂ + ℓ * t)

theorem natDegree_dvResPoly (F : KeyFrame O π) (hπ : Irreducible π) (H₀ : ℕ)
    (hpin : F.Pin H₀)
    {f : Polynomial O} {u ℓ : ℕ} (hℓ : 0 < ℓ) (hcop : Nat.Coprime u ℓ)
    (hne₂ : (dvSideSet F f u ℓ).Nonempty) {M₀ : ℕ}
    (hpin₂ : dvHgt F f (dvSideMin F f u ℓ hne₂) = (M₀ : ℕ∞)) :
    (dvResPoly F H₀ hpin f u ℓ hne₂ M₀ hpin₂).natDegree = dvSideDeg F f u ℓ hne₂ ∧
    (dvResPoly F H₀ hpin f u ℓ hne₂ M₀ hpin₂).coeff 0 ≠ 0
```
[A-C.1/D2: "(…same…)" written out — the first signature's binder list reproduced, the
unique reading.]

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
      (F.e₁ * L.ℓ) * (addVal O (Algebra.norm O (AdjoinRoot.mk g C))).toNat = g.natDegree * v
```

[A-C.1/D10: `.get!` → `ENat.toNat` — `ℕ∞ = ENat` carries no `get!`; `toNat` agrees with the
intended value on the `≠ ⊤` locus the statement's own `∃ v` pins. The stub-stage
`ℕ∞`-plumbing fix the parenthetical promised, executed.]

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
    (hjump : 2 ≤ ℓ * dr)
    (hμ₂ : μ₂ * (D * ℓ * dr) = dfS) (hfS : dfS ≤ D * (ℓ * (μ / ℓ)))  -- deg f_S ≤ D′L_λ, L_λ ≤ μ
    : 2 * μ₂ ≤ μ
```

(the exact hypothesis plumbing of `jump_drop` is fixed at stub stage against C.33/C.35's
outputs; the SPEC is the chain `μ₂ ≤ deg R_λ/d_r ≤ μ/(ℓd_r)` with every step ℕ-cleared.)

**⚠ D21 RE-SIGN [signed: A-C.1, 2026-08-16].** As originally committed, `jump_drop`'s third
hypothesis read `hL : ℓ * dr * 2 ≤ 2 * μ` (an UPPER bound `ℓd_r ≤ μ`, where the argument needs
the LOWER bound) and the clause was **FALSE** — machine-refuted at the stub gate at
`(D, ℓ, d_r, μ, μ₂, deg f_S) = (1, 1, 1, 1, 1, 1)`, **168 counterexamples** on
`D, ℓ, d_r ∈ [1,4] × μ, μ₂ ∈ [0,12]` (the executable refutation record is PRESERVED VERBATIM
in `leanspec/Leanspec/ChapC.lean`'s numeric section: `jumpDropAsSigned`/`jumpDropCounterCount`).
The re-signed form above replaces `hL` by `hjump : 2 ≤ ℓ * dr` — **verified against the source
unit `EFF.HE6R1.10`**, whose displayed chain reads verbatim *"μ₂ = deg f_S/D″ ≤ … ≤ μ/(ℓd_r),
using LEMMA HE6-3(b) … for the middle step and ℓd_r ≥ 2 for the last"*: the jump hypothesis is
the SOURCE's own, and `EFF.HE6R1.11`'s punchline ("both branches of the widened box supply the
descent factor ℓd_r ≥ 2") is why it is available at every jump — the same hypothesis the
sibling `jump_floor` carries as `hjump`. Zero counterexamples on the larger box
`D, ℓ, d_r ∈ [1,5] × μ, μ₂ ∈ [0,24]` (`#guard jumpDropRepairedCount == 0`, executed). The
original transcription was a slip, not a source error.

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

**SIGNATURE** [signed: A-C.1 — elaborated in `leanspec/Leanspec/ChapC.lean`]. The witness
type is **B.42's landed template** (`exists_slope_factorization`, the CHAP-I addendum's exact
statement — the unique corpus-anchored reading of "B.41/B.42 one level up") at the
`dv`-carrier, packaged as a structure (GC-4's inductive-domain licence; what C.35's choice
needs) with existence and uniqueness as the two theorem clauses:

```lean
namespace Uniformity.Density.Tower

structure DvDissection (F : KeyFrame O π) (f : Polynomial O) : Type _ where
  slopes : Finset (ℕ × ℕ)
  factor : ℕ × ℕ → Polynomial O
  below : Polynomial O
  hslopes : ∀ p ∈ slopes,
    0 < p.2 ∧ Nat.Coprime p.1 p.2 ∧ p.2 * ((F.e₁ * F.f₁) * F.h) < p.1
  hdistinct : ∀ p ∈ slopes, ∀ q ∈ slopes, p ≠ q → p.1 * q.2 ≠ q.1 * p.2
  hmonic : ∀ p ∈ slopes, (factor p).Monic
  hpure : ∀ p ∈ slopes, IsDvPure F (factor p) p.1 p.2
  hdeg : ∀ p ∈ slopes, ∀ hne : (dvSideSet F f p.1 p.2).Nonempty,
    (factor p).natDegree = (F.e₁ * F.f₁) * (p.2 * dvSideDeg F f p.1 p.2 hne)
  hbelow_monic : below.Monic
  hbelow : ∀ u ℓ : ℕ, 0 < ℓ → Nat.Coprime u ℓ → ℓ * ((F.e₁ * F.f₁) * F.h) < u →
    ∀ hne : (dvSideSet F below u ℓ).Nonempty, dvSideDeg F below u ℓ hne = 0
  hprod : f = below * ∏ p ∈ slopes, factor p
  hsides : ∀ u ℓ : ℕ, 0 < ℓ → Nat.Coprime u ℓ → ℓ * ((F.e₁ * F.f₁) * F.h) < u →
    ((u, ℓ) ∈ slopes ↔ ∃ hne : (dvSideSet F f u ℓ).Nonempty, 0 < dvSideDeg F f u ℓ hne)

theorem exists_dvDissection (F : KeyFrame O π) (hπ : Irreducible π)
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    {f : Polynomial O} (hf : f.Monic) (hkey : ¬ F.key ∣ f) :
    Nonempty (DvDissection F f)

theorem dvDissection_unique (F : KeyFrame O π) (hπ : Irreducible π)
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    {f : Polynomial O} (hf : f.Monic) (hkey : ¬ F.key ∣ f)
    (D D' : DvDissection F f) :
    D.slopes = D'.slopes ∧ D.below = D'.below ∧ ∀ p ∈ D.slopes, D.factor p = D'.factor p
```
(the "below-floor remainder" clause `hbelow` — trivial above-floor sides — is what makes
uniqueness true; the degree clause is the `(SEP)`-free `n_λ = D′·L_λ` with
`L_λ = ℓ·dvSideDeg`, C.08(b)'s length law.)

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

**SIGNATURE** [signed: A-C.1 — elaborated in `leanspec/Leanspec/ChapC.lean`]. Signed at the
consumed `(λ, r)`-BLOCK clause (the "in particular" of the STATEMENT — what C.35/C.36/C.61
read); the general coprime-prime-power refinement is the fleet's proof content (B.48's
route), not a second public statement. The stub gate's missing-`L`-binder and
missing-`dvResPoly`-argument defects are cured by the `L`-headed form with the complement's
non-divisibility ∀-quantified over ITS OWN pin witnesses (the dependent-plumbing resolution):

```lean
namespace Uniformity.Density.Tower

theorem exists_dv_residual_dissection {F : KeyFrame O π} {H₀ hpin} (L : LevelDatum F H₀ hpin)
    (hπ : Irreducible π) [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    {g : Polynomial O} (hg : g.Monic) (hpure : IsDvPure F g L.u L.ℓ)
    (hne : (dvSideSet F g L.u L.ℓ).Nonempty) {M₀ : ℕ}
    (hp : dvHgt F g (dvSideMin F g L.u L.ℓ hne) = (M₀ : ℕ∞))
    (hdvd : L.r ∣ dvResPoly F H₀ hpin g L.u L.ℓ hne M₀ hp) :
    ∃ fS g' : Polynomial O, g = fS * g' ∧ HasLabel L fS ∧ g'.Monic ∧
      (∀ (hne' : (dvSideSet F g' L.u L.ℓ).Nonempty) (M₀' : ℕ)
        (hp' : dvHgt F g' (dvSideMin F g' L.u L.ℓ hne') = (M₀' : ℕ∞)),
        ¬ L.r ∣ dvResPoly F H₀ hpin g' L.u L.ℓ hne' M₀' hp') ∧
      ∀ fS' g'' : Polynomial O, g = fS' * g'' → HasLabel L fS' → g''.Monic →
        (∀ (hne' : (dvSideSet F g'' L.u L.ℓ).Nonempty) (M₀' : ℕ)
          (hp' : dvHgt F g'' (dvSideMin F g'' L.u L.ℓ hne') = (M₀' : ℕ∞)),
          ¬ L.r ∣ dvResPoly F H₀ hpin g'' L.u L.ℓ hne' M₀' hp') →
        fS' = fS ∧ g'' = g'
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

**SIGNATURE** [signed: A-C.1 — elaborated in `leanspec/Leanspec/ChapC.lean`]. The elided
"context" is the named Prop `BlockContext` (the §5 standing pair + a genuine `(λ, r)`-side of
`f`'s own read); `blockFactor` takes the TOTAL maximal-labelled-divisor body (choice; junk
`1` when none) so the def needs NO context argument — the context sits on the spec companion,
where C.34's uniqueness makes the maximal labelled divisor THE block:

```lean
namespace Uniformity.Density.Tower

def BlockContext {F : KeyFrame O π} {H₀ hpin} (L : LevelDatum F H₀ hpin)
    (f : Polynomial O) : Prop :=
  f.Monic ∧ Squarefree f ∧ ¬ F.key ∣ f ∧
  ∃ (hne : (dvSideSet F f L.u L.ℓ).Nonempty) (M₀ : ℕ)
    (hp : dvHgt F f (dvSideMin F f L.u L.ℓ hne) = (M₀ : ℕ∞)),
    0 < dvSideDeg F f L.u L.ℓ hne ∧
    L.r ∣ dvResPoly F H₀ hpin f L.u L.ℓ hne M₀ hp

noncomputable def blockFactor {F : KeyFrame O π} {H₀ hpin} (L : LevelDatum F H₀ hpin)
    (f : Polynomial O) : Polynomial O :=
  open Classical in
  if h : ∃ fS : Polynomial O, HasLabel L fS ∧ fS ∣ f ∧
      ∀ fS' : Polynomial O, HasLabel L fS' → fS' ∣ f → fS' ∣ fS
  then h.choose else 1

noncomputable def mult₂ {F : KeyFrame O π} {H₀ hpin} (L : LevelDatum F H₀ hpin)
    (f : Polynomial O) : ℕ := (blockFactor L f).natDegree / L.keyDeg₂

theorem blockFactor_spec {F : KeyFrame O π} {H₀ hpin} (L : LevelDatum F H₀ hpin)
    (hπ : Irreducible π) [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    {f : Polynomial O} (hctx : BlockContext L f) :
    HasLabel L (blockFactor L f) ∧ blockFactor L f ∣ f ∧
    (blockFactor L f).natDegree = L.keyDeg₂ * mult₂ L f ∧ 0 < mult₂ L f
```
(**A-C.1 note for D13:** `blockFactor_spec`'s `HasLabel` clause plus C.29's existential `m`
and the exactness clause tie the two multiplicities the stub gate's D13 flagged: under
`hctx`, `HasLabel`'s `m` and `mult₂` agree through C.26's degree law — the fleet proves the
tie inside this spec, which is the D13 disposition.)

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

**SIGNATURE** [signed: A-C.1 — elaborated in `leanspec/Leanspec/ChapC.lean`]. The elided
context is C.35's `BlockContext` (which carries the PEEL-CONVENTION pair, so the separate
`hf`/`hsq`/`hkey` binders fold in); the complement's non-divisibility is ∀-quantified over
its own pin witnesses (the C.34 plumbing pattern); **A-C.1 determination on `c_g`'s units:**
`complementConst := (dvSupp F g L.u L.ℓ).toNat` — the `dv₂`-unit value under which C.37's
display type-checks (`dv2Hgt` IS `dvSupp`, C.11); the STATEMENT's `L.ℓ •` prefix was a
clearing slip, recorded here rather than transcribed:

```lean
namespace Uniformity.Density.Tower

noncomputable def complementConst {F : KeyFrame O π} {H₀ hpin} (L : LevelDatum F H₀ hpin)
    (f : Polynomial O) : ℕ :=
  (dvSupp F (f /ₘ blockFactor L f) L.u L.ℓ).toNat

theorem block_complement_notdvd {F : KeyFrame O π} {H₀ hpin} (L : LevelDatum F H₀ hpin)
    (hπ : Irreducible π) [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    {f : Polynomial O} (hctx : BlockContext L f) :
    (∀ Ψ : Polynomial O, IsTestKey L Ψ → (Ψ ∣ blockFactor L f ↔ Ψ ∣ f)) ∧
    (∀ (hne' : (dvSideSet F (f /ₘ blockFactor L f) L.u L.ℓ).Nonempty) (M₀' : ℕ)
      (hp' : dvHgt F (f /ₘ blockFactor L f)
          (dvSideMin F (f /ₘ blockFactor L f) L.u L.ℓ hne') = (M₀' : ℕ∞)),
      ¬ L.r ∣ dvResPoly F H₀ hpin (f /ₘ blockFactor L f) L.u L.ℓ hne' M₀' hp') ∧
    dvSupp F (f /ₘ blockFactor L f) L.u L.ℓ ≠ ⊤
```

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

**SIGNATURE** [signed: A-C.1 — elaborated in `leanspec/Leanspec/ChapC.lean`; the context is
`BlockContext` + the `¬ Ψ ∣ f_S` clause C.36's "in particular" supplies].
```lean
namespace Uniformity.Density.Tower

theorem dv2Supp_translation {F : KeyFrame O π} {H₀ hpin} (L : LevelDatum F H₀ hpin)
    (hπ : Irreducible π) [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    {f Ψ : Polynomial O} (hΨ : IsTestKey L Ψ) (hctx : BlockContext L f)
    (hnd : ¬ Ψ ∣ blockFactor L f)
    {u₂ ℓ₂ : ℕ} (hℓ₂ : 0 < ℓ₂) (hseam : ℓ₂ * L.seam < u₂) :
    dv2Supp L Ψ f u₂ ℓ₂
      = dv2Supp L Ψ (blockFactor L f) u₂ ℓ₂ + ℓ₂ • (complementConst L f : ℕ∞)
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

**SIGNATURE** [signed: A-C.1 — elaborated in `leanspec/Leanspec/ChapC.lean`]. The `dv2ResPoly`
+ `dv2SideSet` companion cluster is hereby the booked **NODE C.38a** (the §15 RE-PLAN
executed; full defs at the node's leanspec twin — `Dv2OnSide`/`dv2SideSet`/`dv2SideMin`/
`dv2SideMax`/`dv2SideDeg` mirror C.07 at the `dv₂`-carrier, and `dv2Res A` is the coherent
`K₂`-read "`A`'s own `dvResPoly` evaluated at the letter `β`" via `AdjoinRoot.mk L.r`, with
`dv2ResPoly` the per-slot assembly, C.25 one level up). **A-C.1 determination:** "same
radical" is signed as same-monic-irreducible-divisors (carrier-free; no `radical` import):

```lean
namespace Uniformity.Density.Tower

theorem dv2ResPoly_radical_eq {F : KeyFrame O π} {H₀ hpin} (L : LevelDatum F H₀ hpin)
    (hπ : Irreducible π) [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    {f Ψ : Polynomial O} (hΨ : IsTestKey L Ψ) (hctx : BlockContext L f)
    (hnd : ¬ Ψ ∣ blockFactor L f)
    {u₂ ℓ₂ : ℕ} (hℓ₂ : 0 < ℓ₂) (hseam : ℓ₂ * L.seam < u₂)
    (hne : (dv2SideSet L Ψ f u₂ ℓ₂).Nonempty)
    (hne' : (dv2SideSet L Ψ (blockFactor L f) u₂ ℓ₂).Nonempty) :
    (dv2ResPoly L Ψ f u₂ ℓ₂ hne).natDegree
        = (dv2ResPoly L Ψ (blockFactor L f) u₂ ℓ₂ hne').natDegree ∧
    ∀ q : Polynomial (AdjoinRoot L.r), q.Monic → Irreducible q →
      (q ∣ dv2ResPoly L Ψ f u₂ ℓ₂ hne ↔ q ∣ dv2ResPoly L Ψ (blockFactor L f) u₂ ℓ₂ hne')
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

**SIGNATURE** [signed: A-C.1 — elaborated in `leanspec/Leanspec/ChapC.lean`].
```lean
namespace Uniformity.Density.Tower

noncomputable def γg {F : KeyFrame O π} {H₀ hpin} (L : LevelDatum F H₀ hpin)
    (f : Polynomial O) : AdjoinRoot L.r :=
  dv2Res L (f /ₘ blockFactor L f)

noncomputable def pinHeight {F : KeyFrame O π} {H₀ hpin} (L : LevelDatum F H₀ hpin)
    (Ψ f : Polynomial O) (u₂ ℓ₂ : ℕ) (hne : (dv2SideSet L Ψ f u₂ ℓ₂).Nonempty) : ℕ :=
  (dv2Pin L Ψ f (dv2SideMin L Ψ f u₂ ℓ₂ hne)).toNat

theorem dv2ResPoly_scalar {F : KeyFrame O π} {H₀ hpin} (L : LevelDatum F H₀ hpin)
    (hπ : Irreducible π) [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    {f Ψ : Polynomial O} (hΨ : IsTestKey L Ψ) (hctx : BlockContext L f)
    (hnd : ¬ Ψ ∣ blockFactor L f)
    {u₂ ℓ₂ : ℕ} (hℓ₂ : 0 < ℓ₂) (hseam : ℓ₂ * L.seam < u₂)
    (hne : (dv2SideSet L Ψ f u₂ ℓ₂).Nonempty)
    (hne' : (dv2SideSet L Ψ (blockFactor L f) u₂ ℓ₂).Nonempty) :
    dv2ResPoly L Ψ f u₂ ℓ₂ hne
      = Polynomial.C (γg L f * (AdjoinRoot.root L.r)
            ^ (L.cocycle (pinHeight L Ψ (blockFactor L f) u₂ ℓ₂ hne') (complementConst L f)))
          * dv2ResPoly L Ψ (blockFactor L f) u₂ ℓ₂ hne'
```
(`γg` and `pinHeight` land as the displayed companion defs; `pinHeight` is the level-2
`dv2Pin` at the side's `dv2SideMin` index — the GC-1 pin discipline at level 2, taken on
the BLOCK's side per PE3 F-1's `m₁^{f_S}`.)

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

**SIGNATURE** [signed: A-C.1 — elaborated in `leanspec/Leanspec/ChapC.lean`; D11 cured
in-statement: `FactorizationType`'s one-field constructor].
```lean
namespace Uniformity.Density.Tower

theorem level2_peel {F : KeyFrame O π} {H₀ hpin} (L : LevelDatum F H₀ hpin)
    (hπ : Irreducible π) [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    [Finite (ResidueField O)]
    {f Ψ : Polynomial O} (hΨ : IsTestKey L Ψ) (hctx : BlockContext L f)
    (hdvd : Ψ ∣ blockFactor L f)
    (hbox : CBox1Side L Ψ) :   -- §7's C-BOX-1 hypothesis carrier, C.60; vacuous at f₁·d_r = 1
    typeOf Ψ = ⟨{(F.e₁ * L.ℓ, F.f₁ * L.r.natDegree)}⟩ ∧
    Irreducible Ψ ∧
    ∃ fS' : Polynomial O, blockFactor L f = Ψ * fS' ∧ ¬ Ψ ∣ fS' ∧
      fS'.natDegree = L.keyDeg₂ * (mult₂ L f - 1)
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

> **Design note.** Two halves. **HETOW half (C.41–C.49):** the wrap cocycle, the composed
> frame datum, the WRAP-CORRECTED key `Φ₂` (the gauge-naive `chat_t` is DEAD corpus-wide —
> C-H5), and the three bridge lemmas HETOW-1/2/3 tying the GENHN composed carrier to §5's
> level-2 machinery — culminating in `IsTestKey`-hood of `Φ₂` (HETOW-2's `w = 0` branch,
> the ONLY branch any consumer reads after C-A(ii)'s re-scope). **GENTOW1 half
> (C.50–C.58):** the composed grid and budgets ([GENHN-TOW-1] items (1), (2), (5) at their
> TERMINAL forms: R2a's clip, R2b's `DOM_N`/`COD_N`, R2c's three bands, the `.62` K₂-digit
> lift base re-solve). Every node here reads at the CORRECTED `chat_t := lift(c_t·η^{W(t)})`,
> `W(t) = ⌊(f₂−t)·i(u₂)/e₁⌋`; the naive form appears only inside refutation records.

### NODE C.41 [lemma] [fresh]

**STATEMENT.** *The wrap cocycle (HETOW-12).* For a frame `F` (write `i(k) := slotIdx F k`,
`Q(k) := twistExp F k`): with `wrap(a,b) := (i(a) + i(b)) / e₁ ∈ {0,1}` (integer division):
(i) `i(a) + i(b) = i(a+b) + e₁·wrap(a,b)` and `Q(a+b) = Q(a) + Q(b) + wrap(a,b)`;
(ii) telescoping, with `W(t) := (f₂−t) * i(u₂) / e₁` (= H.57's wrap exponent):
`(f₂−t)·i(u₂) = i((f₂−t)·u₂) + e₁·W(t)` and `Q((f₂−t)u₂) = (f₂−t)·Q(u₂) + W(t)`
— "both because the two sides are `≡ mod e₁` and `0 ≤ i(·) < e₁`".

**SIGNATURE.**
```lean
namespace Uniformity.Density.Tower

theorem KeyFrame.slotIdx_add (F : KeyFrame O π) (a b : ℕ) :
    F.slotIdx a + F.slotIdx b
      = F.slotIdx (a + b) + F.e₁ * ((F.slotIdx a + F.slotIdx b) / F.e₁) ∧
    (F.slotIdx a + F.slotIdx b) / F.e₁ ≤ 1

theorem KeyFrame.twistExp_add (F : KeyFrame O π) (a b : ℕ) :
    F.twistExp (a + b)
      = F.twistExp a + F.twistExp b + (F.slotIdx a + F.slotIdx b) / F.e₁

theorem KeyFrame.twistExp_nsmul (F : KeyFrame O π) (u₂ f₂ t : ℕ) (ht : t < f₂) :
    F.twistExp ((f₂ - t) * u₂)
      = (f₂ - t) * F.twistExp u₂ + (f₂ - t) * F.slotIdx u₂ / F.e₁
```

**DEPENDS.** C.15 · C.16 · **H.57** (`wrap_div_mod`, `wrap_height` — the floor arithmetic
consumed, per C-H5's GENHN-LIFT licence).

**PROOF.** 1. `i(a)+i(b) ≡ i(a+b) (mod e₁)` (both `≡ (a+b)h⁻¹`); both in `[0, 2e₁)`, so the
quotient is `0` or `1` — C.16's uniqueness + `omega`. 2. Expand C.16(iii) on both sides.
3. Induction on `f₂ − t` via (i), or directly H.57's `wrap_div_mod`.

**SIZE.** 24 lines.

**SOURCE.** `EFF.HETOW.12` (verbatim displays + the frame-X audit `W = (1,0)`);
`EFF.HETOW.11` (`Q(k) = ⌊i₀k/e₁⌋`, which is C.15's `twistExp` — the identification is
C.16(iii)).

**TEETH.** `EFF.HETOW.12`'s audit (`i(3) = 1, W(0) = 1, W(1) = 0` at frame X) →
**executable regression** (§13); the identity leg of the 2026-08-10 run (`k = 1..60` per
frame) → retained.

**ENVIRONMENT.** ENV-C1 *[A-C.1 re-tag per D7: stated over `KeyFrame` — see C.15's rider]*.

---

### NODE C.42 [def] [fresh]

**STATEMENT.** *The composed frame (tower) datum.* Over a frame `F` (+ pin data): a
**tower datum** `T` consists of `e₂, f₂, u₂ : ℕ` and `ψ₂ : Polynomial (stageField F H₀ hpin)`
with: `0 < e₂`, `0 < f₂`, `2 ≤ e₂ * f₂` (a composite inner stage), `Nat.Coprime u₂ e₂`
(the inner slope `κ₂ = u₂/e₂` in lowest terms), the **node floor**
`e₂ * (F.e₁ * F.f₁) * F.h < u₂` (the `[r1]`-corrected `u₂ > e₂D′h`), and `ψ₂` monic
irreducible of degree `f₂` with `ψ₂.coeff 0 ≠ 0`. Derived: `D₂ := (e₁f₁)·e₂f₂` and
`E₂ := e₂ * f₂ * u₂` (GENTOW1's ONE NEW CONSTANT — the `dv₂`-height of every side term of
`Φ₂`).

**SIGNATURE.**
```lean
namespace Uniformity.Density.Tower

structure TowerDatum (F : KeyFrame O π) (H₀ : ℕ) (hpin : F.Pin H₀) where
  e₂ : ℕ
  f₂ : ℕ
  u₂ : ℕ
  ψ₂ : Polynomial (F.stageField H₀ hpin)
  he₂ : 0 < e₂
  hf₂ : 0 < f₂
  hcomp : 2 ≤ e₂ * f₂
  hcop : Nat.Coprime u₂ e₂
  hfloor : e₂ * (F.e₁ * F.f₁) * F.h < u₂
  hψmonic : ψ₂.Monic
  hψirr : Irreducible ψ₂
  hψdeg : ψ₂.natDegree = f₂
  hψ0 : ψ₂.coeff 0 ≠ 0

def TowerDatum.D₂ … : ℕ := (F.e₁ * F.f₁) * (T.e₂ * T.f₂)
def TowerDatum.E₂ … : ℕ := T.e₂ * T.f₂ * T.u₂
```

**DEPENDS.** C.01 · C.03.

**PROOF.** definitional. **SIZE.** 24 lines.

**SOURCE.** `EFF.HETOW.15` (the datum HETOW-1 opens with); `EFF.GENTOW1.07` (`E₂ := e₂f₂u₂`
with the two-family height verification, and the SPLIT `E₂ > dv₂(x^{D₂}) = D₂e₂h` — the
lemma half lands at C.50); `EFF.GENTOW1.14` (the genre data list).

**TEETH.** `EFF.GENTOW1.07`'s five-family audit (`E₂ = 10/14/6/21/6` vs `8/8/4/18/4`) →
§13 regression rows. **ENVIRONMENT.** ENV-C1.

---

### NODE C.43 [def] [fresh]

**STATEMENT.** *The wrap-corrected composed key.* For a tower datum `T`, writing
`c_t := −(ψ₂.coeff t)` (the corpus's sign convention: `ψ₂ = Z^{f₂} − Σ_t c_t Z^t`) and
`η := stageLetter`:

```
composedKey T := Φ′^{e₂f₂} − Σ_{t<f₂} L_{(f₂−t)u₂}(c_t·η^{W(t)}) · Φ′^{e₂t},
```

where `L_k(c)` is the exact-height-`k` stage lift of `c ∈ K` — **consumed as H.54's
`stageLift'`** (C-H5: the lift is licensed ONLY by GENHN-LIFT; at `D′ = 1` the elementary
branch as in C.14 step 3) — and `W(t)` is C.41's wrap exponent. This is `EFF.HETOW.13`'s
display verbatim; the gauge-naive `lift(c_t)` (no `η^{W(t)}`) is DEAD (`EFF.HETOW.14`'s
counter-instance: frame X, naive key `Φ′² + 3xΦ′ + 54` has `σ = {(4,1)}`, corrected
`… + 108` has `σ = {(2,2)}` — the two differ by exactly `η^{W(0)} = 2`).

**SIGNATURE** [signed: A-C.1 — elaborated in `leanspec/Leanspec/ChapC.lean`; D19 RESOLVED:
`stageLiftO` is NODE C.14a's shared packaging (the RE-PLAN merge executed), so the def is
TOTAL — the corpus preconditions (`1 ≤ h`, `2 ≤ e₁f₁`) sit on the height/residue THEOREMS
(C.46/C.47), which consume H.55/H.56 through C.14a's reconciliation].
```lean
namespace Uniformity.Density.Tower

def wrapExp {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀} (T : TowerDatum F H₀ hpin)
    (t : ℕ) : ℕ :=
  (T.f₂ - t) * F.slotIdx T.u₂ / F.e₁

noncomputable def composedKey {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀}
    (T : TowerDatum F H₀ hpin) : Polynomial O :=
  F.key ^ (T.e₂ * T.f₂)
    - (Finset.range T.f₂).sum fun t =>
        F.stageLiftO H₀ hpin ((T.f₂ - t) * T.u₂)
            (- T.ψ₂.coeff t * F.stageLetter H₀ hpin ^ (wrapExp T t))
          * F.key ^ (T.e₂ * t)
```

**DEPENDS.** C.15 · C.19 · C.41 · C.42 · **H.54–H.56** (via the C.14 packaging).

**PROOF.** definitional. **SIZE.** 22 lines.

**SOURCE.** `EFF.HETOW.13` (the display + the `(LIFT)`-construction gloss + residue claim
`c·η^{−Q(k)}`, verbatim; CHAIN-KEY TERMINAL); `EFF.GENTOW1.06` (the same pin from the
consumer side, with the nine-site manifest); `EFF.HETOW.14` (the counter-instance).

**TEETH.** `EFF.HETOW.13`'s supp-leg check (“corrected-key slot residues = minpoly(β) at
each frame: X: `Z²+2Z+2`; Z/W: `Z²+3Z+4`”) → **Lean theorem** at C.46 + **executable
regression**; the `54 vs 108` naive/corrected pair → §13 gate row (it is a `q = 3` frame;
the `q = 2` twin is any η = 1 frame where naive = corrected — the gate documents WHY that
row cannot distinguish, C-H12's coincidence discipline).

**ENVIRONMENT.** ENV-C1.

---

### NODE C.44 [def+lemma] [fresh]

**STATEMENT.** *HETOW-1(a): the translated label `r̃`.* For a tower datum `T` with
`Q := twistExp F T.u₂`: define
`towerLabel T := η^{−Q·f₂} • ψ₂.comp (C (η^Q) * Z) ∈ K[Z]` (monic normalization of the
affine substitution — the explicit form `r̃ = η^{−Qf₂}·ψ₂(η^{Q}Z)`, whose `t`-coefficient
is `−c_t·η^{−(f₂−t)Q}`). Lemma clauses: `towerLabel T` is monic irreducible of degree `f₂`
with nonzero constant term (`ψ₂(0) ≠ 0` transfers; irreducibility under a degree-1 unit
substitution transfers), so **`⟨T.u₂, T.e₂, towerLabel T⟩` is a `LevelDatum`** over `F`
(C.09's fields all discharged: the node floor gives `hκ` since `e₂D′h < u₂`) — the bridge
datum every §5 object reads at.

**SIGNATURE** [signed: A-C.1 — elaborated in `leanspec/Leanspec/ChapC.lean`; `towerLabel`'s
body is the EXPLICIT form `η^{−Qf₂}·ψ₂(η^Q Z)` (the two corpus presentations coincide,
`EFF.HETOW.16`(a)), with the `Field`/`Fact` instances by the C.22 `letI` pattern].
```lean
namespace Uniformity.Density.Tower

noncomputable def towerLabel {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀}
    (T : TowerDatum F H₀ hpin) : Polynomial (F.stageField H₀ hpin) :=
  letI : Field (resField (Polynomial.X : Polynomial O)) := instFieldResField isKey_X
  letI : Fact (Irreducible (F.frameRes H₀ hpin)) := ⟨(F.hresirr H₀ hpin).1⟩
  Polynomial.C ((F.stageLetter H₀ hpin)⁻¹ ^ (F.twistExp T.u₂ * T.f₂))
    * T.ψ₂.comp (Polynomial.C ((F.stageLetter H₀ hpin) ^ F.twistExp T.u₂) * Polynomial.X)

theorem towerLabel_spec {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀}
    (T : TowerDatum F H₀ hpin) (hπ : Irreducible π) :
    (towerLabel T).Monic ∧ Irreducible (towerLabel T) ∧
    (towerLabel T).natDegree = T.f₂ ∧ (towerLabel T).coeff 0 ≠ 0

noncomputable def TowerDatum.levelDatum {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀}
    (T : TowerDatum F H₀ hpin) (hπ : Irreducible π) : LevelDatum F H₀ hpin :=
  ⟨T.u₂, T.e₂, towerLabel T, T.he₂, T.hcop, T.hfloor, (towerLabel_spec T hπ).1,
   (towerLabel_spec T hπ).2.1, (towerLabel_spec T hπ).2.2.2,
   by rw [(towerLabel_spec T hπ).2.2.1]; exact T.hf₂⟩
```
(`levelDatum` gains the `hπ` argument its `spec`-fields need; `hκ` is EXACTLY `T.hfloor`.)

**DEPENDS.** C.09 · C.19 · C.42 · C.15.

**PROOF.** 1. Coefficient formula: expand the composition (`EFF.HETOW.16`(a)'s computation:
substitute; the `t`-coefficient is `−c_t·η^{Qt−Qf₂}`). 2. Irreducibility/degree/constant
term under `Z ↦ η^Q·Z` + unit scale: mathlib composition-with-unit lemmas. 3. `LevelDatum`
fields: `hκ` from `T.hfloor` (`ℓ·D′·h = e₂D′h < u₂`); the rest from clauses 1–2.

**SIZE.** 30 lines.

**SOURCE.** `EFF.HETOW.15`(a) (verbatim — the `[r1]` DEFINITIONAL repair: `r̃` has ONE
definition, minpoly(β); this node takes the EXPLICIT form `η^{−Qf₂}ψ₂(η^QZ)`, which
`EFF.HETOW.16`(a) proves IS the minimal polynomial — so the two corpus presentations
coincide and the explicit one is the Lean-friendly definition); `EFF.HETOW.16`(a) (the
`ψ₂(0) ≠ 0` full-side argument).

**TEETH.** the frame-X value `r̃ = Z² + 2Z + 2` → §13 regression. **ENVIRONMENT.** ENV-C1.

---

### NODE C.45 [lemma] [fresh]

**STATEMENT.** *HETOW-1(b), field form: `K(β) = K(η₂)`.* The two level-2 carriers coincide:
`level2Field (T.levelDatum) = AdjoinRoot (towerLabel T) ≃ₐ[stageField F …] AdjoinRoot T.ψ₂`,
the algebra isomorphism induced by the affine substitution (`β ↦ η^{−Q}·η₂` — the corpus's
pointwise `β_{x₀} = η_{x₀}^{−Q}·η₂(x₀)`, recast as the canonical iso of quotients; "the
root equivalence is the K-affine substitution `Z ↦ η^{Q}Z`", which the corpus itself flags
POINTWISE-hence-wrap-free).

**SIGNATURE** [signed: A-C.1 — elaborated in `leanspec/Leanspec/ChapC.lean`; def-kind node
with a theorem-grade body, stub-carried as an axiom constant — the fleet lands the
`AdjoinRoot`-equiv construction].
```lean
namespace Uniformity.Density.Tower

noncomputable def towerLabelEquiv {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀}
    (T : TowerDatum F H₀ hpin) (hπ : Irreducible π) :
    AdjoinRoot (towerLabel T) ≃ₐ[F.stageField H₀ hpin] AdjoinRoot T.ψ₂
```

**DEPENDS.** C.12 · C.44 · mathlib `AdjoinRoot` equiv-under-composition machinery.

**PROOF.** The substitution `Z ↦ η^Q·Z` (a unit-scale automorphism of `K[Z]`) maps
`(towerLabel T)` to a unit multiple of `ψ₂`; quotients by associate ideals are canonically
isomorphic; `AdjoinRoot.algEquivOfEq`-family plumbing.

**SIZE.** 20 lines.

**SOURCE.** `EFF.HETOW.15`(b)/`EFF.HETOW.16`(b) (the two-factor split + "POINTWISE, hence
wrap-free: only the single height `u₂` is normalized — no product of normalizers occurs").

**TEETH.** signed non-applicable (an interface iso; guarded through C.46's residue values).
**ENVIRONMENT.** ENV-C1.

---

### NODE C.46 [lemma] [fresh]

**STATEMENT.** *HETOW-1(c): the corrected key's slot residues are `r̃`'s coefficients.* For
each `t < f₂`, the ϖ-read (C.22's `twistRead`) of `composedKey T`'s slot-`e₂t` development
coefficient at height `(f₂−t)u₂` equals `(towerLabel T).coeff t` — via the cancellation
`η^{W(t)}·η^{−Q((f₂−t)u₂)} = η^{−(f₂−t)Q}` (C.41(ii)). Consequently `composedKey T`
satisfies the slot clauses of `IsTestKey (T.levelDatum)` at every `t` with `c_t ≠ 0`; at
the gauge-naive key the residue is `−c_t·η^{−(f₂−t)Q−W(t)}` instead and the assembled
polynomial need not be irreducible (frame X: `(Z+1)²`) — transcribed as the refutation
record, not a node.

**SIGNATURE** [re-signed: A-C.1 — gains `(hh : 1 ≤ F.h)`, the C.14a corpus perimeter: the
proof consumes H.56 through the reconciliation].
```lean
namespace Uniformity.Density.Tower

theorem composedKey_slot_residue {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀}
    (T : TowerDatum F H₀ hpin) (hπ : Irreducible π) (hh : 1 ≤ F.h)
    {t : ℕ} (ht : t < T.f₂) :
    F.twistRead H₀ hpin ((T.f₂ - t) * T.u₂) (dev F.key (composedKey T) (T.e₂ * t))
      = (towerLabel T).coeff t
```

**DEPENDS.** C.21 · C.22 · C.41 · C.43 · C.44 · H.55/H.56 (the lift's height/residue).

**PROOF.** 1. The slot-`e₂t` development coefficient IS `−L_{(f₂−t)u₂}(c_t·η^{W(t)})`
(development uniqueness as in C.14 step 4). 2. Its `twistRead` at height `(f₂−t)u₂` is
`−c_t·η^{W(t)}·η^{−Q((f₂−t)u₂)}` (H.56's residue + C.22's twist). 3. C.41(ii) cancels to
`−c_t·η^{−(f₂−t)Q}` = C.44's coefficient — `EFF.HETOW.16`(c)'s computation, step for step.

**SIZE.** 24 lines.

**SOURCE.** `EFF.HETOW.15`(c) + `.16`(c) (verbatim, incl. the audit
`η^{W(t)}·η^{−(f₂−t)Q−W(t)} = η^{−(f₂−t)Q}` ✓); `EFF.HETOW.14` (the naive-key refutation).

**TEETH.** the three-frame supp check (slot residues = minpoly(β)) → **Lean theorem** (this
node) + regression; the naive-key `(Z+1)²` degeneration → §13's contrast row.

**ENVIRONMENT.** ENV-C1.

---

### NODE C.47 [theorem] [fresh]

**STATEMENT.** *HETOW-2 at the (LIFT)-form: the composed key IS a test key, `w = 0`.*
`IsTestKey (T.levelDatum) (composedKey T)` — monic of degree `D₂ = keyDeg₂`, top/off-lattice/
zero-slot clauses from the explicit sum, height and residue clauses from H.55 + C.46; "NO
x-degree-≥ D′ overflow occurs at ANY `f₁`: each `B_t` is already reduced, exact-height …
`Φ₂` is LITERALLY of DEFINITION HE6-1's displayed form and `w = 0`". Consequently **every
§5 statement applies at `Φ₂` verbatim** (the peel C.40, the projection C.36–C.39, the
exactness C.27 — no perturbation lemma is needed). The corpus's carry branch (junk-augmented
presentations, `dv₂(w) > T₂`) is NOT transcribed: C-A(i) withdrew its exemplar and C-A(ii)
re-scoped its licence to exactly this `w = 0` form, and no consumer reads the other branch
(T2's r12 derives the degree conjunct master-side).

**SIGNATURE** [re-signed: A-C.1 — gains `(hh : 1 ≤ F.h)` (the C.14a perimeter; H.55's leg)
and `levelDatum`'s new `hπ` argument].
```lean
namespace Uniformity.Density.Tower

theorem composedKey_isTestKey {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀}
    (T : TowerDatum F H₀ hpin) (hπ : Irreducible π) (hh : 1 ≤ F.h)
    [Finite (ResidueField O)] :
    IsTestKey (T.levelDatum hπ) (composedKey T)
```

**DEPENDS.** C.13 · C.14 (packaging) · C.42 · C.43 · C.44 · C.46 · H.55 (degree `< D′`,
exact height — `EFF.HETOW.18`'s audited chain `x`-degree `≤ (e₁−1) + e₁(f₁−1) = D′−1`).

**PROOF.** Clause-by-clause against C.13: degree/monic (`ring_nf` on the explicit sum +
degree bounds); heights H.55; residues C.46; the fullness legality
`(f₂−t)u₂ ≥ u₂ > e₂D′h > (D′−1)h` (`EFF.HETOW.18`'s chain, `omega` from `T.hfloor`).

**SIZE.** 30 lines.

**SOURCE.** `EFF.HETOW.17` (LEMMA HETOW-2, restated form) + `.18` (the F-4 `w = 0` branch,
verbatim — “the construction this note and the machine legs actually consume”);
`EFF.HETOW.43` (C-A(i)/(ii): the carry branch's exemplar WITHDRAWN and the licence
re-scoped to `w = 0` — the reason the carry branch has NO node; its surviving accounting
core is recorded, not transcribed); `EFF.HETOW.19` (the carry branch, for the record).

**TEETH.** HETOW-2's (LIFT)-branch is what both machine legs instantiate (`f₁ = 1` frames);
the `f₁ ≥ 2` reach is PROOF-ONLY in the corpus (HETOW-BOX-3) — disposition: **Lean theorem
at every `f₁`** (this node's proof is uniform), with the corpus's proof-only disclosure
carried in §16's table (the Lean proof discharges what the corpus could not machine-check —
GC-11 still demands the §13 gates fire an `f₁ = 1` instance at both primes).

**ENVIRONMENT.** ENV-C3.

---

### NODE C.48 [lemma] [fresh]

**STATEMENT.** *HETOW-3: full-side block identities.* Let `f` be monic on the frame's
opening locus with a FULL inner side: `IsDvPure F f T.u₂ T.e₂` with
`dvResPoly F … f T.u₂ T.e₂ … = ψ₂-power` matching `e₂f₂μ₂ = μ₁` (the 𝒯-membership shape,
C.51). Then: (a) `dvHgt F f 0 ≠ ⊤` (i.e. `A₀ ≠ 0`) and `¬ F.key ∣ f`; (b) the block is
everything: `blockFactor (T.levelDatum) f … = f` and `mult₂ … = μ₁ / (e₂f₂)` exactly;
(c) if `composedKey T ∣ f`, the peel C.40 applies at `Φ₂` (licensed by C.47) and peels one
factor with `typeOf = ⟨{(e₁e₂, f₁f₂)}⟩` (C.40's conditionality inherited), continuing at
`mult₂ − 1`.

**SIGNATURE** [signed: A-C.1 — elaborated in `leanspec/Leanspec/ChapC.lean`; clauses (a)+(b)
signed, clause (c) is the C.47 → C.40 chain (a fleet-time re-export, recorded); the full-side
hypothesis written out as the 𝒯-membership clauses].
```lean
namespace Uniformity.Density.Tower

theorem fullSide_block {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀}
    (T : TowerDatum F H₀ hpin) (hπ : Irreducible π) (hh : 1 ≤ F.h)
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [Finite (ResidueField O)]
    {f : Polynomial O} (hf : f.Monic) (hsq : Squarefree f) {μ₂ : ℕ} (hμ₂ : 0 < μ₂)
    (hdeg : f.natDegree = μ₂ * T.D₂) (hpure : IsDvPure F f T.u₂ T.e₂)
    (hres : ∀ (hne : (dvSideSet F f T.u₂ T.e₂).Nonempty) (M₀ : ℕ)
      (hp : dvHgt F f (dvSideMin F f T.u₂ T.e₂ hne) = (M₀ : ℕ∞)),
      dvResPoly F H₀ hpin f T.u₂ T.e₂ hne M₀ hp = (towerLabel T) ^ μ₂) :
    dvHgt F f 0 ≠ ⊤ ∧ ¬ F.key ∣ f ∧
    blockFactor (T.levelDatum hπ) f = f ∧ mult₂ (T.levelDatum hπ) f = μ₂
```

**DEPENDS.** C.29 · C.34 · C.35 · C.40 · C.44 · C.47.

**PROOF.** (a) the full side's left endpoint is an attained pin (its height `κ₂μ₁`-cleared
is finite); `A₀ ≠ 0` ⟹ `F.key ∤ f` (the `j = 0` development coefficient is nonzero).
(b) the side residual is `r̃`-power via C.44/C.45's translation (`ψ₂^{μ₂}` transports to
`r̃^{μ₂}` under the affine substitution, up to the unit scale — `EFF.HETOW.21`(b)'s
transport); C.34's uniqueness gives `f_S = f`; the degree identity `deg f = D′μ₁ = D₂μ₂`
under `e₂f₂μ₂ = μ₁` (`EFF.HETOW.21`'s audit). (c) chain C.47 → C.40.

**SIZE.** 30 lines.

**SOURCE.** `EFF.HETOW.20` (LEMMA HETOW-3, verbatim) + `.21` (proof + audit); the F-2/F-3
annexes (`EFF.HETOW.54`/`.55`): clause (b)'s all-roots transport cite resolves to
**GENTOW1 Step 4** = C.54's realizability layer here — the NEAR-MISS the compiler
adjudicated; this node's (b) consumes C.34/C.44 instead, so the cite chain is closed
inside the chapter.

**TEETH.** `EFF.HETOW.21`'s audit (`deg f/D″ = μ₁/(e₂f₂) = μ₂` integrality = the full-side
hypothesis) → **Lean theorem**; §13 fires the `n = 12` instance (`.25`'s audit values).

**ENVIRONMENT.** ENV-C2.

---

### NODE C.49 [theorem] [fresh]

**STATEMENT.** *THEOREM HETOW.A's composed-stage dictionary (clauses (ii)–(iv), at exactly
ledger strength).* In C.48's full-side setting: (ii) each monic irreducible factor `r₂` of
a separable level-2 residual (of `f` at an above-seam side `(u₃, ℓ₃)`) contributes ONE
irreducible factor of `f` with `typeOf`-entry `(e₁e₂·ℓ₃, f₁f₂·deg r₂)` — **the composed
stage dictionary, conditional exactly as the iterated Tier-1 is** (C.61 applied at the
level-2 datum; `C-BOX-1`'s iterate carried, no more); a repeated `K₂`-rational linear
factor at integer `λ₂` is a finite α-refine chain (C.56/C.57's refine layer, finiteness by
`EFF.HE7.<nn> — LEMMA HE7-8 [supplied-by: chapter E]`); a repeated factor with
`ℓ₃·deg r₂ ≥ 2` passes to level 3 and requires `mult₂ ≥ 4` (C.31's floor one level up).
(iii) At `mult₂ = 3` the level-3 branch is DEAD (`L_{λ₂} ≥ 4 > 3` — the counting exclusion,
pure arithmetic); at `mult₂ = 2` the trichotomy instance is a consistency check, NOT
independent supply (the corpus's own label: "two proofs of one statement" — no node
duplicates it). (iv) Termination: the tower entry is one jump with descent factor
`e₂f₂ ≥ 2`; C.32(b) applies with `μ₁ ≥ mult₂·e₂f₂`; at `n = 12` (`μ₁ = 6`): exactly one
jump, `mult₂ = 3`, no second jump — wrap-immune (the acceptance record's positive scope
finding: the wrap correction moves unit factors only).

**SIGNATURE** [signed: A-C.1 — elaborated in `leanspec/Leanspec/ChapC.lean`; three public
theorems, **split-mandated C.49 → 3**; the dictionary's box hypotheses sit INSIDE the
conclusion's conditional (the factor `g` must be bound first)].
```lean
namespace Uniformity.Density.Tower

theorem composed_dictionary {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀}
    (T : TowerDatum F H₀ hpin) (hπ : Irreducible π) (hh : 1 ≤ F.h)
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [Finite (ResidueField O)]
    {μ₂ : ℕ} {f : Polynomial O} (hf : f ∈ towerLocus T μ₂) (hsq : Squarefree f)
    {u₃ ℓ₃ : ℕ} (hℓ₃ : 0 < ℓ₃) (hcop₃ : Nat.Coprime u₃ ℓ₃) (hfloor₃ : ℓ₃ * T.E₂ < u₃)
    (hne₃ : (dv2SideSet (T.levelDatum hπ) (composedKey T) f u₃ ℓ₃).Nonempty)
    (hsep : (dv2ResPoly (T.levelDatum hπ) (composedKey T) f u₃ ℓ₃ hne₃).Separable)
    {r₂ : Polynomial (AdjoinRoot (towerLabel T))} (hr₂m : r₂.Monic) (hr₂i : Irreducible r₂)
    (hdvd : r₂ ∣ dv2ResPoly (T.levelDatum hπ) (composedKey T) f u₃ ℓ₃ hne₃) :
    ∃ g : Polynomial O, g.Monic ∧ g ∣ f ∧
      g.natDegree = (F.e₁ * T.e₂ * ℓ₃) * (F.f₁ * T.f₂ * r₂.natDegree) ∧
      ((∀ g' ∈ monicFactors g, CBox1Side (T.levelDatum hπ) g') →
       (∀ g' ∈ monicFactors g, (F.f₁ * T.f₂ * r₂.natDegree) ∣ inertiaDegOf g') →
        typeOf g = ⟨{(F.e₁ * T.e₂ * ℓ₃, F.f₁ * T.f₂ * r₂.natDegree)}⟩ ∧ Irreducible g)

theorem level3_dead_at_mult2_three (mr ℓ₃ d₃ L μ₂ : ℕ) (hμ : μ₂ = 3) (hm : 2 ≤ mr)
    (hjump : 2 ≤ ℓ₃ * d₃) (hL : mr * (ℓ₃ * d₃) ≤ L) (hLμ : L ≤ μ₂) : False

theorem tower_termination_instance (J : ℕ) (a : Fin (J + 1) → ℕ) (ha0 : a 0 ≤ 6)
    (hfloor : ∀ j, 4 ≤ a j) (hdrop : ∀ j : Fin J, 2 * a j.succ ≤ a j.castSucc) : J = 0
```
(the α-refine sub-branch of (ii) is C.56/C.57's layer, entered by name; the HE7-8
finiteness placeholder stays E's, per the DEPENDS.)

**DEPENDS.** C.31 · C.32 · C.48 · C.61/C.62 (§7 — the iterated `(e,f)` read) · C.56/C.57 ·
GC-13 placeholder `EFF.HE7.<nn> — LEMMA HE7-8 [supplied-by: chapter E]`.

**PROOF (route).** (ii): instantiate §7's Tier-1 at the ITERATED frame — the level-2 datum
over the level-2 field is C.12's carrier; the composed `(e, f)` multiplies through landed
`ramIndexOf_mul_inertiaDegOf` + the §7 divisibility legs at both levels (GC-3's rank-form
chains). (iii): `omega` from C.31. (iv): C.32(b) + `EFF.HETOW.25`'s audit values.

**SIZE.** 3 × ~30 lines.

**SOURCE.** `EFF.HETOW.23` (the dictionary display `e = e₁e₂ℓ₂, f = f₁f₂·deg r₂`,
verbatim — "the note's deliverable … exactly the content of `[GENHN-HE(μ₂)]` at the tower
stage"); `EFF.HETOW.24` ((iii), incl. the consistency-check fence); `EFF.HETOW.25` ((iv) +
wrap-immunity certificate); `EFF.HETOW.22` (clause (i) — NOT re-transcribed: its content is
C.44–C.48; its 2026-08-10 supersession re-grounds it on HETOW-4, which is chapter D's
`(ABS-HE4)` — C-H11(ii)).

**TEETH.** 300/300 PARI at `μ₂ = 3` on both inner branches + P5 (“no member ever took the
LEVEL3 branch”, 300/300) → **executable regressions** retained; the `n = 12` audit
(`J ≤ 1`, `μ₂ = 3`) → **Lean theorem** (the termination instance) + §13 gate.

**ENVIRONMENT.** ENV-C3.

---

### NODE C.50 [def+lemma] [fresh]

**STATEMENT.** *The composed grid and the weight.* For a tower datum `T`: the composed slot
grid indexes `(j, a, b)` with `a < D′`, `b < e₂f₂`, `j < μ₂`; the **slot offset**
`w(a,b) := a * e₂ * h + b * u₂`; the **weight** of a monomial datum `(v, a, b, j)`:
`wt := e₁e₂·v + w(a,b) + j·E₂` (GENTOW1's weight — "wt = dv₂ of the evaluated monomial …
on the actual locus a LOWER bound with the j-graded part strict"). Lemma half: the SPLIT
`E₂ > dv₂(x^{D₂}) = D₂·e₂·h` (from the node floor `u₂ > e₂D′h` — the structural novelty
COR GENTOW-1.1 turns on), and the two term-family verifications
(`Φ′^{e₂f₂}`: `e₂f₂·u₂ = E₂`; lift term `t`: `e₂u₂(f₂−t) + e₂t·u₂ = E₂`).

**SIGNATURE.**
```lean
namespace Uniformity.Density.Tower

def slotOffset {F : KeyFrame O π} {H₀ hpin} (T : TowerDatum F H₀ hpin) (a b : ℕ) : ℕ :=
  a * (T.e₂ * F.h) + b * T.u₂

def gridWeight … (v a b j : ℕ) : ℕ :=
  (F.e₁ * T.e₂) * v + slotOffset T a b + j * T.E₂

theorem E₂_gt_xfloor {F : KeyFrame O π} {H₀ hpin} (T : TowerDatum F H₀ hpin) :
    T.D₂ * (T.e₂ * F.h) < T.E₂
```

**DEPENDS.** C.42.

**PROOF.** `E₂ = e₂f₂u₂ > e₂f₂·e₂D′h = D₂e₂h` from `T.hfloor`; `Nat.mul_lt_mul_left`.

**SIZE.** 16 lines.

**SOURCE.** `EFF.GENTOW1.07` (E₂ + the SPLIT, verbatim, with the five-family audit);
`EFF.GENTOW1.08` (the weight + its lower-bound scope note — transcribed in the docstring:
every "weight ≥ W" statement is a lower-bound statement on the locus).

**TEETH.** the five-family audit rows → §13 regression (two of the five are `q = 2`,
FAM-D is `q = 3` — GC-11 served). **ENVIRONMENT.** ENV-C5/C1.

---

### NODE C.51 [def] [fresh]

**STATEMENT.** *The tower-entry locus `𝒯` (FULL side only).* `towerLocus T n` — the set of
monic `f` of degree `n = μ₂·D₂` whose level-1 read exhibits the full inner side: `IsDvPure
F f T.u₂ T.e₂`, the polygon one side from `(0, μ₁·κ₂-cleared)` to `(μ₁, 0)`, and the side
residual equal to `ψ₂^{μ₂}` under C.44's translation (twist-coherent normalization = the
`dvResPoly`-read, whose coherence is exactly C.25's fixed convention). Every §6 GENTOW1
statement is scoped to `𝒯` — the FULL-side fence (`EFF.GENTOW1.14`'s own repetition at
`.46`); partial sides are §8's (GENTOW4).

**SIGNATURE** [signed: A-C.1 — elaborated in `leanspec/Leanspec/ChapC.lean`]. **A-C.1
determination (a caught defect, C-H12 class):** the residual EXPONENT is **`μ₂`** — the
committed display's `e₂f₂μ₂/e₂ = f₂μ₂` is the residual's DEGREE (`deg r̃ = f₂`, side degree
`f₂μ₂`), not its exponent; the two coincide exactly at `f₂ = 1`, the coincidence regime.
Fixed against C.26's degree lemma as the parenthetical mandated. Pins ∀-quantified (they
exist by purity):
```lean
namespace Uniformity.Density.Tower

def towerLocus {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀}
    (T : TowerDatum F H₀ hpin) (μ₂ : ℕ) : Set (Polynomial O) :=
  {f | f.Monic ∧ f.natDegree = μ₂ * T.D₂ ∧ IsDvPure F f T.u₂ T.e₂ ∧
    ∀ (hne : (dvSideSet F f T.u₂ T.e₂).Nonempty) (M₀ : ℕ)
      (hp : dvHgt F f (dvSideMin F f T.u₂ T.e₂ hne) = (M₀ : ℕ∞)),
      dvResPoly F H₀ hpin f T.u₂ T.e₂ hne M₀ hp = (towerLabel T) ^ μ₂}
```

**DEPENDS.** C.25 · C.29 · C.42 · C.44.

**PROOF.** definitional. **SIZE.** 16 lines.

**SOURCE.** `EFF.GENTOW1.14` (verbatim, incl. the FULL-side fence).

**TEETH.** P-4's level-1 entry gate (12 random in-budget members per family, REAL 180) →
regression retained. **ENVIRONMENT.** ENV-C1.

---

### NODE C.52 [theorem] [fresh]

**STATEMENT.** *GENTOW-1(a): the weight characterization / composed budget floors.* Monic
`f` of degree `n = μ₂D₂` lies on `𝒯` iff every composed slot of `g := f − Φ₂^{μ₂}` has
weight `≥ μ₂E₂ + 1`; equivalently, in `f = Φ₂^{μ₂} + Σ_{j<μ₂} C_j Φ₂^j` with
`C_j = Σ c_{j,a,b} x^a Φ′^b`:

```
v(c_{j,a,b}) ≥ ⌈((μ₂−j)·E₂ − w(a,b)) / (e₁e₂)⌉ + [pin],
[pin] = 1 iff e₁e₂ ∣ (μ₂−j)E₂ − w(a,b) ≥ 0
```

— "the r2-F2 level-1 display verbatim with `(D′h, ih, e₁) ↦ (E₂, w(a,b), e₁e₂)`". Proof
spine: Step 0 (weight monotonicity of the two carries — x-carry priced by the key's side,
`Φ′`-carry priced by `E₂`, both value-blind), Step 1 (`Φ₂^{μ₂}`'s own level-1 data via
C.47's test-key hood + graded multiplicativity), Step 2 (⟸ realizability with the
outer-grammar chain `u₂ + (μ₁−1)e₂D′h + 1 > μ₁e₂D′h`), Step 3 (⟹ + fibration prep).

**SIGNATURE** [signed: A-C.1 — elaborated in `leanspec/Leanspec/ChapC.lean`; the raw digit
coordinates are the x-coefficients of the two-key development (C.53's triangularity note
made the reading), so the budget clause reads `addVal` floors on
`(dev F.key (dev (composedKey T) f j) b).coeff a`].
```lean
namespace Uniformity.Density.Tower

def budgetFloor {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀}
    (T : TowerDatum F H₀ hpin) (μ₂ j a b : ℕ) : ℕ :=
  let w := slotOffset T a b
  let tgt := (μ₂ - j) * T.E₂ - w
  let d := F.e₁ * T.e₂
  if (μ₂ - j) * T.E₂ < w then 0
  else (tgt + d - 1) / d + (if tgt % d == 0 then 1 else 0)

theorem towerLocus_iff_budget {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀}
    (T : TowerDatum F H₀ hpin) (hπ : Irreducible π) (hh : 1 ≤ F.h)
    [Finite (ResidueField O)]
    {μ₂ : ℕ} (hμ₂ : 0 < μ₂) {f : Polynomial O} (hf : f.Monic)
    (hdeg : f.natDegree = μ₂ * T.D₂) :
    f ∈ towerLocus T μ₂
      ↔ ∀ j a b : ℕ, j < μ₂ → a < F.e₁ * F.f₁ → b < T.e₂ * T.f₂ →
          (budgetFloor T μ₂ j a b : ℕ∞)
            ≤ addVal O ((dev F.key (dev (composedKey T) f j) b).coeff a)
```

**⚠ HEAVY NODE — split-mandated: C.52 → 3** (Step 0; Steps 1–2; Step 3). Step 0 is
value-blind (wrap-immunity leg 1: “lift(c_t·η^{W(t)}) and lift(c_t) sit at the same
height”) — its sub-node carries NO gauge dependency and can fire before C.43.

**DEPENDS.** C.42 · C.43 · C.47 · C.50 · C.51 · B.02–B.06 (development bookkeeping at two
keys) · C.20 (class separation for the pin lattice).

**PROOF (route).** `EFF.GENTOW1.19`–`.22`'s four steps, each with its compile-time audit
transcribed as the sub-node's numeric check (`e₂u₂(f₂−t) + e₂tu₂ = E₂` exact and
`t`-independent; the outer chain reduces to the node floor).

**SIZE.** 3 × ~40 lines.

**SOURCE.** `EFF.GENTOW1.15` (the display, verbatim); `.19` (Step 0 + value-blind pin);
`.20` (Step 1 + the gauge-live failure record); `.21` (Step 2 + audit); `.22` (Step 3).

**TEETH.** the budget tables (`EFF.GENTOW1.10`: sixteen entries recomputed from this
display, zero discrepancies) → **executable regression** retained + §13 fires two rows at
`q = 2` AND `q = 3` (FAM-A5 and FAM-D); NEC 350 + T-MUTFLOOR ×5 (the `dv₂(x^{D₂})`-based
mutant floors machine-dead) → retained.

**ENVIRONMENT.** ENV-C1 (Steps 0–3 need no completeness: they are development arithmetic).

---

### NODE C.53 [theorem] [fresh]

**STATEMENT.** *GENTOW-1(b), TERMINAL (R2a clip): the fibration and the clipped free count.*
`f ↦ (c_{j,a,b})` is a triangular-unimodular digit bijection from `𝒯` onto the budget box
(digits free above floors; one `K₂`-digit per `dv₂`-height per coordinate); per window `N`
the free-`O`-digit count is **`Σ_{j,a,b} max(0, N − budgetFloor T j a b)`** — the CLIP; the
sealed unclipped `Σ (N − floor)` "is false whenever `N < floor` at some slot" and is DEAD.

**SIGNATURE** [signed: A-C.1 — elaborated in `leanspec/Leanspec/ChapC.lean`; the CLIP
`max(0, ·)` is ℕ-subtraction, definitionally; the fibration is signed as the class-count
identity over `Coeff`-classes].
```lean
namespace Uniformity.Density.Tower

noncomputable def towerFreeCount {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀}
    (T : TowerDatum F H₀ hpin) (μ₂ N : ℕ) : ℕ :=
  ∑ j ∈ Finset.range μ₂, ∑ a ∈ Finset.range (F.e₁ * F.f₁),
    ∑ b ∈ Finset.range (T.e₂ * T.f₂), (N - budgetFloor T μ₂ j a b)

theorem towerLocus_fibration {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀}
    (T : TowerDatum F H₀ hpin) (hπ : Irreducible π) (hh : 1 ≤ F.h)
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [Finite (ResidueField O)]
    (μ₂ N : ℕ) (hμ₂ : 0 < μ₂) :
    Nat.card {c : Coeff O (μ₂ * T.D₂) N //
        ∃ a : Fin (μ₂ * T.D₂) → O,
          proj O (μ₂ * T.D₂) N a = c ∧ monicPoly a ∈ towerLocus T μ₂}
      = residueCard O ^ towerFreeCount T μ₂ N
```

**DEPENDS.** C.52 (Step 3's triangularity: `c_{j,a,b}` = the coefficient at degree
`jD₂ + bD′ + a` plus an `Ô`-combination of strictly higher-degree coefficients — unipotent
in the x-degree filtration).

**PROOF.** unipotence ⟹ bijection (mod-`π^N` corollary at C.58(e)); the count is the
product structure of the budget box, clipped termwise.

**SIZE.** 30 lines.

**SOURCE.** `EFF.GENTOW1.16` (frozen (b) + the R2a replacement, both quoted — TERMINAL:
R2a, `.65`); `EFF.GENTOW1.22` (Step 3); `EFF.GENTOW1.26` (the count-law unlock remark,
whose UNCLIPPED exponent inherits the correction — §11 consumes the clipped form only).

**TEETH.** ROUNDTRIP 150 → retained; R2a's counter-instance (the clip active at small `N`)
+ its inactivity on the committed rows → **Lean theorem** (the clip is definitionally
active in the formula) + §13 regression.

**ENVIRONMENT.** ENV-C1.

---

### NODE C.54 [lemma] [fresh]

**STATEMENT.** *GENTOW-1(c)+(d): node floors and the field floor.* On `𝒯`:
(c) the composed pins obey `dv2Pin (T.levelDatum) Φ₂ f j ≥ ((μ₂−j)·E₂ + 1 : ℕ∞)` for
`j < μ₂`, with equality REALIZABLE at every `j` (the two-stage CRT solve: pick `b` with
`b·u₂ ≡ target (mod e₂)`, then `a` with `a·h ≡ … (mod e₁)` — two-step class separation,
gcd's from the frame data);
(d) the field floor in norm form: for every monic irreducible factor `g` of `f ∈ 𝒯`,
`(deg g) * T.E₂ < (F.e₁ * T.e₂) * addVal(norm(Φ₂ mod g))`-cleared — the closure-free
"`dv₂(Φ₂(x₀)) > E₂` at every root", C.27's carrier ("need not be an integer on `𝒯` — the
strict inequality IS the statement", transcribed as the cleared strict inequality).

**SIGNATURE** [signed: A-C.1 — elaborated in `leanspec/Leanspec/ChapC.lean`; three
declarations: the floor, the CRT realizability (`_sharp`), the norm-form field floor].
```lean
namespace Uniformity.Density.Tower

theorem towerLocus_node_floor {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀}
    (T : TowerDatum F H₀ hpin) (hπ : Irreducible π) (hh : 1 ≤ F.h)
    [Finite (ResidueField O)]
    {μ₂ : ℕ} {f : Polynomial O} (hf : f ∈ towerLocus T μ₂) {j : ℕ} (hj : j < μ₂) :
    (((μ₂ - j) * T.E₂ + 1 : ℕ) : ℕ∞) ≤ dv2Pin (T.levelDatum hπ) (composedKey T) f j

theorem towerLocus_node_floor_sharp {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀}
    (T : TowerDatum F H₀ hpin) (hπ : Irreducible π) (hh : 1 ≤ F.h)
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [Finite (ResidueField O)]
    {μ₂ : ℕ} (hμ₂ : 0 < μ₂) {j : ℕ} (hj : j < μ₂) :
    ∃ f ∈ towerLocus T μ₂,
      dv2Pin (T.levelDatum hπ) (composedKey T) f j = (((μ₂ - j) * T.E₂ + 1 : ℕ) : ℕ∞)

theorem towerLocus_field_floor {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀}
    (T : TowerDatum F H₀ hpin) (hπ : Irreducible π) (hh : 1 ≤ F.h)
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [Finite (ResidueField O)]
    {μ₂ : ℕ} {f : Polynomial O} (hf : f ∈ towerLocus T μ₂)
    {g : Polynomial O} (hg : g.Monic) (hirr : Irreducible g) (hdvd : g ∣ f) :
    ((g.natDegree * T.E₂ : ℕ) : ℕ∞)
      < (F.e₁ * T.e₂) • addVal O (Algebra.norm O (AdjoinRoot.mk g (composedKey T)))
```

**DEPENDS.** C.11 · C.27's carrier idiom · C.43 · C.46 · C.52 · H.51/H.52 (the CRT's
class-separation legs) · C.23 (the residue nonvanishing feeding (d)'s ψ₂-cancellation).

**PROOF (route).** (c): the floors are C.52's budget converted through the recursion
(C.11); realizability by the CRT display (`EFF.GENTOW1.23`, verbatim mechanism). (d): the
exact-height term census of `Φ₂(x₀)` — every term at `dv₂ = E₂` exactly — and the
height-`E₂` residue is `(unit)·ψ₂(η₂)`, which vanishes at the label (C.44's root data);
ultrametric strictness. **The (d) leg is VALUE-LIVE at the gauge seam** (at naive lifts the
term-`t` residue carries `η^{−W(t)}` and the sum is NOT `ψ₂(η₂)` — the corpus's 20/20
machine refutation): the proof MUST route through C.46's corrected residues; a proof
attempt that succeeds without C.46 is a defect signal (it proved the wrong statement).

**SIZE.** 40 lines. **Split candidate:** (c) / (d).

**SOURCE.** `EFF.GENTOW1.17` ((c) + P-5 sharpness: the five NODE-EQ anchors hit
`μ₂E₂ + 1` exactly); `.18` ((d) + the non-integrality guard); `.23` (Step 4, the CRT);
`.24` (Step 5 + the `[GT1-r1]` VALUE-LIVE bracket with the 20/20 GAUGE-NODE evidence).

**TEETH.** P-5 (five NODE-EQ anchors, `[21,11]/[29,15]/[13,7]/[43,22]/[13,7]` all
recomputed) → **executable regression** + two §13 rows; T-BELOWNODE (a digit AT weight
`μ₂E₂` breaks the entry endpoint) → retained; GAUGE-NODE 20/20 → retained as the (d)-leg's
decorrelated guard.

**ENVIRONMENT.** ENV-C3 ((d) counts residues).

---

### NODE C.55 [theorem] [fresh]

**STATEMENT.** *COROLLARY GENTOW-1.1 — the depth-3 node floor ((6)(β) DISCHARGED, sharper
constant).* Every side of the composed polygon `(j, dv2Pin …)` of an `f ∈ 𝒯` has
`dv₂`-slope `κ₃ > E₂ > dv₂(x^{D₂}) = D₂e₂h`; cleared: every side `(u₃, ℓ₃)` of the
`dv2Supp`-argmin with nonempty side set has `ℓ₃ * T.E₂ < u₃`. Proof: pins
`p_j ≥ (μ₂−j)E₂ + 1` with right endpoint `(μ₂, 0)` give minimal side slope
`≥ E₂ + 1/μ₂ > E₂` (cleared: `μ₂·u₃ ≥ μ₂·ℓ₃·E₂ + ℓ₃`); convexity-free in the argmin
representation (the argmin's two-point slopes are all `> E₂` directly from the pin bounds);
`E₂ > D₂e₂h` is C.50. **This is the `κ₃ > e₂f₂u₂` hypothesis GENTOW5's (β)-floor fence
routes here** (`EFF-GENTOW5` FP-4 fence 2: GENTOW5 "cites it AS IN-FLIGHT and does not
re-derive it") — the supply lands HERE, and §9's third-stage nodes consume THIS node by ID.

**SIGNATURE** [re-signed: A-C.1 — the D3-class unbound `μ₂` bound, `levelDatum`'s `hπ`
threaded, `dv2SideSet` now NODE C.38a's (the RE-PLAN executed at §5)].
```lean
namespace Uniformity.Density.Tower

theorem towerLocus_depth3_floor {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀}
    (T : TowerDatum F H₀ hpin) (hπ : Irreducible π) {μ₂ : ℕ}
    {f : Polynomial O} (hf : f ∈ towerLocus T μ₂) {u₃ ℓ₃ : ℕ} (hℓ₃ : 0 < ℓ₃)
    (hcop : Nat.Coprime u₃ ℓ₃)
    (hne : (dv2SideSet (T.levelDatum hπ) (composedKey T) f u₃ ℓ₃).Nonempty) :
    ℓ₃ * T.E₂ < u₃
```

**DEPENDS.** C.11 · C.50 · C.54(c).

**PROOF.** the pin arithmetic above; `omega` after clearing.

**SIZE.** 20 lines.

**SOURCE.** `EFF.GENTOW1.25` (verbatim, incl. the discharge sentence: “Item (6)(beta) is
hereby discharged INTO item (1); item (6)(alpha) … is untouched and keeps the box” — §9
carries (6)(α) at exact scope); the audit (`κ₃ = 21/2 > 10 > 8` at FAM-A5).

**TEETH.** the FAM-A5 witness values → **Lean theorem** instance + §13 regression.

**ENVIRONMENT.** ENV-C1.

---

### NODE C.56a [def] [fresh]

**STATEMENT.** *The base-resolved K₂-digit lift (the `.62` TERMINAL display) — split out
of C.56 per the A-7 SCC repair.* `k2DigitLift T s m` for `s ∈ K₂`, at heights `m > E₂`:

```
lift(s; m) := Σ_{r,t} d_{r,t} · M_{r,t}(m),   M_{r,t}(m) := n̂₂(m − Δ(r,t)) · x^{e₁r} · Φ′^{e₂t},
Δ(r,t) := e₁e₂h·r + e₂u₂·t
```

(`n̂₂(m) := π^{a₀}x^iΦ′^b`, `i < e₁, b < e₂`, `e₁e₂a₀ + ie₂h + bu₂ = m`, the `(i,b)`-pair
unique per class mod `e₁e₂`, `a₀ ≥ 0` at `m > E₂` — the audited inequality
`E₂ ≥ (e₁−1)e₂h + (e₂−1)u₂ + 1`); `d_{r,t}` the inverse-twisted `K`-expansion digits of
`s` in the coherent normalization; `deg lift < D₂` always (the frozen sentence STANDS).
The frozen fixed-base display is DEAD (its compensating `π`-exponent goes non-integer at
seam-live heights — the FR-A machine counter-instance `11/2 ∉ ℤ`).

**SIGNATURE** [signed: A-C.1 — elaborated in `leanspec/Leanspec/ChapC.lean`; real body: the
two-step `n̂₂`-solve `n2Exp` (C.15/C.16's pattern at `(u₂, e₂)` composed with the frame
solve) + the canonical-representative digit reads (`k2Coord` over the `β`-basis, C.14a's
`stageCoord` over the `η`-basis); the inverse-twist normalization is PINNED by the
exact-height/`deg < D₂` companions at fleet time — determination recorded].
```lean
namespace Uniformity.Density.Tower

noncomputable def k2Coord {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀}
    (T : TowerDatum F H₀ hpin) (s : AdjoinRoot (towerLabel T)) (t : ℕ) :
    F.stageField H₀ hpin :=
  (((AdjoinRoot.mk_surjective s).choose).coeff t)

noncomputable def n2Exp {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀}
    (T : TowerDatum F H₀ hpin) (m : ℕ) : ℕ × ℕ × ℕ :=
  let b := towerSolve T.u₂ T.e₂ m
  let m' := (m - b * T.u₂) / T.e₂
  ((m' - F.slotIdx m' * F.h) / F.e₁, F.slotIdx m', b)

noncomputable def k2DigitLift {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀}
    (T : TowerDatum F H₀ hpin) (s : AdjoinRoot (towerLabel T)) (m : ℕ) : Polynomial O :=
  ∑ r ∈ Finset.range F.f₁, ∑ t ∈ Finset.range T.f₂,
    Polynomial.C
        (resLift (F.stageCoord H₀ hpin (k2Coord T s t) r)
          * π ^ (n2Exp T (m - (F.e₁ * T.e₂ * F.h * r + T.e₂ * T.u₂ * t))).1)
      * Polynomial.X
          ^ ((n2Exp T (m - (F.e₁ * T.e₂ * F.h * r + T.e₂ * T.u₂ * t))).2.1 + F.e₁ * r)
      * F.key ^ ((n2Exp T (m - (F.e₁ * T.e₂ * F.h * r + T.e₂ * T.u₂ * t))).2.2 + T.e₂ * t)
```

**DEPENDS.** C.15/C.16 · C.28 · C.42 · C.44 · C.50 · H.51/H.52 (the two-step class
separation) · H.54–H.56 (the base-level digit realization, per C-H5).

**PROOF.** definitional + the range/`a₀ ≥ 0` arithmetic (`omega` from `T.hfloor`).

**SIZE.** 26 lines.

**SOURCE.** `EFF.GENTOW1.27` (the setting + the `.62` TERMINAL lift display, verbatim;
the `a₀ ≥ 0` audit); `EFF.GENTOW1.53`-region (the S3 correction's provenance).

**TEETH.** the FR-A verification (`n̂₂(14−3)·Φ₁ = 3⁵xΦ₁`; fixed-base non-existence) →
**executable regression** + §13 row (shared with C.84's).

**ENVIRONMENT.** ENV-C1.

---

### NODE C.56 [theorem] [fresh]

**STATEMENT.** *GENTOW-2(i)+(ii): the composed refine transfer.* For a composed stage-α
event (one side of integer `dv₂`-slope `λ > E₂` with residual `(T − s)^{μ₂}` over `K₂`,
`s ∈ K₂^×`) set `Φ₂⁺ := Φ₂ − k2DigitLift T s λ` with the **base-resolved K₂-digit lift**
of C.56a (the `.62` TERMINAL display, split out per A-7). Then:
(i) `Φ₂⁺` keeps every key invariant — monic of degree `D₂`; level-1 development one-sided
of slope `κ₂` with residual `ψ₂` and side digits byte-unchanged (the perturbation's slots
sit at weight `λ > E₂`); x-polygon one side (the audited chain
`λ − (e₂f₂−1)(u₂−e₂D′h) > dv₂(x^{D₂})`); hence `IsTestKey`-hood and the carrier
`(e₁e₂, f₁f₂)` rerun verbatim at `Φ₂⁺` (carrier through §7, conditionality inherited);
(ii) THE KILLS: in the `Φ₂⁺`-development of `f` the `μ₂` event pins die:
`dv2Pin … Φ₂⁺ f j > ((μ₂−j)·λ : ℕ∞)` for every `j < μ₂`. At `μ₂ = 2` the proof is
pointwise-elementary (actual re-division — the battery's 8 rows); at general `μ₂` layer 1
consumes the composed graded frame: **DEPENDS on §9's C.85 (GENTOW5's S1.5 graded frame —
the retirement of GENTOW-BOX-1)**, and fires only after it.

**SIGNATURE** [signed: A-C.1 — elaborated in `leanspec/Leanspec/ChapC.lean`; two public
theorems, **split-mandated C.56 → 2**; the α-event is carried by the C.38a residual read at
the integer side `(lam, 1)` (⚠ Lean naming: the slope letter is `lam` — `λ` is reserved)].
```lean
namespace Uniformity.Density.Tower

theorem refine_invariants {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀}
    (T : TowerDatum F H₀ hpin) (hπ : Irreducible π) (hh : 1 ≤ F.h)
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [Finite (ResidueField O)]
    {μ₂ : ℕ} {f : Polynomial O} (hf : f ∈ towerLocus T μ₂)
    {lam : ℕ} (hslope : T.E₂ < lam) {s : AdjoinRoot (towerLabel T)} (hs : s ≠ 0)
    (hne : (dv2SideSet (T.levelDatum hπ) (composedKey T) f lam 1).Nonempty)
    (hres : dv2ResPoly (T.levelDatum hπ) (composedKey T) f lam 1 hne
      = (Polynomial.X - Polynomial.C s) ^ μ₂) :
    (composedKey T - k2DigitLift T s lam).Monic ∧
    (composedKey T - k2DigitLift T s lam).natDegree = T.D₂ ∧
    IsTestKey (T.levelDatum hπ) (composedKey T - k2DigitLift T s lam)

theorem refine_kills {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀}
    (T : TowerDatum F H₀ hpin) (hπ : Irreducible π) (hh : 1 ≤ F.h)
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [Finite (ResidueField O)]
    {μ₂ : ℕ} {f : Polynomial O} (hf : f ∈ towerLocus T μ₂)
    {lam : ℕ} (hslope : T.E₂ < lam) {s : AdjoinRoot (towerLabel T)} (hs : s ≠ 0)
    (hne : (dv2SideSet (T.levelDatum hπ) (composedKey T) f lam 1).Nonempty)
    (hres : dv2ResPoly (T.levelDatum hπ) (composedKey T) f lam 1 hne
      = (Polynomial.X - Polynomial.C s) ^ μ₂)
    {j : ℕ} (hj : j < μ₂) :
    (((μ₂ - j) * lam : ℕ) : ℕ∞)
      < dv2Pin (T.levelDatum hπ) (composedKey T - k2DigitLift T s lam) f j
```

**DEPENDS.** C.28 (cocycle units enter the residual assembly IDENTICALLY — layer 1's
mechanism) · C.43 · C.47 · C.50 · C.52 · C.56a (the lift) · C.85 (§9, general-`μ₂` leg
only) · H.51/H.52.

**PROOF (route).** (i): `EFF.GENTOW1.32`'s strictly-above + x-side chain (audited exact).
(ii): layers 1–2 of `.33` — the graded substitution identity `(T−s)^{μ₂} ↦ T^{μ₂}`
(binomial-free, both characteristics) + Step-0 carry monotonicity for two carries.

**SIZE.** 2 × ~40 lines.

**SOURCE.** `EFF.GENTOW1.28`/.29 (the clauses); `.32`/.33 (proofs + the layer-1 honesty
note verbatim); `.27` (the setting + the `.62` TERMINAL lift display — the frozen
fixed-base display is DEAD; “deg lift < D₂ always” STANDS); `.68` (F-4: “constant term
untouched” means the x-side DIGIT — the wording-rider carried in (i)'s docstring).

**TEETH.** P-6/`GP-EF` 8 (refined keys keep the carrier, PARI) + REFINE 40 +
T-REFWRONG ×8 (wrong-height/wrong-residue/wrong-flavor normalizers all leave the pin
alive — a three-way mutation tooth) → **executable regressions** retained; §13 fires one
refine row at each prime (A5-R1 at `q = 2`, D-R1 at `q = 3`).

**ENVIRONMENT.** ENV-C1 ((i)); ENV-C3 ((ii)'s residue legs).

---

### NODE C.57 [theorem] [fresh]

**STATEMENT.** *GENTOW-2(iii)+(iv), TERMINAL (R2b): the refine bijection and the
transported event data.* (iii) `(digits at Φ₂) ↦ (digits at Φ₂⁺)` is triangular (new digit
= old digit + strictly-lower-height data) and bijects **`DOM_N` onto `COD_N`** — R2b's
completed inventory: the two window boxes with the SAME clipped cardinality
(`Σ max(0, N − floor)` on both sides), onto = injection between finite sets of equal
cardinality, then the inverse-limit passage to full strings; `|K₂| − 1` letter choices of
`s` per step. **A consumer cites R2b's sets, never the frozen "onto by cardinality"
sentence** (which defined neither set). (iv) For a deeper member `g` in the `Φ₂⁺`-frame,
the OLD-key read exhibits exactly the α-event: `dv2Pin … Φ₂ g j = ((μ₂−j)·λ : ℕ∞)` with
residue `binom(μ₂,j)·(−s̄)^{μ₂−j}` (coherent normalization, wrap units included) at every
`j` with `¬ p ∣ binom(μ₂,j)`, other coordinates strictly above — at `μ₂ = 2, q = 2` the
`j = 1` pin vanishes (`2s = 0`) and the event is carried by `p₀ = 2λ` alone; at `q = 3`
both pins show. Heights transport by `dv₂ = e₂·dv`; residues by the `η₂`-dictionary.

**SIGNATURE** [signed: A-C.1 — elaborated in `leanspec/Leanspec/ChapC.lean`; `DOM_N`/`COD_N`
land as the named strata `refineDom`/`refineCod` (R2b's completed inventory), the bijection
as the `Nat.card` identity; the triangularity/inverse-limit legs are the fleet's proof
content. (iv)'s residue clause reads through C.38a's coherent `dv2Res`; the char split
enters as `¬ ringChar (ResidueField O) ∣ binom(μ₂, j)`].
```lean
namespace Uniformity.Density.Tower

def refineDom {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀}
    (T : TowerDatum F H₀ hpin) (hπ : Irreducible π) (μ₂ N lam : ℕ)
    (s : AdjoinRoot (towerLabel T)) : Set (Coeff O (μ₂ * T.D₂) N) :=
  {c | ∃ a : Fin (μ₂ * T.D₂) → O, proj O (μ₂ * T.D₂) N a = c ∧
    monicPoly a ∈ towerLocus T μ₂ ∧
    ∃ hne : (dv2SideSet (T.levelDatum hπ) (composedKey T) (monicPoly a) lam 1).Nonempty,
      dv2ResPoly (T.levelDatum hπ) (composedKey T) (monicPoly a) lam 1 hne
        = (Polynomial.X - Polynomial.C s) ^ μ₂}

def refineCod {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀}
    (T : TowerDatum F H₀ hpin) (hπ : Irreducible π) (μ₂ N lam : ℕ)
    (s : AdjoinRoot (towerLabel T)) : Set (Coeff O (μ₂ * T.D₂) N) :=
  {c | ∃ a : Fin (μ₂ * T.D₂) → O, proj O (μ₂ * T.D₂) N a = c ∧
    monicPoly a ∈ towerLocus T μ₂ ∧
    ∀ j < μ₂, (((μ₂ - j) * lam : ℕ) : ℕ∞)
      < dv2Pin (T.levelDatum hπ) (composedKey T - k2DigitLift T s lam) (monicPoly a) j}

theorem refine_bijection {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀}
    (T : TowerDatum F H₀ hpin) (hπ : Irreducible π) (hh : 1 ≤ F.h)
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [Finite (ResidueField O)]
    (μ₂ N lam : ℕ) (hμ₂ : 0 < μ₂) (hslope : T.E₂ < lam)
    (s : AdjoinRoot (towerLabel T)) (hs : s ≠ 0) :
    Nat.card (refineDom T hπ μ₂ N lam s) = Nat.card (refineCod T hπ μ₂ N lam s)

theorem refine_transported_event {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀}
    (T : TowerDatum F H₀ hpin) (hπ : Irreducible π) (hh : 1 ≤ F.h)
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [Finite (ResidueField O)]
    {μ₂ lam : ℕ} (hslope : T.E₂ < lam) {s : AdjoinRoot (towerLabel T)} (hs : s ≠ 0)
    {g : Polynomial O} (hg : g ∈ towerLocus T μ₂)
    (hkills : ∀ j < μ₂, (((μ₂ - j) * lam : ℕ) : ℕ∞)
      < dv2Pin (T.levelDatum hπ) (composedKey T - k2DigitLift T s lam) g j)
    {j : ℕ} (hj : j < μ₂)
    (hbin : ¬ (ringChar (ResidueField O) ∣ Nat.choose μ₂ j)) :
    dv2Pin (T.levelDatum hπ) (composedKey T) g j = (((μ₂ - j) * lam : ℕ) : ℕ∞) ∧
    dv2Res (T.levelDatum hπ) (dev (composedKey T) g j)
      = (Nat.choose μ₂ j : AdjoinRoot (towerLabel T)) * (- s) ^ (μ₂ - j)
```

**DEPENDS.** C.53 · C.56 · landed `Finset.card` bijection lemmas; (iv): binomial expansion
+ C.11's height comparison (`(μ₂−i)λ + (i−j)λ = (μ₂−j)λ` — the audited cancellation).

**PROOF (route).** (iii): triangularity from C.56(ii)'s layers; the counting lemma with the
clipped exponent on BOTH sides; injectivity; finite-set onto; inverse limit (the corpus's
own four-move R2b structure). (iv): `EFF.GENTOW1.34`'s expansion, verbatim route.

**SIZE.** 2 × ~40 lines.

**SOURCE.** `EFF.GENTOW1.30` (frozen (iii) + R2b, TERMINAL — `.66`); `.31`/(iv) verbatim
(char-sensitive display); `.33` layer 3 (the sealed gap, quoted: “onto by cardinality with
neither set defined”); `.34` (the (iv) proof + audit).

**TEETH.** R2b's enumeration contact (A5-R1 at `N = 4`: 16 DOM members → 16 distinct
images covering COD exactly) → **executable regression** + §13 row; the eight-row
`p₀ = 2λ` + `q = 2/q = 3` pin-split audit (`EFF.GENTOW1.12`) → **Lean theorem** ((iv)'s
instances) + regression. The char split is a GC-11 exhibit: five `q = 2` rows and two
`q = 3` rows DISAGREE on the `j = 1` pin — the §13 gate fires one of each.

**ENVIRONMENT.** ENV-C3.

---

### NODE C.58 [theorem] [fresh]

**STATEMENT.** *GENTOW-5, TERMINAL (R2c three bands + R2a re-scope): the composed window
ledger.* On `𝒯`, per window `N`:
**(a) THREE BANDS** (the sealed "LIFT-STABLE iff `< e₁e₂N`" is DEAD — refuted by its own
first-band sentence): a computed `dv₂`-value `m` is — BAND 1 (`m < e₁e₂N`): stable across
lifts; BAND 2 (`m = e₁e₂N`, at `f₁f₂ ≥ 2`): VALUE-exact for every lift while the full
`K₂`-residue is NOT determined (the unread digit TIES at equality — R2c's strict-`>`
re-scope; readable nonzero parts survive by tower-basis independence); BAND 3
(`m > e₁e₂N`): unstable (the undercut).
**(b) ragged strings:** the class-`(a,b)` slot string of `C_j` ends at
`e₁e₂(N−1) + w(a,b)`, ragged across the `e₁e₂` height classes; within one `dv₂`-height the
`K₂`-digit's `f₁f₂` component `O`-digits die at different lift depths (the within-digit
band, NEW at level 2 for `e₂ ≥ 2`).
**(c) consultation:** every digit consulted by a readable event sits strictly inside its
class string: `m < e₁e₂N ∧ m ≡ w(a,b) (mod e₁e₂) ⟹ m ≤ e₁e₂(N−1) + w(a,b)` (one
congruence).
**(d) upward carries:** along composed refine chains every update determines new digits at
height `d` from old digits at heights `≤ d` — deep composed histories never consult the
ragged band.
**(e) capped-window content identity:** the composed digit map induces a bijection
`(f mod π^N, monic deg n) ↔ (composed digits mod π^N)`; every decided composed read at
heights `< e₁e₂N` is a function of the window data; the budget/count display is exact per
window **at the CLIPPED display** (R2a's consumer re-scope, verbatim: "exact as sealed for
`N ≥ max floor`").

**SIGNATURE** [signed: A-C.1 AT THE CONSUMED CORE — BAND 1's stability (`window_band1`) and
the consultation congruence (`window_consultation`); clauses (b)/(d)/(e) and BAND 2/3 are
BOOKED fleet-time companions riding C.53's unipotence + H.53 (recorded here; split-mandated
C.58 → 3 stands, the three files being (a)-core / (b)+(c) / (d)+(e))]. (a)'s BAND 2 consumes
H.53's independence at the `(K, K₂)` tower basis (`{η^r η₂^t}` — GENHN-2″'s mechanism,
instantiated through C.12/C.19).
```lean
namespace Uniformity.Density.Tower

theorem window_band1 {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀}
    (T : TowerDatum F H₀ hpin) (hπ : Irreducible π) (hh : 1 ≤ F.h)
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [Finite (ResidueField O)]
    {μ₂ N : ℕ} {a a' : Fin (μ₂ * T.D₂) → O}
    (hc : proj O (μ₂ * T.D₂) N a = proj O (μ₂ * T.D₂) N a')
    (ha : monicPoly a ∈ towerLocus T μ₂) {j m : ℕ} (hj : j < μ₂)
    (hm : dv2Pin (T.levelDatum hπ) (composedKey T) (monicPoly a) j = (m : ℕ∞))
    (hband : m < F.e₁ * T.e₂ * N) :
    dv2Pin (T.levelDatum hπ) (composedKey T) (monicPoly a') j = (m : ℕ∞) ∧
    dv2Res (T.levelDatum hπ) (dev (composedKey T) (monicPoly a') j)
      = dv2Res (T.levelDatum hπ) (dev (composedKey T) (monicPoly a) j)

theorem window_consultation (d N m w : ℕ) (hd : 0 < d) (hw : w < d) (hm : m < d * N)
    (hcong : m % d = w % d) : m ≤ d * (N - 1) + w
```

**DEPENDS.** C.11 · C.12 · C.19 · C.50 · C.52 · C.53 · C.56(d-layer) · H.53.

**PROOF (route).** `EFF.GENTOW1.40`'s five clauses, each one or two audited lines; (a)'s
undercut instance + first-band independence; (c) is `omega`; (e) is C.53's unipotence
mod `π^N`.

**SIZE.** 3 × ~35 lines.

**SOURCE.** `EFF.GENTOW1.35` (frozen (a) + R2c TERMINAL, `.67`); `.36`–`.39` ((b)–(e), with
(e)'s R2a scope-pin quoted); `.40` (the proof).

**TEETH.** the FAM-B per-band machine contact (BAND 2 `dv₂ = 8`; BAND 3 `14 vs 11` across
two lifts; `TOTAL violations 0`) → **executable regression** retained + §13 fires the
BAND-2 row at both primes (FAM-B is `q = 2`; FAM-D is the `q = 3` twin); STRINGS 22 +
WINDOW 35 + ROUNDTRIP 150 + T-UNDERCUT ×2 → retained.

**ENVIRONMENT.** ENV-C3.

---

---

## 7. §7 — CLASS SIZE AND BLOCK LENGTH (DECISION C-D1 EXECUTED)

> **Design note.** This section is DECISION C-D1's cash value. Tier 1 (closure-free
> theorems): C.59 (the ramified leg), C.60 (the `C-BOX-1` carrier + its vacuity perimeter),
> C.61 (the per-factor singleton `typeOf` — the sandwich), C.63 (the separable-side
> assembly = `THEOREM HE6.A`'s display recast). Tier 2 (read form): C.64/C.65
> (`|S_{λ,r}| = D″·μ₂`, computable from `f`). Tier 3 (gate-(b) cite): C.66 ([cite:FGMN])
> feeding C.67 (the mixed-side tie `μ₂*(r) = m_r` — `LEMMA GENTOW-6.1`, which CLOSES
> `GENTOW4-BOX-1`/`HYP.144`, cite-conditionally). C.69 bundles the three tiers as the named
> supply statement downstream chapters cite; C.70 closes the side-length accounting. §5's
> C.40 and §6's C.48/C.49 fire after C.59–C.63 (forward refs recorded there). **Nothing in
> this section mentions a root, an orbit, a resultant over `K̄₀`, or an embedding** — the
> corpus's `EFF.HE6.14`-family test machinery at fractional heights and the Galois
> equivariance `EFF.HE6.31` have NO nodes (C-H2).

### NODE C.59 [lemma] [fresh]

**STATEMENT.** *The ramified divisibility leg, closure-free at every parameter.* Let `g` be
monic irreducible over `O` with `HasLabel L g`-grade side data (one `dv`-side `(u, ℓ)`, the
x-polygon one-sided of slope `h/e₁` — purity heredity from C.33/C.34's dissections). Then
`(F.e₁ * L.ℓ) ∣ ramIndexOf g`. Route: the leaf's cleared value semigroup contains the three
values `dv₂(π) = ℓe₁`, `dv₂(x-datum) = ℓh`, `dv₂(Φ′-datum) = u` (each read through
`addVal ∘ norm` over `AdjoinRoot g` — C.27's carrier at `C ∈ {π·1, X, F.key}`), and
`gcd(ℓe₁, ℓh, u) = gcd(ℓ·gcd(e₁,h), u) = gcd(ℓ, u) = 1` (frame + datum coprimalities) — so
the value group of the leaf contains `1/(e₁ℓ)`-cleared, i.e. `e₁ℓ ∣ e'`. This is B.54/B.57's
mechanism one level up (landed `norm_adjoinRoot_root`, `norm_algebraMap_rootBasis`,
`natDegree_dvd_addVal_norm`; the `(e, f)` engine stays polynomial-level per GC-3 — no
silent identification with the ideal-theoretic pair).

**SIGNATURE.**
```lean
namespace Uniformity.Density.Tower

theorem ramLeg_dvd {F : KeyFrame O π} {H₀ hpin} (L : LevelDatum F H₀ hpin)
    (hπ : Irreducible π) [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    {g : Polynomial O} (hg : g.Monic) (hirr : Irreducible g) (hlab : HasLabel L g)
    (hx : IsPure Polynomial.X g F.h F.e₁) :
    (F.e₁ * L.ℓ) ∣ ramIndexOf g
```

**DEPENDS.** C.27 (`slot2_exact` at the three test elements) · C.29 · B.49–B.54 (the
level-1 mechanism, consumed as templates and as the `e₁`-leg at the x-polygon) · landed
`ramIndexOf`, `inertiaDegOf_dvd`, `ramIndexOf_mul_inertiaDegOf`.

**PROOF.**
1. Value reads: `e₁ℓ·addVal(norm(π)) = deg g·(e₁ℓ)` trivially; for `X` and `F.key`, C.27
   with `C := X` (`dv2Hgt = ℓh` — the slot formula at the linear coefficient) and
   `C := F.key` (`dv2Hgt = u` — the label's defining side value).
2. Landed engine: `inertiaDegOf g` divides each `addVal(norm ·)`-datum's cofactor; Bezout
   over the three cleared values with `gcd = 1` (frame `hcop` + datum `hcop` + `hκ`) forces
   the value-group index `e' = ramIndexOf g` to absorb `e₁ℓ` (the divisibility assembles
   exactly as B.54's proof does with two elements; three here).
3. `Nat.Coprime` bookkeeping: `gcd(ℓe₁, ℓh) = ℓ` (frame coprimality), `gcd(ℓ, u) = 1`
   (datum coprimality) — `omega`/`Nat.Coprime` lemmas.

**SIZE.** 40 lines. **Split candidate:** step 1's three reads / step 2's assembly.

**SOURCE.** `EFF.HE6.18`'s conclusion clause (`e = e₁ℓ` — the leg this proves half of);
`EFF.HE6R1.16`'s sandwich (`e ≥ e₁ℓ`); CHAP-B §0.4 + B.54 (the route, one level down);
DECISION C-D1 Tier 1.

**TEETH.** the σ instances (`{(4,1),(4,1)}` at `(2,1)`-genre, `{(2,2),(2,2)}` at `(1,2)` —
`EFF.HE6.20`(3)) → §13 gate rows at both primes.

**ENVIRONMENT.** ENV-C2.

---

### NODE C.60 [def+lemma] [fresh]

**STATEMENT.** *`C-BOX-1` — the level-2 residue-leg hypothesis, named and fenced.*
`CBox1Side L g : Prop := (F.f₁ * L.r.natDegree) ∣ inertiaDegOf g` — the residue-direction
divisibility the sandwich needs, **the exact analogue of CHAP-B's `B-BOX-1` one level up**
(the corpus proves it by realizing the residual root in the leaf's residue field —
`EFF.HE6.29`'s root label, a `K̄₀`-side statement with no closure-free proof in this
chapter). Lemma clauses: (i) **vacuity perimeter:** `CBox1Side L g` holds unconditionally
when `F.f₁ * L.r.natDegree = 1` (`one_dvd`); (ii) the UPPER bound is unconditional:
`inertiaDegOf g ∣ F.f₁ * L.r.natDegree * (…)`-family bounds come free from the degree
identity and C.59 (recorded as a companion, mirroring B.54's upper half); (iii) the repair
route is B-BOX-1's, inherited: B.56/B.62's spectral-norm layer (multiplicative/ℝ-valued —
the same named RISK), applied at the iterated leaf. **No node assumes `CBox1Side` silently:
it is an explicit hypothesis on C.61/C.62/C.63/C.69 and on §5's C.40, and nowhere else.**
A fleet agent needing it discharged at `f₁·d_r ≥ 2` returns `BLOCKED: C-BOX-1 (B-BOX-1
analogue; repair route B.56/B.62)`.

**SIGNATURE.**
```lean
namespace Uniformity.Density.Tower

/-- `C-BOX-1`: the level-2 residue-degree lower bound, carried as an explicit hypothesis
(DECISION C-D1; the `B-BOX-1` analogue — CHAP-B H-7's shape one level up). -/
def CBox1Side {F : KeyFrame O π} {H₀ hpin} (L : LevelDatum F H₀ hpin)
    (g : Polynomial O) : Prop :=
  (F.f₁ * L.r.natDegree) ∣ inertiaDegOf g

theorem cbox1_of_deg_one {F : KeyFrame O π} {H₀ hpin} (L : LevelDatum F H₀ hpin)
    (g : Polynomial O) (h1 : F.f₁ * L.r.natDegree = 1) : CBox1Side L g
```

**DEPENDS.** C.09 · landed `inertiaDegOf` · B.55/B.56/B.62 (the level-1 box + repair route,
cited as the inheritance).

**PROOF.** (i) `h1 ▸ one_dvd _`. (ii)/(iii) are records + companions.

**SIZE.** 16 lines.

**SOURCE.** CHAP-B H-7 (`B-BOX-1`, verbatim shape: “stated as an explicit hypothesis on
B.55/B.58 and not assumed anywhere else”); `EFF.HE6.29` (`HE6-ROOT-LABEL` — the corpus's
closure-side supplier, NOT transcribed, per C-D1); GC-5's RE-PLAN discipline (if a genre
schema needs this as a field, that is the FALSIFIER protocol of C-D1, not a silent add).

**TEETH.** signed non-applicability (a named hypothesis; its DISCHARGE evidence is the
batteries' PARI σ agreement, retained as regressions at §13).

**ENVIRONMENT.** ENV-C3.

---

### NODE C.61 [theorem] [fresh]

**STATEMENT.** *TIER 1 — the per-factor singleton `typeOf` (the sandwich).* Let `g` be
monic with `HasLabel L g` at multiplicity `m = 1` (so `deg g = L.keyDeg₂ = (e₁ℓ)(f₁d_r)`,
via C.26's degree law + C.33's degree clause), over the complete bundle, with
`hbox : CBox1Side L g'` for every monic irreducible factor `g'` of `g` (each inherits the
label by C.34's uniqueness). Then

```
typeOf g = ⟨{(F.e₁ * L.ℓ, F.f₁ * L.r.natDegree)}⟩
```

and `g` is irreducible over `O`. Proof shape = CHAP-B §0.4's four lines, one level up (=
`EFF.HE6R1.16`'s own sandwich): for every `(e', f') ∈ (typeOf g).data`, `e₁ℓ ∣ e'` (C.59)
and `f₁d_r ∣ f'` (`hbox`), so `e'f' ≥ (e₁ℓ)(f₁d_r) = deg g`; landed `typeOf_degree` says
`Σ e'f' = deg g` and `efPair_pos_of_mem` bounds each below — a multiset of entries each
`≥ deg g` summing to `deg g` is the singleton.

**SIGNATURE** [signed: A-C.1 — elaborated in `leanspec/Leanspec/ChapC.lean`]. **The `hm1`
design hole RESOLVED without reshaping C.29's committed `HasLabel`:** the multiplicity-1
clause is signed as the EXACT-RESIDUAL hypothesis (`dvResPoly … = L.r`, ∀-pinned) — with
`hlab` it forces `HasLabel`'s inner `m = 1` and `deg g = keyDeg₂` through C.26's degree law,
which is precisely the reading the node's own PROOF consumes. D11 cured in-statement.
```lean
namespace Uniformity.Density.Tower

theorem tier1_typeOf {F : KeyFrame O π} {H₀ hpin} (L : LevelDatum F H₀ hpin)
    (hπ : Irreducible π) [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    [Finite (ResidueField O)]
    {g : Polynomial O} (hlab : HasLabel L g)
    (hm1 : ∀ (hne : (dvSideSet F g L.u L.ℓ).Nonempty) (M₀ : ℕ)
      (hp : dvHgt F g (dvSideMin F g L.u L.ℓ hne) = (M₀ : ℕ∞)),
      dvResPoly F H₀ hpin g L.u L.ℓ hne M₀ hp = L.r)
    (hx : IsPure Polynomial.X g F.h F.e₁)
    (hbox : ∀ g' ∈ monicFactors g, CBox1Side L g') :
    typeOf g = ⟨{(F.e₁ * L.ℓ, F.f₁ * L.r.natDegree)}⟩ ∧ Irreducible g
```

**DEPENDS.** C.10 (`keyDeg₂_regroup`) · C.26 · C.29 · C.33/C.34 (label heredity to factors)
· C.59 · C.60 · landed `typeOf_degree`, `efPair_pos_of_mem`, `typeOf_mul`,
`FactorizationType.ext`.

**PROOF.**
1. Heredity: each monic factor `g'` of `g` is `(u,ℓ)`-pure with `r`-power residual
   (C.34's B.57-pattern purity-of-factors at the `dv`-carrier — consumed via the RE-PLAN'd
   `dvResPoly_mul_of_pure` helper) and x-pure (B.57 at the x-key).
2. Legs: C.59 + `hbox` per factor.
3. The multiset argument: `typeOf_degree` + `efPair_pos_of_mem` + `Multiset` arithmetic
   (B.58's step 3, verbatim pattern).
4. Irreducibility: singleton `typeOf` with full degree ⟹ one monic factor.

**SIZE.** 36 lines.

**SOURCE.** DECISION C-D1 Tier 1; `EFF.HE6R1.16` (the sandwich, audited: “`e ≥ e₁ℓ`,
`f ≥ f₁d_r`, `ef = D″ = (e₁ℓ)(f₁d_r)` ⟹ equality both ✓ — the same sandwich as HE6's
THEOREM HE6.A step 4, one level up”); CHAP-B §0.4 + B.58 (the level-1 twin).

**TEETH.** the peel's σ prediction (`{(2,2)}` per peeled factor, 12/12 with 5/5 PARI) and
`HE6-T-CASEB`-family instances → **executable regressions** retained; §13 fires the
`(e₁ℓ, f₁d_r)` read at `q = 2` AND `q = 3` with `e > 1 ∧ f > 1` (the `(2,2)` witness IS
such an instance — GC-11's shape satisfied non-vacuously).

**ENVIRONMENT.** ENV-C3.

---

### NODE C.62 [theorem] [fresh]

**STATEMENT.** *TIER 1 iterated — the composed-label singleton (supplies C.49's
dictionary).* Same sandwich one level further: for a factor carrying the composed label
(tower datum `T`, level-2 side `(u₃, ℓ₃)` with residual `r₂` over `level2Field`, at
multiplicity 1), with the iterated hypotheses (`CBox1Side` at both levels + the level-3
ramified leg by C.59's route at the level-2 value data):
`typeOf g = ⟨{(F.e₁ * T.e₂ * ℓ₃, F.f₁ * T.f₂ * r₂.natDegree)}⟩` and `g` irreducible.

**SIGNATURE** [signed: A-C.1 — elaborated in `leanspec/Leanspec/ChapC.lean`; the hypothesis
bundle IS the booked `ComposedLabel` structure (E's expected request pre-honored); the
"CBox1Side at both levels" is `hbox1` (level 2, per factor) + `hbox2` (the level-3 residue
leg, per factor, written out — the composed `f`-divisibility)].
```lean
namespace Uniformity.Density.Tower

structure ComposedLabel {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀}
    (T : TowerDatum F H₀ hpin) (hπ : Irreducible π) (g : Polynomial O) : Type _ where
  u₃ : ℕ
  ℓ₃ : ℕ
  r₂ : Polynomial (AdjoinRoot (towerLabel T))
  hℓ₃ : 0 < ℓ₃
  hcop : Nat.Coprime u₃ ℓ₃
  hfloor : ℓ₃ * T.E₂ < u₃
  hr₂ : r₂.Monic ∧ Irreducible r₂ ∧ 0 < r₂.natDegree ∧ r₂.coeff 0 ≠ 0
  hgmonic : g.Monic
  hgdeg : g.natDegree = (F.e₁ * T.e₂ * ℓ₃) * (F.f₁ * T.f₂ * r₂.natDegree)
  hpure1 : IsDvPure F g T.u₂ T.e₂
  hxpure : IsPure Polynomial.X g F.h F.e₁
  hne₂ : (dv2SideSet (T.levelDatum hπ) (composedKey T) g u₃ ℓ₃).Nonempty
  hres₂ : dv2ResPoly (T.levelDatum hπ) (composedKey T) g u₃ ℓ₃ hne₂ = r₂

theorem tier1_typeOf_composed {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀}
    (T : TowerDatum F H₀ hpin) (hπ : Irreducible π) (hh : 1 ≤ F.h)
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [Finite (ResidueField O)]
    {g : Polynomial O} (C : ComposedLabel T hπ g)
    (hbox1 : ∀ g' ∈ monicFactors g, CBox1Side (T.levelDatum hπ) g')
    (hbox2 : ∀ g' ∈ monicFactors g, (F.f₁ * T.f₂ * C.r₂.natDegree) ∣ inertiaDegOf g') :
    typeOf g = ⟨{(F.e₁ * T.e₂ * C.ℓ₃, F.f₁ * T.f₂ * C.r₂.natDegree)}⟩ ∧ Irreducible g
```

**DEPENDS.** C.11 · C.12 · C.44/C.45 · C.59 (route, at level-2 data) · C.60 (both levels) ·
C.61 (the level-2 step) · landed engine as C.61.

**PROOF (route).** The three cleared value reads at level 3 (`π ↦ ℓ₃ℓe₁`-family, the
level-2 key `Ψ ↦ u₃`, the level-1 key at its transported value); Bezout with the composed
coprimalities; then the multiset argument at `deg g = (e₁e₂ℓ₃)(f₁f₂·deg r₂)`.

**SIZE.** 36 lines.

**SOURCE.** `EFF.HETOW.23` (the composed dictionary this supplies); DECISION C-D1;
`EFF.GENTOW5` (the third-stage frame consuming the same shape — §9).

**TEETH.** HETOW's 300/300 μ₂ = 3 PARI leg → retained (C.49's row).

**ENVIRONMENT.** ENV-C3.

---

### NODE C.63 [theorem] [fresh]

**STATEMENT.** *TIER 1 assembled — the separable-side class-size law (`THEOREM HE6.A`
recast, C-D1).* With the §5 dissection context (`Squarefree f`, `¬ F.key ∣ f`, complete
bundle) at a side `(u, ℓ)` whose residual `R := dvResPoly …` is **separable**: `f`'s
slope-`(u,ℓ)` part factors as `∏_{r ∣ R irreducible monic} f_{λ,r}` with, for every `r`
(under `CBox1Side` at each factor):

```
deg f_{λ,r} = D′·ℓ·deg r      and      typeOf f_{λ,r} = ⟨{(e₁ℓ, f₁·deg r)}⟩,
```

each `f_{λ,r}` irreducible — the factor-form of `|S_{λ,r}| = D′·ℓ·deg r` "at EVERY
`(ℓ, deg r)` — in particular at `ℓ ≥ 2` with `deg R_λ ≥ 2`, the configuration HE3-BOX-6
boxed; and each `S_{λ,r}` is the root set of a single monic irreducible factor of `f` over
`O` with `e = e₁ℓ, f = f₁·deg r`" (`EFF.HE6.18`, verbatim — the root-set clause carried as
the docstring gloss, the factor clause carried as the theorem).

**SIGNATURE** [signed: A-C.1 — elaborated in `leanspec/Leanspec/ChapC.lean`; the per-`r`
`C-BOX-1` hypotheses sit inside the conclusion's conditional (each factor's box is about
ITS `r`, so `CBox1Side L` — keyed to `L.r` — is written out per factor)].
```lean
namespace Uniformity.Density.Tower

theorem classSize_separable {F : KeyFrame O π} {H₀ hpin} (L : LevelDatum F H₀ hpin)
    (hπ : Irreducible π) [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    [Finite (ResidueField O)]
    {g : Polynomial O} (hg : g.Monic) (hpure : IsDvPure F g L.u L.ℓ)
    (hx : IsPure Polynomial.X g F.h F.e₁)
    (hne : (dvSideSet F g L.u L.ℓ).Nonempty) {M₀ : ℕ}
    (hp : dvHgt F g (dvSideMin F g L.u L.ℓ hne) = (M₀ : ℕ∞))
    (hsep : (dvResPoly F H₀ hpin g L.u L.ℓ hne M₀ hp).Separable) :
    ∃ (s : Finset (Polynomial (F.stageField H₀ hpin)))
      (Fac : Polynomial (F.stageField H₀ hpin) → Polynomial O),
      (∀ r ∈ s, r.Monic ∧ Irreducible r ∧ r ∣ dvResPoly F H₀ hpin g L.u L.ℓ hne M₀ hp) ∧
      (∀ r : Polynomial (F.stageField H₀ hpin), r.Monic → Irreducible r →
        r ∣ dvResPoly F H₀ hpin g L.u L.ℓ hne M₀ hp → r ∈ s) ∧
      g = ∏ r ∈ s, Fac r ∧
      ∀ r ∈ s, (Fac r).Monic ∧
        (Fac r).natDegree = (F.e₁ * F.f₁) * L.ℓ * r.natDegree ∧
        ((∀ g' ∈ monicFactors (Fac r), (F.f₁ * r.natDegree) ∣ inertiaDegOf g') →
          typeOf (Fac r) = ⟨{(F.e₁ * L.ℓ, F.f₁ * r.natDegree)}⟩ ∧ Irreducible (Fac r))
```

**DEPENDS.** C.26 · C.33 · C.34 · C.61 (+ its hypothesis bundle) · B.26/B.27's
separability API shape (`irreducible_separable` — the residue-field separability toolkit at
the stage field).

**PROOF.** C.34 with the prime factorization of the separable `R` (all `m_r = 1`); per
block, C.61; degree bookkeeping via C.26.

**SIZE.** 30 lines.

**SOURCE.** `EFF.HE6.18` (THEOREM HE6.A, verbatim display — transcribed at C-D1's recast;
the corpus proof `EFF.HE6.32` has NO node, per C-H2); `EFF.HE6.19` (the widened corollary
this slots into, via C.30's trichotomy case (a)).

**TEETH.** HE6's dictionary 60/60 at the ℚ₉/ℚ₂₅ non-prime-`q` bases (`EFF.HE6.54`'s PE4
fresh leg) → **executable regression** retained (the nearest-to-`f₁ ≥ 2` machine evidence
in the corpus, recorded at exactly that strength); `HE6-T-CASEB` (separability
machine-certified SHARP: three σ on identical outer data at a repeated residual) →
retained — it guards the HYPOTHESIS, which no theorem can.

**ENVIRONMENT.** ENV-C3.

---

### NODE C.64 [theorem] [fresh]

**STATEMENT.** *TIER 2 — the block length in read form.* With §5's block context
(`¬ Ψ ∣ f_S` for a test key `Ψ`): (i) `(blockFactor L f).natDegree = L.keyDeg₂ * mult₂ L f`
exactly (C.35's exactness, elevated to the public interface); (ii) **computability from
`f`**: `mult₂ L f` is determined by `f`'s own level-2 data — the above-seam argmin
structure of `dv2Supp L Ψ f` — without exhibiting `f_S` (C.37's translation: same argmin
sets shifted by `c_g`). This is `|S_{λ,r}| = D″·μ₂` "computable from `f`" —
`LEMMA HE6R1-2(b)`'s deliverable, the READ form (HE7-BOX-4 superseded "in read form" and
no more — `EFF.HE6R1.21`'s qualification carried verbatim).

**SIGNATURE** [signed: A-C.1 — elaborated in `leanspec/Leanspec/ChapC.lean`; "computable
from `f`" signed as the argmin-DATA equality (`dv2SideMin`/`dv2SideDeg` of `f` = of `f_S`),
the shifted-argmin content of C.37 in consumable form].
```lean
namespace Uniformity.Density.Tower

theorem blockDeg_eq {F : KeyFrame O π} {H₀ hpin} (L : LevelDatum F H₀ hpin)
    (hπ : Irreducible π) [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    {f : Polynomial O} (hctx : BlockContext L f) :
    (blockFactor L f).natDegree = L.keyDeg₂ * mult₂ L f

theorem mult₂_readable {F : KeyFrame O π} {H₀ hpin} (L : LevelDatum F H₀ hpin)
    (hπ : Irreducible π) [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    {f Ψ : Polynomial O} (hΨ : IsTestKey L Ψ) (hctx : BlockContext L f)
    (hnd : ¬ Ψ ∣ blockFactor L f)
    {u₂ ℓ₂ : ℕ} (hℓ₂ : 0 < ℓ₂) (hseam : ℓ₂ * L.seam < u₂)
    (hne : (dv2SideSet L Ψ f u₂ ℓ₂).Nonempty)
    (hne' : (dv2SideSet L Ψ (blockFactor L f) u₂ ℓ₂).Nonempty) :
    dv2SideMin L Ψ f u₂ ℓ₂ hne = dv2SideMin L Ψ (blockFactor L f) u₂ ℓ₂ hne' ∧
    dv2SideDeg L Ψ f u₂ ℓ₂ hne = dv2SideDeg L Ψ (blockFactor L f) u₂ ℓ₂ hne'
```

**DEPENDS.** C.35 · C.36 · C.37 · C.65.

**PROOF.** (i) C.34's degree bookkeeping. (ii) C.65's length sum + C.37's argmin
preservation.

**SIZE.** 24 lines.

**SOURCE.** `EFF.HE6R1.13`(b) (verbatim: “`μ₂ = Σ_{λ₂ > T₂} L_{λ₂}(f)` and
`|S_{λ,r}| = D″·μ₂` are computable from `f`, without exhibiting `f_S`”); `EFF.HE6R1.21`
(the “in read form” fence).

**TEETH.** the `μ₂ = 2` frame audit + the 12-member degenerate stratum's post-peel reads →
§13 regression.

**ENVIRONMENT.** ENV-C2.

---

### NODE C.65 [lemma] [fresh]

**STATEMENT.** *The above-seam length sum.* For the block `f_S` (its level-2 polygon):
the above-seam sides of `dv2Supp L Ψ f_S` span abscissas `0 … mult₂` exactly, so
`Σ_{(u₂,ℓ₂) above seam} dv2SideLen = mult₂`; by C.37 the same sum computed on `f` equals
`mult₂` too. (The level-2 `Σ L_λ = μ` identity — whose level-1 ancestor needed `A₀ ≠ 0`
(the peel convention); here the `j = 0` level-2 pin is finite exactly because `Ψ ∤ f_S` —
FINDING HE6R1-F2's repaired hypothesis doing its job.)

**SIGNATURE** [signed: A-C.1 — elaborated in `leanspec/Leanspec/ChapC.lean`, AT THE SPAN
FORM: `j = 0` pin finite (the repaired-hypothesis content), top pin `(mult₂, 0)`, every
above-seam side inside `[0, mult₂]`; the summed `Σ dv2SideLen = mult₂` is the fleet's
argmin-partition corollary — recorded].
```lean
namespace Uniformity.Density.Tower

theorem dv2_length_sum {F : KeyFrame O π} {H₀ hpin} (L : LevelDatum F H₀ hpin)
    (hπ : Irreducible π) [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    {f Ψ : Polynomial O} (hΨ : IsTestKey L Ψ) (hctx : BlockContext L f)
    (hnd : ¬ Ψ ∣ blockFactor L f) :
    dv2Pin L Ψ (blockFactor L f) 0 ≠ ⊤ ∧
    dv2Pin L Ψ (blockFactor L f) (mult₂ L f) = (0 : ℕ∞) ∧
    ∀ u₂ ℓ₂ : ℕ, 0 < ℓ₂ → ℓ₂ * L.seam < u₂ →
      ∀ hne : (dv2SideSet L Ψ (blockFactor L f) u₂ ℓ₂).Nonempty,
        dv2SideMax L Ψ (blockFactor L f) u₂ ℓ₂ hne ≤ mult₂ L f
```

**DEPENDS.** C.11 · C.36 · C.37 · C.38a (the `dv2SideSet` helper) · C.13.

**PROOF.** The `j = 0` pin is finite (`Ψ ∤ f_S` ⟺ the constant Ψ-development coefficient
is nonzero — B.02/B.05 at the Ψ-key); the top pin `(mult₂, 0)`-cleared from monicity; the
argmin abscissae partition `0 … mult₂` by the C.08-pattern spacing at level 2.

**SIZE.** 26 lines.

**SOURCE.** `EFF.HE6R1.13`(b); `EFF.HE6R1.14` (the `dv₂(A₀^{(2)}) = ∞` failure mode when
`Ψ ∣ f` — the 12 BADTOTAL members — which is exactly the hypothesis's necessity, recorded
in the docstring).

**TEETH.** the BADTOTAL diagnosis (block sizes did not sum to `deg f` at `Ψ ∣ f`) →
**executable regression** retained; the repaired-hypothesis path re-fires in §13's peel
row.

**ENVIRONMENT.** ENV-C2.

---

### NODE C.66 [cite] [cite:FGMN]

**STATEMENT.** *TIER 3's import — residual multiplicativity at the general order
([cite:FGMN], gate (b)).* The cited theorem, at the scope Step II of `LEMMA GENTOW-6.1`
consumes: **for monic `f = g·g'` over `O` with the §5 side data at a common side, the side
residual of the product is the product of the side residuals up to a fixed `K^×`-scalar**
— FGMN (Fernández–Guàrdia–Montes–Nart, *Residual ideals of MacLane valuations*,
arXiv:1305.0775v3) **Thm 2.8 + Cor 4.7(3) + Cor 4.4(4)** *[⚠ arXiv-v3 numbers — the
PUBLISHED loci are Thm 2.8 + Cor 4.12(3) + Cor 4.9(3); see the A-3 rider below BEFORE
transcribing — inline pointer added at A-C.1 to close D23's top-down trap]*, read through
GENTOW2's tower↔MacLane dictionary and shear (`ψ₂^{FGMN} = R_2(φ₃)`-row faithfulness map). Lean
carrier: an `axiom`-free import is impossible (it is a literature theorem about MacLane
valuations); per Part V gate (b) it enters as a **declared, cited axiom** in the
`AXIOM_FAITHFULNESS` pattern — published-source citation (the layout print at
`docs/references/fgmn_residual_ideals_1305.0775v3_layout.txt`, numbering verified at
GENTOW2's ledger), faithfulness entry, fresh-context audit, **Asvin signs per cite**. The
exact Lean statement is drafted at stub stage against C.25's `dvResPoly` carrier and is
THE deliverable of this node; nothing fires from it until signed.

**⚠ SCOPE FENCE.** The import is stated at exactly the multiplicativity clause Step II
consumes — never the full FGMN machinery, never `w`'s closed form (C-H10: `w` is NOT
computed anywhere in the corpus, and this cite must not smuggle it).

**⚠ A-3 NUMBERING CORRECTION (2026-08-16, `docs/CITE_NUMBERING_AUDIT_2026-08-16.md`).** The three
cited statements are right; **two of the three numbers are arXiv-v3 numbers that the published
paper does not use.** Cite, for **J. Algebra 427 (2015) 30–75** (DOI 10.1016/j.jalgebra.2014.12.022):
**Thm 2.8** (unchanged) **+ Cor 4.12(3)** (was "Cor 4.7(3)") **+ Cor 4.9(3)** (was "Cor 4.4(4)" —
the published corollary drops v3's item (1), so the clause index moves 4 → 3). arXiv:1305.0775's
last version is v3 (2013-07-26) and was never updated; a later author version (2013-12-04,
deposited under the J. Algebra record at UPCommons handle 2117/28203) renumbers §§1, 3, 4, 5, 6, and
three author-side citation echoes — including one from 2019, post-publication — confirm that later
numbering is the journal's. Statement text unchanged; every quoted display was found verbatim under
its new number. Not print-read (ScienceDirect 403s automated fetches despite bronze OA): risk
LOW-MEDIUM, two-minute closing check in audit §7.2.

**SIGNATURE** [signed: A-C.1 — the stub gate's draft `fgmn_residual_mul`, elaborated in
`leanspec/Leanspec/ChapC.lean`, ADOPTED as this node's exact Lean statement; fragile-order
sign-off honored: C.97/C.98 elaborated in the same amendment].

```lean
namespace Uniformity.Density.Tower

axiom fgmn_residual_mul (F : KeyFrame O π) (hπ : Irreducible π) (H₀ : ℕ)
    (hpin : F.Pin H₀)
    {g g' : Polynomial O} (hg : g.Monic) (hg' : g'.Monic) {u ℓ : ℕ} (hℓ : 0 < ℓ)
    (hcop : Nat.Coprime u ℓ)
    (hpg : IsDvPure F g u ℓ) (hpg' : IsDvPure F g' u ℓ)
    (hne : (dvSideSet F g u ℓ).Nonempty) (hne' : (dvSideSet F g' u ℓ).Nonempty)
    (hne'' : (dvSideSet F (g * g') u ℓ).Nonempty)
    {M₀ M₀' M₀'' : ℕ}
    (hp : dvHgt F g (dvSideMin F g u ℓ hne) = (M₀ : ℕ∞))
    (hp' : dvHgt F g' (dvSideMin F g' u ℓ hne') = (M₀' : ℕ∞))
    (hp'' : dvHgt F (g * g') (dvSideMin F (g * g') u ℓ hne'') = (M₀'' : ℕ∞)) :
    ∃ c : F.stageField H₀ hpin, c ≠ 0 ∧
      dvResPoly F H₀ hpin (g * g') u ℓ hne'' M₀'' hp''
        = Polynomial.C c
            * (dvResPoly F H₀ hpin g u ℓ hne M₀ hp * dvResPoly F H₀ hpin g' u ℓ hne' M₀' hp')
```

**⚠ THE THREE DRAFTING DECISIONS THE OWNER MUST INSPECT** (the blueprint fixed none of them;
transcribed from the stub gate's draft, now the signed statement): (1) the "fixed
`K^×`-scalar" is an existential nonzero `c` in `stageField`, not a named function of the data
(the corpus does not name it; C-H10 forbids claiming a closed form); (2) the two factors and
the product are read at the SAME `(u, ℓ)` with three separate nonemptiness/pin witnesses,
because `dvResPoly` takes them as arguments and no signed node relates the three (that
relation is `dvResPoly_mul_of_pure`, the RE-PLAN'd B.35 twin); (3) purity of both factors at
the common side is hypothesized (`IsDvPure`) — the "common side data" of the prose.
Status: **gate-(b)-SIGNED-AT-CATEGORY (append #66), statement-UNINSPECTED** — the owner's
per-statement inspection is owed; queued in CHAP-I's gate-(b) addendum (A-C.1).

**DEPENDS.** C.25 (the carrier the statement is written against) · GENTOW2's dictionary
layer (§10: C.97/C.98 — the faithfulness map rows the transport reads through; DAG order
§10's dictionary nodes before this node's SIGN-OFF, though its statement can be drafted
first).

**PROOF.** none — axiom import under gate (b).

**SIZE.** statement only (≤ 20 lines + the faithfulness entry in
`docs/AXIOM_FAITHFULNESS.md`).

**SOURCE.** `EFF.GENTOW6.09` (the cite leg, verbatim conditionality: “the cite carries the
load … GENTOW2's own arc grade applies upstream”); `EFF.GENTOW2` (the FGMN-cite carrier
note — the corpus's ONE load-bearing literature cite, `TIGHTNESS_CENSUS` row I-3).

**TEETH.** the repo-side `(MULT)` corroboration leg (displayed as corroboration, NOT the
load-carrier) → **executable regression** retained; disposition table (§16) carries the
three stacked conditionalities of `EFF.GENTOW6.09` verbatim.

**ENVIRONMENT.** ENV-C1 (statement-level).

---

### NODE C.67 [theorem] [fresh] (cite-conditional through C.66)

**STATEMENT.** *TIER 3 — the multiplicity tie at every side shape (`LEMMA GENTOW-6.1`;
closes `GENTOW4-BOX-1` = `HYP.144`, cite-conditionally).* In the §5 context, for EVERY side
of the level polygon and every monic irreducible `r ∣ R` with multiplicity `m_r`:

```
deg f_{κ,r} = D′·ℓ·deg(r)·m_r,
```

the block's own level-1 polygon is the single side of slope `κ` and length `ℓ·deg(r)·m_r`
with residual EXACTLY `r^{m_r}` (monic, unit-free); consequently at every class with
`ℓ·deg r ≥ 2` read through the composed key, **`μ₂*(r) = m_r`** — the composed polygon
length equals the level-1 residual multiplicity, class by class, MIXED sides included.
Proof = the corpus's three steps: (I) block single-side + pure-power residual (C.33/C.34 +
the degree clause — the slope-uniqueness argument at the factor, closure-free); (II) the
cite (C.66); (III) the UFD match `k_r = m_r` in `K[Z]` (scalar-robust: units absorb into
`γ*`, which is why the tie survives η ≠ 1 exposure).

**SIGNATURE** [signed: A-C.1 — elaborated in `leanspec/Leanspec/ChapC.lean`; the PROOF
consumes C.66's `fgmn_residual_mul` by name, so the landed footprint carries `[cite:FGMN]`
(the honest carrier: a consumer sees it in `#print axioms`, exactly as the ledger wants);
the multiplicity `m` enters as the exact-power hypothesis pair].
```lean
namespace Uniformity.Density.Tower

theorem multiplicity_tie {F : KeyFrame O π} {H₀ hpin} (L : LevelDatum F H₀ hpin)
    (hπ : Irreducible π) [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    {f : Polynomial O} (hctx : BlockContext L f) {m : ℕ} (hm : 0 < m)
    (hmult : ∀ (hne : (dvSideSet F f L.u L.ℓ).Nonempty) (M₀ : ℕ)
      (hp : dvHgt F f (dvSideMin F f L.u L.ℓ hne) = (M₀ : ℕ∞)),
      L.r ^ m ∣ dvResPoly F H₀ hpin f L.u L.ℓ hne M₀ hp ∧
      ¬ L.r ^ (m + 1) ∣ dvResPoly F H₀ hpin f L.u L.ℓ hne M₀ hp) :
    (blockFactor L f).natDegree = (F.e₁ * F.f₁) * L.ℓ * (L.r.natDegree * m) ∧
    mult₂ L f = m ∧
    IsDvPure F (blockFactor L f) L.u L.ℓ ∧
    ∀ (hne : (dvSideSet F (blockFactor L f) L.u L.ℓ).Nonempty) (M₀ : ℕ)
      (hp : dvHgt F (blockFactor L f)
        (dvSideMin F (blockFactor L f) L.u L.ℓ hne) = (M₀ : ℕ∞)),
      dvResPoly F H₀ hpin (blockFactor L f) L.u L.ℓ hne M₀ hp = L.r ^ m
```
(`μ₂*(r) = m_r` is the `mult₂ L f = m` clause; the residual-EXACTLY-`r^m` clause is the
"monic, unit-free" content — Step III's UFD match landing in the statement.)

**DEPENDS.** C.26 · C.33 · C.34 · C.35 · C.66 · landed UFD facts for `K[Z]`.

**PROOF (route).** `EFF.GENTOW6.08`–`.10`'s three steps; Step I re-derived at the
`dv`-carrier (hypothesis inheritance to the divisor checked explicitly, as the corpus
does); Step III `UniqueFactorizationMonoid` matching.

**SIZE.** 40 lines. **Split candidate:** Step I / Steps II–III.

**SOURCE.** `EFF.GENTOW6.07` (verbatim displays); `.08`/.09/.10 (the steps + the three
stacked conditionalities); `EFF.GENTOW4.36`-family (`HYP.144`'s box text this closes —
“a faithful-cite unit in GENTOW2's pattern would retire it — and this note IS that unit,
unlanded”; the Lean node is the landing).

**TEETH.** the tie “held on each measured class row including μ₂* = 3 and
transposed-profile rows” → **executable regression** retained + one §13 row per prime.

**ENVIRONMENT.** ENV-C2.

---

### NODE C.68 [lemma] [fresh]

**STATEMENT.** *Pin equality at side-interior abscissas (GENTOW-4.C's m-i TERMINAL
citation, supplied here).* In C.37's context, the level-2 pins (not just the support
values) transport: at on-hull abscissas C.37's translation gives the INEQUALITY
`dv2Pin L Ψ f j ≥ dv2Pin L Ψ f_S j + c_g`-cleared, with **equality at side-INTERIOR
abscissas** — the equality leg riding C.38/C.39's residual-scalar display (a unit scalar
cannot create or destroy an interior pin), exactly the m-i completion: “(b) alone gives an
INEQUALITY at on-hull points; equality at side-interior abscissas rides (c)”.

**SIGNATURE** [signed: A-C.1 — elaborated in `leanspec/Leanspec/ChapC.lean`].
```lean
namespace Uniformity.Density.Tower

theorem dv2Pin_translation_interior {F : KeyFrame O π} {H₀ hpin} (L : LevelDatum F H₀ hpin)
    (hπ : Irreducible π) [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    {f Ψ : Polynomial O} (hΨ : IsTestKey L Ψ) (hctx : BlockContext L f)
    (hnd : ¬ Ψ ∣ blockFactor L f)
    {u₂ ℓ₂ : ℕ} (hℓ₂ : 0 < ℓ₂) (hseam : ℓ₂ * L.seam < u₂)
    (hne : (dv2SideSet L Ψ f u₂ ℓ₂).Nonempty) {j : ℕ}
    (hj1 : dv2SideMin L Ψ f u₂ ℓ₂ hne < j) (hj2 : j < dv2SideMax L Ψ f u₂ ℓ₂ hne) :
    dv2Pin L Ψ f j = dv2Pin L Ψ (blockFactor L f) j + (complementConst L f : ℕ∞)
```

**DEPENDS.** C.37 · C.38 · C.39.

**PROOF.** Interior abscissas are argmin-adjacent on both sides; the scalar is a unit
(C.39), so coefficient (non)vanishing at the read heights matches; the pin equality follows
from the two one-sided bounds.

**SIZE.** 22 lines.

**SOURCE.** `EFF.GENTOW4.33` (acceptance-fold m-i: the citation completed to (b) AND (c) —
CHAIN-CG-CITE TERMINAL); `EFF.HE6R1.13`(b)/(c).

**TEETH.** as C.37's. **ENVIRONMENT.** ENV-C2.

---

### NODE C.69 [theorem] [fresh] — **TERMINAL SUPPLY: THE CLASS-SIZE/BLOCK-LENGTH BUNDLE**

**STATEMENT.** *The one statement downstream chapters cite.* Under the §5 standing context,
for a level datum `L` over `F`:
(1) **[separable side, per-factor]** `R` separable ⟹ per irreducible `r ∣ R`, one
irreducible factor of degree `D′ℓ·deg r` with `typeOf = ⟨{(e₁ℓ, f₁·deg r)}⟩` —
conditional on `CBox1Side` per factor (vacuous at `f₁·deg r = 1`) [C.63];
(2) **[read form]** `deg f_S = D″·μ₂` with `μ₂` computable from `f` [C.64/C.65];
(3) **[mixed-side tie]** `deg f_{κ,r} = D′ℓ·deg(r)·m_r` and `μ₂*(r) = m_r` —
cite-conditional on [cite:FGMN] [C.67].
Stated as one bundled theorem (a conjunction re-exporting the three, hypotheses displayed
separately per clause) so that CHAP-B H-2's consumers, chapter E's `EFF.HE6.30`/`.32` pin
anchors ([F1] resolution: they resolve HERE), chapter D's T1 battery check 10, and
chapter F's faces have ONE name to cite, with the conditionality readable off the
hypothesis list and the axiom footprint.

**SIGNATURE** [signed: A-C.1 — elaborated in `leanspec/Leanspec/ChapC.lean`; stub-stage
choice EXERCISED: a Prop-structure `ClassSizeSupplyData` with three clause fields quoting
the suppliers' statements (hypotheses displayed per clause), + the one named theorem —
"the NAME is the contract"].
```lean
namespace Uniformity.Density.Tower

structure ClassSizeSupplyData {F : KeyFrame O π} {H₀ hpin}
    (L : LevelDatum F H₀ hpin) : Prop where
  separable_side : … -- C.63's statement, quantified (full text in the leanspec twin)
  read_form : …      -- C.64's blockDeg_eq statement
  mixed_tie : …      -- C.67's mult₂ L f = m clause

theorem classSize_supply {F : KeyFrame O π} {H₀ hpin} (L : LevelDatum F H₀ hpin) :
    ClassSizeSupplyData L
```
(the three field texts are byte-fixed in `leanspec/Leanspec/ChapC.lean`'s
`ClassSizeSupplyData` — quoted there in full; the display above elides them ONLY because
they repeat C.63/C.64/C.67's signed blocks verbatim.)

**DEPENDS.** C.63 · C.64 · C.65 · C.67.

**PROOF.** re-export. **SIZE.** 20 lines.

**SOURCE.** DECISION C-D1 (the supply mandate); BRIEF C trap (i) (“downstream consumers
were told to get it from chapter C” — this is where they get it); BRIEF E trap (i)/[F1]
(the `.30`/`.32` anchors resolve to a chapter-C node — this one).

**TEETH.** re-exports carry their suppliers' teeth; §13's gate row fires clause (1) at
both primes with `e > 1 ∧ f > 1`.

**ENVIRONMENT.** ENV-C3.

---

### NODE C.70 [lemma] [fresh]

**STATEMENT.** *Side-length accounting (`n_λ = D′L_λ` closed, factor form).* In the §5
context at a side `(u, ℓ)` with residual `R = ∏ r^{m_r}`:
`Σ_r ℓ·deg(r)·m_r = ℓ·deg R = dvSideLen` and hence
`Σ_r deg f_{κ,r} = D′·dvSideLen` — the `(SEP)`-free per-side degree conservation
(LEMMA HE6-3(b)'s consumed content, supplied to C.31(iv) and to the §11 count layer).

**SIGNATURE** [signed: A-C.1 — elaborated in `leanspec/Leanspec/ChapC.lean`, at the per-side
core `L_λ = ℓ·deg R` (the consumed `(SEP)`-free conservation); the `Σ_r` decomposition rides
C.67, recorded].
```lean
namespace Uniformity.Density.Tower

theorem side_degree_conservation (F : KeyFrame O π) (hπ : Irreducible π)
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O] {H₀ : ℕ} (hpin : F.Pin H₀)
    {f : Polynomial O} {u ℓ : ℕ} (hℓ : 0 < ℓ) (hcop : Nat.Coprime u ℓ)
    (hf : f.Monic) (hpure : IsDvPure F f u ℓ)
    (hne : (dvSideSet F f u ℓ).Nonempty) {M₀ : ℕ}
    (hp : dvHgt F f (dvSideMin F f u ℓ hne) = (M₀ : ℕ∞)) :
    dvSideLen F f u ℓ hne = ℓ * (dvResPoly F H₀ hpin f u ℓ hne M₀ hp).natDegree
```

**DEPENDS.** C.08 · C.26 · C.33 · C.67 (mixed sides) or C.63 (separable) — stated once via
C.67's general form.

**PROOF.** degree additivity of `dvResPoly` on the block product (the RE-PLAN'd
`dvResPoly_mul_of_pure`) + C.08's length law + `Polynomial.natDegree` arithmetic on
`∏ r^{m_r}`.

**SIZE.** 18 lines.

**SOURCE.** `EFF.HE6R1.10` (the consumed `n_λ = D′L_λ`, “(SEP)-free”); `EFF.HE6R1.12` (the
slack display `D′ℓΣ_r(m_r−1)d_r` — which this node's conservation + C.67's tie together
close, the gap HE6R1-2 was invented for).

**TEETH.** the census reconciliations (`EFF.HE6R1.25`: block sizes sum to `deg f`, 932/944
with the 12 explained) → regression retained.

**ENVIRONMENT.** ENV-C2.

---

---

## 8. §8 — THE SHADOW-READ LAYER AND THE PARTIAL SIDES

> **Design note.** GENTOW3 ([GENHN-TOW-1] item (3)): the faithfulness geography of the
> stage-shadow read — WHEN a known-wrong read (T(b)'s refuted object) is nonetheless right.
> Its TERMINAL forms carry three of the corpus's sharpest post-acceptance repairs (C-H8):
> the `[GT3-r2]` certificate pin inside (iv)'s statement, S8.1's withdrawn-inference
> re-derivation (persistence STRICTLY above the floor, under the box hypothesis), and
> CHAIN-NONFUNC's double supersession ending at the σ-only claim (S8.4 — activated under
> the owner's delegated authority with the INCOMPLETE-read disclosure attached; this
> chapter transcribes the TERMINAL σ-claim and nothing stronger). GENTOW4 ([GENHN-TOW-1]
> item (4)): partial inner sides — the datum at every side (4.1), the bouquet + projection
> (4.A, with TOWERRAT2-C's corrected monic signature), the pure-power tie (4.2), the
> `c_g`-read (4.C). The mixed-side tie routes to §7's C.67 (GENTOW4-BOX-1's closure).
> GENTOW6's budget half (6.2/6.2C) closes the section; its caps/attainment layer (6.3/6.4/
> 6.5) lands in §9 with the thresholds (A-§8 delta against the index's section gloss).
> The GENTOW6 caps aside, everything here is FULL-strength: items (2), (3), (4) of
> `HYP.82` at their notes' own acceptance scopes.

### NODE C.71 [def] [fresh]

**STATEMENT.** *The two reads and the faithfulness threshold.* For a tower datum `T` and
`f ∈ 𝒯`: the **composed (honest) read** — the `Φ₂`-development coefficients `C_j` (B.02's
`dev` at the key `Φ₂`); the **stage-shadow read** — the two-variable division carried out
with every coefficient reduced mod `Φ′`: `ShC_j := Σ_b ḡ_{j,b}·Φ′^b` (`deg ḡ < D′`), the
mod-`Φ′`-reduced division tower (implemented as iterated `Polynomial.modByMonic` at `Φ′`
inside the `Φ₂`-division — a total `O[x]`-construction); the **margin** `δ T := T.u₂ −
T.e₂ * (F.e₁*F.f₁) * F.h` (`≥ 1` by the node floor); and the **threshold**
`Θ T j := (μ₂ − j) * T.E₂ + δ T`.

**SIGNATURE** [signed: A-C.1 — elaborated in `leanspec/Leanspec/ChapC.lean`; `shadowDev`'s
REAL body determined: the mod-`Φ′`-reduced tower is the `Φ₂`-adic development computed in
`(O[x]/Φ′)[Z]` (the `biRead` two-variable image + the generic monic division `devQ`) and
mapped back through the CANONICAL representative `AdjoinRoot.modByMonicHom` (no choice) —
"iterated `modByMonic` at `Φ′` inside the `Φ₂`-division" made literal].
```lean
namespace Uniformity.Density.Tower

noncomputable def devQ {R : Type*} [CommRing R] (Ψ : Polynomial R) :
    Polynomial R → ℕ → Polynomial R
  | g, 0 => g %ₘ Ψ
  | g, j + 1 => devQ Ψ (g /ₘ Ψ) j

noncomputable def biRead (F : KeyFrame O π) (g : Polynomial O) :
    Polynomial (AdjoinRoot F.key) :=
  (Finset.range (g.natDegree + 1)).sum fun b =>
    Polynomial.C (AdjoinRoot.mk F.key (dev F.key g b)) * Polynomial.X ^ b

noncomputable def shadowDev {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀}
    (T : TowerDatum F H₀ hpin) (f : Polynomial O) (j : ℕ) : Polynomial O :=
  let S := devQ (biRead F (composedKey T)) (biRead F f) j
  (Finset.range (S.natDegree + 1)).sum fun b =>
    (AdjoinRoot.modByMonicHom F.hmonic (S.coeff b)) * F.key ^ b

def TowerDatum.margin {F : KeyFrame O π} {H₀ hpin} (T : TowerDatum F H₀ hpin) : ℕ :=
  T.u₂ - T.e₂ * ((F.e₁ * F.f₁) * F.h)

def TowerDatum.theta {F : KeyFrame O π} {H₀ hpin} (T : TowerDatum F H₀ hpin)
    (μ₂ j : ℕ) : ℕ := (μ₂ - j) * T.E₂ + T.margin
```

**DEPENDS.** B.02 · C.42 · C.43 · C.50.

**PROOF.** definitional (`margin ≥ 1` as a companion via `T.hfloor`). **SIZE.** 18 lines.

**SOURCE.** `EFF.GENTOW3.16` (the two reads, verbatim; the shadow is "the refuted T(b)
object" — the docstring says so); `EFF.GENTOW3.18` (`δ := u₂ − e₂D′h`, `Θ_j`).

**TEETH.** signed non-applicable. **ENVIRONMENT.** ENV-C1.

---

### NODE C.72 [theorem] [fresh]

**STATEMENT.** *GENTOW-3(i)+(ii): the floor and the faithful band (gauge-immune,
unconditional).* On `𝒯`: (i) every `dv₂`-height at which `shadowDev` and `dev Φ₂` carry
different slot digits is `≥ Θ T j` (the first disagreeing height of the difference clears
the threshold: `dv2Hgt … (shadowDev T f j − dev (composedKey T) f j) ≥ (Θ T j : ℕ∞)`);
(ii) at every height `m < Θ T j` the two reads' digits agree — values, classes, and
`K₂`-residues; consequently any read whose consulted heights at coordinate `j` are all
`< Θ T j` returns identical output on both reads.

**SIGNATURE** [signed: A-C.1 — elaborated in `leanspec/Leanspec/ChapC.lean`; two public
names as planned]:
```lean
theorem shadow_floor … {j : ℕ} (hj : j < μ₂) :
    (T.theta μ₂ j : ℕ∞)
      ≤ dv2Hgt (T.levelDatum hπ) (shadowDev T f j - dev (composedKey T) f j)

theorem shadow_faithful_band … {m : ℕ} (hm : m < T.theta μ₂ j)
    (hval : dv2Hgt (T.levelDatum hπ) (dev (composedKey T) f j) = (m : ℕ∞)) :
    dv2Hgt (T.levelDatum hπ) (shadowDev T f j) = (m : ℕ∞) ∧
    dv2Res (T.levelDatum hπ) (shadowDev T f j)
      = dv2Res (T.levelDatum hπ) (dev (composedKey T) f j)
```
(binder lists — `T hπ hh [insts] {μ₂} {f} (hf : f ∈ towerLocus T μ₂)` — byte-fixed at the
leanspec twin.)

**DEPENDS.** C.11 · C.50 · C.52 (Step 0's carry pricing: the x-carry's `Φ′`-branch raises
weight by EXACTLY `δ` — "the whole engine of the note") · C.71.

**PROOF (route).** `EFF.GENTOW3.22`–`.24`'s Steps 0–2: the division ledger (`Ĝ_j` at weight
`≥ (μ₂−j)E₂`), then every discrepancy branch pays `≥ 1` Φ′-extraction at `+δ` each —
weight-level and VALUE-BLIND throughout (the S7.1 certificate: "clauses (i)/(ii) and their
proofs are gauge-immune and uniform in `f₁`").

**SIZE.** 40 lines. **Split candidate:** (i)'s ledger / (ii)'s restatement.

**SOURCE.** `EFF.GENTOW3.18`/.19 (verbatim); `.22` (Step 0 with the `+δ EXACTLY` audit).

**TEETH.** P-1 FLOOR 274 checks (census corrected to 137 member_check calls — CHAIN-CENSUS
TERMINAL `.49`) → **executable regression** retained; P-6 LABEL 6 + A7-BAND rows →
retained; §13 fires one floor row per prime.

**ENVIRONMENT.** ENV-C1.

---

### NODE C.73 [def+theorem] [fresh]

**STATEMENT.** *X-free genres and GENTOW-3(iii) exactness.* **Definition (the PRIMARY
clause — the operative one at every `f₁`; the displayed `i(u₂(f₂−t)) = 0` test is its
`f₁ = 1` evaluation ONLY, CHAIN-XFREE TERMINAL):** the tower datum `T` is **x-free** iff
every lift coefficient of `composedKey T` (each `t < f₂` with `c_t ≠ 0`) is an x-free
monomial `π^a` — i.e. `stageLiftO`'s output at that slot has `X`-degree `0`. **Theorem
(iii):** at an x-free datum the discrepancy is ZERO at every height: `shadowDev T f j =
dev (composedKey T) f j` identically on `𝒯` — the shadow IS the composed read.

**SIGNATURE** [signed: A-C.1 — elaborated in `leanspec/Leanspec/ChapC.lean`; the PRIMARY
clause is the definition (every nonzero lift slot has `X`-degree 0); the displayed
`i(u₂(f₂−t)) = 0` test lands as the `f₁ = 1`-ONLY companion `isXFree_iff_slot_of_f1`, per
the `[GT3-r1]` scope bracket]:
```lean
def IsXFree {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀}
    (T : TowerDatum F H₀ hpin) : Prop :=
  ∀ t, t < T.f₂ → T.ψ₂.coeff t ≠ 0 →
    (F.stageLiftO H₀ hpin ((T.f₂ - t) * T.u₂)
      (- T.ψ₂.coeff t * F.stageLetter H₀ hpin ^ (wrapExp T t))).natDegree = 0

theorem shadow_exact_of_xfree … (hx : IsXFree T) … (j : ℕ) :
    shadowDev T f j = dev (composedKey T) f j

theorem isXFree_iff_slot_of_f1 … (hf1 : F.f₁ = 1) :
    IsXFree T ↔ ∀ t, t < T.f₂ → T.ψ₂.coeff t ≠ 0 → F.slotIdx ((T.f₂ - t) * T.u₂) = 0
```

**DEPENDS.** C.43 · C.71 · C.52 (no x-overflow ⟹ mod-`Φ′` reduction is the identity).

**PROOF.** (iii): no coefficient ever has x-degree `≥ D′`, so every reduction step is
trivial; the two division towers coincide term by term.

**SIZE.** 22 lines.

**SOURCE.** `EFF.GENTOW3.17` (the definition with the `[GT3-r1]` scope bracket — the
PRIMARY clause transcribed, the `f₁ = 1`-only equivalence recorded as a companion lemma
with the `f₁ = 1` hypothesis explicit, per the re-derivation at `.45`); `.20` ((iii),
"so read needs no `f₁` restriction"); witness FAM-D (`Φ₂ = (x²−3)² + 27`, lift `−27`
x-free).

**TEETH.** P-3 XFREE 3 + the 12-member FAM-D sweep (zero discrepancies, DRAIN self-shadow)
→ retained; FAM-D is `q = 3` — §13 pairs it with a `q = 2` x-free instance.

**ENVIRONMENT.** ENV-C1.

---

### NODE C.74 [theorem] [fresh]

**STATEMENT.** *GENTOW-3(iv) at its THREE TERMINAL layers (attainment, persistence,
σ-non-functionality).* At a non-x-free datum:
(a) **[certificate-scoped attainment — the `[GT3-r2]` pin, in-statement]** coordinate `j`
is **touched** iff the key power's assembled height-`Θ_j` `K₂`-digit (the
single-`Φ′`-extraction sum of `Φ₂^{μ₂}`'s self-overflow) does not cancel — the CERTIFICATE
sense, NOT the weaker `ShC_j ≠ 0` (the FR-M3 member separates the two: `ShC_0 = 64 ≠ 0`
while the height-10 digit cancels). Where the certificate holds, `f = Φ₂^{μ₂}` has composed
read DRAIN (`C_j = 0`) while its shadow carries a nonzero digit at exactly `Θ_j`.
(b) **[persistence, S8.1 TERMINAL]** for in-budget perturbations `g` (every slot of `g` at
weight `≥ μ₂E₂ + 1` — the GENTOW-1(a) box hypothesis, THE operative one; the frozen
"slots at heights > Θ_j" parenthetical is NOT consumed): every disagreeing height of `g`'s
two reads is `≥ Θ_j + 1`, STRICTLY above the floor — so linearity
(`(Sh−C)(f₀+g) = (Sh−C)(f₀) + (Sh−C)(g)`) isolates the certificate digit at `Θ_j` and the
divergence persists. The withdrawn inference ("both reads shift by the SAME g-digits") is
DEAD.
(c) **[σ-non-functionality, S8.4 TERMINAL]** the surviving scope: there exist members with
identical honest σ and different shadow content at heights `≥ Θ_j` (the committed PE1
triple), and members with identical shadow data and different honest reads (the S8.1
pair) — stated as the two-witness existence claim, i.e. **"not a function of the honest
read's σ"** and NO MORE (S8.2's verdict-level-tuple scope is itself WITHDRAWN; the
activation-basis disclosure of `EFF.GENTOW3.61` — search returned INCOMPLETE, read as
stronger-than-EMPTY under the owner's delegated authority — is carried in the docstring).

**SIGNATURE** [signed: A-C.1 — elaborated in `leanspec/Leanspec/ChapC.lean`; three public
theorems, **split-mandated C.74 → 3**; `TouchCert` is the `[GT3-r2]` certificate as the
EXACT-`Θ_j` discrepancy of `Φ₂^{μ₂}`'s own two reads (the single-extraction sum's
non-cancellation IS that exactness — the FR-M3 separation honored: `ShC_j ≠ 0` is NOT the
certificate)]:
```lean
def TouchCert {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀}
    (T : TowerDatum F H₀ hpin) (hπ : Irreducible π) (μ₂ j : ℕ) : Prop :=
  dv2Hgt (T.levelDatum hπ)
      (shadowDev T ((composedKey T) ^ μ₂) j - dev (composedKey T) ((composedKey T) ^ μ₂) j)
    = (T.theta μ₂ j : ℕ∞)

theorem shadow_attained_of_certificate … (hc : TouchCert T hπ μ₂ j) :
    dev (composedKey T) ((composedKey T) ^ μ₂) j = 0 ∧
    dv2Hgt (T.levelDatum hπ) (shadowDev T ((composedKey T) ^ μ₂) j) = (T.theta μ₂ j : ℕ∞)

theorem shadow_persistence … (hc : TouchCert T hπ μ₂ j) {g}
    (hbudget : <the C.52 in-budget box hypothesis on g — THE operative one, S8.1 TERMINAL>) :
    ((T.theta μ₂ j + 1 : ℕ) : ℕ∞)
        ≤ dv2Hgt (T.levelDatum hπ) (shadowDev T g j - dev (composedKey T) g j) ∧
    dv2Hgt (T.levelDatum hπ) (shadowDev T ((composedKey T) ^ μ₂ + g) j
        - dev (composedKey T) ((composedKey T) ^ μ₂ + g) j) = (T.theta μ₂ j : ℕ∞)

theorem shadow_not_sigma_function … (hnx : ¬ IsXFree T) (hμ₂ : 2 ≤ μ₂) :
    (∃ f g ∈ towerLocus T μ₂, typeOf f = typeOf g ∧ ∃ j < μ₂, shadowDev T f j ≠ shadowDev T g j) ∧
    (∃ f g ∈ towerLocus T μ₂, (∀ j < μ₂, shadowDev T f j = shadowDev T g j) ∧ typeOf f ≠ typeOf g)
```
(exact binder lists and the written-out box hypothesis at the leanspec twin; (c) is the
two-witness S8.4 TERMINAL claim and NO MORE.)

**DEPENDS.** C.43 · C.52 · C.53 (the box hypothesis's carrier) · C.71 · C.72 · C.73.

**PROOF (route).** (a): the single-extraction sum computation (`EFF.GENTOW3.21`'s proof
route). (b): S8.1's three-step chain, transcribed with its audit (`wt ≥ μ₂E₂+1` →
ledger `≥ (μ₂−j)E₂+1` → `+kδ` with `k ≥ 1` → `≥ Θ_j + 1`). (c): the two committed witness
pairs as constructed instances (`decide`-grade data at the FR-M3/PE1 frames).

**SIZE.** 3 × ~35 lines.

**SOURCE.** `EFF.GENTOW3.21` ((iv) with the in-statement `[GT3-r2]` pin — the only
statement-internal edit of that arc; the THREE supersessions on this one clause
enumerated); `.58` (S8.1 TERMINAL, with the boundary member sitting exactly on the repaired
hypothesis edge); `.59`/`.62` (CHAIN-NONFUNC: S8.2 SUPERSEDED, S8.4 TERMINAL); `.61` (the
activation disclosure — carried verbatim in the docstring per its own OPEN-CALL).

**TEETH.** SHARP 11 rows (the certificate at four families) + the FR-M3 separation pin +
the PE1 triple → **executable regressions** retained; the δ = 1 regime's refuted
per-member claim (`.30`: "the FIRST leaf height is already unfaithful" REFUTED — the
measured member decides faithfully AT `Θ_0` with identical hulls) → recorded as the
NEGATIVE control row in §16's table: (a) is certificate-scoped precisely because of it.

**ENVIRONMENT.** ENV-C1 ((a)/(b)); ENV-C3 ((c) reads σ).

---

### NODE C.75 [theorem] [fresh]

**STATEMENT.** *COROLLARY GENTOW-3.C: the entry/event band is shadow-faithful at EVERY
genre — item (3)'s parenthetical discharged.* On `𝒯`: (1) the level-1 coefficients `A_J`
have degree `< D′`, so the mod-`Φ′` projection is the identity on them — the entry read is
discrepancy-free outright; (2) at the composed frame, the event data occupies `dv₂`-heights
`≤ (μ₂−j)E₂ = Θ_j − δ < Θ_j` per coordinate, so C.72(ii) gives digit agreement on the whole
band, for every genre (`δ ≥ 1` unconditional on `𝒯`). Hence GENHN-T(b)′(iv)'s sentence
"this inequality HOLDS at the entry/event band" is a THEOREM.

**SIGNATURE** [signed: A-C.1 — elaborated in `leanspec/Leanspec/ChapC.lean`; the band
`m ≤ (μ₂−j)E₂ = Θ_j − δ < Θ_j`]:
```lean
theorem entry_band_faithful … {m : ℕ} (hm : m ≤ (μ₂ - j) * T.E₂)
    (hval : dv2Hgt (T.levelDatum hπ) (dev (composedKey T) f j) = (m : ℕ∞)) :
    dv2Hgt (T.levelDatum hπ) (shadowDev T f j) = (m : ℕ∞) ∧
    dv2Res (T.levelDatum hπ) (shadowDev T f j)
      = dv2Res (T.levelDatum hπ) (dev (composedKey T) f j)
```

**DEPENDS.** C.50 · C.52 · C.71 · C.72.

**PROOF.** (1) degree-level, no threshold; (2) `omega` on `(μ₂−j)E₂ < Θ_j` + C.72(ii).

**SIZE.** 20 lines.

**SOURCE.** `EFF.GENTOW3.29` (verbatim, incl. the two-leg structure and the discharge
sentence); the upgrade is NOT landed on GENHN in the corpus (`.42` N1) — the Lean node IS
the landing, and §14's DAG rows record the retirement of that dangling arc.

**TEETH.** ENTRY 274 — with the note's own disclosure carried: "entailed by FLOOR 274
given `δ ≥ 1` — honest as COR 3.C's machine face, not independent evidence" (`disclosed
non-independence`, §16 table row).

**ENVIRONMENT.** ENV-C1.

---

### NODE C.76 [lemma] [fresh]

**STATEMENT.** *GENTOW-4.1: the level-2 datum at PARTIAL sides (four clauses).* In the
partial-side setting (`f` monic, `Squarefree f`, the standing peels done, the inner side
`(u₂, e₂)` of the level polygon PARTIAL: `e₂f₂μ₂* < μ₁` allowed):
(a) **[floor, every side]** every side of the level polygon has `dv`-slope `> D′h`
(side-blind — the `[r1]` node-floor derivation); in particular every sibling slope
qualifies as a level-2 datum slope;
(b) **[`ψ₂(0) ≠ 0` via vertex attainment]** the residual of EVERY side has nonzero
constant term — both endpoints of every side are vertices, hence ATTAINED pins (argmin
endpoints are attained by C.07/C.26's machinery — the hull-free form of "a vertex of a
lower hull of an integer point set is a point of the set"); so `(κ₂, r̃)` is a level-2
datum over the frame with NO full-side hypothesis (C.44 re-fires with this in place of
HETOW-1(a)'s full-side endpoint step);
(c) **[key bridge]** `IsTestKey`-hood of `composedKey T` holds verbatim at partial sides
(C.47's proof is side-blind — the corpus routes this through the restated HETOW-2's
`w = 0` disjunct; the m-A supply audit is discharged by construction here: our C.47 IS the
"own statement form at `W = 0`");
(d) **[frame peels]** if `F.key ∣ f` then it divides exactly once (`Squarefree`),
contributing `typeOf`-entry `(e₁, f₁)` (B's leaf read at the frame key — via §7's C.61 at
the degenerate level datum), and the read continues on `f / F.key`; if `composedKey T ∣ f`
likewise via C.40's peel at key `Φ₂` (licensed by (c)), contributing `(e₁e₂, f₁f₂)` and
dropping `μ₂*` by 1.

**SIGNATURE** [signed: A-C.1 — elaborated in `leanspec/Leanspec/ChapC.lean`; split → 2 as
(a)+(b) = `partial_floor_and_datum` (with the frame-OPENING hypothesis `hopen` — the
left-endpoint pin above the `μ₁·D′h` line, which is what the R9 derivation reads) and (d)'s
core = `partial_frame_peel`; **(c) IS C.47** (its proof is side-blind — the m-A discharge),
consumed by name, not re-signed]:
```lean
theorem partial_floor_and_datum {F : KeyFrame O π} {H₀ : ℕ} (hpin : F.Pin H₀) …
    (hopen : (((f.natDegree / (F.e₁ * F.f₁)) * ((F.e₁ * F.f₁) * F.h) : ℕ) : ℕ∞)
      < dvHgt F f 0)
    {u ℓ : ℕ} … (hne : (dvSideSet F f u ℓ).Nonempty) (hdeg : 0 < dvSideDeg F f u ℓ hne) :
    ℓ * ((F.e₁ * F.f₁) * F.h) < u ∧
    ∀ (M₀ : ℕ) (hp : dvHgt F f (dvSideMin F f u ℓ hne) = (M₀ : ℕ∞)),
      (dvResPoly F H₀ hpin f u ℓ hne M₀ hp).coeff 0 ≠ 0 ∧
      (dvResPoly F H₀ hpin f u ℓ hne M₀ hp).natDegree = dvSideDeg F f u ℓ hne

theorem partial_frame_peel … (hdvd : F.key ∣ f)
    (hbox : ∀ g' ∈ monicFactors F.key, F.f₁ ∣ inertiaDegOf g') :
    typeOf F.key = ⟨{(F.e₁, F.f₁)}⟩ ∧ ¬ F.key ^ 2 ∣ f
```

**DEPENDS.** C.07 · C.26 · C.30 · C.40 · C.44 · C.47 · C.61.

**PROOF (route).** (a): the R9-corrected node-floor derivation (side-blind, as quoted at
`EFF.HE6R1.04`: every pin strictly above the slope-`D′h` line). (b): argmin endpoints are
attained (`min'`/`max'` membership) + C.26(ii)'s endpoint nonvanishing; then
`ψ₂^{μ₂*} ∣ R` with `R(0) ≠ 0` forces `ψ₂(0) ≠ 0`. (c): C.47's proof audit — no step reads
the side length. (d): `Squarefree` + C.61/C.40.

**SIZE.** 2 × ~35 lines.

**SOURCE.** `EFF.GENTOW4.11`–`.14` (the four clauses, verbatim, incl. `.13`'s dated
re-pointing bracket and m-A's supply correction — CHAIN-SUPPLY TERMINAL: HE7-13′ supplied
"by its own statement form at `W = 0`", which in this chapter is C.47 itself);
`EFF.GENTOW4.15` (the proof, incl. the HETOW-1 dependency audit); `.16` (the REMARK fence:
at a partial side the inner side's left endpoint is an interior vertex — carried in (b)'s
docstring).

**TEETH.** FR-G (the naive-key failure measured AT `dv₂ = T₂` exactly) + T-5 WRONGKEY
(incl. the key-∣-f peel corner) → retained; PE2-P's hull `(0,13)–(1,10)–(5,0)` (the
interior-vertex witness) → §13 regression row.

**ENVIRONMENT.** ENV-C2.

---

### NODE C.77 [theorem] [fresh]

**STATEMENT.** *GENTOW-4.A(i)+(ii): the bouquet and the projection at partial sides.*
(i) **[bouquet]** `f` factors as `∏_{(κ,r)} f_{κ,r}` over the label classes — supplied
closure-free by C.33 + C.34 applied side by side (the corpus's route through LEMMA
HE7-6/HE7-11's Galois stability has NO node; the dissections deliver the same
factorization), with `D′·ℓ·d_r ∣ deg f_{κ,r}`;
(ii) **[projection]** fix the inner class block `f_S := blockFactor` at `(κ₂, r̃)`,
`g := f / f_S`, and the `Φ₂`-development of `f` (length `M = ⌊n/D₂⌋ ≥ μ₂*`, **`C_M` monic
of degree `n − M·D₂ < D₂`, the constant `1` exactly when `D₂ ∣ n`; the partial-side
signature is `n > μ₂*·D₂`** — the TOWERRAT2-C display of record; the frozen "top
coefficient NOT monic" parenthetical is FALSE and DEAD). Then: `c_g` is the constant of
C.36; `deg f_S = D₂·μ₂*` where `μ₂* := Σ_{λ₂>T₂} L_{λ₂}(P₂(f))`; the slope-`>T₂` part of
`P₂(f)` is the INITIAL segment of the level-2 argmin structure, spans abscissas
`[0, μ₂*]`, and equals `P₂(f_S)` translated up by `c_g` — C.37/C.64's law re-fired at the
partial side; per side the residuals agree up to the `K₂^×` scalar `γ_g` (C.38/C.39).

**SIGNATURE** [signed: A-C.1 — elaborated in `leanspec/Leanspec/ChapC.lean`; (i)'s bouquet
IS the C.33 + C.34 chain applied side by side (consumed by name — the closure-free supply
the STATEMENT records); (ii) signed at the TOWERRAT2-C monic-signature core + the block
degree; the translation/scalar clauses are C.37/C.38/C.39/C.64's, already signed]:
```lean
theorem partial_projection … (hctx : BlockContext (T.levelDatum hπ) f) :
    (dev (composedKey T) f (f.natDegree / T.D₂)).Monic ∧
    ((T.D₂ ∣ f.natDegree) → dev (composedKey T) f (f.natDegree / T.D₂) = 1) ∧
    (blockFactor (T.levelDatum hπ) f).natDegree = T.D₂ * mult₂ (T.levelDatum hπ) f
```

**DEPENDS.** C.33 · C.34 · C.35 · C.36 · C.37 · C.38 · C.39 · C.64 · C.65 · C.76.

**PROOF (route).** (i): C.33 (slopes) then C.34 (residual factors) per side. (ii): the
initial-segment claim by argmin-slope monotonicity (the corpus's convexity argument at the
cleared carrier: attained slopes strictly decrease left to right); the span from `f_S`'s
own C.65; the translation from C.37.

**SIZE.** 2 × ~40 lines.

**SOURCE.** `EFF.GENTOW4.18`/.19 (verbatim); `.57` (TOWERRAT2-C — CHAIN-MONIC TERMINAL:
the corrected `C_M` display, with the note's own witness `C₂ = Φ′ + 4 = x² + 2`, monic,
refuting the frozen parenthetical); `.23` (the proof's geometric core, whose `C_M` clause
was right where the statement's parenthetical was wrong).

**TEETH.** P-1 parse gate + T-3 SIBDROP 117/117 (tower-class-only σ ≠ PARI on every
member — the bouquet is NEEDED) + P-4 (segment `= [0, μ₂*]`, `c_g` at the right endpoint)
+ T-2 NOCG 49 kills (the translation is load-bearing) → all retained; §13 fires PE2-P's
frame (`c_g = 5, p^S = (23,11)`, floors `(21,11)`).

**ENVIRONMENT.** ENV-C2.

---

### NODE C.78 [theorem] [fresh]

**STATEMENT.** *GENTOW-4.A(iii)+(iv): the per-block decision from `f`'s own development,
and the class recursion.* (iii) the composed dictionary fires on `f_S` at `(κ₂, r̃)` with
key `Φ₂` — every side of `P₂(f_S)` has slope `> T₂` with `Σ L_{λ₂} = μ₂*`; each
irreducible `r₂` of a separable level-2 residual gives ONE irreducible factor with
`(e, f) = (e₁e₂ℓ₂, f₁f₂·deg r₂)` (C.49/C.62's dictionary, partial-side entry) — **and
every input to the decision is computed from `f`'s OWN development: `f_S` is never
exhibited** (C.77(ii)'s translation + scale-invariant consumption of residuals);
(iv) every other class `C_{κ,r}` is priced by the same clauses at ITS datum: `μ₂*(κ,r) = 1`
⟹ one irreducible factor with `(e,f) = (e₁ℓ, f₁d_r)` (§7's C.63 — "THEOREM HE6.A's
dictionary recovered through the level-2 read", a consistency the corpus flags as two
proofs of one statement); repeated with `ℓd_r = 1` ⟹ the α-refine family (C.56/C.57);
repeated with `ℓd_r ≥ 2` ⟹ ITSELF a tower class, read by this same theorem (partial
side) or C.48/C.49 (full side) — the recursion is genuine. `σ(f)` = the disjoint union
over classes plus the peels.

**SIGNATURE** [signed: A-C.1 — elaborated in `leanspec/Leanspec/ChapC.lean`; (iii) signed
with EVERY read on `f`'s OWN development (`dv2SideSet`/`dv2ResPoly` of `f`, never of the
unexhibited block — the computability content in the statement itself); (iv)'s recursion
routing IS C.30's trichotomy per class (consumed by name, not re-signed)]:
```lean
theorem partial_block_decision … (hctx : BlockContext (T.levelDatum hπ) f)
    {u₃ ℓ₃ : ℕ} … (hne₃ : (dv2SideSet (T.levelDatum hπ) (composedKey T) f u₃ ℓ₃).Nonempty)
    (hsep : (dv2ResPoly (T.levelDatum hπ) (composedKey T) f u₃ ℓ₃ hne₃).Separable)
    {r₂ …} (hdvd : r₂ ∣ dv2ResPoly (T.levelDatum hπ) (composedKey T) f u₃ ℓ₃ hne₃) :
    ∃ g : Polynomial O, g.Monic ∧ g ∣ blockFactor (T.levelDatum hπ) f ∧
      g.natDegree = (F.e₁ * T.e₂ * ℓ₃) * (F.f₁ * T.f₂ * r₂.natDegree) ∧
      (<the two box hypotheses> → typeOf g = ⟨{(F.e₁ * T.e₂ * ℓ₃, F.f₁ * T.f₂ * r₂.natDegree)}⟩
        ∧ Irreducible g)
```

**DEPENDS.** C.30 · C.49 · C.56 · C.57 · C.62 · C.63 · C.76 · C.77.

**PROOF (route).** (iii): instantiate the level-2 machinery at `f_S` through C.77(ii)'s
computability; the m-B row accounting (three rows replaced by 4.1(a)(b)+(ii), two
discharged by 4.1(d)'s peels — "No row is undischarged") is transcribed as the proof's
hypothesis-discharge checklist. (iv): C.30's trichotomy per class.

**SIZE.** 2 × ~35 lines.

**SOURCE.** `EFF.GENTOW4.20`/.21 (verbatim, incl. the m-B rider and the recursion fence);
`EFF.GENTOW4.52` (m-B, CHAIN-COUNT TERMINAL — the two-partition reconciliation of the
fullness rows).

**TEETH.** P-2 HEADLINE 117/117 (every member decided, σ = PARI both routes) → retained;
FR-M (first machine contact of the recursion) + FR-3B (first three-block instance) →
retained; §13 fires one recursion row.

**ENVIRONMENT.** ENV-C3.

---

### NODE C.79 [theorem] [fresh]

**STATEMENT.** *GENTOW-4.A(v): the `μ₂* = 2` decision table (translation/scale-invariant).*
If `μ₂* = 2`, the block decision is complete on `f`'s own data, by the five-row table:
TWO sides (distinct slopes) → `{(e₁e₂, f₁f₂)} ×2`; ONE side at `ℓ₂ = 2` (half-integer
slope) → `{(2e₁e₂, f₁f₂)}`; ONE side, integer slope, `γ_g`-scaled residual irreducible
quadratic → `{(e₁e₂, 2f₁f₂)}`; split (two `K₂`-roots) → `{(e₁e₂, f₁f₂)} ×2`; double root →
α-refine, repeat (terminating — the refine chain finiteness via the `EFF.HE7.<nn> —
LEMMA HE7-8/13 [supplied-by: chapter E]` placeholder). Slopes are translation-invariant;
root/irreducibility tests invariant under the `K₂^×` scaling — which is exactly why the
decision is computable from `f` alone.

**SIGNATURE** [signed: A-C.1 — elaborated in `leanspec/Leanspec/ChapC.lean`; the five rows
as the inductive case tag `Mu2TwoCase` (twoSides/halfInteger/inertQuadratic/split/
doubleRoot — GC-4's domain licence), σ per case with each case's own box premise INSIDE its
conditional, the doubleRoot case delivering the α-refine event data (C.56/C.57's carriers)]:
```lean
inductive Mu2TwoCase where
  | twoSides | halfInteger | inertQuadratic | split | doubleRoot

theorem partial_mu2star_two_decision … (hm2 : mult₂ (T.levelDatum hπ) f = 2)
    (hbox1 : ∀ g' ∈ monicFactors (blockFactor (T.levelDatum hπ) f),
      CBox1Side (T.levelDatum hπ) g') :
    ∃ c : Mu2TwoCase, <per-case σ clauses; full text at the leanspec twin>
```

**DEPENDS.** C.38 · C.39 · C.56 · C.57 · C.62 · C.77 · C.78 · the HE7-8/13 placeholder.

**PROOF (route).** the three shapes of a `[0,2]` segment; each case is a C.62 instance or
a refine step; invariances from C.37/C.39.

**SIZE.** 40 lines.

**SOURCE.** `EFF.GENTOW4.22` (verbatim, five-row display); `.40` (the unlocked GENHN.B
cite: "(v) for inner-μ₂ = 2 partial leaves at pure-power sides — with GENTOW4-BOX-1 named
at mixed sides"; in this chapter the mixed-side name resolves to C.67's closure).

**TEETH.** the battery IS a μ₂ = 2 battery (117 members exercise exactly this clause) →
retained; T-2 NOCG (the translation-free alternative fails 49×) → retained.

**ENVIRONMENT.** ENV-C3.

---

### NODE C.80 [theorem] [fresh]

**STATEMENT.** *GENTOW-4.2 + the mixed routing: the tie at pure-power sides,
unconditionally.* If the inner side's residual is a pure power (`R_{κ₂} = c·ψ₂^{μ₂}`,
`c ∈ K^×`) then `μ₂* = μ₂` and `deg f_S = D₂·μ₂` — the two-count identity: the side
carries `D′·L_side` worth of degree (C.70's conservation), all of it in the one class
(the only irreducible factor is `ψ₂`), against `deg f_S = D₂·μ₂*` (C.64); divide. **At a
MIXED side the read is UNCHANGED** (μ₂* computed from `f`, the decision fires — C.77/C.78)
**and the tie `μ₂*(r) = m_r` is C.67** (cite-conditional; the corpus's honest box
`GENTOW4-BOX-1` and its "Ore-II / FGMN Lemma 2.17 content" attribution are exactly what
C.66/C.67 landed) — this node states the pure-power case with NO cite and routes the
mixed case by name.

**SIGNATURE** [signed: A-C.1 — elaborated in `leanspec/Leanspec/ChapC.lean`; the pure-power
hypothesis with the `K^×`-scalar existential (the corpus's `c·ψ₂^{μ₂}`); the mixed re-export
IS C.67 by name]:
```lean
theorem tie_pure_power … (hctx : BlockContext (T.levelDatum hπ) f) {μ₂ : ℕ} (hμ₂ : 0 < μ₂)
    (hres : ∀ (hne : (dvSideSet F f T.u₂ T.e₂).Nonempty) (M₀ : ℕ)
      (hp : dvHgt F f (dvSideMin F f T.u₂ T.e₂ hne) = (M₀ : ℕ∞)),
      ∃ c : F.stageField H₀ hpin, c ≠ 0 ∧
        dvResPoly F H₀ hpin f T.u₂ T.e₂ hne M₀ hp = Polynomial.C c * (towerLabel T) ^ μ₂) :
    mult₂ (T.levelDatum hπ) f = μ₂ ∧
    (blockFactor (T.levelDatum hπ) f).natDegree = T.D₂ * μ₂
```

**DEPENDS.** C.34 · C.64 · C.70 · C.67 (the mixed re-export only).

**PROOF.** the corpus's division argument, closure-free: degree conservation on the side
(C.70) + single-class residual (C.34's uniqueness at one irreducible factor) + C.64.

**SIZE.** 24 lines.

**SOURCE.** `EFF.GENTOW4.24` (verbatim, incl. the two-count audit); `.25` (the mixed
fence, verbatim — its "this corpus has not proved" clause is now dated: GENTOW6/C.67
closed it cite-conditionally; §16's table records the box's closure chain
`HYP.144 → EFF.GENTOW6.07 → C.67`).

**TEETH.** P-3 (`μ₂* = 2 = μ₂` on every pure-side member) + FAM-P5 read-mode (mixed:
every decision PARI-exact, tie checked EMPIRICALLY — the empirical row stays as the
regression guarding C.67's cite) → retained.

**ENVIRONMENT.** ENV-C2.

---

### NODE C.81 [theorem] [fresh]

**STATEMENT.** *COROLLARY GENTOW-4.C: the `c_g`-read — absolute block pins from `f`'s
digits.* In C.77(ii)'s setting: `c_g` = the height of `P₂(f)` at abscissa `μ₂*` (the right
endpoint of the `>T₂` initial segment), and the block pins are `p_j^S = p_j − c_g`
wherever `(j, p_j)` lies on the `>T₂` argmin structure — with the equality's citation
COMPLETED per m-i: at argmin vertices by attainment (C.76(b)'s mechanism at the level-2
pin set), at side-INTERIOR abscissas through the residual scalar (C.68). Consequently
GENTOW-1(c)'s node floors are VISIBLE THROUGH THE PROJECTION:
`p_j^S ≥ (μ₂* − j)·E₂ + 1` for `j < μ₂*` (C.54(c) applies to `f_S`, whose entry is
full-side by construction).

**SIGNATURE** [signed: A-C.1 — elaborated in `leanspec/Leanspec/ChapC.lean`; the
right-endpoint identity `c_g = p_{μ₂*}` + the shifted floors visible through the
projection]:
```lean
theorem cg_read … (hctx : BlockContext (T.levelDatum hπ) f)
    (hnd : ¬ composedKey T ∣ blockFactor (T.levelDatum hπ) f) :
    dv2Pin (T.levelDatum hπ) (composedKey T) f (mult₂ (T.levelDatum hπ) f)
      = (complementConst (T.levelDatum hπ) f : ℕ∞) ∧
    ∀ j, j < mult₂ (T.levelDatum hπ) f →
      (((mult₂ (T.levelDatum hπ) f - j) * T.E₂ + 1
          + complementConst (T.levelDatum hπ) f : ℕ) : ℕ∞)
        ≤ dv2Pin (T.levelDatum hπ) (composedKey T) f j
```

**DEPENDS.** C.37 · C.54 · C.64 · C.68 · C.76 · C.77.

**PROOF.** right endpoint from C.77(ii)'s span; translation from C.37; interior equality
from C.68; the floor transport through `f_S ∈ 𝒯` at the datum
`(Q; e₁, f₁, e₂f₂·μ₂*; h)`.

**SIZE.** 26 lines.

**SOURCE.** `EFF.GENTOW4.26` (verbatim, incl. the PE2-P values `c_g = 5, p^S = (23,11)`,
floors `(21,11)`, `j = 1` exact); `.33` (m-i — the completed citation, CHAIN-CG-CITE
TERMINAL); `.27` (the floor-transport route).

**TEETH.** P-4 (floors through the projection, every row) → retained; PE2-P's numbers →
§13 regression.

**ENVIRONMENT.** ENV-C2.

---

### NODE C.82 [theorem] [fresh]

**STATEMENT.** *GENTOW-6.2 + COR 6.2C: block budgets through the projection (the BUDGET
half ONLY).* The GENTOW-1 budget fibration (C.52/C.53) transports to the block factor at a
partial side: the block's digit box is the `𝒯`-box of `f_S`'s own full-side datum, read
through C.81's `c_g`-shift — per window `N`, the block's free-digit count is the clipped
sum at the shifted floors. **The LEDGER/COUNT half is NOT here** — it was `GENTOW6-BOX-2`
in the corpus and its Lean home is §11's count layer at exactly the strength proved there;
a fleet agent must not read "block budgets" as a count law (the corpus's own fence,
verbatim: "the split is explicit … a consumer must not read 'block budgets PROVED' as a
count law").

**SIGNATURE** [signed: A-C.1 — elaborated in `leanspec/Leanspec/ChapC.lean`; the BUDGET
half as the block-locus class count at the block's own full-side datum; the LEDGER/COUNT
half stays §11's (the corpus's fence, verbatim in the STATEMENT). ⚠ A-C.1 DEPENDS
correction: the 6.2C(d) cap supplier is **C.95** (the 𝒯-free cap), not C.89 — the committed
DEPENDS entry was a numbering slip, recorded in the A-§ block]:
```lean
theorem block_budget … (hctx : BlockContext (T.levelDatum hπ) f)
    (hnd : ¬ composedKey T ∣ blockFactor (T.levelDatum hπ) f) (N : ℕ) :
    Nat.card {c : Coeff O (T.D₂ * mult₂ (T.levelDatum hπ) f) N //
        ∃ a, proj O (T.D₂ * mult₂ (T.levelDatum hπ) f) N a = c ∧
          monicPoly a ∈ towerLocus T (mult₂ (T.levelDatum hπ) f)}
      = residueCard O ^ towerFreeCount T (mult₂ (T.levelDatum hπ) f) N
```

**DEPENDS.** C.52 · C.53 · C.77 · C.81 · C.89 (§9's 𝒯-free cap — the 6.2C(d) leg only).

**PROOF (route).** compose the fibration with the projection; the shift is a bijection on
digit boxes (triangular-unimodular composed with a translation).

**SIZE.** 30 lines.

**SOURCE.** `EFF.GENTOW6.11` (verbatim, incl. the PROVED-budget/BOX-2-ledger split and
the 6.2C supplier-chain repair route).

**TEETH.** PE2's walk ("nothing narrows") → retained; §13 fires one block-budget row.

**ENVIRONMENT.** ENV-C2.

---

---

## 9. §9 — THE THIRD STAGE, THE THRESHOLDS, TERMINATION, AND THE CAPS

> **Design note.** GENTOW5 at its acceptance scope: the third stage (first live `n = 16`),
> depth ≥ 4 NOT claimed (the FP-4 fences transcribed as statement hypotheses). Its TERMINAL
> layers are heavy (C-H8): GENTOW5-D's two-directional closure WITHDRAWN (S11.1 — forward
> direction only), the K_i-digit lift's threshold at `bound_i` (S12.2), clause (b)'s
> residual display re-indexed twice (S11.5 + the post-D3i `ω_{j−1}` corrigendum), and —
> the section's central honesty object — **`[GENTOW5-W(i)]`, the OPEN transported lemma**
> (`u_i(β_t) = θ_i(t)·w_i^{f_{i+1}−t}`), with `𝒲_{≤n} := ⋀_{3≤q≤n} [GENTOW5-W(q)]`
> conditioning every clause (a)/(b)/(c)/(e) leg at `n ≥ 3` (S12.1 WITHDREW the contrary
> "w-blind ⟹ unconditional" claim). C.89 carries `𝒲` as the NAMED hypothesis family —
> Display A's `(H-VARTHETA-RES)_i ∧ 𝒲_{≤i}` conjunct is supplied to chapters E and I from
> there. The ϑ/θ reciprocity (`θ_i(t) = ϑ_{i,f_{i+1}−t}^{-1}` — "same monomial quotient,
> inverse read") is GC-14's fourth row: cited to the D-table anchor, stated here only in
> normalizer-ratio form. GENTOW6's caps/attainment layer closes the section (A-§8's
> relocation).

### NODE C.83 [def] [fresh]

**STATEMENT.** *The depth-`r` tower datum (DEF GENTOW5-1).* Over the fixed bundle: stage
data `(e_i, f_i, ψ_i)` for `i = 1 … r` with **properness** `l_i := e_i·f_i ≥ 2` at every
`i ≥ 2` (an improper stage is a refinement, not a level); `ê_i := e_1⋯e_i`,
`D_i := l_1⋯l_i`; the ladder `dv_i := ê_i·v`; heights `u_1 := h`,
`u_{i+1}` with `Nat.Coprime u_{i+1} e_{i+1}`; side constants `E_i := e_i·f_i·u_i`
(`E_1 = D_1·h`); the **floor chain** `u_{i+1} > e_{i+1}·E_i` **as a datum field** (its
automatic derivation at leaves is C.91(e), conditional at `n ≥ 3` — S12.1's carve-out:
"later arguments may still use that inequality unconditionally when it is included
explicitly in the fixed tower datum"); the **normalizer recursion**
`n̂_{i+1}(k) := n̂_i(m_i(k))·Φ_i^{b_i(k)}` with `e_{i+1}·m_i(k) + b_i(k)·u_{i+1} = k`,
`0 ≤ b_i(k) < e_{i+1}` (unique by coprimality; at `i = 2` this is §6's `n̂₂` verbatim);
the **cocycle** `τ_i(a,b) := n̂_i(a)n̂_i(b)/n̂_i(a+b)`-exponent data and **letters**
`Λ_i := Φ_i^{e_{i+1}}/n̂_i(u_{i+1})`-exponent data (carried as exponent bookkeeping, never
as fraction-field elements — the C.15/C.28 discipline iterated); and the iterated residue
fields `K_i` (C.12's `AdjoinRoot` chain — GC-7's depth-≥ 3 note applies: if the instance
chain fails to elaborate, the recorded fallback triggers a DECISION here).

**SIGNATURE** [signed: A-C.1 — elaborated in `leanspec/Leanspec/ChapC.lean`, fragile no. 1].

**⚠ DECISION A-C.1/GC-7 (the depth-≥ 3 carrier fallback, TAKEN — the DECISION block GC-7
mandates).** The literal iterated-`AdjoinRoot` telescope cannot be structure fields (the field
`ψ_{i+1} : Polynomial K_i` with `K_{i+1} := AdjoinRoot ψ_{i+1}` is a dependent telescope no
Lean `structure` carries — exactly the elaboration failure GC-7's depth-≥ 3 note anticipates).
GC-7's recorded fallback is taken: the `K_i` are abstract field data with the iterate
witnessed by `RingEquiv` fields (`base : fld 1 ≃+* stageField`;
`step : fld (i+1) ≃+* AdjoinRoot (ψ i)`). Arithmetic data is ℕ-total with range-scoped
hypothesis fields; stage `1` IS the frame; `towerNorm i k` solves the level-`(i+1)`
normalizer's exponent data (so `towerNorm 1` is §6's `n̂₂` verbatim).

```lean
namespace Uniformity.Density.Tower

def towerSolve (u e k : ℕ) : ℕ :=
  ((List.range e).find? (fun b => (b * u) % e == k % e)).getD 0

structure DeepTower (F : KeyFrame O π) (H₀ : ℕ) (hpin : F.Pin H₀) (r : ℕ) where
  e : ℕ → ℕ
  f : ℕ → ℕ
  u : ℕ → ℕ
  fld : ℕ → Type*
  fldField : ∀ i, Field (fld i)
  ψ : (i : ℕ) → Polynomial (fld i)
  he1 : e 1 = F.e₁
  hf1 : f 1 = F.f₁
  hu1 : u 1 = F.h
  he : ∀ i, 1 ≤ i → i ≤ r → 0 < e i
  hf : ∀ i, 1 ≤ i → i ≤ r → 0 < f i
  hproper : ∀ i, 2 ≤ i → i ≤ r → 2 ≤ e i * f i
  hcop : ∀ i, 2 ≤ i → i ≤ r → Nat.Coprime (u i) (e i)
  hfloor : ∀ i, 1 ≤ i → i < r → e (i + 1) * (e i * f i * u i) < u (i + 1)
  hψ : ∀ i, 1 ≤ i → i < r →
    (ψ i).Monic ∧ Irreducible (ψ i) ∧ (ψ i).natDegree = f (i + 1) ∧ (ψ i).coeff 0 ≠ 0
  base : fld 1 ≃+* F.stageField H₀ hpin
  step : ∀ i, 1 ≤ i → i < r → (fld (i + 1) ≃+* AdjoinRoot (ψ i))

attribute [instance] DeepTower.fldField

def DeepTower.ehat (T : DeepTower F H₀ hpin r) (i : ℕ) : ℕ := ∏ j ∈ Finset.Icc 1 i, T.e j
def DeepTower.Dcum (T : DeepTower F H₀ hpin r) (i : ℕ) : ℕ :=
  ∏ j ∈ Finset.Icc 1 i, (T.e j * T.f j)
def DeepTower.Econst (T : DeepTower F H₀ hpin r) (i : ℕ) : ℕ := T.e i * T.f i * T.u i

def DeepTower.towerNorm (T : DeepTower F H₀ hpin r) : (i : ℕ) → ℕ → ℕ × ℕ × (Fin i → ℕ)
  | 0, k => ((k - F.slotIdx k * F.h) / F.e₁, F.slotIdx k, fun x => x.elim0)
  | i + 1, k =>
      let b := towerSolve (T.u (i + 2)) (T.e (i + 2)) k
      let m := (k - b * T.u (i + 2)) / T.e (i + 2)
      let p := towerNorm T i m
      (p.1, p.2.1, Fin.snoc p.2.2 b)

def DeepTower.towerShift (T : DeepTower F H₀ hpin r) (i m : ℕ) : ℕ :=
  towerSolve (T.u i) (T.e i) m
def DeepTower.towerCocycle (T : DeepTower F H₀ hpin r) (i a b : ℕ) : ℕ :=
  (T.towerShift i a + T.towerShift i b - T.towerShift i (a + b)) / T.e i

def DeepTower.trunc (T : DeepTower F H₀ hpin r) (i : ℕ) (hi : i ≤ r) :
    DeepTower F H₀ hpin i  -- every field re-scoped; body in the leanspec twin
```
(the letter/cocycle objects `Λ_i`/`τ_i` are carried as the `towerShift`/`towerCocycle`
exponent bookkeeping, per the STATEMENT's "never as fraction-field elements"; `trunc` is the
depth-restriction consumers use to instantiate level-general statements per rung.)

**DEPENDS.** C.01 · C.09 · C.12 · C.15/C.16 · C.28 · C.42 (the depth-2 instance this
extends).

**PROOF.** definitional; uniqueness of the recursion solve per rung = C.16's argument at
`(u_{i+1}, e_{i+1})`.

**SIZE.** 40 lines. **Split candidate:** the structure / the recursion defs.

**SOURCE.** `EFF.GENTOW5.14`–`.16` (verbatim, incl. the FGMN-collapsing gloss for
properness [via GENTOW2's dictionary — documentation only] and the `i = 2` verbatim
identification); `EFF.GENTOW5.21` (the worked pins `n̂₃(85) = 2⁸Φ₂`, `n̂₂(21) = 16Φ′` —
§13 regression values).

**TEETH.** P-B1/B2 ("floor chain tight, `u = 5, 21, 85, 341`") → §13 regression rows.

**ENVIRONMENT.** ENV-C1.

---

### NODE C.84 [def+lemma] [fresh]

**STATEMENT.** *The level-`i` weight and the K_i-digit flavor lifts (TERMINAL forms).*
(i) `wt_i` on exponent data `(v, a, J_1 … J_i)`: `ê_i·v + a·(ê_i/e_1)h + Σ_{j<i}
J_j·(ê_i/ê_{j+1})u_{j+1} + J_i·E_i` — the TOP variable priced at `E_i` (a LOWER bound, the
`[GT5-r1]` repair: the exact top value is only known `> E_i` by the field floor; the
docstring carries the asymmetry); `wt_i` consumes NO data beyond the depth-`i` datum.
(ii) the flavor monomials at the `[GT5-r2]` corrected display — the base RE-SOLVES per
flavor: `M_{r,t}(m) := n̂_i(m − Δ(r,t))·x^{e_1 r}·Φ_1^{e_2t_1}⋯Φ_{i−1}^{e_it_{i−1}}`,
`Δ(r,t) := e_1r·(ê_i/e_1)h + Σ_{j<i} e_{j+1}t_j·(ê_i/ê_{j+1})u_{j+1}`; exponents stay in
ladder range, `deg M_{r,t} < D_i`; a flavor is ABSENT when the ladder solve fails (the
negative-height proviso); `lift_i(c; m) := Σ d_{r,t}·M_{r,t}(m)` with inverse-twisted
digits, **valid for `m > bound_i`** (S12.2 TERMINAL: the display consumes the PRECEDING
lift instance — threshold `bound_i`, NOT `bound_{i+1}`; the S11.4 bracket is DEAD).

**SIGNATURE** [signed: A-C.1 — elaborated in `leanspec/Leanspec/ChapC.lean`;
`towerWeight`/`flavorMonomial` with REAL bodies over C.83's carrier (the flavor's base
RE-SOLVE via `towerNorm`, `[GT5-r2]`); `towerLift` stub-carried as an axiom constant (the
variable-length multi-index digit iteration is the fleet's body), its exact-height/`wt`
companions the fleet's, per the C.45/C.97 rule]:
```lean
def DeepTower.towerWeight (W : DeepTower F H₀ hpin r) (i v a : ℕ) (J : ℕ → ℕ) : ℕ :=
  W.ehat i * v + a * (W.ehat i / W.e 1) * W.u 1
    + (∑ j ∈ Finset.Icc 1 (i - 1), J j * (W.ehat i / W.ehat (j + 1)) * W.u (j + 1))
    + J i * W.Econst i

noncomputable def DeepTower.flavorMonomial (W : DeepTower F H₀ hpin r)
    (key : ℕ → Polynomial O) (i rr : ℕ) (t : ℕ → ℕ) (m : ℕ) : Polynomial O :=
  let Δ := F.e₁ * rr * (W.ehat i / W.e 1) * W.u 1
    + ∑ j ∈ Finset.Icc 1 (i - 1), W.e (j + 1) * t j * (W.ehat i / W.ehat (j + 1)) * W.u (j + 1)
  let p := W.towerNorm (i - 1) (m - Δ)
  Polynomial.C (π ^ p.1) * Polynomial.X ^ (p.2.1 + F.e₁ * rr)
    * ∏ j : Fin (i - 1), (key (j.1 + 1)) ^ (p.2.2 j + W.e (j + 2) * t (j + 1))

noncomputable def DeepTower.towerLift (W : DeepTower F H₀ hpin r)
    (key : ℕ → Polynomial O) (i m : ℕ) (s : W.fld i) : Polynomial O  -- axiom-constant stub
```

**DEPENDS.** C.83 · H.54–H.57 (the base lift, per C-H5) · C.56a (`k2DigitLift` — the
`i = 2` instance; the reconciliation lemma `towerLift`-at-depth-2 `= k2DigitLift` is this
node's companion).

**A-7 NOTE.** The lift entry formerly pointed at the pre-split parent theorem node,
closing an SCC; the def now lives at its own node and the edge points there.

**PROOF.** definitional + the range arithmetic (`i0′ + e_1r < D_1`,
`b_j′ + e_{j+1}t_j < l_{j+1}` — `omega`).

**SIZE.** 36 lines.

**SOURCE.** `EFF.GENTOW5.24` (the weight, `[GT5-r1]` TERMINAL); `.17` (the corrected
flavor display, verbatim, with the FR-A verification `n̂₂(14−3)·Φ₁ = 3⁵xΦ₁` and the
fixed-base non-existence `11/2 ∉ ℤ`); S12.2 via `.17`'s conditionality (the `bound_i`
rung).

**TEETH.** FA1-LIFT (22/0: fixed-base flavor non-existence + the re-solved member green)
→ **executable regression** + §13 row; the grid-4 equality instance (`170 = 170 = 170`)
→ retained (guards against any lean on top-carry strictness).

**ENVIRONMENT.** ENV-C1.

---

### NODE C.85 [theorem] [fresh]

**STATEMENT.** *The graded frame and the substitution theorem (GENTOW5-A0/A1/A) — the
general-`μ₂` layer-1 kills; GENTOW-BOX-1's mathematical content, RETIRED here.* Three
layers:
(A0) **the graded frame, abstract** (ENV-C4-style): for a field with a valuation, the
associated graded object has invertible nonzero homogeneous elements — `[a][b] = [ab] ≠ 0`
(mathlib `Valuation` carrier; the corpus's `gr(L₂)`; "pointwise, at a root, there is no
carry problem — carries are a phenomenon of the slot GRID");
(A1) **the ϑ-dictionary in normalizer-ratio form**: the coherent per-height digits `γ_j`
and the multiplicative-convention coefficients `c_j` differ by the FIXED units
`ϑ_t = res-ratio of n̂_i(λ)^t/n̂_i(tλ)` with the telescoping
`ϑ_{t+1} = ϑ_t·res(τ(tλ, λ))` (`ϑ_0 = ϑ_1 = 1`) — stated at C's own carriers via
C.21/C.28's reads; **the orientation is the D-table's RECIPROCAL row (GC-14): every
consumer cites the anchor `[ϑ-TABLE — supplied-by: chapter D]`, and this node states only
the ratio form**;
(A) **the substitution theorem**: at a composed stage-α event (one side of integer
`dv₂`-slope `λ > E₂`, residual `(T − s)^{μ₂}` in the multiplicative convention), the
refine `Φ₂⁺ := Φ₂ − lift(s; λ)` kills ALL `μ₂` pins: `dv2Pin … Φ₂⁺ f k > ((μ₂−k)λ : ℕ∞)`
for `k < μ₂` — Step A is the Taylor/substitution identity `R(T+w) = Σ_k [Σ_j binom(j,k)
w^{j−k}c_j]T^k` (an identity over ANY commutative ring, both characteristics —
binomial-free conclusion `(T−w)^{μ₂}|_{T→T+w} = T^{μ₂}`), Step B is the grid translation
(C.87's forward direction + the flow-up pricing `λ > E₂`). **This node supplies C.56's
general-`μ₂` leg** and lifts GENTOW-2's grade-note restriction.

**SIGNATURE** [signed: A-C.1 — elaborated in `leanspec/Leanspec/ChapC.lean`. **The ⚠
DECISION NOTE's recorded option is EXERCISED: A0 (`graded_frame`) is DROPPED** ("A0 is
scaffolding, not consumed content" — the node's own words); the split lands as
`theta_dictionary` (A1, at the C-carrier MULTIPLICATIVITY-DEFECT form: the fixed units θ
with `θ₀ = θ₁ = 1` are exactly what makes the coherent read multiplicative — the corpus's
γ/c dictionary in defect form) + `substitution_kills` (Step A as the binomial-free ring
identity over ANY `CommRing`, both characteristics; the grid leg is C.56's `refine_kills`,
already signed — the SUPPLIES arrow to C.56's general-`μ₂` leg stands)]:
```lean
theorem theta_dictionary … :
    ∃ θ : ℕ → AdjoinRoot (T.levelDatum hπ).r,
      θ 0 = 1 ∧ θ 1 = 1 ∧ (∀ t, θ t ≠ 0) ∧
      ∀ (s t : ℕ) (A B : Polynomial O),
        dv2Res (T.levelDatum hπ) A ≠ 0 → dv2Res (T.levelDatum hπ) B ≠ 0 →
        θ (s + t) * dv2Res (T.levelDatum hπ) (A * B)
          = θ s * θ t * (dv2Res (T.levelDatum hπ) A * dv2Res (T.levelDatum hπ) B)

theorem substitution_kills {R : Type*} [CommRing R] (μ : ℕ) (s : R) :
    ((Polynomial.X - Polynomial.C s) ^ μ).comp (Polynomial.X + Polynomial.C s)
      = Polynomial.X ^ μ
```

**⚠ DECISION NOTE (the A0 carrier).** The corpus's `gr(L₂)` lives on the completed leaf at
a root — closure-adjacent. The Lean route: A0 abstractly over `Valuation K Γ` (mathlib),
instantiated NOT at a leaf field but through the C.27 norm-form exactness — Step A's
"evaluate at `x₀`" becomes the multiplicative-residual bookkeeping over `K₂[T]` (a finite
field we have) with C.27 transporting values. If the stub stage finds the abstract
`Valuation` route heavier than a direct `K₂[T]`-computation, the formalizer may drop A0
entirely and prove `substitution_kills` from the Taylor identity + C.27 + C.87 alone —
A0 is scaffolding, not consumed content (the corpus's own framing). Recorded per GC-2's
DECISION-block discipline.

**DEPENDS.** C.11 · C.21 · C.27 · C.28 · C.52 (Step 0) · C.87 (forward direction) ·
C.84 (the lift).

**SUPPLIES (not a dependency — A-7).** C.56's general-`μ₂` leg (DAG order: this node
BEFORE C.56's general leg fires); the former DEPENDS entry naming C.56 was a supplies
annotation misfiled as a dependency and closed an SCC.

**PROOF (route).** `EFF.GENTOW5.10`'s two steps, verbatim route; the convention fence
(`EFF.GENTOW5.09`: at `μ₂ = 2`, char 2, the convention is invisible — every K₂-element a
square — C-H12's coincidence regime, transcribed in the docstring as the reason the
`μ₂ = 2` batteries never saw it).

**SIZE.** 3 × ~40 lines.

**SOURCE.** `EFF.GENTOW5.06` (A0 + proof); `.08` (A1 + the tower-side re-proof of
ANNEX-LEMMA R1-a(iii) — "reproved here in the tower's own letters rather than cited, since
the base conventions differ"; so NO HE7 placeholder is needed for THIS node's cocycle
residue law — C.39's placeholder remains only for the HE6R1-side scalar); `.09` (the
convention fence); `.10` (THEOREM GENTOW5-A, verbatim, both steps + the audited
char-independence); `.13` (S1.5: GENTOW-BOX-1 "RETIRED as a mathematical box; the residue
is grade-only" — the Lean node IS the retirement's formal content; no W-9-analogue weld
face is consumed, verbatim).

**TEETH.** P-A1/A2/A3 (the FIRST `μ₂ = 3` pointwise re-division kills in the program,
incl. a char-3 row and an `f₂ = 2` two-flavor row) + T-A1W/T-A2W (wrong height, wrong
digit) + T-A4W (the CONVENTION tooth: the naive-digit twin keeps its pin at 22) →
**executable regressions** retained; §13 fires one kill row per prime.

**ENVIRONMENT.** ENV-C4 (A0) / ENV-C3 (A1, A).

---

### NODE C.86 [lemma] [fresh]

**STATEMENT.** *COROLLARY GENTOW5-A′: GENTOW-2 closes at general `μ₂`; the level-1 rider.*
(i) C.56/C.57's clauses hold at general `μ₂`: (ii) = C.85; (iii) consumed layer 1 only
through (ii); (iv) is the SAME Step-A computation at the refined frame — reverse transport
with minimal class `binom(μ₂,j)w^{μ₂−j}`, char-sensitive exactly where `q ∤ binom(μ₂,j)`.
(ii) **the level-1 rider**: the S1 argument runs verbatim one level down (GENHN-BOX-2's
own retirement condition — "the GENH4-S5 computation at general `(e₁, f₁, μ)`"); recorded
as a DISPLAY node (the corpus claims nothing on frozen GENHN text; the Lean statement is
the level-1 instance of C.85, honest and self-contained — the consumption bookkeeping
against `HYP.148` is chapter I's).

**SIGNATURE** [signed: A-C.1 — elaborated in `leanspec/Leanspec/ChapC.lean`; (i) is a
RE-EXPORT (C.56/C.57's A-C.1 signatures already quantify general `μ₂` — no separate
statement needed, recorded); (ii) the rider as a REAL level-1 theorem over B's API]:
```lean
theorem substitution_kills_level1 (hπ : Irreducible π)
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [Finite (ResidueField O)]
    {φ : Polynomial O} (hφ : IsKey φ) {f : Polynomial O} (hf : f.Monic)
    {μ lam : ℕ} (hμ : 0 < μ) (hlam : 0 < lam) {s : resField φ} (hs : s ≠ 0)
    (hne : (sideSet φ f lam 1).Nonempty) {H₀ : ℕ}
    (hp : npHgt φ f (sideMin φ f lam 1 hne) = (H₀ : ℕ∞))
    (hres : resPoly π φ f lam 1 hne H₀ = (Polynomial.X - Polynomial.C s) ^ μ) :
    ∃ φ' : Polynomial O, φ'.natDegree = φ.natDegree ∧
      (φ - φ').natDegree < φ.natDegree ∧
      ∀ j < μ, (((μ - j) * lam : ℕ) : ℕ∞) < npHgt φ' f j
```

**DEPENDS.** C.56 · C.57 · C.85 · B §5–§7 (the level-1 carriers for the rider).

**PROOF.** re-export + the transport table (`gr(L₁)`, `GENHN-2` for `GENHN-2′`, GENH4
layer 2 for layer 2).

**SIZE.** 26 lines.

**SOURCE.** `EFF.GENTOW5.11` (verbatim, incl. the grade-note lift); `.12` (the rider, with
its "no new claim on frozen text" fence — transcribed as an honest new Lean theorem, which
is MORE than the corpus display but exactly what the display exhibits; flagged §16).

**TEETH.** P-A rows (the (i) instances); the rider is machine-unexercised in the corpus
(disposition: signed — the Lean proof is its first teeth).

**ENVIRONMENT.** ENV-C3.

---

### NODE C.87 [lemma] [fresh]

**STATEMENT.** *LEMMA GENTOW5-D, TERMINAL (one-directional).* For every level `i`: the
forward reduction moves (x-carry, `Φ_j`-carries) are `wt_i`-NONDECREASING; lift-generated
terms preserve weight exactly; INTERIOR carries' key-parts strictly raise it (floor rung
`j+1`, in-datum); the TOP carry's key-part PRESERVES it exactly (`E_i`-priced — no floor
rung consumed; at `i = 1` the only move IS the top carry, the `[GT5-r2]` edge).
**The two-directional closure ("all slots at weight ≥ W is the same condition on every
grid") is WITHDRAWN** (S11.1, CRITICAL — FALSE as written): the converse rewriting is
weight-NONINCREASING, with the single surviving remnant the SINGLE-STEP top-rung expansion
(weight-preserving). Named consumers use the forward direction only (S11.1's consumption
walk, verified: C.85 Step B, C.91(c) Steps 0/3, C.91(d)).

**SIGNATURE** [signed: A-C.1 — elaborated in `leanspec/Leanspec/ChapC.lean`, as the two
displayed carry computations uniform in `j` (arithmetic over the datum — the strict
interior raise from the floor chain; the exact top price `l_i·u_i = E_i`); **NO
two-directional statement exists** (S11.1's withdrawal honored — a stub matching the
withdrawn closure is a defect)]:
```lean
theorem towerCarry_interior_strict (W : DeepTower F H₀ hpin r) (i j : ℕ)
    (hj : 1 ≤ j) (hji : j + 1 < i) (hir : i ≤ r) :
    (W.e (j + 1) * W.f (j + 1)) * ((W.ehat i / W.ehat (j + 1)) * W.u (j + 1))
      < (W.ehat i / W.ehat (j + 2)) * W.u (j + 2)

theorem towerCarry_top_exact (W : DeepTower F H₀ hpin r) (i : ℕ)
    (hi : 1 ≤ i) (hir : i ≤ r) :
    (W.e i * W.f i) * ((W.ehat i / W.ehat i) * W.u i) = W.Econst i
```

**DEPENDS.** C.83 · C.84 · C.50/C.52 (the `i = 2` instance it must match — the corpus's
own cross-check: GENTOW1 Step 0 prices the `Φ₂`-part "at weight E2 exactly").

**PROOF (route).** the two displayed carry computations, uniform in `j`, with the audited
interior/top split; the `i = 1` edge clause.

**SIZE.** 40 lines.

**SOURCE.** `EFF.GENTOW5.25` (the `[GT5-r1]`/`[GT5-r2]` restated statement + proof +
failure-mode fence, verbatim; S11.1's withdrawal — CHAIN TERMINAL; the grid-4
`170 = 170 = 170` fence).

**TEETH.** `gentow5_af1_direction_check.py` (8/0, both directions) → **executable
regression** retained; the grid-4 equality → retained.

**ENVIRONMENT.** ENV-C5/C1.

---

### NODE C.88 [theorem] [fresh]

**STATEMENT.** *LEMMA GENTOW5-C: `(SLOT_i)` and `(LIFT_i)` up the tower.* By induction on
`i` (base `i ≤ 2` = B's slot layer + §4/§6's — accepted corpus recast as C.23/C.27/C.24
and C.58's mechanisms): for `ξ`-free consumers, the level-`(i+1)` slot value of
`C ∈ O[x]`, `deg C < D_{i+1}`, is the slot minimum EXACTLY (norm-form per C.27's carrier);
minimizing slots in one class mod `e_{i+1}`; the height-`k` residue is the displayed
`K_{i+1}`-combination `Σ_t γ_t ϑ_t β_i^t ≠ 0` (no cancellation — the `K_i`-basis leg,
H.53 iterated); and `(LIFT_i)`: `k`-uniformly above
`bound_{i+1} = (l_{i+1}−1)·u_{i+1} + e_{i+1}·bound_i` (the PE5-F-3 restored token,
re-derived at the primary source), every `K_{i+1}`-residue at height `k` is realized by
some `C` with `deg C < D_{i+1}` (inverse-twisted digits, C.84's lift).

**SIGNATURE** [signed: A-C.1 — elaborated in `leanspec/Leanspec/ChapC.lean`; split → 2, in
NORM FORM over the interface (C.27's carrier iterated — the ξ-free consumer discipline);
`boundRec` the recursion companion (the PE5-F-3 restored token)]:
```lean
def boundRec (W : DeepTower F H₀ hpin r) : ℕ → ℕ
  | 0 => 0
  | 1 => (F.e₁ * F.f₁ - 1) * F.h
  | (i + 2) => (W.e (i + 2) * W.f (i + 2) - 1) * W.u (i + 2) + W.e (i + 2) * boundRec W (i + 1)

theorem tower_slot_exact … [I : FGMNCalculus W e' f' u'] …
    {β : ℕ} {C : Polynomial O} (hg : I.ExactGrade β C)
    (hdeg : C.natDegree < e' * f' * W.Dcum r)
    {g : Polynomial O} (hgm : g.Monic) (hKP : I.KP g)
    (hgdeg : g.natDegree = e' * f' * W.Dcum r) :
    (W.ehat r * e') * (addVal O (Algebra.norm O (AdjoinRoot.mk g C))).toNat
      = g.natDegree * β

theorem tower_lift … (k : ℕ) (hk : boundRec W r < k) (s : W.fld r) (hs : s ≠ 0) :
    ∃ C : Polynomial O, C.natDegree < W.Dcum r ∧ I.ExactGrade k C ∧ I.Rgr k C = s
```

**DEPENDS.** C.23 · C.24 · C.27 · C.83 · C.84 · C.87 · H.51–H.53 (iterated) · **GC-13
placeholder `EFF.HE7.<nn> — ANNEX-THEOREM R1-b/R1-c [supplied-by: chapter E]`** (the
`i ≥ 3` proof pattern's corpus anchor; the four-clause instantiation table — (a) induction
hypothesis, (b) `u_{i+1}` exact, (c) coprimality, (d) the `K_i`-basis — is this chapter's
own and is the Lean proof's skeleton, so the placeholder is provenance, not a proof
dependency; if E's transcription lands first the SOURCE gains its node ID).

**PROOF (route).** `EFF.GENTOW5.22`'s four steps: (1) values exact one level down + the
defining `u_{i+1}`; (2) cross-class ties impossible (coprimality bijection, H.51's
pattern); (3) within-class: the telescoped `τ_i`-cocycle residues are fixed letter units
(C.85(A1)'s mechanism per rung — per-grade fixedness ONLY, never the single-`w` form:
S11.2's fence transcribed in the docstring); (4) the `K_i`-basis kills cancellation
(H.53); `(LIFT_i)` = prescribe inverse-twisted digits, bound arithmetic never sees
residues.

**SIZE.** 2 × ~45 lines. The chapter's third schedule-risk node (with C.27 and C.33).

**SOURCE.** `EFF.GENTOW5.22` (verbatim, incl. the acceptance-grade fold on the ANNEX R
pin and the bound-token restoration); `.23` (the base-vs-tower remark: J-D0 transport for
count/degree/vanishing ONLY — "no invariance under CHANGING systems mid-argument is
consumed (that stronger claim is false — HE7-T-BADTWIST)", carried as the docstring
fence).

**TEETH.** the corpus's own coverage box: NO dedicated machine row at `i ≥ 3` — the §13
gate ADDS one (GC-11's extra-force clause for thin verification): a depth-3 `(SLOT₃)`
spot value at `q = 2` and `q = 3` on the S4 witness chain's data (`n̂₃(85) = 2⁸Φ₂`
family); A-rows cover `i ≤ 2`.

**ENVIRONMENT.** ENV-C3.

---

### NODE C.89 [def+lemma] [fresh] — **TERMINAL SUPPLY: THE `𝒲` HYPOTHESIS FAMILY**

**STATEMENT.** *`[GENTOW5-W(i)]` — the OPEN transported lemma, as a named hypothesis
carrier (Display A's `𝒲_{≤i}` conjunct; supplied to chapters E and I).*
`GENTOW5W F … (i) : Prop` := the single-`w` geometric form of the cross-frame unit at
level `i`: there exists `w_i ∈ K_i^×` (the corpus's `R_{i+1,k̄_i}(n̂_i(u_{i+1}))`) with
`u_i(β_t) = θ_i(t)·w_i^{f_{i+1}−t}` for every slot `t` — stated at C's carriers via the
normalizer-ratio reads, with `θ_i(t)` in ratio form (GC-14 anchor cite; the reciprocity
`θ_i(t) = ϑ_{i,f_{i+1}−t}^{-1}` is the D-table's business). And
`Wle F … (n) : Prop := ∀ q, 3 ≤ q → q ≤ n → GENTOW5W … q`. Lemma clauses:
(i) **`i = 2` DISCHARGE, unconditional**: `GENTOW5W … 2` holds — the landed GENTOW2 r3
B-law (§10's C.99/C.100 supply it; DAG: those before this clause);
(ii) **`i = 1`**: the SHAPE holds with a fixed letter-power unit `u1`; **the tie
`u1 = w_1` is OPEN** (S11.3's re-scope — the clause is stated as the shape + a separate
named open tie, never as the tied form);
(iii) **`i ≥ 3`: OPEN** — "per-grade fixedness underdetermines (fixed families exist that
fit no single `w`)"; a fleet agent needing it returns `BLOCKED: [GENTOW5-W(i)] (HYP-class
open lemma; the honest-sorry analogue)` — it is a HYPOTHESIS on C.90/C.91's `n ≥ 3` legs
and on E's deep rungs, and chapter I carries it in the capstone block.

**SIGNATURE** [signed: A-C.1 — elaborated in `leanspec/Leanspec/ChapC.lean`; the single-`w`
form in the RATIO carrier (GC-14 honored: no orientation committed); (i)'s `i = 2`
discharge as `gentow5w_two`; (ii)'s `i = 1` SHAPE with the letter power — **the tie
`u1 = w₁` stays OPEN, no statement asserts it**; (iii) `i ≥ 3` OPEN — **the definition IS
the carrier; no axiom asserts it** (a fleet agent needing it returns
`BLOCKED: [GENTOW5-W(i)]`)]:
```lean
def GENTOW5W {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀} {r : ℕ}
    (W : DeepTower F H₀ hpin r) (e' f' u' : ℕ) (I : FGMNCalculus W e' f' u') : Prop :=
  ∃ w : W.fld r, w ≠ 0 ∧ ∀ t, t < f' →
    I.Rgr ((f' - t) * u') (I.chainNorm r ((f' - t) * u')) * I.thetaRatio (f' - t)
      = w ^ (f' - t)

def Wle {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀} {r : ℕ}
    (W : DeepTower F H₀ hpin r) (e' f' u' : ℕ)
    (I : ∀ i, (hi : i ≤ r) → FGMNCalculus (W.trunc i hi) e' f' u') (n : ℕ) : Prop :=
  ∀ i, 3 ≤ i → i ≤ n → ∀ hi : i ≤ r, GENTOW5W (W.trunc i hi) e' f' u' (I i hi)

theorem gentow5w_two (W : DeepTower F H₀ hpin 2) (e' f' u' : ℕ)
    (I : FGMNCalculus W e' f' u') … : GENTOW5W W e' f' u' I

theorem gentow5w_one_shape (W : DeepTower F H₀ hpin 1) … :
    ∃ k : ℕ, ∀ t, t < f' →
      I.Rgr ((f' - t) * u') (I.chainNorm 1 ((f' - t) * u')) * I.thetaRatio (f' - t)
        = (I.letterZ 1 ^ k) ^ (f' - t)
```

**DEPENDS.** C.83 · C.85(A1) · C.99/C.100 (§10 — the `i = 2` discharge's suppliers; DAG
order §10's B″/B′ before clause (i)).

**PROOF.** (i) from C.99/C.100 (the landed law at the depth-2 tower); (ii) the letter
formula's species (§10's dictionary layer); (iii) none — the definition IS the carrier.

**SIZE.** 30 lines.

**SOURCE.** `EFF.GENTOW5.27`'s S11.2 fence (verbatim: the `[GENTOW5-W(i)]` display and
"hereby an OPEN transported lemma, the honest-sorry analogue") and S11.3 (the `i = 1`
re-scope + the three-regime net position: "pinned-`w_i` unconditionally realized at
`i = 2` exactly; at `i = 1` the shape with the tie open; at `i ≥ 3` open behind
`[GENTOW5-W(i)]`"); BRIEF E product (4) (the `(H-VARTHETA-RES)_i ∧ 𝒲_{≤i}` conjunct this
supplies).

**TEETH.** GENTOW2 PE6's w-measurement (w-avatar ≠ 1 at 6 primes / 4 frames,
`u₃`-DEPENDENT within each tower — so `w = 1` is NOT generic and the ψ^{(w)} form is
operative) → **executable regression** retained + §16 disposition row; no Lean theorem
can discharge (iii) — signed as the chapter's second named open hypothesis (with
C-BOX-1).

**ENVIRONMENT.** ENV-C3.

---

### NODE C.90 [theorem] [fresh] (cite-conditional through C.92; `𝒲`-conditional at `n ≥ 3`)

**STATEMENT.** *THEOREM GENTOW5-B (a)+(b): the key certificate and one-sidedness, at the
three-regime TERMINAL scope.* For a depth-`r` tower datum with gauge-corrected recipe keys
(C.83/C.84; the gauge-naive form refuted at letter-live frames):
(a) **[key certificate]** `Φ_{i+1}` is a key/prime polynomial for the level-`i` MacLane
valuation with residual `R_{ν_i}(Φ_{i+1}) = ψ_{i+1}^{(w_i)} := w_i^{f_{i+1}}·
ψ_{i+1}(y/w_i)` — the **w-TWISTED** form (the on-the-nose `ψ_{i+1}` is NOT claimed; the
`w_i = 1` case is OPEN; σ, values, degrees, irreducibility and repo-side residue classes
are w-blind) — at `i = 2` unconditional; at `i = 1` the S11.3 shape; at `i ≥ 3` under
`Wle … n` (C.89);
(b) **[one-sidedness at every level]** for `1 ≤ j ≤ i+1` the level-`(j−1)` polygon of
`Φ_{i+1}` is one-sided of slope `λ_j` with residual
**`(ψ_j^{(ω_{j−1})})^{l_{j+1}⋯l_{i+1}}`** (the POST-D3i TERMINAL display — S11.5's
re-index fixing the degree count, S12.1's per-level twist, the corrigendum's `ω_{j−1}`
index with `ω_1` = the S11.3 unit; three DEAD prior displays), and exact intermediate
values `v(Φ_{j−1}(ξ))`-cleared — recipe roots are depth-`(i+1)` node points (repo-class
membership, w-blind AFTER the single-`w` form is supplied — S12.1's withdrawal of the
contrary transcribed).

**SIGNATURE** [signed: A-C.1 AT CLAUSE (a) — `gentow5_key_certificate` (KP-hood + the
w-TWISTED residual `wconj w ψ'` under `Wle`, the three-regime scope through C.89's
carriers); **clause (b) — the level-general one-sidedness — is the BOOKED C.92 residual
field (published Cor 6.3)**, recorded there and in the A-§ block; the MacLane side enters
ONLY through C.92's interface, as planned]:
```lean
theorem gentow5_key_certificate {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀} {r : ℕ}
    (W : DeepTower F H₀ hpin r) (e' f' u' : ℕ)
    (I : ∀ i, (hi : i ≤ r) → FGMNCalculus (W.trunc i hi) e' f' u')
    … (hW : Wle W e' f' u' I r) …
    (Φnext : Polynomial O) (hmon : Φnext.Monic)
    (hdeg : Φnext.natDegree = e' * f' * W.Dcum r)
    (ψ' : Polynomial ((W.trunc r le_rfl).fld r)) (hψm : ψ'.Monic) (hψd : ψ'.natDegree = f')
    (hadm : Irreducible ((I r le_rfl).Rres Φnext) ∧
      ((I r le_rfl).Rres Φnext).natDegree = f') :
    (I r le_rfl).KP Φnext ∧
    ∃ w : (W.trunc r le_rfl).fld r, w ≠ 0 ∧ (I r le_rfl).Rres Φnext = wconj w ψ'
```

**DEPENDS.** C.83 · C.84 · C.85 · C.88 · C.89 (the `n ≥ 3` hypothesis + the `i = 2`
discharge) · C.92 ([cite:FGMN-chain]) · C.99/C.100 (§10).

**PROOF (route).** `EFF.GENTOW5.27`'s (B-1)/(B-2) legs: (B-1) = C.88's `(SLOT_i)` value
clause; (B-2) = the landed B-law with the audited cancellation ("the ϑ-twist cancels the
θ leg ONLY; the w-leg SURVIVES" — the two-line residue computation transcribed exactly);
then the certificate run through C.92's cited clauses (Cor 4.7(1), eq (14)/Prop 5.7,
Lemma 5.3(2), Lemma 1.11, Cor 1.13, Thm 6.3, Cor 6.4 — each consumed by exact cited
name).

**SIZE.** 2 × ~45 lines.

**SOURCE.** `EFF.GENTOW5.26`–`.28` (statements at TERMINAL scope, incl. the index-0
scope fold — (a)/(b) claimed at `i ≥ 1` only — and every supersession chain named);
DECISION C-D1 (this is the tower-side FGMN interface, kept strictly behind gate (b)).

**TEETH.** P-B3 (10 polygons one-sided, on-chord support exactly the char-2 binomial
spots; the refuting/verifying witness pairs `f32@Φ4`/`Φ4@Φ3` vs `f32@Φ3`/`Φ4@Φ2`) →
**executable regressions** retained; FR-A's repo-side `ψ₃` class row → retained; §13
fires the `q = 2` witness chain and a `q = 3` frame.

**ENVIRONMENT.** ENV-C3.

---

### NODE C.91 [theorem] [fresh] (`𝒲`-conditional at `n ≥ 3`)

**STATEMENT.** *THEOREM GENTOW5-B (c)+(d)+(e): budgets, refine transfer, and the
self-feeding floor — the third stage assembled.* At induction indices `i ≥ 1` (index 0
NOT claimed for (c)/(e); (d) holds at `i ≥ 0` via C.86's rider):
(c) the level-`(i+1)` tower-entry locus `T_{i+1}` is weight-characterized with per-slot
digit floors, fibration, node pins `p_j ≥ (μ−j)E_{i+1} + 1`, and field floor — LEMMA
GENTOW-1(a)–(d) under the substitution table `(D′, e₂, u₂, E₂) ↦ (D_{i+1}, e_{i+2},
u_{i+2}, E_{i+2})`, with Step 2's aboveness on the S11.1.1–.3 one-directional route (the
"both grids agree" parenthetical is DEAD) and the deeper reads by the bottom-up entry
ladder (each rung one `(SLOT_j)` read — C.88);
(d) refine transfer at level `i+1`, general `μ` — C.85's statement with `2 ↦ i+1` (its
lift in range: `λ > E_{i+1} > bound_{i+1}`, S12.2);
(e) the NODE-FLOOR COROLLARY: every side of the level-`(i+1)` composed polygon of an
`f ∈ T_{i+1}` has slope `> E_{i+1} > dv_{i+1}(x^{D_{i+1}})`, hence `u_{i+2} > e_{i+2}E_{i+1}`
automatically at tower leaves — **the induction feeds itself** (C.55 at every level).
At `n ≥ 3`, (c) and (e) are conditional on `Wle … n` (S12.1 items 3–4, with the
datum-field carve-out C.83 implements).

**SIGNATURE** [signed: A-C.1 AT (d)+(e): (d) is C.85's `substitution_kills` (level-blind
ring identity) + C.56's transport (both signed); (e) as `gentow5_selffeed`, reusing C.98's
abstract `hSupp`/`hOnSide` carriers — the self-feeding floor at EVERY level in one
statement. **(c) — the level-(i+1) entry characterization — BOOKED** (it needs the
level-(i+1) `dv`-carrier, the same §9-scope residual as C.90(b)/C.102's; recorded in the
A-§ block; its level-2 instance is C.52, signed)]:
```lean
theorem gentow5_selffeed (P : ℕ → ℕ∞) (μ E : ℕ) (hμ : 0 < μ)
    (hpins : ∀ j < μ, (((μ - j) * E + 1 : ℕ) : ℕ∞) ≤ P j) (htop : P μ = (0 : ℕ∞))
    {u ℓ j : ℕ} (hℓ : 0 < ℓ) (hside : hOnSide P μ u ℓ j) :
    ℓ * E < u
```

**DEPENDS.** C.52–C.55 (the index-1 instances) · C.83 · C.84 · C.85 · C.87 · C.88 ·
C.89 · C.90 · C.92.

**PROOF (route).** `EFF.GENTOW5.29`–`.31`'s displays: Steps 0–5 with the substitution
table ((c)); the level-blind S1 proof ((d)); the two-line convexity + floor-chain
telescoping ((e)).

**SIZE.** 3 × ~40 lines.

**SOURCE.** `EFF.GENTOW5.29` (TERMINAL: the `[GT5-r3]` re-indexed read clause — the
(i+2)-anchored pairing REFUTED at the committed witness rows — and S11.1's Step-2
supersession); `.30` ((d), with its S12.1 unaffected-scope certificate); `.31` ((e), with
the S12.1 item-4 conditionality and carve-out).

**TEETH.** P-B1/B2 (floor chain tight) + the `gentow5_rider_f32dev.py` 7/0 rows +
P-A1/A2/A3 ((d)'s instances) → retained; §13 re-fires the depth-3 witness values at both
primes.

**ENVIRONMENT.** ENV-C3.

---

### NODE C.92 [cite] [cite:FGMN-chain]

**STATEMENT.** *The MacLane-chain certificate battery ([cite:FGMN], gate (b) — SECOND
import, wider than C.66).* The cited clauses, each an exact Lean statement drafted at stub
stage against C.25/C.83's carriers, signed per Part V gate (b) as ONE import with an
itemized faithfulness entry: FGMN **Lemma 1.11 + Cor 1.13** (prime polynomials),
**Lemma 5.3(2)** (admissibility/degree forcing), **Prop 5.7 + eq (14)** (residual of a
key), **Cor 4.7(1)/(3)** (R-operator additivity/multiplicativity — the (3) clause is
C.66's; this import subsumes it if the orchestrator prefers ONE FGMN axiom group),
**Thm 6.3 + Cor 6.4** (the key-certificate and length-`r` one-sidedness, "for any
`1 ≤ j ≤ r`" — level-general IN THE SOURCE). Transport through GENTOW2's dictionary/shear
rows (§10) with the `ψ₂^{FGMN}`/`ψ₂^{repo}` discipline (C-H10).

**⚠ SCOPE FENCE.** Exactly these clauses at exactly the consumed generality; the
`w`-closed-form and anything about `nu`-optimality beyond the struck (H-b) chain clause
(`EFF.GENTOW2`'s TOWERRAT-R3-1 STRUCK row) are NOT imported.

**⚠ A-3 NUMBERING CORRECTION (2026-08-16, `docs/CITE_NUMBERING_AUDIT_2026-08-16.md`).** Every cited
statement is right; **all but one of the numbers are arXiv-v3 numbers the published paper does not
use.** For **J. Algebra 427 (2015) 30–75** (DOI 10.1016/j.jalgebra.2014.12.022) the loci are:
Lemma 1.11 → **Lemma 1.8** · Cor 1.13 → **Cor 1.10** · Lemma 5.3(2) → **Lemma 5.2(2)** ·
Prop 5.7 + eq (14) → **Prop 5.6 + eq (11)** · Cor 4.7(1)/(3) → **Cor 4.12(1)/(3)** ·
Thm 6.3 → **Thm 6.2** (v3's items (1)(2)(3) become (1)(2): v3's (3) is absorbed into published (2)) ·
Cor 6.4 → **Cor 6.3** (its eq (23) keeps its number). Two further fixes inside this node: the quoted
phrase *"for any `1 ≤ j ≤ r`"* reads **`1 ≤ i ≤ r`** in both versions (the `j` is the repo's slip, and
`j` is a different index in the surrounding blueprint text); and the NS-12 scope pins move off numbered
items entirely — v3's **Def 6.1** (the set `P`, no separability restriction) is **unnumbered running
prose at the head of published §6**, and v3's **Lemma 6.2**, whose proof carries the load-bearing
*"with due count of multiplicities if `F` is inseparable"* clause, is published **Lemma 6.1** (clause
verbatim intact, so the COVERS-ALL-O verdict stands on a re-pinned citation). Evidence: arXiv:1305.0775
stops at v3 (2013-07-26); a later author version (2013-12-04, UPCommons handle 2117/28203) renumbers
§§1, 3, 4, 5, 6; three author-side citation echoes, one post-publication (2019), match that numbering
and none match v3. Not print-read: risk LOW-MEDIUM, closing check in audit §7.2.

**SIGNATURE** [signed: A-C.1 — elaborated in `leanspec/Leanspec/ChapC.lean`, fragile no. 2].
The §10 design note's packaging, DRAFTED: one field per consumed cited clause, typed against
C.83's carrier; every field docstring carries the PUBLISHED number (A-3 audit §4). Parameters:
the chain `W : DeepTower F H₀ hpin r` (keys `keyAt 1 … r`, `keyAt 1 = F.key`) plus the
NEXT-stage numerals `(e', f', u')` — the recipe stage the §10 lemmas read (S2 witness: `r = 2`,
`(e₃, f₃, u₃)`).

```lean
namespace Uniformity.Density.Tower

class FGMNCalculus {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀} {r : ℕ}
    (W : DeepTower F H₀ hpin r) (e' f' u' : ℕ) where
  keyAt : ℕ → Polynomial O
  keyAt_one : keyAt 1 = F.key
  keyAt_deg : ∀ i, 1 ≤ i → i ≤ r → (keyAt i).natDegree = W.Dcum i
  ExactGrade : ℕ → Polynomial O → Prop          -- the ν-grade pin (R3-2's scope fence)
  Rgr : ℕ → Polynomial O → W.fld r              -- the graded read (C.104's (R-FGMN))
  Rres : Polynomial O → Polynomial (W.fld r)    -- the residual operator R_ν
  KP : Polynomial O → Prop
  nuEquiv : Polynomial O → Polynomial O → Prop
  letterZ : ℕ → W.fld r                         -- the z_i letters (Def 3.12-family)
  Rgr_mul : ∀ β β' (g g' : Polynomial O), ExactGrade β g → ExactGrade β' g' →
    ExactGrade (β + β') (g * g') ∧ Rgr (β + β') (g * g') = Rgr β g * Rgr β' g'
      -- [published Cor 4.12(3); was Cor 4.7(3)]
  Rgr_ne_zero : ∀ β (g : Polynomial O), ExactGrade β g → g ≠ 0 → Rgr β g ≠ 0
      -- [published Cor 4.9(3); was Cor 4.4(4)]
  Rres_recipe : ∀ (khat : ℕ → Polynomial O),
    (∀ t, t < f' → ExactGrade ((f' - t) * u') (khat t)) →
    (∀ t, t < f' → (khat t).natDegree < (keyAt r).natDegree) →
    Rres ((keyAt r) ^ (e' * f') - ∑ t ∈ Finset.range f', khat t * (keyAt r) ^ (e' * t))
      = Polynomial.X ^ f'
        - ∑ t ∈ Finset.range f',
            Polynomial.C (Rgr ((f' - t) * u') (khat t)) * Polynomial.X ^ t
      -- [published Prop 5.6 + eq (11) + Cor 4.12(1) + Def 1.8's expansion-minimum]
  KP_criterion : ∀ (g : Polynomial O), g.Monic →
    g.natDegree = e' * f' * (keyAt r).natDegree →
    Irreducible (Rres g) → (Rres g).natDegree = f' → KP g
      -- [published Lemma 5.2(2); was Lemma 5.3(2)]
  KP_irred : ∀ (g : Polynomial O), KP g → g.Monic → Irreducible g
      -- [published Lemma 1.8 + Cor 1.10; Gauss transport to O[x] in the faithfulness entry]
  Rres_keyAt : Rres (keyAt r) = 1
      -- [published Thm 6.2; was Thm 6.3 — the non-equivalence pivot C.103 reads]
  nuEquiv_ne_of_Rres : ∀ (g g' : Polynomial O), KP g → KP g' →
    Rres g ≠ Rres g' → ¬ nuEquiv g g'
      -- [published Prop 5.6, the consumed equivalence]

axiom fgmn_calculus_exists {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀} {r : ℕ}
    (W : DeepTower F H₀ hpin r) (e' f' u' : ℕ) (he' : 0 < e') (hf' : 0 < f')
    (hcop : Nat.Coprime u' e') (hfloor : e' * W.Econst r < u') :
    Nonempty (FGMNCalculus W e' f' u')
```

**⚠ THE A-C.1 DRAFTING FLAGS (owner must inspect — like C.66's, this statement is the unit's
own drafting under append #66's category-level signature: gate-(b)-SIGNED-AT-CATEGORY,
statement-UNINSPECTED):** (1) the interface carries its OWN operator carriers (`Rgr`/`Rres`
valued in `W.fld r`) with `ExactGrade` as the R3-2 scope fence conditioning every graded
clause; (2) **two BOOKED RESIDUAL FIELDS**, to be added when their consumers fire: the
level-general one-sidedness clause (published **Cor 6.3**, was Cor 6.4 — C.90(b)'s leg; it
needs the level-`i` `dv`-carriers, which are §9-scope) and the γ-letter defining reads
(published Def 3.12-family — C.102's leg); until then C.90(b)/C.102 are typed against
`letterZ` + their own repo-side carriers and the residual clauses enter as per-node
hypotheses; (3) `KP_irred` is stated over `O[x]` (source: over `K_v[x]`; monic + `KP ⊂ O[x]`
+ Gauss — the transport recorded here so the faithfulness entry carries it); (4)
`fgmn_calculus_exists` is DECLARED (not variable-form) under append #66's category signature,
matching the C.66 precedent; C.126's census expects exactly this name.

**DEPENDS.** C.25 · C.83 · §10's dictionary nodes (C.97/C.98) · the layout print
(`docs/references/fgmn_residual_ideals_1305.0775v3_layout.txt`, numbering verified at
GENTOW2's ledger).

**PROOF.** none — gate-(b) import; Asvin signs.

**SIZE.** statement block (≤ 40 lines) + the faithfulness entry.

**SOURCE.** `EFF.GENTOW5.27`/.28's `[Q1][Q2][Q4][Q6][Q7][Q8][Q9][Q10]` consumption
(each grep-verified at GENTOW2); `EFF.GENTOW2`'s pinned quote blocks (the citable
surface).

**TEETH.** the corpus's decode/measurement legs (PE4 decode 14/0; PE6 w-measurement) →
retained as regressions; §16's table carries the stacked conditionality verbatim.

**ENVIRONMENT.** ENV-C1 (statement-level).

---

### NODE C.93 [lemma] [fresh]

**STATEMENT.** *Threshold arithmetic and the `HYP.82` census made formal.* (i) First-live:
a depth-`r` tower with a live top problem `μ_r ≥ 2` needs `n = D_r·μ_r ≥ 2^{r+1}`
(properness `l_i ≥ 2` telescoped); depth 2 first lives at `n ≥ 8` (C.31's bound), depth 3
at `n ≥ 16`, depth 4 at `n = 32` (the S4 witness is exactly minimal). (ii) The
`[GENHN-TOW-1]` census as a Lean-facing record: items (1)–(5) + (6)(β) are THEOREMS of
this chapter (C.52–C.58, C.72–C.81, C.55); item (6)(α) at depth 3 is C.90/C.91's scope;
depth ≥ 4 is NOT claimed by any node (the boxes stay at exact scope `n ≥ 32`-first-live) —
the census is a documentation node (a `#check`-suite over the named theorems, the
CHAP-G G.30 pattern) so chapter I's `HYP.82` row can cite ONE name.

**SIGNATURE** [signed: A-C.1 — elaborated in `leanspec/Leanspec/ChapC.lean`; the census as
the `C93Census` `#check` block over the signed item names]:
```lean
theorem tower_first_live (r μr : ℕ) (hr : 1 ≤ r) (hμ : 2 ≤ μr) (l : ℕ → ℕ)
    (hl : ∀ i, 1 ≤ i → i ≤ r → 2 ≤ l i) (D : ℕ) (hD : D = ∏ i ∈ Finset.Icc 1 r, l i) :
    2 ^ (r + 1) ≤ D * μr
```

**DEPENDS.** C.31 · C.32 · C.55 · the §6/§8/§9 theorem names.

**PROOF.** (i) `Nat.pow` telescoping, `omega`. (ii) mechanical.

**SIZE.** 22 lines.

**SOURCE.** `EFF.GENTOW5.20` (verbatim); C-H4's disposition table (this node is its
executable form); `EFF.GENIND.176`-family via CHAP-H H-7 (the `n ≥ 8` handoff this
chapter received).

**TEETH.** the S4 witness chain (`u = 5, 21, 85, 341`; `n = 32`) → §13 regression.

**ENVIRONMENT.** ENV-C5.

---

### NODE C.94 [cite] [cite:AGNPRW]

**STATEMENT.** *NS-7 — descent termination as a literature cite (gate (b); `HYP.15`'s
answered branch).* The cited theorem: **[AGNPRW] Thm 5.2** (the Ore–Mac Lane–Montes
termination: the key-polynomial descent on a fixed monic squarefree `f` over a complete
DVR terminates), imported at the scope the tower consumes: every descent history of §5's
grammar on a fixed `f` reaches multiplicity 1 (or an α-refine chain that terminates) in
finitely many steps. What is PROVED here and NOT cited: the jump-count bound (C.32 — the
level depth is `≤ log₂`-bounded unconditionally) and the α-refine finiteness interface
(via E's HE7-8 placeholder). What the cite carries: the full termination of the composite
descent including refine chains at every level — the resolution doc's "only PARTIAL" row,
imported rather than re-proved (C-H9). Exact Lean statement drafted at stub stage;
Asvin signs.

**⚠ A-3 NUMBERING CORRECTION (2026-08-16, `docs/CITE_NUMBERING_AUDIT_2026-08-16.md`).** The
statement above is right; **the number is wrong for the version of record, and it collides.**
Cite **[AGNPRW] Thm 5.6**, not Thm 5.2: *"If `v` is discrete of rank-one, then the OM-algorithm
terminates"* is **Theorem 5.6** of the published paper — **Found. Comput. Math. 25 (2025), no. 2,
631–681**, DOI 10.1007/s10208-024-09646-x — whose **Theorem 5.2 is a different theorem** (the
`e`/`f` formula for the factor singled out by `(µ, φ)`). "Thm 5.2" is the arXiv:2207.02139**v1**
number; arXiv has only v1 and was never updated, while the accepted version renumbers §4 by +6 and
§5 by +4 (the publisher's own abstract advertises *"a key new result (Theorem 4.10)"*, which is v1's
Thm 4.4). Statement text unchanged — the termination sentence and its index-finiteness proof sketch
are verbatim identical in both versions; only the label and the internal reference move
(`[10, Thm. 4.8]` → `[14, Thm. 4.8]`, both = GMN12). Disclosed inheritance: GMN12 has no *Theorem*
4.8 (4.8 is a Lemma there; the theorem of the index is **GMN Thm 4.18** + Cor 4.19), so AGNPRW's own
last link for the index step is imprecise — record it in the faithfulness entry rather than
repeating it silently. Not print-read (Springer paywalled): risk LOW, closing check in audit §7.1.

**SIGNATURE** [signed: A-C.1 — elaborated in `leanspec/Leanspec/ChapC.lean`; THE EXACT LEAN
STATEMENT, breaking the D24 `C.94 ⇄ I.01` deadlock on the C side].

```lean
namespace Uniformity.Density.Tower

structure DescentState (O : Type*) [CommRing O] where
  key : Polynomial O
  block : Polynomial O

inductive DescentStep (π : O) : DescentState O → DescentState O → Prop
  | jump : ∀ {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀} (L : LevelDatum F H₀ hpin)
      (s s' : DescentState O),
      s.key = F.key → 2 ≤ L.ℓ * L.r.natDegree →
      HasLabel L s'.block → s'.block ∣ s.block →
      IsTestKey L s'.key → L.keyDeg₂ * 2 ≤ s'.block.natDegree →
      DescentStep π s s'
  | refine : ∀ (s s' : DescentState O) (u ℓ u' ℓ' : ℕ),
      0 < ℓ → 0 < ℓ' → s'.block = s.block →
      s'.key.natDegree = s.key.natDegree →
      (s.key - s'.key).natDegree < s.key.natDegree →
      (sideSet s.key s.block u ℓ).Nonempty →
      (sideSet s'.key s.block u' ℓ').Nonempty →
      u * ℓ' < u' * ℓ →
      DescentStep π s s'

def NS7TerminationStatement : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    [Finite (IsLocalRing.ResidueField O)] (π : O), Irreducible π →
    ∀ f : Polynomial O, f.Monic → Squarefree f →
    ∀ hist : ℕ → DescentState O,
      (∀ n, (hist n).block ∣ f) →
      (∀ n, DescentStep π (hist n) (hist (n + 1))) → False

axiom agnprw_termination : NS7TerminationStatement
```

**⚠ THE A-C.1 DRAFTING DECISIONS (owner must inspect; statement drafted at stub stage per
the node's own delegation, category-signed by append #66):** (1) the descent STATE is
`(key, block)` and a JUMP step consumes §5's carriers verbatim (a labelled divisor at
multiplicity ≥ 2 — `deg ≥ 2·D″` — over a jump datum `ℓd_r ≥ 2`, the new key a test key);
(2) an α-REFINE step is a same-degree recentering with STRICTLY increasing attained side
slope (the C.113(i)/C.56 shape) — the strictness clause is what makes vacuous refine loops
non-steps, so "no infinite history" IS termination; (3) "reaches multiplicity 1 (or a
terminating α-refine chain) in finitely many steps" is signed in no-infinite-chain form
(the two are classically equivalent for a step relation whose terminal states admit no
step); (4) histories are pinned to `f` by `block ∣ f` at every stage. `I.01`'s
`NS7Termination` body can now be typed against `NS7TerminationStatement` (its `∀ O` bundle
quantifier is the statement's own) — recorded in CHAP-I's addendum.

**DEPENDS.** C.30 · C.32 · C.83 · **A-C.1: C.13 (`IsTestKey`) · C.29 (`HasLabel`) · C.09**.

**PROOF.** none — gate-(b) import.

**SIZE.** statement block (≤ 20 lines) + faithfulness entry.

**SOURCE.** `HYP.15` (the ledger row); CHAP-B H-8 (NS-7 "belongs with the tower's descent
bookkeeping" — this is that node); BRIEF C product (5) (verbatim: "carried as the [AGNPRW]
Thm 5.2 cite-hypothesis, NOT re-proved").

**TEETH.** C.32's arithmetic instances guard the jump half; the cite's faithfulness entry
carries the scope audit.

**ENVIRONMENT.** ENV-C2 (statement-level).

---

### NODE C.95 [theorem] [fresh]

**STATEMENT.** *The 𝒯-free cap lemma and the attainment certificate at its pinned scope
(GENTOW-6.4 + GENTOW-6.3/6.3′).* (i) **the cap (LEMMA GENTOW-6.4, CHAIN-CAP TERMINAL):**
the C.58-band cap behaviour WITHOUT the `𝒯` hypothesis — the per-window read at partial-
side `f` obeys the same three-band law, with the per-window bijection codomain CORRECTED
per PE2-F-2: above-top slots are FORCED to 0, exact condition **`n % D₂ ≠ D₂ − 1`**
(sharper than the report's `D₂ ∤ n`; the FRAME-F witness carries 3 such slots) — this is
the supplier C.82's 6.2C(d) leg consumes (prove-first, the corpus's own repair shape);
(ii) **the attainment certificate (THEOREM GENTOW-6.3), SCOPE-PINNED to `f₁ = 1`,
`μ₂ = 2`** (the `[GT6-r1]` CRITICAL: at `f₁ ≥ 2` the sealed displays are NOT proved as
written): the genre-general form of §8's C.74(a) certificate — the Y-bookkeeping and the
certificate slot at the pinned scope; the `f₁`-general form (ANNEX-6.3′) enters at
exactly its earned grade: its `μ₂ = 2` fence was LIFTED by the SUB-BOX battery row
(x-ful rows, GREEN 265/0), its derivation keeps prose grade — transcribed as a SEPARATE
statement with the `f₁ ≥ 2` hypothesis explicit and the §16 table carrying the grade.

**SIGNATURE** [signed: A-C.1 — elaborated in `leanspec/Leanspec/ChapC.lean`; the cap at the
PE2-F-2 corrected-codomain core (`n % D₂ ≠ D₂ − 1`, the SHARPER condition, in-statement);
the certificate at its PINNED scope with the `f₁ ≥ 2` variant a SEPARATE statement, per the
`[GT6-r1]` fence]:
```lean
theorem cap_free … {f : Polynomial O} (hf : f.Monic)
    (hcond : f.natDegree % T.D₂ ≠ T.D₂ - 1) {j : ℕ} (hj : f.natDegree / T.D₂ < j) :
    dev (composedKey T) f j = 0 ∧ shadowDev T f j = 0

theorem attainment_certificate … (hf1 : F.f₁ = 1)
    {f : Polynomial O} (hf : f ∈ towerLocus T 2) (hnx : ¬ IsXFree T)
    {j : ℕ} (hj : j < 2) (hc : TouchCert T hπ 2 j) :
    dv2Hgt (T.levelDatum hπ) (shadowDev T f j - dev (composedKey T) f j)
      = (T.theta 2 j : ℕ∞)

theorem attainment_certificate' … (hf1 : 2 ≤ F.f₁) (same) : (same conclusion)
```

**DEPENDS.** C.50 · C.52 · C.58 · C.74 · C.77.

**PROOF (route).** (i) the corpus's fresh derivation (303/0-guarded); (ii) the S3
combinatorial prose at the pin.

**SIZE.** 2 × ~35 lines.

**SOURCE.** `EFF.GENTOW6.21` (6.4, prove-first, with the T-CAP/T-TRI teeth);
`EFF.GENTOW6.31` (PE2-F-2's codomain correction, CHAIN-CODOMAIN TERMINAL — the SHARPER
condition transcribed); `EFF.GENTOW6.12` (6.3 at the theorem-head pin, CHAIN-SCOPE
TERMINAL); `.20` (6.3′ + its licence arc).

**TEETH.** T-CAP ×3 + T-TRI ×28 (GREEN 303/0) + the seven certificate rows (Θ attained at
the predicted slot) + LEG A's two `f₁ = 2/η ≠ 1` frames → retained; §13 fires FRAME-F's
`n % D₂ = D₂ − 1`-adjacent row at both primes.

**ENVIRONMENT.** ENV-C3.

---

### NODE C.96 [theorem] [fresh]

**STATEMENT.** *GENTOW6-BOX-1's closure at `f₁ = 1` (THEOREM GENTOW-6.5, the IF direction
ONLY).* At `f₁ = 1`, `μ₂ ≥ 3`: the attainment claim at the top coordinate
`j* = (μ₂−2) + ⌊(2e₂t*+1)/(e₂f₂)⌋` — the height-`Θ_{j*}` graded digit at the certificate
slot is `binom(μ₂,2)·ĉ_{t*}²·π^{2a_{t*}}·(wrap unit)`: **attainment on the floor IF
`p ∤ binom(μ₂,2)`** — the "iff" is WITHDRAWN (the converse is FALSE, genre-dependent both
ways: the BP3 witness attains WITH `p ∣ binom(3,2)` via a different slot; FR5X at
`m = 4, p = 2` fails attainment — both witnesses transcribed as the §13/§16 negative-
control rows); the equality census at `e₂(f₂−t*) = 1` carries the corrected `k ≥ 3`
branches (the sibling-r1 bracket). NOT delivered and NOT nodes: the `j < j*`
classification at `μ₂ ≥ 3`, and the `f₁ ≥ 2 × μ₂ ≥ 3` compound (prose-only ANNEX-REMARK —
recorded in §16, no node). GENTOW6-BOX-4's DISCHARGE (the x-ful battery row) is a TEETH
row, not a node.

**SIGNATURE** [signed: A-C.1 — elaborated in `leanspec/Leanspec/ChapC.lean`; the IF
direction ONLY (the "iff" WITHDRAWN — no converse statement exists); the binomial hypothesis
as `¬ ringChar (ResidueField O) ∣ Nat.choose μ₂ 2`, entering exactly once; attainment ON
THE FLOOR at the displayed `j*`]:
```lean
theorem box1_attainment_if … (hf1 : F.f₁ = 1) {μ₂ : ℕ} (hμ₂ : 3 ≤ μ₂)
    (hbin : ¬ (ringChar (ResidueField O) ∣ Nat.choose μ₂ 2))
    {f : Polynomial O} (hf : f ∈ towerLocus T μ₂) (hnx : ¬ IsXFree T)
    (tstar : ℕ) (htstar : tstar < T.f₂ ∧ T.ψ₂.coeff tstar ≠ 0) :
    dv2Hgt (T.levelDatum hπ)
        (shadowDev T f ((μ₂ - 2) + (2 * T.e₂ * tstar + 1) / (T.e₂ * T.f₂))
          - dev (composedKey T) f ((μ₂ - 2) + (2 * T.e₂ * tstar + 1) / (T.e₂ * T.f₂)))
      = (T.theta μ₂ ((μ₂ - 2) + (2 * T.e₂ * tstar + 1) / (T.e₂ * T.f₂)) : ℕ∞)
```

**DEPENDS.** C.50 · C.74 · C.85 · C.95.

**PROOF (route).** the k-extraction ledger (clause (a)'s Y-ceiling) + the graded-digit
computation at the certificate slot; the binomial hypothesis enters exactly once.

**SIZE.** 36 lines.

**SOURCE.** `EFF.GENTOW6.34` (the amended BOX-1 state, verbatim, with both sibling-r1
brackets and the audited BP3/FR5X witnesses; conditionality stack: the closure rides the
boxes-note's 0/2 — the Lean proof discharges that grade residue for the IF direction);
`HYP.67` (the ledger row this retires at `f₁ = 1`, IF-direction).

**TEETH.** the boxes-note leg (sealed GREEN 459/0, 4 teeth at exact kill counts) +
`gentow6_boxes_pe1_fresh.py` → retained; BP3/FR5X as negative controls at BOTH primes
(BP3 is `q = 3`, FR5X is `q = 2` — GC-11's pair, exhibited by the corpus itself).

**ENVIRONMENT.** ENV-C3.

---

---

## 10. §10 — THE GENTOW2 SUPPLY LAYER

> **Design note (how the FGMN side types).** GENTOW2's lemmas B/B′/B″ are statements about
> the FGMN residual operators `R_{i,β}` applied to repo objects. Those operators exist in
> Lean ONLY through the gate-(b) import. **Packaging refinement of C.92 (recorded as
> A-§10 delta):** the import lands as a STRUCTURE `FGMNCalculus` — one field per cited
> clause (`[Q1]`…`[Q10]`, Prop 1.15, Def 1.8's expansion-minimum, Cor 4.4, Thm 4.8,
> Lemma 3.17, Prop 1.9, Def 3.12's `γ_i`-letters) at exactly the consumed generality —
> plus ONE signed axiom `fgmn_calculus_exists` (the cite; faithfulness entry itemized per
> field). B′/B″/B then become genuine LEAN THEOREMS over `[FGMNCalculus]`: their proofs
> are the corpus's own four-step derivations, consuming the fields by cited name, with the
> repo-side legs (digit reads, γ-calculus, ladder monomials) supplied by §§3–6. The
> `#print axioms` footprint of every §10 theorem shows exactly the one cite — the honest
> conditionality carrier. Terminal supply: C.99 (B″) and C.100 (B′) are what chapters D
> and F route to via GC-13; C.97 is D's T1-battery-check-10 witness; the ϑ-orientation
> stays D's (GC-14 — the full four-way table lives at `EFF.GENTOW2.25`'s orientation
> record and is D's to author; every node below states ratios, never bare ϑ).

### NODE C.97 [def+lemma] [fresh] — **TERMINAL SUPPLY: THE S2 TOWER WITNESS**

**STATEMENT.** *The concrete third-stage tower (D's T1 battery check 10 instantiates
this).* Over `O = ℤ₂`-class data (`residueCard = 2`): the genre `(2,1,4) → (2,1,2)` third
stage — `Φ′ = x² − 2` (frame `(e₁,f₁,h) = (2,1,1)`), `Φ₂ = Φ′² − 4x` (`u₂ = 5`),
`Φ₃ = Φ₂² − 16Φ′` (`u₃ = 21`), `ψ₃^{repo} = T − 1` — as a concrete `DeepTower` instance,
with the audited numeral identities as `#eval`-checkable lemmas: `u₃ = e₃·κ₃`-cleared
(`2·21/2 = 21`), `dv₂(Φ₂^{e₃})`-value `= 21 = u₃` (T1's r12 terminal-binding identity),
the ladder values `[4, 10, 21]` for `(x, Φ′, Φ₂)`, `n̂₂(21) = 16Φ′`, and the floor chain
`5 > 2·2·1`, `21 > 2·10`.

**SIGNATURE** [signed: A-C.1 — elaborated in `leanspec/Leanspec/ChapC.lean`, fragile no. 3].
A `def`-kind node whose body is a proof-carrying concrete construction (`KeyFrame`'s
`hirr`/`hpure`/`hresirr` at `Φ′ = x² − 2` are theorem-grade), so the stub layer carries it as
axiom CONSTANTS with the defining numerals as signed value clauses — the fleet lands the
construction. The recipe-key identities and the ladder `[4, 10, 21]` are machine-verified
from the polynomials up at the stub gate (finding D25/F1); `towerNorm 1 21 = (4, 0, ![1])`
IS `n̂₂(21) = 16Φ′` in exponent data (`π = 2`: `2⁴·x⁰·Φ′¹`).

```lean
namespace Uniformity.Density.Tower

axiom s2Frame [Finite (ResidueField O)] (h2 : Irreducible (2 : O))
    (hq : residueCard O = 2) : KeyFrame O (2 : O)

axiom s2Frame_data [Finite (ResidueField O)] (h2 : Irreducible (2 : O))
    (hq : residueCard O = 2) :
    (s2Frame h2 hq).e₁ = 2 ∧ (s2Frame h2 hq).f₁ = 1 ∧ (s2Frame h2 hq).h = 1 ∧
    (s2Frame h2 hq).key = Polynomial.X ^ 2 - Polynomial.C 2

axiom s2Witness [Finite (ResidueField O)] (h2 : Irreducible (2 : O))
    (hq : residueCard O = 2) (H₀ : ℕ) (hpin : (s2Frame h2 hq).Pin H₀) :
    DeepTower (s2Frame h2 hq) H₀ hpin 3

axiom s2Witness_values [Finite (ResidueField O)] (h2 : Irreducible (2 : O))
    (hq : residueCard O = 2) (H₀ : ℕ) (hpin : (s2Frame h2 hq).Pin H₀) :
    (s2Witness h2 hq H₀ hpin).e 2 = 2 ∧ (s2Witness h2 hq H₀ hpin).f 2 = 1 ∧
    (s2Witness h2 hq H₀ hpin).u 2 = 5 ∧
    (s2Witness h2 hq H₀ hpin).e 3 = 2 ∧ (s2Witness h2 hq H₀ hpin).f 3 = 1 ∧
    (s2Witness h2 hq H₀ hpin).u 3 = 21 ∧
    (s2Witness h2 hq H₀ hpin).towerNorm 1 21 = (4, 0, fun _ => 1)
```
(the `ℤ₂`-class is carried as `(h2 : Irreducible (2 : O))` + `(hq : residueCard O = 2)` —
the leancheck `ℤ_[2]`-idiom instantiates both; the floor chain `5 > 2·2·1`, `21 > 2·10` is
the structure's own `hfloor` at these numerals.)

**DEPENDS.** C.83 · C.42/C.43 (the depth-2 sub-instance).

**PROOF.** `decide`/`norm_num`-grade computation.

**SIZE.** 30 lines.

**SOURCE.** `EFF.GENTOW2.05` (the dictionary's witness column, with the compile-time audit
table — four independent occurrences of `u₃ = 21`, zero disagreements); `EFF.GENTOW5.21`
(the deeper chain `u = 5, 21, 85, 341` — extended witness for C.83).

**TEETH.** P-W1/P-N1/P-N2 + T1 battery check 10 (the consumer this supplies) →
**executable regression** + §13 rows (the witness is `q = 2`; §13 pairs it with FAM-D's
`q = 3` tower).

**ENVIRONMENT.** ENV-C3 (concrete).

---

### NODE C.98 [lemma] [fresh]

**STATEMENT.** *The normalization shear, repo side (dictionary faithfulness, cleared).*
The affine pin-cloud map `(j, y) ↦ (j, y + j·w₂·e(µ₁))`-cleared (the corpus's
`(j, y) ↦ (j, y/e(µ₁) + jw₂)` multiplied through by `e(µ₁)`) is a bijection on height
data that sends lines to lines and preserves on/above; consequently one-sidedness of the
repo `dv₁`-pin cloud at cleared slope `κ₂` is EQUIVALENT to one-sidedness of the sheared
cloud at the corresponding cleared slope — a pure statement about `ℕ`-linear argmin data
(both sides in C's own carriers; the FGMN-side gloss "the sheared cloud IS `N₂(Φ₃)`" is
C.92-interface documentation, cited not proved). Witness: `κ₂ = 5/2 ↔ λ₂ = 1/4`, pins
`(4,0),(2,7),(0,10) ↦ (4,4),(2,11/2),(0,5)`-cleared.

**SIGNATURE** [signed: A-C.1 — elaborated in `leanspec/Leanspec/ChapC.lean`, fragile no. 4].
Signed ENV-C5-abstract over height functions `ℕ → ℕ∞` (reusable for every dictionary row):
the shear `P ↦ (fun i => P i + i·c)` matches sides `(u, ℓ)` of the sheared cloud with sides
`(u + ℓc, ℓ)` of the unsheared cloud, argmin-POINTWISE (on/above preserved termwise — the
per-`j` iff is the strong reusable form; the one-sidedness equivalence is its two-endpoint
instance). The witness `κ₂ = 5/2 ↔ λ₂ = 1/4` is the instance `c := e(µ₁)·w₂`-cleared.

```lean
namespace Uniformity.Density.Tower

noncomputable def hSupp (P : ℕ → ℕ∞) (n u ℓ : ℕ) : ℕ∞ :=
  (Finset.range (n + 1)).inf fun j => ℓ • P j + (u * j : ℕ∞)

def hOnSide (P : ℕ → ℕ∞) (n u ℓ j : ℕ) : Prop :=
  hSupp P n u ℓ = ℓ • P j + (u * j : ℕ∞) ∧ P j ≠ ⊤

theorem shear_onesided_iff (P : ℕ → ℕ∞) (n c u ℓ j : ℕ) (hℓ : 0 < ℓ) (hj : j ≤ n) :
    hOnSide (fun i => P i + (i * c : ℕ∞)) n u ℓ j ↔ hOnSide P n (u + ℓ * c) ℓ j
```

**DEPENDS.** C.06/C.07 (the argmin carriers).

**PROOF.** the affine map preserves the argmin comparisons termwise; `omega` after
clearing.

**SIZE.** 24 lines.

**SOURCE.** `EFF.GENTOW2.06` (verbatim, incl. the exact witness audit and the FGMN
Lemma 2.4 gloss — the gloss stays a docstring cite).

**TEETH.** P-W1/W2/N1/N2 + TOOTH T1 (floor-breaching recipe comes back not-one-sided) →
retained.

**ENVIRONMENT.** ENV-C5.

---

### NODE C.99 [theorem] [fresh] — **TERMINAL SUPPLY: `LEMMA GENTOW2-B″`** (over `[FGMNCalculus]`)

**STATEMENT.** *The single-`w` slot law.* For each slot `t < f₃`, with
`w := u(κ̄) = R_{3,κ̄}(n̂₂(u₃))`:

```
(6)   u(β_t) = ϑ(t) · w^{f₃−t},
```

where `ϑ(t)` is the repo-derivable `n̂₂`-cocycle ratio (grade-determined, `x₀`-free, a
`z₁^j z₂^k` letter monomial — C.99's companion is the **γ-calculus**: the value-0 Laurent
monomials in `π, x, Φ′` form exactly `⟨γ₁, γ₂⟩`, so `ϑ(t) = z₁^j z₂^k` with
`ϑ(f₃−1) = 1`). Consequently the (B-law) sum reads
`R_{3,α}(Φ₃) = w^{f₃}·P(y/w)` with `P(y) := y^{f₃} − Σ ϑ(t)c_t y^t` — the realized
residual is the `w`-conjugate of the multiplicative-convention polynomial, with `P`'s
irreducible-factor pattern for EVERY value of `w`. **Dual-cite:** consumers may cite this
node or chapter D's `(ABS-G2)` (the T3 absorption — `EFF.GENTOW2.92`); the orchestrator
keeps ONE of the two as the Lean home at freeze (this chapter claims it; D's brief cites
it via GC-13, so the expected resolution is: home HERE, D cites).

**SIGNATURE** [signed: A-C.1 — elaborated in `leanspec/Leanspec/ChapC.lean`; stated in
NORMALIZER-RATIO form throughout (C-H6/GC-14: `thetaRatio t` is the ratio read
`res(n̂(u')^t / n̂(t·u'))` — no bare-ϑ orientation is committed; the D-table anchor cited);
`chainNorm` realizes `n̂_{i+1}(k)` from `towerNorm`'s exponent solve and the interface's
chain keys].
```lean
namespace Uniformity.Density.Tower

noncomputable def FGMNCalculus.chainNorm {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀}
    {r : ℕ} {W : DeepTower F H₀ hpin r} {e' f' u' : ℕ}
    (I : FGMNCalculus W e' f' u') (i k : ℕ) : Polynomial O :=
  Polynomial.C (π ^ (W.towerNorm i k).1) * Polynomial.X ^ (W.towerNorm i k).2.1
    * ∏ j : Fin i, (I.keyAt (j.1 + 1)) ^ ((W.towerNorm i k).2.2 j)

noncomputable def FGMNCalculus.thetaRatio {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀}
    {r : ℕ} {W : DeepTower F H₀ hpin r} {e' f' u' : ℕ}
    (I : FGMNCalculus W e' f' u') (t : ℕ) : W.fld r :=
  I.Rgr (t * u') ((I.chainNorm r u') ^ t) * (I.Rgr (t * u') (I.chainNorm r (t * u')))⁻¹

theorem gentow2_Bpp {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀} {r : ℕ}
    (W : DeepTower F H₀ hpin r) (e' f' u' : ℕ) [I : FGMNCalculus W e' f' u']
    (hr : r = 2)   -- ⚠ SCOPE FENCE (A-C.1 self-catch): B″ is PROVED at depth 2 ONLY;
                   -- an unfenced general-r signing would silently assert the OPEN
                   -- [GENTOW5-W(i)] (C.89) — exactly the strengthening C-H8 forbids
    (he' : 0 < e') (hf' : 0 < f') (hcop : Nat.Coprime u' e')
    (hfloor : e' * W.Econst r < u') {t : ℕ} (ht : t < f') :
    I.Rgr ((f' - t) * u') (I.chainNorm r ((f' - t) * u')) * I.thetaRatio (f' - t)
      = (I.Rgr u' (I.chainNorm r u')) ^ (f' - t)

theorem theta_letter_valued {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀} {r : ℕ}
    (W : DeepTower F H₀ hpin r) (e' f' u' : ℕ) [I : FGMNCalculus W e' f' u']
    (hr : r = 2)   -- the same depth-2 scope fence
    (he' : 0 < e') (hf' : 0 < f') (hcop : Nat.Coprime u' e')
    (hfloor : e' * W.Econst r < u') :
    I.thetaRatio 1 = 1 ∧
    ∀ t : ℕ, ∃ j k : ℕ, I.thetaRatio t = I.letterZ 1 ^ j * I.letterZ 2 ^ k
```
(the display's `u(β_t) = ϑ(t)·w^{f₃−t}` reads off the ratio form with
`w := I.Rgr u' (chainNorm r u')`; the reciprocity between the slot-indexed and ratio-indexed
ϑ is the D-table's business, deliberately NOT resolved here.)

**DEPENDS.** C.83/C.84 (ladder monomials) · C.92 (the interface: Cor 4.7(1)/(2),
Thm 4.8 + Prop 1.15, Def 1.8, Lemma 3.17, Prop 1.9, Cor 4.4, eq (14)/[Q7]) · C.21/C.28
(the repo-side reads and cocycle arithmetic) · C.100 (B′(3), consumed at step (iv)).

**PROOF (route).** the corpus's four steps, verbatim: (i) peel `G := ẑ·N^d` through
Cor 4.7(2) — `R = ϑ(t)·w^d`, a `y`-degree-0 scalar; (ii) the Φ₂-adic expansion + Def 1.8's
minimum + Cor 4.7(1); (iii) `j ≥ 1` terms die (Lemma 3.17 / the `e₃ ∤ j` grade argument /
eq (14) placing them at `y`-degree ≥ 1); (iv) the `j = 0` term:
`digit(G) = ϑ(t)·ϑ(t)^{−1} = 1`, then B′(3). The `digit(G)`-at-`deg ≥ m₃` fence (R3-2):
`digit` is applied to `Q₀` (in scope), never to `G` — the statement's reads respect
`.33`'s scope fence by construction.

**SIZE.** 44 lines. **Split candidate:** the γ-calculus companion.

**SOURCE.** `EFF.GENTOW2.43` (verbatim display + the EXACT `w^{f₃}P(y/w)` audit; the
byte-pin table — the corpus's most-pinned display); `.44` (the proof); `.41`/.42 (the
cocycle setting + γ-calculus); `.69` (C-m1); `.87` (R3-2's fence); `.92` ((ABS-G2)
dual-cite).

**TEETH.** decode MULT/COC/MP pins + PE5's γ₂-live fresh route (GREEN 91/0, first
`e₃ = 2 ×` cocycle-live frame) → **executable regressions** retained; §13 fires one
letter-live row (the corpus's letter-live frames are `q = 3`-family; the `q = 2` twin is
letter-dead — the gate documents the coincidence per C-H12 and fires the VALUES at both).

**ENVIRONMENT.** ENV-C3 + `[FGMNCalculus]`.

---

### NODE C.100 [theorem] [fresh] — **TERMINAL SUPPLY: `LEMMA GENTOW2-B′`** (over `[FGMNCalculus]`)

**STATEMENT.** *The per-grade unit law.* There is a unit `u(β) ∈ K₂^×` depending only on
the grade `β` — namely `u(β) := R_{3,β}(n̂₂(β̂))` — such that for each `Φ₂`-free `g` of
exact grade `β` (`deg g < m₃`):

```
(3)   R_{3,β}(g) = u(β) · digit(g).
```

**Direction (3) reads `FGMN = u · repo` and NOT the inverse** (the r2-F3 finding exists
because a fallback clause once wrote the inverse — GC-14's B-law-direction row; the
docstring carries the orientation record verbatim). Clause (5): with arbitrary `u`, the
B-sum gives `R_{3,α}(Φ₃) = y^{f₃} − Σ u(β_t)c_t y^t`. Clause (4) — the per-grade
equivalence `(repo read = ε₂-normalized coordinate) ⟺ u(β) = 1` — is transcribed with its
FULL honesty stack: its consumed form `u(β_t) = 1` is machine-REFUTED at letter-live
grades (PE4 LD2), and its SOLE surviving consumer is C.101's per-height-iff sentence (the
PE6 FOLD's unified consumption list: **the true consumption is B′(3) + B″**).

**SIGNATURE** [signed: A-C.1 — elaborated in `leanspec/Leanspec/ChapC.lean`; clause (3) at
the CONCRETE depth-2 chain `T.deepTower hπ` with the carrier bridge
`ρ : fld 2 ≃+* AdjoinRoot T.ψ₂` explicit and `digit = repoRead` (C.104, = the C.38a coherent
read) transported through C.45's equiv; direction `FGMN = u · repo` PRESERVED in the display
shape; clause (5) is (3) + C.92's `Rres_recipe` (a consequence, not re-signed); clause (4)
as the companion `gentow2_Bp_unit_iff` — its consumed `u(β_t) = 1` form is machine-REFUTED
(PE4 LD2) and DEAD, recorded].
```lean
namespace Uniformity.Density.Tower

theorem gentow2_Bp {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀}
    (T : TowerDatum F H₀ hpin) (hπ : Irreducible π) (hh : 1 ≤ F.h)
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [Finite (ResidueField O)]
    (e' f' u' : ℕ) [I : FGMNCalculus (T.deepTower hπ) e' f' u']
    (ρ : (T.deepTower hπ).fld 2 ≃+* AdjoinRoot T.ψ₂)
    {β : ℕ} {g : Polynomial O} (hg : I.ExactGrade β g)
    (hdeg : g.natDegree < e' * f' * T.D₂) (hfree : ¬ composedKey T ∣ g) :
    I.Rgr β g
      = I.Rgr β (I.chainNorm 2 β)
        * ρ.symm ((towerLabelEquiv T hπ) (repoRead (T.levelDatum hπ) g))

theorem gentow2_Bp_unit_iff … (same context, plus hne0 : repoRead … g ≠ 0) :
    I.Rgr β g = ρ.symm ((towerLabelEquiv T hπ) (repoRead (T.levelDatum hπ) g))
      ↔ I.Rgr β (I.chainNorm 2 β) = 1
```
(`TowerDatum.deepTower` + its data clauses are the §10 layer's carrier constants — full
text in the leanspec twin; the elided binder list of `gentow2_Bp_unit_iff` repeats
`gentow2_Bp`'s verbatim.)

**DEPENDS.** C.83/C.84 · C.92 (Cor 4.4(1), Thm 4.8 + Prop 1.15, Def 3.16, Cor 4.7) ·
C.21 (the digit read) · C.104 (the two-reads convention).

**PROOF (route).** `EFF.GENTOW2.35`: `u(β) ≠ 0` by the single-pin polygon + Cor 4.4(1);
the REPAIRED h-step (divide the lift product by `Φ₂` — the pre-repair step applied B-1
outside its `deg < D₂` scope, DEAD); the grade-0 lift via T(b)′(iii)'s repo supply
(H.54-family lifts at grade 0).

**SIZE.** 40 lines.

**SOURCE.** `EFF.GENTOW2.34` (verbatim, incl. the ORIENTATION RECORD and the [r2]/[r3]
in-place brackets); `.35` (the repaired proof); `.36` (the worked N1 trace — §13 value);
`.28` (the (B-2) REFUTATION — the honesty box: the consumed `u(β_t) = 1` form is DEAD);
`.76`/.81 (the m1-CURE/PE6-FOLD consumption unification, TERMINAL).

**TEETH.** PE4 LD2 (the refutation tooth) + the N1 worked trace + decode pins →
retained; §13 fires the N1 values.

**ENVIRONMENT.** ENV-C3 + `[FGMNCalculus]`.

---

### NODE C.101 [theorem] [fresh] (over `[FGMNCalculus]`)

**STATEMENT.** *`LEMMA GENTOW2-B` (r3 RESTATED — the B-law and the multiplicative
prescription).* With the recipe data (lifts `k̂_t` at `dv₂`-heights `u₃(f₃−t)`, digits
`c_t ∈ K₂`, `c₀ ≠ 0`, pins on the slope-`κ₃` line, **`κ₃ > e₂f₂u₂` an EXPLICIT
HYPOTHESIS** — supplied at tower leaves by C.55, cited AS a hypothesis here exactly as
the corpus routes it): `Φ₃ := Φ₂^{e₃f₃} − Σ k̂_t Φ₂^{e₃t}` satisfies

```
(B-law)   R_ν(Φ₃) = y^{f₃} − Σ_{t<f₃} u(β_t)·c_t·y^t,   u(β_t) = ϑ(t)·w^{f₃−t};
```

the multiplicative prescription `c_t := ϑ(t)^{−1}·a_t` realizes `R_ν(Φ₃) = ψ₃^{(w)}`
(admissible for every `w`); the unadjusted per-height prescription realizes `ψ₃` itself
iff `u(β_t) = 1` at each used slot — holding at letter-dead slots, failing at letter-live
LD2. The pre-r3 conclusion (`R_ν(Φ₃) = ψ₃` per-height) is DEAD.

**SIGNATURE** [signed: A-C.1 — elaborated in `leanspec/Leanspec/ChapC.lean`; the recipe
lands as the shared abbreviation `recipe3` (the R3-3-completed display) with the lifts
`k2DigitLift` (C.56a) at heights `(f'−t)·u'`; `κ₃ > e₂f₂u₂` EXPLICIT as `hκ`].
```lean
namespace Uniformity.Density.Tower

noncomputable def recipe3 {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀}
    (T : TowerDatum F H₀ hpin) (e' f' u' : ℕ)
    (c : ℕ → AdjoinRoot (towerLabel T)) : Polynomial O :=
  (composedKey T) ^ (e' * f')
    - ∑ t ∈ Finset.range f', k2DigitLift T (c t) ((f' - t) * u') * (composedKey T) ^ (e' * t)

theorem gentow2_B {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀}
    (T : TowerDatum F H₀ hpin) (hπ : Irreducible π) (hh : 1 ≤ F.h)
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [Finite (ResidueField O)]
    (e' f' u' : ℕ) [I : FGMNCalculus (T.deepTower hπ) e' f' u']
    (hkey : I.keyAt 2 = composedKey T)
    (ρ : (T.deepTower hπ).fld 2 ≃+* AdjoinRoot T.ψ₂)
    (hκ : T.e₂ * T.f₂ * T.u₂ < u') (he' : 0 < e') (hf' : 0 < f')
    (hcop : Nat.Coprime u' e')
    (c : ℕ → AdjoinRoot (towerLabel T)) (hc0 : c 0 ≠ 0) :
    I.Rres (recipe3 T e' f' u' c)
      = Polynomial.X ^ f'
        - ∑ t ∈ Finset.range f',
            Polynomial.C (I.Rgr ((f' - t) * u') (I.chainNorm 2 ((f' - t) * u'))
              * ρ.symm ((towerLabelEquiv T hπ) (c t))) * Polynomial.X ^ t
```
(the multiplicative prescription and the per-height iff read off this + C.99/C.100, as the
PROOF field routes them.)

**DEPENDS.** C.55 (the hypothesis supplier at leaves) · C.92 · C.99 · C.100 · C.84 (the
lifts).

**PROOF.** B′(5)'s sum + B″'s (6) + the substitution audit (`w^{f₃}ψ₃(y/w)` exact); the
R3-3-completed `α := e₃f₃(w₃ + λ₃)` display opens the proof.

**SIZE.** 36 lines.

**SOURCE.** `EFF.GENTOW2.25` (the r3-RESTATED statement, verbatim — SUPERSESSION:
replacement; the pre-r3 display DEAD; **the ϑ ORIENTATION RECORD in that unit is the
D-table's source text (GC-14) — cited by anchor, not restated here**); `.26` (proof);
`.88` (R3-3).

**TEETH.** PE4 LD2 + PE5 GREEN 91/0 + the byte-pinned statement ledger rows → retained;
§13 fires the witness prescription at `q = 2` (letter-dead: on-the-nose) AND `q = 3`
(letter-live: twisted) — the pair EXHIBITS the ψ vs ψ^{(w)} divergence, GC-11's
coincidence-regime discipline at its sharpest.

**ENVIRONMENT.** ENV-C3 + `[FGMNCalculus]`.

---

### NODE C.102 [lemma] [fresh]

**STATEMENT.** *The letter formula and its species.* `z₂ = η₂ · z₁^{−⌊ℓ₁u₂/e₁⌋}` under
the canonical evaluation identification — the FGMN letter is the repo letter times a
`z₁`-power; on the nose exactly when `z₁^{⌊ℓ₁u₂/e₁⌋} = 1` (e.g. `f₁ = 1` over `q = 2` —
the C-H12 coincidence made a THEOREM: the letter-dead perimeter is characterized). Its
three consequences (`EFF.GENTOW2.39`) transcribed as companions, including the species of
the `i = 1` cross-frame unit (C.89(ii)'s supplier: the `u1` shape is a fixed
`z₁`-letter-power).

**SIGNATURE** [signed: A-C.1 — elaborated in `leanspec/Leanspec/ChapC.lean`; inverse-free
form (`z₂·z₁^κ = ρ⁻¹(η₂)`); **⚠ DETERMINATION FLAGGED for the cross-read:** the exponent
`⌊ℓ₁u₂/e₁⌋` is read at `ℓ₁ = e₂` (the level-2 clearing denominator), i.e.
`κ := T.e₂ * T.u₂ / F.e₁` — verify against `EFF.GENTOW2.37` before fleet landing].
```lean
namespace Uniformity.Density.Tower

theorem letter_formula {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀}
    (T : TowerDatum F H₀ hpin) (hπ : Irreducible π) (hh : 1 ≤ F.h)
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [Finite (ResidueField O)]
    (e' f' u' : ℕ) [I : FGMNCalculus (T.deepTower hπ) e' f' u']
    (ρ : (T.deepTower hπ).fld 2 ≃+* AdjoinRoot T.ψ₂) :
    I.letterZ 2 * I.letterZ 1 ^ (T.e₂ * T.u₂ / F.e₁) = ρ.symm (AdjoinRoot.root T.ψ₂)
```

**DEPENDS.** C.19 · C.44 · C.92 · C.99's γ-calculus companion.

**PROOF (route).** `EFF.GENTOW2.38`'s derivation through the γ-calculus.

**SIZE.** 26 lines.

**SOURCE.** `EFF.GENTOW2.37`/.38 (statement + proof); `.39` (the three consequences);
`.05`'s ψ₂-row (the twist-aware identification this formula quantifies).

**TEETH.** LP1 (the letter-live probe: "the TOOTH fired: `η₂ ≠ z₂`") → retained — it
guards against the pre-repair `(η₂ ↔ z₂)` conflation, which is DEAD.

**ENVIRONMENT.** ENV-C3 + `[FGMNCalculus]`.

---

### NODE C.103 [theorem] [fresh] (over `[FGMNCalculus]`)

**STATEMENT.** *THEOREM GENTOW2-A: the depth-3 key certificate (the `i = 2` instance of
C.90, concrete-witness-grade).* At the S2 recipe data with an admissible target: `Φ₃` is a
key/prime polynomial for `ν = µ₃` with residual `ψ₃^{(w)}`, NOT `ν`-equivalent to `Φ₂` —
the certificate run: additivity + eq (14) give the residual; degree-forcing [Q6] +
Lemma 5.3(2) [Q4] give `KP(ν)`-membership; Lemma 1.11 [Q1] + Cor 1.13 [Q2] give prime;
`R(Φ₃) ≠ 1 = R(Φ₂)` gives non-equivalence. (The `[Q10]`-scope (H-b) chain clause is
STRUCK — TOWERRAT-R3-1; the proof consumes Cor 6.4 only at its displayed quantifier.)

**SIGNATURE** [signed: A-C.1 — elaborated in `leanspec/Leanspec/ChapC.lean`; the
admissible-target hypothesis is `hadm` (irreducible residual of the displayed degree); the
STRUCK (H-b)/`ν`-optimality clause is NOT in the statement].
```lean
namespace Uniformity.Density.Tower

theorem gentow2_A {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀}
    (T : TowerDatum F H₀ hpin) (hπ : Irreducible π) (hh : 1 ≤ F.h)
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [Finite (ResidueField O)]
    (e' f' u' : ℕ) [I : FGMNCalculus (T.deepTower hπ) e' f' u']
    (hkey : I.keyAt 2 = composedKey T)
    (ρ : (T.deepTower hπ).fld 2 ≃+* AdjoinRoot T.ψ₂)
    (hκ : T.e₂ * T.f₂ * T.u₂ < u') (he' : 0 < e') (hf' : 0 < f')
    (hcop : Nat.Coprime u' e')
    (c : ℕ → AdjoinRoot (towerLabel T)) (hc0 : c 0 ≠ 0)
    (hadm : Irreducible (I.Rres (recipe3 T e' f' u' c)) ∧
      (I.Rres (recipe3 T e' f' u' c)).natDegree = f') :
    I.KP (recipe3 T e' f' u' c) ∧ Irreducible (recipe3 T e' f' u' c) ∧
    ¬ I.nuEquiv (recipe3 T e' f' u' c) (composedKey T)
```

**DEPENDS.** C.92 · C.97 · C.99 · C.100 · C.101.

**PROOF (route).** `EFF.GENTOW2.21`–`.23`'s certificate run, by cited field names.

**SIZE.** 34 lines.

**SOURCE.** `EFF.GENTOW2.20` (the theorem); `.21`–`.23` (proofs); `.86` (R3-1's STRUCK
scope clause — the (H-b) chain sentence is DEAD and this node must not consume
`ν`-optimality); `.24` (the consumption note).

**TEETH.** the sealed battery + PE5/PE6 routes → retained; C.90's `i = 2` regime cites
this node as its concrete anchor.

**ENVIRONMENT.** ENV-C3 + `[FGMNCalculus]`.

---

### NODE C.104 [def] [fresh]

**STATEMENT.** *The two-reads convention and the `ψ₂`-discipline.* (i) `(R-repo)`:
`digit g := ` C's coherent read of a `Φ₂`-free `g` at its exact grade — the
`twistRead`-family read against the ladder normalizer (C.21/C.22 at the `n̂₂`-basis),
valued in the CONCRETE `K₂` (C.12); `(R-FGMN)`: the interface's `ε₂`-normalized
coordinate (C.92 field). Both defined ONLY on `Φ₂`-free `g`, `deg g < m₃`, exact grade —
the scope fence R3-2 re-invokes (transcribed as the defs' hypothesis). (ii) The
**`ψ₂`-discipline (R3-4, standing)**: every statement in this chapter writes `ψ₂repo`
(minpoly of the repo letter `η₂` — C.42's `ψ₂` field) or `ψ₂FGMN` (the interface's
`R₂(φ₃)` — minpoly of `z₂`); the two are equal exactly up to C.102's letter twist; NO
bare `ψ₂` token appears in any C signature (a stub carrying one is a defect).

**SIGNATURE** [signed: A-C.1 — elaborated in `leanspec/Leanspec/ChapC.lean`; **A-C.1
determination:** `(R-repo)`'s coherent read IS the C.38a `dv2Res` (the per-grade
`K₂`-evaluation of the own-side residual), so `repoRead := dv2Res` — recorded; `(R-FGMN)`
is the interface's `Rgr` field, distinctly named, so the conflation is unwritable].
```lean
namespace Uniformity.Density.Tower

noncomputable def repoRead {F : KeyFrame O π} {H₀ hpin} (L : LevelDatum F H₀ hpin)
    (g : Polynomial O) : AdjoinRoot L.r :=
  dv2Res L g
```

**DEPENDS.** C.12 · C.21/C.22 · C.42 · C.92.

**A-7 NOTE.** The former fifth DEPENDS entry named the letter-formula node — a
statement-gloss citation (the "equal up to the letter twist" clause), not a proof/def
dependency of the two named carriers; it closed an SCC and is removed. The gloss stays in
the STATEMENT, where it belongs.

**PROOF.** definitional.

**SIZE.** 18 lines.

**SOURCE.** `EFF.GENTOW2.33` (the two reads, with the r2-F1 canonical-evaluation repair —
the `(η₂ ↔ z₂)` parenthetical DEAD); `.89` (R3-4's disambiguation line, verbatim).

**TEETH.** LP1 (guards the conflation) → retained.

**ENVIRONMENT.** ENV-C3.

---

### NODE C.105 [lemma] [fresh]

**STATEMENT.** *w-blindness (the invariance that makes the uncomputed `w`
consumer-invisible).* For a unit `w ∈ K₂^×` and monic `P ∈ K₂[y]`: the `w`-conjugate
`P^{(w)} := w^{deg P}·P(y/w)` is monic with `P^{(w)}(0) = w^{deg}P(0)`; it is irreducible
iff `P` is; its irreducible-factor DEGREE pattern equals `P`'s; and the induced
factor-type data (the σ-relevant reads: degrees, multiplicities, separability) are
invariant. Consequently every §9/§10 consumer that reads σ, values, degrees,
irreducibility or repo-side residue classes through a `ψ^{(w)}`-form is `w`-independent —
the corpus's "w-blind" claim as ONE lemma, consumed wherever C.90/C.101 say "w-blind".
The `w`-DISCLOSURE is carried as the docstring: `w` is measured ≠ 1 at 6 primes / 4
frames and `u₃`-dependent (PE6), its closed form OPEN — no node computes it, and this
lemma is why none needs to.

**SIGNATURE** [signed: A-C.1 — elaborated in `leanspec/Leanspec/ChapC.lean`; the degree
pattern via the UFD factor multiset].
```lean
namespace Uniformity.Density.Tower

noncomputable def wconj {K : Type*} [Field K] (w : K) (P : Polynomial K) : Polynomial K :=
  Polynomial.C (w ^ P.natDegree) * P.comp (Polynomial.C w⁻¹ * Polynomial.X)

theorem wconj_invariants {K : Type*} [Field K] (w : K) (hw : w ≠ 0) (P : Polynomial K)
    (hP : P.Monic) :
    (wconj w P).Monic ∧ (wconj w P).natDegree = P.natDegree ∧
    (wconj w P).coeff 0 = w ^ P.natDegree * P.coeff 0 ∧
    (Irreducible (wconj w P) ↔ Irreducible P) ∧
    ((wconj w P).Separable ↔ P.Separable) ∧
    Multiset.map Polynomial.natDegree (UniqueFactorizationMonoid.factors (wconj w P))
      = Multiset.map Polynomial.natDegree (UniqueFactorizationMonoid.factors P)
```

**DEPENDS.** none beyond mathlib (`Polynomial.scaleRoots`-family; landed
`irreducible_scaleRoots_iff`, `typeOf_scale`-shapes at the residue level).

**PROOF.** the substitution `y ↦ wy` is a `K`-algebra automorphism of `K[y]` composed
with unit scaling; every listed invariant transports.

**SIZE.** 24 lines.

**SOURCE.** `EFF.GENTOW2.25`'s w-clauses + `.82`/.83 (the w-disclosure brackets + the
honest scope note: "measured at 4 frames … does not decide `w_i` at unmeasured frames or
levels `i > 2`"); `EFF.GENTOW5.27`'s w-blindness list.

**TEETH.** the PE6 w-measurement rows → retained (they guard the DISCLOSURE, not the
lemma); the lemma itself is fully proved.

**ENVIRONMENT.** ENV-C4.

---

### NODE C.106 [lemma] [fresh] — **the §10 supply manifest**

**STATEMENT.** *What chapters D and F consume from here, as one documented `#check`
block.* The manifest node (CHAP-G G.30 / C.93 pattern): `B″ = C.99`; `B′ = C.100`
(direction (3), never inverted); `B-law + prescription = C.101`; the S2 witness = C.97;
the shear = C.98; the letter formula = C.102; the certificate = C.103; the reads/naming
= C.104; w-blindness = C.105; the ϑ four-way orientation = **chapter D's table (GC-14),
sourced at `EFF.GENTOW2.25`'s orientation record** — this chapter cites the anchor and
supplies the RATIO-form statements only. Rows 23–24 of GENTOW2's S6.1 are DESCRIPTIVE
(HYP.66/HYP.145's gate) and have NO node — recorded here so no consumer invents one.

**SIGNATURE** [signed: A-C.1]. documentation node (`#check` suite; no new Prop) — landed as
the `C106Manifest` section in `leanspec/Leanspec/ChapC.lean` (ten `#check`s over the §10
names, each with its manifest-row comment).

**DEPENDS.** C.97–C.105.

**PROOF.** mechanical. **SIZE.** 14 lines.

**SOURCE.** `EFF.GENTOW2.52` (the consumed-statement inventory); `.78` (rows 23–24
DESCRIPTIVE, verbatim gate); PA-3(i) (the czar assignment this section discharges).

**TEETH.** none (manifest). **ENVIRONMENT.** ENV-C1.

---

---

## 11. §11 — THE HT COUNT LAYER (`LEMMA W12-HT`, PA-5)

> ⚠ **[AMENDED: A-C.2, 2026-08-16 — the defect-repair amendment on the C.109 refutation.]**
> C.108's `htCell` pin and `HTNode`'s free `L`/`sides` were re-signed to the source's own
> conditions (`EFF.W12.23`'s three-way membership law; `EFF.W12.83`'s `L_v` display), C.109
> gains the inline well-formedness hypothesis `hwf : v.WF` and the NEW bridge node C.109a,
> C.111 is re-signed to the honest per-node-hypothesis telescope, and **C.114's two count
> axioms are WITHDRAWN (machine-refuted as frozen) — the node is BLOCKED pending the
> realizes-refinement re-sign (A-C.3 target)**. C.110/C.112/C.113/C.115 audited clean.
> Certification: `verification/c109_ac2_cell_check.py` (127 checks); machine refutations:
> `leanfinal/Uniformity/ChapC/C109_REFUTATION.lean.txt`, `C111_C114_REFUTATION.lean.txt`.
> Full record: the A-§ block, entry **A-C.2**.

> **Design note.** `EFF.W12.83`–`.87` at exactly corpus strength (C-H7): per-member at
> explicit `N` (GC-9.3 — no uniform-`N` law), σ through `monicFactors` at every-lift
> strength where the corpus certifies "for every disc-nonzero lift" (the GC-9.1 divergence,
> flagged per node), `B-BOX-1` inherited at `d ≥ 2` exactly through B.55/B.58 (C.113), and
> the thin-verification disclosure (grid `n ∈ {3,4}, q ∈ {2,3}, N ≤ 6`, no hostile arc)
> carried at C.116 with GC-11's extra-force gates. **One genuine simplification, flagged
> for the cross-read (§16):** the corpus consumes `GENIND-1` at fracture permanence
> (`HYP.121`, UNAUDITED interface — CHAP-H H-3); the Lean recast works on FACTORS (the
> dissection's factorization `f = ∏ gᵢ`), where "later translations internal to one
> cluster neither alter nor re-couple the others" is discharged by factorization
> uniqueness (landed `monic_factorization_unique`) — **the HT chain here does NOT inherit
> `HYP.121`**. Counting is over `Coeff O n N`-classes (landed carriers), so every count is
> a `Finset.card` statement.

### NODE C.107 [def] [fresh]

**STATEMENT.** *The residual censuses.* Over a finite field `K` (ENV-C4): `S_λ(K)` — the
number of monic polynomials over `K` with nonzero constant term and prescribed
factorization type `λ` (the side-census of `(HT-rec)`); and the level-0 configuration
census `C₀(q)` — the number of monic squarefree-type configurations realizing the datum
`{(d_i, m_i)}` (distinct monic irreducibles `P̄_i` of the prescribed degrees). Both as
`Finset.card` definitions with the standard generating identities as companions where
§13's gates need spot values.

**SIGNATURE** [signed: A-C.1 — elaborated in `leanspec/Leanspec/ChapC.lean`; `λ` through
GC-4's landed carrier via the new `residualTypeOf`; stated over `CommRing` + UFD binders so
the defs apply at `resField φ`'s OWN ring structure (no `Field`-instance diamond — the
binders are derivable from `IsKey φ` at every consumer)].
```lean
namespace Uniformity.Density.Tower

noncomputable def residualTypeOf {K : Type*} [CommRing K] [IsDomain K]
    [UniqueFactorizationMonoid K] (p : Polynomial K) : FactorizationType :=
  open Classical in
  ⟨(UniqueFactorizationMonoid.factors p).toFinset.val.map
    (fun q => (q.natDegree, (UniqueFactorizationMonoid.factors p).count q))⟩

noncomputable def sideCensus (K : Type*) [CommRing K] [IsDomain K]
    [UniqueFactorizationMonoid K] [Finite K] (lam : FactorizationType) : ℕ :=
  Nat.card {p : Polynomial K // p.Monic ∧ p.coeff 0 ≠ 0 ∧ residualTypeOf p = lam}

noncomputable def configCensus (K : Type*) [CommRing K] [IsDomain K] (d : Multiset ℕ) : ℕ :=
  Nat.card {P : Multiset (Polynomial K) //
    P.map Polynomial.natDegree = d ∧ (∀ q ∈ P, q.Monic ∧ Irreducible q) ∧ P.Nodup}
```

**DEPENDS.** landed `FactorizationType` (GC-4's carrier for `λ`) · B.26/B.27's ENV-D
census toolkit shapes.

**PROOF.** definitional. **SIZE.** 20 lines.

**SOURCE.** `EFF.W12.83` (the `S_{λ_{v,S}}(Q_i)` and `C₀(q)` objects); GC-4 (λ through
the landed carrier).

**TEETH.** spot values at §13. **ENVIRONMENT.** ENV-C4.

---

### NODE C.108 [def] [fresh]

**STATEMENT.** *The order-1 refinement tree and its node quantities.* The `HTTree` datum:
a finite tree per repeated branch `i` (degree `d_i`, `Q_i = q^{d_i}`), each node `v`
carrying multiplicity `m_v`, previous center depth `s_v` (0 at the root), the exact
polygon data `P_v` (heights, in C's argmin carriers), and per-side residual types
`λ_{v,S}`; children = repeated LINEAR factors on `e = 1` sides (slope `−s_u`); repeated
factors of degree `> 1` or on `e > 1` sides are NOT children (they open composite stages —
outside the order-1 statement, the fence transcribed as a structure invariant). Node
quantities: `B_v(N) = m_v·N − Σ_{j<m_v}⌈P_v(j)⌉ − L_v` (with `L_v` the integral-boundary
count), `D_v(N) = Σ_{j<m_v} max(N − ((m_v−j)s_v + 1), 0)` (note the CLIP — the same
`max(0, ·)` discipline as C.53), the conservative cell
`C_{m_v}(s_v) = {(a_j) : v(a_j) ≥ (m_v−j)s_v + 1}`, and the SIDE-TAGGED orbit factor
`κ_v = ∏_{S,a} r_{v,S,a}!/∏_H r_{v,S,a,H}!` ("the side tag is necessary because roots on
different sides cannot be permuted"), plus `κ₀(T)` at level 0.

**SIGNATURE** [signed: A-C.1 — elaborated in `leanspec/Leanspec/ChapC.lean`;
**re-signed: A-C.2, 2026-08-16** — `htCell`'s pin clause and the NEW well-formedness
apparatus; full record in the A-§ block]. A-C.1
determinations: the tree is INDEX-ENCODED (`nodes : List HTNode`, `parent : ℕ → ℕ`, root 0,
well-formedness `parent i < i` — no nested-inductive recursion); `HTNode` carries the CEILED
pin data (`Pceil : ℕ → ℕ` — `ℚ`-free per the parenthetical), the side set as
`sides : Finset (ℕ × ℕ)` with `sideType : ℕ → ℕ → FactorizationType`, and `κ_v` as a DATA
field `kappa` (its side-tagged factorial rule is the corpus's computation, recorded in the
docstring; C.116 keeps the tags mandatory). **A-C.2 determination:** `L`, `sides` and the
types' degrees are data fields but NOT free — the corpus determines them from the polygon
(`EFF.W12.83` defines `L_v = #{j < m_v : P_v(j) ∈ ℤ}` inside the `B_v` display; the census
product ranges over `S ⊂ P_v`), and the frozen C.109 quantifying over unconstrained nodes
was machine-refuted.  The coherence is the predicate `HTNode.WF` (displayed below), built
from ℚ-free chord tests on `Pceil` (the hull of the ceiled points IS the polygon — the
ceiling raises non-vertex points by `< 1` and fixes vertices, and a convex minorant through
the vertices is the hull); every §11 count law takes `v.WF` INLINE (the B.42 lesson: no
section auto-inclusion). Quantities:
```lean
namespace Uniformity.Density.Tower

structure HTNode where
  m : ℕ
  s : ℕ
  Pceil : ℕ → ℕ
  L : ℕ
  sides : Finset (ℕ × ℕ)
  sideType : ℕ → ℕ → FactorizationType
  kappa : ℕ

def HTNode.B (v : HTNode) (N : ℕ) : ℕ :=
  v.m * N - (∑ j ∈ Finset.range v.m, v.Pceil j) - v.L
def HTNode.D (v : HTNode) (N : ℕ) : ℕ :=
  ∑ j ∈ Finset.range v.m, (N - ((v.m - j) * v.s + 1))   -- the CLIP is ℕ-subtraction

-- [A-C.2] the node polygon read off `Pceil` (chord tests; certified [ENC] leg):
def HTNode.OnHull (v : HTNode) (j : ℕ) : Prop :=          -- "P_v(j) ∈ ℤ" under WF
  ∀ i k : ℕ, i ≤ j → j ≤ k → k ≤ v.m →
    (k - i) * v.Pceil j ≤ (k - j) * v.Pceil i + (j - i) * v.Pceil k
def HTNode.IsVertex (v : HTNode) (j : ℕ) : Prop :=        -- vertex of the hull
  ∀ i k : ℕ, i < j → j < k → k ≤ v.m →
    (k - i) * v.Pceil j < (k - j) * v.Pceil i + (j - i) * v.Pceil k
def HTNode.NodeOnSide (v : HTNode) (u ℓ j : ℕ) : Prop :=  -- B.16's OnSide at node data
  ∀ i : ℕ, i ≤ v.m → ℓ * v.Pceil j + u * j ≤ ℓ * v.Pceil i + u * i
noncomputable def HTNode.nodeSideSet (v : HTNode) (u ℓ : ℕ) : Finset ℕ :=
  open Classical in (Finset.range (v.m + 1)).filter (v.NodeOnSide u ℓ)
def HTNode.IsSide (v : HTNode) (u ℓ : ℕ) : Prop :=
  0 < ℓ ∧ Nat.Coprime u ℓ ∧ 2 ≤ (v.nodeSideSet u ℓ).card
noncomputable def HTNode.nodeSideDeg (v : HTNode) (u ℓ : ℕ) : ℕ :=
  ((v.nodeSideSet u ℓ).max.getD 0 - (v.nodeSideSet u ℓ).min.getD 0) / ℓ

open Classical in
def HTNode.WF (v : HTNode) : Prop :=                      -- [A-C.2] node coherence
  v.Pceil v.m = 0 ∧
  (∀ i j k : ℕ, i ≤ j → j ≤ k → k ≤ v.m → i < k →
    (k - i) * v.Pceil j < (k - j) * v.Pceil i + (j - i) * v.Pceil k + (k - i)) ∧
  v.L = ((Finset.range v.m).filter v.OnHull).card ∧
  (∀ u ℓ : ℕ, ((u, ℓ) ∈ v.sides ↔ v.IsSide u ℓ)) ∧
  (∀ u ℓ : ℕ, (u, ℓ) ∈ v.sides → (v.sideType u ℓ).degree = v.nodeSideDeg u ℓ)

structure HTTree where
  nodes : List HTNode
  parent : ℕ → ℕ
def HTTree.WF (t : HTTree) : Prop := ∀ i, 0 < i → i < t.nodes.length → t.parent i < i

def conservativeCell (m s : ℕ) : Set (ℕ → ℕ∞) :=
  {P | ∀ j < m, (((m - j) * s + 1 : ℕ) : ℕ∞) ≤ P j}

def htCell (π : O) (Φ : Polynomial O) [IsDomain (resField Φ)]
    [UniqueFactorizationMonoid (resField Φ)] (v : HTNode) : Set (Polynomial O) :=
  {f | f.Monic ∧ f.natDegree = v.m * Φ.natDegree ∧
    (∀ j, j ≤ v.m → (v.Pceil j : ℕ∞) ≤ npHgt Φ f j) ∧            -- [A-C.2] ≥ everywhere
    (∀ j, j ≤ v.m → v.IsVertex j → npHgt Φ f j = (v.Pceil j : ℕ∞)) ∧ -- = at vertices
    ∀ u ℓ : ℕ, 0 < ℓ → Nat.Coprime u ℓ → (u, ℓ) ∈ v.sides →
      ∀ (hne : (sideSet Φ f u ℓ).Nonempty) (H₀ : ℕ),
        npHgt Φ f (sideMin Φ f u ℓ hne) = (H₀ : ℕ∞) →
        residualTypeOf (resPoly π Φ f u ℓ hne H₀) = v.sideType u ℓ}
```
(the retired A-C.1 pin clause `npHgt Φ f j = (v.Pceil j : ℕ∞)` at every `j ≤ m`
contradicted `EFF.W12.23`'s three-way membership law — on-side lattice digits are
"possibly zero"; the re-sign IS that law in ceiled form — A-C.2, certified at mutation M3)
plus the count-formula defs `htBranchCount (Q census t N)` and
`htGlobalCount (S q census N)` over `HTShape` (branches `(d_i, m_i, tree_i)` + `κ₀`) — the
`(HT-branch)`/`(HT-global)` display arithmetic, machine-typed; full text at the leanspec
twin (byte-fixed there).

**DEPENDS.** C.06/C.07 (polygon carriers) · C.107 · landed `Coeff`, `proj`.

**PROOF.** definitional. **SIZE.** 40 lines.

**SOURCE.** `EFF.W12.83` (setting, verbatim: the datum, `B_v`, `D_v`, `C_{m_v}(s_v)`,
`(HT-orbit)` with the side-tag rationale and the `side_index` convention note);
**[A-C.2]** `EFF.W12.23` (the three-way membership law, verbatim — the cell's pin clauses)
and `EFF.W12.24` (the priced-digit count with `L` = "lattice point on the polygon" — the
`WF` laws).

**TEETH.** the N1 certificate's `side_index` grouping → the side-tag is guarded by
DROP-teeth (C.116); **[A-C.2]** `verification/c109_ac2_cell_check.py` — the `[ENC]` leg
(chord tests ≡ rational hull geometry) and mutation M3 (the retired pin) → **executable
regression** retained. **ENVIRONMENT.** ENV-C3.

---

### NODE C.109a [lemma] [fresh] — **[NEW: A-C.2] the level-`N` development bridge**

**STATEMENT.** *The `Φ`-adic development ↔ coefficient-box bridge at level `N`.* For monic
`Φ` of positive degree: the level-`N` coefficient box of monic degree-`m·d` polynomials is
in bijection with `m`-tuples of level-`N` degree-`< d` blocks, THROUGH the development —
`Coeff O (m·d) N ≃ (Fin m → Coeff O d N)`, the forward map reading, at any lift, the
level-`N` classes of `dev`'s coefficient vectors. Level-`N` well-definedness of `dev`
(monic division preserves coefficientwise congruence mod `π^N` — B.10's content one level
up) is PART of the claim: the componentwise spec at an arbitrary lift is contradictory
without it. This is the node the C.109 refutation record named as C.109's real cost
(*"formalizing it needs the level-`N` development↔coefficient-box bridge … which does not
exist in `leanfinal` yet"*), and it is where `EFF.W12.23`'s *"Monic division gives the
UNIQUE `Φ`-adic development … `f ↦ (a_j)_{j<m}` is a bijection"* lands as a reusable
carrier. Consumed by C.109's slot count, C.110's `ht_conservative_card` (the same block
decomposition at the conservative cell), and C.114's strata.

**SIGNATURE** [signed: A-C.2 — elaborated in `leanspec/Leanspec/ChapC.lean`; `∃`-form (a
single Prop axiom stub — no data axiom in the spec bank), the equivalence pinned
componentwise through `dev` at an arbitrary lift].
```lean
namespace Uniformity.Density.Tower

theorem dev_box_bridge {Φ : Polynomial O} (hΦm : Φ.Monic) (hΦd : 0 < Φ.natDegree)
    (m N : ℕ) :
    ∃ E : Coeff O (m * Φ.natDegree) N ≃ (Fin m → Coeff O Φ.natDegree N),
      ∀ (a : Fin (m * Φ.natDegree) → O) (j : Fin m) (i : Fin Φ.natDegree),
        E (proj O (m * Φ.natDegree) N a) j i
          = Ideal.Quotient.mk ((IsLocalRing.maximalIdeal O) ^ N)
              ((dev Φ (monicPoly a) (j : ℕ)).coeff (i : ℕ))
```

**DEPENDS.** B.02–B.06 (`dev`, the development calculus) · B.10 (well-definedness — the
congruence leg) · landed `Coeff`/`proj`/`monicPoly`.

**PROOF (route).** forward: well-defined by the congruence leg (division by monic `Φ`
preserves mod-`π^N` congruence coefficientwise), so the spec determines `E` on every class
(`proj` surjective); injective: two developments block-congruent mod `π^N` reassemble to
coefficientwise-congruent polynomials (the development is a triangular change of
coordinates); surjective: assemble `f = Φ^m + Σ ã_j Φ^j` from arbitrary block lifts and
read the development back by uniqueness of monic division.

**SIZE.** ~40 lines.

**SOURCE.** `EFF.W12.23` (the development display + bijection sentence, verbatim); the
C.109 refutation record (`C109_REFUTATION.lean.txt`, "A second, deeper failure" — the
named cost).

**TEETH.** `verification/c109_ac2_cell_check.py` computes every LHS through exactly this
bridge (dev-blocks over `ℤ/p^N`) — 13 instances green. **ENVIRONMENT.** ENV-C1 (pure
algebra: no completeness, no finiteness).

---

### NODE C.109 [lemma] [fresh]

**STATEMENT.** *Step 1 — the exact node cell.* On one degree-`d_i` branch, with the
`Φ`-adic window development (`F = Φ^m + Σ a_jΦ^j`, `a_j ∈ (O/π^N)[x]_{<d_i}` — B's `dev`
at level `N` through `Coeff`-classes): prescribing the polygon `P_v` leaves
`m·N − Σ⌈P_v(j)⌉` digit slots; each of the `L_v` integral boundary positions prices one
digit by the residual; hence, after fixing the actual residual polynomials,
`#E_v(𝐑) = Q^{B_v(N)}` — S2.2's digit calculation, **no separability needed**; summing
residual letters of the prescribed types contributes exactly `∏_S S_{λ_{v,S}}(Q)` with no
extra unit factor (the right-to-left sweep: one side's monic normalization fixes the
shared vertex unit for the next — C.25's fixed-convention reads, level-1 instance).

**SIGNATURE** [signed: A-C.1; **re-signed: A-C.2, 2026-08-16** — gains `(hwf : v.WF)`
INLINE (the B.42 lesson). The frozen form (free `v`) is machine-refuted:
`leanfinal/Uniformity/ChapC/C109_REFUTATION.lean.txt` derives `False` from it at every
model of its own binders (two nodes differing only in the unread `L`), and the record's
secondary arithmetic (no `L` repairs an empty `sides` at `Q ≥ 3`) is numerically VERIFIED
at mutation M2 of `verification/c109_ac2_cell_check.py`. The re-signed law is certified at
13 exact-count instances (q = 2, 3, and Q = 4 via a degree-2 key; steep/interior-lattice/
`ℓ = 2`/flat/shared-vertex polygons). Elaborated in `leanspec/Leanspec/ChapC.lean`; the two
S2.2 clauses in one card identity: `Q^{B_v(N)}` digits × the census product; base
`Q = Nat.card (resField Φ)`].
```lean
namespace Uniformity.Density.Tower

theorem ht_node_cell_card (hπ : Irreducible π)
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [Finite (ResidueField O)]
    {Φ : Polynomial O} (hΦ : IsKey Φ)
    [IsDomain (resField Φ)] [UniqueFactorizationMonoid (resField Φ)]
    [Finite (resField Φ)]  -- all derivable from hΦ; binders for elaboration
    (v : HTNode) (hwf : v.WF) (N : ℕ) (hvis : ∀ j, j ≤ v.m → v.Pceil j < N) :
    Nat.card {c : Coeff O (v.m * Φ.natDegree) N //
        ∃ a : Fin (v.m * Φ.natDegree) → O,
          proj O (v.m * Φ.natDegree) N a = c ∧ monicPoly a ∈ htCell π Φ v}
      = Nat.card (resField Φ) ^ v.B N
        * ∏ p ∈ v.sides, sideCensus (resField Φ) (v.sideType p.1 p.2)
```

**DEPENDS.** C.107 · C.108 (incl. the A-C.2 `WF` apparatus) · **C.109a (the development
bridge — the refutation record's named cost, now a node)** · B.20 (`sideLen`/`sideDeg` —
H-10's named ingredient) · B.24 (`digAt`/`digPoly`) · B.28/B.30 (the priced digits) ·
landed `card_coeff`.

**PROOF (route).** through C.109a's bridge to the block boxes; then the slot count + the
priced-digit count, per side right-to-left (`EFF.W12.24`'s sweep: the rightmost side's
monic top is the polynomial's leading `1`; each side's census fixes its left-vertex unit
for the next side — no extra unit factor).

**SIZE.** 36 lines (+ C.109a's 40).

**SOURCE.** `EFF.W12.84` step 1 (verbatim); **[A-C.2]** `EFF.W12.24` (the count + census
normalization displays, verbatim — the `L` and sweep laws the re-sign enforces).

**TEETH.** the certificate's per-key comparisons (C.116) → retained; §13 spot-fires one
cell count at each prime; **[A-C.2]** `verification/c109_ac2_cell_check.py` (13 law
instances + mutations M1/M2/M3 all killing) → **executable regression** retained.

**ENVIRONMENT.** ENV-C3.

---

### NODE C.110 [theorem] [fresh]

**STATEMENT.** *Step 2 — transfer at one repeated linear root.* Let `(Y − z)^a` be a
repeated factor on an `e = 1` side of slope `−k`; isolate its cluster factor `G` by the
residual dissection (B.48). Choosing a lift `z̃` and recentering `Ψ = Φ − z̃π^k`:
`(b_j) ∈ C_a(k)` (i.e. `v(b_j) ≥ (a−j)k + 1`) iff the normalized residual of the
translate is `Y^a` — the binomial vanishing after `π^{(a−j)k}`-normalization; translation
is unitriangular on the finite coefficient module (block-unitriangular at `d_i > 1`, the
monic-redivision digit calculus), hence bijective **in every characteristic and at every
finite window, including when conservative bounds lie beyond the window**; and
`#C_a(k) = Q^{D_u(N)}`. Changing the lift composes with another unitriangular translation
— the node and fiber size are lift-independent.

**SIGNATURE** [signed: A-C.1 — elaborated in `leanspec/Leanspec/ChapC.lean`; split → 2:
`ht_conservative_card` (the `#C_a(k) = Q^{D_u(N)}` count at general block degree `d` — the
`d·Σ`-exponent is the `Q = q^d` clearing) and `ht_transfer_residual_iff` (the
translate-residual iff at the `(k, 1)`-side, `z̄` mapped up through `algebraMap`); the
unitriangular-bijection and lift-independence legs are the fleet's proof content].
```lean
namespace Uniformity.Density.Tower

theorem ht_conservative_card (hπ : Irreducible π) [Finite (ResidueField O)]
    (d a k N : ℕ) (hd : 0 < d) (hk : 0 < k) :
    Nat.card {c : Coeff O (a * d) N //
        ∃ b : Fin (a * d) → O, proj O (a * d) N b = c ∧
          ∀ i : Fin (a * d), (((a - i.1 / d) * k + 1 : ℕ) : ℕ∞) ≤ addVal O (b i)}
      = residueCard O ^ (d * ∑ j ∈ Finset.range a, (N - ((a - j) * k + 1)))

theorem ht_transfer_residual_iff (hπ : Irreducible π)
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [Finite (ResidueField O)]
    {Φ : Polynomial O} (hΦ : IsKey Φ) {a k : ℕ} (ha : 2 ≤ a) (hk : 0 < k)
    (z : O) {G : Polynomial O} (hG : G.Monic) (hGdeg : G.natDegree = a * Φ.natDegree)
    (hpure : IsPure Φ G k 1) (hne : (sideSet Φ G k 1).Nonempty) {H₀ : ℕ}
    (hp : npHgt Φ G (sideMin Φ G k 1 hne) = (H₀ : ℕ∞)) :
    (∀ j, j < a →
        (((a - j) * k + 1 : ℕ) : ℕ∞) ≤ npHgt (Φ - Polynomial.C (z * π ^ k)) G j)
      ↔ resPoly π Φ G k 1 hne H₀
          = (Polynomial.X - Polynomial.C (algebraMap (ResidueField O) (resField Φ)
              (digAt π 0 z))) ^ a
```

**DEPENDS.** C.108 · B.02–B.06 (developments at two keys) · B.48 (the cluster isolation)
· B.69 (shift covariance — H-10's descent-step routing: "B.69's SOURCE routes it here",
discharged) · landed `card_coeff`.

**PROOF (route).** `EFF.W12.84` step 2, verbatim route; the W-11 S2.3 mechanism without
the quadratic restriction.

**SIZE.** 2 × ~35 lines.

**SOURCE.** `EFF.W12.84` step 2 (verbatim); CHAP-B B.69 (whose SOURCE field names this
section as the consumer — the loop closes here).

**TEETH.** the certificate's 300 translation-rank tests → retained; §13 fires one
translate at each prime.

**ENVIRONMENT.** ENV-C3.

---

### NODE C.111 [theorem] [fresh]

**STATEMENT.** *Step 3 — simultaneous children and the free fiber `(HT-fiber)`.* At each
weighted digit height the multiplication linearization
`(A_α) ↦ Σ_α A_α∏_{β≠α}Ḡ_β` is an isomorphism (coprimality + degree bound + equal digit
dimension — the W12-S2.1 mechanism on weighted side modules, = B.37–B.40's
`GradedCoprime` engine at the weighted grading); solving by height gives the
finite-window multiplication bijection; the child coordinates occur independently and
simultaneously — **in the factor representation this is factorization uniqueness**
(landed `monic_factorization_unique`; the corpus's GENIND-1/fracture-permanence
consumption is discharged representation-side, `HYP.121` NOT inherited — FAITHFULNESS
flag, §16); hence

```
E_v(𝐑) ≃ U_v(𝐑) × ∏_{u child} C_{m_u}(s_u),    #U_v(𝐑) = Q^{B_v(N) − Σ_u D_u(N)},
```

the exponent a nonnegative integer BY the bijection (divisibility is a consequence, not
an assumption).

**SIGNATURE** [signed: A-C.1 AT THE ARITHMETIC SHADOW; **re-signed: A-C.2, 2026-08-16** —
the frozen form (hypotheses `hwf` + `hvis` only) is machine-refuted
(`C111_C114_REFUTATION.lean.txt`, `c111_frozen_false`: the tree data ties a child's `s` to
NOTHING, so a child at `s = 0` has `D = m(N−1)` while a steep polygon drives every `B` to
`0`), and per-node `HTNode.WF` cannot rescue it (numeric leg [C111] of the certification —
the WF-resistant instance). The corpus derives nonnegativity PER NODE from the fiber
bijection (`EFF.W12.85`: `#U_v(𝐑) = Q^{B_v(N)−Σ_u D_u(N)}`, *"the exponent is a nonnegative
integer"* — a property of REALIZED nodes), so the honest arithmetic shadow carries the
per-node inequality as the hypothesis `hnode`, discharged by the fleet's bijection at
realized nodes, and keeps the telescope over the parent map as this node's content. `hvis`
DROPPED as dead weight (the A-F.12 minimality rule: never instantiable content). The
multiplication-bijection engine and the set-level fiber assembly remain the BOOKED
B.37–B.40 weighted-grading RE-PLAN (the node's own DEPENDS expected it) — recorded].
```lean
namespace Uniformity.Density.Tower

theorem ht_fiber_exponent_nonneg (t : HTTree) (hwf : t.WF) (N : ℕ)
    (hnode : ∀ i, i < t.nodes.length →
      ((((List.range t.nodes.length).drop 1).filter (fun u => t.parent u == i)).map
        (fun u => (t.nodes.getD u HTNode.default0).D N)).sum
        ≤ (t.nodes.getD i HTNode.default0).B N) :
    (((List.range t.nodes.length).drop 1).map
        (fun i => (t.nodes.getD i HTNode.default0).D N)).sum
      ≤ ((List.range t.nodes.length).map
        (fun i => (t.nodes.getD i HTNode.default0).B N)).sum
```

**DEPENDS.** C.109 · C.110 · B.37–B.40 (the graded-coprime engine, consumed or re-run at
the weighted grading — RE-PLAN if a weighted-grading generalization of B.39 is needed as
a shared helper; expected) · landed `monic_factorization_unique`.

**PROOF (route).** `EFF.W12.85` step 3, verbatim route.

**SIZE.** 2 × ~35 lines.

**SOURCE.** `EFF.W12.85` step 3 (verbatim, incl. the nonnegativity remark and the
specialization notes).

**TEETH.** 322 coprime-multiplication-rank tests → retained.

**ENVIRONMENT.** ENV-C3.

---

### NODE C.112 [lemma] [fresh]

**STATEMENT.** *Step 4 — histories and orbit factors: `(HT-rec)`.* Replacing each child
cell by its selected-history subset gives the relative factor `#(u)/Q^{D_u(N)}`; the
multiset-to-actual-roots assignment count on one side is `r_{v,S,a}!/∏_H r_{v,S,a,H}!`;
multiplying and inserting into `(HT-fiber)`:

```
#(v) = Q^{B_v(N)} · (∏_S S_{λ_{v,S}}(Q_i)) · κ_v · ∏_{u child} #(u)/Q^{D_u(N)}.
```

Concatenation-compatible (child tuples compose; unitriangular translations compose) and
fracture-compatible (uniqueness identifies the same cluster before and after sibling
operations).

**SIGNATURE** [signed: A-C.1 — elaborated in `leanspec/Leanspec/ChapC.lean`, in the
DIVISION-FREE telescope form over the formula carrier (`htBranchCount·Q^{ΣD} = ∏ per-node
factors`); the set-level recursion (concatenation/fracture compatibility) is the fleet's
proof content behind `ht_branch` (C.114)].
**[AUDITED: A-C.2 — NO re-sign.** Predicted clean and verified: `ht_rec` carries its
inequality as the explicit hypothesis `hBD` and is pure algebra over the formula carrier,
true for arbitrary trees given `hBD` — the hypothesis-carrying discipline is exactly what
the frozen C.111 lacked. `hBD` is now supplied by the re-signed C.111 (whose `hnode` the
fleet discharges at realized nodes). Set-level consumption inherits C.114's BLOCK.]
```lean
namespace Uniformity.Density.Tower

theorem ht_rec (Q : ℕ) (hQ : 2 ≤ Q) (census : FactorizationType → ℕ)
    (t : HTTree) (hwf : t.WF) (N : ℕ)
    (hBD : (((List.range t.nodes.length).drop 1).map
        (fun i => (t.nodes.getD i HTNode.default0).D N)).sum
      ≤ ((List.range t.nodes.length).map
        (fun i => (t.nodes.getD i HTNode.default0).B N)).sum) :
    htBranchCount Q census t N
        * Q ^ (((List.range t.nodes.length).drop 1).map
            (fun i => (t.nodes.getD i HTNode.default0).D N)).sum
      = ((List.range t.nodes.length).map (fun i =>
          let v := t.nodes.getD i HTNode.default0
          v.kappa * (∏ p ∈ v.sides, census (v.sideType p.1 p.2)) * Q ^ v.B N)).prod
```

**DEPENDS.** C.108 · C.109 · C.110 · C.111.

**PROOF (route).** `EFF.W12.85` step 4, verbatim.

**SIZE.** 34 lines.

**SOURCE.** `EFF.W12.85` step 4.

**TEETH.** DROP-KAPPA0 (370) + DROP-HISTORY-CENSUS (302) → retained (they kill the
κ-omission mutants).

**ENVIRONMENT.** ENV-C3.

---

### NODE C.113 [theorem] [fresh]

**STATEMENT.** *Step 5 — termination and Ore certification.* (i) Depth strictly
increases: an eligible `e = 1` child has `s_u ≥ s_v + 1` (lower-polygon convexity in the
argmin representation: every point strictly above the slope-`s_v` line through
`(m_v, 0)`); window-visibility bounds the depth (`m_v·s_v + 1 ≤ P_v(0) ≤ N − 1`); no
root-to-leaf chain is infinite. (ii) At a decided order-1 key every terminal residual is
separable, and the order-1 Ore theorem certifies one factor per terminal side factor with
its displayed `(e, f)` — **for EVERY lift of the window class** (B.79/B.82's every-lift
certificates; the corpus's "for every disc-nonzero lift" is the GC-9.1 divergence, flagged:
the Lean conclusion is strictly stronger, via `monicFactors`). **`B-BOX-1` inheritance,
exactly here:** at terminal side factors with residual degree `d ≥ 2` the `(e,f)` read is
B.58's, conditional on `B-BOX-1` — the HT chain's conditionality is exactly B's, no more
(C-H7(iii)). (iii) The order-≥ 2 fence: a repeated factor of residual degree `> 1` or on
an `e > 1` side opens a composite stage and remains under `[W12-H]` — routed to §5's
trichotomy case (c) and chapter I's box, NEVER certified here.

**SIGNATURE** [signed: A-C.1 — elaborated in `leanspec/Leanspec/ChapC.lean`; split → 2:
`ht_depth_increase` (the convexity leg in cleared argmin form — every attained side slope of
a conservative-cell member is `> s`, C.55's shape one level down; window-visibility depth
bounding rides the `Pceil` data) and `ht_leaf_certified` (the order-1 Ore certificate per
terminal side factor, with the **`B-BOX-1` inheritance as the inner hypothesis** — exactly
B's, no more)].
```lean
namespace Uniformity.Density.Tower

theorem ht_depth_increase {Φ : Polynomial O} (hΦ : IsKey Φ) {G : Polynomial O} {m s : ℕ}
    (hm : 0 < m) (hpins : ∀ j < m, (((m - j) * s + 1 : ℕ) : ℕ∞) ≤ npHgt Φ G j)
    (htop : npHgt Φ G m = (0 : ℕ∞))
    {u ℓ : ℕ} (hℓ : 0 < ℓ) (hne : (sideSet Φ G u ℓ).Nonempty) :
    ℓ * s < u

theorem ht_leaf_certified (hπ : Irreducible π)
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [Finite (ResidueField O)]
    {φ : Polynomial O} (hφ : IsKey φ) {g : Polynomial O} (hg : g.Monic)
    {u ℓ : ℕ} (hℓ : 0 < ℓ) (hcop : Nat.Coprime u ℓ) (hpure : IsPure φ g u ℓ)
    (hne : (sideSet φ g u ℓ).Nonempty) {H₀ : ℕ}
    (hp : npHgt φ g (sideMin φ g u ℓ hne) = (H₀ : ℕ∞))
    (hsep : (resPoly π φ g u ℓ hne H₀).Separable)
    {r : Polynomial (resField φ)} (hrm : r.Monic) (hri : Irreducible r)
    (hdvd : r ∣ resPoly π φ g u ℓ hne H₀) :
    ∃ gr : Polynomial O, gr.Monic ∧ gr ∣ g ∧
      gr.natDegree = ℓ * (φ.natDegree * r.natDegree) ∧
      ((∀ g' ∈ monicFactors gr, (φ.natDegree * r.natDegree) ∣ inertiaDegOf g') →
        typeOf gr = ⟨{(ℓ, φ.natDegree * r.natDegree)}⟩ ∧ Irreducible gr)
```
(clause (iii)'s order-≥ 2 fence is a routing rule, not a Lean statement — no node certifies
those; they return to §5's trichotomy case (c) and `[W12-H]`.)

**DEPENDS.** C.07/C.08 (argmin convexity arithmetic) · C.108 · B.58 (+ its `B-BOX-1`
hypothesis at `d ≥ 2`) · B.63 (NS-6: leaves separable ⟺ descent stops) · B.79/B.82 (the
certificates).

**PROOF (route).** `EFF.W12.86` step 5, verbatim; the convexity leg in cleared argmin
form.

**SIZE.** 2 × ~35 lines.

**SOURCE.** `EFF.W12.86` step 5 (verbatim, incl. the `[W12-H]` fence); CHAP-B H-10 (the
inheritance clause, verbatim: "an HT transcription at `d ≥ 2` inherits `B-BOX-1` through
B.55/B.58").

**TEETH.** DROP-L (1,136) → retained; §13 fires a depth-2 chain at each prime.

**ENVIRONMENT.** ENV-C3.

---

### NODE C.114 [theorem] [fresh] — **TERMINAL SUPPLY: THE COUNT LAW**

> ⚠ **[BLOCKED: A-C.2, 2026-08-16 — the two count axioms are WITHDRAWN from the leanspec
> bank; the node awaits the realizes-refinement re-sign (A-C.3 target).]** As frozen, BOTH
> `ht_branch` and `ht_global` are machine-refuted
> (`leanfinal/Uniformity/ChapC/C111_C114_REFUTATION.lean.txt`): the stratum reads NONE of
> `kappa`, `kappa0`, `s`, the non-root `sideType`s, nor the child-completeness of the
> tree, while the formulas read all of them — one-node κ-separated trees (and the empty
> shape at `κ₀`) give equinumerous strata with formula values `1` vs `2`. The A-C.1
> signature note below had already BOOKED "the per-node residual-type/side-tag
> refinements" to the fleet; the A-C.2 audit shows the booking is SIGNATURE-critical, not
> proof-side. The A-C.2 record carries the designed clause list for the re-sign (per-node
> `HTNode.WF`; per-node cell membership `G i ∈ htCell π (K i) (node i)`, subsuming the
> polygon pins and pinning the types; the `s`-pin
> `gaussVal (K i − K (t.parent i)) = (s_i : ℕ∞)`; sibling distinctness on a side;
> child-count = the side type's repeated-linear count; the `(HT-orbit)` κ-rule at tree
> level). `htRealizes`' polygon pin clause is separately re-signed NOW to the hull form
> (C.108's D3 fix, mechanical), so downstream re-signs build on the faithful carrier. The
> withdrawn signatures are preserved verbatim in the refutation record (`C114BranchFrozen`,
> `C114GlobalFrozen`). Downstream consumers of the supply (chapter H's entry-law audits,
> chapter I's count-side conditionality, §13's gates on `ht_branch`) inherit the BLOCK.

**STATEMENT.** *`(HT-branch)` and `(HT-global)` — the all-degree order-1 count law
(= THEOREM W-12.A's effective statement).* Iterating C.112 over the finite tree
(C.113(i)):

```
(HT-branch)   H_i(T,N) = (∏_{v∈T_i} κ_v ∏_S S_{λ_{v,S}}(Q_i)) · Q_i^{Σ_v B_v(N) − Σ_{v≠root} D_v(N)};
(HT-global)   #T(N) = κ₀(T) · C₀(q) · ∏_{i: m_i=1} q^{d_i(N−1)} · ∏_{i: m_i≥2} H_i(T,N)
```

— per window-visible decided order-1 shape `T`, at explicit `N`, as exact `Finset.card`
identities over `Coeff O n N`. Supplied to: chapter H's entry-law audits (CHAP-B H-10's
routing — "counting level-`N` cells is chapters C/H's object … together with
`LEMMA W12-HT`"), chapter I's count-side conditionality, and this chapter's §13 gates.

**SIGNATURE** [signed: A-C.1 — elaborated in `leanspec/Leanspec/ChapC.lean`; split → 2. The
realization stratum is carried by the NEW `htRealizes` predicate (cluster factors `G` and
recentered keys `K` per node: monic, degree `m_v·deg K_i`, exact `Pceil` pins, child
clusters dividing parents, keys same-degree recenterings); the per-node residual-type/
side-tag REFINEMENTS of the stratum are BOOKED as the fleet's realizes-refinement (they
ride `htCell`, whose clauses the root already carries in `ht_branch`). `ht_global`'s branch
instances (`IsDomain`/UFD/`Finite` on each `resField (Φb i)`) enter as explicit argument
functions — all derivable from `hkeys`.]
```lean
namespace Uniformity.Density.Tower

def htRealizes (Φ f : Polynomial O) (t : HTTree) : Prop :=   -- [re-signed: A-C.2, pin → hull form]
  ∃ (G K : ℕ → Polynomial O), K 0 = Φ ∧ G 0 = f ∧
    ∀ i, i < t.nodes.length →
      (G i).Monic ∧
      (G i).natDegree = (t.nodes.getD i HTNode.default0).m * (K i).natDegree ∧
      (∀ j, j ≤ (t.nodes.getD i HTNode.default0).m →
        ((t.nodes.getD i HTNode.default0).Pceil j : ℕ∞) ≤ npHgt (K i) (G i) j) ∧
      (∀ j, j ≤ (t.nodes.getD i HTNode.default0).m →
        (t.nodes.getD i HTNode.default0).IsVertex j →
        npHgt (K i) (G i) j = ((t.nodes.getD i HTNode.default0).Pceil j : ℕ∞)) ∧
      (0 < i → G i ∣ G (t.parent i) ∧
        (K i).natDegree = (K (t.parent i)).natDegree ∧
        (K i - K (t.parent i)).natDegree < (K i).natDegree)

-- [A-C.2] `theorem ht_branch` / `theorem ht_global` WITHDRAWN — machine-refuted as frozen
-- (`C111_C114_REFUTATION.lean.txt`); re-sign pending the realizes-refinement (A-C.3).
-- The withdrawn binder lists are preserved verbatim in the refutation record.
```

**DEPENDS.** C.107–C.113.

**PROOF.** telescope over the tree (every non-root occurs once as a child — `−D_v` once;
every node contributes `B_v`, censuses, `κ_v` once); level 0 by the branch-independence
(B.48's coprime dissection at level 0) + the assignment count.

**SIZE.** 2 × ~30 lines.

**SOURCE.** `EFF.W12.83` (the displays, verbatim); `.86` step 6; `.87` ("W-12.A regains
full order-1 coverage: its controlling formula is (HT-global) … the former display is the
depth-zero specialization").

**TEETH.** the N1 certificate (1,196 per-key comparisons, 0 mismatches) → **executable
regression** retained; GC-11 extra-force gates at §13 (C.116's disposition).

**ENVIRONMENT.** ENV-C3.

---

### NODE C.115 [lemma] [fresh]

**STATEMENT.** *Specializations and the obstruction instance (consumer compatibility as
theorems).* (i) The dated-obstruction instance: for `H = (1)` then `SPLITEQ(2)`:
`B_root = D_child = 2N − 5`, root census `S_{(1²)}(q) = q − 1`, leaf census
`(q−1)(q−2)/2`, leaf exponent `2N − 8`, so `(HT-branch)` gives
`(q−1)·((q−1)(q−2)/2)·q^{2N−8}` — exactly W12-L0's count. (ii) W12-L0's recovery shape:
at multiplicity two `κ_v = 1` and the exponents telescope (the `(q−1)^t` factor).
(iii) The depth-zero specialization (no non-root `D_v`, no internal orbit) is the former
W-12.A display. Each as a computable instance lemma (`decide`/`norm_num`-grade at fixed
small parameters, plus the symbolic telescope at (ii)).

**SIGNATURE** [signed: A-C.1 at the depth-zero clause (`ht_depth_zero`, the (iii)
specialization over the formula carrier); the (i)/(ii) spot VALUES are §13's executed
`htSpot`/`htSpotAlt` rows (the stub gate's D15 block — see C.123/C.124's A-C.1 tables), and
their tree-level instantiations are the fleet's companions — recorded].
**[AUDITED: A-C.2 — NO re-sign.** Predicted clean and verified: `ht_depth_zero` is a
formula-level identity over `htBranchCount` (both sides read the same node fields), true
for ARBITRARY `v` — no set-level content, so the free-field disease cannot reach it. Its
tree-level instantiations inherit C.114's BLOCK, but the depth-zero clause itself stands.]
```lean
namespace Uniformity.Density.Tower

theorem ht_depth_zero (Q : ℕ) (census : FactorizationType → ℕ) (v : HTNode) (N : ℕ) :
    htBranchCount Q census ⟨[v], fun _ => 0⟩ N
      = v.kappa * (∏ p ∈ v.sides, census (v.sideType p.1 p.2)) * Q ^ v.B N
```

**DEPENDS.** C.107 · C.114.

**PROOF.** arithmetic + the displayed audits.

**SIZE.** 26 lines.

**SOURCE.** `EFF.W12.87` (the consumer sweep, verbatim rows: the discharge instance,
W-12.A restoration, W12-L0/L1 recovery, the cubic consumers).

**TEETH.** the audited `2N−5`/`2N−8` values → **Lean theorem** + §13 rows at `q = 2` AND
`q = 3`.

**ENVIRONMENT.** ENV-C3/C5.

---

### NODE C.116 [lemma] [fresh] — **the §11 disposition + Phase-B consumer spec**

**STATEMENT.** *The thin-verification disposition and the transcription contract.*
Documentation node: (i) the machine certificate is CORROBORATION, not the warrant ("the
proof above supplies the all-degree warrant"), on grid `n ∈ {3,4}, q ∈ {2,3}, N ≤ 6`,
NO hostile-arc pass (`EFF.W12.87` OPEN-CALL 6) — the Lean proofs of C.109–C.114 are the
first warrant-grade check beyond that grid, and §13's gates re-fire the certificate's
spot values at both primes (GC-11 extra force); (ii) the Phase-B consumer contract,
verbatim: a history-resolved order-1 menu entry "must implement (HT-rec), retaining
complete child-history multisets, side tags, `D_v`, `κ_v`, and `κ₀`" — transcribed as
the `#check`-manifest of C.108's fields so no downstream menu drops a tag; (iii) the
boxes that DO NOT MOVE: `[W12-H]`, W12-BOX-1's inputs `(H-a)–(H-e)`, W-12.B, the tail
problems — unchanged, chapter I's rows; (iv) the provenance note (`EFF.W12.88`): the law
was N1-conjectured → machine-certified → P1-composed → orchestrator-verified — carried
in the docstring as the audit trail.

**SIGNATURE** [signed: A-C.1]. documentation node — landed as the `C116Manifest` `#check`
section in `leanspec/Leanspec/ChapC.lean` (the `HTNode` field manifest with the MANDATORY-tag
comments on `kappa`/`sideType`, per the Phase-B consumer contract).
**[UPDATED: A-C.2** — the manifest gains `#check @HTNode.WF` (well-formedness is now
MANDATORY on every count law) and loses `#check @ht_branch`/`@ht_global` (WITHDRAWN at
C.114's block; the lines are replaced by the withdrawal comment).]

**DEPENDS.** C.108 · C.114.

**PROOF.** mechanical. **SIZE.** 16 lines.

**SOURCE.** `EFF.W12.87`/.88 (verbatim); PA-5 (the assignment + its trap clause).

**TEETH.** the four DROP-teeth at exact kill counts (302/22/370/1,136) → retained as
regressions.

**ENVIRONMENT.** ENV-C1.

---

---

## 12. §12 — LEVEL-`N` TOWER CERTIFICATES

> **Design note.** B §9 one level up, same architecture (D-4 global via GC-9): visibility
> API separate from residual-read API (GC-1's closing rule), hypotheses on ONE
> representative transported via landed `decidedAt_of_congr`, per-member at explicit `N`,
> existence-of-certifying-`N` as its own node, NO uniform-`N` law anywhere. The
> conditionality of a tower certificate is exactly §7's (C-BOX-1 where `f₁d_r ≥ 2`; the
> cites where the read consumes them) — a certificate node never adds conditionality of
> its own.

### NODE C.117 [def] [fresh]

**STATEMENT.** *Level-2 window visibility.* `Visible₂ L Ψ f N : Prop` — every height the
level-2 read consults is `< ` the cleared window bound: all level-1 slot digits feeding
`dv2Pin L Ψ f j` for `j ≤ deg f / D″`, and every residual-read height, sit at cleared
`dv`-value `< (F.e₁ * L.ℓ) * N`-scale (the B.75 pattern at the `dv₂`-ladder; correctly
pinned at abscissa 0 per GC-1's visibility rule — visibility bounds EVERY consulted
height, so the abscissa-0 pin is the right one HERE and only here).

**SIGNATURE** [signed: A-C.1 — elaborated in `leanspec/Leanspec/ChapC.lean`].
```lean
namespace Uniformity.Density.Tower

def Visible₂ {F : KeyFrame O π} {H₀ hpin} (L : LevelDatum F H₀ hpin)
    (Ψ f : Polynomial O) (N : ℕ) : Prop :=
  ∀ j, j ≤ f.natDegree / L.keyDeg₂ → dv2Pin L Ψ f j ≠ ⊤ →
    dv2Pin L Ψ f j < (((F.e₁ * L.ℓ) * N : ℕ) : ℕ∞)

theorem Visible₂_mono {F : KeyFrame O π} {H₀ hpin} (L : LevelDatum F H₀ hpin)
    (Ψ f : Polynomial O) {N N' : ℕ} (h : N ≤ N') :
    Visible₂ L Ψ f N → Visible₂ L Ψ f N'
```

**DEPENDS.** C.11 · C.21 · B.75 (template + the GC-1 visibility/residual split).

**PROOF.** definitional. **SIZE.** 18 lines.

**SOURCE.** B.75 (D-4's visibility layer); `EFF.GENTOW1.39`/C.58(e) (the window content
identity that makes visibility the right gate).

**TEETH.** §13 rows. **ENVIRONMENT.** ENV-C3.

---

### NODE C.118 [lemma] [fresh]

**STATEMENT.** *Visible reads are window functions.* If `proj O n N a = proj O n N a'`
(same window class) and the level-2 read of `a`'s member is `Visible₂`, then the two
members' level-2 heights, side sets, and residual polynomials agree at every consulted
datum (`dv2Pin`-congruence, `dv2SideSet`-congruence, `dv2ResPoly`-congruence) — stated
convention-free (`consulted height < bound` only, B.77's pattern) so any consumer serves.

**SIGNATURE** [signed: A-C.1 — elaborated in `leanspec/Leanspec/ChapC.lean`; B.77's own
split executed: `dv2_read_congr` (heights) + `dv2_read_congr_res` (residuals)].
```lean
namespace Uniformity.Density.Tower

theorem dv2_read_congr {F : KeyFrame O π} {H₀ hpin} (L : LevelDatum F H₀ hpin)
    (hπ : Irreducible π) [Finite (ResidueField O)]
    {Ψ : Polynomial O} {n N : ℕ} {a a' : Fin n → O}
    (hc : proj O n N a = proj O n N a')
    (hvis : Visible₂ L Ψ (monicPoly a) N) {j : ℕ} (hj : j ≤ n / L.keyDeg₂) :
    dv2Pin L Ψ (monicPoly a) j = dv2Pin L Ψ (monicPoly a') j

theorem dv2_read_congr_res {F : KeyFrame O π} {H₀ hpin} (L : LevelDatum F H₀ hpin)
    (hπ : Irreducible π) [Finite (ResidueField O)]
    {Ψ : Polynomial O} {n N : ℕ} {a a' : Fin n → O}
    (hc : proj O n N a = proj O n N a')
    (hvis : Visible₂ L Ψ (monicPoly a) N)
    {u₂ ℓ₂ : ℕ} (hℓ₂ : 0 < ℓ₂) (hseam : ℓ₂ * L.seam < u₂)
    (hne : (dv2SideSet L Ψ (monicPoly a) u₂ ℓ₂).Nonempty)
    (hne' : (dv2SideSet L Ψ (monicPoly a') u₂ ℓ₂).Nonempty) :
    dv2ResPoly L Ψ (monicPoly a) u₂ ℓ₂ hne = dv2ResPoly L Ψ (monicPoly a') u₂ ℓ₂ hne'
```

**DEPENDS.** C.11 · C.25 · C.117 · B.77 (template) · landed `proj`, `dev_congr` (B.10).

**PROOF (route).** B.77's route at the `dv₂`-carrier: window-equal members have
`dev`-digit-equal developments below the bound; every consulted read factors through
those digits.

**SIZE.** 36 lines.

**SOURCE.** B.77 (the level-1 twin); C.58(e) (the content identity).

**TEETH.** the HE6R1 battery's members-of-identical-outer-data design (perturbations
strictly above the λ-line — `EFF.HE6R1.18`) → retained.

**ENVIRONMENT.** ENV-C3.

---

### NODE C.119 [theorem] [fresh]

**STATEMENT.** *The tower certificate kernel.* Let `a` be a representative whose member
`f` satisfies, VISIBLY at window `N` (C.117): the §5 standing pair, a level datum `L`
with `¬ Ψ ∣ f_S`-visible data, and a SEPARABLE above-seam level-2 residual profile. Then
`typeOf` of every lift's corresponding block is pinned: the composed dictionary values
`(e₁ℓ·ℓ₂, f₁d_r·deg r₂)` per level-2 factor — for EVERY lift of the window class
(C.118's congruence + §7's reads; conditional exactly on `C-BOX-1`'s iterate where
`f₁d_r ≥ 2` and on the §9/§10 cites where the read consumes them, each named in the
hypothesis list).

**SIGNATURE** [signed: A-C.1 — elaborated in `leanspec/Leanspec/ChapC.lean`; B.79's shape
at the composed read — the representative's visible data transported to EVERY lift of its
window class, the composed dictionary firing per lift with the boxes inside the
conditional; full binder list at the leanspec twin, its carriers = C.117/C.38a/C.49's].
```lean
namespace Uniformity.Density.Tower

theorem tower_cert_kernel … :
    ∀ b : Fin (μ₂ * T.D₂) → O, proj O (μ₂ * T.D₂) N b = proj O (μ₂ * T.D₂) N a →
      ∃ g : Polynomial O, g.Monic ∧ g ∣ monicPoly b ∧
        g.natDegree = (F.e₁ * T.e₂ * ℓ₃) * (F.f₁ * T.f₂ * r₂.natDegree) ∧
        ((∀ g' ∈ monicFactors g, CBox1Side (T.levelDatum hπ) g') →
         (∀ g' ∈ monicFactors g, (F.f₁ * T.f₂ * r₂.natDegree) ∣ inertiaDegOf g') →
          typeOf g = ⟨{(F.e₁ * T.e₂ * ℓ₃, F.f₁ * T.f₂ * r₂.natDegree)}⟩ ∧ Irreducible g)
```

**DEPENDS.** C.37 · C.61/C.62 · C.117 · C.118 · B.79 (template).

**PROOF (route).** transport the representative's visible data to every lift (C.118);
fire §7 on the transported data.

**SIZE.** 40 lines.

**SOURCE.** B.79 (the level-1 twin, D-4(b)'s representative discipline); `EFF.HE6R1.30`
(the leg's own summary: the level-2 read decides against PARI on 677/682 with zero
mis-decisions — the corpus form of this kernel).

**TEETH.** the 677/682-zero-misdecision census → **executable regression** retained; §13
fires two members.

**ENVIRONMENT.** ENV-C3.

---

### NODE C.120 [theorem] [fresh]

**STATEMENT.** *The tower `DecidedAt` certificate.* Under C.119's hypotheses plus the
complete-σ assembly (all blocks of the member's dissection certified — the §5 dissection
enumerates them), the window class is DECIDED: `DecidedAt O n N c σ` for the assembled
σ (through GC-4's dictionary — the σ value assembled by `typeOf_mul` over the dissection),
via landed `decidedAt_of_congr`. B.82's pattern at composed reads; fires with zero
adaptation from the `N3Cert*` leancheck idiom per D-4(b)'s precedent.

**SIGNATURE** [signed: A-C.1 — elaborated in `leanspec/Leanspec/ChapC.lean`; the assembled
σ is the member's own `typeOf` (honest: decided AT the member's value), the certificate
hypotheses = visibility + all-above-seam-separable + the box per factor].
```lean
namespace Uniformity.Density.Tower

theorem tower_decidedAt {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀}
    (T : TowerDatum F H₀ hpin) (hπ : Irreducible π) (hh : 1 ≤ F.h)
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [Finite (ResidueField O)]
    {μ₂ N : ℕ} {a : Fin (μ₂ * T.D₂) → O}
    (hmem : monicPoly a ∈ towerLocus T μ₂) (hsq : Squarefree (monicPoly a))
    (hvis : Visible₂ (T.levelDatum hπ) (composedKey T) (monicPoly a) N)
    (hsep : ∀ (u₃ ℓ₃ : ℕ), 0 < ℓ₃ → Nat.Coprime u₃ ℓ₃ → ℓ₃ * T.E₂ < u₃ →
      ∀ hne : (dv2SideSet (T.levelDatum hπ) (composedKey T) (monicPoly a) u₃ ℓ₃).Nonempty,
        (dv2ResPoly (T.levelDatum hπ) (composedKey T) (monicPoly a) u₃ ℓ₃ hne).Separable)
    (hbox : ∀ g' ∈ monicFactors (monicPoly a), CBox1Side (T.levelDatum hπ) g') :
    DecidedAt O (μ₂ * T.D₂) (typeOf (monicPoly a)) N (proj O (μ₂ * T.D₂) N a)
```

**DEPENDS.** C.33/C.34 · C.119 · B.82 (template) · landed `DecidedAt`,
`decidedAt_of_congr`, `typeOf_mul`.

**PROOF.** assemble per block; transport.

**SIZE.** 34 lines.

**SOURCE.** B.82; `EFF.HE6R1.25` (the σ census this certifies member-wise).

**TEETH.** §13's decided members at both primes.

**ENVIRONMENT.** ENV-C3.

---

### NODE C.121 [lemma] [fresh]

**STATEMENT.** *Existence of a certifying `N`, per member.* For a fixed member `f`
satisfying §5's standing pair with a decided tower read (separable above-seam residuals
after finitely many peels/refines — C.113's termination), there EXISTS `N` at which
C.120's hypotheses are visible — read off the member's OWN polygon data (its maximal
consulted height + 1). Per-member only; NO family-uniform `N` (GC-9.3: the `R8-1`
refutation stands — the B.81 pattern verbatim).

**SIGNATURE** [signed: A-C.1 — elaborated in `leanspec/Leanspec/ChapC.lean`; per-member
ONLY, GC-9.3].
```lean
namespace Uniformity.Density.Tower

theorem exists_certifying_N {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀}
    (T : TowerDatum F H₀ hpin) (hπ : Irreducible π) (hh : 1 ≤ F.h)
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [Finite (ResidueField O)]
    {μ₂ : ℕ} {f : Polynomial O} (hmem : f ∈ towerLocus T μ₂) (hsq : Squarefree f) :
    ∃ N : ℕ, Visible₂ (T.levelDatum hπ) (composedKey T) f N
```

**DEPENDS.** C.113 · C.117 · C.120 · B.81 (template).

**PROOF.** the consulted-height set is finite; take its max.

**SIZE.** 22 lines.

**SOURCE.** B.81; GC-9.3.

**TEETH.** signed non-applicable (existence; the numeric leg is per-member at §13).

**ENVIRONMENT.** ENV-C3.

---

### NODE C.122 [lemma] [fresh]

**STATEMENT.** *The degenerate-stratum path (the certificate meets the peel).* If the
member's visible data show `Ψ ∣ f` (the 12-member BADTOTAL stratum), the certificate
routes through C.40's peel: one `(e₁ℓ, f₁d_r)` factor certified outright, the read
continuing on the peeled complement at `mult₂ − 1` — decidedness of the class follows
from the peeled member's certificate (one recursion step, C.113(i)-bounded). The
FINDING-HE6R1-F2 repair as a certificate-layer theorem.

**SIGNATURE** [signed: A-C.1 — elaborated in `leanspec/Leanspec/ChapC.lean`; the peeled
`(e₁e₂, f₁f₂)` entry lands as a multiset-sum `typeOf` identity].
```lean
namespace Uniformity.Density.Tower

theorem tower_cert_peel_path {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀}
    (T : TowerDatum F H₀ hpin) (hπ : Irreducible π) (hh : 1 ≤ F.h)
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [Finite (ResidueField O)]
    {μ₂ N : ℕ} {a : Fin (μ₂ * T.D₂) → O}
    (hmem : monicPoly a ∈ towerLocus T μ₂)
    (hctx : BlockContext (T.levelDatum hπ) (monicPoly a))
    (hvis : Visible₂ (T.levelDatum hπ) (composedKey T) (monicPoly a) N)
    (hdvd : composedKey T ∣ monicPoly a)
    (hbox : CBox1Side (T.levelDatum hπ) (composedKey T)) :
    typeOf (monicPoly a)
      = ⟨{(F.e₁ * T.e₂, F.f₁ * T.f₂)}
          + (typeOf ((monicPoly a) /ₘ composedKey T)).data⟩
```

**DEPENDS.** C.36(i) (the `Ψ ∣ f_S ↔ Ψ ∣ f` check on visible data) · C.40 · C.119/C.120.

**PROOF.** case split on the visible divisibility; peel; recurse once.

**SIZE.** 24 lines.

**SOURCE.** `EFF.HE6R1.14`/.16 (the stratum + the 12/12-decided, 5/5-PARI supplementary
leg — the corpus form of this path).

**TEETH.** the supplementary leg → retained; §13 fires one degenerate member.

**ENVIRONMENT.** ENV-C3.

---

## 13. §13 — GATES (GC-11: `q = 2` AND `q = 3`, WILD `e₁ ≥ 2`, `e > 1 ∧ f > 1`, EXECUTED AT STUB STAGE)

> **Gate discipline.** All four gates are leancheck-idiom concrete instances (`#eval` +
> `decide`-grade theorem blocks), EXECUTED at the leanspec stub stage per GC-6.6(c) BEFORE
> any fleet agent fires on §§7–12; retained regressions live under `verification/`
> (GC-8). Every §-audit value named in §§3–12's TEETH rows re-fires in exactly one gate.
> The coincidence-regime discipline (C-H12) is explicit: each gate names which of its
> rows would be blind at the other prime and why.

### NODE C.123 [gate] [fresh]

**STATEMENT.** *The `q = 2` gate.* Over `O = ℤ₂`-class data: the S2 tower witness values
(C.97: `u₂ = 5, u₃ = 21`, ladder `[4,10,21]`, `n̂₂(21) = 16Φ′`); FAM-A5/A7/B budget-table
rows (C.52's floors — sixteen recomputed entries), node floors `[21,11]/[29,15]/[13,7]`,
`E₂`-vs-`dv₂(x^{D₂})` splits `10/14/6 > 8/8/4`; refine row A5-R1 (`p₀ = 2λ = 26`, the
`q = 2` vanishing of the `j = 1` pin — the char-split's `q = 2` half); FAM-B BAND-2/3
window rows; the `(1,2)`-genre bite (`EFF.HE6.20`(3): live at `q = 2`,
σ `{(2,2),(2,2)}`); FR5X (the C.96 negative control: attainment FAILS at `m = 4, p = 2`);
HT spot values at `q = 2` (`(q−1)((q−1)(q−2)/2)q^{2N−8}` at `q = 2` = 0 — the degenerate
census, itself a check); a depth-3 `(SLOT₃)` spot value on the S4 chain.

**SIGNATURE** [signed: A-C.1 — the D14 cure: the expected values now exist in MACHINE FORM
as named tables in `leanspec/Leanspec/ChapC.lean`'s gate-hygiene block, `#guard`-diffed
against the computed values (all passing)]. `theorem gateC_q2 : <conjunction of decidable
instances> := by decide/norm_num` + the `#eval` block (GC-6.6(c)); the fleet's gate file
diffs against THE TABLES, not prose:
```lean
def gateC_q2_budget_w0 : List ℕ := [7, 5, 3, 1]
def gateC_q2_budget_w5 : List ℕ := [5, 3, 1, 0]
def gateC_q2_nodeFloors : List (List ℕ) := [[21, 11], [29, 15], [13, 7]]
def gateC_q2_E2_splits : List (ℕ × ℕ) := [(10, 8), (14, 8), (6, 4)]
def gateC_q2_s2Ladder : List ℕ := [4, 10, 21]
def gateC_q2_htSpot : ℕ := 0    -- the degenerate census at q = 2, every N
```
**D22 cure (the `w = 0` identical-row trap):** the two gate frames' `w = 0` budget rows
COINCIDE (`[7,5,3,1]` at both primes — C-H12); the gate hygiene block adds the
DISCRIMINATING THIRD FRAME `(e₁, e₂, E₂) = (2, 1, 10)` with `w = 0` row `[16, 11, 6, 1]`
(`gateC_frame3_budget_w0`, `#guard`-verified ≠ the shared row) — every budget-table gate
row set must include it.

**DEPENDS.** the §§3–12 nodes whose TEETH name it. **PROOF.** computation.
**SIZE.** ~60 lines. **SOURCE.** the per-node TEETH rows. **TEETH.** IS the teeth.
**ENVIRONMENT.** ENV-C3, concrete `O`-instances (the leancheck `ℤ₂`-idiom).

---

### NODE C.124 [gate] [fresh]

**STATEMENT.** *The `q = 3` gate.* Over `O = ℤ₃`/`ℤ₅`-class data: the `(2,2,3)` twist
witness (C.22's MANDATORY row: `q(3) = 1`, `twistRead = 2η` in `F₉`, the `[r1]` `+q`
reading refuted); the HE6R1 frame (`D″ = 4, T₂ = 2λ, μ₂ = 2`, `K₂ = F₉`), one decided
member + one degenerate member (C.122's path, σ `{(2,2),(2,2)}`); FAM-D rows (x-free
witness, budget floors `[13,7]`, D-R1/D-R2 refine rows — BOTH pins present at `q = 3`,
the char-split's other half); BP3 (the C.96 negative control: attainment WITH
`p ∣ binom(3,2)` via the other slot); the letter-live GENTOW2 frame (C.101's twisted
prescription vs the `q = 2` letter-dead twin — the ψ vs ψ^{(w)} divergence EXHIBITED);
HT spot values at `q = 3` (the obstruction instance `2·1/2·q^{2N−8}`-family values).

**⚠ D15 RESOLVED [signed: A-C.1] — the two HT spot readings AGREE, decided against the
source.** `EFF.W12.87`'s own finding-1 record re-derives the `H = (1) → SPLITEQ(2)` count as
**`(q−1)·((q−1)(q−2)/2)·q^{2N−8}`** (W12-L0's `(q−1)^t` history prefactor included), so
C.123's family display is the source's FULL coefficient, and this node's `2·1/2` is the
MIDDLE factor `(q−1)(q−2)/2` evaluated at `q = 3` — the two readings agree:
`htSpot 3 6 = 2·3⁴ = 162` is THE expected value (`gateC_q3_htSpot_atN6`), and the
factor-`q−1`-smaller `htSpotAlt` is DEAD (kept `#guard`-ed as the negative control). Both
vanish at `q = 2`; the `q = 3` row is the deciding witness, exactly as the gate discipline
predicted.

**SIGNATURE** [signed: A-C.1 — machine-form tables in the leanspec gate-hygiene block]:
```lean
def gateC_q3_budget_w0 : List ℕ := [7, 5, 3, 1]
def gateC_q3_budget_w5 : List ℕ := [6, 4, 2, 0]
def gateC_q3_htSpot_atN6 : ℕ := 2 * 3 ^ 4   -- D15 DECIDED: the full-coefficient reading
```
**PROOF/etc.** as C.123 (incl. the D22 third frame).

---

### NODE C.125 [gate] [fresh]

**STATEMENT** *[REWRITTEN at A-C.1 — the D16 cure: the committed field was a live
composition-time transcript, not a statement; its honest content is preserved below and the
transcript is retired to the A-C.1 record].* *The wild witness gate (GC-11's shape clause),
fired as the HONEST TRIPLE:*
**(a) [unconditional wild row, `e > 1, f = 1`]** at a genuinely wild frame (`p ∣ e₁`: the
`q = 2` frame `(e₁,f₁,h) = (2,1,1)`, `Φ′ = x² − 2` over `ℤ₂`; the `q = 3` row at an
`e₁ = 3` frame, `Φ′ = x³ − 3` class, via the C.59 ramified leg — the `x² − 3` frame is
TAME at `p = 3` and is NOT a wild witness): the Tier-1 read gives `typeOf = ⟨{(e₁ℓ, 1)}⟩`
with `e₁ℓ > 1`, UNCONDITIONALLY (`f₁·d_r = 1` sits in `C-BOX-1`'s vacuity perimeter,
C.60(i)) — e.g. `ℓ = 2` at `f₁ = d_r = 1`: `{(4,1)}`, the `EFF.HE6.20` `(2,1)`-genre σ.
**(b) [the `e > 1 ∧ f > 1` row, CONDITIONAL]** the `{(2, 2)}` read at witness (i)'s frame
with a quadratic label (`f₁·d_r = 2`), fired via C.61 + C.119/C.120 at an explicit member
and window **with `C-BOX-1` as an explicit named hypothesis**, instantiated by the
PARI-certified battery regression (the corpus's 677/682) — never silently.
**(c) [the finding]** an unconditional-in-Lean `e > 1 ∧ f > 1` tower witness is exactly
`C-BOX-1`-gated: `e = e₁ℓ > 1` is unconditional (C.59), while `f = f₁d_r > 1` forces
`f₁d_r ≥ 2`, which is precisely `C-BOX-1`'s non-vacuous perimeter — at level ≥ 2 the
two-sided witness is conditional, UNLIKE B's level-1 D-3 row. (Cross-read item 6; A-6's
booking. The original in-field derivation transcript — including its two wrong turns — is
preserved in the git history at the pre-A-C.1 revision, per the record-not-rewrite
discipline for FINDINGS; what a fleet agent needs is the triple above.)

**SIGNATURE** [signed: A-C.1]. As C.123 (machine-form rows in the leanspec gate-hygiene
block; the `(2,2,3)` twist witness and the wild-frame slot rows are the executed
`#guard`s of the stub gate's numeric section); the (b)-row's conditional firing uses
`C-BOX-1` as an explicit named hypothesis instantiated by the battery regression (never
silently). **PROOF/etc.** as C.123.

---

### NODE C.126 [gate] [fresh]

**STATEMENT.** *The axiom census gate.* Per terminal theorem of §§7–12: `#print axioms`
= Lean core (`propext`, `Classical.choice`, `Quot.sound`) PLUS exactly the declared
gate-(b) axioms where and only where declared: `fgmn_calculus_exists` on
§10-theorems/C.90/C.91/C.67-chain, the [cite:AGNPRW] axiom on C.94's consumers, and
NOTHING else; the AxChk-pattern diffable output committed (the
`lean/LeanUrat/AxChk_baseline.lean` idiom at the ChapC roll-up; a footprint regression is
stop-the-line per the repo rule).

**SIGNATURE** [signed: A-C.1]. the AxChk file + its committed output. **The expected
gate-(b) census, updated to the A-C.1-declared names:** the declared cited axioms are
exactly **`fgmn_residual_mul`** (C.66), **`fgmn_calculus_exists`** (C.92) and
**`agnprw_termination`** (C.94) — `fgmn_residual_mul` on C.67's chain (→ C.69/C.80),
`fgmn_calculus_exists` on the §10 theorems and C.90/C.91's `[FGMNCalculus]` consumers,
`agnprw_termination` on C.94's consumers (I.01's discharge) — plus Lean core, and NOTHING
else on any §§7–12 terminal.

**DEPENDS.** all terminal nodes. **PROOF.** mechanical. **SIZE.** ~40 lines.
**SOURCE.** repo axiom policy; Part V gate (b). **TEETH.** IS the census.
**ENVIRONMENT.** —.

---

---

## 14. §14 — DAG ADDITIONS

Emitted at `spec/DAG_BLUEPRINT_C.tsv` (771 rows, mechanically extracted from this file's
SOURCE and DEPENDS fields; regenerate with the §14 extraction described here — the node
list is the headings, per `dag_build.py`'s contract):

* **574 `proof-dep` rows** — the intra-chapter DEPENDS edges (469 `C → C`) plus the
  cross-chapter consumption edges to committed blueprint nodes (`BP.B.*` per GC-13(b);
  `BP.H.51`–`BP.H.58` ONLY, per GC-5/H-14 — mechanically verified: no other `H.*` appears
  in any DEPENDS field).
* **197 `stmt-dep` rows** — the SOURCE transcription edges. Per GC-12: `W12` and `GENTOW5`
  rows are emitted against the SHARD-LOCAL IDs that exist in `DAG_NODES.tsv` at HEAD
  (`EFF.W12.s2of2.NN = EFF.W12.(NN+52)`, `EFF.GENTOW5.s2of2.NN = EFF.GENTOW5.(NN+43)`),
  with the contiguous ID carried in the `evidence` column — remap mechanical at the
  orchestrator's re-harvest. **`GENTOW2` rows are emitted against the contiguous IDs and
  currently DANGLE** — GENTOW2 has ZERO rows in the HEAD harvest (it is the manifest-gap
  recovery, PA-3(i)); the evidence column says so per row, and the re-harvest lands them.
  Booked as an orchestrator item with PA-3(ii)'s re-run.
* **Graph shape** (intra-chapter, computed AFTER the A-7 SCC repair — Tarjan +
  Kahn, both 0 back-edges, and the same confirmed by direct cycle detection over the
  emitted TSV): **127 nodes, 469 edges, ACYCLIC, critical path 17 (18 layers)**, layer
  widths `8, 3, 6, 12, 6, 9, 5, 8, 5, 5, 4, 10, 9, 11, 10, 8, 5, 3` — 8 nodes fireable
  immediately. The chapter is SPINE-SHAPED (unlike H's wide layer 0): the §3→§4→§5 frame
  is serial, and the schedule risks are the three heavy nodes **C.27** ((SLOT₂)
  exactness), **C.33** (the slope dissection), and **C.88** ((SLOT_i) up the tower) plus
  the §7 sandwich chain they feed. Fleet guidance: claim C.33 and C.27's splits first;
  §§10–11 fan out early (C.97/C.98/C.107/C.108 sit in low layers).
* **⚠ Checker gap (for the next orchestrator pass):** the official `spec/dag_check.py`
  does NOT read `DAG_BLUEPRINT_*.tsv` files — per-chapter TSV acyclicity currently needs
  a DIRECT check (chapter D's checker run caught this chapter's original SCCs exactly
  because it ran one). Extend `dag_check.py` to sweep the blueprint TSVs, or every
  chapter's acyclicity claim rests on its own composer's script.
* **COARSE-edge refinement:** the 42-edge governing-unit placeholder
  `EFF.GENTOW5.s1of2.06` (BRIEF C trap (vi)) is re-homed unit-by-unit by §9's SOURCE
  fields (the real consumers of GENTOW5's units are C.83–C.96); the dangling
  `GENHN ← GENTOW` discharge arcs (items (1)–(5) "unlanded" in every GENTOW note's
  scope-B) are LANDED by C.52–C.58/C.72–C.81/C.55 — the cross-read re-homes those
  reverse-XREF rows against this chapter's nodes.

---

## 15. §15 — LEANSPEC STUB LIST (stage 0e)

* File `leanspec/Leanspec/ChapC.lean`, everything wrapped in `namespace LeanspecC`
  (GC-6.6; the ChapG retire-to-examples route is the recorded alternative — pick one and
  say which in the stub header).
* Gate order GC-6.6(a)–(d): (a) elaborate the fragile signatures FIRST — the flagged
  fragile set: C.01 (`KeyFrame`'s `hresirr` dependent-type plumbing), C.03/C.12 (the
  `AdjoinRoot` iterates + instance chain — GC-7's depth-≥ 3 fallback triggers HERE if
  anywhere), C.09 (`LevelDatum` over pin data), C.83 (`DeepTower`'s `Fin r`-indexed
  fields), C.92/C.66 (the `FGMNCalculus` structure — its fields must elaborate against
  C.25's carriers), C.21 (`slotRes`'s `digAt` composite); (b) land the `def` bodies real
  (26 def + 7 def+lemma + 1 def+theorem nodes); (c) EXECUTE the §13 gate blocks at
  `q = 2` AND `q = 3` (C.123–C.125's `#eval` values against this file's displayed
  numbers); (d) only then sign the `axiom` stubs for the theorem nodes.
* Stub-order constraints the fleet must respect (forward refs recorded in-node):
  C.21 → C.13; C.29/C.33/C.34 → C.27; C.60/C.61 → C.40; C.61/C.62 → C.49; C.85 → C.56
  (general-μ₂ leg); C.97–C.100 → C.89(i); C.89 → C.90/C.91's `n ≥ 3` legs; C.66's
  SIGN-OFF → after C.97/C.98 elaborate.
* RE-PLAN bookings for the orchestrator (shared helpers promised by node ⚠s):
  `dvResPoly_mul_of_pure` (B.35's twin — C.34/C.37/C.70); the `dv2ResPoly` +
  `dv2SideSet` cluster (C.38a — C.38/C.55/C.64/C.65); `complementConst`/`γg`/`pinHeight`
  (C.36/C.39); the `stageLiftO` GenreDatum packaging (C.14/C.43 — merge into ONE helper);
  `ComposedLabel` (C.62 — chapter E may request it by name).
* The three `cite` nodes (C.66, C.92, C.94) land as STATEMENTS ONLY at stub stage;
  their axioms are not declared until Asvin signs (Part V gate (b)) — a stub build that
  needs them before sign-off uses `variable`-hypothesis form, never a provisional axiom.

---

## 16. §16 — TEETH DISPOSITIONS; FLAGGED FOR THE CODEX CROSS-READ

### 16.1 Teeth disposition summary (GC-8 vocabulary; per-battery, aggregated)

| battery (source) | rows | disposition |
|---|---|---|
| HE6R1 sealed battery (944 members, σ census, P2/P3/P4/P5, 5 teeth) | `EFF.HE6R1.23`–`.29` | **Lean theorem** for P2's law (C.27), the peel σ (C.40/C.61), the dictionary audits (C.04/C.10/C.12); **executable regressions retained** for the census/teeth (677/682, T-CRACK, T-BASIS, T-TWIST0, T-NAIVEHE6A, T-WITHHOLD); §13 re-fires the frame values |
| HETOW battery + supp + 2026-08-10 leg | `EFF.HETOW.32`–`.40`, `.52` | **Lean theorem** for HETOW-1(c)/2/3 content (C.46–C.49); regressions retained (300/300 μ₂=3, P5 level-3 exclusion, W(t) checks); the `f₁ ≥ 2` carry leg's PROOF-ONLY corpus status is DISCHARGED by C.47's uniform proof (recorded, cross-read item 7) |
| GENTOW1 battery (NEC 350, ROUNDTRIP 150, WINDOW 35, STRINGS 22, REFINE 40, 5+ teeth) | `EFF.GENTOW1.10`–`.12`, `.42`–`.45` | **Lean theorem** for (a)–(e)/(i)–(iv) at their TERMINAL forms (C.52–C.58); regressions retained incl. T-MUTFLOOR, T-REFWRONG ×8, T-UNDERCUT ×2, T-BELOWNODE; the budget tables' 16 recomputed entries → §13 |
| GENTOW3 battery (FLOOR 274, SHARP 11, XFREE, LABEL 6) + RUN B + E13/X1 searches | `EFF.GENTOW3.34`–`.37`, `.55`, `.61` | **Lean theorem** for (i)/(ii)/(iii)/3.C (C.72/C.73/C.75); (iv) at its three TERMINAL layers (C.74); regressions retained; ENTRY 274's `disclosed non-independence` carried verbatim; the S8.4 activation disclosure carried at C.74(c) |
| GENTOW4 battery (117 members, P-1..P-6, T-2 NOCG 49, T-3 SIBDROP, T-5 WRONGKEY) + FR-M/FR-3B | `EFF.GENTOW4.08`, `.31`, `.41`–`.48` | **Lean theorem** for 4.1/4.A/4.2/4.C (C.76–C.81); FAM-P5's mixed-tie EMPIRICAL rows retained as the regression guarding C.67's cite; PE2-P values → §13 |
| GENTOW5 battery (A-rows, B-rows, FA1-LIFT 22, direction-check 8) | `EFF.GENTOW5.34`–`.37`, `.54` | **Lean theorem** for A0/A1/A/C/D/B-clauses at TERMINAL scope (C.85–C.91); the `i ≥ 3` machine gap DISCLOSED and partially closed by §13's added depth-3 spot row (GC-11 extra force); `[GENTOW5-W(i)]` = **signed open hypothesis** (C.89 — no teeth can discharge it) |
| GENTOW6 battery + r1 cap leg (303/0) + SUB-BOX leg (459/0, 265/0) | `EFF.GENTOW6.14`, `.22`, `.33`–`.35` | **Lean theorem** for 6.1 (cite-conditional, C.67), 6.2-budget (C.82), 6.3-pinned/6.4 (C.95), 6.5-IF (C.96); BP3/FR5X negative controls → §13; the boxes-note 0/2 grade residue discharged by the Lean proof at the IF direction |
| GENTOW2 battery + PE4 decode + PE5/PE6 fresh routes + LP1 | `EFF.GENTOW2.60`–`.67`, `.45` | **Lean theorem** for B/B′/B″/A over `[FGMNCalculus]` (C.99–C.103); PE4's LD2 REFUTATION row retained (guards the DEAD per-height form); the w-measurement retained (guards the DISCLOSURE); LP1 retained (guards the letter conflation) |
| W12-HT N1 certificate (1,196 comparisons, 4 DROP-teeth, 300+322 rank tests) | `EFF.W12.87`/.88 | **Lean theorem** for steps 1–6 + HT-branch/global (C.109–C.114) — the FIRST warrant-grade check beyond the thin grid; certificate retained as regression; §13 re-fires spot values at both primes |
| signed non-applicability | — | definitional nodes (C.01–C.13 class), interface identities (C.05), manifests (C.93/C.106/C.116), the named open hypotheses (C-BOX-1 at C.60, `[GENTOW5-W(i)]` at C.89 — their "teeth" are the batteries above, retained as evidence-of-truth-in-fact, never as discharge) |

**Sanity check (GC-8 rider (iii)):** the signed-vacuity/open rows reconcile against
Display A's conjunct list — this chapter's opens are exactly: `C-BOX-1` (feeds B's
`B-BOX-1`-family conditionality, already a capstone conjunct through B), `𝒲_{≤n}` =
`(H-VARTHETA-RES)/[GENTOW5-W(i)]` (a named Display-A conjunct, supplied to I via C.89),
the three gate-(b) cites (FGMN ×2, AGNPRW — capstone-visible through `#print axioms`,
C.126), and `[W12-H]`/`GENTOW4-BOX-2`-class boxes explicitly left with chapter I. No
other C node carries conditionality — matching H.09's "the fields with no teeth are
exactly the capstone's conditionality".

### 16.2 Flagged for the codex cross-read

1. **C-H3's immunity claim** (no base change, no fractional-height ELEMENT below degree
   `D″` anywhere in §5/§7) — attack it; note A-1's wording repair below.
2. **DECISION C-D1's Tier-1 recast** (root count → factor degree; orbit → factor) —
   attack faithfulness against `EFF.HE6.18` + `EFF.HE6R1.16`; C.29's FAITHFULNESS note
   and C.40's are the target texts.
3. **TERMINAL-form discipline (C-H8)** — verify no superseded display leaked into any
   node: the checklist is §§5–11's SOURCE chains (R2a/b/c, S8.1/S8.4, TOWERRAT2-C, m-A/
   m-i/m-ii, `.39`/`.47`, S11.1/S11.2/S11.3/S11.5/S12.1/S12.2 + the ω-corrigendum,
   PE2-F-2's codomain, R3-1..4).
4. **The `HYP.121` non-inheritance claim** (§11: fracture permanence discharged by
   factorization uniqueness) — verify the factor-level recast really needs no GENIND-1
   content.
5. **The `FGMNCalculus` packaging** (§10 design note + C.92): is the structure-plus-one-
   axiom form faithful to gate (b)'s intent, and is the field list COMPLETE for every §10
   proof (walk C.99/C.100/C.101/C.103's cited names)?
6. **C.125's composition-time finding:** at level ≥ 2 the unconditional `e > 1 ∧ f > 1`
   witness is `C-BOX-1`-gated (unlike B's level-1 D-3 row) — check the reasoning and
   whether a genuinely unconditional two-sided tower witness exists that this chapter
   missed.
7. **C.47's uniform-`f₁` proof** discharging what the corpus could only prove-only
   (HETOW-BOX-3's `f₁ ≥ 2` carry leg) — verify the (LIFT)-form really closes it at every
   `f₁`.
8. **C.86's level-1 rider as a real theorem** (the corpus display claims nothing on
   frozen text; the Lean statement is a new theorem) — confirm this is an honest
   strengthening, not a scope leak into GENHN-BOX-2's bookkeeping (which stays chapter
   I's).
9. **The ϑ-orientation hygiene**: every ϑ-adjacent statement (C.85(A1), C.89, C.99,
   C.100(3), C.101) is in ratio/normalizer form with the D-table cited — grep for any
   bare-ϑ sign convention that slipped through.
10. **The §14 extraction** — spot-check DEPENDS-to-TSV fidelity and the shard-local
    remaps (three W12/GENTOW5 rows at random).

---

## A-§ DELTA BLOCK (dated records against this file's own committed skeleton — the
CHAP-B A-§ precedent; the index/honesty text above is NOT edited)

**A-1 (C-H3 wording repair, owed since §5's composition).** C-H3 says "the §5/§7 route
needs no test key at a fractional height". IMPRECISE as written: §3/§5 DO construct test
keys (C.13/C.14 — `O[x]`-algebra via H.54's lifts) and use them throughout (`Ψ ∣ f_S`
etc.). The honest immunity claim, superseding that sentence's reading: **no ELEMENT of
degree `< D″` at a fractional `dv`-height is ever needed (the enlarged family fixes
HE3-BOX-6 BY DEGREE — `EFF.HE6.14`'s own framing), and no base change is performed
anywhere.** Cross-read item 1 attacks the repaired form.

**A-2 (kind census, mechanical count over this file's `### NODE` headings).** §2's
planned census read ≈30 def / ≈62 lemma / ≈22 theorem / 2 cite / 4 gate. ACTUAL:
**26 def · 39 lemma · 46 theorem · 7 def+lemma · 1 def+theorem · 3 cite · 4 gate =
126 nodes** (total exactly as planned; the kind split moved lemma→theorem mass, and the
FGMN import split into two cites C.66/C.92 plus C.94). §2 is index, not contract, on
kinds.

**A-3 (§7 supply naming).** §2's supply table names C.61 (Tier 1), C.64 (Tier 2), C.66
(Tier 3). As composed, Tier 1's assembled law is the PAIR C.61 + C.63, and **C.69 is the
bundled supply statement consumers should cite first**; C.66's Tier-3 content fires
through C.67. The §2 pointers remain correct (they name the tiers' kernels).

**A-4 (§8/§9 section-content relocation).** The GENTOW6 caps/attainment cluster
(6.3/6.3′/6.4/6.5) planned for §8 landed in §9 (C.95/C.96) — §8's header was renamed
accordingly; the index row for §9's content gloss should be read to include "the caps".

**A-5 (split-mandate table, aggregated for the fleet).** Split-mandated:
C.24 → 2, C.27 → 3, C.33 → 3, C.34 → 2, C.49 → 3, C.52 → 3, C.53 → 1(+companion),
C.56 → 2, C.57 → 2, C.58 → 3, C.74 → 3, C.76 → 2, C.77 → 2, C.78 → 2, C.85 → 3,
C.88 → 2, C.90 → 2, C.91 → 3, C.95 → 2, C.110 → 2, C.111 → 2, C.113 → 2, C.114 → 2.
Split candidates flagged in-node: C.14, C.37, C.54, C.59, C.67, C.99, C.118. Fleet
planning figure: **≈ 165 Lean files.**

**A-6 (composition-time finding at C.125).** Recorded as cross-read item 6: the GC-11
`e > 1 ∧ f > 1` witness at tower level is `C-BOX-1`-conditional; the gate fires the
honest triple ((a) unconditional `e > 1, f = 1` wild row; (b) conditional `{(2,2)}` row
with the battery regression instantiating the hypothesis; (c) the finding itself).

**A-7 (SCC repair, 2026-08-15 — post-completion defect, found by chapter D's checker run
and confirmed by direct cycle detection over `spec/DAG_BLUEPRINT_C.tsv`; §14's original
"ACYCLIC" claim was WRONG, produced by a buggy composer-side layering script whose
memoization masked back-edges).** Two non-trivial SCCs existed and are adjudicated per
edge:

* **SCC 1 = {C.56, C.84, C.85, C.87}** (loops `C.56 → C.85 → C.56` and
  `C.56 → C.85 → C.87 → C.84 → C.56`). Two defective edges, two dispositions:
  * `C.85 → C.56` — **(a) a wrong DEPENDS entry**: "C.56 (the statement it supplies)"
    was a SUPPLIES annotation misfiled in the DEPENDS field. Removed from DEPENDS; now a
    separate **SUPPLIES** paragraph on C.85 (which the extraction correctly ignores).
  * `C.84 → C.56` — **(c) a real structural defect**: C.84's flavor-lift reconciliation
    genuinely depends on the `k2DigitLift` DEF, which lived as a companion inside the
    theorem node C.56 (whose general-`μ₂` leg depends on C.85 → C.87 → C.84). Broken by
    the mandated-split pattern: **new micro-node C.56a [def]** carries `k2DigitLift`
    (the `.62` TERMINAL display, verbatim, with its own SOURCE/TEETH); C.56 and C.84 both
    depend on C.56a. Node count 126 → **127**; A-2's census gains one `def` (27 def
    total); A-5's fleet figure ≈165 → **≈166**.
* **SCC 2 = {C.99, C.100, C.102, C.104}** (loop `C.99 → C.100 → C.104 → C.102 → C.99`;
  the coordinator's minimal back-edge report named `C.102 → C.99`, which is REAL and
  KEPT — the γ-calculus companion). One defective edge:
  * `C.104 → C.102` — **(a)/(b) a citation, not a dependency**: the ψ₂-discipline's
    "equal up to the letter twist" clause is a statement gloss about the two carriers,
    not a def/proof input to them. Removed from DEPENDS (the gloss stays in C.104's
    STATEMENT, which the extraction does not read).

**Verification after repair** (both directions, committed with this amendment): Tarjan
SCC + Kahn topological sort over the DEPENDS graph AND direct cycle detection over the
regenerated `spec/DAG_BLUEPRINT_C.tsv` — **0 non-trivial SCCs, 0 back-edges, 127/127
nodes topologically sorted**; the three reported back-edges (`C.85→C.56`, `C.84→C.56`,
`C.102→C.99`-closing via `C.104→C.102`) are absent/re-pointed (`C.84 → C.56a` present).
Corrected graph shape in §14 (critical path 17, 18 layers). **Checker gap recorded in
§14**: `spec/dag_check.py` does not read `DAG_BLUEPRINT_*.tsv` — per-chapter acyclicity
currently needs the direct check; flagged for the next orchestrator pass to extend the
checker. Cross-read item 10 now also covers this repair's three edited DEPENDS fields.

---

---

<!-- RESUME: CHAPTER COMPLETE + A-7 SCC repair applied (127 nodes incl. C.56a; spec/DAG_BLUEPRINT_C.tsv 771 rows, verified acyclic by Tarjan+Kahn AND direct TSV check, 0 back-edges), TEETH summary + cross-read flags + A-§ deltas landed. CODEX CROSS-READ OWED (§16.2's ten items). Orchestrator items: PA-3(ii) re-harvest (GENTOW2 rows dangle by design); GC-13 placeholder resolution vs chapters D/E at freeze (HE7 units, ϑ-TABLE anchor, (ABS-HE4)); gate-(b) sign-offs for C.66/C.92/C.94; the RE-PLAN helper bookings in §15. -->


**A-C.1 (2026-08-16, the SIGNATURE-COMPLETION amendment set — the stub gate's D1/D2 cure).**
The stub gate of 2026-08-16 (`leanspec/Leanspec/ChapC.lean`, defect list D1–D25) found 70 of
127 nodes without a Lean signature and 19 more with ellipses inside the Lean text. This
amendment set completes and signs them; every touched node carries a per-node
`[signed: A-C.1]` tag, and every signed signature has an ELABORATED twin in
`leanspec/Leanspec/ChapC.lean`'s A-C.1 layer (`lake build Leanspec.ChapC` green at each
increment — a signature that does not elaborate is not signed). Itemized record, grown per
increment:

* **A-C.1(a) — D21 (stop-the-line).** `C.31`'s `jump_drop` re-signed: `hL` (FALSE as signed,
  168 counterexamples) → `hjump : 2 ≤ ℓ * dr`, verified against `EFF.HE6R1.10`'s own display;
  refutation record preserved verbatim in the leanspec numeric section. See the node's D21
  block.
* **A-C.1(b) — D19/D20 (the carrier bridge).** New node **C.14a** (`KeyFrame.genreDatum` +
  `stageLiftIA` + the `rfl` reconciliation + `stageCoord`/`stageLiftO`): H §8 is reachable
  from chapter C's carrier exactly on the corpus perimeter (`1 ≤ h`, `2 ≤ e₁f₁`), as explicit
  hypotheses; H's landed side untouched; the `μ`-dummy recorded. `C.14` re-signed with
  `(hh : 1 ≤ F.h)` (its D20 case gap closed by exclusion of the for-C.05-only degenerate
  frame). Node count 127 → **128**; census: +1 def.
* **A-C.1(c) — D4 adoption.** `KeyFrame.Pin` (the named pin proposition) is hereby a
  blueprint declaration (C.14a's block); new signatures below bind `(hpin : F.Pin H₀)`.
* **A-C.1(d) — the fragile five signed (§15 gate order (a), now satisfiable).** `C.83`
  (`DeepTower`, on GC-7's recorded depth-≥ 3 fallback — DECISION block at the node: abstract
  `K_i` with `RingEquiv` iterate witnesses; `towerNorm`/`towerShift`/`towerCocycle` as
  exponent bookkeeping; `trunc` added), `C.92` (`FGMNCalculus`, one field per consumed
  published clause + the `fgmn_calculus_exists` axiom; TWO booked residual fields recorded
  at the node — C.90(b)'s Cor 6.3 leg and C.102's letter reads), `C.97` (the S2 witness as
  axiom-constants with signed value clauses; `ℤ₂`-class carried by
  `Irreducible (2 : O)` + `residueCard O = 2`), `C.98` (`shear_onesided_iff`,
  ENV-C5-abstract over `ℕ → ℕ∞` with the new `hSupp`/`hOnSide` carriers), `C.66` (the stub
  gate's `fgmn_residual_mul` draft ADOPTED as the exact statement; drafting flags carried;
  the D23 top-down numbering trap closed by an inline pointer at the SOURCE paragraph).
  C.92/C.66 remain **statement-UNINSPECTED** under append #66's category signature — the
  owner's per-statement inspection is queued in CHAP-I's gate-(b) addendum.
* **A-C.1(e) — §5 signed (C.33–C.40 + the C.38a cluster; D2's worst block cured).**
  Determinations, each recorded at its node: C.33's witness type = B.42's landed template at
  the `dv`-carrier as `structure DvDissection` + existence/uniqueness; C.34 signed at the
  consumed `(λ, r)`-block clause with the dependent pin plumbing ∀-quantified; C.35's
  `blockFactor` = TOTAL maximal-labelled-divisor (choice, junk `1`), context as the named
  Prop `BlockContext`, spec companion carries the D13 multiplicity tie; C.36's `c_g` =
  `(dvSupp …).toNat` (the STATEMENT's `L.ℓ •` prefix a recorded clearing slip); NEW node
  **C.38a** (`dv2SideSet`/`dv2ResPoly` cluster — the §15 RE-PLAN executed; `dv2Res A` :=
  `A`'s `dvResPoly` at the letter `β`); C.38's radical clause as
  same-monic-irreducible-divisors; C.39's `γg`/`pinHeight` landed as displayed; C.40 signed
  with `BlockContext` + the D11 one-field constructor. Node count 128 → **129** (C.38a);
  census: +1 def.
* **A-C.1(f) — C.94's EXACT LEAN STATEMENT (D24 broken, C side).** `DescentState`/
  `DescentStep` (jump via §5's carriers: labelled block, `ℓd_r ≥ 2`, degree ≥ 2·D″, test-key
  key; α-refine as same-degree recentering with STRICT attained-slope increase) +
  `NS7TerminationStatement` (no infinite history on a fixed monic squarefree `f`) +
  the declared `agnprw_termination` axiom at the A-3-corrected cite (**[AGNPRW] Thm 5.6**,
  Found. Comput. Math. 25 (2025) no. 2, 631–681). Statement-UNINSPECTED under append #66;
  queued with the others. CHAP-I's `I.01` can now be typed against
  `NS7TerminationStatement` (recorded in CHAP-I's addendum).
* **A-C.1(g) — §6 tail + §7 signed (C.43–C.58, C.61–C.70).** Determinations at the nodes:
  C.43 through C.14a's `stageLiftO` (D19 executed); C.44's `towerLabel` in the explicit
  `η^{−Qf₂}ψ₂(η^QZ)` form, `levelDatum` gains `hπ`; C.45 stub-carried as an axiom constant;
  C.46/C.47/C.48/C.52–C.54/C.56–C.58 and the composed dictionary gain `(hh : 1 ≤ F.h)` (the
  C.14a perimeter); **C.51's residual exponent corrected `e₂f₂μ₂/e₂ → μ₂`** (a caught
  C-H12-class degree/exponent slip, determination at the node); C.56/C.57's slope letter is
  `lam` in Lean (`λ` reserved); C.57's `DOM_N`/`COD_N` land as `refineDom`/`refineCod`;
  C.58 signed at the consumed core (BAND 1 + consultation), clauses (b)/(d)/(e) booked;
  C.61's `hm1` resolved as the exact-residual hypothesis (no reshaping of C.29); C.62's
  `ComposedLabel` structure landed (E's expected RE-PLAN pre-honored); C.63's per-`r` boxes
  written out; C.64 as argmin-data equality; C.65 at the span form (summed form booked);
  C.67 with the exact-power multiplicity pair and the `[cite:FGMN]`-footprint note; C.69 as
  the Prop-structure bundle `ClassSizeSupplyData` + `classSize_supply` (stub-stage choice
  exercised); C.70 at the per-side core. **C.82's DEPENDS names "C.89 (§9's 𝒯-free cap)" —
  the cap lemma is C.95; recorded as a DEPENDS-field slip (the 6.2C(d) supplier is C.95).**
* **A-C.1(h) — §10 signed (C.99–C.106).** Over the interface at the CONCRETE depth-2 chain
  (`TowerDatum.deepTower`, an axiom-constant carrier + data clauses) with the bridge
  `ρ : fld 2 ≃+* AdjoinRoot T.ψ₂` explicit; every ϑ-adjacent statement in NORMALIZER-RATIO
  form (`FGMNCalculus.thetaRatio`; no orientation committed — GC-14's D-table cited);
  `chainNorm` realizes `n̂` from `towerNorm`; `repoRead := dv2Res` (C.104 determination);
  B′'s direction `FGMN = u·repo` preserved; the refuted `u(β_t) = 1` form isolated in the
  `gentow2_Bp_unit_iff` companion; `recipe3` the shared R3-3 display; **C.102's exponent
  read `ℓ₁ = e₂` FLAGGED for the cross-read** (verify against `EFF.GENTOW2.37`); C.106 as
  the `#check` manifest.
* **A-C.1(i) — §11 + §12 signed (C.107–C.122).** §11 on the INDEX-ENCODED tree carrier
  (`HTNode` with CEILED pin data, `Finset` sides + `sideType`, `κ_v` as a data field;
  `HTTree` = list + parent function, `WF` acyclicity) with the count formulas as arithmetic
  defs (`htBranchCount`/`htGlobalCount`) and the strata via `htCell`/`htRealizes`;
  `residualTypeOf`/`sideCensus` over `CommRing`+UFD binders (no `Field` diamond at
  `resField`); C.110 split into the conservative-cell count + the translate-residual iff;
  C.111 signed at the arithmetic shadow (exponent nonnegativity; the multiplication-
  bijection engine = the booked B.37–B.40 weighted RE-PLAN); C.112 in division-free
  telescope form; C.113's `B-BOX-1` inheritance as the inner hypothesis; C.114's
  `ht_branch`/`ht_global` tie the strata to the formulas (the realizes-refinement booked);
  C.115 at the depth-zero clause (spot values = §13's executed `htSpot` rows); C.116 as the
  `#check` manifest with the MANDATORY-tag comments. §12: `Visible₂`(+mono), the B.77 split
  congruences, the kernel/`DecidedAt`/existence/peel-path certificates — per-member at
  explicit `N` throughout (GC-9.3).
* **A-C.1(k) — §8 + §9 signed (C.71–C.82, C.84–C.96).** §8: `shadowDev` gets a REAL body
  (the `(O[x]/Φ′)[Z]`-division tower via `biRead`/`devQ` + the canonical
  `AdjoinRoot.modByMonicHom` back-map); `TouchCert` as the exact-`Θ_j` discrepancy of
  `Φ₂^{μ₂}`'s own reads; the three C.74 terminal layers incl. the S8.4 two-witness claim
  and no more; C.76's frame-opening hypothesis `hopen` made explicit; C.79's five rows as
  the `Mu2TwoCase` tag; C.82 at the budget half with the C.95-not-C.89 DEPENDS correction.
  §9: `towerWeight`/`flavorMonomial` real, `towerLift` an axiom-constant stub; **C.85's A0
  DROPPED per its own DECISION note** (A1 in multiplicativity-defect form; Step A the
  binomial-free ring identity); C.87 forward-only (no two-directional statement); C.88 in
  norm form + `boundRec`; C.89's `GENTOW5W`/`Wle` in the ratio carrier with (iii) OPEN by
  construction; C.90 at clause (a) (clause (b) = the booked Cor 6.3 residual); **C.91
  signed at (d)+(e), (c) BOOKED** (needs the level-(i+1) `dv`-carrier — the third booked
  §9-scope residual, with C.90(b) and C.102's letter reads); C.93/C.95/C.96 as displayed.
* **A-C.1(m) — the gate's stub-side cures ADOPTED into the signed half (the D3–D18
  alignment), ordering and census.** The committed signature blocks now carry the cures as
  their text, each tagged in place: D4 (`(hpin : _)` → `(hpin : F.Pin H₀)` at all ~9 sites —
  `KeyFrame.Pin` adopted per A-C.1(c)); D3 (`C.08`'s `{u ℓ}` bound); D5 (`C.07`'s
  `dvSideMax`/`dvSideDeg`/`dvSideLen` DECLARED, `dvSideLen := max − min` the determination);
  D6 (`C.15`'s total computable `slotIdx` body; `noncomputable` dropped); D8 (`C.21`'s
  two-step `algebraMap` composite written out); D9 (`C.22`'s two `letI`s + the `isKey_X`
  helper adopted as a blueprint declaration); D10 (`C.27`'s `.get!` → `.toNat`); D11
  (`C.40`/`C.61`'s one-field constructors — in their A-C.1 blocks); D18 (`noncomputable` on
  `C.03.stageCard`, `C.09.keyDeg₂`/`seam`). **D12 (ordering, binding on the fleet's
  roll-up):** landed order is C.01 → C.04, **C.06 → C.07 → C.05** (i), … C.21 →
  **C.13 → C.14/C.14a** (ii, the blueprint's own ⚠), C.25 → C.26 → **C.29 → C.27** (iii,
  the §5 → §4 crossing) → C.28 — as executed in `leanspec/Leanspec/ChapC.lean`. **D7:**
  C.15/C.16/C.17/C.41 re-tagged ENV-C5 → ENV-C1 in place (riders at the nodes; the
  arithmetic content lives in the numeric-gate mirrors). **D13:** disposed at C.35's
  `blockFactor_spec` (the multiplicity tie is its clause). **Census (supersedes A-2/A-7's
  counts):** nodes 127 → **129** (+C.14a, +C.38a); kind deltas: +2 def-cluster nodes; the
  three gate-(b) cites now carry DECLARED axioms (`fgmn_residual_mul`,
  `fgmn_calculus_exists`, `agnprw_termination` — C.126's census expects exactly these).
  **§15's gate order (a)–(d) is now SATISFIABLE** (the five named fragile signatures exist
  and are elaborated); the four BOOKED residuals (C.90(b)'s Cor 6.3 clause, C.91(c)'s
  entry characterization, C.102's letter-read field, C.58's (b)/(d)/(e) companions) are the
  A-C.1 → fleet handoff list, each recorded at its node.
* **A-C.1(l) — the depth-2 SCOPE FENCE self-catch (stop-the-line class, caught in-flight).**
  The first drafts of C.99's `gentow2_Bpp`/`theta_letter_valued` were quantified over
  arbitrary chain depth `r` — which would have SILENTLY ASSERTED the open `[GENTOW5-W(i)]`
  (the very C-H8-class strengthening this chapter polices). Caught during C.89's signing;
  both carry `(hr : r = 2)` with the fence comment in-statement. Recorded because the trap
  shape (interface generality outrunning the proved scope) is exactly what a fleet agent
  re-hits.
* **A-C.1(j) — GATE HYGIENE (D14/D15/D16/D22 cured).** D14: C.123/C.124 now carry
  MACHINE-FORM expected-value tables (named defs, `#guard`-diffed, all passing). D15:
  **RESOLVED against `EFF.W12.87`** — its finding-1 record re-derives the count as
  `(q−1)·((q−1)(q−2)/2)·q^{2N−8}` (the `(q−1)^t` history prefactor included), so the two
  gate texts AGREE (`2·1/2` is the middle factor at `q = 3`); `htSpot` is the reading,
  `htSpotAlt` is DEAD (kept as the `#guard`ed negative control); expected value
  `htSpot 3 6 = 162`. D16: C.125's STATEMENT rewritten from the composition transcript into
  the honest triple (the unconditional wild `e>1,f=1` row; the `C-BOX-1`-conditional
  `{(2,2)}` row with the battery regression named; the finding) — transcript preserved in
  git history. D22: the discriminating THIRD frame `(e₁,e₂,E₂) = (2,1,10)` added (`w = 0`
  row `[16,11,6,1]` ≠ the shared `[7,5,3,1]`, `#guard`-verified). C.126's expected census
  updated to the three declared A-C.1 names.

**A-C.2 (2026-08-16, the C.109 defect-repair unit — the A-F.12/A-H.5 pattern: source
adjudication first, refutations preserved, nothing weakened). THE HT COUNT LAYER'S NODE
DATUM WAS FREE WHERE THE CORPUS DETERMINES IT; FOUR REPAIRS, ONE NEW NODE, TWO
WITHDRAWALS.**

**(I) The findings.** The wave refutation
(`leanfinal/Uniformity/ChapC/C109_REFUTATION.lean.txt`, sorry-free, Lean-core) proved the
frozen C.109 contradictory: `htCell` reads `(m, Pceil, sides, sideType)` while the count
law's RHS reads `L` through `B_v`, so nodes differing only in `L` have `rfl`-equal counted
subtypes and different RHS. Its secondary arithmetic — with `sides = ∅` the true count
`Q^{N−3}(Q−1)` is a `Q`-power for NO `L` once `Q ≥ 3` — is now VERIFIED (mutation M2 of the
certification; at `Q = 2` exactly `L = 1` matches, also as the record said). This unit's
audit found TWO further defects in the same A-C.1 transcription event: **(D3)** `htCell`'s
pin clause `npHgt Φ f j = Pceil j` at EVERY `j ≤ m` contradicts the corpus's own three-way
membership law — the frozen cell is strictly smaller than the corpus cell at every
non-vertex position, and the C.115(i) obstruction instance itself (a length-2 side, char
2) makes the frozen cell EMPTY where the law demands `(q−1)q^B` (mutation M3); **(D4)**
the frozen C.111 and BOTH frozen C.114 axioms are contradictory
(`C111_C114_REFUTATION.lean.txt`: `c111_frozen_false`, `c114_branch_frozen_false`,
`c114_global_frozen_false` — the tree data ties `s` to nothing; the strata read none of
`kappa`/`kappa0`/`s`/non-root types/child-completeness).

**(II) Source adjudication (verbatim pins; each with a non-textual leg per the
extraction-corruption rule).** The well-formedness the source's own count law carries:

1. `EFF.W12.83` (the setting display): *"Define `B_v(N)=m_vN−∑_{j<m_v}⌈P_v(j)⌉−L_v`,
   `L_v=#{j<m_v:P_v(j)∈ℤ}`"* — **`L_v` is DEFINED in the same display that defines `B_v`**;
   it was never free data. And the census product is *"`∏_{S⊂P_v}S_{λ_{v,S}}(Q_i)`"* — the
   sides range over the sides OF THE POLYGON. Non-textual leg: `EFF.W12.24`'s own
   cross-check row re-derives W-10's `(2,1,1)` law with `P(0)=1, P(1)=1/2`, `L=1`,
   `B=2N−3` — `L` counts integral positions only, arithmetic confirmed, and confirmed
   again by this unit's exact counts.
2. `EFF.W12.23` (the membership law): *"`j` a VERTEX of `P`: `v(a_j)=P(j)` exactly and
   `digit_{P(j)}(a_j)≠0`; `j` an on-side lattice point (side `S`): `v(a_j)≥P(j)`, with
   `digit_{P(j)}(a_j)` = the residual coefficient `r_j` (**possibly zero**; priced jointly
   by `λ_S`); every other `j<m`: `P(j)∉ℤ` … `v(a_j)≥⌈P(j)⌉` — the automatic ceiling."*
   Equality at VERTICES ONLY. (Chapter B's landed B.16 already quotes this display
   verbatim in its Faithfulness block — the law was in the repo's own trusted base.)
   Also: *"the branch polygon is the lower hull of `{(j,v(a_j))}_{j<m} ∪ {(m,0)}`"* — the
   monic-top clause. Non-textual leg: the char-2 double-root and char-3 `(Y−1)(Y−2)`
   instances (M3) — the exact-pin reading is EMPTY there while the law's value is
   attained by the three-way reading.
3. `EFF.W12.24` (the count + normalization): *"slot `j` contributes `N−⌈P(j)⌉` free
   digits, minus one priced digit if `j` is a lattice point on the polygon (`L` of
   them)"*, and the sweep: *"Choosing its residual = a monic degree-`g_S` polynomial with
   nonzero constant term of type `λ_S` (`S_{λ_S}(q^d)` ways) … Each next side to the left
   … again exactly `S_{λ_S}(q^d)` choices … `S_T(q^d)=∏_S S_{λ_S}(q^d)` — no extra unit
   factors."* This fixes the census semantics (= C.107's `sideCensus`, exactly) and the
   degree law (each side's type has the side's residual degree). Non-textual leg: the
   shared-vertex instance I6 (`Pceil=(3,1,0)`, two sides): count `Q^{2N−6}(Q−1)²`, no
   extra unit factor — exact.
4. `EFF.W12.85` (for C.111): *"`#U_v(𝐑)=Q^{B_v(N)−∑_uD_u(N)}`. In particular, the
   exponent is a nonnegative integer"* — nonnegativity is PER NODE and BY THE BIJECTION
   (at realized nodes), never a property of raw tree data. Non-textual leg: the
   WF-resistant numeric counterexample ([C111] leg).

**Verdict:** the source's condition = node-datum coherence (monic top; `Pceil` the ceiled
hull of its own points; the `L` law; the sides law; the degree law) + the three-way cell
membership. The ℚ-free chord-test encoding is licensed by the reconstruction lemma (the
hull of the ceiled points IS the polygon: ceilings raise non-vertex points by `< 1`, fix
vertices, and a convex minorant through the vertices is the hull) — certified [ENC] on
every instance against direct rational hull geometry.

**(III) The re-signs, with the alternatives rejected.**

* **C.108** — `HTNode.WF` (five clauses, displayed at the node) + the chord-test reads
  (`OnHull`/`IsVertex`/`NodeOnSide`/`nodeSideSet`/`IsSide`/`nodeSideDeg` — B.16/B.20's
  shapes at the node's own data, GC-2 literal-reuse style); `htCell` pin → `≥` everywhere
  + `=` at `IsVertex`. Rejected: *(a) all-vertex WF keeping the exact-pin cell* — kills
  every polygon with a side of length `≥ 2` or denominator `≥ 2`, including C.115(i)'s
  own obstruction instance; *(b) exact pins with a corrected RHS* — an ad-hoc law the
  corpus never states, and the `(HT-rec)` recursion is stated for polygon cells; *(c) a
  positivity clause `Pceil j ≥ 1` for `j < m`* (true of corpus tree nodes via
  `f̄ = P̄^m`) — NOT needed for the law's truth (the flat-side instance I5 is exact), and
  adding it would narrow C.109 with no gain; recorded as a deliberate strengthening of
  scope, certified.
* **C.109** — gains `(hwf : v.WF)` inline (B.42: truth-bearing hypotheses in binder
  lists, never section auto-inclusion); everything else byte-identical. Rejected:
  *unbundled per-clause hypotheses* — five binders on every consumer for one semantic
  unit; the predicate is the corpus's "a node datum" made explicit.
* **C.109a** [NEW node] — see (IV).
* **C.111** — the per-node inequality becomes the hypothesis `hnode` (the corpus's
  fiber-count shadow, discharged by the fleet's bijection at realized nodes); conclusion
  unchanged (the telescope over the parent map); `hvis` dropped as dead weight (A-F.12's
  minimality rule). Rejected: *(a) WF-only* — numerically refuted (the WF-resistant
  instance); *(b) realization-scoping* — inverts the §11 dependency order and imports
  C.114's unfinished stratum into an arithmetic node.
* **C.114** — `htRealizes` pin → hull form (the D3 fix, mechanical); `ht_branch` and
  `ht_global` WITHDRAWN (a refutable axiom is a live inconsistency in the spec bank);
  node BLOCKED pending A-C.3 with the designed clause list recorded (node banner).
  Rejected: *(a) signing the fully refined stratum now* — the refinement (histories, κ's
  factorial rule at tree level, sibling matching) is exactly the complexity class whose
  uncertified signing produced this defect family; it needs its own certification leg
  (the A-C.1 lesson); *(b) WF-binders-only re-sign* — still refutable via `kappa`
  (machine-checked), so it would land another false axiom.

**(IV) DECISION D-C.2-BRIDGE — the secondary gap becomes NODE C.109a, not an annex.** The
refutation record named C.109's real cost: the level-`N` development ↔ coefficient-box
bridge `Coeff O (m·d) N ≃ (Fin m → Coeff O d N)` through `dev` (well defined by B.10),
absent from `leanfinal`. Decision: a NEW node (C.109a, `dev_box_bridge`, signed `∃`-form
with the componentwise spec through `dev` at an arbitrary lift — a single Prop axiom
stub, no data axiom). Rationale: it has ≥ 3 consumers (C.109's slot count, C.110's
`ht_conservative_card` block decomposition, C.114's strata), independent B-layer
character (`EFF.W12.23`'s own "monic division … is a bijection" display), and annexing it
to C.109 would hide a shared dependency from the DAG. Rejected: *annex to C.109* (hides
the sharing), *landing it in chapter B* (its carrier `Coeff` is §11's counting frame, and
chapter B is committed/landed — the GC-5 supplier fence).

**(V) Consumer audit (predict-then-verify; grep over blueprint + leanspec).**
`HTNode`/`htCell`/`htBranchCount` consumers are exactly C.108–C.116 (+ C.116's manifest;
chapters H/I consume the SUPPLY, not the carriers — H-10's routing note; no other
leanfinal/leanspec file mentions them — grep 2026-08-16):

| node | prediction | verdict |
|---|---|---|
| C.109 | re-sign (the refutation's demand) | RE-SIGNED (`hwf` + C.109a) |
| C.110 | clean (no `HTNode`) | CLEAN — both statements read raw `(d,a,k,N)` data |
| C.111 | re-sign (free `s` vs `D`) | REFUTED as frozen, machine-checked; RE-SIGNED |
| C.112 | clean (`hBD` hypothesis-carried) | CLEAN — pure algebra given `hBD`; verified |
| C.113 | clean (no `HTNode`) | CLEAN |
| C.114 | re-sign (the refutation note's flag) | REFUTED as frozen (both axioms), machine-checked; WITHDRAWN + BLOCKED (A-C.3) |
| C.115 | clean (formula-level) | CLEAN — `ht_depth_zero` true for arbitrary `v`; verified |
| C.116 | manifest update | UPDATED (`+HTNode.WF`, `−ht_branch/ht_global`) |

**(VI) Certification (`verification/c109_ac2_cell_check.py`, 127 checks, exit 0; output
committed).** [LAW] 13 exact-count instances of the re-signed C.109 over `ℤ/p^N`
truncations: `q ∈ {2,3}` × {steep side, interior-lattice side (all three quadratic
types), `ℓ = 2` side, flat side, two sides sharing a vertex} + one `Q = 4` instance
through a degree-2 key (`Φ = x²+x+1` over `ℤ/2^N`). [ENC] the chord-test encodings agree
with direct rational hull geometry on every instance. [MUT] `L±1` (M1), empty sides (M2 —
the refutation note's arithmetic verified), the retired pin (M3 — empty cell at the
char-`p` killer types; `Q^{2N−4}(Q−1)² ≠ Q^{2N−3}(Q−1)` at `ℓ = 2`) all KILL; the frozen
C.111 and the κ-freedom of C.114 refuted numerically ([C111], [C114] legs). A first-run
finding, recorded: at `q = 3` the double-root type's interior coefficient `−2c` is
nonzero, so the OLD pin is accidentally IMPLIED by that single type there — the defect is
exactly that the pin smuggles a type-dependent constraint into the polygon clause; the
char-dependent killer types expose it.

**(VII) Bookkeeping.** Census: nodes 129 → **130** (+C.109a [lemma]); A-5's fleet figure
≈166 → **≈167**. DAG: C.109a rows added to `spec/DAG_BLUEPRINT_C.tsv` (stmt-dep →
`EFF.W12.s1of2.23`; proof-deps → B.02, B.06, B.10; C.109 → C.109a). `leanfinal` edit
surface: `Uniformity/ChapC/C108.lean` ONLY (definitional node, no landed proof consumes
the retired pin — grep-verified; compiles clean, AxCheck extended); both refutation
records re-verified against the re-signed cell (Lean-core footprints). The two `.lean.txt`
refutation records are PERMANENT (headers carry the repair notes). Standing obligation
opened: **A-C.3 — the C.114 realizes-refinement re-sign** (clause list at the node
banner), with its own certification leg required before signing.

# A-C.4 AMENDMENT (2026-08-16, unit EWBS2) — THE TWO OM-10 LAW NODES (C.127, C.128)

**Charge and label.** OM-10's §3.6 flagged, as an orchestrator OPTION, "a dated A-C
amendment adding two law nodes at the certified statements" for LAW E-W and LAW B-S2,
which had "no signed home". This amendment is that option, executed. Label A-C.4: A-C.1
is the signature-completion layer above; A-C.2 is the concurrently-landed C.109 cell-law
re-sign (certification leg `verification/c109_ac2_cell_check.py`, commit `44709256`);
A-C.3 is RESERVED by A-C.2's charter for the C.114 realizes-refinement re-sign
(PROJECT_STATE append #75) and is not this amendment.
Census effect: nodes 129 → **131** (+C.127, +C.128); no committed node is edited.

**Grade asymmetry, stated plainly.** C.127 is signed at a PROVED source (the LAW E-W
proof note, verifier-passed, every display machine-certified bit-exact). C.128 is signed
at a CERTIFIED-OPEN source (OM-10 §2.2, 7/7 frames, two primes) — it is a LAW CANDIDATE
whose Lean proof would be new mathematics; the fleet may prove it or leave it standing
as the chapter's honest conditional, but MUST NOT widen it (its TEETH row records a
refuted wider candidate).

---

### NODE C.127 [theorem] [fresh] [signed: A-C.4] — **LAW E-W: the K2-division boundary identity (three clauses)**

**STATEMENT.** At the trinomial single-crossing frame — `F.key = x^{D′} − πω` (`f₁ = 1`,
`h = 1`, `e₁ = D′`), `composedKey T = F.key^m + ĉ₂π^{v₂}x^{i₂}·F.key^{m−1} + ĉ₀π^{v₀}`
(`e₂ = 1`, `f₂ = m`), on-side (`u₂ = D′v₂ + i₂`, `D′v₀ = m·u₂`), in-grid
(`μ₂·i₂ < D′`) — the single-entry member `f = Φ₂^{μ₂} + c·π^α·x^a·Φ′^b·Φ₂^{j′}`
(`j′ ≤ 1`) has: **(a)** empty shadow/honest discrepancy at every coordinate when
`j′ = 0` or `a + i₂ < D′`; **(b)** when `j′ = 1` and `a + i₂ ≥ D′`, empty discrepancy
at every `j ≥ 2` and discrepancy height EXACTLY `gridWeight T α a b (1−j) + margin` at
`j ∈ {0, 1}` — the subtraction-free form of OM-10's
`mindiff_j = Θ_j + (entry height − side height)`. Tight at every excess including the
on-side boundary (T-E-BOUND is clause (b) at `ε = 0`).

**SIGNATURE** [signed: A-C.3 — elaborated in `leanspec/Leanspec/ChapC.lean`, section
`AC4Laws`]. Three axiom-stubs (proof targets, standing stub lifecycle):
`lawEW_faithful_of_nox` (clause (a)), `lawEW_faithful_high` (clause (b), `j ≥ 2`),
`lawEW_pin` (clause (b), `j ≤ 1`; conclusion
`dv2Hgt (T.levelDatum hπ) (shadowDev T f j − dev (composedKey T) f j)
= ((gridWeight T α a b (1 − j) + T.margin : ℕ) : ℕ∞)`). The frame is pinned by
equation hypotheses on `F.key` and `composedKey T` (D19-safe: no `stageLiftO` plumbing
is consumed); `δ = T.margin ≥ 1` is automatic from `T.hfloor`, so (F4) carries no
hypothesis. Instance: OM-10's W1 (`ℤ₂`, `x³−2`, `Φ′³ + 8xΦ′² + 1024`).

**DEPENDS.** C.11 (`dv2Hgt`) · C.42/C.43 (`TowerDatum`, `composedKey`) · C.44
(`levelDatum`) · C.50 (`slotOffset`/`gridWeight`) · C.71 (`shadowDev`, `margin`,
`theta`).

**PROOF.** transcribe `lean/notes/openmath/LAWEW_PROOF_2026-08-16.md` (PROVED;
two-pass adversarially verified): the development identity births the seed
`g·Y^{b+m−1}(Y − Φ′)`; chain linearity + the `Φ′`-scalar kill localize `Δ` to the
seed's one division; the telescoping census gives exact `q`/`r`; the two on-side
integralities collapse every slot height to `H_C + δ` resp. `H_C + E₂ + δ`; the sole
collision (`b = m−1`, forced by `D′ ∣ mi₂`) only rises. Clause (a) is the in-grid
uniqueness of the development.

**SIZE.** ~40 + ~30 + ~90 lines (the three stubs; the pin clause carries the census).

**SOURCE.** `lean/notes/openmath/LAWEW_PROOF_2026-08-16.md` (the theorem + §6's
certification record); OM-10 §2.4 (LEG E, the certified pin law).

**TEETH.** §13-style numeric leg EXISTS already, retained under `verification/`:
`ewbs2_lawew_cert.py` GREEN 2796/0, 5 teeth (T-EW-DELTA margin-forgotten, T-EW-J0
`j′`-blind crossing, T-EW-SIGN sign-stripped census, T-EW-WRAP `ω`-stripped reduction,
T-EW-COLLIDE the collision jump) — the closed-form dicts bit-exact on 281 crossing
rows, 11 frames, `p ∈ {2,3,5}`. SCOPE FENCE: `j′ ≥ 2` members DEVIATE at `p = 2`
(measured, `V1p2m3`: pin one grade high at two rows) — no fleet agent may generalize
the statement over `j′`.

**ENVIRONMENT.** ENV-C1.

---

### NODE C.128 [law-candidate] [fresh] [signed: A-C.4] — **LAW B-S2: the P-BINOM cascade pair-or-triple attainment law**

**STATEMENT.** At the cascade geography — `e₂(f₂ − t*) = 1` with `ψ₂.coeff t* ≠ 0` and
the `t*`-entry carrying `x`-power exactly 1 (`slotIdx ((f₂ − t*)·u₂) = 1`), `f₁ = 1`,
`μ₂ ≥ 3` — the pure power `Φ₂^{μ₂}` attains its top-coordinate floor
(`TouchCert` at `j* = (μ₂ − 2) + (2e₂t* + 1)/(e₂f₂)`) **iff**
`p ∤ binom(μ₂,2)` **or** `p ∤ binom(μ₂,3)` (`p = ringChar` of the residue field): the
height-`Θ_{j*}` graded layer is carried by the PAIR and TRIPLE diagonal slots only.

**GRADE.** CERTIFIED-OPEN (OM-10 §2.2: 7/7 — B3/B4/B5 at `q = 2`, BP3/BP4/BP5/BP6 at
`q = 3`; BP3 reproduces the GENTOW6_PROOF r1 bracket record bit-exactly). NOT proved;
NOT consumed by any committed node; the fleet's cite-vs-prove choice per the 2026-08-15
sign-off scope.

**SIGNATURE** [signed: A-C.3 — elaborated in `leanspec/Leanspec/ChapC.lean`, section
`AC4Laws`]. One axiom-stub: `lawBS2_pair_or_triple`, stated as a `TouchCert` iff — the
attainment predicate is C.74's existing definition, no new carrier.

**DEPENDS.** C.15 (`slotIdx`) · C.42/C.43 · C.44 · C.71 · C.74 (`TouchCert`).

**PROOF.** open (law candidate). The certified route: the k-diagonal extraction
branches at the `e₂(f₂ − t*) = 1` geography carry digits `~ binom(μ₂,k)`; the measured
tables kill every `k ≥ 4` branch (see TEETH); a proof must show the `k ≥ 4` branches
land strictly above the floor in general — the LAW E-W seed calculus (C.127's Step 3
census) is the expected instrument, one Φ₂-division deeper.

**SIZE.** statement 12 lines; proof unsized (open).

**SOURCE.** OM-10 §2.2 (LEG B, `om10_cert.py` B-LAW 7/7); upstream THEOREM
GENTOW-6.5(a)/(b) at the BOXES note's 0/2 grade.

**TEETH** (preserved VERBATIM from OM-10 §2.2, per the conversion unit's charge):
> **The naive "any in-band k-diagonal" candidate (this unit's own outline B-S2) is
> REFUTED at B4**: binom(4,4) = 1 is a unit, yet pin(ShC_3) = 8 = Θ + 1 — k ≥ 4
> branches land strictly above the floor (B5 confirms at μ₂ = 5). Refutation kept; the
> repaired pair-or-triple law is the certified object.
Plus the OM-10 LEG B teeth T-B-COEF (the `μ₂`-for-`binom` mutant) and T-B-ALLM (the
always-attains mutant, killed at all 5 `p ∣ binom` frames). Any fleet proof attempt
that derives an "any-k" statement has re-proved a REFUTED claim and must stop.

**ENVIRONMENT.** ENV-C1.

<!-- CHAP-C APPEND POINT — do not remove; sections are appended here in order -->
