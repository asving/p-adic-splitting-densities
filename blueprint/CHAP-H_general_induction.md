# CHAPTER H — THE GENERAL INDUCTION (two species, genre finiteness, the composite-stage laws)

**Chapter of:** the Phase-1 formalization blueprint (`docs/BLUEPRINT_PHASE_DESIGN_2026-08-13.md`
REVISION 2; node contract §2 as tightened by the fleet-protocol repairs).
**Chapter cut:** `spec/DAG_README.md` "THE CHAPTER CUT", chapter **H = GENERAL INDUCTION**
(notes `GENIND`, `GENHN`, `GENH4`, `W12`; 498 DAG nodes; consumer-first order position sixth,
immediately above the GRT weld layer `F` and the base cases `G`).
**Sources transcribed:** `spec/EFF-GENIND.md` (206 units), `spec/EFF-GENH4.md` (111 units),
`spec/EFF-GENHN.md` (93 units). `W12` is **not** transcribed here — it exists only as an unmerged
shard pair with shard-local IDs (`spec/DAG_README.md`, finding 6); see honesty item **H-12**.
**Supplier chapters consumed:** **G** (BASE CASES AND MENUS — 78 blueprint nodes, the landed
`Uniformity/ChapG/` layer) and **A** (the landed Lean kernel).
**Target repo:** `leanfinal/` (general `O`; the standing complete-DVR bundle).
**Authored:** 2026-08-15, Opus arm (Asvin-authorized substitution, appends #51/#52).
**CODEX CROSS-READ OWED.**

---

## 0. How to read this chapter

### 0.1 The five standing environments

Every node names its environment as `ENV-H1` … `ENV-H5` plus deltas.

**ENV-H1 — the arithmetic arena (the chapter's default and its unconditional mass).** No `O`, no
polynomials: statements about `ℕ`, `ℤ` and `ℝ` only.

```lean
import Uniformity
namespace Uniformity.Density.Induction
open Finset Filter Topology
```

**ENV-H2 — the density arena** (chapter G's `ENV-A`, verbatim):

```lean
import Uniformity
namespace Uniformity.Density
open IsLocalRing Polynomial Filter Topology
variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)] {π : O}
```

**ENV-H3 — ENV-H2 plus completeness** (every node that lifts through Hensel):

```lean
variable [IsAdicComplete (maximalIdeal O) O]
```

**ENV-H4 — the stage-field arena** (pure finite-field algebra, no `O`; the stage residue field `K`
and its `F_Q`-subfield):

```lean
import Uniformity
namespace Uniformity.Density.Induction
open Polynomial
variable {F K : Type*} [Field F] [Finite F] [Field K] [Finite K] [Algebra F K]
```

**ENV-H5 — the coefficient-algebra arena** (the development identities; a bare commutative ring,
because every one of them is a `ring` identity valid in both characteristics):

```lean
import Uniformity
namespace Uniformity.Density.Induction
open Polynomial
variable {R : Type*} [CommRing R]
```

`ENV-H2'` abbreviates "ENV-H2 with `π` promoted to an explicit hypothesis `(hπ : Irreducible π)`",
chapter G's convention (`Drainage.lean:85`, `DensityAPI.lean:124`).

### 0.2 File layout and naming

* One Lean file per node: `leanfinal/Uniformity/ChapH/H<nn>.lean`, module
  `Uniformity.ChapH.H<nn>`.
* Chapter roll-up `leanfinal/Uniformity/ChapH.lean` imports every node module in this file's
  topological order; `Uniformity.lean` gains one line `import Uniformity.ChapH`. **`ChapH.lean`
  imports `Uniformity.ChapG`** — chapter H consumes chapter G's landed declarations by name.
* **Namespaces are the landed ones.** New *definitions* of this chapter live in the sub-namespace
  `Uniformity.Density.Induction`; new *theorems about landed objects* (`undecidedSeq`, `typeOf`,
  `CoveringMenu`, `UniformityStatement`) live directly in `Uniformity.Density`. Chapter G's own
  sub-namespace `Uniformity.Density.Menu` is **read, never extended**.
* One PUBLIC declaration per node; private helpers may live below it in the same file. A reusable
  helper triggers a RE-PLAN request to the orchestrator, never a silent second public name.

### 0.3 Names that already exist and must not be redefined

**From `Uniformity.Density` (the landed kernel, chapter A).** Consumed by name, never re-proved:
`FactorizationType`, `FactorizationType.degree`, `FactorizationType.degree_mk_add`, `typeOf`,
`typeOf_data`, `typeOf_degree`, `typeOf_mul`, `monicFactors`, `monicFactors_mul`, `efPair`,
`ramIndexOf`, `inertiaDegOf`, `normValues`, `normDivisors`, `efPair_pos_of_mem`,
`efPair_mul_le_natDegree`, `monicPoly`, `monicPoly_monic`, `monicPoly_natDegree`, `Coeff`, `Res`,
`proj`, `proj_surjective`, `resFactor`, `resFactor_mk`, `resFactor_surjective`, `coeffFactor`,
`coeffFactor_proj`, `coeffFactor_surjective`, `card_preimage_coeffFactor`, `card_res`,
`card_coeff`, `residueCard`, `two_le_residueCard`, `towerSection`, `resFactor_towerSection`,
`DecidedAt`, `PossibleAt`, `decidedSet`, `possibleSet`, `decidedCount`, `possibleCount`,
`decidedSeq`, `possibleSeq`, `decidedDensity`, `genuineDensity`, `gapSeq`, `UndecidedVanishes`,
`UndecidedAt`, `undecidedSet`, `undecidedCount`, `undecidedSeq`, `CoveringMenu`,
`card_le_sum_possibleCount`, `decidedSet_disjoint`, `decidedSeq_le_decidedDensity`,
`genuineDensity_le_possibleSeq`, `sum_decidedDensity_le_one`, `one_le_sum_genuineDensity`,
`sum_genuineDensity_eq_one_of_drainage`, `genuineDensity_eq_of_drainage`,
`decidedAt_of_congr`, `decidedDensity_ge_of_subset`, `genuineDensity_le_of_superset`,
`drainage_of_undecided_comp`, `gapSeq_antitone_general`, `gapSeq_le_undecidedSeq`,
`card_certSet_gen`, `typeOf_eisenstein`, `typeOf_inert_of_irreducible_map`,
`typeOf_of_residual_coprime`, `typeOf_prod_X_sub_C`, `typeOf_shift`, `typeOf_scaleRoots`,
`typeOf_scale`, `norm_adjoinRoot_root`, `exists_monic_factorization`,
`exists_monic_factorization_finset`, `exists_linear_factorization`, `exists_monicPoly_eq`,
`exists_coveringMenu`, `mem_maximalIdeal_pow_iff_dvd`, `pow_dvd_iff_le_addVal`,
`addVal_eq_of_dvd_not_dvd`, `exists_addVal_eq`, `exists_unit_mul_pow_of_addVal_eq`,
`UniformityStatement`, `UniformityStatementDecided`, `UniformityStatement.ofDecided`,
`TotalMassOne`, `DrainageAt`, `drainage_two`, `drainage_one`.

**From `Uniformity.Hensel`:** `coeffIdeal`, `mem_coeffIdeal`, `exists_solve_field`,
`exists_solve_mod`, `exists_solve_step`, `exists_monic_lift`, `monic_factorization_unique`,
`isCoprime_of_map_eq`, `exists_eq_add_mul_of_degree_lt`, `strongHensel`, `strongHensel_addVal`,
`exists_root_of_strongHensel`, `root_unique_of_strongHensel`, `NState`, `newton_step`,
`gate_fires`.

**From `Uniformity.Density.Menu` (chapter G's landed layer — READ, never extended).** The ones
chapter H actually consumes: `ExactVal`, `exactVal_iff_addVal`, `exactVal_unique`, `readEquiv`,
`readEquiv_proj`, **`CertFamily`**, **`CertFamily.set`**, **`CertFamily.card`**,
**`CertFamily.decidedAt`**, **`CertFamily.decidedDensity_ge`**, `tangSet`, `tangAdm`,
`card_tangSet`, `card_tangAdm`, `depthSet`, `card_depthSet`, `depthSet_odd_eq_empty`,
`residualPair`, `resStratum`, `SepPair`, `DblPair`, `AniForm` (landed as
`Uniformity.Density.AniForm`), `two_mul_card_aniForm`, `two_mul_card_sepPair`, `card_dblPair`,
`prodResFactor`, `card_preimage_prodResFactor`, `resTop`, `resAdm`, `resClassSet`,
`card_resClassSet`, `resCert`, `resAdm_read_iff`, `TransInvariant`, `undecidedCount_two_eq`,
`undecidedSeq_two_eq`, `undecidedSet_eq_tangSet`, `typeOf_three_cases`, `coveringMenu_three`,
`species3`, `card_species3`, `hex3R`, `hex3R_rec`, `hex3U`, `hex3U_rec`, `hex3U_le`,
`hex3U_div_tendsto_zero`, `drainage_three_of_hex3_bound`, `totalMass_three_of_drainage`,
`card_le_undecidedCount_three`, `three_mul_card_noRootCubic`, `six_mul_card_split3`,
`two_mul_card_linAni`, `CubicFamilyIndex`, `CubicFamilyIndex.schema`, `card_cubicFamilyIndex`.

**Two near-miss names to keep apart.** Chapter G's `card_depthSet` counts depth strata of the
`n = 2` tangency filtration; chapter H's `alphaExp` / `alphaBracket` count α-slices of a general
`(m, d)` cluster system. They are different objects at `m = 2` too — G's is a `Coeff O 2 N` count,
H's is an exponent in `ℕ`. Nothing in chapter H redefines a chapter-G name.

### 0.4 The chapter's mathematical spine, in one page

The corpus's general induction is a statement about **cluster systems** `(m, d, N)`: monic
degree-`md` polynomials over `O/π^N` whose reduction is `P̄^m` for a fixed monic irreducible `P̄`
of degree `d`, coordinatized by the `Φ`-adic development `f = Φ^m + Σ_{j<m} a_j Φ^j` with
`a_j ∈ (O/π^N)[x]_{<d}`, `ā_j = 0` — `Q^{m(N−1)}` states, `Q := q^d`, `c(m) := m(m−1)/2`
(`EFF.GENIND.07`). Its content splits into **three layers of completely different Lean character**,
and that split *is* this chapter's architecture:

| layer | corpus content | Lean character | chapter-H sections |
|---|---|---|---|
| **arithmetic** | every locus law, every bracket, every rate, every visibility floor, every entry-height computation | statements about `ℕ`/`ℤ`/`ℝ` — **no `O`, no polygon, no Hensel**; provable outright | §§4–7, §10 |
| **algebraic** | the development identities, the slot/no-cancellation lemmas, the carry cancellation, the σ-forcing chain, the unit-pivot condition | statements about `CommRing`/finite fields/`typeOf` — provable from `leanfinal`'s landed API | §§8, 9, 11, 12 |
| **geometric** | Newton polygons, the refine taxonomy, the Hensel split at the scaled frame, the stage read's count-isomorphism | **NOT provable at transcription grade** — the corpus itself carries these as displayed hypotheses `(CS-1)`/`(CS-1Q)`/`(CS-2)`/`(CS-3)` | §3's schema fields; honesty block |

**The organising object, therefore, is a SCHEMA, not a construction** — the chapter-G `CertFamily`
lesson applied one level up. `GenreDatum` (H.01) carries the local genre datum
`G = (Q; e₁, f₁, μ; h, entry)` of `THEOREM GENHN.CLASS` (`EFF.GENHN.07`) with its four side
conditions as fields; `StageInterface` (H.09) carries the `(CS-1Q)`/`(CS-2)` clause family as
fields — *exactly* the corpus's own hypothesis, no weaker and no stronger — and every count and
rate theorem of §10 is then proved *from the fields*, unconditionally. A fleet agent never has to
prove a polygon fact, and a reader can see at a glance which conjunct of the capstone's
conditionality each field is.

What the chapter proves, by headline:

| result | statement | node |
|---|---|---|
| the general bracket | `Q · B_{m,d}(μ) = (Q−1)·Q^{(c(m)+1)μ}`, exponent coefficient `c(m)+1 = 2,4,7,11` at `m = 2,3,4,5` | H.20, H.21 |
| the α-transport identity | ghost exponent `k·c(m)` + reduced-window exponent `m·W` = α-locus exponent | H.17 |
| the `m = 2` species | `u(M) = Q^{M−1} + ⌊(M−1)/2⌋(Q−1)Q^{M−2}`, and `u(N) ≤ N·Q^{N−1}` | H.26, H.27 |
| **the (A2-RATE) ground instance** | `u(N)/Q^{2(N−1)} ≤ N·Q^{−(N−1)}` — `(K,B,c) = (1,1,1)` | H.28 |
| the composite criterion | `4 ≤ e₁μf₁`, hence `m ≥ 4`, hence `n ≥ 4`; `e₁f₁μ = 4` has exactly the two solutions `(2,1,2)`, `(1,2,2)` | H.03, H.04 |
| **genre finiteness, honestly** | the SCHEMA set is finite; the DATUM set is **infinite** — the A2 refutation, proved | H.05, H.06 |
| the occupied-height scope | every `m > D′h` is occupied; `(e₁,f₁,h,m) = (3,1,2,1)` is **not** | H.10, H.11 |
| **the unit-pivot lemma** | triangular with unit pivots ⟹ bijective; and the `ZMod 4` toy is triangular and **not** surjective | H.60, H.62 |
| **window-truncation monotonicity** | `undecidedSeq O n` is ANTITONE — `GENIND-C2D` in `leanfinal`'s own terms | H.70 |
| the union bound | `∏T − ∏(T−u) ≤ Σ_l u_l ∏_{j≠l} T_j`, with no exactness hypothesis | H.63 |
| the σ-forcing chain | `e₁ ∣ e`, `f₁ ∣ f`, `e·f ≤ e₁f₁` ⟹ `(e,f) = (e₁,f₁)` | H.76 |
| the carry cancellation | the three-term `z̄`-twist kill, **both characteristics** | H.87 |
| the base cases | `P(2)` unconditional (chapter G); `P(3)` given drainage | H.96, H.97 |
| the capstone, conditionally | `UniformityStatement` from the package at every degree | H.98 |

**Why the arithmetic layer is the bulk and why that is the right call.** The corpus's own
verification history says so. Every defect that eight in-house hostile passes missed and a
decorrelated read caught was **arithmetic or scope**, not geometric: the missing `4k ≤ N−1` floor
(`EFF.GENIND.162`, a *non-integer count* `2^{−6}`), the `d`-factor slip (`EFF.GENIND.188`), the
`M★ < N` inference from a *lower* bound (`EFF.GENIND.202`), `GENHN.CLASS`'s infinite datum set
(`EFF.GENHN.07`), the unoccupied height `(3,1,2,1)` (`EFF.GENHN.09`), `GENH4-CAP`'s overlapping
antecedents (`EFF.GENH4.18`), `GENH4-1`'s budget display false *at every checked genre*
(`EFF.GENHN.23`). Lean is exactly the instrument for that class. The geometric layer, by contrast,
is where the corpus's own grade is `PROOF-ONLY` or `schema`, and formalizing a schema as a
structure with hypothesis fields is the honest transcription of a schema.

---

## 1. HONESTY BLOCK (read before consuming any node)

**H-1 — `THEOREM GENIND.B` IS A REDUCTION, and no node of this chapter changes that.** The
chapter's single most important carried sentence, `GENIND-BOX-1` verbatim (`EFF.GENIND.75`):
*"The composite-stage laws are OPEN at every genre; GENIND-5 is a CANDIDATE with its obstruction
displayed (OB-a..d). No count law at order ≥ 2 is claimed proved. THEOREM GENIND.B is a REDUCTION;
its unconditional content at n ≥ 4 is exactly the simple-stage layer (GENIND.C) + the criterion +
the opening-mass laws."* Chapter H's `InductionPackage` (H.95) and `uniformity_of_package` (H.98)
are the Lean form of the reduction, with the composite-stage content sitting in
`StageInterface`'s fields. **No node of this chapter asserts that any composite-stage count law is
proved.**

**H-2 — `(CS-1Q)` = ledger `HYP.36`, disposition CARRY, is a FIELD of `StageInterface`, not a
theorem.** The 2026-08-12 round-2 correction (`EFF.GENIND.197`, `.199`) replaced the label
"conditional on (CS-1) only" by **"conditional on (CS-1Q), verified per genre"**, and its
certification-status sentence is verbatim: *"The displayed general (CS-1), GENIND-6(a), and GENHN
references do not establish (CS-1Q.b) for every embedded or mixed genre … A universal discharge for
embedded and mixed genres remains obstructed until those affine ledgers are displayed and
checked."* Chapter H therefore carries `(CS-1Q.a)` and `(CS-1Q.b)` as the two hypothesis fields
`hwin` and `hprice` of `StageInterface` (H.09), and `rate_lossPriced` (H.72) is proved **from
them**. The exemption the ledger grants is transcribed exactly: the two standalone quartic genres
have `Δ_G = 0` (H.09's `stageLoss = 0` instances H.38/H.42), where `(CS-1Q.a)` degenerates to the
withdrawn scalar bound. **A fleet agent who finds a node needing `(CS-1Q.b)` for an embedded or
mixed genre has left the chapter and must return `BLOCKED: HYP.36`.**

**H-3 — `GENIND-1`'s all-`O` generality is an INTERFACE FLAG, ledger `HYP.121`, class
`interface-generality`, disposition CARRY, and it is UNAUDITED.** The Q1 generality audit's own
wording (quoted at `EFF.GENIND.19`): *"INTERFACE — load-bearing, unaudited. `GENIND-1` is essential
in W12-HT Step 3 and termination/compatibility, but its statement and proof were not pasted. Its
generality cannot be certified here."* The note itself makes no all-`O` claim beyond its `S1`
convention, and its machine leg is prime-`q`, `d = 1` (`GENIND-BOX-3`, `EFF.GENIND.77`). Chapter H
does **not** formalize `GENIND-1` — the event grammar, fracture permanence and the refine taxonomy
are geometric, and there is no node for them. What chapter H does instead: every arithmetic
consequence of `GENIND-1` that the induction consumes (§§4–7) is proved **at general `Q ≥ 2` and
general `m ≥ 2`, with no residue-characteristic hypothesis and no `d = 1` restriction**, so the
`Q`-uniformity `GENIND-BOX-3` asserts becomes, for the arithmetic layer only, a *theorem*. The
grammar itself stays outside; `HYP.121` is unmoved by this chapter.

**H-4 — the `HYP.137` carve-out (`HEX3-BOX-1`, the tail-σ certification lemma) is inherited from
chapter G unchanged and gets NO node here.** Its ledger disposition is disclosure-without-promotion
(`spec/HYPOTHESIS_LEDGER.md:1086–1091`): it is *not* a conjunct of the capstone's hypothesis block,
because the `(hExhaust-3)` discharge provably never needed it (HEX3 L692–693), and its only live
consumer is GENIND's `S8.2` `W-12.B` corroboration aside (`EFF.GENIND.136` row 2). Chapter H's
`P(3)` node (H.97) takes drainage as an explicit hypothesis and cites chapter G's
`drainage_three_of_hex3_bound`; **the `S8.2` corroboration aside is not transcribed and must not
be given a node.** A fleet agent needing the tail-σ lemma returns `BLOCKED: HYP.137`.

**H-5 — the deep tier this chapter does NOT prove, item by item.** Five named boxes, all OPEN, all
carried as `StageInterface` fields or as explicit non-nodes:

1. **`[GENHN-HE(μ ≥ 3)]`** (ledger `HYP.81`, first live `n = 6`) — the σ-decision at stage leaves
   of multiplicity `μ ≥ 3`. `EFF.GENHN.55` item 1: *"THE one load-bearing open lemma of the whole
   composite program."* Chapter H's σ layer (§11) covers `μ = 2` only; `stageSigma` (H.73) is
   defined only for the three `μ = 2` leaf labels. The ledger's SCOPE SPLIT (HE3 proves `μ ≤ 3`
   unconditionally, `μ ≥ 4` rides `HE3-BOX-6`) is a **chapter-B** matter — `HE3`/`HE7` are chapter
   B — and `EFF.GENHN.40`(c) records that neither discharge has landed on GENHN.
2. **`[GENHN-TOW-1]`**, six items (ledger `HYP.82`) — load-bearing for `P(n)` at `n ≥ 8` ONLY,
   empty at `n ≤ 7`. Chapter H transcribes the tower *arithmetic* (H.50: `μ ≥ 4 ⟹ n ≥ 8`; depth 3
   ⟹ `n ≥ 16`) and the composed-degree identities (H.58, H.79) and **stops there**. The composed
   entry budgets, the inner refine transfer, the faithfulness geography, the partial inner sides,
   the composed window ledger and item (6)'s iterated depth-`≥ 3` key composition have **no
   nodes**.
3. **`GENHN-BOX-2` / the W-9 graded face** (ledger `HYP.148`, class CARRY at full strength, with
   `HYP.139`'s W-1 transport as its sub-residue at class MATH). `EFF.GENHN.33`: `LEMMA GENHN-4`'s
   layer 1 at `μ ≥ 3` consumes `COROLLARY W-9`'s twisted algebra as the carry bookkeeping —
   *"the count laws at μ ≥ 3 stand on one accepted weld face"*, and
   `runs/qgen/WELD_FACE_AUDIT.md` records that **J-D0 cannot cover it even in principle** (the
   recentering is an additive shift). Chapter H formalizes the `μ = 2` carry cancellation
   elementarily (H.87 — which is `GENH4`'s own elementary computation, `EFF.GENH4.23`) and gives
   **no node** to layer 1 at `μ ≥ 3`. `HYP.149`'s WELD-ZERO discharge route sits at clean-pass 1
   of 2 and licenses nothing.
4. **`(CS-3)` = `(H-e)` at general stages** (`EFF.GENIND.65`, `EFF.GENIND.72`(OB-c)). `TEETH` at
   that unit: *"NONE, at any degree, anywhere in this note."* Chapter H's `StageInterface` carries
   it as the field `hsigma`; `GENH4.C`'s two-genre instance is transcribed at H.75 as a *degree
   consistency* statement, not as a σ-decision proof.
5. **`CANDIDATE THEOREM GENIND-5`** (`EFF.GENIND.70`) — **NOT proved**, boxed at
   `(OB-a)`–`(OB-d)`. Chapter H transcribes only its *bracket shape* (H.21's audit includes the
   `(q−1)q^{2μ−1}` value) and marks it as a shape match, never as a premise. `EFF.GENHN.36`(c)
   flags exactly this hazard: *"GENHN uses only its displayed form as a shape to match, not as a
   premise; recorded here so a chapter cut does not upgrade it."* **Chapter H does not upgrade
   it.**

**H-6 — GENH4's disclosed CRITICAL-refutation record, carried in full.** `EFF.GENH4` is the
chapter's `n = 4` template and its repair history is the reason several chapter-H nodes exist at
all. The record, verbatim in substance:

* **A repaired CRITICAL in `THEOREM GENH4.A`'s census** (`EFF.GENH4.07`, `.08`): the sealed
  parenthetical declared only the *exponents* comp-weighted; the *pin censuses* are comp-weighted
  too — `q^{comp(m)} − 1` per RAM and per 2SIDED pin, which is `q−1` (not `Q−1 = q²−1`) on the
  genre-F boundary band. Chapter H's H.44 audit is stated at both the interior and the band value
  precisely so a wrong census cannot pass.
* **`GENH4-CAP`'s two-layer repair, the second layer of which the note itself ledgers as a
  method lesson** (`EFF.GENH4.18`): the `[r2]` restatement *transcribed the PE2 verifier's own
  clause* and thereby dropped a side condition, producing **overlapping antecedents with
  conflicting conclusions**; `[r3]` re-derived a **pairwise-disjoint** trichotomy from the note's
  own `GENH4-3(i)`. The note's lesson: *"re-derive, never transcribe a verifier's phrasing."*
  Chapter H's H.88 makes the disjointness and the exhaustiveness a machine-checked theorem, and
  its audit reproduces the three committed counter-key checks including the refuted `r2` ordering's
  prediction `512/0`.
* **The `THEOREM GENH4.B` genre-E law CORRECTION disclosed at source** (`EFF.GENH4.10`): the
  scout's quoted `(q−1)q^{N+(h−1)/2}` is the `h = 1` instance only; the committed artifact reads
  `512` at `(q,N,h) = (2,7,3)`, not `256`. Chapter H's H.91 proves the coincidence is **iff
  `h = 1`** — the slip's mechanism, as a theorem.
* **`LEMMA GENH4-1`'s budget display FALSE at every checked genre including `f₁ = 1`**
  (`EFF.GENHN.23`(a), the strongest self-indictment in that note): *"the display contradicted the
  statement it sits in"* — the same lemma's own no-over/undercount clause failed. Chapter H's
  H.82/H.83 state the budgets in the **corrected** side-height form and carry the free-digit total
  as the no-over/undercount check, exactly as the corrected text does.
* **`LEMMA GENH4-4`'s onto-clause was MISUSED, not wrong** (`EFF.GENH4.09`): ANNEX R2's GAP-1
  showed a fixed-member application where only lift digits vary. Chapter H's H.61 states the
  fibre count over the **full slice** and its SIGNATURE quantifies accordingly; a fixed-member
  reading will not elaborate.

**H-7 — the `n ≥ 8` tower handoff to the hard chapters.** The dated supplier-movement record
(`EFF.GENIND.176`) is verbatim: *"read THIS note's conditionality at n ≥ 8 as: `[GENIND-H(n)] +
[GENHN-HE(μ ≥ 3)] + [GENHN-TOW-1]` … at n ≤ 7 nothing moves."* And `EFF.GENHN.18` preserves two
self-indictments that a chapter cut must not lose: *"The sealed word "EXACTLY" was FALSE at n ≥ 8"*
and *"the sentence "correct for the amended list" was itself over-reaching at n ≥ 16"*. Chapter H's
`InductionPackage` (H.95) is therefore **degree-indexed**, and H.98's conditionality is stated as a
hypothesis over all `n` with the honest note that at `n ≤ 7` the conjunction is one family and at
`n ≥ 8` it is three. The tower grammar itself is **chapter C** (`GENTOW1`–`GENTOW6`, `HETOW`), a
HARD chapter authored later per append #52's fork plan; the σ-ladder carrier suite is **chapter E**
(`T2`). Chapter H's §11 stops at the `μ = 2` dictionary and hands the rest to B/C/E by name.

**H-8 — `GENHN.CLASS`'s displayed finiteness is FALSE and this chapter proves BOTH halves.** The
A2 adjudication (`EFF.GENHN.07`) found the declared datum set infinite: at fixed `n = 4`, `Q = 2`,
every positive odd `h` gives a distinct datum `(2; 2,1,2; h, entry)` once `N ≥ 2h+1`. The owner
directive re-displayed the clause at the scope the proof establishes — **finitely many
parameterized genre SCHEMAS**, with `Q`, `h`, `N` and the prehistory depths as the schemas'
*parameters*. Chapter H lands **both**: H.05 proves the schema set finite, H.06 proves the datum
set infinite. Landing the refutation as a theorem is the point — it is the only way the corrected
scope is checkable rather than assertable. **`EFF.GENHN.07`'s clauses (i) and (iii) are unchanged
and are the ones H.01/H.02 transcribe.**

**H-9 — `GENHN.A(ii)`'s slot clause is re-displayed TWICE and the TERMINAL scope is `D′h < m`.**
The chain (`EFF.GENHN.09`): frozen "one K-digit slot per **integer** dv-height" → A2 obstruction
(the `(3,1,2,1)` witness: *"neither an integral normalizer nor a variable K-slot exists at height
1"*) → owner re-display "per **OCCUPIED** integer dv-height" → **post-D2b corrigendum**: the
re-display is itself too weak at `f₁ > 1` (sol's witness `(1,2,1,0)`), and the terminal scope is
*"per integer dv-height m with `D′h < m`, below the window cap. At `m ≤ D′h` the clause is
withdrawn entirely: a K-slot may be partial (the sol witness) or absent (the R4/A2 witness."*
Chapter H's H.09/H.10 state the occupied-height criterion **only** in the terminal domain, and
H.11/H.12 land the two witnesses as theorems. `EFF.GENHN.09`'s own protection sentence is
transcribed at H.08: every pin the laws consume sits in that domain, because the `[r1]`-corrected
node floor is `(μ−j)·D′h + 1 > D′h`.

**H-10 — `LEMMA GENHN-T(b)` was REFUTED (the program's first displayed-lemma refutation) and only
`T(b)′` is transcribed.** `EFF.GENHN.17`: `[r2]` refuted clause (b) at the leaf level (constructed
`n = 8` counter-instances, PARI-confirmed on two routes), withdrawing the sentences *"No new
mechanism"* and *"inheriting exactly GENHN.A's clause grades at each level"*; what survives is the
multiplicative `(e,f)`- and σ-composition FORMULAS applied to the **composed-key** pins. Chapter H
transcribes only the surviving formulas (H.79's composed degree) and the composed-basis bijection
(H.58); the corrected leaf read `T(b)′(iii)`, the stage shadow `(iv)` and the faithfulness geography
have **no nodes** (item (3) of `[GENHN-TOW-1]`). `EFF.GENHN.42`'s further layer — the composed key's
lift prescription was **gauge-naive** and is corrected by a consumer erratum, licensed only by
`LEMMA GENHN-LIFT` — is transcribed at H.54–H.57 as the *lift operator*, which is the part with a
proof.

**H-11 — a FALSE parenthetical stands in frozen accepted text (`WZ-BOX-7`), and chapter H sides
with the CONCLUSION, not the reason.** `EFF.GENHN.28`: GENHN's *"counts are twist-blind (J-D0:
(digits) ↦ (twisted digits) is a type-preserving bijection), LETTERS are twisted"* has a **false
reason** — WELDZERO's Repair 1 establishes the twist dictionary is *not* type-preserving, with a
machine witness on GENHN's own sealed data (972 of 972 live-wrap events flip `'2'` to `'1sq'`). The
CONCLUSION is upheld by both notes. **Chapter H therefore never states a type-preservation claim
about a twist map.** H.87 proves the *cancellation* (`S₀ + zs² − 2zs² = 0` given `S₀ = zs²`), which
is an identity, and H.61's fibre count is a *cardinality* statement over the full slice — neither
needs type preservation. `EFF.GENH4.20`'s sibling parenthetical carries the same defect and the same
treatment.

**H-12 — `W12` is in the chapter cut but not in this file, and that is a REAL gap here (unlike
chapter G's `JD0`).** The 0c cut assigns `W12` to chapter H. `W12` has **no merged effective
spec** — only `EFF-W12-s1of2.md` / `-s2of2.md` with shard-local IDs, and every DAG edge touching it
will be remapped by a future merge (`spec/DAG_README.md` finding 6). Consequences, stated plainly:

* `THEOREM W-12.A` (the order-1 cell law at every degree) is the supplier of **every** entry-mass
  law chapter H audits. Chapter H does not re-prove it; the entry laws enter as *defined functions*
  (H.38, H.42, H.45) whose exponents are re-derived from the genre's own heights, and the audits
  tie them to the corpus's committed spot values. That is a consistency check, **not** a proof of
  `W-12.A`.
* `THEOREM W-12.D` (menus + drainage ⟹ one `R_τ ∈ ℚ(q)`) is the reduction H.98 fires. Chapter H
  states H.98 with the package as an explicit hypothesis, and its `W-12.D` content is exactly
  `leanfinal`'s landed `UniformityStatement.ofDecided` plus H.95's package — i.e. the Lean side is
  **not** a citation of `W-12.D` but a re-derivation of the shape from the landed API.
* `W12`'s own r4 **σ-LABELING clause inside `(A1)`** strengthens the predicate `GENIND-0` is
  claimed to preserve, and `EFF.GENIND.30`'s closure claim is stated for the **pre-r4 `(A1)`**
  (OPEN-CALL 3 there). Chapter H's `A1Admissible` (H.93) is defined **with** a σ-label field, and
  H.94's closure theorem is proved for that strengthened predicate — closing the open call on the
  Lean side rather than inheriting it. **Flagged for the cross-read** (item 4 of §16).
* A separate `W12` transcription unit is owed and is **not** blocked by anything here.

**H-13 — the COARSE DAG edges this chapter refines, and the ones it defers.** `spec/DAG.tsv` carries
chapter-H edges landing on governing-unit placeholders (`resolution=…gov`), and the two
highest-fan-out placeholders in the whole graph are chapter-H units: **`EFF.GENHN.07` (99 edges)**
and `EFF.W12.s1of2.09` (44). This chapter **refines** the `EFF.GENHN.07` cluster: every chapter-H
node whose content is `GENHN.CLASS` names the clause it uses (`.07`(i) at H.01/H.02, `.07`(ii) at
H.05/H.06, `.07`(iii) at H.02's uniformity remark), so the cross-read can re-home those 99 edges
clause by clause. It **defers** the `W12` placeholders (H-12) and the `EFF.GENHN.07`↔`EFF.GENIND.*`
mutual cluster, which `dag_check.py` already adjudicates. The chapter's own DAG additions (§14) are
**new** statement-level edges — `spec/DAG_README.md`'s finding 1 (*"no intra-note dependency edges
exist"*) is why — and they retire no COARSE row: the coarse rows stay for the cross-read.

**H-14 — the `H → B` backward arc the cut mandates, and what this chapter does about it.** The cut's
heaviest backward arc is `H → B` at weight 12: *"GENIND/GENHN cite HE-core results while the HE core
consumes GENHN's slot layer — the clearest mandated split: GENHN's stage/slot infrastructure belongs
below chapter B, its count/tower results above it"* (`spec/DAG_README.md`). Chapter H **executes that
split at unit granularity**: §8 (the slot/lift layer, H.51–H.58) is the part chapter B consumes —
`EFF.GENHN.27`'s reverse XREF records `HE7_PROOF:LEMMA GENHN-2` count 1, *"HE7 consumes THE SLOT
LEMMA as its ladder base case"* — and it is placed **first among the algebraic sections** and
depends on nothing later. Chapters B and E may consume H.51–H.58 without consuming anything else in
chapter H. The remaining `H → B` weight (the `(CS-3)`/`(H-e)` cites) is honesty item H-5(4): a
`StageInterface` field, so no Lean edge runs backwards.

**H-15 — `leancheck` is EVIDENCE, never an import; and for chapter H it is thin.** Unlike chapter G
(whose `n ≤ 3` mass is re-derivation of a working `leancheck` layer), chapter H has **almost no
`leancheck` precedent**: `leancheck/UniformityCheck/` is an `n ≤ 3` layer, and chapter H is the
`n`-uniform scaffold. The two exceptions, both consumed as feasibility evidence only:
`CensusGen.card_certSet_gen`'s pattern (already landed in `leanfinal`, chapter G's H.07) and the
`N3Drain`/`N3Exact` drainage shape (chapter G's G.71/G.72). **Every chapter-H node is `fresh`.** The
practical consequence for the fleet: chapter H's risk profile is inverted relative to G's — the
arithmetic layer is low-risk-high-volume (`omega`/`ring`/`decide`/`Finset.sum` induction), the
schema layer is definitional, and the three hard nodes are H.63 (the union bound), H.70
(`undecidedSeq_antitone`) and H.71 (the lexicographic closure).

**H-16 — codex cross-read status: OWED.** Like every 0a/0b/0c artifact of this week, this chapter is
Opus-authored and has **not** been cross-read by codex. The specific items flagged for that read are
listed in §16.

**H-17 — what is genuinely NEW here (not in `leanfinal`, not in `leancheck`, not in chapter G).**
Six things, and they are the chapter's actual mathematical content:
1. the general α-bracket and its `c(m)+1` exponent law at every `m` (H.18–H.21) — chapter G has the
   `m = 2` telescoping coefficient only;
2. the `m = 2` conservative-complement closed form and its **rate** (H.23–H.28) — chapter G's
   `hex3U` layer is the `n = 3` analogue; the `m = 2` species with `(K,B,c) = (1,1,1)` is nowhere;
3. **`undecidedSeq_antitone`** (H.70) — window-truncation monotonicity, a new `leanfinal` theorem
   about a landed object, and the well-foundedness ingredient the corpus's own descent argument
   lacked until `GENIND-C2D`;
4. the **unit-pivot lemma with its counterexample** (H.59–H.62) — the R2 repair, and the first
   place in either repo where the failure mode is exhibited;
5. **genre finiteness stated correctly plus its refutation** (H.05, H.06) and the **occupied-height
   scope plus its two witnesses** (H.10–H.12);
6. the `n = 4` template's algebra (H.80–H.92) — the development identities, the carry cancellation
   in both characteristics, and `GENH4-CAP`'s disjoint trichotomy.

---

## 2. NODE INDEX

| § | nodes | content |
|---|---|---|
| 3 | H.01–H.12 | **THE GENRE SCHEMA** and the stage interface (schema-first, per the CertFamily lesson) |
| 4 | H.13–H.22 | arithmetic I — the α species: `c(m)`, the transport identity, the general bracket |
| 5 | H.23–H.29 | arithmetic II — the `m = 2` drainage species and the `(A2-RATE)` ground instance |
| 6 | H.30–H.37 | arithmetic III — the pricing inequalities (geometric sums, supporting lines, dominance) |
| 7 | H.38–H.50 | arithmetic IV — the genre laws, their visibility floors, the tower thresholds |
| 8 | H.51–H.58 | the slot / lift layer (**the `H → B` split point**: chapters B and E consume this) |
| 9 | H.59–H.62 | the unit-pivot layer (the R2 repair, with its counterexample) |
| 10 | H.63–H.72 | the drainage-rate calculus (union bound, two regimes, truncation, the closures) |
| 11 | H.73–H.79 | the σ dictionary and the `(e,f)`-forcing chain (`μ = 2` only) |
| 12 | H.80–H.92 | the `n = 4` template: development identities, budgets, carry, caps |
| 13 | H.93–H.99 | the assembly: `(A1)`-admissibility, the package, the base cases, the capstone |
| 14 | — | DAG additions |
| 15 | — | leanspec stub list (stage 0e) |
| 16 | — | teeth dispositions; flagged for the codex cross-read |

**Kind census:** 17 `def`, 52 `lemma`, 25 `theorem`, 2 `structure`-bearing `def` nodes counted as
`def`, 3 `gate` — **99 nodes**.
**Landed-node census:** 0 nodes are `landed:`; **41 distinct landed declarations** are consumed by
name across the DEPENDS fields (28 from chapter A's kernel, 13 from chapter G's `ChapG/` layer).
**Split-mandated nodes** (the fleet will see more than 99 units of work): H.20 → 2, H.26 → 2,
H.63 → 2, H.70 → 2, H.71 → 3, H.94 → 3, plus the split *candidates* flagged at H.05, H.31, H.53,
H.58, H.72, H.82, H.83, H.95. Planning figure for the fleet: **≈ 115 Lean files.**

**Graph shape** (computed from the DEPENDS fields, `spec/DAG_BLUEPRINT_H.tsv`): 214 intra-chapter
edges, **acyclic**, **critical path 11**, layer widths
`38, 21, 13, 9, 6, 4, 3, 2, 1, 1, 1`. **Thirty-eight nodes are fireable immediately** (they depend
only on landed API or on nothing) — the widest layer-0 in the project so far, and the direct payoff
of putting the arithmetic layer first. The critical path runs
`H.01 → H.09 → H.65 → H.67 → H.71 → H.72 → H.95 → H.96 → H.98 → H.99`, i.e. through the schema into
the rate calculus and out to the capstone; H.71 (the lexicographic closure) is the schedule risk.

---

## 3. §3 — THE GENRE SCHEMA AND THE STAGE INTERFACE

> **Design note (the CertFamily lesson, one level up).** Chapter G's `CertFamily` (`ChapG/G05.lean`)
> worked because its four hypothesis fields were *literally* `card_certSet_gen`'s hypotheses, so
> the count law was a one-line application and all the work sat in the instances. Chapter H does the
> same with the composite-stage layer: `GenreDatum` carries the local invariants of
> `THEOREM GENHN.CLASS` clause (i), and `StageInterface` carries the `(CS-1Q)`/`(CS-2)`/`(CS-3)`
> clause family *as fields, in the corpus's own terminal wording*. Everything in §10 is then proved
> from the fields. Two instances are exhibited (H.38's genre E and H.42's genre F) with
> `stageLoss = 0`, which is exactly the exemption `EFF.GENIND.199` grants.

### NODE H.01 [def] [fresh]

**STATEMENT.** *The local genre datum.* A **genre datum** consists of natural numbers
`Q, e₁, f₁, μ, h` subject to: `2 ≤ Q` (a residue cardinality); `2 ≤ e₁ * f₁` (else the event is an
order-1 α/β event, not composite); `2 ≤ μ` (the residual factor is repeated); `1 ≤ e₁`; `1 ≤ h`;
and `Nat.Coprime h e₁` (the side's slope `h/e₁` is in lowest terms). This is
`THEOREM GENHN.CLASS`(i)'s datum `G = (Q; e₁, f₁, μ; h, entry)` **minus the entry pattern**, which
is a separate parameter of every consuming statement rather than a field (see the SIGNATURE NOTE).

**SIGNATURE.**
```lean
namespace Uniformity.Density.Induction

/-- A **genre datum** `G = (Q; e₁, f₁, μ; h)`: the local invariants of a composite-stage opening
(`GENHN.CLASS`(i)). The residual factor `ψ` has degree `f₁` and multiplicity `μ`; the side carrying
it has slope `h / e₁` in lowest terms. -/
structure GenreDatum where
  /-- The ambient cluster's residue cardinality `Q = q ^ d`. -/
  Q : ℕ
  /-- The slope denominator; the stage's value-group index `E = e₁`. -/
  e₁ : ℕ
  /-- The residual factor's degree; the stage residue field is `F_(Q ^ f₁)`. -/
  f₁ : ℕ
  /-- The residual factor's multiplicity, `= the stage multiplicity`. -/
  μ : ℕ
  /-- The slope numerator. -/
  h : ℕ
  hQ : 2 ≤ Q
  he₁ : 1 ≤ e₁
  hh : 1 ≤ h
  hkey : 2 ≤ e₁ * f₁
  hmul : 2 ≤ μ
  hcop : Nat.Coprime h e₁
```

**⚠ SIGNATURE NOTE (why the entry pattern is NOT a field).** `GENHN.CLASS`(i) lists the entry
pattern inside `G`, and `GENHN.CLASS`(iii) says the stage system *"depends only on
`(Q, e₁, f₁, μ, h, stage window)`, NOT on `n` and not on the ambient frame: the ambient prices
exactly a FIBER"* (`EFF.GENHN.07`). The two are consistent: the entry pattern indexes the *fiber*,
not the stage system. Making it a field would put a chapter-C object (the frame grammar) inside a
chapter-H structure and would make `GenreDatum` non-`DecidableEq`. It is therefore carried as a
separate argument wherever a locus is priced (H.09's `entryCodim`, H.69's genre count).

**DEPENDS.** none.

**PROOF.** definitional.

**SIZE.** 22 lines.

**SOURCE.** `EFF.GENHN.07` (clause (i), the datum and its five side conditions, verbatim:
`gcd(h, e₁) = 1; e₁ ≥ 1`, `f₁ = deg ψ`, `μ ≥ 2`, `e₁f₁ ≥ 2` "else the event is order-1 α/β");
`EFF.GENIND.62` (the stage datum `(m′, D′, E, K)` with `D′ = e·d·deg ψ`, `E = e`,
`|K| = q^{d·deg ψ}`).

**TEETH.** `GN-CLASS` (`EFF.GENHN.07`, executable regression, 2,147,916 checks / 0 violations:
"every CS event at every depth of every row parses with `μ ≥ 2`, `e₁f₁ ≥ 2`, `4 ≤ e₁f₁μ ≤ 6`") →
**Lean theorem** at H.03 (the `4 ≤ e₁f₁μ` half becomes a theorem of this structure's fields); the
`μ ≥ 2`/`e₁f₁ ≥ 2` half is *definitional* here, so the battery row guards the *parser*, which is
outside chapter H.

**ENVIRONMENT.** ENV-H1.

---

### NODE H.02 [def] [fresh]

**STATEMENT.** *The derived stage data.* For a genre datum `G`: the **key degree**
`D′ = e₁ · f₁`; the **stage residue cardinality** `|K| = Q ^ f₁`; the **side length**
`L = e₁ · μ · f₁`; the **CS-defining product** `a = e₁ · f₁` (note `a = D′`; the corpus writes
`a = e·γ` with `γ = deg ψ = f₁`); and the **node height at coordinate `j < μ`**,
`nodeHeight j = (μ − j) · D′ · h + 1`.

**SIGNATURE.**
```lean
namespace Uniformity.Density.Induction

/-- `D′ = e₁ f₁`, the entry key's degree. -/
def GenreDatum.keyDeg (G : GenreDatum) : ℕ := G.e₁ * G.f₁

/-- `|K| = Q ^ f₁`, the stage residue cardinality. -/
def GenreDatum.stageCard (G : GenreDatum) : ℕ := G.Q ^ G.f₁

/-- `L = e₁ μ f₁`, the abscissa length the composite block occupies. -/
def GenreDatum.sideLen (G : GenreDatum) : ℕ := G.e₁ * G.μ * G.f₁

/-- The stage-initial node floor at coordinate `j`, in `dv`-units:
`dv(A_j) ≥ (μ − j) · D′ h + 1`.  This is the `[r1]`-CORRECTED floor of `GENHN.A`(i); the sealed
`(μ − j) · e₁ h + 1` is the `f₁ = 1` specialization (H.08). -/
def GenreDatum.nodeHeight (G : GenreDatum) (j : ℕ) : ℕ := (G.μ - j) * G.keyDeg * G.h + 1
```

**DEPENDS.** H.01.

**PROOF.** definitional.

**SIZE.** 14 lines.

**SOURCE.** `EFF.GENHN.07` (clause (i): "The key degree is `D′ = e₁f₁`; the stage residue field is
`K = F_{Q^{f₁}}`; the stage value normalization is `dv := e₁·v` … the stage multiplicity is `μ`");
`EFF.GENHN.08` (`GENHN.A`(i)'s node, **with** the `[r1]` correction verbatim: *"CORRECTED at
`f₁ ≥ 2` to `{dv(A_j) ≥ (μ−j)·D′h + 1}`, `D′h = f₁S` … the two agree exactly at `f₁ = 1`, which is
every battery row and every first-live case"*); `EFF.GENIND.197` (the C2-G1 definitions
`γ = deg ψ`, `a = eγ`, `L = eμγ`).

**⚠ TRANSCRIPTION FIDELITY (mandatory).** The `nodeHeight` field uses `D′h`, **not** `S = e₁h`.
`EFF.GENHN.23`(b) records the sealed `S`-node as **replaced**, and `EFF.GENHN.12`(b) records the
settlement: *"Every phrase "the `(2,K)`-cluster read at the `S`-node" is read count-side as "at the
`B = D′h`-node.""* A node written with `e₁ * h` in place of `keyDeg * h` is a **blueprint defect**
and must be returned, not silently accepted, even though the two agree at `f₁ = 1` (which is every
machine row in the corpus — precisely the coincidence-regime trap).

**TEETH.** `GN-T-NODE` (`EFF.GENHN.08`, planted mutant, fired 1/1: "E3 construction `a₀₀` floor
off-by-one must break the volume") → **executable regression** retained; this node is a definition
and carries no count of its own.

**ENVIRONMENT.** ENV-H1.

---

### NODE H.03 [lemma] [fresh]

**STATEMENT.** *CS necessity, the arithmetic half.* For every genre datum, `4 ≤ L`, i.e.
`4 ≤ e₁ · μ · f₁`.

**SIGNATURE.**
```lean
namespace Uniformity.Density.Induction

theorem GenreDatum.four_le_sideLen (G : GenreDatum) : 4 ≤ G.sideLen
```

**DEPENDS.** H.01, H.02.

**PROOF.**
1. unfold `sideLen`; the goal is `4 ≤ e₁ * μ * f₁`.
2. `have h1 : 2 ≤ e₁ * f₁ := G.hkey`; `have h2 : 2 ≤ μ := G.hmul`.
3. `calc 4 = 2 * 2 ≤ μ * (e₁ * f₁) := Nat.mul_le_mul h2 h1`.
4. `_ = e₁ * μ * f₁ := by ring`.

**SIZE.** 8 lines.

**SOURCE.** `EFF.GENIND.11` (§S5.1's *Necessity*, verbatim: *"The side's abscissa length is `e·g`
with `g ≥ μ·deg ψ`, so length `≥ e·μ·deg ψ ≥ 2·2·1 = 4` (case `e ≥ 2`, `ψ` linear) or
`≥ 1·2·2 = 4` (case `e = 1`, `deg ψ ≥ 2`) — in every case `≥ 4`"*); `EFF.GENIND.43` (the criterion
in one line).

**⚠ SCOPE FENCE.** This node proves the *arithmetic* half of necessity only. The step
"a CS event **is** a repeated residual factor `(ψ, μ)` with `μ ≥ 2` and `e·deg ψ ≥ 2` on a side of
the stage polygon", and the step "the polygon of a stage with `m` keys spans abscissas `[0, m]`, so
`m ≥ 4`", are **geometric** and have no node: they are the content of `GENIND-1(i)`'s partition
(honesty item H-3). H.04 supplies the enumeration; the passage from `4 ≤ L` to `m ≥ 4` to `n ≥ 4`
is H.04's third clause **under the explicit hypothesis** `L ≤ m` and `m * D ≤ n`.

**TEETH.** `GT-CRIT` (`EFF.GENIND.11`, executable regression + planted grammar-acceptance mutant,
§S11 P-8 "0/22", both directions: "every `n = 4/5` CS event (all depths) obeys `μ ≥ 2`, `e·γ ≥ 2`,
`4 ≤ e·μ·γ ≤ m_frame`") → **Lean theorem** (the `4 ≤ e·μ·γ` clause is exactly this node).
`GN-T-CRIT` (`EFF.GENHN.07`, planted mutant, fired 2/2: "grammar bound `e₁f₁μ ≥ 4` dropped to
`≥ 3` must accept an order-1 `(3)`-child fake") → **Lean theorem**, same reason.

**ENVIRONMENT.** ENV-H1.

---

### NODE H.04 [lemma] [fresh]

**STATEMENT.** *The composite-type enumeration and the degree threshold.* Three clauses.
(i) If `e₁ * f₁ = 2` then `(e₁, f₁) = (2, 1)` or `(e₁, f₁) = (1, 2)`.
(ii) If `e₁ * μ * f₁ = 4` with `2 ≤ μ` and `2 ≤ e₁ * f₁` then `(e₁, f₁, μ) = (2, 1, 2)` or
`(e₁, f₁, μ) = (1, 2, 2)` — **exactly two solutions**.
(iii) If `L ≤ m` and `m * D ≤ n` with `1 ≤ D` then `4 ≤ m` and `4 ≤ n`.

**SIGNATURE.**
```lean
namespace Uniformity.Density.Induction

theorem keyDeg_two_cases {e f : ℕ} (h : e * f = 2) : (e = 2 ∧ f = 1) ∨ (e = 1 ∧ f = 2)

theorem sideLen_four_cases {e f m : ℕ} (hm : 2 ≤ m) (hk : 2 ≤ e * f) (h : e * m * f = 4) :
    (e = 2 ∧ f = 1 ∧ m = 2) ∨ (e = 1 ∧ f = 2 ∧ m = 2)

theorem four_le_of_sideLen_le {G : GenreDatum} {m D n : ℕ} (hD : 1 ≤ D)
    (hLm : G.sideLen ≤ m) (hmn : m * D ≤ n) : 4 ≤ m ∧ 4 ≤ n
```

**DEPENDS.** H.03 (for clause (iii)'s `4 ≤ sideLen`).

**PROOF.**
1. (i) `interval_cases` on the divisors of `2`: from `e * f = 2`, `e ∣ 2` so `e ∈ {1, 2}`; in each
   case `f` is determined by `Nat.eq_of_mul_eq_mul_left`. Close by `omega` after `rcases`.
2. (ii) from `e * m * f = 4` and `2 ≤ m`, `m ∣ 4` and `m ≤ 4`, so `m ∈ {2, 4}`. If `m = 4` then
   `e * f = 1`, contradicting `2 ≤ e * f`. So `m = 2` and `e * f = 2`; apply (i).
3. (iii) `4 ≤ sideLen ≤ m` by H.03 and `hLm`; then `4 ≤ m ≤ m * D ≤ n` using `1 ≤ D`
   (`Nat.le_mul_of_pos_right`). `omega`.

**SIZE.** 18 lines.

**SOURCE.** `EFF.GENIND.32` (the enumeration verbatim: *"the two composite types are
`(e, deg ψ, μ) = (2, 1, 2)` and `(1, 2, 2)` — the only solutions of `e·μ·deg ψ = 4` with `μ ≥ 2` and
`e·deg ψ ≥ 2`"*, with the spec's own ARITHMETIC AUDIT: *"Factorizations of 4 with `μ ≥ 2`:
`(μ, e·deg ψ) ∈ {(2,2), (4,1)}`; `(4,1)` fails `e·deg ψ ≥ 2`"*); `EFF.GENIND.11` (the degree
threshold); `EFF.GENIND.43`.

**ARITHMETIC AUDIT (recomputed fresh, and at more than one `q` where a `q` occurs).** Clause (ii)
has no `q`. The two solutions are the corpus's two quartic genres: `(2,1,2)` is genre E
(`e₁ = 2`, `f₁ = 1`, `|K| = Q`) and `(1,2,2)` is genre F (`e₁ = 1`, `f₁ = 2`, `|K| = Q²`) —
`EFF.GENH4.06`. Cross-check of `sideLen`: E gives `2·2·1 = 4` ✓, F gives `1·2·2 = 4` ✓, and both
saturate the `n = 4` abscissa budget ✓. The `n = 6` genres of `EFF.GENHN.20` give
`sideLen = 6` in all four cases: `E3 = (2,1,3) → 2·3·1 = 6` ✓, `E31 = (3,1,2) → 3·2·1 = 6` ✓,
`F3 = (1,2,3) → 1·3·2 = 6` ✓, `E13 = (1,3,2) → 1·2·3 = 6` ✓ — so the grammar bound
`4 ≤ e₁f₁μ ≤ 6` covers exactly the `n ≤ 6` genres ✓, as `EFF.GENHN.20`'s audit records.

**TEETH.** as H.03 (`GT-CRIT`, `GN-T-CRIT`) → **Lean theorem**; additionally `GT-CRIT`'s negative
half ("ZERO CS events on all four `n = 3` control rows") is the contrapositive of clause (iii) →
**Lean theorem**.

**ENVIRONMENT.** ENV-H1.

---

### NODE H.05 [theorem] [fresh]

**STATEMENT.** *Genre SCHEMA finiteness (the corrected clause (ii)).* For every `n`, the set of
**schemas** `{(e, f, m) : 2 ≤ e * f ∧ 2 ≤ m ∧ e * m * f ≤ n}` is finite, and its cardinality is at
most `n ^ 3`.

**SIGNATURE.**
```lean
namespace Uniformity.Density.Induction

/-- The schema set at degree `n`: the triples `(e₁, f₁, μ)` a degree-`n` read can realize. -/
def schemaSet (n : ℕ) : Set (ℕ × ℕ × ℕ) :=
  {p | 2 ≤ p.1 * p.2.1 ∧ 2 ≤ p.2.2 ∧ p.1 * p.2.2 * p.2.1 ≤ n}

theorem finite_schemaSet (n : ℕ) : (schemaSet n).Finite

theorem card_schemaSet_le (n : ℕ) : Nat.card (schemaSet n) ≤ n ^ 3
```

**DEPENDS.** none (a standalone finiteness statement; H.01 is not needed because the set is stated
over raw triples, which is what makes it a *schema* set rather than a datum set).

**PROOF.**
1. every member has `p.1 ≤ n`, `p.2.1 ≤ n`, `p.2.2 ≤ n`: from `p.1 * p.2.2 * p.2.1 ≤ n` together
   with `1 ≤ p.1`, `1 ≤ p.2.1` (both from `2 ≤ p.1 * p.2.1` via `Nat.pos_of_ne_zero`) and
   `2 ≤ p.2.2`. Each bound is `Nat.le_of_dvd`-free: `p.1 ≤ p.1 * p.2.2 * p.2.1` by
   `Nat.le_mul_of_pos_right` twice.
2. hence `schemaSet n ⊆ Set.Iic n ×ˢ Set.Iic n ×ˢ Set.Iic n`, a finite set
   (`Set.Finite.prod`, `Set.finite_Iic`).
3. `finite_schemaSet := (h.subset ...)` where `h` is that product's finiteness.
4. `card_schemaSet_le`: `Nat.card_le_card_of_injOn` into `Fin (n+1) × Fin (n+1) × Fin (n+1)`, or
   more cheaply `Nat.card_le_card_of_subset` against the product and
   `Nat.card_prod`; then `(n+1)^3` — **the stated bound `n ^ 3` needs the sharper count**: at least
   one factor is `≥ 2`, so no coordinate is `0`, and each ranges in `[1, n]`, giving `n ^ 3`. Use
   `Set.Iic`-to-`Set.Icc 1 n` refinement in step 1.

**SIZE.** 24 lines. **SPLIT CANDIDATE:** if the `Set.Finite` plumbing fights, land
`finite_schemaSet` as H.05 and `card_schemaSet_le` as a separate node — the cardinality bound is
consumed only by H.69's genre count and is not on the critical path.

**SOURCE.** `EFF.GENHN.07` clause (ii) **as re-displayed by the owner directive** (verbatim):
*"at fixed `n`, the genres form FINITELY MANY PARAMETERIZED GENRE SCHEMAS — the triples
`(e₁, f₁, μ)` with `e₁f₁ ≥ 2`, `e₁f₁μ ≤ n`, each carrying finitely many `(A1)`-admissible
entry-pattern families — with the residue field `Q`, the slope numerator `h` (`gcd(h, e₁) = 1`),
the window `N`, and the prehistory depths as the schemas' parameters"*; the sealed clause's own
bound `#{(a, b, μ): ab ≥ 2, μ ≥ 2, abμ ≤ n} < ∞`.

**⚠ THE ENTRY-PATTERN CLAUSE IS NOT PROVED HERE.** The re-display's second half — *"each carrying
finitely many `(A1)`-admissible entry-pattern families"* — rests on `W-12.A`'s depth-0 polygon
families plus the α/β prefix grammar, closed by `LEMMA GENIND-0`. Chapter H proves the `GENIND-0`
closure (H.94) but **not** the finiteness of the frame-shape families, which is `W12` content
(honesty item H-12). This node's statement is therefore exactly the triple count, which is what the
consumers (H.69) need.

**TEETH.** `GN-CLASS`'s grammar bound (`4 ≤ e₁f₁μ ≤ 6` at `n ≤ 6`) → **Lean theorem** (H.03/H.04
give the lower bound, this node the finiteness); the **finiteness defect itself was found by a
`decorrelated-model audit`, not by any tooth** (`EFF.GENHN.07`: *"no battery row could see it,
because the battery sweeps fixed `(q, N, h)` and the counterexample is a family over `h`"*) — which
is why H.06 exists.

**ENVIRONMENT.** ENV-H1.

---

### NODE H.06 [theorem] [fresh]

**STATEMENT.** *The A2 refutation, as a theorem: the DATUM set is infinite.* Fix `Q = 2` and the
schema `(e₁, f₁, μ) = (2, 1, 2)` (genre E at `n = 4`). The set of genre data with those values and
`h` odd is infinite. Concretely: the map `t ↦ ⟨2, 2, 1, 2, 2*t+1, …⟩` from `ℕ` to `GenreDatum` is
injective, so `Set.Infinite {G : GenreDatum | G.Q = 2 ∧ G.e₁ = 2 ∧ G.f₁ = 1 ∧ G.μ = 2}`.

**SIGNATURE.**
```lean
namespace Uniformity.Density.Induction

/-- The genre-E datum at `Q = 2` with slope numerator `2t+1`. -/
def genreE2 (t : ℕ) : GenreDatum where
  Q := 2; e₁ := 2; f₁ := 1; μ := 2; h := 2 * t + 1
  hQ := le_refl 2
  he₁ := by omega
  hh := by omega
  hkey := by omega
  hmul := le_refl 2
  hcop := by simpa using Nat.coprime_two_right_iff_odd.2 ⟨t, by ring⟩

theorem genreE2_injective : Function.Injective genreE2

theorem infinite_genreDatum_of_schema :
    {G : GenreDatum | G.Q = 2 ∧ G.e₁ = 2 ∧ G.f₁ = 1 ∧ G.μ = 2}.Infinite
```

**DEPENDS.** H.01.

**PROOF.**
1. `genreE2_injective`: if `genreE2 s = genreE2 t` then comparing the `h` fields gives
   `2*s+1 = 2*t+1`, so `s = t` by `omega`. (Structure-eta: use `GenreDatum.mk.injEq` or
   `congrArg GenreDatum.h`.)
2. `infinite_genreDatum_of_schema`: `Set.infinite_of_injective_forall_mem genreE2_injective`, the
   membership being four `rfl`s.
3. the `hcop` field: `Nat.Coprime (2*t+1) 2` ⟺ `2*t+1` is odd; `Nat.coprime_two_right_iff_odd`.

**SIZE.** 20 lines.

**SOURCE.** `EFF.GENHN.07`, the A2 adjudication transcribed verbatim: *"GENHN.CLASS explicitly
includes `Q` and `h` in `G`, while its finiteness proof counts only discrete schemas
`(e_1,f_1,μ,entry-family)`. For fixed `n=4, Q=2`, every positive odd `h` gives a distinct datum
`(2; 2,1,2; h, entry)` once `N ≥ 2h+1`. Thus the declared data set is infinite."*

**⚠ WHY THIS NODE EXISTS.** The corrected scope of `GENHN.CLASS`(ii) is only *checkable* if both
halves are landed: finitely many schemas (H.05) and infinitely many data (this node). Landing only
H.05 would leave the reader unable to tell the corrected clause from the refuted one. `EFF.GENHN.07`
records that the owner directive's re-display *"is subject to sol discharge-confirmation in the
cert2 pass"* — an OPEN-CALL; this node is the Lean-side confirmation of the refutation half, and it
is unconditional.

**TEETH.** `decorrelated-model audit` (the finding's own disposition) → **Lean theorem**. No
battery row can produce this and the spec says so; the node converts a fresh-model finding into a
machine-checked one.

**ENVIRONMENT.** ENV-H1.

---

### NODE H.07 [def] [fresh]

**STATEMENT.** *Occupied heights.* For a genre datum `G` and `m : ℕ`, say `m` is **occupied** when
there exist `i < e₁` and `a : ℕ` with `i * h + e₁ * a = m` — i.e. the normalizer monomial
`n(m) = x^i π^a` exists **with `a` a natural number** (integrality is the content).

**SIGNATURE.**
```lean
namespace Uniformity.Density.Induction

/-- `G.Occupied m`: the `dv`-height `m` admits an INTEGRAL normalizer monomial
`n(m) = x^{i} π^{a}` with `0 ≤ i < e₁` and `a ≥ 0`.  This is the TERMINAL scope word of
`GENHN.A`(ii) after the post-D2b corrigendum. -/
def GenreDatum.Occupied (G : GenreDatum) (m : ℕ) : Prop :=
  ∃ i a : ℕ, i < G.e₁ ∧ i * G.h + G.e₁ * a = m
```

**DEPENDS.** H.01.

**PROOF.** definitional.

**SIZE.** 8 lines.

**SOURCE.** `EFF.GENHN.28` (the normalizer: *"for each `dv`-height `m` pick
`n(m) := x^{i(m)}π^{a(m)}` with `i(m)·h + e₁·a(m) = m`, `0 ≤ i(m) < e₁`"*, and the spec's own
observation that this *"presumes `a(m) ≥ 0`, which fails at unoccupied heights"*);
`EFF.GENHN.09`, the owner re-display: *"per OCCUPIED integer dv-height — a height `m` admitting an
integral normalizer monomial `n(m) = x^{i(m)}π^{a(m)}` with `0 ≤ i(m) < e₁` and
`a(m) = (m − i(m)h)/e₁ ≥ 0`"*.

**TEETH.** none (a definition; guarded through H.10–H.12).

**ENVIRONMENT.** ENV-H1.

---

### NODE H.08 [lemma] [fresh]

**STATEMENT.** *The node floor lies strictly above `D′h`, and coincides with the sealed `S`-node at
`f₁ = 1`.* Two clauses. (i) For every `j < μ`, `G.keyDeg * G.h < G.nodeHeight j`. (ii) If `f₁ = 1`
then `G.nodeHeight j = (μ − j) * e₁ * h + 1` — the sealed `S = e₁h` form.

**SIGNATURE.**
```lean
namespace Uniformity.Density.Induction

theorem GenreDatum.keyDeg_mul_h_lt_nodeHeight (G : GenreDatum) {j : ℕ} (hj : j < G.μ) :
    G.keyDeg * G.h < G.nodeHeight j

theorem GenreDatum.nodeHeight_of_f_one (G : GenreDatum) (hf : G.f₁ = 1) (j : ℕ) :
    G.nodeHeight j = (G.μ - j) * G.e₁ * G.h + 1
```

**DEPENDS.** H.01, H.02.

**PROOF.**
1. (i) unfold `nodeHeight`; `1 ≤ μ - j` from `hj`, so
   `keyDeg * h ≤ (μ - j) * keyDeg * h < (μ - j) * keyDeg * h + 1`. `Nat.le_mul_of_pos_left` then
   `omega`.
2. (ii) unfold `nodeHeight`, `keyDeg`; rewrite `hf`; `simp [Nat.mul_one]`.

**SIZE.** 10 lines.

**SOURCE.** `EFF.GENHN.09`'s protection sentence, verbatim: *"every pin the note's laws consume sits
in that domain (the stage-initial node floor `{dv(A_j) ≥ (μ−j)D′h + 1}` and the refine floors)"* —
i.e. clause (i) is exactly why the terminal `D′h < m` scope of the slot clause suffices for every
consumer. `EFF.GENHN.08`'s `[r1]` bracket for clause (ii): *"the two agree exactly at `f₁ = 1`,
which is every battery row and every first-live case"*.

**⚠ WHY (ii) IS STATED AT ALL.** Because it is the *coincidence* that hid the defect. Every machine
row of `EFF.GENHN` has `f₁ = 1`, so no run could distinguish `S`-node from `D′h`-node; landing (ii)
as a theorem makes the coincidence explicit and prevents a future node from "simplifying"
`keyDeg * h` to `e₁ * h`. Same discipline as H.02's transcription-fidelity note; same trap as the
G.23 refutation (checks at `q = 2` only) and as HE6's F-1.

**TEETH.** `GN-T-NODE` (planted mutant, fired 1/1) → **Lean theorem** for clause (i).

**ENVIRONMENT.** ENV-H1.

---

### NODE H.09 [def] [fresh]

**STATEMENT.** *The stage interface — `(CS-1Q)` + `(CS-2)` + `(CS-3)` as fields.* A
**stage interface** over a genre datum `G`, at ambient window `N` and entry height `H`, consists of:
a uniform stage window `stageWindow : ℕ`; a total loss `stageLoss : ℕ` (the corpus's
`Δ_G = λ_G + r_G`); an entry codimension `entryCodim : ℕ` (the corpus's `C_G^{extra}`); a slack
constant `slack : ℕ` (the corpus's `O_G(1)`); a stage bracket `bracket : ℕ → ℕ`; a stage drain
fraction `drainFrac : ℕ → ℝ`; a σ-assignment `stageSigma : FactorizationType`; subject to
(i) **`(CS-1Q.a)`** `e₁ * (N − 1 − H) ≤ stageWindow + stageLoss`;
(ii) **`(CS-1Q.b)`** `f₁ * stageLoss ≤ entryCodim + (S + 1 − 2*keyDeg − 1)/2 * H + slack`, stated
subtraction-free as `2 * (f₁ * stageLoss) ≤ 2 * entryCodim + (S − 2 * keyDeg) * H + 2 * slack`
where `S ≥ L` is the actual side length;
(iii) **`(CS-2)`** `bracket κ * stageCard = (stageCard − 1) * stageCard ^ ((c(μ)+1) * κ)` for
`1 ≤ κ`;
(iv) **`(CS-EXACT)`** `∃ terms : Finset (ℕ × ℕ), drainFrac M = Σ …` — the drain is a finite sum of
signed `q`-powers (stated as: `drainFrac` takes values in the subring generated by `Q`-powers);
(v) **`(CS-3)`** `stageSigma.degree = 2 * keyDeg` when `μ = 2` (the leaf dictionary's degree
consistency — the only part of `(CS-3)` that is not open).

**SIGNATURE.**
```lean
namespace Uniformity.Density.Induction

/-- **The stage interface.** Every field is a clause of `[GENIND-H]` in its TERMINAL wording:
`(CS-1Q.a)`/`(CS-1Q.b)` (ledger `HYP.36`, disposition CARRY), `(CS-2)` (the stage bracket, in the
MASS normalization), `(CS-EXACT)`, and the degree-consistency half of `(CS-3)`.  **Nothing in this
structure is proved by chapter H**; the chapter proves the count and rate theorems of §10 FROM these
fields. -/
structure StageInterface (G : GenreDatum) (N H S : ℕ) where
  /-- The common uniform stage window `M_G`. -/
  stageWindow : ℕ
  /-- `Δ_G = λ_G + r_G`: the sibling-Hensel loss plus the ragged truncation loss. -/
  stageLoss : ℕ
  /-- `C_G^{extra}`: the entry codimension beyond the supporting-line price. -/
  entryCodim : ℕ
  /-- `O_G(1)`: the genre-local slack. -/
  slack : ℕ
  /-- The stage's own α-aggregation bracket, per stage-slope-sum `κ`. -/
  bracket : ℕ → ℕ
  /-- The stage's conservative-drain fraction at stage window `M`. -/
  drainFrac : ℕ → ℝ
  /-- The σ-multiset the stage's decided leaves carry. -/
  stageSigma : FactorizationType
  /-- The actual side length dominates the block's own length. -/
  hS : G.sideLen ≤ S
  /-- **(CS-1Q.a)** — the ragged/loss-corrected stage-window supply. -/
  hwin : G.e₁ * (N - 1 - H) ≤ stageWindow + stageLoss
  /-- **(CS-1Q.b)** — every lost `K`-digit is paid by entry codimension or supporting-line slack. -/
  hprice : 2 * (G.f₁ * stageLoss) ≤ 2 * entryCodim + (S - 2 * G.keyDeg) * H + 2 * slack
  /-- **(CS-2)** — the stage bracket is `GENIND-2(b)` inside the stage, MASS-normalized. -/
  hbracket : ∀ κ, 1 ≤ κ →
    bracket κ * G.stageCard = (G.stageCard - 1) * G.stageCard ^ ((clusterC G.μ + 1) * κ)
  /-- The drain fraction is a genuine fraction. -/
  hdrain_nonneg : ∀ M, 0 ≤ drainFrac M
  hdrain_le_one : ∀ M, drainFrac M ≤ 1
  /-- **(CS-3)**, degree half — at `μ = 2` the leaf dictionary exhausts the block degree. -/
  hsigma : G.μ = 2 → stageSigma.degree = 2 * G.keyDeg
```

**⚠ SIGNATURE NOTE (hypothesis strength at its true minimum — the G.28 lesson).** Three deliberate
weakenings against the corpus's displayed forms, each because the chapter's proofs use no more:

* `hwin` is `(CS-1Q.a)`, **not** the withdrawn scalar bound `M★ ≥ e(N−1−H)`. `EFF.GENIND.196`
  withdraws the scalar bound *"for general embedded and mixed genres"*; a `StageInterface` field
  stating it would be unsatisfiable there. At `stageLoss = 0` the field degenerates to the scalar
  bound, which is exactly the two standalone quartic genres (`EFF.GENIND.199`).
* `hprice` is stated with `2 *` throughout because `b_S = (S+1)/2` is a half-integer and `ℕ`
  division would silently floor it. The `(S − 2 * keyDeg)` factor is `2*(b_S − a − 1/2)`, which
  H.33 proves is a genuine `ℕ` (i.e. `2 * keyDeg ≤ S`), so no truncation occurs.
* `hdrain_*` replace the corpus's `(CS-EXACT)` **for the rate consumers only**. `EFF.GENIND.170`
  (R6.2) is the licence: *"(CS-EXACT) is required because the induction propagates the
  exact-complement IDENTITY … NOT because bounds fail to propagate: upper bounds propagate by
  monotonicity + union bound"*. Chapter H's rate theorems (H.67, H.68, H.72) are bound-direction
  only, so they need `0 ≤ drainFrac ≤ 1` and nothing more. **A node that needs the exactness
  identity must return `RE-PLAN` for an `exactDrain` field, not assume it.**

**DEPENDS.** H.01, H.02, H.13 (`clusterC`) · landed `Uniformity.FactorizationType`,
`FactorizationType.degree`.

**PROOF.** definitional.

**SIZE.** 40 lines. At the contract ceiling; if the elaborator objects to the `2 *`-scaled `hprice`,
split the structure into `StageWindow` (fields 1–4 + `hS`/`hwin`/`hprice`) and `StageLaw` (the rest)
and land two nodes — the consumers in §10 take them separately anyway.

**SOURCE.** `EFF.GENIND.197` (the `(CS-1Q.a)`/`(CS-1Q.b)` display, LaTeX tags `\tag{CS-1Q.a}` /
`\tag{CS-1Q.b}`, with the five defined quantities `λ_G`, `r_G`, `Δ_G`, `M_G`, `C_G^{extra}` and
`b_S := (S+1)/2`); `EFF.GENIND.64` (`(CS-2)`, **with its NORMALIZATION DECLARED**: *"this bracket
is MASS-NORMALIZED — it includes the ghost fibers `|K|^{c(m′)·k_i}` … A discharge of `(CS-2)` must
therefore be read in THIS (mass) normalization, or composed with its ghost fiber"*);
`EFF.GENIND.66` (`(CS-EXACT)`); `EFF.GENIND.65` (`(CS-3)`); `EFF.GENHN.12` (`GENHN.A`(v), the
stage bracket in stage `dv`-slope units).

**⚠ THE NORMALIZATION IS LOAD-BEARING.** `hbracket` is stated in the **mass** normalization
(`(|K|−1)|K|^{(c(μ)+1)κ−1}`), not the letter-sum (`(|K|−1)|K|^{κ−1}`). `EFF.GENIND.64`: the two
differ by exactly the ghost `|K|^{c(μ)κ}`, *"invisible at genre E and visible at genre F"*. H.42's
genre-F instance is the node where a wrong normalization would surface; H.21's audit reproduces the
reconciliation `16 · 12 = 192`.

**TEETH.** `(CS-1)`/`(CS-1Q)` and `(CS-3)`: **NONE, at any degree, anywhere in the corpus** —
`signed vacuity disclosure` (`EFF.GENIND.63`, `.65`, `.197`). `(CS-2)`: the in-line numeric
certificate of `EFF.GENIND.64` → **Lean theorem** at H.21 (which recomputes all five of its
identities). This node's honest disposition: **the fields with no teeth are exactly the capstone's
conditionality**, and §16's disposition table lists them as such.

**ENVIRONMENT.** ENV-H1.

---

### NODE H.10 [lemma] [fresh]

**STATEMENT.** *Every height above `D′h` is occupied.* For a genre datum `G` and `m : ℕ` with
`G.keyDeg * G.h < m`, `G.Occupied m` holds. (Consequently every node floor `G.nodeHeight j`,
`j < μ`, is occupied — by H.08(i).)

**SIGNATURE.**
```lean
namespace Uniformity.Density.Induction

theorem GenreDatum.occupied_of_keyDeg_mul_h_lt (G : GenreDatum) {m : ℕ}
    (hm : G.keyDeg * G.h < m) : G.Occupied m

theorem GenreDatum.occupied_nodeHeight (G : GenreDatum) {j : ℕ} (hj : j < G.μ) :
    G.Occupied (G.nodeHeight j)
```

**DEPENDS.** H.01, H.02, H.07, H.08.

**PROOF.**
1. set `i := (m * (h⁻¹ mod e₁)) % e₁` — concretely: since `Nat.Coprime h e₁`, `h` is invertible
   mod `e₁`, so choose `i < e₁` with `i * h ≡ m [MOD e₁]` (`ZMod e₁` and
   `Nat.Coprime.isUnit_of_...`; or directly `Nat.chineseRemainder`-free via
   `(ZMod.unitOfCoprime h G.hcop)⁻¹ * (m : ZMod e₁)` and `ZMod.val_lt`).
2. from `i * h ≡ m [MOD e₁]` and `i * h ≤ (e₁ − 1) * h ≤ keyDeg * h < m` (using `f₁ ≥ 1`, so
   `e₁ ≤ keyDeg`), get `i * h ≤ m` and `e₁ ∣ m − i * h`.
3. set `a := (m − i * h) / e₁`; then `i * h + e₁ * a = m` by `Nat.div_mul_cancel` on the
   divisibility of step 2. `exact ⟨i, a, hi, this⟩`.
4. `occupied_nodeHeight` := `occupied_of_keyDeg_mul_h_lt (H.08(i) hj)`.

**SIZE.** 22 lines. The `ZMod e₁` inverse step is the only non-`omega` content; the `e₁ = 1` case
is degenerate (`i = 0`, `a = m`) and should be split off first by `rcases Nat.lt_or_ge e₁ 2`.

**SOURCE.** `EFF.GENHN.81` (`LEMMA GENHN-LIFT`'s hypothesis and its integrality step, verbatim:
*"Let `M > D'h = e_1f_1h`, and let `i = i(M)`, `0 ≤ i < e_1`, be determined by
`ih ≡ M (mod e_1)`, `a = (M − ih)/e_1`"* and *"Since `i + e_1s ≤ D'−1` and `M > D'h`,
`a − sh = (M − (i+e_1s)h)/e_1 ≥ 0`"*); `EFF.GENHN.09` (the owner re-display's clause: *"Every height
`m > D′h` is occupied, with the explicit lift supplied by `LEMMA GENHN-LIFT`"*).

**ARITHMETIC AUDIT (recomputed fresh).** The chain `e₁ ≤ keyDeg = e₁ * f₁` needs `1 ≤ f₁`, which
follows from `2 ≤ e₁ * f₁` ✓. Then `i * h ≤ (e₁ − 1) * h < e₁ * h ≤ keyDeg * h < m` ✓. At the two
first-live genres: E `(e₁,f₁,h) = (2,1,1)` gives `keyDeg * h = 2`, so every `m ≥ 3` is occupied, and
the node floors are `nodeHeight 0 = 2·2·1+1 = 5`, `nodeHeight 1 = 1·2·1+1 = 3` ✓ both `> 2`. F
`(1,2,1)` gives `keyDeg * h = 2` and floors `2·2·1+1 = 5`, `3` ✓. E31 `(3,1,1)` gives
`keyDeg * h = 3` and floors `2·3·1+1 = 7`, `4` ✓ — all above, as `EFF.GENHN.09` claims.

**TEETH.** **PROOF-ONLY at the corrected scope** (`EFF.GENHN.09`: *"No battery row exercises an
unoccupied height: every row has `f₁ = 1` and every consumed pin sits at `dv > D′h`"*). Disposition:
`decorrelated-model audit` for the *scope*, **Lean theorem** for the lemma.

**ENVIRONMENT.** ENV-H1.

---

### NODE H.11 [lemma] [fresh]

**STATEMENT.** *The R4/A2 witness: an UNOCCUPIED height.* For the genre datum
`(Q, e₁, f₁, μ, h) = (2, 3, 1, 2, 2)`, the height `m = 1` is **not** occupied. (Hence the sealed
universal "one `K`-digit slot per **integer** `dv`-height" is false, and `D′h = 3 > 1` shows the
witness sits below the terminal scope of H.10.)

**SIGNATURE.**
```lean
namespace Uniformity.Density.Induction

/-- The A2/R4 witness datum `(Q; e₁, f₁, μ; h) = (2; 3, 1, 2; 2)`. -/
def genreA2witness : GenreDatum where
  Q := 2; e₁ := 3; f₁ := 1; μ := 2; h := 2
  hQ := le_refl 2
  he₁ := by omega
  hh := by omega
  hkey := by omega
  hmul := le_refl 2
  hcop := by decide

theorem not_occupied_genreA2witness : ¬ genreA2witness.Occupied 1
```

**DEPENDS.** H.01, H.07.

**PROOF.**
1. `intro ⟨i, a, hi, ha⟩`; `hi : i < 3` and `ha : i * 2 + 3 * a = 1`.
2. `interval_cases i` (three cases) then `omega` on each: `i = 0` gives `3a = 1`, impossible;
   `i = 1` gives `3a = −1` (in `ℕ`: `2 + 3a = 1`), impossible; `i = 2` gives `4 + 3a = 1`,
   impossible.
3. Alternatively the whole statement is `by decide` after bounding `a ≤ 1`.

**SIZE.** 14 lines.

**SOURCE.** `EFF.GENHN.09`, the A2 obstruction record transcribed verbatim: *"The counterexample is
correct. For `(e_1,f_1,h,m)=(3,1,2,1)`, the unique normalizer exponent is `a=-1`, so neither an
integral normalizer nor a variable `K`-slot exists at height `1`. … the displayed universal
assertion "one `K`-digit slot per integer `dv`-height" is false. … no admissible repair can be
supplied under the stated constraint."*

**ARITHMETIC AUDIT.** The corpus says the unique exponent is `a = −1`: solving `i·h + e₁·a = m`
with `h = 2`, `e₁ = 3`, `m = 1` and `0 ≤ i < 3` gives `i = 2, a = (1−4)/3 = −1` ✓ — the only `i`
with `2i ≡ 1 (mod 3)` is `i = 2` ✓ (`2·2 = 4 ≡ 1`) ✓. `D′h = 3·1·2 = 6 > 1` ✓, so the witness is
strictly inside the withdrawn region, consistent with H.10.

**⚠ WHY THIS NODE EXISTS.** Same reason as H.06: a withdrawn universal is only *checkable* if its
counterexample is landed. `EFF.GENHN.09`'s TEETH field is explicit that no battery row could produce
it. **The node must not be "generalized"** — a fleet agent tempted to state "no `m ≤ D′h` is
occupied" would be wrong (`m = 0` is occupied with `i = a = 0`, and `m = 2` is occupied at this
datum with `i = 1, a = 0`); the statement is a single witness and stays one.

**TEETH.** `decorrelated-model audit` → **Lean theorem**.

**ENVIRONMENT.** ENV-H1.

---

### NODE H.12 [lemma] [fresh]

**STATEMENT.** *The D2b witness: an OCCUPIED height whose `K`-slot is nevertheless PARTIAL.* For
the genre datum `(Q, e₁, f₁, μ, h) = (2, 1, 2, 2, 1)`, the height `m = 0` **is** occupied (`i = 0`,
`a = 0`, `n(0) = 1`), yet `m = 0` fails `G.keyDeg * G.h < m` (indeed `keyDeg * h = 2 > 0`). Hence
the *occupied*-height re-display of `GENHN.A`(ii) is strictly weaker than the terminal `D′h < m`
scope, and the terminal scope is the one chapter H uses.

**SIGNATURE.**
```lean
namespace Uniformity.Density.Induction

/-- The post-D2b witness datum `(Q; e₁, f₁, μ; h) = (2; 1, 2, 2; 1)`. -/
def genreD2bwitness : GenreDatum where
  Q := 2; e₁ := 1; f₁ := 2; μ := 2; h := 1
  hQ := le_refl 2
  he₁ := le_refl 1
  hh := le_refl 1
  hkey := by omega
  hmul := le_refl 2
  hcop := by decide

theorem occupied_zero_genreD2bwitness : genreD2bwitness.Occupied 0

theorem not_keyDeg_mul_h_lt_zero_genreD2bwitness :
    ¬ (genreD2bwitness.keyDeg * genreD2bwitness.h < 0)
```

**DEPENDS.** H.01, H.02, H.07.

**PROOF.**
1. `occupied_zero`: `exact ⟨0, 0, by omega, by omega⟩`.
2. `not_keyDeg_mul_h_lt_zero`: `simp [GenreDatum.keyDeg, genreD2bwitness]` then `omega` — the goal
   reduces to `¬ (2 < 0)`.

**SIZE.** 12 lines.

**SOURCE.** `EFF.GENHN.09`, the post-D2b corrigendum transcribed verbatim: *"the re-display at
step 3 is itself **too weak at `f₁ > 1`**: "sol's witness `(e₁, f₁, h, m) = (1, 2, 1, 0)`: `n(0) = 1`
is integral while the η-component would require `xπ^{−1}`". Final scope: "GENHN.A(ii)'s slot clause
holds per integer `dv`-height `m` with **`D′h < m`**, below the window cap … At `m ≤ D′h` the clause
is withdrawn entirely: a `K`-slot may be partial (the sol witness) or absent (the R4/A2
witness)."*

**⚠ WHAT THIS NODE DOES AND DOES NOT SAY.** It does **not** formalize "the `η`-component requires
`xπ^{−1}`" — that is a statement about the stage lift's components and belongs to H.54–H.56, where
`stageLift` is only defined for `M > D′h` and therefore *cannot* be applied at `m = 0`. What this
node lands is the **separation of the two scopes**: occupied ⊉ terminal. That is the checkable
content and it is what protects every downstream consumer from re-widening the clause. **Do not
strengthen this node into a claim about partial slots.**

**TEETH.** `decorrelated-model audit` (the D2b pass) → **Lean theorem** for the scope separation;
the partial-slot content itself is `signed non-applicability` here (no chapter-H node consumes it).

**ENVIRONMENT.** ENV-H1.

---

## 4. §4 — ARITHMETIC I: THE α SPECIES

> Every node of §§4–7 is `ENV-H1` and consumes **no `O`**. They are the corpus's count laws with the
> geometry stripped: the corpus derives an exponent from a polygon, chapter H proves the exponent
> identity. Each count-formula node carries an **ARITHMETIC AUDIT recomputed at `q = 2` AND at
> `q = 3`** (the G.23 lesson: `q = 2`-only checks hide factors — there, a stabilizer of order 2).

### NODE H.13 [def] [fresh]

**STATEMENT.** `clusterC m = m(m−1)/2`, the corpus's `c(m)`, defined as `Nat.choose m 2`.

**SIGNATURE.**
```lean
namespace Uniformity.Density.Induction

/-- `c(m) = m(m−1)/2`, the α-bracket's exponent coefficient offset (`GENIND` §S1). Defined as
`m.choose 2` so that `2 * clusterC m = m * (m − 1)` is exact in `ℕ` with no floor. -/
def clusterC (m : ℕ) : ℕ := m.choose 2
```

**DEPENDS.** none.

**PROOF.** definitional.

**SIZE.** 4 lines.

**SOURCE.** `EFF.GENIND.07` (*"Write `c(m) := m(m−1)/2`"*).

**⚠ WHY `Nat.choose` AND NOT `m * (m-1) / 2`.** `ℕ` division floors, and `m * (m-1)` is always even,
so the two agree — but only *provably* via `Nat.choose_two_right`. Using `choose` makes
`two_mul_clusterC` (H.14) a mathlib rewrite rather than a parity argument, and makes
`Finset.sum_range_id`-style identities available for H.15.

**TEETH.** none (a definition).

**ENVIRONMENT.** ENV-H1.

---

### NODE H.14 [lemma] [fresh]

**STATEMENT.** Three clauses. (i) `2 * clusterC m = m * (m − 1)`. (ii) `clusterC m = Σ_{j<m} j`.
(iii) the exponent-coefficient instances: `clusterC 2 + 1 = 2`, `clusterC 3 + 1 = 4`,
`clusterC 4 + 1 = 7`, `clusterC 5 + 1 = 11`.

**SIGNATURE.**
```lean
namespace Uniformity.Density.Induction

theorem two_mul_clusterC (m : ℕ) : 2 * clusterC m = m * (m - 1)

theorem clusterC_eq_sum (m : ℕ) : clusterC m = ∑ j ∈ Finset.range m, j

theorem clusterC_succ_values :
    clusterC 2 + 1 = 2 ∧ clusterC 3 + 1 = 4 ∧ clusterC 4 + 1 = 7 ∧ clusterC 5 + 1 = 11
```

**DEPENDS.** H.13.

**PROOF.**
1. (i) `Nat.choose_two_right : n.choose 2 = n * (n - 1) / 2`; then `Nat.two_mul_div_two_of_even`
   with `Nat.even_mul_pred_self`.
2. (ii) `Finset.sum_range_id_mul_two` gives `2 * Σ_{j<m} j = m * (m-1)`; combine with (i) and
   cancel by `Nat.eq_of_mul_eq_mul_left`.
3. (iii) `by decide` (or `norm_num [clusterC, Nat.choose]`).

**SIZE.** 12 lines.

**SOURCE.** `EFF.GENIND.09` (*"exponent coefficient `c(m)+1 = m(m−1)/2 + 1` (= 2, 4, 7, 11 at
`m = 2, 3, 4, 5`)"*); `EFF.GENIND.23` (the instance display, with the spec's own ARITHMETIC AUDIT
*"`1+1 = 2` ✓, `3+1 = 4` ✓, `6+1 = 7` ✓, `10+1 = 11` ✓"* and the tie to §S11 P-7's scored tuple
`(exponent coefficients 2/4/7/11)`).

**ARITHMETIC AUDIT (recomputed fresh).** `c(2) = 1`, `c(3) = 3`, `c(4) = 6`, `c(5) = 10` ✓
(triangular numbers); `+1` gives `2, 4, 7, 11` ✓ — the four values §S11 P-7 scored. Note that the
`m = 2` value `2` is the coefficient chapter G's `hex3R`/`hex3U` layer sees as W-11's
`(q−1)q^{2l−1}` telescoping coefficient (`EFF.GENIND.23`), and the `m = 3` value `4` is HMENU3's
`(q−1)q^{4μ−1}` — **so this node's clause (iii) is the cross-chapter tie**, checkable against two
landed chapter-G objects.

**TEETH.** `GT-BRACKETID` / `GT-T-BRACKET` (`EFF.GENIND.22`, `.23`; executable regression, symbolic
identity, §S11 P-7 "24/24 … integer-exact … (exponent coefficients 2/4/7/11)", tooth firing at its
preregistered count 24) → **Lean theorem** at H.20/H.21 (clause (iii) here, the closed form there).
Disposition note: the display naming `GT-AGGDEEP` at `EFF.GENIND.23` is a recorded **source defect**
(a battery-family name that appears nowhere else in the note); chapter H cites the two families that
exist and does not reproduce the phantom name.

**ENVIRONMENT.** ENV-H1.

---

### NODE H.15 [def] [fresh]

**STATEMENT.** *The α-locus exponent, in transported coordinates.* For `m, W, k : ℕ` put
`alphaExp m W k = m * W + k * clusterC m`. Here `W` is the **reduced window minus one**, i.e.
`W = N − 1 − m*k` for the α(k)-transport out of window `N`; the corpus's displayed exponent is
`m(N−1) − k·m(m+1)/2`, and H.16 proves the two agree.

**SIGNATURE.**
```lean
namespace Uniformity.Density.Induction

/-- The α(k)-locus's free-digit exponent, written in the TRANSPORTED coordinate `W = N − 1 − mk`:
`alphaExp m W k = m·W + k·c(m)` — the reduced-window exponent plus the ghost exponent.  H.16
identifies it with `GENIND`'s displayed `m(N−1) − k·m(m+1)/2`. -/
def alphaExp (m W k : ℕ) : ℕ := m * W + k * clusterC m
```

**DEPENDS.** H.13.

**PROOF.** definitional.

**SIZE.** 5 lines.

**SOURCE.** `EFF.GENIND.17` (the α-locus law `(Q−1)·Q^{m(N−1) − k·m(m+1)/2}` and its derivation as
the S2.2 slot count `Q^{Σ_j (N−1−(m−j)k)}`); `EFF.GENIND.21` (the ghost-fibre count
`Σ_{j<m} jk = k·m(m−1)/2 = k·c(m)` and the transported menu
`(Q−1)·Q^{k·c(m)} × the window-(N−mk) menu`).

**⚠ COORDINATE CHOICE, AND WHY (the subtraction-free discipline).** The corpus's display has two
`ℕ`-subtractions (`N−1`, and the whole exponent) which truncate silently below the admissibility
bound `mk ≤ N−1`. Writing the exponent in `W` makes every chapter-H α statement subtraction-free and
makes the transport identity H.17 **definitional**. The re-derivation is one line: with `N−1 = W+mk`,
the `j`-th summand of the corpus's slot count is `N−1−(m−j)k = W + jk`, so
`Σ_{j<m}(W+jk) = mW + k·Σ_{j<m}j = mW + k·c(m)` ✓ — recomputed at H.16. Chapter G used the same
discipline (its `G23R*` route is "subtraction-free" by design).

**TEETH.** none (a definition).

**ENVIRONMENT.** ENV-H1.

---

### NODE H.16 [lemma] [fresh]

**STATEMENT.** *The slot count and the closed form.* Two clauses.
(i) `Σ_{j<m} (W + j*k) = alphaExp m W k`.
(ii) the closed-form reconciliation, subtraction-free:
`2 * alphaExp m W k + k * (m * (m+1)) = 2 * (m * (W + m * k))`.
(Dividing by `2` and substituting `N − 1 = W + m*k`, clause (ii) is the corpus's
`m(N−1) − k·m(m+1)/2`.)

**SIGNATURE.**
```lean
namespace Uniformity.Density.Induction

theorem sum_alphaSlots (m W k : ℕ) :
    ∑ j ∈ Finset.range m, (W + j * k) = alphaExp m W k

theorem two_mul_alphaExp_add (m W k : ℕ) :
    2 * alphaExp m W k + k * (m * (m + 1)) = 2 * (m * (W + m * k))
```

**DEPENDS.** H.13, H.14, H.15.

**PROOF.**
1. (i) `Finset.sum_add_distrib`; the first part is `m * W` (`Finset.sum_const`,
   `Finset.card_range`), the second is `(Σ_{j<m} j) * k = clusterC m * k` by H.14(ii) and
   `Finset.sum_mul`. `ring_nf`.
2. (ii) unfold `alphaExp`; rewrite `2 * (k * clusterC m) = k * (2 * clusterC m) = k * (m * (m-1))`
   by H.14(i). The goal becomes
   `2*m*W + k*(m*(m-1)) + k*(m*(m+1)) = 2*m*W + 2*m*m*k`, i.e.
   `k*m*((m-1) + (m+1)) = 2*m*m*k`. Split on `m = 0` (`simp`) and `m ≥ 1` (`omega` after
   `Nat.succ_pred_eq_of_pos`).

**SIZE.** 16 lines.

**SOURCE.** `EFF.GENIND.17`'s own ARITHMETIC AUDIT, verbatim: *"the free-digit sum is
`Σ_{j=0}^{m−1} (N−1−(m−j)k) = m(N−1) − k·Σ_{j=0}^{m−1}(m−j) = m(N−1) − k·(m + (m−1) + … + 1)
= m(N−1) − k·m(m+1)/2` ✓ — the displayed exponent, recomputed fresh."*

**ARITHMETIC AUDIT (recomputed fresh, at two `Q`).** Take `m = 2`, `k = 1`, `N = 6` so
`W = N−1−mk = 3`: `alphaExp = 2·3 + 1·1 = 7`; the corpus's form is
`m(N−1) − k·m(m+1)/2 = 2·5 − 1·3 = 7` ✓. Cross-check against `EFF.GENIND.99`'s preregistered spot
`ALPHA(1) = 1,024` at `(q,N) = (2,6)`, `m = 4`, `d = 1`: there `W = 6−1−4 = 1` and
`alphaExp = 4·1 + 1·6 = 10`, so the locus is `(Q−1)Q^{10} = 1·2^{10} = 1,024` ✓ **exactly the
preregistered value**. At `q = 3`, `(N, m, k) = (4, 4, 1)`: the corpus records `ALPHA ABSENT` because
α needs `mk ≤ N−1`, i.e. `4 ≤ 3` ✗ ✓ — the admissibility bound, not the exponent, is what excludes
it, and `alphaExp` is never evaluated there. At `q = 3`, `(N, m, k) = (6, 3, 1)`: `W = 2`,
`alphaExp = 3·2 + 1·3 = 9`, locus `2·3^9 = 39,366`; the corpus's form gives
`3·5 − 1·6 = 9` ✓ **agreement at `q = 3` as well as `q = 2`.**

**TEETH.** `GT-ALPHA` (`EFF.GENIND.18`, `.21`; executable regression, pointwise + fibres + onto,
§S11 P-5 "0/2,474 — every pointwise scaled re-read agrees (verdict + σ), every ghost fiber exactly
`q^{k·m(m−1)/2}`") → **Lean theorem** for the exponent arithmetic (the pointwise re-read is
geometric and stays a regression).

**ENVIRONMENT.** ENV-H1.

---

### NODE H.17 [lemma] [fresh]

**STATEMENT.** *The α-transport identity (the ghost/child decomposition).* The α(k)-slice's
exponent is the ghost exponent plus the reduced-window system's own exponent:
`k * clusterC m + m * W = alphaExp m W k`, where `m * W` is the state exponent of the SAME `(m, d)`
system at the reduced window (whose `N' − 1 = W`) and `k * clusterC m` is the ghost-fibre exponent
`Σ_{j<m} j*k`.

**SIGNATURE.**
```lean
namespace Uniformity.Density.Induction

theorem ghostSlots_eq (m k : ℕ) : ∑ j ∈ Finset.range m, j * k = k * clusterC m

theorem ghost_add_child_eq_alphaExp (m W k : ℕ) :
    k * clusterC m + m * W = alphaExp m W k
```

**DEPENDS.** H.13, H.14, H.15.

**PROOF.**
1. `ghostSlots_eq`: `Finset.sum_mul` backwards then H.14(ii); `ring`.
2. `ghost_add_child_eq_alphaExp`: unfold `alphaExp`; `omega` (or `Nat.add_comm`).

**SIZE.** 8 lines.

**SOURCE.** `EFF.GENIND.21` (`LEMMA GENIND-2(a)`, verbatim: *"each scaled state has exactly
`Q^{k·c(m)}` ghost-fiber preimages (`Σ_{j<m} jk = k·m(m−1)/2` ghost slots), all key-constant. Hence
the α(k)-slice's history-resolved menu = `(Q−1)·Q^{k·c(m)} × the window-(N−mk) menu`"*), with the
spec's own audit *"Ghost-slot total `Σ_{j=0}^{m−1} jk = k·(m−1)m/2 = k·c(m)` ✓"*; `EFF.GENIND.18`
(`GENIND-1(ii)`'s cardinality check
`#slice = (Q−1)·Q^{m(N−1)−k·m(m+1)/2}/(Q−1) = #D_k = Π_{j<m} Q^{N−1−(m−j)k}`).

**⚠ WHAT IS AND IS NOT TRANSPORTED.** This node is the **exponent bookkeeping** of the α-transport,
i.e. exactly the part `EFF.GENIND.17`'s cross-check calls *"consistent with `.21`'s statement"*. The
*bijection* (`GENIND-1(ii)`'s recentering `x ↦ x + ẑπ^k` killing the `m` pinned digits by the
binomial identities) is **geometric and has no node** — the honesty item is H-3. What chapter H
delivers is that the two sides' cardinalities agree *identically in `m, W, k`*, which is the
no-over/undercount check, and that they agree with **no characteristic hypothesis** (the corpus's own
claim: *"the binomial identities … valid in every characteristic"*).

**TEETH.** `GT-ALPHA` (fibres exactly `q^{k·m(m−1)/2}`, 0/2,474) → **Lean theorem** for the fibre
exponent; `GT-RECUR` (`EFF.GENIND.21`, §S11 P-6 "0/8 — the α-drain self-similarity
`(q−1)q^{k·c(m)}·u_m(N−mk)` exact at every realized `k`") → **Lean theorem** at H.25 (the recursion's
α-term uses exactly this identity).

**ENVIRONMENT.** ENV-H1.

---

### NODE H.18 [def] [fresh]

**STATEMENT.** *The α-bracket, by its convolution recursion.* For `Q, c : ℕ` define
`alphaBracket Q c : ℕ → ℕ` by `alphaBracket Q c 0 = 1` and, for `μ ≥ 1`,
`alphaBracket Q c μ = Σ_{k=1}^{μ} (Q−1) * Q^(c*k) * alphaBracket Q c (μ−k)` — the sum over all
finite sequences `(k₁, …, k_r)` with `k_i ≥ 1` and `Σ k_i = μ` of `Π_i (Q−1)Q^{c k_i}`, computed by
peeling the first step.

**SIGNATURE.**
```lean
namespace Uniformity.Density.Induction

/-- The α-prefix aggregate `b_{m,d}(μ)`, defined by the composition recursion (peel the first
step).  `alphaBracket Q c μ = Σ over compositions (k₁,…,k_r) of μ with kᵢ ≥ 1 of
Π (Q−1)Q^{c kᵢ}`, and `alphaBracket Q c 0 = 1`. -/
def alphaBracket (Q c : ℕ) : ℕ → ℕ
  | 0 => 1
  | (μ + 1) => ∑ k ∈ Finset.range (μ + 1),
      (Q - 1) * Q ^ (c * (k + 1)) * alphaBracket Q c (μ - k)
```

**DEPENDS.** none.

**PROOF.** definitional. **Termination:** the recursive call is at `μ - k ≤ μ < μ + 1`; supply
`decreasing_by omega` (or restructure with `Nat.rec` on the strong-recursion principle
`Nat.strongRecOn` if the equation compiler balks on the `Finset.sum` binder).

**SIZE.** 10 lines.

**SOURCE.** `EFF.GENIND.22` (`LEMMA GENIND-2(b)`, verbatim: *"`Σ` over all finite sequences
`(k₁, …, k_r)`, `k_i ≥ 1`, `Σk_i = μ`, of `Π_i (Q−1)Q^{c(m)·k_i} = (Q−1)·Q^{(c(m)+1)μ−1} =:
b_{m,d}(μ)`"*), and its proof's generating function *"one step contributes
`A₁(x) = Σ_{k≥1}(Q−1)Q^{c·k}x^k`; chains contribute `A₁/(1−A₁)`"* — the peel-the-first-step
recursion is that generating function's functional equation `B = 1 + A₁·B`.

**⚠ WHY A RECURSION AND NOT A LITERAL COMPOSITION SUM.** A `Finset` of compositions in Lean is a
`Finset (List ℕ)` with two side conditions and no mathlib API; the peel recursion is the same object
(`B = 1 + A₁ B`) and gives H.20's closed form by induction in four lines. The corpus's own proof is
the generating-function identity, i.e. the recursion — so the recursion, not the sum, is the faithful
transcription. **A fleet agent must not "improve" this into a `Finset (Composition μ)` statement**:
that changes the contract and the closed-form proof.

**TEETH.** none (a definition; guarded at H.20/H.21).

**ENVIRONMENT.** ENV-H1.

---

### NODE H.19 [lemma] [fresh]

**STATEMENT.** *The telescoping step.* For `2 ≤ Q` and `1 ≤ c`, and every `μ ≥ 1`:
`alphaBracket Q c (μ + 1) = Q ^ (c + 1) * alphaBracket Q c μ`.

**SIGNATURE.**
```lean
namespace Uniformity.Density.Induction

theorem alphaBracket_succ (Q c : ℕ) (hQ : 2 ≤ Q) (hc : 1 ≤ c) {μ : ℕ} (hμ : 1 ≤ μ) :
    alphaBracket Q c (μ + 1) = Q ^ (c + 1) * alphaBracket Q c μ
```

**DEPENDS.** H.18.

**PROOF.**
1. unfold both sides by the defining equation; the left is
   `Σ_{k<μ+1} (Q−1)Q^{c(k+1)} B(μ−k)` and the right is `Q^{c+1} Σ_{k<μ} (Q−1)Q^{c(k+1)} B(μ−1−k)`.
2. re-index the right sum by `k ↦ k+1` (`Finset.sum_range_succ'` / `Finset.sum_nbij'`): it becomes
   `Σ_{1 ≤ k < μ+1} (Q−1)Q^{c(k+1)} B(μ−k) · Q^{c+1}/Q^{c+1}` — concretely,
   `Q^{c+1} · (Q−1)Q^{c(k+1)} B(μ−1−k) = (Q−1)Q^{c(k+2)} · Q · B(μ−1−k)`.
3. the identity therefore reduces to
   `(Q−1)Q^{c} B(μ) + Σ_{1≤k<μ+1} (Q−1)Q^{c(k+1)} B(μ−k) = Q^{c+1} B(μ)`
   — i.e. to `Σ_{1≤k<μ+1} (Q−1)Q^{c(k+1)} B(μ−k) = (Q^{c+1} − (Q−1)Q^c) B(μ) = Q^c B(μ)`.
4. and that is `Q^c · B(μ) = Q^c · Σ_{k<μ}(Q−1)Q^{c(k+1)}B(μ−1−k)`, which is the re-indexed right
   sum of step 2 — closing the loop by the defining equation of `B(μ)` (valid because `μ ≥ 1`).
5. Bookkeeping: all `ℕ`-subtractions (`Q − 1`, `μ − k`) are guarded — `Q ≥ 2` and `k < μ+1`. Land
   the `Q`-arithmetic as `Nat.sub_add_cancel`-rewrites **before** the sum manipulation.

**SIZE.** 26 lines. **This is the hardest node of §4.** If the re-indexing fights, the sanctioned
fallback is to prove the pair `(B μ, B (μ+1))` satisfies the two-term linear recursion by strong
induction on `μ` with the closed form of H.20 as the induction *statement* (i.e. merge H.19 into
H.20 and prove the closed form directly by strong induction from the convolution). Record the merge
as a RE-PLAN.

**SOURCE.** `EFF.GENIND.22`'s DERIVATION verbatim: *"one step contributes
`A₁(x) = Σ_{k≥1}(Q−1)Q^{c·k}x^k = (Q−1)Q^c x/(1−Q^c x)`; chains contribute
`A₁/(1−A₁) = (Q−1)Q^c x/(1 − Q^{c+1}x)`"* — the denominator `1 − Q^{c+1}x` **is** this node's
one-step recursion, and the spec's own audit re-derives it: *"`(1−Q^c x) − (Q−1)Q^c x = 1 − Q^c
x·(1 + Q − 1) = 1 − Q^{c+1}x` ✓"*.

**TEETH.** `GT-BRACKETID` / `GT-T-BRACKET` → **Lean theorem** at H.20.

**ENVIRONMENT.** ENV-H1.

---

### NODE H.20 [theorem] [fresh]

**STATEMENT.** *THE GENERAL BRACKET.* For `2 ≤ Q`, `1 ≤ c` and `1 ≤ μ`:
`Q * alphaBracket Q c μ = (Q − 1) * Q ^ ((c + 1) * μ)`.
(Dividing by `Q`: `b_{m,d}(μ) = (Q−1)·Q^{(c+1)μ−1}`, the corpus's display; the `Q *` form is
subtraction-free in the exponent.)

**SIGNATURE.**
```lean
namespace Uniformity.Density.Induction

theorem alphaBracket_closed (Q c : ℕ) (hQ : 2 ≤ Q) (hc : 1 ≤ c) {μ : ℕ} (hμ : 1 ≤ μ) :
    Q * alphaBracket Q c μ = (Q - 1) * Q ^ ((c + 1) * μ)

/-- The corpus's displayed form, for consumers that prefer it. -/
theorem alphaBracket_eq (Q c : ℕ) (hQ : 2 ≤ Q) (hc : 1 ≤ c) {μ : ℕ} (hμ : 1 ≤ μ) :
    alphaBracket Q c μ = (Q - 1) * Q ^ ((c + 1) * μ - 1)
```

**DEPENDS.** H.18, H.19.

**PROOF.**
1. induction on `μ`, base `μ = 1`: the defining equation gives
   `B 1 = Σ_{k<1} (Q−1)Q^{c(k+1)} B(1−k) = (Q−1)Q^c · B 0 = (Q−1)Q^c`; then
   `Q * (Q−1)Q^c = (Q−1)Q^{c+1} = (Q−1)Q^{(c+1)·1}` ✓ by `ring`/`pow_succ`.
2. step: `Q * B(μ+1) = Q * Q^{c+1} * B μ` (H.19) `= Q^{c+1} * (Q * B μ)`
   `= Q^{c+1} * (Q−1) * Q^{(c+1)μ}` (IH) `= (Q−1) * Q^{(c+1)(μ+1)}` by `pow_add` and `ring`.
3. `alphaBracket_eq`: from clause 1, `(c+1)*μ ≥ 1`, so
   `Q^{(c+1)μ} = Q * Q^{(c+1)μ − 1}` (`Nat.sub_add_cancel`, `pow_succ`); cancel `Q` by
   `Nat.eq_of_mul_eq_mul_left (by omega : 0 < Q)`.

**SIZE.** 18 lines. **SPLIT MANDATED:** land `alphaBracket_closed` and `alphaBracket_eq` as two
declarations in one node file (the second is a three-line corollary and every downstream consumer in
§10 uses the first).

**SOURCE.** `EFF.GENIND.22` (the display and its proof); `EFF.GENIND.09` (`GENIND.A`(II)'s bracket
with the **WINDOW CONDITION** `mμ ≤ N−1`, `[r1, PE1-M1]`).

**⚠ THE WINDOW CONDITION IS NOT A HYPOTHESIS OF THIS NODE — DELIBERATELY.** `EFF.GENIND.22`'s own
CONDITIONALITY: *"The generating-function identity is unconditional; the **realized-history** reading
carries `mμ ≤ N−1`."* This node states the identity, so it carries `2 ≤ Q`, `1 ≤ c`, `1 ≤ μ` and
nothing else — hypotheses at their true minimum (the G.28 lesson). The window condition belongs to
the *consumer* that interprets `alphaBracket` as a realized-history aggregate: it appears as a
hypothesis of H.67/H.71, not here. **A node stating this identity under `m*μ ≤ N−1` is over-strong
and must be returned.**

**ARITHMETIC AUDIT (recomputed fresh at `Q = 2`, `Q = 3` AND `Q = 4`).**
* `Q = 4`, `c = 1`, `μ = 2` (the corpus's own in-line certificate, `EFF.GENIND.64`): compositions of
  `2` are `(2)` and `(1,1)`; mass terms `(4−1)·4² = 48` and `[(4−1)·4]² = 144`; sum `= 192`. Closed
  form `(Q−1)Q^{(c+1)μ−1} = 3·4³ = 192` ✓, and `Q * B = 4 · 48+144?` — no: `B 2 = 192` and
  `Q * B 2 = 768 = 3 · 4^4 = 3 · 256` ✓.
* **`Q = 2`, `c = 1`, `μ = 3`:** compositions of `3`: `(3) → 1·2³ = 8`; `(2,1) → (1·2²)(1·2) = 8`;
  `(1,2) → 8`; `(1,1,1) → 2³ = 8`. Sum `= 32`. Closed form `(2−1)·2^{2·3−1} = 2⁵ = 32` ✓.
* **`Q = 3`, `c = 1`, `μ = 2`:** `(2) → 2·3² = 18`; `(1,1) → (2·3)² = 36`. Sum `= 54`. Closed form
  `2·3^{3} = 54` ✓. **This is the check the G.23 lesson demands** — at `Q = 2` the two composition
  terms are equal (`8 = 8` above), which would hide a symmetry-factor error; at `Q = 3` they differ
  (`18 ≠ 36`), so the sum genuinely tests the convolution.
* **`Q = 3`, `c = 3` (i.e. `m = 3`), `μ = 2`:** `(2) → 2·3⁶ = 1458`; `(1,1) → (2·3³)² = 54² = 2916`.
  Sum `= 4374`. Closed form `2·3^{4·2−1} = 2·3⁷ = 4374` ✓.
* **`Q = 2`, `c = 6` (`m = 4`), `μ = 1`:** `(1) → 1·2⁶ = 64`; closed form `1·2^{7·1−1} = 2⁶ = 64` ✓.
* **`Q = 2`, `c = 10` (`m = 5`), `μ = 2`:** `(2) → 2^{20} = 1,048,576`; `(1,1) → (2^{10})² = 2^{20}`.
  Sum `= 2^{21}`; closed form `1·2^{11·2−1} = 2^{21}` ✓.
The six cells cover `m ∈ {2,3,4,5}` and `Q ∈ {2,3,4}` — a strict superset of the corpus's own
`m ∈ {2,3,4,5}, μ ∈ {1,2,3}, q ∈ {2,3}` 24-cell tooth (`EFF.GENIND.09`'s `GT-BRACKETID`).

**TEETH.** `GT-BRACKETID [SYM]` (`EFF.GENIND.09`, `.22`; executable regression, symbolic identity
check at `m ∈ {2,3,4,5}`, `μ ∈ {1,2,3}`, `q ∈ {2,3}`, §S11 P-7 "24/24", tooth `GT-T-BRACKET` at its
preregistered count 24) → **Lean theorem** (this node is the general law those 24 cells
instantiate).

**ENVIRONMENT.** ENV-H1.

---

### NODE H.21 [lemma] [fresh]

**STATEMENT.** *The bracket audit and the mass/letter reconciliation.* Four clauses, all closed
numeric facts.
(i) `alphaBracket 4 1 2 = 192` and `48 + 144 = 192`.
(ii) `alphaBracket 3 1 2 = 54` and `18 + 36 = 54`.
(iii) `alphaBracket 2 1 3 = 32`.
(iv) the ghost × letter reconciliation at `|K| = 4`, `μ = 2`, `c = 1`:
`4 ^ 2 * ((4 − 1) * 4 ^ 1) = 192` — i.e. `ghost × letters = mass`.

**SIGNATURE.**
```lean
namespace Uniformity.Density.Induction

theorem alphaBracket_audit :
    alphaBracket 4 1 2 = 192 ∧ alphaBracket 3 1 2 = 54 ∧ alphaBracket 2 1 3 = 32

theorem massNorm_eq_ghost_mul_letters :
    (4 : ℕ) ^ 2 * ((4 - 1) * 4 ^ 1) = alphaBracket 4 1 2
```

**DEPENDS.** H.18 (and H.20 for the cross-check, though the proofs are by evaluation).

**PROOF.**
1. `alphaBracket_audit`: `by decide` — or, if the recursion's `decide` is too deep,
   `by simp [alphaBracket, Finset.sum_range_succ]; norm_num` three times.
2. `massNorm_eq_ghost_mul_letters`: `norm_num` after the first clause (`16 * 12 = 192`).

**SIZE.** 10 lines.

**SOURCE.** `EFF.GENIND.64`'s in-line numeric certificate, verbatim: *"Checked numerically this round
at `(q, μ″) = (2, 2)`, `|K| = 4` (genre F, `c(2) = 1`): composition sum
`Σ_{(k₁..k_r), Σk_i=2} Π_i (|K|−1)|K|^{k_i} = 48 + 144 = 192 = (|K|−1)|K|³` (mass form);
letters-only `Σ (|K|−1)^r = 3 + 9 = 12 = (|K|−1)|K|¹` (GENH4 form); ghost `|K|² = 16`;
`16 · 12 = 192`."*; `EFF.GENHN.36` (the same reconciliation
`(|K|−1)|K|^{2κ−1} = |K|^{κ} · (|K|−1)|K|^{κ−1}`).

**⚠ WHY THE RECONCILIATION IS A NODE.** `EFF.GENIND.64`'s NORMALIZATION DECLARATION is the corpus's
own warning that *"a discharge of `(CS-2)` in the wrong normalization would be off by the ghost
factor `|K|^{μ″}`, invisible at genre E and visible at genre F"*. `StageInterface.hbracket` (H.09)
is stated in the **mass** normalization; clause (iv) is the machine check that the mass form is the
one whose ghost factor is `|K|^{c(μ)μ}`, so a genre-F instance built from `GENH4`'s letter-sum form
will fail to satisfy `hbracket` — **loudly, at elaboration time**, which is the point.

**ARITHMETIC AUDIT.** All four clauses ARE the audit; each is recomputed independently in H.20's
audit block, and clause (ii) at `Q = 3` is the non-degenerate cell (`18 ≠ 36`) the `q = 2`-only
regime would have hidden. Genre-E invisibility, recomputed: with `|K| = q` and `δ = 2μ″` integer
`dv`-points, the letter-sum reads `(q−1)q^{δ−1} = (q−1)q^{2μ″−1}`, which **equals** the mass form
`(q−1)q^{(c(2)+1)μ″−1}` ✓ — so at genre E the two normalizations coincide numerically and the gap is
genuinely invisible, exactly as `EFF.GENIND.64` claims. Genre-F gap: mass `(q²−1)(q²)^{2μ−1}` ÷
letters `(q²−1)(q²)^{μ−1} = (q²)^{μ}` ✓ = the ghost.

**TEETH.** `EFF.GENIND.64`'s **`arithmetic recount`** (a compiler-verifiable certificate embedded in
the statement; the spec's own disposition) → **Lean theorem**. No battery row exercises `(CS-2)` at
any genre — `signed vacuity disclosure` at `EFF.GENIND.64` — so this node is the *only* machine
guard on the normalization, at any grade, anywhere.

**ENVIRONMENT.** ENV-H1.

---

### NODE H.22 [lemma] [fresh]

**STATEMENT.** *The DRAIN locus exponent and the five-event exponent inventory at window 1.* Two
clauses.
(i) `DRAIN`'s locus exponent is `d*(m−1)*(N−1)`, and relative to the total `d*m*(N−1)` its
codimension is exactly `d*(N−1)`: subtraction-free,
`d * (m − 1) * (N − 1) + d * (N − 1) = d * m * (N − 1)` for `1 ≤ m`.
(ii) at `N = 1` the state count is `1`, the DRAIN locus is the whole space, α needs `m*k ≤ 0` with
`k ≥ 1` (impossible), and `DEC`/`β`/`CS` need `v(a₀) < N = 1` (impossible): **of the five events
exactly one is inhabited**, stated as the exponent facts
`d * m * (1 − 1) = 0`, `d * (m−1) * (1−1) = 0`, and `¬ ∃ k, 1 ≤ k ∧ m * k ≤ 0` for `1 ≤ m`.

**SIGNATURE.**
```lean
namespace Uniformity.Density.Induction

theorem drain_codim (d m N : ℕ) (hm : 1 ≤ m) :
    d * (m - 1) * (N - 1) + d * (N - 1) = d * m * (N - 1)

theorem window_one_exponents (d m : ℕ) (hm : 1 ≤ m) :
    d * m * (1 - 1) = 0 ∧ d * (m - 1) * (1 - 1) = 0 ∧ ¬ ∃ k, 1 ≤ k ∧ m * k ≤ 0
```

**DEPENDS.** none.

**PROOF.**
1. `drain_codim`: `rcases Nat.exists_eq_add_of_le hm with ⟨m', rfl⟩` then `ring_nf`; `omega` on the
   `ℕ`-subtraction `(1 + m') - 1 = m'`.
2. `window_one_exponents`: first two by `simp`; third: `intro ⟨k, hk, hmk⟩`; `Nat.pos_of_ne_zero`
   plus `Nat.mul_pos hm hk` contradicts `hmk`. `omega`.

**SIZE.** 10 lines.

**SOURCE.** `EFF.GENIND.08` (`GENIND.A`(I): *"DRAIN: `v(a₀) ≥ N` (conservative exit); locus
`q^{d(m−1)(N−1)}`"*); `EFF.GENIND.160` (`ANNEX R R3.1`, the window-1 convention rider, verbatim:
*"states: `a_j ∈ (O/π¹)[x]_{<d}` with `ā_j = 0` forces every `a_j = 0` — exactly
`q^{dm(N−1)} = q⁰ = 1` state; read: `a₀ = 0` gives `v(a₀) ≥ 1 = N`, so the conservative read exits
UNDECIDED before consulting any digit — DRAIN; `u_{m,d}(1) = total = 1`; grammar coherence: DRAIN's
locus law `q^{d(m−1)(N−1)} = 1 = the whole space`; α needs `mk ≤ N−1 = 0` (none); `DEC/β/CS` need a
polygon, i.e. `v(a₀) < N` (none) — of the five events exactly one is inhabited"*), with the spec's
own audit reproducing every clause.

**⚠ THE BOUNDARY CASE IS A NODE, NOT A REMARK (the G.31 lesson).** `ANNEX R R3` was filed as a
**CONFIRMED GAP** — a *scope leak*, `EFF.GENIND.159` — precisely because window-1 systems arise as
transport targets at three enumerated sites and the `S1` convention said `N ≥ 2`. Chapter H's
consumers of the window-1 boundary are H.24 (`uTwo 1 = 1`), H.71 (`GENIND.C′`'s `N ≥ 1`) and H.71's
truncation base case (`T = 1`). Landing the boundary as a lemma here means DEPENDS-completeness holds
at every one of them; leaving it as prose is exactly the defect that made `EFF.GENIND.159`.

**ARITHMETIC AUDIT (recomputed fresh at `q = 2` and `q = 3`).** `DRAIN₀` spot values from
`EFF.GENIND.99`: at `(q, N, n) = (2, 6, 4)`, `d = 1`, `m = 4`: `q^{d(m−1)(N−1)} = 2^{3·5} = 32,768`
✓ (the preregistered value). At `(3, 4, 4)`: `3^{3·3} = 19,683` ✓. At `(5, 3, 4)`: `5^{3·2} = 15,625`
✓. At `(2, 5, 5)`, `m = 5`: `2^{4·4} = 65,536` ✓. At `(3, 3, 5)`: `3^{4·2} = 6,561` ✓. **All five
preregistered `DRAIN₀` values reproduce, across `q ∈ {2, 3, 5}`.** Window-1: `q^{1·m·0} = 1` at every
`q` ✓, and the codimension identity at `N = 1` reads `0 + 0 = 0` ✓.

**TEETH.** `GT-PART [SAME]` (`EFF.GENIND.08`, §S11 P-2 "0/33 — partition exact on every row, with
`Zp`/`F_q[[t]]` depth-0 tallies IDENTICAL at all 11 shared `(m, q, N)`") → **Lean theorem** for the
exponent arithmetic; `EFF.GENIND.160`'s machine leg I (`genind_annexr_supp.py` @ `f5271e4`, GREEN,
`(m, Q) ∈ {2,3,4}²`, with a decorrelated sympy re-solve) → **Lean theorem** for clause (ii).

**ENVIRONMENT.** ENV-H1.

---

## 5. §5 — ARITHMETIC II: THE `m = 2` DRAINAGE SPECIES AND THE `(A2-RATE)` GROUND INSTANCE

> `EFF.GENIND.150` is, in the spec's own words, *"the most fully checkable unit in the three GENIND
> shards"* — every displayed step re-derives. §5 is its Lean transcription, and its last node (H.28)
> is the `(A2-RATE)` species's only proved instance at general `Q`.

### NODE H.23 [def] [fresh]

**STATEMENT.** *The `m = 2` conservative complement, by its first-step recursion.* For `Q : ℕ`
define `uTwo Q : ℕ → ℕ` by `uTwo Q 0 = 1`, `uTwo Q 1 = 1`, and for `N ≥ 2`
`uTwo Q N = Q^(N−1) + Σ_{k : 1 ≤ k, 2k ≤ N−1} (Q−1) * Q^k * uTwo Q (N − 2k)`.

**SIGNATURE.**
```lean
namespace Uniformity.Density.Induction

/-- The conservative-undecided count of the `(2, d)` cluster system at window `N`, in `Q = q^d`
units, by `GENIND` §S5.2's first-step recursion specialized to `m = 2` (where the recursion has no
β-terms: `m = 2 < 4` excludes CS, and a repeated linear `e = 1` factor at `m = 2` spans the whole
polygon, i.e. is α). -/
def uTwo (Q : ℕ) : ℕ → ℕ
  | 0 => 1
  | 1 => 1
  | (N + 2) => Q ^ (N + 1) +
      ∑ k ∈ Finset.range (N + 2), if 1 ≤ k ∧ 2 * k ≤ N + 1 then (Q - 1) * Q ^ k * uTwo Q (N + 2 - 2 * k) else 0
```

**DEPENDS.** none.

**PROOF.** definitional. **Termination:** in the live branch `1 ≤ k`, so `N + 2 − 2k ≤ N < N + 2`;
`decreasing_by omega` after `split_ifs`.

**SIZE.** 12 lines.

**SOURCE.** `EFF.GENIND.150` (`R1.1`, verbatim: *"the first-step recursion degenerates to head + α:
`u(N) = Q^{N−1} + Σ_{k ≥ 1, 2k ≤ N−1} (Q−1)·Q^k · u(N−2k)`, `u(1) = 1` (the window-1 boundary: R3's
rider below), writing `u := u_{2,d}`, `Q := q^d`, `c(2) = 1`"*); `EFF.GENIND.45` (the general
first-step recursion this specializes).

**⚠ THE `c(2) = 1` COINCIDENCE, DECLARED.** The α-term's coefficient is `(Q−1)Q^{k·c(m)}` with
`c(2) = 1`, so it reads `(Q−1)Q^k` — the exponent is `k`, **not** `k·c(m)` in general. A fleet agent
extending this to `m ≥ 3` must write `Q^(k * clusterC m)` (H.13) and must NOT copy the `Q^k`.
`EFF.GENIND.150`'s own scope: `m = 2` only, because *"at `m = 2` the recursion of S5.2 closes without
β-terms"*.

**TEETH.** none (a definition; guarded at H.25/H.26/H.29).

**ENVIRONMENT.** ENV-H1.

---

### NODE H.24 [lemma] [fresh]

**STATEMENT.** `uTwo Q 1 = 1` and `uTwo Q 2 = Q`.

**SIGNATURE.**
```lean
namespace Uniformity.Density.Induction

theorem uTwo_one (Q : ℕ) : uTwo Q 1 = 1

theorem uTwo_two (Q : ℕ) : uTwo Q 2 = Q
```

**DEPENDS.** H.23.

**PROOF.**
1. `uTwo_one` : `rfl`.
2. `uTwo_two` : unfold at `N = 0`: `Q^1 + Σ_{k<2} …`; every `k` fails `2k ≤ 1` for `k ≥ 1`, so the
   sum is `0`. `simp [uTwo, Finset.sum_range_succ]`.

**SIZE.** 6 lines.

**SOURCE.** `EFF.GENIND.150` (*"iterating from `u(1) = 1`, `u(2) = Q`"*); `EFF.GENIND.160`
(`R3.1`'s window-1 clause `u_{m,d}(1) = total = 1`, and the two-way coherence check: the closed form
`u(2ℓ+1) = (ℓ+1)Q^{2ℓ} − ℓQ^{2ℓ−1}` returns `1` at `ℓ = 0`).

**⚠ DEPENDS COMPLETENESS (the G.31 lesson).** `uTwo_one` is the **window-1 boundary** whose absence
was `CODEX F2`, a CONFIRMED GAP (`EFF.GENIND.159`). It is a DEPENDS of H.26's closed form (whose
odd branch is anchored there) and of H.25's recursion at `N = 3` (which calls `uTwo Q 1`). Both
DEPENDS fields name it. H.22(ii) supplies the *reason* the value is `1`; this node supplies the
value.

**TEETH.** `EFF.GENIND.160`'s machine leg I (GREEN) → **Lean theorem**.

**ENVIRONMENT.** ENV-H1.

---

### NODE H.25 [theorem] [fresh]

**STATEMENT.** *The telescoped recursion.* For `2 ≤ Q` and `N ≥ 3`:
`uTwo Q N + Q^(N−2) = Q^(N−1) + Q^2 * uTwo Q (N − 2)`
(the subtraction-free form of the corpus's `u(N) = Q^{N−1} − Q^{N−2} + Q²·u(N−2)`).

**SIGNATURE.**
```lean
namespace Uniformity.Density.Induction

theorem uTwo_rec (Q : ℕ) (hQ : 2 ≤ Q) {N : ℕ} (hN : 3 ≤ N) :
    uTwo Q N + Q ^ (N - 2) = Q ^ (N - 1) + Q ^ 2 * uTwo Q (N - 2)
```

**DEPENDS.** H.23, H.24.

**PROOF.** The corpus's telescope, transcribed. Write `S(N) := Σ_{k ≥ 1, 2k ≤ N−1} (Q−1)Q^k u(N−2k)`
so `u(N) = Q^{N−1} + S(N)`.
1. re-index `S(N)`'s `k ≥ 2` tail by `j = k − 1`:
   `Σ_{k≥2}(Q−1)Q^k u(N−2k) = Q · Σ_{j≥1}(Q−1)Q^{j} u((N−2)−2j) = Q · S(N−2)`.
   The index ranges match: `2k ≤ N−1, k ≥ 2` ⟺ `2j ≤ N−3, j ≥ 1`. (`Finset.sum_nbij'` with
   `k ↦ k−1`; the side conditions are `omega`.)
2. hence `S(N) = (Q−1)·Q·u(N−2) + Q·S(N−2)`.
3. substitute `S(N−2) = u(N−2) − Q^{N−3}`, i.e. use `u(N−2) = Q^{N−3} + S(N−2)` **additively**:
   `S(N) + Q·Q^{N−3} = (Q−1)Q·u(N−2) + Q·u(N−2) = Q^2 · u(N−2)`.
4. add `Q^{N−1}` to both sides and use `Q·Q^{N−3} = Q^{N−2}`:
   `u(N) + Q^{N−2} = Q^{N−1} + Q^2 u(N−2)` ✓.
5. `N = 3` uses `uTwo Q 1` (H.24) inside step 3's `u(N−2)`.

**SIZE.** 30 lines. Every `ℕ`-subtraction (`N−1`, `N−2`, `N−3`, `N−2k`) is guarded by `3 ≤ N` and
`2k ≤ N−1`; land the `Nat.sub` normalizations as `have`s first (`obtain ⟨M, rfl⟩ : ∃ M, N = M + 3`).

**SOURCE.** `EFF.GENIND.150` (the telescope, and the spec's own full re-derivation: *"Re-index
`S(N)` at `j = k−1` on its `k ≥ 2` tail … the index ranges match, since `2k ≤ N−1, k ≥ 2`
⟺ `2j ≤ N−3, j ≥ 1` ✓. Hence `S(N) = (Q−1)Q·u(N−2) + Q·S(N−2)`, and substituting
`S(N−2) = u(N−2) − Q^{N−3}` gives `u(N) = Q^{N−1} − Q^{N−2} + Q²·u(N−2)` ✓ — the displayed
telescoped recurrence, exactly"*).

**ARITHMETIC AUDIT (recomputed fresh at `Q = 2` and `Q = 3`).** `Q = 2`: `u(1)=1`, `u(2)=2`,
`u(3) = 2² + (1)(2)(1) = 6`; check `u(3)+u`-form: `6 + 2^1 = 2^2 + 2^2·1 = 8` ✓. `u(4) = 2³ + 1·2·2 =
12`; check `12 + 2² = 2³ + 2²·2 = 16` ✓. `u(5) = 2⁴ + 1·2·u(3) + 1·2²·u(1) = 16 + 12 + 4 = 32`;
check `32 + 2³ = 2⁴ + 2²·12 = 16 + 48 = 64` ✓. `Q = 3`: `u(1)=1`, `u(2)=3`,
`u(3) = 3² + 2·3·1 = 15`; check `15 + 3 = 9 + 9·1 = 18` ✓. `u(4) = 3³ + 2·3·3 = 45`; check
`45 + 9 = 27 + 9·3 = 54` ✓. `u(5) = 3⁴ + 2·3·15 + 2·9·1 = 81 + 90 + 18 = 189`; check
`189 + 27 = 81 + 9·15 = 216` ✓. **Both characteristics of `Q` behave; the `Q = 3` cells are the ones
where the `(Q−1)` factor is not `1` and therefore genuinely test the α-coefficient.**

**TEETH.** `GT-RECUR [SAME]` (`EFF.GENIND.21`, `.45`; §S11 P-6 "GT-RECUR 0/8 — the α-drain
self-similarity `(q−1)q^{k·c(m)}·u_m(N−mk)` exact at every realized `k`") → **Lean theorem**;
`EFF.GENIND.150`'s machine leg A (`genind_annexr_supp.py` @ `f5271e4`, GREEN: the closed forms solve
the recursion symbolically in `Q` at `N = 2..14`) → **Lean theorem** at H.26.

**ENVIRONMENT.** ENV-H1.

---

### NODE H.26 [theorem] [fresh]

**STATEMENT.** *THE CLOSED FORM.* For `2 ≤ Q` and `M ≥ 2`:
`uTwo Q M = Q^(M−1) + ((M−1)/2) * (Q−1) * Q^(M−2)`
(`ℕ` division is exactly the corpus's `⌊(M−1)/2⌋`). Equivalently, in the parity-split form the
corpus also displays: `uTwo Q (2ℓ) + (ℓ−1)*Q^(2ℓ−2) = ℓ*Q^(2ℓ−1)` for `ℓ ≥ 1`, and
`uTwo Q (2ℓ+1) + ℓ*Q^(2ℓ−1) = (ℓ+1)*Q^(2ℓ)` for `ℓ ≥ 1`.

**SIGNATURE.**
```lean
namespace Uniformity.Density.Induction

theorem uTwo_closed (Q : ℕ) (hQ : 2 ≤ Q) {M : ℕ} (hM : 2 ≤ M) :
    uTwo Q M = Q ^ (M - 1) + ((M - 1) / 2) * ((Q - 1) * Q ^ (M - 2))

theorem uTwo_even (Q : ℕ) (hQ : 2 ≤ Q) {l : ℕ} (hl : 1 ≤ l) :
    uTwo Q (2 * l) + (l - 1) * Q ^ (2 * l - 2) = l * Q ^ (2 * l - 1)

theorem uTwo_odd (Q : ℕ) (hQ : 2 ≤ Q) (l : ℕ) :
    uTwo Q (2 * l + 1) + l * Q ^ (2 * l - 1) = (l + 1) * Q ^ (2 * l)
```

**DEPENDS.** H.23, H.24, H.25.

**PROOF.**
1. two-step induction on `M` via `Nat.le_induction` on the statement `P M ∧ P (M+1)`, or
   `Nat.strongRecOn` with the recursion H.25 as the step. Bases: `M = 2` gives
   `uTwo Q 2 = Q = Q^1 + 0` ✓ (H.24, `(2−1)/2 = 0`); `M = 3` gives
   `uTwo Q 3 = Q² + (Q−1)Q = Q^2 + 1·(Q−1)Q^1` ✓ (`(3−1)/2 = 1`).
2. step from `M` to `M+2`: H.25 gives `u(M+2) + Q^{M} = Q^{M+1} + Q²·u(M)`; substitute the IH for
   `u(M)` and check
   `Q^{M+1} + Q²(Q^{M−1} + ⌊(M−1)/2⌋(Q−1)Q^{M−2}) = Q^{M+1} + Q^{M+1}? ` — recompute:
   `Q²·Q^{M−1} = Q^{M+1}` and `Q²·(Q−1)Q^{M−2} = (Q−1)Q^{M}`, so the right side is
   `Q^{M+1} + Q^{M+1} + ⌊(M−1)/2⌋(Q−1)Q^{M}`; subtracting `Q^M` from both sides and using
   `Q^{M+1} = Q·Q^M` and `⌊(M+1)/2⌋ = ⌊(M−1)/2⌋ + 1` gives the target. Land the exponent
   normalizations first.
3. `uTwo_even`/`uTwo_odd`: substitute `M = 2l` resp. `M = 2l+1` in clause 1 and evaluate
   `(M−1)/2` (`= l−1` resp. `= l`); then `Nat.succ_pred`-style rearrangement plus `ring_nf`. Both are
   `omega`-closable once the `Q`-powers are aligned.

**SIZE.** 34 lines. **SPLIT MANDATED:** land `uTwo_closed` as H.26 and the two parity forms as a
second declaration in the same file (they are three-line corollaries and H.27 uses `uTwo_closed`
only).

**SOURCE.** `EFF.GENIND.150`, verbatim: *"iterating from `u(1) = 1`, `u(2) = Q` gives the CLOSED
FORMS `u(2ℓ) = ℓ·Q^{2ℓ−1} − (ℓ−1)·Q^{2ℓ−2}`, `u(2ℓ+1) = (ℓ+1)·Q^{2ℓ} − ℓ·Q^{2ℓ−1}`, equivalently
`u(M) = Q^{M−1} + ⌊(M−1)/2⌋·(Q−1)·Q^{M−2}` — which is LETTER-FOR-LETTER the committed `R(M)`
displayed inside `THEOREM HEX3.A`"*, with the spec's own audit verifying all three forms are one
function and both base cases.

**⚠ THE `R(M)` TIE IS A CROSS-CHAPTER CHECK, NOT A DEPENDENCY.** `EFF.GENIND.150` claims the closed
form is letter-for-letter W-11's `R(M)` as displayed inside `THEOREM HEX3.A`, machine-checked at
`M = 1..14` (leg B). Chapter G lands `hex3R` and `hex3R_rec` (`ChapG/G65.lean`) — **the `n = 3`
`R`-recursion, a different object**. Do NOT wire `uTwo` to `hex3R`: the corpus's tie is at the
*value* level for the `m = 2` cluster, and chapter G's `hex3R` is HEX3's `R(M)` inside the `n = 3`
telescope. §16 item 6 flags the identification for the cross-read.

**ARITHMETIC AUDIT (recomputed fresh at `Q = 2` and `Q = 3`, against H.25's values).** `Q = 2`:
`M=2 → 2^1 + 0 = 2` ✓; `M=3 → 2^2 + 1·1·2 = 6` ✓; `M=4 → 2^3 + 1·1·4 = 12` ✓;
`M=5 → 2^4 + 2·1·8 = 32` ✓; `M=6 → 2^5 + 2·1·16 = 64`; check against H.25:
`u(6) + 2^4 = 2^5 + 2^2·u(4) = 32 + 48 = 80`, so `u(6) = 64` ✓. `Q = 3`:
`M=2 → 3 + 0 = 3` ✓; `M=3 → 9 + 1·2·3 = 15` ✓; `M=4 → 27 + 1·2·9 = 45` ✓;
`M=5 → 81 + 2·2·27 = 189` ✓; `M=6 → 243 + 2·2·81 = 567`; check
`u(6) + 3^4 = 3^5 + 3^2·45 = 243 + 405 = 648`, so `u(6) = 567` ✓. **Ten cells, two values of `Q`,
all exact.** Parity forms at `Q = 3, ℓ = 3` (`M = 6`): `ℓQ^{2ℓ−1} − (ℓ−1)Q^{2ℓ−2} = 3·3^5 − 2·3^4 =
729 − 162 = 567` ✓.

**TEETH.** `EFF.GENIND.150`'s machine legs A and B (symbolic solve at `N = 2..14`; the `R(M)`
equality at `M = 1..14`) → **Lean theorem** for the closed form (legs A/B are the corpus's only
evidence, and this node replaces them with a proof at every `N`).

**ENVIRONMENT.** ENV-H1.

---

### NODE H.27 [lemma] [fresh]

**STATEMENT.** *The rate, in `ℕ`.* For `2 ≤ Q` and `1 ≤ N`: `uTwo Q N ≤ N * Q^(N−1)`.

**SIGNATURE.**
```lean
namespace Uniformity.Density.Induction

theorem uTwo_le (Q : ℕ) (hQ : 2 ≤ Q) {N : ℕ} (hN : 1 ≤ N) : uTwo Q N ≤ N * Q ^ (N - 1)
```

**DEPENDS.** H.24, H.26.

**PROOF.**
1. `N = 1`: `uTwo Q 1 = 1 ≤ 1 * Q^0 = 1` ✓ (H.24).
2. `N ≥ 2`: by H.26, `uTwo Q N = Q^{N−1} + ⌊(N−1)/2⌋(Q−1)Q^{N−2}`.
   Bound `(Q−1)Q^{N−2} ≤ Q^{N−1}` (since `Q−1 ≤ Q`), so
   `uTwo Q N ≤ (1 + ⌊(N−1)/2⌋)·Q^{N−1}`.
3. `1 + ⌊(N−1)/2⌋ ≤ N` for `N ≥ 1` (`omega` after `Nat.div_le_self`-style bound
   `⌊(N−1)/2⌋ ≤ N−1`).
4. `Nat.mul_le_mul_right`.

**SIZE.** 12 lines.

**SOURCE.** `EFF.GENIND.150` (*"Rate (leg C): `u(N) ≤ N·Q^{N−1}` … at `N = 2..14`,
`Q ∈ {2,3,4,5,8,9}` — coefficient POLYNOMIAL (degree 1) in the window, deficit LINEAR in the
window"*), with the spec's own audit: *"at `N = 2ℓ`, `u = ℓQ^{2ℓ−1} − (ℓ−1)Q^{2ℓ−2} ≤ ℓQ^{2ℓ−1} ≤
2ℓ·Q^{2ℓ−1} = N·Q^{N−1}` ✓"*.

**⚠ HYPOTHESIS AT ITS TRUE MINIMUM.** The corpus's leg C is checked at `Q ∈ {2,3,4,5,8,9}` and
`N ≤ 14`; this node is stated at **every** `Q ≥ 2` and **every** `N ≥ 1`, with no `d = 1` and no
characteristic hypothesis — which is what makes `GENIND-BOX-3`'s `Q`-uniformity claim a theorem for
this leg (honesty item H-3).

**TEETH.** `EFF.GENIND.150`'s machine leg C → **Lean theorem** (the node generalizes the 78 checked
cells to all `(Q, N)`).

**ENVIRONMENT.** ENV-H1.

---

### NODE H.28 [theorem] [fresh]

**STATEMENT.** *THE `(A2-RATE)` GROUND INSTANCE.* For `2 ≤ Q` and `1 ≤ N`, in `ℝ`:
`(uTwo Q N : ℝ) / (Q:ℝ)^(2*(N−1)) ≤ (N:ℝ) / (Q:ℝ)^(N−1)`.
This is the species `u_{μ,d}(M)/Q^{μ(M−1)} ≤ K·M^B·Q^{−(M−c)}` at `(μ, K, B, c) = (2, 1, 1, 1)`.

**SIGNATURE.**
```lean
namespace Uniformity.Density.Induction

theorem uTwo_ratio_le (Q : ℕ) (hQ : 2 ≤ Q) {N : ℕ} (hN : 1 ≤ N) :
    (uTwo Q N : ℝ) / (Q : ℝ) ^ (2 * (N - 1)) ≤ (N : ℝ) / (Q : ℝ) ^ (N - 1)
```

**DEPENDS.** H.27 · mathlib `div_le_div_iff`, `pow_pos`, `Nat.cast_le`.

**PROOF.**
1. `have hQ0 : (0:ℝ) < Q := by positivity` (from `2 ≤ Q`).
2. `rw [div_le_div_iff (by positivity) (by positivity)]`; the goal is
   `(uTwo Q N : ℝ) * Q^(N−1) ≤ N * Q^(2*(N−1))`.
3. `Q^(2*(N−1)) = Q^(N−1) * Q^(N−1)` by `pow_mul`/`two_mul`, `pow_add`.
4. cancel `Q^(N−1) > 0` by `mul_le_mul_right`; the goal is `(uTwo Q N : ℝ) ≤ N * Q^(N−1)`.
5. `exact_mod_cast uTwo_le Q hQ hN`.

**SIZE.** 12 lines.

**SOURCE.** `EFF.GENIND.150` (*"`u(N)/Q^{2(N−1)} ≤ N·Q^{−(N−1)}`"*); `EFF.GENIND.151` (the
`(A2-RATE)` species display, with the instance list: *"`(μ, d) = (2, d)`: `K = 1, B = 1, c = 1` (the
closed forms above, machine legs A–C)"*), and its audit: *"`K·M^B·Q^{−(M−c)}` with `K = B = c = 1` is
`M·Q^{−(M−1)}` ✓"*.

**⚠ WHAT THIS NODE IS AND IS NOT.** It is the **ground instance** of `(A2-RATE)`, unconditional. It
is **not** `(A2-RATE)` itself, which is a species *pinned onto `P(k)`'s fourth member* and whose
general form is a hypothesis — `EFF.GENIND.151`'s TEETH: *"nothing for the general species, which is
why it is a hypothesis pin and not a theorem"*, disposition `signed vacuity disclosure` at general
`(μ, d)`. Chapter H's `RateSpecies` predicate (H.65) is the general form; this node discharges it at
`μ = 2`.

**ARITHMETIC AUDIT (recomputed fresh at `Q = 2` and `Q = 3`).** `Q = 2, N = 5`: `u = 32`,
`32/2^8 = 0.125`; bound `5/2^4 = 0.3125` ✓. `Q = 3, N = 5`: `u = 189`, `189/3^8 = 189/6561 ≈
0.0288`; bound `5/3^4 = 5/81 ≈ 0.0617` ✓. `Q = 2, N = 2`: `2/2^2 = 0.5`; bound `2/2 = 1` ✓ (the
tightest cell). `Q = 3, N = 2`: `3/9 = 1/3`; bound `2/3` ✓. The bound is never tight but is within a
factor `< 4` at every cell checked — consistent with `EFF.GENIND.153`'s claim that *"the `m = 2`
closed forms realize `(K, B, c) = (1, 1, 1)` — the ansatz is sharp at the ground instance."*

**TEETH.** `EFF.GENIND.150`'s leg C → **Lean theorem**; `EFF.GENIND.151`'s `signed vacuity
disclosure` at general `(μ, d)` is **carried unchanged** (H.65 is a predicate, not a theorem).

**ENVIRONMENT.** ENV-H1.

---

### NODE H.29 [lemma] [fresh]

**STATEMENT.** *The `uTwo` audit.* Closed numeric facts at two values of `Q`:
`uTwo 2 1 = 1`, `uTwo 2 2 = 2`, `uTwo 2 3 = 6`, `uTwo 2 4 = 12`, `uTwo 2 5 = 32`, `uTwo 2 6 = 64`;
`uTwo 3 1 = 1`, `uTwo 3 2 = 3`, `uTwo 3 3 = 15`, `uTwo 3 4 = 45`, `uTwo 3 5 = 189`,
`uTwo 3 6 = 567`.

**SIGNATURE.**
```lean
namespace Uniformity.Density.Induction

theorem uTwo_audit_two :
    uTwo 2 1 = 1 ∧ uTwo 2 2 = 2 ∧ uTwo 2 3 = 6 ∧ uTwo 2 4 = 12 ∧ uTwo 2 5 = 32 ∧ uTwo 2 6 = 64

theorem uTwo_audit_three :
    uTwo 3 1 = 1 ∧ uTwo 3 2 = 3 ∧ uTwo 3 3 = 15 ∧ uTwo 3 4 = 45 ∧ uTwo 3 5 = 189 ∧ uTwo 3 6 = 567
```

**DEPENDS.** H.23.

**PROOF.** `by decide` on each conjunct; if the recursion's `decide` is too deep,
`by simp [uTwo, Finset.sum_range_succ]; norm_num`.

**SIZE.** 10 lines.

**SOURCE.** the values are this blueprint's own recomputation from `EFF.GENIND.150`'s recursion and
closed form (audited at H.25 and H.26); the corpus displays no `uTwo` table, only the symbolic legs.

**⚠ WHY A `q = 3` COLUMN IS MANDATORY HERE (the G.23 lesson, stated once for the whole chapter).**
Chapter G's `G.23` count formula was **refuted** because the two candidate laws
`q^{2N−2k−1}` and `q^{2N−2k−2}` **agree exactly at `q = 2`**, and every numeric cross-check in that
chapter ran at `q = 2` (`blueprint/CHAP-G` AMENDMENT §A-1: *"The two agree exactly when `q = 2` —
which is why every numeric cross-check in this chapter (all computed at `q = 2`) missed it"*). Here
the same trap is live in three places: `(Q−1) = 1` at `Q = 2` kills every letter factor, so a missing
or spurious `(Q−1)` is invisible; `Q^k` vs `Q^{k·c(m)}` agree at `m = 2`; and the α-term's
composition weights coincide at `Q = 2` (H.20's audit). **Every count-formula node in this chapter
carries both columns; a node whose audit is `q = 2`-only is a blueprint defect.**

**TEETH.** `arithmetic recount` (self-supplied) → **Lean theorem**; also the regression that a
future change to `uTwo`'s definition cannot pass silently.

**ENVIRONMENT.** ENV-H1.

---

## 6. §6 — ARITHMETIC III: THE PRICING INEQUALITIES

### NODE H.30 [lemma] [fresh]

**STATEMENT.** *The α-leg's geometric sum.* For `2 ≤ Q`, `1 ≤ c` and every `n`, in `ℝ`:
`Σ_{k<n} (Q−1) * (Q:ℝ)^(−(c*(k+1)) : ℤ) ≤ 1`.
(The corpus's `Σ_{k≥1}(Q−1)Q^{−k·c(m)} ≤ 1 for c(m) ≥ 1`; the side condition is exactly
`Q ≤ Q^c`.)

**SIGNATURE.**
```lean
namespace Uniformity.Density.Induction

theorem alpha_geom_partial_le_one (Q c : ℕ) (hQ : 2 ≤ Q) (hc : 1 ≤ c) (n : ℕ) :
    ∑ k ∈ Finset.range n, ((Q : ℝ) - 1) * ((Q : ℝ) ^ (c * (k + 1)))⁻¹ ≤ 1
```

**DEPENDS.** none · mathlib `geom_sum_eq`, `Finset.geom_sum_le`, `one_sub_inv_pos`.

**PROOF.**
1. set `r := ((Q:ℝ)^c)⁻¹`; then the `k`-th term is `(Q−1) * r^(k+1) = (Q−1)·r·r^k`.
2. `0 < r < 1` from `2 ≤ Q`, `1 ≤ c` (`one_lt_pow`, `inv_lt_one`).
3. `Σ_{k<n} r^k ≤ (1−r)⁻¹` (mathlib's `geom_sum_le_of_lt_one` / `tsum_geometric_lt_one`-style
   partial bound).
4. hence the sum is `≤ (Q−1)·r·(1−r)⁻¹`, and the goal reduces to
   `(Q−1)·r ≤ 1 − r`, i.e. `(Q−1)·Q^{−c} + Q^{−c} ≤ 1`, i.e. `Q·Q^{−c} ≤ 1`, i.e. `Q ≤ Q^c` ✓
   (`Nat.pow_le_pow_right` with `1 ≤ c`, cast to `ℝ`).

**SIZE.** 18 lines.

**SOURCE.** `EFF.GENIND.153` (`ANNEX-THEOREM GENIND.C′`'s α-leg, verbatim: *"`Σ_{k≥1}(Q−1)Q^{−k·c(m)}
≤ 1` for `c(m) ≥ 1`"*), with the spec's own audit: *"requires
`(Q−1)·Q^{−c(m)}/(1−Q^{−c(m)}) ≤ 1` ⟺ `(Q−1) ≤ Q^{c(m)} − 1` ⟺ `Q ≤ Q^{c(m)}` ✓ for `c(m) ≥ 1`,
i.e. `m ≥ 2` ✓ — the displayed side condition is exactly right and tight at `m = 2`."*

**⚠ TIGHTNESS DECLARED.** The inequality is an **equality** at `c = 1` (`m = 2`) in the limit:
`(Q−1)/Q + 1/Q = 1`. So the partial-sum form is the right statement — a strict-inequality version
would be false in the limit at `m = 2`, which is the chapter's ground instance. **Hypothesis at its
true minimum: `1 ≤ c`, not `2 ≤ c`.**

**TEETH.** none in the corpus (the closure is `PROOF-ONLY`, `EFF.GENIND.153`) → **Lean theorem**,
the only available disposition, and the chapter supplies it.

**ENVIRONMENT.** ENV-H1.

---

### NODE H.31 [lemma] [fresh]

**STATEMENT.** *The height-sum bound.* For `2 ≤ Q` and every `n`, in `ℝ`:
`Σ_{H<n} ((Q:ℝ)^(H:ℝ))^(−1/2) ≤ (1 − (2:ℝ)^(−1/2))⁻¹`, i.e.
`Σ_{H<n} (Q:ℝ)^(−H/2) ≤ (1 − 2^(−1/2))⁻¹`.

**SIGNATURE.**
```lean
namespace Uniformity.Density.Induction

theorem height_geom_partial_le (Q : ℕ) (hQ : 2 ≤ Q) (n : ℕ) :
    ∑ H ∈ Finset.range n, ((Q : ℝ) ^ (H : ℝ))⁻¹ ^ ((1:ℝ)/2)
      ≤ (1 - ((2:ℝ) ^ ((1:ℝ)/2))⁻¹)⁻¹
```

**DEPENDS.** none · mathlib `Real.rpow_natCast`, `geom_sum_le_of_lt_one`.

**PROOF.**
1. rewrite the summand as `r^H` with `r := ((Q:ℝ)^((1:ℝ)/2))⁻¹` (`Real.rpow_natCast`,
   `Real.rpow_mul`).
2. `0 < r ≤ ((2:ℝ)^((1:ℝ)/2))⁻¹ < 1` from `2 ≤ Q` (`Real.rpow_le_rpow` monotone in the base).
3. `Σ_{H<n} r^H ≤ (1−r)⁻¹` (partial geometric bound), and `(1−r)⁻¹ ≤ (1−r₀)⁻¹` where
   `r₀ := ((2:ℝ)^((1:ℝ)/2))⁻¹`, by `one_div_le_one_div_of_le` and `r ≤ r₀`.

**SIZE.** 18 lines. **The `rpow` bookkeeping is the whole cost.** Sanctioned simplification if it
fights: state the bound with the explicit constant `4` in place of `(1−2^{−1/2})⁻¹ ≈ 3.4142` — every
consumer (H.72, H.71) uses only *some* `N`-independent constant, and `4` is `N`-independent. Record
the substitution as a RE-PLAN so §16 can flag it.

**SOURCE.** `EFF.GENIND.189` (`ANNEX-LEMMA GENIND-C2`'s (C2.4), verbatim: *"`Σ_{H≥0}Q^{-H/2}
≤(1-2^{-1/2})^{-1}`"* because `Q ≥ 2`), with the spec's audit *"≈ 3.414 ✓"*; `EFF.GENIND.198`
(C2Q's closing, the same sum).

**TEETH.** none in the corpus (`signed vacuity disclosure`: the `Q`-normalized lemma is unexercised,
`EFF.GENIND.189`) → **Lean theorem**.

**ENVIRONMENT.** ENV-H1.

---

### NODE H.32 [lemma] [fresh]

**STATEMENT.** *The supporting-line sum.* For `S, H : ℕ`:
`2 * (Σ_{r<S} ((r+1) * H)) = S * (S + 1) * H`.
(The corpus's `Σ_{r=1}^{S} rH/S = (S+1)H/2 = b_S·H` after dividing by `S`; the `ℕ` form multiplies
through by `2S` and states the numerator identity, which is what the pricing consumes.)

**SIGNATURE.**
```lean
namespace Uniformity.Density.Induction

theorem two_mul_supportLine_sum (S H : ℕ) :
    2 * (∑ r ∈ Finset.range S, (r + 1) * H) = S * (S + 1) * H
```

**DEPENDS.** none · mathlib `Finset.sum_range_id_mul_two`, `Gauss_sum`.

**PROOF.**
1. `Finset.sum_mul` backwards: the sum is `(Σ_{r<S}(r+1)) * H`.
2. `Σ_{r<S}(r+1) = Σ_{r ∈ range (S+1)} r` (`Finset.sum_range_succ_comm` / `Finset.sum_range_id'`),
   and `2 * Σ_{r ∈ range (S+1)} r = S * (S+1)` (`Finset.sum_range_id_mul_two`).
3. `ring`.

**SIZE.** 8 lines.

**SOURCE.** `EFF.GENIND.204` (`C2-G3`, verbatim: *"Relative to the side's right endpoint, its `S`
coefficient columns have supporting-line heights `H/S, 2H/S, …, SH/S`. Therefore the number of forced
`Q`-digit levels is at least `Σ_{r=1}^{S}(⌈rH/S⌉−1) ≥ Σ_{r=1}^{S} rH/S − O_m(1) = (S+1)/2·H −
O_m(1)`"*), with the spec's audit *"`Σ_{r=1}^{S} rH/S = (H/S)·S(S+1)/2 = (S+1)H/2` ✓ exact"*;
`EFF.GENIND.189` (the same sum at `S = L`, `(C2.2)`).

**⚠ THE CEILING TERM IS NOT IN THIS NODE.** `C2-G3`'s inequality has an `O_m(1)` absorbing ceiling
errors, already-pinned level-zero digits and the residual-letter census. Chapter H carries that slack
as `StageInterface.slack` (H.09), a field, so the *identity* is what this node proves and the *bound*
is H.33's. Putting the `O_m(1)` inside this node would make it unprovable (it is a genre-dependent
constant, not a formula).

**TEETH.** none in the corpus (`EFF.GENIND.204`: *"the three quartic checks are unchanged by
construction, so no measured number tests the strengthening"*) → **Lean theorem**.

**ENVIRONMENT.** ENV-H1.

---

### NODE H.33 [lemma] [fresh]

**STATEMENT.** *The domination `b_S − a ≥ 1/2`, subtraction-free.* Two clauses.
(i) `2 * (e * f) ≤ e * μ * f` when `2 ≤ μ` — i.e. `2a ≤ L`.
(ii) if additionally `L ≤ S` then `2 * (e * f) ≤ S`, i.e. `2a ≤ S`, i.e.
`(S+1)/2 − a ≥ 1/2` — the `(C2E.3)` domination.

**SIGNATURE.**
```lean
namespace Uniformity.Density.Induction

theorem two_mul_a_le_sideLen {e f m : ℕ} (hm : 2 ≤ m) : 2 * (e * f) ≤ e * m * f

theorem two_mul_a_le_S {e f m S : ℕ} (hm : 2 ≤ m) (hS : e * m * f ≤ S) :
    2 * (e * f) ≤ S
```

**DEPENDS.** none.

**PROOF.**
1. (i) `2 * (e*f) = e * 2 * f ≤ e * m * f` by `Nat.mul_le_mul_right` / `Nat.mul_le_mul_left` with
   `hm`.
2. (ii) `le_trans (two_mul_a_le_sideLen hm) hS`.

**SIZE.** 6 lines.

**SOURCE.** `EFF.GENIND.204` (`(C2E.3)`: *"Since `L=e\mu\gamma\ge2e\gamma=2a`,
`\frac{S+1}{2}-a \ge\frac{L+1}{2}-a \ge\frac12`"*), with the spec's audit *"`L = eμγ ≥ 2eγ = 2a` ✓
(μ ≥ 2) — so `(L+1)/2 − a ≥ (2a+1)/2 − a = 1/2` ✓, and a fortiori `(S+1)/2 − a ≥ 1/2` ✓"*;
`EFF.GENIND.189` (`(C2.0)`: `L ≥ 2a`, `b := (L+1)/2 ≥ a + 1/2`).

**⚠ WHY THE `2 *` FORM.** `b_S = (S+1)/2` is a half-integer whenever `S` is even, and `ℕ` division
would floor it — the exact failure mode that would silently weaken `hprice` (H.09). Every
chapter-H statement about `b_S` is multiplied through by `2`; this node is the one that licenses it,
because `2a ≤ S` says exactly that `2(b_S − a) = S + 1 − 2a ≥ 1` is a genuine positive `ℕ`.

**TEETH.** none in the corpus → **Lean theorem**. This node is a DEPENDS of `StageInterface`'s
`hprice` field being *satisfiable* (H.38/H.42 exhibit instances) and of H.72's exponent computation.

**ENVIRONMENT.** ENV-H1.

---

### NODE H.34 [lemma] [fresh]

**STATEMENT.** *The exponent composition.* If `D + M = N` then for real `ρ ≤ Q^(−(D−1))` and
`δ ≤ Q^(−(M−c))` with `ρ, δ ≥ 0` and `c ≤ M`: `ρ * δ ≤ Q^(−(N−1−c))`. Stated in `ℕ`-exponent form
(subtraction-free) as: `(D − 1) + (M − c) = N − 1 − c` given `1 ≤ D`, `c ≤ M`, `D + M = N`.

**SIGNATURE.**
```lean
namespace Uniformity.Density.Induction

theorem exp_compose {D M N c : ℕ} (hD : 1 ≤ D) (hc : c ≤ M) (h : D + M = N) :
    (D - 1) + (M - c) = N - 1 - c

theorem mul_le_of_exp_compose {Q : ℕ} (hQ : 2 ≤ Q) {D M N c : ℕ} (hD : 1 ≤ D) (hc : c ≤ M)
    (h : D + M = N) {ρ δ : ℝ} (hρ0 : 0 ≤ ρ) (hδ0 : 0 ≤ δ)
    (hρ : ρ ≤ ((Q : ℝ) ^ (D - 1))⁻¹) (hδ : δ ≤ ((Q : ℝ) ^ (M - c))⁻¹) :
    ρ * δ ≤ ((Q : ℝ) ^ (N - 1 - c))⁻¹
```

**DEPENDS.** none.

**PROOF.**
1. `exp_compose`: `omega`.
2. `mul_le_of_exp_compose`: `mul_le_mul hρ hδ hδ0 (by positivity)` then rewrite the product of
   inverses by `← inv_mul_eq_inv_mul`, `pow_add`, and `exp_compose`.

**SIZE.** 10 lines.

**SOURCE.** `EFF.GENIND.152` (`GENIND-C1`(iii), the GROWING regime: *"with (i),
`contribution_l ≤ K·N^B·Q^{−(D_l−1)−(M_l−c)} = K·N^B·Q^{−(N−c−1)}` — the exponents COMPOSE EXACTLY
because `D_l + M_l = N`"*), with the spec's audit *"`Q^{−(D_l−1)}·Q^{−(M_l−c)} = Q^{−(D_l+M_l−1−c)} =
Q^{−(N−1−c)}` ✓ using `D_l + M_l = N`"* and its honest note that `D_l + M_l = N` is `M_l := N − D_l`
by definition, so *"leg D verifies a definitional identity against hull data — a consistency check on
the extraction, not on the algebra."*

**TEETH.** `EFF.GENIND.152`'s machine leg D (the depth identity at six committed extractions) →
**Lean theorem**, with the corpus's own scoping preserved: the *identity* is definitional, and what
leg D checks is the extraction. The extraction is geometric and has no node.

**ENVIRONMENT.** ENV-H1.

---

### NODE H.35 [lemma] [fresh]

**STATEMENT.** *The polynomial-dominance step.* For `1 ≤ m`, `1 ≤ B` and `N ≥ m`, in `ℕ`:
`(N − m)^B + m * (N − m)^(B−1) ≤ N^B`, and `(N−m)^B < N^B` when `1 ≤ m ≤ N`.
(The usable form of the corpus's *"`N^B − (N−m)^B` has positive leading coefficient `m·B·N^{B−1}`"*:
the gap dominates `m·(N−m)^{B−1}`, which is what the `K`-choice needs.)

**SIGNATURE.**
```lean
namespace Uniformity.Density.Induction

theorem pow_sub_dominance {N m B : ℕ} (hm : 1 ≤ m) (hmN : m ≤ N) (hB : 1 ≤ B) :
    (N - m) ^ B + m * (N - m) ^ (B - 1) ≤ N ^ B
```

**DEPENDS.** none · mathlib `Nat.pow_le_pow_left`, `Finset.geom_sum₂`-style factoring or the
binomial `add_pow_le`.

**PROOF.**
1. write `N = (N−m) + m` (`Nat.sub_add_cancel hmN`) and set `A := N − m`.
2. the goal is `A^B + m*A^(B−1) ≤ (A+m)^B`.
3. `(A+m)^B ≥ A^B + B * A^(B−1) * m` by the binomial lower bound (`Nat.add_pow_le` or
   `Finset.sum` over the two lowest terms of `add_pow`); with `1 ≤ B` this dominates
   `A^B + m*A^(B−1)`.
4. `Nat.add_le_add_left` plus `Nat.le_mul_of_pos_left` with `1 ≤ B`.

**SIZE.** 14 lines. The binomial two-term lower bound is the one non-`omega` step; if mathlib's
`add_pow_le` is awkward, prove `A^B + B*A^(B−1)*m ≤ (A+m)^B` by induction on `B` (three lines).

**SOURCE.** `EFF.GENIND.153` (`GENIND.C′`'s `K`-choice: *"`K` large enough that `K·[N^B − (N−m)^B]`
dominates the head + β coefficients (a degree-`(B−1)` polynomial inequality, satisfiable since
`N^B − (N−m)^B` has positive leading coefficient `m·B·N^{B−1}`)"*), with the spec's audit
*"`N^B − (N−m)^B` has leading term `mBN^{B−1}` ✓ (binomial), so a degree-`(B−1)` polynomial
inequality is satisfiable for large `K` ✓"*.

**TEETH.** none (`EFF.GENIND.153`: *"the induction itself is unguarded — no battery row exercises a
lexicographic induction"*, disposition **PROOF-ONLY**) → **Lean theorem**.

**ENVIRONMENT.** ENV-H1.

---

### NODE H.36 [lemma] [fresh]

**STATEMENT.** *The entry-mass codimension.* The relative mass of `{v(a₀) ≥ D}` inside a cluster
system's state space is `Q^(−(D−1))`: in exponent form, the pinned digit count is `d*(D−1)` out of
`d*(N−1)` at coordinate `0`, so the codimension is `D − 1` in `Q`-digits. Stated subtraction-free:
for `1 ≤ D ≤ N`, `d * (D − 1) + d * (N − D) = d * (N − 1)`.

**SIGNATURE.**
```lean
namespace Uniformity.Density.Induction

theorem entry_codim (d D N : ℕ) (hD : 1 ≤ D) (hDN : D ≤ N) :
    d * (D - 1) + d * (N - D) = d * (N - 1)
```

**DEPENDS.** none.

**PROOF.** `omega` after `rcases` on `D` and `N` to clear the `ℕ`-subtractions
(`obtain ⟨D', rfl⟩ : ∃ D', D = D' + 1`; `obtain ⟨E, rfl⟩ : ∃ E, N = D + E`).

**SIZE.** 6 lines.

**SOURCE.** `EFF.GENIND.152` (`GENIND-C1`(i), verbatim: *"the `j = 0` term of the min gives
`D_l ≤ v(a₀)`, so the genre lies inside `{v(a₀) ≥ D_l}`, whose relative mass is exactly
`Q^{−(D_l−1)}` (π-levels `1..D_l−1` of `a₀` pinned to zero — `d·(D_l−1)` q-digits; level 0 is pinned
in every state)"*), with the spec's audit reproducing the count exactly.

**⚠ THE `j = 0` STEP IS GEOMETRIC AND IS NOT IN THIS NODE.** `D_l = min_j(v(a_j) + j·k_l) ≤ v(a₀)`
is a property of the polygon's content and has no node (honesty item H-3). What chapter H proves is
the *codimension arithmetic* once the containment is granted; the containment enters H.67/H.72 as a
hypothesis on the schema.

**ARITHMETIC AUDIT (recomputed fresh at `q = 2` and `q = 3`, against the corpus's three committed
loci).** M6 (`EFF.GENIND.33`): locus `(q−1)²q^{6N−17}`, total `q^{6(N−1)}`, so
`ρ = (q−1)²q^{−11}`; `D = 4` gives the bound `Q^{−3} = q^{−3}`. Check `(q−1)²q^{−11} ≤ q^{−3}`
⟺ `(q−1)² ≤ q⁸`: at `q = 2`, `1 ≤ 256` ✓; at `q = 3`, `4 ≤ 6561` ✓; at `q = 5`, `16 ≤ 390,625` ✓.
PSTEEP3 at `(q,N) = (2,5)`: locus `32 = 2⁵` of `2^{3·4} = 2^{12}` ⟹ `ρ = 2^{−7}`, bound at `D = 3` is
`2^{−2}` ✓. PSTEEP4 at `(2,6)`: locus `512 = 2⁹` of `2^{4·5} = 2^{20}` ⟹ `ρ = 2^{−11}`, bound at
`D = 4` is `2^{−3}` ✓. **All three of `EFF.GENIND.152`'s machine-leg-E instances reproduce, and the
M6 check is carried at three values of `q`.**

**TEETH.** `EFF.GENIND.152`'s machine leg E (the prefactor bound at three committed loci) →
**Lean theorem** for the codimension arithmetic; leg E's own reach limit (*"legs D/E cover six
extractions and three loci, all at `n ≤ 6`"*) is carried as a `signed vacuity disclosure` on the
*geometric* containment, which has no node.

**ENVIRONMENT.** ENV-H1.

---

### NODE H.37 [lemma] [fresh]

**STATEMENT.** *The genre-count polynomial bound.* For `m, N : ℕ` with `1 ≤ N`, the number of
`(partition-arrangement type, slope tuple)` pairs available to a β-genre at window `N` is at most
`p * N^m` where `p` is the number of arrangement types at multiplicity `m` — because each of at most
`m` sides carries one integer slope in `[1, N−1]`. Formalized as: the set of slope tuples
`{s : Fin m → ℕ | ∀ i, 1 ≤ s i ∧ s i ≤ N − 1}` is finite with cardinality `≤ N^m`.

**SIGNATURE.**
```lean
namespace Uniformity.Density.Induction

theorem card_slopeTuples_le (m N : ℕ) :
    Nat.card {s : Fin m → ℕ // ∀ i, 1 ≤ s i ∧ s i ≤ N - 1} ≤ N ^ m
```

**DEPENDS.** none · mathlib `Nat.card_pi`, `Fintype.card_fun`, `Set.Finite.subset`.

**PROOF.**
1. the subtype injects into `Fin m → Fin N` by `s ↦ fun i => ⟨s i, by omega⟩` (using
   `s i ≤ N − 1 < N`, which needs `1 ≤ N`; when `N = 0` the subtype is empty and the bound is
   `0 ≤ 0`).
2. `Nat.card_le_card_of_injective` then `Nat.card_fun`/`Fintype.card_fun`: `(Fin N)^(Fin m)` has
   cardinality `N^m`.
3. `N = 0` case: `1 ≤ s i` and `s i ≤ 0 − 1 = 0` (in `ℕ`) is contradictory, so the subtype is empty.

**SIZE.** 14 lines.

**SOURCE.** `EFF.GENIND.152` (`GENIND-C1`(iv), verbatim: *"a β-genre's datum at window `N` is a
partition arrangement of `m` (finitely many types for fixed `m`) plus one integer slope per side, each
slope `≤ v(a₀) ≤ N−1`: at most `p̃(m)·N^m` live genres — polynomial in `N` of degree `≤ m`"*), with
the spec's audit *"slopes `≤ v(a₀) ≤ N−1`, at most `m` sides ⟹ at most `N^m` slope tuples times
`p̃(m)` partition types ✓"*.

**⚠ `p̃(m)` IS NOT DEFINED HERE.** The corpus's `p̃(m)` is the number of *arrangement types* — a
partition-of-`m` count refined by side/vertex structure, i.e. frame-grammar data (chapter C). This
node proves the `N^m` factor, which is the `N`-dependent half and the only half the rate closure
needs (`p̃(m)` is `N`-independent, so it is absorbed into the closure's `K`). H.71's statement carries
`p` as an opaque `ℕ` parameter. **A node attempting to compute `p̃(m)` has left the chapter.**

**TEETH.** none (`EFF.GENIND.152`'s (iv) is `computation`, unguarded) → **Lean theorem**.

**ENVIRONMENT.** ENV-H1.

---

## 7. §7 — ARITHMETIC IV: THE GENRE LAWS, THEIR FLOORS, THE TOWER THRESHOLDS

> Every law here is a **defined function of `(q, N, parameter)`** plus a **visibility floor**, and
> every node states the floor. That is not decoration: two of the corpus's confirmed defects were
> *missing floors* (`EFF.GENIND.162`, `EFF.GENH4.06`), one of them producing a NON-INTEGER count. The
> floors are stated as hypotheses of the law's *inhabitedness*, never as hypotheses of the law's
> *definition* — a defined `ℕ`-valued function must be total.

### NODE H.38 [def+lemma] [fresh]

**STATEMENT.** *The quartic e-first law `CS4-E(h)` and its floor.* Define
`lawE q N h = (q − 1) * q^(4*N − 5*h − 3)` for `q, N, h : ℕ`. Its **visibility floor** is
`2*h + 1 ≤ N`, because the genre's entry height is `v(a₀) = 2h` and `DRAIN` fires at `v(a₀) ≥ N`.
Two clauses: (i) the floor implies the exponent is honest, `5*h + 3 ≤ 4*N`; (ii) the floor **fails**
at `(N, h) = (2, 1)` while `lawE q 2 1 = q − 1 ≠ 0` for `q ≥ 2` — the unfloored display's
false positive.

**SIGNATURE.**
```lean
namespace Uniformity.Density.Induction

/-- `CS4-E(h)` — the quartic e-first genre's per-centre opening locus, `(q−1)q^{4N−5h−3}`
(`GENIND` §S5.3 = `W-12` §S2.5's `QRT-G2(h;(1²))`).  Total by construction; the visibility floor
`2h ≤ N−1` is a hypothesis of `lawE_floor_*`, not of the definition. -/
def lawE (q N h : ℕ) : ℕ := (q - 1) * q ^ (4 * N - 5 * h - 3)

theorem lawE_exp_honest {N h : ℕ} (hfl : 2 * h + 1 ≤ N) : 5 * h + 3 ≤ 4 * N

theorem lawE_floor_fails_at_two_one {q : ℕ} (hq : 2 ≤ q) :
    ¬ (2 * 1 + 1 ≤ 2) ∧ lawE q 2 1 ≠ 0
```

**DEPENDS.** none.

**PROOF.**
1. `lawE_exp_honest`: `omega` (from `2h+1 ≤ N`: `4N ≥ 8h+4 ≥ 5h+3` for `h ≥ 0` — check
   `8h+4 − 5h − 3 = 3h+1 ≥ 0` ✓).
2. `lawE_floor_fails_at_two_one`: the first conjunct is `by omega` (`3 ≤ 2` is false); the second:
   `4*2 − 5*1 − 3 = 0`, so `lawE q 2 1 = (q−1)*q^0 = q−1 ≠ 0` by `hq` and `Nat.sub_ne_zero_of_lt`.

**SIZE.** 12 lines.

**SOURCE.** `EFF.GENIND.48` (the law and its landed `[r1, PE1-M3]` floor, verbatim: *"**CS4-E(h)**
[e-first: `e = 2`, `ψ` linear, `μ = 2`; = `QRT-G2(h;(1²))`]: slope `h/2`, `h` odd, residual `(y−z)²`:
`(q−1)·q^{4N−5h−3}`, VISIBILITY FLOOR `2h ≤ N−1` … at `(N, h) = (2, 1)` the unfloored display would
return `q−1` against a true locus of 0"*).

**ARITHMETIC AUDIT (recomputed fresh at `q ∈ {2, 3, 5}`, against `EFF.GENIND.99`'s preregistered
spots).** `(q,N,h) = (2,6,1)`: `4·6 − 5 − 3 = 16`, `lawE = 1·2^16 = 65,536` ✓ = the reported
`E4(1) = 65,536`. `(3,4,1)`: `16 − 5 − 3 = 8`, `lawE = 2·3^8 = 13,122` ✓ = the reported value.
`(5,3,1)`: `12 − 5 − 3 = 4`, `lawE = 4·5^4 = 2,500` ✓ = the reported value. **All three
never-measured spots reproduce, at three distinct `q`.** Floor checks: `(2,6,1)` needs `3 ≤ 6` ✓;
`(3,4,1)` needs `3 ≤ 4` ✓; `(5,3,1)` needs `3 ≤ 3` ✓ **at equality** — so the `q = 5` spot is the
floor-adjacent cell, and it is inhabited.

**TEETH.** `GT-DEPTH0 [SAME, both directions]` (`EFF.GENIND.48`, §S11 P-3, the three `E4(1)` spots,
exact) → **Lean theorem**; `GT-CRIT` (the genre appears exactly where the grammar predicts and is
ABSENT below its floor) → **Lean theorem** for the floor half; `GT-T-CS` at its preregistered count
12 → **executable regression** retained (it is a per-row grammar check, not a law check).

**ENVIRONMENT.** ENV-H1.

---

### NODE H.39 [lemma] [fresh]

**STATEMENT.** *The four-summand exponent identity behind `lawE`.* For `h = 2t + 1` (h odd) and
`N ≥ 4t + 3`, the four free-digit counts of the `(2,2)`-E stage sum to `lawE`'s exponent:
`(N − (t+1)) + (N − 1 − (2t+1)) + (N − (3t+2)) + (N − 1 − (4t+2)) + (10*t + 8) = 4 * N`,
i.e. the sum is `4N − 10t − 8 = 4N − 5h − 3`.

**SIGNATURE.**
```lean
namespace Uniformity.Density.Induction

theorem lawE_exp_four_summands {N t : ℕ} (hN : 4 * t + 3 ≤ N) :
    (N - (t + 1)) + (N - 1 - (2 * t + 1)) + (N - (3 * t + 2)) + (N - 1 - (4 * t + 2))
      + (10 * t + 8) = 4 * N

theorem lawE_exp_odd {N t : ℕ} (hN : 4 * t + 3 ≤ N) :
    4 * N - 5 * (2 * t + 1) - 3 = 4 * N - (10 * t + 8)
```

**DEPENDS.** none.

**PROOF.** both `by omega` (the hypothesis clears every `ℕ`-subtraction: `4t+3 ≤ N` gives
`t+1 ≤ N`, `2t+2 ≤ N`, `3t+2 ≤ N`, `4t+3 ≤ N`).

**SIZE.** 8 lines.

**SOURCE.** `EFF.GENIND.68` (`LEMMA GENIND-4`'s free-digit total, verbatim: *"Free-digit total:
`(N − (h+1)/2) + (N−1−h) + (N − (3h+1)/2) + (N−1−2h) = 4N − 5h − 3` ✓ — matching the opening law
exactly, which is the no-over/undercount check"*), with the spec's audit reproducing it; the same
four-summand pattern at `EFF.GENIND.50` (`CS5-V1E2`).

**⚠ WHY `h = 2t+1` AND NOT `h` WITH `Odd h`.** The corpus's four summands contain `(h+1)/2` and
`(3h+1)/2`, both of which need `h` odd to be integers. Substituting `h = 2t+1` makes every summand a
literal `ℕ` expression and the whole identity `omega`-closable; carrying `Odd h` and `h/2` would
introduce two `ℕ`-divisions that `omega` cannot see through. **The `Odd h` form is the wrong
signature** and a node stating it should be returned.

**TEETH.** as H.38 (`GT-DEPTH0`); this node is the *no-over/undercount* check the corpus names, so
it inherits `EFF.GENIND.68`'s `accepted-with-decorrelation-supplied` (the QSCOUT22 `Q22-B`
cross-derivation) → **Lean theorem**.

**ENVIRONMENT.** ENV-H1.

---

### NODE H.40 [def+lemma] [fresh]

**STATEMENT.** *The quartic f-first law `CS4-F(k)`, its floor, and the ℤ-witness of the missing
floor.* Define `lawF q N k = (q * (q − 1) / 2) * q^(4*N − 10*k − 4)`. Its floor is `4*k + 1 ≤ N`
(entry heights `(4k, 3k, 2k, k)`, so `v(a₀) = 4k`). Two clauses: (i) the floor implies
`10*k + 4 ≤ 4*N`; (ii) at `(N, k) = (2, 1)` the exponent is **negative over `ℤ`**:
`(4:ℤ)*2 − 10*1 − 4 = −6` — the sharpest possible signature of a missing floor, since no `ℕ`-valued
count can have a negative exponent.

**SIGNATURE.**
```lean
namespace Uniformity.Density.Induction

/-- `CS4-F(k)` — the quartic f-first genre's per-centre opening locus,
`(q(q−1)/2)·q^{4N−10k−4}` (`GENIND` §S5.3; `#ψ = q(q−1)/2` monic irreducible quadratics). -/
def lawF (q N k : ℕ) : ℕ := (q * (q - 1) / 2) * q ^ (4 * N - 10 * k - 4)

theorem lawF_exp_honest {N k : ℕ} (hfl : 4 * k + 1 ≤ N) : 10 * k + 4 ≤ 4 * N

theorem lawF_exp_neg_below_floor : (4 : ℤ) * 2 - 10 * 1 - 4 = -6
```

**DEPENDS.** none.

**PROOF.**
1. `lawF_exp_honest`: `omega` (`4N ≥ 16k+4 ≥ 10k+4` ✓).
2. `lawF_exp_neg_below_floor`: `decide` / `norm_num`.

**SIZE.** 10 lines.

**SOURCE.** `EFF.GENIND.49` (the law, and **ANNEX R R4**'s correction: *"the visibility floor
`4k ≤ N−1` is missing … At `(q, N, k) = (2, 2, 1)` the unfloored display returns
`(2·1/2)·2^{8−10−4} = 2^{−6}` — a NON-INTEGER against a true locus of 0"*); `EFF.GENIND.163`
(`R4.1`, the floor re-derived from the heights `(4k, 3k, 2k, k)`); `EFF.GENIND.162` (`R4.0`, the
finding); `EFF.GENH4.06` (the same floor as an **admissibility** condition `N ≥ 4k+1`, landed at
`[r2]` with its own failure witness *"at `(N,k) = (4,1)` the true slot count is 3 but `4N−10k−4 = 2`"*).

**⚠ TWO DISTINCT FLOOR FACTS, BOTH LANDED.** `EFF.GENIND.49`'s floor is `4k ≤ N−1` (visibility:
below it the genre is empty). `EFF.GENH4.06`'s floor is `N ≥ 4k+1` (admissibility: below it the
displayed *slot-count form* is wrong even where the genre is nonempty — its witness is `(N,k) = (4,1)`
where `4k+1 = 5 > 4`). **They are the same inequality** (`4k ≤ N−1` ⟺ `4k+1 ≤ N`) and this node
states it once; the two *failure modes* are distinct and both are recorded, because a fleet agent who
proves only "the genre is empty" has not covered `EFF.GENH4.06`'s case.

**ARITHMETIC AUDIT (recomputed fresh at `q = 2` and `q = 3`).** `#{monic irreducible quadratics over
F_q} = (q²−q)/2 = q(q−1)/2` ✓ (`EFF.GENIND.47`'s audit). `(q,N,k) = (2,6,1)`:
`24 − 10 − 4 = 10`, `lawF = (2·1/2)·2^10 = 1,024` ✓ = `EFF.GENIND.99`'s reported `F4(1) = 1,024`.
`(3,4,1)`: the corpus reports **`F4 ABSENT (4k ≤ 3 impossible)`**; recomputed `4·1 = 4 > 3 = N−1` ✓
**absent** — *"the runner and the display disagreed; the runner was right"* (`EFF.GENIND.49`).
`(2,5,1)`: `20 − 10 − 4 = 6`, `lawF = 1·2^6 = 64` ✓ = `R4.2`'s check. `(2,8,1)` at `q = 2`:
`32 − 10 − 4 = 18`, `lawF = 2^18`. **Row-total cross-check** at `(2,6,n4)`:
`lawE + lawF = 65,536 + 1,024 = 66,560` ✓ = §S11 P-3's "row CS total 66,560 = E4+F4" and §S10's
independent cost-probe figure — **three independent agreements**, as `EFF.GENIND.49` records.
At `q = 3` the census factor is `3·2/2 = 3 ≠ 1`, so the `q = 3` column genuinely tests it (at `q = 2`
it is `1` and would hide a census error).

**TEETH.** `GT-DEPTH0` (the `F4(1)` spot exact; correctly ABSENT where the floor excludes it) →
**Lean theorem**; `R4.2`'s machine leg H (`genind_annexr_supp.py` @ `f5271e4`, GREEN — a
**source-code gate verification** reading the pinned runner's two gate lines `709`/`869` verbatim) →
**Lean theorem**, and note the asymmetry `EFF.GENIND.162` records: *"the runner had the floor and the
display did not, so no run could have surfaced it"*, which is why the floor must be in the blueprint.

**ENVIRONMENT.** ENV-H1.

---

### NODE H.41 [lemma] [fresh]

**STATEMENT.** *The quartic law audit.* Closed numeric facts:
`lawE 2 6 1 = 65536`, `lawE 3 4 1 = 13122`, `lawE 5 3 1 = 2500`, `lawF 2 6 1 = 1024`,
`lawF 2 5 1 = 64`, and `lawE 2 6 1 + lawF 2 6 1 = 66560`.

**SIGNATURE.**
```lean
namespace Uniformity.Density.Induction

theorem quartic_law_audit :
    lawE 2 6 1 = 65536 ∧ lawE 3 4 1 = 13122 ∧ lawE 5 3 1 = 2500 ∧
    lawF 2 6 1 = 1024 ∧ lawF 2 5 1 = 64 ∧ lawE 2 6 1 + lawF 2 6 1 = 66560
```

**DEPENDS.** H.38, H.40.

**PROOF.** `by decide` on each conjunct (`refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide`), or
`by norm_num [lawE, lawF]`.

**SIZE.** 8 lines.

**SOURCE.** `EFF.GENIND.99` (the preregistered spot values: `E4(1) = 65,536`, `F4(1) = 1,024`,
`DRAIN₀ = 32,768`, CS total `66,560` at `(·,2,6,n4)`; `E4(1) = 13,122` at `(·,3,4,n4)`;
`E4(1) = 2,500` at `(·,5,3,n4)`); `EFF.GENIND.163`/`R4.2` (`lawF 2 5 1 = 64`).

**⚠ WHY THE ROW TOTAL IS A CONJUNCT.** `EFF.GENIND.99`'s own audit closes with *"all twenty-one
preregistered spot values and all four tooth counts are re-derivable from the displayed laws"*, and
the row total is the one figure **three** instruments agree on (P-3's tally, the cost probe, and the
sum of the two laws). Landing the sum as a conjunct means a future edit to either law breaks the
audit loudly rather than silently rebalancing.

**TEETH.** `GT-DEPTH0` / `GT-CRIT` / `GT-T-CS` → **Lean theorem** (the node converts the
preregistration's derivability audit into a machine check).

**ENVIRONMENT.** ENV-H1.

---

### NODE H.42 [def+lemma] [fresh]

**STATEMENT.** *The quintic vertex-at-1 law `CS5-V1E2(h)` and its headroom.* Define
`lawV1E2 q N h = lawE q N h * (q^(N − (5*h+1)/2) − 1)` for `h` odd. Its exponent identity is
H.39's (the four-coordinate exponent is again `4N − 5h − 3`), and its **headroom factor vanishes
exactly at `N = (5h+1)/2`**: for `h = 2t+1`, `(5h+1)/2 = 5t + 3`, so the locus is `0` iff `N ≤ 5t+3`.

**SIGNATURE.**
```lean
namespace Uniformity.Density.Induction

/-- `CS5-V1E2(h)` — the quintic vertex-at-1 genre: `CS4-E`'s law times the split root's headroom
fibre `(q^{N−(5h+1)/2} − 1)` (`GENIND` §S5.3). -/
def lawV1E2 (q N h : ℕ) : ℕ := lawE q N h * (q ^ (N - (5 * h + 1) / 2) - 1)

theorem headroom_exp_odd (t : ℕ) : (5 * (2 * t + 1) + 1) / 2 = 5 * t + 3

theorem lawV1E2_eq_zero_iff {q N t : ℕ} (hq : 2 ≤ q) :
    lawV1E2 q N (2 * t + 1) = 0 ↔ (N ≤ 5 * t + 3 ∨ lawE q N (2 * t + 1) = 0)
```

**DEPENDS.** H.38, H.39.

**PROOF.**
1. `headroom_exp_odd`: `omega` (`(10t+6)/2 = 5t+3`).
2. `lawV1E2_eq_zero_iff`: `Nat.mul_eq_zero`; the right factor is `q^(N − (5t+3)) − 1 = 0` iff
   `q^(N−(5t+3)) ≤ 1` iff `N − (5t+3) = 0` (using `2 ≤ q`, `Nat.one_lt_pow`) iff `N ≤ 5t+3`. `omega`
   for the `ℕ`-subtraction.

**SIZE.** 14 lines.

**SOURCE.** `EFF.GENIND.50` (the law, verbatim: *"`(q−1)·q^{4N−5h−3}·(q^{N−(5h+1)/2} − 1)` — the
CS4-E law times the `b₀` headroom factor (the split root's fiber)"*, with the note that
`v(b₀)` must be *"NOT window-zero (else DRAIN fires first)"*), and the spec's audit re-deriving the
four-coordinate exponent and both spot values.

**ARITHMETIC AUDIT (recomputed fresh at `q = 2` and `q = 3`).** `(q,N,h) = (2,5,1)`, so `t = 0`,
`(5h+1)/2 = 3`: `lawE 2 5 1 = 1·2^{20−5−3} = 2^{12} = 4,096`; headroom `2^{5−3} − 1 = 3`;
`lawV1E2 = 4,096·3 = 12,288` ✓ = `EFF.GENIND.99`'s reported `V1E2(1) = 12,288`.
`(3,3,1)`: headroom `3^{3−3} − 1 = 0`, so `lawV1E2 = 0` ✓ = the corpus's *"NO CS key at all (V1E2
headroom = 0)"*. `(3,5,1)`: `lawE 3 5 1 = 2·3^{12} = 1,062,882`; headroom `3^2 − 1 = 8`;
`lawV1E2 = 8,503,056` — a `q = 3` cell with **both** factors non-degenerate, which is the cell the
`q = 2` column cannot supply (at `q = 2` the `(q−1)` factor is `1`). ✓

**TEETH.** `GT-DEPTH0` (the `V1E2(1)` spot exact at `(·,2,5,n5)`) · `GT-CRIT` (the zero-headroom
absence at `(·,3,3,n5)`) · `GT-T-CRIT` at its preregistered count 4 → **Lean theorem**, both
directions.

**ENVIRONMENT.** ENV-H1.

---

### NODE H.43 [lemma] [fresh]

**STATEMENT.** *The quintic vertex-at-4 genre's vertex condition and first visibility.* For
`v₄ ≥ 1` and `h` odd: lower-hull convexity at the vertex `(4, v₄)` requires the left slope `h/2` to
exceed the right slope `v₄`, i.e. `h > 2*v₄`, i.e. (h odd) `h ≥ 2*v₄ + 1`. Under that condition the
entry height `v₀ = v₄ + 2*h` satisfies `v₀ ≥ 7`, so the genre is first visible at `N ≥ 8`.

**SIGNATURE.**
```lean
namespace Uniformity.Density.Induction

theorem v4e2_vertex_condition {v₄ t : ℕ} (hv : 1 ≤ v₄) (h : 2 * v₄ < 2 * t + 1) :
    2 * v₄ + 1 ≤ 2 * t + 1

theorem v4e2_first_visible {v₄ t : ℕ} (hv : 1 ≤ v₄) (hvc : 2 * v₄ + 1 ≤ 2 * t + 1) :
    7 ≤ v₄ + 2 * (2 * t + 1)

theorem v4e2_needs_eight {v₄ t N : ℕ} (hv : 1 ≤ v₄) (hvc : 2 * v₄ + 1 ≤ 2 * t + 1)
    (hvis : v₄ + 2 * (2 * t + 1) ≤ N - 1) : 8 ≤ N
```

**DEPENDS.** none.

**PROOF.** all three `by omega`. (For `v4e2_first_visible`: `hvc` gives `t ≥ v₄ ≥ 1`, so
`v₄ + 2(2t+1) ≥ 1 + 2·3 = 7`.)

**SIZE.** 10 lines.

**SOURCE.** `EFF.GENIND.51` (the law and its `VERTEX CONDITION h ≥ 2v₄+1`, verbatim: *"hull convexity
at `(4, v₄)`: the left drop `(v₀−v₄)/4` must exceed the right drop `v₄` — caught by the battery's
smoke: at `h < 2v₄+1` the same digits read as a single `e = 5` decided side"*, and *"visibility
`v₀ = v₄+2h ≤ N−1`: first visible at `N = 8`"*), with the spec's audit re-deriving both and
§S14 claim group **C8**'s independent recount *"`v₀ = v₄ + 2h ≥ 1 + 2·(2v₄+1)|_{v₄=1} = 7 ⟹ N ≥ 8`"*.

**⚠ THIS GENRE'S LAW IS DERIVATION-ONLY AND GETS NO `def`.** `EFF.GENIND.51`'s own disposition is a
**`signed vacuity disclosure`**: *"the law is checked only in the negative direction
(PREDICTED-ABSENT), and the note says so in the display itself ("its law is derivation-only here").
The positive direction is unexercised at every window of every roster in this note."* Chapter H
therefore lands the *conditions* (which are proved geometry, and whose arithmetic is checkable) and
**does not define** `lawV4E2` — defining an unexercised law would create a Lean object with no
evidence behind it. The `(q−1)²q^{5N−5v₄−5h−4}` display stays in the spec.

**ARITHMETIC AUDIT (recomputed fresh).** The minimizing cell is `(v₄, h) = (1, 3)` giving `v₀ = 7`
✓; `(v₄,h) = (1,5)` gives `11`; `(2,5)` gives `12` — so `7` is the minimum ✓, and
`v₀ ≤ N−1` forces `N ≥ 8` ✓. Absence corroboration: §S11 P-3 reports "V4E2 ABSENT (the vertex
condition)" at `(·,2,5,n5)`; recomputed, `7 > N−1 = 4` ✓. **The pre-seal smoke's RED** (the predictor
listed `V4E2(1,1)` at `(Zp,2,4,n5)`) is exactly the `h < 2v₄+1` violation: `h = 1`, `v₄ = 1` gives
`2·1+1 = 3 > 1` ✗ ✓ — the condition this node proves is the one that killed the false prediction.

**TEETH.** `signed vacuity disclosure` for the law (carried unchanged); **Lean theorem** for the
vertex condition and the `N ≥ 8` threshold, which are the only claims with support.

**ENVIRONMENT.** ENV-H1.

---

### NODE H.44 [lemma] [fresh]

**STATEMENT.** *The comp-weighted pin census (the repaired GENH4 CRITICAL).* At the quartic genres,
a RAM or 2SIDED pin at slot height `m` is censused `q^(comp m) − 1`, where `comp m` is the pinned
slot's `F_q`-dimension. Three clauses:
(i) at genre E, `comp m = 1` identically, so the factor is `q − 1 = Q − 1` (`Q = q`);
(ii) at genre F below the boundary band (`m ≤ N − 1`), `comp m = 2`, so the factor is
`q^2 − 1 = Q − 1` (`Q = q²`);
(iii) at genre F **on** the boundary band (`N ≤ m ≤ N + k − 1`), `comp m = 1`, so the factor is
`q − 1`, which is **NOT** `Q − 1 = q² − 1` when `q ≥ 2`.

**SIGNATURE.**
```lean
namespace Uniformity.Density.Induction

/-- The pin census at a slot of `F_q`-dimension `c`: the nonzero readable vectors of an
`F_q`-subspace of dimension `c`. -/
def pinCensus (q c : ℕ) : ℕ := q ^ c - 1

theorem pinCensus_genreE (q : ℕ) : pinCensus q 1 = q - 1

theorem pinCensus_genreF_interior (q : ℕ) : pinCensus q 2 = q ^ 2 - 1

theorem pinCensus_band_ne_interior {q : ℕ} (hq : 2 ≤ q) :
    pinCensus q 1 ≠ pinCensus q 2
```

**DEPENDS.** none.

**PROOF.**
1. first two: `rfl` / `simp [pinCensus]`.
2. third: `q − 1 < q² − 1` for `q ≥ 2` (`Nat.sub_lt_sub_right` after `q < q^2`); `omega` with
   `Nat.lt_irrefl`.

**SIZE.** 10 lines.

**SOURCE.** `EFF.GENH4.07` (the `[r2]`-corrected census, verbatim: *"**`q^{comp}−1` per RAM and per
2SIDED pin** `[r2]` — `comp` = the pinned slot's `F_q`-dimension (S2.3): identically 1 at genre E
(every slot is one `F_q`-digit; the factor is `q−1 = Q−1`), and at genre F `comp(m) = 2` at pin
height `m ≤ N−1` (the factor is `q²−1 = Q−1`) but `comp(m) = 1` on the boundary band
`N ≤ m ≤ N+k−1` (a single in-window `F_q`-digit: census `q−1`, NOT `Q−1`)"*); `EFF.GENH4.25` (the
same clause at §S6.1, with the record that the sealed parenthetical *"declared only the EXPONENTS
comp-weighted; PE2 CRITICAL 1"*); `EFF.GENHN.79` (`GENHN-CAP-GEN`'s COUNT TRANSPORT: *"A nonzero
visible boundary pin has `Q^{comp(m)}−1` choices, exactly as ERRATUM E2 states"*).

**⚠ THIS NODE IS THE REPAIRED CRITICAL, AND IT IS `q = 2`-BLIND BY DESIGN.** Clause (iii) is stated
as an **inequality** rather than a value, because the interesting content is precisely that the two
censuses **differ** — and they differ at every `q ≥ 2`, including `q = 2` (`1 ≠ 3`). That is the one
place in this chapter where `q = 2` is a *good* witness; the exponent side of the same repair is
`q`-blind and is covered at H.92's genre-F law. **A node stating only `pinCensus q 1 = q − 1` has not
landed the repair**: the repair is the *distinction*.

**ARITHMETIC AUDIT.** `q = 2`: band `2^1 − 1 = 1`, interior `2^2 − 1 = 3` ✓ distinct. `q = 3`: band
`2`, interior `8` ✓ distinct. `q = 5`: `4` vs `24` ✓. `EFF.GENHN.32`'s exhaustive `(1,3,2)` rows give
the same shape at `f₁ = 3`: at `N = 7`, `comp(N) = 2` and the census is `Q^2 − 1 = 3` ✓ (with
`Q = q = 2`), and at `N = 8` the pin is interior so the census is `Q^{f₁} − 1 = 7` ✓ — **and both
rows balance exactly against their totals** (`24,576 + 8,192 = 32,768` ✓;
`1,835,008 + 262,144 = 2,097,152` ✓), as that spec's audit records. **Three independent derivations
of the same census agree** (E2's clause, `CAP-GEN`'s COUNT TRANSPORT, and `CR-3`).

**TEETH.** `GH-JSONTIE [SAME]` (`EFF.GENH4.07`, executable regression against a **foreign
md5-pinned artifact table**, both directions, 481/0) → **Lean theorem** for the census values;
`GH-T-CEN` (planted mutant against the INERT census, fired 14×) → **executable regression** retained.

**ENVIRONMENT.** ENV-H1.

---

### NODE H.45 [lemma] [fresh]

**STATEMENT.** *The residual censuses over the stage field.* For `Q ≥ 2`: the number of unordered
pairs of distinct nonzero elements of a `Q`-element field is `(Q−1)(Q−2)/2` (`SPLITEQ`), and the
number of monic irreducible quadratics is `Q(Q−1)/2` (`INERT`). Subtraction-free:
`2 * splitEqCensus Q = (Q−1)*(Q−2)` and `2 * inertCensus Q = Q*(Q−1)`.

**SIGNATURE.**
```lean
namespace Uniformity.Density.Induction

/-- `#{unordered pairs of distinct nonzero elements}` over a `Q`-element field — the `SPLITEQ`
residual census. -/
def splitEqCensus (Q : ℕ) : ℕ := (Q - 1) * (Q - 2) / 2

/-- `#{monic irreducible quadratics}` over a `Q`-element field — the `INERT` residual census. -/
def inertCensus (Q : ℕ) : ℕ := Q * (Q - 1) / 2

theorem two_mul_splitEqCensus (Q : ℕ) : 2 * splitEqCensus Q = (Q - 1) * (Q - 2)

theorem two_mul_inertCensus (Q : ℕ) : 2 * inertCensus Q = Q * (Q - 1)
```

**DEPENDS.** none · mathlib `Nat.even_mul_succ_self` (parity of consecutive products).

**PROOF.**
1. `two_mul_inertCensus`: `Q * (Q−1)` is even (`Nat.even_mul_pred_self`); `Nat.two_mul_div_two_of_even`.
2. `two_mul_splitEqCensus`: `(Q−1)*(Q−2)` is a product of consecutive naturals for `Q ≥ 2`, hence
   even; the `Q ∈ {0,1}` cases give `0` on both sides (`ℕ`-subtraction truncates), so `interval_cases`
   on `Q ≤ 2` first.

**SIZE.** 12 lines.

**SOURCE.** `EFF.GENH4.07` (the censuses over `F_{q^{f₁}}`: *"`(Q−1)(Q−2)/2` for SPLITEQ, `Q(Q−1)/2`
for INERT"*), with the spec's audit *"`Q(Q−1)/2` = the number of monic irreducible quadratics over
`F_Q` ✓ (`(Q²−Q)/2`)"* and its remark that both *"match the standard W-11 residual table over `K`"*;
`EFF.GENIND.47` (`#ψ = q(q−1)/2`).

**⚠ THE `SPLITEQ` CENSUS IS THE **ORDERED-PAIR-HALVED** ONE, and the `q = 2` cell is degenerate.**
At `Q = 2` there is exactly one nonzero element, so `splitEqCensus 2 = 0` — the genre is empty. The
`ℕ`-truncation at `Q = 2` is therefore *correct*, not an artifact, but it means the `q = 2` column
cannot test the formula. **The `q = 3` and `q = 4` cells are mandatory** (audit below). This is the
same trap as G.39's `q(q−1)/2` vs `(q−1)(q−2)/2` reconciliation, which chapter G's AMENDMENT §A-3
verified — the two censuses count over different domains and must not be conflated.

**ARITHMETIC AUDIT (recomputed fresh at `Q = 2, 3, 4, 5`).** `splitEqCensus`: `Q=2 → 0`; `Q=3 → 1`
(the pair `{1,2}`) ✓; `Q=4 → 3` ✓ (`{1,2},{1,3},{2,3}` over `F₄^×`); `Q=5 → 6` ✓.
`inertCensus`: `Q=2 → 1` ✓ (`x²+x+1`); `Q=3 → 3` ✓ (`x²+1, x²+x+2, x²+2x+2`); `Q=4 → 6` ✓;
`Q=5 → 10` ✓. Sum check against the full residual table over `F_Q` (chapter G's `n = 2` census):
`splitEq + inert + double + (b₀ = 0 rows)` must be `Q²`; at `Q = 3`: `1 + 3 = 4` non-degenerate
non-double pairs with both roots nonzero, and chapter G's `two_mul_card_aniForm`/`two_mul_card_sepPair`
give `q(q−1)/2 = 3` each over all of `F_q × F_q` ✓ — **the two chapters' censuses differ exactly by
the `b₀ = 0` rows, which is chapter G's AMENDMENT §A-3 reconciliation, verified there.** Chapter H
consumes the `F_Q^×`-domain versions, because `SPLITEQ` is about *stage* letters in `K^×`.

**TEETH.** `GH-JSONTIE` (481/0, both directions) · `GH-T-CEN` (fired 14×) → **Lean theorem**.

**ENVIRONMENT.** ENV-H1.

---

### NODE H.46 [lemma] [fresh]

**STATEMENT.** *The E-genre slot strings and the ragged band's cardinality.* For `h = 2t+1` odd and
`N ≥ 2t+2`: the `A₁` odd string runs over `dv`-heights `{2h+1, 2h+3, …, 2N−2+h}`, the `A₁` even
string over `{2h+2, 2h+4, …, 2N−2}`; together they cover **every** integer in `[2h+1, 2N−2]`; and the
**ragged band** `{m | 2N ≤ m ≤ 2N−2+h}` contains exactly `(h−1)/2 = t` odd heights, **empty at
`h = 1`**.

**SIGNATURE.**
```lean
namespace Uniformity.Density.Induction

/-- The odd (`α₁`-borne) `dv`-heights of the `A₁` string at genre E. -/
def slotOdd (N h : ℕ) : Finset ℕ :=
  (Finset.Icc ((h + 1) / 2) (N - 1)).image (fun v => 2 * v + h)

/-- The even (`α₀`-borne) `dv`-heights of the `A₁` string at genre E. -/
def slotEven (N h : ℕ) : Finset ℕ :=
  (Finset.Icc (h + 1) (N - 1)).image (fun v => 2 * v)

theorem raggedBand_card (N t : ℕ) (hN : 2 * t + 2 ≤ N) :
    ((slotOdd N (2 * t + 1)).filter (fun m => 2 * N ≤ m)).card = t

theorem raggedBand_empty_of_h_one (N : ℕ) (hN : 2 ≤ N) :
    ((slotOdd N 1).filter (fun m => 2 * N ≤ m)) = ∅
```

**DEPENDS.** none · mathlib `Finset.card_image_of_injective`, `Finset.Icc`, `Nat.card_Icc`.

**PROOF.**
1. `slotOdd` is the image of `Icc ((h+1)/2) (N−1)` under the injection `v ↦ 2v + h`
   (`Finset.card_image_of_injective` with `fun a b => by omega`).
2. the filter `2N ≤ 2v + h` is `v ≥ (2N − h)/2`, i.e. `v ≥ N − t` for `h = 2t+1` (`omega`).
   So the filtered set is the image of `Icc (max ((h+1)/2) (N−t)) (N−1)`, whose card is
   `(N−1) − (N−t) + 1 = t` when `N − t ≥ (h+1)/2 = t+1`, i.e. `N ≥ 2t+1` ✓ (from `hN`).
3. `Nat.card_Icc` then `omega`.
4. `raggedBand_empty_of_h_one`: `t = 0` in clause 2 gives card `0`; `Finset.card_eq_zero`.

**SIZE.** 22 lines. **SPLIT CANDIDATE:** the two `def`s plus `raggedBand_card` is one node;
`raggedBand_empty_of_h_one` is a two-line corollary and can share the file.

**SOURCE.** `EFF.GENH4.17` (§S2.3's slot strings, with the spec's audit of all eight endpoints, and
verbatim: *"the band `{2N ≤ dv ≤ 2N−2+h}` holds exactly `(h−1)/2` odd slots per string (empty at
`h = 1`)"*, plus *"Both strings cover EVERY integer of their ranges below `2N−1` — the half-integer
(`E = 2`) ladder realized in full"*).

**ARITHMETIC AUDIT (recomputed fresh).** Band count: odd heights in `[2N, 2N−2+h]` are
`2N+1, 2N+3, …, 2N−2+h`; with `h = 2t+1` the top is `2N + 2t − 1`, so the count is
`((2N+2t−1) − (2N+1))/2 + 1 = (2t−2)/2 + 1 = t` ✓ **exactly `(h−1)/2`**, and `t = 0` at `h = 1` ✓.
Endpoint checks at `h = 3` (`t = 1`), `N = 7`: odd string `[2·3+1, 2·7−2+3] = [7, 15]` odd, even
string `[8, 12]` even; union covers `[7, 12]` entirely ✓; band `[14, 15]` contains the single odd
height `15` ✓ = `t = 1`. **This is the `h = 3` cell — the one where the corpus's genre-E drainage
CORRECTION lives (`EFF.GENH4.10`: `512`, not `256`)** — so the band count is checked exactly where the
slip was.

**TEETH.** `GH-T-LAT` (`EFF.GENH4.17`, planted mutant: *"my `law_E` corrupted to the integer-only
`dv` ladder must mismatch on every E row"*, fired **19** times) → **Lean theorem** (the
half-integer ladder's full coverage is this node's first clause).

**ENVIRONMENT.** ENV-H1.

---

### NODE H.47 [lemma] [fresh]

**STATEMENT.** *`GENH4.B`'s genre-E aggregate, and the `h = 1` coincidence that hid the CORRECTION.*
Two clauses.
(i) the aggregate over the ladder: for `2h + 1 ≤ N`,
`(N + h − 1) + (N − 1 − 2*h) = 2*N − h − 2`.
(ii) **the coincidence is iff `h = 1`**: for `h` odd, `N + (h−1)/2 = N + h − 1` iff `h = 1`.

**SIGNATURE.**
```lean
namespace Uniformity.Density.Induction

theorem genh4B_aggregate_exp {N h : ℕ} (hfl : 2 * h + 1 ≤ N) :
    (N + h - 1) + (N - 1 - 2 * h) = 2 * N - h - 2

theorem und_exp_coincide_iff_h_one {N t : ℕ} (hN : 1 ≤ N) :
    N + ((2 * t + 1) - 1) / 2 = N + (2 * t + 1) - 1 ↔ t = 0
```

**DEPENDS.** none.

**PROOF.** both `by omega` (clause (ii): the left is `N + t`, the right is `N + 2t`, equal iff
`t = 0`).

**SIZE.** 8 lines.

**SOURCE.** `EFF.GENH4.10` (`THEOREM GENH4.B`, the genre-E law `UND(h; H₂) = (q−1)^{r+t}·q^{N+h−1}`
and its aggregate `(q−1)^{r+1}·q^{2N−h−2}`, plus **the CORRECTION disclosed**, verbatim:
*"QSCOUT22 S6/S8 quoted the genre-E law as `(q−1)q^{N+(h−1)/2}`; that is the `h = 1` instance only. At
`h = 3` the committed artifact (`qscout22_results.json` @ `dd67cda`, row consE Zp q=2 N=7 h=3) reads
`UND = 512 = (q−1)q^{N+h−1}`, not 256. The law proved here matches the committed table on every row;
the quoted display was the scout note's summary slip, not a measurement error."*), with the spec's
audit: *"at `h = 1`, `N+(h−1)/2 = N = N+h−1` ✓ — the two laws coincide exactly at `h = 1`, which is
why the slip survived"*.

**⚠ WHY THE COINCIDENCE IS THE THEOREM.** The corpus corrected a *value*; chapter H proves the
*mechanism* — the two laws agree precisely on the one-parameter slice every check ran on. This is the
G.23 lesson in its purest form and the reason H.29's audit rule exists. Landing only the aggregate
(clause (i)) would leave the slip's mechanism unrecorded.

**ARITHMETIC AUDIT (recomputed fresh at `q = 2` and `q = 3`).** `(q,N,h) = (2,7,3)`: proved law
`(q−1)q^{N+h−1} = 1·2^9 = 512` ✓ = the committed artifact; scout's law `1·2^{7+1} = 256` ✗.
`(3,7,3)`: proved `2·3^9 = 39,366`; scout's `2·3^8 = 13,122` — **a factor `3 = q` apart, so the
`q = 3` column also separates them** ✓. `(2,5,1)`: proved `1·2^5 = 32`; scout's `1·2^5 = 32` —
**identical**, the coincidence ✓. Aggregate check at `(2,7,3)`: `(N+h−1) + (N−1−2h) = 9 + 0 = 9` and
`2N−h−2 = 14−3−2 = 9` ✓ (the ladder is empty at `N = 2h+1`, the floor-adjacent cell).

**TEETH.** `GH-UND [SAME]` (`EFF.GENH4.10`, executable regression, 92/0: *"THEOREM GENH4.B's closed
forms vs every UND key (committed JSON + all fresh rows), **incl. the `h = 3` correction value 512**
and the even-N two-term F law; aggregates"*) → **Lean theorem**.

**ENVIRONMENT.** ENV-H1.

---

### NODE H.48 [lemma] [fresh]

**STATEMENT.** *`GENH4.B`'s genre-F law: the odd-`N` single power and the even-`N` two-term sum.*
Two clauses.
(i) at odd `N = 2ℓ+1`: `2*(N/2) + 2*k − 1 = N + 2*k − 2` — the single `q`-power.
(ii) at even `N = 2ℓ`: the two terms are `q^(N+2k−1)` and `(q−1)*q^(N+2k−1)`, and their sum is
`q^(N+2k)` — i.e. the "two-term" law **collapses to a single `q`-power at even `N`**.

**SIGNATURE.**
```lean
namespace Uniformity.Density.Induction

theorem genh4B_F_odd_exp {l k : ℕ} (hk : 1 ≤ k) :
    2 * ((2 * l + 1) / 2) + 2 * k - 1 = (2 * l + 1) + 2 * k - 2

theorem genh4B_F_even_sum (q N k : ℕ) (hq : 1 ≤ q) :
    q ^ (N + 2 * k - 1) + (q - 1) * q ^ (N + 2 * k - 1) = q ^ (N + 2 * k) ∨ N + 2 * k = 0
```

**DEPENDS.** none.

**PROOF.**
1. (i) `omega` ((2l+1)/2 = l, so the left is `2l + 2k − 1` and the right is `2l + 2k − 1`) ✓.
2. (ii) if `N + 2k ≥ 1`, factor: `q^{M−1}(1 + (q−1)) = q^{M−1}·q = q^M` with `M := N + 2k`
   (`Nat.sub_add_cancel`, `pow_succ`); the disjunct handles `M = 0` where `ℕ`-subtraction truncates.

**SIZE.** 10 lines.

**SOURCE.** `EFF.GENH4.10` (`THEOREM GENH4.B`'s genre-F law: *"`UND(k; H₂) = (q²−1)^t (q−1)^r ·
[ q^{2⌊N/2⌋+2k−1} + 1_{2|N}·(q−1)·q^{N+2k−1} ]` … the second term is the
readable-value/unreadable-residual band at `dv0 = N` (`GENH4-CAP(F)`), present at even `N` only; at
odd `N` the law is the single `q`-power `q^{N+2k−2}`"*), and the spec's own **compiler observation**,
carried verbatim as this node's clause (ii): *"the "two-term" sum collapses to a single `q`-power at
even `N`. The display is faithful to the FORM `GENH4-CAP(F)` produces (a main term plus a band term),
and GENIND's `(CS-EXACT)` requirement ("a FINITE SUM of `q`-powers") is met either way. Recorded as an
observation, not a correction — and it is worth recording because the two-term language drove a
granularity correction across three GENIND sites."*

**⚠ THE COLLAPSE IS THE POINT, AND IT IS NOT A CORRECTION.** `EFF.GENIND.14`'s `[r2, PE2-m1]`
granularity rider exists *because* of this two-term law: *"not always a single `q`-power — GENH4.B's
genre-F law at even `N` is a TWO-term sum (the `CAP(F)` boundary band), so the r1 gloss "one
closed-form `q`-power family per stratum" was satisfiable only at a finer granularity than the
stratum it names"*. Chapter H lands the collapse as a theorem so that a reader can see the corrected
`(CS-EXACT)` wording ("a FINITE SUM of `q`-powers") is satisfied *both* ways — the rider was
right about granularity and the sum is nevertheless one power. **Do not "simplify" the corpus's
two-term display away**: the two terms have different geometric meanings (main stratum vs band).

**ARITHMETIC AUDIT (recomputed fresh at `q = 2` and `q = 3`).** `(q,N,k) = (2,8,1)`: main
`q^{N+2k−1} = 2^9 = 512`, band `(q−1)q^9 = 512`, sum `1,024 = 2^{10} = q^{N+2k}` ✓ — the corpus's
committed check *"(2,8,1) F → 1024 = 512 + 512"* ✓. `(3,8,1)`: main `3^9 = 19,683`, band
`2·3^9 = 39,366`, sum `59,049 = 3^{10}` ✓ — **the `q = 3` cell, where the two terms are `1 : 2`
rather than `1 : 1`, so the collapse is a genuine identity and not a doubling coincidence.** At
`q = 2` the two terms are equal, which is exactly the degeneracy the `q = 3` column removes.
`(2,7,1)`: odd, `2·(7/2) + 2 − 1 = 6 + 1 = 7`? recompute: `2·3 + 2·1 − 1 = 7` and
`N + 2k − 2 = 7 + 2 − 2 = 7` ✓.

**TEETH.** `GH-UND [SAME]` (92/0, *"incl. … the even-N two-term F law"*) → **Lean theorem**.

**ENVIRONMENT.** ENV-H1.

---

### NODE H.49 [lemma] [fresh]

**STATEMENT.** *The `m = 6` mixed grammar's entry heights (Gauss additivity), three families.* For
integer slopes `k, h ≥ 1`:
(i) **child + E-block** (`(e,γ,μ) = (2,1,2)`, block slope `h/2`): entry height `2k + 2h`; the
**unique** cell with `2k + 2h < 6` is `(k,h) = (1,1)`, giving `4`; and the stage-steeper arrangement
`h ≥ 2k+1` gives `≥ 8`.
(ii) **child + f-first block, SAME side** (`(1,2,2)`, forced `k = h`): entry height `6k ≥ 6`.
(iii) **child + f-first block, DISTINCT sides** (`h ≠ k`): entry height `2k + 4h ≥ 8`.
Consequently every non-`M6` mixed genre enters at `v(a₀) ≥ 6`, i.e. `N ≥ 7`.

**SIGNATURE.**
```lean
namespace Uniformity.Density.Induction

theorem mixed_six_childE_lt_six {k h : ℕ} (hk : 1 ≤ k) (hh : 1 ≤ h)
    (hlt : 2 * k + 2 * h < 6) : k = 1 ∧ h = 1

theorem mixed_six_stage_steeper {k h : ℕ} (hk : 1 ≤ k) (hst : 2 * k + 1 ≤ h) :
    8 ≤ 2 * k + 2 * h

theorem mixed_six_sameSide {k : ℕ} (hk : 1 ≤ k) : 6 ≤ 6 * k

theorem mixed_six_distinctSide {k h : ℕ} (hk : 1 ≤ k) (hh : 1 ≤ h) (hne : h ≠ k) :
    8 ≤ 2 * k + 4 * h
```

**DEPENDS.** none.

**PROOF.** first three `by omega`. The fourth: `h ≠ k` with both `≥ 1`; if `h ≥ 2` then
`2k + 4h ≥ 2 + 8 = 10`; if `h = 1` then `k ≠ 1` so `k ≥ 2` and `2k + 4 ≥ 8` ✓. `omega` after
`rcases Nat.lt_or_ge h 2`.

**SIZE.** 14 lines.

**SOURCE.** `EFF.GENIND.32` (the complete `m = 6` mixed grammar, `[r5]`-re-derived, verbatim: the
three bulleted families with their entry heights and *"No other arrangement fits the `2 + 4 = 6`
abscissa budget. So every non-M6 mixed genre enters at `v(a₀) ≥ 6`, i.e. `N ≥ 7`, and the
first-visible mixed genre — uniquely, at `v(a₀) = 4`, `N = 5` — is PE2's"*), with the spec's own
ARITHMETIC AUDIT re-deriving every height by Gauss additivity.

**⚠ WHAT IS NOT CLAIMED.** "No other arrangement fits the budget" is a **grammar completeness**
claim over frame shapes — geometric, chapter C, no node. This node proves the *four height
inequalities*, which is the checkable content and the part the `n = 6` threshold rests on.
`EFF.GENIND.32` also carries a **`STALE-SELF-DESCRIPTION`** (its `§S15` honest-limit sentence says
the same-side f-first genre is machine-unrealized, which PE6 later closed corpus-first,
2,132,082/0) — chapter H does not reproduce the stale sentence.

**ARITHMETIC AUDIT (recomputed fresh, Gauss additivity `v(a₀) = Σ_sides length × slope`).** child
length 2 at slope `k` contributes `2k`; E-block length 4 at slope `h/2` contributes `4·(h/2) = 2h` ✓
→ `2k + 2h` ✓, minimum `4` at `(1,1)` ✓, and `k ≥ 2` with `h ≥ 1` gives `≥ 6` ✓. Same-side f-first:
one side of length 6 at slope `k` gives `6k` ✓, `= 6` at `k = 1` so `N ≥ 7` ✓. Distinct-side:
`2k + 4h`, minimum `8` at `(k,h) = (2,1)` ✓ (`(1,2)` gives `10`). Budget `2 + 4 = 6 = m` ✓ saturated.
Cross-check against genre **M6** (`EFF.GENIND.33`): hull `(0,4)–(2,2)–(6,0)`, left side length 2 drop
2 → slope 1 ✓, right side length 4 drop 2 → slope `1/2` ✓ (so `e = 2`, `h = 1`), entry height
`2·1 + 4·(1/2) = 4` ✓ = the `(k,h) = (1,1)` cell ✓, first visible at `N = 5` ✓. **The unique cell and
the unique machine-realized instance coincide.**

**TEETH.** `EFF.GENIND.32`'s cross-check against PE5's committed artifacts (NINEMIX's Gauss-additive
entry height `11 = 1·3 + 2·2 + 2·1 + 4·(1/2)`, SAMESIDE's `4 = 4 × 1` on 59,049 exhaustive states) →
**Lean theorem** for the height arithmetic; the grammar-completeness half stays a
`disclosed non-repair`/foreign-regression.

**ENVIRONMENT.** ENV-H1.

---

### NODE H.50 [lemma] [fresh]

**STATEMENT.** *The tower thresholds.* Three clauses.
(i) a stage's own read admits a composite opening only if the stage multiplicity is `≥ 4` (H.03
applied inside the stage), so towers need `μ ≥ 4`;
(ii) hence towers exist at degree `n` only if `n ≥ e₁f₁·μ ≥ 2·4 = 8`;
(iii) a **third** stage forces `μ₁ ≥ e₂f₂μ₂ ≥ 2·4 = 8` and hence `n ≥ D′·μ₁ ≥ 2·8 = 16`.

**SIGNATURE.**
```lean
namespace Uniformity.Density.Induction

theorem tower_needs_eight {e f μ n : ℕ} (hef : 2 ≤ e * f) (hμ : 4 ≤ μ) (hn : e * f * μ ≤ n) :
    8 ≤ n

theorem depth_three_needs_sixteen {D μ₁ e₂ f₂ μ₂ n : ℕ} (hD : 2 ≤ D) (h2 : 2 ≤ e₂ * f₂)
    (hμ₂ : 4 ≤ μ₂) (h1 : e₂ * f₂ * μ₂ ≤ μ₁) (hn : D * μ₁ ≤ n) : 16 ≤ n
```

**DEPENDS.** H.03 (for the "inside the stage" application, cited in the SOURCE reasoning; the Lean
statements are self-contained arithmetic).

**PROOF.**
1. `tower_needs_eight`: `8 = 2*4 ≤ (e*f)*μ ≤ n` by `Nat.mul_le_mul` then `le_trans`.
2. `depth_three_needs_sixteen`: `8 = 2*4 ≤ e₂*f₂*μ₂ ≤ μ₁`, then `16 = 2*8 ≤ D*μ₁ ≤ n`. `omega`
   after the two `Nat.mul_le_mul`s.

**SIZE.** 10 lines.

**SOURCE.** `EFF.GENHN.16` (`LEMMA GENHN-T(a)`, verbatim: *"a stage's own read admits a composite
opening (a TOWER event) iff the stage multiplicity satisfies `μ ≥ 4` (GENIND.A(IV) applied inside the
stage); hence towers exist at degree `n` iff `n ≥ (e₁f₁)·μ ≥ 2·4 = 8`. `n = 8 = 2·2·2` is the first
live instance … `n = 4..7` are tower-free"*); `EFF.GENHN.18`'s `[r3]` **R1 arithmetic**, verbatim:
*"a third stage forces `μ₁ ≥ e₂f₂μ₂ ≥ 8`, hence `n ≥ D′μ₁ ≥ 16`"*, with that spec's own audit
recomputing it and noting the two inputs are `GENHN-T(a)` applied twice.

**⚠ THE "iff" IS AN "only if" HERE.** `GENHN-T(a)` states an iff, and the *realization* half (the
`n = 8` genre `(2,1,4)` exists with positive opening locus, and the machine witness `GN-TOWER`
exhibits an explicit member) is **geometric — no node**. This chapter proves the necessity direction,
which is the direction the conditionality bookkeeping consumes (`n ≤ 7` tower-free ⟹ `[GENHN-TOW-1]`
is empty there). `EFF.GENHN.16` also carries a corrected proof display (`R4 F-5`: read `(T−c)²`, not
`(T²−c)²`) whose content is the realization half — **and the machine witness was right while the
proof display was wrong** (`stale self-description`, that spec's TEETH field). Chapter H reproduces
neither display.

**ARITHMETIC AUDIT (recomputed fresh).** `2·4 = 8` ✓; `n = 8 = 2·2·2` is the minimal factorization
with `e₁f₁ = 2`, `μ = 4` ✓, and the inner datum `(e₂f₂, μ₂) = (2, 2)` ✓ — consistent with
`EFF.GENHN.16`'s *"`(e₁f₁) = 2, μ = 4, inner (e₂f₂) = 2, μ₂ = 2`"*. Depth 3: `2·4 = 8 ≤ μ₁` and
`2·8 = 16 ≤ n` ✓, matching the `[r3]` depth split *"depth 2 exhausts the tower genres at
`n ∈ {8, …, 15}`; at `n ≥ 16` the ITERATED (depth-≥ 3) composition additionally rides
`[GENHN-TOW-1]` item (6)"*. **The two thresholds `8` and `16` are the chapter's degree-range
boundaries and they are what H.95's package indexing rests on.**

**TEETH.** `GN-TOWER` (`EFF.GENHN.16`, executable regression: the criterion + the `n = 8` witness +
the min-`n` scan, *"min-n = 8; zero stage-CS anywhere else in the battery"*) → **Lean theorem** for
the necessity half; `passPE1` R4's note that the scan *"verifies the arithmetic minimum only"* is
exactly this node's scope ✓.

<!-- APPEND-POINT -->




