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

**ENVIRONMENT.** ENV-H1.

---

## 8. §8 — THE SLOT / LIFT LAYER (THE `H → B` SPLIT POINT)

> **Placement note.** `spec/DAG_README.md`'s heaviest backward arc is `H → B` (weight 12) with the
> mandated remedy *"GENHN's stage/slot infrastructure belongs below chapter B, its count/tower results
> above it"*. §8 **is** that infrastructure: `EFF.GENHN.27`'s reverse XREF records
> `HE7_PROOF:LEMMA GENHN-2` count 1 — *"HE7 consumes THE SLOT LEMMA as its ladder base case"*.
> Every node of §8 depends only on §3 and on mathlib, so chapters B and E may consume H.51–H.58
> without consuming anything else in chapter H.

### NODE H.51 [lemma] [fresh]

**STATEMENT.** *Class separation mod `e₁`.* If `Nat.Coprime h e₁` and `i, i' < e₁` with
`i * h ≡ i' * h [MOD e₁]`, then `i = i'`. Equivalently the map `i ↦ (i * h) % e₁` is injective on
`Finset.range e₁`, hence a bijection of `range e₁` onto itself.

**SIGNATURE.**
```lean
namespace Uniformity.Density.Induction

theorem class_sep {h e : ℕ} (hcop : Nat.Coprime h e) {i i' : ℕ} (hi : i < e) (hi' : i' < e)
    (hmod : i * h % e = i' * h % e) : i = i'

theorem class_sep_bij {h e : ℕ} (hcop : Nat.Coprime h e) :
    Set.BijOn (fun i => i * h % e) (Finset.range e) (Finset.range e)
```

**DEPENDS.** none · mathlib `Nat.Coprime.cancel_right_dvd_of_dvd_mul_right`,
`ZMod.natCast_self_eq_zero`, `ZMod.val_cast_of_lt`, `Nat.ModEq`.

**PROOF.**
1. `class_sep`: from `hmod`, `e ∣ (i − i') * h` (over `ℤ`, or in `ℕ` after `wlog i' ≤ i`). Since
   `Nat.Coprime h e`, `e ∣ (i − i')` (`Nat.Coprime.dvd_of_dvd_mul_right`). With `i − i' < e` this
   forces `i = i'`.
2. `class_sep_bij`: injectivity is clause 1; the map lands in `range e` by `Nat.mod_lt` (needs
   `0 < e`, from `Nat.pos_of_ne_zero` and `hcop`'s `e ≠ 0` when `e = 0` is excluded — handle `e = 0`
   by `Finset.range 0 = ∅`); surjectivity on a finite set follows from injectivity
   (`Finset.injOn_iff_bijOn_of_card_eq` / `Set.InjOn.bijOn_image`).

**SIZE.** 16 lines. `e = 0` and `e = 1` should be dispatched first (`interval_cases`-style).

**SOURCE.** `EFF.GENHN.27` (`LEMMA GENHN-2`, verbatim: *"the minimum's residue class mod `e₁` is
`i·h mod e₁` (distinct for distinct `i` mod `e₁` since `gcd(h, e₁) = 1`)"* and *"Across classes there
are no ties (distinct residues mod `e₁`): this is JC-LOAD's no-cancellation holding BY CLASS
SEPARATION + RESIDUE-FIELD INDEPENDENCE — elementary, hence not consumed"*); `EFF.GENHN.29`(c) (the
one-line congruence bound that uses it).

**⚠ THE WELD-FREE DECLARATION IS LOAD-BEARING AND CHAPTER H HONOURS IT.** `EFF.GENHN.27`(c): *"the
JC-LOAD / W-9 sentences are frame citations, not consumptions — the lemma's own words: "elementary,
hence not consumed", "cited as frame". This is the note's cleanest weld-free declaration and is what
makes `GENHN-BOX-2` a box about **layer 1 of GENHN-4 only**, not about the slot geometry."* And
`runs/qgen/WELD_FACE_AUDIT.md` independently confirms the routing. **Chapter H's §8 therefore consumes
NO weld face**, and no node of §8 may cite `W-9`, `JC-LOAD` or `W-8`. A fleet agent reaching for one
has left the chapter.

**TEETH.** `GN-E31`'s three-class computation (`EFF.GENHN.27`, the `e₁ = 3, f₁ = 1` instance,
machine-checked at the E31 rows) · `GN-T-LAT` (planted mutant: *"E31 law collapsed to integer
lattice"* must break; fired 2/2) → **Lean theorem**.

**ENVIRONMENT.** ENV-H1.

---

### NODE H.52 [lemma] [fresh]

**STATEMENT.** *The slot-min has no cross-class ties.* Fix `h, e₁` coprime and a finite family of
candidate heights `m_i = e₁ * v_i + i * h` indexed by `i < e₁` (one per residue class). If
`m_i = m_{i'}` then `i = i'` and `v_i = v_{i'}`. Consequently the minimum of the family is attained at
a **unique** index, so the ultrametric inequality `dv(A(θ)) ≥ min_i m_i` is an **equality**.

**SIGNATURE.**
```lean
namespace Uniformity.Density.Induction

theorem slot_height_injective {h e : ℕ} (hcop : Nat.Coprime h e) {i i' v v' : ℕ}
    (hi : i < e) (hi' : i' < e) (heq : e * v + i * h = e * v' + i' * h) :
    i = i' ∧ v = v'

theorem slot_min_unique {h e : ℕ} (hcop : Nat.Coprime h e) (he : 0 < e)
    (v : ℕ → ℕ) {i i' : ℕ} (hi : i < e) (hi' : i' < e)
    (hmin : e * v i + i * h = e * v i' + i' * h) : i = i'
```

**DEPENDS.** H.51.

**PROOF.**
1. `slot_height_injective`: reduce `heq` mod `e`: `i * h % e = i' * h % e`, so `i = i'` by H.51;
   substituting back and cancelling `e > 0` gives `v = v'` (`Nat.eq_of_mul_eq_mul_left`).
   (`e = 0` forces `i = i' = 0` vacuously since `i < 0` is impossible — so `he` is not needed for the
   first clause once `hi` is available.)
2. `slot_min_unique`: the first component of clause 1.

**SIZE.** 12 lines.

**SOURCE.** `EFF.GENHN.27`'s DERIVATION, verbatim: *"Ultrametric equality when all candidate values
are attained at distinct heights; distinct classes never tie (`dv ≡ ih mod e₁`)"*; `EFF.GENH4.19`
(`LEMMA GENH4-2`, the `e₁ = 2` instance by **parity**: *"the min is uniquely attained (`2v(a)+h` odd,
`2v(b)` even: distinct parities, no ties)"* — which is this node at `e₁ = 2`, `h` odd).

**⚠ THE WITHIN-CLASS TIE IS H.53, NOT THIS NODE.** `GENHN-2` has two separation mechanisms: *across*
classes (this node, by coprimality) and *within* a class (H.53, by residue-field independence). At
`f₁ = 1` there is no within-class branch at all, which is why `GENH4-2`'s parity argument is complete
at `e₁ = 2, f₁ = 1` and why *"the `f₁ ≥ 2` within-class tie branch is exercised only foreign-ly"*
(`EFF.GENHN.27`'s TEETH). Keeping the two nodes apart is what makes the `f₁ ≥ 2` gap visible.

**TEETH.** as H.51; additionally `GH-T-LAT` (`EFF.GENH4.17`, fired 19×) → **Lean theorem** for the
`e₁ = 2` parity instance.

**ENVIRONMENT.** ENV-H1.

---

### NODE H.53 [lemma] [fresh]

**STATEMENT.** *Within-class independence: residue-field independence kills the tie.* Let `K` be a
field, `F ≤ K` a subfield with `[K : F] = f₁`, and `η : K` a generator of `K` over `F` with minimal
polynomial of degree `f₁`. If `λ_0, …, λ_{f₁−1} ∈ F` satisfy `Σ_t λ_t * η^t = 0` then every
`λ_t = 0`.

**SIGNATURE.**
```lean
namespace Uniformity.Density.Induction

theorem eta_independent {F K : Type*} [Field F] [Field K] [Algebra F K] {η : K}
    (hgen : (minpoly F η).natDegree = Module.finrank F K) (hint : IsIntegral F η)
    {f : ℕ} (hf : f = Module.finrank F K) (l : Fin f → F)
    (hsum : ∑ t : Fin f, algebraMap F K (l t) * η ^ (t : ℕ) = 0) :
    ∀ t, l t = 0
```

**DEPENDS.** none · mathlib `Algebra.adjoin.powerBasis`, `PowerBasis.basis`,
`Basis.ext_elem_iff`, `minpoly.degree_le_of_ne_zero`, `Polynomial.aeval`.

**PROOF.**
1. from `hgen` + `hint`, `η` generates a power basis of `K` over `F` of dimension `f`
   (`Algebra.adjoin.powerBasis` plus `Algebra.adjoin_eq_top_of_finrank_eq` — or, more directly,
   `PowerBasis.mk` with `hgen`).
2. the sum is the power basis's coordinate expansion of `0`; `Basis.forall_coord_eq_zero_iff` (or
   `Fintype.linearIndependent_iff` on the power basis's linear independence) gives `l t = 0` for
   every `t`.
3. Route B, if the power-basis plumbing fights: let `p := Σ_t (l t) X^t ∈ F[X]`; `hsum` says
   `aeval η p = 0`, so `minpoly F η ∣ p`; `p.natDegree < f = (minpoly F η).natDegree` forces
   `p = 0` (`minpoly.degree_le_of_ne_zero` contrapositive), hence every coefficient vanishes
   (`Polynomial.ext_iff` + `Finset.sum` coefficient extraction). **Route B is the recommended one**
   — it is four `have`s and uses only `minpoly` API.

**SIZE.** 26 lines. **SPLIT CANDIDATE:** if route B's coefficient extraction is long, land the
polynomial statement (`aeval η p = 0 ∧ p.natDegree < (minpoly F η).natDegree → p = 0`) as a private
helper and the `Fin f`-indexed form as the public contract.

**SOURCE.** `EFF.GENHN.27` (verbatim: *"at a within-class tie among `i, i+e₁, …, i+e₁(f₁−1)` the
residue is `Σ_t res(a_{i+e₁t})·η^t ≠ 0` because `{1, η, …, η^{f₁−1}}` are `F_Q`-independent
(`deg ψ = f₁`)"*, and its DERIVATION: *"a vanishing `F_Q`-combination of `1, η, …, η^{f₁−1}` with some
nonzero coefficient contradicts `[F_Q(η) : F_Q] = f₁`"*); `EFF.GENH4.19`(F) (the `f₁ = 2` instance:
*"the residue is `res(a)·ȳ + res(b) ≠ 0` because `{1, ȳ}` are `F_q`-independent (`ψ`
irreducible)"*); `EFF.GENHN.81` (`GENHN-LIFT`'s residue step: *"GENHN-2's independence gives their sum
`λ`, with no cancellation"*).

**⚠ WHY `η` IS AXIOMATIZED BY ITS MINPOLY DEGREE AND NOT CONSTRUCTED.** The corpus's `η` is
`res(θ^{e₁}π^{−h})`, a residue of a stage-ring element — its *construction* needs the carrier
(honesty item H-5(3)/E3). Chapter H states the independence for **any** generator with the right
minpoly degree, so the node is provable in `ENV-H4` with no `O` at all, and the stage layer's
consumers supply `η` as a hypothesis. This is the same move as H.09's fields: the geometric input is a
hypothesis, the algebra is a theorem.

**TEETH.** `GN-E31` (the `f₁ = 1` degenerate case) · `GENH4-2(F)`'s `(1,2,2)` instance (foreign
evidence at `f₁ = 2`) · `EFF.GENHN.32`'s exhaustive `(1,3,2)` rows at `f₁ = 3` (32,768 and 2,097,152
states, both balancing exactly) → **Lean theorem** (the node covers every `f₁` at once, which no
battery row does — `EFF.GENHN.27`'s `signed vacuity disclosure` for the `f₁ ≥ 2` branch is
**discharged on the Lean side by this node**).

**ENVIRONMENT.** ENV-H4.

---

### NODE H.54 [def] [fresh]

**STATEMENT.** *The exact-height stage lift `L_M`.* Fix a genre datum `G` and `M : ℕ` with
`G.keyDeg * G.h < M`. Let `i = i(M) < e₁` and `a = a(M)` be as in H.10 (so `i*h + e₁*a = M`). For
`λ : Fin f₁ → F` (the `F_Q`-coordinates of an element of `K`), define
`stageLift G M λ = Σ_{s < f₁} λ_s • X^(i + e₁*s) * π^(a − s*h)` — a polynomial of degree `< D′` whose
every nonzero summand has exact `dv`-height `M`.

**SIGNATURE.**
```lean
namespace Uniformity.Density.Induction

/-- The exponent data of the height-`M` normalizer: `i(M) < e₁` and `a(M)` with
`i·h + e₁·a = M` (H.10 supplies existence at `keyDeg * h < M`). -/
noncomputable def GenreDatum.normIdx (G : GenreDatum) (M : ℕ) : ℕ × ℕ :=
  if hM : G.keyDeg * G.h < M then (G.occupied_of_keyDeg_mul_h_lt hM).choose ... else (0, M)

/-- `L_M(λ)` — the exact-height `K`-lift of `LEMMA GENHN-LIFT`, as a coefficient vector over the
ambient ring: `L_M(λ) = Σ_{s<f₁} λ̃_s · x^{i+e₁ s} π^{a−s h}`. -/
noncomputable def stageLift {O : Type*} [CommRing O] (G : GenreDatum) (π : O) (M : ℕ)
    (lift : ℕ → O) : Polynomial O :=
  ∑ s ∈ Finset.range G.f₁,
    Polynomial.C (lift s * π ^ ((G.normIdx M).2 - s * G.h)) *
      Polynomial.X ^ ((G.normIdx M).1 + G.e₁ * s)
```

**⚠ SIGNATURE NOTE (the `choose` and how to avoid it).** `normIdx` as written uses `Exists.choose`,
which is opaque and will make H.55/H.56 painful. **The contract form the fleet should land** takes
`i` and `a` as explicit arguments with the defining equation as a hypothesis:
```lean
noncomputable def stageLift' {O : Type*} [CommRing O] (G : GenreDatum) (π : O)
    (i a : ℕ) (lift : ℕ → O) : Polynomial O :=
  ∑ s ∈ Finset.range G.f₁,
    Polynomial.C (lift s * π ^ (a - s * G.h)) * Polynomial.X ^ (i + G.e₁ * s)
```
and H.55/H.56 carry `(hi : i < G.e₁) (hM : i * G.h + G.e₁ * a = M) (hbig : G.keyDeg * G.h < M)`.
**This is the signed form**; `normIdx` is recorded only because the corpus writes `i(M)`, `a(M)` as
functions. A fleet agent must land `stageLift'`.

**DEPENDS.** H.01, H.02, H.10 · landed `Polynomial.C`, `Polynomial.X`.

**PROOF.** definitional.

**SIZE.** 16 lines.

**SOURCE.** `EFF.GENHN.81` (`LEMMA GENHN-LIFT`, verbatim: *"Write `λ∈K` uniquely as
`λ=\sum_{s=0}^{f_1-1}\lambda_s\eta^s`, `\lambda_s\in F_Q`, and define
`L_M(\lambda):=\sum_{s=0}^{f_1-1}\widetilde{\lambda_s}\,x^{\,i+e_1s}\pi^{\,a-sh}`"*).

**TEETH.** **PROOF-ONLY** (`EFF.GENHN.81`: *"No machine leg exercises `L_M` at `f₁ ≥ 2` inside
GENHN"*, disposition `accepted-with-decorrelation-supplied` — the algebra was hand-re-derived by the
0a compiler before transcription) → the chapter supplies the proof at H.55/H.56.

**ENVIRONMENT.** ENV-H2 (the lift lands in `Polynomial O`; the `dv`-height statements are ENV-H1
arithmetic).

---

### NODE H.55 [lemma] [fresh]

**STATEMENT.** *`L_M` is integral, of degree `< D′`, and every nonzero summand has exact `dv`-height
`M`.* Three clauses, under `i < e₁`, `i*h + e₁*a = M`, `keyDeg*h < M`:
(i) **integrality**: for every `s < f₁`, `s * h ≤ a` — so the exponent `a − s*h` is an honest `ℕ`;
in the identity form `a = s*h + (a − s*h)`;
(ii) **degree**: `i + e₁*s ≤ D′ − 1` for every `s < f₁`, hence `deg (stageLift') < D′`;
(iii) **exact height**: `e₁ * (a − s*h) + (i + e₁*s) * h = M` for every `s < f₁`.

**SIGNATURE.**
```lean
namespace Uniformity.Density.Induction

theorem stageLift_index_lt (G : GenreDatum) {i s : ℕ} (hi : i < G.e₁) (hs : s < G.f₁) :
    i + G.e₁ * s < G.keyDeg

theorem stageLift_integral (G : GenreDatum) {i a M s : ℕ} (hi : i < G.e₁) (hs : s < G.f₁)
    (hM : i * G.h + G.e₁ * a = M) (hbig : G.keyDeg * G.h < M) : s * G.h ≤ a

theorem stageLift_height (G : GenreDatum) {i a M s : ℕ} (hi : i < G.e₁) (hs : s < G.f₁)
    (hM : i * G.h + G.e₁ * a = M) (hbig : G.keyDeg * G.h < M) :
    G.e₁ * (a - s * G.h) + (i + G.e₁ * s) * G.h = M
```

**DEPENDS.** H.01, H.02, H.54.

**PROOF.**
1. `stageLift_index_lt`: `i + e₁*s ≤ (e₁−1) + e₁*(f₁−1) = e₁*f₁ − 1 = keyDeg − 1`. `omega` after
   `Nat.succ_le_of_lt` on both `hi` and `hs`.
2. `stageLift_integral`: from clause 1, `(i + e₁*s) * h ≤ (keyDeg − 1) * h < keyDeg * h < M`;
   substituting `M = i*h + e₁*a` gives `(i + e₁*s)*h < i*h + e₁*a`, i.e. `e₁*s*h < e₁*a`, i.e.
   `s*h < a` (cancel `e₁ > 0`), so `s*h ≤ a`. `omega` once the multiplications are expanded.
3. `stageLift_height`: with `s*h ≤ a` (clause 2), the `ℕ`-subtraction is honest and the identity
   expands to `e₁*a − e₁*s*h + i*h + e₁*s*h = e₁*a + i*h = M` ✓ — the `s*h` terms cancel
   identically. `omega` after `Nat.sub_add_cancel`.

**SIZE.** 20 lines.

**SOURCE.** `EFF.GENHN.81`'s PROOF, verbatim: *"Since `i+e_1s\le D'-1` and `M>D'h`,
`a-sh=\frac{M-(i+e_1s)h}{e_1}\ge0`, so every summand is integral and has degree `<D'`. Its evaluated
height is `e_1(a-sh)+(i+e_1s)h=M`."*; the spec's own audit reproduces all three
(*"the displayed identity is correct … exact, and the `sh` terms cancel identically"*).

**ARITHMETIC AUDIT (recomputed fresh at two genre data).** `(e₁,f₁,h) = (3,1,1)`, `keyDeg = 3`,
`keyDeg*h = 3`, take `M = 4`: `i*1 + 3a = 4` with `i < 3` gives `i = 1, a = 1`; only `s = 0`
(`f₁ = 1`), `s*h = 0 ≤ 1` ✓, index `1 + 0 = 1 < 3` ✓, height `3*1 + 1*1 = 4 = M` ✓.
`(e₁,f₁,h) = (2,3,1)`, `keyDeg = 6`, `keyDeg*h = 6`, take `M = 9`: `i + 2a = 9` with `i < 2` gives
`i = 1, a = 4`; `s ∈ {0,1,2}`: `s*h = 0,1,2 ≤ 4` ✓; indices `1, 3, 5 < 6` ✓; heights
`2*4 + 1 = 9`, `2*3 + 3 = 9`, `2*2 + 5 = 9` ✓ **all three equal `M`** — this is the `f₁ = 3` cell
`EFF.GENHN.32` exercises exhaustively, and the three summands sitting at one height is exactly the
"one `K`-digit per height" content.

**TEETH.** **PROOF-ONLY** at `f₁ ≥ 2` (`EFF.GENHN.81`), with `EFF.GENHN.32`'s two exhaustive `f₁ = 3`
rows as foreign corroboration → **Lean theorem**.

**ENVIRONMENT.** ENV-H1 (all three clauses are exponent arithmetic; the polynomial lives in ENV-H2 but
these statements do not mention it).

---

### NODE H.56 [lemma] [fresh]

**STATEMENT.** *`L_M`'s residue is `λ`.* With the hypotheses of H.55, dividing `L_M(λ)` by the
normalizer `n(M) = x^i π^a` leaves, summand by summand, `(x^{e₁} π^{−h})^s` times the lifted
coefficient — so the residue of the `s`-th summand against `n(M)` is `λ_s · η^s`, and by H.53 the
total residue is `λ` with no cancellation. Formalized at the exponent level (the part that is not
carrier-dependent): for every `s < f₁`,
`(i + e₁*s) = i + e₁*s` and `(a − s*h) + s*h = a`, i.e. the quotient monomial is
`x^{e₁*s} π^{-(s*h)}` — stated as the identity
`x^(i + e₁*s) * π^(a − s*h) = (x^i * π^a) * (x^(e₁*s) * π^(a − s*h) / π^a)` in the honest form
`π^a * x^(i + e₁*s) = x^i * π^(a − s*h) * (x^(e₁*s) * π^(s*h)) * ...` — see the SIGNATURE for the
exact contract.

**SIGNATURE.**
```lean
namespace Uniformity.Density.Induction

/-- The quotient identity: the `s`-th summand of `L_M(λ)` equals the normalizer `x^i π^a` times
`(x^{e₁} π^{−h})^s`, in the cleared form `π^{s h} · (summand) = n(M) · (x^{e₁})^s · lift s`. -/
theorem stageLift_summand_eq {O : Type*} [CommRing O] (G : GenreDatum) (π : O)
    {i a s : ℕ} (hsa : s * G.h ≤ a) (c : O) :
    (Polynomial.C (π ^ (s * G.h)) : Polynomial O) *
        (Polynomial.C (c * π ^ (a - s * G.h)) * Polynomial.X ^ (i + G.e₁ * s))
      = (Polynomial.C (π ^ a) * Polynomial.X ^ i) *
        (Polynomial.C c * Polynomial.X ^ (G.e₁ * s))
```

**DEPENDS.** H.54, H.55 · landed `Polynomial.C_mul`, `Polynomial.X_pow_mul`.

**PROOF.**
1. both sides are `C (…) * X^(…)`; push `C` through products (`Polynomial.C_mul`) and collect the
   `X`-powers (`pow_add`).
2. the scalar identity is `π^(s*h) * (c * π^(a − s*h)) = π^a * c`, which is
   `pow_add`/`Nat.add_sub_cancel'` with `hsa`.
3. `ring` closes after the two rewrites.

**SIZE.** 14 lines.

**SOURCE.** `EFF.GENHN.81`'s PROOF, verbatim: *"Dividing by `n(M)=x^i\pi^a` leaves residue
`\lambda_s\eta^s`; GENHN-2's independence gives their sum `\lambda`, with no cancellation."*;
the spec's audit: *"Dividing `x^{i+e₁s}π^{a−sh}` by `n(M) = x^iπ^a` gives `x^{e₁s}π^{−sh} =
(x^{e₁}π^{−h})^s`, whose residue at `θ` is `η^s` ✓"*.

**⚠ WHY THE STATEMENT IS CLEARED OF DENOMINATORS.** `x^{e₁}π^{−h}` is not in `O[x]`; the corpus works
in `L`/`O_L` (ERRATUM E3, honesty item H-5(3)). Chapter H states the identity **multiplied through by
`π^{s h}`**, which is an identity in `Polynomial O` and needs no carrier. The step from this identity
to *"the residue is `η^s`"* needs `η := res(θ^{e₁}π^{−h})`, i.e. the carrier — and that step is a
hypothesis of the consuming statement, not a node.

**⚠ EXTERNAL-QUARRY NOTE (relayed 2026-08-15, `docs/VENDOR_QUARRY_MAP_2026-08-15.md`).** The survey
confirms **four-way absence** of Newton-polygon, MacLane/key-polynomial and Okutsu–Montes API in our
mathlib pin and in all four vendored quarries. That is independent confirmation of this chapter's
architecture: the geometric layer *cannot* be a transcription target at any grade, so carrying it as
`StageInterface` fields (H.09) is not a shortcut but the only honest option. It also means **no node
of §8 may be labelled `quarry:`** — every one is `fresh`.

**TEETH.** as H.55 (**PROOF-ONLY**, with `hetowr1_supp.py`'s three `η ≠ 1` frames as foreign
evidence).

**ENVIRONMENT.** ENV-H2.

---

### NODE H.57 [lemma] [fresh]

**STATEMENT.** *The wrap exponent `W(t)`.* For `r, i, e₁ : ℕ` with `0 < e₁`:
`r * i = (r * i % e₁) + e₁ * (r * i / e₁)`, and `r * i % e₁ < e₁`. Writing
`W := r * i / e₁ = ⌊r·i/e₁⌋` and `i(r·M) := r*i % e₁`, this is the corpus's cocycle bookkeeping
`n(u₂)^r = n(r·u₂) · (x^{e₁}/π^{h})^{W}`, at the exponent level.

**SIGNATURE.**
```lean
namespace Uniformity.Density.Induction

theorem wrap_div_mod (r i e : ℕ) (he : 0 < e) :
    r * i = r * i % e + e * (r * i / e) ∧ r * i % e < e

/-- The height bookkeeping behind the wrap: if `i·h + e·a = M` then
`r·M = (r·i % e)·h + e·(r·a + W·h)` with `W = r·i / e`. -/
theorem wrap_height {i a M h e r : ℕ} (he : 0 < e) (hM : i * h + e * a = M) :
    r * M = (r * i % e) * h + e * (r * a + (r * i / e) * h)
```

**DEPENDS.** H.51 (the class bookkeeping) · mathlib `Nat.mod_add_div`, `Nat.mod_lt`.

**PROOF.**
1. `wrap_div_mod`: `(Nat.mod_add_div _ _).symm` and `Nat.mod_lt _ he`.
2. `wrap_height`: multiply `hM` by `r`: `r*M = r*i*h + e*(r*a)`; substitute
   `r*i = (r*i % e) + e*W` from clause 1 and expand:
   `r*M = (r*i % e)*h + e*W*h + e*r*a = (r*i % e)*h + e*(r*a + W*h)` ✓. `ring_nf` then `omega`.

**SIZE.** 12 lines.

**SOURCE.** `EFF.GENHN.28` (the twist: *"Products wrap through `θ^{e₁} = (unit lift)·π^h`:
`n(κ)^t = ẑ^{fl}·n(tκ)` with the explicit integer `fl` = the wrap count — W-9's cocycle, literal"*);
`EFF.GENHN.42` (the HETOW erratum's explicit form: *"`n̂(u₂)^{f₂−t} = n̂((f₂−t)u₂)·(x^{e₁}/π^{h})^{W(t)}`
with `W(t) = ⌊(f₂−t)·i(u₂)/e₁⌋`"*); `EFF.GENHN.81`'s APPLICATION (*"`W(t)=\left\lfloor\frac{r\,i(u_2)}
{e_1}\right\rfloor`"* and the re-derivation *"`res(n(u₂)^r/n(ru₂)) = η^{W(t)}`"*).

**⚠ THE CORPUS'S OWN TWO DERIVATIONS AGREE, AND CHAPTER H REPRODUCES THE ARITHMETIC ONLY.**
`EFF.GENHN.81`'s audit: *"the note's own verification paragraph re-derives exactly this
(`e₁(r·a(u₂)−a(ru₂)) = −e₁W(t)h`, matching the erratum's own cocycle display) ✓ — two independent
derivations agree."* The step from the exponent identity to `res(...) = η^W` needs the carrier and is a
hypothesis of the consumer. **Chapter H does not state a cocycle identity in `K`** — that would be a
`W-9` consumption, which §8 is forbidden (H.51's fence).

**ARITHMETIC AUDIT (recomputed fresh).** `(e₁, h, i, a) = (3, 2, 2, ?)`: take `M = 4`, so
`2*2 + 3a = 4` has no `ℕ` solution — use instead `M = 7`: `2*2 + 3a = 7` gives `a = 1` ✓. Then
`r = 2`: `r*i = 4`, `4 % 3 = 1`, `W = 1`; check `2*7 = 14` against
`1*2 + 3*(2*1 + 1*2) = 2 + 12 = 14` ✓. `r = 3`: `r*i = 6`, `6 % 3 = 0`, `W = 2`; check `21` against
`0 + 3*(3 + 4) = 21` ✓. `(e₁, h, i, a) = (2, 1, 1, 3)`, `M = 7`: `r = 3` gives `r*i = 3`,
`3 % 2 = 1`, `W = 1`; check `21` against `1*1 + 2*(9 + 1) = 21` ✓. **Three cells at two `e₁`, all
exact.**

**TEETH.** **PROOF-ONLY**; `EFF.GENHN.81` is part of the A2 wave whose *"three repairs await sol
discharge-confirmation"* → **Lean theorem** is the chapter's contribution and the confirmation is
still owed on the corpus side (§16 item 8).

**ENVIRONMENT.** ENV-H1.

---

### NODE H.58 [lemma] [fresh]

**STATEMENT.** *The composed-key basis is triangular-unimodular.* For `D′, r : ℕ` with `0 < D′`, the
map `(a, b) ↦ a + b * D′` is a bijection from `Finset.range D′ ×ˢ Finset.range r` onto
`Finset.range (D′ * r)`. Hence `{x^a Φ′^b : a < D′, b < r}` has `D′ * r` members whose `x`-degrees
are exactly `0, 1, …, D′*r − 1`, each once — and since `Φ′` is monic, the family is a
triangular-unimodular basis of the polynomials of degree `< D′*r`.

**SIGNATURE.**
```lean
namespace Uniformity.Density.Induction

theorem divMod_bij (D r : ℕ) (hD : 0 < D) :
    Set.BijOn (fun p : ℕ × ℕ => p.1 + p.2 * D)
      (Finset.range D ×ˢ Finset.range r) (Finset.range (D * r))

theorem card_composedBasis (D r : ℕ) (hD : 0 < D) :
    (Finset.range D ×ˢ Finset.range r).card = D * r
```

**DEPENDS.** none · mathlib `Nat.divModEquiv`, `Nat.div_add_mod`, `Finset.card_product`.

**PROOF.**
1. `card_composedBasis`: `Finset.card_product`, `Finset.card_range`, `mul_comm`.
2. `divMod_bij`: the inverse is `n ↦ (n % D, n / D)`; `Nat.mod_add_div` gives the round trip,
   `Nat.mod_lt` and `Nat.div_lt_iff_lt_mul` give membership in both directions. Assemble with
   `Set.BijOn.mk` / `Set.InvOn.bijOn`.

**SIZE.** 18 lines. **SPLIT CANDIDATE:** the cardinality is a one-liner; if the `BijOn` plumbing runs
long, land it alone as the node and keep the cardinality as a private `have`.

**SOURCE.** `EFF.GENHN.43` (`T(b)′` clause (ii), verbatim: *"`{x^a Φ′^b : a < D′, b < e₂f₂}` is a
triangular-unimodular basis of the degree-`< D₂` polynomials"*), and its proof *"Basis:
`deg(x^a Φ′^b) = a + bD′` hits each degree `< D₂` once, leading coefficient 1 —
triangular-unimodular"*, with the spec's audit: *"`{x^a Φ′^b}` has `D′ · e₂f₂ = D₂` elements ✓, and
`deg(x^aΦ′^b) = a + bD′` ranges over `0..D₂−1` bijectively (base-`D′` representation) ✓, leading
coefficient `1` since `Φ′` is monic ✓."*

**⚠ THE BASIS CLAIM ITSELF NEEDS MONICITY AND IS NOT IN THIS NODE.** *"triangular-unimodular basis of
the degree-`< D₂` polynomials"* is a linear-algebra statement about `Polynomial O`; this node proves
the **degree bijection**, which is its combinatorial core and the part that is `Q`- and
carrier-independent. The passage from the degree bijection to a basis is the unit-pivot argument
(§9, H.60) applied to the degree filtration — and H.60 is stated so that it *can* be applied here.
`EFF.GENHN.43`'s CONDITIONALITY also records an OPEN item chapter H does not touch: *"whether the
composed display needs the same `D₂h`-style restriction is **not addressed anywhere in the note**"*
(OPEN-CALL 5 there). **Chapter H does not address it either, and §16 item 7 flags it.**

**ARITHMETIC AUDIT (recomputed fresh).** `D′ = 2`, `r = 2` (the `n = 8` first-live tower):
`D₂ = 4`, degrees `0+0, 1+0, 0+2, 1+2 = 0,1,2,3` ✓ each once. `D′ = 2`, `r = 3`: `D₂ = 6`, degrees
`0,1,2,3,4,5` ✓. `D′ = 3`, `r = 2`: `D₂ = 6`, degrees `0,1,2,3,4,5` ✓. Tie count cross-check against
`EFF.GENHN.43`'s within-class bound: *"at most `f₁` tying monomials per `t`, `f₂` `t`-values, `≤ f₁f₂`
in all"* — and `f₁f₂ = [K₂ : F_Q]` ✓, *"exactly the K₂-dimension, which is why the residues assemble
one `K₂`-digit and no more"* ✓.

**TEETH.** `SUPP-B` (`EFF.GENHN.43`, executable regression on two decorrelated instruments: the first
`f₂ = 2` tower genre `(2,1,4)→(1,2,2)` over `K₂ = F₄`, plus `genhn_pe2_fresh.py`'s *"first outer-`f₁ = 2`
tower genres, first 2-stage dictionary contact, the η₂-cocycle adjudication, and `Q = 4` tower
legs"*; clause (ii) **HELD** at PE2) → **Lean theorem** for the degree bijection.

**ENVIRONMENT.** ENV-H1.

---

## 9. §9 — THE UNIT-PIVOT LAYER (THE R2 REPAIR, WITH ITS COUNTEREXAMPLE)

### NODE H.59 [def] [fresh]

**STATEMENT.** *Triangular with unit pivots.* Let `R` be a commutative ring and
`Φ : (Fin n → R) → (Fin n → R)`. Say `Φ` is **triangular with unit pivots** for the order
`0 < 1 < ⋯ < n−1` when there are `c : Fin n → R` and `g : (i : Fin n) → (Fin n → R) → R` such that
each `c i` is a unit, each `g i` depends only on the coordinates `< i`, and
`Φ v i = c i * v i + g i v` for every `v, i`.

**SIGNATURE.**
```lean
namespace Uniformity.Density.Induction

/-- **Triangular with unit pivots.**  `Φ` solves each output slot as `unit × (its input slot) +
(a function of strictly earlier input slots)`.  This is the condition ANNEX R R2 identifies as the
missing displayed step of `GENIND-6(c)`: triangularity ALONE does not give surjectivity or constant
fibres over a truncated DVR (H.62). -/
structure TriangularUnitPivot {R : Type*} [CommRing R] {n : ℕ}
    (Φ : (Fin n → R) → (Fin n → R)) where
  /-- The pivots. -/
  pivot : Fin n → R
  /-- The strictly-earlier part. -/
  tail : (i : Fin n) → (Fin n → R) → R
  /-- Each pivot is a unit. -/
  pivot_isUnit : ∀ i, IsUnit (pivot i)
  /-- The tail at `i` depends only on coordinates `< i`. -/
  tail_lower : ∀ i v w, (∀ j : Fin n, j < i → v j = w j) → tail i v = tail i w
  /-- The displayed form. -/
  apply_eq : ∀ v i, Φ v i = pivot i * v i + tail i v
```

**DEPENDS.** none.

**PROOF.** definitional.

**SIZE.** 20 lines.

**SOURCE.** `EFF.GENIND.156` (`R2.1`, the rider at schema level, verbatim: *"In GENIND-6(c)'s
coordinate map and GENIND-3 step (3)'s fiber sentence, read "triangular" as **triangular with UNIT
pivots**: in a coordinate order realizing the triangular structure, each solved output slot is
`c·(its input slot) + (a function of strictly earlier input slots)` with pivot `c` a unit of that
slot's truncated ring `O/π^w`"*).

**⚠ THE SUPERSESSION KIND IS `license`, NOT `wording-rider`.** `EFF.GENIND.156`: *"although the
surface instruction is "read X as Y", the operative content is a new condition with a proof of what it
buys (onto + constant fibre), which a wording substitution is not. **This is the shard's canonical
illustration of rule 18's warning that near-identically phrased riders are not interchangeable.**"*
Chapter H therefore lands the condition as a **structure** (a definition with a theorem attached),
not as a comment on an existing node.

**TEETH.** `EFF.GENIND.156`'s machine leg G (a **planted mutant** realizing the toy) →
**Lean theorem** at H.60 and **Lean theorem** at H.62 (the mutant becomes the counterexample).

**ENVIRONMENT.** ENV-H5.

---

### NODE H.60 [theorem] [fresh]

**STATEMENT.** *Unit pivots ⟹ bijective.* If `Φ : (Fin n → R) → (Fin n → R)` is triangular with unit
pivots then `Φ` is bijective. (Back-substitution: solve slot `i` by
`v i = (pivot i)⁻¹ * (target i − tail i v)`, the earlier slots being already determined.)

**SIGNATURE.**
```lean
namespace Uniformity.Density.Induction

theorem TriangularUnitPivot.bijective {R : Type*} [CommRing R] {n : ℕ}
    {Φ : (Fin n → R) → (Fin n → R)} (T : TriangularUnitPivot Φ) : Function.Bijective Φ
```

**DEPENDS.** H.59 · mathlib `IsUnit.unit`, `Units.inv_mul_cancel_left`, `Fin.induction`,
`Function.bijective_iff_has_inverse`.

**PROOF.**
1. **Injectivity.** Suppose `Φ v = Φ w`. Prove `v i = w i` by strong induction on `i` (well-founded
   on `Fin n`'s order, or on `(i : ℕ)`): the IH gives `v j = w j` for `j < i`, so
   `tail i v = tail i w` by `tail_lower`; then `pivot i * v i = pivot i * w i` from `apply_eq`, and
   `v i = w i` by `IsUnit.mul_left_cancel` (`pivot_isUnit i`).
2. **Surjectivity.** Given `t : Fin n → R`, construct `v` by strong recursion:
   `v i := (pivot i).unit⁻¹ * (t i − tail i v)` — well-founded because `tail i v` reads only
   coordinates `< i` (use `Fin.strongRecOn` or define `v` on `ℕ` by `Nat.strongRecOn` and restrict).
   Then `Φ v i = pivot i * v i + tail i v = (t i − tail i v) + tail i v = t i` ✓.
3. The recursion in step 2 is the one delicate construction; the sanctioned Lean idiom is to build
   `v : ℕ → R` by `Nat.strongRecOn` on a `tail'`-extension that ignores indices `≥ n`, then
   `fun i => v i`. Land the extension as a private definition.

**SIZE.** 34 lines. **This is the hardest node of §9** and the only one with a real construction. If
the strong recursion fights, the sanctioned fallback (recorded as a RE-PLAN) is to state and prove the
`n`-induction version — `Φ` bijective on `Fin (n+1) → R` given bijective on `Fin n → R` — which is
`Fin.snoc`-flavoured and avoids well-founded recursion.

**SOURCE.** `EFF.GENIND.156`'s own proof, verbatim: *"Unit pivots are what license the S2.2 slot
bookkeeping: back-substitution solves any target slot by slot (`input = c⁻¹·(target − earlier-part)`,
`c⁻¹` existing because units of `O/π^w` invert), so the map is ONTO; and the fiber over every target is
exactly the free slots (each pinned/priced slot solved uniquely, each free slot unconstrained) — a
target-independent `q`-power. Without unit pivots both conclusions fail"*; `EFF.GENIND.157` (`R2.2`,
the enumerated species check showing every ledger row's pivot is the literal unit `1`).

**⚠ WHAT THIS NODE REPAIRS.** `EFF.GENIND.155` (`R2.0`, CODEX F1, a **CONFIRMED GAP**):
*"GENIND-6(c)'s onto-with-constant-fiber is carried by 'triangular with exact budget floors' + 'the
same S2.2 slot bookkeeping' — and triangularity alone does NOT give surjectivity/constant fibers over
truncated DVRs. The missing displayed step is the unit-pivot condition (the division ledger's pivots
are units because the extracted factors are MONIC — true, used, never displayed as the load-bearing
condition)."* The gap's disposition is `decorrelated-model audit`: *"No battery row could produce
this: the runner only ever executes monic ledgers, so the failure mode is off its state space by
construction."* **Chapter H is the first place in either repo where the condition is stated and
proved.**

**TEETH.** machine leg G (`genind_annexr_supp.py` @ `f5271e4`, GREEN: *"over `ℤ/4`, `(x+2)·y` is
bijective in `y` iff `x` is odd (a unit) — the toy's collapse — while the monic-pivot form `(1+2x)·y`
is bijective at every `x`"* — a **planted mutant** exercising exactly the failure mode) →
**Lean theorem** (this node's positive half) and **Lean theorem** at H.62 (its negative half).

**ENVIRONMENT.** ENV-H5.

---

### NODE H.61 [lemma] [fresh]

**STATEMENT.** *Constant fibres over the free slots.* Let `Φ` be triangular with unit pivots on
`Fin n → R` with `R` finite, and let `P ⊆ Fin n` be a set of "pinned" indices. Then for every target
`t`, the set `{v | ∀ i ∈ P, Φ v i = t i}` has cardinality `(Nat.card R) ^ (n − #P)` — a
**target-independent** count. (This is the corpus's *"the fiber over every target is exactly the free
slots … a target-independent `q`-power"*.)

**SIGNATURE.**
```lean
namespace Uniformity.Density.Induction

theorem TriangularUnitPivot.card_fibre {R : Type*} [CommRing R] [Fintype R] [DecidableEq R]
    {n : ℕ} {Φ : (Fin n → R) → (Fin n → R)} (T : TriangularUnitPivot Φ) (P : Finset (Fin n))
    (t : Fin n → R) :
    Nat.card {v : Fin n → R // ∀ i ∈ P, Φ v i = t i}
      = Fintype.card R ^ (n - P.card)
```

**DEPENDS.** H.59, H.60 · mathlib `Fintype.card_fun`, `Equiv.subtypeEquivOfSubtype`,
`Fintype.card_congr`.

**PROOF.**
1. by H.60, `Φ` is bijective, so `v ↦ Φ v` is an `Equiv`; transport the fibre along it:
   `{v | ∀ i ∈ P, Φ v i = t i} ≃ {u | ∀ i ∈ P, u i = t i}` (`Equiv.subtypeEquiv` with
   `T.bijective.toEquiv`).
2. `{u : Fin n → R | ∀ i ∈ P, u i = t i} ≃ (↥(Pᶜ) → R)` (the coordinates outside `P` are free;
   `Equiv.piCongr`-style, or `Fintype.card` by `Finset.prod` over the coordinates).
3. `Fintype.card_fun` gives `(card R) ^ (Pᶜ).card = (card R) ^ (n − P.card)`
   (`Finset.card_compl`, `Fintype.card_fin`).

**SIZE.** 24 lines.

**SOURCE.** `EFF.GENIND.156` (the fibre clause quoted at H.60); `EFF.GENH4.23` (the onto-by-cardinality
step, verbatim: *"onto by cardinality: the refine slice fixes the two pinned digits and frees exactly
the slots above `dμ` resp. `2dμ` — the same count as the node (slot strings are key-independent,
S2.3)"*).

**⚠ THE FULL-SLICE QUANTIFIER, AND THE MISUSE IT PREVENTS (the GENH4 GAP-1 record).**
`EFF.GENH4.09`'s CONDITIONALITY: *"Its "ONTO the floored fresh node" quantifier is the subject of
ANNEX R2's GAP-1: the onto-statement quantifies over the FULL refine slice, and ANNEX R's R2
misapplied it to a FIXED member where only lift digits vary. **The lemma is not corrected — the misuse
is withdrawn**"*, with R2.G1 verbatim: *"GENH4-4's onto-the-fresh-node statement quantifies over the
FULL refine slice — all in-window digits free. On a FIXED member only LIFT digits vary."* This node's
signature quantifies `v` over **all** of `Fin n → R` and takes the pinned set `P` as data — so a
fixed-member application does not typecheck. **That is deliberate**: the contract makes the withdrawn
misuse un-expressible.

**TEETH.** `GH-REFINE [SAME]` (`EFF.GENH4.09`, executable regression, **192,000/0** on 21,504 + 768
refine events across three rows and both characteristics, *"pointwise and digit-by-digit against a
pinned foreign reader"*) → **Lean theorem** (the strongest count-side guard in the corpus, and this
node is its general law).

**ENVIRONMENT.** ENV-H5 with `[Fintype R] [DecidableEq R]`.

---

### NODE H.62 [lemma] [fresh]

**STATEMENT.** *The counterexample: triangular WITHOUT unit pivots is not surjective.* Over
`R = ZMod 4` with `π = 2`, the map `Φ : (Fin 2 → ZMod 4) → (Fin 2 → ZMod 4)`,
`Φ v = ![v 0, (v 0 + 2) * v 1]`, is triangular (the second output depends on `v 1` with a coefficient
in `v 0` only) but **not surjective**: no `v` has `Φ v = ![0, 1]`, because at `v 0 = 0` the pivot
`0 + 2 = 2` is a non-unit and `2 * v 1 ∈ {0, 2}`. Moreover the fibre size is **not constant**: over
`![0, 0]` it is `2` and over `![1, 0]` it is `1`.

**SIGNATURE.**
```lean
namespace Uniformity.Density.Induction

/-- Codex's toy (`ANNEX R R2.0`): `(x, y) ↦ (x, (x+π)y)` mod `π²`, at `π = 2`, `R = ZMod 4`. -/
def codexToy (v : Fin 2 → ZMod 4) : Fin 2 → ZMod 4 := ![v 0, (v 0 + 2) * v 1]

theorem codexToy_not_surjective : ¬ Function.Surjective codexToy

theorem codexToy_fibre_not_constant :
    (Finset.univ.filter (fun v : Fin 2 → ZMod 4 => codexToy v = ![0, 0])).card = 2 ∧
    (Finset.univ.filter (fun v : Fin 2 → ZMod 4 => codexToy v = ![1, 0])).card = 1
```

**DEPENDS.** none (deliberately independent of H.59 — the toy is *not* a `TriangularUnitPivot`, which
is the point).

**PROOF.** `by decide` on both (the domain has `16` elements; `DecidableEq (Fin 2 → ZMod 4)` and
`Fintype` are instances). If `decide` times out, `Finset.filter` + `Finset.card` by `native_decide`
is **forbidden** (it would add an axiom); instead enumerate `v 0 ∈ ZMod 4` by `decide` on the
four-case split.

**SIZE.** 14 lines.

**SOURCE.** `EFF.GENIND.155` (`R2.0`, CODEX F1's counterexample verbatim: *"Codex's valid toy:
`(x, y) ↦ (x, (x+π)y)` mod `π²`, triangular, fiber collapses at `x = 0`"*), with the spec's own
ARITHMETIC AUDIT: *"Concretely over `ℤ/4` (π = 2): at `x = 0`, `(0+2)y = 2y ∈ {0, 2}` for
`y ∈ {0,1,2,3}` — image size 2, fibre size 2; at `x = 1`, `3y` is a bijection — image size 4, fibre
size 1 ✓. **The toy is valid and the collapse is exactly as described.** Triangularity holds
throughout ✓"*; `EFF.GENIND.156` (the rider's sharpness witness); `EFF.GENIND.157` (*"The toy's pivot
`x + π` is the lead of a non-monic multiplier — a shape the displayed species exclude"*).

**⚠ WHY THE COUNTEREXAMPLE IS A NODE AND NOT A COMMENT.** Three reasons, all recorded in the corpus.
(1) The gap was **invisible to the battery by construction** (`EFF.GENIND.155`'s TEETH: *"the runner
only ever executes monic ledgers, so the failure mode is off its state space … the runs EXCLUDE the
signature and therefore cannot FIND the missing hypothesis"*). (2) `EFF.GENIND.157`'s species check is
`PROOF-ONLY`, so the *only* machine evidence for the whole repair is leg G's planted mutant — and this
node is that mutant, promoted to a theorem. (3) A future node tempted to state "triangular ⟹
bijective" is refuted here, loudly. **This is the §9 analogue of H.06/H.11/H.12: the refutation is
part of the deliverable.**

**ARITHMETIC AUDIT.** Fibre over `![0,0]`: `v 0 = 0` and `2 * v 1 = 0` ⟹ `v 1 ∈ {0, 2}` ⟹ 2 ✓.
Fibre over `![1,0]`: `v 0 = 1` and `3 * v 1 = 0` ⟹ `v 1 = 0` (3 is a unit mod 4) ⟹ 1 ✓. Image size:
at `v 0 = 0` the second coordinate ranges over `{0,2}` (2 values); at `v 0 ∈ {1,3}` over all 4; at
`v 0 = 2` the pivot is `4 = 0`, so the second coordinate is `0` only (1 value). Total image
`2 + 4 + 1 + 4 = 11 < 16` ✓ **not surjective**, and `![0,1]` is missing ✓.

**TEETH.** machine leg G (the planted mutant) → **Lean theorem**. Disposition upgrade recorded: the
corpus's evidence is a mutant that *fired*; chapter H's is a proof.

**ENVIRONMENT.** ENV-H5 with `R := ZMod 4` (a concrete instance; no `variable`s).

---

## 10. §10 — THE DRAINAGE-RATE CALCULUS

> This section is the corpus's ANNEX-R/annex-r1/round-2 stack (`EFF.GENIND.149`–`.204`) with the
> geometry replaced by `StageInterface`'s fields. `EFF.GENIND.170` (`R6.2`) is the licence that makes
> it bound-direction-only: *"(CS-EXACT) is required because the induction propagates the
> exact-complement IDENTITY … NOT because bounds fail to propagate: upper bounds propagate by
> monotonicity + union bound"*.

### NODE H.63 [theorem] [fresh]

**STATEMENT.** *The union bound (`GENIND-C1`(ii), leg F).* For a `Finset` index `s` and reals
`0 ≤ u i ≤ T i`: `∏_{i∈s} T i − ∏_{i∈s} (T i − u i) ≤ Σ_{i∈s} (u i * ∏_{j∈s, j≠i} T j)`.
**No exactness hypothesis** — the bound direction needs only nonnegativity.

**SIGNATURE.**
```lean
namespace Uniformity.Density.Induction

theorem prod_sub_prod_le_sum {ι : Type*} [DecidableEq ι] (s : Finset ι) (u T : ι → ℝ)
    (hu : ∀ i ∈ s, 0 ≤ u i) (huT : ∀ i ∈ s, u i ≤ T i) :
    ∏ i ∈ s, T i - ∏ i ∈ s, (T i - u i) ≤ ∑ i ∈ s, u i * ∏ j ∈ s.erase i, T j
```

**DEPENDS.** none · mathlib `Finset.prod_insert`, `Finset.induction_on`, `Finset.sum_insert`.

**PROOF.** induction on `s` (`Finset.induction_on`).
1. base `s = ∅`: `1 − 1 = 0 ≤ 0` ✓.
2. step `s = insert a t`, `a ∉ t`. Write `P := ∏_{t} T`, `P' := ∏_{t}(T−u)`, and note `0 ≤ P'` and
   `P' ≤ P` (both by `Finset.prod_le_prod` from `0 ≤ T i − u i ≤ T i`).
   `∏_{insert a t} T − ∏_{insert a t}(T−u) = T a · P − (T a − u a)·P'`
   `= T a · (P − P') + u a · P'`
   `≤ T a · (Σ_{i∈t} u i ∏_{j∈t.erase i} T j) + u a · P` (IH, and `P' ≤ P`, `0 ≤ u a`)
   `= Σ_{i∈t} u i ∏_{j∈(insert a t).erase i} T j + u a ∏_{j∈t} T j`
   `= Σ_{i ∈ insert a t} u i ∏_{j∈(insert a t).erase i} T j` ✓.
3. the two `erase` rewrites are `Finset.erase_insert_of_ne` and `Finset.erase_insert`.

**SIZE.** 34 lines. **SPLIT MANDATED:** land the two monotonicity `have`s (`0 ≤ ∏(T−u)` and
`∏(T−u) ≤ ∏T`) as a separate small node or as private helpers; they are reused by H.64.

**SOURCE.** `EFF.GENIND.152` (`GENIND-C1`(ii), verbatim: *"Bounding the inclusion–exclusion by the
UNION BOUND (leg F: the difference `Σ_l u_l·Π_{j≠l}T_j − [ΠT − Π(T−u)]` expands with nonnegative
coefficients in `(u_l, T_l − u_l)` at `r = 2, 3` — **no exactness is needed for the BOUND direction**;
see R6)"*), with the spec's audit: *"expanding `Π(T_j − u_j)` and comparing, the difference is a sum of
products with at least two `u`-factors, all nonnegative ✓"*; `EFF.GENIND.170` (`R6.2`, the
identity-vs-bound separation).

**⚠ THIS NODE GENERALIZES THE CORPUS'S OWN CHECK FROM `r = 2, 3` TO EVERY `r`.** Leg F is symbolic at
`r = 2, 3` only. The induction here is uniform in `#s`, which is what `GENIND-C1`(iii)'s summation over
an arbitrary child family needs. **Hypotheses at their true minimum**: `0 ≤ u i` and `u i ≤ T i` on `s`
only — no `0 < T i`, no exactness, no finiteness beyond `Finset`.

**TEETH.** `EFF.GENIND.152`'s machine leg F (the union-bound dominance symbolically at `r = 2, 3`) →
**Lean theorem** at every `r`.

**ENVIRONMENT.** ENV-H1.

---

### NODE H.64 [lemma] [fresh]

**STATEMENT.** *Monotonicity of the composed undecided mass (`R6.1`).* With `0 ≤ u i ≤ v i ≤ T i` on
`s`: `∏_{s} T − ∏_{s}(T − u) ≤ ∏_{s} T − ∏_{s}(T − v)`. Equivalently
`∏_{s}(T − v) ≤ ∏_{s}(T − u)`: the composed mass is coordinatewise nondecreasing in the child `u`'s.

**SIGNATURE.**
```lean
namespace Uniformity.Density.Induction

theorem prod_sub_antitone {ι : Type*} (s : Finset ι) (u v T : ι → ℝ)
    (h0 : ∀ i ∈ s, 0 ≤ u i) (huv : ∀ i ∈ s, u i ≤ v i) (hvT : ∀ i ∈ s, v i ≤ T i) :
    ∏ i ∈ s, (T i - v i) ≤ ∏ i ∈ s, (T i - u i)
```

**DEPENDS.** none · mathlib `Finset.prod_le_prod`.

**PROOF.** `Finset.prod_le_prod`: each factor satisfies `0 ≤ T i − v i` (from `hvT`) and
`T i − v i ≤ T i − u i` (from `huv`, `sub_le_sub_left`).

**SIZE.** 8 lines.

**SOURCE.** `EFF.GENIND.168` (`R6.0`, CODEX F4 quoted: *"PE8 §4.1's necessity rationale is false:
`∂F/∂u₁ = T₂ − u₂ ≥ 0` (claimed non-monotonicity wrong); `1 − Π(1 − u_i/T_i)` is coordinatewise
increasing; upper bounds + union bound suffice for W-12's (A2); exactness needed only for the stronger
exact-complement member"*); `EFF.GENIND.25` (`R6.1`'s correction: *"`∂/∂u_i[Π_j T_j − Π_j(T_j − u_j)] =
Π_{j≠i}(T_j − u_j) ≥ 0` — the composed undecided mass is coordinatewise NONDECREASING in the child
`u`'s"*).

**⚠ WHOSE CLAIM WAS FALSE.** `EFF.GENIND.168`'s CONDITIONALITY: *"The finding's target is the
ACCEPTANCE REPORT, not the note … **This is the only finding in the corpus's GENIND arc that lands on
the artifact that granted acceptance.** It does not disturb the acceptance: the note's own load-bearing
sentences survive."* Chapter H lands the true monotonicity; it does not reproduce the false rationale.
`EFF.GENIND.25`'s SUPERSESSION KIND is `none received` — `GENIND-C1(ii)` and `R6.1` are *consumers* of
the drain-composition clause, not supersessions of it — *"recorded here so a merge does not mistake
them for edits"*, and chapter H does not.

**TEETH.** `EFF.GENIND.14`'s machine leg F (`dF/du₁ = T₂ − u₂`; `∂G/∂u_i = Π_{j≠i}(T_j − u_j)` at
`r = 2, 3`; the union-bound dominance certificates) with its decorrelation record (*"the fold's
scaffold P-4 PREREGISTERED the same arithmetic before the run and its sympy leg confirmed it — two
decorrelated models, same kill"*) → **Lean theorem** at every `r`.

**ENVIRONMENT.** ENV-H1.

---

### NODE H.65 [def] [fresh]

**STATEMENT.** *The `(A2-RATE)` species, as a predicate.* For `Q : ℕ` with `2 ≤ Q`, a normalized
complement `f : ℕ → ℝ` **has the rate species with constants `(K, B, c)`** when
`∀ M, 1 ≤ M → f M ≤ K * (M:ℝ)^B * ((Q:ℝ)^(M − c))⁻¹`.

**SIGNATURE.**
```lean
namespace Uniformity.Density.Induction

/-- **(A2-RATE)** — the species pinned onto `P(k)`'s fourth member (`ANNEX R R1.1`): a normalized
conservative complement decays with a POLYNOMIAL coefficient and an EXPONENTIAL deficit, with
constants depending on the degree data only. -/
def RateSpecies (Q : ℕ) (K : ℝ) (B c : ℕ) (f : ℕ → ℝ) : Prop :=
  ∀ M, 1 ≤ M → f M ≤ K * (M : ℝ) ^ B * ((Q : ℝ) ^ (M - c))⁻¹
```

**DEPENDS.** none.

**PROOF.** definitional.

**SIZE.** 6 lines.

**SOURCE.** `EFF.GENIND.151` (`R1.1`'s species pin, verbatim: *"**(A2-RATE)** the conservative
complement `u_{μ,d}(M)` is an exact finite sum of signed `q`-power terms whose term count and
coefficients are polynomially bounded in `M`; in particular there are constants `(K, B, c)` depending
on `(μ, d)` only with `u_{μ,d}(M) / Q^{μ(M−1)} ≤ K·M^B·Q^{−(M−c)}`"*).

**⚠ THE PREDICATE DROPS THE "EXACT FINITE SUM" CLAUSE — DELIBERATELY.** `(A2-RATE)` as displayed has
two halves: an *exactness* half (finite sum of signed `q`-powers, polynomially many terms) and a *rate*
half (the displayed inequality). `EFF.GENIND.170` (`R6.2`) separates their consumers: the identity
consumer needs exactness, the bound consumer needs only the rate. Every chapter-H consumer (H.67,
H.68, H.71, H.72) is a bound consumer, so `RateSpecies` is the rate half alone. **A node needing the
exactness half must return `RE-PLAN`** for an `ExactSpecies` predicate — and should note that its only
supplier would be `StageInterface`'s absent `(CS-EXACT)` field (H.09's signature note).

**TEETH.** `EFF.GENIND.151`: *"nothing for the general species, which is why it is a hypothesis pin
and not a theorem"* — `signed vacuity disclosure` at general `(μ, d)`, **carried unchanged**. The
predicate is discharged at `μ = 2` by H.28 and nowhere else in this chapter.

**ENVIRONMENT.** ENV-H1.

---

### NODE H.66 [lemma] [fresh]

**STATEMENT.** *The species is closed under domination and under constant inflation.* Two clauses.
(i) if `RateSpecies Q K B c f` and `g M ≤ f M` for all `M ≥ 1` then `RateSpecies Q K B c g`.
(ii) if `RateSpecies Q K B c f` and `K ≤ K'`, `B ≤ B'`, `c ≤ c'` with `2 ≤ Q`, `0 ≤ K`, then
`RateSpecies Q K' B' c' f`.

**SIGNATURE.**
```lean
namespace Uniformity.Density.Induction

theorem RateSpecies.of_le {Q : ℕ} {K : ℝ} {B c : ℕ} {f g : ℕ → ℝ}
    (h : RateSpecies Q K B c f) (hg : ∀ M, 1 ≤ M → g M ≤ f M) : RateSpecies Q K B c g

theorem RateSpecies.mono {Q : ℕ} (hQ : 2 ≤ Q) {K K' : ℝ} {B B' c c' : ℕ} {f : ℕ → ℝ}
    (h : RateSpecies Q K B c f) (hK : K ≤ K') (hK0 : 0 ≤ K) (hB : B ≤ B') (hc : c ≤ c') :
    RateSpecies Q K' B' c' f
```

**DEPENDS.** H.65 · mathlib `one_le_pow`, `inv_le_inv_of_le`, `pow_le_pow_right`.

**PROOF.**
1. `of_le`: `le_trans (hg M hM) (h M hM)`.
2. `mono`: chain three monotonicities — `K ≤ K'`; `(M:ℝ)^B ≤ (M:ℝ)^B'` for `M ≥ 1`
   (`pow_le_pow_right` with `1 ≤ (M:ℝ)`); and `((Q:ℝ)^(M−c))⁻¹ ≤ ((Q:ℝ)^(M−c'))⁻¹` because
   `M − c' ≤ M − c` and `Q ≥ 2 > 1` (`inv_le_inv_of_le`, `pow_le_pow_right`). Combine with
   `mul_le_mul` (all factors nonnegative).

**SIZE.** 16 lines.

**SOURCE.** `EFF.GENIND.153` (the `c`-choice `c := c′ + 1` and its absorption of the head leg:
*"`c ≥ c₀ + 1 ≥ 2 ≥ 1` absorbs the head leg (`Q^{−(N−1)} ≤ Q^{−(N−c)}` iff `c ≥ 1`)"* — that is
clause (ii) at `B = B'`); `EFF.GENIND.152`(iii) (the two-regime split, whose legs are combined by
domination — clause (i)).

**TEETH.** none in the corpus (the closure is **PROOF-ONLY**) → **Lean theorem**. This node is the
bookkeeping that makes H.71's three-leg sum a one-line `RateSpecies` conclusion rather than three
`calc` blocks.

**ENVIRONMENT.** ENV-H1.

---

### NODE H.67 [theorem] [fresh]

**STATEMENT.** *The GROWING regime.* Fix `2 ≤ Q`, `1 ≤ D`, `c ≤ M`, `D + M = N`, and a child
complement fraction `δ` with `δ ≤ K * (M:ℝ)^B * ((Q:ℝ)^(M − c))⁻¹` (the child's `(A2-RATE)` at its
strictly lower degree), and a route prefactor `ρ ≤ ((Q:ℝ)^(D − 1))⁻¹` (H.36's codimension). Then
`ρ * δ ≤ K * (N:ℝ)^B * ((Q:ℝ)^(N − 1 − c))⁻¹` — **the exponents compose exactly**.

**SIGNATURE.**
```lean
namespace Uniformity.Density.Induction

theorem rate_growing {Q : ℕ} (hQ : 2 ≤ Q) {K : ℝ} {B c D M N : ℕ} (hK : 0 ≤ K)
    (hD : 1 ≤ D) (hc : c ≤ M) (hDM : D + M = N) {ρ δ : ℝ}
    (hρ0 : 0 ≤ ρ) (hδ0 : 0 ≤ δ)
    (hρ : ρ ≤ ((Q : ℝ) ^ (D - 1))⁻¹)
    (hδ : δ ≤ K * (M : ℝ) ^ B * ((Q : ℝ) ^ (M - c))⁻¹) :
    ρ * δ ≤ K * (N : ℝ) ^ B * ((Q : ℝ) ^ (N - 1 - c))⁻¹
```

**DEPENDS.** H.34, H.36, H.65, H.66.

**PROOF.**
1. `ρ * δ ≤ ((Q:ℝ)^(D−1))⁻¹ * (K * M^B * ((Q:ℝ)^(M−c))⁻¹)` by `mul_le_mul` (all nonnegative).
2. regroup: `= K * M^B * (((Q:ℝ)^(D−1)) * ((Q:ℝ)^(M−c)))⁻¹`; the product of powers is
   `(Q:ℝ)^((D−1)+(M−c)) = (Q:ℝ)^(N−1−c)` by H.34's `exp_compose`.
3. `M ≤ N` from `hDM`, so `(M:ℝ)^B ≤ (N:ℝ)^B` (`pow_le_pow_left`, `Nat.cast_le`); conclude by
   `mul_le_mul_of_nonneg_right`.

**SIZE.** 18 lines.

**SOURCE.** `EFF.GENIND.152` (`GENIND-C1`(iii)'s GROWING branch, verbatim: *"GROWING (`M_l > c₀`): the
child's (A2-RATE) at its strictly lower degree `μ_l·d < m·d` ((IH), degree descent GENIND-1(iii)) gives
`u_l/T_l ≤ K·M_l^B·Q^{−(M_l−c)}`; with (i), `contribution_l ≤ K·N^B·Q^{−(D_l−1)−(M_l−c)} =
K·N^B·Q^{−(N−c−1)}` — the exponents COMPOSE EXACTLY because `D_l + M_l = N`"*).

**⚠ THE DEGREE DESCENT IS A HYPOTHESIS, NOT A PROOF.** *"the child's (A2-RATE) at its strictly lower
degree … ((IH), degree descent GENIND-1(iii))"* — the descent `μ_l·d < m·d` is geometric
(`GENIND-1(iii)`, fracture permanence, honesty item H-3) and the `(IH)` is the strong induction's.
This node takes the child's rate bound `hδ` as a hypothesis, which is exactly the interface; H.71
supplies it from the induction.

**TEETH.** `EFF.GENIND.152`'s legs D/E (the depth identity at six committed extractions; the prefactor
bound at three loci), **with the disclosed reach limit** *"legs D/E cover six extractions and three
loci, all at `n ≤ 6`"* → **Lean theorem** at every `(D, M, N)`.

**ENVIRONMENT.** ENV-H1.

---

### NODE H.68 [theorem] [fresh]

**STATEMENT.** *The BOUNDED regime — Codex's half, now displayed.* Fix `2 ≤ Q`, `1 ≤ D`,
`D + M = N`, a threshold `c₀` with `M ≤ c₀`, and `0 ≤ δ ≤ 1` (the trivial child bound — **the child
limit is never invoked**), with `ρ ≤ ((Q:ℝ)^(D − 1))⁻¹`. Then
`ρ * δ ≤ ((Q:ℝ)^(N − c₀ − 1))⁻¹`: the **route prefactor carries the whole rate**.

**SIGNATURE.**
```lean
namespace Uniformity.Density.Induction

theorem rate_bounded {Q : ℕ} (hQ : 2 ≤ Q) {D M N c₀ : ℕ} (hD : 1 ≤ D) (hDM : D + M = N)
    (hM : M ≤ c₀) {ρ δ : ℝ} (hρ0 : 0 ≤ ρ) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hρ : ρ ≤ ((Q : ℝ) ^ (D - 1))⁻¹) :
    ρ * δ ≤ ((Q : ℝ) ^ (N - c₀ - 1))⁻¹
```

**DEPENDS.** H.36, H.66.

**PROOF.**
1. `ρ * δ ≤ ρ * 1 = ρ ≤ ((Q:ℝ)^(D−1))⁻¹`.
2. `D − 1 = N − M − 1 ≥ N − c₀ − 1` from `hDM`, `hM` (`omega`).
3. hence `((Q:ℝ)^(D−1))⁻¹ ≤ ((Q:ℝ)^(N−c₀−1))⁻¹` by `inv_le_inv_of_le` and
   `pow_le_pow_right (1 ≤ Q)`.

**SIZE.** 12 lines.

**SOURCE.** `EFF.GENIND.152` (`GENIND-C1`(iii)'s BOUNDED branch, verbatim: *"BOUNDED (`M_l ≤ c₀`): the
child limit is never invoked; the trivial `u_l/T_l ≤ 1` and (i) alone give
`contribution_l ≤ Q^{−(D_l−1)} = Q^{−(N−M_l−1)} ≤ Q^{−(N−c₀−1)}` — the route prefactor carries the
whole rate, **which is Codex's bounded-M_l half, now displayed**"*); `EFF.GENIND.149` (`R1.0`'s half
(ii), the defect this repairs, verbatim: *"a capped child window `M_l = N − D_l` can stay BOUNDED while
the genre depth `D_l` grows with `N`, and there the child's own `M_l → ∞` vanishing cannot be applied —
those β-terms vanish only through the route prefactor, and no bounded-vs-growing split was
displayed"*).

**⚠ THIS IS THE MATHEMATICALLY SUBSTANTIVE HALF OF `CODEX F3`.** `EFF.GENIND.149`'s CONDITIONALITY:
*"**Half (ii) is the mathematically substantive one** and is what forces GENIND-C1(iii)'s two-regime
split; half (i) is a hypothesis-display gap."* The pair (H.67, H.68) is the split; **neither node alone
discharges the defect**, and a fleet agent landing only H.67 has reproduced the defect.

**TEETH.** `decorrelated-model audit` (`EFF.GENIND.149`: *"Eight in-house hostile passes did not find
it, and no battery row could have: the runner computes exact counts, and an exact count is silent about
the RATE its own asymptotics need"*) → **Lean theorem**.

**ENVIRONMENT.** ENV-H1.

---

### NODE H.69 [lemma] [fresh]

**STATEMENT.** *Summing the two regimes over a child family and over genres.* Given a `Finset` of
children each contributing at most `K * (N:ℝ)^B * ((Q:ℝ)^(N−1−c))⁻¹` (H.67) or at most
`((Q:ℝ)^(N−c₀−1))⁻¹` (H.68), and at most `p * N^m` genres (H.37's slope-tuple bound times an opaque
arrangement count `p`), the total is at most
`(#children) * p * (N:ℝ)^m * (K * (N:ℝ)^B + 1) * ((Q:ℝ)^(N−1−c'))⁻¹` with `c' = max c c₀`.

**SIGNATURE.**
```lean
namespace Uniformity.Density.Induction

theorem rate_sum_over_family {Q : ℕ} (hQ : 2 ≤ Q) {K : ℝ} {B c c₀ N m p r : ℕ} (hK : 0 ≤ K)
    (hN : 1 ≤ N) (g : Fin r → ℝ) (hg0 : ∀ i, 0 ≤ g i)
    (hg : ∀ i, g i ≤ K * (N : ℝ) ^ B * ((Q : ℝ) ^ (N - 1 - max c c₀))⁻¹) :
    (p * N ^ m : ℝ) * ∑ i, g i
      ≤ (r * p : ℝ) * (N : ℝ) ^ m * (K * (N : ℝ) ^ B) * ((Q : ℝ) ^ (N - 1 - max c c₀))⁻¹
```

**DEPENDS.** H.37, H.66, H.67, H.68.

**PROOF.**
1. `Finset.sum_le_card_nsmul` (or `Finset.sum_le_sum` then `Finset.sum_const`) gives
   `Σ_i g i ≤ r * (K * N^B * ((Q:ℝ)^(N−1−max c c₀))⁻¹)`.
2. multiply by the nonnegative `p * N^m` and regroup by `ring_nf`.
3. **Uniformizing the two regimes first** is the caller's job: apply `RateSpecies.mono` (H.66(ii))
   to the BOUNDED bound with `K' := max K 1`, `B' := B`, `c' := max c c₀` so both regimes have the
   same shape; that is why `hg` is stated with `max c c₀`.

**SIZE.** 16 lines.

**SOURCE.** `EFF.GENIND.152` (`GENIND-C1`(iv), verbatim: *"Summing (ii)–(iii) over children and (iv)
over genres: the recursion's β-part contributes `≤ m·p̃(m)·K·N^{m+B}·Q^{−(N−c′−1)}` relative mass,
`c′ = max(c, c₀)` — exactly the consumed sentence's `O(poly(N)·Q^{−(N−c)})`, now DERIVED from the
displayed (A2-RATE) + GENIND-3's fibration + the depth identity. ∎"*).

**⚠ `p̃(m)` IS OPAQUE HERE (see H.37's fence).** The corpus's `p̃(m)` counts arrangement types — frame
grammar, chapter C. This node takes `p : ℕ` as a parameter and `r : ℕ` as the child count. The
conclusion's shape `poly(N) · Q^{−(N−c)}` is what `RateSpecies` recognizes, and H.66's `mono` converts
the displayed constant into `(K'', m + B, c′)`.

**TEETH.** as H.67/H.68 → **Lean theorem**.

**ENVIRONMENT.** ENV-H1.

---

### NODE H.70 [theorem] [fresh]

**STATEMENT.** *`GENIND-C2D` IN `leanfinal`'s OWN TERMS: `undecidedSeq` IS ANTITONE.* For every
complete DVR `O` with finite residue field, every `n`, and every `T ≤ W`:
`undecidedSeq O n W ≤ undecidedSeq O n T`. Consequently the conservative-undecided *fraction* cannot
increase when the window grows, which is the well-foundedness ingredient the corpus's descent argument
needed.

**SIGNATURE.**
```lean
namespace Uniformity.Density

theorem undecidedSet_preimage_subset {O : Type*} [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [Finite (IsLocalRing.ResidueField O)] {n T W : ℕ} (h : T ≤ W) :
    undecidedSet O n W ⊆ coeffFactor (O := O) (n := n) h ⁻¹' undecidedSet O n T

theorem undecidedSeq_antitone {O : Type*} [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [Finite (IsLocalRing.ResidueField O)] (n : ℕ) :
    Antitone (undecidedSeq O n)
```

**DEPENDS.** landed `Uniformity.Density.undecidedSet`, `undecidedCount`, `undecidedSeq`,
`UndecidedAt`, `DecidedAt`, `coeffFactor`, `coeffFactor_proj`, `card_preimage_coeffFactor`,
`card_coeff`, `residueCard`, `two_le_residueCard`, `proj_surjective`.

**PROOF.**
1. **The containment.** Let `c ∈ undecidedSet O n W`, i.e. no `σ` is decided on `c` at level `W`.
   Suppose some `σ` were decided on `coeffFactor h c` at level `T`. Then for every lift `a` with
   `proj O n W a = c` we have `proj O n T a = coeffFactor h (proj O n W a) = coeffFactor h c`
   (`coeffFactor_proj`), so `typeOf (monicPoly a) = σ` — i.e. `σ` is decided on `c` at level `W`,
   contradiction. Hence `coeffFactor h c ∈ undecidedSet O n T`.
2. **The count.** `undecidedCount O n W ≤ Nat.card (coeffFactor h ⁻¹' undecidedSet O n T)`
   (`Nat.card_le_card_of_subset`, both finite), and the right side is
   `undecidedCount O n T * residueCard O ^ (n * (W − T))` by `card_preimage_coeffFactor`.
3. **The ratio.** Divide by `residueCard O ^ (n * W)`:
   `undecidedSeq O n W ≤ undecidedCount O n T * q^(n*(W−T)) / q^(n*W)
    = undecidedCount O n T / q^(n*T) = undecidedSeq O n T`
   using `n*(W−T) + n*T = n*W` (`omega` with `T ≤ W`) and `q > 0` (`two_le_residueCard`).
4. `Antitone` is `fun T W h => …` with the inequality above (note `Antitone f` unfolds to
   `a ≤ b → f b ≤ f a`).

**SIZE.** 36 lines. **SPLIT MANDATED:** land `undecidedSet_preimage_subset` and
`undecidedSeq_antitone` as two declarations in one node file; the containment is the mathematical
content and the ratio is bookkeeping. **VERIFY `card_preimage_coeffFactor`'s exact shape before
starting** — it is landed (`Uniformity/Density/LocalData.lean`) and its exponent convention fixes
step 2's arithmetic.

**SOURCE.** `EFF.GENIND.201` (`ANNEX-LEMMA GENIND-C2D`, verbatim: *"Let `δ_{μ,K}(W)` be the
conservative-undecided fraction of a `(μ,K)`-cluster system at window `W`. If `1≤T≤W`, then
`δ_{μ,K}(W)≤δ_{μ,K}(T)`. *Proof.* Reduction from window `W` to `T` has constant fibers. If a truncation
were decided at window `T`, its decision would depend only on digits below `T`, and the same
certificate would decide every lift at window `W`. Hence every window-`W` undecided state lies above a
window-`T` undecided state. Dividing the resulting cardinality inequality by the two total state counts
gives (C2D.1)."*), with the spec's own audit reproducing every step and its **compiler observation**:
*"The argument needs the read to be MONOTONE IN THE WINDOW … That is exactly the conservative-drain
convention's content … **The proof does not cite that convention explicitly**; the step "the same
certificate would decide every lift at window `W`" is where it is used. Recorded as a compressed
citation, not a gap."*

**⚠ THE COMPRESSED CITATION IS DISCHARGED HERE, AND THAT IS WHY THIS NODE IS THE BEST IN §10.** In
`leanfinal`, `DecidedAt O n σ N c` is *by definition* "every lift of `c` has type `σ`" — window
monotonicity of the read is not a convention to cite but a **consequence of the definition**, via
`coeffFactor_proj`. So the corpus's compressed citation becomes a two-line Lean step, and the lemma
becomes unconditional at general `O` with no drain convention assumed. **This is the chapter's
strongest single result about a landed object.**

**ARITHMETIC AUDIT (cross-checked against chapter G's landed `n = 2` law).** Chapter G lands
`undecidedCount_two_eq : undecidedCount O 2 N = residueCard O ^ N` and
`undecidedSeq_two_eq : undecidedSeq O 2 N = (residueCard O : ℝ)^N / (residueCard O : ℝ)^(2*N)`, i.e.
`q^{−N}`. Antitone ✓ (`q^{−W} ≤ q^{−T}` for `T ≤ W`, `q ≥ 2`) — **the chapter-G exact law is a
witness that this node's conclusion is non-vacuous and sharp at `n = 2`.** At `q = 2`: `1/2, 1/4,
1/8, …` ✓ decreasing. At `q = 3`: `1/3, 1/9, …` ✓. Chapter G's `n = 3` bound
`card_le_undecidedCount_three` gives `q^N ≤ undecidedCount O 3 N`, so
`undecidedSeq O 3 N ≥ q^{N}/q^{3N} = q^{−2N}` — also compatible with antitonicity ✓ (a *lower* bound
does not contradict it).

**TEETH.** `EFF.GENIND.201`'s disposition is `signed vacuity disclosure` — *"a new unexercised lemma.
(Its content is however IMPLIED by every GT-DEPTH0 row, which reads the same states at nested windows;
no row tests the inequality directly.)"* → **Lean theorem**, and the disclosure is thereby
**discharged**.

**ENVIRONMENT.** ENV-H2 (no completeness needed — `undecidedSet` and `coeffFactor` are ENV-H2 objects).

---

### NODE H.71 [theorem] [fresh]

**STATEMENT.** *`GENIND.C′` — the quantitative vanishing clause, abstractly.* Let `u : ℕ → ℕ → ℝ`
be a family of normalized complements indexed by `(degree, window)`, and suppose the three legs of the
`S5.2` recursion hold at every `(D, N)`:
(**head**) `head D N ≤ ((Q:ℝ)^(N−1))⁻¹`;
(**α**) `alpha D N ≤ Σ_{k<n₀} (Q−1)*((Q:ℝ)^(c*(k+1)))⁻¹ * u D (N − m*(k+1))` with `1 ≤ c`;
(**β**) `beta D N ≤ K' * (N:ℝ)^(m+B') * ((Q:ℝ)^(N−c'−1))⁻¹` (H.69's conclusion at strictly lower
degree);
and `u D N ≤ head D N + alpha D N + beta D N`. Then with `c := c' + 1`, `B := m + B' + 1` and `K`
large enough (H.35), `RateSpecies Q K B c (u D)` for every `D`, by lexicographic induction on
`(D, N)`.

**SIGNATURE.**
```lean
namespace Uniformity.Density.Induction

/-- The three-leg recursion hypothesis of `GENIND.C′`, packaged so the induction can be stated. -/
structure RecursionLegs (Q m c : ℕ) (u : ℕ → ℕ → ℝ) where
  head alpha beta : ℕ → ℕ → ℝ
  K' : ℝ
  B' c' n₀ : ℕ
  hK' : 0 ≤ K'
  hsplit : ∀ D N, 1 ≤ N → u D N ≤ head D N + alpha D N + beta D N
  hu0 : ∀ D N, 0 ≤ u D N
  hhead : ∀ D N, 1 ≤ N → head D N ≤ ((Q : ℝ) ^ (N - 1))⁻¹
  halpha : ∀ D N, 1 ≤ N → alpha D N ≤
    ∑ k ∈ Finset.range n₀, ((Q : ℝ) - 1) * ((Q : ℝ) ^ (c * (k + 1)))⁻¹ * u D (N - m * (k + 1))
  hbeta : ∀ D N, 1 ≤ N → beta D N ≤ K' * (N : ℝ) ^ (m + B') * ((Q : ℝ) ^ (N - c' - 1))⁻¹
  hdesc : ∀ D N k, k < n₀ → 1 ≤ m * (k + 1) → N - m * (k + 1) < N

theorem rate_close {Q m c : ℕ} (hQ : 2 ≤ Q) (hc : 1 ≤ c) (hm : 1 ≤ m)
    {u : ℕ → ℕ → ℝ} (L : RecursionLegs Q m c u) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ D, RateSpecies Q K (m + L.B' + 1) (L.c' + 1) (u D)
```

**DEPENDS.** H.30, H.35, H.65, H.66, H.69, H.70 (the window descent's well-foundedness input).

**PROOF.** the corpus's three-leg closure, transcribed.
1. Set `B := m + B' + 1`, `c := c' + 1`. Choose `K` by H.35: large enough that
   `K * ((N:ℝ)^B − (N−m)^B) ≥ 1 + K' * (N:ℝ)^(m+B')` for all `N ≥ m` (a degree-`(B−1)` polynomial
   inequality; `pow_sub_dominance` supplies the leading term). Land the choice as an explicit
   `K := 1 + L.K' + …` with the inequality proved by `nlinarith`/`positivity` per `N`.
2. **Induction.** Strong induction on `N` (the degree component is fixed inside `u D` — the
   degree descent enters only through `hbeta`, whose bound is already in the target shape).
   `Nat.strongRecOn` on `N`.
3. **Head leg.** `((Q:ℝ)^(N−1))⁻¹ ≤ K * N^B * ((Q:ℝ)^(N−c))⁻¹` because `c ≥ 1` (H.66(ii)) and
   `K * N^B ≥ 1`.
4. **α leg.** By the IH at each `N − m*(k+1) < N` (`hdesc`),
   `u D (N − m(k+1)) ≤ K * (N−m)^B * ((Q:ℝ)^(N−m(k+1)−c))⁻¹`. Multiplying by
   `(Q−1)((Q:ℝ)^(c*(k+1)))⁻¹` and summing, H.30 bounds the geometric factor by `1`, giving
   `alpha D N ≤ K * (N−m)^B * ((Q:ℝ)^(N−c))⁻¹`. **The exponent recomposition is the delicate step**:
   the corpus's own audit notes the passage uses the *weaker* `Q^{−k·c(m)}` at the geometric-sum step
   and the *sharper* `Q^{−k·m(m+1)/2}` at the locus step, and re-derives the intermediate — carry both
   as `have`s.
5. **β leg.** `hbeta` plus `c = c' + 1` makes `((Q:ℝ)^(N−c'−1))⁻¹ = ((Q:ℝ)^(N−c))⁻¹` exactly.
6. **Sum.** head + α + β `≤ (1 + K*(N−m)^B + K'*N^(m+B')) * ((Q:ℝ)^(N−c))⁻¹ ≤ K*N^B*((Q:ℝ)^(N−c))⁻¹`
   by step 1's choice of `K` ✓.

**SIZE.** 60+ lines. **SPLIT MANDATED into three nodes** (record as a RE-PLAN at claim time):
**H.71a** the `K`-choice (step 1, a standalone real-polynomial lemma), **H.71b** the three leg bounds
(steps 3–5, each a `calc`), **H.71c** the induction assembly (steps 2, 6). **This is the chapter's
critical-path node and its schedule risk.**

**SOURCE.** `EFF.GENIND.153` (`ANNEX-THEOREM GENIND.C′`, quoted in full in the spec, with its
`[ar1, MINOR-1]` `c`-choice rider *"`c := c′ + 1` … `c′ = max(children's c, c₀)` is degree-induction
data, so no circularity; with `c = c′ + 1` the β-leg's `Q^{−(N−c′−1)} = Q^{−(N−c)}` EXACTLY"*), and the
spec's audit which re-derives every leg and records the one compressed step: *"The α-leg's two exponent
forms are both correct at their own points but the passage does not spell out the intermediate step
between them; the compiler re-derived it above. Recorded as a **compressed step, not a gap** — the
arithmetic closes."*

**⚠ SCOPE: THE SIMPLE SLICE ONLY, AND IT IS UNCONDITIONAL THERE.** `EFF.GENIND.153`: *"UNCONDITIONAL
on the simple slice — the one unconditional addition of the whole annex stack, and the reason `.151`'s
split is honest. Its scope is exactly THEOREM GENIND.C's: the simple slice, all `(m, d)`, every window
`N ≥ 1`"* — and the `N ≥ 1` consumes `R3`'s window-1 rider (H.22/H.24). The CS-drain half is H.72's,
under `(CS-1Q)`. **A node claiming `rate_close` for the full complement is a defect.**

**TEETH.** **PROOF-ONLY** (`EFF.GENIND.153`: *"the induction itself is unguarded — no battery row
exercises a lexicographic induction"*, with H.28's ground instance as the only anchor) → **Lean
theorem**, and the anchor is landed at H.28.

**ENVIRONMENT.** ENV-H1.

---

### NODE H.72 [theorem] [fresh]

**STATEMENT.** *`GENIND-C2Q` — the loss-priced CS-drain exponent.* Let `G` be a genre datum, `S`
the actual side length, `H` the entry height, and `I : StageInterface G N H S`. Suppose the entry mass
obeys `ρ ≤ ((Q:ℝ)^(bS*H + I.entryCodim))⁻¹` in the `2*`-cleared form of H.33, and the stage drain
obeys `δ ≤ K★ * (N:ℝ)^B★ * ((Q:ℝ)^(f₁ * I.stageWindow))⁻¹`. Then
`ρ * δ ≤ K★ * (N:ℝ)^B★ * ((Q:ℝ)^(a*(N−1)))⁻¹ * ((Q:ℝ)^(H/2))⁻¹ * (Q:ℝ)^(I.slack)`
— i.e. the exponent is `−a(N−1) − H/2 + O_G(1)`, exactly `(C2Q.1)`.

**SIGNATURE.**
```lean
namespace Uniformity.Density.Induction

/-- **(C2Q.1)** — the loss-priced stage-drain exponent, in the `2*`-cleared form.  The conclusion's
exponent inequality is stated over `ℤ` so no `ℕ`-truncation can hide a sign. -/
theorem rate_lossPriced {G : GenreDatum} {N H S : ℕ} (I : StageInterface G N H S) :
    2 * (G.f₁ * I.stageWindow) + 2 * ((S + 1) * H) + 2 * (2 * I.entryCodim)
      ≥ 2 * (2 * G.keyDeg * (N - 1 - H)) + 2 * (2 * G.keyDeg * H) + H
        - 2 * (2 * I.slack)
```

**⚠ SIGNATURE NOTE — READ BEFORE CLAIMING.** The displayed inequality above is the **exponent
bookkeeping** of `(C2Q.1)`, cleared of every division and stated in `ℕ` with the slack on the small
side. It is **deliberately not** the real-analytic product bound: the product bound needs `ρ` and `δ`
as hypotheses with three more nonnegativity side conditions, and the whole content of the corpus's
proof is the *exponent* algebra (its own audit: *"Multiplying: exponent `= −b_S H − C_extra − a(N−1−H)
+ γΔ_G + O(1) = −a(N−1) − (b_S − a)H − C_extra + γΔ_G + O(1)` ✓ as displayed. Applying (CS-1Q.b): the
exponent `≤ −a(N−1) − H/2 + O(1)` ✓ **exact**"*). **The fleet agent's first task on this node is to
re-derive the cleared form from `I.hwin` and `I.hprice` and to CONFIRM the displayed inequality before
proving it** — if the re-derivation disagrees, that is a blueprint defect and must be returned, not
patched. The `ℤ`-valued variant is the sanctioned fallback if the `ℕ` form cannot be stated without a
truncating `-`.

**DEPENDS.** H.01, H.02, H.09, H.32, H.33, H.34.

**PROOF.**
1. from `I.hwin` (`(CS-1Q.a)`): `e₁*(N−1−H) ≤ stageWindow + stageLoss`, so
   `f₁*e₁*(N−1−H) ≤ f₁*stageWindow + f₁*stageLoss`, i.e. (with `a = keyDeg = e₁*f₁`)
   `a*(N−1−H) ≤ f₁*stageWindow + f₁*stageLoss`.
2. from `I.hprice` (`(CS-1Q.b)`): `2*(f₁*stageLoss) ≤ 2*entryCodim + (S − 2*keyDeg)*H + 2*slack`,
   and `2*keyDeg ≤ S` by H.33 (using `I.hS` and `G.hmul`), so the `(S − 2*keyDeg)` factor is honest.
3. add: `2*(a*(N−1−H)) ≤ 2*(f₁*stageWindow) + 2*entryCodim + (S−2a)*H + 2*slack`.
4. add `2*a*H` to both sides and use `(S−2a)*H + 2a*H = S*H`:
   `2*a*(N−1) ≤ 2*(f₁*stageWindow) + 2*entryCodim + S*H + 2*slack`.
5. the entry price contributes `(S+1)*H = S*H + H` (H.32's supporting-line sum at the actual side
   length), so the displayed form follows by `omega` from steps 3–4 once every product is expanded.

**SIZE.** 30 lines. Every step is `Nat`-linear once the products `f₁*e₁ = keyDeg` and
`(S−2a)*H + 2a*H = S*H` are rewritten; `omega` closes after those two `have`s (it cannot see through
the multiplications by itself).

**SOURCE.** `EFF.GENIND.198` (`ANNEX-LEMMA GENIND-C2Q`, statement `(C2Q.1)` and its proof quoted in
full in the spec, with the corrected entry count `(C2Q.2)` from `C2-G3`), and the spec's own audit:
*"**the C2Q proof is correct and every step re-derives.** It is CLEANER than `.189`'s, because the
hypothesis was reverse-engineered from the algebra."*; `EFF.GENIND.197` (`(CS-1Q.a)`/`(CS-1Q.b)`);
`EFF.GENIND.204` (`C2-G3`'s `(C2E.1)`–`(C2E.3)`).

**⚠ THE HYPOTHESIS IS NOT STRONGER THAN THE USE — AND THAT IS A DESIGN VIRTUE THE SPEC NAMES.**
`EFF.GENIND.197`'s audit: *"(CS-1Q.b) is exactly the inequality C2Q's algebra requires, no more and no
less. That is a design virtue: the hypothesis is not stronger than the use."* Chapter H's
`StageInterface.hprice` is therefore stated at exactly that strength (H.09's signature note), and this
node is the proof that consumes it. **The floor-adjacent branch** (`M_G < M₀`, where the quantitative
stage estimate is not invoked and the trivial bound `δ ≤ 1` carries) is `EFF.GENIND.198`'s second half
and is **not a separate node**: it is H.68's `rate_bounded` applied with the entry price in place of
the route prefactor, and the caller assembles it.

**TEETH.** **NONE** (`EFF.GENIND.198`: *"No machine leg was added at R11 (the r1 leg predates and was
run against `.180`). Disposition: `signed vacuity disclosure` — the lemma is proved and unexercised,
and its hypothesis is per-genre unverified"*) → **Lean theorem** for the exponent algebra; the
hypothesis's per-genre verification stays `HYP.36`, CARRY (honesty item H-2). **This node is the exact
place where the capstone's conditionality enters the Lean development, and §16's disposition table
says so.**

**ENVIRONMENT.** ENV-H1.

---

## 11. §11 — THE σ DICTIONARY AND THE `(e, f)`-FORCING CHAIN (`μ = 2` ONLY)

### NODE H.73 [def] [fresh]

**STATEMENT.** *The `μ = 2` stage leaf dictionary.* Define an inductive `StageLeaf` with three
constructors `ram`, `twoSided`, `inert`, and a map `stageSigma : GenreDatum → StageLeaf →
FactorizationType` by
`ram ↦ ⟨{(2*e₁, f₁)}⟩`, `twoSided ↦ ⟨{(e₁, f₁), (e₁, f₁)}⟩`, `inert ↦ ⟨{(e₁, 2*f₁)}⟩`.

**SIGNATURE.**
```lean
namespace Uniformity.Density.Induction

/-- The three decided leaf labels of a `μ = 2` stage read (`GENHN.C`; `SPLITEQ` and `SPLTAIL` share
`twoSided`'s σ-block, per the dictionary's own grouping). -/
inductive StageLeaf where
  | ram
  | twoSided
  | inert
  deriving DecidableEq, Fintype

/-- `GENHN.C`'s leaf dictionary, relative to the ambient. -/
def stageSigma (G : GenreDatum) : StageLeaf → FactorizationType
  | .ram      => ⟨{(2 * G.e₁, G.f₁)}⟩
  | .twoSided => ⟨{(G.e₁, G.f₁), (G.e₁, G.f₁)}⟩
  | .inert    => ⟨{(G.e₁, 2 * G.f₁)}⟩
```

**DEPENDS.** H.01 · landed `Uniformity.FactorizationType`.

**PROOF.** definitional.

**SIZE.** 16 lines.

**SOURCE.** `EFF.GENHN.15` (`THEOREM GENHN.C`, the dictionary verbatim: *"`stage-RAM ↦ {(2e₁·e_A,
f₁·f_A)} = {(2e₁, f₁)}`-block; `stage-2SIDED / SPLITEQ / SPLTAIL ↦ {(e₁, f₁), (e₁, f₁)}`;
`stage-INERT ↦ {(e₁, 2f₁)}`"*, with *"(blocks relative to the ambient; compose with the ambient's own
`(e, f)` at towers)"*).

**⚠ THREE LABELS, NOT FIVE — AND WHY.** `EFF.GENHN.38`'s Y-trichotomy has **five** cases
(`RAM`, `2SIDED`, `SPLTAIL`, `SPLITEQ`, `INERT`) but only **three** σ-blocks: `SPLTAIL` and `SPLITEQ`
both reduce to a 2SIDED configuration *for every lift* (`SPLTAIL` by the undercut floor, `SPLITEQ` by
one refine step). Chapter H's `StageLeaf` has three constructors because it is the **σ-valued**
dictionary; the five-case *read* is geometric (it is the polygon's hull position) and has no node. A
fleet agent adding `spltail`/`splitEq` constructors has changed the contract.

**TEETH.** `GN-SIGMA` (`EFF.GENHN.15`, executable regression against PARI `factorpadic`, S12 P9:
*"certified σ 37,792 jobs / 0 bad across six oracle batches"*, including **★ wild `p = 3` at an
`e₁ = 3` stage**) · `GN-T-SIG` (planted mutant: *"E31 RAM σ `{(6,1)}→{(3,2)}` must be caught by
PARI"*, fired 2/2) → **executable regression** retained for the σ *decision*; **Lean theorem** at H.74
for the degree consistency, which is the part chapter H proves.

**ENVIRONMENT.** ENV-H1.

---

### NODE H.74 [lemma] [fresh]

**STATEMENT.** *The dictionary is degree-exhausting.* For every genre datum `G` and every leaf `ℓ`:
`(stageSigma G ℓ).degree = 2 * G.keyDeg`.

**SIGNATURE.**
```lean
namespace Uniformity.Density.Induction

theorem stageSigma_degree (G : GenreDatum) (l : StageLeaf) :
    (stageSigma G l).degree = 2 * G.keyDeg
```

**DEPENDS.** H.01, H.02, H.73 · landed `FactorizationType.degree`.

**PROOF.** `cases l` then `simp [stageSigma, FactorizationType.degree, GenreDatum.keyDeg,
Multiset.map_cons, Multiset.sum_cons]` and `ring` on each of the three branches:
`ram`: `(2e₁)*f₁ = 2*(e₁*f₁)` ✓; `twoSided`: `e₁*f₁ + e₁*f₁ = 2*(e₁*f₁)` ✓;
`inert`: `e₁*(2f₁) = 2*(e₁*f₁)` ✓.

**SIZE.** 10 lines.

**SOURCE.** `EFF.GENHN.15`'s own *arithmetic audit (rule 22)*, verbatim: *"The three rows are
degree-consistent with the block degree `2e₁f₁`: RAM gives `2e₁ · f₁ = 2e₁f₁` ✓; 2SIDED gives
`2 × (e₁ · f₁) = 2e₁f₁` ✓; INERT gives `e₁ · 2f₁ = 2e₁f₁` ✓."*

**ARITHMETIC AUDIT (the four instance specializations `EFF.GENHN.15` displays, recomputed fresh).**
`(2,1,2)` → `{(4,1)}` / `{(2,1)²}` / `{(2,2)}`, each of degree `4 = 2·2` ✓.
`(1,2,2)` → `{(2,2)}` / `{(1,2)²}` / `{(1,4)}`, each `4` ✓.
`(3,1,2)` → `{(6,1)}` / `{(3,1)²}` / `{(3,2)}`, each `6 = 2·3` ✓.
`(1,3,2)` → `{(2,3)}` / `{(1,3)²}` / `{(1,6)}`, each `6` ✓.
**All four have `Σ e·f = 2e₁f₁` over the multiset**, as that spec's audit records. Cross-check against
`GENH4.C`'s two-genre dictionary (`EFF.GENH4.11`): genre E `(2,1,2)` gives
`RAM ↦ {(4,1)}`, `2SIDED ↦ {(2,1),(2,1)}`, `INERT ↦ {(2,2)}` ✓ **identical to the `(2,1,2)` row**;
genre F `(1,2,2)` gives `{(2,2)}` / `{(1,2),(1,2)}` / `{(1,4)}` ✓ **identical to the `(1,2,2)` row** —
so `GENHN.C` really is `GENH4.C` re-based, as `EFF.GENHN.15` claims (*"At `n = 4` this is THEOREM
GENH4.C verbatim"*).

**⚠ THE STRUCTURAL PARITY FACTS ARE WORTH RECORDING AND ARE NOT SEPARATE NODES.**
`EFF.GENH4.11`'s audit notes *"Genre E always has even `e`"* (every root has `v(θ) = h/2` with `h` odd,
so `2 ∣ e`) and *"Genre F always has even `f`"* (`F_{q²} ⊆ k_L`), and observes that every dictionary
entry respects them. Those are consequences of the *carrier* (chapter H's H.76 hypotheses), so they
enter as observations here rather than nodes; a reader checking the dictionary should verify them by
inspection, which the audit above does.

**TEETH.** `GN-SIGMA` (37,792/0) · `GH-SIGMA [IND]` (`EFF.GENH4.11`, PARI `factorpadic` per decided
composite member on five never-oracled fresh rows, **6,185/0** including 4,130 `q = 7` F-RAM members) ·
`GH-T-SIG` (F-RAM σ flipped `{(2,2)} → {(1,4)}`, fired) → **Lean theorem** for the degree consistency
(a necessary condition every oracle check implicitly verifies).

**ENVIRONMENT.** ENV-H1.

---

### NODE H.75 [lemma] [fresh]

**STATEMENT.** *The dictionary's instance table, as closed facts.* The four specializations of H.74:
`stageSigma ⟨2,2,1,2,h,…⟩ .ram = ⟨{(4,1)}⟩`, `.twoSided = ⟨{(2,1),(2,1)}⟩`, `.inert = ⟨{(2,2)}⟩`;
and the `(1,2,2)`, `(3,1,2)`, `(1,3,2)` rows likewise, each with degree `4`, `4`, `6`, `6`.

**SIGNATURE.**
```lean
namespace Uniformity.Density.Induction

theorem stageSigma_genreE (t : ℕ) :
    stageSigma (genreE2 t) .ram = ⟨{(4, 1)}⟩ ∧
    stageSigma (genreE2 t) .twoSided = ⟨{(2, 1), (2, 1)}⟩ ∧
    stageSigma (genreE2 t) .inert = ⟨{(2, 2)}⟩

theorem stageSigma_degree_instances (t : ℕ) :
    (stageSigma (genreE2 t) .ram).degree = 4 ∧
    (stageSigma genreA2witness .ram).degree = 6 ∧
    (stageSigma genreD2bwitness .ram).degree = 4
```

**DEPENDS.** H.06 (`genreE2`), H.11 (`genreA2witness`), H.12 (`genreD2bwitness`), H.73, H.74.

**PROOF.** `simp [stageSigma, genreE2, genreA2witness, genreD2bwitness, FactorizationType.degree]`
then `decide`/`norm_num` on each conjunct.

**SIZE.** 12 lines.

**SOURCE.** `EFF.GENHN.15`'s instance list (the four specializations at lines 1012–1016);
`EFF.GENH4.11` (the two-genre quartic dictionary).

**⚠ WHY THE WITNESS DATA ARE RE-USED.** `genreA2witness` is `(2; 3,1,2; 2)` — the `e₁ = 3` datum whose
`RAM` block is `{(6,1)}`, i.e. **the wild `p = 3`, `e₁ = 3` cell `GN-SIGMA` calls "never-oracled
territory"** and where `GN-T-SIG`'s mutant fired. Landing the dictionary value at exactly that datum
ties the σ layer to the one place the oracle's coverage is newest. `genreD2bwitness` is `(2; 1,2,2; 1)`
= genre F's datum, so the third conjunct is `GENH4.C`'s F-row.

**TEETH.** `GN-SIGMA`'s wild-`p = 3` batch · `GH-SIGMA`'s `q = 7` F-RAM members → **Lean theorem**
for the values.

**ENVIRONMENT.** ENV-H1.

---

### NODE H.76 [theorem] [fresh]

**STATEMENT.** *The `(e, f)`-forcing chain.* Let `g : Polynomial O` be monic with
`g.natDegree = e₁ * f₁`, and suppose `(typeOf g).data` is a singleton `{p}` (i.e. `g` has one
irreducible monic factor) with `e₁ ∣ p.1` and `f₁ ∣ p.2`. Then `p = (e₁, f₁)`.

**SIGNATURE.**
```lean
namespace Uniformity.Density

theorem efPair_forced_of_dvd {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {g : Polynomial O} (hg : g.Monic) {e f : ℕ} (he : 1 ≤ e) (hf : 1 ≤ f)
    (hdeg : g.natDegree = e * f) {p : ℕ × ℕ} (hp : (typeOf g).data = {p})
    (hpe : e ∣ p.1) (hpf : f ∣ p.2) : p = (e, f)
```

**DEPENDS.** landed `Uniformity.Density.typeOf`, `typeOf_data`, `efPair_pos_of_mem`,
`efPair_mul_le_natDegree`, `FactorizationType.degree`.

**PROOF.**
1. `p ∈ (typeOf g).data` from `hp` (`Multiset.mem_singleton_self`), so `0 < p.1` and `0 < p.2`
   (`efPair_pos_of_mem hg`) and `p.1 * p.2 ≤ g.natDegree = e * f`
   (`efPair_mul_le_natDegree hg`).
2. write `p.1 = e * s`, `p.2 = f * t` (`hpe`, `hpf`); positivity gives `1 ≤ s`, `1 ≤ t`.
3. `e * s * (f * t) ≤ e * f` with `e, f ≥ 1` forces `s * t ≤ 1`, hence `s = t = 1`
   (`Nat.le_of_mul_le_mul_left` twice, then `Nat.eq_one_of_mul_eq_one_left`/`omega`).
4. `Prod.ext` on `p.1 = e`, `p.2 = f`.

**SIZE.** 20 lines.

**SOURCE.** `EFF.GENHN.15`'s proof structure and `EFF.GENHN.38`'s five cases, each of which closes
*"by `e·f ≥ block degree ⟹ equality`"*; `EFF.GENHN.21` (the carrier forcing chain at S3.1: *"`e·f ≤
[R : Ô] = D′ = e₁f₁` forces `e = e₁`, `f = f₁`"*); `EFF.GENHN.42`(i) (the composed chain: *"`ef ≤
[L₂ : base] ≤ deg Φ₂ = D₂ = e₁e₂f₁f₂` forces equality throughout"*).

**⚠ THE DIVISIBILITY HYPOTHESES `(T1)`/`(T2)` ARE THE GEOMETRIC INPUT AND ARE NOT PROVED HERE.**
`EFF.GENHN.38`'s two transported facts are *"`(T1) v(θ) = h/e₁, gcd(h, e₁) = 1 ⟹ e₁ | e(L)`"* and
*"`(T2) η = res(θ^{e₁}π^{−h})` generates `F_{Q^{f₁}} ⊆ k_L ⟹ f₁ | f(L)`"* — both statements about the
leaf field, resting on the carrier (ERRATUM E3). Chapter H takes them as the hypotheses `hpe`/`hpf`,
which is the honest interface: what the chapter proves is that **once the two divisibilities are
granted, the degree bound forces the pair** — and that step is where `leanfinal`'s
`efPair_mul_le_natDegree` does real work.

**⚠ EXTERNAL-QUARRY NOTE (relayed 2026-08-15, `docs/VENDOR_QUARRY_MAP_2026-08-15.md` §2.3).** There
**is** a Lean route to `(T1)`/`(T2)` at our pin, and it should be recorded rather than lost:
`Ideal.ramificationIdx_mul_inertiaDeg_of_isLocalRing`
(`Mathlib/NumberTheory/RamificationInertia/Basic.lean:650`) gives `e·f = finrank K L` for a *local*
Dedekind `S` module-finite over `R`; with `S := integralClosure O L`,
`integralClosure.isDedekindDomain_fractionRing` and `IsPrincipalIdealRing.isDedekindDomain` compose,
and the **single** missing instance is `IsLocalRing S`, which
`FLT/HenselianLocalRing/Finite.lean:96` (`HenselianLocalRing.exists_completeOrthogonalIdempotents_
forall_isLocalRing`, zero sorries) closes because `S` is a domain. **Consequence for chapter H:** the
forcing step is *not* irreducibly classical, and a future node could prove `(T1)`/`(T2)` rather than
assume them — but it would depend on one **not-yet-backported** instance, so this chapter keeps them as
hypotheses and books the route as **§16 item 9** (an ADD, not a defect). The same note records that
`AdjoinRoot g` is an *order*, not the integral closure — **which is exactly ERRATUM E3's point**
(honesty item H-5(3)), independently confirmed.

**ARITHMETIC AUDIT.** The forcing at the four instance data: `(e₁,f₁) = (2,1)`, `deg = 2`, divisibility
`2 ∣ p.1`, `1 ∣ p.2` with `p.1*p.2 ≤ 2` forces `p = (2,1)` ✓. `(1,2)`: `p.1*p.2 ≤ 2`, `2 ∣ p.2` forces
`p = (1,2)` ✓. `(3,1)`: `≤ 3`, `3 ∣ p.1` forces `(3,1)` ✓. `(1,3)`: forces `(1,3)` ✓. At the *block*
degree `2e₁f₁` the same argument gives the RAM row: `2e₁ ∣ p.1`, `f₁ ∣ p.2`, `p.1*p.2 ≤ 2e₁f₁` forces
`(2e₁, f₁)` ✓ — **H.74's degree consistency plus this node is the whole content of the RAM and INERT
rows**, and the 2SIDED row is the two-factor case (`(typeOf g).data` of size 2), which the caller
handles by applying this node to each factor.

**TEETH.** `GN-SIGMA` / `GH-SIGMA` (mechanism-free PARI oracles, 37,792/0 and 6,185/0) →
**Lean theorem** for the forcing step.

**ENVIRONMENT.** ENV-H2 (no completeness needed).

---

### NODE H.77 [lemma] [fresh]

**STATEMENT.** *The stage-RAM value-group repair (`passPE1 F4`).* For `e₁ ≥ 1` and `u` odd, write
`g := Nat.gcd u e₁`. Then `g` is odd, and `Nat.lcm e₁ (2 * e₁ / g) = 2 * e₁`. (So `(T1)` together
with `v(Y) = u/(2e₁)` forces `2e₁ ∣ e(L)`, whereas `v(Y)` **alone** gives only `2e₁/g ∣ e(L)`.)

**SIGNATURE.**
```lean
namespace Uniformity.Density.Induction

theorem gcd_odd_of_odd {u e : ℕ} (hu : Odd u) : Odd (Nat.gcd u e)

theorem lcm_ram_value_group {u e : ℕ} (he : 1 ≤ e) (hu : Odd u) :
    Nat.lcm e (2 * e / Nat.gcd u e) = 2 * e
```

**DEPENDS.** none · mathlib `Nat.gcd_dvd_right`, `Nat.Coprime`, `Nat.lcm`, `Nat.odd_iff`.

**PROOF.**
1. `gcd_odd_of_odd`: `Nat.gcd u e ∣ u` and `u` odd, so the gcd is odd (a divisor of an odd number is
   odd — `Nat.Odd.of_dvd` / `Nat.odd_iff` + `Nat.two_dvd_ne_zero`).
2. `lcm_ram_value_group`: write `e = g * m` where `g := gcd u e` (`Nat.gcd_dvd_right`), so
   `2*e/g = 2*m`. Then `lcm (g*m) (2*m) = m * lcm g 2 = m * (2*g) = 2*e`, using
   `Nat.Coprime g 2` (from `g` odd) so `lcm g 2 = 2*g`, and `Nat.lcm_mul_left`-style factoring.

**SIZE.** 18 lines. The `lcm` factoring is the whole cost; `Nat.Coprime.lcm_eq_mul` plus
`Nat.lcm_mul_left` are the two lemmas.

**SOURCE.** `EFF.GENHN.38`'s `[r2 2026-08-09]` repair, verbatim: *"WITH (T1) — `v(Y)` alone gives only
`(2e₁/gcd(u, e₁)) | e(L)` when `gcd(u, e₁) > 1` (e.g. `e₁ = 3, u = 9`: `2 | e` only); `gcd(u, e₁)` is
odd (`u` odd), so `lcm(e₁, 2e₁/gcd(u, e₁)) = 2e₁` — the value-group argument needs both facts.
passPE1 F4"*, with the spec's own audit checking `e₁ ∈ {2, 3, 6}` and closing *"**The repair is correct
at general `e₁`, and its proof needs exactly the oddness of `g`, which follows from the oddness of
`u`.**"*

**ARITHMETIC AUDIT (recomputed fresh, at the spec's three cells and one more).**
`e₁ = 3, u = 9`: `g = 3` odd ✓; `2e₁/g = 2`; `lcm(3,2) = 6 = 2e₁` ✓.
`e₁ = 2, u = 1`: `g = 1`; `2e₁/g = 4`; `lcm(2,4) = 4 = 2e₁` ✓.
`e₁ = 6, u = 9`: `g = 3`; `2e₁/g = 4`; `lcm(6,4) = 12 = 2e₁` ✓ — **the `e₁` even case, which the
spec's own general argument needed** (`e₁ = g·m` with `g` odd puts all of `2` into `m`).
`e₁ = 9, u = 15`: `g = 3`; `2e₁/g = 6`; `lcm(9,6) = 18 = 2e₁` ✓.
**The bare `v(Y)` bound is genuinely weaker**: at `(e₁,u) = (3,9)` it gives only `2 ∣ e`, so a proof
using `v(Y)` alone would conclude `e ≥ 2` where `6` is needed ✓ — the defect `F4` names.

**TEETH.** `GN-SIGMA`'s E31 rows (`{(6,1)}/{(3,1)²}/{(3,2)}` at **wild `p = 3`, `e₁ = 3`** — *"which
is exactly the `gcd(u, e₁) > 1` geography the `[r2]` repair is about"*, `EFF.GENHN.38`'s TEETH) ·
`GN-T-SIG` (fired 2/2) → **Lean theorem**.

**ENVIRONMENT.** ENV-H1.

---

### NODE H.78 [def] [fresh]

**STATEMENT.** *The composed (tower) dictionary.* For an outer genre datum `G` and inner data
`(e₂, f₂)`, define `composedSigma G e₂ f₂ : StageLeaf → FactorizationType` by
`ram ↦ ⟨{(2*e₁*e₂, f₁*f₂)}⟩`, `twoSided ↦ ⟨{(e₁*e₂, f₁*f₂), (e₁*e₂, f₁*f₂)}⟩`,
`inert ↦ ⟨{(e₁*e₂, 2*(f₁*f₂))}⟩` — `stageSigma` with `(e₁, f₁)` replaced by `(e₁e₂, f₁f₂)`.

**SIGNATURE.**
```lean
namespace Uniformity.Density.Induction

/-- `T(b)′`(iii)'s composed dictionary: the σ-composition FORMULA `(e, f) ↦ (e₁e₂·e_s, f₁f₂·f_s)` —
the part of the REFUTED `T(b)` that SURVIVES, applied to the composed-key pins. -/
def composedSigma (G : GenreDatum) (e₂ f₂ : ℕ) : StageLeaf → FactorizationType
  | .ram      => ⟨{(2 * (G.e₁ * e₂), G.f₁ * f₂)}⟩
  | .twoSided => ⟨{(G.e₁ * e₂, G.f₁ * f₂), (G.e₁ * e₂, G.f₁ * f₂)}⟩
  | .inert    => ⟨{(G.e₁ * e₂, 2 * (G.f₁ * f₂))}⟩
```

**DEPENDS.** H.01, H.73.

**PROOF.** definitional.

**SIZE.** 12 lines.

**SOURCE.** `EFF.GENHN.44` (`T(b)′` clause (iii), the composed dictionary verbatim:
*"`composed-RAM (p₀ odd on dv₂, p₀ ≤ 2p₁) ↦ {(2e₁e₂, f₁f₂)}`;
`composed-2SIDED/SPLITEQ/SPLTAIL ↦ {(e₁e₂, f₁f₂)} ×2`; `composed-INERT ↦ {(e₁e₂, 2f₁f₂)}` — the
σ-composition FORMULA `(e, f) ↦ (e₁e₂·e_s, f₁f₂·f_s)` of the sealed (b) SURVIVES, applied to the
composed pins; inner `μ₂ ≥ 3` is `[GENHN-HE(μ₂)]`"*); `EFF.GENHN.17` (the refutation of `T(b)`, and
what survives).

**⚠ THIS IS A DEFINITION, NOT A THEOREM, AND ITS PERIMETER IS THE FULL INNER SIDE.**
`EFF.GENHN.44`'s CONDITIONALITY: *"(iii)'s perimeter is the FULL inner side, and the `[r3]` round says
so after the `[r2]` rider over-covered … PARTIAL-side inner `μ₂ = 2` leaves (`e₂f₂μ₂ < μ₁`, first live
`n = 10`) ride `[GENHN-TOW-1]` item (4), not (iii)"*, with a **fired** machine counter-witness (the
`n = 10` PE2-P member over `ℚ₂`, whose σ *"no proved display prices"*). Chapter H defines the composed
dictionary and proves its degree consistency (H.79); it makes **no claim** about which leaves carry it.
**A node asserting `composedSigma` is the σ of any actual polynomial is out of chapter** — honesty item
H-5(2)/H-10.

**TEETH.** `genhnr2_supp.py`'s corrected-read-vs-PARI rows (*"corrected `{(4,2)}` exact on every
decided leaf; 3-stage `n = 16`: `{(16,1)}/{(8,1),(8,1)}` exact"*) → **executable regression** retained
for the σ values; **Lean theorem** at H.79 for the degree.

**ENVIRONMENT.** ENV-H1.

---

### NODE H.79 [lemma] [fresh]

**STATEMENT.** *The composed dictionary is degree-exhausting at the composed degree.* For every `G`,
`e₂`, `f₂` and every leaf `ℓ`: `(composedSigma G e₂ f₂ ℓ).degree = 2 * (G.keyDeg * (e₂ * f₂))`, i.e.
`= 2 * D₂` with `D₂ = D′ · e₂f₂ = e₁e₂ · f₁f₂`.

**SIGNATURE.**
```lean
namespace Uniformity.Density.Induction

theorem composedSigma_degree (G : GenreDatum) (e₂ f₂ : ℕ) (l : StageLeaf) :
    (composedSigma G e₂ f₂ l).degree = 2 * (G.keyDeg * (e₂ * f₂))

theorem composedDeg_eq (G : GenreDatum) (e₂ f₂ : ℕ) :
    G.keyDeg * (e₂ * f₂) = (G.e₁ * e₂) * (G.f₁ * f₂)
```

**DEPENDS.** H.01, H.02, H.78 · landed `FactorizationType.degree`.

**PROOF.**
1. `composedDeg_eq`: unfold `keyDeg`; `ring`.
2. `composedSigma_degree`: `cases l`; `simp [composedSigma, FactorizationType.degree]`; then `ring`
   using `composedDeg_eq` — `(2*(e₁e₂))*(f₁f₂) = 2*((e₁e₂)*(f₁f₂))` ✓,
   `(e₁e₂)*(f₁f₂) + (e₁e₂)*(f₁f₂) = 2*(…)` ✓, `(e₁e₂)*(2*(f₁f₂)) = 2*(…)` ✓.

**SIZE.** 10 lines.

**SOURCE.** `EFF.GENHN.44`'s own *arithmetic audit*, verbatim: *"Block degree at `μ₂ = 2` is
`2D₂ = 2e₁e₂f₁f₂`. RAM: `2e₁e₂ · f₁f₂ = 2D₂` ✓. 2SIDED: `2 × (e₁e₂ · f₁f₂) = 2D₂` ✓. INERT:
`e₁e₂ · 2f₁f₂ = 2D₂` ✓. All three exhaust the block ✓. Composition with S7's level-1 dictionary:
substituting `(e₁, f₁) ↦ (e₁e₂, f₁f₂)` into `.15`'s three rows reproduces this table exactly ✓ — i.e.
the dictionary really is S7's, re-based."*; `EFF.GENHN.42`(i) (`D₂ := D′e₂f₂`, and the forcing chain's
`e₁e₂ · f₁f₂ = D₂`).

**ARITHMETIC AUDIT (recomputed fresh, at the `n = 8` first-live tower and the `n = 16` 3-stage row).**
`n = 8`: `G = (2; 2,1,4; h)`? — the tower datum is `(e₁f₁, μ₁) = (2, 4)` with inner `(e₂f₂, μ₂) =
(2, 2)`, so `D′ = 2`, `e₂f₂ = 2`, `D₂ = 4`, and `2D₂ = 8 = n` ✓. `EFF.GENHN.47`'s table gives the three
PE1 members' true σ as `{(8,1)}` — degree `8` ✓, and the *refuted* stage-shadow readings `{(4,2)}` and
`{(4,1)²}` are **also** degree `8` ✓, *"which is exactly why only PARI could separate them"* (that
spec's audit). `n = 16` 3-stage: `{(16,1)}` and `{(8,1),(8,1)}` both degree `16` ✓.
**Degree consistency is necessary and NOT sufficient** — this node proves the necessary half and the
oracle supplies the rest; recording that asymmetry is the point of the audit.

**TEETH.** as H.78 → **Lean theorem** for the degree.

<!-- APPEND-POINT -->






