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

<!-- APPEND-POINT -->

