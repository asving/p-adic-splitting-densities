# UNIT TBT — VERDICT: THE TWO-BLOCK FACTORIZATION TRANSPORT LANDED AND PINNED —
master row 5 CLOSES at every singleton type (`LeafSectorLaw m ⟨{p}⟩`
UNCONDITIONAL), the leaf row of ALL THREE masters weakens to NON-SINGLETON σ,
and the general polygon-break type-card forcing lands as row 3's cell-side tool
(2026-08-31)

**Deliverable:** `leanfinal/Uniformity/ChapI/IFCG59.lean` (730 lines, ZERO sorries,
zero errors, zero warnings; 13 AxCheck footer lines).  **Axiom fence, exactly as
designed:** §0's bridge is pure Lean core `{propext, Classical.choice, Quot.sound}`;
EVERY other theorem (§§1–3 and the two census masters) is Lean core + EXACTLY the
owner-signed gate-(b) cite `Uniformity.Density.Leaf.exists_slope_factorization`
(B.42, inherited through IFCG26 §2 / IFCG35 / IFCG37 / the spines — never
re-consumed); the capstone master additionally inherits exactly
`Uniformity.Density.Tower.agnprw_termination` (ID12's, previously declared).  The
C.33 cites and `AX_cellRecursion` do NOT occur.  **ZERO new definitions** — the unit
adds only theorems; the trust boundary is unchanged.  Verification: per-increment
`timeout 580 lake env lean Uniformity/ChapI/IFCG59.lean` (5 increments; final run:
exactly the 13 expected axiom prints, nothing else); targeted
`lake build Uniformity.ChapI.IFCG59` GREEN (9035 jobs); aggregator
`lake env lean Uniformity/ChapI.lean` GREEN with the IFCG59 line appended after
IFCG58's (the one sanctioned touch).  NO git operations.

## ★★★ THE HEADLINES

    theorem leafSectorLaw_singleton :               -- ★★★ ROW 5 AT SINGLETON σ: CLOSED
      0 < m → LeafSectorLaw m ⟨{p}⟩                 -- UNCONDITIONAL, every pair p,
                                                    -- every positive mass
    theorem subface_two_block_transport :           -- ★★★ THE PINNED TRANSPORT
      (sub-face leaf cell, minimal face (h,e'), any lift a) →
      ∃ g R d, monicPoly a = g * R ∧ IsPure X g h e' ∧ 0 < d
        ∧ g.natDegree = e' * d ∧ e' * d < m
        ∧ typeOf g = ⟨{(e', d)}⟩                    -- the block's type, PINNED
        ∧ σ.data = (e', d) ::ₘ (typeOf R).data      -- the class type decomposes
    theorem card_ge_two_of_minFace_not_attained_zero :  -- ★★ ROW 3's CELL-SIDE TOOL
      (σ-decided stratum class, ANY level, ANY residual genre,
       minimal face NOT attained at 0) → 2 ≤ Multiset.card σ.data
    theorem decidedSliceAt_all_of_visCensus' / _of_MASTER'' / capstoneHypotheses_of_MASTER'' :
      -- ★★★ ALL THREE MASTERS RECOMPUTED: the leaf row's premise is now
      -- `LeafSubfaceLaw e σ` under the OLD guards PLUS `2 ≤ Multiset.card σ.data`

## The three charge items, disposition

**(1) THE TRANSPORT THEOREM — LANDED, in three grades.**
* §0 `npAttains_zero_of_onSide` (Lean-core): the abscissa-0 bridge — a lift on-side
  at `0` for a visible slope datum forces the CLASS attainment at `0` (the on-side
  equation pins the corner valuation strictly below the frame floor, so the windowed
  read is exact).  This is the converse transport of IFCG26 §1 at the one abscissa
  the sub-face carrier excludes, and it is what makes the rest factor NONTRIVIAL.
* §1 `two_block_split_of_not_attained_zero` (the core, residual-genre free, ANY
  level `K`): a σ-decided stratum class whose minimal face is not attained at `0`
  has EVERY lift factoring `monicPoly a = g · R`, `g` monic `(h,e')`-pure, `R`
  monic, both of positive degree, with `σ.data = (typeOf g).data + (typeOf R).data`.
  Mechanism: IFCG26 §2's packaged B.42 engine (`exists_pure_factor_of_two_point_side`
  — the `f(0) = 0` corner is handled inside it by the X-strip, so no good-lift
  choice was needed) + §0 (if `R` were trivial, `f` would be pure, hence on-side at
  `0`, hence class-attained at `0`) + CN-03's `typeOf_mul`.  The charge's
  "typeOf(g·h) relates to typeOf g + typeOf h" needed NO new additivity engine:
  `typeOf_mul` is landed corpus (CN-03); the unit's real content is the CLASS-level
  wiring — decidedness turns the per-lift additivity into a decomposition of σ.
* §3 `subface_two_block_transport` (THE PIN): on the LEAF sub-face carrier the
  block's type is pinned `⟨{(e', d)}⟩` exactly.  Mechanism: B.39a §7's general
  product laws (`sideMin/sideDeg_mul_gen`, `npHgt_mul_gen`, `resPoly_mul_gen`
  — SDL's finding that these exist at full generality paid off verbatim) identify
  the class residual (irreducible on the leaf sector, transported by IFCG35's
  `classResidualPoly_eq`) with `resPoly g · resPoly R`; irreducibility forces
  `resPoly R` to be a UNIT (the block's residual has degree `d > 0`), so the rest's
  side degree is 0 and the block carries the whole face; `ḡ = X̄^(e'·d)` by unique
  factorization in `κ[X]` (`dvd_prime_pow` + monic associates are equal); IFCG37's
  UNCONDITIONAL `residualLeafLaw_all` (RIS's supply) then reads off
  `typeOf g = ⟨{(e', d)}⟩`.  Corollary `face_block_mem_type`:
  `∃ d, 0 < d ∧ e'·d < m ∧ (e', d) ∈ σ.data` — the sub-face's block type is an
  ENTRY of the class type (the census consumer's form).

**THE QUANTITATIVE RESULTANT PIN (derived, recorded here — NOT machine-checked, and
not needed by any landed theorem):** for the split's two blocks the classical form
the charge asked for reads: all `g`-roots have valuation `h/e'` (the pure face),
all `R`-roots have valuations `> h/e'` (the steeper complementary faces), so every
root pair differs at valuation exactly `min = h/e'`, giving

    v(Res(g, R)) = Σ_{i,j} v(αᵢ − βⱼ) = deg g · deg R · (h/e')
                 = (e'·d) · (m − e'·d) · h/e'  =  h · d · (m − e'·d)  ∈ ℕ,

polygon-determined.  This is the depth at which the two factor classes are pinned by
the class of the product (SDL's refutation genre: level-exactness FAILS by exactly
`q^{v(Res)}`-sized fibers), i.e. the ladder constant of the future sub-face COUNT
unit.  Corpus support for a machine-checked version: mathlib's `Polynomial.resultant`
is too thin; the honest route is RCD's depth-graded pair-table tiling (sector-
agnostic per PCD), with `h·d·(m − e'·d)` as the predicted uniform depth.

**(2) THE CONSUMERS — fired or honestly reduced.**
* **(a) LSC's singleton-σ leaf laws: FIRED.**  §2 `leafSubSector_eq_empty_of_card_le_one`
  (each block contributes ≥ 1 type entry, so a sub-face cell forces
  `card σ.data ≥ 2`) ⟹ `leafSubfaceLaw_of_card_le_one` (the law holds outright,
  carrier empty at every level/DVR/uniformizer) ⟹ ★★★ `leafSectorLaw_singleton` via
  IFCG57's re-base (`leafSectorLaw_of_subface`; the spanning half is LSC's necklace
  census).  Exactly LSC's pointer: "type additivity along the two-block split forces
  |σ.data| ≥ 2 off the spanning locus."
* **(b) Row 2 (`EisFullSpanRemainderLaw`, composite m ≥ 6): the transport is
  VACUOUS on its carrier — no fire, honestly.**  `powerSectorFull` requires
  `e' · deg(classResidualPoly) = m`: the minimal face spans the whole polygon
  (single face, attained at 0), so there IS no polygon break to transport across.
  Row 2's content is the `h ≥ 2` frames / `deg ψ ≥ 2` residual root fields — the
  fractional-recentring tower territory (C136), confirming PCD's honest-scope note
  for `PowerFullSpanLaw`.  Recorded; nothing weakened, nothing claimed.
* **(c) Row 3 (`VisCensusLaw` — the cell-side block decomposition): REDUCED by a
  general tool, not fired.**  The visible split/power cells are SAME-FACE
  coprime-residual territory (XHS §2's class split genre), not disjoint-slope
  territory, so the transport does not fire the census.  What TBT contributes is the
  residual-genre-FREE core (§1 deliberately consumes no irreducibility) and its
  corollaries `card_ge_two_of_minFace_not_attained_zero` /
  `minFace_attains_zero_of_card_le_one` (a decided stratum class at singleton type
  has FULL-SPAN minimal face): the cell-side description's type-support constraint,
  at every level and every genre.  The exact remaining row-3 content is unchanged:
  the depth-graded fiber law (see the resultant pin above).

**(3) THE MASTER — RECOMPUTED on all three spines.**  The leaf row's premise
weakens from `LeafSubfaceLaw e σ` (IFCG57) to `LeafSubfaceLaw e σ` under the same
guards PLUS `2 ≤ Multiset.card σ.data` (the singleton case is §2's unconditional
fire; the wrapper `leafSectorLaw_of_nonsingleton_subface` routes both):
* `decidedSliceAt_all_of_visCensus'` — PCD's newest spine: {`∀ g, VisCensusLaw g`,
  `PowerFullSpanLaw`, **`LeafSubfaceLaw` at non-singleton σ**, R4};
* `decidedSliceAt_all_of_MASTER''` — LSC's FC/Eis spine: {`FactorCorrespondenceAt`,
  `EisFullSpanRemainderLaw`, `SplitConvolutionDefectLaw`,
  `PowerConvolutionDefectLaw`, **`LeafSubfaceLaw` at non-singleton σ**};
* `capstoneHypotheses_of_MASTER''` — the capstone form (ladder/deepTwist + the five,
  ID12's honesty frame verbatim; + `agnprw_termination` in the footprint).
Future scoreboards should read row 5 as: **`LeafSubfaceLaw e σ`, `e ≥ 5`, guarded,
AND `2 ≤ |σ.data|`** — strictly smaller than LSC's row 5 (which was already strictly
smaller than IFCG55's).

## The surviving master premise list (LSC-spine numbering, after TBT)

| # | premise | status after TBT |
|---|---|---|
| 1 | `FactorCorrespondenceAt D`, `D ≥ 2` | unchanged (THE STAGED CITE, owner gate) |
| 2 | `EisFullSpanRemainderLaw m σ`, composite `m ≥ 6`, guarded | unchanged (transport provably vacuous on this carrier — single-face genre) |
| 3 | `SplitConvolutionDefectLaw e σ`, `e ≥ 5`, guarded | unchanged as a Prop (= `VisCensusLaw .split` via PCD); TBT adds the type-card forcing to its cell-side toolkit |
| 4 | `PowerConvolutionDefectLaw e σ`, `e ≥ 5`, guarded | unchanged (= `VisCensusLaw .power` via PCD) |
| 5 | `LeafSubfaceLaw e σ`, `e ≥ 5`, guarded | **SHRUNK: non-singleton σ only** (`2 ≤ |σ.data|`); singleton types CLOSED unconditionally (this file) |

## Discharge pointers (for the successor units)

* **The sub-face COUNT (the remaining row-5 content, non-singleton σ):** §3 pins the
  image data exactly — the cell determines `(h, e', d)` and forces
  `σ.data = (e',d) ::ₘ τ.data` with `τ.degree = m − e'·d`; the count couples the
  face digit box at `(h, e', d)` (LSC's `wLeaf` engine, general-purpose per its
  pointer) to the mass-`(m − e'·d)` decided cells at type `τ` (all polygon slopes
  `> h/e'`), through fibers of the predicted uniform depth `h·d·(m − e'·d)`
  (the resultant pin above).  RCD's tiling toolkit is sector-agnostic and should
  consume this depth as its ladder constant.
* **Decidedness transport (the E2L direction, still open):** the converse
  correspondence — pair of decided blocks ⟹ decided product class at the
  depth-dropped level — is NOT in this unit; §1 goes lift-by-lift THROUGH the
  product class's own decidedness.  The named missing piece for rows 2/3 remains
  the finite-precision factorization congruence at controlled depth (IFCG16 §6/XHS
  §3's genre is landed ONLY at residually-coprime cofactors; at disjoint slopes both
  blocks reduce to powers of X̄, so that engine does not apply — the depth-graded
  version is genuinely new mathematics).
* `minFace_attains_zero_of_card_le_one` gives every future census unit the free
  dichotomy: at singleton σ, ALL decided stratum cells are full-span — so
  singleton-σ censuses never meet sub-face strata in ANY sector.

## New definitions (trust boundary)

**NONE.**  Every named object consumed (`leafSubSector`, `LeafSubfaceLaw`,
`LeafSectorLaw`, `MinFaceAt`, `classResidualPoly`, the masters' premise Props) is
landed corpus, byte-untouched.  The unit adds 13 theorems and 0 definitions.

## File map (`leanfinal/Uniformity/ChapI/IFCG59.lean`, 730 lines)

§0 kit: `isKey_X` (private copy), `mem_sideSet_iff'` (private, B83Kit idiom),
`npHgt_monic_top` (private), `suppVal_ne_top_of_monic` (private),
★ `npAttains_zero_of_onSide` (THE BRIDGE), `typeOf_data_ne_zero` (private) ·
§1 ★★ `two_block_split_of_not_attained_zero` (THE CORE),
★★ `subface_two_block_split` (the leaf instance),
★★ `card_ge_two_of_minFace_not_attained_zero`,
★ `minFace_attains_zero_of_card_le_one` ·
§2 ★★ `leafSubSector_eq_empty_of_card_le_one`, ★★ `leafSubfaceLaw_of_card_le_one`,
★★★ `leafSectorLaw_singleton` ·
§3 `resPoly_congr`/`sideMin_congr` (private), ★★★ `subface_two_block_transport`,
★ `face_block_mem_type` ·
§4 `leafSectorLaw_of_nonsingleton_subface` (private),
★★★ `decidedSliceAt_all_of_visCensus'`, ★★★ `decidedSliceAt_all_of_MASTER''`,
★★★ `capstoneHypotheses_of_MASTER''` · AxCheck footer (13 lines).
Imports: Mathlib + IFCG57 + IFCG58 (everything else transitive).  Aggregator: one
import line appended to `Uniformity/ChapI.lean` after IFCG58's (the one sanctioned
touch).

## Repair log (3 error rounds total; every theorem landed as designed — no mathematical failures)

1. `subst` direction trap: `minFaceAt_unique hF₃ hF : h₃ = h` eliminates the
   THEOREM-BOUND `h` (subst kills the RHS variable), orphaning later references —
   swap to `minFaceAt_unique hF hF₃` so the ∃-bound copies die instead.
2. `Associated` is a `def` unfolding to `Exists`, so dot-notation `.symm` on an
   ascribed anonymous constructor resolves to (nonexistent) `Exists.symm` — name the
   `have` with an explicit `Associated` type first, then `Associated.symm` applies.
   Also `Polynomial.monic_X_pow` takes its exponent explicitly.
3. `rwa` orientation: after `Monic.natDegree_map` + `natDegree_X_pow` the hypothesis
   lands as `g.natDegree = k` against goal `k = g.natDegree` — explicit `.symm`.

Traps avoided by design (LSC/E2L/CN4 logs consulted): the ENTIRE file sits in
`{O : Type}` sections (IFCG37's `residualLeafLaw_all` and the sector laws are
`O : Type`-quantified; the E2L/LSC whnf-timeout trap never fired); no `Σ`-named
`have`s; no omega on raw products (the one `e'·d`-vs-`m` comparison goes through a
product-form `have` + linear omega); dependent-proof-argument rewriting handled by
`subst`-based congruence helpers (`resPoly_congr`, `sideMin_congr`) instead of
rewriting under `Finset.Nonempty` binders.

## Cross-checks

* The singleton fire is consistent with LSC's spanning shape theorem: `leafSpan_shape`
  forces spanning cells to singleton σ; TBT's `minFace_attains_zero_of_card_le_one`
  is its exact complement (singleton σ forces spanning), closing the dichotomy.
* At `(m, σ) = (5, ⟨{(4,1),(1,1)}⟩)`: LSC's hand-checked non-spanning witness
  (heights `(2,1,1,1,1)`, face `[1,5]` of slope `1/4`) has `card σ.data = 2` — the
  masters' surviving premise still covers it, as it must (the witness shows the
  non-singleton remainder is NONEMPTY, so no stronger emptiness is available; the
  fire is exactly sharp).
* §3's pin at that witness: block `(e', d) = (4, 1)`, `deg g = 4`, rest degree `1`,
  `σ.data = (4,1) ::ₘ {(1,1)}` ✓ matches LSC's recorded lift type `{(1,1),(4,1)}`.
