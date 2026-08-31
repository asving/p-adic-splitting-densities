# UNIT LSC — VERDICT: THE GENERAL DIGIT BRIDGE + THE NECKLACE CENSUS OF THE
SPANNING LEAF CELLS LANDED (ALL LEAN-CORE) — master row 5 SHRINKS to the named
sub-face remainder `LeafSubfaceLaw`; the literal "fire via face boxes alone" is
REFUTED by a concrete non-spanning witness (2026-08-31)

**Deliverable:** `leanfinal/Uniformity/ChapI/IFCG57.lean` (1374 lines, ZERO sorries,
zero errors, ZERO warnings; 23 AxCheck footer lines).  **Axiom fence, BETTER than
designed:** the ENTIRE new mathematics — §0 kit, §1 digit polynomial, §2 ★★ THE
BRIDGE, §3 ★★ the necklace count, §4 the partition + the shape theorem + the
box-bank identity + the spanning count, §5 the spanning `ZcURLim` law + the re-base
— is **pure Lean core** `{propext, Classical.choice, Quot.sound}` (21 of 23 footer
lines; the B.42 cite does NOT enter any new theorem).  Exactly two wrappers inherit
cites from landed compositions: `decidedSliceAt_all_of_MASTER'` (Lean core + the
owner-signed gate-(b) `Uniformity.Density.Leaf.exists_slope_factorization`,
inherited through IFCG55's master — never re-consumed) and
`capstoneHypotheses_of_MASTER'` (+ the previously-declared allowlisted
`agnprw_termination`, ID12's).  The C.33 cites do NOT occur; zero `sorryAx` on the
full aggregator dump.  Verification: per-increment
`timeout 580 lake env lean Uniformity/ChapI/IFCG57.lean` (6 increments, each GREEN;
final: exactly the 23 expected axiom prints); targeted
`lake build Uniformity.ChapI.IFCG57` GREEN (9032 jobs); aggregator
`lake env lean Uniformity/ChapI.lean` GREEN with the IFCG57 line appended after
IFCG56's (the one sanctioned touch; IFCG56.lean itself untouched).  NO git
operations.

## ★★★ THE HEADLINES

    theorem classResidualPoly_eq_leafResPoly :      -- ★★ THE GENERAL DIGIT BRIDGE
      (spanning height cone, exact corner v₀ = h·d, h < e' coprime, m = e'·d ≤ K) →
      classResidualPoly π c h e'
        = (leafResPoly π h e' d c).map (resFieldXEquiv O)     -- LEAN CORE
    theorem card_leafIrrBox :                       -- ★★ THE NECKLACE COUNT
      #(leafIrrBox π m K h e' d) = N_d(q) · q^(mK − wLeaf h e' d)   -- LEAN CORE,
      -- N_d(q) := Nat.card (IrredOfDeg (ResidueField O) d), EXACT at every level
    theorem zcURLim_leafSpanFam :                   -- ★★★ THE SPANNING LAW, ∀ (m,σ),
      0 < m → ZcURLim (leafSpanCount/q^(m(M+m)))    -- UNCONDITIONAL, LEAN CORE
      -- value Σ_{h ∈ faceH e'} N_d(q)/q^(wLeaf h e' d) at σ = ⟨{(e',d)}⟩ (e'd = m,
      -- d ≥ 2); 0 at every other σ
    theorem leafSectorLaw_of_subface :              -- ★★★ THE RE-BASE
      0 < m → LeafSubfaceLaw m σ → LeafSectorLaw m σ          -- LEAN CORE
    theorem decidedSliceAt_all_of_MASTER' :         -- ★★★ ROW 5 RECOMPUTED
      hFC → hEis → hSD → hPD → (guards → LeafSubfaceLaw e σ) → ∀ n, DecidedSliceAt n

## The three charge items, disposition

**(1) THE GENERAL DIGIT BRIDGE — DONE, Lean-core, first-attempt.**  At arbitrary
face data `(h, e', d)` (h < e' coprime, m = e'·d): the residual positions are
`i = e'·k` at levels `h·(d−k)`; `leafResPoly π h e' d c` is the monic degree-`d`
polynomial over `ResidueField O` with those `resDig` class digits as coefficients
(IFCG36's instrument at general parameters, junk-tolerant total read `resAt`).  The
bridge composes IFCG35's `classResidualPoly_eq` (the canonical residual = every
lift's side residual), IFCG28's class-pinned side data (`sideSet/sideMin/sideMax
_monicPoly_eq` — the spanning face has `sideMin = 0`, `sideMax = m`, `sideDeg = d`),
IFCG37's `resPoly_x_frame` (the x-frame digit reading, already general in `(u, ℓ)`),
and IFCG36's `resDig_mk` — NO new residual theory was needed; DBL's `(1,2,2)`
mechanism generalized by composition exactly as the charge predicted.  Corollary
`irreducible_classResidualPoly_iff`: the genre transports through
`Polynomial.mapEquiv (resFieldXEquiv O)`.

**(2) THE COUNT — the spanning half CLOSED exactly; the literal full fire is
mathematically unavailable.**
* `card_leafIrrBox`: the box at `(h,e',d)` = height cone (`e'·v_i ≥ h(m−i)`) +
  irreducible digit polynomial; counted by fibering DIRECTLY over the polynomial
  (`leafFiber`; genre Finset = `IrredOfDeg` as a set, no reconstruction equiv
  needed for the count): `N_d(q) · q^(mK − wLeaf h e' d)` with the K-independent
  weight `wLeaf h e' d = Σ_{i<m} (⌈h(m−i)/e'⌉ + [e' ∣ i])`.
  **Cross-checks against DBL's landed mass-4 unit (decorrelated):**
  `wLeaf 1 2 2 = 8` and the count `N₂(q)·q^(4K−8)` = `card_e1IrrBox_necklace`
  verbatim; the fiber thresholds at `(1,2,2)` are `(2,2,1,1)` with digit pins at
  positions 0, 2 = DBL's `e1Fiber` exactly; the law value at `σ = type22` is
  `N₂(q)/q⁸` = `zcURLim_e1IrrFam`'s pair.
* ★★ `leafSpan_shape` (the workhorse, Lean-core): EVERY spanning leaf cell forces
  `σ = ⟨{(e',d)}⟩`, `e'·d = m`, `d ≥ 2`, and box membership — mechanism: the corner
  attainment + coprimality force `e' ∣ m`; `d = 1` would put the cell in CN4's
  pure-face box (outside the carrier); RIS's `decidedAt_of_spanning_irr` (consumed
  at general `(e', d)` — its first post-RIS consumer) + `decidedAt_unique` pin σ.
* ★★ `leafSpanSector_eq_biUnion` / `leafSpanSector_eq_empty` /
  `card_leafSpanSector`: the spanning half IS the disjoint box bank
  `⋃_{h ∈ faceH e'}` at the matching singleton type and EMPTY at every other σ —
  count `Σ_h N_d(q)·q^(m(M+m) − wLeaf h e' d)`, exact at every level.
* ★★★ `zcURLim_leafSpanFam`: `ZcURLim` at EVERY `(m, σ)`, unconditional (constant
  families; pairs `(necklacePoly d, X^(wLeaf h e' d))` summed over `faceH e'`).
* **WHY NOT THE FULL FIRE (the honest refutation):** the leaf sector is NOT
  exhausted by face boxes.  Non-spanning leaf cells are real — witness (checked by
  hand against every definition consumed, NOT machine-checked: its decidedness
  needs exactly the missing transport below): `m = 5`, heights `(2,1,1,1,1)` —
  polygon `(0,2)–(1,1)–(5,0)`, minimal face `[1,5]` of slope `1/4` with LINEAR
  (hence irreducible) class residual, all lifts of type `{(1,1),(4,1)}` — a
  witnessed ramified σ of degree `5`, in the carrier, in the leaf sector, NOT
  spanning.  Its count couples the face digit box to the sub-face rest (the
  mass-`m − e'd` classes above the face line, at the complementary type) through a
  class-level two-block Hensel factorization correspondence that is NOT in the
  corpus — the SAME missing leg IFCG38 recorded for the split sector
  ("finite-precision Newton-polygon factorization-uniqueness") and E2L flagged as a
  full unit ("decidedness transport across the two-block factorization").  Nothing
  weakened: `LeafSectorLaw`'s statement is IFCG35's, byte-untouched; the partition
  `leafSectorCount = leafSpanCount + leafSubCount` is EXACT at every level
  (`leafSectorCount_eq_span_add_sub`, Lean-core, via `minFaceAt_unique`).

**(3) THE MASTER'S SURVIVING LIST, RECOMPUTED** (`decidedSliceAt_all_of_MASTER'`,
`capstoneHypotheses_of_MASTER'` — IFCG55's masters with row 5 re-based):

| # | premise | status after LSC |
|---|---|---|
| 1 | `FactorCorrespondenceAt D`, `D ≥ 2` | unchanged (THE STAGED CITE, owner gate) |
| 2 | `EisFullSpanRemainderLaw m σ`, composite `m ≥ 6`, guarded | unchanged (ASM) |
| 3 | `SplitConvolutionDefectLaw e σ`, `e ≥ 5`, guarded | unchanged (IFCG38) |
| 4 | `PowerConvolutionDefectLaw e σ`, `e ≥ 5`, guarded | unchanged (IFCG44) |
| 5 | ~~`LeafSectorLaw e σ`~~ → **`LeafSubfaceLaw e σ`**, same guards | **STRICTLY SMALLER**: the spanning necklace census is machine-checked out of the premise; only the NON-spanning (sub-face convolution) count remains |

`LeafSubfaceLaw m σ := ZcURLim (leafSubCount/q^(m(M+m)))` — the ONE new named Prop;
its carrier `leafSubSector` (minimal face irreducible-residual, NOT attained at 0)
is definitionally the exact complement of the closed half.

## Discharge pointers (for the successor unit)

* The sub-face cell factors (at the LIFT level, B.42's `exists_slope_factorization`
  / IFCG30's refinement) as (h,e')-pure block of degree `e'·d` (type pinned
  `(e', d)` by RIS Step I + descent) × rest of degree `m − e'·d` with all slopes
  `> h/e'` — so `LeafSubfaceLaw` is the leaf instance of the SAME two-block
  class-correspondence that would also close IFCG38's split defect (row 3) and the
  Eis remainder's sub-face part: ONE transport unit (E2L's "IFCG51-W1/W2-scale"
  estimate) likely serves rows 2, 3, and 5 simultaneously.  For the leaf instance
  the image characterization is CLEAN (the two factors live at disjoint slope
  ranges — no residual-coprimality analysis needed), so it is the easiest of the
  three to fire first.
* At singleton σ the sub-face part is (mathematically) EMPTY — type additivity
  along the two-block split forces `|σ.data| ≥ 2` off the spanning locus.  Landing
  just THAT (typeOf additivity across the polygon break) would fire
  `LeafSectorLaw m ⟨{(e',d)}⟩` outright for all singleton types.
* `wLeaf`, `tLeaf`, `leafFiber`, and the direct-over-the-polynomial fiber engine
  are general-purpose: any future genre box at arbitrary `(h, e', d)` (e.g. the
  Eis `deg ψ ≥ 2` residual boxes of row 2) can consume them verbatim.

## New definitions (trust boundary — flag for review)

`tLeaf`/`wLeaf` (threshold + weight) · `resAt` (total junk-0 coordinate read) ·
`leafDig`/`leafResPoly` (the digit polynomial) · `leafCone`/`leafIrrBox` (the
boxes) · `leafFiber` (counting fibers) · `leafGenre` (IrredOfDeg as a set) ·
`leafSpanSector`/`leafSubSector` (+ counts; the partition of IFCG35's `leafSector`
by `NPAttains … 0` on the unique minimal face) · **`LeafSubfaceLaw`** (THE new
named premise).  All consumed statements (`LeafSectorLaw`, `leafSector`,
`remainderCarrier`, the IFCG55 masters) byte-untouched.

## File map (`leanfinal/Uniformity/ChapI/IFCG57.lean`, 1374 lines)

§0 `tLeaf`, `tLeaf_le_iff`, `tLeaf_mul`, `tLeaf_le_corner`, `wLeaf` ·
§1 `resAt`, `leafDig`, `leafResPoly` + coeff kit (`_coeff_lt/_top/_gt`,
`_natDegree`, `_monic`, ★ `leafResPoly_eq_iff`,
`coeff_zero_ne_zero_of_irreducible`) · §2 `leafCone`, `leafIrrBox`,
`mem_classSideSet_iff` (B83Kit idiom, private), ★ `leafCone_face_data`,
★★ `classResidualPoly_eq_leafResPoly`, ★ `irreducible_classResidualPoly_iff` ·
§3 fiber-engine replays (private), `leafFiber`, `mem_leafFiber_iff`,
★ `card_leafFiber`, `leafGenre`, `finite_leafGenre`, ★★ `card_leafIrrBox`,
★ `leafIrrBox_corner` · §4 `leafSpanSector`/`leafSubSector` (+ counts),
`leafSector_eq_span_union_sub`, `leafSpan_disjoint_sub`,
★ `leafSectorCount_eq_span_add_sub`; [`{O : Type}` fence:] ★★ `leafSpan_shape`,
`mem_faceH_iff` (private), ★★ `leafSpanSector_eq_biUnion`,
★ `leafSpanSector_eq_empty`, `ncard_biUnion_eq` (IFCG53 replay, private),
`leafIrrBox_disjoint`, ★★ `card_leafSpanSector` · §5 `wLeaf_le_sq`,
★ `zcURLim_necklace_monomial`, ★★★ `zcURLim_leafSpanFam`, ★★★ `LeafSubfaceLaw`,
★★★ `leafSectorLaw_of_subface` · §6 ★★★ `decidedSliceAt_all_of_MASTER'`,
★★★ `capstoneHypotheses_of_MASTER'` · AxCheck footer (23 lines).
Imports: Mathlib + IFCG55 (everything else transitive).  Aggregator: one import
line appended to `Uniformity/ChapI.lean` after IFCG56's.

## Repair log (5 error rounds over 6 increments; every theorem landed as designed — no mathematical failures)

1. `Polynomial.finset_sum_coeff` deprecated → `finsetSum_coeff`.
2. THE CN4-LOGGED `Σ`-IDENTIFIER TRAP, re-confirmed: `have hΣ :` is a parse error
   that TRUNCATES the proof and reports as metavariable garbage at the `by` line —
   rename to `hSum`.  (Third corpus contact; the log entry saved the diagnosis.)
3. omega atom mismatch: `Nat.succ_le_of_lt hkd` produces `e' * k.succ` — a
   DIFFERENT nonlinear atom from `e' * (k + 1)`; supply `(show k + 1 ≤ d by omega)`
   instead.
4. Two `omega`s after `congr 1`+`rw` fired on already-closed goals (`Nat.add_zero`
   is defeq; `rw` closes rfl goals) — "No goals to be solved"; deleted.
5. THE `{O : Type}` UNIVERSE FENCE (E2L's log, re-confirmed at whnf-timeout
   severity): applying RIS's `decidedAt_of_spanning_irr` (stated at `O : Type`)
   from a `Type*` section makes unification grind through `Coeff` unfoldings to a
   deterministic heartbeat timeout — NOT a type error.  Moved the consuming
   theorems into a `{O : Type}` section.  Also: `subst hd` on `m = e'` eliminated
   `e'` (not `m`), orphaning later references — replaced by explicit rewriting.

Traps avoided by design (RECUR/RIS/DBL/E2L/CN4 logs consulted): all
variable-product arithmetic via explicit `Nat.mul_le_mul` + product-form `have`s +
omega on linear atoms (never omega on raw products); `npHeight_coe`/`hbox` values
re-typed by defeq `have`-ascription before omega; the Classical `classSideSet`/
`faceH` filters entered only through B83Kit-idiom private lemmas; ℕ-subtraction
products handled by the `A + B = C` cancellation idiom; the exponent bookkeeping
via the CN4 `sub_add_cancel`-sum idiom (no nested pow rewrites); `field_simp`
endgames with no trailing `ring` (DBL trap #5 anticipated — hit once anyway,
deleted).

## Consumption note for the census scoreboard

IFCG55's §4 master remains the canonical statement; `decidedSliceAt_all_of_MASTER'`
strictly subsumes it on row 5 (any `hLeaf` supplier also supplies `hLeafSub`
trivially?  NO — conversely: `hLeafSub` is WEAKER content, `MASTER'` is the
STRONGER theorem).  Future scoreboards should list row 5 as `LeafSubfaceLaw e σ`
(this file) and read IFCG55's row 5 as superseded.
