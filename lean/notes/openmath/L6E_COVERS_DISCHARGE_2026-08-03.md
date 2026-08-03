# L6E_COVERS_DISCHARGE_2026-08-03 — the II-M9 coverage sorry PROVED (wave-18 U6, recovery unit)

**Unit:** wave-18 U6 (synthesis-8 queue item "L6e_covers re-point"), recovery
completion of the 529-killed predecessor whose mid-work was checkpointed AS-IS
at d0e2b74 (`lean/LeanUrat/Scaffold/O12/scratch_hullcovers.lean`, 90 lines).

**VERDICT: DISCHARGED.** `LeanUrat.Scaffold.L6e_covers`
(`lean/LeanUrat/Scaffold/O12/Semantic.lean`) is proved, sorry-free, Lean-core
footprint, STATEMENT BYTE-UNCHANGED (docstring + full signature through
`:= by` diff-verified identical against HEAD; only the in-body BLOCKED comment
and the `sorry` were replaced). `L6e_partition` (L6e(i)) is therefore now a
full unconditional theorem; II-M9 consumes no `SemanticRows` row and no axiom
beyond Lean core.

## Predecessor-orphan audit (idempotency)

The d0e2b74 scratch was structurally complete AND compiling as far as it went
(§1 chord-pair helpers only: `dropQ`, `faceOf`, `numOf`, `numOf_val`,
`numOf_div_den`, `two_le_den`, `zip_width_sum`; no half-written blocks). All
seven helpers were kept verbatim as §1 of the new construction (only the
deprecated `push_neg` in `two_le_den` normalized to `push Not`, and the
top-level `variable {e : ℕ}` line dropped as unused). Nothing was
double-applied: the predecessor had not touched `Semantic.lean`.

## What was proved (unit II-M9c, the `L6eHull` section)

For `w : ℕ → WithTop ℤ` with `hCe : ∀ c < e, 1 ≤ w c`,
`hRe : ¬ ∀ c < e, ↑↑(e − c) ≤ w c`, `h0 : w 0 ≠ ⊤`:
`∃ κ s, CellMem κ s w` (`L6eHull.exists_cell`). Construction, bottom-up:

1. **§2 the diagram** — `htv` (the ℕ height, `untopD`-junked at ⊤; faithful on
   C_e columns by `coe_htv`/`htv_pos`), `diagram w e` =
   {(c, htv c) : c < e, w c ≠ ⊤} ∪ {(e, 0)} with the membership
   characterization and the C_e height bound `diagram_one_le_snd`.
2. **§3 vertex list + pins** — `VL` := `OM/NewtonPolygon.npVertices` of the
   diagram; head pin `(0, htv 0)` (`sorted_head_min` on `hullAbscissae` +
   `mem_hullAbscissae_min` + `dropCollinear_cons_head`), last pin `(e, 0)`
   (`mem_hullAbscissae_max` + `sorted_getLast?_eq` + `dropCollinear_getLast?`),
   `npHeight = 0` at the anchor, `2 ≤ VL.length`.
3. **§4 slope laws** — `ZL_get`/`mem_ZL` (getElem access to consecutive
   pairs); STRICT adjacent slope increase `adj_slope_lt` =
   `hull_slope_mono` (convexity ≤) + the survivor-corner law
   `dropCollinear_corner` via `collinear₃_of_pairSlope_eq` (≠); the chain
   `slope_lt_of_lt`; ALL slopes negative (`slope_neg`: the terminal chord
   drops from height ≥ 1 to the anchor 0, everything left is steeper); hence
   `drop_pos` and the strict drop descent `drop_lt_of_lt`; the TERMINAL drop
   `< 1` (`drop_last_lt_one`): the R_e-failing column's dot lies strictly
   below the slope-1 line and the terminal chord is a VALID line
   (`vert_zip_valid` + `pairLine_le_of_valid`), so dropQ·(e−c*) ≤ htv c* <
   e−c*; denominators divide widths (`den_dvd_width` via `Rat.den_dvd` on the
   integer chord drop).
4. **§5 face data** — `facesL` := widths + reduced-drop denominators off
   `ZL`; `hsum` by the predecessor's `zip_width_sum` telescoping (head 0,
   last e); `hdvd` from §4; `hlast` (b_k ≥ 2) = `two_le_den` on
   0 < dropQ_last < 1; `theKappa : FaceKind e`; `theS : SlopeTuple theKappa`
   with numerators `numOf`, `hcop` from `Rat.reduced`, `hdesc` = drop
   descent, `hlt1` = the terminal-drop bound.
5. **§6 height matching** — the abscissa pin `kappa_x : theKappa.x j = VL[j].1`
   (induction via `x_succ_of_lt` + widths) and THE transfer
   `heights_eq : heights theKappa theS c = npHeight (diagram) ↑c` for c ≤ e,
   by downward induction from the anchor: per-column drops agree
   (`heights_drop` = a_j/b_j on the Semantic side; `vert_zip_attain` twice +
   the affine pairLine difference = dropQ on the hull side; `exists_face`
   locates the face).
6. **§7 assembly** — (α) at every column: `npHeight_le` at the dot +
   `Int.ceil_le` (⊤ columns trivial); (β) at vertex columns: the vertex IS a
   dot on the hull, so the value is pinned exactly (`Int.ceil_natCast`).

The old BLOCKED note's peel-recursion plan was replaced by the equivalent
hull read-off (recorded at the proof site): the genuine vertex list IS the
leftmost-minimizer peel.

## Kernels consumed (all from the banked-sorry unit's layer, BANKED_SORRY_2026-08-08)

`OM/HullStability`: `hull_slope_mono`, `dropCollinear_corner`,
`collinear₃_of_pairSlope_eq`, `vert_zip_valid`, `vert_zip_attain`,
`pairLine_right_form`, `mem_hullAbscissae_min/max`, `sorted_head_min`,
`sorted_getLast?_eq`, `dropCollinear_getLast?`, `dropCollinear_cons_head`,
`zip_fst_lt`, `mem_of_getLast?_eq`. `OM/NewtonPolygon`: `npVertices` engine
(`npVertices_sorted/on_hull`, `vert_mem`, `npHeight_le`,
`pairLine_le_of_valid`, `hullDotAt` pins). The kernels SUFFICED — no narrowed
gap remains; no new axiom, no statement change anywhere.

## Perimeter

* `lean/LeanUrat/Scaffold/O12/Semantic.lean` — ONE import added
  (`LeanUrat.OM.HullStability`; direction Scaffold→OM, cycle-free — OM never
  imports Scaffold; precedent: `Scaffold/AnchorN2.lean` etc.); the `L6eHull`
  section (~830 lines) inserted as unit II-M9c before `L6e_covers`; the
  `sorry` body replaced by `exact L6eHull.exists_cell hCe hRe h0`; the II-M9
  as-built honesty block updated. STATEMENTS BYTE-UNCHANGED (all of them —
  the unit adds declarations and fills one proof body only).
  Section-variable gotcha recorded: the file-level `variable {e : ℕ}`
  precedes the section's `(w)`, so auto-bound order is `(e, w)` — all
  applications in the section are `X e w …` (the scratch had them `w e`;
  mechanically swapped at graduation).
* `lean/LeanUrat/Scaffold/O12/scratch_hullcovers.lean` — DELETED (graduated;
  d0e2b74 preserves the checkpointed original).
* Pre-existing, untouched, out of perimeter: two `push_neg` deprecation
  warnings (lines ~1142/~1421) and one `show`-vs-`change` lint (II-M10
  `L6e_null`) — they predate this unit.

## Gates

* `lake env lean LeanUrat/Scaffold/O12/Semantic.lean`: EXIT 0 (only the
  pre-existing warnings above).
* Full `lake build`: green, 8570 jobs.
* In-file census (Semantic is NOT in the capstone closure — nothing imports
  it; AxChk untouched by construction): `L6e_covers`, `L6e_partition`,
  `L6e_disjoint`, `L6eHull.exists_cell`, `L6eHull.theKappa`, `L6eHull.theS`,
  `L6eHull.heights_eq`, `massPoly_enum_display` ALL at
  `[propext, Classical.choice, Quot.sound]`, zero `sorryAx`.
* Statement fence: docstring + signature of `L6e_covers` byte-compared
  against `git show HEAD` — identical.

## Residuals

* II-M6 (`hull_eq_iff_cell`, Wave 4a) remains OPEN — II-M9 no longer waits on
  it, and the `L6eHull` layer (diagram + pins + `heights_eq`) is the natural
  base for a future attempt.
* Scaffold code-`sorry` census after this unit: **5** (`MeasureFloor/SumOne`,
  `DictIII/Window`, `DictIII/Devid`, `DictIII/CU1`, `ValueSide/Transfer`).

## Commit provenance (concurrency note)

This unit's content landed SPLIT across two commits by an index race with the
concurrent level-3 M1 EXACT-FIT unit: the four content files
(`Semantic.lean` +924, this note, the ledger entry, the PROJECT_STATE
milestone) were staged by this unit but swept into the concurrent commit
**a30f5e0** (whose message is the level-3 unit's); this unit's own commit
**c88b541** (the full L6e_covers message of record) carries the
`scratch_hullcovers.lean` deletion. Tree state after both is exactly this
unit's intended perimeter + the level-3 unit's; nothing lost, no
double-application. The provenance commit for this addendum follows.
