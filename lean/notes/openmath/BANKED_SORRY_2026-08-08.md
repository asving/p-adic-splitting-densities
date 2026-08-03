# BANKED_SORRY_2026-08-08 — the corpus's ONE banked `sorry` DISCHARGED

**Unit:** synthesis-7 queue #10 (pass-6 finding F2d: "BPLL's hull core reaches the
repo's ONE banked sorry"). Charter: `docs/SYNTHESIS_PASS7_2026-08-08.md` §F2(d) + the
r34/§39 queue display, item 10.

**VERDICT: PROVED, `sorry`-free, Lean-core footprint.** The banked
`LeanUrat.OM.B.npVertices_stable_of_hull_preserved` (`lean/LeanUrat/OM/Classifier.lean`,
the repaired three-hypothesis hull-invariance contract, off the capstone path — the
corpus's single banked `sorry` since the 2026-07 REDSTAB2 round) is now fully proved.
The statement is byte-unchanged (only `:= by sorry` became a term-mode `exact` of the
new core theorem). The OM tree greps ZERO `sorry` statements after this unit (the sole
remaining hit is a docstring mention of a long-deleted theorem in `LevelNCount.lean`).

## What was proved

For `S S' : Finset (ℕ × ℕ)` nonempty, with
* `hpres`  — every genuine vertex of `S'` is a dot of `S` (same decorated point),
* `habove` — every dot of `S` lies weakly above the `S'`-hull
  (`npHeight S' (P.1) ≤ P.2`),
* `habs`   — every `S`-abscissa is an `S'`-abscissa,

the genuine vertex lists coincide: `npVertices S = npVertices S'`.
(The two-hypothesis form is FALSE — machine-checked counterexample
`npVertices_not_stable_of_hull_preserved` in `OM/NewtonPolygon.lean`; `habs` is the
repair, supplied for free at the sole use-site `boxValSupport_reduce_stable_R`.)

## Proof architecture (new module `lean/LeanUrat/OM/HullStability.lean`, ~1740 lines)

Imports: Mathlib + `LeanUrat.OM.NewtonPolygon` ONLY. The BPLL §0 list kernels
(`zip_fst_lt`, `sorted_getLast?_eq`, `mem_of_getLast?_eq`, `dropCollinear_getLast?`,
`collinear₃_trans`, `dropCollinear_between`, `pairLine_right_form`) are copied VERBATIM
from `Scaffold/DictIII/BasePolyLength.lean` with attribution — `Classifier` sits on the
capstone import path, and importing BPLL would drag the 183-module Scaffold closure
under the OM tree (checked: no import cycle either way; hygiene decision).

New content, bottom-up:

1. **§B sorted-list kernels** — head/last pins (`sorted_head_min`,
   `sorted_le_getLast?`), abscissa injectivity (`fst_inj_of_sorted`),
   no-entry-between-consecutive (`no_between_nat`), predecessor/successor existence
   (`exists_zip_left/right`), strict and rational bracket covers
   (`zip_bracket`, `bracket_cover`), and `sorted_eq_of_mem_iff` (strictly-sorted point
   lists with equal membership are equal — replaces any Mathlib perm/sort dependence).
2. **§C affine/collinearity arithmetic** — slope transfer from two coincident
   evaluations (`pairSlope_eq_of_eval₂`, `pairLine_eq_of_eval₂`,
   `pairLine_eq_of_through`), chord-through-collinear-point
   (`pairLine_eq_of_collinear₃`), collinearity from equal adjacent slopes
   (`collinear₃_of_pairSlope_eq`), the junction transitivity `collinear₃_trans'`
   (cross-product identity: goaldiff·(c₁−a₁) = (c₁−z₁)·h₁ + (c₁−b₁)·h₂), and affine
   domination on a bracket (`affine_le_on_Icc`).
3. **§D THE SURVIVOR-CORNER LAW** (`dropCollinear_corner`) — on a strictly-sorted
   input, `dropCollinear` leaves NO collinear consecutive triple. This is the converse
   companion of BPLL's `dropCollinear_between` and the fact that FORCES the target's
   truth (a genuine `S'`-vertex must be a genuine corner, so the `S`-hull cannot drop
   it). Induction mirrors `dropCollinear_between`; the junction case (head `a` merges
   `b` away against kept `(c', z)`) closes by `collinear₃_trans'` — two lines through
   the two distinct points `a, c'` coincide.
4. **§E hull kernels** — valid-line right-endpoints are on the hull
   (`valid_right_on_hull`); slope monotonicity at a hull dot (`hull_slope_mono`, the
   3-point `slope_mono_adjacent` argument); extreme abscissae are hull abscissae
   (`mem_hullAbscissae_min/max`, flattest-rightward / steepest-leftward argmin chord
   constructions mirroring BPLL's `npHeight_pos_left`/`npHeight_at_zero`);
   **consecutive FULL vertices span valid chords** (`full_zip_valid`: the flattest
   chord out of the left endpoint is valid, its right endpoint is a hull dot, hull
   dots cannot sit strictly between consecutive hull abscissae, so the chord to the
   next full vertex rides the same line); chord attainment on full-vertex brackets
   (`full_zip_attain` via the proved `npHeight_eq_pairLine_of_validLine`); the **glue
   induction** (`glue_aux`, fuel = horizontal span) lifting attainment to consecutive
   GENUINE vertices through `dropCollinear_between` (every intermediate full vertex is
   collinear with the surviving pair, so the per-bracket chords all ride the
   survivors' chord); `vert_zip_attain` + `vert_zip_valid` (the latter through
   `chord_valid_of_between_le`, the `consecutive_chord_valid` engine with the
   empty-interior hypothesis generalized to chord domination).
5. **§F master assembly** (`npVertices_stable_of_hull_preserved_core`) —
   (i) `S'`-extreme abscissae `m', M'` pin the head/last of BOTH vertex lists (via
   `habs` + `hpres` the `S`-abscissa range is contained in `[m', M']`);
   (ii) the hulls AGREE on `[m', M']`: every `S`-valid line is dominated by the
   `S'`-vertex chords at the `S`-dots above them (`affine_le_on_Icc` + `hpres`), and
   every `S'`-vertex chord is `S`-valid (it is ≤ the `S'`-hull everywhere, hence ≤
   every `S`-dot by `habove`) — `le_antisymm` of the two `sup'` bounds;
   (iii) V′ ⊆ V: a dropped `S'`-vertex would be strictly bracketed by consecutive
   `S`-vertices whose chord attains the (common) hull across its abscissa, forcing its
   left and right `S'`-chords to share that slope (`pairSlope_eq_of_eval₂` on two
   points of the overlap) — contradicting the survivor-corner law on the `S'` side;
   (iv) V ⊆ V′: symmetric, with the roles of the corner law swapped (an `S`-vertex at
   a non-`S'`-vertex abscissa sits strictly inside an `S'`-vertex bracket where the
   common hull is affine, killing its corner);
   (v) `sorted_eq_of_mem_iff` closes.

## Falsifier (test-before-prove; falsifiers only, no evidentiary weight)

`verification/openmath/banked_sorry_falsifier.py` — mirrors the Lean definitions
exactly (junk-0 division, `sup'` over valid lines, floor/toNat, `dropCollinear`
recursion). Two batteries, run before proving: (a) the repaired 3-hypothesis statement
on generated instances (vertices + above-hull dots at `S'`-abscissae): 0 violations /
4000 applicable (seed 0); (b) the survivor-corner law on random sorted lists:
0 violations / 4000 (seed 1).

## Perimeter

* `lean/LeanUrat/OM/HullStability.lean` — NEW, sorry-free, imports Mathlib +
  NewtonPolygon only.
* `lean/LeanUrat/OM/Classifier.lean` — the `sorry` body replaced by the term
  invocation; ONE import line added (`LeanUrat.OM.HullStability`); docstring/status
  comments updated at the four honesty sites (theorem docstring, file header, the
  `boxValSupport_reduce_stable_R` docstring, the `certLevel_stabilizes` census note).
  STATEMENT BYTE-UNCHANGED.
* Capstone footprints: `lake env lean LeanUrat/AxChk_baseline.lean` re-run after the
  fill — see the footprint block below.
* `Scaffold/DictIII/BasePolyLength.lean` (BPLL): UNTOUCHED.

## Footprint verification (post-fill, compiled)

* `lake build` full: green (8698 jobs incl. `AxChk_baseline`).
* `lake env lean LeanUrat/AxChk_baseline.lean`: exit 0, 1099 lines, **zero `sorryAx`
  anywhere in the census**; every capstone (`montes_unconditional`, all W/W3/W4/W5
  variants + exhaustives, `goal_theorem_montes`, `goal_theorem_via_montes`,
  `montes_unconditional_n2_full`) at `[propext, Classical.choice, Quot.sound]` —
  footprints UNCHANGED from baseline.
* Direct probes:
  - `LeanUrat.OM.B.npVertices_stable_of_hull_preserved`:
    `[propext, Classical.choice, Quot.sound]` (was `sorryAx`-carrying).
  - `LeanUrat.OM.B.boxValSupport_reduce_stable_R` (the sole consumer):
    `[propext, Classical.choice, Quot.sound]`.
  - `LeanUrat.OM.B.certLevel_stabilizes`: `[propext, Classical.choice, Quot.sound,
    omReadValuation_lt_of_certLevel_fkeyed]` — the `sorryAx` is GONE; only the
    declared NAMED CITE axiom remains, exactly as predicted.
  - `LeanUrat.OM.NewtonPolygon.npVertices_stable_of_hull_preserved_core` and
    `dropCollinear_corner`: `[propext, Classical.choice, Quot.sound]`.
