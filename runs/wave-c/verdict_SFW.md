# UNIT SFW — VERDICT: THE r = 1 FRAME LAWS ARE CLOSED AND THE WITNESS LEAF LAW
FIRES — `subfaceFrameLaw_r_one : SubfaceFrameLaw m h e' d σ` at EVERY frame with
`m = e'·d + 1`, with NO value-law premises and NO drainage premises (the r = 1
steep census, both shifted decidedness legs, the image characterization, AND the
fiber uniqueness all closed exactly); ★★★ `leafSubfaceLaw_five :
LeafSubfaceLaw 5 ⟨{(4,1),(1,1)}⟩` — THE FIRST NON-SINGLETON LEAF LAW, end-to-end
machine-checked at LSC's hand-checked witness; all three masters recomputed with
the leaf row demanded only at the r ≥ 2 frames (2026-08-31)

**Deliverable:** `leanfinal/Uniformity/ChapI/IFCG69.lean` (2092 lines, ZERO
sorries, zero errors, ZERO warnings; 13 AxCheck footer lines — 14 public theorems
+ 4 public defs, 24 privates).  **Axiom fence, machine-exact at landing:**
`card_steepLin`, `card_pinnedBox`, `nzPoly_eval_card`, `decidedAt_linear`, and —
better than forecast — ★ `mul_mem_subfaceCell` (THE IMAGE) are PURE Lean core
`{propext, Classical.choice, Quot.sound}`; `subfaceCell_factors`,
`subfaceCell_r_one_empty`, `subfaceFrameLaw_r_one`, `leafSubfaceLaw_five`,
`subfaceFrameLaws_of_r_two`, and the two census masters are Lean core + EXACTLY
the owner-signed gate-(b) cite `Uniformity.Density.Leaf.exists_slope_factorization`
(B.42, inherited through IFCG66's transport — never re-consumed); the capstone
master additionally inherits exactly `Uniformity.Density.Tower.agnprw_termination`
(ID12's, previously declared).  The C.33 cites, `AX_cellRecursion`, and `sorryAx`
do NOT occur.  Verification: per-increment
`timeout 580 lake env lean Uniformity/ChapI/IFCG69.lean` (8 increments, each
GREEN; final: exactly the 13 expected axiom prints); targeted
`lake build Uniformity.ChapI.IFCG69` GREEN (9043 jobs); aggregator
`lake env lean Uniformity/ChapI.lean` GREEN with the IFCG69 line appended after
IFCG68's (the one sanctioned touch).  NO git operations.  IFCG68.lean untouched.

## ★★★ THE HEADLINES

    theorem subfaceFrameLaw_r_one :               -- ★★★ THE r = 1 FRAME LAW
      1 ≤ h → h < e' → coprime → 1 ≤ d → m = e'·d + 1 →
      SubfaceFrameLaw m h e' d σ                  -- UNCONDITIONAL (only B.42);
      -- value = nz_d(q)/q^(wLeaf h e' d + h·d + 1) at the forced type
      --         (nz_d = necklace count with nonzero constant: q−1 at d = 1,
      --          N_d(q) for d ≥ 2), and 0 at every other σ (cell provably empty)
    theorem leafSubfaceLaw_five :                 -- ★★★ THE WITNESS LEAF LAW
      LeafSubfaceLaw 5 ⟨{(4,1),(1,1)}⟩            -- both frames (1,4,1)/(3,4,1)
                                                  -- have r = 1; row 5 CLOSES here
    theorem mul_mem_subfaceCell :                 -- ★★ THE IMAGE (Lean-core!)
      (pinned box) × (steep linear) --mulClass--> subfaceCell, decided/stratum/
      shallow/non-pure-face/minimal-face/residual all discharged
    theorem subfaceCell_factors :                 -- ★★ THE SURJECTION + σ-FORCING
      cell → σ.data = (e',d) ::ₘ {(1,1)} ∧ ∃ carriers, mulClass = cell class
    private fiber_eq_pairNbhd :                   -- ★★ THE SEPARATION (new engine)
      the mulClass fiber over a cell inside the carriers = ONE pairNbhd cluster
    theorem decidedSliceAt_all_of_MASTER_FRAMES_r2 / _visCensus_frames_r2 /
      capstoneHypotheses_of_MASTER_FRAMES_r2 :    -- ★★★ MASTERS: leaf row now
      demands SubfaceFrameLaw only at frames with e ≠ e'·d + 1 (r ≥ 2)

## The charge, disposition

**(1) r = 1 CLOSED, stronger than charged.**  The charge asked for the assembly
"under the < e value laws"; what landed needs NO value laws — every ingredient is
exact at finite level:

* **THE COUNT IDENTITY** (`card_cell_mul`, exact for `M ≥ h·d`):
  `#subfaceCell(N)·q^(h·d) = #pinnedBox(N) · #steepLin(N)`, `N := M + m`, with
  `#pinnedBox = nz_d(q)·q^(e'd·N − wLeaf h e' d)` (`card_pinnedBox` — LSC's
  `card_leafFiber` engine over the NONZERO-CONSTANT genre; at `d = 1` the corner
  pin is a PROPER sub-box of `leafIrrBox`, which is exactly why LSC's
  `leafIrrBox_corner` demanded `d ≥ 2` — the count dictionary `nzPoly` is `X − 1`
  at `d = 1` and IFCG19's `necklacePoly` above) and
  `#steepLin = q^(N−1)` (`card_steepLin` — the m = 1 census: IFCG36's
  `card_setOf_resDig` at the bottom digit; steepness ⟺ the X-stratum under
  `h < e'`).  So the normalized count is EVENTUALLY CONSTANT
  `nz_d(q)/q^(wLeaf + h·d + 1)` — a fixed rational function of q, and `ZcURLim`
  fires by eventual constancy.  At mismatched σ the transport forces emptiness
  (`subfaceCell_r_one_empty`), value 0.
* **THE IMAGE** (`mul_mem_subfaceCell`, Lean-core): the product coefficient
  identities `P_j = g_{j−1} + α·g_j` give the frame cone with the EXACT
  coordinate `resOrd = h·d` at abscissa 1 (the ultrametric tie: every competing
  term sits at `tLeaf + j ≥ h·d + 1`) and the strictly-raised corner; the face
  package (support `h·m` attained at 1 and m, missed at 0; stratum; shallow at
  abscissa 1; ¬pure-face via `(hd+1)(m−1) ≤ m·hd ⟹ e' ≤ h` contradiction); the
  residual `resPoly(g·R) = resPoly(g)·unit` (the steep linear side residual has
  degree 0 and nonzero constant by B.30, hence a unit) through the class→lift
  side transport (IFCG28's `sideSet_monicPoly_eq` on BOTH factors); and the
  DECIDEDNESS through DPN's `decidedAt_mulClass_of_cones` with both shifted
  premises DISCHARGED — `box_decided_shifted` (all pinned-box reads live at digit
  levels ≤ h·d, stable down to the window `N − h·d`; IFCG37's
  `decidedAt_of_spanning_irr` fires there) and `decidedAt_linear` (every mass-1
  class is decided `⟨{(1,1)}⟩`, outright by `typeOf_of_natDegree_one`).  THE
  DRAINAGE REMAINDER OF LSF/DPN IS DISCHARGED AT r = 1, not carried.
* **THE SEPARATION** (`fiber_eq_pairNbhd` — the genuinely new engine, Hensel-free):
  two carrier factorizations of one product class agree factorwise mod
  `π^(N−h·d)`.  Mechanism: evaluate the level-N product congruence at the steep
  root `−α`; the pinned box forces `π^(h·d) ∥ g(−α)` EXACTLY (the j = 0 term is
  exact, every j ≥ 1 term carries `tLeaf(j) + j ≥ h·d + 1`, the top carries
  `e'd ≥ h·d + 1`), so cancelling the exact unit pins the roots:
  `π^(N−h·d) ∣ β − α`; then the monic cancellation (`C z ∣ S·T`, `T` monic ⟹
  `C z ∣ S` — the quotient-ring one-liner) recovers the block side.  Stability of
  the carriers under mod-`π^(h·d+1)` perturbation closes the reverse inclusion,
  so the fiber is EXACTLY one `pairNbhd` cluster of size `q^(h·d)` by DPN's
  `natCard_pairNbhd_of_cones`.  (LSF's recorded dead end — the depth-v Newton
  correction — was NOT retried; this evaluation route replaces it at r = 1.)
* **THE BIJECTION GENRE** (charge item iii): landed as image + surjection + exact
  fibers, i.e. the cardinality identity — the IFCG16 §7 genre confirmed.

**(2) GENERAL r — the honest named remainder.**  NOT closed, exactly as
forecast: at `r = m − e'·d ≥ 2` the two missing engines are (i) THE STEEP CENSUS
(the count of decided-τ classes in the strict cone at mass r — the
fractional-slope analogue of the deep census; the value laws + IFCG16's
`tendsto_decidedSeq_comp` + IFCG60 §5's cluster bridge are the anticipated
consumption pattern) and (ii) THE r ≥ 2 SEPARATION (this file's one-root
evaluation is specific to a linear cofactor; the general fiber uniqueness needs
the Bezout/resultant gap through `mulClass_fiber_gap`'s congruence input, or the
polygon-factorization uniqueness).  `subfaceFrameLaws_of_r_two` packages the
reduction: the full family follows from the r ≥ 2 members alone.

**(3) THE LEAF ROW / MASTERS RECOMPUTED**: all three spines re-stated with the
row-5 premise `∀ p ∈ subFrames e σ, e ≠ p.2.1·p.2.2 + 1 → SubfaceFrameLaw …` —
strictly weaker premises than IFCG66's masters (the r = 1 members are theorems).
Master premise surface after SFW: rows 1–4 unchanged; row 5 = the r ≥ 2 frames
only.

## New definitions (trust boundary — flag for review)

`pinnedBox` (LSC's `leafCone` + corner `resOrd = h·d` EXACT + irreducible
`leafResPoly` — the transport-image carrier; at `d ≥ 2` provably = `leafIrrBox`,
not stated since unconsumed) · `steepLin` (mass-1 classes with `1 ≤ resOrd` — the
r = 1 strict cone) · `nzGenre` (irreducible monic degree-d residue polys with
nonzero constant) · `nzPoly` (its counting polynomial: `X − 1` if `d = 1` else
`necklacePoly d`).  All four are one-liners over landed corpus objects.  Every
consumed statement (`SubfaceFrameLaw`, `subfaceCell`, `subFrames`,
`LeafSubfaceLaw`, `pairNbhd`, `DecidedAt`, `leafIrrBox`, the IFCG66/67 transport
and couplings, the IFCG59/66 masters) is byte-untouched.

## File map (`leanfinal/Uniformity/ChapI/IFCG69.lean`, 2092 lines)

§0 kit (141–314): counting/digit/congr replicas + NEW `C_dvd_of_C_dvd_mul_monic`
(monic cancellation via `O⧸(z)`), `dvd_eval_of_C_dvd`, `monicPoly_one_eq` ·
§1 carriers+counts (327–520): `pinnedBox`, `steepLin`, ★ `card_steepLin`,
`nzGenre`, ★★ `card_pinnedBox`, `nzPoly`, `nzPoly_eval_card` ·
§2 product data (528–866): the `tLeaf` ladder lemmas, ★ `prod_class_data`,
★ `face_package` · §3 (870–1075): ★★ `prod_residual` · §4 (1084–1268):
`decidedAt_linear`, ★ `box_decided_shifted`, ★★ `mul_mem_subfaceCell` ·
§5 (1273–1390): ★★ `subfaceCell_factors`, ★ `subfaceCell_r_one_empty` ·
§6 (1395–1710): `corner_lt_tLeaf_add`, `box_lift_divs`, ★★ `fiber_eq_pairNbhd` ·
§7 (1715–1925): ★★ `card_cell_mul`, ★★★ `subfaceFrameLaw_r_one` ·
§8–9 (1930–2065): ★★★ `leafSubfaceLaw_five`, ★★ `subfaceFrameLaws_of_r_two`, the
three masters · AxCheck footer (13 lines).
Imports: Mathlib + IFCG67 (LSF/DPN and the spine transitive).  Aggregator: one
import line appended after IFCG68's.

## Repair log (7 error rounds over 8 increments; every theorem landed as designed — no mathematical failures)

1. Namespace drift: `npHeight_coe` lives in IFCG24 (not IFCG22); `resOrd_ge_iff`
   in `Induction` (H107); linear irreducibility over a FIELD is mathlib's
   `Monic.irreducible_of_degree_eq_one` (the corpus's
   `irreducible_of_monic_natDegree_one` demands a DVR).
2. Anonymous-binder trap: hypotheses written `i < n → P i` are NOT in omega's
   context when elaborating a proof term inside `P i` — name the binder.
3. `Nat.mul_lt_mul_right` is an IFF in this mathlib; `dvd_sub'` is gone
   (`dvd_sub`); `Nat.le_or_lt` gone (`by_cases`).
4. `set m := e' * d + 1` REWRITES THE TYPE of the context class, splitting the
   goal's `c` from the hypotheses' `c` — write the literal out instead.
5. `decidedAt_linear` as a raw term hit a whnf heartbeat timeout unfolding
   `DecidedAt` — the two-line tactic form is instant.  Universe fence:
   `subfaceCell` is declared over `O : Type`, not `Type*`.
6. The `h·d·1` vs `h·d` defeq gap (Nat.mul by literal 1 is NOT reducible):
   convert with one `Nat.mul_one` rewrite before consuming DPN's r-generic
   couplings; ditto `((0 : Fin 1) : ℕ)` needs an `rfl`-rewrite before omega.
7. `IsUnit.dvd_mul_left` is an iff with no explicit args;
   `IsLocalRing.mem_maximalIdeal` takes the element explicitly; `C_sub` fires
   left-to-right after `ring`-normalizing.

## Cross-checks

* At the witness frames: `(1,4,1)`: value `= (q−1)/q^(wLeaf 1 4 1 + 2)` with
  `wLeaf 1 4 1 = Σ_{i<4}(⌈(4−i)/4⌉ + [4∣i]) = (1+1)+1+1+1 = 5`, i.e. `(q−1)/q^7`;
  `(3,4,1)`: `wLeaf 3 4 1 = (3+1)+3+2+1 = 10`, value `(q−1)/q^14` — both of the
  `(q−1)/q^w` genre of IFCG24's `ZcURLim_qmonomial`, as LSC's box arithmetic
  predicts (per-frame mass balance: `e'd·N − wLeaf + (N−1) − hd` vs `mN`
  exponent bookkeeping checked by the machine in `subfaceFrameLaw_r_one`).
* The separation reproduces the root picture: the steep root sits at valuation
  ≥ 1, the block roots at h/e' < 1; `g(−α)` picks up exactly the corner
  valuation h·d = v(Res(g, R)) — DPN's depth pin read at one point.
* `mul_mem_subfaceCell` Lean-core confirms the forward image never consults the
  transport — only the surjection direction pays B.42, exactly once.
