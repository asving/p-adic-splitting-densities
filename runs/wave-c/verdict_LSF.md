# UNIT LSF — VERDICT: THE SUB-FACE LEAF CENSUS IS FRAME-PARTITIONED AND THE
FIBERING'S FORWARD HALF LANDS — the extended pinned transport reads the frame
`(h, e', d)` off the CLASS (lift-free) and pins the cofactor STRICTLY above the
face line (lift-side ℕ∞ AND class-side windowed `resOrd`); `leafSubCount` is the
EXACT frame sum at every level; row 5 of all three masters is re-based onto the
finitely many per-frame laws `SubfaceFrameLaw` — while the per-frame law itself
(face box × steep census through pinned-depth `q^v` clusters) honestly does NOT
fire: the depth pin `v = h·d·(m − e'·d)` and CSL's drainage premise are the two
named remaining engines, exactly as TBT/CSL forecast (2026-08-31)

**Deliverable:** `leanfinal/Uniformity/ChapI/IFCG66.lean` (840 lines, ZERO sorries,
zero errors, ZERO warnings; 14 AxCheck footer lines).  **Axiom fence, exactly as
designed:** `strict_cone_of_side_singleton`, `class_strict_cone_of_side_singleton`,
`subFrames_five_witness`, `subfaceCell_disjoint` are pure Lean core
`{propext, Classical.choice, Quot.sound}`; every transport/partition/law theorem and
both census masters are Lean core + EXACTLY the owner-signed gate-(b) cite
`Uniformity.Density.Leaf.exists_slope_factorization` (B.42, inherited through
IFCG59's split engine — never re-consumed); the capstone master additionally
inherits exactly `Uniformity.Density.Tower.agnprw_termination` (ID12's, previously
declared).  The C.33 cites, `AX_cellRecursion`, and `sorryAx` do NOT occur.
Verification: per-increment `timeout 580 lake env lean Uniformity/ChapI/IFCG66.lean`
(5 increments, each GREEN; final: exactly the 14 expected axiom prints); targeted
`lake build Uniformity.ChapI.IFCG66` GREEN (9036 jobs); aggregator
`lake env lean Uniformity/ChapI.lean` GREEN with the IFCG66 line appended after
IFCG64's (the one sanctioned touch; IFCG65's line appeared concurrently from its
own unit — no conflict).  NO git operations.  IFCG65.lean untouched.

## ★★★ THE HEADLINES

    theorem subface_transport_pinned :            -- ★★ THE EXTENDED TRANSPORT
      (sub-face leaf cell, min face (h,e'), any lift) →
      ∃ g R d, monicPoly a = g·R ∧ IsPure g h e' ∧ typeOf g = ⟨{(e',d)}⟩
        ∧ σ.data = (e',d) ::ₘ (typeOf R).data ∧ e'·d < m
        ∧ (classResidualPoly π c h e').natDegree = d   -- NEW: the frame is a
                                                       -- lift-free read off the cell
        ∧ sideSet X R h e' = {R.natDegree}             -- NEW: THE STEEPNESS SEED
    theorem subface_cofactor_class :              -- ★★ THE FIBERING, FORWARD HALF
      … ∧ ∀ j < deg R, h·(deg R − j) < e'·resOrd((proj of R's coeff vector) j)
      -- the cofactor's canonical CLASS lies strictly above the face line:
      -- cell ↦ (pinned face block, steep smaller-mass cofactor class)
    theorem leafSubCount_eq_sum_frames :          -- ★★ THE EXACT PARTITION COUNT
      leafSubCount = Σ_{(h,e',d) ∈ subFrames m σ} #subfaceCell(h,e',d)
      -- at EVERY level, every uniformizer; disjointness by minimal-face
      -- uniqueness + the lift-free d-read; off-frame cells provably EMPTY
    theorem leafSubfaceLaw_of_frameLaws :         -- ★★★ ROW 5 RE-BASED
      (∀ p ∈ subFrames m σ, SubfaceFrameLaw m p σ) → LeafSubfaceLaw m σ
    theorem decidedSliceAt_all_of_MASTER_FRAMES / _of_visCensus_frames /
      capstoneHypotheses_of_MASTER_FRAMES :       -- ★★★ ALL THREE MASTERS RESTATED

## The three charge items, disposition

**(1) THE FIBERING — the forward half LANDED; the exact `q^v` count coupling
honestly NOT.**
* Landed: the cell side of the correspondence is now complete.  §1 re-runs TBT's
  pinned transport with two new outputs — the class-residual degree pin (so
  `(h, e', d)` indexes cells canonically, no lift consulted) and
  `sideSet X R h e' = {R.natDegree}` (the cofactor's `(h,e')`-side is its single
  monic point).  The mechanism for the steepness seed is one new observation on
  top of TBT's proof: the minimal face's monic-point attainment (`NPAttains m`)
  puts `m` on the LIFT's side, so `sideMax F = m`; with `sideDeg F = d + 0` (the
  product law + the unit argument) this forces `sideMin R = m − e'·d = deg R` —
  the side collapses.  The coefficient conversions land in both coordinates:
  `strict_cone_of_side_singleton` (`h·(r−j) < e'·npHgt` in ℕ∞, Lean-core) and
  `class_strict_cone_of_side_singleton` (`h·(r−j) < e'·resOrd` on the canonical
  class at any window `N ≥ r`, Lean-core — the windowed read is exact below the
  window by IFCG23's bridge and saturates at `N` above it, where the face line
  sits below `e'·N` outright).  Composite: ★ `subface_cofactor_class`.
* NOT landed (the exact fence): the `q^v`-cluster count coupling
  `#subfaceCell(N) · q^v = #box(N) · #steepDec(shifted)` needs (i) THE DEPTH PIN —
  `v(Res(g, R)) = h·d·(m − e'·d)` for a face block against a steep cofactor —
  which TBT derived by the root argument but which is NOT machine-checked (and
  needs either a weighted-Leibniz Sylvester-determinant bound or the
  `len O[X]/(R,g)` route through CSL's Smith engine: a full unit), and (ii) THE
  DRAINAGE premise — the cofactor CLASS decided at the shifted level `N − v` —
  CSL's fence item 2 verbatim (the canonical cofactor's TYPE is pinned, but its
  class-decidedness does not follow from the product's decidedness by any landed
  engine; my attempt via the depth-`v` Newton correction pins the corrected
  factorization back to the canonical pair, yielding no information about the
  perturbed lift — recorded so the successor does not retry it).

**(2) THE COUNT + LAW + MASTER — assembled at the partition level; the masters
STATED AND PROVEN on the re-based family.**
* `subFrames m σ` (Finset: `1 ≤ h < e'` coprime, `1 ≤ d`, `e'·d < m`,
  `(e',d) ∈ σ.data`) + `subfaceCell` (cells at pinned face and residual degree) +
  ★ `leafSubSector_eq_biUnion` (the disjoint tiling) + ★ `leafSubCount_eq_sum_frames`
  (the EXACT count identity at every finite level) + `subfaceCell_eq_empty_of_not_mem`
  (off-frame emptiness — the partition's completeness in consumable form).
* ★ `SubfaceFrameLaw m h e' d σ` (the per-frame `ZcURLim`) +
  ★★★ `leafSubfaceLaw_of_frameLaws` (row 5 = the finite per-frame family, via
  `ZcURLim_sum` + the partition).
* ★★★ The three masters (PCD spine, LSC/FC-Eis spine, capstone) recomputed with
  the leaf row consuming the per-frame family under the unchanged guards
  (+ TBT's `2 ≤ card σ.data`; singleton σ stays closed).  HONEST ACCOUNTING: like
  IFCG62's row-2 re-base, this is a DISCHARGE-PATH refinement, not a premise
  weakening — the per-frame family is finer content whose sum recovers the joint
  law; the successor proves frames one at a time.
* Nonvacuity pin (kernel-decided): `subFrames_five_witness :
  subFrames 5 ⟨{(4,1),(1,1)}⟩ = {(1,4,1), (3,4,1)}` — exactly LSC's hand-checked
  witness frame (slope 1/4 block `(4,1)`, at the two coprime heights `h ∈ {1,3}`),
  the first open instances of the remaining family.

**(3) THE HONEST REMAINDER, named minimally:** `SubfaceFrameLaw e h e' d σ` at
`(h, e', d) ∈ subFrames e σ`, guarded as before — row 5's exact per-axis content.
Each member = ONE face digit box (LSC's `card_leafIrrBox` at mass `e'·d` — the box
definition is already general, count `N_d(q)·q^{e'd·K − wLeaf h e' d}`) convolved
with ONE steep decided census (mass `r = m − e'·d`, type `τ` with
`σ.data = (e',d) ::ₘ τ.data`, carrier = `class_strict_cone` ∩ decided) through the
pinned-depth clusters.  Note `τ` is DETERMINED by the frame (multiset cons is
cancellative), so no extra sum over types appears.

## The surviving master premise list (LSC-spine numbering, after LSF)

| # | premise | status after LSF |
|---|---|---|
| 1 | `FactorCorrespondenceAt D`, `D ≥ 2` | unchanged (THE STAGED CITE, owner gate) |
| 2 | `EisFullSpanRemainderLaw m σ` → per-frame `MixedFaceLaw` (IFCG62) | unchanged |
| 3 | `SplitConvolutionDefectLaw e σ`, guarded | unchanged (RDC's two census laws) |
| 4 | `PowerConvolutionDefectLaw e σ`, guarded | unchanged |
| 5 | ~~`LeafSubfaceLaw e σ`, non-singleton~~ → **`SubfaceFrameLaw e h e' d σ` at `(h,e',d) ∈ subFrames e σ`**, same guards | the joint law is DISCHARGED onto the per-frame family; partition arithmetic, frame forcing, off-frame emptiness, and the fibering's forward geometry are machine-checked out of it |

## Discharge pointers (for the successor units, in dependency order)

1. **THE DEPTH PIN** (the keystone; a unit of its own): for `γ` in the face box
   (mass `e'·d`) and `ρ` steep (mass `r`), `mixDepth π γ ρ = h·d·r` — RDC's
   `mixDepth` is the right instrument (lift-free).  The root argument: every one
   of the `e'd·r` root pairs differs at valuation exactly `h/e'` (block roots AT
   the face value, cofactor roots strictly above), so `v(Res) = e'd·r·(h/e')`.
   Machine-check candidates: (a) the weighted-Leibniz lower bound on the
   Sylvester determinant + the exact corner term `±g₀^r` (`e'`-cleared integer
   weights; every off-minimal permutation carries excess ≥ 1); (b)
   `v(Res) = len O[X]/(R, g)` through CSL's Smith/index-determinant engine
   (`natCard_quotient_range_smith`).  The `≥` half alone already gives the fiber
   lower bounds.
2. **THE STEEP CENSUS** (`SteepLaw r τ h e'`-to-be): decided-`τ` classes in the
   strict cone.  At `r = 1` it is trivial (steepness `⟺` the X-stratum since
   `h < e'`; every linear is decided `⟨{(1,1)}⟩`; count `q^{N−1}` exactly) — the
   witness frames `(1,4,1)/(3,4,1)` at `m = 5` need ONLY this member.  General
   `r`: genuinely new (the fractional-slope analogue of CN5's deep census; NO
   type-preserving substitution exists in `O` for fractional lines — do not
   retry the `X ↦ πX` route).
3. **THE DRAINAGE** (CSL fence 2): level-stabilization of the steep decided
   census — needed only for the squeeze's surjectivity leg; IFCG60 §5's cluster
   bridge (`zcURLim_visDepth_of_clusters`, `tendsto_visDepth_sub_clusters`) is
   the assembly pattern once 1–2 land, with CSL's `natCard_pairNbhd_of_mixDepth`
   (the exact `q^v` clusters) and `decidedAt_mulClass_of_mixDepth` (the transfer)
   as the two firing pins, and RDC's `mulClass_fiber_gap` as the separation leg.
4. The image characterization (products of genre pairs land in `subfaceCell`) is
   the remaining SDL-§1-genre wiring: minimal face of a DISJOINT-slope product +
   stratum/shallow/non-pure-face bookkeeping — routine given the landed product
   side laws (B.39a §7) and this file's §1.

## New definitions (trust boundary — flag for review)

`subFrames` (the frame Finset) · `subfaceCell` (the per-frame carrier) ·
**`SubfaceFrameLaw`** (THE new named premise family).  All three are one-line
definitions over landed corpus objects; all consumed statements
(`leafSubSector`, `leafSubCount`, `LeafSubfaceLaw`, `MinFaceAt`,
`classResidualPoly`, the IFCG59 masters) are byte-untouched.

## File map (`leanfinal/Uniformity/ChapI/IFCG66.lean`, 840 lines)

§0 kit: private replicas (`isKey_X`, `mem_sideSet_iff'`, `npHgt_monic_top`,
`suppVal_ne_top_of_monic`, `resPoly/sideMin/sideDeg_congr`, `ncard_biUnion_eq`) ·
§1 ★★ `subface_transport_pinned` (202), ★ `strict_cone_of_side_singleton` (408),
★ `class_strict_cone_of_side_singleton` (446), ★★ `subface_cofactor_class` (500),
★ `subface_frame_read` (523) · §2 `subFrames` (547), `mem_subFrames_iff` (553),
`subFrames_five_witness` (575), `subfaceCell` (583), ★★ `leafSubSector_eq_biUnion`
(593), `subfaceCell_disjoint` (613), ★★ `leafSubCount_eq_sum_frames` (630),
★ `subfaceCell_eq_empty_of_not_mem` (643) · §3 ★★ `SubfaceFrameLaw` (666),
★★★ `leafSubfaceLaw_of_frameLaws` (674) · §4 ★★★ the three masters (711, 740,
770) · AxCheck footer (14 lines).  Imports: Mathlib + IFCG59 (everything else
transitive).  Aggregator: one import line appended after IFCG64's.

## Repair log (3 error rounds over 5 increments; every theorem landed as designed — no mathematical failures)

1. `rw` does NOT close the defeq leftover `d + 0 = d` in this pin (twice) —
   trailing `omega`.
2. THE `sideMax`-vs-`Finset.max'` OMEGA ATOM MISMATCH (SDL's log genre,
   re-confirmed): `have h := Finset.max'_mem …` yields the `.max'` atom, opaque
   to omega against `sideMax` — either the `Finset.max'_le` refine shape (goal
   unifies up to defeq) or a type-ascribed `have h : sideMax … ∈ … := Finset.max'_mem _ _`.
3. Fin-typed index MOTIVE FAILURE: `rw [← hmp] at hstrict` (rewriting
   `R := monicPoly vec` under `j : Fin R.natDegree`) breaks the motive — rewrite
   in the bridge equation instead (`npHgt_monicPoly_eq`'s index is plain ℕ), then
   rewrite the resulting closed equation into the target hypothesis.  Also
   `resOrd_le` lives in `Uniformity.Density.Induction` (H107), not the Density root.

## Cross-checks

* The steepness seed at LSC's witness (`m = 5`, heights `(2,1,1,1,1)`): cofactor
  `R` linear with `v(R₀) = 1`, face line `h·(1−0)/e' = 1/4` — strictly above ✓;
  `subFrames_five_witness` pins exactly the frames the witness realizes.
* At singleton σ: `subFrames` may be nonempty, but the CELLS are empty (IFCG59
  §2) and the masters route through TBT's `2 ≤ card σ.data` guard — no tension.
* The per-frame ↦ joint direction reproduces IFCG62's row-2 idiom
  (`eisFullSpanRemainderLaw_of_mixedFaceLaws`) verbatim at row 5 — the two rows
  now present the same per-axis interface to the endgame.
