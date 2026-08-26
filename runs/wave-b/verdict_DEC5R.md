# DEC5R verdict — H.116b4 examples-first map

**VERDICT: SUPPLY delivered; signed node remains BLOCKED.**  The five-row proof map is supplied at
`docs/in-progress/H116B4_MAP_2026-08-26.md`.  H.116b4 itself is not LANDED: the signed
`planted_presentation_card` remains unchanged at `leanspec/Leanspec/ChapH.lean:2963`, and the
chapter-H census already classifies it and `betaExtract_fiber_card` as the open research family
(`runs/wave-b/verdict_XSC.md:68`).

## What was supplied

1. The inherited battery was rerun, then extended only where its tables reported a law without
   exposing the mechanism.  The final run took 153.8 seconds and ended
   `==== ALL CHECKS PASSED ====` (`runs/wave-b/out_DEC5R_battery.log:84`).
2. The extension checks that every one-grade multiplication map is affine with one level-fixed
   linear part, that a node is live exactly when its obstruction lies in the image, and that the
   aggregate next-target histogram is uniform on its reachable support
   (`runs/wave-b/h116b4_battery.py:535`, `:577`).
3. The map converts those observations into five proof rows, each with the requested battery cell,
   numerical mechanism, Lean-facing statement, landed inputs, REUSE/NEW classification, and honest
   size/blocker.  The recommended order is ghost -> cofactor/Fit -> restricted Smith -> one-grade
   lifting -> uniform-pushforward iteration (`docs/in-progress/H116B4_MAP_2026-08-26.md`,
   “Ordering recommendation”).

The extension was necessary for GR-9/GR-10.  “One `K` per level” alone did not explain why every
nonempty bucket has that size or why dead-node counts are target-rigid.  The new checks identify
the proof case-split: each node has `0` or `#ker(T_n)` children according to an obstruction class,
while the pooled pushforward is uniform on support (battery checks `(GR-9ii mechanism)` and
`(GR-10 mechanism)` in CELL-1/2/4).

## Row verdicts

| row | verdict | reason |
|---|---|---|
| GR-1/2, ghosts | **SUPPLY / fireable** | The final ghosts are `8`, `27,27`, and `8,64`, and leaf counts factor as ghost times image multiplicity (battery checks `(ghost)` and `(tree) leaf count`; `out_DEC5R_battery.log:44`).  The proof is landed shear congruences plus finite constant-fibre bookkeeping (`leanfinal/Uniformity/ChapH/H115c.lean:164`). |
| GR-3/3b, cofactor/Fit | **SUPPLY / fireable** | Monic division is mechanical; reverse admissibility uses the landed exact planted frame profile (`leanfinal/Uniformity/ChapH/H116b2.lean:448`).  Check `(e2)` separates root-free from merely child-free (`verification/openmath/OM2_h116b_gauge_resultant.py:528`). |
| GR-4--8, restricted Smith | **BLOCKED research core I** | Exhaustive resultants satisfy `μμ'min(k,k')`, and full lists are rigid in CELL-1/2/4, but determinant valuation does not determine the restricted truncated invariant list (`leanfinal/notes/H116B4_OUTLINE_2026-08-18.md:422`).  An explicit equal-slope/ordered-unequal-slope determinantal-ideal proof is still absent. |
| GR-9, one-level nonlinear lifting | **BLOCKED research core II-a** | The affine obstruction mechanism is now observed, but the filtration estimates and base-stability must be proved over every complete DVR.  CELL-2 also refutes nonlinear-fibre = linear-kernel *as sets*: only 27 of 81 points coincide (`out_DEC5R_battery.log:24`). |
| GR-10/11, iteration/assembly | **BLOCKED research core II-b** | The correct induction invariant is uniformity of the aggregate obstruction pushforward on its support.  The battery verifies it in all tree cells (`out_DEC5R_battery.log:49`, `:66`, `:75`), but a universal proof from the filtered Smith data is still missing.  Positivity and final assembly are mechanical afterward via landed `exists_peel_finset` (`leanfinal/Uniformity/ChapH/H116b1.lean:551`). |

## Standing fence and final status

No fibre-to-fibre replant map is proposed.  D3 refutes presentation stability, E3 refutes the
round trip, and surjectivity of that route fails for the same reason
(`blueprint/CHAP-H_general_induction.md:9634`).  The route here stays entirely in raw/image
presentation counting and filtered obstruction modules.

The numeric evidence uses exact arithmetic but only prime residue-field models; it cannot discharge
the signed all-complete-DVR quantifier (`runs/wave-b/h116b4_battery.py:28`).  Therefore the honest
node verdict remains: **research-open, numerically certified, statement unchanged**
(`leanfinal/notes/H116B4_OUTLINE_2026-08-18.md:693`).
