# Blueprint — formalizing the closed wild-regime-1 math in Lean (2026-07-13)

Detailed plan (Plan-agent survey + cross-checks; blueprint-first per Asvin's rule) for turning the
now-closed deep-wild argument into Lean. Save-and-formalize-Phase-1 reference.

## Executive point (understand first)
- **p-uniformity is ALREADY structural, not a theorem to prove.** `RatFn.IsRationalFn f` (RatFn.lean:30)
  = ONE num/den ∈ ℚ[t] with f q = num/den for EVERY q>1. "Same R(q) at all primes" IS the conclusion
  shape, already delivered by the engine.
- **Engine DONE, sorry-free, core-only:** `OMInduction.clusterVol_isRational` (OMInduction.lean:34) —
  given the well-founded cell recursion + rational per-cell coeffs + pole-free pivot ⟹ IsRationalFn.
- The deep-wild math only supplies the *hypotheses* of that recursion. Most are DONE:
  fixpoint (SelfLoopFixpoint(GeneralMu)), L3 char-indep counts (L3Squarefree/L3Gauss/Necklace/
  ShapeCountTie), φ-adic development bijection (Development.developEquiv + develop_map), sparse/cross
  resultant closed forms (SparseResultant.resultant_sparseTwist{,_cross}), two-/k-block product law in
  the UNIFORM margin (BlockProduct.pair_card/blocks_card), assembly to Goal (Goal.goal_theorem).

## What's genuinely NEW + formalizable WITHOUT the measure wall (= what to build)
**Phase 1 (self-contained win, ~days, LOW risk):** fine-cell resultant-valuation constancy.
- **NEW-1** `vResultant_eq_sum_cross_pairs`: over a valuation/DVR with monic split Gi,Gj,
  `v(resultant Gi Gj) = Σ_{θi∈roots Gi, θj∈roots Gj} v(θi − θj)`. Build on mathlib
  `Polynomial.resultant_eq_prod_eval`/`resultant_eq_prod_roots_sub` (already used SparseResultant.lean:155)
  + `Valuation.map_prod`/`map_sub`. Difficulty LOW-MEDIUM (resultant API over K̄ + valuation plumbing).
- **NEW-2** constancy per fine cell: exhibit the realized fine cells (n=6 [2,4], n=8, n=9) as
  sparse-twist families; the constant exponent Σ m_i m_j w_ij IS `SparseResultant.resultant_sparseTwist`
  (same-side, d_i d_j e h) / `_cross` (cross-side, d_i d_j e_j h_i), ALREADY PROVED. NEW-2 = packaging
  (mostly wiring proved lemmas). Difficulty LOW. **Use the level-N zmodValuation route** (compatible with
  BlockProduct/ProductTheorem's `zmodValuation_mul`), not the abstract-K̄ route, to stay wired to the engine.

**Phase 2 (bookkeeping, optional, LOW):** explicit Q(t) fine-cell closed forms.
- **NEW-3** e.g. the n=6 [2,4] child-type proportion = (q²+q+1)/(2q⁴+2q³+q²+3q+1) via `omChildCount`
  instantiation + RatFn norm_num/ring (cf. the μ=3=20/31 computation in SelfLoopFixpointGeneralMu:121).
  char-independence itself is DONE (ShapeCountTie.shapeCount_tie_general + L3). Illustrative.
- (c) p-independence assembly: ALREADY DONE by clusterVol_isRational (listSum of IsRationalFn coeffs ×
  ∏ IsRationalFn children / pole-free pivot). No new lemma; optionally a worked concrete-Shape instance.

## MEASURE WALL (stays axiomatic — mathlib has NO p-adic Haar)
- `PadicMeasure.clusterMeasure` (:405), `AX_cellRecursion` (:438) = the Haar-Jacobian = volume
  identification (that q^{−Σ m_i m_j w_ij} IS the Haar Jacobian of the block change-of-variables). The
  combinatorial EXPONENT is formalizable (NEW-1/2, D3/D4); the measure-TRANSPORT is the wall.
- count-native: `MontesAxiom.MontesData.nodeMeasure_boxSum` (un-constructed field; its arithmetic
  `clusterCount_boxSum` is proved). GMN structural axioms: `omCells`,`descend`,`descend_size_lt`.
- **What formalization ADDS over clusterVol_isRational:** NOT p-uniformity (already structural). It
  proves the block-factorization exponent inside AX_cellRecursion's coeff is a genuine CONSTANT lattice
  integer from Newton data (not p-varying) — shrinking the axiom toward exactly the un-formalizable Haar
  CoV, with all algebra around it proved.

## OPEN formalizable-but-hard (Phase 3, weeks, MEDIUM-HIGH, currently a NAMED OBLIGATION)
- **D9**: the deep-wild GRADED (per-slot) margin block-fiber count — `ProductTheorem.obligation_hensel_surjective`
  (:889), where the uniform margin 2c<N provably FAILS (BlockProduct.gate_margin_A/B/C:496). Needs a
  Newton-graded level-N Hensel iteration (RESTART_FORMALIZATION_BLUEPRINT F-B2). Numerically gated, NOT
  proven — a Lean formalization here inherits that gap. Do NOT present as near-term.

## CAUTIONS (carry into Lean)
1. **Do NOT formalize the A:B within-child split** (GAP1_RESIDUAL §4): not closed (no clean single
   fraction), but NON-load-bearing (cancels in the conditional child law). Target child-type proportions.
2. **Keep to the fixpoint-ALGEBRA shape** (SelfLoopFixpoint B3/B4, proved). Do NOT claim the fixpoint
   value = the actual census for general μ (the k≥2 census induction / general-μ EFFSEED is numerically
   confirmed, NOT proven — SelfLoopResum.REMAINING_OBLIGATION item 2).

## Phasing
Phase 1 → Phase 2 = the clean self-contained core-only win (~few hundred lines, leaf modules). Phase 3
= the open weeks-scale Hensel rung (inherits gap). Phase 4 (Haar identification) = not formalizable.
Refines notes/RESTART_FORMALIZATION_BLUEPRINT.md F-B for the deep-wild frontier.
