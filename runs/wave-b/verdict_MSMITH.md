# Verdict — unit MSMITH (H.116b4 research core I: restricted Smith identification)

Date 2026-08-26/27. Brief: runs/wave-b/brief_MSMITH.md (map row GR-4–8).
Deliverables: docs/in-progress/H116B4_SMITH_PROOF_2026-08-26.md (the proof doc),
verification/openmath/h116b4_smith_cert.py + out_h116b4_smith_cert.log (exit 0).
Signed statement untouched; fences A-H.7/F1 respected; battery/OM2 not edited.

## The identification (new, certified closed form)

For genre (L, D, N, r), group L into slope blocks a (ascending k_a, size s_a,
content D_a), t_a := Σ_{k_b>k_a}s_b. CONJECTURE C2: the truncated restricted
Smith list is

  sorted( {1}^r ∪ ⋃_a { 1 + D_a − k_a·i : t_a ≤ i < t_a+s_a } ), capped at N —

a function of (L, D, N, r) only, i.e. exactly GR-7's needed conclusion, and the
Lean-ready definition for `gaugeExponents`.

## Claim status

- PROVED — THEOREM E (equal-slope regime, cofactor included; = GR-7a/b4.15):
  the list is {1+D−k·i : i < s_μ} ∪ {1}^r, for every admissible base, every DVR.
  Complete determinantal-ideal proof (doc §6): frame normal form via a CRT span
  decomposition (root-freeness enters exactly once), lattice-valid junk clearing
  (workhorse inequality β ≥ k·deg Q̄), then both minor directions.
- PROVED — supporting chain S0–S3 (doc §§3–5): planted-lattice basis, exact
  per-scale contents/reductions, coprime multi-Sylvester unit pivot, packaging.
- PARTIAL — THEOREM U (ordered-unequal-slope; = GR-7b/b4.16): proved U1 (all
  minors ≥ assignment bound of the genre polygon pattern V), U2 (cofactor peels
  off exactly r ones), U3 (each block normalizes to pivots at precisely C2's
  rows/exponents), U4 (t = m slot exact via det = ∏Res·det(D)). Remaining gap =
  two named OPEN lemmas (doc §7): GR-7b-I (β_t(V) = C2 partial sums; pure finite
  convex/assignment combinatorics, no ring theory) and GR-7b-II (cross-block
  no-cancellation at the witness minors). Nothing else is missing.
- CERTIFIED — C1/C2 verified true-SNF == assignment-spectrum == closed-form at
  every base: exhaustive CELL-1/2/4 (91,945 bases, battery lists reproduced
  byte-equal) + 11 new cells (slope-2/3 blocks, three children, μ=3 char-2,
  deg-2 cofactors, TWO-genre cells, 6×6 and 7×7 mixes, q=5), ~700 sampled bases,
  16 genres, exact arithmetic, exit 0.
- Negative results recorded (machine-witnessed fences): slotwise-interaction
  formula refuted; per-scale pivot reading fails when deg Q̄_{k_c} > 0 (B11);
  crude junk bounds undershoot without V-inheritance (B8); optimal assignments
  are non-unique and never read off exponents slotwise (B11); empty genre at
  q=2, L={(2,1,1),(2,2,1)}, r=1, N=9.

## Handoff

Doc §8 gives the node decomposition: SM-5 (Theorem E) is transcription-ready
now; SM-6c/d are the only research nodes left in GR-4–8; SM-7 defines
gaugeExponents from signed data only. Recommended next unit: attack GR-7b-I as
a standalone combinatorics problem (its strict version feeds GR-7b-II directly).
