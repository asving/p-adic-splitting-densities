# FABLE CONFIRMING VERIFIER — §S-RESUM rev 5 (fresh instance, 2026-07-27)

Charge: (a) verify the (SCS) DERIVATION independently (walk the
flank-fills-the-window argument against SP.1 + (B1)/(B3); attempt to
BREAK it); (b) bracket sync complete (sweep for stale (K-SUB)
brackets); (c) one own-construction check. Text: live MOVES §S-RESUM
(K-SUB)/(SCS) block (11743–11821) + pass-5 record (12761–75).
Quote-and-classify only. Dual shot: a Codex pass runs in parallel.

## A. The (SCS) derivation — independent walk + break attempts: HOLDS

Walked steps (1)-(3) against the sources myself. (1) Trichotomy: all
roster quotes verbatim (DEG-CONS 8387-88 "m ≥ 2 children"; V.6.1 8820
"m_2+1: (2,1) ✓ ... single-child (m = 1"; V.6.3 8928 "m_vv (1,1) ✓;
o_double single child size 2"). (2) SP.1 flank field verbatim (5950-52);
with (G1) FLANK-SPAN (6062-64: left span = s₀′, s₀′ + w′ + right = W,
each flank a composition — parts ≥ 1), any s₀′ > 0 or right span > 0
yields ≥ 1 flank member, and V.6's executed (2,1)/(1,1) checks type
flank clusters as members; non-selected λ factors are members (SP.1
co-factor clause). So m = 1 forces s₀′ = 0, e·ℓ = W, λ = {(g,μ)},
g·μ = ℓ. (3) (B1) 6114-15 and (B3) 6120-23 verbatim; the algebra
W′·D′ = μ·e·g·D = e·(gμ)·D = e·ℓ·D = W·D is exact; the root case
(W = n, D = 1) + entrance typing (8798-8800, quotes verbatim) close the
cluster-size = W·D recursion. Owners' status verified: §M-SPECIES
DUAL-ACCEPTED (9875), §V-TABLES DUAL-ACCEPTED (9277) — as claimed.
BREAK ATTEMPTS (all fail on forced grounds): (B-1) m = 1 with flank not
filling window — needs an empty composition of a positive span,
excluded by (G1). (B-2) m = 1 with an uncounted non-selected factor —
excluded: τ-halted tracks are members (trichotomy source, V.6.1).
(B-3) same W·D but different block — block size IS W·D (recursion
above). (B-4) window-shrinking non-branching read: e = g = 1, μ < W
with m = 1 forces μ = ℓ = W, contradiction — SP-DAG (ii)'s second
rank bullet (6445-46) is exactly this edge, inside an m ≥ 2 outcome;
fence faithful. (B-5) m = 0 escape: ℓ ≥ 1 ⟹ λ ≠ ∅ ⟹ m ≥ 1.
W1 (WATCH, citation): step (2) licenses flank-members via the READ-side
identity quote "Σᵢ g⁽ⁱ⁾·μ⁽ⁱ⁾ = ℓ" — a transplant; the direct license
is (G1) + the roster member typing (both available). Conclusion forced.
W2 (WATCH, display): "cluster size IS the stage product W·D" is cited
via [1v] instances + recursion, not one displayed general identity;
fully grounded but a one-line [1v] display would close it verbatim.

## B. Bracket sync sweep: COMPLETE

S.6 perimeter (12223) now reads "+ the (SCS) single-child size clause
(rev 5: DERIVED ...)" — rev-4's G1 closed. Swept every DEG-CONS/K-SUB
site in MOVES + all notes/docs: the conditionality sentence (11765-71)
and S.6 agree; STATUS line 12362 names no givens (not a bracket);
12534 and the FABLE/SRES pass files are historical records (exempt).
No stale bracket found.

## C. Own-construction check (/tmp/sres_rev5_check.py): ALL PASS

Exhaustive shape enumeration, n ≤ 6: stage (D, W) with W·D ≤ n, side
(e, ℓ, s₀′) under (B3), flank compositions per (G1), λ multisets with
Σgμ = ℓ, members = flank parts + λ factors. 571 outcome shapes, 39
m = 1 continuing, 422 fence-case edges. Check 1 (SCS): 0 violations
(every m = 1 continuing child lands in block W·D). Check 2 (fence):
0 (every e = g = 1, μ < W edge sits in an m ≥ 2 outcome). Check 3:
member sizes (flank part·D, factor e·g·μ·D) sum to W·D EXACTLY in all
571 — DEG-CONS's Σ e_j ≤ e holds with equality in the shape model,
matching V.6.1's (2,1) → 3 and V.6.3's rosters.

## Verdict

The rev-5 resolution is GENUINE: (SCS) is a derivation over
dual-accepted displays, not a hypothesis; the pass-5 critical (the
unlicensed m = 1-branching dispatch) is gone — the size-dropping
single child is now IMPOSSIBLE by (2)+(3), not re-typed. All five
break attempts fail; bracket sync complete; own-construction 3/3.
Counts: 0 critical, 0 gaps, 2 WATCH (W1 transplant citation, W2
instance-cited identity). CLEAN.
