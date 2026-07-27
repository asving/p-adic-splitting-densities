# FABLE CONFIRMING PASS — §D4-R rev 9 (fresh instance, 2026-07-27)

Charge: (a) adjudicate the u*-recoverability disagreement (rev-8 Fable confirm
vs. rev-9 analysis); (b) verify retained-u* propagation complete/consistent;
(c) full confirming sweep of the live §D4-R (MOVES lines ~4587-5440);
(d) one fresh angle. Independence: the parallel Codex pass file
(D4R_PASS11_2026-07-27.md) was NOT read.

## A. Adjudication (duty a): REV 9 IS RIGHT; the rev-8 confirm was WRONG

Re-derivation, independent. D.3(c) (MOVES 1970): p_j(γ) = (j − t·γ)/e with
(s,t) the read's fixed Bezout pair, e·s + h·t = 1.
- e ≥ 2: t = 0 would force e·s = 1, impossible — so t ≠ 0 and
  γ = (j − e·p_j)/t from any one retained (j, p_j) pair; then
  u* = (γ − j*·h)/e (inverting γ := e·u* + j*·h, MOVES 3468). Recovery real.
- e = 1: (P2) fixes t = 0 — displayed verbatim in the source at MOVES 2646
  ("p_j(γ) = (j − tγ)/e = j (stride rule D.3(c) with t = 0, e = 1)") and
  MOVES 3477. So p_j = j for every γ: the stride map is CONSTANT in γ.
  The rev-8 confirm's inference (its file, lines 40-43: p_j are "functions of
  γ_r ... so retaining them pins γ_r") is an INVERSION ERROR — a function of
  γ pins γ only if injective in γ; at e = 1 it is constant. Anchor likewise
  γ-free at e = 1 (a = ord_z of a polynomial in positions p_j = j).
- Non-adjacent e = 1 reads: (NA)/(SAE) are strict inequalities, so u* stays
  free data; adjacent reads are vertex-pinned per §C (MOVES 3452-54).
EXPLICIT WITNESS (new, n = 3, any p): f₁ = x³ + px + p³ (root polygon
(0,3)-(1,1)-(3,0)) vs f₂ = x³ + p²x + p⁴ (polygon (0,4)-(1,2)-(3,0)).
Read side = the left side: BOTH have e = 1, h = 2, g = μ = 1, a = 0,
s₀' = 0, w' = 1, slots {0,1} with p_j = j, w = 1, right-flank composition
(2) — every u*-free retained field IDENTICAL — but u* = 1 vs 2: distinct
strata (v(c₀) = 3 vs 4) with different below-line pin depths, hence
DIFFERENT A. A u*-free P̂ would make A(P̂) ill-defined: retention is FORCED,
exactly as rev 9 concluded. Trichotomy in L3 (e ≥ 2 recover / adjacent
vertex-pin / non-adjacent e = 1 free) verified exhaustive.

## B. Propagation sweep (duty b): COMPLETE AND CONSISTENT in-section
- L3 (4707-31): u*_r retained with the recoverability display; γ_r formula
  matches §C's DERIVED list (3468) verbatim. OK.
- L9 (4954-70): constancy bracket faithful to §C C.3 (4141-44: volumes "a
  power of p determined by the history's SHAPE data") — §C's node datum
  (3443-65) carries u* as an explicit SIDE DATA field since rev 12, and
  E_fresh strips (3855-58) run between lines pinned by u*. OK.
- L11 (5075-88): u* rides in the shape part of enc′; reconstruction of the
  SIDE DATA field now complete; injectivity closes. OK.
- L8 (4943-52): finiteness quantifies over Pref(P̂) with P̂ FIXED — u* sits
  in P̂, not in the encoding product; bound M(P̂)·∏Q_r^{d_r} unaffected. OK.
- M(P̂)/m̄_r (5046-73): deg R_anch,r = w'_r/e_r is horizontal shape data,
  correctly u*-free. OK.
- Ledger split (4766-73): A consumes u* (strip depths), W does not (d_r =
  stride count) — consistent with L9 and with W's definition. OK.
- D4-R.6 pins (5321-28): γ-consistency re-derived — ν₀: γ = 1·0 + 3·1 = 3,
  line through (3,0) slope −1 hits (0,3) ✓; ν₁: γ = 1·1 + 1·3 = 4, line
  through (1,1) slope −3 hits (0,4) ✓ and u*₁ = 1 = the standing vertex
  height w(B₁) (adjacent, j* = 1 = μ₀) ✓; P̂₀: γ = 4, (4,0)→(0,4) ✓.
  No gate number changes — confirmed.
RESIDUE, cross-note (owner §M-SPECIES, NOT §D4-R): assembly note 2 still
treats P̂ as u*-free — MOVES 5938-40 ("each read carries ONE height slot
h_r ∈ ℕ as a parameter") and 5947-49 (P̂ = word + height parameters +
depths), also 6124-26 ({ε} heights). The witness pair above REFUTES that
identity as written: same letter, same h, no depths, distinct P̂ (u* 1 vs 2).
GAP-grade staleness at the L3↔SP.1 interface; SP-FIN/SP-OUT themselves
survive (the catalogue quotient forgets heights by design) but the
parameter gloss must widen to (h_r, u*_r). Also favorable staleness there:
SP-COMP/SP.5 (6072-74, 6182) still cite "§C's rev-13 (SAE) repair landing
as stated" — discharged since §C's rev-14 dual acceptance (6278).
## C. Full confirming sweep (duty c): 0 critical, 0 gaps in-section
- Header/D4-R.0/L1/L2: kernel D4R.0-K conditionality displayed at every
  consumer; branch-tree ontology consistent throughout; no completion-union
  anywhere (mandatory repair holds); L1 honestly OPEN.
- L4/L5/Thm D4R.0/L6/L7: empty-prefix base displayed at L5/L6/L12 and never
  routed through Theorem C(b); cell-vs-node distinction consistently held;
  rev-5 refuted claims remain struck, none silently restored.
- D4R.1: sum/event split sound; pointwise upgrade argument (positive-mass
  cylinder overlaps) checks; F1-instance arithmetic verified —
  (z²−3z+2)² ≡ z⁴+4z³+3z²+3z+4 (mod 5) ✓, digits of
  x⁴+20x³+75x²+375x+2500 = (4,3,3,4) ✓, A(P̂₀) = 4+6+4 = 14 ✓ (below-line
  3+2+1 re-derived), overcount 6·5^{−14} consistent.
- L11/D4R.2/reconciliation: enc′ injection order (shape → digits → s_r via
  L4 frames) sound with u* in the shape part; M(P̂*) = ⌊3/2⌋·⌊1/1⌋ = 1 ✓.
- D4R.4/L12: empty case never forms max over ∅; residue-exactness argument
  (fibers exact unions of level-N classes for N ≥ N(P̂)) checks.
- D4-R.5: statuses match rev-9 reality; the 4 pass-10 F2 cite repairs all
  present and faithful (opening 4594-98; L3 REALIZED bullet 4741-47;
  D4-R.5 STATUS 5229-34; D4-R.6 (SAE) bracket 5420-22) against the §C
  DUAL-ACCEPTED record (6278-90). Count: exactly 4, as the pass-10 record
  states.
- D4-R.6 numbers, ALL re-derived: A = 11 (9+2 and the 2/3/4-pin
  cross-check agree); W = 1·3+2·2 = 7; A_net = 4; N = 1+4 = 5;
  C(2) = 1·1·3 = 3, C(3) = 3·2·8 = 48 (N₂(p) = (p²−p)/2 ✓); predicted
  counts 3·2⁷ = 384, 3·2¹⁰ = 3072, 48·3⁴ = 3888, 48·3⁷ = 104976 ✓;
  bound checks 3·2^{−11} ≤ 2^{−4}, 48·3^{−11} ≤ 3^{−4} ✓; FC8's 20 lumps
  = 4·3·2 − 4 ✓; mult ≡ 1 argument (deg R₀ = 3 < 2g₀μ₀ = 4) ✓.
- Pass-10 record (6303-27) accurately describes the in-body state.

## D. Fresh angle (duty d): source-formula audit + constructive witness
No prior pass checked rev 9's quoted formulas against their in-file
sources. Audited: D.3(c)'s stride rule (1970), the e = 1/t = 0 display
(2646), (P2)-forces-t^B = 0 (3477 — stated there for recenterings via
e = g = 1; but (P2)'s t = 0 holds at ALL e = 1 stages per 1968, so L3's
use at e_r = 1 increments with g ≥ 2 is also covered), γ's definition
(3468), §C's rev-12 node datum with u* (3443-65), the adjacent
vertex-pin clause (3452-54), C.3's cardinalities-only volume clause
(4141-47). All faithful; no quote drift. Plus the §A witness pair
x³+px+p³ vs x³+p²x+p⁴ — the first CONCRETE non-recoverability instance
on record (prior passes argued it abstractly).

## E. Verdict
(a) ADJUDICATION: rev 9 correct — u* NOT recoverable at non-adjacent
e = 1 reads (stride map constant in γ since t^B = 0 by (P2)); the rev-8
Fable confirm's recoverable-from-strides claim was an inversion error.
Retention in P̂ is forced (else A(P̂) ill-defined; explicit witness).
(b) Propagation COMPLETE within §D4-R (L3/L9/L11/L8/M/ledger/gates all
consistent); one cross-note residue: §M-SPECIES's P̂-parameter gloss is
still u*-free (gap-grade, owner §M-SPECIES) + its stale-but-favorable
rev-13 §C cites.
(c) Sweep: 0 critical, 0 justification gaps in the live §D4-R rev 9.
(d) Fresh angle clean.
FABLE CONFIRM: §D4-R rev 9 is CLEAN. (Cross-note §M-SPECIES residue
recorded above for its own revision track — not a §D4-R defect.)
