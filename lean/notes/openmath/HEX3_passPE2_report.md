# HEX3 passPE2 report — hostile verification of HEX3_PROOF_2026-08-08.md (post-r1)

**Pass:** PE2 (second hostile pass; PE1 0C+2G+2m @ d177fd8, r1 @ 2580f12).
**Verifier:** fresh-context Fable, 2026-08-08. **Target:** HEX3_PROOF_2026-08-08.md
at HEAD after r1 (2580f12); runner + artifacts byte-frozen at seal e3f3459.
**Charges (unmined by PE1):** (1) the r1 edits — the corrected ghost-zone
pairing N−jk RE-DERIVED from the hull/scaling geometry (not just the
inequality re-checked), the honest 11-set census, the first-step-vs-telescoped
tag; (2) the β2/β3 routes pushed to full depth (PE1's lighter legs);
(3) R(M)'s derivation from W12-L0 at the M-parity boundary; (4) the HMENU3
interaction (LEMMA HM3-2 fires H-2(i) BY NAME — is the post-r1 H-2(i) what
HM3-2 needs?); (5) HEX3.B's bound chain at small N (N = 1, 2 corners).
Machine leg: pins, byte-identity, full re-run, count reconciliation, smoke
reproduction. Fresh route (differs from PE1's enumerator): polynomial-identity
leg + own W-11 block reader (R(M) direct) + own TRP enumerator on q = 8/27
rows (own field tables for F₄/F₈/F₉/F₂₇, own hull, own double-synthetic-
division multiplicity, own Taylor shift; no runner imports).

**VERDICT: NOT CLEAN — 0 CRITICAL + 1 JUSTIFICATION GAP + 1 MINOR.** Every
theorem-level claim survived; the r1 mathematical repairs (F1 pairing, m1
tag, β3 typography) are correct and were re-derived independently; the
machine leg is bit-reconciled GREEN; the fresh route confirms the law,
the species table, and R(M) at both parities, including a NEVER-MEASURED
q = 27 row. The gap: the r1-corrected "honest 11-set" census is ITSELF
miscounted — the genuinely never-measured set has TWELVE pairs; (8,3)
(whole-space 32,768 = 8⁵) is omitted, by verbatim inheritance of PE1-F2's
own census. The minor: the r1-m2 repair of S8.2 left the main line's
"exact N-linear mass" formula inconsistent with its own bracketed re-check
(1024 vs 960 at (2,7)).

---

## F1 [JUSTIFICATION GAP, bookkeeping] — the r1 "honest 11-set" is still not the honest set: the never-measured census has TWELVE pairs; (8,3) is omitted

Quote (S7 P-1, [r1] bracket): "The honest 11-set of (q,N) pairs first
measured by the sealed battery, with whole-space values: (2,8): 50,176;
(2,9): 206,336; (3,5): 23,571; (3,6): 240,327; (4,4): 18,688; (4,5):
308,224; (5,4): 88,125; (9,3): 59,049; (11,3): 161,051; (13,2): 2,197;
(13,3): 371,293."

Census re-derived from the frozen sources: the roster carries **29 distinct
(q,N) pairs** (21 ℤ_p + 25 𝔽_q[[t]] rows, 17 shared pairs; 46 − 17 = 29 ✓).
Measured before the seal: the committed w12 cubic table (23 rows, extracted
from the pinned `w12_checks_results.json`, md5 0577…) covers 14 pairs
{(2,3..7), (3,2..4), (4,2), (4,3), (5,2), (7,2), (8,2), (9,2)}; the
disclosed /tmp prototype (18 rows, docstring) adds {(5,3), (7,3), (11,2)};
the pre-seal `--smoke` rows (SMOKE_ZP/SMOKE_FQT in the frozen runner, 12
rows) are all inside that union. Total previously measured: **17 pairs**.
29 − 17 = **TWELVE never-measured pairs**:

    {(2,8), (2,9), (3,5), (3,6), (4,4), (4,5), (5,4),
     (8,3), (9,3), (11,3), (13,2), (13,3)}

**(8,3) — Fqt only, whole-space 32,768 = 8⁵ — is missing from the r1
list.** It qualifies under r1's own standard exactly as (13,2) and (9,3)
do: q = 8 exists in the corpus only at N = 2 (w12 cubic + l0hist tables
checked directly: q ∈ {8,9} appear at N = 2 only); (8,3) is in no
prototype/smoke list; GENIND (seal 10:16Z), QSCOUT22 (verdict 10:00Z) and
HMENU3 (seal 08:40Z) all post-date the HEX3 seal (06:39:44Z), so nothing
else decontaminates it; and like (13,2) "its value rode the blanket 46-row
law prediction only" — r1 added (13,2) on precisely that basis. Note (9,3)
sits in the r1 list although (9,2) was w12-measured, so the per-(q,N)-pair
semantics is the note's own.

Root cause: PE1's F2 census itself omitted (8,3) (its report displays the
same 11-element set), and r1 transcribed PE1's set verbatim — the
extraction-inheritance trap. Affected sites (all downstream of one census):
S1 header ("11 (q, N) pairs NEVER measured before this unit"), S1 anchors
paragraph ("the battery's force is the 11 never-measured (q, N) pairs"),
S7 P-1 [r1] bracket, S10 P-1 [r1] bracket. The runner docstring is frozen
with the OLD 12-entry list (disclosed); the honest count happens to also be
twelve, but as a DIFFERENT set (swap (5,3),(7,3) out, (8,3),(13,2) in).
Impact: evidential-force bookkeeping only — every value in every list hit
the law exactly, and this pass measured (8,3) with a fully independent
enumerator: 32,768 on the nose (fresh route leg C). No mathematical content
is touched. Repair: 11 → 12 with (8,3): 32,768 inserted, at the four
note sites.

## m1 [MINOR] — S8.2 item 2 (r1-m2 repair): the main line's "exact N-linear mass" disagrees with its own [r1] re-check; the correction factor is misattributed to k ≥ 2 terms

Quote (S8.2 item 2, post-r1): "the exact N-linear mass of U₃^conv is
⌊(N−4)/2⌋(q−1)²q^{2N−4} (+ smaller k ≥ 2 terms)" — and, same sentence,
"[r1, PE1 m2: … re-checked at (2,7): whole-space N-linear mass
⌊3/2⌋(q−1)²q^{10}(1 − q^{−4}) = 960 exactly]".

Re-derivation: the k = 1 term's floor-bearing part per center is
(q−1)q³(q^{M}−1)·⌊(M−1)/2⌋(q−1)q^{M−2} with M = N−3, i.e. whole-space
⌊(N−4)/2⌋(q−1)²·(q^{2N−4} − q^{N−1}) — the main-line formula times
(1 − q^{−(N−3)}). At (2,7) the main line gives 1024, the bracket (and the
truth) 960; the −q^{N−1} correction is a k = 1 term, not a "k ≥ 2 term",
so the parenthetical attribution is wrong and the word "exact" is false as
displayed while the bracket's arithmetic is right — one sentence carrying
two values for the same named quantity. The Θ-claims and the corrected
relative rate Θ(N/q) (the substance of PE1's m2) are unaffected; aside-
grade, explicitly corroboration prose, no consumer cites it. Repair: put
the (1 − q^{−(N−3)}) factor (or the −q^{N−1} term) into the main formula,
or demote "exact" to "leading".

---

## Charge-by-charge record

**(1) The r1 edits — pairing RE-DERIVED, tag verified, census fails (F1).**
* *Ghost-zone pairing from the geometry (not the inequality):* under σ_k the
  coefficient at hull abscissa j is B_j/π^{(3−j)k} retained mod π^{N−3k},
  so the retained window of B_j is (N−3k) + (3−j)k = **N − jk** — the ghost
  zone at abscissa j is {≥ N−jk}, independently re-derived (B₂ = abscissa
  2 ↔ {≥ N−2k}, B₁ = abscissa 1 ↔ {≥ N−k} ✓ the r1 pairing, and uniformly:
  knowing B_j mod π^{N−jk} for all j determines the FULL window-M scaled
  state). Consulted heights: convexity from (0, u₀ ≤ N−1) to (3,0) bounds
  hull heights at abscissa j by (3−j)(N−1)/3; the corrected inequality
  (3−j)(N−1)/3 < N−jk re-proved: j = 2 ⟺ k < (2N+1)/6 (true, k ≤ (2N−2)/6);
  j = 1 ⟺ k < (N+2)/3 (true, k ≤ (N−1)/3, margin exactly 1 at N ≡ 1 mod 3,
  strict). The point-above-chord dichotomy for ghost-range v(B₁), v(B₂) and
  the shift3 update congruences (v(s) ≥ k+1 chain-wide) re-checked as
  displayed. r1's corner spot-checks (7,2): j = 1: 4 < 5, j = 2: 2 < 3 ✓;
  the r1 bracket's history claims match d177fd8's text.
* *First-step-vs-telescoped tag (r1-m1):* both decompositions re-computed:
  first-step 8·[u(4)+15·R(4)−2⁶] = 8·188 = 1504, 64·[u(1)+1·R(1)−1] = 64;
  telescoped (q−1)q³(q⁴−1)R(4) = 8·15·12 = 1440, (q−1)q⁷(q−1)R(1) = 128;
  both + 4096 = 5664 ✓; the tag's claim (anchor decomposes by first-step
  form under the telescoped display) is accurate. β3 typography fix:
  t + j = t + (u₀−3t)/2 = (u₀−t)/2 ✓.
* *Census:* FINDING F1 above.

**(2) β2/β3 routes — re-derived to full depth; CONFIRMED.**
* *β2 (VERT1(u₀,k), m = k):* hull (0,u₀),(1,2k),(3,0) with 3k < u₀ ≤ N−1;
  locus slot-count re-derived = (q−1)²q^{3N−3−u₀−3k} (letters u₀-digit + z;
  pins −2z, z²; free counts (N−1−u₀)+(N−1−2k)+(N−1−k)). m-choice: split
  root pre-depth u₀−2k > k ⟹ post-recentering depth exactly k ✓; the unit
  root r̃ = r/π^k − ẑ has v(r̃+ẑ) = u₀−3k = w exactly ⟹ w-fiber
  (q−1)q^{M−1−w}, and the u₀-fibers (w = 1..M−1) tile the residue-(−z)
  pattern slice minus the single degenerate r̃ = −ẑ (which needs u₀ ≥ N):
  Σ(q−1)q^{M−1−w} = q^{M−1}−1 ✓. **Cardinality identity exact:**
  (q−1)[z]·(q−1)q^{M−1−w}[r̃]·q^{2M−2}[blocks]·q^{3k}[ghosts] =
  (q−1)²q^{3N−3−u₀−3k} = locus ✓ (exponent algebra checked). Drained
  (q−1)²q^{3k+M−1−w}R(M) ✓; u₀-sum (q−1)q^{3k}R(M)(q^{M−1}−1) ✓.
* *β3 (VERT2(u₀,t), m = t):* hull (0,u₀),(2,t),(3,0), u₀ > 3t, u₀ ≡ t (2);
  vertex condition t < u₀/3 ⟺ u₀ > 3t re-derived; locus re-derived incl.
  the DETERMINED B₀-digit z²λ (≠ 0 forces v(B₀) = u₀ exact) and the char-2
  degeneration (−2zλ = 0 ⟹ the pinned B₁ digit is 0 — count unchanged).
  Split root at depth t BELOW the cluster (right side (2,t)–(3,0) width 1);
  scaling by π^t puts the block at its depth-j refine locus, j = (u₀−3t)/2
  = k − t ≥ 1, with j ≤ (M−1)/2 ✓ (matches W12-L0's refine range).
  **Cardinality identity exact:** (q−1)q^{M−1}[λ,r̃]·(q−1)q^{2M−2−3j}
  [block z-slice]·q^{3t}[ghosts]: exponent 3M−3−3j+3t = 3N−3−6t−3j =
  3N−3−u₀−t−(u₀+t)/2 at u₀ = 3t+2j ✓ = locus. Drained
  (q−1)²q^{3t+M−1+j}R(M−2j) ✓; the u₀-sum via the R-recursion
  (q−1)Σ_j q^jR(M−2j) = R(M)−q^{M−1} ✓.
* *Assembly bracket:* (q−2)q^{M−1}R + (q^{M−1}−1)R + q^{M−1}R = (q^M−1)R ✓;
  the −q^{2M−2} is β3's sum-head ✓. All five preregistered P-2 spot values
  re-derived by hand from the closed forms: (Zp,2,7) VERT1(4,1) =
  (2048,384), VERT1(6,1) = (512,96), VERT2(5,1) = (512,256), ALPHA(1)/(2);
  (Zp,3,6) FULL11SQ(1) = (39366,7290), VERT2(5,1) = (2916,2916) fully
  drained (M−2j = 1, locus = drained ✓); (Zp,2,9) VERT1(8,2) = (1024,384),
  VERT2(8,2) = (512,512); (Fqt,4,4) both keys — every value matches S5.1,
  the note, and (independently) the fresh-route enumerator.
* *β-chain coherence:* the first β-recentering has v(s) = m (not m+1), but
  it consumes only depth-0 full-window data; the POST-node chain has
  v(s) ≥ m+1 as H-3 states; scaled coordinates all retained mod π^M
  (uniform, from the N−jm windows) — the H-2(i) mechanism transfers as
  claimed.

**(3) R(M) from W12-L0 at the M-parity boundary — CONFIRMED, both
parities, three independent ways.**
* *From W12-L0 (statement read at pin, W12 S2.6):* the A₀ = 0 leaves are
  SPLIT-TAIL(w)@H ((q−1)q^{M−1−w}, s+1 ≤ w ≤ ⌊(M−1)/2⌋) and UNDECIDED@H
  (q^{M−1−⌊(M−1)/2⌋}). UNDECIDED sum over H = q^{M−1} (L0's own consistency
  display, re-derived); SPLIT-TAIL sum: Σ_{w=1}^{⌊(M−1)/2⌋} (q−1)q^{M−1−w}
  ·[Σ_{H: k_t ≤ w−1}(q−1)^t = q^{w−1}] = ⌊(M−1)/2⌋(q−1)q^{M−2} — each
  w-term is w-independent, exactly S4's display. **The parity boundary:**
  at even M the states A₀ = 0, v(A₁) = M/2 (the 2w = M chord-touching
  configuration, no genuine split vertex) satisfy v(A₁) = ⌊(M−1)/2⌋ + 1,
  so they sit inside UNDECIDED@H's range v(A₁) ≥ M+1-floor — counted ONCE,
  in the q^{M−1} aggregate, not as a SPLIT-TAIL family; at odd M the
  w = (M−1)/2 family exists and UNDECIDED starts one deeper. No overlap,
  no gap, either parity; the floor term is carried by W12-L0's own range
  bound, and R's total is boundary-robust (both exits drain).
* *Machine (fresh):* own W-11 block reader (written from the polygon
  geometry, not from w11 code), R(M) by direct enumeration: 39 cases,
  M = 2..8 at q = 2, M = 2..6 at q = 3 (both ring types), M = 2..4/5 at
  q = 5/4, M = 2..3 at q = 8, 9, M = 2 at q = 27 — every value equals
  q^{M−1} + ⌊(M−1)/2⌋(q−1)q^{M−2}, even and odd M alike. (The sealed
  battery's T-FLOOR tooth — ⌊(M−1)/2⌋ → ⌊M/2⌋ — fired at exactly its 10
  preregistered rows on the re-run, killing the parity mis-read a third
  way.)
* *R-recursion:* R(M) = q^{M−1} + (q−1)Σ_{2j≤M−1} q^jR(M−2j) re-verified
  exactly at M ≤ 8 across q ∈ {2,3,5} and consistently with the β3 sum.

**(4) HMENU3 interaction — COMPATIBLE; the r2 fired-clause record is
accurate.** HMENU3 §S3.1 (LEMMA HM3-2) fires "HEX3 H-2(i) (window
coherence)" for the clause "every digit consulted by the chain of X lies
strictly below the ghost zones — so the chain, not merely its drain
verdict, is a function of σ_k(X)". That is exactly the PROOF-BODY content
r1 repaired (the corrected pairing is what makes "consulted digits below
ghost zones" true at the k = ⌊(N−1)/3⌋ corner), and the post-r1 H-2(i)
supplies it verbatim; HM3-2 additionally consumes H-2(ii)'s statement
(chains correspond step for step, residual coefficient positions
preserved — chain-level, key-resolution capable) and H-2(iii)'s bijection,
both untouched by r1. Remark (no finding): H-2(i)'s BOXED statement is
verdict-scoped while HM3-2 cites the proof mechanism; HMENU3 flags this
itself ("what is new here is only reading the correspondence at KEY
resolution") and its r2 fired-clause record at BOX-2 correctly states the
consumed conclusion survived PE1's gap with the display fixed at 2580f12.
HMENU3's HM3-1(iii) (β flips the phase once) was also read against H-3's
m-constancy claim — consistent.

**(5) HEX3.B at small N — HOLDS degenerately, all corners.**
* N = 2: u = q² (empty k-sum, S2 partition = B0ZERO + DEC only re-checked:
  no refine species exist below N = 4); q² ≤ q²(1+1/(q+1)) ≤ 2q² ✓;
  q^N ≤ U₃^σ: LEMMA W12-S3.2's constructed lifts re-read at pin — the
  construction (2K+1 ≥ max(N, 2t+2), L ≥ 3N, t ∈ [1, N−1] ∪ {≥N}) has NO
  lower N restriction and its count q·q^{N−1} = q² is valid at N = 2 ✓;
  N·q^{2N−1} ≤ q^{3N−2} ⟺ 2 ≤ q at N = 2 (tight at q = 2, true) ✓;
  undecided/q^{3N} ≤ (1+N)q^{−N}: (q−1+N)q^{2N−1} ≤ (1+N)q^{2N} ⟺
  N−1 ≤ qN ✓ all N ≥ 2.
* N = 1: correctly EXCLUDED from B (stated N ≥ 2); A's N ≥ 1 claim checked:
  u(1) = 1 = the single zero state (BOX-5 seed), empty sum, R(1) = 1 pinned
  separately (the closed form's q^{M−2} at M = 1 never fires: floor
  coefficient 0) ✓; the S5.3 chain's (N−2)/2 factor vanishes at N = 2
  (sum empty ⟹ bound trivially exact) ✓; R(M) ≤ q^{M−1}(M+1)/2 ⟺ M ≥ 1
  re-checked, and the S5.3 exponent algebra (4k−2+2M = 2N−2k−2) exact.
* 3k = N−1 corner (N ≡ 1 mod 3): the empty β2/β3 sums self-vanish via
  (q^{M−1}−1) = 0 and (R(M)−q^{M−1}) = 0 at M = 1 ✓ (re-checked at the
  u(2,7) k = 2 term: 64·[1+1−1] = 64).

## Machine leg (this pass)

* PINS: all four md5 pins re-hashed and MATCH (w12_checks.py 7dc0…,
  w11_checks.py 500a…, w10_checks.py a9c3…, w12 JSON 0577…).
* Runner byte-identical to seal e3f3459 (`git show` md5 == working-tree
  md5 == 83faf7ed…, the r1-commit-recorded value).
* FULL RE-RUN (single fresh run): exit 0, GREEN, 330.0 s. **158,512 checks
  / 0 violations**: PIN 4, LAW 92, SPECIES 172, XREAD 158,204, W12TIE 23,
  CHAR 17 — every count equal to §S10's; teeth fired 10/20/13 ==
  preregistered (fire-row sets re-derived: T-FLOOR = rows with some N−3k
  even = N ∈ {5,7,8,9} = 10; T-ALPHA = N ≥ 4 = 20; T-VERT1 = N ≥ 5 = 13);
  46/46 rows, 67,410,225 states (JSON-summed); XREAD roster sum re-derived
  by hand (77,500 ℤ_p + 80,704 𝔽_q[[t]]). Fresh JSON identical to committed
  ex elapsed_s; artifacts restored (md5s 6e4b…/ce6f… == §S10's display).
* SMOKE REPRODUCTION: `--smoke` re-run reproduces S7's disclosed record to
  the digit (PIN 4, LAW 24, SPECIES 30, XREAD 26,730, W12TIE 12, CHAR 4,
  teeth 1/4/1, GREEN 0.4 s), and all six figures were re-derived by hand
  from the smoke rosters before running.

## Fresh route (no runner imports; /tmp/hex3_pe2_fresh.py)

Different angle from PE1's (which enumerated small rows with its own
reader): polynomial-identity algebra + block-level R + deep/new prime
powers with own finite-field arithmetic (F₄/F₈/F₉/F₂₇ built from scratch
via irreducible-polynomial tables; own lower hull; own repeated-root test
by double synthetic division — char-free; own quadratic/cubic Taylor
shifts; own law transcription).
* leg A: first-step recursion == telescoped closed form as POLYNOMIALS in
  q for N ≤ 40 (exact evaluation at 100 integer points, degree ≤ 78 —
  a rigorous identity proof); the S5.2 telescoping coefficient identity
  (q−1)q^{3l} + (q−1)²Σ_{k<l}q^{3k+4(l−k)−1} = (q−1)q^{4l−1} for l ≤ 12;
  the GF denominator identity 1−A = (1−q⁴x³)/(1−q³x³). All OK.
* leg B: R(M) by own block-chain enumeration, 39 cases (see charge 3):
  0 mismatches — the M-parity boundary independently machine-verified.
* leg C: own TRP enumeration, 6 rows: **(Fqt,8,3): u = 4096, U₃ = 32,768**
  (the F1 row, measured here independently); **(Fqt,27,2): u = 729, U₃ =
  19,683 = 27³ — a (q,N) pair measured by NO battery in the corpus,
  first-ever q = 27/char-3 instance of the law, predicted exactly**;
  (Fqt,4,4) 18,688; (Fqt,9,3) 59,049; (Zp,5,4) 88,125; (Zp,2,7) 11,328 —
  all == law, all species tables == the S5.1 closed forms BOTH directions,
  and all five roster rows' per-key tallies == the committed JSON exactly
  (key-by-key equality, locus and drained).

## Disposition

0 CRITICAL. The theorems and all r1 mathematical repairs stand; the machine
and fresh legs are clean, including at rows this arc never touched before.
Repair owed on F1 (the never-measured census: 11 → 12 pairs, insert
(8,3): 32,768, at S1 ×2 / S7 P-1 / S10 P-1 — note-only) and m1 (one-line
S8.2 aside fix). Counter stays 0/2 per protocol; findings trigger repair;
PE3 next.
