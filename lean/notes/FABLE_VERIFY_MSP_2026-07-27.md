# FABLE FRESH-INSTANCE VERIFICATION — §M-SPECIES rev 6 (2026-07-27)

Verifier: fresh Fable instance (dual bar, Fable half; Codex passes 4+5 already CLEAN
on rev 5; rev 6 = the CASE_MN3_V2 PASS record only). Text: MOVES_2026-07-24.md
lines 5864–6969 (§M-SPECIES body + rev records). Inputs consulted: §B2-DEF (D.3–D.10),
§D4-R L3 (rev 9), §T-ASSEMBLY T.1 (VP), verification/CASE_MN3_V2_SEALED_PREDICTIONS.md.

## Skeleton (duties → sections)
- S1 Quote-and-classify sweep (full note) .................. [filled below]
- S2 Coordinate systems: shift-map re-derivation + break attempts
- S3 Independent 53-letter recount (groups R, Q2 + full (G5) closure)
- S4 Three non-diagnosed N*_3 re-derivations vs (I-aug)
- S5 Own-emphasis: SP-DAG rank, n=1 (τ-hen) vs VP, SP-FIN encoding
- S6 Findings list + verdict

## S2 — Coordinate systems (hardest duty): re-derivation + break attempts
INTEGRALITY, re-derived from Bezout alone: pin e·s + t·h = 1, gcd(e,h) = 1; left
endpoint (s0', u0) on the side line gives gamma = e·u0 + s0'·h. Then t·gamma =
t·e·u0 + (t·h)·s0' == (1 - e·s)·s0' == s0' (mod e), so t·gamma mod e = s0' mod e and
sigma := floor(t·gamma/e) = (t·gamma - (s0' mod e))/e is an INTEGER — matches (SH).
Then p_{j_k} + sigma = (j_k - (s0' mod e))/e = floor(s0'/e) + k = p-hat_k; k = 0 is
the anchor identity. VERIFIED, including negative t (floor semantics: checked the
note's (s,t) = (1,-1) rerun, sigma = -2, same census image) and the Bezout-shift law
t -> t + e·m => p_j -> p_j - m·gamma, sigma -> sigma + m·gamma, census invariant.
Independent numeric probe (mine, not the note's): e=2, h=3, (s,t)=(-1,1), side from
(1,4), ell=1: gamma = 11, sigma = 5, geometric slots {-5,-4} -> census {0,1}, a = 0
= -5 + 5. All identities exact.
BREAK ATTEMPTS (all failed):
 (i) Ambiguous preimage: recovery needs gamma = e·u* + j*·h with j* = the RIGHT
     endpoint (D4-R L3 rev 9: u*_r is "the right-endpoint height"); j* = s0' + w'
     is a function of retained fields, t is the stage's pin — so Sh^{-1} is
     deterministic per realized read. Same-letter reads with different (h,u*) map
     to different geometric data through their OWN (t,gamma): quotient, not loss.
     Left-vs-right endpoint consistency: e·u0 + s0'h = e·uR + (s0'+w')h since
     u0 = uR + (w'/e)h — the note's u0-based proof and L3's j* agree. NO BREAK.
 (ii) R_anch shift-invariance: R = sum_k c_{j_k} z^{p_{j_k}}, p_{j_k} = a^geo + k,
     left endpoint a vertex => c_{j_0} != 0 => ord_z R = a^geo; anchoring gives
     sum_k c_{j_k} z^k in both displays — identical polynomial, so lambda/sel/ell
     system-independent. NO BREAK.
 (iii) G-relation transport: (G1)/(G4)/(G5)/(G6) mention no position; (G2)/(G3)
     equivalences follow from a = a^geo + sigma exactly as displayed. Checked the
     note's (1,1)-(3,0) example line by line (both saturated bounds, both Bezout
     representatives): all correct. NO BREAK.

## S3 — Independent recount of the 53 (groups R and Q2 from (G1)-(G6) directly)
GROUP R, stage (1,1,3): enumerate (e,ell,s0') with s0' + e·ell <= 3: e=1: (1,0),(1,1),
(1,2),(2,0),(2,1),(3,0); e=2: (1,0),(1,1); e=3: (1,0). lambda-sel counts: ell=1: 1;
ell=2: 3 ({(2,1)},{(1,2)},{(1,1)^2} — one sel each, sel is a shape pair, index s_r
excluded); ell=3: 7 (partitions {(3,1)},{(1,3)},{(1,1)^3}: 1 sel; {(2,1),(1,1)},
{(1,2),(1,1)}: 2 sels). Flanks: compositions, 2^{m-1} per span m>=1, 1 empty.
Rows: 1x2 + 1x1 + 1x2 + 3x1 + 3x1 + 7x1 + 1 + 1 + 1 = 21. MATCHES R1-R8 exactly.
GROUP Q2, stage (1,1,2): e=1: (1,0),(1,1),(2,0); e=2: (1,0). Counts 1+1+3+1 = 6.
MATCHES Q2.1-Q2.4. (G5) CLOSURE recount: root sels generate exactly Q1/(1,1,1),
Q2/(1,1,2), Q3/(1,1,3), I(2,2) via sel(2,1), I(3,3) via sel(3,1), I(2,1) via e=2,
I(3,1) via e=3; Q2/Q3 add nothing new; POST-INC W>=2 impossible at n=3 (mu>=2 and
e·g>=2 force g·mu <= ell <= 3/e: contradiction in all cases — note's argument
verified). W=1 stages: 1 letter each by (G6)+(B3). Total 21+21+6+1+4 = 53 CONFIRMED.
MISSING-TUPLE HUNT: unreachable-stage probes (POST-REC (2,1,1): needs a D=2 parent
with a selection, but all D=2 stages have W=1, terminal; (D,w)=(2,3): w ∤ D as noted)
all die at (G5); no coherent reachable tuple absent from the display. NONE FOUND.

## S4 — Three NON-diagnosed N*_3 thresholds re-derived from (I-aug) (vs V2 seal S1)
Conventions taken from the seal: slope-0 recentering entrance => child slopes > 0;
DECIDED includes the retained height pair (h,u*), so a READ-side endpoint height
must be EXACT (height h exact needs N >= h+1); a capped flank slot stays undecided
whenever completions can change the side structure.
 (1) Q3(R3) fl(2)|(), sealed N* = 5: sides [0,2] (one side) + read [2,3]; read slope
     s2 = v(B'2) >= 1; left slope s1 > s2 with 2s1 integral => s1 >= 3/2 =>
     v(B'0) = v(B'2) + 2s1 >= 4; cap on B'0 cannot decide composition (2) (large
     completions push the mid slot below the chord), so v(B'0) = 4 EXACT => N = 5.
     CONFIRMED.
 (2) Q2.1 fl()|(1), sealed N* = 4: window [0,2], sides [0,1] read + [1,2]; span-1
     slopes are integers; s1 > s2 >= 1 => (v(B'0), v(B'1)) >= (3,1); read endpoint
     needs v(B'0) = 3 EXACT => N = 4. CONFIRMED.
 (3) R1 fl()|(1,1), sealed N* = 4: root polygon, three span-1 sides, slopes
     s1 > s2 > s3 >= 0 integers => v(c0) >= 2+1+0 = 3, read endpoint exact => N = 4;
     absent at N = 3 since v(c0) >= 3 always. CONFIRMED (incl. sharpness side).
Also re-checked (beyond duty) the three DIAGNOSED derivations (s2 + 2s1 >= 5; the
cap-above-height-5 line => 6; exact 6 => 7) and the P1 ladder: per-level additions
9/13/10/11/2/5/1 recomputed letter-by-letter from the S1 table = 9/22/32/43/45/50/51
cumulative — EXACT match with the sealed and censused sets. P3(b)/(d) digit counts
(18, 108) re-derived exactly.

## S5 — Own-emphasis sweeps
SP-DAG: (i) uniqueness re-derived (mu = W + B4 + B3 force g=1, ell=W, a=0, e=1,
s0'=0, lambda={(1,W)}, flanks empty — every field pinned). (ii) case split is total
(sel mu <= ell <= W by B3/B4); recentering edges checked concretely: R->Q3 (tagord
0->2), Q3->Q2 (n-W 0->1), full-Q3 -> non-full-Q3 (4th coord 0->1, uniqueness at
fixed (tag,D,w,W) since g=1 preserves w); converse clause verified (sel (1,W) =>
full by definition). (iii) |range| = n·3·n·2 = 6n^2 and the sum-bound
(|S|+1)^{6n^2} both correct. n=3 loop classes = exactly the two full POST-REC
letters: CONFIRMED.
n=1 (tau-hen): VP quotes in the n=1 clause verified VERBATIM against T.1 ((tau-irr)
domain "BRANCHES carrying >= 1 window read"; (tau-hen) "level-0 TRACKS... NO window
read ever opened: v = {(1, g)}"; (c2) depth split; the FC5 cubic contrast — whose
single read IS a window read, correctly distinguished). Adjudication is sound: at
n=1, deg fbar = 1 forces m1 = 1, window never opens, (tau-irr) domain EMPTY,
tau-word empty, catalogue word = the root confirming letter. LINE NUMBERS STALE:
cited 7067-7073/7102-7111 ("rev-5 line numbers"), actual 7072-7078/7107-7116
(uniform +5 after §T revs 6-7). See S6 finding 1.
SP-FIN encoding: 1+3+5+(n+1)+n^2+2+2n = n^2+3n+12 ✓; entries fit {0..n+1} (tag
needs 3 <= n+2 at n=1 ✓, d <= n+1 ✓, lambda multiplicities <= n ✓); flank cut-set
encoding injective (spans recoverable: left = s0', right = W - s0' - w'). Bound
(n+2)^{n^2+3n+12} ✓. Gate-record arithmetic: boxes 2^24/3^15/3^18/3^21 ✓; N=7
witnesses g = x^3+3x^2+27x+729u give child heights (6,3,1) ✓; the 11-letter p=2
and 2-letter p=3 field-size lists recounted ✓ (42 = 53-11, 51 = 53-2 ✓).

## S6 — Findings (quote-and-classify; nothing fixed) and verdict
 F1 [GAP, display]: n=1 clause, "quoted verbatim ... at its rev-5 line numbers"
    (l. 6384) — all four VP cites are +5 stale (e.g. cited "[lines 7072-7073]" for
    text now at 7077-7078). Quotes verbatim-correct; pin needs refresh or a
    drift-proof anchor (quote-only).
 F2 [GAP, record wording]: rev-6 gate record "all 47 fresh N* thresholds SHARP"
    (l. 6750) and seal lines 44/172: only 45 non-diagnosed letters CARRY an N*;
    the two {(1,1)^3} rows are p=3 field-size excluded (no N*, absent at all
    levels per the seal's own P1). 47 = 53 - 6 counts letters, not thresholds.
    Realized-set arithmetic (9/22/32/43/45/50/51) unaffected.
 No criticals. Catalogue (53), menus, SP-FIN, SP-DAG, SP-COMP citations, shift
 block, halt convention, thresholds: all verified or independently re-derived.
VERDICT: CLEAN AT CONTENT LEVEL — 0 critical, 2 display/record gaps (F1, F2).
