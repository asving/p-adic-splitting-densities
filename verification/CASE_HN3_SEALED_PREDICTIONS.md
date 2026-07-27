# CASE-HN3 SEALED GATE — H-n3, the §H-DOMAINS gate: the XHD height-domain package on family 𝔉_H

*(2026-07-27. Source: MOVES_2026-07-24.md §H-DOMAINS rev 5, H.6 "Gate H-n3 (SEALED AT
REV 2 ...)" — the seal is IN THE NOTE (lines 10682–10772); pass records at revs 3/4/5
each re-derived and confirmed "every sealed H-n3 number stands". Case-K discipline:
seal precedes census; any sealed falsifier fires ⟹ the gate FAILS and the seal is not
touched. Every mathematical value below is TRANSCRIBED from the note's sealed clause
(a)–(e) + (L1)–(L5); §S0 holds census conventions ONLY.)*

## S0 — FREE CHOICES (census conventions ONLY; every predicted number is the note's)

- FC1 BLOCK BOX (convention): the census enumerates the distinguished quadratic block
  h = z² + b·z + c over the residue box (b, c) mod p^N with v(b) ≥ 1, v(c) ≥ 1 (the
  entry cylinder, p^{2(N−1)} members), N = 8 at p = 2 and N = 6 at p = 3 — exactly the
  sealed precisions O(2⁸)/O(3⁶). Seal (e) licenses this: N = h₁ + 1 BLOCK-COEFFICIENT
  digits decide membership and verdict.
- FC2 CUBIC BOX (convention, for the representative/prefix layers L2/L3 and oracle):
  f = z³ + a·z² + b·z + c over (a, b, c) mod p^N with (ā, b̄, c̄) = (1, 0, 0), i.e.
  f̄ = z²(z + 1̄): p^{3(N−1)} members. Unit root r ≡ −1 (mod p) by Newton iteration
  (f'(r) is a unit); block h = f/(z − r): B = a + r, C = b + rB, remainder f(r) ≡ 0
  mod p^N asserted member-wise. PREFIX/REPRESENTATIVE convention: the source-cell
  representatives are the p prefix classes a mod p² (digits the block cell forgets);
  L2 fixes the class a ≡ 1 (mod p²), L3 compares ALL p classes pairwise.
- FC3 CLASSIFIER (convention — direct Montes walk on the block, no formula reuse):
  loop on (b, c): NP of {(0, v(c)), (1, v(b)), (2, 0)}; vertex at (1, v(b)) (2v(b) <
  v(c)) → two-sided read, off-template; v(c) odd with 2v(b) ≥ v(c) → the (2, v(c))
  read, TERMINAL (ramified verdict), lead digit = digit of c at v(c); v(c) = 2t even →
  residual R(y) = y² + b_t·y + c_{2t} (digits at levels t, 2t): double root y* ∈ F_pˣ
  → LOOP read (1, t), recenter z ↦ z + y*·p^t (b ← b + 2y*p^t, c ← c(y*p^t-shifted));
  distinct/irreducible R → terminal split/inert, off-template; c ≡ 0 mod p^N → DEEP
  (beyond cap, excluded from two-sided comparison). γ_H at (h₀, h₁) := path = exactly
  ONE loop read at h₀ then the terminal (2, h₁) read (loop-free, per the seal); chain
  = (u, lead) := (read-0 residual root value in F_pˣ, terminal lead digit in F_pˣ).
- FC4 CAP ADAPTATIONS at p = 3 (the sealed cap O(3⁶) decides digits at levels ≤ 5):
  L2's (3,7) leg and L4's (1,7)/(2,7)/(3,7) legs run at p = 2 ONLY (sealed p = 3
  census set is {(1,3),(2,5),(1,5)}); L4's constancy legs at p = 3 truncate to
  (1,3),(1,5) [period (0,2)] and (1,3),(2,5) [coarse period (1,2)]. ENTRANCE leg at
  p = 3, h₀ = 3 needs c's digit at level 6: censused in a MARKED EXTENSION box O(3⁷)
  (block box only; an extension of the census, not of the seal).
- FC5 NORMALIZATION (convention): predicted per-point counts = sealed masses × box
  cardinality — block box: stratum count = T·q^{−E}·p^{2(N−1)}; cubic box per prefix
  class (p^{3N−4} members = p^{3(N−1)}/p classes; exponent typo 3N−5 corrected at the
  first p = 2 run, S4's derived integers 2²⁰/3¹⁴ were always the operative values):
  per-chain count = q^{−E}·p^{3N−4}. All arithmetic exact
  Python ints/Fractions; zero tolerance. Long output → /tmp/hn3_census.out; JSON →
  verification/results/case_hn3_results.json.
- FC6 ORACLE (convention): PARI factorpadic via gp 2.17.4 (built for this gate;
  cypari2 unavailable) on sampled γ_H cubic-box members per censused point (cap 40
  per point per p): assert factorization = (degree 1) × (degree 2 irreducible), the
  quadratic factor ≡ the census's Hensel block mod p^N, and v_p(const term of the
  recentered quadratic) = h₁ odd (ramified, e = 2 — σ-type (2,1)ram). If gp is
  unusable the fallback is the elementary square-class oracle (disc = b² − 4c;
  odd-v(disc) ⟹ ramified at p odd; at p = 2 the (v mod 2, unit mod 8) classes),
  recorded as such.
- FC7 LADDER SETS (convention): the ladder at fixed (h₀, h₁) = all box members whose
  classifier path is LOOP at t₀ = h₀, LOOPs at h₀ < t₁ < ... < t_m (m ≥ 0), then
  terminal (2, h₁). At p = 3 the complete-the-square set {v(β) = h₀, v(δ) = h₁},
  β := b/2, δ := c − b²/4 (exact mod 3^N; 2, 4 units), is compared BOTH by count and
  by set equality with the ladder set. At p = 2: sealed formula only (census-only).

## S1 — SEALED FAMILY + TEMPLATE (H.6 gate clause, transcribed)

PRIMARY FAMILY 𝔉_H (n = 3): f monic cubic, f̄ = z²·(z + 1̄) — quadratic block at z,
unit root branch aside; template γ_H = [root read on the block: (e₀, h₀) = (1, h₀),
side [0, 2] adjacent, residual (z + u)², u ∈ F_pˣ (μ₀ = 2, g₀ = 1); second read:
(e₁, h₁) = (2, h₁), side [0, 2] adjacent (hinge (HV) ACTIVE — exercises (C3)/
M4b-T-AUD), residual linear, terminal verdict: ramified quadratic factor — DECIDED,
σ-type (2,1)ram, oracle-checkable]. Height point (h₀, h₁), d = (1, 1) (both reads
adjacent — no û*). γ_H is LOOP-FREE: the intermediate refinement levels carry FRESH
ZEROS (part of E below); histories with a nonzero intermediate digit are
self-loop-augmented DIFFERENT templates.

## S2 — SEALED (a): DOMAIN + COMPONENT LIST (class (TRI) ✓)

Census constraints: (C1) gcd(h₁, 2) = 1; (C2) h₀ ≥ 1 and (I-aug) h₁ > 2h₀; no û*,
so no (SAE)/(NA). H-LIST emits TWO cells:
    L((1,3); {(2,4), (0,2)})  (h₀ odd)   ⊔   L((2,5); {(2,4), (0,2)})  (h₀ even);
the union equals the coarser single linear set L((1,3); {(1,2), (0,2)}) (coarse
bijection displayed: n₁ = h₀ − 1, n₂ = (h₁ − 2h₀ − 1)/2). Disjointness: h₀ parity.
Census must confirm exactness BOTH ways. [Rev-5 reorder VACUOUS for this family
(integer slope 2); the refined construction emits the SAME two components — pass
records 3/4/5.]

## S3 — SEALED (b): THE AFFINE E, DISPLAYED

Read 0: c-line 2h₀ pins (strip zeros at levels 1..2h₀−1 + value digit u² at 2h₀) +
b-line h₀ pins (strip zeros at 1..h₀−1 + digit 2u at h₀; at p = 2 that digit is the
zero pin) = 3h₀. Read 1 (recentered frame): C-slot h₁ − 2h₀ pins (strip zeros at
2h₀+1..h₁−1 — level 2h₀ is the (HV)-hinge cancellation, pinning nothing — + free
nonzero value digit at h₁) + B-slot (h₁−1)/2 − h₀ pins (strip zeros at
h₀+1..(h₁−1)/2; new(1) = h₁/2 off-lattice, so NO value digit). TOTAL, integer on
the h₁-odd classes:
    E(h₀, h₁) = (3h₁ − 1)/2,   w_E = (0, 3/2):
h₀-WEIGHT EXACTLY 0 — the E-POS coordinatewise counterexample (read 0 charges +3h₀,
read 1 discharges −3h₀; H.1.2(ii-b)). PER-PERIOD MARGINS: ⟨w_E,(1,2)⟩ = ⟨w_E,(0,2)⟩
= 3, ⟨w_E,(2,4)⟩ = 6 — all ≥ 1: E-POS displayed for this family.

## S4 — SEALED (c): PREDICTED PER-POINT NUMBERS

(Per source representative; u free in the chain count.) Per-chain conditional mass
q^{−E(h)}; chain count T = (p−1)·(p−1) (u × the C-lead digit at h₁), CONSTANT across
the domain — p = 3: T = 4; p = 2: T = 1. Census points:
    (1,3): E = 4;   (2,5), (1,5): E = 7;   (3,7), (2,7), (1,7): E = 10
— per-chain masses q^{−4}, q^{−7}, q^{−10}; per-point stratum mass T·q^{−E}.

DERIVED BOX COUNTS (FC5 arithmetic on the sealed masses — census normalization):
- p = 2 block box (cylinder 2¹⁴ = 16384): γ_H counts 1024 at (1,3); 128 at (2,5),
  (1,5); 16 at (3,7), (2,7), (1,7). T = 1 chain each (u, lead) = (1, 1).
- p = 3 block box (cylinder 3¹⁰ = 59049): 2916 at (1,3) (4 chains × 729); 108 at
  (2,5), (1,5) (4 chains × 27).
- Cubic box per prefix class a mod p² (p = 2: 2²⁰ members; p = 3: 3¹⁴): per-chain
  count q^{−E}·|class|: p = 2: 65536 at (1,3), 8192 at (2,5)/(1,5), 1024 at (·,7);
  p = 3: 59049 at (1,3), 2187 at (2,5)/(1,5) — identical at EVERY prefix class.

## S5 — SEALED (d): LADDER CROSSCHECK IDENTITY

Summing the self-loop LADDER at fixed (h₀, h₁) — over the k := (h₁−1)/2 − h₀
intermediate levels, each either a γ_H fresh zero or a nonzero digit opening a
loop-augmented template — gives
    Σ_ladder T·q^{−E} = (p−1)²·p^k·q^{−(3h₁−1)/2} = (p−1)²·q^{−(h₀+h₁)},
which at p odd equals the elementary complete-the-square stratum mass (β := b/2,
δ := c − b²/4, unimodular: v(β) = h₀ with pinned digit, v(δ) = h₁ with free nonzero
digit — mass (p−1)²p^{−(h₀+h₁)}). The census checks this total independently of the
per-template split; p = 2 (no completed square) is census-only.
DERIVED BOX COUNTS (FC5): p = 2 ladder totals 1024, 128, 256, 16, 32, 64 at (1,3),
(2,5), (1,5), (3,7), (2,7), (1,7); p = 3: 2916, 108, 324 at (1,3), (2,5), (1,5).

## S6 — SEALED (e): DETERMINATION LEVEL + FIXED CAPS

All pins sit at c-line levels ≤ h₁ and b-line levels ≤ (h₁−1)/2, so N(γ_H, h) =
h₁ + 1 block-coefficient digits decide membership and verdict. FIXED CAPS: p = 2 —
census set {(1,3), (2,5), (1,5), (3,7), (2,7), (1,7)}, precision O(2⁸); p = 3 —
{(1,3), (2,5), (1,5)}, precision O(3⁶). [Census form: each γ_H stratum in the block
box is a union of full mod-p^{h₁+1} cylinders — every residue class mod p^{h₁+1}
hit by the stratum is hit by exactly p^{2(N−h₁−1)} members, chain data constant on
the class.]

## S7 — SEALED DELIVERABLE LAYERS (L1)–(L5), transcribed

 (L1) TWO-SIDED EXACTNESS CENSUS on the caps: every listed point realized
   (T_γ(x,h) ≥ 1 witnessed, per-point counts recorded), every realized point listed
   — zero orphans, zero strays (refutes (1) XHD-d-EX(∂) and, via the active hinge,
   (C3)/M4b-T-AUD);
 (L2) XHD-w CHAIN: (c)'s predicted q^{−E} vs direct conditional masses from ONE
   fixed representative and prefix at (1,3), (2,5), (3,7) [FC4: (3,7) at p = 2 only];
 (L3) REPRESENTATIVE LAYER: the same censused rows at TWO representatives of one
   source cell (refutes (3) U-R-COUNT);
 (L4) CONSTANCY LAYER, attribution SPLIT: T at (1,3), (1,5), (1,7) along the LISTED
   period (0,2) — IN-COMPONENT: M4b-T's shadow (2); T at (1,3), (2,5), (3,7) along
   the COARSE period (1,2) — CROSS-COMPONENT (h₀ parity alternates): the first
   XHD-u-X count test (4), per H.4.3's re-attribution — a failure on this leg
   indicts XHD-u-X, not M4b-T-AUD; plus the entrance family (root read (1, h₀),
   landing cell = the block cell) censused at h₀ = 1, 2, 3 ((ENT-U)'s refuter,
   H.4.4) [FC4: at p = 3, h₀ = 3 via the marked O(3⁷) extension box; entrance
   chain count = p − 1 (u free), per-chain mass q^{−3h₀} (read-0 pins)];
 (L5) ORACLE: decided verdicts vs PARI factorpadic; (d)'s ladder total vs the
   direct stratum mass.

## S8 — FALSIFIER FAMILIES + SEALED ATTRIBUTION (any hit ⟹ FAIL, seal untouched)

F1 (L1) any lattice point of the listed components (within the caps) NOT realized;
   any realized (h₀, h₁) pair NOT on the list; any per-point count ≠ T·q^{−E}·|box|.
F2 (L2) any per-chain conditional mass ≠ q^{−E(h)} at the sealed points from the
   fixed representative/prefix; T ≠ (p−1)² at a censused point.
F3 (L3) any row difference between two representatives of the one source cell.
F4 (L4) T not constant along the listed period (0,2) [indicts M4b-T-AUD shadow] or
   along the coarse period (1,2) [indicts XHD-u-X count face]; entrance count ≠
   p − 1 or entrance masses ≠ q^{−3h₀} or non-constant across h₀ = 1, 2, 3 [(ENT-U)].
F5 (L5) any γ_H member whose PARI verdict is not (linear) × (ramified irreducible
   quadratic) [σ-type (2,1)ram]; ladder total ≠ (p−1)²·q^{−(h₀+h₁)}·|box| at any
   censused point; at p = 3 the complete-the-square stratum ≠ the ladder set.
F6 (S6) determination-level failure: some γ_H stratum not a union of full
   mod-p^{h₁+1} cylinders (count or chain-data inhomogeneity).
ATTRIBUTION (sealed with the note, H.6): PASS = zero mismatches on (a)–(e)/
(L1)–(L5); any failure indicts the NAMED kernel its layer refutes (per-layer
attribution, conjunctive across the walk's inputs — TASM finding-14 discipline).
FAIL handling: adjudicate prediction-derivation errors vs theory content per the
Case-K precedent before any re-seal. HONEST LIMITATIONS (sealed): ONE family with
TWO parity components — L4's (1,2) leg gives XHD-u-X's count face its FIRST (mild)
test (components share twist and alphabet data; a genuinely heterogeneous
≥ 2-component family stays a re-seal duty; the factorization display stays
untested); H-LIST-GEN is NOT exercised (the family is in-class by design).

## S9 — POST-CENSUS VERDICT (appended after the run; no sealed value above touched)

*(2026-07-27, census = case_hn3_gate.py, written and run after S0–S8. Log:
/tmp/hn3_census.out (151 checks: 106 at p = 2, 45 at p = 3; 0 failures); JSON:
results/case_hn3_results.json. Boxes walked: block 2⁷×2⁷ and 3⁵×3⁵ cylinders, the
marked 3⁶×3⁶ entrance extension, cubic boxes 2²¹ and 3¹⁵ members (Newton + Hensel
division member-wise, 0 residue failures), 288 PARI factorpadic verdicts (gp 2.17.4
built for this gate). One CENSUS-SIDE correction mid-run, recorded at FC5: the
prefix-class size exponent (3N−5 → 3N−4); S4's derived integers (2²⁰, 65536, 3¹⁴,
59049, ...) were consistent all along and no sealed value moved.)*

| sealed | census result |
|---|---|
| (a) components == coarse set == census set, both p | listed = realized, exact ✓ |
| (L1/F1) two-sided exactness | zero orphans, zero strays; p = 2 counts 1024/128/128/16/16/16, p = 3 counts 2916/108/108 = T·q^{−E}·cyl EXACTLY at every point ✓ |
| (c/F1) chain structure | chain set = F_pˣ × F_pˣ, T = (p−1)² (1 resp. 4) at every censused point ✓ |
| (b)+(L2/F2) per-chain mass q^{−E}, E = (3h₁−1)/2 | block box: every chain exactly cyl·q^{−E}; cubic box, fixed rep a ≡ 1 mod p²: 65536/8192/1024 (p = 2, E = 4/7/10), 59049/2187 (p = 3, E = 4/7) ✓ |
| (L3/F3) representative layer | full rows IDENTICAL across all p prefix classes (2 at p = 2, 3 at p = 3) ✓ |
| (L4/F4) in-component T (period (0,2)) | T = [1,1,1] (p2), [4,4] (p3) constant ✓ [M4b-T shadow] |
| (L4/F4) cross-component T (coarse (1,2)) | T = [1,1,1] (p2), [4,4] (p3) constant across the parity components ✓ [first XHD-u-X count-face test] |
| (L4/F4) entrance family (ENT-U) | u-chain count = p−1 at h₀ = 1, 2, 3 (p = 3 h₀ = 3 via the marked O(3⁷) box), per-chain mass q^{−3h₀} exact (2048/256/32; 2187/81/27), constant ✓ |
| (d/F5) ladder crosscheck | totals (p−1)²q^{−(h₀+h₁)}·cyl exact at every point: p2 1024/128/256/16/32/64, p3 2916/108/324; = p^k·(γ_H count) ✓; p = 3 complete-the-square SET EQUALITY with the ladder set at all three points ✓ |
| (e/F6) determination level N = h₁+1 | every γ_H stratum = union of full mod-p^{h₁+1} cylinders, count AND chain data constant per class ✓ |
| (L5/F5) oracle | 288/288 sampled members: factorpadic = (linear)×(irreducible quadratic), quadratic ≡ census Hensel block mod p^N, recentered constant valuation = h₁ odd (ramified, σ-type (2,1)ram) ✓ |
| hinge (HV) | recentering cancellations at level 2t (c-line) and t (b-line) asserted member-wise on every loop read, 0 violations ✓ |

GATE VERDICT: **PASS** — every falsifier family (F1–F6) silent; two-sided exactness
met with zero tolerance; every sealed H-n3 number exact. Per the sealed attribution:
this exercises XHD-d-EX(∂) at the low-height corner, (C3)/M4b-T-AUD via the active
hinge, U-R-COUNT's representative face, the (0,2)-period constancy shadow, the FIRST
XHD-u-X count-face test (coarse (1,2) leg across the parity components), (ENT-U) at
three heights, E-POS's displayed per-period margins, and the loop-free/ladder
resummation identity. HONEST PERIMETER unchanged (sealed): one family, two parity
components sharing twist/alphabet data — the heterogeneous-component re-seal duty,
the factorization display, and H-LIST-GEN's out-of-class forms remain OPEN; kernels
E-POS (general), M4b-T-AUD, U-R-COUNT, XHD-u-X, XHD-d-EX(∂), H-LIST-GEN all stay
FENCED — a gate pass is evidence, not discharge.
