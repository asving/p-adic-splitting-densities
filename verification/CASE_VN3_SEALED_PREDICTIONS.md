# CASE-VN3 SEALED GATE — V-n3, the §V-TABLES gate: table block both ways + one COMP-h instance

*(2026-07-27. SEALED BEFORE ANY CENSUS CODE EXISTED. Source: MOVES_2026-07-24.md
§V-TABLES rev 3, V.6 (V.6.1 block A1, V.6.2 block A2, V.6.3 block B-step, V.6.4
gate B, V.6.5 census duties + sealed attribution). Case-K discipline: seal precedes
census; any sealed falsifier fires ⟹ the gate FAILS and this file is not touched.
EVERY mathematical value below is transcribed or derived from V.6's displays — the
note computed all of V.6.1–V.6.4 BY HAND (rev 2 finding 14) and two adversarial
passes verified the arithmetic; nothing lives only in this seal. WHAT IS UNDER TEST
(V.6.5 verbatim): the CONJUNCTION {computed partition (D1)–(D4) + closed-form tables
((iv)-POLY, T-half) + target typing ((i)) + partition/representative count faces
((iv)-PART/REP) + COMP-h typing at fixed heights and TWO fixed entrance histories
checked separately ((vi), (U-A)'s §C-derivable face PER HISTORY — no (XHD-u) content)
+ the upstream §C/§D4-R laws consumed}. No layer isolates one clause.)*

## S0 — FREE CHOICES (census conventions ONLY; every predicted number is V.6's)

- FC1 CENSUS q-LIST (V.6 verbatim): q ∈ {2, 3, 4, 5, 7, 8, 9, 11, 13} — nine
  points, prime powers deliberately included; every table entry has degree ≤ 3, so
  per-entry surplus ≥ 5 per (†).
- FC2 FIELD MODELS (convention): prime q as ℤ/q; F₄ = F₂[x]/(x²+x+1),
  F₈ = F₂[x]/(x³+x+1), F₉ = F₃[x]/(x²+1); elements encoded as base-p digit ints,
  add/mul tables precomputed. Factorization by exhaustive root scan + synthetic
  division (definitional counting — no discriminant formula on the A1 side, per
  V.6.1 (D2)).
- FC3 CONVENTION-FACE CHECK (definitional): the census classifies m₂ outcomes by
  DIRECT factorization; V.6.3 (D2)'s displayed strata conventions (odd q: square
  class of disc = w² − 4u; char 2: double ⟺ w = 0, else Tr_{F_q/F₂}(u/w²) = 0/1
  for split/inert) are checked AGAINST the direct classification at every (u, w),
  all nine q — a display check in the F3 style (a mismatch indicts the displayed
  convention, not the counts).
- FC4 A2 p = 2 DIGIT BOX (convention): coefficients (a, b, c) of the recentered
  f = z³ + az² + bz + c enumerated mod 2⁵ (level-5 box per coordinate; the deepest
  sealed read is c's level-4 value pin, so 2⁵ suffices with one level of slack);
  entry cylinder {v(a), v(b), v(c) ≥ 1} = 2¹² members. v(x) computed by literal
  digit scan; x ≡ 0 mod 2⁵ treated as v ≥ 5 (only "≥ 3" reads are sealed for b).
- FC5 GATE-B BOX (V.6.5 verbatim): f = z³ + c₂z² + c₁z + c₀ over the residue box
  (c₂, c₁, c₀) mod 2^N — box size 2^{3N}, N = 3 then N = 4. Per-history frame:
  shift by the naive lift of that history's residue double root (z ↦ z, resp.
  z ↦ z + 1); Hensel-lift the simple root by Newton iteration mod 2^N (unique — the
  root is simple); h = the monic quadratic cofactor by synthetic division (exact
  mod 2^N: h mod 2^k is determined by f mod 2^k for every k — V.6.4's THRESHOLD
  display). MARKED PAIR = (f, history) with that history's entrance + event; an f
  realizing the event on both branches counts twice, exactly as μ̂ demands.
- FC6 EXACTNESS: all tallies exact Python ints / Fractions; no floats; zero
  tolerance. Long output → /tmp/vn3_census.out; JSON →
  verification/results/case_vn3_results.json.

## S1 — SEALED BLOCK A1 (V.6.1: the root skeleton s₀, n = 3, transcribed)

Pool = all monic cubics f̄ = z³ + āz² + b̄z + c̄ over F_q: q³ members; W_loc = 3,
W_state(s₀) = 0. (D3): JREF^src(s₀) = {α₀}, predicate ⊤, |α₀|(q) = 1 — ONE
representative; the two-representative census clause is VACUOUS here (recorded).
(D1) five letters, with sealed CLOSED FORMS (each degree ≤ 3):

| letter | shape | closed form |
|---|---|---|
| m_H3 | three distinct linear factors (TERMINAL, 3 Hensel tracks) | q(q−1)(q−2)/6 |
| m_H12 | linear × irreducible quadratic (TERMINAL) | q²(q−1)/2 |
| m_H⟨3⟩ | irreducible cubic (TERMINAL, [e=1,f=3]) | (q³−q)/3 |
| m_2+1 | ψ²χ, ψ ≠ χ linear (CONTINUING, μ = 2 → s_blk2) | q(q−1) |
| m_3 | ψ³, deg ψ = 1 (CONTINUING, μ = 3) | q |

PART-1 count face (sealed identity, per q): sum of the five entries = q³ = pool.
(D4) target typing (sealed): every m_2+1 member lands at hinge value
t := β̄ − ᾱ ∈ F_qˣ — t ≠ 0 by distinctness, i.e. EVERY ψ²χ entrance lands inside
β₀ = the ⊤-cell of s_blk2; m_3 ↦ β_3 (single ⊤-cell, |β_3| = 1) — no residual
value retained; census checks t ≠ 0 member-wise.

SEALED PREDICTED EVALUATIONS (V.6.1 verbatim; rows in (D1) order; final row =
PART-1 sum q³):

| q | 2 | 3 | 4 | 5 | 7 | 8 | 9 | 11 | 13 |
|---|---|---|---|---|---|---|---|---|---|
| m_H3 | 0 | 1 | 4 | 10 | 35 | 56 | 84 | 165 | 286 |
| m_H12 | 2 | 9 | 24 | 50 | 147 | 224 | 324 | 605 | 1014 |
| m_H⟨3⟩ | 2 | 8 | 20 | 40 | 112 | 168 | 240 | 440 | 728 |
| m_2+1 | 2 | 6 | 12 | 20 | 42 | 56 | 72 | 110 | 156 |
| m_3 | 2 | 3 | 4 | 5 | 7 | 8 | 9 | 11 | 13 |
| Σ = q³ | 8 | 27 | 64 | 125 | 343 | 512 | 729 | 1331 | 2197 |

The m_H3 zero at q = 2 is a GENUINE falsifier (V.6.5): the census must find
EXACTLY 0 (no three distinct monic linear factors exist over F₂... there are only
two linear polynomials — the census derives this, the seal predicts it).

## S2 — SEALED BLOCK A2 (V.6.2: the wild-heavy side skeleton s₁, transcribed)

After root letter m_3 (f̄ = z³, recentered: v(a), v(b), v(c) ≥ 1), s₁ = the branch
riding the SIDE (0, h₀)–(2, h₂) of STRIDE e = 2, h₀ − h₂ ODD (fractional slope;
WILD at p = 2 since p │ e); sibling side (2, h₂)–(3, 0) is a separate branch.
a_eff = 0. Height domain (displayed ILLUSTRATION — the gate FIXES its heights,
consumes no domain hypothesis): {h₂ ≥ 1, h₀ > 3h₂, h₀ − h₂ odd} = the ONE linear
set L((4,1); {(3,1), (2,0)}) in (h₀, h₂).
FRESH VALUES at fixed (h₀, h₂): (u₀, u₂) ∈ (F_qˣ)² — u₀ = level-h₀ digit of c,
u₂ = level-h₂ digit of a; side support = ENDPOINTS ONLY (interior point
(1, (h₀+h₂)/2) is half-integral — no lattice digit); v(b) ≥ (h₀+h₂+1)/2 pure
STRIP. Pool (F_qˣ)²; W_loc(m_w) = 2.
(D1): ONE letter m_w — residual R(y) = u₂y + u₀ (degree 1), root
y₀ = −u₀/u₂ ∈ F_qˣ, ALWAYS multiplicity 1: certified irreducible, absorbing
verdict [e = 2, f = 1]. (D2): source generators EMPTY; the outcome hinge-value
cell = the untwisted VAL.1 cell of y₀: ONE cell F_qˣ with FIBER COUNT c_V = q − 1
(for EVERY fixed y₀ ∈ F_qˣ: #{(u₀, u₂) : −u₀/u₂ = y₀} = q − 1 — sealed, checked
at every y₀, all nine q). Exceptional-char convention (displayed): at char 2 the
sign in y₀ collapses (−1 = 1); NO cell and NO count changes. (D3):
JREF^src(s₁) = {α₁}, ⊤, |α₁|(q) = 1. (D4) vacuous; DEG-CONS vacuous over Out(s₁)
(upstream sibling split 2 + 1, Σ = 3 ≤ 3, recorded at the entrance layer).

SEALED TABLE + EVALUATIONS: T_{m_w,[y₀-cell]}^{α₁,[e=2,f=1]} = (q−1)², degree
2 ≤ 2; PART-1: (q−1)² = pool (one letter).

| q | 2 | 3 | 4 | 5 | 7 | 8 | 9 | 11 | 13 |
|---|---|---|---|---|---|---|---|---|---|
| T = (q−1)² | 1 | 4 | 9 | 16 | 36 | 49 | 64 | 100 | 144 |

At q = 2 (the wild census point): T(2) = 1 — the single assignment
(u₀, u₂) = (1, 1), R = y + 1, y₀ = 1 ∈ F₂ˣ.

SEALED WEIGHT FACE ((U-A), displayed derivation): new digit pins beyond the entry
cylinder {v(a), v(b), v(c) ≥ 1}: c: (h₀−1) strip zeros + 1 value pin; a: (h₂−1)
+ 1; b: (h₀+h₂−1)/2 strip zeros ⟹ g(h₀, h₂) = q^{−E}, E = (3(h₀+h₂)−1)/2 —
affine, positive weights. SEALED CENSUS HEIGHT POINT: the base (h₀, h₂) = (4, 1):
E = 7, per-assignment conditional mass q^{−7}. Derived count in FC4's box
(p = 2, the only assignment (u₀,u₂) = (1,1)): members of the 2¹²-member entry
cylinder with v(c) = 4 & level-4 digit 1 (c ≡ 16 mod 32), v(a) = 1 (a ≡ 2 mod 4),
v(b) ≥ 3 (b ≡ 0 mod 8): 2¹² · 2^{−7} = 2⁵ = **32 EXACTLY**; on ALL 32 members the
NP lower hull over (0,4), (1,v(b)), (2,1), (3,0) has vertex set {(0,4),(2,1),(3,0)}
with the interior point strictly above (side support = endpoints — zero
exceptions), realizability {h₂ ≥ 1, h₀ > 3h₂, h₀−h₂ odd} holds at (4,1).

## S3 — SEALED BLOCK B-STEP (V.6.3: the size-2 block skeleton s_blk2, transcribed)

s_blk2 = the m_2+1 target: branch frame f = u·h, h = z² + h₁z + h₀ distinguished
(v(h₀), v(h₁) ≥ 1), u the unit cotrack; concrete states = hinge t ∈ F_qˣ; window
= NP over (0, v(h₀)), (1, v(h₁)), (2, 0). (D3): JREF^src = {β₀}, ⊤ on F_qˣ,
|β₀|(q) = q − 1, degree 1 ≤ W_state = 1. REPRESENTATIVES CENSUSED (sealed): t = 1,
and t = 2 at q ≥ 3 ((iv)-REP count face; at q = 2 the cell has ONE state —
recorded); the letters' evaluation maps read NO t (D2's executed observable
check), so rows from distinct representatives must be IDENTICAL.
(D1) three letters: m₂ [one side (0,2λ)→(2,0), λ ≥ 1, stride 1, residual deg 2]:
fresh (u, w) ∈ F_qˣ × F_q (u = level-2λ digit of h₀, w = level-λ digit of h₁,
w = 0 encodes v(h₁) > λ); R(y) = y² + wy + u; outcomes o_split (2 terminal
tracks) / o_inert (terminal [e=1,f=2]) / o_double (double root y* ∈ F_qˣ,
CONTINUING μ = 2 → β₁); m_w2 [slope k₀/2, k₀ odd, stride 2]: fresh u ∈ F_qˣ,
terminal certified [e=2,f=1]; m_vv [two sides, vertex (1,k₁), 2k₁ < k₀]: fresh
(u₀,u₁) ∈ (F_qˣ)², 2 terminal tracks. (D2) strata conventions: FC3 above (odd-q
disc square class / char-2 Artin–Schreier) — the closed forms are the SAME
polynomials under both. (D4): m₂/o_double ↦ β₁ (recentered at y*, |β₁| = 1),
all other letters absorbing; census checks y* ∈ F_qˣ member-wise.

SEALED CLOSED FORMS (pool q(q−1) per representative for m₂; degrees ≤ 2):
T_{o_split} = (q−1)(q−2)/2 [char-2 recount (q−1)(q/2 −1) — EQUAL];
T_{o_inert} = q(q−1)/2 [char-2 recount (q−1)·q/2 — EQUAL];
T_{o_double}^{β₀,β₁} = q − 1 [char 2: w = 0, u ∈ F_qˣ — EQUAL];
PART-1: (q−1)(q−2)/2 + q(q−1)/2 + (q−1) = q(q−1); T_{m_w2} = q − 1 (pool F_qˣ);
T_{m_vv} = (q−1)² (pool (F_qˣ)²).

SEALED PREDICTED EVALUATIONS (V.6.3 verbatim):

| q | 2 | 3 | 4 | 5 | 7 | 8 | 9 | 11 | 13 |
|---|---|---|---|---|---|---|---|---|---|
| o_split | 0 | 1 | 3 | 6 | 15 | 21 | 28 | 45 | 66 |
| o_inert | 1 | 3 | 6 | 10 | 21 | 28 | 36 | 55 | 78 |
| o_double | 1 | 2 | 3 | 4 | 6 | 7 | 8 | 10 | 12 |
| Σ = q(q−1) | 2 | 6 | 12 | 20 | 42 | 56 | 72 | 110 | 156 |
| m_w2 | 1 | 2 | 3 | 4 | 6 | 7 | 8 | 10 | 12 |
| m_vv | 1 | 4 | 9 | 16 | 36 | 49 | 64 | 100 | 144 |

## S4 — SEALED GATE B (V.6.4: ONE COMP-h instance vs a §D4-R fiber mass, p = 2)

ENTRANCE ε = (root m_2+1 prefix, μ = 2 branch, its (side,ψ)-selection); landing
cell β₀. The root read is HEIGHT-FREE: H(ε) = {()}, h_ent = (); ledger exponent
A(ε, ()) = 3 (three reduction digit pins), W_ent(ε) = 3.
ENTRANCE COUNT/MASS (sealed): I^ent_{ε,β₀}(())(q) = T_{m_2+1} = q(q−1), degree
2 ≤ 3; note I^ent = q·|β₀| ≠ |β₀| (the displayed "I^ent = |β₀| is NOT general"
instance). AT p = 2: **I^ent(2) = 2** — the two marked histories f̄ = z²(z+1) and
f̄ = (z+1)²z; **ι = 2·2^{−3} = 1/4** (each entrance mark carries the D4R.1-SUM
summand q^{−3}; census face: 2 marked classes among the 8 mod-2 classes).
TWO-HISTORY DISCIPLINE (rev 3, finding-6 repair — sealed): (U-A) applied PER
HISTORY, separately. Both land at the SAME β₀ state (t = 1 for z²(z+1);
t = −1 = 1 at p = 2 for (z+1)²z); in EACH history's branch frame the step read
carries the SAME nominal inventory (window NP over (0,v(h₀)), (1,v(h₁)), (2,0),
fresh (u,w), pins E = 3λ — a function of the window shape ALONE, which the
recentering shift never enters). Hence **T = 1 and g = 2^{−3} FOR EACH history BY
DISPLAY**; the commonality is DERIVED, not assumed; no (XHD-u) content exercised.
STEP: γ¹ = (β₀ →^{m₂, o_double} β₁) at SEALED λ = 1, height point h₁ = (k₀ = 2).
From V.6.3: T_{o_double}(2) = 1 — the UNIQUE cell (u, w) = (1, 0):
R = y² + 1 = (y+1)², y* = 1. WEIGHT: new pins beyond {v(h₀) ≥ 1, v(h₁) ≥ 1}:
h₀ — one strip zero (level 1) + the level-2 value pin; h₁ — the level-1 digit
w = 0: **E(h₁) = 3λ = 3, g = 2^{−3} = 1/8** (general E = 3λ affine). Event data:
h₀ ≡ 4 mod 8 (v(h₀) = 2 with unit digit) and h₁ ≡ 0 mod 4 (v(h₁) ≥ 2).
THRESHOLD N = 3 (derivation sealed): f̄ has the double and simple roots
reduction-separated, so the coprime Hensel factorization f = u·h lifts uniquely
with h mod 2^k determined by f mod 2^k for EVERY k; the deepest event datum is
h₀'s level 3. Level 3 determines every event datum.

SEALED EXACT PREDICTIONS (gate-B integers):
- **μ̂(marked event) = ι·T·g = (1/4)·1·(1/8) = 2^{−5} = 1/32** (the dyadic mass);
- **count shadow = I^ent(2)·T(2) = 2·1 = 2**;
- MARKED PAIRS among the 2^{3N} residues = μ̂·2^{3N} = 2^{3N−5}:
  **N = 3: 16; N = 4: 128** (= 16·2³ EXACTLY, zero event-word changes —
  BOX-PRECISION, the SIB-gate B22 pattern: the N = 4 marked set is EXACTLY the
  8-fold cylinder preimage of the N = 3 marked set, per history);
- MARKED-HISTORY COUNT = 2 at both levels (both entrance histories realized);
- per-history split (derived from the sealed per-history T = 1, g = 2^{−3}:
  2^{3(N−1)} entrance members × 2^{−3}): **8 + 8 at N = 3; 64 + 64 at N = 4**.

## S5 — FALSIFIERS + SEALED ATTRIBUTION (any hit ⟹ gate FAILS, file untouched)

F1 (A1) any table-entry mismatch at ANY of the nine q (definitional count vs
   closed form vs the sealed integer above); PART-1 ≠ q³; any m_2+1 member with
   t = 0 (a (D4)/(i) typing failure); m_H3 ≠ 0 at q = 2.
F2 (A2) T ≠ (q−1)² at some q; some y₀-cell fiber count ≠ q − 1; some residual
   root y₀ = 0 or multiplicity ≠ 1; the p = 2 digit census at (h₀,h₂) = (4,1)
   ≠ 32 members; any NP side-support violation (interior point on the hull).
F3 (B-step) any table-entry mismatch at any q or representative; PART-1 ≠ q(q−1);
   rows from t = 1 vs t = 2 NOT identical at some q ≥ 3 ((iv)-REP failure); some
   o_double member with y* ∉ F_qˣ ((D4) typing failure).
F4 (gate B) marked pairs ≠ 16 at N = 3 or ≠ 128 at N = 4; marked-history count
   ≠ 2; per-history counts ≠ (8,8)/(64,64); μ̂ ≠ 1/32 as an exact Fraction at
   either N; I^ent(2) ≠ 2 or ι ≠ 1/4; BOX-PRECISION failure (any event-word
   change under extension); any Hensel/division residue check failure (h not a
   factor mod 2^N, or v(h₀)/v(h₁) < 1 at an entrance).
F5 (convention face, FC3) direct factorization vs the displayed (D2) strata
   conventions mismatch at some (u, w): indicts the DISPLAYED CONVENTION only
   (F3-style; counts stand — they are census-definitional); record verbatim.
ATTRIBUTION (V.6.5, sealed with the predictions — finding-14 discipline): layers
A and B JOINTLY test the conjunction in the header; a surviving mismatch INDICTS
THE CONJUNCTION — no layer isolates one clause. Adjudication order (sealed):
(1) prediction-derivation error (Case-K); (2) re-run the upstream face on the
same box (D4R.4-SUM count for B; raw pool totals for A) — if upstream reconfirms,
the failure localizes to THIS note's layer but NOT to a single clause; (3) a
theory error triggers plan §8 R1's isolation experiment BEFORE any further RESUM
work, and the (†) protocol decides any non-polynomiality claim (one exact
mismatch, surviving (1)–(2), refutes universality of that entry conclusively).

## S6 — Census specification (case_vn3_gate.py, written AFTER this seal)

- A1: all q³ monic cubics per q, factorization by root scan + synthetic division
  over FC2's field models; classify into the five letters; per m_2+1 member
  extract (ᾱ double, β̄ simple), check t = β̄ − ᾱ ≠ 0. Tally vs S1.
- A2: all (q−1)² fresh (u₀,u₂) per q: root/multiplicity of R(y) = u₂y + u₀,
  y₀-cell fiber counts at every y₀; p = 2: FC4's 2¹⁵ box → entry cylinder → the
  (4,1) digit event count + NP hull check per member. Tally vs S2.
- B-step: per q, per representative t (1; and 2 at q ≥ 3): m₂ over q(q−1)
  fresh (u,w) with direct factorization of R(y) = y² + wy + u (+ FC3 convention
  cross-check, + y* ∈ F_qˣ on o_double); m_w2 and m_vv pool counts. Tally vs S3.
- Gate B: FC5's boxes at N = 3, 4: per (f, history) entrance check, frame shift,
  Newton lift, synthetic division (residue ≡ 0 mod 2^N asserted), event read;
  tally marked pairs, per-history, history count, μ̂ = count/2^{3N} (Fraction),
  entrance-class count/mass, N = 4 → N = 3 projection uniformity (8 each).
- What this gate does NOT test (honest perimeter, V.6/V.5 verbatim): the FULL
  table build (VALUE-Fq's 24-q layer and VALUE-p's n = 5 shadow REMAIN standing
  obligations distinct from V-n3); (XHD-u) content (none exercised — the
  commonality at V.6.4 is derived); the wild-p ACTIVE-VALUE layer (RESUM-n3's,
  V.5(5)); deeper heights beyond the sealed points (λ = 1; (h₀,h₂) = (4,1));
  (ii-a)'s empty-cell check (VACUOUS at these blocks — sizes 1, q−1, 1).

## S7 — POST-CENSUS VERDICT (appended after the run; no prediction above touched)

*(2026-07-27, census = case_vn3_gate.py, run after S0–S6 were sealed. Full log:
/tmp/vn3_census.out (178 checks, 0 failures); JSON: results/case_vn3_results.json.
Members walked: 9 q³-pools (A1), 9 (q−1)²-pools + the 2¹⁵ digit box (A2),
9 q(q−1)-pools × representatives (B-step), 2⁹ + 2¹² gate-B boxes × 2 histories.)*

| sealed | census result |
|---|---|
| A1 rows, nine q | definitional counts = closed forms = sealed integers at ALL nine q ✓ (45 entries) |
| A1 PART-1 | Σ = q³ at all nine q ✓ |
| A1 (D4)/(i) typing | t = β̄ − ᾱ ≠ 0 on every m_2+1 member, all q ✓ (0 violations) |
| A1 m_H3 at q = 2 | EXACTLY 0 ✓ (the genuine falsifier did not fire) |
| A2 table | T = (q−1)² at all nine q ✓; y₀ ∈ F_qˣ, 0 violations ✓ |
| A2 VAL.1 fiber face | fiber count = q − 1 at EVERY y₀ ∈ F_qˣ, all nine q ✓ |
| A2 p = 2 digit census | entry cylinder 4096; event count at (4,1) = 32 = 2¹²·2^{−7} EXACTLY ✓ (E = 7) |
| A2 NP side support | hull vertices {(0,4),(2,1),(3,0)}, interior strictly above, on all 32 ✓ |
| B-step rows | (o_split, o_inert, o_double) = sealed at all nine q, both representatives ✓ |
| B-step PART-1 | Σ = q(q−1) per representative ✓; m_w2 = q−1, m_vv = (q−1)² ✓ |
| B-step (iv)-REP | rows at t = 1 and t = 2 IDENTICAL at all q ≥ 3 ✓ |
| B-step (D4) | y* ∈ F_qˣ on every o_double member ✓ |
| B-step convention face (F5) | direct factorization = disc-square-class (odd q) = Artin–Schreier Tr (char 2) at every (u,w), all nine q — 0 mismatches ✓ |
| Gate B marked pairs | N = 3: **16**; N = 4: **128** EXACTLY ✓ |
| Gate B per history | 8 + 8 (N = 3), 64 + 64 (N = 4) ✓; marked-history count 2 at both levels ✓ |
| Gate B μ̂ | 16/2⁹ = 128/2¹² = 1/32 = 2^{−5} exact Fractions ✓ |
| Gate B box-precision | N = 4 marked set = EXACT 8-fold cylinder preimage of the N = 3 set, per history (zero event-word changes) ✓ |
| Gate B entrance | censused ψ²χ classes = 2 = the two sealed histories verbatim; ι = 2/8 = 1/4 ✓; count shadow 2·1 = 2 ✓ |
| Gate B mechanics | Hensel lift + synthetic division exact mod 2^N, 0 residue failures; v(h₀), v(h₁) ≥ 1 at every entrance ✓ |

GATE VERDICT: **PASS** — all sealed verdict families exact, zero tolerance met, no
falsifier fired (F1–F5 all silent). The V.6 conjunction {(D1)–(D4) partitions +
closed-form tables + target typing + count faces + the two-history COMP-h instance
+ the consumed §C/§D4-R laws} survives its first census: the A1/A2/B-step tables
hold definitionally at nine q with per-entry surplus ≥ 5 per (†), and the COMP-h
instance prices as ι·T·g = 2^{−5} with BOX-PRECISION at both levels. What this
pass does NOT certify: S6's perimeter verbatim — the FULL table build (VALUE-Fq's
24-q layer, VALUE-p's n = 5 shadow) remains a standing obligation; no (XHD-u)
content was exercised; the wild-p ACTIVE-VALUE layer stays RESUM-n3's; heights
beyond λ = 1 and (h₀,h₂) = (4,1) untested. Per V.6.5 GOVERNANCE: V-n3 joins the
plan §7 roster; [1v]-COND's acceptance precondition is now met by THIS gate
(the VALUE-Fq/VALUE-p obligations unchanged).
