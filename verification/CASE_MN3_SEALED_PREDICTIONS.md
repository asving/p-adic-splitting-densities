# CASE-MN3 SEALED GATE — the n = 3 species catalogue, menu map, and realizability (gate M-n3)

*(2026-07-27. The seal IS the note's SP.6 (MOVES_2026-07-24.md §M-SPECIES, lines 6126-6216,
catalogue + menu map + per-prime exclusions pinned there BEFORE any census code existed).
This file copies that block VERBATIM (S1), then displays the census conventions the note
does not fix (S0 FREE CHOICES). Case-K discipline: predictions are never adjusted after
the census; any sealed falsifier fires => the gate FAILS and this file is not touched.)*

## S1 — THE SEAL, VERBATIM (= MOVES_2026-07-24.md §M-SPECIES SP.6, lines 6126-6216)

depth parameters (one marker letter + one depth slot per maximal run). What
[2a] supplies about {ε} (plan §2v: "the shape family {ε} is FINITE up to its
height parameters ([2a]/M1)"): the letters come from the finite alphabet
(SP-FIN), the links from the finite menus (SP-OUT), so at each collapsed
length the family is finite and p-independent (SP-FIN′); with loops
collapsed to (marker, depth-slot) pairs, {ε} is finite up to its (height,
depth) parameters — which is exactly the finiteness CTS-M(iii) consumes,
its per-shape masses ι_{e,ε,β₀} and entrance counts I^ent_{ε,β₀} being
[1]/[1v] objects, never assigned here. The n = 3 instance is displayed in
SP.6.

**The SUPERSET duty (binding on every consumer).** Out(s) is a SUPERSET of
the transitions realized at any given p. Three separate reasons an edge can
be empty at p, with three separate owners:
 (i)   FIELD SIZE — λ or a selection needs more distinct nonzero roots or
       distinct irreducible factors than F_q holds (e.g. λ = {(1,1)³} needs
       three distinct nonzero roots: empty at q ∈ {2, 3}); owner: [1v]'s
       tables (the entry is the zero polynomial or vanishes at q₀ —
       CTS-M(ii) ACT).
 (ii)  VALUE/COLLISION constraints — (NA)/(HV)/(SAE), nonzero endpoints,
       factor collisions; owner: [1v]'s cells and tables.
 (iii) HEIGHT-LATTICE emptiness — no height point of the step's exact
       domain; owner: [2b] XHD/M4a-X.
Realizability of a given menu edge at a given p is therefore NEVER a [2a]
claim; the menu is the index superset the CTS zero-extends over.

### SP.5 Honest perimeter (what this note does NOT establish)

- **NO COUNTS, NO MASSES.** The catalogue indexes; it never counts. Every
  count or mass routed through a shape is owned elsewhere: per-shape
  sum/event laws and pool bounds by [1] (D4R.1-SUM/-EV, D4R.2′, D4R.4;
  branch multiplicities mult_P̂ included); per-cell value counts and table
  entries by [1v] (CTS-M); resummed masses and the f-level tree assembly by
  [3] (RS.1 — where MULT ACCOUNTING converts branch-weighted sums to
  f-events); tail bounds by [5]. Any consumer counting f's through this
  catalogue owes the mult-cover duty: shape events are a multiplicity-
  weighted COVER, Σ_P̂ μ(P̂) may exceed 1, and each use must declare
  D4R.1-SUM/D4R.4-SUM (branch-weighted) or the event BOUNDS — a
  partition-of-the-box-by-shapes claim is banned (§D4-R consumer duty,
  plan §2).
- **NO REALIZABILITY.** Whether a catalogue member or menu edge is realized
  at a given p, at a given height point, in a given cell: [1v] (tables,
  ACT) and [2b] (XHD/M4a-X). The menus are supersets (SP.4).
- **NO STATE TYPES, NO GEOMETRY.** The loop state type τ = (s, α), the
  lumpability theorem, cones, congruence lattices, exact height domains,
  translation equivariance: all [2b] (M2, M4a, M4a-X, M4b/M4b-T). 𝒮_n =
  𝒮_n^raw enriched by [2b]'s types happens THERE.
- **NO LENGTH BOUND.** No bound on the collapsed letter-length of a branch
  is claimed (SP.2's count-free reading; [4]'s TRACK-COUNT is the named
  OPEN lemma in that direction, not cited here).
- **NO TERMINATION.** Infinite branches are catalogued prefixwise;
  drainage/exhaustion is [3]/[5]'s.
- **CONDITIONALITY LEDGER.** Unconditional given dual-accepted §B2-DEF:
  SP.1's datum being well-typed, SP-FIN, SP-FIN′, SP-OUT and its
  p-independence, the self-loop characterization. Conditional: SP-COMP — on
  the OPEN kernel D4R.0-K (both parts, via steps (4) and L2's totality) and
  on §C's rev-13 (SAE) repair landing as stated (§D4-R L3's realizability
  class). Nothing else in the campaign is assumed; [1v]/[2b]/[3] artifacts
  are referenced only as OWNERS of deferred duties, never consumed.

### SP.6 Sealed gate M-n3 (the obligation; catalogue and predictions pinned)

**The hand catalogue at n = 3 (exhaustive; SEALED).** Notation per letter:
(e, ℓ, a | λ ▸ sel | flanks), stage in the group head. Windows: ROOT W = 3;
POST-REC W = μ_prev ∈ {1, 2, 3}; POST-INC W = 1 always at n = 3 (every
genuine increment here has μ = 1: g·μ ≤ ℓ and e·ℓ ≤ 3 force μ ≥ 2 into
e = g = 1, the recentering class). W = 1 letters read the confirming side
(ℓ = 1, a = 0, λ = {(1,1)}) and carry the TERMINAL verdict as selection
(leaf per §D4-R L2); their menus are empty.

GROUP R — ROOT, stage (D, w, W) = (1, 1, 3): 21 letters.
  R1  e=1, ℓ=1, a=0 | {(1,1)}▸(1,1) | right span 2: flanks (2) or (1,1) — 2
  R2  e=1, ℓ=1, a=1 | {(1,1)}▸(1,1) | flanks (1)|(1)                    — 1
  R3  e=1, ℓ=1, a=2 | {(1,1)}▸(1,1) | left span 2: (2) or (1,1)         — 2
  R4  e=1, ℓ=2, a=0 | λ ∈ {(2,1)}▸(2,1); {(1,2)}▸(1,2); {(1,1)²}▸(1,1)
      | right flank (1)                                                 — 3
  R5  e=1, ℓ=2, a=1 | same three λ▸sel | left flank (1)                 — 3
  R6  e=1, ℓ=3, a=0 | {(3,1)}▸(3,1); {(2,1),(1,1)}▸(2,1) and ▸(1,1);
      {(1,3)}▸(1,3); {(1,2),(1,1)}▸(1,2) and ▸(1,1); {(1,1)³}▸(1,1)     — 7
  R7  e=2, ℓ=1, a=0 | {(1,1)}▸(1,1) | s₀′ ∈ {0, 1}                      — 2
  R8  e=3, ℓ=1, a=0 | {(1,1)}▸(1,1) | full span                         — 1
GROUP Q3 — POST-REC, stage (1, 1, 3): the same 21 rows as R1–R8.   — 21
GROUP Q2 — POST-REC, stage (1, 1, 2): 6 letters.
  Q2.1 e=1, ℓ=1, a=0 (right flank (1)); Q2.2 e=1, ℓ=1, a=1 (left (1));
  Q2.3 e=1, ℓ=2, a=0: three λ▸sel as R4; Q2.4 e=2, ℓ=1, a=0, s₀′=0.
GROUP Q1 — POST-REC, stage (1, 1, 1): 1 letter (confirming; verdict). — 1
GROUP I — POST-INC, W = 1, confirming/verdict letters, one per landing
  stage (D, w) ∈ {(2,1), (2,2), (3,1), (3,3)}                          — 4
  [(2,1) via e=2 sides; (2,2) via ▸(2,1) — D4-n3's second read; (3,1)
  via e=3; (3,3) via ▸(3,1).]


## S0 — FREE CHOICES MADE (census conventions beyond the note text; every choice displayed)

- FC1 BOX/LEVELS (per SP.6(a)): p = 2, N = 8: all (c2,c1,c0) mod 2^8 (2^24 boxes);
  p = 3, N = 5: all mod 3^5 (3^15 boxes); f = x^3 + c2 x^2 + c1 x + c0 monic.
- FC2 READ = one side of the window polygon. Window [0,W]; polygon = lower convex hull
  of {(j, v(B_j)) : 0 <= j <= W, B_j != 0}; SIDES = maximal collinear hull segments
  (interior on-line lattice slots do NOT subdivide a side). Every hull side is a read
  side (root slope-0 side included — the mod-p factorization read; (I-aug)'s strict
  slope > w(key) applies at POST-REC windows, checked internally).
- FC3 SIDE FIELDS: e = lowest-terms denominator of the side slope (drop per slot);
  w' = raw width; l = w'/e; s0' = left endpoint; slot set = the on-line lattice
  positions s0' + k*e (k = 0..l), d = l + 1 (zero digits allowed strictly inside,
  endpoints nonzero = vertices). Residual R_side(y) = sum_k dig_k y^k, dig_k = leading
  base-p digit of the slot coefficient if the point is ON the line, else 0.
- FC4 ANCHOR: a := #(extended-side-line lattice slots in the window strictly left of
  s0'); = s0' at e = 1 reads (= ord_z R(f) by D.10's well-typedness: positions = slots
  at e_read = 1 stages); at e >= 2 sides in windows <= 3 always 0 (s0' < e), matching
  every sealed e >= 2 letter. lambda := multiset {(deg, ord)} of the monic-irreducible
  factorization of R_anch = the side residual (z-part none: endpoints nonzero).
- FC5 FLANKS: compositions (side raw widths, left|right of the read side) of the window
  span outside the read side. (z)-degenerate leftover span (no finite hull point, e.g.
  c0 = 0 exactly) counts as ONE pseudo-side of its width — horizontal data only, per
  SP.1's "heights and values forgotten"; any other reading would only ADD undecided
  reads, never letters.
- FC6 CANONICAL LIFTS (D4-R canonical policy, base-stage instance): recentering at
  psi = z - c on a slope-h e=1 side: t = p^h * (integer lift of c in [1, p-1]),
  Phi' = x - t (Taylor shift). Increment at psi (deg g, side (e,h)): standard lift
  D.5: Phi-hat = x^{eg} + sum_{psi_k != 0} p^{h(g-k)} * lift(psi_k) * x^{ek}
  (base realizers p^v*u-hat; matches the accepted D4-n3 gate's Phi1 = x^2+[s1]px+[s0]p^2).
- FC7 UNDECIDED-AT-N: valuations are read capped at N (v >= N undetermined). A read is
  DECIDED iff its full retained datum (side, digits/lambda, a, flanks) is constant over
  all completions of capped heights (checked over {N..4N} u {5N=inf proxy}); else it is
  tallied UNDECIDED (SP.6(a)) and contributes no letter. Any side with a capped
  endpoint is UNDECIDED.
- FC8 DEPTH 2 (SP.6(a)): root read + one continuation read per eligible branch
  (side, psi): recentering (e = g = 1) -> child window [0, mu] read in the recentered
  frame (tag POST-REC, group Q_mu); increment (e*g >= 2) -> Phi-hat development, child
  window [0,1] confirming read (tag POST-INC, group I(e*g, g)). W = 1 reads carry the
  verdict as selection (menu empty). No depth-3 move is taken.
- FC9 LOOP CHECK (b)(iv) at letter level: depth-2 walks cannot realize a loop EDGE;
  check = the realized depth-2 letters whose selection has (g,mu) = (1,W), W >= 2, are
  exactly the two sealed loop classes (Q2.3 sel (1,2); Q3's sel-(1,3) row) and no
  W = 1 letter carries a continuing selection.
- FC10 TALLIES: per-letter hit counts = chain occurrences (branch-weighted; same-shape
  factors count once per branch, per L11's selection-index discipline — realized means
  >= 1). Transition matrix over realized consecutive pairs (root letter -> depth-2
  letter), plus the root selection arm; UNDECIDED targets reported separately.
- FC11 INTERNAL ENGINE CHECKS (not sealed falsifiers; reported): (BOX)/(VERTEX) at
  every landing (D.8/D.10), (I-aug) slope > h at POST-REC sides, partition identity
  sum g*mu = l per read. Violations counted as engine faults and reported verbatim.

## S2 — FALSIFIERS (any single hit => gate FAILS; seal untouched)

F1 STRAYS: any decided realized read datum (tag, stage, e, l, a, flanks, lambda, sel)
   not among the 53 sealed letters. 0 tolerated. (A stray refutes SP-COMP's
   completeness claim at n = 3 — top diagnostic value; diagnose precisely.)
F2 ORPHANS: any letter predicted realized at that p (42 at p = 2, 51 at p = 3) with
   zero decided census hits — unless its absence is explained by the census DEPTH
   (must be noted, not silently tolerated).
F3 EXCLUSION VIOLATIONS: any of the sealed excluded letters (11 at p = 2 with
   lambda >= two distinct linears; 2 at p = 3 with lambda = {(1,1)^3}) realized; or an
   absence NOT matching its displayed field-size explanation.
F4 OFF-MENU: any realized consecutive read pair outside the sealed menu map
   (sel (1,1) -> Q1; (1,2) -> Q2; (1,3) -> Q3; (2,1) -> I(2,2); (3,1) -> I(3,3);
   e=2 -> I(2,1); e=3 -> I(3,1)). 0 tolerated.
F5 LOOP CLASSES: realized loop-typed letters (FC9) differ from exactly {Q2.3 sel(1,2),
   Q3 sel(1,3)-row}.

## S3 — POST-CENSUS VERDICT (appended after the run; seal untouched)

*(2026-07-27, census = case_mn3_gate.py, run after S0-S2 were committed.  Full log:
/tmp/mn3_census.out; machine-readable: results/case_mn3_results.json.  Both sealed
boxes exhaustive: p=2 N=8 all 2^24 = 16,777,216 boxes (2.8 s); p=3 N=5 all
3^15 = 14,348,907 (2.3 s).  Vectorized driver cross-validated letter-for-letter
against an independent scalar full enumeration at p=3 N=3: 0 mismatches.)*

| sealed check | p = 2, N = 8 | p = 3, N = 5 |
|---|---|---|
| (i) STRAYS (0 tolerated) | 0 — PASS | 0 — PASS |
| (ii) realized vs sealed | 42/42, all 11 exclusions absent (field size) — PASS | 45 realized vs SEALED 51; 2 exclusions absent OK; **6 further Q3 absences — FAIL AS SEALED** |
| (iii) off-menu transitions | 0 — PASS | 0 — PASS |
| (iv) loop classes | exactly {Q2.3 sel(1,2), Q3 sel(1,3)} — PASS | same — PASS |
| engine (FC11: BOX/VERTEX/I-aug/partition) | 0 faults | 0 faults |
| SP.6 worked witnesses | both PASS (R5{(2,1)}->I(2,2) incl. R1 sibling; R6 sel(1,3)->Q3 e=3) | — |
| undecided reads (reported) | root 74,352; rec 486,304; inc 4,737 | root 65,106; rec 559,620; inc 4,954 |

THE SIX p=3 ORPHANS (verbatim letter keys; all sel-carrying Q3 rows):
  Q3[e1 l1 a0 fl()|(1,1)]  (R1-copy, right flank (1,1))
  Q3[e1 l1 a1 fl(1)|(1)]   (R2-copy)
  Q3[e1 l1 a2 fl(1,1)|()]  (R3-copy, left flank (1,1))
  Q3[e1 l2 a0 fl()|(1) lam{(2,1)} sel(2,1)]   (R4-copy)
  Q3[e1 l2 a0 fl()|(1) lam{(1,2)} sel(1,2)]   (R4-copy)
  Q3[e1 l2 a0 fl()|(1) lam{(1,1)^2} sel(1,1)] (R4-copy)

ADJUDICATION — LEVEL-BUDGET EXCLUSIONS, NOT CATALOGUE DEFECTS.  Every one of the
six requires a MULTI-SIDE mu = 3 child window, and (I-aug) convexity forces its
height parameters past level-5 decidability: child slopes after a root sel-(1,3)
recentering are strictly decreasing integers-over-strides left of the vertex, so
  - the three R4-copies (side [0,2] e=1 + right side [2,3]) force slopes s1 > s2 >= 1,
    hence v(B'_0) = s2 + 2*s1 >= 5 = N: the left endpoint is UNDECIDABLE at N = 5;
  - the R2/R3-copies need the slot-0 point provably ABOVE the [1,2]-line extension
    (height-5 line): v(B'_0) >= 6 needed, undecidable at N = 5 (undecided-vs-collinear);
  - the R1-copy READS side [0,1]: needs v(B'_0) = s2 + s1' ... >= 6 EXACT: N >= 7.
CONFIRMATION (post-census diagnostics, outside the sealed configs, marked as such):
p=3 N=6 exhaustive 3^18 (0 strays, 0 faults): five of the six appear (hits 5,832-8,748);
only the R1-copy still absent, exactly as the arithmetic forces; constructed N=7
witnesses (f = g(x-1), g = x^3+3x^2+27x+729u, u = 1,2) realize the R1/R2/R3-copies at
depth 2.  All six are realized in the sealed p=2 N=8 box (hits 3,072-28,160), where
2-adic height 6 <= N-1 = 7 fits.  So the absences are deterministic consequences of
the SEALED LEVEL N = 5, provable from the catalogue's own budget inequalities — they
are NOT field-size absences, and the seal's clause (b)(ii) sanctions ONLY field-size
explanations: the sealed prediction "51/53 realized at p = 3, N = 5" is WRONG AS
DERIVED.  SP.6's own height clause ("the letter is realized if realized at ANY height
within the level budget") already names the mechanism; the sealed list failed to apply
it at p = 3, N = 5 (at p = 2, N = 8 it is vacuous, and the gate passes in full).

GATE VERDICT: **p = 2 PASS (all families); p = 3 FAIL AS SEALED** — one family,
(b)(ii) two-sided realization, by exactly the six letters above; every other family
(strays, exclusions, menus, loops, engine checks, witnesses) passes at both primes.
What the failure impugns: the SP.6 realizability LIST's derivation at p = 3, N = 5
(a prediction-derivation error, Case-K-precedent class), i.e. either the list or the
sealed level must move (51/53 first becomes correct at N = 7 per the diagnostics).
What it does NOT impugn: SP-COMP/SP-FIN/SP-OUT content — 0 strays and 0 off-menu
transitions over ~31.1M sealed boxes (+ 3^18 diagnostic), i.e. every decided read of
every chain to depth 2 is a catalogued letter reached by a sealed menu edge; kernel
D4R.0-K remains OPEN per SP.6(c) (a pass here is not kernel support), and the n = 3
POST-INC limitation stands as recorded.  RE-SEAL of the p = 3 realizability clause
(N = 7 box, or the level-corrected 45/53-at-N=5 list) is the required follow-up.
