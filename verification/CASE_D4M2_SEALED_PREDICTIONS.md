# CASE-D4M2 SEALED GATE — n = 4 root-only shape, branch multiplicity ≥ 2 (sum law vs event)

*(2026-07-26. SEALED BEFORE ANY CENSUS CODE EXISTED OR ANY Z_p BOX WAS EXAMINED.
Sources: MOVES_2026-07-24.md live §D4-R rev 6 (L1–L12, D4R.0/1/2/4, the REV-6 CHECK
display at D4R.1) and FABLE_VERIFY_D4R_2026-07-26.md finding F1. This is the first
gate on the mult ≥ 2 regime: rev 6's exact SUM law (D4R.1-SUM/D4R.4-SUM) vs the
strictly smaller EVENT (D4R.1-EV strict when mult ≢ 1) — never census-tested before.
Case-K discipline: predictions are never adjusted after the census; any sealed
falsifier fires ⟹ the gate FAILS and this file is not touched. The only pre-seal
computation was pure F_p residual algebra (the branch tables in S2 — root
multiplicities of monic quartic residuals over F_p; no Z_p boxes, no enumeration
of inputs), per the CASE_D4N3 precedent.)*

## S0 — FREE CHOICES MADE (beyond the note text; every choice displayed)

- FC1 PREFIX: P̂₀ := the note's own refutation-instance shape (rev-6 check at D4R.1):
  n = 4, ROOT-ONLY (|P̂₀| = 1 read), node (e₀,h₀,g₀,μ₀,a₀) = (1,1,1,2,0), full-span
  side (0,4)–(4,0), slope h₀/e₀ = 1/1. The note pins the side; the length (root-only)
  is pinned here to keep the mult ≥ 2 phenomenon at the tested read.
- FC2 DIGIT/LEVEL CONVENTIONS (D4N3-style, adopted): box = monic quartics
  f = x⁴ + c₃x³ + c₂x² + c₁x + c₀, (c₃,c₂,c₁,c₀) ∈ Z_p⁴; μ(·) = #{f mod p^N ∈ ·}·p^{−4N}.
  d_j := level-(4−j) digit of c_j (j = 0..3); monic lead slot 4 excluded (no
  coordinate); interior digits d₃,d₂,d₁ free in F_p (0 allowed); endpoint d₀ ≠ 0.
- FC3 BRANCH ELIGIBILITY (L2's display, exact order): a branch of the cell with
  residual R₀(z) = z⁴ + d₃z³ + d₂z² + d₁z + d₀ is a monic linear ψ = z − r with
  ord_ψ R₀ = 2 EXACTLY (deg ψ = g₀ = 1, ord = μ₀ = 2). Roots of multiplicity 1, 3, 4
  are NOT branches of this shape. r ≠ 0 automatic (d₀ ≠ 0).
- FC4 REALIZABILITY: at a root-only prefix NO (NA)/(HV)/(SAE) predicate applies (all
  three relate a read to its predecessor; L3 rev 6); the canonical lift is carried but
  pins nothing. So Pref(P̂₀) = { (digit cell, r) : cell realized the side pattern,
  (z−r)² ∥ R₀ } — C_P̂₀(p) counts ψ-labels (the note's phrase), NOT cells.
- FC5 W-EXTENT (D4N3 FC6 adopted): W(P̂₀) = w₀·d₀count = 1·4 = 4 (monic lead excluded,
  endpoint included).
- FC6 SECOND PRIME: p = 3 (shape realizable at p = 2 AND 3; p = 3 chosen because it
  REALIZES mult ≥ 2 — one (z−a)²(z−b)² cell; at p = 2, E = C = 1, gap 0: the m ≥ 2
  regime is empty there. p = 2 recorded, not run).
- FC7 LEVELS + FEASIBILITY DEVIATION, stated: N(P̂₀) = 5 (S3) is the minimal
  admissible level; the full level-5 box is p^20 boxes (5^20 ≈ 9.5·10¹³, 3^20 ≈
  3.5·10⁹). The tasking brief's arithmetic ("p=5: N=5 → 9.7·10⁶") corresponds to no
  power of the actual box and is set aside. DEVIATION: p = 5 exhausts the ESSENTIAL
  BOX — (c₃ mod 5², c₂ mod 5³, c₁ mod 5⁴, c₀ mod 5⁵), 5^14 = 6,103,515,625 boxes,
  the minimal exhaustive domain on which every stratum equation of every η is
  defined (T(η,⊤) reads c_j only at levels ≤ 4−j) — with level-5/6 counts by the
  displayed multiplier p^{4N−14} (free digits at N = 5: c₃ lv 2–4, c₂ lv 3–4, c₁
  lv 4, c₀ none = p⁶). p = 3 runs BOTH the FULL literal level-5 box 3^20 =
  3,486,784,401 (D4N3-precedent scale) AND the essential box 3^14 = 4,782,969, so
  the multiplier itself is an ENUMERATED check at the prime that realizes mult ≥ 2.
- FC8 MULT AND HISTOGRAM: mult_P̂₀(f) := #{ r : (cell(f), z−r) ∈ Pref(P̂₀), f in its
  stratum } (D4R.1's corollary object); the histogram counts BOXES by mult value.

## S1 — The prefix P̂₀, pinned exactly

ν₀ — ROOT READ (key x), the only read:
- Cluster: c₃ ≡ c₂ ≡ c₁ ≡ c₀ ≡ 0 (mod p) — 4 pins at level 0.
- Side (0,4)–(4,0), slope 1, single side, full span. Below-line strip zeros:
  c₀ levels 1,2,3 (3 pins); c₁ levels 1,2 (2); c₂ level 1 (1) — 6 pins.
- On-line digits (4 pins): d₃ = (c₃ lv 1), d₂ = (c₂ lv 2), d₁ = (c₁ lv 3),
  d₀ = (c₀ lv 4) ≠ 0 (endpoint: v(c₀) = 4 exactly). Equivalent valuation form:
  v(c₃) ≥ 1, v(c₂) ≥ 2, v(c₁) ≥ 3, v(c₀) = 4.
- Node data: (1,1,1,2,0); descend at ψ = z − r, ord exactly 2 (FC3). The prefix ends
  at the read: no key lift applied, no frame-1 objects exist in this gate.
- STRATUM (the F1 point, sealed): S(η,⊤) for η = (cell, r) is the DIGIT conditions
  above ONLY — independent of r. Two η's over one cell have LITERALLY EQUAL strata;
  the sum law counts them twice, the event once. This is what the gate tests.

## S2 — Branch tables (pre-seal F_p algebra; census must re-derive independently)

Factorization types with an exact-double root, all roots ≠ 0 (unique factorization
⟹ disjoint types, injective parametrization):
 (a) (z−a)²(z−b)(z−c), a ∈ F_pˣ, {b,c} ⊂ F_pˣ∖{a}: (p−1)·C(p−2,2) cells, mult 1.
 (b) (z−a)²·q, q monic irreducible quadratic: (p−1)·(p²−p)/2 cells, mult 1.
 (c) (z−a)²(z−b)², {a,b} ⊂ F_pˣ: C(p−1,2) cells, mult 2. No cell has mult ≥ 3
     (deg 4 < 3·g₀μ₀ = 6 forbids a third exact-double root).
Counts (closed form AND brute-force recounted pre-seal, both methods agree):
  p = 5: type (a) 12, (b) 40, (c) 6 ⟹ E = 58 cells, C = 64 branches, gap = 6.
         Histogram over cells: {mult 1: 52, mult 2: 6}. Per-branch totals: 16 per
         r ∈ {1,2,3,4} (the z ↦ az symmetry).
  p = 3: type (a) 0, (b) 6, (c) 1 ⟹ E = 7, C = 8, gap = 1. Histogram: {1: 6, 2: 1}.
         Per-branch totals: 4 per r ∈ {1,2}.
  p = 2 (recorded, not run): E = C = 1 (cell (1,0,1,1) = (z+1)²(z²+z+1)), gap 0.
The six mult-2 cells at p = 5, (d₃,d₂,d₁,d₀) ↦ branch set:
  (0,2,0,1) ↦ {2,3}; (0,3,0,1) ↦ {1,4}; (1,3,2,4) ↦ {3,4}; (2,2,1,4) ↦ {1,3};
  (3,2,4,4) ↦ {2,4}; (4,3,3,4) ↦ {1,2}  [THE refutation cell: R₀ = (z−1)²(z−2)²].
The p = 3 table, complete: mult-1: (0,2,1,2)↦{1}; (0,2,2,2)↦{2}; (1,1,0,2)↦{2};
  (1,2,1,1)↦{1}; (2,1,0,2)↦{1}; (2,2,2,1)↦{2}; mult-2: (0,1,0,1) ↦ {1,2}
  [R₀ = z⁴+z²+1 = (z−1)²(z−2)²].

## S3 — The ledger, every number derived

  A(P̂₀) = 4 cluster + 6 below-line + 4 on-line = 14   (L9; = the note's displayed 14)
  W(P̂₀) = 1·4 = 4 [FC5];  A_net = 14 − 4 = 10
  M(P̂₀) = m̄₀ = ⌊deg R_anch,0/(g₀μ₀)⌋ = ⌊(w'₀/e₀)/2⌋ = ⌊4/2⌋ = 2   (L11 — the FIRST
    gate instance with M > 1; the mult-2 cells realize m₀ = 2 = m̄₀: bound TIGHT)
  N(P̂₀) = 1 + (largest pinned base level = 4, at c₀) = 5   (§C C.2/L12; same for
    every η ∈ Pref(P̂₀) and both primes)
  Theorem C(b) per η: μ(S(η,⊤)) = p^{−14}, i.e. p^{4N−14} members at level N ≥ 5.

## S4 — SEALED PREDICTIONS (exact integers; ANY mismatch = FAIL)

Essential-box counts (enumerated literally: p=5 over 5^14, p=3 over 3^14; each η's
stratum pins all 14 essential digits, so each η occupies EXACTLY ONE essential box):
 P1 SUM (branch-weighted, D4R.1-SUM): Σ_η #(boxes in S(η,⊤)) = C_P̂₀(p)·p^{14−14}:
    p = 5: 64.   p = 3: 8.
 P2 EVENT (≥ 1 branch): E(p) boxes: p = 5: 58.  p = 3: 7.  STRICTLY below P1.
 P3 GAP = P1 − P2 = the mult ≥ 2 overcount: p = 5: 6.  p = 3: 1.  In mass form
    (×p^{−14}): 6·5^{−14} — LITERALLY the note's displayed rev-5 overcount — and
    1·3^{−14}. (D4R.1-EV equality fails: mult ≢ 1 at both primes.)
 P4 HISTOGRAM of boxes by mult: p = 5: {1: 52, 2: 6, ≥3: 0}. p = 3: {1: 6, 2: 1, ≥3: 0}.
 P5 CELL REGISTRY: the realized cells and their branch sets are EXACTLY S2's tables
    (type counts 12/40/6 at p=5, 0/6/1 at p=3; the six p=5 mult-2 cells and the full
    p=3 seven-cell table verbatim; per-branch totals 16/16/16/16 and 4/4; max
    per-cell branch count = 2 = m̄₀, L11 tight).
Level-N counts (SUM = C·p^{4N−14}, EVENT = E·p^{4N−14}, GAP = (C−E)·p^{4N−14};
p=3 N=5 enumerated LITERALLY over the full 3^20 box; p=3 N=6 = R2×3⁴ ≡ R3×3^10;
p=5 levels by the FC7 multiplier from the essential census):
 P6 p=5 N=5: SUM 1,000,000; EVENT 906,250; GAP 93,750; hist {1: 812,500, 2: 93,750}.
    p=5 N=6: SUM 625,000,000; EVENT 566,406,250; GAP 58,593,750;
             hist {1: 507,812,500, 2: 58,593,750}.
    p=3 N=5: SUM 5,832; EVENT 5,103; GAP 729; hist {1: 4,374, 2: 729}.
    p=3 N=6: SUM 472,392; EVENT 413,343; GAP 59,049; hist {1: 354,294, 2: 59,049}.
    N-ratio between the two levels = p⁴ exactly, per prime, per quantity.
 P7 PER-η FIBERS (Theorem C(b) + L9, enumerated at p=3 N=5): EVERY η ∈ Pref(P̂₀(3))
    (all 8 branches over 7 cells) has EXACTLY 3⁶ = 729 members in the 3^20 box; the
    mult-2 cell's 729 boxes EACH carry BOTH branches (equal strata, F1 displayed).
 P8 SPOT CHECK (the note's refutation member): f = x⁴ + 20x³ + 75x² + 375x + 2500,
    essential coordinates (20, 75, 375, 2500): cell (4,3,3,4), mult = 2, branch set
    {z−1, z−2} exactly.
 P9 POOL BOUND (D4R.2, first M > 1 exercise): C ≤ M·p^W: 64 ≤ 2·5⁴ = 1250 and
    8 ≤ 2·3⁴ = 162; masses: event ≤ sum = C·p^{−14} ≤ M·p^{−A_net} = 2·p^{−10}.

## S5 — Census specification (written into case_d4m2_gate.py AFTER this seal)

- Branch tables re-derived IN-SCRIPT by an INDEPENDENT method (Taylor shift
  R(z+r) mod p: mult exactly 2 ⟺ c₀ = c₁ = 0, c₂ ≠ 0 — the pre-seal method was
  synthetic-division stripping; both exact in every characteristic used).
- R1 (p=5): exhaustive essential box 5^14, chunked numpy; per box, per branch
  r ∈ {1..4}: membership = (10 zero-digit pins) ∧ (tuple, r) ∈ table. Tallies:
  branch-weighted sum, event, histogram, per-branch totals, realized-cell registry.
- R2 (p=3): exhaustive FULL level-5 box 3^20 (every (c₃,c₂,c₁,c₀) mod 3⁵), same
  classifier via genuine valuation reads; per-η fiber counts materialized.
- R3 (p=3): exhaustive essential box 3^14; CONSISTENCY: every R2 tally = 3⁶ × the
  R3 tally (the FC7 multiplier, enumerated).
- R4 DEEPENING STABILITY (sampled): 10⁶ random boxes per prime at depth
  (c₃ mod p⁴, c₂ mod p⁵, c₁ mod p⁶, c₀ mod p⁷), classified by the same
  valuation-reading code path at full depth: classification must agree with the
  essential-truncation classification box-by-box (cap-analog of D4N3's F6).
- Long output → /tmp/d4m2_census.out; machine-readable →
  verification/results/case_d4m2_results.json.

## S6 — FALSIFIERS (any single hit ⟹ gate FAILS; this file is not touched)

F1 any exact-count mismatch in P1–P4 or P6 (sum, event, gap, histogram, any config).
F2 any cell-registry mismatch (P5): a realized cell not in S2's tables, a missing
   cell, a wrong branch set, any cell with > 2 branches, or in-script table ≠ S2.
F3 any per-η fiber ≠ 729 at p=3 N=5, or any mult-2-cell box not carrying both
   branches (P7).
F4 spot-check failure (P8).
F5 pool-bound violation (P9).
F6 any R2-vs-R3 multiplier mismatch, or any R4 deepening classification change.

## S7 — What this gate does NOT test (honest perimeter)

- Root-only prefix: no (NA)/(HV)/(SAE) is exercised, no canonical lift is applied,
  no frame-1 objects, no depth ≥ 1 transport. Kernel D4R.0-K's derivation burden is
  textual and untouched (per §D4-R.6's precedent: a PASS does not close it; a FAIL
  on P1/P2/P3/P4 REFUTES rev 6's D4R.1/D4R.4 as specified at this shape).
- p=5 level-N counts rest on the displayed essential-multiplier fact (FC7); the
  multiplier is enumerated only at p=3 (R2 vs R3) and sampled at p=5 (R4).
- Cross-shape cover (Σ_P̂ μ(P̂) > 1, D4-R.5's consumer duty): the same cells carry
  branches of OTHER shapes (e.g. simple roots, the μ=4 shape); not classified here.
- Value-aggregated claims ([1v]), menu/exhaustiveness ([2a]/[2b]/[5]), resummation
  ([3]): all deferred per §D4-R.5. Polynomiality of C_P̂₀(p) in p: NOT claimed;
  the closed forms in S2 are display only, the seal is the per-p enumeration.

## S8 — POST-CENSUS VERDICT (appended after the run; no prediction touched)

*(2026-07-26, census = case_d4m2_gate.py, run after S0–S7 were committed. Full log:
/tmp/d4m2_census.out; machine-readable: results/case_d4m2_results.json. In-script
branch tables re-derived by the independent Taylor-shift method; 33 sealed verdict
families checked; NO falsifier fired.)*

| sealed | p=5 (essential 5^14) | p=3 (essential 3^14 + LITERAL full 3^20) |
|---|---|---|
| P1 SUM (branch-weighted) | 64 ✓ | 8 ✓; N=5 literal 5,832 ✓ |
| P2 EVENT (strictly below) | 58 ✓ (< 64 ✓) | 7 ✓ (< 8 ✓); literal 5,103 ✓ |
| P3 GAP = mult≥2 overcount | 6 ✓ (= 6·5⁻¹⁴ mass) | 1 ✓; literal 729 = 3⁶ ✓ |
| P4 histogram {1, 2, ≥3} | {52, 6, 0} ✓ | {6, 1, 0} ✓; literal {4374, 729, 0} ✓ |
| P5 registry + branch sets | 58 cells, 6 mult-2 verbatim ✓, perbr 16×4 ✓ | 7 cells verbatim ✓, perbr 4/4 ✓ |
| P6 level counts N=5/N=6 | 1,000,000/906,250/93,750 and ×5⁴ ✓ | 5,832/5,103/729 (LITERAL) and ×3⁴ ✓ |
| P7 per-η fibers (literal) | — (1 essential box per η ✓) | all 8 branches exactly 729 ✓; the mult-2 cell (0,1,0,1): BOTH fibers 729 on the SAME boxes, event 729, sum 1458 ✓ |
| P8 refutation member | cell (4,3,3,4), branches {z−1,z−2} ✓ | — |
| P9 pool bound (M = 2) | 64 ≤ 1250; masses ✓ | 8 ≤ 162; masses ✓ |
| F6 table/multiplier/deepening | in-script = S2 ✓; 10⁶ deepenings 0 mism. ✓ | R2 = 3⁶×R3 every tally ✓; unhoisted = hoisted ✓; 10⁶ deepenings 0 ✓ |

GATE VERDICT: **PASS** — 33/33 sealed verdict families exact; 0 double-counts
beyond the sealed multiplicities, 0 orphans; ~9.6·10⁹ boxes classified
(5^14 + 3^14 + 3^20 + the unhoisted cross-pass). The mult ≥ 2 regime is now
census-tested for the first time: the exact SUM law (D4R.1-SUM/D4R.4-SUM) and the
STRICT event bound (D4R.1-EV/D4R.4-EV with mult ≢ 1) both hold verbatim at the
note's own F1 refutation shape, including the note's displayed 6·5⁻¹⁴ overcount
and the equal-strata double-fiber at the p=3 mult-2 cell. Also first exercises:
M(P̂) = 2 > 1 (D4R.2's p-free factor, bound tight m₀ = m̄₀ = 2) and the L11
selection index separating same-cell branches. What this pass does NOT certify:
unchanged, S7 verbatim (kernel D4R.0-K's textual burden in particular).
