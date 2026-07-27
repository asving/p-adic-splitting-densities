# CASE-SIB SEALED GATE — the joint sibling kernel (SIB): product law of sibling continuation events at branching cells

*(2026-07-27. SEALED BEFORE ANY CENSUS CODE EXISTED. Sources: ASSEMBLY_PLAN_2026-07-26.md
§4t — (SIB)'s statement, its mechanism clause, its HONEST-RISK clause, the SIB-gate spec —
plus MOVES_2026-07-24.md §C REV 2 (C.1.5/(ZC), Theorem C(a)/(b), admissible Z) and
CASE_D4M2_SEALED_PREDICTIONS.md (the F1 cell's root ledger, adopted verbatim). Case-K
discipline: any sealed falsifier fires ⟹ the gate FAILS and this file is not touched.
Pre-seal computation: exact digit/carry algebra of the two branch developments and the
Res-constancy displays (S2) — display only, like d4m2's S2 branch tables; the census
re-derives every digit independently by literal integer development.)*

## S0 — FREE CHOICES (every choice beyond the plan/§C text, displayed)

- FC1 LAYER-1 CELL: the F1 branching cell, verbatim from d4m2: p = 5, n = 4, root-only
  prefix P̂₀ = (1,1,1,2,0) full-span side (0,4)–(4,0), digit cell c = (d₃,d₂,d₁,d₀) =
  (4,3,3,4), R₀ = z⁴+4z³+3z²+3z+4 = (z−1)²(z−2)² over F₅; branch set {b₁: ψ = z−1,
  b₂: ψ = z−2}, μ = 2 each, both CONTINUING (μ ≥ 2: no τ-clause fires). Σ_c := the
  cell's stratum locus (14 pins: 4 cluster + 6 below-line + 4 on-line digits, d4m2 S1;
  branch-INDEPENDENT — F1's equal strata: the two branches share one locus).
- FC2 LIFTS: branch b_r's continuation is read on the development of f at
  Φ̂_r := x − r·p (the naive lift r·5 of the branch root; §C's lift-translation remark
  covers other admissible lifts — the gate tests (SIB) for THESE displayed events).
- FC3 READ WORDS (the sibling-subtree events are word events S = {W_r ∈ A}): develop
  f = Σ_j B_j^{(r)}·(x − 5r)^j exactly over ℤ;
    W_r := (u_r, v_r, w_r) := (digit₄(B₁^{(r)}), digit₅(B₀^{(r)}), digit₆(B₀^{(r)})) ∈ F₅³
  (digit_ℓ = the p-adic level-ℓ digit). WHY this is the depth-1 read datum: on Σ_c the
  landing state at branch r (sealed as P6) is v(B₂) = 2 with unit digit 1 (the pinned
  window vertex (2,2)), v(B₁) ≥ 4, v(B₀) ≥ 5 (the vanishing-digit valuation jumps:
  digit₃(B₁) = R₀'(r) = 0, digit₄(B₀) = R₀(r) = 0 identically on the cell). The depth-1
  hull on the window [0,2] hangs from (2,2):
    v_r ≠ 0 ⟺ RAM side (0,5)–(2,2), slope 3/2, e = 2 → τ-irr leaf (2,1); endpoint digit v_r;
    v_r = 0, w_r ≠ 0 ⟺ slope-2 side (0,6)–(2,2), residual z² + u_r·z + w_r (lead = vertex
      unit 1): split (two (1,1) leaves) / irreducible ((1,2) leaf) / double root (deeper);
    v_r = 0, w_r = 0 ⟺ deeper reads (undecided at this reading depth).
  Digits of W_r beyond a stratum's own read are admissible-Z coordinates (§C C.2) — every
  singleton {W_r = w} is a Theorem-C event (S1).
- FC4 BOX (DEVIATION from d4m2's essential box, which stops at c₀ level 4 and contains
  NO continuation digit — extension is REQUIRED for any continuation gate): the minimal
  word-sufficient box B22 := (c₃ mod 5⁴, c₂ mod 5⁵, c₁ mod 5⁶, c₀ mod 5⁷) (5²² boxes).
  Σ_c ∩ B22 = pins + exactly 8 free digits (e₃,e₂,e₁,e₀; g₃,g₂,g₁,g₀) at levels
  (c₃: 2,3; c₂: 3,4; c₁: 4,5; c₀: 5,6) → 5⁸ = 390,625 members, enumerated EXHAUSTIVELY
  by construction (deeper digits do not exist in B22; the words are functions of B22 —
  S2's algebra, re-checked by the census's deepened pass, P13-style falsifier F2).
- FC5 LAYER 2 — MIXED SHAPES (the plan's own cubic cell): p = 2, n = 3, root full side
  (0,3)–(3,0) slope 1, digit cell (d₂,d₁,d₀) = (0,0,1), R₀ = z³+1 = (z+1)(z²+z+1) over
  F₂: branches b_L = z−1 (linear, μ = 1 → τ-hen leaf (1,1)) and b_Q = z²+z+1 (quadratic,
  μ = 1 → τ-irr leaf (1,2)). BOTH BRANCHES HALT. DISPLAYED STRUCTURAL FINDING (pre-seal):
  at n ≤ 4 NO branching cell has two CONTINUING siblings of DIFFERENT shapes — a branch
  continues iff μ ≥ 2 (μ = 1 saturates the Montes certificate E·F = e·g = cluster degree,
  τ-irr/τ-hen fires), and two continuing different-shape siblings need cluster degrees
  g₁μ₁ ≠ g₂μ₂ pattern with each g·μ ≥ 2, minimum total 2 + 3 = 5 > 4. So the plan's
  mixed-shape layer is NECESSARILY a below-halt gate: the tested events are the engine's
  BELOW-HALT refinement reads (VP-2: continuations "exist syntactically but are not
  walked") — the all-depth face of accepted JOINT-D1's refinement object, at MIXED
  shapes (δ = 1 vs δ = 2 residue fields). Events:
    W_L := (t₁, t₂) ∈ F₂², the next two digits of the Hensel root α of the linear
      factor: α = 2(1 + 2t₁ + 4t₂ + …);
    W_Q := (a₂, b₃) ∈ F₂², the next O_δ-digit (2 base digits) of the quadratic factor
      h = x² + ax + b (residual z²+z+1): a = 2(1 + 2a₂ + …), b = 4(1 + 2b₃ + …).
- FC6 LAYER-2 BOX: (c₂, c₁, c₀) mod 2⁸ = 2²⁴ boxes (the plan's box). Σ_c pins 9 digits
  (c₂: levels 0,1; c₁: 0,1,2; c₀: 0,1,2 + digit level 3 = 1) → free digits c₂: 2–7,
  c₁: 3–7, c₀: 4–7 → 2¹⁵ = 32,768 members.
- FC7 LAYER 3 — THREE-WAY (m = 3): all-continuing m = 3 needs degree ≥ 6 (FC5's
  argument): NOT available at n ≤ 4; sealed instead as (SIB)'s m = 3 instance at
  depth 0 (the accepted-JOINT-D1 face — confirmatory, honestly labeled): p = 5, n = 3,
  cell (d₂,d₁,d₀) = (4,1,4), R₀ = z³+4z²+z+4 = (z−1)(z−2)(z−3) over F₅, three Hensel
  branches; W_j := t_j, the next root digit: α_j = 5j + 25t_j + … (j = 1,2,3). Box
  (c₂,c₁,c₀) mod 5⁵ = 5¹⁵; Σ_c pins 9 (c₂: 0 + digit lv 1; c₁: 0,1 + digit lv 2;
  c₀: 0,1,2 + digit lv 3) → free c₂: 2–4, c₁: 3,4, c₀: 4 → 5⁶ = 15,625 members.
- FC8 EXACTNESS: all identities in INTEGER COUNTS N(·) over the layer's member
  enumeration; product identity form N(S₁∩S₂)·N(Σ_c) = N(S₁)·N(S₂), m = 3 form
  N(S₁∩S₂∩S₃)·N(Σ_c)² = N(S₁)·N(S₂)·N(S₃). No floats anywhere.

## S1 — The derivation: what §C predicts (marginals) and what ONLY (SIB) predicts (joints)

MARGINALS (§C per-branch — Theorem C(b) + admissible Z; PER-PATH content only, D4R0K O2):
- Layer 1, branch r, every word w = (u,v,w₆) ∈ F₅³: μ(W_r = w | Σ_c) = 5⁻³. Display per
  species: RAM (v ≠ 0): E_fresh(ν₁^{(r)}) = {endpoint value digit at (slot 0, ht 5) = v},
  vol 5⁻¹; u and w₆ are admissible-Z digits (free on Σ: ht 4 > floor 3 at slot 1; ht 6 >
  exact-valuation 5 at slot 0): vol(Z) = 5⁻². Slope-2 cell (v = 0, w₆ ≠ 0): E_fresh =
  {strip zero at (slot 0, ht 5)} ∪ {on-line digit u at (slot 1, ht 4)} ∪ {endpoint digit
  w₆ at (slot 0, ht 6)}: vol 5⁻³. Deep (v = w₆ = 0): two strip zeros + Z-digit u: 5⁻³.
- Layer 2: μ(W_L = x | Σ_c) = 2⁻² and μ(W_Q = y | Σ_c) = 2⁻² for every x, y ∈ F₂²
  (each digit one fresh below-halt read coordinate; b_Q's F₄-digit = 2 base digits,
  §C BLOCK CONVENTION).
- Layer 3: μ(t_j = t | Σ_c) = 5⁻¹ for every t, j.
JOINTS ((SIB) — the kernel under test; nothing accepted implies these):
- Layer 1: μ(W₁ = w₁ ∧ W₂ = w₂ | Σ_c) = 5⁻⁶ for EVERY pair: (W₁, W₂) uniform on F₅⁶.
- Layer 2: μ(W_L = x ∧ W_Q = y | Σ_c) = 2⁻⁴ for all 16 pairs.
- Layer 3: full triple law uniform: μ(t₁,t₂,t₃ = s,t,u | Σ_c) = 5⁻³, all 125 cells.

## S2 — Pre-seal digit algebra (display only; the census re-derives by literal development)

Layer 1, exact integer carries (f = x⁴+c₃x³+c₂x²+c₁x+c₀; c₃ = 5(4+5e₃+25g₃+…),
c₂ = 25(3+5e₂+25g₂+…), c₁ = 125(3+5e₁+25g₁+…), c₀ = 625(4+5e₀+25g₀+…)):
- TRANSPORTED STATE (cell data, no fresh digit): digit₂(B₂^{(r)}) = 1 for both r
  (6r²+3·4·r+3 = 21, 51 → 1 mod 5); digit₃(B₁^{(r)}) = 0 (4r³+12r²+6r+3 = 25, 95 ≡ 0);
  digit₄(B₀^{(r)}) = R₀(r) with carries: 15, 70 ≡ 0. Hence v(B₂) = 2 unit, v(B₁) ≥ 4,
  v(B₀) ≥ 5 identically on Σ_c — the two vanishing-digit valuation jumps.
- FRESH-DIGIT FORMS (carry constants displayed):
    u₁ = (3e₃+2e₂+e₁) mod 5            [carry ⌊25/5⌋ = 5 ≡ 0]
    v₁ = (3 + e₃+e₂+e₁+e₀) mod 5       [carry ⌊15/5⌋ = 3]
    w₁ = (⌊T₅⁽¹⁾/5⌋ + g₃+g₂+g₁+g₀) mod 5,  T₅⁽¹⁾ := 3 + e₃+e₂+e₁+e₀
    u₂ = (4 + 2e₃+4e₂+e₁) mod 5        [carry ⌊95/5⌋ = 19 ≡ 4]
    v₂ = (4 + 3e₃+4e₂+2e₁+e₀) mod 5    [carry ⌊70/5⌋ = 14; T₅⁽²⁾ := 14+8e₃+4e₂+2e₁+e₀]
    w₂ = (⌊T₅⁽²⁾/5⌋ + 3g₃+4g₂+2g₁+g₀) mod 5
- MECHANISM DIAGNOSTIC (sealed as a FINDING, not a falsifier): literal pool-coordinate
  DISJOINTNESS FAILS at this cell — both siblings' words pull back to the SAME 8 base
  digits (e, g). The product law is nevertheless predicted EXACT, by JOINT UNIMODULARITY:
  (u₁,v₁,u₂,v₂) is an affine BIJECTION of (e₃,e₂,e₁,e₀) (matrix rows (3,2,1,0),
  (1,1,1,1),(2,4,1,0),(3,4,2,1), det ≡ 1 mod 5), and for each fixed e, (w₁,w₂) is an
  affine surjection of (g₃,g₂,g₁,g₀) with independent forms (1,1,1,1),(3,4,2,1) —
  equal fibers 5². So (SIB)'s HONEST-RISK clause is the operative one: the kernel
  survives in its MEASURE form; the mechanism clause's literal base-coordinate
  disjointness is refuted at every branching cell of this type (shared frame digits).
Layer 2 mechanism display: f = g·h exactly (g = x−α linear, h = x²+ax+b, Hensel on the
distinct residual factors); the factorization map has Jacobian |Res(g,h)|₂ = |h(α)|₂ =
2⁻² CONSTANT on Σ_c (h(α) = 4·h̃(ζ), h̃ ≡ z²+z+1, ζ ≡ 1: h̃(ζ) ≡ 1 mod 2): uniform f-mass
pushes to PRODUCT measure on (α; a,b) — the JOINT-D1 route, mixed-shape face.
Layer 3 mechanism display: |f'(α_j)|₅ = 5⁻² constant (v(α_i−α_j) = 1, i ≠ j): product
measure on (α₁, α₂, α₃).

## S3 — SEALED PREDICTIONS (exact integers; ANY mismatch = the named falsifier fires)

Layer 1 — N(Σ_c) = 390,625 members of Σ_c ∩ B22:
 P1 MARGINAL WORDS: N(W_r = w) = 3,125 for EVERY w ∈ F₅³ and both r — 250 equalities.
 P2 JOINT WORDS (THE (SIB) TEST): N(W₁ = w₁ ∧ W₂ = w₂) = 25 for EVERY one of the
    15,625 pairs — the full contingency EXACTLY uniform; equivalently the product
    identity N(W₁=w₁ ∧ W₂=w₂)·390,625 = N(W₁=w₁)·N(W₂=w₂) at every pair.
 P3 FAMILY A (symmetric single-digit cells): S₁ = {v₁ = 1}, S₂ = {v₂ = 2}:
    N(S₁) = 78,125; N(S₂) = 78,125; N(S₁∩S₂) = 15,625; 78,125² = 15,625·390,625.
 P4 FAMILY B (asymmetric: full word cell × RAM-digit cell): S₁ = {W₁ = (0,0,1)} (the
    slope-2 cell with residual z²+1, split type), S₂ = {v₂ = 2}:
    N(S₁) = 3,125; N(S₂) = 78,125; N(S₁∩S₂) = 625; 3,125·78,125 = 625·390,625.
 P5 FAMILY C (union × union): S₁ = {b₁ SPLITS} = {v₁ = 0, (u₁,w₁) ∈ {(2,2),(1,3),
    (0,4),(0,1),(4,3),(3,2)}} (6 words = the 6 two-distinct-nonzero-root residuals);
    S₂ = {b₂ RAM} = {v₂ ≠ 0} (100 words): N(S₁) = 18,750; N(S₂) = 312,500;
    N(S₁∩S₂) = 15,000; 18,750·312,500 = 15,000·390,625.
 P6 TRANSPORTED STATE: on ALL 390,625 members, both r: digit₂(B₂^{(r)}) = 1,
    digit₃(B₁^{(r)}) = 0, digit₄(B₀^{(r)}) = 0 — zero exceptions; and the branch table
    re-derived in-script confirms cell (4,3,3,4) ↦ branch set {1,2} (d4m2 P8 spot).
 P7 OUTCOME-CLASS COLLAPSE (per-branch marginals, each r): RAM 312,500; slope-2 split
    18,750; slope-2 inert (irreducible residual) 31,250; slope-2 double-root 12,500;
    deep (v = w = 0) 15,625. [Σ = 390,625]
 P8 FORM CHECK: S2's displayed forms match the literally-developed digits on all
    members (falsifier F3 — indicts the display, not the count predictions).
Layer 2 — N(Σ_c) = 32,768 members of Σ_c ∩ 2²⁴-box:
 P9  MARGINALS: N(W_L = x) = 8,192 ∀x ∈ F₂²; N(W_Q = y) = 8,192 ∀y ∈ F₂².
 P10 JOINT: N(W_L = x ∧ W_Q = y) = 2,048 at all 16 pairs; 8,192² = 2,048·32,768.
 P11 UNION PAIR: S₁ = {t₁ = 0}, S₂ = {(a₂,b₃) ∈ {(0,0),(1,1)}}: N(S₁) = N(S₂) =
     16,384; N(S₁∩S₂) = 8,192; 16,384² = 8,192·32,768.
 P12 LITERAL BOX: #(Σ_c ∩ 2²⁴ box) = 32,768 by literal membership classification of
     all 16,777,216 boxes (validates the pin/constructed-member count).
 P13 STABILITY: every word is a function of the sealed box — deepened re-computation
     (random digits beyond the box, ≥ 10⁵ samples per layer) changes NO word (also run
     at Layers 1 and 3; Layer 1 additionally: the FULL 5¹² (e,g,h)-pass reproduces the
     P2 contingency ×5⁴ and word-invariance in h on every member).
Layer 3 — N(Σ_c) = 15,625 members of Σ_c ∩ 5¹⁵-box:
 P14 MARGINALS: N(t_j = t) = 3,125 for every t ∈ F₅, j = 1,2,3.
 P15 JOINT: all three pairwise contingencies uniform at 625 per (s,t) pair; the full
     triple contingency uniform at 125 per (s,t,u) cell; triple identity
     125·15,625² = 3,125³.

## S4 — FALSIFIERS (any hit ⟹ gate FAILS; this file is not touched)

F1 any exact-count mismatch in P1–P7, P9–P12, P14–P15. ATTRIBUTION, sealed now:
   a MARGINAL failure (P1/P7/P9/P14) indicts the §C-side derivation (Theorem C(b) or
   this seal's application of it); a JOINT/product failure (P2/P3–P5/P10/P11/P15) with
   correct marginals REFUTES (SIB) as stated — the plan's §8 R-SIB event. Any joint
   failure carries the diagnosis duty: report the exact offending word-pairs and which
   pulled-back coordinates are shared (S2's forms are the map).
F2 any P13 instability (a word not a function of the sealed box): the event definitions
   are ill-posed at the sealed depth — gate FAILS on specification; diagnose.
F3 P8 form mismatch: the S2 display is wrong somewhere; the census's literal digits are
   ground truth; count predictions (which derive from (SIB)+§C, not from S2) stand;
   record verbatim and proceed — fires no verdict on (SIB) by itself.

## S5 — Census specification (case_sib_gate.py, written AFTER this seal)

- Layer 1: construct all 5⁸ members from pins + fresh digits (deeper digits 0); per
  member and per r ∈ {1,2}: develop f at x − 5r by FOUR SYNTHETIC DIVISIONS over ℤ
  (independent of S2's closed forms); read (u_r, v_r, w_r) plus the P6 state digits;
  tally the 125-cell marginals, the 15,625-cell joint contingency, families A/B/C,
  outcome classes. DEEPENED PASS: the full 5¹² (e,g,h)-enumeration (chunked numpy):
  every word must equal its (e,g,0)-word (h-invariance, P13) and the joint contingency
  must be exactly 5⁴ × the primary. In-script re-derivation of the branch table at the
  cell (Taylor shift, d4m2 method) for the P6 spot check.
- Layer 2: all 2¹⁵ members: Hensel-lift the simple residual root ζ ≡ 1 of f(2z·)…
  concretely lift α (f(α) ≡ 0, α ≡ 2 mod 4) to mod 2¹²; synthetic division → h = x²+ax+b;
  read W_L = (α digits at 4·, 8·), W_Q = (a₂, b₃); tally 16-cell contingency + P11;
  LITERAL pass over all 2²⁴ boxes classifying Σ_c-membership (P12); deepening sample
  (10⁵ random extensions beyond level 8 at working precision 2¹⁶): words unchanged.
- Layer 3: all 5⁶ members: Hensel-lift the three simple roots mod 5⁷; read t_j; tally
  the 125-cell triple contingency, pairwise tables; deepening sample 10⁵ at 5⁹.
- All tallies exact integers; product identities checked as displayed integer equalities
  from the CENSUS numbers (so a count deviation still yields a separate (SIB) verdict).
- Long output → /tmp/sib_census.out; JSON → verification/results/case_sib_results.json.

## S6 — What this gate does NOT test (honest perimeter)

- ONE-STEP joint laws only (the plan's WHAT-THIS-GATE-CANNOT-SEE clause verbatim):
  multi-step subtree factorization (TREE-EXP's recursion) is not exercised here —
  RESUM-n3's discriminating layer owns that consistency class.
- Layer 1 = ONE cell, one prime, the equal-shape m = 2 case at depth 1. Layer 2 = the
  mixed-shape face, but of BELOW-HALT refinement reads (both branches τ-halted; FC5's
  structural finding: no all-continuing mixed-shape cell exists at n ≤ 4 — that face of
  (SIB) is n ≥ 5 territory, census-untested). Layer 3 = m = 3 at depth 0 only (the
  accepted JOINT-D1 face; confirmatory).
- FC2's naive lifts only; canonical-lift transport (S6b realizer) not exercised.
- REL.2's base-change to O_δ is touched only lightly (b_Q's F₄-digit block convention);
  no deep-frame (depth ≥ 2) sibling branching is reachable in these boxes.
- (SIB)'s quantifier is over ALL prescribed finite subtrees T_j; the gate instantiates
  finitely many word events. A PASS supports, never closes, the kernel (derivation
  burden stays open per §4t); a clean joint FAIL refutes it outright.

## S7 — POST-CENSUS VERDICT (appended after the run; no prediction above touched)

*(2026-07-27, census = case_sib_gate.py, run after S0–S6 were sealed. Full log:
/tmp/sib_census.out; JSON: results/case_sib_results.json. 32 sealed verdict families
checked; NO falsifier fired.)*

| sealed | census result |
|---|---|
| L1 P1 marginals | all 250 word counts = 3,125 exactly ✓ |
| L1 P2 JOINT ((SIB) core) | ALL 15,625 pairs = 25 exactly (min 25, max 25); product identity N(pair)·390,625 = N(w₁)·N(w₂) at EVERY pair ✓ |
| L1 P3 family A | 78,125 / 78,125 / 15,625; 78,125² = 15,625·390,625 ✓ |
| L1 P4 family B (asym) | 3,125 / 78,125 / 625; identity exact ✓ |
| L1 P5 family C (unions) | 18,750 / 312,500 / 15,000; identity exact ✓; split set = sealed 6 pairs ✓ |
| L1 P6 transported state | digit₂B₂=1, digit₃B₁=0, digit₄B₀=0 on ALL members, both r ✓; branch set {1,2} re-derived ✓ |
| L1 P7 classes | RAM/split/inert/double/deep = 312,500/18,750/31,250/12,500/15,625 both branches ✓ |
| L1 P8 form check | S2 forms = literal development digits everywhere ✓ (F3 not fired) |
| L1 P13 deepening | FULL 5¹² (e,g,h)-pass: 0 word changes; deepened contingency = 625× primary (15,625/pair) ✓ |
| L2 P9/P10/P11 | marginals 8,192 ×8 ✓; joint 2,048 at all 16 pairs ✓; union pair 16,384/16,384/8,192 ✓; identities exact ✓ |
| L2 P12/P13 | literal 2²⁴ membership = 32,768 ✓; 10⁵ deepenings, 0 changes ✓; Hensel exactness asserts all hold ✓ |
| L3 P14/P15 | marginals 3,125 ×15 ✓; pairwise 625 ×75 ✓; triple 125 at all 125 cells ✓; 125·15,625² = 3,125³ ✓; 10⁵ deepenings 0 ✓ |

GATE VERDICT: **PASS** — 32/32 sealed verdict families exact; zero tolerance met at
every contingency cell (15,625 + 16 + 125 joint cells, all exactly uniform). The (SIB)
product law holds VERBATIM at: the F1 equal-shape m = 2 branching cell (depth-1
continuation words, incl. union and asymmetric events), the plan's mixed-shape cubic
cell (below-halt refinement words, δ = 1 × δ = 2), and the m = 3 depth-0 cell.
MECHANISM FINDING (sealed in S2, confirmed by P8): the mechanism clause's LITERAL
disjoint-pool-coordinate route is REFUTED at the F1 cell — both siblings' events pull
back to the SAME 8 base digits (e, g); the product law holds by JOINT UNIMODULARITY of
the pulled-back forms (det ≡ 1 e-block; independent g-forms). (SIB)'s HONEST-RISK
clause is operative: the kernel should be stated and derived in its MEASURE-LEVEL form
(joint-fiber equidistribution of the cross-sibling read map), not via coordinate
disjointness. A PASS supports, never closes, the kernel (S6 perimeter verbatim: one-step
joint laws only; no all-continuing mixed-shape or m ≥ 3 cell exists at n ≤ 4 — that face
is n ≥ 5 territory, census-untested).
