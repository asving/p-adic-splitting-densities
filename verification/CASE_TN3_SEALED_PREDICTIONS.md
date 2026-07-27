# CASE-TN3 SEALED GATE — T-n3, the RECURSION gate: TREE-EXP fiber identification + VP pruning + ONE-F conversion on the F1/B22 box

*(2026-07-27. SEALED BEFORE ANY CENSUS CODE EXISTED. Sources: MOVES_2026-07-24.md
§T-ASSEMBLY — T.0 (TGT), T.1 VP-1/VP-2 (τ-hen/τ-irr/τ-ns), T.2 TB-CAP(irr), T.3 (SIB)
+ SIBLING INDEXING, T.4 TREE-EXP / per-shape law / ONE-F dictionary, T.6 the gate spec —
plus the two COMMITTED censuses this seal's numbers are computed FROM:
CASE_SIB_SEALED_PREDICTIONS.md S7 (PASS 32/32: P2 joint word contingency 25/pair, P3
family A, P7 outcome classes, P13 h-invariance) and CASE_D4M2_SEALED_PREDICTIONS.md S8
(PASS 33/33: C=64/E=58/GAP=6, the six mult-2 cells, hist {1:52, 2:6}). Case-K
discipline: any sealed falsifier fires ⟹ the gate FAILS and this file is not touched.
WHAT IS UNDER TEST (T.6 verbatim): the ASSEMBLY — that a per-f tree fiber equals the
first-split product (AND-over-nodes fiber identification + VP pruning + marked→per-f
conversion) — NOT the joint law: the passed SIB-gate owns that, and its word laws are
RE-CONFIRMED in-run as the attribution prerequisite.)*

## S0 — FREE CHOICES (every choice beyond §T.6 + the committed censuses, displayed)

- FC1 CELL/BOX (adopted verbatim from CASE_SIB FC1/FC4): p = 5, n = 4, root prefix
  P̂₀ = (1,1,1,2,0) full side (0,4)–(4,0), digit cell (d₃,d₂,d₁,d₀) = (4,3,3,4),
  R₀ = (z−1)²(z−2)², branches b₁ = z−1, b₂ = z−2 (μ = 2, both continuing); naive
  lifts Φ̂_r = x − 5r (SIB FC2); box B22 = (c₃ mod 5⁴, c₂ mod 5⁵, c₁ mod 5⁶, c₀ mod 5⁷);
  Σ_c ∩ B22 = 5⁸ = 390,625 members, free digits (e₃..e₀; g₃..g₀).
- FC2 LAYER-A VALUE TREE T_A := [root cell (4,3,3,4); b₁ → RAM τ-irr leaf (2,1) with
  endpoint digit v₁ = a₁ := 1; b₂ → RAM τ-irr leaf (2,1) with v₂ = a₂ := 2].
  (a₁,a₂) = (1,2) chosen so the two branch masses are LITERALLY the committed SIB P3
  family-A numbers. The σ-aggregate runs over ALL 16 value-trees of the shape
  ((a₁,a₂) ∈ (F₅ˣ)², root cell fixed): σ = {(2,1)} ⊎ {(2,1)}.
- FC3 LAYER-B SUBTREE: b₁ lands in the slope-2 DOUBLE-ROOT cell with word
  (u₁,v₁,w₁) = (3,0,1) — residual z²+3z+1 = (z−1)² over F₅, sub-branch root s := 1,
  depth-2 naive recentre t := 5 + 25s = 30 — and its NEXT read realizes the depth-2
  RAM τ-irr leaf with endpoint digit v′ = a′ := 2. Paired with b₂'s RAM leaf v₂ = 3
  (a₂ ≠ layer A's, to decorrelate). T_B := [root cell; b₁ → cell (3,0,1) → RAM′ leaf
  v′ = 2 (verdict (2,1): E = e₀e₁e₂ = 1·1·2, F = 1); b₂ → RAM leaf v₂ = 3].
- FC4 LAYER-B BOX (the minimal word-sufficient box, DISPLAYED per T.6): B26 :=
  (c₃ mod 5⁵, c₂ mod 5⁶, c₁ mod 5⁷, c₀ mod 5⁸). Σ_c ∩ B26 = 5¹² = 244,140,625 members;
  free digits e, g PLUS h = (h₃,h₂,h₁,h₀) at levels (c₃: 4, c₂: 5, c₁: 6, c₀: 7).
  WHY MINIMAL: v′ = digit₇(C₀), C₀ = f(30) = 810000 + 27000c₃ + 900c₂ + 30c₁ + c₀ with
  v(27000) = 3, v(900) = 2, v(30) = 1 — level 7 of C₀ reads c₃ ≤ lv 4, c₂ ≤ 5, c₁ ≤ 6,
  c₀ ≤ 7: exactly B26's digits, h included, nothing deeper (carries only go UP).
- FC5 WALKER (the independent VP implementation, per T.6 "not a word lookup"): per
  member, per branch, develop f at x − 5r by synthetic divisions over ℤ; compute
  v(B₂), v(B₁), v(B₀) by literal digit scan; build the lower hull of
  {(2,v(B₂)), (1,v(B₁)), (0,v(B₀))}; per side: e, residual from on-line digits,
  factor over F₅; τ per VP-2 (halt iff E·F = cluster degree, i.e. μ = 1); recurse
  (depth 2, at x − 30) only where T_B prescribes. Level-0 read re-derived per member
  (14 pins + residual factorization). CLASS CONVENTION: the walker's five depth-1
  classes are RAM (v(B₀) = 5) / slope-2 split / inert / double (v(B₀) = 6, residual
  by roots) / DEEPER (v(B₀) ≥ 7 — aggregates the u₁ ≠ 0 two-side partial hulls, whose
  near side already yields a (1,1) leaf, with the fully unresolved ones: both have
  T_can^τ(f) ≠ T_A, T_B, and the class matches SIB's word class v = w = 0).
- FC6 EXACTNESS: all identities in INTEGER COUNTS N(·) over the stated member
  enumerations; no floats. Deepening seed 20260727; ≥ 10⁵ samples.

## S1 — Derivation of the sealed numbers (every number from §T-ASSEMBLY displays + the two committed censuses)

LAYER A. T.4's fiber identification: {f : T_can^τ(f) = T_A} = Σ_c ∩ {v₁ = a₁} ∩
{v₂ = a₂} — the root cell pins Σ_c, each RAM leaf is the cell event {v_r = a_r}
(TB-CAP(irr): all levels ≤ B22's), and VP-2 prunes below the two τ-irr halts (E·F =
2·1 = 2 = cluster degree at slope-3/2 sides). Committed SIB numbers: N(v_r = a) =
78,125 per nonzero a (P1/P3); joint pairs 25/word-pair (P2) ⟹ N(fiber) = 390,625·5⁻²
= 15,625. TREE-EXP's product form: N(fiber)·N(Σ_c) = N(S₁)·N(S₂). Per-shape law +
SIBLING INDEXING: 16 member-indexed value-trees ((a₁,a₂) an ORDERED pair of
individuated members b₁,b₂ — no symmetry factor, no /2), each 15,625, Σ = 250,000 =
the direct count of {both branches τ-halt at depth 1 with typemult = {(2,1),(2,1)}}
(both-RAM is the ONLY both-halted depth-1 outcome pair with that σ: split leaves are
(1,1)+(1,1), inert is (1,2)). Depth-1-decided total (both halt): per branch
RAM+split+inert = 312,500+18,750+31,250 = 362,500 (SIB P7); SIB P2 uniformity ⟹
both-decided = 362,500²/390,625 = 336,400; σ-partition of it (products/390,625,
cross terms doubled — member-indexed): RAM×RAM 250,000; RAM×split 30,000; RAM×inert
50,000; split×split 900; split×inert 3,000; inert×inert 2,500 [Σ = 336,400 ✓];
undecided-somewhere 54,225.
LAYER B. Transported depth-1 landing state on the (3,0,1) cell (carry algebra, census
re-derives literally): C₂ = B₂ + 3B₃(25s) + 6B₄(25s)² ⟹ v(C₂) = 2, unit digit 1
(corrections v ≥ 3); digit₄(C₁) = u₁ + 2s·digit₂(B₂) = 3 + 2 = 0 ⟹ v(C₁) ≥ 5;
digit₅(C₀) = v₁ = 0, digit₆(C₀) = w₁ + u₁s + s² = 1+3+1 = 0 ⟹ v(C₀) ≥ 7. Depth-2
hull hangs from (2,2): v′ := digit₇(C₀) ≠ 0 gives the single side (0,7)–(2,2), slope
5/2, e₂ = 2, linear residual, μ = 1 ⟹ τ-irr leaf (2,1), leaf cell {v′ = a′} (the
point (1, v(C₁) ≥ 5) lies above height 4.5 — single side regardless of u′). The
h-block of v′: 27000·5³·216≡…: coefficient of h₃ is 216 ≡ 1, of h₂ 36 ≡ 1, of h₁
6 ≡ 1, of h₀ 1 (all mod 5) ⟹ v′ = (T₇(e,g) + h₃+h₂+h₁+h₀) mod 5, T₇ census-literal;
h enters no digit of C₀ below level 7 (levels 3+4, 2+5, 1+6, 0+7). Counts in B26:
N(cell (3,0,1)) = 5¹²·5⁻³ = 1,953,125; conditional C.1.5 step: N(v′ = t │ cell) =
5⁸ = 390,625 for EVERY t ∈ F₅ (h-sum uniform at each (e,g)); chain S_{T₁} =
{W₁ = (3,0,1)} ∩ {v′ = 2}: N = 5⁸; sibling S_{T₂} = {v₂ = 3}: N = 5¹¹ = 48,828,125;
(SIB) ⟹ N(fiber T_B) = 5¹²·5⁻⁵ = 5⁷ = 78,125; identity N(fiber)·5¹² =
N(S_{T₁})·N(S_{T₂}) — both sides 5¹⁹ = 19,073,486,328,125. The shared prefix (root +
b₁'s depth-1 cell) is charged ONCE through two levels: 5⁻⁵ = 5⁻³·5⁻¹·5⁻¹, never
5⁻³ twice.
LAYER C. d4m2 committed: marked total C = 64, event E = 58, gap 6, hist {1: 52, 2: 6},
the six two-double-root cells verbatim (S2 list incl. (4,3,3,4) ↦ {1,2}). Marks :=
#{roots of R₀ with ord exactly 2} per cell (an independent full factorization, not
the Taylor-shift): marks = mult member-wise; two-double-root σ (type (c)) DIRECT
per-f count = 6 essential boxes = the tree-fiber sum (ONE tree per f), marked total
on them = 12 — overcount exactly the six cells' excess 6. THE F1 DECIDED INSTANCE
(in B22, layer A's walk): marked RAM-chain total Σ_r N(v_r ≠ 0) = 2·312,500 =
625,000 = Σ_T (#RAM marks in T)·N(fiber): 2·250,000 (both-RAM) + 1·125,000 (exactly
one RAM; = 2·(312,500 − 250,000)) — vs the PER-F σ count 250,000: the dictionary,
every number census-derived; #RAM-marks histogram {0: 15,625, 1: 125,000, 2: 250,000}.

## S2 — SEALED PREDICTIONS (exact integers; ANY mismatch = the named falsifier fires)

LAYER A — walker over all 390,625 members of Σ_c ∩ B22 (N_A := 390,625):
 A1 WALK TOTALITY + CLASSES: every member classified; per-branch depth-1 classes
    (HULL-derived, not word lookup) RAM/split/inert/double/DEEPER =
    312,500/18,750/31,250/12,500/15,625 for BOTH branches (= SIB P7); root read
    re-derived per member: cell (4,3,3,4), branch set {z−1, z−2}, μ = 2 both.
 A2 FIBER (direct walk): N{f : T_can^τ(f) = T_A} = 15,625 (T_A = FC2's tree,
    (a₁,a₂) = (1,2); tree EQUALITY: both branches τ-irr-halted at depth 1, RAM cells
    with exactly those endpoint digits).
 A3 PRODUCT (both ways): censused branch masses N(S₁) = N{v₁ = 1} = 78,125,
    N(S₂) = N{v₂ = 2} = 78,125; integer identity N(fiber)·N_A = N(S₁)·N(S₂):
    15,625·390,625 = 78,125² = 6,103,515,625.
 A4 σ-AGGREGATE: all 16 value-tree fibers ((a₁,a₂) ∈ (F₅ˣ)²) EACH = 15,625 (min =
    max); Σ = 250,000 = 16·15,625 (C_T̂ = 16, per-shape law); direct typemult count
    N{both branches halted at depth 1, typemult = {(2,1),(2,1)}} = 250,000 —
    SIBLING INDEXING: the member-indexed 4×4 grid, e.g. fiber(1,2) and fiber(2,1)
    BOTH 15,625; NO symmetry factor (the /2-corrected 125,000 is the sealed FALSE
    alternative).
 A5 PER-FIBER IDENTITIES: N(fiber(a₁,a₂))·N_A = N{v₁=a₁}·N{v₂=a₂} at ALL 16 pairs
    (every branch-mass factor = 78,125).
 A6 σ-PARTITION of the depth-1-decided set: both-halted total 336,400; by σ:
    {(2,1),(2,1)} 250,000; {(2,1),(1,1),(1,1)} 30,000; {(2,1),(1,2)} 50,000;
    {(1,1)×4} 900; {(1,1),(1,1),(1,2)} 3,000; {(1,2),(1,2)} 2,500 [Σ = 336,400];
    undecided-somewhere 54,225 [total 390,625].
 A7 SIB RE-CONFIRMATION (attribution prerequisite): the in-run joint word
    contingency = 25 at ALL 15,625 pairs (SIB P2 verbatim).
LAYER B — walker over all 244,140,625 members of Σ_c ∩ B26 (N_B := 5¹²):
 B1 TRANSPORTED DEPTH-1 STATE: N{W₁ = (3,0,1)} = 1,953,125; on ALL its members:
    v(C₂) = 2 with unit digit 1, v(C₁) ≥ 5, v(C₀) ≥ 7 (zero exceptions).
 B2 FIBER (direct depth-2 walk): N{f : T_can^τ(f) = T_B} = 78,125 (T_B = FC3's tree).
 B3 RECURSION (both ways): N(S_{T₁}) = N{W₁ = (3,0,1) ∧ v′ = 2} = 390,625;
    N(S_{T₂}) = N{v₂ = 3} = 48,828,125; identity N(fiber)·N_B = N(S_{T₁})·N(S_{T₂}):
    78,125·244,140,625 = 390,625·48,828,125 = 19,073,486,328,125 = 5¹⁹.
 B4 CHAIN (shared prefix charged once through two levels): N{v′ = t ∧ W₁ = (3,0,1)}
    = 390,625 for EVERY t ∈ F₅ (the depth-2 C.1.5 step exactly uniform conditional
    on the depth-1 cell); N(S_{T₁}) = N(cell)·5⁻¹ exactly.
 B5 STABILITY (P13-style falsifier, mandatory per T.6): ≥ 10⁵ random extensions
    beyond B26 (fresh digits at c₃ lv 5, c₂ lv 6, c₁ lv 7, c₀ lv 8): W₁, W₂, v′ and
    T_B-fiber membership all unchanged — 0 changes.
 B6 FORM CHECK (h-block display; failure indicts the display only, F3-style):
    v′(e,g,h) − v′(e,g,0) ≡ h₃+h₂+h₁+h₀ (mod 5) on all members.
 B7 SIB RE-CONFIRMATION in B26: depth-1 joint contingency = 15,625 at ALL 15,625
    pairs (= 5⁴ × SIB P2, h-invariance of depth-1 words — SIB P13 verbatim).
LAYER C — marks/dictionary (5⁴ residual-cell census + committed d4m2 JSON + B22 walk):
 C1 MARKS = MULT member-wise: over ALL 5⁴ digit tuples (d₀ ≠ 0 in-event), marks by
    FULL factorization = d4m2's Taylor-shift mult, zero exceptions; event histogram
    {1: 52, 2: 6, ≥3: 0}; each event box realizes exactly ONE cell (ONE-F partition
    face at the root read).
 C2 TOTALS vs the committed d4m2 census: marked total 64 = C_P̂₀(5); per-f event
    count 58 = E; gap 6; the committed JSON's registry = the walker's realized-cell
    table verbatim (58 cells; six mult-2 cells incl. (4,3,3,4) ↦ {1,2}).
 C3 TWO-DOUBLE-ROOT σ: direct per-f count = 6 essential boxes (the six sealed cells,
    one box each) = the tree-fiber sum; marked total on them = 12; overcount = 6 =
    the six mult-2 cells' excess (D4R.1's displayed check).
 C4 THE F1 (ONE-F) INSTANCE (sealed numbers, from layer A's per-member walk):
    #RAM-marks histogram over Σ_c ∩ B22 = {0: 15,625, 1: 125,000, 2: 250,000};
    marked RAM-chain total Σ_f #RAM-marks = 625,000 = 2·312,500 (branch-weighted)
    = 2·250,000 + 1·125,000 (tree-fiber expansion); per-f σ count = 250,000 =
    Σ_{16 trees} N(fiber) — the DIRECT decided count equals the TREE-FIBER SUM,
    NOT the marked total (which strictly exceeds it by 375,000 here).

## S3 — FALSIFIERS + SEALED ATTRIBUTION (T.6 verbatim; any hit ⟹ gate FAILS, file untouched)

F1 any exact-count mismatch in A1–A6, B1–B4, C1–C4. ATTRIBUTION, sealed now:
   - A1/B1 (classes, transported state) with SIB re-confirmation intact: indicts the
     walker's engine transport (this seal's S1 derivation), diagnose before verdict.
   - A2–A5/B2–B4 (fiber vs product/chain) with A7/B7 word laws INTACT: indicts
     TREE-EXP's fiber identification or VP's pruning — §T-ASSEMBLY's own content —
     NOT (SIB) (T.6's sealed attribution).
   - A4's aggregate ≠ 16·(one fiber) with per-fiber counts uniform: indicts SIBLING
     INDEXING / the per-shape law (a hidden symmetry factor).
   - C1–C4: indicts ONE-F / the marked→per-f dictionary (T.6: "a (C) mismatch
     indicts ONE-F/the dictionary").
   Adjudication order per plan §8 R-SIB; mismatches surviving it refute the
   recursion as displayed.
F2 any B5 instability (a layer-B word or fiber membership not a function of B26):
   the event definitions are ill-posed at the sealed depth — gate FAILS on
   specification (T.6's mandatory falsifier); diagnose.
F3 B6 form mismatch: the S1 h-block display is wrong; census digits are ground
   truth; count predictions (from §C + (SIB) + TREE-EXP, not from the display)
   stand; record verbatim and proceed — no verdict on the recursion by itself.
F4 A7/B7 SIB re-confirmation failure: STOP — the attribution scheme's premise is
   void; escalate to the SIB-gate's own falsifier row before any T-n3 verdict.

## S4 — Census specification (case_tn3_gate.py, written AFTER this seal)

- LAYER A (B22, 5⁸ members from pins + (e,g), deeper digits 0): per member, per
  branch r ∈ {1,2}: develop at x − 5r by synthetic divisions over ℤ (SIB's develop(),
  independent of the S2 closed forms); HULL walker per FC5 (valuation scans, side
  construction, residual factorization over F₅, τ = saturation test) — NOT the fixed
  word positions; emit the depth-1 tree object per member. Tally A1–A6 + the joint
  word contingency (A7) + the C4 RAM-marks histogram.
- LAYER B (B26, 5¹² members, chunked over the 625 h-tuples × 5⁸ base): depth-1 walk
  as above per chunk (h shifts the coefficients; words must reproduce ×5⁴ — B7);
  on the {W₁ = (3,0,1)} mask: recentre at x − 30 (four synthetic divisions), literal
  digit reads of C₂/C₁/C₀ for B1's state, v′ = digit₇(C₀), depth-2 hull + τ; tally
  B1–B4, B6. B5: ≥ 10⁵ random members × random fresh digits at (c₃ lv 5, c₂ lv 6,
  c₁ lv 7, c₀ lv 8), full re-walk at extended precision: 0 changes.
- LAYER C: all 5⁴ residual tuples: marks by full root/multiplicity factorization of
  R₀ (roots via evaluation, ord via repeated synthetic division) vs d4m2's
  Taylor-shift mult (both in-script, independent methods); load committed
  results/case_d4m2_results.json: registry/totals must equal the walker's table
  (C1–C3). C4 from layer A's per-member walk.
- All tallies exact integers (int64/Python int; no floats). Long output →
  /tmp/tn3_census.out; JSON → verification/results/case_tn3_results.json.

## S5 — What this gate does NOT test (honest perimeter)

- (SIB) itself: consumed as the committed PASS + re-confirmed word laws; T-n3's
  product identities EXERCISE the assembly through (SIB)'s already-tested face
  (m = 2, depth ≤ 2 words, one cell, one prime). Depth ≥ 3, m ≥ 3 at depth ≥ 1,
  n ≥ 5 all-continuing mixed shapes: census-untested (SIB S6 verbatim).
- VP's (τ-hen) clause: no simple reduction factor exists on Σ_c (f̄ = x⁴); τ-hen is
  exercised ONLY via its absence (m = 4 ⟹ window opened). (τ-ns): not realized in
  these boxes (no J(f) = ∅ track); TB-CAP(ns-lump)/(ns-null) untouched.
- The σ-aggregate is the SHAPE aggregate (16 value-trees, root cell fixed) — NOT the
  σ-DENSITY: deeper trees with typemult {(2,1),(2,1)} (e.g. T_B's own class) exist
  and are excluded by the both-halt-at-depth-1 condition; the density form of (TGT)
  stays X.3-conditional and untested here.
- ONE-F is tested at ℓ = 1 (root marks) and at the F1 RAM-chain instance; no deeper
  shape-prefix multiplicities (mult from depth ≥ 1 reads) are realized in these boxes.
- Naive lifts only (SIB FC2); canonical-lift transport untested. REL.2/PCI: single
  cell, single prime — the O_δ quantifier is not exercised (δ = 1 throughout: all
  residuals split over F₅ at the tested cells).
- Feasibility note: B26 is exhaustive by construction (5¹² members ARE the box's
  Σ_c-stratum); w′ = digit₈(C₀) (the depth-2 slope-2 analogue) would need the 5¹⁶
  box — out of scope; T_B's leaf is the RAM′ clause precisely so B26 suffices.

## S6 — POST-CENSUS VERDICT (appended after the run; no prediction above touched)

*(2026-07-27, census = case_tn3_gate.py, run after S0–S5 were sealed. Full log:
/tmp/tn3_census.out; JSON: results/case_tn3_results.json. 21 sealed verdict families
checked; NO falsifier fired; runtime 52 s, 5⁸ + 5¹² + 10⁵ + 5⁴ members walked.)*

| sealed | census result |
|---|---|
| A1 root + classes | 14 pins + R0 factorization re-derived on all members ✓; hull classes 312,500/18,750/31,250/12,500/15,625 BOTH branches ✓ (DEEPER splits 12,500 two-side partial + 3,125 unresolved) |
| A2 direct fiber T_A | 15,625 exactly ✓ (engine walk, tree equality) |
| A3 both ways | 78,125/78,125; 15,625·390,625 = 78,125² = 6,103,515,625 ✓ |
| A4/A4b σ-aggregate | all 16 fibers 15,625 (min=max) ✓; Σ = 250,000 = direct typemult count ✓; fiber(1,2) = fiber(2,1) = 15,625, NO symmetry factor ✓ |
| A5 per-fiber identities | exact at all 16 pairs ✓ |
| A6 σ-partition | 250,000/30,000/50,000/900/3,000/2,500; decided 336,400; undecided 54,225 ✓ |
| A7 SIB re-confirm | joint word contingency 25 at all 15,625 pairs ✓ (attribution premise intact) |
| B7 SIB in B26 | 0 member-wise word changes over 5¹²; contingency 15,625/pair ✓ |
| B1 transported state | N(cell) = 1,953,125 ✓; v(C₂)=2 unit 1, v(C₁)≥5, v(C₀)≥7: 0 violations ✓ |
| B2 depth-2 fiber T_B | 78,125 exactly ✓ (walk through two levels) |
| B3 recursion both ways | 390,625·48,828,125 = 78,125·5¹² = 5¹⁹ = 19,073,486,328,125 ✓ |
| B4 chain step | N{v′=t ∧ cell} = 390,625 at ALL five t ✓ (shared prefix charged once) |
| B5 stability | 10⁵ k-extensions: 0 changes ✓ (B26 word-sufficient as displayed) |
| B6 h-form | v′ shift ≡ h₃+h₂+h₁+h₀ everywhere ✓ (F3 not fired) |
| C1 marks = mult | 0 mismatches over all d₀≠0 tuples; hist {1: 52, 2: 6, ≥3: 0} ✓ |
| C2 totals/registry | 64/58/6; committed d4m2 registry = walker table verbatim ✓ |
| C3 two-double-root σ | 6 cells verbatim = tree-fiber sum; marked 12; overcount 6 ✓ |
| C4 (ONE-F) instance | hist {0: 15,625, 1: 125,000, 2: 250,000}; 625,000 = 2·250,000 + 125,000; per-f 250,000 ≠ marked ✓ |

GATE VERDICT: **PASS** — 21/21 sealed verdict families exact, zero tolerance met.
The ASSEMBLY is census-tested for the first time: (A) a per-f tree fiber, computed by
an independent engine walk with VP pruning, equals the first-split product of censused
branch masses exactly, and the σ-aggregate matches the per-shape law with C_T̂ = 16 and
NO symmetry factor (SIBLING INDEXING confirmed at the value level); (B) the depth-2
prescribed subtree prices as η₀-chain × (SIB) × the child's OWN C.1.5 step with the
shared prefix charged ONCE through two levels — the depth-2 conditional step exactly
uniform (new §C-side territory census-confirmed at this cell); (C) the marked→per-f
dictionary holds verbatim at mult 2, root level (64 vs 58 vs 6) and decided level
(625,000 vs 250,000, tree-fiber expansion exact). What this pass does NOT certify:
S5 verbatim — (SIB)'s open kernel, τ-hen/τ-ns, canonical lifts, REL.2/PCI, deeper
mults, the σ-DENSITY (X.3), and everything beyond this cell/prime/depth. Per T.6,
T-n3 joins the §7 roster beside the passed SIB-gate; [3t]'s acceptance may now cite
BOTH gates (with the standing conditionality list unchanged).
