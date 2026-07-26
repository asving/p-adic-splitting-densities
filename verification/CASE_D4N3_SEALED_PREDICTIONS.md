# CASE-D4N3 SEALED GATE — n = 3 class-3 prefix, p ∈ {2, 3} (mass law + partition)

*(2026-07-26. SEALED BEFORE ANY CENSUS CODE EXISTED OR ANY Z_p BOX WAS EXAMINED.
Sources: MOVES_2026-07-24.md §D4-R (L1–L12, D4R.0/1/2/4, gate spec §D4-R.6) and
§C REV 2 (C.0 histories/realizability, C.1 species inventory, C.1.5, Theorem C).
Case-K discipline: predictions are never adjusted after the census; any sealed
falsifier fires ⟹ the gate FAILS and this file is not touched. The only
pre-seal computation was pure F_p residual algebra (the (ψ, r) ↔ digit-tuple
tables in S2 below — no Z_p boxes, no division, no enumeration of inputs).)*

## S0 — FREE CHOICES MADE (not derivable from the note text)

Per the Codex assembly-pass CRITICAL finding 7 (relayed by the orchestrator):
§D4-R.6's instance spec ("irreducible quadratic · linear", "side data fixed,
μ = 1") does NOT pin the instance. Every choice made beyond the note text, with
the exact value chosen — these are the candidate pin for the note revision:

- FC1 ROOT SIDE DATA: single polygon side (0,3)–(3,0), slope h₀/e₀ = 1/1
  (λ = 1 chosen minimal; the note pins neither the slope nor single-sidedness).
- FC2 FACTOR SELECTION: the canonical run descends into the IRREDUCIBLE
  QUADRATIC factor ψ (not the linear one). The note text has no canonical
  factor-selection rule (L2's determinism needs one); the gate instance
  mandates the quadratic, so the policy is pinned to it here.
- FC3 DESCEND SIDE DATA: side (0,4)–(1,1) in the frame-1 window, i.e.
  w(B₀) = 4 (the minimal value admissible above the (BOX) floor — see S1),
  (e₁, h₁) = (1, 3). The note fixes only "side data fixed, μ = 1".
- FC4 KEY LIFT: Φ̂₁ := x² + [s₁]·p·x + [s₀]·p², [·] = least non-negative
  residue, for ψ = z² + s₁z + s₀. §C C.0 allows any admissible recorded lift;
  the canonical (S6b) policy pins RECENTERING lifts only, not augmentation-key
  lifts. NOTE: the fiber SETS below depend on this choice (an admissible lift
  differing at exact weight 3 shifts the δ-cells by an affine bijection of
  F_{p²}); the sealed COUNTS C, A, and all totals do not.
- FC5 DIGIT NORMALIZATION: the F_{p²}-digit of a frame-1 slot pair is read as
  δ := (c-component digit) + (x-component digit)·z̄ ∈ F_p[z̄]/ψ(z̄). Fixes the
  cell LABELS only; cell structure and masses are unaffected.
- FC6 POOL-TUPLE EXTENT for W(P̂*): the side-digit tuples are counted with the
  monic lead EXCLUDED (not a box coordinate) and the (HV)-forced vertex digit
  INCLUDED: d_root = 3 digits in F_p (w₀ = 1), d_desc = 2 digits in F_{p²}
  (w₁ = 2), so W = 1·3 + 2·2 = 7. (The tighter free-digit-only reading W = 5
  also holds and is reported as info; both give true D4R.2 inequalities.)
- FC7 LEVELS: p = 2: N ∈ {6, 7} (boxes 2^18, 2^21). p = 3: N ∈ {5, 6} (boxes
  3^15, 3^18). BUDGET DEVIATION, stated: A(P̂*) = 11 forces N(P̂*) = 5 (S5),
  so the suggested 3^12 (N = 4) is INADMISSIBLE and no two admissible p = 3
  levels fit "≤ ~2·10⁷ boxes per prime" (3^18 = 387,420,489 ≈ 19× the cap);
  the note's own "feasible through 3^15" admits only ONE admissible level.
  The gate spec's two-level demand wins; 3^18 is run as a literally exhaustive
  vectorized enumeration (every box's membership sum is materialized).
- FC8 GATE RESOLUTION, STEP-0 PARTITION: the sibling strata of the root read
  are resolved as: NC (non-cluster) ∪ 20 valuation lumps (V₀, V₁, V₂) :=
  (min(v(c₀),4), min(v(c₁),3), min(v(c₂),2)) on the cluster, EXCEPT the target
  region {V₀ = 3, V₁ ≥ 2} which is refined into its p²(p−1) on-line digit
  cells (d₂, d₁, d₀) ∈ F_p × F_p × F_pˣ. Deeper structure of non-target lumps
  is other prefixes' business (not resolved by this gate).
- FC9 GATE RESOLUTION, STEP-1 PARTITION: within each quad·lin digit cell, the
  ν₁-outcome strata are the p² − 1 δ-cells {w(B₀) = 4 with ht-4 digit δ ≠ 0}
  plus DEEP {w(B₀) ≥ 5} (the (z) zero/deeper lump at this resolution).

## S1 — The prefix P̂*, pinned exactly (every read, key, species displayed)

Box: monic cubics f = x³ + c₂x² + c₁x + c₀, cᵢ ∈ Z_p; μ(·) := #{f mod p^N ∈
·}·p^{−3N} (L3). Base coordinates (level ℓ, index i), Fact-A order.

ν₀ — ROOT READ (D.4 ROOT case; species: branch at key Φ̂₀ = x):
- E(ν₀) = initial cluster conditions ∪ root side pattern (§C C.0 ROOT NODE):
  cluster zeros c₂ ≡ c₁ ≡ c₀ ≡ 0 (mod p) — 3 pins at level 0.
- Side (0,3)–(3,0), slope 1 [FC1]. Side-digit tuple: d₃ = 1 (monic lead, no
  coordinate); d₂ := lvl-1 digit of c₂ (on-line value, any value in F_p);
  d₁ := lvl-2 digit of c₁ (strip zero at lvl 1 below it); d₀ := lvl-3 digit of
  c₀ ≠ 0 (endpoint; strip zeros at lvls 1, 2 below it).
- Residual cubic R(z) = z³ + d₂z² + d₁z + d₀ ∈ F_p[z]. SHAPE/SPECIES: R =
  ψ(z)·(z − r), ψ monic irreducible quadratic, r ∈ F_pˣ (d₀ ≠ 0 forces r ≠ 0;
  ψ(0) ≠ 0 automatic). Chosen factor ψ [FC2]; node data (e, h, g, μ, a) =
  (1, 1, 2, 1, 0); pool w₀ = 1 (digits in F_p).
- Key: Φ̂₁ = x² + [s₁]px + [s₀]p² [FC4]; D₁ = deg Φ̂₁ = 2 = e₀g₀D₀.

ν₁ — DESCEND READ at the deg-2 key (e_read·g = 1: recentering-species read;
its canonical lift is part of the node data but is never APPLIED inside this
prefix — the prefix ends at the read):
- Frame-1 window: slots [0, μ₀] = [0, 1]; division f = B₁·Φ̂₁ + B₀ with
  B₁ = x + q₀ (monic, slot 1 = vertex), B₀ = r₁x + r₀ (slot 0). Closed forms
  (S₁ := [s₁]p, S₀ := [s₀]p²): q₀ = c₂ − S₁; r₁ = c₁ − S₀ − S₁q₀;
  r₀ = c₀ − S₀q₀ (verified against literal long division in the census, F5).
- Heights (LST): ht(slot-0 pair) : r₀ at lvl ℓ has ht ℓ, r₁ at lvl ℓ has ht
  ℓ + 1 (κ₀ = 1). Box line old(j) = w(f) − j·w(Φ̂₁) = 3 − 2j; floor F₀ = 3 on
  the slot-0 block (DOM: old₀ staircase at the block's left edge).
- VERTEX (slot 1): w(B₁) = 1 = old₀(μ₀), pinned by ν₀'s (VERTEX); its ht-1
  digit is z̄ + q̄₀ (q̄₀ := lvl-1 digit of q₀).
- (BOX) on Σ₀: w(B₀) > 3, on the integer ht-lattice of slot 0 ⟹ w(B₀) ≥ 4,
  i.e. v(r₀) ≥ 4 AND v(r₁) ≥ 3 — inherited, 0 violations tolerated (F3).
- THE READ [FC3]: side (0,4)–(1,1): (e, h, g, μ, a) = (1, 3, 1, 1, 0);
  s₀' = 0, w' = 1, j* = s₀'+w' = 1 = μ₀ ⟹ ADJACENT: (HV) applies, (NA)
  vacuous. (I-aug): h₁/e₁ = 3 > 2 = w(Φ̂₁) ✓.
- (HV), evaluated: pattern lead at the vertex = vtx(ν₀). Concretely the ht-1
  digit of B₁ is z̄ + q̄₀ with q̄₀ = d₂ − s₁ = −r (an identity of node data:
  d₂ = s₁ − r from R = ψ·(z − r)) — a DATA condition, pins nothing, and
  removes the vertex digit from the free tuple (it is a function of ν₀'s
  data, exactly L1/L4's forcedness).
- FRESH CONTENT of ν₁ (C.1 species inventory): (α) slot 0: strip (3, 4) is
  EMPTY on the integer ht-lattice; the on-lattice value digit at ht 4 has
  level set {(r₀, lvl 4), (r₁, lvl 3)}, attainable alphabet = full F_{p²}
  (TYP: images in(p⁴), in(p³x) span), digit δ := lvl₄(r₀) + lvl₃(r₁)·z̄ ∈
  F_{p²}ˣ [FC5] — one F_{p²}-digit = 2 base pins. Slot 1 (adjacent endpoint):
  E_inh entirely. (β): none (s₀' = 0). (γ): none (j* = μ₀).

|P̂*| = 2 reads; strides all 1; residue degrees (w₀, w₁) = (1, 2).

## S2 — C_P̂*(p) by L11's enumeration (with (NA)/(HV) applied)

Read 0: enc-component = (d₂, d₁, d₀) ∈ F_p² × F_pˣ; the shape's species
requirement selects exactly the tuples with R = ψ·(z − r): by unique
factorization these are in BIJECTION with pairs (ψ, r), count
[p(p−1)/2]·(p−1). The tables (pre-seal F_p algebra, brute-force re-counted):
- p = 2: 1 cell: (d₂,d₁,d₀) = (0,0,1) [ψ = z²+z+1, r = 1; R = z³+1].
- p = 3: 6 cells: (2,1,2) [z²+1, r=1]; (1,1,1) [z²+1, r=2]; (0,1,1)
  [z²+z+2, r=1]; (2,0,2) [z²+z+2, r=2]; (1,0,1) [z²+2z+2, r=1]; (0,1,2)
  [z²+2z+2, r=2]. All distinct; d₀ ≠ 0 automatic.
Read 1: vertex digit (HV)-FORCED (= z̄ − r, S1) — 1 value, no free choice;
endpoint digit δ ∈ F_{p²}ˣ free: p² − 1 values. (NA) never fires (adjacent).

  C_P̂*(2) = 1·(2²−1) = 3        C_P̂*(3) = 6·(3²−1) = 48

FINDING-4 NOTE (L11 collision risk, recorded per the orchestrator): at this
prefix NO same-shape factor-selection ambiguity can occur — a cubic residual
has at most one irreducible quadratic factor, and ν₁'s residual is linear.
This gate is structurally UNABLE to probe the finding-4 collision (that needs
a residual with ≥ 2 same-species factors, impossible at n = 3). If the census
nevertheless surfaces two distinct realized prefixes with equal enc, it is
recorded prominently as direct evidence for the repair.

## S3 — A(P̂*) by the L9 ledger (pin table)

ν₀ (9 base pins, vol p^{−9}): cluster: (c₂,0), (c₁,0), (c₀,0) = 3; slot 2:
value (c₂,1) = 1; slot 1: strip zero (c₁,1) + value (c₁,2) = 2; slot 0: strip
zeros (c₀,1), (c₀,2) + value (c₀,3) = 3.
ν₁ (2 base pins, vol p^{−2}): the ht-4 F_{p²}-value digit = level set
{(r₀,4), (r₁,3)}; no strips; adjacent endpoint pins nothing.

  A(P̂*) = 9 + 2 = 11        (shape data; identical for every η ∈ Pref(P̂*))

## S4 — The pool bound D4R.2 ((3i) verbatim)

W(P̂*) = Σ_r w_r·d_r = 1·3 + 2·2 = 7 [FC6]; A_net(P̂*) = 11 − 7 = 4.
Sealed inequalities (checked numerically by the census):
  C_P̂*(p) ≤ p^W:  3 ≤ 2⁷ = 128 ✓ ;  48 ≤ 3⁷ = 2187 ✓ (verified at seal time)
  μ(P̂*) = C_P̂*(p)·p^{−11} ≤ p^{−A_net} = p^{−4}.
Info (not sealed): the free-digit-only reading W = 5, A_net = 6 also holds
(3 ≤ 2⁵, 48 ≤ 3⁵; C·p^{−11} ≤ p^{−6} both primes).

## S5 — N(P̂*) by L12 and the level choice [FC7]

Every η ∈ Pref(P̂*) has the same T(η,⊤) pin levels: root equations at base
levels ≤ 3; ν₁'s transported value equations lead at base (c₀-column, lvl 4)
and (c₁-column, lvl 3) (C.0.5 pin transport at fixed labels). Largest base
level = 4, so N(η,⊤) = 5 for every η, and N(P̂*) = 5.
Levels run: p = 2: N = 6 and N = 7. p = 3: N = 5 and N = 6 (deviation stated
in FC7). All four have N ≥ N(P̂*) = 5 as L12 requires.

## S6 — SEALED PREDICTIONS (exact integers; ANY mismatch = FAIL)

P1 (mass law D4R.1 at level N, via L12): #{f mod p^N ∈ S(P̂*,⊤)} =
   C_P̂*(p)·p^{3N−11}:
     p=2 N=6: 3·2⁷  = 384          p=2 N=7: 3·2¹⁰ = 3072
     p=3 N=5: 48·3⁴ = 3888         p=3 N=6: 48·3⁷ = 104976
P2 (per-η fibers, Theorem C(b) + L9): EVERY (root cell × δ) cell, δ ∈ F_{p²}ˣ,
   has EXACTLY p^{3N−11} members: 128 (p2N6), 1024 (p2N7), 81 (p3N5),
   2187 (p3N6). [3 δ-cells per root cell at p=2; 8 at p=3.]
P3 (length-1 prefix event, Theorem C(b) at the root): EVERY on-line digit
   cell of the target region (all p²(p−1) of them, any species) has EXACTLY
   p^{3N−9} members: 512, 4096, 729, 19683. Root fiber (the C_root quad·lin
   cells) = C_root·p^{3N−9}: 512, 4096, 4374, 118098.
P4 (deeper lump = the (z) case at this resolution): within EVERY root cell,
   DEEP {w(B₀) ≥ 5} has EXACTLY p^{3N−11} members (same values as P2).
   [Check: (p²−1)·p^{3N−11} + p^{3N−11} = p^{3N−9} ties P2+P4 to P3.]
P5 (PARTITION, step 0 = D4R.0/L5 on Σ₋₁): over the stratum list of FC8
   (1 + 20 + p²(p−1) systems, membership evaluated independently per system),
   EVERY box of the level-N box has membership sum EXACTLY 1: 0 double-counts,
   0 orphans, at all four (p, N).
P6 (PARTITION, step 1 = D4R.0/L5 on Σ₀ ∩ root cell): within every root cell,
   the p² systems of FC9 have membership sum EXACTLY 1 per member; and the
   inherited (BOX) floor holds member-by-member: 0 members with v(r₀) ≤ 3 or
   v(r₁) ≤ 2 (this is the non-tautological content: root-cell membership is
   a pure c-digit condition, the floor lives in frame 1).
P7 (HV/vertex forcedness, L1/L4): EVERY root-cell member has w(B₁) = 1
   exactly with vertex digit z̄ + q̄₀ where q̄₀ = −r mod p: 0 exceptions.
P8 (net bound D4R.2): the measured μ̂ = (P1 count)·p^{−3N} equals C·p^{−11}
   and satisfies μ̂ ≤ p^{−4}: 3/2048 ≤ 1/16 (p=2); 48/177147 ≤ 1/81 (p=3).
P9 (N-stability, L12): the two levels per prime BOTH match P1 exactly —
   ratio between consecutive levels exactly p³.

Derived sub-totals the census also reports (implied by P3/P5, sealed via
them): cluster count p^{3N−3}; NC count p^{3N} − p^{3N−3}; target-region
total p²(p−1)·p^{3N−9}.

## S7 — Census specification (written into case_d4n3_gate.py AFTER this seal)

- Exhaustive enumeration of ALL p^{3N} boxes at each sealed (p, N): outer loop
  over c₂ mod p^N, inner 2-D broadcast over (c₁, c₀) mod p^N; per-box
  membership sums (P5, P6) are literally materialized as 2-D arrays.
- All digit reads at base levels ≤ 4 (the gate's resolution).
- Frame-1 objects via the S1 closed forms; F5 cross-check: ≥ 2000 random
  members per prime against genuine subtract-multiples long division by the
  LITERAL Φ̂₁, plus reconstruction f = B₁·Φ̂₁ + B₀ (exact mod p^N).
- The quad·lin cell list is INDEPENDENTLY re-derived in-script by brute-force
  F_p factorization and must equal S2's table (else FAIL).
- Cap-5 stability: every classification recomputed from c mod p⁵ must agree
  member-by-member with the mod-p^N classification (all reads are ≤ lvl 4).
- Long output → /tmp/d4n3_census.out; machine-readable results →
  verification/results/case_d4n3_results.json.

## S8 — FALSIFIERS (any single hit ⟹ gate FAILS; this file is not touched)

F1 any exact-count mismatch in P1, P2, P3, P4 (or the derived sub-totals).
F2 any box with step-0 membership sum ≠ 1 (double-count or orphan).
F3 any root-cell member with step-1 membership sum ≠ 1, OR any member with
   v(r₀) ≤ 3 or v(r₁) ≤ 2 (inherited-(BOX) violation).
F4 any P7 exception (w(B₁) ≠ 1 or vertex digit ≠ z̄ − r on a root-cell
   member).
F5 any closed-form vs literal-division mismatch or reconstruction failure.
F6 any cap-5 instability, or the in-script quad·lin cell list differing from
   S2's sealed table.

## S9 — What this gate does NOT test (honest perimeter)

Verbatim per §D4-R.6's RECORDED LIMITATION: μ = 1 only. NOT tested here, all
deferred per §D4-R.5:
- The VALUE-COUNT risk → [1v]: any polynomiality/uniformity of C_P̂(p) in a
  pool size q, per-vertex or value-fiber distribution structure, μ ≥ 2
  windows, a > 0 anchors, multi-digit reads at extension pools. The μ ≥ 2 /
  a > 0 danger is gated in [1v] at n = 5 and over F_q.
- (NA): never fires here (the descend is adjacent; only (HV) is exercised).
- L1's (S6b) offset-lift boundary enumeration: ν₁'s canonical lift is
  recorded but never APPLIED within the prefix (no frame-2 objects exist in
  this gate).
- Menu completeness / shape catalogue [2a]/[2b]; resummation, drainage,
  termination [3]/[5]; the full-window multi-side read order (our polygon has
  one side; FC8's sibling lumps are not resolved internally).
- The L11 finding-4 factor-selection collision (structurally unprobeable at
  n = 3, S2).
A PASS certifies the partition D4R.0 and the mass law D4R.1/D4R.2/D4R.4 AT
THE TESTED SHAPE with the FC1–FC9 choices, and nothing more. A FAIL on P5/P6
refutes the kernel D4R.0 as specified.

## S10 — POST-CENSUS VERDICT (appended after the run; no prediction touched)

*(2026-07-26, census = case_d4n3_gate.py, run after S0–S9 were committed.
Full tables: /tmp/d4n3_census.out; machine-readable:
results/case_d4n3_results.json. No falsifier fired.)*

| sealed | p2N6 | p2N7 | p3N5 | p3N6 |
|---|---|---|---|---|
| P1 fiber (384/3072/3888/104976) | 384 ✓ | 3072 ✓ | 3888 ✓ | 104976 ✓ |
| P2 per-η (128/1024/81/2187 each) | all ✓ | all ✓ | all 48 cells ✓ | all ✓ |
| P3 digit cells (512/4096/729/19683) | ✓ | ✓ | ✓ | ✓ |
| P4 DEEP (= P2 value per root cell) | ✓ | ✓ | ✓ | ✓ |
| P5 step-0 sum ≠ 1 boxes | 0 ✓ | 0 ✓ | 0 ✓ | 0 ✓ |
| P6 step-1 sum ≠ 1 / (BOX) viol | 0/0 ✓ | 0/0 ✓ | 0/0 ✓ | 0/0 ✓ |
| P7 vertex/(HV) exceptions | 0 ✓ | 0 ✓ | 0 ✓ | 0 ✓ |
| P8 μ̂ = C·p⁻¹¹ ≤ p⁻⁴ | ✓ | ✓ | ✓ | ✓ |
| F5 division/reconstruction fails | 0 ✓ | 0 ✓ | 0 ✓ | 0 ✓ |
| F6 cap-5 / cell-table | 0/match ✓ | 0/match ✓ | 0/match ✓ | 0/match ✓ |

P9 N-stability: p = 2: 384 → 3072 = 2³·384 ✓; p = 3: 3888 → 104976 = 3³·3888 ✓.
Derived sub-totals (cluster p^{3N−3}, NC, target region p²(p−1)·p^{3N−9}):
exact at all four configs. GATE VERDICT: **PASS** — all 12 sealed verdict
families exact at every config; 0 double-counts, 0 orphans among 404,128,692
enumerated boxes. Finding-4 collision: none surfaced (and none was probeable
here, per S2). What this pass does NOT certify: unchanged, S9 verbatim.
