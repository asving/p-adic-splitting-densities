# STATE-probe-2 — SEALED PREDICTIONS (written BEFORE any census run)

Date sealed: 2026-07-27.  Spec: `lean/notes/ASSEMBLY_PLAN_2026-07-26.md` §4
(STATE-probe-2, the n = 6 vtx-VARYING regime; REQUIRED to PASS before [2b]
STATE-GEOM or [3] RESUM is accepted).  Seal source: the per-τ conditional
one-step rows of CTS-M(iv) in its [1v]-COND form (`lean/notes/MOVES_2026-07-24.md`
§V-TABLES / S.4: the (T·G)-rows; RS.0(α) = CTS-M(iv)-REP = M2(ii)) — NO [3]/RS.PRE
text is consumed.  Gate: `verification/case_stateprobe2_gate.py` (exhaustive,
exact; no sampling in any verdict row).

## 1. Configuration (the plan's n = 6 feasibility-finding regime)

p = 2, monic sextics f = x^6 + a5 x^5 + … + a0.  Root Newton side slope 1:
v(a_i) ≥ 6−i with residual R0(z) = Σ res(a_i/2^{6−i}) z^i + z^6 = ψ²·χ,
ψ = z²+z+1 (the F_4-cluster), χ a monic quadratic coprime to ψ.  Over F_2 the
three coprime choices, and the transported cluster lead ("vtx" = χ(α),
α² = α+1) they produce:

  χ_A = z²+z   →  vtx = α²+α     = 1    (VAL.1 SUBFIELD cell {1})
  χ_B = z²+1   →  vtx = α²+1     = α    (VAL.1 NON-SUBFIELD cell {α, α²})
  χ_C = z²     →  vtx = α²       = α²   (VAL.1 NON-SUBFIELD cell {α, α²})

so vtx GENUINELY VARIES across VAL.1 twisted cells as χ ranges — the regime the
first probe could not reach (vtx rigid below n = 6; results/state_probe_output.txt).

**Frame dictionary (derived; verified exhaustively by gate layer P4).**
Key Φ1 = x²+2x+4 (the (S6b) lift of ψ along slope 1).  Φ1-adic expansion
f = Φ1³ + Q2·Φ1² + Q1·Φ1 + Q0, deg Q_i ≤ 1, with the slope-1 weight
w(b_x·x + b_c) = min(v(b_c), v(b_x)+1) and the F_4 digit at weight m read as
dig@m = (bit_{m−1}(b_x))·α + bit_m(b_c).  The root stratum is EXACTLY the
Q-cylinder (dimension count 27 = 27 pinned bits, both coordinate systems;
worked instance: f = Φ1²(x²+2x) = Φ1³ − 4Φ1² lands in the χ_A stratum):
  w(Q0) ≥ 7,  w(Q1) ≥ 5,  w(Q2) = 2 with dig@2(Q2) = vtx = (c1+1)α + (c0+1)
  (χ = z² + c1 z + c0; in(f) = ψ̄³ + ((c1+1)2̄x̄ + (c0+1)2̄²)ψ̄²).
Cluster polygon: vertex (2, 2) with digit vtx; ν1 side (2,2)→(0,w0); residual
quadratic R1(y) = vtx·y² + d1·y + d0, d1 = dig@((2+w0)/2)(Q1), d0 = dig@w0(Q0).
Classification (F_4, char 2, d0 ≠ 0): RS iff d1 = 0 (then d0 = vtx·r²,
r = d0²·vtx); SPLIT iff d1 ≠ 0 and d1² = d0·vtx; else INERT; w0 odd → RAM;
slot-1 strictly below the segment → TS (two-sided).

**The 12 probe states (CTS states of the continuing ψ-cluster; ≥ 2 twisted
cells, ≥ 2 loop positions per cell, ≤ 12 states, each cylinder = 2^27 ≤ 2^28).**
RS self-loop states S(vtx, r, h′), pinned as exact coordinate cylinders:
root stratum (27 bits) + single-side + RS pattern:
  h′ = 1 (w0 = 8):  d1@5(Q1) = 0, dig@7(Q0) = 0, dig@8(Q0) = d0 = vtx·r²
                    (33 pinned bits); census depth N = 10; |S| = 2^{60−33} = 2^27.
  h′ = 2 (w0 = 10): dig@5(Q1) = dig@6(Q1) = 0, dig@7,8,9(Q0) = 0,
                    dig@10(Q0) = vtx·r² (39 pinned bits); N = 11; |S| = 2^27.
Roster: h′=1: all 9 of vtx ∈ {1,α,α²} × r ∈ {1,α,α²}.  h′=2: the 3 states
(vtx, r=1), vtx ∈ {1,α,α²}.
TYPE structure (τ types the VAL.1 vtx-STRATUM; r, the vtx VALUE within its
cell, and loop position h′ are UNTYPED): type A = cell {1} (4 states);
type B = cell {α,α²} (8 states: 6 at h′=1, 2 at h′=2).

**One-step move ν2 and the readable fresh word.**  Recenter
Φ2 = Φ1 − (2^m r_c + 2^{m−1} r_x x), m = 2+h′ (= the ν1 side slope); re-expand
f = Φ2³ + Q2′Φ2² + Q1′Φ2 + Q0′.  Theory floors (D.10/TRANS-RS: recentering
kills the line digits, vtx transports): w(Q1′) ≥ 2+m+1, w(Q0′) ≥ 2+2m+1,
dig@2(Q2′) = vtx.  Readable fresh word (exact digits, refines the ν2 bucket row):
  h′ = 1 (N = 10): W = (dig@6,7,8,9(Q1′), dig@9(Q0′)) ∈ F_4^5 — 1024 cells;
  h′ = 2 (N = 11): W = (dig@7,8,9,10(Q1′))            ∈ F_4^4 —  256 cells.

**Deviation from the plan's "N = 8" (recorded, not silent).**  N = 8 cannot
express the states: d0 = dig@8(Q0) needs bit 8 (N ≥ 9); h′ = 2 needs bit 10
(N ≥ 11); and at N = 8 the recentered word would be empty (floors 6/9 vs cap 7).
N = 10/11 is the minimal depth realizing the spec's own state roster; the
plan's BINDING constraint — exhaustive conditioned cylinders ≤ 2^28 per state —
holds with margin (2^27 exactly, every state).

## 2. Sealed predictions

**P1 — THE REP IDENTITY (primary sealed falsifier = M2(ii) = CTS-M(iv)-REP =
RS.0(α); pass condition (i)).**  Within each type and h′-layer, the FULL
readable-word histograms are IDENTICAL cell-by-cell, exactly (weighted rows;
all |S| = 2^27 by construction, so raw-count equality = weighted-row equality):
  (a) type B, h′=1: all 6 histograms (vtx ∈ {α,α²} × r ∈ {1,α,α²}) equal —
      the vtx-VARYING comparison, this probe's reason to exist;
  (b) type A, h′=1: all 3 histograms (r ∈ {1,α,α²}) equal;
  (c) type B, h′=2: the 2 histograms ((α,1) vs (α²,1)) equal.
FALSIFIER: ANY differing cell in (a)/(b)/(c) that survives adjudication
(arith layer, truncation audit, Galois-relabel check) REFUTES M2(ii)/REP,
BLOCKS the [2b] and [3] acceptance events, and opens §8 R2's wall channel
(one 𝒯-refinement round allowed — typing the Frobenius relabeling of the
non-subfield cell, i.e. comparing S(α,r) against S(α², r²) with digitwise
F_4-conjugated words; a second same-type failure = R2 WALL).

**P2 — THE SEALED PER-τ ROWS (pass condition (ii); derived from the
[1v]-COND (T·G)-row apparatus — Theorem C freshness + D.10/TRANS-RS graded
landing + the §B2 carry floors; same derivation grade as the first probe's
claimed row).**  Every state's word histogram is EXACTLY UNIFORM:
  h′ = 1: every one of the 1024 cells = 2^17 = 131072;
  h′ = 2: every one of the  256 cells = 2^19 = 524288.
Derivation on record: the word digits sit at fresh weights; Q1′ = Q1 + (terms
in Q2, const), Q0′ = Q0 + (terms in Q1, Q2, const) — the division triangle has
no feedback — so per fixed value of all other free digits the word is a
BIJECTIVE affine function of Q1's/Q0's free top digits (fixed lower bits ⇒ no
carry into the read window): uniformity is exact, and the vtx-dependence of
the one-step law is confined to the outcome LABELING (r′ = u²·vtx etc.), never
the digit row.  FALSIFIER: any off-uniform cell with P1 still holding =
seal-derivation mismatch (the sealed row, hence the K_e-row reading, is wrong
— adjudicated against the [1v] tables before any wall claim); the identity P1
remains the REP falsifier proper.

**P3 — FLOORS / TRANSPORT / SIZES (carry-algebra layer; sealed 0 exceptions).**
Per state, over ALL 2^27 members: (i) |S| = 134217728 exactly; (ii) 0
violations of w(Q1′) ≥ 6 [h′=1] / ≥ 7 [h′=2] and w(Q0′) ≥ 9 [h′=1] / ≥ 11
[h′=2]; (iii) vtx TRANSPORT: w(Q2′) = 2 with dig@2(Q2′) = vtx for every member
(the anchor/lead rides the recentering unchanged).

**P4 — THE ν1 ROOT-BOX ROW + a↔Q DICTIONARY (independent a-coordinate layer;
N = 9, exhaustive 2^27 per χ-stratum, a-coordinates — this layer never touches
the Q-cylinder enumeration, so it independently certifies the dictionary and
the state-entry masses).**  Per χ ∈ {χ_A, χ_B, χ_C}, enumerating
a_i = 2^{6−i}(r_i + 2u_i) exhaustively:
  (i) 0 violations of the Q-floor dictionary (w(Q0) ≥ 7, w(Q1) ≥ 5, w(Q2) = 2
      with dig@2(Q2) = vtx(χ) for EVERY member — the χ → vtx table of §1);
  (ii) the fresh triple (t, u7, u8) := (dig@5(Q1), dig@7(Q0), dig@8(Q0)) is
      EXACTLY uniform: 64 cells × 2^21 = 2097152;
  (iii) the ν1 named-bucket row (per χ-box of 2^27):
      RAM7 (u7 ≠ 0)                          48·2^21 = 100663296
      SPLIT1 (u7 = 0, u8 ≠ 0, t ≠ 0, t² = u8·vtx)  3·2^21 =   6291456
      INERT1 (u7 = 0, u8 ≠ 0, t ≠ 0, t² ≠ u8·vtx)  6·2^21 =  12582912
      RS1(r) (u7 = 0, u8 ≠ 0, t = 0; r = u8²·vtx)  1·2^21 =   2097152 per r ∈ F_4^×
      TS(5,≥9) (u7 = u8 = 0, t ≠ 0)                3·2^21 =   6291456
      DEEP/undecided (t = u7 = u8 = 0)             1·2^21 =   2097152
      (total 64·2^21 = 2^27 ✓); the RS1(vtx, r) count 2^21 = 2^{54−33} ties the
      root box to the state-cylinder sizes (the ι/entry-mass consistency).

**P5 — LOOP-POSITION INVARIANCE (the RS.0(β) height-shift display; pass
condition (i)'s "loop position varying" leg).**  At matched (vtx, r = 1), the
h′=1 marginal over (dig@6,7,8,9(Q1′)) (u9 summed out) equals the h′=2
histogram over (dig@7,8,9,10(Q1′)) under the floor-aligned shift
(k-th digit above floor ↔ k-th digit above floor), cell-by-cell exactly:
256 cells, each = 2^19 = 524288 on both sides.  FALSIFIER: any cell mismatch
= a loop-position dependence inside one type (same R2 channel as P1).

**P6 — CROSS-TYPE (report-only; NON-falsifying either way).**  Differences
between type A and type B raw rows are EXPECTED-PERMITTED (carried by the
block system); under P2 none appear at the raw-digit layer at these depths —
the twist lives in the outcome labels (r′ = u·vtx-twisted).  Recorded for the
[2b] table, adjudicated never.

## 3. Verdict rule (sealed)

PASS  ⟺  P1(a,b,c) all-equal AND P2 uniform AND P3 zero-exception AND
P4(i,ii,iii) exact AND P5 exact, with the gate's arithmetic layer clean
(closed-form division chain ≡ literal long division + reconstruction ≡ the
vectorized path, on random members per box; Q-members reconstruct into the
correct a-root-stratum).
FAIL  →  full diagnosis required: which family (P1–P5), which state pair,
which cells (first differing cells with counts), which outcome classes (the
ν2 bucket labels of the differing cells); then the adjudication ladder of P1.
Any P1/P5 failure surviving adjudication and one 𝒯-refinement round:
STATE-probe-2 FAILS, [2b] and [3] acceptance stay BLOCKED, §8 R2 wall
protocol invoked.  No result of this census may weaken the sealed reading
post hoc.

## 4. Census parameters (fixed before run)

Gate `case_stateprobe2_gate.py`: numpy-vectorized exact mod-2^N arithmetic
(uint32, masked; products < 2^22), chunked 2^20-member slices, Pool(12);
literal pure-Python polydiv/reconstruction cross-checks (≥ 500 members/box);
long output → /tmp/stateprobe2_census.out; histograms + verdict →
verification/results/case_stateprobe2_results.json.  15 exhaustive boxes:
3 ν1 root boxes (N = 9, a-coords) + 9 h′=1 states (N = 10) + 3 h′=2 states
(N = 11), each 2^27 members, no sampling in any verdict row.

## 5. RUN RECORD (appended AFTER the census; seal above unchanged)

Run 2026-07-27, `uv run --no-project --with numpy python3 case_stateprobe2_gate.py`
(numpy 2.4.6), 16 s wall.  Long output: /tmp/stateprobe2_census.out (copy:
results/case_stateprobe2_output.txt); results/case_stateprobe2_results.json.

**VERDICT: PASS — every sealed family exact, zero exceptions.**
- Arith layer clean: unit tests OK; literal polydiv + reconstruction + a-stratum
  membership + Φ1 round trip: 0 failures (500 members × 15 boxes).
- P1 PASS: all 8 same-type comparisons identical cell-by-cell — the 6-way
  vtx-VARYING group (v ∈ {α,α²} × r ∈ {1,α,α²}, h′=1, 1024 cells), the 3-way
  type-A group, and the h′=2 pair (256 cells).  M2(ii)/CTS-M(iv)-REP holds at
  the vtx-varying regime; no 𝒯-refinement round used.
- P2 PASS: all 12 state rows exactly uniform (2^17 × 1024 cells h′=1;
  2^19 × 256 cells h′=2) — the sealed per-τ rows on the nose.
- P3 PASS: |S| = 2^27 every state; 0 floor violations; 0 vtx-transport
  violations (the lead χ(α) rides every recentering).
- P4 PASS: all three χ root boxes: (t,u7,u8) uniform 64 × 2^21; named-bucket
  rows exactly as sealed (RAM7 100663296, SPLIT1 6291456, INERT1 12582912,
  RS1(r) 2097152 per r, TS 6291456, DEEP 2097152) — the a↔Q dictionary and the
  RS1 entry masses certified in a-coordinates, independent of the Q-enumeration.
- P5 PASS: h′=1 marginal ≡ h′=2 word under the floor-aligned shift, 256 cells
  × 2^19 exact, all three vtx — the loop-position/height-shift invariance leg.
- P6 (report-only): 0 cross-type raw differences at these depths (consistent
  with the uniform sealed rows; the vtx twist lives in outcome labels).
  Galois relabel layer: 0 differing cells.

Gate reading per the plan §4: STATE-probe-2 PASSES — the blocking sealed gate
for the [2b] STATE-GEOM and [3] RESUM acceptance events is DISCHARGED on the
probe side ([1v]-FULL and RESUM-n3 remain [3]'s other blockers).  R2's wall
channel stays silent at the vtx-varying regime.
